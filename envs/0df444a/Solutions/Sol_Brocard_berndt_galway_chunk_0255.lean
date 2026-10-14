-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0255
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:46:55.699549+00:00
-- url     : https://prove2.me/submissions/7782da32-7605-4df8-9678-a477e84f710f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 45683457 ≤ n < 45863313 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 45684707 1250 45683457 45683461
    0x412050c070b04090b1e09071101090803010302040b010219030f0e0a030b01030309050613090b13050a090507081f05060109080a06050601031a130e01020405030f070302040e07051309050c09 83
    0x2c1c41c0c242d40d010348034001010f401c080c8804103071315003000750a00e8181031113800c509140c1408140f00c1c420740010400300602440045081005202f030064100540c40760010568a6065204010448000a2030281190722054413000e2640c0f00901d20042a50507042150030b1402c08038040750741240d080401c81e0445207c0070b00101304440c0b24942c0d41a64480e880741a40d040d01c2d40140040c42c0614001c0590b01d45010908100651881c3d102e0318103014050002580003404600325403d560007079540e01c0d0405d5450702c0750b00c2880000c0c086407010300030200140413414405403c145000813000a601a060ba0740ea010407010381c041c490800050843c801554456003060900c10014407084a119003c241040103240307803c8140301c00381c280c100008005004d28000800058000c0584e4940c00451350350811010a035a54204051100311105200609031a170540c4148410f5410170108078030254021074040c441680c44641713185040c4c0300501e00050b5a00e213030600c503251203142c04042d40c1040504007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 45685957 1250 45684707 45684719
    0xc090303080609270601030b0f1e060402040504020301030b040605060609240c01061706010501020c10030b0d0c17120901020d12060e070f021c0906050d090b0f100909020303030412050c07 82
    0x1805d038100c0740155908202d581d03c03ea00d0301c20000040302c480c58140803859208c00301076001c1c441d6a412a40240c40181407685a001141c00ca0f0f0081e0004e882100740744041100b001030501406500000585d42c5505140791140401c0090f144c100d281500f2184015028134800710340b43c1a03502103402d4000078020796076074803075061110740c141c07030400410f0050600218843d400028100840803029001001d4900d01d160300714010004000d030150320058041c1c603000403c1c5180285405010045444002c4144500480303241104180314036004010910070844940c0c0c0114205200c0282410000e1800030543c20080040c44641c020110502040c0203101c015584401508608013103a02107500d0104002540105121b901150314002000e070318041c888c0354800c9020342840c544010700443d8904155441c011810700845001ca0004010343c10807100c04a01d40b81d90000301180700c2c0c200505130458001c65200d110040000d002144030800c02500a4440e2044070030200c03010017500c5d00320380c80c1c003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 45687207 1250 45685957 45685963
    0x2090103020705030a0c21051b0109020a180605010c02090f0c12040303050105130203040510151706040b011e0509060111060702100e07060e040908070807060f0c09030308060927 78
    0x141b419152180e82031024a0080ca0982c03803030014001a4a46c603080418550030f4005070032080705980d05075522002d850700181c43e0030071074130064000e20904c4212007180c007021004603682680194100a480d803441da01688894040c0c40e00706600aa0741555681e6410703103203420784542c0c406600d012031048100000c0c035505030300c50f905a8a040b1100c030b00910030102c940b000d0b4002664003501d2900840c08076444039030282e1019048402240248001d195a603078403c0c1708103140c0080c181030350800030802003040b003409011409050302e840c4c0c01050300d181e400b040b45011450b008a41c020270501c408590261301881541e038010341e0740411100715180c4118000d4495841d0044042d040d41090485880e408001c101841920340980c2da07240d80c45200001c100281a4030481514280010400c2c4404254200c0003800030074001c91010810108080d222030403034801ca09540d04100c0741c8001400040d44c0700680d40e401c4281200e80704410b0700d0f12001e21403150301c0180305080f8003081b020340d80d000c20404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 45688457 1250 45687207 45687227
    0x417030a0506090a0b0303030f0403120614040b03070308040902070303020409021803010b0402090121020d0203250212030c090307180e060a0605030309090703020d090f050c010216050402090103020705030a 90
    0x40e1540700c29920f03013813448415129600c0507164150014000038407e8904011a140c0c031a0003450b1918441c5407014002048030a1341d001400d80c8a443c59a24405080c10301a9800304901034006088081c51a1039404150141d4000c43d501c698000a4440034584242c05843c0a0025010119034407840d003000709000b400c128100c18002e50a18000c40f40074a82482500c0f03480d00180c442400798601951030580319291540c6802c8603a07420701c05880c0300390803440036602c120541c0820307082607a0369101c0c09983c4034803900c40360110351000650f4407030011030005594021a983d5140e43d02e07001190b000a08111854002d101d003441a056050440f100a403c548001d0440c8070645241382c031944106400d803800c0c1c2c000c454240e4800c11498540f4142002260343c840481d03c3c0050920f03101103402000e440d450007040da070140c0d8000c0b80b24144641070201e2241d808090004050318400510030403000d038034500c070b01c074481c6502190158040c0d00940440e940c0a902c002500d0f40d84581220140c055661 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 45689707 1250 45688457 45688459
    0x10090204090905060a140c0702120d0201090b1303050f0315090403092c0606090a030b0906071e0804080a020102120c0414010518090402040e0f01050714040f0506030417030a0506 78
    0xa10800f0500c4495184507207030f80219480ca0000d055030301e00e0b82c000c801d42d1151408a80111a400d12b6407003100d001c0c03010304005602680041900c051a05080d480341c0b0000c0e00b10085214114140000030781c01c1012500c1d480500c800040d12955908983d108000ca0044801d400aa01c0c9007041300b0554880326080941c1d091400b18181c86545d50358503010b541d150842c1d624a1450080403401904e8140058403070b140c0c004010940494681c0e407800300104c010b0b034072841680e216409000c0e07201e4125611889a11001d60b0050403219064402040d00b000134002602150000515200c407030310030340450701d040002451030030716420121646041035015100315040254046422056036100b541141c060601d034800c0e00740c00c0b02c43c0400304020110041d108a9106640c0c00c44d112040605105c084107241c0c0000000650785000c1402600500c00e02950402e1000c08100038480b08680484103000d945050310410b4032035440c0d15215017102d1482041004600c00402000170404064000e948a040c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 45690957 1250 45689707 45689713
    0x60801061703031b070804080106090b01260406060815041101030209060706050a0207060c030902030f07120f0501020d0603050a0c06020303040b0129030702030d0b091e10090204090905 81
    0x754594044401a4840c440514190010008181c0c030460910031030208029141143e40351400036510b003100da510036408040983d448800401000d100d51141c9152100c0a003003410034103400500c0b01c0380000724005003104100000020a046c0440d0b60b201502034101402200d08081c1d0520307500b010580c04a404a9510920542000381035211380252115040c0240249040945a58980d0040e0600a00140c500e950a00511002c00c0e00d03401b6807015034010f52000100c003007071401450305201d0705499a03102d550000608011000341c1107209010075401035000c01880305a0f182c51406482a03201034000b0600b0940c002c001e01c0780204440007038038420f405a6060b56030f564001e0340c40c2d0204031400340000803c800108040414a10316040d01d481c1c00043c0c00107559846201384482d00241c035a0b60041c0d00120b07480801c841103200313500c3d00c801c040712100c00c82d141044084c0c2440401c084048030340ac900c3e4010416010042c0e40c90f5000d046600d4003903441707a0700c5000410050640007000d5a142c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 45692207 1250 45690957 45690959
    0x180506010f051f0206011203020c0310050403031d03040b0f09030109030f02150f0105040c051e041502120910090e0108010c0e09060a09232517060d0f06050a06080106 73
    0xa03c0400706080050440e00076041c180e10b014103038000007204250950544c020303030540e10b100d80d805004156000c40c0301440003c5a0503c1c0c00c0050495150528058800d03845e020410181400003082d1401c0300cad1200b0046035601c411102c01a81c0d0700496030f03004c0d01503007000503100c201a080304140c420b202e841d500b2920100d102450100314141d00b5214111000c10315001030081d8206038012180120391410030b03500d400032442003089802001c01d641c0d06c0c0c1c1d20010400b8490f00740c6410428007044003520040800c941150084c000520681c00980c0c0304054885040402ea4020750041009100c400c0782403c1540e500c518041c00b800b2460701200001e4011154401d40740380000c412401950058a207010450600080c0380c001c4c1428401d0b860407815040c1e002041c86404030485201d40390940c0c143c1c4251011344034210200b4511100745017401082440d440f0080c807054000e940c07004044520a40f1644207003001c0a0004c10050f002d400d05003031000308042031000f40c21441c101d03406480200495 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 45693457 1250 45692207 45692239
    0xd0615080609040b010303200318040f060605121017030309060a0606020604020405090709090c0503060903160809040f09030e010206010501020d120b0303090d21030519180506010f05 80
    0x1400890b002402c00304e008006001081c800c15088086448148450b003c4580456020f481d507004050036141400f0034440041040c00c0c00d01803446d4090f01e80c841440050b003007400181c41d42c0200d400d14200c0406050002e102144003801c0d0000070242512880c900718402d55469841e030748100e60450300351250501003102c038211841100c088403150340c0035180320741311942004050321000c2c2101d1050321032864041148010b0f4400c07004003078403402c01e01d0101803501007410f007401402084400c0c02e800c00d100d40e0750b030524100381102c0ea183d48450760072741e80c030340000005000f0024034004014aa2814510300101600140ea1081441c0241c003120703810f0383c1c3c03100120ba4544800904200080802d50080c0c1303482290f8120f425803030001815207041121080c040781c3c1d103007035203901a10000e0142884902e4402611240d1002c1e4429240a03c514902852072030200405c1c001b06641440c0c4d104402c40041041c0c0d0a9a11119400070a854a41d6500c02c07141c41100c42c6800f520780b24003940002d02c550 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 45694707 1250 45693457 45693469
    0x8030a0e0d0305160309030b07050a080108010203010509040f151a030c040e0d050d1803090315180314072301060902031303111c02010606030c05070c03080a050d06150806 75
    0x80a41c543e4590340362141d4824a44d0361140d00c41c0045060040054010000428180c1e0031071180003540d42d401d0312090030310002000a04103034080c01b107070391040006111517102c46401c1036005400500340c404062161030b00114003000107081020040c0391408401484009001900904004030119040088004200000c54101005c0e003030300c99100e03c4503960402d0042025007901014020700041420030140c40000d8160703081c0c001c80015405840034410084000c0300011a0700441400700022900454143d0b44030180000103414000c03102181482d0703844180854019035030113041004510207844280a80719203581c3c118505501b4908040f800d66068800d80b0f1080304094514050500651002d4070500d640603500071050040e000300a01d04002001060342c500015400011030a107484001021140c0c6c501600c400c2241c10482c1034041540c0d003d02d03074240c030f8221184a03903c403071a40060b5244d02c641c01d01005601d041250004a00c1d400c3c0c402044c10710515140c85000355544810415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 45695957 1250 45694707 45694729
    0x30c07020411120601201c08130309060507060b060c0109110303120609070c0b040f05150c03070305090c040e06090c06030108030706020f090909011b080c09011b0c08030a0e 76
    0x42d070f040f8290002400303984110712000d02d03803404080340c075030044030260007500700520034001c000318904c00c480301500c09900c541410b9000000b108040418080d80d60020010100c074450300c000c01801044660a01003254042c4420b100e004101c1c90ba9094030300316140c041d0030400d40603542201014114901e07401c0c040106d0302c0c1c00000310400703003148c5d542d88200700c00504c0141c02d4008019401c440000041d036507070201401180140806020504075240c80780c03800c1000c820601c40f143c1c91100307100e05a46244103a942000b21800d001c6010341d118000d01d4078210381c135100c0b60707489070030048100402070780455001d02542800f42500c2000a444040c044540303c01c2c89188078607401085124041042980035040e006c0d051242d0614140642c0009044001c055035183d46a941d01d8480d10142000146040704005550600a440c0c0c43c1084514246004004055040c002c03011224a41c140641c81c2c0550707103543c490000740c0c420b6200d0781c50540d02c2e04080e81c0c0c1c40c00700380b04540018a85c581928500c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 45697207 1250 45695957 45695977
    0x2070e01060906030e010f0207030804150209100f02121b010518031e04050409110906010c030206070309020f15030f0106020c06040303031e06081f141503070b030c07020411 76
    0x110b0740c1481c02c10200c0041040e6481c0312195566070a18a03603517603a500052402901940e00c215490500e8206440c070b0044000e00a144e1510401c841d4445864100300380031020540c2c14904041056008168201100207038070300c0d000e07400014084000e011201c2210080c40c603400c020012941c980c00011451455440d40714041c0c1e00500220490269240d100510514400304a908041c0d660012406884400760102c64424014941300c01c02e040c800c0f5200e501000921f86860203a40e0380d1006512108041c101c0000c0584450741e80c0155281c0303000b29464200701805010020038202140c101603001914004d00c40110000001102d80c4001000b180300c500040013503240500c1c0da44d042e40240200e880c0744078442c417001c1000141d0600380c4980300c0180341600c0500040b030000b204a580100308001e4104c1034504e0304420304442d041074081240c0c805050480c5119400c5610000b0789070408503408161070301e000008200018410901031b1800601c248c1e024000c1901000548416000b85604a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 45698457 1250 45697207 45697217
    0x90206070f080408030a0207060e04050601081504020403140705010305010f0e01060503130203030c01090c0501050408030f091c06060302031009050c0f04020d0908180a0503070308090414010e060102070e0106 91
    0x100012603154168801d1031803089245524165540201505607001030100c200960000380382000782076084459030703440c000304503010401441c090300040e0202101400b00c9414840c942036214150f203465046174040c40c0c07c005182c1c941800c134000c2c40c0d80c620050203040d000a080c03400002e0b940710503681c10000c0e5071849078210500ea003403003002c44a941006103400c0340c19010508440c0940c50500c018040c64100074004180d01c42c050900582191641d4030841c1003160801c410031040d180031003034500d050030010f5140d9075840c07010300088011303083d55000041c2a05c000540310400441da0f02620840e413080c0c050f124811001034038942125642c4001a0050300050000441494400c00249129000030401070600501d150206e049400040045406042c000b40c800c2d8120100b034031304111840e045440c415054101000300b80c40761484e20004181e0f040204070b200007955182c01440d03034081c041216090b99039481c40e000000c010146c9c1c91a0140c050b5550114021110b0b8010f6410798413242c0310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 45699707 1250 45698457 45698467
    0x10060905090f070c02150d0614010e0d0f0b010b0a02010609020a0e0108060111061e0a0e0a1b030206161202060103030806100201021e0301170303060f0607060b030703210201090206 79
    0x403501010b03005141004010f121080d102c0140c0e581c00c2c400300160340050041b52070302034a0740e40702d0448005400c00390000a40d54034000c41e82c2e9010010710001c28090f140c96400b91650b240c01c864500c42e002d4020310448036580003040030700103c0003a00c0f240d03240740d009016456545250500320300c201200c980c00a168840040031035400340c1e5180741c010206142811840286c020b00741d06151080d140c10140c409a07110390359010305014002904642c038684100510082110140e0341c5e00110507005004c03445074405103c95668500802006540240050340e840103d6040c00c400e0486031582250221255004000c4140c8000303449410380b54151a007004079110081000b0000100d41507074800c41d0340801c19800400b82100445d40607103001c070011a107950603e400b0f4000602c0742c3c40b03001410380c8103004102d0240e4854420032203000b03084d1100c0f40d07100c00c107041c04805000c46c070f0500d540500c256100002041000c1001c050400e481c110100380c00210b05100320300761040c00c400a0742c09901800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 45700957 1250 45699707 45699721
    0xf040c05040e031e03100e0f01141c08040e131703060d020409060b09091c030c1106090c040b040b0a03140102041707050103050106141801030f141006090509 69
    0x402100c204040c0c0040742c0c1000c607010004560301040207848042c0e04408010302040550b00c00c0b0b0b4402405000d81030f40340c94074023812203a034002014420f402c514851400f09103040e80760151201004846002c80203608141c0d400c1c4100c496005200d00e0a0501d900b0000a44030300042540c07002c04c80d849201042c00e040c1a0300e044d0025040588101e0b03000c0c4881c12958010b80c0e4521542803400e01c500c0300440d5200710242041000341004005100300e4200e6018004414841c402044a50031141000070b0b002d0709541d012102e02e210804804501d204aa040c04005280001e50000185049034180b00000041d014403090350944240b07160402000c003000c3c000541100800c44110308024001414180d40c1c0d880300c008600170714480280c030b03040078206020030759160183c1ca014040605103e07181c03040750036500d200d82c80707101c0007030703a8090500c59441410382c820741292078030304802c0909002000d40b90015200114003980da490000555040011300b090080d8141001c49400070702d0501e40d035a0b900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 45702207 1250 45700957 45700961
    0xd1b0201050d0b0301150906050a08010c020a031b060606020609070602010606050d05060d1a0106030b0913120215070203280203160c03020306070305060112050c0301060f030e0307060c080f040c0504 87
    0x1004195165480d06e43c44007403803601034040c1d40101f00c036240200303000e8640300501c61090702d160001582641059042c12055400042d0220b50640c0361500381045051103c02003400019450014003007400d04c2800903a040d400925907020300417020a40300c4041d0341d914241e0807562140b01e840c01060742444512038880c0b8551025601c000003a1080100022030794624420801406081c0c010b0990240148242c40d80340c400d00690140c180c0340b03c1c1060402c405100e4040f0745174035000789010980d800401740d180c401d0103d1014006500d81907092401c2c042000b9440350450b47c10003100e00740e03106e100000c109d10510f03406100c1d0300e160055031030a0b24100080c040c00241c0c2c5401d40b03624902d104000010f031000c02c64079210300040e075400036403070500030700040c84001c2490fa20740303a66003404280030040d414102141d045440318142248018a5090160080e1103a02c42e4403055000101c0e00c07100740001500b2880481d40f860b0740d0b0500035a20407c170b100900d402a02c000c1c1454000f6032084c0030f141456 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 45703457 1250 45702207 45702221
    0x406030b18151311031f0506030105040b040b0928020f0a0e03030c0307060b01080f06031f0b090112020909030406050313060e1009051b060d0218120d1b0201050d 71
    0x50445000f2507807110b00c1906a642c0d41e20100b142160000401103207a65603050307006400031620211750558900000500103000601615114680d11309101c07445035a280d01c19240d4480c0a4001100740c540111301503003030041c00e000c0103540139080c401d002000d0524402c03a0003041202c40c480b410074981030002c40f9505009800140c1510040081c030519150400241001c04e1054a01040040c025000109a2400500650580603002c1e090000c075550202e1039240035620005200c0031110701c1e40c89800681b0700c80e0384060300800c48030004210440100c864900690091795109059201c0e5080b0542e41e10462080c00300140c4188049407110014170360380740c1b504c2c0c0513050201d1100b0060b207005003040c2c00c200004c0319040e51402d0040c2041401e20504984146030f141e074000981440300898002e05c076000c14900c0041e400581040e9160384440042010903015080c015982d02d05200d25036581d1544140001045880040051002d9004c4041c055591706a43d000c0c2403c1800c8501b001400c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 45704707 1250 45703457 45703459
    0x15010207080a0c050f0a06020d0804060b0d0605010e070206060102060705161202011e0203271002040803070b0112171318090209150109051201020d0906020406030b1815 74
    0x9400d40020084020804101c000380104145103280b40340100f0894140c0d102d51103103014001d54401008420f40100c4e840585608508005aaa40d40c40c9403020052040481c00c960000001c60b4800134001c660340494182c80020994207104d4949580684e91540b007141d07041d00580c03000c00006d00280c442c002800b00b02080313100c1c1000e1407409940e0101131040140e01c810050795110f0032910a400440c00c1d2001c807036a400301c1146181010004c5460b100400007a003200b401d00c2c035258100c2800100811401103400c854110340fa903032a4500300c1e40301c0d0300249013542d00754108000070464420403062061442d40c41440041c1d40c4041504070307200c0340c01041031504030300780002000a0052101004140200b00b45100041c00c07002c500c10821207040c054031524440400d00812415a41c008030140e050322400c460418294108031005400b903c07c0c2040f02a0310340c103144180c0100401600a0415a000f1b501d06002811403c4240912050b100c06a080c02c0c5040d00082401203490020b10741010340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 45705957 1250 45704707 45704713
    0x1210302031201060e0310060803270301060305060f0c0406020703031b05061602120c061f080a0b01090f05090c01030513080313060b01180e2d0103050d020102090306150102 76
    0x2040b100003050303803070003680003c1c08103442400100541c030b01403003903c0c810708054804102a03410402810347c1c074050004488c002501000c0490001500d0700920085401c00900030b0180e96141e1401c2900c2d0481641da080e018074001c000b040000f4000016203003502c0c8954018117806203961411a00c80004034200030010811202e06030214a0600103244940c010070051140c580f004030f0001e1400000d22000c070f110140510603011004030100351282c00c150025549016480340c0d441d04000821907600001030f910904d1014000c000003411554120740058401300176500004143c00700342c0c0c2003181c015044d9001014840f045600941c03149822a10410403d5244017040d580c030f8080ba4415104018030801c8015500100302c014018050252002e03c0d0003000d500040d01c03807448194082c05244404c0f002c41300000c41022001c414011804e07281c0700e14850300c1018042407000c4090070700043e24640101006a44040d00500840340558000380c01007841c1d80c0c40083c2c0d54900314805e00e4060440c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 45707207 1250 45705957 45705967
    0xf160807020603100819020f0f0303040e07020a030215040206121503010207030c0b0114060a030203090111190809060606090607060608010c1806020a1a060a0906080d0e090121030203 80
    0xa2a00b2010b1072091041d0019000f1580c20720300c10a14180c1e41082c01c0102260070705002c401610f400d603440c40c4118095a52030122802c0303500003030460080c1d80000d2845010901080040c55000031091200d6000e50291208401660f84040342103c003102e019401179010407030004100f0740c455055034056000414a144104001c0020b800c0e68005603003640000c041c501841c0601040a424500409908000c541004000c80200d006030003860107040c02c1c1540400003e0b01041d00303422401c445510a50300700d58032803505001004070300048214030001501c01c000030b410f4440c000783c0e0f14000c050081840e41400c1d141c60402a442e031101c0c600701c07251070b11000006400003007400307907004c0c117505911000d00d0a104684508100c100b590f004004541c0103424540114581000408188980a005030010399030b0b036000c034030b0740400756200c160400e24024000030390b1030300890f40c000580381655454500ea804802004001d40080c000c5180240004c61000c110318060304021840078802d0050700e00700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 45708457 1250 45707207 45707209
    0xe150a050307151707140a0509030a03050705010e06010f050d1707080415020303070807030f1407020d02011404021e0102070314010209040b0103020a02060609100503060a0c0f050f16080702 83
    0x114406034484880f115021068081d00c5800844010b03c861078000c0c0c100c41403900342c20081075800c02041c001540d1000107642c000c10351050003120900b1102a0807940545424a8018026405142c00b0b0700d50307500e00548442901400700311103040352032000c00d07a40058282820800140480d0a048464480c8034a0544003040c1e000c014088190007110a01d071210301d000c0c0785450b02c500f031580c0802190410010840301e5500f0044480d0040e0103071070000b82003014608448000e150402800601ca030708003040100c5958001400d80220540f907009000305814201e59030b56901007a10001e6121100c03213110702d000e100c0016030000f10300052048907a896520b880b194901c1014401c1001e0301e0350001007498150510380644401c80c4401c2ca411898802d110400940f82c0c1320160500340702d0a0a200440d00050b00d0844003030280100605883c81800c101c0c00e0040200381b40f000b01c0c8003155002034081a04d6004800341c1d0030303554041428502c0d0541406900e801c41c003102e542164011300910040d009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 45709707 1250 45708457 45708463
    0x30608010e0607030e060405060c03040f0503030f04030207050f01080f0703020f041217030105011e0e030d0203040e0c0304030c0b0601120e06040201030b040e19111002160501020303010e150a0503 86
    0x51956000c1c0642001c1c104044020240c59010506aa06501440a100001d0400245582e01040c0c841e01079860361264900075482c2038149001408920011051228110007241f210303000758420313002c0340c402c0c0d607452f41809144041007500c0c40c0481d0300b40300020400d94450410a40c0040700c0d00e00186020303400741290090b600141c215410050640c1089800c110700c621481c1c40c2c2c0103040b128141103600d4030380002c0c5400140c46001c510103810441946100b4062540d10038540402001d5600c55454110000e40c0c98001e0b11844804500c00b50108100507072180480740159010b9035000c045c0c07141500c50700c4452070007918003810880422010008402180320300404d800c000000781001c2d0501c1e00004098030142c21229104516010106e400410001182c0b07602c03003054000d160f40d242c854189042c0c2200044100f07a0020006042c60740d00c2d40c1e02240c0e80104076050b40090103001d0700c4200490383e0b80024000c40c031010940700d000c41c2c3d05041c5181d010b28100c0d001400050220748031408281 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 45710957 1250 45709707 45709721
    0x402031003060e0a05060a021204060905010b06030109020909061c08030702120a05041e2301030b0604120c0e06012a1407060f0c0503090603040c030507230f031b0103060801 76
    0x100a404c0710b201601007003824806290012400c25083d820402400303001035490001070300013031450b0740e22010142041301c2034001c1307010080010130301038480da91072903c140a580100c0d402407060403a0000144c061409001c1c45044140c1c00010100201ca655200e082640c00904064190f2050301a0101070010381001403203480410760702d894845140c00340c01c2c4903c020550948007210308001c3c00b40b001c070710318411000d1403031068000012041c03503040050b8018403030b5588181d00030b140000e0100303030104030004040c82944100c00e592030315980c0301c005d607c0916060b5407160004140c1141c4e2880f10100003034802d40080c0750404460f2100300c40c1c0c0c501c210391440b5a08500c0941110104100140c2c0144800134002500e0403e0f03418030300c03aa0b564645a208000403e80b080e040031020409202c1540380f40740141d580031040f140e08540354084410b200600d200d240f00e500c0150044001d590414446650002c01d02800412500500c000143c2100246141c4d66041568840c400a0440005d0207850 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 45712207 1250 45710957 45710981
    0x2304030201090c150804030f03060509040c080d0503040b010b0d0e0102070b040b0108030a020304150e0d05010902030c06090f04090305161a0a060b0a0c02010c0c0603021804061202040203100306 85
    0x41400c2540307400f401c41841c0784c0c01070390044100308900300c03403a13000211a81e0041d85460001c030008460364040e00100002d82245811401c2c00703040008001600c0c580c0406e03039410740d04a80c80e00241c40d60441e01b5100450700288000050001004020244009003440e400c0c55003001ca0742c88081000307a401c9800050054450f44056002c0c4000e1041c80c010300c83c003600a000140d0303e46012002c005c1d64901c0360784100006464004020010644101008994100f0007440d008080c416410705c0fa01a01400740264802e01034a03c40030010f140200844804804c0036060884001400041000500e00da407001e030240501041070061501c10071140510003807040c2044060701c0e000250401000800405044805240a0090008001c0902654160380c46031424001c800c00c2480129244000d98400610b01080190007060b050f0301a00034040e001c810302843c410510310402000203541c0c481c49544940d5002c10301410260a141c0c0040d070b880070303181c00130700b03841c0c0d599075175103402c4844201490b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 45713457 1250 45712207 45712211
    0xa0905070302120903040602150a1b0c060c0203030717070909110a0305010b120417040b040b12060f1e0402040b0c030316020105060319030c060f0b1003020403152304030201 76
    0xa01c1004408072000c4c0c005200780000c604043c10614065901d9000c19055a03032451208005400c86089422514590304140740301540110040e0300540b0785003280e40211030017410300740d980b0106071000080d680300300080d664890301c4100380b0311071000c40c54010b0440ca003001081c0e41c000c00c0410b1540070366020780d12844101c56640103142001006c44006812071500d4180401c160004503619680d01500b01d81c200d07014801c40855008504100e10440e8014100c034070010400040592a62001d41982c0b07242c880414240d648000c10042616800030f0301700e0780140500306c85100c2840010034440c0c10340c400307040180352a490303048000054004c1c042c545001c2d8400810400301d03069502d480d01600b407090000380030908201d00042d4450040b800c0a408000e0140164801c3c103100c2c01030080602e0304540e0800540892491703c8025240e00c10026003e1441d500e40e00495500c64400c6034210703608070b44040686030140c000c14000d010004d040403180e420711000c03c0810600c1d40c03400b6001d04c1c80390b000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 45714707 1250 45713457 45713467
    0x80a0b12030a0909060308070204020a1b0501141806010608090c0411070302010b0a08060606091f0c030207080f03040b0a02010b0a06090e1303020309040e0102130f051306061d0a0905070302 83
    0x30407030b003500c2c4c011002d203038100501040024040403c1e11401d550455002d138a44114003422500344c42c50702c04d41d66102102c007140310240304065120340000c00304c652107041549d94603400150320300080302c8040000d50001004224461054a5141c2c00c030100f0002daa490700d841e103000400b658080c4001041351742000840703104054092190080059043c0c0c0c007400ca032440c1c0b81c41140c41c0c040082449000e08400a100d4001d9507905c94484a404282a00b01d00d204520540051151401c078004902611501b100428000800104c9410140d814002035203042d044c0421b1881503008140d00109640d220540300c0f03840c0d511504c1d0400a04140d540740c1400510f00310f2a9110124040c0c061404038240e50410f4020038ad01000b12048030300c0030b90303021901c0040c26400074024851458030400c0300d903402401147d1001c1c0d40c0200c8080b103c0454070548000200030520302281c00c10f02c2410081400005506c00c01c1d8001000c51449440081c07640c540c15990b10107800594100f15116070004c3d41c0055 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 45715957 1250 45714707 45714727
    0x91503050906010501110304030602070f0b0c0702100824030a050304080607020c011416031e030207032d0f0203040e0a0524090604020708090607080901020601080c10080a0b1203 78
    0x82d85005200c00d1a140c40e40c60030100000b91280315500001c0c29443c5c00040d154188a840301c0342500c2c0c41d5000100e0b2116180ca01c6001c9010381000004a2181840ca941c0030a031034420842070307004002d400b1540070091501d444c0c201d01c0c949240f04c0076805000f4080e00c03101040c020701c080d0000304003010190175946800c580003420031080c0020303241405803030401c2003001c52444013a82c40301000501035110038002800d0075100d1120f84a0f0110940ca061408540101c2d4150041c025891194680744900c0000b403000c81900740c50b043d041c5000c0008070541c94000c0e442802d010303c08400074015646401e45800c102071141c2e100b00c8002440d140c031842806515090b014840c40d180b14003010400010040e84001080204050405407069401151031340500101404640c2d0342d810003042e25540b5401c80c174294603170f504003c000380d0160040380c0000601e01800314a80e082c822000b044440405a1600141c41840b0301408204080c0da45204032602a161441c0d1400c0b403002e108015034889a00388 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 45717207 1250 45715957 45715963
    0x7030503071106010e1503010f0c020d021612022202030403020c10031509020315040204081014010305060402091005031501030b0c040f03170705072c190b010915030509 74
    0xc0300d2030126403203d40100030f0129074054040e081440c0400c40da0742d9a030400e00003805001015408000b80d0314000d0441c0c00d154001856203030400180d025100025400c6006050f907c80764420301e00802c02d206a07050051412101c8004c0c104029a5625541c50310001960200d8108950440c09a03204501b0003506280240502001d892545018400d061500c0804a4100c071544100000c80b500030000c14881106031601503064080a00119111580e03454802d58030a4403541082a56141c5107800308075040748890941640e07080801820284c0721070b400c0c03000c1100020300600c00346230649004600c1c0c0da0203021420040362010040917039541113003012404444e01a1000d4184079080000b0020200e40b00185400c03250802062071004651444c01803e61066000c020402e00a400000c200c10b400c0c20403061441c00881640506042c110082e074042d040280c035051050640030703010128400d4550060b00440c4410f26104404903611407484454080c030380d002e4800702c0e4690b000c00215450030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 45718457 1250 45717207 45717227
    0x50703091e2f0d02030c1002070509010f0303020a0f0c0e09010b030c0103051308030c1b0715090501090311150406020c0906030c061207211406010f0504050418080703050307 76
    0x82d41540382d00c41a80c028141c00c04003921201070040c5440c1051806555041c0720210390213602820a801c980b02c0349a000f5110056802820710666032080085420342250b0752040c20f4990580080c6001c1074a030311039600340398020b03804941c40c0040c6c001c08075050721718030002070048800c14000320b03403035030090105810300c1c04503910141010300d000304225188280e003c240304110380224410350340340c460848505207885031040d02c403c08000c0c0180d620141100046203011111841b03c01c058211268000711001e0001d80b00300350005541040920200d050341701a0b21420200400d581080d50003004119185c0d0825844000035070000d0034003030b4a40c20101c0302c9690002044010703000c8181c413200010603a000391603100038540590400180d0481c0524166150218007003603641021380010092009072030000045403c0000781030115149500800301420000358944551f4105420b207014800100385108504060404840c106408101070030000c0c40401d02a0391050340ea8a0514000b40c082000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 45719707 1250 45718457 45718493
    0x60f1d070804111203090306150306010b040f06050306031f0f0b0301060e010b0306010504080a050a020a09020a0e04110405060403060e01050f090307110f090708010609050102031606050703091e 85
    0x3101d41044001411030381c01a2030b0031411524007841d18440c0c00803e1460107100f02080d0184144414000c2c2e07002110224007107450308400b100c09176030b01d0350410102801648203201c0b40e560b1540c0c09021481c0102c018650055028003203d60a07128146c003900f42008414285003090350b152068001c50760ba50042000c4903038180c0c000d12440c1e14190070f03007464000503c83c1d00c0f0402c4c0007201141c07150f2300c00c038122002080d01c0c40071280265031604043c0e4a60f0503400040388644008036001814210b68001c1d20940c40c00d42d100ca14224520a060100be0558143d85014031801040045615910740010380080c6000c2c2c0300000c1c0c88102c8000044c00c580c409484011251920010000c506400004517103001da84010110042500e40000c17500c1060b203a040143d200d070888080020450380004140d04a500366600c140e0200e40d031782c00583e01c030310032106011b009131007244d0042c0c082121a0025600800c1c540340019020b03289840c3c00182030321003241c200703815442e10201000e00c103180e0340c0100f040340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 45720957 1250 45719707 45719717
    0x3151003090203060610031506020d1812110102010e10050a1d1207020f100816181a04050604080a0501060905070507150f020d02130e0405060c0d060f1d07 68
    0x1d22500002d40d038032001800684204038003005008054800e0300b100204490400350103403070342d444010181d2601c03500f0643c040040c10284105040380d6800351900f088403c40c90240800070105d40b2040010954884801e041d50340710380c1012140c8000300a60049281011000209810a44505010790700301c41c0511290003030301e41c5c41041ca5500442d044c09002c2d50007032440e07903e03411071011031101006406544e0740f0440c84c0e4010311100c0c0e000401c0300e00c80c00c81011076248043c3c02c803e0584041c401d03a00c140100708145502880004016031540700400150101242050b650380300107a421362198101805d190440382c4202c040110034080c4902908094000f0b203c1843c0404d8000c10394000d08001510f5009025110007807030030b195020507140018410203650300c0c0c1d20149000060340c0302010107203007000e008000084001c520b2080b14080d50380130014041ca0384962104143d030390852a001c11641d030707442e94009042d44000600100801040007500d402c450361100310840c00000414443c1402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 45722207 1250 45720957 45720971
    0x60603070305060c0a120c050d0f090b160207120309030c08010e0c0f011205010609051c08030703091a0a06170c030c0402030a060b030103050309030705120a020904020d0803151003 79
    0x20b6004500c00b42c1c032058000c5141c2d03c4030401e510884800c403240800550483c9040141c510450380840100604031441d5014040d040c03d0300c1c0308404132401d84d40c0160104800801141504044031440340a0062a104032101c4603141c1200c03c064108908045001c560044010401c00004032902801004490000c03c8800008144240c0b9000b020703500034401d030180701014400368082c94054036402e0041c0400c004968541c030000d03120340d5442c011a0f21032054104103c00852010f440800385235032110700c442c1151911380081c0c001e070080c04000c0700d80011101804956210b00c000311031007100754800c041610340c58410b68840b4841d010003a42c80580040c00f0308007450310001155000c40750143e1340140c1d40c3d658020044000c4c00c40d900181d00c1003030000000000c3c4030000010b0804200120141c4440a03078403001c0140120603c110071400340c0008000740007500e0003019281d8050b0015101803003012080d40d54102c03079401204e4282c0134541c03d001480813402c2c082c40f60340c008031450408005507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 45723457 1250 45722207 45722213
    0xe13050c0613180e010e01020403030504050f030304030f030305040309050a050303070b0a18030e0907022d03071509030f020c061b0109020303070f060b0105071203020d0e100c020606030703 83
    0x5400698032403801103070000ba10a000300e10040c540801040ba10f480781040b03221080348880502507100203100c8960901d02492007094061003158122035068452a20702481e020900c5180070035a4211079240c08140000008107041906460519100341c1e0000346c603103403034034000c0c01526407908617a002e1382916a081c05540ca000007101c1d80243c03c091010402d45e1500103050103855074502803801c881002e4000ea04144c1c104484400e04441213a2600707440d0b40b9410100d0b92003141c401301001c21800300c0b000d0301800000c500380404070341041060300e1403c0c01c0780d225030706030004221001407000e03a108450024180d00c54900ca005101c03601c060000c0f80c0900e0009409400380985400811130903e208110400e4258003610744c1035406000c3e01e8172691242800340b011007040d41c0998440c0d092100c5404c866228a0032603102d160701410582520191110480007074003d88241c41800350313110140024044100000d501400e03c840010032501d1103140001e05003d000740c0000c0c002e610090040c000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 45724707 1250 45723457 45723463
    0x80109050106121515020c030106090e060403050714070e0123031b030703020a060201020a080901090804121e0c061704110405040305190503060405091902090c0403050609070e1305 79
    0x100008840d0209074130004140d1640c000045600034100701c402d40d5201d10b04290089400211070034114020802c10356116000025540106049000341e0003a400107400070340641c024152107805502020082e884a942403450007550340c100c813501404050040022401291240b40032050140708078210074540c50109944e40f1402a0075544003001c40d011480c0c41d00c0c2000f4900c011900207108580d01a900c11002c0d000f507001c0c61000d400910040d00089071880e0501454a800b5809403c0604d803516150b0130f4428080242d8080f500d401004564880c4100b8103480c030604580200310f4043d013030f0300c0c000b4041d1031884c0c0c6002244c5903217202c2e8100000f00341a40b00341c3d52007072425540820b042e520781c98111010f1080c4402180e5020030b6004100c040ca41c4031010718414207041d14100581e490b44801607a589100008882c130b4051444650401030803c5210380c0e420260341009542030036200d9480341d0034a41c040750b44040a0f03005903410820900f40941441c3c008400d80d2068031880401e445c0c940d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 45725957 1250 45724707 45724727
    0x804061107050a031211040e0402030c19050411280813210203070206071a07110d030b031903050c01140907140d0807030804021302130e0603100501060f080109050106 73
    0x18009111001c2c10359088641103800b8007408003000b1b95a481d1a00e05500d84080241d4090b40284110110180e04d810901e0300d003083c0760f65107000000e80502d804108009400741e9000c0e86141301092000314410480440c0d00300009140c44000d003024462148001d0016100809840d4200d20b640203101c00b048200c20205000b0301842c0100380c0c0c1038039803281a0318511400341c0080d08071500194031005d002518000308416000e040400c41d00c0c0d1516a412252650f014242c0d007919001f2000148040303001c2d6000b07003002000941601d48200b99a1084448640e0f0b44206402080e000035a002c0703400c40c20310844180317240808090ba5141085581a66a00e10f5400b99103410038100c40000d440361b4461000c40d140f6a4044200d0f0307660f04480c94000d110300426142240030b000e6078a1580d5140c1350038002d540d001e10109000c0340700e46142c8010140e9965001d0718050301405400c1d40c201107040b460240c50701030b00c2c0c61f844191443c800b28038004c14002e0141d012008003454900140241640402d04513 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 45727207 1250 45725957 45725963
    0x1709090708160315030b040b0f0601020c010e010309051e0703030908010204140108040609242919170f06090c090103080f09030f0c011b0f020904050a0804060804061107050a 76
    0x1c01104e0f941c04d03400090712036000508188080d000300420801c65130305542c821140c00c480604d42d902c031000103a980f101103480040c00308100407101c4a05512a170f02c5504414041c40032528a207401e80307542d1584400c050b9a040d0b090704082e20074810305400800d20001003c54400841c5401e103000558400384898881281c10060f801c0c010402303110361a040410b049410000c00e12000041d030a03c0074078004100408992a07080106c040d540c030340c0c080d107079411010780d18100080ca0400801001030003504440c54802c40c003003c082c003085202400c0344025040c965400105101341881010a01d00200202000381e01d17031108000c1820ba40750206118112580b10391f905442c0c0d6110545201140580307001580c2600c1400714400c1000000586d0600034482030301c50b410300f030001038042e00120a42032000740140d0005080f503001805c00e4040c50340e0090041042c0c41d440c070503a82c4e61200b80c0e80036510900010740740009000c107008203803145c0910a5200e5400a1401c90030f9036030f041c1c84064808000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 45728457 1250 45727207 45727211
    0xe07030b0a110408060109020406080106080717130503030a0608010b1203270303130906061107031e1a0415020403031e03180c1403070303080c0d060317090907081603 73
    0x1040460002d407054034080d000420945295607180c058240080d0010300c1400e000a41c0203000107516400303101a0b0f80152003d503034411440301091071800507664040c4c51020b00a503800b148601190051000d94080c0000140209072180380c020705500b522519030001740701d1250074005d042051070000466410743d0701e00443c414000c150035140ca40d41004190b000c1e800d80000183c230030b5501303000d141400989980a100300a0310303440e140110703041403804055100540c0064070a2001c030f01d20710741e0701043ea0350003c0b20740805001c0d507843c130340002c4081c0a2005141c5041c07091108005090b030b15016025454807045080c545907860003000e881c118000540e54112040040303030264400e0b000201d464150068011004100c2c1ca843c4451080d140f16000710070490840910541c5000310710701c401c580d055aa40800c070784449100b401c9550011586012107655814000300086100d80784669000c030b60001c03c0d4441c41400c06000b05000300500d83c1040020003010003031600035949048400030018940 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 45729707 1250 45728457 45728471
    0xc140a0806042a0807081005010c020307091d010b100801090c230414030705010512180a060207020906010801061b0201050706050c0702010f020105010503070b2b0b040e07030b0a 78
    0x2c98001c201c4103040c5104000494010f01034054450300c0250155060703078443d0000c0e071350088125806c90041e10f40f041002c01e44c1c0c10802107503100755455401c6900041c1502c07a03c9984602d040100c400007114049000700920501d9900740083c41240c0300c06406850001610807052801000c0000c14040c00710a0341c1d0726081c84000a11540365a9880381140e000c0300a2007500c1c020b8285940c01a11420380400f03040c24a40c04141408207131181160810b071102801c0c100103281089405400a1001140e50812701d1003503034091041100c09100c90082d000180e8030030640c0180524444018000c0d81031200210041015a03401108005240ca40c110f42c204800b40a01c01200c8600c24107001514032800e200c20302072030309008001004403a100740c07150a003030140d1080590a880003442007540c55013003c5000c1080c0120040105035019130541e18041da50382c003000e44901100c01c1029846010750f1200c03895080d00b810302c280c80c0041d0041005101561555480c1e0104c00402042003014507150301e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 45730957 1250 45729707 45729709
    0x180c1106010308040e090307050f030405030f0703050a12020a06020f0306010f0512010b0a050705031201080f0a120807030207120201060e06031506040f02040509090319050406020a030c0302070f09050a0c140a0806 93
    0x7c2501c58440e40001643e0b01303a41218040ba5032500300c0e000e000e210303002d0343c4c00c804030003d00014400100c070fa01002400c02e00c02e00c0e44640c2240030012070341d80b083d40200996000061110710081250300203c1c1d90b402c0c2c5a06001c80010000508442c01c1e41c1401810401900e10045900e80581143ca101c15141d030303980f201c0c5000311018059400002d2161001048041d0070108182120b416a4090402c075140306190b004090f5036001503031000360800060720001d000c40391150703d04688c0300304941000340c40d00015030703505030b03086400b0010040180d544031780611080d0860410583c03c0807045008107407805a074400ca8015407000780100384220f5030b442446692010b0f80c5c0544008100040903c0c20501c0d0511102f6103035403200000d640c0c3c414481d080007a10501074016a4142d48140e80101640c0819950640380740140d158250203600c148080010134548000d51103019101d803640208081c1440080482952500030b0542d09000ba9500044140880c400c150303181d05200d4900800103448242c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 45732207 1250 45730957 45730963
    0x250918020616020f060f07061a0907030b0117070809210a03050402040b04060803030103060f060312120905010f0f0e03090f090a090b07080f0702010b06030a0213180c1106010308040e09 81
    0x10079604150040f07803401d408041d140113010942c2c080ca506109d80700190070114001c0c141d008001d540482c02c1c3d4041143d15210b80c1c00030030000c07418140709030a03c2440001044c01e0900f240c600000400c280704010300000d040c000ca112444024660080307403180d6940c418102d009400d40c6204060f5100001000d42d03480740c01c00702c00d008000d8820407003651540c01d4a5202d6000340404c0c0d98407030402e51005c1164400e4841c02e0300b12a00805120090240500210759000441148204481e03c6103000c8011540070710a1200c0380e000380340006404c111000e242415592040c134604e220b82c10500c441c10054440b80f0440288500c1181c4001e015680e25003180e0052920100150000d4a11030070400e41e260080c175014010751700c02149400b1640e0340d6200300d00f62800d035a0301541000c414004078510300900d0700509148800404806045600e800c01c040441100c541740e0140e980d21101006801500442c2d40d690207031011020708034540c11a1035551480c4514490084810300c60307000140c0080d018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 45733457 1250 45732207 45732229
    0xc04090b01030b060409050405071d07080a020d0606030c09091505010f110a05070e0606070c0b0a11061501030615050306060a0e0310050928060b010225091802061602 73
    0x8100c151501c2e102c030081002011f048600700c6292240081c045800300307440f951078542c1102c0e40d2468042c0c0e91034440445a0460242880c20341c2c64003400204030114840c02141e02034001d66900203265080d180d802405103811390302c501000b41c9044c03021040760313030100290306c1500e00038241100c880c240420704481502601d003304440b40500c6200c0801c2240224444d0200c90303850545030f1990702c880040000340e11402e5001401544100d904020340d44002000c0c1510700c0b900d051000c408904010006d00701001151280440e80b220346001c0c0703c42d07070180705150203403640c610545011810b00602400a2001801061183d0720100e002300e0481c0c0314844803041e080c00034040e110802032200f24000a4801514000c3c0c0c540110329107010705041c0606e20751084030b2103840c296444001a259040106242c5400301d0440c050002c1a581c80341226809d049100c1e5298040300004ac40c243c5944200c88083c1c51001c0c0e4603030004101ea0159660b403040d030305072007000749416091341752520002e0180081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 45734707 1250 45733457 45733459
    0x4060b011806020c0f0f0102031204060209030a05210c190807060626060925030218090f070608012c0c12060901050d080c010b130e150c04090b01030b 66
    0x74024001c00c456074040f6100d01c1e00d2105031100907121801204000c814000a414240103900920001643c1400c401c00030b90450b016200051504800c500400e0500444000580d007640c000c2902841295250151031100350b04810701900301426403400f03584980c1c03054081005d40c00000e80c014280100c400c00c035241d050b4440b00821440c0d1760b400004150959200e000c044000c100103403c190508003094940c030450000c000b41041c10080e060030000d042c0c40181352101109203036808001a1108000141101c1e0030b51900c0b5598034040007858549054480e003500c654010507820054550040c19450541701000f88610103080c0c400c0c0911010b2070600c04010b1014016000d00c90400d80340c2e001824401600408020190307103407000d009501d8070a110f42e40e004407071001b01e40c0104a403903002e0304010150000100d00161100000b032511102d141420402c036a543e46490070424003006190501e5070200540b50443c40d0056013a000e03401a17202d007604007500c900c4a001540e00ca5403021042c2d0344 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 45735957 1250 45734707 45734747
    0x40f03020105072409030e030a050c04150302090f060909030a0e04110d060b0a0207090b1c0203211201060e010804060b010201090203030f03090d020a0c030206070221010902010e010e0904060b01 85
    0x1590060703007000e0305d00340d501a0301188003401c070305949040216401d0280c0d0b401c2002017030181e0240d0140030040100d950a2512200c0034000400140c0d280809030340a909034a0503444a41051400c000d061a40513011030126402002800703851900a032a40440c09412100011200380c0c4c5c14019070503100d80c001c0b05a001d89412804101000d82ca0090402000d1903402c842003d61503410745011aa00904880da00c1200710007440e005400d6159280c3e0900d10150951300700030710707882050700d40542c40c107444840350402044134410300c807218802d40d004100c00d1034130344070003030000380042c220b000040e20192555072204000652a4001d41140060560103400c9a0741d450120b426488150003c2d9002c51040c061052401210741c40014250096900591301210952455003080300340d5200d81400c0341c102d20303011081c6543d01d40c400606003031400d5050020410507405d10004280002002a06043c0001610001150348442d4030305a4400e078440000980c1036807540058807807000c001c0300141540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 45737207 1250 45735957 45736013
    0x6031b011d04021902011109030a120c05100501080c010302070807060b060f07140c030a030210020c07050406150f0203160803042a030b01081203070813020a060504060e06040f0302010507 82
    0x51100c0040c3c0d1380012096000304421039030040011900c0c450304d5650395042d4841003021010859202e0700a441d6241410401505007050780ca040c104042011140b05243d82c0e01d004100d40c038410302074201004003d180c11454a40c49649030303003060090310009044103503115580c682945542e0215440c1c42c12146a0303a465080c20f280914031002103040c00491402000403402c602d05000507103000c107a0381034000c1c240b01c9020615a10094004140300c0505c0d105000d40018162030714410000944100046031b070402c0341010001e00542d00d04e4041e041154400c0101411812102144040b0540e010301404e94a8840382046e01107607280c8540d4071408120f038402c144c407020400018004981c4141d480c0249684c1e01d482040d110405035400ca000090308000040440f0b1082d0303150b5a2208158003408800700140d008110702c96103a8000c1d0000c00d4000030140100c6400031065050094119003492400c1d04140c0c010351030486c7c610000381070090210b000001c1080e502c0d000d004070907104242d04008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 45738457 1250 45737207 45737227
    0x60f080a0201030e03030108150403120612061b02100c0210060605040305070e090307140109050601080105100503010608070605090d0602031006080f061809030d0e01020a020606031b011d0402 84
    0x21400180d00300c1c08a403074400003002001d404000d40b4125184280036080b01d4901c08808040c80c0801402181086005c1542010150107403060601a1010100001c2941c0441c5001c100302c40201c002c00100034135251300040044e90010f02250580350b406008184a11003240c243e00c0c0505052035035001c47d003061381c0030030207e521402400440340242c3c110f54906079124000481c603001a141030000307400030410540810303009140322000c49101c0f000001e5523400e503211a400d01d0001c2c0c0143c070290b51190148101c040c41441280085e000840080042d503281000a55840ca030314409c41d0248080070921170002d0b626041118030b1140c0111066540f864510142c2c494410300e030140201160750400801da9042001c00f0741d602c5404040c1c03008160903098050b41c24000c00050030008544420041491031501602602850381407440000da140c0c0e0720101d01074200100201014000e0780440104006142524801d12a246003828030702c82c1c1e5026002a000d81c00c1d201030b406e98006000040b000d1175 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 45739707 1250 45738457 45738463
    0x316140d0f05101508010501200a050f0c0102010605010206190209090a0b030607050708070b0a0f0e03040305060105100503011a040f080a02031203090c04051e070f080a0203070801120303060f08 85
    0xc1402c1c68682500b2140c2c50b2030f4128111038841302c4610005074094014042540603986402c0c009021103000945400000309040c60012503000441c1c0e81c2d0800e040010011000304071120410900740003e200d010306000000b07544010007044540501320848500d02940041d6049490031072015007482c2d1640707040e0004401070700d60b580c1c225004e84a4540018441c900c603000b5220065400a00285000841c0c2c0310354508403000351107209500e640310f0001150301c0381441200201d01c46500074580700c914600740f2a0808005910880c02040346411410441d68490b013120305403586001100300045542028165501568021028640d03500001080703c1c40c000800e2040325108074200c1e10f4501070b220300e4282c140000c0c1d8101c081a0b1001401800d54501030304a2a403060b034101c82c080b0205051b140310003601500b81c4600000c110210030400d0a00c0d031104080b0307441f00c1c0400c419461400e00e290002c1c00d802e41440b92041600c02d00e01070300c0400d0700ca41c0020000300803943d41e50003059102c0711102c1d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 45740957 1250 45739707 45739711
    0x160b060d0209040506041b0f0b0a0306080313170111160c05060703030516020d090b0a030b0402030a050103050708010b0307030f08190306050a08070315020f0c0304030b04030806060316140d0f05 85
    0x703200180e400c540d003400340100387d004107441d504681d0b104010f103000521003107900140411000d040d200c42010039103040c108080c00441d840711444038611484d00c010102c0071803109150400c107174149a524031054485000321041c00410800780101c800036400c0603041c81060341c00503644a040011410180365045c1c01440c0540d90740031002410f00e205100a90303460b050b119200d000b043d00b170340040001500701c00141c0720307610b11810b01041c1043c00d000024100da0046030181121b50b038880c010700912804001c2d40000d400100000c110359081d40000179034544003480010b000c000700d007080004000804094460031001c0240d8a002c0301d10140c0040e02404890140d140508540c12000031109000204901202d401490030302c0c00320401c0c400c19010394055060b5040d144002c12150503d420104024001980546160013035810540340041ca080c50140c01280720790024011300c181c1500c0000c44000c1d801135424001d004511b640903001c000d000b8080d4107181c0700d180284030f60458003d030300214 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 45742207 1250 45740957 45740963
    0x4151406010306090b09060603070e12010903020c03030a0801030206030c0c01020a021c2d0203090a060c0b07050301031e021201060305160509010602061303030204151211160b060d020904050604 85
    0x400700e1a141c01e40c0104590390119070030750105506c00031491900304200110340046032407400302c0100c4000804682e0881d42c58030450700c0e1760341d030302e514805160f0706010100b1071040c110041c40c41d00d080001d0041c50380c0d4043c00302038401c42001010911241d603050441700c07802c02d400001c1d0744071540744001940b92140d0a031342680702509282c4500d060386c030600840c207100701c0d03403075182c280b0301a6000c0c140c070038614003c8880c0540c0f000304205130103917031502094002000e8a95484255124a15220020701005130800c0148403040c0014400102403c3c0319450703407141e440103c001541c89000081c0b03142c0020407402d4003035191600203c00d211022410801058000b951064103c0d90746051210a0409104100068200c03001154901250f02c0c981c0600d940a850098282911344280b02202c100030f088038130211380005840e0b80081d030140242c15211420030074150902000108200081c0700100c001080160280c0004005a481101d8510102d4000d4040ea10360b141c0752400e540e503820203440030303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 45743457 1250 45742207 45742211
    0x3091305040b0a061505131d09011401030c0603091a0c0405032b0c0507050618010e040b010801090f11040602010507080a06150f05071502040f0e0402030d08041514060103 75
    0x924800003600030501205d8402044a484a0907640704840c42d41100d0080310716400b40c0000003800c02d107440c0ca01071000c80300c40036001d46414581c480e0f40c21a01982028032600c100c46004201081603a40054101c45a07401c010403072900e0fa103010356840f0100c0c480802402c107690144040114404090300507a58242c0845000040d80340011840445202c0340c1040d50a04100802081c1c0c45a5119090035216004661650b074540f400240d207500406800214001c1017400c0301244d690010030074401c01c200740c500300070b001d1000000901044050140800070b540b83d4154024030421603016003441424003445548440e1108002406464152400c00c002241d12001c036413002564450b540c11280d061860030720700b0328446006e903001f0f01150041d00c1032040502252010030000c2070340040e44171440c031005a80300d00b0101403c0c540704041d04100e1401c441c0700704100c0162000a12800801c01342d0904900c035546d649003002800e00c0808120703c8903030030250360346101c03d100108a40039000907201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 45744707 1250 45743457 45743461
    0x19050a030b010302070f0611040308070302010507090e130809010c052505010504080d0c030e10080105030f01020a08010b0702060f12071202070f030305072007050406080607020703060e03091305040b 87
    0x110f080e4041ca46001c1d15405504540300001295540400e0184001c209403a081c29030340c3e103d10009810088040d0007503511001044003242d8410b8031300c400703000305d21840000d50924000c20740c0c00d8105604001c0c21444000350b48030542e8043c40001c207585034004c0444055491405003076003401540380c400c01e104801c141c40402c0940c0180103840640303800500030a500003140301e046507030b8560201e082c0c05116442c40413503110784030020003100b040c6c11902e940c22076500d0901854a44051001051b150b07034814010b00c520203510129030b40c111208540c00d151160103a00020708540714801031220700c1c04002034440d404414090040340b003030f400d680b5481800c044040c0300000740e214110004100e11010300d001e4002138001d61020350459003601d41030f120300301501c3c0c00d0100090b10103030858660380258403c01061809000c0c500240450f00098045801c00c600042c1d0354004500000781070946600840e0b181d04010400d4400d0810000c06500084400c80c191070000c2c1000c1c0e07000d840a500c1000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 45745957 1250 45744707 45744709
    0xc0f030c0e0612030a08070504180e060108030306030d081005041b02010b03010606080606030714030903040911130e0414030f030105030c01080105101b050f03120109050114040e0319050a030b 84
    0x203d050340c6a030520301440c6050f1508008031503180b4001d2205040c84000d08c004111003404400301d44983c0c2c050f402c0000c01d00e8854005924021050f031203120746510400c00c0000d280c8000c01c004221100320305100050303440d00c07100344c20341d074140d500026006480e08800c05100d58038071181083e031401c5600200070f02031a02040c14242d031101d010300400304140c1d401080e01420400b000b168805440d1412518502006201080a0740155000c280c030764804a01031050000350320440c50800301c100100d52038035103404604d1140315414410310040c007420740c2c0041c041c0b10781c0700b5a0390209103454003580d5555444110303041d01f41e0002e0160500900c01d6481d2303102e07594000d240e8079050315002020a01c450600318800c5982d84010108c02c00341910340b800c102c0001e54100420000c00310303150051510340c0220b0b004000c0c6281d05038005114641407900401100c00c40d103427003d000352400c1e500400c81804c0d00c4034a07455031143c0b01707050400049441d440c2c0c2a00741c0c408060300c000e0515a40c18410303030790140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 45747207 1250 45745957 45745969
    0x307110604020d11060712080709050904020d02010e030f07060c0b011203020615120a08040311030a030801120804051c060c030e07091d0601060c05060f01061b0c0f030c0e06 76
    0x44000350040a803c01890102e100c21aa414101034010105481c2201da90364264043c01100b0050004c00d682d81c2c2444400360b00300416030017800003a550054645000c0d000184034044681000e811302c084a0000c2d010b030f480c14451840582280011260841c2c2d88500003040d01d282442c0c00d0350312452582c00420440100c00b4080384042c1c05500601c2c0342e4440c3d1140c0d40c034103035000c804280c3c8601307808400d0a507c42d05010f14500ba90140c051580c803a469820b000c1010f00d01203038101d04c00c2c1c00c05440715002982090318541907032041850000b06030f48900d452880c5109940110340d0140001c120f54108820762256000030398031440b018004c0c0c3c0796400c416030540e43c0d01c04e103400050300404014070078110303143d021a0949194103d4528212850480c0b142028400c1c0c01040005000e13410480a201c2e08111783c1d83c01480201c601d05107585807040040c4107030700d0140c0d12500064407504100030b0103c164081c4016141c000141d0220f26682c0c80c0408044119200ba82c00e10090a00080d14500c1c0070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 45748457 1250 45747207 45747211
    0x318111c05060601031a0301060b0c0105010504110403320c041104050a05010507020307090e03070302011b050409091103060109090203150403020307020d08040f09020702030f0d050409090602040e0c03071106 91
    0x40001082980c48840054024015a424038039500d00c0b05881b051031507409014207001007280c540d01325903544060000500b9904160090b5020728140b46140c040d8442030021502180c0d009101d01240d001291200d21100d0555182d0003c004160f1103030301d06044000c602c03142c05007002c0751b04114103007a49174020341c503004512441d0b5021001000401095004400a28a407403000f0152400b03292510b00c2c0c04219820310400440643c0003040c6181019024070581844082c101050480c0841d1900d0080c81441140141020a0340701e504403010486203510f00800b6860050941c0ca085da121410100204911a01a482880780300405010801e00f00c0700716018903050350142d4a00741c02502409060014070360111104a01048000b03400c4d90200d0a50303000d40406880135a4400060042514210715401c2c3d03104c0c66005600c04c408800d4011040341c040b030304000c2c00401e5148490428000900032640255000240c003001c0104442100c8021881000c1584581c600c4035200b00c4010380d00e01c41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 45749707 1250 45748457 45748463
    0x509060906030d03110c070806011517060114090301050726010e0c0703020703050a0b070906030203190b04060305010f05040c0b03010311060313050a050610091811010318111c 77
    0x11900c00c3c045054030a0300075035074807080058410318214900c0c0c266880e18080e6800301c00103070400c8005104003154606055001c41072480d11101200008110202030140a05000d06001c0c1c500d2200e84d501c0003260944008160080080016281c40c61001d04401a012140041e1004620500c1c0c0c0050b0491035080c143c0d081d05e84074400302c0d0740e0764003082c00d942d0046405405600c5a1100040021402c0200300c580500c50541081c1d0782c208810f014040d101590011000d05005004005016120300c802940081c03070a5408500d410f25400801c005180503000074010354285140c20724000074075000540070314454298060400c1d50b500c4106003601003800000c2c00c00340d03494040901071904201458109624484c540d94403056903171001c1c901011803c0c00c071011f400c09010070080c002005025002031051000611080d0811020800d0f24594107000034802c4611805c10380c03169111f54040c2d601c46981103600000701440e81000d0f8401c602464001d817123100d00070500c85d1042c032003032603c28006034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 45750957 1250 45749707 45749713
    0x6020c0402030a14040303021206010c02100e0103150905040212070312030504050c0a030f03020d0207080304050d0c0503070b0418060e040b0415110c0106050612010e0a0222050906090603 82
    0x2192008210180d80060100710000d51101c0800d0341c0302c840114060300907480381d100165180007100d894491240010401c0d13041c00181582140541c5a4034444c55100d92985000100e5090319801070b8011700380003007400d441c0b4840d44400f182101166006034041c034000c43c0d14a401e520400e0319a80c0c3c5c0e070f40c180001061f0210700340c02002d8103030081e000203800620602c00e40e1030704941100440d4850708168015078441c04000505428150140b0401002954a00c0900142c0d801c20248595920072881801d01404000c0c1071781c014080c4080051010b042e00409403810540e90382c50b01403072600315004007490015240f0340e40900503024446d0108403004441103000c240d566840e07a4101c200010010355000d08120a041000c0b415803007500260100628980e40b03a15455416600f1180c3d02d4000c54010107082004600041015803200d04480c0e01420014507582d60321f4551010f801f50025041c11004c0b0704420410510106000c1401e8a90646e944550340e51031404201070b4a9081c0c07540d64050b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 45752207 1250 45750957 45750973
    0xf080616180b120f0a0501060806010e0415060c0506070203090a0303030b01030207050d090f0603050c09040e070806090703060f1e180209090a0209060907080708070c0501151802040602 81
    0x90195050081d07140074580000d040d0303652802c01140c154010504181030481d0142000701c3e421a1202c03050708850780c400200103a60421501410030540a0300e05070600c800710225041c1e613903660b0007a0b50300c41030000c035000c04156501c038054407a85025400b12800e0040c50009840d451002050f609107240080030180400d14645040d80181f160008040c10540c00b04100e001042e810414a04403c02d1640c400c6a40b5160064481c251412070304002c00f0503042c10240481e928960b0140ca0007401d00702d030300003080094251301c1c516100d06941324107024020202042426080403440704220790013440144210b0003220709810841e20800c40400c0f4174401b004148400691a52000c10010500480d00040c43c1c102e40000e034580e20110f034075040592000c1030301c01c21820310580c482d400ca1000da4002040d0700f841600548030000003010319080000070f4002502281c420318075205120780000081107050360041404503515801d002d40e07030306c2e51046142d40d0714200f103502c210f4040b50126400fa00c000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 45753457 1250 45752207 45752251
    0x110108180607050d110a020706110c0102030414030a120e0a060e03030307030917070501021c05040b0c030603011b0c020103060515180402090613061409090106050d091b0f0806 77
    0x20313040913030f000d9031903a031300c162640b42e60f0a00001808542c0c0b25400501c2c00d20b240c504028500c1484070030508880d041600c2103000d598002050b901503e5410003000aa540c140d40820301c0c3c2074030a1b40103090b201715080b850b61100d81004120004050980320740607015102d01080da811035a50741244d800d03900800004408030f1003548581d6109119032616600203e5006a129603504840c2040d0f40381e950004401c0340c2c0440c403807a00d00703070800e15440070702552501c1e40710460071000041080a40c1800040010358950b004e45c003003281c0b070b440400d40082e629403007100144031009049040380401d1031b14002203918a07202194101c0048403550039403034910f070058402c5d54003903819412500941c09003d500544c4c2d440300041d2203581d44030502c01c6d1003e8030302000200020009441e00120b2207080041da070064840b01c14580c10350300c0904190b541d0f201074850081c003c200c12000682000c41c108121007800007503041c01c01c220f401110541103c1601c0d0905503803282c00640318104900070150020100f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 45754707 1250 45753457 45753467
    0x2808030901050403141c09180b0d030f1803030c05010e070305060601050c0115060503100f0302010507030e030a0c0803090a061103120403110a03080105041107020307030215070f110108180607 84
    0x242202170050313404002d50188070030f0300050501031038008a1300c41601480070012046c50380101402d000c10611007480140b0108410084280c8007030104a5160341515159003d0b400c140b903080701055011140a64908008091011201c4201c60700d5080658a1035417660000344501a650401d0181415840e283d006403401e90140044500b295242d01082010700c0c143c1072900024003060311800c0d580d18044980c9c264140c00c1d0f4100c400d1035501c4c04810b10140c1d034824213a40071580d05060550407040841d0000e41350800010008051070070341000070600034408000380034640802e907043d030f10103a01d601080d59026990b1640c0c101580c020b018060241042c61603560301710380030b414180b5070801c042c5805410604041c1d410f40100384024010001d03400c00e8860120001c6030074200724184002c81e40080e445034030703501c8040e01c40c0c00400104020341410200304c0340115807080c0107540000c0e9a00d001424030f80a6140c0c075021808183c00164111081c082641d4550030360b001900f5595108001920 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 45755957 1250 45754707 45754733
    0xc02041b08060103020c100908070308010509070509010804030905040e01090303060b092202040b21060604050306070806060408010e010f0b0103021908070203070803130c0803190302030a0207022808030901050403 93
    0x2844c0d12a08440e1f0503603010034030814101501400760382d6518800c508000d442c03194181e02031801200716a08001c2560350200c00d40f202480300b4a8128074945603403c0442e9030404981002c3c0c1c5c07040c50a60001e003c1d0805503c142d002501c04d4900340140c0303903a00c410001034090680d0142e0012240340007100e0142e041c082c40301d00700807171360380041c200741c0c1750300e510b241c1c50308160500e14808121622125100d116110034943c0141c040310707040d00c0c060034440401d844510141c0f40209010681012a0030344da034600c25030740030b080c0410080000300c0a45802902070207209503855a1a8949a10380e10654030074002c5403103926100b007920200440d08081145c12a100400c1034086020134840d0000044140c03000310301a4410310103c1d18410042e0401c0c03240158540c6c0310455942c0308000000454803400721903250601d4a040042e140d0703036400c10110180c812030038025484100b8004440f030580b4080510380300000b8601e00c02e40b102d5110b14003183e43c1e12428480341d000c144203010400000c0c242c1d0340c40403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 45757207 1250 45755957 45755977
    0x15011b050312040c0315020405010c02090709081006060e0a0803040302060d020f041d0a0509100c02070f0f0e0106020c0a0b031510080a14040c030f030c050d0c02041b0806010302 78
    0x41e142000d8104500412981a0383c11070740d1500c00d2108106100c2d00304010b030040b184956085141c103160a0010b0001803c114009003d014018000b4240901034840c40c1e00a0030088165122004044204030046c455030180c00045a0028501f02d0607052014140c8190384c12500210310b0b29041da005c0088917088800c1900340580c08000150807040c003100a0300040000c40014690409828102d12000e40020103c400840c42d00c0100204d2140c0022180040a0340c2400003420360f801810407410407a160704a13840354003e40b503000a54032100090002124811810200241d80703401e0b0807070722002c042c200030b40e01c20313448032050150300718910045400c0b2000000a0031003644c1400441c0e03210b0b5400140d0310110384503800300000403e0724000c00300400c0d00c06940c0d124070b103000d9a4102d049081c030700029105146c4603e20208050080034000c52054000048135000020040020080c1001c510100c0c055420b088907413458880100e844410403007540c8400301035071b503084011002900b00b1038106c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 45758457 1250 45757207 45757213
    0x61e030b0307060c0503190c020f090f06040506010302040306150312080103030f030c050d0903021506120715020f0723040903050d0b0a09020a08010306050c1315020307141515011b05 80
    0x347c41700006610a4002d10001601d690031104001d0040088907604031044030700500c404420040b82d0704428404950094040310300040c0c40d2244030040b0000c0c0140c1d080142042d1900b82044c051404210103002168410b200c003101808116104444814084c44014080340c80c06101c2d049942c044e800040c02c104c51403038141c0c28201104603c0341a2862a141540542c2003070f030700305240d00309000500d030380900103071000c0d13a10700c01c81e803080340e960006440b490a20003600d621541c440b600c2406071089003e0b9000844403001d840d50904009482c000b21480101c0c000c0281c80a03190406018409a03290507032079140c01c04581e042ca072070140c003201001c5079210706151404a090f0b107152000e011441b086940d011802e605500d0710354100c403801707403040300d4101d02801508410840c00d11404281d84c10800d00403902c0050280070791030360094900040c500b400d0941d8481c01e1620001d50684504554401e01c019034490144411402e2104060b00e030004003042c1c1e10024041c0070400e00d400703641c490402c0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 45759707 1250 45758457 45758467
    0x70203100c1b0303020a03140912070503040e18060a110a08060d050f0d0e0d0c030305070809031005070f1d01111203090106080f030c0706120b030106061e030b0307060c0503 76
    0x1c1003585070082e104a010036070102d0000a429814481c444d10008a000089030034100250031980e01c0b030b0101104440210001121b00400006209031001802d600d61f070030342182040c580d2480c8100d500c001d080d4070f5104100010b2078030740d0305028044111140c0d04c0d4803442e20071521422588410010142500076111042407000500c0070071140c01040c5a142c00b0b442d0002010030004c0481c04262003561280c00030700616030119250034100c13000c0720360505084d59a08881d1070034141c60f00607403041c0f40d810f0103082e00741c992103100b9401c8075100380b0881d03581d1086040c10b00c0303003031f580314204100c83c0c0502c012120800d9180c1d402131041d249420841c104840c0112821281c0094540c0111404202030b519000c0411540c00100010194540154091400e2031403800e03a1a590740070500c1030030100b03c0c004045030140032196200c0c03a5091400340013072108035155800030f810f000003084940464600070510820040c820710420b41c403c0341c018060f2100701c1c90440704803914008230505603528081003103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 45760957 1250 45759707 45759737
    0x1d030406140a0c0b1501170108030f03100312020c01030605041406060309030d02040312021c08190b03010203040b0402090a020a0c0602070516030c0503070b12060d030e060a08040506010605070203100c 88
    0x1564038421050001c4817100345e0b507a00001080d600741d030081004d10b0070400340140031100001c0151f032409000c018889850342e445003400d07400e0000607031000c2d00400ea000845201d8aa020803844072003102170b281485655910130500c800c5825410f8880081d080150100e4440e290140007150040c281c2d108503400c1c4080c21028078103d90003540100c400d011482080e030b2000760148031200402403640301038a0080f0038918043e01917038000f0180311803c003007483d0700390103452250f1106e042c0c4940503008548910701031403c0c035060041503034180d208540c142c0010b00124020b008580220280755242886c881c034560381ea9000e900b000000b11050b00071000044005e80112910200840c01046403009103441e28090509042c529003101c001184100841c400d10b1001d0100c2c260404801e450102d46200349040c01c40e441c1855004180c3d1001c0b002864040080d400042d0900070350223501996902c1c1d91302c0005403403034800c00100a405800c60300c0d688410900035845407407054114105858142c0d6140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 45762207 1250 45760957 45760973
    0x80d0e1204120b0708090303040b090a0b01060e01020105010b0a0e06030606040302190e0916060503072a0302190c060c05010902060a030e060f010b03010b25061d030406140a0c 77
    0x1800c014140388802c0201400d1200010b00e40380c110f009818201054102030742410303221702c4010406030031003040602240c54410708002004060f60408004842940c40b110000c024000d00b00340980190700744400410001d900344200ca0560005481d02000001c0000038011550030040000f83d206105000005c056100c403084c94090101d0100845134080c12300c491410301d0040038014684c1c0e94400c500310300c031100c54855014107075203440c10150348a41c2d501008480100c109520b01104401c00015441a41040942c0c810698829001e4070004440c2142c20814419102d0019201540520f4204820b0303004000103444035000e00c0001c603922003550040f941c40e034040201100003958803001104259014006140c21540e081220240e952600d0f1140380d1034081801401000e03100090003800341460160b0344c9050441d00c40050801240c241803c4008158940c440030038003201441d200300c840d82c08000ca41c2500c1481d101c0100c003107600c3c00885543c4d007000785014140084a051040891044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 45763457 1250 45762207 45762209
    0x8070207171e010b09070e09010e04060b0a030506070f020a0b0112031101020c06010f0b12040305030604020403020a03050a0b01080f060103110d1e060b01050a02060406050a0b060f030a0612080d0e1204 88
    0x40b00011440400400a2128680740206500b0411050080740300c6155034044c0300700e045542c90444600f040e00c0350b041600c024003084c4460b0368040ad00310000400c100000c99901d200e10110744a0511204104034103903118a0102002007000c10480014019007041e15203024610380a40b8019174036080c0c2d5624a801c82c0e012a04000705940200010041e81784650301e1000900990b00c8004e08007200301c1f00c04070300e4410150004090150100024016494540c182d800560b00100b545d400c50303549040894030307080303901000c0e540c0f200a0000030801010008440d056840b4900003005283c0c61621541c02a14070302400b80e034004101d40075000803070003007248140003461911250380740c44103c5c0707041d0088030102c0a50030305010f0240b000384011900414207640c0f041d0403807400300750344e41d03003100010080041c1680c1700c2c0c2c4a0b00200c1d026009545884c0076521030b44252904200c0c0325201c4001d2081c2d5159404014106030040020342d02c49805c1d40c00589038040030300100c4400400c018641c03d01074000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 45764707 1250 45763457 45763513
    0x3060d08040305030a0e041107151109040606030e060702060105150702041103070f120606050d0203090304030606030b07091208030c2a03130504050c4006020d0807020717 75
    0x40e40c48603110300e240c04c1c0b113160240b0408d1540c1c64500405643c480c01d000c104116500070349940c0f2040490400b400100b10341030f144000b041000703070366200d035009001484050104040c0f4442e590003e02034034000980d05050301e200074061100001c0d0203000010650051000700c0e0000e40314203050107a20054400b8502520554880510700721168000405001100b100f5410b55030070400d0401580e0341003803c4601c44030014601503501c1d80c44080b1545540b0542d0310080142d4900312000040c86854110311380900e400740d03038405a40c0d507a050894040856054081c2c1208000c001241542c8c0b480720003000d01d20000c040e41d50348020890380764050030781507040840458000164000c2d80d1a08000c10703801811007282d0400060800c240c401415018011b5000002e110351001091080010803003070b0800500381c40011801280c03203421442d804010300c07844002d4800d000b004581d9030300409a00d40b150002c1da00508240d840d000000860660b146002a041d000e500c841c041141c2c22a002024400c003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 45765957 1250 45764707 45764717
    0x212070f030206070207140d021507060b330a020c0d030e0102010e060c0403030302070201020a0803010f0e0f070f050d14010902040609080f0d0c0213020d06050901050409020603060d08040305030a 86
    0x340e050190034500c00030311032011900609014024801041a412500c2c802075170040302c14540381c80410140980380c0f005208801c40411003400308216074010b1064034074207950031000c03030002c2e22450b000f002c88040412024140502c000f58070f000408058000200e051040b507407a01606004640200203060040d000100021140f1082e960240540a52600350030014241c62520741c00488550180303000042c1050b0b0001858419a84204400324a00d50051502940e0f5651032408a070300000a201e000401e00d407010016080c29822a00148508520745031070405200e00d400c11161580894690b01c0d03040e070340b1140010840c104451003800b03480307982c2c40146e036036040040180403031405034400c64090303008908140c0000c001007042051034410382403c01c1581154800140d002e40b25503404104c442c030106000700000142d4000c10101c400645648000c1d03622082400f05031505c002000e50005005c00104020341000c4110001d00c501942c020350825450f9038607c0d046500c0300c401407000071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 45767207 1250 45765957 45765983
    0x209040b09010c050723011103090c030c040209010203090d0206041a070c0807050a0e0c0f0324031914010b0303190806190603020a0908010f0603050c0f090610021207 73
    0x4240f08116090425090550400c0c0c40c40c1c0c0c401440c0554696528800c0a042d414064030032001d40000b024100b03000c00d4251a850580506a40c45904400340c500c60710413a403100d141c82c1011f208072900e040040e40a0f625008d10442400b0111058142c107d0b0019810400091075400030401c1480700261180d20650761030042c2888440c0c0e89094002002a41042000700030540d50f01c4400380031104d070100490b5503543e80c4030281d101030040c00d06603501c20100204004107200702c04d10801c503010681100c8000d4803544428580c1d03440f040c8541c11901e1a9080b40c3c0304c045246c1c0000c1402d6051104000f141030803e903408241150840640559441e81072240e050f00c15401181a9034460000d6802c0400c900d41320b546100d004200740710b200241540010300c1e001843c41800808003a080d0704d0000e1241c2c0c0c1481c440d810041070981b00603034a60207031100071551803411361841d00704000c004000c481030b51640c03810460110840150b00041d4402c034a14100e040e408400500681406028011450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 45768457 1250 45767207 45767221
    0xf10030f06051915020c041503030f0f09060e190909052107060e010b090c0a030b0628091205010617060f010303030e101505040c1707050904090209040b 67
    0x5145240c201c5440f42207401c200320000e038882e9080300101e45a1200e150802d44001d00140d04107507400c10026009400c0084042190705803104100441e0f10942d1525405880500100c070480800c1404000049000c1002c0018a1280083d6030f003802c0001d05159414440c41416464071209070b01c1507101a0b100c18000c024060203124488032400390412407509150007841c8014a1710542000601d590390305d82d29920503e0003507010000808020b0140410fa0030900d40704446600124068400603041030b40c06005070620205a480c4500c80c0310802c405120050751240745440300d40203480402044101c0010b007182c0c0307000d402c039619003e50000a203042c1052071120340880881121a6594007080c18001c0318040460301c141160f41620700024240b1a81ca50703141800c8000c2c1c07544070400c0c200b002504104000388402c0e02160b004a400300803078504c5050a0f03c02010307600f0040050201200001c402600440007004003440050000030001919400140159001d0b1000d4a010f1090307400c01840c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 45769707 1250 45768457 45768461
    0x1050906120a0e0c0a060f031104050303070b181209060a02010e070902070501050c120f04030908030703020106090e0c060301091505040903080a05010911040506090310050906040512030103110d020f10030f 90
    0x304c92007540e4540003281040c0c40902071001408004c0205645c5503060001c0c0405803050f14050700c0000c0650340e444c501e42c01e02c090764140c242c41c210341c41e83c8552a50280e11030006002010703084000b100702d00341a102c10030085a84c104010340340a554842c00800182407045c00a040640b014000040c1c441055041c95400c54600400414402a0030003400c05010460500a9400444902a00c103541d4492404031030f40480c3d03600214440c800811003004141c2c040d08010305840781e40b4410000e012003c030f5810f42e00d80d5042c00030380d0002d00810051000d4220b58000300404e000e00d64a00c004241e440010504540c001203060b8001150b1805000300c82401e8080d03c4c1c01082007013410301400f944549004400d101c0c0d440f038a13105000004521a01d070300d0a000301074600382221302c10442c6242001c4000d440c1d00c0d048508407428002c224280c054004400190f9050300c3d040151088511140c905004045040c51030036070f80303c41d402c1c14a602540e28401058200380055a010803160801c48041c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 45770957 1250 45769707 45769723
    0x30b07030213090902040b03030f0903010e060c0306010f0c020303040b0a080a0603021c061401080c10030e0c0409050c040c09090c0207030203060c03061309060203010317030403080601050906120a0e 87
    0x4160041201c0300140003008914801e0b180f00d1000010000542d100250003447e40342221501400007207090302180d00100098040c250301640288038050b8041100364860504a520f40444078041c80412005d5200d2100b00201c04402d0400f40f02c8135240e42c00007071954001d641305659031000000d202c1006030380301c3c0d00c007600303c5140c400510407113040d5030000304070805101441c0c41c0708201e01009420f00130326400c4035400c42c484010040b625615105420785075414551440d0080120604107024148a88146036005040170b0140020184d19002c110280010f414152a00c3c8075210008000c0e40e500c0c800e4400002e1030391107000c070316490304407498140d0b030389102d0708415500300c0b0100f0409a100031406692040c074060046a9964410300042d076440706a80644d250f0034039080c0744004002c0c8070342c0154180d902590b0f4401e190440d103400710051303100480c0c0090025401078042640755021b02c028240740710000b44040e007007142c1e1540c21001441704135144a006030f20782e10070345000c6006000e204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 45772207 1250 45770957 45770971
    0xc010204150f111c020309060d020901020c030703030c060b0111010c020106050906010f08150105070c0806092109040929150a0338010308090a0503061003031209060510030b 76
    0x106000d60f070010b00035158092190148a803201303580078410400e100b80304840c0342c003200a002d80d440c0c141c0410000000e4001104071405031180c450300c507000e4500000c400c030440b0f51544e110040d0100c15611440540702c01000d550500104030300c0c000d03104801b07001b0841c00e55420341c000201e030f9152104102800e44013074072041c140000882220545030380702190641c0000240d05035580c000c100d00040360103100d42100174024121000001c501c3c01c01c0031520a008009000031603c06007512541e65600c803148042c000c1c5024003c1024070050f080c180c21411045005020046046a03c40107a40456621040300311802a18a0810180c0428080100796240003920000c0d0090b00f03656600980e44c01e5801d02001c59a90640700c0c4201c8840418107041c01d542c440001089540e4901d040c40761070708002c110320304c01c4040d40d8000c42c86041c001001742c0318400541d40c0007903152450302d0603258111402c2c016844030ba1241a560041540750080c41e008001a486240031285941031281402c00c002c1c02c11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 45773457 1250 45772207 45772217
    0xf0a050601020d030213080d050a02070e1e0403020c04020d15080c060304020913020409140105070e09011206020403080c0604030f0806031e011e0e0c0a0f1205030c010204150f 77
    0x400040e0b6400039801c0d000701241d040c0140e442000360400c540000403648003080b00c0c400d80c51011000c9070b000c0f0203007509218039022240c01c3d82c1c64181040c22031004841100c90140c5a503100c0314000c0542d5000da030401d0007401600c0d61005507001003016a031001c58182c0d5816151801c00c1800302408041d00000c1c00007101410001d880c000c001420b030710020344060310607646100440e05059200c0c80520312640d006104003d030440314039004800c40341c01c1090b00f40e29403a040000f80d5035406141d915003000401040881c59a0030510101c40c0c0c150f00349000c3c0d0b001d40d800d110200020340300000078000001d41400800880c175040c540201941443c6400f2400c0003042014820242c0340020039090f0b0113a90f034005100080f0390f0b50346500402d0070750a812403000c141c4100071424006503111411613050b0f0302c01e0f940c4d00c002c0441404100a0140314000619241310740401070304404040c4200040c1c0714101b9246080f0440185500760307082608040f540d00c5880b5544014250002c0080010840034140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 45774707 1250 45773457 45773461
    0xf090402090103020d0512340c170304180204050405180303010608041a07030e0607090303080606030718060206060a050409030e0d0c050a0e0a0f02040b19020709140f0a05 75
    0x200e40741d100306210003402280b4140c0c1003130410800780300100341d8001e0b118503552500260980c004a10300a2aa03005000c44903245c48509000f4542c4600807054108000da9451850034020056a0024281d800d505001c1404042500e141c050400c0e000b00d0200c2001680f01c074100002c200848001401104030180d40c030510b80012400841500d0444403d400c22142513521070604002590a81d07074500d0508440c401040742c0d890b010751083e0201c2040800320f500581d240502502c1481c0e107404042c0224448500184591030558000d40d80180305241028400b03203103050005c4510034075008a00940c000408104c001e050110022004150031038082c4080001601c0c00b80948020200c01405080314001400a0001e038401c04001003202a1240c64402c0d1b80342c0000e0190f400030f540d0384902038200301010b1782c41400c40c004e9400780c6412610040c9000c000c1e2413041000b843c03410704501503029400c2c0014000304284a984121005007248880f01d25010502c03d0440d40024401c1c2c2c0000e01d80b1003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 45775957 1250 45774707 45774709
    0x10305070b0c0a14070b03010b0304060b0102240c0d02070b0f0a020708040509060a03080f07034508100c020f0114060d020d0c06050a08090714210109050106050f090402 74
    0xc07008201c50300800318103c04130200e441d1030b007844131641001011590020000401c4114240214810350041c1c0080009a20032801203840d45088420301406250760040c0c4002d011115929030303009190301d5161441c0080c0e2204c801e0a0303130040c0300240c89104150041028031030708046415484170090400310302d48000780e51502502d020354010700c1d0040840e01c0001c0c004c0e45031034500c8005507070001070780da80341d074202610369030250300c0780d8421000030390403800040d130101c5044c404e40018001148098900061900b0414a56803c1d0a40c40a01114400001800b43c02444840044100f540c00450304001c90310000c0e140c0001512610103e81c50110704102c1c80b002e5010701c0d504076034110b458032844500c9000180c02c0400a0b807015140d0001c8440c0058a9500440104410582904c820103140d469507003094880c88144103a811640042c010350340a4030780000381110b510700311482c00c2d40506e0080802401c40d68205800c071120b0f07548040c00d00080c90816080350900304101c0b404941031034164 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 45777207 1250 45775957 45775963
    0x705090306040809030a05070906090f150504020702031509151806070e0105071b0306150f09021605010905100f02040807090e03070506040b0a060902030f072a0605010305070b0c 78
    0x50001c1c2c0552030208082c0c10342c5d030741440785025030b076000421120a140c40f84502c030700402da98810700080c50314014162800341c03c14041c00011804401078455820b1510b803c1c40040d5110840480c2c0c54043c0107140481e004440885a009003407070801000c50003a0b8510384101c2d084080c1c08082800c0800510310441c0700e00003041944040716240c180700303544001d801660640500300b001440c03000b5510500036100e100d142c10b00200d9010303140502a0080c0c01c084031005c80d00074041e40d01045203230741050110f10100d400501200a00b02c42000c00f941003619524211a50032200301c90315084880d05c4d02c01c59400f40a58520b22600c604118230b0645070504290350f40106124444172643c5694511540e03e005009a5507900e401034241d600525084c94044070119007201d082d14040c0c602500441d02404901c2900e200d0818071003501030030b40310403a069a030060101c1d2140003c0d07110f00b042607007001c506212040202c1c861100031502e03504602d822400e08099400c4600d56a4060125403507100c400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 45778457 1250 45777207 45777211
    0xf04080c0a090b060d1d24060409020901030803130206030106110607090617040204060308040b030a0c030501060806010806040e0f0a060b0f010c020907030e0610031101030b061b010b0d0507030b0705090306 90
    0x24200029911b83e400c841c000e0580881042a01640204404c202416000c0c40341103104801c0310b280007041f030342d45104210440c0d200000c0039412a00d2080103000003488280110b42200022403070104101d00caa00040c03807540240c001000288c00d40c12072901040c0d08220f83d54000d81c541c00c1c0b2030400c500303064005200c45807142c0b10b0103441840c0030125007552241d074062000f41d90080c800c07a80c1d541d10303940d062455510035070380b170b02c1c0d01868541d89020f035a01c01d1007918180c1c2c10030742c2c41c240c40d41c9800c001144c1c400310250105600554601e1070340c21140c41008265000050700c0c0140410b0b40f02814403070121880d401103603001d058010000d02503030380d0040304030f041d01c0c0d8100e4820005440d40a403c03401400c2a1b07818252074418102442484088045240100c5e44905402c0c1028a01c1c000114266600e101000b50000010b104050100164100c1b22540ca80d082000180d1400c14500041050381000340a40d0b442d000f001d014010302442d541010f502c2505414120324200c03c00c800309641d84d42c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 45779707 1250 45778457 45778477
    0x30b0117090d03180803070801050907051c0203180604050705010306241103071e02040e0d0c0206090411120402030705010c05030d150302030a03031a0f1809030f04080c0a090b06 78
    0x340d40b8541380d5038144041060707601d0750407a00e12038892610010140004000b805103d00c1148500c0000350074500ca04200c8036024015001d900e00c0d40889548a0060b400240582d000207000c0d83c05030b501010100000761149000350700500c50103160200140450361141c001ca01001d0040410240003046007148100c00c400501d00b101c400c0344003400c0ca50450148502c010078010413030307214640038111540354008450003182c00f0060401089030159a0f41101900a030118287e0888003003d4a0900302909118030081d001091140c030707000c40700907598400d00650b02e10455000c00c1c0415402c080111401803c0282450b005148040d00c0302e950302d000380e15030f00a900780c0390720309e0302c207540b005030715042c01107034040e04898000e074003850041c0103000041d04c0c1a001a5248505100c5c1d1b1825290f23507224108080d000707208800d140022501c00083c0200394100d00d100030010301c2c100342c00d003000400c014120031001d04910395140c0100290800076520401c80c1c40c1c00c080c20101559140d10483e10840f403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 45780957 1250 45779707 45779711
    0x60506090d03090b130302010f090602061302030f120403120302070b0109090203030f0a03020307030b0306070c030336122102030403020717010e060108030c060412090510030b0117090d03 82
    0x80300c0c82d0403508011243c1180000c0c00000c40ca08010b0210403c000090328801d80b50701d00309040400003101c2c440414420800180e0001c00851804140317482c510b6000e60025064450b210800f030710480c44d140200560b10310a400000d000c00030312205200358982154607242c25490040309480d540c0c2c3c01070040c00b0f45001c0584e0780e1012021950300300125052014200d511544459416502030002c1d002100c0e060040303070400c4d403040f559190108015224a1503602c8a0000340340b141c804070000c002001c9007415484001c98416810110140307410303443e825070301c46061241003a2801e0207900620742c001c842408010410034442e410341c8418000c40c050840710060301c1c0d07a61400c0403440c043c1c56602c19005c01d10207142c05104018107400c4000d4209044085031490390369030910503900e1240d000003d82c1c0b80c0214001c18001550121801420f540d103280407c2c0c0c25442c1c100246280900064520121f43c0d01c203821099540c010520305030182001c0c00c8a10240350021120b41c07078528005030340b02095 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 45782207 1250 45780957 45780979
    0x12170408120c1f02030a0f0b10030c0323011d070801050d080706090c14060415030b030a0c1811030402100f031517010506100e040c11010207030201050a0b010306050609 74
    0x1103410042d41e030b01c02503040d400a200208000303c280c003e60050700c84280791407d09050b40d010012500031101404c0e00900215002490311100720020300d42c819540b4101a26118000b509420400c903840041c1d0a1194000944d490301c400158100c2d0801d03003032b5040002e60780070055403e0f040b480c003604480e429580040128030502d00f01030b191203000c500030185843c060400c0144032500740101c069484010f0410341d6440607508110b51800340748201001207014245691036a403281d00500341401000d411104080780c0d540d107a00540202e0b81240b580301d16201056a01000b290007040c41d181d8250b003180d480d605003030b0042410074039540d601c401407102301803050214074407a40c0280760343c03804074418030b130030a8403040390240d206201d00711503e2540c00c0502250301458120326041d607254a5442d00114004088148009030034000030f0741007409900103010000c42028001403c006100e41c0c000919880c03c091000115101241c02070304040c50140f013840300f6140d02c3c040743ea140c1c2e82103500b16550 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 45783457 1250 45782207 45782227
    0x18070308071a10090b0301090503090409050309030a0b060102060f061807050f04060201020909281802130e06010806010501090303110309040e100f15050d0302161217040812 76
    0xa0b00d2410861580041c0e840420002000c0c40c00802d041e01c80750710b000c2c0f180343d810700105402d07141171402c0540f45410030421901285416800251218414170a0728240400d84c40081d0804809080903141d01341c03801c0c108095176a050000c036038003002c102c80f01e40140c1000380115130101c50740000f07440000c01c0708001c2040c41c9d000c0c001b6580e09401065030b00b6911038989000a01075001064614024001480812050350740d5041c0000f6124401030801500000060300e08060000700250940a6103c00b0001001d600c2d011012801034000c900d011480507820710766140707440416400495150400c0d0014080c5a030301c450010200c03034142c0b4006503150721044c0c0050a52150009269005242c81402100d1860100f80858403801d20318080000d2441e50301c0c2d8009441140c0c0440c0b80503115850144181d2070720510300b44100d4040c0c0b0490394403c4a60b00c4c1002c02e481d1580000b40912198690702c02002085103e24540309010f074040790915140040c0781d0340d140c2800800141e4074802056100311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 45784707 1250 45783457 45783473
    0xc1a0301030221010c0e0a08032b020d09140d0305070e0609011701030b0103031b05071a07060501090203010906050301021611061e03161806050d0204080102211807030807 75
    0x1a0b040303c00004c00625420a601905100f03c900204d0b010f40400080016900400b200383d41d840b91002d050a00203100f02070541c14440f661a6071010350070b41c24400c80c00c0103503203482001c00c900d1240441c07000c4609100040e618103164403000101301400d2004101406520403928821200d054030300b00c0d1200b2500006880042450040008280c1d8000000080c00744181c41d282c1200c3c02506c0305204803580d203610407981503108001074456130205070204410000602d800c5900d0180c156a00d090503c5070307032044141c2c0d5083e4025070f040780e00400140001f4220388100350041c0742c01c0f0005c514003107440e1a9409045082000039006030380410841c02c03507899903811545204e91140d2412107000307d100715034002d0340042d1448444106511082c010781030107440007544d111041145039450a1400703208440642c00195440d800079028000041c4d45042400517200074152280701c4c0000d0300300200540b4022800502d1000640b220004c80743c0c0d45607010400c0d90640c0d40040072140c2d62045410f203089 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 45785957 1250 45784707 45784759
    0x40309081902011b14060601030509060c030c0d0b04020a0210050a06180518060405011a0109032003010204050a0801052202100e0f0a081c0207082d0a0305070c1a03010302 75
    0x110000c844170628060720210303e99228841c00d0320104400c1e01c8110515607548400c031010695168200007146800f0910340141503141381079400842d081407214040703016a08141c40080240e4010b94140c000c4081da4058140c0c0301171049000c000c00d40c40d0401a00d00740889034a440d5400343c1d2100401c0c443c4503211000c41c43d141c1007100300c480c00e0070f0600e0068001c1c241107441d0800b5004000c0d01c0c04596204100c4001100d81007111045400c09490300b210140c0354040e440380d80b5644c20000052103481d0045104011b1042d06c00000703041c0351408003040c41d80010080001040244038840f00144c0d9000c5006210451520b032448000f103101003c00c0d450050303c1146540206030703610005014800040f144449103602c00c00030704078142c07003000343d80d034031280e0050700c0c1d01f0303080014803a1000322040c2107080c2a40c40111500e4125101c44005400c003042d00105074000340000070904180311500d40108000c005035503c040c005080070041ca5168001800001e20a1600c1d60b0030862200c6c4801c2112 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 45787207 1250 45785957 45785963
    0x51f140604080a14070504020a0c03080612061e06030a0201050a05160b010f08010c020a0312092613060207050a050114091003020c010b0303040f03030f091d040309081902011b 77
    0x524603102e0713130401d940380c0300703000c48102d00303500c140d40003c10603043c80c0c000c1c2d48410b49261038000010f403031550143d0340500d0042019030000344480038060418802c03c040d50143c1c60001070405507075643e40c9940045000242624002d9001144420060341e10408640ca00350113464007070f40b80c0240311044c000300a00c049000e01600350b040b0010829401c140382201c1210300c00c200802c03c1541317400040c2d0b1903481c1450050007144000d802c0186881158101020051041e0301002c0544e40038074500451030101c0c005e00040e140c0110f0f40c0484941c4180107080600324074002003206500d80400550220918081c01d0704000c032035440340ca44000c049040e0b6940c00f0300103001d40c845008401000f4025040800980d5040d070801541103118100032045609440441d0405524103003541c900b0f8410b2048080c0d4501000748005000840c04995581d2801d01404207800410508290500902241070f43c0c1080301c03941c01c0400340c002c803004050000d0039000c1d030a0900b40c1d04094110002042656090006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 45788457 1250 45787207 45787213
    0x40e0907090f020d05010e0402010905060f0408010219170405030a03150305011d0c1507020d05250302010906050a0e0f010302090402161e02060301031506051f03051f14060408 77
    0x2480400c90b940d0043c2000c40c5180c082004943e070b07910b01e00070410100f600c000e4081080c440061119041c050b004052203c009420341c0d140c0399a50340c103582245e00031001d220306003540708207000800d580300180c00d068000c040222551424580c50301360301c80c0308410590b010f0690360b4890b0080d4241700d4580320011074014008100c1004481c1490502c446100c0d41d80d51540507440c0000b1140c505040e414030340c000040c1d84181040340603801d00512a4411070246c0d640d106201c544150100c08840303071100304500303800030707140b96107144005012070409811400c14802c051044807652580180030b0400540708540c8985080046001039000b4850400529000750000030042032103450200084276903446501d1030144c03035130300480c100088203000b000254491800c03c010800300306803000402443c58484c00000304140d40f20001240119900715940c4401c102440b0102e003140c00d480340c66840540c42d120741e031a0000110581310107400b2800384041072140f0802c01c0259494a9003960f010340072801c11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 45789707 1250 45788457 45788471
    0x61d090c0604060809010609050106050a0e1c05150a09020105070308060a05120d02120403030212031008031b2401060c060603080c0f19050c0103050603010e0d0f020d0e06040e090709 80
    0xd0135520120341c4107086608008000034592002d11550381200d10325070f65a410a000d071482150b008074624252030388521150030005038030003440d44101c0e45601c00c200401c600418041041c1c01070300000d01c2d141d062442d00d005280942d80000454082c41d502d884c081c011540e50740c0c001107400c2d0941c0c00554202d070300214200003035000021000c151380c000343c013102c0f541d40341900b104000c0d12882c040100160041d00350113081800c0c08000e1508080b440504010341038490196030710716080020030404080041e05921440101030018414600d03503051503800d00e190041405902c400103105040030030060807540c105000d4035500c940c0256511812143d943d2454005041e601c90b254080500c0310700030780030700944085000c030035001d0351940100038044580d070040c010b4000340300c000d107916015500c549070a64180310a0200384030108094880d4510b642085074001d15044400e81c2c10401e0008501e080382d500e03a1803000341c404070380340408410340955035100d10702e0410400f944000740181c203001c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 45790957 1250 45789707 45789719
    0xb010b120a0905101406190302030703030e1c05030d0605121b0f0603040c03030806060a0905040207030507050d120608011509020919150810060c020d08091e040f061d090c0604 77
    0x3200d0701807401180d00c05080c01c6400d500c15041f030914400250325601c403880400000c1e0242d8560103c8a5000704406500840e1850121464a11200c11560b80d0400262030b12060703050301c21030010300700c01d8078600e820342c400201c0c0654070035003400b2a090310f400740784604070581e0360502c100d20414400b6000d203899003010319007a009001103000c04c42c0410003020000342541089815181e1056080d95409015032034801448000e600140095007000000c0099401107001005480741402c080da465280e0700440c40520300403241183c000002e0b603410085034040c6810302403c100c043d1265103000503510040c16000400c810782c80f50013481c0786240401e00003482802c850002a80d01700945034070000790780d03900d1066100c000c41c0c016400812081042c480c09410182007803c0440d00ca0f201c824684580c2200185082111000202040011400390401070605004d6080c1c04400e02c0b0f01409880d041020807240c00c01000062040b40700300c1d100042012201f0440e140c50480060507041d512501e42c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 45792207 1250 45790957 45790991
    0x5070911030906070c030f0f170f0601020105090706120b0a09060e010602100c171305010213030501150501020a030503040804090203130b070c02060306011d0901060c0b010b120a090510 81
    0x80d4a140b050048800040b00540202c00c80070100e0390594034125003080c0814181e480d42d0020a400d0100082c0c0901081d49180c1c1c10545400345044c058045190318200b0002070030350300000e082500d40c0c1c0205404102e040e80101d100c1e107600f504840301150325104040030910040c0f10b5840303880320905201c0001001a4038058080c1030381c1c9290b081d0b8661407454040241070700e0b0b50300010345c0020303168040c01c003040c10400140740d04126690201d00392905151600340c26030300a5100c501146640702001c1013004070900c16132050006610310200d4039032800c5c0010f074451086010140500c1030020005040081c0d0800700c5021f011840300440d00d07820724118520190b429420100c883c03125a50108807070602455280844070b41c01445c152035aa182d000448030a07480301d80c0108420b410700f184600796a90f0300c41e1640a404a5502d201c516a00d0b81000241094182e00100d00c0038030401840002c1058500c0056000a040202040d80c039901d03c0c00c42d240c0290b40710f41100c585d00d4022040a141145 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 45793457 1250 45792207 45792211
    0x1e0f11100e06150604120203030d0f1b1106070813060903020607170f0402010e031009050a020405100803030103030f1e080411120a060c021e07091401050d0f0507091103 74
    0x181c0c111091070b56001c0c0e6602103403540c040d4a80d80100107201c00c04c12241d070001c988400d03034805420340e400d0584003131840741640c1411070715003070b601d0726225000c84400d41c1d4951f6013241a42d17460000b0401380c078020460b0b105da002030082070401c40400c00148004480d045102c1101354007683c1005110b58a060007900e80405a4510300001c41d81c0c3c1d404040308004042c5940100351403102c0d0601902c66a0045d100d41044007011501360041c010510303400b128903c901d42106010f43c01030700c000c240620401040b01c40040070b044c0c4600142405104020001083d2030540b81d050a007240701c9183e46805403400414610254003410401044480c0c2d903078419001d600440c8039400b44441c0402940c01c000500c910762201a280741e01909030320000c82e01c16080401e0910303490056030381c181540640400340140344000d07101e040e4048041004090890700c564000c5070703d000f0149002d541440d000841d100701c0c61101a04805ca03000ca044184102030090700010120038408100c0300300340c0080190140c1007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 45794707 1250 45793457 45793481
    0x1f091a070918020903030d09170703030f0b0307030c0b03070504030b0109021c020301080a110a080706020604030207060c080901180510090503060a051b03180102030a020c010c1e0f1110 81
    0x42c51400c40a040300b41d000342d95004000802450400030f41811321401040101c81c10380703001c1022448000c40c6032840e03000f041180c0c020b9070042498800314105005079081100c1190080c0d1200c042000401e00390340703a090565102c2c4a0b11650383d101d4080407911030040d5003020309207201050001a5018203680100411244095484001810103400408a0000f445100d80b15080110701c400003e1610400240030b810080140a00700d403650744951405900e5084003015902c07a04c103020525804005100007402e0381d2916501a90701540d540b0030501460b0180c80c10700100211001040c01345440c2500640000f9020013180310400c0c02c011301c068024858940203000d5000842d1400209010300c0d4420540054451000e064080305039805510003800380d1600c07403020344600d110b00c0c028002580034004005015840d80c9075860f1460844804030001c41c18491680c01002e9100003c01501040c40340c00c0c24a20070f2099070350016907100d03411403051541802042e081007030040c1607600503240e40714 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 45795957 1250 45794707 45794729
    0x608060f25110123240607050313060302040617040206340b1602030309070528030c0f080a030206060118030203070b0705070b07032304030204050a05010e07021f091a0709 75
    0x32803151440700c00d4070034840c041d6012502130400051b814035030010095103201c0c0d4201c07494415081142c1070724202903000300300003a40000d020000c50b948100381c903a643c0c499490b001c2940c2406d0b80001d440c0e210b2021501d440b203541e0101c200d8060164031000d0950304d42d551001c115542180f030000c4104008903840c0103070f02c9908000c50a41440042901d20071301039600106102030611080002c5a041191010307028000290f24400c0c056001000c0c1005522074940a5400c5090620380f01c1c403d402904480b049521410b070600c0401e03400503c0d241c00440c2802e04552400c2038620f000c04441c003580019405119a400004001c45210002c140ca54010300503245c4140e2030b0702034450944207045000d4001801410000c110060b0011070441100071104041c0c40c0075a00e902103005c0e58812a4440141e40c2c4d1140100100101d102070181c0c04a92803020f8a204011401004404401c10000850070780d40c130390a4108101080700032440501d440314800c146450a00801040d0030002d0262172030400c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 45797207 1250 45795957 45795961
    0x80106020f0304031a130c0b072d03030e0c03010e0609010f140a0e070e0106050901020f010c09090b0310090b15010219080903070b0a030608060f25110123 68
    0x2070084207560542e68019036018100e503030882c00d0500140094584c6032010307200600c0000150042007018014802c1c4801c0c3ca484107600d09203043c0b408201c0e0105180c1c41c40044904140c0b0003200c1650400300d50500700000c1d040344030500c86107008410b1a25a80540c60403440c41914140014010b20403564070300240726040c020003c0724103032900b0320020b00a280300c640215103100e0b4690800611303903014408940b0320359a03070030380050140800c1c0e0000020842c00150301c51603590507c8200c020182c400000d00100b02c20307030801441c00e684c0303100e203d080607600c03801322440d6034050217801d09040700c035034090211f106141005500310400317903540014949070744140c0c00b0a50022a580c02c1e540e280c10441c020741d5100b13440d2080543d0101113960b07418040c81038003045005403100039108001d401d55000412030700b0701da6060718024001e045220031800e00803c21050007540d00300014132034400095a03100340c074034180c01d56801c003204025100b1035080075203800d0701c01590483c581a4080d001980c0441b6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 45798457 1250 45797207 45797233
    0x1225030209060d0c05010c0614010e0901241802120c030f09070503063d0f050102030322080f1c060b070f0201030b0d0503120603010e07060203070f0c09050708010602 73
    0x3a50000000500a10b91307242c1c208500d40c002d00c6880c144901516000c90303401e180303110b011030054007604064404541d044c02e001604400f40708440081c0029483d00e030300b845851310540c0e0070a001d4824034091100c1d004040030306195a0301521184800f4100204950500c140c0500e0f040e00201d074800032016180d0000781c04c40c103000960104940004d400f40c54203480c0c04500c0800c0340080b120617010076071000403095050044d80002c40b100000c0c00c0d440c0d00b02c00c3c10100d043d5100840ca80c01a030456105100b0b1000c8030b100700c1a081c00065464501d24003074000c074507002446000e005226000309802258450140b007007405241c02042e4024020021951610b40051a5004d1003074013400745502c0903150001540203030f102c56031070800140714840c0c1031100e995441c42c54ac4514200c0941800c2c2c101485a2410b00b4000c0454640d200e0000c1c020300d50510000075580e00a05501426000c40e0802c81070610001e04090310103420440000d00162915060140c1054000e109001c0184130b40c031104510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 45799707 1250 45798457 45798469
    0x1801090209121f02070204110315043606060b071a0a060605120603011d0c0a06050403030503040b151e0a0e011a0d1b021f05010e06122503020906 64
    0x80e0509241e040f40d070b942d08848042e40207421961003213070041d80d100710a2024001820245200f1440c904005e41e510500c101400240c54085581400c510a46251128000001100003819a2651058502030740e05414020042c000303030391003d0030740500003800c103003803084501e001000320075040403403a056210205800b00302c581501c5000c00040f4144041a80458012030381c0b9084080240045005102c100250140d0303014801c503544142c1c40501a16241d0804043e404020a520309003142403d2445d00c000e0500d1000400084c04020000c000078800131030302c1750341030700444c0141442e0403424203500b850940c40702d120004d511071001c148000a1051504603007034145c1d000e440300458030f040703004101300d00c07034200c00841030006032110751910807841714038241055040e40b58000c040c40e2208002c2845481400d04018030b50a090800601c00a01150003182e0046815034062070351003119441c0320708007008000203080d0307065681340e01901c5403144502031066900840d0030912549a003000c20030b03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 45800957 1250 45799707 45799723
    0xb1609050f01030914121210150c060e03031806090d0e060c07030213060e07080906040b06010507050703200409020901030b0408130902070308090a110609180109020912 74
    0x26110001440c07122955100e600900241071081c02014020b035103580c0d03007030b0405000403844c084800000c01c008401c0b28284403404d4010b1500c0c1207044480303003131031031038800782a00a05542c24400d22000380020890340d17901034131280c680901542e0704c80c04c04940c1011841401c9070008128070960f00854030104011400420101c5a030b10390321041084241840001c3c1c20480b483c0089010340c0e00004050380340c14202c06400a5207035000243c0341d043c45458010f003000981703400200700005040001614000030580d8100d904a00419010b03640c5030b004a8035403040c9000140103004600d0000300b040100803141c3d644400d5281c0c00051502154140800c0340c00300c040296101c00b81c030004001050031300c1e1070660014050000d6a00e04a00fa6085410611040c0d2041c20201d034005410014154001105a00480600302174405c80c80c150701c81c503aa911620010310f104500c0000d0381643e03952184068000441d5805101c8055039640507118020b40062200714040d41561891744000c59010a81070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 45802207 1250 45800957 45800959
    0x1805010602010b092404020d0209090f0c09040b04060512010c030501061701291303020a06030209240d0612050f060c030a050702010204050d060f06080609030d0f090f0b160905 77
    0x44e2075a4645d00607a401541034050b00c24030483e42c0d0207007020f60b16680010151207100d40300140c0d0f20103056081c81500d803401031108461b0030101061004084450080700c0d4840000c84000c5a104c10b2503001600900360f543c1b0040d0702003402c15080c512050306400500b46400c2645040005030fa03514001d0b10380038400c84062030000190801403245c011000040c1c6280319022600d11004440c58400501d50340c003107201e0045140101300c08000314a45109007001600d1185825414003141c4004100190740025418001000000210044a003603d058601c03440142005004890303903038a0380d039010a88110281c40031301070800c0003d541070740041d2407402101058101840d5988001840004110180080301155020800001e1030755442d4030700951030b07010b5900000c9403203611041c3d40840f541c0b6400300c4c81d06c0e0000c008212181d8408810b070b818207151450041000300700400450010a0201c80c01421003072000203880c244400103004505c203e18000d0f00d0503107100550801e8030200703040c3c4100d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 45803457 1250 45802207 45802219
    0x504021f0215090a080417070f0f06030507020c040513020319020a0e09030c06010608160207030506010b09120a240203010f14010c05120306240d11131805010602010b 73
    0x142205415200e1561040f40b440c00da0b0031505499840e90780310f900c036602405030720f85036a003050340640c42480107900030030448400f25442c61070560081c81b00942881400300381a59280080d44250003444a4006020010800c2205180070b400329001116100c00913802480741c0312140100980000d03070540304980090280c0441803904012402f84c110080020860340400d0000c0b007000101040814003810168031403090615061818040d0356001001800855014107000c10218802081250554020400050fa90400c40011400d5000c882c515003800d0301c15160a20244242400c0455414000507100303802803102c540c4040c140d000030b02401e900c2d191255010021665500c1d40100400e04c181006401880d1507216a4100160841056056403001040008a04d80445e40300c003942c1c6a95002c680400300d80d240c12000307024420706a0b0707400d652283c0b0743c004030b95118203030344d15041c0d5660800756440e110003103080c4a44031051840122414200041041801801081d1001e2406000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 45804707 1250 45803457 45803473
    0xb0117010b0901020f120a0e03060601090e1503071502011107050c06030a0e030d050403020f120f0a02030f07061e0501030f0201031a0d111806010503070e060405060a030504021f02 79
    0x103240350700e600030301c0c507181544101e00040e410800e05204110200c455115440d44800443c40060148118411031500c01d410640c01c210213680c0144074a025182080444016a40d4035501102c00241018030319070325110b10300001800740d071581442d0700c005800d60700a1203c81ca80caa00480c81340503d400050058010b10000411407c11300c002e158070070207003403000c94241c054403061400c41d40b191f040c044005448400300403c1c590100443c1001e40b10100080c0f0070195044000d40c11401fa4003e83d400040f0001030610b4218800c00c103a5405101e03010083d5651403451401c2001080313040e075082590191590b240f849580c0300d00c921070480ea00b0030714bc0e004503542c03980110003d01e8808402e44522812221840c1c2d292a000c5011821038421000c440c410300d000020804180d800880f480315074442e100421a00742d034010180c030703048200360410220b0341c034544002661500480d040180c200c01d000c9002484690302d0b4000314001c0f402500c40e030320144070507400200d05005800503e00980e1061103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 45805957 1250 45804707 45804719
    0x50d09050304030b0c030702120307020a14070905010803180102010903090303050a030e01020a020a03020c0a03020d02011209062a0c110d0c1205010b03070801060f0608041109090d030b011701 84
    0x1025580c46581901d24081e101d40d10304d1800f040544100c3c0c40f00d800802004001c41d01001502d007001c030240c040c0c81c214030380794000039030350900400001c01060310148101300000b810172504010302905071040c801e6603142c06e4110b94a0700042a07a44c00d6160094910701d840d401032040580341d581507621365a5050450300e082c1d03000e078481c4202c80f041503a519003500020000f803002d0002d14021364080c2540003001c0c10000d251442c081182ca00c6005098420801603607100c041104496080c00c020b030050b1341c1c1482c40c01c0104002d074009009981400390348004180500c1c128045039030012030440d1482080c1c9c104956580121400900c4505880c0c1956414945a051640103034403608041c0a016210f11081001d10003026048600e80c0d10f410000c2a5840c0a100030405032070311200070810705190083e02d00c4407a080e4840c0f44188640200800d050000e03880c6088400a00a05607540e2803d12803041a80d0b40350500748800000d14000e0382c00032940c0309103e4400314101000c2510a01d900f011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 45807207 1250 45805957 45805961
    0x10801061b14010e070506180909030f03130210030c08010902090d050304030602040e0c0708070605060d02030a03021501080c030616021c0507060b01030605180a1d010203011404050601050d 83
    0x1d1441d9581c0320600741280005000000804100c0d0034030400420b50a511300f000510340619900090311804061200110032100315605004444040320082000e888090644c0d08610800950b600250000000c001817100c08a5098040b030f0710a403949103000f0001c0204600310344906881100141c818801004804503d402404680c80300804007408a01d00707660716131841c1d000d035000f11103050300814104088003000d5825580321340859045460442d2543d01d402d4248241c00c8005c140ca0355401c08501e403a10307001180480203501900b03c0700c441c0380b42e04001e940e51600c110240240c80c4000300100d0a4400031803a0301d100c610140080985403203001034101182124410f0b0070031445810060b007041d101c03059102c5044105a1200f5a07145c1d02c5007882010f80da05522520305050070f019080000e42c480061424084078451410364517a200e0070003a801409070800e550561980c1094550030041c010740c000c41c100c640b03800c03007102558450700921081d240e048604a01048089c00055030081190b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 45808457 1250 45807207 45807227
    0x20a05060c03030406270b090d17040b0a0b0a090207020f040b10050304080c03041e0e010e011403010b060c011d0604080702010804080d060f03061422020105040306050906060306130201080106 84
    0x10032410011000d40b800111801d15051b02601c1004442050010501d001e00401030950094602101c4081a80407003082c06400540b0080c20000d1650000e1070102d5103601c50a40240c0080031005929941c40075000a50030607a000c0c0c1c8a4203070665400041d1405110703c113100743c4041c1000a1080d1400d00941e455000100107071408041000411182c103414001000507103003d440074020003520740c1c20381031030342150b80201245c10b000c0380042c8080c42c410a0040c0c11a02d00c038110221614a200201e40903040342e101440d00510041210900201c041d0040a0800219840c54201d44040b4040c3c81d03840d2403ea4010f045088200300600155100342c400707030f0340304d802031752000e00d440042d00b1000300300d80040e40102d117641c090440c00d0041102a01924036428041640003a403030030604e18125640300142d14104840c5014080501164005d900ba80d006603008001000b0b40c2c41e00303844064880c2c0c8100c400c0740c405d003d8500002c451801c04480101d140b42c0694442055a003080b03403d80725400130b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 45809707 1250 45808457 45808481
    0x71205091c050f0a0206010314010c0203190203070b070f030e0303040807030f0c0f0f061109090c090102010605150d0b010207060206041b0b03040507060909061a070f0c12020a05060c03030406 84
    0x30881a00320329000f800400355251382da402044958594145031755190b10703070841c10585905224004420b01d9000003a94144c0034064000101d060044000b645103102e6840001d2050380c185040100103500030494800742030540d2010b1160354228003149032039120071280188400c4060201001084c0f044004202d401e600e8103010503007044035181d105130034841c80001ca400c084640740c0369042000754040e510104119200107410a2111400240c160600030a0003801410108541080340c0c400d4000700d004000c050300700700d00a014140c807440103512410788a40454100040d00840d544005003042c2164a940d010701410303100c56544500ca103c00100a14a80f06101000305043c0c0c80d600040d802984180002c01d1450303e00107002d80340303034450b52101c02c0321881c0c088204030f051003822131480ca000842d03061039038402080c07401440f40b08a20402070300c0c1e540e80c04808030380030351540205441340703000300c0701c0150aa907200d08002141c1f140e60082101d41e041480800c001074078a40220500002c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 45810957 1250 45809707 45809717
    0x507031407110a0b07050d0305090c13150902040302150f031b070605130c08071503050408160804030501050f01031a04060603080a030b01090e16051608070308071205091c 75
    0x11900000c3c01e0100e15401010b10408000380c02000c200f0204070300d102e0405942010300c05890964002515040c042c40d02d18010880d404560b06e25450780d5000030020207500400620316601d4494010094009010481c050030600d41c261814112100641c1e4140201c00303441c0340b955032440000c1500301d1140c003a000204400303111170000102d941c00b40a20485850300740c148002414101103060020580c4001d2050b00300d140244640c0700c000c42c042070020304a06010031561154170f46040f262141003181008001100074507001c001030000108100c1e4000c030005c2c007441d200c1c000c64091100b020300c401002e084039602300ba40c2d0030298214140d4040d018030000148580e4075158600280d0107500031a0003e5940c0c6800d01c095a04409218041c0c895411450000e16100304074206000342007209109000c000b14001407881e401400700e04c90700740e200100e9901e174405407401030806c000c1030b903229000c92403c01014000805520540d403007024108010080c0040342007890b22003d15000400302000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 45812207 1250 45810957 45810983
    0x12060302040203010b0a080f0c180d050703050618060705041202040f11030a060603091a040212120406090b0c1b0d08030405030301060905060a0e0910031202010506100507031407 78
    0x2070303601d2002d0340c001c0000c001c1c060f603948003142000389105001030508507001c46450601090202c1c0304240c03032081d0082070313401010414850019802e641180c0d402029441803407008002c0003c0800c0e005e0060f03143d2510040c0301c482401c0907548400c41106ca050019006210800c01000c0bc0344100303040c1400074100060b404540b1100b8803d80d800810b800c05003013000410701900c92614801d42c8000d04182c40d0070070403a44e041d0f0300d604e2281c80c80300c411018080c400010070150342d181c0f080003121042140031100c11803200398200c8000d40042c440d82c0b0200340d901c0c1c0005441017404007101c005a51001c042e0400c845060921504c6000c9040103a421000400200000840400c01075000d54018001142c1342d43c90410300038100b40154001501a200c14402078003d20b03085955103c40e40700455501074180d90705000c01c040840c91b6803019113a00e0007040c0f041ca0040d010b52003a4015001910010040f0121a0303090725244502c200040002d00400c00c0603030210015006004413a220b0759800c4600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 45813457 1250 45812207 45812209
    0x2030a020c13060b0d050712090201050313060b0901180b090403120911060403080d0c03110708070510090f030e010809030d020904092405100e060f010e190806010902041512060302 79
    0x96086080c5d259141030782c40c014012215000980c2c9003031a410300405204184075580000e115010285c000c48580e5140382d030120030861240c202c0b9004810280c0050645d6960f1a1031510f00321111110002a81c90048a441e041c00e000c0003613445140c1585400d4410703948200a07100501024409a4006d00c0584c5092281d940da10001c0000390b004d1000d8075203641e103d050b40307011108450b4104040c1460050554040c080136010380c0c8246130007010aa443d10300b642021402c02c3c610003042e0740002d01d410410001c0111107500403120b5800f80d50345d0b0b60000075001c01035640840948501015a100340480c000010031303033b00180f081c900702030320108000c003055580c0b00704041801f05020100c2034869a0000000443c400c1d2130f400044007280c200701a240c80c0b81da564100300680b00b01c2c01810450034640c03903640a40c510404031113000d403000c0e0105842d01b0310601081c3c10703400727110107a008010000485544030b00941e8241c80c03048103009001d81302540140ca0110310308454070840307a2100400005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 45814707 1250 45813457 45813479
    0x5010516050d0c0501060830160606030614010b0f180d0f0506070201060f030201030b19090203070905031b0126070504050a05060c070506090d08030405030c0d02030a020c1306 77
    0x40b074180c1e0b16140d4142005240c82070030754896400000c26a070013007840304100300c46105068004070b0071800e08480001d00d0841c1041038030803005900b65943d040031107401080881e600c9032088034011081000750b590161500b1500d184c013131140704280c200500101c084680084024901222808001c4404081001c0860f4450002120035102815420452030a1040501682da03020707000384000c001072410320010040008450201904050f45d800c460360040d2951460804000b000c00c0480000c583d1700e0146c0780103980100c405c0d400203440d0317070400104d81c28006050115020070042048040103030100446020b0030800d400800f48503c0300c4954088070044419074003074109550340c940d0f614186400d04c22540656484103000da4010010000d0401001c5407400c266841150016a00c84a41c0c0c00103803119480d00025003000000000d001c00c001c400801824900c490720300b9a00d45c0003205c074040e601c9024942c9250056005801940c90a240040600004000645000038141e0301e400c10305032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 45815957 1250 45814707 45814723
    0x816170703061107030905090c0703030218061314040b090c030a060b0703080403140306030604060507020106050301150503070f0305030409050a140a0b1f090605030a0e1501060801050402040f0501051605 89
    0x5018503001580380c040c1346e4000354100c080c10054901039043d041c0406080c2c10f503c6800f0b170141c01c01da03000c40c2c1100c42e00101c05058070421001840702d0b031101c10021414000caa41ca204294544106800960b01030915006510b0f110070010410095513035501c01c201015403000b070141d103601796220804101180700c000076090050103030303503186018a07140c58080e058250714003081c1698a0217004110180d039000404c951700030380c407d80c04101a10b80660613405040a5005983c0c5135082c4800014a644150340704000c0700d10882c112007003a0307540c103c41051007515000107003c44e04104030920090103a50805c130b0704030b441c1840006650a0f101120003108006450704440551520750340311141c90003424542002c800c802da407042200000902424100d02d920a0701c003804400300000707640e403500c0d5200d20541c040c0a4161056049500c04240c0f036a1400d014001c0466005800807989040c00d10030303581690201d882e8a210a420300d001541d15811003858948422070505082c8005141400358034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 45817207 1250 45815957 45815981
    0xd0b0307091508190807080d090506090a060f020f040b03190227010f050306040e03070605090c0306070302070312050406020705011506030b0319080a050c01050c04060306081617070306 81
    0xb05081d08100741c050410309240d0614035040d104016038404210200e0848407041c3d402001555616034810103a00580303941c1030b0250640c020802000610403000c0b480c207a400f48100c408200c40321502200004a0003040a41c40d1452018482800404080801190400440c0301160f1b0015003e03c0b09005076485820a6210844070300302d0038900c01e0760382a03008095142400d140644c01ca0a000081a601000304000c1c415500e40c6604582e00106104a58250703030091014032140ca00070b000190b6504d2100061030091040000080c401c510034401ea50200b0b5060f40c528100d401440200d50207440c02400985d81264200301001c0020000d12610095000c0a0440341d4414034000000d01103c040e1103a55001c2d030000c0c0000c0c1001240c002c04008072641c0710030110388130381002c0c004403441c2c0920305130741e0310940c41e020622280c955018040c01c210b9006076814006a03031104c090580300c0380e299030342c84e404c0110348070103210407116104a9150b11080400701d40610f5600d03152402500c2d00078202d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 45818457 1250 45817207 45817241
    0x5010603060e010506090a0c0912060207020901080601150807050913240b0d02030a1407030e060c040303020d08090102190507020a0503070302030304030615030c14040c140d0b030709 80
    0x8204202550150780b0700410000000c200754070380315010501e89103004014480481e66151840c100c0ca0203201350901400815512482e64006c500c0d05030025440014280d01c41c3c0c0c51200000740011000845a060790b03040f030020b0010900c40f0400762020712000d0b0a42c41404002d01039600c0700d844081c140c00d41807211850218250001c610040d620b83c40c14218600c2407005080e0a1002400c803004840328240d46100c016500c3d40c03040e44102c010040c010014145404003014802c2543d4180c000d0021095454141c54041d1a440c10200e9648660310004003da04a00100010240228003032940440d6160015113010900101c031102280510207482c042039010501c0c00540c1021103004028000a0340107110060443d000240e407402035100080c8100e032640c004a07031031200504500000c5078080c04c590089c6481d040c881580900d2110031304d000300d103000f03400d00d0118030840c84000414540d0813040c1c940402150500003610350344030041c1e0035110700803000840418a20440b40200c0c0710400d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 45819707 1250 45818457 45818459
    0xb100f030b0603060f010c17070803040b0a050f0103020d050708070f23011b080c060f070224060d0201110304060507031202040303050406050c010b0a091b110d081b0304050106 77
    0x4040c044a44458266008075010700c01c00040c1e40f280003411102070403d0030b04208407040f61030300e08244c10328549042100c1c00c000c24020104520540650f0050f0b200359035401c401c0d5100300f04082221400c403411040c8180d100010800343c140100008407660140c01525241c0ea182c03101c1524000b810360100180c104030341000c0011003615104c250080001c100407107903090f40640020180613105001600d10030306501281c00b08030024044440c01c080034026555545081c054016004800300d902102501419045107080300d204640d1410f03040700d602c544020b41c2c80d01e20a0200200c41e080003241888254110960220303000c00c060802400b1b42d64505584010070b144c0240811203c800b4021020b006000031300c000b9801000b514160782d02d502d4020b40300c2d0300e27154000b80034080007120260054610718001c034082002c0c0e0401c40c01e139282d180c1009182c064411044a0142e5004034286803a085816a0056144200e04550704003004851054104402001c3c0031102d034000d8a0442e2169900c2c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 45820957 1250 45819707 45819737
    0x30108010606090e0a1e090804090c170f1b03010e100b030709090908160605010501110a02010917030705191514040f020105040825050405090a03050d0b10 68
    0x1401e40503207003030b1600000c0c1e10301c0d003401e041440c030000e0b054420380c07500c0e02682c60319001c1501e403070381500c012a4814010341000e810405079039442801052910307400d04480383c40c26130240c62a00016900c04146000315580d45d0041c4241c120054050f4600c0580701a20484811094029602030890010306d940d80e41044409040c000032594000711100f80d080c401c0242a83d00612910110796034140301150190302860945408e00ca41c0780070142d00c2801c80a1403040c441075521180c1038a5083c1c854090712105d42882a540e0b07508088001d00180c04440103006030420f84445004400214048904100c82c4da52564105415a500740c41003249a4081d002808104e803402610f43c5d003810802c000300c1c05506036040905000800203007130131190400310811640302d001107400400184081d1008654000c080c080700003079046090070700d00d9040740301046502d018850640500c042c000104050a0185d80645440d00100e1581d40c0c0159180450205610380c50292038484a20b507880d032408144040d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 45822207 1250 45820957 45820961
    0x140c1306050906090f0a0c0e061c0b1c150609020a020f010c03060e060d03090f08100e030315090a020906070b1906180e01060b070807030207060e0105120c0705060c03010801 76
    0x500352486a80080140300005e049903814076000160390101043c3c0c1c1d80c07606020b84251414040480c0c0043c0b00003811700c00340203601400e10408651000600c902e100030b20401141001c101054002d900b00a1381c0d800000304d5072884e0958840168001007042c0e540c600040382260401420080540c12a00803810078102c2880351206512aa0508004003424000c0c44101c0712802010640504407406c007000a150041c503442005001c1c450010301081c4d200e55541d600c0c0c0e21503c0014046506141e011b400310900441600d200301e046001e00058221000c0070000010340c00751400c160703a0f900700048001da80f40ca100a1402900030030085009080c0080e09094000301c0540b030f45130309450985c09104889a4034000902c5816040010668001213034901c0d0042183d0340c480c083d00c1d40e0008000040120702c101502d20180039800766010b00c2e41e1014191400c40310400418001841042081e0008112000150b041040ca2030040e080541542d52035207085820703900c2450810000c4010014610300b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 45823457 1250 45822207 45822211
    0x908070c060518040b011101060f15110c040506060c0f03091302031006030c0302091c020a0602070f0612022b0c0f171503030f070c12030c140c13060509 67
    0x585000c07450840c400c43d283c0700301010f03141c00300d00c299100c0089001981c80340c0340d21609069101e0082004942d0764a044d000a02c0c0c41c8a0b00098100000c0c20f0213200e80100d40c0e4401e2210441c014240b5010410100300060130001d0099522500c00e202c40c51804600b0001a00075210500003103070350f901718100f081015408c408503500140e0040041081600c0343d1400401150340c1400d0100301c0c42c621100c150064010005250b0708682540c041841d510012146c03d0034444c001d807103840103103440b86030032620707072a003802020310031881c5110402c0100e200780c0088400c40440e1000600300702e155010fa00d48011039100580e0010620900011014124462001032110364100070700c1c00c0e0041500030f0164818010101302e03141d076010009600c01c850101145428800606603a9aa030040d1045c200300c5d0007605013540c4481100402013a034400b030f54079900d426901a2210f070030030328540d940e41c252810710030b40015030b5000b111007401307080c1c8a4403816141c2d500300705400f19989081c2020b0190b01a80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 45824707 1250 45823457 45823469
    0x21201090603030203070b0a2007060c03020a0801031b03060212060a090501120206031806040b07020f0a031202031503010614041a0a0b07031e0804021806150a030f0908070c 76
    0x280c90760400000340c000007114250f55000e07501150640c0c405583c64000c01d6400007405c1059076001d000038008081c800103082d81403040d03008010000d62240c0442c200d000e0103032070300041000c030401030004c554039880d550040304d80144c07107082a94072039417000d06a8000d5100c0c000c80750328000c140403051a024006a000d0070342040108030561401181071440c08032500c01078003aa00002c0410043c101400060958604000850b91941014900641c1c005402c84241c3d005010f440e20075101880c001c0303070300c0007a01e403d139442d586a480c60060100007540b01034041a103140000c0c6842505d0707202070140c48010042c03854103c0307041c3c941c0004d01041d00c0a0125083d0703850040007a01c002640d400d0100000e40e4004c00d00340da10346210f89405d40300c40002c801c0c0c0140f544c0c0c41118401c02d031036001d0040e07813060788251175942481c200b0326008070a1010a407800e0703130b01141c804050565420006c001d0a0410911715020801158441c803a0040303e000000545480200003600380502031080324490040070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 45825957 1250 45824707 45824711
    0x10e01030c120e100203010605030103140601060e0603060303070609030504050a090b0a06030b01121e0b031b040506010c0c0e010e06060a0504030209040609080313060b011b1e0b0a02120109 83
    0x1c14903001400782c034001c140c440030b01d942c2e0780b040c5224610403c810b2220610700c800840d42e039612403901034080d8100b403000315211403641107101d40242000c5003840c100c5041c1c1d25501c10702d1241d2001c10200340c0008050a4041c0300a00011000c9800c074000c10000034002d0304c3c4c156031181850184482c1304043e81010304654240540c2d400c594550300c0f4858111040c510300000c4071030f50240120b402c4469903a5401f8501e04091117500314030021800c0c0b55070451010303c10003070743c0c0107a4181522150a000c1181d00f820b4200344030174060500c0e420403603000c40705241c1400c10300c40035660b0046ca5140307600140c0d45200c5800042c0001d020800070320743c0012040b5813003420411018001842031040d03001c0240142e00c940040340070403a15420028106510a0300d09880e80f4100b50413451808001c3c4017a580c00c2e0034282040b20300c0d400f0f11030b080c50344c0700d86402116469807940ca0350070340f9550151280c14142000841d11002c40d104521050003505c5070007015940c1e0b04d0030844050400c00681190100038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 45827207 1250 45825957 45825971
    0xc020106030b0c0901020a15020a0e01090303080402010e1f0c0515060d060f020f0d0e0d05030606040e0405030c0132060a090c0c020316050117060603070503040503071203050402010e0103 82
    0x41d111525180d0050008508513500d1915500403814154404401004200041d00d910000d502c643c01401c134001e81981d6a040c444445401180c2000441c40080d02207003020f000314025511542a02d1041e02010300090760014805107456066000c0300256000079a024a465007040414044102c4014105000020b17505040c40003071442040040300400325551040c045a20744100c0d019075007070b08000c0d168140c460b03601e4603104000e0003c0140348800ca0107a07980320541e060081080d06d004c0c0c0401341c210fa08040c10103441110701c500c05442a545407105201004094800f4000e4400b407000307280244034406840300e01441446006000036850b40105401c00a5586411041c001119081c20020500c5c07c40741e00c064407101001040650540609140c2c0c400310034440039004101c0d41d0a036a16410a1000076075905071190554820b030707210600300080340c03001d40303e03070701441e002030081083e070307141c8840c0366904c2a90190483c40003011076114010041550b80045014215201c01e007014081c917 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 45828457 1250 45827207 45827213
    0x21f020c1c0201060906060f180806060103020a090302090a0207051b0907081302030f01051008030702100f12020c0c0906040b0306010306051e04060b1f020c0105070f05010513060c02010603 83
    0x39180c00100401c100ca40740d0312054001d4400d403c804000d10f111141001060307100c0c0401071084044d2041c0f040440c1c04080d90080030b06c5400c4409003200c100102800241e01c440c401107010754072055000d010440007100120140e0b640b18481b0b8000e0351003c00c01a510390181c07400500b4110b06054924044004a42000242d203805040079403142c464030b4120710300e503905410f080403484452000794162083c4500c0c800c03a6001540000e00642b01198800d4a240d03460860070740da48a910b00c001d400020801410028501030408191490110308004000341d40440c0705600305d070400300300007009500540b2220014200400c0c2c0030380102003918280111400c800c04039130f5854061000600b507580d580c00142000300b04000022042e0f041c2d031004852820320f030400401400700d0001e0759208215406101c42c613501c84203800691342d8140c2d00039061040c030700300040d0741c0f03508030400a440780102940130a0001d24203210b11072140103c400000b12080090402c1011103600f81c41200c156807610782c1c20f1000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 45829707 1250 45828457 45828463
    0x91e05010e0f0c0108060a091802030616050f0d0e0321060a060806130b0411070b090d120209060d02190905060f040b0c1c091d010303270b0a021f020c 66
    0x60b000f401c0c2081c0c52962241400301c0c01441191380592010752624410740c40c3c180060108400d01c074001c174201d40080d150000c200900c442080344c10408280d04110700d202c104010390152456032104200020200d44189010f82913520140180004490100c1c0002d229074000c0d10468220105464001f1101d04002020708040001303456103100e007000d614a840c202c0f0341c3e500f220000a9010b4002d0227040c4041050610301d8000c00f00842c0c64880e035900268241e0300000e21a0080040c0c0c1c0e071202d201180c0c0c00d0b9410000c1d40301d4900709400c41d0b01003004013401c2c58079000920030b0360701541207550104080c0b5401011034126403c41482840308200b206000340e50001654203490014985a69541601802e80d141c0720f030000e41c000d00700040800000d901a0007681c200708450101406000814205004050048003408001c000c110010030b0014109200c0c40504100480d400d030a14200c3c1c4c6544034851180c000c81e050900581c0f10418443c0702030b0300749408240052018406508040780d998034079813 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 45830957 1250 45829707 45829723
    0x3150e0a0e010b030102180306060603090c0913291506040501110a140109030f030203271905010b01090605090a05040510090e0106090b030607020604080d091e05010e0f 74
    0x1032680c0e101c20140689010a500032a441d6000030000c640d0b581003039210300d500002580615100c1c1c080c40001a00900b4042c1c11070313204150316809440c0035040c034401c020450304046e00c52014107100081c4440000c1c10000d90301030011102d503c0003e2130b0701911640000003001000842e0f03102480d030041d043c2e5110001070701c003034503002d0801402c0006600201c900d8035142c1e0001809004201c80710250007201903101c0c000709802599419100c031440001501644400e0720201c032001441800c41c0740d0030310700b00c0320a12100c6c403840a4403004503002000604c0403120300804ea0320b40e552240b44541960708038140c00010001ca0502e5410603038407800243c2d920040c3d100c0c0a01850b12080001d0701000d000c1403403005848028010414115603881072f0f4000e0035a40162201c85142c00c05002c040d01c7c00050340c07031140902d68011716240d0f840b0b9a42088903001a841c00b8107a85d150039818000500346040444803805401424a2500e154100036081d5202c00d20204c02c240c00c400741e000741555010802c00c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 45832207 1250 45830957 45830971
    0xd05060c0309011512020a0501090605030a021c0c0801081603020303190207051305090c0d02060a200714030d03020c060115020c0402031e0a0e03040e0c0408061603150e 74
    0x580701c0d80c602140c640540722200c0c01900325000c65001080041d91200000d41841c000d0b25600d2640d9181c00054803142114090380000c54800c2c40001c514040c190020494505801d0790381e0104420b400e49c03a0b0660726865140d1300403d140c0e000501c500d5408200c1c4018801c0c81184c01c4445a00c0c540209840344102d070602c7d842841c004c007108080f117008200040c000c01020300a1031071015078102c060020301082c0e0741c1e03c9241c0914040c9005c10320b4810601218a5001841549032100b8104143d42c2d01a03c8040103504c9814210a10412101402544010000d03d45801c0410076958109070808144400d44000d140c418820f2510003000007031007038151040c0350b00c9074070902a100001c4e854049110038080d40b041c000810800c0f2500c0d603101d01507036100843c050941700d40354450070800f903544050703403c840c551060200f0003240b80f04031299a0002c2031840f9903460552a500b016003030507000ca400d140c0075070780e41e01703204501503161103410054810301003c101c17020b0408202128040014160b9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 45833457 1250 45832207 45832231
    0x20303160503151f080601020a02010909020705010f052403030f04060c050f01050a0c0f1119140f060103020102100501050d030804151409010f050103080d1d0111090f0d0506 76
    0x2d0180c00f07240d80c41d24440d4100800082c240324008a29480e054161484076000804c00d80120791954000a000315030594141c44402c045410240044000d42042005654075921421030000410740c2d80b01d61070264541d21000f582c4c440e072000103100c520ba03002d0307a624001c0c0e00c1003059007100f0701a00191020307141c081c5482c802c20019402c000b490080000c582003129440c0405100115400780d0000f422220940c80d83c05003001600380c02da5000c2c414818814250b080980306070300b010740c00150743c0c4c40c0724460b00e0703200c42c00642c8417407a5141c4001c1d411145103e074000b400500a540e010041c1040c40c007400f181c240402d42c100000b02e80040a081801018805034401142c00c105140c003000f40504280c400411101400c1e616883ca2040241e45213000c42d440d241c103101c0d100c8814000c060503260000391962070111103010071001003444180a5040c150383c1d0b1840642c4a80c00e000351045104510303800c0307031175100a4081040300441041d01620405103800014001a03002c1107480e0300558003081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 45834707 1250 45833457 45833461
    0x503190504050d081c02030903040501140310090507020a0f0b0105011403130303020703110a0506070e01023004050603070f03060f0608150609120604051626031204030c0b07020303160503 82
    0x7019400641174190852014004020014111700c000003900c12100309991309180b4002c0003a480080d480140d814002e2182c48010034800701d2856013005800544500c11101001030f5926080100c200900c3c0c00c40e44400c8072001000b2940e4001d420240c4a01581d14280c554200b4088004440401d214020141600441c01001341402881c0340c500590025058a142102e24504203458170340c00c40313454000c1000580349a03003551001900c2c0c0d85203a000802c59811710300c0207001d98810b101c280786880c1810820040824181c6500c009940600840d84403020100850390307015094602c640c000d00c0421001e00c208010039a4001c41e0250070010a890b8a50403d0b0420041242e034843d43e00c0d0581c0000308884102d01080000415500c51801003090381c844920308041c0c0b4403041c640c3d1040785a004ca40e02210031002c41d0300c03c01405008100d10032285030100c0307000d0007820b0038412641500494540300010082c17001813691941c3c00140d51000e50f1461a285840d050030381c8085070000100100440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 45835957 1250 45834707 45834727
    0xa020706110307020a03240b01020705040b0a0f0308030a05010803120105061c050c1222020603070302130f14100f030902040209040e030912010606050403020621040503190504050d08 80
    0x308a030382d140d0300617013503a06458903402c10303050000828401ca8841400c40071403c240549038440c40d10700701416400381c01400e1500301008044e0211041e107035441f13001e82e0300000b00010801c00700c600451090105540b60700e45a04d00404a0700142d01c2034509810400c1010390342000d02c200141503802c2220000c0e10b400b01e100002501e552400000303407100b03140c4414003507000107160140c080c2d2078001c507000724507a4814101c1c0364601d0903401d1450352040d52603142e800520702003025651003440703450010705000c4c00103070290900b504c80d80014540d924009050081d152000b80c403c2d40070a081c0c2d80d943c5940303510000140000c045203140d1041654800f00340c01150380d2901214140c006c004e10600071404c50f43e0b4556126401a05064419580d100c220b1a154006025500494000b5203071281032500c0c54003881310940c007413802020148030300004040c498009184a03402240294025601c0c0e290303400400b0031048100084209203c0c00f40000c0106955040f10800642e52203402c00703403a0a60344d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 45837207 1250 45835957 45835963
    0x6070516050d030204141c33060510050c100b010309170306040513050a0209040303020c010e150114090c09010e06120609010b041202090916090504050c010201020a02070611 76
    0x25030000c0c002e00039490020403603607054000c1d20a40e00140941000001d0700c03c10032044e1889500c0070000e0912030300944010680038801d502214111001401880100314841e004a08410074010a265503500091102e4100040f551155031080d05100345407030100201c0d1540e51180e011840c16482d200e040080143c0d100340c0001509550010000c451601000410b23800c641048079154080e0746003100160701941c40060382107001c0d1700b11018002034072030341d024030410300d00c0100182c0615400b0040141400802d11504e0703483d02c41c80001e0a00c81000512000b211001039001500483c1040c40b416101d94030034034069001884d5210442d5100030140050341d0340060602c00039407010001c1003410108101c0c1941c2071041604231640c0e03007142e0300c48021003100c0c010350088008000d203244003000181882c050340d517040300350081101e050308191841c0d81c070012110340001201039100c81c140403c0100400010b03032000c800340000d50800e081882d000f9610103d84c0304030710410a099001203000007040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 45838457 1250 45837207 45837247
    0x30b210c0d030201051801060e040f03090f0806190621060f020309060108010b01020a030e1207030b0c07020103050f0c09100e04020307051b0601141306090c020a021908060705 77
    0x604400c07000c110508002e03000345011101d0b41c0e41001c0202802090000600c92003060310003c44908440e0b86881d101c03401d02a41900003201444400e01c0085910344403040a00c009044100041815140149200145494100e4400c03c01420300606005409a40c5602f119140542c0501d40c94502c03103061142c00343c410100348030035291001040c420380110118446040e117010f00000e01030307176151500481c1d44540c400c1c0c0103000503c0d05030340003087d4a000080e540305101e480b01107901c8180c8944402c500745c1400d9541d0190340700d000804004658041c01956400107428031000308620301001c1000c41441018040c611030300c44800004601800350302e0072507220308083c00454403440c120350058078691101700d4522150620107208001058005041410b030341600403c100e16110300300901c091080b07080d9841c040c0c0340e180d00020914001d680f103a6601c5003000d60041c4a034034528014003502d4001408000041100b00e68144984040016007503001200351802e240d4904000280250050300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 45839707 1250 45838457 45838459
    0x604021810020f07060c030203090103050414010c0e040e030403120311130e18010c0e0609030f01050a0b0a0e04110f0a030f05010501031b06020a0602090d0803040804060807030b210c 80
    0x20071a41030540e8001541e00441e40050200d4640c6174031303070f03006550644d580c00780100181e10410880f441940b180d041650440e2091420440081143e0382603403e50304816082400142d52640b030040625241c098450204990b5010754a403130b003180c690302c0c41002d600307450b40c0925031184102c049010702501200d00310b550a0160884207925104100320525041d102d41c4103031061020701a200b1001845140d07080c8100d0f0300d0301d0600300a50000d002080c0c104511407689405030302d2051822620030700500b44143c42c4840c0001d01c00d5050700400c195814540c00a00610380041d04003c0000c10b070400c910b035110000c1350803041812401d0002000344070150401000136980c030071300a041100541110b410303a03100c2e441c03080081401c8011112046071601c91240140d01c9128000302042305503008004917a4007610f2071841c0e2501d070716291416030041d10119043c4100080822406910003155a04120580341c2072103505c0e11200001c0306040e0141404a00400b00740c15000c540320200403070078103402c3c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 45840957 1250 45839707 45839719
    0x1505031b0c0a050106032907080402040e01020f0d06140901060c0219060f030501170c040203150d030f031a0f100e031006030215040501021c020a0c0306050a1503080306040218 77
    0x41c2e82e1414502034501880212041c401141c030700c1c0140760b8621030881d00706c00385241030705c0d2550750300c0030850310280302900590b0456924008144a400207000521000001e040d042e6a58483c03109181c00715450340d0301c034840b031481c031019100d44c907a1481800c83c11580185030800c083d4489000149010504041602c0200701501d000034000350051000021808070742c07010049030f80d845541103c15444411150015004810b4155492809034099600103015941c04038440310035001261f28034245103c29004200c04105403840340d9811300842e03022951103803203620349110f03e00c0071407202003405642d90310a068003811060907920070f82ca054501d203070007021141d0454003010840002c0c030311804180d00592203603840307509410a07101210100c4006900800e50101003001c010510402d000b140710850065a00341401b01e44101c800d0700255005e8103001545003841c003240001c540e0800e5019001306030240e41040442d074488203580e84407409480c050b03603d01d50000344220b0311915401c8154848 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 45842207 1250 45840957 45840973
    0x20115030303061d01030c1203020703050f0a0b0106021f0209011205010906090b03030c06060910030c0305070e0703090f020103020c0102120f06100203030c04090c050f0d0e06011505031b0c 83
    0x50b03064010204030f03030707a1944003002c0700070700802d54031125000d0001a206a01c074000c101305014208814000722400380c419609070076201d640b1141031680b403200d4880c9030391180d083c00301440100ca803c68014450380c0010403002015106855084c603420070310400c0e5a40c0411034085690080000c01541070105900f04001d685540c2650300600f010b0261000a514148102940f0304000003100c0320300600c2d07402414243e40304c0c010061240c100034541c416200c103501000002440708104000518485c0c0083c00540b81800b03040d41407050010400310406081c4188000030078459048050a0364081c0780150744c076031803020083e02911514031101010380c00b000412000e071080302c903214003928040300c0185000c941480c003281e0760300050310350a01031801000201312070310700d940c00a04160078a04102d41800014001860f03582c00942c10325800c1c82d120f001d5600003d00074007050b405040c0d462071041748828070700001000c07808001e0102d55940d14080c0043c44100581c420380303001401c003004582c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 45843457 1250 45842207 45842213
    0x20706020a0f0207120206030103060e07120b04060b040c05030604151203120c050306010512060f0405041a07052703030c0106120b010603110711040f0f091a0702070506030702011503 80
    0xa800c850b40744018065000d000c03a200001070703c6011403d030018000342c20350342983c5408000782650541190107100301d0600088001c501c102c600c0c042401280c42c840f0078580b504290055800c4540b049200c0d41c40d002c90303450030503006029640c00c07800075200050400810400c1d219040ca140d0011000d075907098184808043c0d1103d04000c000c40241e1040c0400c105240e01501d0320700094a002d0702080c01440300502ca9080c14042551004009000c8040c1074811307070119086400545080d650004840c00c005981c6860f191225000182890064a090407020783c00c101c160418400320005840d484003854035640820548042c801000d000300b0030242d4541c0c030003031070f10980c10303003100c05200356400001e031107010348101401d13400b1101002c1c0c54400c10b13980c0d44203411101035403154401d40e40da44802800b0198070900c0400000220005248602410100c2c250b02d868030001c40c5a4081e98201b004481d40494241c00b110025030700c494032611340a0303082c0d02604001424102541c0340c0c030000024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 45844707 1250 45843457 45843467
    0x6030212070303120b0a03020d030201060902030c0301140906030c040e0703080d0606110105070c030c0614150a0801111b070b0316080109021602130b0402030103080a030506030303130308040303020706020a 90
    0x88902c00d1315100015a4503640720000d80703141c0e10b40e9540c0900f8135101040541407a038040b0100520910000404584032618403040380c0041c0c070841403200000c03005102c0510054102c0c0c403504803c4623100c5040c47c02c0c40010342d445170700009050060792210b004d010040d204002d408040c40e405420551a107841701c0e04a0300030081486030340d0000380340041c0050742c00010300c01c1500179001c55403001701c0c00513540c070b00341d0b06401917000480c1d44940e90550455420205408980541040c000e040c0303002d60301108000001020341c01c0b90005900d8019408004e805d03400403500c203c811240603c4840c08103891060030000260b100203003041d8000208a0102d001d42190300000c01380e5240c1d10000d0341c80d1449039089000300e450786042c1661007045c1001524191520030b085604035000031982000d0f034004203040e07070001ea02c116030912000c42e000750010f4050081c9507001e50198015402c1d031400c041e10803072951034010050240101000403c040c14481e4045035403807604800305641e01c05010301f0040c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 45845957 1250 45844707 45844709
    0x1305060a05270109020d0c090b0d05070e04050a06060201050c040f0e060f03060703020d05070912060f020405030106120501141b181804110102060c09040e030c0f0304090e0303010513090203010603021207 89
    0x10320618140b07c204a0764021007481c000d5030a010412070500008101e580003c040242c95442030041c40e0307020310303240d54a900a51340318045112001c19038918000010b170135590013910f042005001400140301c0ca2521420120840c5c0800d29140c180d5202c120114104c081c40c0a41c45d43c040c0540820018080c1d0190000c1c000c0c2130754554200141e683c0c11400f1260807429008001d002c2c041c0d07444020101d442d58004100c17071007003c50010700e40340e9110002801c4406580c40303e11901201e14113142401b030284a900500e070150300d0b07242c8441c03500900354081c8804140786003042000100300402c02c0d0241c00304259850101504114210344000c2c801c00d01c03044100c40c120703520504580340d01400d500c08100031b8052101140c440d814440100d04220181141c49124074062105002548014134200084050203030300c6006560b643d806d00c002c1005131082000b10a040f94030403c010082031311940d1113054030030304099000070380c040c0318030010780035020070362020398040100310720f0762000740c03010a13a04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 45847207 1250 45845957 45845977
    0x301170601080a110f0f0307060f0207081209010c030302070219141504060c02030c0916020f070302060717070b0403020105060f0a0e0601081003140c1305060a0527010902 75
    0x1a080e03aa035207040603a50400620f0051401000c6610010241044411250300b210003c010303005403498400401c1c94100c03a0340c4801d0000f2003002c00c1c00c3c01c164050010401608c24000035029000d9440c5680b049889404c16150412440010f000c041c103100358142c8001642c01085184102596084216200104c0c000d0700411385000300160b0186ca4010811155400360903107050a09141100030755442e00c1d520003d0780c040c0500c4000310240e69401d0645442001050501090640b01040003440c1030b990b0691000d803584450400d20150340c0319001d030742070f071584007444401c4000d003d00355806a010b5108010104034002e03044c4020550103400007481250300307850511080c10843c0802a5000071440703580d106500300404125254412580540d05c00741991840e131460303540f40c1c1d49401c1e114483c6442c0d0081c0c4c000c2244407515142500d4020b1205454503400c0c85903081400004e20039142c03500c00c6c4c0e8411072141ea0882d661402c01400c0011000741114941036942e50b540c040340180d840100d2030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 45848457 1250 45847207 45847213
    0x180f07031703060f1002010b060c071a03010f15030204030204090f170f07060b010e0306040c2405030a0f0608250e0405070603020703051e07020102100204150c140102030117 76
    0x325100c0541c40c1607a102e110300038280101c542041050129a500b02e900040c119500e50424500c9030700c41c1e000501900320b950300241040c628000e00e21800c00c0880750b1811410b4001c200401078104c000711018140d41d440460380080381d001078820b40091245520003508035051218040500155802000318140134110403504070b180c81c0d0f8040c0452040a203603c001000502000e07022407620760205005840c181002c50450026000213454200212800c4030340030300c1000305000440618031210b40102c40b18880c81c1424442d20f01c00f8205020080c19019160f55911003041d840c001e90304644004c11000c8141e03045408031300c81e004401c07a121102d100c420107041c640050310307c000c800003070b21980e0030034040c1c07407840c5c2459011030207940300703400c02c1d070030001c00f88205c00c4c00c2043c81c500da060104000a0766580d5502506c0060700301070f000c00c0d98444d9584180001c00c0f0589008207201141051850a09041c42d00c900d420885d01010340030711422580b02100204503800b04104490003140d90f0412 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 45849707 1250 45848457 45848483
    0x30206090105090d0806280f060c0f030806010c08030702101104030209060108070e0a0e09010b030c1509011707030203010501120b0a0905090109050105070e0a0f0e040b180f0703 78
    0x4203007600d1040e00c0400c00f50340070030208a040c0e4403507265036812541c0100603010040b01c205a848070b02e07a01100010000011200421844d0901c5503080c009010504050b0074480294451a600303215003403002d01400175520008030b403603204242c051310f05075101074855280c0c01d0000300203541d48120010f1882d40d03403501a0b82d011f41100c5009030350480758001d003143c0c0c40d592741000454566401500351400d001c0f00107003280990703551440e483d000d804034036120145494045c404a00b92601c00420601070703009680300c00ca05d134940d44d0130070701d56814071400e0a41e18000800120740200d50030750310360722a20448c42840740ca658590001c50485001f40c1c0e130b80d40e01017000320380c810488440e448002e40c00382c0602c008100007405034005642c4008038000001384540075486281c00e4032412035a0f98001421150b0000040c94040c0c5408082c1c02200d000b00c3c452400c004415603007450150000d86207032a568000740c403203078841704801c01420b2000c090700c01048400200765aa002180401c980e1002122a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 45850957 1250 45849707 45849721
    0x32318030606060406030b0307090207050604032a02060309030c03030a090c050306010605030109050c1c0902010909060b120408040f030b041502121503070f0b2502060d180c080a030206 81
    0x2401900a20000f000c4928151400740d00f58000c2420706070761034060040801c00507221825201600b078180c021009004140707068074008000b04802c807070b003924000d08114608110410300458004469042e40c845a490b2100c80183f840c500a081006107144000000c0045484460f0002c021700c41c40365003441c840d01d448508054031244240030300380002d40f0030320040200fa07100c0e40203140c010342c4000300310b07142241e83c50f07031444d41e5201070700396400d10340d12040840f04650f4040c0307400313004012018080040d075041c000700075031902c6280180b051020307070300d804541440940000c84004060f0451580c480e95600e1502ca41d00000c103c130f0a40d220040141c1d5001c0b03440b0580212514000404041480c40d62070200c24000200040344058052065001c08190b100182008401034900d13400c115032900900003240300c0d0b440b10044003940c1d41d40300d000b0440041c0c5422064a003054201d48002c940301040281c0c5e210000401103001d00064450140002c0380e05010800c000300d0fa0080c0c0c00d86260303950b404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 45852207 1250 45850957 45850963
    0x9010504030f080403050708030412080a0b0d061e020307080912070209040f05100c0c02030c0f0303040b0f0d0903210b10112b09080a0206030604020703231803 70
    0x1500540480c07100440c0301c1500f0320405010f54010b11a003899400c0c4001912800f04580040f50b00b01da082c1c0558104040c9142c020151580c484556441405107540000214140407210140102155190034002542e1140407544140040c0384980464403460081c4005000000c296a080018001e1210345066001c4503402c403450303150098082d20007500c1d66a0780d46140702d2202419a000c0c01415620110840180580a1030003800d5541c1200c0f440c02e401098203040c43e2941162041e400b9180450507078401105880840d078103144007940b10900ba0104074101d2007031400710408589001c3c0200c0806400c198440080c2d071545482603200010845510220fa80c10354410b07038003130303102c52001940c1c5203e035041c0030302000c622041d45c40e10061203905403940011003646050512070322049a18030b60380704084000419800004107202c014980200b6850300c0043c09041c01240c000032f00c6030625015480152241c0c100103803405550f03040351a01510b0b81c1240988964000c0c80c205905400d10b800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 45853457 1250 45852207 45852211
    0x20c060f0106090305071809060606020f0d110d0804020102150717060f030601050402131212031b09031e02090403030506030105010501090506030f0402120d020304060210050910090503160c05030105090105 90
    0x17020082811034106494003160000c4603101c0c00001d03803182c803070783c00050b480c3c000d0000500319a0010080e4524001e032050801050000840c20048541038280071035900080d448120761490074095540d40b20740c00105c1c1011107001448002c50700103000d2200c4a64001c01c0d0301112905240342175981d45803081006401600c6800041d81030344041e0040c000ca01c1e00fa401018008601c0180c206a540c0d034004540c542484c03082b0545000d804101c1440006801d4000c08400741d80c4000c4e0921030348031081000d0b10601d0340380005410001b1100840308070000b29030303c0da4085c0d500144282014a403629008010386412510030f40a542440c00002d955401a07040c402581c4e40240503d00719515044907401c29840144240d90010309041411481c800c1440403103581c10560703000d56078035810080044d240040c5100a413600341d00d0181000307101000400d00c0c60581c0c42601012580e001e0900f8201d246010380c1c628041c903c5105401c00e410000d181001e641110016002401a580c460b480c1c50308071101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 45854707 1250 45853457 45853463
    0xa0c0e070912021e040204120602070b09010e070311031002040b0a09060e1507052e0b0a050f04020307021204081509070617071e05040503012a050c10020c060f01060903 74
    0x158400303800490b4030540f04d0481402810040c2401d943d03022180e64440030010550f007040e40040c407502070111000903075031b0200c100e030020b201110592451964666a510028001c4c010700911024655400d000740061500b42480c15510381b912890309014036441285400e0210700380c3c140c0003030801d0089550900000000b018072860200e804140c03c0541d0040200700d1b580e006080b0507071481d4060506001d20300d0426000c2030007102e000d0000c0e070101c6203590b1400d441800111000c21541da0ba0703c1c0e008031080d2003a90301685070346609a00303a25110701d10b1501340c41c5400c0480d02080682002804c07108400e594080b1040e90b880d6001919140c488500843e000648100710780c8541315901c3c0c06954020a840c900300c198000c1d4a1103101e0007100d4180d6084c0040c1001408115610b000d00403030941c1500042e452016100321100b0341c5540d141c0482120a1010215039000c0254081c0032002194120b00c109542d0341b41a60007071a2a51000c4600e5408580349000124000b8442c20703034101600e078 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 45855957 1250 45854707 45854719
    0xb0f1b1201140301051911070203010603030c02090f040b0412180803030a0f05100303031107050d0504030b01060509100e030109240c020a20060405120d080603030f070b0402030a0c0e07091202 84
    0x82c109200b4020700601e0300350520701f03a020460500182c03403d1049000641c003960b55001c105000c3d104100501c0700140409009602078000d21000c03030a108011500705034411041321003d558201c2c03c0d2000d01c10f030f01090b801f8454034000055204004001035224410364a401c102041e8143c0814007140d0054841040581b4a2130003031001a019910926020205100e090f081c09160b944541c501400540b545001603008182082080860003003a405008507040040c106842c40000c90401007200b294007040101070403d04100752000c1d07001140380703900030070128421003d401910040f11144428080402e11b80101e14001601c0824207600e01a0b00005c55003a06c10345590b2609207404144045502030350401001034640d0743d2611100c0310382c105c100076184054203c0030241440b03000400281c003d40081003c1c0c1018080e0f4400c9405c0c01b60300c281842025210390010a14010031804000d00007111464040340c0384c00801d81c218070031020f541d5a4081c0d40d8588065105203030316910020f42201d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 45857207 1250 45855957 45855991
    0x50d0f0212041a0304020a0f060c0302010c0519080604020f0a08090c0a060203040608040c050d0510060e0c040905040c08030f1b1203010e090c03030a05090306130b0f1b120114030105 80
    0x1d0f4803c001140c006000420842c1c001e612103608010007041342c0e2001d400b04030030200c030307000b09502801041120038a03401c1142c10a988051246110030f542c021541c02c102c1110300064540c0d65540c141e0344646c2c2c00328901c5c0c1d22690800d03c0949040c0301541c940b070031407081c0c101d1100c4e14a000002c0c0c0c82503800c154082e43c10503150500968a00d00040c03c12100520441c60100c0d4603212110007600b07a0380500010900584a1034840007140c0d255000316951904010401414001807001c90b021104600b0000641d5a00ea040c1515001d6803a0801c3c03095000c005003404c2100600d001602e6421480742c8004210144810034030740d00c038180b91510042c0c41052004102c1c1c0045605951781c031000700000d64005101810011741035a0000702100089103022480084070b0500300f044e180d100064252158000c0c94a480c0c03181750a100502c0c0d044044010b8000944041c0004000e11000c040a40c019844107450040844024401d004051f135440c005000031800d407405015544c091081301504207161 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 45858457 1250 45857207 45857249
    0x2040e070503031917100312030b06031305010b06040306060302090a0216030f020c0306070809010e06060d080717031509130308041b0503070803091f1e0903050d0f021204 75
    0x1451061001c1c0003400400b000d4000d000c50705d05405072140d50b030614101609801d42c941400a10382c2941a103003090b1405000da19980c4031041200e070010b0480d92480c02030030541c40c003e809840286c00d0703140c01140c00719001007084150707000042501c6c8202e45402d04c1d40e171800c04c21822801948104003c5403000f8009001283c094030400f019820342d813040c1d5020349000400300c1e241c0a4161862030000301650f00b04031078a0b07003c1c81110641c6a6100140c181c6007441c10019083c0009604003429465001a03007001300300c121500c0045400528075255180e00c2c00f00c0320066913941105565004512180c006103100280c2801015041d6145d203501300f0503140c50b1904c0c0b02ca5010354209108451645c000403900f550304000210040c0601d200460380c4102182c1806200f000c103000440046c0e04246034100e50b260002c00d40c1c608500c40310b4510030f04c401d0500c0211551911540017030080d0080c15480c88803103510140d4034141600301d800301c07072845072900e550302058401c40c0300d040408441a00020f280d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 45859707 1250 45858457 45858487
    0x70503090402090f030102180406060c03090b030c0903060c0c0610050918030405040905010504060b01050c030f090d1406040302120310090b0619080f0702010510090b03070801021602040e07050303 86
    0x1a4903c080c0030b510032840f2000100e0700b280d00c0a241485c5941c1060102420707032a15014141c080d2046161070200c10030300c0e540240c80b0b2080c1c0e005101d200c0c0804030020b200800300000f95024210002d0844002d41480400c540c3c040e88043d03500070301030080030001190701e004135a142040381c401401c04c1410f60f60b54245100c010b076803184591030f540001c01c0001100e580350301407100c206000740000145400d052519804680480c0946c81c1400000d0050a5140001002b6202503078000840e2959882c00d0900041c2101c007484001031010005071003a60800c80009105841a803182c0c0884001c00790481840d5007601040300d000005114183c0d042c050141c0039002094284000f40540b410030341c840d811220031010b42200c8000107601c0504200c40f80f050b0401d25a080706460008008506000100d40007088241c09030094240e16048045610b44082105100501031038008544400855a01402d42c41c0c2d1203805a2003035082101d0000d600c1800309400341200d01c01070003145000036461841103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 45860957 1250 45859707 45859717
    0x180c09060e041503020901091a090f0402011812060219030603020609060d1404050f0601060c0201020c0405090f0a030305100501030b0d060b01110303010308030703050702060907061809061701060b070503090402 92
    0x10f0700c40c40c000d400001a1200220726000e050846804100902d800f12600300d40622125101c1c1302c0c00c00d000501c020740800107035140c0c101d90207107040407614540b10013045c40421990300041000300c02e07401440170711180340e0142036003004402c011600005a084214161411070001035409141040f85102c24075101004200034038819030007041c040d01c284402215102c00b203c056480d0b80003100e00503900c180c1404454050b201a0518005d00003458000075541c80c140700314a07000f143d03108040782c1c610350100686c0c5081d10101d4200d9000c0b000e50324005010f00001c1d1280428060303c83c0c4041060b40c001c2c0592800400058990038100c240c0d52038150180500364000703410b02448a408200b41817090000314003840c001e0040550742e0a01d814028201c03132001349000b04540083d0144903420401080c0d50084a50300c5c64102c401c1d000c050000b0544d00c081da4401c42070245040c40005c0c040700390041b41e10300402c43c1d1008201d000d5481c0380c1209184640d210080554200b0800040c0c14a059400b500c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 45862207 1250 45860957 45860981
    0x60601030e01060e090102040e0702160312051c060303020c010c0534030b01030c09020315101103130e010b03010f0e1b0c010b040b030c010e010815030106180c09060e04 74
    0x8039403250740390040000204107417008a0b00381d40001d41800290800c91f0740c550080d85601c020410f0f25403100030500d00d00c0b841d000c000c1040b030240d460114864450020303549080c01c8200c1a001074584901c0c414014402c46c4801c03005130040440800140d030248044e0450242c118002d0f20300018801142d0200303400101c07005980704414012503c0c030b90f90b060401400f55106101c402e0003541542001e00c070080c0e00b64880c0d500e0900410070003d040300c8480112000f2a0181d5120010503100038003034401c0e404941d1070110714403010480034a895080300002040320b07842c02500b51140d0302c800345001103100034010b401448030b000208000340d04401c2c0085500c45c09859408191044841d00b00c40203501c95960403007140e442c0c4100505510b01449400701c030040480c02800c4e00041040060b140011052065060009080c00154040403071086401c090000400070002c00d625298070002c0c200c20b040c03941807510300d0424440a0540035000f01c0c410b540030360b214900480e500070208000b810342c0c0c2082d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 45863313 1106 45862207 45862211
    0xb010b131208090603040201200a03110f0d08040c0e010308191d0103020a03060b0301030609031b02030a171903021c02070b04030804080f07050d0e030a05060601030e01 74
    0x803044443c080d0350345900d90351b4038001a20003804015072a50404041c0a4442d101e074030225002c64407510948810002a04854a45560311109540e60707101d94090030702014007034054176485920922030718000c180142c4038071100941000c02c0c3e1041b603440c1000704180c048001c40c80c0d05401180b460f441c22582001c00780c18180d5407203100c650703070605040d8009079041c4000d209070061400f4000c60f144095581d650303441c1c110b00420100307400b0380015003071001242089521845030708405400030000d0900c814244c50302d00c101c640c8100804139070203080155403000f007048580c00700c800ca041e48005864410018550312054043c1300070201840c8100705e4040042e1450103120303041901031030210b1941d5124540340040d40305810480d01c5200300071440c003013080340004000c00007455030781e1540001d84c10303e0145690344602e400020710036041040010025446984001c038040c2000c0c0c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 45683457 45863313 := by
  have h0 := BRFrame.cov_init 45683457
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45683457 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 45683457 ≤ n) (h2 : n < 45863313) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
