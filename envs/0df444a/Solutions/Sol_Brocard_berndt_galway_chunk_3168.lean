-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3168
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:02.302787+00:00
-- url     : https://prove2.me/submissions/2c80513c-69ee-4f41-b8c1-1828f6727bd5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 569604316 ≤ n < 569784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 569605566 1250 569604316 569604337
    0x50d0c11031204171606050718060f12050703020d06050a060c08070c36050112120915020709110403051e07030618050f0c030706051b030301171605060f 67
    0xca0111a813080c503a09588044485180078450400c80010014240507896004125107416029509408400301c4030790070314001c100074402450b0051030b0041c40f803c0200e00702d02802c00c2c00d01c01410503203000781c002d6004240b540d10701030800401040d81c0c1414100d178812114541c0c0c0e054010b0256440700c030900d4009581c00c803001d42c2036040004003240850a02c0340d02c2001c007441180d41d0100d070480a4140a2050041ea40090400004000c1d6a20030a20700402d95080924591000c025840c1200e40c035003140c200706d0340040c403644003180c034507400140d20041c2c4450348002c11046480b10240300150095200041c09903114040b103a038480381e107965810300e482d4880106d424582d22683d0b194213a81c80e5048000b10400404510010300034204104071409401001401c5611581c4000c070303807a0010f9001d00f2052100004034941c04100c200f01c1070001d1104607050f60f480c0d5864a42405c20a884040c0c1500c440c8036043c1404442054840c0d00da003140d000030f148502d0844024120b460b590484044034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 569606816 1250 569605566 569605583
    0x3091d0c0a12180b071701080d0509031f0c120911040c120906020a080c031003020915030601080304030308180a03031503020d03030603020406060f0c020909011b050d0c11031204 78
    0xe5018000380f210052185200b14190262460b201038000c0c402d14498000c0401076419030010440000041407a03e00420249401561141044003080c44c2c81240748070032a10110b8618841500c0c00c0e141c0c02072001310742d182d9030f902c4a640560f41c100700303981d00d081c00030b044004e1081403c129441c00ba4031085000c40d0905140744449040d9441804444c44d0030340650300d0940010b802c1c1d42003940301e0041684241840f0310075040d410030b40f400c03059509003400021300602c1d00340d0105000d24141e000340c0314007801c014100d81c0151707191a003a507100d40040c8801c038040703142d10000c03420b807807800d000001104000760010800d000540c0c42c2103000d8810007030216020800300d000800962115010940c1c104e001e620b01182040c40c1d48144400c8550983c0f0000400911140c81514242d0001d207036000103030100d03200d00c030a0701c5001403140184400c0420340d0046e80030700340516409400078040c20182e000c01c502045041280c000590301001c0800707041d2420f401c01c00c090054100c400c60300e2500a400784504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 569608066 1250 569606816 569606831
    0x105120a051501051c03020a030f0909090c181415010504180c0f02160501110708030301030b090712080706021b01020d0b0307140609240703091d0c0a12 67
    0x22582005800329802c00750140040040c00b2170706141c0149006403e0390040c002c0c03c43c6041d20700949846a40d0401400c1118140f040c04215101386209809000303e038108200b20040ca1924a5200c81244900c02c00103c80d090503030050080c0d44101405003240c0c8941441c1c0d41d42e0546d003101c3c2c0d0084541c00d141400700900c004500c50707064018480310055820000680003203c4c01c1c01401500141040c1d00c1117500c00d214440d80800c410b001d0500700e4600f824401c4d52181a0112181080b005130000c1d18075110100000050207042d40c0b00b240500e05900a41d9aa01e0720343c03005070f40000026001801c072440400482d800550305038020422001c00c4000c3c8000d003401c803940389080e40d00c02c0e101c5504480e00d0700c1000000d440c0c10b010b40401811030060302034050340d0450100e0a6070240c040030510641200c402c2007109406a04042c0c081e1428005403903651110b841d0142805c0d0a85c06024406c5002041d15001042035007889401549058112400c15501e0101210f40250040c90030080302d840319507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 569609316 1250 569608066 569608073
    0x80105090f0424150303120e210f0304030201051b280509030d271203030b0d4d060c0c0315041103120f07020f13090204060b09090105120a 61
    0x4890740003208010060b442403075820018804891071f40740224951802609a00035000068800d002c3c56030001050a88030b12208081280c1c000d40d41c0d0702241d080300000704010158190310803842a110554038003440345d14020040c101e070152002d01400764400101088404070050143c058401c1e50b0301e001d9203400340c421f0100741440c840c0d84206010821a01100380c00781215a44e0510a02d5064042c00302b60340f6003254410b95180004000c0c0505a076806013000c1030304d4100310841c04a03040700307414040800d8a00b001d0345440038121f40480c10f02c03a0805104081c9034003914010f200320703254801d001484082080081c2c541c00b040841096114a050b001c816031000d019aa02508142122004526290429230351800114001c14825004100d20400c400d039008181c03400d09443c080e03201d40702c64051002c103c83c001c1c043c016a510100031009400240e800360001c11802d0303c01d607001d00c50710f907841001315014040c2c0d44804c0c3d4000d005000500403801c0601034002c0380e813040d038100d0710581c6a07a00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 569610566 1250 569609316 569609321
    0x30503011806080f07030303050c07021806032a0a090204030206030a110904111c0c050406030509521a070206030907060f0906050f03100503160303080105090f0424 72
    0x4000c04645c0000310100141a010b00c90742d80d1200401303181c54a04400f90380000c1c02d2100d901013441ca0b44160324049640d645040122007108111010914034038000000480d14070500010312901c40d554256001c50072081d14001d60b0102c07540608424256200d8406e140040c0101d14034414031684148074905165895005200050201407510380d078401c0c40507040d07895944854440e590b0f1600300340050340c5a5a010040350b0849000c3d01d00012107031513107207500d41491040060440c02d107542001d2820740826002502d003014118000c107a143c4903128070b051100300c519595501c9000d00c00300f030400c905c0d800358040b41400349100000e946007003000c1d03000410703980080d2a0a0711544c80650b05026041d04400704201e102a5414680c44491800c84010210703c1031072460018441c1c084080f4031030300c0605186102401006081e60102e606d407a50460340d6048500c03056001070040400001c0c503082003243c090003220780f003085004640e1552581d000d4603022074a64103071f042d40c001c200c10740b007202031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 569611816 1250 569610566 569610583
    0x290d11060d2702131505090703200405090a06050901051c0515010f09271a0a0c1704020a1431060e0702061b070503070501060603150303050301180608 66
    0x1011039209079880d42c0144444c80c0041d64103907407140e1a08812255451340c07a0021030031540b08452002c03640c0c0e500403040b805807090702801c0c0c42921103001d13903003034684000b409081500d5050f1460304440e550249004180c45040c81590b4100389080010312481c200f0760b418000780741e08042c0c40d002d1220650740d8186400060b03411091010a00030041c01900c1c1c00e0b0302560001c040084042c0400c06000c0d8840304205844040c8600040b4546810000c00200600f48220100c01c01d85550b070b9032404a8400c40900a00d000131000039507031002c01176005520400440c0200e402818036003416042460010354124075040b440d61240102e007100e01c01219102c0b0968003180b44010304c002000040d5100b40558070190403420f480c11303c08040042c22580051110390008071560080d03180012080404458410180054031a010002d00b807014084150003e008864a41c0e80411504400340500c0102c01c105000c01400110100010440100724103803c2c4240d24420380300064240c1d403500c9040c9001c40c503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 569613066 1250 569611816 569611871
    0x1303080618160f020d08070c020d05030d0504020310060b070204050a060e040309031e0f061a0d0803090c0a0b03041b05060706090201030b0604080c0616020301290d11060d 75
    0x35002c02021082d800502e440e140c0f6694001002880040704015002040003088a410030201c0c1d001c140543d520302c00003881254209007900d0303560582400a40280c40121010380c043d10503a000382c803182e910f030301c580001c840da03c40813641821310076801c100140c08041c000d200b10544038580030078400c00d031070b00241c0154403907101c007490b13076280d46401c011000c03c09400c0340d1001491040303c004507200407410b11131240d000c1d030000742100d408130003011030720102600c06801501c0201406c04020722000254012105582100c00008a403005c01c0070401d01406407042c030010034808203000640c5c0385d0010107c4100132550810141c0c80d040815003d07005050160b034079907203803c1d0000075542c040c401c8004220050741d0040c5000d0400402d00d5a4000c2a00418000c000018642e050244d0a021003484075900034000d00c0aa000c0920165454503c1a00c00551070119612128986806038040b030009501012005502644104105150304003002178803045032908000382c1003070070300d800880f0403000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 569614316 1250 569613066 569613091
    0x14120601080a05240604020a1103030c0909090106050d031227030f0e360906011703090d0204051509070201020a0306080a05100b06040902030a0b0f091303080618 71
    0x200ca0400c280341c040545003135030b1240101d00000500182c15100309501c00d03400e8401590b6400a0601107410100e10390b50180b007400044148080c085a80004000e815070888024126445920100307003200c44074410542e07c44900368000000078082c04120f4540c0c6400c075030001d10500c103c0c03420301046d440300d10312420040074940703035004160300b050350440c0840c507626240c400484c40e01c01041e81c481c0a00c816000342c203c0c60b11091040102d185e00d400b900101040406410b080c07241320260340e980c0a00910845c1420045018046a00007041c3d405121000b00703054414504da400380001840003030304010350204511828041c903115541e169020701c40c0f036400140e98203d001c00c003c00303d50044d00556048c2d00a900c082d1701147c800143c81c1d201038010340f00001c48440e048001003581c82607070310940103a800801045801c108503441540500816038041c030f401c6500404100014504864014001188090200c0030a1007904c1059009402800070200084480080c05840208036100d40300c201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 569615566 1250 569614316 569614333
    0xf070306021b060f01051225030606290f1603270305030403061a030709020c0c0d050d12110414101103031306090c092903071412060108 60
    0x403107000005640003284080c0010b420060502d580c100d07011b228040c8900f0204003200100f40080c00380708603100a00410004250b100280c555a001103840306030392140c40c003800010703034281d0000712a0030004501030f40c401c0c0717002c0c0d4110700341c554100d00c03070f40c2c18a0703072042c0240c50643d43c01d120035120941c0a80c982141c201006900d84943c0704030030007490381c207070200d602c1040050000000e640079690701510108403904200e0700c03540c001c01003c0341240d0600c1880c0740080c0070740a0f81d001300340b421f40300300c00d44100f0385c2d1110034001c404508400082c43c560203e2411440c5522071081e6035080306010b0f1010450150016030440290842e4001c0c0a190640c0400d41842d8a85910216075402c0e250900824480142c0011a100c0c0801041907200b8560042c001c004c11600354401007803294009900c40503507443e085810700601c9400c41c00c0d01360111710000342950141403100300241d020004c0081144c13904181001c071124540300000e503001004c01e0f00c201c12041c0244591400391070240020175040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 569616816 1250 569615566 569615587
    0x908070609051c02151b070b01060201050a0c0905010f0c020a1805220f05070b1801022512060e030c0c090a0903090608041b060e0310060f090e0f07030602 68
    0x11003002a54003000741e0401c6043d54443d0045440503064403c03001c030240136510940600c002c0503000c03480782000e040c0000c07034400308806070079064184c0b04c1070b40c002c110760303510800c00c80106c0f10070144c08008102c910504019a42c03161289c00c0ca106801c0c545429405103c0e4041900340c20140c01c0380c09401d0003219030306130301602486200d034001400c40c0025640c024050340748020724044180602007090206a01c0c051090401c5410020079488080c2c030307980d140400b001c40c0c41fa03d2a58104ac018021080c03c1c00c16024511860b0010214801210000514000c200d9844480b0140c0c1110356a86403142003210300f10034005419016040806001103644440800a107040000c1007000c142e8940400da20100303070b120070440107566035402c1120081c0c95078140014000c0d0810115080d1504141002c03449940c41107240d50303061816021500812541c8001074151b8000340103482c607052650307030104044003058000a08401000081d01e801c401c642e5a29070910310b0540080d102a034001540c64841c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 569618066 1250 569616816 569616823
    0x22d0f1002180a0e040f14032a0303061003050a0e0307080702010305072303070c050a050c0109060306030b0a020f12010b0a08160818010209040e060604150b070312090807060905 78
    0x10490b00300c556504060901100c581041000f90000d0290044100100100041107440000c0e40605900301c17a1940c0c0d12240b00d903000c500d402072800c5c0400002e001031040103c00010340e030040100422a4499070702442003140200340c000c01c00d1800c1034640d03e0000c16843d0a10007401000d00400c1a40c0e95070b00b081c0005401c3c0d9401030084400c0001207906403842030031600a5005000f0312259869072a02d611034111100000780c48082d006000701201701041250020760202e201200780c0f5000489681d80009804480c403d00c4050103241c2000c001502e8042c0795070040030454a100640e50500040821440108e2026045661003e00029000700d1b299000405c940c0d11020100d544922051001001402d104000e0010010001d940c40d0100c3c0c20a402e4060b507403044009407003000300d00c050310700c407556600302aa071050003985408003a0711501e20807080c030702c02d6807607040019146c5510b56501302c8440780b40b0300d0350950141d95a000800083c3d00034004146242c05010007060307030341c0030b401c01606 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 569619316 1250 569618066 569618107
    0x405010b0604030c0e060109180209031203070c020d08120c0408010612020607021306090513150e1507020a0503280e13020c011b02061006022d0f1002 66
    0x45828184401c000282130004000142e442c90780488500d82c4170080180d40742e4160b504414480180760383c10301a0010254040c00c1e03000c0c400c07401c982c4800000c4c0c0070700f0721911040d0340120001c0c10040c10040542440700f0480300b110f21036590180b6007004220003a040040c00c0d80c1c6486490000202041700c60002d01400300603002501403204c084040d940010114400d001009025180c240907003042030706507600580040590910074410f0b40b810319100b00d02502c243d2801c5480c42040041d014003000e082c07052000e8440000000c00040400004288141c0310040002d01103202d04042d6030005007081c4007074502c0315002d500c0c1c1800480540a1050940c05448800040180050070500c1c19601d500141c4414212100c005a5900481013114058112510707101402c00600741c2d080e81c0141d0009000d4410003900440200d01e54942800700c0c1c8a03590a2500003094080e2184d0020520b55181c0300c480c000c044000300c0300180c5600303400302e04059070011180b001c1c0d50b001c02c1c4800c00668032106100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 569620566 1250 569619316 569619319
    0xf12180901050112110702130e0d0e0901090c03201914071e08070c140909070e0702010e16030605160203090145080708060a0e0f030f0418141305120a080405010b 71
    0x1882f01a000d0045900c10300b05204070329100f070b143e00b1030000a9003c3e0f48075403940c141d40740440c02e41c40403800020189178004801c8039050841a46080d603080e1146580c4224820700415542c54682c107a01ca102e04181d800f12101925124145407900080141005044940c441c0c4400300380703985031100080080000c000c2d03482c0900c000804110984202003009401c0d10503c240080c0591520303201203004200d03400b540396041c4107010350041415107101c03c5038100d0707200b0001800316503130b80341c20f0880c020300031060035026a00602005030190300500045110f4140604900040024411150714094403076040c4a90312040b005159040ca1043c48010041d284080081c50242c0c6402401c0d59541d8009100d458803da49100344102c80c6002d1010080300b24107a0101c80d03c07504a041d1003829540280720f40035188942c00100d00c3c1220450007606070b060705c011021070b0b03290b8030240425030b405000c4400329814000c0d40d0303e2213130790038039500030781030300003c0c1d6507140710341d180510340390303003100c400b840081d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 569621816 1250 569620566 569620577
    0x70e0a05160f1110021e1e0f070b24030102092803052e050408090603040c0e1f0905010e04080a020f12180901050112110702130e0d 58
    0x1039001c0800008080104074030704107900c090180c00890b050b44080c0348050f024000c0400c110300e80f010300d401510314003485410130191180c030401c0384200d40c402d0782c0d000051701607142d104910440c41500940051101c1c41e0030039107800c00a0361402e030165004c82d5100b42d50044010314580070a241c290103c003010301038000718030b03107420280010300c00c045202401d00d0038200281c1c80000c142c0c64560b4000155840f0044446c166541484006032611000c0003824401c40e00c884c0108104840c02000d0059801008070751030281c211090041a0f400184161449d0004003400940068a01c00341f84c854001c1c01504145808414040e55400c0350542c0403404a9007404014030507844980e4881d81c001c3d50050307a8039982c9440e13000503401d004010b01142041e000d03100c8a080400d224000402083c14000103404442184808004d4600828042c450002d610350148156960181d8045492214a60440c3d402c01805030b000a0820401c031624405017a2590401d0307051400400615003151201d0509 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 569623066 1250 569621816 569621821
    0x9030302031e19020f2701020f03030411010302071b0e010603110306030304050108042f010f02030c120a0201020d180b070c0b0708040c080d020f07060504061b050102120108070e0a05 80
    0x3c0115007100408400b07002580083c1e14003030b609000c2e00b1244c0306412285400a034881c501b248030034034025800301c24094002c1203420000c0c1d8002104403032281d035000b400d449030f00e611540110000c0d001502c0c204c03607075800955175090404101c0c200000604101891141560419000400384c031112004100000030034014000e0a070b6000c002e907006e5071000c0c0382ca45443da40740c0c185480344280000c805c0303d80d0004002c0c0e041010002d0200140b00c2442030300c400340d40c0700c044e41089999100c0c0144104054011000b10407480b540f810062046c4005072001508201914002c0c20845d80403204804c2c81581c0790011804020001e11060360004403404c042c5e040840d03a4a80020500b0018191410864403200180400125400c10006407400d6011204401c104040c0659079030340da0102c4100078411100001101803140302120166201c2e50343d601e070050703060807035042c01022402044419540a02c4643c01c00e00c1c030160194002d1161718000d0141924002c40d4202d18030000c2c1c009141981030508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 569624316 1250 569623066 569623081
    0x3030e210d020705030a240204030b0c030a0b09091902041d07090b04060807063e0f0607090902030903090415180969120503180109030302031e 63
    0xa880c040c200b1f260640f03034000131561000f4031541d000100f1071800602404405540d51028510600802c60b040002c10401c004011400070b00b113031603003003e510604202407010480800d411055101074004507844090600c1000c42c00e10b060250305840d44030b039104010302c4505000d40c4000b60b105580c00c03c041400d000310a80c85889074050708050200b408940c1501103104400e80c0e100c241302c115131400c441401c008140810f003460080c14498800c90a202c440508003052850203030030380b40c8400b190b003407420f88424040c0d08001d2030410301d07020602c44039440303445500522540d04401c0c1c0580a0322824008038400085002d4030900103245004007901c00904150b011010740e2100300307034a046420004841c1036035900c207041034811410306c0190701c950510b480d20b1800356040303101c0419110706641c0c0110342c040e801d070344030040d14217580c02100d440950b00610085130041e007d8401d19492507100045c0a09540d801743c403c070000381d400000c010010043d22041005d1512004406259007402003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 569625566 1250 569624316 569624333
    0x1060e090a1112041106030109020405010815030d0f180b030601110c01080604111c020405040c08251103160b010501110d050c07031b150c0c03030e210d020705030a 72
    0x900d0110f07484160300200f020f02c240441a40f41104000f0001540c0e580c440b040039010307400500c20140462445004961007064114052060a00207030041448400885045541114034000c0c0d03401d00840800d0307200490080384025000e000f02401c600d0b61382c20710b140010100400103900c24403070f812200443c01d17140e81c402c10103600224101d8004c101c0e120410b5400045115000c0c4080c08099036010b0008880d42d03c0d00504102c1c0e1088800700441603c051065807114811685100322815040308119148482c000340c1c94800390030b02d80b40080c084040392031455a809200c0600c4540940d10103a010481c880c09040e000d0b041c286000440880f0083c4e650340d0b03540404500000707004010600303910407041001030800668002048038044102c1e000b82e40c003500010701821481240001c040c080c850302403991511140c2d8046074000d0301c6441c54908854054401d108241c0c0540c1e694504996601015001080350032510040d2450a52550020b850030300b90764401030207504403402c00c401140004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 569626816 1250 569625566 569625577
    0xb0d0803061c030e0919020a12240b180303040338061e040903111009020117060d0210050a0e010f140d090611130617190f0501060e090a11 61
    0x20380b45d070307611a26810b901c0108114404d000c0d95945101241c1040700c0c40d40301000d104101c10801d004c001c0901d0401c1e0081a803502d0f071505803440034009004104d428401002030040300310081e500e1581c0c144040c0001e04542c000d900c1030b43d02201031003410080701042d0318001000510460100340d60441c0d08550a0745810080c5072510070355140b9008020028202c10301d006841004008104040d414a0090620500e2086200c800d11500b00300170b4030068140301e98942c03184c05131202c0132440c011480742c091080000301a1b43c0c000c1d460301c444000584a203100845001c49544409484000d0181e004080c0c030048120241006985501d0403085a000b0380c04105d0300443c00e10540da0f80e16007113007000141c40c0001c0010036480c58031075025440c2c040000503205410302a032441032441e0742d44bd030480d1100000e0781041782455034080403c49403001800c850340425443c600118001c4400e1441c141103400992090740400c004841036040c61514031580b9520844201c401c0081c15a005044e45e95070142 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 569628066 1250 569626816 569626819
    0x618110619031a0301050907030303110405010801120c120f05010c140904090f0503130f0b04050a09020c1501030c05122404051204031101030509010b030c01120b0d0803061c030e 78
    0x100d43c24400340c40c3d904214100060030180c001d0150b070812010300b0359120500d2005400103407501603100f40c2500190100c6040310b10507504d2090507424000d21500303805681204070303a44400e455001540c541a20541402980224480c07088841c0d54100749094030176440151080014482e0500e0380300c42582c0c10703101d540100b48e03000102058249801019003943c100c014010344000304620030304182803805502540c05800003851199911840c141041c003481c0240c0d64007110310801400980e0690380500f00c07044806044690b0071a512101000705103017a041540c800c200040244254240900c180910310b2144c0001d14000c001c1203000c0e41944000310040713000c0300700c072004101400420041412880103103511155125602c1c500ba00c04145a0201c0d103001c40c1c201400070742804030622400c0300842e0040c01610401c061400112005212007561460b095a40d0900f08402c0e2120707003e11520a06c500c44541d501c0c140001000003c02c8005415011240c8584d01800025403121440582010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 569629316 1250 569628066 569628071
    0x90f0103081e280f020a06110405061801090605120117011e0b030105010b0c0a0b07050d02130503010b091006082715010509090c0d060207061811061903 67
    0x1d40558030482800e2200322002e010105064200714940038407031400d5034a00300c4050400102440546400d2080501d030000343e0850b1003683c0108219402c0700110307188190300701c0d180c02d44542c0050002d0b0002492070300c4403221918003c0701540c010150b2400b030b14050500505000540043d4805101d0500800e81c142c03041058a04c030408094119461180d08403800d80c601d90702458064004140b0700b2180c80c465824980001490116202110380c0943d81201031715040c105030301c50003070105014102104000c0c0800034092006014070207041c019014550104035945040205800d68910701c14182c82805c6400500c0500308003207041d0802c65006080068560b5516030014040c4000000e82d1706c080458803c0100c2d98540224182540c072000c5042e1500a9072107500740a01d040003100c035180e0130b900c05491742915141015602001c14418500545040320f01da0b41c02c8140c030482d41c2c40e49400011004000d0410454520251180e0010b0700e81500345542c6260143e6814003a070180f0b428942e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 569630566 1250 569629316 569629327
    0xa0206071103060f042f01030506010c05060a020c070803041d0901110f03070f0f0e15090a080d020d0f020d080a09020a060914010c170a1808010218090f010308 70
    0x9080da4181c0400c020050a998052801103c000000601241d0459001d01c8100c000483c11042c0c0607400103841031240b0f14440c0704031000c0194020600500b20f90305000c042400e41d0005042049810301c80c000d880d40158440c2c000492152410446030044101c940003840180600c0c1d10009900e1016021a5031320031507903c0340300c10b42e80145040900c2c040b400300006251801d10004900941c085c0a140d61942614556403a08030340c0705071400d005500084602c070306806035182c0800208080c1c0a41c10003545407501103000030b61003000d03d600404580e0003801e40340000c0c035018000c004466015040c80401401510340094454010354495014410140042988101240d000c0b26100d940503200c04600c03900c6000140409101c3c2c0b1030315051710840c00908019510400301084a140c3c0142001c00542081e1500266504200d040c04104031508286a1003070b81e00074807a500628004000584d0380b50743e41580481c0c045022540c40c0119409801c2c0000d8071804480e040c1100e41001c0c0c604c0d02c44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 569631816 1250 569630566 569630573
    0xc0d0b070807090b0310030b0115080a020d0b030f010e0d050c06040b0a020405190509060406030f060e030f0315090a1118040b121b04110d0504030504120b0405070f080a020607 77
    0xe00c0e1a0401c3c030f1360a501004000d44401c04403410400e807401207248180c9a0b90f1110410028400344030640002095600800d0354040705801130314010001000102d04401c4103000310f45001c0d810500c41d29260b445006207551164240a6a05052b0f003610b0f10600e001c41c001200e03a5503000142c0020300c909818400104c0014266044d2009020002c1c130302070418a00c10304c0102d8505031801100d128005036804a4020b203024818582241e511010030700c95a440d5460b150000c01c8004c8215101d40020841b41d400e441014004600c2403900070001d0600341c003a5414000f0200c0c004103c20061440e10340110341e140e203180103848185801180c801490041000490301400c16881c20035000f60b003860b0000920750000c100c0454221540320b9035035141d1a0101003005868815000941c442810080c0421405444e0410b0340c1c428024100580b0301580c0c3c150401094080b0031083d140c9009400902c0104601801301d000100741c00248920f02034104205e040d120618014001c0c461000018050b080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 569633066 1250 569631816 569631827
    0x5070803070306030f1b08071401080c0405060f0715090c0e1f08010c0305090309061606060b0307031b0c0506011203140a0908070b0c0303181507110c0d0b070807 71
    0x14562040d15840e100305c0340d14043c0504907104400c29119034240d90081005600056a078046800b80030944801200070300c019903124501407c10704c0d140d0710030880032543d6110b4a0041007080402c1020555803411820030710007185104807542300d201d080c01c2c468004904071203052002d44481090010716070303e401c42c80300d02d00031000000c0d90030031010890000700741d20306500001c0c1c030310f060391030070302071035480542082c0c4910410520580c05034007407010000700032050401180262048000107455078440f011158282c10498520000030749405900c01024010b241c0c042c42c1008508003021000141e07503c0c59111782c014042d5003044102e030440d0b041418880c10507401084940380d003c2d507031012000c1c0c0082800d10b041c05000c00b40e201e00c020000b0840444c804913650500c000c006141151113203803408a61030300181c02d002480c441d40c03000b9050906030781040c0b8000d01c409d4558004034640c02541c5030800c6032603400366215880382d800c05c4d030204103a01200c07580100d1501e02641155030b140010340d40c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 569634316 1250 569633066 569633069
    0x60c0f030c1c091b1e140111030d060302010e1c11060f0d1a030304030305160f12030507180e01030b0907030b09070303020115050d0f020f040f0f0509010c05070803070306 75
    0x403040e003080c00300740130300040c070b02c004002c80d440d10300b01c107686a00c07150500480440880821000111038400b048081c00c805040c5100060515003c0260521824207514682060b030440e0000c41d40e4000410440d81c00a402d96a01c48060320781d02e901500840d41c1c0c040d486510030000c0d200d9692840300070b1855a800044072071500c80051100d4840002c03840103802001a0718a5640c00c07880403000c002c841c034000042e242201d91590f40d0070b10702030704040f208a28a00040080b202002c0100075403000884000e01e2511141d202d075000205803821440c000c0c030200074090307110001e02140f08103115402c0300441c1181501d4001e4003109440d02c1701e01c08140741c0000340d400a4110f98584040c403a01c42ca001c00c1401c1103034003030f6000b444404c8140e504941300500360311440c0e9012900c01d101c0c200203102e00b40400102400180b20442050300b07000460283c4161104134003c85648441c4686400340501c50607410121480082001c025013020144c01881001000b8201d1840840020302c0a882038201c0c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 569635566 1250 569634316 569634367
    0x5060f131104140f060304050a0f05070f1503060614370f0e0303090906012115060201110f031b041206020904051e070309051e07030302060c0f030c 65
    0x140c0d540e507a404502960707070031200c90764441d1307040c2e145152040c5400025640100c0d00000680008200e81d591180c15812040381100c0c0d0f401241800500da1460a500c41700820354030310340f00d40c1d8441c000401421034480350007035020320813520010131040f0304040079034a80010b0030100d110010fa00300c80810701100220f0012200807a6080e0400c002940301c001000d4001543e10b8100d04551207004041d101d0080c401403030742181802001030410340c42400348160344111300c81d001e4491908d804030f84041c2e4808903d000c024905c891000c000540e42407081001c0c21001300c1401c2e041080c0c1c2d5000010038030014000c5003a00307410300200405130090000301d07001025002c0081041800030b103030140281d0840b01c4441d00c600e180000041d801042e03058502c8200482c42c400130059074079400c040c3d006182d13481040d25140b040c03a0310010051001c1d15202c24030301c901c2c0002c0c090286546002403034220002d0040058040a124090003081400282c0e90407000c860103c0e030f2114920203c0625001c0c4045841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 569636816 1250 569635566 569635601
    0x1110721020604080102040e182d0a03030c0f081b03090f030c0a1a0f010e09030c0f030301170d0c02060912030a110d0f0e04091e0c140405060f13 64
    0x134040e40550051040795054822411255200020170ba208440100902056041013880610400c41610140420baa220030801070b903c021100042c039140001c14200e012a5603100c0ca0242c040c4c00c50810103c0400d9481c2c103142a02e06a50810b903072294502d003c51b05408040040750503100140b21a05241c1c2e18942102d07190051a0042a61fa10481e1001c0e11441c50340201c9180c020b2440900700c4c4182600c000891240e480c11480c0c14a080c4000c0529545010501480500507800c1c048143e410940310021900c0754100201800b50103040b140c201d00541c0031940314510190400301a2b8092034040710501c0e2203a40c202d0120fa20140c0c00680c2c6a040d0000090012005401854103181e24144501700c541e18188602c00b41d500d855403204040c01710301265000003280c50035820031403805d40304002003100e05840043c050041c40351000225101c01481d041400240c0c041142c003100f5200071103050040f400c0110103d030b001079061759540d02031140381c004014020785a80088515242d03e0215 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 569638066 1250 569636816 569636819
    0x60e13020130050603070302100f0e060f030f180706050705060702030301152114100e070e04050c0c0a050a0b1311010c0327030302010615170405100c03020306010e01110721020604 79
    0x81010103074400ac000450300018402100f410048103480c414040d1541442c030b591942041013503500c3e001440b65224071444085180c0c03469041c0040c800804040c0c0381d15803600058688181880030003414401154001c1c00100308010010403102d249c000141050001640b00c0b03103480f00b1880c45a0480b11100e410f10780368268092010301c03614860f40c0c424241008407500e4402903020100e055603020005010f00a0340c8100346402d0b40402e81040f0585821481c2c03103604140d543c1444c81c040070a07111a00540b00c0e03402880142ca00c01c55014110200c20b16a0070131b039944000c5141c200c881e8450410030603030420401c05000780084903046807285409082040a12594100362040d0b010480055082c4640090088447d610311418905591141030700900a6030340256034040083c015205445518002c3c19141250710030074401c00d182e50390150343c0389040c0c40054080110a8810340c104841080c0e41da151180c041400c00039500002d00340001d2064802580e51420103290300a9401180002c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 569639316 1250 569638066 569638099
    0xb04090b0403110105070203250c082803081801020c0a05030918090d0302220914010e04050c010e0a030212010c020601050a1401050304020103060e13020130050603070302 75
    0xd00364440d80c46030365032185008080c1e940500380d80d02640d189000d40e109000710503411940800791941d803066030045400040c00d070303202d110301116543d0080d02e40c1d0300154115440344000310990350009007c40355848031a00c40d070350002c191701e90042c030803032a1314000c059410356170000703404845000d481903089640c08030b07490030071039100c1c1e00034002c03644a039101040d520ba0105004a040b442028514041d20a21050300003c1c0c1c0030350701680e145084e2141166120b6a01c1d0101200400680040d51000400d40399400c0429074490041c0c016000008071001000002040000c41040081085ca0002266442c1c0720100d86148000d40009500c0300c90100059107081c41540180804d00c41d560031141c441e41e80e5001c0c465000d82c140200c0d0540d01100070400380c00d50040c0011034000348180340008000350f950107030072224001540e0744049081001307004415507030f000411542c0c100e51a000c61103505440010311a01d001c42a8032a0001925500081c40503602030000400a6801070106154945580c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 569640566 1250 569639316 569639333
    0xf0b070201142a100920060f0307122714100c050c0d090e01030f03120c050c1b06070b0a020409020a020d090b0a0801030803090109050d0e0103050604090c0302060d0b0409 75
    0x1100416244245510b07211806010b015180d201500111303401c4403c00c6500d1003054503070083e1b880c290449000c00c9a5140c00d0100e10056204100540d545003c040301d42041805854047c1c0c0b40c00030180e21041903004000446141010843c0c0c8680d200c030000342c00041041c01d0100c9072581d410500e2504420b0f0406540000c028011007035103609441044447c40701c10384690080e400342c6203c510040d00141300003640503040c14100740c040d007410a4500c3c004881241503448100094001840c04202c212042d4000c02950a50140719035826031a003c0a5010030043d01038440040c0180750f600c00890700007011981102c0c054103030700340c0a541d10840900041d55548801402c04000b0f0902140061404011030a03a1840c5180b5501c101080c1d10f07644402c251500040d00804a039541c0c1d804160001d0001c1080c01d60410315500c43c5030a03d103526001508454000389400d00035400c000ea0100041c076200040d03000e503981150090307110300c1c4040a000c002c207018006e581c1c0040c94034030100d0034407001070b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 569641816 1250 569640566 569640637
    0x4150302100504090506041b0f0c020d0f06140f130303020909070921150b120d030608011401051309031206030605010f080d090608060d060f0203060301060f0b07020114 74
    0x202130501641e2030310300601c070807038000c442d005006403000b881e2110710380e00c207405502c01c102151905c023501c2d0030170343c000981c060004481241c04030b55400030001040010700407000c000341001080e807940d15240800c404a060020110108005425813060426000340d040da041c0784009000900c0c030b07145c2080060b2400c503040c014480601200c420b440f00d42080d0201c1c0280340daa102100c8540201c01c218400041d10712031071010b40c00754009290945441e401c000c19500d01929940101d000341c50039000508540340700120000843d081c4005016545400704003c00c2400322450019440304142421034000c0404680103400794101a070020500090780c00c611b068584965a29405640e640c0c00c480d070701c003904800c1c0000708184000410015000e131510543c40030014100e4132620150741e41e0310040314080c1496000703440d40802400000d08007441030002421458a0a49116081004d003040500400d60004d0401c000c407400da02c3d47c5040c02d0700340c9140010107803a074040088000c95181d44446c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 569643066 1250 569641816 569641829
    0x4090209010e030a2004020c01090320150610030b1002030421021e010207170106090501080d020709110d062409051e0409050f0f0f15010504150302100504 68
    0xb40c81c07480e06494003040002400798407041c0c0102c0c1da140c5440c41a45050b189882c198410360030b00c54040c68041c00e01420103118840e81e206000d210080361076841d05c0000c0c180320fa0351503200d820b401641440140038650030403802c80d025492105035510450107080c07110410350b0484007800e0043754994000024000781c601401802c1046151030005031149130001d4006944100c030003000c0c640144c0e0160001401d94418819107007030320748565015080705100000b12000780c0d55228100700d240a50301c58a40074040040280500010105d0700079541c0c8824001c0f040c20329a51007041004140c0e00044440c072198a64041c8140790380c880f044c1c507600750f015035821910321004e400481103d100301001c0c3d080c3c1d00c0c001c00503802c2000d00d40549050342d8040b5001c2e60081d589080b4a000f1510401c82410301c3c03000e00004025040340c03100c805082048400c071200c040d40c0b03c04070f414800c0030301d511543e05403070b030580e000250707040f03488078008404405500280d0081c2245c2d01c145c0b0510b074050000e2003903814 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 569644316 1250 569643066 569643077
    0x10903020d09060512070c320c0306010503031210122001030b031c0c08030c0a09060c0816020102100908090307050a051305071211030a1b020601030809150409020901 73
    0x141c814055813544140b83c2c000c40ea034001ca1000402d001d00403010220103d00500790140c4680300d9116140c0e07404400401254804401096440c000f03070100b0117000b2140c0140c004c1c128551501c00465900d0040c03400c19400005100000340d03001c06158000720007001c1e808245501207101e800c3c0344c0c2c84814a40b242904407415201c580c03240d9402402031b0a28058054000e046c040c2c180d502002d080c03007003049000b082000c2058200003151520740512b00461050900c58ac1e00c800b0741c0000707000d5510952002e01480120700d28000887c401ca070035a50315800f80700e40e040d94500b95100403420700841d500b0200702280b42034115014410301c1005054419801c0c0c0490350301c192190200b1108038028460954001208194910210501d8005a03088003481c10305251131407201070b140050301c030301d0f081504c0142c00100070444c00078524003403240501e04078650114280d404030340007910340005010150040c400064890017641f070710715100d005668560790060311691142d84100280d801044154000340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 569645566 1250 569644316 569644319
    0x606041d03030c0703111f020d060503120a090522021b1015060212030c0f04150e030d0903051c02030d0603050a02030606060a09062615090f1302040506030f010903020d09 75
    0x4900044244100034411400176161f200566200065400448074802564803181c00040645041120304ca055902500c81d90f1611481000104440b6003079225a129029180340d0350a9001c8074550b060f414000d5840140e81d036102c10703100704030a480c0c1142c041168400d1101d071000c40e045c0b0f540f11440f00c0b0b0802943d12202596841e0490760340902c1e00001c003030207400300003056407456524020300e03199031150011410a695241c00042c5010610025404a10313a20107001c1103180603c070b1507c42c010030b420585d00203420368a130340c0d5880043e004242d42c060711048194519a0080003079644100b40032000f44503291300c0f80b400c039403074801054040b4000d21821000c03420303601d00358090741c600340c04031340d92a01e403d4902481215000701c42d0521003032240d0a451401c1803404000c40f0380344a450a00c15507480508504140050480000c0a19400300c4184061160041c00290719211403901150085100e40303d00c80000e080150040044400e98038000580d41056004101c4c41c43d540c016803241c41009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 569646816 1250 569645566 569645597
    0x9040c021212130f030c0b010f0b0405040c0c230c03010e06060904080702040504120809071404090201050c16060822140a141b120606041d03030c0703 66
    0x1e0615900040700c8480a00c0030141c04810009038551182c1c02e0902007005a0141d10390000800000d42c1c250000b80034800540b040c01a00c0700f03a1401800f9404045030b2103890060b84200700c1c0541c2c00744178442e613103c141280c415885590402941c40d0402803e003908003003840e02291082444100303461034011108240c596103018031901d0043c003d0b035806003180340c2c1c541d410400d50502c000e004032442001404080701603121482214030541c420044000303465000388010b048514020000c400a0303000c140e0070300090381c1ca41c0002c0d80044096030081600c1c2d00c644010b0b40e59004000c5000202d10400030b5440e00020402c000d4022121503440e03040d81d544403025000901c03410a0400c204e00b42e10f060f411000207511030140204101d40b101900c45d0b50407156104a450071641c020303540c15500800c1c00580740302015541c80b011000444055181d401c80580a940b600341c000c08061185a03940c107110b0443c80e10034080012040e1241c15030341d4a14290142041c44d400c491815000503030240740c410705c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 569648066 1250 569646816 569646823
    0x6020f010e0303011d250201020414091306021c1521200409021905090105060c070b091c0b0411040608060a1d07080f060a1b05090609090c09040c02 65
    0x50340d040c48542281c0e641c02601c420401701016010340c0c068100d001c1b07494000603046454003102e6610b83d0001d660b42c0c0c9000181030081e801000300c1445012500c0c1408070b45000680e111010075404280940c40782c0340700e0000c02d41d040840f0745619401d42000140c80c00380144100c110296142d0580b048010600b00c52524001d00441c10010310218120514542d0b0301c186061040281c0c03001000450300c5c07c06540400d80c54100c84026200420b07405d0030500041c9440c8900c1400b400054525504112001c0c8586641c1c0515108011100c500054010325607182c94000220f2254043c00d000f00621051810044e41c40c4111802ea6081140d071040507498505030290008852100700104115129040110010b1100026003d848402d0210380c03081c440d000c0c000e0030300801d181005032000461f0b100301c460070400c006250001291400d0200d91940440d104030304980840c0341740c5240c1325407000700420850321500a0ac03079440407005081010542460b801020a4403098178203100c0f0485242050b41d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 569649316 1250 569648066 569648069
    0x712150806010e0a05040228090e0d0f020f1e07090608070906080313030b100e090109061a0117070203040b0301170c0904050d0c17040602060907061701170102120106020f010e030301 80
    0x1880061b441d9289211800c883c2a01030130303030f2303031000d29a80240e503840c2490881c0d6820301160b5490300a1803a05202c2d6400c0500e195001800740041c1c11080f507059113864491494410f180d0f58000300c8040d03844c0b43d26040000e0350141c240c81000700b00407602c1d62201d5a9070400c520968030305a08108010808036800300a0b81d000c0701c41e42c9003085040b0706559418400d010300070004814217209101c009092080200c080d07024107140300001071140d14509007030041d55060043c0c0c11810310910414661030342d00503094189600300902030119a1582c4c01c0c100c3c11403045900c00684404080004121842850b012800621018044844c19646003080c88062402120f000d055a040904000040c13805025990b0100344a918092174611701005400c0306504143c000c1e90060348000d04000014900700722603c068a0542062030038082042031a201c0075405024043c21004200c0d001011001c007501920001e403036016a201d850342e110308000356915400f000403070303403503003407074440328030040302008490 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 569650566 1250 569649316 569649319
    0x1031b03030807080a02091503091e030405010c231e010c0e0f04091407140618060d14191505061801020a0506040b15010302040605030712150806010e0a050402 70
    0x950383d4580d4291807503130b0014803035050b00707408100880141c1e0b650908110344901c41e4500c240c0320308005200c035180c600342510220242c0c0c808040c0305081342d000800d0340c085510910b04405094034074074201203020310948458a0b0341042e20155102c0c0280416106001804c203904910505101071031542a10041d0040c80042850004414480e00782991419030481001d04042001c100316542e2142480c46841081204d4200c090181300789101c21030810440c5404070340c200e04001d480402c50300070301c52620600f80320b00400030b100741074200680c105100b00e002400524440d4a84543c1817a641401d510106400d02d25101e54400b1503c0415401c200303407140903081a013000c0380400200030710402509503c0c1903101c1c080002000074800c02c101d81c130940c41034010224500b0b001c0501c000361055110468189801840244096907000003683d034014050300d0103409090001902d80b0041004074002010036540220100e803841e00096003904071640e0041d00000c07540ca00710708500301c1c3e00c00e90f40203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 569651816 1250 569650566 569650577
    0x80601080402120f070303020c120106032409020d05100f0612030c0f210f0e010c0305071506082a030606101701060f080a14010506070c0305031201031b0303 69
    0x1409410b003020351124040a0b003048503101c00341340e8145841c2014641c42100140d01078200c5904c1410070805100d84c8405c2400280000c900f150b0f1100300700340052804008400c00006164840d29081d04100d071020340203018641e01100d1030800e0754941542408103180e507410f0010b80d42c028a050320034030088404c44c0c410450703654050340c0d044607907461020095a42c943c5000500c030114803d000445024401e00d03070340f0360001041440140151038011240c2d001d101d51901400e000c0d90300080d217101e802d58145800381e918107052900025641641c0180b0f2900c6140c4100840e0a89001131104c4001d0410300181040c1c00510803841c14a6820052aa404bc0c2049010410701d060240b422564103100381483c0040a800300280404003c09030301103c00030b10a0801020101d80011100d82c1103c01120b0901c00001c80e00901c5803980d2061094900804001503000709106040407003501031070744002980da40d6012094807c40c524000e000c141c0c0c1a109a070291040c64000b8101c82003220342c1500e68 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 569653066 1250 569651816 569651821
    0xe0a030b070c0305070c081c05030c0909130b09010203010519050307050603060d0b09150a0b031e03090604031407050d12050306282402100c03110714060708060108 72
    0x1200e80b0402c1d00821400d0060034031802c03000600a910000190043c00000c001400c5050003140013022029400d106010301001130100d00b008002c1201e40c00d4a0a0b03508685684a9814900034401100d07805003d000c1c5000500c100d003081900118121001111517152000441606a01e014018412039901d41e111000c00c1080d0300b440c101441c0d000500607d19009c50710261103e84040c2401c440f500d03140e410040c1904441c1c0e40e009a120b40100d080f1804001c001034210210741e441542c455501c100803944241ca0079118000c004503605c1140281589031201d03030300e25004240190141140302e5600540d803010820341808007004040a4010030b50b80e5025500e085c06681d154005000b03a900200386100c0c01c48200084d6116000c46030740003203080182072800d490b54840f4158120f144401348407110080302026400512080c43d51400c40c40060384043c0c00c01c05400505180201c990501d0010410505101c0f070004013504510046060720b20320303030316035004a4041c94101c1303140b404114128007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 569654316 1250 569653066 569653081
    0x12240604050405060d020a06031b08160c0602220515030c040b22120213051045060b0304150218061c06080309151602130902010e0a030b 60
    0x1380c11072006030540d00b40030480d8000c02c030000b845400000220351950f0100900d4991401c0820401c0b4091402001c0c81c104940070440c0200078600130020844801c0441062144e1a41102c0307220440410200528040060504d055025440307242c0c840c0940c0e0111003130110865081701c2c41018800000e5241ca41845030414842c0c021001240032100344004510b07140e00301c044032002500000d01224a21640c0c1e1041043c6c240200c140400b409080405100c035480c02140b04200781e909100d1410b0490302e8401e00f000c11032892003900c0107405c8810741000c08421030784031821440d01c0c8580080c4a003a1300d810001c0ca4620050390003c16035a0340c0300e00c40840710b200c0c0c0e0182650072266015040351401d41000584160402010308a112116608665007c1d5442c0700f420000c0c40d4100285003070403800c20004030129012040c2d900e80d041d000500b5801c000d10310f41742c420300c60307070040c800426240c1c8400c22100401050380120b010070740803200c1c10001e04d4096246805c40b90b0000d520780083d0340d2403030f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 569655566 1250 569654316 569654321
    0x201030f320103170c0102131409100303020d030c020c1507030206160f05070201050903120c1006080a030507020a0e0705030f090f0c1905090a0b0405010b13060305060a0902122406040504 82
    0x442c59011b55400c0c0000c402112603180c200b40245916070040001d440d80700204121040041c0241c2c0c942d508803007042001907004a031440304a1000d04001447d01c440305800e9040195082c81070790b1181c400702c2c8800001500304050b100f030078069030803106542c0d943c104c241c450b00200c8681b040420209000c00718568411001071800c1441803401d0381c10030800c400440d150501103480a9210314010811402e030320b004000c810000c844007401441b8142c0303017407a001e0b15911306c20030240c1004400101f64055440d141c5004004010300403402c010b518007400c000f421138005848001d2035003c20004512641000620044c00d40000005005a0b55450080003084440f0400d0104038610a0900103481c0d50342c01c0a241c40703011140e4000c229945090200012144160031848031a05c0078030114110034400c3d0880410f030b944900f40080c2d2500d4603400035880d90030f80c0d03000282036800019a603646180c94200035004110f4840b2842d180311030748a43d90302c1100420149a005031090000f086540780a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 569656816 1250 569655566 569655577
    0x108070819140a0b0411040323010e030c100b010f02030d0509070b0706060306060605120c030714160c0501020d0c0803060f0303070c08070e060f0d0201030f32010317 73
    0x4040042d1200b404068004010001c4400d404103540d120211580e500b00341c081d440701c00700001c040d1458581140e1300d2000d0f05080111b01c0305491051001d1000400c401d622080341e031b0364020100c030340300d03071204044643d02c0e090001c062003114106864061903502400d444201a0b07010b80246041071104007042d00280801040910284a25840016414480390040080d0f40c002c4c1d8003c114203042d41060800e0300c142e9032060b41000b00030000810f1340400c91032a50741115039081001d035070f5100c4550445002240030582c44010307600040c0c61020043ca0140302421a02c50210201d07082d0b0b4503c0166110552017541e100490513040e07002c400180e01000440d4003500c000d001d80000507070711010030b2844e048201c0c2120350344041501400310000401040d0b005001c05001c800c11450b010300402c001607105200e983c000c050246100d03046a0003a0010440b850101a04220010094445c0d43c1003070661900362401061800140340788800c0c1220307590603207400602515582462407a0802942d101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 569658066 1250 569656816 569656861
    0x315040b0a0f0606050406081501020303040201050c03040b030709090b1005090442080c0604050909150a0b12031819080601060e120a0203121317100b01080708 70
    0x340d00c2c048100030001e2285202034006a9a00c40c0c50702d0034000040c2c0390725000381c0404801c4034491340500960780e00000310b9034032507828038000341c0710348403a81c00ca443c0d4041c6410001d184040801003142140d4030944140c110741c0440011300c408a0b05000744580b0850030307899180003c0040000c13801c00d041981212401d240855036a940d19901c0c95a110400303000701c810001c0d040d6949440700991050209504050300003103015001c24004400043c1aa200d94441c03a402800f265001940f411018400c1c030080d50f0481d5044240f500c0c000074004010020092498030401c89429500d11a0742c000081d681d030f07081d00340007120986010320100b11854600c509064550754000101240301c910600105008100f180c543c1c80ca48100c12040000d49026003081460a40c840c01880e405650000752030841003e804641c03584d03d07000203400f0b094a13030a90b041078003000380b01902d01e00c99040014091105040500d010072014040c4801152400c505642c503100054110001c075500e2000c02188130303400d000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 569659316 1250 569658066 569658071
    0x32803090b04030503062b05250303140405120c0306150a050d061805011415090a0b120a030e0a0603060305030a033206010216080d03050c120c07060b0315040b0a 71
    0x603c0e01902d480035404149440c1d413084041c031f0031010000101703c0301c8a4007440172a5000840e030540d9003a4002c029600c005800c000700741100b5212007880c0e008480c003404002e08003c81c41e089030066541e85a40e6119054020b20902c0c1c00030f0072a042c1a0888656030100400c40006136250a0402820003c0c03020280d614035610105030703040215002e801c3c142c00740b01c0d00011540400f440701465002c1401024001e10101d190f9800081750b845105561b40044c0d4400001010981000032030342c0c0c150071001c0032131940300704140c1c44e05254010808882c0d50f102240c882c07180548031582201941c000f880000c000340c0c028040c0143c1c071030090b04503040c1c45a15109050000b0b00c0c188405541c02d41007140002d46281d11010310050f544c1c180721540d19181c001210b58243d6180403603950382c0791003a44001d801c145e034074008102c410388a84201d82048858100b0b120484c1411542914075074030249d0200c4107245004501c507034034100820381507641c0e40b092801c441c0d542c0c5c0f2529031012071074000340099040359 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 569660566 1250 569659316 569659339
    0xa1101020409050f19020a1403090a050f0a1e02011b080706110304060c080c0a031508010e06010608150a0e06122b0806090411030a05032803090b0403050306 69
    0x500074402c00b0700c038a6400b0081c0c07800303091406241a1701080301c114000114010401c0340101500200303806400401007000030307581ea0341c00340c006080003102c203070080650040140c0440e01c1d150008401600c0360080150082c0e46108084142c80d00e01c0c410320007400714102e0300b01500400e05d0711480d8a01c081c0074040da10702c0d0000c25501e660866003001074078130a1070004403d00062090a200304000c00741c02c1d00b030801040c2007442d042062030041001410402d502c2344c250010940c414241200106403030b20091240800d40c0182503140c0300709004400c0005c1035400000c7c1d0094040b0310106054201405001e2042d08009800102140040c442d41c0c000d8a8011051003806d02000b044841c0c10b103460b0b80f10b001a4009104044244410742d180342044100d030140001030341c0700380307000b42c10550101c0e001d411b1001e41d0021a08002200c1030252035400f01181c0d84118400300800700e15000520101c2401603a001c050907011543c0020001d08100300010000340003901820041d601701d000200903030b0108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 569661816 1250 569660566 569660579
    0xf0105150111030d020c0318100905092d0f1614030a0b0d050a11150d090f02031e1911010e0a0f030303151a030c0a0e0a0e040210090602030a11010204 66
    0x2640140607220047e400058035140c070007502c1d40c85105850084034140c00302c004050001b0030303d40143c01040e214080e80030124071405070410140712403032416040c2c3e00d05050700644101180104890104c80b80c190000028541d10f00b180034001d1018032500c07501c08500d081d11600c9810307000101881d6413560380d8148140d2a0741c2e40c1071581b2410303104000400d400078843c5007080d194070003003c04a02500d05ca51440e20203000800580b002084082e000007a141400e051200c800209042c010b9010302a003408111041611250a828003403a40704481c5103903100ba1021504000d10400980f50383d807511428455580300318550402c02000400c40c1103c40d84801640c035035808168801c40101e9070b034501440003c843c80c603699004041040c2c2608070b2010fa541c0d107a0b040d12008140418040c00050841d59003805a020f210594074054041c08051791902e500d540c1c407041c159406d0b0b22910440356001010f0f4410b00d0310000b03460656010b14200742c0300e040b0955850010000b603200d107540070710011440c2d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 569663066 1250 569661816 569661821
    0x901120b180a05100503010c0903060e1011030907082404031808032203020f0112020c0304031a0604060609170106031a06010f083d0e090f0105150111030d 68
    0x100b90b0214001200d080c00b42d0310660720f40265103e20300030b034100f044007a00c403030b0018880303000c0300c0e081003021401f95808102c0da410800d0703c4008111807807400e03500002201b2000080c1d440f9401000417aa0066140c61703006035510390150511901207400000040695400341c00301e034106129082000c40c00e40f400c00740000311103454002039420391002c2030078058240e100c203009001140920b031101d02241540c02041c40c083c0c0302d5003207a05201c52240c5c0c8216417400d5070304507000c1d40d0b0b041e03042c0c0b034071350342c80b07142c50020040b5896200c00d10035030303183c0401c00070315080c4115000ca505030780329111401d15152101445050201010340c0b19507840900101245000c200e207011a0301280000d8443c2c034000e00003400f80d040801d60001003200400030064015084245240c0c1080d03040c030030100501c124030185072540c400c0401d06030155254000080e881005030070050041d140c0c3d030309a5001d583c410012a007201d10461710b03401c170003400071b105049039401413a4021265400c5426245001d621038040c01c103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 569664316 1250 569663066 569663071
    0xf0210050a02010606080108060a0e0a050106060203090a0e130b15060d24180231091b090e040f050a03080618240a080a081206060901120b18 62
    0x8103000044401226078280300d15000303001d02d418001280d50602d00010741c2c400340140340c8604d2990303e54502284071030030000b10440a034801e000344002078956030000d459400184003140241d6417650049203426031003d099104201d009603003450208261140d14036180d01901082d8084d205080d030010075110540208824000310001040c1a070207144529980d80c5a100e009212240b005402c0c8001150100d22001001c1780000c0580c0300d90307100710300d02d1074002900358a400031181c0d540103407a60103031901c6100886452440804c80030501035445900c0b00c4040e100d400002d4003c00d400d01c0082c1141800030742042c090440d000382540550340e0580361084242068010902100401c0841c2c9410400754450ba051907031403482c0343c10300d0b43d008142c1c10500035544210f480e03002038800064035400780b402c0c0105400400c4400322601d5081c44005940300d40f40a80780c2840c9240090006d082400c200c43c456403042e900d40b4001d06004214000a1110310b16080d071081c0c0d5401c0404403079040205190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 569665566 1250 569664316 569664349
    0x904031b080913090203060f0c1603020c01272c10170c0f010507030c1709191203080406060b0721090b2208030c010b090708150d0f02 59
    0x907502c44910741080001c664000d941401241000200700042c4c5000c01e0171a00081c00031000590f80c0c407401d0703c40141c2e000710814400d8411000090009240d40007a01e400099020f0700e80d140f000d01d502c0183c401100140d061390408134035541c0100000c0c909017030103440905160301e000a4074800b0f0f00207142054402d07540c0c2c17030300c82d40e10603018011400500c9104510501c0c190041c00448250000300c1c84e04004109200c0c140032000c180d40c1d051601a840050304c40354094800c0c0c01c44540d04100742d06603004141101e00455007900c14004003034545816100b035440c0c08003940d0981d807160ba0b044038440801001107440c141c031007500064204029001c2c26103d48035459030f42044a0f4032800c26508d03601000f41c0f81c10881c1180c03007009040110700c1107600141d402008100000d54124000a45900e030341d100325464480054021241c174019070208000c4d6001307c80030f05050b2a00c80c0110303103104054840c10b03050211400b100b20300345000080710f40100c1c82a009402103140540008040e0390f800c02046 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 569666816 1250 569665566 569665583
    0x4060f0b0c060f10090203040f02090a0c2303010b160506010b0406120207020a0902030c090909060f070206190b010c082d070312050907051003020a03050c0307020a020904031b 77
    0x520410707014841d86a20030000c2c0c030000c0a6160498109040301c00500c1000f0032036a00002143c18020782e0480783c1c1400da001b4124202900b070100c001d034018611100110b00061680b0000d00340b20b841841c0b20401103035851140c50071a400c001142d842a400400e600c6201607000ca916800103c042c03000034001c000003140241c84920b8200007030241084100d400020383d03c10440d070401039aa092510003980d49031706005880f076444220a203010b1040d0755600d68041488400c11003042c000042aa1080e48408000c280580725000c090703940341c4d804d454103401e07402d14000e2801c1700c0c00320394400c1e41c40100501d001003082801e601d691041d41d014894491003164110300780740600f0114071440b0050000741d5891485d110741070320001d007103800b0f001c000400750341c07141e0100e0b40a0f507080040300d020b058010a9920071520044020700290b00c0b6442c00c90201e410007000501c4480350f20252b0384140d100c0c0e009001390000a908100a0700e100078411020301441d6030000441c0452100703480903292068500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 569668066 1250 569666816 569666827
    0x304020f0d0b0106210606170406060515040302030c04090b16051b06061002072105010e12120f040c060f020f07060512010f03030c0f0c08010c1d0a05100e04060f0b 72
    0x185d8258503280300c0e000403440c1800703800c01900703038000b0003412048042001c0c00190b4543e881d1120180c40d00723510403980602615075880b00540e9580003407048078030072402c803a000800b540a000c240c2c0c5441030042c2a94540c0c200140010003c00c660051002c140d19040d0700e4802140016000714035110440b502a0340000100708036414600c10203503c1b15803600040c09103074584040c014540700c502d4101c3c000260740001034410400c2c2500b044a00c4c0081a059980780728a841041500b600401c1c034010100704c2003404038080c500e5151090b0b004130707000340032901c6075410040c09560011140d0a44421031098592290411100340403540c0500074554403650b484540c6500340e06401c8040c0c100f03c0010136080401c2001039004644500055440030a461300c0f0141828082481100765000703400d15420704099058a07540448071035a5007440035035410400f6802820b10017001c5581c000d05420816220140c02000d01501400b0b032034100041001c260740c0e407030701c810100c0900b40341d10000700500c2c0401c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 569669316 1250 569668066 569668097
    0x1050102210f090d050105010605070213090f29010f08010c030212073605181605131e08061b09011202040522200304020f0d0b0106 58
    0x11001890500741d5100010114010640c1d01803144070401540d40000054030f403c00d4450000440e003858100008100543c0c0d40c4401809030340c48060128461842108080c2c052443c0b072240c1402d041e00518801e54003081545c66074a60b82d101d00d003050044142005000c40380e00500845400390101c1c2580148030352400d02d1190941e24515643c00c00d060041c0140c1b54090000d44440e40d01610038a0401c845000210f800c41012405040047c400040c0801d205040032009003014200c40d4203460780c0114000081410303c060006881e5100902440103030810b6541c4180d002d0645a41040200f80040383d50307400c865841d1485060301c0b401c0004080c130401c08850140001c0c1d9001203080042c3c0c008218000810185209501241b410b01c0700c00026030060112a0b0b054402814018181c000c900e81110002814a07a1440310044014200303400410744030003466481c4412145041c503035085071a0345e800c100c141c00e00761240742d4015640342100008038107026103550082040c1c0c0c03100108484440c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 569670566 1250 569669316 569669323
    0xa0e01030507031a060304020a08070b07051c050d0504140a140c040b0a0303030207080f1602030c030d0c0f0618030f020115050a030b060102160603020a0305010e011202060d0207080403030801050102 87
    0x410820626103030030b0105940744110700e01c04e039101404649140c0e4a555510001d1100403d030b40250740144500c0b0000300f000744c00800104091401117085402074207140c041603190420b0030122031700140050041e0300e1910380c1c540085400500c20801c8050a8170980c04081c9443c00c1c8020941d0410500140800c46d03031010300222941c2c1c0b40c103680900c584182c040c041404d03400988030040c10194001804401d01c1070741d41c151a9201041c0041c03e03940e092814070602a9541603000307034428021a10707806010720300010240c5105d6110b131501001040384d51607203c8042d540740c0003a501c854403002420581e82e07801c420b152450703100c2d40303c0010b01c0e1280c038002030843c0c60a5554001810f075000091100c1d946610347d0b4400c83e5417219030b4060315651080102c1c201004186500d14102c01407802140d83d9070150040c04291030903980c100310580c3da032002040302e01c1080c45200d111195014142c0003504082c0001d04a0070001c00015281071001c3eaa540c170954403607402680000c40c42c0b4014031496a052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 569671816 1250 569670566 569670571
    0xd021e0d0c14040302060703050c100507050318011505130f2408070501021905012003010801140c1e0f0d020d050c030601020705120c0901080616020a08041a0706020a0e010305 77
    0x2c00d00c00b410503040d54045242481900000380a0100100b0320341070403002000b844c1c03108115068148000d082c900d20140c0f00360002c1c1c5890402500520007041021014403d81440c043c800c054035106a260030140400c104115005034035058a03812004038006043c0103803201c0703201d200c0303615804a184440000501c0e0b829002040d8542004508003c0c40c0e07400a080f001160804800ea115820755207881d17270040c00340b4a00d0540078150041000d090500d810f01a40c12a103100000340141a04c40c0b81000400b0003c40344040c200300144105140c950040c039100042c404004c0c544e6141001107100300306241c020581556003075400291040000c0005d014080c0c21245a040150850410100203501c885140c00351354000c0181c40400381d1000800c001c0442e1166002c1d200c0300b01e0756104c0404540b50741003100c903000c0c911010741c06154894030029421000540090720181018101240c4040c4010300d185154100f407402c0c4122004101544020b0131104559142c20610302444c900250030388400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 569673066 1250 569671816 569671847
    0x7030302210d0f0b1314100303050304080a21020d1401180b0310021303140703030203030406020c100e030307080f09030d091e0f15110d021e0d0c 64
    0x919200010604100d030640e0b490b400c100c00085460110015060014410510030560118600a4410352844250300040740c1c1840c50420000560311540c402000c1c080911005002400410000700071400c070034041d00c03c0291a207411202c88504c40340c0c10f10000898020003115617030001d55500c11080380d00c00c0c104035408056201480b985041c0502c5d500d1528960703405116901c41c002c8424941e03060104200d8104900411502c44101413180c01d1504c0507030000320344840c20382082a441d040001818000c0f2030303042d0300a620319a10340c0c0c1c440e03000c6d4000c003082c0d044038420304228404c0380701280114959000594015601da02d0b00c20001015000c0181001c0701080513003040c042110700100480b105500e0101c00415010380520307100180400881381c0d00c4860b85d07185005810002c203800c00038005400346c251040c82c0b0081950390012500d0b0002014200181080120303000383d40c6030003400d29240e000c42d43c64211481800c0412040e400031403e122480e596150384140940c0240d1140d640021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 569674316 1250 569673066 569673103
    0x3010603150b03060409030207030204050c1201050d230c06030a140f0c2205060432060901030c231e070f02010c08040b180906030303090a030503130b0907030302 71
    0xe03110182c000d510010704898096038680590a007494000c028100c003c59001d0006c2215241c003021242d056001200d50b103031000c24544c000103c61a00300c0042400f207400916104003581d150b43c440c04000342c0e21943e800c1fa405200e603501c8072b50740d4201c041c3d403040e81e9000c00441e03405082807072640128401400c03801d91003206810b110180c103261040e10480c00e24116170095048080851b64240f64180d80002d07445600040d0205000d940841000fa503081c00381461810004000401002c0984440101750819000d1094407a20361107500285900301407801c1c16401102140e83da0300080645145c001c404030700000c1c182c016915244a880d944001e0103c600b03003000e00c035640d04961903c903410003904000117100e59000380124201200e0081500c5104c0d1990703100c40701248026407a03d410b865114400d0000010814240032046074400d01c1500050a001c082d1960243d40b6504042d021150b903403540298075000030014840300e80200c80c280024020b052852500a250192072480c80186c0f21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 569675566 1250 569674316 569674319
    0x70305070617011d061302091e010215010614091518091f031b0f080706020705060c100e251404020f0d0906110706021b0309010f050c0c04060b0301060315 68
    0x78134225406800c840100c0d00500d1002e4501c2003880a40140d1007000d42c4012511190300000009041e096185c40d020307001c1e2510150351200031021000701344180c40c0403490982071500c0c400316107402051600f100600310002111201219040f13030704160b01791802c11069507448401031511110f480c4e44429405180200c2e048070030000d5500350b015200040010005c045007820344420660148041c0104051103a24266250702090381c4803214401c15025029122001c07600e818071a0403261401029002080103075015100380005040c0b66480314810302521404404003d0400160341c40402007403602080035091010601190f485140500c0c4110704c10000b60141551440c02e0f00d894604070f0340001000c09041c20303d02c02402c460a81d5076000c03140029400c0800035141c0c09000b001c081f0701fa45019100c03031844d60640d80e1059030402808194801280c07280a480356009002980e004030a03074048519180100f0203840c0a41c10050500b070010005000607681407080b8030048080c900d001c00d269 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 569676816 1250 569675566 569675609
    0x10306090c05030f0c0d02040e0610090b04050c07261b0c09090712050f010c030609051005061c020912030c120a140306011106090c01120608070e060307030507061701 73
    0x1045405e5105000d11610440714056549590001140e080480103407040391030800500c2003a1461340c001c180344580f408040743d1141c10b041c070401d1303c202514a2040d1400645464456144145420171002d00f15103024910381d4003030000250a911003d80d01c0c140c000150003180c41d0910207540003150141030f6040410095510001d80441220100d001c41140390081d414a60305200e0044000a07240d803d192003c050300364980e00500840700344c14070811082d11801c030355580d002924404e0341e138408400d0040d02c8070306140400100700c03c40c01502c01460602100040f0341c189005918440d882d0b0004540783c40070110500c00c0c001c10303409440c001454a1882c3c0406800d10700b940c0c8102f0351b841d001100180059002d00c2c0d225504251034801c0303943c1450000c2203555104420301c141400121511007401402d0f18034001c0c8416655044c019180c45420002c00314080c1e0782c024002c560501c61440c002002c2501400624003031b00965485810040c40e80380030410b0340e1010b0384107031070845942880c181b42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 569678066 1250 569676816 569676823
    0x300102180316150c080a180e06031518120702031203100e0a0b090907180c08130305040e0901050106030513052a041805070e0c160302030d0203010306090c05030f 71
    0x7075400034405112a004401002c6803041d1460100502604000620682c0780d50041040c0c803040c080b1150302c0c81f1054480d465541001c1c019039000390141c1c01926a0500c4c17030440c030009544032844042c1da401c0d00350040300140c0b6200e05403018070386059000840c4400e50809200d4140d14440a84986240d0305221413041100388180c4540b003282c2484501150320070350b50342c00c160f503140310040c0b6130040741c01d100040c2904c0c0c100d02d220701c0d45694a5582c102c14a00554054092400e40c2c580300d030080c0d6542d240300046c402c00141401c900b00001003001007203010150307a142c1e01a11500000181540c1401c0018040b04c20190561491f000a010301e00000f03280014070b00740c240385000f0500c415000381801c42400d22601004d0382e90050910310f41300c25103e030107540402c4003805641200c00c0a0754541a541c1108010740e0028016042002134801c0681c0451040b80c03d588240b04891031b000c001ca2882d000c1f43c000b0780040340c940c0e40b07031b01c1c866040c402e11444640140c40704030041c02031040c5441100350f9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 569679316 1250 569678066 569678069
    0x127081c1b030e09041a06100c0311100e07080123070c0c05040204090b090a0b031507050c010c0f020f010b010504090e0304030f050c010206070201060302010806300102180316 77
    0x403100c00100000300300342c460404400c0c03016001d41003200d02e04061800428803101b90880900540586001510615103440c036914144219104c00a2101e46500d00711200740b10402d81407043d1040010ba82d01d0b041191195045002c24000508181d90070032382c0241c2551803c800d081e452940f803000860411150710b00082c0c0100d41d604102440c0942482c2124005100303511140c0d02501c003280009480c50180c202d485036003401c81d80b10550382c0c0e83c007082c0f00444200d18141605a0b000041d03880d440119207201542110b03641c1050b83c1840a0442c94a080da0f4141054000092814601c1c40001c1d8040021220040c0c040c002400201000c0c40000c0c0103020780e20600b040151120910b282642003841180c02450304000300035445803581c1440c5d5031b1940c00c60340b0680144155000658480d20608c580340a880e41692903441a4441004110080480d60781a02100c03201c0c5041d44035601c4480907482c4d03807448000c0056183d841c07128415010001c4085240c3c001e0308090f55081900100446800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 569680566 1250 569679316 569679347
    0xf07020304090b01030f0903031a0a0e15030a0506040309140306311b030c0e0f0a0903091d0f0a0c140c0102040b030c030108010b0111060a0b0127081c 66
    0x10f583c0018030041307020308254210703042d0745840c0001d00300c01c1c160b242c2c00c41500805081c00001d07414500381d05108241130140305181c01304c04010049048180c2c001680380c044640141100d1912006440d4075040680c103460440100b440c9220400c0102a400c03c02c800e0040100d0181c0818031701400c444440c3e9510072040c0e04101c980b604030720350815035000c039090641e0b0402d0b1600400554184039000415840c003055400360030360740000420096031080240b0076009000c02e41560740340c80c1144d1000d003021440450920100000210b81d2401f4013069072000390001c8110070a90a000307c8800e000c0b40090000083c040c10803104004080d003100120005ca40c0c0c1080142e82c3d55035078841c1034020301450f00410070074000003080c0180c45034520003650503a601c540003000200c22002c01501c0400045803480c5c1d180c0c000b040010303104609a444040301344810705041d00948a284c1c844e81d108549103c0d10408140051003c0c00003d07410410440c0d00141d81031900183d22540d50082c0c141c12003400d205 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 569681816 1250 569680566 569680571
    0x303070609081b0304180b010f0309020409020603070201020a08090c030d0809032107020f0129040605060d0e0f0d02120705031303030c21080c07020a0b12040b0f0702030409 76
    0x620410061504452065407400c580c40f80520b0640c690355101e50140c0704d2104807035003e14a1355500d400600c035804000405031501c240780e03200d150307058024020506080e6805230f985c418400c01358541c03100561288200b5400181c0d00c251800004d02094006005200a40e00036490b0068a480004008100d03034003174101003605a07114460f25142d4880d03100c80d910f003040b166401c003158002d9403603a24081d04040c0c0070343e04508682800c40d802c90f2071400b01046504014014600c242c40081507404c0f013200d0180c804942e8503101c0010440c81e90003103164445039030703490b1304d04000400c0a0001c0030542c0d003110007a00600340403001c0255102c0900300200a2401c0020b1b0200400c0810811202069400c03110200303407503940e04028280d440502001c1d540202c010035000100c1c0100b030703180006990240c40746455038485001c60340140e000313070204a8010150603404580103e030349018101440141807aa00203240c6454041d03402c3c1009410450140211014801303150b4000c41610b0a803809031800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 569683066 1250 569681816 569681831
    0x9100c0e182a161a073f020a0206061c08090d030519020601050a0b13061b060c0f110606010207031b080a0807020a080f03030a051e090d03150303090909172b050603030706 75
    0x200085440d1160701b24001440040d01090ba160046000d03445607500300c5035056420503030112154141c81031200140181410080703c041d078a00f07a8038104c5600d009103031103818060303e104540e07980c10541c42030b074015030300c4400108409d10f07000a800c405003010300481030901d0080158295003803880d0161000b03000910400090b0200600d0040007110b80090301070094000031500a043d0029100b01c02c2c0008444110a034ae0441000402c0d03801004103034005d001c460b240d034988020310708c0c611210034464110000300003035031a020031072140410301900e03d840e40c80b04103104002c00107100b0f070701a1280d5041400c412400020200680c3c0e404042c500d0081200c1c0d0307450300e0003802c000d29049141e082100b914148144a800050000c0340c0f2222a14108403150a05801c085100305610004001501e1401c0c24003030b503600b9412007460b2521070f42d0004100c1000d044840d005802480c0714a1107940c0c0032440402540741848003034030750400c43d80b01300a1410b003e80400d8891080b120003a2010b900c0300c61 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 569684316 1250 569683066 569683157
    0xa0306021b1203090105161d030102193c08040f060c0201150e060a09020d022503030b1c0b09100c0e182a161a07 50
    0x44100710012000351000c0c120751201d50011a0815504000c0961034040060070341005040d8181c502142d940340c506003800c01c000b5100300e80b401143c646801d95000e0051201450001220302c90b007031003a40b00c0b02010342014404c042503001e21003408000c80002e10320440b04180502c100c0c401240180303020140c598450800384c22540004000400803031811484900c019811752110303201c1e80645003648811a030718030384800100c800759401d55020700c024800301300304641d03540100504102400094100b101040700444160b0400301260302c903d00c86201d0b241019414442d070b03040359a04a0380d00e24071040b540c078244410740b85041c00414031070803180401d80e0980c0810034920104500345050250007000c9100401d001e100f0305109001d0094a04000d040308040c044032403180450300808803c610079a0322000203d10103450381c1c140c401c010056814116841c11100000a0082141c01241cbc206a00d88140404004068078100715a81e00405040c400001c8500d10002d003c450b0420b41050041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 569685566 1250 569684316 569684347
    0x1a010807020f1f0f050606090105131211090c0c07140607060c031a0913020906010c120302130b18090601030f05010f0503150c04031209080d1d030a020a030602 70
    0x140c01d00c8841c03066000c82601840040c04a80041d80d03c0182485640711401c5482c040c0d46041d102d0700e41c01001400381c0351080d440b54000d170000004d4101d1208800355a08004010340700711910641b8050013001040032242040717842c6980001c00120035520342440540e80b580c84d20b9080c0141800d00d419526462002d5580c50160b40581e5041401004020717100380000e0010003c074007143e10440c0041c044140c20b858403491107403060012100c010007000540e420011400740041550741070001c640000b201081c80c0034088080300d0f0f40c68a0060341d44a40b6807a840f540d504940c800002c00b6410004070401c034150680c40300d070300c61055401c0d030b603161036920050f4042c091640314103540e50314210000807440012001001140c0c029011350f000c4c8031407484a1101400c0403240c01061601c02c20003000050360000c10070007001614036105414907140c10f801803c206c0c00d0100c1c40d00180c2c5000d2206541c1c12044840305440004800400049405601055441c42540f001505244c1c5c04548000d1081050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 569686816 1250 569685566 569685583
    0x3053313020d0c02071a03011a04030f060903080f01060f08040302010f020c0a02040605330904051f080606010c110409290109110405210706020c12011a01080702 71
    0x450203540b00d03048118503070300410000c248200140b080c0300c00001d00034208201c400c0c88500388142c481c61603003400d0550b88402d80480c00030540d020200000000f0070949603031810000d200340030110b840d03a00d40c00c0c024241c0c80080d060700201140c0c140108451908450302d4607071103101c0d041821040d951410103900500c61144401101800001d0b9500390305400310302c0140d5240b0031101040329540340c0701444049010540d034180ca0001180d00c2e55205070307030000400c0480303004519640c40c000c40500484c0070755005840d1150090f01280e032003885204e00211240140c040c5000070012850614002030021030310002c0544110781c0c115010b80c03980ca03240c110002e12900444604c080381c500108800a4143d150b0101c2040c150000002c6003400c030074000d4402044a0403801030500f030078501001080c2c2c100100503212016403171440d00b4a10018042c90008110300e8020344106580807043c02104d038001d100040c1c0691400e41180c02450740d10200384071045003032034084502e80e981103041e840c29400703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 569688066 1250 569686816 569686849
    0x60c070b0a0905061512010b060702060d091b031e150b0307080303010605071b060e1309060e010f0b06190c02120709060510020a0308010905070c06140106030533 71
    0x13001c08204044450b01041da48008080c5c903400c8454000c03881c0c0e603007203a210034152540706c8001c2100c60054034104002c0c01c9440302100c00020b809101d80e0764003140408210b0210402011502d003001803220300349800c9641034180c0e4030500918140da4071101e980c48403805c102c86080d66100e4082580e02c0421000c0041d11259080300c3c1d4030b5031a000c019040e5042a6001c40711a100000800c0c4021120002c0e00101c1e41103441e00c0c0700741d1402c40100051504034800302c40549603595842004281c01d405840015006980000383c24102c082c041d5095400c070810650040204002030f0300030344d4031140303061140141071038400c1d040c000c00c1c40040c0306420241111405031050490125002480d0707804070046520450b2440e582e45100345090b40c40c1c0d0128100603021036075580040182d00e1581c1c1001c1d500214501d4a001030042c00d680305070803140000c61a009010144006100c41509403113840d03000040405001d11710034072142400c0e03181101d40440344403c2d84089a03440107817140140c01449015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 569689316 1250 569688066 569688073
    0x70209010e22050709050403030b0301021b0c180606090103060506070b0f160c2301140114010e1f0201110d0b030c0a14010809030403050109050a0311060c070b0a0905 73
    0x1d4407803000305503040039a80b105100308840c0620000074103000c030404505038000c0c0074000c0705141880b00801064014010350502d074940c0c00796960b41e5000e100400d415425001c9000000444400003840c195030059090300035146515100300100700c422505a000b6012540030b0364404a4500403005000e1540c41590002404540c0004010f07403510420b1045416400c01e00742c0c1d0780c41c10100301c00e01441c0c6802c1c0010520010307014010030b00d10122007000e41c0e800880940c164802050721800c5900c40c10703032103000c9130312440103200d1042d00c5081d00b42003107030910303240a452036590006803900f010a03501680c400c50034610860350358000c0d0498001c24140150382a11070154040210240c4050380a1510a01803010528040e1504e0b482450690b1840084543c80790000e10041d00c400f0809007007540e86100a0000100040d0240540003140744580d0103000d00c503443d0b01e00907110402418402000d50891007c00ca603a841c20820b41d12403d40241041d1703800c0d101c904008004240d0504003418031700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 569690566 1250 569689316 569689319
    0x7020a0809120717150f070c020d1b170d020d0513030f0809010e01030522050c10020c0a060906080601200a2108040b06220e0610060302070506061507020901 69
    0x4200d114011300401201c00c1d40c00600e40fa58455500000890b8480402c07402d55001c2004288030340d0110010500c0a00500f50042c040e44845e1010300c8540d1481d052350400e0380e0705001c080b19004d501d01203401008000d0000210070900a500c079160102d111040081c00f00d40c80190101d9000601c00039500500c0740008151a0f0a08800700e41c4400c0c41c813030102d640b12850821551082c81190b1142c0d85d03107103a1840420070341c130700c51110070314241c415101c1e80f1135109100c030381d0358a2040c60309400c03180360000d06000004000348960029030354407030014001d055a0403c034046d0401c0f200c50f03112100340780c484d80703500c4c00116800b00e800350010504500c0c420b580b54001004900070b101411480110405c0c010100c0103c021604100c080354010b00c0400507101181c042d0a0000c080803445a443c0741c019801c0c81c420400804070b400900c0d1502050340032006004110a641000c0c3d00903020724501540741003c1d503190f56a940002410103405422005003080300c80140d00156410154000d003058840e5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 569691816 1250 569690566 569690579
    0xb0906300705040b18011503060b180306010b070506010306020306130903111207020f040917030a06150801030506070c020f150304020a0506030105010c03030b0402090423010e07020a08091207 84
    0x1109507009081c0140d14089804940d440c0c04004005101e02c0741c20440c0151f0b080049000d02400c600d07200c68180740d1510004103003920b0181c0039141800715003410030450745070340c810940340c042d040e4801c085c070742801c200910219001156690540f0b810250160b965220000451207030102c01c0401e50b18640b602e0022010164085407101420300783c80300321948103012030011030041c400c03580d000f58480e03034000c2d42c414a82095007080b44480d002e00c40340d2080420402c10000315134000c44100b42031130b43c3c0700d105204901c065480201481418503000b616503065075241a03940718043c2c0300714288141c12000908543d642018003009600183c061074442c0e60b584c4800c1065041510101d21074420700e100451541040707820b50f4100c90050b580c0711005051518203400030b1015104e103036040754003000b10034000d07180d42c05054400c0d643c424960450001c0f582c03083c58568010307005041c0d090f80100030301007900e5000402c0d0080c1a042a6025520b450750400a0380741440c410070403840f17004450002490 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 569693066 1250 569691816 569691823
    0x70c050a0209010815160c1e06050924070f08180d0e0a050d02060f030c0f13140307050f0f030f0609070f060e100309110306040605090f010b090630 65
    0x4146a0340c402c0f50140c90340011080d01c01d0442801303400107200e4901f9000498030010000340c41d05140c0b4820303c40090142c849005555040364503800982c000c6041c01c2402c546c10301d01c000c0300c41004805141e80e0030881d4004003903220303035242c50042200480104d20200500c007211502d01c0c490300b0403580304000c03004024004541c5412060303c680b00c0c1d040c001415007424501d0b158500c5e4010308180c9402501140841540c00c0079000a01c0030b82c00340100d80c4802c9540006201880003a034000e01c51500d4020b02c001081c0e070700324103903000c0d0700000381c01c208030384403036042c0f003403400f4200d5810300c0310b264501c007003480c0c029400303c054014850201803090041d40070450f10181c1c2d4813400320840c032039207940f4191046903c200a4540190185011800b035034429800343e030b8018842c81c1e0341032070b2661303100000b490400300340c07016038403599140301f482003001040003c040d07411543d50091207001c6520001801c000c80c01480305000d03c4140c00043c0e40e014500c0d64200000704200c01e10342406c525020450768 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 569694316 1250 569693066 569693083
    0x50c0a060b030d02070b04170a050712020405061e040e031312020109060f0f030203060a0b030a0b010e03010b06041503090c08070e07082503180305030604061d070c050a02090108 78
    0x64010600d41c0d00d40340344017051803000d0b100c088604074a01880d00c03428180c1440e040d0f000942d24012940d0b00d400250b414080d20f00100b00f0808110f00c1806640104000c82c0d00c00ba100d20f10400c00c00b50a039102002c182186a5620700407280007c101004007060390031485042c3d40d01c0b0f12980c000b080480da12072401c19810445000381da1704202d0b82e440b40c03016100032009002041c00701d9105c28080c0d620364400e0300215403146001d00030707080492703032025181d500e034000760381c3c524007582c603400c2045007564003044c0420f11520440081c05405042d80100c1c0c0d5a201c1e81c000c0807060380490262940d0075001350819601207622004500d422035603401c40c2915554980515140c0a55210200300200d03c1038403c5c42c010072150355401d09403003045e007888242c04401e4159505158552000101030b460300c900d0841c00300e0203034440c9a942d10308002007000312409508074000c0d042c0e80c040d80c0c0300800400d0807281c0e401115420722141e109664240702d441c114214800944c44041140040740f1240003003207054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 569695566 1250 569694316 569694319
    0x120a05070201020705060406050c0d0207050f010e012f0c0d2a0c1710020a0f0306080303040c05240a0e1c240f020403060e100605090c0307050c0a060b 66
    0x105680358984100c0c240d125844e80030b805940440d0108012460380d030700c41500140c440302d030035281c000f403144480240d8010340d00c00c1e1895003040d0341588642c8028080d400a9104180003080344284c400040d0660900d041007401d88042c28074004615075000c2d0040312450160b00044508504004600818501825440227955030b000c9042c404031140c038190100c0002e6100041d81c407014181400e03a88030918034901010284242c01d0b80814660b02440207140e440b805607142d407102c1d0b100000c043c080e40c0c02c0744e10180381540100708010118811a4043d4140d513001c03100da84a03c50382011000aa14809550000807800003c0c20030200750442c107030304201c0e24103803011050300d28450001100450a0240508102496a55005640801444040e2400300040c3c0040c04555074044041260803d800803200656141c0c1c04042014081003040c0420f1811102440b1180c1018081042503602074644542d180b004400300301903030b0084041d00e403102044d0049800e00c081a04000001d4000c103100745 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 569696816 1250 569695566 569695571
    0x44090102070e0112150902130e0d0203030903120c04180501090e0c09160512010b03090f07080a030e06040302060313020a05011b110307050306160909060302010c0f17120a 75
    0x2803000b1005401d40c100d455101000d03151000b1a02d41c0d41d050300510a07500c0e0304079582c000d050010707035407122199900318050300c000419254400c042441c0000101c40e80b015940b0600800c00340d407000000700e45208007440d400e01c00030703210400200104c0c0690341020503134502c8440c0c281b401070300540c0220704a4280020030b104185188140395201c048142200e904400d0b2800014141840130320910316028071342c50850b01e480c51001044207010020b070003040d40c4c1403000003485034402d4104a40c1d0ba0740101500038004030303031400c1c10481d038602e00070074020140402090000380c01e9803494180c3d4025134000d081c0c01e54034904541d940620526109049220b00980c25000c140c652260210340e41c03244035000322012030101911000c002e80481c1c45811340c140318058011400d82c4051150354003803007a07600301000451030a4805130840701d10303812201a8510b06002000540c0c2d10210080f5100d800c284802480d102e2410700d148540d510518800300d084c000240250b11007624288140f1030916600b04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 569698066 1250 569696816 569696819
    0xf050109020406050306220221060a060c302003030601020309040b030a300e0108010611011103090c0306101a0f04051801050405060d4409010207 64
    0x44500702d000d103005600010700d09000041060402c681c1c2c000d900364242c2c0c0403002ea4041402680141e9005010848840311540e61158070185203809064001c5070480780400703110b090481c01441400c80500117400b88007074040c0b1034580686d10701c261002000c51280282c02c0482500054007292a01c059a500c5165100e003040302c0c072038044142c1b405810140d014500d0800741c0c2c1c0400c0060090302c2003281c1d160044072141c400080782901040c03600e0079840880907900d04080c1981c020550a1120001071260f00c907065080740c1e9221120074152442402e000502d8800104042e0051031031110400c1190800001d01107601400110f51a1103e002ca04603040c0341d0b00d981609443d02c404d031140f010b0501c464401da5030302d00562809071001c006400161800c01d65900001030103408100c5884602010360b40c01440142014011280d005105860320041480195030302614819071120400d41040ea8166513200070119601100450b5213184405051903065032024407150b0100400a01510072000d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 569699316 1250 569698066 569698079
    0xc1509041b0f08190b03010b0301021201061202090d060504080702031e0f0712030323040308040b07022103070e130c030c0207140915130603030e0303131401210f0501 73
    0x241c1441348036482006200c0ca005500c1d05000b4040640d40c05625540300c1d00c1c40b12058400344094010390000d0711b407030581945031280c054851f803c0640744c1403d0600401403d50140c0322451043d55032640100d0001b081d90300c40c2411900342c048c0c240c000398580100100811894070b0720050620282050302516604c801d080e030a281c1d00c08080c424004600008407980011a00950185801001c5116030380028180c00050f220442800c0307904401140c945400e10007800a007080306a8051f406000400e4061503946880f12503041d105528000704030f00100080c05544203500304048485c1c00740200302e00442600c101c101410110034008002840e1580c0d20900f1403000410004503040c00c1045c28244101d0000d00c800c03501c000341016a00a04d08403110019100c0c44244a8602050307000007440134110301d2300070410501102c80b184a50300a010000040412080303c10488080240c003894402e0880300689032401081c01403c1c12000d0480c4040d5014216001802c007100100802c1000e80c3c0c0301d03032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 569700566 1250 569699316 569699327
    0x1203030e0610050a0e090102131502120702010c23030c0307061404020a090f0b0d12030f050c0d050405070302060318010506010906050a0503090708070b18120c1509041b0f 75
    0x219a5900c425084800c102c600b0503440c40a03003046d80b5000152501c0c1400801d03080460141e88442d007076541050308400300c1503050040c1c40068050701013051070901c49400090100342005070251881c82d4800c0a54020611580144a62000c07402903075101d10080c1c00311503d94000703c5050b1281408c0510800003e108040000d1007503034020041c016a606004a060080c0b5204801c00d000d41d5580b50030840740c5e910000e4040c031141c031803000313160040441c0ea00201940c2404041c00300c0c040c04d01e000c3c005250036402c1aa404070108100005040d602c0c0d00340545041c11550029402107000811b0102076103140812296221940d0000c3c04103480d05d0004440d00300d0302d84110b0001030018010b04030b032544507034000c40e00050300e0021248001c1d104c000c580d040881581c800d1491181c001a000703021105004c042d140d500b4110313041d5250007100061692200407100380c080c401d280020005030091002800d441c1e405001800400030824003c44400c06841154004000329086d000742042007403041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 569701816 1250 569700566 569700569
    0x608011409040b040f0f0804171b041e0204030303150e25020c18090d020c030a0605060303071502090a05040c0e1c06050c03010510021203011e1203030e0610 69
    0x5081c04030569129180e0201e01d0070094000c40d88450180c1c10000850000640401600d0007170305050350b10f0b480d03c13207140350050003030004100903088204603108140100d01c0c40031480506450220b19030010720340c0c03144007001d04000404814400f0402005060b4107600010806403040c090304800b9031101a10031403907000302c41e01400414414016400f80340901c1c584840340c038140c0101c0b11220000400200d01c9410300101c070398240004010040c10f03a1003003002c0c92042c1094009010410604804251141420840941711903101c1c40402c101d0388082084030380540d003152205100400300080c0b480654401426248039003412000410340f45810303c140042e9050585a6201c0b8035035410910041d02103c119010b804181462040003158050281d2440b07180c58004059407036042c0010000b00410b180381c207504540c408900101c5409424007164152840d103850329441c190031080390076071802160032052020a040116000700754058000070240761084083d251240c1c1e0700d4081c5010178155 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 569703066 1250 569701816 569701819
    0x1022703150109110d02360a1502031606090203060601050906071203020c0f0a170903150603011815050114031002071a24040507050d0c0908010f0606080114 69
    0xd400100f240403402d81c40103d08020b10f460341414098113600c1c0703108a80000700c41841c20b0f545d20311001c00504050320207107034100c0e1611a0340140d02c00d96012448030700a5016480c0c1018140c100625413034001c20540c0c241101445021044a54914003107001d004c070f40e0000c9002e48205000710702c0640c010380c2910604900941542d040c1216070f1240c00d001c103040440c0c801450381c00c01c011401450240301e000395880840c0b0041086540b40d142c03c08580f06040043c144810301804442aa1380c0c0c00704840c0b030080c8150010400e41e48528000030300400da40307801d00d81403035046086282000545852800201c030800410011a0303614544170380790007581c81c00f0690581100b91802e494098a42c042c200c0c2074000e1000d8034032010100182c040915040d1a1404020240618601031080628040e10094010740b01800b03181400301e005081030054450514400c0d442c1c0c07a07000040d42c8540c0400008102e044007d000201d40f8502d0380000302054002c2c0000100803400200340d5602102018240140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 569704316 1250 569703066 569703103
    0x10f030510060e15010306080123010b030609070f020c0d06050a14070e010f12090f120507050325061103090d3213081e0a03020604121101022703 64
    0x3120a03031507003900c0071340d0341c03160501d47d94003000305124000740300e03e4207803412842c198401009055241500b08030143c0c0048180301003082040840d13225002103a80040d0b050515801d4102e00c48400d0382000350403140e0b01d030025100b84450080c0602034120f6030060000c644c1c1001501303200d01c04d01d14005400c4900364041003009c80d404400b075101c1c40c4240042081481d110707004a0080122400b50b80e8000c0b0f05654105c042c2600c401445591300501c80202d801d4203240c0d140c248640e4540d80c0702c0c000d4088184107450b1402c0f441c282d68154002c030201003544a00d08000b90b001640c455442c0c0c0d002903e80800501c039001d640d1103910f009001d50400d417000460010b254070360b003955400c50101c803030740d03241250b000600c039285015110010700400780c000c403c0a00708540c100001202c1c81084c0441e29401944258144800f0036004250150065007040c41803501d20031045d801e40300f02ca49803000206a40c0300007440e2a200041d0724200407140c1c0007622040403a1410010035a0fa94a008419450401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 569705566 1250 569704316 569704321
    0x40c090303140c0f030702090c13091a090403020708011a060d05070c050d0f0e0d080306011d0a060c110907051204020409060c0201050f0117030a03050a0212010f030510060e 76
    0xd00400142c0c02c0000010040c5190207100841d81d8202440a0140c400ca6440480e4540840c40c1070103009a00103030001000781402c440410700044a1514843c0210060b614070a100e03c8444020349071440c000b0141c500f18050802c0e140096540c4150b12500615501e001b141c40c43c08807010401d80382412004141d1800d0651b0140d4241c01008060000d03002d003c85140f0120000e05d00303214001820090742c8030201a0052090060180540003007010312416040001c000000c13080005c0d01d4111600303180c8683c0404c2458800f0020707042200c201a400610301c880060300c10f078064105c086542c803901c40d003062019034a0a0081c541010b0341d400001c107034180f2508844010a140c2c45074041d0004102040d000d203581c55000072035580d03d06010050b5142d0f0100420b920302055600d005028080c030401061485a526603120b004103c403140800d40c072880424217960007a015903a4134a038101c8808030b00d5941c5d88407040070301c00b18030044895025100d10b518032841d15210740c0701110b0040d071441c86d4030b5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 569706816 1250 569705566 569705573
    0x311031605060d0f060e040b010303120c090603020d0609020408071809110d15050a0b040c0c02060a0507030e12010912020316030e04090b1609080c10051e0d0911040c0903 75
    0x18018924145021945e07641c00140d050180325240740240d020701c005100039415410014040c1009844081c0f01780d0500d0b182c0c2500c25481010101120b00b60b140058030303840700b0f400600c040c00d480e501c8203e10900106020551031004202e00c8112450454460f1601100644000a0f240301c0200500845026951405681880080d40c803040e40304144008003042c00e80c40f50012110161078200c203255a0b4403002d1514141445019000c03421414034004a855590001d01c1c07910808038039604210000c2034650405008081a1340380a20003001000e821031480100c0e402002802d006a03401198a00c2c14480540003000310354a81714861410703500300c499505c0c20380e10907040349403154106a440014802044041c01458040c854a020a080b40620b00c40000e201c40603642001c0d2003504a420601102c1e5200c004440c4202d1103401c215403243c4046100000c05000c0d420f5188142800207100c0a0710700351544549980ca1290502048400440007440121601282111302041d158542030011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 569708066 1250 569706816 569706821
    0x60910090801020c0c0f0f0d140a14010e15040807030305040f0b090f070b1206210a0615150804020d060605280e0f0106031104050a0311031605060d 65
    0x9514040c20040c190658444229089030700ca07102000c103a4000104440e118500400d00d03e402d03039012a412400845500000340070542110700c003d00e4402140d48801c000101030182d4004107800156081d840c0904002d01030217411010404c50250207031094600e481100e00103100d0141350421461802e000c015903041e07004000150060b80e4001d06074211707030001144143e503076100b0202d8001409148070f001c88254500746864000c02403500050041f0004c151a0481040d0f0200b402c6a548a00401e4107030380d00c640d0b080c881c189150343c0c060b1003050b0080c40201c0d0070442070b00d02000100b403c51a99142e609803051410328035040019107060105004d46042c52140b80024010300c0c0001d26241c3d0380000500c101c000f54100b80f98401c0380c3c003e0038a40003a00f0483d000030212100703015110300d072401072030b01c8031481400b030601403590320340d03120b118208850240d030098480548056440780e00d0381001010340001c0340302503100c1d2256140300c091181d1120b050f40304590700a07051906000504494801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 569709316 1250 569708066 569708089
    0x110703030305041716020406090203090a02041e060605040e070c12030f141302091f18090c120212121e07021f021b011715040507030f0612020609 64
    0x9040b081140e031884a021000004c2028034004c2d1421700d41080c0c00e105100954510740d00100c03403d0f00c14020000e0202c0d01194042506604980016503540c8050540118402524001c2541440c00101042e03654200c0300400030b40c2d4408214407440d40d42c400e4211078503000041c0042c4050940d140080c41b1038000c1d040321840110341c1c2c0c001b00340545040c000c0c9410000c00c40310490040c0d0341c42030113810f5040c103007030458100140c08406c060300350b4403058054030400307140720350404d088909625010f076200d903034400070b509680200c03502c04044c4d032641c00c0c2400001d001d0b0103030320568503000f650b0384040d00010102c01610b05042020305000c0c000c4101c80307100c0720304058070300174503001c22800740140c0d114904900c604a070220700b841d01085051000340341c40d0042e11445500d08008054400e640e0700305515800800b10b081c51038030b445d5503d44141000c55010210150420b04000c18450566096084842c1d10401144104043c0b603417109030712000e2400101c040d4011000300711708042810000c01040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 569710566 1250 569709316 569709323
    0x4120f050d090b060112050103080702060702061c0912052a0f19060b0a061e0302041d16020102180d05010e030a03060e010e0c030703090203011d0a1211070303030504 73
    0x2810036101081d40e009452000d40100c6510601d401004400c0da040042d840e480c0f0540d81d000c00548d0b04643d03030b405403480742d200040d101e007902090220441da80e010031039400451070a048504c0700001c0308044094a180c40c01242c2c4172881c0c040164440d80700d4020f032418224209240043e048200c00c0c039902c1903100c0340e0703602400e00400700120f24506040040c0c1100586c00940700c070a903c03031410308008403001181024420040710404210455009106c42e00c00b000c50740000c490b0040d1410160020711880d40082c000002c16040203181000e46983e2510440082030105032014013803030308a081f07200d1f11411881ea40880c610209580c105980312240c260b01c80c0c8000140182d22000041c61500208000750000c0d0b180d82c01030040004400360350340100700303901c13500c4d8480c2411502d00a039070000601101c20182d40b41413907025907809400920b02c03a0504100d80e5005410003415540712404044262229400c0044d14058903204611010304c4500031030140c14003600719031341103010701405041a0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 569711816 1250 569710566 569710577
    0x3050129010c0510110c0105130c090b012604030e01030b281706192702042022050a06230f090f0405010b2b0e010501170604120f 57
    0x704c400c03004501c2040a202e8071048181d4503400c650004500b503900c01000180c2c5040b581e10b52900103800140041c095548844000c07505c540f54000413a0132940b07085100494003480790891165a40c0c0f103501c00e004a010780c1e521076a9681d0600150151030200c06c180707400250300b198040c5003020381c40c0d6061104c010192160002c1ea510740310300080d00c4a00d6880f00300c1ea04110f041c0711503d0f040d25400011810100802d00005074849900245003680728801c07080341c0305049030042150303101d5003c1455580040c0b400c0812450b107100040b0035030045076041c0e14084e2020851998070030890f1400086480c01001c4184040c01c00030700700d403072008242c201d022000190441d402007e8000d07028080c03010401205035210b051f01d50070000980c1c1030a4800e802140781c100144402c6124038203e640e01002106142124413001d500503001c444c0741c801811086283c0512011040d1064014030304941000400d1411003500864403621003005071030090034001e074840310070862401000340c0301440540d400c0c503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 569713066 1250 569711816 569711833
    0x30e0304090911060d05070917030306040207020105210618160c0812010602060f1609060e030f07030605060906220c030905030a080403110304030302070e04020a18050103050129010c05 81
    0x41215038012017213440185442d601000742c080e501ca002e40d001409a001000c8410f10480702941d01da100c06040940900c1c0c001400006690203841159502c1902000900e0f68030400443c0100c004400d07502c2a00c62071030034184014054081c4240f0b070160395524146140c1d0005030505465044540758103e650000a20202e654203035140d0126000b401070350050001031509294040079984000e11404450216090012041d680200c001058515a04000c0c40020b40200040d16003040c250180b071300d500c20084007004028041e00140e000384000d40703400d90310392945820001800400b0b105194241441c1665803100300c2140c019200350b4a1074100000c90f8000f1741c41b09415a8420340541d00403c0c0380307038140002c06512424841072041010042c50805080d680c0003900c802d42485904445049000070406564444a44000134070b12529002c009550030222003000e85806d1105a0702d0707518202900d501c08a544602c04003124002005000e0880e950317005481d060103001c000e0300c0c14807403501c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 569714316 1250 569713066 569713069
    0x311040b1203120405010c1d090907090c0210061508070c0f140c0109060207080a0f050f0d0c0614040f02100e120307170702100f0216030606031101030e0304090911 72
    0x24014043d510801c00c1051400d41002d5003503d08840c00710b010481005c00c406001550145036805180b0221070341c40c00c588030011003600c0d08101341c02080100f441c204c4160800c13a00002c002c4d20280f0b10340c4040c004195142624410101c0c00100c0c440801c844100003a092407003000b040d1100c82c415040c1140c1d003005900d4000400c03120080b40d1546038041c0c4400915986c0206034080103040c90301c004d0040b03a040504054640070100d80c018460f202c12000001000300c00d100480540c01c0d032100721809980d070300a00416175004000d041e03075030038a01401343ca40c1c005c000c014148100e800000d10035400300b8a40c01d0101c0e1000c401642c0b0308028007100da201030740e0b444114000d80305420100a54440c920341c2000464582c004607503000b4481c0070080640141c0395040310703446080043c200079a684c0c450303e50a0742084101c58034004080021310000c0b0070885154041019070380541c1d807403048024000015003c031100e61615015982c0184030400000d01c46070070040005200380d11001d8040318410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 569715566 1250 569714316 569714323
    0xf0307050c0a1a090a0309051c0210020303060111011a01050903010f1a03070e16080907080a03050403060612030c1511030103080a08130f0320060a0506010f090311040b12 75
    0x4800f00c5030003d485a01036402542600c000d508400c401024205065040e0f4001d000350303030350340300c0d00c0d010380041302403040c01d650b1260310520310f960013424144098044541c000d440751300442c1c1440c0880c00c00001c100384080144100108070310701d001da8bd40111044001901c07035800104c400c039410742d243c4203071114014032400340c070012400030708a0888840443d020517041c0f05c500c0d00049d00c204941e50400c035a00d128510b401078500c04a040c41c20070740c1c540241d040c2c180307510707900102039a114540d021010944e000f401002103174001d00f4100f003816202d881c0180c900552001c05000500c180121902003a004880c640c0d000380201000038084081d11050042a04240c0c0140c4040c0c0000c1180500c56030002c1c0c086030300c01d05921078480020702965541c9441806994003504000780080080c103100051a43e400c0c60054140468141d0716200003980040c00c01200d5043c0003c40e40a240d20405001700c407602c003900d6001c1010001404104203020081c10f05800c0b55912181310102c8071642803003803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 569716816 1250 569715566 569715583
    0xd060f020c010b040c0f02150a090807050604020307063b040f060e1b1b0304180f0b09060a21060213231804030c0516030b010b0f0f0307050c 62
    0x50020a80703001c43c41c20081220381c0074810705c0603c0346000c001c00200382d01082500842c10b2141c212020b540702c3c0000d0000800b4450b070020840e200009030981032080014030107210b680308070115010141c48a808a9030560310012204880c01076207041e02c41103d201040b412220301c81400541c0d8060300b40005819a13228601c804841d5130741d21001d0040d48801c03020180e12850180900c01c81500400b8020114890050f0850b8400c400c96040803900400744211001803c0c81a00c2e910854151078000004000c80a441c2c918540f51020071649801c20800720f51003800b008020305451464034850400e1782c111807040045c00c442c06128403001410600c0a05800054003401e240703a80c1c20100100102110040b1400d18640d03e545c5018107640c54940204032105d402521204c03589075460306461541010714020079900a24040000000000ac200d00031a801100316000030b0b6039803100740c0032030311402d442142c00100c10000b41e0040e00a080046402810398a0510324003032210007c4d5003041d140d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 569718066 1250 569716816 569716837
    0x60902100c1b0b1c020f07030905031b03060c0c010b09070906140301030f02010f0c06050123090c0d0e0a0c060f030b0102010b03060103110f0310270f020d060f02 71
    0x10940e410a014009604600035088910301a510703c0c02c2501c8841a400b40a607020686000c8500d80841c400f01501030340c2e1100040a001912a0054500507003078202c00c0c040c030b5000b071066452030894980d207801e2101d0030300380c060702070040e40e00c40c100c000103564040c00c03c0c1501f81d901e030601002c160700c0d20400c0e0b03489002e881d03865041860401314002d2410881c0b000000c1440f0051006001241d480c02c40403104d030350b0908021240500c01c61068500c081100000b910140c81c020001403600020412456101c0180c400201010b180303004000c101d24098400c1c000c0c03484148060b6440c807955500c11075034603050340216198172540e55120005819640c1003000002c40481400c07140396018040e081c1807903401d00081c4074686030140483e585440510000d44829100c18561840b501c0e82c00050f4601c480150039101045140d00040000e00050180081c24404c8600039409901d0039100504c0216440700e0b120000f10b046030204002c0da90314a03002e03540c0b01d59900c840300200c00503100410704140e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 569719316 1250 569718066 569718077
    0x9051209040e1f0c2d02010f0606120504020307031e03080c090607030e0406090204060215060d02031b060f070311070905070e1c05070b130f0303050405010c06090210 73
    0x61009000585022102801103039012100503108543d40e90341014851840745000107401901141c116010022404a07504046608400c204600300b0910520340001c0f054009002c1481900d806c4c1084400a2080400103803d038250035944204940042e50450300040c11503c038907860b82c4407801c8890b04581030790300d40310407981d0b10f004054200003010340c810445840c0c94102800c40010910903c1200d000404000c01000100300623034030396009101500040c58110348603a08c6100c003070b5031084400c07010a421400000060300515046002d0b2208690103806800071103514560076400c41546224070740d100501344854000c01c1500c90103425014001e580c0d1140c000502d40705141000c0c00741d003041c428141088100180d49420030a0081d902c18161444404400c1d20080d044440a040000410902607004000368100c0d80c08050140d5441042e2903c0881d0356800c0070000c100214130009021450600c8100920340c012440d80801ea40a1500403c104005500180b400d0131690b281002007070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 569720566 1250 569719316 569719327
    0x180a031407080307110c0901051f021f0606020c12071203020a080d0c030b09090601061107030812060102100605180411040f0606030b01090f12230307110d020904080d090512 76
    0x5c00c00c01c12540c0c5000d0555940c412941004046480000d07180e1700101c00814450701d8050051080110090300144180c042110b502030710b96041c040c00880c483c0c0c40040c40f50f079000401e6850304031101507580030100d00504540d4a46400030040442d041810380c2540100d070003020115032804000c202005c144800010002000d070b101808481c4400f00807409010710b034040041e501000280141501c2042c14480310b80c1c80503d07c114a4800d150704010045040800c11004c400c000080540c001e008c01d8007034a850f80f60030841c10044400c90b100d49640708903441f40c0e0000c0c0c903100110954000d401001c200040540000101c0d007a00c0c40000810403055580390300b004a1945032041ca500340c3d100f482c21408241c6072460340ca40d0300307145014205080e400611480d08109060318040012000940d400032541e0606030302a840e07411025061320b06408403040380c07031395242090400c12a26401424044951038940700c47d0042c0e00418241525103994036061004107100b003100f400c5000400c1074003a0b490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 569721816 1250 569720566 569720597
    0x3040f06020606010c0b131707060b0d0f060506010c050316020109120503041a120108070e0c28030e0f010920100e0d020406150305180a031407080307 66
    0x1241603800364045401100c140b00c00c1e40e80c80104c3e07152040c0c01814984040d07e5004111440030b52901008002620303c40c90252811a018043d140b880e019540400105950006000c45100165001401134880504032000a22154040703508250185003511a08505946042ca0b5511507100480724071074003032040e0119a80301a0850282c035059101005c1e02000360380e03c0d17a480c010750003101c000c03410301054410004101030a50703902c81d00c0c04e03c4526030303940e54110441c1c54918901800d04040703003503000103240c91001d0342140d144180081e0480c2c21034034600000640002c8202e0718408041d1503c4410121075020001d422820760240000505900720349820062001c032400e003a070a01091038200c00090381d500e85100f010008078217080c81c0c90300034038000071a21a80b26000941c0070389890008940c407400d4130340b0f44844043d80d480c20000c07034903800940c9080d03100309a034920f802c7d8800760310340000921407003090512410140c01c1c98108031040d5039284854004035124800144a41350103e0780 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 569723066 1250 569721816 569721839
    0x1602060d0e0c04201606060b0a17041e020a0e0702011a182d0c0307030e0106030c060e0a080f01090c1a0405040b4b0a0528080304 57
    0x644604450400c950305004925095100c40280f00f010218400708400d003560351800c82d41d241456004804000131038071023160800c03e41000c8420b0b4006945070803401e070460781c81d030703135040c06142c0240b40681c0e00b5081d500c0001030b042840b14201e03040070b840d81000500040c402042e5018881035000440c200090054a5031020f003086c2c0c4030307232081074000f071030a03000c01e800114540c00440c0110100004c1500342d50320086108222200781602d0382100411840d03c8001c0d0265000d244140e400340040ca180c0d00c4100e003070350003600003e8002c15000d5010803041b40a0b00381c00e201d140014010140440d039551a090034800403030391100c0c1c580d448001103c10854070148560241c151400c100000003140d1030b000e80303140568020f150240d60760b44071290340c80e038a1541004a0b02e01003480ca2803440f40d100700ca40500c1288010198500b845901034104501d00052080c14015000c1c140ea00001d20700820070a1b0055081142036101d03140e24600c090b1880c2620402000c0c0180c0801182d5603843d08228001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 569724316 1250 569723066 569723083
    0x30c06160e060412060b03031b010f14100504050a090c0312020f060702030301090c0e0d150b040e0a02060702010507210f030501050f0d03030e0a06060f08190303021602060d0e 77
    0x4980b00812050100d280d8480e00010300541048000503e00c0310603000c00e2441c8180b0492400c50020091850105081504241020712445009010f84015803680300d44000c000e503040350300f1000c4031106100d6800d1a601c047c3c1e02c44640c0f940400d102d00d0341d80b0350010240054100799070b0b4400500b58030302e4003030301040441030640703221009124130321f800e2500a49074001030140d042059120007220340418070682d0800030380c01d0014900c0c0b05550342c41c5400c4110440b0030310320240441c10407108000610340340c411050520209005440440d24a600f08601030b4010242281480000d208400c04154204041021501e504940c21011000d0a00241c00034041150b13040405040c0401882551034092103290148400c3d02d503844c05100d240303015800390071914144800c80c03140c040d0701405d00a054025030104d0f0440160b1710b070059252001c0e96164044103070801c003422141800c0000081c1710358001d296a017034094004d0000e03940d07035001030065441f81d21503180c2d85840704800c980c1d0003418040e400c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 569725566 1250 569724316 569724319
    0x1080402030106090f0b03011a36010602100c050901172d090609061e0a14070504050f100f05031005041802041824060f030602220302060d0c02030c06160e 68
    0x405481c80c00005108a1140804460b0ac9007910103042d0081c8030b80401c0419048081d80c5009480d80c4442c0700950300c41c4100201d40f1030a0400f40c1c82410340740250f046500b480c0c010380d14251120313404110101d000320054094011058510300401c00301d802c040b400d02c902503080c441ca8480d07040204490785040780141c42408035030041c406200701ca26035003c010920720141494240c0e03c1c2d481e00384041c001c0840c1d103212212070310042e0402c141c03190301c1741c01027040e50411a04a01c00c00803410034003d1040d04c03003140d00e021455018100304030501500103160b002015070300d8a1512611100464150f400d002d07500d151300d5008004281c03c42c0752500500118206140760380d0681c1c502a1120800d100c1e01c07001c0d405030000d10180350708866040e070300000d0140214250017000075a580c503014001350300121250380300c01441c419900d034055400503c4d0341183c0c2c00800d600d003802000001c0100800300d0710350280640c0301c00c205200800c071003805803a100b0b03071102024a5084840745406000864010000c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 569726816 1250 569725566 569725601
    0x801051020190228090f0b1e0a080313270c202103060d050a14120a09051507150509010606020c130216080f0403031d030c01080402030106090f0b0301 66
    0x26890070049402c1303003118001d00020550300445030b030400090044a556070b4102000c10352441e11b1302429080701c003a140c400c4c0c410484103540d0342d40680d1a8003c01e400c8680112080c10100500f0083c016442303a6001a00b04a61560845070310079800c603180300c42008041a02d4040b44588030111a07031401c0c0d101500c0000e0030b0580461390145c100c10415071504018190302001051b0b098484071080c9034000c1d0710408407180d4900e1030401c502e1200f80d491700b1080601c0340c0031494812900340d0301643c50350005601c40c000d8041c100380800030b40510306042c0d9000f144040c49008045840c410204900742d0300b122000030b050500724080c2d42901c00e26004103066511014035503916840c2c2000c1c04401224001005849428040003181d88404483d0003821141d0040b84407980c1d00c00ca5002402140d210307840303c000a41c1042406480340c45000c8016505410242840700030b5402181003607030041c0b005000150761500c8007051011190501d0752544402d030365101211450900f4410100344401d020500b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 569728066 1250 569726816 569726869
    0x307170f07150b0d0b270d0206010801240e040303110a0305040c0902030c0d020903030c030c10060e0609011203180611061e19060302090a0f05060108010510201902 72
    0x12841704410240811280148114120340708120460b000d41d82001040240e071011008a0002036540100303006181240d440e0441d800d04400c0c80303040161400c0c12541c0f9a04e5030b0307450513004c0c208510004009900745034840401da60400540b0009020490142d00e00003494103280c00e10203014590354010b044440c0c0b04000380810030049000b0343c4c951002086016076240e05d0040440e04600810b9100c580c14400030075800c003180c0340404c00c2c4416066080c41040310a1b0345003550034001d501682e81641101c2418014040b60ba40d69000320744e0640a41080c0c2401408025800d4032036115602000016900d2400b0b0303a00304000b440410b800c01400c2c440c0030f5074a8140b1511111580015050741440c2c0e5181c0700d800c22403500c07a00f000b4019500101030359100c2c5031102880024150034101200101c1c030b404001542c540c090040181619409401018110000d2030260340500140d620b50700903c00644d0720040000342000356040c410307540003034240300e805180305000311415136032086040901e0100a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 569729316 1250 569728066 569728073
    0x50403110a051c0201180804180212041202030702031c120614190902040306050412050703080c0d06121b0803210c0d051e070507050307170f07150b0d 66
    0x12a00b100c0710503c0a601420442030394103034010048040d18030030301d20344910b040050040303410107441291001b028500321491a149204100e2040d400b11150050b41640401c1c040384002001d00c03214082801102c3c54034840b0380000303151495450300c80c4904a00f0321a4420882e1f8004010a11109011000e000042c14030741b44940003000c1705003080c09332500c40826024030411054800013004182004c5541d1070301ca061a001400c0c00705c07019103418803102020146e25200e01c2c12074004a8155580a0994450000151140d07102c09560320509442da030380400c40d19000360b02e003120113208542452400c0d030070001001d862103940e0300a00007a0018045c10075901561110428080c1400c0030940050f80c0e840c010440600900ca800e41a081c034000400002c081038041e11003024240011000950760392044c11210f5126030140141103400c103100c94070001f1148807086041c0c041c000c4074981004c65038406c10100b500080010303500704d50b44200741c822115141c070803180350a006030369201b00c4004644 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 569730566 1250 569729316 569729323
    0x506030a0507021c0233010803030601090e0f1305010e0f0c310905100f1d0d05090d0c0801090c1a03010f060e04060506160605010b040f26060a050403110a05 69
    0x131020221200ca0542202d0190810500c00d06d044112540845543c4078641c1030340e04d400841e4058007180c0845c1002c03400c5e4802c81c20142c810804482d1080141d918184d404c01c8006c0c6160782101c0643d03c1d66000000c0280c1884417071995060303080204414405942000214541c1001425000c0c600d00e07175107000c528140d06101e40b0b002c40a140420b810074586071107843c00f91420aa00340c0c103407038121150400c089540094107150070081715200050090390403280c948454011031400310343d04003c1341c1701c2414010486200640261350400446076216a00c5080d601208021281c0c01c0c0320301420312000d011f1500e018004003c2a80c007500b1503040802202e210902400f4450500180d03c030440c0c0565900d0300200040d1401621060b1599025407107028000d0a01c007003220540d0030b040000c10054042c44c140c400b00d40070112000700c01ca1800034100030340c1c0103000901c0c3c180881c8030b500c91424041002180d0040030784000c000703020324107414002c10740d903040e540c44501c3c0e400540c1010702140000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 569731816 1250 569730566 569730583
    0x1020a0201111513060c110613020a090606050c1b090a0902032113090b13051b030c0a03060b120f0702030403050a0506010512030f180a0506030a0507021c02 69
    0x81c201001107103440480b441c40c0a400031050358000c90654200300704521008111007a0754420301c4180105242c864040c0c0392000d500301181c00300c0e44035400080c8905142c1c410601407a0024015040070754071410400306032500c83e080000465400100801050010002c3c0d180c0c2c030048044540c42c50207020f0000b0003a40300900b40c06c80b0705d5100d03441c0d4420b5650500a1043c01c02c00ca44a5010f100508903800701c40d50071003188103030f803000d0303203800055801c1d058024118004002080c401040e10800405001000007070a8818610000020b1445501c01c5100550150300e05c50446138540350385d024003d040d01c459800c002d88200c41800307456400320b841c034852508080002d0303e5000941d11010103d02d1070059030320240541c454102c040c3c05001c0b000c24021b060303600c16510880601d004100e030b1a80d902c110001004d4044003000400d990362040064880c680d000107117954150765590340011000d40003074440400040c0d407842400b803215010002070000f4038942c0440054040380c490043c0d154070380f8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 569733066 1250 569731816 569731819
    0x207031113020d0509011d070302030a1502120c13061416020111010903260103020d0b07030908071401050f151c0b042d0b010510020a06050721020901020a02 69
    0x701140119215465010355003500e4000108200f14582030075010302a2004480c20154210034501d400c64030b81c070100303003c0c041e6500074000b0414400303240c0d14091012070185100303003410342c20311101c080c0c00954041a405440c0710051940c46143e41910459501e40552198061003003031079144054190f2802900d0405421040c01c0c00e03c0101c600060792044030501d160505546000300351020942c1144850120280300034140341c2c00a85500103080e02c2c50203001c0a5844040c1544502c0014415060554400000e107001b00300010181d5660507160000780c01110380310504556158a4a0244100c9600c48402410110705040825134010398800e4810381c1c900440302001032090024103d01c035004110381c000c90000c0589801c0c01c024039030035444c56041c0c5c241180c0c0340c0c1e50030fa4084900c1105c018190803107c0e454480c0d00c0d0504215100040098010a41c0a00d201580c080341c80d0388a00c9118007115100d000c400c60514040205060090401d590030510503c149487e50340d00060321200f1650 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 569734316 1250 569733066 569733079
    0xc080f01050d030903060f14090d1413051c110307180902010c14010608060c0310060815031006060207080a051c12050c090f040c02060f102301090602070311 69
    0xb20300b0116031342011500040e05a07810708403090580025a030040c03d1181c0e81d001808000d454a201e440d46030300b600000354001500201491441e844940001c1c42041010782040c2041540d0b10b001c1480e0342c06d0306400200c01a0b906207064144012828204000394086019200d06414041c118424010050200d00d442da6145002011640a002494403280d00310f00e100ca00c280c3c003950054040d0005000e0305200d40146400f140c100304d4424150303070207002400702c81d06916003400ea00b1101c48000400d4030054410142c0350b01e2a03520305200c44041c00c0c40c1e005020030041d0826601031f02c3c0c6165030380714010030b610200701c00010880101e0180040c4c0703010600482c411103804002c41e00046611032407589285890140f10740340442034000c040b01035041d51500807154420081004a0b881d000b421400741c1c100328000345942c004075031490b07402a0341005109000307486403045140220460903019610f200060709008568100c0d02c3c0030001c04d143e20050400500f13698a2a50010f54030076094080c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 569735566 1250 569734316 569734339
    0xd05030628036212010b0d0605090f04060f0204090f060f0b0a1d010306050a0b0705120403020d0b040212030705160e041e0816050a172b1503050706030c080f0105 71
    0x1442203084502c00d081c40c1445900ca561078400c500c191f9403100c10781e40c651628048000a01d4100040405e11070603008200040680d516200c1501078030581842c040056402c0001140d424810310a40201c060f02290001e030241c10b00e06000b0818502303070041512030304140011295190b12044413041c03c40d141d0800e52888400d000140c0107401140c119030b0748000c9070180882c00d000060003404503140944119042c171031000c01501c14034481c9010280d0001c1611040c480031034017000c13521780c010344040c2044400c16090b8a642d811a00242c4040390070b508400c407112540b0440211500180185191003902810651744040b07840c9a420103400742c800040f5129414031000c442521144074850b02030500d000201d140c00c0e502c1e181003441c00c039020704c1d1a1002d01c2019050310300791101d40d01101ea1104074034000c515030007602c103204810703a880305494081d6660061901c1c00702c0001144100c005051203810140060142d8141203848002c1112580030010031031031a5030254110380c000d8502b075103010f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 569736816 1250 569735566 569735753
    0x170f090d030f1d03031005011b02190e100e0f0601022e020d05010824071404030f0b0f070e0102071202180c0a020d0503062803 56
    0x401c0030400f24039000c80f035218404a6450044010742c800c0408507110f61900d922130f001034079000b45000082c0600c00c8041c4109005040040d00f009030b041480325070300a425501c1803c00080d01c0211118044041e91840030450030b112612400e0300428044000c4409280c080c000070356481c0c003c0b820241d000c480a83c0500140e100280e04038684001071819560340c81311003080700c040c1200384941411407207020407440c4a1104d0400801466000e841c0c4c050003502c6001c412500c226200300c484010082c10803002000079000c140ca148441d12503680c0c01001e20707204c00d00d00740e5800020000d80c00d111900301002c000d81e034045a060140c541c280c11200149c000d600114000c20b091001e07000340204001c0030f0005003090301001d085401da0315400c803410060811800c403960700050f03603140d030401d005040e8809d0b030b143d82c15052488001c03080030228410f550b035241c2020b10407520980003a0300301c814101a48410b652a81d94814403070ad141c06401540650b0121820782c1d013443c2a20006044044005042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 569738066 1250 569736816 569736821
    0xe2809020405090a2c01140c120711070b040905150a080307030302071106180f030a2f100c11090105010e09221406090f030a0f0e040507170f090d030f 66
    0x82c8503040c42030038114483c005c0098000c10034241d603400350324900340001c2d40460307003801200d1354030800c0c1c044880982c8a5042c1541e61207024860030300300d802100c8011580324505009080145031812000c1028200900480e1079013190030340e0785000360410402031180b07503000800c070392110b941461300594a10381410b11404002140002c1d80d03200500082400d50741203801c00e03249012504440300208040c900381016921421040700070114000150782500040d1030300c13a40c16850984815400d811209440042d2521140c0310f83d000210f43e0180052042c881500f22440c200704003076400001550400c40040c04007600b401000b88200014800246500b060719841d40c0ba008044010303075801d28561400f80d00c240e0810034503404900c03440002400380c2c8000204e10b4a4401d126005c0d41c6810503c0744115201c0200300751076018405030714044d032203070b40b1584203403403040012380e9401140804003801c1980c001d001a0280707403000006070500000c040302054006140c2603d007800500758200d030581d8000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 569739316 1250 569738066 569738111
    0x2030d1107030516020d02180610081006030510090501030317060402040b03130f05030f0a03050c091c0309080d200c01050901200f060906071b02060a0e2809020405090a 74
    0x400032031144142c100c0c00c0d02c00c08080d01419040301c5004802b99012030850352032008440d1554081500941040304034001e91140c0c1e004040303403004040407a2240003034016664280e20840000c0c0c20b29802c2000c81c00c92030382c100c0e00600c0844040d4035280c64122100310b98000949005441640d24a55804000b0314070400c8021a41c03042c182d0b601d62034071000c0c8003a1a0030895541780403d003844002858646900c080b1583c03860005d1450a400d8500c2c041c000c1c018607800002c8060000d071039000300c0ca440d001c002c140c41ca0070340c0341d4501c5203810071700300350b00d441507501e070380f0f4150650000c004401d00daa0440c0589409180c00c0c600710780c80502203203820a01612510a1040074042c04260a640190100e58035203e603c0721421580c0e1902c0b01e180442d860718200381350041150040d84d1302001450208003c009200a914111a00c0e900900002e15181640c10606907200341a100040c909202c1410000041c22245411801c140c50b2601141c0000c00040569401c40d80e1944081c2220b2420303101d450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 569740566 1250 569739316 569739319
    0x41e0503040311011b0302100b0603090a2a030f030e04140c16060f050114090903040302150705010e0a0507060512060409050715030506041d3a02030d1107030516020d02 74
    0x1170188642c2c10b01a4071084221180c00c8180e003400b2041a1904201c41203901510040d8001d119014490302c5c1c5034541410b0001043c1c3c0342095100d243c1941080040170f40140d0f00801c83c0131424511441e01815003008245800d02aa0504207003c5002c0c500d0456154041c1d0311612040d5513100b000038000180d1001a80207010619103030300c03212410781550110b810f030b58880c181601240d01007000c1007a1050100c9150b071081c1d108210600040c00c107569000e1408045050301e40c1007499940d2140d0039a00c01006a48903a80b000c170100c020700c00100000c800401c45400c000e4984928a0500c200741c801c01030406000b292106c55441c200070040010360014102c0d444078040d4119074560050190406843c0b440c030484c144018074498420395100d81c4811842007000301000c1441c1454220301446a07104040d078a17070f0682d0003818080882d02c8442d055011907001c0c50307803000410105000c845032410760b407403102030901c80c00001036000001c6480b180c82c0510884050716003440010340d41c54840100a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 569741816 1250 569740566 569740607
    0x9060f15070c05030606041e1a091e070302031614070c0b130501020303190f0b060c1513020d031202130b070b0a052203051e03041e050304031101 64
    0x509024410b800b403025030780b04809640c410f07101c441c10031007a948001e039603140b0030315200c01181d82601130f41e0001d084000c0483c1e003020800c1401001454200c41100c46807000a038a0201d880804c0140981551009840c10110305605001070309024812030602c0440600410071400544081504180d032000f550000c11003440c941c540c144070111707801055402550302c00104c03001c91a0341c004015a403017441c01100b00c0c0304040980302100040c151071a08000c0e8181c0d40c98040c00f058a41400612520f0a030740e00405c030f02c3c040c1500001c10300d10010030542d010458410407000690300c0310f0030300c0159501454400c0c810207000e0401c4009100700383d0000551901c610002031101c203140701824002d409009a80c1751546d0b421645015180d0496401801103841520029168111243c60810340e0007072074117034184054911098110780c1c002000c924002004001c220400140440c909a420743c5000765021004540e6203041d41d9001340d0100500142c4c01020345100c5034402c1a52544041049154 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 569743066 1250 569741816 569741827
    0xf01020a06050406141b0d020f090a0303020601060905180c070c0f03050d0f0e2409090a02042606150d0b0a0c141c0c0507020d0602030f0a090209060f15 67
    0x188010034000e865125a141d2a000041070410040e50300f50003801d4103818145820781f4102d1040080d4064000035070746e103000b8801e0b00c60350344850121a018510940081a5550428101074045001c42e8006031003411540800c06803220020400e5811074205101e050703c4400602d0038040420b450382055212009040c40001803100c0001c0055a151180e01c81c11001d07071a02c982100c1901450500b5a00002c11912001d0b0750300c10004080c1008610005484c1451751007000206820400e582d4401c5032034010405001c4005001c81000c3c442416468070104416051038071521510010010031100c420001409034688540724900c1c4842e034451040710b25450044880e80041c01380740700c203100040750b06c201100c0c598403580841c0c484060704080f1310000d200a4420320054000d22401804000c418041003006803030b0800070408041c0300b0358016849207005c54201614000003400c5015250a110016003d40c075091402500701d40252240000ba55448001c50b01d0603407411071500c40c00f100000c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 569744316 1250 569743066 569743073
    0x1608031b13031a0f1314010f020316020d23120a0e0d0f140d060e04030c1b050d0b0907151107050604030305030f09010f09080a02061e060f01020a060504 67
    0x10084242ea12030410b0a002d0840650451003040c0c0c12641350145031260404200c0103e00e941c20644502c4c030614445120900858096007174030548010502926000b0040c800702000340014069401c0ca035100611041e011a20001c2c07041c03100d4286010880c000d4640b28405003201c0c4222400c0500045c15584103050a070b0f03801c8018014006000203500610301c504c09494840e5107012810b000c2650340c851016260a036650655110a05010b9925521400080c001004c240100d05c41c0e4020b890f003100110035400d107040383c40c0c40c01e0701132000c03078005132014411669180c1400592582040c00d02c503803580e62030605480c201c50368100d4070295044c01c5003848400d44c1f041004550004280c02d540034142c0e81d205002d4240260300005000c0345003800020501d04000034113641c00910307080041000c00e103d005503c2110f540a0f0305440a100000301c1e06c1040f80c0420440c3e4000c801842c004100c41221000208260070107030441c0d1140c41c011129440c0390f0300c01c01c07000a2294028804102e641017514 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 569745566 1250 569744316 569744347
    0x9150904020f070b180319020109020312072d290a060801060b07050d03090302121908090a02010c031233050d030f0e01110a0c09050108031608031b 65
    0x10fa04459601c3c0c48400254030200441004858440000085060000d010030f400381d201f000704000000c5650310460f10002da60100150701ea008141ca000c0790b550f0019003040780f801c08150f1100141c1140c0500710301e040038101c0d00403005158000024a50850304e8001034110190400c0d03070808210300710410f02c03482092a901c8a001c448400c2e0081101daa60750000d25441c1c0144003000e0020b402421050709168066004005854401e1055402c07881070001c50b41c4040c2c00180b884500bc080303000c00048603030303000f0301056045041d40005000c13102c0154002081e241c1000402020001926411900360032039402c00714081c40807055103014041034003e01c111020f41c01c401c00c62401c441881c0055213090260b1803210b10307505540d0302a21410341030710644a2900800000381003194408a40401842c24040c0201c0b45101c1d041880c2118644480031040d0b8006070401e2001da0010040e40d40c0180f0a8807407019410f510825143e01c035510003200308403200482e400802c0b01c0000040d001d8824140780c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 569746816 1250 569745566 569745577
    0x60f0c010b04150503250e0f160309050a021302090616020312031b0a020a0b0c03040b01050a051e030102071a0a0f20070203011e1d01020f09150904020f 67
    0x2d8070108204080c142190181c200940325560301070300b00e800030785e060a01c0507121010603100100c02d031030440e6861103c545215012514415207628003801d109201c01c04080d040301ca0040341c50280030141080e01c5207503c603040003000901c0342540142c880392040603901665105080101075503181c0c0720342c1074440704d850b41d5400220300c24016001d01d49002e000035000e1340c0c0107100b526510307010b645070035800d2640f03a4009001c11056100c5c01c001500000d20351103400c1d2040014040d0f0700d4070ba003800d10b4021700084042e00403034403030103e00c0400c0c00591141c1c0301a0410440c496403203824039966a000c81e0091042100103443e100003151038002c1034088000b1140101181201000b0b0000f040980500f2100001340312401605205c8072041244425400f40502500042c00000c001040c42c4014419030340c42d03502c1c95095612a402d501d00100320500380907480c541c4030000e500c5d1444044281c000c6204450013030340706100010401c9441c1d0507003c250740000784e024004542c0c41c54040c0c0d4020040c0c024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 569748066 1250 569746816 569746819
    0x1e0325032003120f01061b080c070b040929010c14060a0504050d030510060806041428090b06041805070b040e01050f0d0611070503070b011409100e06060f0c010b 71
    0x20b82c3c2c08150704c4400c2d041014100d0f1040c0c1d83e01c5050302d184190b40e1144c2250585e00782d94165080c400c410f9100018030124008100701400c941d651450610403500740c440b082d04130100501601803c002c0e003280f0404454801a00746040c51400c041413600c801c1e50309002e40c627130240784182800c01010b040f00b80e2240740128003d41c100c4503408446c040c1101656011110202c80c0c0790303ca0340800c0f5003401a4116600840020404114844d2900000c180001c040394101c0380d10001003030407200c00303034002000415031100c49024845034400340c80b80c100d0940083d14880c080d50790741c004c0e0041089071840d0075087c02c3e400000d07100d4050351055003001135081405102141003030180009a240351044010300306840107001000c075452241c494100500316032140c8454038004120f0799000035010b00060002d244075800d91882c44d410f00842d100c0240080b040d16000e407014805104401c0e0f07240d0b1901080700d804440300d0415076164400b040b03d0340150242c59030840004506a540303800103402403400c00a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 569749316 1250 569748066 569748097
    0xf190e07090509100608041a09010c080a0b0d0b06011e050702011706010f08060402040b071505010e040b04140307060204140f010503011802030604140106021e0325032003 75
    0x2c80340204015820182c50114007a030b60f84404200450080700c40541c414041c469100c1c16024400b96079082c00000c0340c01d1415a5902c105c51621b0642000d151904215a100100562410034002c224025042140940043e040030002400c61384500c10306101454420045191342406000c05801a0400701040340400c2004c80c00040341034149081e141301d000140d441c410700d0143c1010646020303001900703c5401580820001c03070051030220092070380a205040000d90083d1080340303001200e2044e003040d0714110403107090001041100f0012034210303400c01d030102d1000b90000c041900d14821800000d01300e6001190010b07101d1034401c00c0c241035a8058a003a0700300aa641c004491901c0240109008400e6040c40e80c8901507595000d554840d8020b44001880483d45084080d0328000368400d00040c1e02242010304224402040c510981c290f860041d820441401e0900034034034441c80c802081000c00003c1070084c18400c0409030040410600340c124001c0b04030810b2a00d0341d011200704292481c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 569750566 1250 569749316 569749319
    0x4060f030c0605190e04060b2a0105060612130c170c1203041e0906032a0302010503060108071808060601261f080613020a150207050f190e0709 63
    0xe01440448060040300f04800080c54041001a20800c0c0e01c260446d8000b5070310f020220703000c2381e00c500805111181000700700800344d1014159100346464504600031f81d0501040c0300440d1100d400b41d4101c00b003047c06400c4035030f454401608d003802c3d400a0161041020303410000d48013011072035003e9924440d0099a80f050256000e10445030320410031400c150784200010848100d9186a441945c00c8000340151103d80d00c200107405d465040e00b05850362501e051400c80e01c6030741d06503080281244111824003107032568002a140f40402003156051112002c0051103043c85240f0000f150b940703162000105d151a194210390303034101103854034041241e104104809541040b00b403240100602038661666076007000c21400c1c1060501c000c0040c405013000441c106030b0a020f800e11401e03403100c046c841c030600350041002c18100c0354010015072500361719130b0343c01981c08a4240300f40c2d04260b4071290800780c0c410118000c84076164220b40e00810410010412003c02c3d8140e90081c440e5036a0f400545 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 569751816 1250 569750566 569750579
    0x1030c02030a09090b13090507061b0803010306111603020a02091b180f0a080c010e0a03030f08060a0f030803011701060e1602280213060b0412050c04060f030c 70
    0x9102e40c0d6519004141d003540c040104407102e0708810034044028010129105040014005944ca20030003100d15410070b0b08140001d40c2c0c0200b4104ac800c4444640d00c49100c6140c841c041d140c4818040580b41c951500c001d50464105d64040782c2c0401d1545a245401048505000303464001c101002c81c820070f082004904580709881070414410703407500c2c8051500c0e10041c1c2e038400c800c40e500600c03600080580b03101c0050380d03540f1840b80c00030400c5034043c2017004242d5000421100c01064100d1080202c40c00600100c2d81c4000b03500712882060a140d03c82e03441c1c120000389201c0c6a68803641081e041400003004005492003c4c604880445204640d506445845282600d0850140090003910800050b40c3c604801c150000200c03a1801560805807080a10703000318042912052200c045110b0f480e0110b0821802040c94901030f40410000142000c20600c102c0c4514071074002c44507030201d015403e22800340426100b020000703004100c0e155940c1f4032403041942d00d1000744c901d494a02c10002d100e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 569753066 1250 569751816 569751823
    0x3060b07061a0a21171207020105090a0b0430050d0b0a030f0b07030b0429190b0a0201060803122401021207050309030d120605030a1101030e0f01060b040501030c02 72
    0x54038080f8480e450341048240740702e508080c00352800d580b40d8800b0341140d0b01503000e1100611b8848145400c071250b9240c6846c020342542c801400300302c61f41d4490250032011400d600c0c505508168801c2d80311220724844520800240c011a82da45510135025002c047e01e0354214008086c10100e40702c00b400300051080400a80850903c0301900d0b1030300302c00041001404d4200d4440e4003140d10309000400040341d00200d41200d0350018200411b0380885100c201a10303e80c811a044400120f0700246441e9903124000d0300c113405803040023042c450110700300c0c001c0e0b0300070b4100e840502010401c494407000480e440c0004214250b0302d001d000400b08a140400107030100c00c0c0c0c5180c10042c0c00615181c00e01d000d00a00c1e03075001400c00c0e0340c030780002c0c450003105a409000001c28190740342c0e034810f8070f08981d40000086810075840903100e070780305146000010b41000c00e0b00d010031009080c0050070f18000d449243c1030600040c00481c4a502e44100410051002c00140c170a9500a91f402c00202a00e40300690340d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 569754316 1250 569753066 569753069
    0x6150609060c02060a05090d14010b0405011707060f02030904050906060a151b0f02030109032115090518070f080111090102030d0e1911040f11071203060b07061a0a 72
    0x100413030104a01d40c3e800d4020030080811070b102034003116003078149843c1e00b2030110100c051480140d440c0d00e03001e18603103040e024450140291a0781400d0010700e10034510b5441c1401d1203441c0910000000c1e03c1c01da41e00a01c180d904641000d00184000e00c0c08240300c1d5102c0804a41091098444c0c403000309040c20b4104001c0e102d02c100c0d0b20340226101c028400a0446103e0b003404840d8003000741c1c580c90060310f0a001d00c20600b8807907181e0280c5000340f11800081041060024801c10b8503100060640c461000c2d002c0d41100c07a4040009500d17115418283e2075003901e8291482544200ca000040c40038247c100b107012100302c1c000030003a50803100b010700d0310340c40303010030450040e4024004a0b41c018440d510084659850030304507440104070b20805202c0c003651b400150baa46043ca20f840301c15050601034000c1e01da0840c901005451017203048101a40105000500401004143c07401014080d60292029260814040791a21182c1c80d101001d029400100d903121544ae601500e0242007500540e030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 569755566 1250 569754316 569754319
    0x503070c0b040203070f060509100e01090506030402060c1c021203060109050907091509090e06040807141524040506030c0d1b0f0503071a0315040906150609060c02 72
    0x11880ca09072240218410301400076681801804400181d5814490881c0300420103601c0f070f19140d0f007070703070b07041080340ca040e603202c5402e01059481c0d00c0e4050fa40b208591082d5042100c200b61240c446001140f9140a60a0940c1a502c22000850090481c4280200c88401c003942210480080c404040c03039203000c02e81e0640c0c003090300980240014a4014041a800300051402001c0725568030b82e5440003900315030520010554020b001e00540e03040303000344103558042200501003410141da451800c0c0c030904a001d01a940d550000c1c9085042c180860440c0700010f000c100100e041c1102110b5008004c00c801c04d15502c80c4140401c501d041074000c8501c111801405400c800c4d85070002e101c002c6c81000011551a442c0941300d0801114000c03401c40a00036855294440d14104070602d40380c42174a40001440c2c034020111900640001d00403658000280e0a91040c14094000072038007a00041500074469410960041d480100303d482d02401c0724440e07030304c21500c5e070b07a210400d84030b003141c240010303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 569756816 1250 569755566 569755577
    0x706090b07080d1e060f0506040b161a07020619051005010f020705031501030203010c0203040e1617073207080703090807060c05010b011b03031e020f04030b0106050307 74
    0xa001041280300a4248441c4008000c2400260b070060046283c0813440d21082d80c0c0c0d9110028050101e20111420142006480042c50b0a003070400001090051a03005d403070020792075403010304000100f016031040703044854a01c020b90504c2c040183d107900381200c8030802a00d03c51a200300a40c2e05008642c05920a0502407101609210044903044034103c000d03820751141600018043d20100030001068003410fa0001c940e50442c41014203640c0c204220b0401c650003404103200b400f21401c00541c200724000c408220030100050b007607403100749250540426025a40800040c0398020345c01624440f0030502229901c8607950542415400d10446e00c0b52420080c010840000c0383ca40c01003081078080e0901880b515902d4001c00e242020756002407000480003200c0204006c42401401400c004c01d00f4602a045440310b90b140317001c0c803490310107410140c0b6002e003100d149a0901038035901100000040d5610654000c803554554818401141c0d6441214000035001e4070540c1603a0040c0203d41d540c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 569758066 1250 569756816 569756827
    0x4030f0b063c1f0206041e0317090114010b07021014040605070c03020a0312080108011b201903080105040b0d23030a0e03241b0c0313080706090b 64
    0x40200c005848007107580180880c0c08030030203038003c407003100c042101e954010002464145004040c00d10102d20003480d00300300000e01e00000350051600030211007403015a289683d00c072001d181c090700d21082d01040c6040300c40004180e48000b2001084034a00961710004962400354048410507940484040d141005000a0060350720420092048a01880d6015800758036a0002000090703e40e004403032000c607800c0301e04c96440d006064a40103104000003000703919100a030340208651203240840030441e1036044003a284150201032142545008200c4683e000460030202a0104440c4107801040d0094000542460540030f0f06a00036009400c14400c3c610781c1d0b840120f4001c24904082e055084a144c1d1800c5081c01c00103844100c049544049a1001250605090544030003c00c15003043c101340084210f24651078194006219004c2c440210000c100394605900420301f4001e030324040040c10361404249924414282c545980640c3c14041e511882550000b00038070894819400c140603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 569759316 1250 569758066 569758159
    0x80301090e0307080d06051206150402030a0e0a0b0106030e07050d080c15150f0303070b150111030706060303020105010618030615092307020307050a020f0604030f0b06 74
    0x100142a1400122420510079030341d1181d0b2174112001e038041480d03a44008110724601500d0641080d03d03614081c28403420220000001d1070a140c40141c0034540006c007044420b2042e80c40030304c020585005640c6114038038940315090903001e116220000b030500c96210104500420840103c42c1e008164881d4000c0320f0740c4550640d00404135502c620b000d8181288291b0012140052150825288c0051082d00c50404c01c150b054440800a000754010300041000500e05440140c00010041005c20a000c52100483e50000080c4105009000205184040041503000503056034800d8000784003da072640003c4540341c015120b407881c0c00c60102c10800105520754031608a0440400700c0c0095035454250410030741304041c0340c003801414540500595034252560268100340d02d4405103103000c009499403030751002c8079503020b44150128440103000c0d80e40d28084400840d4481d6509402c1045424040c001400495401c3d004a4085410307031544a45001c17030001c40001c02000102d10485180c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 569760566 1250 569759316 569759321
    0x20d0f080f09070803040b041508060d11031f050406051806162d08010e0105130f1d030301080111030105060a081503010f0605150903060403050a0323090c0102060408030109 76
    0x800b0010240102c0304089104403003400144060200106419a07030703880c18444081242e445512078040202900034410f681d80d03100940e01e28690040c03880c2043c2c0c2c0f2078100003400c11aa904008013100368900348403503c402103402161040380560750070881541d0308082c406c1102d03442500f500942c1c0000300050121000c04a041050b10001d01d010200e418160400e031400310f08440c04c2801024030340076042d03860703644a900320340076015222025442c0c0d4502400f00d07a03082c1140400b0700d041c9071200342501442c0c0c850343c005952038a41c0e50407030f00d80e01d030344450f05900c942c803e0160840030b5080260011729050300c1411a8103c8030050212407404a442d041298500d802a014500458074000f500109980c01d0288607000340c01c20600003070a514100400c502c05e01c680b0001021014144001ca09a130750200e0f10075802505070410030f40d41d03150030b0403c6005019603400f950001040d100610708485103426802c5c81807034606d0494440601c04030040e070b650b0744201d4006210110404c01800b80c840e094 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 569761816 1250 569760566 569760571
    0x4020a0522030f08072a1a130902041d06010804120309050a03020106140a03080f0f071b060323180a0c081b101205150402130303020d0f080f 62
    0x84034000d15194032a9240810b094020720155844c074800710300d003000e0000b008002d10700c80380821300c0350382c40d5032601006004031a840d10403200c2c504004004900240c039003004031103940310072481d10401c2907200d92042c0700941040c05821900f2029910440000c10844041c030301a5071f058641080070380d03484c2d80f071915200113151924205a10f03144000b00181b402c00411030103503c660000b0440c9130800342880e6280c90800b480303a200f94120341d8108041009081100c00440040262554806904030340c6032351403080c20401009010248107110921002c0084107041d1001a5018020400c24000074403c5c0c210031600316070740f54003071030100c0e548080c580c103441008082d40042d1440c0001e582c82ea8149900030740e0020f101900072652900003c03003d5130200f010381c3d0045503480c1c00245041801484e4000e40721b42c20896964840114040c42e149240b14084c0650050040d5641d803112100030200d02d07403611040f801351040102c11050103004107200410880103683c1c4070855599181407070b01420b000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 569763066 1250 569761816 569761867
    0x608072102061204060b1002010902090f040c050d0c050a121e030207091508060f1009020a050906041e0b04180b0409020409051609020a080f0702100c020109020f04020a05 75
    0xc00c104050004070b180104e100e50b006480000d1030071842070a000025101c0c0b40d03500700f1645080c00c01001a0303502560a50001d540d41c929244590f0b403441d0409024030b0315003089522031300c04000b043c10040c2e0004100f0580d102604c02c42c00d160340c0e801180e991107800d541300a00b1044a140c05c11960340764030401800050091048801c9183d0f6840844100e80d865041c11088a40500052207503010411103a9001058094003049074074288890319500d45450090b408002e0300000c0e412000e80c45942610103200d0000c00a60b601c5644100710258801001c08a08141c0d070320040019500c20000140c0d01120202010f40d001c1a010080e00c070700902c440c0d1052680555188103a0f0056182c520039005064400c1d0000d042d0701040e0142000402c04660015802e07500400141224503401071a46801200909403944540c88400081c3e00300460082086a05490414600c0c242641500a00c824a000341c039200710300b800d9641800144d108031620580461010003c00904191000301d0f00c030759000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 569764316 1250 569763066 569763079
    0x6060b0306011e0c02040f0905151e040c050a060c060b100e0d0305070f08090a090b0d02010f110f1c0509030d0c0804030f05100f141b07051e010608072102 68
    0x2201d900240c211241044a1f207038096031000c0c9071041100c1006401b5028a9800c901314540c50308a03402e03210705010013125031a54200c1c4001c03404101c1800040c00217800000d01d01c500042d2070301e9004007559142c080c140c07074041c2094448840390401c80c1c060202c6034215501c035070303a0b10f130004113020000304d03003080840422104021b080041104e0180041003076101c0c1c7d90b00c6a60784000c1c0c0400007042c2242d04029441c902c0c010300d8400c0c541d078120b4036650595080c01c000401c2070b600002a103421134640182503043c000c1040f1501c840714080f601003c01460301110347e120b034100306c400722030501406202e0398041c0c0c007504041d8440b90250003044880703072144040b18a41500d0369507100780300c1d124032011600355101c0c00421044d0310043c01001c1010b000e0700410469030b1003117a440c03845240702a04401455249981400341c40190308219015030350088222690308004030f20a08031060b01d4000c201c01540303403807004100b00d000461560300b10340610211520800c030406009500080207001241d200c1d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 569765566 1250 569764316 569764337
    0x40b040b1005120307030206090d12050a09080d0504030f0e130f09080d0203191103270d080f0105100512060d0c2603040f12060e06040503030406060b0306011e 70
    0x20b43e01030029440e9000c6501854a0710642d240103841c080c400b805500440e0802a80801c046500a0074503074a134411a2000c10a44c4843c0c44030030061070010006003d031000020500c0020139240c20070780c002e500c603642d002000c80321228100c5001240f58000795000308061141402d81005e60807000101610308000541035140c0d60b100b15280d0f00149945100e150003104000e06502c00c085c0903061340000b1001845043c9020001c400148402007082c110425401c180041c913f0000c2d072042c41080c00c2e503084881e1245030050207400d5070421140301d00f01844410000c00c1c5c0703003801c1c20a03d11301e008940300c040c00c0c003075403104141e005034004003d01e0300308800c0b81104000c16201c8905400400c07006e95000740e803203040c2c062200800400c0c0c100d00040d5000300010010980400070610880700c3c41400c5402c3c0c143c20b0701d400d2025002c011400e414034032601050105218001c001140298480d04040203480d9070782048000078007003281c40601048240d00c14032100f608680c00d0b480c909245241003840e82 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 569766816 1250 569765566 569765569
    0x503121e0c0a11040c140c150907140f010c03210f060501110d02070501030b04290319053d0f06050303091302160c0602061509040b040b1005 62
    0x80c0c000880001455100e084110b0034041d01040d0100640303030949040c0510f000104014168803586191070210075000904101000403e10001480103e4000c4c042c40505040d91303070980d140300601a914442d050b810740e50a851919070000902520180c43e02c8031400c200c0c1e10180c4150207848148055842041d02401d500c0040380300b0007001047c500c9000540c0b034200b1000611a0803150601d424950200c85c0680e100c640004800048980c2447d0208004205001040103050740503544000e6024144480d0b08908800700b60b0080312500342d0071594280707a98103c1c0e100d0108090005001d60708104082d0444400011440004480d0041c4180299406000800c43c4840542c9501540ca982d04060700f090419402964010301046000b5400c0540410000b04241548902d000c40f85a0020301409940303041301921840320b4001e800395048030b59800c806915400c00b02c0f9209003038a4919160005841d011035094010383d001540c181c01a0350340e50314241d885001601c83d201d1409150303c0012035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 569768066 1250 569766816 569766877
    0x130c0b030403030203220203060c0a090305010f0b0f010819090303180c030209010f230102190b060415080307060c021c0203040f08010507020a150908030a09020910050312 75
    0x1140b1990780160740307140040c2440003280f0088221108030b0086004400035960000da040d4101c0e80d26080c051307443c03030340760000e4601e614503520040055003032202d40b40c540540e1350303c400e030103040035200180c112100b103004481406c01100c08520042840e412610a081c00d0790000000c02c1c402c0c2000107140440d0030014003055112502100d041007441804d02c114288461002d0040105a8266001d54206049400400c0c03080c10101c2d241020101740d240e071a07201f0008520005060580c0c10500c00050900080403a4111000c0e8016810400c400c1181c0c0314030401402160b20140c007550521300b01c0e50380e44000d070490768071101c210303c1100718100310088261423100504400b9001190b0301d0340391142c030081c4c40f2600c0e4402c4031540d02d08010400c03060340100f00c0000c4154880580100c0c110910081d8000700221480540021340100800c50580c4d025403101440074000c58a080305599201c0c00d182081440b4050031317401d50880144aa20820554043c00318580d4241010b03038421700300c00c0071203031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 569769316 1250 569768066 569768071
    0x4020403020616030e1f1707020309190e0f011a04030206040612110406020106030b0a090512131e0303120e070501120f050c07120903080702060c011404110126130c0b03 74
    0xc5400560f030002e280e007024007840078102134011f242c441c0c6843c0c0d2019403a03004024030707540140300f0b45680380c07146441410038001410700755800803a141400584082613080034060364004800c21160784c03282c00d050005850480794002d1089191604180c01110903d102c540a00303401d03511400c03481500ca1815007d0809000c007a800000ca091950600a40e86003000c0c0005d20001d01e8160400013184010404251075084c8918070381c5c1d501c00c41402444148041c1d0b01400710300c180e06c0b5042c00c200c0c0000c241c5000300c9010340d40368000308202c2800b00040350344091540246600c11542008030394028009803420220800c000200589246900000c0d90130460309160003440000d651020003942e42c3c031405a68003a407614032071990840d50341407002c0c4122000a407150380c0118031280b525000750071501641c1030300c115600303450a2a1034004d0243d15612300030341c08a002075003400841042071450030a0021108030b184802c2e00e07100024440815600003d070380702896000c02040c1c0741c00c3d00c1d00460 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 569770566 1250 569769316 569769349
    0x50d2f01020c0706050f030105010516050a06090c080607081816180617031c0207050a0311010f0209061b15130b0114010206061e0a06020a0b0604020403020616030e 72
    0x40c1d50b200110350340c5040821580045050200034003000520f4465001aa81920401c1c01e04a07a00e105101c41c00d508030195850040445c13092080e1401005200c2c4c106400b0300340b08460480030b02c0c0e00d032203030517460b80021611311002901450000c0c0001420710824040100d9503015611180d82c6000704c400052540d07000b403032820381481003841d40103030a803203200300408001902022202880300d01030b40b2482007000301010403002c1503101c55800c01c1d6074111849107a04c241118603c8140d0714016004406940302c5810712351819941c01c1401503039000f11450080d009020f1071902100700b00c030b000c015207c141201c5462040c1c00303c03010364107100b03035803903025100311050000028400d02e000c81c50040140c02c081c543d00307022003015400740d0b000134016800c01c1c41210242c1c134810746964000e52200103005100e50005401000150340e64011903986031141c000d00d110207581e07450500380001c1e441107102c000c2d0442410014072840401d2601503120441c42494206801c1c2123400c0054841c60b1a500c009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 569771816 1250 569770566 569770571
    0xc0b04110f04060602011e0204050102030f03060a1205060a05060f030a02090415060b07120504030206030109021605120c15130201050307051303060f051f14030309130c140304050d2f01 81
    0x1f0307003503402014000d025031074800c000350319141c10000004d4403802280025000d07071801001103a11561650030840240500c01e0140c4500c0742c282c104165248010b0710780a90b4940303030030301149550030040004091711401400030001c0200300c0e400e00c21a460000c0c0203030b58403000240c4044003504036016090040800007031282c1c6400181c2000407644590035204818003008000030401a01d51206480c111001c9910044c0c07251044600001d510000e804018414050419850000304144001e007001d058031904540715002c0c41000604c04d005c058801003100000c0d01985001984a00b00540e4003940c0307490100d060941040e0301e40d00c2c0600319002101c42540311801701c034070440c1c41d100c1d003940949407204c801c500306c600c3c82d44215aa0b116024003041802170a0707041620b500c0c10030840b0103800e006811002d403d82c0000c810402050707142d941e00300103800c0300b04420383e02c20b000050303d000d141c0000c00340144d84420b00050307800d0030810407281040001059100c480c032000c885410015180031001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 569773066 1250 569771816 569771831
    0xf02060315180f011a0c010606053f04050a06091101120516050c030708030408070b100311011b050d08041101030905070b091c060e0106060c0b04110f0406060201 71
    0x1084204000000d240799010680310401070a83e8084800c3e50441c0c010b044440b500c0202d403143d5050b1841030306030154a07582004400200a0746c454010700e03100e1200881d407003555422003440e07030300c0c0e03002d8006446070300425072080310611854185040d0020320075403c440c0310203907964888040e1780802320141c5800350090505403c658202980100e18240c52204200c87d2510300d00e407080021480404130100507000c102e0805900040040700e0039140c04c040866101d14041c6880c0c001b541c44183c0440c1e2044881c00812400005c000a180950340c0c088c030404007000c1d00744011614000341c8a6101d014140e400b14a03404110240710700561584aa6035020552403d414000240d07480d204904c0c1c1098980000003011500201c0d582c8281c8010303d007002d56400c0314200050400c0700301024020b40005403818001081305607807011001c501248020f016003603985c07805581b1109a5400544401ca0440000d000517602200c050000c481c000c0c000083c0c0300d0203101040454950f42c01110240c2c0d5104034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 569774316 1250 569773066 569773069
    0x80d080901050703020c48030d090807170a150903030e060c0f0c030f0309070312051606050901090503031003061a0a0e1b120708130507050d0f02060315 67
    0x100c41d4010710600701980f90294401d030f0b00340d840624181d0580d040405103007403800361044486400c000c1850b0071f20010185180c8980413048024050460720900c148502400014000c251850454640d00040e2481600e0801d40304410744106221402c42d001d003108110014007084803d004000340c14000080100300c0d031402034100c64504c000140c4950000b01002a20041e000445401c0d08600d5405505e99150030380c82d61441c010300c0c16a01840c4004801c00009041c0064004210b90080c000c03511401c1e240c02041d00c141c0300d000e01c03101c2040c10828008003c00d00c10b401c0243c100181034000221100c16848079405c4d60000e8071040041c1024040401c248080b500481500c00000105000708050010001e140560740340300300c960481e2400300080c0300c1101c622214241c64441102d5030b66032403070f515400c0d840810454101c404261183c004c0313405900002000408079074080010071035581081e007002901e81107d60126850104c1c40c4441700142c4512000c2d6012780384040d40010403551500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 569775566 1250 569774316 569774321
    0x1205040b0604140103020303040b0c032808011d01050f0f0d0b0a0f020309190c080d080117160618050406031208180d0f050904092f0108150a080d080901 67
    0x44105854500c603d00501c0907903400302c2200d04560080310b030f55589614044810f4114020710725580c0540010b1000c0e89a02d140c850b1403c40806c00d1607444031036581e00c0300c41640051806c1e02e07240850054200043c03105051a07040d4050b541401818071711802c622078005100e004466604a270803010752810b01c0045011405441d05056040d0070a60461400100c03040c4c2d10380041c0e04801e1003200307200300f030f44c20b000c3c054220300007820130a0180c07800d42440010141c00d0390300a00c0b49035541503a580035030031580400b0441e04031021821544030b007c1444c1180498088421148011161442100020703160380c079845098010342c82141d1030001400c0e032003409441c4a41c010024009c14003000c0c85645803c0c400b180b04940c01c0c0c00c41c182506030000440b01220f8500030ba001c81c0f0b0b0490b02d4081407209000f1084121440e14540a0b034a5a10b40068114107448085106035035021a03039074030102d040c0340c40c0c03418126001400070b4400c0004079550762110340741c400d1f9541410042045041480090b000030b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 569776816 1250 569775566 569775581
    0xc0706090819020906040b1008061801060f0f0207090c0c06060b031e071205130605091911041b0f0906050f09060c0a140c12060702030f07031205040b0604 68
    0x2002501065000c0c00200b11480300900b0001c0c0714042c900b0005140d0f64441e4020351104070b000c3c143c4104107210303800c00340c5102d0045e82c2c00b500c2002214039080307255030082e807014141c0c1c00700d954041d48000c40b034070103844501c0b0030390000045d405143c4011840741410b124150380318800d583c4d185005001401e080044503215008002031f00e03c10000c00c41d03400150008216040a1141244201d40c2daa01c011990b82c06c0c0c030000300d00158144000d10203c030900740d0b8003804c154020001086142c48995080e61b88034045230762079202034903a4962030089846e10909207030303002001e070020815101d12260701c0650f4100040420100e0940c00d0000c9015902120440c09440759080031460320038040c107210030034050900000c0c4030b0400000d000c144a0401d0010b201c04d10f501100c1185003508400f032454603140312040b03250180c3e12891003076079160360000d1220b02403281600a186010409400c90010750f2082c4015028402410380d0b0201c224124480c162080380200f580643c20704006041000f9102c0d003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 569778066 1250 569776816 569776829
    0x11040306051e011a0c01110c0c010c02132307020601060801170c22050c1b0111120603030705030c06070908010903020d05030a0b060d050103050c061315050f0c070609 73
    0x30100b01e4000c1070b00702480b141550002800303141d06a40d000983d045910407041c2c540d0312075007451080710364403201c107029041d5004034005a59502e81c0540c0110303050382e49000080c0d8440c615a1018110b42040c0c0e1105c1600c5e0140340038642180b51750411010005c3d0142e0b101c00059000700c0040114540c003070400c40c003508505e02d203070001c8210b010700340d80d075107800f0840d05201e203040c0302040740007a03403c600540006d42c48000c103120318904044800c403d50008041408000c0006c5050b071081070042c411051a40f51003a04542070888080d81091030410060020b0f4241c07200704210070104070104080c00b00d420b4000024130080c41c01801c000c190b02c3d82584101c2090303042900b036400007600454125100c4205240c555201c1c0e6403108017001070b0500c0b12441380c215200081c00c600145064220354141d80c040e60858403101c504074240025441660728030341580c4107900082c031021400400c294886a02c51410b2802c21080d13455040f41c1c0d512009802c64a6070004100b040204d0b00001c001004244 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 569779316 1250 569778066 569778091
    0xf0b06090118020a050412030e1309150e010603080d020904060b03071e2307020f0933040e0c01020c030f0c0603040606030501150906121104021305041104030605 71
    0x98040c100b500406100302d203480e9607070042003200b5130f0780c894402d650040c00340900c0000351888608016202c4a076122210f03020f1246803003407110901d0140204031840d40c2c8401d9030301603003107420615402410100301d0340a4a549540000001c2806500a0003880040d02c0c0c006a940089800f0802200c0707680d48001640c110a1040042607608511070341b442c000720100340142024110412076514258008840e00302e00d145848130000d038031001c00f9240c505c0c42aa540e6074445010803c01404110868079000100c0f08146135090b483d6903904a0300c441c0004501c90200d17895400002810b6900304541c21b02e0b03e91061441c0e13201980d040201802ca0701c0141e000d00000640180c0107500c0b00c14000201c2e0040341c0010100c0e003001240c1e40140021604100200841552510052240d0f0203620840c9600350400344086030032807a46109200103030b40f20280304c1002c114441440060340100c6448031400d070060000241e240ca490203201211020700b0511030b80c40f41186811801c0341c4014064004540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 569780566 1250 569779316 569779319
    0xb0f040801052d0405150a020706290616020a0e0420011d0a05190608010b0418050c19202a030a060c022a0a2106090f0b060901 56
    0x14407501183c0a00c2c15802c004a0865a403814020725003480c540c42144541130704810844050030035800707080010b124a20a12010104444004003041e02851a9182081ea040300038800e181c0003005150700c81101c0300400441c10240c001032002522540001d1003610810200410007101c894600050400b040d0b1545403050000c00003012154484080013291402441050b015540c1d50034000060200405004090081c6103403003001c0d1881e8815540803031441000801e0151111080d02c0a035048103001c04490402d00003550060080600b021b005051b00f00400d000c0010040b00e64034150301e00d501d44002d1144400c03c0c0e01d0100d001011540101d4006880c012200340700c20300d05040044c2449980303401ca482c5000060b00f0601000d0700100744c50320b40540c180030307950007141001c030240c00c0702141070074a401102d03107021803100d2584141c2e0240c8800c900f40840078182c4201c2041e080a44a00b00b284819030b0740c1d440440e0600c18080d1094441c6400c0a810050b261144a034032034016a00000c055 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 569781816 1250 569780566 569780611
    0x10303170a1e05130f06020406200d182c0604020708030a05040501021c060315050405060f1528080c09070e011e08061806030307020402130b0f04080105 67
    0x6600c48602c0028494071080801c00980c2074441c0207040c00d40240109014603424076180000350300a1013a900810b031004810002c03210501c03510030000c603044015020100c10104101c0b00c1c50707081c500221180e40060b001081ea64425a070440780f40840400704507a108042051010b4020010600386c4540e00401a41c030001e81d40c601529080800c9200101e85e64550b490303d40d0180c05a000701e1f4810280036005036181041c1608080b085a001d40041c40a0301071541104003035a8045901400f164040004102000002c0360026480036070710b902111b80c0070580c000288032990428055071802c90090810600f045183e40150081061000420020303040e0800b0a81c4548010621018010140c1806142c2d03401b804819200c541400d00300682c8038070455028200c60001e0721316502518401e083d10101c2c21782c041006004000080c0190b082202079030800001c3d510110000f01500c04448000074081c0c01800508942140349a00c9038485081031056801c540c2c2c0202070303110084440300850300c034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 569783066 1250 569781816 569781851
    0xb0f0a02100b030d0e1c0818090c0403030806030f032101361e02032d0105060a0309080a030221010b090d0807021509010e04140a0207051005010303170a 67
    0x404a96081003591400d5170000141c8000c07400e41c0f40e840362505103071440104403401d001054500383e44010b40f440ca9010b1814040c010408648036050f030b0f1000c000502c0402d014a05856000d9002002ca030041141c3d02c4049003075400c075031041d40500d40030640c60324038020556190b6000d442043d503025000e0b980c403807101c008040c4c1468811006444808448915112600800e42400920003000008120f4200e064020740c0704482d06807608101c5e0510302102400cd034680408841c2e024128001c3c0c0e401c000070050603a01c2103454a081c155200701000001d00c2500207800a40090340f00180c46845100c03801148008801421000507105801400401e9010042d503840040640c0c0440e204e07070b038618110015208141000c0e41c044941d921051213100d01800400c4441c400781e8803a0795010002051006482c0d1240303141c401c400300000080d48502840d4094146140540c1c01c41c1c4030b0000da58002c1007191801e8000341c0028401142154104003500a02504030391690803c1280c8130011524045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 569784172 1106 569783066 569783083
    0x60608041101030203061f02010b1807080907030b0a0b04021209010501032001080a0902040912020604021f0c02101812060c0806060d020705070b0f0a02100b03 70
    0x410b510900070340b0b00900000d041c1c0300c8500132044201c02ca00d5555006101190350b10081d040842c4d0301d869a009485e08041000e01403410803000060100500500082441c0c0c04070b6400c00000702e4040006503c001014030005005510800140c0031b44105c00c403503c1c80004040074418458010740c400d5049074441d4840400317013024046041081c18050f4103041c00310301c8400000720840d4464110b050b403184010070002d0281541d40c0c1c2c00031695910314110380161702c80420042181030221503161000310180d51300007131300308650b0001e006552100c1b000740a441c0c00040c1d240403d00400780c0c80190440d00c4180b005854039001b012900603042d400075035106060480100c015406040160700442e00030f042c1e280342007a500da024000c1d41c0140400c0765030303101e80c02002030080790a201501000d41d4010201e942c0d04d2000700002c1c03411520120000b103251500d000c0007941daa00249407c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 569604316 569784172 := by
  have h0 := BRFrame.cov_init 569604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 569604316 ≤ n) (h2 : n < 569784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
