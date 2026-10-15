-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3939
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:05.765384+00:00
-- url     : https://prove2.me/submissions/90c645bc-0a0a-4145-90bd-1f5eabc73979

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 708273381 ≤ n < 708453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 708274631 1250 708273381 708273383
    0x303010506041707170a1208010b04031106040302120a0512031009091703090d0e0303070503043b041b14040c0c1a01050a153f020910050408030304140a 67
    0x3d018517113901d0300e0142c0400c1d51250725000e4603420105846246003901d1040080c41003e000780c3c400c100800109650b0301a4056000000304001d262540e00d80004101c0000341100743d40e15004014044200a8100715500010107200c8001d41141380c100c06030b004d00c00c403d06c90a60000c0d19505124100501d10003800324140d544a4615143e041c503c000c140c3c2e0b40400440640451622180440c8500c1c0000070361304c10680c820000c44c900f0341000c0e0381d40c0703000d07048030300032640a61070705048542d40d850b4481e070620310300296242e410517150909000006646201030104550800704052041141c5010b40c0b010564050314046284031318407108a52803404404041c180707040b05040050440f400b0300c2e65604880f000c450910030300303803203c0c01481241d0800300d000303001c45c07a403040d20855002050156a203035040c844d5031080c40c17122134020500001100348982106540000e81e078480d480c4c06101200403c80070725101c0e05040c01c00703141907070381d101c06440a000704440050001e05c00c10f0030000c5003042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 708275881 1250 708274631 708274649
    0xa0e100e01021210090c02010e0616020f010204080309010305160206010303230301090e060705282601030512131a0f041205010b0d050d210e030c07080303010506041707 74
    0x1813420f9007405198101c2400b0300c01c800b50404043c1d0424510502442d01c810902002409685d110815030340003582c04500002c0550080c0074640100203000e1010b04024206030380910703a2200000f000404940e0020b00700e1030103010310780e0040d0f5000e5001031028152589810700c0c11854490b080191284d001c8580d800300354441c000008210380c481904130002d00c10885045a8842e158480c09888038020f02c0743e0303880803400c02c180000d1034841c0e440582c801d0308000d003003062028110f140c54195190000c48040284010f0400420410000b044418012014104034505201803d05865030a149500c9803101c1c0411711003058440b010044201c43e42000d000b2031242c0e07915500c5150202d04612480c00340e40c1940303440199213440c10042112060b59901601410452010b1034064840c150b204807407019010000038021540c0c100d0f44240c00322003500380000d40d203500c58140130314a020302075004020a6003051004014507140d84041c1c409543e289441c02c0312a2464100ca1460601603038060648 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 708277131 1250 708275881 708275917
    0x31006031103211602041503050f0d0f0e13060e1915180911120304050306010f08060415150b270108150301110c01060e0a0e100e0102 59
    0x4108656440c855010340070350030f450307290300081c1c401d200d0503031056640c280c104420002c00c2020000900c134204960f04c010400149041030720012101000b543e00202c6032503220140d0601d1204d410820404000558079112000c103081107001080da40180c00c0309409020300c020408510a030a402c0140035000c001d04501d110b01d0115082034912215500184001d49486a801c03204816440d1000654500c607910583d02010250f02800800720010280e0342003229010300f08007680ca440c1110410340c05d031f00045807560f08110401d8181141a44801995201807004108400022a134180d1064000c20700b0400000c80e80c4452001d403103118101041b01041c80000720b041540703400074004104440031105650b4070b048800040c01d180c40e5000d2804600007000040c0d03040c1a481c0e4040c8007540180010410104103142110b070754211000248d07003651101002c0c8040300012012a0340b02507041410300c14803401d4441142c60b4003a14801c4194540c031400c110404c0310094044130740003000030507440341c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 708278381 1250 708277131 708277133
    0xf040b030a0204020f12090c241c0b010f0801080a0212150c0a27091503020402180102010b03070605030c030a062301020c04111b070518090c090403170603100603 71
    0x2003980c003081b0b06d51048242000419012140021000020300010704071109015101c1002108103104200346032040e001000710118002030941d1300e5440320300e1960301007881d12071403002404411030094943c00f0072081100400400800040001040fa0103403040b00b03824080d07029160401c0d01804812080ea14241d040c40004046c41e0010300c4600a075a441c90010120b0514002c4c2c103440c1080790308205035400200b84040640c551016108070b150102420301e00380c1e60fa000c507090760010482442d090b905610491503a50302801340c50b102040450103040e150781000b4000d0040e00000e003500c0c0c4450000300c0011724404140c3d2100016144007544142102400e000c1e4598a8030218030351030060143c540140c19608060040c80c1c4000442d070300e294146a4064140c2000c007041004000280c86064400074030764540c01d81600c0d02801d0003075080700520700103881c9441c004a042c4542d002e40020300800c40442d520208400355400c59080d8541c0c6038507948002403400c00d2001002c403200e4a0a40000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 708279631 1250 708278381 708278407
    0x7020a03080906211512060a0c030e010c0e0901080c0604030803070504030f08130b040503071205010207081605010506010c0b060405090721050c030106120f0813030b240f040b030a020402 82
    0x740c82407080c5606a8003144401742800703c15200001500120780c00703603000c141c524401d50000c0c1e00d12000b41c600000c02c1c106040506007902e48075000c1d5404602444d48088182c02d04101541c05005280020101d0500010104016103c1c6110140c02c1100200114400a2142003158021600011504084101c50410010690208440b1801249451f40000e01050003005840884400030041d00129141001001c44011600000c44007950300b000f90100041e455009400c4170704c1104030448002d8624a0280d084840144c00d150600826104400000c1d0103000820f5101d1001c2e01c0c08565500d03903050b207034a003003115080b003040340d00387c900e05405411030420300ca0942801001205c89105540c8103060880314070b40503001c0c41e554030b04002070100d44400d10074142203115840e82071a00d07441d074080c00406859038000710b0700d004000061080c445883d00000d110307140d001d4039040c2c5a401560000b140141c0108400380030f207450b03a802070501c1c0c1c7c0c00e01106003001c1d0090820766540d44115858 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 708280881 1250 708279631 708279697
    0x31d04051015110c0d0203030d0609051b040b180f030d03150f0302060403080a140a0906030e15010e0a09080c03030717040f0605190212010603050a0207020a03080906 73
    0x103558480d4441c0c0521501c0b501c81c000303c481e104a040050504410b1000074401c81d110f440340c0513078151008010010324039105100b4003000b81140d40001070a818094000d182201012107c0c2590010501091140c49494030444542400b41d020000110135401e01281d81541560660b503410700442c60b019000740d03056040203000900c1c0c0c108000c61240c03100040303c500425800003035003000c0b06000503c0081c0e11407000b17050001040c1013150081078a000c4108550f40014054000100c2e400001c02032182c05000e040100301d5110050b1008004c0501c007410b02510510407800906030b075a010841d64122035120020311600488210b17581c94406031465900d41c41139a02030005200d480c00c0f1010340a06001d220300556101803441c000e002c80d45c4030400900f5025145c0990400300d040d04014002041c401002c603514400032842896140c0a000b03030840c1d20082c6100c2116004024200c0140e40d8440e03002d090707035408440b0a44850301000400c44034042c62030300034060700900200f417410300300c48460 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 708282131 1250 708280881 708280889
    0xd05162a03140f070b030c1201060203070c0b040e070c0212070b0306101b0b07021912021213120501021b1c1d0f12011d0c041404031d040510 62
    0x68400d50110b01d21440c0d503031040340fa080e01d2990042002801a4107035000250f030131a00312046d2906220202c0e11459407214203034000400b581c4005807a1042040c240f07603110040c18910074207410300d484c1031950740000000625190421150b1824482107644401144204008220840b800c0c5901d4080c040e40e29031003515440d12841000a00401c41da02c1240c2d0840c0c0158411044d4610050301e80e60107103840000790240781580991051040c03130150722465680254004c11505007507001400d0040d0400044c039080541d2441b08002544000c5800003c9104982200c901c0401010013070030024024041e502000d8180307101c94103610600c910010b45c41003c01518034148012100402080d1440b1101c0c2c400c050344010141141451454600f010021a01010300901c40c0c05804942090844135220340410b00c81c40c0325100d548901800300191100e80d181600c04000d231800c940f05c01c0c01001c40c014001010414500c1001401c030401c4860030000072030242c0184240c2c01c201c0c0d100c1444001d9802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 708283381 1250 708282131 708282143
    0xe01020c010906181106070f0210121a01020705010f110319120b0f0f0105091002010c1103091f0212131a090d15091b0303080601020d05162a03 63
    0x161040000c13400c1206000002d60140310407994208a20074800243c01c544016035048020300c6401c400361b1240741e001e24111940c0c0c2e88240311086108014000c0701c1e41700700000d240b000200d146540a0360001160701c2601c0382404d10551041c0342c484210344440307800d540071405000110311078000855035170344a81c442c2050344810014450030490041103c401c00c40480e07003c005000c00d50514200b2258000c1540b0043c58010701d44400d850200c0d200c1c3c0c0c13040030600c005039903517059101141e81c820f81640c50700402c031b0041c601e0411030707400060312011194403401d100d40d03113600380902c07090080201d141d0304002c0120440e00e50441e84003000740c0c00040e100d40d1440100303d0501c21650046001100d00942c0d00900e0014280d82c0c0783c68110044c4050072408412555452241002c1407415800c07a0350603104125000b03050b410340c07070014090780d405040d960555101841c0541c8454200081c2d071071281610000c50042401d41c100300c495501c01150360f0900c003aa40750f01884076a500c40c00705040d240141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 708284631 1250 708283381 708283391
    0x7030c05120f100911030a0c05090604181103070f03150f0507020a0b0703110f030615092b021302090a050102030406051e2208061e0414010e01020c010906 68
    0x2051040d102c188038004410243c202080020420210741c0c0143d410500450a00411100c4030001c2850800e010005441005505104000514010347c209520090954003844001c030207400d10a20050550b01c0280101c4580041110380d8904002a0008040280d04031026a0780c0c0d0809000f803000e5265031020984c00d14a607802510001c1c082d40b4018003256000700320302e150546078280c2d03668010700050101601c60703004905612910b0054010f07146e841200c2940c90409000304080b603c103205455a03007440602001410b541d03a0142c0d130030340d00111601c0c002840c051003039040f883c108001d4029403102c6405e0601d8261a909e80c0903051001054443c2c0160646500c01aa42c0b8000c40c866000010703000c001c1e2a41035036a022880c03032400100002903042c84001c04d988007440a0420210703400c0001d60801300305141041280300d420080d522030702141c4081e540c41e22a10b680d030040000e040000d40016003030141d174095000d0130383c45480200841d02ca0f42c1c40b4042c940a1f0000c0c40c2c0c2076850b28180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 708285881 1250 708284631 708284659
    0x20906030115020d020a0c0501080901110c0f07050f1c060b06030c071a101e15020102030f0703060b120c0d0c09050f091501030e120d0606031802031b06040807030c05 73
    0x1b442d11101d41c1018540a00130300c1c00303004460b0080c0050000c12155207039401010740d00c2000010300b0b03e01d9000000b81c05443c01d070060103450b0180307640c0b00070b108503601200c14100ea1903509407100b4521480d10030300f881f5a5203007070000203000306e0794075243c00c91400010010158010005802c4452080c040c220300142d050745400360010f8261490b00003100061400c004000c0e50b254171520642042d40e0328401c0555801e4040c0304140c41c6c0c1c03200f10240c3d40000400c2031320000c2e05900c940c82800317400c0420039a03003001d500700418007030301951039001c04e10500400e4600e205901555904d41c0342074000c0c4624580654028030303a0000d032080314009c1818a64014130317441c01950491088814a038181010f0b036480c0011409040c03a80c5080c0038500900c5c000150204500f401040d0201d030380400810203600e4088010b041f502c400d1038129080c20024901d0005940101e2003009012680d440300084002240014035144650346c040702003803155020000400c07140220701000c4030343c21602e07100030344070b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 708287131 1250 708285881 708285883
    0x140d0c02121f02090f0d08040311010216062105090a0b161710030b240a08060406051b040602010b03010509160303080a112a030f040e040501020906030115020d02 71
    0x1200c8403400d1011000b4960040c0095242d0241415000051103001003084a4010480c28094840c0c2030780d078070030005400c0c401d01c2034002e620030384950b082c401400c2c4140355101080d5032591034041c030020007030191381d85000a40c2c141d0795a55129075543c0100458148400b03442d58803604181d0485400710010b001411070303100300300d403564201c640c0d0b00d410130030b10b52120f00ba6a40580060007407075501c06280c404400700b80c1b0001203602c550040e4540b25009900440f1980303140d0b050218852003120103260034850703240301181e41600a0360145010a05858000890419628070040340c070f4144d2000c5800580c00c0d60541128014410540c020001625125080c9890300742800907030140190001c81000003c1c800c5140039800601075000003101e4103501c0821025500c080702103000c0c0038070300310140c0c8001c0f070142038450300b0001503000b1032038802c4181c2c404c01903018a1240417506110b4400040038400c007901218000200208030654079a155026028034403050052000144111030b01002c00c180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 708288381 1250 708287131 708287143
    0xa020a0201080a02090f120f150108070f23010201060b0a02010f050a0e06012303030d05090f0114070f0c0602030108031308070b04030f081e04090e031201060c140d0c0212 75
    0x1e030150075500481b58040c20f004444802a2904030031b48507507045443c50640600c091615841c00d01c41000032540340407061458910103070440c18040440000030054401c0d064946002d0582607400b6241c22100d850040c2c1c01800740340d0001507401000508040b07210781c10751004070454001081002541c5034000301c0c0007240d0a8184000c906d501000c014010020740b9020300031716120408441043c0d41e0b003140485d0558129400000c480b98507601070203000c06040c050b2400c10042c0600070468143c0c0031180d1002010041c00d1101406011800e0074145442042603241060300a0025566940d454400955903884510109100741d50010089a040c82c0400c0c00302c2111007030902c45003440d0a41d22007480303038100e8690882d92160700700700000f190600d031020020082002000103441d185007002c20700503500d4117002c00c3e6542d00200b026400605030b0410342e505441040c40c11661082d6240741440740340020b02e10303011280c428240084030580d40800c3e65485948283c0f00354a00b2807100840c15a40c0c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 708289631 1250 708288381 708288397
    0xc030b03030a0e0307030f0c05040b04020a021b190326040807030204050a0902090a090303050a020a0903110102012007050706080408030a2705011a2709070b0a020a0201080a02 77
    0x90002c01910000a00c10b080c03101d5900401000e0381d0b07560380d036691030404401d400b60003118070408106081050f403616100713000550b402580c040d842e06e60403540003900d0701c41c07020340032540780a040c1d2070003860380360755284075000180c481c01500e4458503401c2111401d012202c4900c0c801c004652495015940e001c207442c121101c4500420310305042d44c2c09c02001d4840240b1204103980d0f070303068000c05030f550b50000f680100308403080003419003840d08005040c2d44005011444103801000181c041680c003199420480e40c011060015082603800104e024106a00072104101e2103d24180d9580c06d40c1c2c4014040507200e2021140711554807841540c800b003044a0142c07000c030341400050342042007600034105500b07442d917222050742074404202300d01c90061202900c03283e41d241a0b103022031003406020b032a6030390100c6102844101c0941104a50341c07203451550a611700d21404038040c400d00308074810103003091003c0252230342c98a01c4025030340d40c41d0360426070000d9010000b24002c298240f003101c1c407103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 708290881 1250 708289631 708289633
    0x40c181b050a0909050a020d0903050705071a07020603060f121b090412110705040608010f1503020d0212030903063c06041830080919060e0609060a0c030b03 69
    0xc0f614001c80580103000050030325900e1502040055000b4500e4400d03003100b6803103038503501e44070134050900a2900c1410b4110a62000850700700c860f010507410241c400c2c11b6811a215941ca03610f22020902800300e41d0f80b12a00602c0b40b20700b040040b400410500202078065182c0482084010104520080e081d41d0242030400c0c1c80a03071001403403081d07420310000d07540003040b144020355070fa0100d012505c2e90340c0005401d0355528580c034070510845c000c0d05018888890f15260103030035074000550310005507000034803484110004001e02103061084c0e8170911030040648406103084c2c2041b0549102e0143c518440061310120a4140c072202c00c40300500070004000f1030b01958500741440001d00400894501030302d2002c1440f80055100c0b110900c0040700304101c8002c96040c02340301c00c814030b50717140c111007480282c000700444d4800004040c2030f03e0f0400181e050085116040c004014402c0d030324000001e005040030020741070000520030b4080d01d07910000b000344403610354045080751b180305006d6500d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 708292131 1250 708290881 708290897
    0x3030f02150103060504020f0a0f050102070803090325031b05101e141b01061a0708090d1a040b0f1e040b04061404030c03020105010614030a05040c181b050a 69
    0xc29003503804a40c0c407d00c06007505a100a050000968921140d4800c00c40c0191303125040c80300d9641403191000a00c1ea10004600701010880041c0d26840080c400d031440148503d00660920350600c000001140c0003206a00710304178241e4107040540d1140201402601100b0404480314802c1c10380c8105080030b10109241e08540781401c4442481d8445e14048a11007403000e0f1140003000c0c111088a1040032000040440c6444107085c010718541c468403883da0418400c03900407804510407558008000c90704050000503503d082e442c00c003954071680e801241c5110800042001c140d09450082001010200700c3e070340d0b0040d2494a180c41140080c00ca907240001280001d60b140c548540c2041c0306e01404103200020b940004140318040340c056000864410641040c10f4084c031a0a002d041c907031070080000020500881c405102c050400d400031075840002409000800e511a00a003104150490841020040e000050302c15180d030007100000d900e00d583c00b000e029100305c0f00d1440316038a500b08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 708293381 1250 708292131 708292133
    0x908060411011115040b130503120a15060e090906130b0a0b03190615120807060f1107062a0507060b0315090c0904050c04021c1503030f02150103 64
    0x100300e001c1000010b042c807441028001d0b11000034004000d41c4c020805400980d4601824200391050025042c2c143e000d0f07244540d64007080c4003004a804131624054194025200d101c044801804818801c2000383c421201c041a40d03a07102c03914019240c021601c0400d41e498620035180c071840c00b03903080d10011054500540009a00841090307100220307400c00103001a500012908254044580c0803111100550364003c1004900c41d43c03005540c203004100707155041004c1e292542044107405032101c20041102410049541c00003007800003900005d0094060000c1d901e44950054241210f0490506210031003000e62451034400780c02640e0340e0400e12011038401524164000303501541d01a80710351013920151001c00580880124010f00c03c09180b0305030f49850f09008095800324032464a02d8240300100d60001810307001544c0c100c50040c0e842c218580c108110f0184014020f200c10f040038510002c0781c00301060700e0100d0b4060f40303800f18032018110080b602e0314202c4c060141d04911400040c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 708294631 1250 708293381 708293393
    0x3030f0b0a060e0d0311030301030501020712020a0308060607060207141606080610030506060f18040b010c02090601050f04320105030c1912050a0c180305030d050601031104090e060709080604 84
    0x102540242031881d4081003401b80b82d421680b09030025600780c2e40001c0c1007810001d641c1c3c1c0c503410000991000c1c0042046555006296520140110744500e83c0810180180912941152005907201201d00c692010081c0926140c0d080500381a2400129400006541d401800418410b007001009201d03841116a4164001c12001e00459007003003041c04564002e000307070b500900003440c0e80030b00e060b200303580d0800300400d0714050740036541048006c202c2280103845e141c29a030b1b04841c00b42005030b1145000002481107020307035400b641003106001e2000704001c41e4107041c40502c513603815009040008003001075883c1c1c80161403200c2600b10400021148800740c603640b0b00040c51034500242c0c0244a6201c4c1c00030307940e003516101c40743e40e6130b0136140380140e80240741c51400c00c00821007600740d00e155464003516800b640d83d0300203405840e140007900a0784a0360050380c8801c1c050900c1c903143d5888140c07e0307006080b103403c584503c0c89074001203900750703000361004412607098400400095540355505 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 708295881 1250 708294631 708294649
    0x18100f02060a0e10091b030602180d03021b032a0411040608160302040b031509010e0c07060b04060e010e010315050103080706180204020318060a0c02030a1d04050403030f0b0a060e 79
    0x1515046c1800314620a8040b50142450045000e16009600c4d000e007460318900b00d55844004d20311450b240b0b900d480000c1e40101c2e14018640b21100f0624003040e085010a05011039654540000001c900c0d90f1054004400e81d005200c2030140e40030464003080c80d011351610b105501886c0042050a00010400380c0e0200e0040d151070398518015040554445058115400c1540d2100d40c5440c0d100c1401c02900707011160600500c00041c403401c10b410701e021030f07050074404c01c80090841ca0302c1d40804003107504c40e50070031002440018a1034040d0760307483e4002c41c9030340c600303010407500003102c045400041c02c41c0b4003403030341640d400c0164603107007404aa55420007422142802407400c405d814442d0050380d40e43c030283d48100700c0018036090b010500314903981003284c0104448103152038180d010b14126800404d03a56075500238100780b00004940c25600c0c450841410180ba440b0341031501700410564140c00442c0c0301001030006202d2404200e08010724440b081c01540002080d070070400301686042068 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 708297131 1250 708295881 708295883
    0x41e150f15083301060c020f0301051029160c06080f0c071b0303030b03150c0f09011b0309030303180b0403080c07050a05070f0509190218100f02060a0e1009 69
    0xa10f0203403070100c214685112000d0f40810041030009000c82c1c1942031407000800d440780100c0c000c011526140000c1e0300b90907140e000da40803410a1a003914113a904419071685a0041c01103803d403505140711041c020303005a598102c4d07200054403800a18107002d403c510740071b41c42c40c103480405995682d0b91035505030020304054502d101c01404106aa04510006a01950190746e012640d00301200a00d450000a84001050308002034104204070340800c0c19103409140d00c5500c9503940ca00800100c3d06000350a410001040034464a6030405801c039030100c0803079109032428071010a0601d091069144550300260003504500c00050029120703551095000071b2190406042c41c0090f110940342c21030458007202c407544465400e20500701041c2800d4000c10040b14141c4e03941c0781c02002c1c1a829414031044140c8a40c0100ba82c0412540151241c14481d4010b0000c2e05600340e01d00005000052251041380503000307090104d150f41441d4045e0004e619980740041680d031200050f000024201928 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 708298381 1250 708297131 708297193
    0x71b08030906072012070609061802040e070e0105040f0b06040f090609020304020303160c170a1104060503030d020307030b0616021206060102032205150a03060815041e150f1508 78
    0x6a40002d012781c8904c0610358003580717550043c2c4c1044d1052008403805000481015030080c00204110b00721442540e054440c140c0e0041190128880303080301903d40100300d182d100001050105010700e4440740c0000321402040180441d42d030340d4080c10b04901c015103001e501500100120502c0d4100f510342c10049500c0307040b201807141e80d00c0b8007070324500c030f0b821a118265401c602450f0003804565600040e100904403410010707185400d001944d00c0c441c9143e07601c031198010001441c1c032030003503010a000d00c40103000c03d55507550b00a04071b29080c4a101c0101d100c0c21310101412550400000c19902c50306040e0020740c60019158a49c060091005060030301c0d26144400105454450000072030417160454003e5464900c10307980541511038a802030b0010b80e200340e92030b1041c843c242d0586608a40c0100441c2c800034107505607a0301c8800b0605c005095080740d01e6a00c000030183c1c0c1c2c401d880410240108100c449000c500e280407036401c03840f0b9440380754008120000780700860118002c40102a807 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 708299631 1250 708298381 708298391
    0xc0b09010903080c0f0d0201091a09031b030c06072001090309052218210210020c0f010e1606180905220614060603040308071b080309060720120706 65
    0x418464684514010560010b03511409d1000401085400120340c0c0003241c5007040192418003c0740d41d8900446007042034003082c40600042c1c3c0e640900c2181c2002c607a51050321001d28089d00060a540524200b08a00840d040e8a2101710754041c0b00303071185070b5407607500c1c040100d28140400802c2c071862801e000240307040f401d0083c143c100d18880d9130440340482209000007c002e041101d146100c0130341415421107030f103094404480d40415000e0f94103071075480060f2500010b5000c585099200c0d440c030f01442d883c00c00c9804000c1e07400101e41c826000c040f040a00d0990f114801200e82c03004c10741d84400105800103082c010981c0a4122907804650003c60b506a082c56052002d00042c0412060b01c010b5651158000701b090f045910301e51009003512a1455824907903401442640700a14a4042012a0001104c050b030420500e5152a400040c2145ca0707003041c0320781a440340810b0fa120750204039098050180465840c00300455203211001030a900880314051030403903400980100c901555407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 708300881 1250 708299631 708299653
    0x100203090402070c0f0503061e25110c01030606050409051b03100e0a0207030f030e0f030a080a0b0109030f12030b0a080d031413020f040e0601120c0b09010903080c 72
    0x80c4054403106025503441d5102e2444c0c21201c20317032001c480d042140039800500800040b494640c09401c058241c407104030096aa41040e0f00c1c2401654070050607031103580c8607003905500d40c040c0c0042491013651050f01e500b1500c00c00107508951162203604085003050204010380c1030158003441d0f10814001d44003a14002c691000c81b01503104407041d4250303559883d0107000340c00d403420712030794001900c44045151a0940d107000d00003440010a070310402d0f468a620764520102403100d12021452380c01101e80b40e024a20014080b5202142d01706501031504030b01350307801d40c4541d07442000c8a4002c031705c1d40f02c440d0440d254450740444404443c0245515511400d8698032524042001072045a01500700c0c031699410023030645502d4003013007030a1900141408048034220750a0003401d54101d80c0c266840605c100407601030504480702210780d001c1c42c0000100700001901c008059071080351688952600d0300800042809210381c0d00340017818020701400050201001040403a02d0703482213840010760 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 708302131 1250 708300881 708300889
    0x20a0605180d050d11030103031b1a0c090301050606090d080a14040b1908040528020603040f0314040b09010e011101050c04090b040908180d1e0b090c03060610020309 73
    0x11480002e000810010b5140107010b114414500503403604105649503500d1518000c2c25658000d035000700014003900341c0000c124644a559400b003040c0c0c210618540740a020342c0c3d441d030f000520003e0195003800c001a140f441c12104503020f040c001440310344240b00c03540356010260480010981441000e81e100f885a69100b00908000c01800c8891b41d42c484e410885d40158514800740c0c941803018981c240000241c0214811240480c00e01807400c806000302090381c145402e000e40070f90801000410b00041c800d54220100b5028060f4403a200d00120a0201c1c0c01035204901c11803030404070900c40070b4601e40c46030b0303503070900e41e10145484c9080008840e4200d0850340300759800803443c84002030800c07151082c0e0041d054212821601005050b1468507a03002074480c48103c58002c10322440f00d0407041e0f0720f5010004455401590410141c403d104a21502101c62030003aa2200d0503280003c140c500001821a280080500500841d4565006011182d00501c1c80305066000c14000480c007600c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 708303381 1250 708302131 708302143
    0x418091b03080d11161101090504020d050a060e09100c3b15160f0f050604020301050c18150c030c0615100804030c060230010e07020a060518 62
    0x10055501d990784a9203c1101411191342040c060039102c0c1c107004103a891041088084c00c1d030342d0040400302c0300301a90801210009156081164001c0c40400d0140600b00d140d0701c01c0c2d10514603407104000e0b032074443c0e4010030104c40c06c4500c011258030010807500c030003103190800c0042c09098145804010010124900120000402504a0819680b0345c0103000301c01080b07050040303010b4400d460700311042c4006003c00d00c5030204042800d07070103115141c10851004032800c041908422018000e5250b80303095600d986080c1c07001d80c403e6081c6400314141201100440b40d412180340648010b8040020911100400052040411160a1007d0720041c03100b40010034600b9800001f40c24280350100c4810150800c0c451442e004000300201c11290a811069164005405080026000b151441c2c200e000c0e100703101c3d03c08403d0742e4000c2c2807014603600e07011303481c0344c0d4100004500060b81c8071481100b064408403581c2c030042c0d014003103d0010130300b140c3c029500039809a10300411a81080e40c4580740c82d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 708304631 1250 708303381 708303383
    0x209060f0a0f09060f0315050d1415060d02091b21100f120519030e0405091c05070510051e0f1b090105091305060a08030418091b03 58
    0x11000041c0340245651126400b401d42615080c26000142010002400c0b4800030705d07210141a0f030782e402200783d080381412402c000c10005003a01c140e900f4914002018200580c054401c0744a14071001c00e001180001b800d00c181006000080c06500316000c01884c0f07035005e040c0191045074416a108002c0150780100801c103608425512102000d00c6030004240c1c004011104104401c24240140d90002261504030303400b0b0b070740304100a049418201d00b001c00f640a1210880d0220b0480d0303007011f070080380360001100704580c00c12280d51200040307902e500c1c520208003905240c115204c00b000e406800549483d6000f43c04449040719520364140032941c0c25103d80002401060840001068001c0319952103040c030300407080e440c1003290320210900040401c055807400e0205803400d6607445681900e4030040001c0410b10084400308404c80281010b07030f51140144204a000f141a8200000f1102207490019012003014040348615000b44420041250b07510310307104001b452020303d824264061 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 708305881 1250 708304631 708304657
    0x307121b0501060f0b03090c01030902010908010c0e1f0c0219030b0a050609090d08060d14030d06050f0a06051c090506040b160305010e0a1e060b04030c080304030b0c070501020906 79
    0x250303003454204541150560b009a011175020002c00c90404000718070250b0f08002801c0200360900240f0060f1000032840c2c201c50160b603e010142e1005035888103110b503222030242c954038084080f0000301c0004602004681010608244503c001030800b420a0758640b8420203044440e280c507a0795803182d440050781e0881140b5111300c1803101c10320b0607001858100205200034100807030701c44800341c207058000300b259104840510900c0203221442d00f0b407800c0c1030843c1d000e4070b9a55940c4a166070040026003e01401003544503902d10413400c0c40c4650405441868407003d04200c6038441c2074181300045400c0c80030b03043c2c0302c5410038000b4034100f04250096108101080704c0f80741c140e8042105181400e032642c01c050820340100890080a01c4d0309400c42c102d40c0e40402c0d09020f0f600c1801c02d2020529060369090719000d00050103100400180082e030303104043e00050b180d501c410150f960b014a000c06000c000d10f05012403c2502c2510042100da440b0b4000175061081c0c0300e00007419131300003c10036490 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 708307131 1250 708305881 708305891
    0x11130216060c0e030a0303020a0507020406080d0e043602030106061709010510060807110615090c0f1b1c030603150c020c0f0d1205070b070c03020307121b0501 70
    0x4120503802500c02c215100d02d00a0701a0324040006955001410806018140c0c002001910180b0610403038080c9038000e081131000c5940c900d0101d5130b60202c2400780000882ca28060140c2d854503006a1180d0141034810342410a010359000c1c1c0ca90380407060a600c8058540a48001a1005c3c00350000800b041c1e1691403404002410a150083c40100400280d07458242040702c12814105500c1c00d8880601c2e0009860b9941d1317000b980e840c14a02c0b40060644265800c02440c20345c0440103440d02c90081e165030440742c0b40e039846854180203445800402c51420b000080e40c03a04001d81c02d1210002401c01c441042540030008900b80b10454102c00c0001c3c0c0303941051040c031501c3c80c00d2908a035250101040361242c154002134855618540082c8200504108580959141c040b00c509241e04607410203c07400c542e80000d0000d03840408201d402e2205a03000130540e60150141c0d03482c00e601a00950700d44912a664071f90f034500c4488862050091101081e501c0354805043d8485140c071030000081c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 708308381 1250 708307131 708307133
    0xc010e0a050d08030f0a0b03070909060f0608030a0f05040e010e090307140105070e010c0b04021507060f020a020c0a06081b0f03070e011202070c0b0706140403030507090e090a11130216 81
    0x1740744070010001c480c00d904115400c201528002220300495208230000243c51446207084c0f005000030b070f15803400c0315040910205400b1000f20051249403516191110300014018007070311603015a21907200a02d42003001000110302c028a40d039801200130054915086c1c05540d000502c60441c019101c1682d501e404003c401030708100900e02c84442402c0101c5103400c25915111410780c02007000340204014001c904070440c0c10b0007907510103039100c40c05007c2401040000030080d0007440b0300c4801441000c9000314581400c15001040d14116a502d400070381e1100151142845864001d2007a0801006500314008000000d1170191000780d960170400340503000014540f5035518419024203104000c01c1c0002401c0d210303010210b80b00c905041d81c550410742004002403406041c4602c0c80c203e840c0c100810503a043d030059115030119100c0d008484d8545454040d0004112000b040c103a01810520700840c0c5075011140074110000c00041102c2c190900d0f1205a03002500140340c100703c00203100f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 708309631 1250 708308381 708308401
    0x2c010c09050d0b06040b01020705150306040f0203040b150a0f1e09020405030a11030703080703170a110708030a09020a09020414060f04060c030306030b0c0403050c030f0c010e0a050d0803 82
    0x980201422581d082400b081c070380780c0b4204038001401d8075205a94030f80302e4540d182d0080c031807007005204c0200310070400241c0d940100300c01c0e0b00c01c541c21741c400c03407416003e0b901d0201c00b07100f40c078080e94002d07007248559501c00c40b12080304054070f140d2a0303000901c1c030000564010a42c20550182c0001004600b00941c0700d0340f489130030000c50308070342c2d02c0a0050100b4070503502c000a0104042c2d411450004907030000c200030134185800c070780016280c2840020500e050641080754030704007a02031120492165500c000c00c600b11280003004920111080194001181250010319008000e1a02c00985082c05900080c0c0385011988612601070b00806c00f0072000d2141d844010304102c00307407010740c9040c0840500301e91600c0340d07000d00750a10140c031815500f807500ca80d1020024507800f00d410002400c0000d00c2d113085401610048800b845203583c090010b0802180c076541e05070360900100011441e0400642d0098440c01c0e08e0303a001200c01c8000201d65840c1c107081000341e8044c02440e507807400e0070f44e584 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 708310881 1250 708309631 708309647
    0x5030319021c020d1515052118071d06010309081204050c01020f070b040b0304050f19023607170f0106080601090e01030b0a0209182d0402042c010c 65
    0x3c0c40b08950004c1c0b040010f0410802c46d040d0103191443d005641d240700c000340790245000103a403c070715004042c04001c0105508520301080149002c11950416074441c0b004001810038003d013039035003402c20041142035000750081d0041c01d00c0349009500700361055081c5640c04004680c00e482590010101c55920350301800b84114202e07504021f0301c00141002c2e00c1c007001c0c0c0f00e03603c6070031f6883c0c000000140900409100c4108503a41e16000da44245c00c04515000101c0d071100717010381c0300e4240c070341c0462468404078408040c100400c920110540745442c0c03030784000d140000c04980601840300c0c50750b0300c15100c180d0024030896810103e9922541030120081074036400074500c80c10310480140038020790b2a12a40b003411607510401b200442c4e62000013442c0a402402e031040e42019071104004440310490361260f00c5001130070308494409122040e182802d100200303109c10083c0c03544004c82c000d810306401488136000101c0d4401d81a15118051032035890070710700e4aa00695440f4003440344903a0104203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 708312131 1250 708310881 708310901
    0xf03150b0702061312051015050108060409030908160906060212121b19080907120f1112030408061501050307031805060106030b010207080a05030319021c020d 70
    0x4809222400c1151003003a62050420180c418103011071110101c110004400c1c0141001c2c40c1d201d9401c040920b171055903a034402c4815401e1078100081700402c404031032180822103605a540222545038681030100920400005400b006102500816440c008124121105c014401d00b4080586000e00340b0342103c58580001c2d046400144110204000300c000391945100700546650b12a181c07400e480c40040b0246245210b6248040380d1034000c5503c03402c14601d03140a0fa00c80c85403682d5450f4000d80c480d00e00b030013030901c0c0d00790500040020900c800354050569100744d081440e060511000103018030003900188103da030001030140f101c01814031005400c40202680429006030f82400070303000380001000c1c0010165184003000d004142803000d03842e581e4002e81610709558562200034040d01e00c09058902501c260f01c400200003500040120340e95800201550030f60703c038031300001039180c03c568411400a07000d01c480e041e5a507030500400104680020700603036a8540c0c0d00320000b940d5074244 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 708313381 1250 708312131 708312161
    0x903060b030f0d141213120915030e0c030601030f0210090605120a0b090a061e1d09070305030d0903030f0b1f1214101208161707030f03 60
    0x25020482c100c001164244105542071002e141e01c0c0108000380240641c5901800c8602c040d07040c01401441540d40594080c01004000c088400307956041d40e2140e050b10510348516004810740818070f1190740401c01445914050f00ca42d0000303c40000e1034014283c0041d0780d08440c952110086190259800a905800c0d050554905180090260003405903160701c0362a010711000160b51401958001e2441c0380300101404510300f05000054000d0503030380070b02041100000c00c10668400282c04101c122207034441568100c11020154031200200944013204c03611035110084001402440542010381d54400c000800308801d040c014162034817120501c444524042072007000780c60300030301c000d449a0040701c0551600d00e11042101c2880e0300b20710f1040524504010014107002d11800180215260315051503510380b12456080d503020301100080000f03104105601c10000e016000b051414010100082c2407580d0090700d020562150104400140301e0b003410100c070a4041c86a4510091080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 708314631 1250 708313381 708313393
    0x71a12041b1a1e04030b07080105090109020403080f1b030a0f14190c03050f0c010605090a1e090f120201020c01050901021905072901030b0a0504030c0f1a01060903060b03 75
    0x3003180b20501ca0540c0c407204800598078180c10074041c500442d0300450303100d403580c1264505250004c2611000380203461054901e20b00004d0500300354000e503015240c00140d010f20341035500075030301000d0380079040714020450200c040c035110b19070a0001c1e055011306600c600220180d40d81c0018003484800e01d4080e18061700b803144c040000fa900d81789000000f007134181815200d5060400ba1094011100c00040c50000041c071042c0380d010642260003240c1c0d0580c1c5103500d075100c1c860004142e55500d020011003082d0356014130103588580d00a944124001d411420303491903243c980c044c1241d2010f181d0720250303400294078401290301344545544204507c00840c00c24403411b0161443c0e4136581100002c00c1000714100e07042c40a21001108081110310203040f0321180040283e11807402440283e49107001d59002880542e014042e052189034560380750100061107640320503511203291010380c0c07181990070320503490000c6002c459020b400c540e100c2d01800d516602d400019654540b4034a406a0014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 708315881 1250 708314631 708314669
    0xd0e010201140a0504170f0c0709020a1e0903051006031103150a0b03030418051009050411211b12030f0f0a02100f0207021f02071a12041b 61
    0x750312260303005100083d000c10305031558145160b02c00d0402c50400703085500010001c074401002c3d0002c0c0040d00c9080140da90841d074078030340c040490040c1c9801b98003190b607501c10515450131043c90400d144816003003078815542caa40301d00303150100c8502c0e030700c03005a91000144207014242020a00c0301c04e00300c00500c08034074900c2581140820291080380c50644405c2401c4103640c0c107000ba5000b0789181c0c450300003103c3e0030181c0c250140c08141c814510860711200003150b40000d0340281d030311550300844c0c0000d000c081d04c018428482100c404901e884211503007102000c4101303109c1c0c011000305825881310401018800c00c034140c9810064581c05a00c20442208125440410745054004600b82c081e11a803243c0d000340d0906c90200030903448580f800c186043c101070151b01a1410030300070b41d0152400150f503000504030501c000e0327282e0050b900c000e1007080701c0c0320700c1c40c19090b0f00b8500d040c2d41ca007089198032000c0380b4004259011a245406c048503103061040116900c001494007109440000000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 708317131 1250 708315881 708315911
    0x911070201021018020d0f03180b180402041d160c03080103061d0609100b040c0203030a050402011e02010f05100302010f08060a21030f032d09060e0d0e010201 70
    0x1001034100d403c0341c4070701c2000400f08040b1313043c40f030040c0c01030301c0400311108500d840610000f80d60303800c501040840e402c00c0d058408103560201924200d044040c5401d40070b484100a9014004c00030f0b501036020840030034440c264143d00e440c40c03030003002011031a040c0114816940c014215004c001c005103402118007095100d14001c4c1100d801c0301c40011b00310182c0d8400405c410001070181081c3c0301e00e00c184107903440e00290054882c00c18210400111000c4401c000c290340300507150400607403003407011a0690351250700083e04148141040100300014146030365503500081c3c01400541d540700100c0700803c00d0390003841c0c0e1018445040000c00390030350340040c16407a4104141010020350000095041c2c44203420503001d003407030001030450003400160400790003414150807000518151200c3c1401c0f1700130302803039021000c0c400d070110f0b81c100c80ea2060700800300140190b0141c0c070f440d54035a50101c0e4052007418030780182c4001030304840b04081c0010301041c809c800c0d002e04583c542091400c883c08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 708318381 1250 708317131 708317143
    0x106020d0903061505062701080f15030a150902190f030803090114040f110a08060606070201030902090705070308010e060f0913061d071a0301050d0305040306060f091107020102 78
    0x54030143c001800303041c2541e000526580c0e0b4110341d821100010310405055040c501d254082c0c1c55181a61180c12280401100e4100b016074504c84c0c010060004903021400304a50500001d0001d070440d0401c2040d62101424075610100c080d0603640e507542c07100c041d4240200007440d0519000c3d580841d640c50001c1418258069200103010342e02e0201c080307140002c0c2034120004044802420b2401ca00b410304213844920141c010865552584824007141401c00700c4810701100c0404d03011706025600c0b181444080d502c01d880c102c0c1096900c840010040c0c2e10210810700510042d0754240d1176100070301c1c02500b080c1041c1c01111b042001d5404000d00c99444019885458a064885000035125840059841511204000c00d458100504000780c0902d9001e043d21214001c0100c9106030b03075550b1150600300c100a2100e071440f604100600960810707054840c0f0417813081c81c0c09071a180c4d0b03c1c0c84550491740f00390440c0c6411600c5000070000d820250203001c80c024801d540705413404084c0d0780041c1d6039032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 708319631 1250 708318381 708318383
    0x140f07050f01200a121223190501030803011805040209062b12080702120d18060f0504150b2b050f1f0c05090d151812090e0109110f1b060106020d0903 66
    0x800f828000b0f4040d12540030014601e410723054080c4044e507140e01d040c102d00e4109000e0380d031081c24a40000200a010340c0a0b8a00864010340501e0064662009129586c7d0b910324248080c1d80d240015641c07442e402c5e01940d56464001d001c4c94072400e940c00c40c000d1600b03034050840011903020f0880c0c10752103d601d40840c1c04154601600042c00d0140001c807201090607010080c2c102c510341001c00d921205160170a40c45036100d04401c1c0e080b43c00b10301c585e20440e860440380e00c0d0800c4036400002c0d600300c04081c40311200929800c801004c140c06a50b51490005003103e00a83d0b07800004412140c030300a007890702005c0d0958401402109040312000304240100101c041c0b098ac0c0d12403140c014402c20380e20000c80c034002d19009001000c80d245140b050503600074000c0b0b559910004494811034031400070101541c5803100da036001e99213007420f603601034402005124085001000030b500c003024000010100c1000240011801001d440c040c02d047c6a8164040c1065401c1072005064596119104a0a403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 708320881 1250 708319631 708319691
    0x11100807021c0c020409033b040207050c0901030c0f05180622020f0405010909090203060f1807060c20091609080307140f07050f01200a1212 62
    0x4030340c0108103d90a0100c594040e410500d0b12404c1c0c403e059000000d56001311100e40004030500003090781c0e0a008940c180800012021400410900e1405400078402f02d0b000760110f84001c2d1030303040010000242a4022100c0d1400e42904001c0800d41000c4100200000c844c91290404185603242074140b004004a01c43d107981205595900400d086500813071080c400304540b40c804001c601da82d59030081c0141c6021503c0d1240001e40341850f801108049503001d0040c2c912903c502031103181008014081040c0300100302c003882c002c030300100003280041015503181115010f0f13906100708035a602500e1001c1c14000703054806400d4840170005c2d070b00300c4190001040ea410341ea100403103841c00d6541220b807003808005060340501c860703010307418295008401912070075800000c00d107554038a144600c3e60060307860024401c0c00e6000d010819519815141c40e072410125000000381000104030048512082c10100042142c2e8031040444810b40145d1081011080c415200c070f01441d0340820405803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 708322131 1250 708320881 708320923
    0x306010e0403120e01060f05060f0706021e0c0105070807030b0f0907090b0f07020f01021c180506190810031106030901021605010b0f06031302130b0d1110080702 71
    0x2c051040740340340b058083d240420440c1d1000c001e0154003805041c0701e04500d07000e00000110f900e103000e00c00c0300d849244240c485807900929941300006034001120314244c0a03c00603810640c0d140c82c1c8000c010761040c00b4000911b603c2c011030701034000d0b20098046010940b4050a000072501c131070783c04c45502c58045419005565035820704640815454110304110803004c101d00c080c01058a01800700c02d8401c40e02250380c190408012a41c8400f41014008500d038180b0721b900301075000300c4030005803e0100c8268888191980c0c04103410368000c0040d50008503001d8015820254099810b80d00700da4284241c035641071841d03d4000e01c10180c0d00019100e0207000010400d503250940c1169103c0c0d842401030703030030300030b050410b05e0082030083e042c3c600522044004141d18030b000001c0301c2c89100d0004200001d10003a409104180c000b0b100c81003c1d480c0c0d240c001800580d01c0d01100500d0b144101a002f0200c84188148000303403484200c5a810304c01110705114115401003600d00120000c00745071702c1c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 708323381 1250 708322131 708322133
    0xb03010e0420041d060726060402040504020a080703240e090307020a08100e03120a090c0e0a09020a050405010b09060c01091a041a0103120c061e020a08010605090306010e04 76
    0x10720000c0a000190703c540340445440e0031a0760042d0303034000183c0c85026202181d407292030544862460060341d481c0340b103e141a10703090b40200d00000d42c108001038801414180c440c00400c00300d07440742a40d60007294040040000240d81401500304000c0072684800ba0065101c2c61226110907030f0080420a04501d000280d02d25810810f0b01d00b0546c0080c42d81c4102d503990810f460b02c594801c00101009030800d200301d14420400012600150348400700d0340320980e10048a60000d00241104407200506c2201c00515001d16003909030081c0d00108000503034842c030f481004505501030f48a107019900308001001514031345810707511107520075202c0c2030340c03009281c0d02c09004001d900d030028080c101103085969001d00c00103407144602c1c46418000901e16000040e448510800d10004101d54216215958000e2190700070260003441074001050f54030a850400a84e140c0380075203404116404240000c825610014150040c02d80c0d0510380d02d04902c03032011940780e00b0140201c00102c0342c840c0200c0c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 708324631 1250 708323381 708323423
    0x30c070201030228020f011404080a021c020706020c01030e1207020a031703061c0c18060b07080c0606010801230604031a010302033f070c0b12010b03010e04 69
    0x41c00c000f01d01403045544c4070b8403461400b0002107510b0f580700107116000407480c440205106100d28407031191042503242c1e440d60380340c0203194081c100780801c50041c071140300b40e905c9003400c45421980b0b454001d441030505000d8020320f0100380034403003410103041c01003c095030b0101084241c03501e51440c20b8150340d80b030f05001040790383d8403551000307115203007804200540c59800700c09140554001c80e07a4003050785002070402d0780302070702c92400360060403d580200100488030b01411503850004801107240b507035500c10071940b60450741080d12121000503c10740700c688188182e541c0b028090904940701d50401070b5813a1005102c2c01e03006100100c0303c150614981d90081a54011544840f0f5040e00780c3c00790f86961074014080c442240240300302c14550001c408084401c03951501e2550030800408c07941c04600c030000c0d2108102c4510f082d0108890000309205a40340c101030610b80d010b26a845600e00f40152220340141c0c0000c02c17914040c4014046140d0f1a40d801c0c0c0c0107170b04540902c030810805074a0f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 708325881 1250 708324631 708324637
    0x16020d080a150302030a0308010504051311040e010e0d090f09060803030c0a05040302090414070801020f07150b0d030507110603190507090b1902120a0f1b06060314160308030c0702010302 82
    0x40d42c90310a2206c68410990f2000d441416500309440c14480c82e10f49240d801d200318900b8130002e18088401901c07040d01c1c1443c0c0d00058170711010000103c0c54003100b1100c0d504000c26002e0701c000045600c3c50600c03200134501410801042c82c20340c1088900d140c003280e9602c03404058080c83c034800c0000368030340e40503110700c0542d005141c00400315480360500303161288180048000911641c0581c0f030000603c41c1041c4243c80e506080c1051172032a224969031360000c01528243e210590030340da0208401305450300c0c0c0206800754880c0c0c803500d07590400d0342000c001000c0703245031251141d40104200100301c0110807001c004080558000700320b9494504050380c1c01d00071504401140d810102c0c001c02c2250041c85034190458158007038910060000011241074491400418040342210064403000c0d407041c1584528410248078a00071444165a40340a8074416803090f5108840000070b11180300c030900000d0068000f01100c0702103035240d9a6a1940e40c08001c00003101c013500031480e90103690080d011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 708327131 1250 708325881 708325883
    0xc08070f060501090e0f1c050903011508010903020601080a0510020d1b030221041e080706020f031b0702030d030f0905070803070b010e090316060b1816020d080a1503 73
    0x81c00701d0761315060780c80c00400078501c6004140c8691a04546130100c081251600c030740fa00202a0520b80c01c10100f510a40d01c40c1d80d0a0350150f60300d800003c5a070b01c2500100c0f0190118800102c0c0f0301c01c031410000e00d443c0c410f8000c1c0c00c098101021460001d840010240c2460350300f00700c0541c1b1501003903e42402414004003442d60300c00b0420311a2034680c1e1682c000c00d000044215070f1a807050402900a0041030111001014048072520101c50a0310034442120514413034209240f40400c0359039100240c1e0000d42c000c5c09200000700038880411650030903244c00c8003d40710fa0500b132081540000307a44000002e40781003410b40c0c40b5444031100c00241c0014001da070300700c811120496070350958255240c1c0640d800760390308800384001151048c0b42039141c41c0182d80d520021030901c1400303030705400b2403041020100da40507a03602a00959072034014000c400b50702a100100510715000b0b60341e641030071740340e400182190440c0307480307400c91a013103c4655001644c1e18000603000c1200c8050f5800b080e240c0d04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 708328381 1250 708327131 708327143
    0x612040b0601171003020a090204141225150f020c040c110d0203190e010909050606090901030f020301421a0a020715050906070c0902031003021f0c08070f 68
    0x10421200c00c04c000800840f0b1080d40d01d100247d43d918402c01c12805140500e0280c80c99000c031404184c80c0c0036403510701c1c40140206a4010300c0c1c10703501c041d6090240c0c0310058018540503004001c1e2030400c0b800c0c01810b9070a0f0415a118442002c1d0003510342201d050361501c144d548003150300c0b1481c4940340c01c24801a0410440b03d002640e03001c040c2d40ea4014100340140308283c1800c40b10091311441c941c2c1035044060310340c0420399041000e807001416005104541006040c000d0500580d1303420405402940150031019103c0700d980181425204a55482081101307110841c42c4038030a41022200020b0b10180a503401c4020f0f000c5c102d00700386456105805922000c0c0d0111060040440140034583d0113800700d51a1a039140c4410320000c0d109420000421400e100038245070603c0401480360303a02c01d601c40c0b22005d44982c2c0c00f00480c2c01c142c641400e4001e4403070b02802182030801c0c85c00709449046415190500f80c440009001400358070005041000200750102000b40f0b01403a40e01c865030001b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 708329631 1250 708328381 708328427
    0x30c0f0803090a0c050a03051507050909040c0e0703050c03010b09060f070c081c021e0a0203100c0e0105090303070303020a021005130c060f27050301090b0105010e0612040b0601 78
    0x2410180c1d985000001502c1e44c2021450024031854444031170000c483e807220190071582402540c0c601c5600c1d0040c0700c41c0034010f08000303400281d5565006148075500c10064120491308042c0c404129041c000c2a8005040c501010311040108034426641110310071108240c0d40c07e220780c0818454054244810145140882c0c880e0401c900711a000003072744d1058080703503045409850b6102c906000c0540943c096045510b020501c214209a00c0c02001d482c0c038102c40000205034046850a6080000c94007101e030746444410510f6401101e600341c020007403a1141c145080714000030303120b00c16900300074145580026248015030083c031190000702c104800800072403400c580c10242c10000c8000480380050300300000304100d4003074103041280785025030745c1c0810445050360417240ca07504150300030030b407116000d00040c0c42e40e0b0034020310324101e1180c0c004180035403400d000948000e10b41540544648418429038140c090341c089055030043d0810300d12503994036804c1c0180ca90440302201549048044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 708330881 1250 708329631 708329641
    0x1c02070b010801111806090f1003050a0501080a020f0d0501061a0a0e060f032413021306020f030d051306090506310206030a15180f05060607030c0f0803 67
    0x900340030390403260307250020311810b07501c042c0030504d070b2003001e61800d00b083c0480251041410701070081e010002d4090310f060001741c05440000c3e28100081540f00000352148200014203806000749401003080f400100100e0100781c0c0090301d8810320311400ea01a0042d003d081051200c2508031030004c04580034500200f1540310b4140c1580c0e403000f8001030200312582c58104041c1000c0e41154100d4510746c848a08603290310750202c84c81108144010f01c0000030403a140515a500401c50211f103030030f40c10050361043e090645d02117000e0b4035840841590400b02c440c6840b850f000c01124400c00c4500340000340c2d80e5600c00c41d09401c3d25901d6001d09102d2030103400304100000050030b140912580300d40802403404024124030008110800f8070030a201c0c80c5403440060030070364040c680040b0801e00218407502801640c188517403940d8003400b8540d40007141c507450680c00b0b21030b002c0b0080c101e0600340418501034003c0f030341c0c034421400001c0030403050110070380901200004070000198000036040d035900740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 708332131 1250 708330881 708330893
    0x5040807030908070311040b0f03030a09080705090f01030803130501110c060a090c09020a0e0306091509070e0711010b0a0b030a0609090f0201032c030a171003081c0207 74
    0x400e100840100e08070690100d1012030014694084980c40403c101200c0e5298013800094204100829004540314a05500c29a4140098480c40c0311903551b000500d442c02200b06c0c034003907907581701031f0080c10744900380002640c41b081950f06694006400568a45820b680d10315181404600502154a0409090703044000003009180014910f400c690b5542c079000703455000c0b0703603001c0c400403c107010800c1c0070400c070000354001d403800c44280d040c0450078100c2d03000401c1c00d207003045034106078a03006003e0454400c80884482c0e6080320080e4000c0c4049410f00f904001c0c010b402800800503c90040b0441d89002e8094025182601d0041c00340c143e050354a40340c1d14040d4105580041c500d5040500108225980d031190240b21030300b201d800451380149070015801071082d660040d03410081610205a2440002e8084600030b407190000c50703460581c880004c00c100683c00e503400408824805000803200c034000000e09494200125a44e66a040e5104103c2c0300c450608030b1080a001117041824400c4c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 708333381 1250 708332131 708332137
    0x130803010905010e01150c12172a16020405100b07050c090718150c0c030812150d0308091617010e0102030906070503060310051f06211e050408 63
    0x1205a00764000c990b03c542c62281005036050350080011440601f01c400f041c03002912442010183c240a080941015241c00c42440112001f04141c4818422a03a1010404441140c28030303200e6116420300c000f00403040840320440f1401783c0302710b84800214881c422205140002811585039103036036201140b51098440f04843c0201e40307d1410000017800a41c014079602290a400260401259041c05803905c914040440361004029080407100000791803441500099406054100d44400340c104142c0021000203125800d4690104ca203002c054452100c4010000d40c1400d0460955540a4285203010750102114804041d0340d14002800a88225514400517000d8000d002054070901403a09074402916401030717940c0308200091250b2300c074902454020301c3c010261036040c2080405001a1082502d0f103103140001e00e0001030351442c050706600018001820411404402c01d0303c5140c43c00303071038680486225150104050a08654042e4038109070804004100a041174100b03858150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 708334631 1250 708333381 708333389
    0x909030e0907081b180607080415030b0f1e030106060f120204081e010905030403030503060f0a030201021c0c021c020a0f0803030105150c0706210905030d0513080301090501 76
    0x600581e0208049034881d21040d803250810340d8803812448039a4030a528158012030711524050070390301418000e65518070042c29020b00900c6941e40340c0b42070108030303c82c400032030640d1418546002e5800d54a80c660140e1912080340840d18103a241d0203001000e8981100c1035425549941317804004103a41d500602c99104120699986501c040e40f202000c404a00c80c41c0181341d0710ba80104040c11000307452001181d500000d0b00000301c4c030b920b640e59aaa107581c020703400880101d440442001200c0c113040340400340406003103806e010001d00d1074001039118400802a0708000c00c400da081b40d20300707024484400c10360354090400030645021100d6840400d5407614200e1161156000c0010ad800700007592406840041000c1c42c0f071a441c29003003280c0144011800030345200e0500c140e606400007441007000820351526001201d1050760001c030340451865003000703001e40ca07042c09480401c200000b998a01480f1742000507203916420b07075081a00c225a1801045c0c0c14000001240320030f10750700a54100c1d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 708335881 1250 708334631 708334639
    0x170a0513090f06050f0f090c160819020a02100806210601080f0d0f0509151204022106040605100f090e010f0507080703050a2c1b130e01060909030e 65
    0x303c1d403124100405540f04010303c1c1d40c4088690345103600c914007150f140d50448001c4130313040e01d00380c82030214030310803900340c881651700f11030210f81c0c0c5090006001d1202c0c0804c19a102410404d400c5a0009610521034a260b40811a0807400125142c64a8540b80520140080151046200400c1e500d070745450902503840a070003400503540749a1030024860480c0ca516441e01740041c0c0803220222582d4101124065101481e4540306080c0040c03070f0010485004142c41740305452900d4014400c2c0070815440c845940e0101164440c2c11400118000381c00650200c030205058480000d8104003041e01d4220200e81c00d8070910005402040b0762000c2c0d09900b0380380081c0410801c103140882210411580f0101040d41c401c00a543c440c03103940000d81c81110356600091b0743c1028140d660380843c4220203008050020032400c0d941c41c008120811240220703003900103000d1069404038016485400c01c45450b40c0e101c0143d171580100c03e410610141032407401c108403c40c01414000c04240040d210280a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 708337131 1250 708335881 708335891
    0x2010633030b1807120e0d110619020c0c030d08070e0a06050301030201030f06090e070602070e0c0901050a02010b03010c03020d0c0806100f14210a0207170a0513090f 73
    0x340e58000d01031900110340c0100031022a5040102100707070600300408140070007062021005070302e680c81c403903207000c241203100504000101803000340044119008403291944190308100e090b00004140c1c0c3d2030300400d4540581c82c0c1c41074400961a0019100e0b0b80c0d1307814065a02d04940644e4402d00341c42c170800545d51025100b20030f0100740298000e19004010000307004100600265000b904a60413100119200003800c6581c0d01205c002ca810700706852245400500c801c01a1981c10840304000c0c05007801e00b1005030401c0c1d02c0710340d114131503540c006045c801c001c205126441d000b0351080740520000b400034403000310002c200500a5200d0b8440c03610440c940410f6600d001d1090a000307200c1c42d0302a1048079500810142a612070f921071259104014007960042c1130306000c2005800007410903a059100e0102040f00a404401d000f0710083e101c1e481404100041400390840014420100c0000e035070701c100d007101c11603443c4140c06280705140f5000c00c00040d440460350000301010361160007041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 708338381 1250 708337131 708337229
    0x206060109090c090b2b0209100207121103250f0b120f09010b031c030c0c0c06180b0c0d030b0a0515030606160b0603070b120f07020106 60
    0x2c1107424410a0304009400407005008810400b80180301c003480b0610120181d242d40c00d0041c564031880d920300d210154001c1109180707401c3c050440303010011a40003418015042100d40301c0109028040a032008102050f812005e840c14011004200740e000204110114031105024500400c0e11990200940c3d40a00060050112007a298890042c0b00c00c0b82e0a600c4003403440c8440b040c00341c06043c0795569a5031451003650100300951100f84414141c056400005801070101c4500d80c840e0804c2c450601d81100016503d240c1242c00c3d00c40c0340c02c0c00d1015403440346030358200d0a540c0c0c0203060074182c0080c0f8a000040005100130451005039402e101b50443c0c0802c1c0500b2027110710620780c0040000d915128610840c0c1d0203540e0021000d4403203400d01003240c081d4000807150b028151010070b1880107104550800f405650041c200310119a0320300310001e101c10610307400c01046404551421030124011074800c0d00034100400c0c03448951030501280c100d104200b00341d0700fa5070341e40c0201c503150010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 708339631 1250 708338381 708338399
    0xb01120512070819050d140f06040501050a030321090317160c031b05010501060504092714011e1409011a0607081303081206010206160309110a060206060109 69
    0x41040b680f0416a83c104442d2482d41c10040003600d8030402444010711800d500101c06200f449403119251010012604100b41e51500649024141c4c03030049060800500650b1114808a01140da040ca80040c841c1c41e1a02c80512082c1b44807190703502c2a04019941d010306602403d4480c010140c038650002c6030301c0d240c2c490500018034109100c041000c00300d0241c046400b07001e610201081c400004450140143c3d502ea0031a0b200f41c0107400440c1d404101400313030428031b00c912011480741e035540d0420000c4541c00b401e03a00c1e4420350300500d26814400a08070742c07c1c0c29044040d2031407007401a00c00849407a42150090400030300555003406904000504080c0140180000d14840441142d500d400c00d4052103043e0b484141d00381c5642c8003c1006e202d0400c0107145610080d0300030030300300e600c03401140744c0242a0480030308a2411584540c0501640300c0040086141d09802d0b810000b070103210b5498450440d45010020ba6803000b00804000f13100358010a440f17108003400da032400c0101e900c440c40c60b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 708340881 1250 708339631 708339637
    0x2010e0c01020d0c14030a0804031e080402332d040303050c071a04150e0a0e09010e0105040f05060c0c060a02090a03060e0c010f0e09150d0b01120512 66
    0x501d00507404450094081401200c4d080d070142c0c020758203900d40409007020280345074030240c000e0340010400f80c00c0200b41a40031102e1030015010b80401080440c001c0c0f40142856030103400648074031408000303036161602c011507901c1101c0b505c031014200c0342c00c15450301650740c12200030701020f01c2195080898a51004002d03d00d011035080045040a0450318110303070a03001108520b2603486410404208000da085140d41102d2402060586e12400e0005114512810510722014030105201d4491b640d43c0380a014001d44000030407401090740c0b8005054050300c4040c410004652801041c03105000c240c14901801c14014000c951040d21034410010b8148550003250100380c01504c0460490b0b58070340c004040d07281c0002c141045454680c0c841c0d0003142c080080107402503020100700c281c1c40d41c1201e51307440700c0c6040b03091416101440f04041444140300038904414010403c40c20006c541e541010b8250950700011040110368450075506840e074504a0240d4441c80b4003810740710800108411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 708342131 1250 708340881 708340903
    0xa021903030e241b0609151303120f021b0606150a0c030f1407030509030c09160c02040603021002010e0c040513060f060e09031b01090807030c051f02090415030804210209100602010e 80
    0xc0e03145070380180824ac1c00106001050980000d800300088401328103100100d1480180800191155040c100c1c10020001c4a2010b102c403c0c0394140b1103500303426000481143c52540505129201d001114003c5a00c0302648241101a24011401e20145079110002d0080d00600380d0480c0c41400c402410081115001c441d0b805401000c0d59449444500c25046101240e1016001058281d26680001c0c14100c40c040d04c540181e564160406000400700260000010300359010442400d0080c03201c1000328000f0380140486449190030071051005500080080c41c004c81c100c48141031070440c59490b41d2000e2541c18500700516503415050206220b00e458603030780501e81030300c0c0040c0c907601034401d00b001410035625400390583e00c1c0d041d0b072201041c0103280100385a0060f5225540720411003100c0030180d5240c5a4050b0203014000034000300100c0b029915003008022494503c400701d502421120f0038025009600c003000c1c440c4180303041e2090390640d4030f40c5e00244001c4c2407100c0081d69440d56105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 708343381 1250 708342131 708342137
    0xf030d06090f020c03043003110606011d15040810060305060a06181116060b0301150510051605010e010203190213090c020a021903030e241b0609151303 67
    0x200401000c254409107480314408081205441644440105254088540c090b00410040b81e1000b103509c0c3d0502c030740d0317901501c2400e18030001c0d41d244d001e08889800a1007042e004186d00d0100d005a6400798003034500406460b0112108040110410b20280215100842d028492000803400a007000d000b02801e980f410348080d1541c40d001c040c10320140c01138200840e001001000488004107444c01d00c00c00c4107000c1c060104260541d031051500b15940c000303c0c80092440c00c001031019030f6401075440300700d452610384a82c03990070110202048804d508802032540d80b80c5128162245011340246100d1000701c441c07004900c0c44070b40400f080c1d12410525442d08200044148484200c580c0808801c11585c41182c51150880c2d001ca03180ca411a1300c50645001d6101c820001c040e40300c041c980d04441c043d200c0c05101c0008620941070076812100700c0340d016501040713044080c0720454100042c0b8003590102d5030a414402d545640300c140d0b184040c2000309403030001441e501c0c0c050141441099040ea = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 708344631 1250 708343381 708343387
    0xd030e060714090111011a1509030309131107050706021e0a0f03180b0702090106032a1206060807030b010e011713020904031d010e09180f030d06090f020c03 69
    0x30402030b15652240301d01c81c1c10b0202d54114138103800d0091091000803071100d400b01c0440d501d407000b0043e01010064600d480490704001c00e04060724040107580c15204140e0307650a040c40c2c00481d01018050b59174a041844070013140520500c00000341d2001210101c0d020b8490140041001c4014942410580c2c0100e511000d81a800142a070030801461f50181c0340c22030804520302c0740c1d202130078002d03480b00d010004041b80d194294a080403006004050905080110030701c000640c000c5010303500c20345041c001010707a581c0d8140c2d0040b00c0114021040000c00c114054507890080d0036450140d03070110000c0d1070300040140950055491217414001612603060b5455040100b490382080100720788001c254500d21000144c69030280c0d00c3c0100e110b0b0301c0c0c540007044200307440d4204203124510181042102c812020003034507442d003801c2d00000d1041000145603280310b16030f4170b480240304900c842440000f5003075401d142c04e5031188090300c0000005101300120b041c00c10381039000701210480c403038000b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 708345881 1250 708344631 708344657
    0x30f07020105131b0f0b070302010b030c330a0f300c02070f0b0306090a091a180703051b120309042705060105090f040b180a02030703050d030e0607 65
    0xb440100d0015204e5082c43c20708607225a004500320000f41c0c00501e00c00306c007141b098101034083c05003960321801900240060110800010a00650340c0307540c105c080c0680e04c01c50b41c441d0404151560800070388100304d540d6540b01100604c0c4400d00c52001b0002042100e083c1c620300301c0b40f0038103400e4841c05040511040c9180b0483c0780100300850602d400d5200301c1800040a0000c9410417005042c41d8603403540f02d151240520105410003010700003485c0c81d0141d14000641d440c232540420403402c500205865403080c45000c9011845004500c491040d20000010460009405500304070400b15605024030400306001c4070f07036140008140c454000340825000fa0800d54003207140340d08180c000c148440030407040c03061000740d5007100365065084040103101710300b003854030309400441c080401845440d02d621151280b4101030705080000550201440c04032200b00084110a6001410307900130a0f603e2403e070303560f22002070044001c03a0520b00c40c480000e00c00b1680c03c3c0b00c2c0301d0b551a01c10780f012038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 708347131 1250 708345881 708345893
    0x5130f03050d0e10060602070b0c030a050f07150605130207030203040e10030c14030105010b1602010807120c020105010312051e03091f09020f04020a05071502090d08030f0702010513 80
    0x40082c0d800290b035641c036212080010404ca04003d80403d80020304241444070080c01c00d1619080b4840e940c4040007940340c80700c0c000040703419040c81d80c03030406e480e038008001c0112103104440010700144000710780300d00a1030352036000c0c50440c0e84c00c459804565105102c820f090340100382020340075820600040100358110f100e10303a840900b0b51020a009502d0f980c80c404000e032283c1000210401c000d020800354282489540d0151850513049070810f280ca01c440301e6901c06070740b4002d0410001c0400714030054000d080c00c008544122005224a080c0f4400090080500b4030054540076003c0344c0080905009004440c0306644400c201c0c00c0d00088540100c0703607a072002c1c00c1401648100c0c4900d001030708030000410102d120310440861b000e4171600411100c00442448180301c4c51041180c0c038405600242100c8505910180c030540807084000c03080020b000d41c0601c45e8010080382440d408001200000790700c9a000c0300942641600c0da690200d00f254422900c403048c0c8042c0c40361140c04110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 708348381 1250 708347131 708347137
    0xd0606090b070809040e1203040605060118032307062c15070f0804030c1401020715030f0b031c120902060d11071406091005060a061103040b07080d05130f0305 70
    0x406000442d04e410080c40144c80c055204076a82e001c0791f004018042041400d0003120f40003042460034102d8881c52905580140d400d5100040000d001607a0b00264010300703281c000b81001e0101c054661190342c07000c0c00780002120300f076100e40c0d140c41c101040d644000c4d4001d01400014000d007004100c400c0180d0301c061140e009600c1a20300c000c4810003400020290001400690300c2030000242c154600707490b81915085441c25035055421a80d424840c0d0280d08000c49190700061801190707280721942c240c0000c2140c4900e55415000d107640d2640f01904490402041c0c00d0f141d912408444042401e4800304d44220f10000d5106d4401c00000b210034031030383c0140050b203080021051812a465480c0401c00380c40c105c0c9000315401010800186e024141705210201c03e40c64424803c5207820000a00403a0440c000c10090183c0c4401441a199082003510003520218803a070f642c0b0006410004401c1d0070040968203090305040000b405815405181d6040e503074000c10403100c1d40044d82d02906d440d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 708349631 1250 708348381 708348397
    0xa030807021012110403060605030a1511040906030b07260c0706020f0d0608010c030905070b0d0e0d020129100309081905030f011a070b15060307050d0606090b0708 72
    0xf010350400307070606514a01c03810b00d82440d42e00a8940c0c131490351030030900b6149070f076009600c6500810714110100340c0d6426111580d0382c8102c03001800d00401d440020150150303810100000b03250405c04400c00c00b002407118002e402903191401c0e0401c42205a0110380c2c001070072500301c1c04c008408101e403002240040d0402c0d5210701005070030700d20720f200c501c046038001c0c481003100c10b43c80c0d040800489500f032081c0b484404080c9020701c40320680b03803200d03951070070380c0e12031224011800038281002d800f040c1d0000341e1403040001643e50203848114024080c0082001c4c0945045049807101e00700e2003c010b0000d40c0010140010000201d0a142680141045407054407008420001e940611808800440c800922503c231b072070300c904081150020203031058000e2240001c12040120b0014403000984100c41d5014000c2d00c6280e503014101d00400f6440c044140e0481d0010040c8011250800042e042420030044108802e83c2d131020100e645441c107200c0e01c0e00250003081b142d40450807c5004040d48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 708350881 1250 708349631 708349637
    0xe0703030f2f03130b040f140d0209041a01150807050a02160801090b160e06030903070506040c06080709050a290d09170705062403070e070e0a0308070210 68
    0xc01e216030b46442800d010052614850f040000c01010400b2100d481002130300030094100d040038100300e00d03150490b4460040c03400300c8801c00030109a540d0b40c440ea10340e05a501600641160030149082d28001e5007600d00610b0b502036500c0045001c1078918140c000003c0d095544002d02d44071481c094460380c1c00700800404502035003e4070003403095007582c00c800905400380005141120b905000442c000c01512080d8450310380610340030140d6200c0324407088500d0455042d507072604c440b041c242c40d5102e800401081341c0144c0f01040180300c40d1500e0f110845040d500ca881880e40e070402c0489411070a8080d45500428000c0140400c01c0e00d115820f042ca11210300340f0403507400901805c05903400c02003c00c480c0e40d4540c00312808001004841504031035110808070700700a860b56a403501c1d03210040c08450794007580d01d81008000c4840f0001c907050000901621155520b501c1154644034040341c0d441e012603417040b10700c1418200404810100d0b5040f040040c00e0a980f41d00304101030001103068420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 708352131 1250 708350881 708350927
    0x307030f0203150907080d0509060708032221020c0d110a032004110a02150415180219080a20130212071b020d03030e0f030301090e0703030f 62
    0x510421480664000c51350b2900529242e40ba040f8410300d41170400c0d415000300401408407a4040d124601507600d0a0b920217102501c030396402031040e4500309045440c040c0244080060740030300140d02076280d001c44841c41200224200d07010284c0c0c5d00e1120280c029000050b0700012408100b803141e00710301c0004010300d0340e64110380d6500c8030303900c603041c0710f8081089041030584400c151030702d40b2410080c91001c030768490404040200107904ca04000c3c04400b0750105242c0040d01b00074810003498000801844100101c60000181e500d040303401340000c900408150003041c4100b0322104a410407a6440401080400101d503940382c5418071030110401490720030b11580c10590780360800e041e444012480300588408c1035038201044500f02030000c0061002c1100d10244062101c000f0505c4603030183c034140c00701482da00e0110f0040c54480480080c90040d0036030b60214402c0400198122180344409000c11840c508002d43c0300c071610b22006000c60764694510f00c02e14043d106006840100c1400341c42 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 708353381 1250 708352131 708352153
    0x1c15050a290d020c0601050324010b07020102010b0d06021e18040209031c08040314030c041712130e060a082812110f0105010f0915030204020d150b07020307030f0203 73
    0xc03e80c1c1020542e400503800180041c411405d08001400e10030118842280380e02646842108c014003045c01001e4825038002203000a69000350024545c91102030300346880b0340020f0402400a41100c101d01e9002c616041210412004401c29101e5402c0c040c00824032907458001003000035403001041075090300680c004070500000c50b8894031043c6459860340c0e0410320781761500500074590140c441144800c01d0042c040102080c006a900742d603511140d00d00344d0394071030307816920380540d03407003460040000094188504411054120121401001d001c0980e072100810014140d10034061a03000e64885010300d01601500b80d19001510800300d0f8441040c80742d030701c03200040c080f01c1900070040380007402c5400405004004080c19880c250b00200819414581e10984400041c452000b0881c0c8a00000f9098400791005c00000e5030f004004568841c40311a000300500f43d441c215540440803d1070001e006d600d00400c84050b1540100a0b001c0541580c0c0c49000070802541c0590701441601040a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 708354631 1250 708353381 708353407
    0x1050f030c0603070e2101050f0903070f030f03140901061a0301140415080f031209010b13110909090a060e060f0a0c170a0f060611030f09061c15050a29 67
    0x842d10904081c0003023801e280905103c0d411083c068a0720380300c0d038810400f0401103a4488110407005906160445281c41c908004502406000010007c0c80c1452400d0003842d400551114003198490100e40c0611178410b2101500b50100340302c0c2c40240e016460600510786480e0f0711540241c1d6494401b01100b40d2125a514900b201d040c00d20103c50703100103010280109003005565008860400074050400c0301c2c00410b00d040c0d03800100c0d120050319442c0d0b4a60480a54054130f030b05400103000300000c0d240c0190359940d54444030744155040d600d03191420304049404910303940308810300c00f0304506070348540045030010185031506c4030030059803150302c0f880e981c0303150310300b43c004e00302c10300c0104180d00d8869400c412210f00398403003c1440103607a03107400406804000d60320ba0502445811351190554408a07a9512500c1314410340c6030f848110309070440e9504c0d408003058581d0300e001c917112281c56400307102401c0046d01454041504d140c1d1541d0300c103001c580c10700180300f2001140c17a04285440c1d141f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 708355881 1250 708354631 708354679
    0x60f0305010f050f33030d12060905070504030f050a080d0b0a08010501050f21030309060702070e070516030e060c0706120513020d08040b04030b01050f030c0603070e 73
    0x3250541d4461060041c00340d00e40c0200b44d0803020841c801421414000c5207805400c2d08103c40074900300c0d245040a000030041c1900181e1514040e043c0c500c0e415024400400750b07a8220400c403c0310b881d0010202e001301451050074490100c41c0c0f00d152030301e070071911071049601c4c881c001103e80e40318030b84d450000228801d015211002049001160089190b000c01c803500c1e61503009180c0c0c90b032400d0010002a0388142403c002d040f01540d102e0542d08900c158440075103603080d4071101a120000c28070030366a800042c520710070303034050b425111840c2e2603007034103840c42c181601d9600020b0000d010042501c0e10001c03028500c0d07807207814414810000036001c51000d820221134040c0f0703600800710800c40301e604911034074654102a0402c106500c3c0810b683c04111941c240007a0003030207900300b50004c00c007520040f203010308440c605d00c2e600e8a41e60f06d84202c00c1003007405503034050b520550686200b4180040d464010000003001c09081d81e4914100721882492140076a520400040041c0d010445815039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 708357131 1250 708355881 708355883
    0xb04060221041202063d030b0429060103021b0a0303020406020706140d0b01110f0a140312010311030a170901021e07050f0103090615030b010603110409050901060f03 73
    0x303903004900d0541401c0c8200341c00c0b40c00031015501700e80d0400c4002400b02d011000040c0f50361007040b40240c05c0c02d4000d4003001c01040d94500c81440604040240000174021070b00c62403107070306e04090151200c00310842504402410010751120240810070b190b000760013501e004941e040c0041103600144c4280c6190049922042e804294001790030300000794103110788800742c2050b081001e140c078500f0b03c005090744503001283c0300280c7e13502c40400840e84034401c1100d10100203401c88603121804409140c480c00e440030100c0394092120909211040040140d81180e10740c40035080aa0386941c42d40321510310002c4080b681405000c206000155490340001e41604500d0801d6841c0e05030703040060701d440c40486a5441c1c80e8a61141c910003500c0001d45034007603c0003030b9410a224800440180c002d440344017401000c150400515080e5001c1c06215042140e00401100003141d03039481c01981200d401c000b1440b00701c1000c11007444600d41d150070a90b00802e80d02e000080b5a41da9949a4000c01a1a00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 708358381 1250 708357131 708357187
    0x120a0b06090a02180d050f071e050901050102030703030504051c12060503071212050f0f0a030b120a0f0f050304081f1109091302061c050901060807030b040602 70
    0x900c12142800340758264007002e816411450040c41c0f03040703542050303d9420054485c221110301c58007040301c20300c05e907a441304400b030480d039016440744581e01e03502c0e801040406004090b0640000d0f14507000f6085412a00c068001c6c51511303a86450440240000920070b40c0c1d10301c6042e8100c080e00c8225140d0806006e025640c00c41500304000c2d100c41a01c1d299844240f03c1d61140100b840031a42064110b101c0c240d04c100004880d0340348031420750b031a00070090310342d02c180c40200701018400c2d0f0b1840281a0842c09940400c488000403080214884800c9a00811940064074020000d00c00007214406140507010900d0909039551380c00c0d145911580000280c1d40101c20000b442c6c48850602e000f0003070749048244004180e40a052141d409410300c664807515421011414015103a003c5540054000e402145c0d0b46100c501c070303c8070703190401601d00080c502c0c04000800c0c0200602c1000103440b5540040c02000e451500c8060768100085d1003540c0140d030070044008592940e078a20484242d01030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 708359631 1250 708358381 708358403
    0xa0e0c0a0815010206070f09050303030a320a09020102031b03041508061e2e140c43060f1e03020c0a0501060b0706050105061c0b120a 59
    0xc10050804501070301c1086000030a01140341c0e80c0c0e8000c01d0296010019240102464841490840f03220213507600407074160000000340021816550080200ca240020b000c20400c21001c05011000000b450350780810b0041d540032440d007844070303084000074500510484c0d040420150b0840c2c0740008101c0080e0190380000350421901034000381d030030949040c600300104c45207070400c0410b96588121201c0c0d0518010380b921120940e07600040300c90110030100f803ea0400b00030340200303003c0c1c2030110402000b25590880e01852504980e003250030503180722001d41130132031a000a0320841c81d201901d41100e5804c84a490b14250324420b91150503c0c090b2501182c0540381c83c0001d010b0f03580c4075004004001c0920101e041840b0750314403180c0c02552030715005035211240e0300c002d41003140501d40203004d5400c2c03c0e000a040400c10000c0c0c04028000d03042001240d0380e40041098511070707681d204031641144007a075100340c4115880380714850006000c00514000c1c030742165042522800c405c4520305081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 708360881 1250 708359631 708359647
    0x504060e01050f091501030b0a120b0711030a0c0807020301090f1104110313020f0a05040e0304080c0a0305060406050621030a030b04180807020301060f0e0108100204120209060a0e0c 80
    0xc001c10324800002d130744000381ca082610540208200c00c0d1100360525131a2000440143c651112200003001021441049101145860702c0403c0040d00e1500000d130030712200c030007510008411070b84a0300300c2d921000454000b07656142d9107a00444010781e4155607805070403020550340c0d212101407503c00c140c0ca50604172410200001c0710b00701318031440203507001e02c100316000c0d4030741040340d500f6501161200b03031340ba0036034001400c004904e0f04041d8000e400e010080340c007402c00101030010341d45100103460402c200101408606200c61001030107580c031200102e40440e001d9480700b038202c00007409404984042e103032003a6002c120400344003003a600000d075210905038103101c0d41c0c0001000b214203201c040a034515440c10005000e2002c3d103110b01c005802c00866800754011402801c440c07108210455071406044407110091041001c503016011103c102c40010388210f030705a450b003580031079240140e030302404540034005103455000205114003084c031106001a081c4035000009043d580c1d2040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 708362131 1250 708360881 708360889
    0xc040803160605090304030b18010b19240507140c1801030b060103050c1b01020909070905010210050f07030b13050411040e060c04171e2b02070504150504060e0105 72
    0x4020003c3d101174009000c00d00c0040c1c000c24841d90440c06040303240e1420317041102018010480c40c4081a80000d41d4458128590086082c01702180c4010110380c3c080e03011002c01c038810b69401c45210340040c1c408c00c208000190103c081091080c80c0300102c42051400c00007182e1072200005600f520200400700400404c0003422821340e00160a00c6c00f07001c0ca0516150341a880e00a200b0411700a0701c1c0d13150001c100d80000d42c181c80450600420b40002030a08660140c0340791014001c01d4014040c1c00e50050030040c3d107004180c0200500e10109045541d0300030210024034440d00b80c19032009002034030200100745070013006d01541c003c02c030100000074980c04010407101d88028082c4190411410040801c107141c3c251812112075089880c44203501e04202c0d41840ca506060b01302d49291010812100c3c1800a01c400c0c1c060f00c2550250f03210070b00189040741103241d411000d80140c1c840682800f040c28641c0050491a2004502c0e0104644500000b800d4403e240c00041010f881c0800411103454 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 708363381 1250 708362131 708362141
    0x1501030f140f0d0509150d0902121203070309150509070806010f0b180a030b100911390d0c0c060315030803061804080a0f0f050a03050c0408031606 65
    0x100a6004041c504160900152103040d4400b51509002c4003040032541a1070f86d21000300b034034200710b441c2c0c0e0391039080d04140300c0240050070040e409038403940c025000405c4005110380c55204010156429507907900001c0b00034042c0c1a40c01c03207440481100900c031321803050103200e0107034000402401d03c0780c2c00c0202651030b04c18140d0204041d039005480800c10001705c4000c03100c25009042c1400c680800301d4000c104410031581c07000b03020300042410003e48140380c1080805494900742c2c00d21240754069200300340c90154810040c8011810f4440c82081171880c400c8a4511071044440c003080c1780800c003441d0800c0740d40f41c481004500078280e58010402050f0a0401410082c20f0030421498041382c4010404564000106a8140003010548035550701c0220941c045a103c85031580b403626150141d800e401c000c54590104000c038071884002c501032100740c0c40d0b52500c0ea5801c0d0030400108800c80140c0006032034090044810040400d4400d020700007040302281d0752851040c400018035081040398 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 708364631 1250 708363381 708363413
    0x5060d0e1903170702031617040b0a1d0105130e0a0b030f012316080712020f1209070b03130606120c0f0b0c06061005090306100504110702211501030f 66
    0x1b400410401c2080141101003024803904480b1400300c919141d06101c4d82440341340c2080c2c01411002c104140740e1507000700b600c860105c000c403900315611090001034455002d000082c80420740784e024140140c1c0304100076268000c0e40b0010100711a440710f07010a0800c030504501c2d103e20f0351540c0e103c20112503400050010300101c0810f01f00a46010b0401606004145000004000c80300e00800c1c800303886072034042110315042c80d04641e02c801c004c482c0402e41d40403010603602c14541c0f2000580500010550404980c42c0c1c401f0b0307030724644d5442d003500c18105603200b0458003e5034603100464600070840001c00b00718441d48205200c141001071b2203c003201c0e164000c005120042205d0050f0500104429802010a1f20450110208100e007511980107062a10342c0611886082152a414401a0b401280d005950030488101c60114200080c85524006500710303211446d102c11070441e00244034038524130441074441800c01d005484152803001e03801600c441030340340b002c80103101c000c684a2600c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 708365881 1250 708364631 708364633
    0xf1107020604050409030c080a020c0f0f09160306090203010803180a0825270e010227123315131104080a05100605060d0e1903170702 59
    0x424150300048451045010301c3c0e01a0b600c615425041500030003c114090364804900f0b51070728000b0360700965500080886d1807042c90b18142a0000382818082d0410600307019094520130303580e26000181c042040e58180080640d2000c1c000b42e0024644017541c06044034902540d940d9000c68080b42441e6020b000340c920828030401c2c208100c0d400000c9100700c2c03035036169180007204400403414950f10708a80c1300310740050501d003903004056000b101ca4074140d42240e0080101070850070b080e508034043c00100800009603800c0140c007092900c90311001050008240c2c20070389034620703107882c00c10f00e40034142507640341800415100c0b070b0580503207103024041c4120500c040f440d00c40c1d00d10300c2051800d08000c0c0268039a002d001d003c120b458000710282c16403001039640d90707652814000e44d0b80f80ca64505903203074000d85050109080c0395014a1049030b10061a05041403024540c0c903004201108280c55140710783c0344014102c1d0b50802400e841a80662100321802150080403035010000034041011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 708367131 1250 708365881 708365887
    0x20708070f14151c0207080a020604030210020c1509120c070609080d050409021b011a1f09061101060503012c010506090c09030a020a090c0f020303100302090c12010305010f11 77
    0x3d1005a001981d01000390440104240358415050000910406101505843e400108422100d07000a50030b0301a0b403181c0d080b510342c604c030120395008038042e0440c0c0e14543e8101041110f11817284800c3d0320740003000417054854448003c0400b000960013442c00541c03580141c0700c200040c503044102e0700000e0003070402800000481c2070004149102e24019000f01c164041202e410070f8140341920b00800361a54000c205015040c00c07074185030f01206280b14803440e504040c0402c000026000140d03141e1072500c070104540d042020a44a0311316900d40f01c0c1c0c880d96200310000d001e580902074603819031070b4903841500010700031035452541d00071a20707860b10a80c100b405102d2a512100e000b80e500801081c0a039460303008402c00241000030b01e000195000d0080c540c042040c082c40c0d8080c40d22071b5450348403e100000004426030b10b030300040355150403e0034504010809400d01c1040c069100501c1c9078580d14100f8103000350060020280c005881d184c0d907030034010020344460711030742007810600504107007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 708368381 1250 708367131 708367159
    0x120d090b12040803270601080c0f0f0603060102030f1303150506030a150608031803010b010f09260105150102060121110a03020d0602030708013201020708070f14 71
    0x30340700040c00061600000200040b405501152010b05e89070080400300c10b107146404805070307900340030300a03503103180621401c024892030b0501d85c03d04c1d00c800141400c51006841400c100c0740c1d400c02400c140c1980005c01581400d42450001400740c60b45d80c1c0c07111071906056080140001a5201301c0004462610003400840d5500160076130307405600c4540d1202d10002000794002a10141c0d100c3d240c28071000c10078180a2945510005110400350000c1210f801d0300300044800c40e1202c59480040380340d0b408180450903402e03050300e18100f00100d050007a4400e02040c1e0303084800441c2d05a0031015400460045580c1c184041401010202c0880c0000c1039000c114840100064038000c05191071501d017046191501c03116000115001003445411308000c0c10200040d40c008c880c08400a9085400841e42c9a049a10f000008010300341d1465010305c112840c100031615a080c290640c0314100d000903650710304000c036002906018503903003541c902d06030081a1059048610510038015107403420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 708369631 1250 708368381 708368407
    0xc04051f2d020d032f040816031401060b0a050a0309380c09060d0e120d0c090312050d090b0108100b03010522111f0815131a120d090b 59
    0x424070580034545500812403100c49010640704c2d550007c09035020310001e00e0303003000e10b6040a500f240c0c0950188000ca03441c401145080f240940540310f036030181440615192032190024001d04441403c0c000b42c6000030313842c0c032182d8500c40503502c50382040842c03007910b4142150200d030090480c1803401040a043c4010011590300805030014010540440c4011103140e4541282602a17510400c0d500301880c1026080d0321584444911100340342401d418602c00c502c9242c5000032a50007022488400314980d00490310703a409141070000081c1c9400301000031544140c8418002c1500400402c4005444044e41c806d8800058141e40310764588000c00500c0301c0030303d80700701803207120110000c020001883d0488044e00040700141c1c110003070030340149103a0400304001079203032004c0d00c1c0c240140e61005451100e520010301d2a41c0c0290791019000485c604a80000840d0310048001032540b07050701021a1320107850034a44400c640c016507100400d9034100c003114000d04600300d00341e464680040090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 708370881 1250 708369631 708369671
    0x60905010c0314010b0708040f090b030f0a0b01181d160f0b07081c0501080102040e06040b0a0902030c070203030f04030210050304051b01140705060f0c04051f2d020d03 74
    0x3001e01170b00009500c000c0000c0c4d03204960160045c00c0810200c661603400b800000c00c400582140203201c0d48219001160000994805242d40851424410b81c204003c1c0c000c00c02518901100e956107070340c0907100380e8a050403201d801199600040c032072142c0441c02e07031000000692020309018130311071003400030b840107004659038150000b80341542c5003178012441c0e1a26400d954500c00161822001082100381900248201c2d9a030b001011410703100c0344100303c1200c40311200b2a500c115144410401c11081c0d0300916400700c260780005007841081e40200c4d0456003e01954204008005028000c5140201500345c0941c003901c0c10504529241e0b407010342d10345000a84028545061242515582c40b8066462450f0108103245890b01c00c1c40c5485907440b801a0744141e60520780c02c00080d10f44411f00d069900300c58000304400e03425400004131741d2000d030803240d000f0100705000c0c141c4154039028150401d9031651030303001d43c81108032070700c802800d00c000165070608143c00e00c618100220400c00e10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 708372131 1250 708370881 708370889
    0x10090c09060b040902031806090705040c080f1f05030a062a170402030a081b0601090e070306021305060f04170a0b16210f050105030c1807090909060905010c031401 72
    0x140d4070340b52000c4410308251f5102c46000c052040d81c040001810340800c0502c00c480050303c1c28800d0074001c00b41603510110441d080060011034800040071285102c000e440556035900d01c8117a070315100c0c00401e0501d80840001e0b11050b403a0301d085480380c40c100e06107419006404030612413550040c0e2000380003001302250800110b49500200c0c00f0340d6800d00511040c40e0748118950341e603803a040f01d25026840c10704454006d502407003000156010140c0156042c10101c203000d84601c40c02c45d5103160003500300070401c02003000001c00104d0b4548604005040000303848120711b0310707030346480d4800c2409402c0c1e580594064200602200008180701e00040c0c00144801405040a03c94401141c1384001140000c1d2050b01e082100c1c0b01c07179500e6901842d9442d0903d40f05000070ba80350028555945c200c0c07042160002d1050410521541c8021b1800e1307000340c0b45282c00060342d940c549801c401c2e00c0d60000c060b141c450390b45030003204104091060341c20751030107402c040c007a5480e03401c01940b001c901449 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 708373381 1250 708372131 708372149
    0x160501050a11150f04120201050103030225050303040f030215040501140c010902040c0e040c02060f0a0c050d062c040b07030b0609040e0f0d05040b04060c02040e10090c09060b04 78
    0x303105282014840030025001482c2c80f5a81850070700e2070564505020f03142a03818107080c41c0307180385092042c05400e0680c0d4040e00140040e801f0f0350810032080c42100b9a08a2502111601003540d80d810f100520061143c0541780003014114010014031848540e82c03c213a00508100170080b41e41c02c111f441c0301c9141c42c20301c010b45a241c181681ca026184269000354814500b0500c06031087e0005ea00c502010303000d03641008010310f403110580e60b41c1c00640f114618080814000740c800481a0403810051805162060401540d21820703030a60b6215000030188029564807000400d01820344200341079108203120410707041c503858801c5100c0001c0d0a8008054407060030250b40e4440b0411281c0c101400b92003004442007060405464880030804003c081c00342c940c440296901c21010754081e01d9018425a01d03282c41c0140580c1d00303098000080b0f0300162036158107481e1901c00c0c03000207a0169494400326074040700e480c00503181e5059402003800180791a000f40001001c40c01924281c034200c45c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 708374631 1250 708373381 708373397
    0x3230d0e0f0604050d0b040c09060303050f0a1e020a150c0e24040801020c060a021908061f05030613060f0909110a0b0c060a050417070201141b160501050a 68
    0x4010944030f11581d00103a80020110140300c0401c14a40880e6201314001c109614070540c8a80341601620114032020700011000d0005078076074203c000c0280100c80460400080660a0300c0010b820114a0304007040580c02420406041c0400c2031b401e070300d00c00d1000c5020003203041e4803003001d041c600030300510501920850450704000c2d04541407030141c441c24050341d00d449564403400740307001c3e503ca450501c20700d0081c02c01040c41d000c080e000f41c0e000a1642a00304450118101c0f003140e0303e200c0108201e03400070002081401074112071510002010b52070f99000c2e43d911300007081c801c1c019000500303000303080e290050421612101c0041c010030348100210101303c141b00c074100440e082d000721000d6944400d013200d0028142548100502c0312445010603030300f0036a0b8842000003140c0d8101d070003030420303254035124900c0d15000c24014541644141005000c489000901c4101034100c0d8500c0d001c03500c03800d4601000f401c410080d0090301d007003500309036441500302000200140a000d103d03009010324a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 708375881 1250 708374631 708374659
    0x70503090d170117120d0b33030c040510030228050a0509010e030d03050f010905090a03031d1c2312071403160306120f12020c0a03230d0e 61
    0x5c0c0b00a2108038002c42c0140d44030803034000d44500501814003058460140300d40f0401c0329504040a04a818040921515a61554070726107079a03603000400c1c51820050400000c6803035694403155440e01d04151350016256840c44a0241c580e002c0880c3c0307840d0741c0b00c4a494040d061a4018111160034080380340103529041200016542050180d130002d604d4021119140101c0380d2680c03080b4425004e02c0c0b509450350b40c1e50401c0d4421a2425a0b1240f040c1d0480c86c10800800d00030b801620804001c101c030f0f094802c607282082c0d0b00740b020b810190505003c0320004005210751105400442c072040c01140d2000100c09041c80d102445030016009100500500180041c0d0081b840c240101024500c40c2d036603460449500a000840c0400c1140401d10709034000c01c440380c41c2003001c0114de50205000240a026403601040b070b4450541d280118454003009104035140d01c0940d00c02180f05100040c000320b904444440400418994007140c0c1d03114500c1c3e01400c13135004800d82e02080d0160349a035007a90381 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 708377131 1250 708375881 708375883
    0x111060601050903120d051006142d0c1e010e0601030f080712030e010c0903110409140d09090b0f09070c0507030816020f04020a0e120a0605070503090d170117 70
    0x38014000030b11000c0b074240103031b4145800603071044031a800d5480419071600d1055803441200c40152007180c0e030034000010004002c000010003d03c0c01700d4950419051041c1800256001044500c550307000b03118110002d04d600d0803000300b03100c8800028020218400d07030050741e4100520002d00042e109414032820702c8005030458071426001846200003140d03503207000e0007a101450038030401c2d6113071100138441c0d54400c618490907264010008002c1e00c045404000207010920300945402c0041001200c01050410080c800c48034640c0312044041d04c0d1200c0d2500b01c81c4090340301e0f4011110081030703c4155480c00d20b0b55902030b029080002c030300c4010781005840c00709140c00041c6060000031700c640000c101030b1004920306108480d141c0b01001040240400d80c0249008200442c0312031a20f07030b2691800717500c96858121420111a14210b594641c41c09690041d076003200400d1000060101a81d01448100040c048504180e01700d0f1758040d00c01c03081c8120500c6126403040c08000e4070301e007002e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 708378381 1250 708377131 708377143
    0x22020702191e03150218030d020706020c0604290c06010914181e03310906050f0f18090606010f0201050c03070315030807150b0111060601050903 64
    0x1402404030715050001c18181c024440070790250080d0012001402d0285140c50260b00c400d43e90310084481000c1500c9200501a4000d840700c0c000c40c04038050146100d4500b004980c55040c900d90080c0051031820101070305000c086058117005180811050154415a0005200d02518a140641800c0d0341e03d1450f41c1e1800350301c050300114041d2500010b1044601e4119005012a01008094684403900348680605540c0303071240f080c2c1c000000e520011020098000a0f00911009891520581e40341d658840310503d2840c0380c2d00780384080c0c1c0301c032040c6c4100c0c0001c0c054010303544100b05440c200000503a031040c500b802c252040d480c0c1e81a08040c0d4a0320700d000040350600640302e101a081c070f110b189480d0001140d00078001420058000c2c09103105028040c050100c801d1480d2441d11030311012005041c9041c02c0629154008000100082d2240014201d0f80d00925004c8446040200400180c1d4603070440c00d41044070502d8810098980840c5c4140c02600034241146d50300d55840120741004c0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 708379631 1250 708378381 708378383
    0xe03300706150e130b040b10080a0804060e06070503040510090b1303111c080304020a03050313081c020613020301060807170106080f070b070317070c0204050f06220207 74
    0x24144aa030700d0303107010400000825142c1d01000080541d03141405401105030b1540d01410900d17a0742c0209001c19102201650440f04080b0048100781e01c9444140c43d028250740100c4410781c002504020640e0303c803000c0e01412000b01d4240f4900300d55500d801e40d80b4040d900800f4850f03c0448002c0b02d45034007603603881004100d80105261100d00d64500c1011100a91009489050820300399524a00e000362200480107407034181c1c4440d03465076464840854000034412138000d40c42c440c010020400400282002c1602410b8651540d401c02c3c8401e400c0038040c4c048202440c3c403180404c00e441c3d4020403059441005200e80c207140050300e0000902400b00e540c441c0b0030074015580702042e542442924554a00d80002c000d000070380c0d4440c0141d03a91350b8942e181c6c1003c1e410010092140c010100c00500c0507a00929125081801c41c1075001c240708001e903168404038240c0703100b0008508103070040950100d441e50100c00c007132401101150200c105400c090002c000c0b01f519028111855034141d440745 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 708380881 1250 708379631 708379643
    0x160e030313060c110109050a06030506060705060921070c0b03060a091b090b040501080c1803011d100c020c0112020c03161a04050a0f0203010e16060e033007 69
    0x210ba9500c8024001c10b11881041d41d80000c0766219600c039501072040e40e0104c44001c1e2070703440020324101e8110b000300740141000d81c2c0b1401c10048000410300030006035000d102040050900b40340c00c840e2160b1650b1180c51160098201444a070002c06e41e0f42c1c1c800c2040b2840303c11140c0c1d0300d41c0d0305800203800490781d030042c00e0b50350310703045803080e000f403c078829550301c051640c40c0c00c2052511401082c2140c0103510400e0300203208a00000c060900740c001408508202000c00b17203030340b00c072a80082d00355190000120f03141c030191000110109030801000320030001120040041e079843d0310000b0f44888070203101605211305200109900005641162240030048003643d40700c5610a1204048400c4500241c41224004070f1031190000c010146030f004603030090040c00c480d1125941c2d04040c65800400f6a495569100012082038091104111124034031058004a904000c03002c0c211811000740d0707900a80c480c0f201c00107800640d2110041454021080045991643d102034841e44140540200300d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 708382131 1250 708380881 708380917
    0xa060e0109050d1a0a0b0109050109050d03031d070905040618020109031b080709060302030706021501061d030d020604020907030c12051512031c111806250c0509160e0303 75
    0x1814017107078000000140b00b40c0e01c2c07040b070035030780da004560141072800742c903505c03606440310070340040d000768026904e100d8030518403403d41074003600030f60030300717410781d1000540a48850801c8100718241c0705410301c4d41031040c401c172008801e540000f0900030a5020040025101000701c0c01d44c58803524a420040282200b140d846c992100303404809000c0900c030490003440380400c089408d40c0085046100390415804003810740c3c0c030b4820101e42c3c035483d080c1c0c101003501c89895424860348042c132108688d00c035680c00034903560601d481070101403c0010200410107240c912440700031a801131016800214107080442d007911882d51a0030100340e070b000c1c9141d03c8407030849001040100800942150f0301d0302003c40e80094581c0c1c0a4900b503d0601c8508500040d013045020410030142840020320f41028103100d0804040071102c0c05090b41c240280703c0d100c0c2038154811f0412503050100006002c4c191741c0c4148505100b800401000c201060321000d000741c80400720800c0c0c404005032040115040004e00c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 708383381 1250 708382131 708382141
    0x30703050d230a050702033001090501081f0209060a020a14010b0a1a040909050a0512130612061a120c09010203120a0b1f02010e010b0a050f030a0b10050a060e0109050d1a 75
    0x140d51b00301c0b00d241c00c008c480000240d0030351030321545040764140ea000d44a50a213030b40c540d1140040b038451102c4180c1e82880558440d880702000750001142a4004060b1405c25007496018222a501d40042503810b0144820b16510b540401004441d003906445c59034103005030410509004582054012520300401d06042c4000016003440032400303101074820316041900454554415140d4140e100201d02c501000410b2103800d00006101248800240312034541c04800121005246050a03195010503641523080781140c8003604052132001203850f1400c81c0700040e489006814070108440c03014030005154440c160400d1012641c0104a08950030708000021401c06060344008019882d214001d0307200c000c14031078440d02060040216020030301c0c0104000201e101c80515942500031800c904000500b0710016030300600c50034034003034103407424041403201145e01030344103c0411034490409600c80c3d030051038040c181c82060310300201c103401a05060300301070f030b80c1c0300110030f00312900702085 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 708384631 1250 708383381 708383437
    0x120e01050c120906041211010f0c0203040503010c030605033a03150e0601080c130b0c0d08061c08032205100c050702011e02070503030703050d230a05070203 69
    0x2a01c14044a540e40301d0740a025a5810105d038000c1000e081c03a06d031809258080e0301201d501c000104008240e1040d080d8295040ea42d04400f8180075900108081c005031a0a0081c07001c0503c10341707010040706103400700103559003a01407180c0100710240c03890140303855084590190182c0c01c40c0300c48503c2d0300480000400a1610380c00b0030000d69620070703010907030b150720604c3c042c0104c02c140d5610b80b25072130311041e00100f41e00c08444050b8103c0748043c0040d20f40000000f402031161003001400b4502e00800c005000d5000c02040248a07040c002000d0074100a0304002a45070303500601200e840b503480d601c8480200d281c0c40b10f58502000034135010010000c00090403a18108224003d011110407440f003666140200440240481d01140021a02805510668014075080d10451b01d10a1b55030002c00d0a562120314190002000000c410b102440d03180500c0c0f000d0b40d0200002c58600303d64040004088002424071403080e5200c00104400a10070000e445841c031102140441d01c0301045142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 708385881 1250 708384631 708384637
    0x90b0f090f06070c02090c04050d030809031e042d030809040f060b0c0c030601050d02010e190807090501050105030c0405060304020d201806030706082d060316080706120e01050c 78
    0x480c85214280001174641f144081a202100e0f40504118a101025501517482ca50001c1c6561440d00c020301082004c1e84000c450800d1502d0000000c994460610940854107480c00c400c40320050812040545104c80e0b449560040380d4100c42000d44800c070680004001d00f50281c9490386450801d2004241c4484407001040e400303800d98100c80348413542d03005140e2600000d1252691003000c0080580c050350003858045c180e598000e19041440100380c3e03e071120398001ea086002282c0c801c20091000d18150300c01c0310301400c001d0a142e8118a4001c02c1c640b10b41c0f00d540112400b0704008000b14086448800001c034171039601240b4191312491091085000b500c681c1d00061192504500f031807074540e0300255083c003031003018001e0902141403160941c1d80410180c11680d048081c0c100030b542c028411401c9070720140d8415480b032001c0c100002090f18026100405080001030300320204903224000909204a8650342441c41c074100c41100490b000701640800c00f8141d50a1400300b10003e040c1c0001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 708387131 1250 708385881 708385883
    0x601050a110714011211090402090a0b0f070b0106020616050c01140c1312020603150d0f0305031b091003051005031006060807090e0705090d05030c0c030d03090b0f090f06070c 77
    0x107103001c2517241e10041041c0d40b1104900410868101320010041c1401c0c0c00409039440040d04086860b40d0390b05a01a4980c40814403c0d400365020907550f04100c0503454890042800e0300c0100600c6c1406c10800c1c40024855141c0c4017407100004403076a40107001e4008220900040c0454006844c0101c41d01c0140c0d48018110700103600201d0010a0685600c080d1074206a00640690b05568490b180c098440072614201a0b00c18102c2d01c0b20000143d401e021206440d1081d500e00e0380764204a41407140450110700503008050003030205944a440306080c00d1505801403030041801d80f44e64440c240e00591075000070381c160286410040c03240304190040c00490702d940d916440c050380c0710041250310310441c1c0100d0340501d41180104141c00c0c402c0014100300c2c03c000b80354041942035a6209855940202e18040007038200705650384a900d800d000000d00c1001509040c044c2301c101c5d98031810000c0f00182044100c1d81340c14040f030759400b8204580d02d6945601422a01c207405d21100242c42e142c2400d40c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 708388381 1250 708387131 708387137
    0x6180711010c0212040b0d0e03160c0501090501021005060a0807080304080c0103090201050d09020118181d0c120f0604081305030307020108040b060d02060409020915030f0601050a11071401 83
    0xa086001144005032101d0008140c0b484c65080c10304040c61120543d01000700150364035155800c1c3c0318241c6040c0001d15440101901240d044180e0345042405400c2581c805418425003800c100b24a0b40c000c202044003444a100004a40c2c0d6440c00040142c40c480e0840d0391b06204510011584200002c01003044e02d00308011240c0c2421400011002c0d1450312800a0000d0701c1404214044086908814441c41c414140403000020b01682143d5080299109155844004422000d114a030348101c0114001506099040f42103a00d901d6548101e00003890380901c40850503010056411300c244030a4114410079521181042e043c81d2410f504801c2c02c0e110328884100d40040c07240780000448651a5041e10b031681035540c0c0fa10303802001880108000e42100308a440c0070010790700e6400500190000220040e01d40402e2030900404424104030072001903c10010700400400160845506ca2000d10b0020b4bc0d803038081e030301110849240510228103102c0c0d0800814000f8001e25406900e42e002c2e6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 708389631 1250 708388381 708388391
    0x18080d09060e1b01051b0303070f0f0e060f0d02160501020901020706050403170d09050a0c0810110f091201061d25030b0604030512031b030c0a0302030618071101 71
    0x100a661034001101001d240300020f145251015401007000e445d83c0210201942c0c8842c82001681d41142e004550160010b23450800c080441d680002100d09101010b183c460b02c40714401011400c42e10a00c8500c582507a0041040c04251161b80c0450312101e0302104948a0740c0c00c41d02d800c034040e4010500d05030141c0603204000c0b90b854850800d55003241c0e0880003000041c2101100e450280d44440801d0000544410810300860300801800700200d11071801065030520b4072064500340f006010200c0201c0b07080c04220781c000c0d127248041d14134001801e2403640d55a888076001400e600200c014030007031380d400c00c0300006007101c0c0d10007c0358040c031170603050004623aa0a10943c181c0500410f81e214503c0d40300c2c4080e00301e40d00c40d07808050a8000902450314280c1c40f500c3e00ca280c6804070890300c1c00e00724000304000c101c512039000f801c1c4401c0200303242815420a00000c8907280507049015003003650100016100e80d41d8040141c1506c006000e580302c2c9801d01c0e00b0000e06078480e100010b0203660800b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 708390881 1250 708389631 708389651
    0x40e0a0e0f06061903140703060524130207330203130f1112061f030302150a060909061d1c0c050102121f060201051918080d0906 57
    0x31036000c0e03507000300c0d0000e814107555190800402c1d82e0540c61103040300348030340e102000240e82210500202861600244400c628514041c0180c4000030b00300d1a4105428401e42ea04080011040803214011143c821455807590450300083c05822005000003071a0b02130b030006c4807000310404011a0707490300c1800c044240385071030b8004d07031000340c61501e41c031072150303000001080e040c281c0851514480e1485500e1204460700046040b00ca41880810540140040c0885d05007400307401c0d04840700400412031001d01c0c6803406525500c03184c00d040341d41c184000000c0c9442d10241d1106000e0300c0c00180412911060f42450001450a4900480190301184041c40283e074005010030240031682844404e50034103000481c1c002c0c140c030314121a90742d000c0c044140c010182e201624460b410f0400f001c841c0740312a010710304540d03105a010000303591610051013203000c1001d540c04606a50b0400109452003402d828502c03900c2c0c520006400c0200c0400c801c851050241c01807124140150807c0c0091120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 708392131 1250 708390881 708390883
    0x210504080a08060114030406150308131e050d1b090911090a05060f130f05360d03090f1202010204050a0b0c0316022b0311031608090402070206040e0a0e 67
    0xc040303e9081c061001b0b00000d800511150010b90b82c1c4403086240c4003146550b0f0342d5011550308024280e80c55110400f00c00e000c568804000e01e400c0380080401a0754091803d4003245548240020141c00701d8802c92400001a00001c002c4e001050b0544081108942d1828941e0343c03820807042d603e03c2040f03188085000401d00340900d07400f5035002400e803a00d00d00b91200f0444901740200d80f40c3c10883d10340680300740f4183e891040d903102d01d501c1900d04480410b040401070700c80300720303e40501c0450014095800c00c0031000411401700055030800080090090034000844641010300900c1c0072130700404844503960640150044450a59a890056880d04032111650180036507024480d8002d102c840c0d4121034242010a140c0e0001d00711003241c0c80782010315a82409545074140d502d80c044200301040543c001801a05da80ba0350000c0e45c02d1090f4152041a07809103010042c10049001c1a40f0000350340d1681111070b10b07a0b004000b0380e070391681c0e4103099450090440d0406401468220302002030f45c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 708393381 1250 708392131 708392147
    0x12010806161101060b190f020f060610110a060e0c042003181c170708040b09010f0c0210060f030209041401060b0412060c021903210504080a080601 65
    0x8258801c4255000c00c40d4045a40c80a8181528029926000c00107140840300c0010311003001d800c00d825241d500d0310f41d409462010300520070011540028003004401c540400e040b500540c0c07c031103038140512009003c507040c4802c0e9490039a070b40201c2c2c41e02020843c0b40c3c1d01c04406940307a001610503907100203080100721545119a01102e1450b461090f00303140c0c590000b180e102d010075000080c1c501100d074505103032604641c181e81c2d103040c80d000c5012416410409071481038072180c1da944080d250030b07403000f06a80300141c001031030781e580800450b09910b02034001403000701301c0000400a0224131040250754200d514907515503545400d2001c0341401c611010072055a40242c190b0141b5112599810f0100040701c06e440255503aa002c0810301d009054002c0c4001c0c06c072810701640454030b50504600320740007404000292362003400448046107009001e640c0154040c107182d884407061042400c112801d00c60110f03140c61901040208001004010708410303c0159a081d180356250801503501c82e13 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 708394631 1250 708393381 708393391
    0x21207020304081b0a090627061d18010c0e01080109050108030f030901020904060906050f030c030d0f180e070801140a03060e010e06040c091817090a03080d0212010806 74
    0x600b1940350080300042c00d41c4000c0103000080c0a0b4680e46031b548180b4811101c840c0c02c10b00f102a402d01c90032034410548040d1480225040d0420008141b40c401000020142c048508003521517001c0044e01003c1c00100c2d80503c0f454000c000d009140010704020149550301c4101404500031000104e500490f911826050b218910003c600d0a80808807203031880c3c10080918081d59000c11206d40261071714041d001c0203108081c0b01007002410103007000f6401240d0340740075000b07030f001c8400b10361941da00051410448106047c00001d2880503003080310312403461a0b8150141d5080d800000700c1000710045188500c1023690707030100d56600e5610a2003d2410b01d40342c103900c40c9030b8030000c0c40400c040b41d0280141030401400064803a25851481d414888122001d84454400d060100324403261401a12040242c0e80c00302d50200d4440d640325220740360019a00041d146c03003c28100559280c403510000030b1a04107400c56266243d400e6113030040e601039a2050040590a0000100014000740c204d01032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 708395881 1250 708394631 708394633
    0x140601030c2109020a122402090906061c06030b0708090a050a17040e0708040507080a020319050c090c0d14160f05130b090a1a040308090f090a02120702030408 70
    0x96042c5540d5402a1840310410781c1d004103000c01c00100018580014140988140304640c01a018940c4441286045859014019004000403044d650300c1d45a0303282c1c400002c9480301e40700d14880d503504120b500e0304150100c5481c9003013004420301501c0740a05104d2803a540d601c0d2215a647d00a040d200c5170308050090030740c0e0141da8807000164000040c01780200359113a102d4105903a4a401191700b00b0142e40d4000860340c510140403d000c01480004d0240643d0030081074000d609a010a0b07803190208588059420100e02071030410800303102c90303622034074014050200b905000c4c8069101d5440503a00483d440c0c502907031556041088884644141e2007068072000007022194290b6041c0a500c0700c0108102c1d080010078001c0e504840200302030180d0400355600d800100301030080119481d001042684261010b55030301510582c1104d003078940c050704c42a221030f240d902107402c440c09041c00302e5010305248100110441d89501801c1c40810100c0c03002c115031904c01050742c0700d1256000d10151 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 708397131 1250 708395881 708395927
    0xb090606071707152301060201020c1506060408032a120a08060316150305091c0f050c011805011506020c01030903170403050c120306010f0e0112140601030c 69
    0xc0c20101801c0e0b401d01850718240c0c1010031008100032180e1107005c0c00d0f40141c5003858580e404100b500d00b18050040d0740021440e250054521541d0340500d6078082c542041c90100086098480a040c0e40051080100f2aa01c03110010320740c080c003e00400801061241c0c1c03900c0c402e010130380002c2421a04140450306440c0840c1500c0480302c10b02e0041c8403d0f0180329101840803d00d8a0300713003010042c001c5070002a81c6628900004044d2a000f034203203140750344021901011b200d042c11180307904075036504040e038601003d20415901c81c090508241d98035441c04940c044920b0f0115002e9079030500c0ba0008000c040b0301610020111080c41c01800010707404603181c820b07554002ea1100749014040d00740890070031400c00a40c0409030003140d08600061000c204807a5209013000813645400003040140d0444c42d1010000b000015009020000c10007800014207159018580501c01201030210920000025607050b840b114030a5400c0341c0021b18080581003c9441140300080010440091202e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 708398381 1250 708397131 708397163
    0x105091c0807050a11151e04020319020a15021b040903170901110301031110020d020309090a020f0c0a0201230304060b0102030f12010305070e0103050a1b05060d0b09060607 76
    0x1074a900030484c14004d01041c04079802c8030f0380003085005694805019210710078034040d40390251600c200e4009288201560701400016035021880c08103011080d03c840803a185203000003484000d441d4000c41401d003482d202009404c0d8086a85613408003900a1035008003140c80038070003120099040680058610b0800705c0d00a01c105641c107401042c0b460020030000e03444030410359554402e0f841140c50302d900380808040c5040186500c4c012200c07900107048028441c1801944031300c242c17001d035440b80c081440025605203044c1d058501030403000740010340742c8986450050b6910480041640441c1d8180743c80e20202c000c0c1010010f80d0003060f4100d60440d1200da494002500c2040b031071506502040c400d45100184260152921850f0404440107551540c2015810210039130007180d82c0c14168401400440c1000030629111030380022802041e0000c0c2d50b242117100c14681050364040d8001600d0120411180c101420b245000c450081c02d940f600d0040001d94030400f00700034440004040450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 708399631 1250 708398381 708398387
    0x4060f030e2401030b0903040b030c0304051509060402010201110f040b0904180b0a06050f0108061c08040807031a071b0309030f0f05010c03140a0b010504050a080105091c0807 77
    0x8000c4101c400201c42d14102c1d03800e10a4519110051400c2100c41d14000410521090114494002c110711026600e020304041200e0500c1c44004c2c0b10382c07001d0600202046c1085020441c800f020b44588120b4080c508184054546a02080d98140e005600744038030022038000401c1103806241c2440b42c081c0c03504e440c058540c10f094201300d00050380182e54a1088807804400e0313681c0d05140c1d10921201215180207a07905040390840d4102c0c138020b0f90502c0e00340d030280e604101016008401140c110049421244000003060702c0340030018441400030038009400f001c0007994000345ca00c6104868052000d29100340300120003110240000341141003054541d540d00400f05040c14028601807400c2600d0fa02d0301f64845010000841d1220142103500007804002e00c41c221038952103140510180c81207444031721800300058080343c001c0d40d5494a80800f42c3c054821a0003c140260103800420364450903e80244011a1003000c2401080b04c14185520790b420400c000b0281754031030310140e0f00c5d000411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 708400881 1250 708399631 708399641
    0x41404150b0f2106070201051e01033c150e0606062a030a0903020f04020a09170c0d110906060307022526070f080705120a0c032604060f03 61
    0x6401041d00100c88012440013804503501c0f4a40580010580d4201244416241601c1001da21603403030030390740144000b4150f40c000304000b00e0500b0101d820082410928a55002d600b1340c3c02500c2400c225441d000c01082050021120700c2070601003009803040c92405840b4401121481e40c400001c201c0f5035000f01c03e0502c01e00c00c079041c81101081e1203407d0403c0324a580d008408601c08608601030030021441c0c43c03003110351089000d907015400c00c241c45c84040c1010fa250301542807161240c40441c05041c0c000c01803488810401410502c500381c0c1070600e10741064030306c1c07240340c003239014900014460b080000440f400341100f54004c00c20051140034810701040c403000441041b0351a000700080c001d422003040310500c5a55900880040014080c072888d00701180d002c034096500b6034004000c00304022039407200722442980c2010030706d165032204034240314100390010b1682c0b500f110044188905010b4070340a4901d120344a40382c541244c51030a2080c020340c482c0c440000d06501201e14143d1280c0c01c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 708402131 1250 708400881 708400909
    0x80a050a02070209070216141c1401020a230c1f0b091602010605040510051201060b031807050d02060304030c11040f0c08010b07031b08040302041404150b0f 69
    0x10050602030b89900142450740c1c1a125540140d114220200f006031680000d540100b20351541005202d4000c0049070160441c0791500f4680310400e03c00400f0720800309030000d8400b04070b10086554440750940039201c130143c558980901840100c0745c01d40301d40c80c041101e0301c20a5100050503440010180c0003039900c0205058552145c491550304c0301030701d0f51520a40120300070000c1c0e0a8402600c4002821a42254005031089007003e061010758543d008044c02a2141036031a0311240040702074890141c0880e84c0001d022902c00001c100c8007000b140c3c1800c0c21182c0c03031810303120850303640c5e001c1255a58503508040d611036000c101280c0028000c14505e48010700c2004105a0100154005421500340030448003c258840e0340c0303665003640c00300f03005001d00171810040d070070407035142c4000300944c8601c2102003900094155075400c0c4000082035130010340c1e0051050080030180c05080b004600241c2c0c1c01c80e1200b500e01008280c0200c140203000d110b03d00600f207a4603859021080000100c0d030100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 708403381 1250 708402131 708402151
    0x40f0807050a060906050a0b0315011a0c100e060c0a080105041a12060115090b120c1c060e070509090a2412030206010621020d060506030f100b0406080a05 68
    0x382c0040c07414003580e03815500900e0001401c1c503040503000c059070340400c0424400d803c52100c6405209040811a042d203e110f180144002000500501c044c07003808402c070650306c5a900b401085550b07680040462485c0201619040e440e02d181d49030700c0e40903403240e10b0301003915413006005a0a25601909031080414500c0000740b10800116040c1d141e4009000e416400c80b8006020580003000382c02c0e00310720540b034108841407801c1b90019a5020700003102c400c40540348040f40160402c030050300c5404a103012800012000072510000900b07042c032030311040c060703203c5c0040d0600d80214191114214090b00700b02c07541e51141d813082c004108414110303100481300d4036160141c01e401070107580a0415041940312041c51420301924064050b80040108600780280621020701c9484088100c030700c0d110050b840d0030042039800301a0103650030007900a80e0100c20030a403004150f081900031380c0388031b8501c8541925070014554034815401a6400b0690700e0b0049080200c0507130003554041c003464 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 708404631 1250 708403381 708403393
    0x12d030321050718080a0312090501060312031a0f061204022803020a0e06101407080c1e0f0304180b030703081909030f021216060c11030303040f080705 67
    0x1102504840c8180c40304800100c3c0c1d491500080f00503404c48001506014005140007811617400410010391a2100e0030800d444189440403c40e003500400055070b40f02c0c10401003078a0b160300082c010a000b81c044004410f462008042c94180801c10040141c3c010340030074600480340d502401480c00180c800c9030890311001e02c60f03407690050403283d414607140708080e2118a1850042004c10b0340150880840b8401160030b00c00155200100d844c0007040c2070030b144217211007108444801d8042e41d207000e405990000341814103401c003c52203190303080200390302c444609541001d0f19660002c100041e96550f00c20801405103000c01012051080f490220104605c4401400710b41461920340c0700b216940300c00304000528004c85441c1c00408142c0b4541b036000285542c407800f450380140705c0040d0042500507441108040c0910001a041001c0382030620781a940b140d00602081148400350b03220304804c0342100380c40c41d011045900890300840030740180052601e4000071580944000c640d08e10441c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 708405881 1250 708404631 708404687
    0x4080304030f200304030c150503060d0f1505010819081b0f010c0201020a080a052a0d060303020c0a060c050705060a110f0601090501050409030f0f02010f0e06012d0303 74
    0xe1101d07103400c43c03009070103907490f00c0c55850142c00326101c1d030b049007010f030500b41801000309603c0810340ba4000c804a500d0303100c0c4500c5082c8000480c2c10510058005120b5200031480960b554001c0c2d41215081c8044824865440c0c0348140010a402c0c0014080d0740e081007080c0320031101a8565005000c400c095401c42c41c400e210007401c4980c0ce00c1d030f140160350041003445140350003860180d8452a00e17041800a440c1440c1070300e0114070840300340507002c01074601188041d010300c0c0640307202c10103c03603040000d40e07168240030f0b47e154202041e03588134038001d00c00030444038882c0202000c80f0340c0c0440201306ca20309180410480344c000110803420085a5100032012041c204000c0d9140e61344c1601904030341d4100309150054640c1600482e002d00e04255154000030b500c55501e000d811131600d0103c89849003180c04034054003074010000117031802c05c030301c2c907844681c0420204d04840e4450390468032100054101b110160f2170100c1c0c10078983d0615010400700f40a800d4021020b0004d0340c00c0f10180d03000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 708407131 1250 708405881 708405917
    0x50118050420033c0307032109020d0b040501060812070204051506040f181406090c0d0e060f060a12030513090204080303060f0102030903030f090607051218010804080304030f 77
    0x820040c2c81c3d0300301100e02840113a01007200914901c5081c3c0010310301e491100d407009468003035821b24008043c2500b03007000091280c5a4020303291203600401d01c0c41758804170f09144c105a8416181524554030301200000e4211000503440c0f10710304994040c80c1040025003c100c02000000c00b51042403040c6110b10504da5107a40c02130010f0f01402c140c1d50f1100341403914021a1810041441c0503080c42c00b510f04852041101407194840011103400c1c109549240c10020b43d8014455034000841c208080c41c5411345010858034400d00100d440e040d41d0307a643c070041000d101d00300e201c0c0315100d4540c88400c0d40480d110384010002e00c1010b40c1140d40302c95440e500502268890391109586803c04801d105071440c01c49120405045c09200031824000d106c0f000a40387c0c401c40e00c042400840c002031100b225100c2c2019a02040c1c0c008094454960a0342080009640443c80075030b0604141c1c030200140d9800341004601442d0032100c064150344c0c481d80c05582c001c40820041c41400082034024095800d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 708408381 1250 708407131 708407173
    0x4150b0708030709081203220210050a1b1212020705030324012102130504060609181803080402010e190602010e060c07120504080106030605011805042003 68
    0x44144401d50341da00e001c0714000c1110034075400c610380d190400c214130f040203481c86c0c003500d402c003454120110b00c0d400c0401e00f580e2440404a0001d4001070300e0050442c1c126004800340407016829154401d05424904034041160b4124400501105410b100200554815130305c42c0300d020100703a4010b2a082480d20f84070318503003084880107404e0b107001c0581c0384940322100e0702032214038080c2802400d0480c019103103507540c0040c500803004258040381c0074041c0801211140300412002d0410452503860321002000c605c3c0c280a800041d020052080c0710400b203500c51180f81c01c41c01640080243c06507a8212040d05001c0d1081c0c0c10015020304e103203210b607070740c0320401c0104408211542c6003034030f04080a404d449520003107041c1078001c0d00c104070284500004441c600356205181c2c0d00c24800300101512540660b070050310481d8a0102c010040200591205050380c040c0d1140e0a1b80c141ea40c0e01500c00e42d9800c54005020141302c2141010f0314081b03066110104400030141c6162161a0040606401c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 708409631 1250 708408381 708408383
    0x30c020309031c0504031a190b0d030f0c171213030806270f0604050a0c020c0d06060e0901020c0c0d260d09061a010201140118020409110c07060801120204150b07 71
    0x1146000a11042303071240790740c24160314010700041c002c240e01140024210002c8a2002d0144201d984003807031864418090348400b654445003111114044a0305085c940c2c1000601405071a40040410000b0b02d90601d170f610300a07415640c6001c42e6540d10240017440096491b00703c942000e603840c1699616807021014455045001d00005918101c4104400d8950161040103d68500056401000d501045084141d1000c1e5414101c00e0030600e001c000078211503001c481640c64080c244502540190010805413101c1c20840b441109043c00f0004181501e09005115141c42094540c1860410b60030f003135804201c0244034100728290710898180c490342241190810780e034000058103490452011420200b080c802000740c0f803414080c1d102414018002c846042418030044800000c1d10b80480b00900201c91003800040301358455180c50350000803c1d90014040c804000c20040e115100003412950000e1031030b2951499a020311000b44000e441051092442c00d10106410001100500d001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 708410881 1250 708409631 708409673
    0x30f030b04090803070306170309040b060d14040308010609140f01170c1e070b13301101141f032907080402061b0118080307030c020309031c050403 65
    0xe140180004045074610f4101c0e22000b4020040b02e23085040c000241d4450442c292000182740b945036002070f0303860003003210b1180d9890602064800700f50072441c01c107008a100762a52030050340c03034031000d54650682c1e005a1a40442d203030000800f52a00c0c5070042c1217440107040c80c0d403014203c4003ea50401d001120801c60000d0005103001813409410780e00c044003040b030019141400485e544c5c40a0814001e0444d4200903c2c01001300180500000e40018041c0300c0e04c040341d805a14117803032040d101d42034014072012610405100740e01600600811901c5400f051406050f9a41c0d00e0190900704081407404a90402083c4080001400b44443c144100c0010088070444000390f07101c56560b082c010504030401180303e00b40001600d903001502e50b1004000549540c00150341c14007070050210b1058400603c0803085900c0034029044010750140082d07a9040c00fa00318001000d0b66030b480f07003c01150305903114031004c2501c90108076501c400380500780b0700380b4901552501c406000d100030000714024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 708412131 1250 708410881 708410887
    0x120513020315010612180b060a08031c0c020a02030627030c0709060b0a2109020315070207080f0303160215010303030f0f0b13151e030b060105070b0103030f030b040908 74
    0xf003642001080d003440c13000c0641031080050800c0844402c0e208400000e040300601808a0b06070380d91127004c0409031910b542201e0311002189103d0607100c410b81811000580381103450030169101249603146550050b00800c02925261130200301300300c590743d040703507404000c50549007260400d00090001c124404000d2507410308295030310302114810f03030142d1035061003004034144c016045040140001c05840764540d44100106818000d8607140078025403502403468810070b110003808005008101d07540c2102c0e02241c445041c203039107021224a508a6500c10b200092150420031540d0b02d42c0c80380751041c1e40c6041d07a0740035030403c545403e070070490200784c8501104251101a104080c2442e0344e070542481310359040d0300401c8140860030859540c803030325140c20742c100e68a8031140d4401403040c4859014105802e006400040c0c80034042150382854840101f8070030362040381035841c1c05400c5111140c0702c1e40b07584d5050711205020501c0d5024103807a03c0041e2125035a41c800c0d603d941e8018070380555 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 708413381 1250 708412131 708412139
    0x20913050f07111c02070902040b1b01150b0309070905070908100501061e11031308010e010515060705120703030203090607230703180909050f030a12051302031501 72
    0x1944000411400800c0714640c412409900e0005580200310400c1c011841c03c04d210001c100d0804000303800000100d4000200043c803403140600410840e891407a41c0000d100a07a13914600707075a120608546411442941400394a0400340290707040f0300c00100f207682003640e401000c0160783e0215810f0000c90409101040001e10500802e07a040010210030041507040c40005440240c1c20208041c030101c0502e514496103024080049075144080100d0b0b0702c0f2800300c11031890064850007030049550803c4a400341030013050080718081c60008a44071480c40500d000d004054020390400d603050b20076104c003034035141c0781c9800a200040c06aa405681c7c0d03e030010341c06140000240030042040204001615112101081345191080c84021180c0e51315982c10100c404d11100c691259045443e0080000c5081c826404035460610400a541d0f291a56240081e1207011741b810030b0001c07035054040310f14150655400036a0040051040310500421600442d1600070340b5150042c01c0c440d0f940040c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 708414631 1250 708413381 708413401
    0x21306060206341818060902041208030903040f061715131a1201020703020111041d04030c080d052712030c04030f03050406030b09041a04050102091305 67
    0x10b40e020711410b4103070305407039a150f41901500701c08010254107201c08110010740c07a88030701516220809240c41a0142c0390301e52600201c40c041034149500b04a19003030740011a90058000e40b81127400c1038110031800045510b4241c1503030300042417240d95000401c4086a200062502000030300450b950b482c8000d1f01041207190201d00c040c00940c907150001c40d641c151684c1e240e8141f0460324021311b0101c0c4102051039003104091000c6170f02a03112035418500e050300f910550140c503095000764000c0c0610361020900e40740c54496801360750207060208003110760149240400c680c102c2e109180074504030245858002c90341d0000d0340c1c149003041d2a80c0c2807105070007a04a0078800d000c1c4042400051407410303c2c4042e924003806642585d000343c003100244415005c0c0e8250750043d90040c4100114000e94500245141d20500841002c82d140210070042030030300a124038401c540c0600401c50742c3d003501c03055201000e002403089036159020005244146c03078a11100401c4285032001080300d0908400032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 708415881 1250 708414631 708414643
    0x409080c1b04110903190303230a05010e0601080c0c071d06040605010504051e030c03030408160b030103030e0d0c0b0c0a110f0f01080c07060507110616050409020a0306030213060602 80
    0x2d8071105a0a0240040542d0f012034800c0c2806e030409920305960a603490250b010b400760841171104040d41c18840b081d00301883d0002c1e4442c0013400410015aa200c0c0c084c219200020748407a400140060006000c0d01d8000340113140c0c0682010841d11480d40d036401c2201a05155103071121468419000c0c01000d013068000c14000d890242403c5060605100110b4092001d034201c2d00c010302d4014a40d188145c130148040e5080e880c010301600d5440d91110b164941d02d0f841e01405c08004440900c00040c400c6a500560341a2035042d96412400c20040040121514141034140d40c03003054040001007901c0000018014129a00c014214003849420200308040c20760000c1c90103418600401e801c02e079110544010828003d0a00c151503846200a90700203003c0c0b803400411061415080c000c803940c1101245c40c01c0c5520a08541d81c42d0b81e0740300001511010726a180f00403c006110501c4001c000d5005407007003040740e103400074030a95079400280300c681ca80303a01d440d172003035a801007808034a5041c805 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 708417131 1250 708415881 708415901
    0x20030c01110c060f090607030503040b0702070b0409020d0e010606020c1201060e0408031009020d090b011205151b040e011d0c04030206070201113c0c0409080c1b04 72
    0xd0030a000301d01c4200d0b107681c40c03441e0141c4209000641a26181182030941e840808003a1550f42c442d121460060000d620544003035444410440000b03141510004040040d100034520540c11f0a1922503010040c5d046040155a5141c5507110b00e0a280c80911402c001081c140d40108552070b0600700340103805000e40e041d42411790404c0c4050122039a2902019000bd40c400384807a07803941d41c0e401c03000300400b854109071f004c58000140d19142e1026600701c0012070f4000e4011100990f40e070a0f604080e60100340c002451a0408c08200c0460041c4070300c8141e0202031068110f00888103c1c01e071800580c031070b810445851054400601c900c1c01c0c9881d02160030802540704140702e0800484005070303400389210083c4038510008040c030469106840b003440c400020001c1790540b002210809030070310740c1c41c1c0d40314441d100310340310300481c40006050392450001036801404c1c0c0c0c841440309100c00f90994880030789141c6002c00200d10311800411014050010400c0001d2203403101604010540d009182 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 708418381 1250 708417131 708417137
    0x301051312090f0b0a020102070c060c1505090c01030b04061a04030c05030604080414031e030d050903130515070210020607030e011109040b010903050f1b0307080a02061620030c01 79
    0x3a0a10041d0400c03e1000151a400c40d042e42d00c0f0901c50000301e0183c0319240e0700a042409003500001c0582e044030020303000911a9140400404581060701d048400480710380505521641c4001d8055000340e2050f0003003407000d0f01c0411201d4032412240c10803600040503070003c440000341002071120060982014040482c040e080f18185030f01c03030003030502450081992000d0061a002030aa0301003181d0014481d00c98a42904100e0002d1034a4503030f0013001035240601e080c07000040e60000c0101c202e0301a0300201c1045541241440240010012000580d0200844c2000b220b005a81d03549194005150f40381d009101c07620703150100500761900701e80c41a0890381050304081c1030080d07070420354003040425600000c60929402c0129000c041e01e43c000f4020f07001e150383c080c07140c10300450b8180000103025810303084003004100703142e9102490312420090740c0141652000601c1c1c080010b1003000d080c081005501c1d0b98649034160f80f101c1c21a03042011070345601c0309040d00c1c1402d104043c0c1c680c100342 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 708419631 1250 708418381 708418397
    0xa1206050409170d0f0630031407031209050a1e23010f141b130302040207080f0a032007260c0a05060f010b18010813020301051312 58
    0x143d21450f22400c2510000401d0074040703503891000742c0d00d85c01088125a140c0c01480740301d87e00d0380c801c0020104400000240d01e1100d1000144034142c00440c0445a499a030705400c03043c00d6951202140c0082400300c2c05c20450340e10f07240c0e001c5294040e888460340030380c000c0d0455810615000202644005c4010b0461b00380007464070118a10389040c4a082801c0036480c05c103090040b04582c01403441c0a001749050307107000c843c000c07290a03240d010b1307102e1045418100c00d0312050422000c0d080c0240c81b020b4052030384428041c801410542c010b01207803442141414180102c020404010703400400c0c5c0040001d50b0307420001400ca60b030180e0078110b880d103665030901e0031000d42c55903050301982e00c4921040c802150b1030700203240000401c44060390901410340b41074480a10b0003e8940c1c009454805107400450000f1400c508100c00311180001c1c1c00f0030315038412032682c0c01036449200040024810381072410081700561401e01070741c0e1244d28100700d11808010145010400881031800d1002040102e03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 708420881 1250 708419631 708419633
    0x50f011206051005130509010e0109020d08090d0c03060507020c0f060a080601120c02011a0406050307030b060d080c01020702132309100c020607090602160e090c060a1206050409 78
    0x1140c00345038641d0007040205080d601c08520050380c0c46143d00c5580c1000080c20304588604165000724003d14200c0c0081c4492040d0b41e0180d800d84081000180d40a40c1c50f040c00070010b058103004001901d40940707c1100411181c0703c0a4111040d58000d6038101c0e01d52040143c00760341801000084501103500c10101da02540c0407400b82d014018220041c02528404904a6030045005103614007080900740f01c044000ba00c001c0c080c02542110300c0b41c04070f54200c035208615060203100103685001d030080207001c1c82c68950000c81e6001400d4141c10200e51a00e50001c1380356000104460800c140002d661842c8620500416011210b03007400c410345042d105081c510326002400174031081642c0780c196541c40310702985003050303a00c240210790f240c50003001503500e5030046042485000b00b9260084200d50764102a611141e00d0034014403a0140d04000307201d0034058111140d04064000200c40c1412019804101d1941c040901a004200100e0440d25044154019100030f81320507903050000b0205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 708422131 1250 708420881 708420899
    0xf05071d0c070203010b09160e030309010f140c0a0f02010e0d020a0501110c3601180203042103020310120506220c12020909060708010312020a02060d0e01050f01 71
    0x103020111112070001d0030b036095503000d4114604014000380a00f00c1410603e100321051210080c0c0c0b4808600070741203602180c40c011023501c0d107045044e158007000140355001150744124030815444200d0041c03110200c2144100f0540c00c100d0300c00e0061102e00007003800054040c03084c20583c50301c100030b142c8541c00107884080c044012103100b803d1042d14081000840d60a0002c0c10000340d8110001c8020b010204003c03422000290710000d40000c00c50003612040c034510a02402074010300b429120116169194560045030302600840c2c8401c140642d00ca540d450708a000400040047e40100034498203001103081c0000400c81c0c02035100c4142600c0d680e070382d00c80d0b0300103011140c1170308811400030300c82d0602c549a0045950114150016a44540c2600d6900345c20840c268000c001d001b0010b034202600207126405002d02e80c0340c04044d6881d690b0b6212125401d410f00c04114013410800364016150f04c0003130180600901c40200e0f40c03140103080703180ac448000b801c0d1050700c4484c05c0104580301c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 708423381 1250 708422131 708422189
    0x109050435071104060e04050307020d031215060f020d02120a0306150c05060c0a080609270318040603022107031a0708100501090915120f0507 63
    0x229005880700c110140441c859007410354408806140480001d40b0b10400c40143c240c0b54244004480801c4903a032160b460482ca004212030042c1035070720400146006d403600c07402a5501a100780303455800e400c08423421900b42e0b0380b04690301003175449440e0240702d0b807a040000701c0e0040e00b261000f040c1c0907542400080d036481c140c1c010289003000001d89c41c02407034425040400035108500c000910b9028042d802050036100c100c050f5610b00600003c9504161008222602a034941d99070000548030907003000003419015004455418540d007001a03104203064134580f4040c0c0c00b00c051a1124001c4e0324040d41004070800c09440303140380c44400e00050b07803904414920750070070004078011000c01c04010352800000e074001602035070300c102d1aa04a00001321056200d01900d03590003c45440305108123442422078003c0c203002c07401c00d035418440c40005601c0070003034081d0301100c00d584e0b070b90354030710030901900901054031403440e500d5842d414403400300407001c000d0459070311000201c0c80c04542241d9180c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 708424631 1250 708423381 708423413
    0x30816170a02070501140906060915060918090703050f06010e07050d0b0d0b04021f120f02040e0115091502120703050c10020c011a0306041e080d02030f01090504 71
    0xe54110085120340314070b42d041d82d80c010361240081000700481412400c154004071803210b81d42c4031b0340c00000e960303051069241d80180141c03d012a511660700f01081469086003202ea0b07003110103100590b4070764164003c468010200c0202414042e41103040450600c050003400440c1644404c004000c0c00c1000848280e004000749412034a0307018104440b400b030410243d101d94400440035060301031089100126020764803c0350220441030000002016140a01d410803021420060503c1c40380c60254210441285004070014640303510f40c100801c01050030b80190f0721580b21b819400c20141d42098150b0003030038241e9030f564613080f29400020750f103100c0c0007490b0820030790100c0e01c00c007010301440035a1407a92a050036034201c450203001c007000a400003442c00a0300d40c2421a4040880403004041564540203406003805540c1d944038800c0c203124046102c14200031084d40b4602240d0300c1000380000021080e00942d503810100486c0315110010707000403640b903141005100000f122008140448 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 708425881 1250 708424631 708424667
    0x503030f06010c080a0905010905010309050d0318050307140c0a0f060507061e0b0109061103030a050402060f03182b08070203090301020a260402011205061c050a030816 74
    0x3596084012a0411089840100000d44c041340c0c00c406581c100034450195075003030742d5030103805030355500450680d8043c1c0006461030308900c8121030034511070f41081c2c208800d4074004030b011408030364607140b42d176108010584a80d440311502160058090100d4031180d407089901c0420301e41400118145072405100c1d200500400080301010400c1e01d40061140c0c20184401e410f507151034601701c130043d1054002050010704581c80208a07503000d2501074000d01801002507095a41d980654001040e0140c000d07a80b1000a1181814000340b48004501c21002b44105a0207820b0105116281c0403028221410b00c201c1c03201c0080c0855401401c40e0b9090015180c10106910f407905c06034103621440410b15055400050011a00c40c1c001107544000c4000e40c83d841c0c001d54400560010080c000c2e14000d000070b0109075035001071030f090303002240c2040c4000c100c19100d000c040c3c6011100c00c602042100d464100b00d800e40e06068200854950105c4940c0603c8400301e84440e004100c040001025200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 708427131 1250 708425881 708425911
    0x60f05100e01031b02010b01020f01200310050411131a030a051306050c09030f010e19060209100e040c02120f07030c1407171c0e180109150602010504050303 69
    0x490b0703200390400e54010407094660007661a410800038064294150b40b00d01501c904814442158014821400b048610f20380c45000803c4092845040e9840540a401e00c80c000e010080340b10f984520440a002c84a0000e59039904d18440c0d403040d0000303140d80141c11004041c6c4c41c444040700c01c0400c0303036072180e20548006829078800040ea901e4841c581000b07007806140c4820000c8000d094001441000b104601321203442c06107025080c02d9400b210409403c640080030210602251084103402440c03141801500b05801d682c0407803aa0a08441c040b800520301342c16244160030180300d42400c0d588948060300003440004c1200c4007070321401c2c3c2c0c403491084001950300240b5100d00350f550381e41036210034901121940c14503059601c1c0c2460041060024000d5143e107481080087e00c58000004280d24501c2e1a03210f482c00d03222820401c10031a00040b0100d5808994403403a4601c42c06800d107160300150440c4901100c2c00124100e4104405580c94401440086600041a00c0c4d0007002c2102a00d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 708428381 1250 708427131 708427157
    0xe0702011b1d3d02010f06150819020d0207030e0d0c031407031707030228150f0e0d030b010f080613060803030c121b0d240b0706060f0510 61
    0x662802c000c100511a0540c103028944400d243d64880400100d0354001c2c0301da00e0010240c002266003d1044055501c03240030901d000d01e0089001650000305618680e52200b84120104c080c1c3e441940040c1401c3c6e40040d2503003c01d90401000d43c520f801c140d80c0e01801440c550340303001d450a924080a001c0c10300240c000c0d840124200624000765600281d85613403510107089100568101060450260043d901e80c0c00c0042d400f102442d40c80b2000c4c0d40c1100d440384140d140d0b80042025000c4111140b501c400341440032800500038296000d014030300801a800440b07600904407010038041d81e0400c16101084240c1039030003103c00d0340102e02160081642d83d02951441c00819a56000907102d0101004000300c04407500042c015a03a0100720f030f00c1e840d941e000140d6100705000d034100c00b035400e0b042c080000b1400290f440048400c2600024484800300c01490100f90381c00e0307900069500600203070340700030020140101c01c0241050388029502509250001c0c000000c0415540c1c20003494506c10a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 708429631 1250 708428381 708428419
    0x80a0e0705060d06030b0a020304050601030b040302032506050a18080c0a1b1823070215100801110328020906030112060b0909100c090e0702011b1d 65
    0xe0020701009240950725126140558040c1007144000e8917440c0080c0009000c1100b00d000700d031300c10b55229006e403d15030700310ba4840c166000e0240060341144800e00503a800244111182c1d03000d0b844103010541904002d00d042c009841d001400214841e08240f51981e0300882d010b0a0205c00b0303840181c150f00c851460030520314207804c580b80078089a501100104500d00c0d41000b0f102900e40c400704c0d034081d111440401030107075518902c419004220400d2a0041c0050002d0001d40146051050b9071a45d40e0303071012111249410740b140c480400341c401d410810b030607091203000c500c41c0c0d44040613811454104100b904030001c0c03030081003006954011155442400740e04656000e0b000401c8903440e540c481c481c0301d8000c00b42c0e00040741d54500c0c05444442078500300f1140d41c800e01c412070061140c0340314090050098069400400c00340080c00c0c03000700300da545c3c0d1400d4602c1903180784d00020702d01c444415001da10700c0405400d0800e00003c9903c0240c1503d1250164800e00000da0700d5080b0482d89420030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 708430881 1250 708429631 708429643
    0x4090213051018051c0501110306210309010c060b03011a0102100b0f0108100905070201020d050604051308160512180d12050f1911010c03020f0904050c07020a14010f0f080a0e 77
    0x900c0c2d540ba203c5230424011000300514090341e03099440d00000040d0a202041520030861804030366403041c00154019803155425034002486800003140c11010140820300b502c01050407001c0200308031070003403119641042030b03451515001405000401d00040416000d0703103000200c5042041200029407442d1080c10700708000d0000314010420b901d0000c50090013508000c40400406007403c01280b00382c90030b40103160007040c40031041207044ca400d0b42c515425603c480c90f1072aa01050b07c2e421008501d0030301245000002c9555100c1d503441d40c1c908032000310700f08881d0140c4500504407101002c680185c212100d60380160070059521140510307040708901940c90b48050301e0002981800041b94804035130b00d1100c2c074400c020b10006a055002307900341d004181015043e40801e00949140d40703401d070080c58000721940b00482c5441c01c01c0e0080f603807160f01038220450a5288482e20700032075038004149030940c2c4071403502440398001002d00415031a00070f4564801551a0078444505038030a0040d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 708432131 1250 708430881 708430883
    0x2701020a0519031821050c1903030f1e05090106210c05151e04080c06070c05041b0f0309030f030e100203010f060212070201020303011a04090213051018051c 69
    0x19044c40d9a8062904014685040c04a12081c08035280310004140c0204180c0307540c0500840546a103504180962481e104292020303000c164a844001707041c12814030480c9541c4545039445c07070700a0002020700c03060324405080314035075070703d00f0b130342000520b85030000d007000104200e50203440d4940a08160a6800550704400d1b805040f0070010405642802d000b404800603411268580114092200072540914403c404544d00103000e800d840c1d1038640300900c109403259801c8552161184040750032149442c80750621180188001c0084171b811031111154600d0314a0706100d500d542e940d004040041c00025001899102d0b1042c00c01c11005022501d0780e00120b903030464680da0340c3c021100d42000c180c803558026014614440d0071041c07482d0204e400450b01030300210b145901e40080c801080820300500850740c101130201103003840580c00108503112109914098503801c0808018071030300e41441c88020b101c035145200c1155034050494004070380d400ca401303520f051010340304000101c2c1d502d14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 708433381 1250 708432131 708432161
    0xc121003050601090207060c0c15110d0606020f070b030705090d2105030a0b060903075004020c0601031202150a0501060207151b020a0b032701020a051903 68
    0x100100709542d09174007402d07144d80604001e100c4030003481e405035000498500c010705140400c04a0b0780c0426142d820001c03000f010012183c0c607002044441104641d05a045400141c020410301c2400e05020003112015000f202541d52441c1400900645a4810341d40c0c0c250060f9107803040d042c1400174016108200e148030350703042c5843e00311a00e40140164001c4951041041c40c0130080d10560514009460180c1000740051a2450034040070102e1a00780502c8e001c02820061071070580c141542ca40c032004000101d50022104104070125201e694076040700f6070041d0320600c0301340380540c400105a41181c0e00041145068072441c1c4040f420000c01413038a80882440c0e43c1803100956071940164100c036020380c20303a03005a850380200390b8000141841440040e0102c0c10141d0700100d4441c0241d6000d1004056011160790780c1a0610f4036007046401403100005e8030350221840050b01c84810208044000852401c07410031805002406160200031802c01c420001c02c41442c01303a80071401d0f000b00c201d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 708434631 1250 708433381 708433393
    0xe101d0303160302041d0103050601061409280308130b03040317150d0b01080f010209010203030727060e1504050a12170426030712050307020a0c0602100608060c12100305 75
    0x11b01c04206440e01380300413107852054000016140d8800d00c0442465402041c0092078042510104561020703081042400322841f80103402010140814030300045109e060341c16141c01c4a000903e2210207141d04c0045a00d00c10401c0000180d4405414154516400568100d54441d50410785c0f81c801000758294200950041000602155010050480d0419422a95a005a140c24500381c1c000d000151340564418400b24207150300030440c0c041c100391a150000d240644809107081d200889601c19030100c0c840b00c50320b91007410046001c03054982410281860300e89003402245d604d810341e00c00d5940c2088418500010042c8a00310000d80401513540c0c1d030b0f100c1d034a6080c007141000d1141d020707042981049010445000d004810740d0318140c3c011007045c00a603040c80e800da400c0c3d0300007060b8104501402004000049400c4542c03005400c0d160300900c50300c0c03c425100070407104582c10801180d440401008a260300081c1205c81d03544000c0b0060240e03444007035200303941d03018039000203002c1c3c060b00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 708435881 1250 708434631 708434669
    0x41505040314040f050f0d030507020d1104021206040b0307030507150e03030f03060a0e010308040306050601021e071403063d180b041a0609060403060e101d030316030204 75
    0x113001e0f0b034240c90040300c0040364180741a08100c0d05064020005020450500c40ca1001d4a0b14055045140b07020b50400064481c510000070126407224881424401256090100f07904042c40368001824081d0001c0ca40707241182c40e40303643c038142c42c0b1400c4020b084100e00c03541c900b881000c00d104d240320041d0450b510703400641c1d65100e41c0e0f00100c40407800b6207889440001e9140d4002210380c1266000744502d80b400b03043d07480340c0d005004000c104c02e0543c45080b81c4010305242155141e80c80c000c5d0301c80540307405400c00c8000300c40303640030000c094400d51120007807007800f030402900c031480011840412801c0819040810548c03040004140c0307440dc52060000481c000d0a940550b1074400d0700f2010809071304610708000c100d0309213881107062180352081c1401c2505206000b0018184000c00c00c50505a590b0744601c156001142d181e00781d82c200d03450205805200d405088000c0f00310700050144120a25180c40d41c0e1301005001072080010b800c101c9081c1c0d8003030740c11103015102e0944c0b40102c001c90703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 708437131 1250 708435881 708435899
    0x130f030f03030c09230a030f0f060c02030a02030405121e060106080703060305100f0b060c03220302090c0d09080d090c060203040f17070b030702060403090501030504150504031404 79
    0x100e00e01900880c0c144040880c10600c1001884151780c4101e109400c144c0c2d1089000f00d4206002c4059500070400b1344004c8081550380a141000d98131a00b0b82c600d007032249141000903100c000499000390f40c414882d290740c25402100b944c040d038009807400350b41d840e548018207250050304158014400003020040381018000b080d61416690f958449032880c1d101c012044041348c3c020320015040b0b40111501c0c8401c3c0c03280350030034800103a502d0000b04e80c440a9800040c0703198801309600c040e0340d00005401d40c12060103401c80c002901c0f00c070388200c0c03e07a1564004c03401c0160002c054450343c007800240720138450050340c001f40b40240c2112520380c032803444442c001e000f00025503003510710798420080003d85500c0001201c00317a07103c4a0b014441c840c0b034242005000510020300002e1070041d5000820203540c00c070003461041105034010205814a4280507000c1205d60300003604240c100000c120101381d01c1508226924401c80b400034095407076003070440d0341030640404000038001c00540000c0b5420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 708438381 1250 708437131 708437153
    0x140906040309050102070608010e1b13061b0b0f040f060204030f1a0c04060c08070f1a0c0c060118141f0603140a020a050705010f15050420130f03 64
    0xc070a40b41c02040e40d0700da000582e9034103400e10804000400c2480103100104412030610f4204c03009008240c200400003840c00c0303c50701700800b03280707202e11507c41c20010140c0c8840072031a80d00114605074204400e503107907240741650091010306d0101c44240424100401d02c2d40841030385070080c07001c540342d03a10b038a0500900f038955201a14004004a0f0614003800c11010290080202f00c41e540d140600d00b42040d0b445d801118001d95100b50b060142c800400c1010b030030307400114801c03840c1142002080d41321240305400501420300c1c8180074040181c40c80c10018550703056a210741000005402007035030800241c180328451000c0203900100780900d014003041301c11842e420103600c1594080c1c072058210b003225102010038505d45071240201e800104260700a000168543c6400c0c3c0c0750044907201c0509565603849002d20050b6218060384883c032000c4003e1024080c221000d002040342e03249080c8440c1509500c090301000d001418502c000e940d200040024134501400920560750317400d0001e0800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 708439631 1250 708438381 708438383
    0x12021617071a13030623091b030c0303040b0405011e0507030302030c0d0e010f0e0c010206011403010212010b1c0902220e0a1518030207060c031b060b040c03110405120114090604 78
    0x6e20108107410442e01210b10544221411401080034540410920013081c600c40c0b94079806000f84e44440030140c13014070042000d0002201040d84e100d18000004166015440c2c0003005414140c4170380c0c00c15607210f4200c9a20340e0305485c0158403a03c9040294041c1c3c0714a6030104012490550110890034064010741030846410707000b00302d403c2c4a03040043e100c4440350f1465005030400d100522241c0c00515100640c51800b40005080040d0440c2010080300f003a00100e5204c140071440a420140031031a00b034520f90b00403020702801c540c076404112400420b1070b4121503d9400c01e10302a4081190f40042040b50304042220180300d85420110546003001c9109500303182080417031300c1001448581a07411641c16401040d44a1610f0403c0b60b002049450442c03c210b480002e404101d641440001c000a01490000903880c10400800013100c4544585000385800d0645120440400d482034408885040d2500d100d0a00c452040c54010200094031403000e403105c00500c00e140da4001000c0e4415 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 708440881 1250 708439631 708439661
    0x319140d09170306060901081302100206090d14030c0702040f0f020a090e010503030a0f0e03060708090f01140711010e0d091503050f180a12021617071a130306 70
    0x2030780d441081400c83d2004070741d8035030860000c10170389165510a0302d50603804484c0210713140740142c0e10b9001400d40403e040b840c00060380100180030200b501801101009549820000705d00c500303881814005001c010701c4890319140c086119019500e45410058800c0c2441d0710400a50a80190050003900514944d80000e801c3c030b900402c6070f4401740110360503901c00800450070b00386410021140c6c201850f00c21000c009980441086944080112030b01400702500c8004031403601d18001444d01c101c148490141d681030031002440518140c20b01d9400a508c1d180038500c102d0800140382c09001005079640300ea200d044501ca045a80c841c1400080d218441c044500100f5400422001d46106581030380b0407240910100e4000c0c0040c4081c04540301e04007068130140c44007078445000c038500100310507025803c0f2100b0f58240000031003204010303203e0018000c0342040043c501c2030365114031707002d40e42c02028500000803030410b40d034054624040c51030382d600c0506500c9141c910094190a0200303600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 708442131 1250 708440881 708440903
    0x60c0a0b01140303120105061c05010f05010f050a1e17010906140a061403040c050607030e03100e030417030433141c2c1e0319140d09 59
    0x1c900d004022650010b081c020412806d074248002c000d01688a00700030150f801041c055000d66400b5801900c3c0240010b5040c0007481b031501c40090111440000070200300003082051550443d0050b9100111860f40580041000b5404600351142030a0f08802c0d03110412030800000c5078111500504140c420741204042c0e00000c541c1441000c07481e0b0300803500400c5514509000440c0040e0140d5407150080d00c00b41c81041c0c1e0b54011981c1c03a84200020b41c001115030007003442600301006032204200f030010040200d0f2103011611900e0740558021151200c00340c0d0200e1002080c104280c078090000b081c1e400b40f000054041d404c3c0816843c3d000780c60041100303002d41e13000e14080d16104a2030700b82c00c00c3e4030380741c90140a011306410702c052500d44205540d8034201040700890500c100040d1100c0381c40c00c4101d0210a0344a440c02240002425280000d1040c50300c1144002c41a50b0341ea4004a440908940c0080801d8a030303044135003245108a01d01140708119907860340c102580b041e01460390181 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 708443381 1250 708442131 708442169
    0x60e070b03070207090216020904030c03031b0905370f0806100504021c0c050904110403050c010503070c020303030a0c120b0f060702031609090b070219060b060c0a0b01 74
    0x40341d00044500e1005608000d0040103100c019030000d040c1041c440c003a5020f6200c9540c00190420710907617080d80059203220b1058201501403003215002500c001580c45c0500481c04014850b42c4240a218001c0c02c0104240d034646014000038038401c0502c105000355201100c4000100d01000d2043d080360300e010a01c001813840740491b0081c0103043d07000c850075950b81860b040c00040c3d48088020b80d21f40c00d040d521441420100d21440c58021042c1d91003541d00d0028004100c10b43c1c2c40320211000720b0380108404c00000310700040055000b0380c01e0918076129a1800301c103440c018100382c40030350140400001c0041165855105494115450322a13078001f4882e002d058080711000480243c000b08002651041450244041c2170011301c014211401442400c80c03e0a28100ea84d00101c0c207242c4402040040165642583d0390003030a5200504c10401044250103102c2486400034150b5981d40580306034986440b0110303004100e07840304441c10307292a450030320204407091084c880203211490500c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 708444631 1250 708443381 708443399
    0x5010204060201051f031a04081209160b03010e0106140c01060602330408130515130e0f010b07150c09140d03120f0207021e01020c010302190c0204020c0703060e07 72
    0x501a240c00901f80c00c003d1360101c1c4003400782a000342040d20200b500303216505942c02c0c0d005c4d04a20405c8420054014070706440c0c000030020b40a80c0111408540500041c04003c41280000303045451910704018500903d4003042158442c05c440c000ca0395090813004135042d0340004100c6031101c20030b50b0032209403469112020310003441d0440c4031000002c1c100800c1c00300f1201c201426007400c01d00d141e22401643d40000031456020a008107080d000701046000d495841c6558810040185603024496032815007140b0f03249400c14000d040d000e080c0881c2003001e228051644401c411100c02007002500c50f00240a0301d42c1180703105241081300e042c203101100d030910311465030165a060300c850250364a005c0d503400141210150440d200c583c20f104a20142e5128005040d030b40e0403255207405001d0100e00024284540600458145401080050f4060710094220a0040365525103141d11882510015001e0700c5581400440391240382400b01c01d111490307200400100e24030040b111703103a43d681d070310b2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 708445881 1250 708444631 708444691
    0xf120314160c12110d0806040f0c0807030e0a0803010605030f010501021c231306020606040c1d0f1e03070e130f1b06080609330406030501020406020105 67
    0xc00006040410b907070001805069003da1a040a041003114580c1c0951350703500d080840000b840026010781c00380402c0d81020300c180a21020030799800d00c41c00444d0741010307002c118040d01810825654000840318800240140c2101540c02050035a0304d503903407540104a0340090300c504c001d0100e044000940c40d800003440409907001d0303102c203032003c110406007510140c00035407a800400c407083d510050a850460b0040a024808900c5240c607207060000083c60000300030225409036103001d4800c05017541101e03a02418002110040b41004a2600400c240102c000c0220750454440082144a0140058020711090b8190708032540c09556596200c035074482541c911080f91003499603d070100310300d031540c15507c501403021505064030300c82c000c034507046c81540184000381c240c030140315461400005082e007142820040c0780004040003d8213210340d00340540c1991614610110702d4540e100d5030458401141c10800031519a41e564901901801046480208a0700741625554205189070b0316 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 708447131 1250 708445881 708445921
    0x1e081207050118171e0c010c020f0f06041502130f05120606090a05070912080409050c09010f03051503070b0a0201050f0f0103030c0f02030307050106030201140f0f03040f120314 78
    0x141c10300c1413000042c4608103620000d480303600201e00151520724541290002d09800003028000500c034007080760000d081c000201043c103459000f103010b5141c003580014100790401c0c0c001c503c840b0540840842c0a00a1049802d8000c030902c030240000707240692111814100c49080c0c03000c60320706181c0b081281e194007040f0b901c1a48521150045200f2403e10f600c120351040080c01d20fa100c2e1034460f0070042d0201b140d0305040b100010001403e0007071110a004207500310364020310071414030340b540300043c0c00c2d401034a0310001015502d0001406010500311f00500d445000340960710516103c5244c00d06550100541002540c01e1802040d000781360b0011f4144250000000816141d00711756080340c100c0000c1030296082125103204c0000f40e9024001800213521502c00028101d28620005d8051518400304803010001801034051524106003250080715219a0581d03582c0d5403440c080c04c04095002c0090480710306c500300484015056880140300040a031051000c039590710001d45140c0c1130a00e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 708448381 1250 708447131 708447143
    0xe090907090e1207110a0305150a06060503012304061203090f050d030917030d05090c01030b01020f10090f05010204032402070f06090204110f040905060603010e011e081207050118 79
    0x484c1c3c01240360f0b48600d60120000a1030030445503601d443e820318208046807561404000941485071100403032041c44000d0003942006803c44d0324044400342200f050baa12000e111840000418081c2d0302ca0380101c02410711022241840c21031410000d280c1091805900350b030002c0c205010900d0309d0002e80c0b50315600d500d95150a1100d04141c2d1108980709012004951440203011803040f00055008030351040303440d80010f15580482d500018280c40c21091100d055404c946070042c2150404075240d0b080024004c0d0101c1c902105241c000458210200e0140a95201060100802803c0b401c0848180c062079140300040407100d190b1012480b40d80da00070b1190703caa85a01000611980208200c0350005000260600d01c1d200605050b510910105d2184a40000c090020040314801c0076080f0100b69241425581044481c483c0100107004031041209001c64861408024208a80c00349c15840700791000240302d00d00d42800c90b01301c008200d825508141042c407101041c5e14003105e000350811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 708449631 1250 708448381 708448387
    0x5010c143708070212070f0306090210090b09040b0d060f141e0406051f08010c03061a040501140f0706090b13030f0302030601090f031109061203040b0a0e090907090e12 74
    0x5400c014840605d05140038250240000c00250880140805401540603840100380b03500c0718070400000c00100080542030248111060140010a9003503032a582000d84002607810710f20400140120800c890007000d00e41044507130500c80c0c4042d0480c1043c2206488000965218500050701400c0c120700c081245c0705020002501183c104d82009411a101c10704810f41118007605010314922035422100f89030b03440c1c03d07041d441d440c3c5c0f5114010041503804420075211020389011075440c03240748a814100305581c0ca03c1107454081004130b580190303070205c10b80e640d08000d15048025121055080d079400c401c00c000130300804005c6401540d26949aa505501c0700000348082c0d0003504080c20480c108100c0c2071000c202d8601ca420440051800f41042881c00300d180c108004106a00608050107480862200c40c21854000250f0742540c80c2006915100c1e03000d0802211400804041e16602c0300b410f60034040d9145010501030161445841e0a00c22010744002d025506c01c0c2560400c0f840038020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 708450881 1250 708449631 708449633
    0x5090a030c0b150613260a02150f1801020c01050a08070f09080a0605060301050105030a030903030c08190c021905240d020a090f0e0402010905010c14370807 69
    0x21840c101e42c06001d80002c88403003e4680c002c11050f0b0410103005030001c086000c10b020700c0c5950110507801c680c04201e203064048030250714a8a500d101c243c024000c641c1e0318009520048008103549525140081c21074132400040c06030f02000c0800f00e101ea025029144040300d40307500c100c0881d01025169200c00c0d2141e2200c0070200d40c03800420302c3e04800c000740710030701203074660052003c08286400b800001c0380f1070234400109401c441060784064400c0d40900c42c4500002c0c8c00c40324040460360942050b14011100d800c01c01c6442c400d4192210f42d88031207409108103103402c0104003140500a442c84481c0c030003010106480b00609005480d40160001450b11b00c9a101409000342c2e02c82100b92542400c0101d0000c10a030b03000340c0208004a00c41d48400e10402c030007401c0c021b0050003000f01c07480d810308081e0006808028103015840c10007010720003113000c0c46112000148001c170302c07030200c420520b418000469000c42803d00070704031440740074050342e2108000c1e1001b44441d0300103030302c036240c1181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 708452131 1250 708450881 708450893
    0x150403080d0b030d02072417100302040e010606020615010801060f0903081204051e07090209120d030c020d05040f05011d0312180301020f0a05072a031518150f0f06080105090a030c 79
    0x1c120004278181210040010784443c011440045600700020032106c0c02c200006e414071400a00b880c03018921810006134584e032118045044902c0341c02d20700700c00000141d0881b5800103d41020388240390000b421030030105014400d0f8030541c020800e90b45a01d565a0805030400402c0200c64625840001c0c24410701c0b0243e801005090b000815181224140e40602c5007824001c80b002804a951060b01d040c403140c0601c203009440c3c40b140703080d5240c90300305108002c0308a1540502410008804c900d521700301350001c15840140d90017012a41800100140c9100701d901014111042c0880c411004109040500a845035a6100040d8074104420780804407400d4020712402d950450000780c08102040c00850f030403040a5410700e0303000032035003107007002000e880345c40354003102c5e25141c400b034807004082a00720358a4455008580d42241c04500401310007030484a0716403402c0314035040e00551221825440902210001c40003032011b1341d14403160940351010b20b00d001c2c0c00315909403114000149 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 708453237 1106 708452131 708452177
    0x2040e010503060c0304060b061b0d020c0103060e0f1003020d080301031e12212d0905060a050901200304030e150403080d0b030d020724 60
    0xa091013032980c203102c02080686902e6035005003c43ca030303603260b08880b505030950401c0038010800d02c01c082e40321020740309248051301c29147d10300e006501901400085544000340c40019070755100c0100c2920300000d114886207400400e0120060392811201d49400c4d0254101a80b690b0440c80d04000301e0f10380c4c0c1481014522080e241c580000c2540544e1108114545005860200c541c6843c40480591060100001d41085001c190701d035402240e48900484410000d0400c00e0002d03840402c5588108001c0d210f034002c2030000d101416181c000640010540e4000101c1d90352144208407844050001045204000000c0c4000c1c1079110a10b415007407070840309168280c0d441e60f4000007070301c19840010701c9110081076400d40c4001d1075000564445024007a946c2c0300900803030094807465517006202d11906850004101000841d41140111342103803903200d580c00780c00d800115144 = true := by decide +kernel

theorem cover : BRFrame.Cov 708273381 708453237 := by
  have h0 := BRFrame.cov_init 708273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 708273381 ≤ n) (h2 : n < 708453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
