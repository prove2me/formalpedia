-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3478
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:47:01.943535+00:00
-- url     : https://prove2.me/submissions/69db0436-5dec-432a-8831-7c63c1cb1868

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 625359712 ≤ n < 625539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 625360962 1250 625359712 625359737
    0x9040c0915050a0e16050406080703020901020a0f061b020609030d020918040c031101050c0d120b36070219030912110a140a18022703013207 62
    0x3c10240200503d4480d0042c9454940b04550307200402020019000340002400280469074100c1d00e40b941c0081146001a180c3e8900b4004074600f00c03440501604001017071458009200d026003107590354441c500044040e80e450071034100ea4a12040340d46228540007803003441495000303030700108507964004014029255a4003002a41024250b030300302c51091510310f0170010042112104602200c2c06d0a02d07604088040b4101031710f4001c2d0f44002e20800807540244c0202d503040c0c0c0d11202c400940641071400001c02103030780c1c428002c00f12560f14504d08502892004010341d490b0031031300c11340c3c1c0d65010340309801c03600600080d44025110214240990f0400200d02410034015a004082c0031700948283d8105050500c2550307005508020700800e240c41d0000055191001090700300d4540c0c00210b003400b441d02e02206c000340500c184403000b412038100c0140641000704551320302c03050201e00800c01c45007031150b1a0481c04405410710b8a0411001c007100c8032061200d00250b100c1c07418108070401420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 625362212 1250 625360962 625360969
    0x3040503070801090209060d11040c02030c160302040f050105130e010b0d03050d0c0503010f061101020c030a02030a0206060a030f0b0901110d0914010c020c0603040c080703030305041109040c091505 87
    0x100d60300b120116a43d107040340000c0d807515800954010034155014502c41c5043e883d20741d00c1a294001640c000c50b110f40790031203994420070840b0200c0f0352a0058540c20044140c01104840c00c91005030300c5030b401c1c00075401d0041424403546040340c0c0020144900182e41c4007012015281e0a050310180f550b07a0041c00800380c0b281050402950b101e66a07941d80c1d001403000002c100c030b113241c00d044104001440180134440c5070040c90410380c0d02a040905801c0d1a813040c40380a03110703c2c400c00c4090f00000c1401504e041e0000003030850704c4040d0f0246c400301d5540c00107001c400710391031201520100c10b00c0344020108800c040d50342c0c4c2217103070040049078032000241902d00781c0d88540c085941041c0d96240071410300480110402c040c148140080c0090500b5000007981c170043c2c11200d6114000c0080417508101d619010b95004107d080e040d988940c0e500e04000c1c1c000c06044034181c403100901d1861240925081c1d40e0541308984c4100407400d26401c2403c100010480c0d0911003c0c8204400741c00328466a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 625363462 1250 625362212 625362223
    0x313031209150e0c210f0703240c0c0303020304020103020909040b1b0c0a0311030d0f060e07020a050706200a060911090f010b030a1d0a12020c1c020303040503 70
    0x6004101c1c103403440ea000034602c411200c0f0075611440365003007003200140640d903580c01da596070700400141410415820011038103010440d080c0361150310480900104009030b911030100c0110119040c603416280d106510810380c0d504550100c0050701c030f48000400a4020743c095a0031600600d00141042c1065002c40d00b0b420042e207080d00d5a841c03010810540320803d0051040a80340603103520f0820b100380c0c0440742c1c0c40c200004024107010038048a442201c008005a40c4d1401030084117000d03150078488004000c0c1068003410f4042c0e0b0045c0001076043e800055000ba1240d88a00100409442e090381107640505040020629030514400318101803010004000c4085c0074040014a43e120383c60141d1800389000d03180c42c00384621a0402005040d003462040c11900b040e1245a60f80d996074140c0c2d001000d03201441c0700300c1105203000000900c80001c40c03c0d07810b40304000140c0d1890300c04000340d03038980300586100d500651128694003c5002c2e202d24054180c4003034100c13420540c591000a0810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 625364712 1250 625363462 625363481
    0xb0a08042d1e080306060d020f1306030b010e09150112020d060e06091003060e030d0e0c0a0611071217070b1f03020a050108040f120e0102101103130312 67
    0x7500201c1c0510034000c0980581c4010309100814188114083e51100458003004150600c65a0017103190004060a5012140c44141010b503041c2d458601c0c40c0b003c280c0b5101c2c1e02400300001d00c1c02c181d45100d940155088409a000148940c96595079586400d58403240031140c1c0b030401c0010941c0c01c1180d8401c1c006000c2d168003500011580900340801c1d80d6460400504042c803800e4043c062180440c1500604030540341c004d400402e040c02d40c3c40c00c00e840e601c02d1001070700100f40b408410a0071184c01064080c4038590440304103e285607101c038100d4294211035044402078101480c10031100380a005074035005c5102e151454034001501002c142190441c85003920003a01c00010010555241e40381e00c1c1e484e40e10161007840603400d41d0041601c002e9a40034040c1401144400b242c14001310301440340c0d0709030b0b01400040d0070320006800204440754480802e805803003411100c1c0421300d500d0003042e00000040100c64295a280b101001c1c1c1580001002d0f805d020140507030602c1903509000d149801d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 625365962 1250 625364712 625364783
    0x1207030b060307090e0609160f14040e070f0201090818030f01020301140a080f03120c130f14010203120c0a05070c0e15190b0c0309041a0102160b0a0804 67
    0x161442c0840c000001500145240c1c8644407c800700101e5041100c170710002110302d80b03030041c3e0380c010f50102a1804260b0304c04c0e660805101080c00a01c0c0ea40307100042e03100e0784039550b0320000d4030982c0c00143d00723840321198000d1039020240411017a01401c0c141309200690010102d07944911404606422a80301380c014004c46c0d01c034094a92654144203030b0b2a002400104001c166148a900c205522802814181c0640d0b0154400ac90020010310090302c028110b03042650300015500c10803159414032910801c1080e4812341e0074604150f0000c4203903485815140c1c3e818055507100e420301149540100c00c0c4609004042c040a000304202002200c0900781c583d00001503402e2000415240d44134030116176210300c00c11038001e07508409a0354107108440c0c90702059500c0c1e1614540160440c060154044e410501c0c143c6c0b0201d03101d0184e600211446400e07020b450002007002d41640d800b64080c01284030800c410080c0303242d1144030b4400c0952060042e11200c5440b20400350580c51000e103108403166 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 625367212 1250 625365962 625365977
    0xb1206040b030a20150a02070305070603090209010b0c0f0714091003080a320711090705040303181a19030b030a03030f0e06100311030309061207030b060307 69
    0x1640c0c00d0520800002140c11001031909072120341c1c40e800c80d402500110702003000c0f0b0541c1070050752600511001c404048103419501e4843c01d2400139940c00b160b11080e82c5900c220440000c400340a41303d00061990040d1048800d41c0c24503081121540c07040d590059244a03090388014000e40921402026120002111403811342400410010b074801914000101007440e40801c000340119003252920361a606101da80300e1444002034aa04038a410a00b403090b0405030307841e2206103e0001040da4522038440303072409000c0901032040c01d940031905100891400c010030300c0468001c42420040e08445100e41c940940c0f42c0c0045003000441d21482d540605c000705541500741d00d884250700502c200b0785410041a00c1c8240066600c075076415000d0107043d500c01d026401f40c07a044d0015803100001e44122481420410020518030989100944655040050f2000d607071502004403250010002c124508042c1e4035003000c0341c1407801401c0c01091565420b882412070721414051441103c980d143d900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 625368462 1250 625367212 625367221
    0x90311130e0a060b27090c030d121b0e1c060207030503010e0a0905060610050d1508100902090c2503050c011a030a0602210901060504061202010c1b0b12 67
    0x401395400000d580b40b069402200030190030002008485120b4000d03e1034910588581c000282403010428139039800d0301843d2071240980b038211701c1d89180400c126604000c60008a4820581c0480780c01c0d4601c0094080c0010090610300405503c443c0991919004030b024003941e56001260321a26017240407a0003c1300403c044c003003d114a0790302041e0802d003441108031595545884407c0201032600c1005c690382c064281c0351055080e01c46c0e42400f02d104102c0c2d0401c01e044030107090003034843c0380c00511590f0041e00c0c03001807a02400e8012a8080c20915030b0340c4906586d520706402c4901403e1000d00d4820b2070680380920120168029802601c5165445c12141103507402e40b096042001d14603085540c49141540740020b400000b02d03007003100162039a03001ca080d20b02130300b14008200e080c00848802d00020b000f040d4028421582c00700c0e0200580e556580e00d04103052200c040c0680803848007101c50000c180062054030201c10071100c040c0c21180c5800141500b90840c1c81e184281078080d20810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 625369712 1250 625368462 625368473
    0x21100506031003260318060603071805040f150510090213050d06090c0611150105033a0818150a0b0d0209010303020303040c05090601090311130e0a 65
    0x508000e445251a6142c4110000700d094101c1c40010401c104580840380030780c24a409000801d010b1413251390f503d00344040e40d900101043d0380042d030280030b0140070496500e00015040100d03082405410310103040443c0d410010080288152090104444200000307a8271101803035030324044000016813400d15009070011010a070300180b25541c41003045103000c290b41c068030011290304035402c0c40045c1d800d181a60240011100040480c100403d0205850350441e030008844810340701205d210084240540342c51103000c1c4030301605a0400c2c0b20b00c000c19803190003807900b00f4136050044505800210950026994180040d000150441c014031880143c00c0750119503d00c4e80c00014100d440d95102c1c0e8100c2c010000c0c082d4800b0564a280ea400c1c02e4840c28491107840350020907480c8290ba603420007070b407250300499084584d000c8040b4041200d14108c001140200410b13901c40c01a1400c560390f0466041d11140c3c0035600003801c811280038402903000d003500501408006c0e02e140301c1c162801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 625370962 1250 625369712 625369741
    0xc01020d0c030204064b02010f060303080f27160906030b220b240405040b06060c0312090a0201080f0f04060f020d0e1605060903030304030305070521 66
    0x80800b0540104404c1110b154003100c85410b03003030000540c52900c03c0a041a403049182c04c2e06496404800c03000e112040008080540c111600e2900240290115000b000c411200c16000007000316010380041001aa4020318003a406101c910316a400520025441041c00100a1180d0111f60000a810031003450b07072580c180050420303500a01200b03085070b40d280c0c0309110003801404000c05154042510002c45200724a1150700283c080480d8100500078101c000c00c00780358016802c0550b91303030f02020305151058910590300300c000c41810f80c0f908010040b0719031260790000080c7c4400e002107880d5024001c03942d03015041c440b0040c07005a100d440090701807100102910789105110b03080000c50540f01c58010340c4598403110020b10440114003090090003035001e40465140b41c09502d100030500086c02c0c8040e12000c0100c04502a43c079020000d9910030002443d4054000340042400a4020f400103a0000980c0c01d20f0781c04e142811070302c111003450010306019a62488805d201003040048035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 625372212 1250 625370962 625370981
    0x20d0f14070f030c0504020307090f082116080f040915050102120316050f0d0911090a0b0102030f03060d1a19050103051c140c061b1306230c01020d 65
    0xc1280c2c040b861603c4800d110b40052041c41d0003a44c0000010b01018415061a00039110089070f24a034162100c2000351382e040f4940b10000080d1240c09101c0301808001c0988410404203680729800200c5a41d64903c0398011039a5103091007424400850114040d0203143c00110002c201d580034107251078002031504224280c9800ca0320783c10400d0041c0000b46240c460882d15035401d24a503103034900c0c8200503440c4204c08040c02283d10f0300000c641042450f01001400c117500f02c80401e42038981640f00c00403a034020400e2800b603401005404001035822000d15803050000744450752400c100d4440116884101101d000350503034210410905da88004556003400c503900404001a60555032079555450720031240ca22400ca0728160b910180d03110b400d10040c18140c24a09503201c0e00d001204c2541e6120968040301121101e44040e80341502600613100b1a41840d03503004045480c1203416a00c0d1900045080d0002a040004142d0501d0010050003542d100900060ba5140c0b41c0344071404403141200c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 625373462 1250 625372212 625372229
    0xa05060417061e13020112020a0302030405010b0105040b040314030c061e0709060906050d0b030f01091a060a051207050315041b0302060a030f0e0d030203071413060507020d0f1407 79
    0x209a00841e0f00ca0403450b40b110780601d190200301407a00058580b0159030903403507152800010f020741180c1c1d043c0c014601440c4520024440041c6000c0150f505024a000700e030010002400200f022400490440980d10002c8060b249021841c405560030b182c01111588180319481c3c0503080117103402681c01e90b12005610b04285501d0800314001d003505894401c900400c4000300c0c1030048086594072015101c2c038020202d90312404a0240317540030b800c07400300a891400d030207074807001400c0200804178451000100017203400d50030002045070140f003100440304d4600c1280c3c0041aa91002c0020000c800c3c04003007400403a1400d49071854902d100e8103c10320600fa8aa40100016140d0030b081c0c0314102d901d4207010440c6d01141007800c00900034040c51031340b107103e100d030350f0b0450a80540c002e5000361107680c3c4038403055680203100f4035280300d5080e5001410380120300400c4650f200e20098440b040c4002e060342c5490700b8035285d10f0341d205038034001500e45660b855542c500444c401c00040b8000c04128 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 625374712 1250 625373462 625373491
    0x906041706241c0203100c11160f06050703140403061b0c0f150902030a0606090b090106020c09040812090c0a150e0909070305030f040e060604030b150a0506041706 72
    0x140850441180180007003c000040c00d0310904540d0300384242e01201e0100310003000010003c0f0030042c410049004000c0c8180110000c00041c002a80e43d60303030079142070403c0140c3e02e034584081168158054200be404111918040384480e01d1110300820007540034400100e90300081441208040640741a10000e110040c0c0700071001441d928004400350350000c582011460b105008200641036601000790f042c000c2c0c10403d81001010b034040d400341c4840c00c1c81080380f01c81d11018041c0c80700e401e014000c0035a00580100509150480d101d41d4000d05c01d148003030500701200d036510141c2e58295800715180e04a0031485ca8070381010390b03604005001c1d402c010718598401c01000351030550302c252a2802456804001103400b43c0c10014000256840001c80b5500c42c100000040c841e00300340142d00b40d0030165001315a41e807812005036002c0c0da4116403546226228078800c0f21498420319001034105818003800141682e8000190001b000d07030f20b10700001981c0014041e410302c0390080c40001c1d007041c030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 625375962 1250 625374712 625374781
    0x12070f0906020a02130b0d030810120f080f090402070311010f18080c071502061b0f0d1e020c0c211f0e030301060e01080702010c050904020906041706 66
    0x1d03407500e04130f4050765072042c01c0c44403440b00e07005401c062407031607001901ca40005e810540d1080d40307203100343c1c0c1c01e51a0b00c0140380c03102c41e40300b601c401281000c1d001c032010360110400b00e410318008000030318000b00142d14151003100420140d8010314002d0b00030400c00038010413100b000303016884000c40105410004100d00d001d10103502c000c81007000d401c840c1c0c04141508501801c000d0036020341850a0381c1100c0ba01c0c10b035002960b440c0b049501c00180800541514500d6016100baa001d24213001c910905003102c0faa602ca0007403403601406059401800303282e0714002001d00c010054a1141d80c06042c1c060f01c00c01c240141c0304942940c2d1061a03200c000c403d0701610000c640c0081e03030304c90300c0c415460201030340d03a981024008000050f00940400400002c00c107400c0a01d03041d41c803c017070301c0f103080301d54501d070050b401c90b4201524400407900030410081c051404c1e5008000ca40f8004120a09040d240c0c0103410380d0000c2460050310340c0d442013050020b0603501c60000821000c802c1e8845401500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 625377212 1250 625375962 625375967
    0xb071b111f090b071704171203090d0e030c10030501060f02031305040203040312060f0617060108160918051512071215020a09090c0504051c0206040b12070f0906 71
    0x2c8502c111401c1600100c3c502040024000c0070009841d41e8844480d01d5030741758011003840c901a9800300c4203903c998a0071150000f40101981d00c0b0700211000340885850440e42621003460907074030103500d4002d6180700c3c2d85983d21501110b80000c0e89030360014443d0f0402c00060f20068103d00c05106662080c042c078880c00512240d1501620710566015840e52540c0c6420303a144130803071441009190814201042c3d010749840b00800316031290b940e85040060303645040c107004000ba650360740003900d05030000d9020f19805250820720030452800c0e40c500c6613958800e5030650b1068002503000c98030380c801d01420b4040100703001d5070340c00119080e04900d030386038200c00d41d50141441100c0500c1c6c100800c4805114132880b0341106000010340135941c413440d03100300400c40aa54011145018030707003104100310a02c2035054506484001c0c00c411824a0b015401c1d00c3c001c10303070050480e4400c130100004952011108060400c00b001c05042003542e0422420140841c40c004030310030304101078504204000c55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 625378462 1250 625377212 625377227
    0x307050d0228050607030c020307150804060e2a03120309030307080a0b060a030203040b370e0703051605180703020a0c1e150501080a0b071b111f 64
    0x30b0600008059500c40300c400582c1202944515401500480d62100b45a000300030f40b40c0440c82102034801c5551147e040c150000310f50756417140042c80c1c4100040004801d540140181c00c4070720100e4150a02c81001000d40742041c8044440030074452205018504080117402000b0b240c0d095414203518020306007607540e010081c218001c0010200c042100c98420790b0062440d0721340a0b1105545204402010380030351702c155411174045440000043c00c22403641c99903031000740c40350302d8860308003031203807100324100c48c0c0705d00d00d0360b40c1c956030b0102029992003042040020341c81140a030414024103000040d902416500c414005d03085003107540c6070070845000d207650115142c04c0058540c0549002103403281c602d050b0082607007940d070340405070315030002d00000d9500f840780e402041c60b404100c0c0500d05032034080c03281e0b60080d8010303041c51000840069003079511a81c1d6190ac20300d000e0f01e00c494000000a002010b48100d00f07142c080c8103041c10503e4080c00703000e035100c010302100a40d020000b441d54 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 625379712 1250 625378462 625378489
    0x302030a030f031b0305070f110d03091e05300406110c1e0a210308041a010b040302040e03180f060d021c0b0a0602030301050609130c0c020307050d02 66
    0xc942c03802a0742c0403034000d90010010010402088640141c4054040d008210aa94003400300780c00ca030b040c1494500c00d81ca4480d107003203014058040c0070b00303025094000d44011001180c01680c21051401e1280309a040081007038042c800414200c3c6070030039282e000d01c600300c60500d141861168490910340441d0201d404480d814039264420800d4800c6880c2030a000d001c0d03a640c0300310542400104402e1441010b418036204807849804036544003c02c0001e404048251181d41200e081c00c00b020030b0090020319409070003410070010b01e4000c507003681c1031407400360084200b06c08089014400c0d8103240c0b041c2c65041440d000114a0070308010f15104240c40301c9444e441c82845aa0501412610384100340c885128105034155204c04110880d1a8100b00504505080e1850f001555141e40b400c1540c00c81140c41680103946183d0910062244c507a009101c825000300e034a02c074141004070075100c1c008000f0700c69998046a003210303104060500c0590313408144502203404400d07000d030b07440d51044401c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 625380962 1250 625379712 625379717
    0x61f0501020613152405090606040302030a14030c07060f090501050705061501050904020705210f030109091106030a020a09050609031b0301090b07090e0f130609030c2a0b040302030a03 81
    0x1031000d150005000340030140880c1c815078008075071003061507190010000a031241110407c0250391218280a900c0c05a444041d41c103034401240d20f0041411a110b002d0b80440030001c0d40c0c41d020001103001c1c0b420909610a600188040c10f5000d481503000d200200a0b003002d203001c500e08441c54441d180e036503502a01d10b00381d85480489404c1103a005130304503450501e000e48190345450090403c0e0762520312020181000c411914071100508176000100c44000325070403070369400c59081909001c002c003c80301c4200c41c9041d905500b44003666888014621811f200440569a4000800c006200d55030a03031000340904030a000000b080e540115600507010b001000c000344000d21000000c2c00f40c01d40100103401140c140c800d102c9855400803509041e41c0700390034100300701c1c0c8810000003070464040300d5088600c00080901000038000d504030018060280c42c00e0308280045484022400d5007142485520384500c54025960510a00c1800300529940704100e081038070710340110342c5500000200404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 625382212 1250 625380962 625380983
    0x90d060b040f110a09081527010f1b0c2612010f0608070c0b01180e0105091014011202090c07060603050c1c030e01081503061f0501020613 61
    0x3015140c5500c481c2c200b00342400103109075544590345401070f9200c06803600010f40b88010211b8140c2000452503d016111840e0b2011030341e5800c815580d400c903143c207031200f0102c1d081c00240c00e00e0f400d01440029120040000440003202d0f01c08a034011505c50202d428411480190300100b200701ca00c400c020848509080000211105050303558401c0c95070003035170800312800100d150f42d28031240380b040e00d0280e10341b03801d9603d428409075604849144000c26080309040180800603e4011304074102a002d14040780b0000c00b94041c43c2560811103c4040135444210131a007040c10074000d150f590007800306c0407049541418480401007800c2c4001038000c0031021301140c8480c660b28201c2c1e00701da8011074200301032901d034035002d43c80345ca134442c44910404558002c614900c00d030001c0074908540c5a12060302c0390484030015510f00c178004000300840704010400055a440c14402c0521032608003900207a1024260b0400c8034001d1181c0210f81198000810403840350740d6607404030b04c40781d0405e20320792 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 625383462 1250 625382212 625382231
    0x5061002061f090f0504030318050318040e0f0c27060d08070f0b010f0e0606120702030d06030c0302030709020a021207020f1503040203010f05060d1e0f120806010302090d06 76
    0x10000314080e4400c3d018545007442940720081280d014a014a02c695400d11004400c4001d0351402c0022240140030364000b041026600003039210b15210b451409800812544404c011046c140340d112110404d07160044a5000f00d01e141100942c004840102ca0032402c3c2c240705e40307d0400346c0c3e0004198034080c985081100060103a84000d0302c00d1690310280144410200f4940320129401c20312031042e0012868001080300c250003054984900c4000c3c14203410104c40c0c40300071001c204040d1802040d401b081100058111560140c800074500844404c1400c900c0d51042c07518003103003079100070344440c410300181c1c1c180c3c4d5001c90302007504c0780340703101c03e82d10380c4c96500001d044462000d01c0d00c0e03481020744003560130396480e52016522482c0203c0007003142422060200080c0c4100301c603007aa100950707216150006417200d040c216952008481c80a101596640742c1110303418410003138411003803109441401c01e40c0f00403001d82c031820a103000d505001c89130004c14140c07441184001c1800c1c1d181c40818 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 625384712 1250 625383462 625383511
    0xd0e01030510121a131505040f0816170a08040321020d1b080403051b010207060c0c050714090c0315030709060501030b010215040f02060c060a0605040506100206 71
    0x20f45001e00203070160048914000340900d4503c1c5100f5502d800b21000039100c6049032940c00344064101420070010903188410b00e0007410020402c9542110400c41d0001050105024158121141e1f5142030746060f00d0400302440c801003a8515413400c805c00004280e2035100310456003090345802c01480039030044004041d1015403603900d180342880440d20f000a2000c94021100211920798650b0107541a542c01716403000c8e0849000d03011440803c92131035141c41500c180f88200481d04001400c22800760784000a42d03221340318810018001d10081380a104007400a4401000750b200c0c0a1403200340540482d1220800600c0d428441c0e02c0480060008d96002c0032040090744000c098800c07503600c4403401c0340208a5801064002454892044115400002d00070b820150020b815105507a4994486030707080343c44031003245c01c2101440f20000201c1c040040d107001d90a400f5011031410b047c00709000451350001c3c03281d4490f0761000402c03051680c0200388160085c6c01503200321954400c24110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 625385962 1250 625384712 625384741
    0xc1b0304091107020a330f0f020a11131e0204030201170108062205061306061a091519031e06060c0f0501060f180c021212060f0607050a140d0e010305 66
    0x80480760301d41b0b00086000c00341d01a04180e00b20000c1d40728110580010744040340c2e89e01c1200b00080c80800311403080c400e02c0c0340208403d42500c8000d0008140c4e01041c48860300030711400707111140b4668000c9014821984c200148944143c41080348642d41c0d89030003c00750f900c22001e0403510f01001e084e40070f203000081000d03014080d1030b007140c1101c0c458240039107020705900c44090203075146403604101080c090304070b0b20018055030814182c00e04202c188420440c2d0780c0141d0000c85100c2c0400c20440c44413407005550304540750f2140d100024008100301e071a441802c42d0311050310700700e1f141c20014000c250300034580f0345070b8940041d003600344001c5514000f40140000c0c0c12212038040010030010310315200505407141481598001c0c00101e0a02c60140d035901800018085daa250500c0320051110307900c24000d6009400404450001d5501e0002c81c0055011040907500c5030049814034007400030b01c000c20101011100c2c002e181c1001009030081c4030700d43d80300c031280c10503440f134001c10041940c2584 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 625387212 1250 625385962 625386029
    0x912070c050f370b030f1501320403050d0c1e02060a120f1107050c0a031e05010f0603120318230a051203100f030c0e0c1b0304091107020a 61
    0x80c131aa0790403ca040c0d10001002101c00100c00b4643c002d48603919403160b8558801c0340341d1180c985500e1070500100280140307407500200a058010311000012410804c084201040d40d6100c1103d00381007401d002400c1c0c8048014504025560070401c2c1c0181c8802049030b82c00021458800b4207508941003060282040306e0321040e4a50508124a01d8822441c0050007454451b00031510300488682c1804165541440b01400d240d20200312422603064010452507010300c20000025000d6091100d40102c481301d400554041410641c000c030350340c2c0c05210343e414070541c910070000080c0a03940c4001d03104c0c03551081021031100d682140054a00200700385403002d5444800c6d60041d4440d001d9130034640c4c004a95083c04d914000c0c40019241d00304070b140e0300540303402c0420b00900c0c9041072816210300c007000d42a0b0395816010054111100007541c1e021420703203480c102450381d50785801000c3d03095445250184198030b004110800040e612241c94004a804a0000541204804104012801d82d024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 625388462 1250 625387212 625387229
    0xd02090301050c04050117060f090723090109061d19091a090c07050a111f11160f09050a090807080406090e130b0912070c050f37 57
    0x244901c120080d000380040c2d031402c4c0d1f00c50f0311b0b10789240391462032044140c43c201c2d0041164200c169460400300f0103540d00210b9424044494150f040c154216010440c0c08001146d40108032071009690014103d802048540f038105541c07038103c08210207460003090460b02c1820a00b00c00d5402103810000349000300344c1101c080040940d5084d500c590160b1048442d44251031490001d4800b520200681c0c50700d54128004116925850355100500300001065640c0460704840102c00c001110542e40040e044c90790391184807210003042c040c6410510f66a80c5e8400507034182c103124601c0280c10344822191007070400325240e00c420940e8001008031010145c150800064a241440782e9040204211486540c0c2c142c005a83c40c04000c000e0a8283d03082ca190402c03552505022622610303071150494100c10580c0c500c005104040f01c0e1a9001c89000c40d1410b00c044800c1141d864071003a1900b46d11819210b4101d41c10341c500210808107200c80b02c02100d520b0b407244110800000c920325030040e26000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 625389712 1250 625388462 625388471
    0x20d05150709083c01020403020f01080f2206050108030912010b03030f1e222102130e0613170304050304030308070e061b01050a15060c0510090308100e0108030f0d02090301 76
    0x1444c0f1800b039807003804107134080d04000310380c02c80c9035201740d4000340700b41042070303c03860161030304021080844000520701c001d000045207840b01091446c800c0c0d9000f45412801950f641500c0350034040c9000b034002111086900d40312014072280c038040200c42e100016029031668400a030002c03486102c56000b400620020081824540c21a050f11005401186035800c0269250344045441e551a542082c20003100500301d50f140044c1402480240c0d4844603203c00303e464a000e5a00502e4110304495400900e844400740340e09000d01819151903401501a04515618282e265190340740f05070701c0001c080100c42c0c40000c1c0300c0c40c401c0c504401031142c0141502c0d620040c3c02001103401000010040e07565203400e0214502c0362252245030750320103038103034903840407840e1450a0f98140319480060340c05000c5c08000e0b608486040c80780c07849440c4281c8030346040c0d0030010407603002c0300e256400c0440005004401070110880000c240c50702c000d100c4001690300c40c0483d0716100607000f20401590191b0a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 625390962 1250 625389712 625389823
    0x1002071a070c0b0a02133b060f0d020906120f150403031415010503090c0a0b070c1508010515070506091011072607020d0515070908 58
    0x1021200401c1c5000f510700e8415500c4400f011022446a2400c0d070781809031944081180c0090405500c401c083e51200c03a03d8005403606202200c240e520308400480e000a404101f00c528109d4500400700d181a12020b85a6602c3d5000c5500301c0e202821381c1d4030070103d041842d029030104000a610400100044e11805600c2c20a40d0710f042c2d0041e03030114003090600080c01da4000c503400300340f03204569180784040700c00000001902d4650019010305810701490030a5003c903112041d403100140940c502c2d9568031041ca080039003108800d50040085c9500310b2041140107584266501d042d40c1003103074164080140b0b0100800c15204001008145010b403000f000011000800c02d0003107030700e00d40c1d401c0c086003050348400103843c403078100020b00382c00750351000319400d44040420100001c0400c500e245015280d40004100034040d81045459901100c040e44d5889010000f0742c0e04100c0742d04141c0c10041c10700001c0c5841d8001a0308010848690440b4100d1010040c100c045440d085e800564001010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 625392212 1250 625390962 625390967
    0xc121b031908010e090a2a03050a110d0c0e0c070210080609220305030901060b040f150309020d030e130204060c110a060813080c01050a0606120506031002071a07 71
    0x80c050000414110750000400202c08501d10344a20b05c184060050344d00c0c1980e4500301d1100411100820380d4580160700c2c0b0020407441c00e8405180160f0013040501e480d450310701030f0382e0004501280104200010400000d1080c212a815a8070701c030081001c90ba81c2d83c1103600c1030300452901a5101c2600f182e105c1450f0340100315180110000d845004860743c42c031844d5004800886c90030052001d82c1c500d50b60110388500c1c00785421820017000400c1c0c060f52100e2241c41c580181d0015005000c882c10201322640510000000443c9541401e0040c640b054000481e900c003a48405170902801d1a214012076680d60250203403005801030864a1b90784402d00204404110342d000c90301c406080800043c40d1924010402c201c941135520100b01da1354240003034100f14008001141c00319400d011100d2020801e0007150f00c5054800000543c1f40d1500c50000c1c0030118a01e4500300031403500b01480380544010441c1003d8441d041005a03071070405217420406507107844100511102082c060111495 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 625393462 1250 625392212 625392247
    0x91a1801110f010c08010806180d030c20011407030504050c0913020d20010c0f02010e0a03050303041a070c0314160b0a05090634120c030c030c03020c121b03 69
    0x11f040d001110242d9407600701d140b500700041c0f00622826400340d011141003e103e0740190005c3c54581c80c004aa40504617070340e11b0f56802904e00034503039944803e0580d10f005c1c109140190300101c14901030000b0704050300c500743c580f4107140c6a18000c0c60400c2c001a200d400083c01d080c60254080c00c20307170b0160060b0501004090320080d0f40644010b44000702452980715036014240a9003001d146031748509641d0054924041021a285e0088980d49002000c25414001386205501600e00d41c1c0140d14050071400703198400804000a0020714503001000c0ba500c42030900501202070282d542d91030409a0081255444c144002e100040201c02c01040031031540049014902000032510203445002c504404c51780c4480d2401d0b019440308005000340680341d060b066140c03400341400c4040d103040c150300005461030a108980443d4540d48100801c1398584101c581c8101c1e04d207400c6050140481c00191900c40703d0040d40542d0102042441a140c0012a0820310107000c3c401c40e40d07900341c40d640900c01c09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 625394712 1250 625393462 625393469
    0x320010b01030f060302090a0c02070e04060c0801051f030e01060803041202130e0a030309061107060c080901020a120e2806110a0c061d060106091a1801110f010c0801 73
    0x183c1486010501c020300d0f4000c800603641d009115404030360310031300030400a0801030141c2045109030240080d4900d0780144041c06203004d00710204240200d514040c090183c1a400240124000d0000501c0c403075203060303035001c3c0c5005403a0108048902600f42400340016401c81c5c00f450000040003c1e101ca0000a60051580f082d500300200c4070f0048550411101112130100540e001200305000080c883d07800410041c2c0b00d0030000410440041704007840c0e80066030304641c030641d110f61041c0c1c2c050700f07c0d00c040d5010201ca0700030b40c5040c801180050401c5503050700d0f0701e03440361031380151648444140f20300c481d8500d40180b41c00f01200407034003c1105100c1c2c44402d0310018906110580d9a4955404440d0310340325a4842c60300504041d505c0e0b00c02070940c2100786445001111488000e0901442124020020703a0395070060301d402c1844146421024600c0c00d08003040800100254501c250520210b240007400c0621040c00c0e844682030800341034084860581d4030f000308507401160080c2409058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 625395962 1250 625394712 625394717
    0x6150307090e0c070309150c0f0b0f060d200105072135041103010c020303070e030a11060702240304230c1e0406080604050d090f030f0320010b01 64
    0x152192080c4940f03a10894501800040410506105a01200c0103803030380c202c41442c20110802241c0c580460b54901e14000300d0b4440403402c1403285a002e4100040d13044417003110703440f06204980d51002007a00b12014914080300004012408030fa010360151140140c001c5c004260044011014070250000c0080403004182080071103480c024200101c20101605282000c680030404002410074040003170088804c54030100c101c24194a00b03000d01d0200945540066440381014100604100110301d03000d03000b03620840001020494148107005802c0c2d040e0b900903038500403400440c80a545100031403a000f03c00340128100081c0d031400540c0301310701880503516075089900c141504c110005103080e0340c90b800b4400d108518606546195150308200d0904124003d04401050a460703142e4000e9480c0c5c2c01030700410003404000d01140100311841c0c94200016030038950201680c400b1408007a20240c000c41c0c0c0042090b00070011005401510407803d0301c030049065045000e045880c1c1880d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 625397212 1250 625395962 625395989
    0x102070b04060504061d03010914070501050c15061c1101080a06060e192c1305030307050f1201032102010c0c1103010b090c04090621020103050615030709 68
    0x102040346005541c2074074110364032585030514005c011074400f4000c202c03299040d18190515100740c0e90034031500c820648540314880344001400b0f0032904020300b40c0e2019050007410811144903d80100d806510030140d10418600754441402148404540d12160143c100c1031400c00028001860030414420700260307540c03062541d034405000d003a540240b0503000410018032034801c1038606400c0202d09003c2c0b6141d41c92032184e441907a01d4100c0c82403c2000c5203104036524110140c5044440d156002c20f02c2c0640750b25030000d0340e6503d5035a110043c00c1c1002c202001c0340e26404075041d0021100001d025101c140702c2941c590405c80c0303074620f140400e4210007010300d6103020104d0042c01441070b80f001a85400e200e02003036807075440f401c10000d462160305550324034081c807a0703036a142182e07800b8600312840d01c0c0e00c0710304000341e441c02c6454581201080c442c0900c0d0346884144041d03100e01c64581c0c2880d0114244e1181c02c00b18161802c0140941c0c5160030101c00c00020503030010401c001c07203188002920 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 625398462 1250 625397212 625397219
    0x112107110f010e041a0402030c040f0f0503070b07150213090e0106062001020f04140111190303020c150403050c0709060503030a1107090501080313150e0906210606010207 75
    0x2803044044507a450100b50300003115401450660310088481c44101003240b003901107500028100e9004403800c07039414801060620440202540c014041e0015050a034940d504210010340d0304c4145108942d1090800102141044280c107040380c481001402e040d5200e881003040c1000b1032a10f40207149019107004007100144805006060071581e103520b07090078076080c0f0f20742440b00c0c00507220000019902044200384e9804a24000d0008028410044001503110800140001440b544000c0540e2181c21340c3c0d00d840c008203188406140e4103040c01a03030752582c18106030500300104215a40706000d08200818160494000e212036038a4000b9100c103aa254400c02d0304840150140ca60550320500142d80383c40e00a911301040340421100711903816a5031500441038881c01d820000c07c0d0b07000403070b182c000c0c160000002005462405440241d006240b4801010b00d26501455132045400c040401c1072502c46503803594404000140c01001c0301049041c5990315070083c3c2d2a20300501c00d410000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 625399712 1250 625398462 625398469
    0x1512060f1d0f0609060d080301090501330c0f020301020a030f05011203120209060c1605041d0c040f060807170f070503100911060c15160f11210711 65
    0x74880d050360010b08419444034400d01a11907401803009800c4249074240d900460f0030940510300a1050030004a52507050050700510110a40680d51004400d450603c5a2400c1c2240115051000d81b801c3c03038030704089040c61545980c07030600280d0154800a40a40d049501d50042002d40c1ca8414040c0401c1c0d98900d039401300b080740144040c000410031313074101f002c010842d0003c2c002548000e00b5141031002044555040282c03102c0c1c0b855900700c1c0c90384200b00d2030415005181d0078030900ca85400c00410601401c81c7c035260b91660440c8034640e0b0305002019204160300c18005410400308a0340600e4640102600032004001d89500d00d100742402c00e0100b440008103007003501c1019001c1d20f4007070514103581001d04004102120b0b20b0f0100b40c00c0b58115100c400c0a001083e0454004110031600e0000180c00004094a060300200d90000105502a041202c0105d44103d03807a00305005c402400d03007142442d10540003149880405102450301d801c491019109280c05015101328421108040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 625400962 1250 625399712 625399769
    0x50609120406170a0f020a08040605060f0f0603040312060602101506050f0c0304050d06091b08070b07051203150907030605010903020913050d050a021e071512060f 72
    0x10b1400040850304070503250350341e207000ca0307800911003400030071540d6048901c90160303009050010001881e0400700302c24800a40120368028405642203101201e40d00040340c00380000400e0a170264600001140405114060030b06520000d803c0410001d6105c00009440301c015128401280e0b05000014a500300c2e10080b041c22201107449182c0ba0000b0b009250f58140c02c504480300d43c03400b00380400a2161901c0114481d02d6114000016505500303103420090b50710959a008800140d005080c4421140001c50009a031240020b840d100c452524082e81b4100e413400b6401d00518002c42445284968031698500300318045900c4001a5a001012001c585461080c40c0c0020954442007005d420542401398000340200f04c2900214140d40340c0034688130070800c0040c00034034000380b0f0488055040c041c00b6030407009107030041104920301034003070344d5500749010f1a95071138110546c5000c1c003401610282501d8410079014404560b03907601c541204030036803140c0d0000c0e0780d1100340065400b400340d10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 625402212 1250 625400962 625400969
    0x50102030f0d0b180106170a020a1d03010f1a040c050c0d0c1419020901081908030a060e0a0c08010e06030a0f02030c040f020304060e06090714030709090506091204 72
    0x10705909042c03440140c0c60183c011038600941140c00d90101c014014020f0084c81d01038419500c0c0d1044140300e10703102a00303240006040d03540082c4144504040f00e0f611405141c0c001610b810740c030040f110700d000080c2c018a0105280c4102f030b8a8141850800e650308244c001c00902c6c2118204030702c5542000a4036544140d04003030880da00b08070860320f8810b001e4100441410302519202030fa1580c0d0244052800440980740d0b0100c0340d0103804481140f5041f000140509041ca01504404461185d80201030b80201c01c01000c944011002400803000b503071221b0014913104407210b0780c4e42800000030000f860700d403082400103a000d00020808000d8416071501609000d0020000003d0540f100b5000401c03000d030132a8140181c40c0e00c80303800e80d01c9000340001d100904d11300680d2070400d13141560480b0050100045650042c00c200600c41d07038046410800c4480080f0b0561001010f80c001038100842e58002d01c54a624000d03595040c001c00040303e903c00c1d46048200c41d800541d00401c0500f0b80128131 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 625403462 1250 625402212 625402237
    0x3050d031b05030c13080f250302060d0b0a03031205011a030c13080102040927020121140a0606020f0c06041e09060602160603050c0d050402013605010203 68
    0x90000000e240300700b0007164400100b14040e030810f108904541845409a401180154489600c00076500c806203c5103542c4800560000341d02078018003890b503581110f01c0302a200d4000451042d000340000d42050b90760300300050002c6003181e203d24002c1c0040c480080c0d407101c81e614010000c1212490304001c140c00d103501e400d505043d40e88101c50705c0301c03560000b1241c0c0e0b0b058201308030000f1b8404090000d480600a650b00102e0405a0b0703414401f440b42010401c0901e00d83c5c080c8401c00544d800482c01004a8111203428480f03410500c10300000d0a10716103101540100042003010040c02c0341e0001090312015400d4070040300101660554462031221026880380e010801040807250304100304440c00708801d00030b18006e58401a420031105a0f90090006d6042003002214503524100300c20701a14550504018a0402e4403400002d0f003d1000542c003e282d0700e0307022a056a0003a0164520803001000c0c0a030f10b502a0320000160307140ca1f88244006940043c00812a5800407080d65102030507a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 625404712 1250 625403462 625403501
    0x30b0a15030807020105090301050115020d080f0c09060705120d23060907090b0706050405070b03160e01090e040c151103030f060d1203060e0c0c0619020c011503050d03 74
    0x580b0340d4200c0b42d01881c412414031a08000a194a803000c0c0110f034020300c812801e14034408000c00000e0b00b000030400400007000501020899407082c04901180c004045004180c1ca032241c50021404501ca41030380500140b25428a80e01d03d0f0113404010003d84003401f2082c0000c085100002ea411009944618861071070300001610300d041540c0c0d0a035001e4414030380a070405548005c4108180d00006084d03450f0707030312801003105102040210400070100f04402924500e0100d9401132031040211007201044202c048010f910b038403d04108000c0e206443c41d041250410780f502144001c036610482d00702c2814100c01c900e003280100c400039140035145005d1482c650701c114040907080c1005000c0740d88a4030482004001c81c4036041400d13854159502c00080c5207051101c14180d44600a00c403d50316070040103050f1542002248280c0c20814811705005403145610808001e405207141028042d03103010b5200c00c4180041d000901103901440980c1c210145900080f0181e0768090114064020103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 625405962 1250 625404712 625404719
    0x50c0103180b042612070e01080403032d0c08090106050f040b0d051203070201270602090307051302070309051f11011407110f060411040c0203160c030b0a15 69
    0x34034115409881400c51220812820740d40e00c1513501d0003008040f0720000810907503461001e03940c078944c10500c1e5040c60084c3c60082d800007070100c04000d00040c00c0545400d0702641281d0100c1c40c80d100103180410103646403151090240c0103004040c0b0b40000113100b60b0200d0741021061064a068840c0a00084c440004000c1404080c10081c00b03071640180796080ca000100d601800002580c1900141c220b5480c144804000d081d2581c0d0782113480b001111a44010035000701007900e0240310350000c40561035255110029082010540c00242c1001d03841c502d0540d0f40304d9690003014214806d40310f503140e564494040c4034491420441c0c91203101d00d00080d524029000b1414024a180504000302d0051a1100265080340c5c0aa8004004c0394245a0101e40030384207005826921050381c0007405145001c3d2100344224080c03958045c0141da40d00f544600180c424070449001c00d442040000d00c5502c1c40c5804900e101e8144410b444031050b66000c214074117000e0188224030042ca07500010820f06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 625407212 1250 625405962 625405973
    0xc210403122c030d031d030406030e06092806090b01032d0f1b0b0409050a060902090306060f01020a02030105160206010b120c090a050315040312060e011e1e03050c010318 75
    0x21030011b41c1c003074529844004a24036082009001038100c80c0d5020a13602d950f5490145400d201400070a41904480c3c4070f42c4800030281010740012541c1d1523480b0018415042c001c008103203022000d0300c0c100102c070000c41403103240c6203c4640032899025002c01d40f0150f90500d5203000001800800b210310f1800c000000c15180f03020013444a00740440d4000da540e03100c646028550040d484a20b80507125810010101c2e95441074a008000c40c60041d8035244545000a4403240c004101074803500780d078980120140d108000603061301c0c5c0e0250082003039040c9851100680c00f40c42c403e01e070052107034100115035041d00500341c400207006031074000300c5500c4018868240b40c00039600160094811840010207580400040b005035035034400c040303940c0c00c0c2801e0007041240a0a0161b05242c00c201c4200308000c0442c03189411501050b550b01c05400e4154411800d0301c0d4158040314900c841d4034400c41e03003150f01c02c00e0745003202d124800310f4a4003495440190140c600080e0240301000301d00043c03402080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 625408462 1250 625407212 625407221
    0x8010e09010e0d030b030d0e1c05011b0905091303091503020706090b07030f020913050619060206010e0115080a0203040c030210031a060c210403122c030d03 69
    0xc03524000b060003030100d48a203203030020f00da02840c0000c3c0c54001108581c00c05006000015030145000e01c0c0100400010802c0c800501d00c03041c04140340549c2da03800317200c2c0a42c01000c0310f08009240010580c0ca14000400403001401a9441202d04002040b5003801000c3c40d040c1c010b5140e10703200700d01440c0501102e140c00f5040e0105003803503000c01ca8040021050300c200070b02c0d5031003041118154203064a00500312284c400b49048070030720400c40c0300c2f190394a080c0c2a948407160003101007515600d10f0003141c0314038180406240060348050010a15130b0300814003905031180110a980981e903102281d40c0f00c0350080d203180c00840c60007004a8010400e0343c004690080c0160751244c1407640d2640401e118040480b10400006d9071076008400c0010b83d40c552071700c0b00c84103c406500702450220b00300d41341d40504103c1c801d062000030008003200c0c500010b07a8003d43d08034915000c50103801c2e02c05848040d80078150403c4110303080d11801d00d4102e6414030f690143c1c0180003800e00c111714800940040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 625409712 1250 625408462 625408471
    0x203091e0c0d0b01140109141014040806010512191403090a0b0a03060b0f0a0e120109080306040b121b0307080115090b150703140c031b060105030a0308010e 69
    0x740a034144100c800e0310785040b0816194465404401c4940c9411007058810219803581030401105910401c0001d9008950042c1d010044411280c048140d032810384503101d100d41c020300180c0011800150350240401c10038100c40c020f03116410212404402141c80c0e602d0f4440910016540540314008106030303c100002607044842140e00e040c030100e0000e903100c4516400368071480c10006410034080d5050013020300a054a40c1442d041c100128450403490081d0b000200c10405211400380c1280d075136032242030350805030f14000c022010150500380f025a100b214860b000d2810300c1c40c2c850132400c3c0b081d001ea003400e4901018125280d00124154461109003001d10f0b818821240041007000c070038812071400e9a80340e50304941c00303413400140d4004d885119034001d10038010000511405030f600411030f1242680351401c00c00d40702a103400900e43e801400d420020501c00400c401c0f411250742c1d004c14854000c002d04841c09a0303a20f0701056660b688441c0700030002903a100040100091448125811 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 625410962 1250 625409712 625409773
    0x31c02031009050415060843081b180610021c02060906060907090b071a0405150f092a040c0f030f0209061c0f020406030b040e01020309 60
    0x40740e0b42c2d540000240c0d602642c1c05c0c0c0c1ca5a90098166681320300510860004064100151426154550200304a40c10f50100b0b1417000f80c2c5c0394500c49140300e807600144582c0030007248a4480c143c03a80707039056481e6000400000512241c41c2c40c2191482d020314040d645655030031022405a0b100828800402c0045101a041d4441c403020100341000e0fa0074054a4030006500802451506581462820320007a0000d801915154180602150303c030100c01c05880c1c0342d80c000c035510074035450707c038424503451070302009005100410302c8100400070a0b180043c0281c5000d0344000c2c0c4401803a1015140c0c103940183c0301c1e9103c100d62801005082e0320344200c07901c042c42034030740d1079100c10f011070141d403510400b10000440b04881d017580d490f05442010783c0a82c40300c00c11410b007580ca502140740d600c00c543c046150020060381c0c6c4024440319030020031040700c00090540d02c442d03039000041c0161484460319032050707080c019001c014082c14420781c0e104801150082281902d01412401c02454000320707040c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 625412212 1250 625410962 625410991
    0x6040605130e1503011103070c0b09030c0a03050a022e2406020309011404060c0b04020607050d080a0e0a02091f080706050d0b030609060604020f130b0403060b03031c0203 75
    0x8004480100c030b1403060005500c5424110510000c15003100c20494416214907010f00900680940c40134512a8290b40081160b00945510304281c3c518010311040c642c03a17110b022420000c2540c000041c01601301141c0807130714203014151141040c0160a00c1125850b800141c0c1e0380c5917400e00e50060303d02c0850501c0c1d01c1054103189295101121170f2600070101580c400034444020756880160700e24011310000040f4201400d06e81e0007030091755968006069148004d0202c0c1c25507079020304481601c0c3e4000704451490a00390006840b02d58222149010685404800360000c1c00201d84d20140a6005080441703560310f580c5421211207280010725404411040c000c200746c10b0400060f8080c01c00d0703841e070a85900c4011106803e032150100c0b02d500a070094802d00406402c00141203801000c12200942c03900c228100c010918010345080521026240600144c80303269600140305482c00b6100a202c0900004203040c0e8038420b40c1e62250866000e00403070840c18819074040c50704154540341502c3d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 625413462 1250 625412212 625412219
    0x62401230d02280e0d11010f0e19140a03170d1107060207060b040612021224011d091903020a0204020f1b070506090d111c11030303060604060513 64
    0x659107428440d01c841c07440e800b0601071801c41d0304480d08613011002111044800390403581e802c0100c9040014260600080703400c205403060281d0020a003442e800f5004507512042d0b401b03a0039480c6030601c42d560503248442100c180034107182c0c2549050325000111420aa006182c2c01c3c0140e50017040b00e110071650741e0884d00c0040b0035500041448600034500561140641c0c18504212800920628402c518040c03007040004003440e00c02501a804490070103e02d1038035801142448101c3c08864410105200d0b0f004104800e10300d544c1c180c62803d1000c146440c4641d0a000c0e807070310141ea81d81c405a1000b4147c42d0740a40f501100c85446100f403040e5a007010440e4041010b98225541a03c2c01003004101c800c1d00900381444080040f10b180018070400303180401080b518816400d119020360350300c001d02407e00c44555510301c0f64402c058501c40d0000c0314080440c54101c1c0c0c03c102140c14215a0200d0466403034000182d90007008014591440d1031314003c3c00f035565500c000e81d9441500b09500000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 625414712 1250 625413462 625413487
    0xe090a020a26150f0a060510230a14030a0207060f1b090b03060105090609030609150a0606051c0e100606030f02041d100305062401230d02 61
    0x150007485004000704800044404410441055900d09019640440f2050480c91105102c082c0c0108908200300a00c0d16008800d101900b5144c1080d908194030006840100741d0040840d039800049010440034501105034040f2107224440010000414100c6041c00415102c402103030401c4d0f154400518018095840300107603224082c000302000d94526440740d01080603d82c10480c1d100740e280c4802000c5c24a038003000e5a0101908841c10400c021681072080d4468404a0b01e00103c02021500586081c0d0042d5540e0b44448412a9020100f00c0118802d802c1c180244d03c1500c4141d00c03030904103d0390300e2080890941161641050580301d0b0300740b000344e03441480990010340403044c011071101c0c2040f1002d0309448208108041e0988100010005810744280c220141580c10500d20896110400f10003072032034540d08003424500450040c0190070340e440d400480031145070074454003441c40300340c01594000d0700c0780e40b1540c04118501040c0402d83d1401c0051a00e80c80c00c400043c10608405982c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 625415962 1250 625414712 625414729
    0xf0906030312150a090507090e06041d0c0f090714030a0603200306010b090319020105040b1206030111120403030b040e03070c0f05030d0f0305041118061f05040e090a02 74
    0x303d0b2002468030702c10042c0d81c20b140c0c0482000c3c01300240c0c20310a900300350307600801071000351050300a2a094003000c100302e0765894104600d5100102542c12a440401483c85d840d1030b000c14055200300043d840000c8982412400c003031103016641c46450002500c0d00614442d5440108441a05c50b91090080b00050800c594540300509405000b03000105c0041071529225044e040151400c0d810300c85c2829030355000400c8007440d0042c840e44803c080c2140b0050740e0314050354000c45040500410b14440359036100d1320441c821241100240031300100411602258072a841c401c01405500c0e10010700824000d0304107140222001d440010550640003409081d600071001c11038041b081030360100708102ca080d00c00700180600300d01400da0b8580c802d6000c1c140058403030b101000d0540325400a8180002d5a8001155020162804c0786850060740c0e41045038804451040c4039109841c0c460010701c2c0c4142c21300d0251101078440e28585800c0001602e41d81000074103100051040758010001a10340f500c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 625417212 1250 625415962 625415971
    0x1b06060506030711010e070825030803010806192c0a0819080a061202010c06020d0207080409051b0f070501110c160e07020318040905010e060106030b0f0f0906030312 73
    0x1c84c840d4120600c04010709503130003c40905229800054140b01810021903010f021030008100000c90301602c44000e94248525440501040c502000018150070046a101e00c60060210401180d220000500c004c54080c0c1c02d004003550170703041c0c07403403822340c0d10002007041701001400b11201071a040d91690344951140d01d0125211120030b010006103900101c0603500310000030000d000e8036080111154110905103c041d040001744510b00051140e5581150340c90303400202d081d0f541d00b01b28204116182e1051041440040c40d00c0d000070200c1405954045690903040c0c1003520704400c1203692016900030880507a5155654018440100300d220002c0c08024841c1c005480c07117032040a88081c2241e10b5a1146038a200d51100708410320358040b00b107504408a00442d032020b51401c0d0b01040080118400042066182600f1522700c0b540c0043c0c042c3c1211643c1c0da003800700e031035100d0074017107031242268180d90015040641c40a4510741007041541c0304002a013201d0404030030f040628a108070030755 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 625418462 1250 625417212 625417217
    0x1020c03070303021b0a0315050402131104031a0f041104060b03040c1505040e0609070c050307031e020a08040308180d0b060406062109080f040608010f090c1b060605060307 76
    0x8456403940a5240700c0d0303400c043d038201c400106c0c6510390f8540c121030107039988083e0382c0141e450000900319900e4607189074180f0340d050b604001d06110300003c908507500c00d002c1a106c3c01062010080b180784140703903a40c03151602c4100d1209a0f20359a807403c000d1000340218a0b809601c1e124082a60002e00000d180714a01510601454528101c040481700040074000000c10074100302c1440222240c070411038102200f84c0b42180b46544550007102d0004c180da60041080c0000035030b200925502081440c518002030000c4110b604c0da404d4141d9549070952801450f40d14240300400110307000c140a040c101906000640003112480002011540316801c126071440180003446014101445160080e0203d410310300d492260080d900d40791079050b55965000e0750b8a81182c0001c08c003075641038481440d40c5501440e2145d40760b90707000d0301c0c0000900944480c02c1021170006050703401400340448000517910b40303030b228200c02c2c05c03842261500b2010940e100f91305c0d240c0020b02901c031000218462180c95 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 625419712 1250 625418462 625418473
    0xf0301090b0103021303110f0904030c02030c120a030c05030c060405100e0c060316020c040c090e0c130b0307030b0d060b0108280b030c03010e06040302060a0c0806040b01020c0307030302 82
    0x45280c011600c848032040c1c10140b050007000e07844c0c102c2c044a107080e00d400032000064000c5010001e179042c480b1204041d0400c44400074002019040750120a896100b00c081e035400c1d2064030144290464240081600e41c0c0c410322031540864020303209624040d0055060303901c0d01c41001246440c021050707030201d40c40d90101a00309009641880707108400f00d1ba501c0940814120700c00000c2c024000036101d4524102d100b2100d01c030281c000c005000100f00007034800c0c0000344a0076005004030801d8402d42003452020000a035a07980503504403410b000901105995160401d803c80016030001040d5070285039540c00700c4001a598072444003080c40c4900c2000c01c0030b0301d18100040c440038004d004519a600901606212840300c00a101c0010900c51800105000c1d0600000e140510044d2800d130554038014594480120110b03000e841980a5000c4582039100c031000d500840b1000d40680f8001030420b4013182e0185031603003107250004014812107a00000d0755001a0804d081688100c016038042d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 625420962 1250 625419712 625419719
    0x6060f0509070503070507080c0a020406032126100315150e060102120f0706020c03040314060c030621060a140601110309041508071205122a01110f0301 67
    0x140c5207260340700005180031030443c140b41902510754000c0c2400101001c41c040391860701c259007008901c0c0915001081171205a5403030820521000001315180da08032001c0c00d2010f220703030103445a4244841da002a0740c500c405508445000c1960142c03030449060401c01002001c25680b940c000e80c015180030000038030f03654407a0301101c2d16490380d000c0822000c42d00100800d90fa0045001e6200c3e01002c905a42e41d480c110b10710840502c03401e800209000c0c80801c800440780300010103003058a01c54680401998007000805075a10003c0300d086912100801c00280325060500480c1c030115201c440c844030000034030004504000080342d4031005641e0341d01c00c1a4203050100352140d00010207081141400d0341c2206401d450f4800c1203501405251540e5088901c4040c0003011002029100e00f952450751705c4000003403081ca680c00098407144601400c41c6001d040d441c00702e1b502007003d014032010030002c04200b10502007007001030a0701950303168054020032071b01000606400c2c2e50b080c0e801d65070b58103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 625422212 1250 625420962 625420969
    0x90a0207020a0605281704050708031308190c090c0c060e0303041a1006052a071a090f090601110304080a03110604080a12090210080f0f270a06060f05 66
    0x25105e21000d80b400540800201103402010590b084002d094500d20f0a54071424001d01c0d00e102c40d402060305200000b02d034419a8000d40301c40007a201810140da0840100d4101004901c0c2e000d030001d004040c103018204503e01655100680c81c80041c1441c0041c00720036103600e011100360300c1e6400402c0d040001003000300501e40c02e4041542542c0d86054100e410800700700c5807010910b0143c0e6080c0700c40020900d100100100782d074640c41e450402c0311000b600d001404030740c640a0510070758000d0382c60400301c2c5078500e00940a41b108a0340c0034000c40385003403240381040f401e550043c040e0760500ca400d01c00c8509545003480101b0140282e03400034100310342079180041c030880d80c0041048498200006000000e0b19010403200c4d00c011038604640700302c0c10404000300a14220000a620020002802200ea034004e09400d1140c90320084258081d40c40c0b08a004400c1d804943c50104052588604511420380110440741c428109003264801c941ca6600e400860b80d240d0013001104c05940010800ca16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 625423462 1250 625422212 625422247
    0x30a0614010801152003131d0103081c1404050d0905031504030c0c08030403030e04050115020a03031a1804060c0c120507080c06190b010509010c02090a0207020a0605 73
    0x20000c1c6021129907160000c1c1c04c07101c1403020751407010802009414031101c0440700c080d0380003826020640307a8502c01103100024021440c864040014138021034a80070340550600c42d41241d410030a0307585402d0b084001c442c0700f142150700384c400c000d9966030610002049080210302c10f9115800411159003003140c050011100d41c0d20a9101e0352041d43c43c8580e03c116240f83c160041d80c1800c207102014400c0c0342145500055030802d80282c03201003000024180d00c101c0d48803040301c0585e0100f01c42e0b40c90308002d422440e00b408440016902040c106000030740303e40c1c001c0750111044482d000062180c81d0009446428070411b508050b002e101c280010320506110702c1d080b04101d4141f00f0795015190f901d0954004101a42006110b000702c5c0003c284241001100e00141500301078503803130f29000c100050461014004c92003050b103005102601d55010340c007241c4d8020416114046250010760070000f6017070004001c0000b4075004e000910060f1114641000074200f980c0301c2580b10300301c0b002c840c0c01c0074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 625424712 1250 625423462 625423499
    0xd0c060f02090112092429010804032a060b041505030a0f0609060f090302150c0d0504050a0b04050303010611010506010c0602030a09320706020c01050c12030a06 71
    0x600c108114405a070b00144a1401d0780803130180858641154105040c1a000c0401c1c2e280b081d0f03214082e001d00d00f01c601c0e806002d910414040c08a0341d0384103802c640202c45920540316000c0b4081c9808240031034080c2d460b07400c00d0306484c004480c08190444170300440c403610480031900e450b16964650120f14042c0a114070103010319898108051511001943d50480118041c0100e18140b10300b000b07000150300710301c2100703801040900403801656540740041090741010b600500800d03c3c0c011915040703c003141d000c1c429030003125081481002d100303801884042d00480c0c0500c100303450400041c03c58100588210300500255890b50301d000c802400d5820701c00500001a49000d081141c00e030b030800010008603400120068407a62420b074a1401042c00b004060312058001c6c01009101e8840300600d039400c0d40340c141000400c0440d03180e20741e0b914002d014138405600139558051544d4030801c05000040d900d1421959124441807001c542c950058901d901000c0c0c480d10207000000c01c40d500c18001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 625425962 1250 625424712 625424741
    0x3020310082d0f071701021e0409050a050403050301090c0905120105070f030603051203040813090606181d06060d05010603051b070f0b0a020f0f031006021b010305180d0c06 76
    0x41d83d0440481c1d11001301d4000d94440300035031059480c401c41c0950541e00e01030301c6201200b88030181e0b803000300c4090b00107200c0c0c55111402e2400196041c00d640c043c02d230061b035041d16040e003143d01b880c4c240700160950350301002c05c0210200000500b40d0b1441c0c1034462061480c03000098504140c00001d0129a65201c11824141040c5041000890000729058498010102251a81c40d0b5103044107030780c40758902c40012040c11035008942c1011540c8404100e821a40f25003204142c0d009060307080d255584201440502155900d41c1039a0340d40300301542c0000c0080c55245003100c800400d01c100d810a82107803001980d684c0030840241043c0384141000030441440b941041c0869860901c40c03c1d16a4000f04100080c00203d44215400d4055501450900c1c203441c0d1644004401240250406c407403a05080503a00700c00507407140041024484003002204e010000c10168006501501010f840c2010b40400486412034030241032104481c00032320b0741c0d5a8400e007492820b244040d42c01e00c1140c0c452 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 625427212 1250 625425962 625425973
    0x5070c021f0e10020d23130e070c0506061c051504150203040b06332208060106080903070f051006080610050f0609100c0b07020604030f03020310082d 66
    0x1105800203017200e456041454540c0110111010080c42d40d000c1900c850b00309100458242c001c0d0340904515016981c14040700c2400307542d200003c85040d158400c003e00590064004511582001070004060000d0001d00d05c94082542c1c3c0d40600c4c100801e01102112030243d4144400c0103502c01e0200cd002c0481c4000f0f40c02c1d420151582c0c1d03c01e17900a48402d01c00e0f0540e112480c035800c0042c1e074071511070b11016200c6a80b6020101d0150b602da1083d212480754000104103d220000c2d94144101596a00001844141e0905e4400d80e103180d80640b10490074401400315400040c64942c001c038205100f2409000c00b0301240d0900d200b6640326420081e06034000c41c4c1000807402d8496144030454104549010609070a0b00104425104d00c00c8200c0d04680209174841219070065140e08516205803a0b01889549140080340c45103001c0c0d8000380002d0383c3d050242e4800f4880d802442d001000201c0100c0416134408405241440303840350b034035400c01032120350482c00c3c4081d8942003194000001909 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 625428462 1250 625427212 625427239
    0x30515070509040c020a06020301060201241208131a120f04032f0607200102030105010509040902040b040608060a06060309050c040c020f0613060c0309030c0605070c021f0e 76
    0x14510b0041c812064003482d525481000e80600c204158003103150400021035980d611540024080c0144610510701c890002d11a401d000c1032200500045840b1b0350500701004075a6a18030403503502010802008900117a0702054460048603001e0100c41290340c0195a503180d1031400e60400e000424919041a00030700700001309420400c942c51482002c042b00d1040039580381003003502c00382400e82e82c405103e00020410050f811551204079a110060744c0d03450490044140d07807d0384401d003d01c50000c0c0c000c0c00503020341c0c20038ad003100424520040010580a07041030200e404c507a0198803403a0340b940701c4400e02c1041c1d4443c0c460440a40440d15003404842d040f41c03240da81d16a11242628025a551400d414074240309004103064105902d040d10258203005444440d100500c01042d600f01e840c00c8034049440d80240b007580d16059158442030351141043d22000300400000780103605004100b51a4801641c4140710a52042181c089445001c005043c0c0148503a0484450500034510000200c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 625429712 1250 625428462 625428467
    0x5100f0507030b0a170f1902010e030f0706120212090c0913080f030408130303020604170313020f010e150301080606010c350304050d0e060a120509031b0703051507 72
    0x1c01e866003600305e005d022081e034804600c1d298034541203403c54000c5d025a4188506d044003c1d40405000b41e03684020310041001f09600e451039030368040c042c0e0388080cac0e0820407103024680c2c40601c03004c0c0500050600212000c1d2004400049544c14095080190704650303e20b4402d111541183c010038400740392502c190b03515182c52095001d155214800840040d04101d0301508541b01c41d621a204800d406503227160107940d0350000d81d4200c48148501806064401c008015244100015050070380c1c0d15034642c092200074101250054100201d0569601580d118842a4072414008181840c1d0302d41c50224890308182018000704c1c10041ca940c031220200d040e0307160800442040040f01c440080c4524008512860403040201c1c1044003c4204004e219000c26040c3d02c448007901c4030b0316209180390400440340f10b501d0810010a6103d4203d001c4e10401e548150f50100544013142e14041e94042000945d10000e000710449034024142070040210501181d150107070b48820725801c504114002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 625430962 1250 625429712 625429729
    0xd1d010e01180602031347010302010c02011218050708010e030a140c0a110102060718090c021501030507030314030106350a0606021506062505100f0507030b 69
    0x80e0000d130300840031502d0404074042c0b01c1c4401d0f41c0300b43c044880601c00e10f44e4518410701a421a8041e800d1400d11503142012000907021290000e40d03621290f03070855005442900d01d0407000da041040803945002c184540c2d220321441d4044000d0000d80c402810b1602a2030207145e900148440c1e41810001c030100d420010075200c5000726400d000c4a004450410302005010341080382e1030b544036525490091001c914803880711a90700303900f82c511540d00c500c1c060f2807102040700002160003008404005008a40d80104283d48485c4107843d042611a04841c0360502c00303030019141038012050070010550410072101201c41c1381e41c0b08605661424a000d010060354800503100e507103c4607004070305182c25040da82110b0131703942541461420041d5911005240900075034001d032050b03003101c1c0f030008a009003891145000030f0441e0304e400d10322040c0c01c03c92940440c0c001091500785043d00005602800601140e400c0c9600003d40910200070420039501c020313100c0c030140340c07410503091003e40b9113042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 625432212 1250 625430962 625431011
    0x190e01060e24042102100302030c0c0a0b0129030a020901030608012412051f140f070906090524090a08010203012c0a0e030d1d010e01 59
    0x800e44001e03030003180402c1101e90310084030416203561000840d6030018200103041500c110740d0102c1c4084d00d1549840c0244001c1010213035102860102c503004040c030a03001154414500c240c01d038106407d954080d0710b040c1070040d048540b414481e005104000c005240a41e00010b903400c0c41c0e9145000080e000e10a00c009801100702c2c940002e400718032a4041c0e00104000e111040003006003c141031a40c82c00c4000822920b0340d410700071400000c3c2c1c0f120381d0030720a10858222000e01f5601107502403010f14200310315400710f12161140105102c450700140c049108290103510113509103068800200069484d40041003403089911b420b11082d140c5190441a04000c01c002e408541c500b0940744480d80641410301e0740c0104018004101040c064010314104e83d40240104058000c816940140302d183d500511070b804000720014074100c0d02900540f203031403072210940c0d02d006010342d0380c40300b680c0c0303800801c01000300e0b5031070044201d08091150111a01c07810000b08a940b803a62500c0d2a0380000700c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 625433462 1250 625432212 625432217
    0x103080306011e0309030f0e06090405060a0b04080f06070c0308040201050c0c1309050c030601140918030a0806010806030706360305071a0f0403060504081605010506190e0106 77
    0x70348942d001e100001c05400d10110800103e9544180040c0905550101103000529491700218103d024000031030301c7c5c0704d0080001e410203030240180700046c5001403030780b03034850900200041d4485d40e00005101800c0307481e010346082414034200310b1502901400e41380030094454550004690301144041e046a424602181d42d42c074001c1001e0300e00ba03011036185a0114001c030052140500507480a47c80911a4060381d4418402204058440c1401d101d40d40c0440300b0039284030200d00d40410758541c421503151020903021166030400b843e5400000865020580003424801c0a60700601e05d46c1d4840411401413500a0031f00324024a8814001c1e0301800325210036840e204212091445080d6441c0f01c1d14558041607034a00340666110200d201300125040b0180f441c0340350801c108111183c84030100141e034902850f6517102c900400000b00141d45410f81400380c14450304444140d80d030300600680c0040b4090514200308600d07d2500322940d042c2100c6483c04101d41071200c400241155181d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 625434712 1250 625433462 625433467
    0x1b080c0405130501060b13080f1e10051e0f040f120c0b13110102060c070312060905040f0c0902070b010905040f0b0c041a040e1306020f18040f14010308 67
    0x6401010010304100c4000c3c419400c0100118002809002034401250403c1241420300e58400502e9180d1000ca0714185d4150064071007003080d18813400074030856030421001c07203060400344148901200c5060300c202044441240d1502c01c1100068849034018286152100726401c040c0c1d076544802d0301c55500100104210000e4030101400743d42c440030310035003290ba40030700c9160454040d10584440902298500a40704901d18294070005a441c8624120f40f0654a418040d4034181d41d495010300f000e0540c2c9894110100300b51034903004440c0124803c2e003c02400c03548628001c0c079040c3c1250802401c044c4144101c40c0400c031480c946e18112600c4110028043e00d4506241402862861015041c40184014481070121030305c010320441d5001c0404084440007803444d0304282c0f0030751142050812502000c1550900c0082a07000941e00c940b00041c41c04206840503101d541000f01c1c880418003a06501a109041c640100b036251401c4130800c0003411181c2214914100046c08040d00d1424007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 625435962 1250 625434712 625434721
    0xc0d030504080f070b0405010e0a0b1b040b040303021b0118050603150414040b06010509090c0c0a140f150606030c0d150e2205060c13090e0a1b080c0405 67
    0x8190840d0907030100f1410507642d886035401e004e1005501904c0456003903107052401c1103240b401140150083d0740c8141405056211010000f41300801f030100e80f420b1648c1004005402d0320048000c000652080c3c01a184140200c0c503a045841c01c0c1109031814031460102c2d104009a101030718109482003260b0305512501c600c040e0151103500155000e07001031904072110248001d00c6001841588288a01e410b07e039182001110079000358000d098120400001207804554071030080d02039610000201c512228444d15440044d10343c1c10121101e907002540c0c8a141d0060902c10110200e03211001c4503a076080200c0030031802d01c80141440104003002c10150301c6403150b5041210310000c10b6103401103007030316180004004a401c1c2c4407145880203103080e03070010003032050700c071407409400c02d010704001d40e911071000c40340d5403003030704151413911038010027083d489041d10803608103242d160000c1010300d00314940b0003118415020400d41c6031404140c100481c0c20000b074150704041040c0c80214198a070b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 625437212 1250 625435962 625435973
    0x11161206140906071b0b070c02130c0503040f0203160320010e13020c03121501030506030f0a03030507050708041e120c030f0212010f0b011202040609030f02010c0b09030309120c0d030504 82
    0x10f1700500141410b88000502c01503a40c0f100003820078a000321004071007480030040d4103084544915491010400900024022070301c4050000d203007500107000da8800750310a030080d840d20034294000315144000003115010003080d0207205a1104420b007001c10800131801c001030307034888142155500c42500001c100305c50705401c0c0b06a48402040b906404003d007003203402841c08074034182480b0700080c5003d00044051400081b207911604611011740761004298400b200940002080d040c1482000c010980025106e140100000c002007640c142c10704148200303084180c402d545c410241880c100342540041030310707240c401046a60004594054036141e201281c80765008a01e202481d52801d0807a410a44e215001607003007400998400380d101e4540c083d001c0c100e0149000303038400542c1100342880041c45000840c42054014104003800c0422136981c07a5154004032901045034001205120b0740c85d004010800d1400e800840003400d2140c1d032403400380c2e00d018814030321080540b210041001d025 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 625438462 1250 625437212 625437257
    0x4060c020c1e060d1b0e040b06040621020c0a030801050306010e06090c03060a05040e0312010e010b0702010e0d0203030a0c1208010e0a1515031e0203040803071116120614090607 78
    0x3440c82d10010300300e044105c001c0c281050380e8a904d40581d09045c1a01d095180c0001220700b40c40c860340340c5881d043c5814007202e80d060560f04010a10320b078200141020500c0c10051480103501c02c0d610718180798146024142007a80c1070f4000071680c04190103000c00c0381d0303d0440007544221405585512541e0f0a000200c2e1810241d01c07440d0854502240c40d903090002100030104e001940840f040c80342d99072215904201c00074810000490002c4c010340780190305c2100e1015007000c00810001d51201c49800113811a40b2850552001c119407000b140108408040300c402042818100814103602d8550000c9541c03100600840700c05a4582001714003510210501014000007501500721400302c150160041c010340f0100c0c0c24040410107800c1d441041c1d030086034442c030341c08000541181c56451081c0c562140817400d500c0395000d80000c801100e445030841400524100340300385240d101a04044007102c0413181c51400109003101040640e59000401c0bc1d040301451030400c5a100c81c0c1c0e40c4441046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 625439712 1250 625438462 625438481
    0x16020301150e060d031b06050906070e01210902041a0310140403030c1707020f0c030c1c17070503030a1b080408030601030207050f0c040e062206110304060c020c1e060d 74
    0x34031031008031010300c01f01d64051886100804110780d60758403503810686400100ba5000c60004004c04109102140049081b02c250404c40c2808207c003440b070f5001500b0344121548480f0810301058501445107001c10200d240d00c02d21400402540781982101d20704020300a101505250321500b004104500c662000b0a07000510310a05110741000ca800a490708480403111502c1d1084480b40e00701071034041441105603400034030050a00362840d001c00082c03202050192405110802d2480c03050307441300020007a091090010319940e16041c1d04a104030b4100b4103200680245000e00500070641128216410507040020603440e950740e000100c02030b10905034018004d000702210501140800540b40c0d8100c0c008640c140014200b0f02c4609607991001c45802c002121281410110364460480c050303446805038201003070a1404115030003040d8410340e01160301607a42c1d00e00d0040303a17605012145004030f0454004182c202c21509140a414400301018880c0b071000480501c402103aa0011015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 625440962 1250 625439712 625439747
    0x11b0f080d0c09030b0c161515060201051905040f020405061909060e010e0c0f0309011107080307110609100e0a051608160e070c0201090b16020301150e060d03 70
    0x10a60500e00080c0f00c0141032004031000460300d07000c104005000015900d03170840818041411000b40c1c2c48684c280c0d03401030341c01c403540c1d946c94031700c1940001400c00307400180c0344580021949040c03140c11104424075200903544100d207000d09010016490015040c2600d4045401040c19110031001a131a40e219800c0e185c290043c1c841c0c00076140d40c5c1c1c4c0d0080c5003143c5250a0f00c0103240c2c0d84115811807240d0844510585a0041185c04540c4809901954124184000000c2c403000303515000312243d4407034107054403c039001200300510198031a0007081ca5481d0600500641c0c2481190700c0d55400d02000081c11550301e480d86001c1068003001848280c64129044603a41c00c401c51181d8040341e010b0003086e400340a034a00500311952002221030488041c0e00c240c0003a5034500b50b0032070321000400b004904105018900199a10f1945c019107585038000000f07213040421f40c4101400c5907503020b4009100c43ca80c4c101009105400702a06030b00c40e2054504581c0c1c0004c078581103c00b00b000e81140001c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 625442212 1250 625440962 625440971
    0xd021504080d0e1903170408060703020408010b010903030504090c030b0934021f1e051017060105060f1308060a0b010309050a021003020912030d0b011b0f080d 70
    0x5040d240050346009407580b80d191600b4514802081c031400e080681c0016800d80d030500c0b0100b001688090a0101d65802101c001d1f062a4960780034504101c402c0c0c605900090300410f050060400a04c1420195202400c18910092540d90050001c0c000d41c4a00301070030f503982c4d50b14684030b802038001c900100300041003081c2c9450040e04164010b04505130101d042c038000c00300040b0b100003140c250601d28429030000c059281e1049050321182221025400782a900e58556002c521520390301491220141400400c0c0342c0340201c00084500c0460f48510450945010854140c48003c02e84a055034001e9416554418506410744a00c2c810041954803895010b0000100000c1c00b0440368001d880c0c9600034821100024011020369480340c1c4042c00075003003400e4440041c039255810f00d005400c3d50402509002c41d07170000488841e148513080302160000260001a0401c4e8481c02240d00000d00300294680c0c0344000311400d101311040002c0816901e05040018010403c0a0b81d000e5454143c0c1880b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 625443462 1250 625442212 625442219
    0x151a09180c0d240e01420e192106150e1b0f1c06120309030b0f0f0c0702010c06111201051e09180706050c06070305150d021504 56
    0x2410407806011140803c0c0105401080808010760081d040300c1c1c01c9455140301c4440034481449050020751020b11810b40340740008507505041c10456451a840d44602286032500824010728040e103410a00140003d80000d104440414048900d003101113522480508618a0080300500c800c501c031041001d0309980005580d00b01d00503043c42100c59005e5500c40c0c1103503c4003288940074170801000c1d103110501a850a950040404642100b4080804152143d03a11140303810131440050980c00152044401d10901a6059200b504000300d00085000362411165a87c01894054040a0748d01c00004228095a116404c802d1a494001408205d0b1070294091410f0b10352100c0282d814201680000280e1483c0900380c6c1d04187d1641c6031200c100e4201c080420001c0d55000f050302c900c407401c95000308620a410001c0c540a80805c0c0c440d03a56a0380e81d402050724051340203000c0420103040c8410031103d281c6c0e003150203201c280305507182e8580c440c852000866110340c1d500c841050900215001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 625444712 1250 625443462 625443491
    0x702030a20010504150c030c060c110105060603060d12110303070c03120b03060106050c0109050a0614010e061008091c0e0f03060112020d030210151a09180c0d 70
    0x452400c0d49039900d00071000442401510240541d2246280e00e13007142c00d0b44404c3c070740940401d01d4001d00ca8581011164007603540d803401c49601d1860b01000512070300000b032405409100d1242c0005040700c915003075152200004a1011600c140105090030752002620510300504403080701d10961300680b900c0f4500440c005240010010090300041c054481c14500c000e654460485102c1d0f0203001f81c0a2a803c1c9801504e0560041050844542d6900700da10007055003403150a8501d4070540000ca1080700f0743c8514000c10300181c0142217001c0d015814085184d03544413110307021340712a0400050b9541e61a40050030004250340ca0243c5844944c0350700c0c1c1c001c0e4400d200d44c23076102c0115489080002c5a00034180d940500340200009040000728280240c58035060603a251442481100d48100f000a103e0090f07070114100c4420042e144901031141c043c0d14a843e8403680480e5503224200207008001a2104100c02900c400b903400c10790211742400d5010049850714203010805002c1c08180300d021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 625445962 1250 625444712 625444733
    0x7050f010b01080a0504030f0e01180306050a060e0f06090c0c1605030f01110d090501090215030103020418022d0604080307060c111e0106030b0a0203101703041403030702030a 77
    0x1d80e0b00095204002451410041c81402e0295070945c0d1034090700102e5546c00d45200c541c4c00e002e00e0501c014800039101c500b034861452405544980350100f541d0070003800c0e800a81e80700750050301c0c0c111040c40410640c07103c0c00d031209a03c884c040316110001d440316042e00b1114490010940743c20700660f502c0c1e41002582400c003804561056044640d00100e1100e2682241c05060300c00381050001c118020003112a44c22803000503001764000228242954001143d000180c5580e046500c2c000c80100103514041c0320b01c001c2003040e000d01f041800c4841e4000340c00c400301d07451500203503501071800d40c200110105540c02d0101d4090546640c0d9500c1b480315a60704d0304000000c8076410300b040e072140351252107552204041c0d00924000e05240300d02802d40420b0600c170100c42025596591710000110b013801c1c0d040d60007581e422100695074140b900d04002410910b802c0160601c1d88601921600c61000080350215051481d05440003808100003904600c10040c000e903042c450300001800740000030782c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 625447212 1250 625445962 625445981
    0xa050a060b1804110111060601270b04080607140f03130c030210020312160f080a02090a090b042d020a0302160605070f080106050307110313082103010e130807050f01 73
    0xc1d00c50003a501e0b50313103050780d41000308d810f2400200b0101020a02e4803088400007180c9240b22001841241c40c2d107200041600940d1000c0038950000050001190b003000504d42d680c1c88000d400c51411500c0107100742a0711010b07011000ea1082038030540c040c45541072050000e550b008020440c01c1a81000096583d0070402e0030a00c1c040c021008078402d170910740611642c040c0f0300d454008030707030611420941d195200181a0b00d01c850702004915140d6403420b05900181600c4a00000d9006d103440501003100c00182030340700b102c501901e0b035499600010b121501c10703801c90341d40580c3c0e43d150f4076000c9020340104040408185d1580d06084104081c41e00894801d060660321007449001022040b244480c081c40381e0000324008001044c201032080004895005d015012a4503051000101820595203a440003c1681114800250100030900500582440071120900f594100b1a0034034020384040c0403c2e82d03481c1507042402c01c1010304415181015000001d40c2d1071941201303052406451541c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 625448462 1250 625447212 625447217
    0x90c06030f1d061302011b120f031802040c0e0904060608010510060507080307140c061603020a0e190302060712020712030e0d030905041104170a050a060b18041101 72
    0xb00040d0845070000311008420b90040c01040580c82e004450228450b80d0581070b41001001240080800b80d00c0135100c502500c28104115200d008603801083c002c400407107102018140b4020f0590b4a2140c0b04c1800d159804031400116040400420307500740c400a00e655401c407000004000a0020560006085829200080c45150360744085090320724070034014400882c90078407240d80450343d81006140d2080c5142089120007041c0d150b8440560400175122a80e580501c1c104104400c80d03034004800016103050039410145008806421445110349441c0100302c003046191521020483e40e10003143c010b081300e9a40c00c801e09200703182c0030f072210420f80503200d4500005000504000800400ca805a03502c01a190100c0100f0400b61840d500950820205000c0131407580d50b940b2491a42d2407001ca00103584914100c400800c03003500925101440e0044403900380800d0f4040b41c2c3c005c0740780c5e12210008203440400002811691a8070b01c00b02d181740e200302000200b0420000402d00d000c4241c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 625449712 1250 625448462 625448471
    0x10060816050603060a06110703230706080c09062d07030e150f07020a0b0f0d150605030f09120a050408100603150209031219080c040308030c0706090c06030f 69
    0x54060019503c0203540164102082000c200881c2e0f11172000d081400750310340140e6800d140d0740d48821106044c03940200441d6800e10301c03d040c2180341000000001c2c40c1754100b5807818a40703201d00d00d40d03602520b9021801036a0000302c00340c1c40050f0b900380341d1481014044a00c2006c0c075910b0301c010a900320620440104d10340d40080c000e2442c001c0c0030400b9030300c001d0f21018500801c80d401400d050300600c408a82149510101140c07070802c0102500c6000f25185000381c6480c42d00e56140e040d0390030380d20301c3c41c1c0240603880c0501c80f80f03910508036644103540e4121003c594903141142303490048420010380400101080c40030f601d9a02c40002d1040340c00310b1048030310440d00c112a000456205c0d110007820540d81088000c1c1500e0550054030300400010161026204000c6a0030141c0c0d2015000400703800082c0d42c030b940d1540c1c200b000d1940240741501201d05080c00c42d940e030740d40d610000c1c0030301d101e0560100f018810411182c002000c001d0f800743c290128150342c1c85016024184c907042c2c011169081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 625450962 1250 625449712 625449719
    0x9061905210f01030618120509031506060a05071416060e04021c0c090509010e061804030c110d02060d0c020705010f051213081303020316141210060816 67
    0x31100280a501d4001c0c410030641d185984072401020031b0081902d40c198551030b103a02086420081034002040798a540341d80b004401304060601c0c1d241449100e0314061103003401240c2c1c072848107403070903e030b610f003000703a9030300f90b00e082040c944825040480941c1c4030750000c01143e001300712018400c840c030356180c4020440d240030402040c1e0203501c1910f807a1401c0601040920021034105022421550518942d115125008104402c070240c002d21000c590820030b010103410601c082e0300f4940d00401c0211001d05266130001c2c20320382201400f41000480c0441991103986d0f035152001d0349a4010178440c1e80c3d02d40300b511280500800c07030300c940150081c102c0c005841c0d401031214280383c41c00b40e0b07280c40c0340040424911800340d00c00b0381440d401005080800000403a440d004108200f0502c04501c5500d15500c1010702c0c18051300300c2d0902030f00e40300f0810005a600280c0d40844803904688901e03200811340f2800e85403644000c480207219060410000d410100030030b0001c0c0c81110380352940c201d1904e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 625452212 1250 625450962 625451017
    0x61220041e0b0109091803031d1212010f050105070b060a0e070e030d020309031f0906020406120b04140106121b090303090b07050303011215090803150307080c0609061905 75
    0x7022100b50560b032504441d0f030f4001a20903409004407620149c1d01d000014009940c3c6803412960901050b0030000c0019801d44035071003620414018080300c041d0031001e60420000030140d001304080145000b0490f40494140d99441c001503025101c03403160740313801f4903080700c0c0100503942c1c1018590003800340380c1002443d0b030b10200c12188801d038060010504039240c4030790340c2c0001441c0d456200403030b550303880402d000a2141c0000c00c014800790b40c80c807081810ba410702d003003200c5201112a00c07a502c1c110201c9030990182c1d00141c1114403508060511106282d03c0ca4041c10100c3c0c881e420281d02400744001490700000c900c001d4a009a4440c06050b848105d51010703403190000140c0107600074401081000640101e41c421540f04402841c0c43e541c41000d5503066410340002255148000310420101c40100c9881016801c0124000c01840345040543c54441500340b440c80e009860000304000f1b80d0312501d04450a90304803200b865071840c1d86800041c00c80d0060905010350703003403800c101c1c41e1002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 625453462 1250 625452212 625452221
    0x512281a060f060d06030b0f101512090614010f08010f0932030c280c0b0307030204080a0b01060e010804030e0616081606061220041e0b010909 63
    0x42c0521103a00584070403c039980c0c00007092188003a0b1190408000a881032101c180a56420b01c1030702e0385410540814031960b40d4a41103103180d8060f04c0001400c03e58032401c0120340d40c0904100065a00740c0f4201a03020700911405000400e1015000058600c1c48043d40e1086a040000030002d90b103a1000840544214010180188100d0304c080301070804503141d40c900c021100d100841501c501d2400c03c6045410814100202d07400040004107a50000401805902d401e0f070b540700c00305020b80d031365000c1d5a8854096040000e01c0400080e940750300036030440d405440801c040307031620701451030700181c4008240100030010f0b502d00c1c0e241242e5402481780c039005503030641b0342081c403100c0170091100700c0d0030016111502c5110a5030b41c1c40400d5030800100503a2483d4a01a41744004074109041541d480343d000303014880780403001001086000f40c1c02d513800d000c030082c0304580030076030000075000d080c118504250240c40d01e0100c402c919459407001402c032100b85c13070f00d828296403030070b0300710894 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 625454712 1250 625453462 625453471
    0xc0f13080706140409020307090e04050f010b0f031e1612020f150a0807050d0c020606010e0108070215130c0f17070f061b17070c140a0512281a 63
    0x4005000034400707045c8540195a0160b000d00e441c80d0740c0c1f59941c00980509000b56006d1b0b0b000c0c2c100700030302d036003400d0b083c0602d00041e4000d40c0d01968140100012a81e241c1d07820390101046400a922208548814000140740d50340d10300015007016114443d1207100c80844034120310130840c001c1c4444003414590315440082c01d80030501414440d00e44000e948040700200b10340100141080000114003c0d0712480f4401602c980c000e03c654645840003620540d003100b00d4905000301a41040fa40943c0000c6241d06554a0000740d4a2a202c0c01008000300d94106001464a42404400319030108401c041d00e003141c5210012008007a035400507551500d01c28052030020040015051042c1405400d11551a00c00b40e400c0041804c501d44851411000d0900c03c05c0c0082d400051050501070f0741c2d5080006031000c8440441a0101100005c04107000791040601509101020610450050012111030005000e498600c40c038000c0711820b45000d840ac0448880c807841d01c1c1c030a45103036440d1205124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 625455962 1250 625454712 625454747
    0x13050406050f010c0516030b0402040b030604050c19090e15070e09270a060204180608060106180e09010b1512070e03010e0715030e0d170c0f13080706 66
    0x640748042d004682d840c080c00800e4405210741180d401d050950a510000114000c6452640743c0c18144104001d0700ca48101352480b0345d10860a000105101044d01c1c0b1750114101c84494200d60b000c240380c00c0d0700c0001d40c03000ca4410314180da03295020030b000c180110846045950003856540e00c0c0b00540d068103141807440d41102940b400504101030030209058040318079850307030101850040700c0d285003a2591008403a4543c011904000c581510701c455828451803403c00c0c00000d00301010b0715a14401440352408020f90710410808507100d0070302d01c001074030400105e007010f03240201040d0301820165500302d010b482998a91114102c2417025200c1e1001e174100010007175110030300c0031201c100456000035459580c030009812004020000c0000400c14440e4041d1500b80322b90000e82101d0f8041a0005c0d640c0020f843c14400075407000d81c1690120708480cac005c1081d00c5542c0c4107102e0b03000d40c2440c10b241180000b5014100084c0f00d038203d003110f81c003034204d40005c0e803034650481d80b00560351000c101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 625457212 1250 625455962 625455979
    0x507110616090b13080706090b070209250309020f0108010b1c06080a03031d0f15040c0314030c0f030a020709020f0706090305031b0a0e01030e01110c031305040605 72
    0x301108030705100c221401034501003041c1601d440a1150643c4558801d03004020102020000134200b40080e000804c0d45d4184000c2540c600300780310541e403184503c001d224400540000342035402da14544516000000b1181d00102200725000d4000c2280c400c059204441e24440d040c5258883c0300c40343d05a0303042e100d40c18113001d5440c0380b5031030349000003400c8408035444e514041f503d1030701085104440c074025500424151041444a4841000341c0c9030031000b50407191110f1030b40340000804400401c50b0b00707904100ea030b0341d50410700390040365a08000c0c0b05041c5a864120030000c00805400e040d180081992480011020302e26580d2107688604009600401010403160b5040e48c041d005402910b25274520f45106680c40c50101c40e0303601d00880200324081305000303801100f9024865080b0500003401e1810040f04000303441c1e0100b1900d200d040584801d4815040042074029002c072030304900c1101d0702d948004516503142d400c421030003005e440c101840050b00d807401e40901c4040702c001800614 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 625458462 1250 625457212 625457221
    0x1060201110a200c04050703021314010f14120f090d020a26121008070e04020604050d05100603050309040c08011404022104030c0b070216091802120105010905071106 73
    0x5142d03040c2601d03e02e4a0003004d10740d0f08280c03900c0c0160361103581d081c0e40041e40c0b5443c1c0c1c01098a1141e00f60010205124144c60344492a40c02c0201069410ba40303050a01d40340071340f8400800240b00b0b01d1410380c0309940710420301c1b003298401542140580301d44010307030790703983e41448040307990b8920070001900c010400f03510814003249080e100c1c8014284c1d06e80306031811409409203c100601034600004ac090380003420002080140900c0c00501204100401c41d810b050700050a00e0140f8042c0c03c0c072a124402c0e001040100c1044202e00c80380c1c0d44501401402d40e01e003003c0c6c0d10b80c5c02c410291801141492404000c1c41d00c04c881e03990580d091030b0084803145d1629818880290040307402c07a00c10006400c0154100d0f000d2210b40da210b18407036030b10303a060102c00e8a815180c03404054801c1c000d5500c0449040c8003151814024400c3c0d90103400001080b00e0585c11101d09181d206101940040c01030240b02005141900040d041e158051070500c45c030b232200442152420301424486009410810208 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 625459712 1250 625458462 625458497
    0x21b040b03060a0225120f0503160e0409150b0411070b01120201050417030a1404050d02040c0e0409060203040b010501020a02030607030b0406150519020304080a0f0c1d01060201110a 80
    0x31701c26280e1400d04002c01c180c000c04103c80b4a95509401da9038549405400c00c00b241d07008840f02c200c4001072400505504200040860788440c00f688a01031006881c002040c68803542d21900180e074000040701001d0950f20301190040040c002c40700e00550a18100b007610020040460380c02d01e40c02115082c450786000d40080c9207904208040307041140030440060050511910010403001c2030003e9a602c140c90381003d00401c22003051f0002c581c0d024001000240d41e0130007208146034040d1000315030030308000782c225042540c01740c4040d8400e141c2a16041032007079590255101e00d104a032101c0c3c469807142d006a96070384010314000e506900c104002201c807071007504010b0741c01c10b000d0008240c0707a449500340c034404150800000c0004401090003040464180e0005800b0045400510f152a0910783c03c0750700c4100c1030304080d0820401d000040c0401c420303150107000510012070081c40e071000408a030515001d00b807060200540c2081e5042f541c880e41c0c1400c41d412031046448003141b0042d0345d12403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 625460962 1250 625459712 625459717
    0xc030304231512180a0309031203110a110f012c01060f030b0a0b0910050402070503091908070e060604051309020904120f1103040902032203021b040b03060a02 70
    0x10640000010b440c00c580901c0050160640710b0700200e0419291a00e0300d410b05004030340400e2200c142c1e001011240200c3d07000040c40c0203494110a5a21607007070900d0003540507140d0700081030001600095543d0015501100c44401c4440040c01eaa82640306230075841d00781c1c1c50110740000c000e02040f0800d000b103400c5000910015038000c0000c00c0060342e0f00000a1700003500c0d4030070f5a1245842c0c08010069940348100a1540c030704495000c03842c02e240382c03101900c0b442030150602030b590020b903000511808005403210b00030300410204c0c0c10320b02c6000303007500082c6510a086040c1314010000c02c40341d600154162080402501c01410949402c080045490300446202d0003a681c401c01040541c03180c88407244694040c1d01c80e82942050a20004e003608401002e040400c248041c10170f15070b0300040100d4003161201e040240e1640c442c42515004c0202030710380074458642c460f0380801015000b00c0d0320b1440e240ba200c06424540300e81000d0100303503042c0540403689a0030400014020030603aa02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 625462212 1250 625460962 625461029
    0x70507080a0506100b0a08010303050c03131205120301150e060904050f0f06180610140301090e1603150e010b04020c011401080d20101109030c030304 66
    0x48801150351461218240119044280e689801c65420019240c0c00050010020402410303801e1508246001c01880c840040c0401410440c00181c010b2440c07000700280c425815154008061007030340d6030b419a131020100081100c450158186641401c401101501e04030742881140c0c2c02d03400b0340813000b01c802c0305030900115408003003400785504039180d07841450320800700300c104c0320ba46d0b007800100c0b20942f230002413400740314034019598170304000c08081016030414403d480241c50302806c1a8180c82e4803040040810f04211b01000001d0205002e4000301c03c43c10000c0144c0307284d406502c242c81d031008420701001d010009504c1005035a0190380d070010400304c0383c1e640006142016480081d050740d00011148800e40e45030102c0204c880c46041070f01d80140144070041030103400500703018083c09114005034003032504554141d41c0030341082c8004010400410400c00200003640c180240300c0e001003103c0c0307009100d14642295103003000012102502c000a00000390194114074690003c4061038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 625463462 1250 625462212 625462223
    0x9030809012f070e0106090b070f1a07030b0306130f11041e0e010b0d02060a0c12050408251806170303010302011b020901060305061f1e03050c0f07 65
    0x10881d803601d064002003001078000b951800010210346040d0391a0500075003010a400f0344610040140e10380299900088800d65500d1644036102420101060004220003414001c03501340342040f0f01440b40f01851080e41980c44c20490300c0991001d255a034001154070140a00c032518036000841c42004510740c040b0b01c22841c0c40d81c410304100105090b16100015220364001c910450082c0800d980914410800550020003400b08040d0005401e9582024082d004420024541c02c81c0c0344582d14005030250040b1010803d01da0543c001031039607000d4807c0c01c0141c002c04181a1299138000c0c60100f044506a02c10698030f82032408110301c0c0180200542e0045580380d20001c2c030284800c005c207036044032040155403258034600024010380e04039018203128504030342032900103968510303c4078107441e102e140c001000c2e665000482c0b0780002c110301c421403600843d01487e546039441090f03152103e20041c0d0321680d81c124407030300341c0a884c016118541004d4050066140708182c0c000075020440c002c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 625464712 1250 625463462 625463477
    0x20a0b0a200c0301061502100b06041205030d050709030b0702031c02030603070f030503040609080f030a2a05100b0f0102061816060908061302010c1b0b0c0105061203030105010903080901 82
    0x30b000090860f122648041e40c0b110b16102803007102601484021070704240b060041c06026003140001c3d400e03100758001c218000b00c03200011402d01104009545103414100002c10003810241c0e80504071101c030740300403184081c0200005550078804001d54000054154000c07158150180303541d030181d04018403690f00352040500001f412003c11042d24011400780001d103075220f00384400180b082074580c0100740d5507845001d40c0304400070000308071020500d9504e400450112600310002131180344000035481c48040206030410301c40085020440c05940b202c1c2049002c40040900c007454514103c59805604a00b0004502082240c2100d500901c0d800a5458240301c0c52440800011070750010300005d15046400d0000410070080307550070022202c2c4000710325032030707a000030400c02c140d14000380f800401a81341203040d08698508406001e44041e6a619034111540303283c028503085817030794880c15661203008a060004000c590507504107035518007000307065454040e0710f9070040d50070b00d0411038130 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 625465962 1250 625464712 625464733
    0x3030a1d0307030303020d1401050a18021c0b01080609151309240507050313110102010e030a0f0206060d020d0b070e13091110051e091c020a0b0a20 65
    0x40c80b004024612a0701c5c0107071070f0440c046003081101c02d84101801c80582d07002c014030266440304c001d1130844500c80c4110080301c0000c2c4c0302c80f0280c00b858400500c90345054a81c031503680c82d542c02031400b541c0b081ea90340c06030395a00303010881044003d03140d042d18076144150041060400449210501c00c0280e07001c140010f2941e101c2240c080e0810402d0010400b0300780e45000000c0e075000d0036030082d01c1450210b045003071040ca0140c890103180c4000b400c40d00e1746034103411b660b4000c1d005000709400f0380b029a9140c14140a000d0040410b20080380010700070000000c0d101d141c080c14055031150003400301c2ca2510b0555803407580d06840a02000f042c060114840b007519564030540c191070014540b07010a0500c400d1901d815401c0301d000f0b150b13104443c03510104900d1503021041d40d0751500300c0c5040200723401c0b40d035500c914030340f080c21500e507005045042c251412a0140c508850541d200340c866420b550307641c07030340c2807460701803d100300c3c000840002c0340c034600103040e41091460010000540703031030000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 625467212 1250 625465962 625465969
    0x1e070c14150414010e10090326070314091c12050103050d1103090904030e0f06040902031b1c0c030e010f0507030b04090309150309051b0a060e03030a1d 67
    0x4109110707003000450104100422142c0010440b100d60268024083c1c2070710b40360001d8590681c80311440805a40b05100001c0c18401e1800412403003850000342034105107454510603820007100c000700882e003480000700e40c81034802e80c1d00d44102281c1c0080d010018030220b10010248262005108105144000048a0f0303042c0c420b1030300a501c00ca000f017034188a45c44028046542c03181440c00305410a001e600d0f10b50701c45c1c442c6140d0081d410728040001103903500025100e415821003072032b0000004540884d40c4c0c089a0b0085028080156048629901c0d00415a031240f0401d045017000003810f0701011071520f0103402c032019840355402c0c04a0f182c85020701d52401c541e4041c0360410102c0c0c07179400b4400c085030148034459005101340c4003031210300c660fa280900842c04900c60481e030038400d00320031952070b07100b43d10030013006500ca0107a40344500c4012040b00404000380101d4072a07000081c00040c014041d045240900402401035420075519000aa500401e028000c0d0b0300804401c2d4004141d03078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 625468462 1250 625467212 625467223
    0x2a23030d0f0b01090b030a0e0304150305060f0f06040311030a12020d08070306140108060d12020a0c2c0a0e01060603270218070306030c0314061e070c14 67
    0x580d0800144214000341d042040d2508008014184040408244840142c50b0b081b290700241240000c07440d02c4440713000500c9c0d446141e001d0244082c824000f00461070349508882d008820071a850b903007510100c0200110020000d0f01d10750711540411081000910401810b060100010261401c500c4240c9450b01c822680c60000001600110b01c100d4078107800c01c120541001492500b040f1031030400b40f0740900341120018036414405441c0000c2c8840ea1010050505654400091902075203031081c041d40e114441002111206000b40000c1172480b030303c1030580801201824250b080c0c3c0816564155440c0014258100103512080500800b0009000303160042c98a554006207031042154402c00d40c7c04003454040610300c04240300070140c0d481e14100c190302081003050203815110500290f00520582c0c0c0700410340000c1000010901075503040d0340c3c1405500b42f0941d20560396440d50000d481c0c1804c00d04240c4030703400034045044540300302d0348144c11911600080c2d00c2c800034078901c40d02c0c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 625469712 1250 625468462 625468477
    0x10f030915021b07051003150f0306060e0c030906040b0c0c06090c03010b03010e060610050d050703020406080901051b03061908070f050a06090b0f070605070e012a2303 74
    0x740d400284075800d1040c6060706511407150800601080303820000003030540f019004605042545614500e5214885070195800a00461015104442d0703286800d81c040c01091140c2e16050392544c00181e05660080c1c02c07071348120000005441c2547c0c17242e82d1429070100c043c041d062543c10500800c2450384003002200d010742500001448a14a490708150a4500d100700148c0240d051911035030280f0300c0000c00542000c000c1711140403628100324101c0746402841407071215203041030305214600717405500030415102d0b5599405c6199035042181c500341c48003900c07100c11031918206a1a032801080004d150401c07001000c281d14007030b5109040100108a0b0070000407608003000421080e21858681801000103440d0b503080d6902e000c0003c1c0241000307104902d2803040c00507204c2c042c51441000c0782c41565001c0c90401003030620103030050014400c18440350103c2d1142d0725109a105801da07841c10364080b03407174039604000c90741e0790f07142a4884a500072698078000d4201e41c0f09040824805003504 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 625470962 1250 625469712 625469753
    0x11a0a05090402070c0e090a02150a0315060503100905092e06030b090c0a1a220b0a0921060b04020d0e03071203020f0d020705121b0708010e0a02010f0309 68
    0x221760621030030011030480a4000c9581d903009007540d80040e02e0307000303a42d4010686182d03082d0300c50404ca081640a4240c500034124a00c504000101c2c02d150404081c40c010003940c0c80851440e074940310380c04111781c800e6603141420f41c005002e044500c03402c2c02c807d102208000c4a010080314070151040184c6101d038004950004900c402c001d442c527000c10248400e4401150700e038502c10314102c904c07241101151009541440005508164800c00c04021407140081389118082d42c0e940b41441581030700201041d1001500507107001442d101001c080314204001100036441502241d80d600d002400c0c01c4110365045034003480301120b1500c0610809004035031510203195101d109190500303d006144513207a050620600606083c86103260546000442050006039946044c0c100f2a10307000a04141c550030744030018400b0883c2c02c0e588c3d009142a00d000c0100c404a6072a402c04038203a4034043c61105c280c1c0d1103000004055840303299581900304482c03e000602e0189501c50480c0c00b50043c042000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 625472212 1250 625470962 625470983
    0x30a11030c0405040e0c090117070503030d06090c0c1205070309030b0c030601080a0522080d1a0f01090806060910030804031b05010f020709020f0906070501140c03011a0a0509040207 80
    0xf080c1400d0060f5025051100c2c040c215200d00c0000045001b9418002d1101c8190281020f0414110400507200601801011070351141c01c1c4501c80e070b02614090142d407101a092901c00180140503900c4d1440080c0d105009044840c0c400404131059084003a0541c100446458000007140b0b442014600503012001810354903d811070001d4003400c0c028112132081c0c0d161008000d89820103c11849035100950b805640d507076641d0400c00c09901508401c0e2409916041d144d103480f03045103400da80110025603441640031505001034a00c0c2c07065205000858100307200064903032500040c02c551003103000500c1c190360394480d21162002d40003604126410245441d04000600b13030300c02100000c00d4240381510710090021002510342d80288110242c8680114441404440501c00c0e1008488050800c544405d890b042681c060030340c2c00f00700f204151401002c12000c5081c4c038112410780300031100030b49041c0660302d124266640000307815803c201d024003800041d03950318002440024001c80c2205c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 625473462 1250 625472212 625472219
    0x2301060501050f040302100e04050a060e09370803040f1703130f020109080a050c09070305101a070c0e04060b04061a070606080d0503160c0314030a11030c04 69
    0x142116469040141448400c1c018440d9030441074007194140c036410713141c6408004405005961100781030440075809402c10003000071900041e8044404c6420321079911206450b0801e10f0307502c0e0424020b02060070545040202d1401c01c001c4840740408015031014900707080036880320015a001030350111000e030395107403541d03003805840700c10100c4134022034180c1e80c070314103100b10401d444001d860780c010000d4403500c9442e000c0d60f0151065000420000341501e088544a19025448640d11b0314010f1150022002046160740b00b03128092040340030b500c208401d2810401051030034107403c2341c01404103d00f0400040090074805620340148800c0d9403075901d50425141c0030041d1842c04488902891400f2410491151740c405402c000841103042d85540b106503051480291119030803198040c841c01c14540c004942c80401103101d52180c06c420b02090505ea81c3c21150361280e448040c00041d0714294040130b03a1000c40007582c11071800f03007001590b900000032440c210f40040b2401c890507040402c0c2003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 625474712 1250 625473462 625473533
    0x6070b100b090603040b040609020a1409090a0302060f04150c0509100e0618060415020a020a0e0103020108010b03220804140411070b071403130204060501020604020a06030e030403 79
    0x100161540090442c2400107880c040b0711039000041000d48050002d0020500740b0000350b021840c0d07542c0142c00c032400643c6804207001e07031030b4091401c2e602822030040050440300e008518114181c0d4150301825898841c0322120301d0024001c1d000340c4039400642211254404907100d40104e038146900e40e25110101c0d00d0411601c810ba8501c003d0a1000320608851195600c1c4215998280c0440d2251040d54481001c20a580142d4020300106d45076050320094261f00003d0002c0e4617403080300d00b41c0c181615150f000020070b40030300c00280413505030b4006200d100d4007100071356481214403200c01f031910140094a210286051010350340c140d0009403c1c0800010b50141c00b00c10601950103003d8004608114034807031080900c0641040c000301d0200704070510424810304c14000c45a10345440303051004600348600d210f140d04a00c20313031030494006525400460f54a1045070020980604686052815005170400c0341c0488258002080088001410b0062005800381544407070300301010004580e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 625475962 1250 625474712 625474741
    0x2003070309050a0527090f030f07141504020d0303180b1807080705042307090e07031e09050c1302040f36020d05090a0327030b1506070b 60
    0x2a406882544441c1940b102e51505c12001d400c000a003140703440e035030030040a050040f4503c540215004c0000c00f40c98002c91180608800c50240d003401080f0f4110020301075841d01c2010035500010740801c00140907140c80580020703032600906010580d0440300c0322102103e03030800c41c00c803605640d481c20711103d14104d0005011800c1b1820003024920304142600b980c0d400c0501c2614441c0d81c0b5200c02c00301800c031006040e00d0861070505030080d581400a00a40140194080c00500d035007400001103e0a20a00a5140c2c008103e800d002a505030382c0c8001c4041d242b5048140c4661050b060925031300e80b21a80d2680242c1c2d07004000603200d0303040141003070001c0c4156000b442110750310001c03c3c501007010b44c20740030f034510a8500c001282000d130601c01d0203809261a10504245003a040002c100400b185180031144280e0700c4031000400550321011010601503242e2240810b0712007400002c1d10510501c1c0c2200e020302c00940340d040c0303460000751107a0020900b25594010ac0f028806400a103046 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 625477212 1250 625475962 625475969
    0x9030e0907140d110c060405010c02010207080a0806040b1302120901060b121f03031d0a0e13020609060c0a03020615031f0e07090e07061e2003070309050a 68
    0x16034110380e04110000410414529a03a150024000119100800b180f0750041900038110b08815460b02d21284845171105011142582c0c15400c1c1400210700038030600c02c403a180f80c0d2240989040040180c1c04444180c0c3c002c00498000b80c1c2c84811241039512050342103052800d050000d0303074403911003884454141c000f610201440e810b0603814130241c1c41c868150b610b055a461259901a550004071015101c4641d282020801c0310f03541c08820305501000948000000c800341c00000c000040c2880011215803040c5060b0240706c0010590308441003000040342d034000ac0c246800c0c600329200098055000e9080350000d03a1110044804064040c00020352140b841b440c4c0c0d81801c2e0b0300b00c01180d11903101450351482100040e02d86802208941d10400e040d030301000860314043c1d260340010740104002e400014191003200c3d40007c2623071003041008580c0841c1590b80b0b012041c800c400341e425542100c8500c044807a89441810380c240c08001800d0003500035540c0659051400c4144450b084c030341d81 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 625478462 1250 625477212 625477219
    0xd03020705072c0103050c0f120d18030c0b19080f150301020c060a05010e091b0d02040615030c1e021c360b091027170c060405030d0806010e040f09030e 67
    0x1848004a50001c51100f1407105c01c0c0c01c01202c94400403070380e03620940194100030404034100704007042e00c4e124800033f401700c0b651040300c01301c4403d0514010398441d80d0403541070b41254a0b0000262114108281c800b4480f503001e0000341c1001d420000a500340b031400c40b96460718680d504010000c00e1451100705030050400c1001d00fa9081d03422800b911103402005215000f4400700440c80c2c119104c80d03102e1402000a5121902d101c1000503004028000b00840140003d80c2c0320700300d001c1d0100c604004900c02503160020440b04c3c22000a05c80324901c0380c13240d001400b0001e40c0303c481c079510b4030354105030340b2100d10450682c011401c3c00e4013183d122550051040010103010068991b2554541203070b01c94200c1c20079907a416260f078500a2410702001081c0c00001403c080040c801c0c1c1038941140010748140156030f1480108014000c10740941d1040a40c15440407801d044d1031030190b10344981001040c906441c51144a0005c03500790758000c100e1201455591082406143c0e200c0c48007096400f085 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 625479712 1250 625478462 625478479
    0xf04061d100203040b0c19030f0f11100905030f0f04030c0905040309030b04141905012415110d0801140111030f090409060504060606020d03020705072c0103050c0f 72
    0x2207400030f580380207900850940c0350000802031100001000602130341c04083c5402e00c401c2c03c0d540b800810840c0c51903442c0c0049000f002c036008243e40940b5011404446400003481c05e0302ca00020100a00111170058404d40010040b072118183c030354009154100540001c0c50780c1d10310f50304d407040641c1c11a6100d002418074000038400040e910101d50001c894210f6200b1a5985440c1401403003d045600c0c0c45943e0710408940403241c2c01500c5c10001810701450080217030700c0481100424840062041b22003110710b0345028000089807040740d101400940c030f4190114071400058a1074944400305840209450703100410034171890240d480c85604081c03070b00140e010b44401151340c1c0d80c002d0100007103441d8008100a44245c560394040ca181c5074014030309119605141c01c00000400060055800600036060440b90050290007142c00b0075901000034818540381c8550f20081c2d1342c48000295540355098140380041c0342403410f0328080d5010342c001d4900d01c4115400c103c00e0001c011071103400340420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 625480962 1250 625479712 625479739
    0x312080c12061003020c06100f08011e180c06092d0603051e0a061406030906220b070f0e04230a0603080a020a0215070203210f04061d 59
    0x5021070560000c00550751803850301d26076681580680070f0700d041410144100300412402d602c1c1d1040e440122003401c103e010030349895400c0c02c5d09075110218100e14180103000c020007c10034039032001000d20208036444040c45402c1d88e50100f030305a01e600c21400100c4080080c030183c07000d4126145401c2078040c85c5a040802a0400c1290141c148070303003800c0c12768402c0050b11404110440a4406142d596044868a4188124001884030f07000c0c00c01013001c282c441e00100c0c1042005c690042900000a00d560399604400c070461102400e6001280c0580e0070a01c400280c030303102d90351b0041103d500c807540c220000c14001816075852004052080e400c10155943e41c20307000074481464074812044003125071b500c0c0c90700c802a02103544014452000000d410181940c08a9000980f920884002000c4b200b0090701d10f0150244281c060340c1500488044600b05818001040c002141545481d00303181c0070001a003100e40050b030200004c6402c00304006403080e43e510000012040842d0072002c1c1a0f06c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 625482212 1250 625480962 625480987
    0x919090e2b080703060f080a11041806020705070e040602070506060f060a031802121c0c0b010e04060e0303150a050303030103051207060906020f09010e040b0303030606220312080c 79
    0x30050041c0e0600000c0400302c3c40f01803090b00715102800c1c00d0074046950550b601130031030b44c480c2c1c41d0400340d035a450f220054500c2803500c0d01505070b0300210081c0984d90319840e52104402540036403400c89140c4248140005c403055040c0b10284280d00030040147ca13800300d4280ba83c18280b00800c124070540f0018640c1d111a5183c0040d0344030281d851030700244059903102511898010b0540c0a5841000f201e840c000c510f400088855031a1900580607040302c9410009071031807840e103c4000c005100075401880000c021044865025003d02408600607103100300040c2168001e68824004903030702000e00145080401825000348020303001140f856255444d40d0b82c4610003120211803250b400115034081c00140d4005143d0780d030308a076045680701c400c0c484c40685503001c0c80c1003a001c83c125141d0002d85203060f100d0fa801d603030000b42c0910300d581d03160820001e1a0f0700416003000e0b2200c1100ca0108601184100c00c00514800c0100c0c42000202e410040c080c4140104030080060040104135207608 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 625483462 1250 625482212 625482283
    0x7020d1103011812120e030d020703020d03020901020307030806011b060c0e1f0e1206090606011101091a070329011416110a031e02010f0201060b0405060919090e 71
    0x19014174003d00002c481e46124000f03401c1c0d0103980d6600d840089000f0000704807942c000d09095210f6000c940c0214040c0c0001d0307060b0300907100e5040c0560014403040000c1780c001c1600c150b001d0014540301c004113548900031034000700d038604140d41e0503584079120030b0095044000c018915404603034840c10f00c14052003d43d802c0e50446204d50400140640847c12030311003030282181c1d40d0a400c251001c0d4503104c808544e9460341180e803540082e41e801e0842825400610442e42000c2d0868030801010f1500f0404490300300340903200702d0400d992001c00c01030401c032060300b80008406565101c02c0c000c001b40b000424011014004050f045c10820011078580100c00c403c88102d60300000c40d2000108078000201d101b0003d50014001480007890400c5046420000d00300c964800d80b50b500c503264440030100c0c2282c2d0503010b0214002002c00c014046880c03cbc00103800741e10f000a040c3c0c04a0036981003400720400f402e80c05108299100e114203180300700700740200e403a42c04c0350301c0f12802d20511800301c80c01c00c2c0e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 625484712 1250 625483462 625483493
    0x3091e010915020a0302040b1204060510031a09071e03110105031909060b040e011d030c101505031903230405040f060f0b040503070e01050102120f07020d11030118 72
    0x2c0b0790010711000194005c0d01607400600c001c021154485088500361a1407040480742112054a8500019000355807000d44200b51303a0000740d2136a24902403d0b070182c049602400380d10b910301c2a4280040c0ac14400c0182545841421900d141541d00c0c515004c1070688e614111541400018403c0100080c1e10403040d008840c3c2158000c500c00360769003080c1c0001c0c409620034581050501c0d604422002d4150403907940181007880c1040d1402c0020860741c0c490183e0314900146401c20074811401050785d802001c00a000c90706100074503590303400064540301c043d2603240c140d00b22030040e15041c10b421480083d48141000740300041e950500c0020015840746014243c49036a0b503203910500107015500c904050401c001c904070302181c9801034414103402a2181a00c41d01c21f00c0404900c4040c2e51071101c0c120f910603002001b2549134015400515000701c01c0704420044188540d1780943c5d240700242c00020300481d41500f80407032090505094903580703001090704018030004400003660268140388503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 625485962 1250 625484712 625484753
    0x7031805091e0c180d0c03020406030614180c01270e0610020f060403051b0d3501060f020a0b010603020301050a090c171308030a14160504031205090603091e0109 71
    0x44091860001c6503100c0c6e9810103904903103040070100c02c10640790f0002107040c81c0c18076841da481d500c985881d56195900c100c54401a0841810130b0000e50068800e80481c0490a0b4555440305d041000c081405280ba13011040b0141641e050143e00c0c2807601c840409100c0c00d102400310042401d1a0a07a100f4014100070100180007651951101d1808010040705030340c038040c0d6800d0106000010700303017201503101c400900542140240040c40601e6111500043c89070601480e80c40c0c51000d884822084644034107600031000315600007086050064003a05954400503102c0d41440144404100c03940c10095140d0301d01000030440ea50400640350034034a400c1404040c5555100e1a0381003540141070040014102106020344280260420b07001c80842079000d101329503075a503110044600c4160b440001ca40104401e001190041415034200c81d03a03401c1c59442c00d5142030215145502c2200c44003000d40004844081900d0b0101d283d00b0f890242000074403503080107488802c0c40c0150105003012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 625487212 1250 625485962 625485979
    0xc050102061605030705160b0106030f0e0a0210210e070e040503120403030605041104091104050d110102031204050a020102100b01052a0a031701150507031805091e0c18 74
    0x381d172031040341154594002c51080c2d02c1603035003c0c504010b0b200700078002c0340003081c18800740c541c080300c440c4250518500100000d210001d406c2d020b101a5800081e01c0c00d04000d00d0813070741480122001c12181120b00b8a040c00030355100011482170405030180c00c40300ca0b0031160418400840c82c004140c407144c1700c50800d50034042d05c070b91030154014482c1d42d00480d0040e0408000380283d400d00c04c090421212241410b20544420b010b410405101d28011942c2c00100d214102000c12492030303403409046010b004491030441000d004155514044070119026405900c028086581c140131221031080e118005004807501040003824034080e03421204c8091000705404051620a0440016540c4500d030644800f0400e505000b840c5040d4a250f403000d1064403400000c00c52080c120310400000a6a555030421400d641c08032490a0603c060b0361040c290104040354035501e280d100d034003952412074824107000e0745401e58003000d030005100d41c0c2c4105042c882e0003154100c440951440503402c035038244 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 625488462 1250 625487212 625487221
    0x20a0c110f0406090c03060807060504060f0908121b061b0901021005090a03090e010f0b2a100f090c052101020c030405010305010522020c0a1e0c05010206160503 71
    0x2514201d407070030820340c4141401e10000341c40460358810868405036940c14800c244d02c41d61540e0340c6d00034901c643e00000e04200310070040107214100007039080a107031420b012403d40e40c2c010141b4005907280301440415000510401c00502c410400516007815000f41100307140000261203681030940c000000034400151440c000d0b0b1003440080021100000100a203040c45080d00390f48040c584400c034042100036202043d6004900030450480b02d000980715980c90420507580103e0304a541a24a0545040401d090040c000c610014100740307140024100071106040311819079141f02150301c9042d20b4001700c0008a40f5030106202591416180201d503019410888110309000b40180d20b001c0d44089410203012002000410440f00260f9041c4810798030780040014107031900010803400d5040c40001c880c581100c0c0c000d0244002c140055038141760382510b82ca03a41d02501c161a40076142080c80724001c00101d0301440000e000f003032004000c2490800c1b6110003c0b0450341000090040110014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 625489712 1250 625488462 625488469
    0x30e1006080c130e28051902010e0108010e0615070b040308041b05060f28020c031605091b090d11040f0e0a030e0a0f0602160b0f04050f03011107121101020a0c11 71
    0x145d4203030f0322404450036030403c010300c00000f40d01018100d000801a0305005279540c032035000f05040e1004208894483c2e01c494080000491441c85c10884040040c8440c1c1d000c41d81018080784114000c0d16100e0766881c003441c00b040e06201d003110a1200110446040c012a104d18042d5040000718200c0c996a03802c011b058440068621002d16540c10030031144904260790126000343c0c42c0000341c1c100c030b050345041e2100701c5044449005080d0846903c800103a9038100390041c0001e8070b42c0c0107502030b00d8810031102144100c414184d0980e04049801c01c8094103080074402d808a030250a4801c001140c0041e400340e8403880c091402604218960070050f0150346c400003c1001091170b1554010b041c0c2da00c0c1c00c00727900d60410703a100b6113042001c0b0070001500300c811011074120007843d4481501d00782c28082089411086003104039090340d41c48054018203c01e16008000040c041d820300303800242c2c224001840a66091030304d0300d03d640144131030001c140e000388031202495400481000c00c41c0415020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 625490962 1250 625489712 625489783
    0x1c0206090418080406030c030506100e0111030331050619060f09050403110a050d03230403170c070c050402031510030b0f0d02060406030e1006080c130e 67
    0x40b408003007a404410030429070001c0c4100e1311395480c1032100d1a51032030150701319017003184c0c030580001c03500c4844019240304500100e01705505051600d071000070518803600c1e581045401740d640900055a55143d000d201c1d4040030f1649000d215a0f0300c043d6280e684640b41c0002401c41d4a044403080604c03d007242c07030390700110f02404019003a503488598945800000c0c01094405070b011030318441000c0007091010560303041e038a40100c0180102c1030203442c1107004294018081d140c101400480c42400150020118091030195483d61652400500056403c00e0060a80c600000701040501d0018080c0d0461030101c0d00101c40058032907441c0700a414030700100d20449a4031604000c0706425881c0c02d9030240302100416100000031a4000003482a8801c00d010041d600131814042001054400c1c1c11030a66107541d4002c0e43c0b2000d01182c014010b844540d00044c0f0540c00608000761107040c54040945000c01c0c000f17003401000d0035029003a8403030400603814564040e0081c1c40c24640c5e0083c442 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 625492212 1250 625490962 625490981
    0xb211e0f0d081b030412260c1303200312040609090f0f09150b030a050606210a0503031603050114010c0305040f090204080705040b090a200a030b030c1c02060904 71
    0x40403a605d103054908111168480b00361180031a041d00c11200a410611240340090807120b03440c020b1079100c068141000750800c0085041a41ca010404000188010391032a81c5694251100c0510200030007050b040c040f046000152858091008020190303008802000b01c800e00c5d000098003d80039400d11001d045008400c112480c00c005000003081310342c1c0c035410142c03030b02200d0800c50303c44400105900e454288402810603070102e004242d05d4600030381c0540d51665000090100881050101401c010420a059450303400210070440c2605100740e003008a008585010001507040810100058080d410300e903040040003030760b00b4100340c0200e080350301400d81d4151310300d41d40f0750300c44400d0084c0d40140a8080c1e07a001c1c490000031203013094040d8081c00c1e1001031046841e680c07550841001000c0c0a1850401c5414030700701588482c1c107140c020024540c5035a40401c84900e0041814581209854080d008a0780245d95140c4110380b0540110300640c11600d151b45c41c0c0440d800100a400d5008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 625493462 1250 625492212 625492261
    0x2120705030a1b02100b010201110a0806060910020604061a060304061a060c01060501021c17070c230c010e0a0b090f040f0603120c05060a0b211e0f0d08 67
    0x214403c4840741c0000d114005008080414084501c00e0001282079445007402e03002049818420960380b13a0007845442d91110015000d80c0c2130481c5800014902d10241c3c1441c00540c1100c8113200500c50b060041d06035480c04021106400074400e404118188002070014062950300c07500500009031024451401000080a05803641e1030003a0701c900801c00342c4543c2d03000d031281c03c008128400c4259920080707080e19803110410385104440d18601000300400301000c03c5050200d180004605400c000001165005400c4100d0491720320305140407124801b00d814060b250700c17604255903070700c1c0882c400d4035219403056868244040100b0740407500c003072520341d000e8142902910300301075a52105040b40c1c000c9510364070070b0840740c500762415985c00c2c0000d8803d03000f040006220400a4100c504d1021014004020400c40c0400301140c507101080c510300e55401210b900d00b0342441411496041c000c2d0741e40a401e01141c402510f80c1c2d03c170000c4603180c0a002d090302c0001c44c502c904600040d44c50044c213 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 625494712 1250 625493462 625493501
    0x31205120f06011805030303011205030408101d1f0e0a1e05010c0f09030b04030909091103060105031f050411130b0a150c0b0414032b02120705030a 65
    0x190301401c164216000c50004038114001c0e20350131512007901e011100040c0c003640c61a4201030003201c004030b0400050710644402c0000081407d8104940051040b19201c00211200c03041c40122a0a50004043c4869032186a40080d01008078061041058420034001810541c00142a060084030b00010f884544240001154a0707081a000c410319882940204000d034080d000581d0f0421460100e2400100101014070019041d410500e0b0801d0203400c1400c9a1030350340c0c00c810140c1300040c2c81200c4249450041440d1400c08000d0240508012400360801d0144400181c0c0001c07c0304521012098848c40840d041c40500114600c1540d0045c0c01c01c0c0035020309048a01c090100d8181d81d501440c6d40510000b00e01100ca200203d2034070300d56076000d80e00b0382241c80345060400e01400a07504400c916681e110208000c0005248000707801c111035588900c0030741000e42000c10041c0510345c090042000d9000c05201c0b440d204e030b04c26080e007001500e81d00c807100c81100130640310061107540400e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 625495962 1250 625494712 625494721
    0x12a03050c06010f030b07050c0712050a060b010503070c0b040c03140303010f050a0501140d0f150501091d07080705070b10052106070c0201021c0f17070903120512 72
    0xc0c03040700086812035001d6680e80f00104840b442c81c1c031014104072808004606d4940c818002421502c01c0101211403140d1260440c2c03426001d1600d0489087d031150082200f0020301c0c0c001c2c0b03034000318242002c5046140600300502085115a00142081c980e00001002c000004e0b550b880070b190000194004481d1805116540b44e000f0300a181030703081050000603d07464504d07600000e079a410380d9030070850411300b04110726a0700070300d0b01d000c2170a8403800c0600c904001480b6501c080030841d414583c0c65464a00003418003103803508502800307000d110742d02d2480d094022038181c100342c25141102c1c5c00d599244c0c08035824060342d007000f00a80070f40801e10403041074100900b0240c52086130518080c142d42004620001d41015041c25290031034000540b40500808034490058018015034940c003405a840e1012104411001004203c1100d49001d00ba0342c03190140200c4c9001070080591418441c001a0482603140300c0100440070084414005078030403000d0382d6403045c91b15031300c0d2443e040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 625497212 1250 625495962 625495967
    0xf0c0a1206020c07060503010f080c06070b070c0f060522080403020d02241206030606030d0e0616061b050408030405060f04090c0305180c0901120503040b0307030504051515012a03 79
    0x428881c06003274451011020a80000c0403c0c4070312508070041c404ca10f00300345540c032081c2082c0000c1c1900c081c040540740020103e05d030100c0c0b0101d03070b501c01d400c009414542004908030320303c444045405000220540d0f440010001811a82a40d804a542e11034035010b620000e1141c02604450081402c11401401200099480a002410200c0e00c400050b60390780002d0543d218000ca520701d078117070f004005085445020705005211f030000034143d9442c210750f00309500700e034180780281129080d98859580700e095540c5c00b01006866a540781c1640790500c4c005250396a4012401554460000098210102c480c000115801481c6103030f010b01c06141100c3d4068014503045600e00880c00e00271805074110b40c03000c6801d003209107005056011690070040800e0401c0c2c0b140380103e903d0b1004100c0422400c1580c0c025500c5030b14a03a90114242c640391030b045003040904045641008201010310181010030b0400085400081ca44841701c0c02840078105e001140c00c60300d420006060448a00a02d80d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 625498462 1250 625497212 625497217
    0x8010603110d03051e0d0c1107050303040b2205150c0d08010503120304020d020a080a12030c08061003090606060905120c0d020d210c050f0c0a1206020c070605 70
    0x1d00a4101006414688041c82a0040e002c100140060300c10006482115a030485030360400007200f0941c2d0400035904400130803140300380d08070340111310340440e40540030b0b1080240d0806044107074040d40c24a80b8000b84105280135907103407002c003182a0a803400c000c4102c07403840c070300a190041285051050507000044640e01110840300e0b03c0c0965540302951a0144850760704858000d0000c0c07409464800300400c5a4101030300c03c0368090018140400545d40e940000005490f180018000078401c0346401410384000755030903400d142c2031408001200d81c201940c1503220700d05a40301d429640318900c0841c0207003c5802c00800203443c010700402c5580d4844820420340700706541c1c0c06043c45440710316907500c2c4920140945c8c050881d100e0b010060804250b138442042c4a84101c84036000b0f4801060210401c2c0744c9410005040300c0c810100707203c0b04006c41021001c241024107801c810070340100740040340a01921805804103040d500400405904451207a049034090f81c028986804e401000740d07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 625499712 1250 625498462 625498469
    0x309060a110610090c080403050d09020301150f0501080106021c080613050c03090d02010e060c1606060303050304031202070c26150624070b04020d02060c0a1b03023304080106 77
    0x201c1c50b12001c171480038080c1030740b40d000715095103a080c1000701c80d0101d80040c040c0307040201e0309552641c03017001e800150134030f2282c0501110075004000b1418040010014407050f07200004660000d074008030003c2c00d08050262443c01443c2100e081d0ba00d000104048141c5202d81c80c030002c0c80c3c202000b460a0a06010f1805512743c002034411521119008900b0703290a4260750b070064001c440810504c0000c4ca00504040580c50424038400b40103803104000c58907641d006a012600c004208070030141e101038205d00c845031920003181001401d4590440b0340d0a140241805211542c9a400b02101c0017010074041100880c00c544504080000c4199200000d0345c0242c0141c405040a620034251107200d0551001c03c011710301e0038103103640c40c1e640101c00080e20503604401550003110168840c10018042212050024056581d0070310300740c050604019001a018482c001d42807005075076006580400c526090081441040503175481c1c10319001204813500c5041d00000c00003100501904168104d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 625500962 1250 625499712 625499729
    0x20d0908030403030818120c030d140c1c0e010c0207050f10080a0207021f0c0b160c020607020f0405010303020a120212070204021b12040f05040c020309060a110610 72
    0x216035580100079940e0041d4000100851a4540002d00c0310b0580d85880381c0c1c1a03c05412103440f42c24541a5031081d82c08102101c8040c0c1000428240501080c09640362607601c5150100302481e0101212a141c0907402c284418800301b950715540c4004140c2141808c04c407254020003c11445100c06543d401440c840e640c050f4900030140099031505528500e80c0a1960304d441d42c0594074002800000d500c1031508990060244004490321500454606c0c0d04013001d0720362000e15010390608101155004040090451071005110255a80a421103650f0f56040e1081034407000140700262044035600c414507001440c1000000a1546c0040d50680441c0100380304000900203500807a210391501038054900141000341e2001130400ea4000c1c60b08054004618008525680d402402d0801c20007040b140ca01001c60300340070040040480c038005000441d000c01c5420380c141e07030184d244c2c05554541842a00046001e901d8640544a81d100c1941c48409680c22450b14200c406040c41060148240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 625502212 1250 625500962 625500977
    0x2150913020a050a0f050403050102040b0423030706030914120901080f010503070e04060f0501060918020418180b01080616170402121f0603021903110d021f020d 71
    0x60200680300320340341c2c0151941da181c03034940420001d890010b00c0305898000c1150410000000c98001e202400181180d030804070750701e80c1b0b00f1221600c069104c1f0b240740c2480302d40081d550b000381d40c0082e2030740440b20a4100440c920b52a07040461929090419049c100c0c02190220350500c001c1e40000d04045c2400d88900c292a05e03065641c0d4013070502401350755003540c480d07402400100c86642080d54403520440000c2210320343c10f80750302d0a07164207034004d1000c100482c2c001c0c0203010214500307490180407658114109803502403416007981c00981c910300c1013596940c00c07800c4800584da0001c403286c1c015000c8485565910b650940d54038045072025040c45031141940c48143c424203c0d000154107002c0040c03200e450325020051162036500d8040103a100e00c55070003080401c50b14107104803650480001a0003451401840760b96400303caa01090446a5030040c000900072455a01d0031403c2510b80381041ea480d4808581124040c441e44200d8003100d010024500e9400540140c54201c20b680d8000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 625503462 1250 625502212 625502239
    0x602070b0709062a0f0f03030605090615180d080315040f05010b0714010f1409100c09140a0f0b030a0c1d01031a0603010807030501060f05011b03020a021509 69
    0x2903080a0016080304440f41c4c0ca1000295803480c0380c20f804400340128a00d210b03408140d0303141c88180348003040071000b20344c880780b04110030301d0107141c500c0d4444030a031641021014903816821080c807807a51141c6030b0380040c960f091711507203500800382030107544042c0481e920b05051019030f00f02c034070140840b48280c0c10312203c102440d0407405014101e40385014190304181c0b881c0c1e10301010f540c1d902211002e9640c0c4100300c12120b00d25024090000301c080e001e403072a6042c803144c41810301200308400c18a441c01e1000c004002075001409800300c0d900300803050104282d000009000c0c0701154000b03928921400d102082030001e2800550140c288410300300b210742d0241c0341c196001d850103810a1702714040b0721190161540290020b04d8090002d0320483c4035a465a00020025007003a00821a0342d4000103007401042000d200d120003800c01c0c00e074030b20403061500b0300003030070148000c042d49003409181c0185001c06000308022004d5560085c010104c0c01c555802d15290f50b000300c090349100f82c14007003a00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 625504712 1250 625503462 625503467
    0x908010e1c0f11100c021e06010b031f0906090e070f1a04080712050d02122a1f0b0423090304091503110f030601210602070b070906 58
    0x10103019260302000c0a040703089860075111800781504031030901070402c01d800f2103c103040c001310440c010411000100008402402490302d4001d4140341d0f804801810115a5200c00180603811108840080c603941d981d08a203508440e007509020701074078441c0600101309202d50f81c201405445402d003003040605040a000d60380d4020314170a881ea1144035801c103101c0719460502c0d021815402c000e02d1842d05503182034842c81c04480b41d0001d000304600c481032108105080c40000b042c40e00f684002c1190702034014240b821445000302b03030355030f03c071204101c42500558802070321180314500c0d080d204804041184c1d0014800380101e01c0007801d140142c00000303032030184a104180c00b0310007503c00307007040c800142010722500540801c41600c0b06200004171082c803805950000d141281654006629515142207114003100d5001d110f07000c1031031084a0383d00d000500364110b807140c005400300350890700342400c0c085c001600054100d50001404c2418403915171030b01c0b070280c0b000b5a204201d40f035690204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 625505962 1250 625504712 625504723
    0xe090f070f05030a0212090d03060b0a0801140d0203061608010b0408061b04031e1b03080d150b0c0a0b010510140c0c0a03060506031005070c03080c04080d0908010e 72
    0xc66020614124902000500c0703480515845001c80c0001840d06800004001401c042280c1003a060380c0080c2d203a2220b00e6140c01050f0082030182c4035a41003032017040e00500790744014080c42c100c001620b40006219030b600c1030308441d40398014040e9456818001490040890030064207004502c0b80e00000503502442c400711400c4800c3c1502600071500c3c0c03400c40d0300200f543c502c0307000a4402d06000100100741c242100c60541c1c200c0c08800d89940b159490040b40007000b44048100c0c0c44580c4008002007520b80c0111034031503d1000c0005080000b902c8500c450700d40c540c002030f074802c81c0482d00c00b450b000c00040c2e100e009c6018442070342243ea81ca60400111707003032101a000c000f4620802055280d001000609283714140040d6040c086581001c2a61214664801d59401d0b0321001804481d0405208008940c003050340140007500e01480c001e0300380501e0701c8009040040b0000043c00f01d00b44002510b0242014030706450544941d40c0b0000c0425046010f00016946070500e04515824001003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 625507212 1250 625505962 625505971
    0x60f02120601091511070305030a1809140406090c3f0f020925032403080f0c10020c031b03120a1a0a0305061e0c0d090302030706020301060e090f 64
    0x10948400310751003401c0fa811782203aa41c03240742e440345080200000c2c0090000d001c4010407903440094002034140d06081c10025075010809840c60094610590201c140e55a64400d4010f1000b207850686440d104111464580c0403a100701c0c080d420011041645044822013201c195580c401180d00b0000740c0c001e0940020401008107102c0c6008800509010b1411036200014417000540803c100306400c003001e18010300c24002990f03070111380d8982c10000941c0545031841550244d8800c0c11581c440c03403284550300b9035445110001c680307000301c11400c1014140a0110314000d6441e80c000b0715995a0b203802c02040b0000030511020160900f010001c151600004e070b811112145031109000f64000700821044e0043c01640301c86801c12580f9643c41c404011031040c00281007614002c1544c0448020200c2510110003104051108030f003144826a07100300c003191030004882c205494141d256200301c500041c840c500100002403455009080c00300c2400040d110905140d586c40c008002c04081242c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 625508462 1250 625507212 625507229
    0x210c06010e060a030b01060f03060e06010207060e0a1806030218090a0303051e07090906050402070f1401090f05030406030605101709070f030b01080f0d080a020313060f0212060109 79
    0x100641076624070800d8020401401940b495600da4aa40b42003c00c00d13001500800e000f0a00b4039025a03051103003200408000340c4180a900300000000d44401042c411802001401171000b505541d90641220040101920124002c1c0d4840f180344003410891109a1168203a0340c50005912109101144182105005829406100d0780c0c1a0002c2c000501030301c02592900e01462541569222140c0c0140895100c554a06181500c210140c45c1e040d00001e00441c0140b100400249601c1c44801d000caa100d000030710120000c014140c0140080b0700042c2c016184000346c80c087c84400702c001c0085c0c5865907030a1024940341d9003800400c40400e40c0795000503030800d11003c40140100d100c581c1102040081e21000c40da2805d4001200019400070b075078540c4450010000790a0411001203510b480030007030030020f01840f0b805414550000c1c000e03448250000009070b803250640780030a207159071042d0200040c0e1b4030f20f58880300a400031982c50001c4c5a8007070100b41c4960089610070b04898110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 625509712 1250 625508462 625508473
    0x30803070c080f0a080a1b052d0415090801110427020d14360a060c05040e060910210f030c0c0b040b0a05030603030c0609210c 56
    0x1050201d544040c060300a4501107414800291110318038402080d10541980d104640741c24884469011070701c81d882080c06407103014a0015800b504441a1307405224107502401800000b05403840c050a403d00d010030b01a80c000a0204000480503d1945581c1d82c1d9036070004882e440b0b90045080b80c032803800c0c0c010305140c140010002403001c107040350342c00c0c0348070020581003e83d200110003d0b0382020040c0a519074444803080000e903000c0c0c40b11540507540781017014184a0f03003825074000a455020303070000550008030054104008205d589203041d4001e40030004400b1191300100180c002d8000c0e41801e24003c1c01045c401c0c9441c0b490346000b081b00c0d04c20810000e19080141a040002803c01c0682c88848050b81740440c20302e040c107009071402615080760082c80c4e40f403c0031503030701c03907030003510081c64140f10074480032082c00103a50904d00c090030102d035a500d6040000b803850080d6080155248181010450b11310800708100b0102c0c0c102c500401600c070882c2c908040036001d105010542640301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 625510962 1250 625509712 625509721
    0xf100803070f05031e0c0c0303120a05181005040c1e05060901030605040603080909070c0c0509040804030f03020d0801140915012f0c1806130e010612110406030803 72
    0x8004002c0006031040007103918000c804050031030140200e844030030054a01140c01d0f240a0024401c000403510201c002c0c510304900903503240703609400a8003c051700d9aaa8000400811251103611880410f1008650f4000e01c6604003501a103000c8134104d41003601104002204140d803075034040003050580001359071078140800c1c4078581c1c21150400d0304254442d13400040c03a844a06c40d01c40614011205166210114000d00c500082c1c0134010300100112400303108046007124030524144e4100700d0b01000540c907142440320460103140c001a0030b520364412030000309a00083c0340082840103441d1202c50703aa071510b00d01c80244200107000c0c1c10040c0e8030006020714240e82440000800d050510784480000c81c01502c5109141c42107854102560910f840007102042006598010f0f00b1180310701007003200c40c565001c8070f50140586025003851800402d040250b80c22a4481401e5075008001e00780d552409036001e034521840941b100c00c514080c0f072034103003898010842a65000321885195444 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 625512212 1250 625510962 625510973
    0x1505030a0c030605060a021c14040308030a09020402160605010e01060903080903010e03040f08120315060c0109050f0d110105040b0613020d150501180e0a020a0216030b0f10080307 79
    0xd403a0101020555200c0700444c640e50740c3c00290440309416801000d00b0100c2170102d48045085480b820107001c0c00c1e003c1c0007401c4050f03008071400c0e41d40c0406901e44a0321a004c440020b0b03c54040000d50150010520306044008409400780c010700900042c0903599885106048030700c0c1c01e02640d80000e82da05002d1010030f0708640104a00c0201800005919401e0511541550800d4001c815500c081600410002c00108429201c4070065515a403440c04c00c40364092078600130741c001e2801244086101c0b040300754291b0028100a801071309480721012101d424540f255000c03217140b40894042240222078110521481b4820b07584200c00300041e1302c0b60340811050400c0221800001902005800075000c0c242c003610920b000500741d20b000c444d0600c400501404141d001c000c42510a009041040c80b843c90344182d0043d02008006a60b490f41540407800c00b00001c07040c1619079400c080c000200080c0b04051881101c42240050301900c0d060300100450405103e8207031103500a00c01c40307003c5070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 625513462 1250 625512212 625512221
    0x31f0b0f010e2803050123060a05100302090a0806090d080f0f0603070b120f01080f0a0809040e071706060d031e121401060f05040f09023406061505030a 67
    0xc1c580f002c031108080c0f00d03e1050011181e0300121050b035160381010302e2451a03441e05410b0382e071860f81c0d1010b09141c41408070300002640c6c410705101b03400d10700c0955607160003a0704683d030a120151450125036110842c090b40c03800c054554800c103110302d2005600140c403d107081030041c010105a800e440c1c071521780b401d840c9030020384020f030f0500401c1c200150030700080c0e008010703030300c00000a465180340c0702c4a02c44105805074440c505030b40144008003c0d527440411547c0d120b43d4044a804d441c0c004090100300205200c1150911030700c2840d1002c101d104849071a4040e2415540c121285551b43c8018042580e5235a140100810340981100780d40d00d02461861481c0c026a180844900c070300e514040301910500343c0d00c440c0d454107200c0140485030f4040c402460008407800c08500d0145040002480785006105100099070302003a0036200c0341601c1080021805200104079032400c62100c1120706040550701150810f01c1e0000008030300c01c81c5030105181031026102d080c01d56540002003070160 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 625514712 1250 625513462 625513489
    0x80919020906060910080717061809010f0204030b0105030d05091e130c030506010f0f090e04050c03060f25050d0b0f220f060b0316030b031f0b0f010e 66
    0x3c03001c3c80100015181c0713645d20340580703050b642c0d08540c034101070101812025200612542032441c04c010001c4613200d40044a08000a8140d8101d0590380c442080c0d00400e01c404141c469a40001400000e215900080505803041207090740d4010044040c2901e50348183e041c1c0c0c6070052a40e81651424000302c11010b0700b030040c0600010f5180c00d40c0b8070000c044625400b03a11012075514020700c0060750307204840342070300b840505000000c1c0c500d614000c1c110203924861110184801d2000a08002043c0704d0a03503451005003c4070f0050505540d4074210308002c807804503000103003125503810882910380090f8500c00b00e8580c1c601d0301c0e0300d4500781e00282000e6001c1c0707500001c0b141c0c0c41422540700c0400710700e288040450030b216000070b0407920b0410f4940391422103403031504000091000d8000c15089a40082070300416945507481800709030007800d84062601c0d41f5020740c0140da001c0101c3c0c800002c1d07111445950402045041904010144140d00320f9140010600e56049130303103013414401a200c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 625515962 1250 625514712 625514719
    0x30c01080702120316081501080a20040e010e09030a05122805150a1d06011106010b0a3e10050c0702030c03060106050306061b03160201080919020906 66
    0x10030f0804101e981c1c0f141d000340c803140d0003201c0c154000c0c00e24503402804190401c10200e4400c1d40e90311550002020300e440a01070b2415143c0d940b000c21148400340f5441c04101707500340a03a070785495039038002882c880300901c00c4500d1024a80c0001701031540c08003c980c00038005841d540d04100a804c0ca4100d8664028071800010380d040240740b0198228070408030360300d000b49002091034070780300d03000b04022000040c03941d007c1e82e018281400842c1001591020912070750003aa840c1399103100048031a00f03503060ba0415140100c030000300d62003409030024000c890b41c580380c1002c0c20612a4130002c0f40c8a00b04403c810b0702d074001c0810a590602d015003194118510703001c031501e111685071a4012030b41c0a95024403801800030b2242d0442c20300340080c0703000310000c401030034166241650142081c8401000c07148140c2c0002070b040012a2900750032150307243c004080781e840700c040b00c08002c40504081000e90206d1034510000b242564001030440c0d10301640c1c012503d4207803660b4248440c2d550080c00143e032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 625517212 1250 625515962 625515973
    0x1d070e040b06131407021e210f03090c0a050109080613030203040902040f030b0606030103120f0912150e0615040914010c1e05042105070302030d030e0714030c01080702 74
    0x20003c030b280c02083e465010703032008000030307090010001c0d182400302100c0c2110008807841014150401180000941b0300002900c0c0905a075680896594812500c01c1591845d003c03080c071500310300c0050700c2d0580e030360151200d0814a80f1032005440e225060701c00d880c8660321510005d03503a01b0350090005941c502c6401141d051070b0b25400f6200690300316030014200c0509101003001440b0081064030b4011805441c0c1d20325650550700c603001d8480311a200306050004509038000b0203031045040900074502c5115070364a03031240340303001d5032130041005003a2121307810f042c800d00001401240c841d01a026100398180c00c04182c41c24400900303000c0c001a40d0000384400d411001003021300452500036100d81e9000e2018824142c01008185000d034001c0030408107010a201d480001840c60406110064103c003120302c0d94030f00b961800b4501d8100a401d80641c0052130751440d0503401c81e805c40e5000f1170135241504d807500c0542003d00d03448000103916074080b1520640c0b5500403440b094218030640306640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 625518462 1250 625517212 625517239
    0xc030f04140a210305060604151d0d060e0f1b010e06130b04030213060806040816050d020c030d0311040303031d06010f051507030e061605101d070e040b06 68
    0x48031101d00f52040c01d48410f12a0303504048951500c42c903640300500700e54003402e0609086c0c44080010101d0306000c02d0042d40c9914403509085009140c2d62180020107101c2c03200f02619001015000c03410b04a002c81c8200c2c1e0a070821500d001c102d668401c4184601d0201340f540e44001121980182980186c00040411007407580c55600301c0700314041c0c4a03200703206c0da07290700d180f0501030b07100148004200090300c1c145040c0038408010030015046908000c0302511010790a400c10740c00c409003c0020150f10646041e482c4041d0007142071031101030101c00796040840c5248040c2c0a07240f02c41081109414200010b01c0041c2c002d5000c000e011030740104251001d46c481f0072a5243c4a020b800500200f528142e080200340b80901c0b10561a81d80d00084a003003c0c00c51307801414845001080500c940c0002c105410300780c000ca00401c007219002402c6401031034101d00342c200207101c0c0840000d040800800c0740108502c000500743c04482c0c100c4250201a503da03141c40840e000003030b05060b40604811400b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 625519712 1250 625518462 625518473
    0x15270b04020c2a030703170904020c0d0e090105191e03120c0c060e012003160b01050301140106021c0212041805011e060302090f04060e0f0c030f04140a 67
    0x500740602c41e500c3c101d0071014040c0070400d140da060410f544a6401200140b00180108041060400d4030000b956201d01070030300003030043c1c0a007179204015032040c402d604e56021f03800401207602d00b50a440014a51340c032501488030310308007500800414003003500204524500d807181140340e50600340c0121a116200c0d61141c44002403410a0070008407070100d4031041c4100c843c512001858507041160300041c40d08006000030018428070b068030030b00b10b001500402c1041c1304a81c041c0120480c4d910300314207076141120000305c081c02000d00070f42c0f8160394050718149a40342c050680360103070004d0550000c034101d070842c540f83c5014050110b0207821411000c0900c1c1001034006400194410750031164030714411000c80e00140d000d0000f070168004e0300100d0811a00d0564180d500c0c0f4038005d070745c404401c0042100342d01c0c0c04503542d03005440c148000802c001e49031a0180242600c1c0c5046e18540c13980a01c140f114001038455a91014042001c600001d400701d415420302603251060390441c102c3c80e03c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 625520962 1250 625519712 625519723
    0x2130f0510080a1d100c080f0105060904140a1a0a0506040b0318060103060905010e06160309060b030f0f0610260f0a0c0504060e0c0414031c0315270b04020c 69
    0x40303200c40e401031503128503c200c14011201000507a24080c021f41c9040d0040e07038810401880358078002d10001071003c0054986401c105621121540c0c0020141030480110b401041c0c0e035002d8070344807032400c90120442d15080101b03004558008000300c1c01c080c00c2c413203c010031b0340c4090706002400c49201c0b500e0007144803c0c01141d0086019400019030300000781031aa096a62074880d460300381c3c02c0315017000841880380c40000e40710342c490b143c00034142040b407030b00c40018003070054210351600c900c800e81c0301400d00015511300e4844100d01a500170743c0300c46c04203a841c125240901c1c1001c07801c00001e4100f0308954506900740086060480c3d040004040c286800d20395441c01c2503900703a80c401001e01c0f11f403d0134003a1000500440c3c400280d28a070070061001580140c0c040c460341c2500301c0e180314090740d508110a1000d101610200c80030006225805002031030031194003a40800e0350000094440d00d80402940e212017485140d03041a0f0b200c1c69a080140084448030b030784a542402100c411a01c00c000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 625522212 1250 625520962 625521011
    0x3070c06031a0409020d080a0c02040608030a1106160e0a03020d11040b03030405030604060f090b10091b051b121201050310090c030f020609060d02130f0510080a 71
    0x40008400140e80b8546580c07008249031940550f00300740d0140700503100e00720036041103130b08004c00d1a1240758031a01100d008894020203540300d81428800303c1c1401c40440102608429500c906418441041030141c8401041f52261072143e0b4950088500501503415800d023288014942c40b1041e441e580044d0300814840016101014000b00010180c00d080c0b2907502c0e100c1040300214105890302e40000c0c1d5583e0012310003400c00d91a21410810030000f5000003001c180d0040c013410b210b18002d500c1e80540790443c4120f4242900b4041c201580085034510214501241d13503c491030018100791807910341030060403c400718824102c55010300940c80018103984000c62020f5141540350100b0035141803007155008111038646069000001c0221000c941100e40c4030480b02c2c020005400050400d010307440c3d600760015000245c011070aa1607500400301c05040ba000745c98416140e0f000c10b9500503580c010141c2140a502c40805414014441a80e000c3d540d4500451884140c50040f0080042c521 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 625523462 1250 625522212 625522217
    0xb0f01080c1614010507121b0c060204030203011b020d0e09040f050709051503160501350f0103140d090605130f03030507031706062b05180c010c0c09020c03070c06 72
    0x18882050b41c401c1c100005202642000d00c90030440000c004000d45c0d000b5215009e0020782842c0d02c08100c1c103034040c3c034019600100200039007005e0380590300301d00f40c2200c00c083c014041c50010307291180c0600000d050b07412010703010b146107599070ba480c05500c0e40040c105840511541000003003042c1140203181c07084554404c4000000c440f01b042c1860038800c402d2440c2845012207082c0000c1e41d02421010b4410041d02c10032a0040d000000c20a41616a001215088045c2000c000303030004440c1896040f00c0c45106001d64011147d42c00a88030210408200300007192010100000c0e4410030140c1807110043c55041004d903034441d05080e4000040c1c0c402c4001c107102044003000d0580044d07500d01c000304003a010f85490f00e080800100d882c4a0402d00049950081d000110100381c581e618901d2101c501000300131a040c880b14040c3c00c4221440043c2c02d510035070124205651003440b100f01c02d01d508c00c030560102814520101e01a40008031a519588018003c41740400d4110102d100100f1454 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 625524712 1250 625523462 625523471
    0x6031801061e06140702101e08011d0f16020c0307030b090c100e092e090b04020901020705040504030e03030316021c080a0504020a09060b04090b0f01080c161401 71
    0x1940c40c081c02c2e50341e8444000d110107071003003044022402044825440d8125040c440c82e210018055841000d4010f8070a04210240d41e0038441340c2e08445800d05a902c00c0000344024034441e010508114030403150085821980004240f002100000c0c000c03005403180141c540c0400c410700401d241031890340c8140d61010303254042c054100d40c14071404000c1c85042d0303221401c1e101901e801410000c2003000c1903019000600000d90680d000103180000d90381300580c070f00d101030050845034004007801e019045c0803601d840300e122010301c0d19100b165900001a009080220710344420000203181c018021f5050000b025003d42240d50f00b40000c0d0b03c00e03001c2e41c60071070000841090080ca401e000c00340003800c1c0d20340403048500450700008410b503c00c90304c6002040c1c5980d6031010030004c031803a5204c00004c90804001291441403034000c0c1050fa042064100910511a4100b01d04900b030307070b001c4601240074000462080d07402540200410ba104403041c4400c40c05541d94690382c2801c0b25640003090752340e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 625525962 1250 625524712 625524749
    0x130c05070c0503150403080a0b0a0b070303060b031504050903091504091b0921200f0402040509040b0a020708120610020706050d0e07090504060204170a030e0603180106 74
    0x84454001c06804150024800b0000382da9540f204984054000340600030300c40d001030004029034200321030b01180980403c03201d40d618213044103640c01070001100031074200a004a070906514003a28430403102200c0c002a0407121100b440001c0101505a40349030004000d000b0041d103a240343c525021901e00441a5a146008600f0084407200103040d2411400f40b420380c805564881096410b0300c07000d0511440454038940a502e5507104140003c0030342e0005060030000d000e0f00681e07280001d000340c03281416030082c2d004000403031195000b5144d0010700080480c2c0032520313203640694840c0b402d6a00526120041c4c0704e0945507004180c400c40306502d02070411a42d8144000c0310100c1981c0ca0004005203420000058098020310702402c2d101c5585828210800500704001001000c0c8154100410b0406d400e051001e503200c5e028030407032010b07000150589188001500f1041c107405503101c8200189600410503d0345c405072043c00d080130900090245000280b0860005003004000c640380d200c02e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 625527212 1250 625525962 625525973
    0x30203040e0f061c020102120a020c03060906150d050a0f0512070605060a0b070203070e070e04020c0c01020d02120307031107021908060603030703091e0e07050d0f062102130c0507 79
    0x307510307001d00c8201d0131000740500140d80018402c404c4505041045450b0380e10614200c1c9085454100c2c2a458410b02081c000d068501040e000e0281403440082686900950107001070f0b0b480c2e100303000f031055002580b03503030116400881c03002d18a0b00c50070039102e0851210056103025000b0000030b482095651051281c1441c20544090051900c06905400d1a04030340000313443e0805032180e940d001280c03400281c8158400d454129070803000a100b1034503000117661265441c40030070007542c0075124548000d078003c0d00000310a20901d80c0c800109207542d50b451011009414090a01d00015005200e40c50050f5117200e20401e00b2405147c0c43e6207038600c0d207460589070400180a00d4001c0d0820002100032030f40c00900703482904c40c04a041240c007a0501c0400b81c0b03694841c0e00042001155000b4809807581c400b00500c411200b0070390612100705030903c44421501c1911a069150846900100c00c95202c20300300c1155a00041092092824060707210054171008030540b40028000102c0c0300c104030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 625528462 1250 625527212 625527229
    0xb0309070f060329010503040b06030309030d0c0c2103120f0606030506041d03070206071502030708100e0c031501030906020f0a090803030c040b070c0306150e09010b010219030203040e0f06 83
    0x113920000303a044203004500003070030a2202500c040d100c0b407640800108992401c00c12100401c0014003201e0065129880c00cc0c42c0b0800540304440074a68001d00058100441d02e4083e080310341e0711801824000c1c142e405440300400c031052200d1894546042842104143c070807580100195240412580341031800c2000300c80d41201034440f80d02500140020043d0000b060741c200d5581a681c0e56030750240d0b07040c4010480804491014020700010030032240c1980480d4003801105401d1003041110b07113a65044009020466030603013030500500000b401c0d003a880c02003240a002c103040000e1404120b441c4c04c4143e0b404080c019549110000c0c800c0ca010354000e441100401541001d1421420501c000d04801c0c0304610500400d1030000c00c0c00303c144610394107100000c503442501001010f180c411049403952043c8502441302c03090900007401c950040c040c1e0b040c024416805009888000f40244440002c10641a01180f0040c400070510320003020b50309004001d03c146000852030b1a404204006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 625529712 1250 625528462 625528511
    0x40c0f15110105010f060e13090c061716080c090a0e0106111603080901110d0206061305090c01050a0c1a040203010c090f030b0c0f071103060601030908040b0309070f0603 75
    0x343c0c549401000b1001501ca0303d041500d0407441c1c80312880341c1245c00078240208030040d007120641b40110510400c0f402c100a00d080301c01503110700c10040d0798041c15580403101200c5150480c5014110030010b588030740000c540c00914060f4982c241884c80300443c100c083d00703800556101c0c190038011b02071580c01603503030b80f02014080010842101c11f00d441148031a2a44002400c01201064040030740e8014040054448801d80032035080f813108400082d50340b00180d841502444003844510b161000c10700840b84a01c01582c0102445555200115440c0c6e00030b100140130010654104000104114001000c0b8842d6508115280c10140101401c5403010820310040c0012448104240100c010348042100d420130a5052190f0701c16214810611921000c80440c3c00006035180c108080342c010340792281c000303408a50071a51500e0040d4200ca001c0b09019140d00c0c0306100401c80a126440111b501180700c0059604c004e584d60040c000d40c88064100202183d00c52007001c41000e400074100511 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 625530962 1250 625529712 625529747
    0x170604050c060708071205091509010305070c02030d2025080a050607030b0d080d05040b090714040209030c0a06170c0a1e020c06031005030f01051608040c0f15 70
    0x50080c07036034842c81148a0000006c04000203070803010f1000f40608240e50468002800b818691040220082d246034011103610740428600300115460511401010f40c01c1580a00100185540c108003511110400c10401c58001207801510114034024030020030003010201c2200f8660048ac0522144440745402640446c2c2c800701042011940004110f03411200900340020340c21200004240d811a08050246c000f02c400070341b46031188103030352084e803083c0d00070700d46200b191725014085600d4281d60310805542a07000d450840342443e242d40108010f003002001c80b84c0c0801e510010844c00c140e540d2010000ca25040209912108a0b40c2080d80c0428604202c03850114480006422075100703424136810703009103a00810076940200045610301a000342016183d240c041140030a103400d0703000741c50003401001084007a4400c14040d41e0f00900c81d01700d035400191b001040440d42404001d1081c2e603801031a400c0045c844081003403800c01f810032441d061807a50703001540074220f1307490700784503e01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 625532212 1250 625530962 625530967
    0xe070602010515010525061b1206150f170a200301060c1e06061419081b0a0b040b190c0c050402030c0408190606060207032109170604050c06 62
    0x5044c3ea110b41200c0d040301c6071411410800300d80c02054480c10041410081c041850a12090040c902d450854072511065a581c0100002100513820690340f40b88140b1703080000e254244010b030b5000e08a030002d40035062810041004094942e00c002c040140c4480c80703210341e15540c440149491803000307103104541508041c91549000402051140001ea0103402ca010300ca4465000052088038101280c0c1c0044080c00032075221184c20b516076030008c99880c490001100105180c0b03040c13100540850340b40b030000e01051500b00340d00c0080071900c401d10590082100c840400d210201001804c0541640e6005ca500d40383c60300420944082e03c440c10700c00340651000c0c1c00001074036140c090b40903950305490141e22a01c4840400e15180180e130054241401130b07180b1038090301d064203000c42c0180e01900c014400699100d4060ba01c1e000399010192040e00c5410907403210000320001007002c0181d514080141e5581c6290303107141c0d4000c1d003a510307625812210512090080400055080180407103c251 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 625533462 1250 625532212 625532251
    0xb070507050a030c08070b0403080105030c0d11100311030c07020108010518060d05101a24180307030611030a060605191b0c320a03060b040902040e0706020105 70
    0x30b0b55030003004001420005000c032240100710b0103c050f21131040d4860584401800c00c1e2a000c0c02840c002d01a80c0d000b4419840a110f15241c220040e00d111600100482100c058003411301501103420000d2505050700c40503854459844000114850305107040325a40700c0b00244001098080103a0000e403060b0703a5030502c0344030f0f0002142c2d06070300084102e030003142d42040c500d0010b00b49030b82c9003480c500d0760f0314040742c0201e40690001c200c00000021618002441c0070043c107410060109401d801c408141070000005e07081c807004020303030a240001c00f1980f200350741c3d60300c40c010348200142411840d807002c000c1c007000042c0f50082c0400f5102a0400340c1c249041181032007034103004403101c60204030140b40e2504504105201c007008107078000702c200c21503a1700c404520403495980c04418000660403042504558920b1540301800c620090141086500e15100c2d60302a0001400c0940c0c0700b5170303503848040181c0d114415080d1001342000548900e6107042030190864100900c020407c014041600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 625534712 1250 625533462 625533473
    0x40312030f1419090206030702070603110406080402010f0c0c1419030302060a020f0403151d06010f0303260a0b120610030204020c070801090305091f08271005040b070507 75
    0x36501030300f031242d41264103003407000360b201410002001940121000050180359540480c3c01d2060f00e480b40c07020300031000c00c20380040340d900c034620400000072403070170110b00190b00c00c60200602c50b01714a4207130307e900c00c0780d290040c07140c82550140320194280024040c0c14200510f2280800d0b02c0600c07050100307407441d280652030f01002010780110039400a04100c10010341c0003030701e01a50700858120113507000d6109030802480314808103030b41c40d10403203103803181ca40e00000c0f0503040c0c0e025081c0240000345183e50aa980d142d003c841003840d0382c0383c0582034224080d88403c481c46200d140001161040d06002031081140e04600d03004141d420207420000e041545900082c1141e60640e80160b41d0307481c440c3e0f5142000200d0f0404000d9500701009002456400030280400685c112184454400380710b400c510702000340b040700400b14080300c000072010950400300c2e0b0404038400c1c0c0084030385001451440d080000c0d0b038010155165848082c00284403002101941c07180c51410308624049660710364 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 625535962 1250 625534712 625534751
    0x20f0615120d0f050310030b09060403140a05070b0703020c010c0c02131103040f08130b0d060608040203060f15031501150c0c120c0f081b0312180a0506040312030f 72
    0x1500244131002001c9082c0c0c1c0500c0d44118002c541124207044c1904154414a407a6001503030143c3c00507400103000100c049414003203d100c011030780c413020b107408015038803400082c200626030300501d9420f0001c071203030a0003070242c900145e040d80c1d06c41040f8a8180f04200801c0a20a010368480d841c22113440441404201141e4010782c000c2408410b0a400d880c000c034051003107a02c00070344001c8016001880c032800030068150798054100c2401003d44900c011a907520003200c000e541075001d400410403441b10403504d10342010030b0104000c120001c10f03012a00c0c1504040c429640c010913200100207009030425407410300c0d416071400308444040760302c80c2c15014a980c00350003110900e4440d05020050039464101c001c0c045035500410140d52001d82c66110106503c5c01c00500001a00d0143d56207008200464107002020b023031428070b04000646250050608140c640000038024040346a0f640e800190009510521180c240c101c074114005007629103d80184c0002401c0400c80055900600385 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 625537212 1250 625535962 625535987
    0xa020901020607082e240f02011b050705120a050d050105090103050a032d030b10022a04020904480f0c140102030901060b03010312030903020f0615120d 67
    0x464542c5045003001805c0f02e81290380c040c05103001300404400ea50703002160718031030170209625480c124003220f038026820b03914400448074104008007800b40c803a40c01900138001c200c0c0a81300b107450341c034501c00a01c2e500754460300e0001c011031340c08215145801120300802e405000306588a03a11035240da82c0303441d600c6903603590080c2808142ca0502121040140303405200b0b80000c3c1d01c8542c82c0d10385000c098010a810548540240a0a406003d90304e00008800b481c9101d0f001401b52182107030080703c102010401a4035600c15005c00850003d0795917809a0500400c103a142c14440f1020b5070901d01414007280c5400c1010300c1d40e040314927254142c0400629407181c881c00c2001c0c480b00325403c102c03070100310000d004005040d035220402420505601842c8550450700007000043e865046019040c00240303c021700082840060038840c81c480d030001d000d528031038012600301e03640c1400c8080c10704c501203c1110040180c03501011907450a2114441030100100203000c0308509610010610401c0350b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 625538462 1250 625537212 625537261
    0xe0619051c0206070609120f1e140c0109150e0604080f03150d05010c0f031e18021309050709020304120804030509030f0606090901140a0908120a02090102060708 71
    0x4495070259103800045950440d8844810421504140b0704403121b600c583c504840021912301c0c0310104c06000e0b10ba039824184006226100740c03c3d0203c001c1702d0691400600c2c0b56541c1060006403460a0240100c12001d40301d0320041001405ea20100d404585015200a03450392094003444089494002102c644002d109001d030b03030300c0d07071034401880310050038014032074004002a200c02c1c140101980b15a0075030025940380803541270380d02d0b011003d07203042a03420000c0c0329413800701d070311081126445000048030b100c05c0c04202c03a8841c2c000600b10034580c841c03071866503124885502000024040d840181200c9a011421810b00b41c64000250198440b001d05000c3c181c00814203160052080d03500c01640102151100d0803403480c210303110350082e52050b0186800d44040703a50b500041c02131803182c4840c0501d040141d078811000c00c0207004803450544181c40100040c03810125032010851103030641000144e03951140c00002840d04d04000e0500302009580307024040325000548c1d81c0c0342c0c0841c402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 625539568 1106 625538462 625538509
    0xb04050108070e04050c04020c1b180a0b0102010e1903090807060f05160510091a01050303030a091a011403190c150e09010e061905 58
    0x203000c0e01c811070700140c1c2c0500002c1400c860180d842805941150000d0040e003002c40c040764408071000070390780c200022086500004c2c0e110441060303001d03110080600c014080d421f04640e00588000c0089494400755503040c1e100b500302504000c2082c080c0c54590880f02c84400f04041d40341000c80101d09404000514040f0214041080303a0442d150390a03550000e2108854a44c0320040b4084016884104040840c0c41088400e50085150740009050341103030030301d00c00c40f080303079009490341e9410440140401e44011007034070380000510b000030490303003c3da103040561000e8440030a01200b041d40b000043c240701e0101034980062003901600c0c00394400322410042c60314448406021718000e04410807408103d028920013019451802460310012080003a10024080e481030740d40100100034480c0b1490001e652038007444480c5100641e1510706000300c3c0344024440c02035072511145 = true := by decide +kernel

theorem cover : BRFrame.Cov 625359712 625539568 := by
  have h0 := BRFrame.cov_init 625359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 625359712 ≤ n) (h2 : n < 625539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
