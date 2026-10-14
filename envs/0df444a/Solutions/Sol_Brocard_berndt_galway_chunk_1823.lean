-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1823
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:48:18.091977+00:00
-- url     : https://prove2.me/submissions/b5727d47-1630-47d6-b228-9eab72f2ba5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 327697841 ≤ n < 327877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 327699091 1250 327697841 327697847
    0x1707030b10031b020c240409143c0c1903050108072103030506060c010c0903031101020a0e0f0a1208040906050603040c05040203040320060a050a020f0403140a30 71
    0x3c0d030800c242d031001c402400f46c14109401456800403440710101e0a09064a42401c541507460b000c600c5c0070038415100420103c85030070701c8030394000e680040c0951100182c0348200500101c04124400c024a00840850107502c4d00604131102455071080c1d2103614800ca81000740a400c00b0320614469100b001c101291001c50783c080c0c4142c45c42c070800d00c04406580c582d000d4005d0900108800e030322002c11701c2503410420082c0601c5400304a82e07076600071442d007580b80c003038104900e1407a8a0403036031043c001d640c802c40d005006201040000c50729040200c01c0c0000003402c3c1082030b0000d0300302d4582c828441d0100003603000a001520032411052000603160410700445010481d400750a0300c8112404102038240380e401550001d009292003211800079150750064548002e501e009290b20000400800c20403070710400c1e4000e80080d1041d440c00100500008044c040c07404082c10000300705440036210001080b0b00d1315515440321120341d940000c844a13902c04c00c56080c1050103186c1c040c9000c00803c5c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 327700341 1250 327699091 327699103
    0x606080c12031b190c0305120901020307030c0213090c0e0c070305040312030b061204050f010218221d010605010e0607060504020d080c031b06071707030b10031b02 72
    0xd0302070003582882503492030010540950b51880030180500505000c1c400050700304218001c0c0510a00c800852035850040e1801491150f5601581345c1400684a00da81c04003c0f00d044541500e003038440b9015500002c1c1880800c601c500c0c64462a188c603a0040055420b000b0b01282c20741031081c100e668594030949518400c49000030005802080280300144400c208140c04032064540043c7c0c44800c01d0201c0c4c801d60100014100e595801d00400c810407808000c44510346808000950524035103505100303042c00c1c2d180106101c0c042e800750150310140c0c06040c40c400588080380903c111401c0f0b4042007038500f405601e42049500b0f0110100e1294010a04403020440240410307242218588500e030081c040548200d0f4003116550042c40800e11200c042c2070440c01600103141d5402d510701820002001c02c10740714009030808400c000c080380d00004200d0580f005156608600c1e038481030110020003502c002a0751007403030b40d076511210580c1680b00115030740380540c25508890121800781d030f90f10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 327701591 1250 327700341 327700369
    0x4063f0b0a0e1029070308190207080c061305060105100323061807050d0c03020d05040501050126060406050603070f030c0911130b0c070509010b031f03110405060109120606080c 78
    0x121308200320f50019210b0744a2580c010308184149120000641c11403040e680724503000c0c0e92803480400d8901a02800b80504c2e508421207a64500000b50340395503868560070140f0815104c0e00c03070140644d141d280681c02001c02807100b410111500d243d441036408040300203413041c50081703413404a0780c1a2403110b072451502a035030350388810303040074502d0032490007a000885008082640911421441588602925010301d20400001c5000d6041902c0e000403181000412160204640b0603a112000c01003035090704250449008152a40c407140031a1600c500359021040140032442c000003484244a0340e8825580e03486400d010111410503c3c00c9980070305041010881405103082005407104001424249500804d1302d078080e903500002010040240d107c907040340400000c0005003180d041c600080140a055410180740c00c47d00d0b0740d01540080b44119008039600d1011800d1617000746600c4000f84080e241110103400d892925001030621441150818403c444940c2081e24040c0b100403801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 327702841 1250 327701591 327701669
    0x9030705120a0b162c06031006080601180b03040218040602030403180602150406061a031501082404020d0603050a020910060c15060b04063f0b0a0e10 66
    0x108000c6245d1350081c0c1c0e0040d6101502c0c001036103115a0359116000503520903080f41c6d82580c2d095191007400f03460039000071301c145d0400000d02008000100c00c0c44d038090688a41e11082d9440c9d80c1c480c4049a801c8602641040e20001403400700020400c5c65001940319600c265078000504044015203030300050f95000d024090780010010070070071040364108540c028000c5d003000c580301380e680006130340d0b42100b10040b44581c0c1c0000100182883c40005e02c0001d00401c0c0b0f0980d081789400e500e1625401581d04800d50703400c0c50f95107164020f5403260141c0711a446106000c0100c65500c0c40d01554030640031008a00809101d4005071140c269401c2c1c8201301c8400c0d4a03030031418042039644442100301440f822812566a07440800c896201034043c1020303080c5922005452824070704032181e200c1c5145501344042903120440030002c4070414038104150f040c2540443c60a4540c0000340a1210540020204e12804800c2006680d50742950300105e6900241c541c2642c0c0030b124410b403141d09001960215 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 327704091 1250 327702841 327702857
    0x30703090f050a120f150b0a0e01030305090607060b150d0e0a0b061003020408061e0f0903070f080d05100906080609061f030b070203070c0b180609030705120a0b16 72
    0x80c80071141d070b40020292151702a00916200c50340c131030540d243d4890101c1c010b10b580e035001e1440741c1050903090003e00003640710200780d0b6146580060091045400082c024000420014108001c1e9000b0341c0c1d04460003040c2c031446c41028a510f06e511341041001600450509103003450903040031a01e04623394115844803803969610040c802c00c170380755140048c10950708001c001407208081c0800c034041c451521865000031480000b203c9441000340650094100e1407081c00710503d400001c40e1481540400c440d4845a02410248032900520005048250801c170400c000282c00b11440300a5424440c81041816110000340c0e42c2c4880403a0118020351102022500104010040040110000d50880102c3da1030b5510380c058860182c608074090780c000318180b01001002c801a001408101030140d00700f8244950001c0c2100c854010302c1d000c1c1e035001601c03070f0035900d0510100f0040c0c80e000d0440240c03c001d001039595203170905030043c1c46420001c07011500c10901d8041e010312000c443ea940c040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 327705341 1250 327704091 327704099
    0x703020615010905120708060f0702060615071202070503010f0207150209060403080f0a0806040c050a11010b0406120b0708010605180102011b020c1503010609140d0c0305030703090f050a 82
    0xd9826014044506012010744005030700c0e505c40900e03050604a040242c4121490f00c492146803600140c000c1003451100c2c1d0411a4481d800554150b00a1003280c4106505010403c071a000f4032031424083c2101d038198510211154000607100100c81d0243c000f0030244910207491400c034003a03c3d200074040d070300c101c062401c400d00b01d402801500c0c80003003140385000e81e44d03502c1403116442071480f4680b0003030206900f045203801440c0702d60f2016003920b05001540300200b00408501c65244e6190034409049458241c804095000110900014004201c0c480d00c038510003940c031704594001c0300d0303140c2103c00041501c1d00c074440b024102c1d05d1503100c60b03050000c1a603e80070005150107020f41190b5940c001d545424200300e85404120319142c0180081e050b00e1030600c0200e0304182074130200b80750100010040c1a40c401e5410085a40e8040500713a01e0000c000000c007041c50004000d8080c0005000200c14407001100501c0c03414844e40310031881954840c1400360000d03152042e03135841080800104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 327706591 1250 327705341 327705361
    0x9070b041a0408030423100c0803100806130507150813141501050f040c120c0e0a030b010608010806010f0e06031501090b180609040f0302030c0a080a030f0207030206 73
    0x1c401c00c118808900c0c2400e40700c00c1aa071079500f1503400b020280405c01407100d011801c1a100b0114281305a401c106500d040b03550140403140103220040c90b1a030300100240448030b001c160580545494401d690b8241401020b040840b05c60b5402900d040c025150001b440b1441d0442060108242d611126030b10b40d1010f00000c032020f1840c406076044c80e58024072301c4007000c05000c02041803252103100d000c0c550420f8140b01000c81d40c2d9a00e03030701035071030090464900c54103c0c0f114002115850008204d004074410112a4610120034144d040245070300c0220070070400b21000c1e4181d820707560310b60400340ea07540b2a4540d81c00b001e02c5112088000120305001150b400714030306a00a80190450b10340081c0048400400c29090b44060804c960780e80c0c0b106117919014004031036420040c89250101e041c4440054030340709001d4402040010f400d03c0c40000c041c020300c151a401d014503000e840c40c03070346a41045445d41d0310103110b0030002480e00c120744410400e80d1081e00e07060b5805034028480c0f13a43d030308060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 327707841 1250 327706591 327706619
    0x705041d0607050a090e1303030c050702030c060f0c070905180d050307080a0b06070c180c14090301090212150f01080a031103040f06020708010f2703030209060c06040b09070b04 78
    0x400108081c80c0320200f811b40c03e0b0204a80540b400c0e440c0c40307006a2060a0042c00c840f002c00003003041020401010025a80004503051110402c4402c00e03954440c54001c0031252242d16400310341c1c0d0290b035400040090b8036601480c8202c0401c41c007040d41080407014262582c10110827800450002d03c0841c00d054441c500455102c5003820002420b0146040001c0d5250898001190141401001800700c4040e43d51807500e08810000280301003110010051301062951000104480c008100d0f004640e800b50461014941c028092141d03081e250720045443d6260382001c8808041d03a0b5000c034030904a08044181203c075490301400340c03041e1566089420082201c08111288020310022a8880030900f00400416158005000c500e280c110b41c4c0e0f007941d9424807100d003403c0c03400c409214207006044072030704401065180440300030310b103250070b500070b01030229800c1d0403050101d00c0141043d00002d002d40580e0082c03d01c410f49503100d801342c51ba42c0c440c030b0084a402400c20300040120200301044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 327709091 1250 327707841 327707857
    0x90c0803030c0706090c0f080f01150b040302010c0c09050112060c05070305030c030619060f0e03010b0105040302090712020409020702030f1218030a060e1c03020403030c0b070e03010e0705041d060705 88
    0x1504255a038951401541c542900008c500da04202d80c0843c0d449002d1160340300904d0001440711080d4030704240c0d511580140d2001070b06100b540c0b0410b104200c09403000b480509112502001390b035840e0000c221034510381d506d04607969481d00c448210040c1c0200242c840c800c0d815903a4900e5a40d481149014a4001030310107074000920502c0340401344d000fa80541c015180b60780d1048800039075140014520340005607454003030f91501c201c0b40c000c0e0764000112070a4a4060700c1114082c1c035401c604075000080d440f68251068408a8003180d82e40d42a0020460716000700d045400710802140c4554a5900700c14400700020740401445000071403ca000f6500100000d00350340041d9016107c200680d000315020741c40c41c1d00032041b0001e49100c4140810403114240c80c0860601f41903640c003a00c1a581104040c00c82c0d4940c10020320120f210314640c01c12604090001d10906010143c11550303401c903401890300c504c2c01d001d01001c0d000c550b81801d108c18050076000703000030b8403465010b644c254800c0e80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 327710341 1250 327709091 327709103
    0xc010c090f060302120601200f0f011d0d050309070f06090e01060512041205090d060f060b0705060f06041b03090506010504090519050c0907020c0a1205101d01090501090c0803030c070609 82
    0x107200d003808c41c01032041280c00e0510074041d2000340d5074208a242100c074075907425001c041c61018924031922000940e81c00701091803d00b660b0301d441d040b0398149420140d45c050b250045100f0b80120300c49521100404c21100b0b881101c030398598880b1001d84041c0994000745003440c1040c0005008208014042c020340c42c02410410301d4807211601084c0c41c180340030401d0764040c0d158041409418190310a810080542c0107100e0f09050550380c803d6114003019111254249090b004609035645a074051201a46c82c1680d1040007090810041c0c003401d2000c4094546026500c00040d0074102409802c0b1500d0b0720002500c00d50200503800314040c0d807181d1b010f50312442074203071210050b203507103000038001c0146800904804054100300301e80c40c45942c00840d5000b0303019036140000340c0d0004051006404800012450300c44030107010f0041c2030941e660030110744c2030020180a1140c10740c0110480d90088440c40344468940c0e400300d68a100554a0850070341041029901042256000380c541e20f01c200c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 327711591 1250 327710341 327710387
    0x60c03150f04020f0d0e1b0102030307050c07050a08010c08091603020616020604030b1911040e3301020f01020705060708071206090f0b01090302011d060c010c090f060302120601 78
    0x12101c8441c0390080036881040d95503401b4040c0c440c1a00b0081d00040c0303000c0780b408801c40c0440c00c00013501da00000c1e040720f05110001c1000070800307405001d15005003001170030b10030750709540380b00c0c1c2c0303029081c0340701d0540205078180c0120b101036202084049100c00b03102000800030b032640d800c1c00a66808141d0941e01003a064060350014be44031b00040c0019405000c41140c00c2c01c00302001d02d10003400b0704410300c0c0c0358540030070082400e10420a135005c0304c4c080c00f80d40400e0750b625440d00041400d561141c0c00e4981c2005800e070501c0035240c014401c5828280e084506d8081c0202c4001d080388104e0101404c507a00c1400018010703880364181603489800303803401000084e01c0c101c0306400d480b1a0340100c00c0042e1250145000000305210314048880b0034684155044e1035900045c1910710b48844620031143c0c00c2c400354880d620b07924102e4454445400080100c2c0038192001802851140180344540850180008206109000b96038142012809031020b940f00e002c0159030341c4046891103071a030844c0c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 327712841 1250 327711591 327711607
    0x1050d14090d11070e0a0b120d0315210b06010c140102041401050327010213030606030311030f180d0605040b0103150c0905040504050c03070f0503060c03150f0402 72
    0x3040c0032402071400d40c00030852296049000303450195507008401d0303507511100003000600380c00c0d10500e030006102040010250300c1480452a802224440890507102d91114030b61031690542c4210360740380f401c40310000203a4a42482da051600c0c80c0090710444070603e80c103403000c99030000d44190004014100314006140c10b44d0342c0008010104802c090380d0358089000c20031101441900403010f842460305615515200100d00c0040d00200016200c0311443c0f10346440300d1009504a800186401c001c02940c02c0e6285072900161a0b94001100020b80c00c42004980388800020380c0c2c019141418442c0c107104c44115001c400311440240d16a10110300003a48020030818410680958003a074008c3d40150305509120035030310f44443c9240b0080b4504020700c0c241d19480a80b2074143c03001103902041c2078450f420842d140000741401d40c2e905000e52500003500540d540704110840d482a01941c0c2c146e0f0380e100c40002c0030300040364007500002e46080030a0880c41c10800c91508803074001d200500381a01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 327714091 1250 327712841 327712871
    0x2240d0209040e0712030905040c051e0412110406054204030813050303092b0506100602060906220311100c0201060e060a0e0c0c0d080f100e010501050d 67
    0x40342e00c100300551030f04144c5c50905a0264610010b030209440c148880b03032410300020454429010100317142a20705d0a03031049144281c08a40c014103110003900412601d604156881c4d000d01500315110303e1a01d9030000349030a01034950301c01e440c291803006040f0010040c3d2010046110304003c20381102c01c400100c03203510400050b1000d140900b00690329803100100c0501075102e10740050344a40e00130f03c4003055a03510400c030283c2d1311540400c41300400744410108010a4000500140389015032400c102044503007120042c22160590300b203d00d66150340000645503502a20443c0000c8150b91035070440743c8007001b665003024442d20b440a00034a860541505050780289400d038581c0c0c1b07075103c4629040d4240030740300c083c0190000107140c6090903400200d14107000c0c400c043e00d103141100055482148103090343c0b062031040085d5100e101015070300411a2000701c40c00443d811f41b060201b80d8100c0d5090589064540440c110012070742854010f4a854204c407480031702490b11501c86d0700803014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 327715341 1250 327714091 327714103
    0x30a02040506070c08010c11030a0f02010b03070816090b030304060e0f0a0e15033403080406030903091422090615060908030a0804030e0406050402070c0302240d0209040e 75
    0x30050382d541390701c541802045030035100008840803c01c003807400b10a4801001000f2140c02001d0307030803c044000d00101090713000d407130310002007580350103103120001d04650302160315104000d201c0502c030703503468443c0e50301c9003250442c200c01609a40140001e00c040c60003110411030040c40106907100c4155003800148540c0c00e950403840c0c684402409120001000d41040c10048004070081c1019410b42c500d881c4010b00841034009040c020200e02003110340030b07040803601464200714019503031910341c0000b41c0540307002a0101c00107000301400041c40f004e44000300003d464001c4c0005400410010780b0620040d243d620041e41035926000000051010700c10107041e80001802e440c0c6003490118050584165644460030307503041006000c070b8070703a407140c4605d500a80c141007600041250318086002004030390405600644000380160030b101c1c1d84203071071040380d00c200e4000001020101061440c12840c1c0310350840b14105001c60704021415801402004a0241c000565120038601d030700e103405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 327716591 1250 327715341 327715343
    0xb12040303021623031c1a0a060806030c0a0518101203031e09120c0807121d0f0a09020705030708070b100909080a050c1005070230070206030a0204050607 68
    0x24000401c03100c4000013010b4851088048402075410510428540c030455000300c1a8072a046a031101440390a00a1804082c2c00240252007112600d80750600581500c00642e0100c1c03080c8518200502d540c40d025955400f41c03000501414440303041e41580c00c04000b00940b8004051041c41008221038440e07401c4c8a1201f030090b80e0228110070011700008085611400e41c0429904040f031110125004525040140a4a01e40454004003c0c1090440c50240060042c07485042c695202078580c0d101c42c4450341e080300e40ea00c140d00a40704004000824125420242d00300b40086002c200810569015201a50040c0c0a89140c0031490341d070341c034042d8005030045541c00400070a0041070640003102c44007800107800d041103040313501e0322408101e000381543ca50400c071000400301d0940c0c0b018000c0da07420321007410052013142085a0082d4480702c0c120409111404604400c980c0c1c0c62000075407450201113604102e180c0312442d02030004a81c0000c01358060350b6001c0000107455110000140300079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 327717841 1250 327716591 327716603
    0x9010e0319030b0a03050c0d03050c010f140f1006030b030f030706090c0806190c170c0d0e12030a090f150b0a0e07020607050a210f0e03040b120403030216 68
    0xd801c03038101800300c40f0300000c020b0294680d4402800055400191030b044458121402641650581703000c4416204080c4190403079402d141c0c940061851581020301d044240c2c01403d409036036005c40f00c4200e00030480c0e1003004810102010808640a42d001411866020700bc2d141c0c0c000c508200c0380d117150703c00b0100300c031200e5880701c000d03003441059941d000140c01424080c0130f144c20b00955045c49400d20898200c2020350350307074920604500650414140364040d442164031450195180401074101120400e0a9803c2a1050b84800e0340481c040c860320740c01040141c02d42d00c441100c40700a100c002c1e8102c07840d6040c40c118a010405e000ca1040b40c0305451030300411640002024800320200580c46100805140020311241e41d4010482641c071800515206407290880c0c0300484003e114004400781d2003081c80ca960701210362503042030a40303210104090222100744180c00f90b8030b200e00d100d0300c44408814050b19969109110509800ca40607180141c1803c4009030450010f001c041c00889072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 327719091 1250 327717841 327717877
    0x1c06031a160e0f061b0f0601060c0c05010302250f0506060a051f14040b0a03140f15040605040e1b0a05030304180b060a0309020109150e090a0204031410050907060c060509010e03 78
    0x285882003241f507014001502e0078441091682d07681c400040320038010315040c07540100c4d9000682030b0003c0310800b4119861711070b10000c40241000411215005001d682d14004d42000840751f090001a6404440c00540740e01d003e8038068a0065141c058101040104401c1452640c00030130036030042c0c805460131841c120380c1c4064414000e030840e1459072000030040b618508108550302840c075115070050142103098080c0d10100e0010f4001e08031078100070f9101c0d01d02040d0008070390300000c1c66a000d04443c1d820450b07008000b420040000400d2181070382c1351340200402d0023060342003015007a40961200c40400c0000c200d00004030160403103440b00000075a500840b005540e80461080010f01c50071002c11a094041d5100034070350701d03290282c10300a01d0010027143d000d078240c1e0704441c011600710b4a0a95070a0301112003940b502c201c035054002460501011601440f00400c0007000c8503120784a0181210559507418060f1000070f201d0100340d580c17002181407040e020b000a207500040c50700f00341c00c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 327720341 1250 327719091 327719113
    0x70b01061e14090603042a0f05030601030b0714070c03030c0b250311041d0609010906083307050316021c051c06031a160e0f061b 57
    0x8050104900305001c001c40000b000b06a501448101d81e0340d04000c1d1420342c0d40750340718140b001d4094440712944030840b40c0e0750450002e060400441c4000d030303460315450800ca6507595040507583c060a000140095046401181c00c0c2c2d406600c030303030711030440c0c0c048401c1c10300c1c2994460a020b951154429404a40c4405044040298100b1a0b031303881140142440c9610b5402500140d10001400c070540c20300d651109141e260340703601c0301540d0042821507403040303030301d5490b00c0000c90107034094034494060070403240045200090350246005440c1d8240c02482c42d900c5000c0403400c0c01480040c0e00042c00550f1016440d41200c800305544143c1c1c4a484240d40c03414480d1640c400704460414540c21904007000d001004104656142004c4865160554440055011110303c9040d5000c204140d41d00d03000c0000100b103902c00024855584000d04c030303003043e61501d80054074010703a6141e03840040e24481c00e000346854110040b00c1d02060251680d420310f040410540c002e0f00c1c16540a100d66408286003d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 327721591 1250 327720341 327720377
    0x9100c17040e0f090102120424050a09031803050d0c020f0907200a030816170403030b01020706050403081e09150403060c020c0612360606091614070b0106 68
    0x3a13000001c2c0c5000b1443c1c0004600c0e00100300d800607100505484800300490300724281c10750131580d0030049000030803050602094003802001102c9040740450010080805540050b028940489030004098040c2108101c42121341d04007940c1300700e81c003080d21010070351251204200c891040714562116004401c818040202a400d43c52480c0b1035039022000c0240021b80c4408001e400100c5000049500c800c0e5240907520030700c5000420007041c641800700070903d94140c004050520b0280c0a403102681c44410441d4244201d01020f44820300c10000c0e50440960794036141c0004480d4072915082180d1540000c50726540304c4007080045401142c1481404490700c501c3c1007440544c0010724541c00071a0104805018440031810700f40700103030011784510040414000000741c0200401004d41c544005140d0002d0b4180303801036030b8880d49000402604005078180d0040616100340c500103030318004122100e0005225110100b6000c1c85408005245440514041d0549844464224003194452 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 327722841 1250 327721591 327721621
    0x100509100b0f0307060e18040b070807090515070201030603020301020313061d0a12031103040b010602010f0b15160602030c030618041109060d0c1e060509100c17040e 73
    0x1451007402d01e28010b484566000800104554203030400b03070840c000903c005006e00e070705034420b170b6038025283c1c040004002110001074452889030700c1310b946513110a0320490b03400d0158081c031a0082e013400c0f04408200142000307094400d105140209a554890f400300f07003607800603920000c09030074140d010820004180075440d5105803c4800c41440c5c2d840403456540e80c005a10080c0c401c604000342060001d2090300554960114100c4a598034240745c64607941b040ca003442904d006500e412400c0005c0c0109000310510103400400d044021ba0561141410750350201034840c9441e460206442d00045076800903610601500e20a00c5d128507241051084c142440031080c803403080f036482048000b03a9000c25011041205a44480f003650742c1c0c00c042103a40e03011010140c541101c0754000607842d424500d41c00c0303c01d021210321090381030b95820169068098507a40b0b50780810a00e1403211142e01c2505201c4c0201d0141050400c14645501c802c1003540c456000354540320b40788410403880c90182041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 327724091 1250 327722841 327722861
    0x114040822090c02150907121b0e160c0c06050a051e040303080903120103060504060f020c0f010b0a05010518010302040b0403050102040e01060504030506060d020619091a1306030b0310050910 84
    0x300c07485c2d91400c80d91454450b0600c1c01061414a0190010740510000c504132000401c404176030540302c20f4554004102c820012902a0300503e4100d080719140b03403003801c4442c92154000035580700641812025640d6400c6440b0b070408008003800500500c454681c510200f036001c801000d035542c5d0843c200140160001072011009078410010a0044e401302002c00d41101d800c801e000420707455034904500a0180555410000d0380041801c8004200118002d550041c42000802055803010280400104140324403030108500344107141088030311007510086454149401403401c0d444101226950b00190030a480c42e82d8042804d1000440b4503031282e0141074a801c1a500702891a0355150356a00c00818203800b031805400d03643c046403641000d441c400c1d540088081650707180e20b02c00614024062144a6400c05018109859500e04200b00e54641c450718092158003810100103070f0261400401d8980c262040464914445003c0d1042c14000e00c810405070603202249450f000990340c0c1081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 327725341 1250 327724091 327724123
    0x103020a0b0a080c0f090d1103010c030506061c060b040b03010f08060402220603080d0f0b040e06160207180b01030515131112070905120114040822090c02 68
    0xb030094141c002580e981d001100344002c0d582da5501c410800700c2ca005141c1c0c0290006079420142c2c04111045903407025001d402c0d402046120f403070050490581c4c906442c0d8980010b020004118403c400384031000c0311b0300004401185190381c5a071502915031190380500e00e00c4c40088014042d022050040b4402031050741e0041c0000d0070590001030075800e000e1602e008645074801407200e0083d003600504000d5400c4010740c1e403601d081d9200d010141010b0f18802c0c1d0040e01e4003c0a03001031406100f00021126048020300303e9950381144240c600c014000201c0540c450074030002180455501c0d2003180101030350003c5044100c060003d001d03035401034200130000304000c0e03c1c000b881e01c80d4058102c40c40580800031417040c0f1a1200004144211840d00c0341d00803a4108110000b90022000811500705540310702400c44459072041c200e54004900c2a018130707141c404100441c49030000340c9201c01c441a004000c2030021894085250015840301035a652a55041a820794040c000723482d02d207078140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 327726591 1250 327725341 327725347
    0x80738090c091f08010204060e03032817100e060d0b1603150b03040b0709030f0f111801050a06090f0e04050a0c06050d05181c05210103020a0b 63
    0x65080d16aa91000074a015560110004181040382c50348801d18005030700307651204507260b621481c041d601c031f4012980494881000d01000303040c00030407038400085180d54103c9941d140410f4600d9401e91007080c504209030452041c41c2c0f4080c030607040b0b000d441c101c0b004404061500800c080500d00080006201c2c5030000c4164021500c41c69046030310100c95500d260308040b024600b0b60050a401505020f0a0490000401d161185000543c0654011001031807180d0fa1040100da6540702c500001304401c69500000c40000c200003020701d1039034402c1e403280303000346213403400b0443d43c00164040c1d84084414900401003414041d80602c081c001c9468100da0305070402c2c111401103c4240700c1d64009080c410006020704c5810b00c04a108260700581007402180d449000401230780102e4003850b1705034580000f2656841c140659100c1100c40b0381c014001e0806800c4034062654036078003034a42030200801c01801000e0035202c40407480e040d500307041a0b440d411401032150703016075500540a005020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 327727841 1250 327726591 327726601
    0x405010f05010c1412040f0e06061603110c130903030c020f0d0c020a0504020309030a0305071d060a0e042d021321051009050c010801031707080738 65
    0x2c40001c1d0700f4241c105070b48124031584086030901d0491490718084600001003004a0051400004101100e2000300280c049448540410450b44031302450208100001040500045e025821042615843d007060703e8140423480d001c1000d601c503c440f1401541d43c0ca502000406806100c1c2003044101840104401841018902d586403640d580240c2030260f40301105045586144100c4068030f0060410f6403241132481c05141c0d2504501280360202c1e04020010b4405881b4414580071141205281c1079401d6404062110540c00410041d04000b01c1650b03099403070301c4038050100c00d1200d01e00001802c401c4150b941c8614841086002c40305801000411080b0040c2a60b01046c0c90f500d1135141e01c50580b10b4802c4803204a080c07001411402010107030849103956034440e00500380035034161036100540400443e00310702d003400010270103060b003020305072030b01055009810441d128250140c0b50404680700c40318049005501c2c200000381010402e010b14103002508078103040354030781f606228100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 327729091 1250 327727841 327727847
    0x20c060405061602030d0302040303110c0108180109020a15020c01030902060904051e0901090c15081b0c012f0403051902040204050904030f020d1d0f010e0603070e0405010f0501 78
    0x9a4459a40310384000305040030441003101100d0a425130040031100301c90710510014029400510056012410043d8404280540801d2419642e00305030341d2481140c0e248411901281446440c1e103485650b1190300e100107071520784510024000074145e07050701d08807041c0003d19007540d141c201410541441c82407001038960009580d03041070708681c013103015901e80140c4490303c541d0450742c2d44d140d2001400c2c07214040040d88516043c5010706a00c0c807140340c07030703000107003c2d45620b00311b860010398544002601c0114103044d1f1900d171300c07103440c44500d468002200700c2d0a40f008e522019410494000f03a400980382c10400305885003000382070803810240356072909611075003c244800300480303000d54080c0c06c555580e411a005032031300800550031381c10309080c010003d10a4002101c0944200c81c807000009002d002d02c00c2c95014540078807107504440106005d009501805d0560505c50b448001507902d6171200051071080d0020307526540c001d804c03c070400044d203106034030107048074056070030911450364 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 327730341 1250 327729091 327729097
    0x1a03030a17090a020d080408010f1118060d092a0506040b0306010507120503070f08060d0809033406080402090a0203090a050d020f160b0306011d03010f0b03010507020c06 75
    0x1c03460005003190340358011141403800c07940c8001d5001c060994070808102000d809403003600c0d9010020004241c441c0c40140464010302c0101c291603c3c144035299001d9500d14001c0713040c5001500850604104d03001100640d1000b602c22034000310f0f10511034038090500c40b8044c120001c1584161341c65807805010a00600c00d5020b1070006180010018180740d0048007107072041580103040b0a10711140180c0241950000e0341c0480c0001d5214007001da1291043c5060f40c05046d00070001d840005040d61403036180d81c0000100b03a00b40c01134000e05140b0842c8022807114050040c51138160790034000f0240c030b61f914100e80288041c00001c0302400702607221050b0340399110024080c01031f626142c0051851800070b00003001015441030f114000170255020601000581e004800ca0310b031101c80c00003c0c80d510a081c0619507030403105000107005903204a01091455070b0781c001c544d110544c1c1c100840c1c252001d040180e8002d917100d00c019942420244503540c0e00442034809003000710030700000070303032544 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 327731591 1250 327730341 327730367
    0x120c01080c030424090210050d0b0a080d030906110a020d120e06010b0702060c0106030804090f05011514040806010e0717090a03030e0f15041118060103090f020d03031a03030a 77
    0x180708080f130001c40783c141d0391110360344a0b001000d04040f070313015880081ca03075400114502005030821084416506010510700141c0d40da201c09040c10300c100520440041019035001d540e910f84489941101802c480000c000c2c600940c0e001d030a41160001c0301405812080c1038a6107510b2901c0c0204038044800300b002d030305440101644a07950b01c040c0c00003c595000c1d0900da81c0031946098000410042450010300c201c0d0512803040c846042041c00110860301c091145901402580780150790281c81085034041c1e4031a40505141002c0d1200c10b040d1a11070241c020b65400301c15201030004041c1c1104e00302a08001d10041e0304100e1904040080d182c410508008040c19140d000b1005074038010311000e048042010101c80d6403003e0400c01400009050307401fa40c40c0c0340d0508842a403401e024000c00810020154840038a4640300c004500800003038a003a03a00c0729110030008016501c4029800c02c05009640100300700001d00f540440b01c0341c1d03a0b4540b612a500c00c10103616010b0300140841c0303501e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 327732841 1250 327731591 327731633
    0x2806020a0809210609060a06050102010606120207030507050a111306050f010c03050c0f06011d07050304030c0501020f030c0a090807050a030f06110309030a0801050114090907030b120c01080c0304 86
    0x3d024809403c400511455403a403240307000351800c001240f440014114407418490344207200e000c3d40c80005900300c82140c02004000b4035622a24048816950000c100c00c6110346030403072401e61141c56050500d21440022076090071100140000361400e03101500b1007003485501046864038080005544050b00307103c0340c6c14045000c034038800745802081660741603949901642c0b00c0440d404001522a00d0034080e03410165038041006240900e440301291041d020f5451703252039912a44c406480450780c0140458483d9020020241035040001c0918002c0c8468038215445110f00300000e0b0023404150084003443d071264408108558a40c100c107012039400031040d80480384c007400c056026000c1405950800c05001060010010000001f0316201c2507035a41c07075030266201e400466041d10701713103030792050100103024060151500703801698000600d801e00250503030058000c981d4030008000c008030150006041540c0c01d582200045900401c8120000d255141a50b24034801d21244900c542c0302d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 327734091 1250 327732841 327732859
    0x10e0a0f090503040609051c0507052b06050f0a090c230a0b03010609061103030117030c011d280821010308040311060a0c0308060f2806020a0809 64
    0x14402655015180302500038080c0c039691900d17040c2c00760025007944a024052480d201402120059002000444603400000740090518080c104a046000800c8075900502c40040c004522080152030300485485003402280c2031400c060100c148000041c0300007841c3d410280c219001800601b4214140e45100c0c50f203090b03103420a003d1401d000d541017002c40d04440d02040120b8807600b01070146040340c90982d00e074001151920343c215042800d0710300c030020035407085c0014400140b106442c01403401d032200031203042c0781040380001c0c01e40e08294034807500c00c1e02419003014459014004806100c541d0304a89020900381451112080054000074080c00c5021460b040c80d8402e0021804d00313044081c0c000c13511961681825460365000e80300c01c9989030728800a890160410a0030380e00d1281e680d4903030005043d4240c070251000080140b106610481c10161121165641d031143d0b01c0000c6160140941342446100040c102102d40d0450b605641c081c40792903001842c01800c841d02e454003540c0d0201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 327735341 1250 327734091 327734111
    0x1005150438120105010503060726060111030310140a0b0d02030901060312081905040809010c06020c0d0c0b1513090305090907050c1c140c120c030a090b03010e0a 71
    0x40c03030541c0191030740005100042c040e480e0054001c1d506840049007900c00030340300c3d400c0c1074407080912a02144c00c00e0850b029881c0c3e0040c5040000d0f442101814005201c490b11245142142d001300c0d015000840c01480c244071030f60200266100006055819040b800d050030a0041340b4000c0102c100d54080d000030000c0e507903403000c2d0058001182d00c02c81c0309018200b2400040c1000000f1540b442942400b00c403074110005450080320f00881d08101d1711841c6c000408011603000500c0303e0140c404c241c080001e450103031000c01c0078150981003960f0760706141b442441d0901c801ca90180400e0307920700401052a1031690703011620306144a0304e140000c3e611910303103015645400b035029003950000d2035030b0030030007402c1d089001002440609400e81d1100f0303006916101e0034441c1c027220103000451142c5400c0282480d90018100d0101e00d504440a9505051a120483e442b00e1604000c43d0008034422790050380086004001c0c00c40c00717451504540c101803910142e0311004100740d110584408a2007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 327736591 1250 327735341 327735431
    0x815060a050307080d121413050c0307080a15020c032d0a0905030c030601030503271020010209010203090127030803061809070302010f020f10051504 66
    0x4401001c014041c1c428440d13031900810745518070a800980030540280f8103111241d0303584200310030708200d03190040c0c2d55214060070f00d070f1803510250112803a1084ca8402e0390f55507420061103006060000003014102030901d0401001c517084d403581401d4900501c50074110103808400e544050a00e080076440840c11200124040500b004d0500d502030000214802242d0307003c1c002d002903820a0302101c3d40703560180d080c1a641d007824880079007a41c0080c4044910300300c444001c18448004074094445c100c0c608000030302c40e0707e600c484c10303404140400c0c09100705092514601400f244040021800c1c40d6208001135228400c3c058a40c3c10000c491660199185030300900e08800300b40d003210040420340f00d19000f426039205844091103001c0b20801c80311403000d51000948103807082030250845614560042d5411810008001c0035030107100030341410039038108180d243d8a00340d50404140c030700b03124050480c03840030480c0c0d042c000d030f040c0441c050a02c040d4075078484a10199503d004141030803c4860 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 327737841 1250 327736591 327736609
    0x5090f0613020d06050103060b092202040801020d140709030f080a0504080f10050a020403020112020c07050d050105072d0f110f010b030601090b03120a050f03010801090b060a081506 80
    0x40d8441480401c1c43c0d41e19200a130f002a0950340c081c0c030100142500d4510014082c0110954070783c0c0035075019580390041c40b070744031545602c0e03a07020809403d0035124886582a6044064059446c907601d030b001d6421118880d0781183c2164041c00c111110074115142c04415030901302001c0c0c00c0d4400010903520191042c01114010a0241c5c1034400100350300c9034031500d03841e050070920489828000854000d22403032080701c088039416102c445071645528145006500180075004490085800000b00c64a603880d0302d8052034420740000900b483c00940203041e0204001c000e4440c00c100500c0e031241a22644840b6481c0c8265040000301022048401c681c2c504920400000e81d0068009100300030320b054208485d032074821130946240c0c0e80c89586603001c0b204565880c44e8968440040c40d41d0100000d0002c104206642c60843c1c0f500258201c2110340703038000c2e803004002e070b9500c1c860a803c0c802d5403031070190480000c8581300c240a15000b0059501d8400c4507500401d071902c400421181d80c1c8004070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 327739091 1250 327737841 327737869
    0x18140903030c0715061d0c0405030c040b0604081504050f0118020d0638060903030a1d0d0c0303031a01050d1a090a24211509050c01030c0905090f06 65
    0x100307200035500c4048100413441b0171010220008458808141c00314103141c180c5050b150080d006084441e080b03020000501012852584c0140c01040301082c1d83c5001c1c45030260000c000c0e0090320160a0902d850703890712901101881903645440d100d00c642051656083d294590101c0d002c0c00324402c1802d184009000310040c2d05a04041007031000700030210103202c0c1000303120980d04580035201000601103c1d1141d240c0c425410380023044080d0346d881c0124800c561444520314102444030402000c81c8904510110685160b00c03040010001c141d45800781c480c4c1c0a014003c1078641d03103905070001c2c0042c0100040400c0840d02d4400164020441c2d011196201078020141031450414440c0d07035004250b10490100101c4406006030503108a00300c1c01000c4888400c81c05002c0e81a100305440b041011000442e0820280549642c66103410701486110a01920180c05004a25000541241d8803040510300740030740001d08202e00e0342da6102c402c1d400f0f80400800601c0c2d54a030000680802c640c3c0030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 327740341 1250 327739091 327739133
    0x103020c1c02010506030d0309050d1103040915050a150903141002030a0b10080f040b0a0b030a03121d060105090408190c02011b050303070e061318140903030c07 71
    0x90400007154150030460103008103800303039602200c078032404401755824014082d180e81d005007442d01039203100f04410fa55400458060702d06081d11900d021041c1c8203200600200d9010a030b03000d004070f203001c0c060f1500419107005c2034100300d156003c0180103480c062002504041c40d841040c5000d8006100c603038040e04403c2400c40d603d1400c0c80000c0d0040c84c20740e105d103001c0c1c1e1900c4c0490507406c3c0585030945c06482900e041003219a00c07540c562a41c01c90050030000100c0d01d60300301102c01e46080000340d07066440780d211645040c1140083c1400c9411115041014400100703440340e040801081c031b1815182c0540307007035000340c1d282d007400351b400d204003240c01e00451100f50f043c2c61a00d0b804007498a81c03c1c401d980e030085260f04144440c40000400c24090403c2c2c008001041b4118050740314551410005442503080c120f04c0345c403840070000d460380035203081c0500400c0741445589034800c0550003040742e5030303800d1309040072071030287d03a80001000030700d020303400103001d406114002d030000c51298800e00c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 327741591 1250 327740341 327740383
    0x4141905130608010b1c060b010e06030108010218060f0a030207020301151e0504022107090312051e190c0c050402030103060b09090109120e04090b09010203090d1b020103020c 77
    0x5112002041d0b103216825440d4a0110090030518111900701e81040d11910005da000a113511100001c1909852550601c0b040d030101120984400300594002c1c0341e03070400142c40b442040e810f5540017040d40c0704644032700c400300325a0038074020160a403201640945001600d8515600c0424010507440300151280e104190700001c0b0b280027440382e80803642000d109a00c0c0d5a07070358400d102c141e000e1001a80088541c48400c50800c0c45020303a040d40c800c21502c1c1403402c00d1f959413518aa100c80201004000850000b249422920503034080030300e802c3c1481555103416a10300b445031104035a40407440821031040b9042c1c0500030469040009480d008000f1903a0307507502c0ca41070000700305004900d8080c0d15900002268058103208102040d0f400c0b400100b045454550100e582d40f50607e0b81c50351060b91031406001081c6007a11f014032580c1d4a2000684d6030519058052400b1482c1070744c581000841040050405818180304103419070a003405030310f0b01400c03216542041070142442c040c100b098 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 327742841 1250 327741591 327741619
    0xa030e030c0a120516121205270a0807060c02030d2d02180f01110303090a1703070f0c0f2004050901020a050313050a1703011a04141905 60
    0x101d16850128490924440c0302e6140f50300a40d040e0080480802c0c0b00d20f010340d02180410460010300341c4000e49413402e0007a0100e0801c58004440b0151000c451000d205102d20b0b0004400403138110f64a00079400030041c1400e80d42e02d00300303a8424050010200c5458200e02c48101d80200240d44101020380307014000260b814442c401c850040742081c0d11800218803481c1c0c108a6144200c544188411a0480c034401498090050b420382e0001303464100512220645161390081c40a54012452030000e0102031125052501d0b01034004e00ba2241000e0003007080c004126001110f248806070242032003551007409080c190320005203094081d040b49001484002c400c20444c40e030f0311038000111800c20403030300d40c0e00d0018203d000315050ba0020810410105100c2c20303000b074001000c07621035030403101c1c2072109a8032103100d00c4295038200113458000c0014040344d140241d8a66520184c0413105041c5803802003002608202c0c0d03608140a440540040040d2400102014000e0700001d0320350b220070008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 327744091 1250 327742841 327742843
    0x110f0a020c01030515090415020f0d05010e090a0318180b15040f0e06040615021b0405041a0406110f070312060605031b0c0618010c090602120a030e030c 67
    0x1085544600501510821034480d40c0030b0301c1000e0040b02000601c0f2030007058202444140d40c0082d000380e43c03801c80c50410080e4441540024541c00c03900c1c5618903100d40e200c6500c0002d075407040e00081c004145100c10844803032800141205c03c10340502c1d05101b82c1c8206902c4071f134588401d030404554500c030751101c1320516196070444242c0741420f0b102c3c4524410710001580a40c09280035110b082d80303145400704040300c00c8403400d640000d0300400c0002c2d05542c62003840d00c0041007a4042001d80c21078118024112407088011088100c00e440c00d01043c9020754603080705035220981d00480d0480480420207002080d48089140340e854a5800e0b174814054026104c0d40d00065000c0303000840740c41c281c2c03c1c00a038900503d011501c1945526040d82c646581d65040790003003040c103049034074091001d11a422402c00080d405403940c0800c4541b20380720b01c1011400d45a100e1801c2c0184070824104019899000400e502180007982000d6106e0030855411030250998040c0355507207100101c0e00d141a124 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 327745341 1250 327744091 327744097
    0x504030804050c0a15270e01080601140a12080712080108161d0606070602130603050a0911060313051b011106070c080d02071506050a05030705030a0213110f 69
    0x2c041c10468104403240010005890840d01640300c220000360001108980281401c0c8807805040070320704035a50541c0c0071a90034684a5020706000e400410041008000a00000d405001d038a00096032118006000c1000c0f82c1ea648035410200329140c2030f10044c0035050302a20890750380283c000c004280f18000007051440280030718215070152211034600c2c050305002c0345040701d07100c2c19040001d10441c460f0104080e4014015030704100100122030014610b03100030200351900d086d49000a0381410700c024111440105003480d010310700b80c000b0000c1914000f031101907a40440d2650780d00e58034481d1480081010000040080c032801c044000c004d81e00c2e181a0a0318502030f80e038618821054610242d4a400a07500c403000f140310f0341804000300301d0580040c1302905181001518215035540d4441220f0070300082d1007401c5580703007410b0085203440d00103440108002c070010040030b030400c00041e45440d250f80b0001d00c03070cd018a01441038000f19810880d000800d45028603158407803034081030310a138 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 327746591 1250 327745341 327745343
    0xd0c0905090a0510050606070f201806101e080405010507030b0d0b040309150507060e06150603040c0305030a02030a031b0909020c1203070e03071a0f07080403060504030804 76
    0x150400340025961807000a2011000d5008001410548603044801e03004200162400b5003143e020000b640225242c50240800c0350b101d42840181210210503640200c035074612050700c40d50101540440c002c4050850342e801110446d058001194900410381c1d50303080c00088540f03480054034040d0121a0007a010340d2060b80204001c2c00150b4034003c0807800c49031810103035135004405000d420041485016140e9110b803080c180004016148c40c000150030300086000030010b5400542e9004105290185080045c042c0c1c005200b0360400e9000c010615010614550051101000143c14000342030440c40c0203540007001c0d04d030b84107080000207488c1d41c00b9600b004042400e08030180304920060802c480303841c8150307440c120130314180718181c00a0f40c464015a005445110b40100b440c3ea00d0a004500a80c00c070b440d1840010b215a01f41410018070798021042d209403000ca420720308000300c04031680280070890f000d80d02c440c0c034541501540210380000d091700c4c0c81c01081000301034200c3c909034052 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 327747841 1250 327746591 327746609
    0xa0c0b0403021507050d110a200f03011505010507020a090c2d02060f0a09060606020f120f0403020d0201090e0403030212090607021018020d0c1403060c0f0a030b0d0c 73
    0x3c411003006940580c81a6100203040b41e03c041d01c254242c0c5c3c851101840302a034500c090319a00842c0e030300c9490b030b500101c0d030302000311000485004002d4502280d0095451409a00034881108002088040700130a8410103050200001d071280841d51350980350006001115410403020000000051030703500218105100b50100700c550500303410340c001c1024140d5055500520240d0b581084400302c001c030140c540c50b03050741c55500b8440028140d000711009080c803a4020882c2c0181100003d140c050108000b070843d100800c9120590010042101d050320f030152034a0403000924401200c4505140d809908510321400034001016459001000d080d4000401135056444050000307407940d07410746120016031f020300005144803c80f904a03054205001c0c4450000a041e0340108200c2000b000e02252420341c264018048040c01c8503002122000650042c8031a10f05002c1e900350343d1094100b40d5403080e2020840015052080e008020b054030080e14034601d002d824030300404114170f41c2c0912811 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 327749091 1250 327747841 327747859
    0x6030105010602190809040e060403031b03020403030207170f03180109060905010e01080405010e07080a140601030206040902070606151115070e1207030210050c0c030d050301090e0a0c0b040302 85
    0x1010303c0000c072035801c50402c00359507a03240b002d43c1d602c004a900c81190b6a8000792220035142c5407813002d20a09110342d004c3c3d100171480d07209200090303000644c02081d07a0705140c070600007400865400141d40c01903030200c6910721b400d5681d41147d54500300d185d000c680d00314400051440c1ca070401126810701200000e0b00c0e00c822003501d0f01e80544048020303005150014001940620080d0f1180d0103040d000b50040e8000500c900c03000071124140540c0b500b10f00c0c9503512110050381000620310301002e1210180c1c011341071550656000031803a00c51886052a1150041501414890140d101e00c0041c00000342001915440a801820b02c07034401d0308076521402802103860b00c0e404640403561280c1c90301c0d5503006490420b0f20401250f60805001230403030748141c0c00d01000688a03140e60012075412916011703180c0e80c400500520f0714007500f5201e4020341151444950b03082c2c004d402e503030640343ca0650128419201c805800c0c60901060b0000c1d01c40d01030900d00041c101605401401528026501842 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 327750341 1250 327749091 327749099
    0x20f06131401080c09010513030212071d04080a082d01061d130903030f020d1d03040e0a0507020c190f090221040503070b010f0f140306040303240e0603010501 70
    0x92503060884050745604c03003c0101d8050b40d88140018024070048900b02c506103500c98000c03c1c1c1c0d0621521000d0b1081e4020b220078042480c0c1c502c010901d805400f4011515807030950f440c1c40282c019880ea120030b01c903c04002ca2190090207014814007004003032001d08507601d031202c2c0406114203205d0280895000c41000005a103030b00c0c800c0401c003902500880d000c0042d040e5400003420a520300303800b055660901e05005981381d000070034114424001c08900d408034161409180c56260200d20744030b510030441009000303030440445a108a103440c001031030f641c1d0f04100b40d0401854807030030741d44005011003020100c40f0030700252058450400c2c0707200c8096142e10f9607000700c2c891114542e040c46225050070b20300e40342038059258450b00c1003094a003032032016900d03605003000c281c01012a56004900038021b00241c04000c000030541036601d041d1070851007006c1780d101d0030042d0000d402c050b142d10401c503040354085540300e10662410354108030682d982c801c0c0c0552f030030150340041c46942000d00001d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 327751591 1250 327750341 327750347
    0x23a0b060d050703110d0606120c120317060d0803130c060201060e01050d0303060f0311041424030f0a03020106090c020c060a0f0c060c020a0303050708130609020f06131401 76
    0x40141e0707401802030803200c2c00d40c0ca6110381c0c40c00b8242800e61222200010000245071400f959008000c90202e182540b416031601d000c6000040e0000f4a9641c000d1074600702090703219990003810007001d484079125445150102e041503520400150484400100348000c1c00b0f85803c42c030603224010345501800c1030b1616422801d80d0590700c50781519805c5800188103900c0c0c0b040c0030300342c0d4600c00c0c28000342e030551b20380d40c0030040740060340b0548181c81c0c1c1c0000207440e4201801081c1a2901780c0c002284946043d1426131402007820380304045560540000d0600e079141000b02e44000f00701d89080302d82e03890592400901815160213060303030040c10b01c2344d415102800000e10000c9044000d01d10341c00c02460740b4040399044200b5002d01e04001c0c0348241c480c04503101d4451085900036660180c05501c0082c100070f400e60740301510718010410560b040015100c42c0900079101c15a01c4030010070358461900000b040252036101c2e00364410350018548214007000d070b11402c01c882081030351502c5010014015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 327752841 1250 327751591 327751609
    0x30f020301050d08090f030f150115050f0a0e13020c0f06040f02240a0c110a030507061b06020c01060e0c0316080c1908070e0a0f03023a0b06 62
    0xc0d9411078000d038006800030384c0c039201403d071242014010780480c01076000000c0c906011840340d491a5044017018461090760880528050105c500c4202007134004408020700794070401c1c1d0100c00f5440089128404184076400307d0560b488010304402071a0a802a420300941c414825000c0e94402c40341c00c260300381008203085100d6500301c01035a0000007075409015840082d056084c07940e1540b0042d10425940c4c0d80301411b0040610390718078028a081e0300c2c2800b036050324940741620400480070108002540082c0b1501a211645480c0c01604050b2054107051a54010700070a024000b0814105a0a05510074800c450001c000041c0d1038889072000c00c52840240c0b48c3c64000c460304050724180d03500550744541c100010685091500d40030092500c00010f4048107d030014180c501032002003640400318100c1090111200043d044c542000310400149901c070003070054100003042126031181203003000740f82c200c91207401c40f04620f00384504503078900654100d51421141007c41c086081441c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 327754091 1250 327752841 327752849
    0x150c020714090109020912010507050d0605031f020c030412050c0f0109060e040b010c05030d060f0b1215030c0310060e0c030f18010b04090b01050307060201090c0e0c0702060316030f020301 83
    0x40102e6900b4440c4401c040d5000d041c0c0a50452a04d921802d5843c00921442c3e2141225076038260322504041d507040141c44007070340181d01ca5803220790034400c11010350a00c1d0711044c008110050703903040e15861050641c01940d1000010064000b8014240000442c00c2c54046408031801d0100806400065440706228090400011800d610302e82c2903091980c4001c0c8815014100348500020b503070390b445e1941c0e10018499001c0c1e034481108209011402040b0070203040454044e0341003003d625622200d03803000801104003080b414818801c9500d09001044c0600c1018066800c102010800c0c1e030007030040c030f105402207840f0010000d2000000c0d442503d01841074080140b40350b40b603206c040d4120401c0700350003440c903541c1e40b034403e441a526032003907454051240d1024085076240c0810542400d2003503000305c0559050640e40780c0014001c144940c2610104211a00a6120801c18007540c3c000c045009420140010a0040d00d110b080c00040035880290350034001e0010140041080e4002845 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 327755341 1250 327754091 327754099
    0x709050f180a12110c0102011b1803120801150f1e0210020c0a050f0105040c050907050405060d0e1902010206070309080f030c2808070806030a150c020714 68
    0x101007102010000c0401d00084a440c04480d002d14840e00c601a0034000c808510001c10b50714001c203449010103224250450000f4002080840301c0c10050300409510921510300300010b0518100140b68200380350006140c02c070030280c00c05c42d0361798030282c0107900a00500100351111141c856543d0310820b4103080516081e9200140e425000281032845e010500c8010158090b11506582c82c00343d51000d040004041c0f401031030f40280034200341e810100c07a46000240c07079041104100108085a082004480d8141e60030902c3c2c1d611510202c03458001e80e004243e002074005a541e000d0341142d0000d01d00c010425040c0c808005901a03c0c0080e100698002405a0000d100080841f8029844030a40500403804d803494440700e0208603000754821103929003041c0f4041254040b041140500e1043c07a1030704141c0c656003110a88010b024600010130200810440c840010855103080c0710042010b980410000c805010f00f828000240000d80030030320040c800c4040010f0799082030313190f0400300c41c0054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 327756591 1250 327755341 327755371
    0x212340305070e130c0e0415120c17010504140c03070b0d0e070909030801060503090705130209060d0c081311061602030303040803010306050114062b061205070905 72
    0x620140d0241000512190074031041c1407281c402616040000048214001c0f400511813000348806490703111080c0560340242e103092150082d103012080c0c0c0009480c68800001c1100070702c0d24211807030242070340001c01040d81c803030f65205605105400550091388521100010075403070301c0b00b41f6a10070301d0301c00190f4140e200860401011034008000c0040701100c50002c01c00d01e00e070664441c60b10803168040621f0b16511040c0c982816404440107014056518055141d4104498019920f40d02030042034031a107840060303400900358030340c1200c000c810302030045501c41c03001000356802000c4040340040814201000a0522090005000c20a980c084410750680788a0000c4c042030783c118000c1c081616001d8a01d41e009070f03030108003a40c4110f21407581942d41e0340c11454400251003069000050603604528185501d64580c0103854810881071b840c0044080e250410703400b040c03080c45800304106c1c504000416070f550001302040c4414021000ca0b07100a5503000310b20304480c01143da8905056801c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 327757841 1250 327756591 327756691
    0x70804081e0631080c0f030403030c080f040306050f1005151b03040509040c180207020906061c110a082202061303060507120f090c05120a060212 64
    0x3c0e058600004049000d21403144000600000c1404101036080d40d11000209520707441640c100f10004208403140c01031401c191840c0d6003e080d00021a80c010680200891000e00352019481610019034002c030060049007000351802010700c4060301d0301406c0044600010819080c2224826502d203000c414091a100c0c20941d008102030714885804a1808100300c0052240e503200300485c0100c0c000d9001d40005841c1410f031100040c849054055224014000301001d640c4004980d0390001042c3c50160f40c0e080c8811010f54081c0c05500c016400500c0e1400caa0341000c0c414000c3c0060303100381d46440340300e6111020b440c110b201c040120700a014100f03d181c8801410302e24040c00d442c801600a10b05820b88a54550080e80c40072245400024a40c084081106c48a4060916805102a01080110035907141d0030026460f80c02a00e0150031943c81c80d00290801301709400d41560020001c54917400401781c0381c04400030544582000e0288800c5407a064201a50410041a40055440c0d042440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 327759091 1250 327757841 327757861
    0x603060e010e2a060d1505090906090d03020307021c030e1204050306010302060903150406051b12060405071214040c050a0f030b04030e100806100509060f0f0708070804081e06 77
    0x842441150840411701245400c04480e000c1d10b81b00600941410380507505020600208102c02004401658003080c1803102410010800604072209860090b82da41c1c1c071a807091f881c00007030040b4280780c0091300b40c186a88580c0340c1c0c00030128204800075990403003000320b01c4a40c507010314065198190040d1004000615102d0b00402031118080e0640d61413124200c59a0070144080b0380940c1d545407540b081240303031601007400071001d0107060045810808021764100e107294000707020704c0c0519035a101060107a80035000b0310085002d01c413030034000c110020b003d07900024010b07141140c900003040008146440c04002a5017542c407030303142c0461a107281d80c891564090700584250248800030078901c0880d2160222824241d016458040103400e26805106400c0a0054080c003000b04c18040380d002540d50508031800381724020304244e01c036031a18486d90011f11840300006d040d05000103404007080b80d010b0141c4201e43d140b00c199802c0c400050f14010750500320b900c4818040c0c21010000e00d100f54 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 327760341 1250 327759091 327759163
    0x90904020f0d080901140c0c040e0c0607050c040c0504050603070f050f031302120d020a02010c06060e01180605030304120f1403040602030706050112030206070507150603060e010e 79
    0x3000a029840c11400340020600b14144000c098898035000034407030045503001903000903403d2400508a2402c040c080c2c20b25220013191a24500c9240c0711854030109c120708220303c070041c0c1e000400392981c80b0542e107801542c0700340138050980114107141d02c25800c1401032013518100d50307001d011146907075582d403401c0300c031015101c441c01c082c40710602c8074191400c11032000d50710030650f018800d24a62024010828002d82d9600608003580c001952204501e50101d19034030342581c2824081a2100546403000240c101d94004c00500c42d0654000180c4040400900002001091080001548400c141a01c0340b21301e000c1c3d1800c2140d4414101c0005031030f00c00420f15140251400e2410013400300801c0c0c29035110b54000d10050303102161140034030610380310b91401480132410494141d4460390b4043e4682000410000034484080b408074148000501c0c180307841c03290701400b0050103440e0301d460002440342c0390034240e043d868101501c1b0201c03400621441c409175105651950049503503510b401c204 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 327761591 1250 327760341 327760343
    0x40515151b01060621290d0506090a0201170103030e100e3f0c0108180703050d120506010804021c1509021203040b0315220f0b03070308090904 63
    0xc9050301c1c1c0840000d001c0c441d5901500042d9103108580a481c205100c9403a0b02642c1760140300c3c502080c170310000040901d1790900c080713a1100201900148000030f8070443c031024015040d070281303400f00203603400c0c003182d010b616034402d0300c2c1c03000d02141118492208100900006010480c2200c00c5002ca10b03201c22081c04030680f13868aa03800d1181a40441d15034100700000d00e4260180d004040b50351600444603808201c000c028001c080180ea015040e074131201070988905201004d40403812114000111a20055000003260103150381c03464001d84d2000051045c4000808214090032050b0060103010b0040205a545083d1911142c00304015044415158000001810800030000d1000003481c10404040d010008400c030b11401809807044019018013001e400400c02802001c51f03010981e030308110541c44881c460505000814003040b80d940300d5030034403541000c440303094415940080e080b20000040a05c0140c504005045d50f44503140802001600244014892401e10302c0d941756100d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 327762841 1250 327761591 327761617
    0xb1b03131e05030a0306080c0d03090302040b0d12080f06010c0317060a08100509160503030a0302070c0e040f11011806030e030412120e03060f041101020c060a020c04051515 76
    0x120300700d5640c8a1843d4001051400882d803508070030407000030103001800b0440d20907103c003201c000599038000c109100c2400020301c00d65031030359080c80030b484c2d840c070b1411100d80c032108510203800f00c034a02604059007203544c4410444070718002100d5502c40c41944150617415160400d000314202d0002c41c02c20401041650480c0008800003080c0c03070100f00010440405d22800603141c2088680c903410b1500020702c801c0c072400002d07420012620000100c4100000074a401a200c511918105000140642c002541232036100203104c2403100c00c00518a14502c604143c08140202200540f816100481d640116a8003030b9820400c0902030340100e4001c600040c2924646a25101c842c185000f9610013641c0d09507840f07292000c0e85812400100901d40200e000b40924070700a0a62a502000100003c2150400b580d640d20b46900030032000818400c010100c40d114070381003000035950250f600615100c0c3c2d0600000c0b40e68106505030b00a0f80030720280c8a00c000b111030000d44241a40012903039105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 327764091 1250 327762841 327762893
    0x6011d0a0908040f541b0e03010903050316030b060a0f0e041406010f020316030e090c04080a060207110a09051012020310090507030c0b0d0b120a0b06030c0604030b1b0313 75
    0x3224038a2040100d49001e82d4091060040d03100b60003040501c0c8001d0b01f60103607140080940109801c0700a40390b02c81c40d1540c156040d03800c3d0506c03c9019181c00d05000350404004101809030542028010304e8040040c0c1c0d9400021030500d00300002d035541400744c02c44000c1031748085803080d403040c410050b80360090b0045900d0a070800a450704051586842900059103a500642d07030743c41c1500b071468200d030721b10507031074241802d0999440c2c988003041c0006240e42e90019140313082041d44100044081d00060411302200e03694a008000350204035008000401c01d2100800c170464145990360141b50054002d003902c0c0031410403c0020400f420059991344103102d00080052500c2c0c2c40c600c050010074520720303203803c450103c10f020707501420342d4940700d81003010b83c40840220000f42c00b0400c1e6003002c5420003e448020110b8201801c03400c2c4a90002c0740041d000c418044069400ca000b0241c02003803440c03182814002500e18042500c804040d450701040c0d100110b81800310001c40c005200012a00f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 327765341 1250 327764091 327764249
    0x8090111060907030b0606030708010b0a03140a15091503230f0c100305010303050d05040c08030c0109020f0103110f030a021908060901050306011d0a0908040f 70
    0x1c0350090440da00301803a8010a0103004003d0505c0700540c202c64243c52032811810012800303004c1400c14020b9001078a00400d03103042082c482d40002101c10114510326403203003841d04289000d442040790b00c48901da00302d500020041c041c0d101e0343c814400704100000e18a810366907600c90024400d0001910260b00040301c510401007032102c0c2e0800942c0a00901d5a1441d010034400d4460120040301d0506181c500100301007a0030400b29041a001800005010b603a40e25003100c100300e007a004139015120203e21440722800540c8242e18440c02100c01c0c003140d03001607004400340d503458a01d60030055000d000d5071881401d084061038204040c41d60150a218140142c522070421190480d400103045100740206800c3c4500058058002034000e0a0150705042c042081049246c050b03003481c031392030f00c0000d03a840d08541c010700b1015481606a1307a200d681c2c081c00746103441c1600401c604080241707082c5910702469280d0707149000041e5280741141e03110022a100aa03040c01c80d07610806e83c082c1c6608 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 327766591 1250 327765341 327765343
    0x3040602100209031c05030a05160804060b0d050d0f1206050f010c0302190305030402042318070e0711060a020c0c09043e0118210f08040e060301150308090111 70
    0x9030080c0e08030b64800b80c40c0e181182c850710680d127014254082d440840310710422156806450b90303a00c40d80000c0080744991010001c144810f124000150807801071480300850540c1c4208030a00c0c150301c0c0d54a020124080020500448100d48101d981c000700114840e48594003850b20490218003078010b41e40300025150100c815001580c0c411800518004100411032800d40700d6901110301c01d4406100b104010003c0c11100d15000e0103000c905000c2c3d044403541040100310036805001840c035142c0741030920400291001410203101c0b60280100c00c00207a041415100740c0d0110201d0600900e213821049051100b0100c02500988281d5500c8080408030f244032103440f903ea0b00c0c81c55915111820700e0400104a11921a001341001320711905801e5002d082e188507801c0c0c07450f03640d08515038009060745800a8848101c001c10036040245100c05005280f000741045a4000e00c042620380e032142e04040c200c84079002e051007176a00c0c00341d09101140444c40603010711801070510702085a4003074640c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 327767841 1250 327766591 327766633
    0x1106011203090b1207110c0a09021b150f0c040503010e0d02010e01061d070e1f0f05030f16030605030a060504050709110a0e06070606090902120304060210020903 71
    0x1140001040c406000209503001ca2100000d22142c1002c0c0d0524030502d654507449940a0700b044c08010b010356180703042c100c0600c021100c080008000c0540d01d559846818069041102402140f518080c82c00030a1768020074204000c4d1500c060401581d0b96140010302e0355074001c0d000c0b8074240b105000c049071541b800d100d604c905418403801410000d205450080c02c0d00c4081c00000c20690424004210f0038039503010801c0d5400340413034a0302c01a40c584400701d94900c200d60950740e220b203052103005000b10390034407001406501d0707940302c500d110483c01040d10103120070780300c20481690040003d48600c04540d40b071950191b0a1801040f03259803500000d00e00f00703c21000791000b031f58440c240800c01c107081004500078500d0038000d20401c200d035082d01c9654026007466000344800d440c60344141c1c0e9038100480e0040e65001000300310707181c2c44081039001807104440880c000c4a283d040c180200d440013058404803040e541c014205644c80e41202130103500900c02c030035050712031858034240c2c16520f4a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 327769091 1250 327767841 327767849
    0x40e0d200123041202010b01050409091b1d071b020108060312030a0212160918090c14010e01030b0a1406091e031c080705070819050901030e07120b07110601 69
    0x507902d40b4145410880c0c10811101001815603250014102041e41c100041d00c00721a08541c0000d80c0d0515810056410f0401002800600340b281d03602065010421038034a1a407048040145000e6980c3c40050350748402c60007803169030b40c10041300400150b105840d01c903400900134040d10340a014900e007002854009950300c0303d01351b40101d058240403100c5404141c1c88680000001824071003418042e02d1140e0340e0140c0d44070440081c0c1c0100c403c9405800c8111140d80c81950b4141c050303691081c42d540d21106840440c001810000008141c0d8030074042c010000c41d0040903c00c00c0e47ca480c9000b080d820012200c1504594203105600d210b0351034980210540e41040f80c1d05010844401c01c05041814090700700e90402101000b42c6403440d0b000d03d48907484102d9042c09a954822418040c01c070303004510381e0125018100f6050910294000302600240340c1c01c2e02c05100700340c98115080d0b11990a0701843c40b503460110390700c4004c01d006002c6140c000c0780c107007011042d0303064a040040c02d01d4800d0308 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 327770341 1250 327769091 327769151
    0x9010e0a0b010305010b041502070b070804060318020a4104060f0b030c0a09050d050c0a23060a180320060c19020303160b06040e0d2001 60
    0x400100e98058000c001c00d208007441c04020030360401135000407501890082c050030610805501300641e000b0801c04001e03216600d40d440e1103821074644400154010300841001a0404030b01503c0ea104803030070f030823000b54010038120281e403d203410304200000d0141c3c0840140051042e2001078205c150f02d49541d00e400b1300c03c580c0800a03031000d10082d07401a038840e4482c0540c20702c04010289050054030f03000202c0041141d52580c3c07507034040f1100c42040d0010b9911041c5080280c041220014400641040654240c4642551010f4a08078004854445c40d9100c1800340c80701c07a5458900018001c0303403114144008025408003002c00c1c0245560400c44540400e02d6002c035210483c001101040701084464610b0070482000c087d842e1219182c2c588400d040c29554101155030500641d1021900280c0c1c404001546003070052040c0c3c016901d241c011407030710800520030308000c41c4800c04040941c851440074607144c04103542562581c1f072a282103550310149040c51584840e0000840e0344c00103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 327771591 1250 327770341 327770369
    0x1c03021c110c0a0e0705030423030d06050405060105071511030108030307080109090317070212030a06090605120c01230d0b041a3003040905041406091504020303090901 74
    0x641d4149480342d0303410424422045003404000340d02480441d075a1090302460501e440392910300e04502c01e100d03100e0800041c02d616110307101e9a6039000000d00031a038080030040c00003d90750010300c030444070700b0340c4e00500140c001c11070080071444a81a420010381e414200042d4500c101c140c0609582003a000107000e5040001888050741c0e100749160702404003541c04201c21500b55030080d00600c0c00300700a00520384c95000290b00d590090090301c540140305480a41e0301e00d05030100000a0095005100e141881d240300031805040240c1420942e8080303400400e01140000010f440103400ca1808401900c83c54401c02c400c06034140240c00580304103c03010840814200801041e55600508401480140b40c0b90304143e030340b43d41c4032003403101d0b1400b036234006001e47c910851071400d0401c00500030740c0f000040c001080b40b89a48001e100320f000d400c036000001c40e6104003644844042d07030321001690105561344511102c0384101d6030040c0c4024100e030701c0d00c0c08501c00701e41558002d901c010b036036101e02c0f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 327772841 1250 327771591 327771617
    0xc10051611151b15010e0604020c060903130f03170903070906060203030a050a09110f0d02060c06090f0f0c0118030f03021005010510080f0408120c03040201030c0305061c03021c 78
    0xa444014580c0f0181c1018181100c58005141d4a1180510803062410801c0003c50a2600d4540c1214203040c0c140d406c0c3c03402480c01c1c804141d502c0c0c1c8802d118500c000ca203040001094002d90503a40b003626400220780d0303204200c0c805002c070290071002080c1d6150162183c0011103007003601c110f100502054015507101d00d0310352056000c07514010500e10310039040c0601200018408030074401c80d420210703148240303402d024000c11031100c14144000e40002d0001003907058a00b000a10904c10ba041000321402d05a1107403920340c0312950706a40300519401302c4c13500d0a80390f0064040c212401090305071800d40507625120f980201c1c0c0f030000c0550242e000b080b800880d5280318000c5034007600c41613900d100701181c0040003c18645c0020b00307288001e01c21001280800c1225822070710301c090a0420b0f4400b9007400015034082d5031058404a002c21700d0f04030410303101170203800f07142e00c40c2c0703801010141c00c08095880800d0104200300202c2c2140607040900f4210b40700b0040e000b0b0400706a075640c41c007003141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 327774091 1250 327772841 327772867
    0xa0806070206070207060309050c04110f1305150901020a11031606030e01051807050f0f04050403090e1e070c0f0c0f030302070801090f0f0c080607110c1005161115 72
    0x3182c00001c00c248c146099038002c40d40015812500150035140021a40014010030f641405003010000304a58006000100040200120b9068540460790313418080d6065998013054401c4580c2180583c00400d5840040340544030f090070501800f4041d10098010345001c00d0b0140704913040f882c0070a40d100f050b500d2b90f020900c1a9075201089903240c81d00c4c900382d200034560707408140c842c0a1103141c409800070416103414003040c0394810b0240c8140003030b0030185001b42032144540a20044251404001000c0c051b00400d00140140100082e80351a214420100c1e200c200603c8141e0344c0440c150503600c00104001d50040c020f00f40a078100701194114a0000c1c18500b16600c030b607050723030705141c1c0a1000c100000100b50356140e11550241000d8820b10b403001c88098036901583c4a40518010021070542142c6d02001840000003520900c5107090100030051541d00c144400082c410711141041c51403c04880048902501020780c034441010300203011103460003540080d01c1004696101e080407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 327775341 1250 327774091 327774103
    0x20d02120126031e040306110a020610210f05060f010f12050d1808070801050a0e0a23010b03120c0607050301150c140303040c170c011b020a08060702060702 69
    0xc0b4034070000d00010644580f41d481c01250107150341a4928542c040e81208540b049600071948141c050003a060340b64140e04a64000f2003a0078058002c0800003000b04200401c1035081d21140041c001c4d0f00c0b00000c0740b510140810817170448400c44018081c40204504000080c410380e102c40c40c4030450b40c188480b004840459030f001380c0102076500710310800114080340314010080c43d0b00d06a42811003005541c800c00e0301660004640c0d00440300040f89820041d00998440c0119000510501105c06801130390741c2c2113804081d10755907a5111075218407000d0a54060882a044004280f14016400107810007017009101480c40c0d100107040d0304182d03010700003940d220300c0e01e007005800e5614003140c441d0099403500850040145030b8030760300304014800070a800e1106c01c00d030840792039282c103103445490700c5040d0040c9442140540d0044851180005030280e4030041a0368000040c1403038002032109201c00f00c000c82c1d000c0d160000c0429a1501000800d00c100c20b40d50081000742042d180290511b030f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 327776591 1250 327775341 327775379
    0x201200601081b010203160515040624050d060c03021b03040e0f011a0306180a1e0b0a0e09030c010c08070912030504030803070e0310090201030e06040b010b0d020d021201 75
    0x303281c0d890300803144da8000c81030340c0c0d544218a10039003070b07005145495030400101c1898015480302c48410701080c85a244e00480480c42c1900c01b16070314162136001982985664460f060b4030189003184140060100d1700302c1e50080400313007000350034540c404c200d444131806031001e0a81e40b43d20219042000600486440b0381252110030b480405504140911014611048040c00c4520000010601d591604941000c00002071305410406042500583c8003814926201030b6048a960000070f100b0300e540c0c03040c044403003401401c0e001580e10b0f200d02c514419200500302c021074002405403c01c0001e0a00540004140d903a5031008a032030a2070015000c030800e604180350340d0b0f1143c90340e640042d402000300d50603203801c01c240c03d071640c1d41d2900c21a00d00780e20524403505401503e14505050a540e000303988014404d807000c0c002000c042d40d206a441c0310468000d042212404010032854541200401d0f000010000140c60619800d14107030983e404506a10f114074041d00040100900743d1003014520 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 327777841 1250 327776591 327776623
    0x1302040b0d15121403070c03140618100b03010f0504060603150209030a23011103010f0e090604080a0203300a0209010807050d061e080d08070903060207020120060108 73
    0x241c14402580f403081c04915005050703003001801e0300140301003001910703001540102003190b00c0340c6a10381401d100070b6842200c407840c401c000c00709008035102401e0601c80f1000c10002d0249000c059405c0c4003038101c107080942c0656958895508600c0903000d201c0c841c030b0040d100410740f9855440c0502c104145081080003030751040c01401080e6030003060140005421000c0d176403c4000c810071b10214050034401c0700c1810361804004842041d02c3c4809503040b2400004645201540d030100c0425907601220a43e0454000000203000030b40303200042c10b1035041038412a42840c1c0c0b4550582c0356014030300c02c048038041c140d030446a0800300d1140125400007041005505200d00040042c191070805403114040c000e0100302840380005941c0400004e055400f0070710280790801c1c0300042039400e82e0103808600c0c061910142c04440c00b416149000d85103036641c0d40d41d410302d0750b2a01402500501401c80c10001c8941001000340000f6503480300c0014410054055545407940651170006015140605 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 327779091 1250 327777841 327777881
    0x102070608060d020a080a0609060c050403020a05091807080a1110050904050a11210603060712090510060602010c021618050a1b11010b0901030c06030b1302040b0d 72
    0x591548201c805412040a8908010300b140d1880040d461000c2500880000e1040b01360b00300620807103402c01ea52060107104204082d1081c1c010468040c459408082e412032500d0b68200400c3c10610b0a45500042c6400e03541c00111041e82058100b80b519070081c5003503840b10100c4c030180808000c074403a00040840b80c41107985540000900607020744c100862040d0b83d01c0c000038014000a400c404400b4051134001650307500c812050000090340110203103410700115001070524103000513403a00071400e94031842c51404c0c0607989040a0850030000322840e0081c042d64280088290040b007001d00f00580012a5511400c10001c2c43d09044c84803140d54141d00e01b00c104100c05400d180c28004500a41c80400d4641d62038680d080070b40b2407034aa2485141540c001010420307800400c010701c082c0041d009201400756181009000c0000380009441044841c804204150081e803003d8810382c8090080300c00e031803040020000703d0300030340e10240c202000041d041389903013030030f200310401c62601c039040d041c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 327780341 1250 327779091 327779099
    0x804031b12030c11070b1c060501020c0607060204031e0203060a2c01090b27010501030515151201060906090603050c33040509010603050402030616090b030a0209090105010207 77
    0x140e40c1c22955509028980d88060a000043c03069001c00b180880400072580b07030310303611140752505a10803c1e1903000f03806c2004610808007480d0003680c044440580c01015500c41d171800704180da520014040b43d155900f0040000041e041c203a4484080b94001c40380c5003644110b00602d801c0900c01489400c41604e05801c15804200321481100964a41c500700711a980d00311000c140100f00d100405840024150200110b000804080700340042066460701d426855607010b003030a0750400c1c0001803690b0002d081c0c051452541035141644511442e03008196040c61001090441c000410000380c00c1e51244418441d484650241c4070050490344010004545140c941984680d800c06005204080c18103a550718072250a07290180c0d103503c1c220503c52180303031080003200c66101e80719050190740c46000000b160360103803180c54072540c0c019014011b0f554070480c01c040c0d01c3e480006ca02c400d100c4d0354174010804803100b1018500c940b20074040140d940daa40c0c001c003da24441603001d0f5045611440b0284 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 327781591 1250 327780341 327780353
    0xf030509151603060806011206060e10090522030201090b0919020d03090e0a1b0c020d06111e0702040501080610060503091011032a370804031b 63
    0x1d82c0c490190075585904440c01c1404034043c0c0b0340c661001505118201c000f00d40710b030701182ca280d00184680c00410070740f80e449012021004c0708032400d17881d507000c030042000100f087d41c000503800b0710088248650344904400e04000780c0800341054005039034907174030712003040070358000503410028002c010220485800ca030b049001020320f000031302031240d520454003094050100c080103020405080c2910f49007022a40300244407010358641f00076010b01070200c58901811a4104c5c058001d400401c10b03c42c80d4940c030b005020041c004440402042092700701900c000e14030343d041d60141e04400f0340e40300c119004002c141e52060300180c0d0107410101c01d201601d031005000104407443c500740b1684036566104814117203615250b80303520030750070444900100c40000d00154410002e180c145e0481032000ca10079411303005c031306600c0301032403008010b10304901070024505031800010003c0c210a0440301303515a503604421a00640100764110103000c10503801903007900e41d426282441c0510201c05031980 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 327782841 1250 327781591 327781633
    0x603030403021309050601080d181208090a030803070302130506040e06010c050f070605030115030c020c04020d110c030304031d0603070c0201020a0c0611100e0c090c04150f030509 79
    0x3807203038691410401000f0030b1030304911241034100c0b041d01d106607900c0c0440c94803602010300748400a01582d00311921006440454400e072071744205240541c03182642d8010f4a9030000c140294000c032840000130014040c50000c0d84100b040e6540982c840c030503a10759515120840c5c03c110311615041c4401d108030700100720782543c000c20929003103080c1e0280e420700a0030500c0c400c05a1101c3d01885001085050300b25008604842c000080710100311494803048085400d0f030305505005030480340d00800546490303000b40a1b10180c080e0002028000b0b1700d4000282c0d80000740140c2d184e003000c010041810b0700100201c00041e0b00c201d00f40088110000010f1591000800c04403c2c4208001500c0075a4400c200320140541d000d00d203c15225100e1030064915106144005440e1007008100416140c082c0030b40d0f5a09d010070f0004040f6034200b80200441e0141c01442003860540600c40095400501c04070300c540d9240e96215410740300e0316030000400343c94000300713400303560b61000803102e111440f00006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 327784091 1250 327782841 327782843
    0x6080705030a0f022808150601110a12050912010609140c0334020106031b1a0a03290307050a0503030a11010b04060603061509030b0117070312021e01050603030403 72
    0x5481a96070809109203041242e940c00f0b207640b40001000030441120024500c011f524104141c80300d9543d8a02c0112a8503050244004042c0c002d500b9960001d020f0000a0007c0c5040782401030920700307102d003c15a0b8460b650026101691500b01c20403121031540b01e810341c148100d4405100307601d03001c0400c2100f0300c005840507100e506590400c0e6025030317007140c0c082c1054a0070f80403524904126800240038041900040d925031254011206d40c0700a000d644100315401a110340150503103540c11004540c10005a01c41031603106c1d0141aa8040d024404810008429482e0540d001c821070070716141c0901a01b21034020004080140551350300001a908009450b00c1c0050035195203005440c05810307810502904542071410104e0400d03010b40040d4240c070f02010805aa9200103d01143c4405d022311001d051b5025080052005070150b420340a0030621030000c40b0140380d582c0c3d032000d6000c0c10b0004240010780200000c10008c3d03014080d1a100390418030001d1055051140001c0d0b100d00c11444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 327785341 1250 327784091 327784099
    0x3270a030e061903050f01050604120807140a080c07270515090108101416081f0f140102070f09020d060806090a03021213050d050102070c0906080705030a0f02 70
    0x210304141c99807084216011228000f260000000190a000d000742c0016030700002221450380002c181420084255811540f03a400080c460400a417112100d035401110b05072402190f000c074810340321500300030504440d4403c0c002e655903182d02c03500300e90501507150004445444c4102d48410102c1d210f00c100f5020100040340028203480b107041665070200c00070802500304038040300005041c1c0e0003145e1a05c10118503801800031600820202c12444003c403880514001c000601b840250b10a02c3c555074084c101d0f40400c5c0007000e02e00ca220b04013042d10303400000001c54181d07003404214500346070704051410030300042400070309142101486011501950381e40f030764041104400f62000760441001041120240e80f41d0341403101c162502c0c0e071481c00c02a009486240d411041603290003044400810300e480040303032114204001c03c80e6110030300105845c2c56409011100c041944903803d1001043e001c41c000a44a00d003820701d904041c29a807020b40b02e50000d040074800301d07104468929050768121 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 327786591 1250 327785341 327785357
    0x714030615010f050a0201140108010f180c1202030a0609050615030c01090b0901090b1209191707170a080f0703020403050c0f01050408030d02130f06021b04061a03270a03 75
    0xc0c801b2401000701902c03881d403116007800001000300040d80058051101d003071061041c0d41d6045094000f080304030400070107440c2c40550401c0945a90007402021034401029120050400d84a080580b07000050075101c9410540501c48400c1001c803000c04045001d0700030b050961103007000a0882851445010410880013800741c3d0140e208101304c40152540d58402c07600d404d603102c0c3e418440304042740c480c2480e1080ca458084910b241d008224410380d80030340c0c0140d21152152038021181c01460b012641a0440c8030100761300105200900407200141c3d42e00c41c002c0c58191940c40070144043c141c40c0c1814410001031002c50004510700d85034610580702d2148141d22100100e03580c0c0f007194850701590002295032018a560368000300350707204c124410540410348032010030350b00410740d10951000d0380c8605000c140710000c600c0c0c0c20f080081c00900c00920255209100f200c1c6480e90281208107503000000c0040c0305800994408600d4070001c08c21124004007140c0b2950b036002c5800180c28000c000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 327787841 1250 327786591 327786607
    0xc050a0303091b030609060f0203040c1505040f08010212060621090c030106060f2a030309020f06032809170f04080d030218010f0212090301020403050714030615010f05 74
    0x41c0c480c160a8082c4500c1a00c0c3d040c0e5203040020040807110401c81e070443c03e1070405281d050281c002d0301d01407074000f600308150310b00e0303c0402c20074414901d2954082c80028440054401c8a40d0382600c014481000056543c0103507407141c0d000c070b14000300341c00c0c402c1000703003c01c0c05581103940c01d2811110548082000540b46c104810b0314005c03801c4030007a4150308082002c00c800e130b4410f050b100046070741d0702c4500c80e036240d0413030b04818500402d01c0030b900102070f40101710100707102e50070401d025400940a2030780340e1003103030224050347c1c130440750b51089180c2c03080c8000c41141c10800c0c0402c104541642005040625528a01d1100e000c0d6031041030210082a4420741d0380300007049800400c40340d012185c0c210002180038000e50402274050000a40300307440d03589194001e0121703a0508580358003038141900708290461098101d8254240c06660034000440082d50403c03044002d0301440342c64101804013002094a0080020030207203650603125030203040c590700001c2c10010904903090550303e0b5441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 327789091 1250 327787841 327787853
    0x80a0207030525030207080606030d030c052215030608030a050a1701030f0b011706010e09010902030a050a11031902060f070f0b09070b090604050607110a090e0c010c050a030309 78
    0x1200001a1541003c6101100c54124020700c40e260500c66020b0b130303090b150750f041c031541c843c4000c5031550340580051800b45403062280d4401c058000541c00c21509001c4804403001000b5000d8826a600d078030000c10501c1942c1201c071005c0080310f490710f410b20030517051440c250f4490080c60314140c1440004141d50318080d000e510010307603030711420a800c0269a541e0800600b00394040070182e9842e40c0e00800401c210170b111510b03c000e05002e0303004110b42d928250b9041d00c6500000e0030039000307540c0c6441c8880103a0b018044003202c1d9000e20010a0722020600340517803640000350b41c20344280e00008440b10400c00401e1101c20381601290b6030354035540c0d14100e0300c015124080006112801201906080058036841c0074010600c02049442031501c03074481c00c50f240701709918107900041c00e100802c241c1c0340850080c10b00e144a120902201e800002c045920b5520540005141d1a00e94040110410082217030085558003480c20032811449070300d80ca500c0c1c1303410300c802808040c0c96284000500c89 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 327790341 1250 327789091 327789097
    0x30a080d23090109020a0b030c22050621010f030201020a0b0417160302010507090f0e06130606021b0301060608070309060603020a0b090a0509010803120417070809040e0d080a02070305 81
    0x201c0e0607146200d4039120b08060700070540300000724410004901e01141d0019041d007900e105680501820785095450b050f0104217135888004032514403604000402c2540f6030101400360b4001c418aa820000100c1750031566000050f0041000d0308107031142040540e0340082c441c01a550480280304060301d490801502c103520300c03103000c01d4004000a110075142d071751001b010b90380ca009900030021a15120001c4405140c18840c0311002512020305009009038103512a030403c0c03004007000b500e2211541d030402901c1e856488031000d40c1010b005a9844181c0c101c15150500d4200c5c02003002c14102a0041e22245020341034008066690200004000b03055001e280a140c006007200a03030759642e07001d54810386c4000501400740070100f000003414185099a03d05850404014600700640c140c5841e46032a4010001d0702c84282c60680d440240a10800602055004c0d0120f140d440280c1024441915030001c610303030361f40d8030a000d80380005074806601900511000320140e80e0f45c013107003811107440c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 327791591 1250 327790341 327790391
    0x50303030601020a0308103f020a170f0609060108060a0c3006090b0406080105010308030c0919030c030209160f030b0301322a1b0d0903050c030a080d 66
    0x200b0401c08c03138140404481d0044081e10043c0000301c50518400345101300d00180520000d4000c0c58045050103000485d940c0c5c070442d10523180880300360701400f807a098541002943c5041141d040b80005100c18481801913945c4080340f500c2c01d20042c00b00d403070014a00241c610a10120340800001c40d010320310f106680d40465030004c030091000685034000000101161468180b04a04c1d00500084920060050f58101c03908840c1e190300b140d49e0701d801028554445006641c0c4038940600d125182011b1111120146029000e6040c16034114414011100170151561110840b885084a07041d40d01c03010f407003080d0501c1d18001c01c0180110000c2800b400b503401900021501c442c03002c2005450552002406510005420ba401e888000741d241042048620951400ca00c201b000a1024020b40041c40030341010600f484904180041041c18060895510000650101000c1082c45020400c9410051040340544003101e400ea4400c001e0b4480c48040c2860562180c424100c0208200540c4480d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 327792841 1250 327791591 327791609
    0x5041104051e0a060503030306040c030b0613140f21032a0705010504180203040c050402030108370b0c04120f03030c0c03090e0a110f07030801050303030601020a030810 74
    0x900302440210b040340070100325400c240000d0400681c02950a000342d404841000d4040c40c0355407146001d220281003d80c0c1d4603400e0549031a11aa12504d94000034400140d81c00b1200c2c424500b08090000718a42c80e20500b445400c0c8480072000325a200e007070001090b0300c58051030352100400d00c10303103042d4003811404014000300c1d01e43c880591426119050340658082c41a02d8000341c0f1080107480c00d0107180251100c039600c03c0704280000c401a8000c41c0c00c103000d10312100807650740e0b00008050381c1c0240c00211032600088a003101000441d19607002c4401031440d8000385411040c0c0c107000301026201301074082900341c0c010802400800c0700f180d0203410b842c8405201108a0b05124417020035543c0304400003481c0c5407001003090f02c41d82d04840c1503503141d0b44d0308030018a00048404c025801a0900c2c460035615006841d103030740140000c001344c1502041c815100d81003401c0240c07005030144d2200d8001c2d0000c20421840303a0340803405c12003190303050030301c15460740ba142234803c494022a0028448 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 327794091 1250 327792841 327792851
    0xf090a080d060e0f04050d05030c04030c032a0b16150606020309010807171602101e0f02071502070c03050601030302010614030d02120a0e0a0f050406150c020405041104 74
    0x8041150841403c0c0e4108440650f0035071158040080c0741502201d029200e5000200140850340c4101c00640d00000304100c1e80d824103417603449082c440e83c0680e20032100442340f1503d40d6486900003440c0c00042e021800100c00311440c1070742101e0b2922031540b260240c034682464500801403402c031002d016591401e8104155500d032407010f581c3e548005a0180860304210019070110b01c20b00702e80a007003151040324401501c82200545040d51002c80c0d44080d07010782000020148464441c00400520395690810244d01d808c5154084508440320758000038010003c14002c240744600c94100d6100c0c0c3d40e0300580d2502c1e03a040c4204c1034615a00014a01d000380b5000105065054100d0030075107003044501880b5040c8001003595136581401c610000d600905040c0c40d06983d41c00182100049a041c11100c0e0b05040c3c0c00178450004580106910740408038044c000c42c2054072400f030282001410a0b1a00e80c0e1240c1d02501d40452000000e1046403500001420020360b40f4004076804406001404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 327795341 1250 327794091 327794107
    0xc040906090605030f0703030c11062b0c02030c19061104120c050d11101b0606030501050c0f03010b070f02040e1e03030106090905090a022809140f090a08 68
    0xa00003910403641300344520144509058008159071080740d9064480c407407030302039580c4c61140b50845502078a6120300c0604c490440100f8419001c61708510f01004091502070126410003264043d0350200219442442000d015038000110351040c08000c1403110081c070080d151040c0545a04140d001d41c1c280701081c0042c0b1080b800450032415480345140c8a8000d072164140501e409200001074a5809841c1c4c1d189024200541840c01d020074a28006062070390104440a031840c02c400101c50f025504d00c1e081051020a100381604a0300360f80c1104d02c1d19080300c0d03d040547c001802140114907000a4403400c1200c9d441e403e201c0c15a000e4030034011300f0034501c8450384401d407030300d04440c108a4100106102c90400f10840703050714400d032280618607040c421480300a140081c20140c1500c20580048050799948800032010320720100c0c880e00241c40142c1c0b003020040300c0c2e4041144182400710401c10705140080302980046040d013070440d030781c1d121811240341c0003604901604001d030004000c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 327796591 1250 327795341 327795359
    0x705030703111f020901200a0c090516110a02030d200105010308031503011e0c1205040c03020d03030f0516110f060106081b03090709052d0c040906 65
    0x30009000c2e44400544400c07054031181c0f1002d40f00c8103841c10a04680b40b0700c00600c03283e07018004405040c5841d41c48003d003045c3e0130b034407a9202003001c0d580ea071088614a08020030407400c1c4000e00380d001d40c01e00c2142050b510300507120099a1030282880841c0320600d4106800b0490110804e0700103088076605114444050444041a5000c82c1868042e4480b02c000341380500807241229804100035142d0f13a00c481450b400da0800f9407446516540300c41005004c030203003a603040c180c004a90700010b01144451406446034038407100d08403805d8100400c20000c80c81035120f072800c9a030151b403450032141c4540790480043c11100a6203101d00d01d010180900501301404038500ca104580314902c81172807400041d559440d1056000009500000040c42000c0c0b00382e4415410a40d01401c0c807901e1400b40303860f030f40c003030308116a040360315805802d00f0808010140145030300000302c500b05050065002e136403103e0030001c0e1455400c1c0c103070105010030711100b0900100e070000d05400c0020030156403500400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 327797841 1250 327796591 327796597
    0x20400b04050a060c050a0206030619030503130e090606010309030908161503090b010909140307050d090f0303020a110111010c1d0f131a0604150f1805040e010b0303070503 75
    0xa0250340c40450100b0880d004004a0072513a420000401c881142613080060540c002409540c02240301035900441d000308200210113140708402464559020b2040c05030909150350100669080d03650030b00c50421000f041842e00603c007840d001c5900111170a040d6107100259000c41c00300d11440e41c5004151081c00d00c000c0a55605201c4442c40c0c4900303400440a035403500d54060840300d80b10004001c2c450181d805010070501c181c68103a8220f000c00b9510b800e40c0c00442003038440384c0100c150584480d91200d403c00c0076100107041900094210b8400039950382c440c02c402040307581c0d40001440b41368059214141e1641c0c00310006e005000798079800610741300328400c802402003100584820180351484810a04220240098030b100c030b035011015018152542d0b41040c60105150a04040e456a070f00600140c60415042100140405d80c01412404041070001c100141070301180140110100c051341150012540400c0b0345113a00d2540d40101055010300c0c0e4140300c00102e41d07081007404405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 327799091 1250 327797841 327797849
    0x50a0e0a15030f0203071b050106050d0312050601020616050901021c02010c0336080904050a02070b0610080112021201020c210c030405010f0c0204090620400b04 71
    0x34040352030f1841d156010b80c0002d486a00c0482e407109203180c1d0031510605a1344a107800f84c000820b15070742e030384086141031103c20400c1c1c0000d410300c400308038150000d01039240c00030000c0c401402035281c42a00c4440c6100300d54803c600700000043d80014a0b84204044080041440c00c100c0503115140c001900a20b0800e0721000407070b00f0401d00018102c8c10f0006440030f45118100e0008085460984060400003050300b21150503060203188810780707c07403054921402803c1c10041e034030031080c14112041d00d03005141920501d223041048032020392000880d41110080d5011021600051000a80c030002c1010720007295840407440005800c000200100000000c0c82c440162203428600b140d694441d12485060320344c8200410031036940b00c0c04414103c21240d1038290694106640090250b5001c21815148036031036140001c560f4280c0c0340c0540c4565a0102c1503807a01e0354845801e02030142c00400c0500c08001155840340501c020400f00603550441d03915401055100c071000110354002d401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 327800341 1250 327799091 327799097
    0xf340306060c0206160c0906270506010c11030c040203040f020103060e0c1e0c0d031a190302100309120c0b0c0721020705101d0406060807050a0e0a15 66
    0x1e038041c012141c0040341c03a000b03080240341811280000000307202d0110304540501c20345800040c0b021003031203400040c0c180a004042000707006400c1d0080d0040003154501201e00c0d101c1409400d03030304440c1c4c201149604c4240d140100c1e0000002030300780040d602d9101d0b041800041000104410442c0d090700451003600d00704881074a40b070406206080032505084001400c114414840c8820b9900c58a108582a81140b80c5640e40b804c0740d0030501d6035034080c004640c8a0307400d0b495000c502d000444640100390707201d060080200c648a032100c4507510019003d000030003464159944a030300300840550b04151441040f4811100003130103070341031900c1600c1300b085840c0490302c4d0064480c02c88942c550010340d560003201003110b408005400d20203c000c01d51003840030029a036129000c82101501c802d840d03515004400036060400c01140b48a00c6100324a0903000307102e41c68210f022250462110301c0c02c240c46641030300060703c0381380f0104507255003d5142d2800103450750244d1210098010659 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 327801591 1250 327800341 327800351
    0x906030809031608060711071d090c010e150c030708160309080a020a091a090108010b3313050604090b0102100e0d0c1505180f0c090f3403 61
    0x10b10060f40c801d414040c10016810050208070300302d200d000c1010b00040d000042d40c200d1561260740c0007062001204004a248042c020010300d003d0610a0040254007801d2800f070300010701d4001181404105150024404041104603480c2805c1040d1109103501c00011a43c90800a0040301000080341c1c0480002c0e1400c0c1010038180e4001c0380e80c4103039581c040c1a103901c150070110303402d01a000104100c0170010245045212540d501c0300c4080c02040d0901c0002200304803c03080c401d90b101c800c1007e14201801070505203009050300b031340419116800600070f48842c0600326000c0100b0299100a42c00100402c010440340e20b540d0100fa0007600907000c0b282041e1154000780103a071841c0300e02e4203036034101000c0181114040d203030261003503100f004401c0201e0185640101100c606913501108242e42418190a9001c204001c54040034600010b18440c1c001d40000b4190341c0c402000880510100d0780460411001103c15811140c07000e10405a12106001000380740b94400e00c0c501c4c0001d080c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 327802841 1250 327801591 327801613
    0x1d0a0b0108010c1707031b2a02030703110307080109060f240504020a050912210408070605070303090b1e0109020a080402090720160b042409090603080903 68
    0x5100e0602c5203001e9032110104d0152044801c2d2184200420007000e2680300d404400002d4140300700b02e2044400c6807101110610f4002440a2410806403003803540d407508416100542c0e80040c41000300c980c000c11040c004641000400d00344500c40d40324941d0384d1709042d688030800c8004e820182040c10a070404101c450003540c0020b6003203100c1542c90145940c1d0005c18401c0307007400d40082030f0f00705a0381412803402002c03001040300740e80d90b00885d840c1b41d008160006500a00d810041c040341004000090030903003481445511280280301d0a000e1000c0080d8800405009400140c03000303401840540136807a1403505880b81c1d44185c25a03045044595001140c105800d100396201c0000d550385d0312201e81d40c0da5007400304d040d40c00381040c810302c92001402c00b14014900c10016030440b0a07400f401940e508079041188000d0540c20116840c00140004e009144640100070340c40607030302d44002200011840d0903942c041944e04100c43c00780c1046008403d0050303200003450780740b2082d41220b103a0340d02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 327804091 1250 327802841 327802843
    0x120601050f090f0427050705030d390809010801051509091807121202070e040305090d05070b0403050708070b120415090308040209070206090606060a02011d0a0b0108 73
    0x15020084095a03818001d0b442642040d070862100100003400002c0d4440002e29803181c4200245500c031582c40341c408805081203070902404c0c1c014a001d0f00100400c0707030581c2000d404031005c80003102e40c40403074560414255a11081940301c04810007403001c0c00c45914205101c03a64491756600d40826501c900010306400c1200344c0000c44d004803540301c4e04242e20f00c0d0406c841c490001e00a01400c002c15140080c9024061100c4001400162000d034850607144c03a1220b2055042d034011005d5400800042207a4000949032a5011382d0502e8090742d542c00440010710701e8100201c001e0050b1040d40d0b40800c07103020704c100400c1032324040c0e803c64248695a8201545c2e803505e41c059400110024002c003042c80141c11502d5410604c03031040e40090041c9442d18208541484500b038000034083da01380310950404a40158000417988003410f0036190520910343d0320320b00501070714050301c0300090504d0198401c1d0301840302d802c0950541c203240d140201c4c2c0e45541d0702100406492814090b070001980c084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 327805341 1250 327804091 327804097
    0x21501030b01091109190302090c03102705070e0307050d200d080310030213090f031101020d05091c180b0904020903150a06141c05070b0705010212060105 68
    0x9801080051280c3c20455000054002d40394110043c3c1c0d01442000a10b54a594040090041407156140719502d5801040a554005408000180b81c10424000426006040314068501582c40740c401001512018125003240e6840c00d41c0052401d02804511a40503203d220606030072411200300c29280ea08003d41c00c549000000d000119501050110701584052800551001030114010800c580c1f13801c5983e91048a5450400074510014400c5180451020003844198081042014007035620122140c1d030540c40507050003200310303800d00804c2c400d404554403041e500b40140000e0805907580d680d5055840301d031412180d4026212400184103a500003c08a04101017200d0203140001080300b82d0720500806030002d80801c140005600c0411a403d1080750882c08051a840c0254000d001c60700b00381c01c0f02c080d40510360341602542d59415405220000800d03c09034110045103800d614045440d8809645a8000b1446000348032042d40039040b180304040b03044034295605001119148 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 327806591 1250 327805341 327805343
    0x3051503070905040c0f0b0d1d060415020c030c010b271501090911071b051e1801060c0c05090105010903080705011508010b18270a060c030c02150103 66
    0x39004500401c20301842d50440b83e0440c0c05110040111904c07070b40c403e00e03842d48a0308011142e000c00103402010382d281748148050312000c0c21600703400300b6455100e192551302c007401c00303003562808820350601001d903035049407841c0e11101e0803030380c0d500c03a0b0100c0d8078068440100041d120700300340c200604100d0b24910351a164688034481244030b40d44d90310880244044404030f41c40c1081031b0034402054100d024442d140070000742c00611512411a071500d0009005041e2003204c1058465108200b142c948260501070350743c1801081000324404404a18801070030513000c40003154400000920a4002d5a6000e4840c0504588242c8a40740c03414400d033050207105e401d0010303a40000070008074040802030100c0a109030004903040d041078030801d065038599000340700b06075980c41ca40c5442c0d141c1000040808410302501041602d06800021078807141ca018002d86030303209007881c0414420030b200300c03c1004d901403020420240d0f00300000b0014540c003041c1a0242c824480e0551980003004001d074102c0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 327807841 1250 327806591 327806593
    0x11e050c030609070c0534030302120714060c0306180405030d020a03020c060c09010f0306080303071107030b01230303070f030e180108060a050705040b0405010305130b040f0303051503 81
    0x250701d0b4201803000ca058010304040410042458050000c3c40c2030004085c510241c01c40114500c070042c0000a16940d2090048441d400440081000a070080341041d0034410f40007104c3e4486689060400303d0fa8510071042031180150b1040185015281c0040e42c0150801d031452071040d240c4400003120132400b0b85002c1d08a80c0280000303040410076800501101c80c0c039250140c2480c40c0382c1c814a150030803e0b540c5004d1250040707220320b540d580c0560714040010951400707000051400d0342e400d442e48006000c000c00c00c105c00290f01c280c03440c00c000e030200450340500680c1c00c035039544100807520400c40c2c420099403040d0000f0350b4042e10b000000e5900191300306038041a002c0c44c6580c1580c2d50782d60520303860381108441130350902290000100358000c0600030080c026078603111344042c04441d0000c0c10300c41840b41c1800240200b411000c2902e003036035400e0900143c243c6074082c001009641c10300c0024410081c02d01000104a0310241b207082c65131103901c0070302c829104c50a10301050803103c4c04e0340b13403d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 327809091 1250 327807841 327807847
    0xb0a0216060816030608030c0f06060402070f0821010b0901031b08070c020406050a180b10020d0f02150108160504060b160609171206010507080f0c071502011e050c 72
    0x10003524460082d0400f80f00b0704001880320340d518441030842d04070245000541c1c10080e0b280071364600c180310b9141e10a80803201146800259a035403a110750719500d0140104101081d2000c688880318a41c107a0340c2c4130b15900350b501e9a51102c1d912825404495058002401d0030215440b00c80015400c0200304c42c0ca0f01c034000d2951300c84200300c0e540d6040046c280e03406030326800000356030344402190a0140044402d4001400c6260014805450300a04003074040d000e00145903050350707400301e00004d024016261070192120f601904924140d2030441d00741d14850014000200c81c031000405940f600d1032a0b03000500c10f40d8500c2080700711041481071409074042008103040c9500c0c07004000c55054458080001c26512a81b60030300344c110044031034030a080c00010300b203030070105c0e039501507521070342c24640a464080c81340e44030388031800785418410b0599800300350115081d4081c0040c41c090024041d00c000341448200c0000c1c00f8140d440c3e00728030000b0724000c404500300500d00481c0d00c1401d83d120b180385 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 327810341 1250 327809091 327809101
    0xd180f0e060a0e0702010c14031005060a020c3601260f07060e1e01050d0b1c0602041802130501140f03131e120f12060b0a02160608 58
    0x4400d4a0041860358011030400d404102c43d070f214500140241c905900000d403603120004041c01c6000007100c840a03000b07061007000309021880740c026065071420740380356803604600b2105070b00d0714017203010440d80059854401c0e21a60300840300b92400940b000c400580602056840151070075085c0985102641c1000769004030200c3c80b084100358907014411610598480340c0c1c0e031030602e01c06030008000203107054552151491f00c0402c18200051454082d00c5505020001078031900c50681c2c01c001c0a515003c0881c540e961700040e85c501006514900ca1405084d803400c0c0000754010701440302611502050008100094820795002c04408510080c0c2c590820005503030250018034200440c8004122132180c0d40c10342e502440c000c102c55000c80d1441c0b0621310f04011505860700100003403210f10803184010651801400d8001032040c00c1c095604000d080c01141d542d01c2c502d1030700c25814103281d40040d42c038085100400d01c2a0b0650300340d8030030100e0015109050b182c5032040c030000a0160300855 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 327811591 1250 327810341 327810359
    0x40c0302120a051510063b120a020901090b0102030d020d150b1e070308180705030a0c0e06030a0215090406170c0f010306050a03150b0306090d180f 65
    0x480504607100807119a44590394403907160083d00040d4050003d4001c041c00340b02114440c8040246c070917070906048040c0c1c650050044101074048080c08046a031041240c075510a6001004551010b0b04201e0040c0341151055030300c04205004a01884080f000004c0208440c45600403601c816030107075260500020301c24019400c01c002d50240036650300c004a4a2002d4030a110009000400c8180d46981401c036414020821505201104a01c100001d40019602103120740c0e22039050100c04003180c1d1281c00c664a0b02d1080d42000d41c05110352020b240c184503010403a01b085071000c0010304460b94a25080c541c0303800b8400c400030f4001c0c101091504440e1122005400844405080080d185541d010714a40d441e079030100044040c1c02c4841000d0190405004102c2e140e0f4080c01e0502c170a40c0303820085805201284005071503502e1381d2000760450303521031f0003030000680018122180c500f0710124998480c0c00d100d0031b20010030101e40d044c0c0340b002c80740c40c0d540044844076040582c40d903151075800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 327812841 1250 327811591 327811609
    0x81c211a03061504240f06080c040b04050103020a03110f0c07080d080601081e04060207050609010b0a0b0705070b070b070818030d18060507030b0109080705130c1112070605070503040c0302 83
    0x1c1006103005c2d03450b420114082e00403500c01020402c0f0600d40e120b15080002e421480702415031024030000300401e1040032070f01021a001c545003031034010b95404118000310014000045100002540014081c16118042001d010500c0f001d8003a510f12aa94980d110740d1030150026400c00306901b24002200f40d070048403040c1d88508015401c09a114010042003070903002190b084803441c3c0d0100344241440710810205034030400080c020002c04d802d03500061007003a628819859519000105c0c00100641404520014140c10349120344418407460805a9580122140800140c41c90300282c8510005100c484d00030145201862401201308040b5024100801c280304080c004480c0e501c00280c65489254450402541d000402c40754100004200d00015400355003254041e0a007407055503911111501032968012000980908043c0b00303503030000c2400502881d5000f6030f400c4845012402e0018584984204c2c8204040d5a411400f1740b00c03170006640103800040f800000744014103000900d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 327814091 1250 327812841 327812861
    0x23010302010c020a170604060612050601030647190e0711030c0d08070906080c0322030306030501060504020708070303110f0d06031506081c211a03061504 68
    0x1400d040d15241d17070389680c484070f401c514111158007810401c400d02005115020141907107400c0407032500d800d51141c5d03a0b83c4006010241c0140c3ea10b08a80e120f0321801000d06641e20314404c00d0031080340001020110480082185030130010b400305101040e85050095a0214501c899038481004e041600640103400003c0003041400031008001030f1614040000d0905104018000c19005a44220080005401070090403d10000703190501080307802c1101d441c3d00201000080d078403561076149444008a500344900d00c1c000d20f8004007801d2560582004c419240a08024001c443d0380e07005000480c03290100c05444031030203002c0700001911940020780711800e50f0a1040c189481805000f0319540b000c0d1400c4201030b501e8008204002400c0c10211890f0102c05080012030f14000361240c8489680c0c0201d42411140034105098034061039522004400b07040703400500c0148480b8000050894080c258072403241c1a03d0b641043c503000400340d11030704810349061006604c54003440080c2400f403034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 327815341 1250 327814091 327814099
    0x90d0810030f051f0e0705040e0307080903010b0a0308040f0e01060e061e0c010f11091819090605190c050a0507030309050102030f0103120905090412051215010323010302010c02 78
    0x1c4401d540080c0131306120080a0000840b48541c605041c54a103843d40014092030500d40c4d814517038940401981c106682040b0340039550800c0b0030000b40101086402d299100660300c0f00071080c85200e5000e07109403100346488001079921503c0c003950001091145600180c85d030304c1390085a061030405400d00191351469881000350328520356004e0382080421740a135030354400c902e90f64091a406030701944540303100894a884070200100e01903010700501460b40d01500d40200300c80c002c007512012151030a64400700410b0300c0c0c500e03010010f00380590b80d5403251401e06e03060f008600868070640100c0c2005899031751402e140c480007611b668000380010340034190b488030340d03001040c8280000d40c843c140b4561010b546604503c0e114803c03400d040d480c40c040080300301c01407160791222140d20b0340054109a86440203880b81108942920644111420170002c0006020700500c4c0091800c2c2c0e010826201800074840d118102d80350308482c400d6401c107161031100104050750198a0440b0071a001034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 327816591 1250 327815341 327815353
    0x1809090203341403070501050403020f04051312020d11191106040f090203040b0c030f0a09021c12080a0c0206060f030c120303040312060608041202031303050303090d0810030f05 78
    0x140162210190b940500003050043e401c1a40d10329091103200c01800f800d0034400d08040c00c5802140c0418510152507010320368406c04150761151070380044952581c0413060b02c04009070032900a444100f00d94000010421119810700e0184002c200508444501902c0c040b500c0226200c003030b0300640c005109034003c8070410011441c801841c130f0400140002040160781c0c4d060a140c0b554800340700a1000c5007800e030606c00c2c0f00714442c130405107036040060804080707002d440038000980e01070201404180311485440c0c0000070460440d103a4480504075032201e0b41c840e940c495aa0090310050050507005070058000100c0d070b03203000341d44414000c10160441e1020001d440208041c011004034400b00380d400801000101a4040b8982c205090041000d0014a1801201810107100644000c00c1e2081a40303481118910801c1a9007960024001208980b0303500c1c1004c0e92268000c2da103040281c05503c14980c00240982025801080840c0000710094595291100c502180c0f990446007070041d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 327817841 1250 327816591 327816673
    0x3040213180503041401020f0703080c100e010f06050f0102070501030504050c0d03120f0603080d020318030313210f0c0c2301020c04090b060103090c0f061809090203 73
    0x1c1c65114500d44620700841d5194149a804040d040c8155101c60441d03000340007d070800000401c00c0f60840c4c0d4002407a545443c90444864205a18583d64520b603506c1c10b0060502010150401491103119150821905403280309004550304080c030102e004d60f000681c10065548654402070340a401042940d8002030001c000889121003944160006100d5807082c81c000300071446125003a401510042000510b10340e1a60124011010202035043d404800280f50483c41001c000c0751141c00000d0780c0d92032802e13070441e4901d181c400c2c2d800e07501418086404050b10481c84d08000d07001c0c00a894409401c42e515504a88030540300104840f020561800002c3c003619071007690701d10744014000028416a40c1b0002868840031415003842036080c005000041f407101009107800070804c0c0303004210045142413400c4140c8103588900d60b0420041d1002440c55030103910350105010801041da03203299503132810703020760348800406035240c2c2008050580b070311813035144101603151661241c1000012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 327819091 1250 327817841 327817871
    0x9010203070b04060501062a03050d0b100201061a0313080912030c060f0702210a02011d1b0904030824100804030306060203040f21230114010b03040213 67
    0x40d5804c4504607160320051208035004495400c40908194950a0a007140d01c110703030b1001002d080103810300c94009101d901f00840d0ba00201c0a00d00050056045190b00c2c01c00240204054400d0066001c52400e079064030312a02d600b00e07400381e145c9042e041c44d42c0c0349644440c0340d20392004002e43d40c020962910303130300340f007005001a004622010020303250074501301c022144000c030300400b00400c540004690303980c4900c10300c111381d10700c0e0340540c103460304c0d160b0803441a401880184011f070b07040c1e04100c0d0403c01200000924002e607001005c40390f42c4c03440c1c0e03103800d05c648030406a030000d0200302c2c0c01d400145041d0f42c0b00050760301b00c1c050f80201141c3c80c8a20300800e0796003400d175944200050207401008249501805000020805031001b189071618004801c0381c1240c0324042c80e14142c2d00302000b13462001c0c982c070200b400f60707401a5419518141d108080c00c05070144840c0e18219500f00440c5804010401d10441e04840140d011180b5598a55003008054404080500c5000f070340d6124400722004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 327820341 1250 327819091 327819113
    0x20a15020a0c090b040501090b010c1202070f0b0408240406020715020c030d111623030a050d0c08100902070f0b090a031b11060c0705101e0e01080c0901020307 70
    0x10f0180081d424020b20309100560340c058228540c441c1c00c000705052280da01550019180c1d40080e044200d614801c44100d040c000b496202d0030f4020080380022541074880c00c000c0c13003210038110403a0900d0b0904100711a1398000c0781d003007144040c2c1403800100440e000e900240b4019200e0f852a0b103080c1401e40340ba00490300240b100595a078000b003040368540000c2d1080385042e4a000114600700810a507a040c0041c4103e40d000304081d0821000010800c4480c802e540740b101080260ac1d140d04d05803900400c603811140400352490f007060b0101c0b1000f405644c009004030f980360f00c1e00c0f11460401c04d203c0081d50003100100c441c0c00f05141c003070b40800c04400e125030281010002900300340205050081c0380501c1030040c5245155207000e60800a6000c440c80c030080c00d400d40f00b040e258204002d035281404041c4d0f001c5c0b0b4100c2c0303000c04886200340c0d004001c20000b0054243c0d624440d0b070900d904441c3d01c0e45000d90700740486c5442d07020509144010740600104001481281e141107a29a40d8590b800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 327821591 1250 327820341 327820349
    0xf0d0b150a031415151201031b06030204151b05070603050a0e0f0304380703030c0219080d09060603260a0203030408161a07020d020a020a15020a0c 65
    0x8004a52021095814011000c0380801d007800c1c400302e4105040301c4c83c4200e8001010500c41e00741a841010101c15020a860110303001c83d416031203e40c2c1d80d0500c03010b00c1c113514280100c11809480040f921500910a8070251060301365101c2150300c1e03090054424003614400c40407055881d00c802c800141042000c4406029a44d402082908085080070103507400601d40000307940008800e110112800000d031402c542003100314004800104045c40f01000700d02407020b819000100d41110354401c0d020003807440ca4880d07942048030160b1006d040340c0721640d607210501c441800c40300788404508070002829000155800020340e40d0001c2d920075085414a500807500d203811500b45000c5081c10205515401602c414401e2600c40d4035000207441e41b100500082904a0214408500500d000c1d1030341c10f41d6601050042e6516003440c401620342e0800c0300c0b008010300c00d12000916491000c02c800120f15409030000c4001420000382800c507488600352a0114801c103070715500411500000c060081c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 327822841 1250 327821591 327821629
    0x311130207140f0309030c1c050f0601180b30070e04170f040603021305040f020c16060f080a0f051e0c04050f22020c0d11060105060f0d0b 61
    0x915104900b540c240b1000000100c00c6400c284031080b00c54401250391071b00250f0448030b100d1140311542044141001d4a58007030018802d9088000038540d000071a90705035140c0e00c080302c128004540790502980c03603807400c06801407001035240c042400c0440a0407000c448031185156000d11010301c60745041ea03527911840001030290b040c001840856141c0c500d803400480c08541c80c080c400145114144150f210748020964006103081242c21020540406014000d200703020145a10000c40d003c0e4101705072815941c0601e082e44503620010415140485405072116850440000c90035200c0ca000101030b20810380d142c140380942c0940c14030030309104061500c503040943c0b1b9140e003040d2038040010440700c504081000300b03004c103a030340d41d01103810850300b03c0f1015036a1712004070800c20103030300e00301812145001103010350460001285d8008640300c0740c1c1ea2160590701c90b00b0385a50311030082c8500c94014000304402c00040c840c1da001050f0301340d940c04006c202c0e46092004900f128142000e241c041c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 327824091 1250 327822841 327822863
    0x4021203180f030102030c03060910080a030509010e191205030c01180c150813060e070e011a070f02040b120f0a0606150e09130c0e0a0c0809070311130207 68
    0x10741c5042c240c0c0005024042d0000c5081d0700e42501988490305c0040e2400d0b100710b00b080009801c0145403c03d01c1c02402401c0c2c20368884614030314028000c0c0c1c01c200350780c0e80840c444202070400c90034400104c941d00061020406002c61805840225040c113014069680307020401a440c014072017401480c140d6045078400c104055941d0a10328801c0c40c00c0d07008189206504441d42d801a9032240c03034079030031006c0200c4800845013a440c0c500b00810a008045440d8001c6000004981103151403442c1240e40010203081201003c4a0f1501e00b441801d000030a800740c9d591895016081945c00010b000704083d240c1441141c01450044c0341146400c44011583d00104610017001150b01032203004101040521074000b4a48202030500803230600400c0c0920030920018012580ba031642c0100990000c54100c0000d48469461072681c03011a00c207900c1034100000220480d100b038288522031020700c40601007590035580c1d001410368840001940c4443d288102c0a020a113510040c00040e100d03010002c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 327825341 1250 327824091 327824137
    0x26031303020f03030708070813120909110403020306130c05061909060806010219060b100201020705010c09060c0b090a140303040b150303040614161202070509100b0304021203 77
    0x482d141880d9110000e40d08103006000100b174205a080741c12218600b00782c0d0303050343c60200307540070074203044005800c1001010400c4c1c000c43c1c000f91003c3c240c070f0843d4804c0c004103200319034044c40f910a5100c004d4045d800000003c0d00c506004803078406191060f5100341c1c1e255656000110960080281c0c0581c40c003605034056581604124500c00600940c2403411041c0b8100d00041e44940f42c0100780c4000140702ca104034204002d690040c510014010a101e028400d5032030024001d42010790221120740c0b81003010318105000c1e981c1034045803040c0c0c2d9038000408855a5201c0c050401400c1500c05102e81e034041d0380010302002401c141c01482100071a00d918013810850310741c19010300501c00350114100c18100c01d840100450b01505c6140c00c0800324400040b207518079503ca85000b081a07410000b500d8020031601448117044200e244d82299562900c607000c0200050042e18014001181c5410030409441c910002d154041c2c0020500d002900082405a00315804100c511056001e881342800c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 327826591 1250 327825341 327825343
    0x90509060f060a0e1801090b010f030303051014010f090e010902071109060102030d021303080309010e1005010602031b1908040612110403140a05030c0d030612020d2603130302 77
    0x364400811103200d04803510b00513105110300000ba01e607565040c0c505c1c2031a000c4039800d411000d072aa9010716110202d680d144403a0031401c0c9140022000241040040b80c0400d0b030711034400058400c1040000da500740248019110280c0c0044110705000400300e0004445a0111303400303000b4007608002694660251410b8200300c030001d14418071402e5000c0c28404140d80c00010f80312900d454440041c2e0b21003602180d6001109545e100904284000013040401c100642280030391580e0281103d2001d510943d401060b1740702409038600503030052003503151665500380d50b000005200c4065030061303410003d4820064020040c1526490000030301004895805210002c0a044c80c03c0e0810403202c0d42d01807444240b10701d02c8007401e0700c00710001100c00c00c0c900f80008032030150300a04982e513884014040a0b11403146081400c00300e8904a0300269050714008610450b0f6030040409880a01650340d891102040c1c50f4070b1181c201c00b544000076002e0101006600404c0c20809030126031010745402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 327827841 1250 327826591 327826621
    0xa050d0f0c1214010213090f09050321010806090c010c030509130c1101022502040b031024030b040b25020a020f0d0c15020102210402091b0a05090a09050906 69
    0x442e00b00c1e0300c1040b05818000a46c005001a01d080e0348011400c00e01d00c02c0c418024008507200a03106000009585074115510382d04a6000342400650140c00c0e80ea84c800142c03154401c032000040c5c1d0304601030840d01c42d031140e0408005144241089824601030710041138031039070042100030036039944249540b8079542146a51340c280c40d4820013945003000d4a4140395880c44000122240c4000f401c0403142150784540055160003006412240d100e2007600c814805041742c036251300d44561010030711060b4400018031081c190b94000300d040825481c0c07a510007501c814024540c400d901840786411103003242000c1a1100401710764010084045240100108040c01c075541c41d00c50740d0032040c0600001d421044400032100c032007050020703415060200380e0183c4510390a09200f038501e0200705064074a19100540594001e41c0e41240c60307541e0405000c068420044602c49a507018070866203210710a00080403040805012080501e607540e410b14180d0b00240c07a0701680d900800204060888030300b02c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 327829091 1250 327827841 327827873
    0x9010e1e2701180215090603101a03070f0c060608160810020403020d0b040c090524030a020609040c0903020901080d0206070504030308061c02030a1211010b0a050d0f0c12 75
    0x81100710603002c6800094106000020700820a05c500310000341281010355042d0341014001c15520f1a064210440903507050141101d108007141c4440b40301c1040d54142c91142c401d50f1070703000020945242c265402c03040c2c0401111036070345400380400d80484c1401401b81c001b40b036881b0300c1005800c1c0014281030400ba59000f400080c4144820000740c2d07100c000641c00c45410000c504a81e031224108200405140d4004d80310b01c1d420107080c8000100f02203a00b10111003034191104003141040b08042d00e030045004081d5020109120580c40340c6010f901c02101a5994103009101d03075520b0b03000c105840001d903c1584542c000d00280c001d5142c041c0166030340301da101c0c03612764501400c582d00a40030b050080c1c9141d00440c1c41c01c4d1940c14a014a02c2c0c03405c07d442e0014111481002c05140113003c00e04900e609100081100198441605c41402107440143c0010300c1445d969080200340000281445c1e4107840240b00a107204005c0340040c526440075005a201d12080d02c6c00d02c0c103068001c4007080c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 327830341 1250 327829091 327829093
    0x8060c07060903120e0319030b010c020603060d0b0f0a05060d030504091503050a0c230d02040e0a08040e0f06090702060f0912040605131409010e1e27 66
    0x410040490020000c586900307900c0303039000400d0080c034241240c03090405682c2120061410b00b491030f00100000203444510000f8100750044a0380d41e03011001c1d038a8020394180440c954400900c01441c280e40035541c0030001900100600903a0780360003005140540d048403e40344003505018803200c4d2806841e511440a45140e00c850000341c3c0e00403d0752140d40329260703141c0c0d607980e074a0038803201500381a80219000700446001140d0307030070800d04a4610b446000c1340481103043c0043c0508109002d9452100010201003103d6419000d22024003034030442c3c84014019071034424002443c5030050703c060020081001507034600101500c25590019295510800641c02041001640002c0c140d90040100450313500c40d481c0e100d40345203090070204602c0ca1003032012601040969010000c2c00350303441e2500c0f4001c560f99640301d054080900700c0c043c2c641c00c038142c0c000500a50001d811400e803ca86114590031920380640a2900295410341e4001010f044020088005821062081d00740c0b040200c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 327831591 1250 327830341 327830353
    0x10e0a08070218010e1f0b030a0f0b03010b100806181008190f0f050705040501090e211e0c010c08040605060111070621050921091c02030307052508 65
    0x7040c09944403001400075a08181d4080000b0000800c3c1b14214010b05d007807150315490303051000351080541041344100140358035150034804a860140240e00305000c01420000405007000b101300c075141002003590b03801c12108602031051500c0580d8a5100c0d00c41d0324144481e140c1863301c8141041c1d40b110300480c1060258500b10003140311044649d40041d0f204808001c1c000700e610300241841e0483d03114a611902e04000040d20f21043d0300801c000b4040001034071103803079502500390a00c0b100d100d64600462024071001c0d02e603240000078640388130f503540081410a400801c01c5800d4400300100706000917010020b010811044d40146508038100f42440380701903000c1c680d6603907102e240d84588002c104208000c2c0a90042c080a038000b9580e02d01000d002e41d20703005094640d13506046000325072104509038540100120902528006a03004041041010900c583d0003440500d2040c1039a00d03020400c501c0c000a0010484655101050b03488a07644400b03111082c010540b03c2e51002d070558100c0303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 327832841 1250 327831591 327831599
    0x1060b0f090a060203031b07020f03060f090f070806011419080a12050c1c050d14070905180a0c03020d0e060103020f030109020108040f080405100216230d0203010e0a0807021801 78
    0x1f000c030f8070320341e604410f2509469030001c1c0001901c608203e400340b60903000301340030711949076100c12001303101d094580f0403a048514a4021360355109118820756800b90486001072040d19404060920404002450004c104480c1c060501401009502084d241d50040c0c23185400c00c008a04800a4031110b410034a01f40010048010780703400044640105184c2c1008880e41c0e424041d809680c0d4201c000081000300309244003030203c071800c060b18030101180d24180e001510780780c210b52040844101849030100d644035120302c607024003040c510b403009043e000d0052041e0031040d07106181c48902e00400818a551460040c0100b081c0c0b4892858003a9040c00f10002c0980d030441e4800e5045941b0001c060014681400d0852082c007803a002580e000801e101c0245000d540015031416400070170500e100000e40d03400300081d034015110f0902d00d10340c24540202405107403130148a4501800a4000300d110301180309610700380304a001c0300b110302c2c2d030380811030380194240050481442582042c03101c02c15410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 327834091 1250 327832841 327832861
    0x30905061003050c421b070b13060c020102070e25050a0219020402091906030b040c210f0f1d060403051210030206161b0509010605070501060b0f090a06020303 70
    0x1007400540080c005103800407401c0d60100300c01581c0391806848058464117464400c0100c10406c100c0584507105522010509070181800c07500c01180700041518002d00d450819a0103c8008809074154000c000d40055000d10f11305d1120700c120741740034070350401c51103520369070900408a1080d242001020700c880860981c0015030b0f2a0300c4000320b0300c00d026180c500d200140c040d114001015401c8844400076004039800b102c5154180c95864405000c149502e10a000842d490544100c002800c000030a0000c590030724101d00004030960310114480500d106d03036106a49460240608055a50f83d050241c4464480806d505c5034941c03024101c0c03810191030081170340c0255815402c01c1038403c0c0105a0070001d1643c2c070002154050003480d00d4060310040b1486410342c0d180c03f586c0307490500b131010544d0394800240030242c40c0000d01d002000d07400c042c01110b030740d00810022181c0307660705c100118102e441c0001911100d0720380921155101511008c0c01f41400c09644030388103640c401c0c01400403803e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 327835341 1250 327834091 327834139
    0x501090e06040803011a0903190b0a09050d03020a0c0615080c03071a03070903050a0f020a05100909050703230103140708070504020d060b030403090806060109120210030905061003050c 81
    0xc050085d0450003807110b04500c0c4a48524400198144278804e1451551414241c010324214042c03c940441591203030880d8040d105661001030054106100190303441e030003a805000e002005141140a00c05196904421a032a20802d0440c001c0100c1040080000410041e092060103a0141100910307042c04604030383c1b050f403113001194402000080c07925210341d168400a42d0048100c80c4201c03020f0800b401c1168070440705901890400c131011855043c0a07800c0c6105800b15614070350858640105031000f400d020307210100301034031040c00b01d4541044922064030100c05051080c1503500d18500507960311140c0801d8001c613009401c00300120040840d80380300701c840a490241e50351030b04130a118003c20081d004031240ea0340110502051507441080c5030700341e480a400710f84003030b01c81e01d0064032144610320505214494440700d507801400c04514104041c0c0c07a80c2000728008c0042d43d9414100942144c0c000004100b0b0703030003001071110420420240c1c01c420341d038200d80544080c0c008100d02d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 327836591 1250 327835341 327835349
    0x60109021204021c0c0b0a02060a02070201020606221a030c1c1217090105041211030d020c030d0603080c07090c08060d03020c0a09090201120506062d0d0501090e0604080301 76
    0x82d500c8041650140380c4e8000c1c0031840c1d034010300701c0c08000c1e02c55008000a800c00c80840c1c005105680c0000d252256078402c50741d41d01d405800400c2199144002c0000e00361600c9070034002c811640c0c41c404410401c60160030000d5101050381440c0e905147d0502d4a000031030038a607403040f05000c0c04884214078002800c0341840d080483c81c003c0061558081d201e03000c60300b810142c40440c98003000303140c010641c44140103500c52a80103443d81000030040b100143c03028121241e50300b081000140090701507000340051001d040569080446542e011002c460842c0e005585607600082c10540c5030005002d010090100ca0400304040026418001c2c00c40300001c100c00e02074007200d4200001d1600030058031000f02e80c014800b9041e04c0e1502d0844028010003141280030514401d80081800c01e18040c1510400e8042c041d5401c000d143d011b003845910402802010340350709a4100d07030107100001b00031f11145085c01404269945800c20580465191910505454200e04140000503a081044034112 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 327837841 1250 327836591 327836599
    0x6050304060e0610080c030604030503180c0301020d0501051306030b0708041b060509030f0f210d05130209090102070201020a1214190e010f0203120c040905040c03020306010902120402 81
    0x40d5950303140c1400109014030600e0620b11a0700208070b84070011300c9003c030640707a8090503103000701c0c00700c0b00b45951004c0c1520000c01045081c40001c1080620001051006810f2801c4461440c0f030280441e08990085500301c8072542c40e000103206a040000860403080c102610401c038080c039603242c0309103c11010300034204000002e0045018005107810b20b40d14403000c400c0203e2290368520028260b80d21409401d8003a000d0940c041c0d241c0580450000001a000742c0a44070381c0440b40c101d0003d09002000603032a0b08014040d00ca010111441424410900c280c502129a5560b00400060007070080000f1502d81c01081403c005076408103502820785c0d0300811600c2c05041140080e506100d103403c4400500e000800c1070080c801d48100160705131000b68565202c50901100115117000841a0100c00742c6e000304551001421a400415401881603400f0350400352144080010b503042a84c065031103144100c1d040c0254a000d00c62940105400c410441c90554046908180c0803001000a442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 327839091 1250 327837841 327837847
    0x30e0a120c03050409140a11180d0c080f0c030114150f0303161a0907060f0f0905120f07080c0114030402130903180b0a090306020a120f02040501080c090a0605 70
    0x4143c00350080d00d005d400802020b00552003004075400d070900d800c60305004064105a54404000383c01d40031109074144c1801e60102e00d85011084c8400004001c1c0e04690101c3e85a000050064051045401c2a0002e0f0003402c00f00d05507070105802d4600440c0030104c440d1070001440720f500f01d0380c91024000c010540b460104007405c500000c0c194000d10100d2013881200a010034104426041c11364040d5a10010b200c001d511000000c1e0b40c0e6056034042d4030007003440400d940f02c0d400d000708095401d04020b031a00303000d07594459020440e0501c0d00c01c0c0055007030340144802c035500c0da818001800500100300003050580d070000c0000340040030303601429494080000c00316040d5100c2051001248103030580c00d00c491103140c94002c0610303951003080c501c0d00d002078070007194400600003200c8050140c0da0311000c22905680f01c01000f9031101c964541400042c124421580445002c1c1052402050200680301c0f0324040014158540013821044200c13000c001050780d40e40c0381200b210a0340c2c110710b40252 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 327840341 1250 327839091 327839093
    0x60b1801020106210209160c150b03010903050309100b01080c070215041e0906051324060206161103040905040804030f1203060e042001090306050f0601030e0a120c 72
    0x2004010f107400c4460000020307070400c96418250f480003446144250b5606e9820340e180720003100b048119404d81e41c00100010074080116031400d8034101d680140110004080c18803200103402c580b124082140441d0340801040390344e510a200503801081c0603036080c00050040c500081c202e03a4011300d481070703140c1d000c02e120055403514524084021074000032160758548445003419840050200710308003048502002c0b900d1003a90049030100c404c06005d0507030216400c5040006800b1a084403401440c0c1c16605411200340404258000c103200c1d0041e00c0c140c00d00f0103014145d100000000f03414480500204051018004102ca003100c000354030004a91303e40c0d281840b40c2d0710881d070016200b00c2c0600c0400060001c9030810801d80001c5032410003075541d80e0040440c1f201070403039014000e120f200001190903c024044030b058120145841c0741402c0c0c0b20342c0c1d044100c40d019280d001004c1c0c240700c20051156090312414075040300c040020100007441d565001c244100740c00c520003c2220011441c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 327841591 1250 327840341 327840343
    0x506030901110f0301080d050a0806041e2d0c0516051204031a01150804060e0304080f0312060d0209190603080703020f011505100e120628060b180102 66
    0x1203003a804001c0c0a80e6298040d0f112401c1c2504280240c49041c01605604451107000748110b8036a4812602c81c1203841e52118200700003009082c1e00c1c2ea2814000c0f114240d81400c443c8114904001c8100344068100200540b02065903404850104113500d041c2110074281d80003001d0319103428600308090740340007072413622506010303040c1e124403640900032401004202a15030082c22202c00280f2040300c6070b0361003045684842d0440c1009010a04d00808038020440c6604207410101d10345040320301e06680c84504d039113003010a031220f61643c0c00101d1aa41d4074082d50001c1c54104dc030403180705a08248680000303410000c0580a602003070130703404480c445043c003500303c440219000305105480c0c0640341406034407415100000a0fa9510740414045024114080d41003500e60162101a400503042025298100c40115040d4443c00b18142120401020844503210340c40c0030b000382c03100460020300c52640890306080000c6250030301d20300f4810314104205841d03120780795240c5901105d040c80e00507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 327842841 1250 327841591 327841601
    0x91507020a1d07051602010509010c0203061008011a060327060c030106020d1107090b1c0606150503070203161a091c1b0204021e0a0906170603070506030901 69
    0xe401c450780e400c00003400802c030500c0120842c01e94400704003036070f0b4042d8100d415100d401c120038403900c1841c4119003d54852406030011640c10704018010f648150002403804404480e411180201c009090006036006c3c01041d10340d0840713142c0385c0043c5181d00e000aa060100811400f80d002b65441d80d0280c0c0c4921725845400d0703070480020380b0b180d4100b10489900c0c41e8024019071015208682070040b282e03104400d02d80004e10194083c0c14110f0510442201400303241030801e42c4400304035240311118003030300710ac50320007032242000281e000d1400b0100300d040ba8100004106000003401042030b011f07000720444003a21001e0440c4903880300300c2d1a000034092994810b2400d007030718650401c900c1d0080048c140184400d00460101130b03071403120040340c1800c0d04109080f26820f4a00303a40c1e00608082e0043c00340c0080c4800001401c101c03800f825600c0e85c11403c0240700160700c00404000c81c81c1c105c11010b4010880c020b0403034a0749080000300ba500c83c4c40b4400c050144500000041c0340c10029484 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 327844091 1250 327842841 327842843
    0x809100608030a0806010c030807142203060b090408030a090f15061a070f080a030902060a02010b040f051324150305071205060a09030e09010620070b091507 69
    0x208039058441054990303940040c2c54a2000c01d00385808202c03590f00803241842e003103074141c2d40d91302140e0f5400001c40352410606510900c04009103c6aa02d500040e059000140c044400d00040384e40340d802c1c800e060741c1000032258000c401100070301005c00e09040403668420b15802e00841e400f42c4510307110a8030b1b16003a0340500f880350311401c20480c4400940140086804500400d41046104551600d4500c01c22200404405041203d000010111009401c500c0a54100050601781540120710660320021000005075035650109560b86480c1c071a9180e4107401c120200014034150311a070240500c2440040e00211481e0130040100c41074846e156012590940d0034804100810030840b540c0d501e501040381e0364042c000f00400c1c03280010841c0d00c0c0c60f84c0c0060041c9096114040d06e240106907882044e810441d40031040e146940325101c5180c000c00031551208940088065014414034034801c50f00701581041c01c0421aa02442040e603100d900200d92040d5218440604c00c030040c400d24070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 327845341 1250 327844091 327844123
    0x20c1b0301060e13140a150209040507091d0411090903030405060f070e060c010f1802130b0d200a0311030d030608070b13090e030c060a0e12030408120c03100504110304030809 77
    0x1c80d154487c196006440b00100666080c4000d032202d0310146c0b2020400e000e00d00035a501203404442c8001c00c992090b030058042c260001d50014010003244150b40c4c225441900c80c1d00000c288410040108801d80d809103000445110318140600d0040110720f6800e240c0744105d8002c0b0b0344c1e50242d6429485140c0e5800000710800c080140700090f500400b0101320260301c54503260080c4181210a802042c0724418010103000142042d40d80b00b1001c0ba600e6210344c1150b0310582009800b903112081140041c1d4090400301640b1481c1d001014038000d0558100420181480d0003000a09000600c0d10141d4902031501c41d11071149070510300e41044190b0000c4820f904201c0000070482c00800201074410103402a2501a6909842c08058440141520440790701480c264143c0301c031510080c5410074400e48950b03140101d4106075601c44001030b509113039041e10000501030462501d00301d20006160644080c000c81d907003405c000d82c0900009001034140480302d4005002580280101c00c03b9407c106 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 327846591 1250 327845341 327845363
    0x30904051f082503080304020402030702030c0111030a0c0e03100b010e03070b0301150504150806010e040218030607091a0918010609031a010803160204020c1b0301060e13140a 77
    0x302040b950f59071415094034034040600c2d055003221104810181c26684c01010080c5140c403981c0c00d00c4000d50005100e10114081070045280702d182c02c0c0100030245030f0007143c0c19202d0901e208600b003101c4001d0821000d00c450000c9411043d100070501a0644000040004440700010016200d401218842ca41e05005454002c0b4808200d18059070582e4804038901030344075480e0109850500c110701a914101000c5440c4800907031081007180d501100602d0306032146410140400d060780c224020f4980983c25990026245040410a0b9540580d80b0b04d400180e0700d02d061208100c0091540507155010000600c1d00b8458456110f54540c140e4030070040b940740c2d031b91031200508211aa00048074004034003041400d188003d440824181d43c10980a0340c5050310800d80340301d88a920440491b0015024030940e18410310901c05084000c1d8005031b00008d0846400400d0300315502d136044003410801c042c003481100d050f88010b5110031507201d0101c02d481810140620318020700c0c180d00401d03c001c2c034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 327847841 1250 327846591 327846599
    0x2030d111e01140c0408070920040801021207031a0d1a390306190b0406090512011b05030912030c0d140c090616020d061d0609030904051f 61
    0x551041c1c803402d5010203c81840d4644442c2440f41784558400c16074142c0c081101444080c1880e030004110300e40c007092030304415840000c1e070980c80d0403e40c031801450f5808158540355100384c104480d40102c06150801a10426a070000361014a4122950042c80a044080100415007035803e503002005074105119243c828560b84403c00c503426118400113400340c0302106010312010324103403603402c0c0c140c00d4256a81e50007845400040140c0d0310510650000e00011203e10020007480074129694894404508003824061301c0b1100f41c1602910340e2610202d800812120940018401c03164a4550f5994441840051030200d484940002c40c2ca400820f02c25200010001040c01100c000e00601240e49080403085c084501203d03659141d044c10880010149480c4d00180100131142c04021011280340d00410383e140e40054049540a42c3d44520208010343d8007d05d40c514080074008008500c2c0c1480c00507140c0c014402d030140a1038450700400d10b0030b610a0390002c014411820070802da10b6603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 327849091 1250 327847841 327847843
    0x90b0f0d0b071d0a03030f1b11010f050c03041203050c0102030a0516020604050c04020309010f050f0a0e1f0c050d0c0e100219020609010c390302030d111e 68
    0x4295081000702d8100548688807601d0500000041c610007040c00300c13101d1440d01c1c25150428543c5085007000300c54858000c80c42403000c00c03c1501c501511f10140802c5414001522010f030300c1d00e40c3c405101c818048194078403400012a000c2d12161070070020141c07c185410b5a01b80140c1c0850b09683d4004400c00402c24080e43c842c0d40700b400f11450705c40d00c50409031026615004155400b408540141c0f144001d641026002160408000c0c0000a10000c1e000d100c2e9088403401e803070050014a14800340f007241201800780403c1b5107481c07001307401c0b0089040b503015044114451062609034803410b041e9070480c060020f8407000710151400388081c0604140040101c0207505170244034011030400100020310010740e82c50b07507102c1c522251a14041580800c103990b003188603854100b002c200410400198903004080d00c00c0306006544194104100d000d60260080a2040c294440c0e070034030420141c1c0d03001a072100c3e10115414604504003215841c0c070304100d1030590380721026000540384820020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 327850341 1250 327849091 327849113
    0x190506040b0a140c03030f04080c0708100b03030a0c03030504060b060c011e06061b050109080c070911090109030f15020a170a06030f230a030f030506010e0604090b0f0d 74
    0x1c0d0360700c0601403e10507403070102c0e002d0f801d68000f240d4018000110b43c0c1c0140403405410030f0045031034505142000070203500d09140c03138110070780d50b4100d48455080c00500e800f0b80c52841728200d001d1030800c030590000031300010212001404140e00c0710013140603c03000307500601080d0000fa101721358800502c82000e001c2e003810301042c5180c1f901d0440c010851840c0b445002c055400540e903074401e55018844d08003440b085001e0030342c3c4556a641c03668001841c404004c2450080e01009061142c0c0760001000c1160000122184100801c0041c044241c3e0b200349414203981d403044400c0d501c404035042c00781e1820074064480d4403082c80040e02030042900054464022204810385004503640c0740383c07000c00d81d00d0030711004102c129100c16180c00150b0542d4480c44408030740340741c0744050016000300c034500420b4440a40c0030441c00001403881c1035040c0101d550191007804e000030002c20a41c04120b05201e144255030405075204000031081e40c4107412011f5080c0700519244101c4d62901380340001d58 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 327851591 1250 327850341 327850357
    0x1c1e0f030c02011b08040b2203030f08180606040c02010906060602012705060705070203100c081e0906180c0a030809120f0d05091c03030c140c030405190506040b 71
    0x6a00b4244580c0c80d4003841c4c410042c1c031540840c3c200d00b00381c5000401e142070342001c0b411b0034150101d9500510948032441510700118002e6a070a0100311030404040c021034000f13402000f1114800c0c010341e680000000b61a900210162800a0b41b5400c40348201c0c01802d0500c4014486801d00c0000519181c3c15001344003920840304241c8a110310200e1800b220708010200248281c100c8000100140d001c1c6020b402d0b01340c0040c084e5003005462101d0601116851029035011465601c14411800b2070340302c00019040c2e800003d40543e041600302556150f2005082c026210f000f89a41c0050480a102103016480007400a59005859107005003640d0400201c2c0c9005041c40e444100b1181c60001e440d4604204c0b05c0083c24004401c21003c46076039101c90540d64000d8101d10802020703610700401901c40c1806035500003044112039400501e0100b003203050001110003841000003211011040f42d00320ba808841e916003020141c41c42c181320603501d0744002c2d400720b001b00d40024030b1050700c40109440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 327852841 1250 327851591 327851597
    0xe090f060618040605070507050706080f0703141302010504081504061a011b021c06150509010f0501080a0f05090307150c0503060f040b03100606020601051c1e0f030c0201 75
    0x35903114001d1000003014610001440c20400c1c010030041041d5078003c80e040662403420501e0905240c8a85241007800d038020070000754400200544203070076078105500200c0500d014812040510001190b82102405800303516820481c0002168054400c03100240a107205541c01031101c0d119a00c0001d500701c1c1c0a582072403d004081e00c0c0004c6c1c40e08075a071005070503100d10000280041c1850102c031031580e401c0303030440b44a00700c03007003400781c0949000c9107103120300404130302b41e00c01242c19004d01c1190340c440b41c02003007c0c8005100b60a0701c410711500b541d4084c42c0a080a5403510402400b509200d144001858900818040800303004001040a0307801000c8070740c80007908070000411100f40c3e00c0000002603041c000b0858900d0801d224581d500001003002c60244d90900009007001d001168102125a40f0b050400441d501071204c00c0c014074080719000407420002064101001c5c0c840c3c0020510b43c2505c0b40039494460180c0454074064100940c1e0340303411405d00d4003400c0102d4803041a404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 327854091 1250 327852841 327852853
    0xa03140106030c0e124204020118030203071e0f03030207080d0e0603060d050a021918050910020915030c0301090b1002100c0c0f050a0b011e0312090e090f 68
    0x541c24000e045c22a0810320b0401032122580501c2002d807040211b070103021603452502c030038402c00c1aa072640b1100b05030a221090b001800c040c0f00140601003409c0b20307003103030b4920644104003690f07000c01c10004459080710300341248008101e10320044d91498201610413501408007205042d4001520300030307151007104996004403007200540d80c1c9200030040c079038800001c10000d0080c0c1003580040c2c110501c00c034110380c42503c1903030000d007140441c503840340928030748044104014003e00030790480f00001181c080001b810b1140015854a80c010701002c417030b0740c000070f5509690311100c2c400420902e014026a0300c2e4100321600346055032080c840c07016400d0410318820780390b203003240e00b07035101c5d5103260014035205900170310103005449150160024401c440941101040b0011510703903a030f6100300c00ae8400900c00385044c24100b14180c015034811111450790010514141c8810703070a0b00d80000e0f580b13034032806081c0100e038103450a411008070b1008031002d2008400c1e000880d104a07861718400d07642 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 327855341 1250 327854091 327854117
    0x203131a07030509060906011511061303030b0406060e090c04050603130203010c03060e06090c0c01020d060519030f0809040603080d0b0f060c0a140307020a0e01080d0504030f080a03140106030c 85
    0x2c1c1c0c4034806d4500c0c054542202004001111031004032200400031401c0039881d0010120820b800c01400711444480740021041e04401c0584c5441840320190048404120030303420310400914188034501c40502405031400800c00034404102030301c0c02014001c01c0c450780d92a010111840410300300c80304030b01960801181c0d1205a0103401510b040da908130012907007541c1c41200f04035030060702504940c1c031001e003041003c6100c035003030004028484a081c1c010a00394640030a02c040015016003541d18480003038028400203032110540e002264110007995111904000010003c041e0f661004003803000014141880d0340d030703a801c21034011600b1203c2490650458040c0a294449e101600020760440345042c000038415540f0002840b050104a0b4242025940480c0d1610b40a410148010002c4401004060f40800c40e4001801c1c00707103091801c2500e555280444169545401410810049141c00e0690311a60040210011200d103001c03507035039102400740040401c07011240c0000c295040000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 327856591 1250 327855341 327855343
    0xf02280801090207080306091816030203070f06020607121404030e040f050712150506030c030405070909030923040603060b03010e06060a030f080d020c071404091101030203131a07030509 82
    0x203500c1a00140014a103540780340c10003505030401401080c5410002000c4402700008115428503100d040359603131b280c181140100342c94951240d01110b4007a1a5210500140341d0108102c1c1d008146400d01c442a203003010400e2000d40724400582240300d2980d0100400d055110b004251510002c3c0c0301002180340c0d124050303040e0f07402101c011000c071b40c20344040c0c9402c001592180000b040c25101c80208681c80c1c20000d401030740103943c103614528000c0103000506c031040c8140c500038540c00703a08110034119070307401406890f61441800c03400030703a120312150381d4204800c180c520610000d0081202545918042e402014400e9010380203605c1c0c0240389040e40300015109000342001015200001e10355641c0c1459160403010881c1e0414062000001e001d1075400a440d403100d10302c0142000d14201003c0c1041003a10802440c4103509240da9040840e21a010001e0256020328000da62a134075481200e00c001c180700130042a010351000040701415500403428050074040d5018070075615502c05103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 327857841 1250 327856591 327856597
    0x10b150901020a020906031905030d0b0d03080a0f3e12060d050f120904050c2a0c3105040b072607030c0908060c09040f022808010902 59
    0xa90701680c0f082c0702c0304002d0319050480725441140101125454445d0b88036150a46010307600444055201069505a0030280c2c010000e104900361400003c1c102107031001484034001a041d400b0669407455540181001e50300300b40100c074034082c2d07603d029017081e050003030040d208481c440e0b00c003018001a400d1620300c10303000c403114240003500820305074481200300200c00e081804121040d104089400c03031820300900507114140f0522080f2911448900180800d50780010032030a60400f04018890710070b000710450202240343c5504d103445000921800e20720307110548440726404000a0562860140d40c0208015000c902500007105600920300c03070000e0750800d95004151304d11450004000e503104440300704e5481c040c6034205c20300c0010307c00e00d640c05400c141c9071103001a440f51120300302d543d0800c00d40ba0042000a0003018a8070708079401d0005801103045003481540c0b60172109030002080c0d010340c0c10b05841181c0c210550b0071144610081600030720780308400300b444580009014101c920070303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 327859091 1250 327857841 327857857
    0x6060c0201032d0b0303040f03030903060c051603050919090608011a01050702010503150607060f0b010c0b070f090b0c0706080106022404020d060e0309130501083a02010b15 76
    0x154103d000502801d00c000e0010b20080301e4040c8400c0c440025a00000004c0200031800303030311603400250035424408162a10850308005104040016a6a80c400760306140041601440c001d9210204a0b002400c6654114503180c0009119080070489807ca64044411541003400801c030b280002c0101d4000041c40c9107555000c030720180001c50155000703000466214003d05400c81091114038001400754110004c02d59201c3e42d514100460103800f88564041c1a0003420003140780d584664403d4240d0800401ca84100200040501e00e003034001c0840e007000d0030140418544074400300c0ba5045e52141940328030300028030790000010302e20b800480c0350458130074081d070f905030200c080c045041d480d824054000c9810207500404880840d0b040c0c0306030810500d424001c0c541c0c0705003440410443d030b04540300072810103181c00300400c541d4000254291042d420b201000c01844403914406554074070361b0400d60101d9840000c800400c56065102a11a0b50102c40c40500d82400d60070341c00c1c2034003076038003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 327860341 1250 327859091 327859151
    0xe030705010c080c0f0a06060e040c0b0a0e09130c0b03361c140c100504060e1b0907030504050d030e0c03070b03060a120b010605030402040f06060c020103 68
    0x80280980d52082e4080300742e460207115a140b4050b49441c4040c0342c80744007030035110300d038022040b1780e020490180034070001000921001681420291078007c0d004010313115119019100040001285001d007041055981004004400d185040e038031107041d01c1d07841d24045810710714041e0082034140e1517038150703409001502d607110802c42c00c08424950718110314807450980d900342c900c1c40c481d902c410062003180340c501001d046002c02c071802c00500401c0010701c40f900d4081c8288203400444000180c4107440030b21041e4081010380711410f04100405414885084030f0013050140b04c01503080307104003034011030705a1744414a6600c03548214209c8000b903070020407980005081e40e1b6141d00c690841211848550261074442c624000000d142100940c042c118442011080020030724000b090b4038014902e0440200501d5040e560700306040f00b050003200c06002002c4017150641d21198418054003880c020200040d5032110000b804030040f5407004c03030000e8180003640200030791001e550120741003884 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 327861591 1250 327860341 327860353
    0x80c030c07030903020604030317071b0809040f0603080304050d020a0c1e0504050106110705030106050102032b060b0301050907021515010c0c0b0915090f040207141c0e010e03 77
    0xc449900300d54008102a000c0001418020001d82d54240060004501c03944404e08021000c624400300d61400038002d01c00d22800104020740504d0401075000800c0d072240c407040d81d80c00e00c8800a0024982c0c103e1651420340741103804003c0006a00056004038025411a0103410074aa0704aa0703d04050000401d4444600303130400c014121b10006203054011040464030054640b800b00f411624240d02000c0003c94001c10701800d203100340000d2000d072109034000e10505040c00700103550780c8989140e10b0480c3d04054944071818003400744810740724000050602240c3ea6031a20158550028061284201c1400021400c40c9000041d08421840381d80b0b50092184c1d01c66503006401541e141201703060100c400041c00004158802410107051f515150b181c40d49002030520cc0012080242d01203211010401c001055840c141e607041c200c1e00440d00960741d00c0152409044074450340400d01343c0c0d07110b114100040350f009102000812401c1d0794510303486414101c011128221703142c8803d50141c1080b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 327862841 1250 327861591 327861601
    0x6150603060855081b0a020607080f1b0718050f070305190603050106080f0a03021002071703090606040f2a17040c05130507021c1211090a06080c03 65
    0x51083e4141c2003150b42a075919181005007900ca0f030440b4104440241c40040c44400c104941d1504814000080000f07104426580e030100d1441c0c840c012010740564400b24240046100207011245162409030748008400402c09030283d5034002409171001d030000508010310a00454421180300d103900f500309105030348130701034107070024200503010410914010036407490341e0780c040c0600401940b180000040c45d61503c6070b07040c10628001e112000d9504800c0400c40460340c0040c00c10358400410138010b907078504910301840021030614030500949804020441464008079220b4031400d42a00c0c2400744516041020b01201c00c07510014000855000c070406801280c3c4c152a840000c0030305010035101c00c20780c0410011072086038116580c803180f107824003143c101403003900c000d00c0401e4418045800c24a801035101c05d070b503400b101010b010000480758224481d042d48a60000104002c100e4030044580302130050380000d0400b0b000300308004c00000c1c151b1081008920455520003098115218 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 327864091 1250 327862841 327862933
    0x5011203050d09060f111905030403050301031b17030c060106030e07062613060c05030f04080304050a141617071205010e19030206061516061506030608 67
    0x1203000f05a07811a0384d80c0311202484041d10401c0d840302102c0c202a500c1e1482c120f003180b100141e16850004010342481404002504107055a0549500c40c00112821400c2440c0320042c8580b98042c008029003004d00703103071888000c4000e0501900d8070081d0358003a172300c1d00c00c00d0301501da0a0203021802d070300803101000b403d48a2240401d0740590203100307800020401407010070480c0e00391380d00d80e9254031291050081046070b110700180c00c0f01d5410040d00b1131612559000354010b00030000307000000300100290400c102440784811580d40900300c0803078005586580c59443c800122900008015207001044840308103144503b038800c1030004225403404d0107101c0e4100c002c0100100d9081d9250404452100d006004440d031089041d1a07511516900d401c0c000e04c0c2c078a025100501415a18011040d600401c00c00c031110802d54001d07142480f0f007a454520000c241800c0c0c044955220000b01182003540f58003c401121100c40403501e82103a454415030086900820030001840d0102c41e0307400181d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 327865341 1250 327864091 327864101
    0x803090918010e1005060f0139052e06030c06050901021617071a1b1204030503070b0a020a1d01110f06010302010201061a09040c03141806070e1809210a0305011203050d 74
    0x2708140340d452424a80d0740c0d4a103000e0310b440f00e40f0403513a220809500ca204494002d01c9803e840c0d448184041c921715103038800d4010b80380c055502084400540343d5041d03402005291168504440329141c566528407180340302c245024507401e06c07809260b0000401850102e0222050394402c0c601519144079650400110251004022940e01070407019880054050002c1d20003580940c01541d0b90b408289804240c1d10002450b100724203106000684c06254809013101c8803500c50317845001101034420050310340c61000c4000d10074074414065019203044012a510b4101c91003a0000d01c04545c90780440d4400090010000c140940c0c01d04c031940303140c03070f142d08040c0750300300c90342400105106035a03e40d15901c0c0c400c8802d04950501c9210440a072a0104641a030014140c50134002d203102130000140441041065081045214004102c402c0070070704c00c440022802080c1c10700d485941554011481d0007016080c80441d18003000098014051503144074074503815910306142500b82c0f016000108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 327866591 1250 327865341 327865427
    0x1c0507020f030304120e0a180c050f0a0c05010b030c01080f07092d05040c17060a05040504050f19020121060e090703050105010803090918010e1005060f01 68
    0x312508049038006201403004601450041170b0b810748815240c0d4015160760100b030310310390250500240400541351003821002e4a0103801c140483c4a424054044825010f011010030452000040030384903903801040e03050149100f18004e218032000601003648540055101602003154400003843c4283d0b1a19440c0c0c0c031591504181d40d0298880721480b4410784800034800e000d40c98203484400c826101c5000000504003250309014110030307030500820841d810007001c40710103602004680c00d07654112602d40500302c0901308101d1441c080c1450360f583c16203161440e80500030b001c24080d4011403000c0c0241c800740c0603100c207011340d10030303440380c003034201444030303492801d40e641e44001c650000e1205685000b000420000d00303285085081c6582120300c180c0c4401174541c0104010a641d440364503126074030502090b50b030b040d401d00e0148001d025169684180f2882e00681110002a0026038002d0b07015600c00e40708408507000b8807005688400100b420440c82c0c10408100d15080000b00d030450b2218 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 327867841 1250 327866591 327866593
    0x9050402030c0a2a1a0f01081020130e090a0c1208070f0b090706090e0106030b0a0f2411060406051b120403020c27060a33051c050702 59
    0x1139041071602403090080c02040b6410404c840382c0c100c004130480c01e400c0d0024117007103000c1e6040d403400b0306c1c0c0703941e0f2002c03c01c100a20a440e604103071100d20003850f8a94556a482070703002d42d6401c03030071050381500c459401041412100000428641040000c0b400090307581f1034072411009090860341303450744040c03420495504404010f00c80001d490208205a19845140e00d182c150406140c0a4109800798120208000d0285c0b41041040c548a400718111845414001090844d203030100300c0c00511074200c0881020305d46800a0000403128040070f02c6002c1c2d260714101481c0030541105c0b40c1058801600b22a4032000110340400d070503900058000910101c1440c1c9200403e100c83d10a41002c000319200d000321408101c2807507010301420098440458115005001401245007082800e05000808000100020f0587c3e1030785546640070b000035064840101c4060341700b900c0c180d003200850925030b5190340e01d82c008860091054400140c02d058401c001100140c0c030b14002030800400700821 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 327869091 1250 327867841 327867887
    0x115060c06022a0c13090507031403040e070207050a0504020f07030815150904050a090c06081504020f0a11010b010e0405040221061006050307170a062409050402030c0a 74
    0x9510581d00780d0034403d031401e400b401001c1c01e18010000368142038941144024245854400043c401003128801e49500060450803850840c0a05d407071030003182c0241e1408500340c0b0520024540004d0782d401260812a190503041342c43d01300340403e0f40a0050000307000c01d018450440040e0140000950082121400d1280d002a80700000d545005034a24000c4556000031503040c03a003814021564000039240b010f020561079943d80e0b41c4003641c2c0e44140420001000d0100e030328401c4d6182010b26002d0010015501c4805000090140f64004040d5030003054190000e00c802e003206006040c88204140c44c1c0c00c015910078030501000d05001007040740e10440314100b621080d840740c400340c0c04d0343d80f01c040100740d01d107000c8e4100b2404c180a43c0210060120600400c02d10342c0d400089000140e400703600c011441d4545000d040c0c050165a00300b80c0222540540718440410020307103c60310760286035100d0b036150f9030314030600c0100d110a8410b00030b4864204401e190300350048003100c4d4413040740200304c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 327870341 1250 327869091 327869137
    0x11190b0c150a02040e09060103080f071e03080105100e01021905010f0c0306030203070b090f01050a0315060f020c0111030d02250507090b01050c060403030b0307030c090e0115060c0602 81
    0x78041c080b40c0602c0916030124050041004003144160310580c0c0c8401001594199110f0700c1850040303005d050008500040c6000412541502c1c00001069503841c8203190300d19890007400e5202c007401428040c0449442c00844240315041c202005841a0080c00e903030325085541c48000002030009550a649800084011141c0da100e402e1922041e590006070444c15441054103090150b4003d201c011820b10480c101030380c4020103940e07490000d00b002d41d0b645015407020b8010f23049094145410325503a240008655800025040d5103400759400d481011901d10010344400619408140e1281d00611a401250640713900038095000110103165900700c0610030100c1e0380d4040d24007261150405c54082007421540d0081300c013001003d003002418031400800156a41e90010009000c06407030b806075000da40c505101180c05107810000e0800e00545401000c40608140340851110707612b8000300402c54240c0070a250290341c5580d48403164103000303845020281d0041d400e5004ac00601c4074142c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 327871591 1250 327870341 327870373
    0x30e010c09060f050f031f050307030b0c180618010f111e0102040b0c01060608010f05010c0b1b0d02070b06030303010806160905100e0301060608010f0303200a0b010311190b0c 77
    0x5032007010450484004000000c2001c014050140e08c482d0280c1c2c06448240005443c4c40b0802e0380c0000001c4080c0e4944801d200340327501c080e00c05608960022400180300f0418580b8041c5581d07c07100a0722208030341c00c0d0142c001c903500f000200e40d41e030880d0041b000c80038030038284d0007125000c03685040001d420580c48400040700d17a4490014480c6985d03503031b04100034181d000502c107030040411031918420b2926040010780110040d400081800d00303860002420400528068000192180c42e0503440d08544840b1030003d61000d9070941da0019400300040329858000304890585000c0800f0b04000d89071154000320302000300440700c041c081740d44004511603d030710260102d403212559645a0000420040c142102d1503600184200001c000051040c4046d07000c02000322a410f1904070a100c0c1c0d000e0200e86880412059105903000d142c1101050026440b00d4505803070142040c219015003001c10002c894594003810a2119400107003046000d01d050094076040d41c4a030305540b44811500c1c400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 327872841 1250 327871591 327871597
    0x30f0c0f060504080105011505040519080601060908060a0c050a050a17130b060d08040501120902090f1b03070c140f0a030221040b0d021c0f0c030e010c09060f050f 72
    0x7400c002000400d040140484c00d0080070300400b041d001d80d0b4007a10801070300400d0751240d801030500a580d02003030311000325404d4050000410540050b15102e58540000070075800c458031603200d2522814011810b40c0c0a075118075800203445403503031440e02000150540b07094003c1c900d19000e11080f1218000007204403070b402c40c402c491080102c44074403081e141050015501625480c01030902111450019040e5012074007994000d09011102032240c4120001418813584001c0d080201d032824441003c024803411405a00005854400e443d5607400703481c400d010848800f00001c42500d01301001c5814144a045404030142c10f484060500111492410b01403010440060f03014410200c02007051050518655038140700541c40e241c500580b804d014003542081e00c0c109580000d0005800b00010507101456440c01c0341440201200c00c44d41000708a0b906500d400b00741001442d48424006101d100540d6682c0d4480707002e2581040004c8a0032004c080c0c2c844140403041040c5064a00703101c5c0a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 327874091 1250 327872841 327872849
    0xa17060310091b08010b0103063606050d0c0302010e01051e0307031409070303090b040f03080c03070507321e04020c1e070602010615080c1606050a0509070807030f0c0f 74
    0x41410780c0340c06c0006088510a9208202d030302c100d152800340c1090010980c0c030880c01c00750200c032599214505541c00829241d400b66510003c40301e01401000074030f041607404c603030007600e840441c01d071000019a040d21808210201790036a800c03c002200031020051345c0c200d40d00d40b4000540003000c0300b0103131240c5000c1c0da044d80b0307540c0034907020004c266100700e5140c0074080c06500b240c245490030300d511000c1c07482804001d011040200d0600e2440c9000c00a54800b9504141103519090f40d880901c1c2080200c0c2905240464043c000f06804101c4e040d01c0061020700138120710071014002c075081c0c0d0032540c595a40350f4415020040710800761010000e0360390107110701004900002c4110310251401c03400b94411020340e414501c04102c4070b143e01c500310318119903905111680d40c0d101b0b103034407225124250450b25400c4000c0104020b109066108620408840208200e2915244049980ca40c160710600d505540207400c14000190f491810885061048c12015002510303640380c010003044c1500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 327875341 1250 327874091 327874093
    0x415030504021e0f1e030706050706060801090f1209030b0901060e160c0f030c0507090204090b0f030304090c090308030702011b09031112030c010c050a17060310091b08 74
    0x3400194a0900d90740f820380c00038032124000d4000000c003c500581240aa560b1007805041100510b8401041c4a041008002400c5d50102038031844003600d29040440c0640d81f8070b00d040e80c00b20700040c0501c500350070540c0044910742030b0003280c0d440c8005c03034031040354280400c0074614002001454042c2914010100d1900115907941800b03910a14504000e02080b030201400b545000c884d50445103940310141c0140b94100005d00e0307810140d035441c1010000030b10b644590702000030107010550142064ae01108003c2c000c5500803010041180c219103a400e5058004100410550102e68403412214096090505140c0d6aa45581505801c1100d10101507516103c0541c044403014040150031029420682e0856045840300c4003500107044030180200b500020880300d640c8100250381c01442200028440400054002855500b00b4104035000c101d000071100303241d007100d40b0700700c1c4070704000340c000c14040f15003c0c1140060503d042c400d80b2180c0e044600c0d081121126940079010301310b508 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 327876591 1250 327875341 327875351
    0x3020316151d0d030203040f142503031412070f20030702181b03060f0409051605060a05030606130b030a02091504060c2004091a0a0c1211041503 64
    0x500a181400d0500e03102104052042080000082407410488c10f040d41150884d40c05c170704080c0d559032514040c0b00d410008101d01d40d001500320a15403803040c0941e440307035a52600f801804501c1d48014007511012011898044001034a09841390032110800d40f014a07214211204101134507488810318240101290400210401581003c2d0b1807080d4403554010b100c9440d00d800394018040102c060a0b44822100000105149030b455201c1010340c00030041040200d080713a45003450ba11680c42200459070a44504002840c0c40c0100a4400304010768075414038559401c420041a6440075000d0f21424000c5040810024070761005144a003544410042c0c0d40c281c20801c1080591881c1014014000104418001e5691002e40c00c94030550003080c0302ca0700000c003071100803803000c168045900702d0300c0c1002c40b41c00e1105240c1c1600202074011104140ba84074404188242c03403e000e00c810114288000380243c01e801a8040288001c0c00070b5407906142d1660820283c3e0904803c0c1c0c2000a6119 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 327877697 1106 327876591 327876641
    0x328090b010e040303050a18020f060d020f03090c0d0c0b09040608030d090b15030d050c100515131a01030207060b03070603020703090608040302031615 67
    0x318051420399a11090001944401150150006414507010844000321403041e0201b00421140c4429011159000e000181201a900340d4000d00c0400c040c03c2d40050b584086c029050341d13a00041d540382480e9810342d1920410b500f00034805c8aa00c0c0c85040052070850702407044070062420341e038031191190000b42c010510ba07070003049103000001d100d142c3c00c40d050340800d040c240710b06440e030001c0d117422111512007081c000600e90103a00040c0f260b10000c0c040c0340a007171700d442c0080449a500d81d250011a080c0c420903038100c440c080002016240c3c514250b0801040201c201004000da02c4039601840c0f15060903012950500d940010040144107081e004040c02001c068101c0340007581d0307080004e00942c400b44040c1d0018000b01d20100d406481080c0c4140641c2d0580d00940c14a000e00c031554003800319464084460740040030882c1e54408290150014161080310441c80b203040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 327697841 327877697 := by
  have h0 := BRFrame.cov_init 327697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 327697841 ≤ n) (h2 : n < 327877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
