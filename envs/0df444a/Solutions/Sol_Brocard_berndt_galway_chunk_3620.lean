-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3620
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:44.4941+00:00
-- url     : https://prove2.me/submissions/7e177f47-03f2-4c67-ae21-a25d484a3ae7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 650899280 ≤ n < 651079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 650900530 1250 650899280 650899289
    0x30c010522060906170f011502010902030604060501050a38071a060310050603070b0a02123702061f030b04081b0703082203061406010305090a0b1f 65
    0x12400e02921400090f0540342a801003500046240c0080c00d4107500c2c41c00350501604003403040090036400c00d00030f548440c9a40780c41ea4159900d80c604000162000c00505218600400c4c002030b055040500700f10000d1441d40c4410754040604200200c02c980d070112103c500b804103024412003102c410b000d01403c2c01041c20191140c0310310450342d0300c8440301040c440d01c224011010f942d030614103001c0d9101202c105803a0580c0607409420305000b8035421000030034400072180112910f0070000b000c0400d10f03512004065800d1005100441820302d10340c50080e10b00341d0b1030341c4644070003420308100035036074000148030010512541e52921145111000004061604002d10b8115490903051001c3c03903600005e000e941d020410b6400107500741c0c0204010094903800303103045241016203031032000e18501582c1c030f8600317410f00400e00100150592060003a452080c85010a0910b481c4001400b01c1d940180b822120b90071408106000440c0e1910155008100c1005c651041e21032a10f5502c201c42c2c290403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 650901780 1250 650900530 650900587
    0xa0503072313180204080c0d0516060504081504031b060b06040b0705210a0f09091d10050118020c030d1811010c02090118150909110609030c0105 64
    0xc400c2c403607204401e00c810903200100342d2288014908400e4030708a100d248030b1038800342c0042d0000803441c5811802e0f4885127002d401118018181d110111080340d0442d40b149000c80c600050400502e40203020011700785003001842245880d0948000d0807020720350b620411642d480301020f01c20014203a118100030308000d0201a1030b507403102401d6020743d1006c10107403600e101d030003038035284060003800d140200b542e012a0541402c0c0c00305c0c4140c4407441c5c0d401c948814403d82c003001140c0044588142c010902410031002c10f5042c0c1c0c520050708050185098800540c106030042c490382e030003048945907940c9207000050f035401305640c9540c02c500601c00007102c041d040480c1d1207030b09000c03c0313031541c00d46005a040003a60340d46203005442c4030000c0c000082d0400c0c1024010040540ca80403070744519002100003056092000101d0380310b1a070340b80c01407014555668000e4050140c4089007905210080d1000c1d440d05006400081e952910610018108540040c1e1040c0d1199112000b0504840c00708 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 650903030 1250 650901780 650901787
    0x19060f06090e09190201050d0e0a080a03051e07050c07030b010e0f09030702210a0b09070f050d0c0314191101080a02090108180f0f100507050a05030723 67
    0x40018408000751003441503000c0d48001054400a000c20304030840325800364000d80c000c1c40c682c010f6640d900b15604c4003c030705903280609034508405200c120303200352141d8062966400020382c042c0484801034501461402c0802c1c85000e800d12604c2d44a4200501e400c1090322040c4088040789060101d400c000c001150342d8000081c1e413145603044601450405190308001c0d03547c1c10026a4a006085002e035000441d08600054261054400c90400348020280d40600c849a1198020703081d00b6102903015031702002081006042c20b03050f801c0642400ca42d8600a4849a201c030011003099010243c0b02e40e0070000d188400041c00c001c41800c02d0014a544100024030341040d0540a021220160110320042d000400b2042c6901c2220b61900c03050712944038a8680e80602c81000c102440d00340002d00c80d0844400b01d4180c100700c88048511524002c104001d0140d40741c10070750b2401b400704020f04c030040c4094000140c001c010769600901e54501040703d1501562101e100c3d41c1c0b03164000d841e140001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 650904280 1250 650903030 650903039
    0x1b030a06170f07120b04032318090702160902030901020910170a02071a040203071e1505030c0711030a06141b090a14210d1e050319060f 60
    0x40307501d411201c0c2d502e007601d5049a4954030100031440d00e40c0010101241c03240024000390050000c030054103070030006040801051060068194085861141d10307e69010f40c804961419440040d8068154806800004202900c1c070002a00718000c011800e5004800103003111801d6050ba04010401081a6030008080b0400b8120020300002400203180307010018215800e1402241d0740c040d40302817169000480c00750b252071420740150007242d0500901500040e000c2c0c1c1014400c0303a0541017020500514903007d000c0b19180580001d04050040074010023880d806070a00f5984100c0c0c0019415441c0b00000300001d0400b00710240082459280c036400a5411801c000390500c200003000c0e11201c0715a0066003039820303000b40e010456200103007039400d0101d450b0050806501d0b04016000395400d1116030910841060b01c1503100d411644140040101e00b07622100d80841052407030b65084011410349001001071200518844100705078008541d9070381c1080d4812002040c00c1c47d004660940c44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 650905530 1250 650904280 650904283
    0x21e1c050408130609090e0c130e100c1710060c020d1e0f140f070510050d14091209061e07060c1d180103020405060a0e040303021c051b030a0617 64
    0x10303409502c91b8185454402c3c10038440000c1d400609074801440b4002d0100ca40b06180098040042e00c0c0c9d00c54051a50001814241806074070100c5001e82c0710450701590300115070010040041002c2c0c5074000c0742004001040e001a82040d1494065643d4143d120751402c1810f19808041c00d003844081d0728801c0c86041c0075464441d0b484581c880c6c0c030300110304542c00b032002c0d035101c8009030120081d801c1401e0401c840d20340508040e40038503041c10110700300b41c582c2c00104201c50004144000050f141410030180c0d0005001c017800302d1242013907442c14a0010300c04a9014000c9240b200c4544c0345480040001140c080240d801056101105100402d0340d0384008060703501002d80c4843c012110031a80702c00345441080d43e0341c042046541107146030b20310b8081202030400980700342e405c0340c10032a01017000540c21801e03500c0345020751401369481d0b6440240380140071007400031004503440c0c00c062051800c1d0b60840c0c40c1c0c0c81e1074400d400c10703100e0700c40c000c07503400130320882d485212007021b2040401c0b50080d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 650906780 1250 650905530 650905547
    0x801020910020a0c060822050d0809060708040b04060b030a1208011403250510090303120b0603190b03010c02071d01031a0a0b13021e1c0504081306 65
    0x40c103035a51604848803040680e900d02103100b004040d188000302c1071104d01d2040c0d8203141e01c0000c8260103c644601c071b900d802100f0003290800d950b40e8100290110030b0030b4220103900c1e00700203503000812a5241c1a903006090100181008143c810300384045014400140c00050803400e0040c00d482d07240c0c255280001c3c211580341c50a00100d01c849000003184104100f04000001c4094094002101c074401c24540910071031909400307800d4412004a900d48075031801103007140207500e440c1c84942c20750801a2110f442c3c61541c802c528105810001d013500d41c001a039410460003d00104c010404003400c10150a802c24219015071801035040d003002c1d40040d80c40d0840380c01d4410800a030709a1500c81c1c8000009000c098860b0518081c7e4143e003000d025401030f844040440001500e200340c20029004401c15084c0403213698011030b60074002c0b1458a14003145001c8214041c1c40e010004594000f801c4d80c0d4030704132030307420790344d40c005030900c0199001c070b808501802a029101c5034039244c001d0038100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 650908030 1250 650906780 650906797
    0x180b070204050f010602030d0b0312070c080c030a030e0f181f1d0f13060204030305122401030b0a050406060201061a0705060c090d14010b1c080f22080102 68
    0x50900c1e01080d43c00f86401d0149058952503070103149050a5404000b0280c401c0300052a0540303e02c2c42003900700702c0f00c0000350403003a118800104c20246040d115604c0c0a403107040e103911903003260b1003800001b41c00c0070100442120a0324050b07500ca070201c001034144041e1a0b89002c44158000130047c030940d08486542014460720a5034803690b4036090440c47c1240013050070802d03482d03000041411503008024071907000f6220701c240010a10540e41d400d090340c219074011808100d010505e04071a40c0c3e080c0c1455448424039400702c420412240760310b40a80c0205000d2414035940f624600d590340c40301280031028100103401849000c1e070344c8100a00a0080d449280303000d01e81c000d0756400b10403142c012202400d802034010069520750301c12158665201c0c0019079482203c0e81300d07a00001d91402c984542c240030550000605800d0700041c00082c6800e540f550304107080840311500010320400036203010050316066903480d40c41d60341e80320700a6415041880c3c94030007010800180c00c51305400404401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 650909280 1250 650908030 650908039
    0x6080a020904112809060b0f0306030304150309201807020c03070f0806061c03050307030212090f0c010f3e0105061305010b0d09020f1c1a07120c180b0702 68
    0xc2c0d550303000805c01c4a10318000c160b82014100142c800420340030016540119000b0b090708d280c95a941d2003010b01e040103210900100e5140c00c0600c00f03101a41d100b000740300341c100106103031580c2c040e80042c508031402001001c0d0958a00c010030110751013040840b00b003444c090b00b01c80c00c640d00d6201c1005164164415091f45d0301ca42c2000a0362070406240d04e94240001912807880e0079a1030740c09070713041c0d000203040d902019428003007800070403026a0b16a00901004d8090440748202c01d001c05c0c2840405a03c89052061400c6950712980d44140300604074440b1000800107001091101c24540004a01b44506520301480d10745181e0419400315020340070480c3c2088151052040082c03d4510034481c0c0c60940101b8041d00182480b15005103807840e200030644001c4401d00c000048c42081c64580504640400d80c90312400c1003c2c3c8003c0d08014008420064187c0c0b034040301c02071141e01890300c2c110702070b030f15000804401d034000d62209032070500c0d003c6020b10b0103403951a4445284c100700b8090340b18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 650910530 1250 650909280 650909359
    0x15030807060f020a3f0b2e0c05030f0307021b0328060b060409020711030606030613030228031b081b070b030a02030708070306080a02090411 62
    0x200c81d101c3c0308681c40011982c541e440301810560441d00314060515120024500c0c200c100c404044044c0e81203800c0088078039000507460064000e00550140d0800c80400c0341c401c0403e4180d0582405594400000061030301c00750140384d5141080c198018400110b0913800084144034060703401103448001a000b8240c5441c4081c1c4100c10590b030780c001c01035090001d480c060078a852107000c0c200301c0a1001d01494010070382082d5040403500561041e404000ca03264049010b00c1040440146503420031000c800402080c10000c2c002030300c51710007a0140c00000c1401d91050300300750080c8100032605466400d4582000c01040d940c1c3e03152071041400f140016800703244482c1c0360703651a2965604542100c1d025040008441d1020b0340d0b03901101c0480c509100302000010340c69072910045208002c02c940140c0c8906041601030702d1000047d1034070301858101702d41407040c0074002948100d0660100c2e90724480751290f092602c01604046000c54200b0030a00d000c0a005100700030529400c1051040d0045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 650911780 1250 650910530 650910551
    0x10c090311183139090203070c0f061b0801030507060e130501060c020906040c021b01020f01020708040302120a0305030406180f110306011703030c0a170a060503070f080d0c03031503080706 83
    0x61140d08400c544000408802060000c1d0000e680910381c03216490500009c08a00c40d158825502209103007180e0300d03601c1e01c140041d0b40c1340589441040d0b1005061001303040d411903a41a456804070b0017100700b0080010700c2c21040da594074407c00e068030502d040c1000196100d03030340240088048102a40500d2a1b040450031b582000c1c4220075080c0300940c0500b28500c148140d401c100015081058114410402c046c03914110a2006040c024410003c0d59a0b0307038610b03c14440303864500b05081c6015002061610082a08001141e9020742e1201e0001004000744070304244070016220054000c09000c105001041030456080340c241000710201c410a0ba070f00c03903c02425043c0c0d0040341e03000340c1060001c10101f044400103045d00c42c00c1800d1030031180c2c5c40000c0600c28410200c13690720105407141410405030400b403100102a08801040c2c0020038188029035558a030240d00b00c0d4100441c8600308814180311f6801407405807445d40c06101007070758034141000960003c07001624400e140c603640d4034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 650913030 1250 650911780 650911853
    0x1401020903010c0518010e060408070603140c040e0a020d110301090e01050c09100810080303100f0504051e0402180a090309050a030203060412030e010c0903111831 72
    0x1140084440c043c3c42c40710b4005c000441d0f10080448800790030403824400843d00f8001408080050700303240e5000500300030f2a459000d5540005411500002c004000c140052211000329a03408220306601507911050908080c000709116180002c6031b0001000108000791940c126034680c51140d0000d2003192140402d44011784a4141d52580c0003214601d00d10151380119100c036400b0088001d07411055075070324815030460f0310848d8003599202103440c060000c0d81d010070100c0040c2500b6141000765241c458150f41d20008407502145205c101a03001070f04550b074045488403c8000d61007194128200421607a02402880c00d049011800c103010200701810400405030807242c00500828080e01c0740c2d200d000d86402400a080105600c0d01c0000c840354509029200520615540d0300b04410b14609285c200304205014641c07080304101850341c83c035069002034982103040c10307090020001d8100d20200e1200d0384144440706482c1e0703512a0200340620041d5600b400324940c01300c0326104000403600f5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 650914280 1250 650913030 650913037
    0x2001060b0324031b03010b03010903020109030207062c0d1223070503041205070f0f0501030e0c0d1b050433030512070f0b090f010b010504030507030b040f1401020903010c05 76
    0x390f4165000740344040840c1011041d685040f00301800000e00d003600d0001182c250b4990b08020750151b919100d004c1c0400d80c0c1080307404010521440c1505102900344040b1014680004010261030b21442900c0f0060b6500c0310324851441d40280c00d85142c000c480741c050480681e00458100340140340b2030031540c2c07401c1c40049595040c0e020b0f018510b014100203850464200401f400e40d450f20413440042142030424a1880240082200c00521646800c00040541d016980002c480f5041101c00c0352143d11501c0c4000c10184e8090020451034284400c044101e040c2c950000741d00074148101c05803001c21020044d00707000d11202c1030501014000c08540c40107807003888024501d90084800300f4103035080b034010f041c116201d1004004403000f070743c44069032a0001c0e5036a0115403c02d03600c00c0801e81d4244100d44503030500b800c082d400c0c01e00d103495440d00d5624920018000380c1c0301c2e0002404207d01c0203640400b83c0c0e40001c0e03820b66000003441c07050007074028021031130081d8608800e4148150080003034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 650915530 1250 650914280 650914351
    0x618010201060510080f180a0515130b1314070b07120e0a030308060402040b3702030901200316030801091401051309140c09010f12032001060b03 64
    0x34401c264035a0880020340507001032452a07048941c0907e200001000e004940155004900500c50700c2c1ca40c14802c880b94802616103041e925424000f00c00107150011181d91240c1c4000070140c61001a0810a032040c1640030280c446002d0940080340c0d03414482c024005842c041ca500e90300d1400b96020580b4180030f43d8a50b107501601c41c2d4070800c0082e2050070402c2c1d2060014101508142d5101003411041e0011191280f020b145a00243d81295810b158180385520f02c1a2a8840810407003010751207115009001d4104000ca50b40402120350802114000e010b40c142200d40d590301c800700f66610747c0340c0c100d402ca0010703a0100000840d01d10600410403400d16040c48181103918180c108120500c6803070502c0c80403521101042c0c0450f0007600c42240382c400f9000903114511000080101d406816044031003d1582503000340701550b0000c001c1c1d4189945403c040a40e11018100d100340c580300d091008240e582000c0c0003069051542010718010390135181c84910070084e201d884012448448003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 650916780 1250 650915530 650915537
    0x8040807060806271911030414120901030c0201180c060f021203010603180f03031505011103030f0603191b0b0a17100f08030406170f0615090618010201060510 70
    0xa5513200740d0325000064210000c0840e000042142d14419400e07540320200700441e100d400300030030062140e0b1000c500d030ba040482d009810b0003603e4400182c65030003a11780c4941010f907a101d801c0f520500035401552582c072480146810031450385084400c9d0710050040c10009049802001c200741c2c000101100030301c650b055220709681c203016044000300140640c41c1108440e43c038680340170403040182840c040b4001e59020a003010a0b0000d91044015075014504011100d401c291010340d001c000d44e0b03002508510860030a44132803000074503040c8008158000c9400026001c01004203d4021258405080000000c540d940e105c8000150041d4030a10000c10f1080d10204c580b241c0e45c84d0b0803a03210466072414604035407900c0c0075504000154200a41c541c1c00003c0900c940e40d04882c0b241c0011005120544d42850f20b0120f010386031321b010b8080d9000c4c20103a021036074000445001e5410803000075148580340c5403801702403000304030a801564055481c0040206160525403040707845004d80f602e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 650918030 1250 650916780 650916829
    0xa09050d0204021207020709110906160c080609010e010b09010302131e1a03010b03210a0903140319050c03072621060603150f010c08040807060806 65
    0x418040c40300d104990880e8030550030040e480100b203912911500401c42a4001c1c80464200503078981202d81034071640c49210710600c0402170f41e40c2d03503401311002d0752210304d0740c245014820701c0c00851100f0b241c1c01031a61030155200b002038003c0c05500041c0c05d0f01e40039009020b030003151000c2c0301c0100002e0001a40143c3e903418800291040b540081c00001e035014100050001040d035240c0443c0c517001e810800210106210160380e00c0c007400380b5a03580c0d9040300a80f25185803040c42c5480704030442e60b130180000011030540107490240c5c49010085801450200c0d5000c00503020135202d50205183c10304100210462101c954416801d07503210082e910011460700c0301c90303243c01c05200960701950b030868221083d50a1004080c201030300411a84800c8010010705e4403000ca1040c03500140010700034141070040207040e100c2c2521100407a10181d40c0f80c2024028800100c0301c90764034050140035903070000790004400d800015a20211091551102c030240c948800304098840700c2d880300c11303c000510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 650919280 1250 650918030 650918039
    0x3070329010507030e030d0e010201060b0a050715021c02040302030d3b030703081c0207120c020d0b04110f06090f01031e050c0414040e0d030203150a031401110a09 72
    0x2c0e001048068001c1c00c10f0300f040150301d40044d10b0580205075640000312000450b014658090090300c000d403d0b00811641400c18810b0300a01500400c680078080361540804d410800f10f00740d040b15000014403940080d84e0b0601c012820182d84030340f208070b0013403203041d0400c010544101a110742884083c1e050440c021300c1d400210701084040c184d10460700500506240f0941e0341001108020352140c03800300d40318118440301001030a070a002604440b0300403c000b0000a82c0c01d0103016504a0a040071003138039019001140e802d41036858002c100c0d49410302808203100c00c0342d50482c0300c00000c41d8006002c81c45101801464061040040e0704401000300c201c043c0e42c002c0c1c0008001b0040c0700b00098020030000c0080c41603500540f80321982510000d014403000245812440e4045000d0307a0a01600100d602440d560700d011065490415034040045015404016104410f400001f002080100d460381004655111510300d01e45003507207030500b05051880c440060300c000c0b04d8262281d5000c40c4c0381 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 650920530 1250 650919280 650919287
    0x30c06020307030e0f0301060905090d0f021606030c1e030f0c0c02062a0a120e0909100c02070b07030306092307050a0302070f0b060901050105030c1e0f030c0307032901 74
    0x1450300f203546c10f5407100340c04101e8501c5446203a2103141c40300007c206d01070343e005000d00001002e822640c01c5400c4216100694030803461200202d41c56440c0020300311442c890101c0d00081d840104907400c55050540c0481141d16030001d120b0307562070000411607218214400e607000c02e0001e070020f40000c0d00b0320110602203c0304546034a40340c500440442001096200b860600ca0390100c211091415002005880342d40114010100202510182143d0515001c01aa2601000010a882030301c46d1042a000c1d4403d1001200500220541e60f03100d43c03103854068003426150107542d06562620000c3c50903d0140301144100d1385890f56409085c2d11602000c58141d4030540c1000203164003080030341c000450f502c0402e40c106000e04000c1c3c4050500c0420812040c0040c2d100c00e04202044c0103002100070064121000d5001c03404080c1050080d064845480303020307882601065010100030030400d00c0e4180300943c410840364be0208a0210302c04c00b0301c14a110190545100d485074441d000655502 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 650921780 1250 650920530 650920549
    0x7020a0213060f1d07030203010e04060b040e0610081b01050712030902060721142d0a0e0a0603060b0f0307050747040210050c070b0301030c06020307030e 68
    0x1003416022070b0058403803030100d519041c43e62160042c10581407102040101a58086802070b1440c0342c25403641d40350050361041c4000242010344220b940d11442c1da4555a940d010140c60801ca00a84000345483c580c2401a403001f44a20310403030150b0703001084501c80201a00c0703c9290142c45403410145940c4401d900054850030040a01d0394900c510800350392400051300326a4810800240b10002030400340e00e044514031003c0080c403101031942c0001c82200b005a4242032110f100c403002c400da03040c088007ca08035507000a401c00800040d0245d165034810000001f0b031030705031420001c480d0740340c2007103044030418852500f00c5e2005001a0000f04411002181c001c00f01d454500c1c00c10809849440c03980101e0789005440c0d12180d480c103e5104055043c829010703108040a00000350340200d80d031034401d001000248942d1440311341aa07070500800607a12000e411038203c0f0107490b15098000d00c20340c000e00050743c058048401c0058417510000032540c0042e07060f039484188e010b20006000c4103a9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 650923030 1250 650921780 650921809
    0x80a0c09020a1101020304080d0c080f220209160e061309111902060609100b0f1605102703020309151605012906550807020a02 56
    0x80100c9442c3c0260b10240040c502603070250b01a19900c1c02404185400c07512000814420302c203151041082044041044a40c498002040c043c0c4c140010316141c0c0b0341c01d10300f07500250700c02070035000d100e11003034850010400072080762524020300f44000e0070000d4070b0280c122100ca00807004a800d01062001d43c00c0166407405005085003404112100260740400c42246000180d03c190100202c601e03001082c103410014041e281080c1d035080c500306062a10484200c10701070900010030f41c81da44000c260410324190040b06440c1c00291024000020b4040303500501c20000448510180346e0580743e65a0043d036500d900114a0241b112013031091030301183d90140e0308028184041c0e204014074401c0012403901c294000103d44008580c8a072030f009148004100300c0340c02c50510359480d100c0d00c1c110395900c480212a039400b84120209150000c6c00d0348040d118000d4001c500b0030318191441103121013690480100c448541c510341007181d6065003102c244006038000c08000016091024000341c415 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 650924280 1250 650923030 650923037
    0x20102070512060a060e1302190b16031106060a09090c05220608010902100813020409060219020c15070c0b0c160b0702030703170904050c0310080a0c09020a 69
    0x1d6450002440c0b0050500c00001c0941100e0f040240c02007440c400d403c007904101031001d1745d40c100100c03111250400c1d001c00078042d40d1800d2209005020310304080d070090103900382c0103682c0c04500030801d484000542045011074900e8104040140000c509140f040a0103421003440d0b5180021000180c01c1240c4107a0301600d1190000c2882c3c1c86040c204060200455103400c80d0308a2040040308442c425804185984d1508a2500050366154240e000000583c98110415150b801241c400c0d0195900000e6200d8500b07528407042109640103400c0183c48101c2440c0e5442071042d040c0c0e15000901c8196601400342c41165001e40382c19405019114090381130365a0030340d1684614011136212940340601984a04500807220b003414072100003802680c5001402c003d103c0d4042070343c44040c0d01000382060021a1807059034a074902c00d0741c0009000030400d0200e8201403c10023010751050300c0e40c1103403540880d8041110100080c01920150f880327004800701600d0000c6001c025045900e920081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 650925530 1250 650924280 650924293
    0xc0815061003140901061409060303031b1909090c0c0f02060c010902091509070527120604120e060a0504090902060714030a0f0801061b0303060b0a18050a05030a0f020102 75
    0x210f0a0000300707407145001c81d0000138184c0c1420903d148082c0c901903081d2103044004100503090300c0220580360008200700d0001961426142c51031154001c04107146c002c0c400081892501c03a1303000303103d0412600030240c2080000d000000440d10142071103005050001101000300c0141090401030025018210001607482d4081d80081d45514041c1c0c1c3d006212340000100c041c443c034003441c080d90441503e050807442e00000106040c003642002d044100d0180d4069461002c0d070b1202060007040002e1841662954903281c46c114141801941072940054003000300001c550506404a561441c0d07541c44041c18586806980000b402d0242e4040307070484814050b0303d0008542140c4140340a488401544d1201c80000004000914030300e241d204016284004201103034218800140c04051000801852112424242c02500d41a48821503003040015481121760780100c0500d00c604c1c004113101c524a555000b04006481a8090a54560806500003002994040401514074418010b8850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 650926780 1250 650925530 650925551
    0x5061c081c0b120a03090911040906091d0d090302090a0b1f0e04090c03080705070f08010b01020c0904111e0a060c03080708010602062a13030c0815061003 68
    0x4607040d85412101d0700300c1c0c64064011151610148030311181d404070004060314003d81d100184888024410300d02c203140d85500785005007041108543c0604030980003445240e03a982000c2c0000c1440c100e50030506e16111000020401020802c0000e00c0350513558442c1c21811902048808000503003114130103561048900300030b4407140c032154950b07031500c508420070065010000d0110681500607a00c241d01d055481000210008010f100b41ca0b0014079041d1101c005203070213454000c0b142c106080c3c0241d0244000f0b20413070150006e4075402804c0c2d01352100315050a041c40b1800500303440040c0002d003408400d08141c10b0042100a481c0306081011084070703060800f249400c02e072038108400042c84903c6100525801071112500540071703103080034540d80741900080d29020041c158400900c1401e840100003000070301071204201c80810311070b83e281d06000300c40e2001d10b02c5101c21141c54108480002d01c102c0081111202626000184109035940904000070305100001185c00e15581d42e2810740d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 650928030 1250 650926780 650926807
    0x50f040812030402180c0304060f0902030f0c0111011401090c02030d1b03180c23120a06060f08060606090427170a021504140d031b0305061c08 63
    0x56548501d140c01654900742801030128079505c0311190364441aa16080c0203912041100710390348580c10200010f10403c070900e03c0c1d005840300520103503140c42009010f85c0d0504000c41c0c4548080f109880700c03006440070320141030030303911540e000341d40e042e080d000108181540d07a003003804c1c0d0001c0c52040c0c1780340030407807905c09040703034580d02e000c000c081c0c1a0400c884210b074040c495520044400303008040840c010b907a803540d004015000e0802d44001c005000a4000101c031610035204da001000d0010404c03c03110416078400c002e2106690143c14884c00107406d1680c007540130150759103000a0016a0b8074501071103043e500a1030b64603000750ba1382008041074500884580d41071140312500140281c09070500d02c203402c21a030000e50101030100005203240c0d0300041c0116040d40545644041a901d03410072211442c5103000140050181c0800d000b400e079416481000009100400f4480c100390081d822411207404031201900012480c5c60004081c030990300d00c502e002d119190349442d0070680041007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 650929280 1250 650928030 650928043
    0x20f06160b011811031501140d140718060516080408010f110c0d1b050a030f03060e06010806010c11120129010903020d0f0b0c0403050c0904030f050f0408 68
    0x2624461403580040c803070030303003070200919511003e0b44041c4081c00b00d01c51500007500c03001d040d00250704403000202d10607902900402c51a10013181f1120345900b03003051604042c0905600c00f00d18041060700007108180920f540d069484149040442442d040ca00191031580c4010350b08030120810610305400034403080010f2014048800021070207410860981007a00c20f0038640103501c820600c41c000d21781c100000d4440311900c1518007030903034440c0344c2c9186904aa0341c1c580a4400d000c0c203000d15090540080c0e8284450400e50343c200721242c1d07184290b82c3c51050175600c06001842d840f0103d1810362064984a0301280034500031003900350510700003507049900c07840300d00c00e40c2d4503441c00d102506180100c0d86454642c41e1600101c03000745074002854210b40c4c0c04028400c030001040601840f2103450400c2040d60f0010741441241001e40141d2603a40003484201c07400c0c45a40a1002c0504082d03c1040c01164507445031600b131641e5220507901508450354007085003000744400140781c8401c1080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 650930530 1250 650929280 650929283
    0x150512070c0203300901050409051f0909110d0204020904050117010e0f070510050c0303040c03020406120209040605090a080403080307020606010903051b18100501030b0d030c020f0616 81
    0x40022441c40d030b20605040c01c034012440304007242c0c6002e0000d180d200341c1c4420811300e515400341e0760f0f035043c034400165038501494102e8403c8519200c1000710b003281413400c250515045400c54081e0907031f2051154266410741714000d10304000c180d654209800e0000000007540e10051000d4103140c0718801290840ea4241d01c0030075803d1214044020456080c401c84203410700103c0175202070040b03103105507038500140c4111401400e134209180e484c944030780140d60303201c1c20321000d80c1d5807810242481502c0500b24001070307210754076140b8001881003000829034509640903210b0044c590f2280c41e050010800100f000500340540080c00c0001562440204040d5126105545d241d0401600007031030104000c001c1414081408028004a900090759501a1903515014612074100d90b02145500c50340c1500d00c000e03000c04100f40300059510b400e201041da03030301780d800708510201c5000b044051000f0320000380c003003450303c8940c0c0098209008c03038416202c0082c01507072519111582080f6069440d140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 650931780 1250 650930530 650930537
    0xf0f0d0605060d0f11130b0304050f03280503011805060f12031308070b1605011b110c0306071205061807020a06200a03020a020a081309061a030115051207 68
    0x1050340858156116400115444155060400200c4c1e041000e0041b06401541c0c90f944011000a04100c4100007981003a40c01900317494640c000205a0040d42d9041000305a144805c0f882a5181c240f00fa07040c1c0b412140300344003041d0317584c075000c41e40002080b01901043c0c01c2220101034801c00c1d190f040c40c0780c0840b1503c4004656426a11501011a0700e4a801601540e00266000c2140110010076605c1a20a0701c200d80500140303032411a0050041140c0b0044400c0c248400e602076039000f445891149201c2d90981e80c140c4900001c164407060b040f12041d0104a04d03d10010385102c003070384290382c4194043c103045001d032a0f501c4180160941264000d00590090480c10108400f034024501c84806800710314110b9211004008628011062b01c401010b82c081400401d6901c01c00035600b905400040c125524204000146420200b81c000d000c191170030b1000004a403420000c8071248040c2d0b55003443e0071030b42000c14004120386901c5e210010043c1c00d0152401887c2d9045807180278034802d46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 650933030 1250 650931780 650931791
    0x20a080c1b010623100c29010e07230a111005040c17070303020d050a02011d061b04150309020a0911040e0c09010206040b0601112409030f0f0d0605060d 67
    0xc041c04d424440702d0b0140d8000e4410007243c0811641200000b07000c02c0d4400b502d114018203030909000b80801081003201c1c0000c0b10f50001601040e4129020b0041c0c00c0d035600e640c840f149250841c20f5481105041e0a81c90004001381c40d619403180e108200e40c0f9100005960660203404030040581d08261b038140d40c0f05401050800c8242901c000c0026080d04100141c1049480c5440282d00c1c0d04403c010101840030006100c00b42034400e5210340c0382081450a5000c0300000940a103a481c0021500798881046026500000900e0742d0241c404841c0b498840c040a83c0b00004200d01910005400700e801040410380800c20709000e00138030b40c0550380c5032801c039200d03850518000003d40740a055171b01079010410904d030b401d0342e0104031039600540009070121903884150040701c2c241482002840c850040340000050002900c400b20345000f048005c0c0c51041d100c03400c02945034807072400045540c5008001d50030054031210082c000c02140c80304002a074543e00c3c004104141d01c41d40c40e49500a58a5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 650934280 1250 650933030 650933069
    0x10e0604110301080c0a06080106050d09110913050606040e1009051603030c02040605010503130b0c0c1b0306010b1201030605090a12030c080a05060d02010302090d020a0f18020a080c1b0106 83
    0x9805c1e1b280140080d103004d414039450150081c10070f1180c207000320106c0e0b8540c441f0800340004100b0b05541500c0c080d0644100f0f00e41b20036160980c1622050440d1a4003901010461034600b80c00342100303002540340a0082640c000742083e00512980d10112a140246e900c085414400d5400040c0110301030f0721140c0c100b580078410001110301d00c0e004181131000c107000380300301e00c4885044280507942c800d010010a80300c404017404140107414001c807a91007000518080089481c030700242003c4180e0407100317941d0b01c4070b4651100d40a80c1080e400d080e00004010004600d5603002030f50000146015940054910745460381a03208510300c02000c01d844000040d1015400070781d240d4401810402001182851000034615101ea240041c0c105900070a10110315070700c0002614089038010602c00340036a49011121a26000d03200d0340310f00c0c148043e003422000030b10b03000300c940118075942e5035041d40d92130841200c1d4980151220060f02c3c040041462a01c5500b441407001601128945503e581c009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 650935530 1250 650934280 650934289
    0x1060602061909020d0204020a0c1104020703080c0721090303020f0606030c0f0f060c0705011e0504170a05010501170c12070603230703051617010e0604110301080c 72
    0x25400402190700401c00c0040d00d03102c80c2081c40d030144460344041940c6256000142000294040c042e40c014800a0301403e0590042c1d41034a00d9403003050a52150301070981003200720300800c0c00140c003141300c5000044040c06220000c007451071003204c0140b079642d403200d2201d82d1441c07038030740240110310703003060034801d26404100300300c0c03800c41e000c00401441c900300011980702e80403080080c0c040c0e11514400140f90351210900e20014002030700a64640b03104040b80382d9101c12500c1201e001c115506d0b200c00c030280000d03800c82620101c070380342c0516103840c02070b0301000096641407041c0d140c021200c41800150081c040c8600030640d04846200c800751400502d0704003c000c3c100107100390302448191030000000f20341c4000f21045802c3c00070380c400c1c60491403000c86645440344807002c682e000c1001213050b050303030000d4001d43d65400700c0c02ca104641d041c00d5a11080c00061103507211862001042801c4194070507551107130f4003034404682c910700020841034513007007a0000401030b0000906031829050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 650936780 1250 650935530 650935541
    0xb04030320030a0f0e0d050c06030711060a06150215010b0f0708031005030f0c1807020a17031006110a14011b080105150304030519020a0807080a2d0804110418030201 73
    0xc00c45242046c0704880d902c0641e00c40c1c841866030300600c3d0100010744040c3c080c11b400c1c800e54540300142c0c2c2e0300d13281540000d0024040c45c0074414080c0307a51075046c01078038070000b4000c0066000c4e00c5051466400e00c02094460b42000b49640102c6404021309000102d006003c2e50007500b049e042e5490140c1810101400e0200d10004900c19900109032508c40341d83da043d20049036040f824071100701d40c070340100890806044000c09414801040301e06151a04070300021031098441c103542c00b01c203584400341202d4a4520900f402500d6010071a00310201e8016104a8540440c0c0e00000541241c5403156808941c07000c0d2403280840d4004004100609002c2404000c61040141c0140383d843d040d03401502038020f4020b03641c8070003541400862081d00801c89004400d40100d2a81c0d2181e05078507140f01254003000780c000000e11164080f0700110054482980f55010384064125030b01d10f2041e00302e802290052054551020b5112006000e4071607124403419074062101e2203058100c00d09010303081d203c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 650938030 1250 650936780 650936807
    0x10203031302040902030a0c0b1b0607050409053c090c0603040f1505010902040501020c12100c05120108031b0d0c03080408121f08070b04030320030a0f 67
    0x4104204000400500301504041c869044400043d030224a00210b07182ca00089001858919900c04c0810803241d0040907006600c205a103d03000203281100c0740d41c940c03a050b03406c640031031424401480b107a1529008039038020314100000c01c10714130b080b1000d21300800c2da00f10f06020000003401c0c0c00d000024042e13042e51060001008004d01406640420305078400140084d110307420b01380ca01030410800c80d008041041c101c010510455031945140c1001350300c50f10a10b8090300c240b003961813190400b003100340384411a00000c3c1001c03000e40d07240c07440504100303840300d020060104a80e003200030305c1c40c4e8007034003070301d6550015600c03052401500000060700610a00c12390340103460b44030225602c41081421507505241c0848030383c440703141400c140e0181c0907500f061941c448040080120951003002c2540e07100020503400160f0300c2c0c01040d110b03000c0e0300904504000030401840468007849107042c58600f4284069801d100e41c61007682903070010340c0b0302d8000a0380c8100441c01254009101403503107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 650939280 1250 650938030 650938033
    0x18022b0213080102040311061b1b040c0c020315060105130803031b180d06090f050a020102101a0d0507050d1a1b03061203130e04050d020613031803061a030c0102 71
    0x26040d510b500c140c0c40071207a1160f10480f400a0010010700081145100540c0303a541201c4200352140305418080d09910072b828002c3c0c3c5043c1100040900c00c441c0d881659030047e0240a00d0b0b01c441c0e00b41c0e041c000004055906012080140e007940780d044005c003400034603055020b103846e424855103405401d9600807004680160501c1481b44800d450703c06510280300c1118a00d100100d14030f01640a45100640500100b0003201d5110520202040f14130b40e0138401d83c00d6a00c1c008a5920322411206040c81801c5075a401c418495602e09202c0406d11025010b0421680c4050344d400008101d4030100c40101d07006420701d5080c8014060269030306402c010145124041c030381c04170712000c409003c020800791041c859008030000f07001050046402283c000c1c0f1019240c1d81e242c04ca07030800068140d90464403445503d404156082c03010440f04d0048000d00c1c2000c0c0314022540341110f55523856481d150068541c200000001440c510820389d540742c1110b503c01044500c882014200710880c21a0780c10b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 650940530 1250 650939280 650939287
    0xa0e030403050102030a15050a17010b0d06050601020d03050c0406030b0d0f2607021c020d2f0a0e0402120304081c0f090509061921051618022b0213080102 68
    0x750303a50300b09c40c10503208501c868010b031141d43d22000b40502000c510080d00a550042084103010303182d04051300c07454080e000c6032800c44104504030300310341089545100d16941480107000d200d11071340002c0d6101308004c0102011314402d444224810000000490380e4203040f01c8800040103c40010542c881d09410040c1d04080b03442d00810010307254103c41490140440c0032050440d07803082c0c00403040c59001100790840c68804143c5e5101e545940710110040d40c049400c043c150f103001d10109085d2818110340c0c850503100c50f400d00486021a0b4107590345400240f002113944041080400d485c4980ea800c80240d000c80c40d03401810004100c80202d040210703654061059444406290ba0020b0080d6070403c44010407192a04411029410902086c400a0800e12019104074500c64030702e4050300542d40700120b555210310890303c451160f4002420b00600500042c0d81d25406000c810400c00b0360102c5116880c503045925250300c0449111b1258081203810402130a01221405094010001c619 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 650941780 1250 650940530 650940539
    0x90a17070b040b0726070207050a03020307060c0305121314210a17040b01030c23010c290a0507030c120f06080d09080c010c030f080a0e030403050102030a15 69
    0x402407005101408000715500843c458510030102d00003a6141400411050b200384a038907070607000705a400000506c20600b01040f507181003505030b000c4a43c010000c1500702e00e489803c1d15840c0c6011010381c00c2c86401c0c840c41e0091100040030520881b000e1842d80f42100c4a840c2040701e0105013205020076a114148243d6006242c40e1940300c642d01c000e09850300c800803000c084490101036010104e4807986c020511007045482225241680d00c40c1107011610b07138a0780182e010390b0400d03902b100e0380d071480004181a130303500071101c21081c01d009500304c610b43c43da00a00b9104032620414488884030652013004500802c80c860305400101c2ca20b4240301500210344010b010400505021130802e5452000c2c0b5a00c501c558418002081200169050003a00d00009403082c00144540b1102e80518103d03160365600c9100c0800d40e865050b100c941e03d442500d0811100a03100409a0464507075504451220715010406400158450f500150b5603103800300081d0306840030612142a440e540711350900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 650943030 1250 650941780 650941793
    0x50f1002091305100906030501060819030203030f0402040906021209162d030606080a0302150417181f0e030c03031c021303210801030c05040e010f05090a1707 70
    0x8442081c045020500303884622403c01340c0c01c074952200755114a41a40082080810742004085466160a50720196403143d40200e085a90080090050b04100f0004402c540710000c1d060f006070014200068800040e543d1030100c0e409014188200520141000502c4400300007440c80501c0010b00d070503405243c60940020045c00303024030030040640e5006000d00440d40081c0e030008640050b000d000c501d68480b1460b0315590451029130042c01065400030190201c000d503240501c2c0e00c440d56515605411b9406c0805070401100d0381c000c0c10ba481420320855850322030032110079039401d8500500c0b105a40c4064028410480a00c0c000d8105440c5007409680c00300c180c42441030351800808054280441410091040c0d062054803000500408014400b1155200d600c414003000340c0341540c081f4802c10380350b201d024031000b0641c2c0540702080c00346080a40142440b400c0100021500d4140d64920f1001d40f1012144101c2940c08003581c281804104c0a41a015502c0550040d1802c616503d40c3c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 650944280 1250 650943030 650943049
    0xc090f09020a020f010912080f040b060105030405100606090920250c06023318160306020c0c0114030406022a0106060e0a080316031b050f100209 64
    0x2040880d400b0404000d4070b4001c1c0004410006098020084480c5510385400c520480d010800005560100060b00c00a44030140c2800b9a802543c0400160740700c400460701680001c00484003030003101d04140014013103014000141042c3c1d201c450030075042440104c21a19502811551840f602c180c2450801c0750400302c4184648000f040c090f0500c900405454540c4942c10051650110060009203280d001c0f802201d0b43d80c0c59180c600e0090002c040c0c00c0f003c011041c0b50030b400000e903140410f010003c000c0608917025101e200fa10300042c48400052006100741d03100743c880d2500000d0010200d107081c49001c000325000d082c4008540007140c0e02d03070389602005200030407940c0e0001d040d0f80700c102414a075128800d1982e48004207a006070045602800ca68031503070000c55808a006511440d00d4800501541e40d140000d5042c200070b0025044031020041c001c0c1c4c184003030103410004140d98840c07010f01490040004041010524511f00d00d483c10812030000030390300c107100c5041c8643d103c007403c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 650945530 1250 650944280 650944289
    0x2090412080a0207150209060c0609060103050d0c051e10020a08090f0a05060411030a02060406020307140c180a020909100e070302120a09060f020a121103070207171006060302030402040c090f 84
    0x180c503011581d01040c458889c40c01d52000ca8810703001040310507100000e0042c1a03a21070400d64541d090840070070340e01e825805000a0003508150600002d0080d0865810910314814044400051202d4240001c03a40001100780008000d00200b2a94001c1004109a510000d400a0280380380603152180c80d6040940014001280c2d001908071a031390403c000503885400400c115683c551720800079640754031100003100c0c601000d1103003401c07903000411094100342e005440703503001a07805c8030b64001c0381e44010f040c40c00040d070900c240c0f209030700c032241c0c003510036000d1680c1c0c85021428000c1c4409141c0b802824002054010004500d400c00c0d80302c03109400c80e03062000450203d450b45080c401902c801c101c4242d2491001c2100c0f90801e901110320185502c0b40c20b000c0214030808001941c06c3c0c842242c1c4200540e000074030400400101ca0820070240c49481c0c01c0c1c0d0003945900e11030344251811507004c2c00000ea0084140401d600d024491040c000186051100034a840e204e0321405404142c0719 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 650946780 1250 650945530 650945573
    0x16050a05160b010905040204150608130203030d0e060f010e1506180d110a080c0d110a03050d091703090a060809120f0d2706051302090412080a0207 65
    0x801c401020710411107640c6080e4811010358003980c40d40940c5000302800c9509900c224201044400031000c2d428070700c3c1c1030304c2da5030351081001e5440341740008007188409400c981600c002c00038191069840d12031801a221003802030189420200b0308108201d00682010221410580500c246003010300a18400305400f510855125182d00c10130b86a4900c6255030660808000074100c0200100c0d2280030912072000c40d09045455240d000041d0f407034000303062090300300b0f1601c410710b008111a0400030001490003044010b2554a07580c46608001c40d01c05000b011a8441000b40140749040c005110140c0035800154104114003001070b0324030f010361003140c050142c050003191218500740070003014001d41048050f991500c02080f40d220b9031100780a40701c3c20f032a0100010800705190740c508840110301c0c01c8407413004090f80f1404000c0c5000707030040e40540354548440307005840742494113110f18080c1e560064440d8200304058142d140c000d00d4440558810448500002e14407000818000b04550 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 650948030 1250 650946780 650946787
    0x50406090e0c0409020a020a05011a010801090203040609050703050105060a051e0118080106060c21080411060d2f090a0303030f0609110705102a031401091416050a05 73
    0xd4004000f4400d54200310002800051901c0000d600003d010900a2054000700262045104008940c00304411007034001b91042c4010003a004180d0061508240038800000d4020b807203954a902d049265482210a0b035101d104101503841d02c41a410000c1506540040d210841c4800c10300030300c8032005a0a051025804c1111400e12200c64000b01401c07941001704400764075a400038101004201d4121660030500c0c0030324218541d451107204401d26992500c0200c0c0c0c1343c030340d02c0028007040380c0b528a8001d802440700390003090300e40c0280c3d00603000b40d40e510032441d070294040420f4044a0104906140020814803a2544910000301c088907054500019090000e00b2207101910b565405a0308850801017111406103480d0014200c451148013116406000c3d070a0300c0e020b59007007410504209100281503600c000302003030450030039450752500094034519019001c2c1b00030400e8100d000455501d0340761480000015241c01e4106120740301c2103500038030030b10005000d403080c0502c0c54200003011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 650949280 1250 650948030 650948041
    0xa060507200910030b0c040e040f03170a140f06130b0a03020303030a06060f02010902060702040e25090b09100611070e0901200909040803070c0618050c01050406090e 73
    0x9818068a0341d600800070910340c140700658020104850000b9104078036200017140c01032501070122021180007000100d2aa034444d107810403e507103003200039010300001d0842400411024000c40748204c0001070009a4020310604448403140001d02070b4070700203102030500030141c0d5240e02044808a420a000c2202106400032030140402544003c0d0184000300c20b10400d800982c00800c2501c1d61a41c2d110444140058100d0903a0440040a50000d004000c25009420940c0014001e900044221420308c44e581194868403089040205804d0402410a01103480b5501805840e1a03040f00c24825600744218404440b21b520b103c2c2d002400350310310000c0311004040c00400010080c505000380f07545000c41045001e45103a1107104c0e17201d0101d0b244142c440d0b201d8826075440c090060090080c81e62141d80307650856001070000300900020184800005080e805031842448a51141c1003142ca020310f012890449062080c40c1404010b0209100143d8040d000400700d4140c600c02c0391458548 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 650950530 1250 650949280 650949323
    0x20a0504020c01061a0304050d08010f0e180610030b33030705100201060f06111b0f1003021806120a0f0207021309030e0405010f180209040612030e0a060507 69
    0x44d54040040c00c0c0c180301c0c1880c038100d149400b03184200e00520645141c800754500c119615a000d00401040008050062203a2407081540c0717a884464000c00071003a0541ca4000c501d803070070891b03001e0521030a00350f090040041c01c82400e84c100740a511407100d005101c40304922440710a04140414201c40025a44255000c000000043c00d028050303010311500301000078068100390041c2441000070080020790944900340251045400d4001340401c1c1c01c100c404107111051180011391710030f40e1142080321035642c1d110304902401480e200141d5403841d10100f0506030010307180c1c880c4101400e20298201302100001c0c980e00103900d2800192410380650980021301a40401035080404859055500f0040d41c0c003c106107802902c0382e09101e0202002c10054034801d004030404c0f54a072003020003040d03152050050840d1003003140981000c00701e01c040340441b04c465102d05001c074014040f0744240350b08541d24007400038061361898038641c1410405484c5110380e44000b000c900080016401c0c0840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 650951780 1250 650950530 650950541
    0x203130807082214061c020c1609060e01050306061807050d02040f090e0c06091002030405030d050a11030708040302010e01052a0d03020414010509061b0607030b0409020a0504020c01 80
    0xd034042030f10700b00d10030240303d450240f026008242c105034000f40d848900e440c3c00c0c001e54403810355201018040c0540010050302075001030a105002c1d11030120f10107410f0784200903110141c81090f80000f00a4905017486c1d030140f030103030300c618005e82001041c041580c40700c3c1c0c04202c4a4541817001042920340b130200b221740b032003601c48403e05e0610104007c00c90081041584007221a0380c1024030184003500d0300344d52204020920103522501c2040442046c1c180780f0750f8101c200d0305600540b820301380d032080403078204060412886c001601c0029201840c5e5000400703164151600002035050503401e9641e026640724901002c1e0520140300c44850302c6a02c62400c590300c00d01040039801a8201405051010384204c100d4607585001d04c440c0c14020500c24400e4808884003504c0c6100018519001500c50b54810444c1d55000758040007114170010f00703000401d2512680100420300c62400940007401c54115032000ea2185062400840140e41c0e00038000c41034078030440b40140e03113a00e0413101600614 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 650953030 1250 650951780 650951797
    0x4140307031214151e030f06060108070c0c0303050d2a020d2607030b03060403181d06100e030f03040906050f010801090209030304030b15040609020313080708 70
    0x4000905001055803200004180a5000c00c0c00d10440ea820f0401c549152022100f40c41600d072000d4a040307207071808107110307600300c641c82c11005d50249642011908000048401c410346030b008506100d82c55078081781480d0710514030702d0f10704500c0f1015901c0c010711801e144000f0382046408161a4510300269010039a0020310566842c0302464a40d820680c08120f65a040b025005054920003030314090442840e01c1c01c800212429050070500f040b090742000170308540b04042d5203090f407981d50380b4104241401240603841d8012802c00b0880c180c0100d040c5c0342c00c00d00d103903070305010f10360604614902c0840d0055801c8800e11441c002c0c040c0101c882a07125620107501d032158541c403a10185000c0300a02c1030301c071002018010a501c1c0d00c03c3c0007220000408090010310a800104810751150303000d022090303001015640b40c555a900c0300d2441000035299140401c5406044142c549081d00c00c07032001f81a4140154114604070b100b00c1d0404440c03100c041c4c405100050008100200e4a08544008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 650954280 1250 650953030 650953033
    0x30c0f0717040e040c0605040602070501081f03081c090201080105011d03060130030801150e06070b0906130c120609050f1608010e1f0b0901030b16090f0e0414 70
    0xb10350b54680c0b01c540d40401e032800c0d41c01030b002042c0410071611480443e0183c07080c2d0b07001040c3d294580030044448120050042a8003d4000f003517203000460308001c3c0b4001c40c02504010f488501d030074120303414140d4803405407a580c2c2c0340000da0030042c3d0f006130150b41110f0b402d090013081002d040c0d10540004100c0207509a050141c00001325058554020254144030115940c1d140840745d0980c01135000b020070001b9002c610940c0040144c00340700500c40000000c10324201c00783c075910001141698100f458221707483e0307a003441080b42c902030422900364818080c00706141c0368503054840081110050080c00c1484440c82c200f102801156081041925402001c0300d921402c511141501da5241c554402da080300680b80c00506100e050241d121010445006030280070398820004c4251321905203d0b1904a446405440840d035509504c10700a600981c1202e003189815050345145a01c1c03071000009000031083d0501030542258810740c2501c2c91941c92000c540c8541c140b903014410400f0425045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 650955530 1250 650954280 650954287
    0xf13050a1401180206040b1308370213020c1e060601080705120c0304020409050102070303150f0e06090405250612060b0a0f0513091a0303030c0f0717 66
    0x41028074120120a450a44001c10100a0a4040d4107180e66000303c042d52220041c44144840138a0304024200d40c0301d8200314910666407424240c4c203000340d03040c2004c03101113652030303180020b00350003145251010440703c81c03001440503500064850303c06e032444915840d808100d40c00b40000400c8080c40401e451001d003044135070005c00040d40c41504a40d1b10380001c614201044426014500f80d42d8040e0070f080c088600b580d24281500d23030780c0d00001c01c20707603000d621111a900800c2c428070084c07000078020350b004140030030406140c030700494041e4840e402c0015181c07010041c0c50185000c254005d14119001e840030740315030502d1890038400c42908013040d03800f440a40c0301c41108903407540440320242c8404030300c00d40f92058101154414032420301000400c20600e0b40c4079210340034000107040541095410070062101c203414403a400d4000004480d520001352340d014120000703c00f0240b034114001c520750f2914028030641406a80b8a010340306030086801020132808104820303010a08105081d203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 650956780 1250 650955530 650955533
    0xa234213090501051b03060604062717010b150a050d060506040e0403032304080715020d24060f080a110f030711060421050f0406050c0d05120f13050a 66
    0x30300b001d603411a414400144d08045a161405c103480c032a410040000d400c00e4640802502c0c00881007250002005104005004285030200d01001900500100050300260300d255582100d41101d4031034410207020b0400709013003030030b081200c140c00c2c0790340380c01780c1c9450350a2115000b810654210320352150300882e01040500103d04001c0c070a40c000c1d6801d01403038030543c000082c0318040c141080d41c1603000c040010003048442c002002014840e070004121901542c075440c080b41c00144182c0c0649444c3c0c860380380650b0a003407000158090110007900320358030f8140702034003c4040e4406481030081d94400510007501a82c40390016442e940300c0141e07160a160b5035402c5661003103c006021804000391401e0720701c00094014807940d0304c9681c84101076560807164144800d1802141c081242c100200700780c1c0308049015000410554076040c1d00c0395040603505003058282c1d40342c5000c210742480328040c001c4401c8840c681210358800c8000480e05e45500c201da44007000328014041e44030f002400740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 650958030 1250 650956780 650956783
    0x30a0c03023c1f0e090c0405060d110909041b09111b1903030204030201110a0f0b1317040504140f130602040b1b06100b070b0a2342130905 61
    0xe510382c41c00c07070380d8180b240d540807a10f4000c7e01a034010640c10040c00c0c8010411b45d40a035100c0401d401e812001d03541400320341c07000074103810b000f01c5044801c041e031000d104044080d0480e1410141c0f15440d41809164404405a0450300a400c0e4181e1046a00c03202211100418411145062920b00c024141c103400307814040d010717502621040780003c81c01d03c141d02c004403003c542c0000903684810341c912409459110755440c030501400a03907204500c042e00380c000441103075400c5400031003051155125854101040b0407250704903100b02d0a607080314108200e0800c0524841ea101c80204200c921900345424000001d005540008400040000305408850030403642d038240a51103600b1100d140c1d440d048480c081301d0b0f55100c0d01207104c0061054000081c8040e40303a42d880b14030550000723100800b1030240c0401c0c00345044440100100e58003400b50341d00c0f2444000c04040485140c003044110320b9541e0960043c1e10820b24071141c1c100c10030b20481951410b1000940313444a20051096034210b0900c0b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 650959280 1250 650958030 650958047
    0x10504030b0a2412030c0303060527090607140304060204030c1e09021306050c0127030e1e0402030a0e0f010c17040c1211030a0c03023c1f 61
    0x916450940c1c0800c0c1d824914407801c01c0c02d44081c11301280341ca22584c1d800352007102c0d100f0011814581c0340c1d00c001ca01c640790800ea0020604100000615403003040205044e5a0409826120036400002c100b01c5220780003412003c4039504800d80030b90301d68450400c40001d0049403c0142066028180010800846102458214107682419510958851502e4100d00c60a1980c00e0321404540e400c00546010703078040e10308242c5090003c1800008100040c012980f00c1100c40991142d80d1944024164010010140888151000c0555554154218000c1d9035884c02c690310450700000010350415030768202650054000c0e003126000d900c0d440700507000c0c180781440c00d00018280782010b02103184446895001d1034000100c04005c40c00e280d01403828109480e0301741c0d41d0a038882000d118546080115800d01c134001c00b20b0101c00c03810740c0304115581841e413405c5141d4594940803101c0c20b0000403401100c829204642012401c040e07030100f0105440100007407c0c4240e003500c9070b68459000b81e41c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 650960530 1250 650959280 650959301
    0x201090b0109270b0105100e03070b040303170702100f1b0503160302041202010c021825030209090604020903071802130608070c060b012a02040b01030b060d050402010504030b0a 78
    0x21480001580380d40407440414080a041d5480c4d040040005041501c841c002031000361604072a148a030501282c648901e59100c1710400500260400615911030011482c59034130101040e40c0d801c00d244002c0d40c0f81c120801110350300b640e07000328240c44421648120000315843c0301c0e5031a41241c40101a11a400c12070380880700e0a01013100ca0405c40c424802c94060700c00800100c0000400c5400464003402404422030700300d804510144103a000c5000310600c42c81081c4041c0020100041a180c011980000d600703061500600060300c051741c0d100c0d03511354806400c2d1001a2103501c40030000349408500d0784066844142e04d03801d00100c6a00760000c00c410450f01080d4050389944050890304048101c40c090001820b8404d54400100b032504130b00c6000d00c052501d81e12a0740b4034240009040c40c56070031a0308984096410700e0171400c2a000b034003070740042401c1c10052034030200d010403901c3c481c1401030820a5a03c2000408581c000e0050300c01850700827044c18160301d07009901000038400c5195 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 650961780 1250 650960530 650960561
    0x120c02040b0103200c031c050402010e0d05060402151b0a062304032d030c020706080c040b03060a080303040f0c141008060102010f020a0e04140609070f0201090b0109 73
    0x400c28079540a8051102c1510b454031280841c0e040303100c244101034206400c2c064903400204008105880d03c0300303031000580d02d09200000d00381002d1001420200303039451043e001304c01e4410080003141c004107086038060b80554160706801c05024403480c0520504920034141020300d000c013079480c3d0300060b07482000b9104400030850700044540404010b004050307004003030581300740001c0000380702d4200e00c0c000130189905810310b40c0407405103000c0e2112000c20000000e580d13288648030940d040020300001c0030b003420050080e061001c2c1c1000144a54090951014030000c0032038415224043c079400100060415241c076402c03d40b50101d080c0c2c0700f0b6881550420280c84011541e43d5920b111240c035400001c100b0310a0b80354030082034603080f500400d5581075550700c1c0c6c2540d0091419000130514000e40e507940802105100c0200800c851444000c4840b003900c140812189842d989a010780003426414100209004080300724003601e800c070001024401c8041c00054003004981000414030801d44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 650963030 1250 650961780 650961791
    0x405011e05010c080d091101030c090803030a020702030304031b0f0902090303030f04050c09010303031d0303010b0d02030903160b27100e0a0b1008061012030e0607120c0204 76
    0x114054040d4408104903091116003000401c041e60140042140d050710804000b820003a05c54103c1040303408a41099032034050554503289590707454891001744d072009080c507102250420603019030341d00005101e0701c02c0c2a40003882105656080050705d00550340620301301d25440a0700f1011400801038450800740000c11a40800c00070414003e035980000c2c0030b0021070455a910400000c50103010f0010303142d5006034020024181c82d50401c281c044c1d8020344001c00ea2071024440620551228001010715410034001402283c03400021030300322240c80e030405038980c0c8a04c401036040d0300c00c00c01c014040040103008081001240c624540c410031041c8210711480d51402680f4802000c260030401c2d9070b801c6480007400130842030b4030640c08521840125552500582d460008101c801c0c0c400e03210149849908000c01c110801440e40d0000b03900c1a4035500500d00b60202d45403140c0380c00010305004002e82201d031070341c5a40c0c098442d0a43c004540d8005000d0b20039000d8070380001400306a00550400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 650964280 1250 650963030 650963039
    0x1d0607050901050409050a0e012f070609120c030e010908060c0a1e02240402090a0c0509060708090906030a050615030c06190e0103050c16050a02030d2001050103110f031e0309040501 80
    0x10b02070481420b03000c02403a20110010000c41562f070101800700c444682c0d9103510000f20b100c8000304041000e50303459844c2c14104609000d04141180f000d0b0703a04109240000740b00c80d4402181d19078024411a503100e4864481d800d0981c1c1d075509800040140040303007200310115643c00221040a4008007171401144984038540010441d000c844c00394011000c2000b1030005c54a0381d000e5220140d003860040d043c0248000064401e074890131054441002c00310341c100b41807030184041034000100710028007841c040c7c0c0e99125103da500601c08520034400280034201a1400d010040012600600055441304116038040790350b4904111100020320701d80c031003007140d4040e100f0f080c01030000f84201820040050242129601e0489007200d66004040d181d00c010388003000480c0052140b510750800ca014140c5c009015041c3c610440d0450340e041c0401000405c3e040c1030111041d080c00e070307004c5502d0809a400310307141c842e11013031800824441c15075404c0148800f00140945000c12502400320340da80e0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 650965530 1250 650964280 650964311
    0x1b0e09030f07200a090e010b0a1401110a17030a050604050103050717010b0604030501140a1b031d101d010e0c010c150507121d0607050901050409050a0e01 68
    0x2414032240c1681c0c410840200403c006895032010400140212800c00e0f8034080803c20340c00042d071192500c541c0b50702004041000030700940c81405e4007558200300f25850701084804005450345824180441c55114180072103003440504071107900080142030408550380c17913030000d03032084440d911010328041c0800d01c40c0c13905014946c1242d4003c0f0040100301c0c00c02c420b4101c19203102444c02c140790748e2603604000c1926a0707005000258001c10002400c888a2440c241010f90000c0c41c20841030b1900c601c03042c04018808210181110501d00000e000702c07049195a041d0300801050000c620a40301150000d65003600604161004a019429040403100c605420b0300c94a02c6140381c103400214100b88554070410700f6840d401d00900c103400c124040003018804980065801100003000702c02c2c224001c01950042c4403010381c880240d0b8410701262100c49031101006404101000b0001070002000d80c494000d407005000340c03032800c008909280503200024801e9003c80d01d01542040d0307010380c24819 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 650966780 1250 650965530 650965537
    0x30a1e0c0c14011b110705130b01090f0f09020a17130516050109150516032c1e12100b0f010f09150216090906051503190f1b0e0903 58
    0xc1c044000604c2d080001038650313598549161641740308403000064031383c0d11b001004c50101500341300024071051103800100b036075110740c1012241e04080c01081080c00c0c200c1040200326038a0400c0141c9030004c00703000310b4512040e10702e01d0300102901c0381030214028500f00503846c121321400c00c0720310a640d41e140b51407400c41e080c4203042c04140079030800c20101e1002107120088400c24a002c038036003900c1d01545400341e0180982a800200d501081c059504c640600141d481060000c00703140e040709850009000c500340181044044150f000b1000064a4040385071240400300c0099403610100f4113103400c010010518054480c00f18482c0c001b540394012a501040e0708400e60b41d104209040c14081c41c11030074040c003034030118410341d403e40f02450141618040070701140540843c0460090504109550014144201e141814042ca0b100c41ea000075589a081b808421032102440381c0d8180000310b8804040040c140440140084409101701010141981c0720809142c00a03155132025035502e02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 650968030 1250 650966780 650966801
    0x9020318070f140112090c03120201051b39101404050601031e061a010210110d180b0c0909091507050c101a0a05030f03030a1e0c0c1401 60
    0x43c4406040c0f166511440005901d0601c4440201d201200ea9031421640c0178a54800d50b00c0341d183c54041004217a0a005050700442d10440c0b115411886006529103446507146100500c540c00e100080e841584202030b075003c501813129116211b81d011001d07512a41101039a03400507103414000100b035103a001e003050046401c0b50003000241e0031507507200d460004000c00c0403541c1c1ca0460700103000842c103000e83c0c040c850683d0f06050744084070b88006031520801000d0312403400c1c14181d41003510340005042c1d4032131200203031000c60283c1000b654030815041210303020703140200f02410051002408402810103143c103503542000395443d080345039240c15582000320811794900e0041022140b003803000e04940ba00840a407017285c0404440300044582d16000c1000040721440e0301e0710146060300c000c8004200c19400750241c404240c000c16200c2c03000070070b0780508603901c12078803c201100c868001550741980c1310801c801046a00c01402001d02c1074811641c01c074100081e4400d00c407060090340b4100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 650969280 1250 650968030 650968049
    0x320a14010e0307140f06070615052e0503060103020c03040305030c070b030408041a0d1401030201020d0302040803030c0304170a0203030a11040302010807030c0522050a08070803030403031509020318070f 89
    0x241d00304130400244849007520564040d0003480000c01040c0d00e482908800c80410a44e00704051a2800b4850b0301010944207a42480341502c1d428a8038407900402c910304c1c415407405e03079070740d81e01c8100680090045c038248030010310000c500402080130000c010001290500c085960040d0381d01240e089070700c411507004140a5003408104650580e081600d205200154440c5051080c2d495642c421030364100d0f000180c14203c0d00041040d0358050112000103409464250300c6c1a051000d03450366480050700300380c0c0d011000000a01440810651400c1601040038050b80d00d110125000755690000d880ba488d42034503050380701200024860440b0101e030b0b4103854100440e616940203400400f0300b2540c0200b400710810030410701c02c1c5216528500600340c0d24801d8140c6042c0010301052032199000303d0080d41c41aa014041a440001a42d600c154546804940c5101d5100306060006040c2c0c4402d0000d80003105110b210700c031075000544800c22101c122a00b040d910b54400c18155818861040d04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 650970530 1250 650969280 650969309
    0x18041716260d020a0201060504110706050105040203070c02010c02030309030102030408121509070c060608030406030603050c1818150a090201110a02060a03090f080711010206010906320a14010e0307 87
    0x8602c141c0181040409034000061200d6503000400d0030f50341e0502002c02005000945001001042e1145901510050720218110314007498050514605428040d0611000c0041d41d01196030402c103d07004401c002d40290744a0900785071014031604481041a0045800d0700001c00050b581d1a441e0340d54540102041d5080d100c0141c180c132804010034040d00c1b9a43c8603400811826010001040101066a80040e8541c5035062160070308889048240c41341c04424480d144d01a00c035080d09030010031200300540e000c020382e00e45918003848054031644501c03126003040400d42c11503000f9007445d4000c0c2c80e510712200500e040070703884050f44800290300030020b1103028840e07440381d030003409510b124508202402c81365480d114010303001a08129003901a203200c0d6100743d607051207514018250320400340621410941e400060258400c2d00c6c280e24030103e041c01c005481100020040040003405158031203482e404481e10100007542c0080c0400d0202900b18070a050000d9084100d482c00d02e4003040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 650971780 1250 650970530 650970547
    0xe0702120a030e0f07050a09050f04020103050711060a0506100216140109120f030e030a150c030b0d0f0c17030d09080906041e0902091804171626 64
    0x80303640101681108160365a00401c1400c0c00810000310110310395030090a00900c0c101c10400c07409100d40090300001c0c02c007000e101c1301ea0407006200e6041582401c000c5031aa503007442c00c5450380742c02558071040f4840c00043c0706002c1c1c02907002074021441928450354a0710906000c1ea9211100c3e0701c807038503905002604015140c80d1018100400b901450001c12035030b60788941140d400c5940406991000243c00000304158101d0301901c0014001d034050685044075880c2c1c034030000c42003940a920740b91521907540340399110380d02c006401000100450f82c1c0c1c2b80c4608007100d810b9107a4200715a5440c02000c0030507604c03100b5901e0150303a001c5000441c54a05103264640107000c200c201160382907003d01615003140d40d214080c10242001c12001c0072002c1300c0100c0c0010740490b945c400307800322b441005004102d850b00e01c4480c0388140e451641c1101d940b00d91421451106400205807160500441d1016094040040c4561414016079400e108030b00c0c030140707114008400b515101e20f0300008010101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 650973030 1250 650971780 650971813
    0x6080c0103051510180602010e0d0c0f03080601051204032003180613171c1b0803250c0204152d053703020a0504020c1c0f090e0702 58
    0x154644c080c503140300b0501d034402c441a012103c0e45c205a000d0707510f41d40501d40c034960030404014a5045450400010006501c0303103110140030050142c2040380c00800240c00d81d02900031250a5a4003070b10429061a00e4103004102c100340102010406032000e44840e034240300082541c43d102c40c00902104055134201c200162540a002c0305420003407070303220008500d00758400c041480d40384900a46034124030484000c10041200c019801800041024030404110318803100101d1036010049965a407a0028030090215005041c02008078410500c0004294418045400b1600c251030511000005000e8107030200001c2c0502142140040701002da00386103520648204540e18040c0c1c950107071a200862000854105445444074402a03140590246c5102802110780100081c1c2000c03403c43e80082c0707080600e4400c0512694020032500c03a85002841445003ca2102d840380c0582080d01c08082c15040c144040c08000c142110030020300c1d28001003d6900c1540c856001d07080e9021002800c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 650974280 1250 650973030 650973049
    0x70b1b09061b0303130c060201110d111308100609110306150d0903050a09080c03061605121306061a071b05090f0907060e18060f060d06080c01030515 66
    0x18600c5582040714040000c905000641c001c00c8108010340b105c695500f480b200158a81e8005000c581c540000b809203131003544181c40404100304008078140c091546240a50302403422048031107114041d00244c01c3d04c00240203002c60a02800900c022940e4845140031140d000504c40e050311400c000250551800d02c003000800e8101035901c41c10000d02d0704040d02114011201100403950004100740d050390405c80c80401807681100800404001c00042a00d400029200c086850902540031140c1401071090b22519840b985034036420b440d0005181c2040e0b088000e0903589a4a000c0c40891201810380b4101c002184940c1698a0300d581e503a540454241c2068a084d0380e07032090540800c082e5500307045140606072041c0c070f400d810f052160f0181d050500950018007406070803410002c0c1070b103601c0e00f40d41c824000c585010034641d8481c400705501c156481d0b0500d921800c00a14411504a00d40c400e009440b040c1d421a40700b80f400100550450f0300c180c2e0102c4620300c420b1545031451900c110712 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 650975530 1250 650974280 650974297
    0xb0a05011d0d0f03030504021309020d0b0c0d0e0718050603030a0e03070e010303110616020c060d0f02070305191b08030712051005030c030d0923030a08070b1b0906 72
    0x4010010b0b43c85190195540503000c400298807503081c00150301c1e241c2c5840c80b842c00c200d50100000002c550009060562151009044034003410001e0102c4ca0000c00b80c1d1780c4545668803c2c00300f0f02c04901a02e0301c400c240d0145407074142ca004c0007014803860358801c00e803091a01030002c42c506681c4603400e4070420107580317541e94180704611011401c0e03007900102c40d00a5104e511440e582c0e102036100c02e824400c00030212500c00c80403044c22000d15500007400f08107480103844182d550102d0380609400340c180c80504044550000940004041e0b00c10018041e0303050051194085508001086600440c40034514401e5280e0300d146a020071041d400854000d2003604004a540c0594020740c07064403000c0b076040c150941700090410590174140b00010340d24004a0182c554010402800341102c0007900800d45001d1a90424418000d0b004030b002003211001802c8640e2942d0524218009905c03420044540b4441100412440c034076858a484000030384090160400c07001d00d00380015038008800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 650976780 1250 650975530 650975539
    0x41a131e0c2102030d03091401050c04051017100e0f0708040809031011090312030c070609030c150f0c030504030e0105030c07060504080702030f120d2a030b01030b0a05011d 76
    0x2c0314006950800c2000030a00264602203006401800c1c45018242c2c0300702407410503410f183c1000062061242290103070b42d0102c411600950500908843c00403070284042c0c4035140c00030038800e800c03043d490410212600010040215521203800030f000401c10b0760441d011503080004200064600300241c0480c28014048a10310050a800541904c41e0f1082040070014001440c1006017420b0000c0440803040d80030451541c03d121461069600c81c401000d4413266031501450308242c82003034062102604121004d007081010700602c0005c12180d080035142d14071f40380b40c1c0c1c2c08007400790240512440e096152611f501d407000c6c3c015517080d800100222100308003000300500140e41481030074003ea000f02441500c4644034814107160012240740c0f082564402819208150052403c56041091503400416445044110401c1c2c24810b801071960111f0b039195400700f1a03a15a00203058004240da080c0910b011231070034049172441500450340001e40a450b1220342207500c41030b010f4071160160 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 650978030 1250 650976780 650976839
    0xf01020307050c3a02010f051204020f061b0c040b0a0501020303040210020f191401020403080d090c030b07030509010b0a050d03180f030804060f081608041a131e0c 72
    0x180c1441109542d0722408800c401313034a10005550b4440008009110700d800c04074517110502a0b480ca01c0d18004000920858820000c034901d51248410788048200302e080d0710707441410000402d07481d0b1341846074a0f4020361a2414400305468a000c1000c1101d106802440ca9500c0780d40030f000203281d0b10380c0d01400f0351103805200d2036183c00821007452000040d1171014101400c07841e0040402070301d4106a0141c0c1c3c01804140003103901001290400ca226071000610b060700c61030240b406619540c030140c200307603c8000700650b03103805401092203900701a000300b11006e20300303042044060aa0107500d81080206000b41c000034000c070140d40d480c3c00803102d940c1000380d48a040e416108000d03042150340d181e0100301003000d940c110014083c0c080d85c50810401603d0403081884c402618000508100004440820244500c10740e441d0b00c0d181d450b402014180c40d084002200c04441d243c0201c0e04180c1c1039160b1031601c0000d251444060341d01c40340b20341005290507001400f814070001c0f662201d41c00300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 650979280 1250 650978030 650978089
    0x905090c10020a03021c080612070e010306060e090a17090d02060705010603050712020f1320031b09060a0809071512050702010c09050402030a1401090b0f01020307050c 74
    0x80d40d034100d04071035a5008121103070891500a0801041c2101030603c9452411441803e607049000c450f444070050340c84040c0c070b4050048045c5451116441848002042030020060040907040a001d03038050311000724040c5c891040055550b407002501801c0b0254810800b41760344528401001040801004840544201c0d00003a0213648015022181c42e03540d03071420410480e0900c1164001c00701c13000340060486494000c203e40f03c05002c100c503c00d80215075005c0c102080c0e98000c030503840e200d0b48102c0c0140b080c141c0c103695a038020b4a050120020082128015081010071035421410203001642031403c5c0d040282c906000141c6407240c00e000b402404500e2107920110300401c100345a030b800f82842642c04d4000c4c112100139292504690400c2c0507180780b582c010440d141101e0040d100140d40e544c80d0081d5400030840707042018039644880e000005d903201640c10210350681e049810911218801005a035a0b21a110340100503070002c0038400d40c035140c245183d41c080002841c110302d890400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 650980530 1250 650979280 650979289
    0xf0c17040503060a0f14090309062b0b15130909020102010e0d021005070804030f270803030a050a0203130f03050d0c200304060233190b0301150905090c 67
    0x300e9203100c131301e40e5030541c120748a2041d00640c030392400100740c400168200300440c00d44134850749031045e004001c0021010300002c901d00c4295414021806c419520315500307520400a4103103070175140d00c1072110300c22078003800040400315614180805d008851007445e1103c4900640807101040e415550307200c441c6c42c0c43d01014014180040116130103172000e17612400c45a821104040e009100304000681000300094100d81078440210b40360802c40c00e2210701055040209031a803510100940000f800010f8804000001d54010b65074940140300e941d95400d4040308034002103c4041401c82c907041004041841a040c1603642402880c1843ca411102040ca0055030b00010480000402000c803000b108010900e580d088a40c2c044042d5140601d401c000075079548810a020041c2c205943c0e0021444600000c0c045104070004003801103840c128202802c20306958044552003030928802c81414601841100c081c150760001c03581004c2e0030030035044000d040c0100002c0d107170b114803014412155103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 650981780 1250 650980530 650980543
    0x320100f11030103030915030203040809011101060812070c05040207020f06071104050c040e0a0c1e20010203101a03011a2101090c0c0f031107090c0207060e010f0c17040503 76
    0x6c0d00ea070352040f8903055030000d5210503007940300c08040c814001d0000065034402202c00018007403a00c0c88640504880c80c030300400103030344030307a0389071280e03220440c91000000054400e40d030040c8201001c040e03540f41400241c1c842c011000394000800303940c12035503141013009460300a001d1030441944140b42000b20781120b8003510000034a1030049402c00101c0000303003016501400c051801d101400b01500d0280c98842d22941c0c1d43d0b001c1000483d100307005446940000d0f1079250486203440d40540a4403214002d6100b03551200c05100e0030342011404a41c05141a468200e803100e50902e540c0c6000d80c81c0e02042003200061404004c1000003120406618601803892072140c0644840c551500001e80704840114640c84180255800404089041c14000b14100f42d0107003047c018294030a00c4250070041c1030381081d0400c916001d9104944d903400a200707010303212035841e14424010040c0065070200c0b4451158000902511a018009402e220800b18104050b18141d03040c0b544402c002400d005c0e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 650983030 1250 650981780 650981783
    0x170409050a0f0b0324060414040c08010606230a140d05150a08060606030403020c030d1107050d080a0e1302210c04080a030e0a0302090c070320100f11030103 69
    0x40d20b6640c45103240c41d00b84511440c80c10104c00402146885183c0d28402400c402d543e00d614911840000729583c80e650440c5c0740c030101004861400c0d207480d01c0c0c0390040320709a01480d0807a6280240c049a510302980014103941d00040130301d40c0d0407603196801d0703c0d1a44a45812800c20480c1c80c80c07050841400303000f418034019504c03404903452a0605840c81c08403036210322640305865019007040000c0021a015130046419201035980303640d1400c003a8500f6000d14402e81d014480c41119070411076200413070308c4e140400c640030b03544420340d44d4082055044100c64060100300c81000500130013809110b805c0250100905008800303c0c0030760400049802100d245a20440b802600b070003104811000750f580481c0356107255040606149443d955080010001000c4c010304c5550390b401950340400c004010341c2d00a04030369041c50704801640b20f0341c00200c0220045808130a0720911803141d1589401b105a00341d00802078a4100505c90012b00040c50101807010740d40d42c20356440003081c80042d1b001c0d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 650984280 1250 650983030 650983051
    0x5060c12031e010801021909050114090f19030c06081009150305010618110c030708130f032d05210c1209031006030c06110f0a051e0a0b0417040905 65
    0x1e0343d14000174130300080847c029004105210761300340001c1e03800c80b0304012041601d56000d9101c01c400700c08a0703414040030030b07a15400b0000d040d071180c00504425003042030340d124103410301115546610079560306a0a907a0081082840da00070301c9203003480c0c1d2042c540030190100c404407942e900d40350182103c82d039130000041c41350481303848600c1026a018000c4400e41c03800300a07260a007030280d131350b80364080c0800c02070480c5030020742d030350007601c92410b020060725a40c1621920309070389240007000c1c5100c001051b81042126100e1407100140d450040c00c5079600000581108840d01c3c020300e8003034000180c07940100c8028000e032108040c0402030021004110480b841d80d805011003014940085911a80d540d1801c2910600004140d1030002d01159441e04005200000f41c40000c4d040503481e8000034010f1003500911410f01400152015201d10407940c810000c48481c000543c6814035460060610010040850000341020700000c1480104411850030244c03901c0c40c10b010781e81c00fa280c1c0500ea = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 650985530 1250 650984280 650984287
    0x43302030604060e091c0504082b030905120c010f02040f0e060307030812060a1205060a0612050a0212030702090921091f020c030d031505060c12031e01080102 70
    0xc0b800c01d40f1464020701580303180040e86207411665144d850384080208014660141c2207112958050307002c1c0c0307014000010a030799261501c9080c810f014000d150306943c2e034003454034800f034400e40280f042144444d04000038100800b40c07001406025440540c1c1c0c4200c540d80c4850303200941c211440908041d1012501d1484483c1c5018010070310100b02800161180e00300c2001000010940011140c00884030503d44105940d190002745c002d0400380d0265042100542c000c0b42042400300d21a84134805d440c1c0b0803c401034071103c42c00c00200f10104000c0007603100c10f10ba600540341c07800104603080703081c508480c0341c80b2159000c101224425510b80c00540d001a07251048440b4000503107a03403101002d03046040ca0304034000161121740e0a810080c2c0c101807100143ca50900c02c1c4469210341d000502140e040f10f0101000030000c101e01c8115508201a001022566141c8141184c10314407503480108105184124030705030550000e000b8030030041004c0124460700c0d0944254034000c04411000585 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 650986780 1250 650985530 650985541
    0x10110a08151c0203120c070e0606040f2d150c060209040e06040302190c210b01080703030e09070203040b0d09060906090203011a011e050904020403080a1707050304330203 75
    0x19054914500349081c4105002c1183c00d950001450400c03580d02c8d42d402036041d241e1102045082c45983c2140c00d500315096008038600c031600f01c0744c440a203403950803d44c64001007400045680d03514055101024403070380010004c14402c50341045060f005032030051034103480307c00103000c5900140f2450105d4101d213042005245d0148003000301c1210030145001c00b100300396101d1030403051030b0066503034580c04d45800c1c81804400c0c5401003600e680c4a001000b403540c4540c138540d9201d50303502c021000104003062144842c00c0c00c03540e00340681d644c0e07002141001d0034502e105409400841d070b0310303220a036241d00000119206001d04507001e8040d07540050191028014942580e034004540804c1c0b250070345607584207980c8681c401c40b110440b0800074901e10913002c000c030380f030780700c0c02c0c0d902a40540045408424424200020101e041031511a00c00403000c1000c440300d1500101c1c2d0b418040b40d81440090003044102c0320b0f0342840d04035444041011043c1c443d8001039840f1884210104036404002c204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 650988030 1250 650986780 650986783
    0xb120a05060a14040204020f0d05150a0f08370b1005030619020c0708011103010501230703181214010608030414100315031410110a08151c0203 63
    0x10b8102420b180d003400f0040e1031605260111030702400c024020f581c002100e01e202581c0c0fa042d07810150710301d8000d10260500352001c51034070885440503442240a148002802240002c0c644103c1c0c1000000d06401e411841c0300f00e190701d007a604440e02e01c03a001513041d410607090b03d00d000003503803140c2a560200d052040c80003c01481d60303000107000341d21050500415410440b404c01034101404800b5a42c2c280c440245410482180e0014851f0b6003443c450f480401c0170100954140d400aaa0f60020000ca030302440360b072180b0b05030420118580802c42c9001280c4685185c844030810401c030300303041c00c0d50b0f4450f03d030089840c142c1c10340700110380c42505c0301c2c4240b00303004840040100500440c103050800d03012000801c15003078054451141c05035201205030003604510700041c1003400040c9015502c1c00d0100c40c124661007124802d0140107510300c01a00b00c2c0c400c11002586c0c0a518500781a005102910340c03000140182d003111694127141205aa01d00c44040510018152443e00c000c48610606 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 650989280 1250 650988030 650988043
    0x30705030d05070801060e010804110f060f0306040510061e0c08030f0420010230030f0906071d060309012a0305010f03110d111903030e010e010801060e040b120a05 72
    0x6c0040010300381255100340e9001040c680c0142d0011040701000c03e11400103070610810b4050365410a070007040d901d50800018005d0341c414034094600340641d0745ea01c40c04c402404d2840c00381c900401c5031070019410152080d00c90440c031812030304100d5010074081c0c44d54007140c0c004a4034050303c00030000410080001d0060000c0007008120b0004800211440010b501c980107804401742000c60041e5171f4080b008040d281103082814401010742d41d003040e0b40d191144800440380390460784200e00214814502c540c802e034046000740e4a000d00050140810082d59500141c158040c40d9268619841c03020204442c0074003040b10020083c9102880c080d020b02a150142e0048005d014007660400c0030030003400542d282480200c850f021020803500e000040321084c0b518964019001c50700048400c4c82e000c500d1784c107407030180d02c90001c640860f2004403210059072421781c0c0003032420300040210340e00411800d0356643d001080420340c01c80d81400300300d03040900000c11510b544110310030000d001c0d050020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 650990530 1250 650989280 650989289
    0x9040b061c0309050415030c03050114010b0301030b06150702091017030c0309041104030611090f2e140c0a1b03050a1b0308120402040b0d020a17030705030d05070801 73
    0x7032249081154401810b04015481841c0c0a16100c0142c00c0500c000c645c0e000003c0c540c842444004d9540301c0c01c0c801c0c020248030b0180580c02d0030300400402c41a031640243ea040301d034050140349141e541c401c1404907000320310200c040a20018401c0302c006a481059041c81805070800f030800707561038a0407101d9a036060f031500c0e0266400810045066481c0441103968045045d0f60108000030b00d00c04460081c82075500241074130745810010001c40c80704600416910b030f4211881040100f03001708000d100940c1d0005c110304000d0000200c005900b0f02e2110805421a9003001100e03a40500e02090642e4410740415001d50800c072080000c0048801e0783e86411850011140e0815055560302d0b650303460560381c090010002480c4181d00038448240b40400f81da449441591544800900c0d00c1d225002503504030b20903414400d00c807005050000c1c40c480c050b50020304244a00703150100c4482c5002d845010010240400c01100010503420002170401c0f03908200001414036141030028407000c0103801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 650991780 1250 650990530 650990569
    0x60b160807062c1228050705030a0201020405010f0306080c0f060d020a12060914040609110604082a0d1b150801030618020d0312060801150302010201060f030c060503070c0209040b06 80
    0x840d5030710303108170401c0385054607a0106064a00910340251494003800c14014404d03c4002100c0e0301c10369042d00980100c1d1000c0e03c072410300107040e01040d015118a40201c00b100d0b400b10001441e546081c482c18407400e0700140c00f06107480c003140d0020b403c0c2d070311074045c641c00308142ea048041d0300021351080a00805a51804101d0040501746105c60320b0406003000e08041d4494000400780420400e2000350898020902035440c1c2c0d6680c1c10b60f4840814140b040080600b9441150000b4458805030f480100020111b030380c0440320b40d403110f03903403240e419030401295036580e00899031405e42c0d038002020360317107a0310341c0d50729985142380100650350504401003510082c80305e07100c01038030f604948034245076060504001081115950500030034007076004d01815070030302c4000d182c05070001c0404001da034001e9000b0300c43c1c40d03212a080d00003002c5620000344001d80e140810800e807841100516004620780c41c108a05030b59580000c0e195420950742620303c2a8180207203d00340ca40b07461a401110018239 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 650993030 1250 650991780 650991787
    0x19091413050a020120060106091e080c01110115270908070803150306010b0309010605030307020a09020a230405010f080717060109030219050103060b160807062c12 72
    0x740c6103601c984032008024140070100c101c04160703440e078100071908000101c00302e03004c40d03035100300060007401248150145060103254104500901b809103c065542c1d2070700400d50b030107030307140110b4030496817206020880d540d544901c8440402400303010020150060341800c0c000f4041c82c40b21007070803103c0c91000428a40034909c0001241c8009888a40386c01503101070700d07540c850045060a06021140355458028180089090150344010307501909240d8000c00280381c540c0c00f455a00d100c1c020019502040d462000c0003001500d80007400300303100b41d24041d490100529400d00600548100703094030528046814010355178442c240c440c0c43c001600d0050700c00e080050001d800c02c24002c020840280d000e000040c0c1d242d0141002d031000b5540940b40c003000c1180800c41e4600c1b101c15004981c00241010b500081c0d0044a0080c0c440c1d201d032805502c1001443c41d80c4081c02c5074400102200c106d5294035404882c18a00d02c04118404400103040c41c15210310715004d1300b04004000403090403d03060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 650994280 1250 650993030 650993033
    0x307030b0d030c0803060f0409030201090b0108070303051c15060905010201050709060509120f0d0815010f14030a060b04141003020c10020912010c0903050f060c09090619091413 78
    0x10f01c860b00800c2e00985110303503e031034680c080741c800d50702c4c80c80c0550407504042c0342408240c0d05601046180380542001e02442e6200c8d4211074803000d8620020b0000360003800020101d07111010610182c00b20604c0010341800706404201000d2400e82c01140803801c000030802141d40c081c01030382c1d80680c140c5007041916081c00c00160260060f11004e034001c428201030320901003070420090307010240c030f041103607140d001041c002421603004541710b0700051900c48214101c0d501640b1248070101440d1503211602d07821b400500603139000100240041a12808000f5884c106a0014009010002140881e0206078030602c9885104e0002c2070082600c100403003c442000031a4000bca03a0b00c401780541d45070700c0038001500380e80c00002d07211015480c015000201c1d5400559034001c583c881e03020b03140781040d0500c015884801c1200c40d4182302c0d4081003110054540818035641c017950050042c045441c100e00d9000900710150000c400440e640e6411442d40e01d4149501640001842d02101100003d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 650995530 1250 650994280 650994287
    0x215030708010e1b0901030b190320100809071a0d0b03070b040605090a091b0207080118110d0f1b080f07060305061c0b01030b06040b03070b09011101110307030b0d03 73
    0x1010303011080b400001c203092217035a2103a0018001d07404024180307100419000c488001d50f010500c411038460001c901004100404180b101d4035000c002417211b610806041d0381550542001003207481300c3e000319107012400580600c01c2c0a10642c2e003040a50b291624401b072030040700c03c5403801c00d100380d03c0381404200305034a104c1104c0a45503075240640c0c861205101092502090390400d500050030405c3e4001d0008c0170b220b64043d0505c0d158212100260340e29610b42c01c0ba103948046130000c800120340c807808151b00500c02c000103c1c1c013424445078400c0c1c2d900c4a840c03070740b101130b01118071307501400c0c1442660082031800009001e480c4094040040e03049240d6548400c1c80c45400e0a040d100e074001070641e902c4004034680e102d005004807074402035614140d003162200f40812104c040b01440440e0090406204540c5e130f400b030240c010441d41d41020341e10803660b0030005032130741005410300310380c01c84103801c1c0150000c50064196070b41d141d0604410250a0310640c050365130180d1480f00404001c00da2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 650996780 1250 650995530 650995561
    0x602120f10030311010b03060420010903080301121a0709080105070f050301031b0503070b070c140f090402043815030a020703020106030f030512090601121106070215030708010e 78
    0x515082c40b002140702c2c4c80700a400b60840c0c2c80241d034580151800c002c00d010255480941c0035600c210309240304c69281d0015030310503040d8040070b00625003e00c018424210011005944079000346000710800c090084881d4403c0c4040b9003200c001030168800b0400c91200340a44e81e0820310301d04000d0070f4110401c038000e10a0005200c0070b040c580206000c010b12000000d06080a8240941916a19512071405646a600c14101100d0f540106540043c5944144221103034100000b000c5180c42c517904010020070b40e00251083ea40266521407425646000c4a107040203020710051303910003d107106401070385000030400450300580041050945000d000c0e03044079481054408016200d981c21309040b4010090740e0002090484000200340605070414041c014001a44601600030366a000c0d0258542d00288034a4281001c01c41e040c0000960101c0200c07100350303015000a044c00c00d01d4000442c521401941e4980740b40c0000103000b04030b54492122030141542c00c2c0c4a849a08100b0761000034902c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 650998030 1250 650996780 650996783
    0x2120c0f1c0605030a03050c06060d0c0608072010061e0501080403020f031b16230f0441060d02030109060e010b01020c04092a0801090602120f1003 65
    0x1820301c548500140c0303a100300040d2602808850307402d200b603d4094082c1c0c0c89666229a070344144000200a0714012403c000c030316500684005005182139019a04120b004e04000c081c04144120301e59400e2000b04444c904004a10042c0702e02081c20000000b140d000c2d0300000b9035542107960603440000d5003c1c074801111020b20b000c0506944500301241000030046042400740000078410310072428070b0fa00c00a524220801b651a10b150b000301c568030a0003a482225090500707540b00796214000c10f109801104d2016061030446c20001c8002411601e08120a05008804060f002c000c3c420340300e0402c291282c49807000d030000031a5010070071100c100a10142c40350050719507120841d1800e42044405652041c802d0201d91313801804c450180c034617a801a070040c414043c2403441c52800780629a400c0b40c0101803500b19002803240c0441c0703426075494284a1004080700012074110034802c03001f0840c0540401600c80f503034020a50b0030f444002e010b24a44400d8542071102248014191070100ca = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 650999280 1250 650998030 650998057
    0xf05030618040c0b0f0702010e0909120a11072c0c27120c1201091502071416060305010f05010215070e032506031503170d060902120c0f 60
    0x3941d9500c0d00c440e5848040d041300100601c00700c1c0c046066510f00b00500181d51003600c92181e1039018905201c199101145c149030305030312400c46c01e00c1c00e400c030300c1c014000c0f01200d01c0c0c030341c40150002d00154640078043c3c2c001240c1d201c1c1007030304031180748504070300c850b009400101074441410910020322940c06811141d9003004403a004544090122081201c44d0810142041c1091045111055120003801c480240a0500b4007200c13400b42c4818802c0603c100da00440344003404500c1da1008e8001e41002d14202e816501e140c43c1c0543c0520108414000e2901c5014100780050038030400409882d01a480900c6004881d403013400540c3c0c000c61401203a11038240744507610794484408503150a0a054065010f015215404d8600700c45502c02d080c0a000c50103140c05581c0d0740312021001c0301d4441403071500d0701850007018000110084600b0410391607080800f41003805070704d4000202c1e0b420380c2c090b900030381d0300203440f060603840310100c198000100020907003003041c140f8030346905110b02c07134002114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 651000530 1250 650999280 650999329
    0x616030606120203220506091e07030b060303070501060f08070605040501080402130b100e041803020a12090b0f0c190213020f160b091b10031d060c0a0f050306 70
    0xc2e0055030400d42c0e000c2085001080801c1c1745041940d12001c0035070b82c8290700c0c004c3d150f4140d6903002c400001e161300014000105403407441d40d254250070000243c20603525000410007500802c00074001c80000d8502107185141607494041d00b24039000b490381c008400e104040c84200079607a0429031040c4d0041d0161021030b0380d080d414115100500c54900c1084d48644558107083c0380d81d40c0f2085e80c4002d0201518100006002e10301c45d141c140d00764080040c0103a100d01c60440c00070354100d89042048905040c0301c6112910b41d4145216a0003002c928408500e020400c010392040410034000c0303025510258108040064010440848118800800b03503500001c0740740c0010170340c008448040d40c250b00e091450048914140740365040980e00340d481445101401d03500c07a00300c1e0342e81112103040107001d40120320340d4002c150301500c207101004090345414030402c00034907020300440380b0a42e41179080a0b51780407842e4015040d042015415801c03c2818400c01182c0c0d294210424041e89104001d483e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 651001780 1250 651000530 651000541
    0x807051b0307020301060303030f141501110f0303090a0b011e050402090312040b04030b091f0906060314060405072312030403020d0b04022d0f041d0616030606120203 73
    0x255101c1c8010094040d1701e00742c000400e150b4940e1010b002c03102c06200c05c1c0003615411480400f482f90580e255200c1076000480c800803903000740507400880d001c0c071064900c020301294000f82540c000f2903820809030810691542003006200d10a030150141e01882c1c60b041000400d100c42140b154001d441c0120342c00660944683e0b030801420103210b5103071403a155103584541d04551250018802140c4402003030b40031503040100442c0c410341c0b90402e01880e0b400d1f101d80025030405002801402c2e9034080d51048048041101d02d0800740c500a02c0e00020407090515242180c50b1202c0c95002600170700c8219200444c0d011128021481d1100491329010b4201a058615045200b65440203611480203001801080008841984164021a10040390a046052441c10b401c2030b196010303a05c3c5410841100a4078051406085414001e4000100e1025012031044902000d00000070f040c0d000d442006011000b804100a401d0401d24003400101d103004000b038031900c4424107036200d55401000141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 651003030 1250 651001780 651001783
    0xb12190c0503010603050c090a020c0d0513090f0b10020102130b0c101b0e0102030406090618051021060b0301030f080d0227041415040605030d020c010f0807051b 71
    0x3406008014020050ba40e0360b442c040350f4601d121003919000340c010500180003004240f0940340d1100d001805401050a420400c81e10f40d07000810041522428640c0410007054610440e0b00d060b0751401e00090250701941008120300b019510b210031a80100421700030010003030000d2048610600c1490b46074601494100d05104611103500740c00307483c14a0380e4440b00c021254203180f510050700d4880018035101c004980340c2c4183d000f001c0c0400d844143c100724041c0301c0d81006030b01c000d501420800d61a1544002000c00c0c0c0700c844100000354121440e1070300080f590a03d07280703c00125504110301854404501c0300c0e80014031000d00200d200b00c0f04001800050411508a160130140844d5140c14628900140782082c01c01e80380354500c1d03400355002904081c8201c0b2407030080700c0c5040c0200e66441c407a041100c15141d840c140c00c00e071103180005464a040007801d5020f04190050305401201000040c80704c8042158541001444424070803101c0c1c020084502c4501c0c1000465803102e146401035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 651004280 1250 651003030 651003053
    0x30311300c1912090f080c0f040e0a0c061b020904062403151a010e040b0d170915121501090308070b0f0601020703021e15030103060603060b1219 64
    0x10b1003955400e90081c2c1c00c00460b03807000803485000e510b0702c4420340d8071070719641089002d0307004402c0140c5c0100c441c403c0d14607042007410501b560080010034078905152145007042c2401500b1038100b0034070402413000940048d40411042050b40c0d0400c0d00c41c0346900003034122800500043e0000382c2e03400c05040c088440000c8009100115415941c03410355910700110380e01c90071031807058114135102281080802c14885202d00760016542d0111403d07401c0d04000c001e0a410884a510111455002001034006804003031002c1e00d8003141e90b141c91a8178240981c025004901b49800c407070822405005604081080e6004000c1e000079240380c400c440010b9880403060740000c6c022107808188075080000d42c1c040d287c03240502c03d040c060b040e11900c0042e6501c280c0d40c00025030068054100e100201c0314024038281e440c50041c51500d030402004040400c1341c1c42038006440c0a91030f182e042c01806414010038405000c1a6004500319000c450101d80711200e0600c21489291654040b005004030064003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 651005530 1250 651004280 651004303
    0xa0c45020903161d060f0907110709050a1401081f11040801020901030c022d011b020a14031305122b141e0307020f0106030311300c 58
    0x80750310101102004001d010300e10f12840710b1035591907550244d54030f00e02807641c0c090b00020780a1154503461004100d0301d120700400e14000c011209040000d0100d08106003001440484c4001510b41070a41072181644e040003059004001d0130f03401040520703800115008801102a01c1007203424011142c60b010b1b00703004500c4014140d0106000c02c0704141035000340a8100d00340c808000002c1000c0741642c45000401c0e507201e20b40b40b101007a299143d000303000c01a035100b4103c000285440d42c140c0207040c0c3c0c00e800d03403a0001030740305680810030031280c4c0c1d01d04001a400c03d80118140104801d44d91300c0e801a40c01500d02607061404a4026810100502c0684002ca000c6088080901c1440d0040b1030411005410011701c0101c0d4107110241100202c4901e54000b251030b81901241ca008010240d0002e000c160440c400c542070f100b40c00e102840303800b021f1446681d40362070b140b82040700240780c1903620a46441411181e010300da49030b458084030b220051051416030780c84113026244541000800d500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 651006780 1250 651005530 651005533
    0x1510050d0602070b010b0a1b03081909050f07080f011b0e030a20100302180f0a1502030315060a0c03030b040b1207150c0f0303090f050a0c45020903 65
    0x802d030005817001921072170700b4580c0d80f1005a020b40071100045c0c0812301d000740105442c00040b0b4401c400c580048400740104500c0860383d240c07d5030381c103441d1078030b115003c0f030340354014090034800001d040c402c4010511018000f4800d0554010b10080c8032444000c1e0503040c0b0100d9280b40c40b0703684090090820042c0c22a010b200340100030b024080d801070010851611440501d000350031300500034400d580031068014850f0210344001030900005184002c003280e803252005c5000948a020b0076201006d50009501071503c0b4104104003060a0803141707003a51140f4000d0100b08821580010401a040e4240c0f6001c2000043c030700104009000d40840550000101d80714075540d50743c00942d44040320005e40010b2000307841901c0850309042c01c0b0790010240070b42000300102280c4290001e8024601032002e0790781c040620381d1110702e403000145084510b41d400d120b003002105201640c012000d040c04107040d10b4240c01da40900d0880044041046514000c0c04000040791900c0c0e042d126030305030140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 651008030 1250 651006780 651006803
    0x11e080105070e03190309030b250c020306010f0617071107081f0c2007090903030e1e1005090309030f100501320f061b1510050d060207 60
    0x8010201048030340428000c0c885c414202c030381d0310000388509000c0382e0181c1d689085d003415076031085081c4001401c000002100390440240c19158045a4100440d0030f840b10503121070588145402d01005901c540310702c2060550401c020341d08204086608882d40103240c00c61b503207805080d1000c1048100741095031003040004249480001240001c1440900050264a51070055182610034801d03010300007078000c4d001d13003103c0340c551440c00e44581080015548626291603082e42103450410050300025150481d40342d1100d8148003082041b001010b5021003040513040d041d1390740c2e140500c40c00c5020360303c4d4001480da001c180192881c540c0000c0c1500d89001400b11000c0d076515800480a90300b07803805000099000d00f614180d05551025000b034800c00c40d12140240f84882d581c1011500f16843d4004400301d585c81b00c005100300148601581030041040c210f05d031400301e02054103c0d88407a184140041c101d010b60000e004c40344c0454040907600f15a18010000c1d00a0403001000b44a001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 651009280 1250 651008030 651008041
    0xc09060602030a1d060a0c05070312030b04051803031501030b06030c07050f011503081804060e07021506090117030c03040306050106110c090604020a09030c12060b0102030a08011e080105 82
    0x2200405078a800c82e5104d00410041c0884040304140400486500c00b4080010b0980c5500426203516414014020303610300590341e8503242c5441107810500c00010b9034808080c0036500e81441040c2d000100c4010800740103003031041096682c44050710102c0c40e03000c0c80c840ca0b074250707101e90072189510b0b001800081c0c41e8185400445440e400200741121103014001190500760f20511460700c0310341d0601c809000c0d441c0340d516081851f50018400041900b0482008211604c4a00590005001c20110030f041d40c80c0148009040101c05042020b0340c0c2c034403000b4001c0d5951400c6400d0b047d6004001004220000c80c211310f07285104a0048d05154000482c002003031019030740c405030407504107032110088048000ca07010b45071842c4c0c51009510505010110b055030810358080c0c1850120fa05080000d40e8880d1580104c1c0507240c0d102544104d0700c02d0046080042030700072407a0440007030000b0b504140e1550800361225005015010310054003240b19181d00c069008042d004000c9500201f1060406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 651010530 1250 651009280 651009283
    0xc0c130b0a060c0b0105041a09040f050c03010b010503010e071e0c0201140301080318030304090f021e09131802060d09120807021515090717150904030c0c09060602 72
    0x10411034403038204803000003012406101c030301c008203520102220461307080904100050000e0722344041d64407011001c0c0400780d1504c1c00c2e050301071402101c0f016940821440c01e04d10701013100b50302078042c1e41401d010208698111054905407492820101c00d20b907074004003100c0c0c02450440120384202000030b5200596002084900c3c418002e90b283d01d440b0042d4040c442d02803000b0302c11550254001c00c0f0604040c2500103100d030301c1d464001d069070b2505546462101c142c94504840e100e500c1d500091a0701c076428004980740701420020310b01d03810901c11000061001a182c240da10307105444507201c00b08156509054504150700030702c1c20781c071405c92a0b0024018503403401b085070401e65034a440c140302c6001d2010944107071019801071214103817511141c1d88540020b130140004e4404800240020360383d0b602000d21413405075861508a00c2c07021044000d40c44d000e010800c05610100890501e41c031ba40886580c03003901350411601d060340e00d1070000e503040f55640c03101580794034000000c1200f550 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 651011780 1250 651010530 651010541
    0x2040b030412020118060914071d0609070c020d08071a04060c0c080a030b130905032a030d09021903080903010b010318030c03050c010218040c03050412050c0c13 71
    0xc034400010515050403e03400c88240e0700402c11011022049000001d404d5042403a0701482801c910843c0c043c54217403645030080300e801c01c00803e10441442012845503550041c0d0080e0200d0b805206803c00303c001038180514008080d02880c05011a041401064800c035018944e05c14110001d00c450302d0700c1a41c2c5c0981c180e408640c59402c3c8900e02c00040e01c910f803280c5c103407504248075a180c4920907070103400034644950890741125502445200100080c840d400081d07000f40082d60b80d44500d00c43e440e174903050286403035194240f4031781c1141c024a000000d640741c407254514005115103550000546052040002012946455102004010603c0c02074000640c007a002802a00c50420054055030884c6090850041c0f0310b51200000c6446001140c84a0307010b4149640340c900c031003888609aa01c1030301141e0300c0c01d4181c1000802810580f141041110701c514040001e410700c0e40e21480c11071030681201e400c2080104030728680b03074003d11a019409200501020003400c480c0c415101428 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 651013030 1250 651011780 651011783
    0x131a09100c0203120117011107051605060f04210f05010912030b030c10050f04120516080d0809010609020705060117030a0f110c04050403020c090a1e0e030c0102040b0304 75
    0x181071040d0a0303915400001075034641441d40700202d0060703091014040049184201c00009592140d40d48051309240c0001460701c00d02640140c0f0403100c100f00443c1c592181503002d9401038070308105629031403200c00140c6081d18002e400c841182d0100c44840d030004450014050303c14000d801403907042150551200d440640305030f003580c10045031060190202c071407917a11950190400d10801400f0710746192821700c0001d140c04c20130f08001c4410100825500203810030866203d00200c0300003400710030403151600700f10307040c071180080741001c4909840301140010301003840400004a021410300303400010103004c80c3d01e003c64030b491503810b0031990344c5400c0c0318048075910ba03c24603040c4030201108455440b405522000b2030990b5407003080f41d4864912140f00354601840381c040d9050350710b41c0503003409140241d000f091140714400400441c20005441c1402052500c0ca150290141c94100644e0b414112000010b900c4183d583d19411071240000c41460b40d44002404507604101c0b401450103103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 651014280 1250 651013030 651013063
    0xa15051006030c0c030503040204111204140303060105071e05100c0908010603050319110318010f020a12180315290f1309061d011a09131a09 62
    0x40d640d800c4168120342400240b82c0004036500d503c1340109004900a54110388040c20004d0a92018496126180c000b90056181c200b10b4405000034015150000014194460b01951840c101840007030200c0c405c6c1c0c94000e007089805840c0043c8604101c941d01c5c0415000800c2d00c08a03441c0021300e0006200c0c100305040822170116012171003100c148516400e0345e500a0046241c103a0400751503241030807040c1503004000e240303540d80e00a030074103201030a400720a603108148800c1e83c4100160a0140c5881e22400f154060710110010962080e00716960240714100280000900100e14600080c0c0e50400b0707202d003109a007816510343d85940041c40706100602c0e003414a070804c504444940702c40407100c541c403072212080300480b80340400204041d4540c0c000c1c0080c0307001d410780d20401a140d4280030407a030f101d81070540724040c031004c0c0551301c00d081e03224500c0f10b24401603000184520f41d01400d148001c03168500c0072020410803001c156640301040740c2c9180c031864120861651004120070b0a000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 651015530 1250 651014280 651014311
    0x30209120705033009030a0c0306050106030b240c0307020301090507031e03020d030f0609050f07031a01020a06180506010b2a06040204090c0506070803040506010f061d030a1505 78
    0x41d05410044a0068100c0409840c0078510714041010345801c0030203415418040c41e2541e4002901d4031132310500a512860010410f580f6020020b4112070581c103180340204441d00c2803010000d00900e5201c0d03243c040c003903d142c07102d00140440c2e00d1800384000080d01507280015907000e200c000035520040728401d2412003802840c110260140b080383c8480180541e0100f052404a51b0081d00242d070440d08013400011101e83d0b411160040d41c0c81500c0e0b00b040042d1f40b609010200f035040c003030b1154859000d007400891109080000b99550704190014010303d079a144501841c1a481e01c52248003a0402c0071545c00d035850f50300c040c0495000c00403c1d42e1083c5140040038515944c0124040e24140c143c0280c042981d0365020700002d00900d45080781c505075254004140c80c0d9032980a002c440d401100c15035124034003807400514050041c4c20581d050481240c041241c2c1da4480c4000e91910040d000c058101c01140d40803c1c6401c800250003001a013102c52034404039803041c4d004901c00d500d4150300b00c05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 651016780 1250 651015530 651015553
    0x5030d110315041b030b010507210e0f0f0402030406020d0e0d0810150f03110d09020301240320030111180108061c1406130507080d08040f0303020912070503 69
    0x4031510007800d61507a5181004d02c0d409240640d008059140701814424030340380007540c80f8a80289480304009611101030307452840d69611064040c0c1584098581000040b080c20003e0703000104010940c0c81550000005070400890303406403a01080302d403c0a004403500c8000f411785850b0290071403000110308030001080500b440c100e400895000c2001d0005501c0c40000850344411100c490005150f142c58190003a4024940140059403e0b0000080c0c14122441094259035940716006807149842441d0719a00415960f08000c0b81d03400b00b00100341c40301d10144e118105091001c0303264035500e4036011840c95100240101700d182800d103594107041286100540d070043c4107444664000100390a0744c003010315180c004008160146819038401b40d4025400d82c94141c003102d90300741c8001c924201c1ca04100080048101500e41c84000d00603080b42c039007004000d040700078809891104c0000100040c907000b90b049030304069001d0a22004551001003455841940d03200341402880f443c190140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 651018030 1250 651016780 651016789
    0x40302130506180a1404061b0507080427020c0d0806180f0c07020a080d02120301081906060e10030209061c0803100b0c011e02180d05030d110315 64
    0x510525000f46102e80308600c2420741e040b048801000707107007915502d0050040030404225007600c1175126081c04124405002c1400ca0f000d00d40100020038090203004810014500d20309450548000285010407c0c0d204116a9806815420101c0b43c2c203100040300b034084800824000c8420700701b5240c44603d5141c171014440c05005203018483c03216070000100309020b070181042034211001380703150303820301d100c68002565403005948601c0a646c06213844004140d010701c02010001440600d05056601d0300c00055100d2a980c0c55404c6200360030b005c10800c200850b1310880c09011203210b01a00f030b26040c101015551000d000c180d00c40c00983c00006c0440c60400820181100000c103a244007200c50355440c441500085c0c241c07065021744a60220742c1a5684015101d12040d800000c40d2400c0f5400d4101c507441a20701030741c0101ca004010300c0707205110289070f0350003184054442daa0000307242d0402038114019490500c82050901c3d900302d14002000014501a40100d1341c1421103848090800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 651019280 1250 651018030 651018041
    0x30909050601170412180906030615030b0c0a0504090c02030d0f1b031d0a051c020105010518150613030204050604020717031003150e0d020a0c1a160804030213 70
    0x1540c03202082c0e0b00080002d0300b54400a025008070303090030000038140542c000013007050ba401400d4171f5607690004100340001801641e40c0301040300700c9028514110f803a0f07d078000100400c04d4038500000100d031041c6503c540c04841c02041c1c0a042041035440da104000c6d201c1d803041a441e07081c4c078200700d0b0407007a00d0481d02c034600141c406483c0a1541c04800b220540c00f411040da1900048007e1011840d040c2e1402d01807500300d01c1c0b061001d090b681d000083d038070144402e41082c0340e00710380c9008018480f0f0380300ca83c2072010041400d040e1100568070802d500d400340341c40840060b00484041181c1c1807410b00700c8400d0782641e1084030b043c4441c0e0395860500080b805461300107012130003084091030a035000ba00046801413400a4240d03080e03502da441710002c140020500b1314102d56205104114a030092001c00c00703454651014040c0c1001c00e86415840101c54083d002e200000c0700c1c04102c20b08140f00071101d03003101140c03100134807038410f051100040c1c00c1440140c1c01111908003810f9965100c2c45072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 651020530 1250 651019280 651019307
    0x10e1005030a090204020c030a03150b0408030405010c151419051323190b070e031203060d05070f0311010c0302070308030a0b04090606090c111e070b07030909050601 73
    0x121070031640c940400b080900803041069801550030080003c50800601c01810951003a0720f0126450b81c82c42d80c00f00d4101102d60189912040034001400080008001c9404a650910f006842800142402a088070440420f088030501e0103044da00e95507444182030788141e108000b589007071041060140f09442c400c40d500f440b2903400d2464440001d04030480c4090581e800030700442d83c8003407420000e01d807018040b1008006502405c0349001c1108050105911003000e103081d40340080280f011960341c3d280740b03040040c15100800041c02c0c0791a0b02107407c0820707801c00b0480d0b40055903075003130720500c0c1028042078036418886994201c03154010041054a140c0c994001d05000e459602c0c0c02a81d50400340050380060348902c0056401d0791140520b04806004080000343c05140001580c00c4400708803480301800030407060980c9103c0b02184c855002c00c40307614048411101c1d07120090410031141c00c0604418030100d650803d050303215480e40709603110b00e4001c02072515414010340b00c1040c2d4011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 651021780 1250 651020530 651020537
    0x100903030c0b0c0c0f1b0d0803040201110c100806181605071a0114040606020c01120213150c050f070e0c0a140f27030d0815031506010e10 61
    0x4065001480e8410656400441e180c0b0300c40c01c04031584c450606020a92226a003d58071503158140c201c0704000701188040c40841c2c9090819000e070361818502d0000030000307070601c22490a6007201031000e000001c50544028921071808020300c03400f030115241a24118000c8001058010311031811050f03c502070031341012490400c4002100850700b40c0c0c006102120303225a07a2003c0800108540034080c00f03440d8041e0080c0c240f022030000d2100325030950b401207003154084c501420751640c0103d2880320020301902d01690350240c05480611078091648256402644000311041c0b59a01002e0291800d20a4040e0f9080003d5025510350f2180c0c24003d06004030802400b14120445003402000e480307896040c1109681003407400a0155000490001d480d008009000030000701801d0342e500000421180e01c0c1d1500141c00046a65481c1d20b0740827009000d110008120050f284020358a03820f04000d0450703441e0715113000114004201940d200b80829100345d81c100c1545407000d030228103000d40307a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 651023030 1250 651021780 651021797
    0x50403110607330606080403030c0e1309060212010b07050615060904020307180f090605031c182114011407080c0405092707062f01020703020c10090303 67
    0x100f0001c6860042c6492002c00f00c98484491040c01c103000f84801040180c1740c1801c3e61421b070401800341e07503041c5006400c001c23489506c1c0c10181d84031074444105040c08400000e06600c0b52401c54001d12480e0092544142c1010001600668110042c02101d00c07450545090b03848a029024100780c1c40074641c0d03441082031299424034240381d40615403109207403800a5260124040d1034190315041e4100380504d00b94403400b8007038811640612030062030300b43d0003412803040003d05101c41c40a94007a94040201040c0b02c1100c0c510800c409402070016280340c1c25500b80c0310b184540c001c90300c07400c0403201c00030404400002e802062150483d124030809407074841c1d5566900c01c544c0c01900030441042c41806210201c0c1c203403200b000041c81114212a2903400071400092804040e46030740e1403c04582c032000c0140301291f03208140364517101e03032000700030701c0d10010340d403010050b038200384030781c14658804945201855400038050403001c0c8181c039145142e4603407507011600701150340005400300d800305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 651024280 1250 651023030 651023063
    0x815040515130204090f031e05030105040f1e020a08071407060e10020c0312100513020a0507020607030314070305160804021503181c0906051315050403110607 70
    0x1a0150302c4803400082ca441d1080660004e000c488140300f05552910544040d00c08050b0024100210021060900c0c140c0070408240201984014050240103a44500700f50440e5038841e00515003000e0b1203002c41180450802c0b03407100075040300000d03400062480b008104194001d4003800592541d410110b840c01c001500c42e00e01401355180c410b012071040c0d1100501d4009a48082c200d0549503c019543d100c6032011540c810503005003855614400500303040210f5602d0800b00d642844a031000913858012050341131b05c09014500303002e9000031001662004141d07043d07200301c060140280401070142c4902208504070f400440360b514075034101813000200f4501444505502030701c010641d25030801e000e0741c407251f01d420a0320340700c01c0f184045032804c1a49406001b0303a40d030841110003a4140902800000703041d45098400d80c001e016001581452902c0c001c401e100152030000101c44050351502c3c80203000380e0252000745d80f0010880300d200d4152070b040049a00c815000800c8040c049880d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 651025530 1250 651024280 651024313
    0x10305061b1e0a0c120c291303030e030f040305010c0806010f0e06131e0902030f0105090711010903211107110a03050a200103020304020907080907030804080708150405 74
    0x4503e1040078004480c10b00c0b00001d00c0d0038041031100d00c0c0381c0e651540051203403070000400c090640c2500c0088600000e40340c50381001c0791286901c0841981d2000030340410341801d4000380b02e01c4404102500000440340c7c90060024000c0040382d2040d00200310b21848003404507001c0c0c0080e110140090700e050074a4496034420b00400b10003078001040f903460000c04503076450880e481ca900c070b466654083d050000042217845840801002000c6040d0301d14500714240d60b01060741409268800c00742440411217152203421400403103030812008016400c0941006460040025100101c01c000c03003c0306002c5a0460041a0090783d000c40001d0400500d903466241c0b0030744d00d0318540e402520b00900080410010042c01d245140640d409600c09075100000354104550310b42020b05142c0108107010040e10340f04c0c421a404060b0f450220016101c213110f50341082d030380340d00c0500742c001d01280200b00c011000c100f00085805902c229245c200c0c00b110b07005450b11040320702603c04d4121003601c21500d8403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 651026780 1250 651025530 651025537
    0x100507050906030a060512121614030721090f1a0c0703030e03010f020403020609131b0e03071502030a030504020303130b12091902130f05010305061b1e 67
    0x115080c514200244a004030b41650070841d5007482e41a100c00080013075003019500102565900c80141c41441d4800c0280121031150f0741c510500d9024a180744020320602001050915a84005899881989081100b03101a540d01120010400a10640704d0320380180c900d4400c481034400c14400103071a1000001521014607a002d41034101002103845039a01403011202440c0709031078041c05610b0310010f1508543c0314062080030b10b0b204010070700c05640c421054510b00c040854480300c1a03540c1c0014030000e88203e26200000100722f6541011490f00181c4400f81c0220a904642e04182e03030716140180c10f1400c0480d940540c004022650007148030f50011507000e03001508a900e4100042a1041d08071a01e41c40149141408190414082c01c052005070300485414010700c1c0c86291901e0300008444d5110009103d032200114032040c00825800c240c440c05c440940801c13641d80d59042a5131550011281851107108050001e241d003c944015111307115042c1c101404550b20f041d10f620318551 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 651028030 1250 651026780 651026791
    0x50901141e0303070305030a1407120b0301090816030320220302130e010b18070c0c030b0c120c0c1e16060315080c091302150a0f0912051005 62
    0x40240700e000c50181c41c10001005450301c01c0e6200ba95a240c81d040307100440b448040803441210b003010620003025408000031145407098400000c02d214048000303030041c2050a002801c659000c620300c00880c1c3c040021840403400781c1c505110301c1100c0d010046d070a400c081195100c56205129803840000c0040b802d040c0e40d25104c104450170380e01e0b43c0000d001d481c0198520000c041d1101414400884203001c0c800d01c0a405460101208010340b20480490b4070080161b03080000a20a04041c0300580c00c1c044010754010103888072900340000d80328801d907c020030058480070814003003102c502d080001c80c2d270707070b41c00c01c0d4081c154030b074040040013086060800b00311401d8410541d030041c1070051410f040008205584000415040080300c00001c0a00399120803215041450115295284c402c03405074402000c10611328135142510000b154035200400400d404c1c8408558003142e550443c400d40c1d6070008030740b13800a0355a03071013000c14808008503130024515004604500c00201d103540210347c000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 651029280 1250 651028030 651028069
    0x812070f0611040e0f04020a15020604030e030a150506030c0d050601150c15090b060a08030d020a021501321f1101090524010614070f021806030705090114 68
    0x3540d40c01110700c03102070030f03540c2c104680381d07500500c011850070041c0f036001030400380c0044040270817440f00691203134402000503080c000c0c4001e01e14181c0e03605014441200e40c2c4035540310710240c18400d1180052608175103880c00fa01c16803550303055a1408500d02407180368088001c04850782070508440b41901139070104d00034006040c140100144205240111110031b01000050901031401c1200a1400c050070441c017411301c018062044103401301c2183c003800e010310000b59803920081c0d01240f4105000c410440345d070343c4100c00821000e0000f00d07a4203511250f92200032140190552041180c80724080300f5900000044034031011103500420030b08460400c9c10420042c4a03603980301800c2d2140428110341c150040403141801103000d01c3c0d000540b03401014409640d40c10002c018000040300169440710304004644101044010303410032210b40d0340541440310386900c9040b040c2c6100019102e0505c03900a910000c180c5050442e4064100c03070115104004c003071000d10a0203c14510070140d030180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 651030530 1250 651029280 651029287
    0x30b0102070b040806071d0f040509150117070609151824170103050601061101020f16151b2109110a06030608060604021803060c040812070f0611 64
    0x42c0d000c400d0180c0001e0000002038041c61600b810000c0c035a010355030f04810550003031a10030100c1e8417000106031101a00b5100001c950312911940c0d407500d440180c444494010b001e0010503a100c00445451300c240101c001c942c2c80980711502920a01c0c400e0203072418004024417480b55441c032a805049103803810040b1960350a44a0984d0070800b0310324038609803040002c408007200c40382d002440b0402116000210007042d4110340d0b4403a140c107070600c03514040206c40203090f540607400390304503060b603850f000c0a1681c40100c0080c40b40c0c90903240034191090038080e182c2e1444801035005960071a0703d400e103068416801080c3c2594100d10400f499030b046003d00890000c4041c6030720848030700a00030300300d40751031000600802c010003c00f60130600403d420070104025a03480000d42c141c00410450700540c41d080542070411049480100541e030511460b01407000010124000340f090310008030580b44401c41208455002c0d204400d401404281e0445480c80031404c0303a40004194509034154524 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 651031780 1250 651030530 651030539
    0x30c130b03070c30020309011808070e0712060806061005070b0c16020a030803041407030c090c121410170703140f06100e010512060a05060f0a08101a0d03030b010207 73
    0x41102d44c0006990260340002204070096800000d0152001c0351800980f001c1400c003818191141118814143c0d80c02400c0701003800d080c004c0c11004003070000c24a08102081d540c003102551940c0640b08140100d03c070604c003d0078680b0513812600c1580c0c00003148a040e842c1c600c8042358544c880344400d03c406210412050050f56003511328001540109007c40c1c80c0c0c2458201a00314606640508007564080881000004c590f004038030700700c030904040061039010414080e140c4d0040004020301c0c00340b800c402c00c800c2014924125000390040030300003025030345503100792074110184140c127a4a0390003120200700041440130380701e41003100c1005031040200c0c0c0041c814609081070303420751414402070340c0c140010040d1008590043c1000c0354084982d0103081c0c02c0580740d030409881121000e07120000036a04c1e845122090400304000340508100310f03541c0c95401c5d112030003401000d0104d8101a09212400000c00705201154802000346610288907541600204066580c050642c010b4180015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 651033030 1250 651031780 651031853
    0x61203030601141603020f100608070e0411210c01030b0f090a020408032a0105060d0609020a0812071b033302181201200d06050303030c130b03070c 65
    0x10b45282c0721b60010001000c0307018403181051016403070b4400710b80c90a08100001140000c5c00400c803021f41e40842e03002d44030b07420400c200306000c07002290805589900001100300004048601c1c00d01d43d02901c410207a5480110191803400390842d6101c41d0140301c0760000d18204d18030903080000d0103401032802d6910041203007585c01000c490700402440381401c2c0080461060100901c144640c000c0119240c0b400000d100d010003210f000d04050f6445a00c0c034115214000840050030051007142d43c0c682c50400c00c0d80d00ca5010805c00c45003a40700c211504c00d90783d550038400c1d041c0da0380410003046003402c000000303101145000303405e862036050940000a140b03d510041c1000042942000078180069044c0030b4010301806244589130301d8406034000e0f0002d0707880c12401b00b861105100d1b075502410480300c0f01a02c95900305e03da0600000091001040d01d1100400b004c84c1c44070806140c455407607040c1e4207940011039540c4049007000b8205000221841800311410541c0c1e800408c0c05c90034100d100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 651034280 1250 651033030 651033067
    0x10200c0c090115080702010203070f080403020c03161409040803060607050a0f0c050901060806010207030201110111030109150608250c080a030c18030809131e050f06120303060114 79
    0x41400601c0700003c03d0140d034002030980e8400343d580002e5140d800c294200801c120f02c244c81c04010420701001007010103101f030091001200f03008007110109000d0121011009001d44650346070303221603c406012509140004030b21864100984c01d0450740da150034814a68050581141d02d0302811040380e000841801c503c02c40305000e40c00300c0c1da0450600d000e12800100c1a0070000901000c00100035460703a0006a03030040d40e90a180c00092040a2040b26026040000345048184804800030652a0319135000784a091825019102544d90381c7d0002d403260f00e004d035600f40700c00d11425102646501024840042650300340381900007080e1a4450054503081400103500080d21108440003482d0701005000b513464150f0b404d00440343c555581d08031a48620307400711b4002c581410b1440d2150503142d02ca0350341e0303466000490100c3d5a04c803217032900801c8122801c0380c0013a5035501003015400c08071a24016502c60400862841e01e4000056640d048600e440300594082081703d08403982c0d1801c0c0c0f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 651035530 1250 651034280 651034289
    0xb0307030b060f010c0b1306020c03120417031009110714060a0501050405070c150b040e0709050901050709092d02072904120306050d1410200c0c0901 66
    0x150380240c240b000812885000b4003180e24100140d8100140109660000300d9421007030032420142c0042c070920340440030380260342680200d808040703640450194507400c10361080307214048030118541c02d4038142e103a501060750900c4007013107411001e124000c4207174090810000c1ca00303051418201c41d591b950030464460000781741160004000e02c4054515401054007424040b07030203101e42e00c3c1c203c6008024081d0160081c00c00e00c0903901000e0b114000707900070b4883c208003500500c41c4400403c40c9607686e2606210b074110741c40c0391000050010b10184a030b140a550260f03524000c00349070210000c00362401420941e81c40c80c1d502000410b041605115882640c00c081c0d0150f03ca1a0a0400040c40c40100d4800507000d46185d0036010304001e810a22544541c0c08080d41c812211054822002000035400098000c41e40e0600310041c00f02c0c1c03802c9232240803d01d40c115003080e00d40e001c441d0140c0f00e10070301c400c0080b6001e076182d104d00c5004502411508481100702d4655020060006502c52000e910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 651036780 1250 651035530 651035543
    0x4050301180b1614090a080703032003160609060209090106030608070f05060f03091204320307090c020c090a0608120304080901080403050d02070b060910060206040206030a0b030703 80
    0x6030010092031200081e4040b1840b021a4a500c3c55103030041d0584645115004e500f48000888181c25540c03414940043c0c030424085440c02074891502a140c84502c129080b4505414101045540c0c000000c43c1e07100428001da0b03005412a40c2d0303411000c0c10301728000300d40c45030b000e000d0441180c84580000e8024a02540d01054071490312002c203003019250f070003041c00d00756144020700c2142c4446040764145480070543d180e6a0381e451320361034201004100f104c1c5008400042c0000c01104e025072a610190f1214401c0b512041c2540c000b9204800c840015901500301b44810009051150b00981c04010980103644964583c45d00284c3c0c021022500c802ca540e94401c000d1000d50070403c030011251401040013840e5050030f464142e02d602854000c02d040019580010b0704062207802550920891fa001c2907440b980b0500c2c010030950011920707140522510760004100d008401c03d000211507140c1c01070041ca4a40c0d400b804241c0d440140005030341901c4403c2410180c9080140fa03004600030700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 651038030 1250 651036780 651036821
    0x30615100c050312042a0e0604020c100903020d08270c13060306240b07030302040e1504140610080c130b0d051320030a02090106090e100e0c0d0204050301 68
    0x40c209003195400c1c0d4256005268406ca604182a188038510040d100751303040c107024070f0f40c9060004000e4800c0c1d0000402c10301494044140c1c08626400601907a03200790280c1e00b40d44c0145d24100d40c0d6640454200d80c410760035040341d00903104c204903021140300c401c10513540310708400c4001c10000c500d000240c40341c01e0303650b003c00c0042c80718900c100118603c4a51541100c5200e0a19401c01c09000380241c2000c10f0001501d103003014041da0458005001541c00c440c090b2402140c0030301002b10101c2024000c908100f0401c110741d200c180003502c201e400600c6100c162840350780440d000403000b4030045003003004001006003810380c0c43c1800d0040501248072951a00d10450f902d0035103001401800c0b114600c0c0018500203170582080c8080c855100e80b04903116003485000918001c1628000303900825010000b01d94207602c424280c0a60f440e484110b61540c8504890701c41611945c42010801e20308400802c1035004108000e168040c0a6000542001d480c1d034002800c54200b008a0800501d614 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 651039280 1250 651038030 651038033
    0x30a2306010e010e04062706080d110f0a060920010527030a0605101401120906090c030c0f080c031c26010e09010902130b040f050109020a02010b030615100c05031204 73
    0x580481c0c40e000c0c001809100c030a19150300749a507a00703004405803d012f021985150100403c11a817000c0c1c1500c9c004442d00040d10b42032510040954076001d540700106032004d0b40d003440301d808419594a41c1070703650600e4904190a292565080b031010114101e0020903220300e55034081103003421040c011040001c5904211a25084c00e91860748050780641c000044102c0582c2c11244000e18600c841001241a124510303202c0d0060107c0701d801000c10001110210900c10350300302500584902000c00103016032182012035444121641c55035155000c4101c00a21002540c00000b14011600727100350400e0888000c6460402c48007482648410380c200100401e481158a2a0b00601008000c000240c8140c020076200110314080040e0691a0303162800c554076141d00030040152081403c11803540c60301003020180d40100b15400c015070a00728240c00914000c92030a020b11001c13802201314a60b003000380308814424410702401d203c000e05028007c110248014110000400c0c0700d280140b905 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 651040530 1250 651039280 651039329
    0x50115020c030d05040b030a06050402130806070c0819020f0a0b041709062b0920061204150213030f0201080f010810050901020f0a0203030a2306010e010e0406 70
    0xa481e4511a6103c84000c0000d150400304640649009821440d074039566101100c1c05001d40358800b9801910009100760580360201b4080d003900d407188c080e5500342c2c4074840100e55200743c4600c054001101040b600503031310701c0003a02002000c501c2c0141c41d400d0507041241c40c10700d0b04981054031021000010407040098407290b80002e503c81000050503c0c10b40b03800719400b030141c54030784c12078421103540201030707074030103500c8100b81c1c0380c0c06a0305100c840130324580795009500c03481c03145090b1070b513a44c0034500b00c1c60710300290b981d4240500c1300b80881390b840c0d4403209d0407840707602020b825041e400c02003455020b005407000409036000f031200025800c25031000400c600401000140e14070b03c20310061080e090086865550520340c5200400d841d243c105500d8028031900d49018010400000c03022829600407002e144601d0f0140da0800405070403007230404880c11100a07040b441182a03001580c25070181c1e8698516030b0040c542826084800c1d008103007114407680104243d1555100c2e0450346200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 651041780 1250 651040530 651040543
    0x902210c03030715090f0212030406030506030c06070314130320012c0a05100207170a030503040201031806151e03120c0302101103161805041d0105011502 68
    0xc240d0080d480d04049032280c1241400c0d444208a2003529014100e09010111202400341500140701140b50b28201d000217513643d0080c0f0800d00828140800203072280303004500741c0444a40904920b1415500740da040f40c232640c5c00900c07805004800c0c00020003140003c41800088e41c810f25a104081c100b01c0c0c070707420900070b04d003010a0400084600c80926041c8082c1c5108a0302c00c503403030322035411800d03c0008010840b160010b40d00516034000c4403420b43c1c0e00245074002c81e100b07609107009620724141d642c1e440310303407562018000c81c000f00081401941700c2c0d4802d1000300744010156042d1a0716940e40003d54881c900381440b45800f401342400020a111889030f14030421250344080c4c140303160780b011044590550041e0510199014007801d0500900c130031f10300d4440301e0004103d41c94001d490142c00750401d4a0820b0b4900e84403040b140200c0c0202010400d052100c000d0a0340f9a103800204005820702410481140100701c41c2080364000c24050180a0840c0003404140c0301c080c0d2200a20308032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 651043030 1250 651041780 651041803
    0x80a0605012106020a0306080105041101030513030206040b0709080307060e0105070903020913031403041410091a0406022715070209040303020901030b15070201171009020c01090221 80
    0x65040302c1c0301070a04008510754071455804140903031200c128000c01d0300245499440041294200020070003044416030302c02d10124001d03201041561101c144101500f4503516000740541c2c444008074001c240c1c99524580e02c4a8203107824070810b0340b82c000b86411500980421a00300c0c2d20f4200c41140c004d0280601d544c0000d96260085800d40f5503000581c024002030000145408441c402105040c4508180040480181001c039960700f001c0c034060041201c480d4041d0568020301004840349000d42c040c604609402280800c0c0198059000c00c01c940c001410072103c03698204540764014920200300420226200502a80032904000b405031682001e00c0718012040d08001c00705c01a6120740c0516082a09032500507101d0b821000140d00074028156180e50003c0815142115007850600608107140700703998540c460341141019210320032054845200001ea20395013071080944550152004254003070020070812011380114201c4070580d041c4885003c0b429921140300c9008101014081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 651044280 1250 651043030 651043049
    0x207030f180512030702090c0d06050609010801090b2107050a1205210403061b031a01081506071406011e060e040513051203060f0f0303040306110c07080a060501 71
    0x303401da000ca203440d4100c940201440360b035070303030f89a0300f801d0600300f00b034800540e4081c200340c6080c200414200015005440180c805600f4400082094280001030b02c0c002e20303040e15540040e9003044444000f0f0180302c84c90a801c0200c0f03500081c1d41210240e44d183c0d0030700c0b001d0090f062950a11003404490304403508265891059060000005000080d07800d03404441c9184842412800054001c500d20803031b40b015080f00c1c20495000041131080c22040c0902195881c1007019052240802481440b4210498040780c2c03520000b48581000c061001d047c0880204120700d0541c00d0390380d0b070004003404440c0008584c04080144100c0d00203400b03000b03008110480c410039441c078040c001020b080800000a00444e10742c808181c010b000d40043c80e02c001c4d4001e0999108000d0103426025603041100c54601c120000286050709082c12001c0310640000a400303146418110781395407010740b40560b00c8120700b400810000e509440e06012190260801c032025050603006805e08001396101038000b164070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 651045530 1250 651044280 651044297
    0x110d0e03030603060a02130810050a06050d0c0608070c1e020a051f03020a0c0209242d061201031103070b090618010e04060e0103060f0e1f110705010207030f 69
    0xb543e40000c1d5465201c01801d0740540d50b07815040c82c9a95010340b41d0700c0a29540708680890310540d0090b0400d41c0b1a1180410801c20a95201c0411031040c0c103100000e0888100310009108246c03040e40419400600da04142403030480c4e03a62810089000e046962400050a810100451610350206070040508503100110400c84c0c103001c0c40001804240f05050540c00949480d40f40d014911030a1159001005000d2034a80700c1003802e441e840784e81302c00c0070f120840c0c0701c44c01841c6002c0c060700103c0300704500203034508156240146640900848281d9000205001841401d480f42041502861044a49403024080c540c1450301d0704c102a080200c904100744800f031b5030340e02c440098070030300c20b0344071010030076241003030700688130400d23441c3e046a0070509000c00416186500b101c000c0c12244140410445c40071407128000071205035142034034240d001004004030881c200101d03042150742c4100c1c00140c0d484a180c4001c0d659012400803030300c507500806c0e030000341a0003000d4504501207506080d100e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 651046780 1250 651045530 651045541
    0x10f1413090515010309120f0e091812040f03170c030f0c10020a1d040f05070315080102030c0405090c0408061501020c0d02102601060c1b12021e0301110d0e0303 71
    0x41f01308800c030400d801c000113802c032882d2141c4140384442e02928060440c2e82c160a105140340c034244a034640c1c1091600c1020a0340c000c0c100120201c0301124400140090b806017543d8508403a559007181000a040050002c1d00b04a8403c1c001094024031440f022562a07500400490070074104040b0818400c1c070600c1400d0002e90040c0e08503642c070207105a2402c1d5040c10a001400401042322400c0d0b000c0d1620307081086054140c2e00000f40e8074003d640500c001599242d1172400e0f80300842d49580d04600a000410407414070411140d08081a464450b01f019142d580072441d11404541038402d0f4201d00030344000c156014000c0d050b08890076207880480492580200300241c080071400720801000300c8401201921b00c0c610003046241950b0164042d59403502d008041c0803006805a92900c00e0703a00100410205698a400310b0300c5182c0c04540640301d80c0c00b0081c100150780d00350160300c11300004d9a1010f035400c0c80361800702c03420701410585688901d40014101d504001003071459038010006d018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 651048030 1250 651046780 651046793
    0x1b030307030e040f0f060f0506030136050415060e04020109150309050f070f0b040608070c08070b0709090b01110312092b030b06040302010f1413090515010309 70
    0x302416018144015400a82000706008140d0021884046403910814541001c1a50046000c451210300303280e48880d15103040100a100030b10a507900105424004418032007128101d6041a40c100640050740601ea81d420050b154125811644443d4184805040590610034a0040c0402e000b03200c0c001e02d0320f07900103400d0004d980200d8603542096003850710000d200c1c2e00140300c00c40c0e0190903591000001581316584680324002e10321072802c00e24020401e0703088075007654222149581c0f0403095072a48101514003d0310140142c0f00007070700304421000f2a03111000700d801200c0f1996080c0c6011710b0310111401312110380c866181008058500c151685d040002a80c04024401280c60711503101c00915504e00002c441914000c2c1c000041c034980900c0010040000382855600d00340310000f140d1040100d50f11440c080280030403843c0700c2c8811800c0c0f003410024194450055a46d145c0760266a91860f80f50040d40301c54480b54841c400c00c8070580101d41d036a02080390a08051041c9200340c1c1d500b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 651049280 1250 651048030 651048037
    0x5100f080711100908040f080a150b1e04020409050106080403030b0103060b0901110304030f08070506280509010b0319150506060f0f120a0c030c020c03030a050c0f1606021b0303 78
    0x1a520f01d89410740704040c401c05404441c0142030080145000030340d214203140d00e8003114402640d0745002c16500d00c0441c2130031b000e2100440c0c40100a0721810380e55050000c162100b50148036003150342031001142c0301429101d00c90103819140c0b955003152403e458000c00740c8940c0d890080c1010b081003020024400756106640b030541007401e050402c018014110b0746903001e903a00c05040c90072942c0c1d1900600107034900400981340140d00340da04075900d4079003c0c1c40108500081d80900c20041c59020985541507010503085040540003140c0d102c140000030345819140d502e5200d850414050350420042060300483d00390802440c14401441d05074001038075801003003541c10080b1070009840304035407065000c0f503034090301c40a0461060305040340140000d001d1034100501091a14019510645c0002590008441d00500071440c160451404071281c0d0490a43c1100c180f00d403c4400c0c640c80014041500303c00402610b4582a40c60040001e1a080709030706082d401d4412142800110b40b8044200c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 651050530 1250 651049280 651049303
    0x7060c0903022d040b030f01020301030c05120a0203060c09060c070305030d0f06050607030507050f01020d2315060d090b0a14070c030905150909090601090e0f060f04030905100f080711 81
    0x60300140c1703200031034180004200b141000b03501c004004005c1040310a00d04056038025070301202e40148050b58550380740c80301c003006945a404900080d0840912000038480b040c0c010300b12a003044241c0448d2450800c03d80c10845035508003080032040801c1621030003507481d00c126400d12101d403600000c203446114190000d02006000030700b138401e101d800c01182c000100548021940c2c0e203000c00000c001030902c4001c21201840c000503004004004001503802801c0c2a4802606500450f00700107a5500c178a10410720720ba250301d401804030300210102c52040360300d140301240700c01004d0070080c0c800a0007403100041c000050802004650f12207070800654500b9200700b0b81c011074000303004c911400345041d0300b94843c0c07040080102c003000100300f95040ba0360a000070b0183c40020308601b40c0710302c0c1d01610310000e44e104c0d00004044503c00c814064002e40241400c0e00700b01d0f280c1c0301260400304025100c0021403240300080120943c041c031107076440721503451b20340141c10714507407100d86403840c2480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 651051780 1250 651050530 651050539
    0x10305060705160b090a080f0c100207110904020406152d080420090109021201051c0f021c0b07080c1c020c1006090903021e12070807060c0903022d 65
    0x144140e008001031b003403481d002442d050301e41c0d031180358030b0040341d01c00d030400905070040350413040002415000782c90b541580190080c0100c90741a0a0141681008009981c0b2030f8407030200081240d5442401c000b44801d9076200441070249400742c02075201c1c00c040b02409201200b00303840344035500250181e00980d00203d218103c02ca0342d034254200407900c4007583e40c41920440001b410215617801001f20b10815800300e002c0341ea0300c0d41042150360510380d81c0c04c002900c005507800050200c004da85120742c4010100030600c02107403e001703094124260212041c10344041032040175174010b50000da00400540a541c5098035080c45180c01c1a80300c040c1c1d5468540202d04070200d8081031100400c07400210404111259680740904c01501240300180c015000d08221014221014101031640c075512000420071082c47d8180c50b52a03520074034094401c22801d20840d0001607081c000c40340d600d43c16654165001c0e0440c0100b00395a680f01c4100e20b00e00d902c08043d4005103540c07c5802e000c10500300e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 651053030 1250 651051780 651051803
    0x5130f27020d11030702011b02061302040e06010e060a08012057030901080603031e0d0b0306130204050702070306050405070603110f041203140c0601030506070516 72
    0xe502601a001e00e1401440c1e0a0408400350b070703c41c4150303000c0e502c962100d030f0003404400c8020824104407440c542c80900180c02c02d00001d0721100c8020302e52030328503102620004142108075101800c1000c20b8002981d040288400d01242e4600029607401600c4500000c00000d80c803034030003d52410740481c6000c03c541c000b003540981c000000e600c00d010400310a41c900d85003103c1c41810a03100401004007101c604040350089481803500c5844d91250600030001c1d40744c0b001820055542403001445154148001c0200b01d9408001c00c1190104c8034641102640318200c148401003a18800440d25010740c0c071520421005c541c503c4c100382209501a580010580c41c2c418040b401c02e885900041c00d400e0600051004102001803103108489141d902080f02d1400c0c01c0c46401c05c1e00c181d20441c0141101488244512140b03510444011031003820300160300001c246200308540c01c9030f400c8071081d80100004100f449000d105965102d0201e140c541d00d00700340800e83c4807802840820103041d91440d00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 651054280 1250 651053030 651053099
    0x405040b0a180e011b0c1407080a0309030201120b13050405100e03040906060f0206070e0301021b060f0a051605030a1d0d090518011809020603010605130f 68
    0x611648058580c0010310040c41000d551a407003d00700d40a034000c1c01e90310344801041000c6014200c03c03107140d00d5a40c3d071a54811240c0325903036406283d04c81441c013400743c1140003608100400110301c1d100d12984a400d4a10b103540009441e085040700a4101c2078280854a0a10351751010f81450031201c403900050140c81c1c40c24000d10b0202541e0b0031840d0140707011107454000e04000081c00455070480030070f00c81681c440d00100c0c3c9403c80c0c8d110034400b6901400105130350a002d070464120341540540018103001803038442c1c80c00d24000c03208600154002409000f818055142115800a420f0300d043c48a070401d40422041070181803c4030003000700200c0030881010658214032036032041d0003542c2142c1c10101800c0343e01d54980c4002d102c0418800e0400003500e080a0001800d40c0e5030300703050280d00ea07180064100200003524ce084806076501c1d5400c1c80160740e00d80c061400307007900752780c0d040d282c030741070f44460130001da80307400200803100043d01c100646d01d104540c030f2000c2d407a01c50200307413a068038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 651055530 1250 651054280 651054289
    0x11413030e06040f090b2b0501090206030c0c011d0706031104090501090b030f0d0807030b12060108010b0f0414070315090f0507080a14070e1314010306110f0405040b 73
    0x180400298020030010f40011091100030399007055414641c0f08010f222507440421480c24010060080da01e030110340301d01c40350105002c110141030f0240c40003088583c00359002074403941c000c440c1e03043d009001180c441c0b101d810920649039a914100c00000710398105c0c0740e6142e5181c610b4400e110401da12099564000d02d41002a18000c0c50000b030184a2940c5a45449015144410b410381c0030703200d100111802c1c10f800054074a03403c0d0309500c1c3c54800f515a0041103000d4180c801009800c44a12904040151400c001c29030082803603100008044004604000e28017000741d020728403860611044403409595109090b820160740c0c280082c0781107040038038000d81c05407075102c0205d6602d4010080c00c44801030f00418440d880a40d20702800340d0b00c030304110781103402e250f03108580b002c0c0403400110392502078810000e44880003841d00c5130341076010070440140c4101a00d88100842c03498010401c11440d40641040714504091312800e243c1d00c0c0c880c40f4114083c030700c50140301d41e49903514400c0703940301c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 651056780 1250 651055530 651055547
    0xe0910050402040f09150311100c080c060109051605030a180c030f1109040f0f1106041707060201060e070e040902150702090604110405040b0a0807061e0201141303 72
    0x4050010341d111565004132900d00d02c2c0038850075031000d00706142054000c0e0b000d9202070959900c035501c5100302200c0c100340182054240b85550074822410071040100d80400041e05503152a00000d140540c102403240090724006071180b600c1c16400d400581d40395800409403607200d61a0f400000320460031860a407031100103034a001d025040e0000020052003184501c0c0d071340042c011140f881000354024240701c034900c0116030140c15459280d05003c0042c44030711802560901421621a10b243c00350000303170380e55100d640300711202e46c40b80c0107004d80390006101e0680100202c1c0000c00603140351091f00485000003d0680c0f04020085004000940da241e0000550540103001010f0900c200384000c20b4950103c01d09a11a603007460010302c5910b0316024808448007a110044e0500d890142400302510090035040d6000c1108900415803113010401080181038540c0c1d42c822020a00841c4000580c240114100b1641007003010928840884034250300460f040001001004080c02c0803207600340d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 651058030 1250 651056780 651056789
    0xf180f02032116231e030405062709090703060b0301092d0c03081c0c02070501030f060b2809120f03110d0f0306060e090c16060501090c090e070e0910 66
    0x130103000c3c1d0304400c51002a014002c07a0b0305e21041c1244010140c0c3c0156070740291710689900801c20070010144400c000341c185480c04c2401000c82d111404d1a001640409040716130065a9125410800501441e4000d44084081c00d40003017094a655850b040b0191401000304120381d41004030003556000b06032004038415400070b50f1030600300e03180d14017103003554881003040002d2051b111189820030b4280c858070040780c0440d0001c04a5070301c0c00d80198040c164103030241c164030f1356905002503180084001041f02c81052044803940c2c04038614036a01c0c02c952000030f5420840d600c030341404000038006040304025000728400d00171500503d01101e03403600d040a800001e01541090b840c2036500180703144403030051603c00384005a2654411a204c4942401e0300d64051042c0b804118032220120043c1032030810a101d24483c519030f030f1241c50542e07000381e100c00140c503520507011451079440140701d8085d0800310702c61320395400e040341e0080c50f2402e20426144283c80d80004202d0110100007500001c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 651059280 1250 651058030 651058073
    0x4050c160f0314160314090a09151703041202040e0d030b0f040c0207140f09040302030d0501170d0f02010b180118140a0f180f02032116 60
    0x4240601d8a050401c001c094101c0101e684900c0200048401406551840150901c808100d0f1160344080380c01c0c1c00d0007924480c0100d8200309214480e00c80d1246072001c1c240c45031000c50401c0040b03a00e61400c0307071590303c50151f40d07a981c2c0342c01d140e900021045804030303540043e885211500307500000b002803081c04600402481075031555003c040e010f4201484045007200d024601c00400703401c0c0010f5500010025005802c404428330030319408860003080e2500c007070441c0c0a54580d0f2030106610520036a819405030344041a1500300c5002030141901400c042e5070b0030030081c90101941d0307554194441c542401d0113015038054070ba803807003540800c0c0200001040200c840c001d94070312018049081c022103a00d0068019652010704842c012010a2511b0b8001c0c5005075655056040040c4008101403a50b6a1030302c020750310f900c1482c0060b99417180070f100700544940c1d00d8410180340a20040c0c0701070960901401c0d0b0842c0d00b0000b4242d61051400b218402000200d5103003a0190002150604460 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 651060530 1250 651059280 651059317
    0x50604140102010b130e1519050c04050306040b01080708030a120504030c240e15040305070312050a0204230a050613080f060f10080604060903110d0509010210140604050c 75
    0x1c05c0c030a0b40002818054060a03101040c250300e103001041c407011954025501340c4400c1e1b603e00090241d00c055844001f40c52a44d04054440300000d05102c000c2da0251080e6140c2401880440c0d001e01c070650080100344021031402c2604203014001012a09a900c8419032f030b84000340a050190365075036201030f4412951101080d90500204040c0510a5600381c03035441c5c204a8502c002c400145101008a030709040030681d80c0c2c41e03038119583d0780207a8044041144141000c180300069004580c001c1e002d1a00140c4c43d00d00b803805618140203851603030881065100c4a03680c4940702c4801545c00c2e5181994910380c1c0c3c945075000282e40310711517072050310113109100000907085004641940916818816518036459455903082490118000c4140c0381d0000e0b07012400007051984600b0031584030381002c1559034000000c0c41e0820040c0109000458000600c1407007946e410300400d00325090000b800c104a0148046051007a10010704250199541d04081443c20b1401c6003568044000c40000300342 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 651061780 1250 651060530 651060559
    0x140604240902130c0e010903260c070e160c0b06060f1605060708010f0e0703180506070206040c0602010c050d0e010213060e1c0f0f0311030a090e0907050604140102010b 74
    0x9241e00102e03840056a240450b1011b0740c031031070480741201e81068141c017074001280450750b9514201e200c92210f00304100402001c0540c00e0140400910380304520459030700d0b0076080310101c4407590002404008080c44100d0005800144c0c032030300180161941d54840b0500480e6100f680724150810b80300c064070041e44001c00c100007850704c2c8030700c1450f52108200e036a1442118030340103180c0180c0207220b441400107428039100380e01c000c03140036503048085606200c030f44920f420400d040c1c80050050b0081000c01050104203400c58000f0485071008001913020010b0042c4540900e041101c1280d4840d40ba00c000c40d802501a280306802060200700c02c2c0c1c0c0d980f03601030488400d500d001400f078800440204041082ca5202e4000f0300d8020078901400c5465036190700d000910b10400700c081c40f00031106600050003c0000c3e00c403014443d20344901103410311008000e009030050032411558856030301803009455039010743d07089030780507d01070f4480e8446400503400340498140442d0480c0540d0040f60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 651063030 1250 651061780 651061819
    0xf0b2805033d0504060902090a1e051e0909060601020a11041b0c03120504020906010e030a0503180405090d05040e1e04080d0506034b0307140604240902 67
    0xb4125002120104485551001d0301c0d000d90281d030340499446410a5410480200d50003061416400303076122541d0140e440c9c000041003001c0b400f4003590408090342c8000600d0a0050200790040b032140020005403821a000130341e503000303103000201920031003444100c19450719004000c0501860a40b4103140d900c01a004002068103802600040d81103401d070000000c841c402c040c051900a005e4000c036598120043d130302e101d0ba13000c2d010f4052003080b014030046101400a080d4010f072107031034245501c0040b0100400e03200e028200e15803c0d0440c0017044051a007090444084814104040d0700e15a24031203812031110b00c0c02c2c581803915001c40c08100800c41d0708001000c0c50204a20100000d4407458107056580000301c040d01d05444020464a003500000364403074280f04d02102c40140b000720180f0300368401a028070744881d035035032020130040c0401003410165003240075890003c18440c60a91901c01d401140c641e00703c110104800000d02441c4601c0d0410301f00340740c01504a489007601214000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 651064280 1250 651063030 651063151
    0x130215041502191205090f0a08060709050303090d0605100801090b1603050f0612070906030b040b1b0d050406110c06071209020d080f040f0b280503 65
    0x500040c0500c004000b441040f90005600c2590015852030b244800c080d03058402c0d5211008459000c001070764002803aa403441038032409003008001600050a068030042c1507414070380c001e00d1094000b886026110307182ca986000d030803a00580003044036111130300c0e0240209a190058501942040e542c00300b0f10041c13180b05401010301d010191465042454100c08840055541a03425803000004c03406a140583c66050840c2c103007016103080581da51010710403070790164421034038010140100401e00903d25907481c1d2002c000d02c0003c0c0b079608007501f069410312900d03000b40c140950b85c03404a024006c16601010015920500482da00c9080326111581c5280440324400002c0300400441610903050203031615565029044146800e45a525410140c0209002a00030381c0240030014034100780c0e80402008000e02058155111985d030b08099010170441e61011221129080c90b0020a503c90101c83d445000d204007210300da90321b08070341d1822803c15144580c0d01038401d08544803070284444e14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 651065530 1250 651064280 651064319
    0x1504080c030307030203041a25141303060605060f040b07051f020c0d020d0c2901060f090b0424140c030c0c0f1005130306021303120c0b13021504 64
    0xe40c56206d00b045421200b04440507827602d02404807083d081480c85400d526640d20505104214505c00f0b0906441604075281a0505c40c04001c001c0040c00f10f00d00c5614080e101c19110141742c10240d6501704114803543c41100c01083e0001420000c1c44002d1044007207041405160507442c5180c2480c00010b504600001d0707200d40200318800340a58000503c2444a034100d44400100ca40242c03560442c02c200b4074220200741030f07081c2d1350703184d1003508030100d80c00f0b00410703140c043d17640c6120300d80101140c01982241c8116007080109020a50004030b030700b80c044081510300040e00c07550082c00c0310a014440410324026002107441c0c8400c010100140031075442c0d44007280c1004002104102e00700d80705500b0039810190342e0701030000701842000100405680d48100708141503603a070b0b610301240d00c600c032014100151400309004015200c013088081040c9403418655031b02c1b440c1c032050b010010241c811450700480b44024400c5490f0100040041d405210945898641c2c81500c107001e401042d04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 651066780 1250 651065530 651065543
    0x108031b150a06060e18061005070b0412021006050319060b130e0f120d0504050a21140901091e090f0207020127030b10050303031e01050d03021504080c03030703020304 74
    0x3640e0b9420b0824040b40340603980143c9031444c1c0c6d51100300902030400d103040348400401070300700480800b01d0780d000c3c81a40124400c0c042400100008140207080001036181914020f0400c04200060b0398001081e42da00109101d824038022090b1610030014502c1d0b440c010f400240c140081e04186405a00c00f641070b012070313802d5680f41002d40c0601529620b945e2071115039008140002240c58050707a110030340c888e11500c212041c511198032f58551000b02c0030181d1030003451500d000340e80194405a01813601510b941c1d29400c001c1c03500000307071200701c1c4d500a08032070003118100342500d403100d81c20410090150443c10003a52408940e5400a0752022078168003040780d58900700313101d8809103444500a000d0003940e0b0041401d550301c0c41c01c2804041c01e402a40b0518580124031550184021401814003007076114040ba28000704040401c01603200714414049a41d071f84003c030360041440780d26219000c140600035911071070052100e0040d68280a2103120220401c01d0b03094040e40150b001c0c41c010301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 651068030 1250 651066780 651066797
    0xd080a06050f010801030f170d0b1e0d0f05072304060e0c03011203120f0c090503030406090b1308161e030210030c020f010203090a1a0108031b150a0606 67
    0x24800319140b039181d0786000800003030041000c2414481c0c1060894803454003480320400c510800c2a2a0b00550703980e80115564600318031980c038103541201081c100c81520f501807458000c0004506501c0c50401a0405c01d040100d001041410711a800c09044015007100a0f1221400152040b01a0006283c041c62402201040c3d81e2030200c1a40c0c412100444401c0c0b65130f0030a414101e000e10100006c5050002060b440c1805c01401d000d400c0c0d0024003a000001d030076401800040031140c4a511450098100304014800c040c0e002c04504161031546014070350703507441526540c48a000d1548200c109001c2d0031410001d904c0a61b0740c007070840e549a2400b46031040700e444001c2003031600e031000035440403446000d9400c441c02500103554400b86070040c0c80000744071038003070f03800da074000c95078502181c00101001d01008540d07800440e2101894030180c0c007035030401d403003643d40b031060310396508801d00d005006000c1c2460400c020030b0b40a040150390442c9003401d4880f50041e21650042c0300100721200c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 651069280 1250 651068030 651068039
    0x40509100521061e060d0303091a040501050f160c030e0a170d1404050906030c0409060501150206062b08040e070e01020109123905150103030e010e120d080a06 70
    0x1461340b1502694003030380d8208503840c3c5404022002007043c0c802c138103054450001e1000300703943c82c4440f00d40c48000303054138078540750500e8400e084a400410404c0000103810500c00f191003030b0303600940c00c0040c038100b202c0300501e13908050380c00c002e07010329a0b984003110400100b03100d90010850340136080c21400f115000d010040c1d041d00c04144042107844002401e1000b0821460311110558001d80c000e020313a120108d10f000840c0a94030581c0c02590401d0f180c200402c00d0481144d0440c000b400644003509180c240803001038a601c402000c00d004a103180301e04228042030301c01c0b0745c203162540300e030241e9541c2da5030321380071540790504913500800701d00547c0212079070754010b020b01500c50741d0009902034050300c803410039510b900911400e03039207140c40c0b500490300c1c48a9a01808a07000070b00000080c80c82401c1c5006407400c00c6103280030501503186001000029000038202420300400d003080318182a0801c082985a0000c07111204030313100e0541089201a00004000d018480c9030784180043c035180d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 651070530 1250 651069280 651069301
    0xd080313120c0312020a030f150e0114010806090601020712030806010311040506030a1e020c0705090c040803070803040618060b090901020a020304060804050109020405040327030804050910052106 86
    0x82e4803024000c600350340302080d009180e503801400b0f40d4960741800503104803142c02910855070100c0f00303100f00080c0d01d0340130300811000400440c01419030407002c0700d41d1203010300020f2a10b6805810a0b014503644004681c10b40c1c0203001c600d0107071038500c80491010106090007031a02d01d059a4031804286800808051207030b07000700700c505807400500a5407954940e008280d000300a00c4880d005255010f404400d4140c900c0e000a048001d00704004107101382c100010401a224086c00441035800100420000d0b44c00100966110903006004252643d5560030241d0140c1202e01151507a07002d111030040030040b80d544015501e100c01c2c1c030040415680c08603014200d02c11a07802e100540d00900040100c80c3c407904216500a110344004181d100c2158007040c140c8078203682c200c0100d02c00700300300c16002440d03440707160000e100e4140c0f42001034a03607141c41c1c0580c4217500820f80600541000905003802c4084480e00805001d01115810f004401d4451114010480006054003c420204261005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 651071780 1250 651070530 651070547
    0x2402030f040c0e010b090603060307260c06031b030703110403081902060411120a0605071e050a0c080901111b010e0306040507120c0e0903090a060813020f0d08031312 73
    0xd00482d2030072806c44100030150700024081585803044900c042400d070064062041880080c0d60003020b038588188601d0b050a01080340d990040405004000d600100300e9840750007074500c800582ea5036181c00104401901c14001d03040b40010000800008010341c10740109030712a031980801825a401311400c83e00c6540603100644245a0140c1e0341c01c80b8906554040c142482c0d60040310411000c4d80c0d2048142e40003121408081252000c1081c0341c030050221003000c41070325141a910b8050340000103000000d130710401811a650114880d22540d01950031601581c0b040000c440000f01076100c1411095900d800c12800030380c40b1000362010741030000740c2600540e4403034068580079003408440e14001136928800e541119032510b0000780070304000030841c0030300a0400950740c0c2e8082c0009001250f90158484030400c8401130400107510381044030007051550440d5802c0607411503600141c903145100d10080d191020000c2030110100c056110b10340ca03030f03204022084007000030706003c0c1c96121 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 651073030 1250 651071780 651071789
    0x105132405011517270c0d12020705010206010f2715090609061a0a02120d0c0f0503090d0e0f0411030411060703050715061211010207212402030f040c0e01 68
    0x6041c6101d1260020300d09030b2501c0d002d10b210080301c00e041510000100520b07d80700040d91945000c180c00300c403241c1d060103004041c00c401e000809423540f4108207a195043c1b14440d01e290394895004501d10303002c0255002d4000d190808040c0911036a541040303610210b24480d012486180031000914080e442c00358908403001000d00c0e4095440301840c22580d584490320300c000710300840c080750607200e5402e40a0801c4410000000500308884407024008803003690024040c04424020050043d800041245004a861501c800820544000701b08490000122a039125081007400215607909a02031031041e4003501a40d4180c0351140180300e02403003629000740c001030040140501188084010f40300030380c03c2c160001800c1b81c0d14952403600085100048800710750140aa0482d50380c100180d10290421020064641055000711100520025801008804003c0301408206814000700d01d2030726000605550300d19108407242100d4108640c22502c0b0310101030041425812441e245050300c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 651074280 1250 651073030 651073051
    0xb0f0c011a01051b0a020913030318080a11120a02031e0a09060c11190503010c031401120807080307031506050c0307080d020714060709080105132405011517 69
    0x440004004c40b00541070b520030441910948001e00016265014107501c23602c2d01d92401511003443d460014143c88248407620a18104812282c01040001c81103607080c06907810262480d000d00003000c0c0c00c05080716403144403ca4080740e4446425004402410000c0d00201d2040342c41d0304940504c1c90364064105034000255425000744001170107058604003050081c1c144142c6155044002000d000d40b1441080d0405c80740300081000d400c0c2402201000c085034141403016100740c1d025206004014491000000d0013041240d05100c600e204407910705400c94407441c1d503480d000c40d018020b003031400c4488003403030400580000c0d042d2103070042e03d84407000305000c0c5290640a8545540341d07003025041c0e000041d820000e00300042d0b84540c3e580010380012001c0d11080ca0803490140c166001c41d4041c032901d0341480d00700006034450340c0c001d0740030343d91105018200304240c0c07581200700000341003200c008174604000828007000c1c6101e030a41c004500c1d500c5000e00604d541a030780f0690b8058500c1c0c1e009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 651075530 1250 651074280 651074287
    0xe010c050615030a080d272001050c010f051f08070e180607020106090f090503160507080706050c2103040210180b0301091109090c030406060b0f0c011a0105 69
    0x1450801d021002d501100404075030510303046840350070700ca61040d0036a000342a92a00b080802c2c902d14407606205251383c440c4d5072140c01036034844c8111056816100350007800344800c02140c583c0240103a0740c41c540c2d500c1c0200302840c8280a04d00040600f9900440341c00c041c10201c03140306500160076010b582084010704001483e00700c80914212000c0c2c804044002d8980e44001c03c3c0da400c200d6248564065400030480e40d103040c4c0303401d040722004100c0e04c0700c1038103000e148808038000004a48040c03100c49111104245070303007002410070109030442065400340200c001041c41d48034010b480341000c0d03041035450030b610010f04443d5044802c806c20306494410b10008025140207241403c1402e0030303080200c60440c4022421001c00350642000c070308000040010301120f18248031f0b0700403441640502c02e1400e00d2600020f0840040101301038903a0500100207001c022044e00040d008000000c0400d44818040710051f10700d40001c2c540012540c81d11101d02d000341d045420a50303c0364811f07110070b8507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 651076780 1250 651075530 651075541
    0x1d01050f070b27070e0403090e1f050f0d08180901080a061401030209010506161202030406022512060216030e12060c0a0513080f0d0216030305040b0304020d0b0411010e010c0506 78
    0x5580d17400034026000d1040700e18001968000513a09148a8115240c4002c0c070684040300b080c0c505000341e005140500c0c0d80c01078031440c0d81c07180910401d0158000498644640c880c00384a0724005c080610945c102244000000e4100c030000303820001203100740824454400013a100850fa11070034031010394071008201c010002400c1010091212684103110311030340100c0d548814403110ac0c0005608010303400010304020ba44e90602180c0030086011240a4100384600c51600c05e000c0540111081207035508072010400459074100d540b803500091520119100d5030401401018981c6c2c1c01c0c0380035002d607004c550307202d03540440c2d024829501c041c5c0560410701081c0080b541b41e00103c50070b07180d00d031880801088081040040d019022091001443e01c0580d040000b401e0914061186548a0440c441070000075080300644081d12881600310b5200d99460000529081a921029144440355418442800007160740d59903d030038280c90300d0031955918801165190b08201c1c0c007421a400c810081403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 651078030 1250 651076780 651076799
    0xa030f050a12051305010815030601060801050f0102070e071b200f03061003061a0415030c060906020601030f06090f0303150f03021f2007180c1d01050f070b2707 71
    0x181c10480230b0760041c000c0240c503808039140038400e0300b20102140c100c0004101070710b02108840c0e40c802007031001d8440c107845d010018001d02005007112051040005180c4500c4221524035428150082886140501c65214400000c042e80304450b004603002e2070107410301c2c140043d00c3e60080d030642c0042c0061394a9611150020312404040c60205101d9424145285d90303a40110b0141fa000d00c0d5054072702500d980f03001140d58070b007944080c003445028002040244d0300801c4290450760400b400a902c1d80451030580010301d24000c00405403c02031100c001803685c1540500360103403034085008542a100c03007611806103510320000b0343c003a00c546088400da007404078520f0600c0600781450100c1703691b5803041c01444c0000c00100c000c581e005000400180a13603509c92003121200c001d04101031042c0c4000200640107401580003101d008441a40e00e41c0d00c20011221704107070140300e103502c070303c118900842c50b140150b44251040d41411502440b04c10480015040445108002c212280c034040011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 651079136 1106 651078030 651078047
    0x30b0913020f19092304120909050901020310050301060b09130b03030c0a051c1202180303032a040b040512010603080f03040219030503180a030f050a1205130501 71
    0x5058405118541c126400800d0f8404802d87c660b826528503d003503110400c00c5140c0b0301007202400040d40a580160170304102001069070320802c260913200180501500321760200403548440c035006020408044480380d0105509100a00080c19500141828901600051100d01c01c00005000c2541100c003030740c50002410700601d400a00d080002400003411a0b0300061055550218041c0c41c0e0b110388004049a0344c80c5480000c02c0700c0c401c8420b050740d41d4608910150061030303a039442a00c060701d542c00304c0c81c0d0516103080200300145038400580b00041d566001c002c0007054091001b4a019059501600d65a01306441440703072507594910750340c00d0305d4010030050002441c088100c07012540b40d46032072031091050070006440c0f100c072580010003903041e40f601001003000c0802c440d01e00c24012200c1035000c501029042d00c00b8841c21f0004c0c4241403080d90280715079030052a01 = true := by decide +kernel

theorem cover : BRFrame.Cov 650899280 651079136 := by
  have h0 := BRFrame.cov_init 650899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 650899280 ≤ n) (h2 : n < 651079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
