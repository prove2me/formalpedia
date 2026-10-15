-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4379
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:26:01.471994+00:00
-- url     : https://prove2.me/submissions/923c6fb8-39a6-40df-9c67-ea554dae631a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 787410071 ≤ n < 787589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 787411321 1250 787410071 787410077
    0xf070e0d0302030f0d02160b06120703230a0b100503150601050a0e0a081b101e03020c0a0b07020f0d110304031e0209090a1104150302011b14030c06100501 68
    0x8200392111910f02c45d4003080c16080410b0b400e0000c0070342000064a01c02ca803500030a00c254240c20000c007003041c2e1200f076404985040c0d01c00001040013034411284c00c60700c01c1c0503030240641400180b40740d50603c0c0d41070800070700c1060603400700042c40101d0b046a400740d450503812240c030405640b80c011103200b010358100e0b01080302880003100080c824904107415a0028260203040c1c0e59130905540b80c034400300b8840500313a00500704031781c0a007041c044000103030815151408a4510030034500305031055201c0960105038000490401f42c4004004107a140c50740080c45040915111a00a4030381c1d464141c03140f01405800c4903d201603105080f44003401c00040055407410785980d45100408490b00650a5006594588900503913508080944910511009460440f00c1880c00c14425404540d02921a5141c41800e041030010b035403200e0144c0e44d081c20824007a14a11152106100320400010689241c44c0d40780c8440503408806000280a80c40c200d070440e0f142d0a407d4662407010303008040c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 787412571 1250 787411321 787411327
    0x403050f062d0702011e0b011206030215070804030c062001050105010801090905070b030a021b06010b0d0504050a0f20030303011a03180d031401060e0a03030e0102030f030f070e0d030203 82
    0x442c070407100100c0e001466030000080a08009000c202c0e111a00302c83c000f1000e6684005201558005403101c6ea40c070001740c001c008250a60b40004c2c1c900c1031024280044ca04045000b0082254802c221400303141c0001c0380c20742069450300700800c0c0c18400b1300c0c80c1ca10015503030340140381c07840140501c505941d0142c559141c5a0300300800500148810001501c0038451841c0014900c0d0000c00190b000d07560304500581d448141c0c0c03d004040b400106480385055001d54010080710710707000b05030b80c80811074004c00b281544a904000c2e01d80204110003400345c0010f0905d89080254116054003070040c004005124010450200b5840f030209204200100000c01200c580f54040c0d80004c640c82446280280c08124481c85500d01c2c2081d203410034130100b56a900d40c081200340c200121401420103261883c4010b05c0b06c408600103078802d120042c10f0010034090281d00da802801a2074080c4c2d031780c6503c0d5469150007802c01000600950741000840d02c007219401c82414000c1c61903000c140c1580007103103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 787413821 1250 787412571 787412641
    0x12050a060b04181101020708070608010303120e10050402100e030318120f060916050f010f0e0424050108040203031611060a08091605151c020403050f06 67
    0x150195900303640d8800c0d40c07140f402c480f190884808404842c0906244c0d0119100140003920f00305654102c5110f41c1d0040408002c092b03407009110b41540d602d480c244030030402681d01600641142c001c85007440c007403040300406030f10302540030034440c0c0d0080703400500d10340f0420300540d800007600c8001c0c2d400d07400801c844100c82c000b4140d5102540005042c11300b16180c0e44640c3c40c2000c1007402e44008a0301301005101e0134a03003c100c0f8a240410364800d100d40d4500c0c150016084030302c40300c21a0b041c482c01d030181c03c43da14050004100500701c045c01c1404400c0040c4589003610401a515002d201c51905010640e54401d1031003510495010b002145092003100c90a070640014030310481c0c0186401a04460b180c0310761000d0700e46903100303403510144c46c00c0c2601a0b5041c2000c2c95842e01801e003421104204aa9401400f02681d4518a0040d5a15000040903451418003e1030040b04503000140001c20010001160080480c514094442903203c640810405418034400290a0181031034441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 787415071 1250 787413821 787413833
    0x30b03010b0118061116060513060926010e030d06050405130308040f140d202109030c03030c0a02130e06010501030b0d05010e0c030c09040b0109020306060d020c0a030912050a 77
    0x340c05100343d07400c95040e209441c6108006c0d03802500304200141c0302058214045028240c5580606800e007070030b00c541c904010194006440c1090100421000c0080300c032110007081d130111b08942200000d8a580b00c0325a186d0802400c2c0c28841d00b40528039140000c2e1500d011803400f404019459070f6010220344640d242c00b200c500c1d4043d41a1180c845503445181c0300001003081103c0b44030070341c80350420100012200140780b466407440c0c01240d00096518100140c5001c160714100c205061216110409140802e1526010102d07142c1c05100005000325804000507017288054030880c0c181000c2142c0050702000d946070780c0488080b9502c072000501c0658040e801c074028040e4040c0030381400d214030f901c50b6402d40b55104071030303286904071100e0310009050920441e803001a0039542110b441c20300e80d842c5402180144511109140c0c040080355403651603400f101d0b40a41215801d40d00c80b0f8031400b0b151349031604041d0031030100711407500c00a68586d201512030060f40c0c11001500d0380404e292540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 787416321 1250 787415071 787415087
    0xd020105060a061107090929090c01050d090804030614090304141c02090f0f0c120105120c090c09040f06051c0303020c0f010609050604200f040f06030b03010b011806 73
    0x1c1c4d001c90040d2200400c40d0b030014403a1480e40e034011009880154004440c020490105040c0050404815402c10001c1c00001030000e82c2e5590a18105a54494104585000b8891018010020880010000107101032500300d03801c3d011041e030340c28455480759042c0542d0f038862449424503002046138908140d103440280210306804040d5850611802030380016031401048070f244100030200014000504c00407140700b1350014060000758600204d030034892884420511405114103540701d01014441d80034852424220005000d60132203042c205140b4080350001d1049034015440d00d84c0a2480c590349016110440300007038450340181c0810101281070107401c51003502456002c00104d0f0282404010810602c1156400040c2442c20442d1220903901c2c05003456102e5400d01c0c1c0300071346030319406c8001d000c0c400051041a50303544910002e00138a0081e544480782c0f0217082d0000182046d0981c01040182c031045008115880014005603009015800c00b1030400c5068001072006030301039424 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 787417571 1250 787416321 787416347
    0x708100e0105070f210b10050a0f0e010927020f0a08100b1b0708030c070f05091b0a0c0510050610030c140903150903120c0906030a02030c0c0106170d020105060a06 72
    0x41b90761502c04001c105100c0c2030700b00c550000b59001503120f20b81644a1140b044403800c514117070781c1d140d102d400002d008800c240030790203068954642c1d02156140c0e0340e036100503244c2c1c05e44040d519001031034801e14081d0408130600b40421549000240c014070003819000950303550550250814068000e11035040f0075030300f406080b9105010021461000070400303041841203400080004908058815840740e00315841035003e016040140301c5110b6a110804070060440004c0580f5001d584c00308807103400c0c0590028020380100e000302d44400d092600140e118a0701503038410800404140100c0c00c4404403100a4005200310403000385108003040100030303801b001000c0302e5140c0e40810b10041c41890a80c0c904050307a10014030340040c0060309283d180e000c1126000c0e07505000000001c900c0612008100d83c0b42290f000001562401880c001d848100c000400204849902d512800c2c42c494444c5038120590312404181840f0644140505445284080c081f621503901c4c10505481c10085100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 787418821 1250 787417571 787417637
    0xe1e07030b030604060507110118030f05040914180a02010c031d060f13170601090506010c0807030206040302011a220e0f0604021f0c020906030708100e0105070f 71
    0x40001c05903502005442d0085028010000b1541054031010f4600c001340351220002c3d9040c83d0303c4001942c4820341c01c110090f058144500d2044c1c103884100da0900c21504908082441c0903040c00e070032951038005500c21040403210307918600403400311036980c20f200e0000a001403d200c80140020b0b01c2810300700e640d060400781f00d094a82d00c101c00911280c21092780f21650042c0032420400d07440303404941500070400b101350000e058118000305070303c40d82c0502520742800c0e101c1000c039000764880d00c450711040e904901c54544070081d9140094980b0400e84090340150709042c1e010400500f007108840074240300501075462007040030380b486008048654190107650340c03503495008428062100c003455886202c003402c610b1405204200182500c01c0c0c030740c48a5500c0380c5802c80031540180344001c3c2641c041381c4000c0d480d503980c030001e8a003030501d403c40c00150203443c1c0340510034a20b940180c2d1400b001500240705542d03031520101c4084002d49110030005403a510003a0100d20401c0d02c644101003030b04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 787420071 1250 787418821 787418831
    0x90c12040f140a0609020301180309061416080901030605040b060d0509010b090907150201140a0b0a080d020a0c080d080601110c090c07020907110c150706050705040f0e1e0703 77
    0x1d0814200380f0905400d0b6071070b40e240c3c07a042c17003186028414030380301300d00e054440c000540040d10f00401d0f80d0001d00410701170011504d00c0100d9803c144040e030b04e118400480c208111401841c00300083e40040806030302182c01c2c0712000c509443d050082c010a8040505a241480344c2d4000c403401400e00134004103069581c40030100c00a032107110743e40741309000c540024500b2500d400e500404003195040300e00d01316450301201c011852480c00d10303180c10040c01d90340450300b41510000603e5115141c2c1c80350901e48100441c0c04003a5070041018007a0f01e001d01c0400448039a43d006807521400c0190164001030a0a00010348542c080c4c84179440c1e40b074043c8100c40b001040c0c1d60110ba0b0144090301e50152041c808a40c072011880c1c07291040f40c0c0a02e040ca0001c81000280c8035095079403001d1400b180c850f10109004000d2000c8020070b440000b600400280b0050400d904090080c2d03025001e9140380d0030b21001d01184030384244a29034001c0048842c407551494407420300d034464040240a8000705600e507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 787421321 1250 787420071 787420103
    0x200d150c02070303050d0c0504120b07020f01090305070f1b030c230a03031407060504050c09090a0c0312020f100b1c080a3c080709050612070201060e1302090c12040f 73
    0x122b40d0000c1074900c1455003030703d1401e21301b4019160003002c980c1100c0c42d82c10001d10710b0009910800303036500140c0c006041c5a441086151851100c002560074a030a0400a0000070034059406421800c60310303000d841c48104200251240c0304110071203a000c0d0001261501003000038890700c0022186100c0c062510300b80b20456a03150b094400540e0f050342d003a8420b103060080c030300d4105c00c01a00402068005c01c148807080e036451040318560300c4003a100301d42d03501e0340781c00aa009000a280480110054a80b003d02040303101e401004c2c5030300f0041c09014020b0b1481e1080100170300084542e03802c8410582010340405c400c40d5055034500e0141220890500210031904000b403c038040c640c0b1410400e0210940c55000801d40200140204c04200c080301e41005152155400c071840d0f408452000401a50b42c5941640035080da644007000c441c00b01c90402007e4806c5107801249688204d42901864850020701031007801103503005008200c04001040004010b07002701180980302e0381c140506c2480c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 787422571 1250 787421321 787421339
    0x1202030c12040e151809010b031006031203020f160f02060d3306110f0d020a031107060905040b220608011512200d150c02070303050d0c0504 62
    0x8000c00c02041940c01103810b1000d0420f914009510083d5442051141204000004d40107180c2c0c0043d001c0152900d8040b40301030300d00390000d4a00100180403076034001e20480480e40281120301c000e5840030020035200e0180c0303200e8021100e800258015045c20301c0180c60403800d82d030f0004070080ba403414264240b0001a222a000340c240e01010100c00211241110003092a1440e800c1400308140c50350b00202d03188240ca8040c50781516824640071005840980c103084c41c000f0321010705205031282e40305500c6a242d0000b03800c00f00034402c1d9a440202826450000e0b41ca000c98028403022550100062082d814140d1000410140092010601005a40d0140c400302c05081b07070b0a0090741c60780c80601c44500309003d408600701240c000044240c0c90f1481d020482c10580c0c41c001d08c1820100c01e1503403040165500082119002040c0104811a514000105c0b03040c80190307100341e0b41072900a0500c5400410768000312505604d400d817501d001038441c030006040c0840f152051000a200200344c99403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 787423821 1250 787422571 787422583
    0x9090c03060703051614040911070818100201050411011101090b15010207060c080a080405070b0c1b03063603030907140a061706010903020d050c0910121202030c 71
    0x280c07030f8400207554280424100342480c502c04105041c005201ca0031010703220040100d070308690b285000021420f5484404c51110301ca480c8010740030700c801040e60121301c0ca400001b5850600d00702d8900696038010401603080c1e0300100c0d000b4040d944d00c1c0e907400a282d40242d20360880e0702420000014486002e03a203200340b0f0728043d60f441c0c500e100c2c2c1c24404034495804221000c05801070b03040c60210307501103070345110f9140306c0d070003800e0200268100401c04100341002100080c102c04200c003500c2344151a15503546a81c2d020154040314a0690740f00c815003000708240740107491580110f10200454200403100e6401c03140b40d0000145011442460b4290030300c0074500400160300503182d100c2c40d014030300e0382101411030614070034008800100606a0041c3e03100f18580f20101c8451810744d24000143e400446980c0003941040032035507640c003004000b1410800c03000e011541840191241522401c446c01ca40c000c0c1c901d0212400d04c2d10003c9600769821112a12852040b01d2801c0b0b2100700b0541005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 787425071 1250 787423821 787423831
    0x62e0e100801030c080a050303132102062a2b0e061906150e030a230f06070522081203010e0106080c0403150605120d17090c09090c0306 60
    0x7110a0014030030808540444002030582e00c00600c03540b800b82e143d2548905c1b020300507011000c0340c00711001c10800d03258000e00450005060111000c00000b10194481400b00d8240c999048465003204c6100d00712001046000b0404445074142544110850f407400086011045003210f00d9050301c0c91480b150060151602d04400940304500f002015642c0b40000e04e0b07010142542810414000008009051401000b071490443e01071100803021900307110789600d0140034608000c60040a000801001c5030150154000312101e1617900c850710398a617141a0b90f1240010020020f104901401094072000103100030070900c801a650185617141200b40e18040000742000f10042010311b141c51401e40c01860241070480103482c0c40d002c0c90311580b1072400014000f035841301100100411907070004015040248c421801001201130040d40c60215528040000700d86035a07100c0c60301e01040c409400f98201c00f0041070107103104010440e81c80801000740e02103126210039540982c1d81042624021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 787426321 1250 787425071 787425077
    0x312020307060f0b09040201120e1902031c050318030f0c0f0607080c030a09050c10120b0109050a15050d020a0810050102190b07020a0213020901020105062e0e10 71
    0x81d49451801000b514609440000010316220700b00c802500e448115552003642440c2c00c040c0c2440030201c0c00700034482e5080720341e010320075070405c5800f03c074170100c41b100301d18000c6040340c0d0414040541506404045406400010400c0c00820207214060070001135038003180c02900d060040c0040b5441003a0040e545000703c541c005007804159000078070207241c1148040c50154030900e4402494070240c0f00207800e18070403990b9094100240071050000b000c4182000b01032080e8070810007401804110040702d200d50041c94090000b455600400440040f01c00103044180550303d0941441c03a146951b2034602d0a000d8200601180c420061008040280443d2500b400718105103031810901c4102d90021415540404802c0c0300c4c0354800d50300c0302120307a032200d4a8106556640c40072814444000402904030445180a24030681941c02900e0700f00001c2e402003041d50380c0d400400c801c446a0b1445420b6078482d802501c0011600e4100d240da00b8240c3d801c126091640c1b07500442c0c00525010418400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 787427571 1250 787426321 787426327
    0x13022b02120903040905010803030f06011d12060402030f0c2803080307030f11122410020601030611042304152603130504180606061e050f03040303090c03120203 71
    0x6442a82c41b5881c0500f2962000b5030852406806011020002403c1c90341480b858101c656102c500c01c407001c070a640c40c06001510403150f4043c0059440784256412440383c0030340259145074550018a005102e0001031003548c11900c1c0882c8201d2510384061040c80003400e41d900400800e400e00e0084bc080d4046940000c3c05464550f640303002c95404c1c80207089a020104907650385018000803894000544140052104081c00d0800f40101811081c1a4001c002c0324044840780360086a4907048a010b0b110034089074a03401d141248921481c041c40d01c15846400b05605040c04030454480c0c0500094000150081281c00e004d880c852a6400808d80d200e04404202c035680018544100e1150400b0045040032540024090040e140b8011503005568880102c010178010b040d10b20380543e00701c40200011070700c03031400503c0c001801d01c00090a100d0102c1e8405154802c100312010503540100b068119201c9650071005024101c1d4241c641402006010010826862030510500020340045503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 787428821 1250 787427571 787427579
    0xc01050f07090b09060c0708061f03030c08030a0b030106151101060312050a1107170d0305040201121802120703120903050a0b0604200a0e0a05060712021204120213022b0212090304 79
    0x640480c02c4495905032584130000c0000a801140c000392481e40306003520385950e166104038004003540388200d64958200000007400002e5a01c0310310000d45c6a036110528211040c1c3c42c20b080c0c400d01d1100415034280c1120804d2014403a0300035007214811450000001d07034808010900d441c1041d0401c11004401c42d07554840f10504110700d010541140c09c060000340390680020f0404035410491551030381d100c01100c507aa0403064440c000441d030003021201c14684103414950307500240d001c101c80300002c049402898a00071608401181d6000005040b0301c1040e41c0e80001c201d0000d80060380285d211110b48500d15942030080b050000c2990b18540c0303a0368240e03c0100102c25540903240181c40044091217651151003c60b244c0300d401c255040001009d01104070319090204140701c8841c5008180466103203000710341d00055900071202203045c840a02100c901324800c1441c0c2c0343c0e0050200b1100034035003032500710387c0501d5052a00c0c010b040139082c602d0246900070860320a4041c0d000020244 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 787430071 1250 787428821 787428841
    0x51915030b36160c0312060305030f090307061d0613031416060e0d08031b040f0603050105060309060f0603030903070603020903011d100218150c01050f07090b09060c070806 76
    0x6a07100c64081840880f0401c5480040d29480b2038100c060100145000d217042003400b2500000b0041d503000e07013101d9980d10003400048043c0c1100d940b0f54442d00501d2400110148101c46000000b09402d406141c142001020001c5584c042c40b02080444c00f01d9034000301184c11620301c04d80e80d1120802500c031029030441c807560724910030740260060041100d2030801a80b03840300ba01c074400c0e601c00c01c1c0039a030f40c43e41c203108180b0f503001c2050700300310b030701c002a020491814002560040704d640d41c40901407a42c8840410105000071200c0040350f40c04800000c4c068004c5540b400c0d04184003034256441c000c0e071080402d007001080d4002102013134000581c0c2c201030030709119035014a50b120a2900418005185d807685030190b686038031054580200744000180507070280000d13142e00082c584802d00c400b02c0100d080e1a0050365985255500e0940000c4000403041d1050b88162160398a40c141c542c00d2103d00152604605a142c0e042182070102012000302004004040c0060400806252030070007028 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 787431321 1250 787430071 787430179
    0x140901050108090a031101110714010e07120f060f0f0e070503030f12280b1014031b13060804053a0c170301051915030b 53
    0x881c1046150801c02020200105031158000d0f414601a4200700c800c5036003601404c0b204c06214040070002070342d030007000b07005122802c540340101c00032320004d010fa45000b0344403040b52090140d08070922100343d00140d000030502c10030510a00000070b500852121080407604040700b2101c02942e00d1740081644142013055000900044005615062410040705403c0c001c040700d1102021303501c3c1c0800c440340c0300110301d01c070b40381c8a0560781000c582c4200c0501000d007a40329143c500400c3c0758546070b20618071a14202120810009503549903456442c62046100d25138416041d08040511010504070603240e0035400078800c80d0341d01c03013403420729042c00b030305100f142d055140f1402101020107480501102c4030500301c840b9452621724400c1541410750340707612030340c01c024280064100002118984d117005103044c0d03041540d241d4080103002c01540d900010f14010b210403c0080d004e259525882038014400542015141d0842042c0602540741302070302e0f0201c02040c282c4540c981207006100f428103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 787432571 1250 787431321 787431329
    0xb040f061719021507030c0f0302030a030501080102130e0c0708120103020f10020601141206070f110a030c0209040f0b07020124051818100501231e030a060501140901 73
    0xb5600349a0750000b2514000f258070f0040c0c0f210080b40342000d02d07001d00d640812803600f0280d0039000c01001d107070094681d840110b4070030110f0324020020400100501c20b03171b03e05002d02c80300035000a00301031041d044064010801c08920344104403500001e90210040d200e1914003600d81d03816541584100484074000c2c20070f89024414204e1032110b400ea000608504580820740010340941d000f00129800380054080c1000520540c000d001103a94064012a074548851fa144208040d01d460b00755110081c1c451b001c1e00056190303e000016180111a6542081c070400c00784003000c8055841c016807200455101002d40d550352042c0764101001d03203052841c916013042c01250107040070001000c204206a5428103032440c40c0000d0884400055003001420111b0704030340f4014000c0030800e0180c5070901401148000c40200b034039402c5007914190800ca0741c02800c00c8201615007a8649a003104a88080d0b80340c07107034060351408140584034a81c041c14032440c8040000d00e800d014040c240c007060348 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 787433821 1250 787432571 787432603
    0x30f070f120507080301031709061b0f0303070918180b0709050114161703181203070234090501090506090412122a0f0503010f03060b040f0617 63
    0x120080008202c4c0b01220305499000d203242c02c4041241c0110002030081604603074002c480050003464181009240b468024188000c5034207030301c184c214a6840780400e540b41000711359004810f03c29080c50f40c0b041ca5064481c0400018072180031240c10103950399a000c2690940515000c3c0010300d58403503501d0000c0d1000b801c00150789001e43c000081035200d880610011400110702902c200051080407101000040011986a007080014400889030308040409584a0513191a000c941d0140a40e4130800701c0b0f170040c00310500c13603001503210000c1c000001c00c40d0810ba00f60035800c110706040110b01030310382d0f074400150541c107200115089580181050344a03da0480402001400340b500710010000540351641d80080c404c0640c4001e0910001482c03000180360903100f106100100c40c21480150b5503884c0f001252843c01c2c240c4407031000b0b002d1105179104285062000c60f815402100c50300002520004201010400b4101120183c0d000a104200d075802242d4185004002280c803100c0088 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 787435071 1250 787433821 787433827
    0x3011e080105270c0904110a090515220e100c0c120e0d0c3302250801020309010f0c050a0206010e13020607030c150626030f070f1205 59
    0x14410303039070600c0f034a00e8100000c901998441c2d40d0000f0300c0101d08540e4040d0041140d81814a8504600ea40b51a1070500071a4000c400184101d25400f07001e000f2120074040c0c5110b5404030080c0448070301d4441c815000c100b0b5000d0010404410f03841107000218411002d402000194100b000541d500701c0d20590402040343d25100124214104580840307815051910701018198045424a400d081e0302410400c1c90480020314581000081c00e1407540d1049240301000c2c00144411404403e4150800103034090321405070181c401c0e10710303c10000007001018818030f0b41e6040107820382e0f100700c91a10103a51240300d007104101040c05018003011407070030314500f0b0060805c1e00a40c0d8020502c10006440542c40c04510300d81540c40c40d41c034155401a122f141e4481450070041d101c4031503d80d045400341d8521107600082c081c507104280a8610200080545240080001d40c0010754600c1541d440d000401280e40b071040b0041c0200007562058454190a5285050a000a6054108070802c5c45410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 787436321 1250 787435071 787435081
    0xb0a0924030b061920010c0806180405070605070609060203041202101e0f1508150f1003020103091b080d08091b330304021c11040b031203011e080105 66
    0x84c00240000d05035620703100110420720031044804142904141071954600803820b0680e545c01200b9078800c01040d110804040410b012900d46800d0032280034105411010303090020300d20841c024078030a40145008503420f0f520380c8646d07080f81c0c81594101d40c0e110720b054100084a8041c48801001441568104a400b1080364010b04004209504480541e5206600c03101c10400f40d112046201000d040c019800b520340c4251039460700413292404900c600704000400c82401c1825691282440c031310103003612441c66005401501d40c1d80e20490350344200c00311401051008000078001408400c00810344e0f0b42242c40b0180030a00050940052a00040c0c544284240842103040c45145c0540b0490201410b4070221800b8900c0a40514040302c41e006480a000030303618040c3d03002c0e038000c8400900c600000070036a1815111064001d0213009020b0703004145141582c091100100c02406460802a000401c00389a0f8802d81100c1c54503402c040004c0d00d44c40c401400f144c00303000c0c450001c100078100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 787437571 1250 787436321 787436347
    0x405070206182b11031309021b010e01050118150311061908070306050105070f080904180807060e070b0706021b06040c0503060a020f040b0a0924030b06 67
    0x300502c44044254090b20b918400b100c10420b6582c208040c0c604060780080560f00c4034100d1021080c0345001804401c1d030a01801c0021045401004c031090041d203a03035103014103880c041e410403040310f40d50390760714240b110070f41000f0700642071400421400051198100841000c081003212407607003030300303260051a0841d6003184039030300103413a0440e010600d207400c00800100c41d81300f2420304181b400c0c01400c0e81e40c0c40355008255030b4001d4405445c01d0040a0b100c100440792401000c0d03014190b55001c0d082c103c045003441005040101c00984080342e0744802ea940d44d0078403003041c641200c07480383c005160028010b480c860b030b201c54601d8401404540c0e2400403041031030300031180b01400003980060044000300786220340b60004d00032030080da09103150504100f01c070042188907050180c000d0340c00280c507190551003180d81045003000d4940c1024144060301800b504a00c1c8001c050ac2500c1c50085802c0c3c4100028094548048042c903165215691000381a2444502c81d540204803c0c8280700031a08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 787438821 1250 787437571 787437583
    0x30905070f0f0311030a0f0c210b0a0507030b0a030b10050f09070e0402070b090607030e01022a0a0f1506050603060d0b2e170304360212060f04050702 66
    0x1d004001c031302d03052520000080c1071401901d002881c40208010302420400e4124580080300c001d09200b00c5410800181660035010214008100d001e00000041a62580b584201c2d0002e01520b000500444140c01003110000e02c1c0d081a12050040d4041040d0b020031899180c01614003038401201054610001c201682800792080e070074040344510300c1038641c84d594159401e40c0c0e0058047ca426041000d002034985205a4020001908224144640c0d410500840b11144140040b542140000c6011000b64a4001c11036284a0180c20321501c08244481c4c880001d441c02020407610002022a4150444100d42c6c0001d001740000d1081044503524102c68212841c0c0203911603145903200440040402580d03140159000b07480d00342c86501881c0c160306801980c012042c0400d00d03114000202d6501e0041d442105080c00542804e13581d1003134100028450303e8a2107180c0386105a40803100030503a000150ba0301c03404000b10040210754900b0300244008107100361020003041c240709500075100c04e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 787440071 1250 787438821 787438823
    0x207080a050d090501050a0905062421011b0f0801080d0309140d030e0f07050f01030c14040801091109070e0402030606071703151207031b0302040c030905070f0f03 72
    0x4041440b01c00103205811201c600d135070000080107103190a021180080a80c4007003074949206000c001344900f810b250546019045200c803000b01c00c00c0c074104201c0145120030001c5c081d2000f214011025400c05d0164a240036141ca203802d48071851040018569508800d18608104001004224108020403a1141070406107070100e0300130064105518180700b4549040110710408504510b40750b415488000001c043d0310a486500c41000d6804d0b40c1e502c41d40c050b2550240c90308070b0401545d80240d01a4042103c14184003441120a582110440c2c006900410b5107944607042401003004540c00b8603039010b02210b03803100d10305000c0320081a1200030040e4601035075000000c14119a04d240c29a1401d075400807000300c04000f41d002c000030716001503d190010300c0640c03945543c140781070788044040e22403481c000d104252454582d40302040081d080811003107016480400981c40b580a09415400c90352004603040c1210300e4150300d0320980307621140c0c0c0409880340034000010801b46020440b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 787441321 1250 787440071 787440077
    0x30a1a090408160327030201110d021903020708061006120c020619020d0213030b09030901080a051005090f041b0510050904020d0608160503030a0906030903110318090105040207080a 80
    0x6103d0a2805680d40902165503201381581075a000c2907844100404509581c030070303a00d00098900744a111661241d01114807405030300320b02800c06d80e016001c0a21204a4003e10441c5d0520b40d60b40b000a040810540b004000400341d070703105005098200a0031407043d482c807131080080c0200320700020345070400500284604030a94814404c03250b801c1e01079a00300c0305030400c2103540c0c051a4802c05110001484101e4400b00c2e80d5001811000010098562240040c1c417542c0d11a5900c40402e070080c44010f08075404a0f000080100d0356444501c4014866040039108200508050910083c80e00c2d4102d081d5122984070f0406006648a40e556000c208840d4201280c030f42d81c82000003406800754140285c5118034141c070000e00702400040c82c0b0540740000c1c080385030075600c907802c0c55224461440783c2c00c041a0300550800c03104d8420750050546070302a160041002c0b000c1d080e0141180d028080a0821070440100758042d0310309030000c140180411101140f03017802c580e5419185018001081041c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 787442571 1250 787441321 787441357
    0xe0a0506130b0a09030311030901050306120304090606050a020c0405330d0305071a010f1a0c060405030a030e06040b010b1605070b3001050402090d0602030a1a090408 73
    0x2509107889040d8024003941420503844010450000305400f034584400d400081d040000748054400c0070044480719034040c1d54107841e41d0358120a03c0204011400c81c261213100030800011140a00e10030f41010b0900d03a135480742e84401003040246070120b0003d01511461518003400781801e001c0c40034050080000121882400c1041c103100c428500c0310f00300e550031401480700300d420580d010b80140710180c4a04178110060b00030010a10202400340140030180c10710781d03800e200c403140d2108154038408400310160300d0b04228048940c1401015202160305900101d403110138140c05008035244a00080700412043c6442d8407400c002d40018800c0e04484040003941106200038039000b400a15007102c00c80300120b5580000d00e0031688010b19a01c82406141d1420700c2c0d42100600c1d840701c200c81350500e81820390030242000300039400b040070903a110440001003c005581c0c0e0000c0c52051602801c0001c50700c200540810f030340c440e5004014031a5000c9410070000514001c1035070703912f094200801d91 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 787443821 1250 787442571 787442587
    0x91b0e0f0703110903190b0906090613060b1008010e13020d080304050111130608060901031a09010b1c0b06030123060f220c03020a0203040324060e01030605070e0a0506 74
    0x1451003603200303079034050040302c40f070300b9803900b4260002046c148120101c0b0302c5a656010304a0701c844d41522044016000880450105000703140c1814159005010020b04810031100207a0b1201003c00e80030702241041004001d0304840d02007955100c541d03a003000d03241d114954001101703c4084000208103000100c08034040c40000d5008880d803425090031150b4807010b1010128040e14940300e91400030352180005405400e011040c541220b9001004102c00d41c0920b0525529540c02040b1010a41d6a4030011045503a20200000c4105c2d814032452280c4021381005a1490320003488a80203070b050481c10300c8030020074a01c225000c604401e40e0304440d03e44c0c01c00100e154664104440e0b02045014070000311103007490140480d0318102c0d504020001003014250141d000e03200300c07100527030010f00c0308002040c000543c0b80310961082c3e0040a0031080307580050300719171443d0440090902c0000040c000c000743c038415543c01c41c11606101c00700c009404005081e11034140603d500401340820890 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 787445071 1250 787443821 787443851
    0xa0f0302060f0c030a1d0312030c0307030e0d0c0b09031813090512041707030213020906070c0e1014060304150b0306090f0d0302030115030915091b0e0f0703 69
    0x640c4280420007625641c0100700002030507540502030183c81b80240c1c08074100c8601e00010482c0c14400310851107419641c1d5034001141540004000c0000d06071502e127000764500e01030055001c078905644881c6100030144c00e188204101c0180f1803500e13584208009500ca0301000030070031038610700302e4840c1c0005140d40c00f104040d00001c50010030030303c240310f4048411a05400a001550b00603508400341007080044260740341001d00c0080c0d007009030400303c1c580c8c4d002260028000c2c8100a8045850000756071f461300d4841840d40d1200440008103800d0141d000e07410281600108421244001d05420300c000081462101500040521004055038111181546c0058203000350080030360f0100e25000110300d442e04071800440440740541201216400e003c1d00c2500d045c0c9414501011045440c00d4041e4010b0070702080c03e0b150418800003e40304803607035018180a8522071183e49a0241c005540c80b400041c2c41c0d080350861442c85000c000c0104141c000700c9a00000e0341c900415460b0b8004000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 787446321 1250 787445071 787445077
    0x7050d0305040905040c1d060f06031012050307050601060507030504060509040624020705010f0801090c140c0f010b0a180f0b150c0f0a171c020a0e0f0a0f0302060f 72
    0x30f0354160628041006104000d480042201c1c017112102c43e01c6d10030398643c0351000c90120382c8150312800c0780c4000003450514001a550140040511640d56612081041c02d650254070b8111a540d0000800d201040400d014490041c00c0904100d805d141050341d002d4082c3c040c40c0035030350412901084512041d079981e00684001c00c00d40d581d50386880c0c83d0030b81401c0b000a10110278009880384039070000e0785503c1024807848008855686840590800d41000c0c05040d089201e10100040c0340e03d2240740c00d034050010200c418040c4020140ba120380e842c81400c2d81e642d00c3d2003500ca621358800c20000101c900400c04058170741041c0006440a80d5403508006010303522116070088180e611001401401070003c0410390ba403003088410f00102c045c01503035201800b82000308448000300002c01410440c401030403803650040004208035290b0207401c8100e0700814400c1d000124880000c80050605c5011383c801c010040e94040b6580d030401252062121907844001e00a00c00015a076042030390401c03c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 787447571 1250 787446321 787446329
    0x20708030a030207051c050c0c010228060603051501060207050d021305071e120b06040f0b0c0309180411030a0309060e01030b03012f2107020c030a3207050d030504 72
    0x11b007521035031070a00014803a4004400000c1d40340305005284c030300f0b0741c00090142103942d61070600b00a41100326001059030a540d0304100c035526110480032001420601c0803a9030031031000e1051000d07600d00b440c001e1810300072f54402400f80ca15501c1140150b128065009081e0249500c08925500e9a01048424006d0201c046a441d010025549000703548580107102c098158242408000c1c28003040040070b00c0785202e0400c05503090f000401c1050640b1011300301003210101940e090890820109403080110324820031015aa2010002000380750a0082d44d03c0304190001c03d40380865682c0034104001c02d015420512044100c108541d038884c0e08280064000a0024841c0c03842051408090b40700d15800515141c501064600183e10b05900383e83c6d1130b02032006041c0c03030894820302c0b0044c944009801d0900b140681d501001060714100060010944290064681c506c00c4d06c07500030080034a405010a00003448440c0320036180001101c07400d558040301c192064500502c1d05403194411588 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 787448821 1250 787447571 787447603
    0x403110607050331060504021503040b06131a12031e03061002030711040908040504091a070c3f0323010b070b06220f0c020708030a03020705 62
    0x1041001e01540302010350f01407080000705901001c21000040950044007019050100ca0803100001140c0c0c0e075007103113401900140009140f2201c4040c10411544115010364500445030700388101810716008280303240200c0d030f0040125070701240000081c040d1008809200e0300c17141111300c00c0010b0500c02c80d40901008406804503100811100e4000d8004850251155002214141c03001c0e0012088482c0540c1c0300d90301080c0c188200d01000001c0c10013000590f500d00c41404085000d80382c5e0300c0b800345010f000320040e91481542d08981005c10900030484004c00107c9002c41000a01e20301c0d078019a03005031200c410701e103c26024001081607400d00e590102d00701c0c0c0100c2560301a0564046c004000007031083c0000c1040714058130425250a1040115158040210b180416440702c60590480d1004007040101c10015901401e200720b040f800c0d4099503034070414401c03043c80601c2099004902070001e00300b00c924140c1c02c00c1e1240100301c0d0041c10301d40c0005650041110501c4a6803c2e40106d80c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 787450071 1250 787448821 787448833
    0x2601060918060b0105040305121606061805150303070b06060f0a0f080a091205030901090b10051206010803120702150f191a010c1a0711070e0402060909040311 70
    0x40c1d4032640744040e10384151401c502d0442c1c00311255200d0703012501a00d401c80010070300c40b1442c04444400d9402100380c1011030a040014100080550251900514580c803500002c002c5540c1603000701e030000b0303000a06003900c48150944036140403041e980b02ca904800d038030090b6604c100100702c145c4520113070f25000c1d803000a000643c142c3c22168002c150001070303403041003c4c0e0710410f115080740d485c0302c2c000c0c0000b100003454004040c45540203680c4240c0650000c9028003803aa140841610281c40000c0c4001041d40c0c148003034182074100d030401d003045100800540d40b600500356164460700c0c0d2070f04010b107402e000260f0b10f203000700107001a801c0080c3d0504902d04c0c0c42c68590308460780544511141100c0c00780e0802101000d07003c2e00e0741c00303038146941c000701d91501c90041d2400138100d10700720350500c000c10000034510b1a00180500c505c40d20744403127004000011015050600fa504017402320100c000c14000582c48000c02d45032401001d641e030000517181e038203054900030800c075100012803203a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 787451321 1250 787450071 787450091
    0x40e01051611060f040305070215180a0b03070c0317040501060e0604090203250806010f0504201c020d090f051b033301030302071802030126010609 65
    0x15032100780309910440761403a07401c5248a04645240e03181552141d603503c0302001c1a941da044160140d00680b10b401d00074544442c43d0f0120301c3c00b0b0b05a09120150400c00314100320704c3e00c41c0701d680142c905812590300280c5400e01154020500010b0241410000d103440700c0002c0601038121090b03005070713148603c450361400703242180c041c052a01030304501c1280580030403014100f6004109400f50300030054440d46e403520a000c071102c0d8020380318a55451544000090111060000f5806010f80d0440600340a04003400c0c082074400040300c9030080e0008190107403188004406540b00a40b201517035400344522210b4502c06400341c2c03001c21021501e0044511304100c1c0740088002202d11501c103035440ac480c2e84004200c00d4402c1031000d9050b030045001e4113140e6441d002a52104050030000c8100000f10180b0140312410980046025a00945081c0400001c5011041d440580001e00358034560502d52a01c0c07114480b1201e100c800c0ea0b42c000390000c81c031000c4d000a400740c10007540c1040f0003110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 787452571 1250 787451321 787451323
    0x30203061506041806061407051f0f0c0806180c030c0d0603170318010509030409110d0501060203040306050108010513030c0f082b0504020306061011060a02030103050c03280f02040e 80
    0x1a103d8080400d4450b211200400d651f07405850302135401c003021300078950922021201042c00680760002c0c044d80c90421200400e4503226254041c10190b5a0a1641c41d0200502c0300b5401c2d10511f20074082c40340e10410020204400c200da500c440c0860380c854442e860040801d020304034540004241074100840c0009094241d0b02440c40341d200c140f4906001410f10000c2800c84000340c802a2043d002003000344218403170340c0c01903d03103021900700503403034a810b00b100201281d00a07080000140c000003410001d000e52805454027419003000204514201500c802005030006080103080c41103103400103050054200916000507040007145a540340160000c0310810300c102c0039001c14285501e090303a1190558840e10748074580c050010250713034850324100b01507000c0d10080d200c00c0080040309020086401d0200b2409a1507a880c090380f25411032a08a007865501c0c40d0a82c000ea2140310000240e80e444c2001d41c1d031034410210001461005828407400c40401040003a401c135050080081c941c0758 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 787453821 1250 787452571 787452581
    0x50121050103120201050a0605090114150c01020306090a0203090a0f21120f06030c03031809090b150d111908030301080334120905040f060f0b040302030615060418 72
    0x1004e900070001135486200740011140603008030350304010082c0040c08681c21071070588591440080803405841140076906905138042c031541d19050350040248501801c00729102a04180e20742015415032510403071056448500b100060014901050032000307000d18210700c0701c43d60800000800c0c0c2c0b00010b504c0034040c40e400c1340681c0c0ba440d28204403e40040392510901054a0f8004508040140744d40c03401c803840c1e0038840007507801d41c0c11900e00048141d91403045183c55481540296014a030042e840c042065868807440e005140c0b101040f0006a1640e441002c80407085030101d4148443e02c1d0b60410031078580e00407100310b102c00000400c000c200000981b0784200030440d12004a130025032802425200b040d9040d60043e41c2080200006660700c82c0c0c3c802c034104501d4070b013110594800015041c1c4120310b03c2d600c0301d5607940c40240450b0f0765040196010342458111a841c2c1780c51540421f43e01d21008103020b911442209080d485940c40c00e088074014000611541180b885411148000388 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 787455071 1250 787453821 787453853
    0x90121060807060507200f0d0605100e0402130c11010c090e0a0c02030403060f09150f0b0303030c070b060d050a03081819390504050c0c07050121050103 67
    0x100c00d02c0b10000300340744100201d400300c0c2c0c2e00008014080310b9141507002a00c0f50719080c3c41c1e02c010100c1e58400c86846d208180321215000c0d20020400342001c041702040780b41c50790080c040d102e50820402001d41c507840b41400e82207020190010300b0281c034000403640c0e20980c211340c100c0c55007440076100915620120500079a003850303907506525101c22920f070048605103400c100c00358105110400100391140c2c07200200b010b10004c0031500340790f19603440000001c51a50710208540d944000c1d4850401b0b07104a11544800741c000f18a1400c180100b84090702691200802d0503000d400003d0264941c40304140030580d000307003140c007880d0281c5406403c20f0001c0701c0c0660700c00000307145049190380018403010894605c0f05248445000780d1103250900110f0f11403801201035010b02c00044039002503d480d19407004c1c0160040003130800c0104401c2e140094801341007c041404523011540d40171501404542003401c00301c0c1d06141c20704218400700d080354980c003c25803500d0000010b000791a20718540c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 787456321 1250 787455071 787455073
    0x406080a0c14091f1d27070c0602030a021b060405121b06130302060906130213021303060f0c030212010506450319030e01051c2c0a080901210608 64
    0x65901c40240403141c50300d15000301422140d0a8940c90a081d446c40068014485e8500451185440c1d100c40f0160303030094a241a000ba40016441c04201040300c195001c00d820700c0c00b401190078941c450b0340d6150468000c1d41e201400010354403201042c001211158080804140c034035910b000c03011001112a414004c0d03001d40140800030f080c1041c0802c0e014400e03807000c40d07000c51902d81d5400744072000000308581c4d003103154200000d090510581d10913070001c621882000ca0300324076040d0244161002c034407411060500500800d0129a0030540351815280e00340c840b251500c250755074441c7d603500c0c1024480c880019800b03412000c2201124041c5890a640c0302d10007116140800781a6520300d40d075118404188101c158800207441200c2c09504004145411400d0501c2500340070203407111104c0c008103803543c807c62280000030030200c01c402d046024410102a80030b14a01d1511000482070041c00344600081a40040e0f0003000780c0450646850455000c0010a1842c02c0041c4180c1c010b140003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 787457571 1250 787456321 787456367
    0x1e0106081609140106020a03030f0b190302030708070609170703020a0b040302030613030f0f0233150a030305030a0213030b07080c0c0d03050606120c0406080a0c14091f 74
    0xf6252203164414101d4400d0b50042003809000d4500310001c008000d04401c005480e007465000540e40c044000e4814901c0820000d6514954410180340881e04d07402440390340c101a8080141541110609049420b40c080f0002041907280300581807841c1604025803001e100d1a021031041c3d007500181080d40d02c02d0f401c44a19071a2000040c1c10701e203064400400103500d4405c0068168440d03010b98018440b180100c1c1c1c002c1b414080907a1800c4c40001d511654a0303815401064030901d21844a600429002c0200240e850400f022942c0c2040c5408040d0034040c000010031040b031042e0341200c1c11203444000e90840340e0348034504140c0c207140c00c4d2800c1000a0442c070110f8250a60035088811090b600402884844800036040e001b404000345142d511003418400d800240d0542c0c9400c600c5403400301c0c000ca0343e803418004003800410001e051640041c0c03400310404000c1d90080d080011410700c0300d501036203507c000c800040145165000183c0007464012a1104540d080702c808006d0503208003030101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 787458821 1250 787457571 787457591
    0xd050913020c0307061107080d18060e10241e0506071a060306010b0301051207080105040501060f06080c0a030b031e16050616060c110a0c05011106091e0106081609 72
    0xd2031301587c200505107101c108030420464110368040d0302000000c00210250240c0d5446410441c0e0700c0c5080b2001507000350311202c84800103441420030310322802c1082c0904140709000e980304040c05000c3c0c4a518a00714100380710f035500d9119080024038006107001e41c3c44140745008940703196035503214482c20a509022541714a0080faa2905954421036000d00b160701c1e01d01002000010003010711618000c010300031402e0202030081a10843c098000821424507006441c070200709154440c0c000c010040c1c0174044c0d0380400000b1240c8072072461502244540030039001905200013480001c113a484112042c00904902080032080180001514030b842c966884c184901441822100c08e00650f0342040e280000c0e00650054000c600c0515000b03410784007142a4034030340400740106a074070b020145c0c4100030940c0d120f82500c1d824061640540840d040c00a4404d555411036a000f103403140520340b155a030102d09502c0180144500c404440b83c1407080403030550355521b076024244100c1d040540c201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 787460071 1250 787458821 787458851
    0x8090a1e02010801240e040227090709061e110d03050f09010e030423061c060605210402122b0c03120903051b030a1e020d050913020c030706 62
    0x261104100d445d040c602c4511034801100c0c0f0694180086502c503500340529400d40040c0000d8004020313440807006001d41c9010108032031b071440284560b042041c4000b090004540c0000805c071079103000040c0036504d1043d0101901c14102460001c5198821a161361035100d9054000b10300454900006810369281d02c52110300307071100001d0340040f59000704003c10061501190f4000680900200b88059600b1080004c085600c441c4070312106100800200003070114910400000f080c990a2452602d502200c00c41400b0400141c43c15944d00041d0016055480340014000114458000d42d10540e40f0b2a82d0302400c502142100c0e14000d40c04049900300c0c0740140c8819600303540684510303200b40350001a000c05450341001c03c80411500344003d521038882d03281e8140c01403440102460700c034036400744001c0005010061030a0303035500d0f1803182c909003034000ca0510164202860442d6882d080d0300c0205e440b600c1d100c0c0e40c440c01d00748001140350150031301002502c0d0a520440b018490304544001c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 787461321 1250 787460071 787460099
    0xd051501050f0c070801061e0b1215133204030504031b0b040308040503240615090d06060e07050f04181401080c0103150e0708090a1e02010801 63
    0x205010520070004504102e281c0c5019103080500001213a01e5141c0700c00c429030a40300e9551000c406980e510074170441280d81054030b00007910710011b166013494200704c00103070b00310340c041d00030b1a400c0030707100100d42e0300d407581d0840d10403001d4503000c1071140c10640001c00703454400810b40000801c5c203145c0b8a4008205c0d101d59603000d81d40590341c0310b007461f055450b01071000e80184210001030460a00000b41404890064001140104001a00c891410050508002c651000d42c031200c1440b49000a0000403641515002401550300109041c0300000407001e52203070403401d642c04004c00f0880d000f0031809410020580c2d10a40300865161079a030800d0380d0342d001c0e013804601c0c015024407041c016400e107040c0c6452400c0011030b010400580705403501c202c403503081c0c00c0468650004422506903503018028048a20303001c0f05c204408a150288800c40d59101800b8001002410000304141d414100304030300410b5001003654281c0403603120170050b4425501c8040b400314a0010000804040391020303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 787462571 1250 787461321 787461361
    0xe0f0f0603220b04080a030b09040f061104180912050c0303041b030b1006020c011412100b030108030c0c27090f07090b030f0109020a170109060207080d05 68
    0x19046490b0840505050344010402e240410390b481800c03404180000c1d80103000304c3c041c02d90300356100c040e80402810f407140542c00c60701810422050000045524280c50342068020600140d600c52982800000c1e204035403203414000a80424500248800d0f48402d51041c031500b2214503010201c14103441c03500071540e010401c0d40043c07000401054020601d100403400311600180c42c00d03180c3d5192445000c094038010b40b50f0002001c107004047d010461082d140800742450b0303c0c04c2c401304241c81e0700c905c111000b0103508001c0e1030106504c50080d5641d000600a200351140d241d60315200101d40d6600420348007010380c40751160b800c806040c0540881d4007044020079140e00c0300884403000e40c103c50060090030041c4107440c1d54607000c210511142c030203015400004200a1010300802d1b2500c0e450004094a07649820f10440045c0e50300d0480000300e038415455105206000301c2000e004240010021f0700d01e0b8000202c0c43c04000102c0000c08040c00811401c00041d03d40c149044031440700710070303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 787463821 1250 787462571 787462579
    0x6110c04110711130c0e1908070603021305120609060705190e0111010608070806010e011d0a1b05121303081b04090603080306030f030f09040c0c0203010501060e0f0f 73
    0x81c2c08100c100d26050703080f800140c1030510300740340b45400c04101e5078034214040024144075902070483c0742064210031074003600c408041c0b0060074000e41c41d46a079920b02c108014558002514414a2540051070008200c02130000c603020340a4000107464100849003116a4001c450019103098021410384444601203141c034260071285050a840704c18162070102c2c1800005c81d41151141030900425003d0408000508811071900140501d8070070306800200010070f1003130050141100c28038401e070001c010200d91400945407803241c00c3c0104600305c076503510207001c87c0019040d5600103000384844840314000300615581c441c03000d900c09039180c1c4010006120340c40450f02c10303203040c1007622200c922205414a084c2c0e0381c000c175030200c420b81d51085074a10030110410080c0d14040c415000c503540d100e0302a5140808031314181d2290301c03915900070720881d0340300380a0410354400c0004802450380980204210358641e9400303448604824480703480340040020752141814940041941d0301c40c090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 787465071 1250 787463821 787463827
    0x50711010c020d0e0f04050114010e03010911010804031103072d0b01090c140d0b03121e0d0e0114040203121303201005031e0601020307020409080f0406110c0411 71
    0x9100b03ca811250190513a407121178a081820b059582e442418002c0410001d003800f1100120300240840c0c814480e800d22907450003000c08089440c1145079850030009103460790b21581c40d0300e0f041e50740c00e403022030303a4210340700100c2e07403204000c6034110060744440d4030742e81070804d220301c501c0107813802c06c034080010b2404841d4001003052400c1d41c2c000e500070780c03c01d041c000c0040c444d0180e001055004800c483e2403640d01c400c041d1105007070502c80e01480e071224484080c0b030312f680c4840418101c0c10301d1252414049000484000141c0c580c1d01084180410a0003806000d00c1c801c490002401d003a1003c0e442805a051944002a07000048492288030104d980d5a501e01c4c1d521450a0104100c1c001d4001c1c90303c01c030012078955a5045201c06840c110f403612074807400d00300f06e500b11452004154aa896a17088140b0215031380020950300c100b903048502080c40c1400785821a09401158026041d055021501084664103c000c0b107500ca0283d41c01c5900b203180040802065842c90f241079150b0100070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 787466321 1250 787465071 787465093
    0xa05030304110a260712030801090606090503120903010906020705150a0204180b0607060c0f0305010b0307052a0d02031b150c0a09030b04031733031609050711010c02 73
    0x1800600c1c001100c0300d800d80c0c0c0907a41e40c524101c0c0c5007011b040214002420200140011000f612030780300500058601030030303020300300000b00e581c0d01c03085514503541400205030280c40b81c4c1c0941001490b2a40315005644034103162800c16039840221119620301182780c0d0004491240b00e1003500e0885212078405040c41c1501000304008001440300c0c0c5070071540402150012940c507018a840c1e440032a510300d030315042007079002800c80c0d80c11781080d00d100904000340a070707103030340700042d81e0300d000c4003c0c50601083e90f68072440f120010009444009070003054203903d000f50b0080060061000c00c44480500d240300c0702030710b0b41c541c40c0e841c07150100e0462901c082143c5c2d601c4040a0070741d1406030704020101c0c9481c1d80703d5081205c002c4408800040320b0340204840c0003400c03000141c002d1300000f4140c200c42c5010f07148104140074100c013442119141c61181c18a99802c21000303c4807240f0344420b40c240c641300d1442002800d82107030740401203009882c0c508042c01c014420120b1080e101e40c068031520b400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 787467571 1250 787466321 787466369
    0x2150d1a031e070b072a1413091208090c010306050d030804020d0614011401030905070b0d020f18181308030a06080f1f0204140d0c080a05030304110a 66
    0x40300b00d580ca010710030301c400415041600700c003d21509024005400c060074040262124114001c40d007410520341c010340410004034911b4001c1e00b0142d044400700e0404090030201001403041c0399016191401000c0e4003c496038102c1e452600441c3c10300140c0d8a1105c0000041d4107844180c0319240d00328114407011804684940440d5805c0b42c4020025500241c040d00c0342000e540085000d803040314100401003220310002000100002404c2c00c0600850b051529042e450303002c14801d4800c40280002d010341c406100760f04546081007403910481e00e541554190199040b00020058010760007c1007090341100d0b034589851041d1102c0a82c0c004c00c0d1440e03030701c591103a00044c14561219440d03171400308001205100d00610302c658034005140081a40b10444501031915207042000c1d032041209200b200041082c40203800f400303a0303131491703d01e4042c034100f0007510300d9034400d88150284c2c50509040040100042d40114041c442c00c1c07000082010801c004055240300b0607030365a03d12840c06000708a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 787468821 1250 787467571 787467613
    0x19090f1806091407092a050d0902010e0402180906220902010318050c0a0e160509060c06010f0f0b090105030708091e100f020301120f050a02150d1a03 66
    0x40f2524800901941c40300c1054a049401d80252403911349800030750f00710031501e41961616510b034180c2003280c03180104000d465441140c0c82e4182c038584074800c260959004500b03007140e25002409c1117640d0b05200349a0403d0880080d84036101d80d04190214450386001041c01000d28440780d43d036822642d080512000601190100701d05260300d0340e007184d401d07100440d82e41101ea4003a8014011035212007007086035540c015001340c0034428812040c4900144803d90381858843c150801c1503071501c0c00e800041a501486609085500c80d82001185040c0c000400104071141ca13908461000c0c0c40325014070203030184903032080c0000e8050000910380e9104884e569040211300d015034122a000f401403100343d51042e49103040a5101c0e00740c8926580c024070800603c889000d404600b10750500d21044644005240090300241c0c015070785009018081c0108043c840d402002c0540b0700b0001191400039030000d1941084d01850959844001703001c11642c0f01c81048020040e204480d03003800f000c0e101030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 787470071 1250 787468821 787468823
    0x616030605040f061e030b01181d03070c0807061b1b080c0a1d1614210112030c170d020d0207020906330919090f180609 53
    0x260311108005815202da210b090300c070034000d050108485041590000741460042c40ca444a02c030f0b511410004074100c0c044e49030541351220225850103880903452000307031a0072401c07440071800d10b0130907000c007a80000050000510a100c0703e030031075549804032900c81e6414442e10700403a01e180e43c2d82d13443d00c003014400d01e4110311662070440460813504203848034107a2030300104120361003840507075110300c1e281b0300c2c800050042c80c1b240c504003408080c808040d0007001e0300620941d50f0800c0301c0c010003400381d099641e4901d845403c0f1602c075413101001517002c070703050013080a0415011001184403004106056102c03034050316594103824181c3e40d46820b003c804945d8003c07844040c80554104000c5000514291104980c0503844600500412010b64400360076140704080c81290040c00e804c00c15411905820303060030300e00c0c0c0941440ca2b2400d007445000d4105500c4020b0a62180c5500901d00c01e06044e2800c41c5010881d03c050742d072028003120116145104a82001c6050710002a00c40e000302340c0305 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 787471321 1250 787470071 787470077
    0x9060408071e1d1003050d020a060b0d02180604021209371202030f0a0302070c0603051312020c0a06020f060c13050d1505090304060f02030325090806011806170616 72
    0xc175640e40310241803d440502090060708100b940130203100c1319005902e0104070488212003d98400e50014000054105003061544e5020b0000b0310180e03655410b46480001c00e2910000301e203001d19085e03840b09a2001040c101c1c4030072030301c032680c1400ba1080184100800c0c1c540500e28110603103d680c1d01f2030381e90010908510003002a040940d40c1a03001e0150034055031030150b104c007120f00d400d0b03132080e265400000c101480d00c0c0070032201d041800701018245400c0092062a20050f8030101d00b840c03103c0b035005801400040300000d010b0f07800902011042c2000050310201c0d22041890105840f41c020040390f08140581c003401141780907181541046e105059242982041502060643c0c0048130605025000400c007000200d41110007410b00903403907c081c501d10303d00324080c007254900d0801317071407442201146400c6d14240104c15010103400c0180458083e076a481e000d42c1124279048883d80140c90400c82c0001d080e90980c0200e45440c28500044c011540d11004469810b5007498003450030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 787472571 1250 787471321 787471351
    0x1b0319180f0801060314010b0604060804051501060807030b1f20120406090603200903010b12030a020c0d021e01051309050106030b06120103060f0209060408071e1d 72
    0x1c21070004400500414607880041000c3d0700d58184110603880410a0b100d050741400f5003840c15540302c1c0f080b038050f01e03203500b0141c0290f00c4a0800ea880c080992441c909113110880c00420115004859207124030340c5950148044010b0b1001d22211543d6181e03501c00c050140044c00c01150300440c03806031601501d49484824030800d1200343c0c5040700103004d04d240b44000003400d100e030580c85600d202c0548000c2c1000e0000f122200c80d90181107051030f8443c0d18400b40402c121007559001c0d00030700c0d4070480041c0318400010408440c1a120381c848288030000d0300c10480885c5090400b0f8003c003034890303002815035200890140c10003211411612000c0d04000040001c031207601500505e1002600a0080014256041640c05411140200724241c46004140000c40c130802c00c48401a0640c1d078018000b080081a001c5844d0180c0180802c0c143e02c03030004a000b1a034181d00044190403122840444401d102d10900380d9907110185000e02c005614441401c1c0001c00c001440403508141c0075604184 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 787473821 1250 787472571 787472579
    0xc0a020a0f0f0515370f050a0c230a0320030a180807060b0312070b040614040201020a0f051203070f0809010e100506060702151b031918 60
    0x3680c00c824030402c4600c19025484041845401c10212054100445105450741003800d402c0c5a038101d08003090501e08110400c1d42c010010035003110f400854516010f00c1118986903c08014001c200c908600180c9081841c6480c2445040003002504030041100b298a480b000c84003002d03400112100281512040b42ea0020398140500c80000001e40c54080e4680c20014516000c1e20103411095000c089800380d0300d80450010001c4402c0c40383e0100000802c0354041d4046400c2c4200785880d6240480081030714818050b04d070008620951050808000d0707000980110341d1000010355001c2d006074004000c1d98001000c0b89548003005006d0412106614201e2134802010390007100c4000015618900315100c090300328500580000d0020000d000c40040d040c001e50f40d0362501903c07404142e4541e070101d520b9885242c100c4080c03e401806420075408860350400866000b04034980009003d0700701c80c00c500401100b40c400c018042880d0a0042d001090110f80720040c41c244e001403190f000c0c000003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 787475071 1250 787473821 787473833
    0xc0c08030d270303020d0b22050f010b040509040321020c0c03071215020d020a110f0a05030f160503220f0302030a0807021305010305060105190b0306060a1b0c0f09020c060c0a020a 79
    0x105400100320001c1c1c0030300c200900307c00c00c0c0c07027015012030349041c0c0800050201078005000d40b0191841a0341340c1c0d802e99290b084c00c8940002030b0458080c641c2860700040c280c4e007411340050101480700c000b152400ca84d05403c0c55a194254400d81c00c49a8903503203000b00048640160004101c1d00f8400942070000c00c035085001c03030344904040b01c007003440c202c1540040c86080c0001c5010703100820151182c0603441d120181c50784662540c03980d011b600000c0d45509041e80c081c03905640c6030450b040700e0320f40b80d43c00c40c00c005032800d151250307091003214400050480b1804c241d100981e039001e0040d004c51145d6540b1409243c0001e44100da2149000602d000c0c0e82e022407003101c2c0210b00844c01090103508d020203101018030703100c124050001a8180c01e002159888007160b410070400d94069980c2c440301801126804800200c905600d124064030303900340005540d0103416030700c003031000480c06555074180c58200d100c4c81d080810302d40c120f0313800229030807880d801170280c070210780c016070f000f46010781d8074a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 787476321 1250 787475071 787475089
    0x20708010c0804120201180201030b04061701061406030c04060c0f0803130b0702161a1204030504050a0504020a0f23040803031b041d04030c0c08030d270303020d0b 72
    0x20307000111090100428440c80380c4030203451520500003080003407606690078100c941c1c0100080e06047d15440c3e1000c0c00d486951100c40107140300a025000780d202c04000c903004c2c040f10f110300c0701c4440350011074180f00d25000b01104c3c09242d1500c0d1840c6803a18140084d2100c001c22502594003107030b0b01c40e1890103d0724023001144945038000024000358103e20f845030301307100003400300011503101600202c005444502071405440104020341200c0341c271440110740301d10807440e00d12040e058501c148000c040d00080900151542110740c0c00c42c0a444a0520040340244141e003000a031100b08100001802114661a001400c0740714030a8007100056501140e4490740c046400d550001041104080180400d54240d140703014070309203810300d401d001c4a80703076070095100b11007800041d02007000c1501402c001c9182c2680200c401e5100c0e9642d00e540d81c0c0320b80040c2c8a8400752420008916a01c0f000702041060171440180cbca001101200c1e28120000e40010200c0710444d0341d20700042025580d44492 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 787477571 1250 787476321 787476341
    0x30b091801021b0d033c0e01091208010506030705030a020a090b0a0e030c0402030f18100c0e010f1e0c0c09051006090f0f05010c02060d05090319050c031902070801 72
    0x10140d04c100369134000c0483d51102c80580c911100800d40900541c140c044a400720b044400220761014620303036081c030052490b6419402e02c0d600e0b141542e4104550070b4084092502d042e118407505a0307982c814880144400c403041400510100006104180140d01a0008614526055003071903250401444158085846d4501181903a000301f180b5250802504506c0306044d5429421814022611481148040c007050326498505644155581c01040520a407500d0841d0500946001a001815142070b880720540065404001e452129000b0038600b90751941c1c002c84200d2031829400100c036035183c1c41d0301c100e030601004070002a02805500131940a0500341c03944d64036440c81d01d6000b501d5032106500c01c44454000315002c1003c00c580542000840d9000c1c01c0c0400380300c415100080e4a0f20a020341c0c044454a41070600030031910001c060b20079140708074105481c03422032060546150103560044aa80c1e4010030850710841c1c4100b0020100800600482d101d464031381c00e18500351854006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 787478821 1250 787477571 787477573
    0x2041407030e0f0303130b070e030d0914030a0c0e071b230a050c100c02030703062708040302010305040c090e0604030e032a0111102a0e040e03040b040303020c04060501030b091801021b 81
    0x40a005900cdc01a402c40320040003100207001e600e000b03543d141c3e0100e825100d000c20391300104001035a8a40114029030781c18030100041e51004101d440c0043c120100c1e00c0740000c90780e102c0c0b0320303045d00c2500000314004603030b400030003e0a101d29841e0402200c0400908010208403510191a0058400300405009903100d090089000c4008070760309288011a03602d050301d01201e0480100109940e0411942030341e4081c6000b00f83ca0ba41c40c242085004031540c007041e022454503420000c070b501d0200d052402035109649040e04040b6203020107603543c8080d51190ba101030040b0b6800102c2c81d2080007816001418142041c142c442c010000c1c2c108014021182105501e441200e40030000c4035072811084c00d103110f1181510002007000802502e0700304000d502a0342d03200310301c556581d0100700791801005150b41656455850b498000c3d00c07401000f48560107582004d9012074a0341c0680122507061201915035012581e41c3d08402081540207440340d169951708000e2841a070a4416402d20300da10235038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 787480071 1250 787478821 787478837
    0x51903050f07020705282705070809032a0321090d120f06210b0105030c06030c030408090a0608010503102702041407030e0f0303130b070e030d 63
    0x980003002a10700801803821500300007030901460f5201402403030032000c40307804490f004004031010301666000340c0250340c078080b54584121200d030780c6603168291980c41c0e440c1480140c42c1c0c04801d0f101c080b0199281d00b040d0b04188075441041d00c0d549054203110152890b0811444111f20f85181140d00c4110250000200001d428002c80f0800080c5074001619000030b10741e4400403500101021044580c0b5103031141c6540c0700c00911f100035000356002d0190280b04001c1c10507001c0000c0c001d0701200030100c07000e104040c000981494045000b9107403150161000c0c0c9107a54520764400f059000800c22500d2220611983c8500d840f8114158003800c1981c8038901554102410186404003001103803184a040c22708281007443c2070002129071441341c103c0040314880d170b40b0015002d482e4900c0c1070544680d00b0b00802c000070307600d60017200c0094800c0c004d03140e0780d40e1030510040c1c0f01c0c4170840e4103207001644200210009002c1c6c1c040c041d4480d0051411500d49800000082c0c00c240c11a922400002d42d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 787481321 1250 787480071 787480081
    0x504031b050c15130e07051204050a02031006180e030415120f0902040f0207260f0d0617120f1c09050c0a090603020117040804080a1a13021f05190305 66
    0xa6a000d13000e000b01c040c10000525040a00038154403444182c2001e0b110460301007000c0040811101800355401010348214142c0c603041500200302c540700780c0b0440f03ca80c0c0c04086084001e44102036402000ca8041c501d007500745510501c1c3c110071043d01ca41005010308016205640b1445009512242007401254030703522401048140d443e41c0f074080815500c1004524000399000d540209036140d120902803008218042481480c0501d0280707244811001820f60700c01e18180c0e00120564515551100c03004010102040d650030440c141c0440c411400c10004060005181c040d05002d540781d0320448070310303180704410020341d244004102e4595100e00030700c90310307440c000e81404060664030f00200071031803440d0002005030f072018410000e034510b131a0110302882680400c80f0050040501242d0717174401286003a1000c00d40041c1000003a00c000d8001c107170450240d11080c00500c0e0010b203007812000407400c40c0e1140040026a04007441010042d1004240c02c00001402e50041603e000400e4542 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 787482571 1250 787481321 787481347
    0x61b04301202060f010806070c0303021902010e060f19050604110c030d0605040c02070e060d1704080d05090d06020d06031b0f08030a02061f1d0106020f010504031b050c15 75
    0x800f40484c0480000d54005109000c00024810fa000d21503250480d100c1c819824160002e1041007603107444500841c0a00c0d02581c0c05400000441c2350450403144203580b80c1450050300c1e00c041e01e540380091070100040300044e441b80c0101c0d4011100900005170b11840441c0382015900040200d070098201091600300c0c40210710400c2d00420701580c1c28000c465400030000d4841c0c03d58004c0051014080e0b002c40e583d610303a94403080301d4aa2107003100d001549620404080c940042c41034513510702c503d60110304402d10890a03501b0b4040c000e000b11061503030b150b0790003020f500958a0035055aa40b1000000031a4814184046411611a150441c00d042842c10602a0642c0d0006801c0d43e00400400031000d03400200d96034031140101c000c860000236441222610701c09036100900e07070b90745003118a501010880f0118102c5006408441d2020468240c050a84804440c0034021556910402c07581a008a00d0b030350f03c007803003082507495013840f440001c0d5800d209a9983d8001c0140441e100c012141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 787483821 1250 787482571 787482583
    0xc0d1515090c090602100f1b0804150b0f0904030c23070f050307090b0a0b0f0a03050603060610120b0d0c0503060c1303020d03090b07060e061b04301202 67
    0x40c42c0d1a02c500e415060000107581c45004088004d440713603640100c00c50340401580030a44162054245801d100c0141400420301d00061310f080d980400d0f0b0180c500480d024a215190b1810030280c05003401070100c8080105041c40140140e0520076418031210006005481c400318503200f01d101604c0c41d82d031501240345418640d4010f200c5030544168284241e54000070014110f4000000100e8424028400704a80303d103968400802001c01042070399007040010040d0035190030303036501004a940c60800300766541c0d0058a0007600207620540c1c90700101d10903241c01c41390615520001c1401422840030800c0112000416900c0349010320081c801031509000040e01300c031404101c5818504002802d0703c138847c8030300c4024421501c403e0341c8400c041c0681000c070000c005020030192149810f04085010704070084802d40940140070004a40c8004200c44c6603088080c5131040c0d0410f810001c0c07240c0224410300000300800e40b0003032001407038240c101d01c95401900c034801000300744101c000b010745020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 787485071 1250 787483821 787483841
    0x111c03020726062e090221071b03031b020304051305060114090f060f1803031c02070c08070305100b1e090a0b150903100902030c0d151509 61
    0x4621010b80c540c514034000743c0c4030340000741190305113840001e43c0c03070f1200c004130590303a9103550150201000500c50240d40c050a2800d1280c0e1042810708205051a0000300c0d040342e200020448400c81140c443c2c5298505c1c9000510a080004424500160108210341607a44210050317100180c107000ca0b080103a481d94101c41800030502180c1072a8001074290b83c44900800c01e26240801c008a40c4e58498520810360a4054000ba50742c2102c583d41041940c8404801346506a003052002024240007084807018003c04160075243c00d54605c029000c0c0d8401c40040c0e80d422107090000c40c09031801c3c0020002107104400a04000c520003c001c01030300c50220103e4810038034440302011158021b4002e0144240444070903401c1e564030b01e0118010014031040941001c92045c11252698280b0028010391008030110f40c40d400c108800c4c0c0040e11011840250503030091510f007651402c082d00e0302001c1e43e12410446445000e0800c50a04417407801100040803500c0042c00c01156210b449948062 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 787486321 1250 787485071 787485119
    0xf09050610090b19050105030403031b030614030601050a17121605071a07080f0d1a04060b07111207080109080d0b0102060f040b0c1c020703030c0c050604111c030207 73
    0x254009402225284c02c0d1441241c1c1441800000141014842c3d0301483d12600f076560788500407280d40390010010605806a414100c00c10100c0d69071034500000c10904a0b60001c1000782030a0400c400c007401e016414080f20814441c22010300c00c01c4038000d02601100c452544c41e070741141c800e42004c80c60022207038000100300403041030117910031503042d04988241d40c01480b52965008030305449038003481180003421013980b600c4500c0814000800d8808a050700c100c80512545448a81404151250b00340003071442c0750100f26102c19051002c023002c1c0442d0040140c40d500c0f07644000302c40c25501240700c100c503e400c0014080d041c0400b140328200b0742e0002071004051620b481c0d1000c44a00d41c01500c0078200001c500700055007071600800310380400c00e00003034010380d40b8a01c40300d00019400011b0200c0c042070801640f40c2c1c0da503100f00181c20780e10350041d00a10032615551501d85119132404409500320100080d03030301030782c10301c410350113801442503000307050a41c64501c100759141c540440c28800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 787487571 1250 787486321 787486339
    0x109021203030f0c03070503040308071b050d030e0c0307140d0524010905010608060415050d03080a240b13090614030609010b0a1406091801090c0509010801090f09050610090b 77
    0x5645d80c000d06232588203a0504042c8240d40301c03180203982e49042070000b1040301502d91011b200b009400309031011030b40310350f8509000c82241041c403a5210a03a05c2e01aa4050384480c4040020b91040183c42c0e02c0400d01030810314441e4070b42c0e21503501702140f868800e0001d400581d44400c4a41c0105841401040c10220421142d410110000d112070406026140310321b0700d81140e00c00d461f69900300c0200600006019030752200d0b40340b401074402030b4121040817225280151000542c0b070341d0783c501000400c50601c4030090900700515040c4903042040c0c4190710a40a900101d1000b032184501c0700500007241280c226076808004041c80c198004201c003101e03034185500034045481e004003420079540307090f6a0054407500ca60120380389000e06980143d00598940041c00b0804031580400c2c141e1305011000d11610305440d1003034440384601c094250000e1010740040000d11180c2d0b211010021000e800411070303000c0382e100c50340381a00940d61018500282d01003004006414411885810b0301a119542 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 787488821 1250 787487571 787487581
    0xa0207080d140409050612071203090914190b040f020706051005011e0309062a0c0804060e0d120503070e180406090f05012c1b120109021203030f0c03 66
    0x201c0c2d402640314900b4910707240c01c0803d003240d803400c2058503070700f0880003180d1217070f0368030b102c0f036801c100704044107901040c0004004507a516050280c1d429400100d0700200032602d0340c2d041030302041c11003081c3c4498240c0c0c400140700c0c15611401901009980c02c1030242c0c07151032508002040343c5029040150f4203402843c00c00069800c0308015001060650301108680701c900701c154083c21502000501d03c0c0d14040790001611080104141c17440b8421780b1180740c010b62154191000014030a01a0085a0610003048901d100d103400745a40e080142c185084100180e982c13030341000301000000c02003840882003203481a40100000b0522400719500c8414000c142c03003000780c010b4040d001400290300c40349a40140308a5280b000401d651010082008462a440c1c4002d050410b800518004124008100c0803013800503103031030940c21011b074100a032403030901001034a80c18503601100c19500d904601e005a0b980e101d020180c0704102c030246a50341741c40a8018650b4070003d00d03a070041c500c1401400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 787490071 1250 787488821 787488857
    0xc1206090703080c0c1305270a020d031403070f1b2102120c01050910020a081f050310021b0102040b0f0310210b060a061b080f0a0207080d 61
    0x2c0702d41001100f503403500e601c04c2e0141460022188550004295545a103200e4200e501661080e900c0c03403415840380c4142004007080d050701c3c8184840039405043d06102524126072900f0300b441c0719061588240040c00784140c0300307070800c0b59441c0100c2e202407c1001d840d42c00018061f5904003991222050600c00d40e1003010100b114551091060200c1510310640e0b402008411a45019202981c0d100c1c06000190303806004201c0d170013410b5000c2c40f06d09244031500d50080d00d00303000164941d12044d079034500d410508100b01940b00c03114042d0080e80000e0359182804400d200540741c0c1400340c0d40d00c40d00c08850940c4000c450142e100c0340e10412040103401d00c41c205030741656503c00e1000e540c035143d400e10000b03031b900f950304040d0741c80120b02060400b500203a68070084040c0300c0c450000240e03882400304000c40045108000202d2034240d100103942940d9100d00c0d641510402400d03051001800240216400105042d00580d11051007070102a20402101001305114a00b1000c148052070000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 787491321 1250 787490071 787490083
    0x280b011203020709110f0c070b0310081c140d0902090c12090303010605040303050a05210a050703060503030405100c050a060605130e030a2604122d0503040f140c120609 74
    0x2a81c040d0000c21f406464280500c8910000c3c44551010f5440e401d00702c44900755941c552041401d41d01c0b5580d00c80808808007071522080c0001d86d145e40c0400c03810780d0b000030a603502c040781c60302e015980c0e003140c2c20060b6a42c5420500401c40320f00d0042d12846440102c80da9403102904810a960040c001004015400021181500c2d40351520b6500c42940d184251000d01420709600c160801e01240290781130400a170807481118011814812601e4181c8241d08440c1240036444e01900100000d20039414082145014040c16281406440246d47c80e0342d4240010a00300712112602e41c1c20802c40c524014468140010b91140304000c5058013422180c0d07a44540c40003107061001d01c01001e110102201c07007004503030070340a810030058503007032408003000d09403500d1160119038020300380644801113000c1c81628070813682004202c42410182035999403c010002c8580d1030381440d140b000580300355111011070512a004002c1440500c0c100311018000160b14805039109200700200c90000241e0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 787492571 1250 787491321 787491337
    0x5040b060f030a0c0e070306050f030c060f07210806031c03090804080303100812180d0204060b3708060f0118140a05010503060102280b01120302070911 67
    0x7988450380c9845000c82d08094403108041e05064001800107150030920100510549845d9020459a51208104010040c000140c00d800d580100c0d00040581005c2005000f040880b0340441d040002641c0c5103c0c1d0407419295503e01c0c1c4240c407401a2503160042c501d01d030420400c4028100c41606021408842200c1091040030140c0321620b02e000d1001d00803c40b000307032800e242640d43c1d80c90007088600d40e510081c8144030b1284285003450700a10021001d1340c04100da000300c1044034654480420503280d100a0041c4c0e0b100ba50303807400041c8025038100500340150f89a05050000301c540986100060240790b00703030204074880103001e5516074421041d6070720040444070043d044584900403908403211510f500300c3c10100103400710300b0000d1402041040b51049812169107502c4400454540c042a2040e5015034001449607803091942d294080c0300208035121401b031450320b602ca1462000003a80541304000444801c1028183d0512500000d0b1240741e070107000341c04810706a00e03c40d1080d688 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 787493821 1250 787492571 787492579
    0x313060b011e0e0f0906060d020c0f011e0b010c0f080a030f0c091a04080712030c02040c05031801060302060f0a0e0409140d08070e010c11090403031e05040b06 70
    0x4840302180c1c1c0203808101d11440d0300030301e51020300c04024018140c002c04409040c452840320302c00954511703204528170b05c00c41001e00300c14100030506006c00040c1d013103880140c8407806808003004005c2024071905514140e40c040007000e425000700740784112880184481c1c1081803244078040411a030702040c010003503211907425550754030408110700902d1000300c3c20400c40d0520401608040c1c0c405c1c601c205540c2c0010b80140400c6610b01017020511482c0310b0003586070400e035802c000e010f0b0440400c048150084c100010076003d1580040c01300d891500707880d00480c5012080c0400303103491800071040c0c201040c0080054906580002c1c0241c0520a07402c50341007000141d0075011442503042e00c03804000908203111401300b5141c0075402843d84811790f00d0901c1040b045d440510310880b1030034082c40c8107807a0f050390040038200441d806600e1410654080468290a482c642c5a141a480c800c5000747c0d40020a0640146101108000311042441450070700b0244004201c1f52104580c000700115 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 787495071 1250 787493821 787493831
    0x90a1a070c060806011e20010b0109080a1e030504120c15030b01021005061206011401030b011e0e011e1206080313170a080a020c0102070e090604030f1b0606080105010605031306 78
    0x10f500b00c81100701e5441c10340c260104078a044040d51f00c150821800c952003629102400e9456620140c5e88500c101301c00381c181d1800f2001c030450040d0300360003c590340c8d00900d070080ca4280ca98403841045040308004403008206000108030b40c8010b4a5240c5170f80e0804d24090002d0442c00700000c0d5101c5101500c4101c4c9075551010421360343d2889102c4800f80504010b0f81d400e5a0b69000c4030340e4201108000d507000c41d04050b45017442e50701c141c10941102d01c13104100aaa0008103100320703004460748140070b06102004514a0340010901c05e10130141c01150b40308018080b0000407001a03804592160b2895801071003481407248080800c0026160551900200b092807010150f103800d92484028041400014482e0b58080d1301048031495041d007a0207c941640c0c1d501d04001c40c0f4401243e200509420006c00308000a00c2048894000003207450f183c0d80814600101150305075941e00b046030099520401002042d00c00e01800d0b0052185090a500b14605420040303c2040c001400510351030f514 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 787496321 1250 787495071 787495127
    0x10060f110712050a0213050c040b0c0c040e0a120201231f23090c030105010c050109050d020a0614010501092903010308040806090c1005090a1a070c06080601 69
    0x80000c10000c1400312045021090326050064139050310090503800342c82440016080c1004a020b40d82c080d9092210f0a071030a481c20700070743c0517030708244c05100441c002c0c0c02c03124440e9581d034040c14a6465041001e0180c055040c5040301800400298000039a414040440b42e414910440b001c00c000411602e4101c694403072141c81c40c2c0300c0018603240100c121071140806c1c490301030325050401030014004c038054140c240e02001010201125111050b66080006209651155201c0c0e00800c2c40390700081000c4641d50f40d803505003d08214610011307400b400e0110103002a80c0150030021819607500e00b640d5040200082c04a083c900a00b1819008144171051907041d8504c580407640f4450f000c01d859585a140100c07040c0d205204000d03c500c01c141c00300d401450045003007820304900500329007100d45c010405030341c5a0081050f0075031111400c040001c0010f4040700b0b40300c11078603003000d50781c1d40c5c401807405507011000d5802020800c8115070401c9010798110300c420000b019007601039440e00c500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 787497571 1250 787496321 787496323
    0x1502070302040204151412010306020702010c05060114031513030e0604150918020315040e0708011a010807111207170d061a12011703090607110910060f11 68
    0x1a600c001e4000b031000a0000f52040b038040c0001e80045103aa0f40d440302948a41500320600520315000c9186542070f0041001a80650003441481d106040c5105085101e40b46c450611509070f02440310540c00f1081c880712450244030071074142040c0c2d0700c00103950421610410307480c1c0340005c0c02014042c5d00e205001d015a5402d0650300100584c0280d03280300140c0c102d004100000502ca40381001c500780c0f244140c61285802624401d10700d0201904222658400b040007a02c034060301c500680c00741d94008200c2000038020002d149018021364420350034004001403444a0052125040054800c0f04040140d00464410304113100ca80001d0307110700f024104034191003ca40c82811081d00006000768811610743c100b003040752510002000003038880070018090b881283e20070740e1030403071400050018445103920303003e0000898003101e0070f142c0c0038008101154001d03002500c0b81046102d01c612a4540340c0c4015500803c10040c1269007460075002800b00741039501580240611441481a10300c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 787498821 1250 787497571 787497583
    0x3091a0f0313111c050705040603053a020604110405160f1b030807171b13050315150103060608040201112d060a060627230f191502 58
    0x402420741c00d2030380c60004e42c08184450128100c0340760268910005c0d4900c0c0911407042240c4d0020b0103400c0114401c1000804202d44003c1030380030745150700400500c0d5000042e18000c01d0000d030010907980c181030904401c85443c500843d8401c41c20107042204000c0c5200605404039401d044c4259856403401e400e948080040903030300d15050000c1480e00c1819403011410740500b2441d29840085508036420943c0b4080866003e403404808c1401c0b45a14109c410003031920114403008800429118000203041c4070500c43c0c50400c003480c420501494a6110130b00b118580000d0804200c03440c80c0c1000a414400d0040c00a03042c441c03902403031159500140320410184901c41350700014060b01d95022031340c1c04001d9154070340501c510b0b000694890118860318003a5007407034a17102c454074210b07184500300c0d10076108051b4051408a8000900c01c0040280d5072031811580390340c65003440340c502400007a2034145c60040c40f620000c000240024104c0b110107081d00c040007030040c500e84912000381d25040d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 787500071 1250 787498821 787498853
    0x501050f04081005160f0f1b05011109030f06090604150209040608011b0e0d140f1b0f030c09160507020303030f040c0e04050d050d110703091a0f0313 66
    0x4018004440d089042d2503101c4c901c110844048071205282c10b17002101d405285075540b4000c03d80c40300300e80e20700c075001e501c4084c400004c07640c1150b035510b20380d030301c46e801e50340306101000340c0000c003103092103da10702482060030700c070f6410004001c0d07860b00c160060b40c0e4000241c4040c080700c07441c1608541101064044030130b18440a0014001c1d5a694562503000380f40b44c2d00c81005801c0340f40d80c2c038005d044c490b0520301d00340c1400038103086096030680c641030041c0c2201482c10f400343c030510b065600304042c14060000c0320301e0803080448081c04480184a440c007000c0261500c0b03501b0a9244a070300e607807001c80868010b9091440c0c0d5041c1150510f0940d054031070040e02071b5242c40080104880f800745010040c0c8158414600e0220f03459031803581210b11078043d18000c000c1e030090f140d0726045034440c50142242d03207040b14010408080780d11508a04c0e902c5160b041d40016420003081c40321042075800c812500f4600c001d524a01885086c4041f800d00028020580234008507a0500520000c0c1040314029 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 787501321 1250 787500071 787500073
    0x51504031101090f06060503150f0c04030b0907030b0a05060d060b01030b0316170105190b040b061c050c0301060203091909021603110a0c051c060609020a09120201090501050f0408 79
    0x61070f02e130304010400010366401115034500341540464141804580800e96460b440f6102100343c40e8121072440b18100207007000122070382800b0010105044102e824001c4a0750005004100d0030760a00d400c1501c8000d20f090039403802c0c58103102290b01d440d09450541c0760420400100d00d10f2207401203001e401d110321240e5040c0704e003505c4030614401c01e40c40039040310b028410711413042940e00c81850983d001200c03071030560341e0b580328079001c00c10094000d074141560040c000200601903030300040254110065805100c00d00180407480c21100d0b100f202c0d000201d4005160a641c50a0350095681c81002109400366403480000404d003035221800c070003c2c258142c0d045d5101d40c4421101c1c06500000301c5c064000405102120700c6010380031410255141c0c000e101c0c0f05041d4188010b104007054007041c00c0c40a00d10303048441e0301003061403103041c01031b0466486c0036030344030040c406c002d020f030100f41c00c100300c1040518a0000142c3c1c00860180455030203080aa8448610310020f0003207000341d41c07240ca06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 787502571 1250 787501321 787501331
    0xc140708061819240e0106150314090c04090c0f0303030920150a0c060e0303060102011a06030a1107050f0d0306091e0e01240608070507051504031101 66
    0xd0480e010301c104a0304500c1c904070381121943c83d803281140c032803481014142c0080341c2211110384110301942a00c10006a9010840b00789003d042801c507915035124030307120082020002101c81c0d1502810324441d1100004075103a04100400d10345421004407014440c1d0340e00d514180811032400d540b81d0050a0b0114030f040907966030f04021f009403500403011654900181c0e03032280750016240110000c003a01a07d014480000390850100300e9102c00703081c405115040e41e41d00c0004140d801460300402c0b510002e181c60303003441c0e00003a003520302001e00605030b03141d00d400002c0719881e00f40070b80c2c0d48010f0f000c5021900e50090104a20980300382a00500340d070180d08101d800900c0002118800014165810070950b5500d07001c071003c5070b0006842412000c5032480c210600301494004918180c04200000355400f903e50403400e004002840b85c01340c0000e00301d0108290703504031304450340c800300d907003812032500f0380f540ea986071240702d695000460300c94400f006c1010315115619451242032944002c201e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 787503821 1250 787502571 787502581
    0x13021831031e050702010c110607030306090b010201090809040518060f04050c090115230d090b2511030d020708181516060b060f031b0a0c14070806 65
    0xc410401500c240c0118028480d800403040840c01d140340205002c3e51000e0500c03009500450310719a44030403e07108007600d103210450355500da1006001c071510a1f14001861450030241c802035800c03900070307103065900d007030b640c000454040b1003103403d5860300b29000945569802099054503864803442e07485842000100714440e800501c103103004500507400c8440e1910707040d00300b000c624400d0180b004007141040030249c103180503410502801c02800000d507d001c4802c4200407541e00700031426409180c96901e000240103030101455086a00441071aa002c003041c240c80244041c8a402c050130444010011581e450041c02922000900100203660701d992505109060b038000e000100261b001d6440003020901c3c044e11101800c20381e4000741030511804c0d541c1d0120031020340780d0a0b44c1c1607460744030320f104c6680d442004040d03100454502d55182c2c14008042180018100b5412021500400071207008607003044a04c0c4245501103c241c211401000c24203080c4800e95000481c0c510810b02400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 787505071 1250 787503821 787503901
    0xa080f060703061a1b010b040213062705090703090b040c06030c020d02061609050d1b0b180904051606110f031918080a03020312130218 60
    0x41c000c840694003401400c0e103560640c1014110310500400c041e00030031135640303800340c040d49814207485210700008903042101d0100d020b0b64040a01019003c00c011000d00074990003960740000011780c0328038240305402e01d0b0f1113045e6409a40c001ca5104110144c0007610a6100307400c04003090307500c0003518100b41494a410990320445000d4880441e0400680400b4203100081c43c1016542031b03070061041e17032260100307550425040002d28040250801c4041601c0d00c0d4401110005480740c3d803841e0121080c07040b84202c0c10706a03000007101c4081084410703800c0800c07103105804044110360100c0d4944031490400d02c0d00c003045442501a18101c1000100540c110801003c40341c1020140c510554240c503210792a03105111400030341402c40749013240428400d804042140070154a2115032549515440d403405450301421001039200144503180c120340c0303088641d0001c14802e180000b9540d0380d0b000900360048484c596502c6e00140c4005403021102c5560207a115404407480c2c140d00c05210091 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 787506321 1250 787505071 787505083
    0x304120c0801020d29030a0605180610090606020303070c0b130605180c010c1e081b0c01020d030605091f1a1e0702030a12052b1b0f030207020a080f 65
    0xa0100c0c0301c1e40f44034807010440026202c0c03501e10000e007c3c110701a8179664810090a01400140a4002c160050083d2000c204079070f40c09104000c04015841d8601a01c84080ea401900f00d441103400600070300a41c2c41c2c022025061040e032101c0c040c100d5680d00142443c1d0340c5d8030485c02a0205003000240081d9503004030480e880e6007504001c1e501c01c41307002c0005450a00c0c0e400e1000317003015000c00c0c5c4620b241c12002403038030403180300c0c60741c440c64400d524004100d00f85031070b260104203401801c0507a0680d0303010040c003000c85401e8101800114503110001d0341d5000000c060b60748401c460b10010950b08011200f03d80130305001c00c0b48040c02240c0d45051240c42e04464500050b003041d9060b41882d8101182c283ca4500383d000b03004200840450386d58601007a05003d00e2400e1010512011040c3e40c190302e501b841d0b500c480004401880300c1c04c2443c000341d401252a072080407030703056131581d550340e8401d4400e541c01c80a81005641c8088600c04150009055800a0728601507900400360f240e03c04201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 787507571 1250 787506321 787506341
    0x3150b0a121403030121140f0601090b0901051e0102010b040c020106030302071a031803130e0f070807051806120c0301030c0b1314010315030b01051e030304120c0801020d 75
    0x80b4925503407040b40c509682e0300c02809900d01d480314150030801d00150030f900150340316100388414082036a00712804c40ca4104411004901500400b005201d860014801c125568108469440c203551403c008503281c6d070320000207542e030002031404015050b4003d402481c1f191401400c1084901000b4100a00800c1c0601080b03005018102000a402654101d110800c0000b102014590303213400000800701c0581c60010291801700b8004021140081810700c0c00800300403074a8074162800c1001c000088800500c8001031044807800c1c4281e280d440401d80d1040c1c840400d0030402141d0401c00100117002d18803c2d1001600200d042024906481e0040c5040324800e0706802c9401e40c542036050891700605000b81654400d000f020020100c1c0d1802c440600740040c180040d03a40c03202d1500444180c003d4105130744c4500d2000041065003805501d520500080d06100305142e4600400607440b8801c61080c00c0c0440400c02203c2d003401170101c2844000c20301c2500842d920203050516030060b01079002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 787508821 1250 787507571 787507583
    0xb0d080d0c020f0309010c15050109090614100608060d0503032a0f0f0702061204030f0806062a011d060601020d05070203030a230a03090605010602070602030403150b0a12 75
    0x41c101001a0001540d0303424246210040c5090050180045a0049030310506460f5840d540c00d800c01001464170859001e801100000300341401c041c04c04006a610ba015000c0c0c0380542c490070848032105140d05a41581d24a1411048540702c071400640001c115541c050702c0c6000c00002c1c042040d00c0a134003003218025100c1d4030707207000a801e030103494036004e19095003684600c00c0055241003000d0900a00d074807031000702660b0500d8101a64240c007190b04503412000f00d01500074110859401031401daa024400700c0d11340f450100525a0f00303041420b0010a111940003101c00ea40703c1c600c081d00321072881c0308408862510021841c4042e5a00c1c10151031190144c0600641c00d80c00511030412134a01d0b9401030021450b210302e2380c200f156480031907050400c0d07a0940b0f00d818003500fa0b0010013441e00e51495030b000710700124075041600445130103900510942d0300c0078004000c40c580100584080305e4100550340c0100880c054003101900d8498211a800409003c01003160180c4c5490302e540e45000381 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 787510071 1250 787508821 787508831
    0x1051e0906120f161d0c0c101a1e0d03030203090a05060709060909060308040e070c21120b0a0323060408190f05040b070804050d23060f06130b0d080d 66
    0x125505a080c10300c4280c1d801741c5c16140001891820184e005003014407034001200d1079086000c2d001c0c070031645910b10040c09083c2d0001081a149004021900d00301032030381c01c54410482840001d82007508403403004003031540100002c0c0000302c003072120050351600300040c1c0d04245440d0b00300030071480060003140d0108816240119651406105a03c00d90782e112481a25007404c03c44030390b1034058001c02c0d04d002c0081804181002a10301595100100104417a1b992400120100500500103d002c41d4103050b10384008224550384022551003102c0d0171080e0f038034204500d00c00c240c0000090710100100e502c24a0284010415502c004101c80d25030801062040c2d000ba28045031a1208a401840002d00070f0100380031030000240144000752259030700e94941503032440820049491034505444c40c018010038200d101404030a00c10248c9025030103402e0300c0ca0600649103032080701510160041c902d900c504115644d0641c8a005018cc1c0100b80c40f0204040c1c1c603101c403a6a1040000c018074078101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 787511321 1250 787510071 787510079
    0x70c051c1203110d060b0310080a2105070b0f041a0f0417040807090504141c081512010b040b0a03020a0b0705070506030403050403030801051e0906120f16 68
    0x30104000c0007075004002280e421054403049020740fa1200e8402c210080400000c607003400603100c0c07400180200091aa02c81c500b5005417103a680c0c0b10340c0000b000b40c01c100030050000e4003040c1003110000e506001c034480c007150090202c426000d0090010426041d03002030007042d0b070144908900c2144034100f4810709003413819a0703802c00325082e206900c0810002e03002c64000380074943c10010a11030292014101555550500c0c030307100155220000040d0b4401c24401444240101c4141160102004010210483c0024502780c4200c0542204000b10300c0c0100380e03c0c9891109055001a004103000700c070365040b490301c500070030680c80c5661096103054041401420948001c004503034005044201e001d1174401a1340c2c25912508046660340500c1201007243e80e60800503602490280d0b031595180c5055180c00340c00082e040c4c103c03074820325980b400e0031524502e419842c00c0c402015940c800f003d40710500403604480c400c40e410500307400b4194050340d40040001e958440800700604409a031540e03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 787512571 1250 787511321 787511359
    0x50618040f0e060604050702010e0a0b01030c0609060206130318081f1814030c120c10020f03060d060b03061f051005122d070809010b240708070c05 65
    0x500c182c00e40000d800141d182c070382075002541c07108141c0000b02d05a0109130f496400d000034011304844881c44040140b040c40b006d441c02902525541c20408405030a1403c007035500e001c000c08142150500005842c01c161054098100002c07248448070101501c960001d5117032071150140035106c000301000c00c522002a03005901c51042c0e0f11112140300505a181e25180c034040c04002480b9200801285801c81000c004601c088952040c2064481080c07480060506003c1240119517600501421259490180441c0d40000080300c1198506060b4a0a10302401d40c0070300c210340c14000d5074104014011200c114444083c01c01c914480c0b09a210b8040001100885d450000000c078203100304140300e00000e42c00ea8100104124284076140784480c00460031850302d00404610481e40f042c040395036003202d40303941c11001000091040501180110300112031680c44103d50720200e0a81c3e95200c070000084401c581d8100c403803d5950380f614205a0901c06003485020300a21401195100c0030755 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 787513821 1250 787512571 787512581
    0x6060f23010c0b1b030c18151c02071a0403120e0c101806020f190f060b03070801060306150e06010c24061712030c040504150b070c080c010f02031e04050618040f 71
    0x25010b40d01d504100c000803c1d02c1c9010540c0117035800c11032b0301300000f0011440340c0c08042942d40b21031224400510f085c1c45c000b00025042c0f04440b180c1801c224202064120126600c00c50aa041e9043c80d00c0701000ba0b000c50781300d055039042c800484800100800d40305d41c0410311010136091802118001c2c4e0a00004c140320350280d0074043c101321508180d800c00036105400030560702100030102d44007551a55441d50031141203030b20440b001c3c0d039100e0300101e0a5020000c6580101a82c03054503034a80380080c0060001140e1920060500d6011082c1c010254603c400101405201c0e580c1000704607210001e0710b5118844000240d81172044201c4102000591022288141c4040d5411404c00d487c002c01c0c0006401c8040d581d40d0b4002881e00d020503580c0316280a80750840c0640d02e02c0d011035241540003814900c43e81d40541c100404442038200040d000000c407819101d55600c0c0c0c442a4070410f901202c14025508000e9211000050705005058400c42680014004440811840c030481d0440c0044030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 787515071 1250 787513821 787513849
    0x9070c05060c070302070513020a090b2109280605090c03070612020f1206040b09150d230601080705030a0f080a090306060f23010c0b1b030c18 63
    0x1a0089002601c10454003002d420f440f880390044803c55034581000500700086801c0104040303038042a031150f030a40c0085440000c0981c078101c186001c2084020103688801910042c4001440f030340841c1c100c40c01000f4520f503a03038810700e4981a0740140740e10100c0d2040016401d441041c00c0001140c0030300408034144901e410001d00a00d0f08a1034003105480d50340e590003821164542c00d020580c00d05035150010700341414000c65404c12031400c1800c01c4101c80300504800d0041403400d0030410794925082c4601c6c0a690101e4403010001c0891078520004078550f14408141c0441c80b104480d8a0400155107042c6d038201001d03110300075122014580d071000bc80402a0891003410520008a00140020310790400c1070b25081180540360344549055801540c02071441c101b07650307401c1200100041c807000110940c042c2404000f4018400246414084030002e004d101194010494090042c2442c0c080c06848601d9a45c80b490b00c4e40c4504016080752020000521030480b00c4080e51501d040700312115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 787516321 1250 787515071 787515073
    0xa2d0603060b04020c061801090b01060f02011b44040c0e060901121505070504060306050105070c090c051909050108071b03030e0f12091810030305030402270609070c05 74
    0x40d900c00b0440300109444401d187c000d5580c40c00c046010070750004006020b41a83c4e05d851500c2660b3341d00013070071980e80c50000c11817901a000101d03d502d074003401035425200041009178900b00308600403025021a10150400d420f01c8031171400c05d011814030707114401c9004000c0c01288540c0e62400400038182144ea180c1e000c4103e07401070000f19000b000c42240b8a010b901074110030404007035030f82c08803481900e00e4404190040b03810013807a68540140d402414084c604a8180f940c1566840051a8a4001c090440da00c940c620b0054500c22030558101c0a1165610f0800c4022408050646452402030b50300041080b000100464010fa140714498001500c61102421294800320002c22a1445100c92800b5004074120705010030420303681e00d043d40b14141d654450148041160810001c20144184506502000841808508841c01316605070404d01e5880d59544005005610361160030302800360f11039819500259098803140c03040f1020b8070f01190b15211003805852180c09004000e003070f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 787517571 1250 787516321 787516333
    0x300c0705100213091a0a092901050c150108070501030c051921020408070e06060406030b19090e0f0111091c02040507021f140a2d0603060b04020c 64
    0x107070101c1c5500402441c01d440a10002c042d0b281d20b0303014152100c00591840300c02c0542400171030740c600b0300301031401855045d1082106d0451404040b90340404982c1c1c4003001c004803910301b042640a641242c500844001c160781400c1540c80913040310650a0103209010310a01c2000720301940241b01d058a43d0f00076803100b5040c00c40d841454007000c10210a400b08000d4500c1d080c801090209072868410030f4070407805a211410140c0c005c1c81e2400c02c2d030045d012220302c1c1050000075264042268107480442c9804502400c0000204101c80d03c541d908040a8081c4e2500051000183c1d10812005e0b0081080e1034040030f9040069013030701d040c0304280d030301c80108200b03402403850b1007100500c3c3c01681c03040326445041f283d0000350403210200c0c0da03400580c2004e507004e00028644802e1542d520003c0d10100001da21814070f0400000e0010058014940d442d80021030360403200303c0092151100082042c160700c8400c4160003c1d0200d48000c440203400c2000c4082d0a151500075a0341c80d203d04001082 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 787518821 1250 787517571 787517593
    0xa060b0328060603020604080109060e1c0f110d0c02010810030804090c2601030b010b0309070b0f070210050a180b090103021b0a0614010b07050706050f300c0705 71
    0x42280c03200101242c042d9500c100000060300c0d01c0d03014000514140000151420f118245202034170a0031500d0242900500f03c003c400404142481501c030702a843c158480455410041c0c46d46540240194410310030719644c1482c00c0d0740800c003040018800c0c2d0306c603507660b202d4072410507801009002c0101034007014002032113400030710340c42036000500c249442d01034121340b00c0001881c3c100a2048030550a0200014420312051840d40d42c010011a0b1247e031031440c00e08180c5445201034000c1114440300050f0400c4404044425100840d4008114800107454200702034415800314640c9801309045507150910f0106105040d400c858401d030f02c892900302c5000045009520024a80140140342401e00c001e002c2c0030082c50700114420704001826031010341240304415030503482100d40510802c00807000410204025013103c0503420281e45a007299a05620305000d040390f02c0049001c000c0350103807100003154500001400c5020070b0489501c6036008140c4520900c40064403d901030400c00c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 787520071 1250 787518821 787518883
    0x61401081504060906030f050d0207030302030306040203270a030807030c21270b061509100905060a0305180123130602030903090405071b0228080a060b03 68
    0x4200040010400103c00340c4906008045901c9a003007900c2109940c40c0b942d081280801410b43d4183c00c900083ca421440c1d07a0700250f49120080c02c8600840c1c01202040304c4025914049020070200e2510b4400d0000581c45156510070810040d4000340c8401c010800b107502a1003130140344592682c034450704044012a0006e2410221045401c041e030b1349805075800c1200340c1d450b5880c1c1c4020f06004500d4090790500d40340d052000b6100c13034819829074418a030b16180840031078050034015907600b4031034095010141c071818041e6120a80100f0005040420b0700d915034000d0b4132440000c240107d0381c1a00d070320f0b141d08a851074501100b0003000140200d0800102c034507a954403404107140180c03121100c0da10542a40c00a5074102c4d595400464400e259242c503002d0f40b0391022003032420100d400c8465880206d441411440a8001e1170003030300e5080121100740340b901c0c0301001190f41110480c0c7d141013890341d50280c0c0d03000362411440d00e01001241e1401040302044241d15403018801800560691 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 787521321 1250 787520071 787520101
    0x21302220609170c091003030e040b0117040203070302060a0c0201091a030103080f0c030a0c1509080a0f0302070203010204030b01030b0a02030c040504180203150a0e071a07031106040809010306140108 88
    0x103d0454818844800b2440e912201c9440c85034003900765a1031214a5880d0240282c0c82a5030124800c50400c00840b0590b64040b02903280c240540c05842150384450001c2418000301da08081d400444c00548081040c0c2c020404000385131007a1313100da80740c5954101d41d0b03c2d0000300c5c40420211000400041002c954001c0c050140454100c41c1c040c40d02042c0600c0307d2940c0e00c0000f81d80041440c2001700e50a01500c0b4054260305200800705101d03110844ea0f41e0403481c820000410701384107600f4410b58500d84213605031541154040c000f19683c0751641007141000200b4401142c404451100145002c00b0038001c4d00d000e54250201c40d07041c94141020080584689001c0c080050325084050340961b50800924401c4107002d5211003c9052500350041641d03500403a50f00b0560241000708020b005c070001850401c080301100644400c49031a0403283c04610f40320401403441094140300034041204010103425000741c03010821380355510400c81c000c1c3e5100c0613040c0032030950350010b07103071810803282 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 787522571 1250 787521321 787521359
    0xd0809070f0f1508100303080709120506100503030c0a020d0213020319060603020930060708010837060f020c0f250b0f07021302220609 60
    0x40d105019103031100c0c200c0c4a032082d48400c0c1e028198200400590782da2820f1204180c015142c4502280b4203084039103400c00541c400101004034440c0082c103418815a0003101a14207403150181c00c9940e030400d955110803e607552113202040a100041e03d02c0d0001c1180d00c100007840c00781129051980801022400c03d8600780e801281918101c0803441103031000351711429480c9044081181a001030004a5042c2d41005050500c10080c6419595a100d0110211005a0b00d0540b0740c403103000380a0010000c00607290454031442c800c0c4040140c200ca071080c1640c441000711015094100051020842000c000001001280340301c1525410103404140626018a2001c1041e60000309454100d80c440c15641800d030700322115901c8000700510101c001500c5040403040f1040b01c2059200755000a88035891039060006801c0b8007840c1948140c40b039040e0010185560300c00503200e220041c0d40b1401c0780c2c0d404600c07908810340755480880310201c2502d103d6603500c414107050400c01400307003c070100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 787523821 1250 787522571 787522573
    0x5100c111005011a090f09090a0302010b030c01170c090415060e06070816050c27060a0e2419050f03010c0503060f18010824091f0f1d1006080d0809 65
    0x85081300b65118142828043c0034020001e02004270325040007400c441b0303101c45640c8660000044150b240c1c0e0b100d1a0f1004041c0321020742d220f2a140e44500c140c140c40340d41d004035081800c1400560102035800540c0c2c08849058917101c007940203410810000b442038100040150005103c850440f07114540d040d0443c91240086407101c03030030600010710100300401014002080048405502c240c0010b40980003541540e6101a450820306040010300d4014181a14070445010b1032101d11070614030910040d2000c3d1184940d008108100e5540f00f11600030340340035040074000324056003030521801a84200558a850031511030504002d2842c040006403544000c414180c0c4d8621652084020300811210f801400041d8034642c010002d404071805040042c000740b4104200144041108480780c880c546a040515084012800080c140e01a50301700961402040c0454102c0308105041b24019802c11284001c100060440540b0024005c0707825a4102c0320303100407258014074916802840f584 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 787525071 1250 787523821 787523839
    0x1090b18040914120f1603090f33020706081302060d0f1d120904090602162319020604080d08100e04120c05100c111005011a09 56
    0x4000505480c100c2c1020790708109007058408120300108030b0400c038003a03500107031401d1204100b150245401942c09610b002d403030b41d0600d00c0415215480002c060440c284220721a191a00310445592a000c0e1a0a802d0131010100047d079041c0b415200c1c2e0011202c7d40140f580c2c40c14010211340362a00540394040c01e4a080700700d0030060740d580d00a4071403206a107400141090341440300405490201140d6850880d10041400c01980e01003000001c50340c6410115566007110b03004070b0000d03c1c0d6924041c1c00d803840429452070985c001a48440b14500504d070740742d0b00c0450040b0301000350020034031a1a1941c051007100e0100d041e905410822940000d14642c1000d956601050420744881e1031030340083c0140041201d110051300c407050141ca484a0380d14140c2c5003559520180540600700d035400c0c04901080380c4100f080401500f14a141e2602c014080c0c07249461025203600300d244001074141c0206003204400d401d4070701c03d4a040703030341c8108a43c0044000800781c03082940240c0340c180d0011102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 787526321 1250 787525071 787525117
    0x90d15020409020a12110708070f02060909071d040501061d04060312021f050c030c0d0f1d01060b0306030703120201020f040e01080f07240c0c1d130201090b 69
    0x5032015151080d5036442d600e2003010b00c0341d01e03003040300c8943d046d034015001d050000c000401c0303401050315416984800c4244044255000180c1c1502800c00041e0348a154081000780b0b083d8400100c0c04d0716072021044d03400c00d0014000304410f5440c24002c050001d414051040c0958266440b81880200060400510181c4a48030141e8541051503403a000d640000100b0140710301c4910782400da609101000c001508112501e001395210260035494090030224401031040310f1b80d40640f6000b010680f081043d03664055800a4070289803264082c3d0303502c1c00d0300005071644d041c0c044078410003004010f4000b00d8250344d50b5450fa0038208528008665007030050070301c0c500d40e442c010f0001c1c0c000040003066070740c940b0780598030f002c00110b10030a0540100100300300c2c0c4403402c02c044801c010104241c01462038070b05c00482e50003001a101070007442c44000002448000390200703442540d4642200799080e9a0348154280206000d50001c0c00946610010000703c280c2d40090040c0850a5400d03446108203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 787527571 1250 787526321 787526339
    0x120b06070f0501020306100207140108071b0b0a0c230f070b10030c1d0f22080d0b0d241103040c090f1802040b040626010c05090d150204 60
    0x82040854480c4e50000610800d4900454284da007111617200506403030703007400000501c0e401088420b9041c80100001328a034203020703c0c0c180c000403815290354140f0000c18102519503002c162080d0040c0e900e0062a201c946110b960b4251050900310210300071180d00e8003048030140d10003011980500c3c410320070900000c681103822800b412038140318403042ea066061424444001e80d02c054102e26000d00ca0b140d40050984c40981c1c88040c1c04409120b50b03546056103100408109160310318504d504042c8003c014401010b0000080403810801c001114032040c000d45000c4060043c3c18000799001c06940b41441d4080d200551105070008070300701e041d206060502d908151011281d40741c20500501c141c00396031045034050720b00d041081c030405120101d400c4e25680f603200060f0055464030301d1007080d516680c0003000202070713134103103900390188025901161500000c8100040d500b402d8404010710b10038815954200b80040064140e01910380d503545440d42c41c00191203030385400307000014074000c2c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 787528821 1250 787527571 787527593
    0x819170d09151a04110418060f09090503030103110105091f1112040501050d061a120604090b07050c070b19081311062104060e0d0807120b0607 63
    0xc6240404a4041c0c002c0c50700d0701c000070300c1c040115000761a0018040301c0742140e04038290850016200043c2c3d1070421401812135104a810203402e00f00c031040145100d0005502070b40403100308118285e845619144880150b85008401614640c418030050001c0ba01684246842c1201410140e1404c1c43ca68082036010310000610102a940d400908030b0454004158150302102c08018203800d54400408030a0381c05540159030400c0380218007020090b00a6210001911002c00280d041c03464210044c4103da01c010405100850360402003055070810f802001e40d510360100c0c200b0042c3e83c2d00b0004a80303c5d00100000305852185400001e111441403008081c01c4aa801d02d510000b0031700100074113070600113801c110020074a0701c090401708551400d8201078200c03c40d10b0680d60308121614040c120311103604400c802000c0400d00c000c1000b10352210600c401d001058800200c9100002c3e1107040702120060041105003a00c1460408035502162000c64020403050030200c0c40d80b01c0c003194507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 787530071 1250 787528821 787528837
    0x91511010c030f0b03060105010801060c02030a0b0a02030106020d0306030c030f08070c03122604060504051f0609061517060d050102191e02030d2d09020f0a081917 72
    0x2070340c40000100f003140c2801900760105059000305440c1d494140001c162010510072007042002031040103085503002c0c0441c03c0d0b01c0d074007c14801d685080451262001354000e00c600d60242c0714249139007544174000e018807070440c2c0e0070445280015140d502e0301001504009c00480340a80c3c10400f42c0000380c1040c104401440c010143e50341c4101103040f0140180034603428207840003454000c40304038440341000842d403050340440003051300c0d100d03450a245803003c1c1e270a0391f0720000074000d103900301c2c0209544888211000140c0a0189560350a001d68045a1425070800014042103001005088945206401000291064200711543d40b00c1c03a0072a0006802ca280603140c41005441031a8000c05006100700c031102040c08408200030042d54911820b8460022141c0b5030075411019050004901e0a403090069109441c0300d0701e1032404000d0204400492060550010000550074029200d40a0f148110b004100f84264104121004100540c0440d0100816801148140c032010080d00000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 787531321 1250 787530071 787530077
    0xf0709051e150f1615020702060f180307060216060e0618030c330301060512100f06080a060609080c0603092d010507140a030c02070b13061b0201091511010c 69
    0x107096245041c0706800d1040c500140006d00511a50b405a5104d50483e20300890054a00d41e17501c47c001800850711281494159144c05808800207540e03402060484000c1c2c505035507036802d03c0e03d482c001c2c0c400c4122004150740102040c841500420728807680c11403003160040c21a0440c0011000158500840080c440458011402d0150818040446000c1580044401c1605546c1482c400a149014024911191041c2d400100c2d100f6040005404040e090052001c039006032100d40140100360305941c610506407414070b0002d502446030078040c0c03e88680e000604141c50038030003004520f0308003500300d070010700a1450651200d45002c000c1d0700d01e440740e04484c242c0d81da10407104908441000f03007000300380010310100e445182000310845182c02c00e03d05000a00a680c2e4904038a4440c150700000c10045c0300280010032420710b494250704641269407504000c8240c092003060100d01404003c0c0030407a007000910401c00c0d04000c80c2428840c610309000c00ca01400701950a50360801070070008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 787532571 1250 787531321 787531357
    0xf051308072109080123070c0611070b060915010e10030204050d060c11160e07020c0405090601140109050904080906190504030309060c1203050c070501050f0709051e150f 75
    0x421300c000e004a1410b000302d051003029042901030880340e1024014020701c01c011992544804001a5030302424044c4aa88070795501c0d201c8910f001c50841009031180380c810340d480000500c100500c084500002c0c64103a4408450590620500c4424102d04a14005164090201081c10b072074058000003198003c40e008105c401c80c1120103800c4418a10000905402c410300103500048229144400c4804a0400f002c40e591031110807401c100a800b20035500900f0282440f880030b0000a40a060745d10304e0035185000c80140707005540b201402c0c4142c64103d9140d100050118402030301911a28402410341032400220300360a0140625418000001c940041001c1c0b0a0651065803d80a44558140620020a00e440d42904c4125040605003095203500000311690307514425140940e603c1030084c4058104100010703840c007801c90354000010114040010355161020030f86000c09084204030b02d0700094001402080000000c010341805010042d01001c002110001e043d541000041f5030300b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 787533821 1250 787532571 787532579
    0x30301090518060106050703050c0303070c0b090705030a020913050a060515011b021002011e02090f01020607050a11070314010e2a04020706150e01090f051308072109 73
    0x845501070000008000b80422696410784005001d6040d0740c1d060a180fa2240b1051904689611528407901403078000071090016030f07600b21000d560844c3c40348489409a0b60342508140c0c0d107407070900c40c15900d5408003501401500304103c2031744c0c0100c04c5001c10501c0f140f0a865962521980600442c2c803555507400304824411080d0804000301e20901c0c01011240407a50820413140e5084d1020f8446c0d40c0b1800728072007a9000b50b01040900301d000d070520400094003c1924000c3d000312700900e020390000049030300d440d031011981d14880c9043d83c4400c0d08001d1170400803100c84040540c5400584203202c4040702003510b540480c0356100303200300049810071580303810905004e03c40c2c040f0543e001440c3e5020b0284d540144e04102da8610681d001a101c201d1414481c002d081c0200910311125106d103004918040000f42d83c605a0340451030600400000d0032034070007100c0b4101c0c0c4482c001c0030200706040008021000404240d4001c1e0742240c0c941c65002c01c8240710b40001d031031480203d0100d4000f00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 787535071 1250 787533821 787533839
    0xd0507020f150103020609061809100509011e0b0c120708030a15030321110a0e010807090503122110060905030a0b13141207020a08031c051305010e030301 68
    0x440851944505030b481d4515804030b240c0d406600030f490f115401c04207264403070b41c0006141320103103d0020514442414000c8007405010043d0090318000c0010740c0000c20512107007620f03141d10b803031b4102084906c5490704404160729000082955014025142c00e0030b427a2103030802a203000c500581103207603a42402170710282141c50790302d540302800d103c5407000c10200780c022200c510000f03015000e080c00e4801c2ca202800060018400e40c449541010555201660b0f00c0301000809042c281c0321a40c2c41c0c4c0350703604261800c0003c0c3c0324840d413640c05000651b12500c034200107424009240e108949122540d28805981500205d804140c0d4400c00d00c8100103e07a0312144c50001401305402034244018541c81c3e42404010042240c02c01c4045080441c040003030842150f05200c91000640340000480300101340b0740c1e1300221003a8030030350036404c01080d19500841280c2d00c190040c1340301c150320070410340340b03001401004064030000c400e04143c101c0440c50070700942d1582c43d0781601440e0340b98180781c024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 787536321 1250 787535071 787535083
    0x8030f0904062301030b0f032a031b04020906120f060a3f1421210403120c050301170705010c0803101a2a030702060c030d0507020f 58
    0x543c0181a102d101204203c800184190030b50028030380414041420004210804444010140c040c07184414803d400030344441040018100c2481d4a20480c40b4038003059902c28a8803000344400140340284011840c0c180d00500d0f030002d02521040c113088044204080302c60b000ca8201d507840740d00308100003e6250803c0a030b406001d219504541016840d080c82c43e24004400c11a0301c114040100c00740504488154400001e074081260080700d203500c0145512030345012b02900c121403001502d02ca9024424003590090341403803400c00310b07041c210114000d14410141045c0c040c00080080c5a0400302a030140300800a01900c03101d0f603035403525207462042e07148032188075610b0304081c1c0c1c18020f0ba0303484003850941c15089400d558494035503841710140c03d641075100072a40381c10081c4140c100400140649403442d40004072403c2d41348000c50800f11403804280145040d0400c01c542c400610700103000d01400c102c030000300c030705081006270800102c3d0341c1a55013401582c400194100110010440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 787537571 1250 787536321 787536329
    0x9091211010612020d0807020301020708040e0c03040b0a021c15140604051815040c08040311070305120a030605040204080109170a0906030c050c0718060e0f0105040b0a08030f090406 80
    0x8010340352030300c440280d038943c200718000d00c81d8004070310a0050000380302c1500ca4468004000715541d9100c1c6c50405041e60240c410319006031445400a0b00c1407051805491140350018406401da41da60308aa100a50002400380600c1e03d40d2114145440806d126048000c0102400081c3c56800c2442c0c0702900031020701d03e10b2160a0400080c402511505d119280d030300210507960a903a22684605400d40b0020b2800c160020f00e46001901e0b010780c0304203028004e40c0a03854014112a0085000352100c05d140400351069102c004074441d6013900100508800300d5518000842c1622000082c0590340700e42d0040070682e440b002c1040500c5840700c1040030000010740d41900c1d01134000c002a1001710b07540305403020315943d415034044490059045464204806c416954000d4441084401500340c0060b100c0c0f000e40780c03038070106001d41010f11050260707102800b48241a86031a040002900301e520700c5640010954000041440c41007025094000c00300714825100d0704214180021110300d640 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 787538821 1250 787537571 787537573
    0x1407060210020c0304051903060e0102121f1e030803010f05030c100c0201030506060c0307061d0c0306040209070309150c02010c0906050306090411030307030203030916030305031f09091211 83
    0xa950010b03e002044804854081e04d8050849000313812680d040c884070b62000c3d054070704000d02915000410344c000c04200e2000d5103008455180c00c4480c0010280030103090788401081c9070284070507010700d08100e0100c0d03101c811210a01c3d4680d81d0300c0a064000380d00032002240010400d10aa00d000d000f000300c1c404c4259554010021640d6004141c0c80a03050003905055544005c225561030395812114114084070031031b60380e04460300d050070061607850303810084003080c003104d8403080901041400050340014000c149684482c1c0802581643c00381040307040c036a85201c11000101c510841d01203541c00d401c400541700080407030190940d0716240c5ea0b44e08210b0512420710080780c00405482d08940f007038039894025910383c5000c46d0114189984560b06110220706982055800002140725808180030f4071086080c4400c1d21201c01140c1c000240425005c0c00051142080380ca00341c80300d07030601b800e11844d43d56944042012103c8410f02580c004400310700034260743e43c104241428803030203c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 787540071 1250 787538821 787538827
    0x609100e0405090c060409050703020706180c0e090718181a090a030f0f020a0b0c04181a0d0f0c0308120906160c15050709080d1106130f140706021002 66
    0xf0f00003641e58480c90047c101102c2e524030100c1d8480b440b1354141e82e40350b94090320400030340d21a920b46030b050280e0703094200e0707100c81103100204d020780060684034003620b00d040042c0f11440c14649101d4103001601c840303d100307503030b1680107034441600c0a070040d800500607014911a14110381034003408a50040c8582040d50090101314002903102844006030341043c640141200b07000c4004900341010b22101500c565441d5042c4100022444001e004071000b65042841d10718500c503100341a10350107815224144c03004c1c030100030302d0300344001981055840740c45580824225070752290411511790300240d4030318801040425202903007524072030f0059045c100030010b43c0340c1940c3d00701036054002002c508000401264508002c0e22809070580c2c05a2541d05118503d06540020f0101c1464405c7d9042d9210303034092016103d0103801e5040304404c02801800f4aa5500c842c007040790103136030000703e07586030040003000007190319512201030b5908940c0c040d0407241d1500030b0081c42c00c03180b0020110024410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 787541321 1250 787540071 787540093
    0xe030d02091c120906080403080106081905010e070e010c02031b0604090e0106030204180c27061502070e0708010603091e051c1b02040903140f1e270609100e040509 72
    0x4446044a00514045405039203371060401b07211152421007540b2400e02d4008030302c40714012821445448540c0e41d1030b11352541040115008051104040d416800910b80c9410380714003800040504030024118501d010365884405086603040b00711490565076807541801103103400e00403107280d80c41d98550080d080d4201e8498411034485481070040411018403541d0700f0000b124000c00002962240801c03ca030707a00c10111001da000310022000600840c0c0700861300c00c007105180f5000d40c08035a51000c4aa080a006034018059188142c4201e280e406004c8201107004001c59441b034420070180c18a4550100011100c0350740b2001e003c24031040700d80c00500f150300b5104c1084215011940800e41c43c0306403c041d20b10740c0c4a1440e4081c00f800c00036540f0f0304009260010030082502c1c1c3d203100c9250001598201e2207014959990b1003e1102d4410110540f154500c0180300c210f000b0701c1c00346000da000300001d1440b12026040d5001c6205000358030301c1807601c0d11507a6846261039000c0e02d01c19001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 787542571 1250 787541321 787541327
    0x3010b0d050d1d040614030606010302120a110d0c02010213080607020c040b0d0b070c054b030a0905040501090504020607030c0c0312080a0b040e030d02091c120906080403 75
    0x980140c10108002420f400d48004205044484141000341c010400c6035200c8082004a21020400768002d10909012683d9544139200303e034003002c1c26040410450700e4030071006018080601c0c09080c00725052040b035034250030501c00c0030340c20740d155000142d82c0d9040504440e10080799501000140d00050200718650f500403c80c101c04800440f0300080c2040841c0018403006100300003c1c00101810003000001504400d103450103d024000302d03045814108542019450803050140b480541150000708540070bc140390b0146154444d5242d0010140381d0030940381d60800ea101070005840c40f0001c03c520b00301440b0301c0d40500500041441039192503004142184101400102000707220200f007400e10a030103040c400a9644141c294462808450004101c0c00040c2c840a0116103016070600152034a0f1181c041d04402d00b00195003040c8035070b000c41e4025040109503a410080110001442d03403e0321040006c0144107994290703075040b010600a01d0401035800500a0100400501000c250 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 787543821 1250 787542571 787542583
    0x150709150e010206012d06030b150304120c030c0b0a020a030609061202300307030e01080405060f1b1b160320010c20030d09030b0114012304030203010b0d05 69
    0x22081c0c40165070003000c400c980d00c1ca1b5040c00c8848031943c000f002d0108907150b05420450108904503003455038140381e4042c0f5070b4a440103480080407080d2000c3c0c004042406081c2d40c2003400d0007410200943c0d1000d881d00d040c60182185e1141c1c4680e40042c0ba444240d81600c1030801922307080c0301c104406403c1110013000c02010301006445840ea00f400f8040090800340d00c018541582d20801e9100840c0a03805507880c0c101c4501280400c080c81c4003240b40307520a02e85039100709c2d0403030003c01c07503911664030b0781c0381e450005041403803810741415901b2100e040c0c4400400404c4e5409182890400c0280781c106d041c0b03800c25031990068440e4080030008140501046044450b540101c103803010843d40c0140c800d4810b40c0c200034030021120706084869009915240c10010096080d1000b041c4103040071200b45070a400000c24088001c0014130202c1002108441d012030181812100031500c2a0782248203008200003141e84480003800703008606081c0111508184141e90b500c19000c500d5840d1511a1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 787545071 1250 787543821 787543829
    0x7110a0602071a072301021815031f051e13200f0d050c030f07030b030a11270406061a0d0b0307170a0b1b030612150709150e01020601 59
    0x202c080b58100905c505180a032103429280c101c6440c401138940c044034042c1d040b0514a052480500d80c00c110b0604203a07104c0b1240c244c980804170703e195914031364903d01c641c00e00300d01039139040c0d4030f0380100f1191940d090301a40c510070312101c140f815100c4400c00811410707018600f00d82074213185400d001d403001c000e0030780c107100c20000340981c0b10078114940000302d000d21148120b2144c1480103000c0d803410080d0085008001144102070f1560300c04200fa410390329030243c1c0c990160b11281580380810069000344468950003401c0c6071101c8040001c194007140b50104212000c40620144130800481d032244034000c05a00300e0281240f580800a120b490007000d0f072105000b503d401d00222240d0f41030110001a11410003190381ca420100182641d4900c490340403a03d9591500c00704055961408642590f95800e0b10424a0340d55010140b2583c00203c1074090a44d1240c040d040700c20074104407070750740304148a5544e00162031800a140d0503c030b100e000c0c0c01e002e0080005501c141c0741d03400700d4114107503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 787546321 1250 787545071 787545119
    0x406020712052103091606020601181d06091b03030d05071709010b010e01030b0607080705070801090f120c030210020a0e0d1203050f01120b15030307110a060207 71
    0x400382070802c1c0782084503020343c4028403441540c00314003602c0400003450003401c1500440700b00b00c410701800000025580203a00142c0e00039001001503086c4008208540343d040280414100c40d5201c02d923412050100d0401030300d40003e82042080103040103094841c3c00326121a0030700c40c10000c0440d03180d1050801203400e9079250303070000c0d0502d40145043e07800204c101d035126100749004052a40240481c01c04280002e0791015402155031007801000c01d0620000c0c1028688051640c41d20860343c0704900807107460294400002c0c28910038414040f48600500340c0003190005031400910590300c0a50900601100d800301c0d4011030b50018051b0f1031041c80000043c0d4034099400141c0d8841010f8032084e50041d610201802003142e18000c05007034402680741404140c4030300284182c0345d58240542c4209648001004001c1003881c25100d80103049071860b00706621907500480c1c119031000d00242c0f603450856100e140c145c01c00c01540300003072941e031000d8042a41402000701c00c2c5400240b00b00c0b90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 787547571 1250 787546321 787546349
    0x1409040b060d020d0210210204050120070305030406030905010506040e06180c1306030c050a030f03050304060617010e2a1e0d032001090c0603050a0e01020406020703140304060207 79
    0x1c5440b041c0c1d413901c081e90010041981e030b015805004084088030341a07005041c3c0400c1c28165a41100d00964059a205854420302d885106200784601180010004402d1082840c0000804c40070310081029200582c0d0201c1d0340042ea040c40d6094840150800303020346d1a102200a2003540821000c3d0480c01d201e4403038046018100300d551401401c0c11185600140700385140d0900319043c3e00070000c40740300714219800a1b90f10020055800007510018040c410303030828940000b0300c107000441e070040c42544006100c0b1340343c04143c138010362500b40c881c4542c1c1d540c4a400803040000c1202400d41c0d491907000400d6060711509002c002c040802c03079180102031503200941c44090b00c1380d030603140600c0a03100e10544101c42c14010304000e11407801c0091800d080b405040a540180260507200b900410880715180c5030400c200c0040c070b4010924040035a40310f94a10040740d081c0002d10003403415600030100a400e42c14083c507030783d14400c5403030b405500c100b208002046d00803800c00200d405048000340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 787548821 1250 787547571 787547573
    0xf0903010e010509030903070801090b0c0a050f1603021506011e0c0611070209010605070b07120f0e10060506030f06040c21060303090905040b01170c0310061409040b060d 75
    0x301605071803140d400c2650030803081126402c0c0000140210b1541241292001a6150130090803140b690b04050940d1100e031000500c00c4180710001d0035418024a032451070301004c0d941f000c000d5009105400f0b04001020b0b203403403e2541c10480b503048603c3c12118810103040800000c0c01c070101c0b11420782e504c403591035151107025000304a0001d0b4150848401d200104905411500302d40c02200200d110303403003c00c008100c1c98410002e41e05500da110a10032850380300c2d0201511103004a21010303144540b04c00403081a50124010000c1200d000700041080f201c0c0384090b030090f03d10302d8001a010718024810800b619440001c241c0d000360081c4c0d0001800d01340608100c94050b040c50038001002903d003802d074034030451035200e0b1044034041d03590006001d0f112105c110940c0d2042d2400323400740d4000001032003140d420801c031044010f00142180e10002000010031b0410030540c481e030422581e80c00d000c10001d41c8080f0688002c810464105050386407580d9a800651400780c00d0900400c140c0d00810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 787550071 1250 787548821 787548823
    0xb010c0804031103010c0807020a060504020f181b0f070f02210307120f0503061504180209090612060f1023040b0a050d0f0c030b07080901060b0f0f0903 67
    0x415164004880c0380e907564903810403500b11281c880a4501a603c2c000440d0200c621030040903004915640c080c141745066911480d01a100152069034170141c0f00a005000713651315040801007030813401c3c1000092802c00504e40352204520300349218a176007006101584401c000032206140c0d4131170b40c0364031101c1c10780c00031a0030850325449406829000b51a810207a50700000a008814420304188010000c2e2030b00450b0852201e4a1a4001c5101400410240c2c6030540594190f211248001c5003003d03592868817660220111081c502c4550002e0140c8030780c100a40000e50000e01035070892084c510002c1d481d56600001030100c07a49404440114010b070400c0c0c03451000524001c900d044042d1454088000c900e564698414402c500d81810005241000b1030600201c0700c0040c846d04c045015a101c8000441c0282c00865a600c20a0360201c0090715050020340201c4042d901c074a1145044414142150010b0b002106900070910224440b0544882255a4085403c0c0c60988420440d400b007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 787551321 1250 787550071 787550087
    0x70e030309011202091c20090a050a0b040c0306050102010b03211e040e0a230c07030203070203010203100f0f0f05060a0203130306051e01030b04110102030712020717031c0b01 77
    0x100d500c51422600032410046006d11074408034003d2500315044601110b80702e184c1054940d1080d084a04030001a10b03a4905a208035401100c43d134000c84c4901c0c2440c00078007181c5510012a021035075900e0309201550382481820013120041e0014100a02400a00c8800400d803c80303007858000300184820800ca05291f00850f4803240b10242520313507803260359210082c4011190240c01da49004482d469200b043c41911aa0061240004030700741c0714034203800b2281d40611720640070740c0710401141c00162000d00c02140300d0341546080000041c280101080165003a84c04454900e58080050204001c01c0001c002142e000700c0f46d5956683c60b6010690640c0503001d041038a0b040c1e202000010300080d500238034404c40c00c0380d22261142032a1040e81c4454142800050151079031000058009003080d103d6a0118005004036824040300d90b55100d6034101010080005030004131301008581c24103007003000d201c0f0700e1901070742c00c0251610051007603002e44100321062503202d00b030000d5940d0154103c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 787552571 1250 787551321 787551337
    0x10b1c0b060d020a094e080309071a0a08130507120c170c01120c170a090203030a020a02090c0c0c01080414030c072603030403033c05070e030309011202 67
    0x440b0300c00f1b0440554031040d01040c00e030108011b00c0005a0103003005210070f848888280048a081005da041c1d8541207410b4000400f00e500f10301c80c03014049a19210420340710100b5054508841c7e4030300170f035031004088180190460310000504c0c10707800d0001d0ac020818074141c400300b4000182890090801482c44005503000300541c03802490f6910302442c0214950190182c01e0b04c030540b00c3c43c2254440c40480c3c1c0307815030041c001000e4007000c0035656a600c40c0700c1d4010841120200722880c1540000e41583d0240000c040564001c1401c001182040d04440780d11054101c551402c00c0680d42c401a01d41c102203243c2410004207600007410000120614480c1d1800381d400c4a131106245281d655440390603004c0c06041098102b0b01c40d07603407052410310740c19100481e8095030460301c0790b6505070050903031080094607407010014040d1840d40204002c03610859034514070080d4900540d941400c8501c0030340302070b04101d0300580072080da80300001200c00f000c0c803e10f4044501c544050661001f80500c1e20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 787553821 1250 787552571 787552589
    0x31003060c140c0c01021b0a0303031d0d051305040203010b040339080f010203040c1a0904180201120605030616051306020601061d010207060c1109010b1c0b060d020a09 74
    0x40c204000701001804d080c9100303081e000c81d5968103d02e54500724031402003020960002e03503a0411700c0040c6c0700b0780085000e100200c10904408030f034405a00c1c1050340c486038000018202050400c5000307501090030000b000142c50840c40d6504206448900f803103035020191403020751620b44400140d00b080420b507400c44070000000f281040e0b040e8203001486a1083d00d220341f00b460036940e24a103040c4201e90049901c4441d54980c3ca14021008140c6803005480510864044c0854059a05c40c5c0c000c00e01e9511403480c0c0c00310308540300c2c1300141005040440c0480d40602e00310782440540c80000d80c207500640518140c0b16540c218070b41c1202d1a01c00c00450140401c020100020a0b0b900090b806040e83c645480c0c00106512094184040c144001169801640300e4981040460700601d0341c414000c1c024400030f01005156004039a810390300781d11008124000107138003e607685141d44c01d0303600000c00d09000c0c46600400c20000e4454002c844801c1c0c000f070740c00180e040c0e10900400600005004c3c002c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 787555071 1250 787553821 787553827
    0xa02040e01020c0c0f06030723070506100b0c0c1507080d06030204050f25030e030c0a02030c03011104210510020c0706080c0a120213030c1406031003060c14 69
    0x100c00366010350404800d150142c4100142d5443c2840c141c1c000e06600080a0085030071565900c40440c0d0b2042c228100d0715080303209031101240f8914004c000c00525010348020101424240ca0404442d19190f001520100c0180b0000900d4440840c414031121030887d03480000f05503201c0b00030110322035400010540c040014104d003000502e03400c02412203000f100c080000d0b0380e5800c2950442c072401c4a107005003602c9081c082503074815203c5a00f484400a01e0009604100000180c1c6194800a09049680c0c4004800000c41c84c0800125603082800c1d0020304c0035001c40c1c10505464062809401407e40c0c80341c40c024034038000c00f400d840c04607400c0011600070800c008080f10081d0302804121005015910010171254001c03030b0014002e95002e1680d42c500003c07404c2c03c80e0610031180080141d55003c100c00e04602d01d0460454014501910300d402c0c14030318120718070402881d86c80301c084c010041030041002012803024240d040ba500403402062200c0031340000c0356054012103403201094408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 787556321 1250 787555071 787555091
    0x809100f0f0501050d02130e0a140c0907180509090c1f0816091e030203160f080f2a0d0804090507090b0307050a0e0607050a0b010f050d030f020a0204 66
    0x350704181c11110303072140c040000d030341c0700d82c20310202040183c2d0284d0401c0400203840d0003138840344e102400030540803003500c180031000c0d40c9103540310066090380c01007580144140c0d400c41c03410498040d00010035082844540d5203400810700002464480c15100e40503503030003d44081c0c4148404101e000004103400f8020007070103c00860300d101640c0c0f007000628420001101d0840c8907814021002c81922481c500c1807800458088800c4030302c0c1440c03400c0e000c101d4000300503103040040209442d4024074240241d8203140e10003e1501e2594800140c42e071024200d07040c11140440d5604524903807070200c00c40c4a080326000741c1c01c1c80e21100710603041003411021100380004030010344240c0d402c2c0c80d0140b0458490384000c4400c08910b00a851040b00c1c10808603003814094802042114003904107542c840c207103a40016184d412491090300c40d034004c52001c0c0200312401144c83c2c0904101c090034071049044c00089071101c0d001c010000c0078000128813a4124500030402100810780c000d10038440360280b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 787557571 1250 787556321 787556351
    0x5071e0e040506010e0702030406080f0402040b0d0c140307030b160203040f0f09060603021c150f2309041e08040909051605011704060b010903080a021c0c12080910 72
    0x109210b0705c800c8840d00f201041d005440030040700c04a40301c0d80c0e140141c6413641c0d00c640d411950301030301c204c1e40030f9501e46810402d910b4640180b125140070304000c0c4500c1e45131a0022030a1f8843c0f48403148030f9085000207100061003813444541000c119800f0070000910444160719600c02d0341c0140c2002981440f00040303403c604840344c82a510800710070702203660f43d52802d5041c2e0060f40610200740c00c01c8914200c500380790f82e1120030030144007148040c0c401d0361b9511013030790810750390064515079100d85100301044108a189601e620802c0e00d24001a00c0c0130b40fa8847c4207044805005091504201c200c03040c002040e003500c000e0132903102d08000e40b0b852450650b554907107110039041c0940701118001007035030180713881d007101c001c05c0c00f2503643e156120b503142c4004091544404e4140196400040081500c01015200c543c609070018081401c80c0f50030041c0d0310b88026010b07401c000804502c0c0000401785080e501d140405c5081a40f00c544400c583e030f5081c845a400400e45076850001c440d0718011b5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 787558821 1250 787557571 787557583
    0x150e0402010e121f0609020c060414070501120b270612010605030307060b0a080618072103050310031b061d2101140c121305071e0e0405 60
    0x2100b621008160b05a800c14003241c40c001d001600540c2d042405890306110a11066180d2807100c43c000107645526503001d40101c0c1c01c40390304152283e1021080002300a46084c142030078240c0900280141480c0c000000c0420394084000d1901949a969540301500c2e1007201c0c07501106070082c020700f80e100c101007400240200300c030940c0c4140c010141c6050040700611842c0240d450290245241410f151142c83c042c0403c14842c5802080076400003502c007405102c514068641002858071400403501c2d0300b403410b15160800b502c1d01890011802c03190100c141480801c0d517150400548a54403100319030600d025650028001c10182c1c07400d200600d51484206013560201d0720745001c048442d00f0070b82c0b0360030f2034200c6580c1c11004c43c0100404803655142040710810030103001051091403505181c00d440c009a4600c10351078404035004030040c2c41c0a032480c0e4007135000b004a21184299458462b45d51040744035280c1001400b48000c5040c140d040c54480160558010962907414580340440d581c074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 787560071 1250 787558821 787558823
    0xb060a140d0507031a181b071208010810060b03040f0807051e0d1803140f0318040608031303021e0d0b04020103060b03010324020403050d080f0730150e04 68
    0x1600c0d03950900d0b106c4c6002c0d9400b071880416001c0100103680c0740e03801020400c10300c0d00d21003e802000e010900c0007990411f142c1007180d200e540d414032294541100f4624125000b10010310042c1014014004840b8640035a54031642142018085042a082040d060b02c220780014103036000b40c540d00c0980d500000686000d410001089a0311511658000c481c940c4000300d1180036041d2290081012400e012104160170341c062007601d50500c1010130991543d480481d5005140707000305071020031458548075480041c15041c01641c986840b1109020102e030303003804001d101e5041169030700408144000c0740207514a0140c40340840320410305020345001d101b01c500300d00180c02d150001c140c41078a50180ca0407a42d0114103003c6107a0f9410815100030b010b0303003000500542c00d1000201103171040000700c0411110361200241400d000562000704080103086a091001803890490410002081c61009886c50b80302c960141c0072500710b0b0005050190b00c0e010344034040b001d01040565000380d1290080d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 787561321 1250 787560071 787560101
    0xc09040e03071b1502100b0328050105160206040f080f130f05040c0c060f0b06040b070302150c16021c150c02011401030219030b0a06050102100b060a140d050703 71
    0x80d43d076104c420b910340b402c1034228401a006041c042119030318a4100545259000307090314080b581d07920300c8040c010000400314038030640384043d00090207400e104581c0c005800c600c1903100003018200103075071a1800340008004006420a0100380107096003a961450305904410399501c45840c04000c140701680214158035107040720001d020701d001e104401280040c0d0b1605c3c000b59000d0344071a40184200c550040c24141c468454405546e04c9000030005452012a10380d02d40030381d800c0003450108001c4c40c103102c0c000e400e4144881c44000074151081c41030044181099904c86201007641c3d0301c942d860702043d180d200c10850080200310030000c1044c0f44000e4041022603085c1000f2801d9611080c501e00091600c1801400541040301c0303000c1d060a050000c5001956a90742c07103000c5c0f034078202d540320768255580c4814015503906011480c9000d155050500816058038001609e80c4035420130503092020071407443d8800f42c141400c1e11041303103007a50100001e00d05070b5006806082100d20f60410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 787562571 1250 787561321 787561373
    0x10f0305010605040504020f090903120f0a050601080106080a090602040b0a020706140403020603060409111005090109060206010f0b030601210b01091707031101022d0d020a08030c09040e0307 84
    0x70b5414030703106403881183c004107008e00078a90380080c0714056202070b0940406000c108004240c10428010541c024000d903400d200141c13404580500403190051716450421003020010404254045034068201e50300800000c1c025104d440c2940081c46142d11034440b1110205407035800c1b94011903403208555880d16242d4945107840c20302c0c1090700c214000250701c1201400840c6460502d0350005080901c00e00070308d0390301d44004000441d0391542c2d100103400510001003a00081d42d000450300003c00982c00100070700c0d41003042010300045039018010100c0b0300400010fa96a20410000e1441c0382c01d00d41000d03004020b04512001341c054582c40a000c12502c14000076001400035440f46018948000f8241032410356540803804603030b4400c1e0504500c50f648008400070454001418504512450104c0007100424080d00b005010183d032402d40d000b4200c0003010620840450354011001030803142d4480d50038001400501e50320007080b203288070200b80c2c3e50030843c0603080c5904010088030a83c407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 787563821 1250 787562571 787562579
    0xb010f050a1d190237020a02060315030a02060304080d06050108070519020723040e0a050a0f020d0b011d060a051e0d060c080103030e010c0308010e0915010f03050106 73
    0x51840312407071000021041100c0001c120380a8030405900c80f480b007030b0015140441210941e0700c008009003081000394085059150f41c090440e40070161101d490016040c4c1031110f40016100303010003005a4031401d10121803004a03038050180010b201d500401e03450f240d0030302e42440421a00482c05070280e00f440c00e100400c3c0396000f2000301d4814405139480d245000800380750050191141d10258065200304000481c1c0c0c0c402403003240d4480c241c07000b580101d6611000810090707601d0710b149040190040000d59010600c0840d0790b8803115000701c1c528150304180d1000c11500703001000d000d801445454004940e416006c051040c0a0b0b08400010034961102020840402550311a46600c00803c4030030007550108040800d180300c0d8014034540350320b40700352030392800c0d1600f2468500000b856540148201504592032001101d403e1030010442030a0b0f580140170042c7c103004140a42d11060001080000c4c10444030410703003c00c425070426035940d1804050f00b4540c50004480950800308041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 787565071 1250 787563821 787563839
    0x50307061214060a090c1e050c01110f0415091508151f1b02041802132f0c070306051504020c06010605030c040f030b04020103050a091a060a030b010f050a 68
    0x1500800c4010100103440b07140a040740000c10001b43d502e0309200d585041140282d52a41002e400d6601e5622559500d1402200503400c49030040764130b0420520031300110043c0c0c8001d20581d1306550004d016030b25550031038541610703611841e511030405490300c0e0700d0316414540d10042c520b011300d00b03880c5500d10790700850b07040103103103490005210703070f40d500046080c086503118000e455180110340a18000c00079098003c01c0035140000302a0910501e036040c2c2e002141001165603031041d0003514104508001c110344410441450440c0d4448070103003d0342103a42d00d06038003c407500310341400100d0b1041366982c0707060700180c1411210326480c1800000700341c90f039007003038021182031301d100070003810340c0d682031086c162910b07013024003200d00d042018000403500310190404000914003540315800a89405d01c001800d460004156001103400c0a50741800545031000150070b40e101c05c82c2034992641d030040418054000c82c3c0c0003074102d0600d00d0000481c01030741200d000c156603090b9001d0707900f15181c601071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 787566321 1250 787565071 787565111
    0x9140309010806040203100305031b07080d0507060b2707030b01050c0721050d0534021003020c1504120504050a0b03040203101109040c0809070612060503070612 71
    0x41d002c02c03600c00c002003903440c15500450b0300040c1e800c0c803215100c0e00c980310507141d41c21480c0f010090a42e076000310000342000f003103180000c05030342005140700d04942000030600d0050b9400100401c8d100d014000c9130755650018a000e50020841482488141c248146000c903001d07902480841e140207420501395200380300301e03404600042c000780181481d24144128001d241342c1c2400540807801c9120380000c4003171107140030310880f40da101034651b81004100d40c41011202c0c60800a1100101d10b03454404080024140868040b58054910845007030203030003a1040000e8a240d900504403a0641304604407405070013140104110581c514040c0002d442d44e100d14007500c1da101d040a02c08020300a0b0f03840c01503620503c058140c41070400c0702091a4250fa02c00c0450704004080030620840b9800c092065100507200c51620010a0034481511a1203002e0750068204022921080c21150b6000e40c2040d00148000f40840e00045d81c0c41c10010300c4c0c3d054100e412404203040c007034090b002103e00a00707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 787567571 1250 787566321 787566337
    0x80c030c0405151b030304140307030c060518030d060602070f0f180209060d050633090f060301140901080109080a0c02030a2a080f03040306150e0a091403 68
    0x15403809007007000b0026003480791105080e1000b4104515080344019880e446800b11340c050003140c50703090a02d40001d26007451003420b40705510502204000c6035200103040c00301070300310030000342d1a103852002c21100d00f408100b001162100091807c4040e5450388180c003228115405d039101c17903803074140c0300c6a14041c40c071a1707515a164581051003402410704500300c10308401c0000501d001d603920003080041d04019444080c050b5100c082207201d06060070030340c10001c0c00d003000000c200b1403412030300070030320700110210513035003022441c0ca01c11340318178110404503100103101c940c0301d681da8080504924a44a00180100070402c00020076400502402c202c0d2a4418050750400c2d401ca0011186801140c4080e81c2c0351045512010210349213a61305d40604803101055084c0c0304407018005d0a00401da801044141c3c4540c01c0200038020101c01d1310140d0340d2010022070800d181003410402e030f80468118000c034641c903005001e000d04c03641e400b00d0401d910404100706041e9088030059200e02840308 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 787568821 1250 787567571 787567591
    0xf121305040506101124011701020304030807081902072604081b01120e071a130e041b0e1005060f030703090519060b1f0903170d0c02030901080c03 65
    0x4c0c010814170f001c2c0c03422005a51500c030458100403010604402003045080b1100d5440042c10018409058840d030340c51350380e07800200250b185040a40c6c0c000e140c4400200000c007001f047c030703000c81d5100c03220709805641d101140b0740a5458800038141226031400f8625040348a66001c0c1a009154500e6804d48040b2500800901148480860f0300030248040019807410000e041c1c90310742c25a03c80344684007842800e140103181660802400c1c0c100740c48280540180e640c4140084030038441465504015035000d202c489945460700e03d840c0c2c0b181d01001051103910020050042103503c40c80403050b11400c01701e100c113000c056854060041074443c0800d82c00074510100009080303140240c10081e010792044044a45a1851000c18601c2c0d0300030890071580541c80d070a030440c1a1400d00e8180300d400820916514070800025400b400030141848010101a038210fa4000c4101c114002d980c0c0c071201c0c814050241c2c0e40801002034482d0300107042076021422170004070700b503202d8080940b4400c8001030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 787570071 1250 787568821 787568839
    0x140d1106061507120309080d09111f0c1a070c030f090b09060c070b04140a14210c04060f08060916060309050c0310021c0902210f121305040506 63
    0x280b01c0140142e0f14035101030504d911ba140950000e82c5400003002c98800001c400240a0500e140180101303280181e80c92103a0104522540c044004140610441101d418403c0f0b2505082c900300d4003400540020700c0c130458440d0108818140c10100d941d035520f00c83d07503c80071801c07200c001c241c400002a00810140d02020b124441e044e003056070080071200182c00c2110440c81c0d8490304100641e1282d08030340411980c02161180c41c1c2080f0820380d000c3c000c5040c40c40000b80c0207078003103070307010100b4603002e41d004080703010100042c281809000100c0d04050400d0103040d84030140080000128400c40802e4450200040e100c214003048040c01e5980150316054a245080c60071030162043c10008d803890f0040300c80c1ca065942e400c01c051074414001c0302000d81c4880380342040c1c40280d600b01c2800342030241884900001651580c0ea1031080701e95100e059032401040d081c8003803070075500c0c048901c40b0340f080c11003080d00124100058030180d85501001003002fa100c40c140801d440003a11010b07000110b02c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 787571321 1250 787570071 787570073
    0x2012a030f1407030f020312010f050f1c0609150e2d060c0f04170105010f050d0308010b0f0705010903030b040c03060b1228060603050f01050f0904140d1106061507 72
    0x8503005c1c86280031a00c112400d03c52045003840680d0341c00ea0001c0e4201c056207408000c2800c00042d10b1f1418642100c182002c0100007020308402a4880802421302d95201002c804004000300c0b8051580ca075604200121844010000d0b502c0b5000740d0700004074009886002d29100e50501c0d910b0518241d00090007168580d01c40000854020320458a4200005e000c04241da500410500c00c1c000c1c038403000810954034100402440800c1500054010420a142180070035041130540e0304441504440d03942c1c40c518404601450f016002c801411542081c0b200f405060f417542204003070701c50407601004600220441907040310014421a071017000c2c144040900045047c0000303a0100030a01004500038100c84045030300041d40c0701000e00540e4544041c031209500d445203070740c043c500d8000c02e5a01c3d410540000c400b00d104910480c441d5407550700080400c0141e03003000b061010b90328220360f001c003a01a0702405000000030140c001c2e104030340014075145041c00074407188092655680e1324055207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 787572571 1250 787571321 787571327
    0x61510080601050c010c020a0b070306210218090604023c0d060c17010b160204090309080615120604021c210c110f010f0c02012a030f140703 62
    0xc000c10242c14401c00b03000c03865403c0000e00400d01340c01e000b40d01800010a02c3e00e000d84440b4005020b101c205441c1c448144521080900c044d400d50580500c04965000c0a00c006919542d00003410400d03482c00300c0034044480400209680200d00c220350321000305a1501c2500c111310030800c00d940120351140110410f0041c1020380b00d1101801826130440082140c031400c0c25110381090b0743c400601208841010f210100ca01507001d441c46406131490200380e00109c1c2140500f0751400303842136a9490000701054020200800148104801d88405240100c181940010015600c60003107500120082c01d948000c90184d10840c0d004000d420500b07412a81c000c0139803842d01044070340c0e0200070081142106901003510603100160b8074030b81e8101c030a1604d010030104803000940035248000450955a80050002c640a1107514010560725858001229240f1301d4181d8801c1c8009411240f100500104c10000036080c029142d564800d96180e00c1111100041315801c449800107220440010744 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 787573821 1250 787572571 787572587
    0x16021b011d060721030b0306040222140105030705010216120f0c03050309041b0f03020c01020f160b070206100b1c1503061503020a0312110f03090102061510 69
    0x81c88554940d510344180e808141140d001d1001603580d032021441d03804242d84040c158450303c032031601e814040091194040303a80c415028000901c14421100c8941842c8440a80c07900302645a610602178881107440d80b5140a0013030013140d00038012440b02042d0741d4000034801150300c42150110b95207030320b08480f07408610a9500119160007480c407400b000308401e0450700020b507025901a5580c2d80e2010704220488003008900d11008040030096060960800e0f000800c4103103500700035903503000401016009129802c80d050301d929020500141e5010300c040d545501e184159064080e03615a10001d990310301007100c030703203401404c20700c42841820060707030140841410642640e025280c1450300c0c1402d0b520101e244483e0410382003010070902c046070103003210103101e44401420f001d0554001c503c0390911400003400300024141c07000f51841c414841901840b80d134405540c040288a010305480342d10003c4210f00512813540402c1c50380394a50706200502100410f08545004102c4d403d4030040c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 787575071 1250 787573821 787573847
    0x15050604240903020a0e0a0605040c0c030c03180605030103140102030c07110a1203050304020907030204140405180601030f030f020106121101030b090c120c03060604060c080903070b0316021b01 85
    0x101c030b40000016101c85100c2006000e202c005250386180040302c044c00c841c610380c060b510540c00c1518640b001a00303d01d110351099014030b8000208c0c0c1c00b508007a520307055200c4c40c2c01025582448005030740c0ba03110f4050b5058074420120181c001e031801418500380e000030b951488003541c00300160000070381c50204641d0f82c018050f011552441c0d07107801c1814021100701059004c600b0000c200300441c40c00c015544c0c2c1c8090b0a0400b141041e080200b01c58206609040e03a900459071035011601c1c0710b402c10b550f01c2c0780040807001c4032650760716441e20400d81e000c448000c41c04201c0a409100d507840c0107010300001d0307845414448204544544601300820042c0e00380e0707414150340f108895103a840b944203140c8039800c401905c030366a910252019a0f8218001c000c0b511780c03582070041c440780355540b070119001c544942c6004425101d50b428202d01a02c1081ca4596041c030030440005903403007104000d94401d01035141145018100d1450036078880d040750204c1240340003c2602c4080c290f0041d08103400b01c0d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 787576321 1250 787575071 787575077
    0xc01080901090b0c040501030f0e0309010315030b181005011a030406020909091c020619091703040f03110309010f030c0210020403060522050d0302180d061505060424 73
    0x1658030394880f0501c4100640d0800781c001ca0004040c001560140102c2c9451090349004018040c48610790540381d0280782c1d003880c1055255810305c2010780324408650043c541000d61030810341494200c1d40030b108060604109107010301054588400c0c054410203040302d41e0121010901403020024a00c990f20082044a081e58207000c1c3e45840c1d11604c041c1c91260004600610108140d000659000d10050845c001154851020071003140d0464003103240b00701c0e100401103030a55180c64486000e40b90240d802d074205030701200704000c0c001c01c810800d5600d07020f507c03a01d000314011403c8a40300d210340382103203000c0b405012603055110300c030741d11501010969106807a2030b586052110010f07a405584140c4005440398140805c020020158a404104c1c40c103064001e00c00c42c1d510591201c0d005c41e0007409150f8041401c0240e0b039031603c80c0b01342d060030040a01680c141c1903d404801030900310b22041207043c000c8070200369820800b003160151005034a001c41a00e0407100c08110349900500b80301c0030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 787577571 1250 787576321 787576331
    0x60603060e07080609030c0319030b060a0305100e060f0d060e1e0c040e19051509030a08150f0d08040801092103020f0304020d0609050709060602120306030c01080901 73
    0x20542a21800c42041c0724000900a5585080320f440c1ca4240b0240c80d18202e608100300c1d001c44071100000b162884000ca114114038103241810a500801c2c40f101441e8001c81c002a5072880d4641c1940624400c1081e030072942c0100f501e508400008017022070348244c00035801540b030714261600c022024030f0300f88601c8010400e054031141060a04015200bc0c240132242d0440c0c9034000c03c0c003400342808400041d00e0420048092419055542495102c0800080420340840050000134071441c14905075a500c100c0c12402c2083c14181c4d60341c800011840095441c00105a5502000700807203400c2c0d20080200c440c0d0001101081898200000101e0b20300c0c00402000840715400c0c0142c040881c095003542d000000c14981d0a5080303029800401c042610400500c1461041c980c00c6e0303904a5010380c1e041240709200d103044401002c03000301c050210710440350009000d0041c1d0304028165003160b804c1c1c8801a29690300f0042500060300e03015415044454035242d194402c0944e80da00030620300011030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 787578821 1250 787577571 787577573
    0x626090a02040204090f0501050d11060c0721120206190209010e090a060509150307140616052d07050616152a08180708030c010b09060604030b070507060603 69
    0x890341325600a00120751070700d0880007240103a101d0f02c1d0040c80e080e60784080300122079a43c03c840c3c0c110000680c1c481c4802180658103410f04000a8000d0081c00704581410940c885500c41000b84002c0110303110528010080041c5202061450251980030726004481213000045006908503450140c10010185a030b11060b40c3d441001d6400b41c0000360380000c0340c41c2840705000703024800070520f01c101c110041e40300d4650348001901c20101d0344c2c9028491003806084c2d0014150380b180040307410780d84801003142000d02001140701c40c001d424442070440d0f548038141800b42420001e02491100f03420090b001c0000d414544014515903821081d07a00d40320300e09945d00750740301c0f15400c8181000c0b0b03a2201000964000424040949600c2042500c08148121001070007400c00030000502c0e800b4400821403050400c20007200548105002d50303449020300c1c42d2460080c40b24400349880740c2103040214003039040030000c581c03d5a0b003081d00b440740396030303903100030b68580c1e00040d81102e4003540c450f0000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 787580071 1250 787578821 787578829
    0x9070e180112050d09180b0411030403171b07060e01020403080f0a090501050309061303020f1506091302010804080f0f0a08090c0109080a0b06150318070626090a02 72
    0x25019003004600100003020b01d0030818038002c4c036560343e0401d01400e00b505000c40020303400070249401103210042403803800200400c000d881c510744480360000b03000c410f1104060300300e4040b101e04400140741008658035440880002d04408048110401e020041d04000c180c40c1c5d0400101c0d01404000585442d03038075a12103103e588520b16140c4c0d88440800d82c410300e150301c42a100300070700702464280d04500713150074040e03141c48014150142c0700310b40c503601e002014000d01030141207851038030903202c114201c4150309080340c0b0101c8040d0f02c92844000003c0070b60410302201490f00f40c069644c01002d030b0341c1d031752404240c7d03220001c05001e0b4041404000c0d042400d85004115441c4266134481e401c0c02c0800602e89882070494400707062100c110f030180000c1a00040c14002e52b6001020003440313071200404a8034400380108000305d5420000200403184542c074070b4020410036014210780704150303140f00c00c07078101d0444058801e04134000034210815200b001006074002400c4070a441541050380c0c006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 787581321 1250 787580071 787580119
    0x912040302041a120f060c040311040902010c0602220b031b0a02160303030f0f0b0303031501030b120604020102070602030c0c010c03121406190815090f01150e01090b09070e 76
    0x13201241c5d000765022180000103100454000503285151420300d800c2d039440c0075602ea00310b14014001c90366429140151780c4100e00750304410350040300856035240406060300b8211240c0c01030714074002080748006031495030007080740d116416026021421440d08017400d1095800005020304505c100815082107050142c5128000c5101c0e44000030310091b80900d11056400c5117040403507e03071070041c2542c1e884e2404001c41390301c00d15142c03014007410314100043c1e0042c1404e8415076081114000d1f41c10324980c0004080340118000d03001c95847c00e680e08000ca82d20710681e42520100d400020310000954010910b00c41880c0c880d0420344c9199503118550400c80d8146410b07540c028285000307226203401d012804413803d000041c145042c007418103d01ca550388901c0100034507410003c40000710741480a00500d604400c14000a002403464440c001410400301d00645281b050683c0000518601a21403100c8203800038020300100c4c0e407210030a58a09585058082c7c00a4070944101503040c0c508801e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 787582571 1250 787581321 787581349
    0x40b090607140f1b0102030a02070504020901051c05040b09030304030519050f0c0105010603180b0133020715080f060d02031e03130603090312051e010303050a080912040302041a 78
    0x209200c00c820411300060900b4082518195081009041102c0303a0103c1c07007a082c0c83c020381d009a034902c5030381c004840e144555040320218003035184100040c0000741c3c2245001e41e0050451903481c1d2078040c0b40c9a00d0340300a50b80103003c0b4108101c0c100740034201a000710880c00150130b0081c180441d41d009175a00d60300085c1c0c02c4200d03035501e0006000e8a6054030803181082503c4c2e08110904110340d90b445400348040c060a610395102c0c180310512002c804d485181a02c06100000303c05014296000c1d543e14081e0003151590b1044a4561107820302c82c5421a10544c00303601d014501d501e4160038030000d4000208140d0b00f6005040c0e00c0e00d21751043d00d007803100024110000710f070340d54400f40314805020200e801070f10406040c082801d02190b0700082c58244426152000225a100e0350340f5400103010390500c4442000504000000b0b058000003c1c1c8808145501c450070565245162117481d4104074a072401c000d8001d02c824000f504040d4031072116896180014140c21081d00c00194201d0001d004d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 787583821 1250 787582571 787582573
    0x31918060506122a190f0e01060c020603010302042a021f05091213030f03050d1a030d050903070302210d110d0309020f1003050105040b06040b090607140f 68
    0x24000c1a080208404680300c0a001c0034000484c413888400700c0c04884000d192125821001541056a459041d0340d940c1c028200b0809004d00e9503903120f6402e540952044406030805100001100d0f40100c900008440e0b0042c42c2a195030700350341c00c100c010f000080c0c89440581402403a0000d0106461885c00d01c1c004c60340040050801102034403265541130507000c400d0341e0420b818040b481a002800f448118010084182c480228076084c4049600550002c2c120b03414031501c02d418542c2010046c040742e00d51040a00500688154200076102a003002c3c0b0b4041e844074040c200740340d20400282a008000401b0f5844056690700020b0361801c2400417404a40e40040402c2101d40040005071401182d50424a0094a800710a69228080441c880b014140c075900d0a50441d60b03102e044550030f0350b00900c000d12001072054010300802090044c14001c078030300300d0b841c0704a2a107402070f14103c0d0b030b000001500e0904020b003031000a03045200c044540e5481c00c076100c0e0201805000d84c0c4115004c8030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 787585071 1250 787583821 787583831
    0x2070605010e0121020307032d0c1a070507030314090d0605090d1b020607022d01021006081009020f0a08060702010606090501080f1008012a02030a0503191806 70
    0x2815807550341300c46040340f0319801112940e800103072004a41441140c0d0021005001100c0e8108001c22401d4641c0003403c250750410000c1c401c1044060040c0305451030f01d000107002001c0764200c40124418510003a0031540b0982d01040080e2045010780743c0710b00444031003401c0c030602c000462000350003094200c03886a1680d08000d9030103406c00a510340e680c82454000310b01030340380d420781c0316121455002034000c0d14002800025522205000980c0085071f4281d00c6045ca050303070410128103200041d050050080304503030510608076008030000d49400001829002007123480b494010415200101e0304800e03030707240200f0329545d080740d180000c055450107001949060030b0000d0840d2100c4d0094018060f807110203200690b4071650f915032101145031032070321545440103090300320307203442e80704034003a41c03e0414500d0284060380300c404d5000401d140e41000507141c0c400503030300c90062844210003d081400018003402d801420120b060182841c0052500943c500e000d580700c0c0002c1e000d90383d141c0c0b10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 787586321 1250 787585071 787585079
    0x1a19020720090c041203050f0301170708070f17010e0703230d0504060c020d02030d02031e120403270605040509090c1302071106070303061e060f0305090102070605010e01 75
    0x841c9646501c4208550191039803410f908802520700a40c00341d00e2203004c0b0444080101130250040350340225081390b00396100d45e910b490710000ca000c00b452401c401e0250000003d1a1407002039014191205001e441d40369605164810442400f409281409592216150301c802d1034280048800385004000c20313104060584203400000c4540811041964400000744145c0d9a21a0a4400361807580c60704105e6541e00b400040c0070381e0601a40a5450b000b0304011150041e0000024601c1c10100400b01a002404800405a0307000d004a104d90000b548000030307000900c110258603c03440015000540740303840006250302d034181500458041400001c0030300c1940b030040e0303003594015007440061069541440108030090961304440035600d40100d882410445400d403502511003020b0581ca880720b00c0da04004000c2d0089105420648904646c00108000ca18200b4820740340305440701017480c45c035100210b00500c00109099115582400030100198075070007801d00a1107004800f102035418 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 787587571 1250 787586321 787586363
    0x52205010f0f1202101b0605090d030b0108091903051e030a0b1e13140a0c110a1a0c0d021308070936050a150b0d1a190207 54
    0x81a044625030303040c81215030f00166503d030b081c039540c03955078903001c4c0e1100084121b2035181000360600030101e030708000400c00b008030005164400030f000c940d000e10103014904010b50740d5032400d40d6131007007030b400903622002e08a9050705c0e0291980c2c442e240c07040c0380200f91040b550748880329040404001c0000400d201c1e50700da450051560f402000c64071f42001541c610881c050f80160104c413680070301c007103000c8501c280c2169405004170030380c41c500030b19071445c0412211004040e03010030000444c0d140740740405442c41c000390103501641d0046840099051b080d80b0481007000080030004084c0d07040000e18842e81c1c450014169100200f8559802181001c00050400645401c00960315180c840c15901c1c01d010b4048080001150741100c4032000f12150400c200019200f201418501c1180b01c90030400542e02003007844150655070410139040d1090801a01e500520b070701604800e000c0000d03807020340a48400c86d801102c408100d010020b680c0f00d100081c0e800200c001c2d0303003000000701c1c80c8402282c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 787588821 1250 787587571 787587599
    0xa1211060a020a021c1e02011d06240f100e1003180215040504110c0d032a020c100518030106050105071b0b030a05041a090601052205010f 61
    0x11070728815400d01c0f03035150300290b444d203104440c2101183d45c5003030811100d02a0000340d4102040c40c13000800c410304c85501074081d00503020650f00d060030b40d0034601294580071a2440c010403001c0e000c22251060004512141c652804105612080e0074034020380580e0b03181c2c03445076909101d4a0b40030f4404180e00070012001840280c0206040c00c12614460b20f0a030100000d0085a0460b41d040465043c00b030310740c810313000e00d801c4075810619081c034224a044030315000d0f280b001e003100c088821500001c1c600314207482c80070507801d900c044e03401801c49548400040d0014903907428411181e4911014000560b11041100c082001c03500c0001e42c0340118040c1d4042900c0207000340c001744030580c90800020550b10030480080c000c4040e46c3d40c02003c40070402201c10080c08102082e80c1c07030b41407192a80c0020003082e10100ea0804610803860302c1ea034020014280301d911240003808039607103400309019120817902e600304040b40f0105400b0142000a00c0f0b20741c06032424891030140e2900300903200280d45 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 787589928 1107 787588821 787588831
    0xe0108060d0f05062502240a2309190c06051b03030103030e010806190509060406081002030a0c05041a0a0504050315070e0402041809050a121106 64
    0x12145030604644000c44400b9019030401d0681c4c0c2647c0d10b069141c080000c1554441e4a40f0020b0b485900d2980d1245d4034500124140340c0c1c9074403100f00b403072002c8100822001d4441c02d101a126082110f00d0b80c20454030f80102e205640e503140c00c0c518004a11801003001000150f02c0001024410ba040f8200710003c1242c1c3ca0b96100c0c503002e0845d01402510034001078411000803514580080403141c881c1c00303807060340c03441c0782400144040100010071003500a610384500003880481004284540f4043d10700068403030801041e030805540003090110100401840309005140340201d14a001002134045103954209495003500c0901071907202d1549401808c6890001081801d0341c240324010542c0c40d50481440041048120f0045000c1d6100d40001ca0300c034410b000c0d441d0f0307200245150040e000c5503001c2a05c0d0762411140302c810081e0f5800503049014031001000100640d80e049 = true := by decide +kernel

theorem cover : BRFrame.Cov 787410071 787589928 := by
  have h0 := BRFrame.cov_init 787410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 787410071 ≤ n) (h2 : n < 787589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
