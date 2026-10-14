-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3357
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:25:57.333465+00:00
-- url     : https://prove2.me/submissions/3c81bbb4-c974-451d-964f-3075f75d9e94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 603597122 ≤ n < 603776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 603598372 1250 603597122 603597167
    0x1e1011040e070203090a05040905010b15250215030601090906060503062805150f070b01140909060f190507020105010915050a030206160c1523090d02040219 69
    0x20700b140004241c401c0124000e02c085142400c0c94180310181600720401c44483d920f58a80c14150b81d900c02e00c056007040c42c03030a4903496448002c0c2d003020f822200054043c1c01130804018001603114083c0e2800d030500103000496490304d80c140120342140f040c0e40045089480d0039000726080350b0040045001341011a040d0349005030074013513400c0490041440e4583c2c004030600030406400c000b50744030355000200c0307001c9082a00c0489001c001c2e522003001100d41107540c1c801404241240d21a1503410501a42c4c0c02c003052405810300f13030b915a0058841c50317203114401d0020342800c206100904c2820350490f8144118103103458040d000c0d01d402e018292400b400c083c04941c04041c42020a011504000e10403071090b03107543c0a001e480c1e84612401c00c40408007248080100e006c240031440107200042c0750a00300e0080702c030000c24010030b00010501c0c0385001028440c1c60003080c0283c8013610001c03115400001d0303071480042d00910032410070390076072030b501034940400c66000507140d012001c91085031304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 603599622 1250 603598372 603598381
    0x30604140c010306230f120f060a02030f0f0c040b07030807080106020c0307030b0613020a1d01021c0e2818051b0304050a0819020d111e1011040e 64
    0x506071906030140d0080c492a104190640031417032008098040e0002d40103410940040303021610084926001000c16400882c504e03541e00006c0013201d9210300091401c6045080c04000c1403c1034101401d0018682141070101c0d8684408000f1034004100c404e01c2e040c0e680c1c069240141440740111060780106480340d00001d809030001c1140401a20001c0107000d4043c2551740b184204c0070007924840d080549510004494545e81c40102442020381d2520520184103d64000e201e400001c12241103400108500e04d0b11300b24040c02020003010f6007803c040f40b0507440040f030b049040c80c07038018100e4a10228480d186030500d18510341650701c042669005003101d504d8900c1a01d0054039441e95943c03d076250f183d42c0e24240d101450304148940700780c80594403141c5441085400c580845058203007162115203160340c04104401e0010503908010010144802d855a1682580710010a00107100c000c2d003809410144510141900004c03010007660089040d414203a801030b0041402000780324000c107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 603600872 1250 603599622 603599627
    0x90f070239010e03060a150b0d021c02070804062006250203070b07080403020a05070801060509010e100902090d06140106030518190204090803130c05041109060c0a02030604140c01 79
    0x2000f502c9000360085c038564462a600d1001441203030b5031580840710300540805c48910480041030700740b45510000da16602c01d824108210030102c149440e00a10401c14000040c078a801520b040310b80a017010b002e410400b1160b41c0014918803070700c42060190343d0400005900a000281c90500d0181c1c0c503542d8a414a4400c0c1e03601d1042c440080d2410189800140e51a0b10499203180d000b403003031054a490700030b0f581e507480c5403d07407d421030012651681818006810411b5005006048075150304055040042444002c09094050030010f9a00040e100d502a100d560f070307001c40f080e8070840801506204c401c0c1ea0782002c1003801254002030400e00450112540301146421069044014017060700b009080c40c070340c00c03005450480e0441d880d80906c0d4045603010707010b50b204020118260040704a9454030303441c200042d1300010300c00d51402011514550603c0d003607c00c5080240d401070b645900140d15907150203040d4500075803501c182c0040004010590a02c02d171010540b0007203820444144006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 603602122 1250 603600872 603600887
    0xa0e01030c050403210e180a09030e090c0c100c080411040b060406030e1209100e010c14010c0917030a03050a020c0a08181e04021305030601090c170105090f07023901 73
    0x14a00b0030741140110340c20b003a103075000009c80351103030034000388050700f402c0032540c0300c03100700c2c0c24240c00c2d1804035080c45c00a02c1440075070007480090508201c000765901020301050340103003015103e1034040c1211311031078941c0d900c40d464040340101510b403995902c40e002009400b6100c09418140580c41c0084510824102600e807006402040d00c1c69021310300c1002c1b9013000c0c656805904000034200d082c2c0120740c00c0644507042035810000441c8401c4200781c09088054960b103e444101800c00700100385420200540d08008614507001c1404d49404040c0800703409419414000c600802ba210010400e1070001401c01c0c0e004c011100700d610200e9020030040416a01259040b01320131038070302d050303490705d0b600814008221000a860054135440400d18040c0241c021a84161340c84020200ba03c5d00718081080380349440420122942c14139001c00d404000107822401c8410200021a00d124004d02690a1052600441507003140c1410702181f198050a00614070041c1200d03200c0d0010b500c110304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 603603372 1250 603602122 603602149
    0x90303150815091c09060206070915050903011b08071413090209181602070906210201050f03040f1110081503120408030408120a0e01030c050403210e 66
    0x250003403406180741c07000ca202c0018000081d50151890100d9490741107522805205465920b8480e82da0520740c010340b0303044010700020b00f4010904010040200c42c06090350700d01189240442d21151694080780c05410000100d60110240059080200e03600c20461031044800b80d484890130003c044407650103208014101c0ca01d983c014806105892094000705510301014100050101c0450b00c1ca0340c1c0031505a8a04d2290030a040d0004040c540c10005c2c4405000c0c00d400820106e8039050740c0394000c201c028221101c541500014409580c0500182c890009240005540c0c034078140ca0304900004c8000c85c1100c03c001070401665590a00d044541e42007a0252910492500d0f01440d1510200401309138540c144240060b40f009409600c0141005014600065484900302102c840c106117916a00c3c00011200740003048070a1340c8048894a82042070030300241c0b808818004450b9071203103420150940365031442c0892805141104045a25010b50b694030f000550302082203a0b0446004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 603604622 1250 603603372 603603389
    0x10e06071707200a060903140901020a15090b07050d0606140a03050408091c05010f27030e0603010b09090705030714130312050403050d140a1b02060c0109030315 71
    0xc0025032140e02030b0840c0040c0c1880e01102410022445220fa0316000c083c10003203514035101e060400825801c041d1450f04c0c40d10019000741000c1034000000c0d61210039603005041641c061056800d00c00140d80101d00d83c40d00b0610103c10b51501c40d1014206520084050942a00d40301d0f0002c2c80a04c141c4448000a5103003020078588403088008801809020b40146c4121808110f003010b40c0d070f00c1c40c0766a411b44890409100c500550b0307003002d80c00c581d00040004007540c2440c211407404803050464210044028000760841c0c01b00c1e007000c442070342100141c650020000400840c01030303042c002420392542d04641244c1c1701c0c2d42c0d01c0030495a500064910501280224803214841040c100152071041c40b941c00c00d6585035a00d80ba2035084030022020b150203d1070008090003402001d000701001e22020b410461805075882c08408082c0c4a882620010092024107856000c55400e911012503074005103241d4564400304c070000e0007004d0641044010034a8042035000c20306000011f14120741400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 603605872 1250 603604622 603604667
    0x3031713080f2a011508060f0708070e0405040f021215070e030c04060b09130905030a050309191218050604030602030403090f0807030209071d0f0a0f0305010e0607 72
    0x340880c0110b8002800029240f10700034850180c0c070b80c0f68406407036030030121800441c40f0701078400c01000814090f08083c002e034000340308101480000c050040d802ca01d10389081c0c0e40070b80d5040e100b110104a2488050343c0b041c1004180f1040c0491b00c00490f44443c000c88a6898001c49420030035900c40a15003502640d20300c260000b152240511100102c5ca400902583e84080f22000020304659407a08031001c1800082020656418562100141c0b11000e00042040c1d110030385806941740245200c0d10104080080024010b100034800240780a4503c0208400d8800074501041d0101e01c05110f140003034000070508028402e14684401102e00140030f00c0c3c034060440c1c40c1c1d03101075800144164203006416000194500c92005401e005000400241c0451800c5104010028a020307001104022a001ca80b201266444041c21140c00040702d0402c801c0404c44081000042c040c1c1c00665013000a140000c00e229064028410401048090f0b8515980c3d1610035242c05441c0b02a086588911 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 603607122 1250 603605872 603605887
    0xb0702014b02060f1906090203090106031112060103020904061e09020f0406050a0b0304060608060103050a0c0e0c090405181b04060e04030207090b0103020f0409090b10050312030c0c070303171308 86
    0x650300420000103641d4030106403144c4a8018505132782c420307103902d04560754034441002404035a41d014050300c0303400c0310200400004041d044c0d41d20030043c00064441c002807404142082040d5000d0311100e04107014001a40f00c200f89179400425034401d06900580e02c0480c05130340b901c0d05109040603180018071141905050042040c5680c100030b2084402035940c03040450580c208201c44c80c004c1d8800d400400303d104942ca170150071404180c1c402c1b0300031040c0f101480000714980085d076240800690300041c00d03507207000b02084501c10700c20000b001c4c1e00810051700098000344a80d0213031240150360502c502030307490072080040c03142180d020300160043d040911101040307402c90700040c030f0145005030410982d033541000c1540309034402c080d110780d038998401c2000300c502070495000c801c61005140c283d2420000c80c3d110b03010036a00035488072000000500049c21035040e10f600c2207041c400c440c9015245d00d8040d00c0d01e0005008607a0384814400028034a00343c280141c89050b5200d07120a050181 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 603608372 1250 603607122 603607141
    0x9011802071b03291512010615051206030d2c15030a1b140c01060902040305030408060a020307020309010e060c100501060e0301060b0702014b02060f 66
    0x4000c40460710360640c2c4500e00d940318140a91140030318041c40c070800e0a2524400001c400c1c0d4409012045803100301010070203806003200982c0c0c0d14940035254110b1030000803c8540c0140900e0b0000c9016521403071a640c100c9038444043c0c0302110355903591400a4540100309550340c0c2e4406038080020740409401c1c8804080004600940182c00180c82442022400000c0c030a10010002840540c00881005119521405000e903c0c1200044805503524411001040b0545002342c941c25220001003000140000b544090300070104888115121501c910701252283e015100d0104c01d0310801001c62200e030b01c10b208503030081c1495001546448001d41c010b50790065400d1700103900003000c4c0151500e0720b80500c030083c1c1c000041140000c0035070401102030200082c00d000d8600980c5007007428811ba2413810200d4410f50b809003040c21484011b080381c90540c11481181c2c01890201d0107100000440000c0c0d504410f42021000d01d03100c0404603400c80e034032502200e981c86401c1c44507010032084003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 603609622 1250 603608372 603608377
    0x201060b1c1e0f0b0405131112120c0c03010c1412060a12050604120f051e0918010501090b0c060a05060402190c1514011502030714160509011802 64
    0x35000001c5560314003600801e4400c5503480025414459159410321132240350502c22a584248001d24500740c02c0d03810740783c004003c02d43c10405801000005010703007130703000100900d481c40c104801c8071690303c000c00403866485801c40c2c2252030007503080040412505004090f298a40228250801d0400c904c13140c03c5029060090210350304459401004500382d81850030034480b040c0554020a09400c240c40d15004d40d140d03500307106040180c2c0a002c1610280d0080458480c2564402003110100c014507182e01139104d08000d02ea40b0803400e560f00e5068071141420700c0d049400903200c5107c0da940d81d0408840350700c110503001070340c1e821a0001540300ca03510380c40320b0340000010300014209030039810380420888144042d00c022591030240b280410016900c00103d12400707031001e000c80d001c0b0300c0d40b00e45960418054500c2000205418107c01d500c2001610030300c0350010369481100c0050303115151105074042d9440d002040d007040108603030510001a504a03203e45404420200350041000002d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 603610872 1250 603609622 603609641
    0x1502010c1b030e10210b030c0409140f07030c08010203040f080a0306050a1701050916060804050a0506160f0e011b0c0801091113062103031d0105070201060b1c 70
    0x301c0c92a010141c0f03030241d1901c850442c50f10f1365513001d103840590702c1e6417221252200c5005401c1450880071900d02062101c009076095401003103403a090703c7c03c10344440b9a48540416849020350351104440c00240300d400b128002d41c00d665109855900650030b034442103a0182c042450701d007c14000a141c0f0f00100545500791400050280c1c40b0400202c0007003441e84800c48410303e90448038203e40007071150369000704943e0700809009000d00e0f420703140003106106840521144100040c18004240162888283d000c8291070350752509000c2c40d1b00b405455003040e40001c103401c000755040c902442642541c00c80584401c21480f407030711380300d80f18441580340c120749002e01c003e0b002079100c2c030900411034064428900d003071400c086241800200e51504801103101801c141c000c000780d101a04103050601802c60002d1480811b1313080c1500034001084140181d5045401ca540c070045040d4481c40c05540c4982c002d00c42e060782d40d201500d0303a015031040411700c0500c5510120791301c0529030004244 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 603612122 1250 603610872 603610877
    0xc0807030912051b012a0309020913030504150201060614130e060a031a06240f0d110c0c01120903050f0c0a05161409011d0c0c01060f1502010c1b03 65
    0xa614a402d0201d0940301c0c07610100c180c1740b11a10a00fa0121086d44880407800032600e010060300380c0359000240c0e02c1e500a0a0460094041c02c09541418841c00460f4064040040100c00200c03100d400240280010b00c01d030b8001419003140c0c000b25a0100741114050081002440146400e12034140c8444c54081d100340c0e80110300c40781c00400903084000010341c076400c3c50800c0c00e040c41c0540501080c440252140d4114016045101940e401040c056420060303122002039260726603481380d000107110308001000544000701ea00304240c08001a1040f03860402c1c1e9031102400041000c038000d6800480000380400c03030520041c0364400d510000740041110136000c880b845844d5865441c20305c11494014448000442001e00050482200000c203c6c03c081d00e07049a00c0d07151403450b050400f8541680c0b42403441c0d078070100d001600250140d82c48644004000c21001d5a00d000e513078003c82d00343c8a00250342040e958035010315801803080c518440807030303181d0011455000c001114074400780c4104600303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 603613372 1250 603612122 603612157
    0x905010f0e03070f0b03041407030c0603020f130320090723041203020f06091207020103051e10030501051305072702030a06052d1201020f0307030c080703091205 71
    0x4407600052138076801002c1c0ea400280d941e0800d810a909441c240394600c160a03884601c0820000d000c0c0c100700c200300c3d8141d1600580380c158003518022184240008062a2102d210b0007005110003a000c02c007188400406980140a80105004000d0320803036401c0b0200c0c0d0a034030003141110286803990f4482042e16007040c5030544072203a69480c030852280c1030380181d00c00903aa483d222800c02c40c03076802031054801003e60b00510803882010380300d205002810152a0004516941d611020352002ea0001d80041c003814500110644110314051100381c8a03582880d02040c4061003061810401c2c40d00100900096428042904200781314410900014482290001512941403001d54010110000f021480d6172620003080601001950000d4a40d03880d0000204106030040c0250795030b0f1010348140520007105000f01d402401203072034020101c0f0000040200303180c0e00d43e00c5011120300d01e0301c031030350a62102007048045911a0000400810060360300e4403816024502600c0302c0c51071101181c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 603614622 1250 603613372 603613379
    0x300806060a0306090e0a0b0702070e04061a0a061206061d010305090a05030d0603030e1207140105040305060a060617010b0a120b030a1506080c03100c090806011e060905010f0e0307 79
    0x10300311510f0788481718564019208003020010b080707400c036070008940e2004200407414040050710b0070710098001003a656403840200c807410150118800d102500601040c40c0c80e50b903410242c43d081d100300088034003600d8881d003c80c000307002d4510002041e0341c0040b1400001045801074000b4800501001d03503a10415458000041c0204002c00f43e14206600c00b0882034a50310740a04440d045520442c4034540c2d19030007451940380010303150110340d41124295040b5550360010703070302c0d4407031504042e20701c4c0600402c0048000c4a5001041158200e03540d0001c0448180b604030741040081c0581d8218180401100d4190303880380c2c00c40c0003248510580040c1468240740002c2c030304042440110350780c81da40c0015910420140c1702c1c00008144050143c110703040040000b0b600c411405c1d0040320540d0f61100c3d02d12642d481000c4400140c143e900443d045961143c070062003613448980c03208512800c550780031881d50706c60480001203400607114074465500ca003105444140e05502003a070144034115002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 603615872 1250 603614622 603614639
    0x19080901020a1704060915080609060111010f020405100c210905040203072d0f08091e061503030405090415090204112101080d0507050118300806060a0306 68
    0x22820464020f0b46590340d10b141400203040c046c0c0a510841e100b18902603903c40f001d404c41400c0354842412101171241e540d0f1000144e0b00c140362a03030000190742c60070041440080072540140141d5104440e05400b0b2000703924111125020104020000b00480a0380c0101074810f5110b80304104d41400c01c9c40c1c0454507800424102c2c0c008692020008d001e0004803080d04140d010507910503100b151039044d07171301041f01c0041c20b500c2e02e402c03201c8100040f1600050340e510052000545d070020b00b0303484840342000030741c0307942d95840192840c0000b60907a0000600616001040b1411184050103130314480e50b4a4a0354071400c642a500555415103e080401c010780d034900c15698440002c0040c982c446868464281e41010b40c00070014131400f088006002c400700000750b070014241985403480d80d450a0b4984940940200087c0e01e80000740340b107000003000700045038140101d07504040b01c1406241c01004510510034901e120001c90742d00b50102d0101d04021300281600350040c200030502546c1d5070200b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 603617122 1250 603615872 603615893
    0xa0201090b0d021c0903320901031b08010e280f0b0405310209060909030c2b211503051608060702030705060c071a0f07090819080901020a 61
    0xa20f40e016584480780700406420a87c640c0d440204032401658100441e0b4102010f030324800000c14008a01088c541180d80c800d82015000d0312424448100b4405002c40107000b09000380208081c40034840006401c81228400c0b04240c0060090700003106109113810400426217601c1d01c4400f1071722031404075051f0300e82d13019650180c0d00d11740005641c04403068010208960000359483c0465400001d5005640c50b8000944c01203411200000651581c0c4481c0e8131354860030b09401c80300d00410514007210b2840b000c400c0d000d00c0420100f0711400c4d42a03d41200e42007800000081400351160301103d2044003a409000c0a20851444491080d1281c07a5245045001500201c81101c08002446040400e0002da50454440c1c0010340c20880203a80d95500c84c01c005045c200200340c046150b4003885882c18558180b40100c1c0c1456145044c4480401c087c41d2048030090040303002243c00081c035030800214001c4100450380c401c00c10b100c841c0d4803464541d00100c0f0b800d04600c0f6031415a400b04540480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 603618372 1250 603617122 603617167
    0x19030e06180907020d08390d110909040f0311010e160905060d0303092105120f10060c150509031c180b04140615040e0a0201090b0d02 59
    0x140010050014000c00030b080760020701c100f04541014000c1d00c0c0c1607800c03400c159000070061601203607001e0543c10a0040c502801c225260090352004942003800140e0000c1424468000080c0034003a500c03007801d80d0900c50b200c2003540082c045000500407801c20031026503910b109180031007450945140e141e084d955942c068440300c5c1c1204500420700d80c40c1a11140081078a603001303000c02d25101c00058004411004040e00741074841c20382d08104610300ca11200361440d81000047c00b82c0da0380d18010103a4006581d20030b41680a0b01c08a4000a000c030a501d200704903804c440c81d50303503052480c00c03941060181400c58807142d12101c281c50312442c41c0105c5204102e003c0045882c6d00d21581e404e1741031300889484140840c40c20301000c900d0034000003012a500e400100101e185c7e10389283c1fa94200c9014030501c0164003482003401011807189204404200007143c0610500014039005d5450f1b914500000f80801c1c0f610004001069007000078100c1c00e124140018140010003401d08074a509410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 603619622 1250 603618372 603618397
    0x204020c1b041a1203070605040b04020918030a1d0d0b100e01050d140a06150f0b09030a0f0309031a040b160903060222030b011508070219030e06 64
    0xc0148406440c151680100c0080c219418007070f02c51140644009140380d80001d41c000d4114020075003240c0c00401c00c40703038200d502540401551800d0300307101c030780b00d80240c50407889010681c0110b0058521000c0754044401c07100d0244d0314154582c4070640e1901c040000e681080943d61801c983d191b91480f6064508501840500303189107030213107020480c4183c0c0d80241440e44c40190042c0000d4450b0030304218150342c0203107003121405240321010310b031140c514401003420381420029000740481154000464107000304001200f40c403900201e02602450200c580c0603403006461002082d000442c1e1a5580e000b42002d410342c944a440c1d6120354a50b4001d0f040394a542c000501007005602c1030040e80c41404d00d0007425420048040c000e2215801e44400f078a520340124001402c6141a45038002540402807400c919994078a0000940202441401546030440540100c1039002e000c519200390200c0c0d002c0c10300b80d203005a03415030305008004180c040108041304038000743ca07024000e00b180f100b4030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 603620872 1250 603619622 603619633
    0x14090a2309060108060f0709120204090615081603031b02150406020a110d1203090501020903030c0709052d09070b0c010212180a030305090a0c0608150405010b250204020c 75
    0x213190340d107000005804490042c0c116410860860351111b1340c5e03400c0d00c4515070800310a809500028000e002480381c054a400c1c503000c482c0305a134840041d00e404984564050300c10140c040e840c8a58032484500c03002c0c0214201d842c1141241d6070b84d02c101d02201d403009050b1030302c9a0345002c401c4859041074100501685c09914088203000ca04032580c0303030a80f0202c4440e12903c440742c2d243c421141e41307490030005040c2c9418021040010071f4040d50104800036040343d0b250884100441d5540e021485501601c4d0301d0300000c240600c8801c0c00340b1070035a001030900030400c03200c0010608005002410740c21f85d402503401c0400c1c801102e000922a0500c80000581c071500c10505032030b040c4101402019484540042d00e840c104400f141c03946043e030705410002255076800103414101100c40364010240c004044001c9155608004610b0041d8400711000250484400a000c1161000e0051281000c0c00380031341c0142c40d600c104081c544440d4818059800c40055010805981010400150380d8101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 603622122 1250 603620872 603620879
    0x230a0b0f071403070213020703120c050904140603030714010b0603010906090b0306090c100903121e030e03040e0601031808030601141309090507180b01080114090a23090601 76
    0x1d81019001550240590318004d49580010456003032016100000c45d00880d4600506009410b04101000760210900189042020080c0503500010300d00e4031541ca003c0b4036190341044144441d00c1000060f005515200154852800d003c3c002c141502c1e8640d203804484080e43c994002460003052200008a081808c2c20a240705030703031580c0c28941c00381d0b205208116074150b00007503001711441c0507549249142503210f01180c2111b00c540000e000c08643e0f2400205044d4015450710541205007a00071030720030803401c214245c030788407610040d056105000a00c102c0c0311803095160044014100010900f100340056031003121040401d4079000380100c10001c1558002a650400100d26000700345041d806080320b01402d0014091010b00a0799440c510701004820400300010303148511301100c80e419001d0041000e0041d0807240c0e400a0800400000c24840e6040d8012000a006081140e15038030441d100000b00003409544680d0b803682044c0350031588210003440e000318101409010550306 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 603623372 1250 603622122 603622133
    0x1101150812090607060c0306091103040c05010806040605040612030201150e0105060d021902011d01110412050708030c011b0807020d030c18060203090a0b120f060f04061d0106030501230a0b0f07 85
    0x60ad03280b041081f4604204000014510000e11400e5401c00d09100100e42c03205030124006144a40000b0340003803603c070740441c009203040d840284491080e402400b11035101c06402d610908e05200380c0707007004040790041c000e40c60b048002c2c01e524800f100006041106240700900c500c02c03c3e1801c640940d66500d09540d10b403031351036040c62208882400074480c03408011860200d40c07069200d1000900900c851750020040141722000060071000222130315202d00d040002d0003040341d4040c00300c2d1042010100d90095004040c1030340714030056000703805988989901038018100355403003001000b440c6403100400b004600c40c418040c082c60ba00964403004041e0500a100c01c0d16002124203d2045c4001c601160300140e002c0e9000211905600b030688549001c1690034031f00300c441079407042c104980818605042025054128111140550306907620101901120300a000320741100804000406000400c0c0480300408000038000e0b010240e641c5000b410035401505014101e03101c001040d10034000e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 603624622 1250 603623372 603623381
    0xb060402120c09090903030c071e0b1f05030a0b04020d030201090b0c13050d020d2405150f2211090402040306050108060c0f2502040603031101150812090607060c030609 74
    0x6070010001c6d0b01c0c500307119440715500c0c0140c6070010b10020f0301d5241c082929510020887c09154001d0b0408106e041003141e10110080c008901100007544000005048c5400201124400c2d0406192403c40d121602072105802410000b80d0956407241d403003000241046040324840c03104411100c0c0c40c0c43c0800c60303810143da915400188920407054a550142e81c603003140b0300d0200d1340440320a07076883d11481003182d50100400742c00403491501040020020300b01408040c0d102e021905503c81418400402c000e152200000c440303076901041c6407544001d03c0f540b024021050300c3c9041801d0014500000c2c041e40d1040d002100c90640f03d00040128481c00c1107260703005001d8410321410708070442210302d03140c0511251604c14010090440c0c80a40c07108446059003900038005208503a26410042c251060801c0e110016628103140703940c44650442c661400e4075100c00140080e2074508421042517002181200d80c40300c420032248000a01c28454520359080300d46000c214070b0314050021040b079 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 603625872 1250 603624622 603624631
    0x10f0b04090203030d1d0d020d0e030109111003020708030408090102010608121c0b121b06070b060f061b01050f0105060f03130312020c061b07050304030b060402120c0909 75
    0x11410481d00e040183d0300802a80d9100c144200e00288034841e00c00a041d0701061480680c026000c0c840d0b800c1100d95000c91040340303d03caa0b840b00703040503401000349422180006030207844441c3c000c02201c01d40c030304a207101d04086050314000d4104840c68503040300c0d030361040e103085a5103c00050210820358081c081c4100801d2204080c1a80c1c44001e01e58040b6449501c40f43e4486810044604020780005d501c100410340c000713440a400b103811401d65551300d2000f900b5040c440300348061042220724103042184d40c0342e5031090411703000d0307124182403001e0024418045a4440010f0180107082c0490008401c40c1000e02c100106031400d000303140b81c05038001130708607600070001040291000ca00441c2181d400500200c0c24410b6404a41000c40e8090034982180350114000120603581080000b0782d00c0c05010f144143c0d9040d2500886074081c14400d08400514a0300240703c1080420061a030843d44104007810152a00d40c0c16038841c00042801c03200804e0a070300c003003060f108c142030490004e90310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 603627122 1250 603625872 603625879
    0xc0801151a0a050316090e0c0a1e020d1112070507030605010501030902100e01020703060c02030903070519050d0f080a030218120c0f0a030507060905100912030c051501030302010f0b 80
    0x501e50345500080c43e80c8402030101810409050103030240e0743c403d603405001081c544502544030305040700c98004d00c3e80315410000006080600c0071310024103828001d0419112038005002410340800d0a0300c2c41d08041203920700364041d0301c4032003180d040c04034001c0034110704c1200600300b12070441c0351200888030f060300654101454641100b00586032010000c150300c3e001e04040f1050503900004030302d004901c0e040100076505117050981c0c841d400001521034208100c054804d065100e07400d01c0600110050210b10141c2000d1007000300e800c2c404031a06100f40aa80703040310526807521001c2607944503041c0500042d50004184d0140201c1054040501c0811144101400003c00d5941d9403141c000031414890b080c60304107022203a858040c0c0000445c0d00c60195400b561707540d0300140c4402c49512943d07004001040007840c00e940b10b10041002e80b01d0811031098003032079640b400c640c480c50071a0125150711594030003602c10460141903600851081d030001c40c03079140d507080d00001d41e149015460700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 603628372 1250 603627122 603627127
    0x30f0901120209060706021b1218150403111504060f091d04080306030c1305010303170103030504150306121b0f060e04020306010513121703130f0c0801151a 69
    0x14965078000c02c441c501c0ea040701c000762302c898a030024449103940c0c668509645104241ca41c4082c1184100a000a0064002a014850100f20601c0000e064002861449010030881400011401c0c0d81c81103c0240c0034000041003900f0141d640c681d0351140e08004040381041421824484e48030709510b020303000150b00494524150f03800c07951800030290004001340c83c00b0000074000d4808104109440000404891400f0605002100202001e000550014030701c2c40780c40b2140000e050074a03049961561300e084c6400c1c5400380308203944400300c01400401d9183e1038000341200c00c000c0d040d0080e9000d0342d00c60a040b04440a4016280069809603e480c4030150042107100c0e00880c400c0030f0703424242da01603941c3d654800102d4492081c803406d1103008903401000f2504500d80603805203028481c83c4405070340e2040d03007a9500c150004942441100c0c0d120740e41d010000d801d149103d00920b11901d2540441625000e415080d6003141d00082c5103408010700401c0300b040703020031120111200d4a000c43c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 603629622 1250 603628372 603628387
    0x207030306172d1b0f0d0807060612020904060507090e0f16030c14030426030702060a060509041e05060c0a180605070305130f060f120c02061314030f09011202 70
    0x81e2903143d000c41c004483d82c04200741c1e031038645406000c001490340041506c01c0c50906403070900c120b80c10544d001c0c0c4030b0790720309000483c9110f01407000c941c81d1600140320300e00a58071569403c1c00b91800800c0d000c2044140500045c0462881c0740086c040c040d00d400c1d82c4d881d1726001003010030b2055000d08090406050181c20030200d5082103c0c43d4120a46044041d0380b641e542c01d0100d00c0807811041160843c20711520b06400c1304000000e03501809071075090720502c0d188c00e650401035404501a05500c00000008140003d100800f40303820000c46540448000019840342810f210301102d01400c283d00c000703100080e1a0b40021011444090000c8284400d420315100802d82e004815005040c00000540c581003a031600e50210014404100c17a188542c1e01e80d200149842040c01d400381c04125120f10100c0d502115000c0c940302021603900401c0305030b0380d02c61210300c6400d014209454103e10f2004014050005000601d1038801240615a40ea28003200042c09594100020780102d8030600c00017 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 603630872 1250 603629622 603629713
    0x4020f0a06050d020a03090206160203060a0e19050f0607020c10020109081e07060c0207060305011205060c0d060f15180b041211090f09061612020703030617 69
    0x542000d00e64003070040e15910940406c0d00109003030f00d801380d07102c040400c11010380a801001006524820781c203442058842d015a0800d94030309604100160f0480481000c1c0c1e030500b2212a542c0a000324221000c503960111000d041c07100075245040160448075280c6420704010b03210b45180c850742e10003008001c030703291901c01c9507018221740039500c0c844a60b80c0030302c205038620540f01401c0d0001410007010f90000406503582c401403240c3d5008c02d00300400028615501e4410203607040e001009061141e032100043d034216840f00385445402e0781d55020104600c40410a420060074655004039151a04490b001e85440307103500352044288440c1506010440b1508107071402ca614100d00d40d0b00d83c0010780380001004080c0034809802c03450080030130801c00f01d1281240c0c01200e96401751149070b11080d02145200c02ca8940c00da0104425404e5075940d112280d000f840d00c4d50080c60000340140d01c51004122003901c94103a07a40540c01349400c2c52000984e2241110501c1030900304d5006107041825a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 603632122 1250 603630872 603630877
    0x80a0807110a03021f0206131e080d150e06060310060c0302150a0f1406060403030e0406050d0f0b06040506130504140d05041d01030c180b04110304020f0a0605 70
    0x820121003010000420b46031040078002956000f0a0108400440c80080c148441d14196410051060002040b2114007182c100201d150700700b0201c64010283c40c060b00c0007440c00e440103c07807013001084540480030107441152020080c070b4a0643e8960302c0c0260440f4100c3d000f03018107115110130001e00c024041c3e8801c085003201c0c2c550400760281e20160400340c4c00c0050351090308401081a10400040d44059406a01c12501d40c0301c0420180c0c607151031200301d10354110f82070764100d54100300034070100e4060b849100003948020030120384284c6072000b09d01c0f00211030800b222420a079095400070000402340c8560300081c165002c0109207061000202000c01c4003401e644041d80c4c8602080902030520048c4d190031040504441c29140c1e2190001c2c001c0d13200d441441604c4120030041c5911195050a00d0304907504800c0a00e113072400d10103070300d0603143e41001d094401661140c0100c401e894900440c2401400700500795100c2c507007801401032401070583d100c0d124060a00c828070070190460103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 603633372 1250 603632122 603632137
    0x8040605040905010b0c2d0a2315070c140d0206060108090610030f031112031801060e06061b0601030c1a07021032030106110303090a12051210060306080a08 69
    0xe06881502d400307c0d4040340b0003e501c001e01200d001d101c09010501c203801811030001003945010324200302002040a80700c240b1402c10341c902c2d007209400b00d035003180f240b620a10128041c500311008400c088030040e140c0705683d00c1050151704483c0800c9159030b0403000c02580300019201034441c5181003100b8621034080303030000604221014240c1024107225100148042d1403c00031520002a01e031000b6840303030000c0790302c0d0b05c6c806041c0061001480044c000d04c002c039040300c1c0b44042c41c0d45801c4100f02a40e081104124400041010010b40f0b4150810185000b10b005105851840741429409217008036035058140e4181d10410024005803030b548003c0c000004203140020174400b111103c03108003452144141a103d4030040342800862400700154120790145c0c0704c2c0211010007204081c5c07240000c581140702500404502383c086a0600301c043e07103841030f03441d01d0780c03034200c0308140500110020350301c6c82e001054a810901016405203e10380180590074020808510180c1d03400c411442240e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 603634622 1250 603633372 603633403
    0xf1404050a020f03040c0e0a060e0408090d1a0114180a2d0b090a050601050d050c0f032a041a130b0f0c0706080709140a0308040605040905010b0c 64
    0x100403940c1d0b03506580901c0729940d0001c0d581d0400703007003041c403860303c074003600904030b1158000c5000000d00c1d00c11001100e0030105918a00c1d5034584036422284c0014a513250030154010b07000000402c032601c00362003038000b9600d0079415410403049045840c4040d1585000d000340703444500c1150900c0e0009684214440b40100f181800030385824550454035501c0078074014110b40c03c400d41880c0350488490750000f07031a4001c440d0b0340d1305020700a4074001d5800a012034401c10a5030f80275130b01c941003945d20414001d5074030700e0041e00c04020b07807030b0707900854580e030400400289c4c030b0429500c46000c640404484044041c241403e1000c20f5034a010390b03c085071609013000441038011a80b0882d103800034070107885829100c8076510103413201c41e44049483d1640780a41c801c040340240c01640c0c40c1d4045d20b256503800c5100c504081e8401c01000441c0c40503548488032540001c0004c179544010005080150344990701c89240002c01002d0b2001a00400c0d071405041c0210a94143e0021f0103003070601c043c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 603635872 1250 603634622 603634631
    0x110435330f190b04060f140a0e041407030b070816020c0f210a032d08070c03030b0a03050f011d0c04110706020301030602030105100e030a02091504020d0b01090f1404 73
    0x1c2221009202c40158903801a0410400140120780104421300b01e0744e0039041028811f42030340400ca2074080c940141c1c000e60361844c0108010072a6020000034104020045982e05622501e961381c0c2e2040071980080015200400c000d9070300e820001648101c6410b0008003000119580000c1950111880e8940951000d5a58600d403000409002ea0304800040c107442010765903060050002240c0e6030581518021000c0100b0403401c0b03620007811a00290303030b5142e056100c1a1040b00d4807440c42d44c083c5c0806843d040381c10010790300c0161400007903100b0030040c5000a20b2501d81e500351101003c0012401c031140c000b8802e0803002048081060000b1580010004076040088105000303056014003082c0c80400040104426540110b040c2c0b001101c5041629415603030480382560003551150701600540310000050400d00c0d5582d800c0b0440500b000005280344022038102e80001c1c2410000d29141d8445a1881d40c00c048500d000d0b2004400703002505003802d441101090015a6542c0034036030f04e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 603637122 1250 603635872 603635911
    0x160e010e190e010803180109060804020d020a1508091608070e09151f05040203190f1e09060b01050304020a15020c1005030604110435330f 61
    0x12030707800c001e050510004000d81d40c541400c0c981d6038210803501c0001c582e94058512880d80168010310485025503074601c41c1d5900c1c0d50a02c2030807640c142d022a0403907000100480d0201c0800c2c00c4c4103541260ba9608451440d201062a02c1d107039001c507604800340400d9000b48069a408104102034801c0c840c4146803603210880154036254481c00702034042590002480311000e00015905407030310761403c1c000780c415214820041240310584071a0000b2071130045050311030b407050300000b10401c00c44e1000501c0b0140c6484504081002c252a01381e05030ba20107403101049058400c01080c01d0080c41c00c681145410760111b507036640c0c035000341e41d80d2400600032104661b00c00c014411035080007900720481891a8100503186400035140d0f984290300389002d400300860840b00780d404039418000001412005031181c02c202480d07403c40b6801c4079034514222412000b0403c40082155007032003003600031036440c00e001e5070488041031480340c03021070078410301c0a10702c200c400c0e4603000b203415003034450078030b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 603638372 1250 603637122 603637159
    0x50a080123060f0d0c02060a0c1707030c110d03141e042307090203072316030225061e020c04110909040b091209090109020f0c0304030605160e010e 65
    0x20000814013203130503c0c9810014580c0491080c0c0511050070b000c2c04400602c1d14142d0b16040e110107042d0a100000c00003440440c803d0b00462406003c81c00c040032038040c0c400c045400c01246105000120b03480d03071004072403420a40ea03490384c0443c0c104040d07001d48904a16400301010090300241030080b002141c0540f0780b10b2810f8149130307061100d00701c544541da02c0607028080e4000b200e8050104410b4484004c0d00703580c4030b0a0302101010760000602c0c021300b968256220380952103064085111740c5503050148a600c03203c901c83d040c2c0010803070f0150341c64100000d2511030104801c01e0244c0c045000460040e40000e1210041c030f40441d0040741300018802c01d020503014941190303600420400138070080c010340c1c401e03050089491a003690084401141f02c0c01c02842008099500300c08085c6c01000f04c008150702620400403140941850208203204451440c0c01a400c1614890b03507034000d0112000c5000041001808542025140311000c100003902c0540c82d40ea1060240e100c10700340e9054802c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 603639622 1250 603638372 603638377
    0x905240c12210901090210200304090e010b0105040b120402011e0903030201061d0118020906070302070f091811011b142104140301060902030403050a080123060f 71
    0x20180051a00c0d441801c048007140c001c820032014080c2c0c0c00e40c01080030301e241030107801e04543d0058814144030120190840722811107804886030090006101c20401c007082c001480203040e04100426907140056240f42190f481d1028541845010401040941400c600780d95103015260600a400d0f0340d00c2c0010394140c42d03682c441d500407e92142d01007000c07641052403001a01c0c000e50081000b5901c41d0029040501c648206910100010004005088600c02980040301034020098181003070200858000d8001e0325007100944c100290034000300d0b01c910303e07510080c030300c1c0d480502c502e102e100d00d17002095a2110005d0702d10300320152841e00c181d0240c6020111546114421151410507060083c1c0c07006860010200d01c4c0541d08a084900000700c409100401c9143da03c18645450003142512410341e0031030443d003554a03111300141824451000d54071541c001c0d180e00d6512200000700070120310051300244001e44000c2c1a01d814050780e54850380700e0741c105851041d514209407406003c1c50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 603640872 1250 603639622 603639643
    0x4050414182b030f02030a0e0f0c0105070807110d03020a1a0103020a090e1501091d010e03090d1410020a0f230d0207021e03191707060f050114010905240c 68
    0x2074000400d010061009901100c090020103043c2c50030034456170f284079118580c0c0748ac420300103282840b524021500b088010882180f090f000c1e545120b01c00303000324070302041621080e00541c01400390306051240325172484070382d5032800000c0d280e1981164000751050600b806000251035607180784405003042001a0311503540c42140901c070540e5501c042c0009081e12000268803001d4220b00c0f648005014020700503030003019405181005040d03805d000418801010940f400e8960b8440c0d15051a001d01120312664500c00001d41d0f5810f07108000f403d0703842022908001c02246400c1d4071416400c81c003400f6880036800000607075484201c4011806802400406588080010301d15407106800a01951403000140c05a500c014101e04d9030f10000030107000040c1515890300060b814107100d41006045992003800d00091840702d90902e80102c4a00340c01105c041400302c100c9000700d40e0414100c000811084801d4541800d102c041100c46940c011014140400301060380d0340e416070284a0a0901c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 603642122 1250 603640872 603640901
    0x1080109050414011a0118050a030b0601170708070e0d02131d010e011a0d150f0f020c07080609030a02071e1d06040b060403021008090304050414182b03 67
    0x82c0c1c86190b2952102200040300170780441c10340880b5204d0034500c1e051200460700010b0042140740d256440e4407000c0b500c0100039a041040070300c0c9100c7c1d1524201a15030080b68140d945440c980341a4102a2450310011340c49480341d01c4044200d17006968208070b82c0c90740f4080c00001305450040806481c5041d10703040b00c42000d9402e0550300c02c21034405601103804144c08071024003213803201005001c004594036402506941100501c140440226041402c0e456005500011028002d010200407a00015081c3d80b064108660400c03046c0020000c0c20382200b80c51004e94a0300040c64806561092980328692100c22850f0301c800441c152008201c00801c806002d4103c0b21100d40c8030a80310000494041d4071507454036520452508244060300c051704c0e400b4003003034449040141d003a180400300404070400c5101c108000325640d15a40654000441840c81118072818000c210284815128552503d550301c404000c85c645c2403e801010030020400c110390070340404040007200641011a0408070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 603643372 1250 603642122 603642131
    0x7060f06092a02070b0429030115110a060603060507080601140a0e03030903031309231906241722030c0501020f071505060a090e0f0f0c01110c0108010905041401 71
    0x800c1345032076503224030540280b1f0058103c00740d00c2541e008980802c6c002c12402100c15007a45c02c0742c60281b209a01d69540002c01c680210b1a59030356602507031301ca0341003280c500380c6440c18010740d540c1190406821075401d0174882000d261134101100b01d07001e1200c0380310401107950020f41d02500c081c02240c80050018054a949030740e10b41c0c103106901080c2c403480c00028070b81600200c1101c0000101c90442c0303013441c0c40320050b444002c4003079440040001e105250680ea940c0c0000c0d0607244c05086200004442d10301883c2307000000b0040c1200c10001d2007648400c2440c0100810140c0d1707080800c210051540c6c0b220411b0403d801c04850080142c4402403031584001609200c402c2240082c00c6002c0c42900c101101c9540c8003020000c5c0d6074140c6044e60070a07440c0100703000c10f11003071b000301d80001034841c100e541134100e14841906d050255080d08034550000040b030344003568014114414451108000c2c0b803500080b400080c80000144a03504a0a5860010504100c2e2410703a042e0402c849100900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 603644622 1250 603643372 603643379
    0xb0313021309050d0f05040302030307111903031e080402060a05070302150127020c1e0a0503040b12160e063f0702011514041107060f06092a02070b04 66
    0x4c2e6108403030824000451185a05c400c0300d18417540440d030a0300d40c040c014606280540e80d071515511030a0100d142c0c00a0304a8207014581c8214280f10b000358041c0d510000320f202c10a80c10800340218020740810130103000100805a2190000c90300411641d1034120398a0881d810101c0c109002c2039600000002d01500018008582c0303d04096044d482a0b00c1001d04a84002408103e101d0026600c03110f40041149840c401c4965510869840e41041500e07029400c41d40e503207003180d000e0740082c400a080819442e03080704408011035401102510700406160070040c01822907207800d0003140c4500000aa2007003034800088101e1b104884100c081c6420818442c100c10761000007480c80500c085201000640c050b0cc1405980d0f0300b100c0c409010081f042c1020030080384c000032a44d40da50841c0e10380315156070501d000300c000c16095018040000340c0d0b20b40000010140e8070b040d80140d07500f6040030421000b2420b10401e8003c50026042d01107002030910100340e04080c00c5920005141d0350105002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 603645872 1250 603644622 603644633
    0xb090105101409070f0915090e01060c030507061119020303040203060c04150c0501090b0c0d0f020f0f1308071710050112120e0301060f0312090b0313021309 69
    0x14001d20341042158541521108290801d419400e24181d015581201080580380100304d01c0701d8074405450310907402501c3e002600314418800c401180082c404a80401046444010040c0901001d2901076200e0600b610010114020400b01403c1c86680f5540c07822041200c1040f0340240080140e81000d40d02c00303100280d1281c00449085c0d00901034500082d00064018080f03400340d0315142418101d051000d1030032280581c09288c12980380d9079502d803641c04a280d5624051160022188580e036440d82c81e0f0340307a4161075070120310101241c0180072008540d02e01400780d40a88040b04004d540307a6585221041c5060060b41c0038a00c2c9014070603005c00d20403010081040010a00e0049400350001d8055400c100c0d0024895000c41d5040c041844002a0402c0040412500300345403000c000c2c1d0f140b80000707084800c96840226a041603003001c204019030690b4a070904030325420912401031801032940c0b40c5100080641d00110b500001c5c02045684807001480c40318403031002080070325070702d00d081d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 603647122 1250 603645872 603645881
    0x506090f2701290d2f0406140310020c06060d1a0a05071407020f01050702011112030103060f021201050f0402300919030e0a030803040f110613140303070b0901 70
    0x1c500180044405620300c0c11300c00c51075080a98031940f203854980410005d101307440c13280d18449101d00824140a2810307035440c01404050309106040d40407003030307050040500d00b92606030b81d144424010b00c840b1b1710382840400c0b0140d000744240d41070450348080749002c0c8450b083c0b00f1103d043c43c5a6103028880490503680c0024402d000300e0b01c0380090405965210742103400b031004000d5120b130121642c000305500c5a0041c2000d20720604000000f9654481c24500340700d000000e2200056010004000307000041c01600b6001c8610700782107251603180007d406140005006150144442001000c07140d2202d90440740040d45898010b008410140275441c8922521041c40342c1149020707011444034903001c10709c802d40110096940342d1081080e941546c49204888945900000c0d00c003001020032034010007140b00d00d1055081d510042800e190048a208000200f2801003030203011083d40e00d02182c050702c01380c0d00131101c0d1001158000000a10314420040002e281e46c200c1c030144441c40105411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 603648372 1250 603647122 603647171
    0xf04020d020609190e070908120d02040e010303110c0f030d0f120606030203061206070c060e0304090504060906150b090112023c030615030a1b020a060506090f2701 72
    0x5e01c840da1340301c041c401c40b00d80d50030740545442600b081450b00175001c1c10000822030a140c0c000050700b440c1e80d40400340c00c801c4099000740d002c12100c0d00320b0b1503100c506100c0703248a04004c4034910180300d081c40102c1e0740e4104484021007480042e070546000c09000c3d0b0f074800925074640d8410702c0b01548440c0c008001c0e404c2030341c0c068001d50740e0b01e20b41c44c207000c80810894400c41090392042c4030300103d5180c50300500102124103d0b5800700b080f000c5003888590203400c0c0728030301505011030171507041d103003031003c0382e440c0020000e41c40304901041c01000340c00c8086411604003480c0070a0301d0495002484001d108000c00e01030400142a20030201b0589042200c000c7c0b080b21600840c0c1d001c00b203407010041d03c421140c8550225580d0788840c1d641c024032010b03640002600780000748a00e090240d8286a07162000c00d000941d0065544000b00030141c010b40b0761181c41a00c100109041098100d8038108003c2c0802c0c0c0120183c265104441da10404041c11602c0204020b10481c101c04100503451a038685 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 603649622 1250 603648372 603648389
    0xc050d140616662102030f09040f05040f03090f060e010f0315060305060f031902042f0304110316030809060f041502060108060f04020d02060919 64
    0x4003801c4050b0000d00c9042c004402c200720f20210704654241030300d061440703500d240b81030103040c0a60360502d00040a10251030414610702d40400c1640c0e0600c40720401c00f14a0f6800895401a1501030307865000c000d80d880007503064401c5448400c07110005028000c80c04c820550329180c2010402401080000071103014003c1d02d07542000d0340c46403440b50b00341e1114052280410118001c2120302c0d4407a100011001c581792034001250f40243c060341d40304141690007640020b8a400506c00389107411213103607019000032402052150320340812075603926031007103000c0e2140f65910b1070390390b19191205d0180c8203913000b1154040100c041103d8151540c000b6a400c2e5080351080300110800e00307001450b10114501114901030446c0b569403070a100e80d000f2b2400c0c40e00500c0c24015060310b151740c0300240c400350020b080d802e94803640f00c050007032400005034081c201342d0788001d040c4461403800d426402c0d0881d40650300ca40c3c10700158004039541e44a40401d0319080401c07202404102642d460000c0c040d0760995 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 603650872 1250 603649622 603649637
    0x70b04111002060f10030501050a060603060506090a0b030a020f030f0403020601060c02031507050c031305090f0709090b0105043c0b040e100506070b040c0e040c050d140616 76
    0x4500348904101c64825880c0540e0001c000b040c840044000b00700d41c84141e00450481140d03c941e2440d095880a442c00e6107001d4403100700740401038141c02404050301c82a200d49003001a03140029502001502c030300e03003800c10f000010640540359030b0100d80c03100c140c2500050303503402c00c841d111a94240466096005005120000c11800d00c80c8200c4020650010b00424085a040b00304400b00540078241c48c040c80000c11100c04420700c24006004400785500c2238202043c6003806001c41900c0042070382981c2e40004003000315443e040398540d402d9803011a0300080148003000147d4042c400c81c0c22580449100c98001594000307a4003d40141480c01f0460b010a020003034012800140c990180c030908040c2404113010004e200480c440d441118801410300080e60b91022513080d510071103055500301c24050800045c0030580b14480002d20703202c282c0251514280d00c845c80c0b5460103010b814401d0390450300620610080c641a03803010340d00c41e02561142e00f460903031240360840c1111136a02081c03e8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 603652122 1250 603650872 603650903
    0x9020a0b030f0c040b040e061311040914010503280f060504143403081209060f040503040509070c140615010e0607030c030909050a050109050903090a05100309050102070b04 76
    0x200b2090b036003217400c2041c0c91810142464030707000c91000021310720354014440200e88101380070280907210217001c18904d4143d645040c0041a03041d50707060038455418600700c000400050310000355a51805242810001d080843c1424081e000c460a10000c0c10700420310116805000041d80054080c40c41071080c10641007907881060380710344520054011220004000d4107441e900c5003d040360b01404040e007a50740076225661034140e5008404c10642951403030381000308842c4200071054000c1c17000207824841303161558031a070341e920580c020103000740d0400c404140303403501030500280c0d1180d01030b1f030f85400d16403100384c1c06545840c201c920450f07881c0702400310b072441d5010b020b0507018074102501c05450820540c8040c0e5008280707031012802c01000120002d1400c01c1446020b00502000300c1c0480c1e1945006008410380300c024110789000d0700100a032035105d0380c81400704001c0305c0064801c60300704400c803203042d00185003044c4007400c2ca500000d043c5c402c011003030100c10f00c214410325101d40700c41d18 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 603653372 1250 603652122 603652141
    0x1802042606010501031128180b221205010b040501060e0609060c0f03072001050a201207030903120801050904060b0301112a060c0d020d09020a0b030f 66
    0xd100015940c150007000c01807000754400d8100d481114101403003a85494040d43c1c500c0f4001022904201250f0803110b55400b5859009907281b51a0349001c50750170582e0305211030514141308510b500d90300c4103904220b1800820301029000010103061801465100b52070034403a000c3c00da9400c0451040d0302e00b01c0040f401d580141d0f071105010758007902550420700c800b01400b845910800ba820310354400c08681d14043c1070100024a1030394450303802e040c0309401003a1419801d004031074100d0305002c001c1c05040c600c80d9010b00e1000046c801d5001e280c0c240790000000604080b10520700101d48940001d21400340760f0400420411a8460500c1200202c015401194801000e001d40d6a2019015020034041070b0150006071030803c4c001c000084d0f44a0b00d0800d03802507404490194410103050b00c821030b5802d0490580c00880c0705c0200505602e10305054607903072500c114405081850350104500040c9034156021000559002e170800310344e01d807100c600e90b2032508100c403080c0c46920700c1000076520300e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 603654622 1250 603653372 603653429
    0xb0334020706090803180a0f03080705010501060516150615050a140304021f02011103040b06030d170a09050a0501020706060f0f0e060103090819091802090901120804180204 76
    0x4c01c10300141d4107011803010f041401c0c0d10b00707a01e0b00c1d030311103884940031030828581c01c00203000350701c50340c0143d0341d92140d49011070940d14140d1021041c040c0030320807410b0359480c09101003521a070040000c0740d000d001045107002048517401508014100c0300c604500315030800001c0c4a0390400703881c0c3d607041600c12211020148411a0025081410030044000d0200d203205600160f8415000101c1c00080510003091141c0080380c06543d9030300c05105010643c141400350803400d044a00d0442401e541098050b8400d01c4054000d00040e81d4a541c10707400c0c0079003840b8003000aa8010000d5543e250282045006802180101c0b40c03080031421000514031550301c0603038116200c001c60801d0340d54036000150018524100309840343c07041003003034625000c5128028460081503494450940d41080041d24410400105407005075204201620490742c600c4101811078003e03200d010040d0641d884c2428050242d07078048085401c10100180b24900c950300030f0010348001c031241d81ea12880e105100001e41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 603655872 1250 603654622 603654629
    0x5090f071a07050715090e010e040b01030813051e311a040f050702190206030103060509011803031406091608041106040603150f0e010b033402070609 66
    0x1180c81c5038110211046501a140280c000c2e801e0b03843c190780d40c01c58101c1240384c0c0b031100c2e000201c014100f4481c0c20600c6d000307640503103400d80794804145043e43d00c0001800e410b0002604804c40411807040e8026a11140070280001404410807a030100e503640036800c59804200b4400c0000c9401c00e90011703040f0301c00c040098402c0005c21440304030071000c90010b0200002000025502410060b5580c030f9601411048a1207034000051900d0300400c0281003210485070420b41c0010711210201695a84064a05494009200240c0d50300c4810800d4010f1400c005c0c80700c3c0c00e400c02401201170503003540c07101c82ca0080e41c94101015644071001c000902c4400c54802c0106000700048215481c400e6400c00d901601c6100e00d8602c00083c0000211690003d500c21030003c1c0d02c4091081d442c2c048801502d00500902281e035007440d041c120045080034050280640f000d101100061a007280b100c00481c000c2a51040e00c11089001f040c900d52a2060601d2400035200f42e000c00140103101d40b045601305c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 603657122 1250 603655872 603655889
    0x30a0b010201020901021e1905060702070603060b0d050618010b12090105062805030615031e0a02010f0c06090803040201170103050c2701092003061c08070c0905090f07 74
    0x41f1340e00f4009003400039401091f84520701c143c500c911100c8030a0414110228040d0005103110302e040000286801c445030000380c10141405820860344464400703981079021042c2010500c2d07610400410018818140341d00d0100d10750400001d0b5011032940103244880711031070240c8507030791041005401d0303c1d41034500c0750f0002e010000740014032200d02c0305120031010910301d890010340e94400092400c036080c0c41c80d0361802c4250b11840c400345001c00c64800d04142901025969000c4a035090b40ca1300079800c0b0203030600c2000c0c008000305501c2002207101641c0c0c840d03400c008410300c0d8181320200b500210ba04a01107088001441400f888522070941225130150040c84110800001c2c0b10700104200b60220301584030a00749524500c04280050291074011400034004070701c6d02a40024920b10180c0a600171420814020940c07980031805640b9440c05808484946d0300d1301d0b01c142c0d140704c2d0070009800d02da800000801c070800207400c05400b420120080f14291a01e00d0303502da464103500c1c481c4400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 603658372 1250 603657122 603657133
    0x13180c120903020c030a03020303070f0e030a031b05190c141e010c0209090d0905060a02061f080105090706030609020f180f0a0305030301240e010c0c0803040b030a0b01020102090102 80
    0xc085a03801114569101c0c1c4140e91100000001117803500410810483c00358001004101460364400750f0001004102e240c0b148030010701401190301d0304075008000e010044034000c505107011004503e5800c040c1d04c00c0490301070441c0d280700002084200e0f90101c54006121100240726103d5961220b0f0a410042a00086000141d40f400c001018cc22540e41446030000c40b000150340c0d8002031911800c00301d40a40416480443c0c01032284045400141c411201071108442c5039600050b0325a01000707a50464042460044020786d1440003580644190b600700b40810074818004240308048620645080c000c803511a804d403404d80c0611001d01c8802c0302c003030103690841085501d5900c00001c000d40300c0182141000d01140c5803d130560800e48544e8800030040040a2822281d2490f04250040e40e500160540d10010040d00c0913400c02c0c0d04000c2d07004018405e00c41c2d0b0050f4800104094011a583c42d5580c5840c0c034200d4200729105162140340803201d02e00c0c0d5006008a4260303040c143e0103440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 603659622 1250 603658372 603658397
    0xa060f0f020c0409060603060501050312071202030403061e050a020a0e0402090628080603070f0303082806032a0b2d07120309030503191113180c 64
    0x9410048a40c601400c600c150341448076035031a40e02c940401c0d90300a00002c902941141809415100d040c1e02c0980250300500d0411510200c0100341e545c0340ea805000c01c074482c1c480e02004c81c518040d6410180c02685441d0040d1410f490711348203441100360798a001d2103140e4805074003404070300400b51a40c01080c0312000c1d01c0c03402e24103a4018141c07908000e09150514cc40385c1c1004940301d20300040c1c0914030240d44203081007590450b0090f42d01040840080c1201803c0018954402d22036200c0101031104541c00f18a03010320101c41d04091404290340520100340c0c59400f00080e00a5100c1079455504005507104009000c90280c0c40c4241880d0754010028a041c060240c1540300801400f00700c80414180c0c0700018451900018440b44145d46a03100c008604050000d40c1e1f400310000c00781031510802c2400680c10401b600da100c2c0710001d10310381e8000b5207150603020341480e41031030220b41d00c00100c2511180c1303070059020a848019503540c1c8960044800700d0125a22040240042124080610b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 603660872 1250 603659622 603659627
    0x3030b010206160e041b050a0801090204050f010c15050405160503030705030a0f11030c010903030e010b0a031203180c0e0f0c03010308071713080d0309110d1b030605040b060a060f 79
    0x310141074005d80006030341166005004c540e11000780c0d08500049002403180152a0320019090241410240452030075142c2000101d40380766240180d07040c002554010010f1040044c1c0268200e260f00ca0180101d140518040741c83c2c01d45003025464900300d500010450782000001d0b078030745961040003035180c984440001d5540e00c5003140f4a0f01001071040d445c441c2040700340f000d4041d24521034004a4104075925020301620dd42c4041108160725181d0360344125582c0d0481281100e8005540c01400300340303841c0440c050030741c100d020014003800c4048502040030524161048800b161004101034803a0540440405029228082034010504c01480413512000007860940d1145403415000d08815081c4c10140e0840078084030b003c040f000742000030311028030800451b2215441d003000f40f01c0042e9102d00ca014003902009014003d4210b841c030402c000300e800c0c0c0c070140c890361828003207040e0b51b85003410260408403001c44511400303001140072402c145c242c1c00181d56803500d502d0041000075004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 603662122 1250 603660872 603660887
    0x15020d17090f03040905060a0b0a020316021201060b2a0d0e040f0f050405120f070b060f0d0f050f06041502030703060f080c0a0803040b0f0708041d0403030b01020616 73
    0xe04418000c0c00c041c1c68082c0c0c0104002e00052050131004520f62400c1010014406c40b55130007042040c20402c0380d030003665408400c03a100c404001c00e45010201a80c000320300050402c0008100544c80c00030003017004925140506842303101c80e4120882d9002076152035070080c0c05015000010f500c10700f080b0604c00d000c1c43d01c002d981a4042c00000c0c40090340741c191f07000e4901e41076400800f243d8030310900c0180700084c010340381c0d420462403005140514002401c800f078840d02d0401741c00301025601260141d500d040480071440341c0207009140c12143d9007801d40c102c0104000c1152103120740015003001d17050208a0b0740c411070304401003c82640320300807200c02a5000905440425540300008260600e01c084d100c005441d8043c01048000e0600b414845880480e412800c01c0368000c1c00100849241002280c40e0040c0c280d45031a1601c08503e01003680d4050350700551650022554a008841100211180700d5806a41c06024028481c001642c442c64180c800da00102c0080c103144602c10b005841 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 603663372 1250 603662122 603662131
    0x702030a0201110c030703031e170123060f030121020a0b0c03130b04060908060c04060f0207080d0503150d0b0f09121207080610120506010c060f0615020d17 69
    0x54030103000c1340100183c02e04d02a074004038040340c000046001340c480580e420014445141c244010768940b40b09031000344550500c0b5070100042d03188582c086000300d0041030100741c0000307030031580c40d98400050341016400c240030f811660f0000b8490320f6103500c8a0301c051920180c0241440405505188200c0341590004031295403d03c820441d42c814241310200c020001c00404450366119424050000c10810b0f6623841106558040014000103400c10000c95007150864100452082820442a03042101c29400a0000d00502c8000402c041c0c00800441c45540d4400c010600404a242045003400d900034014014124130000114500b02d04ca407060780020f900300465244006401c040203207a07004505034001c1905080c1408a9603403c1b80701d041c0c02c600304558840042c101d6440007012020740201424000b42c0340c00100c0e00e182d0041c95800d0b003541e00610140030840b078000340c00022b0f214901c900d14900c0a00c80946840b04e02c049048a03140c111517880f2003d00c585504008071100000c3d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 603664622 1250 603663372 603663407
    0x3190204240809070e1602011119031503050d1d060a17090705130504060605101d091e0405120a08090c010f080f09010b030709060810020702030a0201 66
    0x10941c2019011541c007084028400c0040c44002468000e01012014082d40e03000d0384802c605010920308010410b91080d80d0086a0703403080786100049001d0500908190454400011404024500c0c06284091204652001e0ac4041d050501d170a401c4880e83c48040c0440d000b40c8138080040340304144800d140c0e01040c1e0303c00303020700000000072265030024180c1004500b0790020040d88081c0084840e501811100c06028150700e0311010038076210302d00394007010456131a40064100400b0b5070010000d46405404052070200d000340141c25203154648107100c150b40f00a07006105d142c80711101c0c1c0324000010b003411075107044441c5a0b1224001400442e42c500881000341c12410024001d4800703c0d60700d503910b4480d814005003007814011140349080c100000800021307040da40000140b6000403482c00d00100c581e6403040d43d98010991451860360500078400c00003080d6046401c100142c0f40c007a01a07501c10805101c18004034407400c580217415403c0000070b60003542c0a0030021003500c8256 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 603665872 1250 603664622 603664627
    0x15150109030b0a06050112090803161b0c0e0a0b151605011103011502070b0306060a17040b0901060902070510180c230108040c0e070507080414091b031902 68
    0x307580d0500402070450300030050781d6031340c0d804001d0356074010f1403a02c1c102030740e2004014030b0b54203032203000c95484020540012100050b000048251040251805212994100c0f07070802540307142c803581c1c4005a2003940c1e40200d0030400b060314103030349210b18903800300028601160f08001e05002e000030b0308a0100400342c031210001102c0812000e00500d450308481c0d62a0580d20341c10101130058030300d8203009070011503105000500c40320300240b08490700b000045400300e0311080c413200100c0328003100302d10320b484c0b00641d003090204019034100c0040c000c2c2d1480d0028400f0680b1075549204a00803954007403c0fa07400081d40414400440e44100079412101c0801c110340b082a45611200100c0d40d03112480507614100401e0081c102040140c070a1902443e0407001c0341090344410001d10f005000701a241810310011400140c01881103402c01d943c8441059101c655501c81c908817100206650f5020b103030b07441c0010380038914600084545062130241c2500307584030000042101e001184885104c076508 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 603667122 1250 603665872 603665879
    0x12060a0b1602090c1305010e0112060e010f0b13060320070615081504120e030d020307020307090209060702091909050321010308030f060a090e0616111b040b040203101715150109 78
    0xaea001e10805800100c8441d150781d40350030b108410080c000e40c0703c220344480a120b45440702d06450107083c2102d105240c0820300b18000c0c3c1c114084c85004940301d0325103500026640e403c01440d0b40001c098900c10117030300d52480347d849800716180c0b40e00d4040041100502c900040005418201103013550300103103070140d940765405011070328011710b4a0100c40035900104040381140350800405000d40040481982450008004207815000f1004020310444d85c01c0c0005420714040783c2002140e0f44401d40131701421010f030071321a40721780c072403051041000200e00b04025018400724032241200d921103040751840e139a0181603040c595020317000a81c018100f040009040540380105660b500c2200090400c40c00e00c45030340c03688054a00e004006206541540210300500840c09040030300041060707064200118001800400880c1c02841e400342c0f000c000d006c0c0701c1c4021070200c0159180c010074006029074903460150340c2e411324000300d14241116400520500136405000311805010705250782501d03103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 603668372 1250 603667122 603667157
    0x90d14070c260319030e1203011d090102181009150807080a0507020309150d110405120f0307020f0d06050702011a1512060a0b1602090c1305010e01 65
    0x85610049011100e5402c51001c0d8508450880d280e542240065140038007910240f00f1181a841c048400d042c1d403400408031440051181118240c03a81d4020340e503a6860b403a0381d8006400030400c44003500c0c440000944a0350051080794030041d1310903100c1f52109034500030890722550795001d602c2000800d080020358000f6107800310201c900070703440d0003085190500c0010311501c4014404d200a0342000d0a00801a402000b2945203180a803020f5041c05a91009090244a02010a90118500410306440e845150060419124102c0702038810354195201190f5071105007000b203d03540c1041211000620303146001d0340b561000540030b086c00c0b40b80b036200c91046400866401c40540d44078032441c2400281403030070891440c01141c000f1024240c001d0f0307015081c002c00240e040c1a881200c0880c0896642c20550401042c1d0100141e94541103000d20045515035010100d004040201c04a032919081c003080c2c4c2e07400440340322008003030391038a001100c000d1402204507042c418241c1100740d201c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 603669622 1250 603668372 603668393
    0x1b16060504030f0e091f0b030406090302062a0313020414040605010f180b120709021e1810031b02151303050d0b0f060304050d030f05090d1407 63
    0x240112000102450241030141c655294101003804119400603801256a0352005071504030303403c07601d158440d00030941c14007000407450f000900414000310801081015a07007110040034440c0e400d690310f40d2107650460204142005051402c40b02e8030898207042d0904c500515840a83e0150b401b02c00c403015008181142c2c100c41c9603060005100e0200003d2000c0c0d401420300402d1521761405480d40340c0800c00c15898042040300c40b000d40c9441c03154000340e68020100407542810003d880040e80d40d0201e1f0b00007541704100c107503c5640009020310600082d08113031030070080b001003000c100c007809404100f074914030741c00007109040c0c0c0c900c0100300040f103242e103909101480740c000b80300c0544295580c0803980c400500900074444440c00201c0041d9001003656480c144070200400c140220b00700190301c100c42241c811303810103804400c01003403004c00100c0d000f8141c119101040751110700a611010787c6ca007100d04034850f41c40304090003081403103415400e4100c04d640b20642c0c14007202d0f55404100e503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 603670872 1250 603669622 603669667
    0xc0702030304210c15020a0f060e06100305010501060813030309030207090e0703050f0604020a030b0403050c010c0905191406131a0912070f0b071410020a020114010e1b 74
    0x4807046450008020401c41d1120280c001d600100d070740140e0442c00250b954031421f0006100800ba02988000c010031500481c120b40d9120003610b1241c500724106c03298040312884180d03600e40c284800080d0712805540f00758000e0a07031100041460b445610183c000e4000031a00b01c0c00c51080110009050b9114070a65031003601e000003804440d0705e1030918902d4003c00c0c0c10b0803101d5402003428000165a40e02c08001102c0d40b181460a02c0d50303440c00c0595842c003d900002d5030a500f05003020f10141e5200550b02c003502c074102d03111020740c03201c1c814004060b074140c011031140864100d4101010720386031026050b2650480c070f0410241d40c4940800341c400503c2603402c00c0008000c200300304646000454202914880e5009024803450803d40507084005032140c85094040000d00105100d15058481d0014000c00201d419600c444007181d80258014030404005529000c2d00e1150309500c07404880c1241c061880001690312405e04800190111280b046451031040003500704241385044c105125 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 603672122 1250 603670872 603670919
    0x30f0304060e04060f0e0408070506090a020901080a1a1f030b270303011814070206010305060a060f14040219020d23120702010209040914010c0509090c0702030304 72
    0x46525069001e00312040b196400c0d4883e504004c1c00b40200002c64401c0c1c41242c042c090241c155480d50b0410448910915002070414050041044a130080010302c1d40070051080d51421840ea0307a80c09000c1c1c0750700c000e4400038843c411070f2081a030760003804041c4c4d6030400701100b05200071441d810131100030382440d0b910442d20001664108850f400f05980c4004011407004051130f41c103040070711030304c1e100d03c41402140002041c1600c8021619226070250b400800070701020801130400d400c029550300c40910003107910303101c0c0320009080295140190001c444205001102540c10140e0b01142001544c124035002a0b09001c1c51241c0d038141d6145104420f01500074200001d40000c0c02443c0701d803e48200c06c960324003401c6c2c9440c3c00c500041103403402e089080480c141c40e1101601207001e4070461700b5030f0f60701c070341000031501c01c7c0300d21b03a1003583c2d646441d00000c100b42c2211890564560180c20b100683c00f2070b501c00012aa40300c2c8000a001162008060368905611180f50001d010039408403da078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 603673372 1250 603672122 603672127
    0x14011e0f09080a0c080d020106150c0804030b0c031009020a35040305190c03050406210e01020909060a050306010b0706090503130602011a0a061b0b0106031e090b01051e030f03 77
    0x1700070400d00c101d900201d00391000b48405410005030044194041072041b04104035a0a010144880303201a180619445990307500c00341000c409240054005840e402150480c4a10004242c40544201d4005254580301c01080a10a800901070540c20f00000710b08408000b0500704800c054403105c0c1c0c4501e219480b0036480d030190010524800c0d1040440d40c060000950460021a4000040c2d400300c079003030314007188000c030b8541119180081120f4204000f90030100811030804041d000f500001e1000c0d11903e80d41d036541800c101d03058149110701c1f50190001d80060102030b00002c010b254040c026400810466555941c807460340e800400c4600584403168418854950b082c040d02e8071001c1203d40441d4003088c201d00041c010042845420203008400806545540440350310381d4500790030440781000c40da5203507400b80c060040621040d00c19080c448000903422001e00c50000d14540142141c035603a0300f00424405900080319400a05c40c00900c6c51040d155810414800d08600e400040c54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 603674622 1250 603673372 603673379
    0x5090c0c0c04051f0608010501080a1d0a12020d1d060901210c0f02010504030210020c0c092a0309070b0703050d0903020a020a0b0a051804150f14011e0f09080a0c 71
    0x7480c4c07400d42c111804000c2454010451a80c2c415180307a04010f4460f40054a603500c15240745070300210f00c01641c0e06000c0c0761070110030b100443c1d030088825043d48d02960b0310b80d4851101251b0101401c0381c00590804c3c00003084016040c228040c0c16119010305100e01244034041d0140c103020a40080d0110301603d8084180000d54040942e05101129000a00031414a9a0069280c101daa91010703c201e5000c18000c40d903c5042040b180400401742c4203010300e0602c1500910a440e051310b0140d19600101040100d020780a030440c1d1051a608001d400c089081154004680e401458144d04020007842088400714140c45046a03241c82900285064003103031040c00100070b859844a14421024007403110901d030004100d03036400400303d4a1203032042001c800200200f9120034030a841410100e07000c02c42042d6010203030b080e100c0098150020b00c903807000440d2184910200c204000703038074192a420041c003c0d102c259600155040001c0d401d902c4090301c40c6010200401034624030b81407003040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 603675872 1250 603674622 603674671
    0x909030a0306150e0d020114070308090c0303070506070c0c030b070509091602120c2506030f091101030f0603060c0302070b010f0b040302010f0519030b0102100605090c0c0c0405 78
    0x1004034007403407000142220310142280c1c0e441076001d8040c4611128440c06c6a12481146610b00d0ba690074a5031580c000741002020320008848900a03482840301707584c42c034640041502c01e8036078001300900881d40d845070f0803a0b18100040040700c400494100100000340000342071803158106030358442d1039008503001c00000d18805040740c45102c440040c5404640c1c1c0c00b042c1c2296806000c40d68079991074907034101b149084180b082603150441506910304122816030b850f0811250f05d6902881040e8038200d0313046c06c681c128035000703000c507444a510844d6540a90465900c40300e03403900000d41195207450304415290090411800290300041c810b08001004500714007603d9502928024039047c07480030f00844c42a808060306001502c00c0e42000315125500301c070256644105004804c003803501000d0702070102000380781e001d40600d82d44820004135900c529801c0350001003002c802a12229040000c41c1d010640b9a500c9008245210090b034450340a41c0e405200c00e990702c2000742c160301d81038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 603677122 1250 603675872 603675881
    0x403120204050a1403010c1d01030c050c0a11031c090e04021f0918110d020c03040816030317090a060b0f06031927030516024603080705010b0909030a03 67
    0x4031003800031280305423804008070105c500560500382000030700c14000c1c4c0c1090700c003406154820210780c400c03c5060b07820050410018004aa0300381c0881c0c90107401c0380062615890020100d80c0001c004070010007d01840011703080e00180090103032080003000c4000e03c0480e0b01a420440d011503c18170003000026642800011001811076080160709a094900c0d0000c0c801d068440014a8000c00c036003240d33400c28000c98004168000880b45080c208201040c0c16407620300c02500407c0544208040701840c1c214264461042c030400b0303040240d41c999480c0700400c80e089250b508030756040070b00350150320b5140c001c6010300360805068140240c46000d42060310240700c514104c641c54541c0c0581408014103589990546c1402c1894884c0e481090035514000c210030301a62290140444000c1d035a401c1c0002d0b40745801c0100708500c07040d0071003031010550201020002426488a01c1000410b00c2d10740a000854030803400440d170b6805400018118600c16a035240c09500009004140076405129 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 603678372 1250 603677122 603677141
    0x303070e030d09050f0f010504080f0708010b010521070306080d080a0b01030b0102150c1e07050c030c0a0302060c10020f0a03050106080f01050d020d0b09010b04150e0403120204050a140301 83
    0xf0144100e40c145400f0450500001e00024000c50103030f58684c1c416800341c000d84010303201d91400c0790b03000c0d04040ea82b29512101c0c0d10401c0d035194a0422910744a51165003100d441d000241c565480c13008912003a1503c2c2e40307000745150105559040003249005040c4015807854090381c0d41c695444c00c12414410881d801c0110090503d85040c0b09151140d0f0003149800400d1000103c010199130707a800e0850140c03246400c0e0140b00404d40034110b0170403c48101410141d80600c0c119800902502c0a055507251030009165109602070410401443c3c000e000b041d101030b0b01d805a501ca0001b03a6410026600700c0251b03100d6208004c201e4103043c039814071442c3d0040c015031030000d005e03040600800c620018107010745e502407065a0124415500c3d182081582160700500045403032406508007402020196070442c0b2903400c020361003084010070401c5105071032000c0000c811907140e903681a00c03051002c0550500d42a020301002403d651403141c2c00c801041480020084076030300204250171a0545075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 603679622 1250 603678372 603678377
    0x4090b09160815010501050a030605032d060106021b0a080601080606030d090620190c1e0e060402030709031407030309150c020f04060e1305070b070302060708070903050303070e030d 80
    0x188030729804007204600f504441d002e09109950b03100c40c074400c0b8013414031034010a4048c81030201c200310320000320302c400c1102e03d05c0e50b01c2c4002e45003280f02100d848000a1050500503404498003064100391403101059070b40008125540c5035540300729117401d284099201c088a50801d80812907103080c248a05181b0000601d800d0440c0b6052403000317041c0c040300741000e200f181c10170960045d41c510204804541c0c9105041c9212a0030f5092501d04034042860090023009001d10305820948001c0c110703454241d440c42c0310807440700c1d030b508020b1100a41004260768104911f0326400008a046800c0540c0032030740420140c0986815805c015142040c141c1c05126405104022030501580c080c0656000a604440b03058001c1d006000050142c00507401180c03a0032001c600b80120356119164180000c0c1c806c000b9141c0d06503480000341154042c4020113030158001c140060740c0584600086503101c1d01e0390500c82401500d0380c4600e440c0d50000c036110f40c08922900d0b10f8110034a4100503020314078101c0e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 603680872 1250 603679622 603679633
    0x50402120706230f1909052209020a0315090b1006051b030912150108070e0a051b0d02030402030c220e0c0415030b0f01050904020f04090b091608 64
    0x40d00051441000c0502140f030410182c0080b1800749511048030000b02a4001d0a902c4407042c03201c120400303144406020114281d29000281402c0104c91600c100d88110021020f031001202844040e02c0c40c440704aa000c0305c041004000a2245200c0c00c0e010424003400060180c0b00b40350001182c00d01030280380e1044040c00c010010030b580902100c03441c1c854035401c0705140c0d908441d041d165000e030b225034a0b402103070b402074001c8800c0009080050000801440c40c41640d03900b1025854100900507204002e800e0000a6a01640307500800d411048134251180b00501800401205400907001c1d405410740001c02c0c0420762904014890b5055006c07a03504a02c1217201541c0c2818a08031022010b07100c0e214034400404500911500040c144094424401c0c07a900ca110484030392460b000480e201802200410003070440481202d051322009861026281c55980800200592280e00c055021361514040000503100d00000c0b40102c04100c010504080c4000002a0b2552207410020299122 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 603682122 1250 603680872 603680879
    0x10302090105010e0301090b0c070204110c030a0507050c09100518070815031603140706020a0c060e0402070c0b0406030606110318010203040b07050318030a021318020a03060504021207 81
    0xc002600e8110780003402c20b00340380d284100c0428050019110040e20b0304103010100302e00c01486078000c2a281c1d00c2103d0801606800b244401028040c94a031745640d83d00511220341240e019500416071140540120350711203100c1c0000591801040306c41c4400051885810042d50400c0240c020181c403000ca0910b80c4c5140581004210143c014491142c0e00554004400281c4047c02091091040196000c900d41c0c4c99080a140b40d200794025a14203204690002440d54408108800c500340c2c00001ca210740c42c034100080310302c1302c44845002da005900300510340c00a848031042e0320090246500003074944d450410050211042a4041d00c1802449841d000321000c000c0100c640740528a07000030803088903000100d10354011a00302071410400015000103014002001d0310800c1d00300c1d454401503800300010301d5142d41c10203400941040c65081c10f100704035181d0704180d0780076070b000c02d01d030900e000c2c80d40006502210075401030710140e94417403e001c01d500b4580c151101c11445c000041c00418a07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 603683372 1250 603682122 603682129
    0x1a01030e0c010806060909011502150417030735060d080906030403091805040c14130e0c041107020f041b031e0504050d08071d1302090a0b041706010302 67
    0x48520280b81044200310001e402030b594042595034280300607043c415550385a50040e00d115100004603c00b502c2013042300300e47c51202e11881da1040d075001c4601c440c41c5031140c090b1a0300c0e4102034800000d00480c0801c840168041c1c0024200c0400050104254525040d88074064400c000e44007502564040c01a007000c160000d0444507100b0701901c041e503a0340e0352404c0481c0c000c180f0342c022622801d00c0d0001d0720485000c0b0741000380524000c02c04130360b03080c3d614403070344c10083c030050281d07900100018840c544084061740414406040c100c15100c107209424000f8040307502e03c500703810a040010403600305500700b2150202002c4000e440400952401525852892022a0010b41051348900004204080c0210210f0094020f110305200b281002e00e09030b900d40b030460441400064155002400c3c0728442d501d401c501d0010888003883c24021503051007505080d4002c0c1e400d6482c1c0801c110202503c414889200600c44002d06540322410409080c2415800081c40742031540014014005070340e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 603684622 1250 603683372 603683383
    0xb040c022a0307060e04020d020a090f08030403032c03160f090c022109180702191e05030f030a1e1a01030513150b01020d0207080c0f011808011a01030e 67
    0x120302d4203200000540b10350011b806403090420807501140045003640042d60045118401c0d5a240ca11519101d40c58501c00c40da280503920024001500c0072800c040c1494450f032010020000e480e900c000301c0b00a100c04240740084080710071080c81e2141c5020441d0008003a581c0c0090601d4031024480c1c404103c100030750301c10740d078840c0c4507803201541019859040101c04031000c6d40005421020070150006000c0c41d4010221803410260050390100443ca07088a0381d4444003c2d4048000d40c00003485840100301c001215030202d0f110302c0100204621041e1a2014520501601d000494032040300002044d010081d840c02083e40f50802401c00d510785881c241d0090508000e20300000c01c1d598842c00b0034602c82d082c00c4050426038141c9440b9580741140d400c0303044295401e07001c44244120142049030b84810a05c00c10300e040e0070610894a1510b0703c8804440c0c603003414540300c0c84441c0101102c04200c1c13520390203101560755034000c4040e1900c050521000000090800700010040a03d02c51f8440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 603685872 1250 603684622 603684629
    0x225120e030616210608030d060b0723010605040504050a05010e160b0901140d060533031b0309070810020a0e04050402030115060806040b100f050702040b040c022a0307 74
    0x2403844c01610f461001c0000c044000e080700c40c0140b0a8903901d9065a80782d5010325051552a4140440801d00701407001c1202c150a0f40f040301c90201c84181c1242114401c4026403820103035403240c0e800140c2e2384d140d000d014012030292010344410b5405280050845000c1407130803030a50070030700c0d1381034500603956010011142d25106850383d4182d6000101c5001221407580b200c05000841d1030801e000032a401901507840640c0d600c100c00b03488111440442c01000910403031900040c0b0300010101105002d903800c248010700c0c10800031554940400b483e002112002d8160340b06560070424202c041041d2034200d448004114680003005000921b4010740703d4203030380120b0b26680800e0454400354803024085128124664550361150801895808140c5e1964812410003000c030b1514505000000b27041c2c46c0c00d4444021207508900240c030107030408a4180e91060fa155510001901c4a0007542e50720150b560203400c1c82010280a0000c4102203010700001002c0307540442d0035500d002030072500b507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 603687122 1250 603685872 603685877
    0x150108070c080309012003040605061e0d0602070b01030b10090213140a0306050a0e07051903120912150f09030e0d08040b0c0d170402030606040225120e030616 70
    0x101e41d2101342d81400f60030840b862030340105e9640c1c41c01c028006228082c5010700e101c2d60041c80f09880740800c124802a404a0350894200304040f04255840d2507050340520a2052a0150a00e280c944407d002010300b42c0c02640e480340c0032010010811270580030007029101503501103082040304010702010212034080c1c450109040409103180359200f0203284000c50f4095402d016034079080d075606016220010f030356150342c0703e1450041001d2412441c0c41034800084421059024590f846a101c0c01203618002024081c800e90701143d9010310207259860345000d0014501000c0100c00076400700e43d1034031000c103602840c100001c03001070760140101e42c002604582c021002801810b0921540c411503001a200a0001500c912518800309032010b04880548822010010803c0340ca00d000c0422100294141c01031400901c00b4070b882d5000d0840d9884004420841c440a05c086082d044c4070302c50b040c2c0b0400640d002c4852030985c030980d0801a620194082d04045c10201c02c542c501e099070709a0b860a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 603688372 1250 603687122 603687127
    0x70b0909060616030207090b0603010503060406240602031305221a0402040f0501090608041203020a0c02040903080a0b0315010b09061207051201090e030a030b1f08150108070c08 78
    0x95640d5200658460b001843c4140d0000c580074940030b507440c00c2900c10b1080c0c007800e04080701400e2a051007564101c540180192510303680d42d65580c0d0003015402c07442d44c40d01d101d81060745110411816128050312464006513644c48440c5000d001b00160340e030016109051000030214605400d015005a000e0f007040e01040050628110a00300b5100b00d2006800520106000800c821a03001e1a000c9400c20380790a103036662515800c4034858006c44003d00310300048080c82544610076402403c0c85040c0d071611100c40407007a0300240503203006110940028060009100c5090424410110340010407001440c04100d07002d80d414035448144500b0040050114010200d6103070380c400c840002500d4000f885540c5000b000140198104a101c100000c9250b8004030314443e180c42501c0b2562507200c010b41c00c1c40b05c000c40850150018141064100700280800032035001440103143c820041d85c3c61301c00b07180c42e1141407608955107250b05581040030340da082c8184517400081c0e40b141650400741865 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 603689622 1250 603688372 603688381
    0x92b120e070b0c1605010f051806090604080d08010b090307060c0c03081903050709030b06060327030706110f1b0a0807061409010b0a060507060f06030809030d02070b0909 75
    0x10300345142a442036816150003d854881c0c0b40003c11560054541c0300c8424052985420044480080541c6010003080007004100d440c044d07846c24038080040c0003010f40d171412880c0000318500d42c202e0b84c4440032950010040e40600360b00b1881d01c60162610084031400d0001e45000a540d5110600c03510081c01803582c003640a00c84a000307204090358001ea01c056132510442c40220240350500074000000b490100801c0c00c2c103102d60342e940c04880d041640703650303980c96000402000354000b811208030120300c10019a52840701e060607448152582020f0b40c0c4407405418801f0a841e5041c00d8400741003010049a00d0400b130880583d0000131001d1150840d03402d40c1592a40343c08040380e0040c0a14a001c40c4e41810010945c000b1402001c074040f8154051b218100d1303940c02d0791b800c2082140c0c40031410300b05026552150014101060007140080b0b01e5001914030302003142c0031340d00f00795440c400007c1c0c2038401e03003002c01018070060b00c00e100a1068526240368602c1c81d01035510920703c200048004034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 603690872 1250 603689622 603689651
    0xa0302070f0b09160509040308090a05012d0203091005040c091104090f0b01200a02220e070e04110d3302070822030b092b12 55
    0xa4104541c8072065103801c014a09000b620108100d81d210150310644813590781d10350003c4030740021904080c0021240d0b0703c5540d01540c0f01500203100b035085104541a04c4003146007401401d40580c0141c420040550b01c486403100101e10b01061500c50728010000d00c203c4010011302d000d101235610030b00003035035221403070540041c002c5076101c0500542044401d940d03412403030000b8000c5601001c820440c03520140744003811b0307030019055035006c603068040401d680a0096243c01c403000c3e0504c10742d450504564000340c0b113100103420341c8a01c20050604a542031141744103101854a0140c007e004051520380b4102040388010001420f24900800c9100705840b400420303010b4552000d20f0b00c0200c5600360740400d45481000406580c5202400700a5411340c580c07088030714643c0c01500b003514210855040740d180c1b0b00c0800750301c0101180c405000002c13814a4907003900841405000d0000c18041013541080644402144004096101300d40010325810580c210003408401d030011488094804a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 603692122 1250 603690872 603690877
    0x11b170705070f0503071703160201030e100204051e1005090102160b071104051003140a050304060c0b01060305010b0a26010f08010f0207030c1b1d010303020609210a0302 75
    0xd00502c140c510114042050701000d8050354416400c482c0c40301e544040b951044011001100f2041e00204044074410b0342c070000071400b080c0181000701743c010100e40b0151904039402c205074060303a40483c0501c0780c0d01c4d00e2881c1e1350401c60341000d40d0281030303c201c000480a030401000001071000005d02d00659034024080c0d6012040318079407403e812a40ca5503101c03041e03441402c08945c00f52845425000740c0c9818807542c1e0203918001c501d258003e08656415000c04204407410545201d56400c41001802c20170003400a80500d80c2c51092200341450041c00c540c0041e0407010070b25040c000144603040c10841a10105a131500e080460144050a1702c101482c0c00d141a101000d49040085181100c04440c402203a03000700c000c0116080306140c1d20b00321700402c14010001400c216540300030508c0707110a101800042407442d01000c0e5546100c0f841c500d0900e40a0356082903440c0108107268040c02140c2d0311003c5800030303000000401c52002010900c0380fa02d029100d00100350380c0d0007248650305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 603693372 1250 603692122 603692137
    0x6081f321819230108210a051305130605130c02100209011707210b06042c0403030b0f061204080c0106180f05071e080606090607060b0f011b17 63
    0x1841900307650f00404046421424080c0204070b1042c4003601740241801c0042e011940c02c210591402c00f00c11f248102c403668060f401c0a050000c0c044000326840e95580e440c0d043d0ba10300740d807001906030303d04418030211080f46006620741c240351000103203001d5008204203501d11249080180d4034080d860060b5600d013800410214000c00c1d0000300100d05400004038007404042d6818800c0d90a0001450000d8036584003100c2e821200a21007040144180b950446224a1800340ca40e0071024000070002013210882d8140d0000792540e01c40c61144c20032003840100c11600760391892030106e4940b15900d85000150004040c60400107610344030030310a62008014295000c01100100d400c0b0f0400350140003c40c07040e605141c64540803a070541e01030543d04114860b86007217410300f403982c1d8400751100b03540108880c0e000541008402601d0b600c400c0105400762160200240b44180e11043c0001d200d9003030265410300c402544038010311034003416402519540f11380c05000a2401c0180d08c0440e000384007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 603694622 1250 603693372 603693401
    0xf0f12091401090302061003050a0b0606040b0307081614120a1e0509061302151c020706020d0c0e06040308071e08070302120406081f321819 62
    0x80d0700848000c0642041425902903400c40d0081d484030041c4920003200c6100007009030b4010640d80300050b00092800d68010402050142010f42e60360b00e004845d801221404001111807003040020b11300e070200c5100c2c0500501d0540d0681030b001c14400c915101e100341c80d0313400c241c9405c002048085550069280c841346a080240260b9040c030b068009030201350380300b0391203008080000300148100042448403a400519a191900e902e005409080d400504208a010307201c030040300d482c0e640c40c002001064842d41d80140c1e2403d15a40c0e0508071140300c00c900c010000342009001090b91003505990985e900894143d030383d02c5080c50f01290b1007100c800281083c2d00320406250600084e00302070103803507000b5003e45800050802c00c104081c8668002c0c400403070480b002042c4001c108030304080c1d042c8403a1141d0b21070942c44924102d620034075444c09604494a040c02e04500101c070240c40810385900342c030010b4440030402444103400f400100380c1b045001d1107064480d24400701e030708007451000801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 603695872 1250 603694622 603694643
    0x603020a080c010818060f190c050a11010c020309010e01020102090405040f05070f03051c0e030601090e0f03040b04030807021c0f110108090a06150e15100f0f1209 72
    0x110702041d1600002210320b408500c0a90001c0e040070b06000c4040307542440030015203469911008030030824180038164000c8580c0f401680000c10009101e0340000068944445446043d02c980007001e91445000b9107000c0c0e410910010400754002054030100982401c0c10010398180c800101d00a01403100c1d4947c0c030500701000e0005011a400c140d0f801355010340c06852501d5203954464000344914170004101d40d00681ca841c0d456a50350342900d10503c158640040f0804038807001918015003a04641d4245907941204545d104e0308220613184001038a002d142082e01c1e110348001c0a008a100240c03080a00240400031942e03052404c242840055840340c2c01d6040c1410325504014030b111040300c20700f10b010401e954941c02554494407480360700000300340c500c11690303c3c5400f8005601e8054400350070010007290000d01c041c0ca85100c0c0d82403d088400e4420b0349400c12610104e845807031014844e44c800d51001182d80800b5850411889041807d1320b20315814031a402000008405420140e10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 603697122 1250 603695872 603695879
    0x30a0806310609180308060904080d1407030e0c0d0b0901150305070e06010504050f04111e1806040302010f03181a07030507081012050a2a0b120a0e010603020a 70
    0x155000320142d404200d0f0402211425911201200302c80950240205412600107122481c1c4200c483d54000d101c0d102460900d05841800300507128054076902801c44600c0801135145d07818850721385440c550174010190162500c01140403519402d00261030350421000050701020250404610980307400c0780818076554070304201e038942586010300902e0300010804254250b2203030b07040e078003601c000900144c2000101c1c408c020091280541c120040201480545001114a2900b9000d421841e40382030780d45058615407030000c507090b040907105120520051026036444406483d60002d103080000300d40b10b9590482030f110415500082c45488401c040c081000710080da03060090380d882c0c4060005840310031301950089003c45881e107000f1303010b0070200108500700654480b1540500c0588901102c2e07920b0390444503c0e484050417204600c81007402c01b4a14840f030385401024682002c5003044d1540c8190750075420007a00320f04403140c4481140c01e0911081d0700640080d41d000f001000c94070f66 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 603698372 1250 603697122 603697219
    0x302090a080715140a09090207050a0204020a051206040608060708090a0c030c080c0909100213030602070803010305100c0824030601141c02030d050a0c050a0302031902030a0806 78
    0xc9900f1102c000340c2e0b0010040c008111400660310480500e8071101c4840f414280c0c003a000b03403c0a40e0550780c5104006500000d40c86510042ca918074080d55910380d21070a040002072480000341074a40101d00e0140f04110308030022410a40182107031a02c6a11a120154550714000c440c1d80c024040b2160041c0010411003402d1a50f03080764020002c3da01e018101004000b00807204466921064200040280b5420f03441c0e0700500d0880705100e40804802d88039242c110482e00300c4e08084504650001c0140280201005141e4261207007030f40078060300c906103000401543d0081c0c007400c6031003036064620300659132000c00388588038409001c443c00380da55129800c201c01515840b09004180c045880d038908012500140c8031143c01030003e0040e414032800481c0c444e4484c041103000c1204403070340c0d100003640a00c56006414003d500658070f0301030303446000d8131044200000704150740c000c000c0c988920360852849540318104480260300544004007032a00e10311541d40300810710350904c0145001e0039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 603699622 1250 603698372 603698399
    0x80a020409022d09183c070905010806070509060a03090203030703090e0603030702010c12021212010603060b070f0209040215070b04110427030309060905060619060e010302090a0807 80
    0x9003240c1c44050340d05c841016003024020011504d074550402007900050180c001c00340010301891038043c00e49400d5070040c5440d40d4504039400e8035940c100e402c00300103206860091602406218003e00038508080e01c2c040c0080c410034600c0c6014545c003090b8401401d0095020310001500901902d60792000c0303241c0217003001c4660207500d03413894800c000f04116050010070380d0820366040c1c50b01c0e9900c14903910380d10300503400c4504007411442020500c611049140015043c0220124040d40c2036505260018085d03404913040744001550034000f09002c5a4000c1a0074070302c907015070ba40340305601ca90004c41e8907070b50b82c1541c1030603050380040c00000300036003420030b14802c030701407159407007030400450401c025520908001422180041d142520380c0ea115041402d1079032190400060304a80d0f0f80e6010140c420860054170f268000303204000d6241004418410090f0b501e40240201c1414208050a0080c0040e800c0741050360100e14100c82c1d03122a1440005841c0750801c64002940d9400300da0241c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 603700872 1250 603699622 603699709
    0x902040c0c06050c0307050d05040f0c060c050f01150608040528060b10050a1409040906020405040f09031202070602040b030a0905100522210503150307080a02040902 73
    0x302c2c40d250000c1c040c1c412a03400e5900a5050b40d80d408e191140700b80484014020151081e12141c0744110010006600d0b0700218000b02421b0302c84803550b0303905040207418040c000f83d41e40102d906103008000d440c21500e8402041e030701541030804940d1503600306580707000c80080c000c816154005030341d9039010300c0305444003840900c1200240500d99925083c0a200707603401d403540001c01d40034018010342074000d401c04404030360b5101c030017424280f047c4c1c00031782074862801e011f540e507541c00107041c42a41000d00607040a040b40130402c0c0003041d031655000303100300c21504410b0181940400e00b2410040d41b03404590080030500720302912420a098000024a0941011601031040c0c801d6221401c0d107074040e1502c5000100ea0200607501d0340610034070030104601c82110740c483d100d1150141001c01b600380c1040c0e0102a91001e899241080080050701506030720540707e640f00000c1046228000203241c080c040d41540e01050785045803010411515907110541203003c80d000201041030302c00f03030244441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 603702122 1250 603700872 603700883
    0x1170102131e0b1602270a0506011b0210080c0904020415300f0f14041e050c0609060c150a14060105161b0b1902010c02030307120902040c0c 62
    0x1c659880f400381d80d06115400c20020081c2001d241d0002524003d420100740c90f24595410050a1320b0546081449004a41100d005581c0704144099968440b046403891020480560b2520303100340c00082c002083c140b0700d5010800e15200041e0000428416200703c0340c8080e00564880d6207552503560080d0300c104880700050f04d9941c543d030842650055080c0f511003900081d048010a5001c040041c0c444e1000302541140c650700e506458032054031907015164840c4066500c181400d01c2e00303614009916241c0c0344003070315a4010a010450119011034074001c21121240d4403000013010a2140c0185030030107405000d07601d07c1207100e000800e000c0e071007003564150401c18041d6480108514003c01d4841c00d0001d002400001a460340311184008550300804241d048443e00742c9540c18140002d400180c05003001180341118003d8041c035400d08070003070f40000c1c0050382d81400d00a589000090102c01044489210f20042c24840d51003015030710380140060000d1101e01c5800340105461000072186c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 603703372 1250 603702122 603702179
    0x7030b060306040c060e0a170a02030105070e131a100809010506030a0f03080414013201050141090f010c0c0b0c011b0c0c08010c080117010213 63
    0x151464003007100b6100c1caa01c40000036200b800c00004407510360309072000d940c010090b0719002c0741e00c205102c0ca100d403244400000340213124062043c14295000608100300f444216001640b4039550208240341c5000c103000005858900440070300c003198068010950003900c4164a000081d90054800d445240c40b8002401140c0743c40007855a01c05050002505e0b1007004030072000001d200e41c0603103800a0094402225140c0000350450071240744694a01600941c44a000840300401c41d0643d5180d5611039207550b0b0798504000070b0090995a049240c019200c0318031140030880c2d551518080541d5400341c55840090041c2505a6920185809210f01c410150380311032588a4400c2c40c51030380c6d200d04089000d601c0c0440c10803081c1c00945522065549454258801c140840802c0e241d0907a41d03a00d4410601650524031100340040d00f100f48664105044003034910b400500302030456440000d241146035082082500900a0b09016149840700740e00005074086950030007620750522048280 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 603704622 1250 603703372 603703381
    0x717010204051e090c0d0f060902090f0406050d060c0c050307051b030a1121190b1008030708030403031d0c10031812020102040510050408191a06030f030c07030b 71
    0x46031902843d1006512100d07140c0002d02c80a0054050203d0359246c1e240450840000642c2c141641c0b036682240c890a54041a429124a49503202190509060758100000c074100401308014010240d0041c00d050384a00d440c01c03a141c820300d104000c10b030300101a01c2e110101d0780b608949554402c000d446188035100000400d500c1c000c903540750030951000d00d007a00c00c88042c00340301d1403288004103203400c1c808440500b001c82c0800e0140c80b481c20324048462012a6282c0341c031410b0407e000d85030540300001000b05004d180d41c00421145410340203200315482c0e50ba6072400301d01030100100d180700300803c11086d15400901c0090031449210040f50b81d82c1c074a14200d841101140d101c1481840074110b044440008103156184002400c4242d20006d4a85611280411090b000c1d4102c0c010004400290400451006001c807094180b01407041040c4601d603611081d1041c40e03440c02c03685814002801041c0e95075000c11403c420390b03100006680e00e0b81c0d40b880c41292240c01e540b005880c01c40d003a00024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 603705872 1250 603704622 603704659
    0xc2604020406140108150102190c1e0b0304030e0a050a03030c030f180303080c0403060e03031609030b0402060c0106091b09080c030715050d09060e19020604090207020102071701020405 81
    0xf455008010780d40da150a6a800180500b5412982103181c1540a800303c40d138a6031085041c0c40130030318000d42000c1c86861400d51100300340d089000c1ca860841207440d0301400510740c10400c0f240c201e605460311105070300c02c050006119903681d0b40115441405410f00008040e00000580c000d10b0103900e5024001c0c000790015183c461451101d1400c0071130745c82050002a029092242d0030109500115007000c3d00c80c0e66a9040340c0008a00010070340c004020132251a1071241d0441c0084002e151000249245581d002c024040180c0020320444000c510001d03006025448a4010261484207121000c3e2108880da07000403c90360802c0003942e43d10b800318084a001952401880c40a801400d01a00d0010f03800504445000341e102041410891a007000300310b0b01444240e60701407603001842002c0008030a292044002c00c1208651001500c640960b0703489082d06c08859030301c2005640d4107070300d00c0100d041003034540008007500d920070240c140701c04c815405030042c0d48085c0c1d105560169007501c60b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 603707122 1250 603705872 603705899
    0x31101030615110c03010504050604230d031e05070302090a090e12070507030f030206061e030c13090f0803060301050c0f09040902150a03150b070c05040c2604020406 73
    0xc000007400d004505403400b5110303480700fa072401407120590304100d030b40400180c00e480055400b540e55600035000d00050150720f98212071149900c8070042c0d240500801d01c01c4d200e914100c4c6050a1589e1440b0310403032156419840d2880729030102d410050b0380b41a9002400a402c4091100e0050101c0100070580d001c2a04c2030382c1c03e01c0002c0d401042c0b200c0100d85024943d50125204a601780603e0b10000b00007940c04581c1c42c4041e1280e000f03400300d86050300a001c5240c0030074081120103400c6080460f004e4501180f12a146407050f41c6d00c2c41200e400940e08000381042d04e40003070201800c2c00d42c803028021464044d5015034000c80c02446903843e01e41d1010720600801000e4001d1142c1003089140c1481c1c241d1119400c1d034406005000400150594010305411840040002c070341c552010811843c045400003000d007606941b11400e10b141903d42200c005094019140110340c0d89403030f003101a0055a98011215075200540600c010b14650800000700544040740503508004d000701e4107842e20003030f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 603708372 1250 603707122 603707129
    0x604090f1a06041d0a0b0a0b030a05070518010c1b12020a0b0c062e060c140706020d050d02040e01030318060206010303080c07021203030c1b03130b0f0d14010311010306 74
    0x5981e521288000b031600d0581c1300506500022965020300000a840b00c0d2006402054008466074403032610804041c29681c1c01000f03036040001c10060981701c003403428281001700c0c0081c81c011110404e90728000400451041d003e280e45003400c04001101c2d605103000085036442960020340c5290754a4001d4020b0140e00c0d50460190070803000a0030390040714111600c0030302403405030109064010700c601c586510540181e0300084001c0c00c02010700250420400380d119200005200d80713840c00e00029203071102509890304218000540c3c016411190f010f41e4003030800c080c05614036503034900e0050203501007414034006401c0140310020b4050b00215066040741c4e099101c1004580c0c0d1803000c0503259000c120704074dd0004c4d41c181c05082d007000c10806103110b030403561403150342c6062000841461a150000301d251580c0100b02d90008006000c4201c0103e52401041949580c0d409401e481c050140700d40c4001c50501d8800c501e841d241c20401d005049a000307025075101c0045030300044040d280c1501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 603709622 1250 603708372 603708389
    0x61303110d050c0d0501020f04030c03030314040b1b04080f070e010609060806010c2405180a050d0503090a1505100503010b0a030b27161d070804020604090f1a0604 72
    0x181d82c0f0224103208082c600002e128030001858034a602ca06500243c000780c000340d0b000165080203104151b054840c048074840e145000481a141c11f81e140740c3c044078000d180d40d04c0d00301281e044614800e445410b0702c02a0904809642c51402c10071440c50381d445962040b0310028030b070b260001842d02d00540242c3c042c2d5204d50340306041e5644410040d13640148030b0034112070705164040c0102c0c25072100410b01b041190420004a20380c01d00e4505664440f1a0700d002c038046401c0455083d001403000550f003501c2c0280c5080948e140c0d03865201403400c10710303903007805848118544280c416107081d5900c2244100d01f0706400d0428640c0b2403003814221008007210981040318903000744085012204c1007540000e00040300e460300d100100c01000110040d00c0307260400c4d030252001c108041c030a2803014000c1e00c010b09120846018030500912510f00c05032034003040c07149010100d025522035000300c80141103c4001444010101c0700e00600500c40032007c00c4200b400da10303190101d03190000403902140c0130513 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 603710872 1250 603709622 603709633
    0xf180305210403030c020d0c090516030f1814010e060903030618010308070201110f010e0705030714210703120e040608030a02251d0a27080a0e061303110d05 69
    0x503807c1c442000c4504506681d014581540011140e101e405038070322a0b00031808099440050500150541c1d00340c0c44040390890903c5900807104030000c6d0300030070854100301c52901c41036401172560b0040942248806c960701840d0104010410000300031800b038041511007102d0390351640c0c044102041e00380001047e19500b008810301640c400d0b4103568814103501c00740c138101c0f6032200e156401c44070014004c0c41141c0240200704814a401c0c4a807030024180b005000e48141c04d40000a10140480054030141e0b1860011240304800304200d81030103564000308450400f48102800b40a046e10044200d200714109032002c00c00d62400b1064400c40c012580040c400d004010032003020320f4406c8940c860020403500d40c0011911405001c0400c040d191a2803d42141006000f00003942e074480601041a10f1440090642c41c112800b50b517511034200c00340a03110006054201ca8070100310304003507840080492010303000c030803045648007141d114010103179600301c4d10010300c070030145103440240198104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 603712122 1250 603710872 603710897
    0x10503010909030207050a081011120105120a0b100509070c050c0d111021020c030f0a120609021b0a111011011a040f09020306070f18030521040303 65
    0x240d004009082e00c00c0c0191955a82c0740e070045011100c7ca0303884000c0640c072124580b50f406030b55105d0b0000e0102c10410040c90252041403908a0b41e1062080d035000e140d2808034510200300c103000510009600c140c52402c642040002840d010b0494040c05200342140000b14144a010f615002c40007984940a000d28040c1501001028201030109551900c1c030a001402140d4480140c8800a01181c840700f401461034094000c02403065a20702402e10b1042080f03105865000065030340071403540138403030b55a844881040350030761401880c54030b16905050002c074406800d50017074041c80440b500c07a05800410385a0b0340d40d950044080180400280d8454101c150074501d0000c6900c510358200914106e240850301800c4030080c0d0320b800c0300c0c591188905034541c44e00d4020401c1d107000c01c42e4240550f9190f07400017a196280a4141000d100306081c40c2202c26001d02c0c1103000382035180c8600d05450303030307a030410544440c01c4487d0f03894800d00d065034400c00034101100340d4081d260180c4c1c410128545 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 603713372 1250 603712122 603712139
    0x207030602030c0d020d020c1c080a0c17041505160e09071b14153318040b0c031905060d02100e01021e0d0e13050907030b010e040201050301 62
    0x7025180f0744003203004020300301080c00140020402007040020050f0384010306049541002c80c0c40c1f84140c2080307041e40b00d601805900c6994241c10a04200c0002008070700100c017a241c0e000b240d00e41180c800c0d03085007040b0500c030304811044c146070b08400c0240b01d00d40e5540f0708200310500c00501032020401d000245080b50500444a80d032101d914100304050b441c0c400c0303405d00201d070701310802c2f1000c0f03002200c181035240c07003070208001d40104640c4a00c0281400b5131484070601d1b00e64200d903d010000040040d0f480300ba0036410b1a4180050150720f490500f5001c01b005d03000003150b054483c01c500802141e02861a43c044a1040c0ca108611905820b011004603015000c0030b0080b0f42c4c03004c0343c1000a40540c1d1009a10110802c00d80c07100c01c0709066003400a07080004540c0071f400c514846c034031074200c5014046114454180b81e4500b03000c2c40c00342c40b070001d4140510751800c124010328040400181d140c001403200242c90082c0881c0415a07a690191229150101c800034001380040c001044440b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 603714622 1250 603713372 603713377
    0x319030203220f02030a2a05060708090301150b1b030c031903021c0e010b18150a03050715080a060f090b010e120c0f06031003020105090102070b1317010c0207030602 73
    0x9102d2a80c085803003c440e00001c0c54108500f105030b40c1007402c083d05502001d03a9202d04c00000d0080c0c48082415803030800055203501a901018202c844009040c4c1250b030380a5025042e143c9400c010612040d88a100c5600c0c1504401192080b81400c10580f059003c000420b48a81c105074400452038216550031540c41041900700d11420302d0740034002021709070305003040c2c0000704208000008001108600c0039081d151503c014a005500c16198270a11441a105469020310018808240301c6803000100f03484105507440644140914080482d82201e041d03080d420301c1c4119900e13008151a15a4280d044460620402d00d10b03e03500701003044003030b400b0742050300460750506068080f02400f2022404840007890303015403c0e048002100581c0c601076008110f80c5000759440c41c110728189401000240e2980806414014007041c901004da200704501d0003c3e0510004c0182c5a00c507150f4005864101402459102180c20718504e83c115014841e0b030702032042c6a0300401b117840c80c544800303000350b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 603715872 1250 603714622 603714691
    0x1c110c04020a0915020d080f06130e100906060e1e010e0a06050d0b01150e0a0b030604091a09120a0203180402090d0507170d08010902180907020319030203 68
    0x4281d161001a101015641162004c41c0b9500a08120741d01110000c041d940b009004e103078900c0d105010b001441c3c0344c0c001c5020144081d180002070020290070000d10701140c07115005402e0741010f0444081000a404c850b08a603043c0c250020b5030f464103480a9680850300c00030f02d00800114004000d8140101d141a400070a29180001c5664890000c01c5100049450a40b11b2500103c0100040c11011407100304a12082c1343c1a01c010200100141040382a40b00d8004e13004000300100f00f040ea5207503c1100301681c001c0c2180d06c00d2200c0039440ca014035048650712400d00440464851541401d0100c4540c038402c0e5015501d040c00e001612503402401c0036619070815800e200c908540d880300281c7d240c08502a60080c40c07501c0c0340c4a04c031451904010541d10064111020007072020b40c01107a040d055522035400035840d40703040c0d2038165900903242442640403401e4020b00060030b4003c0000d10303d1107028001c0a083d4059548240d0076448180e0b80c080d0071424100c00e58025411f01c013004000c0303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 603717122 1250 603715872 603715877
    0x504030c0f08071b050105090112020d050103050d080106020a02090604051e10081c05040e130f0f020414270a0c09330603020c031603021c110c04020a 66
    0x2031100c0303445200700c54160160880c0c0c0c100c00000c55000740404c14a04103a51450850034501050030038000030714501603981161f0501c000d8400c4e00030110555019038151091a01d0304208640c0c1d02c0c141103982c1c44110080c100415401c00020030401d201040075842250050609542911444180700c01842c000f00090000010240740d080e038820f00c4800d140c02a0300980c40020000e0a18030f240d4103025048401110604500c441100901c3d000f0040d1011500c03030303803c403000680e2802c00c0801c5850f8044401806840810818000c108912001d581401e0083d1801c01c000c1c00020700103d1031140549000840400d08030b03016441105460801c0c1c84900440241c0da00946280d46040d0480c401d5002217190f25190545134249500c4120b403000007608006020803001d52500d02c0c90414199402034808050300007071135000044c8200304698240e0b120b20203500180189040c000d403100780c08004a01d0003114036205a0800748661589202840c2140c0030344050f0342e085040100a40c844544e9005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 603718372 1250 603717122 603717137
    0x181a091203070501090507090c2c0109030804090f0506060c0616030b0324070c030f031505100306030c1403120a0215151305130f03050c0a030c050601090504080d050403 74
    0x250280580c5c10810b12940c001d05529080840300000c0d9020f0291540402648000e21444004a2442c0c0c00d900d4441140d41c4100e084007034012610102c16801c090180d8400140014a12085270700021506014840800c0551a81c404102c050310520101900550101011034148800150711030003050042c1000112034031a40d0119040048110300c464031030490b181004245120f551195900100c5846c214041400c0340e5806400f201e488100710040507076403400d481602500c88131050160500400c603e20106089000a000d0700150000711118070340c1c4000024101401d8980d9583c80d0401405443d006011059000035608141010030440c860701048106050380390b030a21740a41c445005140303070200580b0611a9900c100359158845034900000c11890042c440b1101014903440fa03080a043c0d09181011111070103840321401c414080c0c544000304054200c00a880000e01c20025074a00d680e0310132881040380d4089a010b48443c0e400c11404914220300da10180d440b80c800e040c0b120 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 603719622 1250 603718372 603718387
    0x5100819060902031005010219140a06050c1c110406080604090605010e090c0613050906030a0506090106170c030a030c0f0b04111806310c181a091203 66
    0x141e070160303801840c00b03035400402d01000d040e07a0030142014220a000900b8800d0348207401c6082040d81c184003910380b00b0580b03000700c0b1400c070074012606c0b0190400000d03c898109008102e0342b50b4007043c140d00c0903104041001110704110f02440208040b540401c078106840c010054641a00007000e4940c0103030384003903620004440d8820a8040d086a00111580f40b130300d003680d10b02e07110b003103a80e8a103e10418020740302e0010b8404081c10990307c0c140c50964003510342c2d03800b181c501380c800140203102d8000c0504120b161007056020b80c0844062500c81c0441d03c400c000b070645c85001074017005415070081603071540824000e1a002c021548200600404955961114000c8030381c107a50407200e034003001441e5000b1f460041c084840061145480e1696410003100240050360740c6c0e0b00108104c3c1480361441d40d411500003421030f0150380b030300342070200d109402c5004041041582180c15000324000001c20100c0902e514079011540c1d03103200c80d141c0b0406030108500c503948800100f0141c401005440b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 603720872 1250 603719622 603719671
    0x90d0f05130302130b100e0607030c0212070303030b100311041707150906110613140c030f062e03080f04150c0506060319060b120d0c110a051008 64
    0x8004440700e007a00040d03440041e0041200760100c1c215040100040d02107c0c941c2607545104640c01d141d8181415403a0310114400b084080e0b0200135aa040380c01100800428140c01d07800107241004100e507183e900d8550440e0560482c2d011170105003114500380401c0c0001c525407040051242004c01c02c603008140c0e255800400600e101c00c00c0d9000501119040000e039401107808050f10710600003030b240600d40000b180044906070800902201c0158071403030581001400300441070b100c05019540140040c8410b5980c54809985005901544400c10082d9801e03d41c4001107041137000401002d61943c0c07281c8400303030002502039071a21000c0000160350450340317001541c01d081030344a441540c002070a1890424400400c400d0080c1c1181a0b20384211505c0c14000b2001d41c1e00c00e40c0001c41912000211700c1c00000304c0100204c500c0b0350a1400c0c640c54102c001c80285511a40c0030680419030b90b024000c1c400da1510410b504512544034101180780241c0b40d41707904c00d9103008052041c800c0c64408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 603722122 1250 603720872 603720889
    0x3050702060408160609240e270c0a020a112209030306140d03050f0c010e031b0a0b01060c14100603150b0d0f050304080a06020a0206090d0f05130302 66
    0x155905a11030f26044d1420505440014000d2901c2e040c16130790107103004050792418020045420f043c40e0104901407030301d80610002c1c4600d61000e400340509030b1a480d2050700c1d90035480e19000c01c002d51200001e15001c1043d04607a5101e9a80e4003400c4051714a43d100100380002c052000c1c0c0c030091500301c0c4034030160a040c00c031000c280c0d08540450560024240035080316025004210703104030741e001d006055180e010440103008da0503d0b1543e910070800468811500407188021829403d00928201e5414004040c00070044c5400c0281c03034a401280c00b81d41d4906918400a0071489120010094103020b299065511401410b40842400160071401d00300680d0000395801950b5a100c00d00a00c40c0e6042d0386035122001d04402c110503d0602c00046000a110000500f2504034040d00c404005050041d0340c010541e00d030071215490f15510306117000c0e40150300010014072424001034000100000c000b051303160562984001c141d1910012a09a40003000382c2c02030154940c400001622070544 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 603723372 1250 603722122 603722129
    0x60913022b0317070206010f050f0a05060c1509010207020a090c050c0a0b0106231803070803041202040c0305070f080703060b0706021905040b0f0304060f0203090c040506030d020a020d030507020604 87
    0x545000200342003441c3c62540c2c00240c1401c085500800c0144201d40d404144102901c80031103900005501c2600040e4030840245c0101d42c1040c0c0100d07246420788800541c03611440b102200000d4036580e8007140d5402c07401882c8000e54408110601042112415844482003062a16102c1c0c580440004458544545061300f2141e104e101c81c010082e00382d002d20600744101c0820000314003000403411030340c102c0c064000b80080100b00d84004030020781e001c0080d100140200b1040e41c3c0c94940d03c09280950b5201400181d00850820900550705446441100c5c4604025100e030307044100010400c4604444c000c0607217081c150b031480045842080b44018215040c030481001d640c48002c00102c940c442000b81da03020034030a090100b4042141c4020036a01c03030b502180141c90322a0b60b242001405881e5107018684000d02c00418048501d901149030342d4180300585007070123a0385403041415030340d005030412200140c00441c1842c0042c90071148903e40e040c000d207010307814802c05400080e4540d016a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 603724622 1250 603723372 603723377
    0x170904060b0a020708250b09030102070b01090c020d03020f160206090303070602071101030506150c1603050a0611090a05131d071e0b12130606120b060913022b03 71
    0x10040091450401ca0222281402604c10b08540c1c41d17861091481c811b503001e030207010781c40803030800f40d01d8900f50305071200c050708184400e43c0c650390317500b1010043c525860042c0060040d20610440f950007402118500138850340102d142800c040c0700590315180044040364000c0040203080c885590030070150520700d001b050010782d03440c0245095244c0300c1c4130717aa205045c141007004001c074598070303050b07030303040c100440341d2043d13610911900f13460700f0035490309030800b00040350582c00702c2480700c005500014144114401c0118000c03c0c0f1404000e402003464041d840040f100c420302171743c00c151255822040082c040481e4265030030044102c0b411a16504082c580d10110041284440c400c009001d02d6004042c0030a02e682041c4115503144207044031540d110b5000c80200f240d10900108040380590422010045261106858050b5407040e84c801d032030b00780c000700c081480c529100d06114002c40100350800141510b80d4244001c0001084c2407040d1100038101008001c0f85c0f010910f00c5081c0b20343e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 603725872 1250 603724622 603724633
    0xa0804060f11010c0212030c1603080601020f06090309040222060e0a0605030c190e090a06090f020324130204090903030606111e0718050f06010c170904060b0a02 71
    0x160030082c0700034604541699542c0c1011500d40541c0d4010071000700490300c25920b1641c80c0d9440114040b5803241c40078010340504402e40c1c010070305070b00c03240550054509a00381c1d101c078140390503000d44d202425101100c43d50803c1004800e1841c250740103102d04c495003d03580340415410445901c3d01c05107030b40003030b002c20318040c0031011520340a4414000340845042c1a419418884140803850054254503029513a241744401c03410303070007549410421080200021010300d001c0c2c0d02c2034054422480b42c0e130261400d2100c40140b0076640d00940344070340ca00b144a0303100c201e03a6580090820003a5a1420f0300000d408c1d020303603841000d500091020303103084070000c510303000300d031034000c1c101c4816901c09020440c01c1c0c140d4a0b0032070303004104035001c3c030440880d00504c920421610b43c01d00d881d079841003418902c054a040110109034100e40d101c0c09980b0041810350760307910015142012802801007030444079118040c2e0032040c0801030040a6006040050107179203070000c0103401d40c003501c158005039000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 603727122 1250 603725872 603725897
    0x4080609010c020d2309030d1d011103160c170a11010306050612060102120c0a0218061810090212091b03031b10091b09020406090510020a080406 64
    0x90040300303207002c540d100412494a0b00103008040c00d840d950341e45980c5004031a0f03041c9025042042d1003c480c401429140004120300000d8881950f40c0d8400c1032510201006202a6001e43d011a5440ca10340c805035183c1005514603035280c038220642110f08000c450700c00b040303443c2010354030b43d580f4840000a095140e1582445042050342c0403c081c105801c1c50381c240035170303151501a11551040409980b2640d01c031000141d040075903206500808040104c7c140a29620000350b0f8907046000b40ca1081e03408060030a40d443c0c65004480441d080350040888029060b800b180107540b0a90035140c1c100e0f001d4a803803020007aa40040d0070891100101002e0108000050080350351150122a114000c040450b0200381c6078041ca00d45c80d035601010125030b0340c4486081c040c049020303142441c10050415286041c031203003210445581003d03c1c4035080802c080070380c1c1c82264251003171603c5034800240340c03804011181c030510640b041140940551900003804440c0078101800058035021060180c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 603728372 1250 603727122 603727141
    0xd0b07020f150123030a050102031905011505120405010e070f060f020a021005090102010209091008060f1509060f090f0702010b0a031115070f0503040317091e030a0503040806 77
    0x25034542c0d00c070b00000000040264280040b60010b40254490103100d60391003010000e41800060306002c2e116500010401583c60820070301003240b03c1855008101d40c1c1d880d0810845c1242e00d000d80840411410000001810740703140c0c0b11580700c0e00c54400421613183e9010303401c2c10f0285075400740c08040030010003400155000003034039058950701d02c01071000c10f1040e00020001c00c0110340400038488005104809a4400c0d011103081d154050030f01ca8103400c24140000d02030500e40b103a000c981c00b4140110f0300c0148248501d80c00b601844aa09c42c3c003442d06020071040d45000f6008a0303100080c0c000c90101078a468200741e20641400480070300902d48000c010b42911200f0403100e1288500400a000140790510116040300d41902e00303440b158408029000c0c0c034403c84502410a0b018401c840007080400001842940e20a5250516541405600b00c1c46030045100c29a403000d050707081c0c00724522a43d15400c0032000c004013120a92615a11030b103086a1041d04010010341000040148411 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 603729622 1250 603728372 603728383
    0x603020a03180308190e03070f03080f0705090f0406170106050a06141902010b1e031e060703050a1e0b09010b0a0f11010b06040b2805090f0d0b07020f 66
    0x1400c01444400c1c611165400400e04c0c0001000000884807000540c000003107581c1c40b00c209100444216030b6280401d05108040300020031003103000074500303400100c0340d4401541090203882d0540354581070048030800c1194600034000000e801641d61080010004005d00d41e41201c481d041d00002000c50a040034816201040e81017801407000e21018003101001003422201a030804200f0b54403822158101280501604065203510040100003041d0501d05804245000b03d4100d04440c01100c1112101c401c03000c42c024100103d810200000381c00364000d4022030f030321102405001420101340c40340a81d02d41091408003002e03c1c2d95040c0d2001c14105220a02d014210a07c08142000714180c4010032007002d42004000b00f2010f04002a8401c0b005d40041f000381c0d0008040b51f40312a02d80c0a00c0c15690080d41c403000914000c03031149002c2001c1141d409820b8606507a49a2a0513006414804128040900c141d04a60755003103203030200c0c17075140390140110000d602815451200030710151501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 603730872 1250 603729622 603729641
    0x5010803030c0d0203151839071511090f04020f1e16150f0614100908010204060809100b0a03020d321002072a09060603020a03 56
    0x1540100180300c0e0b420b80c41016030301a141d0003000903a503903551b20002050300f08450505500030884c1700961041c02d04d01c10b80103105030203c1d001142030641200004811140458500040b41c0286004a054241503c01840b000c1d008013200d14a007000500110121008440c005104d01004540040e0920b060340c8825100780c8102e4041d406c00c0c00d060490b508074403030070034050414180c801c0c40c1c058038002c20040d10903002c080c500d0446810340d1401d102c04245d0003000c19824140c03800705441c800449074890b52003541c2e900005200c96031100ca0601000c8819800c90105220400b6400600c180c0b00740001c1c4054000e582e03c903000b40c10114180c503c0c05d48148001c2940c6810083e00350b4684d11240208000c880e011110715100400500b030541c1000b500604880c40a598041e0b4100074022400850f0540c1d002e050403100d1030307031501031144203c1c05101001060991114400d2030103043c0d00101c800c01003889400c044030540d4644100046850341e601c080080b94001c1088a8950380600c00c00c94032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 603732122 1250 603730872 603730889
    0x5150c0a09050316170a05160f061106010902090d020619080106210b150309010b10260405070f0311210c15090a06020a051b010815010203190309060501 67
    0x800007a10613100610b11140903a00001c0050000e08449400c100305045c50f0710340140580d0090302c0e2000d1840340103c2c0d28020f00103042d214103000200a40300703d0b1401090003003480a08a03903420400b240029502079880b440c3d020800c8100c5901599401000303000100401e66a544030100c080409810070005901880c280700300c1003d03140c16504000590111000d107030304d0000300e00c2d00c5031000844d0f03d0040c1c050300f10b01a8001c010004139030300c1548414026001211025142c00c0301540c01c5924403501d6181d90301050410100d948290158064684c100f485070b015907017050740380c00980c002e4100c4c0c1d600a54403074460300d030207900038100144c004120444200b500c00c0e07070740032403403070f5a59034803010300d125008003503c0c0a940201b214080c140c88131180000c10704141f050f910b0000940e60601c2c1c0c1419a840e0160304200b90b03950400a4104105c031506845444113507807102001d010f6a49902c0f500d60542c001040040010314510000070205280c0c2e840010391400b0a04160088a00503017245a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 603733372 1250 603732122 603732133
    0x708010f020c030d020304030302040b030108060603011103100509130506160908010b06160f020406060c06140f060603100b0406050a11010501141c0c14180412030905150c0a090503 79
    0x290804048121680ea040d13000015035030b03458514044009104983c0080034080000c000840c03030900c04907905008800450081c0001150301a2042c4144425101c80203420120314007004542485107169600502c0c0b6890340c551003038103444060400408542d80395400903800241141250482c0010010300b070500000c00103043c0c92000308249110b01041c800208413940840c000704604c01c03801c4041507502400a111156655401501039240c0d0401294031505007104200042ca07402240c0344550754000345800c01e52103440c140210703540050301403001d15440401c04981c03013a042c401007004154540d115551071074030301d01c000c0040199011148036039060200403c490700c0c495405960002048404c60000c440c0302c440d051114883c410014511241010005002100c0041001d107040342500e10b080d121b484001c0c040c0215408a40041603074460001107100c041c840c1d0700180c14184645d040f600c510a08841d142a00041156240d80581d00002e8000089501c804000002d2000760003c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 603734622 1250 603733372 603733387
    0xf0301051906020d08060f03012414130915090321050420060c07140103230f13020418060c02010b0603011e0e04110315010605030610090f080708010f02 67
    0x7516001402d84c502c0c00c010741c2d2404210160346510781c0e0052840010020460509540315a10316000d145440c0480c101100500003070f00241003504007010140209400300110074040940028400c14505807030b07980c00f02e4a480c0d42582c0740c0c480d04d41080e00a4480c0c66540c0c4085012045108000b0004210070b800d25040c0000945202e8401784c840700c3c07030000d085259070004089000c44c020180541d056215140f000941e044030354000d146c00203003c1e0b905100311141d852140304c11038400b250182420f4460800210200000b1001a0f04858070000c03184500c6032940004050b00e07034071102034070030030604060802001a03501ca401c048004900003400702e8419000003034514041441590300a050300207c2d05840702c0301440100203010720746002c080506150607c1c03840c01c40c003401d000303000f88100c01094070b04254090309141291802d58500d490355855006014004101304181018040d12002c0032540c07042c20f070000e401034080b25009000302417400406d6420b59440452604a0920400086 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 603735872 1250 603734622 603734627
    0x115050702090a1d030a030516090501020607030f0f020703030c0807110c121606020318011b082a0109020103050f0402031e15070c03170105011e12020f0301051906 72
    0x30b5103c0310001d0b0010380c075840b10310328400c4000740c40c0288000703000004460f0101078059029902884c8403140d40f4801c0b000202050b0b0f05c000090003090b01580c040c000280d1000d1003500403400f004140300d80440c0f13064401140320240d8001107811800300391500301500142e80e020b048254014502d1074428100d020201401392202080411075005034600b07225118422000c02c065580605d02040090350169101c1d030003503d80d009800510042c285081088105601c0b0f1110340c9180140042c0f40c0c0c0f012041991005499807019036018404e041c100c00301b0301614580700350941950f049800102c0c512800d840010216000240703d042020000c80a100150f2400618071f040002c4442e0680003a21070100780034540901c060003070452540b41001c010302e0380d60284400c1041c9200f0b40350041454008130348650110400d0080a00141c200b4282032100e29a00b04052001c03000d50404a040c1e85202d40b00200360b9104a804e03100010b80040100058184140c032004c00c1c3d0300a001c141d880d10f0405a00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 603737122 1250 603735872 603735889
    0x112150603090201031103040b1006170a050402120d0818060f2e03110907020c0d080d0b04051311031b0108180d08070f092106090c0e0115050702 64
    0x5203010140d440081e0401c590203075001744410034001c00070940b00d10303080c50894404e40f01100c114542c40101500000c000380514020048010401d06100d030790398603c10990010000100241d034040c0d2100d50301707180d20105201c0188001c0d0740b55942a003901c2c200780300038030340c03c0705002405043d400001040340420a12102d2900074a51712044204031400910950403802d24140d1021013500c0c858001040180340c1d01c84400120042da40d0206550312580c090380c03100f4440c0704c1c40703400081e051200700001e401e95005041001c140080002d42c8000a0041404c5400032145070303011018121518062000040350901401d00841c018542100368020740c002d4880850700d81030600a00d200401d9040d4903900408800800e50002c0f01c40121703803a4001450302c9400d0300d6903404034828150030b5080600c030b0f200f400d055408148484041c0084e202e0411700103a1900c03016104c45580d40c4c5103030000f8030518002002800314400700b4075594149080c00c100180ca000342007090010400000d401a190f9018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 603738372 1250 603737122 603737129
    0x20606010905150f120c0c1e0c09040501110408071a07171c0c080a270b2203022b0e0f030c04020a0230070b0c071205030402011215 58
    0x45258031110888401c3c044d50103214408411a1900010403e24005c04800340100490601c102c1e04007017441981d05001c040b0060008109800140030720100703040100030160480e01c100d0000030102c100c5415031405420542003054660086c038010440c012403260400040e0841090307451400003030b95980100030b00210070701014036001140410a00262440040485c010650140114602d00000130015001282d251800614140b5442d42c01190880d10f1850151070304010a042d004944419a41e44c8000b030001d80004622050400d14020b01c0e080341c11410f10a80042880f842c0c0380742448040d0b12042d035980c20001030184046070a503440396040855001c01d9030028910101000400e04007285030800d40d4215000045002d1120350000c0c00519011400e8054000701d41c2d804141180741000100c4071409800500100011030401d0071441d0f040700004613401e107401c0e0260740388101c2481c0420340901264021041009550b000010b4170180f031001801005849800080d01c0e207107049a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 603739622 1250 603738372 603738409
    0x270501020705151e0706060e0103060f06060203250501110310150509010e010507020910090b01030506100509010207210605010509240406030c080607020d14030103290f07020606010905 81
    0x60036100240b941040740c0c5e00d81d8002030244849031f00d40b654114196801c0c0b000f1640c5914101110310884014446e41c403d8940d243d01441c41d042c510f045440da24010a4015041c5441414006e40007550903c211a904031440314220b03240c0c41d020188044030030f0b59a005981401812525008240e4044210344d1446000d0900c5644100e518004884902030448000d401c0300b200010b000d0143c0d002000703c1e0072a0089902405503c0ca100011002e842056a04507004014070b106945001e00410107403a50300c0043c03040352243c0307a4420740340c81120445500c5c0c00840c11180245800d2200502900380507080584100800b41072001e4020320743e040c60f402103014103800c43c1188681d56142d0300410300840e003100b02e40d0042c945455040b42c0390781c001d035001070141c400d141c00000380c00c1c001c049510300c13164074032103603402d41e840c0d600c030500e440c0000f039412a120030760b80d12074150703061841c98103601030550350340e41c00c00d989400e0300c010f445e01c0c0340a05040e05224140c1020011999074104008940d54000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 603740872 1250 603739622 603739657
    0x81c08060910260c030c0d0204020304060902030a0f050706090b070b090f07030501020c010f060303050417100e010c03150b27061912020906040b0a27050102070515 72
    0x14203810803008541102d078104400254544404a2054039101900144000d44e0f024480810030181c0e2998500440c54001105041410240c40c0035030255501500031600440d120000344d001030305058148408503640f001034560102406001c03c452009002c203800c2c41044036090071a0020755015044000f00990101c1000070040750307081c820f50451901032001c8946032602c07441d096001c0d40040004030080e61078546140106003e03801500d080381d4243c0c0b20145098101039822011050b400358404c0c00384519443d81c41800010f1040031030440418000046200480c9001025034002e810156a80c00b000441030101c000700030122614050030302d02d196044108250300c80404c5100807a180d03800f0034080341301807102d261000d050f0340d2004a03540e00c80007003020084440c00ca0046404d00ba07088103007444180403520901006081102e140c3c2422000650540401d50100841c42c0c400d40d5081c0100c0d008000350350701004400040c1070203c51084951800c00701c9100180105481030a241908 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 603742122 1250 603740872 603740881
    0x90b01030605300304050109290403080d050601020607140711090405160b0304080a110102130b0901111b0405100e090d1b020a0603020d1104080106081c080609 70
    0x9600c29002030030080c040e94920790b0952002d448910f6811030030040008103482e881c81265010040310140d8034140c650418190401c000090343c2e407202d00440042c10b010384a00d40e10182e5030406000114400c0d1511661426071655807000d81c2c10150040d03055504c6401800b0185411441703000d1300000000f81d464480076142003500001d40300d40721281c0c2252503042400207104010800d0100502040d8201e40c24903528005661030344400c0710003414004081c082d0b030519511030311000221020203030000d0309000e0038901e118840781c159841400b48800000d007000095810061724400451640c0c0604812142c03100660380001100b440940711700d81d0b1ba40050444203c3e950200c0142440303040005882c0781611500d41e595101012020214a500c102d010803c00251411011290301811220710246812401c4e0082d401080e1500c62a640701ca9a0905042c0024050001440c41d0400840c0c910710f0040118100442050440e40c5000301c525401011908600701ca41c002d40300303a500010300e984 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 603743372 1250 603742122 603742127
    0x10903020706050f0706091a0105120a0201080c0c03030a09021201061802070f050d0201020a020c1002030d051008010f06032003030304150b0909010b0a0902041503050a0905061f0915090b01 83
    0x40000c010b080340e10709440b91f01071220340304c0f2802e001400c4002d0720450fa629082002407203508041200e41d183c2c809442c2c1c0b401544100851a003101a140da40360070300000c901180d0640e081241c0e19075281d95144101d5041d072512286090080c002c0d84000c005403820a0341c903010f03590a400c030b078205940d0006040b004005d000e10405030350542003010b9520b40e03010307040c0081c041c1d4040322a2000504c034030150312610b85080c48031104102e4041d00298039012050030080007030880242154a0103001004c0000d0080082c05100c00041c0350f0100001c07082c0c01d516006c41ca807850040c805443c600c08034885070700c0752000000c80790042c0e000b6550643c000d11001000001e00f03e0250030981000c003c03403e000c000b002c1508400c0009400b1a1401c07a101d0722400c3c0042240254816607009000400000c00076a0103030340410340003140103102280c020b5030358650620380b030415290103203545440c0b0102c80e05150900e544601400d2008410b00c00e0404520300303030241200fa0b0151900071507803011810016030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 603744622 1250 603743372 603743377
    0xc0516050d0f0c05091e1012060518060a240b04030f0609060906050f070c030807141e0405010f0203130509070c1a0603012315061b031b010903020706050f 68
    0x43d0080c10720501b8504030058181100c07a0305405220b00503c4000300d0f22082070b002c0e912040c1d4560300398610350036026460b80c801400380074080a02e810100010440084000d00c09544161401d090100d950301c0500d1704802d80d49000c50b0788811141003508d0500c071400c0c0060880701100e8004074110303a6a010360419030018080090000d251510b0944008100a00c82c1c02c1a480341d4001c002c0d10706c40b41d603a00000e940011403002c008000a00c0d40002901031401403441c00c05007002000307114101102500038000004030701104180d56100498108002d6070300120210303922000f44083c604044800c51054241001401094031404a101c00a024540300d107180d0550203401480c03182c21000c04800140c4411030649542d8060b5080a06c00240690b5844148080c00000d802041c4140c4d9003160510243c941c5100c0954014020803529001c0600b0846400c28401c003940075560722801c140d00a4130b03408495000c4c1d15183d04000aa0000c81c0d00442c81d4801c41e6001c1c1011035454040b98020340352403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 603745872 1250 603744622 603744629
    0x3070203040f060e010905030a0f081303020301020f0309011104060504031104020d0f050709050d1a0406021c0b130515040504051009051e1204170c100c0516050d0f0c 73
    0x504442c100000d5081e40120b0482844c242a254090140d40312000e05481e2150540080e000c410044030741000510311000902c8040003050707841002d9520381e40041d003680e11044e80d00304a214040240100b4001c00c0c4101c2c2d16071801d1042607890300d03140010140040c001c03440060310300418880540e02507101c40d0129100c038031007041e080001c40303800009000100030a4078083c0c001140748402003141e040c600d4014808541200d2840010803071310702c0010a11b4002441105c04540034403440c081142e0f00340c00f5003088a43d01c2c901052100c01c2e503050000b4801d40140040e05a8180428840d40340400e541d00c100005054a0108841e0fa603801c01503e0402c0d8030010103906e5141886000600c203010a200c0c0d51040010111382031111135001e4555030700c18030860200265000c00041025640c58440c44460741c03940c00503940021401000500ca9503254004032001c640d01c240785a04012043c01021500b81000300d421440d80d0525020840c01ca4100100402031850180490144141d0214900c001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 603747122 1250 603745872 603745889
    0xf060213050a030b04060e1f020c0a060e0304090b010e100f18180b030c010f051e0f04140405040b0118060803161208150d110a09020a11011b03020307020304 69
    0x850f602e113400c0c903000a084405841c2503260607a07561641c0c80100e400b550300f18034501100504072090301c80400035400700640b442c00b482020031100c005196070107032400800c89170b8042d64172246010704000c02d4070181e201ca20704107c0700741d407100e24640e00c0300b203c2845134040340b0700b021503036035004829039402901c3c05c0707040015a00ca003400281c2d01c0b00c40415003141004e401091090303196420905607078034032000849020400200c240c80e516482440908030425100703140e5000103001401883c01035000210040e091000007506020045070070f50190400c0809860030001450192952100a40f0602483d421800704241c01103200707280750401c2018080680c2a203035510100e5138951103c442d40101110840b00284441c0206030090345954030a0030307400c00103ca0f42c1051400c05c0160f91450741c003128034030a4501104c00395151002d162015100b05480180e98a1a04401a211360b400f2990f8290f281c0c108200380e40c00226144001680c1c41040c2405a140e032900001a8114061a00300006 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 603748372 1250 603747122 603747139
    0x1e040f02030609101103371103040309060c0512030c0c06010e09060907150c060603150b040f111209070e0702062520070503011e060f030f06021305 65
    0x1030f2036008aa011110b919004042120007144081200c4a0100325001c0c151906d14010700007004141c1001090381d030491b42c2c600e01501e0b0780000003100b22030380680c3c6841039400220030041095044900c41c00544a14140b072a00500e455583c07075503070a030040407a2030582e00400499540c40042c0e00341d803400b03140c00301900c840f1f6031103a040860351807044410034090f10840021441c19200816501700340c070401e0003a5159101142c109580507003100408903210390740e0310000404a002000b241c40c0603000b4901c0420302d007070100200030543c1c012404540303a041c5800d03807480d00254840221000c1c0c03070302449020070b1a900c00303034001d040144035405260751580e0441005010780d804100c413403142e034003200f01c1b0007040d208200010a40c0008031100010440301c4000d00510340302d904548503400e000400f183c15264031440404d080d240420090f840b250011801c00d0b003805524042d04015000c1030303110414003491a00e50b04915092240d001d2310702d503030004154006c036000b144008041c240c058142c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 603749622 1250 603748372 603748381
    0x60a03090201120914010f020f0406030b030c09010e0a05061c0204110c0304030b0f131106070507090f020417030a0e01080a02090306010e09061311011103040816050102060903031e040f020306 84
    0x1910004500c0c40505d551030301c3c1c072030800c1075602d2090700c141072441c150700d40c02c0a040040681c000d00c840c40c00a0351510071164034042656821200321f010b80060003240000381040014031090b52409030445104500c0c1d42c2a104103101150034415070140c044a01288000342c40010202500c107044410f65603000c00a001300a1050809589005141d0303c0ca5000280c0c2d038080c1500205184400020561100d0100d42c50742440c20002078141030303006034145e5002680c1c0d00c0788031003110b00300d413508001c40342c001c5410448441030034082c6241c440b801000d945044510440144000e02e9525200d040c060700324003003414150260b065962001000d4101d442e03558403072a001a1620341158200c0c0305128920000344a020344100748c0501710b41c010a110356554400c001520745501d00e408120040c80b0620000440701c400304018105144ca04125490460421000a040c00360041c44082c65038001c0041c0803441e2002480036444a072940741c0d0b0040360320341d403910003410340030800003940c107200348800d10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 603750872 1250 603749622 603749633
    0x614102d090e0f070e04020901030f030e090103123518010e150610080a020c0f06040b0106080702030a0801090908190306080c0102010902010804020913050a0c03030f030209060a030902011209 84
    0x1520941c0544040f5080c03103640d41d000205c00c55044600170740101c440c00040000445544041700302510908201d10b00050b844082102179a003607106a43c00074425144400450b00681110798924a241c2001e130a40701662415007000c0030303031500c91440c4560000103620750419403602d024101d1840024402240e4081916a82d50720800c0151122201ea101055032450191404445034600b51120070259590903020305c0290410010b821050013442116004240240600f511452180e22035003503c1d4104036005114040085c01c0100b9544104461444160003203201811100c02c140301242d201140d14202030b85000f0603414800c0c000080528102c0c4640507003100081d40d89010854031147d1042004900317940c0c011b40e02a000c161140081005414007500f0b09901409405651542c040c03940d4a851400c601e50384141c80504201005008055003e600202c443d5010300c2c0540c1410100c9001032503612403030250105040e620020b8100716400761100d010f00c03140b0400204080070990405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 603752122 1250 603750872 603750883
    0x21e0604060f0306050a08100911031009060b090919021f03020912071a03060a0e070807020d090f05010c06140c070510060308120901020d05040614102d090e 69
    0x18034003c00d003030030710201340d40c20040c04520031100318100038441400c10021031001803006c0c4200383c4020319400b4841c08151000c10580307041c2403e201000580e45541d040ca50100e401c0b5000c014401c1c01c00000f07000c8148000203c64108038003070350505038000050300c00103210100c54180314400b984120803000449405a018107510102a100e43c41c0c0900320b14111a03c8034194021101c08120382980005a400c141018561048025049054042d00d6040309906410110344001c00141c080c0100402030354140003011103d206402c051120318104900368004000d40e005003410498a50741c0c00e41407145036041a114405035645001860808042c040d1090303012a0059a0340c2c441c604030342c4c581d0016442540102c82e00310084904082d802104e80c03103e80c5001c1c01c64042990280100d040007500d500c40d07140918459500000c070f04410740c01885020000804107071001d2441c0800300400415154002e50710340641521000315242c000042d500d0a143d030b001910b1070744c505410303d04030020000e031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 603753372 1250 603752122 603752147
    0x6070221100b01111c050904020c0a06020912070f17031b07080d140a0f09210c0e040f020405101208040305070512120d0f0f06141507021e060406 64
    0x1e130100048131a03c00c4980d9110101011881c0307808021490464502c214003600c040180104054074100c10400110300c4d01c4d4070b441d42a200e40303034005070b260085d1070b00c1450703c0480c80c1040094130915140081d00c3d0151170701c83c401c00340d540303041c180500d06202d000d0040b80c010030060700161080c1c5c0680e001c01079854810740160309030341c410038900c4219140248440d00b80c4034816412586443c40c0000100c84850f240513440c0180b05101001003002071000001c14501c1091040d02440720701d00f81031001d00b810341d41e0301c40401c4080020a00010440800000d000150152000f10700f5465913442c00c0040c3e0486d40c802e04400c0c2c8400d007082c04010a545c02002100c0c041e40032104d41703a84030030030400c1e1a11540c4140b000799102c05410210345501c1c03000752000300c0803a24009101d00940e140d0006072028184013024050340d5807410b006548542030140f080c180d007070701d02c40340701d040956403c004d42c410190003900c101644000307008162004100032040200141c880c0d6200c43d0342d418060030341c254144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 603754622 1250 603753372 603753377
    0x7060207240605030a0206070203120309030307090506030f04060b060417030c0705030c01020319050d1a0a0e06011407080702031f0c020319030e10020f070b130206070221100b01 78
    0x150709062003619000b020161900140a0b1814181a03400c100030f0f45c0c400b68080360580104003c0c10345c19550740014620034003802010315540d1500d131030018a109103039000648507200c14410f12000c0142802d80031381c8070394800000a4100c612900240041c02141c0c40312041c880c2480d500c40740b420707021018084880d8040708403500581c903901010344505000030320f54010390091083d43c4001d03040364460040404d00c0d04201e85049505000c400689142c80c40400c1a0a41400e40007654103080e21080c0081002c00065006802c2180000b07244800036149030150020102d5810148004a011620030700d900904885c40304031544c900b4000441210491061a80740a1030109001d0012003103a031803403420844400124140b1a00394002d180c0c2440001c220b1040d41c0407a01c2e903130040d2000b40b60800c0d10f0703440c0030303222155071030711070b5030751400800701e0504000c40c030340940c0142c40b58030030365510650407034500d5a400300f00d070350903121881c0c44280c105640c4580b1b600010b04c4440caa1168000c55001c0c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 603755872 1250 603754622 603754673
    0x304050a0c0602011d2b18141002070b0d09030203090d061d060108120c011d060a0605010516140a060204090605130b1008060f09100e011e03120507060207 68
    0xb107000c07600d4045005900d20051ba1ba401d0102d040200070304107000200d400e06001c500307540000040c550440b000c0d00006401d4024100b48021403a0000020791840c2881c0f0042c0402070800310f4074003440c0540900801d16070303101c4000d00d08060090054030b0b9103d002030655a146079032030411b6800b5290000c202100301e552650700c24620f0001081003810307204d0303210040c039041d0f01600903020140c1c410702c4041555503992650200c0318080541d1550007040c0e041c01040d15040c0030042500701c5019030f01a82c1880b404010350303042507400b015103402003908800101a491040304c5200c2c28024a040010004e80c0300042c0400c1d4a4015801074094450640d20036040001240d4100200c66680e4541940224507034812502e8902c20980242d015201802114a1302d5445011031044e00c010384400803401c440c150184280c210b8441901e00424140f07000030720b8180300741020a0003e201d40030152014011440c0194003502030022120882e40c004400c550b0740707aa50a119141d480c003143e880c0d00726101c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 603757122 1250 603755872 603755921
    0x914010f0c0f0804020f060706020714060105040b03060105090703021603020307050c0616060902060f0706290604230607030f0801050906031b0f0901060c030e030703170304050a0c060201 82
    0x2d0520b03401e2041d034645590350b4a4980f0f400b00f000701c1040c51003051f807002007042048001031640c0054694188100610030307134407603050001070038080c050700700d140981d10381141c468581d9400035590381110003e840c8044281c4481c4000c401038411079017518041000f032000305040540c0080100b86160094040e214904030b15010800d0910803484560070380403013441d1801c04124940d202004203480102940c5c030746440d80c080541503401841040d60907a644440706141300100510400208541001c5001410400000203405009600a504128100c60041c035410900b034003081002c07110041c142a01c4201c2440c00510020520400b400040d003018000505400c100707918901501004001d4114403c4820003440402101400316a01c0749040f4111240c2e034031889061401307006541c1d1600310b4840c5604014298014020401e400790740b1000341003010030041c100d83c0040d20b0008030042e07617035121410114500311612501821040c01603070001002901540700e41e024040d0510b1614400780c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 603758372 1250 603757122 603757127
    0xa05150c0a0e041b171005010804140c18091507270513150b07020109090e0c030f0304080c030114070c02120307050a060b04020a0c150914010f0c 64
    0x24199400340480c0820300070202071a000c1c180720405400d02410014000ca034418240000c11100112040881c0c0e100003c0e840048181c0d640c1e85d8820740ea481710b031940903d45000240042c9000b031015101a101389454950442d0a02c002c0340141401000030100904600e040c01103650207482c100170034400c6800c80741d5183d8002803910311400d1180c0307903808a129208042011158607009010705884107090104107943c03851b144280c900f4030020700250350464803140c1c0810100369001058144024004140142c0e4080502c50907220210004642a0100611135280150301000c0650600404501100f01c01c0004045e1007100c1c0350341d0848229210702c1050500301c8695111000038030380800005500107000d0b0381030040b86440501040781c100c18038180301c0d095800071003048034240c00403e080000e02c401c5004010502100300d50443c0303005c41c4941c000d0b01c00c01d01c414004101040c0e00d07040c04802032156001015081e084500a000020107c281c1402002040440c8d0790080c5445403500f00d051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 603759622 1250 603758372 603758413
    0x30409240e07120e031e04061b0c0b0d0204080f2104032a050a0303020709050703060e0402040b03010b04061e080d02030a141c09020a05090c09040902040f0e0a05 71
    0x507161548800ca6030640403280c06070042c44031300781e800c0c0700c1085076490000c046031402160180d100d120a846904114000700040818010500c070071454030603d0000c1080b817070020040f1a034290b00d1681e1101c034200d00f00080d019560140d00c090080207004081c420313000c2209040c8611184002e0503c42e511121a200740c090303070202400740c400d101200b0b085074091002c54a4811191031180580315960303000100607220b00c6d00118016080b04104001c04e10641c0901500140a41418000d50f414000400c1e03080d000144003070b2099454030002051a1402c7d0710107201183c002e48203001d4282c582e0648001f041e0b402c0c280c06a12201c0c103c00242806001c00c254910101c1e40d8051407a214242c00112107a01c00c0e54042d0743c0c0e800041107411501680c9900e6107445103030300140803914089500400c0500411a031106014011503000c01c880c0350825000c4071411141110700103540f92a6001150007881c110105aa82a207801d0942038081070018024005520807412201190040d60580b091503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 603760872 1250 603759622 603759631
    0x504020f01030c0e120106150c050d05070213050a0b27060f0a060c08090901090606020c0411030703320f0702030a0c0b0a15060302030a06060201060b1209030409240e 73
    0x1c8000e06001c14034545240548000c10300340002203007082e00c585003515003008c456142c40100d010202c0f10400c2100a100741031641e840340c14018200016900403e0001c0c41c1501020065a8ac1e80001202c20311241d000c55418440030f0015110007020220140e440070410740c03640301e19946000001c98610b06052000c09154015066500862810000340d403101d00a000445800b10b05000055003501c544101070300030907103000080750b40340c03034244041e00381040150701780d01940c00d0100030409100941c045a80101d494230380002c6401c01d2a80c4614826182c43c5d04160040c90000d4004d029103490300c1c0d450149803014400c803070395110700c0c3c0c2c1a0b0750f9114140c4c101011511000302100860620541d00342d00190b051030124100c00c842c924650000c0b480d030002c0380802d901006010b4908054403440003d04104c3c0000c00480307041c06e1008402c0e008804495050b00311b0200042c3d90341d0304c184141e80080c03042d03040074043c2c103405c12002c06248124000700c0324020750a4400040326801c04100300d009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 603762122 1250 603760872 603760877
    0xb040f1a070f0503040b0a1706120601060f1b0606050306071b120c211b030206011517010303090501170f0f1f0b030906070207180902040605060d0504020f01030c 71
    0x80950700e69940d078888008040c10307107041c0018003001510604900080800140d03941c1c84010a11031100e083c80703000c10240141d4000c400900818550260003d80c041c1900c01c0c600b441c0504010b401c10450345a061100e00e04c05600071000c1c04020000603410038429100110305032007c03a40c44e540203c1c0c000300e005c00c00001c5400e0490b41000400c0191501242800d0744d8681429020080d495800c618040c21126083c0740c26041003502260758000300c40403212408407001d01c601c1c4810384000b50340e500180038134a030526012a54105485c05180c0c0c83c0200e1520031001402981d490a02402e51800f034411103010402d15034900f0041030808506600c039601070907030b65010f916061b40c83e07403c00400a04416442c1202c0d421048801c20704d84200d8003c21140c0303051603492a00407081420064090203c40555100d80e60500c044be8111992480380c07075540e82c00043c42d42403400050080c003510b5001c90f400110015044480d0b04e140d0304428440c60080d500e9209000324000118100c1d283d000c40d1200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 603763372 1250 603762122 603762127
    0x1516050c120d0807171509061c02090910061d060d1e0c0b1903110a0c0b040f170315030d021f09060f0209030706030606080a0e0f070b040f1a 62
    0x15030b503002d1200943c21400c41d18000040c864000724020f0041070a0b41d8410304e82028841307003101403070502c2d05613074807000c01d80b10791078800c1e030a0710400000c05a1034402032191070b9000000d02e40c0041002040c510390f03a0301d0028407420f5170381c81164501074004001c42c07403040030a4001940c5130500c0421100c00641c403c0400110703070401c106050118034100303021517803010404c0c4e000410b50004405441001840c540c1260031303800402e0081c0803501c403501d010480d02818451500115002103034414216040083d00c00c203a074580c0fa00d440d22400d184001003401d9000c0f9030390702025451102451141007540508501d04100b5030806a4820500a0540060b4441905158514980700c101c0030603010009010070192003a9a40388103541c10161410016070340402e00020368601040110b000b00001d0074100134031410032400601c1c01c0c000030090f01ca640d448140c8203005120402c0480d92092001c400c2e251a84d8650652118a80c8107100e00b054000c0b001c0d0001c5030b0306125404400320b00000c6690940f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 603764622 1250 603763372 603763393
    0x50601121203051f0e070e0906030d0e1201020d060e0f090d1d0310020904050f1006180e040c0503060a0225110a0e012102090f061516050c12 62
    0x5010340030091040036584134200c800090902c030b03110071401504603110390341c40301d01c0c281e00f00a000c0c50303425600c070740700d180c0361003d11039107480100362455003025900d03021054080c406c01148110004900071020b640c400500c1c0310309008554003c00680d01d5a188003007140c0c49401c20148001d0050340c0910044e0001d200d401a52030090300880c01181c840780c80d0707a22144c1e0100000f030402c2812100c0c2000c090f000144c000300da240500c16180d1000786500710f04c100c3e0030919000c0341a611240500414403402c04540062040c0e40007034480248a1045014154681440c00c40e038540b03858410b01d8000e1043c6d00101e41c01640d9070081e00c0c500038514150080e4141070700c42e10000340008080c150b84491010b164809162600d402002c00340440001312481545049000868269080d6004040c1196404d00300c0c01a91948551070308240c800075000d0650b181c010010b280c0624890208002c040c0000b011280070100400c1d44040d01d00030f005541000c1d2400c0d05200203040c002c2081303645504440a0340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 603765872 1250 603764622 603764627
    0x912080711070308030f0106090f03060504020a0b1c0f0513080715020a09080f0606060906090a09020406031401080106060e0d061116060b0a03150221040305070506011212 75
    0x998041458035080030107500035400207080c06502c0d0026035004100000704034086115015160042107076103098440e00c3c2c5031030101c42d00c02803e030000420320b80d06c44000c03d0a6590b04000c03007000d00304c1c4064903551021201c0784003100344030b03443e44404854200300001480718003030b100c2c01c0d104284288200794001803655030800c8035440310030100c83c0082d2076a42c040745941244058000d600341c0362150300b011030804580d42e11b41024940749440c07950000041050036100d0809803080080706490720382c0c65007004c500142100c01c554112181042c401300e400114240d2581202c0c521004046003480c9590701e03421014240c965a0080c0004a2410600400d59061940805a10600a0800103016204203221501e0366201c8821000200d80d54815241405142e00c540f1841e100d0868402c81c80d5482c40e0749190a01f202401c0c0340031520b0f40400c00c2101c01503c0c455200140040310f84504581c80c1502e009885900481401c0d1241c0c4103200011400404030010342041a8022594500550300001d08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 603767122 1250 603765872 603765887
    0x1e0d0b040b0d080d022101060801031406090c04020912010c0216170c010509060d0603030503070314060906010e22020d060b070f0209130f030f0f050723120c0705010806040912 77
    0x6c1298013441c034070f240865013100304c00d0302e010b8001691154125491030070843e0f0110021482d0610681103002031202c03000e40082c1d62087e00030292000b60f1650b50001c0040c0c05d05000910220203542445c842265056001c2030340381c0c00214030301c0c04203640341e111000c003c04440e180c1c0c102007140d440020111442e60003807014010800f00140410f20b4181c000040030140da256610403404214040144001030b50507004d603d040481d80e46050410346028400242e1044003e0b1009040c800300d010b0300d001d0794840305800c004040e5040c050342e54100322a244040258050140e44815030303d0003a0201e030740351080b0119019180c01c0740c0c41c103084080c2c0350200804000045c0c40c912101c40070401210014084403070301c0e140703503000352519840034501d000058070608107d084c98042290800c0b0b1100015410500901c42c800e0150503068415880043c89180030f0360155aa4850b000c041038240080c0c400003107005c20b4460aa03145101929007005020940f4421400108840c1d2080c400d4214075109104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 603768372 1250 603767122 603767137
    0x15140d050c07241406030c0f12070f090c02011b11030405090106020f060709050303070303050c04080f0a03020106050103060e13021f03090215031b1e0d0b040b0d080d02 74
    0xc403a460541035a0300e42540841500f070f41c0c00b000d241000c1d2214803061900c2428014140c20903245841c0c6410301c0000c0c0c9810030450124480c00000c084d60459484100d00d01010280c031400f04e43d400740d15010303004000d085921070441c040b803c1c000711095161041c0680e02c030701c00c089a50400120700c8004292a1209520703d10808ad00c400c6c00001140d076121140b0300e0003080542c000c1c2401c1d81101e00424148040108040c0901001040401c80c0e91400000c0f100c0040e01803a0026040d04d8410100c0070601c44c60b8010301007441118603c001c0000040349010b1031910030380003000490390300c070019000d44030a48100300701140fa00c0009100c100001035400c210a01c024543e444861003800750200104951406a000aa4410000c0c0450030000c41d640e40040d0003150507811460b01032000c0210b0000013855004504c0701140080e0310b000822118458030700d04042c459101d80c0c45080c0d04005100d2007130014070441c101249041907050100c1e661301e5054014820a1a0400008840b4042d41c000c05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 603769622 1250 603768372 603768391
    0x74104030c1703160b0103200a05010513081506011706060304020d0f0209100503070e061005070f050f030307080106030b0109061803020d050d110d080103110a051201050115140d05 79
    0x20107050140404c2c010b500c00c841c482c4d44251015415401d0603080c0040403200e9101c4500192054460365079104400e8040380c4c024031b07095580340c4c0304c44020340c40c42155a00054180c894802c2c20080046010f0381988190003ea0391048103244051000c1c204c07280c240c0e08a5003111007003011a0150810a420120140c01003200000d0011075902141c88840d0441d01c20b103401000e504144400e1405220b01002490020203d00d99070030004d00150100c92040c0300201031210010362a8100720440075a460080c0d00101038903d4001c4c0c4000380c680300d90044980c000003a0480c400807a031a402446031801c241c006948130916103003050801e540760704402c01079040b0220800070020050ba00ca456481b0154401c3e8083d10000c40c0c100c0003d0001540120107600316000f1440d4644a03d84c440585411203030891380c801034512040d00481c85025480e0001c9410050f003802c007441c1c40c403054004034100d6100e40c8181540190b0030070f003202d50800c0f600141c40c400808114083e540c01d9140c01c180e40200004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 603770872 1250 603769622 603769627
    0x161d0409080a0c11060f030c09031513050106090606020a06050405010b13020c161d130b090a0308011e09051008030a0f122003074104030c1703 63
    0x280ca03854200d03005842d00307030002a1900380c07a10804c10a10004146801e00307507035131414a082c003405214280401020071001d4040400d140e081c664042042c0702100a40082d520341c0c43c18003100421340d0390f0580f14291825800d200d0f0015030800d45200c0c401c01c445895000d81030910745940d81c40040e01c1e01a109442541d01e03070800b00b440f582c03070b82c548800c107040f010340059451040542c40c0f41004140d0b41c40368101002d000c41002500c9103003130541e0f40c4802c01030300e00000303075102c8104a0000d00040c00141c01d00004a042007035401c40010001800ea0082e2a9481f141e03030303659090052003481c0c09003501541c0e0001010015280c04c1d030009a0030080468a91a03600d45039140079140d604845c0f14a00042c0c208802d2841da2a0002d100442c0b01d0042501803040540c808220b0140c40350075140086a0710000000865061150001500c013243c40307842011418a07404440c108000103a0341d1014000e0000c1c82d00e42d04065100c2118102e079400030046044500d08140700300e0706064450440c0740760004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 603772122 1250 603770872 603770891
    0x10050f0d030c0605090706031b050316020703050a03080910111801030902030f0102070c09111e09090108060a06051f08041707050115050409051b0a08061003020108161d04 75
    0x714007804d442050300700c1c0280300081c5080b00c0201a100240000c5501c0c421510b041c1c0105e036030141c2129803212207480040c3d00702220b928103e02d41800c070390024206000d148008810903030f00440f039500522810080b40c80c50019401ca450480301d402d10307102da26031403c01201300d80c0e4880a02c843d01030030050500180315502c58001c80c0c02c0c803819a02e10411130350f0000d81c500030041444158405445070074810044140c0c0c001001ca4540b207094440c02c2c082d12980519030002074480116044540f0180450449581d01c0000c15503440c070903102c01046906140000c82c007400d00014540010140d48c8188504101030242590a180c014000307607032000c452000740500d410502d000b002400c3c880d078000140e041251450415611094001300d2041e030409084401081c00042c20340204c1e000071000e1040c0f41240c80014510420340d0744003540c640950030070000c10381741101d4540100e034001c1e240c017061130340e0318441c12499801d50054100828070350f400c207103145d0203591310746000c0c3c3d20007900c0003411022 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 603773372 1250 603772122 603772133
    0x4060c2108071d21061f050d080d0c0905090c1305060d020c1e0c180f06010302190e09010b040518061305160f020105100e09070e041a10050f0d030c 65
    0x208500f4a08005200d00658504c2400800c08542d208440440c1c9054590031030f441c60040080604c030389849024039082c0c01081c84064001c4408a00c20208200600034000d50045c0c6611960300c11144100d04040008000c04410002c5500d00c810118074403050f5801c0c1030800804d034006011101c03160741c5c20310038089a41002c118046484030b01d12401e00118900c114814941a0072541d15030142040c84a009a007100390202190040190742030b00d2020741e26440100c009002d801c1503580b040e40702c2d0310214041a00400381c844100c0e410b9039418080ea0300c420350003401b88131350710901790054000510f4035890701214800a40002300244417164483c50030411205681c42135600309603100c084084a80d4040c1c0050140c1c4101000e03000900c40d034542040c4142c540c9807184101c1d100c010110340042e040701001d01403000540f0b682c075140811810907003071103201c01c0e25003110140115081408200c030750780110020f0341220b40080c68885618200e000317102041c03c10000c100d06005050001d00c00244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 603774622 1250 603773372 603773389
    0x90507090c05072009040618081c0b060f09060c031201170c030c011b05030c0a030905010f0c020d02041815020a0e04180b0705070804060c2108071d 65
    0xc4150341d80700d44500321400d08590905610004003801c40b54400d04c0500c80d198141d00b540e005800c40c0e030001d120209001200303510009501d00500480c4005094650204030800c200c94a5581007000c0294211840034007101e8400c80003943e12710f180a0050841600e0103100401840d0320032003d0b0390500407512034002c80e125003a000082aa54620210510b0103403c00c0900709892084004004000c60f4070300107010991070307e01d2001442d00c074290f03410900100300100d8401c91446000c4aa01180e40d0800a040000303a00944c0d0002e50400b18100c2c0443c854042c0600c15500100310580090590f400c100040a1801400710382c9030b014800c2d80007140060403000d140c0c24500c0d00240c0d8900e40c203d0020851000c2c10b107c0b901c42ca1030010504403d200d003094a0404640c000100742c40f42e01e4000d0f050381e40c1e002d1010001c0c1216000140403031100d82c80828000c1c03031072041c0100c80031502c005002512540e040c2c1e00381c0001441980024580320704c150b203c80748040303000303540f035039185511070209107401c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 603775872 1250 603774622 603774641
    0x110303042102010510050f0103091406040c0501140d020a031d06010e1b0915090a0909150504050c04150f092901050313050102160b07030e190609050709 67
    0x124004001c4951941101e040030040c000e44020450b0307140500c43d50107044014010540580d03012a150006a40280d200706912900700c40d4034081d402095070b0030f80d07882c64101c804481d017010b007000c0040e03254051070460409035a40c01c60750b401d0940b000d010000030740003950317144201a22003009400d01c2c884d24401b410100c904001820241d81020000546c0c6000a070044100036526841032001d050b111054880955084420010620440d0745c619002d000b00e0005070b03030040342d031800000c0c61440e0340c0c810310925219030188640c001849070403508455040700c0c050296080642c1000ba2440c1c50350080c403601032403245030205552101081d002c10102500808045540d4181d0801d80c49140008182c49032040f281e0000703801c0d25100020100d000c050064200b0b9900d20307801d070702046420f4068913520928001502401040390905040000d0107907107880c04640f8050801ea00c10501003600612007514614001d05416140ea45200918401409a480340120f40c1c002c41c56184900511a10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 603776978 1106 603775872 603775883
    0x6050c030a03330e06010f090501180314100f0221180109030c0b07020f120d0f1812110d0c060906090b0a1d1c11030304 53
    0x100120b0114110342200f41e98251400d008103801c01c101114201081c0b401e15880e104010b440200f0b01c1070942d40000d03c1e1180a00c119402000142c905580c40120120503641d26201d21107914000518061290018020030038103003174a0140840b00c8842d20411032401400707598580754481c0303080304044c9040200d0001841c1040c0d420f81202c900444600a00c540c0c042c1e450000c100c148071400c21650282c0c7c80022a1901d44009101030906070700d00c1c02482014649600310126801080e071040d80380f500c80c2001c80c17081905005100b80788802e2a00b09400c4405490300c0d40c016596071403030f4000c03c446404088840c1600056503900201182000b8085003032a0409002030028601c001d420a400c1441540400c812002c2041c422003032818204400c080103c07011440810b80c1054171069031180da00600c9a8400e170003403011100c0c17141001c001d01e400840040741950400c07601940c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 603597122 603776978 := by
  have h0 := BRFrame.cov_init 603597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 603597122 ≤ n) (h2 : n < 603776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
