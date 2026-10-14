-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1324
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:22:44.339663+00:00
-- url     : https://prove2.me/submissions/12535ee4-5c93-4d2c-8db4-88c16e08e796

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 237949640 ≤ n < 238129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 237950890 1250 237949640 237949643
    0x30f0d060b040b1209061b090120010506010216030302070302041d010504061509140f0702120c0304030b0901092001020c060f04060e010c05030403030509010c02120105070207090e07210209040b060312040819 91
    0x64a00b81c010ad58502c40c1c405920b503100314641c0d95401409180e42c0c04000c2014030f82c210407142100107046a6000b91110801d00c4003c2c0510b07180c4981020041e0000b11080401080c0c3c0001c200a203010f05059000d8040351914490300040c034007010481310b6850042d400d1801c1000c6801031305480b2040a240d103140300808281c110301130412031719191540000100040174505009688407400c41c103141e0101c10010340f5440340c83e803400604200107104224800c0240d200740f4a040750344003440005030b00b0141104407132940410700048403c03c214007800030b84146d5456549102c0319000c04001520441c118110162440d403081c801080040c3c400c030300800c100d101c1858049074650965010580034920749090306507594541c001c00c5406a4100a0b020080400450904c900507808030501e8a80e9940e000d4140012103002650070707481d00422100802a601820102c00e500d00760818150003d81a80c880c1e11a00605c10703240e050800450542e0151909107010f84801d000b100701011410f0b019150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 237952140 1250 237950890 237950897
    0xf03060f0d0506010e070906020d030c0e0d03030e0105060d0302100f110c1b06090a03080f040f0806010f1e172a0a09020c030f0d060b040b1209061b0901 67
    0x22120601d4907129540002144508020040355051401104107600300a04010030420441010030080d0381c00990358005281134223001452490014003100c00440d1005401d41001059091800f0142d041c0d000995092594000704031580f203610030810700030004000940160302982c0300b8101521140d22800e4071502c0c0031070010350540a0ba00d00c00c420381082c507005001d50000344801c1448549103001c801c89903411203101c1d1400705200000f4120f443c1602028000c5000401c1c00805120203100b121301409450740c070300d02d000d40d41300013459071003000740140c4002604d49440000d0440310200281c1303c0340f0354003950070f040e50b0500345413650b8240444411456071051403450401d12140240e4100045584000b98008a8410051192910b074540c01030380d041d441049248040c000120030740d0b000d00002d10403640d99010901d240c0f000b91240b030b01300e1414648005130005050007504010020701c064518040c1c550f550b000c3c2042c0e01e421040303c900303c10b4140040411824030303101004190f071040504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 237953390 1250 237952140 237952159
    0x30405030613120e03060703020c070801050421020c0603010e041e12030c0503040f030f21020706060b03090d03020903030f03010f0806010e0712020a031103040303090b0c07080f0306 80
    0x100064039201c0191000b030030724030a5400c00024000010307010203819200b400d0500803050182c01003a9103900c024105410190b0100d000728181e5018082c11004000b2180203005074182402c201d0407240036841c00c000341101140c82241c8041c0042103140c1d0b96000201031900f142c1c41c00f0401801c840340140200d8448500e81d200882c40d800401221003010300a4406c0c1824000140d070141c12101920340d0003007801f109004000009462011a200c00c540c1031419200b020354012042e112000350381d000c104070601c0d0720602610b02e0800ea01a20f0350382d000e084140a050380e20f10a0344003910058130801c05d541c010480a2070b50500a400902003484003400304ca00d4054000240382803500280c00039a0a80c003446810004010100410350141109184602c2c003410050000361009850542c40c82032160040740d07a40707180b80039030b00c9508d1540c4115111641c928003460700400400b03c00f54103c5028900c1c001080c03290784202c1c10b880c00d10740d00003201ea1400b920710040b00440c0c3c00040c191b03640403201c0c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 237954640 1250 237953390 237953399
    0x25030b0d05060f0a0501080712080915070b0a050f07020a061e0f060302030706080c041217121603110f090a0f0e01060e01020c0a2c0106020a140604080306120304 71
    0x10410603116101e1000d543e800d80c14107194440030368106900c4011281d0201c070046c481c0c621841c1c040518251b11a03801d076902c44041c400f14030b611a001c141011044400309100003440200503984d8421404141c041166598992210440d21811f88001c40140d122040c540005010759100b50b132644400b101c0300c1101c0500f483c800d001d560100c0021281c69440300030810460070b040190f030003e0415424118400d281040b480f500c1c5001e030f84501c18812804142d44414030140420103001036024045d030755910103203030280440e8001c095441000d04c0b1450107070719910520074400d1408105195610701d1a00426848041d865080319400c99400002c0800006480f43c1c2450341400a141c00410480c1c250315007400907150019110140e8199080705038081001e980303403100b000c2900c90301d00808203041d0305d0140041412050100241079180f158002084440d00000c10f0781c07480d803007078100c40f030184a07100c0d41e070780c54141c19240240182414008680c0e2403416003d501280c000f03110480342007aaa4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 237955890 1250 237954640 237954643
    0xb0901062f0304080d1202030124050702060a03020c0d09081002131211011805060a08090a060e010618060803030105151e0403031d0306040b070203040302041103060925030b0d05 78
    0x203a00085040d40041d00000c051900700e1b1500d01c0000c481c800c00c506542c5010391b0400c0c0c0d90f04803904060803184c42d0400e4030a4031301840660752207540141c038040c0c0792000c0c2900a0002e5020001c40b2001c3d114110004040c5445000d82d20f00f580c4814000d002e00c0c60340381010308043e401c010301164410502c200b000c07401035648421150400c4c0039414403000008180c00240804040c030604480c03e8040800a100e0341d11f80c80102c40558040d850084a5561003a6450342400740008004141e142010112912540150000d10649818010202e0004e000b50400300c2110402c1c0f1450f100d5420500040100340740135010115070900b000ca03c2d43c5040c8007a80400c010b241d4140c0c150615844c00305050050681c01070340f000c640e01c40016004000c07270301c043c0081d682c1c4070002c100920151000c0c4c0080c0a8031300c20300a44000710340c06441400802d070080400d001517042120858000d002c00c1002802d4070b0000e60108091041400010050f542c008000b1000382a03032100700c5030081d4800100c0740c0040c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 237957140 1250 237955890 237955897
    0x13030219060806010203030108030421140114090c09010504090c03020a18510905010e07081e091203160306050108090312060f03010e03030405010b0901062f03 70
    0x215151414060030301a014102c800c0c041c3c001411580144010300c0400000012181607401021104034607c81c06020400b800c0c80c4801c004048800c03408a4104150341500030440c0c100e030110041c2280e9540c1c4040613a14a15404032035440003e85004000ba030815038402448035000300010502e0340d0300d030380224022014561008903a0b00402d004282503147c10304c131351002e980000c0140517682c0600c8072070b1a0343c62034000000e800c0b8142205003004e10203192005607103400540204c4154296074215020003050700744180c1030b000d205400003079a2544074074040d034440e60042c0180f5940702504041880035200060400040e48190002c4050129032900510321488911110b08602d800688004041d185030381d104a040c00800402d1202c0e407a03000c400e6494003100c00d03032100f52658070180000c0f15040703107880e06034240d460000300004036880400214801c074050300080c082055030009100525109215000018400c9010002c203070703624541d0455220380c0554035070005000b842d00702d41980d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 237958390 1250 237957140 237957169
    0x300e100c090e0c0f040603020a02011b020d02150f07050304170712170f060d03032a1b080405011b051b0a0602010b1c0c08010504060203010509060303090f0402130302 73
    0xc0050034200419400c40c01c1d03440c0d03c6141c54400c0350074129070b007482220307078000c0e400b883c420315801042c0400101d2007507004500042c107032401c0c900b450220080c06915502500c80410050040e40c0c0b40c010140c0f207c250660080101401d01d90043da14848201c4094102074000c480034209400d64401d1219001d01404246006020801100e12a403c1c0a0b2810700c0c181c0294a144070f000080115610108410950140056920001c4c00d24945400c0b001400c1c43c404400d410500c8009055800401141c007850ac0001274446404082005001e054040c2005100400c909400c00040c00303603511400d0300320060240d005600300090303820b07039403075041560110301d0b0b02c1c41c0058275590111514001140800a02c0c0c02d000030864040c600d404600b03082c080051010040c2c140f0301d030110400225401c1d44009104d00c01c003c0140d4101131800402a510a1080740d21078460800400c0207850080203d82402100900c6a4038001b04542804060b42001454590260300c001001000d031301c41156580400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 237959640 1250 237958390 237958397
    0x30908040e04060609180209062412010618152d0f080604060303140a021e030703020127060e010b0a0b0c07081926040b0703300e100c 59
    0x9410200d2170700464000c4550510100211039607100542c40c0e1804054000f00203440c0113200d082d444000c0c2e44d02d40381c0c08038a035a9103103000815408010b0308420a90680e5220b81c3e40441c0c401e091500e07904001c642d4081c0c0705d0041046c440201d9500d0241c441d600308041b840401011b40f403000800013103910880062070003c1850f1310f254400d1107a10001282c0e020b00c044504225a038250b8800070003001a40411a010560024120000030300030401200070128120010492042c500e4510f5102c0d0484041100550300b0194600c2d01c81c8810800a800e0010310004452803010b80d44586000c5c04510071900319556959250f0110341c1c450307082c40c1003d0b00c4c141d052182e5407001080000d15060b419848418160800651090b215004e01000c40302030348c107d02c1140a00c2003000d400c0f1014920481001d66003100000c0019044100320060040140032782c0b41d07910300d9164101100a21811400b58220030604186500030b450002c1d4001304500700c1e44001c4490b0f01c808200c144007103842e001c2220011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 237960890 1250 237959640 237959651
    0x3408090109060809070b070809030607180504090803071805040f0c090509040803060105182e03050906180721021005090f010f0e0a0306061404060f0501030908040e0406 74
    0x865030088a090000c0040346069209480c049229a495a03840d00a91000c01e0780040e004007407103840c009803422154000c082d90500c2c01d114070003030445040b1410025110241450000e4503241621515640c181c0001203d4a9566a4201200c44924001d02c906007148404004521a00c0e140724071100b06440c0d2000140d5503010714805400744946030b05c260f00c030302d6510003044005042c820981c2c2d00044d003800c003035440703442e004545001c80c15940000c82e08400c003007012183d05460411910001c602400c2005030b501481c030400c4050381c40840e211103217a4000d2010417180f450084a41900c2a0707490107507540a031701c0e03025800c1c0c14503400104180da0414660504150310304504132001c2c03400c60b800c00354079000e1550085804151070001642c103120359807009440c40d0380514000d87c91801c0041140340d510303499280c054001c101c2c44c014a40c030780104800c0b1504a051a00c07074407080c0c0320700c5803010700e4180c603100046024004d60442212010802e220014008035541a4103005500c14a8003086 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 237962140 1250 237960890 237960907
    0x314120403030209031908040b0310083c06070806011205010e0601091e0506090d02040507020f010f0b18100b0c0109120807051215100509040506060408033408 70
    0x589204103c40748070b0b0351031b00541c00e00024060400c5808507080389181a0312540d40c0d04c81f0342048603580d4071482d00b0380290388100740300c1151030b15038400c9085039002e2000c0e02c821043c00c0c44c05107240c074031300c3c1c5407660702803c04640c4080c0600e2280b58440030503d030903011010710079954016602d00f039200d00b48101c4060144070240d03070070103100da0207406420360000c0d40070400004208418a24400c480c00783c40c0010b8001c44903182d13100065103040c2c02806c14880e50820b408c0080d40c03a2010329450381c80d9440d2001020b20765000307014402c0660401040c442803c0d9a051445040c0c2c000904000c484101c00301000a00c804001e010740b01c041441c1d000000c82420b617040502d0075400c0007520000308250501003024040e08007003070340c4280190810485107903550301c29546409039040c6072141d020b80003940d40b1100c01c0e0f10600a14407060191000c3c40203894480a000c00c600440c094100f40f6001400904131010100100d002e40c0320000c611054602c0c4052010b4482c1c28040401741c8036240002166003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 237963390 1250 237962140 237962143
    0x3030a050402031c2102031b0703121a090c031905060310050c041e05090c0a03060b2b180209070e0a0603091103060c0d09020f1f0212070c03031412040303020903 71
    0x16821581007010342c42c5140c02c000c000c0c4400d1410b03e114234084808039924003410320500c409032071001c1c0000200814100486502c54075001c501c40184100d402c00d0002d11300103d500c05990091007407541000451220031410400741500502d402c1d05841855248085211103006050013205030000c0700e5665400d2400c1d410340d410000c44141c1210002d080104003c4d1115007034568040f08800c0c015071031b038032641c03030071006417806a2003201010780c0800d0681c1403048030b4240720142c03913800d920010442d0224500c2d2064800d0741028406100c51428004054105031b403855134015401e1800c05074072060000041c640a2031074000d02d0000307599020354810440381465100c45e03284128024151803508100a444920440308080d04042d12906804215140c41d2450301e03010a00074041c0f1040c000010040c80c0d841e254404520040c410380080007038030b100280882c2e004076080000b004105080d038034141c420803490404400075040c208420300c0c01484a00c149800f8500c203940141e42d41c0700000405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 237964640 1250 237963390 237963437
    0x4b0f0f08071a0f0403050c2410081c050c0a080408061501021516090506030405010b0a050913020f01090305010507030b03120f0304150603051606031a0303030a050402031c 75
    0x103400382e000c0d414014440c00c0c041441e6800303949072602075a9024019410350074030700401140508a003500d2550400742080c0800e00f03125005d08440a0071542d0344000c07c2e03554852030210600e19400165440001507c104010003040c48003408440e8102060795500840e988640c0c4807103c00e4100c0414000c0c107145616120590581c244010001c1e210fa0507400b203d65007001c3c0011340c01d4002c000c45180300c4d6000302e2030039005000c0140540d07141c0c44c290500758060303c0420907891260011384c60110b103500e40b10307044c203000702900ca1242c07025426076400c0c04160310782c1095450510030841c0c00000016424001c0324420032581d640401c01100341c030309062070044403a00104261000380031201c1e4009040042c0e0350b11a801c03118205019581c201004010f00040e040035045000e4510301c100496000405c03501120709658041000c0002c5210394036070b00c111008031550580007000030a9401c4d18a41059401c0360000741138030b2850003d8034044048503192403140020560400e454015504110b061 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 237965890 1250 237964640 237964673
    0x504050904110907210207050c010f020f0f030c07061e030c18030602090a150c060f090b0108030406080708010b0f0904060b270405040803040227044b0f0f0807 70
    0x1b9400c2103507503070303d80e41c54000b5400326904114200602c018001d101b00040c001a4100340e003510807036560a02a84d4499000006401a9100e01140095024070602030001202504140c15409000e40a4220301030f2258180d5501000002c1d05100190300c4110356200085220b08801a510003041d014031404401320340c842201c040c1e414108500d140c1d04454080e03441644524005140407505040c0001804500c034080d00032400e0750004a40103100200501c2030707a1854032914410340e40d5240c2124080c2c000d008030b568859080c80205801000380d400341220000041010071a603031240c0c80080d850300945071a10035107000404421350412402244070840c0003d6405102900d0143c0f0341010174440070701300034060100348000900c200c50f07285d94022840380c3e8049841080c140b0741814000388100d040020310285113000c0313080c5040000100350407444880e00c4400d0b00f0b019065081c8144480c050020f81d809003101728483e00103440201e0000c1c4440c80380c0122a01c038025400d0a0300402c0541c4c05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 237967140 1250 237965890 237965957
    0x90715080703230c0706020c0703031115060f13021b010f0b0a030b06120a080d02072108010303050306010c062909010e04020607230606030606010f0504050904110907 73
    0x20f800035943c0d00b44070429030100e941d606080c3e0710b03241490010b00071300c81c541c03903440f85000c4d081d404030405a2200021003408aa6800c541180c1e459083c0c0b8184181c0c15642690301620310500c041c0c03281041c1c01d5814801c09903010050420a1030341c0003000503a080c448225041c2d42d120740305010340c12144502c020040b0151a10313001981103503200040c106016240300d104c0c0c2141c507241071200384104900209154803a180c16102c1c3c00ca80040b82c040d400a0000b12150070144d04101e00c880c00406d892565107541e85e50f44c16032640ba41d1019202540094101810401e402d80d03802c02144190040710f41c003441603070380d00013851180f0342ca00c1c12220b003112940b4441c20740100104001d03403201810940003a0101d80a9a44910307a141002003c0060f24881c64511285800b180d1031900200f007440c4546425000d80d003013a5150401110030500217046d190100d8003e2001748018105004125400352103200b10325044940313940000c1d5000c004a178000b0000d20058030002c1d0300081c00441d000b44080708034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 237968390 1250 237967140 237967181
    0x709090f0e0309040e071511010b101b02191206050604090302070b0f09040f1d011107030804051014090c030c0d0206090a05060309011a060405010215090715080703 72
    0x18042d26845041d003814810707900d0b81403078082008188098001840710305007c55403050420005880409083c1017040c1035440c0c40740c0c002c65414a50503a0b008c20800b039456010b20561300301c1c03032426404429410f90704140743d030803102c2180030030354600381c085c241150452103015103034035148040d01c20007040f480c099410622004002030b000144041502c00700e80c0b003152194150000f01c010f82c05083d46940d8828100010540803042d0b42c1c0c07000c548070344081c07545c0000d00c49a0710200d0903505030710007424030f14104110315000320b4811860305030090301c0f5405440d010811800c03807005850f520841c03800f01c400400c052000a0b40b04018101480390300b5009400c6c2a0400c030002610745001805c081e01602000454a60300d0381c0e100042d8000e80b1004103216100c3c00c040340c03007c0c002c0410950012511042e44020720042c40c101040d101128030582c0104004032082070b0071882c142d00500001f8840c82041c40100341c0002203560500d490100341d8802d08585404400201030b11095200c0580240300103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 237969640 1250 237968390 237968411
    0x9060b0903061303021911090a1407021204090c02030d020a050c0610030f03050d09050706031a0d020a1406070b07080f2a0c0f03030c0904061a0316030209090709090f 73
    0xc50001e1b00f03507002006650703da095504209060300c212540c529444802582048082c80403a8808000c00c0c00702c03481c0e0100c6594400301666190f40c220114918501d05000c00c00c00e00c0c0040d0041d441c1130000d031066905251401d18003000741e03044096003d0101d800412011081e001c07c01c00307650700002c8103c203144030034130f90346038050040c0d40c40c58040c08100f40010b05501c0641e0503045000c0e0198000c0440e00c12555500c0001c00420100441c2006844014550740c50ba1a1412181044c076800810601c616480e2100d451034800c04841001e800101c10301400300425140312b040d6101d000141c880c00b0300c2d4644484500013001004250b03407002c6000046250700d4580303e074424540402400d8850780d0750094901c2c41440c01c6450140b50076203104c008100412540f85501901d5043e009a80c00c0c828a52203c5040d06551121201c1c0304201b00306000180840d120010140d1903100c440c24014940609403000ca4124042150032002140c00c004003001400d07160308c20b1410140c40700c9d00410000844 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 237970890 1250 237969640 237969643
    0x90c02030a141305120d0801060f1202090102121201060f030504050a120504080a1a060307030209131506080105180102130e0406060816030302070b0f040605031009060b090306130302 80
    0x280114030320108085282204001c08014410203010300600b03d42959141982d416903d500c0c2ca01b02da000198920300004460340141d2400c490000c0a03114412240c08060100740250059059241140318017102d03c0140b504140080c088079284a082094a6040601c0035014000201014040510745001c02c00414030200e032142035a580160007030b40754000c0c007108540c0da000f0340d00b1005007402003100c258104000032101c07070080003100c107142440d41d03600c200b00740d218406484041e41010780038000900200e48400403c581c6071044444403420024101c9880440380a5005100269556020700c85421603618807080003a2504000354a40120400d420000d2180b5208540c1c12141403c049010465990046070241118808540e00c554207038030001a6106030f84000e03400b60003694004140103952404450142c20303800d0005150528150003107503140d10040049290000341030010034001410301501c0000d0150141203a25040c00c1c2d01050b042c00405014040165058a01100040d40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 237972140 1250 237970890 237970907
    0x70c0b040303090219031103070b040611030d090b04060f060b16080f070b010e01061404060c0203030d06090609060e0f0f06010210090308012c0a02090d0f0c090c02030a 74
    0x901114915054603140380c20380c003412040c0c000a51241d400000903920ba408601c184007202d0248021924856000042c1b540b201e03820b02070031904020812090007a0350140344541040d030586005c413460503007603c0e40c01045586404040724107104800500003848028014003200480118080002510301400c02c103940c031451702122030302c1c5120324940f030900501e40180c90b40c1052802da1160340d20001d16280225610034002d9007000c03003402d400404d4462040c10141c504d80001e0170b0702443c00d800c0c601c2c29030303040058100032603040c0700030028101019010702071800100703004000841c44508000d0f805064072020f8002e6800c62503407608001c0100300e0748401642090b00f40300301041700e403075400040381090076442284041d181007501440416074880c014074102c40000c000d14482180b8170502c2c80c20740c50b80a02c42c40b2000308080104840c16020742c010422008001d03c040181f6209546251080048030001d5800428a07039080003440070700c0c000c6140182d4284043c614103541e00f5000f0300200e5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 237973390 1250 237972140 237972143
    0xf0f010911190519090e07031a0c0a031107080a0f020c0301020901050403060b04090f0b060924010f031e06030203070504020408060703151a03190c270f1502070e070c 73
    0x2c90751015490844004d82c0c200020f4204a0014010b4015001c42c06941c3c10580c88112058100f01c0c288603602c205100301c0b103005030000c0607007502d0710800318000c50241400050048244604000303150002d60703441d0003400d0800058892034040410304402a080c040840e4510340283d004002e100b10743da80c000100d4083d603510041c0040c1c40403201011030020050100000c003041840c030018410f12190154a40c4070711411a0082200d40d030700da041000a2140504815069125092040d200e60050300700c0040414240780025400040302107040d1591090311207030307a4441e524241401903007070510041c006071105032415442d00f840d00300342a6961400814400070907940c1c1045104103c40100c13040004c021100d0541d540091139040e20345940c1c070903991812a004160383d40314140305c9500441600b174241e0348840b003c1001442340351000c881d59401c1c0b152940b003908808165280a504a1000742c1a08207403502000111b52020349001c080790881e103104400181013081140e0b00003004150039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 237974640 1250 237973390 237973399
    0x604080a032304030305070b0a1103040303050915070e0307050d030207180e01020301180b0f01020d03090804090e06010f0803040807060e0609090414010609140a020306030f0f0109111905 82
    0x10120b4448200246400b4003100c2000340001030b0000506911402911000e40075000241a0380c40e01d2401a046854200f212424800c040c030000d008030f8003039440396030711a01504c143c034035512001c103940314074000440d0300401151008104c2461814108a0080901000c2d40c0c2121450b0b52900c01a60740c00043c071541e002d0004101566081c0202c40d0400c29410812000a54495864658610301c6441c00c0390b40780c500500c0c02c0c00e050300f10b28080405451041d8181c019028004051100301d000d806055020389000900b000b00090f2442540b1512200c00000000781015504019104910150304c0e804206d040c0c1c42480148072012010803800121400c2c0c0c00d005242c10034040208141c0d0194404442d40400358004000c14860788040c981c40030039090000b0400a52601c0c1d016044441c40c1903e0f444070005640020b9003101c1d241d000f150401c0f40102110104400b40c020305160030650380c400c17040c69442e03007220f404000c115a80e400c65a20100c07119000400d0b80d0800e020749650511405106 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 237975890 1250 237974640 237974657
    0x70206042108030415050c12010506090f06280c0b0f04030309061401060e04020406050904020304020307052205010e152e20030a1715040e1b0604080a03 67
    0x80240785060360030255018407034075100d141605008103136503840c1c001580d90900301000124500c0602c011200f1101c40860072603000d0f4207040034460360b904100038440e0410340210310258a982c3c9c000242014950a001c0c40c480c90754910402f680305a050f03e500400d00c8209100080080c980d980100d034822341a4440d901e144c0d407241800c501a0803164406800d841c54000001c0c2003e080d031030080d0503545252030302d005100d43d80051104a210b54801d40000400c28041780e1800e1400750001c1d40c0260005044070034032900c0d00e00280c0300301000c03284601d42c0351145610f00000d21180c00b5650060114042091403484e1445281d041204291138640c803884810010b050314404c3c01e406c40507508001c0400e252000c04416001d0300402503104d410281c0d02220160701c100030400011550131800d10341d1170070f102204220000c0b08040020382001d00c1d10423201280c2c10382c0d03151445030443c040d850600500b0345120f0027840811205811200e0b6018031000c120030310004800148403480d007a4145048501d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 237977140 1250 237975890 237975929
    0x7031b02060a0c05060c18010305060612160e040209010801030206070501061a070605010b040b0a1202071b0e0601030504080a0507110d0f0c060c050d0f020a0b01030c080d020307020604 81
    0x14441020500940c4007501040b4205059488505000c00d035100f90301319507054464100c0b5400d140162090181e06145180031882c2c0c0d03503c01d40000317030041000340659042c41006020f50205400803519038a4607009906074504040d8890300718007482100342c80440c03078041d480c40020b14405050002034040e0b80001104070800400354080b034001c0c102000c002c0002d40c40b02940b0120740d40706000030b9801604090010480d0b607000700803941241d4030040610300d041d11030300c8296404502110b0713600105600340150b02c0400c6e04181c01e08481c6a502c0d0302c4504280c10b142c444442c0c03240260502d0704061411041000007040001166082e085602b0080d41700c8902d85804080c41400500390381c0c00c21304101d07010f810003002100c0da02c0042e1041d0040f06004d0745441e8112031030282c03801d025005a222094416669004100d10741c3c52011030320603100c3d00b1002d074031058021340c000c0c0e0084460404100d001c1041100c18030170302e85d048030705102443c0b405075580c0001c1c1d001e014a0241e0080d04060003a4102c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 237978390 1250 237977140 237977177
    0xf03070f030e060a050c16060203070201110c07030f0302030c010204090c11030910030b1903060e0106080a11102d0806060406170c0909070e010801150f03050c0c010f060f05060304080703 82
    0x7000c40c3c600e47c44290f000041468440d01a400070b4660501660820a41184420601041d02c49001d600401805081c0c44c45e202c0d490344081201007034017580020029100009000c0c001840540f5242c0c4000c5640b09045000418000410b05412860f4005006052103951203409241580d0716030720b0042000c0d008900010300744441c074103c03040702d10075545000007008420b800064003004203400070400180c0d135501c80740e03c2e0858248002c0044664940358911850a05500781400c00c00d0724107000741c03080c4083c030310300702105e0196800514160200d003d0820340e4031011880e80035200740c455509091505078043c2942420340e4900740c10244403400110140000c3c03003078400341c0702c0081c100c00c400c0c10b00b0203018122001c2075501c80c0c00180e1a800100d03810200d0100f86c900c8210303554400b1404d0040c40c0040303006150217801c21341e05403030400a2802c4030000340150310195002d1403000030403a2504031508908000f035440386001d03080602c10880480c805005403014243c2500700340032459050400c0c01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 237979640 1250 237978390 237978397
    0x100b04020c0109030201060906150504031401150303020c1513051c0503160606060804020603060402070c0305060c0a02010e010c05071511040308040e0a0e0d0c080f0f03070f030e060a050c 82
    0x741c407a503281108003c18582c1c15004038048501c2d00008014454440020f08205a809202c0c03001040d4201f1080001417a41509804482c194100006034260046800025101c1c10360090700103070b00c22803240c87c003450322005070007690170305d41c0d0000d10b01203080c0d0304440000b15501c143e82c492000d01c1001c050140170580610314440c0d1100980740e41d01c100d500c4d07a031070b00c4c00401400d450f0310703103008004034205000310081c40c01950018003090440d40d481c4204400307580b208904440140340c444001001600800105000c1c1700080348181c0c884049070002821940c10415040c4140c0c1091007103070040303400c08201c902c1c5541244480d4a001d0a10341300401401c101806a100e44000081c00414004141c0190050f14204205002561500116081507500c0c9151000c07854100600700b400c80c85c00385030091003280c414802103046c03500e8990a2035580d0000194010086000410030525991041c07010582c400b003414104403010000d00301903030743e500003003c54880c1d60352000440d14001c1001c00342c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 237980890 1250 237979640 237979657
    0x403141b121002040902040f09060605030c071407170d02070b0306010c05210a0806030a110f0406050607060207020108101505030a0609090c08580e03120705100b0402 73
    0xa43d565991000480001c2d1f1242c800e60414001810b804245080b0078010007044420958555045491300800301a407039200a00850341103020780e1f12450840d80601c002c10040244440004c9104071042d141410070b50712525143c21504181e0081c07124080800a482e0417403001c1c6801c1c443c0303988525045180025904c00d400f880040d05048081c418007803001003250b01c8880e500c8005c203496804c10705644880e00d0740020161043c041d95011981880d00c0344030b81d0418005c1002c0f880aa43d8070205506500141c003d82d4803d80005041c015560480312040d08a103100b5803d4400510700281c0030098039510070190100a40007000c9003603808907801c00b601a01c6d110f0010803030700d0540d203404080da00280c41084028050000310202000c206618103c040324501c4820805010031419852040007558020180d40b075420410943c001040708412414602034035030391000e0b2074501c10146840f24076030708041c000600b00036581c0011800b00d803504660b00710520116110101c000007030068000d9511 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 237982140 1250 237980890 237980923
    0xb01120e15160909050c0a030902010905040212010305011406100e01020c0a09020a091712030c1b0a050c03010209010f0305060109030638010c03050d200403141b12 72
    0x2c1c032116800c6410b2028100015881e400400c1d0780d5441020141c81d03044070201c011070343c11311a0313894060007038124007030803441450410000c544500c0010100d81042a81180b101b9040006108005013442008604890744004020a1924000003285444e14240d2003003080300d24035258a00d640200306e1507040f004020040d0f0300c050b490b131620200030f4120b0380c507032000210282c00c0082e000d03018100d000b0760720b00104045c001e00d40000e40014059070014210070f11502d020094000c40106c2001e8442d00d00180b900580840c006504045290402c0c910121740300303920400c003800c0e46a80020300408801c0752818041116030f928401607031171460f554005880182410140b12210310340030b041c07043d4007910700303103001c145441c1400300035590941c100c01c0e60110701d1421100000c640140f02500044107559000709071203500f002d4800e001030003e99542e100c03032800304091080014070604603002c040b14030028000321408000b0700710800900b083d12402000040703502459200b0a000d4a20411000c14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 237983390 1250 237982140 237982183
    0x30f030a09020f12030412030e032b080f0609130609080307090b07081222030503100b091503090a06060e1005061c0b0d0212060403120b01120e 63
    0x2510384050144108200d10074110b4424403612858240400720a1544550086040c14102010380001d041c0079003040d018007841c04071600c0da6580801810140403911184040c0050030001403d500708140640d12040c0a48082002604100940000c2e0302c100304503880700c4c164544c410b521440c0d42113618090003032402c3c48941d409002101d03008500506042d6a03802c00c86684441103e464061001c0c018034086042003003141420720000c0f61a0090701e0064484042c40c480c0702413110b008580001203011a80200800500c004041c1d001d60051003001c20607460240603100144400c04402901c40c1d01d2800403010651440b402c2200c9130f0003c2c0d101c0000c01180d6100e83c46c50070502d0040b21040c241c10248040495035040142c250b642c4602c0c4046c400e80c400001c8400040600707032601850342c03c41c104413024005a51881c0c8401c10100c16072015124070b0401d400e00805410a000722608400d040481e10740c907699125510000f14443c102d00018881e09070101c2c1403d00401e800410b01032141c82 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 237984640 1250 237983390 237983401
    0x30e030a030e0f010e0d0204050405150901090c0e06060909040320030c0105070f02030a0c051903050d0b010e010203041a0906370905130e030417070518010501050c030f03 75
    0x111140c103010b0102c881d001d200009000460340084820304e12a0000d4800c8141c4005040c607070800e9402c98414800d8a0001c0d16025040301800011111840ca80c0e44412000041c1314803000329a010b130010192809080c034007100840c61500c180f4244501802d0043e001909040c49074000f240700048006c110b20300c040c00401896660b401058809201c0e518210210b10604d0180c5d0b40350348610259000745051180380036003607820a8841c2d20503981c50246600c40a22904120400350360329206e80c458680740c50b071401b8810101c3c3c1016007081d0601c45842e00d101030aa80010070751302111012407140310115089400c0300c129000b04010303107400c00c0d0081280074a001551407220550001c0140c1607460034410501000f608084d1038210000c900c48040900050909109800300001a00700100f903400c3c640540318556440b0381d2003d2460081c0515043c05800d00384071520080070101c4d1980306603035203402c1c4480400010711078a410311800041840c101982442600c80c086281f8020b25100d2402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 237985890 1250 237984640 237984647
    0x90c03041103030c030405010311031003080a0314100305010c020c2d0414040201021011190507150b0f03031c0e1203090c040e0a0c060f02010209040908120f0106020a020409030e030a03 81
    0x744c040c950200381415100803c07015190280c338450580700c1c09581d142c5142d6140c00c000c90713019107120410035803551f0002c1600200042041c0c0904034003900700007a28034509040b821502904040c10854100d0a0000c40b25900e107030003c002480301c8609200c5060b1030b2440f4041d8042100803503030f003060500d11584a0090a010700d1880740c1d000b80c0a84424044042c04d843c00c42c1e08041109216080502586c10040d4002000e96050030b8642003140c600303001078481c0c0313104080b04900401c60948444c20140302d402c0040141c815100c0940c010b50a240c2503c5c0c02040b005090095034561540e169000301524000b08060302012000b1310400355a81000340e00a6240d4103d28440e9020307070f00b4002504021000040c50001c3c1c60307008240002d026042002c02c80e5000c180100b40350440d034080c00f196116550b84e102e007884142c0300ea0308040ea05e03010850a1822082d000f01115201d11780c8100402160740c010461500300356040b5000100d1062501e029504212000f5010350940318034a200e4040680 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 237987140 1250 237985890 237985897
    0x20c010f030e0f1515010f05040312030603080c0c0a12031e0e060c01020c011107050606091f09020d05070e010c0f02010c08040602030d062403020c0708011e0608060402090c03041103030c03 83
    0x600034001703040d42c1c0c820801500e00240c00009000001c100b0401000402d0030402014004542031070041091942c9403101c00300c0c0d400c4280341040030f4100c805500158606003035210000c00e034034003000382c041aa40d100a03000d15200e01e0841c0c110070116071a5043c0a00c10901c115070350a0040c41e1645945020b000310f4000e400250016803035601e081d908200e480b2104040c0d8101c1d50380200104081c2da07078281401800d00c07015004150010302020074200c0561740b1401400901051580181c039001401007040964402404007010300c0b80b2881c6c18421a68410070220740d5a800a04280c00ca44581c801280c44030076500002e001d00c14041408a04076038040010700c070754203500c0014010642c80302194880c0c070f10405105a03c0104000b03420f20340b14080e8000c1e041da041040c00f0346003196038810005003500d1030a820103008442c0c41d4005000403003e446008080d0464500400291030240d0202d007030410f0242c0385d6103200313102000241c108911440840a81031025042c0e9881d51a041d80640c1d50b42c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 237988390 1250 237987140 237987151
    0x1801020307050a0807020604081909150e0306010f0f0e151c14010c0509100e03030c01050714251110020d02120f0403020d1e030804020f01020c010f030e0f15 69
    0x44d20500461400c61000524a0085421103105490083d03000b0440c0c440554810000c400c1c405a10000180014102c01d40c0c401e40707890741c07580d01502c2c00c43d20070981000c005800450710703946ea8007000e005401100c1030403000d51307106100160035907c9005698140c9842400402c3d4829030441f440007803c5141c42c12280160b01c10071907080342d80320803000d2a00341d811500c00c00d0000b403800d0100b045a0700c2c00c3c459444440c451410102082414031b40402e0941c0e00c010041c0000b42e4503841030288059000306014110782500c0e10300d9040080305022080c403000a100d0708410110000b140070140504101c141c1c5001500910000141c403001310040c0d19401c3d0f1106140260149030386211200c204070003181d28210400c03544520b02402d40d0b08005210810550943d1024454071402040c0c4240c10341c80c3c0c3c50107004c4d458418080c54140704201201200360782c024119040760400000b140d8100300b500c004600e80e42400f1a0400ca0800300c94034141003008202003910580c16480611040b04c02900d018a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 237989640 1250 237988390 237988397
    0x150504050309130b0f090c090301110a091208040b070c0b0d061703040e0f0c0403050609070f090207151116060f0e010e060103060e1204090b040c0201110708031801020307050a 77
    0x2a2200d00320b000031190040700441d003250300c0c10580561484c1002000c1d6111f51800b0708a13041540101c00f09085807050441c60b00c40000000b0300302404c98100080b140200440100450910a55a40c2c0d02481c029481a100104008240c05080000382803111016008800c0c0560b201c0100766100405450700e445210040190051004100c40000c42281c040e5038121a04003c0e50703c80865690700c401000f420075494010520011000480038440c282c06601d040e03006003500390420780000394445550b80326224a0707104010740360000e0924170214400ca40400b0000442c0c11601c0d03400d000318890340644046074000c1c03080180411089600c5083d81180b801c200304254100510783c0f908030b88410030031034503550006004100095058001d5084038010340c2c11780f10001000b03145941c0700c0d00300d40c00024004e5110700301d905060400e8841c00744d41000601c0203020100c44003504e00d415208600d0094800c1c000040001d402e2441020040c05008030f80d8002c42d41d82ca4070343c0004200b41c00c0800c0d0315000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 237990890 1250 237989640 237989659
    0x206040c06031104030809060c0304230108150409170d022206020a2015030708150105160201020c0603010314060112110f0d020d03050301090608071a07150504050309 73
    0x1c1442071141c80074400400d0b80c414500b1382107803039181c2c0036000005a13940c0208100203418000744c003031020f4002441045030345040906a03040540c070303c142894142c1d04200346074080020452400440d4a10306000361070003e41e010349400c055000d207100c0c2402a50408000646202d0030300568014010800341c51541b69650b20746248520710340300c483c419540180d1248007914045048448040070003001080581c0c800f045100110300c800b2100306144591a0703001c0704002c44150044005c039407000e40c092080c0f103c0000140040c0141c0140880400000710312034032502164000c1007180308444004061644035039491a090260007075004402c2900d0045000001d0a5040d14030310300300032170b40521042d02240b1480b0505c011a21025466a400742e220079014002d40c60b82c03104141b03401d0081c1d584035540c1d070410700d000003601e031140e100e41600d51040b2000c004008090707030a9100319000d42c41156030fa140d982031041d510360740e68419a41e01441c7c1703000d0104201d0000010b01c2801d00907a5040d81 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 237992140 1250 237990890 237990899
    0xf06010c0c081612050c010e270612010b010f0f0306091404060b0613050105090d020409121b0222020903160515030c030a05041e051b0f03070303030203060303040b07030206040c 78
    0x410b18110b004045d0f61041c0700b862030f00d60140d00c0380c407000803024080310b40f00104c06552140c08c80724103101e42032450b0030a091140c5400c0c007078616501104c40c040288040b1591000081c002d902002e255000c0203a224071a942d01842030300400f000744500d610603c0002551905410030380c0341907408490061510005404a00b020b81c00c1c0c901880c04c05000044543c41c0000645095001010f80d41d405403500c04048010ba50f5849000301160040000c0303c5034405040010f44200710100a040c2003600306200400140d0b07401114019000502c001c0b6210000c02d000303c0c0c0080d004503140544e050040802c48a0940002ca0500040303940803141c403034907040d00c109803203040d10056501d00181403080002402d038551607044160001d204082e100100c8120780000c58119900b8a012941e5070405207a1100401401c0301040b80c07031504640409001e500c80c800a95a00b040c2c2c8001418560080000b9100ba40c09100303680c0104402d00c1056036650305885c0003501c40384119021200326040100104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 237993390 1250 237992140 237992159
    0xf01020706050d11040b030408030f060301020313060905031e0a030501092a1e050d0b0402040e16110d090e130c140f041b02240f06010c0c0816 63
    0x4101d41c441d844039403408601400a101600c52184c1ca02c107007038410000090344c21642e400035031041307000d541e030551a42070900010144910150680344281e0051080c815200600301181946130b9201d200060310500a10700241140942c400041d810350705003c800d0702d40101d640080c41140d14a03038003001560303260001c02e0101c4140d4640100031984401c400e20200b080402190700415550070240180702040c40d0010740c000b2014884400184d0218404403201c1083c0602030264a0031a015802c0506050304888464402400400408205140b801910b4024880e450b1205418815140303004c02c0c00c0c030058040b0100b8132884110380c8145000580d1040103040044200d540204100c4841d031810b2071304504401807410759584102e0800c0110010380d42c5103d14080540d044503001a82c124004000c1d0034911030070200c0b50000d18003419040051480040d0035404034030070343d0b11484c58135501f004940764218100018080c4a4400000c00c002070001140c42c0038a08494201100644941585 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 237994640 1250 237993390 237993403
    0x30f07030614010509060d0c0f020708010608060a110c01060602011409011503080a0504050a0305010f051e010b130902070302010b100507020a0e090c030712020406060302090619030e0a0506060f0102 87
    0x8482c000007200c5200907541c800e00050041c003000401c540c0c2001e07001c0e66020101c61105101320041005c585410342140e0701171100342c0042401134001c02501e8500501551900d1008201c0040140e80d51450b005c070102900580390b50130001c1c0002c00820b03842e10b4011f802005403031580c2451006000005101187c14007a5002ca81914007064030210701c3c40c1d441886a07004050f04400b4010240001b1070f0300e85904207440011400340d8004200000720040940817920040c00b03481109032400c10304a1050150226a8115a40c04940660794007882010880e00c41c11900000740c0580002980004d250f81504006107040d000c40d2842003540300414161418451350030001e41040c255017003005114107502c60b9640c090340100c1903500990800c000241448a036070441d4050820080e5078905504180c4211405402c1030f050461a0034a44030006045000b000c50b603000c00400580f90442c810b1003500024010a55402141c01045003442e00ca0f80f40c500840f0300c107000b03000e52404040b1640c40011305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 237995890 1250 237994640 237994649
    0x20315240a050612220b0105100f02030a0f0203070c030614180c0d1a0c031005010e010c060b0f0405091f020a050a0807090b040f06020c010c0b150f0312030f070306 72
    0x42440e00700c0c844100c4800800042c5100c105c04015140c00609041c110091444144900c5000d0b4846d0304000400402c8848081070000b00b00b14001c0c1740715240c0c1c000044960945a0307041a111646501074103e1462251003001000101000d200004203d4160401100185a0310300d80710301e960b49255841c0c0440c1803007002462a07012003c8009a030600d416084503481c01840703001c07140c40880c402624401c2003542e40803041c2c2c00c00020040b0b03070242c00c04400c02409091038031146009801000a0103040f0720403020b41015540c500f0000142d03650038807402541c00140040c031051420a0100e619a0203410200f1195140c0c0740c01d201341000d0a01c2102c10010441d11140d00380000010b0032181d40c03900030190700034005401804100040d15001a000404100c81100c04040c02c107a00281403405030803d0070f041c080d052070450f0010341d1052880f640315240307500405540144600243c090024103082c16014021540107625022010f4000c2d8410343c071906865085d40c560880880c100c0740c65105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 237997140 1250 237995890 237995899
    0x9100b0a0c051b03070909020f12030a021005370911040e060f0c0714100b0f061303122102040806070c050d031806050a0506010e180112020315240a05 66
    0x42489682e406d42e00801c100e5001034142c4c80c20b0749e010300c049406031403102184081980003140103e40560304020303500d040c03101000240004c1c1800181002100e1020081a21050300c0c072066000c45014071142d881c0c040c01b1100180301880c0d2a082090050303840c0340e2211300031818030342900001100083e40c107004040d0405802055a0352803a00d80d40ba4000103000c440b2041c0c159040d1020b0381c410400b007028400728403400580d1031380302001c010400c81c060030964080d01e018001d031044038140d800510212a000250200411403501c800c030340703107640314107510000550107100f00b581000560180c0107803a1001c003210199100e440060f00c404c610301000400b07583c03211142401c0c01d48280c21003000990220750244040c0400e81d03461041d0b0f2401c4078500401540c5608014a0f583d00c1000d40c0000401900c09140e15592170000641880c8140035680310000a0808602107450070010307c034090340030f40e2500c402c2c0c1c1003412010080070a05071442c031100e00e022440c00c00b45e140498035417007100e40080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 237998390 1250 237997140 237997153
    0x601110304210219060905030606040b221b0c050106051207060302130306090605090d030b06120c04050d05151b04060f210c0305090c0108040209100b0a0c051b03 71
    0x54040018a8800000f01e800002808100c42c0743c02c44148560042e00361034030342c488003a0418080c1132410a0061145214a041c02c1d141d030003c0d1600118001405450341e00392240f8140030110001401004813818a5040880084080158014a00e03410507110704001e12095a44404200b00488584030801c1c0c80c2d048014100200740c0658000d1406114504030083c01c1c80c3e40e910740c0c01c03c540c03107107c05449098442040050500342030004810070410390800700184440c10010500e20f00a00c601c00755884071407070226951070094416a4014500103010000c101402d18045482d0002c84100c440d031000240d01040b481d20407401589424000c00d100b182c10549016411180c50031740c2116402071004502e61004a41c00319400d824401c82590000b02c0c1008090b44003e0407078400510100240e0000344500689030b0340091420742040e01240e010410307898180c440c102d1422140d0003403215000004280b03800907045021542a00d00030b100b40d9032000c0d8800e560220800c5c0214000381c0c10780198 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 237999640 1250 237998390 237998429
    0x3010e0312040c05091305060610050f0a020705031912170a020d0b19060f110309010e13061410050705060f090a15020d0501080a1203020306040e150601110304 70
    0x1940303030b00600806646002541d54004107000e18800e07507040844c6060b1510a00a00c030003044529040305090316481081c09000d00000d005008691194159440000e000b070328451080229401a100c0141940c550100140362012030b40318400045071401c0503480710020007401040c103111102c681d03010b01401c0d80c5d82e42225400030b40c040341c1d511401558440c2d04240689031020902310b05a01c00550212035800c0c950042c1140c0a602c01d034208210807081019010300d000310640c5c0e1005c10078281342c000107100c000050300190b040151034008501e0040002205450007101448841e03040d6440e803000c0d071415000b160280b282030740c0a4825400807020490f25144250300d254000d031280e040d6184990303181d8034503c2d001c10201c288100355401103003048080c0d0440c4a07441c010080f2030000d080c1d8043c143c0d40c003c1000180c01c604010b040d030110000d189a1616080300ca40028402d054800800904489104101080d1401c0d400156902c81a1044140c004100c030103446148103e2403504d0001d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 238000890 1250 237999640 237999667
    0x16080307030f1106040506070917030d1505060c0307031b0b061005090604060801080f01060e040f02040f06080a1a1512010608060c040312020303060609040b1f1d03010e03 75
    0x420b20041d04001ea0302d100710782014010b202c998003480c400d501800643c200701400610307601e083d8016640c1442e00060801103203800000b10744140791841000b040400c0d9801c0c0960034013206038071040d00128002000c0101c401c0200040160f070f44251030340c9107038100c1d22140745890000310310b000300703c00e100307d001c180113280609041022011501c2c0075482c0c0480c200c08190980c105a10020100d1244401880304810034822850301c1907201c80200030091a01909030303070284020f040603000310110b0100c14155150341c0c001030340e02500401e05100e010380d03545a03030b61340b5800084141e6007014041842006841d54554043c01070041085000030405503204002ca0390b08440300c886625941d45800050044050011030310508050210f29180c074034500304480c3c20611124a003046400420400c02c007070b982e1106549440d401500e002401c0303e096400308030034100400b88100005076600491403c80e41c010307025002d03c48543c070301003c1245101c003498281c824004040c4440c3e0170034080003c03004d40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 238002140 1250 238000890 238000907
    0xf14060306040b2805041b020601030b0c0c0a03050306011d0307090e01021309060302030f01090312020a1106040602090a0e04020d02010509010203070605010b070b01061803140c0406090e1608030703 87
    0x60040c0000060300c0b6840c031080e810fa00b00a0f804e403507850b9071901008070b403610b0300c00d81c00e0522584641e03405800d0a244000e44a60f41400f00501a80c256008201100801c90658043c145114119071910515080107000c0740c0003203441c2030002d1000e401440c290300650300703070f101d01840290044c82251f0038100e80002904a140078690346650074456030034001038082c14180104420040000e4940c110300601d0f01381141504c22040c2c0340c3c140118040003d90241082800407240b400068444820384001c0b240c201d910030030510300d8030a8000703003c00d02c806a030080a000704200c03a41108a90354168449000b00102c4000c1c0d1301c1502000c1800242d400303a401070110f004140705407032a2000554a03101110002e170440715041c2d50201d43c42082002c8040920b000d07240a04184500410243c40740c000280a400300808071000030703911015205080103a2031071854001c10902800f038442c01e0b008000c1c400304607201524030131646240c100c640140d8440040d01c1c0084042d40c44c090303013924280d4080310f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 238003390 1250 238002140 238002161
    0x10e010f0f0c08071203112106010915020c01020c04061a130807030c0602060601171b0c010c050c10050912070c050a090f0e0609100519060f0f1406030604 68
    0x800718542e000500160010a00300384101036031041702c0751440000b42182d1565107041071801040080c0c0340d4041400c48803a035441c486e80c420f044152303503200040b03880c0d114a500000300c00c2c4070600403003002600070403824509042030b8211290303206002c00f000b00342d410904c1080032030070b80d400343c403100303c20b1441c01021880302140c01e41c5021951a1455071030861558001d0300c40c85213214092140d69410300c41caa070056001d01c0c102800c0c2142c68103e82c0c0c0640003426a440385041c61407807c1c400404581515000e04600000b001a0388030b0702c80241480e404040220303210700030034125203c418100e01c01c1c0d602988842000f07018400158003c0c880c0c95228410607210348001c0c3d43d0005c1c065682c0c040200181c4220700e000700310b03d030891101d101501c01d0140502000e40020b0700300603404100184c6110400c0c98000b0110300c6880700701021440007000c10007060840d040c41070100c1c40b00201508a0206c810400180e08850366412200d05203d00c00f00c81e080d4001e104201065540c64a81c01148841 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 238004640 1250 238003390 238003397
    0xd050a090f080c010f060b0414130501080f0f06091510091503020f04140c0a090f06020c090a0b100522091d03030402060a05070507030b0a0515010e010f0f 68
    0x454041d1600715200080c40303001c5658200018401c6460003003030050700e0800c6034054003804a01d04019204d1060701544c041c0d00351455007c0490800b0f945d9078104044505007800d010001540c48140c0242c807240103103022216807160707204102c001c42c0b00242c5648a1266540907000000f6590035080e0041000740c81c10b103400c40002c801040341e4601c0e20540f10ba56040841008a080c51403040c0702411103011002803041e850030f0103104a40140300000c0e41c0c45113011840c169244d002640c107441e820921380100703c514003183d1003c40e11070780000d004040088115038403842e6680d0300c00410300b6600311080e10340c0c0020440300070f1a03c0300c1c0220060214903038144c03141c144600d900035203c107603212140e10200308684c07680180020410f000c9071242c0c00d01307010000341d461071400c0d4012600503c1840c000c103003004400100c68040c0302003404290041e5511078440102713420300000c2e40e00a05003d480c02d0302e05441e6804260b60a42c051850700c030a02d2810703141c2d40b9070078185101c140c0382c00007810101c0c03052 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 238005890 1250 238004640 238004651
    0x10111303020d021906030b04110a0c0b06150c07090b03030c120714011404020f0a0b0403110301090b0a02070b0a1b0324260105040b04060b010e0d03021b0f01050d050a 73
    0x2c1420360714150b01034015541c00140c24180c1f4010001034510310f40411100c494208038284106500107102000d59070401c0c42d07001719403103070004218613a1800460384d44a40e8085407001901030041040d6088680e41c00007030260007462001c140e12403040c485c0c096120743c0443c11040410420b8030140c803103103000d0700e4001c00c09421a4031441c25500034034058a0034003110001c0004628051140e500301ca0301c181c6803900300702c1c03c105000e5920721440c0005000c050b54440d03040040c2c1c0c0c01b50095040c0a60202d0300e00d105041145100000e9007081d801118607000160001d0f00c0b100e0b0a101d40c0007401c012901c09140104407620a90051081c4080506412100180038a1180d24000d5600040c26120194000409a5140200a108a81d01458071030341440240404901324641494009800000c005150701d80000140e6002c040b40420070340015490b20000149034000c18011411061540c02d003902c07000540812180c1d0b48200344040c0402ea0030b001d0705105200d19400030f5803014000900246 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 238007140 1250 238005890 238005919
    0x920070f1a090124080d11190309030c0815041101121b080a05060d030f0e0907031a0102010903050f1b03041214010e0c04020d0f0e10111303020d02 65
    0x741110111074080941e07454201101d201034508001100303181c010f2008071185070400200e60346680300c04808504202401c603584c5600e4030b0a001c1441802034030b4603548030040071464040c2c8140818441030b6284600480000b81d2400c01184512058180300020240da680b1981c0c0c4001d22058410700d40d0401505440744000c13903c59200e030760043c90031803102103400301403050000d002c14001800c40050f641080c0c2400407903220341002d034210030381c1800c00c1c0511b4130070840b080b215581c150007001d501180441c1485482a01a0311000c00b0301ca002c00308103485c5111000590a0320082c00c802400980308008482c0c004c00d0201c041d054120300000442c4480d000403c64600c3c43c0c10a40005070801c2c880301c40842040142a0f2091000c0b901100900c0110044d8203041d80ba0071180c40c0103030003560005003441840c2c1c40355008000c100f003114010000c6000e03d9480590380d003003524440b1059071624001211800110059403080000e842070081c1d0b4908550a200c0c09034003904040f600003848621031035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 238008390 1250 238007140 238007183
    0x60302030712030323061c02030604080c0a0b070f03142404060b040314010c14040509460b0906060706020f0309030a090608040f03030c05090a030803010920070f 71
    0x8400c01244406403500b020310030040050f0740e0034880c0c21f01540c1c0300d50110068801007052075000b900482e4198803004030440c01e03405e01c60840341c0100092612010001501c2d04032203c00103408040c0d07010040961388182030000d2070001d40f2115400c42c203c02c40d90342091081031540e40c1020010304081003150b03454800b002c181d0000e8004441e4440401d104a819100034492840c0f41050352070045a00e0040421000c8640300364007030300340140e070a00001802d4030000200e41441441a146039040852401014030480282c812042a440c07201d8001d035146050034001d03240c2d510401030101c2a552502c004000642d8081c2d00122100c0f9000d01411210725480f40c00f541c030940740c5102071581c526414400804940e6030380c200009101c074540611000c508004190b1400782d03454140003801904010301942da90160006082d1f0180d801c580100030401148044d42c12030307411200c00e1041c101418003e0904086000710050842014480d100215145854804c642405000740090300c071301c041c5806 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 238009640 1250 238008390 238008431
    0x110303040b030612070302090703020901020c0a03030e01030f020906090609150a0c05070501020102070809040207141e010f020403021c0f1a060f010e010503160908070602060711010603020307120303 87
    0x10041d5800200403c0114105030a14002c0014818017070404c150456000401240e000342c02c83c0105903012038840300990081101c9810440003e05c0003d43c81c2e540e1074000c0c5040034810f0800d0001e4100401007240110a00903102a0b1200078421400c1c030241e80c040c44440d070448080140d012a0380c0310707980350a10540300201807450b0b02c0d07590400c505c076060400354504441c1d23a101c075045a1041003044c2c003080c00c503420ba81480004403400759844a19040c101c0d07551040c0e09010304e131802001300c0b250640075144500c01c1c032040410001d00032007849040c08000c9019520010750048100003001c001000d100e2600c45804c0e2240b003080700c04d80142d88515a140c0481042030100d00800c105000300c61400c05480a240c0c01b00b440c048c81c501303840100003400c5004c0640103e0034404880c04d4100c1c4980555604001303404668122000f041e07440500070f540303000559915020608106e5901401e00041c0a00e07025a41c000d8001c01074240340c030030303042503012040c0001d40c10144e0314001c01140e10b5240c01c54 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 238010890 1250 238009640 238009649
    0x703140a0c0806040f08090607060c031a030106180c09081c090803031b030903040801020c01061d13080f0408030a0f090b09181b0d0c02060106050f1611030304 70
    0x42600c1015480e0154003580950400c2071564001410040002c411000540c400f07540521200d44801c00100804c03150300520034020807140c10310740d100a903285d25901c84080030000c8845803164070080424075088841b1405100f0003041110030040d2200c0f03254000a40c0f44c016072030048039096450f0072460505421210803420050306400c14591264851001c0000c0c3c0079441c003461840c10a0340014008039014081e140f0440c0d800310028440c60410b04c1590010030400d4001c3d9920800460400d000b000e850003201401c200401c01c036110203003403641c554481c01c410035503424402d59076121040190884041171413a410108000304800c0414405000115540d88030340c0500145410003401c540740c240c004e101d207920117015aa89503654901c1042100c04616160000358aa00c2e82c106040b1040708000c020040001a5420560009501030003c0c002103a0070b490259032170b07100403201c91140e0411110103030402e000c681203440d0540c05200c00e01e88150807241048004030082030943d00a64031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 238012140 1250 238010890 238010893
    0x27010b0403020102070e1621110306031501030201120b04150305100c0e0a120f0c030b0f0121020405130606090608010e0f032d0f0901170106020d11070314 68
    0x80c100304550301000004082c04101c10221064601071400c0000001c0100d081010001c0740800700b1000c0e080d031031b4442001041d20b0000d2040000950002c0d1261b4010780b05c43d0b000f4424000500d030001401c00040f410303a50b050b0741d01c800d080741412081d000b03090344c440120b03441959000902c020610b4125820021485107010704541080c0e50b040c50102e074161a050400d106040f82101602d0350740c514000262011590b140d0300b1001582071800384c0b41820b050041c8601011000401400320b0803045620560580c850102c10742c0e25500310748500e80101e4410780c02c00c40c10b1001c0400516054210715480701001d03400c4241d8000c0382c2c4981c0d080e600241d11007005541e0b41c11003805080340030700502a514420f58024208048400b040030b569101d04688132495041d004080301014840c2444c6400c12540000c00039110340394284100c2e610380c0700b50304080c003040c040442c4240301d84005004c00e040302ca15030060880c0c0c10700342e07405840c07030b20307090710101c01901540c40d002c40000c1c101560314481e1540d060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 238013390 1250 238012140 238012147
    0x40504030e01120b0a09090516080106030b071704142109030106050303120406050601052704140f0103230709091209030c0b1e0c0d03050112020306040227010b 70
    0x20003d00141c5544005100780760400301c908002d074440380d402508407010540c001451100e00d0415a0401d61315000c40a00300c3d83e01003001508820540000043d00d008094007402d50b107030b54a05565548001494041c4800300d0000913020503441e0302ca500403000c4142c141c503103400b450507403402c014050a0a64100c000302240b01000f5007402d02c60345000e40810760046107480d15901c2c0520f1803690042c001845107888200041c0c0a92190081d035102d1107655080310300c0da20b100700c03841f8030304100c2c0c84209000303a140a051210480d03450905501505000415880d40d9003551036918003001849201c41145c40c41d040d201c448010100240002802001c90020b65030031607190000062020302008402c1082d00c46c030600201c2c00c0c00180b50120b60020307000c00c0c2e480b4170144501c50108a04a50000c1e003141c0403801e610303507400104154640c604283e500b0006680c80707030784510852203250800f9415500c028000b800509010114040d0603289081e0b070b0300740981d4408a900e400341309801544d003460b07020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 238014640 1250 238013390 238013417
    0x702071802091809011107051c02010e06040c090b040b0d120207050a0b07060e01050601020d0c050c040912030e01020c1b040608010903020304080d020105060135090d090909031b050c04050403 84
    0x2e10520101c48001210246000c17148d44810303666182c03220800a0f15480c10740b5150005000754014101182880241d47c00c62400c1d007480c184c040c0c114410303c80c9960500c0703003103c0945460721448221001c010030040000056403600c0c411900b00c0203007800ac2d0b106020022441c0d90340c81d030049009200035a0260354a540d0740c0f50039070aa888004440d072590b130404040c81940d0381c010403a0705003071003070f80f42c0900710075400d0500c1d624160f0070310402c50b0003500d04000032040c480d501d000f9001c501d035251400e00404140b0b02c42c41d8200e1040030640d0f080b6400504074462a18030940c05003c007018000c00102d140d030b07120083c46003140c40c0d10b001180560704c001000c001c213840c240a0ba070456001030008000c1c52520800182200710a0500c0001d24244040103200885481c038020714810051080c0000619013803c280e80d030342010004a0b4007040803510006010040c50080302c081503415501ca0245000c85040103088003810002140e09000b001d040c05115161ba106251245020343c1d558103c0d032440703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 238015890 1250 238014640 238014643
    0x60408100e1b090a0609020a0e12060c0a030e010f0c031410030804090b01050c0106060e150309030909041a0a020d050105040903080105090601050403060504080307030e060702071802091809 83
    0x511076208150000c0b2030080040c04400010040800151002c0c1416a00c500c01e60b801050030341c00c002101e5201241c00c802d2a40d02c500260b5a1000c1901d00041181300020003695849040300d0401c40e1040402c11080d58030f00c65000a181d0a0f6901c0c000325407500d0319001d000507115805401d8000940d140e003500744017030030f02c0700150300070098882c1d0071071060454440c40218480c07030168101d910707110702e01c055059108008841000f00c04030001c010a40c0c84050040882810340d124034407131040044e00c0c4090807101022640521000c500039817030719950009111601c1d800a105603010000d89118030004441401d405204543c0c9410044e9a600c3d0924440115107040e00641c0c000d500d00044440040e030081e0130641580d00480c2c04005950720030004a038580714a0b08000d00090070001804100035081c800b5501620647d18180003028405110980e185802c4680000691100204202ca010118a01c01005807009405407502d40a940420008480c248030104000f10810410040c80720 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 238017140 1250 238015890 238015901
    0x50d09050108070207060e060919030c051504030b180f010c032717090316090e010203040f0312020403080f0702040b04061203030b0d0c080a0302060708041703100506040810 76
    0x7400c102c1c1c030905003580000d5036200280962001c4c0451144000300b19540e46083d5880d450004204134000c1d1f0079400346041294080c402118480d9034010082504d00c1c04031202061540d150300018107140c556241c089592001418892040080c080300341c03408842441005003400d105000441d0381461380100408440071400c031501410b91a13480c800300440c102044404558016010845182040716140d8442c070a0201050b414403030f25200030301c00400c0140e01780454012000401803000801226070070307403004880c020407084044d5203410010340902c212008040803110b0042c01c00d501c0e80d0b40d000d00b55106041c8200c10300c5011078040110b150500818268403015282031048900d00a0440b40300700000c5801803d042e02d4130369200c4551201c20061101503007001003045c20540d590007170358594118110a50050284900254966003e0344d00d49004a50144190fa030710000fa10312410150400340c200414400c600b000062184d42d050050030140114001601c12100340c07803921000c551 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 238018390 1250 238017140 238017149
    0x1323040c0f060512100b04060e0f04050603030a050f090a12021311032701060e041407050f0d26030603010609061404020a0203120126060f040618020d050d09 69
    0x12240d590911240f54020255441c80c102548441c04a0704e8000041c410320b0540d0704600011a00841d0006a266004103450000d250550b40d0226404400042c001603c00807225950540c0c0f04015282c0498840c1006200701e410001a05080002c0d607c0056052011075200d03202d4440c0c92050b00c1c055140c0250500454050980200414120392089040c00c2c00001c0c0420b000d0480c800101c40c00130340f40c045200040100c84c008010701030700d03400c882807030400641c0d043e01c4c042034189003611100d03000520402030b40c1c0000e2860040325201c0d010400306201a5100f1070705001009041c000224100c08011840c0d01d494071000d07180d19016080c90b0850300c155010541103410300074200210340549680c01d921344800e0f030700541d880c0d06c0e20134140d00c0d6209003007424000040300380000480018040c00e0030303080440d414371724aa415a0002159540c40c3c2600c0c00303d15000850086000241d641d440350044c030840b086944070b2540741303400050748000c0c2d4a1042d5442d401c1003400410480d44540400c0251 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 238019640 1250 238018390 238018409
    0xc051003020711041806050c040e010b0a020304050f01030609020307020619060e01180603080d270201020c210a0308190e06010e090c040204031b05010206060f1323040c 74
    0x1024507200d0040110014100030700481d5555005d18078040551520501d29070098018011818002c008070401e03841340c4120419010341e1400801e00800345806c6070b41c0071915a005606003418842040f03480000c02040d20706155554400150141c05d50001d5481207400b074000d810070b4541005000040d400d110940a90f091500c1000d00001004107501410349024540d410061621400c0050052109402c0034020a4010840c2600326640e82c0106540c0704002c59060700034800285816040d4082c000300901580240440505078140680c1d402805c0c041408588212901c03159038a041503420042a00043c20003010440e60b440d2400058442c3c16031110200002001180c0342900c0ba030041c0603056003440c1c0d00001c02c4101d0420441c0803042071000744110350303441d40c81c40d20740904100311010401000206000007155030003c03031341500c104405000c13501400160000c105140d4100d080c0740c0a500d546a9900e501080c01400c9104009441007014600741801e0400180031840c0e1b0b408800c00307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 238020890 1250 238019640 238019647
    0xc03080a09050901120620070c14040912080718060302090f0904020f060a050c07060f0f081603090512070b0f0f042d2f0603040c05100210090c05100302 67
    0xc074a505005c080490340c03c000000f44444609910300065400d030010201108008034000c402c2c014411000c1d022036110b0508061158821000d00003035425011b805021940140003202c03d048c0107810260707101e003040c90240d42e01407105445992440240d081500000da000c990a9821708140081016a800803581c070f40702d0385015400254401001c00d15107008030004180060000e000c1c0c000d407140c40a1034401d9515141d00d8800040000c0304a03080100001c504d143c641600c130340510400740c000c01544400010b10780303030303404154090030480e03400300c846201d008142e0009000c04000740607031611408422040741000c5005610180c1c002d000594007007188402d210001c1c200050300c41d521131980c0d5460400d0885d50b512544284003a2901403c6404443c899900e260321714003000000300f02000c100408080ca400900041d03003c02c807002000030261040900c110711304000d455010306014411a0780c1d0401c00700f140c40030b82e003101c18120382900b041c010074041803518042c0c20710120b8452504504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 238022140 1250 238020890 238020899
    0xb0312040509280501060302030a0b011d06130902030c0415110c15070204050406050f10050306011e0503070611070501170406050402030f12031501020a0803010306180c03080a09050901 81
    0xc061030007038401d00f1411010703c00c0034000410210501e00c0c0a0030110100401d6a550901a005e036000302e402e0704041303161650300701c4a980218946e041c40b00c403101405054481110030310034207071320501d9150003620400000040243d8079000441c1304d030070201c0340103403902d14005a03440d01501c0b0055940030300c0b40480301e220041e640014071a0a03001d01315041041281003c242c4600c84c0304202e0301a401c40c0c1403a04020503c5440c0d0001c0780120303c29030168034036590f4400502c00802d00d501420798550032400040180750b1140120104e82000b6040c1000c00964075400680741040941c441001b00b613800d0b0302500076580500c1114010542030900d020412a410743c045400e5000038001080207581d5030107e003e5490800a808904024804031a1000c102d0405098160000c45003080428800780001c00f00c0e5101041c21025150b000d0100c40c00d603421a900c08003c1c0054809400c1c84400004081010814104a05e0f000310300800d0781c1076a503080050010701040c1650405801407052200400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 238023390 1250 238022140 238022149
    0x8030403080315061605032101080a08030603070905070f020601090b010906030f06030c0f231507031e090e0f040510151206020910030e0303041211100b03120405 71
    0x96104900402d0315000100f20400140e035409a1124402c100c0004540e1004000002004101c1440007082982c0c001101514280250b8424080c4440c9500561141d00010340030341e014641191000742503844840c2c4881e0000200c0b1421202c3c900003415480c0034503100c40d0144012409800884420303c010103103100081c0448001e841a038042580d5007009814868543d4030880255500041001d182541c1d400d283d41020458041c460041ca80e5101c1017459041006045192107030152995442000950714014190401c080a13014000d006400d00700104003484451035180203502c030f80c181c160810700c4007442030318001d00c44e10541ca166828840400c7d000511210318115425010900400606001c401400990f2140303aa40303a0000d8903004001c1c2c0380d0042c1040c3c0e001590f00e0f0400c040406401c1b0140c44900b050b10605400800c04280400c0d80c202c45048a0b058074144002d0070001c04450500c0c4c008042a0503001940d40d801c7d4240d1807070305000c1c2d140386103100009130303060a081c1400034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 238024640 1250 238023390 238023397
    0x1003050412050706020720030d05040f0e0c0c0f010504110301051b0a0525122d09150201060305010c020d0915021606080a050606031302010e0f10020a0c0803040308 72
    0x81d0038050041a00810010720b43c044500c86036021028100f00205001c0e039412509154802c2c030320901402c80403064083c4a0400d0342e08840c1c0c0c2540200d0310714601580d41817042c20281200890010810100c43c0c001c2c0100403000c154107841c000001d02c0e26081c10310545600040700c00f548281d0400f411712142c940c214100d401e10101001500380e844044480c01c2d5840d00c902802c07491940c1c0d1300034828410b40c5510040f802c80034001c1c405007550001d152000c50340e040c1507030742c140400761000303490418018000810048210090402001d0503032143d10f4010288a00e40b14080142c0d10381109104100302802800c2c4c10144a000030f000095014002078074407600e500031707012003000c01d080d480b40c018801c0101081070400c004040c6c00e030031707280c007001803400d04126115100c09051402150103801d00702c0c1102d101d461191821001c1da40c2507401140da2108504050380d20502d14000c14105589003011004c80c203d66800800d80e540503031514810400c40765010646903002440104041407100b8206c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 238025890 1250 238024640 238024673
    0x3040608130b04021e04111902060f19060504090809040b0a05030312040f0c080a12020601030807060c030b04051501110a020303071e0803010b040905130201090504110714010203010510030504 84
    0xc1800c040102030004140c00080d145c16441030400304441c4006c100d180003043c03421440c20340d00808006100060780e80d00c00a4406042c0c8104000001d694040900200c00c03a02076520401f1508039642c02c0010292007040405540d145800079070290f0300c1c5010310540d101ca600641d4102d58040c5810300081e02c0f40103062681a101d0318144c00101084038080b041d108541d4800d205142803501e480c3c1055903020b203803904680420108014121143c000030319141200c0d070140d603103032400c05160b803210050f00c40440c0102c103250700c33441c2d03509032aa40c60055a10410a40f0030110311038140100040040602c00b0007003113035800006e07040001d07031000300454400c9a007200300091000e0b240c011801868a00403c06050305001100200f03285104e600200700f2145200428040c1c1d48941048050310180c01800a010800f194010416814103403c00c100f459a4180040c4c240321140d01c4440386400780c01c4040ba1769075400001482103141c06e400f08902c041c0c40d0301c2d08210a19003566800c1a200700c1290 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 238027140 1250 238025890 238025899
    0xe01030f061a130308120702071a03041202030d050403120b06091c241a030c010801090b04060f09090b13080423060a020a2114090102070b0a0203040608130b0402 71
    0xf01c4075000d0000c00c19400056501400f096a05c8a070130040c40d034001c10640d19200103000c3c1d00f20000303050800714110304a140c44541041d00c2c58640b903403000c42503811410040d055000038045d00da520070091088511450003901e0301280040c0800e1a0700c00c03902d1914161b0301c204010f00040f000f944640250b000450755060560403400500d04010000c40d141d106034181080081113060716000980d007100026400b80003c2d004400104000c0585415039140002e000802c00c1c001000415450313000600b034400301420004001b521158200d58440e52904942c43c0c0e41d440d2000d21040125190322203600604031848a9040a02d9582d00301c2140305a100709038130750304101e19440490961040307008810800800b170b81e543e00049800a9180c000541c001d4403003d01048034841d42c6491305030018038041842e614542d818402030014099600001c64060443c880c484000c2400e5404d0360082c0712911041d0025526a440c0c01402064003400410f19100e0040d03800780e090029041085040c0c00682c101d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 238028390 1250 238027140 238027147
    0x70c05100f120e07050d08041e15090b03062b03020a15270c1805060405010501080601050d150302032a010c0c0e1b160302250501051e0301060e01030f061a 68
    0xc00ca030b0103008d5504140e50040700d038581a807000810040100c101c407850281002c1c44441c00100360380745001c52003508014041040010380c145062103480068008000180c1016080c084d00034941c03444048080300581d00c1420a81c00b032040d801810071039108412810301003840300c1c0c0c0c81848811740c003214a5904002c0f121000c410002d002c5003440c060041d40c1b070203111142d081e99410000c2d00040d21410701a502c0c000021550754441c1201c42e1041406031517240c64020800624002014610405405685001d4000c40182d6007030000d00750714000c0b00466010110b85420301746c43c0840861540c0c2c180303d0035068180008041241d02000c640059503580850741c0e40d0660034001c0c0c00e151010f0a020b000000d00c0c44081401c0c100b841807114000d070f003140c101d8501030312109038002d09a1011000d454881800b040030758455001040030b0702d64400e4005645040b0400c0b1140c5420a802c08008071300c41e40d40200065915208010b03010103201418040390345070440081c0661070b1040070700c0813980e001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 238029640 1250 238028390 238028393
    0x50705160b0a1409031606030c0207050108060d1e06091e171612081005010903020a05041e05090a02090a022a12031005090c0705030906070c05100f120e07050d 70
    0xf801511149000175043d43e1112a840c000c800e01065103005c0d1902003850700f840040090310000e903480030b40e03006860f1074219441d80400c006861400040c2110100e0440740b440022500c000b4042210900c201004203640728540b40c540903640c441e42c880d50070a900f030344001020542213900e180c2c08600c0e20719041d41c0e803c1c43c2401c00c1140080100040c00f40002000c502c0040340d882461984175100c86481c1500c0b00e910b5000441e0b10b03e410f8030010358490411319003404113190541c40900d001150308a200c403020000c1c8805426158216007484050b0801210b1900758184a04820f50109103240118a054800400c60326030250290308026000d12440020701d4052080000348401d115410036652680340c4200c124480310380c0350051a0040d8032180201c0e410fa600a0700390f075690365110380034604209170003041c40350343c0e0001d0074180d07100d400001d8005a56282c990f0003448858141e0782d000c07000c0840a0016214000707070008508003a1900160b00d05540f004901442501e00868030b100604a4a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 238030890 1250 238029640 238029677
    0xb041a041505060411030708010303110304120206030a02090a0308030105090f13110105040f030c0512070806040b10120303140603030c0703080d0f06080715080609040204051008030406050705160b0a 87
    0x19030b41e40b0191811700005005030282c00c224258100c922a941e00c024100e050703e10720b42c607030046200f03013010700d50301210031001440c0c201c0c0a190300a00151005003000c62040000c1c00040040d48180c4801c04000014405800c00a242651110840503582d4860510710012076003000c0041020b4804d070b80c40c5040c1d8071540c3c8540c1c12640140102900e140e80b25442c1e0800d42c4010009100300d910940403c00c05031150700c0d01080d41821070300b000d80501015a9503890741240c104009288802501c1088030100c1d11000e0041010340b0715000c1d51300042c0510409052043d403600c0a440984680e20a00900c89d80e403600180d168190b0340c2c88500c3d5a150201020035002928110281d54032b0b25003040c2c004100410300180d10411500c40e02d00c0c20074094400340094944500030340d041c03900314040350005000760601d034200a81050080703011a0059995203a5541190440c0e0000800548001007400c1031050410900c44000305402440141c0d83c07421040d03411920560444200b40184501c8114a8142 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 238032140 1250 238030890 238030901
    0x304151206060527090903040603051b041701090210112a010f0c0501021602030d030c0203030a1a0a180b0303090303031b07051b1002010203071d120a0b041a0415050604 74
    0x14080c1c9002182d0174005a100e840307800902504001a24010018078580c1c944e0327059034085091407480c184dc4c03504240c0c83c05802010700034249400d64070f412015005032110407807049a803031642e581100d81c021034514107007080050b5401250500c111200c0c04000d01082600300a081c2c82400d282d0071490302d240c019581d48140b0180a0300b15480400c403400407401111180c0d007042c1c401c506841c50009078403825800c540440d54081c0c010b0303102f480003540307460b0580d00c0701a00e040b4002d180e40307554580c40002140000150001c2c00341500d01c040c0c5a501c43c1160186100c82c410440c065800c1040c00c4020a030340c0c2c000203148803202c40c01c0d1003041d00181c582a0440d01b03015005015a404100e800da03140300041c41e101038890244010101c04e92020f88103200b43e9000300141e9a8060900380401c2003441c032401001040303644044046807601040b082001018410341c481c4800c00401d10781400c0618030144120980e19040440c4030070400003900d0041c0702c03811980341001c0044c4070344601e40414001c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 238033390 1250 238032140 238032217
    0x1315030b0a020915030f270f07051203090f06090d0f06090b060907020a02130e0d0903060b030d0f1404050d0305090a0906140409080c03041512060605 66
    0x803005041c8861852140c00400e00888140c40b043c04441104003000308074842101c12950001490380070030b410381424988004518541180344040c1d80c3c40d1228503083c60905240008160300240080025080c04851200d0070084100510304244240300803907803948020079800d105660000e410b144c0c0d6940c40740d0481b0080c1c2c1043c0000c00070822458100010105035900741d40c40f45003400054802d25181c45464400e2000783c1c06881002074503401d0003120b81170483d2404100780c480d2000000d2030b07410040b070144000250307900c44840780b960070803104503183c0c01030103400780e044065400a0300340c1240358807084511601d80810309240030a03052078940180c3c0c000035444a400c05100d4289613020000d08607814045617041c442d16601c1000008a401e41c2c4598a05020b0a400b440c48620301740e484410024060a03003113161a02c02d4442c00d0569115030416960302c505011840c110340da200d213821340303000140c0c1801c028a0342419800ba0503400f6092100c80c203202c5500c1e00c4844d16200d07045484221 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 238034640 1250 238033390 238033403
    0x90909240604061a1e0301050d14011b0c0b0f0f0c0a021002042c16030c05040e0103030f12140402150d0606050d381507060203190b131503 61
    0x40c0803044c3d400c100740d000940340c0000b82e02156024810041e90700c1100d0403510010044041c00034035030f0311082c01b61203840c101c075501d540c0c035510015a0501c2c1d80036085001210303924084010014904611840c80c05001c060848101400300048400d48900954000203c81009074480c07103200c13001c0b4a84000b0100e0b04007800c0c0041000602c01c0c28a4400502da481c400c0380c000c0380305101900294000070106c0c3c140b11100d10448100500c24000e0b401110b00340a94a840c42c505a00c0b61050761940b9001e074000c070005051a040f01c8945c952005440000c0780805109101c0403403030180e9041607000260003c0e11410030040d903104104214004c0700e4001800920900c01e85a507000098016040170340d003c112103051449e540141d510071a00307010610005035401d03070140d8460860104d8244c0000c0600e80006059002200d50305040e0080c1c0425880741d5009aa43d152209090b42718814006036080240d00b00700c00c01e0150745d940d900070340a6901e0100002a4044041007003a0001030950024220 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 238035890 1250 238034640 238034669
    0x70c0305010b0a080102070302070b0912150f09030304030804030f03091509050c0d08121e01030813090b011b21020f1b090408030907031709090924060406 68
    0xc200e019000584040030484010032616610060749091348520070380200141c000903011f104440101d0040e00303501320044c141c0a640692001d00038a04080e030501a942955581c040010035552500100e9100005101960071424180c0c0c020b00a482d020300020b0a000310940d08099281c07096001191013a002030620390b0700c0b031035801c403103001b000070010076034150184100501090802145410f1102e910994007807501448002a40c40304001800182c002c201328036504940a0b0034a007001c2c0a54001e50906a4820912000740c2808110341d010815081c1000c400c03421a81e042101c1090b0074070324690140070b44505141c20103c0d0480821200300080300301d40c060380d0b9507900281c0c0b24409591502140e404c520500c882e60b580c1740500040d580c0c0900c8441c00180060f103d075024582041809088820082d1a90f4a82101c4c402e403280315000d040d03001c00c0010141c98050315907070700b04c9070203000f60606000c4a01c0d5801384200311403890f102001800081000c40d00d070f036840390340280520f4108280 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 238037140 1250 238035890 238035893
    0x1101090b041212050705040e09010605090705120f012102010309021f140c03090d110d14060a1e020a0c12050a1206180f0b1503010603061208120408070c03 68
    0x126000291103810014000f0360203800c01e41900d101c4c681c01152a40c0b40c50781054902480d4040c0000e0080c188440307075407070300c400042c81e032690340715a0b010b600c1580b41c0c80d8075445640c2c02c002100900801c05a0200c0f1a0001001407244071640d40c1c0d110350014000300a400000e00050703004c4c00009000030b400004140490201640400c0201029105582c0ba0f40e05500d04040302409802803940040d034a4100700419551864880240c8903507074800e1240c1a1000c94134000108220254176094501c61400c181300030034540b00744105a40310700d540004120924000c201d41188464141140044c80d500103019000f82e4010000e00b0700c8154050302ca075441d0030f01448002c26030f03001601d849012440c11101043d0010407406642e040d103010707140703480300c20340c031407660801810f691040c0400ba01c0e615041c0704140d4072481c504034500c0700c42c00d256681d25454840001d04580d1030b9400302d00c18503038072400c2c800003030110b104031345c000c0303259000001c02070301e0b20f0500a442e8450000700401d01190701d0400030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 238038390 1250 238037140 238037153
    0x30c0c07030c0503010e0609191403040602030409060806090a03030f11070f060b100f03020304081b15010609120215160f0308060f01121a1503090c0604151101090b04 73
    0x400f512010741c024884041c0d410074042e559a010740d00d80e603403504544c00c80c2548091154100f40c03294020002e036084141d01c903003143c1c1554000c2d00310f140142c10004e0b00b840758018500030700001307040d448001c01e2540b4020329519190075000320b00070308064a600142410311401c0ccc00c140c1c1c4071030520b1801075450300c2610742400106000a03044502e0340c20a0280031480c907000c40d607503071705c40703600e48402003010069a0304030025480104112010034050001001134249103400030050702c420300080074203a00703a076892035852005074005810801050024000b46400380a0400d41c250f040c4c60244003211032410b07414943c015481a52a0625140c2d880e03810301200180c400001d03406030b109c84209440c0c560503c18403400e0002c003e8003158414441005440d480c2d40442007803103046030b18002048042001072600c400c684405109280080b0912610440910200c0d03000c0e402100c0070341c90140751a00c2d01540800301512a424001002e400e002c1d0800290860030446910100301d0500385018540274 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 238039640 1250 238038390 238038413
    0x209060c0c0f0603060618010c0b01120b090601081002070204110a1d0108060622080d120b0406080a03080405010f150305010509012f0f0406080615120606030c0c0703 73
    0x2900c01e0782c0c0d5150692050500d07100301d90040030040c0209141001c18420082e00e601e21101c0c660401072640c1d151804185422000c81c0a040d401c62204868005400c00e001440300c05050104a60003410040204150009082251504204d0b025888036414000200206810b80b088030b40f0110000b0034414899000941168041d840c081a41519001e5401103030324000444981d900804100a07000c40100ca81c4450201800040c00b012041500c8400c40c1d814aa441907143e004504042c40b80400031100d4051010258401c0da000c00600b803401d85840d55402e41a00c002d41403100b08000329080c400e0a410413000c11190140c140400d100980c0c01c415170f17902e94401540c00b5440c10010071781001c07040c06030400c0ba0003828054032030116101180e0140c1c4000148900861100b08012803407038490070040c0000740800d4403000c82d146000d1040c4a40200b0520380159480400c00807400341506400c0c0c0300341c11450035130b000c1e0b80701e94a001642c0514801c404e10380407680300300034001040102c480500d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 238040890 1250 238039640 238039663
    0x120602070606080d1b03080f18010c020303100501110303010b0a020708030a020c0405060d0b041410051501090e13031b0f05060412051e18060d0912090b0a0809010209060c 75
    0x2010441d410b00c0c045c8070403001c01d40000030700289114010501100ba0051050f41110f05d41c025641c0e070040301a4502e08481d840c088007000750300007008114801583d2507543e8000e00080c00e018403911007403c9010742301d00c8140a509800000402c0130040c1034820440900940300d0326080301c0d03449401e202c0c080d60751120500182c1c40303541003600183c05400d224820940d2650f00c1100c6894a84942c0da80c0b4040c05d0000e0030035055072140d11032807480807400b0300a1074060710081d03000303001007403c1030f000400301c082e181c00c404000c40f501000e02950500803802c95030f00703540524008a00264007001e800c00c4201152000d44054445440c0805100010889034040c80c417900508110341204442507807680511460f003502076000d0000c0088110001c0700070601200490701201c0b400b60740c60300040c1303280c0201c80c400417039030398030b404810820038080d02901d007000041c18004501890308201000c0d500c02c80540310100900310b40440c1005c0403d40513645100f03801400152160340900103103640d8a1100d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 238042140 1250 238040890 238040897
    0x1b0212031503300901020d030c031104030c05030706030207080a0c02010e0907080915100501032301120302010f0b0f04090c05030d120506060a17070e130902030c0f010801120602070606080d 83
    0x18003c0c0d4880744001118880c1c0d206801a02c0074880452090340202a0301c1520024961501400e180da102c845000f4805107118500c1000c80354100030906240500301e40048092601c10801c0e0000b05452300b042d00c6101250389001c00e4079071010701c0121020407110030890380005818081c4500150031074412485040b020040390703070407070111202040c003500503a003200030f17919007050074420740d486a0014480d001442c0e811000e180b50401d42034280708002d9000c3c2c2d0130351000c00348070010903a0a0041c129204a480028015024800002411480c540c4c5180384a59582c0d00102d0800c00710980d00760042800a09403184541d4511000e080c0a5007507074a42400e514240004000d45450020742c0d010b0015070391042d01c40c15466001107403241000d04860b040c0704c0468462100d65540503421041c440320441c002c141220301d4414145082050900c0302c0c0700301c200b076190000300d03680702000d54115551150106204c0619040040091051140180c0b920341000808a0f00160020710a00600350a55 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 238043390 1250 238042140 238042213
    0x61b01020a08090d02060103022107050603131b0b03220609050105010f06051e0c07090e070603050a0513060507050d1d0d05030906070804031413091b0212031503 71
    0x10304c200d84400007404000d502074010100d00c1d5141c1360003c000c416004400d0110341500707846000042840c0c004807040c8409190a400300b000300400c0d22850108880300700040d1061a0418100844d18040100b01c18001a641051040e641e01e0a164071b200301600140200100c6026003003071030203421309018507044080c403404002800b52184003100d040d006032091040c10f0b01d40d00c40394256554031002141e903270307846801c002007524144c520600000010f080300070301c2c0082c9814400ba0684100410000203685400108950160485103180e01a03074044800070303460f41c55103810f80d414020403185001152501c2491482220004010424000c8003002c40b25140c036911000c49080c80101c4010004d41c115402207a449405291030307035081840780c107250141407401e0a00c001203400520700342c0c0410121410030030504030076124000d0b4081c86d10048006070300b2400390203552640c0364440c01c04040b800200040444441454801c5812002011745800c141c1007840b204011080281e0340400b0714106 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 238044640 1250 238043390 238043413
    0x130b04050615070f050123100f18050901060b040906140301050403051905070206030c030f06040c0c02010c02120105071e05160305031308031602010b041802061b01020a0809 76
    0x210b10110100c1100741e10945407200700e5550316044901000d0403035040d920340080a0982000b01e01e0314404010301d80c1410b00c5441e090307520216409040d0b0001d1005842001e0601103007a8507180e0075068194002e0204041e00c4888100740140b81c6544980340000b00400c021480014a410100865800d007855041c2c0350f2140c1c0c1090700701d070426100100494410445025141124090081c10545505100d0b0030444d46801140050b4021285412084000020001900c4240075070039041041520100400a000030001c0e11611440380084d051012240780c10085546001c118043d2a8040000340703c6410020005010040001240e40500c0041d4101500840c4944143d4601a218051608a0941d21303141940c2640c0050200c84e01012a80c4c21800030483c2c4000560040d140080030400303032000b08070700031300b103816040c0398611940c2081c2801506445a40c0c2160110390101d40319640c41d407451800030901a404c010321400c42d400410901c041d10741150442c0d10902d0000d01340c03100b01884 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 238045890 1250 238044640 238044649
    0x2010b012303040b0a0908070309170607050a14091e0a061103090d020117010602210301140913050118030e040b1e06040807170f07080a1709130b040506 67
    0x9040d011400c074050002802080d038083d106a004056280001503110640e01d5201203684044015800f007409140300b0400307408030b2042c1020718075100011782114200804004d0851140d5902c03101008072041c103400680400500300c9070030100c010701681802403044254074401104021062080891341c030000b420502410480c440791100c04082e528101810040200094040c00240e04011242c184140c50503140100350703001e00900e80003072005410000e407411040460380d20000c0a560300340b004020a9000640c4800100310407102d14182c0d07914400c0114003000a090042e000c2c0d800e246c0b03084e05d8000e43c103200c1030007075000c0c3e6200300b5180c07041402d0105480840481c280c0120304441050901001130704800741e465001410b0501e8903644003080c0389806041e409c0151003a008003619207400e001003004500340d8100d44080c01c600c0e441e1030031581d1180c0c1120700c06080502c200f40804114055842150b14041d00280400700320f150200c0a140203004141c031842c05a4035210202c2c00c903181 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 238047140 1250 238045890 238045937
    0x150a0e1c032d0c09030609150c03020703080604090305281806020604020d02010504080307050c040b0f0d030509040204091404120503091e0307020d030f1206050603070f0e06030702010b01 82
    0x4080d40180560303100255034000d00716921101c0402c104504041700280c042e0250003a800d00804100c80400c2d81040020708542c40100c50b0000d040c81080540c1c0000c1c0c008401540c08041203e0014180180d401d0135205881760081034a000007d528008007809030021100356000d4155444403403aa031020301505032a0040d000d802c02683c408400903006160004031940094810701d082c0d420582d6502c1e11034550741040a00f29801d4200e0704010500381800d10840c18828001c644002c2261070f060040b0b440b002540001804000c000600729225466940440d0000c2407000003c000000707900f041c141580c903060303034101c0d0130302c0040080d1103045101d8401c1e60b0246601c0340c0a44003010303800c4000321700070b125140e40c8002030009000c2907001d61748151b24201014041e0320b0302c4041c2c20788100000c0400c242280c41c100400d28020050049855003001d5980c004800c0c01c000e0039030008540181c0d100d40345040305991042d000810880303140e074107400c401070b80344c82a00e0340b044081303681c10044032192 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 238048390 1250 238047140 238047191
    0x5060105030a0b0a0b030c0a080d020c090103080f0708090604091d0114220501060b071b0303050901030b01110708300d11160b0f07050309150a0e1c03 66
    0x581e0400304550b084d907584400000c07403009080b2a102c25a03080441c003000016803262026400580e0780303000c4079805005c400f00819084845070200d42c110303650304480d400703a0140301640c00004902c4504000c02c1000300d030800c210082c80315449a81e100001da002e41810340d41205180060003c03403400040500650ba41143c0f40f191440305941d80500d070141c0d1001c540c10402104015000c0900859028490390700603060001d034040c0c1c1c9560606005100c1001c1d85107021940404120400200c0d378024152864003100f440c0114001402d0320040b50441c2441000b01c1890040100000701040001150355030103507411400b000c0f503441b562201c024001130361003014000508002070035010307400303074051810000c2c90311040d400e110001400255450401d10100c4a041c1c0c1030082c4000488031225080d03200509281c03c91079842d00e24210794a5075207000b1030000f84001c44000c0707144c0359030300d422841420101208450000ca42281c02c0340781c00042001000220b4036050816102c402c0010b840d60307150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 238049640 1250 238048390 238048403
    0x9060602010519050606121005010806060c2802030d020f06090102072a0b0a090f0906030f060e2a0a0e040506010326030a020a03060807050127150206010305060105030a 74
    0xf0440d032003080007a2a005007070990050041102036408618042d0701802048004040e110340d40c00c0c000090b014070b10207844948100800e001b548400340c80000e1500b0804203546a0303120710000900e04103000a030f501c1000790325004218074400328940c00501e0b40c4c8003e080710100e900e103852712041907080b44101c2c5030160045410040d54403106c5441d1080c19800071004c089030300034030743e1000c0c1401d00303030410004a070014010b403008020080102c003c0300301925007540100000751450741c1e200c42c1c481d01e0840050005840d0b480c01004d500d428040c20021a00c962681c580150740c0320080c45140e04c40d002c0080c0f14084012006c2140e41e80400782d03070303c80c99001005020603400c6480716030083c0101440c1d070250745003000c454000784840d034001e140940d091002c056243c4a0350040038040d1440e54001c1d500c00d500400c0e0030407490380e0101d60b80701d514500005180d5203645d207507900e00c0c1c3c5481c160005403846910070000f90140380d002601d40d040328014801c1d40c3d6566210401c064903130003548409001c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 238050890 1250 238049640 238049671
    0x306010f0905100c1a01081e060c0409091502040807050a080105010302091f0503070f03021807050a050901051201030f15050112020f012010060b03060303070b07140d06090606020105 80
    0x640340108003c5012078045c0807001820150380120701844002600411341c07a800145a91089140760401802005076a01c05020760b8509404a214940600d00c1010011a1a0782420f0248001c094210000820010080d5a120b480711821640c0e0040c0784a40d40c000c0c140340100180c40c0106101d03481c1030325401003561419443d0303608113043d50640d064810300c1200c4881000176442c0e40c104030329001400040007411000786140104000408006100328000000c00e042103452503001044519a0256080c495110301c00c64004a07024090a81e80080350903124001005001c80480245c1501c0d2140810025610f480149882915020b208079480c4064041c0e440c001890f18841c00e0040d41d0040c0341c058001c0391a400c002c0e414080300e00511005401c00502c0e82503425490158070080c00380c9050551030b500706900469600c0c0300b010805844100c40c0400704440e2445202010b108401444e08503444030320b1076070304c10000c0074030b4880d08500031310f040400550f4034010300450b0321403040060090380 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 238052140 1250 238050890 238050919
    0x20d02070f050f0d02060d020a020a0210020f0a021002030c07090e12040305070302061c0212060f010f05071203020f07050123190504030306091a030d0503060a0308090a1205030306010f0905 83
    0x281440581012640403800f0703c030b0390452621f03038409800c2d940420f034010076580350f19005010140c0200d03154034007150030100403400e00520004210b45015070540d169110101d402c0000ca040d0302404400c00c540e802840c01c0041c900c0d40340e0300701034071003101c00007030f107000c030010024501c01c501c26848005e09507000030404001514099020f81291550031040c84451172503120610101c2c1d000076a1851030000c003c0900020742406e105181c003c0074207003011000882c5051014069026180c001098599414107800e0342c0f80c46030301030310342c07615071500d1594903081e8030b02e070071406800080c02c042040e011008110840d0003441d40c1e6180149040c0d0541c0d40038409000ba880007070500200140c050648500c0009008201403085500c0242c43c2c1c0e0407003000e02200c00405042200c0d0395044810001c0500034007095a50304507005084990007401c1c3ca90782e00c0254041004200980d0101540c007891040c0d40781072200c040b004503c9500e00340d99184c1c4141c00e0482c10b65882c0340c1c40c010386421034000b079600c1d01d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 238053390 1250 238052140 238052149
    0x6141009060804080910020d08010801050c040e040f020d03051b070b07110406080303070309020321090904050114011d06030609031608120a0b090f040b0406090f020907020d02070f050f 81
    0x243c006000d4403100340b409500d40b0208070400c108010f10350050b8891481c0d0400e1980c130040607805003421100030f00403030502c0c1e0501031081c01940100b50403005000081800c0100324058100210342c00381038841131031641d0401134000d421069205003080c007800084c80c403001c4017148400540740154842410310a2a407241814034149036001e50b041b40c0d60721030102e03c200381040698840c5409540100d080600c51060508060314203030050351030401549141d4441e540002524400d08041c0c420341480e5943d400c01501400c040c0d1504008044810004100740703400030307000030300000605d8070a0310f5901c03a0310605540e44c030201c0b0a410103400a1044118030180104241c1d038450003038103941d08041000c803050008103003d0758084505965100d21500c50309080c80307030542c410050307112038070146015211080c503544e000340001d00340e43daa031038400c00700002c8848010840d0b03009018034805160083c006591184802c02010140c4500720000601412503074020090310400741ca00d8024107121801d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 238054640 1250 238053390 238053407
    0xa020702090c1c110309240403260406020702040b1c2a080a05070509010b0904020f12090d030515010507060c030902120a0b01060c02091503031c0614100906 69
    0x50030181030950450215440f18003c094281d4043c40d900b980d02e080821606140a08200e48440d8040d0405507400d104e940301c000d565400344e014201420f8900107120700b500301000c5190000303001401c80040c0010b02c113885e40a400300301d20964082011040d100100000d050440888a03004c0100c2c0307100b0170005005c1c261240c81014005019180c100d058000030706880340b10340092100b0b078000303004401403100412000004041c1a10b10040a5043c603180030107511801d0402c9020711340000c3c07518020900e04040351580b82c0104001072042c10100000c40e103c0c1d804a4401c030000e403d00c404038502608810b01c03007245a4050311010702d84ad003550768582c003910031084c808050568600c400d00158680d501807406800850025007062000c40c5000707000c0000c10703004901001402c06c086070050301c9404000d038014040f1407a641c106000440004e00e5403052811541791066010040d0922502e039400902c1039800c080010030f2606c1d20710090002800729580c644001513256074040146901810740c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 238055890 1250 238054640 238054657
    0xa02010c02060c01060305060406050a020a090b0c0a120e1002072105070503071203030c1e0305040c031b0f051905091b030c030603100b0907050a030e0d080402090a020702090c 77
    0x43d052440c100074840c2110f80036070050725035800240401c41080158480c2c00c1d405124210210b04120f282d94000300302c1080c501904182c190002002045401d00300300704090103034408148900c140d5200c50040042682c00c0340e150060f82d008504c2c000c10b90021038454169118546d030f0042c103211a0b024000ca414171500c05072402d000309900800c1c6a2024403401e0040d00c400780c0054502e520742d1800408403044081d10781c0401a8103c0d5400b405011940b007105803e041d840c0128090b1114100000f00d80516800100301d04a40480c00b40c4034404451800c0448501840d00424113556205100041c020b43c4007104034500444028411460810702c46a0014024840841402c1e2602c0e40701302d007a4000c3d9080c0d07019100100c20001103203030800030011008070302e4109101900b80e0a0101e030b510304010340a8001c0c08000308134201820300c40c1d40320540c00014241114440841c80701c000d00840002d03034060b030248204400242c0360700303054021205c41540c080c01a241e1941e9541085006401c2007a0b03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 238057140 1250 238055890 238055899
    0x5010e15040504020c0607080106020d08040201031116030e04060609031a090a1203090606080c03061b090d110109120b010302040c03020c01051e0601111f0b060a080106030605120a02010c02 83
    0x11600341c07507504c013802e100e480e160020103803070420506c040d1400c81d050b401181154044100030740d219901614058010398207007000300d00540d04464010b400c2c000c084c01d0800c031801c0d440150040c9a4000002200c049064808201d000c0c1c031040201d480a44034000541111801680070448050b004112644140c405040d112900e60701d0ba0380c44010031b000000d44000940b910004418803800d481480010050741c0300400c0e080580c032000c0394480900070710155007100c150380d05040d5008140f00b1144403010007800880d2902c0c0714135100342100640c4051a0000d5411440468025801901410040d8002403040304d03e030310759800c10004d00041100041016000d00680b00001c2c024028039000c1c10b40740e5203d00c40701c0c1c040c41440240788801804941003011350400d101038803c011902c04031084009103901007a00f00350000714080c0c11800040390308000006a51451161301c0010a8181e4100b80c3d024000c050344e0f48104411001c54500c4038505821029019006601440401000a10280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 238058390 1250 238057140 238057147
    0xb0307182408060601090806070305040203120403030302031f0302011b030e06190e03121210030f0c06021009080f030414010e0c0102011d0c1009080613021905010e15 73
    0xa0030780440e89900200d09421500d42409010720403003402003a62001c828a05212024945400c480c0e807001701800c104c040c5540c4d800400c0554a060204011566040e454955120382e2403031f000700298000c84002100400f10200c01d0104e00c40a1038030700c1183d405964184040d811f8200440c0c10891211084041c45508400d072401c46d00d1b84005020b0b6140e950702d20440c2c0304000380c0301030001c000c41c0c01601d110703410014409803100050410f541449203603014081d801c0d59904001803184403140c2003e0000000071701c80c076003005103020030300742901c40f103509a40051200341c074594181c0700e0b81d14001740b1040707050008100070612800550362180c01280a01403941e0051400790031a4454100880c4c11b40019641a000d56024000c0c200709201d4640034040d404501c2445546407188140005d218641da500141d03210707446031201e40003420154054400a0038014000b0261400500b0120f001d0b4000f10b00780300c461038000e507544040340d4041c5c4554424a030280f00b0013006035800c0b03481603040035051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 238059640 1250 238058390 238058411
    0x1e0106050406120201020f070e0a020a030e100606110705060304060b04090c03030503060114040803030a0528060302010e0607050c01030f0609140403030b1203191e0801060908010b030718 82
    0x60050a0061041c0c400e10f035102c00041c0002814040c40c1c241003e0036500582042100c41108608103a02541400c8016113418908404074043c0030344006640151140c4900440002407540c01401103884548031965982c2a07249210307150011403140b03a5001c041400003a004c526141c000b8401c1010003400081c03640324603134038545220a00c0c3c006400042c004400c0007002d50700212044240902d004c4000c1c07d1a280c00f01d038555910004100d060000e85880104000c005661401c21840710718941c600c20300c00c404e000403c000c1039a4482640015913015100209003406400c4580454204014050140b840801035010303190001400700b0b203d969400003d5020305501c41c0362800445030340b0101c406d0078a4100142500c140144041c071400406095540c1000f0000485080380c420040c400c12074204d861094404c031010231100c0e55200c84601c2900816688481040d043c0d0b038032900d0300c001c5c003500e4070140b50032100e0340400c094040d07221590a0101c51b84401e40034480320185140441c500c2d110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 238060890 1250 238059640 238059649
    0x121206081903030b0102030c031b031b0a120507050607081512010e01050601020f1515040203090c040c260a02130e07030605010c1a04150612050705090403021e010605 73
    0x4000c0e9110854650900c04010154980241550f44070240b0081d401c0000380070a46827280700701c003401c04007861101d010001d4040240140c0d1050b250900b00034990104840d58142c66105620b400c4607203044110f0750f81c031014022001e80b03201c10740200003000195141d0700203030b5014038040c08a101031900c40c8401e00c1d01da904c1455401c0804203040000c200201051802429a0406410039042d500710031404101c078500050824020403c4000c03c900540382c090382c50848105c000c602640041c0000108070020b040084c40c12400351080d40c1c10056a058100e00315051503000a0900c502c04000c5540c1d8545c516513051160403150039000185440072400403000c15140e55807010501301d0a00c420040c0c2950140704940c0102000e00b01059100003a40d00c40980d0700141410402d10903078440418140b1001040300e4152103049a001c0005a40b194080c0d552607030382c490200c90910880306d0200b00d508014a2080c02564950001c0c020205002440810000043c1c41d14882750358a400c00659070381e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 238062140 1250 238060890 238060903
    0x70801020a0203041e05031f0e010212091005040b010501050d0213031b0608090c10170a0209040b150405040c0c0c03030c1203051504020f0d110c07080a12120608 71
    0x4180c004503500d920f09203103c1d250061206244080b160028000c106d103071004261048d0244880e22038007000001801028001e10082c1000c103e15031003c1070860080c0c0306070384268059000101110b10913100d01c000041075a000311401460392812900402955004001a08180e00305c00c40c05810325a101c3c1600e0b10110b0a82d0056409403100141400c2d0302241804030400750066140c0140d4514240c2c0754a81c0d60078500440038052180d03444140d0425105100c0660400b0110499001c4e81c100480707820081d4208203015072189160600060103840d1081012461080441c04542480c0c50141048000c2c01c000c1816024003008030401c9000401c1840c04001840c441d8440703203460205810032120b00741301d144c10201494909000e1048198180329150f043c280304860269403140451300c906254084e10b0704c4600720b14202405021421032100c041c040001c01034046440507695000b40d580c1c5c0307403601e805c050300c41415850002c0266100b50384084040c006c548010920560380c14900d8607145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 238063390 1250 238062140 238062157
    0x1701090b040803071713030c0201050d0e070501180f031104110a080712050105220f060e1806010b1204020303131d0601020d0e061c110a0e04091a070207080102 70
    0x102c00003c02c58490b400c00d00c9180811000300c142021413810421501c2c4207904407101030305215080c408141168800e03411100b00d40743c00d541c14403020740241d4a5550781d0070750b8003440e408102c1d1a11081890100000114100d6443c81c0c144400070f07181d62200319210014a41c02d68200d0b0701c0d500c0b0f40004460600091a040301d00d690781600030b1030488001441040c2598a035181d03181000010000b540d2035000141e0f0028141006010004009500c00700400403000040a03003410400001074030707580c41e04032500c2489a200d0209036001c1152000e034442d202400f440324101000e000da65584c0300c0040900d40d00074400340880e03180180300b0090400c04039403540064030480c00740681c1d80e41e00ca0503c1d89640c12070741c280000c1910801e820000740050800307042039409118042024485441c10a000d604a020800002c21450b9901904180254400c210301004078004c1405192141050711030300d1801a0003003503119141c4001000014040740240101007140b2800f1400b0071000d0003840203000b00d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 238064640 1250 238063390 238063403
    0xc25020a03052a0f0108270106030c0504060e0117070503070b0d0e1f11040e071709070806062707050c0705040506030307060225050a0b09161701090b04 67
    0x14040448002c15045100a100b48050310b4581801c01c140c990007004a40f1311801d0800c160190b0396080c2c40b10300c0d641810203010507407120b0016a2549503065000c0070640e401000400c24540d1980b00340702c241e50151040c410491a0710004100d000a04e1091070080700b030050a40700d85c44d0741c0d00002072800c1c3c0c580e0451091a1400030742c80e440c282c001c2c07082500800c4200e01809007030f002c026603c1002034a04501040c81c41e243c82c181200440030200f180c000e03001d50070f2501ea160070207941c000c244101241c414170340d00d0780b080e01090107802c0c0051100100c5084d18018066a0341e901c09000700c10086488064030308d2070080c903c0f003003a1104000b81c0e1180d6031a981d01615054114001481e0100030f82c00310b80103a00d0301040c024651804821034a515421440c0035968a00704a100b49150300c071a10213a01110403007101c0800c02c000495000e04183c05485070003000d840d2455840d440d012108401c644815240c0c40802c48002032482100303109441400018040100f6260914206022181100e28 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 238065890 1250 238064640 238064653
    0x40203040b0406411e06130207061112090a050705060706020d1a0307090c0503010b03041a0a0f0c030621050705030307030c050d0e0112021c09030f0f05030c25020a0305 74
    0xc42044100b51075100c044103145c1503041075020b00c02d104030307071000d400c2500a0483d40035000002d54103404448440b80c4c410810050340100700003001c0580c01c2600c501815068410100d12000f4000075190501c58008019180040c0340c4410403000e0f0340003000031224540c00780714105110103148200805a09401c5002c00000420b80c101070504e40950004c02c2c0061401d034820b10755550100c2520b0555408804107640c031313280d03401d2509103442c807403401036030001003081040364400d055004404134104810302400001d182c0d500513070030b40c0d495005110b03d900040a416445110301c18082d03002c60f02610558140326100d0000c02c2c2181d114000c268045140c4003140310802030104102e450105003403402209210410b80001c04104114044203a03494012030704a1403460312040c4290403c524100030400c0d40d00c0341c0340107840000307501c860f4000b24252000980d00726000e1400c403441840110941440c0400300c00b100f07a0f42601d90501080c484040d00d800100680300c5104c090060342c0680c005050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 238067140 1250 238065890 238066001
    0x6140a091208070905010806030f030a17010b041802070c1502030406090f0501020a0f030201150e010e09060f13031119050d030606050a0804030e150306010e040203040b0406 76
    0x2044890780890080140840400140c42c0d44203004c1e02c01d440d42480c0241c01d5132a102c0c0080d14010750310704865014080020740d801025080b4030003803850003a070318031102c0c660b0365044940814022441440c00700103c0701800490410140d0080503001d00c00c400c00220a40c0f100b0f82e952044600060358400350384002014040540c20a5031440100100301100380d8450410000079100d05e0381c5c0340001c14100c1e944043d0020036000303420010040310b41c582c5007018241da850812048120a00c44c24003842c1b140d10208041c40000308059109d00b4058410581584a6041c0843c00ca11600000c3c3c0400480306030702110010103020780c3c40c00390941c0c11030300c0108840e0b0030700d00e0030700c14a031103028285490044100035003900803060b666407403483e0900c140144d4503810180c9183d00155503072035010407419008031030078801c10081c1d4040c0c01d0a1765000d071241c11070000e000482c401a2005001100e8040c00100016079640001341003404003551240b00081400c02c48055041c40d0340242da030180b91409011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 238068390 1250 238067140 238067153
    0x30c2a1f0204051528020a031709060708060301090f0807230d0f03060b0c01090b0105010905060d0b03030417100513080307030510080304060c0506010522050406140a09 74
    0x110018034aa2085150500e03001c00500c0c240001000303042d0011021075921400c124141800700c44034241c00800c080c1c007201c400020f407101c0c51002c0440c0030558031000040d6840064a60510504908000344480c0d2942c800c00d403200310700202802c0e819902c418444d400a006030080140c840d03c80c0c0c1200b600c8460918203843c0c40ea0b9056016091640c02e259200710700c03040002c8210307848283d401c00e4840c007041b5060841c090312090700070340368a00c0c0005490804000540c009280d060142c0a05100369803a000111003103c5544281540981d0074441d50740c068205230300c0915a00002011a0b1409584d0000310b40040403103058121241c0006c400925412451300410344e00940c14001c0e015030b80b03440ea036402c40c24000600190708250341c503800900804c4140e04c05c2409030500c00122901d45030b4a0000500955142804403064042c050002415040080d08500030071015170303020503001c6c0c03400c407108000e0000601c1510746070b440cae03c000340d49145503e800b82c0c0695500c142c040340c1c402079401c215 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 238069640 1250 238068390 238068433
    0x50d1e090f02150a08070e040f0608030903010c09050a090b241207020a15050601030603020a090614060f0f0705030409020409020405030607021c0e0f04020406051e0906030c2a 77
    0x1500f00e02d00400402c01c085a000290300d074000710303d040480c030320728819004c1b0340280140c18403104580d01c0c200000c81c107101d000000d042c0c4014100c0007804050910b000894400c401c82c45070381c1d00144a21810f01c002c1400360000d403048000540310082c4000e0390b40010016840d1048032444803040019807910314101c550000764000c40c00d000070b008071100c0366210b0080d0100020145280d076568004074560b40c0c03080d08014015a0003c01d00440d0544035910440280b40c02d104e5080700d00004814804103050480c19518982041040a81001802c0c5040302d026804484111100d00081001091000c56880644003503c404c01b00143c441c1d003018245071038807101403c50415944000d5100032429070040781c0580c11200c500c3e1150001740e04038042455403104007011640b00f800440c2c04034003194000c000d01102c2d240c00080c021014554030521555110301d10312142c111500b0030001c0c2059102000070402031410090022461400031210707100200d16a00b21440b98000304401c546c52080500304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 238070890 1250 238069640 238069669
    0x603060b03040b04050307210215090c090408131401030e010b0d151103040f0203010506060408060106030513080c060615040b091522050a15050d1e090f02 68
    0x410029040c0031850140d40002000107044142100c0010b003000310600030b42da0140e40c04080b0003849254400800e28400d2101c00072030042c403803c1074007000381031411103160207041e1000180124070469010f01c460074400130420780304558100400801800f015072000b00600281c490808c0404a5a0005003500d403080c0c040805a03041100c3c01c206503480200074140c16038020154143e00c151881f041c1c01070020011844120f10011040100b03102591400700403980c4210000c1103030795229801c029060099002d41c8800390322020051050368000e038411b9401c04045c814803041c4021907600c0d5401d69000d1003003c1a2600143c2c1440054144211008014008803220302e0405050840c0c00500f4001c941030b031849040c45010341c1c0901c6881500b01d5015078607010788020ba0510903003040000002c18407400c0e0080b0060b5000003224580c2c000642e50901c1e240d5115854440c004100030080e04071602d040c5030300741948c100c0d500741808500c04c040c00307144540300c00324075540c0724010003083c0d4988084 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 238072140 1250 238070890 238070897
    0x10912080406361e08040302030f07081c03151d0601090b1c020403021c0b090c100f120e15010f03030e0112020c1605041a150d0906020a0f0906 63
    0x34a4202603542c810140745031003034152102202e9080c0d081c4801300020030030381c90f01182d14403c42241032000c200020070589000340c088401841000c070141b42d48024500c54404a83c1068030300b1100c6111442145c01c521a4501e40420460764000440a01444c03903484840342c03192508004038501c418145c2c89500c0f0009003080b2050500e4098400d46c01d2050b4a1070311aa0030000340b220314103610b01d90641c0e020f15000b401c0d540d600e0460103819410102901c0090311401903d070002641c0420009a81b840741d240549004140b0696110968040d00300080c07032418400322000e50024420b81c2e12540f00d822024000614010521105d540e80140b010b03048203010b14903401082c0046a0840043c2100490030b180c0003603013070a80c0b4150782c0240580001813015000790703100c495008108a81c11000c1c1c1d20101c2e000c1000c030054100c1071658a0114006a03002000401d001d29260500c00261044c01201140400c1d030a440da6110710072030b8808003212001c5180c0d015121003850740403040b00040c3c0050308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 238073390 1250 238072140 238072181
    0x10e04090b01090905031b0f0f030f0409020904020d090803011401020c06030117070f03120f0305130b070c0506130c06050a0203091309120207052704020603040302010912080406 78
    0x2215242110030500a4445003901e48013184100801003045030484000303440b80e0310142c1c001c3d20f8025180c1a9902080307229110711219205821004811180e44040880e500c908c1c0514000b03040000c4e40000e15982d900c60340c21701280d0901c41641c02921140c62094015607680d605045121001c500d401401e01c1c11907200d09410302c01ca850740011681500c000c0c41b8038190030401c00d00d403145494519002040d4406503c1c00000030810302e0030203503040840c40c3c0c440381051070b01d11008408130740c003c40702d03401503101c1030f80d1650115909001458101c0c455140500e00803d03c1c0e1500b503c2d2000035640031890340850142001070190666480006d80390b5032078800c4c80e0807038601c4c0c001d60301d02540ca41d1504c0380d860200e900306440040e43c080030080b5407100071041d80500a21000e500c0b06048c0c4600c80c06200c404110103100c030120507000c1d20070707980c800804006444640a01c00d25401c0180100c05540d600c01060f00841c1c00400e103080a0381e0b0310b0740c2d5038210f440c09103446002c2c1c1c0c500c1c1202c80e00340b0f14001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 238074640 1250 238073390 238073393
    0xa0803070b04020d170703020f010c0e011d0402161506050d0803070311040f030312060512030f130b070b1837120302070c0b0708030402090405030423010e0409 70
    0x64407a038009404440150307804480c0d0400c010055100d280b000d80b8654002103200c200340d000b203440600340c080c542c02044144004981507a03100414043c40d40003070310405004051034001e4048003400e0002510050a0058044c0c802804580b00d800030b90b4180643c402c221700030510380c011440640300564401c5405c031a5644c4140c81ca00000c0d2080040c541c41d00081c0c100c4207844406e44000f00034480d000b100c0c26035241030240040c107000c41281c402c1d50620801013541d00300701d124034034a80710483c000c2d0310701041c2c021100c020340c001c00b81502001500500001d41062890003804200380500c10a0b011401d10078105a040f00c0c1c42c0d000d07181d050f088120795882c0c50070024404e00400b0004280328041191040d03002c130000c012040024030003010318a0f6071503507542c1940500b410511a4446e2807055441d515040003602645d50002e2180e41c2c1003000030014108403d103650018458000c681c02c2980341c02085400b607824540700d0020503000b4000c00c0041da07120100100002c02a1010001d40015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 238075890 1250 238074640 238074653
    0x3080a021309020f1309090b270a060207061a0310020d0b030f2a131a1f1107140402070311030c1011030f0c13051206040302161809060603080304030c020a080307 71
    0x500f189c022140e4540c2c24030743c01c03030046545200d060102042d901040d0381860b11070000c1d003018000f916043c0c50f01c100081607903400981180c03102c80084c020168a1823920340040a540140e02c0d101c0041d03100e090804407500c042215a0321105000c02800825840c010050080c0600750601e10304100c0c4040501503e441d01048c41d214224202c1012030081c8400c4440c01d404c222275040660800c0c0031515022031000c40b0040c814070980259903807008500e041c40c2d201e035208507a0141d40305291003140320403814031702036008007a013034864288141982e040741e10003030540c0c1010317201c0f10150f0000c12278001c2c02c5599100d00450f01c5910750400d03083d0f050418036600503800c02000d5009640300020203c4040e07501c1f0802000034800101668100307980c2854441c1c9460342510218050303c541e56150303072016508500c1400f5201000442c4034110040302200c0b01501c20301e0016600195920305c0880860b00302c100444c8628041d4503804c46550035481840b0101c54958401c1c10260003d00060001560 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 238077140 1250 238075890 238075913
    0x13020c0a02130c111906020f090d060614030d1b020307180f0c031a090c0d0204030f02091005180a02120703051f05030304032003010203070c110108010303080a021309020f130909 78
    0x401140050303c401c0448e00c045020b20409403416804204500720004201032908080d090740c40f8440c10408520a903001d0544d100701310300e80708002c038010800d000030003100f017851842164002000c0301c5806580d410041a003407080780500709100c0c0c0718115684940554040c1b0010b000c400d14041108031600d031a0030140003140e0040f10b104000e101d0100d1342030001181a18080b40720b40108541c0c1d00d5880c505082020b000540c104e0042410000003000c0b02890748100040711006080c20b03041c0c0ca0700d003110403071007039005040c00c01c129801c1c481d0481d08015000310754400e030110b0301c00045504150708400c10101c10480d01c014840102c9000388540c0c1c4021043d903040360342c040388280041350901c050647c030600540d0600d030190310200802c124a64444400c884482c02402d2502604403014011aa04182404060b010035020008101260155030007040d802491a50900301306840311003a40030703680422a6100c8540700412000d01010129580c0c400410007402c0c00c0180c00348640e1220200030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 238078390 1250 238077140 238077143
    0x509010321020109080a0f0206060402070206031305121305030609070803040b1b0d030b1503090a0b0402060c0a112b03050703090803210c0913020c0a02130c1119 71
    0x45481e2900c0715038003d400040303800e0751180b441038403502e55000007070015800c884504014803c00c40460882d040c648211200307076030003418403851650344a08040501da0401030440d040d128a141850031070074818094051620226008203ca601c0c15040514140300070788410300c9900400f0003040003e000204480440f50034a8500d5120740500c1d81c0d00e80c40c41414220114607000e501901080f1f142c0c940c0c803032030420104443d07140e41d0640700300c1c00000030702007228140510341c8109043d40c0070030b00c1c4050071130348148002c000c1072030715100c40b15450810a0707a1078200c0343e1072303074951002e00545000d040142004840910070043c6002c0801c0c040368541c04e0381d001a00340100010f9030000c0c10322503a180790151004a00b12036039810300301c5200700f458030000f080407000007100001c18001d070f2281707045640f000710083c200c801c0e044007803415600035840001d4401030b5101e4000081c00688413004a5021715400c0c2d0303000528a4030382c0320050005ca5000704481400d410552950710803030b40c01d0103030302801ca = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 238079640 1250 238078390 238078433
    0x10b030709031101020a021207080f0706050405010818101b020f070e0c1b06040c0e06010e01120b030d05031603050105010c0b041506080d0908060606070611071205040f05090103 78
    0x164400f00c010707424481050006900101b0a0380c4076080a00c00082960488044e001207851020840c001c0c47d031214814021500041c0302007000708210740c4200102a04075403004510048580030404051801c3d0407046446c9015441d45641408029440c8040002e010703140003070940c001040002944130700e402e014041942011001007a4583d034030400390740b400c0d0711440c4207410b644150754040e99180c00446040350312030030508010070100c9444124a0099034180c4400741c43c104284015201c04412400d003010040d80c42c45e1450170b6a4007000740c01c0d8103480d02c0d1100b950740d042103032040701d1006001080c5001c1c181400010482e50341d00603a1613161940000fa90702990b02ca0786024803d031030380300310354102813401d19001058140d40490340007441c6900380c4940304069a0781c001c80e5243c14040750301ca54405c40c1030101a0206540c0c3e004a0b214041503a986460302200703075142945500c494125400054011406010400c441015080504021603c4002541c5140e44603010322100b60103000b01c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 238080890 1250 238079640 238079663
    0x6060e032b030f110a210c080a18120c03030630030903020a0605030a23131505011e060903051c0c0c030302060910050405030f0901210501050405010b03070903 70
    0x141c68460340070140c0a10416440c982d01d1286001c010320b10300d04172842509417080e517422200c01b10001e110f908142c2545450351905591040321000c020050482d00d800360b40a100c022100117500c0b48510505001d140e1685d83e441d41d01030800504850301c9421806030300c003030640034120a643d45c4240050700c901102894110540a2070105c07035500c1c013a0300007900a18140c101250f002d401101071072040660000402114080011405d054140507100c3c4014608000100704001040540044124000c0c220481c0403030a1400c1001199000d07401601501b8540250014040b00392281600a04d2075180010a0600b19103a468482528001c20903000c128079180aa2031805010603c0e007407030700500c40d280d9165890502075241d1781c04441d09180390160b00c1c03845100c4442442614011a013040055080c80140c41d900c5c40396078000c0c1c07100c034140600c2c41c404080d078540c020303c03244000030681c80c041400e526040511007980c4c81230304100060305c024420031064a40c4a001501260b0300109016407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 238082140 1250 238080890 238080911
    0x30f0d0c0504030501050f0106110309010e10110f06010503121206010c060603080a030e0d02010e070b130806180c0d2f0d1a0603030306010f030e03090406060e032b03 73
    0x441c0d21540d4030060503542090304110781c09042c0b07440107048400680b42d01a41607184424183c40384030b030f603040c40e01240c04071540b8061410414510314007c88942042202001d10403a01882c04a0104040340d00f50301490050005040c00d014240900307000340c950a0514104626221011000030000b5040003061544c260911040f03801080003190090412561680e40c04001009002442c11000c51845440300f100019441441540b000d1502075024003103180c28104441020f07486401107501402c0b400902103403140f010301c545400785241c0c5801d5034015481d09000b9090600854950b0710a80203800c044000c5580f8680903440f02c94a603008540001128004900f40c1640040403904400c50310900300400c031800014500010a0160700909580e408040543c0d0707100840d502ca00080c55400d042808038001d8000e0214901e06506072410800c0c1d520100e002c695a990206c00001c0c40c05050385d003e4141402419807100500f0011003c403002e0152602e0342104034001d580805603545003a01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 238083390 1250 238082140 238082147
    0x2615070210090302060a1b021018050f100e0d08011502071a0705060609130803041707080d0b04110f0c210a0207090221040f0b1f050102030f0d0c 64
    0x92030a0801d0340100604840d905009640320002c42e846501940b4007084003200344d03916804010000c40c00c1d40102440c09900c40d040707004d8042107074100582d03800003050070000350042c000020f042604038001d000301a0ba804150b419612131030b0510826070401481002c80541c4140014152070200034203254014a1400032032030200d03607502c41140c4c2000d084c5c04d2100c40c2b01650040020340e003e2400c542050315031a00300582c0f49400d81d102d09140c8251a02c3c600020750700400b540e8020300485c10340305202c009580c200c4807a4880320b021900e060b000110038840c1e079414461007100003c15101008440301442151400741b05800f02410502e47c0480c0440035400c0c104a80c0041c41082002000d02d006a00c000d01c2c12074001c0345003400075005210000c01d12100d24825200d4030800c00d0003070b100d440e036460003c8000300405001a11081b8040c0d03070040110b400035050303a005061171506129500c3c642e00c00708124200c00c0e0803050454004010030001c2c451401d00b682c10500309100300045c0a44450001d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 238084640 1250 238083390 238083403
    0x2100e0a03020120010f06050f090f040204110c07080a06050a090b01090e0f010f15052d0a15020d0f0906080c091c03120b062703010f0609050126150702 67
    0x1404c07035801c065881c010310603035402540840d6410355440d09080f40c411b0800400c21710407a80798001c0d10804000401501d03107034220700410f070010355425242000c01003080e424000c1d103421082c0c41e50b00c031039000f88c1001388500c50b8682c0400c21040405c824221591012002d041c1032045410040d05c03101e2101d284001170242181e0b13440c005008100030180c401000c406483c01c541c0c030203101d58000900140e18204074036600e0f640c4848070a0b0304080c40c0e501c010030000720b0200300310700d0304415411004240104900032029030041d05400030261280b102500a0840803d06181400c01074606006c115468025030070b44d13082808010000e4840c810170740407481307040d94054502c04458030300d8903001c2495088004851866030690b024810142050140310403480707906084054014096425641900c0402c002c9174107040041c00070801c00e074a408074200b90f41403034001c020420307500d00040009031070040c0324a0810013083e800e103e99040c0c1c6440c4640f948aa110b07038507903082400d00040c21032031080c4440c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 238085890 1250 238084640 238084697
    0x80304020f0a050414040620070f080d051f2c060f1c061104051005030603011e020a02070e06061603020c1905100c052503050106090902100e0a030201 66
    0x704030003c85e040e04191003840c20707601a1420303417512800a84d250074070b0034184000c21941c000103281800c19540e007070024007141d405a0344540c007840300080744003107402094000c260780c1140c110000343c203030204800580598032a02035050309031191180894584ca0181ca40300d91050384180f01d07507030303440403520707030004540130992000403441282c2a410540885404041c001c14080000444003a804810b42c07090f0f00800d503000aa06200001042c032580065901c6600038001003261000254000d10302004000e1515000b0780129800310081e50402c4150020700502c0040b52003402c003130005c54102c1c4131b291501031891802d1200b200503d4020080d64a56442c003070048000c80c126005064458225405554418948640b940c04601d00c103500b5103a481c2d40000140c401c140300500599a05411104801180d2015201c00004204280b18420081003003d2002c600d0b020144104043c800103610b281701401000c080c0007070140c8031a914002903d5080c20038072411a40b908003040080e0b00442c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 238087140 1250 238085890 238085899
    0x803040306050414071d0712051008011808030c1b0d08011a0a1d0109030204060311041518090f0813060207080a260c030301060c020108010b07080304020f0a05 70
    0x6001003007090541c0101e11950045860540314207115420980741c010a10070508900444621529951b00040110303403c0001400d107000440c8810700300c034080d2002100c0b5a0150011081c0c10400c4584c280101d024030305041194000206141e600e00100d4013018200103042d100c0440c1c11010b01c25410342c06c0000e146140111035a035802c2d20401030002800b40603100300399007600c40541d640b16403002690303e4030169490341c0a42e44d140c445042102036044038030f07a0401c101280c00202503280c1e0b1060001941c024207017100341101220a0009803049015103a445514191040090800b03654942007141c2c1200404501c041041c202403036807803070404000c0c01603070002910640c0381c0c0607010a4400c480050f004d40d00410341c3c61680e02d4440000c101c0203000d1500c2020511001c03103a626000c807a0142e903070300460500f640f0340c1c1c8031072840d0000d030803403000706001c4021b19043d0768000c401c01e40108040800d4918106495070f500c4003500001e00001e00440c94400b0001444c2c1c0d6204c1d068014200161 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 238088390 1250 238087140 238087147
    0x309060316181202041d03070b0702071a040e010e0105150c120d0b040e010218010c051204080721030e040b0d020909011d01060326040b0301180b0d0c0b0d02040803 72
    0x2601c0c44503543d2041248101d10344003a9200039112480c20000a0b40020082e505110713031500e8003081d0b1400208583c0450241d22404038004c400c0a51070030160601340704246d190350505201e08400c01040c4c00203442d403c0340c08010001560b800503c40e01c058120310351141c86128901c409450700c0782c2d4150000c90b00c80302198078072184025500000c9081e02c2107609012104004005900b00d12500d80c00d451000c6e074911800119500407801a16524032840c02c441000030b00c040e20844d190080e40081000d9001840304004050000320080c6004030160f407400c00380b107015a8050031610b00d4218950250745c441142d046d18be5140046250280d4001d03042c0480c52610558050003080840002040404140c441c5520f05405102c2c40d401c1d0b80e4041000b6001c280c03000f038448596508881c101a90910401002c038060b80c86001031802803000d02c0c800e8207441d4451400200faa00c450410f2405080c1120890002c58803c4040300100c8007040e6030180d2701c8560380c0070180a84683d4000500512001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 238089640 1250 238088390 238088399
    0x50301050c090102060708010303080a0b01020a02060c010c090611100b01050903010c02011b05070206030402011b060f060e070c0b01051e030102161b06020d0807050702030604030c0212030906031618 87
    0x104000c003a480c0b4243d083d01c00650720708000383d510110a00001d40050116000508641d801c1c0d44021310f01c1405004a45295402c0c1e4002422644118001109070751214181443c2d282c00441c01d6001d4016410304074403062903140069500d40303041207800300440d200e54512044da4000d0040321280400607000b400800082680030b4040e0a03205007201816202c010212000f43c4503500307071000564001c3c1503a1a68950307030011034485c82114072030210709406425410000351103201d01d47c00400c1c1d4140105200d8038101d89440d0341c280040200742400341d4114810006204290300c1c50641b070085841b40440c881c4188948031107082d41035069015880061860403002c00541e1401c099031240c02c00c10880811950301d0503001030f491140101680c040c65181500c5805030081581c416800c0ca052800c00d545600000c0c540041510b06401090803001418154208020290500c0308420021441e015020780401c1c854480280400c03074441e800344c1c1050142e48507034107460416403100c2140041c507444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 238090890 1250 238089640 238089661
    0x50304020a05101e090b09060d060b04080f0c010f0215090304080102040e0a0606050c0a03031109090106050a030f0b1507050a0b160905040501050904020d02180a020c0c04090b070f0905030105 84
    0x3040c2c13400040040008042400d1280d48100300b42e440640c051b0b0f040c1840d000c00e00002d41c2241c2c040501c10b9448440c0414100d03401d2014100400100d0300038000031824401c41410140041780e15070402c1041d2140d041c01c2600007401a080300000700d859029540d5400c0c2c40c1e411400380d80c200c81690f5000181c00240e02c5c2070f0303500d0039000d14a8898200405940c400781580d651217005c1c611080e0340c00030410b4801281c020b40c061684030702d008000c1850107400900040020304c003600220b01003200800d0071010190f251164065492071a03000304280d440000c00510f200250160b650028a40010b0385001c0100c1409005141eaa00c0300007480ca0b410040074043c03941411582c1140010b06086002030390f8900740c012241215000340c0b40c030b941d03501c842d024458400c088400981c0c020f9040300020741070400c2c1060182c4124140d060050715500503108280c01e200d20300078101c0c403170303428100503101048400d41d0158000b08141402070301c11801e28800d407146a00c0c0d40c422903141d4640810070101144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 238092140 1250 238090890 238090907
    0x3130503011d0604080f0f0a050a170c180f040504050f0f03071101080702010902180615030103080417070909030f03050c0325020705130b04110a02030a050304020a0510 74
    0x2045000307200c1c241c80598081ca048801d51000c0b1515400714000c500416041802803990001c09030401d860000854030420069001a01620000303400143c1c810131140c0c0a0b45c074543d08100b030000202c560a1840140309140149001030070102105608000079a03140b1807031102e00751001d0000d0201d4506420310507100d50a40010714494091020044442030001c0300f19201d6952004500300c0e0045000b0045444180092402c01550b6a401032100903a403038000030741a45407030784100807440c500714081c40090750b0746000001220606000600000d0b48040a0310160303081d020840d108003083e05092032826200364008140c040ca000398400525034001100d00c600865a10306104507240c1c000e1150240c8800c90340e0204928004101c0107004506036805060b4803500d10485040c1a101d000081c4018005d5060041603a91403429072010b08150203036846035818517a100d0300344038107044040e48911a5081040401400000040440d950200d1042c0504400341510140c0e4100d0400a0007111 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 238093390 1250 238092140 238092149
    0x105100e060402070b04120318050601060815120609010c0c0317041b0902030411010e0102061801021c091101180e0a1803080402010e0901210515100314061311040e0313 74
    0x382480460303945550410318080b1112b50101c003c000390b038602031080b03510007405040903502441324200070303180c2d0762025581d403180d89024019140600700a4000d5003101c1415040f60b0511010945030404a1340003140d008508044a0301910b60343d446180c08010b10002d201107a50400f801c90001c07603424200d0380a14400e43c0701c0c0101111101220300195070f0f000642c2034150043c0c1c0034500003103070340b8a141c2542031400d006030005414501c40740c1405080314140540c1102090b541c5024405108159030601a07a07802030030701600c0070300d03c800e61202c0380c0204d00401500003100380c0850900349040d4400400542c8146070301031503101915008054171410380f800d81c00102d10310040d4250b0b103084070ba080e041b00d13050030249070001a08000329542c14034100b070a80b420b0148071040c3c5601d5020380d0030240b141c0085c9800418450035031601c0e80060a05d403030525410b0b03004504110b175812002210241ca1f40c1c009003034070f14841c01480040d024100300c2c9002d0f451408046000c0d03c13820301612410040e503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 238094640 1250 238093390 238093397
    0x150a0503191b020d090b0708071b140f0a14060a0507080403030801050108060a06020601140102030c070f051302161104021309022106061206010c0f0503120106020105100e060402070b0412 82
    0x341d800c0b00045584081d50f0082d841c6c00c020130820800040c44000080880500c106446862002d113160140e9134030b07040741c0c804c003180c545a1802c2e01e1140341410840b04984012075600307111505008120004a80c8010305038044d620001e045001140124182c42081d0340c050724583d600c0da22458020700d004002c0c4205408101840301050080c030b001220b040584100d40d00a05180e80f800320441030001d20001442d05602040000601c02c55040c08910b001d041040e0080020918003c140890481450040b0449520601c0007203500d00c1440300c0301d0120703600044030030105c64060b40010000c0c822200c0c0000c686011a800013443c10054000c1e005030481c0179409400c44440b000c040c400e0104c116141540000300f00a040f00740c0c4505055150403640c10b141c101c000040e15a152024804078007800e441a40c00480e5a80742d00c610b440e01c2e603015011610084c03015040074004940941000d010343c1d11a43c0080c00001d0f1151076030350640720015007004001c9841d0525081c009590040c110200001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 238095890 1250 238094640 238094653
    0x312030614030120030604020c2a010503070c03050d02190806040f02130915150305040c12120c030311041206060504110d05070c02060a0509010e150a0503191b02 71
    0x31440c0610611242c13050306404a422000030b02a1914503030300060296510a40c00d110405059200700b2044294203c0c2000d0ba0180c0c018020310450014201c1101c1410802c0c10010030501c82e900800c6078802c00e5243c1480e0780c5642c41c0421941c0030703016569401c0c0007400c0012100e14060390000300700e400780704243c40401c405000e41741c054060788100820000c82d07250801080000340d83c603070b202c01601071030103600031072442d00c07040401c000086604a03040000d440718140001d008580086000500806c00794010814150362400c40c1413201020b01024007010700e0f4000107050094200c9905c40d00c4030000c46a58540b0b07031f05050103181c02d180d02a606113181820105490829102c1c3c5120540c01e01302181c10564065041c07406440020724038020440305495000050b26100040c000081c450f85545844211103800144001c119042c5240701c2c3c444403100d00c2030390b8411011210710400da481c1941d5039546081d03540007000c3c40741580d18407051401200200340c209410710b4840c50b40c00707507007030380c15 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 238097140 1250 238095890 238095929
    0x812060409350406050414040e01020a05030403090b0304031719110d140c27130f05090705130e0a05030301260105061309230607030c080903070f02010903120306 71
    0x2428043d0707026600100d1010402400401d04154003502c0843c0010800302d1000c071003814450998004034484400b00f00d021050004250b04401000040c225071032910741140b41a8400406070b0084016a89480347c10102003004020840c11001007003003101c0f03080c8540000c45181c0e188940c00714000420340c4d45000308a8044045101c880350040040d1011141007400d0000e410f0811264000749483c1c4046a0b01e110343d090711081d00c0100240071810001901496010380314054070340040401a44d0740011109124580d205040d144644200003000204852000460752070901102800b814501c4003100004070288813070000a03500390110b0101035003c0788009511300f603c20980384142c0c01440003800380c12448050740440100d90082070a0848075141038000a003a408440d46100d080d04a881082132aa40600a10202c802d01d40b404000900c2c00384c06407503c1e4080c1020040c01501001080025a031080c030041d00039507000781ca0740361990032221000d4010f001c0c901c17035992400b0b2b00f2440030341c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 238098390 1250 238097140 238097243
    0xd0e030708070e0601090801050c04032009040605130b040b04020109080a031e1710051c17070204060308120a140402030d080a060f0807210812060409 66
    0x1422190744900902c6141d050a6001010500060403541000034280c8000760b4031500740101c80c0200078000c203050b5610b0540c101803003034200a003944182d00000988000d901d403501840744e07a110750040d40c001004d44620304211300e02001140080d00b0f02c4000b000340014025030183d40307400303103100745c0b180b05505039070b800c24603201d00c40381e64041c0103d070402c41c4001440c614901d40781600001480d0000c3e01484108024a66080940d0500141040054180000c2c141054045564600c1c140c0403540540c0c165500c02c1050444031456519680c003082103011510390340c01c0100039660102ca0310b600c0d8000b6000d405100358044039500340c07a50078640d200002400e4291503601841e000b03400740c84203d4060030140c60102c0080d105d4810305070354580000b120075055040b0800780521a0260044a181034920780142d4140c0321031440048803110b82100103403500040b59521480c5010b407206135618900003c006112020f4040c02c82036600c01e0b00d980b00c0300490400180c910194072004000c803400036204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 238099640 1250 238098390 238098403
    0x614010f050d0809040219020c01030c0509060d020f070519060c05120708060f03070603020703090b0313020d03090b030c0909180705121e07051507081602060d0c020d0e03 75
    0x1904515525480e00210718a0b03401010102c0004d1710140c039000296103128209024035510000680200342094880d41e851700510459003810301c1c00b02c0c03c080b03010001030344a01c51014405421980002c00341d0651140c03d0640b498141c104003500c03200d008164a019042c1c1d4061400c443c240c2ca841400902980900c043d83c000d528114903a104503520010103607102c42019101c664800c50041c0742d103a03542d03403c211101c05040140d401580742e1a840c540039220b41f155401c060610031040c81080b00c020b01c100070444490b070b01280d005184010324142074400e0310858005e1201030f500001003000c1c244901c5c0040c41c060760f080e0b41e140c80c1036491000414581050050449585d0480078040080780f0707100c0801e440b100c1d400d0081e0765805005038400040b00030b0303400003100e00b83c12070103041020b40703802c1e22040c070070705800d000310b03803030000e41f503031511018410072408070a241070b551800425503e41c2030136500346c8515203070308010a105070300e40070755968101a40710700000d0780350501d01040c0c140400c09 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 238100890 1250 238099640 238099649
    0x60f1e0602010e0601060806031608010c1206080a0b190e01020a0905042003310606050306010b0f0d09051911041404020409110603160806060304110112020c0a0614010f 74
    0x5001e240c3d00b05030085487e240e010b0903056142c80366031901c01e00150305c3c481c20302c005c003509800018080c002b0200580415030046e2100561803074040304105a01c03001c02d0141856a01000035843da03656031080e0980c0d44141840e003900c1b5031600f4aa20580001503004014403d8180c540108284c0e8400030131059030700340761503807080d00c40038034a40a0200582000e980c12031404007040704002e4000030744000c00c5081d020481045252004503509101030fa101f6078000d80001e4000e003401d036040c00b0304100584282c0c401ca6082080010307201880d42e0300e42c4e01221906900c4001e403019002c006207180000745400c5410b6950142e00c0e03040b60100d150030310030306511061000010000d507030780790200401416520019034003102085128072070780e40d0302d400940c0705500840004903100c0c06903030018003785009110303602401080041c4800300d804545954a5041c0918210224045100c0c0301d10190150305000302051040b0200c1c0d004004a90700250ac82c00f205000c100f0480c1c0c1d03100011070940c4c803184035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 238102140 1250 238100890 238100893
    0x405010c1101090b070308061207080616170a020d05060306091b0a05040e0607020106090b0906040c022b0e0d0210080c0702091503010b1801050d0303060f1e0602010e 73
    0x24503034001040201c0700d11020005040400d00c99a4072540140658051002280050113180401915140c0028030b01e10102ca1200205040c60134006002d543e108080c00210014800744d004100440c461618400c0780d13410302c41c80f00102c1c00c04142041c0650001c1c0c001000d25400c00002510b00d003030008820348140000d4000740040c0b1580c134040183c1003902841950044800c0d0404680350721180106049400c0e042e009021602d400c200007402c4403040d07048041c02c0c506000c1150301c140e482c1c40ac2c042d00310800316030002d952442c1707130010303403400000c500008090220500c6040c100180340b4800030308041c0c0c075242d01080c04016410405954a81c0e00e0096000c07012105041510784104c1c1507650010307031a04004c1c80e280642d0009108090120740b00140c1941c0e21040d5a154103081c014004811801c2e03620610950502c0b03802c560110050041c240140130404414045c5482508400010007105e01d041001c0c036225032005452064001580c01c009542030000650103105104072076008201c0e90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 238103390 1250 238102140 238102157
    0x1002030901030c1b0c0609060221390d05030910051b0c0604120c0b010302060306010302220303020c010f090e150316050901080a02010e0d1a0403050901090902040501 73
    0x400540040c10a0324909003000303030b131100c541014150070841c450b00d140254000070510303181c054000c10540c0550080b03011034005101c4ea501840c55052130040340002114110b480c0c129686450f00f44050320f13604a0550b0900c0c0684801e094031aa2441081035980d400341c03815141c005006483c1d40c801680c1440c441c1e0302001d040070030792082d54090768208050b903001c4030b450191003c4404960300a2010300115812010521042100310f0310281d00040c82401d04500c02c18403030302c0380c0580d00c00512029010f90700000c00260168407990480d0001e2007030600c500c1c02c6402030b0b404a40030640c02d000480252080c1c1d0b0442c500384d0301900e14199959003559400090608011503002061000341008000100034041408180d4051007103a500388581a4aa02c0d09498041040300d10141030703102842d1034200c00000c6015036032102906400d0f100c02d5810125511715898a20400403005a601d40c110940d4810b20040583c450700070005990240d0701e600c2d0391900e41094004a00c2244140b5000c1500e42c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 238104640 1250 238103390 238103407
    0x209010b1204120c0c0f15081302011101111b010e0c091b090405070203031609051003050c04050402030f012c06011b06020d0b040f0c050406050c0c130f0b100203 71
    0xc41c401e0741d5100d510314141c00c070742d09a56031344e08401543da04290090004074a06005800c0b6103a1420647c0314207240841c01c90501003107104200105041c00303810014051181e000c80d11b025040f20f101c11030070303110180d6100380460f040000052204a174140c0340d424400706c5015410000f4115514030320080c58a08151140840000d842c8100d44013004084004e1108401e40d540301c1c4a0301d80f090507030b0303000345603070b80303458005100303203120743c14a02d0280810f0041c144410307280e0443c007003030041d000c3c10000380c1e607100c0d40300c045614003a540c8095889400001040790070449982c51604076442c81e100c003140000d100700c421200308082d1b4070605400c803044001078480e40c0b1444641c521b10000100e03c1021072061340f01c0700203a80c0a88010703800d894490454400c6410248a03903401a10041c008102000b03c544008006e4810ba22400c0304200e0041170038103504c1404c0c407201d2940e040090800c91403000f26804000640802c1180220307030b80ca02144861241420001c25911807290350103581b80903040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 238105890 1250 238104640 238104653
    0x601060905060a030b130504020906150307030c031b03090c061b0204180609140f0f15100e01081608010b0d080a02010608070b0909011e0303030f02090316030209010b1204 75
    0xa044001c013056240d40710a0342c0d50f203c520300c04402050704c980c0400c036464640181b00343ca10018200500070340030520b1542200354080305680d0464801e190202d11072803e100211f01601e4480d0800690f400c100f038404010300e03010340c00a03158911504880d06c00c580d0300c5a0503141e0500703020984003a141013010100051170503500c04059082e07005586c40310341019881d29000c541c450181101c0c0402103903070034040003030104440c0e4440d02c4480003e10000c20303a14819621103420030000082000e800e0003041540c3c8949a01c01d02400d03107020301d8800b42d03035a02d40c0036546510700e1580d480301186500d0003160790130701806409980d0001a0034001000802d541c5c10820f13501900f84101103550b980004260410180700c040c0c010a00351400c40e46401640c0100404000b06a000d006110103034051040301000080b80e11003125050b0400158400c03103204e00700301070710412009541c1030141c0050305040440f24003020090301d00903910545142c0e00d4022400640c480d28058425070407110000070002000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 238107140 1250 238105890 238105897
    0x20f070b0a091701050114042a020f0604051b0604030b060906011817010b190b070507030c061107080f0c0613030b0c0703030c020105060a0603021803060c070b0603060106090506 78
    0x26842c1c0b81141503034520194145040000001105035110401041148a8a2500440a601100c041043c2d1744101141448034194a03003c0c0504d541c1d500040c035129000b4441c2000480301d40342610107034038140c502551034150306c00036456148008034a54005040030401d8805581d84201d181b0180d448103410010f00850042c80355040140140e4004450201c0da502c100050035040e5103298884014120682510802c180d91400b81d2030040645809442c0d080003c0304032078602c0c031620341d00d00490034020f0800460b900040c0030281012000500b0503445407103c58555811415103110390f49565805440d80c500c4980444254040392504813145000401001508001a038a06110341e030390b81e81002c2c4200403101561031881c0803030181e09054260141031000a210302c0208000e00c3c0000c0010520f103220301031001003660206a0070903c0c054a003590200600040894203546020002d0b20390642c4152411900140b407040814034030700340010224141c56036610303115001410030003404401e81 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 238108390 1250 238107140 238107157
    0x210712020309160603021c020909010302011b08030115080f04030807050a03320a021318020c010504151a06090111191a070e0108060618090f01090c020f070b 69
    0xd2080c3c10a400d030307051408400410b00ba4401503200c0001c070244480110081400440c1140100030001095840c522840c0c1501d609082c4072241da100400d2a6544400036800102684000400030503c08021038441034030880559802c5440d41d20021b4018403c0426240200031459580206440c94050005059079001a2600060151030300c24203c0800d101003a508640205404074110402e211940c5150b000c0e104507400d51401d001d0b460141c540046521401c01ca07100d460745a03041580164040b24540301c0140002d010608040c1003060700d0707082d4510030904507450620b00507003401d0350314a54520b84d50001d040b0b9040001400041d20040b41c0b81a2040045c000c5042c480c014540111001038140c0c09503102c103001c03005609185c41d02c0100034003c81e080c00b20f421107442d1143c1e444040702d50b11180a558040e25081c00c1500b60342003400c0d62204c01d90124407230f0b040045003100a032090f4121546010144000710711801c0c203a88030300e01d2420b91079250f00980320600591001d40300400442 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 238109640 1250 238108390 238108393
    0x150b0117150901030b060312070f020d02060706020c010b09130308060603270d02070b0f0304030c020a050d0605040b10180519111308070609031112010e03210712020309 74
    0x20001c1000404040c0240c004852070b00c251400c3c060582400c01c8505807030304081d28203e00e40369a0340c0b650f2011640c072000007481889098514011912280182c5907245d42c44841551503680703481d1107502030000c03011810b004e0700b89074000501104c1c6190900401a80540301c01119840c0c403c103200d89580700034001d002d802412070034404100d030b0461031141c2c00b172984806080d00c608804130083c00d02c6010751040880190500005504101120403242c200c3c0c0d050030b100320048494408507002d80441d03400b180d482044c1d04102c00030310075190069132103603208050065542d41d6803400c2c0030f0906568041c00d81005600090b841031280b2a074000e9410502c180801c00c0e08014001c1301c0c0702071f51606041a030205501050300c000860070340014174080c0183d88040c065140c1000c600400c0c407865484082d114090241c0300060310380314603109816040000000380030040984034a259654025440d001c00309841200c203007049003819278468010405580c5015400f41c0010150380650000351194249 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 238110890 1250 238109640 238109671
    0x31805180901230f0f0f13030c05190c090501060519030e16050111060919020604030f080903060114010c0b07111020090d14030d02030a0207150b0117 66
    0x1241003e4069022001240b40c0520f10318010455800059001d0148290841031344280f000c803003281450682c1c00011105194000f90b59401d0498031010034000241060040c0401d001600c081917090f2017826000e00c54405038140d2303421000c0c0880c1c40911844001400034032002040364086400807060040d03500d404505102600007190415094810740d0700700da07402000400035942c009001e01d504981c0000a0840783c5040741c400c03a221202e0603070802042100f1240340302155180d030700b541c0145030048020000d00c800b0b41f410340f0040c0d11038500141319104241c00064042040310012550940684d918408403107580d4072002201e0b4040d204c04180f01d00b501d82800450810001c103580c422a0520214428003c0c40182c210302c00c64140e1503075602c02c1080f640e0041c1d1610091710b04bd455204400075410b4421403056070441c0181d54524506a000100344003c09156030003400304540103510344038100c0d400d04540001c0382e007120820360101d00300c1c4100d90314003040380c02c541703603c403420300c42c101034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 238112140 1250 238110890 238110911
    0xa050601090312080f061c030f0c06050a020408070509010b090904020406180f0e19080c0c0628030605011e0318031805030303190c02030d02070b04031805180901 71
    0xf101160704004000142c03a601000f103045549865250002001d03903041c1070f10440507070220071007600290083c2c14009556841014103114034500030040c0e401120400c03a0341004059039000e5403162040940b41e04c02e4040101d814500041034a0403101503034000c52500c05820107010350224010803e917406680c030b000018100d40c00482010030807502c05000142d07002c1202c658001c882d181111298640d000d41c03c08000d0b201192048407255400450154841c2110600c8501d04284200003a40210000c5a068920407040c580c0301045900c21018000744038240030210225405482698001680e00080d003142c030075a151014041c945a240126040e0310942d44c0c001b500c040d80300700f20000b84101115000d9501c0100c9174601400d4101c000e10301d542002ea0b903c0031007080c841d08503003080d9134804031940014020001c0340e100e00d044103070030f54541c0340754100135003588800c8a05030081030303100131240001484d11650405440d00100046804050044010700320305e001045820290341c1c8041585 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 238113390 1250 238112140 238112153
    0x6080903040e0c0306120102040f0b0c03130305030703020106210204020a030b03060c130f050d020105031302030a03050a08130507090b0f090c0a0f030905060609040f2f060903060a0506010903 84
    0x18810145080c000d503480c1014006d104072030b084412440c403580d01c1400107000c9024a901010121041440034540310b00201c481c00c1d0a5200700d41894160181200d80003041040100107054400d000703400801c104e654466440003648400d055000100061901200040c0b07000e501901840c0b420b460300007003c4aa00c0c0110b0300d444000e6541090142000c91521a1005009440070103450004a403503146413170000410b0a4580e860b000030306001000c0001141c01800c10380c07040361160000c0440b5200e0001c2c0c20701401c0c0d81e11807a0110001400080014a0740c00101200b04c07015030300600038010325187c4040a4020b04003192059406103622042d486c065990030f0b0000c3c003520081b21130540c7e81065180c05401010300c01250300c14542050140d10209601040c643c3d8000010b03600c04907980c2e52440c001e0350a85290000070600250000321240380c8070300c80d20702810503801040c950328003c00c400810009001d1503080300d80c16484400002c25840303464111a03008101818280ca9007a105e036a4171 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 238114640 1250 238113390 238113419
    0x10f11060105090a0e0106140a050a0311150d091a09150601200303010f060e03060709030b07050706050f010602061e01140109180b01030605010519031a030d090f1e0608090304 77
    0x75008c50310121035582103182204a0100411044a00c00c80c1c04e851561040c40c0c1804c9003900300d1050301c0e800020b03045000c13100c3c00c40d260543c4c03c2030200700700d260f540f44c0b440311908008032410a0307038041c0c00001c0000314009880007865001000e81c6c0d0703c41d500c0c200112a04d420f4805041c0110640c001c990078010300402c0958060050800780300003060400350014000b2843c4c494040c40380d4406001d00c2103280d00702d0800f07801e40e83c0140f40d81090f0350304d0400030781b1113215000b00101818544000c10000701e440c503002d18141c0301182d098500b60744403003021341121403e4903405201c1c5080c01004010f200342151002400541c1070601a8200f680c4924215001c0380c003441044440303480e00302094243da03042c4540c601034102405c00c18104070701e5402e101c1409417040c1802c000c1c140c2d60244020748086000030400b0615004013100e850b0941d4403002855038038a40300d14090042c5606005c52034410121040704000108000c901c444c2e07241c010b0460f00c4c40005001d140050200b0032010400d401141c0c240d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 238115890 1250 238114640 238114649
    0xb1909080306040e0327180f040506180d08220302100b0d0f0201050702030c04050c0a0215090a2003030a1e0201110904090c23010f11060105090a0e0106 67
    0x945460b8500710701480140c0c0c5883c4031455442d002040601e1000d40340300200c02414003401102c1300381e402e80601040b01c03c501607080e404025030030010000014407032040b03248a18404c40030350741340f51115840c01c1d0b072130300f444c5d40e03025900d07000140084066072056015070341c000030000c0e00d404035407503413038002000400083c000e80050700050007d110700c05003130007031030f00109080e41e0840c803800554a80c41c00240303c4a40003410030400154400640d5402c00c9001d80c08600107000b0402400c01d85038075906070b400641d0402c0940500401c0311002e1240480443c03040040c0e00c00f802239421b641d41c0c0c06540182e01e20b002c1120a4162003140c04588080001d085101c201d611541d580170307050b041513400381a000b00c1c004110f80c102200c10111100307407420356851040940e008607900d00103160255035100190071000ac482d40b0141c002100304041c2d441c000281e002130f00d41c40c1c043c10001d83c04079401c0000c10345551082d840341c00100058208150420750040300c000000900b2950b0070426425130300340b64071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 238117140 1250 238115890 238115903
    0x1140702060f13020d02010c03172514090409020a090f0f06120201170c09030111031506031e13050d0306080f0325030c050d0302040608060f0105070b1909 68
    0x40042c0d410390080c1c10b030f410210906050001a0407030b800079000c6503014500a041001c00c90074201014066400f92998031058907032070a60345010090700c071017991001503102c120790505640300d00b02406189101c81d5420ba4a038075600d084c0807401031002500b5070700c0c400c0381c1100d600f81002600010754858800200c0072158082103941d102c1f009841503c1303003600640200c2a20b9402d00d00141e030401507444035841d511843e40e41070b0741d075480c0410040c05201d29550b01542081d41090310b04022800039032003103d40303041100100c0c91503003c0c0300d0350340803c0343d403100744805141040d8000210110900e81c02205440c03d10104d2070030382c1e20f4605124800da8648042074851105010100b0f00340b2a038480610080002d500300240c4800e00081d00514640d0a403000020382c0c45081131510a11840e09030035000320455042c11400140100254402d2040708006050440840c1071440c003541003080700b05d01603407210b0401c601c50300c3d08802c4c850040c2035082001700c242030720000601c2c24090a15401c0c010107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 238118390 1250 238117140 238117153
    0x140a03050306031e0c01030c0201060b1204050f010203010303021002031f090902010e220e030903060c0a09080309010905010e0f0910030201110109231f0b01030b040b0105030a090501140702 83
    0x3414500004007404c01c0307483c140900c5100d07204034000341d0300302d00c0c030780903c0c01060381892000160300502c541e030480b07035411500107600200c02010501aa0042d88034200b200d0300c5000c01045e1500302d01003808024016009140321503140042134002d507400500380400c44055200e41c219a80d00722000781c2c00302c0207060b200c0000c1c0096607000102d03c0c40c0d00c03100380d410b0409001d914100304000c2c0403865031580707015640c000101c2000c104006552254001404441c00350038030b05020301083c1c20090400f80000d0004101140881020047c0c0f9080b00041e10b80c54802030400f001558481001d1840542140600c820070b041030390750030f544d14000c030031107620320030003078118000103003082d99105d604901c0d85e040200050004e5145001d01c03a1070101c0154008940c00107400c0d00b400c3c03007681100701c3d2505011600560458000d0b034032644051100340c9003013041d09008001d01040e00c410114141c0803c10500003d180c8510542081d18400c1c1720300700020300c140d56441c218000c840700342c8403500140e00c0382 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 238119640 1250 238118390 238118401
    0x6030501050a151701110d090b100b0301032307030803010602240a091403070615170d030b011709030919030f08130305011a0907140d09140a030503 65
    0x70300c205508007000c0e80060010041c02c00c0c80d404038081c50b1040c685188034070a00d52401076029881030400c10700512155035078100700c0c2e210b00060000c0c514140c0300c4150074404225010341d45800d5070210b59802a013141140c0c82c0d80c4030707500c10b86150400000005210b04a82e608440144801c0c006984504011747d00d039410444001d1a028003101c2001c07092054071010451200081c1a0343d9000c110468045034400d15868582c40c0c0e07030340140d4071089610010903038804005603900a00c0203813a1415542c20b490365544040d0480c2040c5500400240d0469900b040085120f504041d54101040c1070272060413a103225071810b8001c040760340c160b076a0004205a82c003454003041c40300b4010005110304e045641191284040e050300044020540c0500003500c1d010100c901d29004000d6410000820441856031185c00f44042c030000e1552141c2950ba0004040d03038090100e40d160541e001c100c5a080c05811080c545c014170900c00b00390780c44a28011000d01001080110700341c454841c0d81e03003c2d12030508 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 238120890 1250 238119640 238119643
    0x6090a1e1401030213030609051906060504050f160c110310050a06050f01050a05030403090f080c0f060c15040624090b1503070302030411120307031209080906030c0c010f060305 78
    0x41c070340140d04050042000c1416243c10115403c240c0e500504002044945490010300c1d1900c3e401001c24034402c019400300c02d002c0c0b035601c400c003100c80540f028802969600203110401070100c41001207040d50258085d0028850721950382078621035854480c1c0400c1c01c0000034030380791010b1a55103441d504c0300c0c204100d140d1a40180710042906030303101c000d5078241c980040c0143c0600c081d058200710001c070005050501c280303054001421010800f190043d2203480087e1110410310451b40507c40720090314038a41494030480343c880c8407a00c054120700c4401c0d5500e5990200190080d03030719644942ca0051900314101ca2540c06200004503001e005191003c00d80036600c0003c0d2251040104a0f440744900c803c280407694444c5140c40d00590702d66480c40d24000324403001e0300c11600800d4441c0d6058110750004000d2290b0341c06501e50411620042400c87d0545101d4400241200001c0c42040b050b8140300000d1030f0030680408040b814101511206400c58440201840b2480e45a11080050080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 238122140 1250 238120890 238120919
    0x3021c0201110703020105032206150617090d030c1404060206060117160806040e01060b0a11030403020f06071a09030703090605090a05310902030706170606090a1e 72
    0x401c0010f00a92031850300040c00c240401440c0d910880000c4241c80c4044180c400000b11540e07218001b0800c0c1d11600d401c0e000032119502550002c81c440c800001c280080c4001c101d44030340c0082c002400c154509500c120080e1401100f90000d01070000004001c035403c44020700081c014540c001d200501d84080010f20b006081a2001100c2c1c1c4070505104000644400300300030120141094aa1901c485002c40c0051142d4040030141d5480c040b001304460040e60000c02e0b41d2400f60740c5040074101145503084d22403155100080d4000300c031491700c58545c10058054181c0c42d0040c80544082d60f00f2207e44070b180082201d8010326604001901c80030150440803410140c0018a015410240400c000c1141d4510354040c0a1051340c03107408008911500e40c42550401e18040086800b00b4402c1c0301c40300c06050745803412803180c003510002048441c0b00358000d0354a0030303601901c4610398075403100303101c51684a0b11820390000b001c5c410224004603046800e20544444c0c11000024a19006000d0100103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 238123390 1250 238122140 238122167
    0x3040b120609180c010e0604080105070908010c17191407090305120c0d0806041d16120201091802040306020f07060506011b1704090608030c060c040303171003021c0201 74
    0x4210100c00e1a0054000a01880d021340c2800d1100b00c51110000060740e0340925440748a45600341010000c1d09a4014407035400c4500400083c80040c241c0d034410382d504c038000c17080c415440b840100000c7c60342c3e88555600b032002803505000030740030b88005880b00400d4021140300c004540b902004204006040140f0b20200074602c03622810446425130890f1a000c401100d082001442008034005941d103a03c4548040b1074050404850154640802d031100081e4001c0450358020040000b200c0109125680c64643d0503502e2918a90a000200c1001d80c03c000d441c240c40d50f0f0034400840044d89601c01007420100c5080c01c0da403907100c586042c0056900090409042140314440e03441e442e80d5642540c5c45141d44200e105100c1024112903003114051984030b03041d0301f410002e002a040780c3c080000c14400c0f4103003003550441d030f4640700114400e1250388001000115180b034021034401c0020107103500400b810301d8044480b0307900e4001460403442800b0b11801402000f51440c2103603003700503681d015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 238124640 1250 238123390 238123411
    0x18022d010305130221070816080105010e0f0705090603010927020303040902160b0106050703170606070201050a18060519020601030b06010c0f1b030618020f0f0303040b120609 77
    0xf4900081c041801d04000300b8024000d60091129030f988105280c0b40c1070941e44404122081980e42d11407032665440c0c80c15001d000e6001d050004507165106004031816030388030340c1d0142000d03107e0011100c01040006e1060080200501c04814185d459500031070080c0030340ca502290002600c040e560400300032036480c4481e50010401040180c41c044240c5003205c02c0e8000060f2164450000c140e0328443c00e100041000140c98000f08880303421601416440380a5500c0c0f440021441516030301070a403d4400950056050203c440151312940082030018014500400e01c0204031045036843c0f00f10350084008a180821406c641e00c0c0341500d0030680c80d01c1c502c0100080d5243d41c54040d0703800030152809041000c00d03c421010b0082820340c0c8100c0d42c0e485131720003040054502e500b090481c0c0c00c0c00300b100d156060103d0360b84042d040085500c2665001003814060010000811950050201d0785642600003403200103411180305000e02034406801403c0d84061401904000c0ca003c001441c10245 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 238125890 1250 238124640 238124651
    0xa151508030711010513050307030b0f060105180607030525060f062d0305120705070501030b060d15091a040f09030c17090909010e07080c031018022d0103 68
    0x410f402d0700695030419800e003803007552070f11400d08401d81d0102ca60080c4e50140304a540000400008100d1b49214540921450007181c590f07000445042c03080c4081c040320814500c0611182e4640b81c0010801d80b44603080035407030180301e0b10722914200380c2c2003074442c202c039402c800300c00a00102e405030b20701314100c1c00000c000580c100303811141e174940c070310304205070100307100c84034030f903203094000f03894010755004001c480d00d01d0039801d0b08400640c41010b00320f5041c0282640003034194000c1c0544c81c2d03010401481d25003000300c11540d0000030011581240019901810001000802445090582059610000e5003005001e05010035a800d0002000e51a480c05205d000804c1d07110b5900019a540079200b0315465003c4140300e86075002e01100e25034440745034000e200385010305601c4484200958800d480300c2c19940c01c02c0a0f1100100700d0b819803d40c101c1801d080303014034035a0203d0303420014904c039443e80c030f07440b5000300e024142e030104d503410920074980420b458480c1040500311030403024a0b00303110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 238127140 1250 238125890 238125893
    0x30904230c031009022a161a030a02090d1202070501080c160f050721060e010e1b04090510141501090603020a260a0b0f210a1515080307 60
    0x45100b43c0d1207500c42c411303404518001525541c3c0500c4004c0595441e521440071240b071942c031344880e107c0d41181c0b07408003046c50001300c2841900e0b1038000c04100c4426a411a41d174409a64040d51005203101c1d0310a0014800c0d41c000303140150340301036500040d8010107900d400c0c00c0c0050a034500250400000d843c0610804100d03907441c3c444000d0701c903840b03588400044803d29015160441e075420501070b00c90828a03d141180c164084c80545500410042c00707107047c8903200c41d01300c80082e40114120b03007102d2501d240d05149000d11101d408070242000466200c1a00c0b254100441e103080c01d0029511806e0340300017403456a50b400d420407014032401c603000801c080047e140c0b041c1c9104000901d500030554a4003140580500003030000f00030609024695801201401c0c030408450446015240034841c40b141c0c20101d102d0b480203030000d08050142200c9a030107020b900702e250b2351449184510980f481c00140c040791041d1081940c464042a078080200500140c40c2442d001400e0700c0e171050116a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 238128390 1250 238127140 238127161
    0x6170106030f29090318010819020310080601080307050601080721110904030c0b0c120c0708040816030204180f38060f0a0f060302030702030904230c03 67
    0x10b1034603401580440102e40303400c06502c1c20501d410420881070f06078010060102c4001c00148841c685264812a04125503001502c4080041e103003a14500c668881e0118042655802160000e03d070304201684103603507502c05454804c00340c01445864101180c801c0800c8010080030b40034080000103815418201a413020b44240c2c0e014140071250210600c1030305000d440b00f06a80c1c8440e0150030481c1c1890142809807502007020400c403000003c00c800030301c04007551810b45414a10b0080300110750780b00d901104100741c215200507900003a0400000800140401010b45d080c00b0080c40c0305182c3e46036004110890748200800545829520210800254080a400240303540903501d20307400030180d191510b00c031100b2507400320f2803480304525106005402030000e00c690170440d5641c4540001c00180507406209116401101010705c8080c0b1840b8007980180d0350141c03c5204032170410320190001410384100d8200d03298192030f25480c40c00d04210340c90205034401c01c08481170b443c5043c070f5603594 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 238129496 1106 238128390 238128413
    0x3080306130b0d02130e010501171c0e0d0309031403070519080412050a0611040e060d02010e0f0f040203010321030b0306040210030209040f0617010603 67
    0x803200c0101c5000314003603400c01a06501104000d5420b200c81079030100c1c2c0140320070ba02c1750300700840d0030341c00d124050080c120b01c1d0084075662200f18116007440c1085003420129030100030301c0650981c20103140d14196605844514007000b0034182120f040d0fa80750001000c0308410190501d03030325000406060413134003900550300e02c44448420169180c481c06d5004203264824442040582481746002e01c13170030700078000c0e0350b03911003240d6600c0d080380e003000e402c0075061902003014000000c0524406504c00800c4e142a04084060380001c3c01c1c100030f0f0015203103d4090b542e030445171a15a0f0344a80d44408010700195103a50316481c2081001d40c02e40b070180044900000d860320301074400d01403c658014054003520140e00c81d0380074814100b07590b038500c1007890340030030101c101901c40d0300c60101c071026501000158542030a44110307034201c05544003481c90f81006400d001040080da0388 = true := by decide +kernel

theorem cover : BRFrame.Cov 237949640 238129496 := by
  have h0 := BRFrame.cov_init 237949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 237949640 ≤ n) (h2 : n < 238129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
