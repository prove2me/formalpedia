-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1236
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:55:06.682929+00:00
-- url     : https://prove2.me/submissions/fb3f0132-9626-42f2-98b3-db56d06954cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 222122302 ≤ n < 222302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 222123552 1250 222122302 222122309
    0x130303050d15081c081005011d030312040c050306070e04020d0e070602010c11030903150a0b180103030e0f010e0d080408010207030e090903070503040b07082a0c0609030601210c 78
    0x650201d03503140513454405200800d00d2005050603085401c100204000e841c0081c065941004100790792100c0100c590444000e0900000d401e0b2566920004800145050105c030160b81061014200080c00d04000034028803d0b18150380c2c40aa01c40c1c1c100070080654000d80c01c0700e10742c40d22001800106c0c202032041000030002c90700000350501404a01a0405150b000d208465810a1003911a00e46011841a04807031a07802401c1c425951084110000c1001001d0039030031200c0e0098000c0300240c8a00e505050720300076100c00400b00c0c144801c00c540e14401018050004601003104541400c102d0404040d40d0b125885403402c003901c6000701801ca800ca030b6001d8000601d001211103890030b0100100d40c20481020143d8500381e40d503125030740d9078440c41c441d07010303803040000b2428240610841070750325400b510f0039155103040e90b03010380035400c1040c0002552580a4200340401506d040b0b4203c0e006020090090011a0320745021101024010102120783e00408494403000904000120014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 222124802 1250 222123552 222123569
    0x912050a30031505040608190302030c0a0c0f0e040f0210020307080d0203040c0815160c0629010e0919021603020f06060103020c03030f060301151d090102130303050d15 74
    0x4620f29038401d12066505612103400f5518120f824880c1c140c0c08184800100c61a64814034510450f150032440c40c410300c4824a8a809459064420002c1420100c001c5900242d411007415444410b039001c0742000b030754001c202411001c500300060512444101c0702d10318500641e8140102e0703032182c2065034403c03000320040a80c004204070402000c0c070703000c4029102c500c0051102004179541c0d000400350140142d213510300c107440e158034400d2081c056840c00d10b80c040020711082e00001010100006603211658890381c0d06051002c00b03500c40c3c0c40007500440c00a003000d042d80c982d642000100c01140000b461000e40811061402d00e40081e60828107a21a03401000c0c8138080c030300c0c9542440c0c0c025008034105801048031042c4140b000041d01d4000040c2c40d544070f11501d905002900400c0340345110041100000b400140c0003041d20345004410914000028a0369030302a941803c0b8400c840b1518400001840e040c00400e1045000d020b07a0202076a000800140b526500a00c800c01e65001000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 222126052 1250 222124802 222124811
    0xc0615081e010e0601180b0316090e1209010509010e040204030f05031b0d05040501080709170705040b0402070b0c030a0209450606070c0b04150912050a3003 69
    0x489502440b079020f143d42514060182541090540b6080d40344a24030441d030366880b210065025a401e0141e5040100d0100c02c4420032999405413801070039041c06007540310300031503e4410043c40c041c0101c0d400c00300160b4482c4d15240c030100c0151083d1881c2e081c0d182e00550700b880048005076100340705440d11401130005644411704a0385400c2c6424145615000720340000882c001010b402c10180c9040ea10242802a12903032202021180b0803800e90101e11007540c4400c0f082c14010340410f003441928402e44042c0103542c81201880113a11840740028203000c20400001d0249640d2006150821101e032800b40c5009042000100254a40da0f8000b280d059140020104030215064070304070030403c0c01c60707200399034110703c5051001c0c000100010300861000070071104110040400038050101c3c0702075261542d460704807810030210301c030655401050380350001140c1001112094111181d1000003007802c100716a4510334010807003800c0090300d40c2140c2c0340c104d110241420306060b14440d9940000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 222127302 1250 222126052 222126103
    0x170106090314070506030114040b100f020f03030606071b03050a061a0d1208061503040516060c0b01090c0509040c02010b0a090b0a05060f0c070e04060c0f0c061508 72
    0x141441030001440b040ea80712450401070754a9050580b4112040e1181020f24148128045005404a20200c50340085003c0c0d807054038076000100c441c2004296400c61708121042d00c0040d03500d22090741e00540c040c2081c441c81002070f050f03000d0301582010300014104074980d681d0b15280b1341022110200c2c0c51300c0e114411002114248015642d52030800c4416a1301501245c0300c0c80c0002d10301110030010000403900003201621000c0d003805510603044120307030740e0b8a014242152505010000e5142c1100210f40029a15200d01c000c490000c1d00a10320003090391800510704010114540000140101844490704960380c6200700603114400360008078002a8800030000c0360503054121800305c1e843c005040c1610348800310104143d0f801520174581da51b66044c0626100e0082c003480c55a01e104400010812031009080140510b00c620f40c02d00600300300303107000d4603280100894100040c1c4800100c0d4086840c9400404140b480000c103500700030344410300c0d1b606051602800010901a002c150b5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 222128552 1250 222127302 222127313
    0x2031c080f0a050411151606060f0b0304080d090f020907020d0f14160206040519030308090d0c120c050d03021b010903020a02090c0d0f0b040b0a050a0501050a1701060903 75
    0xa03610940d15442080f4a1804c3d0791600141288020842e01035030494100411600c090343c00c0301c261808a0502446040c92807502130041d03c907a004a00d130001c0c0395440061000c1c100313403d40f8000c0d6440707a00d039030a003001c1800f800003d1022007420348451117004e00304005a126024018010034184d80541035105101c08081c10a40307031031400a0800403030640212013044001e090702d40c5030b040700034000c1d4108103900014905018642240d944102d1036040c440036100b003125100122480307910707525801c2d47e40c04c804944030101110001c1c0451810480c00c0300168141e100101010304604081d00007a1198403a01e203032202d01030504001ca5070000f84040d02c800b00d003450b00d0892840724001c1c8200345460364000e45486203000024021030f0382a002c61030318410b403c196410710f02c1d8114100701c040c50304c10780d21001d4070008900034010f0f03141502c02001420b221068000303480000d44568880c0380303010011142540700c94890400c0001180d007448188640c1c400701802417005903280c407085403d50a00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 222129802 1250 222128552 222128581
    0x2c150a0e0d0314130503100b030d030204030203060a0b181006022104060305060d05190b0901090f030809010b090c030412050313020f0d080304060609050106032702031c08 75
    0xc0d03a1060701070080c0d410010340e010405154012034030445030384408a543c4a03039000180342d003026600d4007e4a81d004440011503118007101c91040b0105c071500008070a00b54100c3c070980c00080d405820240000c0c4108800d07400610320359102071b084200011a580740240c3d0381806945001c460b0f080c040c0100000c55041041404000103c0da050101010900b00b41c4d0031403046100d924141354403403001507116611444a503c9880c0c00005507100c04441c000070b1f0580308001e100880d00c3e114010041410000d051080301c2c402035006001c2c1018491603141074421600013014500c41c1c1d0340769028a4407903204d50340800d0040b55040082601d80c20b003031a043c100003500d4400c0c1c2040150500400c00902c1c80e4001440050f6010b0718013902c07000110011484200c860803000e025540700100f444100905a4443d408603031002208002c0d41e600c680381141552901112103014003e000401c41c00b4001c1c10302c2c1554061320040072100098040036001e0700c80300c1210928004141004208407801800604 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 222131052 1250 222129802 222129827
    0x9010608100b030c0d05070509040c06030c1b23070e0402090601171302012f010b010f0c062f07061b0c06050403020f060a020d0b03010605012c150a 65
    0x203016042515002c44e07511341d14441007610401188120b601480340c1407100f000034004c01307040458246443c0c10811701400240c0f060300c00281c50036041d6030500d40320307051031100090008000c0c000c1d8456601e9655802000201012100b00c038171500c0c09003190100a000010541003110040c24603184c010403403421002060a07050000030b02d405070b500f1440e05182a881212070103142800860303800100c42030501440e07200034020301c042c03d00d024240d07040e190380003a83c0c2070002030103540e1211004440320104c0051480218030564035110000d006034000000c03192074151280c803420300c3d000c114102c0311000345216481502c0058804140080f83c041c1c204215420a00550b0030701e5505402011400364640c06080c01d580e840119040510a02403032004d6070b41202290400c1c02e102000e40001d6014050700700c005441c00d900d0888504041c01440100c40f0705071940502d588507495410000b00392a001d9010718080d940c11505c07030707944039818180341d242c00e034070f01d11b403a0103581c440a4090540f101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 222132302 1250 222131052 222131083
    0x310360e0a0803130501022b0e101a0402030109021e0f090d1a0106020c0307060912080a0504030c1d0601020a0506071805280501050a021009020105090909010608 71
    0xe4644101030380010800c840560090400d6925a01c0c04104a803070000424001e105500016520300c0c0f450342d8600e180c0e01520307403d2001c008a00d04d604a0310458404165000d2281c00120b4911031880e15a0312a14581c008808014001126900010200c0e4000d800c90b600b6030364041950650130a0802812000d010ba000358140f521201803078060740790154901141c403e07548103811104202047d0359400301e1400d00e5800c80d0345545c64520203501e9101d00c00e8020302030300c549080020058460301c4c03800100d0347c10f049e03048841d22080c0c80e0000254080161501031200c200000000200100c8640b0000c01d000000700f240900a00d0700c80f084540e02410640c1113502001030392000ca08042102a080405400c0840540c0c0f03080e40f0310441c02c1110382c07060380c3c4078030304c1c0d118040d072030426151003180e041d03902d96201020f68440005559074000d1100318401644202040c05001500c0d41c030000002d4014101a400c0080e004c1c0092a400f504542d51003541e5100c40040041005c10083c02691120741c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 222133552 1250 222132302 222132311
    0x50f030c0111040f031b080a0b04031101060f0e060328060b040911012f010203090601060f12020d020d09060c0f02010c1704080706020307020a0b060f1302031036 71
    0x40100d0044c1840c0e00010744032041070646140d003612110400d00c000d06825054400346400d40c100381494000444040d0007082801d0152802c1c410184601000d4595031181444064144841c000071440000d00c03564242c4500b0100501c0ca010045140710007240d10148103c20307034007601c1c08109940584400710b015130b0a1a88650004405208000c0100c4080c640700c9005940100310b0f000382807004010034252180f01e0704001c491003064004503c15132244040301e4060b41d0341c000c03c686c80e90501d8451030004a4410740385111542a40050001104150026040c082c2c8402030404403842150222003466481914801c0260001001402d244090000700300000c001c5d00f014085000003884204200d20300c0000800308602c0300e00f99080641c00240454503864485400703941c031070701c503901960b001c40b200001070014a00700d03a9041002c034024056000044400d00b900001c0d40000e00b00550050400d4808242003554000080d4003100240b154200c0107a1480500b01c0c20740b000c00500a4035040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 222134802 1250 222133552 222133559
    0x305070b18120a06020c07091109030601170307051209031606091703040839010f08180d0906030b040b061603050d02030405060a0b01081003020f0d050f030c011104 72
    0x40444848051805840540300b600d00001500e0a29044000041c100751001c184d0b00340819000070720a083c2d461028040000f100303190074203860341c044c82d0103941d4560312000041c01008101011580c40562440c11030717013070581e9035480c242000c8040303111024511000c1004805490304210a8130200c02c3e100e580d010640c02d00790001e1000b6014011800800c107022007442d507a0b0400c008030b030000e1007c0c1054034034094065103602c2c5120301213144c1721284114030441c00304450b41c0540b038030340038ad005840310024885010000e40cac051000900100e1414182c0d2000c4402c964180001020091540d54200040c0d04100000d82120020340e46140542d20b0416100f005072141000c9a000070702c10000040c80003a00c1c6404c580c1449040404140b140c00401480200640018614042c070f540301c00611030342805600464000c503003156681c02441e6000703410405420305103c240c010701c0c0050441080e0303104a844a52405030642d600742d826030300018400d26051000e1181c2020707036181c07540807484c080c80c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 222136052 1250 222134802 222134827
    0xe060f011b11060708031005120607050304020904020a0b030405010e0610030507290705070303020c0108070e041e180c0b04030209070e2e0f091809050c04050906010305070b 76
    0x44510002d001518090340c03402d0701d55a81060b50781c41503200300842d540713180c4a0303110320041d0101e2148500031a001c03020700c008814003080007440317280705a5810341513654a800708500a0030103001030b42c02002008010a0a1000000543c481c03030040e800801c6424142d10714a1034903000034000442e1000007801800054008144e10040f2401c1c8206051500300749030221901204841d000b1028410000f071800812401260703c00c01c0b02c2c00794007912104c0100400548000f013084074081c0024038401481c4615241a86c400d0b10082e5400380e800c100044042c0302d10084803482d42680e0b010f09844001c5404002111100d90003800011040c0c1d401c043c0b456010070302c6028054030381d805001208030b140b8000e48030b0640041001c40c2c0c14107081240800819828081c0201080f030b000005c0c3c01e020f035010702500404c200c0c42102d43d801d1002e0205160b0f005080014544000103c0f0300d070050140000e2195200c1c00f402d401040c0030130203000c1951452a0081c83c214103075200712103011051041d03444500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 222137302 1250 222136052 222136097
    0x60a060207060507050c04060e24010e121c0c1403120c161b030b0a0606051803120d060e160507030f0c050604051b04090203030910090e010e060f01 65
    0xb8002d04010743c9900703031032500300d00b0715104184144c0c00528002c00002c820103d990624054201070100400040043d42c0c2e00003040c0160070a45d011800ca0700c50360901381001416004e181c031013041034031801071000f10301c001081c1500c2011030010710340028510522103003442044002c00000019450070280c101c02003a0080002c10340118008003203042c50301c034041000b6030390446900011064100300c0110480e0141821404141c81e050003c07000909105072034428a016154a906c4450800315107904000c41000110b21064040c002c2e2032680b11400240005400c84042000001c24882d060400d5161618001401d90040b81c02000d002c0c0702460f00242114400e5030103160881c203080801005484050500030300074028800d079400c02050000100b410590003c601c80105000000c0c8401c01c81500e506480180d80758004111090441c54a40c1d60710f0000055410801841660340501822a6200b40e00c5086542480010440c0328030b0300c4d0b022030300c5c3c544090070300a03440ca00c808140c03402c15 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 222138552 1250 222137302 222137309
    0x503010207020d080c030403051f05060906010c0b0c1c0f0b060301181503050a0c0305120f27030d08010303020118050c04051f06031b020105090d03090215030a14060a060207 76
    0x501c00000d03da003020303000b8021a0301542c9c11038111036000303500003589200420040080d00b95a89404041005840c09951181c020f44059460714440c14058403840c4200d04050030710b0042410400621800c00c1170301541203214065044001800c0014645200543c0c0c5034824051003441c1c10801402840580c0c4103c0c25681c40a0800160301d4004007103071100702c816a00701401702d204080d031a80411020304921810382e8030a01c191105a20440000d9102e400380070b4002c10104004d00c904803400400e00c106200300c0c2c1e6134a00b5403503400e400c40080b0b42004c0c0d52035960000200110014420316409000b4a1165510f080c0c0d0b111402c5015202d0a03228030500c0c2199200350340300c43c042140b1000b00c1c62040081d0b950b851340c5079091581c650001d4002c00c40c42034007440b45039401d0800000341e40184600e5102d241d82501401c2d0142420100700d00a24401404984c4488003020411109404202652040040800002c1c1105615009500c1c80744024216449580040c2c401d00c6481d030302180e0036044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 222139802 1250 222138552 222138563
    0x62107120302010f0504110a0608280b0d2904020105070b0912030a02120117030304170f030a050105011107140112090203011406011b02010e010c021206010e0109060503010207020d 79
    0x5109441c5400c9014081c0068120703905401e0405110070300c01901d001100c1c10300e08507071140d44650780390030941782e240b0110703280014070607079036040b8224501c060010789207411200c0c1c0010f0b859038260b0015030700d14041881502c8101800c161841054030041c2c0e54900703040074500250a5240590001b805d61140102c01413007040900c01040e100d410400110141050705c8440544030304d402840b00d0025004002c3c5e0100400c51000005100d0005016a0350508031020280d4650b0b5116100c00441011a2a0140c11a04200201e00c50341403d030740910301a41e0303101c101180c0e80d45044001410381c10400403200594100040170086042d01c4203400304411000c0c2040c1c2080301d41127107404018610998082d405500b070400c2042d50840c7c40c40080d01c103c2c1d00740c036840400700303a0402c00c0d00c580c820808004d000c52540303151101c0541c09840c0100c600d903c001c0c05002c01e00080d80c0e0080c2032980030380c003001d00407600e0001070180c03002500409018010680c0214140600703900000c1445041c120007510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 222141052 1250 222139802 222139829
    0x80c04151701060203130605070c0302060702060705030315040501050f090103060506040b031b0411120703091e030207080607140d0906021b0706030b0a05060a080603030d090506062107 81
    0x25a03029180201080e61504007200302580d540c07030069180c1c1c0c003807201950592a10301d00400e1040c050415a880300b9001100c0f01d40c0b036410341d82400805e81c4151030076640032100b0310500b40050300c104015441101000c0c8014801925401440706440e0107811641c0310701e0036246041007548405184a0459401c8100441c0c0354540a01141c0100500980d041e054081c6c244441070b500101d180c6032b5025003050398100001050410401d01c103025242444541c01c1c1907d003c0b51101d8440d401000c0c40c140281040141c2015141d81046e44c840e4842d4200e001d40c0254200300540c1d001032021641c406084d080500340d840d1007940c204554070072031403503061003680c51101d98240901a81a61540d4050701079000281c040f580c42d0341c0d50b0b11802c0c8103407000030f410480320036080e062070310b800c80c11107801900c01410842d2a41054440f010024101398152205000c0c0040c010118025007a071180104091710b031a041284c14090320f07030340c1e210748003103010702e0542c0b03000016400040c3e4000b141c8207442c1c001c130f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 222142302 1250 222141052 222141089
    0x603190c0b04030804140406050102030d0b010504090615021005060604090911031203090d0201020702060301060c0303110307030207030314060d080706020f18030d0c0c06030b04140c030f07080c04 86
    0x280090516040105403000202d4003104000c050700052080d46d042c90f40c07800c0314904100030401a24803038040e20340180c02c240011641c05a4a8200c01c01006050401e41d05040c1c4440c100000c580031030303001d5800604a180d001260a806205040000700300c582c00f80000d01d00680031510501c06e610884520703643e240ca038a814002d9803600191540401001d403046644214403000c490b400584a08101c2e0191030210180b8a0052003200c0e029076020345480d003582e04e031207410b41e41c0740001c8000390305054407003070482005401c01d001144908011303200146c843c0190300700102154004030381c41d20714507a19001e1204d41d9599a1296050660107007129550b1202d40c90300b80c0c064007403e02c8220300c64130040340710b43d41004901c60020030040b05400f29640d24180030001c8500c1400d001d0040e048844801003846068425000f6124101c03000c1c10110300c80070996150a4480402c81d164200300d036000c0203209800c0010101c5581140152501001908190481c22071600c107134170450101001100120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 222143552 1250 222142302 222142313
    0xb040c030c210e010203040524010e070e0102010f141005010806090115020f0601030b010515190f0e0312030402040b0a1818060c0807090609081f0605030a08040f050108060319 77
    0x15552451120001e644074282071801c02d64681c1c183e6a00384241c40270210b00f24844c003c6c28422412110300c102c2004240e21800810745c3c0340c07800075440c18110754031201c000400340c2c0c00340a5810b000f0b101c1860780f80c440c82c0000c0f08032402c815070f0300f01d10f0400c071001090040c1d40e90350381c01150548041d90079102a02130071401c20b0749000c82c6d540f040d40c86805050000000d104c0c83d401018100c0f80261000f208211520f00078030218403c901c00001c460070300d0031450354068407800300045264a1410109903c54445000914040003400320700e0f89000008200003c509040c0295440b06009590081d00b49007440c61403514882c0254400f1703441a943c03182c0900400507150300781ca0310350b00868100000300c1d070100001d0034101e00b1150b21010036015040018003501c50002c1c80111804880034100481e04140a4503a10103030301c158502058548102081a07607091041160491041c00c890b80d0715407614640320005007040d07100506119860040081d142c4002c10900013a10a8814810089180d880d18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 222144802 1250 222143552 222143561
    0x60f1f140303070219030b06120a111302130915030209040605040f080a02010e01111305010806060403080c06150109120303020309210a08060d030f12021c0b040c030c21 74
    0x80e41c0301d0340c1340d40400d20b1700d00f00007403e4054034010845030640c1c1c1d035140b051140c0c0e440d0f2036550703054562021202c2c1c80800e031210b2042c0c50102c0001c00300030b0f007030b81da00d0f180c1c2e820f0343c0040c224102c500302c03c0b9030108200801ca103d0308a20b019403c0000040c240343d0f400103001810001c00140485403a4800078040040113404490f055500403202e9484a11018000f402000d00e614400311643c0f8082e54103000007041c0e02542c40f51042c142c0f02844403400c1900458450308054204d94014500340004000039041d00043c2c01e60303045d180c00412103883c0c8921403c501c1c200c2d0103030503030500c034090006200e17074a004454620550340508000d40c3c2c170340ba090714040c0b9100f4000a800000d07a80c1441c030740e901e0015240140040321295542c01c40d26146c2404101450407640001004601410f4040c0602070007041104141070170b100703005040001404a0f844801c286251010b842540c1d008075455034038140c4039618196800d458104100650084007a10070003003802c07035401c144030380880d0805e9820035400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 222146052 1250 222144802 222144817
    0x3071703041e03050d1101140603060a0902041d0d0f03050708240901060224060901050906240306100518040e0a020406031407050105030705070609031709060f1f140303 74
    0x1290803484080300003e1071043d1002000ba071b01d508080140c039030440c424024500440700100030700015100d03071007054000c11801800b203820a80f1616880380c0d440d5056010411020844040c1440c0440c0303840080100a0001003132003858541024030440c940c3c054845a40b100075403580c040b0070b00c00101724401c0f91406500b003503031010389503001240c016804142c1d03200c183c54118a00031082105110100049000c40b02c0e00e40003416000104102e01d803c550554110b40090240c500b40070010300c190000c0c1d1300c07000c541e1030b902d5000021300685043c6044c000720044040c0c0380c0b0300d003403000010403199039901030340c5214030441d22804c0c405100d1006000d4625001e070f0040041001564903c1d0003964921080d100c080c00d0300500000141650048080300c2c440d80d02036440a18107111940c80380c00500140707005a04000790140d946540d0f8000b4050380f40031b4804000100100d10b08010114000f4100600000e0740803d460011003210140b600c0c2c2c1b0f021b40d2180b28009201c100f244000c60f00d180201003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 222147302 1250 222146052 222146063
    0x31b021911100207090c050a02060408030705040f0b180109080a0b0a0e010c0309020406050103060b0a1412040503120106030e0a3f090509130605070c120e03071703041e03 75
    0x2c1800710b540014804c0c1c21101c3c42c1006025918066009035014003906040f0750150304108005000a402d820041d41d2004075404c0460a1035200c104102407001c458206a46404d000255006c00a1940c424580480380c2461711140440c02d1022054172016007440042500309d865020403a0143d1b150880c161824040c8005c03c004c0445070b8004010701403611003070380900c0c1341440c003280951290080f10140c6080409840c03400034001022125941004031517840d84209000e03031215402641c960030300440c01880291740350000e0320170003154504182c0c040f07014035103089600920f81c100440d8150030250404081010041d60110294003901c40760b9460b101c450418401241c0e14443c40c444080d800565075840c0280d50310ba40601c02001c006541c03122600f401c80c3c0c00000016203981040340d20003000d1503c1c0592201540c1d6005030020801000c9001c0b40d2800202096814100145d00060a0703800c141c1a10740c280e40c0c16591244250b01031035000c03006007054042c82c120b20380b090000565008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 222148552 1250 222147302 222147319
    0xc04110a1101140702010c0801172a0603040803010924060c0204020d110c15010e04021323091005010b03070c0c0f0306050f010b030403020d08131b0501031b021911 72
    0x404c0001e00a0048040c400e010448401c00414030b01d03403035000200080407a1008000845801e030100e01000103c8503110804021180891010349608d4041d5001d00e101d20f2500380c032941441e01a50640c2c1c9a44404050080c0c845020b203c42107109813000112652400c2803000242e0600104005c1c2c403c2d031512a03005401d001d8440c6044118900403c1145800e0040d904060385d03100c07000c0302c1c1040078400c222030554910302240151402c03010022400740b01c0103002031440b10800003101300125000c059100424054100448041c061040100c060302404040240b5810046458a140030103498101007040d0103040008000011a001002c8c00d03648001110081d0707a40351034005850104c920007503500c81c01000103040504101a00e02603541b540203401d81c0c0f141608211035441008144c180d041d1004904031000c100400c1c1250b03d0103c0a01078075000324201800034068031100588103110410440c42d1025040d808948206c064014100440c0c0341c13921810590308903900104081d0780b100f0750 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 222149802 1250 222148552 222148561
    0x6110903060f0105040e21030a0207060c020c10020102040501170c0903100504020a05040c120e010b040e011b050403030c1506090203070c030e060310170313170c04110a110114 77
    0xb80c001d5040714030440d028804000020394051300c400101c840c00786103c031818807103000030b26050081d585c080c2c2c244e81e0040c00d00a00707444070740c182e80415040c180541c0046540f41c4145c1080c503045401282540000d42c40c01d45400002001e006a01021560403900c1c0701c086141e000b1000d0444402d000010121107842501c128508010281031741e080703100b040075100015050130f2a01600050301019100c440340c90744a9003503013010f012104d401350929541ca00ca0500f81d9582e40c851780341d46a42c1d50703000103000301801100390340d2200c04422040901500303010400c0025401102458866406014a5001402c0c04003500c0a0b115641101c50080e0001c000c04c00c885521400c3e00c04124040d0742c40902050000050099600c001d88007100d0346604081c00340226540780220320310040a14003160b2900350042c0306540c0b41c074000d0700300d030034000d2404141c0520400d04101002ca5490b04a400704110521071b0882d00380d61141200074020b12a2080e1580c400000c2940b1a100b034180c2100c015000d07240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 222151052 1250 222149802 222149821
    0x5040203040203070909241a010302092e09090204050a1a040801090305031e0f31140706050a0219050a0b0f071202090a06201002030601080a090f0611090306 69
    0x4100c0c1d17034021a1061100160070347d68001e04d001e685242d0303603080c1400c0d02c0c0700044010f54401c0b001d06421149420548054208601056408181d40d425100c200c1c03180d09002403994005a00000c9201c0c01404140000e50754440c41d1021035101c00400340c0c40700e0b000c01c6420968021907200d504654038100c1220141a04040218420a0404a150703042030a0b40b4950710009802e84015001100075400600003990303080110000036481d82c5070072442c18a104030b02000e00c966402c12070341e140d001da05020561401300190030162203a42801805c200381c02e0402540c44400da84d0b03814040b80c040c07100e8400e0100c1400b4148109800074865206031030489200c3d88590f8003503c0141c0015403039003141c5094081c51098407405e20006000200311860700904883c0280c0002d10801890054480104225001c1040400180b941c4001580341c4c5041400500349801c0100b548228508101410001412900c440b444540d4440e000007004482c40c44450090300969807915094400c06003880344115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 222152302 1250 222151052 222151073
    0x20307020109050321030a02040e0114040b0922081c0902010e01031802060a050c06091006050105091011010f06030b04050c0402130b16020a031208180705040203040203070909 77
    0x38002e80360220455564010f05907680b0003e074155036031116108100262040d4080116004046c9403409814140c0f91080d0030381d82c0000780e0000b030036501803564030003e0381040c0c000c4800000c02120124a00d03d40208401c520036014240040c56106400b600d504201d01441520002c2c18521010311012820325000f100421082a040e800308072400c080d2142503103c1c0c0103440140c80032501c4104481e034a1341c00d0000d280c1103d0100824400f0511802402000030040f40b03100740e0014005100c25024000c10200301d6000350407544c1004800c200d2155070303031210505800411024503005070888468a501c80c01030218554000c06942064000000c0c050009100790145004106845083e294035003080202d1047c01980101d000342c5000820016481d0b40240481806030010b01400c03900f95400901e8142c402d070002c03a807649811243c1c0030300c558455645075010003450030100ca542c0c114203001e641d6400e944120b0b0300c600c0c2c0000c00a011914140880c1d0000e0400c46820b1006592070300e403040111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 222153552 1250 222152302 222152317
    0x12030903030c0f06110a2a02130908070b1501021506010507060902031e010506030105041112010f050a020414010804080d200a02010606020d0207050609040515151c0b030c0907110d0203 81
    0x1d0702403142c44c6c0050141040401f0f2582c1e10303c039202401d140c658203205030202140c40b2503000e66500c000e0315000c80c02d58401090102e10480052103070345400075130460001c0303801290b41d04650002941d4202c514282420b16041602420002d07242c0c2414600b04000e4500c0a20094050050b00e2145c00031944940900380c58540400c0244071540d96202490300700c5a08980143c410b41c0300ca50461107034145502a0034000b45000d0001c51100c3c865a174001c02e68070195030140d61603500040400140084440008640b6000d02e4204990304140d200c4083c1400b45100c04218035640b88072212540024410310404032081010171510303041c007018060b000741800c0c81040c01501070020b4400381d0f1480842d6800035950001d00540c2009002d00c144001448010800d9012500340c288461345aa82c07031518081c0501454035a80d9102060000c000003803001c0c111040040d814010340c1002581c012482145003281074400611603074800c00c040303400005507202980f440c0550580c015640b503001c0003d1614 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 222154802 1250 222153552 222153557
    0x6130f0c0513061827090305070614190203061c060f18030903030e1c0f0c0f0b0f0c0a0804080606190b1803030405100302040e0112030903030c0f06110a 67
    0x6036503c00041d51004e100010301d1010307644014051040c6140640320311200c40c152030390240881807011055080b143c001500b40c2c0819408102d4608021060003000c1c00d4004442c14050241801020601d680c0500408400515004000106c071b6880e8620f940541c00804100081d940300d40e4140a00108030340600d00340b07142d041c00450308a011450010345092603050b507442c030260740380d0345044448540340e5103400e50041b4082150b144102d03070b882d13002c00b0302401800c0052140b0075500d44584400d005900404101300e0b08441040080700340d00544003814200d031781c02a40d511002d20078504018010700010034400021070f0101c2c49040c0040c04074845c04050764440d110b5002c01d24404858140707840b9035400b02d503042011080103003540451107040440982160300b031586804c0000d24040001c1444000a40d01090030000844216005801880c1c60741c27609641110079240200f885100b40405001c5c080c401c810002045110f203402d40070140c000c00c080148220f592200c903101d600c081580b900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 222156052 1250 222154802 222154837
    0x305100801091a06030c09010303170a20090402070f0c090e0318040c0c080a170a0b060a0c031101020a08011d09062206060b040302031005010501050306130f0c05 71
    0x80c0d200c014480e0000103a0410800002c0a403100e20308101518000c00240c4c05000700d00202005440e0000d90700c2c065446030f19001090801006030300c6008000034840b503405402d01d001c1881e1422520000819442c1703408000342e9a02446000c035000c3d20035400010320756540c580c1203009110803104141c0c161500d4600c02d2280390010002d07180d5a00550000900204400004003006c3c038245e80321000d40d90a070b0a090b403070581c007134032a14025001051102c000c00c84003480c1c05006491045201d44c0142c159208200814481020915a00840c0192003c2c020410002030505015968113804440e03040000d650340c0c103c0202c001c00c00c0100b803040c1c02405030800c45001e106003801280520481c0114000d2006079106594030f003c1c0324a10316000300d8818200c0032138020400754090b0b80d01401c03400c00c009075210714600c14589031500015840f620b43e40381c90010311260303170700c00e00f182e8000b18101d510030020481e000140008000c1d002000d503c0b1031a1141c01400150400040c04850000211008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 222157302 1250 222156052 222156059
    0x92e081510050a05060a0e090f0703321009020a09050a1202090a02031e1005010806010f02061512012409020901080c0f040509193c0b0301020a030510 66
    0x100c985080d8001c2e543e01c541c407000144107130304115000c0c20314000ca616000d10b15050f08004220701d100c05607041012071840104200c496500360180400b110550184610b1440880174140490b107100300c6048200c102840203d01c650220070407480c05010060b8003150340f0307501c00c0070142010708140700d528003528541100041005c80c5082042c2081d8001c1d10500c510b5841803503603002503100402c1010344c4a0036404010025151106540c80307440e20303007050b2029505020016010190040c4441d0402c142d0240c501ca1295020030b1213038216214000c0c9007060311902000600c030075000c2070b049400d9071030804074400f04803540b40e2104150700c0b01c00700c1810710b80c1c032621407905030f01c690150907001c03520000100c0d050075401d00c020440781c13401c0d01d6402d040540b07480003c3c151900c19680311802010003031441e4030401e454410716450704100103141ca41e243d14104810000314003603592880c5030300c02403034602020130b554222102e4284000c2c002c40d580e01c08410040d009040c00d5a0803100b14032010f030040b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 222158552 1250 222157302 222157321
    0x90b0405010308071212020f09030c0603040c03120c06050a0c080606090105040303081005060c030301090e011506111203101d04020a120c0f060e040507090302092e0815 74
    0x41c103998000c88200e24003180760311036800d03046a0045000803c190b448044407000358500c00340030b00c000c102d082c2d10b0352003004504152501040000c0144a41820030601c000503860100e0182202d07480f402409820441710025903103418003040290001b410320b001c20900030102da000618201581d02d0f54605600d5030814820300c0c0c0078425a1501058007048140b010034041e402e0700f5401400100110311031921076020400b203401002065015038400310060000040c280602d183d28005c010080048005081d01008070400300e10403541803103a2894181e00b036503000d2103c02c4030700c00d18040c03d9581c1e00302403461078071202c55442070b0246100d5114004030503440e844441402260000c090b030100905102c02c8082d01c8204183c100c07181d152000000850a0898050900a000545440c118000104240300503201c0003001c01c0d0401c0140d003014001a652150b4590704140105c006c00c00030190400400280340e0364243c5044010029440000d5505d400540301078a0006078941901c9911003414a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 222159802 1250 222158552 222158561
    0xd020d0912141c1112090d0c020307060f020f0703030e011107081c0203130e0417031e0903091503010f0e01060203070f02011b030306031b05010c02040b0d0c0f090b04 73
    0x388940501008802040c0d034110482c42003040d118500041c49094804d0076038080e52100340c0e12600351118204001d1805000c1c0f103200307007a51007410100012a070703960010751503411900854003800348056450708001c0c400c00c070442c42c10f10b90008507000140c89040180040c3d02c0204401d001038401e2000c2c10100c103010070f2000403143d1b0362000700300301402011880b00c124011078408003140710602000480000d00c0d25060000c08030341e0303045c56a9061605014418900418242c201c1080800174042b800b00035020318200c0301c00d45400580180c4801400c9421740c03041c0080781d0ba016042150b42c10f02e40d4030107002141290004400004880d9403203505485a0100f4843d40b4056007003030003084041910003890442c4148145040440d15503280f80c0340102c41e02d03221054000171f075141300600400603d10020180f03041c5101d06003a00c5450309000815070090078000901884d02c400d48042244ca0f03406454400e0344d442401000c03070680b10720308000c1c01701c050f100313251080d424400e1212031400c040c401c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 222161052 1250 222159802 222159827
    0x9010501050103090f0f05150a0507140408060f1008100b031c08130f060606050d0b0303030c1e0c0304080a0510091109100801050a09031101050c0313080d020d0912 72
    0xd2a0b0151781003600d418601c109180780a447c2ca005801c1301d0580403009020030fa215800c190400a85810a940c00800c408c41c019403169454800b08410f105e1544c000801d5944048080c050f0300d01030760b509200f600085840c0e48119140d200e0314504520006150708160301401c000c1d02142c18040001403582c080300c02c11040000800c05c65400714a075016607240b220407960040c001c0d4001d01146544100031a4825801000024800f00b96009030010354001c1d5203103070400320000d50949c140300c0c1420302207202c1c0c8044081c8610005100e40f0220b19048141c1e985800c0e0182520f0725280d8510380d00c0e8866010050448250043c8070103030468000501c550382c01c46422085040c40c800010050018107030014102e190801d41d441400100c3d64000d02415210340d51041011030324030554500034180e41d6090b000c40700903074105410403403000391304002d80b07512000512015650040600300b013000b43c030403d0442c3c106d580c0005464070104080d9000103668600c0350755041c2820848a0007103400801c00f20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 222162302 1250 222161052 222161063
    0x40f020406030510032d02101d0a180b010e030a0803060108240d08120103030504290313080d02030703061503020c060601032003090f0c1905041503060e060901050105010309 76
    0xc0030000c20355240da41c3c1e1646c3d06220024240c0c410711b40000c0d00f8080510f4a4400141c6440660110f00c400301c110352404030780c05d4a034009420b00303003414401d0b42c021101101034143e03614034002c04103a1040c080e05410b11000f401361080e20401d8203041800390300072a1054003150044012401c40d0030388107650014800200601905014440c04101817607e5161041c0c94424043c45034a41000d50030040600840c0310f9101c01e03580398941160310041106160b5803882109614043d5108a29802d0032258080040e500922007013201c0d29080000380960079400b012a031011040244207505540b00105442c50480007441007070041c40214281e06c07900c2d0300e03032405030490f1010416550081e040b2908508140010404c11881e464010005800444008509500c1b2640c1a0042c980501c2a0310708201c06603200081c0c0d0003c4586000300e003003d40720300e0f40210395543c60360405418400c0d688014562141083c03010b044804940782ea07815040c0e481c0d00c0350703500c0c11000142c00d42c02449203012807940a03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 222163552 1250 222162302 222162323
    0x218150a1202090603181c0e191d0702012016020303040803070503090406090606020d081e191b0c0b0907030803070c0c0b130b090f040f02040603051003 67
    0x1000200c41030704520300000c28280d000c1c41182010394418015521807990b1348620566204000c2d00740e4139000600b10403c0941040d0701560703c1050380001d18550751602620525a20b41d06420f01c054400c4460780100700b28142200d8602d44a0304500c04103000b80c007280e009001e11401d0064a005c00465942c24007035410081010306c0e041e21981d50340d46039450004003528100391303a51010504540c0100c40403200c0b034100041b044142c3c03a151061130083c0c02c2001c000c100c502c0c20140082d50301c0090321a29400d21061900289203800701e001000c4c0d4512107003800c1c0c49541003203418018030701d00044000014034142603075080708190340b0340482221000d55540360340510103515103204610026004202a008d03420004c4003091000000794024400f9540702c5070003c5560a101a1081d02074001c84001b180411440c074001d076021b143c00d001d41d840c40800d29501d25080340018200c4007030340740b21038110b410468400200784c1c20b50b020b042225500e40701842150743c1d411810715044101d010003010138000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 222164802 1250 222163552 222163567
    0x106080a090209010f180903081326030105090f07050a05180901062c0f040b012102030a0e070302061207020a0804030b0612060f1803130306021815 65
    0x150109504460308800000703500041e5000709001002c260800e10802c4e900c00303010850117a001c440c90600c100440020042c82e82683e030000c0c4810030252005c4012003a008035041441032001407800014000750220048140c1d05583d2a00c40e042442000e119025030f000280c3c0c00018040d41e240315076140c3d0383e540d03c1c1070550362040d80da9800a00c0344c0070101e000102c07010465100c01070518040d041c00d840d14224141c0705105002c906482d101a02403404002c01100c0a944421007200a818012a008100000f0402c012100d003220600301c003995a80c144802c0761912003d03402980240c507189028022190700d0040c80e5a201740c1c40c400250042400c20983c46014800500348c2e4111a452051741c2c0e0303403040c03501c0f10b031042d80058006031407801e0f00405000765803600000240000c90102c01805a9240845009004480043c00c401c1e0443c48044400d0018400307004035004420000e03034040a0715103c2c01d01c50300075002810600d903150546040d074001031070710044a010a11100106038501782c203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 222166052 1250 222164802 222164807
    0x30f0302070221030d02130503071707290712030f0902060409021b0f010c0f0c03080604050411150304110a0312031515080702070b1608031b07030c1a07080106 70
    0x11000c8100002e004c144442c82a80015000404220311105480744e4450f0600040508040081d0320610007111081801d000003003002c10f00c5001c4400d50311014581c5a00004001f0085120f9603c1e9110741000080b00c03410044090405000d10403544d0301041401c02c811036010031911401c00c080e510030001e0004020301c2016070020080c91445024408040a035080f01c2413803c0280c101120b880d035185d0054041c0c03150310441c58504c0f80315034034010076188030350348000c0c10601d006001c0b680102e444400040030301c00740441c0403420083c00f0f800e92007035014040304d2050541040e18115071100c100e0708010b020345011020501641e811038040c000810380a8010b4004020f145800520051945c100040300d20614000d01250309090300d80310254603195400030f040548603040b0041100050046d0300c0c4041c000c05020f01c02c1307030307000310041e0352a01d40446c210758642c44d0101201480b10005200001c141d8000c9100c410305102c1c0850380b0400c00074102144401c00102e5080e0000b800e0394004005991 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 222167302 1250 222166052 222166099
    0x141906020d02040f0e040605070816050705010b030607050711090108060f0a060503030a03060602010c0c080f0702060f16020a08011103040b070c120905030f03161205160c03030f03020702 82
    0x50702010051809580d9880d50fa01c541659000000e515040c00c04c01c002d101032805880d510000ca4a05500949061403080403261407510110003003100200340c1e003007082400d42c010210440000c0403224a46085440100554003004089410300008a6044000d0610f2814a41039a454102906540c0c1d1021106010003038003d0020b16820748030b4034000f0321602e0a00042014610503940420000d04002000c1d09442c0078504070300812000201c4003011640e901c050310864040c841c941c5664080500011f1510b010b00c659080391854001004140c00c448030a5200c80c5038401e9610030040c81ea1005028202c404c02d10030803000340e000f00b00041c0015260030626034081141e003001c003060401a140e451004100340185000b00e062808140114502000340c1c0985100d520011031601c0c550007105134001035084030080441c00001441c84025000d0300503181c14602c0d1400b64914807496007042b010040325072000740e000c500d8040e20300c0d07100c5100e0300880f08029000382c00c5050149070803c0e07444803034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 222168552 1250 222167302 222167317
    0x20c03030703110f0c060609160f0302130515090301050f100e061f020105100f0302061804060302060d0b01080a02180f040e010903020106030203070503160b0d02040f080a14190602 79
    0x1100c08002c0340c030040c084034001d40045c1c82524006d000c0e82c42c044080c00165480641b40c80c001c0c07060282d4900303803141d2040d11744010b507615107005033303e542d07298140c404c002d01e039030300226070040c085010740c01c3c000f2030741000d80360004c030440007880303191a0065044803d07030007a21400415500c114061002e5142204d440c0d80044001c2c00b002403801d101258802409038072004900141d440714180003001d00d1290210004e8a10700c40030880091559000450511441c140305603141d0031405851050768465000310015600548056641c00c041158030300204045486e00f4041580300d00490462441c510030340f40b9007059000d090b451500c02c03204014085040b00f1020350b1054550140f0790406e8828000c40002c01d109070004a800740c02c5104142c00c021150f0015406644440205900840102e04420850b09069081035603480303569090b002071b1180380c10171108c01d00c0c26640010b00301000201890a00d018400310360743e07080c41d42d1400b0b8641c00461008120322125115010201d000c0350b0041010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 222169802 1250 222168552 222168581
    0x405070b12131e03110d050313030c0c080a030c060606050403020a06050304050c040e01020a080c1213080d060b0a0e0103060b03070311090a0b040518040c0308070615141201020c03030703 82
    0x1080083c1800c00ba000c0800b0f5003c40000b0b1504034040342d44082009103984003002c0c0d04000381546011201c0c0b28202a09040190800030782804010134882c1410041000d40100b03c140e800100c014280900b400d039181c442201c155103005000981c20384101d050314103807640145005c01c01c900d010b40849480e040030748255001e000d2140b080ca0b085c0d0740c502c03840e000030300000005600c1e417151420240c0800c1c00101501c040d41001c011a01d004492185100d904c004036601504070f104150400942d00d0041081242e60b0318035204001c01d8070030481d00a0095002075940c8c0204540300d0307000443c15100307a44900c280c1e9143c00d0000c104010300076000b0544000b0700d0440c060078500300344001405410298002d85030404009000e012034100040c07e56003071031100300d05036020308169036041b90407509071102808a10340030802d0780070070031640c10202014140d0055040810b440d440b42a142216005600d403090701c6046003c440180103000b5620705003041d601840c11951081070035000307442459401c010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 222171052 1250 222169802 222169823
    0x7030903020f1c020708030301050f090403210203040b060f010207060f0c081209070506040e010e070e120c0a0602070315050402060405100914040e060406150807030b0405070b1213 79
    0x10004810024480d0b0840030404550200441080107414421160041c11b4590010801448284c90710190113501c0641038403e40401e03580e5040841d81c03000b00024a000c210740d0010351241c0781c041500554080c90040001b003480c2e498903001c00c041c00824804141c00340e00602c8003000f2050240495841003c00388c00d000740c420a02d40d0780e0b803560781c2c000c0c2203184841c0d054600b071007108041002400d001e00b00640d01103140909061500c2c0d80007105103e00c4640500480001d600d20b0b1140c40c042d941014003502903401708000f0b00b1040c0e110b1446035109070041c1060000004e41610028481046a401079101c010710315082001e071000e0400248141c1e049041000300150644a1101c0e60300c2c0d824551fa0f032098494148001001e820001c2d0a0383c522076402c104454234541070118035207403c80d0388098001070034103550342d01c80c80c41104c66201e040d09014450700042800340441034148107034401c1c42070b510100d456016042d10303800f888440a000b0300500d4002080302c06180d1040d0070183c0a54007468 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 222172302 1250 222171052 222171073
    0xa06060c0323040b041a13030602030703020409060902090117060609091308071b06051305010513090606091d0403020a0816120c060c0207030503030a020f1902160f0506030703090302 80
    0x8050343c01940005090040068100001d54401e4000044c401c0200d0300b662903c01c14900300c50182e159808050320855001021808070390003541150020f010040d41804019500c02c1220025002041d0307880c04505e00078040c04420746e07080300d40c512403200209100e0a213a00a0140070071410014085464a0582c0c00814007042000000d440c5403813207130090641841c00100c81c40803050160f84104180642800714800c45091300003104180e030401c0c40c040b5190031400903545075800450307000c0752880e45071110100d141030340611040c003902d08104044100c43c024035500c034000c1804580280041c0c101c0d003180340020b02d6100040280144914401c00c83c030080792111900000706103a1f040200300f007405800b0800040b070280a4146100e030002d0520b10785981c0780e40303480e444020804510117a00003104a007145d115025100a9160341c05549000329941d00040e58131030310001013400c00d40701c4180010307403118000408400e942000d8051400c580b58290140d02030040341104030700b513000c1d600454 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 222173552 1250 222172302 222172367
    0xc050307060603051b0306010317070f08130b27060c10050711030a0e040b010309050604050304030209091b04150510020d08070201020f04050f010215040b06090a06060c03 75
    0x1040154010440010001c3ca10315040c2c0c41c02c1038584001090450b103a9884490390f4000c00c0040c1129004885188104030030141e0700480d118000c030081c200441c3c040c5103030a2040a101400583c10019010b0b4162a210084c5d001c3e680220498001c0c44110322250021a41ca00720141e0074409010340f00c00e05025110214504040210521002160f40c407803c02400a5000d04540f80724030b14803001d5803916a144800030102040248154000c90700d6160355a1b041e4031075030040c14420307000403ea40540c106440c3c950345079031103448107900c10110503001c1903000a0102d51050170441c0540e0140304011104103210180c25039401e4000b0200ca1840009120744464020008001c1c1540c054601c440d0740c0340b8044c0070000090303d41c038210380c4144443c203007082c0324108946c2079403001c80e20003001c250801d0040346070507501c80e003000500c40942c0134402040207500682d40075034001c031044a0340da9a900e0201c011904d26108000000310788019010201c1e002d0058641c10302c00341c4110321000101000035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 222174802 1250 222173552 222173557
    0xc0e0f061e0d0209180603100903050f0f0c10020406020a1101120609050a15060906111c0c03090501020c060406080402120f03091309080319020d050109060806062b030c0503 76
    0x4070702e02c150005101002d80c58009417100c1301030014092072910b0300740b00c1c010955450014a07031a03400c40e139900320f10b428140604161031584100386581b6540e80c611662002903504030140191f082d100e01190001c0700c482034001d5800790351103580108401c2805840c1d60b2404500c140039503040c00f80d082c1d20440184090302941d03000c4c00c2e0040c000314990400c11880000c54074a400b21006a06030190140b1440b03034880d043d07104441c3c081c5441d03248220040720503820404402103807201030071190180501250010070141e000b41c001d4464802c0141d0b11801640c075410400d461a40c0074900308014003041d4010f0100c550028009800e900d00c032010f0860310741c03901218107210a02588081840c9105107007143c5524002c0a620b1000d00500045940c0c3c61b1190002510540311000c50b1051501c00c1d9200d58151050441031440074802c0b03580d0340d140307030004049600402040d80500000142141011400d048100403803900d580e91030a0744242c5010560714045081f001c20207070030041800304104201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 222176052 1250 222174802 222174817
    0x50a1703031f0906061e030603050309060c0102130e04030809012a021014100f15050306010203121302090a0b090106030b03030c150108010e06010e040b061807080403030c0e0f061e 79
    0x413164000101a80048102c4002d000605c1c10542441c8c0c05200240010041c2c82040030b00b5222181c40e00f018440090180c000c0c2420f9002c6807441d041d0000c1c1881c0300d035030614012402900da400541d210340c001e2720300b45c460414422521011022200c0c0b24641d0340b02c8020340040040c81a1001c807512803c0d2035003600c41d43d503070034842403440c0018010001214200e0700000c01820803860021403070801181600040c2129440034090040005503081c0d00a01c1200ca0341400012000924605080c2215014594541c16409514a80001009085140300f0040d41201c001c01c0c1c424141e03e00003003100078100f05100b06801d800248810603203200204030290030145c050001420b40d43c10206401d08541150382e0b082602e5020500400c80d45408072100f90b081900000a01e42c0c41c2ea0308008101c0c0590544081d0003141110360401805d55440074182d400b8502c242c2d0144101d201c203880032100d000c4042112a404455084014080d181c032030018010409503801901c085842800d498106030040007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 222177302 1250 222176052 222176057
    0xe031815040b18040f0e060c0306011e0c060f0c1d0a08160816050a0b130b0403060e0c0919091403190314070507080a02011b09050a1703031f090606 65
    0xf045603450f4034103800b84209804907a2010000d00801e8444036945180181c040340740c000001005c201c8a174450040d00065031002c144240c804100090000c001c0314180c4000e41d00c0714581a45049801203d000d64541e182e0165918400190346800124070303030352190700281e4030070380750f01c000118560305002c3d0401400c4003002100c0c04601d80060300303052001d0303a650761b201141030b100c062101d540c42c0004207043d40d82c0852180c1d00e1396550a00e03484440e400342c00c000010705001c14000200302203030308110407861000d801d031040f0040500030311218900a032403100700da6240e110b40d00d986034503035070103030451b28001c04003012a6101000481d003194040550385104408560f400e11a140d0140110b01a03d102e1400441061811440007400e501031070800400f8010b00003103004001c2c0c03007500301c2401030ac0103c0340b402026403052000342c51a2590f12520b0300070600c42100040d070f0f10340b06211401c000801d802452031a90780303018078100c449070014142002c0740d4426000c90407007a02c2c8a03000103800c1c00c1c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 222178552 1250 222177302 222177337
    0x60711070b0f031303050904020d062c060d03020c04053309070c05030c01060e0604140103050a030f02150c0a03050c16060c0909050405010501090e031815040b 70
    0x15981508012198210300c0c06100104000c4154800100850742c0c000300ca088000064080d03490101c480344141c08000d03a000e8000b05180f41160b0055000781c00322050382c1142110300103540c01013460a030401400d90780d6560210001000e40c144004030310070091081c81582c1c5c0e01a410740004027200c80c1074800d001c3c030028a06900707a84000910072031040b9003030920260801c0d00d400000802d641070040a81040185e407403007035810800f04000343c5100e600704100a00119803100040c100d102000c907107041c815410710003100c20002008072041d05803908400604201c50480c0c0302074448807401b00030303201144914518002e42e418012062030044007060074440d03645c0e21040300181510030141c404108042e04101c280440c024a000ca50b05480d4091008286036501860550b01c00c0c009911500d4402c1c2060700704030400134198480f505842c1810010007480342a824030030740e280a00e40841d0110072108004a04c945004070600304440080003000d85020780790071004031180c000c0e4145030b9039110355 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 222179802 1250 222178552 222178577
    0xa1706040b09073204090c05120106050f0c011a030c0d0f060b030313060c06050a0b06030609071b050703050d02120d050603070b0705030c0c010809120309010f0c0206100f050609210607 81
    0x30780c01120f0340c0d0f00d03040c41c0140c100319080d41c500d827042c0c031306100350710a2040005101400341d95400035180000076100003003000c905548010140c82c40c4201d034051282c00b42106604851800c10060080c6d99080054a0340008a6035200c10007886002c03400c40c0e1511007072060100d04042162890003a00310340c0d560407001012860007030700750b0300d019181c0310005051640880158681d80c0599601c468112a00f80d1161074a410a8a0b0700b01c042c0d404842e01206085090184580007600200300d81c49403013150200304c0c8007441240c41c1c1100d02182c51400b41e04000e110110600c61700807940040c00102a1904280d80314011700e000c0c2d002d40c00c101c0b0542c00103e0044a110b05c10320440020b10801e0030019260b29080c0010f60301c480d92122951407402004c00400c2144000f588550b8100104000810140d5000140079503114401c031154103100805080c08114080049980421180080e186504150101c401c0156490300d492402c00440300d900103034094591300704211801140103440d602c98034142c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 222181052 1250 222179802 222179819
    0xf08070b0c04231f0f090e010806040f05070b0a09050f0d02010f1d030a03030207140703230c0d150b09060d0308040f06020a1706040b09073204 63
    0x801403540c0340701c0106010800220411907441c0400d0625142084412414580018044a09406168580c500100f125044182c00c519101206880e5072520b41ea51680e4100840702c0740400d004454080e0400c1000c0380010b8105080071002c24425010741d150152141c40600c182c1e0046541100040d0700c1d41c0b00bc0009003800e140340501c40b04c007662206180e541640000c0d0102d244a009513080202c42041c0325012990408a03100380d6034024240c1d0070b102c2103401c0007406504820b400380d0f0700401101d00e42401d150b0019120045941c03044101d12580019503580400580300c01214074140101140303031181d43e444915030501540300b5900c0710400009040e000b811102440c1c051030161010780140110ba599180d0015a1540c1c5840d00d40840da03164589801c00300b01d038820080c84c40f070020409008880c1c010b000c50310550310101d02d0528903039610741040107480700f81180c0e6400403902000b0450442c0304501207500e030884040c0d6100d0500d426030420b03100350a401c504a15458001c1400d000c0d042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 222182302 1250 222181052 222181073
    0x150106110609070303180801090b101514030c040b0304060c0e04060b0f0c0717030903120a0c060518030c010f0f06050a1211120a050f01060602030d090507030f0807 72
    0x2180c140080c0300500e80110025910b021601014050024009005444891078542000030b000248001e101642c070381e00d0b005003181002d43c1c2240b0007000341d1a0210b1028828604029070725115039a5030a240d45000c40012290b0001d022800480010007012072980000002907004a1081c10009140304007044010b0180c140c1030310940c46a42441c604000c82c00b03190090319110366a40d015241d4801d01070303020300c0c6000007a5020421200c0e01200c1d01c0c000b08000300141402941c1a0241c5401c0c89046898400a104d00d88140300481c4000c01c40c50701003441c0da80b140e90b0040b8040400c1c503c65211140141c6150807030304c80800244e45905c95007211124030b0103111500d40401a045c40017a04000c0050194000c0d0b010b4000325525400c0c400c014441e6420184441d8030020b09190212001c440000d5100e000101050741c052248801390041d0040500c9540c1c1152480c0c0d01844c20000d104120002408980c601620746104400c00440032840005c031005c0c816100d1040e059a40030380d03103066032006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 222183552 1250 222182302 222182327
    0x60a0807060c0201210c0801090b01030507140304020f0a0f0305010b1507031101060906030f031e0806010315080f0322030515040204090507140315040f0803040311150106 75
    0x6800c8520200301541d001601c904000d83c0c2420185034045115507000541944044034410b5a801c1203103084040350040041416034241c14018040312260500650644d00141c4100c000514010128007a05030210091a00a44001c0071200e003640d6500020f502c41000f90083c0c00e209d28120410020031009104004111106944403091200c140690008030701a0140c083c0900030301030043c680c00c010a5001101074034100e101000308a13242d04203040140c406060031008100300d02490f005248100501c400e60f0710f016950100140e9070a001113006d0141d8070740c102c405198681c408103400900b80200c40710074601c10b00541d203400030310722074220400d149002c825162a0758241800800c03400b081070395002001e07001c0c52059441c1d42c408038000344a40c00024111703014105004c1100344440100c103104070001c400b111080f2000ca00c008101081c26a0000c003010440345806000442c40c00c00703194054024103040c1101203070300c00460300304414104e42d0f503c007440020050040c180c005400360001e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 222184802 1250 222183552 222183569
    0x60904052508100302120708010216030f03050609061002010f0f091a0c0706020a140c070911120612010b060d060618080309010c0c0f09050114060a020d0507030203071a060a 76
    0x29800e180c00fa8080d10380740c902000c1d0080b01ca106140c1e604120410600d0010716400008550340e5100b44110880c880c40c000048001800a0450745d6610307200340100b46c01b528000b02018103d844840401110a0600c2001020765491384a2065400c07054400d030b44420705050b2021409030300c240340402c0b8013901014a0180035420000f4015000c800c042500c80c4107038400c40c016612400590281c91300f5040c2104504c100320300181c030140203200416100304840e03503154144030301040c0d10780400c1d25018020790751502c80400c03400250285410b03d40c444070903020b403000040072030101003c02c41c00d80c8211402050b607602d40c031081141d10343c4046c441c80780004007114958100e0508050384d450b44598000141041540c1610405101240141000034014080000a0b2540d40e4a02c10080c210074403490000482882c005800360901c0c0d011603c6920f072981c00b234840780725048019034064110320710980452006101c0b0348000340c00c000c1540700c96030b031101840410f031034041e00b00700d4141c103a5000b4914 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 222186052 1250 222184802 222184817
    0xf0b040617031204020102150405011401090b0d0f17030903070c0618120c08030a0207230f060f16080c0105070306080d05090121020912030414040b0609040525 70
    0x40d440040180d6022150030074101c0065101c4c0e00040346010080c403241ea0340341e8a45000d100c10808150f03c03000c095031000b10101c845a80c0c64103540308607620407030180c1d040844a000c0100080c00c012115440502c5040c01786450300040030140c00a0300708413241c02c00c0fa400006c0a6041c819002d40740c4000385454070705081c0c140c5c140c0710000f90030b144600c10740c00c0802d11804201e0411440b25841c5010703042000460391030382100003000b540ca00d0b062003000c3e02c01e000e0b4081c400c10402070811840300c1c11005080b1028180e82c920511101d03602c01c45071140011401d1000c282c1007000450304068060150110035214104a1b0140342141d0018140100f0b05203809402c000d0744501040c5880a0300040c2402da858030344950040e500c55229010f07102251410303440c0d07602c0260f071a90240844e984260340109a164101000b0740c2d991240340943d0302e80c1ca000b42807070386244c0707025080014071940152411381003034130500214044e50360643d07001c417030441c070781400c121200d5070481c502c64070481500c1c0020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 222187302 1250 222186052 222186089
    0x306130201120b01020f010f020a091a03010b0306060c03040803070c23060c100905061501050310051507081207030b0406050603010504020f22060f030b220b040f0b0406 74
    0x3480d4940c1c42c10703079800b0b01c0e40b10709004080ba8024004110580c4041c0000c1c40080c0c0070300c1201c0c0080d44540c0c501400706510880106040c0740c0b00341c803001c410711040c48251440c2d003040424200e40c1c2005103007a0740705008200141c0c0340a03040c4058801080389c41d0046850305528034003820711003080e401c030503401066008011075031298442d40c03981102d41903580c1e550f85c0500202c22401d01c480d080ea4006414142a421000c00c000054054400c13a401c20b1540d450024440044403103201c15100c1040d006503541040c0824504000386144003461004043c0c40c003410340e9070ba0001034100d580f09a104203c2d0b00c08000d225905405505200d031022202000440e081c007001a0990206028442c003171940402c1e40035403960b5181c1200d0040d150b00c20800204000c042c002e509d60801401142c00160440080c2c5659600034050001e00c40c60041001400c0c19003d0001000090240343e0a151551a9070368004035071038501c0f4081e5026000e8201048008104061105546490b4000305000b03000c418042c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 222188552 1250 222187302 222187307
    0x32030d06090b130b0126160e0604031b051305060109060509100c020d021c05010e190b043002070509070f110705040501090e060703060b0d0c090803070507050306130201 74
    0xb00d05000708000511203140304012190714003407140140868516012207a000c01b801103000d41b061812210300040c140c20800101c503100d07296040c40350008000e1100f40005010305c00009240040c0d013130001c0b9800d0f992000550020f0303c1e1500760041c5680e0340240803003540c0c000403000c00380c0924104035241c50021400704100404d00802842004140700354001103549840b0342d407180980007020300e25900c10200034500c8646000cac5040320039620b0a60042e12540b00030542c0c0d81910740d03144040881c5011070b140e0402c0e441d4001c0044448803120102c1000780e441c0085a01c61b201d01543c41d00c00c04d100c02080183c034245140d048540300b600d03282e08004185901540e000c1004485207080350304010390920039840e04015421641d48141848000b00d42c40c51982e00c12070002480c4ca04444154075240b0017941107950b14020314011440400600c0300220321900418088030303107880c0c03500001d56507c6040381960400e0350101e403140c03c4204100000e10302000800e07042000340410b1495030810b0b0303002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 222189802 1250 222188552 222188569
    0x160602031b01020d0c0816031503030302030606090301060603050907080a081801111236040b0d02150a02070605190c03030608150906090d0c32030d06090b 68
    0x141120150042201c0c038248001e4050310315070340100b40280200b02c0394100c05421008200d912841c820320802004000621038041c290f20017500700c0ca0502d40e1421510210044d510080889804c05d000300101070607604e0900c0344000410742035400250381e080c2105070074113011240c1d0040e40303c0d5203e5000e074404610f2410403119031410130448030034000100c10040c0c0d920f40141c01d0703100740c41c0203542d01000401c218600410020306002c076603105200100840412b5141d6150307111810203054841c036103003800c01d9846071032070000050031481da40405600090f0401020002d10b8041310340401d401c104c80c1c0c2c04003c000090301c001d0803c0d905110f00030011040d04502981c00c54104030100f03074824145402640442c01501c010010344000f80030303ea0f10410401d5050365448414410fa00002d1100030001c504060401e10b180d031012450f94a689a442100c0d1100c007800616811003540c40e520184010300001014000c24003464540c108844c189040b2400b030350208165a0900c050000d055450010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 222191052 1250 222189802 222189817
    0xd05090409020102070f06021b010906080f0403030e0307080909060612040b0406020d020f0318120d050402030304120506090f0106060c06240b09040509030406080c0a020a050d030e16060203 83
    0x180061010807500040b49400c0d080c2c1d00c520551078000d540424140c1d8003084a02c0b80031400c1c0700200c0c0340703103400d001114001d8241c4114400101642d0200d9552400b03455903580042c0245404910000342c0d0141506540c05840119841c1700c00140028103070406118042c2d008070200d030b0301c0381030901200030702c0301c8140020300040041a1000018040080c1581075500c0c42c50400002c648941041280310055070050b1440007214a0b14240d91400d0100050b594080f00144c04003142010030f4250508050301c40a801264076010a000105141e8000d0b14140c8076140100014403450910311861420300c902c070074403000640d04100e8140001500040004007607075101c28001070520090360f0001d089402c1304181a602540780e14005480d000803005484090000c840400550300c6440d61296244218030507500400d9050000401da02110720242c9003c4c0c046006455000c1d204d80d440314140300d092030050010ac0e40c1c400030480c42040410483c0c10008640013044040c60401c480030f540c13400f4614 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 222192302 1250 222191052 222191059
    0x105090405030715090807110117090c010c110301020a052104050a120201020d050c0307090f080a021216060c0b07081306050a1107060c17040305040302060a14070b0412020d0509 78
    0x4502c941000300303580517408054101e4101d541320350441c5041c071051010359081d1070010b500b42c05034044202c02084003500680c001d80c010314021041400542d03605041500650f0000c40540d01e002040d1002c0c001082c0c40d40a07542c500303660b8440c101301000d4840724844000038441508041000145002502842003904100c2e400340900c890ba90880c00fa00c00e1607440c0d045103090405001080018401550140005850360629079407251507542c8213800da4411140e0950080030b500015082007440d41500c158910700303860200340110701410600c0d00075030111300015800006802800b0641080d540c10450501c1c005180c0e041c040d414441d080010350000d4146561200402e00030041c56104903195078801c0344070360b1100042c0c10080c0042c081800104d0205240b401e1031101450000510740c8a51303816141d035800d10341181c092018540200031f040050009402468012400450180141510811042c04d091a0500e00804180030041f00807007994001c403180142c0e1500102034850118068 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 222193552 1250 222192302 222192323
    0x20c060306041e0b0102190b2d13020307140f090c0d0903080906010e0105060f21010b07030e010509060f07060204050603070f03061d1611070b04030b01050904050307 73
    0x18400a002800718038003001600c039048843c96120001a040740d00204426000d64100031049000c5d5000c210325400f0003040303034213602c00045501515140c014401e090010003641842c00c030741c1427210748800a880340e4108901c000b40c3d41086140030400c100280110039490180d40c400f140206190075241e4500b18454101c140000307480d50b104c2400d880700c1c00d60810342406540e505007406005030740c0c151000401405600008a000900311003c00d048a8000d0b0000e490318840d050400316a401005a62650641458110300c0c8034511000c510702030001c1120440d503680d00351401034480400039101c9418040244144551580c5580c02d0b00c081d4107918801540d1408240760850091103980c00a5a12030004010312112030790003003062901e4034a0f41c070b0420030162160203501e0386480c64074640140a80e00000102c071049021111303400c10240d810034100e10900d40b407285003061300b690008400740320085000c105005040c9a12401000701350703801082410143c542036124414802e01914400d01c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 222194802 1250 222193552 222193561
    0x80c041407030207060b13200304050a140f0115060f020606011b021207060e090903041a0c0a020d06050702070f03120503040c0f09020d0f02030601090611030d0f0f0e030a020c0603 79
    0x12034204250291001f09915041ca0380d03440c003e00248105c44038420303001c01d601e039485c5280c15440100d901482e0008001d2400d10b201c0d0781c441c1c048400c1c0e45e014207110300900406980c40e61007402460495501800c000640358289030001340320310380d001440c208660220081c441581d0b00203404440307a00131740220024402582c008180300d00c40640c0550349508c542c0341c000480c5a40001c1c0612202c8081765540c1803030f01c0c1c1d694002c1c1e403802280600d00d00103001d2512000784508200081180d4180b24042da0602100d9800003481e20202c070100f92041b44d2204108002c0545c10702c80c1e040036101c40691030303480c1411074031102c483f43c01503440f0800380240000270506202845519a004000b21b00b804400c2030f4440403400041d41188034079000e924141204550401268001d49200d80c006039a6843d0040c070b81035045884404540ca000e0711030008029002c070840c464040c104461511420210305882c180c0b0811042792010004010650420305c070f0349480580c003080702149c0701412204503032251107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 222196052 1250 222194802 222194813
    0xc15020303101e2304061505030c16060e0a0b10030803040f0311030307020a0b0105010318120519020f0d0507150c0203042711090d030311070507030c080c041407030207 74
    0x1035004600709000d0104a101d80343c1444c261034071030110540c1c042c040243e80d03149029141e0301d9440580003141c41440069403016140015104114886a500600c80c0480d00d5050440e000030000b648603400c4000d80009110f600c023503c41d004140281d082006a00e161602c50090101410081008801d00a54410b1500c100a00c0c0c04016a400c141ca90f00e06101c0d40103581e40c4003540080340e410064100004030307907010744545a034886c403a031410341414903180d84140403001000b002e44103100d01481800025502440c1d0b0003800030058000701049101d641c41580703007400403c40c1e5802c010042110400041d81c2012000c207499a05d4400302e4001c0010070180e0540c0199084890780801c86444405031000e10311025080e02d242c64000c100070844c255125520b032040c40c01c082c0c0c10240804e54040028460b074002032900a40d0321055082c604d03070b43d9a13a420719403964801e5a16502d0440b082c411001c00344402d000e4510300b01e50800c040d455000f445d81507900b00800110515030b0214025045c80b9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 222197302 1250 222196052 222196109
    0x150e030c09010e0117010b090a0e011e090b160c0f050c15071124070203030409020c0106060809010b100c03022b0f0315050607030504120c1502030310 66
    0x2007807000c0541c2c507841c4103400640d0910600b185803c444104609480d018440c507001c9450180140203207035941e0920740054840408503000342d40da03c800703034070406044030400c1c1440b031040c042c081000c4c80c590400100b005c0f000b524a19910001c800c0d001d040ca50401864801154855048648440d103030400508001c140940103801c0641006603940300d8000c8001003e06a10496032a0317008041402848170b6002c100d05581d0b2018554010340e400402c0d6440a800814402400c9a19190300c44400300c082c3e13080307052220780607910f940e000d001003500100e01c02d1b440340f504002000b5200f4080c0002d4804081100c0340d0040c44508010130062503c01d00601040e841c40c011100032007180d001000401114030350710000000c2c0d01600e5090260320901034010750000e16511095020300f800c0403c5100c0c2d206040490600034100000501c03800510f503081802800b404808134958540940d001480c0001d0b8080380440d08100100804000403e00c01c50540f00c0308120012000015565840c1c0c0340c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 222198552 1250 222197302 222197323
    0x60c0507150f031a0f122a01080702061509071407030c12050a1e0c050f0a1a060907030905010b041401080706030e10050601090504090f0b10150e03 65
    0x280000d41c0c000c054030740118a80c4481d1107142e030100101d0040d018110440c0c44030300e15407036014100509074031040c43d007111004021030610082c0c0d40703502c0303544032103400a40102c4101400c2000d0f9048030364043d0b80000441d071340104113002401452808105e0250036840b03c0100d80d01c00e011500214044902c04c4860042500c1024403169898045c4d040c00760100d04204c0c1d08a6400d03845110030042144907a058401a10103070b00c0c0c2c4a24241d00d00c0a02c1580c120407001e0300c04000d51080c10b440861000c01c0707810480a2180040c003070140031820141121004174100740c007c030084c00c0900826840d0030300001d40c032120318600007d4071140f40ca0440d001d000c44144055000341048030041400200d400c486040721252170417141e4280c0c1d01e070b10540c141d98001c40721440c103810801a4801c003900f1030700426807000d0140f4000640355150b000103400c6400c04442900c081c1106900d030340412800303254560300100d1104082c0344861402e1558602026000b0b400d10401000e0520b0103441e03101000380c111078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 222199802 1250 222198552 222198569
    0xd091505010306150504020f0a050c0a05060c03100f0308073e09060d020306040f21050301140f100e0a090509010902100306080703030503181b03010b0f0604060c0507 73
    0x1d5940b41840005407199007400e0001da20076800015840c40c0034400c89804205c0c036031040e070074046440030603105a04480c0501d603035801503001c04070001e842444003c1c0300d201f40c450095103a05000e9800d01a00855401c54000d61401240030f00c0030030b030305800756120700380d02c200c510f0710407009412411070032040070400000f49090020700414071850080494902c0d80103403191074041c0c0d60b410030000d406103042806900b540007040410080740c400380da003d0440740501c48181822a25410768117007660181140c0740001c00100040c0104402281d0920842000f1101c4880702c1b6015070015884051005803070701849102002c0d0031041c0c89481c8268010641a20708111a10304081594042c046039801244640241c400b034401e442e01920844e030540e214900204100c0e03045581c140c803107610103050389458031303504907000300c803204100302c2904441ea04003c101c8400400b10b06040c00d5403419515688600e400c180c03148425100e00c029101114010302c1c25142400f46801d001d0305194060f0006101d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 222201052 1250 222199802 222199811
    0x30f030c12070e0f03010b0a03060509190b070905100807081b07060905070501170601030c030f0c0201060e07110606060d0b061201050118051807020c030f10060801060b0d0915 77
    0x1406400445404a01c40f0946200c20403c00700e0040500b00c40041103400e0b4001200e00040c8081543d80e40a680e0040c103c41c00ca564541c5001034001030702401e008226400c0c1184420000c25030350200c1c2c400014081502e0b080c100e4000841302400003c8000c080714100702c400e40010303800d00c0a140c401d08102c200c3e0b1201d16030350900780c2410307400f4150000c0f0681d414440d2400006095208604080344001034051544450303c0d0346004601800d1030503106410540c94081081c0041400d11030005917010135000028500c0c03070301c400341c004210024403001c18460b01d15482c0291a5020070030561241c030480e03843da601d00f8084d64280c0103004040710150401000700305c0300221400b03130040030306840c0242c0750400154102c855649092949000705038101c0301c5104c41c4500d001103000c0d8250000840d0050310185181000800d282c50502d190403146948428070b06504800d80b441140082e10200b0008e100090600b00e05400c81d2080041e0200c0261b52820003c00780074a80441481e8007103004010310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 222202302 1250 222201052 222201061
    0xf021c03090906080303190504020a030b01150801081612080c01020a1809091707020f030610030209160f0f1205100503010e070501080c0906041a1902010905030f030c12 74
    0x145a003440d4060100b1851820301d000c41c07440c0002054038807071000c08055006056100da0884044c00000c1d2040340c00401c120f0020000500c01301100d4081d200c811400341f03c0441c8600c00602028042e0b0000750541c01501d801c001440002503502c00fa42e00e040c80f081007011491800c04458800d44074440b055501c0410000744041c4e0101e1264804051420280e0800b505d441c00b00040b00d64823180107200e16103d454804800c070000707001d03044060000300b01d010548402d0001c02d0805200f155034500f17144410005000314076103034a80f50b070008104c0701c1e401e0b0383e40c84040010703098070b0003d400842481500c10031880c14610a05e0214503180c5071080500007402c0c403c0c41300c15030041c0760081c18802d509040900f810807100007040300403600d0503556942c445c5c503841025035071a440b00c1e1440350000000c020102c0c0c14080024488040026004c0c5180c5c0d1780e5031082c04007003089440343d0600440e4107282501c40481c1000068900c5d828031403580c5c0e03035a0340781c4c0d0350703240308503c10320300748052101d008030800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 222203552 1250 222202302 222202307
    0x30b040501140108240703022106010311030609070c0f050106030302070e0105060a1d06040902030405070303140f0a0e010309061508061b0d0b03070e0c040503280f021c03 75
    0x42c141d014030022100250b40caa090850310307090a1300d0040501e500781007030f90020b0a024142c15403c8110350800500d4001011161410b80c80c2001c109480e2281071020700415507418403401450f020000c01e502e042d4100a400a00e2010000d44181c04100c22803801c03c040c024809100b441c44d41d0312030000c0000c1c82c1c0e0780c90040d440d14650b00c11303038204e40700c0d02000244505100003100c0078404655070302000d15140401c000b0390401205100c680109003440007041c0320903d840114020383c020381c024441a45107240042500381101048003000c07005025685040512a0a5038080507150070090340d81504540100d0050485100c05080542440d00c1c4009a01c0e003000002e084d1116402940c20701d640c0c6c9009500e0110070103440c001c070700c5800c010102d8419640c0c0d0060155036002002d07540c1d1955140300c0d01c82d4138102541d0f00901d20700c00140801c5549010070905120128801959050701c41c01c80f40b00c00c140904c0d40c1c01030f01c2010400d5036030046603911840300709550801a03c95080b1a550f0500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 222204802 1250 222203552 222203561
    0x50a0b0a121a13020415120312050a093804061e0b01021f02070b0115020c04110a03020d0902060a0c060b120a030c1e03050d0f050c0301120c030b040501 67
    0x10b99070345180030314252080c1c501007071840c4540d00d1003c040c1008425603007808010300c0f607a950303001054103003400030890a43d0204080c6e4a18003035030f20800e403034a105401000719140984507918261a01da451000550005c40050071810004809080c5040c00c0084440c542241800c00008448220401040090540c0500c110400411100c0d208980c181c41714022104200c0d00a0f0159101d1454102150000d550800301d02030008805400c00c00d55690b89281907500f82c01c0350701200381c041101c80443d54100070942901d00112418410720043c210f0522107031244581b0a0308040d0002840207510386646c110081d25a1301405050340c0c0c0a010700d004184400040b02110500d04024403d4120724050040000907080399001d4082d2800c2a90159460000c00c00120780d00c00c12102c00c01842c00c4003040e5085090b0207a21125591448640084122004580d00b507001c6450309003404001080340017964107440007440000c0d60f4500034181300794810044d81c001460305451380300704020458103412 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 222206052 1250 222204802 222204839
    0x70803070e010903051207050a02040504050c120d0504090c03020c0a03080a0609020717070311070311090a0c140a18030c03021002030c19020d021c110301021309050a0b0a 75
    0x6800c0032844a0000450f08020548006030440e4000711040756201c3d034a00043c0400c500c15021916407000341e9001c6000e5600c211000c0d00e943c0c011201c01411801c0074480c407034409007480040c0c001c640c0e032418040c1a40c00703640903010029642c4c00c400c65000b4001c0d4100d400005168003110341d219030724a801841030710202e5000d00e5007410301340002007041e03143c02503605182e4089101360300a02c03c0c24544c1186e400281d13040c0c08000c03c802c00503019440c10300080b0042d50041c001c101c4400c0f4a0414001188009040c00d54020b00c0d00303108001c225030086d0b018840b41003c03040c590351181e40c16421680d42c909a0008002450440d00020410542e03909003000c89100385c1c1c00130783e190303021075003662a070003901618105c40d005130b0a000040e50b80465075598191000345040c03400c2c42c0e160041584113012010a03901803d65854000921010305560301280104030000d42c5440400024014118024406d00d2a45a103d074003180f540c295175001034066190280ca4000301c1c44e40d9031000903603c5000d15 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 222207302 1250 222206052 222206057
    0x302040f0b150901050304020d03090f0801050702160302090f06130c110106050301020408030406050d090807030e03010615020a020d061107050715020d050301290a050a0905060c1c020102040b07080307 88
    0x34201c102d00d0003541c1590788030401616550b046645a80038448100c01070b00341142041800e80d0086147d014400c01600074010300400000d1514205201034901807048d00008001d40504100f0030059854107911035020340001080c00f05604c55201142c81400c0105064200c0c90400700341155255200001c6902122440c0092106030f1f03403441418201e2107940a078100c40d402c10401404210701030002000a1f603070000000402841355100c07000b840d0005030084000035061030b00480c4c0e6180034040c072400381682d034036425011785610300041d540e90100d9200a000d044107140710030070b101880d8099220400b0380040d20b540c0c0e442038a031503074484015004000780d500c92001282e100c070340300041503c102d85040d211140703140d08010540740641903000d0030702407135501c03859520b41004440003c1d00003000300703071035854650260300385c082d00144264120600400c03003400004c802000008005002c0740c61841140d180b00a6101e080340a4030443d040030001d00400101401000303801001103101d03000072b5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 222208552 1250 222207302 222207319
    0x14030c1b04060303080117030f1c0e0f071707081c0809030f0703110a020a140a061d060a1403160f0305071d031603051c08090706030b01090302040f0b 66
    0x200c00c000c00c8407441c0c000540040c817240010701030300c141c03e207612a0071207010b005c0700e061110200f40d0b0075441e405491521803141540201c80c10403421401455100121140900b02e0031030800300082d5a402c941c80764070003610341500d90344950300040c007003013010b441400d00350384000781c0b038038400f1640001400e05900003c0d01c1000140b0510804410707100340d5100911001e1038201c10f501e0884803151000c070107500030b0086c0b0040c500180e840c0d0b49084001d03c05044100c080d4060320b810072200c0195070380b00c5400c1c0098123503c00c884015620340d68507045402c60306140c4407682c2420445140c2009003051400f4903002051007021b40d24000c10545428159a4035400c50394034100c01c40a5450981e20040030410001e514100c1002c403030260b2014480150403505031b180c0002c1000306038400369005a8042d0840303000c1c40151200c40c1041c48040c1082e003051001428000d210640d150303030900c5100e04240c1d0710369050300f82da071240e070718403001710f4000f4801e1020688500410000385041d1007240d100c2d0410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 222209802 1250 222208552 222208603
    0x3010e01081e07060e180709030606061706090c1c0e0105070f02150403050c031b010e1203011202030102190e090601090f09020c010b0d0c030c060503060f060714030c 73
    0x4054031942c4001a51002d00151441c21806941001c48074010b241d00c8420605160991101c0c01642071103454569902d8844170310790308040e130072078156030002c00c1004040f060207103024016140031500044240c545804a688210507226240200140040c46401030980240c207008141c01c1169504e201704000c00c05a180d243c4190f604425030542c1d803000d41c00c400305c0030180072480c01d0075940c864041e0504911740020080120300350f078080d4101c4881807040304907811aa407800d2054248005c420800dc0c4542d01c85140403298034001441240603000b921100301d001c648080d0143d81d600b91545d2402c40003890103a00c05040300b400ca500441c052400c000c00140c066204058100469024586440360142080c030120040d40c0f003440100d4080d034139a161107406840c7c02084005003809511030b42c441c81c0c01c40c0303015070380c400b040d901010802c013007802400403560b2a81541c000302202202c01e15500d100c0c03450300c00c410000d4030480310054000400c00d0424210f0104140f0a40300c601d142500d0705072031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 222211052 1250 222209802 222209833
    0x2120403051216090e060307030203010e07060909050609010b0a0908030a26010e0a020912030a080108121c0507030f0603080c0d0206040b060d050a0501020706020a030b01020f0a1209030803010e0108 87
    0x140841070030015a121008204c43c5d4120304070303250442000f03010b4031015503c0c0d070042400d440b04c20085818682c40910b040003080c1d0300480c4032020303004881051107075051800000700011810700503c10291400039100341c4143c05026020003c040b25401c2d642c85d07842800c000ba1003c0f940c000340c51001261030112040c410f901c00442810703940003074440400d07a16000c20740d000a40290441c250080c508000742804000304101501d5001e00c0c542e0b40308025070400c00c1d451300b8024148030b8130441850a01129a42441c0c8224421180080410014a43d0780c0c2c48006c502500d03021b004170007c0c516200c07002c000d105030240209007055000c0200c80a0040400d0120390703800c81260003500c508800741c04141149840c0d030045003440d01410031031302c212100751600e600f260310260040381c1c041c0e400542c1003003c58050050125200d001d002412040c0c441c9200b1944a04864138001d1000b816405c100441c507006030b8425000d960000002078a944e10b884004a60200a0054034840d10501b0001008143c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 222212302 1250 222211052 222211081
    0x31b030405040c020f0a140c06070b0709211b210204050603300915040905060a0308070318090f020310090209150d020d0e01050610030606170901021204030512 70
    0x2804008140b550360581f10224415140b07807035441c3e00d00840303001b01d090342ea650b806002c02d5405000c5070915403c01e808080c00082c520350100710440c07441d10302e54a038060030024020426410401000c4240c00d80304100c0003010712504081075480012414081515142c42941446423003520100300c952296001c0554841c1ca90b03000500740c60341c2c90b2840d40304011810492962080c2c824900b03051203021000501c04211628084500d124041402c100d5500207000d0590001015181c030405181140c540015034441d003c000341c00d0202e00c103180350b0709a60b0f0382c20640080c515040104108411081c442c4041c0d03000755605085e1444510011070528070174800c5640070b501c000c100b16860b00090966481941000400707010b1a9401c0c0601d00a001c154010040003c014100001c2c1c42d241203400c101144c251810784808040c604035080c448903030801c10111414034502c011110564400c00e5040c064880c2c540005130110701401484201600100540701d1005206084409951048000400b0700d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 222213552 1250 222212302 222212323
    0xf091101110c3006070c05010606080103030e040b010c050f01020714070f06080c16060c020120030106030b06070210030b030715050405010503060d0b01061d030102070f0212031b030405040c02 84
    0xc1400f03003002c800f1118105140700030307070041022000e0060b03904016400e0040486400010501c0007029500304003082c421400500000d007041d0b503d55040d510000c01c1c0c00c030610100d0380143d9440e000c0003650b078060089490420f51100441d80340c0504040d5441c003075002640c04540000c0c5a45074190890710100c0c00c0001c3d80d141c00c82c3c1c0315100b481c2c03910031901400040c210200c003a004000280c2070701c28504074010160f02030381c40412000c1d41814001d0843e202c64540e0380100000a00c0c10b40600e00d6082141e044034024a008200340d440301002440a105084000b5400b03070600e144000515055001140c0c00c40f8128261352070f00c0c0d40e40c03250300c10b001c2d8000c9401e000183c0401c0700744480d600800246d50030400240803090404015501c0100c003d0003030f00114040307102d25a10700030031500c1c2248800c0040d000e45c003e50418070070f603580c0e44807070302e01000082c0b00340e58204000302c914000700243c0740006000040b09203002c541403001c3c0d0320390b80325000f06405203080c0340310654010300008018986 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 222214802 1250 222213552 222213559
    0xe120109230f06060619110111070b010b09010905090c0c0102070506060108070c05060103150e10151d2208220609060512040302030910050409050f010302030303040311010f091101110c 81
    0x104807100b440780011b0b4030101490000c6c025908030042290300248560520340501c1a1070a0f542ca0349828803a401000503030140c4081c0340100000f400b41c0c2d074061680d8044540c00d41d8000604c0d21070201d5200c441c020301019001c80e40c4040b500106105002910500800080c1c8234860301d6211100111074120341c02e07001a0166005500400c00a42e4840d43c080f151580b2800005500203000382b2141070807442142104881d03161107414010088030b048945c004c08201e1442d84443c00d0240c0009240310000f005400f08010900700d11540c02401c08c26003061940c0182c1c0c450765241d442e5256980039416141e9558030080d595004910a4090b98000064540c40e80740e41c0d0604c0480012144a418001d200310114042448201c1c150703140c1041049503090305456054841d810407800404a903001000440b1041c01c000042001d07803804002c49420a405103458814a80b640300c03124050b04624000803403ca2800000c00f05002601840b00c01c0000d0036a10440c00d5030f0b104120320f50f980c0305070f50829072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 222216052 1250 222214802 222214807
    0x503100f051518060f0a020606011d040207080708120709050d0804260102040f050405090d050f03130209040c06020607030603020901061206170d110a030e120109230f060606 76
    0xb00112480250580103c51142d440741d540126000ca4400c1d0886000218002c40104002c1034140e01409120b600031030a180c40d50074180200c810300d2140350050f01e4180180c0d400507140d400d11400d202103a10041d0040c440c5079030345120a178044000e00040750340c400003800d400307408100c0385410280000315907000040282018208103110490b14004066824a981e060300b110302603100030b0020340000c14420b04480c1103189442d051105940300140000d0307241d045032090480d400d4100094131b2400040803009034036907441000f03e01d84800780080280d400a0600204030400c00306914010680d0811b50035280d09440e4100305400b5150380d804020351101d814001800300a11501450444918141010400b40d6886000581201c0c3c0c0007010b20103504610043c4a8898005244180e42e502c00d07402488884180d4800034807202d02119014820303012880c4140411801f500208031080d0440500d42241440e0095800f44c144141c60f80c01641c014045000240440800c440e486408064009403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 222217302 1250 222216052 222216079
    0x629090f151c0b0f060c030f1606111c1e110909040b0105090105060f0d0513081305010e0406051804060e0d0903031205090c120f0a030503100f05 64
    0x110010840d03250180c03004003405003401211407aa82c10031108241040011a1070f998804e0024102c0c0c0440d80c42e01410701004040344803540003049940f550444101c0c262108070700038081000540d4a40301900041c1042004046a0ba650000300b0100c600d0042c14011004619205800d0b20b4440341e0300a180400581e40f03810303190320398000010040000302ca20f89003660580c00114034850a1b1004c3d41c08000001c01030006003804078161307015080480c0d00300c4c2005403c0c1280c032180d2041c2c0448000d0f403500c40c004980c0d09030100b9081d100483d480740b02d80392a00b0038881403c0c100300d0b80e80300b40c1e40020080c10b81c1002c00c0c02c0c01d12445081e20400ba0a0200d64000b103a07000c410944090300c112503240e41d03008030340701d022000d0210607000c060a60b1a00402881c40c10000c6c9070340307840342c9a05e007840c0c034050038031400c21000101784001c0c00f41a244090100d00260005007004c00000380a80c544c041c6120340820568003200562003051400840c640064032410140804000c600903182c0100c100b58042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 222218552 1250 222217302 222217309
    0x2061006020d0f02160e0105030d1701031b050409080c0601060509010e0f0a080d17150a03140a0b07030e0106120b2404020406030b100c03081906090629090f 69
    0x2000c03e0801d0049403184602d20180c0c1005603100c0e4411031000c1695001800f446c5000c2c4442e05014050b440d01080044089400d184082c1042c031004003880c2510200c10701c13941c0b80041500007050018000c00c06145103060000203030f4051152003040d401030304008241c03140a44c0641c5e0003080c041c3d5800d0703490b02400b01030240354112111111750100483e00300041c20042080845500c12080d03966030155107000344880e0441c00098441000c40034962114406515916040d40450390449504010420b486c1241403e1000e400c4015141c00180c10410498a800d078000302c5c409202c0c540200303d46940c0781c603844650001c00d80024080040c4801145410742c2209107038180c00c0940e044035451900c0b4500184c102d070b11030741c824004a604da902180c1030703140990b8008800040360412507000a0284e6000f811000010203445030380c600f0b84418a0582c83c654401009801c0c414800c0121507150604100000b9000c12041c0144410000e8408427100007400d03036181c020060851840104e100c0d041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 222219802 1250 222218552 222218567
    0x12030b04090204020a03020c070b0324040e01140117060417031906060c020f0402090901030311190b090105010812030a020702060706090309051e030c0904110904030f02061006020d 79
    0x55903842621020040c0150359248003d084450650300c0c01680c0d500300c01c001c2c50030600b8540c061268020140108240c0802105000340d02181106070752540c1c0d040800042c000709100f0a200d001740d0b04c4c2443d80340040c045000042c0c165201c230302c4481a269412104103a036018101d400510500703201540111700b0384003070051504000b08083c0c0c0c0249030790262034002281c04a6202e24001031040003c0300c29401d01c1d07650220145801c0d40c0a515111400f00440c0b4205010722006040080d00e605060740014140003403d00c03c0361866001c030b1079030f00074107006a0306034044c2c038183e005520700310000910142c0014401c0c0c01e100c0f40c40d0328604595603409000002d42107580c1c2a60840300070000f00001411610543c412075100327031120035805062030140b0040315200028143c0c00c07035040c40d8032a183d43c0c000940c050b900b042220600f842d5510707842d02c0c070060302c04484541d070440c40c0b100c140410035070082c0ba003400044107542160290fa958400e54102a45240720f00302c05038101401244085219030403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 222221052 1250 222219802 222219821
    0x32104081b060f1012030f05090a0e1b03090a08070f1e1115090d022407060b0901050d030309060b0621010e010e0c03041a072006041203 60
    0x161400c0076925034510140300d460503903540140d005031041180c5591031144050304003e001c2e52420440d814401d9030b2000c06031403480030f0144002d00c001c2c1d022403481b550846440e41e20180031200916956521612030030350948460010703114100c01410342400c2c02065a01c119610001880c4503440381d107c020441e071040001b0ba540c00011030b105c80c04100c418521034a4044c142c0e400b042040d949003480c42c1c0441006000620612111049040c034923a20410303290828012206400500d10310b2000403000300300540301c032041040c0075603c0b012205801c0c01030050716004c2d103820300c08907070b06204002000c2824090a90301c40241300002d0082882030380405007881c40b4650001d081e0510300b00060f455080800c1080000b95207040c804032161034046142d0041c0b07406140c0078859410a8403c0c01da21500900240b9030f0440440020280403451480384003814442218007941e00f00640000c24005650014204150b403180300e03c21100c40004a26118540044001e103080d1010307042100507015030003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 222222302 1250 222221052 222221063
    0x10f09082b02120711160501030e150f011d070504091a0406080601090f02030108030d0b0303040f0b031605070201140307090506040e0901060b040303090e04080f030a0902030f032104 80
    0x70201040341c4140300611031070b40c20060b84042d5142c0800000c1070032a82e08807100f01500800e0220003d080b13000c40c404c2c01d0358001d00703000c41d080600c0221b003803034044130084a201c2d8500d0001448003500303001303514a040c0c0710f44c440340f62500802e0f10800ca09444050742d80d00002401044100a80045540403a40913202c4584c00302c0b030741100800090a6400507000b040c4c541d048040100680c04003071041c42c10200400c1c20550030f542c5420380c15a280e02609140c1c03002c140d190258180103903000d0045038060710a2065070003469803100004085504100c400c604445202c034041c1e0645070003202900c54440d416580c602c1c1d1100a8003950149400203400c5009010394144040360594612000d0005040202c121500e940341690009003511001e510400d0026000c0006002080d4021102c00540b84000d5072881036844a00e003881403441030003c1d080a2442c017009200009480c1d0700b01100c241e0007107040724000e02400089070340301e1080440804d418000c940f40d003541c4a1060003547d5115005c0d9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 222223552 1250 222222302 222222367
    0x10050f0702042306092a0f040b04151202030c070201030f1508010509070e0708160e06040602012a09030b04020d08070c060201110f0a050318010e070602010f0908 71
    0x1000da41c01503c02500c481d1180846408200d5203040c0b525074540c0c440d01c12280764010f00d90b561000d800c150500e03500b1070480d001c0000c1c021040a01e42c4215001803086054269490b940c2c1d8441c0d80c250b102e0380d00c0560010b850310110019550244c004c0c0d9014011102280f40341021660054009044004a80d8002c546481a664810400000c5200100740c01c0c80041050728260480c1420b00445d070300300b05150b241000600c401e0990049001c0e42c408218171a0201b01e4074281002d8603440000c0729030950050300000c01251a40d07043d046002100c215a500b03021400d5000302640c8a840387c141c0c5a0002070000381d04102040c4070403400c5030028006413450009601c561148409540080c00c165410303441000c0030042d41d582441760f07241107443c2d000e00314148440d10f464403d5912440410b07804104000c80406c09840515200807075070340c038000081020301d0452081c40e0700c511445c4a00030140d442c00e0190429500030303000741c1029a0b84620954a00100c0c241c20000744d00307402621001c0c03071924 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 222224802 1250 222223552 222223571
    0x80c030a0902010e03010c020705210303012331110d0903050f030408070209090304080a20121c02070b070204090804031a060429040c02030904090c0f0510050f070204 73
    0x28414140d1347c4d151980a001c105050000740304501440b01c82401c0301c3c40c040f001a030842d18000c0141c1c0e05480c540c001c40104c4450714036000c3d95450580400c2a444410412440c4401d240c096460100800b405294942005950401d800310b802d40407420001c0d640801c03502203142403c2d8080002c0d20f02c40d0801c141006680503400304075401c1183c0840ba00000012604252f2800b000025400000440210b1a241c1454049a1256050000245a1401908660040310320190403900781b0f8000360180d404c1e5003914010075a1240420300c9044085c00c804080c840140c400300c0d51505454400322018603241c05503003800001c21640c201134581000034031001c03000840c1c0591100901700c1d840c006140d00e05001c0b08210445607490080c40034034882031041101e84080c034142c0c586140b030407140020038400850080e800d602c10003050f558400d06d4080000c00308901d14801760140d403e02152603200644031000c1c800f001e440c0d0010007000c140180300803c40310385510002e0855602c06803010400d20300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 222226052 1250 222224802 222224809
    0xb04021908011503020103140705040308071518020f15030402060c070f0f080714130b0f0301090521030402032a040204140306072604020d0b04140c01080c030a0902010e 74
    0x20083d0b03aa5000c2d0464038820002d40d0303454000c044000d06180d43c46071080c245040081c00c41d104502c0000d045500100e01c0c401806030102d10142101c44084081c03060703003000303500984200c0d61340c50100d20503045001061814248010100c40e0f03240303807500461950f1255000c00c0703030716042060304411610a100300428203480a0300008010001c00402828060904030154100b14207a0001c45486015456404066a98091082481082c00e500003460005840402d076000e40c10240c86805600f0003064008000740020303e06c3c980703001c0191002c0e0300342c0d00e0f040c1150746200584002c0d40c9a4458000300c600b03c0d80c040741040400300184501c0134406040c501040603070704554080c42d146d0001038002c80403030900380809540055640351080700ca2404610210b0300350b86d000188130403840004002021500d9041da83c011a1340c203c0c900d80314a00c1c05107401c9980c800c100b103416100303006007034203c0b007654003030154030340076482014400b8107503517645040300e0040903000d00c01d83c100851841c100c1081d44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 222227302 1250 222226052 222226061
    0xf0d0210090305210d4d09010c12170708041401060501050a03021c11030928030309050a200102011802090103020f010c1407051503040b0402190801 65
    0x10100d40394281c09600d0341c00c015040c03a09046196403106000d50031600d0503c05001141e0b12820711038400500c000100a03006104450010f8500c20703002140e006850350414985644a04045021129400c40807521102c030180076441680d8003041c400000500000c21010048003101d000c1e10341108030b445040000e05420500740d50b0203020515407010311017805650405191105204402409100d143c4000200039200d0440d0240800d039011802c258106218012404034040c650003e10540015241d80c8595030b0050322003401030710070300800c00340d003020100258004050104466a41d07611030780382034024203070b0f05070102e500c1e000b060300000c001813641004000e03c0d003044900c6446448030000180c00c640d41007100040c0d41c249084850b005176502d10205041d2641035465800000003640140c4034541807003401000b20106480362001d84074001019000c0b82c8003261712a101c0110086041e95a11060b03401402254039100010301501b0a09000c010903021095500e00d0140d40707245590849 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 222228552 1250 222227302 222227329
    0xc03061309030c03030c0f020703021e031213050904111302121503060112080714070f0902030708151f050f04060801030b090105010b0a080c0f0f031905060307050f0d02 74
    0x10500700f090000d0541c54450302504c5c140c00d042012030340320302c5072020307503500028440288a0380440002c0300350301c03503124441e844190000d000c58000201c841c041e451147c20168050b9048010514001414a03181c04820701541d000048a5158a8241c080c490100d405480c10440e00ea020003016680100407101d0b18800c3c0d46181c2d18600b001ca201080600b442010b074400e8000300070100c00c00020418420417244041d81c411304821a1203d000511424025540d00c8403608601140c8000303070700e201c0e5400440c441ca44541e01c49010380c3d80c1c00041c946c8084c20003e032542000300d14030344c00c80349005c4103141209000f03541400e60518004841e00e038a40e0744150010310000d102040100100710042d203519400c400380200a20213981441441a940d0048110f0b117010002c1540101c0c8052003484129441c0a00c1c1482c81f503602ea14460b20011280c0c0141c0d14226400340c0503680f2018411a88102400340400034090440203140600300004011500e1403943c0c044107030b100c42401a9103101c8040d0307a5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 222229802 1250 222228552 222228557
    0x20a05100809070b0a023c03030a050603030a050a0c0c030b0c070201110102181005040801110c0c03010b090105060f0c060403030b130207030807270b1308070308030c0306130903 78
    0x520b40b40d802c2c1400c20710154043d0881000034001000d0039030300131580454204030040c4000007420341d0b0fa050b124540120066580e505610355810065020201c008c0d1301c41e5580c0344081c02542c0310101850b58a104241140c000074805000705c04601707101d0742c089400c45001e145d4801c0c0b226100e03160b51020700400d079101200040000b038100b0840d40c119640c0c20315185190f0003181051a44403e45030b030510b50300f0205104182c61761b41075900d00c2c043c0c000d41d00600a0640200f14424009407400d00703503403008a0449691040110348002c5141c14004c40c003082d000a0f00d08038041e4a801c040c0719880d040200000070b0a001031000040a202c2001954413503402a030b00402c981c1580e106012050f4100d03049980d840d40100051401300350480002c0ba0000c1e014503000b081813140c4400102d00240c280207252070307048119400203c0400210107170000c1c0c171400a58410b19135030303507001599400031884000d01641091000460801250010f1680000c01500284418008074848012a41d280c80c04402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 222231052 1250 222229802 222229817
    0x170d1e0c030e1306090c0206010f03060513060203070306050f0f0d08090126040c0b03040b0606070f06020304210c050c06030601090803070605150d0b040b1504090c08010f060e04030c020a0510 84
    0xb11410b94050b140d040c50305400602195418944030000ac440c0a00000e0802e0b612503020442d00c107608941001010303088074085403641002803008004c0c0a80e4401c10b07104003013810242d9054030b01064a0f581c60100180480004031050759015100e4000e11005814080d41d400152443c143e490900b01103c5228048190300c2d1400340f0f004081c400440d0490041031000303008000014802c074094a400c8001200d15a07203c000c1403030403440098240c203000f0711043c0040240420802140e0103600750000800200480920724102200c00051502c000303400381d4030481445c1181d04017000156082041032408184070342c0c4410354a0715503840380100302c9030280c0d2001003040d4000d118491342034901040760801d180008039201c0c2c5002440162010b01180e0596000c00c5000d404012001e40400c4041c0c014008101c446c101b0001c200f0782481035000d1542440d2211b0707400007013440f452064468410b01e10440d0740702c03514100e540040921080741c001e4982030001c01c55940e265142d200c1c4040a41d00d50302c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 222232302 1250 222231052 222231059
    0x1302030a0606080907120501060b040b07060b010201052412120a0e0409020105030703021305191409010324140f1812040b13090204170d1e0c030e1306 66
    0x5045500c103a200c002000a0001030040483c40172441d41c040b1038946001101c00100d9007000c9004241c943c0c450024801d00103030008407402070074050921540122410405444890010790903103400b2501c4d8280310740c1c680000c40580502e0a203021110001030041407d904201d040f01d07152503403603a4104001540070542e4400300d64490201c58a4400651b818059600d983e40003800c03502000e004141070607004035103d00c141d00d500300003a004141c000c01900032851031084c0960402c1050152040c1c50f42c541142c1035241c24040090f504032644980c2581401c19040c0b00c902ca00e5240000240ca51601c03031300e80d41002496202914060742d00c420403d01141000e445481c01ca001e05420642c2030f400055240d02c220308040151412242d0b9a5040c554070980e0710040c888400198220000e03040c80031801084c01742600ea203813042140c1c8801114018010400103480400d0070700c0060250020086480e40d20511500461020324820309000c04518000c80003d406003d0080f00c80809584d074202c00c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 222233552 1250 222232302 222232321
    0x912030c120f0307080a0906090303020a2309040203070c0b0103050c120d140d060f03080901030506060f071502071415012709140303010b0702190b0304020f030c130203 74
    0xc1507901c941006942c5010000400c002d210b0100a001106026421001450b8110039030007007031809a000d075040106c02d03031500d40a0029001082c5d020005070b9026460404a80c43c080e20040724100c0345112400c0c00044810440a0f40c1b0090011040282111030000010300c009400c6003e14416000303041c9901102091102c0c02c40e00078048030460780064041c000068101c5aa4450510b18401103551040c03250340d8140039180d683d10407080c03816600030000500c92084003600c55000c09907000e00c829140c2c1000c01c01140141008490415010000400003500303660211054555440e409400c00c51252100041d14207a010108001d410407800c0005080c0204015030140a00680307000b02406d0440c221051482140041d0010700c3d90741d5481e405000c03000c03150545041030142243c0d9690713102d51264165400030070049001d0300c42e80b1201503005c0703960038481e0140d03200840213034190395031502000074500b041c040085d003502885240e42541d445840c03010344005482c450151781c80c02d1047d140c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 222234802 1250 222233552 222233563
    0x9120305071b02121005160c05070b090109090c02030c10020309071e170f0d03090b070c240207050c0306270f0d0e120a11060706020912030c 62
    0x100405251004015215400810b500703140d12424269060049181c07000c5201031400c00b203260313464070074400c00681c040750f13580119224454601c00f0a00c1040d9410040c2d817035442004008109030002c5070b00784900d40031400504030101051400368045036503102100115800800d0b04401a00b00190001214800300407410445410880841ca14900140c0c0c040c2c03202810700503421003e41545002840151007580c100141801030056400354080108036a40c0302181000040030340203140c060200240244104003000e50441b07040503c41e034844500316001000c141048410000c840e0301d41102d83c00d2158540000300500d0300c01a0380e0040d40c00d24038500307002c05c1e240c588241d014604000c05892100c43c0402c85450781104030307050800b00081141881d180070104200e51040c0c1460340603003540011001d84440301614014031043c03202e1481b075200c001144005c0c00b002200f9240040034100f030002082d82f203000b040b0050406010f40d000400c1e141d08810704840f23703400810107111080b0b00703100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 222236052 1250 222234802 222234833
    0x515030a15050a0902180306010608010501020706090602120a020a06050705182704030c120c0210020c0f19080102030112050c0109030b130303090503130e0903070c050f040b090a09 79
    0x18003010910340300004110040d940110b50300e260b00440c0b541280c0c50044e084054840001f810380c0e5880d0784403d402015000c091081c54014400c89400040b06406006c0d1002a00c2807075001d0a1030000c41c4180c2c0d000b81e4440300310881180f243d80700000100d4840e01c16036005103460340d5040d07560301e15007a41520154142900314400c1d42452402c0c3c8450741c0842105040900c5d02c850381030f9560301d80c101500e9013845400060030000c1e0301412803921070f030700c0001c00390480c1c800c4445084215001c00200d80d9090711401560300b000d101820001c4600c0e19800120407198844000c040154641c4507071400ea0300300782d1141c611812080740c143c0c104041413081c0030300102d0070320b040b404540c5103403030b05a0144006001c0740d10341440340f09a1021b15109400c04540160402c00b107a95940c003020340b031103040d052403154030034501ea448046540b28801104442c07040303401051303800b00e40303051004001703142e00400e0340c0680c4169070f2001c40c086c0351503039500320303118034054000090055402e08050040700c00303560 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 222237302 1250 222236052 222236081
    0x518060a1b0504050d06050a0e0f01060303031503030815030f010c391e1a06240406050f1b03040e060d0201082205030c01020a09080c060a080903040515030a 69
    0x10038003980d120345186008186d000032020a980d142c1e448030f040100029500f6109500451440c81824801500321508a074400c0d5010000a080c46407042e480b0740e4280001000200f20320701055441200c10f03181e101c2c0c1880201036030b0500c601d2a00a508441866003001c0114400c1040881403103005030000250801048401c0030702d0301580c581c06607807141250010202e88044188510f0344844078a0890b6881d4131094020014102c1c1d80d20200071b04d81122003a102b0083e03401c10b140c110042c1000e0881009064038000e003001e04289068030950810801c14202c08810b0280103400515050107002880c2243c02840c2d61314101440c21030f51220082009006086d2000301100503603208032a107030f020500b88d4282803a04071118860129164102000c0e0041c0f00218004141c1c11066000307002c2500c0d547c845010040e9500c45098031000300050703466001000340300c000800c0d40189003207540a8048000d5900e887e40340c0c03000440f050005d0716146100d600101c10400c0b07106292007480080c5c260503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 222238552 1250 222237302 222237307
    0x1902030901060f0b0a05040501050c0f030301270c02190602190918050f01030206091201090606080106080708030f130314060f01080115061409040f0b010201050c03090d030518060a1b05 81
    0x110001b03000d62140e880760904001c1c0029041400c40d50602408220050001c107807556941d50710605110903012000300b40c4142414010b0015a24040c4102d802c410078540243c070009031445c6800809a4080b04103a440c00c1d001c20101000e20101210601101d409880701c004140c100040b0030340540990b400e0854861a11003403001300f404202d0202d04680e070448800b5601d07075800c008250300c41d481a20b03480706507081c81d00940030400ca5800000503039101c1d0008001090f0b60b89230250340c80203107100d43c1c11640c20403c80b00001c0e4a0302e400810081000c2d00400c5400d42e60303583c0f854041c42a843c0044c050303410074003c0c0320020340301510320743c010120750009002a83c2c4002582e8410350a40c4603e41c01e010300503105d10305000102054030000b0b100140104036144a85040801620807004564019440c08000442c20b114117001c0c1c0e40200e00c094000e1a142441d40c2003500101805890500c8024181d81114000002005400c1c401c211040c0089582c00d24000d001c58141c03590f03102c050030300009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 222239802 1250 222238552 222238567
    0x1080c0907080f040c090c020715140702090402120a03170109110a0f0e03010e010f0c08010e04080a1b050f070501020d3905030703020c0a1505031902030901060f0b 72
    0x42800e4014460400900894882d0b05c4c119007454656800300c075015003041503109950b40c01140b000100c1d48204444401442240c5044075821801c1c040c0800f4910f082c0288000342c205003600342e5102b03201400303412040c2e121140070b40c604441001d044002450b0b5103004c80102107080c0d0050b00600c60501c007440600c1408004142c180202c050032020007030001410f012043c4100207049001c40098003c103d1301c40201c0b503e03806401c0120701c076108076040c40804c0e00790174410803500e030407108600c1c01400346803125600c0440d603a1149880204016000007820f1341052084d04130702c00140300700000c0c40000c403030790161414151513500483c1550844401c2000300d03500403428100074942401460101c03028400304508103000c80549002c505030300d0010804200c00040141406070080d0222001c4010150411403e4101c502130b405404c2c030180401214240140d0113980c000c0b40c1905074021040d44140800200c1e00708442c2a006a91102c4082010b00604440940a40715400009103440b01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 222241052 1250 222239802 222239807
    0x112170702010e09061f0c0215090108070c06091b140f0609010c0f08040603020a08010906030c03060e03070b09061501050c03090d1a0108100e1504060c0c0605010e01080c0907 77
    0xf44040c480e402121200c000500d1a600e90b204c0c40c0715100320406210307a41d094518010004040d805c1c0880c040c40e0f880d511202141412000d0b0b50401005940d030411036941c114081350030100056040360520703224203403d0b000950050081c4411401a159900e09034640142c541c8840314100310a80640c540030100c50050300c1c1c40d400c8917080c400c00c2c280f04d005214645880c6030420b01321000904108000306000c200658180c00600e007602c82c50303440c1a9030341d032200100421600c16200040074013030400d108100081c061b4128016241030b21042d6030520311940c965419000c1d0071504640c00d41c01007010812880036048488146101c20301c2c0c40340c100003c0d50701190392440b45c500628816a44110040304010403110303c0100d00c091500c5003440e5595690300c203a503c005450054801e81d090803d50385030300300d000900700004440c11a50600035283d40d142d8000a00645080c4001c015900c008040894518021103000344162048802190304d4143d4503828159202c400500c0340404005001145a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 222242302 1250 222241052 222241067
    0x12120e03060c090a0305010921110d0c0c05040c0c0c08070501200304080a03020d020c12060a0b01050405030102071406150a0905130f050a03080a1118030c09011217070201 75
    0xc200e00c0c2d4041e515a8141c000039400d41c1c09a000a0956003001c0d44c000c100034001c00b4000c40c2d601c48880c071043c08100c000e002d80d214070314803000405c0366000c40300190082d0711884404150384c0c01900f24488564841d404503050b102141c2d5030102007503a1843d0401003144c00d440031001001e0300000303401c8e1a420040003c14480881250b030000103c107003040e02907250140201c07002840d000d400c0f1400c1c840c0902c2c0185d20350740c03900c0d40c1030094041c1980541c12410501c034182c3c0c0d44a2030a0181c21a540c130318608500030040055414100541400040b0ba00e4509100070004c9034007504070300c00554050b2000d0380c0f90600040c14000c0c0101680c6180c122915012142c00136561008008100d687d10a95103d10414a0b41320240032041032042c0602405400300d035600801d80650b41d8101c2d2030350380c01c0580c01036900c04140200704600401404c03040542100d05910003031301c01400c2d500001c11000c00120700950a800078421190f500b84400304000c1100201d00c04c42c0c0c0d450740101d0030025070f034002a00b01d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 222243552 1250 222242302 222242311
    0x6060e0307080106080a2d03090e1006050f03100e090a05120c03040e0702010b04060e070f0206161b0c03080307230d0c0309021e033f0f0412120e0306 66
    0x344864103403416002c113170030031131000c0d211210011f500c42c0603241001804004a80b00e404e8404101c0e40c0840e004016084e00e07007060740c0454640d585000d121000b441100c0c1c0c0001e05040625500c0c0001154005100314941c3c0501b080350000d00300081d10381081400d000c040004c0702d010602c2001100c04420021080d00e04550f070315011110315075208041a4003400d200903146a1003854030f0400b169006044195034045c0940b6a141041c00791800c0003070b0381da5401a648140d04c500c0382d900d02c0751094440c800c2d141510151812501c050358859540d030381e000406400c1242d0500000c030030400c2055000545080d5440740c18001045000e0750b40b28981e00348a41048001c40701c1d2600c0104401d280030760803031108145c0c0a0722403400e03e00020301d01001592100c480b00d100b8014065082031515084c103c0c03c91110307580c0400d15000e04001103144ea40503606441c500300d0542405066003014a41010304014015031f07050100322009840d220b02c0c1000890311070707000d00c200d542c810340031a14001001c580c003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 222244802 1250 222243552 222243563
    0x504020f01051b03040303031508160513020f030c04030218040f03080c071208060f0a030803011818050c0306060d080a0815120c04050f040f0605150406060e0307080106080a 76
    0x2103420081050105541c00e15400d400f600c00000c0000801d50701d07a002a021107400091100308035103450469464403100d4403032aa9824441106014901d050281a608940080001841c0014546020311160412030300c03c804458045020401d500780751b44030070790360a03543c1008061803030701e03640e2603003811442e410260401141c40001402078650000f2611b00340e403c003110240203802d0b40001004180100c62403030250341c0800348103e0a0904146070800ea0b50310030b9509055a0030035404074489150744800c19081d54940078040c2c04103d0b0100155450350251000d8400c09681c2d400b458a40000a044075008136410341d1000040340302d85082c4c4209074824503101c0d425884070f5000a00c0007000c540c5040d80400c80e259522421103000802d0201c040041d2002e00541e82d8a003c0c002040300e003110090150140d000c070752400a1003036800710364894066500e008600c03104001160845846410a1b80400e0001c64028803620382085054000e152080083c40000c1c1071444060b1241c100f030310020030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 222246052 1250 222244802 222244807
    0x1203050a1404080a030e060603120f043b04080403060c090b1912020f04050d06060909060b01030510050f010e01050f131703131205191101030b01030504020f0105 71
    0x410344495004500d04074140e404448490a2508005406901c8110b491000c00d203054013021411130b000c41c00b40e10504006000d0100554500e40d650b1081d8000e102c00c0c46107c408000102c0c8100c0c9481d490380140300a024151440c0800c0c0c400101139030b80c1004034010924480741000300244001003200d0540798000700c045182c000544050b11101070980107180c5201d00420b40100c000041d124818410a09a032800c48284807609202d040f880340111480c1c014008010912030f03070914000c00801c45120b0b00000413001c0c1d03134040d080c00701d640c1400d04851490f201c84c24495190b9140c0151501309581c2080100e002d460040001c01d50122031104e20305010200785a40d000e41e010783e060711010183d4144032546c408010100c1080070700d580c040d043c644419800d80e81c400f1403002094485d0344c007454520b00305290616800741580134010b4801c460300c0c031840440c07488074510090050603503440b071111202c210849a0014064409810301c407030425150000b0000540d0306d200d0040d40e8070764203080c59a07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 222247302 1250 222246052 222246061
    0x10902120906040f06020906090907020c040b01090b0414060d0216030f2c010201020705061302030d050c030307051b0f010618020c1c11060403050307140f030610090f090510080109120305 82
    0xf488c90003042d144d1580000c003941001151600441c0482d41150112010406507207981c005464141303043c02811900b502c01d00c0f09100e1600c0d4912850104c180c0100064141441c90b09000240c0e40020400342d5042c910030607810030107410101d030280000b1141008048090190428074010b024151501c164030b40c80320403018240d00039412100c040360040d080ea202850480048801400d0601c401c90280c030603513088000c99413040041d50491001c01c8080c0d895a26440800c40320384d0490400b0014507204005100c000780020802582511300305400410041d181018240704601c44100c3e140e0740e10b00420113000c0090011a941c040414600c03c6007420784800001124103a900d44a0b40240d84515000d002c01d050304240594031a05e0182e64a2100c02c0120303504201600640c4200c240341c081c24800f192040c50620320b40795101403103141580500d076940004030b600b04c01030351003100c43e01d68600c1480014030803520084040d0000500a10a400d003a0355860b90180b100311020041661b00c04c00b04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 222248552 1250 222247302 222247309
    0x10603020a54090b0603010e06060904020d0f0c1404030f0c05150705010b060405090402060702040f0c090302010908060f040f050a0602072a06091e050306010902120906040f060209 79
    0xa01480580030460982e401e0b811516214107509002d82d0452030303820b900015002d115008050742c095024040a003143d00c1d00b610a141c803003000d813084d540728409020001075900c4600c007400103a0300d540004540c255003c40301400f01c5000c408504208410301d4010000c03600706108980c200e0307611520780b000200b503d0a00c50101000d40e040280d02501c4540d8415010f05054040c00016010310002c000780b202040c108009441288142038101e1012000540540f03800c0300a0112a400604046002a2014044d10486040b558038801140f0252002d2096591100790039002d000c0c80b400a01160a024043c6202c40b080244010300d5001818942000c00c401805400f545c0340e0700c40d40946d1641c06a10380061001d100c01c65581e504000d58802d029103a050800d0082280c1860304c42c49455400c0c2641d070f4008001c00608075128403680c401c00136860702c00f00002c0e03000b01403402d8010b884000303846113010103280241c410310b40ca910440501c00803425040c40c1c080e40c250b020800507a51303d21200030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 222249802 1250 222248552 222248627
    0xf061b09040e010c021203060a060c080d0608061803120a0506151201090f050415020a091e08010e03040e1f030f0609050606010201091a0a0b030a0c0806010603020a 72
    0x2020740040c10a00500564201500b2940184c100c903001c1d02c02d00200180380341c1103400221007107540300d2481a420000103005101c0d09012030302410b481850304298091160540e45241e0046c17106901010370060075042a1140e188505586400b0b149800b442c0141400221005001d45030342d19601c2c80071030056a1800a40541c04034070000c4903071200c5400500303182d80ea009208014516003031100004140665100340c0340300c1c039404003842c420160302410390402500004003560601c0204240850030f052400c4501d006148010100108139062504050a480e800b0240b0b1513258410310080c4114803403030761407590101c4090400d10401c003802042e5400e0b04c42c2584050300d041200c80340c000a01101b42c000040307850040044403080d888540049080343c05945001c1e0103c10f5486008500c10103400280380c102d41140d50229408040e100000c0c14240c0b62901100c030003640030402c124004081c4140c0340100f21a08003103040410002020300244154003000c1c4800303c000c161a031982908159 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 222251052 1250 222249802 222249817
    0x161404090b0a0f0605120c0423210a21021513060e1b120304090b12010203090f0105011203080105041d1e01050108030702010e2b0305030402090601020f061b 69
    0x303e0356409582d18000303005503004058903280181c20717a000801529080341101c045404426403450b0f41001030231450b041c0900c044002c0d03070140120031010300310740d1800041e245600c002806000c8610300e038a4007403240c40d004408004581e41003861402d4564000c80e400714961503c61a0462650302c3e00c582c1d49a10401a0008203240d02d020203003104044002920748040c40c4220302a203084d010101000300458003100030b0801356104005c07e1041c80c0c0305411000e02540080d2401440c03d05070b40c03035982aa04101c035040f40b035501c00c10380700c601c0c21406d00402e8010b1640d1011081400402d031401488040c0c14000d450041b911110420b012042e00340c42c030b001e01c40d101c41c1543d0200062200e111a03c0020604400903982000004180c3d00c001000f1280d240358161202d00e00584442305000c502500244e8203100d890415000080040360420300d9925944240d0742c1c1a40d030f180c148104003c01201408503811580720030220350054000160b070640001d465650790307814004040c071600c500d100d00c44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 222252302 1250 222251052 222251069
    0x103120c021903030807080f0106050a0203041205011e05150405090c030607111501080d0c0201090906121a040b0705090409080d0e070b1305040b040b0612161404090b0a 74
    0x490702c82010301401d00350310076244a41d46581c481d0302c42c5081120310141c2552500b5841c940c3d140100644c42c010030052002a046005482c2000d41e6100c211304202c50030501940c003651203103540c101c000d07102d0b220140346221001c2c0410a9042c0040b840706650140103900d40030300c5d5960003282c3c0b001000c0120b40780509000741160401c0c40c1821707000741b0031054111842258400d00750111610b845080416050360150802041c0120a04200311803400e0244000d138140aa11403000ca03a513651801400040c0000107180c0b4011451417400c0354146100705200c0c0c4180c010402030000040d5079000301e03034203d006450640d44914940d40040d0040803000c078000c0429900050303064109a05e5000b0303460490139641921960b694554145030b491103250391000c0480c50840303051049151030392101c0c11001c07024000040301c0306001c1c0802d80a9000c50310302241a0f803904204040d1241e0240360b2803400c400d61503c0f03150b00349403108100d018080c0d0b020700c000d01038071001c00c107417a9250301407810006d2070380300c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 222253552 1250 222252302 222252319
    0xc020111031801020c03150f06060403050d0e100804231009051b010201140c0d0605091e0610090b07020d2a080712110406031403130515030103120c02 66
    0x4000072080100b5428410702600648004403130b40d02c0c002c5810a0b0216812140b0a0681c1d02d00104901543c0b005140303a81c029401e01003c0003284042140d40c10017038464560080005204042213a101017200b01041000350050411001170313032140000e071480300740d014a0104100811032071414080d01c4010003408524090718801070140005600c1003810500d80320000398105800124240c072807040108581007050000704814000d08001090aa91044030009089440d0400a107007894159007180600c0109285c40ea03040040c1080780790002422a41c0c100403004034280a82900300320312400000c00804981c00055450f80311504140a521406242c0d10654403aa218601c0300700e4060203148040c0d49801089401000800c001560000040454000200d5550f03024880011003030710740180e241c01c40080041c484610380880f80391904082d5450f1400c4801c2d09660b100c40341d000070703c01c10703403440032030704100d6000d080301e054a03001585014070145184055440c0c9000c1c0702d000350000500e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 222254802 1250 222253552 222253567
    0x1203020717100605060c0a08070507030515061f020606040906021e040314010b0f0418050a03050a2c04020306180a0203010e0606030601081501020a0b1603110a0e010c02011103 77
    0x42410542c40d28020b10400825403620180001401400c0d83e2400d0350303000071161004111514050a0a1880380007105c03101c81d240e583d110304000c03041c1d0846c280b6100c003206100c50b514001812025410815181703078404100c50320029600c51340034103998000c0d40c0e0740e0002c4040c040c0343d4046403041146c5c228031500c0840d00710090340f82c1e507100b440150f403a500c10702c0f080e44642d101030040c01c000080092480b9030000401040100500c1907009a410b014810660307000041d9061103010301b040e0181c0c036038a07280c040390f52005d044940d001220105080f262180141510110382007003a41600681340142c51781d0f1440e020500d40003240391130760a440044820400321f05541d03001035068994130041c13146162903900038425203010580714076000c10903420004816044d9001c800303044410520440b106034180e038407050780046040da40030304142e400080490646815016070400c9444010207540341c070001c0980100b215801180d9281080300c0d0138460019a0303c147c6008805005d07200c1580d0791502c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 222256052 1250 222254802 222254849
    0x60f0c020604021c050f2d030304030e040209130c261f050904050c030c010807231905090a0b0c070b0a0509180f1f0e060301090b0106080f011e12030207 67
    0x4200004400341c107a08003d003403105404444204c7c0038a01c0070015801d50701c460b40c00741c0d0a2501202c040d41c200781c1c28481400542d8030010307098040076805070b0006008550100040084261588031a1424418500016142001c8840d2036114103c003281030190405d006000b41c1214190b0b00c40d561110b408000d02042c0300700032800341200740d03044080b2490311058000542d0030100488003500400c1b0043d100024840c0054592089034042c800e60070f02c1e0020614003c114000901d00140000c0c0020440700e402d810100b0b031110103040030b051035500b41070000030300a036180d805001e0780c840c501e000300700580d400e401581540c0700c8280c014110040b81c0c01e20300d43e100908001702c1c0d50540f801880004500385e510b03c0e00500d10324421a201c00b802003410314080180c681c0020b45882c0e015076030392064a0100d4601180180603000d99904c1110300e040848410024520681018201220701c0100c4100c800f0182c0041c8212001e40d0320740d080c440c1080c103081c4d081028503400078451072a00030300045400c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 222257302 1250 222256052 222256063
    0xc1602131508160812091003110409020d0e0a0206190c020904080c0c01080c0d150504050103050303010806092d030702030105100906090207020f0f1f020109060f0c020604021c050f 79
    0x701001d04890f481503980c0350143d50f40161609810601c4000c2018200600b801203008101e48898207001c1003420010b40b00701c205601540c0144403107039011500c8100ca000720302480d0703c000030007001411202d50030340001d40d05120b80c1011480e1102e85c0b00752103052602802d05400c4d01034004140d010245800d061030400740c0d0200b100c0c21924011036114840d20740c002c0900c28001d0544142e07090801c0701100030400105880340241b040001d80c080009101d590354081e160107584101c0207940c03a5490802c440741703002e0f800f80801e0340743c0c1c004190120950081d1080b9159030003880c12200255286000824110300c0307403500180d095400d110401800d0a486100d00c001c6030600c0c3c10400520740c2e40c20004040f4050000c000707512101450901a05181600044200b00001810800080b4080c508015100d904d1900480540d458043c01001c0c090688190380d017511500300184488000d84400948030100244000e10810003200c800e8038181c0c05405001d049588402203500000310001000c3d40c42e03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 222258552 1250 222257302 222257323
    0x5090c04051e040b09070f17010c09030f12050d090302060609090f0a060203150d0f0203010b04022107050c033403050301090207150609090b0c1602131508 68
    0x1181070101050380344400d41261241411071242d4086683c07a5681e4074100824050500c5101e0b04c1490b4010600d029825a448020314200788040303200d0780030104039400d4504406042c0c0c2480222507040010a1405c0c05c4003526650280a0f41d0304031030b28040a448901802000441551810354100c04040e00010864050002110f00c0100c0b56078400c8a2076588244000412035a0021011400011519006550024802002c901c11444408041103900d10b02c43d40039184030f07c0308540712040d410288100300c60004183d4056180550002d40c1b88003c2044a503820a0700d0503506c00034070503a20500c242c455241070141039030b070b46071802d019296a20001d20740314140e07911131450001c410075852002d40b96882d410b0304c40500b960720b440c0c80100250440d0405039544100454030b84a510300c9440380788090007404000180d0500281410026240d0081000c4000306081001c2c0030312030180b80605401c29411550301484030049841140600700403a4000e01c181041d03800818911004104110b11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 222259802 1250 222258552 222258559
    0x30302120a0519050603101503120914031605060a1701090f1109010f11160f06020c0409031d0a0b03010303090e0f060d120201020c16091a0907030b031005090c 70
    0xe41071581ca5003c1111000d45582c1e40c981e124010700881040203401403d1005089800b81038490703502c1e11078580c1c032900c250011000960782c03502406103003442d40340b18200840960051000311124521091100c9860040702c2c40340070085134030784600f44035540111800b48612015400340d6034520040d00505041d1900e400541d00308a04442c180e440c04007507400001c0e05070350305011001c01640035140340c0d41600d0301000900461800f0000441d144042d036008202c440300070403181e450980001d0500c0908041070b07106034105099000403c1c0d0290813004071907901c80714680040714920001d00b2020050f44582010300003c4000418141c05c082550212100140c8881c0c1e1a55401041c40c0840011a0001d40c44401403c8401c0030681940f4040c403600c100f8000117182191801d502c0746840080388600080860079441400251100d00850030390b00002d5046109a21242c00011a42c840040c030200806640b21619442603034100403882d61000c04580030400c1c0d00b00007050742d4450f210550707510300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 222261052 1250 222259802 222259831
    0x807240b24030f090a12020d1706010f1b0c080303100f0b030a0f110c0a030e04020a020616170f040c05060301061209380f0603030a0507030302120a05 66
    0x2411480d19010301c0205003a103030314a140d030350000c40f281c030b040041c1014031303684260341c2e50300700044014034445070f50140c43d001010652046440101a001c880074080303903030340340711090103e40d07600f181d40b0f00030300c0e07440d07041c403441d5060205090b4178151802100540360b112000f00000b03c1c9040400114010200304051540180c2c6031952a10055000c3c40380c4621050f040000541e2640d407540f0907440302640400204214030100d0410106401c840d4080010b500410600002c03d6005800e20349002c40c1500d00b503082844042010352524001030101c011744010140416204d841900c81c80940c08001c0f251007900e0030f250342010801c032030072501165105c911190204652400d070003503a040304c2e030a58510794025503122000e4090a400791040b503244001b004140c0c1c103068039400365007040f0444040d628203180d5554410b62100c50142c404032007845000140241a1008401c4944144c0c4034201155500f150b0302e4220000c0c427401c29209141d0030701800b800750030300c000c0d001540655040d0a042c207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 222262302 1250 222261052 222261079
    0x30f0c0f0607020a06020a0c0c0b090109140d032313181803030216021221090d030c051018022103040501030f06080102041d0a06030209040807240b 65
    0x103a49070816210000507a00c204040c0c1c00151564000309011051898800d42c03205642d964038400060b6074010b420340c02c2c80800c0e4010b981d680885e00e00c000340b0300802c1000001c00d10714041003401010400c040c040002c06d50300c41164118045041c8060030018010a40c2c0c2c4244a002d12101052401020300302d01907042c0040c1000124000d029040320790460807050341d2241e5500350020352142c100c901040303035860f28807005039075048020981c080c5000302034501d1030003a0340c0d803001c1c2200300700000c0c1c4014402d01914a65032150b011400016a00d03040c8185c48070050306200746030880c0101019601030030502e0001900e0009668803403000c0c800e1320140581c0c4010040010806140c114244440c0c1c000d0104100940c400d070401051320040301700006041e6102c2050302e081e42e202d6003040007181c034000710071001400c0503a012540300411050400c0010b04642c00070b6038810b00900b01410800001c0b48540030b0005001160030344000c020b040d24648181c0f009110064460402803921030803003a81c9a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 222263552 1250 222262302 222262333
    0x513140c0703021b1f03020408010b010302040f0e060105160606051005030f1f05030102030a1505030f060103030e0103230108070b0a020703150605030312040b1302060a0e12030f0c 79
    0x1104019819005040c403400b02444044440c00341c95081507005011207818003a0304e0405400c5e078400d0700c2c0f5030740c09681e0300c1c2040416070031340b40701c0e18280d03040520410041102d140000001001ea80081c0700c9504140ca84000407162802a030000109288010190308100480365100030202c07403081e1092440c055042c0025251400115400e41055841700001072140603049440c9003015a140d134550003051311180400c0c00c80c3c2045a1000c03910703503151083c110b80000c000c001c400403d402ca00404040710007070301040d150f59046c4401014030002c00d421038641c0e0b00a4004606c0711110b001c041074040300c689820a0799000038810050360340940000807400d004540100c1d0a5842170b60000d0408920316501c6e01e42400c10f0601128050b96a84030214007a81d00340b00a155100440d0341c10a040d061038101604106006030800e00445a101120301c0140c031800b05544240c8002d0400445c00383c010b01c0844e0b043c0b05c42c003080d0585400006130724040102000094086070901c0821110780c40c0550201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 222264802 1250 222263552 222263557
    0x702100903080f07050d02040b13050d0224120403120f0b030a0311120c030307030f0209011407060608030a020f0c040902090613060503161404060b091302040513140c 73
    0x75002901d40b5001940310a503860311a50014030380e1604d2031134141008000c2040741c0054000888032103000a181416041e05950342c409040112854a50403020350f000484d00308020b84604460358041d00d00488246940f02a5440030b05400e41440507840c042c50020200303c0700c4121150b2044c607000320108002c40c50701c81e11004100160003001c038a54030361801d94070081102807282c2d003031064132503a9542c070300340c2400b800751400c507580159281e051000c000340640f0300268040032140d1050140d800c8130f0381e10070351107403501c004035001d1a9203002034100b80000c0c1c80c8a0300320700e605110000300c1c0d0060550004041584698440541c8c40c610261401c01094410060001c2d40c05401c00c004101d2603c2c00c002a80b9880e6118000011850380e2200441d0a11640c030030101c0c221500d0032010412102c02420382200324a0445040105508101c14005540a0445494080c0750441c0084040594540c120350247c0b000401c580c12012645110754050013a6140d800c0412001034080742110385007809 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 222266052 1250 222264802 222264821
    0x4060f021020180319031b030f0507030e0909030405280302010302090102070f08070501110607020a1e1502030a0c170c0304020a0b03040615080307080d2f03070210 72
    0x10045050070b0341d01e8003442030b5040708210440150000c44540d80701c0d64100000c80c03440f06a01003030144a8000d0801030206074011f040242c5000d032404892000035401801d000c601002d0f41412030300c1e005981022281070000701d00c1e20f5041010741e002d00400030400000b0784100d401c1246c1140c2282c114146c40d1046031400d003585000c0d50400340b024401036011340c000e030048a2061044481250751050409030301c5031180d0041d403031500581008d00681d40c4c414000c1d1040280c180043c21142400080255030303d42000010b405400040c411820032481d01c42c41203247c58000a0100e05c1d5042c0d034079228000c1d8015940120712074a4003400c0480c01e0302a080a21440113041292201640e508510503620703803005008985c420100b01000c0341481c0e0020280d03010360302540c0e0000c0e80080c101804081114181c0000030700c2d501c18051540002d800780c0898841c91044400804d5a591014110003054010001c0b2035941601d412103050500c2c44502542c400d907000d034202e460425880d1404403c80d8172080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 222267302 1250 222266052 222266081
    0x15030610081b27060108060a0e04030f110d08091504030504030b0402060904051302040605010e0d080c150711070608010b04142b020301060503030a050318010e010204060f0210 77
    0x6040c5035000800c1c9284541d8402c0141c019488032881d004180401071100c0c0d42d005038030401c030b42071104a591000a10f0b034806025103500c92405d0a00f124540c004600400080402041b40441200e40d4480e640b146441c030b100e5012a4030b004014880a880c0c480b0480d9605c0942c07043c0c07100c003055001900b052a0249405440301c6103400e046031a080c1b55101c00400980c1c20136400c02c012500c40c0c1307642c40f8152144ca4074240b02040d41c00288108810b03160907a006904010707000f4101030060f03a1700041e02d205940d11080041c0d0380e690054034903041400c48070790405207008220400c090240c0142240d405010742c881a218102e07264181510101030a014500189401740418400d05601a1400704419401441815507500f01803442001b41400035040320005001500b02c403c41c01c00b40614005810102c025500380720481c10020842d000c000c00c0100100d041300d00c0aa075040c03081d8820107803000100000e541d52074030b80740c0142034480441c0752040140300e02c18100384026164411520800e5559 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 222268552 1250 222267302 222267313
    0x3030a08010e0c070f06021c0504020a1202040f060b03040215040e040807060e060103110310090503031302010c050d02010c0807030e0c060d06050405040f02040c0809030922051503061008 82
    0x2035186054188002c0c91020001020013403000401c1011060307802d0b8034402c02002d07aa880c600c20b451001c103080c145003003840d94100010302006a0311101032000f80c603405403045091148900016000e07011481207008154034060780450713a01400c6005620490003555003d440340002c07078a40a03144254494035403003241200100b8006070030b1a0082400380d0054001003407400c001c10322642000d4081c0c4c021590100c80c038400500e80d0405000311000c000c4000c0040040c0ca10b5910354036200d200c01026003000000e803490100c21607014a0b2917180d5070390030174222070300442c69241c00303802040d1404c801c0020404980028525a00c00d024a04070984500c001c0c0c00c510b034002052000c10b4015421400f0350544951021030181c45074860a40701e1130217900f50346400d65060043c84211403503001010100409141040b04080001003160100d550a54019585400d80d006001c1d40d20a80c000e00c1480b54181420f1150494900740e102c030b00403e086050304c03560f0f00e0310b00c0038912811040c03140102a1700403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 222269802 1250 222268552 222268559
    0x5070b0a050411011b33050109240302040905070b030109090c050f01020a0b04080d09230105010506030c09010903150c02060c1e0306190305060a150b0909040f02040609060e0603030a0801 82
    0xc440185460702034141b806450140413240c2803c007201040d55112860755180e004000c90400c40c01000d501c16404800d024038424080c00d2480001410300001c4e00454513801107508000041010038020404800e4280c0c99507120403824018042c0fa44043e00c000030508008280e0340341000c40c0320002d60058000340f00303258440d510b8105541004100343c0395a9401d001407a011001c1c0d0082d1440c45200f8840d03941c1c40700343e00c100301445400401900750641c1c9010018060740d00c520381100c0d003220441c018075840b9401240101c1d4001043d400017400307004014401c40c41c1040d1a0080205029207800382c0c1c4041c0d070354425800c5030780036800001211040082c8460344d00d12000d001560005005001c40b201c0c039942c59148031090000e82d2040b21b107a071120040203c0701c0349a106121074100201c02e0803510710307e00450290036010322034030341d0300c42c01022011904010b0415000ca18050740a0014444143e175500300724000d19441c81040959901c0e10001019450080106c1e50030340010b48814905909 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 222271052 1250 222269802 222269813
    0xf01090e07050a1220090711190b04060c1409060d11030c04150801060504060e0103090b0c0913020c06041112010f060603060b0a020703060c05070b0a050411011b 71
    0x10301036034900c841c0a18040400c603502c81c02c100d40d001d8681880300d4511000549014081d60880c941115461003802120501303540d00d80008541002c807038540542902000d504550801c520b1500d00754850440d0300340d9004208054403801d106a000c1d2004201140e190a001d464600c60b01108410240080003c528540b90181c05000300e0a40c40c04002101c09900421440561040d030381600c900c580413030100070301404c1c031a0070342e4103540900d0b042c015940340800290160141d80a00410f100d270b0500400c039a640301c4d9000d41301040d00100c0c600342e142000707042c8083c40c2d4071060702640920000003403655126490b00890710392002c1c0c1b80040049070f881da2034420340c204100c13481a6001d0340d0b507049003100303146c2401161691a4804800a01d040c03a16001508443d4241c0c401c40000b0000c1c09140300103034012855030120780d0071a1002c6054410fa2008940501c07840c074004240b04014014003019824592007984501c0c80b80540c042d4803280c403030040d500b00030b41d04010b0495180140c0c3c4540002c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 222272302 1250 222271052 222271061
    0x40f0906211a130b09060f0108070803040308030a0e030304030c02030c010903080d0f1d16060c030206070e0103110a0905040f05090d120908031e0a0e0304050f0a030c03030c030311030f0109 83
    0xd000c1e824940300310308030b81d0321142d078104e0650b402007482c0d00140911a20030050301d401801800703090001d00030b9601d04a01180c8074007a0344009021503401100181c2d03040032036000780161200b030500766943c918203403801500040c036024050f0b000784103446d20f481d40c6500032111042a60741007241c16040400d0444103401070300000c040c00000940700d114030399812850b41e1480f10158943d10142c511072003110029000280c0d590f005004202410400001194011890542001007842c0000c002184140183c0c0540800281e14040800000e03a11140030f038880a06801c0d03a4045030240043c181810b00c81b0300b650410b8a554440d40c00ca6040d408980340660801304083e00800c1c000b2403407004a46511940340c01c22030309075403800100c180e180c0740a5800d415282e80320740701840c100038450304800d200fa640d018a0142c140201d001c030000c2040c0d0764500c1c100c0d000942c1c0c010013100308a030b241d2070000c04038038407560f04901007400c100020216030300402c150b03845130034604001b00b4280e2030b1101140190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 222273552 1250 222272302 222272311
    0x90409082a031b031210090b0d080f07020a030804060309140304140108041b030803010e13050607200708010209120d0c020d03050903010c0807020d03020c0604080f040f0906211a 78
    0x1c2c4010004d17402d04100d84250706108400340d841021903949030107110400d0340c848802d65032248032000d981f01c0005640300c040e80d400f00d418000e41b68440400d0f1005c2203500441e07800240c003070715011400107911545600304545140c410a240034084202101c040e60b43c0c0901c1c0540a10f240c4001c01c10308040d4400c60a5a9105000c0c0c100118609007401c5060010f07840303600203485041c0000014032504203040c0d803940e00420125850001e06c211074590303503290407000d000700c81002440100351107007508140e0001600f070382c454182c842e42962007030124000c2d0300c40c180ca1405501c02c0ca82d01c0a02da04081107a213400c500e5a00d441100b41015402c220070084401800c405000c000c0c028902244c42c2449841040e00180d10703041580e0802e420040c0c0f900b00c801e10014105401041302c00d001880208600703400c50386c00703001c850319014440c207100418021500412004461540002003c0040760070120442e24001d86181010074110001c0c1c45049a1485c09010840c800c120308402050744c41403954007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 222274802 1250 222273552 222273607
    0x1b180509043e0f1807020a050f0f0613050d1202070618110406030c03020d020f03030a08010e060d0308130c0815060f0a05030607030b06090409082a03 66
    0x14000000c0e04560000d41c0c50200d01d00012800741824510300030100005582c1d000702c400403030070480c94000a0288072208840c0f941c40090b100801d4829000b00071305018680d01906440c1b0380c401c60400704d5076420101840c0013542c4110703004200780443d400034680c18150814083c2c131a9004884043c2e480e182040c0720a5502039007004000d02186407441241c0b065800102703050003480d12401c11801354500c44100e10b120310310f0690104000784080c094030b41143c2d4143e4a4012844175030001909120000300b01c1e50705400002003110b1280d510440890585281c01091940c6032203060034840c44030070b082c00003400b2900040206010700f2146c5ca0103a000f511a12901070b1035920f6000c402e050103400c545040594007050188110f500d880f40714155010b03c00d480c4202a01e25050001c0d95035440070380354200b8959950240403d64407401e0440c1c0a1070300c080c2c000c0c04680c8207443d000005078030842c003503140031303070955440c0501c4250000d00c00c0c5241c05010046080084d01d00c003884408030040b42d102e00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 222276052 1250 222274802 222274823
    0xe1c05191a01060203071704050f04050a06030206040f15031a09061518030f150403050d0e0a030e0301050a0504170c010f1b1701061d0d14011b18050904 67
    0x70355281da180801e000c0c0106030f01031611080145460f00c0641640521130600560a0200340703e5070303c0b0b128252480440454001c0b8941c0c031148140d00003049540c0003c1e4101c1000100450954001036644040300e1903c0039240016030000c40c11000c55103045000c000121030769026101c5450302042040e0092001816a02a40c05540344a41c80c0d07409800e0041201c118400340e0082460240454124404040064110042103011501d81c15400810080500401060410392180264450400c5460510468580d204141405010b0101c440a50b92096007050002180c078441c074000c00707004503031041c4010980d84070050240182e070003181d0159000d65076040100381540c0706000705a072481c2c0385081c0c140a04400c1100401c11103803041544515030b00f1600400c042a03000b032900d0000c14075201440140030222000a00d05a610707100070f003403d511400d07051181941036001140152102c004080c502d0a40d038400e44480c200035045030519034200b2004c010380d08204081940c0507106032400320 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 222277302 1250 222276052 222276083
    0xb040b0405090106080f03030906010312050f040f051e090a02090402070204140709050604030816020604080f0d080112052116030903020307090b0607120302090607030e1c0519 77
    0x102101c000319298180383e91161020000c000080c029120511101d00185295141155030300381d41d1441880000c0101c0151500e01c2034451141083c1c1e0910b01d2901e0306160348503540e4040354203554060082d98841d8000c3d03800e400921a1228604003041e1001e404c021040c0e03110040d120080d0000a00b46c0e8000390200303c030800507a40c6106505460f805281c3c158283c1c2440040102035180340e401c61406203200f00003e2020801e81c034191581d0300400e010b0f000c03015800b480407510074016503008140c948034443d201d1030b42c840d0109690342451103d0751040703900e80e80c5280d03101034040d00e2040a00b03590810800c0f00340300c44000ca000011b84000c0340000c1e240038480c4609a080700340f1035200350009a5030310018811840d040c040c420003441c250005026407500000055450302c26680010007028401c920300400b1070003501950320203080142190b4035400c45040281c848200ca6801034807c9040e110040d2440d0030035002d81241075003040041c050210f82c1840c030501000003800a440801d201035503a0f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 222278552 1250 222277302 222277309
    0x70816050f0d0213140f0f04030203190507080705100c05040f092a0518010c1e050a0b0c180d0803010b07080910032a050901031d010e07050a0603110d0b040b 69
    0x20a84141140954492901c8100c2000c2c01b000030301040c403102a18814040442c1d40041560321a41a05582c804444051501a80c1c541302e1031400502e0503002144100500c00c011861240d00001c00800303000c00e4a041c0e404131514820780c065207000c081410010305c16400f40da03200582e00817504804000e45102408030750003001e0020800400030300002088041003071007001580b102e030020309055a02407101c0d0b40e500e0211000044821a807440d800a11060010400030043d660b03402c48a084000c4c205003030b103c1c80c0355210414442c0c003c0c08400080313020381070282040f088150440c421504503424460f502049500c58002545c42d484d05020496030f9640c1d1180c4c0c041c051101361070004841da52003448010b0300c00f103446c1c0c2e070f071058040740744079868150803908861056100346400544980510b081c440100c402d0341c1d40010340c1d0700c2d001c10603a04900004480084d2072045603050f5199544003c118180ea220090314031800100380417009180d016a042490b0464000f000842c49a030f032480170 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 222279802 1250 222278552 222278561
    0x303070203010e03030603071208090904030203090405040506060f190b07051f02070c050409020d02010f0527120d020a08160503070620120c07021809070816050f0d0213 74
    0x3d400581c000000740642840c0c100035000090010030400d01c0540003640301c82c0464010300000c14060071501c0c2c0010101442442280d91a41000f001001282817034100700380d507400301b212080d0159a9882d0007406e28a01881e00b0b55031380201043c12901070307007030030402c0c009904150b1044800b88100b4078007031100c0c0001c0781aa0b95101014200507151902802c3c82003810700d07a030b40124040c0b85001c031280c0c05620ec1083e10481d543e028244083e44000c0240210b40ca88114018454030702c40c400d4411000d410b2803142c0c00314042088078504201000d0f040f40743c1e15904600e0311040541d101700e40c58000100b0940180005c034401d96180c1510314403a4135a107046501c072800c21544159035020151104008150508207032000754203140c1031110a1580741f00d2035101411545010802103074010465030f5400c1804040708452640781c0041c11300c0c014003940c811281c02461818040c160314460113920215081041b164014203a046001003034040c405c801d00915016038000594030341048034461700c0d008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 222281052 1250 222279802 222279821
    0x60b0d05031209010b01030204080c012007120b150a06120908030112050d020c060438070308070305070c03230f13050a24050c0607080717040c060e030307020301 71
    0x30b100c20600d0894411801c5405100405043c5807043c0030600c140301d00060b1044c2e0100003800d0100d000d001200441c00001c1034000d80e160079104602011034a0780c81d43c000156101d1140c001c8dc005600c0b15250429898800c09589410243c60305040040b14410300c1d01c2024841000000140030500d91a48100f59100340c10520699410101e40b60030001c0801c48008022101d1010b0f0401f00c4070800003400ea8416480394003031400c12100d17407000c060410001aa40341a040c0349054480208a400c00c1c60303038100c5081900131840351800034440318002d008407413080805980744505030506540030b071204640c042d110b040880311801301c814081d10250040280c20f0b1700315403031501c5074503a003810104094036821182c0100c100103000c201c50f0007403040040c0b1002452100d1084041c41802c1203030f0500a5590403001481000f0074032003c01d030000785403401060590358001c862920340d507241c403191505440043c031034000c20302d0420101e4801d516400e007612008040e44d01c1c1103c5e40c0c002030300750b400994 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 222282302 1250 222281052 222281077
    0x307120501141f08011202040b0a08010519020306010c120e03070e01180e030a140c06100905160c030e1903080a090509090a03050d09060509070306060b0f0304060b0d0503 75
    0x46202450181042822100c5080c504941c0c0d60901d0b000900130310062081c04000c01500d040e1b41c0c1150342c0d5030818400300700301401131610141e40c0d003411070290006961030080745a0760345542d03110b420180201c034402c90f41a140d02240900c16554900b43d0101400c40104100400d0308071f40c82942e06002c2c64005043d07a29441e842035041c405846080c0307681500c02c000b80d41c80c0003880d401d60301c0b020040d51001159802d0605440382308100c820b01901c1b410100c400240946c9040080780d905956940095444018081000c2e6550100f4191200c00c02480c00020034501c0500c071000911810040615a00150207000e000e280044000b42140e40c42d003040b12021408181a02c54a0780030807220000c0c5400c80f0000c0039410450040c40c1c07251620035000c2c0400400041c0e120a81d11143c01040805510881c100700c941341c00c40030aa2640401d01045a2480c1046400602d080c141420f1741e02808051204c140b40d17480390b995178002080108540c5130000c081e03e04030b001150090010b0800300030042d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 222283552 1250 222282302 222282329
    0xa110f0615131406130c080c070c03050f100f1e1a0315040b0f04032003090604060f0905010f0e06090a09020f0a02160f03110d1b0504050a020301050f01050307120501 73
    0x118200120880d41c0c5e000034018901e410700e080c55055201e50400e4115241c1c2400e50399414003420b01e43c011510642024003148603400f4038802c0b4410000320013425813031680040001e281c0c0748803d8801c0c0d582c0002c0c00e020955081c40710404021460340400001e40c680c00f004801101c1142c0468108460812100101d00c404000c06c000d100001f5822580002d1121100c1704a02d0244e07400783c04c0c0403912600201c005444220040948020070454a441c00010300407030710740785d4a1100030000c03511481d501000500f00400000c0a5005200508030100c003a02c55441c1900b4120078401250041e00415030702800c401c00006203011380348010140c00158501c907650b155500c0303001914105840c28261b240b5402e014040026841f00b03140b040640394044032504640d042d082c0043c05e016007030440940300785901d25800d0000c0480400210858100b510244240d40d607024156040703000074403610ba0031100e081c1400700359611410080d0351087c5642050905140312016010446109030019000d16444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 222284802 1250 222283552 222283561
    0x13050907030911060a0504060804030909140910052205070b0f130608010b181908010c140306030309010507170f090a080f100506150c030a110f06151314 67
    0x41d030684202030031044d14590700c1c00401d150001d00c1031040e0b00c214030412681d41c0104080510034102000109554401404a00c9902d80c8002a00c80300380c07078036015485000d250aa54400d18040d641c03044800c20090000c00c456402c02140000025004544034014100e000c142c001da407030007802c19046020f43c8107844261790110407118002d0b54204400f80700c0600d0041001018000072101b80003500c030181610f4412a102040c0481e0101507208013440003030401084600d070541c0810000001542c5881d80c1c040d0b1928400420300c41621499015041007158001c503500a90091803503a11451000c420041e0144d240001a080819414081400017a801c1410b141801d074aa003e02000c4024000160002c041c480c2c6e40c4070f440d8110000c49850328000355559903400055001c449118441d15603482d00106c030b9a80f294080360112001c500d010b11030b415615800180881001c0340309008201d10f032511003217008c004601000c440c1c2c1c03080c400108031005c7c9420340500b0310507035880d00c000340d01e5091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 222286052 1250 222284802 222284813
    0xb0c0106051816031e0515010f090b071b050a080a05060a0b090415180f17091005160228060503061309020f04060e040b0105010302041a130509070309 66
    0x291496003086400010180f01d280c11410f82c45000600c4503050006548145105501250301015501d02d50149003508210400c130a44d0700200c02883c0c260b0303030501e002c804102c05941100040c05480d030b0b50301090103940e000610304114a407045044107000540195034600041105d09960044a46500300701111010000700300045c035008219031100b4001a000e20780800c5c0d0f0820000c0000c3e06001040040040d80e82d0164802007040d03c10303210701c0100c81345a0a10613103103440da440c02c642104269402c45020007030241692910320f0010040c0c40c0c02041c2500c1240d00303801000407500d862070310588190040e82c40c81040c0d405540303d00740d004d1351490030b400f803004603804a5002e42e05104042007009590f0360f0700c5920620b80c0c400d01100048503101400464552003884d500503421502d0f0a4005c00d80b00114826079102d64818051000e2a83c0c860004400340e00030b511442908403a112400d0b1400c40790000505144900107801011035a031325400116101000e48034040071960b0b48940a06000c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 222287302 1250 222286052 222286069
    0x3010605091f08190206090d1217060d0803070807091e03030809070602030901111f1d01020f090d02030a0204050a06080c040204050904030305100e010f0509060306060d1b0b0c010605 80
    0x2c20307501514004800f14960b01c207130796203940000e00c02c80b00064510000d60b130f01c201007109140c0080c00e16111925540303000e064101e51080950710180000c1c0026510b180030351051b00e20b20703806100c40b41503440b07042080c0c0751608083c15060920060010100d011910002039800d000c49802c041492a840c500740984000c0c0094081a0340380c1215009000a640010880382c1c05034003840c144603040c0d200e421380d0781498002807981002c0c0c8401098600d0942458101c050200304440028410000180541e802c034416501f05c0c902c0300d241445152594034081c6942014180094259410340086900003000c03550202c945024455a0b400140b0042800308240c00b400d00081c0c1d001c52400782441d00140342100300900050801d6120800205043c850720f4000c00207000220080d001c55071103006000c4448001e0103454055520368000404500d40054514000c1030003901e82e19400401da1a04501e40081c2d1240c44041c018298002503101c80c07079001030605074003070310001480b9030400c0704205129 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 222288552 1250 222287302 222287309
    0x10050f060409030e060c010605151e07150504030e060d06061d1809012403020312210603010b0a0e010e09010c140306010c1e0201030b030303010803160203010605091f 73
    0x76440c14112a00098001d02d449454680c1100c2998a40482c06001d034050401504000c1c0c00428004e000d11030403802001409503981c3c40b07010701a001410841e00c007494018880090300c21960307584603481800307056100f90380040c02490025100b0080d41c0120308180d024000c2c005036180e40c0c0c102044800c1d07000355030303251010343c4840340700268000390000381001e02c848101e0a16000c0c1e080114541400075800040b28070a584025007512001401d450300401852105900074044c09500928503800300b001ca9074400d210250600103c107000c00510380018004007165010b40da51000d80750103513505054480144044410410030350b040086c4002161000703040c4519680c1455145014030742c03c54100d40d540440b131098181c0740d0b0394400c0104d861040084016084807000e4400f11112120064114050750007030b00c06100e6102e1000900d0340da4442441a169150828030803003045645650900c55120300050020074203e4841c2c00141c25020155210229101c544146000c042c1c020000078004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 222289802 1250 222288552 222288559
    0x501020601062c0a0b030f0c04030c06050d14012601020304020303071b05100e100c170901030f0e030301181b11031207110c0a030f030e0a0810050f06 66
    0x225407600b03001424840140c0d010100c1d0044604961030300d8100c454a81d40110070082280e040d0559030304010009030b00c00d071021984c0040140000b0818000c2c01d048404a0382e00070062a04175141540850b02904040948044661512540c11b00e8400382000c5c40e0107007007420542521001401c04801456401c0242145541d0050042201581c1d021080d149040c0d042818241d54107a40c240500706280f494201c1e0b9400f0007440b0146c2c0740d65038802d0201701d0358801503842e01b44810b0a0b05042e2410301c84120010600f10340007148940d050500340c0036000c050b1301810042201d00f14107803910181e540c500c403496080d5001200402501c08030802c0304207000100441041100100c01081e02c5001d500c403a514203000f40588442c00c40441003045401078400101207104604161000501c142c1952030450081d01c101048044a0f2400b8120007040700d61005040401d201e8640d070a84401f0b12203401e496020a92041c00a542c0c08140031465005011301000915032800f948240c0401c00050400ca00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 222291052 1250 222289802 222289813
    0x216120225030602070503040e0c07030801120203120c0c060d02090a051503010902090d140714040c1707020a0b04030f120506010203090d0204061203020f0f010b09010306020f13030308060a050102 86
    0x10301104000d41c2410380c0e40140340503941ea4582c0c1809032841c46103034003aa00300d00030f103020401c000e500c0001501201e88079130b407507a07917590b61103400c0c2d4082100380601a51513080032400d0303620341422500800d0f841e41c01c40150f40340200e030364000072003541010903014003460300024080b07410700c0c2086c0c038940031345400c4a45144518800e280110180014015000d026500041610b100d9031140c08a002003a40310148101c07020744080703000d40348c08052140c03410304620704105810500c1c041c050f00810031425620313104860020381c142c29803124050704070801d5002d10303964038000c603c1e02c0c0006e40c8224080e40312044202040e8400410803000b0201c0a071410340303044140b0059a9003c021240f40a604a9a100d000b42250001030000c2c24aa8018410040040c1da02c0081540224054000c91285016101005440502107003600ca140360310a600420940051000554544c09400300c0c060010526081610600104501800c3d580055000c2a03000c000c2258a20b4240020000b401d801e02c042e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 222292302 1250 222291052 222291103
    0xb030d091d07050d050603030f0705010b0108010e06011b11030d020d0908030f03070c03031b0c03020f060411090a060f2601110a051608030f090f0a05070e070302161202 74
    0x1c0c0380e806060404240c4c15180c0010840c581d5041090341c0c10122800403056039101c52b480c01d14024403e144003d4040b07150070b40009404070900044500c40c600c1a100c2207101c0c0c07140c0102e4036401d10b5100003114400340c8400c0e81c5010b920308101c1007030791150740e80080804000c03081c00a4800c04042e442401c4542c000c00111248090b11015640c02c108581040640c483d070500d07007075000c0d1080c50728020000c1361030a50450803030743c0881200e10241c000d2302070741c0c0188524020181c03968030884021740303c1b544001745c101c0319080c00322200c0c0d40500d200c0390010780715440350a5001c48a9203a444030b0030205d210303403020800d240c00102c1d2458410011008001e45510b40ea040800d0780104000003080c09400f2135a80501c1640c580c4a0014a500c290a650350b071078001040503040005070b0b202c940601c04d000e0f641e40044c40c00611506203d80200007083c0303140ca0241009107a003402441c80c001c0640900518030400000008880c2c61849503d038100540f100e2080245841d00040300c031005078411241c0c05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 222293552 1250 222292302 222292307
    0x908030603060c040303020a08092404050a120b060d080f07030e0a0608040c1502012406110f150a1d0a0b0907050d0609110a032010050a0c060b030d091d07 68
    0x106910769000019072b8842e141d0300e00190b254249011007204440d00f801000c2e540d604500014000d13180c0485000d81c40a031108036007218040c40c00700081001681d00c0115034541742085017000454410807840d031409030b80f990003081036000003904602050f00c0d86004640307031801c40400d001504c4640b4025015251a44410043d1300051241c244130f18150252402c0300751007900a004080034800f071400711002801d004900c7c07410f81d48600f00c001161550350803031181000c500f401e0b60207a11030040280400000c00141140405030030f290f00c040d034500810840440c0003120010b01040d0002400350440c0e6070906001c4e20f04010041c00440e00805400e1000f951901c00e441c40a6402c40c000050030760742482c11180140c4c0f40361410b54054584a000020412082465100c6120710800c40100d03c18100c28024a40d0004444070f010500c117000c41100329100320b0404581034003e0340701180b01072452012a0074400c1070b0402d00001903030403005000340b255140c5000ca91111000307600310f5070700e0b111000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 222294802 1250 222293552 222293563
    0x10b01050306012709060b030105040c020106152f03070303050f070903030c06110c0304060207120b0103080d15141903030e0108070e0306100315051902070f060908030603060c04030302 81
    0x259160109945903080320743c0c0904c0c0d050320103815202c004001040d150803c00030950001d2190a1181c2d04000c0e4003031007180b060003450100c8014103c8481d1301c0c1084034003510158407d039401c1d8003200c1c601d802101205083c0350060030342c81081c0003544ea01d03071882c140241582d500034100300f0303030800302c03401d2045090707005180320100c81d058030300f00780c0b00641807600d01c0103484044001072104401059041900c8000300c000c2c070803030303007107400310380020341e49050840f003100390040050410034109004101051610303008001205004400043c0860103608290364103130590070984c02c451110046220700c1c14200c002c190148091192402c0711851645d00030088800800ca045c100180103000c24202ca01600010710714900007410b6450510349001c400e26401c000340700603074184001034001d00c0382400600c103c0b80164500209491202c030307261080d401075408400c040301d10301c2d0546d19075008503600f0312070785041600c60041c050f500d007490000c05240480141c00d00182c00c60801081000030b400249 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 222296052 1250 222294802 222294827
    0x915030210050703030e160e0a0e060c0c010207060609061e0321090e010e04060615021e07050402031005040b032a011e02210918060a03080d050108010b0105030601 72
    0x3030a0355218820320b02103016010040f0720300c9003445044680c1c000790049400b81c50907a08d451444550390754a141d01c401c00c1c0e40c00c4500c03520041c0c005c136020841400c03901008000c0d0080c894000b603c3c3c9062591200c00301c03415503100e6410290346101c20f2000780c0c00c226902000c10103130580202c1c0ca50960300d0f081d1360300740c80741048600252105a1021014000c0e001900100040300d04071200e503a41c0c0e504a00410310480b07044408624211010030000e00e403c7c0d08a001c01c41c0d40d0700502000e0000703240d081ca154558a0820030360701c01e0100c0054181d8070ba00040d4890110511480c02c481c0c40c00d0280001c1d81c031080c009030312a1300104199805001031090a0b4101882074454540c0c0304c1402c80180c40b410103e01d401404043e4000e0003c2c41e040d0009026943e04040400c506141500402c83c02134500404c0e080c55480075000c95940c40c04902c0000803178000ca0002c0001c0b400a0340d90741d0b0030301207520414442e20314039212401007100b44003e100320384155100b0708106186282290008203264201c40303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 222297302 1250 222296052 222296057
    0x23130b010807110c0607020f1e030610120b0a060b2b0c02030a1407060609021216050f0c070803280201110f1b0607050c1209010507120e0a09060915030210 68
    0xc6c8102c20755540710800b009020024180c40c200303441c64698101e80e011a00328881c000d02c501c0c0d000c11114038059200c40d0441d403000f2500c1040001c1c95880c42c00c80c0c0c0016101d807040a03282c0801050a803d10300062074159910800c40d010041c0a0442c02e1585507841058030b4903600c0c01c0e20300b000c0c0940120464601110514010240f407000303004600440c0146240540f080349000710103d400c0e0b0403940140b8034010807001d03040c40c5507144040d1020003404209a8000a0000d00140121100d104c01a1004060510a4860098545d0281c03803550300f020300b8203260941300115013101180002401101c1c54150f100900c91041c0e1044031000603c03c141d1134000341c0c02d0000d080040200d14201c442505901d100503a020b6080c250700080c0309030032101c802c840601401012110f014501d0341201c4001d40113844450520b00f0380c1c0c80b42c001c545151075a24061001d40718440c1040d60740d688a8801074801000d000490505201c9030000315801d29501c0030440c18101028400760780c0d030f540e030711400b1003091 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 222298552 1250 222297302 222297307
    0x90115080a110a0804060f09020a0603020903030d05070509010909022701111501051507110d021503280b18060f0409060212060303031023130b010807110c06 69
    0x71040d14010440c0a094201105000c81c55685096100030070500075400758501303201c2480c0715540349080301d00280000b07511070240c2c0400c000312806900540315154005040d00e0903c0d27107001d02c00040d02d1044928000042001480c180c3c10b60700a0420f1001c0e1940c0d45003103080405403100900c1c201d000c2c0b60080701c01041c502c5201c1c070684c07203042a04540340e100000d8800544080000c05d008074002e004080c0f14420040c08603461804c1c0c103040d01c0f109500840c0900702070045005104080901074000d03030b001100d502c0c5030b540304004000118040c61240480301000e075150044404c509101000705416135060449400a40e96402e03a1443e03851040388107904152038007000140a000d0740c2d0000c50f000780c188860f101c148605540a091710540803590032405944110425859100c00c442ea030300c2030381c030003034041c4403150741c001150b0071a903c20560801ca1032120000210030454242c0c020300d400d9140c200c45200740d64050b8031582c0010141c140075641c506030030220307a00d9601120a490140202 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 222299802 1250 222298552 222298561
    0xc0b0f130501020a0806031014060603090109020a0e041109040b160203090d050c09090724120509061e091509101104320d02030a050601080d0e09011508 67
    0xc440c182103a004000715900d4003031500180241d42d088500a20074000d1986010040c00c0600a078880408000d440c85000d68803c01008000e410251102d851907688007641c40060f20340305103e5002d8049214031640310f03c1c081c900243c81060300c10750180907070310507424040007600740c60000c1d804c512504003d84a168215904a00c1d40c007410b00c0c4658081c03c1c11012905000380414041c554280540301d40d0380d956102403029035a10700a10442c29011028440001e081800c0c0460790b143c20a180b40405a0111010640c01920780640361411503420010a0101034202e407007041c1c1c80c5610400050019180c00c1448c641c03210920400702c0540403004d000164003113810710030b6030403998407c10100940780c48041060407a40003401043d0305043c0400800c0128007542c5071741070004421100030080c0c1883c10b0244004035031a40c1c07040f0780610a103030140c00007030701c01d0001501801c1c4030740c014180c0c4203c000f001000403196428060158002c480140300d01c030001c07034001060640c41c1c140014180c03038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 222301052 1250 222299802 222299821
    0x1a1c05040f1b03050f01020a0f1b02040c0e030f1f020d060b04060804140105060a0501030e03070f140d0509060403140a080f090423040312061205010b01020d0c0b0f 72
    0x103401c4002000000c4410a10405004010620043d01d0040c0200d441c030901341e58800e4200e109401b00361003c505180180803c480c03050b110050381110070225a5215001503000c103081e580704031841d1000c01c408401204090408100d61040c481f04c900080c1000340d800c02041c5070211000c0d03c4189400e800083c404440d19a94000c480103240d0707203820035903075a980c90303000307007032400986048514030140041c880000005000312030048100038003c2030360514040040d00104101200040540020301c042c030085a4102c101102035801400248042883c02e40310f14180f00040074408148401030003040d10985405050301e05403a0b21107009203100f2640b4080a00d4001d003004010a003c10024018000300c100b440607226910040d60184804035122407216804500c85410070080b113483c000180c0845d10511200c0074034a0303680f9000401c4c030b40f1880e402d404460480340685540e91141c0300340c0c203e9641084000051601850030790840d48265590012128000d000c030450392015074003113000e480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 222302158 1106 222301052 222301073
    0x40806090a0605090d08360d030e150606030c04050904060b04050c070203100c09050d050a1712070e06091206090705040507090b160602070803011a1c0504 68
    0x585202c060300340301c121a4401900c0001003a01450787c514990045014901180050204100102406415900103a40038691075000100b02e0b10301c0b6501d184241d4001d40304440c0741d130f525140c030030340b4007060300854210700c0d070141c0340030144000c111850703100301403584e425035040c051540d840b0f5400c20715000d55000607405800c0f43c82602d01c0050282c1c020f00703401d409420000320b05511103010440c401d0140e0130440d482d62298204000303100306469441000030140301070034540001e80f0781c13610303c0c140f010302000280405514001c29540e03950381501d40080b030103001206c40341d160b861026501e01c020b07a11030109026516010680e401c00780540b911540f000e407a4480b0840c9091410421039110780d1251740f080341192003000000d5840d000824442d4050a4655100d504000c03100c004001036400e159003000041002c4022045109100d102c0c02c5000d070030014003940c07103003000103c00b07 = true := by decide +kernel

theorem cover : BRFrame.Cov 222122302 222302158 := by
  have h0 := BRFrame.cov_init 222122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 222122302 ≤ n) (h2 : n < 222302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
