-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1945
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:15:16.111504+00:00
-- url     : https://prove2.me/submissions/03a05035-514b-4d91-bd4e-95a9a8d34b22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 349640287 ≤ n < 349820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 349641537 1250 349640287 349640339
    0x706080c0d05041a090304080f030301051509030703080d15050405040b01060e0f03070803040f06091d1302130f0b0a0e1302010228051c23130303020c0a 67
    0x119100d01940c00154100c0e100b000c0e0000b04e210250420f19001c1310a807000e480d940c0000038200700c120700070070041141c03900c00401341d442e5525100026000d601030150300422040c01003000440c42c4e0307052240500440d081030855590303013451820a0014070110f00d229503007080d045408181404c003481614444d030b500800000441c0d00b402c8040d41d000e807292055690010342e0901e40348280d24140840801440c03198015038866040540180001055030002010000d0604040002a52003001a8006c0d000201d00b00795588810710004c544a8201401039000303403255469141c030504a52040c031212031010340030050002c841c01000101091442419400c0592902140c42c00701e00c03a21701148180b05004480b030265048024030390004141c4102020048900c04400c18400c0601ca02d0340105181811028903500108003d01644800710381148a03909544001e5810304429084a100c10342640940510710b40da40f400940e40c100c40701009004044002e000a109007855542003050300e840c00340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 349642787 1250 349641537 349641547
    0xc030f1e0e030409020d020c060c070b0a02090307030f05032212060b0f09042117130606050307080d090b12160e0a1212020c061806090a0e06030706080c 67
    0x1518060407100308201a02d00003000005090b070128402400520084000075031070310316000806040500050260700c607080308200d2400000d081a40e01e560002c9036820050304c50102ca4007107403810340c16800060040d440911100700307000d0000090190714410001e110f01150031480003110a000c00e12505841320145040040081c0540d00414003160024050b110342c078131030342c2c00500c25200589040e14000400ba10098234054440c0e010042c0c40c500e070a00707401050022000b1380780782d50000e1800c288034061030039050810030303240c0140307008100040c1210107281d1105912503c40d070b40c540003000843c0140c84000741d45041742c03040c1c0f01c001d210b103c500c280c0303a1340b41ba034006403515072a8220402c000441003d032506a42d0302d9100c00c05400040e035078000e071a11503e014040607850b250908155400071151082c9130b44d4100c2111401355514000c8130b0884880c81c0403650900402c2c0045500c20407022010a03041000703c0c0b004d00ca09000c0b000c895006a54800c181d540c24400e4035040b030715500c1001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 349644037 1250 349642787 349642841
    0x4170f0d05093d020604050c120f070902030106020d0c3309120e01020f0a02240315040b0d0c030602070206040308070b0702071e090c0e0a06030c030f 66
    0x3a0066110251290070201d012061400c02c0107201c02c80f107180a00f04002010078094040c01080700e0110a000070400c5080c19181c1590303031402804010f20070301e9941404d200d02e040900104070411039039412035034003a4075244140003a420901076000144241084900700a20620082d465180c00c00d1000130f2668a42412038480d50102200166841303a00600300342901441c80f903241900c0c002d01c0d405501103080ba10081540f0017800c561030456010f0101081181d8000c648031040540c1281d020100c1c01d082c19000d404003002c82c00c280504403000c42041001c00da66605483c2002c0111010000e0a400c44101701101681c03800141c4401d602020500c00a0407690045c81032500003400c16041a80e6a502c0c1019540200c6049480341e440000b401400d50b01003215001400031003c040e41c0d40c45d8105262250843c441c0700d00300d13080c2d8840d622140b05501031505404140350241c05450503c0e141c010250150035002c81420009140181700e05a691152240c000010034030b00c00c005400810b61 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 349645287 1250 349644037 349644047
    0xf06030705090c0912030c010e1209090a0c120204080c0f0d08031f03020d08090909011e1e05072601050d03031e1a120307080702061305030706030204170f0d 69
    0x100034a81044c001c4a040815005c2040030b8841c405240001281c1040c031310a00c0e0342003e2401c940124041c0052000b16860b03600e80900e10b070b00000c1c0020029040c400c00d001140e80d90160540707000e045100190120b48050301140c120304200050300c0b502d907000f24141c2808810780c00400f000e1700c001000c6c80482ca0010380b8412010140035a0f5089545054503030700081c0400c502100c0440304040d00140109a40c102403000540c048020002004108054011380640c0700410248032146591003c0240304245030701342c000d80d414440c0a04102c1c910b40b1000141a40320760320a05252a880144210040341d81c034013000c1d040e900003514465030b49550390b400381c028018078024884254103c1c1f200368542c0c0d1140c440c4010781c1c0015001c0302c4151410b00c0511040ca210b15290402c1c1390401c002c0c080118100310119140382e581615680e80d01d84d41080a00903914594110b15854010481c002828903810f0700900b080e03d030405040440d442d00141030b071341d50b001741056050381500180714031388a0038012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 349646537 1250 349645287 349645297
    0xa090906110307230712080702011808030109020f1606020309060c0703020c0f041d010219080c0306060c0f0109060f05010603090203150702030904110d05010b12011203090503030c060f06030705090c 87
    0x100700160038010142e6500c01c003030155406c6100000d201c03004000903950b090192a0601000d0300076016100c0c03542e100da02851205000b031004c1641c0010300388002942c0b84041380c5400441d0005200616541d2030048042e40c0305a074000c9507841100049460111400119195580d15400034454000c0318424008132035031006110f0f40c05642c03078103031100c5900700403560100500040700060b61280311160300302d0071092450030b080030403940e0300800114241e18801c59070054170454409469403d903000b02c40c54540d8a00392403c0da54203028074901084a10b070803506103504610814801c03070b0f0b00c0340c01c11401c45002400280d8142e02548900014054250348580c009040c0c0c0306582c500007614012809407501d100078411804c60001e12005050800c1c400c1502500c01401e2880c81e040082c14880e182d0036040c01402e07103400008007c3c00030140100c21420062a01034140c3e40c40e04200c511064071351000301c5071101e400704210001841d41c0703804504101500d40042110009403150408000c4c80e8000f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 349647787 1250 349646537 349646597
    0x3020907050c0d0f021e1e010603050a0f02011e0e010305190c080603060a020a0c030e0406090501061d0a0515031308040b0c07090605150c0c0a090906110307 69
    0x81003101d011400b00601403080004002d4591100c0c41c103004000910780300001c40d0042c401020920240b4500802181500141303041d440b40c003031b2580401c1c05c8240106165440207001d48103420b024010410f404019103001c900036220030075490900c1c6c0c81310141e510244900000103070480340ea2120366000c0ea02c00d0750044a40c030b0440d80401d400b014000115464404080d0102e84c080c0200205441d040251640c09100000194204081e090010741040c11407640103041c018000410481d039100d650090005040881c82449196503c1001034112020703039135040760052000c200c00e103060030b00103094011146c02415400740440140796641050304080c01040c1d119003000c10380c1e40440c00200140000d045420615680c0e0041e1004c100d1500456511022440b4205402040300360f482c02d11940f904d0384000d0302982c1c1c0d41c00c090030041c1099401c0c1d0100d68401c02600c008038000060790f2000381c03898480d050400110301e920380b00c100c05000845400700060280c03d0b01010190811924044400ca = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 349649037 1250 349647787 349647797
    0x109150c060204060507060b040b0d1707120c02030f070b0306060c030c011419090b0f04032003090f0604030804032909060f070e0315090c0301090b01030209100e0103020907 76
    0x2619501c05040c1c2c1d002d944003000090000c80d4040a204d80344c81002881e8504030f80402c0002e0111000c100031070f200001c040c01c21b40c0d11103180d80d007c00e0b01e0070403506155840311441020004102001d407204440c58070070b0b806841043d00200100f03200143e280c0640d0640c0c1003507411a0380340390401645078032410941d0180d0200340000d0040d0301d4240074030700041d45101c520034490728200101c44085199032404c1c030a982e0030400c00c0c2001ca070004440740c0e0096103400c800c0d5155a1207090a032920050350030402c500007000074082e1031403103000c0050701c0d81d030f08100c1d4056031502098040144900840c080a03010a00802c003c100150b8044403051104c01224522021070380d40b0801e12044403402c03030ba8000035402a40800112005444000b5031001c4c450800313046601443d80866940c0204804111011000102044c0d031580100076811004800600a001140292500300c45090007032004901604c1140081020046407070700b01d400740d03071030500d1400081c0c3c070315020041c1d052005448801448 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 349650287 1250 349649037 349649057
    0x301020c01020d05060130050c04080d0807140c060a02130506040314101b2d02240601120c050d06030f020f04020a020a02040b0f0405160311040302010915 68
    0x4a030a001401080740c0101e40066185803110003d00740e001410120207540011004280b000517800c0100d042c80411789a0010301540c8107801c030001881150400c880038410300001108066004151510030314282d42c540201e07069000700034035180110861088550000d00001d0310015059000d00312036042a45003c0400c1c0c0c0d03030800702e10985c0c4181c01c2602c0700c2c0c8a10400007401130081000c1c50702e295541c4410403003c21604154850206824400d40801c803007181006e480b44c50b020084090032542144900a000348600b0281d1365141504988002d8400d0b941d52640e050011001280714690603184c0b0030844102d0070303c59005000c500301c40e0060060501c2a140c3e41e4405100780030207584160b405212001c000d004000d4041c41101c85c0c40e1080c1e004200e041030990340801c8176403510368190707404190300300000005034001da51010669042450042044a00b900c09242030304038800584081040070689240c180b2588110301010f4085041c1407003c0003c80f0224480092651503450300014079 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 349651537 1250 349650287 349650307
    0xc011a030c281703030a060503070506040e1005030d030c09090b03122101060906030b030105040206090402090d120302030105100e0307181b05030615030f010608040f12020a111914030102 82
    0x140c6000c0007083c2d8554000300410030891520300c80c0f0070260030b00b10010a8220701d070000044480c0f080e401030010200300326000c03a003a1105c4000000c0a400001d080c0c58003034414200007030081c0301c1d1049100c0050804140010f842080348078201448002802801c00e03594100b0a00416500030410700701441145500401401d8242030142d000e0841a9280d5604500d030240046c03d40c0e032811605842640741c00140001a580d240407214042d801362005a10740503c0e00000781c0440705800702905a00400d4484202c955159000b0350582d4821035800c8804001a8000c448030300002c110b16800d9400f10383c090019144441a841003e1000138010400c11303810304910a41961548010001c600048180305440c604008d4504100c11002d48407400c6103400342e4103681340d002c10b201e00300500c0604c0000c9001d101041c000d5000207034209544040398013500380001e58070301d00c40c43e050350070407550910300202d032400d01e0120040203020341e260700070642071002c0344e00620312440400e585076508018540c24 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 349652787 1250 349651537 349651559
    0x702061920070501030617072105010515030613030c0807020f0d14010e01090c050d080405061602040612080703030e070f030506010e0604141902040306020c011a030c28 74
    0x4440e9980142c01ca6500d04000501030702c050b80c00410b602a80740c40401003030400007038440200d4900080315194484401982400d00e020314070081d016500702410803010788076603d8a00c60015056080f141d0fa9640c1e01107100544d1189034001300001c0c0d0340e65141004c01c04c01c0000c5c118440c001000d0207404401500000e508094503002181d411828a201c0300c80c0c408203101e60210200e03210020300505095076100112021140a050b104000d051400410710082c07100b50b801a010107400590385e40026005400000c05d00b0300103d00c1b4034140780c1c010441c488407803069000240c0c40404207080000590b41074010700040c1003400c2103440b50101c0020036124603015a00114010b00250655504140004159020046c1503a02803401c05c01040e00301031701ca4004540c40b160400c0c200c100407488482d8040030307101d55032010341403d00102d6004554030042d84841140005022124003c2c100070081c0768607420800095a40409600032010094500014241e044601301d0110100035445d0001281c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 349654037 1250 349652787 349652837
    0x903060506130504060c0908010506060906030a021308160f0f0b0c2d010e0a08120c07020d030302041503060305071809080a26040803060d060b030a060b040b040207020619 75
    0x5e04517072500c082680b0142c01450a4001c0c043d0762009003e07503c0e190020480d544244a1050b0080c900000002c0d80201c0550580d20302d90400b902040089640d844820b9440100503070340c91400700620340009101c21003035115011640c3c503003100d002142c907208240611b5007280000c0c801c81d0003078650707103600401c00000315098044c035007007080d03210b1034503c44a908407140c0009481d042d41c030145600004ca04a10161542504d00b0008035070b50303907541445081e243c01503101c000e402800c0305011004050700343c2c000e4001d445124071400015503030301a04a040d181d603440041c0c040d4002080c14010210f003071550016040441c100800ca00f025a6034a01c1258450320b081c80000d8250010b90140710b0500d0051400e40003d0340749000d050401d0341741c03221544005040c05214018100b242e03020030902e504600001c82d0010151120700040f4248180503004100c40365220364500361403924546001d100b6a68015000b4200d24140581d04113400c440d05c0c0280c915505000906c405280440d100c0780d2119 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 349655287 1250 349654037 349654043
    0xa020c1503090106050105040506160c1d0a0e01021c020307020139050c100b0d150507021c08010e0408220501021005061c080d020430030903060506130504 68
    0xd50303689840c0342e0301400c40303099070001410054200010000ba6480d101501d500122840300c2ca01c030003603146000c1c6214500342d80a41103000407000304070300d81c1c89000f501d00c1c4140072021051003440401d2074014200e1292462010b100c02618030300803240c1200d036014586c48080d074000060140029076201c0708600c540203c50885e070740f0b81e0008200c450300034003200c000f08000381081414039100500c1c2540340c4000451013505130350346200805259031070407500031103141c02481300b155408007414010043c000484002016200d2905280a10241d0700410b0350749084960303039041c082c2d01703002407500a450003030070980301940c050000103144c0105c01c00c4288508202030381300342400e1521002a007045410011980071510b04801c22080747c4402d4400f0b110b100c45958001d40d10650fa16012400e4011030007030b60481c40c030110380400c0065007080f40094865003101050b0914940e440456000016010300a00203444400c0400014036190850394101e40c3c003e04103c000030782c481c440340488030111419 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 349656537 1250 349655287 349655329
    0x215100b22050301020c0f0d03051e07230903011b05071e0c0605180405011805060d0b13172517070305070b0f0906070e010e0418150509060604020a020c 67
    0x35061f400040000e111000c0140c1000d00881c588101888140c2490010108140c4035840000d080684910060003642210b03482d0701c9407440740f04144480750f40104480a00962800e190340d40e501900340c14903003604009569051422400e035072003281140c40c010703120110040c403100c0007000a078240c40c041c0c0540140d40d10b09071500c411440101c03e0000030401e150080f0b01c0d0078010710003c1056008401044010000884c2c80e03160040821704086100300050514607040c010f05c2440341e01000d410242c0390103007000500a6418103440d071034901c1080c04144c4000c149408484000c91311400e007114123800780e05215842003140c54034070282c0d403100300704800107a0300044076020000d0010009030803054080842d01c9c40d1a14014055440e00302900c080c09020028842120a038815445005881c0c0050014424440d50a032601c03401e044140c0110350180c1444018868051a440b80c0ca2144040000915950700d5280a0000a40c0701070a400c2c2140142201c120481c2c0342c840c42904c401d2200a18 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 349657787 1250 349656537 349656553
    0xd02150301081c0e0a09051306110306040614060d0c0207030c1514160206090d0203010608010b0418030228060c0e1207030203030306041107050d0215100b22050301020c 74
    0x10f40302e81d518045021506000c409164090700791a4020800e09540b440d000c000760300c1d142d024502c0d00300540e150004118034182000d01d031080c0000000f56000e014203070f03814050540c42e418030b490013001c5c01031180d0304100180b0034112542c806400411401406006071b464094423500c4842601c03900b50040100008410245140e1650080e490171185024000d6581400d070b4400094008615820011348151008035602c113a99443e88814088903500600800955580700c0d0b4007030203040c4c61207002c1c0c032442c50079007211000c100c1c41071040741d020380c1507010300b210f45500030724010320070044126100740e120101400710018015124010311440640c4030300d44010502d03020410701031041c03c075059580c0c203e81c4c02000143c800005583c0c01950840c0d012604100101c0000e41900603100060214402c0300c1d50f00c4070054011410741808461900c1e0742c0000da40b050328185800d2042d200e0701d07110010030800324440300007022200401120741e103645d0b030b59581c2d204006400c2e40c0105080c07070055002540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 349659037 1250 349657787 349657813
    0x8031003020f0d0b0412180e0906101212050904020a030905060c13140f0402070309090e0303010605030109020703092601061e260d080402030d1103090d0215030108 72
    0x3030400c0020890710410243c4a540d036110300741501410042840310800421070600e8000c414007801d990106a00c2d0940e55550034103640d140c0000e646401c5503000d946c020551503800b900d00201641c62150505200500959405007a244122180d0080103c04d201d88142560359000074440d500441d5408240500c26040442c207080c00074004a0342c2c0c000c100724504101c0303681d69070301048801d1401c00703450300c50300d01000c079003050400d95032154014030004802d000c040d008441641070321205542004800103510b0040e5491000b8012003000c02c00900041286226540003040b68078824941b10314446d0b9520b0120002004004c0d0b03880d0041c6424040e201c0d5610244501e000a00002d001c0d001e0300c0e0003881ca1030301800214050016a0161013090701801b01c882e5411a64803158882115880340c54110024400041a54101d10038005c18040300e503042d10440c2a051f00ca01c04802443ca001518000c1003200900500101c0e00400200300010701d00d101c4002550003050500c0150041103a410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 349660287 1250 349659037 349659049
    0x100f09020910020d02060115020708060a0203091006030201020c151603020706020d05070b010605070212030d020d18020f0402130503060c03041a010b0405040f0b03061e0703020a080406020708070803100302 90
    0x220b601086501155207501c506a00051090440f04924080c0340301c020707160401c9040040355003110034184507040c04c0c4804055241d00841c45809980c0c04c0e6458503080412440c181d6142c0e11002e030060f4410030101100d440d1000c0d5407003c884055540c10302c4c2000d449140d0200d6031074003205401580001404210882d01440000f000450501d002d038540030240d84c0e2044142c80600a1900700100481d421085403501c1c42440100208001120340700c0c0010441e2401035400401c808403900d0401316912a01c4140405103095641e0007860201a9803900c000e0000941201c20780c0800d0a504410014441c1c40c00d00040d4019002082c025070389280c54144111030b1346920070300d4280110500010007203403c0200644054502c01c840c04160350040d400c4072805130200404c01c0d03a15026600074083c000d0f015003840c00e000d1110398400a082d075207411041d8128060003451038042801200014001042a030052410922400040d4113061844d00d82015a40089498402002e0303848400d00551a1803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 349661537 1250 349660287 349660309
    0x18030801050a030f0f05010b120604110109030b0a0b13020a1d0619030b032103040b0109052e0e0403210915051b03070c030e04061d100f090209 63
    0xb6a01203031164610340e00e26001d0070749540c001e0720220241c410b400400000390000c2103280002801e20244c21031103a070040d210001510704840c410a1541001d503103500580c0300400300d03a0028640d003110ba031560b21000c041c04082a443d0390020b00c5920000d502400762004d840750302c84d1655000e189000c400380105040440f106030354802c203000e01c88550700040da04041509802d1500d404100418414082490400000b10f480c00101e080d5004460500504020314451070003005078100c56641c40180708200c0c0c42c1034800e4015041c004c080000159103d842e15416290045100403c56a9403081504020425581100040c840414102d40c00510524451b2891708410341005030195950760392070351500c4d00b00c2c0001e040351070f08001036890603086401c40e03900c1c481454055480c41c020100502c03200c03980d4000c0300401e084a03c0a1000c2c01c1c20320542e42a281ea803810b640700110040c0225001e48001030a01012001c50360707001c10030750600c40200c0300034a00100d02589540004041100420303003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 349662787 1250 349661537 349661539
    0x20105010f151d030a061415011b15020307050301030c080f0606041116080904060611070501180b0403050d0906020606090f060a0b1602150c061501030603061803080105 74
    0x101e15003401102d030b040007502864660b900f88a01e00c0340056001901c0740a45011160b814021040c02d00103205a58021042c095600240420b86981d4070540c80a40860f00c5075031800140c12000e640d558145046400c03d2030f40c040c181a0003200100900542030343c0c03040f56900700082d0044010003c0200b49120360024101c24005001400d4008078680c0d0303600c1e03009144900c40c0b51038a982d980700f0015002210402c0102d06e1400c01340c02e001c1d0400303544680c00014050301503442e140000442030300c0390a0038943d100c00c0c207001e015130a14240c011100e000b040134020013800300082001a00c41100780041c401144a4006010f03281114400a44602283d50250066401000822059940d13001c10070303074400241722242103140c40f00c00104218000d240c010b07800d11240029100380021007801c40c0c0d04001e100f2642148038064600b848a03c90242003041c0b0b0f002d900c1600401c1070030032000b408000e01003043c50001030041e602d8a501c000d4540d41c02c1e5541043d4030302d4070018140b5500c007007024007400d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 349664037 1250 349662787 349662809
    0x120b010602071a0306040207080c0a20060d0e070f180c0509091801151413020a020303040f020121050717090309090c070f150e060c03010905040f060e030a02010501 72
    0x1c5000403004400340f41c0c1c1c000c01114200000050816034981c0c0c16202c03c241c000f000c03917866002c0342010554a90300e56609646800780c103080c9007000d00c42d04124407590180a40090304092403082c240015004411203540c581c014400c007c03d0501c0b002c87c04c0c10003803641481100181c0440030141e07085481e480a14000c00c00e0070003180c1000d454007013605030403020914042c0040d5180240306801072452210314950320701072250015858000e0040d0759a600e00486500340310240000c6904101e00c107440b01c0c0009600140b0014010504000305d00d003a850060600640041c0d034440c400000c0001180e00f401c40a40da0b000707002c502584011121010034104019640300e0422a007040d0341d900985220b1481269000c0000d02c1982251080d9580350f42d201c0d010510140c44c0d40b501c008859407802d12844000d20b00992181000030014419000d80d800040d542d1940e400c0480603009040700401c20340e24010003902240025400f441400c140d110440302843d11042d80f10402800c3d2141a445445208 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 349665287 1250 349664037 349664039
    0x131101080f0105010e150a26070e010c05011b030203150d020f1318050a0b0903070c030807020d02181006090e0703181208041703130206160b01120b01060207 69
    0x900401500e415103d09081c4050703000415800200d500116a480d41e40c51701000c1000704013182c001e001b520314404602c1d4100384804c14607040c1040301d4001ca41d164005051300781000241c3d400354030b0040284d806580040b481c00070905145e08002d480c80d141c000040d50001c200100c00445903a4240892002c841c0100d4501c0a5000944c04464030951140b00f07026460303c0640f0010b440d845850041941d10910399120540d0401d2038407101c14840580c0d000d001080020540f80d40401240c00c1a40e110307070110461030950315029a00d4100c1941240c00c0304070780c4101e1000d03956240010f0401a6030184540c0346282c20787c0724403a411210350041e4140411a803040c00000030f0191415802050351a000842550f10031200000d140c00040c0540051120f282e00c2c3d02c4158003106082c403480c015141c00709825114a40c0404034070040b600207002c0912100c0f64001032414000401d620300800c01d0584a0352010345031080106002c0c0c0c03002c5d111500e4692810200040041428018280d030300141c00c1d01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 349666537 1250 349665287 349665301
    0x905150a080c0c070306065a05180103110105121306200301081203130201120b060c010905071d0f04020307090e1b04020406090303050304020d0203030313110108 71
    0x7100c0140154016007400724070640b0007102005100015900700b40140003055581000841e0640c666a40d0a00510850b1044140525124400c03806d02c0301041c483d10070a03450002c0016801002c0e6140c00c0800c82c107000081c155a90755690310000d50510350061940d451460242668000440c03003d06101040c000c03030300440d41c6180c009038807074030780c41022a90007894030f007000003880303007007910808061404a4410300d01d442d00c01650503221440c0484840c01d0801862540502084652610304940351b03044000551041000030080107148102044c1246074200180d41504039040b0004282e42d10f121060522000b0440840200030070544594241080800c2c44c15181005201161041810000c2021520100b02240c024080802d04000301d18070001c210392940016021030208810402044040345024401c50f0b04860250b151044c0c410b2945d6400d6032030786c04c01001a40d001c0b8040c0d901901689003440203510071549058030340e10402d0289061b622105c202081c00b810041000200144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 349667787 1250 349666537 349666547
    0x9050601030b01020c0a0b0c010b0a0e0f070c0b0117070803040803181c35070614070206180f0708030301050a0902040302030a0b13052d030c0c090709090207030905150a 74
    0x107440052801d50390300c1a14200d08c0b03014017660420310f5041250040d000840031201d0500d203020f151b441c202c1603180d4a58400c100c50380801050b010702043c4164004100240f141000c0b408a01641d0f002d8408041d07aa41c000e9017540c0043e40024026000010180b80e03581c3c0241124060130380854038034280d41340c40e065910440c0c4440000400c8000c48114801070354440940c0024034440e1504502201c00c81405100642e03048203208441042c00e00d1681d1130041104400e09218941e944c2c0100845c1d910b4000d1403488207440f8242003000c1c0540c2540038400075050282e40c016220311130082d65a07514140902840c1485039028000081c414401480103a5000ca10704502c984c0100c941c28980d00c84814480170070386290070050040c0300c0c91064078124004888405000e1540c000c01a003091080e581140d16403041c598000d5207508640300c000700614041d17000c250072454616001c22510303181c03980038040742d00580c800d83c0422a03210007008985880700d01d501200031011032581c20801d481101501c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 349669037 1250 349667787 349667789
    0x120501080a140a080703030603021509101d03120315090c090d02060d0f0e01061409130512030406050a0b060a0e010806061c02120f07020d1404030c09050601030b01020c0a 75
    0x40d49a041540107100b070390030484000d103580c01196085c1d030b40c2180d01e8050000d00b0301c1d220480c0106030300910b14030358440b168103030703540d00001814205124801d10000c41d03071502c0314500c2c0022520803000301403181c0c6040210348a09407000c29419541d0814a0100034a51120340342a40314441203010000700c0c024810503180c580c00103441e0540c2d03009a40c800500c0ca40145000304403000e03d030901e80000d01e50150003c8514140e004001c05c2025240c1c0801801801d6402a0700d0700007401401107044019080250114503019009903a400050703140000c049500607501a500140c80e04240207180040384102c0703036500011038081d8600071003a0f101400400c40070803481d041c006a00b0018000e911031804803820845910303000b00c2030000c8250f1300d01c000d40005195111109510b0300003000c1c011000115406400a9002000e00010401045890381c4030362841601c00041800004005402110300c400607000220f4042800c0c41d0580005003103a103064201d504541c44200038480503100e15600c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 349670287 1250 349669037 349669043
    0x3080706020a090b03040f0212030f161109070206040501050906010302090a020309011d07030318081f020d050a0e0609011506030917030c0406140324190b0406120501080a 75
    0x1d82c99a0040d4415a441c02da241c2c0070700d15a9100000700300420040c4910301a1080c4225040902da07154004181d980c0d005001c1c8040e6410310800400012040c0503801d03000713083c8201c04c0d14a0208100f0041078401c041070341d503903016074030450500c010400203004260f4400088402409950714640004180081c05000410301c02c0d80003000c0fa480740c000307410408a10315030300c00d1070a404135803101075541c40c540c51005034000ba000c0c800003a800c10000400c1c004035050705d00200944003c40c0600903002c1c040900e08201d0781d908211024401005002e150703c500c0d0000000544082c80002030741c00c000d001000461142d1502c14008030f80c2d9241c0d02e0f1071050b2490b51900042613000c0345000e036803074040796541c04212000441001120168000104180d0300303141e4541e4101040022030350389030701081d540c2e032600c001d11980b901000c3c103482000052550000f46107d01d101d8500140704590348840d040618001c0000030180003040c0c1004248814000702c1c0c0703013009258505440c182e200d0030550390003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 349671537 1250 349670287 349670291
    0x306031a1504050601020a1a09010b0105040b0706230a061401050c06070e0105040812130614030f040606120b010e13050a080306010c0b0a05060a0611151b0a0305040204140103080706 80
    0x1050145e4820403801c03c00541c080300c1c04180c41800780c808549040c0440350448150700740080300c00039512800646c0e040710150801a400c00139181d44040241000c565032446c0d4010385e2003010103a42c20680518000d440c2c01c030000503400c0c107000750b5481c108001e041c4581400402c00840580a9000800b0b65000440740340603036240480b800101c5403441942c4c040d010500c03c0003040c105001405004013410810a4000000141d44070702c1908c07140b0344d03602402d02c64031060002640d4180150b50b083c0d4040e200300e0001844545660790840801004030058407e00710140047c40100001c162090300030915940b80298520a41d6686580d030b21207400c01082e0981c04801310b0718590050424050150b44446140340c18586101c4100040c00200c9145106040c600700c002070141c0503003402c1c802034025102501c642480c2101800c034240e809800480410400c1e1080601184217101419084105503004992400c06004000a5401c880c4050100035a240010000180310004550800ba800800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 349672787 1250 349671537 349671541
    0x2040b0715182f06040312030207140604050d030e0c040209030313171006030c0b03180d0c0b0c09010c1e06090b07030e06060609041a0607030306031a150405 69
    0x840e03009002c89403a8800614405903407007040010080c1909203401d09000c0301142e407001c0301a0f41103443d4001403d180c00900400040c000300b181174014014a1b130f2103040141c5403444640d951008056060300105154110300700f4170007005024000f4030060005072405206281e08a07501700e480c0c448900c0c01c3c0d403180fa03000410084644092041c2d0340c004c51340e401d5a24007599514130f8003d84600441001071207024128540c03443d0f1900c0d00c504415a5041a080c4a44504107008040c00750700c007401c0e90101e07103035248201302d500c0d0040184220518807551a41c80a00c0310f031030a8515150080c00c003221011042c0442806668400c500814a513000099841c1c12500312501c05205056048041d0160b03061484d20310a1100000a80c0c0c080d04d8903a8040051144d0381101c0790700c0390000d03202c40d5030103075041040f0401d6280c00d810141080701203101d01d0403107855550000b14160b001007012404662140810024170075003201e2406c550100402c45409407a210644410151081621500c287c4d0303102c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 349674037 1250 349672787 349672823
    0x8040b0a18030501050412080c03011a07020301110a030608010902030d180801050408030712021806090a1d04030e030312010303031a030d0309051009030206191803051c02040b07 78
    0x20601d0035840d1040c00c1c41d20a9038580c2000c5010340130450303060310084164001441258031401244d4424540b55000c81d0459082841940fa8951040580c2901c0d03070b0213100300005031382d003845402020070304080302c1581c5007031210010742503c07803652010806900d481e403d040582c030007251200c46041d440c98080c2a0f81e12030700c1c0c13960441409400c824669840c0c14100803c1140480046004034125180c404006030010314070421b030300c1118541d01300e04d143c60680d0f240c1420000c020f04070004000384070f2605181c41d442c403130081c0c842c4c0078845041d0100e004241700c1419004140800400800d0703001c0c5240040c01b460420010006100c0203003010750765031100b090710346e204121600142000341601c02040c0d51110003005444004000e550500450180880030140f9103c0c510800f03030f0540141c0007a07580c0500b299017420312912524131140d100c5100a0b00d400c001c1407500d82c8070344280ca030310381c480ea4000032035120411000c5801c58a14030400080c0203045440d030075039a00e55804110b0201e8406692 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 349675287 1250 349674037 349674047
    0x306020a020708120406080109020705030909180114041217180703060908030703110a020d03180507120506010f051302070203070f0902090f0414180c0303030a021902010908040b0a 79
    0x150001c00c3c940079112a100e0101c0d043c02c000c00032900c80d65903480550741c807240200700f01d1007003000041c695070040110342200c0c00c00c5042c09a2180f00034000352164030010002a09544070042800c0c9060940000c02c01000105940078125082c4e5141504085007036002814400d60f029001c0c5858508421907418a8501082610003a5a00071000e1240d054580b906459603042540c503407001c01c0c1400c04051004d800c080698980d15a00e50007081e0b2680d50701025401442c0c52105003800160086141c00415020060381008051041c0140c1201e551403c160341495410380051083c07042031002040744e44e44003114002c461048501c0182d4882e44d80c4000b0f450b02d85584d024442d80c0c0005140000c14007000d60150032001000d0343d5440e0140403400401c003c5623000c0c5601103400c5a100c0200e0b074246002c966107101128840e04851008040000191441d00b0448101e007440382c0008411082d0841000641e98503e51400284070481c2a6a12030920303024a010341298518040b07071504505100d6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 349676537 1250 349675287 349675289
    0xf040e18150408040305010218130b0f0d2102070302010f081303080702031b010501090b0111031209120415110d0905040c1407060c030e071d04020117070f020c06130306020a0207 78
    0x3040007195606274035844015241d010345000c0b44a00361151010052805074010350000e00402041e40400580200c1001044640310000b581c44e940000043c1441d40d2005215128203046500207041c16450761000414100c29040b0a40c1000880b0051215105406020b100310681c10700342035903103507a4084202d1031406254180c402c1c62005500b020f08107101980558182c03080e480e814403070058503000550703903141c0d00e41510500b81e104100014846035a40805034000313484c041540c05041401d407504070315811a0704101003101092154000050b0481000d02c980a400b80c050b21200b080248094101d0b8040c1c8500750046448804051141d44200380503803100104850380f50300c2c1c01c15414880020801e05032103102181c540720740020507000000300c50040ba04050303810341101080c1d0f201e40e2940000a041241030050f01e0344419543c01103806002c3c0300d6086581c680d025603911140084c545001c61b100303580075510400c40c41340c0d100048413103002503a40180c80580d4030304080364124500840c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 349677787 1250 349676537 349676543
    0x50709120c0e180316030302120f01050909070308040b13080601060203180d02010507021e0d1110020610180b2107060503162303010305060714091f0309080f040e181504080403 77
    0x180d00411441c0c60b040c034019414cc0e081035802e80f52503a1103502440c4c0d5000030b40009000c6120500040046030145401401101c44541e81e00f5480d039910760f04103160035001c2e00720502580001c44e00b007c40318210100002c90650880c0c1c640f480d80364030780000c0c10307910604e50064080c0c0d12040e12114001c030038851101c0c03c80e01c05070401d440c1038494104000c10004c88480c152150102e150550f02c400c3c40080e0003801404d07268110601c162420349103402e500c40300780501c0c2650f80c45880c20b02c4640c1d600d800d400c502e544041c1c1a031103004880e51680d1b0070302032030f034004109100040c42072110015484500c00c03203010039070600351100d6030808601c180f49031b031613030225202c0709000001204002000c5401d902403540d0323859a5591813000020002c040c02503910383c070b0b04041e04400074400b10118803080e5401a6a5040c001001c180d185c40f81c10507a4000c0807004142c0c1c500080810004851061490f4802d0b400003902c070780c149002c1c01e0a915000d0300880280c00c004408003090078050500d08550003194 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 349679037 1250 349677787 349677817
    0x90303090b100503060c07020f0d14010212181b04090f021c1a01030201050a270303020c030c03030708041a0f0c0a110315010603050709120c0e180316030302 69
    0x19050760540c0b03840c0581c0c040c140c0607000d950040b818545116066a1209030f00a00c0d07103848185840a0103201e04203840705441c000c40001c3c011140e90003e1008000d03850104040510a2401d5800d01d070b02006c1c001e074614030710343c0202009801d0324221150940c4208d411540480d01c0030701801d1410355110411000707036100c4c8004410044280701c0100344c1c0c0101d40700740c01a204854459034032103158582480040c0c046081000000141889441c44411540b4a02c100c6121844910700500040c0a150811400f42e40440e03140b4103a480c0420100c141e20030110300461a00400755075110b900d025030b1191483c0b0310329050041c1032a401e00002d89448a007015202c94441422910035540c466102e4802d039003d9040000b26545410086550002c0000744450000310340d117080c00880c002d2600030070160800441038408034650b00290a600489030244200068180c107001c903602d150b00c400307841a8041664841c003240c900002006a8403007169107032400801d4202e6040c26000ba220b40003603481064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 349680287 1250 349679037 349679041
    0x60333110706140a0501081204140607060903020f100e0a0809010201020720040b0103050601020a0b07090b0a09080c0d03090b07081204060e0715050403060e0708060403020607021207030c06090303090b 88
    0x8a0218100c3d482142c40101c01d1006981c0c0d40710749900d902440c00508000741e01040140411089100b004c080702902819551808443d610b0f86000c56401010450041c0c002c000040d580d00020880102141810141000600403141c05c155403403928a2f402407904c3d1011070501143e078001c0d0b041e9038610b40c04c52042c4407600380500f045035080441c00c41d20b912852424100c1c032240c1d40b00b0312900c6d12441040e0000e1813001003646400341c00c0e0300010312036420032003490000706103540b03d100a003c460b1081d0303d0750302c4407909100f84141403589010b1890700580c101c0b41d1200220f40d00003035480c01c0f5012a240c60f6542d0b00e1508020a0621425480c1d00006160320180010007810b0f60001040a0511050b106415242e42c6241c111802882440001600a210600100e007240e400103442d1140c2030b0442d103d141e40ca18009090030f004440c1a40940c0001e42080081501480104e10031440700705198601140c130350b07000c0c00300c2c0c0407141c000e0a4240e807800b480007018065400f0310642070b00849110428 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 349681537 1250 349680287 349680311
    0x10215062103030405100203060f0105090d0804151106040209010e0a0e19050f010b010518060c01050702032a0706030c020c1e040605090c18030a0b0a060333110706 72
    0xb5031058130201d40c2481020f41c00e00034807007188250707070085000510803011030000d000110341a40121a0541d40851460307a00030000b268070000704021f01d0483c4c0703078880c00001e5040207010010650801c1c40c03240c21800c200001a45c83e0015a4107441184402c0c018a0711503104c5400100300000c5000c0d450b100d0782100304500b101f05070000010905ca0421600c026180103031070380c02d90341450115404181c06002c013a880240c2c802c0900041c070400b409480c2404e80780c010460039901c05565950150300009262800301d2804c0c0645401e55249031040b51588401c10002503075074103184a40804c0598441c400318020b40f00380400c10a00c4002044105140407411001d1001c10080c034120f40300754a00140003c85080c848003c0f80700320100d8240ba41003801c440360b108101800383e2042d59150142565840018566850190058031402d6002440d0750031454000b102103011807144400e40301240628004214504480c1c2d08605045404142598000c05a1240d4041d1140c020401030420086a000b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 349682787 1250 349681537 349681543
    0x7170c160510020309030d1139030616030203040c081609060f06020c0f19080d02100b101d1302121005030304060e18010308070308060a050102150621 66
    0x50760412100c0c2c0d03003981500740701a60b0300d00ca003011407a010b41043c4000c0c1c0a1a0003032030ba40c0841c04942c02035902900c03d0032041207011104003005103401e000800042c0c0094103070a04514540425002032031307141005d4080340c40c40d00e0800d80f03220030150004005030030801c0040c2600c00a0040320100c3c2c0883c520103110076441d944a0086542e000e2410400151411501d0124000c0300e04940191110f00c49040c00c2c401a012141c440c00d801c82890300c070100c120100b14042c08010070082000e055440d54400000342005030b110b0b49040c1d00c2e820100981800d58504003007051f1207003641080041031004040c41e8916181030300265a1050002c505403d080446400030316407891001c3c4000260781d40d9494046580095006440c1c0591040c4402d10915006160400340d401006100d100d0b2944112102424098260401c9404050102c2ca80c4101a086008907130041c03400c8860914082c10280000e60320344004102445407020800800d2541d2903900402d0500503000d102d0311484a200c6070f032542c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 349684037 1250 349682787 349682789
    0x70501150e0426041d10120215040510020f010b04090c26030c030c07050901030b0103030807030b0301150303170f150f130501050a06030908032d0f061302030c07170c16 74
    0x904496940001046140c0442400d030507911108447d0381e1310a541d400b0b00640307202c2d80654174400c1c007040001040c542e4403049201c04411055004002071446034000301d007525110b400d0280554101021100001c459040303074001e588400c1d040001d50b42810840b42403c0b240b070a001070711400000b03407980501002100810a40e02c0c21001c032160580c0d9a821f1019902c1c0910025010082c280c0061000070b20580d080c0f40c0140b010324000c80d0b010f480b000001d084910700201c1c080407902c106410410950070540012090090046082048c50710034120808248000d04048081000d0300030320103c0e5580c001e00451220015048084180950068030000d01c1c081c080c1900ca100300307410000f2403520900803554026070000200b81145c490b00840402d02c09071801c00c14030f400201c0c08001821252181c201e1040031411402103a50a001e028011082040130002541500400410042c03034151022074001d81c0d800b80c800e41c21600c2c681504d40301c17402010001043d600880c48100c13000384805115038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 349685287 1250 349684037 349684079
    0x103060e0312070302131a0f091503070504030b01060c0c050f010302070b162d08040f050604051005070201020f040b070c0b03010803041401030603111002070f0803070501150e042604 80
    0x4203116211072007d0610000d402d8082035a0b101045854440c2e0080c01c00b600d9452000303009041440f20b0320306034024640044452800051010804000380075883c5d480c180100b409080103111550191913808040103d0f010395805801d4030182d0007000c0c0d1180c1d044a1601d41c1105010459003020f4030340c0126071065801842c00035036085000d451070315190032101001d50079420803000c0e443c05c0781003d407848400284140c9101c2040700480010542c180070b02c5205504c0b4001820f0307285440d5181008850000d802003046a2052040d03100f0b140541742281d050b50460001300303884000074a81801c4001c50780c0c1201c0069400407000248c000c0c8000050700170340d12202d1400d0030b1000c640004400710381c01840054896904441a1b40d00c83c08c1040306c034940204144103840c050781c1c0715140292003000645c04020079600000300d010a01c1800c3c071910303140c04004010f60700340c40d1510b0348180c00360001400140064458008042414500004130141d03003a820ba46651110b948816442c9040d190785e00784 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 349686537 1250 349685287 349685317
    0x81b040b0603012105070504090503070c0816260a0b07030605040504020a05130902120c03060903030709050603100807030b0604150503060a0b040b04052502010605090103060e0312070302 82
    0x48485481c0c6101901d040e540b003045182141c1c00030082182070601e0200080c0c0d480d000303240e40403c4549940c0611000140500c00450303450a41d45822041c1c0d003c1507001c40d526800c451a182d80898948046030101c0b48090201c00c40c0952940d138010071840801d071308003d02c0c03049404120420000d179030704038400d1129803420000b95550388240015036404485c000e521050907003041c40716113000c81d0700c12200a00c07000c4c002040002d80d800b2400006c0c2c41420040310780d200d016514200e1904105295001041c680510b08508121307c0140c4440032500800d8030800c40031000920328144009084020aa000e0464070b96603aa810100710f804002c2e20040d019138105041c52045111000c2c030f240484034060010821651041d00600c0205160321684d5400340d16010760383c00640c0c0758003601d40140c41c88044c00000110500b50b520200c2018210201564104282003003a999180310450450341c00036004240c2a15010003241580301c0c2d030303112420800d00c0d40f050282a582c1070f80503141c28000c001035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 349687787 1250 349686537 349686551
    0x30c090f24020c01051207051b030315030f060103020d02060c010615030c2613061109191d0711011d1227030703020303040e33010810081b04 62
    0x898464802d40003090201d5000c006d2071182e4104030404561203400b0b0314095003080c1c28800c4100c4440a14003064045a1001c020300001d4100c111813550070f048101c005111728241040000e40b5844c05110107031154150511007400c1d516244200c450108450000300840c3c0d031100e05c0000c0611114a01600007481c1c144601507107401360316844001510b420403c2e0713841c0030b01402051800e40081661400015444407040081c08500546562000515910b0340700e00e000014044101d1031002600c0e007000c0c81c1c0e981080600104c0301c54401300010801031444a80d01c4440580328518040489003043d860404000c0400000b800b246000381201c030103444980b41c540c1e016803154040d2014100189140c58002e0407445030400028403180000f4080c0c56402e41e581d000241542c0166020298100e5910104591030410010304d0003007071244990518921380411202c0310501ca00c0004d1414800d505c0c000c1240c055034400e04030b009040903c100c5842040141601146400c4403103528041e40c20802 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 349689037 1250 349687787 349687859
    0x4060207050d0206030a0f110c010b10080609190b060a0804020307050a0f06081806010816120b0402060d0f05090f15011a0706090605040c0320030d030c090f 69
    0xb4900c005600240a00d00350b44400254000a0072000c24903044076030f5442ca1941c400c0340e5880070b014880c05e103600000e2440130803400e21000c0c840805d410000c0115110400c2025903609906507040346c89100d0003104198818050401000002c04240c0d00c00008581c460b441c41d400b4519034400d900c2607040d0b900441d510f42c140301e609200b40c054414080c036610402e100c807520480310903178000c1c0c088004036002020b00e1449414650b003030700111003e4000e42c5008118030903030400500140506201c100110800c1d4451041c000c2d13020b40000d114440024200f5840000b0b1741100710b40c0c0040c0e4000f004079081091040740e842c5400310707418030280513150040144600c0c0d1002c0b28100d4640031502d0781081d0240090b212103920108048880d281d5483c07020001c0340d51840346034442c42c0b14400c0001c000b811030400c01c0d1545171506034910307286034012071050b0589021072440004411350401040f0070221407401d44c1c80e90754540080d000c80240c5400020f481c05002600320186d82c0f040a0340080d800c0e140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 349690287 1250 349689037 349689049
    0x50309211011041502100c0e100c02060409020307030f050a1b0206011214150c03180c2407060e010902010807021203010608040311100b130204050d260a03020406020705 74
    0x100b20000c018414001004100201c80c0300c0d010031002031060700c01e01c81b443c048035421551056000000640c0f040c40c080c1040c02c120040240850190034000400070450340081d02500c2503000348045150044041065070340281c01c14444401d03803d8082c042c0785000c07025403000b0703c40c03a80c0c0b41e42c00085081d80d58252070b00104050341030783c110404c80c209901480d00c0301032480341100c41d00700304d0f803090b500040d501f04030a030191030085090103021640d0f81010900121002e5680c401181076401203200d1601da59117400116800d80f0b04034682c0301c200640c14405505134019a400070f02694203100901c00101810750000d0f600c0c078400d80b261a05915840d20483e520304900c0740c0c52600c5001003005001c8603029000c0140d210f4401d15112600c103180f12412400e00544c0c65089000e0307070701d410007242c0620b041d4080170301c070b2030880c44214245072a0200090184060000242545005421040d017243c042d41b00e242c000c1c0406114556103400406006000b54030900c1460010300400c80045140c0c9049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 349691537 1250 349690287 349690301
    0x204290a050a0e130210230301080303061201110c0a0c0e1909080d1409071505071509080f04080105010f1203051b12040602060c090604120503092110 66
    0xb800340e4021504000540c00003800c064202010a00001099130040c2c3e200070300e21038031031090341d204010044051002c3e0b6021891050f0b06c5020207007840144240e50001081d254031410840e4088000b241c10b000460041c80c10003440401c2c0c10b0300099401c4050310000d22054042d110300b4480b910603a95054032514680181c4240411a6001a1101c0030309a207402400e00b0038005d203401741c54040340102d618125025a04205030540d000320403c1001c174070034840b00e002061b542e002e44a80106500c0000d00f14400d5900c02480039803851422100c040c8941d001d1300d41554401e5040f9135a48000300c0c00021070b040351040300340d00c2d130a000020943e5020402c003030086400e80c6001c400d00c0d80741982c1c240c8036604405103001880600000350110741104001c8200401d50402c09666101e0620300002c1c00c1610080508510440c1084907100e0b80e00d600f401c40d011200c0c508010141d507511468000e00314402c41110b1680420842c0c10344000d0194001f50407210138241080790440d02e40007440c0000e8401c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 349692787 1250 349691537 349691539
    0x90c0d230a2c070302061e041211031b13060906060306080d0e100507021c03050d06090e060c0715090303060e07020105150618040203150301180503030c13030204290a05 74
    0x500c20401414900040d25147c180d06100040d4141007011a00203a0015801050b003a5048403891046c8221035032010440101600075200d4a021142090381400d4000c091718080c04114820307801c0040680d00c048090070700e680050100b04d59808008001e02a0b41c004e0b88410b0040242e0078201d54010107103c55443c401600840804008010560751600101c1c0180d03042101c850340c044508403d60b0909410b41d100713490b016240e010300d0f4070a6046981ca0340221006510704441202d80761800035041398002c41500503240d0b0394078545820700128120402c0441a1414000420b00301601038025200b56290319240109940d11500103e007078403400d0f50412100081c0d41c0c000103240c1007481c001c02c2038202841000d060844c520010030101d0f4012074104113143d60300b110409080ca000c1c000c840c0c1012070303599070311a44000354440e540c40b48409403481e400d51030700103903554220401c08444001150000c2080150200209001980c00c2e01380c054151981500100e44ca00c9141c405403010036a68 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 349694037 1250 349692787 349692793
    0xc1e120324060c0f1005090307020a03080a02010e06010b0415031e0c021f0f111c090203190f0b0a0c120905010902040204080304090b090c0d230a2c 65
    0x9110100600324401101150b42004042090780c0796418100040385012113800300402802040c04041011148003810540f441c0e00704000c55800350b942d1b400c1e01001d60360005c1c562599000340607006d0b4014040704601c5400c138040c0000006070445e81c58058002c54480c0c402d11106150718040403411142940c40041d220325054120300b0345503803d0b078031611384180e860040314140000014520844403580b60785209d000d4581075003040604450050f17480180400340294104100380211400140441540441c0165238200c1202596410007111a207004981003603083c514646c1011882400812401c1c7e42041046c4003090780101e60344555120410070f5620750500d100c2c49a011000307007205010a0340c481d0748801c0c000c800b5a54a10040004003001d400840e611440d005c2d10744207484100c500326225a810008100000758558102e40d440384400b50005103091050401c02e0f5140b800c0c0061042d441c00140400c0034500070342d0300221403065400201c40e02c1e03030003000900307034403103480130300954250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 349695287 1250 349694037 349694071
    0x412020c0a031101200a03021014221205030906090a0809100306180b10020a1502071a07030c1704020a0e07090914040605060f090106050c01020c1e1203 67
    0x40071034107180c00c1e0850501d00f0010918210490604c0c0ba2041240c04c1c1d40c03a004007040130100744c3c0402c0100c203001ca20301c50078400042c0020ad211011100142800350b40b04040c1044804c02d140c0d045180101584902180132003011030000410076082103a035000b070303071003031901040b410040025a00f6a072a44245803078036100500b024000640a004003007014562a50408280603d45070300d152110340b011700d4009440d0410300708000000c08150078420964014118a2004c00c0e01440c000d10044ca5800002d661406c05141c5800442c069460a0132915445410300009a5158208404030340d8156180c0e01c00c1c460b1034400e000c5114003a0380096100c0e01200d803c005606240c0505076122215040c00c082c0e4564410360035065900070952480d130040020208800c1003600e00c01c2d42d41041c0c090b100c1a140100540104a62600c10300a01c5e05004011803928a2079009404680b1040d84c000d003a52101c884007074005004da030140c5409401e50003610001d03c20080d141058074070a01680e85084410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 349696537 1250 349695287 349695293
    0x30b03010e060601031a031c082208300f070203040e0f0703090c0f15030c051c0204090f061a0c030409110f030106050a08011401020d1808060c030412020c0a03 70
    0xc0400e46e00d8601218810801d4401c00d035410706c407140c2031030110041c01c0407407003203004020041107000340740c4007aa0018003219241201c0c0c3d8000c0d000590351004000750384410307001e00b110161020306811040e140f94052000f2203c10715441003401501c08a40390100b98407402e034240d84034011406076403011812480010300d9408250308283d003191701d506000458002a46818100c4c0016410440d03507585641e40401c000d83c40c88007000d00d020010310b010451840c94160040140c03240d03a02944034003000001d540100106035040381c00400e00600d040090b116080d001101924446c8a444079a55514001b10700303c503410004c0303900c0040c08201070342c509802c00481d0002011302910030306109005010355440507a58038021806002d50342c48403a1a50780ca050018109030341600a0642c8001703030b4010a90507600082da00403000b07020f0424404860300d5200c101c00b01006680302c015944070b034a050280114a400c01140a50300a080304008601803407002c0c1e0f0384900646210307800c554415410004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 349697787 1250 349696537 349696541
    0x1505060f1606020c1506100909150807080d08060907050906160b0703090b060a0623090406060906090f1d0c21011706041208280c030b03010e06060103 66
    0x829000062072106054040d25a0012030b000440e0300405644416107540c0f1a4020f061140c2c0d00620894403106422514400103122094a00c83c2081c40780c0c845440009a010903942d41e400780a51804841030700d95508a030070b0362003003589031300004104143d005c02d4241c1840302100e482620b55803103407031903c0324020034040942d01c6180503101414050b900740300054100000940503501507030f404100407403281402d144030400981030b1485085007000070000f464000c800342c0010380407100d070300a40711380080c80e601d518400d2891550b8800e01e0150082400e0350410544004e030380055441c00203003a101c002c0740081c94040d0060a003010080c0d020324110640e120312191b03100228060f45820900f038078501509007800c2d8400291000a07000051024088902c000740203560840002c10a90915841d8040b00000d500140d50030403441100080583d81ca46d034402001d0703c0101e12a0048941c511103500060407400311980c00a070401401021910741409148882c0301c1c204094406030320382000540c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 349699037 1250 349697787 349697797
    0x30f1104030807030c0804030803061008090c0f0a1805100503210f070b0f01180b0105180f060d021c0207050309010e0f060d05041104020c0a03140712020a061505060f 73
    0x4c00c220300401c24034000b429490141009600c903207038007034980c1081c604002c410214214010100042c040400c52072040000b45038034104d80c160b072050464002c2e01c003c1244541d6a410003000681241d055107151101075208070700c0b9040030808689815190030405d925000300300145119501004c0d400700f08000c0d551b004101baa00904d243c50310f07000c0c080d51580180ca50442d0400b5014001c08010001100e41803039008101309031800070041d03c0c035141c002030200d000d91540101c24107589001c00003c0d440b004042814510010083c0d81c03105070380c40701d540c083e60242c40c103444030b440010031100c0d50400f14001d503200702d0b610034040d6040c6080100116a900c2c178943c0b02c5680008100d24400d0507443c1d850040c007040c21505004a4145445d00308603502d0b00480c003081e03008900c1000031442c08072300410f40b074000551600e00505107400004112102d03004100c4050302c091080c00300f48040c95000642040c0c0c49120721801d003c64080c003450b041701c1b210288100307900200100300c00c05441480800400b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 349700287 1250 349699037 349699043
    0x9190e01021306050a0206090303240f0312030a18080409020313020a09090b22081b030310150807020309130221011e06120506181501030f1104030807 66
    0x50901500c06846000d800d4a0f80c028800f1603c00203071014902e41c1800002c1d8403188101c019407541c10407418007100e00b550018030b5001c40f144d01901d0216603030340240300d03009140020220741c8525054085454940e00c291030702000c891034825102003500c81c40c140c010b1301940100380d0030304046c0b80c1001e14020394001041348a01000e5450301d0307001039440c04132240c00381c0740c0100001082d4081c3c2c40c140c8101d200141c002c0641d05035034240c114090100080c00030100790b1207450692289060300807030b1148561a407481d101804040204200c00d00c035261400d041b00d041a002c000d042000802c02d6414200643e1110016003081040c0b43c040d040040c030711180003501d203500514002142c000303410107240b4081c1c840744092080380104185800d5180c01d2525908205110014914018010709290405160502c10545500c00210642d4400041901c0841451503156003868182507580c901442800400e01003440d000341e070030314100944030761541c0c00504d0110030b2805040d03440b96620340d00481011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 349701537 1250 349700287 349700291
    0x3060a050403020c090f0a0e01061202100c060e03070c0902030f01061103070213060602010c1805010f0507020d2307032307150305070207060c020d2a14040b09190e01 73
    0x118001e6150f10176070354440ca80720003104201e41840348040082e00e69010303859009030f050890900c683d42243c500c0b207640c140d044450901000d00444192508070000001030003552070000b5510900342c0200081c20107900c51214030032200e44405a10b0308a000650f07928205540480c0103200c0180510b81c0000701c070502c40112410700e0484c2c1d00184110314002c3c3c40c0c0110390746980741000300135024010030140c4401f50504514400050341000864005403050f68100206600c7c0942d01c107008208481600e07802400c801042c2a050404041c01d03075211000c0c1402ca000e0f01c40b107000da00c40c040394030010703a036001440d416661f00e070a002040c190241c0c0708003260b074040c0000c006203c007400710307250560404e10b840202e0180340021000e420107295030f01600074040102c9144005945884401c0015030f8040d200281c612440011100030341494130f1000b10180300d004021071614550103000041d510111070500c0800e1105007801202c180666024000c0031245e00c0c01051141940c0001b900c10382030300c2c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 349702787 1250 349701537 349701553
    0x1d060d1509050309040c0c2a0b0414011205010503072304020a020a03170408040501210507020c0f03010e0616170c0702010305070e03060105210709140703060503060a05040302 77
    0x2401c0300d120060440c1c042d400051502c0040c2000e0007036940e003841c18146100c1112194807460300c0340d034101c2990136111418411110382c94200010300c40240007940c2c091074441d5100d01e25800403501c080d1006012445000006a8011a80c0a5141a00d070058050b08495240406c0340c00c1c0c2c4480200181d02d03443c08a8403500039519548054088208654018056070702a410081d00c00f02c203541c0c0034030f40004810104000f180900c0221030443c0c0f400e1070000b6203080b0607503204184105508001e080e45003400248210707154002100341e0500c00407205d9540c40103a102c201802c840c2814226146c94001c240002c090540700444052004018107000c0d00c0003459607071440890070100e40302100064041091b00039035905100e2164010070a003002c00a400000001968030702051003140e2044460070f600368040441c03e000b0700484102d9200301e074405600d84d080c020140001944c0070140f24030010004054502c01d0007503400321a0040c024004a4486203005405400010001c1e002e40c890a14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 349704037 1250 349702787 349702823
    0xc040203090c15031e07021006060815040204030f020609060d140103121b0213110f03010312140406081803031618061e020f0a110301061d060d 63
    0x21441882a007019000c0d2031200c01c00c21154800303d4644104000042c010002e11012807040c00391030745a002c1540d0303800d0340d440030101e01c4c002050380c0b481c011a04144001403030642008505009280d43e00c0340e061072a0310042071208038000e80c40b0242c40c0001407807a040240c20310307400401034558003501051400888600b20000e03100f0040c0709141c0101c0000040007440b6800038031042035079051402580c00c28100c0f001d400000c009040c0a0700c10803c05141951260b01d992041a82080984500e6280c8204007100c6842d90424401640c90108801829050034403d1045040c0407074034041d060704042c208141103400c0d450040c100048864242d5240300141c4c400c002039846002c1d074140800108507907000007400c00e400815110382d41d074501c07103042c801550494100c40ca65480404400b000100f28901285480300100d041d885030b0003001250414411188805400f040341a4001d001003503449145244102c1d25148002c074040f41d0301c010400e64139003192040d04c800c2c011194240342d40c1c8115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 349705287 1250 349704037 349704041
    0x816022713110114160303060312030509190303152612070b040f2406240c050f010f0b0a050405070f051e0301090e010e0a03090b0c0c04 60
    0x50490351000285650481909511401840d8050401c0d048101d01803040d03501c100c10440b682c810981481001d800c01d000c1e10f8982800d407584031074000b1a200c1031103032600b0040d0080095000985812503042021170885000b402903c7c062070440c0b0050100b08075101d000c0869140c810000c4040640300d6250404820b04200002c000d415122401c6034503070084e907004186a90034012030300c09034110940100f01500c0b100e05807004283c000001000702d6917103241c00005107001d060b0041c00c020b90705002000b151103200038a040c40114540400c200794544594144903200390f510011443c004000101d40107100e49209030900384100102c51800100881280c25502d140f80d000400541c0c0740c1844a080c0307404450000284401c1d00c04004504161500900c030101e848080000e2110008080c020030705440510b225103500305c0e24094607561030f2060300e030203445040020740f2198200050041c8d5448041050602030b503140d00c810302258a4242e20360303115001030801410078001c074840200d403a11070b8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 349706537 1250 349705287 349705309
    0xc0c050a0608060906041407050a0c02150a180503060c0a170a0507030f090203060402061309020403061b0f022a041a0306282705010507110d050403081602 68
    0x40e848140051600f081481003018005140604c01d0742800181d82018001240b0329070821910700e03110350b41d82c00700c2c0303820740d10b5404180c0004c0d00812261901d512a842d1200600b4602d0507594800030900392518040701e0052040c000c841c1c0c15001140030032000f06a850007001d00f94850305181d404132031a150300c626034100465074481c29603150420004050f600d072040c401c110f288031000300722550403600400d90f0740324001e0009000781d0700014120f903008891a801c0300280f1480e50155907981e224030b45840a0120340e000306034030a80180500d01414040c4507902e610207042c5c1e004041413181d00800451070801d418151140348050507450740103403a58014141403a410080304001c45c0110802d05280c100010003000c0754142c2517108540b12160b40d1341c64070004031403403400314541481000e003200c0304041d00101a400035400c0413260802c00c042d0441c91140741c0640783e401c00641c00301c0b0600c0d150200c3d901040c000540420062000903841005041b100c0c9005c900141c110080b6404240003201c1e0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 349707787 1250 349706537 349706549
    0x9040b0607050c0f0a1a030402010c0c03031d09010b03040f060204080703030503010f0f08061303020c18090d0509100305090a0807030804060c031503082209060807050414070c0c050a 80
    0x1215007036a0500341031344d00f031150f184240d8245605074a0100200c0f04400c0d0750140c0b1000090001c0481c05580c454229104410303040304684481c19032b01d02c2c0142c044400c460019203191070507654401140342c91032145040741d4045449a10b15603940c0e45805810a602908031103403030f401c5c000403500010411540000e075210b611740ea982d82d414801e02458140003540060130f410a2540288000c00c000703e4201d81144400040407401e040c607140907802d141c0c40c000d0301034100c443c0001e1466803071189a0480c1c0204003000a0364240890814111654800c01d017031140c00165407040700e03180d540f20398400c40d0b1204400003a02c188a295540c0c0d40e01c4c55204040540024a00c00240400c1c00b0f2240318401e100c002c0703801e0070014010004840d201c99192444040c202d00000310344d0410002c601c00717822002c20414210181c00030f40b42c5c02c00e50010b01407030040040c40d00c41c915000c992420a44588032020b0b4032800300ca2002c0c3d176a10000c40c0c1581801d01d08840201950350700007600d8442581c07500c06803407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 349709037 1250 349707787 349707793
    0xe070906030312090c0302101e090617010608060d050f0a050312180a08070302010b031204060323040f0804030b0405010b0f091303110c060409051023040209040b060705 74
    0x2156040003019401c3e001002e0f0006440c00210714001803602264104490f419100c0405d1005408803c6d034038555090030034011074101c3c1415005442d84403181000380c42040c1c9850102c0c1100394004011110f09010706004500102c0c08600b0070b18018802c0701030144500101c071110b04840300864245481001c007100c030b40d031010030300001c100c03140340d60f0b40d80c090401c00707412000840c00c0081c40d695900111000d0007510000900e842410b10070340140d4401070014003220381c05400c5d005802d409502c0343c401c1d40c00103450465040c90030600c1040c06080b68480e4540681c094686845052180020801c2101c000504000000018114408103403107540140000a143c158120621204c41d00320414588030b140c04904011514100c0100c1704881d5805180c8008000000c0c4c8404e80707409808510b0550042010800041c200081d403c030b00d1080d0100050003040380ea4403c40090008150a42404880b02e507892005082c10658040d240f281e00060010035041c1c0d5072000700ea41944090801d540340d030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 349710287 1250 349709037 349709039
    0x80403050a0218040308010b280801051509090103060c051908010e010611030a0806120304030f1112030d0b0616051c020c2d042a020a03120209040e070906 68
    0xb1414502c941102c03e42c2c009200c1c000d184c035513002020b00c081400f482c00c090902113401805101455600300d04030030508a2107001c0b4040c2140070b01600000d20905100380700c01140c1c0c3c440003905005030b901401000e011b44040c1d034216076400b00075000d542466410005c0070f000a4542d40e203109850106121a900c80b5070a5505100840c0002c6805802c1002031248040031602010b40000444400240500d042c200c10745656002401105000240001318030003c280442486003070100c090f420b070f2040c00c84095100480051081650f802214402550001d1002c0280d0511940100d0740c03405008248502c3d00c40c9000d81c41c2000040050240c803282d000b80f40a00346000c00b495074000b004030b140002c000130030b00b8000285a603200395a41038110020312071040d120154a046d4441c002034018800c0c0003041c00340503601c840b0142c0d0010441100384c808d414609107800810a20346441d0035554141c4055050064035011b50300c421001900070f50740300202a42520280001301c05070008110101d619 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 349711537 1250 349710287 349710289
    0x90901020c120c0307120c0606050306060109030b1005060409020901021c020c0111010e120702130515061e0a0203071209030305070605060d050d02010606120209090f04050a0b1015021c050f0403080403050a02 91
    0xa070962b80005001e64410303428404140c0e0070031103880c101c0740d1203851200c1c00c2c2c0d1a01d6800c40382035101d50005411500105000c0ba0070348058015000c00d14dc2a802c80b0761491600000c12080a0703003410240c00341e0032402c01d94815500c40d00d4004508841080003103801200061400e00e00a8280c0c03501112083c003182100861406410070100c18221010a02c4103080806107501550820302c4620306c00d081c0002d0034a8a0802500e40c04d40d01c1e20710150701c80c2c840408140c065242d5000010440c0c000c16070794104107840e406004c0540580c4e4142d41c41d5400c2c10041c0d61100c00a00000d4803441e0b212480b060520000f5a04010700c102d4000b041d4004940545840300c050181508480c02c0c00640d03005000300e250070303111b0104080c1d0101c40d5484202098031030742420b9007021200344000d0888001e003803c0001c0084100044821526100030703070342c08102075a2089843d1200c0001d0540c8401000c01d15007842441f543c040c0ca04441c5050025213013540d06d5440041e40e60240c0c0c002c40e581e400524813074082d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 349712787 1250 349711537 349711541
    0xa020103050a050610121e0501050406050607050c2103031e01170312062e080105060c15150406080c120c060a030c140406030b090901020c120c0307120c06 68
    0x7002c1541d20500a42c1002c00015040c1410a4404420040751900b02d00e00c1400da9082041004a841c05000300c7c45030080124018100900616014900f00040000c02d4100310301290a4190843c028290242030501080a0590540d50000e801d04000c0b98003803490070b0500065010b80c0158180b8840b805000c0c2d40120b4017101648040700e040300396049a903003505c003c0b00b101c110003100c0040c00c405942c0c0000244810a80004420750141004005002c4044030088400c0384031107912200320903a0b841e01005124461581043c110740c1003081c05207c580105009079412000c1144034840d001c10100105007214125804503240d40e10442c006a481d0614904060a5185102c06400540c603001d021440c07034400c800801c002c0556074208a40032a20540500074a040024203060b561681e8034001409010004c24503842a85400042a0055014030848115070390740300190609516a203903094440d0840c0404003498082040400009a950b211103051264503455084d0300040031309050f01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 349714037 1250 349712787 349712791
    0x504060f110409021e2a060606040b090409060e0a0209010b0705120f04050a150315030209070509010c0b070810120305120c0d0c020d0e040219141b0a02010305 70
    0xa103141ca400032107032600d8040000c0303409503212a0000750303403040e502c0c20881030308044642150300340c200468586000b20790b0301030110b500030b405005001d940b02685100c2c6d44940b02910701d594004410481040340510b4540584005003004000040e0507000e51502c0040e6180d844060445410003204a02145051601940034101c001080d0382014020b503951170b501c034103071051901c1507007001c20540b40508007030f400c0383d0140402038600310886541300c580a45030f079844001c0001080c1421603100340032452401d254212500203103070094076203500c10169010380c4a020458100309111680c038010600e8092018041d844a6a48140c0303807408040c60700c40049150007099010502d40344400c00300e5072080075110760640042d0904030503254102c5100d5103201303042c902034005040c00108094549c020498078410410354803078103106000001000100c1c8118909400d10b6456a00c006401d41d10800001c8441a0207008561600000b20780c00034034040010b200b0780d0594022035400045503407601800d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 349715287 1250 349714037 349714061
    0x61110021206191815091e052a07050f0a150525030f06120f060507090f030f030e0607030f0e1306080106080c0603010b0a120b0603070201050406 64
    0x1410030000310805051030301c0140645201e50901c0b50003401c040000d4240200526003a02000c40050340000141c003c1e0410200200e060f11075a2000a000c00003401440081c04005044035804440380a00600810007d402c0c0daa0540415000403a4a0101c0f04d145569032041a007160b1613603164a030503850000070000784003054100102c07a00c00202d240d18000569580745a01040c10b5995900c054440301d156154844c1044011448c0d001e480d426a1000003130301d12445040c00040d4560a40441c610400394004003220200003441001c11000d61005800244501d001036003184e0325901020b4401141d00169070304080c00080000301500260304901491080d16494107002842c2c43c040c01c804100c5c0d951000b8403070421441c90a503694100c0c541c03840c00725604100806034559042da402401d50b40102e0115100d2007040503c94079010040d00e04844440400d0391400c0c4154804507110800b03c80c81100c0c1645032092458269240e40165105071155400002c0a19080c100300c0c0c141c5d68614016 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 349716537 1250 349715287 349715291
    0x3071e090207020a12062007061a180c091f090905040c0312020a080406270f1a04050315040b060d0b060607020609120703031103040b0a0c0f0c061110 66
    0x4070005031a03c2c002c4608480500c41e0001800201d0f007081c002600d030411002c0049081f009905508080703040280401502800041004a01959442c04103005640040b40e201c80300c0700a00c4000c0710f05072201036202e41c034085001c1c200b0204078003007402c914044289903030b4142c1e0048400155035005100c0c82c020442d03c8818042c5090603250a040c0011a02003e0030807200040e5881e0302c0740c001c102500c809544220040d46e11030392000e00070068400100e03482c085115088400072420421190031b016a100781c02c0ea101d22a1402e201050700341d80c90701003101c480c0780c14040040d2030307038040c00051582880f00040c035203070b45001d01e0100c02c4494000d00345c51044507130b100b8400100e400d682c80d07154411025a550796640300e45e400052498001c49000c0c50348800525071107050300340c0c04035151045034401e417903245003a440c01100c1910ba01550242150522051107101004c0740302314002c0700340b18080d090317001c1202070383d498803180314500360800c82c0480e0f03120000c010322a40c00c000201080c150080b007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 349717787 1250 349716537 349716547
    0x203010303050412050a0b150a05011103090910030501140f06010329010c0506090c0907080708070503100e2701060b04052b0501090c1202030309150903071e0902 71
    0x58401c3c02280109202d181d107810070384080100420244c42e1054000018050500d010902c0c441d02c608114180e9001d41ea41ea10002030315405107031458541c09008002e503062000c800203200010380020411610301501c0e42d40003000c40c000b8458600e20101039294a103003460704044d03110411101404040c101442c080350080c500c1903491080c2654501c4055004242d071340c03132004a800e00040c0c0001741003030280000740418a0390000d90555240f01c141c038032034019598654140d407010030884446000c1030440000450103445a0020355200e08400f20001c0599125200203103034040882b038488181000c8084c41583d410380380009241c224801c4001d03c00d103420102c01130420300907445024090b4030718030380344501066180104240181d5480300814801400d050070350280506501c140d5203600c07440781c0481c00760501888a8003030364010703000b140342c56424401e01280103803080620805400074448101c541e9004d01a400060205514100074445d0606080089000300d0b484032000c01c0c41005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 349719037 1250 349717787 349717793
    0x702040c0e06030f0601050f13030501050106030e0a080d110403060e060f090d08040507090c1709030306100f020f0d0f080a0605150f0d1d0c0d031d0a0510030203010608070302030103 80
    0x100e0f54407818003c4044151703256180140c0c1d6038018085080c0c04000003091742c0101d45103240340f400031640140d00034003650340d880c441502240d034203824009031600700540c2400490341da0001424121585a000541d04070a01c0568603940c00541003204d44c16182c0d003484c0002070042101c00d800a003e0001282617041030300d04d46540d10401004241030004100019092107002d01c940b80042201d1007042c080c80403d80001009100044a1000c0c1c0311074581c0800c0b501c000000a80b07115103030242c00c200e800c1400940c01e55811108204401c21031080882c1e140213201c3c140800078040055403078004001c49800805040302d100184a070300d91510304442008145c0e10311458a07090007000400301d42c0e604484861000522445480700001802e100d401d110307494010440c0500754011400303843c034002c210010403400511141c1d000d00040d0a00c040000c0700781501849a080550081080644a40c2c5030041403118410024a0303002c80da002c401000364682044020380c0c4082c05203021495903040d65 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 349720287 1250 349719037 349719049
    0x10110d0b12061b07120305060a0f0305032a2d01021e091215010303110307030c03120902030106080312010509010608071404090203090d02010c090f0909050a080705030702040c0e 78
    0x20304000d6003180006020810b03030340703000c201c81255070070445907600c45c000050003a02415080c1c580e076000d00045500016030f0903420310041c003580da0040245140032103102c0400f070341d030390051a104030617000107a000d19072550410018400c2c0410080700b00103c0070f582901e0076034818200b41d03194140d0041008580d001d0000201404d5400b240148a8491001c0383c0800c8a40201141100a61044100041d1181e1100f111a8101c921990b100d0031841004002a82ca074042c100d80140420130310100300000900a40e60700c062641d41d540c0c0024281c651b500001c0c2921031070741c407400359504006804d020080c00140454090841070b00e01c8101ca51401c18001e0503210f00410202c204050042000300410100c000c8400070680460259103a0607c00c84041d100c0c05180015800341d0b20700f0883c16416070040d9001c1c030849041905030311820b0b00d00011500030b0040724070100c800303000c0d852000b400609110003030600140214000d50329422644107000403507a0242c0043c003031100314420404030b0799a803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 349721537 1250 349720287 349720291
    0x1104050423042004060b030a09053f0901091e0e0408090111160515070f0b10060c150c02011b0f020127080a0210110d0b1206 55
    0x80d40d000451140001d0141c04005100360715945007502001031105200d901c1e085155244801c91028406000d5041004120780c2ca03840741e81504401800002d8400c0718940c00700107114017a005845010111035040340240050b447c00000d000c601400005200181041c56440e0f240c100207224602600c40001030000380840c41340030a459440b07850300107015500301900d0000c201d40007240341c031414146411050f5810a40d562800200d465180003050100001e00f031010311180313450742c21918103080a100c14a807506580440035003003000700400260013245140490384c024204449141005104a03d40440f03e90004041180c1c10720341e540484c0480b6072400080c0019000001c0240980c40d00740d0260503000040700740e081c801001503c03116000851200d507035035103038000c22820442412480d0b040c5081c00c894603845055078880c000003400d4a0081101c09454012605645402d82d116000d41d410441c1b4144803110110340c00001d45040c3c02041c8806070100c134484100381c0fa44179139690712800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 349722787 1250 349721537 349721539
    0x307090f050a03021f12020a0527091902070b010905090f0604031205061f05031f0f03120504080102030a27150203150d0809030f0607080f10080f01060501030b04110405 74
    0x25070000000d646002d4450640440742608040d504c8030018003014103103401404c003d0ae004000c58a050441445030313444060215001001029191103030794420340c00d860707041d0904a40310750030000c01c800705442018035402007504a401149900c3d1655006050020746443c221072640714605010001c0d03000200484a00910400010ba43c0c0c2d44038000b44980c41111400109014900c42d414a4180e0210007544035089040c0829143c2d0f0300251180c2c007c2000c0d1252844281c000b074018400299601000501c0c1c029a25104d4205916800000c0c220f91040d103443d20f0b0590703035a5440d101c10b01350002c483c18000004080104600058543d541d018409920071420507a0000005840c081a10754a61200c180903100b0142c0c0c945510b010b03041a0302415607144607120b04205002d182070005081c070310424090342c5030603958841c9003410f40f40f44005440b807180d1610318080894920f208200041100c04580000326449240500240c1160920042503000c1c0f810f003d03e42c0900c13004002101e0803980 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 349724037 1250 349722787 349722829
    0x41b0e0f070c11100305061c0201120b01110f0f010c1d0d0305040803120406050f04020d080c010603080d1a04050106090b0d0b1203040306060b090901031e06020307090f050a0302 78
    0x211034580841e482e81c03e1540154044030712401c50454641c544c1c081c0384038940584214848003035076840e5018001d01c00100a0004000c0146203210b0741c51500300e40844401810003440a440b50b5250760305140c8101c50714085580324402e508040b50090003003110540f07d5085c5414103c860740b800c052010b4800c0b20130b9001d0070b80c401c0d1010030927100b442242e0081807440c080d29190003204079441411a416030b402c5d1005404c140200f40c0f034001c004a660300a660040c10703102d418810390355101c1143c0100c04810100e56903440d00101150718400140a6060340840c0011200e580c003100400303851310712100900403440c0c60014880c40e5080a4480c1c1558050f00707021b0f440d0241102c52501400e884240c00307801070b0345102c2c02061810000098070940384501da0500c074050303e0b03070803420442c050000c40b00d50100412004002140743c4254100d1402e0b03925031280302103440c90701c850b0141e9009aa100e00040d50480c0d08014a21421240c41d02412084400f60000741c0385400007050044503400c0040d01007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 349725287 1250 349724037 349724057
    0x70c0201020a12020c12010c0203040e151c020102060901060308032404020a0e0a060507080d0e150705040503070501110703080f0c1009020405070c0f030318060203041b0e0f07 77
    0x6802000701c80c203003d0340820141104042c03414000e460704070300741c0c0c41e9000341020746804980b55010302403580b40011542c025410701d403402e1000c5c52465800391600403010842d11000c4a251a000178080034110114980d034036440051000910303017840181001100d900d841801e200040b040d8040700e4002032010804140c01070000090040c688000281a0380144000755a0028079040048180310f000100d85030ba443c5030b61001d094405104112b00100215002c000720038040c0d4107507000004103409071048401001c80143c03861180d4800381c1f0076001007000841d00300104c0c50f042002d840504000e181068102000d01007480d070340e001c0360100038501040030921026150100090b80d000101480c00c0b51100409091103000500003500164095824400001c030028001c41040503000d500c0490790301041140d803411001490100a005080b80c0142c1c50700d8045001400503500403402814080e404403510b0904c0018800340303510200442c3e40203020041c0000178540c1c003030340c4244d042c200007581c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 349726537 1250 349725287 349725289
    0x9070203040503150604150b071704050910030605060301021e0706151e06030c050a08072601050a0e0402030a0b07050d02040e060103110415030f021911010b0a0608070c02 75
    0x502482e0000307038051207038603e40075810b203c502038075014920035582084100000d0101e52910001d0f4024858a4113081200d100082d00700c021380368124204002c99410700f40c40303500045840358203032207421400780400c0040c418002c483c401d980c0c014501710000c61501e4240c0c001100104914203101e5503540000c100750040c401c15030001022144400326061106407a05080d0038003e086102c040442e80300300d4008204030780030f03100c0c40d42d03040448e0321118100305245404450043e80249100100114402ca07585000320702103199031b01c0202901969465170500041c402c0c2204240e0040d04001501d0040c80003588001c2881803106410041c01c021956803107400f40e030140b00c0c2070060490b8a00c0050002883c5003038628950244000340c0e0280190241e00d46041460300846c040c0614013030198114905c054065440450101440200542040e13610080705118909003407601010075038036400c5442c1c44000707201d071001d250000c41c1c0502c1c0c0300c3c0c14450010666200140b00c8414041c0b410010025 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 349727787 1250 349726537 349726543
    0x5090106050a0e07031a0f130b03060c0c0f0703020919020702092d01050907230c0601030519080304020d060227150301031104181406100e0f06090702 66
    0x3516014007151a80d030b594000011000e00d084988000103450b298051403c5041b5000104845000600000c00e00c21510300b040b407108000e0b08094012079654040e842e02c0d03141403100c580310f40c84852010382c58043e41d902c43e40c144000a00002080d402002042c001030b924104915040284040304510802c40a0402e000a03c11090080d6000780100c041150f5000c01c0d41c018915a0b5076111024480420061a051081000e00950f039104a5490024200500c11801c41307000c90300004181d802d000421280f504d0541c040c004559981c4c0100d03006100b0702c90108402d1113140725503441034903644502c2d115003181c1c1c000a00020720605200040d007092102e02d4060700c1c10200c140140300c20ba41c5552401c81403142800e6000f0340511480140205100492400e0f0b078100c0e500520174202940440b420440241076450306003c60308041c900b0440810100e590483cbc4c0840c20b034004040500b030000c00307000ca869483d480a0f1319181d089080100151110301c200d5084402030360789140580b10a03c0982c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 349729037 1250 349727787 349727789
    0x40303020c120d1d0a0209190b0a03080a2309060708040e0a091101020c030c0910030c06020d180b070b0a060b070302061e10150306091d0c041802010305090106 70
    0x160a0300301054165154903e40e00c84840a9000300808041a0503101c2482d102c2141d80d9000c4d51015001002070007a03506411169030105c0e00500005804544100241600080340c0003540d0200d40070601d02c0c149030700302c000409441d041504031000c0d1625403551184621400101b039000c0c083c080341e1042040914030903103010b40b21420b0150007528103111003c00818038100c080d1402104000d1030402540040f6104441d404080c001d0482d12801005001c400c000243c104c9516182e400000004500502004005086543e0140924000002000708080061090a01000d1206100300f160f46920011189119441389001c0c08980d01c1d82109002440b20b68081119000c001460404140d4082201c034411108032040d80180380d00100200c80711101212001c0404e840c030a41440701001c0c405c2410b050413054603000c582039490744c4a10040e2860280709548042c0c004124036261202409070921822003601c0403c800480c007103c3c0315080306400c00180c189a90391020642c0c0b0407007900a50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 349730287 1250 349729037 349729063
    0x1506041d16020f0a0f1a0c0c060c130311030712030c050d0810090506010908010c02010207020a0b040807030b0a090f111c0c050103090203070806043f030e010209090c0415020f06040303020c 83
    0x1d21a80f811f6001e10385c040d030202d800000d80d8020f01000650452100d800d994005d80c00e00000c0c110a421541e409404201203030860741c2c144201d21000840e07221001043c0d10041c4030350385503d06c950b1103160075803500301216810780c14002480c0400c2002140e43c0c88005c21103422000c041140e0b1a40700043c0c4507101560000075155080001e440c414a405400600da0715100b600c1c54a02ca03552503201114034050b6000d008e00365000684104041110480d4490300300e0041400018207480603540c041c2e10041c0c138070701215010030303038801c0f0841483d01005c8203065050118a074403081d800e590b50b4426107402c3c0d02542d41415a25158001991010080c00024002d00002c81d40311b070074142040280c1840d034203074940725110a40c0303141103845290340043e07003400e4441000445811a100095003d028055441e440303a40d828025060550b0303c228000d4011590135042682e2a030a040719840c00d1528850a482135601a00810600c0b40c000580d965010303405150040e01c69056000807828114405121 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 349731537 1250 349730287 349730333
    0x11202030a09150e070609030f030e0a0e040c06030c020d080105011d030f0c0910080c06030a1b0e1512010e0912040e06130507081506041d16020f0a0f 66
    0xa8000e844940e400404c00305102c0003101c4900313690724000c60780d40065000040c0701d11800300002001030700a4450110b4030034010100c0f00c034141c07240523203d6288000c445c1a01c520341c4200e004c00c9140d4051140f00107000c0c2c184050303c240c054225000d4120034062041038100640700b8004200da41c00700414211070301d4002c00f0b0310840c441d048901c550354101107017181c0c0710b52600b2000c1807102002c000810201c561010152800310400c41c01c101d82900010000c2c0c180d540c0701c01c00091001d2881056501803103007502c1d5000c026aa1009021000c2406040401004000c000032010300c8203840310b10b03045500341403103100c403940c40c140941c1c18900c44505010210402080200d403681c50100c06034800c500c103584451150010042e1441074400039500000468001404200c2451280301d000d0b0b28882c014200d28070302903070380101c428082d802d40c0c081e900b10345035401402241c20140c80c203040101c0d000d100400c68008040741007a291400180c005241282c3c1c42b464800300002a0039801a0500d4140c032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 349732787 1250 349731537 349731563
    0x10030f0c050927010b18060a0201090606050616060519021605060702060c030a090f0b0a0606030b090403050909091c0e04150b04060e1c030903020306090606011202030a09 75
    0x409011038001c04420b910a080d8421100808050003011004400e042503440e0403607403804c420141140d1010342a804a8a04042001425260303d8014600c84419500000310320086080101c21a00309410080c80303842c0070411f01084a6602c54000d01d01d641201c030019194581610f82d40c4120114041e5a80103800403030410f0010362402181d00141e07000740155845071f0344404e8200d8617620122000341c0070a1090002c142d2000107903000e040554811030580307032207401c02c0d2039000403540215641e100290725100140410b0754513000da1032040505448142c840d05040e079015082d03009464085008040708800200c07a14400c022108040e40f40d440c01c110000717900d030710003451003425211043c015820202c0c1700034410281007001d030480e9103200712141400d080ca4802c489403120a200d0a910117a42050400c030b4405403000b110f00c030380c401c1d16444111869441411300744940109211490340005040010f5130340c01c03100f20404140300c00300059482c1e0310b4024400c0107098102c0c001e01380c4095404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 349734037 1250 349732787 349732811
    0x31509010504021c0f030f0c060f02040f0902071a100e0a090b060d0b07050a03141602150c03010311180901090b011208070204051005101205070e06070210030f 70
    0x4000741c002c60080e110800c07001041c007500d10394844616001800406003548840c040780c843d20701c5141121940c5050114605240c80b2001901e1300d0504107400254009800c22101420190710307030041c40b0032001507041003000e403a01c16014055410680408180d00001000c11644249510250140c0c84442c40d0380d0800000d40c138024a210f410480e80c0c4092480420860b16220541c06070742da80c0020010070507610004115515080040707a01c09040e101c2c04008200040101024481c00610119611101c1e406030000e2500d2071001f0708050040b0408103016456891008980c192500521080d44102401010440c41c0c0d42005c50940c10b4048801403003031000d010f40101c0140c0b80128428001662034018041080c0c1120b28001c0400304104403540c0141040d41010798083c911007000030409513900302050a15015a0020300040d1003004050041000c0d0b00c605a00603d02d480e08902030710301e200c0828028400c6040182c49650340300d8807a04c4441c030940005202001e0101700307105090701e4070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 349735287 1250 349734037 349734041
    0x32d030c030e010801080a11040e010e0c090109020a02100c0903170a030e0f0717011b230301050d1b03051e010f1b1b050a031d09160e03150901 63
    0x100d0880004982e018407000d0b561044043c941a14500806448220440e544000c10005445809600162210402d00d0b00403820301c25002001c4482c03000e4500c01d07180303000f00141c80342c050300f002402038814000250403903800540380c026403081940c0090920103c00f0155990714041d070008112001210b9162200010103000d804000c02035102030080c1c42a00e221280c50700200c0d1000342d583c0d840b44000f04210001e4041000e0016242d0300001100d02812035401c0c885194103500e030f0003050000c188a2a0700c2032003000c04181442c500a000c0c01d41d4180000103110421a0030007030b105001e103142c0a00391141566100009540c000100d851301c0104412001e6503116a2907401455440c0c000b0007801c80f11a8080c07038031180400c08030080050725416041c0c401e0100118040c484900881c1c51600180d81000782d001c1a50080c1c8542c03a41102211824410001501000b40516200d1050151341e40b0407008801150354942407007c3d6135841c610200389030001060390050380d04520010b000c9000819 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 349736537 1250 349735287 349735307
    0x810080717011d030d0f02040b120108370317071112070c1205030705030708030a1d07030602031e0412020606030a0314031302040c020607020615030601032d03 70
    0x3030028441d03c081441c9400d040d058101018041c1d42040020f00c040f0452548409101801243c0060600703031039068090701500800480031143c2034013001881960020841444c0c105222000b200b00c0c8280380e509162010780008041c0848410f8020040426000c0c51940c01d00b0008030b01121717000d103800075000740703000300000400da5280504501003512041080842c2c460743d41155043c1701644c6040780c45220b241599609481d140014880c00001075002e04c01010014015003407187ca9003040c082071401c0f544290000c030760103181c041d4091026000420030008481e0401001a140c0c0d0750100c6100e03129030314400d11a1040041000c10040001c40b00710b099040c5020703401c1314841e541d00c2040c1640c407601002c0145c00f15088018555220701c4000086038409601513100c0414840c0d980407405503040c080c4130f100540c008034104102150b041081c25408003102805089100010b004a0b4aa81041c040a0841d0241d1030070140d402105140782039451175014024403550b01c55040082081d00d071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 349737787 1250 349736537 349736579
    0xe0d050a020a17061305070b0309060a1a0f040c050c0f0a1506061d04060e13022d0f040b060301031202012406030906111813110304020108100807 64
    0x1400e02c04103c50b0185100e601070440303000c0041055445203040c1c61003518021100f11214442d901c004100190003030041c0d0b01a4000000400b010b09002c07490000386e07207007400710500f0080502e407000c91655444065400507030080d200080c81c5015170900b15010301c110781c41c00d840762003850160040d00c280000c1c4c1d40d09150040700c0100100140607001010758402d4460840000c83c24607200340d407007408080046011400410024856584011030b060945084440075603040c0c00e4206642981001940c041c030f9a4405035151a80b000012a21402041e5500c1c3c058007a1007811a201ba050320f49901070074054800801c89900c039a92441c0001301484003802490065003081c981914200040051815900b4490071041d1a207003084400c9005100420302942c420303031603201600e20f2407000402052140513505d0440c0b4003490880c140700c8401c0300c0c6181105a5450464051403401201e0240c036081542480d10040603120f400b04502840880d4000c4801c1d0300801e040092812180b90f03208009603c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 349739037 1250 349737787 349737799
    0x60c09090f02090906060309071e061107030510020d0b1302091f080c03092b020706050405090411030a061b080915041104021b01020901020c09090c01030203070e0d050a02 75
    0x4030401044059003d095603c030342100300d003004920745d80f44c4071015607842990b000480e807019035180c0e800b404618540122401c81d8401c48070074000383e42d0021003c1c9039480c042008200451171561b4150380e41d40c00303118041100b9804503154135132151640185d21a034400802405400b80810082002580001510b40c071865040f01d00b40144280c0941d5016074146540343c6201d0b558544075180d0b0582d000a00080c8140500010740520b8034280700c100b11a0b1415004002c12501c24900280c60140903030000c4040c00028441000103a45e0030131510b501582c4080f44803090a061400300780b5101d8503010007002c850514840c0111091010b04070180b0359419034600c030b51910351100150311241ea2203031000080390748500140110b803444220307800c10040038000501d041d00407070040c4108449909440b51594002950500540e4100b00d00203440004803114491402e00782406503a600300340e0150750505402200003620b26004070b0795075100190181042034186011701c3c01d41c0e01c2c4e908001c402c9203c6c403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 349740287 1250 349739037 349739051
    0x6080615030109051503060f0a150e10080610210201030b130509010b0603010303120c020c121b0604050a120303181a010b03130f021f0504090b040212040303090609060c0909 76
    0x32070001f07540c030b004812504144c44151540008180940695081000c13688000040012411080100c10344181320045074482c0c442d0604020340d04004c000341c1001c0c884080c0b42d4090102000300c040300756500811603101c000455061005034050302c4030440316580004a50007400c140d02e00c1d500218401c6079500002c10681d4110701c10070406003c207003c050005503000c545140d0500840d40708021603100c1e07004551440b038605002500700c0030810321448141e08030000b121120041c42c920441c44d4002210b4190500b800c01f004541c0c0d04505108242002c4003c6d044881854021307404410420020b44014282101c45d040c603006500246511641d0010007100001e02000031205407405141000c0800d481c01515441d42801110707255803e83c0d00c81c400b100b04840d4044074224107801601c890b111640c40301d150106480440c1c1d422079085010707900400100c0740c1018680030280c4c1c410782c1400c00049811450601c04020020003400030203162070b040d1a07a14041c0c004041804844072048140400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 349741537 1250 349740287 349740289
    0x1f0f031103070b0d0923150a0c05030f10050405010b090f01020a08040504090503043b1015020a3c0b060108041704031b170601060806150301090515 65
    0x40080d0f100710052240240580c150041103904010015070140d24007034074103031704003030001c080c1da8000e114100700341d200841c031404443c1090030041d404404080104a21542508090b040f0b01c802070200c1d01c0c0e00c0740a000a0300f000c000d194183c002d403030042c000f081a0f40e121a0018803952010306014480d90b40f05100800e40c1d8030000b00400324940c406030031403c0c02c0c13600081c403000c2d0200020072035281c002444003007804180300c00e480c180c100c0c1e0101c610384101e0315450340000200b180d040346000b400101c420002180040a08501116032902e101d00e502840f600c41242413900c043d4000301036048004803007080b4080c0620411140d0781031598200c80f800058110100a00f06010060a14102e080051250b6005007011984140150607000da500141160741465602a40007210030407a10844440440c0064402c030780a0240d03071888400307003410303000c0726030303039944148680d00c1003240c10b030001a46612602e41041d034005070781d8242512540c440044c003010b0001100c108060104c0c0d03588100c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 349742787 1250 349741537 349741543
    0x3030a050f091f23060a05010f0c021c0b181c0207120302030f0f1201050904150b120a0303050a05090d0c080702150403080306040c03060501171f0f031103 68
    0x140d100d050040c100842c4210020501c0981c6010400c02d4558690105001c0d205131200c034202c0ca801001c0d901c1251030081e007000142c0605030001c074104038107100b013102020b0f048100b45481580480d820440c2d00b50407200c403c026614041c00030701c00301c0c4120510580c0c84044048080d40a0040203880c800128404405a60310740d0045003030050307201000403c00180314244504400b402131041d240b81c101c0401103031342c0950115100f00000c0ca03000800c210b000044c0c1070800d000d0300d0304880035540c9040a4560110b04980000249880da648400b0105260388042240340800f820606403000c400845c280680213143c200c505000c02d504140024451100109880007218095196420358001644840c1015003104c0ca0403a008000800c0f03170408a92604040c10045110f0045250b07a444c0140c180815907400c4e0141606040c03d040c01070040d41e030081c0011800f0311402d0b210050b20755a800c0c0000b610000d00c0140e49008007510404a10540030b15606801d590040000b210705030060340034155 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 349744037 1250 349742787 349742791
    0x4030618030f0f0c03080a060b0417060a0c14090409120905031606141b120301090c0905090a02070f0602040f030c0b0a050405010503090a0204111c060e01030b180106060203030a050f 80
    0x1380120b0307660713000074040c81250740c02c444640400070b045500c465500c031542c1d00039040400250003400b4034000502c020004c0a512808901c000e003d91a01c0000203000360007158034000d01e090021580d81c181da100ca9000103406604050386603842e20700c40d20041c2802040d8010940070b4007071103840c13004c240c4c1a081307440308071510343c2c0e288902d04407a4402c542040e003001a03100710354401540030346500780040007203000b00d400106c00103940e5490003a0240440303d4050340300c4140300c00b07035a003000b5590301c8018190740701c5c3d029040583c0c1c80302d90b45000c000c03c8008002c0100103070302c040b0b80031404030004060030040e240300e1180d03204190340340c68002000303018040d028030008004000500032544254003954022102c10201e55070403400e54002415520300030075440180601080f03c684112420884d00c5140d280b80500700400c40c01c01c4e01508181c2e10501002d44140030b864003244910b480b4200d0342030381c5040e200081203000e80300c620003916540203440384910f20341442c011580c01d50b07100014074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 349745287 1250 349744037 349744067
    0x110301050403111006030803130f0f32250509040f0201140f0a0c080c0307060b1c03020a02040222080a1502040e1501110d0201060f12050a080c0304030618030f 70
    0x58110b0340c9e0100c0c0c000100380c3e10081214980d40342030700080000c02d0400c44c403038820f10130f240d5944070540340700300110781007190030101d1780d08440c030316440004620105284030313603004e9582009501d400c81c0c000000780750380585c400c0c2e4000440c06c0c2040305105516100a801d18401d0340e495001da888079000391024010621008003040c400c11542144078001c1d9001501c051040700c502d41062032003209582503800010080e610f10362524900b040d10300e4005820485501142542000090f05031002941c41d80000002030042e0741c00140e00b41e40c074008241100101c9220220a0801a1642030240e110031440700f04036a241c40303940d08581141014002d0300c06660080001d400d880d91004031502071120707410b11aa0610003d6162500c010f50309000da1592500140c001103111031900001d1622000345920070744510100090440008001283d0383c4aa144c10515980d00c8541000241d8258802d551005110034680a820f07505000210000b03410b0341d0281c0c40350601035040c410305071a01c280746030b160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 349746537 1250 349745287 349745303
    0x302190b0a0e3922020c0a0209160f081b1309060b04030605010b0711211c020609010912140906030a230720010902090c03010806070f080105010c11030105040311100603 74
    0x1180c01c405913000c1c0c003103240c49004440444847e500411110042600c00119810f03014880e0b00c4020f030424aa102d01d02c8072480c1141c03c0d841d0000d81c41b2061504000884076480002501409503d200c1250201801038003400704030780d95035407a903040960710030300c400c880e031a003060000507070811780360280c6440940146c0642c11006c2e200f0108201d420102807101000440e03171145041c506403c0007140304a0200340a1041c0161510201920b0420003d0204289078105000000062050b050406104074241401c1c0700b0f0840e80400c07800f00d40038411a01e600140d02100f00000d92a0315001071001c1d150311040101440481072070444c2c0ca60040380c0600106120f25610315910042411161041c0c92400000401c220654009a04100c0640d41c524013502e0100c01400382000130321145030021654100804006244107003c2c1c42441c0500c030b0181800104040581408202071100840240c024001c003c1864549400ba001c83d5100d03c0f200151700c00c08005601d1200c2d10710488080d20740203010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 349747787 1250 349746537 349746589
    0x3050d030203070302070609060b031b062a061e0105060903060c0f070804030c08010c0f0f0e1206090106030302010605060c0a0809041407020a0302190b0a0e39 70
    0x800d802940c00640000c003010303400c10801c40412194420000040d1040300d000c50049182b404140c0380000e0840c2000b600180c0c0c40c0312100c00e550300310172203c2c00440072500f00c815204003100d14080140e400842280d9000f004200488200d4591304028003408055404d0301d66625501440340700d00458072529015440f01010900355069800904000c1070b9101d544c0d840e00c0c0340c0d642c40384010f41044e03008564201100e04144181142030081b80b80960309840c200d10700c1248035000500003901081480300b4003003644000152600e0b04074480060300b406108681e102d0070603100c818000c0c0600d100503001940fa00ca408a00340c41c0c45800c4648840b8404010901401c0c90385610b62640d200402a65101d540c1d1080400ca1800c0c0c41e81080c45a1181d1300030340400790345400e000e0309107012405c810ba10860501d825400040c0310300c0046421000c0f030b0600064072151031080d940380200340b9180411424019070307842da4118890000342c0000701c9002c6101c03046c9200d00244006c484005280d5003400c000c100d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 349749037 1250 349747787 349747813
    0x130806070e180a3903021303150b0414060109090213170c0d080307031103010302060f1804061511060112021002120412050f07080d0e0307031b031205040305 69
    0x4010b410036108440091440c03880701d05108907104c0040e00101480a03000f002001c1010f0303d22291240440d82030a40c0340950030a41700ca02c3e10402d010050400d0701d0340e41801740204050b800641140400340007084425042114800000703000c80c1c5140c0010380910010079042c0f401d00070750f44124031108503580c00d00c4c2840440d2008040c104006511807082c0002018195607c00714418810b00908045503641000d03c401000d0750a40c031402c41da030131410001000140c46110480b028070351203001942e01c40741d0740300540c030704182a00480f039805400c1000229448010f8817030003109592030b461b10603107010958a9540c07524024401d00201c4002c600ea0b070720250034000d8099155071580d1050b503c07006040300030300350700c2e030019000842d60440c4580e501040000800100b080c140d00c0c3e500900e000b924040b40b007a40c40006100b003404220707800d44110500c1e101005a03c000d954003d003941082034028181c502c0100d03ea104c2900e240180c20300b074035809800744007241e00b900d4100c001791440036507400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 349750287 1250 349749037 349749079
    0x801120212120307180305060103120e0a06110c03010b10050f070605091e03070b0103030318050f0606030d0c112b140601050109060e090406090206130806070e 70
    0x40681e041107a000c600c91410800740104074024008444141d268103050714000d10782c1c000040c4c0007094100400b4280040385002a1a0741140d602030060714120500798030403100c01d0a1003e0440e04010190030200708950894130f217a98006414048641290382d200c101401c1ea1000c14445030840d000c05002d0020510803c003c12942c0d2147c50340500d0308203540d0310041240c1089074440c08a4100c3d41034601c1c0b46051081c041c2107108d0810095003010350303139110361242c8030307040c4401404c1c15522900116a00c1810b9940e41036980c0020a41c0d40c80024004c009445840031529144280116030259100303c0c05498001000c45e0880c18809043c5445000c3c440542c50024500c1380c801450300010b010001103000c68070019215031420031000807113250580c074010040e00502d0521045400c1030154603408410030032400c130120b03010f803255100c07800c1002c000c01c0c416a010303400640c0029074400c19025050340c401180e9101e011141b09680324001290b64600903000d2940c460121340100040751008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 349751537 1250 349750287 349750319
    0xb0d060c0519020d08010e0c0a0c03030f0e011a030f0303040809010207030209090d0816021f060801020f03040c091e023117060112260313020f030a030801 68
    0x15050942c82d040081c0c14512101940b03014034401070303100395008102d06600121450062013a07410816281c2061304800c1e1503402108103100402c24820780c42003c2c588641c2141e18a201e10300c100b0480c02c880080390781d019081b219001c01c481d921609040d146070900150030401021030b040990700b19110ba5845100c80c0d03004041c40d44c1184a08400400560f583d105914043d40643c402030008144082d0041c150355402002c28100080450142d0002c2c0d0700410143d50084070000c1c208001c1031518801c000070b04603504034003580c0d032005c5861030b40740b05490019409580220403ca001d01d50703401d610010307120585040c81d4a040341c11081c0d8110344071a005421030a081b1520601c0807207031060422401400070941284604070701804001e8140d503858260721000c0d080c40a0310301581850000d0541c81d141100081c40c0404400f00c071200001c20400216008080180782980e0381442280f0350000081c1440a0340306822280c0c03c03a0710b9160000c0d8640d6020391544403000241c1c43c200100c6884c0c241 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 349752787 1250 349751537 349751561
    0x6020d080a0e010c170f010e0115090819050f0601050a09020d020c01050901020d0608060f0c0a0207090911090a230c1e040f0f0605070809040b060d0905010f0b0d06 72
    0x40ba020728815410038040c655200507242d82d140f80420b91944410030385c00f4050150b40d00028031800602c125045220018103694103800c9201c0c0f00e540c0700078100d9201c44641c2c842055030080030660290030500280c016403503801a012615551500d4070610740307c1a080c4501c542c80750520385c003045221510340140c41070456101005040a800090050940c0d4003203a201c0140c0c3d50004200e11180350714030a000217000054001c045501d441c2e009001c06d09800340400941010114211501910070050340707001d86201e407024002c5802e140b030813054416450300c03240c0c410724000c070001c2c03007910251103100d290381a00da441480c0294801709910341003602500c05c03000040104a0540b59200b14849200380700311080f03c0c0c07552903203041e0900c62641010b03001610715125403941002001c0d880415550308036001000541c1e100001030009000380800458607070005030100318500c6010f0141e0060b4a203e0080000380700608046081b40c2c111559121020303070240d00d0084100124425610071a1015070b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 349754037 1250 349752787 349752791
    0xd0801051005091206040b13020a0302090604090516051f020c0d02190e010302100203040b0307050918010e042a09050a020f04030506090d080402060702011b0b0a061e06020d080a 78
    0xd004007290480300e0041080e4295407000f170503c07080110003418158801a00c3d1403c200101d01c0754000340031001c0d184400b1b4810140340b40458650341d40d507403051807403e52010444419030a002514081300e1304078420790303210b03504040109c00c1c00c1c041c3d1008003041068550103014602000000c03c20416100b21060360000451030f20740b500160075400b803501400d4006040e500b070303624610400001c00c140e054604115001070104000e81042442500c2d00705c10036040c850780741d40c102d102081c0c4040850211034400c0990000001c1d6200190040303602a60190803125084521400c000311040d0760300a121568041403641041138801540c81250809110340c030144c6060500e951f02c400541041d0410b035159041070040c4400c01d10704002c050301160440c02c0849261400d9000103c2c1c3d4000c03614080e050141c80c9010000c0130b440404581c3c0b00d01c0e8000000e01841c281000075030b00070402405020707440c41107400d0031a240d043c501841e008807692039008010391034003030300100c6e4031407000b07021403c00d19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 349755287 1250 349754037 349754047
    0x30a09121b1217130512010f0207030e04140907050402070507090204030809131509050403110f0d020c0603040c1a040b04030312050606090a090e030f0d0c09080d0801051005 76
    0x6001c00040002015860300d00d00c11030304075081c08030408102240d10340315640c00300854082076029584030802c8400032100c1541e9000c000100c10f01504c100304002800e140300003120320805420481c941c4030304e4029070f005c00c146007844450b80c5039250182d0700c020b40707580102010491450a60010a40688200250365406640c0c8040400b81c0c1c0041d007046482943c0418090154180003000c04800c410003802032103881c0780c188512003042064000c101a891702c503800070341458003900e400e0b034101c07440e001140c172400c40042119455546212900340140500c7c07080c0845450010700f580d0045d90828111000d1501e803120540e07401c04100070455003075109200c002100f008140140004501980340c01417003020451244007120002041d2502ca10800e01c0200744a8a4142204050750710f110000198015623141903031441c001c42019440003580000d1421a140c81b9030001c00b0860a16110b200860340c03984003294448400500c140300054601d4010000e070324102031b4801320f96440d03051081ca04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 349756537 1250 349755287 349755323
    0xa090f1403210724140f010303030b1206100e0106030c050f0304020a030f03180f0b120712060b090307080c331801020c010516031809090507090c02030a0912 69
    0xf00902c443c00c4110144c011504890341e44850040080c03400c504c4d00d104010385012241042200b01c1800090105a920075502e40c1a4a4058a00b0f01e0312070b03414100d030381d02d280c024007241804006000e8503210541010000030424041d0080009000507600c900c1d003001c4040d20100416000200141d83c484039809000020a510030307061147c06009030390f0740808152b41100200402441c1e4002c1696900040082008800180588010101001d40c038851508c4020045402d002480300000b8450701e05440000c0c01c50030314000300320307880d000e90540d807856a503a040641c482c40104040c5070045001d43c10414803081c4c000c1c440618080c020440306481c041020280c000340c202e4400c142054403001a4204c040da0100f00c0c14000d150246041482e10080e8184c4100c1481521801018494096012a0165040704545c2e01900426a040082e4030746410419a603442c0c900c510218185480700c00000c1910103c122464460365031981a400c504d092204503400075109800c0e20000c444055803004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 349757787 1250 349756537 349756553
    0xa12140108060f0112020a170c09181006030308061c0f0303090201081605042312030915090307050909030d060807050a05060705300a090f14032107 65
    0x41c140d0000140789919012480140140301a00285902c65950841200680e2941c00304030644080740085103410114500451030504485c02d016405032a400810540390078402d00100020030020440300348074620600f40084030003c1c00007070700080d2080c001880d1818605820f144e03814051040507240711580d120460800c2e4114411000280c440f100752007907603840124550007048114443e03014072800c01d005000c921541c4950f100d11400c0c10032508440061a15041c031180001d0100207400100b0740b0900e40781d0388440c4400e4030030f54009518401165815080c1d8006603000781c001c110450400d0200000310b02c004040340550320041200e001390316894041c100050584500a0103128280400c101c003003007403504040d00a000c00d108100215800280d2100c00302e64410004810208040d120703940347c81c1c2c10f00541075041d0002010007a190380407890204403484000740707000301b984482e503440c0000c00150b44507038075a00055102648a2020000e040301594000c50307645804610340e180d01d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 349759037 1250 349757787 349757789
    0xe0c180a08061f0501030218130e07121b061205061314010602060106020a0209010510050c070f15170420030f06150405040506041101090b0f07120e060a121401 70
    0x408003400c1e0400511050fa036043e140058002404c003541040c4001020140e0758240c142d40382e2007008290f21600b28140c90741e0182c042d42520300300b40c3c0c030701c0b0341c5034582c0d142d00c5a00c200e0700b210520540e060a00f00d11401c042144245e03942940c51f9900780d0224032180e00076200140035035a10050040c400d2564007464071815510b040c408560410303070740c9403000190400c3c505911032015508010450001a03917008440c42c15a24100d5180508403130001003114203000d1244c14a8941c45003980209262081c80800011075030307526013160388401c041d40116155074000480f803080021500201e40000c2034a40d0003034441d0000010301040b6a44c0400082c5401850b4100006039000103017888003c90315180300f052094000d0742e06010a0829607901643c4182c0200060142195902408150b038801c0d000b103401040004d200c603444d803080d6252503065a00280d400c0740c02810b4071a40c4852a80a10142991100024003460401c4122001aa05140c520311912251a5207608041600c01c21140c2c00e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 349760287 1250 349759037 349759051
    0x16090e011409010905011412030f031003060b0607030f080910020a11071a0a081e0109140f1027111e030c030a0e010e010c050a03060e0c180a0806 64
    0x101d020004000d2001c00710041e00000b004900340390060050040107002c140405100b42c0b510903811406403001d40c01c6024070703800084440350003c24008002c801030401410b0342d00501c0108000310249007000b50502c1060702c000c0c0419800c00000d0300b03480c09004a150700480039402d4414000b0080b0510b0700b268460f00080e408600e032002c1c640c0010108008d6400039241d04800c0700d0b240402840c54005900a001d1000200482400000d4600d0545080d080d0115403104901440b941c5410401c8040d088020207800c0f40b440850002c0c80f1b108074030314418064164a040820054103000d101e5056140c01285131040d15031304050443c03140703002d20501500031805c400081d1100520740c9802560041c14030303032860041c018000d01074008980e00450350002d0020f0701c0000c202c0a04c0308042e02400750341051034065484c2502c24040b0700d130800020000350041c0d5604103c0d00d501c411104502d1707881605e403421503042c01e018180b20701020529250000c0c01c002c050888156442c4a16803510200312481c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 349761537 1250 349760287 349760309
    0x6120a060e07060903050309060705071205030307030b0616030807050c030c150c0a09060c1e050c0103050606070b0115020f06160e0109080a03031a0616050c0301060e16090e01 77
    0x110522010510528000d4403a519007444d226103141c0b5100e40d04e00911314520320072800001e1070780400c0400c014041c018902c3e4611001d002c2e080307040407038803600200c4154000c42c0c1041c00341d17009441d010080782c0c1307641c01241007034860010741d407801c84000000914000600108116020f00c02c901003014028102280006000658046042d0b0104401c040d003034100c4500c0038019041c07001e40020410081d100039140c51102c400f0720f400c1085400503209000c1c0150100c250040b0140031010a56548040742038a0900a0ba103450041c80f8491168100c09048000803400511503021244407502c00c0e001c403031045403904443c1c401100d05020090700c03490411900f06a5648001350132044a0034424000d0030720f6142e6902d45034206889980d081c40060402d680d415100400c80c45401d2035021150010b01441c3d100d5180321054142c25607001d06c141c40921401704400f1140c90140a4141641c440c0725486159807208400514104040441d14003808000f14001ca0440070031400c0c24000c0880e5285 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 349762787 1250 349761537 349761551
    0x1606020c190c06020a05030d020c01090c29090d03110a0b1003050f01020304030f1b120e1201110a0f020102041a1c0c091a09100c150b030c01050306120a06 68
    0xa001800b4450f40300805541080d41140007051021003641d85803402950b025070303580f40b1084440e005089a0200521107211040c000c02d100782d240018100705a00c06a401c6200d6100c1c840700442401580c501c9988100d28000b07000010b4802c180420284145e4812a40004c2c4aa60fa124000300102c81c540c3c00d02240ca002001441410030988080b540c90800031071031806d0075140207010014082c090002d0103040741c034682203590b8003c150340c10143c0040c1003440c00450000000c0c0316011050341e0920075031403110960104441803107036594008000990a24044a0750b1050b940f168038400c011096550a100000301c1a0880c0e00503c00303034601044150381e41102da4801c1145008076516252414175000d03c501c4200e8000d0122800d0380d4182080c00b25a100300d0200345201d10a8014042d04415034041c1801c2583d084003140b0a01032050740b0f12007170500030058443c1200c0682c0c55030742d455849800240c145500070740c0295005800a8503041402e040f101c0c0c1c241c0b03085071a003404c5883c02d40d220b003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 349764037 1250 349762787 349762793
    0x1080f07091a270103111011071509080a050606040507050c06040b10090609050108070e070203040b09040f090f290c1b060903040302100c081606020c19 67
    0x8a10291010040c01c211010403951003149806006035110f001d8080c460003064109003039003100789800fa904034288000d603100c1c0752440c0c0090154030b0300341c01780300d400d12901ca40f14000c1500100d03c4442c5c0c0e0040c21202c0c42c02c01502d40640482a803442400300c0220003003203041c814040c00e07440e1800b0b0760007042c1c5c40c11708006000c01c841d0000c01c10810040280a001d0809102246240e00035410080b01d8465484050311190b10340c03c5948040c42c1a890120000342c1c0f00110340200341214200400c0c0c8201d540e5540340c802c0d01840c11034080b001038208200c10b0141007040d1001e0611079074007520004a00c070300080e50754203d4000c0003098a50307400c0c0c002c030f0004000160002c10b050148102e000d015035114111512541c80000d016820100404240740c0e58503020300d45696070400c0c00c03408540d850704010440c2512a802400280e00451003842100100d5020700403000303800d81c0c4090000e103006940d0503070612018002c9404c50f900742c1c003000f1400c003001c4108055011850150b10307001d14480d2901d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 349765287 1250 349764037 349764043
    0x206010504090209150102100213030b0105010201020415051e0f07020924121908030723030408130803040603020405030c030601080a02010f091a04061209021c0609060501080f 77
    0x1a00c120312640c20480e4640040c1c4442c1c46168000e414407140007403110a01e00140c2c24800c1e100784110040d0701c00301300c01200c44100e802c81030840780904100c1e1f20070b0740c0700c41c012401e07803040b80030f2100140c001c00c2d2106981442440100115000f14607a020103862003110019164405060804480c0c80480c8060540c076280c040d840c0c1140208540321244100301c11503070a00e03890660914410f8540380d0303106806030407e002810a514020148003403406043c030340311010350000d513102d20003e054a0016045507159101eaa0000319110042c141982d0780c55585c0b0246511454850800c403c8040c0c0c00290700f0810009007029107601d0301e0168880b82402c0900d8038241010014a2095010f100104236100380481c4900e4010303020301c0d0500010724490010750b400748142d030068a14941c1075692429240d011000303041030f91555a10510342c2c6038090b10b06000d80e03000c414003a500c20555010034441201d0401e4100c0d00602c9400c2c04a029a4542c50f9003013265826402101c10340c000a62035601d401d818 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 349766537 1250 349765287 349765289
    0x15070c230f160b0a120207030c0b1008060f072714040204140409050f1f0b010804051510050d05281e0804050301091109010512100213030507080c01020601 68
    0xd40c0003031946008442a00404103658852100d1039840092104c1c0b5041c424401a410f0100c501c00039075032101580b500900c6ca058100c0f06507505002c90300859005c8809084803c1120070110050500742c9400da00e000c0c51441c09031118003800b1805050344600c120071001402d2080c07025018a1802d1303d00020400313003000d042442880750344104030034041180301918076503690f02c080d20001400d501ca0b25205107045628900d420041c8500e03000d0320280701032034007010341002c0a40810300a90295a0066034890002d4030010210b402c415030f1522a134115901d03a644c0070b00501003a90800780e503200815400031a0101c143ca1a0f00000b80d18a211580c07904180c103191002000c42c442d08960b9114181042004240307030a104402c001c0190512014200f41e50142c81e0040003004510818544000300a85c400c03059030082c0c00103000011a80740c103801d00c50812180c0000b41c6003403407200c4d0712100290310134180064030422030800032000c00c0301000180098010080246050000300001a02e00101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 349767787 1250 349766537 349766563
    0x2040e072339014b090b01090618060509041103071208220f0b07050c060406050306040b010806010507080c01061a250c0509060411161e020315070c23 66
    0x840b40440460104200421320015900342c41410040d80884540001c1c11500c000502591071501c0080303040c0203a944291304980d142540d030552444d41c07443e600b09403102c42c440c240e80084108001004954402e0100000360801415222000d441d50040d540030036407030b1000d40d0110307800b0825400484040c0d0b00f0070300601c480246256205d280c0002001c03000024040d0050003a4041021010070400b00030030004220002c00154035142c9540b4001c10780c1e001150b0082c41079007021030007440b6501904149010b400183d449601d041440d449220895004901c0b410242d907803144c00040c0b4113424164940700900000403955218080e4a4010840d080340b8510406c0000504880c2d0009035001c00c46c07002ca86054410094075520400001c00400a910765030002d66000203248070101c03048200c80c42c01c6480b07203c031a910304464100030b4550510702440250150300414403025011001d00c49181e1181d82454080a00300d0650780b003031074070560351540c0d04102907224510035600606000001400762 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 349769037 1250 349767787 349767851
    0x90209090616050c12031503011a03060a1a060711010809010e0a0f03021e070906060903020a03080306130c090906241103070602040e07233901 63
    0x100a0711006240310441d007060300f8041d0003d035403400e20340305021401084501298043e16454500d03142d141a0009400041c403952a10203841408203540480082080f80a00140401e5403851803070401001c81010306c1d800d04e084116215050b0303407014010925544200c4040110310781440c00903020346070181c1990721a9041443d940c00d050000141d04a02ca600b01024041080d09070038142d09203010300b1071100038400b60102036141c1c000d00203520b400b00c400341c00307080103400d54604044400800c10f0200035808081c1c461700300302141c5c014001d0341e00000001c000544040c20105072408503071031204840040307610f0450401050410744560b100600c046a1154540b8106559031150403440f4807129050040598514403100002c105840d41c4550148046513290303156081074032081c008440c180009019104c0a1110982602508004945580c4140c0c20b0021010402281110a801510b0900c2d1881c02d075021070600c42d601c81c7c8840411a0001545d0502c01c2400078043c0701850300001160 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 349770287 1250 349769037 349769041
    0x8041508010803070803161b0302160803090f060f160c150c0305270d060f06060507020d080a020313090203040b0a0c05160203101b030506031204030b0a0e01020a02010902090906 78
    0x18111703400c40340d02a00d100c0380c003215080050026510b080705140807191050078260100201900041c45080d408140e00c480040c1c940d58071142e070340e24402c032041580c2012116120880031f080940281c801081901c0881c0d00341240c091550b030740000c03085015290494440310800100c4c0ca01d142c0031002c09000c0c5084240360f00981c401810078800d250075024120300c0010704110762605680d0701d640d80a0003c11800c4a4922400d00402400034a00d0b800341c4603160440000c0d40c2c41c058012516565405000e8140728001a20b07408202c0d04440b8411040d408200801c0e11540d03290f849100180550702001a141d041074280f18284a8004000510580ca456089482039401500307a40d440c0e00700816401d091003842c0b02090400c0c0d140311501c20614203180c1c3c00c49900000d803040c1a4802c44a6408112540d900302c1019540c410107401071608072070070001403011502c2540d84c2c03503004152680204842c0c203020482070072079000c0564400140d540c3c2c0346000852031b000004682243c0c03154002d00c494 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 349771537 1250 349770287 349770293
    0x607142103010e061c051e06090a02100c0602040909080403050f07060e040c03060306150617010f0e0702030c07080f0c0901050604090b01120c080f01060c051e07030804150801080307 80
    0x1600a000c1030f101d80170f41d080c0001e110045198808116a00c030342500c10804005035410708000c91258440c0d214003e11000486074100000c17080c00441d0020414007000c81840740a0361070701c041007015a007454003003001051120481c05050a494898401c41f5034803803541c00d21504010300410b08188a400c40c000400c0241c0d030201c0b4000801e40200e800245004803504240c0040203154001040c440c00c0c9580940150003405600007211040d0b19413010303004500b240310150301402d0203076402003103112800f407001d41c105520700c5500100e00c4c01124034100031000d20920303180c0c080e84509a664410103e080502000740a00207419805641c032000c07650400001440e540558000e4085107955020410403d80c4038084d0300c3c1a41120100420104c5000d81c402040c500007155030030002c1050400014100f0b215186d82d49502d074004c0085c040040240d101c00804000030880a0007521520802001045144008100416840e4224003000294680280580c1d505900104003900103000b49404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 349772787 1250 349771537 349771559
    0x80105060916110610030c17030712090803030a051008161202010302040f0b030103300305090c1201050609060316060e15040b0306040f0b0a14060714210301 69
    0x11612207103075400b034001c203204103e0340b03002004650402c0d0300c201000c0c03150740c100300364403101640e010754208100c40d0b03281d100700d035a043c4031031254410380d80c420001e240104850300708515003602035251040785150369550702440c2d80c0064590702030442d602c00510407a15051450100282045005829071000c100709560018586104a900304c1c40b803441c02008581c46a41241c2c00380c8503a280501c401920391400c542d050308240000c4502031001c030b9015110000155252001e084039580030b10308030900c204210b000d880301504401561080410030441c5a480040811384019050300006540c03505c40100581c5203005003030580a9001070108070240010031031400241c030103c0c02c001c4191000c007000305000160040c486d40307503440d000c20041440c800c510300941c01114100e4041c09101408140003048a00706c031503555000d5880c3c14108240d002c03000c0e2102076100010021402c010b003549442c8113005036201d54401d241c01091030844841e80541d460024010036803a43d038210743c104032941903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 349774037 1250 349772787 349772791
    0x3030409091b170703030c11100f11030f030a09030e100e180702030f180a0b030604150b0307030c020c1806010f0201090c0501030209040f0f1e0b0f010e032a01090801050609 76
    0x104100403031400800b844a400e0540781081c01c05440400e0303001500c20002c00c003119201000000905402d041c81c100d03880033042e68442854041510b185850340c1d07031003000074903440c1d01c00c50610040085400c01541e0b503154142c803c007995265020341c0d05181040000c0b42e091980402401c01c003c0040c4040b6580c00015a0410039010560300c3c1d40b0314408030385611104c50000d86030360090110740c0101d00c504122003e1070190200b5a410310075030b0081d003e5101d40c0314003406005039038101807000540c0b8601c690003940c000b08183c0183c4110b4001180417031075200740703803030a5019980340c68148016035078094036106030703c0e95910003080980203039582e16441d132007039110310f83c10180c0105600c865555aa03124180d800704904080001c40c40c2c03c5420740192990091108850507401c0b94031200e152140541d0b401000300401c03269681d00207130015645180400e9689070113220b94050700c03c0c1c40c581405803e45007205400c2501c0710031840800100842050b03007101e1100e0b41000e00340a0fa075151101016 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 349775287 1250 349774037 349774043
    0x6080312071b080703020a1205031621050f0103020312190c0221070e0a0603030c0813080a060501081009030e0d02040e010612020f090f01030b040203030409091b170703 74
    0x40c0745480060034040e0100b140420181c03441a00042c1c1800300350b0009105075002d88a902d202204086204041c0c07050b0000708c8002210300c81d10340880e4031941c80303044c8841c401c450902c24a19101f49124082e4111401150030124a01c0c0c0e1400610652500f0080c54130001039001c01c0900d80b003007086102035a80c500214030030a20582100701000c6680303001d0312501c078030788203210b205d90095074a0440307680c3d40b140c1c8104216591780780c020034540c0e42940590015a034064489021a0281c2c0e42c078100c0d180c0c4503506129241042c0c040215034503500b800070200300d902812000c100d44d410081c001d0704014005a440015525003c0b00e5400260485541c0c0140039048590399a00c2c5814004100940080c43e800c3c61154a808400711705c400d900309030080341a000340c8004154081c4c0c6024842c4094060383e504840b19150401040012224181642c6c00703031025043d00d0900741d44031a800c09440d00260101c4944070b2044030407003040c1c030403644000101641c446501281c00b4031020725445094901006e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 349776537 1250 349775287 349775297
    0x2d010c02070e0919201002061609081f02042402060a0501120b06010e270a0203070806150c070f030212060c0405060a051908011e08060105010507020102150a020d0608031207 76
    0x99030b4080140e0a403892840000c1d000d50325001b03000c40001d4031030000b1a91549030740104590b05001034131642e41a0300341d0301003000900716031082c0d0004020413447c4070404e0810703079004c10000c40d0f852649020811b184140c10381c031480e40c680c20a4042c1c00c1000040418060510f000010030481204092010030ba0381c110a01382156195080100c0b1003481c580c1e85a900050444102c5192288400c0c600328801d000707520010864441c0640304050b440140d42c05800204ca03803005ca41c0514000004815000c2c0080c00b01d46800a00c0003424240303492039201118035041004200107508043d090210920006030180000b85882640942d09025500503680900c0c3c0c00325a198900d03000d18119141000c0c80402d0100003030b4040d00042001e40240560020940503544068000072200340c080140e0718450f01070001b0703070300b4000111050342040c0b400364118860384910030086c1035422a4180105000074015a80703407405080c0030107807040342c0d000022940c010403441001512402405410801c50b10702 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 349777787 1250 349776537 349776563
    0x20103110706090c0504060909051506030703060e0c010305061002061902040503060406092a120606150801060219020d060b04110d14070c03022d010c02070e0919 71
    0xc859514050248000e01941c0382c070901e50f080c400c8918502d01180c00c2207900f40266520b440c0180143c84002000410701d901c020144c1c41c03da03807404411a481080a82114030a03540c03900c440c0d050390b11101080c2035507041041c1c038040c05c6d681030103120342c0b001d820380300c0b152000c42010f030080d40c810004002d4580d0603403441e1200c905401c0ca404580013003400a08071442c1d401c20b0f0410710002d101e240d90440e2200454074421454404042d10007427444450041131035144d20700141030943e2090200100c0d4101e541ea100803074802d14440030040018032075943c4000942c10620080c2c81c1c843d5034403d07000c55490101030900141d44900c014040c440d44014081800d070315900c0424090f00c6000c02c50003110304041407404520041e0f030300c80030340781c9401c000f51486030302ca001c4195104902e4281c0078006800a04013240c4004030060560410f20007902c03d01e401e14651041035003103400d4041000b005030883c0c40f0800645906201c4c55030800b00450140c803841c094080e00c955a030b80100c00080044080c400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 349779037 1250 349777787 349777811
    0x60411011101020a0302031e0412271205070602031314060d060602030a030b0f0108010504090f0c060c150b0a03030f09120c0e0a0902060f07020a0b0703020106030b0106030b0d020103 80
    0x38100c8041c14034403000b95100c828620001e03004e900107d03600c4500c00c8080c41d001c1c140041c400e1156000c0c540003c56180d40303c417001e900301c030018001d0b400d00b0310004041d0040e80858105600a100820b4511002d40f01e41c000d0386401c2d4100089a4040d4003103600070f0100683e20300301092000101c0350310b07018541604035400042182d5000b034008111840c2d1030b04034009841234012004040700c1059503410000e022100c030070030031081c0210411a00151410006025500780340d03200d191854003d4503800002c1c8003555801c8080c11141d009540001c2d20410130382c08010b24181d5504102e801101d05001d552607540c085400d000c204e120250801200b00c84409036280920076010280c80d99251031040800141400d035584000c4d4031a6000d02043c10300020310002942c804d407464a6401001070345003600050b855a207541100700243c4e40014032200018900401800510300340340301c0c0d00007041c070130f180d402c0c10020842c0c164000700506040480280d420b07607907100c004400380e6090800140850b5501e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 349780287 1250 349779037 349779047
    0x40503271002070806010f15030f2c0f071d0601170901060f060531050d050c0f150706090c0503100f112a010b0904140106060504050306041101 63
    0x240d80070781118510102025a0740e01003103000035908414111101c0380d80c1c4041c1100c508000b482020b0000220919040440748030b600030b04281007a00310041045a81074140205003502204040310074030b004440410344a40500804d003182e1007400117407041c1460040707014400308080c0407208020883e207001500ca6805480c00b8042c08241c600c200e0114a4442001402000107005071200740300341080014640344141e080f02c00d070082c6070002e43d0005070315103010950980c10395004292400000d02c08034080d2a00154607220500480061400d101c0c0300041c0407900c0040c010050242400d0991070304441840c0b4102c0307403480c1d40030100140115060904209044d141c1d00003d80c94090300c2407040c0c0c0525a41c105071054403550b40100719150710610034000d144103400700036000c0c09043c0b500c0e04030300d018040b148991020410021034040c900030001903400504440c120792181696181c60810b807000d100340c0000d850b20742815031a146c14400080d40e40c810051004100c0e0800c0303000041a0f0348030b5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 349781537 1250 349780287 349780357
    0xe032808130f05060a1e0302091215010f06050a0509040b1c020112050106090b090d080412150207080927130b0901020405180c091c031106040503 64
    0x10165203480054800700c509104074420001c0480044101046030314003803003200c084007059115007640580c0080580d031140340003e8500c0c207042c0d0a210114007500c0d0310040052141e0300c2e201070407090a0030400301942c1101a0000b82900269040c1403000303a40200480e043c8903050b0034a2501d50056800003005800c464800c0c81c1c0020501d0758a040040c095402189000d200340c8906c08204448910382044039024482e940001e50b064004100e03036801500140300006001e402c0c0d09014441c2c0d10350b05070950207644039002c1c0412000901081c01403008010300c0c254400342c402d500c1e003400d580760101540070382204103214841b5a81818442c0c0344001001e03000840800c2e80150301d2410300701d15030703112107810001d0310019155400a10110300620884003a940002c0082580350700380644020700d40f000070701c50b00801a04212011103650751103007005a608080110400d0045246030042c41d9032880e88107103045070b0005041c000058808025218160071080301c1c2c0c51140140c071030514003003440d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 349782787 1250 349781537 349781543
    0x121b12130b131a0403030201050612060c0901140a0203040503100203040f03080a1812110604120305102412020306150f0409050f0a1805030d020306010302042102100e0328 75
    0xc1a214a0f03c4880310005001201d0294008002907541c000c18003841800d00380c10b03000c05070414400200d89400c0341c002f07410f44020601d0b00c10104003060f0f201000507404000070401503032010800f0041c528040000901d1500d03040b40641c290b08096645c40041105c0040003410f0202034000150f1000305a440040c0c0c458071103039140408984d5040c44094140031030702a0000a000064400e43e40c400025554040c2d540024461803010b1190000c0300107010140c9112041c01c000c200005030315a00b02641124080c4101c402c0610390b80b10603003e8401e030b80d0f139004030104900600810046070703110080c03182c07613211010040ba0b85071481d844543d41803085400500c9858507080601c4032605112001030320917010031504109002d412101214180034411000303055500c200100c194020054003c1c41d00a10181005070500b0307100c1d03204a0065644141d03903070350b04281c0c050350130551515812030741c0002c60310300b44041581c008802023900c5004030000c0780e103008910310480520442c00c060418000d60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 349784037 1250 349782787 349782809
    0xf0402070b040c0906090204060203030408070f0b09160e0702031921060302030c0f03060711010b0a030303091b15050705070b03160906050f041403121b12130b13 71
    0x24242c40c2c520b5410388a1300501001c030f80b50040129005a052003140d00707503421500110300b143d403039941c4e2000c186e11020b4212082d0050500003030014910181d05401804040060480d001d0320398540c585040761607000034414410102400030380c94021048a11842d020007110498030785481041c0c6120400100c2031043d020b02000d000c0d203503002035110303105a134400c4050380c076401001c508014441d440200312070b81c5508500082152a8010034212255068074000031440d402e640000414000096000340c011075120401c0804202c104a40030703400154940b09020300d40e013081040c0c65860b1080c03100c50103008000071004140301080081d82d005186640c18a40e8174940011250200d402d1451810b01151402c600880c60070b002d0011307502117410307040780b00d82442d03e080e410b509005811001d4540602036610424010004800186045001045950018000301800c3d501e042501c80c0c4007200200240300c03000103900c0405030780048401002506440321102504c5c175103108165400601c1100e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 349785287 1250 349784037 349784041
    0xf1009080f0c13060e01050d11040207030c0b060103060602030f070c181413020d0b040f0b0703020306121203011a1312030e0d051c140c250605090f0402070b 69
    0x1c005450038400302c0903501c0039205403070640c8100584111780100181055054018802401c001c8041103126008495400090041c840030804903800080c040c0e0010f04585200030902100350306880d0030190071b1030200304841c9400e50094a030700401d0100b0b0400140083c50030240001401440c1c054403010b00203503048a84081e0351001800b10010381e1f00308007260000131301e050708100178412031140c020b807200310b110130030780e03201a150100100704441a001c008500004100d0b5250401d10940543c2c400503500c2c1403500400062000e00e548224965214246000103181900d040d60f0445441070340c01c0c4500c0f144213005859601802450542e00042d2050020310b6829032071030381c3d01e81030198540c884494950414451240a1454058040c0e80515000c441021081007804998a0741d482c003851844000e03038140f001d5030b0060400000d41d40c0034002010360324024240000c0f030b244250501040f903c3c9004409055805207102c224402c1c0400b401c0003540e621a9012103481d103034001c0440c0514 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 349786537 1250 349785287 349785313
    0xc0507021504050a0e09070308071a150316030f0f050c100f0e061603140405062a03031e070509130f0c020106180f180804080d020304050f100908 64
    0x142c01620610344188414000000c03480e40603102c5902910000f0050701529041da10f03024003070303030000404990303450104100d032400c00c4843d0700b9980540076100d802e1416118105c02c0600d01184402c60203914210010100001003060780313031140659001500c444806440d0034510700307004003c075060f60880c140004610a0540c0202034689022040d2100c0c081042a2406d00149010f0a4841c0160b00d43c8081c5400209014042110401e00e0041c850380c602038598000c02c04070307084040540c101c0d280788100c0c0030701034004110040700901424010340c19868185003101400c03010f205580b003884062004145068424000c44004610140813000c013401a07114480c01002e08004d000314451400340050700c210700c103004d0041100c10161070105601d69101910000b0041c0c4100f001d40c1d0f0b5940c3c1d00071204c20b0101d410b8a454a80a00441c0703440b18a45108136003006000f6049004540003048280142e0b0f40b40d603081c4007100c000b503c0c10407202822000a0316501202e8120980710f1041181906207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 349787787 1250 349786537 349786579
    0x1914010c0503040b0108010b0609041508030c10050c030402010806150f120411030708030307030b0406091b0906030605060703050d29032407050f070c0f050406080307150c050702 78
    0x6180301c0e000c40c08185c4e03aa803034090b080b107442d070f445203900c481c0800c1401014074150b040380c05130408144020214503510b400e29851036002c81c9000c400c0c1e4105c0e282d50112400380744201d560043c20050a1469407400794002003d2010051005200301c4001e00c590115850600079502d0310700e42038010940c4e40041605a0804210440d01203451180c14240c00c2c40a0030b001c9003403021a2900b90040d400c54035551320030b40191070340c0c14003150000d82d0350340c00198450143c0103c0351000180b00300d2001d0511030100081c03a12500303800c07034024942403036800c02080e2911400c44100540500d000c40c1c0790b18030440040c01410030364a039210702c0802c81612403107280714a424402041c000b1811950b96000300c41c0b0115400300910040b0a441c00a60001848140110001d0038805035612500c0d142280139551412490469001440c84098680c1d06111a0416110740400b03086114001d50901c483c65840460340c50224503419a480d80301c1c6084a0018021819550f9587d03009040030703a1035035900b00400d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 349789037 1250 349787787 349787791
    0xc221a0403150216030305060d05060103080a0e0904050a03030c0c021e100f0503040f05030c06040302010b0a0902090603070c060b03010216020315130f03090b030a020a020114091914010c0503 84
    0x900034006035400b0901401c00c0c402c9411003a41d0f8860342240380300340c0d10258000c00c0000c101d542c000c01c0000d407110010b0414881d140c0a148100000b0b41c49441c2c3c282e00a0080201c03c20040c001c1d681c82082c0000314500140200c1c2c4540d0500c1c0200c0da0500b403900894000c011020000c0d0410442701030034203240c588182c41e040100b001da514000e090305088085078018200e84011010403420800328001c944101d0030054a18041c0084910b404010f21205103041c2c411174040d00180d560750490f440503e005c000c1c0d8002081340b01c05c1907080010280004110340b10140000d01030cc41c4140f800d50410180341c004e407a40c650700600845d03e6403039031072034108860141c0204a209003c1d0000c24240303852001e070440e0040c200680070340300107070081c0d5605204403040e01064040c8904040e000900501810086109810702d031000b580307841d4022000303425280000103482021900f002008040070001682d50708a0030880c11440b801b0344581001d000d07005055018004550808801c080700720b412000441c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 349790287 1250 349789037 349789043
    0x1f0e13140a0b0114090a1d041a01030210030b150c07030605010506031b07110316031e0308191d06060901090207030f05030414060106020f12030c221a0403 68
    0x100d036644141c040001c03150110003860101321100c40c142c1d640c4a0050182c1001d04018140c490701c1790315810b0b1280d09003070200003003001c101c1d85000c100422085032910031ba07204030300c00c1c0c10441794190390019010032440301c103c1c000c01d03942d13040c40c0300d071030f9501002c1c04000420120307885e0392040a003a001d40c41b80d21600082c0d0700181044000140c0d42004001c4911503840800d41040354942d000f015140c40d8440032080c0c1d00070384400c009101969041c024101004010a03800b4066440c0d0301c0d01d038612246425868108180030102000400c2c6c01036a16a03005440710311040754003040d503542d03000805001c184a1400b042007803541703144e0000000e43c0c42c043d40080710312a0072683d803030741400d00364803500300e000703000624101c0303155609400b8502558210384180b82e00780204070891100352600900340d21410059005030260348550000340815041c5c0d030410a4282c0ca580f5081c060758406129048051040b5030407010b03240c0c420140c24a01001074440003c140c911054401085500c41d00980015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 349791537 1250 349790287 349790321
    0x1905071b06051b070203030d02071a091b030d121104030b040803060f0a0b070807140607080f10060c1e051c0f052703030415120b010206061f0e13 64
    0x5400f201d00310f0098412042e80100210702d07004011072024042c1d0402c0408542061241190ba05080a1180ca0a1094071040020111051b501e0001003040d00d5100362903001c1e41110085441841e40a4107003034110144101c081144070346000c0c503803101e1189078130280a60b0064024003040100402c025400b0743c104440c1c030300203205440200044da500e980f29080306440204001d04c0050101d0018111240c01010041094a410141c01d410a8411a015070004160004100c0000350200815400c06a254a0046a142420320162412804170b0b005000f90b0b1084040e21002002490b0450001e0b81c0030094403140e013090b540041070040000c1c0da08001c1507141210242440c480c0e03055a6082550622022121010b10111f05526101540c0c2c1c6415010402021034044444180b05c0d80d0030119968180361100c0860120f401c40d20720005250443d0031007400e0200c10303514080783c01000b150458103100e018038010030980d0b0301900f04034950b80280311010f612003070a58580c8041d03088400c0c5092 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 349792787 1250 349791537 349791571
    0x91207030506070e010c1e02040c030f05180709050c0f04030b07020c090f070f03060902030c041404050f070f0e100f0f0801060f0e030a021809070b031905071b0605 72
    0x140d1380c0b00250700e099800907070091281c00210303940210858619100c00c0d00d80b500c0c014150003040c00c0c3c540501c10f00c0c0c08130f620744042c04010261407064640c0000000d980010540d5907800007030b103034102d5106800405031500701003901440c861044541d006000f9030b503642c1d10395491a044040e001c0c12507282000d802822124079182c10000c170340134030450311030300865241d5a0f0000150303000180262420200b694a1a01143d2100c903440218000e26800144d16140c902d00040c00d1089814014000d010303a0070702d014018120703014903001c1c0d0000407a003006520f0030384003802152010302c200c00350340d401041034041030351494102c40303140c8454103203a45480c201001041e0903038140e44203116000010b51181a0404050b02c110a02801e250005040e0342989a250300042c403c802c104c26a041e29204d94010b0201c0b00104228510081c50303084003641c20f508d8003050720030605070725500c1032040540b81c0000030042481060301c1689842c110381e0b04a00c25040e403c04034000c200464001c10581c00c2c0801d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 349794037 1250 349792787 349792801
    0x818060f0d0b0a0e090703060c110d0306090b03030918130818010f1b08030601050d062402240604090506070807030e0115090e12070f03080606071e020303091207030506 74
    0x301c1d1032086400c803005041b01071031995004000e0070301c00910000c02008810a444594041c050281d23800c04035030700820400c0c10401003d017207031241c50303c2038400d9004004c3c40495482c0d80c0401c100001c1002d03e807004035031342c3c00c6020020740a0031078002c01c40c0360001503013180c401455042034000e031420303a0f42d800b00c0e107040602901c40203c0801c0c8440558034409120740041d40220003940e2080e01031401c0b500b860807a408480c01ea55954128042c42d081c000100c01c2503500c003040001028140380b0090500e140d81d02080d441e01400c1091005144040700005421529690812a0000d41c800100c03041480d02c410018044c28056031090001b03410100014003507001405280400f00034200c0002c01589015018801840f40070039120f614010481180c010601e8800072b06a0240100403040988a007440c004050640c0184241d2265106100ca10701080040c2888a0703c08040900c030030040072540006841d60054048203603000041038402c3c1409030f80441c440085a00c1ba50449443d600e40031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 349795287 1250 349794037 349794059
    0x1f0206010512060402041e0903110c01020303011523030403020610050a0b090d060905070e01030b07080f01030f05010e030d1422120e0315010e10030818060f0d0b0a 72
    0x800982c40b43d2004000c40c01501c1d21354080c0c90841001b046110000780960044d400b0303610000c9055022800c0380181c0e641032703c1c052007680c1078001d0900c040c525540c140b403041554281c0380c0010b07a041148081c01c252134041c0b4034803e00c800c501c420000c1358a914041c038000b0f41c2d404007141c1a90707425141200026507801c100d284801607a06803008a0300706100042440404d444510042d10030304c0e00c1e64010b01c0810018004c15000e0040751401610944c1181841e0581a001804170010418850100200300f01540891415207a01501c01da039141480d080141c09132014000f410800d0000060342400b0041039480b0380014008098003400654814449110502020758190002d0340807042c7c120018076490b070106041c1840d428005100061180031a250089019000401054034401402210804880d030381d804aa01c5914000300740c1140d444d074113940505100000310441096054040b951440c05951400aa00d085240c940c1d01840c01080038100051410307002d40c9400001142e40c0c0b54030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 349796537 1250 349795287 349795309
    0x60902090111010c0519091502070503061806130515160306050d0209040311030f040303081509100b130e0907030605060108040305190306030503030f06010807090f03110d021f02060105 81
    0xf0b85820b0305000f94100c1c03210700c807100300060000f081f46c2d06402003006040904040c0c030701180c42d4000c00d011820301d4185854010094400e0315400f10080c0c00307c8007006c001a00681c0701e0019030542d680404d2300e2500c00d18190800a0804401024108012004c842c075512200900c0c86030350240402560784090110040c1d44038000394100300b0301e00014021a005a8001035130040c910101d81ca400c004845440d40c44d0055001100080c10b00000e105207680400c41845141d80c0072074048400f41040412599080e600348946e0401c12000320350982d2200c0100c80d040300800546d000c1e02001e25002ca446502e8100d1404221180752a210100d0065485028145d200310fa042e11030070700e410400d4401003000410b590440003055103070748000c00010020700280d8010b001007001802c071810030300c00160040000500d80c500304041001c040000342c1c04240940100c1e03400c2000030301040c042c2c60110b00840201c7d480a90042d02d040080c40d000c1e4071241e201c034001c5400364242e0721b132640c0303030810048489a5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 349797787 1250 349796537 349796561
    0xc03090d030e10031418060a0c09050307120209010f1203031109030708060402030d030c050d0b0301150b07120e06070206070c05030a0318060503130204021c05010f0501080a050c070314090406090209011101 90
    0x4038100140354807003250700c6058609d2040c1041d4062070b90700c90000340b03050555000181c0580312940711108505048403000e02414011207205005400c0075074010260601003800360400d5240c02a800c01000d83c8411142c2100020b4169024180c4a84041d5514107003079504a02234812199070340525840f034401c4130a5034025503075151400100701800d10242800b11a600d506540e117080c03013113010f0560047e41005103254440c55485030320070700f4141c0d0a0800b4442503030074480e060483d6402c03a507406080f180810341c111b031096168131040c104035801c11680c0d0060b94151040d80c059200303244c0c0081074114101c1d84110850041c1e515503100302c40c03e000c2503820045280f00500104010300e0980c000c2c0226034030581c4206030414840c01442d090315400c2e03110300200400180140525680083c4681d4080510b600500c40390406180c032060f10720460714082c0070403016a400e421317000b281d08102d61505034010002d1001580701c52100000307602025441d40880c580c040761400c4644103010f40251690 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 349799037 1250 349797787 349797793
    0x605030606060310090f2406020303130f060501170f010b031509030d0c09140108011d0405070e04080406110c090a021303021305070201110c03090d030e10031418 71
    0x101c0364144081078001074411801990061030200d9503410364803070040072860701200071030441c0c4054604180c50192078000c2c01000c034001d0060114540001c216070b0020041050105040064105200c0082005400804c010305100c00000c5140204025840c60343d602d400761000010008000b03800c03503141e03800c61030b0590045401032200a204d0302c5103550280056090701e00d0103400c403036140c1c102d41e205019079000c9035038948240560208e5036007010040400b070030102c840c0c1d41000e640c094a40c0070b00040035814900d000010f010458184220002490582ca00180c141414600940c0320f420a00a41001a10b194240c0078030a000041c4403124a030040c0240040ea11450414406940828041a00c81c1d401140c00001a10b585030b4003200414030400000f075508082c10001c5c00c2d251181c4a00704818814090030740c3c00f04c000300c00c0302c010000c11603511941c40072030315017920034519003101550300082c0d084108440315015002158129007108e00301900c1d03542d103049040003014120216215078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 349800287 1250 349799037 349799041
    0x70e01092a0206070207080114061c200301050601050301141207260c0102070501050d0f060e0f090d081e04080c0d05040807050f10030c11161806050306 67
    0x108007a441009140e4050080c0340704030001100460300740c000c00080d140140d0018082201199052180c5406094600024003000a041e5107009480780c0c080c111030708c100c65818a44800418014a240e407141d840720445056659408626610345440740d44107010b5404d00000070b50b00d41c4a00100c0c0d040c1c6201c1c281d04c005282100003807140320035404048141d030b0303c207001010807107154941d1158185a2030110345080d150b40d8200039814020a200d213203065501412040c081682c1101c01e1380c40c4002041c00014192a07000e01d2480500295030042000036a0720701404601680e1805c403c0c840e480a030111200c40160510480f52900b0880d074802c4800700200450080300302c0ea401c15908a40101110340c00d004101020b24208040b00ba07864000c10030008003008540d0050021600801045a41031415401c1c0c0000c242d00c0041541281c08155940c0082c0d5a0b090080101d14640640403084442c8481e0681d24640e0302102e50140f40d032842c010030342d8600d10a06034042c0e5000d80b640a00901402c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 349801537 1250 349800287 349800299
    0x180210030e1e0a021311030609040c09180b0601020c01210603020306150901060c080a14130603020a0311090a03020108190c08071b0c0b0a110f0106030212070e01 71
    0x1014070440c503444600440034000d6400c80e1102411038040030960152407080403901c100300c8458011002c02000c1c90034201d81141600410090761380c8480183d901c41201d654030702c3d09030101806600200c01c01c9180030811000c042500b401121614070450100845031181c10040e60388094a0090310300140b00b03c0040a084184030000700101c240c07598010511907203d500181c00c2c02070071100b03000b40301842c15a0101c5c030300c1c140820306d004107001d040c241418101d5849100480c407400000b0400e0054090500720902c038104121400124030401c440b0440303880741d10090207540f024200e540001d0a2802105e00154031701d08507078182000400200e030f080d14560054a2101c00100700c1c4800390540460220705842500985084003100e07628600c06203852038024281042184004074110b021408150000b850b400b5500292060140056210403000c4000c55074030000d0000e080f0b280c0610341c0d403211040c1054018030103a901c200c1d201ca00189404a06660303405041c0b04000c441c0598000410007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 349802787 1250 349801537 349801541
    0x60402270a0c11010207080915070f0f110607030324060e040504020604031a06010318030f140c0703050609010605060a0212180418030f052d0c160918021003 69
    0x8102d00c07400e081d500310200403241800ca03004250262035004000545954519000700c07148071856039030910350300308100d985400750b0403541050010841d10700803121034184130480144070003a8400400c040e548296900c3e009022348070a0b80310b0400220805055907401c0c1c140484d040075218035a8461001464000400c07026100140099800c030004000100119013500c1c07111240e00703203800a91000f401c00a0004003210140001c10018000510441c000a680903209849008507842c008451101d03c003200c0d840c42c0304103402c0018501c81e1802c00401c10a01090140c82400c85d00004c0080a54540c28840144500201c9000507040b0b10082200b42403d400502484820307d0102640c4010140110b01100e50007a82c222100714a4805e15007010380c0034000030917031501ca1501d40e0070200c43c011703410f99040765841990180075400150b004404030b41000d6840050a2070100d4a000c002c0001c4140101c5160180001546c2000c4400c80e8968046c01d070404600c1c0e015110126400042d001100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 349804037 1250 349802787 349802801
    0xc0307050f011d040204030302030403030e0301060b03060d03020c030102220f080a080c0c0a1205241803070b0115020613030e0405060d061506320c0703060509060402270a 75
    0x1d00503031074540481c10b5159172010303001442c800c1e00296a924190b09020701442c21000015111f681410f00600807070032004140ca4010000351424003480015260980c24180d001c2c01c0c8641661020030780c07211042c24a11103000d0075070041840c001c05500e50141452002160040881550090210400055544000380641c14004056880060f28032000030482c20aa9100414403041c0c501140d060080910200a000406100c0c448051035805803621034400000c02d008215801c2d5036030a104500c050040354401c0d5400a554106981c441980c6840380080909c40c0c2c0c0184640c0002500204651540c0001d15416860303110072650401c3c1048003600d40101040d400c4034550071345500040301801100d0310b5105034007a21021230f080c110018441c4812172010100032001d10308088607040d40d10103101c440e0b0300c0780040301c0e9940792820b001450030b4050b5100a12907032800c002c0006031b10000c26440d00484c4221440c421550321110070f050940300740780761f050040640c0d1010580552890344101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 349805287 1250 349804037 349804067
    0x17070b0306011b0c0605070c0b1809070309020d0f0c08150402090c0723010e07050913080702060a0f1b0506070807111504050c0409050703031d060d0e0c0307050f01 72
    0xc0f003c038807130366031403011500c0c0c0c0e4490808508041101c2c410040c444030785001070300942400310b040c54948030b19551601d940200650140c5611408283c0c0144a41c021060b6541c010342100c00d0440a450160540c5045c5441600c0304000103002150b20703000880c1002881e0750701e0340c038001d164445808200c02601d0250550703d842104000310703030001d450400311150703100f4101042c1c0075036100c5035600e40c213580185450f00100d400801044c0001d5230f03080c0c8129003082107a0010305c0310207614941502613105480c0003944c012400700703800940540c0150419200c00803a07070744040da500c003007081c01c0e070040c90030f0b500802c5e5070414000600110310881e14540e0080252514002400030f04100c5030400c00030240d11503031584400c0811092000c100b0000109071002d403410840e4140c1502c485440d114030703002c01000c21449c400d0a1802c2019400d8150b1421002016181d031039050510b1036000b0a40181c1e42c110030b00904e8000740b07081c900801d1180403580c0180c00700018501d100d00454001e00050411 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 349806537 1250 349805287 349805327
    0x3060b031e010b041b120209032103090d0509060a0804110a090903080609040b010b0a0908121b0a1205280206040c0b04060e040c050702091017070b030601 68
    0x1910840803031485a207201035508000114001840148000d1300e90401e54160302c0310500c0601001d0715805400e000e51883c0750400140c0710250500000e080c4151100903010b00d500307000409203400e401c1002107004100f61001c82e4820012240180e0300d0380507214403998030610a00c20071102a0103400d1950b4054840c56860700702c4601c2600044007280250400341441e540c0309844000c250308200303095003048042b18042a2450547c0e1000449035050081010b074a50100d07211400b24000c0003040044e241040907070740b071800318081821040e0491021001e07003550411561441040c046210480d442d040307104600e10305188030b0265a2070307025059003414040070517160a40f1401e8610702c0059006241d02900c01c90609007481c440c1040f0320342000c1d49140c000c1004100503500a030100c0d0800005840214510380b40010507242405502e2010b504100c1201c01c00c910ba18103894150f06440e0721156000300180f800c100d1384e5581c4094011300807082c00803c007003942580901c1640c0e990075040146 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 349807787 1250 349806537 349806553
    0x4030c02011202120108060603011d0a02040b13050106021f090c0905070c050312010603110a020604020f0d050d080103060e1207080c01090212060703050105040b0d030305100b07050a020307050d020105030103060b03 94
    0x61030313400101346d00646c0103402950911005180a018524813501c26040800700100f412006984904640700002e00ca41d50b43c9043c0045500c1d150703142050911941c02c208442c0da960400a525a08100c031300341e030400c10180e51181984981c0c40f90101060b00300403482e000d43c4c1811005d10080c071010300900c0600a03898107160000e1000c0004001601507040030341c009500d80391018060340e508003510310070190240115039025600041d050760164044a0003440f84100c0008500c051006443c054040d002d0924000f0b10183c222000c2412244242020884029540345854031142110744405070010104102008a207040014040b90b04c0340c040002401c0107260700240054015550b50b6820780c02c003d040062281d0107100381c500500c0d05035014450b555103500000c001e0b203042c400040c1455695000710b80c202c0200107418024040306d4124564801542c1810b50380c0d0f020310b2000b2840ba200e1998081441c0c2001407811402940c1a1140c0c2d085901307554901010700325800c00703540c0600c02c0b025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 349809037 1250 349807787 349807807
    0x218212112100b0706090b01091107200a12030e01080c090d150e0d17010509010e0406060e010b070b010b090a12050c18040209060111030904021e0706020309070e04030c02011202 78
    0x5014a030305c24000011440c48030b1074480c5040005912070070203246482d546000307101d281d400f142e5809034044250307402165149280f403c02106c9684443d0049420407011a03005d50328800c0d840c110380291aa8080300310013100440e03241804941080ca0b4810511030380303010342030007105494050f1140820111090a070310f00035003101c48115150310325600c4801803c40d4940c00890700030304100b010301122100c3d8145000308040907010b00c541c071441d06180d000075050041e80da100c84098a03007983c001c1042d580d0b039a00891607070400c6c213068501d114204000034071100880200c6805140c06441c140c8003626084100e60000c0a12405642c1406610410080c6030303158941c4150308900c83c101c9542c2d034180342c010b0107a901d10040c016810320800c3d0068840d52003001007590004842107030090390f0740104101d030003084004034041403544100031940e941004442d40146d03210388420740480d1004c035610b004c50040740c001654003501150702c042c1110b01651180a0070205c0010801015141c04025a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 349810287 1250 349809037 349809059
    0xa050105070801180b01051603120c0e0f0a12020d05030c120d0614090103150902092502070e01030206030a0e03070c290d021821211210 60
    0x659000008682c0c40040c004600300e02d900fa00c1c04010044100050340305440043e00b544103400001038880003441d40d000406208c0c607400003011103543c0c0701307010454122001506518564640d90b108040200000c0c103107082001d0881c044490412900382084078603000d01ca503002c081442507170680400c002c03200f9110f208109066007400e14101142e039815078008110200c0b800d031f030416950440780b00a880e1080d55104040f0781501d801000001c00c14a80244c03050040040403c0250001141c10400c030b00c010181c01c11082100c080c074940e00802094810490f12040c240c0114100500141d0052001d814800301560b8842d0000c5000900000c0d25000310f4550341090a00b2a540810250140305114002030880c81c403042e00840880b582400b0031907102c0c0380c00b6500b914a04a5404503200c002d400400c43e001210383d00c041d04481040c0c501721202d65081800e014504168450b0000b24442120703600020345484804035915410550000300141407028040d140f8080b07549488408590043d0350 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 349811537 1250 349810287 349810291
    0x2070c0e06031c0c02030c09040809011d0307030c0911030621011d0a021305310204150e06090c220806010609081002041a0f0708070605090f0f0d030e0a050105 70
    0x1e078403107500c018007905c1010310b4200881c10841c000c8a4501c1804002403160041e1000c0d90024245800100c4485444080c40402c2c1c049181c0d16101d01000001408140e0841c00e080e2103642c0c80500408042c540c0c0300e40c1301d20090f6013050708074415047c1c1000781d0040c42807543c0850319880000c12008506891611040501c01d940b1002d60070104c02481185410440e0701c00c40c4d00500c400740200d10701420ba4101e02507089008125142000400c1d120340015420040c0c05190300400801103201242c00c0b403443c6140314001d640071000f100300032a205246c14947d981c401c00321901e8403850040c0e000f420050300e40401c0c585c08003400e0180d0b07010991200c2132040a003c1d00e115640c0d5414203203080c00c03c0e8a007034100d1461088080c41048140720550500c0a0b111001600d131945c50340d100d440c114041541c1c412074502a060340008101c0a081042541110f40207410700002c03109408030041c0500e44604129482c011a9881008902901402508038441f100900d60a441010750300da26010f00351581 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 349812787 1250 349811537 349811593
    0xd170708090111060f06011211030901020306010908010506061605011b02010c030606090e070c14010f061403191103010b0d1a07020f06151c05060a050a02070c0e0603 73
    0x4003041000032035074404506040d51030f041c4000c0c080c0703041007004020203480152100c0c0c10440300f9280e24100c00b440d83c118041211904840e10b40da2300d080564075000350030a4854030f0000f0300360880041c280005005081c01410020012464041c41c480148988614600121b40954a500c400c40b00481040d0708100c5d0600e5540020400c5c8500950040454600e074114000b80b04003603105000c0c8040c1c071201694400c070300f41000f80c00004941024548100541c1480c141036007400215203c0c4101500300d40708403203070091030890601644d0109512981120812071280f070b558440b20020030048000401e81d1600070f0700002e8060000d4002c0b030f5a0a14620741542c051101c9401c0600003030b01c0c01a69540f00090344080c1030a07502188415440b54030140c00001da00c90b90054101040c2d54803a140304042802e2607203c485510a49421912244212001c01c0514600000506040c40600890b90b900364000c40c1030b451141410044481120080d1840350113106040d1400e03800c101202c0b1342803074140c0e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 349814037 1250 349812787 349812803
    0x30201090b09010e07031106190e093702040f0b041e121202010b060c10110408120c100612060507141219060f14040c05090d1707 57
    0x80c90381001100000050400c01e41603140c010720702c102000220703081c0c0036030f07a1050394a01c42100c07100024005020f4603110f0501035407040d101022050300201326070300004c42a141c0030840e6075180c2a009481854020310380c152081e4082031101a0b16120301401e8000700840014202074550200321004130a5800030001608002014400c810045034056650840c03021f2108045082409803001090b1100009191615401c803001006000b900244207824014041a8842d51116405551003844488481c5440d00e822003001040c02c0e0202114280c544207801007980e07038103141c603100196000c280703415580e00454042002d00040ca000703050042007240d220500340405410070b1011118094040004d0045110014011076494000d82c0c1d545850106110281c1d680c60481e0402441e452603405007040c070b00440842c1d60451a03401c5015180e07103c0402c16840240c50a200c1103030342015a51000c141d0a0100c0d9043e440c1038280070b840c4078401c00707861018542442441603240c2040c1c0086800c41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 349815287 1250 349814037 349814051
    0x2190f080705060a090506030406110304080318070b09010c03030605060a05041d0712090609061508070f0b1b120715050c190e180f01050f0d030813020a030b04030201 73
    0xc1410000300340900002c44101e454006840c2c0042c161700581d104050246101100150502819034401440b1010300c90703055580380303000d25103c0c54030f60048400901c5140e041c61001012800003c840b000d68504100440c9000354071001502c03462180d060440030543c8410300030400d1380740c02d000b8040c07224694480300d07101c5080c20215403071916117410700301e255008041001441c85c0d020b111100c014101020004070380405d400d03c00301501099402070b16440c100011101017503505001c88088441c1141625002c0b5103c82060f01401d45c24030851040100920016403e07035003001c580031046210f441100c2803491030180c00f80c6250481d18042c0c50142c00441003042145807806a00d6014420100042c944102541860202c0c1d4000500004002591803603204a4903241040c0c0d00401c091500f8002614107050000420780007406018007071541e413402503902c0c0c10700c110389411781c9906454100701956081290742002d0000d0405a034807100019002010400186155019900a50001c9200307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 349816537 1250 349815287 349815299
    0x2150705011e1415010309030512040b09010608010204030b0c03070e150a0806011b150b28060314011a0d0203090606090c130b09040213060c03020105220f02190f 71
    0x4521007550240c1c0c0943c030b6402c0081c80000c42551902c906803d003000182030f01d0b6400d040f1007901817115035040f24511030b0709210900c440701c600c1a20414841000703102d40b0b5103a2240c0703803e0307000c4e40c44000c0101d110400485c00030f50703101c40a10340c402903038034190003c65414070020b420300c0c203070100d450701c0b04000080118146074400e461640c490820b01340300c0141e4441208154840500c20005026801caa140d44072404550342c004456100e001821041c1915070465407460b40854228248192078106000282d0f10303000c0d0003560340d030362401304416010b613281000d003007500e0480a020740c1c55800d0401100d01107004d144040c4d0300841242005280700d01c3c6c4003003400f480c0d103405480345880c044107002451009112900210907104218201501c41d40e100010802900542d5501c817810000c0d580d0114032035902c16404800382e4060b9001b0f2009803500b9403080c001c070440c071441102080d04010400041201056034440c8a84081c050700c480c030081a1040e010459241c01c621411402e01c1c0b82040b031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 349817787 1250 349816537 349816541
    0x40506071d010815040c030e1b011e02011e06080c010c082704060e06030601090203040f03140c0a050705180c04060c1502040315230402150705011e 65
    0x403000c003038103000d00703045100c2110310044605038400c01d040003024000100f41d0071850451014040300908148071001c0d807110058060031421000180501c00c0058208030310a0b104100d681074641a1280d00544035680d00045443c0d070651090015592207104c0262405508182c2d0844035204460020f401c509061216050451408400741000b46001c24400403a0604044544030495040741d5102e000e80480049110104004000da00600c1c000001500c4000d60b0380e9140b02d40002c038155038080ea200c0e00104100c1c0030a1340c010b0804104006000002070007514035280d00c030700700030859040801b580a190325000c41303880c0c201c40719084010104028240301040490110406200341c0f00d92038065842e41c40e83c001c0748203006c01c1180d211540402d2003100941c441542164141c2036640303d440e410b040c0c40060740d200f103440d00e0500c0c0281c00c020200360b01d15444101e016010748561a51100c0d001c000e0361840002180342d0031001001103900060091240540d0700000e031691100101d448940001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 349819037 1250 349817787 349817791
    0x1d070915080c0918010902030307050d0807050315090705040e191107020d021018080c031618050c250501111213170a03050907080d020703080906130b03040506 70
    0x9610408002525a840502090b0700013040e6400814512490803018050525100e0194150000240140a1050200b0b048450400c02d0b11544941d4407204001c64045c4402c0f038040040705032b00001c000c4240390407036116811000c50b180141c11300351101ca0341c4c1030300d05064801c00c1e5513100400c144512040031f4000c4070810064075042c182004130b21b4021400455022100070f20560003003048000f0340380503235001002104a840525882519020503a0750744080300000b5219101d0036005011044500c2c8001c400d660041e4045900c00807007510708400b4100140c890980d0350024402d07140184514030364a1084030034020400a01c0006041c040c2c00c440070000b00700c0324400200b00b1103035500709066449030400200c4441e20000d50f62420003410b808490502c1e50860754001410240c80c0380c2c1500014003410a0f03405a5181555405c0f1481e9901c00100c078940140c0c0120400f0070220381140701914419401404140c42c02c182c031100d41640d02465003103185000404401d01042c001d041042c03a07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 349820143 1106 349819037 349819049
    0x60d02030c2b0e0c011e0c0819180305120c03070507120b1f0603150510081b0f07020405070201021b07061403010b0d1d070915 56
    0x3051810350b40e060703041050401c07a658544600c08181d02c42d00c064143c45500c0078246010400031030080b003802405c1400705501c0340c60045003492004001c246540f03c0140081c200210f005000031048607030b46005d001498070184001b88000030380194003c9226020ae84076002d00e408145180b20f081c0c40144140a01140040c90000030316035801d6042c0306190340120760751009500425021309641050801584810420030a8001c0e0301c0000d101c2c03041c0003041e01e010b8440c0c0105452046000c0c2840c0095600400c10000031507404051000c1105548810715080c1403107501c40081c0a0424040d10560752103006c10003640c004d504961010740010711240011035160400350300c0b13200d2840b51202148802085444030049201140e050f00d41240e116420a01206c014400800c10441d05040d8001020a0088400401c00080d401414129004549600c1d8400da244006065038419 = true := by decide +kernel

theorem cover : BRFrame.Cov 349640287 349820143 := by
  have h0 := BRFrame.cov_init 349640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 349640287 ≤ n) (h2 : n < 349820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
