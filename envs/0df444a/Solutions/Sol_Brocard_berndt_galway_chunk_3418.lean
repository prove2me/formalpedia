-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3418
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:33.222669+00:00
-- url     : https://prove2.me/submissions/e91c4b0b-3397-45be-a843-a5c03fdb160f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 614568345 ≤ n < 614748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 614569595 1250 614568345 614568359
    0x1603021e0a02030610241407081b0c0607060f0b0d05070914070906111005070e190302060a050d110d0e0d090b0d0b0a1701091a09060609090c040609060f 67
    0x2d200300da0032400703160185aa40e03980c07002140c50a032150414041a40c0d40c5001f28800a00107140701446501120788982020481c000196100c1c2c803003404507401001c01c01e186a0301e6000707860400340d00c00004111881646200350282a80d6403003d500070340b030149808208440402d50358141e642c54002008140080008104000010340b404c20100700400b005000769803051580c0b07501e20b10308a00711084684041031039001c03507804840303c1d40000d2140703d40c0750b41c03840c1805840100210800c0103d4209007540c0001c0c00c03a1107003d8035239003030140018945a140c40305400c4842983e640410690319081c0180f07288024200742042e00c0c07010302424281c52003190007062034000b0780700301d03111080c00c183c0c005038203100030803201803000d40c410211640003480e840891a40b150b141040030007c0f0f200010380c42c0c901031402340b440c00b403080705000404110840000240160348403008440c480001d448030003046003046507202c80c1c1a0401c1c1001004100e40582d500070404580401490a000d19640c102c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 614570845 1250 614569595 614569621
    0x1b031e0403030e151309020a0311120a090c09020a0c0618050a0215040504051302011e0804060b0a15020d08090c15090a120c09150b1603021e0a020306 66
    0x4018082565445403c4180c14982260409890010481403034092020050040d0360a070360f000c460b0707040d000140c00600650500403066101c4512592a060071018202e040c661a001455100590766a1004400703019040b40c00100030011181c045541d0310018100600d41046940e00359090740c18a005d112140407450505190306030070001400d01403410b50308000220070091400c00d8003c4083c031004c2256900d034400c490052030312031a46902003e03188005040380c5400107002c0e013a040244a44100d864200107040d074010303400b00300042c40901e00c00000d491055070303400c03002c031400b50107507002c06103a00001c05484a401e035494100c80c5648540c01c566440c240d05001540122803000302051800c0201c0150440d442c008100315142900c0c0c080301104940400010385803041c9400c01000401e2892181c00307a840040464a8100c509250025406129130400c20402c00c0300f600208c1c090602c207000030070828480200d4150058071410099580308807010099109020349000300b64004050a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 614572095 1250 614570845 614570849
    0x270103110f010c021504260d032705030403080d1508060c0702190e0f0a0b2704030c02040e0304261c180b030f0a0606020303060d0204021b031e04 64
    0x195402c20b038420564284146090010300c4c5c0d8210007001c0c0004100f51001c8480380003844855085101c0c08186c1d0001280f60994140c84201070600d41840342c8114180e91003d640398100412082e0880380b1146040351442c81a40c2c00602003000204030307031441180d80e8218207000c404519000e0001d40d00e0304023098840a007641d84080c1c0c25001c000740401400c00070719103d0440801c0f1070a201969551040c103807291002c550783c00c9000002000c0003143c0000f031040b402c80300c0c0c041c1d5904420040424501e422022031600200c1c5031039440c000201018480c04608034866400703041445100c00c081803481d6250800c3c0280c20750ba082d0b5440c802c502420302d0195848030f146180040c0b40100d2031044401c245104001c0302001c0043e0031030b14410326100340324448001c5c002d0403180e55a900d0201c041e03005896000d800da40702d00b030612004201060303000054a4000408a44a001050f2a4070009009218400c50b440180c026002400c1071118080701400003d02c6119032041480002c0080e150103110314 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 614573345 1250 614572095 614572097
    0xb1b0c0108061309150c0e0a0e07080105210a03200102070f080705031908070905120604060203070c05010e060906060a03240207150903090609030c14270103110f01 72
    0x652540c02c031500f0150418131880c0e001d400c5ca07030142148100c07144103071000810084e0106008400c03003015801d0000204000340030391031401c440e03030074100c0008007003881c10b00c02c00d8407800300f100f41e088447c950061580c0000711030004460000c542d42c0360150002c1d0784500f40368408140c198050664890600849131446c1d804460150809203503503c0207001c5e0000359060307445200521546180040201c0945e0702c0c48015220518603160003040101201c405400640c0601c4158034074120f103807400501640c00c580e10680242e225580c446080780d245028500190556003010324891142d040403500f14000c1a0100c10b40e00f49640d1941400000a002d200060040d02035050105130519a80c14944207084809005031500240341c03940c0c41518607520015028a0366552070600301600300784104000c15203814002080c2c0e1a47c1c0322484600ba080c81416072000d07068200c421240d4071004441058514141010030025141001e0781d6850b60901080320540c6010703031040503514000c05480701e400d0701 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 614574595 1250 614573345 614573359
    0xd02070e0a0207050f062e0e040f11150d050601020102031009090303090212031317280209090313090b09160309050717010b040912080c040b1b0c010806 67
    0x16003803000000350f100070002e68550060500419a1240501030705004458240711005a0041060907000004c000c000c00155a03d010380200243d054640c02c0c95440340e0064020224403004d418080c03014140101c1c3c0650088c4083c44840c0d0300440390019129000f0401d0040201d03560b18001a403c070300c010744860701e1100880c41c0800c207003500d40d044103c1e50392027441c020401d1615a40400c800d10341054005134560004509102c12241a41c40240142182d01c0281c4894a040f07403403030785401c466258201d1011007030004c1500640c3e20071400001c240d000d041c0000e00d00c0c2ca10809501c0750480c40050104c5005c4a600280e40304590103927202c40e610040195103580c0320030044107000204080d503c03080c191a1903c03200031980500001004000500000494407401040c82d8211244d402c120ba02c52880c0003250070100d01507100194120105003003c1000e07480e8ad0440d0030850080c2d0303009280c61000020600c02e40640c01c170041c0c00c195040d608559403480880300548a00388110f031a0360700542 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 614575845 1250 614574595 614574601
    0x50a06270516020a021003110301030602040806100623160620040e0c0a030b21010c050f071112060103050d0906020307170f040807230a061e030f090f03020d02070e 72
    0x10b0480c1b07409000b12018100040c121561400e2860260001d9100342d84080d400704041007083c01c00d0110946c031203d000c0140d120a41042c0c00076013141c030380000100d00270300d844103120300311024001102d06050341c04900c0305d4000164a1300c48041c0c80701550402903070303194101485c17a61000c0c906070b03019211412000012603580c0740703044807942c110380d418904058441281c2d410300c0c0c44441c40c4114204010320380354004904150420f003520801e03124401040820091540c3c07100215040d20800b560040405043c0604140058060f10184046c203a080c0a010000401c1280020ba01c0c0580c800c00e0312451040380c0d40b6802640c40f40230342d0f48080c1002a000100f000409402c00c001c084078205811000d0070f2903110229a41b07001c0b80b5030802d400035076035003101841d12400c1840d10a8000c0c1e040390300244950401b02c0080509540007010f501080800c10401c007c00e000b60040351284410310000c1094890030f080100190110328015009409504000150984041020019501c44026800e0151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 614577095 1250 614575845 614575849
    0x30c120b0609040f0f030f180302180a021b03090915030607030b190906050306060409030c080901030207120f1404080706080408041706090111070c0306050a06270516020a02 76
    0x1030b070040c8111030319405002c0780d60001d0904c5514150b41d900a6483c1c100d448691100504003040901000b401d841c0050303810001a40d407840d80400b0010311201403000758456545401c040c0c0214907a801407540b4004040d1044000003001d4046004101c4501300107441d46e201103004140c00e1113039603800d60020303c005001103003c0c2d00f000c960464050511026181030449500c2c0c00c208070b4011084441c2c540c0420031503444c04000440d040311048a040240070f4142e40c1c041c0c0391240040005005030070100d0000581d0f8040e03815a203484e03401030304c13160055010000081590b00031a00c03ca0228200585010301c0754100402d580079691214002d0900304d003009001c2d034000d040100220b800840810011480b0301800c04403080150101c0002c1c003240c02d00c010540c2c203403040d41403030011840040c031000f004220401e41c00d03c12290400400204ca469581940c1d01809890b00402503030b001c0c0104052422504164290101c1004030003080300b916400d40790312a240d01c0c41a4100140d215540090140c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 614578345 1250 614577095 614577109
    0x30c0c0c0319050106080312270109060c17060609040b042a0818070501030b030c0d0b07121e0c020f0f0c0a06021c180519030c120b06 59
    0x10048040440c0d03800c06108001a01d400c40e454440d45802031055444410080c00f406484080d0803100c1c00f0310709100c4411300c1070600c1c1c08024152407813151860111510040b407070035054040746041000340090801810010040e00c420005040040d0700b0301d07a462003490a44e841a8000c0200030800b03850411b40c84200006030000e00c010743c0d48a50396110f581040e68a03d11055141034034003d0315803602040100140c0702420007000101e030303c0f0301000001d0030a00040341c1e400903102c007400e001940c2080d90b07000c0380c500f002e04051180c015002808410a026503541c0c0c00c2d11032011544c80f0703100d0740d03c108100001c1e074050f003017100084404019040480d600c0d9400c07120520000740704407a0384c04407240c01949000c2c2e0b003c100004c2c40d04003035001001c0303080404194024000c140000d10a500e600d410060300b0310345100ea8041084000c00c44650f20700980284c200090000504410f80640072140d058924085d0303220803290701c0902803001914400d895140c808042e0482d200340465540d140c180041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 614579595 1250 614578345 614578357
    0x303020a110a1a0603070f080f2e150b0a031a0f03060c070f121110020c190203031908100f21170706020306010e0f0a0915090204120314040b030c 64
    0x4503001d1b207800800c1d0082c01c044040020950240104035881c40750613542d060803403040c08582c03120740304484807041c0e00e03031007078440006992107000048010350100456084215a0005141c034000010603001e01645a00054a814148098030014000d40c1c0c0070010b4806c00c1c556a560941c2060b8000784014102d040a45180c500a401c2c44101d0045a500c504081c490603100b40d010440306d40315003028400800545450306100d40d400c514102100da806a541c00303981c042c2d03017081d22440a25204540381813055940e0b4901001082012600b9144007411500d4200c1d2030952440940f00c0010720700003241c001104590849071316034641d02590b45811040c0055500076201c0090ba2400c0941d0304151000403d01c0c180189001601ca050040004002a210207180307442906812624400340e911400c0460841d407110800081c0001500d00346801090b1503800800c0c081d1001c940050801103a641426101c2d20a03550442000c2c1075289030311290007180940c1d00d80c0c1005200141081c10440010f1107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 614580845 1250 614579595 614579599
    0x6130e0705060408151308070803041b09092f0907170c030a0e0a0b010b0703030902030106080708060c040b0418020c2d061303030209010c0b01030303020a110a1a06 72
    0x585070712100882c1c00781c2d00070b81c02003c0907800a241d12088400c2241199046107040c1e0250076206002c1d1280803d60082c0d00d405800c07008000040390400c030009042c9100811384849040d034140da07c12615000b03055904040e030300a03003042052003028206d1611801d034664140300440482062000344010000010300d0340c4144503005002000c0405da460940344100d0b265100b140d40da140c00c5903c00140c800c079180b500d18541c4000c4525001401050b00c0b40d041d02c5d210060107031941c0b90f50074102c003d0001070704e020390954a003c0020a20000c0412844203842e0a0030891b0845d840e0071021403a80e128500c00c00900280a11051100c800b154056001c000d61011b009814003043d86941410120745560140410b1000c000881943c000780590340f4840c03950720090203c0c0d241154210030100c0340c0c0c100007003c00d54001503404a681c051008404040e4010041009943c1c40c0d20303004d4020742c00481d4241c04140c8509802d000060002001880c003079001e88500040d00382d9503003031800c900c0081c06c0c241d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 614582095 1250 614580845 614580853
    0x20090903190e180606070606030b180102071a0703020f03010308031b0c1c110f0109120905010e04090c08071203021516081b13090e06010f0e040f080703020309041406130e 75
    0x1007c40c030741780903040c00745000b03400c40c111500301804402c50200840082c00d400e6401403040030042004900c960074109a14581c003484e03951584d40c01c070f00900c5503200001302c40c0c6000c8008000d100d6a003018611903041c080b800511022031011100075400b2700c2c0d0031000e1542c001581e007000399003c0c02502081600b02d0600c040400c48410540d4108814140c5400c0a80e540e55155001d02c11400ca000d6101656424508001b0341010002080885c50444440c025074032001c0c0e600c20404441640c500500e4004255100e041e1600c10507410003007018000d40040c81108101c07000d2144c841003003030080d400f9100703480c028201440181c4540100a14070701d21100303a60b512200004000c0010002c000c80c80044844842c24044444200d031803400190a1941c40750005100c2910b12040502c1a10241c10035000d0340e942c0c1d403410032070700c001800300102540c0d80407034600f040580000241020110071203050215403040c22742142d40280c21038016511290707210741d1181031551507000680c0e411821043e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 614583345 1250 614582095 614582107
    0xf0303110c0d1a0c03190e07030b0112030e04022a070305010c2d020a02061c02120405012307030209010c02190e0114030a20090903190e180606 63
    0x580036184420b41a81d070000d451000e80f41c1c2504000402d68030903600700407181181404041c40c4102c0c00c1e4540c140b00540d030784421811150740b040000d10029a44409a801c131580c480011709254003840e90200e012400254541c0c105203864000d4512075485046581d040d070703e100c8044240340b850b4111303c0080d80201c007004008203074203010354111112217484400341d6080c06070150402c05490540e5135615010f801c00745810580c0030a28104040e01111030b01e440e00c00068001421445032000528018800101c007049074441c83d290522690040000700007941d40d0002060030446980700cad1020845001d00051401342c06540035200c0400e041c900245642911350100e0310880030844c08801000883d40c00300500f0138412001c80c09481800002035070001c045c000b0a0356075210540017410100007a0002e94964602408007103c9240101010070500b0180ca2550b100d900c10700b0100c22085601004000590103240180d1282002800c6035224154903c101821142c0261505601003020444 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 614584595 1250 614583345 614583349
    0x609041e0e1605030d08060a0e0907050f0904030f27030602030603013c020d090c0603110a0c02060f160c0e06090c0706110c07080a110108010f0303110c 67
    0x1125240d48944034000030100c0707000846510708081d140b4042c9050084001c180559100801c413070079900c185090920940d110280010018050b40d04070864407220740c01041a00e02000403070034110381007035034482c0300302c000e84c41405182ca80403070300580400c1c0e40070b070050107840c81004203001000344620f004901841c00113840140c418079510645000b60084140481850300303124504402c000b04807240e02d0600131030552080f10542860035645581c4030b05985032580416011501c091500c9a810060411140b41045030140640100f50019280585800351451403008403541c1010396143d0070f0344003155a0800c901c43d404003a2540e1440c8061120170349140d041d81803080940c1c89103803464000340c28400d4400f0145001425140305240d45c805001c000d0384500204c17003200f07030041800310321a008036000c1240b42c80b801d00403510900c0703135140002c0e0040000c07072040c411600c1624070140100700300f001152030b80401e01808039841c4248400300f001074050085a44095460341c1134601501c22500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 614585845 1250 614584595 614584631
    0x2190606080a1a01050d1e020a030209090f0106060302090a1701110f030115020105061302130b03010906060e04060f05010c030201140a020a17041110020a020303190f0207080c060904 80
    0x4001c569140140c0108004071000f100c0f241c2c0900029115915203001790b480d02c201000f50751044072440d8014031401002e540318000d00b50061600500700c0217590500c52699a643c888041c41c0e420303594600000460400d1217802100d5a00300c0c024040c01c8403508002c0c1e410080d43c0d0002100c4070640d6030b0403007030400143c10030151a0100d15041903540341d40c50700e0701900c0c00030f07060710b0402c0869240c6003c10145940c0c001c20701040d5194040010b0b140c4003246060001d440d03054101c4004080c000c0000070380c800240d0020002d40d070352561120004059007041c841512694000d125030605000f10500c0305510440990814034081c2c030011034035500301200554104030585041000940003c1d440300b02a0300404c11455200c090400d0040382d203026100d01b400c2c201c4d41d0301c8052060782401c00040c01f8074420800c8400841e0010292684c1d190322581d10110540d0ba0628000462000404024950300102ea10411142c449001d00a070a44480401c05c00c5d600c8419005e6110b0f0383d914000796081d180c07203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 614587095 1250 614585845 614585863
    0x30201140f16020115260114010b0702030a14010203072c1504091107020a051012050c07061113080f0303190e0109030c0501061e0504020711100e010f030207030219060608 75
    0x245d040c15400c1c070031125081d030315940e411b8100303d80e81011000f030344256900d1001c90440c0c1c010220280c03906040e01c002400c00803030f440050b015440100c0401c060001c10742c01940688001d07102c9010000710100d5120030b030020340710f180e00001a501c2110b22303d4289500005004111205014509600c418161b400c03902d011000300fa80301c5000c9000000c43c2415002c882c00f401c4112031001d00c594040400030b00c11464800c1420182d6100c0300030a6000740544182c481099001d801806011080e4901c02c46d1604078025241c154104080006103003000440c0d600e0b080a080c2c8086e40ca1660364040e10202c84c11641c0da6811403507919455002c00880a02c03620036254841d0b1f4600c18840d915060603400c0d0344480d04420568240018800e003804e10613420304045070425078025860722141d0130403814407285404281d1300034000303061205442e503000420044202003629500341c138100e507010480c00c0b4064440c0050240e403050340c031020703842c0402e02c250040a02c0382001254060f243c01a55041c40e06803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 614588345 1250 614587095 614587109
    0x2040c09031403030106020d080906190f09150501050405060d0605280911011b030c020a0b070c0320010c1b0503010e0c042a05030714030c07030201140f16020115 71
    0x13000600a0325030500c01a82c0008240c40c041041d4100450006c0d1949400b40c80011000301b8050301c03c55082c4182c00c0806181d006200811444642e03040c4910401e40da800d80c0f00f4002d29010020980c1c4c80c203031003414080d60024080d5540c60403103541c3c1760014500600500c0032800000070820b003541d00c842401c1000155004081a990071506d041303c044400c2030001ea040c040c01d0414842104081148408450340610b8918144038090011801a01840d0040711041d04000b41c000c1c280f0020b00c480b41c04403441901d084104d03a00c164001c4625030100520140010598103584000c20748510100c4440400004444c0b407a1783d03283d002a0858191805986150304010142541844c1520804011546240f242c41c0c0c0040400d0305005031550306004c001c18000003101240c070040c840c045240c002045038820507507030700b404c50403150b00d43c1000c241100150300b001220f488040c0250050b500494858030113104540710f02d003003410071350b41140c2d0302c0003190b5031560010164844a18010014554 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 614589595 1250 614588345 614588347
    0xd060f050702060408030c180d03020a03120b010e210f07081203060604060f120e1b1f030c031103040f020906060304211103131e08030702040c09031403 67
    0x5549190416544020314507070a54001d03908002c0841c081d0340840350321031440114141c0e1480078110380c5088889640d40207401c1385083e0500c0042580004440740c08074082d41f01c1c0c0384040110761444040d40c8440c18980d0010b1b0400d4004069404d0100031b58000a40309400a1580e0402182c0185094290501c014096014810410000509211900c400121a0700b81440e52a01501054144c801e41c4940b404002c0e10300c80700f80708a80720714503500b01d441c8022814404c00d18220b61030781d9078078465144542e00c0342c405030a4007841e1401050480d03000c1202d1034075852070100ca407026801054000881002d03d80c895903c1e08414551000542c0b20320f225003071740d001c480c20368010301c0060100204950300410781001884042110100510515110080056196010140f0403105000c1d840028030091201080c80c8100351070500164064502428030001900c0d58080700c0044406148202d40311600f08100c50005418207400c107501501c200d061640c0e60f0340e5aa521000c040004514078449030704 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 614590845 1250 614589595 614589611
    0x309170c040f0207062d0209090606030403030605030a03030c021615030b010504120c080606090423070e01030809090a020f0d050c07050703080c06160815041514033d06050d06 77
    0x151707020001809081c1100301f181411414000700d54407004c003a04051251710080f0014041500c41c0d0000c20141c8400b9095405044481c58054080c0902c011828054050b10400240051410890000710b031140b4900d000304180c1514190020301d02d01a0060404c8010080810307039038004070301c40044a12903503448002034030b084189428040b002d4403482c441e91400c800d10000c52850618904035a1a0484501880d1280c102d11440c0411580c02180510b0700c0100001c10300c0030720340c05081101c2d015a2403034042d0340c0310f04c540000c910a00c0d5400e40c41c2c0d1000d220036105441940c0c002c40c1c1c0102941c0b0b2040c603041d110744640785800410b500403201000000f07a03524290700f0034000d40303401002d1244035000c0ca82c1c44031806010b6001c0144200d400b0301c02d0b50701c50300d001c0e5101d410070b0800f031801130303500c0788503d480c1c040043ca0b000c482c03c2079500911502d140401400c0700313031810b0142c0159241d5800710403602c0c803403508001c8802500f021900e98507101c002c4b50b40d43d40c1010820946100c1d000000f0092 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 614592095 1250 614590845 614590901
    0x91201061e081203040201091a09040f050105031b090718030512042c0a05040807020d0303060f050916032315040f05090a17160c030309170c040f020706 67
    0xd100f00012410100c1072042c400141d0300000080c003903c444080344d2205503020130a1a82c603004400199078400d00700040b000c0e100d24640c0c0a079050340c506909445882c0302091700c418542088a81540d0070803603000008010600c601d00c0700710300c51850b05050700c1d00c60780c80c1c603018546985503400c0c4e11500b400243c2000500501c0d050681c500ca84140b04104082c1080310403c14090b006286d010f846031102d00280400c4890300c101d802503580201190302c0c2080352b04005009042d14002c40314062079080c0003040501d1310190580c0324500324007114000c0c0141c400c1c1107024101000e48500401c03080c00030a44c42c1400c02c01094030818094482442031600507081009460045128000151509051007082c1c10007007440c070000c58215601006400c081d030541556441050926401c1d480101515010003001034400d004403030296444060183e12000203025401560080070300a031b00130700c8804101c0c141904000c20580d1280001801c0c07000b0350b2207510a981c0c0c142c1c04074001c0e00007013032112010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 614593345 1250 614592095 614592103
    0x803030108030322110103020d020403080c072d15110a12080c0906091e06070c090b0a0f0e04231006090608030d09020f06041d07020111091201061e08 66
    0xc0e1061040b410040005464880d102110601e101b810035030001445c6141c1aa15011500110740c421422940c0351140b65a035070b2200750900410034030a066032140c601d820b056100b01801e420820440001c030380e1805a11040e11219040c029003800f18503030700c4c2440311005020508459020380112280000100c40051151000500c0740d03100c5201404002000e89824058030901c80c400d80d050603121401d441810703010b22903c0541036001000040980812a844a210302182c045250505c09146a0300810100c003a180c059150941061102005507801d129a525001801040e002c05900194001c08040c5038100c940d21400358094800d05045141e10311030a0010a102142040f906040c00b50a40d2a481600a002c440944686080081d552000c000318504540201002c1d07541e40d0719407040b0841003035141111681c054980c0054005401805201c645407900031100f880c001c0b11004010107054002400c103e199a160710100f4980020300305021071100c605500d80c0b48502d8030a008d454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 614594595 1250 614593345 614593381
    0x910060305010f12080a020c040c03140f15100302090303070308010810091205090604080114190203090a0201080a020d06030b0910150512210910020105041106031008030301080303 79
    0x50721401100c100b00c60340d82e030303150f0083c4c6580c08171030036550f0844858124900450643d16940c403514000b4072440c2d041e05540100811498003845006aa64200d008400301c482210081040080040c00700c800d0700d02051892810242420300505260740040071a00d03581080d80c0c02c401082001c001804841070800110343c0d0004003103400d20000405e030b550841400d255174546418003201054060050b5200720564015141c018000c201100e0707100c500c8440840240c0301d08810b1404031001c80d03c0d12202e0300849102c1d1f2104002019804e20075401101c107400c2c020042601c2d160f0030b2054645402c0540195801180248190784990400304d9040c2e08010a052100b080e4074a82400b0010316002038401c03c00b00d820440d075600b100c20310f241905062a103290303111b445000304030030030030b2030b02e0014000380c44491002e84503030f0305480803900c0c141e0881c0c605850140c10040d280015084500c0c1100003154050204080070410642c0c9084d4207285030003c0c0c10020b0283c10110411941108030500c40b41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 614595845 1250 614594595 614594609
    0x603030313111206090102030a0b0a121e0209041115180d050109080c0a030201140603100b03031308060f160503160e13020c0d030c2c091006030501 65
    0x200e1410004151280907903030742002058010300c001c0c10b103515035508202034010001c1c03406550051914400140c000e5008840e8054194a446100a41c40c10084455426074041707149422a44d481d030b0302c40821340e0042d4051018885581c459110041c0c60b40d168543c002c51090360300c00301d0344180d0001c104541140640384068a001400714a12007408100c8000d5041d0003500d0407040300c0580e04041e80500302c1110090450703a8000340d13010240c0000601e2071103050099000f000b5003200d0790303a0500154000d80f00d469140d40422050403000d546603102d0038032624014201d07450014044c2400784880c03451340c40381c4500d81050003017108000710780c003003a6406406001a1a510f1a440c0b0b805003d50002400d1041035810184212040c54010740b40100c078035100620110840c3c407140003241c06580403500c4001c81d030003801001043c95019014507680110b40b511a544c400c50001d02d007041c2082000c6600d645000123160101c0d03103031100450180500c6688400640d100d05212010b8191801a80400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 614597095 1250 614595845 614595847
    0xe01090209061509011b050102030f0f01050a0303080c0309010b031b130e07030f0c051c03030f0b01021902011205040f12050a0503060d031707051c05161103040f0807050405060303 79
    0x3035401e030b500040300d0a607202401c0ca01c010346c060510000c1c2804d0b04c110000e08942c400001c0c0400c0d0b8028100c1c40e40300b5404140070113a01d80c0c9075018095203000a110040201d40440c010031010380c041c201542d402101100005900703140c2400180c509412420000c0d808009016042c83c5800d14400e1080407400e064030a101840328800802c0d65090144400b4000c036101000718002c20411030000c0c4000d04004001841c0c1d40111340b00d080d9a4035220104402092914075000c0c942d03801402286030144058015003011032041001c00c01c008194081281003080c0e60f200c0803202d90682c81402d01403070080108903000b00240c5807030007079013202d42081014480c00740311a06115510808490b0302210548030241e42c0c01e002e103010f5400000d00e0702203c000f10390b0f03141005142d6502401a001c15001c4c40160060a15103040d940c0464605550b8444842c200c1140e803d20240281c810105c2c0780541421240b4003903035014034100003030b41a04111041c4d00007460402181c5848c0c06000d0b080441100a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 614598345 1250 614597095 614597119
    0x4060e01060f0b16020112060e01090e151504020d02120403031103041502090a081b03060109110d0504030e0d0807020f0a0605070f02040612050f19030c1407090e0109020906 76
    0xd04018001e444213036206013007807107180086910482e0644091884d10070203010603511400034080406007401340402c0c02d07280031080341c5070709800078180210764282205400c480e11244841c100c001e0110240c603030415020064420541c086100815010303100c10750480440c02c041c5801810786000441c50318050100b40148404078906165401e1440000e2a0060b6282400004240b00b41c0d05030380302d508140600703688628415081000a241407904809848031070ba25825a00121510300f0340c0511810828064402d0f8403120b58001a0810b0290418180142070b420024410220b114801c85445038041828000c60412001005803003a007100e46c140c1560400500030594040c0349005084180009002d0055486544c49540680880b000030007040003039040003540c6070054002260742e44900a04a0500c411100800c10047e60680e14411981c4440e1603200c52480e505007003580310302804034001848036042c464246444d510400220b81400700e4010403030800001028240544014152 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 614599595 1250 614598345 614598359
    0xe070e0f10360204030807030908010e19140d090e100e160c171206060f0316020c030304032001020f0d0f0203090a0f0f06020114040f03020a0b04060e01060f 69
    0x41032115250090382d51000c40500c5180d409a071081c10040510030710000c1c001c07050200010003000c1c5c06001e40c42d80d00d5102c3d954852982207401d0f11602d112142c011054041d0250402c140342c400040c082c015482d0b00c01c20340c5407001c1c28900080040404104042410024031003528102648400e205440103001440c0043da5a01c00030000c0078141e01c6c80c100e00c80076034031901440d242000c4030b8200680e5141c060103805101700c030380e001c401502c03143c0a104001400510b410000c0300e007540a82008542507403503245842030718200401c1111b00398041e0030241c8805481c02c0004e4001103000380c6803d01d04814614000b02010301001d03150307045412402c101540d05a00054207031081c64286003110a1440843c1e049040d03004050a66600c80d0004500141d4108110305241c15608000180c07880381d582e400042e0b08944903222041240c14188001a002c102c0390760756400c50a000f40107440d01d4880954840d46042412030301205c0695490081c203000d2402442010007505005400044c05801c01c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 614600845 1250 614599595 614599619
    0x1090201020a020112200306190308160f080d02120601030b03120c011104080102090102060702030a2c0d0506040519031d010507021009140a15030e010e070e0f10 71
    0x7001078103202c90f517000c3d01152462035100701c01e5002074610710310101c040e20b40b549a8503802a1007545c031136140c148001903140e103d04860030889622104407851300c0f22910446502e03200d0400b0540d0030002d0a04004c02103685400281a42c1040c8000142d850191448450703d000001c3c00490425140c010000201d13200044c1c905542c08003180802c0d00c8051a20100e4050141081c1f44408007601140000710000150040c100c921401d800b601d010b0381c0c485c0e40890f84d902402c282d200c00502c600c0103032022490b87c40d604c0d64044074103412489011100e10003050701034011030700c1240c45900400400c4103005040c842000f05074020045111200c1e8692402020743c051502c9240714140700c2c201c1c02c03610b030780203108481e0581e41c0030f00f9580c079000d458940030341180141d200b486680221560004541c0c0703030100c60b4406031004181c9280f0035043c001d00031401003002200a400c0b40d9a03c138400b003010381e81000041d000380401030b400102840c00001a1442d102c01030720a049c41200b0a80074000b200c6000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 614602095 1250 614600845 614600863
    0x510140d150b04062601021911010b04021b0f071d060f09010b0a08010503030712050d06180e0f01050708010e09070315270302030315150d0902120109020102 69
    0x8030301c00c003840041c4405103008000c140703a1982d01a20f00321000072080c0345194800d06125420304030207911440c0014a40c2170744148019000224100c0c80d8050f021801180c3e500c03901740070305c000012103102070f02c00b042c01c90b40004105946549001390219008404001d8860b8001c03504010b07181e882c4c5030a0780c2c510011074140340050f24854040015403142c2301d40180c0c85810341c00a10340c0040d969a200d005400d507021640c0500050713026000410b490400104403a03406600007003421003242d503d90f01f02c0f5a6001140a4255241ca81100280c3c00c9400c201a40c6045100c0100245d04036008149900d080409041000075034100410086d91300c0d04a0f1003c3e04484030300040014075510b10f4541420101240c200901d0088001c940b038503001c206a02001d400600ca01080d51180407101214034003000715000100164000c01c00a0558100c90ba030b80c0d8032046000c2d1540c0300284000c1200c0d003164001d5042050395681e60007690b015407500141d060f5129200c00000c1101402540000b52039000341 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 614603345 1250 614602095 614602103
    0x225081603061d1f0b100f0206011a0a030e0f0105280b091f03060c02030d0e3705010f020901020705010503040803011202152106182e03060510140d 65
    0x81656240342c05003540000c14503000092106c0110105900b02400c01c9440b91808170042c4178400c00803c550304050080c140740e8078045c0b102802c0c10414070303048003c0c1101510280d618041d4406840e10010309024503070003000030601d100e0070b80395100310990b0070018041c104224a030901183c0c1d003107910740f100340350782050418440c2407896140c3c4001c160b100300300350300080c55180b0b8540c500c9038143d400f001a05003a1a0800c00344902e0200c3c404469a403001c41c0c00081c143c03c070f0004110341e140e0b2900f0890307216803070750210020000d245440301804c40714000017074019140c0002d8611429030741030210b04040c00090a0140c194207054803094058001409480300d004000c10079401595100040c05030a000ac0c41d410b80e54403001e505d100007c00307200070f0307220805044400200320f81c0e141ca4100711085501c0010b800500d41c4c1c072801e02c80c1440b000c2154030f0510030300c02605403030b502c00045100c02c082d50080401246c85e003080d0041404a610f5a03101c1c041c0d21104a0003807000f81d0390041030710141500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 614604595 1250 614603345 614603383
    0xa0306020c030910050409061205030a0e0a120305130515041505040f03140c0f030a110d0c06020d0813030813030908060a0c110604030225081603061d 66
    0x1085055500d0351080e9205268491320052810f43c01c942e1005c01001603031210b1006002241d174510740d458000108030001441504203208a0552600c034036000510000c0050410714030558502154000d0305100304250002500001c0244203580700102c944020001501c2c2040141d40c41c4074034030030502481c020702402c0c200301c0e0b04540b0400e21400503100600340c2880e5000b1410381c0d903c0c10b490200e01d80800e05a890203120303d000d070306142081c0c02064101c03010300640101101a03580c2d003881c407554084240e10408500c2030402040d00030010070050146500180100d01d202c8201803d40c1070000c0c100d48942e04002a0790001a07486480181c01207001585401600014942a600c0c0344103034101118612424080041c0302e407803900b000910407072544417400000358910141d80c860800b00e0740500940d0101510500010091030180c0390144119240d401e800e4440711180e00702070024400610504c1c40b84824401d0140030303c80d015405644001442202d20001089a141c0b1008507454280c050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 614605845 1250 614604595 614604607
    0x130b0f06060a1115010914070f05040b0702010504150c021206130b0a18050d0e010806030706110a0c0906171c0806010c020307030615050904030503011203170906040b070306050a030602 81
    0x9002c005560903660f009107070080329030b185c02129004088001003014144140340103d100940265072827640d44000e5614039107001d003803418564080e84440c90803410854100700005020602c0c20140d20b02d0221980c03031844203803280c010840c0b122480600c62410340c00c000c040c000c1d0803038510943c84600340e128001e401036a9814401000406110741d080940c0300b1450313000e1040100208500d402c115050703d410441680c42c50045412840c202c0724990160b20064060000ea400750314035002050b21070003124402d5a440d0303907004680c441540b2051810303890315010311458104541e92000c4806000c000c2401180000d4421149000b0026620600841e038011860030b03481900800406074000c3c0c11603010999915045004150808200780c04d080039903808116440c1400f1154061034040d51030f40e055900f443c4e00c980300c10101080c11400c0c0000e4000d40319a00b4261140c191085003004c000d4042490141007500310244024448000c02d131500105000a60355140c0d001706881d04100b00507161a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 614607095 1250 614605845 614605877
    0x30c0304062705060106030e010605181b040f05090106030207020f0f030f2401050102070e241005030702100c1b15020309061006050316030b040f05130b0f06060a 71
    0x34150240b0700000c1642c000d5403018031000103800d5040b100141c3d020080d14990803c00d43c220744950040640c089280500304007260540300290b0b8020b040d0300c0b0398040e900b4201040495641c0240d01981107440c2c08a0200000c0c5844444c0600400c6103040c15860541c10742d0004009410320b800c054400d00411b804541240c40410075514042c04070400c0f00e08086503000d40d9158120304e000d0005c1c00c40b03006800840c140d4808180c40d41100c072070f04070b0310700541c0b41c1c04990100006402c01c007811100c3c0d40c41642c0841d42e61251182500010740d15940c4d83d82c107059800900b4141c80388941c404460408404201603503000100340c0e00d0103030390844a83e20311494501004204118281c2c0e042c00343c004018003410345408100103015020070689840e196945d0f00c810359460104441c140540182c0d0044084034070301036041361a10080003440042c0c14442c00074003108a074419580d89001c4400b92184004100c1455010794008030940506d9007079107091800142c41d84038400030b410401101001e4441c00d0313 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 614608345 1250 614607095 614607131
    0x60a18061517012c030a120f1a03160b090609060d020c070611070b0d0e010b090c1e0f0315060705071503110c060105061e0f0c0c06030c030406 63
    0x40d2840c0700c00c41c85450301c0781d8140d42c044c3c1010051514180c400c00c0b00003101440b8107003861002c0c1120006541068042c020035242035003590003110b000380d100c10701c0f2030f4920400d00c646c00469a5140c00703001c51003186014185410340e0521032072401010b00c103042c04503501d030b10b01744ca5401100300e070340a541d030300000c000c280380703024030000088514000f240303c41c4d10365070204200b03051b1900d40d51400c2c486007041d80100d41d102464400d070b8050b84810030461036881c03110741110014820b502c1c00410400b5540000c00c41c036040c2101c485a400f80003049151040024141821038a0320400c921402c08a00040034192032001900c5c5007040300c1c0301990700390142c642d0411744070201d4000342502c0c04240c0c3d5010208121010070300902c00649481207a0740d01c0c245181c1980d130040440401030000740c0c244000e1100340e9214850036610320058a20070b130560041c2c080106080c0801049264550fa0700c2d08a4030300d040054031840744a21005d0003005550781101c41617a07031060704182d02262070181c00b14034500e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 614609595 1250 614608345 614608349
    0x50111151e090f060714070f0201050f0d0b0102240a1508160303030b01030e190314040b18010507050a06200a0302090a050a0b1608040503031b060a180615 68
    0x5034000c0d2041199030380d000b00d481c52404043c102a60000d540d400b504440030307503a641d58451400700a002e0007000ca03400703a0501d84400d02c181840d91512540d6030000155421805154200a844000d07843c1d8559040c4000000c3c01800d886c0c5040c5040d40a00620709144000e0002060980c0c400c40146001d40300c8005400a00c80d001c2034501d1040071448504821184e40801e5002c01c2c108202c8035465440f0b0320542242e0f82c04900030780340800c44c1c11080341c20301d0f41f56030040e030030401c111408a159018880c010001000007030003080d501c5001604040c015158241c5a40c148a402d0000c1004034001281c1d1100b100d82c40900050004840c0c0402407034215484440380d0403c00c04206002c25a070154018251303010111185d902095440b800c01c00c2e521074501840b416041e09018820110b0f5241441c012b0140c422040c1a0a142d22403001c245140c0102000050030890081481e80701d04017480400d8000d00b403042c06000001c81d400d05000301c0b0800c1079006080c103544458440760300c441c41c0c0c44500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 614610845 1250 614609595 614609641
    0x5030705270a0b0a2a0204020304030e0a27200a0203040e0403080402090a1e09020a090e030714150c070305090910150504050f040b15121005011115 65
    0x1100342c0d140c800490f51030700000307010404128030b5840c0750746840c0800a0900400c280c14015400c200d425428070002e5000600110180000c0909401c1960344410421018161100c07515419108000d03445034075031120b00c80407a50701d103048030f2602409002c000d03140d03100f04d10980050f40c9604000c0c040f440c40c0b160398055600d10b20094240010160301484141c0a075000310344401103900c4050b43c2d0001c40300c40e031900301c1301d1035500d2114106580c41508102c0303039140000c5c0907005d075a903101b81407019240c1035811110a50400200c0c24108043c55801a6070710b850320b00109174101e08480c48005e24100a00038490011020801e00308051040c000c48160340c90181007400ca034200303041c1124848a2034018030300161124043c0381d44692060007554110340c00144031510501d0f20701c003400010295000000d030070066001040da0381803030307120082c82c400d4041d65030b48882d843c0c0f1080c10208078500b0382026041000c144112070484400013408408070701d51006088140e200c1d03c03000345d00d051450a08075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 614612095 1250 614610845 614610859
    0x360b13030c150209091f09050c040f0305010e0d0f090e040611130603180206040306020f0412050f07050901050108040b191509060501080c0d020d061a13060503070527 73
    0x12201c2e40040c0c0240c60780110640b050504e64a0310b03078800d0340e002c01d92100120040301c822400c00c2035590940185070041c1500c209a4502a1141c0f000203502c08070350010b0307800740c4d101c4400f280071140400c202112000c940c5810340e1121b69000d0000d00280c0c80d8803c544845c101c07070010509210582d445031034a0000000400e60304c020701d0b0000460a11988295004603180c40c1c50540102209100400c0341c0b54000c1c065403070141140e07640f00094100c51001e06481307400f0710000c0b910305d45224030003100e14002c0c4c4c0101003035040c071a4a42d24080e0390b50001405002c84500400559801100c0c140c3c203d0f60214600480703a0f10903810544004900544540302800c0503092070000418103001429200c08000c20300007181c441300190745040f800d480209174040708101c1a29091101d0380503183c4203003034210114545960340036140d1100e0008080094604001031101f52181007402880000c01160074018150b01d00544098100e009440e0a075003151080c0101d244841109040d41c0078020008002c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 614613345 1250 614612095 614612123
    0x109090510020c0105040b0105030616051e0301123f030e06070c20030706110f03070b01080c01031a1009080609010501030b0702210901050d360b13030c 67
    0xa14064082502c0075188601f1407000480d060902040c024070400001c0390007004001c1000c0c0031115988480181c040d002e05003002d80b040c081c10080118001c041e69014221641200e00f49001b400301400034440303014040e84000135520b02418003490000281d41c1104a01d803c2e000f00960190181100843c100d000309810061200e400910454000340100300f0b4602003000700030351012803603403842001d07415488032000300708450dc43c05010610b07240c5541580c10b008800c40000749590130280e81120390b502c3c01d0340144601c030b408001d20074104800b481c0501144840c46403588030040c0d0120080d000d2904903845c9101d0302c2c0200022002041038500311040381c50909a554002c00080c0402c541d43ea00c0480410603082c4001200c4201003070a40002e4004001c10041d411035502404185050000c107114100c0c9c030080900c40c846104003186002d05444800714584110303895071210411404100c4401075000c13032005151203900245010034038040a10b036040643d80a00d0060004165090201c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 614614595 1250 614613345 614613367
    0xd0605040305220503060f0612030a020d030e0303062d06030109092a05060304110306040f0311071404050601020f0f01141834060215010b12010909051002 68
    0x1002c3c0b118540d40c83c44021842c01451150851113481030660581c4800b010030344a00c02000a41e41002c8010038005207503001403035060650700b2101c0c0180c00340e0484c4000d0701940742c15000700b03c4200c80784c0018602d9803414800254003003800c0146440d1404082040390345a580c01400030380300c03540061202d070f00c0c2e42c1e5a40d1014080d045c3e420301180d115030300c1100c1c00d012b01c1220344a56402c06120720742200c100d00703100078030900d130b00010300c06d581801e8403105041c0c85850512806010b2400340981c4071952030281400b030411808040d8040d40c2d5804400200306611410700004001c103000c03a0702007040d03103400d00100d1034041000041105401400c4040700341c2c4005512281310360004001c030f0740060ba80c41c0d80002840c100d0700e20800250b00420a601f869107822254081e00300c0c121441200e17907420301005800d505071035401000169009400003502c1c10314100e415401041982055494849080c1a425074100c041c49607a8031240c4910b0000c0c00c00c40140102c210410003204219224a40300360 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 614615845 1250 614614595 614614597
    0x30d0903051b150c0106180504020a09020a030603060615270605070c0f170c010813020d050a081308060604020a02030a0f0309082802010b030c0f032a1f09140d0605040305 75
    0x20811003218800c1947c81c003441c0407801140d1045400900d968080303071905800390080d40c420450726080503503030131001c40010418070944020304050a20b1010b0000781c1d0744040c200c1d07803000c0007842d01c01c017280103070000080c410243d00003034031020701c0c003940c580e8801c0c5000300031200d0b079400402080c540204003141003800304550399a0620540704540414050a0056440030011b680e034440e14640c1c140402c002d4280034401080071803041080718091880382d1151403541d081182c02502d000181e0f0030130402810304014030386e040041282e0852800d001c0c118041d64a11031010801c0038000b00d00e6080c46028040c2e030010380f4075500184540c4c1c1d90003500407035005c800c654025800d0350503800030408000c6881446049446100a002045107610820401c0921318071482c94640c180300b500803459109400403030f0180c080d852504519135503004103040107030614240c403060b841c0e070351151015200280d02c00c440500303d500344008014210608404107074071a003a02c0d8090300c03890801c1c044c0000c01d0b6200d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 614617095 1250 614615845 614615849
    0x10614040f0605130e01060804032d021b0405010b03070818060103030905011101050f011404091b03020a060212030406020906161401050c0c07030b0a0b030604050c030d0903051b150c0106 82
    0x40b040c4e40743c003600c4610400340000300313021b42400500920005400a80940d049410852104414032050349a11206480302e202d07082c08100160841c0301c03598070307134040a202c0c0004204111810310071503041070603465071030000415034420014807902250600c0119550f800c041400741c4240ca10f203603100c0c00c0c0504842e440340f142e0b900040c40f44500400850040c415030f07000700f40c002100c0710164a003a20350400d069854002035030080d52a030710000000c1c2c0c0990010702d404a46448ce1565602e140100a001c0c10319911400c2990401030326004041c0c4041c003100d9105034070540c0140c031013400c80d0110701c090203084010034045025850340e4003031144810888030710202d40c2009211942d108012641940203100114044d540000130620014a28205403a0322410841c000541c500050001a103002015a82034903280c200e9000c1413402e080501030900150110b08010001c9465131361001e46da1070340c8400048040442c0080043e042e6183c1c0a480000504184007603112088019070320300074400c80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 614618345 1250 614617095 614617117
    0x30402011709030c070f05030a0f060209180906011401050f070614011205010c020106290f040e09190308130c050a1e05040902010c0b04060b090f2d010614040f0605 72
    0x868009601701c1b940c213a01081d2003018000d030540013150b9a4a00e13040722690b00840d90780e9024400306d4640c0c1c65018020b0700d03150f4445001071450818800081c1880b406800c07400b5045001500c910403032760400200d40c011410044411b5075803046040202c010130300c808440c401c0740f103080d000054002d19081400e0011340904002c1007000c224010503422150284150000340c1071001300708501007200d090b0700c1c42c80420b01800f0b502d03100004003038002940c0180c1050411030a44014410280390800140020200d1550410004055518003400c8004000c2186d0240d024046103182003003a00b8420f0001000090405010203403200c108144e00c260283c1c003010307200031880000603503180030300a07504400d4041c2c5840e00d6400e01c54440d110071901c001c6c015180140c4030707580f1404940f990703080350344180741a0540f8400c40c01c14020160b2640031005c1e150044080c020b41d0301c000d900c09118250704542d09800d1024210304075940303885081c0500c1c0e1100040c180846c900041607900030000b46411462 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 614619595 1250 614618345 614618353
    0x70b07020705030607031d030d02040609091a040228020c0f180a0b0a0305161a0c060c0d0b060d060608010501020d080604020f0d050718090b06030c030402011709030c 73
    0x40000481e600e000910400d0381c150b0203200840c0d05240280c4c04052001e4150b09842819101d044815103568840c0021506980d4006010003d580d0712050301c3c005422444414000980da4580c102c601204508442e40304079800200d2030411401842880303201521450340e070301d8940c1e8142000e910354076034000c15401149290100142481c0845072500d02125001c1c0c054007039120541c0c03500c0104003400c8120b400c54a49400031021410801c4074003050762a440040c03825604024029031200c40b4141c44244e6002d0a205070218080e020640a6000214940480d202e04100c0d07201405031504100700c9401c2040024920348000350f540044c0c0507a12079171142c2070300b40da80d0001241d480700843c0e1640d0008402c44003142541c50550020f100390041c2410302d90910640148090403140261000d001241c00c070760441c6004413232102041c0040c00e050004002d00708403180410401d100c01000400804e200000160031a80242d04803036030810011140f404a15003100203d030b03030741c1c0216840705647c85 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 614620845 1250 614619595 614619601
    0x90b09030405030a0f030e03031c0c1407150f140609250c03050721020c04020f0708090604080a0309090509060403170a0608100b01121b050c150705070b 67
    0x40001101c0841c0c2010300100100111a21084a240002c0204508004d640c55602c42e450754100040c094504c0c5401004141d140490208411503540391080c1090011190f480c9004050850550743c8540d001a040009076140e04250030081a010b0907000b0301ca0328280c8400180c98514202ca031084100f070f140394403d901d031565003200700001c0a003018039070b2003800c403030319140c9220b41307907580d54a4400c0c2005401c0c804a44e940358400c0f40d4840704070f000080350284d040090342e410002d64442030000e4408500e04048090289014030442c0805002c1ca8000230300070420740c403283d0480d002018000240d03180c40c000d9103401000d0b8a0103214510b00681014081150000c4c0400d9190250b035058844c042c002c41e81d504412070f8184004c00505440741d40e003000050b854010302c402d80498005020000350084404005841e241c1e00440305034015280c008140007411502045000740b1209081440e12160b61100a0f840c25028411654600000500384690241c120000e451850700c92041c0b101155 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 614622095 1250 614620845 614620861
    0x90c08180f1209090a090b040206070809030307060906240b090607150509070630140f0601021011340308010609080c0a0620010603080901080c0f0306010e01170a090b 73
    0x2907041c032800fa00d03000540000c074005280402c018400700344203c00840c10310141400081c01e5410c0301005a424646440519007040828410700090704a12000030120028105041c00380382c1c000c0c040c0001922000030006402d58078502910809a1b1103040c40020350280c24071280600001d5440d5401446030120208120380103005d40c02006101000740200740203810312030f0900c0301042c0c8192045541e1010307808582800142c0702489552449032150310b5042c902c1c00281f81001064030f00f0700d03051500d04041c0d4038000c6d45040f00e9003c090151070340e05e00a800b00894548040e002e07130652140110780c600c101019000348100c3c0c101d072181d440e81a0266130700d040381e645465141d00ca0541c400c21440d8144000d5001745100b0000c10250240915030040340003000b404c4a805030001d4480d04800f080000d410341e40016003540c0322a0f0b202049040c25940703540a10309010203484279060080c0028100e146074440d403c5075071110400c1e220341103241066801403009001840040e94a0001d080000d4910 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 614623345 1250 614622095 614622101
    0x10902190f0509091005120106030215070f06201c0506040209060904051503030a12050604200306031c03051b0412080708040302040504080a09090c08180f1209090a 72
    0x401c0d03840c2c807010300e094070203420001403481c0200b0f00032020b0038100002c1881c6c0c4801101c400c004c2c414400009021b801d41c01000030003000c0d842c02446800041188800059410700c080301031513444900400c490b00c010f04c00815a0181c800b40701010320b40442c2080a0f003034003209003144415400000c10040c1ca90106001c180d109100301580c00204c1042140c0c0700342003580c800d5602c0f82207250710a8811003035000183c1190f20001c0d00750001084062440044040e610459402540c116002c01c51220700001d22420040d0110400c603001c5804000603845031000e111000c48207804614107110311590040103001040b00f03840d42d10380146852070040292414100315020348981d0105a8491800c84d901c00074664040c000c110340c1d00409000000c01601ca6010706405a44502d190a40700d200d50680140514001d038040d82500d800c00002014003034212520f540c01c103042c00f400025140c101411141f4028188000035224032554859110703691801e00a41111441203600f01001d4035042505415 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 614624595 1250 614623345 614623367
    0xf0a0c0e01050d080d0b0a0b040e010509043318120206010b03011403100f050103151a0618030a110112020405030607030c02240a1b02250b0301090219 66
    0x459020824000714000c4d0025045062440c000070640051010204850400303d901c489076042c4040f805102032525400c0080c0900001c0d00d006000f8a0241c896030413801d030100a20024075002c00510000c4402914200700810200c4014001c9481000c554600011019800d50740d1000700c09441c1152407020030218100e90b4401200d07425642480001280e0150fa00c3e0030a6052040b8000b0070312003480e501860110303106e40c1c030000540d5855400c3c40580020941d00320030050785800341c07102892003003803400b40b41c03500107450301c079120040c0c414841090180d0602960b0b052080d60003501c20080c42000d00b50b0614803c2e0b0b5040f218545043c42c0404ac0d00545c052030354160407082c00501998420f43c403460b003480251049515a42d110005200d1252019080040030010f500801581c00c07840d0240310150700e0910810088100f541e231000f900e030802c01082d860302564044004140301c500c2e04402014141da058a01e41d20359541f10310348000e52150050180001000d00e110001600940c80503507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 614625845 1250 614624595 614624599
    0x80a140909150a1a090f030f030f09010c02041409010c0c0b0c0a14030a0e070b0403020f0904021207060c0c0e01060816170103030f090506130e090c030f0a0c0e0105 72
    0x20260325481e55207449200e5030380559070850b00c003000003d0640385007040c03501140d03138600a1a6a54802c0018424501000c07507529019601041c59558400c000004a552004600036a203848000e00c0740100c40810035104086d500c0340c200390380b1074040300742d26801601900d40d140007089a10b14942090380e9002c8030b26005088121b0300740005042c080001d0003807014824502d0000305201d2241030040f0241c1041e42d491980c1a80c501c0c0329040c00b401006000c0c0600055032409081c0340c610390010780d41c1c1c90100e0303040b0302490402010030110b4a03030340c1071014420b50401c01c1d1800540c45203401844541c04000650b11160303d42c0c400030f802400c0f880307a54141c03034141e9210349055968a001840c0c20020b9074010701000708102c0d010f880c640e00500c000d401385109996581c09840503080c01001c02c503080e0000340c410741040210700516620001c440301141d001c500703104141d9440083c0e142c1841d4248002c00d42501030320100030315180d0081001c13100c00d48a01440842a61a102c00d000d107100240178242d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 614627095 1250 614625845 614625859
    0x17011d16050418020114250b0f040c170c03010f0b2704020603181e0f0c1c03050418141b070305180d0804080f01090c090b0616080a1409 60
    0x9015500c07440700e800d81b444000340c03800c0c0707002069400c0010b45071050016007604c00164030b0391000c20486620241d0043e6141a00b411142080e4441420707219951040d4100750550546c108281c2c2024000210941d000800811446035403000c6400584460802c040c4a50030701d500003c00e9031001494000c454801c241d00056554459013030000d02d41c40540380400300c52104856030310b2030500300014030907900e00107406006040300040007490103040007140201900820030707003440c9441c0c0322909488120b24032200144001d95040c159000d1081d9004007000c000420400405030304aa00140c004e150012002c2e09569a01d10301c81a442c1e00032015038030114000c008240100e0700c00c10190014507141da08000e40078218a0010f2135044924004076041c1030049010424002c05014903017040d42d204d0000d120802c001e5451030b040c1d100d98051654080d55802c0d4083d203e0315070700251518802c00c00c030307207034202e50203820700d86e40c680c01c01c155800029213100d1000210b62203007400d5580084001e4540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 614628345 1250 614627095 614627141
    0x9050d031104030c03080909060418170c161d0c0702040b0a0503011e0b030a050c270403020f2e050702100f0b030f060108030417011d160504 62
    0x22000703080d020a07081c1401c1810b21020001c2003244034a90011403040030500d6544600100f804240700c80103000c02e03c80d40c03074107010f51140c0b00183d07880d000c22580226403c1020324480c010805c00d00401600c03882c1442541121144000400700c14406e5807502110441c1a2000380f50b440c480c440102c49403070031280b080c41090014107103900300382d1060b01b00400315400303280c940010900b1074580c61031049076169500701158003084030703104140c44254142d015013000c010641795540c0e00c546220841e03010380d4201401802100f9144403980e4030a55448020402d400c088c00c00a540380c500341c401243c240607070b92411080301c036480d01010014581e01c0c902001c54009840c01001001d00601d154158000c1c4190740219440030300c05c60b0540802c14000203111003003041890710b0110381d44401d50440c2e11220062203103c0c400015a0107d481034810441c030011000b07000c03030140c00203400d4007a605141020840e081d070b002003464401a440300d81c42c65a42c568403410401521460407240019960322105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 614629595 1250 614628345 614628347
    0x140922060f031e150906090213050402090c0906091201020d0e03031e0f06061303080a050c06010e04030e12120a0f0813120c060b0a12050601080604020f1c0501050a020301080705030109050d 83
    0x203c00901802a030001403441e51f05e802040e640310241c101c00c0b41c41035445042004525014410750303003145512031054141502080402c40f14890b40d081d582c80340c0c1080800e558551000d40484080b5100640140115211044246c6e56a00161041c0000c1c415048102001c55000820a8880c90301a07030070284d01c1d01c403038090100507840800c1ba444030642850b0040085040d02002b40441c4625565503a03565503501401c030300f80003040e00100c03a401000c00074400400d83c0009503055203032040b2000b503ca041170000051414080f15500c07c1c588902060441d04107401104c50a020140b40e26000c0b0a6602d5601e142c02c40114a032006081c000441e0283d85818032448030002600c0c41800e00040700801000061754011040d03214018800d6068440c00421038248941401031410314000c110303030708050b0b000988000050041c54002d10011007120040390078001010b008503046002080b081c00d00e1210b1030081d40c424050007407184180c140003e1075040500c105041241c22002614041e80c071500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 614630845 1250 614629595 614629601
    0x60f0c0906072a090509100e0a0c0b07150915050c090306090a050f060106080408071707060c091a031504020415020604030f140922060f031e15 63
    0x2600c540200d81840581c00107120450a0020211000c200384076080302068020140c901a41086603218204400d0000388800003a520981c844013450103da20080c29451510301800f01c5000750641c1f0190a00103a070800240c024070200c0c1c06041d100212003082042c10041d905409002049000c4103000c3c140310f0300c0c481c0d10481d0803c0032200d01301c2c6403500020000340b80140035180f45080b03803c21010381c402c0080070801c480c40d05141d035010300025898288050072450300140040e08240c40021520200441e51500d01081820488859101d008a041c0f80000f4440d8400010110b941104003140604d012050302d104618144000c6181d03907a070000586500508103003858000d40c0a100110705400a1040c03504d602045030b0090080d0701e000c1c20010300019044140300140714490300001d030b640c0c5d51181210982801520031014801d03045800601c502c03459408040094a850004150020700403400c1d021640141050585220340c201034506c01041000c004040007001e007503800007074106070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 614632095 1250 614630845 614630857
    0x3080306090a0b030f1f051612090c230f221515270b0c070911180f010e120a050105071707031b0302090a030602070c030302060702060f0c 61
    0x402c011409149020100f483c000805190114a4201e0081c107103100580c2c1d45202040c4009030f5090049040014114605802c1c42c0c4a030010403079414010b0300165043e030001c0c015554840079040c041075840965120060352044082e81c43c900d256007000c0c461414011110300648024070030382038000000100c0d8500940c2000492086440b00e2580395103403100c084040003042c149602c4134100c000114018060180c1c890310b100140d090209022032100c4000510b015030f84002c000a5172143d40d09812458100c140d8040c6126500b4040c40300c0c01f01011102504a280107079100c06c0071008101f01300002440e0484840c1d0010390820403402052070300c425116030702103502d819a90500c6450311050b00351501258100d0204480d07500440100016100007640481d2619040004100d60040b103500e454581c8041c204168000c10380048955031900842d00940e03000408542d20002498070310b203140c1d8a0f100c140c0160042100007508140007107442071084001200c8004c05684440c0310000e20341000b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 614633345 1250 614632095 614632111
    0x409080301052b0f1209060507151e0f0b010c020904022211030403080106020609101d1605040b090115050d022215020a1a04030c080d0c03050f010308030609 69
    0xb031038004a80310f02d404944803040780200d60f445034166250806048146040a592003000380c1c0b40c1041013010b90020070b40300643c0c1d000581e81c00d0342c1c440794440c402a1001000c1014180b030410340301c00d01d00a40354840844c0c440305040a1008000410055a0131100303948043e4000e01c510001400510701010002e084155000c0c500e8000020490000206c1d20411100350204c0d10020510080c540c001d98030034010416840100703028a000c008107034030380440081c01c1c054107480307106d508482078030205540c0d550300d10541212103490404001c0000c0e10034610629004ad4509142e407541820121442c0e4107030303560884d040c4da05483c1c240c001c4903d540800052408140c2c01d00c0030301344440e90300100070026010305041c102c0b868241040070062007259000b11095620118a9a0005540380004000c41c0c42020b08582070f0387d01c904003901c58012801c40140803e40001d1104129511613206001d4401a90380030030039660380c0450300565140a008c00f81040d6030920010b0b44070725000881c16440890 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 614634595 1250 614633345 614633389
    0x3070308090406030f080d110412060b0f030d1d0301020f16260705010b0301051003020126040c06090602070608060609041d03040302040b0f090711010603050d0c11040908030105 78
    0x1403510b64015070201170744c04586084001590309052800c600444101c804503d110740c0c605807514404402c0c024007008006d1040d501d81180381095030b602620f01020500140542e10350076024900201038010285203206101c1002446103054141482602c0200c040c0300c030003034604049112404c1e0b150003d01c1080360300d081e6200741c881c840038103a1009000001440407040d11210760713240103829034510402c241c1c00382c1e150904100050700203500c46000c0320340a00748211400b101c0d16940141950008803508201c044105000400411807000301c00c981d881c1e642d05d5000b507201e0404a0f202c84452180d01c00107810540400d10a1420400410748c1c50001000010700380d040e10900800c03105844040c821a41010500300103600300740c0030345410240300722180260382000b01c001407429100504014100008920181005c080c2584000b020b190000c0840310002d000520041460800d07101c122400e01a0190070803050505019100d1402e62103081d083c2160300380000c0c01402c50b0305140f25180112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 614635845 1250 614634595 614634599
    0xf06100e1807090b030d030903050906090406050d05210702101d0a08060a0f060b0f4005100e0112110c0706090b030907030f02040603060e0c12070503070308090406 72
    0x100801042c001400c0100000c03a860380804101410001000301c6034050508140c41040000d47c8041118100c2c60110f84803a107c084020214005088503000f03240c015042209031010b0040014042900648081075607071140b40703003021071045002d00c1200940000f0a40880c54090380180d40d2507100c00300b004500c401031a445800104002225442525990000c0b0280010703d00980101a040481220305010301ea1400a00945500c902c0d84d03074020045000c5904844800c5010344000d80300c44640a80d955990f210301194150f403840c010311441003040290024240c20035801d415440d545680b1003007101d0102d0401550688001206000d0041c0e56030a42e2540040d0b400c050400840c039480282120307410094040e208240a402081d2480e00c03d100300318800780c0000c3c110050f01e60004803881c28540c1403009c500603041d00e0b08000d103094101507010b079840c40000741000a0081c03c80302540381c0404c030288942c49403494040d85405805c84401403020070b0614004044055000c0e1001a03896 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 614637095 1250 614635845 614635891
    0x1e0402010e1c060903030b031902040b01020316060b09060418020925180803041211010c0b07030912031b0e0315090610091b0c2103020c0f06100e 64
    0x42d202580403503074180c0d280d0122050650500c81c1c0183d40400b40c0040c91075813003410340e115a0440001009224a888000001302c91b4802d009855240003400c859091616051901002400e03141d10320a018201d1800060300310b140c1405000d0002ca03d00e00f070310070781200030b1b001e01002103c01003031345c401e140890040304000c040d4200b4420a1312816034074880e039200500c65400c4500f44c0b030b0f400082a940248401e002c407000201c440a181584003003810720b400c80c07500042e1003c0d00c0005010307260091030402c02c0442d50f0903070031041c1c6491003190b1402001c0c031600001d60807102d05251110f0076071490b0790030207045401448000004240101120300082d500d50014801107001c17a0800702640150041c01a088083c0c405030024101a40c2c05201c4442003031480303080c243c08840c101e81008111070580c001d200c01d1000d0690708031106e0400c135102d50010f00700036001e9800715103010315038400d801400100d002c020803d18094114102c0b000042440d00c464078a20b20b1019200400c400558a5018030350 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 614638345 1250 614637095 614637139
    0x6150f1401170a090b06030f0601150306050d0c0e0f10182c0d142703011506120b03030d020903030d090f02011d09010510051e030405061e0402010e 65
    0x640341c010f00442e080701c15103090300c0e8504000c2c1015001e41c0c8030b1038403d009000c000ca1064150307040c43d85940d03034250781d030a0210098a200e0384000d4024107808244414400c58109603030990b810001c1c0b074040d50f201d6071004030480310200c400000148000d001800442c849641003a0401000c60b0003150003002194460350602100c129001c858003111003000c080306051000749030341e1742d49007443c00082d0b1400c92a0312403403150304500101501c00c00c10500760056400024048400085c0c0200a0004501c603080781300e1480d40104070219581d24180d500140c1d40340551820340101502560074185944460b0001c0d4010508582d8540018401c1401c162414401c0901c2d0b240225034021000900703000140c107409a10100600d04c0b103ea541984041d141c86507214111071069855801c03c4484c604112050300400c8107045422110752403440207804418003030740c0183d0148090301c9158990119000e00502c40e0f1074004000215a0000340242d070042c0c0009985c040080c0000001c0900c8441035052 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 614639595 1250 614638345 614638351
    0x411091203040e16020a2d060b03120f07021e100e040c050a020c010f02030c0d0903020a0f0503120702150d020a0807032d0b061606150f140117 63
    0x4551001c03400f084800301d01c4580070340081203454058402ea00010f002901d914a24070040c01c1e904030840c134081d503003410851681c003034411602d00700403801d030358944a40503102d415081d5100b44560300713280440344032a204485002e001d1940e501d1400310742c2d034284241c02d203600402942a01a0442500b081d48801603c0710310140c0e9684c1d191020f891040400c022240f040c20320404019050024140e840d030001001c618010090910050001444c0c100324903500c642e6480f460300d030065034181c17000381d60400700354015607208841451269032105106c2c2d0b51508507100b8158944d10100b803048050000000800750140040d00c4046028048080307003007264006040c03800380d0b6900081060950360300004090300300425140c18042d00108070907000c94205150410000000844075484200109901c400c80a51000d80f402340c4414881d0b455040203188807905440381d44c00c192064540403107450700c00f004d0b82c0316009195201414a12888568504100c205045c40364100c00700140102c2c400315544 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 614640845 1250 614639595 614639629
    0x3010620161d1f050603180f01090506010b0f120c0705061e0f0424020d0504030e100f0203030106050c0a0515270a0b091906060e06060c0c041109 64
    0x10407500c030810360006502c0001e015040300c0c403038411110081c10b5000c08207011904104c2c0d101d0b4803134840c2c072000c0e02d242c00c0303549072080d05200d204200f08804806400000801c0e0044042d02c030386a0340c481c16010b040c466500c03001d06aa40811158024004900b825504038013011105400d0001c0c03951001e203801d106a40d010803442440682d0b00003011605c0c07070030358440821602c20382542000c0d9a031034428140880800204180e001c420071401c40160305640310f010141300140018101400d01411403280188070601800c003004050340c1482c010078880042c008035a000b1440c6130b10306441140c290301700f220302004501520a110020940400580905243c0c2000d01449410010046e844250400e84424010f181c0d0700c0d0040085040801c0308100d00c0d822180d241426900c2c41c0300c15040840e401c03180011403001089413001e0104c00d60208040d0303005501440e80a4a614040107040e001c1d59005c00b00d5a4029500321900b0300b03041c1c00c48401380015030501d80c100906800026004d00500003244 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 614642095 1250 614640845 614640869
    0x190b030c0d0501120c030b130203011d0f0f0703020f0a0305061609171005040c0e0112050d08040b070309030201020c19110105030402061215040207140c01050301062016 74
    0x10a0080a00c906401400800c1c0c03807061340d4507955680d1038100c25510000e005014100e002034403500601c4940c4114a0b8002d0081240c00b049032840105030765020700b1410035110352504c0650030800050040f90301e40c040d10051440e0f620750303820400420060344030306801261003d000030002e8801c105190286c1d4100f074032104910095071000341403690320381c80621070020340d0f44a10801280400d80307402e911201100030030b4a64840c24030f01d2074075526921815103000900300008900c44c1c540c00120403980706070151040007211300400c444182d0700341c070701408081c0c840c40800c0e9041d0196001400d054400d000150030003c956152070705000145079003c00c0304110008803401c1160f03c80740070b4040304c400d013025402c50401e50003181c0341340203410000e07411002e10b0300412460b01c250410a0840700c8010804d40d500e07480303882c0c20072900c040b10502c904940f08501c019042580283c082d00e0690f03c095480d881040220036101050320071400c1050442d005400043c070310a0503070841c00f0301030b19068500d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 614643345 1250 614642095 614642107
    0x210614011211060a090e060a050909060a050a020306011706040f060b0913020307051911070f08010e0a02030c040f06211205030105130e030d0501030b0601110615190b030c 75
    0x110b424901030051284a10000c100b00c031043e0740c01007203603000d5942e21242c0840aa5540000c1618100c0540155034130140200030400090400540d030740c4180000e83c42403155485109140341640000d0b200c10303010980c0400e10070782e031990344040d0540c0f1074802000860458200c5040208031407a0b5000021209000500446941401c1405002c501235001c011481c61030070740d600814602071503c1d103030844104c11814421840c07103041c98804032602c00054034209035840428800d800c5241c07158200d29401d04901c1c1ca42d1450100e00380355400c0d00940503100c1d03a0164030400004194441c1420138041c0d5410003c5585050000303118019482106022a120481e05100d01120b00000d009010000100014072264403580340205980d205200007150000304484c0b124154064030012900152404000009011119503058020315082e00c2d0022070441300c80c0d4103a203646040342d189800422100c00707507556041c0400c100c04004642c10714400402d46541c11a4940e81c0143d410b044550000720b19 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 614644595 1250 614643345 614643353
    0x2031f0e0114010e0a0e04140709020d0b04140a050c1b060a150b0f070c21020f030106051509060f07060504060b0d0308190e01060824012106140112 65
    0x9100725850909142032024a10b00000e40d0a9017103000e654000700940020408216203200d0728074049400d40b054400041e15494084001c1d0070620000209030305211000619003828480e4039481007110f8203014a07a0303038000142c0040c002c0580500200b240420510285161006904c40e071000000042c1045040c10b40868065803403000b16a080c094180a00300002000b03001210750785c41e4141e403c0e030344a01480c1040c1380c5108140d8411040c1030b0030803c00d175036211400c03029108914800c551040410b0641c000f030600303d032185d0040c546c000381e1250982d26100ca28074050540c0c0c41d80103181900e40744582d4162001500141002c5507082c0d20741040c401003005501031544000000c0d142c106903026a5203000700003803030240820702c610b094010002d4103c4141d07040307058010001d20003840901e80c1c6500a82c1e580042810144007034091640381c040b20481c404040e41200d249100714001000010800a0724030401002190701c16a14110640030310980380155008006060b4a800c00700c0c01820 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 614645845 1250 614644595 614644619
    0x50d0f0605040510080303070c0309170f1c09090914012901232206110705060a0203040b0c0312100303020105091516020f0109111f0e0402031f0e01 65
    0x4c1041c9000c48168030901c401a80081036950101030b40c0340c51049104a400c4c01e8603480d8540d009180d060f4844443c040d5441000a03503c10149031050441d4000d9080f0046036501c3c0241102c44000600340d15402c00007610590000b00840c0e001e01d091041118880c900c0d5401c4488059002c026003070b0203d480307094242d000e5050880803400b030074039020301c9034a044204c1c00c01103004100b900503100841d08148509080e0b240d50314480f0034130f0690300495140c000c0035010346040c0d55904054419080003040b6400d091080d94030b103a0040c1c0040d4103144c10059210282c2c0c001c1130307100e030720b40c4000c0c4036200b00101d541c24428000c3c8000e0720711080c01800e50a00900355540148000e0044c1d02006a510f2003400c03000c0d5956100060518600240e40c0e03c80d0200c2c1001181c41d0300300340c150308041064051180160b18000001003c9904901005500309154041248000000c0c045140f01c00c04201e5424141c0045a1100c9071140d08035241010b084050520402c5410442081b200e502c0180043c01c0005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 614647095 1250 614645845 614645851
    0x60a11011506090914010509130609080d06090603080f07150c0f08010b070b1801060b070b09060609012d090911040b0a030c1203020c06031503070504020a08060907050d0f06050405 79
    0x10203100c800c0c0c1c541c1c01c1000d54401841035601441070000000e0315050514440ca0240707030310050622040bc0b01c0e040c100c60541224901582031403a010001918090500c581030440c5d41c40f031001030a01d0b0111005d600b4a4003ea001900c24103540841c40464182610401c1c912188039122040b003120003040080c88c40b40142c200d5401a0001c01000003c00c101c0206145e100c1a100d5024022074a2103241c140584201d42c802c80c20400045065030401803c100071910810b10748080b81c02a940390000c010440c8002e1003004a0394425218450030800b03600c1c00e000034a06805801c1131140d54420b01d40c402c0b180c0041e0192000d00c0c80c8200240030307140500030341300480d0044070740319074041c11601c50a01c4075000e0300c00c8121901502c1211800c250080c0000500d502c80100526101d140c5a903170890036096410380c03e0300c0781c024108041417038a01842034900e14501d651f0f440003956240d0051014414010703102600b07110044c0300d1007020316841d0084852440d071410f40400c0403854802480280e41d40a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 614648345 1250 614647095 614647109
    0xf011d090307020409080f04030807050d0249030e011104050a06030203090139080411010c0f05061008120a0e0d060f050c0a11010b030c060a1101150609 67
    0x820038400085800002e841400e0780444001412010b54500020395124402840c0c0f03409002050000c140b107404400303401e071036010b541903800060210000300d850311590300352100342c40301050715004803a4000d912051214070710200c0c02c4000318608135100441d05a1203048000035114400e0015008087c080c2c000c60354040c0c000300741010300384070005030b002107e405250304150780880000c14405007504000c4042c01440741492072980055100040503800005804901c01600e4a0188162041507214032640c1c0080b072035500c100907503004507101044910169010b200b9a80028081a024082d040c0203030b01c1001031a039a41c2c03800c10458200780b000780c884107201c24103006000f105500503000050341d4000711501817103181c0304e14000f401065002c441c01c56140c40c00c01004082c01c8040c00034010308a058403500b480c1c034558000e06007a288550303030113901608922030070001070800300043c048602c6541005200c645000081a08403000c888001000d60140704040100c00d4201114501800103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 614649595 1250 614648345 614648399
    0x2003070509061203090d051606090b090d030c0203010e07060e030307081e07061505011d10080a0b04051005180702150a0902060c060105011202070b150a0305060f01 72
    0x182400141d074201c002442240141e81110b54400c015100303100b02c400c40c040c0104100c5c20300c500b604002d40e035099002c500c10080c0c0e460f98000b107074aa0051018004a0b120100e4540c0740000c880306001170f11051107000c40502c12080c180a00603034003809420100703411100144811482c0080061440b10440500b9000e9003040103884c0c0441d00d150226890441c0144034903c41c01600000c2804500c00d040d40502224645172090100d6007001032901701315603003617842102840d60380b0340d02001c656035080e100b68003e06d401102d40200707002c0c09402d9070004403100006840031b10300c070208083d180300700d235940030000b821070043c03100780360942610108490b003010100340c0e0715044401039504d00800d5040c60108a103c1c00045104100e42c104607000350f0b02402a03500c07a01c103a50784503614031007170040c240418080000c0e00000c150070f200703449420b034020a0300440f9842c2c1c108880003090720a195543c00c0343c0c2010f0044042038007008254010001c82c2c1e03100c812585000a0759000552850030302d07100e20a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 614650845 1250 614649595 614649599
    0x3081603020406021507020f030a05190819050718030602300a09081303050d1101270c0503060702060a0c0e01080610090f0b090a08030309070605070f02040603200307 73
    0x580003034401700c46075030701d40d40d49907580310640c2c244d103040e25074000112035110000ba844503041c0d020380500380d0640d803a41d0f05800111020416281c40740e0450301908210f03d0340701c01c004d01c00d00d590046500811142440105400c241c0e03502107641a05802c151841600003482c512a074069040c6a43c0030b0743d5100d8004000b002820140021400241c240c4030125142c010510600038048203c1d90420b01181142c1e00304d507500c0c50b003c0c0c3c0b82c0301107140c01c10200f01140f0110000d16818003950028004c0c2400014902100400816040406000030703202039010650102d040d0720b0811801c1d02405094004114510b4041301c14410744150b0601502004513402000a459130483ca61513002041155000e40c00c000600c1e088414080c0f5a005070701d6112030f2000010080113003002041d0403101911403c070880d40355000030341e0381d20080d603444440d6800746e14100440d5105038007400e83c141c071a000c50f8039a840396030005020380b8101d400075505c20051004140701554080000c00481e58140c1c06044a54 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 614652095 1250 614650845 614650847
    0x60606030f04020907121a12070803040612021b0a02190510080403110d08100f150804020a0f09020414032b1116050301270f06090f03081603020406 65
    0x903010708024001c007031400201d945180600f04c0e844030304d40c203a101001001195030007950030502904c00c55000d2101c103108c049801001081e00760558440700c3c011403805140c898101c41090405000d40001c2d60700780003200c07102010103ea00c0d480c0c40721500804c40c2040c18010006450758911408007440c011004c10083c580b02d00c02c00706412565802d114405550b0707410152000c0c4212a0314000b580110340ca004076440d08040310900403104209a04401c544803c00900d14507054003446c01c03031100710f4400700501741c0b041c01099070051025080b0180300b6622600740d248000c1c290425a09180c01040521030550185090044004120000c052009004410043d440100455521000c1c150484c0c452003034002c0340c00810450345071088461a0b000700c110300750003040e1f0b401100d1281d401c010014090160318511121100e890389801c21202d81580c2c0c40341c2c2c1d200600901142d8650b00c4094400100740841003c102030303402a00c80c02c46618242414140070740a125155081c544188800c0c0021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 614653345 1250 614652095 614652121
    0x1707300608070303170c0d090c170a02030a0b0c090307140103110a1d060f04060203120a02040302030715032901030b01020609030706021e0c0d020705010201060605070b071403160206060603 83
    0x109040c203c88402c0391111b1104c00c03201c0c45001802e80b03003141464a208104900d800c07030b501c00c5402e542043d80f0380f000c80702d855940320362a5078030181d0b040e4084910f0380e0101d501c130591f0b02e811400c0350260928200120b40401e04000590f40303d15030001088041905c156058001d0f600f08010060070140f40201c940000340140c40c0421010319081d040071501803850300e915045581c0218030910568855640707071b00081d42ca40c80340594100d008c180002068010040e8002d64050341c1e0700030060111715051008415075010750310750b40000c041d1100f1030f504032030b001303101c41007400184248500e040126220015081e540447e450350304642c0320000b00641c40d6004410364842a84c0400d0150b91002c49010b4070418880c020030704031003001c000500540040000424508506984c1c082c1c42c042c1e0350341c100681c01c81309144a42804581c0c2040705070300240010501c0e6911400302d04140102c0c3e0380401d4403450386d4200300c914903a0429420180719080ba01003213629444581100c0c06032031490071000007409 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 614654595 1250 614653345 614653367
    0x9090408091311130b040302090c1c0f09290114010306081212010e0603060106081f06050924070210210f050c0a1707300608070303 58
    0x181401140c40051956480008202c9960002080c001594140d00d0185180d000311501d504e0184050790015003003d00406482c1100d80003000c0c0c456503914007402006551240424500b400c0354000d139031040f14070f64031904034801040240010030720321510300643c007055083c0c5500c100c02c0c01000d8034a101c0242c121682c0c15189038070300000340303c442d1000580140c03032950001c40a0b07008c0c280460f8440c00300f0350060850024408041075017a682e40a541108242c181c55054040d003083d00181700886c040c10640d504105444c84018444140c22004984200c554011900207400080c1703600c1d0b1443d016800d0015400444020310701c03982040c45013840c41c0300b12140240240784001c110741c1000c2c0aa50f130101c071841500010241c03801504840001000072094a04d0a11701d8a00491320307101030302e415920703983c1c025100c500e00902030580c144016000207049204003e441e028141d00f11001e82d0100c0f0000070340d4546c0b0802400620041010b581140d042018550301c510310400100f0f6000c040c40c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 614655845 1250 614654595 614654603
    0x6030b2203031d0703110103050c0a020604111206130b06100c0f020a0e070c0c0b0426100e0f010b04110307080c0f0f0901020106080d0c02040e0c0d05031e090904 71
    0xc6111220300314903600315012241c030f000750042d40301c0042406041c0030b4480606000340c0c1c1c10841030355603280b48040c0d8059851030a006901041c0018000b4039020340342c4101590003443d107040032081140040c904001240c41e21080c5400304451000c101c541d56545822000845040804040300742c1c000708407032462100604203103003414455095449641558014041e101101c000f03174030740740a0103800e0b5a10303500102c503c900c00e40c0b000100395174604c003a50140e5078002d4044800b90f912010480c0015104220460340340078a4000c00c04161040c0318001e8210389000c05003290000300c0f07000300e084460f640040740c0103c2c14040071854580f0b8071021240d00500c40d05040708591240047c000380d078007070912104d450b400000356040c038260b9101e001d072800c103d090b80284545522032280e03a4a4007140140100403444002d1342034010301e4039800000803404042d048070380c140034900014080c4484408141c0c0c56410009071001c00314407012001c1800c0c8040c02d507884c684880d00c0d02040e07050314001e02c090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 614657095 1250 614655845 614655851
    0xb0a05120a0524060f070f050c03060106120504140303010f030303052d0c12040c0510031406010309030203070209070519020d02060415091407060e09010803180607060e0106030b220303 81
    0x30569130b400c0d0685045d60404480706850315654588103004000c0001c05440c0c0e40b00e03401342d4041501d4009040c5043c1c404d9a51806e140e11201d0a0840140c0000743c811600c50102455044401100300f0103103000b084144070141c0b00c1451403d025003128409000c500582040402980100e0800407185c1801580381910140c1c40d56007240601035800380b60007080303105480c5020710050045c040c08420580c0d0003101d100f40c804200741c60540480c2d0a0000000c9030500c100d00080480d0301a604c6410000d000707006880c81c204095001501c08441112030801103903003c9241c0505001920000c1071610341070008014524070810007950728800200300401c80c0e807121104d84c14426440d0030400210350312a07100004a06003841d1241c58484e13501480002458180746a01c0ea8609100c5c01c50403180000041c505d07040312480b098108040380300206401400400c240400203010b1310452079001c2e0142c00021703156065150640031040060440c07607a10f036903c014584440390030f000746c140b019170500f000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 614658345 1250 614657095 614657161
    0x18010b070f050105010e0103030e040209010e120321010305010c0c0b0c0d020c010504140d0e1309030203040509190c0e01050318010e010905010b1002072d0b0a05120a05 74
    0x240700c05440000004089508010000440002c800c80041c1624401d446171550343c2d900c84103010407401040d64040c0001d94501c028071103428501c0030383d4403009100d000e69150020003071402c03000b0410800f49901821a40f4010018014203202c1c0c12524026880c1942141c4032541b600d420401c4003901d0b628484800044c410314010055040b84e541480701c00080c041482c00e802e10104078080640454445d01504001c2810640b140312500ca10850007454080c00e0b5802054040040119800c01c0341540320030013001c50030365200603034148212800d103418500c00070510b040e00281c0d1072050781e2505000c008860600681e07002070560341e211101d1301030f86100d040e401c5542805051090800307820380d446c0020300c10500c401034001c00010702c000c3d2100c1550442c1082c1c1280c1d01c4283d231255084541840b05901c0b0120703007036807801495200d14096041315a031900ca114071940e200071030352008554009121003034500c40c042a954030030001c220130032803031412070b041501c41c44000d40708d01076092643d020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 614659595 1250 614658345 614658353
    0x207171f050a02131503060f060f05073f030203100302040e010b040c05090a0b07030f0c0c0b03010e1510140a0309150e25060305090c030a030909060518010b07 70
    0x640d254040000c510503041c44c1d48500c2605c44403502d80391000020304051020039816000da00c228126240c580d1240300c0c1d82c0800130b003114281c0102204440501d0000343c88640440c8400c034102c0d5070b16503120410040b01c140e00d281000e41484014003024035005100704200050250885000c1b281c0603100410781010090050f401843c25020f0203901c28580400d401c281c80d40007020305180d0906445602070703581c0303512120882e40946a0000c0c00103882c0c440354454217200b0701c40307003418070300c41c800c024042603c0c2c12001581da0001d803c401241c80c010410440c1c0d4030f09000031511000b200340e0300e540403007035500320046c4040c2c1340e5100d15403244000154022541e20a40c002454030f42c000034203044440f00d400c10320303002d42220040000d040c800c0c55200b40c1100400b0030101d5100e0082d40200000c18035250007640035000083c00f240c5940078450203202c880d20144801d100a034429910100f02d2030070321807000704864098101501070207106c0d502030017005501c42c140c1c0c15200400740c000d4a4010600c1c4c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 614660845 1250 614659595 614659597
    0xc0f050f060a02090a0e0c040306110705070308301f17030c010c0906051227060105040507020304062007030210020610120f022407030207171f050a02 66
    0xd8410094070030a801c004000703034654094510b10000302d95000e00ba59903a54290b040c0c15003600c035605204020030040000584039400a94044008513886080c0000390715900c3c207000c0c0b150300c10786408200007480c82c12840b4110301090000340400800140b04035004002a00c0c0e10000c10402020102c02c0305036034050030700c0c00030344010091940d140fa14402030788007881c0c13a50807140c2c803521030f98207001c0b80718182c07405071180d441551b01c07a030354481c2000f40070080320302c1c008809049035081440c0301c00c9a042001440041c400000100802001d85524203001d010031540014560021504103100620140394030000013041c804641c444c02070305007a1004010300700007141e40000d50003000c0c540d80319090b58001c00d11a106083d5010048841541c8003800c03450b0381152103000b40403840000041c00180340044120316541044098000b04000b107102461b280d5001080642c05030340b10340c40400031441484501d250520b00d58025003010b80c01d0443c103012990b2062014024591120000303407816179240c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 614662095 1250 614660845 614660863
    0x9140105041a040f1811090702030309030a0c110d0f0b0906071202250b0910020406050405010f350a0b06092202040f0509180c01051c0203010305031c05070c0f05 71
    0x48244001041c00303107860512060f4021b603260003240360800081d0010b0020040c2c80c45507005001440c90540c034040100e0303110030900011140840054259143e035140c0050102c18244289104a154852414040c040c003000500d441a41e41c0704c0c5042000b8076902843d190101010b806015031121007450792031044207110b510802e502483c0c00008401c0c428048144e600840c000c00503951804402a0f0700400e034400ca0082001141040108000c9540f14114032440e1000d03a1401402000a90b54030b90f80c0106074080d85070061100740314500440c0c04480a8507000009080d0402c000640c0b4404503501d4003841c1000c0b07101d126509102c4e1109030a50b00050035000d0111400c5540c0c0b61103840c0100c19814074041c0c1400382401d400010b801c841e0070030728008141988001010352102e50401100c142d807100c5482c0c100b80704850104d005000300c40c00030710302841c030070401b56448c0d01c45500710186a60b41c80312110003190800e818402e0351600300c641c040380c90340c11003000d00301e040c80341c1400c2d4504140d0b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 614663345 1250 614662095 614662121
    0x61e040e04030c020111070e01050d060f050a0b030c061c020906040806270d09091a0402132d030b0406110a080601090522090f0c09140105041a040f 65
    0x140301000105980714400c0c40100c0d00c00d8880e0250101d00005042da10401c90055241d071003084001030001d4641200140501c511410000c103090f00000e1030107096503815900100301c5074030742004a08070700e000d210740f420040781031b1120307801c0c11900301402c00841a824645280c40b58006040e052a889000c2110051729498048505908080c03003445107040c555545480c8a049038241c00e940d144001c2543c2c00c3c044503944d40c900246080440c454020010903034445c00c3c46003100e144004a441311700240c0114111800590310483c5082c1108408580424840e9607460350b410000d500c45040c0c150710340a581c0c00546100c1c550780c90b442d11800a11500098950022001c5100e0030340960111180b032041070207996544116a440e014002e03514030720390000700c1061003003005d1085005103500003941d045c05480603040020441e250100641002d40144600c0354482c0907000500344540c0c60700d401802c003640d04104409a0b01c0141d500400b070164000e201d181c03141080c00d86540f1325080450f10f0861 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 614664595 1250 614663345 614663369
    0x20a02070302090f011d010e060108062209051605180601030609050405030705010608011a09091e061f23010c0203060a0c080a090302071e151d0f061e04 67
    0x800080c4c1800c48248103500d10718011641070082040080311090403510021444c02c003175142e0b00e0054030b4113030000340140e800080c03090551203003c4202d1213900100e61059000106080c090400506026201c5440c21083c0c20181040090f51140c000e048100c000d0642031055646a0030012009420640c1c00000300c2030030f00d0b01744014010040010304030544a04000c0201d59030300c50400d800e90b480441040071071310303121000d02c186051030200c3d40d03448200d45c42074804210300070a103090420640c0c2c0c0310344103c1d8044410001c2c10081207000340101c003507500c10078941c2c91410f21405c0f171400c00e80e0513824501d5042c01c9040c210b0390107681c0c8801010b6004003501d41d00d107418001d45004107556140e407030000d166030001c107144030b20758401c0c0e040490b01503004e810360034100b110a2441c0041300c0b086007421441c0c01d030000382038003105140d000310056a990b0203a40010b6049041031185d58400c030035100c0c6800708407242d100d0b40c0e80002c480040c0100380e4500740010781e40c0d100c10717554015030b40a2104040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 614665845 1250 614664595 614664601
    0x10f2102090306160504050415090f02091203040305030d020f0d1d011103040c0608041b060306030201080a140630031b07030302070e2e09050721020a0207030209 71
    0x14258001d01003865082c0c0c21201c2503641e0040001c401c0004408000100b07001700028003c83c102134000c900c081d400201d07104602076841c08210101c07018610b07100764442d40420101a14986807109103c0544072000460829083d80c0720f6507220f201c1c0036040d0311030b01d0740003c3e0103898116080550f2086418450100090030302c02c1e1940341c560700f00f0050000654a0184c1038000260000243c034029031300000b8464003141041c006075104100a0020380300484203425095001c05a22880c401070489039402042d42491840050913088015040200407800d20500300300c425582188681d104008883c11607110211103081e038140d0000c0700d02250701c40031b15050361030340b0130002008042d07504110f50341d1050784da00710803000c8d00c03842103010042c0107070020039080110303440030042c4642120b80303c00c131307401c1c54801720203002e0102da15110703038104140d6032200410001902c3e11401c0c1c0d00045d581401e103103036141c0030760901941641d41080b01d5003590102e420040c161003008240301456000d041290581 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 614667095 1250 614665845 614665907
    0xa0b04060302101701170312040503041a0406020606010c1a06060f0414090c040e07140412030309050d0206061804050a05120706110a05040302220f0b0102010615090302010f 76
    0x51414690384c010096060000a004501c01c04000800d0844102031414203405207454501d03c8c0010348103030340790300c000d000204010b10f0a60394440002d1100d100c040e03460340f404102074117045004280138140860144210f011420910740444001030021131041160f03240f100145040c01100c140080100e000f26000c2907a46030b1009500e0410801c0710304045541d40c0005101544c8075130300440f8001510007001c2260980114100b060300307452070007203c2c107142c0c40700306040340300e030150390142d000075102e003820303014000140511000001d032032025101c1803901501003400349224944043d0002094030005040c4403017488441941680002950507a0016600c071102c0c1e60842082550342618000c3c5404800c2c88000864003c04c005450380303801d01d451078003000b1901710301100740f9007030021000284025035414414541d81549a10001901c4240040020b00b10f8045801030200020b04094071003581e0f400403c0001243d5091804501c2801800c174100c669010200c601020040718102c481410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 614668345 1250 614667095 614667107
    0x1803031008060129160f0308010510030509061503150f16020307030914010e04090323070b0c03090325030f020d121503080f031803040b030a0b0406030210 68
    0x450710381c03089896503621603915184404522003020090200015200401003051001c0d00e1000e85904900d51000e06a48800c91401c195510450005031400300600551903c40201c5c01458618a01006a4645503506958030700016206030340c0d40103004e046401c10fa0301000141280d40d1a02c40d1034005007810804007a240784281c4100c0d80c0b05c01c041518001103072001003516400760b0584d40c2c2500c560301d08000f540c40b16288215490420108208265054441740a83c1004500c00e5440c03e044a200c50301104952040c0940c2d0b0010306002c00450010a040c91030090700250595482d680d6034a41c10840c51461140341c081080050180810715208082c07400d100207000c1c0a0b8440c980d41003401ca03002c988640d00c12141401140d5000c1c2c90b41015410383c1e0200100402c400c2c450720000352a03807181c13031040e0080c01284203603442c0003081001280d001a015200e21904e40011400e2500f0805400303480e0000905114225584a1980b40943d540307801540065030050b11204c01951100002004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 614669595 1250 614668345 614668349
    0x31d130b0109053a061b020c041a040507030e1005040213020a200717010209030f03040303090e1506030f10080729041e0303090f0308030103060518030310 68
    0xc50b072407400004260a201080400840c8203004909607420b44420520b5113450f648001108103990407140c50020301c040c41020400c0012202043d14181810b00c024030305820748034502c1c0250f0400c80010f0b0039441c000b59000300d50700c2c202d07070125943d51440011401003114000104142c403c0c0099452191071a1b40702c64003d9009983e4409800c6038003a0f580d00340d100b21303c0c83c80300042030003140c0c1510326107440d00740180e944004c09035458155199505404070400232540a45a50300080c0d110280c80e0410148184031a0500a1400c081c0b940c0c07805401a5030391311800b881c81c40030000140210440000306c3ca8404001884180c907405e0040f420420000c3c100d071000201c1f1069900810801c400040c41411503441c807001c8880103850081d0403101c0e035510808000305003400d110124170200d09400d807442402c24110010720f00c034a503040007801011184d0186000d8621f840060011079200d8085030306481e00480003080136160503511269041203100c4941503400080705004282422608441c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 614670845 1250 614669595 614669597
    0x2100216051f080613021c11090609040b01360801050f0f0c0c030d1d060621073c0503030a112a120c0f0405060d0b07210b030a031d130b01 61
    0x99510314400000691140364440c561000ac01e020300c860900d0141c006848201c03042c5400d50a800b100c8824410110703210b03d58445601c0c0203145c1d80040070074012298028030050009100d83e0900d1041c02040d0b500247c510f0440c240142e00281006114004454109500c00704980d945c0c84c03406000b400070000014012136101c0c2e801d4092005a0000888070f0048078000c0031980f07800400c007144260084000964907250141140000f20301070700d80400c80301e50304049800c551f40303540845608140c074140d00a610000e0051207041c4159180002510038207040350920402040e08a10303051310700300c0f5000c0c003008918140322502144201e940201121400b0903250703e80c0380803800c0003003500c48003144c005a40148442001041d0351401e03030400d40d0000000b508180a4400c10340343e051101504685407404180c0d609070140c41300b500c3c88075078910a12451400c1150050040020b42c03240c001c00d80140810460075401081020451183c82c40303828000e280003005040300308100d000d031800c416164 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 614672095 1250 614670845 614670851
    0x6070209090a08130609061d060310030b010f0306050c130e1b0315040c0306030b13020d0b010b071b06080406091e030e030706080105090a09060902100216051f080613021c 75
    0x228240107441d903000c0851907201940c844450308c4144203c9030801402120b01c0500d5440000100301c0c0700401ca4040c10086c403510a120f4110b091583c15108054a01031317003030404001150100203000417040a548080112000c152244138482803000203144194494060000500040080c607440c08036039004103072801c1c086a6501c000503812103100e807002504400011001484050300314600c603140c20300c001d110300410a1b06403210300d40b10000360440700c0314410005824092000d0700c294544a0310b007002420f240a800c11f035000307259540240004107803548440b0f441e0100710500035420346284c0c1c001250b03a403084441c10001d0001c400d01c090f240c000d0240100c0455054810100b0905031075000c1d00380741c400d40320000880000c04070b041e000e03140c0c80e40c0c6141020040c0c0d96283c002000d420303581d00810301c00d49844044110900c02ea8055441001c01e40d404403030b1407018020008245030503003495420b42e88c0e010045040e40039084000c01c4800d02c0000e4142540c0340c0b040d00b40300d24010740f000c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 614673345 1250 614672095 614672099
    0x30712080f100b0a03091703070801140d110f0d020301320f240312070b070207080607030218121e0102090a090b0d150501060e030a0206070209090a08130609 69
    0x2d82140103000b1520303c1d800c10011407800c2406604100b600c0c40c403070402d00005c80301440d40090a500191403450001d01d120004100404200d852064460421100400407107250b90b2048016140b504038240586c4030b88003103540d5940d483e0303a040309450b0040e000380650600010180c100c01c40029040608014200440c003c5044402600b80f16a4040d88520b60949450340c0040501d241c81c201100741860705c0e2124500c1c1d86052049402d000c102003155511041e0500c0c1134612440000c150104550155404100c0f1110000e100c517005071290500503038818444018800c144445d0507007d420109000240001c4140041e000018414a21418410031540c41c00c1d2420303032091400ca0356000c0fa05a600b030000004951064a084034018109600c900d21a9140d054134a01042c008643c1a039031302c0104040c0743c002030003500300704084014000c15256540000d00c540580c09010f0300919444e03000400050041244904a0760401d400d00c0d21204840074040507a9080c0c010b00b00012a000c1c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 614674595 1250 614673345 614673361
    0xc0d05040510080f0c09030f070e0703060803070c0b09060f0301180b09070c021504080a200301021303060507111f110309061501090f08060a11070b07080702030712080f 74
    0x40e0340d015071311640c005411512071200c41411508443d8016506010710040f0343d11444d0104459001408102c03624001817900002c00b80485000c2d80c41100903800c20042000010159405407082c1c4018a040c00d4480d03034404046419400b968400d046250070010011450305031101450707031520340e00d000c00d000c3d0000c400240310345a002640c4801c0030805a248140041c07504184903080b002e500800b013400c26a032003a84501d440c602c10b030305562a00306581812054042c43c10f5035610044150006e40c5480760001d4a011707094001d10020b0b00c1955520b000c2412544181103112152030603070704954904803020401d1445002002d03104240a1500c00a01c503884081000d50b41f003404150301401c266038130b0524202d140c0c030700b02e12403904002241c8808a24604154402405440100002e0400b440c2c00c061700800c03500780121900106100b071040f000019030715541c00c1d501000c589007801850311050b4041e8a9070246240040ca1450149060f001e40c0703038041c01852207041400d40780b51081e1a9841 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 614675845 1250 614674595 614674607
    0x605030706050a0e06071a09060f090a0206070f020a03141504021503060d1410110f04030201050a0201200c010c0f050d0908040b04060906110706020709110c0d05040510 74
    0x210309000700300140690f10305280107215400b070440000e02214a005030a9880884c0920001804140283c0001c184000d230003007000442d6205082c58a65030440c00e200d54141d41c1c0d40041d0304024482c00d40010742c4810400b40702c468603e410740c00b60100800c5074583c80c10700107130501c03030040000301d2099840e0f210701c0420078407025008903009001174106da54002e0b0346d480303c3e60009100329040304090180500149960350a8200c105440014149419074040071106650154a031101035200c1404041c07040d0f9208011503040747d41c2424090307910030b000e110980c090120090140d16007100794054101e042e65801c001d001ca41c01d1080208040440c001c0150f07010081450613800241041c060900e290340c89a0210343c895024411f1035060545e507004802c0f05074403d030400c2c40000d410703603010000342d07800c841c100320601c1341e5501605c00319041001c001e6580a6910840c40ca10351500d080340c00e004a45411618842e80034416100c584e000d41d1000742280e403041c4500360190460694000005200f80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 614677095 1250 614675845 614675849
    0x507020f0c060304080d02070507140a0501020c060405041e0f0c09060f0903080a020a05030c07090525050310030204020a0306080d0c11040203070512070e03100212070c11040612020406050307 84
    0x500c100c0c01e44d1101d407188600c5d900038400310101c0607402c100560214008004810040c4030f880c51b0040400c07051404d000a0440035403000c1c0c1554072150802c0c1c910b94405060b01c0503501700380e03400102001c84000d40818081d034443d80d03801591070500000155455034000307901112058407081d0b08143d461008941c0100600034000004c0c100040500c00074a400c0000d004624151040b1030447e40340351229800c542c030074008a1a2580400e40820540d0b56a0085a500130310b0f0070ba0000c0c91080e0901c00c43c46014100301000c0c1009000400142e29080c0801c41c44095a00a041191a0520140003400402c0e4134016200207118801425088a1103108600000c3d07902156010a00c1e500c2d105200103900040d1109041c49400d200501d100000c000c5814822466a40da131082080a60300307060070580c2108000245500421851500c100c0400355942c11140c1450b00311071030003080c14445c50200c4411141c0d40c0c000e060050002e0542400303104081264001c071001c025542d610810180d480d841c1d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 614678345 1250 614677095 614677099
    0x1020d05040e072312010503011406031009063305030d02030d020f040308220b12070c020f09270c09130c050d08070308151e040207150507020f0c 64
    0x50350010f85000d10400c42c02144001920540300c01201107481d500c1c1c0303034011a40803469007841400412961809000311240c8201a0b40b0404407030511002181c0c47d10040c01c240e4013030365110f40b044020805c20b980a803114a05495604001c80d07540745031200301d21102042c4a40e49a05080081994640450024042c0d01150015450880313242c0e5007901035040340440345c90401051000201255004000f0301034000e100708480b90302074204139440840413683e000150f91120038403024601c040c1058030141c00c4000c03820101045a081c5c80024031540c6000310054000707401c1d4003070140201003100c108011b11400c154213011000d108805641d02c4006000c2c80b036000300c0741c0011030314804c48149a1108607000d0040814040d0311100450041089081c0465030ba9400007005420b0507842078210b0703040300030080d01d24981488540011108201124a00007100500c00c0c2d003a020f581d50390443e2226540200746e261762070114515071005010440d909400740c05a000184441071f00450b240700b0034140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 614679595 1250 614678345 614678369
    0x4150c020f0303010614090a120b07052704020706090b0114030609060109050709090207110a0618260a05150702060405070e0712090506060f04020a0c061503021e01020d0504 76
    0x80c20000300e40314a80352540c06d0f10034030300b008100e4080e12010a84c0c00504111210089500310310f242c40e81e1902001801501008810300808060741c290541c0d0214040300f00704241070100e24200014028845c0b0f4070700408261900e406403040060155249040300c0456103515074100581e801d15880b150200d0301803503a0b070071100051201e60750581c03009070801201d16081c00920b80752a4010100e0303020480c1600c0302100c051041000c0d103060101e40000e170074145401352107040c0010703164040b01000d000d1405040035003400000300d450303c030f80e10540492071501259403251030380c10460f8481b91401d0703020a000c0c507c20001441c26000007003a5000c1d541c810000c24070981303421402a0f4502000d030051341003010b070001e603e1000301c00e4081c1a00d454000e1024140c103080040421280401ca03803402400340b80144541840c0941003128002c96640010001c81d01070140441c0307003901039a640000703510240c0300401c1c0461892081c07410304201c0703003a021102940112101901c9074000c80c40b80007000f00b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 614680845 1250 614679595 614679599
    0x706030b1c03270f090209100305040501020f0409020301090609050618040305270405012301210603080a0314010f12030309080a0c0606090203100e180604150c020f030301 75
    0xd001016200c1c154000c0c684402c030284602001c0f00c03043d110740829030b01854108001d1091269503020000102035a0104502c1e00c2c0640d03002c903401c004c0750a540c009165a81e40080c050107030070340464411005460056940d03545602c400c0c8000d42081c02140c40245c075002c0013007000101071207114001d040041050120041d441101c1090302c0e0000c0085040090034040b88030b0300114105001d207100d82480c0c007034100f0030251081c00200c50059005c03020010307441c4d50300400d4150071852040c54100031b180403810303450b04908801c031029806003850881c514241c0c001060001c204050202c0d802540d400740100102c54084140b00c00081c000d0040000e000e040c1000000703c450440103034248a4100411103859948900070107030003513004500031801022452041000c5441b540e8054603440100314118103100c0940307000c1119a0043c1a56100c040c004038a03186c0e001c2c4001c61207107c40d1021103000c0d1900d440d00c940151a54036000000c80d04254074064a02e0012a400043e0484000114103580c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 614682095 1250 614680845 614680879
    0x30608030a0e1e09070509010f020d050a0516050a080403020310050c03070c02030a051b0f06040b0415110712060f0c08070806040b18040201080c16020607020f0d03110706030b 77
    0x101c3e001c004101400269240d8403050300c1c2c2c00a0107100d070605884481c3c651007130800241c04107410140300d8007190089403000c00c000390010161100c0d8485031421903129a1214007404c0d200d90001000740062044494410420424100900980c1e01c29400d0700d6402041c00c00c42000d68100340c07404104110f042c000141d1082c0b203180009c1c14035000408648038030748a13484083c20204c003040c0d615043d078031001c0094054203040101e1a91020b05541d0741c1e10303091a1209240250055014420250440b01c0344a40b9a0784109400c1640031901c0c800d580c541a51260415024610420200ea49a041c0040d2044d80802071148013116840c2d034450000b0ba030749640d0122680c1400404d820781c40356460342039246940350f01c01801820000c41c50304408904041c0000341680c0e800420200a405041004000d00303023545e13842551556041e00c03a50f0b200c449170710015095192655a541e00325034001502803c1c0b65001100c98194180003003031300c9007140c41ea20110b0903110800603540e046a140241c01d1514 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 614683345 1250 614682095 614682109
    0xf081005090c0715052a0318150f07080a180209180307050601031a06030a080a211b0306050f120c091608100518041106041203030608030a0e 62
    0x32a03081c881c2e070318110865440f22038100300042d900740390710342d250100640c45060640d4092104107681894506428100030322140740b200410b4003104000b401c1c030403184400204072800f00e0740d95426507952940307030103010a184e041301120403100068001340420b00045180c0304d0403202c8442c0303000c0c40000300c03081e07000d020400c100506031700e441c28042035080380440e5040c006400c825110313a01429095145050242d000101d41940540307460f611000d00c03a142da0001042e03603a04c0d078444482c0b916900038120a80e01420a65502e41c12010b13007805c901d04c4c6842030b40c014a03039504044003804c6a040e80b00821070484903135010b25a00250118054079491400220854520701c52500b254124101d65020400e192026240072080c0b18500300d0488046400407011030344600319048003000145041e0006507003040c1d480d959100603071040080780c01c0c010300b503071b40300103249002e05155912a0b554a0300103803404040000d40008c0d01e8034401003840728001c421035404d403140303540d1441c2e00380840c0304001070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 614684595 1250 614683345 614683351
    0x403032a1d03030a12050114030613050109051c0f32041508041e05070302060a03020c1203090f03090a03020105090d0b10140f1e0102011d010c0f08100509 68
    0x1205180307950300d542d64003003008203940c2c4a981c0e00c119041498000050584406800c000da643c4203204191019440000d20546c1c0114544029a4440c3d80e0703041c094014980784002402c1b60013201c07142d40070306041100d42100c480d17841c0c5d100f00c071030701340070800b19161200c140040e01140d600740c00181e4064000c0c049500182da480380e8440c5091341c1c80d80c0288582d4142030100300410b40761410402030119240f611600000380c1c0e40c0c0c24103403080c10703502e19407214110b0100030300c5000041203d5910902c2581902c00c0001c00038207c620b40340520011044540044a08052911614480e001890800f0080d9007500e135010301040c10850840d03005450a420140c500c50308200c8009611020501401041c1d0284800d03643d0303541020306110440c200040c1900c002c9004418500c41d010bc1d6450307034099880c8120710000401c90056140300100d025010f00040051240101c180c640f00e000c0040d03206010f02c98640c2c54821102d106150b0036640e24908071640342c0002c043c040d041009051182003a54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 614685845 1250 614684595 614684627
    0x4021e0109180c180602071a040503010e011a01050702030c0d05010207240f1107020108060f03010908090f04140103080c030409110c010c03060f180b06030f0403032a 73
    0x50a803a02d034001041c0d85202c207a10511034440452a003016007011200480c1c40c0d1000504100c2814034002030760b02da2280c854801182d04583c9825084d40814003030340c01815001700240440045d01d140c0038003800c80120950341d00650815a0415580284100d640c00d5601601900030b4107004010080b910f80d00020030313038072950204006800205c03281100c22282000c0b0050a80c1c650120751441d00300e8188007900d1003110b1034245512943c2400d0700907100100c0d424a0200d000795902000303e88444045808250598202821401042500000760180c0305e0151071340c1d50014044810081511710006041c0c61389103c440041c0003280140e001084840740c441e080703915241e550718049007151345400c9240d00203180441e9403221103d0a003d0034100004602d02444141c1c00d000c6c0c03108040b15584030340741c2d00700e0030b9180c01012082242c020303a16612004004589070300c5c1040c03110312540e10490301200024501186081c22009802116844800301c2c0c24440d042141040b0a8500840760720b1648 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 614687095 1250 614685845 614685857
    0x30b1c02010806030a020d120e0405070905060c0f0f0703062739091505130b01030f110309102c16090e1204031205130b0424050304021e01 61
    0x5c05601c807e03601000d454480d2001b0840c103060400d00070984009840f10a00c81d0703041c08180044194842c07900307001e40324200d403010755421785828001d10b0100c44003039003d058001c51600352034001e0041036802c2120b01034401800410280340488009111003210180302000e040000300125920003080035004410390144120340000e01041099040321180e40e01d4003604548060041c40c82a0064800750903004c450083e5450400001600d1500004003d00c222039988400b84420b81c800d8000340328030500f5102c20843c02c00c00d403009009540c021954400e4030b01c120021520300c800705105918142c665280b0686500810095151a0001070004080280b1460f041c01f01c2a50700c980e040c000501d252500010740d0240b1170191810000b10100402c030114007440100302080e91340d0402c0c404883c0e140743c81c3d5656180c9030307051118459140c104408104005c10041a505001c040c0442d0040c0c034240c2c04895165805811a298481140c00a400100c881c00c0540704400400c0c007070300100c005040c04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 614688345 1250 614687095 614687113
    0x206030406050717190c020c0907050a030204090e0d020705010908070b070c15020c030c040e1e030c03041401031125060204080307050105041112061902070210030c030b1c0201080603 80
    0x150310544005e40e02a41c94001840080c00b50196920850301c038149240050502075441000103030309208000c00040520074002220807903144240c1c11900500401c072810050f503080d800304991703207195446e5004050b2180c031601144640c0560368071001c0350711090084c140e040c01d004451003550840030084510782081003012a0142d00004120701c02e40050380100b03155030a000c2094030f08450303001d206029528244404c0301e640c90110310486980401c100502080b2081d030307a00740c036510844600c401940408640490b40d0380e43d101c00d11104032000d81e0144a112140007a45c502e900c11882c04031091182c4403000000d50591140244020380584801820035544481490443c0d00c10001161540d45d600204004c00c03c080144a00c880c0f0282e503403044866418003030b00d981c0e80c0c0180030700c10500c840d00c00300b0703003011080d4046a802580c013074405a0341078040400913002e0700c9a00a800d01107401c0c103019400c075062581004003812070668100720000c00c66001501c1e0050701070299a003501815040d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 614689595 1250 614688345 614688377
    0x305100b03031b0303190b010905010c0c0306090b07030e0c01052502040c051b07060e0607050106082d06071d010201180b041a0f01061b02100f0905060702060304060507 74
    0x107100d11030f00c40c02d400340d5920300c1d2008540c02190030070102d07900f89515081c00060140d90140c442400d4402c00c2c24940303250b814a04040701140901d502c0104203c1c201028002004403145103d0b0051140341c80c140510301c10f60709240d4496000482c40d0f0f0015209002e000d42c40c00240c0900c0f003e0b00c10711105841d0250f501c0e0082400c1d50340d01c0d01104040341c0002030114200c8141c034a03030048007014602424605090000082c00c0d0744c12100483d204010108002d01881400c0d4030103402010600c04a85000c182c20300e8241212203040c0021040300c0d0031085002c0c10f984003081c401c1c410641550307070a0204400c007020345400d04c00a0180783c119982c40410307900c0c00c822031311440c00c0c1130300174440c0e0903544ca81450205621981c03008181e800c8203031007082c041c82e9442002241d05440c090f04042210012003510102c9030710649034060740c04160400188103580c2c0007502a0043d42040d42c030000400c1d00c03442880414032461000a4001c41c1c100000350204041340e01054001c052031034041c0c014184944 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 614690845 1250 614689595 614689627
    0x50106052707141e0306120106030c14030708010c030c11010e060412090e0c25080301090b0612070305010305012301150504080706020c03060a0506060a0c02130204120c0603060305100b0303 83
    0x288105001c003000043c402c640c40c0c64140c1f15400c80240d8000e00240382141e484901c0c2014612a80c1595030103c98028a40e0798203000c880e0103001084003c001503507034100000c018000b60302c95040030800080804000101c10300034a072480c44000010070981e11a80e90300e1001c03647d68820701c0c0800076010710100f05000c14080e15070090381201c020f1511500400100303c401118141040038120201e6424800102450705507811607001800000d14070141c1c03004103005104441c500c0060745500b504004c2201d030194001380c1600d001e54000c02c1112000d00010103103c841d6898281210701c54001040050814164403c9012161821904042d0358a2181740382074606c0e040600940c10050f64800301c0d003030800c152030b48009400f1060000341024004142e081c401d040c0d1803402c01400c1000e10041d5118020480452480c007642150b881d507403044843c003a0b000107a0100c0da50f2035903100c00500144030380600300543c0d400030040c050074490761600310002d00345c5d038162a0301030100380010300382c41e0304480c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 614692095 1250 614690845 614690887
    0xf010f0201060522050c031618120b0a150803180a030c08100f0209011e0212030a1a09090601052b0605090d020d0f03090201090503060405010605270714 67
    0x20414210580c50341302c244203440d002000e40038614814001c105160103d205009041031050400c81c3c0d540a9501001150a255420041542e11901111000c02c10311881086c0f187c18100d10800c41102c03030701c80c500c2e040180b9110b041c41a520034089406002980d044145400c0b1000305441045031f81d0360740d6060055807640c056000e541020701d4420910256011384400001c0c000c000b103241101040c0080d080b00003280048038444100700000312014000c11422841c0054541216160700c0d15480d40300c080c00510081c043d085600d07103079400b1107003031140d40d0901a10340e16014103020f070709040034810542040544602c951a100c9180d4110240ca9055206101e0051001260a182c00130300549401d1b078403101c1b0411540920611001c5c2c9038002000c11010300b252801050700c1c511400126102030694108a505014034028001000030551180c011a039003941e1aa00d21400520036400514100480b4807050070801c001034441c502c11014010b5007688100041d00340700922041c1c1c0c030030356a45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 614693345 1250 614692095 614692129
    0x204170307050d03050403050403030f0e12030a1d0f09131718030d0c0b0612010f050103020a0b071101050318030a08060a09021806210c0d05010905060f010f02010605 73
    0x2260001c0c408144201a10200f030780c2001e008a050a41d40241140300782d1001404000d48406074000151048003e051010001040c07610003134940000a503c0c0c0e03014400e06008210307600c08200c0722008252940c0301c098030040410b24401908000d00038040380042545143e803004110900016218923280800d6200c40c040050321030103428010701ca40100b0100d81e1784282d0040c0c5c00030b20100da10034900c6c22450792202c17400340d0986403840810032110388604018019401e02000021241b0f85a100f1812a402100c5c210240c5546403d000207030301c02e03410098405600440c80380d0761540203800440c0c0102c480d0001c0a84152034801e03160550b0000b4089900050b05d41382401360914001c00090041d100c05441107140c2403512115030141140b01d52003600961303020511020300c5600d0790305580555030a18249040d850060080e43c40d9030300c0b030030f8a165091b241c6800403d062000740300c1c403481000d002c1c0c21607540e408800015180008000b0440c0115921743d2000710700383d111060010780007904 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 614694595 1250 614693345 614693347
    0xa05041a1206120616181d0c0f0f090d02150901020709151707170304060807020313050103150302270919120201060305011b0e0a06050405120102041703 67
    0x41c8400d80340400304003402040c4a042030400c1d1500d080d4010500a400076111a00030612038003a20307044c2c42c60110b0302440d204082404d0000140980300c00c1d10040002c3c2e841b80c000c0050758036000302c007031140662001004410780600545414100400c001c1044e580014140089605c0944c002924600e4a4141c001004130102d002801c550f010001000604003040043c000100641310840210342030348110b8403011a10707100505090001c1c00164007606011811601001030a0b8080d980e0741c0c0184501e000094040000070140b40c0701009440c0060f130742150a0340d0f02440d1400440281901c0116903040d09074600300000141da41d51141c02d40d15401940d6489081d034804c10348500120000c10f02111900820b44a030349045100c3c1d440c000141c0c0c00305005141d10140b00c000c03401406142c00c000c26940c40d04031300014280e00e11007001030318651652800716800d014414800680b20030711500700410300900081c0142d103810841341025038041c0000601b41075460940c0404403106189180407900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 614695845 1250 614694595 614694607
    0x6040b042004050112021806012a150c0f09030305070b06010e0d0308090c24070503220f08011401061b02060d05060f0d0f080a1e0e0a140a03080a05041a 67
    0x10000050081f80300050a00300083c60f0440000e021901e40c3d407403041e020742410010030031200c201c0c2548030a654001034860303000d00100c5c0c4801c3c02046000710703850204242200c07906910f0300c10a1460156175040d90740700c0c10404155a184a01540940302c42e05000c0501c0c2c1c0041c19464500100d00d505000c0c0c0c0c0c0e1500715007031602d501400c110840210341c0c01074600d019140d00e803202c1486692502d580350b00c10315a44403801c0c01c00d10709500400c400058040c2e01894010313071440442e1000000d88030440020154580d071203076401d080f01c0301f080b42e22001c000000010440540500107030300100140000300500c91426a000585035403040700d02d080d0350380c1d450003031203601e0904d070715801c40800098500545822058850032207040101350014400c00000a6602d000c611071209105105040c8030399000501d400c44001c0c1405842e981c0d00f40c0900400311001820b601d081c01004030b588000f50003040302504581341e0405503030000142006020040100040352642d201d0030142d40740c406800b103a1164 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 614697095 1250 614695845 614695849
    0xa081c060806100e07020a0f080309032205090f040308040b060f0a0603061a161b0f030807060506031612060e0303090f0106060c330204080a050c0306040b04200405011202 75
    0x400282c1120215841f0b040f4002c0020075185102c5076031030b080700c0c0c0c00d41c60355581034002e45940700320300c9101484d48081d414503c5604081903c40c0c02e481048031641403035503800954441d110811100940000c5050740070601280c2260550303508a0805481c0c3c8020321407000c0412900e0800342e0003180025607950301040000a09003120441050002c06107181200142090301c240148aa010301118100c48003440464121342c01c1500500080500b141c0da42d540f0b04019200350081802a030706a400c10000403028900070408518a1030030f8404c017417a20307007404c4508800076501007084800a13600c500342c41c1c82c0c0900300003440c81039045500800d0302c0a04509001c2c00c3d00c2c0c1a41c0030005102c404011800000d100e00903a103001c0c40c10144040500c50140420500301c0124080b501d4078900c001004640000d01040c1680224028811140c0d0b51038408207240e0b41d190222406002c0724040d50101d0b00140b080c0390307007a440d41d1020341c8840541050100103001c030743c0d00ba0b2100a1140c5000f044500314 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 614698345 1250 614697095 614697119
    0xf0c0905010e060405030d180909080a0201050f09210c01242c060f0a0605041d04170901050c01060e061f080a0e100513050606030a081c06080610 64
    0x20b0542074920b070781880c0c60500030a0792090166070900034020510030003030a90101081e014005c2541e03400070f1060000c0390030f09602c070741d0020381d0310b20040d42094001442800c407050120300407004100208010340d00c100d640e1050314404d100300300d6007803810403c0b1458180709010b5018100c41070000032406001001040906020342d40c0040d024400c5e51040000510b80f00d40b500c4240c40526440c50312503030303500001415403106420741980c01955a500469059804809041071ba501044401c01d15000c7d945221112901204c00508080b007a41803007950540001c050141508103040c10740c1800002041103080d80c400c2e0f00050824000d030030400a080c070f4a40c0e00c0405000381201000c0c0046002000144400c1004000403507894803001454640101040b10000743e4162050811140c10046404001c00300d0760702c4140d400d48181c101003461442c0106a0210441d030103511507180c40385481d58100701071200c5280f00c10043c2c1e186e00c0061500b070b0a10405200b03440c101004280a81481070045103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 614699595 1250 614698345 614698367
    0x30c0d1b0e090903030a05060d080c011b0c021e2704150b030a021002120a0206010f0b030c041710020406020c01030f0605150304170703090806060316090e010f0c090501 74
    0x202c2c5a003481800340285010084036008100007401048590700e040200d4448402118018404500021501c1c400d030410b505c1520315209450702460700361a48002240d16404804010b9800021055094000880f500d4403240c80e06024005c158168015100f04100000740700b180d03640818002c04020401c02509408117110080c400f080150a241c080820b50f00c80c1503800c000d000720000035130083e406008000310b41140321405060341d9a60b0292070002d445e03100030b1142c24a40300c0c0ba25408a8104040c500f564410750346260030b44d052902d0f05100e00180d800444a561301c0340a40e50803410303940342d0381c00107002400ba10340041209854100c0018100c4504106d4ac500c44c0c0d141540500ca0b81da54105032140c00110103012545035295800d144818101d20740c020405001d00190b0310080580109008045a1400c010b0340c2c0195075072002d0648545650b14426080e141c1e46206005841d030340d80c8262a031441d0b100c00001e140c907a241c0110101e950405110021803c80d03c0204400c1d80c0c00901c4c810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 614700845 1250 614699595 614699599
    0xf06061c150908042705011508040c0b0304032601080606040911042a230a02010f1415030a0803060d030c05060c1e1e030c0d1b0e 57
    0x40c40c0e42400c5200010401020003064188995070501038107005411055086410119450b0ba0340d075a020980300000c0e2100245002000c00c0c10b40701d58441951003500c0c101c540e80d01303100f04140302c000340446030520b000300300b101c055036644070104007106044099417143d8444d0b00c94925840891a40241400001ca00d804505920b0030051004685c0454041d810080035100400c0c0b102192403c0512112201003445c0c00c0303494a40c1854004040e980d4452981030460404501540c5c10f0703104480054214002807030400c0d4030042d441c40d40c0b0000f0010000d00308c1c140b000081c00b0034040c1041094902c400034002841761283c0a0103008807a6480780310b0381d88000c40c000c0044900319a21101c05000050905108101640900062601804001d04c500d80d01c003003130f0b5a0614000601c520b59070404220741a202540f404103001040b601412900d6400721003005140c4049211400c40031503100412403880c9240c2171200703900060140c00345240b507413900c4a45100c0c031995842c0c001d0851000d160194 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 614702095 1250 614700845 614700859
    0x906090902010212090117040c260706120609051f0b0918041b03050610090b13271110020a0b0c0903031b010c1403090318130204080f0606 61
    0x1030040c0e030001104020324800212042e03d07184c41100681d540a2142803a12007081d043c1e00b044100840c002444060701c00035030900c40030840580b0003040011088100ba00e207640048401e100d610700503101038010408c03215011402e0f5442d42c119070103550781510803a41c90080540d0880c01d0035640400764010f00f07000c90005050070030f000700042c2c0442641d200d044803040820301140c00e01035401d43c0c1c0d00c41c0040713901800c406580d80785012961400221140c0c1880c028000c00803802031001c0c020910b01201c000e207070b00b18184480c61000300504a4807080c007010402010144648a518142142400d0040e07081c41d000c03400c1e5100341300003a07030718180c22811904284042030000b01c407507030190780104170100c541c0e44600c0b9980100c0d241d4424075204030a0030103814000b4001100c15002500c3c042c400d55148240d00c40e50411440440c041550200415042840491240d00f014004100c04940c0140315180004200c4182c400b00d03802904003d0458000c0c070788450f405075081140701d4100f94151103034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 614703345 1250 614702095 614702111
    0xe0c010518011206080a050a031403060d0213060801332601060f0f090c022802010c08070605090d0e100c030e041a040e060f1f180501090609 62
    0x12146036242511031414410f00c042400e21003200c651142020b01402e50031645407a106052050303850040e034104900003411040c8541648011005403809550301420300060b4107010750800881000f4903004000280d580d2400043e005024004c002d00f1030b09070f0f440034010250b030204514500741602d0048804c00340c04481002011000072180180340304155907445101d400380325080c050000e642c80740c50070010003080803d1700b080d180220011a19161020010410940d03001d07a00c454041d0070412110f45400c3c020301c00882e00300c210441e000c3c4145001000380700300e651103003200d802c0114240d505950b100100705c2c0b10101008480030742c1031942070203030401504100007503065032001e07241410046550300900815014000446064000610a2010400d6400001c0f0102810b0b11064412400c00c2641d200b00d48020030500d0058100000f20301855480d08c10050305008501e0450480d0f80c11034a001440b0a030b40e02500310310516024001c142545400c46003070030341d21070790000c0641905c0e042d24 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 614704595 1250 614703345 614703367
    0x3061b03140105060f070b2401180b0306030a0b130201020c1e010f0905060c010e39010e03120c070608090319020705030307050109051203280f09060e0c0105 69
    0x141d030304491044036503d42e10b003016082071105000304c0c54014600c000480c184110810340316080380c2d19071510848614100040310044424410006000101200040090000c01100320080d54090800f50031a08101034035910000548412211040520101c41181c0115a0306100d1a03041030701c2141c6040700d01e40d40c1c04030090102c2404c0c0c01ca9043c02030072529404828000c46078034004000083c00141c40c0c07071009040c54041c00e5070030048001402060b08999a07038009000480f1f0032030030200c01207070960258086030005c910380d0640f42e041c803021041710032407550100300e003440e02c2c807604401a4540c0e04d4560003620b03010094000205024504040002c5698004203940b42d10310040f45aa110300340148050741440e10981000d0b416000001b5403205104d01500702e02c8a46101c0e1044a456030140174088409000076160065541325050f00c5a00808503042111072903420381100140f001c95409c506c1c0f007180c6040d0401c941c070507280e00340180100d00038441002ea100c0e084c05e00c0d51810f0107280c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 614705845 1250 614704595 614704631
    0x40315020c15070c0b01061809050705070206090f0316172406120d0314060a12261303140109020a051504030c0303030b090c0406080708070c0c03061b03 67
    0x4080c1442a08490020304104d104414403140070342c00013102191541c56100082210702600c1015514458030300c0001481e010a01c0350600c00e13411541c1c0c041c14080306030300304000c5a0000240517400800c1c40c00c2480c56071b4052001c8031416040110504010303240000e41d480003007014141803065004600603502c00c8601144c01c11242d007035410000b19036502d0000144500408002a000510031094410110b07070701a80b01c18000c202c07030042e960260f0380b454200200101c440c0203101c060015580001d00140a00405400310344c04140b58150300714900900d2801c0e500001441c00b0800f112140800500c2543c150703003900307035030580d0090046009035004968070a400344a000d00901c440351144c2e400c040202d041d07402071640000d403841078030780d00d080003001b8000070742c038162103001e0040c089440505d42004031303000c543d01c41e2210103250750303454410b07118007100800550600800016030300002d02d0501441d400303180318040010b82d28a02c074402c6100d0030201c540002c00d040ca0b0420311034141648807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 614707095 1250 614705845 614705863
    0x1e1b07060806152a01051f030512130e1501111518030f0d0506040c210b01030e01021209010f060f090506120615150f0a03090323040315020c 62
    0x5030200d603120100100603100300c13400c0b2098540351000c450328031291401074200c14018681e072000728694004c14600d41c4050072807444000e10b650b000d00c8458034031101c0700000d4005e640180320109861070340e0b45070510008408458094541e100038a9540b00356170041c0342104c0b400386550040c01d000d0005a2404440c16018180302c0c2c10251289880c002c0b02d00c100215924100d280030125294407004841d03034081c04098a00c40c2c880c2e401c081420741860b108a000102d41c0c90240c01071a007103490a50000b0040004040107810186c44078440644410f090000703240c1c11000383e210a105240c80080f042c00c40d0300b4054090003da08004080084600c800d8540058070784050300003480703844075000148040000450b049007806040200b10340d0743c80120b0765442c1d140041c1d407103083e101441c0040c116544102003a11040083c14055400481d129a20104900c0d1080c00c00b541c0c0b11901d56a030481d034020507070303003500e88440008007801085000c56600300b2248880000390300348101024040e8440c41d00c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 614708345 1250 614707095 614707129
    0x30c23030d09051f050a0f050c07060e0109080c0d020c0103020a0c0b1f0b190f0903110a030b0a2009030d050a03060b0f030a0c08010608010b1e1b07060806 68
    0x1c1184805002c414004009041c1d001c0540c4948540d89103100c5010702000c5815001031361a01d944194211000d00032140301d8020a035041d46403d0442d5281002480104933a101540d40c440c4a580000c01e000f00400c0e81c082800000c00061100350002864000026030040c1058014440c0545a80d00001c03a024400e501c110020302c580d41e01c07030b1a00610346002840001074450903900156022a00c001000700c01a1038500601428000c8002d82c0c140e00f4051030280015010a801c102044d800c07403840908000040188808683d07940320272802c91400e44810035820303580e40150418150084160303280010b0306158a08011a00000a456061250100c81404000210480158400e62005000e800c40001c060380743e540c030051689090300b080300e4030140d1a01c2c0000c0164124019524281200d2841e501d070b483d681c0c2401035101083d0495a1428426072131042d044030300d9245075003e0f0074040b910800003c05807880c2c0c17040901d03040f4194000000d08c0194020300c01603032505500b96540d0003107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 614709595 1250 614708345 614708351
    0xa0905061602010b0a09090201020609030f0f0f07050f0c031504020d0b09070803040303030c0801050418020f030c040603113c210a021f120e0703050a030c23030d 71
    0x103001d050b4054501c601c2031035448910b07010081840341407540001140d5000b80e084900760394588040607607a12330200540504101482a10001c2d441d2074028420202c0c07003004c450900355a030342e4184c6401d800c0304812405400580a00c09241001c004043c2007070000d40070a2500c0c00e00384c010800078030905402400e202801c0000a140041c104140002040c111044907a01d60741c2c1e040040042442c0e815810004013500c1c00000c1c40d2402c0e00440b08940003800322011004182d0b400c0110b0000210f841b00c2e00343c01030000c00c501d281d0303d40c8034036401940140ca8403028905c0c000b0402076803070f15100c1e42041e00500400d0031459100741207060101e043c1e45406c180c050780b13400000a00c04060b01c092142100810fa4900302d81c122001c02c03a84080340c8207540e100c0c0d0703884012190682803210010003d002a501c028044010340803a00802401007150041d54441500d03500c030581001d04050007600451281c5c0350400c100184248100e180d110100c0c00051250051000c50380c507440b45114009503262 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 614710845 1250 614709595 614709631
    0x60c070803270f0a050105071d040b0f04090503030109060501020102070320150c090415150c02060d1407080f040b1503070e0720030a08070c080403050a0312050a090506 74
    0x51504504016020803030101c480c00d61640c0320b0703c2d96415164508844950808004c83c1070140151220aa0b40074842543c00740c854203402480010910030402980c0074035410411840754a442c8500f07507103d4028405541e496051204007010380380c05a004070304580c41000b60501081c0d00400748140031400c80d020f044a20700030290145014644041808070f0842c0f4414002106a4140101134060050783c09009030b0095000b051100d40b45486507500141520004a104c4c5105402c0408014070041410342040c4a90440504540440d0551011644950184000d1030340100c0055031010f82010154001e2a04e0f9941111408001c0d0203825180c000161000007581d043c031000000e02910300d80e640483ca03158900410b003080c10382020b5401c90104440701304180010044075402155525013080301c0d240c803042250302c5400480c06841000081c400400029400c0c00484000c0307000b07a507540c00411100c1000d0045075400f90030300d5007017480c1c150f0020026201003030042d40040e09e40c5041c44182 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 614712095 1250 614710845 614710891
    0x30c030903091309122c06070f030306031b080a081804050703061a041a03100305010603030201090308090a02030601140109030b010f0f2907060f050f09060c070803 72
    0xc0030b01c01200d5480a402050954140e985602001249004505005802108902c140d42100540200804102c0b001d0b25448060300408826641800054143d5181000a4456203004680108110002512200c2c2082407113003603003a4000101c2c00c02c05a6101c546032409030b607501d040c02c01004042d0392001c5820b03500c400380d130000c007080404050000d0001e454048030007401005a4019442e101500c42e20f6200c0d4030003058280c8068800c0d01c5100800c0701040f0710507041e0358000904500d03007035a9606001c00062001c2c0a101c0c01984a900049011f00a614020303001500082c106840d680c03012042e03030056030340090003904481d000c0c41003100c3c89071079400403901401d06800c054004c4511078000107485144d4003003c400c80308010780200c52641c50b6003d20808800c005c6249003441c420300318412811103054001c2c02080c0c420700c000a004580c0c89a904240c610803500282511036540030015600400e006c00d691240f10441440c0c60443c0030b0390b600c001d5020103000f80c0c65a0100f42003c290305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 614713345 1250 614712095 614712097
    0x1080d0e01080a0b0d0f02011409090123130c0e12062e170c01081e0a020d1410140a181401030b070f0c021804031701080307030215040305030c030903 66
    0x610000351000300e110501d401c0246d501054148101d0000d0b46c84140b0032038080c4181c0c04d49002401c001d2030500541d10300b41c1003001c03241490210542400909030520000e075958000d5040b40c1140c2c00011601404049001c0e140201071801d482c043d01c0c0c8403200a19403100400c005030300c81c1c218190484181d11001da6172207070380030742a40b41c03880080700b040100e0028660070b020790703030703044180101c603043e95081c0011510030400340c44c400c0d210000100301c0e11600d1456088145d214115140040c10110a00e17986030582e40200b00000540c10000e0034412100c650403007a2028103800c1507810010800e10740802c0503941d00c0c3c8507108845217aa1550781c000140c580042006c480304c0c80c801c10042d41c40c1c1c1040410004140c440b44041380584100c3d0020a0252034602c40d8690010009945004005503412807004010821820003601c1c45600003031050200190303020303014100c01551aa091031502914100c564207d03008400201c41c1004000b0f0342c0f0034201d95001d20b50700c0d40d260b00c1341c603404401e07459 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 614714595 1250 614713345 614713361
    0x8070e041502030a110f090a09020705070e1b12090d080709090c1e020322061b03120c0206010f0603020c030313020d050102030406020306180f04120c0804090c0801080d0e01080a 78
    0x2200c40001c0e1080b402c03e00c6c0000f5024940341181c40384c1c54546d40d02c1e1800308a11811000522035000381c1c108214032101d40343d201c0d50111055601070b07007030503642e1007480e010b500501900000ca100b0906010b440c038000c00c07085920a4060420006d80d0429881c00340000020b880b44031815a120050211180d100e4199000074108500f00180070b81003442c0042e4030794006800c07141601c14495880c030b00c03440c01d4a100104448940e141d07900e086030030450508194588403001d4050081d1030f0020044d6032010b1040c01401c0310642e003c1c1c4050b504205007075642030110307403104042500600101003140c80200072260030410b6081c40043c076201c1403020401e000c1b28004080c11070351020041005128968001350300c9510308540305220300d204000b881d01c107140190380d04140c4084030710000e40011101c2528564049a500344502450400ea4400815912580020801e036444195070b01d0207640011509016000c0840580485540154024135000031030013450304200061020400c0d14400b036024000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 614715845 1250 614714595 614714621
    0x5030322030804170d0e070e061f030f091b05010f05040f15091e1d07050702150d0905030c010606090b070605071b0f0302070905011404020912010e0708070e041502030a 74
    0x41041031214805481e010582300c2c44260400340030000d1014541003a00c8000400025140300050805000440c010b0282c600300095060f0b440400382c0202e82111801101e2220046401c442a0f0410000406480d0b07440c41840501a05210900a0f40d11090106c42030302d0115501c000005281c90301118171850315400402e40009180c82c891800c1046602141603038507019603007030040d402c0e031140c029501c021210000004e5040c051040145002484032a8015103a10801e04010515050034100c803078a21080b90b9641c000100d001c50b0b00400c3c020b22000f003c040c180031b60740f00c0c0703040c0c640403181c4103841c1c2c006c0c2a01d946d180062021806802e10000700380d410b804002490405241248410340b4080f0f090300948261782000803d80c1040c001e0506071b880c1094291034100140027400080c3d040003010650000b030400451400711001d00c203000707001d0315050081c44a1840c0148081c1003040381d81201c01c5024003801084081076150b00c0c8207403002480308006070b0700d641e1005030000801c41000c81070307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 614717095 1250 614715845 614715851
    0x80702090115020c0607080904050406060305060702010b090f060a060c21050715050613020a03060308212a180a0620060103050c0108060a09020705030322030804170d 73
    0x401c2a0901d00e0b80710402140316000ca80030040764a00304546401001802014002c00f046020520b0615410a036080f030720900300460100d0b00e0360b4400e41000c2d01210382c640140e5481c0143d045520b803098550b504403440651480960910ba0045480342c4a20f010b54424004407090710380401c0760341201c00c4a04601030007042c0c20081855801492a84008401e982a409481c03050084078698460903000f50002081075420541c040d44800c00f07508a240401c00b41a50f81070000042184d9400510281c0c281c94503400142042c2048030000c1d0a0140c28210b560402003c010300002e2003250b81410700342d400c201c550300c0d00032058500b4006128011004d8003c20301c0c40c000502c80d0741080c4850317400411154520005840d4280c2255034800c24480641542c0c4050110251940110f40b49600041c000c1c08400b2415119a4a0426a80300d5102243c1aa00010410090328156403210080000601c800c00f4800c0b0961001048407402030b0024108040c082400d10800c04000100c0e2000c1455001c00c2c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 614718345 1250 614717095 614717099
    0x10306090c030f0602030610032903070b220e07141b010207060506040b03010b0901030f061103010b09010f260a0b0d0b160e01021b01030213090504060b0919090807020901 75
    0x1c0c4065042502c042d400348680d9a4460380d44c27070281c0140724603840a40c410100c000384000d003d15244200804468040c000c15402089860400000382900b5010201c2e07441c0035280e128101b100c0c0c0c4102c0d13200703109001c3c0070000c2c000fa882d4001100008403240131209034841440c90103502c41105140d0f02d40c5855803000400008202c0e040e04100d101d02d408a6041043c1e100c000140340c02c1e42c011107641079104140320014400107220880d95107032107029007000210400c8010000e10503500a0b00840706801011450711115a445400021940e0f00762a204e2000444c981407204040e1812a14908804040f000502c6a1441b5070003039a12090003000240c0d54011420030051780401681d208000008020b190104507014120b55180c082c010fa004003a03000c010050803869204069a5a0415400b0003002409803000080350010380001d10f400150f0341060b152071012a00480b07030b07560040e0b0041c0d040140075040364090146161903a44040b60a11051503d02e0541c0700c0d080009500442c00c0b000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 614719595 1250 614718345 614718353
    0x1502030c0912100b061e0705030d09030207031b0506030403050d09060c09031703070203121509070807020c0d0206092b121214040204111303050132010306090c030f 72
    0xc0c3e0010205129420004101001d05100380c0b4840c124010140b44d800844e0680702a17044402001c08a004000f90380c1070040b600b03804c3d020750b841e820080e00140e0007240103006010250080e980110900201d180e101c3c0e01e0040418024000208043e0030310038040f4101c0e0120420760883c280b036a40c40f040410040744840c001805035405400151031501c500c8000481d4a0120403c1720b0181c806500214102000707a01d040321082e40c000d00000402c0e0f0120049079058807040d00c8180944d01a0312514510310708048000d281c002d4203501184100100c40c1080b0250b120700e000c88049000039030300d240f01681c0302d1030401500300520301d40c0411300265011030780c01c0c4404030007140070707000e06681e440c2d030710540c40c2e0407180584034011060f400280c4810301042c014035083e0b10007404410006802d0341401030b80c02c00283c2122030380c1d005075001e9456000010382500196035443c3c1c51103025001c0e1001c02e440d5149c2001d04001404010030350b0b40d0390102c80f000d00058428603401142c2c0001000501201460 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 614720845 1250 614719595 614719603
    0x90d06050135101812080a051f050114040b13060809071a3402011e21021903060e0601080f07080703020c0a030e03060f041502030c0912 60
    0x18862541400c04641c621003903009502200b402d103840350040c010301a01600c0d41009240b00240c03a4980d003410038107080040c40d00030043c408214079072200c6d00e5a15050400301c00b91a80186680c2500c80c400c4d03507a908551174a022401a18020b2810102030706000c80c11603554425a000b1071891760010800d01980c10740382d40d00006480c0207503520082c039140c4d1612259544514019600d079114a0300d003130106800707004045c260740c11401d800000c0d038407200f0317002e445460321b0404680326100303025000074103550304680c00c07401700b10311166000c1d201d4000f200001d0107070b61600d1050740e890544064880300d00900e5010303280d11011066003c1ca1100c412000940241154413503002442c1011000903d650b00800009d031044c4234840320f02640360386488c412504204001c1003401070507400c3c0b0001c003100741d042100c8507000b0700c00d1703d0315850004528109450100000e050100317404400c800c100000b2402c0c514031900d50085a00580c0701c1d25254812942c5000b40c1b54060b0304074056500e05045028002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 614722095 1250 614720845 614720879
    0x70303051f032913030507050321040209240d020414070f140405060a080702010906020c0a05120f040510121118030a030504060f2606030609060103020114090d060501 73
    0x2000700f060488002e90541c0b800c24201c49950313044100680380d030302080c068001011400d10800980f89080044525032001c900b85400364802011100100811401c1070038800d13803c0003080c0d1400d0340350761101001c044030500340c50129004001020b450401c54540d90801017101c00240d00a4015141c1100014240c09009403410005003801607445900341c06041110241c410160000e4607040910f80e00391035407980900a6011076582c0c030b1080020800da44040c01481c0590000341c0300455850030100c1c42c200c41182b81d041e50350390800003006000c840300d048900710f51080d03550580c02c1440741820360710100080706c2d41e5821800e0a00c520006400040109140810f1565503040c0b40e0264092507901c8880580040204108100502501c1d0140c5460061800c0600d01440442c82d1001c440710454842605d0000b0181103000340f02191405202207544031410000500e8503600d5900000c1c07401c02a00d00ea510315402c00284040710303403030f02980f04441e150044014481c0356510051855152890 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 614723345 1250 614722095 614722133
    0x609010e0a0b03040b04120c020114071b08030a0e18060d02010c05030f070c0b0307140c0f010603150606051c1d1e0d170109020306030114010b0304170f070303051f03 73
    0x503080003101034014002c43d1402c98041e5107034514044480a01c07038660b4003104060300d800c50340c1c1001a400dd5036403c11a0040c200001c05580c0701c4214400103002a141c4100c201d1160310061880325611400c1041e055000b18111082c000c00d074030310700050300c0001460300060180e001c0020b090302c280754540010311109124280881056685a4103520940001c1c0c90340e1f40010003091442d05250703800405054540c5440055070a41070310240250301b154540c0d0f00c00c0341c00d82c03180311a001c486c07059440f420300101003a007440391030904440702041c01c00686510240202c3c0d40d80802d003000101022042c4880c2c07070408100c0380b401d4142010f40000d1100f52141e00d8440c800da1400c12006031049107040c80303007003404e001490700d40d00b08004180030750402402c4503055942e07418007403800540482800d000301031055101d55241041d08110130f802071500d40d50000100f0070041e18400303842c030400311020030742c05140024254036941c40c8150800100d405002c1c1d44580704401000307104a04807455140880 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 614724595 1250 614723345 614723363
    0x6011409060d02010807180b0c070e060301050c0a0c0804090501091d19020d0f080f0a02010501050a12030c0f0b090304090f0b010f12060b030a0603051b0609010e0a0b03040b04 77
    0x19201c10028410070500c80240055003a8005c5000c0b54060000042c1006030303d1003140b03e09882d4012a401508600303c03020ba0359100d41010003101815081c0076801040c1030340240828502080c080103107225041d006401c0000f0201e04405026030b1f6829100a8041d10005100710359403220aa0042e1110300b42d640c03200550b520f51752000100000d2458480c07158420500c0e940a156000c003c1f107107035480d2041e40c81c0900200c0d0400040c0d0940014040e02c09100091915400c52540007400c41340145c00441c015410804203203c01180d10001c0048650301d440c3c040c409010914068050440340030b0002d050301d400b0414031600c50404400740082d03c3c00088201700d82c4411984680941d0200300300d03540440c0c0c43c020041c42040c890307d000d030400a48000080744d69581c5511300c0c0e1107a070048450303115140c4c2da000309008108080c00b0040685049000b80e4102545540000710f26119190407107051002100da06401074032009510401060240e0b0301c162645024180814560001c60302151040a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 614725845 1250 614724595 614724601
    0xd060e090c0108010b0a110a03051b07060c0b13050f03033309040816050c011209030e01051305040f02090a1205060604090f0203010c09090f020f091e0306011409 71
    0x90300260410344804165a4803100e42d00e810381c900900e9100781400410850311010341c4508801c100031860440748030381d50396a40e44840c51821100c203032225268600607003105004000c0103600c2041c800245030000303600100303512482190031700030039480002044c1e0f001d400d160124010340400618031800b4200303080d501d14a4101c40251900050b124142c420812282160805091850403030764481d209000d2589004844a403800103010200005c030390035805801c0804095902c411242201c0d115480140501d80d40350390044c1043e11a80d104034100000496141076500700d8040d04002402c1c06401040070140ca10074000103580a405c0e20750107810740820006000062628207007940da00080500015181c06007084040c02c1506070607145160f40b1036214025a600381b00c1d20b4040f1001380c8444142e245490414815a0b0740c280390421158418081459500e280c60b007181e130000c07401c4800a0890100c2e036a00b1008292061580742c25120711030002c550040c9038000c80b907103440202d0b80205269 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 614727095 1250 614725845 614725861
    0x504060e010b0a09020c0712081315050a180f0b0d0c2307030c0606090b090f070e010c0602070804150e150d0506030f0d1d09040305030103020d06060b0d060e 69
    0x900003820320343c005814030020440c0b1040c40c2e0142011072840400d980354665030f100621000980c10302e060700c00c0307100000d9008201d40c4d07400c0350800404000c40500014014a1001761081c081c50813414180100d0400c6071951940b140030240140407040c50a1020540b20300e41013030300350420700f006007201c0d10b0445d030780c490280102c0d013004d400b510720401562249041c2000c00d15070740040e0b00031014400116040c0c40003503124002c0c20058100041c0000b4030140500400c071104d44044c142150310f20344641840289940854241c20502d002e00b082c0802d0809460030784020321034440050002c4001060100d50b0001c1d4a00c200380a5000c3e903130f041e06809040040100300d0b010103081140110042080c040540d1040d00030590111008060f201160809141c0703500b094803140702071001510030007145901032050702d5542c1010505840704049894540ea011b0458072040c040a07100b00c0020b0401000c100e07554111070080d088170020745440701d20880042002d010300c0e01542ea00f044400e00094001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 614728345 1250 614727095 614727101
    0x90801060806010e0c0a0207090c050a3b010e0d06050403180819020102150a290604050f0a030f11012606040c020708031b0601051c03121d010504060e01 67
    0x381e4a00308031039510b500d501170400f035954031600c03000b03082d0f00800d080011590510701c00c080d0b842c05640c48071a07445001c81d400900c40c0800c803c070712005000c980e0030020241516811290804e140880c0c0001031404540180d84c007400c4112495801040b0760b2501b41080480c0d0440ea0141e4801e0302e409460300e00e01c000c60401c58403940640c0142da0f0050600c10748500b81394030880c199031300600542d0207800354801008548482250500611a240c01e4100c520b901411592524110300868180c2e5130040300000075194802e44c4034543c4617510100e4070300340d680e41e1144c00c18025076002d0111b110171030541c64454245502e088510b40031031246603201440200e104403583c070024104444946030303520031081000404000300c1e003a00314481e803940407902c0c400806c0200281485481c441000c3c0c40604c500034a00041600841d00900a903a40c0c12000800361940842c007642c181098200c0c95010344e0b03500001e141b109152000c05110028411042c141035002034000c80c041d9100f442000b0b40c41c0e0001d800c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 614729595 1250 614728345 614728349
    0x60e0d080405151509040605070f020c0312030c12010e1e0105011b030315080303160e010f0c0609020405011e060e01210f1e050703150509101509080106080601 70
    0x2603000f082c810300006011901d142c1c0d202c03078a00300301d2218241e030b080800d14144084408450041d510f00c2840b000c0e64000c4141207060350705c0d2006015040541000c00d80714126038001169030030010010600c1043d001b419101f41f09007101c0d23424001c2d07950300c804800082c004d0361100c5425401b01d050700c94800d0325278280750590b070060310f40217209156500c00c02400721484074150109030b612510107401111a1300704400800c00000110303102e00f0301e40c0e0307a102074034241c89021043c031a4203d0300c1c0c240382c0d8101c448119564418146400c1521050408001400c042e441c02980a441d15001180401c580c104004205a10180c508406138403103500f954110030361082240410703041400480144240680111408011080443e200300c4241d003000684030806260003281c2d030304c10310341020b043e8148102940299075160500100c0ca401541d40d1003801140150b500a0704580001041008107105280c014078003403021100000311003800801d0b05100b4002c4900550030b025001032184000114181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 614730845 1250 614729595 614729603
    0x50d050f1e04050a05062a12011203030f1e150302030c060c07050a031a0f01051509060c0a0605010504110913020901090b0712110303041205031f03060e0d0804 70
    0x240001c00303020407038681e080204216258459841ca40001440600216000d0f00c5038124a400d100368196084080b000160500000c000e02401442c0c000300721079040a04596100141c0c9641d42810309045010b000e0f00020440040d04040c0c0d4258050740c83c003146008401d8940080242400c10f03200034030081054403000e507241e44042400821860450010002400080101c0754641d0382ea40114244407135691081e80d500488254210150104002c4e580d40002e02c50499095981000001102240601c3c0c40d150200404200e00441d030301c811040701c4c00c1c04582021100c040c45107150400c0689403d0040b5070150741400c0c0c00d01a4212194140d8001520013084902403510f44400c032402034102111160400000b403c0016000d11000700408100b8054800344c0141c9803180006400300722101002040d5500400400004c110411004100c0810500e0705c2940e0b5120540c02d5029109a80085c15240c00070480000070400c00b5446292100060307020b60344051101001a1810801160060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 614732095 1250 614730845 614730871
    0xe1005030a0f02090705040f14030c10020706120e030c06180f1f14132001050706110c01020c16050102072103170f04030908070803040e0907030210050d050f 69
    0xb000510f441a002c80d4054140c0c0350807404d141d0303240080c41905280341d022000c04012140044500d0500784681585d40c3c030261484030002c0040d00b8025a04d00403441660200f210452031048001042d4008000074415081240e841c0c05440240a45a10054880b041c04500140c0e044055407804a07002c1034103648070b1f020300403e141060690031842d18031208600081e55904005a00405503247c0034001c0b00002503ca014040e503240001c03c507440321603245030304104403000b000b8603a0b20008070340c1078540c4813801040d00c5000200006c1031340200300c04050700e540049441501c4810015000b550310b5048a58001c100382c2e82c0005903110700c0e4070f00464009000c1155a02d110242c00c006007003040d4030070b250649090796907100240074958103560011101042c00d05100c01d15030302c1a20329025103070100141810304e140c01c920561b81d20543c0306680d03010850350005401e111003400310b01e0046402a010420081c1444401000381c2d00840c503c1072028584070110f112a40c06070079452186003460404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 614733345 1250 614732095 614732123
    0x7080309010302090a030f050d0815060702130b040c050c1c022e050406061d0f18280c060801050d0303020d0917130602010203060a060f1205010e1005030a 68
    0x110080d41c0900c130385503041018100c0c00000035054507100d00c0c401c1d02860141c10303242c0440b140240700c40030103065600c05000941d0711b10001d03541c0e4011a8001541128608408004010785101601c0380982156019240a814036507540d0407000401002d00e44800f5201c2d45111803130606800100e80a031200140e1001c40710050b002a486144103080d20035110140e09048900420b000303a07401211b007112034503220380d000c0207440700500c200c0011b0007006020110341c1c07806650780d200802004000100315507011103d0509588141b005a01d041000420f000b008201c600f40c02c95550102c06048950302e1070341034001200d6100300c42080c180d41004240c00346104164404802a41003050701890340b540d1042050000781c0c0036070f083c1c003400c41c480c0700c41922500030b02041e081440c00d90744000190b900400c0ac110844d601c04880c1010b0f128503062010491111450456008000c0e0112220442c40e081c008940e00e44a43c2c22588030790302c01060610403e03203540038035031100c020400040c84844070704030b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 614734595 1250 614733345 614733347
    0x5060d0512031b041406070c033002060f1f030804090c020606180f0424060612090f02210a060209090610120c1b0602070219030f03030c030b1f020f0708030901 70
    0x304040c60080303201c50390700c8d92039403140341c43e21141603e150803400000b10003885c90581420b00000e907403502c1c000340c0f290307103030424042140c6a03004000c0d200084405207a00ca0601c480c2c0c600002840d0070a11158a807500c42030700304000c00f80311100da40940b042c00001001442c00f024200741d021580700404c03583d81c442080300d009204024004803411136051151189281880d641e1950043c4155001f1a0712032800e00044c028000a840c08505981000c0300030020440e610045209282d061380c0b440c01c1c5245241c2030743c5170b154009288a0250285040704418052203030058003c0010072284030046841b030908119160aa00300046c0114821248424410509502800c000c04290402c1e00880103503000c48240d00c40486070131170300350354081221415800c200c0b03d4092070958419142203e00d046841d8803960130582d0800130201502e42c0000041c0c903102e43c01c211441d583c090240700070941d4100e0154060442102051300600c920440c820a44000055900c112400c81d0061441c0c00300c4040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 614735845 1250 614734595 614734597
    0x90204300f020a030b0702030d1505030304210c180c0504030b06040e0f0d0c0c0806041a0405030904050103060614010206060915010c0b0703060609061701050405060d0512031b041406 80
    0x90700303903030001c3c0300c8400001048203810254803500e26603028603600c1040640390380446081c101c01001581c0815010f1000382c50000c201c6042c0e54900c1045401e200d00c1c1c1da4001c64100f0759a8004003001440c0000103100c44c1d1520000d10311030110700701841000c65850007164a80600d21019180c5031b400008112282420b0b886000c00c026a801540d543c000e5041c00a80780042c074051300d400140b40c039100d01041c03004404900000c0d04422002c1d210034101502c40b000c03081a600303418034210300488042800c0000800444440c80350180007803125684d2410300c080100341d01c0c803445100b0101000709104c039601c0440e0040c426a4000c1000440b5140e14851764040b400c0380c403d80741402032103980e40c00415503020004d4895820740d9000328660742440002080c000469005009002080c0004602000302c20302440c1074400644000071030355908000120703181040e240c003500c14040c00b28040d030f00448880c010b5100310003c441b8a12001c1d03001801c00b1003886184a83c0100d980722902074041850810 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 614737095 1250 614735845 614735873
    0x1030807081e0307020c040509060106032406050d18030c060b0f060c03040603060f03050d030213030f0609020306060f0306060906031203090a12080f0f040201021609020430 76
    0xc540604000148216602c8482620055041c019010003000100e42d030402c541080000140d40611071802c0214410741e407013406004210516032504400c043c0d00c005c014940821456501b8000d120903940d40c0d010340340798800003034203104605091f603181c0ca2660341241c461203181d0559441450a100d0f850740b8004141c1c50140940c44800081114125035985015080c48000c4602460b9120314058014085680b20b902a02d07446800784020004030748086071400035084942000b698410000d18074608000558000030034a501007102101840910b40c400030b01e845c0f007078040722800c0d1500020450011110722251340d05903c6800065031070304114225035008134003d0f00f02c80110015411460b002e401c201c440c404158020150b0b40140401031442c2008030502d410112880e041c10316081000041c0103041c0e45c07004618502040031644204000d50700d42c142803080b24600f036142e00e01e000107503010b8030500e10110740c0c01c04c03600030185108800c0349078100408035800c0001c05965036050728400035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 614738345 1250 614737095 614737103
    0x2100c030e150a050702010b060f160803010b0a18050303040915121b0b030c180d05010f060501230a0c031803060903180f05060c0307122303040b01030807 68
    0x1003081e00308018003002202070160701c5210303400c1140b0304204000101d0790010501021681491030040b40c6880f5001199200c5114616035591600d440350406400c4070313162002041d4040c00000000d048011101a003c880300755691000c080e40d100f5880e40000e0280d004142e17058004101c100803440c1c0316440b4886045009000280b0346681c1c000c10f5000602d0380c0801e4640715100d03004c101d0080d0b2145000c2c40501044010b20382141003c09440480b4011840340540315031b410102c18015940b0442c03c0e000b6158010001e000c0c02c000e07401c4041c060021840b409010800000d40c41500c0012070880d40303172545051000c0c80c10522140001c403560034000c6000da0602c0411820f41642030807c2411070043d502a0601095004140ca4000e24801034008100c4260300e1008003801030441c089030103400c460302110099168140c41076814114410000000d00003d291540a000745800c04103802e20f02d0311000b503282d104002c00401c0e1050b071200711070003845c13150403170b006000040c00e00014100c01406 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 614739595 1250 614738345 614738351
    0x30603120518130b030f0a0c03020f0102010b100f1d03030d020a1b05010606090b0306090604020a14030f0609131703072006040b0105030a0302030318012004090f050702100c03 77
    0x4900104405030780107011407200c1a04c3d40d030000c2071400d0400441c0441403104000b011105201d803100540300481d0b00000b80704800104801d100d80c6e100b50019600c802006241e0083d40c035101c0e4020b00300d4805e51201d440481c6100700145014000320302981a1010068051480c03c0c4144100400940c4a100c0910034004442012084d803485841ea500145204200004e145070070401d0182c000c0e00da541c480d01c1080d00c10001c00400740c070b134644803a03044901500c01513112604000240c8070540d03040d412101d64280807041050240300045400e000300416143c4540715101d1101c1031030360f02031a19003e0201e41816a01000c6000014019548070500d0714280c0581c1032080185a0a0a88411006d00c203610030001c1c0414440c03c942d140d0700500c401c0300201204101550087e40700d0100500c07140320060f4011500f104d031074081d00308064121030700c40103200c59200c4640d00c3c0000d0b00f05004105840b840e16003508065600c81c0329140c045e40e40b940041c9400303e60a1a484080c1004803445010191 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 614740845 1250 614739595 614739637
    0x23010c0803130b041b0b0306010c02012307050105040c060206040b013006050601020c01110d1805040c08070e040605011d0102150a06081c17090c0a240306031205 71
    0x80f034120300364015480f444ca107040d140950700c44034061003003542120f0000c2c0010400d02009a800007104c40000b903080c00d200720070850001010000e80c24000c1e451000c02000200a030401030103500c014400c610400c1210049a21000100c5c1d544000716402000c40c050100148000c000b0840099140390a003503d05140c14a28000c0c0d00b4038a42a503c11200c03d500d81c024007c981d030701400b03408100c450a1814081d4400242c0c201c1c1c1d51703103010110b140c2c01c1c000f601025030040e6804142d48805040007402c14001814030420081505404541c940006860600308808502d441e0050300121141607444e071081c1100c0c540382104e8070180701c1c0b00d54154443c602c051002c44080012041c410362201c580010320b245421450340c10078103e8a80640f8101c511200e11074025008916400c5a4101c01d019641c0e1b0383e22034054078508080c0c2c804040d0300c0768403698002403040b9400c0d40d1418149254042c02031062040d041502550300601000b0b040d05582d4160562461085024201d08200040306101981c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 614742095 1250 614740845 614740853
    0xf272a250809041b0201051803041a0408030a0804030f0c050303010608060f10091502120d0b030307140105071b0c06030e011416020d080c070f060608030d0623010c080313 75
    0x2a2446084e5110313074407080e03441d0b03003c10340a1042039440b014901556080c0c4010b50700c11601d0303201d2402075058002c04101c061882c0c26580003601c1c003600440c001c4035540c500c01913018040a000300e408400040045103a141c01c14412084c1600c6550700c00000d505590030004140c85080c00102050303080001c000580d411503484080344501003045480f190003060415940d511465001c6400c1c01c00d542c030a400b1032000d00c0c0000100c5d02c20503810080014104044400681544500400030340805040060a0401c642c19440320740225540e445004815440d104101e800c3c50000001030490708a808040000c42d00075000641414a14400016013181c01044400144415203482c2c1c1c601180780c0312400300700d40411035002c820400c0c0c10101810b10305001488054414108002d222650040c003100030030959401100c05024928243c0b6241c0840507100d10041130ba038460001da90380d88041c00d58009500e028074104e642c1069507030480c0c50040c2c2d120100c480d400a4111b400507403500c07401798041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 614743345 1250 614742095 614742101
    0x3090d02010e061b07230d03020a020a09020307121112060112090503071e051b01030f05010803030a0c090503030d1805030424020c0f272a25080904 65
    0xa803070480b00300d8402c0514915002d01c0c00710581c02682240c40b42e800c0304400f1450000846d900c000d01213404515030420740ca0124208568080000e42081030000c001c00d03100c100d9000345115042565070a40c1c681811210201601c080c4041d110041c1c5003008040c440705201e403c0b143e07003c4018142100719480d100c0081d003c41c0d0a002c0203944580011030010b0400012070b064000200800510074490342060301e0b040d4440c070103581c54031151480130005500c0da9010741c21007501002440d02c00c100360b6035a8205a0f80300d034000c8541007409441c0042c801500307401201460140c6201078011820800b001500304000d08032250040302c010300307800010300055001c0009101400c007111004110200c00c010b0708101124842c00002990000e00c001580b544070105900f10b04c0c0401c6440141e003000e407009584c00c5170401030f1151046d085d0740c01086050902e42054a200c000c140c14080070001d80020f5014490090802c0c04401102c45801100850841c0316648003660040701120304d4410503000041c22 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 614744595 1250 614743345 614743357
    0xa060818070f0306110c070b07060b0a030b0105011209080d150f060f08010806010b0f0702010c060c020705030d030203011a070c0b030a05150609010c02130e061e070f0203090d02010e06 81
    0x20740c01c0c450070500800c0250b026400a050180005c64204413150032176549450107809035403a0307081c0219818041c420705801c01c800b005805421610003035100d0409800140302401558046000c9091031072070700600380711b089151600160749509110007001c8030000f07000760382c2c05030806000510003c0303030511591030f0400c0203004640750703010018072030b541c090301c03441c4168402e40b03160700b01000411241d07080030100c031610300242894a0b03882d50345200503074600940e00e42c05802a4030b800e480c915090380004e0000141c0364110129200781c1d101030801c40680c4400d000b501c101c80641000d0184407850760015000b4184030b1040c0c021400e86030900b00034280c104460032604d203501c6070207011210a81000540749090300b51051443c0c8440c030400a440d40c40c001c01d0081c0030301440407400c1c1e21243d4503031240014810700000d5032040e0421031580160078070b00040d10440b200b0810f000c26402402060b203140c2c544d01a0700510b050600c800204803d50a10960580c103020020610000711307561b2400400c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 614745845 1250 614744595 614744609
    0x131104091e0612050a080a050d0e0109140102071a060a031a01030204060504090b2e1e050a050109120507050d030c121b08070609021009080f0604020a06081807 70
    0x2190102901e040c0c0103482455200329203440351007903c01c1c041500400c080c4401c9070400300d007941d0740c40d4181048405108240042018502c0c2c030907585030401041d000b030b0502c94001d44001243c0c241d0611894200e00c1040c7d8010602080d00710a048104a091070313142c0d01c680300406007610b280d40c2c0d446540c00041c50484040056010b400144214074042c0b16030805400243c500b0418400182c1e41c48074001d50107080d1313421a202400384c038100300000c050011620100282101c04955640b007001d1001c00c10629407080d5143d6a050114080c00d020626100b00c7d0016916407414502d4600310708084841d00c24103070307800c3c054940301041c0c0b915038a0071035006038400d55800b98a41d64905011911550200890b000c011000d00c0c80241c1a4481401000c550742110189030f4948840c49c04400601c02e03084000c1d000f84618031103d80c06a0803503400b10031140000c056400b580d811718106038891000f00c0b8000d40c40f00b400f581c1070180394460300c4480d030b0101c20b418081c562041b029206600d00074880d1f01030b82c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 614747095 1250 614745845 614745881
    0x1a06071401021213050715080a0911061303020a050f010503190e0a03050a11010e030f090a12030509120d0813020f0901030804060e0406290d060305070608090c13110409 74
    0x501041410006c0c18018140181e035402d0590680a00401c0500d02418428529466464481c280081403145940f2100d00803e11780d0b5038031030490000b00000b800d12050744101700101c80040d00b818030720100c1c0d140d40342c140e441c1c03407440ea03640320308540c4807c600111941c90341e0f0b940c12414882008000340b0441074025114207803a1b000710000101804a801540d4a0305c3c0d050800010106500000380c2c2c000ca44115120340e21030140501249a0003a0f070f074407441d020078020180743d09140d003000041150800544070009481c04011450b544c0b000001c01d20000150b103207002401c060341c0008050502d40c4001c01c000164844803002070302056080c0c000782c413164400502000307a190001c6080006520a032828411a031070000807642c10b000c2d0b144070b4120000b040403031501c4402942c1c22035443d05c04001d01000010707100e00300311303a840f070a41c015100445c001401152042c0d400041c0c404190400400d0044041c002a1030100945440900405110001e01002c11619018050b10090310316282c1d00c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 614748201 1106 614747095 614747131
    0x7030b18100608010c02061605090d0803070201050601020f1902100201020405030a0c03020a0902030126030d090302010f140f010902031906060c05011a060714010212 73
    0x20000c9008001c5012003140d9182d01820a54220000070030a1071a012400e90fa41e440541e03c0c446615032840d02056a2403082e00246606900907010317818a203016070714409039400c2540d0002c0540d4407a41084820350741004506417201d0710000500d11480d03840c25104040307960131000383c06000b516005d240c5e0b00c1d000350111002068090215604460b039410030484900380b60004070f104958001c03001400c0036660082e24140d4005145040384c0101c40000220122401c1c0051a4140418080c00001500b0341c8143c22450340260008251405141d403840100c620260480d80c220320f40000b40000046000f060340d054880901c00182e0340d0f00d4113400501d4402c901d442c804411410300501040781039007c05100e8200b88140000c1c40100a5402000140920791440e0b5030441d4092219601081c1e0120341d804145c01050001443c2c50000c041b0804480000c0f6140009954148a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 614568345 614748201 := by
  have h0 := BRFrame.cov_init 614568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 614568345 ≤ n) (h2 : n < 614748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
