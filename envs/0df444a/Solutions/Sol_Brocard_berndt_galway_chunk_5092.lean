-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:43:29.077752+00:00
-- url     : https://prove2.me/submissions/bd5ca41b-0fe6-464a-9a0f-df75414c01eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 915647482 ≤ n < 915827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 915648732 1250 915647482 915647497
    0x11e020f030c010c091509090b18071d0109060c060908160305090f0604050f040f0f11040f06020a03140903070504090f11040b0d06020f0c01050444031302031002 71
    0x1190070391765940303d0504000300e45601c40780002c1031140c0001d020700e20450703002c42c103550340c0201060301350281920060380c000f006468080019603c202108400031041309031070705c521000c0c6402c480e494a0103000901140206000402c010f03141d8451a091010306000c0d0303440c1c1c800000c90400c0c0c400852402810a0388940c003194043d10880f80140058035150040d02c00325172010f0040b03440010200100001130960032415000c0faa6181c40e51941c44015105400c00040300004541c0d81e6801c24240200c241020b920000c02c650240c8069000694015142c2c401201d601c0e846030b84910040000a0902c4000d4100030b40251410b04e950007880898194100c1c1d44e4020b4101c0740c0030160180070f21042c0d9a03403280454002c81c001c01e004001980e550b00411103401c917403090300e082c407030214401c90960703000707840c2642d042694041482c1920144911320143c030302414034844000640ca85d01a18000803464010a00c5031302000144c003507074090b881c00d134916900805907511516142c038410025044a01c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 915649982 1250 915648732 915648737
    0x12703020607080f0c0c012714010c17070903082710020309010f020c0a0e07020d030b010e040e10060f08120909130f0507030b01140906011e020f030c010c 68
    0xc5030705140219525070103907400341003014030390b0f440080701e41080d8061b16500d1034640d1399a442001c40101c001c0d090b41e18002c1d500ca400210903003030a000081c5c86580501507c0303039140600c5000484e0f08402d9a144034040d01170511801c0d95a4141034940303292580c805002c15400050000c200103040300001c602134154540e41d04034601d0002800480b600421400002d0f0340200004035040d8054514070080012502c1180c1c00700c201ca0300420000501f5600913854041d20f4401d2200250b0180031140380343c211854204a460340b0000028090408022494012030799841800c646070010320010105d010500b07800c3c080d16942d80c0d4400311040321440340c1d0100d030084840301d25008030070341e0807aa41038000a22050045d00c9813208103c24040040c002c4075082c844000c0c02002807414081c4000540c040c0c0c2800d1200e44c5000c0c0300000c00320002e04481e100d030b4001f404215042e80c000c002d0601044600c008030450840c0c910741a407078070060b4841c031a81c03884040b81015192405401c03100c0c0000e44d80d03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 915651232 1250 915649982 915649993
    0x19060b120115270f0225170304060e0a0c1a0c15091c0c060b04020705430f0501020d2705060c160f050d02011101270302 53
    0x815205088418280496003051890b450821108920303034085508080c0303800718900c00c0616003080e038080320701d2080c4103c2030340d80102d0340e0b502031404600000030142c0050381841ca080c0880d035a2001c03001c6a0802a50f003101c002c00421f041c40660351095045949140c1281e920030150f082030401400184608a000c040c5880650702c040a03030010b071011504514010969880034004018015500a083c0c0009104660540e01184150402c07191124000e488441c2c405102e400d245003650240c10540c2d000364010044200065000906000c1e4003250140c1c801c4030a002d22020b1740c2014444682c206180117802c80080d40350768961441d802ca0303d41c815000180c990752001a61603003c010748980128540c0310040b003100d0085030268000c442c0e81c10700d13040d1064543c00040c02e2900000c50321007095100003100341c10681005440e00240900c450b110f02c6d154a0440042c4000e10114002070402c65030b5420300364043d809400018a03545400840c100c40c420b200c1c04180203d182090a50061058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 915652482 1250 915651232 915651259
    0x105060406230f0d0b01060905190e152d0906100c0f060203040303050603010b03010e030405150409020c0f190c03030e180712061703070b04020319060b 67
    0x16200740700c01c58094101028200840e410000da040c8140021690000d24841c034020f41036a64843c3c05080c40d21540c17481c0115410f00100804a006a810090003440315a221a800c2e0b820541c0010890740244141010b940e520b403003a281c2940368410850304008296200960b40341f502a040403d60b401303202c1d01c540724800b03074100204000e0030344805800440c41070540401c1c0b8402c904c296801c0b405241040c0356083c0d90380c1c801040340c1c4100e0f0250300095480060164920302805110b1800504400074441c000583d8080340d280c0c0315910a1501c9048420301c080403d40302101078400a1136103810442d104c0c03a60801107903c410513900c0103031050007081c0e4094003130500071041d151030383e030407a004034020b034117554041e0740701d00d03064a20560141c4182e02d1004088012030003c1d20401d116540c1c145c0c1001c40310204020f480190300064500c50b429108503080100000a480e05190000160201e6464600110381424110206c1c0c588200320320491703c00b4441d00e07402540e04c038002507170010f042480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 915653732 1250 915652482 915652489
    0x30b04050121020a03120302040905130510050702010f230606031b070201050c06070c0507050315060d02010c020a091e051303110f01140a0507090501141c05070c0203010506 76
    0x2406142c0e442016880b24407202240c03041d441a2852000e0316507a8102c0d1252202005440a0401c1c0d900203a0001424401c52100340903540d00a04803603110200d090041d5036641d12000240180e80d4816924000030700000d10075000700d400c081900d4410070065080460384040701041c00c0081e20401c103a0000701c2c56504003202160300c58902c0e08490b682e003034002204080d059100782c034240d0401c0800d1084c2041c044040c41658090781481e2101c8a080350b2518107641045980d0340002e20075086103018007000d1480780c0c5000d41c001421503018950b00c016100684d9041c03141344001c2e40052100d400410503c8569000c0c01270f00a00000c01413160203810707201d07401d46404650040e04000c0c2d44070303170703d0020340101496911944081c040e100d12800100c5240c0c215020070040c9040341107484140305080241e032040e190404080c1c903003920214100350010342101805040200c00b1440060040d101c801c246a40d69081940d0001c18402070900b04002810392001c41c0c8164881e51818001c03499524 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 915654982 1250 915653732 915653741
    0x2c010219051303080706021b01021314010c0209091c051209010b0109180f181403040503120a020f07170d0c110f0d050f0105040c0603050601021c050909070f030b04 72
    0x40b07807004109a120300750765038042c5a8114a4080360b034a902813229011440d4900342001443d511080010f031140303c166400c10640800e507102e010160380f02c0f00c0b407071243d9038080a59400c19405640e40d40319901ea12403040c1c42d00076185224030380c2d0a84030041c410320560020041c1081400640810010340758481090708032003420300d00501041100030100907540c80c1da419440840e0440c2c8002440780f8281401c08180c0d40c02502244c2d400310748007102000c00180c81e160349000561900198100350a05020903a40c0103809440743c61003801290700f8800620030000382a40c143c44a050742e4209076182d1030026181680f04442c071042c050030700d0616100348181c03681e800c0c1581040000d598810601c05000c0741e1014a6030030794005100350640c0300400e10801142d10f1010391040002403900e400c0c141010300e96607681248082600704800e000c8035a900080802406a13420200700005080c00e030240d9240c81602c0e50340b03400820b5a010010815041401c00c045101d6a84060110b82d10103001c02c01101e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 915656232 1250 915654982 915654997
    0x1e060a080f090610030b09030706150923042a0914010503150601050c0c04060f03021f0f0e0d0f0317010603020f041701060b031510030608030d2c01021905 68
    0x70155140400104011b140d440750407400c40b0098070303e440c0c80c0d41c65441c15a1011102500b02203100d50040020b00c0c9603129541c417444e540c81c242c4c100d100103800d0301201003a0240c0003074400481ca5400c11903408018140c040320300000b4643c2c0e42881d41d1051030301d01034075043c0341800c41c3e140c880c1c0000070030b4240410031505100304d505405183c0c0c1c3e5098015141904800741001d40c0d4410170000003070584039442054090708480f028011031a10b548100711652201403009449107026002e080c5450b6004840c00e0b0720200e140c03d1032070381000020081901801e850001070406680c0b191080d0901d03800050302913090b0001172181711141c0c1c8441058044c2e1081044083e00300384100710801c00d0a041038042600f0319500c100209849644803040ea030b09400640380000d000f400344011950300d1500e0300c803607400d401c801c2c20706000d1203113400107498403402060001c42c2e00300d0305e60704aa171500326503248030254500d0310a40c00800c0307070300131450a0003034019a08510001e1513060101000c07900441c19140b00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 915657482 1250 915656232 915656251
    0x10b1008070c031d10021c030b09040312140a0e011401080a0305070f0c0602030406121506110a080c160e0c090105070825050c0409020f1e060a080f0906 67
    0xc00b4426a42250340328070101c0e680c500d06000c00b22220340350341e6960604d40803800c540e00a21140c00e001e2150040c084c9a0741d10b0750141442c06101f020651a140d6402354419003501b4031062100400d140d11005c4c00c604004189607041103802c025429406a010030384103a0083c000700580d941140382e00d03828000a000307200aa41c040250700c1e00180c480c4005003440c4c1e220302c2d01209030750b2007035071010414038581d08034601581002c181170107003d9102003621408290044180004078002c0c98080c1080c5245c060f0400f0800f00b012400031041040201040741a03102110550303c01250b02c0d00e41d113940d03104042d110101d41d80900003a0016000340c00500817151030308031500d8980080010b41d09944056021580d40e003052103010074049122240275011800401e81d0240c4150b00d00d0040d0410f0030300130303640e8440c514142c00d11001da00c03580c41040e1880300c140e071420302518000c03a0300001d02c040320024660004001400c00303021944107035042e00910004d6107241164a5040340300e13840d920215001c849 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 915658732 1250 915657482 915657497
    0x812041a0103230f0a11030d031b030c030209130c26130507080607020627120d1509060306062907060b0603091606140711180108010b100807 62
    0x440f0391070801d004144459010450714060215070f1090304003804550244c800745116080c11409003802c1c00544c0ba100c0d810310b020040300d07a85c4820060070ba07000040c030808156807840c1408206d8000da044587c2518005c00d03040c400e030b801c4860720f006001e81d000c2038000a000d5281d0665105d2008101d00c0c0c01000a201001c86643c1c1e002c06018108541042a900382c490110300103465141800424010042d55018000500d04021501d14007880500545581c0c0c41600fa85034a104010602080c0e00e03030f800198035070703a44039200c03140c01400044010002e00c02c040840001e408035143d000c6411244110000d010160399403070f401c821700d105010190001140034920103038211240008080c0140302e414001400c01100700400c10981084071004666444841d10300c40003802440f800c00144a076141644170000c000824a5841c0182e407401040320511002203e4656504030307000c0300c1041c03035105c0380c1602c0d079540441d41d020b40a02107a090081078145904100300d4450000244141d0f01525000d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 915659982 1250 915658732 915658763
    0x3090312030705040b040b040302030105130209060123040b0711090610050d1503051e01110906030408041707090b030309010503010509060a090c110c2e0207030812041a0103 76
    0x1540d80e40020541ca080050030040031591140e000098400b0300b4042c1040703502c4904510515007110409810030080d54a002d24020040c1d0b17800704c02c01e80c400000c0c030b4060707a40b549451500504c011522110758107040081008251900000f026020450080c2c0c0340800c01040c0c0818801444001e84115030443c8604800340042d502940003405080d0312420005a8503d070501081c0208800e0740048400d60004e030040d402c401c0e050603c0c80c44140001e00201714009805070440700d031744a62401c446c042c900210014040c0806002503900501c10340c000b481c0e850152490080e26141503021710308090b49400e050b6011401e0020580d040e0042c1a11010700c2e60f4240b1040140c140401800580d00c108014404a44200a4011412510495121100e07901400c52626041c85522410f803400f50440c842110300d264074010440c041c95081d110401c3d01c0c17104000c8100d052000c150409800d4940028110109104404110703104034007032808807078220384d513000c401000c21084c400036008004060844 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 915661232 1250 915659982 915660013
    0x161b150c05070302040f05040b0907240302040f0b07031205060a0909210513060c020904030c0f0c260303102d150206060603090601060c0c0302030610080d02030903 72
    0x90266000c1c0044a001555940c006020784444604400c420f41d16601840700b0003003105503450b0400180e00250a115090500100c500440c640a0716901d03071901d0414007950f0b0095044134003410700b5060790070841d6161001c0701c449600c10071084000407880340101f05000c1440c89858041c4800a151140c1d00e490683c00300302411a004050340c024032210204602c00c00300c0141440007941580700c040d00e039417041144180c040e00c554081c000b88000304c080b030340060790341c40940d99120340c1c103042ca41500c04550030888105e02c024440101146444000800ea1545107044482e00c81000303030851420408022000340c0f43c0c0010385000307105043e0081d0502c210b4003003070440104900241c070440c00c0c0fa1808044030071000c2c00c070b610450404603034080d0043e15a6061103680e034442010384040f841c50906030800c5640d1241440380504001082da55942002008804500110b4004046550340e00700310011108042c01072080e10283d1080b4000c400b03489002005507486500020090722641c81d4a0302007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 915662482 1250 915661232 915661247
    0x643030207050906130c1806020109020f13020712020a050610120201080903091e042304121b080309010506152a0a0f061a0a15030908161b15 62
    0x42645c4a0501041c1c0980c4000e14401c1d00c00c41800d50b42c3c0d0219400e400b40415003840da580d00507904590500b04080056200c6040d201d2601d1020340340903001e100a000d480000b0b0166100040840840c2452210050340c000752030301d08207006805a0380c0a071504615a02d0b0030f40310b03100b0010074982ca02d01700d1026602603181141d000c49000d09880c6480040b40004107010b0550203c0c070320300c45c2a080075803000c0c1458407600c1000920800c14060203030b000e108034a02400c009100411609441540880303c622505482d80c19030560400d00307214041e00e190803074450f081243c0e040150340c81d10000a015152240c0e08600041c189814185011035001d2801c0300d0011010f00745c2c400e0080c400c41403582100802c0f010007094010b081c010031b81c440c07038034180f001d1b180c0d604001302030441080d04928080d0303900c4640070112440038140700c5925484010036405440002c0d000340280d0b030003107082c01d004c40c5100440090f02e4070403182d209a511560800b5012003a20340100d110300c0100702d6010b800d19001e03042 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 915663732 1250 915662482 915662491
    0x1207080a0228020f060112050f010b0303090d15060608010305010e07060813020117040b071407080a080603010920040b041802040c0c061b110c01020c04050606430302070509 76
    0x180c804c00b6502a0301e0500d44202a8402040d42c941d0703c1161040c40000c0c081002c585108030002d2000301503d2000a5581c010002040d1044004001042c10007600a41e4200c60002c100801d00030b6503a50721020302030f101c0902c0b00fa5000d50078448000000d00b030114400060301c00300e442c1d4420b5610f8030801032982c003100c0403040741800320804410000000c41c1c0c0c0e1192095101c0c0110258600e05107000810b61040031070540740c403074020b10a070030002e60f11718103848802c00545082d0180744c1d90600042d0140c24550405018a501003a500d49090385011140e52401020340d8140311610452040c0001c8507144507400c01c0c0c54038207440b2000103240a03000064020035a10388440d40141c552103650403076210909001c0e01d805603044445480360407540343c0c2095080c0340302401c80a051200040d403200d080e0460148103555420009546a40702010381d82043c1c44212207042054403907016403c0e9142220300200060008503407500d41e130308040d4450007420f0340365015041c1d461a04081c440041405030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 915664982 1250 915663732 915663737
    0x905061317010216050303060102010e0607020604060203070e0405090709110717090a0314160611031207021905010501050a051f030209060d02072105030919050705061207080a0228 79
    0x1016031400e003004c62600300d20a020b100659541d040540002e0308490900400702455049075080102068000c1421503110b40c00c0840942c0c0c3e6555044211f41002ca0502c0d05548a45841c1c14001014800980740d410740d881c0300b80c2004145103241c060681c500950308000d088503a1400c0998401041c08060180e251028122050040d200e9448030356092800c420044903500c1070000000a00720400b083d40102118180404041500b28283e622440362104030661540603e022540d8284200140c141c0721710fa104010603048141d1a05034081c00c820310660384560094000460f051410700e242900c086108c003041c8011610511094000e501b200d200d0b20b9014406111020041c9818002006c41510170039114200c007010042c0911044080d583c5035080000600400444110006000143c05152030084041240900c0e0292a0000940102d80c0040340071a2400c110000a20100e01500da25151000c1a0b074078413032030348120f00400800f0582107014820359440c403507250f20714000201403072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 915666232 1250 915664982 915664987
    0x1806020f1204081c060302090705030612120a0e12030702090a18080c0d17071d0301060603050105150a05191b031e0504121b030b0f0709050613170102 66
    0x118241d00450040301c050b0b452a5001a1801410900000c9030f14030454818041046600315008503074040c2000303024034240324000011402035600c110215090314154411102400c601184001d1180c000e400b800c004620855441c41591605a0780b83c5038490b9002c00a5040040c1c50b020800a001c0c0640180c00c03481c1e4460340180b0300c0103c0b10014203050700030021180d0f56500d09250510385402804407030204002030302e25041c400c610450481d0841281d10382140e07001c920381084955448251040b50f41036280020003d122605904014100c850490300314a5030050824070504612501c4000400103004115118400030040460b204200b018030f440d0304500b08031100602078040904042d4007007284c4200e1001815845d924414980c030310780c03400750706092034800ca0070416140414001c0c101030708a10103081402521940d5401103401c10303503051850038050340800e03450109039141d8000422440000c101410020200e5002812108c4010303031a42c54042c640b2510038441c0200400b65408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 915667482 1250 915666232 915666247
    0x5090f030f150c0c1006061106060a15050d05240102160603270501050906060f0a0e0403050f03011d010506030f06040e0106091a0a050a0609270603050a151806020f 72
    0x20000c1740c002c800f00407070000f642800d00102410384004000d0a004030b034021030030459031342c582c14024022180302e66141820724042e180140c2e0203000d09801410820b03c1d00003000b0300c1c009120305986922042084c88106190389600480c1c0b246034054400740a003816000070050107100b1380c07003a809040180c45241145001140703002400c0e0980900790f8903070b074580c1c0511504050500003070340c204500315428204030706490301141848106100b81c01d145000d2a00042c181030003241124140b805c0b01e4100c5981350785a0324404c8008200001c01c40503503c0c81c0c0c002040500b41a41106d000d0b801a0034900700941d12242000084c01c5c0313451565440d55200c41c4001224060307030250085644038204802c1c0c03446140400d100380e0041c2507004910903d14000d08101d83c94001c4140000e68481070300e05072032404800074440c1280482900fa6480528003030000007030003c0850181c3e0b044c0d1048008806120090301c0c224190f401c00c010607440403900030400c40000c0d56550003011000d0005041a003441c62 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 915668732 1250 915667482 915667507
    0x1b05070f0618030c0318050a0b1e0304050f0606010c110d0512043308010303200706030915061520060901091e0f060e0c0d0305090f030f150c 62
    0x400040450100c0c130000b030903600309130b04400307540421020580035942c1c0380c1c544000106600800d10800d4901040013601c415540c8580f030541d03c8501c603840e099650fa042c00c0c60815640c180d83c1c04141e50340c0c01000d011402d25885400c1440c012500005c40110351042076040181000c6148412641d92041c070b6628440103500401900003061480c020f01d41160001800c06000301d00c8050890120b041c4508080c038551704954624152a05440c09144c0e070401c800c4210090710328a6040400c0d031203104000140da5505400004000740300740501340c4410499a42c400945245004140451200a4104081c2c038810a901804807000900b0071040841c0d110a150030403006480002251351294015170620804019290540b955807080090f484000c1e160305020002d682c00051891307407284061300c41400204486030b060000101400b0243c0340324507001e00b150307103c40b0b007035401041c03041c498401030b00d000718076030101c50084805003e01007140c400c06078813604010031096042c6400c1c032009131100c0c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 915669982 1250 915668732 915668771
    0x10e04062307020705030d080c0a2f01020405040b0402130e0702030d060e011d0c040918020907020604021905010206010b0f12041a0c090d15230a1b05070f06 69
    0x40b56402810782142040c080c075091030540b0403a6001d2100035410302540c40c081d0000c5609c0704003103107442ca03102c46048941c8020314140c4110b14201e4101302c0c9050303200c010194000c10856804580801c000d04030b002c00d0106034010158800c1c1e8038050000c5c00c0119041600c00ca9500c90b81500c1038034074055407090000300303c5402d83c10400b807d252000c014000720300754280030019804203840d503e45070710f0902000f03030441c425401060b1400d511800c508400d191030800c4031a070294000c20075000352418100080d0356440859040e44903040390080550310358800079002081d40c1d0180e014100344d03030070060194601d5004040f05c103215541002010200700808101c14005c521804075816215407034011002501e4028011580914040000c01007541c0d50b80c48101003a0b51050014940f01c040850000c01410700113a10b4003041c0000c03407030b06486c84103040c4152003040c90700001c120354180e90f0022000e00208100c2c0d200810400c014500c08201140b001161592042c6000b1900d1010710754010b0028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 915671232 1250 915669982 915669991
    0xb01030b0d0c080c180117150a0e01111e090a0509010e0103110a121b090c020c120d092106020f0726091908070b040305070e010e040623 60
    0x4040b0101030010701024803a09070060011a15411203104d1441021101c40d010b101d50b01c80385842d000380907108002448807640c001d03001207550301d0a05d02020004098043c0c3e8103100180e502e000e455000e14002a420f6486000c0a42d2030303101003550a0b480142030790311078119640e010b985420000351984e54102c482d40600f040400400083d459850403003a1070202003400707845071900800501500c1c0710305412880d507503008902074008085000000400031604d42080f0303039941c241105a5403083d00010b0282c1c6a181c01d6032128200200407030640c0d12030100507240c40004031540020414a00c04c0e10590100d0303503004010209036582e0b680c4140413603115843d84102120046000400c1c0b20b0400040e00150710851408841c0e03005d02c03003520996105403a41117100390005051503000d00c0d076080320000503029100c220390700d95803a0300100319150172031320080300c1d83d00c0b80a001090038401140310504032540204070420340e403510358540700500a42e402c880da1010014202c04140106125241d014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 915672482 1250 915671232 915671243
    0x132406032a0b030606030604090f02100f0f050301080c0909120403121b02011202130306060806010e090f0601060f03111b010b040b06090f01030905030a09151b02040b01030b0d 77
    0x8030071582421880040d4654400c85a24406004106040c1c603848100c0b5809242240d00150703485061a14081e08005c4941c040d410088000e2a034003140c0d00700302501c408284548402d5901c211042040780c0c0d40c80700f401045515003200da05152036041c440710164024420300c050f01c210350f25a0140b5401034026a0040c6d48581c498044610300d0344e0480c4c0c0c40602e0720b1074911f8500f1403503000c0c1c0000e014030505c000300c5080d80c0e600040501e400c41e807042c3e9007005540d0090050010a0707444640d680d0300c41003030003082c4000c0b0144001c650300540c0001c90400c0e0724425005003085030700e810f0b000d8a04808000c10802815250a6008900013012000b000076070300ba819500b800114410b0b01c80d00315400500071303a0040389404000f4003959240030541d440c2102c1143c001004c41c5040f00101d010340301160004010744808640300301c103d504110610700f0f4802c0110210034a0140c40400c5410075189d13401d031740d10000ca9241060140c00c10741c1110780c0c0b1007010704011403514210300101d6040300103902c05403107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 915673732 1250 915672482 915672533
    0x1505040c12080904061517061201060b030a2f0c030d0f09050d02012906071202150f10060c050106051203040f05090c03011707050d06020d0513240603 66
    0x40e1802e803241e400502540b20460210040d2500087c2044904001000e080c00d003000c00a140703540d4020700008450345410081c00354030340e0b84d8603c020a0300280c035071059507400d101060b180f4601003c20b0240c8013000b02c1100125402c03c9001c0345c410751200c9010601070004000c3c040181520b402844001d40030540000f540b501d550401d5070500c4012641d56085904081c1007045c00b20381c01c1d2904138066a180b152a00061244000803c2441a03410041c40410744803081501c203500450161015130100e5000d14041e552070580d0586070000f03d80d50302601241210500c04c0d144150030b4540000e100340000103003552039100142060114003510107141e030000605000001c02901040002c10040e501c0d148281032079004182940014000c20850000e40700300000040410400300c0001c0074068024004000c0e40d0a10344040e510088050100301d080c04045455010f0095000c0c890b15001181245500d10445d442452001c140000c484090388600010010a480c0d500d10801d02038417114006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 915674982 1250 915673732 915673747
    0x5090f460e1905251e0513051f1103030603120903010209090103150606030510051c0b0403030203060f0303070f12030617030a080c0403150b04090b0a0e06060d1505040c1208 76
    0x4090560411900b003005014090005c0340c8440c15144e50b101c40803418000c0e11038044004d483d110100316401958003181a492110b0200880781c40c80c64613410950f20604689071030504a6520302c0140c0e48141c1541c40144084132900c071417000380c00c1c040310040016117000d1911000810f01d080c00e0b00142d403c003450001400399021944691401417110741030521052801808540002c0c082c0d20465010760354103118002d15101203060804050b40c004030740042402c003801d00a00035001102c04c503015410060824410380341c0003060343c030801c0e48101e8000c032100841c0d0300c01c0b280152a82201050640340d030004260f112a2811803490180c001008548800350850011329100020b00428909082008280003107064824a020f40303001c00000071400001200104008150201d0081e082c2641c41c02400901c1d00e594003d00303200001c001c03c80b080c5844000411462081c6150000e1040981c0381180d0011042a000994094003905225401036520313a441e2410f00c040d4001100c12110006060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 915676232 1250 915674982 915675031
    0x150604090c020f160602150a200309010606050301290c070603020706140108031605160b09010305010605030601051e0702031f050108030306060a05090f460e1905 71
    0x34000c04080b01404e011041c54054060348807803c40405c000550205400a440813049401400344800c5100f000701a43c900c41c4002600f87c0c0054a80c040e042d42010381c0010400e02c600107480c140e5042c14800005031507056102c04010030982c00001e50080e090120f10b403490340c28046000148000c0e00d0160b070ba4501c924101d0200c1e0103a414113455000070300010322071250000140e42010314421107401041c1032a041940c0313030120242c068a0b031070304032503408548211000b02400d403802007a2424080f1b640c0700c080036140d90004407066800640203000070800365a802c1d402101220720310714142e2518600384c012900345040904c1c0041c010304610110a0324070200d20402c4d00408030280514150b01302040000c2040c49140050820418003043c80d50890303030b41e504880150f080007400301b50b010180328801d003000304c01c805d000c60708034224900d16141d80c0d141c5a8811490075007030700b590b807010b0f0402034007a80d1003101070f101851400742031004402c141d03c075200d554007d910852840000030800341d041c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 915677482 1250 915676232 915676243
    0xf0d0209130204050c030c04030b090322060f020106180c09081603050d0e06030c07050c1008070306090605421201050d05100506010c2301050c0f03150604090c020f 72
    0xd000780c600317042080040103181c2c04240c40a0707a0f4404881c1c00f50f0703110402c8a51075400b400040710715003400710700140c2d6080001c0c0342900445040d80c03511405210100707426400c0311040d101302e10007001c0e20307201a900c14120798042c0d0711000d2282400c20031181c44200e403d00d0130014030700748100709154840a0080c80707020040540b0798256480d100000c0072046011074071030b01001d4002545a0340125004041000030700040700c0d41000a004124605481400240f041e13405527511400701e49800c0d40850b244450340103800944001404903001c01e050340403182200c040709040c00555402070000440c002e01e4120003410442040700c0c0190715841c3e00c103001a0811010790050f41f01e081c040e504c0e01c0c0003c00110702d000303e8888404c070005143d901c0c800144c40c4c0c0d41e1030b40402000e5807515500301c4200b150402a06041c1c914040c005c000135a21412200c20030700c9540340c01b4003060818000159400c0d4510410580f071074024201034103143d56410300c002501c41800c13100000d41c004050302d5100e404100207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 915678732 1250 915677482 915677491
    0x6030311120406030506060d0c0c02011d2101020f030108160504051306050702070503030a0c061112010902130312030c0807080c070213140f01080d0801140f0d020913020405 76
    0x180c80100701c100c0c0c081810780b09038410b09041c1500c03800081c450342e480c030302900d1050300034040a1114101d110002442c0188501080380880d103816120404002d45e22a03001c120100502100901112844042c1d41030030542c0544103199000c00180074400c401c03030041c500a21185c002841d03102c0849c8028021400c03982c000d00d000b0761400080080202c011070314409081c0d002000043c1c240c035450000c038180034241c1c001a4040c03200041d042d00c9250300c11041d0300500d020321003c209046400c0414000e41c40355581d490303005908100140560f020036401024520f03196110380351711660341e42c1c0b010242100702c00607102080daa1807150450540184180d50300c48640d141004981c030340300c14000d149020b034000207401000000821400003001c0c0d8440480010240c10000007490040c1c4450a166403d0207401120300a000d110b40240d4080d10300941a50100d10b440170f81d48581c2018003948101c4c80046a41c00700080d940718004d40c44440c200c40c0655140382000c0848140c0e8014002540c0c0040c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 915679982 1250 915678732 915678767
    0xe0a090f0b09240408130e011d090a02060702060a0221030405060f06151c020c0718090210030c0e150a1b021507140f01092904030e06040306050a060303 67
    0x807200e410105020181d0b4003681c08074081d0788402c0d011b0300503982d904041d0071a0316149095800490350003401130904600c0d0f982a03004041d60799407144095252041213800039000081400a1070040ca070080142c5000007480c0b04a5100b51840c0070307084640c260700c611249120034000103000030300400b440b046070300c500004414010740c2080d070041801100c110700141040d5001140c5865880e400c0f100c0f114040300070110031754582c21817080d203948424061189000134038a06215040c46242805141c4d80300e5001000101903a007840815401f0308280360003203040000c03440b00c040c0195203401d590000020510318140c1c807003407480006805c03140003011600c084290880b0300700043e5610080c9036901011011696140d03d4580380c41420700e1034440740200e01d0302840d8445161040d056010440042c0a461030043c020540f011400723681a06a20a0092034100e50000b80881d002d8200340e40280b1014001924040c0d90351180d40490740e054810400701500d525040060607132054000360b9110102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 915681232 1250 915679982 915680023
    0x604020a030308090f030d020a18060e090a0902330c030304120e1e10030b10140d29180f0a021c021201080f070e0a090f0b09 55
    0x250006a0812454800141000034040003d01140828031483c1401d42005040701c0d21401100416006504840741c0d04000031008c032212400c020703da03803480084a80680310001d00520174000e01c401001d008010300034040c2c50f001c00c100142c40301c101011034000004100402600180c058050b02403081e086241442c601b0700031803010110100480703070000ea2081d200301940b24050820390b1a4401005003940c0b203008007a09110b40b00400c5081a4005000c0b29862181e0301a101d00f607003110603040740680c20100b1b2140d0000343c070f40549003c0c44090301100003181851012004030080c0d80100321540303075031034401e8100503102000d10391503582640111140c81075040d01c40c102140d0020010824440c10944030046920049140e04803250301e04111001990f100c02801c47c94040d511424030689100403610001960a0010841d035041a0414000c2d00720f040c900701c4403255001010b40035078141b41e95601130764009000031030307a07056180c803a154070036503880c040029600309100c80000d0745171880d20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 915682482 1250 915681232 915681241
    0xb0604120b0c0a0f030b040b0a08070e07021f090f17070605010e04050a0f150219020d090e150415060206010501020f212809050a0b0f0a2109120305070206 68
    0x100340081004c2e4490720f0002500c2c1014400200034180f9088241c3d001024540041240100030602c101640e0020300c4c5020242caa0300707012a80c5906c207000d444c00340d02071030004545811583d00000300340c5004100e5801c1d1440d194541d0314490901c9014140003540019021041240350b0140300d0041c03d42e07014042d05407500c0d456240c1c9814000380300a2941385407001d44001c128a40381851ba0000c00680215140e144589038640361811003070858015200715003c401c07010740319210b080c060f10f031403860101c15a1140c8041b042440c00c0800d846610903201c8601d00600c0005907121002850640c2c010441e651600c000a420103040320b90148554110345400720000702e503080ca11245c14100081e440e51144040e0900400899500910003111180c10380700145903803100d86542911005c59460301003981e0f0740320550300f0b03200e100300441e0a80020720030464494028164540031004a404030218200c14000300421154080d904507031100e03a080040d141c10384d05208250703000c1e00e45e000030400d07800c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 915683732 1250 915682482 915682487
    0x110708120315130e030d0b060304052505040e010203060901120c032405040b0f01060c11090a06120f1104051e250c0b100b070303020d0b0604120b0c0a 66
    0x200800801000d0881903114442c0d464426110750201d1400c201004949090304003652030340c2c010710700c000c1031a08001490400346030010490780126072010082100c46110448030360341e002d444008144420003540001043c0d155401550001131200000583e00e25080d0704000304500182c04c41c0c040980c042050354000740d903100c0800e069a030000074003c1d042281110340702a80026084110000d8200000c0c4410855905a1507002c1c841e40620034205a0b01e03054110b409801038107016180031000b04001240d41081c400482c0c1100d5070000224405484e02010741405030508401c44040c02c20241a006100c80710602140302c80c001c44042c0418100800d0040c0f802a00c1c1c2007a8110041d0b0801241c0d02c0c0c60b10410880400c188506a00074600300010040c201090b0074500780c40007001c00c0c00082000c0e031010307807800583c0d0325800402e080071001c0e1400c030f0007908006180c003001540c034140030100e45d451001400003004005c4c082d0b84e02000030b2402c0c00003006c01404441082c8400c0c003030b00c4012078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 915684982 1250 915683732 915683737
    0x50303070b041704030f1106030919020f04020c07061d060406121b020d12050f0c0334180e01121e14070f0e0403051b0d11070812 57
    0x241c0100303245500780c0781c9090403d0028094007083d440c0d143c0c000760001c02c1244400c40301c00880e0241120841a0000c0018440244001c5541c50fa1035006100c58161204844e26003545d641d001601d00754800c071003140420300703d80c003800452801c0d9100366800c0101039071003030340041c100b158880d100c0502105100400c041d4040c40c00344400b4406200d51443c5411000d070321520f902c00c190381c10121892000307100652150506d040b05000109615041000d1001c43d0050601552480701c03903c205942d090301c0740a8542002d0980060214100300548020300701305920070300e45168010400d902d0903d03000c0588040c0b4607044841120310303840e40802c5071031a0141c03218115010740c0f83da442106081c0c50600b4488030b05414200207003107840880f40601c09400f4104500c4400e00c1f040303c200070384901543d40507602c5445002c0f204c0a00100040000b1b12a2014264040031940300c01c840d40f80d854482070415411040741000150149440000d49600b00b04283c010312489028000e25000140d11840d01c2c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 915686232 1250 915684982 915684997
    0x1e0c03051207020a0218150d0503070809010507060c08190504150b0a030b040c030b010807080307080a110d121109060d1a03030304031e14030402091b0a05040e10050303 74
    0x7010280005070540e00038040b101c406a8000d1842941c259844589115508103645081055010381c6e82d980c10b5040072100306e4145501700e802141845041e40d41c00c0c00640c8a040c640381040001d00103900050064000c0c1070103101103440e4094030345081d8001000300510122030b02240d50600003807201181094009005840310040085007000e1090042141901c0d954070051a100b0850100b005205810400c5000c2c0c9126034440000350742d0b501d85043c3d480e0081d000c0e200b01900704020080c0040c40000060400c810941401d03448140780b003200d1410300c0c8210070240c010641c024440e120b07078070780ca21a0a18000d5034003043e07800d0480b02c00101e070060081144c100c01f02d40da20400c9070b07080a54802c00c2511030707600404480c1e41c0d280901d4028422701000041098540300b070400d01500c2070184512004545040d02000d042d6500e80d001c0010f5000c001c1c2c0410f041c1d21780361403400d92080c502c0c80203020410164031441d03580c0c0e241082c0610003801c01003c007000c41c0c4540c802070006517000300480724903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 915687482 1250 915686232 915686257
    0xb040503100207150c140d06050330090a03061107060f1a011b0b01180c0e150904090206160201080603060105030a1b0503100b01030b0d020f0d150c1e0c0305 69
    0x66a40c1101030f103861805803010300b074446e0f0106224185a585820000550320190f05032240b10f4140300301c0503181804030100f070007840c030414501800f2a20110250038800c41c02410400d199a070b9840d50350450304d2140014610060000307401051003218041e0760041c0710b120004000f800d03552055600311820420126041180c008c150260b211070b26040d00c1c40e5550440d00b981401d503590070701015842960a41d41c1020b5040621064003d409800c80503052200a02400c0309030066405200156000030b4031b056002d40c2d60002c0001507158440544203440340f018022003429098000507002620007000140f10780d001c0750051010b070b200801c00754a0264030041481c5e0f00e0701c2d10308200020300e215070000d58040c8100103011000c1c82d0f241c1c00904031864281c078200040d80311002441020380d001c84029400150500f00702c01d03a030805420800956010b541d0320103010f040c108040c000e50351701c46009070008030200d259020301d400131201800a007c4e9400c1400d5010344d155405400e0303000d50403241c003c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 915688732 1250 915687482 915687491
    0x300804030f081506161a071b03020c06090315070e19210221100e030a140a050904020d0e070608070813240c03180302070b0702060906040b04050310020715 68
    0x82c040180c4440c5904d0680c072003008041886d01c028240030780d0a0407601103000566001004100148009204210580590251806c13051035010b010320790f441f80b50070070f130148280d5101c0050000142c1516000d010144d07038201095074003000300314280c01180300f04a43e5068514040160500c810901104a1003032400710a0079045400003418840115500c0c0601c141520742d41c031190203000c101200b0b180040e1030200080840300c0000b9a60b4082d90b01c010700440d240e0015208104d8540010300112265480e00d24a0f00c80e20318003190980e08092007201d02a511049103940a00301071046001030701071440c1c5800c403850130040040c0160406050164030026042a62061240c0442e00100c036000b5409040003990a6031000380c0144545410310313002032316104180e9514150400c20b6400f0641550040000e41c1c00c00c0903484284e801510100c3c0e000d04e040060040640b0360f1000351008203204a40b19443c0c910702000c0c1410702590000ca000041d204202260008980103620040668002130004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 915689982 1250 915688732 915688747
    0xa1e05180907030204080d0903051b01020a150f0e070302040b040e06070c06060506031e1b040611030909040c1e0f0e09010e01020d02071103030307020604300804030f081506 76
    0x400034445d5070014079950284083c02e20280303402511a500b1280301c1c1084900c0c80803042100041c491914101d0790060308010a0400480d95404c603030008103602c000006003e0b0046031201040b203443d2545040b050304203500c10019840d2501c14509104000c0ea8180f14000080301403031789951006003800180143c104200040c002c0c580e05c031801030032024183d039540b4103042c107002030700c4558400c20401c901c00240028020380e0301d040c2920300c003405061074a401d05007401c0c404c0c1c402103050761005099100900040d03400d66240c42c0d10398002d0f03020f9180c0c07031919404d000b038000c0c26440390791100341d60704d008000c10000007213003100341000c8070145148003140751a05040c2130f000d0640e4107035540c07942d80007140151990f00580c1c01001d400d8429071040c5082d400c0c860a240c1c403400100c9400e805a0010400580415141042050154100f04050480340b02c103d00c85401e415188801f81d0004a180040104064001000007072090042c144564103140070310300311245110242e4030314040c030404200e05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 915691232 1250 915689982 915689987
    0x21f090501050d140a1e110d230408090a0e010e0601050705010e0703290420120a12030501242322060c08030115090b0a1e05180907 58
    0x80031000050a40b940b514100f2500a80141c2102da040c1240258004420184201c4501c21f00111440c0d000140f801c2c50800d034a280010b10340d00e80d4008105c501607016034915562100d0041c4075503c40c205a07502c031a100d00034402071004e80e40100000702600001402190540c04046034080c009103000340e80c0e00c450b86421800340a4444500905200b1f002020007044a046500c5800041504000c0e240307001e2a5500d420120098401506d082d9089101d54400074146030003903440500609544040a1000340701480d00700300240c103840925811520601d8107525014071401405145605461001160004810301c130820360b0b008140807a20310001e0a483c0000b048052500c04c28200c55145d01c102c4142021070710355100400380c50000c010021805500844401080b1a000303140241140c1c00c1c9060300d20f000d84411404800e00c00104170001d403001491004041c426a41d60f9603100d0040f01040c550034558601039000c0c240030701444010000c408000c1c3c0340c80c040c042201d02c442c0d07d89984009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 915692482 1250 915691232 915691241
    0x130b070512090a02030d02010b01050403020906031623010804031e090807031103070501020601180b010c06050403031d0d121a0a080303150d15051e010602010603021f090501050d 78
    0x1c5000000c51000c02c0100c1901180c6031482c14003d070103541851581070f004030700b2240303c1d03030448e80400d20500051001d801c050110942c000005401c85080c00d114404e02c0300d20100c070b50b11042802c9072080624031154110a544c000820b420b09200c000fa06059a025125603100d150b81814542203140c51050070340f180450307000400c00541514421902c9040450480b560540000d01034420403a000a055100140c164102c684120600d000610000e003290098100e1a212a04004c1c10b004c0d02000b0071114801d55010f140311f1303100016131041c001f000c1154403222100f443c24a4000c44031940055402068840c441107180c50001200b80d416000100d2581c14003400c2500106411004144510300200650181c4103a0041035003d50818040244042c6000e00007089410800718802c0b6008440e0407058100c008110812100c50501c55280070b60360b13090344030301e0040c2c0d1501420800d504000c000b4459020045d220180d0540280c034000c0c00320341e801c1c4036407070410030300140c2d4040e81714040e0f10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 915693732 1250 915692482 915692497
    0x40e2a0406121101120513170c031e0904150e06090c1b0a0803040605180c030a29090105070e01080f0615070b04050105151f050a0905060310140108130b0705 69
    0x4000328188070381c091244400407042141c400340234107400722028010340140e402c0c0d8400d14004520b4503100c019895000c400306055802507000501ca651902d41d81c41c01540d40d00d07010302426090080c90941c500c200d40c8006094a0701407450ba100344003141c1d4140d41210300c1044036801d41c4050000707004046250112917400506044004814001004441e80199000750340428041c41030a08001e101078881407800022070389544409a942c0024bc4448000148400036030540b01040614102e51070014004582c1c0601696454040102864100000170a1303c2d500b803070910018500130b5140e182503100074001c94401d4403501010640008201c0c101c81a20340d0004100782c19040602d8110301070401503030302c1d800200da440901c541c5400d0041000c141c6012039840a40c20703c00e4880280c40d940d11601c2d407001007142d001408107107521203000540c014880103d5040820303107031040d5015075400014030306040100520502c40e00e003c0388100c20740c0150b00300e850113501c0c0d1680130081d1254415180c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 915694982 1250 915693732 915693767
    0x1b0e1c05150a0b0a0b0702090a11070320070605030c28090e0105010f05190203310605070203030403120314010603150806160e040e2a0406121101 64
    0x81014000d0041011160103550b0300d02d000d200111040c01007120010075030160a01100341800300c500940780400c006138100c240782400244c550b1b401c541c0e501c102d5000f80303002e5020500810310b4030018840442d40e0440c02c0b07084000b405031a41044801005031102810600032580b0119002d052040c00807070102d10360f218040c40c5101c0001d1180b02401001c2948180006810180c1c00041e0320750007122554416030341a590746180042c2038981001000c1c5001643c82144170a1040007a0740e2407410030f0f000c820740400b103180c50b183d060041802d06000716030000300402100340011401a1030010644042e00d43c050140c807080b0314401c0b42100280010003c0f1041c8000d0240001001074041d8810031702e030a41c0c10410744416403207544e410754643c0c003a920104603203445503480c0442842004040c00b10207000b00302213004c83c8200d600030300d0300d21040d00402c1210300b0010070340340c144100481084400b909031414400a40b411a010403002c0c1843d101420101da403078201441c83e841520440050400752 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 915696232 1250 915694982 915694993
    0x14060c071e15030b0d06020a1103160c0503032a030d05010f0617040c060c14060c0408071202090103201f12020403020f1002031b010c031b0e1c05 64
    0x205060311000a54403844642d0309481c1c400064451181c013030200c490390080c0502205800541c0c42d00001d43c4156098000c012802046440140c4144008d0030303241c4840d01c25140455043c01e2042c040c038001c1d4881c9200703078000c10020248039445002c241c0442d202ea04202144290b20030402c0c00c40c0304540c28090700c246403000100352101e604a150095076582d642d14a070940d403071810012014420f440284c0034a42d0b60384e0070801c0340e1240074407850043c41012283c09281c10b0011039440c000341951018011a80440c050207400400c001c514004c00c4150040d80144550380c01241d00c2d00c83c1800094030326200d407482d2200c5002c00030b0002c40c44010207002d02c0f8101044851003c0401c184200000002d0008042c9002e00600c40c020341d000e494005100c5440c40300e42800b00301c900320132060780744150b0005200c8092400121f10001c001903000701e0010801c004c04800c000c0442e03c07051030101a03c9001c015061085034043c4540e920282c09a50241070301c1c0c801c20345030304c0880101c00000c01c01e00c00c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 915697482 1250 915696232 915696269
    0x1f0e19150f1401050f0a090f0b1f0e0102030a080a0f1d07030b01050d08090603041a09011517100f060512010915270c170d0206010902030114060c07 65
    0x41e03900c4030b2056059800002c00e5641c0f11000c00000311090120380e0341c8801c04403424000c0d540d9607841038a20b41c5c0b110b0400144003501c8000704491445600002c44520000700f00490302a8000001d03141d404024400340d0f00c0e0045034034000e0110903016103c2e01909075103000340c00c45010264081000044a5520150140c48030b058503a51080c543c00100ca000545c84d00000f154205840d9075040e65501200c514103191125050112070340000307000740e0320204078145a18000080320401c60140d004500082080030107040041c81c41001c650041d040c1341848024540e9081c000310320521030900c00480410400d1038810620068045504a03076880b80301260b00f240c441405501280000b480381c3d01c6080307075170000c0b000e01c401c880c078010a4001c00c1d5403142003500c0240803665050700062150b0f00d803440888d1510039070625000d4000c11980e0b01e601c00840344001540401031540106400c01065143d07604050070b2070f10316040745242500809000c91b40f8694a07005002d1800a0144c0c021906600400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 915698732 1250 915697482 915697511
    0x3140c06160f02150606091c140c4209121912050403050a0303021209161710050c0316030605010516050a0b0106021f0e1915 55
    0x1066403210400c0900c07441145140707000300d821005482064000c0e1040002003040310300e4002c00100f03003a9004008000403181c603611712980c0c84410b0040203864140080624000c6800d0020301001102e9034440100315401ea503604004c40980e1011241c0c04503225180407602d428032800700915103c481a225141030301306090009041e001c030b02111403064140342c030316000c1d40301c24180c80318042980660500c500030441d44c003a80d0030018010b1510601d4259262110741c2002d00d05401200042e80009d9201d01c0d0701246c805c4150092f0510018052551358551440d0ac0e040c880d10403018482d1004144020784507041c0110b540b4440034900600480c5400040040350b5402140c2050f800309101114209281c46072058005030740e01030710384a2800c00c030000801040c00d100c000856a5214484092002a64404141e0b00a2106030020025101552082c1e605070701b298082c003002c1803506541400400c0d00140000c03540301000303900300c1481e20604241c6107420795100904030050420003202036002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 915699982 1250 915698732 915698743
    0x30f060c0307031503150209010c06020a12110c07061218110907020f07050904020604090207030818010c09030b07020304081c0906092601020d0903030209030c0402090d030c03140c 79
    0x410780d56082046141805030b10341c242451740005440c4114440401c0c5d4041c210354000c0c4540001410022a900003550340e91050b40c1c010740440d40010620680c1c020040443d0007070580c0c2441060f46075040c000d04030360096854049220314010400002e110800000301940440200f08001c130b01003204851a0520a40e040c0c0130344481e5016082100002c0d5aa80c404102d50303124046101c090401c072494007082101c0c210001e04166400762040000081e6290581300a100040c800c0c4c4507041c15140c0041003812005036540f00300c540c0c3c0d04284416080f80d621400820640364000310820a03500c8100c1c0482c03946c0901c0d04000124800c80303105580c007500340740d0b00c401c1d10a000c1d510203001586900d012600c00c0c03840e00c22000c05071400c1c644017100e1ba0702000c00c544d00d5001e140005042c02100326030241500d10800c000d4021a82c002840c10281c03c0500401c10703200000c2d2020340c40c01d0b20300004144107105042c03018081000a9054104140c42020703040c1640100e1040c06803607245028440740c480 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 915701232 1250 915699982 915699991
    0x40f061d090f0c03060f1b0a0f03060f050102030904180f2001051923032e061403040606240806010201090203030412061d030415020606090a0b030f060c03 68
    0x42c071698602424040700003074010b10300100500a0102911410322070402202c0c080d02110a54514482040c1106582005000d09210320b96941602042034040501281c50380d4008034020014103000340420313600001158075441040d00e000882192284001d880200d0b6007100412a1500318444828000550803002000c106000c001d2100c1242c0c40040d41c041c407543c610002c03a0045840d07586c42040c090061949082280c102d01c10380c41c400641c04200690044958183d4601c00e8002c41c101109442c035032100240078410a041200d0910b54040c0c83c001d80e4610b00740101500000007070421015400c100c00410315842d0f080a61240300041c003100e4070541c42104c00140582001509079841401444510381d0083c003e103141604044014920012404081e6921170700c0310484042009034040d8500020083c030042c5898900780400846c400820700e510381c08542c082070a2011507500c6c2e4148030b80000044e600050b07000308007404681040c007424201200c13409104c0412074035244000c01944138 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 915702482 1250 915701232 915701251
    0x70506130b0103060506030109060c02011b180b03091e0304031703040f08090406030b010e010603060f27061206060f0609060c1407030813081b0609040f061d 69
    0x29a980d10445280142014401500c0411034400400c045401d590000e50403403400750006c82d040d00e445c0c4031142920014510700380143c3d510001d032000d1103032004c1042001e502500d444400c03404030b0071107400c44404e18015048024800404100100b20410109034115107a200c5038510340400f142154a035009844103460034800b920b0f0000c0c2714613204044a20030340c4e1141d00001e0b08001034484c1a840e810010140b500956515408404107101140543c000c05040100145541c10174200500740c1705242d009403099507107101c003070016000c01c4104005070740207c482c0201c0c4c2c1180340030180c0034141541c41690900c4c1c5481c1c42800f4003072103401500c00d94005145811a070f5075524401c0320365100750300c6400c0c0010003d828520001c1c0650008003192800b110032100200d0300ca0300e902c4540d500c840c0d400741c0640808042002120024000d6181c5400c20b1000c02848000f0040440d0541c4680d00d5000d200d0760340e4084031030125410750310481c0500003110020f03c400b500d0580d10a86001d0540312000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 915703732 1250 915702482 915702493
    0xe06040c050a140904020c0309100305240103090c06022d031c06170a03020c030114010b0a18060302070501140c0417100906092001210b0a0602030705 66
    0x141864003030940000c60555840d49001800a0116003070258030701c0da1681c024042080c880140d0710b60000d0641200807502035551230801d0010415110254504141414100404c00c1903400d46c10028071809000e02d101207600c042642c004030300500000703c004056008416020034070170390015214550103403aa1401d5081d210040e0140c06a400a6404030074944c801c10800c200c008103400c240c111001c4801e03002c42e201d80c03200301031202c018090480d90034507031143c0d0344103052541c1040243c00e92441a00208817001140c00540c0780f1110500495003d04c40008018019070f1088441ca4001e042c1d4102c15403c0320744842c030007006588000e000740c13034960034203800041120059000d0b5000701c80100c40289018508101c01a0407200c10003c134900c0d0043c2c0141c0d248009481c020300800510951000401510798a496003903800440003600c08003244183d24200c03660400c0c018801e62609012901c601c0800d03401007000382030b0742c100c125000f1901000000322a80c00001609ccc096102c0e009881 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 915704982 1250 915703732 915703741
    0x3050c100606081f0e27010c0302090a0f0e010302101b12020106090b030a0f0c1208040f080a0215220e07020d020d021b06221403031314010e18010e 65
    0x200c00400d00030300018286040c08200c1c41010b1000c03101c81003000741440391600c6c416544540c2155540c4076404007080e00020001ca003441e044005c0c07400f82c4040a102801d080c100443c0d0210580c0500009020f42c544c2088a0007450040107e034604240d038011803001e4414501d0a0a000003640b001d8501540c2480e40119401c0d80d280540da480c464041c0c0140f09200711901d4111944d800d080b800c0c0c488181451022441009981e11001d407240549411035440745003110040304140c855000c52000d401203102e00d030041c0d0b40c000d0a00307000f80c200e50016449603080d41000c1c200d0a80390030551036104c441100090b50556181c40c0c030b07118140e02d409581ca03000100300103984610101c8582801a0011000070091888441c0c0c0b203a007282014201344d00740305910800d01c44c20f414000c1000f1920b103800600700000303480310000790283c2d10294055410a040c60191081c1291207004d1030003255500b61000a41da486000140745201d40201201405525039103214030070002030140c86ca03441c620b000000e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 915706232 1250 915704982 915705031
    0x501030c020318100302070c090603030e04180204110408010c0305090c0901031e08040905010b12480304080414010c0305040b09030a051605010e090c030403050c10060608 75
    0x2c0b03440c446030f0300180f402c440d840390410400d210a8500307481455820700103d000f00700043d00450103442401c01c0002c00034294240545003183c1e03030080c10b01c241d040241c0302030803180603064208400d5044c0c5002c901c52012940d192010b015540100740741e5842c050b43c0085407030b410f40000d0b0086407008196405400034000b0b005480c01c007408007810a140101620b00c81d0080740105c054201d0080014034200f83e200e0303028009a402c00c2c5c3c0000c43d418000303c0d860301e50384681718803950400381403c00d5809055400702e14150740905034003040b0542148036107401000013100620700400b0385480807070756a40340514007544e09410a00544032000d00180c115001940902c400100c0f00e9015150641000d1030151a0800d1740d22540c10350741c06002d92144c080004034200a08080081c0c0c0111a09005081200061098048040326449205018140208081b614003100e0300940c0525080c0e030748013880c266003071070701420340c101c0b0801f40d142010005103168060344490140704100e04070003c901044440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 915707482 1250 915706232 915706237
    0x1403040b0105130f110c06090c030c0f010306050d0b040512041a091909020d11040b250b0a0b0901091e0e1609021e04030f060b01030b0d03090501030c0203 68
    0x203126840c0d5034018840e601c1c0060310400c1080050402040d4007400121050980701700e862001c40c00785021502c600503100921003940e0014a05000300001c0e0250710007e90345d0400018517a0080c5240a0000c045074481d2f00300d0b201901024000c1800b404243c80c1042c00b2a40480e0709079031750f004100c000181824224101c60032241a1104281c03035040e01c0d21050781c294050044980c0c04210105040d0f0f080640341c04000c000c10540e00c00503190700c26000c403002907403040c0c1d00c00907401c0b03020003040c401042000c0542d1807803031102030101c0040f4224907420202e251010030203400b002c010810010100201d8000070701c0003030309841c0244c860360390310641d00c04d0b60082426003e241c3e00018070381195400326400150f0051040080740c403510a103040c0c2c07171401c0d2107a4004005042d00010580c01203c100400503c051150a88803860b140c0365072244055954a11801801c0c16102c071801411a882030b00030b5082050001c00d0070b2000340c1c46207805803040402d031180c6800b0074280f0410540882c008000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 915708732 1250 915707482 915707491
    0xf0c0901060c020f13140406050a0b090c0c0f120a090b07030e24120a0509030408100b0a0f0e04060b22090f1a0108060a0501060f03090203070b03161403 67
    0x8803910b00e030840d54208890800c1d001e01164111104441c888014451030042000c0f009119030b00344c4540c01c0500b080c0054400081c02c0088050418018803502c1c3c83c2c0405171a0302101c403120203500c82c201002c00c1c07810403c0c0e140070b884d842c0c46440e21600c9048a2031008140d030380d0782c1d91580120315079102c0300d0140030300030517002601003140c1070594034450408903840880c80315880c103010b6220b0f0303481503100d2547d003000c80a00c40c0700d04c100c0f0411440342c84074862240c2050b4100011402d007450030a400f075690b0201d42230341d8441c580343c0c58203054a4a800100b03e002c0c118a01c001da00301e0f81c440a0002c40101c04581c25900141000d940c0040c074101200c02d51003482c0703521145400880d509600038060100018200c80c41c0560b10b6410f004030b115200714061000c0050703509031540d450203848919055000d01449030070307840c22004001d090341000710700741c0c1d01119040109844001c1e00001c0c2c2401c107268082030f4122000001c00c07030340898525084441203029264814843c4240709800110b010495 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 915709982 1250 915708732 915708737
    0x3050f010b0901050901090509010603140f04051c021501122f10020c060708040312020f070e06060705070e011509050a0905062b0b0601020a111005070b090f0c090106 73
    0xc0c0071143d44920020803000806041c44000143c0d01c0e0003280074000300342c1c4004002550390f08031502d906005d040407500a00c1c5051403a5007414681c403001e0701c0b8105081281c1450b8245031803515000d000340040b000344810400c2a484940c0d658403520316041d5402c00464001101d0320b00903080615081c044070001820324208940c40300c0d04420310107240b144000f154194855240c00d141541d032010018209244100007098890380317035144c0b042140b121200c1983c159042020301e4a40000000340c0c400c2244c2ca1206c0a01c00d44d00c0b0380c00440c0b9144181c03034001c0c00034091701da000300f10210180202c5040710304050394a00c14581520b030403216040c65000e4681c3c80f00f5840400c201d1018542c00090700440c0040c5880048a00e03526103101010040340c425000a80039640e80042c4424101c13400d0b03108a0030700191051005595842c4030b51484500440d00c00c41c50f80c1c010803c154802e00588601a070307c22024400ea00340040724075950107800304a0803c0f4480c03040540c0c490309011070403504079030154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 915711232 1250 915709982 915709987
    0xe12190201210f1a03071406182706150403121b050a02030d0302090907030e030c16080708030418091a07081b0307050403141c0f03050f010b 62
    0x26030044402c140144401ca14030266400ca4140c0708a0910404038510880000002c4110161402400c0300418038041071003600705110810050040310a9110141c000700d07016540c500000b800784000d050020b903200d801445526200303650240d05110003580150f40343d54070040755a00401c105901e0781204408201103028441003001454001d40150140301074103004464450f100b0512140c0c0c175400e801030b9101d90241d0307201c105600f021310801d00d440b80a89019403a00c01428082580154007801d500b017055a1803c1c01c1052510034426a15001c5400e02502c03003032100030744003030302e504e200780101a0580501e403800501c03a8000000c40d422181c0e986a001036441c00c07908400e0040c4071518003900c030400880203012119110748101803150340c40e912100581d041074100b10b008129a0030443c101100108107000c411034110741680d08895120f00740b4465400c9900c0078500300510342c0c030412461441d13001c0000d8006d0304080c0d10707801d140d100c1e0b504000315501d02c04200d60240f400c0c8140300100208 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 915712482 1250 915711232 915711283
    0x20d1a370f09050d05070b060a060e090405010f0608030c1e15040812040c061b02011e0c0204110903100b0d0f0212120408010e0c10081305010c0e12 65
    0x940c00007a11181c0c190740009003121291142d138200800516548001500010500100002c501c50640c01290a41d115501c541c00c008010303007440301700c10000c0e100f00044000601004802d4211840550900d01c0c1841420f9886003099a2900224080030f01401002820400d030404c002081104851400061901d0b5252884007540e0b104003400c29102e400042103501da07540c0b006040c840c012403141840c102070601d04080282580d082c2030913911f0b140c07844080500980c0e4010351a41c420200f00d201000d0307101d0740440a0f034503001410002504282000c21030202210301d1030140047c450240c0540d0203014070410030344200e9014401c06079108454500ea030340820400101d114966102a00380000c990049040c180b5000305108015080e000006051101004c00e01030020454680c6000f0010b6420304030000da0b01f401c1040318607007000b10900014103048a5500e1252040350024000c1000e284040030007440c1e0011a00c5842c0556181c44d0041a4a00001900d240406000400d01d0b041c060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 915713732 1250 915712482 915712591
    0x723040b01050f030f100e0403020d12020903010f02040f05330c0a060903180e0105060306030c0a0b13122102070503070605031614040909020d1a 64
    0x900d03044240c1002814088448071002410085020300240b4001e100c16190088000383c801849800c02400d4a940d1801d21000a40000d103009103100715041c84c070782d19100b6541d0b05000b40158040a0350560030210010385140655000300155030011000b074220707548074410b01400070001c41d01702608403514a00910000e2005442500c403189a43c03a01c0d03e0034200c0c0030b485113014022001601d8086d501d002c1c1c5000c0603000010b00103140e40549000e8486442e01c41740110b074000500c5040c0c080c88000002494a81d401e10005005031401000c6c081240d488241d00c2e4800d400c001075004050102003404150318003502d03600000950712180282c46000306841c8605e01480d9a0442000e61080d5200815960380600c007c6016020b190340340d58481c50a145019080f84401c140c5000303101c400c0c01c000b0a07141e041011a002c1c2c1c0d041c1c01c1c0c0460700801c503101103400d13403546d01c1d1b024010764041385004103480c42801c46070b80100f1040b42000d9144c40815842c0e5000b5203100052440c2c1d581c0b00020700700340d45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 915714982 1250 915713732 915713741
    0x312181f0f111e07021203122206050903070501060b041814040f0606050301180512030108060f090f010c091706010509070c050f03030a02120f0603151512010e072304 73
    0x210802c070038248551540031420140010020b0442ea40010402003404c210b40e030b60f4680d116005050032200c920030f4204201804027040409003c0701d40366000100c540c00c0030011a00130700d60140081103180d945031140b1000f0341143c01124811115400841911180c0e405004540b41140300031844c1c80d29242d4460107103120104048401c96200c1c400020141e900380700d50030304058800307403004200c0e01601e03242e42401181905510008030034001400071020018038640d005c00241032114660705c403c140030349404900081c2c246903601f003001c00da042580c001400c20407500c0048a204540088414003902d0300424001c0c180c000320528001411944a03204071541980104259809402454001404c50b03200721900c0c0310040d000034084428680d0340008035404a400d9070f50484138242180040e403103100410355444a1280c1e0000700f210406407818088000bc4000c1c40300d82d098202400c007030b02800307132903414508d11b002c0c1940000b11a62881564203030301c1c030303400d205000c0d14241c04d007040000d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 915716232 1250 915714982 915715027
    0x506030c2203050c01090b1608090310060303200d1d0114070804050f0a0308030601030f02041509061e0503041506050a031b0b040302030312181f0f11 66
    0x441007500d21241da0402078119024600a101074418203928030000340001c1e40356840869401001c20440e0400c0c04011010580c1320390040c1c11079034600d0120700081c5405034000c09064070500c0e00c18000105604403000306201d2940c00c0403503c12501e245145620351100c6d00510f00813880282d10000d0103825040066164030050404448803814900c03010140d400102048400190000302407119180100301d803000014211401070400d030440c1d4442d12113001c09800181810b403121a070340100c080503019a0080c1c11051850b040e15003031100000c1011450740715007804a00d00c80981030400040c0002c096060300c542d210940b550b05c46a075045114070b011b105c03007540569141310101c0c2c90360300c0b0b03803403a001140203807241c420b00032521600c40050030b407940c407900c5414010001000140c60100039103544880b1082401d01c2603803000f008943e560f1581c039000f51140152004205001c202000810a59904482c20848034011001c00002c1307507601002c0079401401440480c40001a026051504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 915717482 1250 915716232 915716257
    0x81506041205011409030702030a1101090302101d03010b030a1704080d0207080106080c090106122d06080d080414101e051f14011b0b06190506030c 65
    0xd080da204681c0000755441001250310f80d4507070b00c802078456442440aa04003440c0f42c003840c5030400560009540b03081c1c0300002130400d1b42d10742907184180c0c00b030f1169038011034002c3d05840050b43c5107100100303001e82e00c2c50540700010b2030003d03a8070141014410b0381252080500107150f42205511000414644e041070f4582c4000e04200100c2d070f50f1010b02c00700711391643d0f41d002030090300e08116a007401c0d20050f410041640d44080307071070f86180d5a18400b5604564181c01d01d03441da080b03002d940380d0103803450a11506460103180c5050261406050740160072048004c0d0411070f030713915000780e03d854a208040440000e06c030f1002050106041d82900d191810300a000c070358070482510902c038107650b940962400210680000004c016400d4000c1d6944441e645c00034510390000940c0c0100001ca481c0214203206012000c16480da9005240c040710b004010110301248042c10b2070004034281c401c07189a8029a60303030074000d0180c5410307032208094402c01000e023411543ca07000340c107003180c004c00300e40c01c070303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 915718732 1250 915717482 915717487
    0x50718180f0204060f1101020703021207050114040c171b040b0111070305060403091706160507051510050306091906060314010c0f11031b03270a050907081506 70
    0x1da841072440108000e02c61525201d446040c4108003801130f081015003c085640104544c03400a40c0c0450400b581181804c1080d40b56115820300c0b074010060121491344010080c41030006002080a549088481c020340c145002038280d00d503991100105090044466141c8061a400e80f400c0d4019025080062500f84200b00440034140d00e031251035802910250004020321041c9a485955034025052003409440043e01980344240e072600004c103821502d20310803183d1040c0603c18411a03e0701ea030404121a15002561040042a84180c8240c400c000f419400001d5034100400e20358424840708025141c01d80400400d0b0001c002000300454903595521004400501c0c41c01400710b403d1485800041e44001c180c1000d005240e000c181c500502500c210981100d1600004a070082000e072034609036510b10070348145186000388840c5400896445e900c9401c0c00303031110300d0001c85600858042405950320350038440d69101c107450303060000c1c0c07240700010388180c0c4021512001c0d4030040d2a191 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 915719982 1250 915718732 915718751
    0x3090e060609150405030c011707080417040906090f0912180e0f09210d090c0b040308190c0b0604020304030c051c1805091603092405071818 62
    0x107026030f500c40c1c0740751100000411300348014142001411100902820619001e441c00a0a003075068401001842082030b11000a010890440c414404410810301c00b01e0700e0766100c0c400c0300d0213807040d03000d40580f103460913014080d811641c1c090313500c0541d0080945013107005801c90484100d210744120500e0100002000a40c101e00c1ca00b05610442e24400304411604102440a09000400000c1c1d00815884281c00101d2160441150503a1203607003000139200c0641d280154401c03a00d94410855180081000414000a100141054407040e0501c01c40b010321400283d41c980c0032030344041e11015042000840c1401d0035801160080d000e0300702445500d40650342c1f20f01d440d0b000290280c0800000600745110703030b000000150210340c0301c900c12081e6810300000c00d160020040c0b000307100340c4031050455005030190f480001c0d05a00710072030003000011080078101480341d00d40211701d002d2a081c0080d0f600d038846c100c000c1c0488a0518080e19107468404104540c041861001c94926601d0f135101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 915721232 1250 915719982 915719989
    0x30c0e07091e061e09120501060302030d260907030f0201050d0617010b09060315062403011a0c0c060d110c060103030801051c0f0c03081803100903090e060609 70
    0x914011409404107040f400c00e4001030007200c90760400303003500b010300c0c00c90310045400224140503102c412084560510041c14201d003d84510350011390140176100120301c800d40d1144200040d5441903118a40201b9810786081c4008411112803c80f6080f4800a20009420030180c464603030051405505104801c80c0c010212003035a4402080c0b0302101c02c04c510109028021464902000c031002d81c110320300a00400c6d1121203100c0c100d1105402c04001808640d1610303240991900ba089540b41a4020f440b40f82080e680203020b101144182c0400301000c066546003250101c0c15143c0181c4400030904042c030505401c0f0104003415070ba198038081f4880a0000c020307000e490050401020207514604024014040c1a0419401034139000c0f006210146030008480307c0d00d501042e10010740b04541400c03112802c080d0001010303484002034070421a0240004100c0040045054901080709001d40b0b104030351108500074081b5594060030070010826400c0c003948400060609840d010605002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 915722482 1250 915721232 915721259
    0xc0a021519051503012d0504021c06050604060905070e040903090503030c07030209131e05010f0f1a0f0d11030309060a170f10030b06030c03010c0908060907030c0e0709 74
    0x110156844407004109403a0174001c6c08028400b11448091804140a07010301c00001e40428000341500d8201040c115140d11095000e210800e00d0000f008103c2858500060403064545500c00ca04001d0702060542440c80740500401c00c54480c40d460050040501001d00ba40541c140d0134020815170004864800f40018003e61071402d01401086055104000564002402102416200c40c6450000400e552560b51141d075501d807441009251924040b400750600000d80c459031402c0c8581e403030129056801c0000410300415024043c00d4010081c00b2481285040c03255115110440b0000420384441d400d00312002e01500f039a1902c1c00020109417541e104800142c00129400b05448030781903c00d03015500030410000861140c00c1081c606140080e00f804090100024a008607010b0b81e0100134013151302a000e0000d0000d41d1020380023034050b9500c1c0c42001580d009403000540040000301e081010b496018800c0d850325030034034085c203004070700042031841400300e000b42c0820707a504100394 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 915723732 1250 915722482 915722491
    0xc0c05030d0c0516060903140316030e1206060108070e0f060406090602060108120403060509240702071406041a0d110d180201080a0b010c08040308040e0c0a02151905 73
    0x251444505054508985480182d000c00b40c500c441c444403e0045c56480134454041f41d40003da00714001314511041d40c1503105215990440c041010401c40030107030040c61024007260101d40240d1444030502d0156241e0104459450000f26502e00080d1720314020051104c4042d00988508889074140340420179a501c2500408040f803100300301008210340c1000382074094807586010b803c80341d1f0700314018601800790b4000203000546070310005080744020010400a0404070f446002d44046204403020780400070344009005000c0d100380440c40600d030000b001d82484010300031520741854204444150103801580101040d410021070a01d4403d03070003040c2c2842290f141560340c404511951303404a5140e15481c50000d001c23111040050703078100d10940d91100c0c0080021407020040001200c0c0ba40348024024203040c0041404070610540328003070700c141c50052651000c280c5560907540201c2c028210580d0040c2d210000300300030700b07209118080e04003c8240010013080d402c15800c109a680444 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 915724982 1250 915723732 915723737
    0xd030e0d210b090c1308211b160302130b060403060b210c0a0e06060a0e030f01090f020406060905130b0f0406030b07020c0a0f06030203090c0603040b0f0a0506060a0c0c05030d 77
    0x1400d503055040c04001c0c0801400c407940100300f5840c0600c0d080000d0a00c6841e52201c1240c0800c00f40804400b00c002480f00d407079420305503604421f6420314140f09c00b5039804103901606c2c03034035001c03c1c0160300b510a4400e04100100322a0a05196545110142010340c1046400c030807001c0081141d10088096007a400c030045000c0e0140f034124005108462000d0b5100c40c84809191040c005981c4490003100c440802c14500306029030025030110f403030201d001074004c10344d41c40d14083c1400d110100d24502c0d820351007200c080c03050b159209801c6902020501030706a100821440b0542d0040c02030b400003440c480e0291624811403103000001e42107076910750080c0c0f109444001041422030f414080c0303205007141110400d1501c2e042034104049000d01d4010a4181580000450300c11007007004000500705004200e0750340ca24141c0b0f00303060a40340640342e400d0840301c101e01188081006024041c441d0802a02d0381d410901804001c0314685200141603030b82d08a05000880e00b41c03070070f0080151040c80d94 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 915726232 1250 915724982 915724987
    0xb0d150f020a2105010302010519031508010c08010503012715050f0402120d051b07260f010c020c010c020144040c03141005090d030e0d210b090c 64
    0x11402203d80c3e80c0c00806000080d850300005100503a0414261041400e902d041d00320b010405401c2503008000c2c03221040480d0f13099403000a000c0034150400d4504150503611403e45903aa8001d042c01da030041c40904802c201404021030041d08030384858800a4015101454500020404841221810349035000c6901c0c00c4401c0000358100001d040102d142c8400041031074841000c0d004000c0d0040c003040455081641d0b0b00004011801c10a02028207919529210340ca20403001e403041c074854250450880d40202c070b6010107840010b105160903900385030050561028080c004460050409104134184044803848040303d8807010303405c84500c441c140c03a10303030ba01401c50350b142030410b2504100350040251004003c000b81621018400b101d912060150000070404102400e1444000d04031200700c0c500003c20080140c00540398941c03420311b407402c0003951200c0c480d40d40c8400f01b1400010128540d000450710001403465140c0c0c65908017180000d07800007038000114420b00540340d5441d0030601 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 915727482 1250 915726232 915726257
    0x21220519121d090f060402041d04120c0b010308090607060f050609060f130509010b09091b0a060819060803131409010f140a0e0112150b0d150f020a 65
    0x15001042c03040c40c8840c441c401d507a01ca8005146450000e00d80311100310384501040716521260195000741c01541408170031303074045010710000840e080300c09841100502503042005802142c02da04c00c160480340c0b1120703a0782582c540b01019800349c3d1090703811444c2000301001003030481c4070380c8030300b880940f40100f6241041802c001c800b200142c2601d110727005583c1080d40e2039582c103400507400324020300041025540c2071400c500418a0303175521a0000003004c1003004400c008100c0300c2d120b140c0030240d001c0d41c0c1c00c0c003414850090018040d00700401d080201203400d08811001c03602c200c44140d035001c2661fa03151400a411030700300711003800e91210b0040007805501560034010fa005402920300510325850242c0311440c00041d40b1661000707000702c0d080b512480c0c44460542d00035041e4040c0c01803865968941102e00c80030550010303260f02e00564000780070080180200c01030a103000708500c11140c03158035460306c80d41e24100c08810701991290f101c0f8201c580d500241c1350100c02d9490302801c90300b8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 915728732 1250 915727482 915727487
    0x70302070516180e0304050d02010c020d0803040b0405010c17040204050615040602030a02100c090b0313020a06080a0b01020a320d0e1008070903061a0a0305032122051912 75
    0x4044c2d2401d010344c00c180b10901c051340300e032102200b103241c0903c0c0054004000d8004501d10440b480000b506c0903000100b0041804002094140039510650080144444d0200111801f45640c1c254007050b20703440002c18003600c0c2c15001590031040080003433092070000106041c0d0ba81c001ea02c1180540c201162099440b03405200300c142100b4000300900c60703404080c0b030080c2004ac0500038102041008070205460035441103007848440e030301400140c1015210170020b8011202200d203080c02c0c5003011901c2c0141d51011400462080d0b000c0c8400140c4401c040150928141d60b12400c2c04540b1125620b68880804100f0010114210b80b0307412044160003040c07000e40d82c040081c007010f000d040b0043c0039416500c101040212500084001200303800c4e41c103259088002a80300b01d9004e4804240442840b0010000348903602c5120300402942c01c10500b1104100000c941c2c0e900514000c000c1040c0765002d0b140c80e100118031030415a61994500c000c1460900c000c2d200035280b000c00415411005074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 915729982 1250 915728732 915728741
    0x403171204050f0d050c070603020c1002130521060f060f1e01090e040503160602040b07030e0f0a050a15020a020a0305210f0703121127120607030207051618 69
    0x84e6880c0c260b103882d8002000340c1e82e5a82d1403141c01c04041c0d0000e00445030ba0302c10b00000b214035488040656503591403181d0002802d50034055244602e0707030b074a61149106603005014034085c2c1c080c4040c0a540d44c0f041c1402c00c9200380201103035044204008070400c40e50750340c04482781240d804a034600c1c50458007000105141d469401c40c1807000c40110a00020035800800c2c2c450910340110043d41e1481c4524200019018030303806948200d034045403050070035400c00d4030154901d500341d43c42c48540d95154200602e04040d4450a0b8214401a10910803041c001040d011515031b140100d9009480c05d81c0411305058880e441580c039a006420f030b11000c8121211021030140c0940d00d11410242d07800700e15410740c4151840181889280d124990b0100c1e9503070052182001c50300400d43d15236540e0054a800250002c21180015040501c07040c618900603a81211048201e801040300d5903841c2d0095009601922040d903003031058100d5002c0341c1062140c95400307888030b10840707404911129042030548 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 915731232 1250 915729982 915730003
    0x80403090b2101060c02130506180f1b0a050928060c0308060301050709061b0c2304060803040302120129030c0102010e0319110303040302070f090507050403171204050f 74
    0x101740324400d100540d9a901288031038007150341000402e9210310001030b00c680482c0c210203604040c2c0404001401e01c0e40c20409100b003030041c2c4545030b800c0480d080c81180344551306440d008180144500b4507941010844e00c00c150260030007040a088410034401070842e4139900450001d00340500c204105a0b204044c0c9030043c0c0c0680081c826400c090001800640e280d000b42c5041003050320755980b010040c960a8424141c2050b01c000c081030311010404070143d400560911401d01340c60f2032040c0d030300702845281c0807a98013074055800c19080d6801c000d0510000b803040382403913407542e43d0410411104150304819941040790420104030b6030062608010ba9004520306691601000700c10988020003124141d02c840081600c15001c803880c1580c580d0b66501c0261124407001c81000200740d00050f0303120542e410305c541a00b84903134603143c42c0c0075508100c0d4032000040e0188000c00c0091802d0344402512440d52540c94240071004240c0c400180d000c031000c1e1040e0303220103a5806065030501011a40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 915732482 1250 915731232 915731237
    0x90d1401020a0906030b0616020103091a150d0b0f0612120a2a03030b01020307481a1903060306060b07032f16090f0516080403090b210106 61
    0x20b4520b1ba8002034440c0506500300008000360381514003103a200b580a4580d06a00000f0142a04c00e1800c1c250504542201d04408180d600114025586000869842110b90041d0a1101541e941b42d18580c46000504010341201d4000d40c00c1001c12010b00039210081c1c620000d4580f1045182e070002c105294510741015505400d8035400c0030016043c0700050007079054200452403140c2080100d14504c41c1940141140b0903526851500750801001d02d629030100c000c100301c1c00d045d4110700c41d030b982141e501130341c0b15030140c18400c02c4024210740144924401d5012110304003002c18070505a403520030745515000a070303034400070b10070003c45202d01d2014000310b11050b4103013000c2d65805010034285a035110080c8411500071050314030f81842d0f00840100580503180000529950003200c0010340c040c2d0008242400b81d140c0035a020381c814544a0240343d00b174521540c481e404281c0d0000c0300500f040d4100040341c1ca0101d001c0c01200000d00e94102107000700784035010f9074102180b504d541a00001c0c00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 915733732 1250 915732482 915732491
    0x50d0c0506181c270315110405100201020903060a022107031d16080303090a110d02060c0a030f020a17031b040f031106040b222105010b0102070803030a02090d1401020a090603 77
    0xc298205032020a00105140000f00c07120305004061f0ba901555200d242e004000c103048403401c540c1034018100e8048107030211801d58a40250520980c00303a40c5107100103151088030030750480c0c4036482c081c1d08102181030002e40701d03c0c41d010b00c03900964a20b445001aa0100d51003c042a80c0500d00c4c10007002c4410282d4207605000c5202ca44640c03400001801c20708080410380c7d0183e032845070103401a0780c011300c405c0d541e00d1081c040503251800440c0580105410f074449900507030021881e00c040607803010748501903400601008645400150503800942c9403a05000d12101d90000100094010107400820781441d51504469840c13464201c640030341024041003040b014410140d491880b0030403201c410111120552190001031a4030454070b0707402610303c1012121100070301c1e401850080c0024413246043c0070045e07035905c22607c01c4000c1948200005a9808240d80c05090070746070041482e40e401c900307074a420604c500003090000c650b0350b0000d040b44000390018200030090490313041c24031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 915734982 1250 915733732 915733739
    0x5090d141c050a03240909021206010f0303080403120903090f08010212040618062c0f151e0408121f1802040b0d050103050d0c0506181c27 61
    0x1400c0c3d009518a0800b41600c0b11440717100e03000f4602842c841c0105003848205295a5841d81c2e901603c180b0800b6805103a002040c0c030302c0b022000c1f99a0307050719481c45a1841385031461360115410000184240c007000401c4858002075400343c001c075034940b402559062182c0d424a07014001c2d900c05540f200d540d80e8410003080c1d01921364043c907158010341042c00051641404401810010058200104aa0301d006510800c1702c2c688084104038489140617428406618641d940d0341350440c4030701d91000c0c1c1c01925a02401d0844400c0c1c41d1303002d105001d103100c43d44a00c02c410044000e0640e001c5560000c00320758a9050084101025446070407600c41c684c0340c0706541e100d0562850540922740210100044580c2d0083d41a01100e004002c502c0b030180c0d41e407003007a40204c0203003003c0c0011070b40c0380a051000d8490710b02ca00054203005400c0340241489460f03054290300c2040b541c1e100280d039030041c1c4820800c040300001400e00c40300c0f043c2c1c6503c0304a00003204404420383c0740428003150b41444480a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 915736232 1250 915734982 915734987
    0x70f02190308130503041802250201080414120a030911010306120b0c0f0a020d0305151507051203041412031608070c200301050a021e070305090d141c 66
    0x2241c1000e0440182c0c000f041c0d80d81403450452040382c0101c0000920f0600a04001c1840c1d4010001c4829114525001041c000c44800c0001121440030340040c42100204012030f0202050815811402040b104c86a4101200ea00113400440c0710314007003070b907807044002441034130407840580c07000034607003000103504105140307029603034010f005450a10064005501035003490301f10380e5150320b400c0c07040e62103080c1c90380001d40d01c02060042000003400c1101141060380a0041044d80000007401c03c02d0a046800d9043c0c0c20342c0000340d05451500c90032520b1160300141600450149003d45011000c2090518509240c40c5204100c1c1c4e1340490208204803840f0000b4a01d500e00a88034035090240f078450705000c8801a040f003d01800151343c6050b07090381c035002c801918000540c2503000f031000b03944002c003102c101d0059240d954500308105460b845540c103004014143c60303102e803c100341003c802d1804154210004402100c0104000800b0100790808010b000000d01c0690118650300c00c410400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 915737482 1250 915736232 915736247
    0x30d05071202190b06031524060d05013005060a051f08010c1106010f03020904330f0b0f1017090102130f0b042705070f021903 56
    0x98414855045280807292081c045000c0700c0c0c103116040301090049040c082e00084094a00318845e00c1120416503420345022421403081703410b549a1401142c120700d445e1000094120115030000040103c81d09000851140602800d0303400a19492a007120411010b40300d0440c07054210b40344d81c0d00701c1b80000b42e4000380345640403c10381000709050715081c003041d111a50b00f501d03002d01c4010001010905040540c807105510800b603840e810101c80c84120325444080c05c0c0034401e42c41c00912420300260402e0030b8159081440354a86400e5030300c1c030011502e400002d0365030040f00c282000007003203c41c40c1e20340210040b0201c041070070403c0244201c0003075401c1c46a01e0845018102469a6041c0c85001d24145010301d039074480011190f203171820034903000707600420850318041c030320807808161000680c918800f5201c0000090349410f00f010034642d1040240045840d028003181c01000c1c000071640251400341840b0748410007110400000030b8202a01c8503070350480072220400302008668010075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 915738732 1250 915737482 915737497
    0x7090618061b020301050f040c0f0b0904021308030f07020109060906080402130b040f051012030804150207080d02030a0f0203150402070510060e04030210052806051203040302010e030d05 82
    0x180b1140b82d00c0402c451124031215180040e50552070305017000360003c1100f40d80c2e07102e40e00c42d0200310005501e40030603068981a6000d0b04110700c000b032007900f03401e0401c5d40c01494410030091140c0003c0303039100011031070750303204056004004c1004100003085503000004c21025041d2800c0c43c03072666080102c000c04602d00108041d20420080150148101c09980f00d17100070040a4400d100884021003540c01400c0140d03030058003511079880c00100705034107500c01060107078103903110320003908c441d112404c01d6076418081c1c2c0d451640c2004080001402c001c010800c00b00301c83c8005d80c8a2400310042c800f140c034501001036115004004201290741d0f82c40f42c0c030403003500850300141c42d502c0c9801c100b85403141d801c00346500320b8038042001c10b2007420030010071b10851080d0f0858292034007400303030a01038420544040040d50901c0000b21542450f00c0041d04602d1400040050f143e1750f80c070000f45004031184418121900002818030a650344408499841e40040d070081c01c1007540c2d01001840c0b44207140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 915739982 1250 915738732 915738737
    0x403021c3e012a02060f1c02040308030403081e0a06091401030c0909050c0406080a0c0b0703120c0c0510050912120705090d0501060b0a030f15060818070e0709061806 73
    0x281e4803603540442c168440070f068020b89680c0d1901112441840e00b603000d0040d052201d08020f4880c4da000c0500e000311402e0340c0d40000005d00316201da59054903480720107000303900c84070a000700c204403040080e038180340b2402403000007243c40c914102205040b00c0043c541c1c0c400f9954044018808100703a09100000c58160f440f0000b4100010f0070003d082542201195034810b0400c2000141038030300240f40010603005002c8440c0c00c0f41e03038002040d000e100305113000300450382d10114805c40f01c0d0f2640c04031194000c0c3e42820001c10700f95a1300ca9041c906a002d621180598170003d00c010903508000510a903042d0a8405160007851080d040d284c98009090008010000414034283d449100c80050302950003002403012a444000c4c4592a070006041000013030300c0c0981d498079807101c50040041c82c0c19900c4458500a04200c0200c2e4810801032022061a10b6841d0244290300100b103100700420b90001500c2903802d01580c000c0c001d8265900c00401c220031880c66040f403000f40324480c0110751490 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 915741232 1250 915739982 915740027
    0x1406010c02210c0603090a03020d0f0c1b0806070207080f07050108010b031503100618111204061b0206061503010819030c06090302030702090901020c030403021c3e01 73
    0x84401c2d5141264015460b5040a00803080c003100c00c0f80000c90489640c803035002e450f9001c0c1904000c0383c1403228800301c903002400750f1181c100428910341c0c61010002e206000d42503003944480895142c12401d0f0303111001070b40300794000c000d09103080c80304005104146000d030140a2038840020806001800f0729622a980000811207110505184049240000d02500c2c0742d0800c1d21311080003130086110700031540010782c1d0361051030003540c030a005100001e40300d00c40c200b1040c42440107200d0b10050080b86d400d5540c0202d0030701403031101a01c402e4940d20341d0013400b00749005400c0c00043c0c0484ca80e154495403040c0018061688045801e48040c50800c16813694240700d400e044440b2036510001400e840d1900729060203050f07010000b407041c10b000742e0305c0344084d856800d210307801c0341703e90803007488103800600c000c0c00140380244807102412011051039940600b25103e0a140e01320038920341c1c0d4000c0c000901d8124040b0b0300300f0880c0315940b150b603c810101c441c1c18000f805424a410034242c000610 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 915742482 1250 915741232 915741289
    0xb01030f020a0f082a1f02060a29010c021504090e01090807020d0c120b01211502090d0b0f0f0f060114070819020d090801050c04120807050a061406010c02 68
    0x145898080d0b802e001004819180094100c901d070351022981040014092390000031900c4006010390311090481455540722a401d21750701e07100c000d110b10302c071a04014101c485a0096aa00e0107000c041001c140810384d03685240082e070350201d0b03100c0c00703c0303803181d90421300d45101040c14002603074105e40c2c0607a16281b4569991903e40403180301c1d9000350780d06c2941400070f1000d0180c95a4580d05a515441c08040d04401c01c0000d1400c03800b038010000d001c84aa2184003000c0d841039005401c0e1280c02821400c5107011555440d03040d0441211131ba14410705030380c1003100c510108000c064001030720030078600b42400c00d400000c00c1d14501035070210314007030005040030800800340d085800c0798000c8035441200030005030000b520b4988600000c00001c06040d4080b500300010311500e401420301ca1862460149851176a84810511510030780e10386100303002e0748020603005e0180141041c030511002940107200c0c0c0f49003864480c060419410400c940540d04016181c068000c1c4c82c031800140c1080302c6655 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 915743732 1250 915742482 915742543
    0x501090506070b0c0c030a0507021804150f0b04060e0403020c0904050604020d02120303091c0f021e01021c1401090c08060103110c0a050307020301110f040612090b01030f020a0f08 79
    0xd0650301d80417030b200005215910f01e6111000d0039440788200c1c3d020416103652499a0301e0320074165009000104080380c060f0464000f540800f4044c440d84070041000c0550a0004040320556484450940014402c020800da4107020340418801c088810f0304441c1405c5c0c803010340d20540100028080c600b0140420203668130700015041000d0103034109c955a1501650300340d120208001200c8840481d802d0f5444940d018104002e6405a070b9030090960740c0d1480d02c141502c6400102d010b00c15503081140441702d2218000c00c48902d200703102c000c071300c0d29a50780d045143c02c04140c0c80002c4282c034111501103d150f10100064003d03a00f441c021503518004440d0f42603600c550680c2c2d61305031003584030b203604000300800a41900e9000318001c02c500c50005c442e5206d82e108012030303a0344240e0100310074400b8a02030303e0b2003601c0c0300b41141c0000e22100b107944c940344290401e800c2a201e54444015500c00c500d0309903040000b80400d11040f0407598600804c2a95440e4440320b02010042c040c100030000b500d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 915744982 1250 915743732 915743737
    0x91a0c040512030a0206070203090d061a040c08010f0801061a03060117070201060618030b0f0705040e240109060917120403080a180509070c030e04060b0c070501090506070b0c 77
    0x41c0041c00b0780510480e0303115040c0e0300c1d800341d285039015019000000c2c1c9814000700607900ca01c0c0340503000c040070b0f60341d6548580c02080c0007449500040d21800140085888510500d21b004c0300941b100d2a070b03941000691450720143c0e900c206510380c1881000c0c040000a460f6051803040b007880ca00b500da031940c0006072400000c0d808c140c55811150020450295070540200017241d07019292200c01007022600901002803c0c0009002070312031202189600150842e190b500070403914109050544600061f2005c000982d40e91104994003945260120102608007c4840302400c0c81d01d204e615241c17025180400e180b082000c02d00008051034416002800030082c80b108460b14160343e241c413450812182d410540d03502e40011003103445049007041e00da91800c103641004010301d5050f900c8000403515041c0c038580c110200135441244148549941c000c44010702040003115488080d0007400350b1501d020381d40241e0400c0740c3c4107410800d58549070100c40c01e080d0001038115042c0e039080070030300083c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 915746232 1250 915744982 915744989
    0x304021815030f0c0103150e1b071203271101050903030c120304110904150f021204031707021506060f070b010e01241710120c09050703091a0c04 64
    0x14041e104420301c0c1c40b0004581302c0b075a0f0409032020401a2101c903040640003105005009610b80c030100840c4442c003004600f4040c6100c400030707503407900041d5505d0409030140c42e000503021039252003d10141c048086d03401d1000b03a4617180f2101c0501010b444044d01e9480c540c0c02203042c0100041c0c5142243c4041c400c40c2c20f14490642100e004403100c000c51101a27204031001d450002441c3c4601c1300178640350700014002c5070850700302502800c401c813103040200841001c202d05507a00304000c12440d503080303910300d108a0103038941d2030742e03a110300008003402d43c00140040215046804010351322001130b001103802a809942c5123403179071003d191469561190791000351141400764000078174400408000da058480400c0c62007048601c0c40007100f048040400e0380004140424203100c0d246249170122544150703c03200c1c00140960320811180010b550780d00035950801d28041c140b00107245400703110b401130200d21f41041449640c1d22010701801e01103004040b040d0140e0041303000328048500740e4000c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 915747482 1250 915746232 915746239
    0x309061e070f140703021c0201020a140a0c020405040501091506050102070b1b01050f011502030405060d0515040f09030e2b05030d02030a1d07051c0602070803090a14030304021815 79
    0x100c0312035007400707540c1f03800410718803000c000c8145031400d91510600940e9040c1c0803d4031124501706245444910680000800300108010f4038102c0026a846000c3e80380183d010f1000010394844506080001d140100034010030642050720411003070b40c0c000746100403a0f0000c9003658a540c400303c80c4812004000c2c0c003203400c1b51300308002c3c030a943c024908040e04a031010861500b20301d416800581c0c480c044d0b0320907182d00074000c0c84505200c00d4113410103588454074403891140304401d540040d0403950007031640c007095544c40081008040c3c100e0750700000e0100440704410503803503002104500c1303403000b80301d00c201d8416900794108000003042600c1c1d06c42814003081d501e03031501401110050161052651001020320341c140b22010021503140242c2c3c90140020f64440c0c1900003903c1001030880d0f04a484a50800c2907801042407074020b540034901c400d0140c0a4901c085c14540030495107070071200300d140c008100740070040e0748140070300b00010034005c0c00c8082c130703074070030100900201e0804802c1d41c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 915748732 1250 915747482 915747487
    0x5150c010e010f0624080a09030e031f0b04090803041119060503060a1508160903052506171f03020913411603080309061e070f14 57
    0x1000f03c15500500142d418291420480051300d18243c4034000000349000c02080c003040200307101d1410744e0421103581c0e0080c01c1c41d020801074000424503041202015610f0161041807880c0e4041c82e2b40289510108122000e12101190380c88a601d01d110140c002003940d10900489081501d0b400810034503160ba0320380209800b0307079030a00680664000c482c8207109014010340841e020151100b04440c1441071f58891b12140d442c402400b008100d42d55100c0d0910400f000d000001a804101a5030b400300a40d12000e0412a541e06c107030711000c030a400036428400b20446040081c0f82c45820160300023001418085030901012000c4a000c82d03d402c0650002500420080509229401025080d100740d0300700101e4682c000c400d42c102c0d9842810500501002c200c000307210b041d98554035503042008c0307041d100c0343c59401640106044080d80b0845070000007200700b02c84224213025603079106090111003043c590440500360341c4041d00802540c24010905000a4590b1103a0714101980660b07440003035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 915749982 1250 915748732 915748751
    0x5100305060906090915040201030608070b09130501080a0609110d120e1504180204050307060c05010b040204030804090f060b21150108160309021003230105150c010e01 74
    0x10058003085550314024481c00000c500c0c18109810303558803604112014280c0282070410b61345034802c0150084e0304068840710045410f0400303101002c000d1029080c455980d01c003900512101090302900e05102501e400010082880c02150095482c1c0c0c0c0072400080801203468041600000303809110f810034080089441000380c005030503580b080d06616100080c0811804200c020003900c00c501440c4241480204601101d801045055044901d0007605194694021918042c42a03111400003050480c0e0030f17090007800c1c8550140b02c0b9040e80e00750720f01411622004158495485070406003030f03446c00c24440982565025178060807012000310b68801810541d04141d00550503514002820740c00401c0841144103491024000103031501e0388107aa07010303100089a04180202d10915407a1013a0100503904c08030b003442030f9030007a2000100221400d0340380103152400d010402c81c01c94450018045540c810340c5016880c0c996840b19a660142551040c6c090f1040041c20400c541c00e011040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 915751232 1250 915749982 915749987
    0xd06020408011509180c0b07020a080f0610150503011505070512090316030b0a23090a1106070f110a0e01230303190c0305091807093c0510 61
    0xd0841300403c409205544030801c0c0c2000d074140240c030003064508480010051000c0101c00380030564001808084155510605c5900b0400c0340140d60b0300c160440d00c1000281191804081701601d13804844528240305000050314034070040c0038222130085805c6a079411640b00300212210b1961040644440d40203154001420703401036030449103c3e01450115400552403c2906402c4940080c038092040c0c580c0071320380300100071801c0407002d90000800700b0210402858840c40c00307031031070b5030040400702c40c181441c10000c41545202d42c4610f800300188030110b01d01e100110344c00c036000340101d500c00142c00c0000d0030607002c55128009107c08034000107901000d1130003103802000030001c1d41c0242f00910040688074450028840580182100b00100440c81520f0103441548039050092074401504001020324041c0301d01c1c4885400c01c1c0d810800720b140e01a81c040c009103c08031409141d50740c0e0b8039500224000840c40400c40d168180f0401d0059200c0c40744000040602804140361000d600321700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 915752482 1250 915751232 915751271
    0x6020d09032309120102160803070f210c0203040512011d06010e0426030a0b0a1401050a050c03190f1b0b0c0912030307031a0603150d0602040801 64
    0xa90110740c1545204002d01151442c40301c011a0707001c84503203407031030741800c200c80c0706100d01d0910450741d4280002c010341e14014150002c500d0052500b152207241040d0700601d46e10707440340904200304c052003815924062010100c0b007140d9031154003050741c0c108198102e285000d03590020350312248030418038207002010760000302884070030781010366055402044e13659a0031080c07141c0d499107a021400030780420003000500d840c52003d0141c0803101580070b4006100380d0030075950160b4695413100c6078200c030300c1e000c3e41200c02040c40014800506601d0000a000d90140c4061101400000541600203840030310488250034440b5a045600d0001d14000812107000079903082c001c115884280059040c0203484018981d5010030594a2999104c81e0311415401451200f50018084032008180800c103202451284036956000195940b03800559040150006071640c0554410024050200040003140c00d40400c15541118100000e18012000384038aa001031859440d000c1b1800403018080c2d04c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 915753732 1250 915752482 915752501
    0x30f1603032417070b0319060b0325020f120a020c030f1c02030405060d0b012d0e06090306040f0305040e19060506090f1003020c03040b0403060c11060601120906020d 73
    0xd074451180030f6295a5554880f90181d101c40c1c0d403041c80040c02d0369030341042c0c2c0a250301d4800300214049079561008640c07501b0030703521004448513407846c241e00403120001e0003c0b0740e0281d1008190221441070f459407103d03503000820024140010301080c2047c000c11034440e8081d006130485107c107060904980e1205241a100c09104844400341048244000142d5090700d0b4014040c61800c415080404010b05e40fa103602410b2000c80c5420b56900d040c0c02c04401120790914802d94182c41440e000103001000d00760310288242014480c0942589000812503071007a4820703c221050440b5040030380d042c2c001c542c0005000e118003003c108600b407404040002d9104446000c0c452151214204100c1e4000c902485402000140703480d219460601c22881d401001424014a000340c01c03502d260031135105800010031040005410002c0068622a1500742c1c01c443ca084080c2d00040550304c0e41314030000d0803007070410a809082045103030f126400001d171254425000c5641d81d20b40d0100d54017402c10b0701c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 915754982 1250 915753732 915753749
    0xf0b1203091f0f05070311010914120724090b04080c1902060724020406030e0c0a050a0e070201112701080106210e030408100509030f16030324 63
    0x840e042800004091441c18200300b544900c0e03040c0a003007104071184d4003c40c80070707010854000c0680d404181c0c20311441e51b240d0301460051218a050040c401d1914000c60744680707100c2c0042010b500840c000d96001815510100300401c0c507540c8a4403c60080d000403c0080e02c20803900c810b020801001100034078401c800c02e010790f0413940e800e00c1d4a4184c00c3d50200040d4010004001003130001d49030240d420106003403c89101030803400160300d1412604590802d0001c030390f0381c031030040e2a04030804c861134028200302ca400065605050210781454030610600e40f00f13814503c08034055038001c6d0458451001d0138610540c0740c0d02d40ca0b50103001c8984015000c1128601182480c419522512459050301d015480d18240e580c1a092038001c0340c107040e0031100d1079954411905040d0101480100000c24104000f407240500e2542d0040440d080505407500c0d50b4400c0150080d140f058000343d0f113a5510b1031100c110262000d041c15405007002c000e07034003410307020000304440740c00400790170105039040c62 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 915756232 1250 915754982 915754999
    0xe0a1a071b030f060c110d12060b03010501140c03091e01030f051017071a0a081f06050d0b1003051918110d08030702030901120504150f0b120309 64
    0x18a0140d04940c0360001520b210f042a0200c00858020741108843d0300440ca401c0700740e4200480d0007414044041101e100080044000c488141e840d4051030000e80f0b5410000d41c5103514100c00600001d06480c070034940080041a501d1041c4000d1080e910140c4c009040c44000310000069203641d00018400980070a15010007400c103c2c029100c0c140c403c031a1001ca9029a80c1400c90015803000000c1d0b180d0b0042c8a5481c0100b231902c45000903580c2004111040c5890703422400026242e500010711124484004204858210051042260496000d810150364441c1a2260000517080a51460360810021f295001c00c49a03d68480c62041c4503105001d03440c54042640001940c0c0300c18030350042d50740004015400f1442084020920200c0107000000c640120360341c1c42d0641d042218110003507040402c51800c5942c000b8526840b60042000030456841c00380e4601d21560b0030030b5002c1c070b81c80f6925102c0120702000d03a44900000840107000e1803856221070b043e030ba070b66840000d5260155021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 915757482 1250 915756232 915756263
    0x10060906020303100b0c032203051c02030d150b0a2f060402060c16030606030c0608010e0a09021909151401120b03010f09030c0308070503160e0a1a07 66
    0x110a6900403400040082d0030740c0e203030a40911741c50700140c2055449000801290480e8520b030f9000340107081030003180c0c450f06071840c2005030070848080c0c500b00704100c0c000c10086200d46e010007141c14254449500280304e15944510785c810081e02d8100380700d08600003a2040700580c100c03589401d03101e0b5210f003590030360301001c5000c02d0000c446070120045602202c08a00145020f40240044034000011958070700728010102140e42020341c42a6120b6542d00d600307000b40300c103c41c0560b0181c031690403d001c85501d0404441030a0304000e01c07101155035980d096070210b54070712002001780501c14a00c0c12403d61541c610030020000e80d020a030002c0c4c05480000b030700030043d44d4014015001610f82d200c2e260b41c41082c0c01d01501c9400203941d819580c4e0207560500400c3c030b200d01c0d10f250703000b5650604526100e01d0041c00000c0301034205410710106004201c103038000e04420803590006858000405460000403412000d804c0d0852107046041202d81844410180081c10781c040c008e050b0840c48115 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 915758732 1250 915757482 915757487
    0x15020a0b010504060b0d0e0c09010e0f152b081305030105100332060f0601030b040b0a050d170325030e1513140610143610060906 57
    0x26901ca0040e10308020b02010f001d106c0ca580c0070084071400788054584142601d40020b01000d0240c02c1a44102000800c4c02003003000c2d6445c0c00e41c49029101044101203502c00002e0b03026400d803c0d8809058a1260001040031010348403044441d1300800c400d07201c103000e9190f030713905440600502e07002c0e40c03030880000c0140c031000d4425001c503600a0314410b800080e28034480d0003803401488440c04034002d50820210802d0400000e8491850f003400c04045040c424001016900d6003640c8510580c104405008140c0d44e08403c9400c9a000300e580c202801c0e0319140c08002442c0c81010702c0403a41c004420800308001d50f140300e64001d00b1400c0240540361b0810802c0c3e040f50200f040f005100e503c40c0c4200140000c554543c07a4028641e4025152180c060b0713602c0801c401c08020080940d41c1010041c03101c0181c4031071440c00500b221200c010218030b00200841c451078401240141200032149840107500c0340c5030103140507100409407040d8985007294104c900b4204a1003480006445644001901032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 915759982 1250 915758732 915758741
    0xc27010f0207051005130f060503011a07020306010605160609050601060810031205130503011b03050603030c03071e05070b0405011e020a02010c151a030105010605120a0c0915020a0b010504 83
    0x3c4004043c61525003801c48100c41c01d80040700b5079044d0351355000000c0795185800c04100c000f81825655195a9810b001000ea6101100254501c41c2c403024062400140d80108200d41075410034500369846811a00d00e105200d4420301010380f9040c5001020750070f0080c003140c0c141c140c84141e00c4842540e103c48a040251003054840503001c800d211003451800f03480b40c0b00034410001c5d1036049000c01c0b92200300003400c56200e000200e24034100b05202e54846505800b42c20360100c1c1c124003a504140203440c5440d12481030038401005070318240c4d0a4420480c0c00100891810707000021960302580b6170041c440242e220340203c038045440f1850400c0d0107004140c118030011040c0c2d001c0d202d01403a0398015a0000e41007002120041410000c00d8840111171282040c50b019140c1f9030202d00e1500c2d81494215803060304914200001040400305400c9000ba0581d040348035010700003002800d200f01150015081d81180c40d214031028095242c1c5507000800002540c0126140455642da620030001201e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 915761232 1250 915759982 915759989
    0xf050102030a0c1205092205100b0405010c0f0605070f11161413051005040605030f06040305030a09050102071103010f0501081e0304080f070609120206030109050c27010f0207 77
    0x2030b80310110380b000075011040d003961040135050190410452000086100526451000c4607400352004000c40d2600d601a182d0054820703282c00807080d00b2310180313000c02d04c01c600841d41031003e070380d440a0810003501c80c010503642c1c21240400c00b900b0304010081084040c44d0707443d000106910031600740640f020800011000354445060221490a07450010866031020401d80c40807100030104104401ca000300c5105464810342108113504143c1040b04889098200a020b139004041c98030401030f00103021500243c1605242d903d0741d0324100d0b1080034003451100100383c1c2d4000b107041c2c130401860044500c54024101c2c0244440401a14a002100c900f4401d02c0600e900c40d0f83c4260340c241d0350907003403411600000c003581d150a44900c101c600e0036801000c18031302688490400c120385a880b4075890040c00c910910b03802600d44603000a1424001801418640d5580308003103490709010600b220904451040d070040c84409010861101c0300340303480c1c542d022504500600c2c41c031620114504041c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 915762482 1250 915761232 915761237
    0x10020f0301170f010e07171f110c250510090513020702031204050301060e01080a02011b2406080a05190606050d0f060c080106050a12020f130f050102030a 68
    0x4581ca440c0030b00d02000d5040b045000b031401101c41c1652010400e00aa9840c10358900c02860407510300103900080810007040e01c4503540007041942d103c103458180111821100ba00e0101d486a00780390500c1c03040c403404410075514421412980c0020014030340d04a0b182540300321848a1596400901082d41d02c0d40303c3d800c00154192109100c1460220100c0c581328020a1006040440c1030740805c1c41e00001d403800b8807104801040811081c982402000b010708903900700320b035030f84d4504a5810307544c0c00031440003418400c40100c41d04d0840b080d40310040a1a4200f002d100e0fa800b01b00d90b5100c00075410500710080700f030a02d940441c1c3c1400000301054050f03406801095188a072030341c507585e03a88102a041740c00c65254840018180d507003100d259072040c0900001c05140640340f40c031108407084280c910040c44062401040895000020f50b09404a681007001c0011100d91001001303110b80301c100740b4441404034001e0b45012081c02500305039a46480c049807141d49500043e6628090444071800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 915763732 1250 915762482 915762487
    0x5130618050d082a0102040e041b060c0f020103020d0501060507021807020a03030b04090501020c06220c230a262b0e0306180105060f060d11210105010210020f 70
    0x10415100c4010941c80440c0315020207100503540c4d1407400c1e644583c2c0103406030340d074a1043c4001c0c0b161030980c0070201d503401110000c03410700d0403602804995441c48040c01075890b001c003043c296402a0111184192600c2d000c001c0e941e11424003070480e4103c81401c0e40958111121049a0190140c030319008046540041c408a0b0803540d0480103805d0b080c44641d0840e8842a644c80064000d001400a4500030409420301d490040802050302685a40710712420311048483c402042241801d4000d80700d038035000541490125606c02c4580360b0680602d030700007003988000034281c01012a2210300640d0310b40c0c40c26040d0300310110360303603191096601103080c880800ca1842d419244144001041c02c51f40c2850110640820300082c1015402c58183c0007100741c0c0803c041d00d07890281300f903d5201034212107020300325102001190560190b05e9184014554421452114440020035255921a40200c00020381030444602c2280c15080c4542805403090000c90416031050f0700940d400500c03c0a11a030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 915764982 1250 915763732 915763747
    0x311030f03040909060608011407110303010b160303090506041104110f0901110f10090b0a051314012d0605030604050312060d020d11090603150f040305130618050d08 73
    0x4020300c0003120464005d6074800c80003600203801c1c012903502480718419880c15207850351000d840388400400c62030b041d810810041c040d45843e0810b603000e00b103d44500300d103440c20f1032600f81e000380fa0618010f00b1380d218031802c0204004c0d50403801c880c4254240c03800e1014180b42c1c01c0d00c41103030150021000d031101c1c0c14003100815512031110100101581011110101d0580d540c1a09181d02c044a590043d0b4541300c8110a00105441031a00884498020803035031403d240c448110a8440200074000f90000c0e80200703000e0030942080b450450b1501078000d450740f14044a041ca08100f404d51502103042c5500010b280ca4046609480355030400044c2d8601102e0030340c4005240c400030586c940c0640315000150141c0c40c1c24100e0b40b0024440e11740303000303615002000c11840c444001d0620b407083d0300000d440204040c81584041d04016007d041c04010307181c0d40340666450082e800d07043e4000d03c40000005440c1d610610101600c81c0a668001400351508103020303541d0b1111002800d0b5010410400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 915766232 1250 915764982 915764999
    0x10e0a0e060904020312310305031e0f16020306070e0a03030302031b0318060604060501140711060c0d0f090b0301061d040606180b0408070b1804090308010311030f0304 74
    0x503400f034801410780c3c050b20b003c401c81240355000070b02a40c01d11071880c107002c03807003200b50704030001e40ba04084466000c0918665a05070350b881140d180c2d8841141d00d0503040c40004005040e030785030340445038421380c650000c42000580c2441e0b1040c1a4400e10070040400c00e502d006074110746010300701801c407e003001c1c29a1401d801a62020b0401c1494180070903905919182c400c0185010b0b600362526207004032500c109280c03030518081e20300da11840c5468001c1196a82203146400031501a90009403502c2040c28044404000c840e5141d41105001603c4a0b207a0004208200e010f00942c403484445d051000f011507903403100340140b0181c2e5a0030001440300d54010304224084040c02c002e503a00c4103941030045403e5809581c0000702041880702070080a95030350074000c018001c20003101c0d040c1442c01c05003c0c4e461102d0b100d580400640055515080700307130341d2205000c005010f001403140311850301c2c001300800f000b444142c601c02160b01403d1030911b4040380411080c1c503c01c000350704103810043c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 915767482 1250 915766232 915766249
    0x6030c03011e0f0609181b03110c0d210b0d0b28050703111e09060d05010305150112020a0e090c03070e180a050304060804020607140705010e0a0e06 65
    0x103000e80780e40c1c80c0400040034440d20540d90702a0503035584041c1d505140404800f031b0903e4103219103c6c8a41008840c120310f00c240d000c0351002500f20314001c607a01e002e05146e00751521074188410018040c03014000c084a41010301c00207188041090b84c04050003542911041b1043c0021140e4050401c01d25007002c00c03200094280c020140201d0349407501c11300640351004070b00c4440f100342c03060707212410040610780501c100c40e9041e0215881768640745028001c5080310820007440d9004000110740240c01d91298010f55003000a080d5041045503124240342d40d560350620424091403e4410002c140f00c80130121014034142e02030040342001d402d009400d035080800400f5003c0c1441094407164403550308200450003840e04051440345030820701e1103812081501d10350400359a104c00c02010010b0400012941211443d19002c000d0340c941e880020281e00c0350b0307136015054072503481c090760380101c01050080c2200c4c802d803507407007a0702e0101052003101d900d6071103802c00b0494210001901f50810380003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 915768732 1250 915767482 915767519
    0x103020f0f0402070f1b050622051e040f09021e0103020d110415140d0c0203040314060709060305060a0e0a0905150103050d05190f1202040803130506030c0301 70
    0x1072440c0d000d4540401e049070007003501592035070390700702034907043c0445003840154030001c114145c90020308060120740c040c4190494003485020758100b4a02c001000080c680c0279010081040080c41c245040e80703048002c03181c03038241c800c0345002d450120601c898840c2c1c805169020307010384d07550b110000c0060b2410310907085071418503800304160007001c207562141d4042040610300032616242414000074042d03a45200840038000c441c12150049414241903a500d10f41065000c2a01902c0e02c0040781140901d80c8014240014110941d9440c44080f601a1003105075980f0b0300303c6e10f9644e40003101521020340d08942c1101418070244207502102074000e40c40020218003242a41060b518903140000c001c00c4582c14108080040c1b00300070050080082640341494030301d0815450011f800c0d200a501c3c8614003d215412000340e4a041c004c0310401f040c00780d580c100f1921a0342e640e41a9850782d010040c0004150080403000c45c19213410003d590089081c030001c0c60850f0300700348001c60780795440704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 915769982 1250 915768732 915768739
    0xe01030e0c03060c0c01110c030702241303150b1f05160807020120060f09150a020c1011250503030a0605090f0702060708102d05030a0b0103020f 64
    0x70600107198504100c0607026001803109940d444540040090171610302c480440070b201030810034907800341400000c1d51103032501201c00d071141242212600c50b20301c01c180020840d070880440e04400790100000c0d4042240d00030300030142c2e49024500800c0440703e03101c1e07046520103144000c01c00c0d801800030001c4507041090422910341030700d07128002080d07401e80390300f103600c514005668011035a02a00d051003400310002141500600c2e492210344860f8010a40400e2200f8000052200303c0c0411108068001e94000290b01e820200e4000c4081d6001e01c402149910460fa0b160b40740d44030700c4c400c040060401d03041c01820071459040e48102407101030040444440c1c628070326000705105000070b42c0501031500b030005600d4544814816040741c020203004441d190f4104001c007a54000c60015800308440c6844086036807441c0c00a92001e1042e0000c0b50341c0090954082445444101e01b1070741d211824402400555a0780d0405580d051440401040c012030440100018140404d0138196210002c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 915771232 1250 915769982 915769993
    0x1813060c11070e1911070204060617150d23011d25051809190807060c1116032a0e04080702060c1501052b0602090a06020a0309090203070e01030e 64
    0x44a0361390540d440c4000001101600140c0d4a0461400b480398900802640c10022130341108484420070b40e00005002c0048500400c225070720981e5000039041450703030b00188080080303d0114000c1c04405203a43c00d044990f20706010481034440161024422140c1e40004200854441c0942c0c0196202e480e070074158030414840108244c2d0301c0c40300c40c0910818245c0460150300d00321041034034020780245018140360848401c900800c0c15441280c0556400035800320b10410702034400c03140021480a1005603002c0c2c0d80340c400100c66128500b40849029000340235021420012440111400d44074000076804c44140410850502c61007069000d03000380740312030400819801040c400d44c003214808030290000505034900440202e4814003400b0155611072000c00c1c1501304224894000440304240c1c1e80444102003000502d8040f241074840150281280b0b903540c040107542c405440c4400c07008145022004240005941300766403081642e0350740e80203098003200044d030007040120340040660240 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 915772482 1250 915771232 915771271
    0x71401141906060305040201050409150e13150c021929071b15111c2003090d11030c070b0d15051e1813060c11070e 51
    0x8034051a449000c1071940030705182110700c0a0411a0700541004003414980002d00c80540d034071400761070541d44803240c002044080501c512511304440d5008118901c509400c0110000d100c0f41003841080c880c1100003582481c0c0785600060720f40c0b400c0c4000040e40040700e808098241140c006a2460040c02000541035004010301d14100710040e01003044009035081c4040294441400d50b4903007040c8558680410307641e60380d44e00d01c2810300c01d0480116120940d83e008040d1402c2160740300c3c180782d10254922026004580301400c41080384112081d8080080031808070400112032050358504041d012160303240c1410b4038110300c800e140e00d003d03110621034100414001c1052002800215444a0b2580301808141c0c0a40301c03401d40501e000c20a24408001c1d0740c42d10745960107100c181200d0800055860800300700c40c0c100c0c0600803241c000810050010344640005104200d5001d924207000790307041c03000b084d2009120402c800c2c038184e1007100b04000310b000e00000d09400114034a0803c105903030307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 915773732 1250 915772482 915772511
    0x30f0618080c0601030c06084b0103020102150f0606210a1d0109080910020321040b060d0f12050405150324010210090816030509031006050303071401 66
    0x1182c101041c465104000501c1440380740c28070440249090700d04508285044401250a14003041000400d1040000003009600c0300401441c240514040011a11200003048002c580700a1005034054081c807180d10045440100d5018403801c5804110a8652103141c140141d55001031460240c41801c95180482d4a0020804502a0094542c00318031040c08200d564902286002c40c440c0e960314001d01c1e0000202000240d03a403007031044803051030306a0400c000340e00314410074400c03a44948030b140c95851114880410319005600641000b0a01e644420601860140106001e4000d10300608030100081c9a040c80d110518410316140341056607502c0070a80b031221400e02400003030004002c00400e5000d00c113200128002c07030406000c1e2070300c0440000c4d44500e42d86144090554944140030144803031001203d03441440141219504130103400c00400329000b000b5602c0c031a02481852070078081450040c0c0d42074820081c09146454101e9030b8200e4040042242c0c840b05540702c0c400c0c5010001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 915774982 1250 915773732 915773737
    0x30807020a080c0309040c2a0807141f020a09090203040606080613020909010506010c03081f06050424120b042a0906110c01080a0b09090c040e0601030f061808 70
    0x1481c003001145c880c16000e0800042e21901d031100420003084180000030204180848181d10b1142c10030400511568104960341c2e2140f1071001e41300b192902a80c6060301000540c0302816908509402034041d0b909500300241d02c540240c0b031000610b00383d000d0040114030b5000319009881039500254090351065140d041030000c079803101404e8409a080d00540c01c105040c07580c040c0b000ea0080029282400c0060983d024600014042001c142c000420303d0290051044030190240070320f11307110b41c1d01d16008041d43d120780a0041558405a4614408150304290040c051841c0d25043c2c5a070200c440701e0802000408103c5510940b2070a034042c0804d1400301000e07150b200e0711084902910380f280d0140081045511020411003c202c1800380c1150101e01d1103510307002441c1c4240b2503100c184013000038003156070603550700060303150601646210020380b025950005560600070451150b0407a40c2b5100e0920000c0e048a0030501003e0000702940c3c01700032000d5900808003104a510380b40c0d4445078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 915776232 1250 915774982 915774997
    0x50703080301050109090b0a0b0a022a0112140a0b0d0204060b0714030703020706031503051c0801141e060c0303130c0509042f22051501020a030807020a08 68
    0x800c4000014441c40d40e005a5000107011000300610100b5089404201260100d128100502c0000321701c7c030409510038030009402e1078000e0704180344100010319200e0380c1c03074400f007045000c6114400e5400c00003600380113028006154402401566580e40e00c164090303d14070281d6980010562081d1340166642d01c0b903d005040c1024010340c84070800e14051003045141215010340394420f215540000c1c6c4d00150002c00d441092030041514001c10030020344103a2103400c02052801020b01c504110140864290001c0c072007a5030740c443e2640e0760048a000c00040c42145508032603811118071100748040070490001c00c01600407441c00e00c0c0701100350b0540d0000c1e2047e418601c07150b152034082c400302841003030240c00125040700442c103103552440040300d405c1030311003035a021441d41d51011003495503a414a15002400d00b10b021150100112031001c00c03102d540c1c101c0392074803010944114050046500d0207106030001e1000040035203050f5040c0f0340060403042144074020412000840080240002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 915777482 1250 915776232 915776243
    0x5071e050d05330f04020f09030c01032003090a050105090703060b03010c12240b07050616090519080703030f0f020d081f08031305090c0a0f08090a050703 68
    0x12001c20103450000e50b200a000440d4201050140e0120f03000c03102400080f894a510900001d06412004141307402c0c56120b0042c0e02c18400f00d00c588900c00050002d24a00c5801c03001c0c1e604c1109614019411220008080d4200540d145590604010107400441d00520f4070740803900c0d00c6850f070b994513007911001c071903d0380c668000e200b00f00204001801121600c42c1c045009000d1070207051001802c0d02032803c156500039444030300c500792586142002009812407080c8000440f6110801c0c25141ea2150b0b100b110648a95000500052070b01c8003900c00080c500e9a522180c60302c0c02c0300300a003940c01c21604070f1000e03900c40300005281204005520055100e40c49074090700041c3c030009003400c040c580065040d03400480035001d2590b0300050b441d0780041c0c01000d6510b1210003900b0485840c0680d004020140b1001880c0c0b0a9122075414460445404807100881941d40c01080307902802005a490041040494448070007801461300e581e015403d9000c8440e17181c62610341600d07112403940117944 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 915778732 1250 915777482 915777487
    0x301090213152c071209060c120603110105031806090a150c020723060403062f030406050a0902100306030c06021b04050c090a0b0c010b011b0605071e05 67
    0x84042c40c504121004215040010101c01110755191410a006002403203511014600049541c0d008100c0000c290b81c03911350400c400e030031501c0e26900600405449130049001544403a503c1c464500805056a5000d40c0c1018442d000100541d400e410103000c2c1c2c0e54414240c0d40c44000b808040060314411002800202000400740c00c00f82d00350f0622000c1d4a0a080c02d114408000303540000e082e10488065810440d2000a9040354450b00c1040e210713281d6203d4800900001070022a40040da00e0b400074444d6924118102c05500405084c0e400f0440c2440b0001c2c000100480c16941c4015408103100a0100b04112258002605040d0f4094940c0210344c1d648014014004400e440c0809004540001d091440101941441c0c0310341000d01580304944030030000b031070b68209105940b241e04000c0e040302d00072900c400d214540d58000403c0d10925610342054601c0c1584a2b0480232405101d100044c460b06607141c03a20005054010700035400e1100403000058004070010442520664603a076298 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 915779982 1250 915778732 915778751
    0x1103070b01051813021002010204090f05060a080f060103030c050c060a02010f060504110f0f190f0e01020303040c050910170c091008062404231806150301090213 71
    0x180d0508010300021900c80b500040004d41c501c0c00854250240d01101d4440c0c001c0280302049000e407160350031075503c0c40d06011000c0d10001044d005140501001c60b0212103060f11050391698440c100d0f5040fa4043e0b101030b00420102e8000c00c0002c206a02403020b940e00340c1c80714000304007507030b209250980040c1e554aa510342455040e109800140008450a000c0010741524181c203c1c050365081d40300c11800000d803805800b01c01004c03901d544031041c040c04d4a92450360400f03084c907240301c1c6046003c2201140354143c0c640c40030007200c1c403d5500c41030728940c1d1403e200900c00401030042940c0c2c0384030030064012414a01c501540036100e080b210042241c40300800c00e0003140c51001e401101c00700d440017000d00c03400703401080ca41e43c4a100080c101e95445c4000c0c081c605140d10818441d50094900381d06490b180080051401c41000300818400f0907481e00c22003489090511014032881390031640100c0c6079801031036075600c201e11009002044401f02070b00001d0440c60b02103517000c00b41d0756032100503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 915781232 1250 915779982 915779989
    0x11012303041a0f07120209040f0e0607110106051c030507060609151a030703020a090e09060103170c1b03120d0603030e0613030201030c1115010618050d080a1103070b0105 75
    0x243c0c400b45095040c0d08038107001102a241da6480c070155245140c010501a0698480e5440740c0800724205005101e031030041011152150000c5d219040024030b08011402c1000b0140503c42c116007005d000c17a2040d4070694199190042000c600300c041220402c11040881d00c94022030028048022000800c1440340603024051010340d800801d407840188443e11904880d0401e0303070382c00070b610f090140c0c0d1426142000c640802007074120035440203441b001c0c805231007030008115050b03d02c607610200b02d40c000d298000b0914000c565140146510112000806103422684144410300140c2101d002c48061400072140f904901128442150f41e01c070100185540516408209071007500d00034501135082e45040500a554000a4181034640b846010001e105010303024414204005039102240310070280f520300785081c410280064294140f000d4036203040d526910468100070030078584159a581e40010300d0704000c90100c1030100701144030380c01b81c5040c00202401031040030307024017940c106400c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 915782482 1250 915781232 915781283
    0x80c010506010e1801050d060615020307151a040e0c120c0f060304020a150e100f0e12150a0605030d0206012c130525031a041101230304 60
    0x490b114001c4401480051a01c640340c007415210701f52888400d183da94200900034103603da2198010346041001d00551940c0071019120f0544510b08403404c0c181040508001c0c0c4124955480122000e5801101e0614090b442041d5840c0140191106000310304001684900c2500c40082150080d200403080781c6040f11400824200442d030403802c2d400c00b80c010420a1040e402a490640d2860801c1840c5501610300c6002881006009817403800c0c03540d0004044e0303d1041180d2000c601d000450b511946402801e00001444c070100504800000107444500900e000c1c3c00c03413602c960742e00808511510180900310021010390010900e43d40b4155418000c042c0d40a030040881d011032007560060120001910b4126145100c018001450390420a0900400c04078800700310180310741800c0400c2810b1400021240110b0b0b500c03c0030902000e04000d6028215030040c4144107601088405600944035516040b2044034040401103d145d520081c6602c2130701c3c15200a20784000b14840084010b0341c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 915783732 1250 915782482 915782507
    0x1060509091803031315020703050c2a1905060f190212191709010e10020313020d03090306060801052403100f0906061508131a040f080c01050601 64
    0x420184141c116119100c2c0005010814001c805c2c840308000c0c007582c0c4c1c030060307034803c0144c2c02150b80701c40307070710f070141103a840035010202c14000c0714008091050061100758203141440d180b10a0b00880070100900d0b02e5440360300c00c03541d0483d60f0700411107072111000383c0024594154610b80c0e03111140c1d044044621031078120f00440d804076030100c054032481001e45103c6c030302400e4007560107803a90200b6030305880c00803140c080c19850342e005c01075140015005250300081005c1070b5059044034018802c2648400c8500314031429015401500500700b2511040341c0500a15058801d15241d1365003805036003050344590342d66034455003400501660701d17072090301900d0100400c1400c0d0542038042a25481c280d403699400583c3d41c498a029210140c00030480d040c0e203c0d1042207110385404104110071030100030f9074002503019001646105294030008503481d00281502e51104845002844441009000b00c4210100c20f084500003403400c800340200d0000000007045500d80078ac00180100411070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 915784982 1250 915783732 915783751
    0x5010b031606030911030102070c09060b040609050f01051b0303010f0f0509192c0c090903072d051507090f2d030305030f0109021206040213030501050106050909 71
    0x400070035801c12412508000c40c1e1550801188020b0b003401c3c0240c0000c804040d49405500006a107400c000030145424146d032400c050030080d207600d43c0c0000c4c00a014900403480410003e400c24011490700301d001c0000402d051412628041c0c1e81310481c2032520b03200d80d04896991000c00144400d10784026100083c01c40500000161498040003038005040504803620902e404a13512407101026040411190846000c24942c1350b89040e10740014000b500401d0018058500a40181c1c075088003418000c4000c04011420308000b512015541021321404900000e51150f24540d14445c60012400300c600440c05000f16041c0028030b00b9945a000b40900f0800c21300080c00d01104504c040e0900c250740e0030100801c6010050740600705030b4414080d5811500c0e401060020801d68064011441182641290f200e5a641c6001c40d00603070040e5110176210140d01e000207486030500d907014012881510340e460f0301c02d954a03200e09003101d4081e005607002842c00100c8104500308203d0f03d5030072400d0032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 915786232 1250 915784982 915784993
    0xe091902010c0302010b031c171005060a18091407080412031a090916080f06070f030207020a140118120b040201050c19120309050a08090402040b04030f05010b03 71
    0x60020a0900101050003818001440b40c080e06042c400d44c8400c64042010b4111602c29540c1d4030000040c1c1c0240d40408001014000d8400c240324004c91458011500c81c041c0308d0107241040104042608210100c0c410403440c010b0101000207020603820051104610000b80c801c260300d00040d00d440000d29080030b03c0701001c14480002c1d8a41d0300200d080000d07140c002450304142204121607091006440c2d4040c1e0a04103101c1c01010201e00c42d420345040e0420051441d0341c5510240d101e14604100e04d410350044800101c4031400703a80c1d10701000c101490010302c4e07c2070030741c0007803060351160b08030001c031380704900b0304d8001c0d035800c90b000403562403008498880c140c1c40c0ca54480d070840391050000b4552541e40000c03408690141017a2500800c0c1002916a81c07002c100702800300c0d1500c4007050310364003508805000b64038000d1107071404040d002005000d400c00e0340c1c2c0728200709074480196150403941c200800030b01c0781d5a11b00608055407186050725850011400e01909580c3d4004c8134900c00e0308203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 915787482 1250 915786232 915786253
    0x510090b100c0213020c0109061a01080702060c09010912030903021e0904060e0109020a08011401150509011110060b03061306061706190b03271018080a05040e09 71
    0x2020400182c940e044038004080c00034140e00d90083d001d02c1c00340b54000d60030107030366504005442e0022100c8001c01a44035808100c941d0044848800c1a202d40c809a04814003044231004448002e0035104410b04200e10f1156036840e1034180701c28803010030f40004040c50301c117008501e000c02c0000403040c03c60415829080309a400540340e001d02510003031900b9130302d4280b1303041036070700707402c1081e155400030031b4001c089551301c1e07181d80680010100b00144980300000852003174440c0d49801c20300d2030300780e0b43c840c202451140195201010380b6899100f03446880d0101100c2141c0340a01e40240200349001e54885c1400303400d119102072081c14031440c490410300180007c81d0f0000105001002c0c4102d885c030b00d41c807440701051044820010700360b070258002801103055107242008600800c3c003641c205280080b602141142008603422402240d0081046500c03208610341081d00b4103180d86100709841111541c461104d036002690341004100040b8041015411102c00350340d2203840d00029000b803261 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 915788732 1250 915787482 915787487
    0xc020c030615060c0a0b0f011a180f030c040c02010209010e1e01120f0903090302180708010b070606080709060602070e1302060f121527010b07150510090b10 69
    0x8020b0768001c0c1d401090040b1010010410038504e660408400318060a040d03002c1c641c19002401400a02820b000b03070340070442d14210407a00c00d842072081c41c081d034501140030856000300c00d9560aa041c440c583e02c000d4580d45038865880c41003120b800060707481111600151036080304003030a83c030407024030341e49000389480c011440500c0b038401d1900c40e0200c200916104018100982e03034221703952920b94818101a048032800051b02d000b1140f0340399942d00c01c40c41341c524090482d541c0f000038808000401002070b6010240140b240300394001300707200703880e0702085181103100d9204941c0a521404100a0300d5014041030001d8040403811602510b02600300012302c002e0084001d004110000e07212400f0385154cc10780f03c1d8003e424081c0c96050501039401050001d8600c0c01d14407072000703081c000d16003481c3c40100481401240c09103811503880e040504800d07811074a002e4030400300340d408080032102140300e1584100208c48005030b455040106141c21a40c01984442c0a40c45071292355030707200d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 915789982 1250 915788732 915788761
    0xb06040e0c0f0c0307030810171b040209130516020d050a0e06040302180708340c170c060a051312050d0c090302090601020d0c06090c0312030c020c0306 67
    0x24542018030359200c0404141c141ea9210f2044041c1050001207042c200b0140c0c0100f401c2c2c020582c40d154810f0300c5445d000070300e03006182c2c00d41000c01540300079100c0d160000351280c0100c0c00c0798014801410070480d10007103800303c001c00e00c00c001041d54a2041100b0400f401808c000c0211040c40100300041c001400a4802d100e4100b81e1000c1c465000b440d80440d80d250340407035010b154050114203502c010034480100c640e0042d5490340120303400c0750004400d005080050441100140455240a20105a51200340d0b0803014040c2c100581ca41c1e6107808600c00c01c1004800004c01ca801d640e45540c0b040d56141071050207412004441d0a00040c004014440360f07080854a421500080d49040e207400c0035652489220110040d02c1d041400059410383c10070301041c12a4001d50302a4865a10070004a866a450181c648045035101c0e900801184950b8821801e0500c1141c8150010f80c59483d11091110001c444800180c5c5407440c2c41d4809a040c006008040000e9008200364281a06071140d80d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 915791232 1250 915789982 915789991
    0x150c100b09071803061e1d10051803030f090d0c020a140102071a071104060b04121502040e070f02010614010c06060e01090209010f0207031a2e090b06040e 68
    0x44281c5401540c3c81c4030499000c0c00450307001008200b00e000d480e4590502115241400168a26042d5414501c49203100d0020101c070001c2e000d8405072018404072402464040e011040000d40160b03080c1c0c02600c100010f42c010b00c9200329000b118505060b0542c500f814040720b00007000360f4604250010b840c0c0460820a603004013050f00840302042004074038003030b095408011b1041c04200c0811070700d020140249070b140d000e50010412110301c0002e010070703603206205a2418a41c10001040344181c00ca082c115524031070b14403005034901c0240020143e0300310b9004000e02d1519001801007140d08558501042a141d00081c003056180c14152405600c04d4608141840382c9080c10700104101a031000c8003a000302d40310000c032561980442d070000e4100058240c013040b11154803c2c03056000148030350459500c4000c0704020000307029803c9018070050460000d00c00072001c0402d0b02c19000b400c4e8030b03125056180401c0103524110000c8142d030541812240a9241000148a02c020058101d64407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 915792482 1250 915791232 915791237
    0xd05120a0924050105241206010c06060e0105040b09100905090f01090821090604170909070c06061215050403020c100207090506040608030a0e0f150c100b0907 70
    0x41212410030a141c0c5480100503800103901c031907520502102e40c1c1c01141644c00541d60b901d101d501300e0554010b06001e0948003a0340c50005c2c0030711010110a0b92800d40d100c2c1c07061604440200040d982c19040c1ca6682c0c008652000b000c10040c00785080074401e00382c0744041100c000407641020b511a0518204074040c0000080d220f10014640f0402042a030030012401002001580114249000e03e508044800c014000c9070740403042580000e070512f1406501c10302e000d0500c540f1643d442e45032820021007001030003c014020600641c0e112030005114546c2e1b5119040c0c41c000503d06181141c0d165004504204412407039900840c11004000c901e101007001c002815843c2c5040c02d901c3e0402201100b54020966480300d03035401d0340070032180121800c1c4a070a0005840382000c00c010365a00d40101710503a4002c0c48900c40191240ca80382d1040030740600700e03a0012b105407012814200003140000a40000014140070000342000381c051022026601048540d92460000d800c01c000070b0a001d08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 915793732 1250 915792482 915792491
    0x9060904050421050d231911040e100504050106021908070206040b1c090f060f11041215060302060301030b040602090303071a340908030c0c030d05120a 67
    0x811151811043c5140c0301e208182d020301d15640c1006080d0f41c002140000700c2070411711a01c403c0e08040300c4d908001e61014070449a0346c3d8030f0099210a240c000c03032030a850703140c43c0c444002d14032100318024400360440c4800883c403450003241c1068112900c1d40024040c0d440c0c6401000301d40e07404500c4c7c100c000038885220040c2c0416080001140c000c039100a0350243e00094001400e65501d0010042c2200c01e4501042c070301001c1c5460401ca49800b0720140100c0040444e2030002101a80b162160242030003000421040c0542c40d010303150065003222040e888803c0c904020b101408000303202829680b04180401c505503408258940010300c0b00400f1401400b0219041049a03010385a16a001604507515a130081c146000072a018610b5110030310400c10100e000d9242001890000c4c0108404a46890340703c801500d058600c00120709042200700305021500840904c000c0000c0c1180380001c290300d5095070101401e0081074a20340d01408010491808480301c0200e51541c00300705101c0016 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 915794982 1250 915793732 915793741
    0x40207020a0e0a0902120d0806040e0114010608072d0e1c0614010e1612060506030a02042402071a0909091501080102280212040e0603010b060906090405 67
    0x9020040d29009180114081001c009805083d540a00d01240c001c64882011201190010b61035100c010381c184005540040024400e0600d034106841022000d800062840170310141503100300c1003a0000c20008200c4401d01c0f2840d9802201c078000007200d01c980ca80380b10210060a1810305000103001d041c05900f1140c25543d03910f0722b0b6030200007200a19030740c200490341d14040004051320302c110242c0e080d4050022030100d4020044074403500c0207200c0c800c1101520001910a000510703c400300a546854020509480d51405140181d040d4040581c5603400c103a200d003441e41c08440e64603401c2480601d4510300c1d03a40022854219010f10500e2080d50380d254115200602c00d00c912540c010400c103040c80486680004d602ca0002003000c0d04d400a6602c80501c0c500780c0c82507010130050107140109602c20310b00031103248801001c0600498660410103d841141a00203a008210341201c07081040711905080c001e002c0f1a10044aaa40c90b001144c0001f400602898031050b0080d035a42d0b0014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 915796232 1250 915794982 915794989
    0x6180f070c1709150a020a06050603011b02010b090105040e06041b0e0106050702030c03060606070803060f0d1a0f01120620180a0506090616080f190f02071404020702 73
    0x3480420780000c80d0b10705016801445418035401501c02d00d000701d44c608004c2c0d081c61400002c2d20051142503003e131490644070344900c0050301001e071000d9499540d507240f0009004088080301010a0190004502180490100141c2100c160304c00c40c0141d04043c4088582c05010440c030b035102d42e015000c1d010442006c1400001c408040c0c0000c400c12018070000b203049500f1801a00c0c0c141e00c01c800301c0b040006082c0a054a8040643d240c43c1c1080043c40503c00080342500550fa00410160841c03980301c03040300010345c0360102c15409407808511401d1481e11005034182e2982d00c00c1290950203425403508d01100202410b9a001802156895000d92100341528103403050790b044000e0700715101c149114201050902034600644034a2040c41d0004807401c1c80020345d42500b5000b40440d09002c441c4008424407200c64104440c2401c0c10406070398103418043c041c0130340c20300c0c522007000310b000b1080c0040c004012200c01001590b103d80d0342040040101d4640505561061301d01584230011352011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 915797482 1250 915796232 915796247
    0x7080a0207150507021002070602030f2b0617030307050a03022101081b0103060302030c010305042306011d040b01060f0908060a0c0306050109063009030e0906180f07 73
    0x102007002c1041d0025920070751240140088500845040121491300d81051342e48175890b10918000d600301780315801031044201701418040e000004082e00ca00007654070740307880d141e01801c100085642e54131b0500100640307094500004040c1c1005504d103043c25800900a4000c41c48000b003055000030390781192940489444c180c80560841070306039543c503060095180d41c0001038480050504a002120f150b110f802040c08898001c1c003d012420701010044019140c004c20a907158246500c06a0302c50300d0640c502d1100d500942c002d014654109000c400180040d6207001e4a6002800f060002058018001d94111a0b20b8141611046041c5c0800d4880300005e0f400b00100f8003c1c0704c02c0000308034298208040940c07290382c08119150702c40d001510480d809008a80005002000050603031202104460403001d40c400b00b440031210500403007058529040080f8009014103802d01c0c0c0a044c081d4a09030807480c203d4440440311341d070740e101c480701030001440b0307800c12101440840d08846c041da00307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 915798732 1250 915797482 915797489
    0x306150b16060e1f0e0d08040b1810020a0206060901140909070513060e160c2604081f06080307060216020303030907031106030f181501090c0809010e0307080a0207 72
    0xd0b42c80c0641813521800c00310313407100d80500d00c0c41d0511144020a480100d611100a007064079903968a840e1a124843e80c4203004000c180490440780703c1640300c020030003900504e098100ba001d070362405510402400c128003e00b08501603040d090050005280d40348140b5607a0405a606100c1540c84041d02072815449030300c8160490b80100301450003903034941100055400381d41200296864071190045061880007646001903950013001c00090078030480308410400440b0342100b01d110201003511983d105a000e4a925404408129100c0c3c502000c03a00d1640b01c400d004009581c640801c1c0e90b200e2141c03010052040d9070014101e44c0c45840c01c8502e111264025044030745a151021085954289500003910500f02c0b8600350b69640c5000000ca0340320700d203c1e4001440c1d43d00c90815495401e681038140041d1130191614103034042d0300ca0780b8141d00810000310085010701c0c4105c0c01603d580c8014040444903414030144510360b00000007203620a035404000d03640d0341e12505c0c20403414a1038940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 915799982 1250 915798732 915798761
    0x6080112060b040c11070b0301080c091503070611011d1c05040b1914070201020a020f01051c020904060902070816020a0e01150f020303040f03050306190801060306150b1606 76
    0x130a116142e03a11550210b07102165500b10782c2d026440d2882210140000d11460100d6070012848281c1401c05140d0b840d080820f0203000d002000040000904180782034102a00241f0f22280c400610b250074052020054555041c3c54058084800c41070385609500340e05c0c030082d00c4080c40007907039184113600b2a030040650302c0300203444070541c050311041040c2c0c40340c0c06400900b80a48801c0039081200840f07600d1503050b001001565101d900344200100549003850600c03000b0b020ba681d03044e6080d450300c1b0022140c0c450059480382482c00f00400c0f900283c11001c451481407120400003602442202c0311581c8440484143c804030b440094000941c5400c40d180d905001000010a12481041696205500d44030072041300700e03010089030b99020451f4080c080260720581c043c0464029001581c000c1030141c0f1142401e081032500515103800c9a2001c90035030344d114010803e00c0050311030b5452442d2061035030569545040707038550f02400742c503250b0948003204e008500c0420405a0010f0940541d48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 915801232 1250 915799982 915799991
    0xe0d111509074b0503010507200d0206040b0c040302060a020a03090b03190906020c03040311270a05090118050604060b1207030611041d0109060b0406080112060b04 72
    0x40e01d005071180b03070318071034110080c5001015109103100909110714074109014090003c01440c0c19070708018010a0707042c010501c0f142c1001c62036440a01030a880f036400d07901c07022840e000a0308109543c19181018406903001014903654459010925035041038003e51900119150060010194802c0768002540070500240240102d6008582c042070b2900a0b200c5442540c0c1d52400c4d04030501c400c41e10f245905005071415403801481c0c0d03129007802401a80f0040c18140e02060f0b45140da480303504107458580e40081d006038030340380c8040000c00c500c0764030b0405000b400c0001840c0d208520080c1189203002d484000080d43c031403095114840e0444c01300006052100036040031901c0301c400761001c1d141c103410b090a85070306040425a44000509120041403480d15540381c00008061508400342c44120420001400030280e00c15800307880310042c10380586502d0101c12208450055100810741502800304000d00b90700038201a04641c0344262150101182d07141c00c81c01402c1c6078114951040c5031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 915802482 1250 915801232 915801241
    0xf12020d0614040302160b040b0a0c060603020a08070305010501084c050f10030b07050711060406050316020a0c0b09031507110c010e0f04270501021c0e0d1115 70
    0x1150031486c151496418003040c2c688004646c1881180031740c1d1940c6008100c422041c51041d4994a0322600800d0006161a229400110030072590350104082d80e00c440c1040c000e205003849058010505000144039146034001c0c0c01940c024000e01c2c281c000c5003069410b400c8a58600d44a50340c80010400307010245110703000c00c10003404256210040ca01c0e107100040c900c40507014403030060380e0b000b00c0786101030ba807030103021140c0b68070080c01119611212202400c883d220f01c40584094045619582d44070700c1e01c2d40703034413110030015071448046500101e070f001c0c00324180000d0607090390b034003c0199603036503100001310303192440c000000bc8032181c0a000704580c0c50780c840020190007044a080d81c0d8414004c0e401102d40c43c4500412540c80400942c6901042c07600e07a000c24220000d80420300f003c000007440748a040c001c400c0007910540d400003031014003804035540409104a0303502081200d080fa001c145c0e40d0301c070071041001050010440800710715003420080580c000b4000d0326104520b161 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 915803732 1250 915802482 915802487
    0xf100204230d0605070c02040f050411061602010c1a070f080105040e06012d0305010c03060e0f0f0c0d090f021f0f0e011206060c0203070f12020d06140403 68
    0x215104007a242078184800082000705150008160342009100500303060b5030b9200c100043c0800382c05c0748184044801c2c003500588550041404288800d200020300c2d2609062907243c0940b110b100602c03a01017080850034010182120140164084c40c2009940c2910701d080c0c6d01102d04801c54802000707400080001c00ba0307000c501c260100005a503084442d0340c0e11400c0c071080c0c41288080d04001d4119000502142c1d072000d1168150081513410440303400b0f2080a61182152250003d564a075112100c2c2e87e26107130107000d080c0c001d12090402c2e052510b400307400e60a407400b0140109250a8170000410403d4494006490204661490412050034146080d200403844404100e001d20b02d8401d89003500700c1040f09003064038030585c4036017100303c1c6c9084003202d02d401c28000301030500005040c08030843c00103108030006800769484940207044507004051514130300d94410f0040b8848040140010303001e5a4114120680c1601c090f2a011114074043c0003030306118820f0b6910350f0703a4001300f00504d607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 915804982 1250 915803732 915803737
    0x1701290a020723040c1103090409082101080f03120106120f0204060c0203011112010302240f04060215011820161a010e060907030213090b100206040f0f050f1002 71
    0x1c100315820808200c0c9808203441c080d43d0f45880c413981f50401d100c0110b0500b455001210380503c507038080c5241c1440703c0000c00880490640008007170680c1401480f00c00000c219204a0780c010744003d50403c900802003c0814105001c0e02c0d041050305480c5401200072500846000607403000155181d40c2c5607800102904200c0000340d00c65800c05501d051014401c40869864000742ca1900d03c0da68216000e00071214096480c1c204842e611031a009110303020180513081c0c4454401c85503590741d01d42440246400c00e03035841d80340b01c000b002c0d00400081798903465000c0da0a40d6003c01085241402c1e00166042101c0641110901c40000e401e200c64001c80e055000080e11a408a41f03d000001c40c12804410090158246103040070002c95010b00d002441c0c50350100c0c00d450054900350702e00c0a0ae2401d0758895119811194a560303038184149040644045e24100e00d00c02002d90b0324090b101d0b1851940468405040b12421070303000383c103110042c0314034810240d04500311603414000105040003035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 915806232 1250 915804982 915805049
    0xf010e0115140d02100c0803070801030209010b0a2313080a0c0e19020f0408010e07090c02010c140f04050d03050c060a1404020108180d1701290a0207 66
    0xa840355004a060031032080600c2e29400301030522401a0560350a11554008201c078100620000ca80100005851800114030610300f0346d0340d18806500d1481485580b08040e040400803400c1031009002a503408046000d0641c2d001440007a80700e04644011000d104400060f80760b920b0791342011895400010b01d001403248180b43d60031603290340f8408418a490151a444028500c403030f84481044841e07000f500561088604143c60305685448950840b1b20f445143d9001c3e4004031401c200da4001481511b810b002c0d907000910841c02c030404000e1540204d0f81d07070302c2c003070483c00714115601282440c00e440c09484081c000422030161400d000e4500c0c3c0002501003040d11998000071132564403030103240000e1200704000340352030b222540150380c0340c40c0040c041032554100c0007026003d89000c01000c0c1c0200142d46943c804e0440d004100048014140c10004801d0f032103030b400c2c60741d2802e07610804501400807040d481d103e260554089041544039070141e04d51420415141c0d020079078058031b4800c3c5c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 915807482 1250 915806232 915806261
    0x12050c1801050d150e011401021207020105040510120f0c020d080a020c030a090305010c0c020604030b0a090524090d021906020c1c030b03060f0610020102040914040302060106051e09030f010e01 85
    0x2987c0d0b11901c81c10b500640d5190725005030008807808030b0a20303500018010191050401a0130240c8600c0860402514400f0403800180d2000f16140c031001d00d0b12500880c40381b204000e112015020310040e5840c00103e003c0403c000444c00020035003c0558181c413480c148800540b13640c0c02003240003c1c9203800d24003058910b546017011a40c40a4081c0d18080c50b01070303000d0001820140785440b0a00f8036440203081c1440c10351500c8101c000100c05010741105901c00c2c40c1404050b007501d040071181000001c01d0300c00c4591218200c2104c1715000981540e20101900c0c5040f070b55001031a0070380290207035002e00c00c400c0c4a81603015000c41e1a103a02c140003030701580c4c0d08100c0044013000b010b60f169003c0e0b544030001c80e082c1c130100740300d420b00c03180d000c5a1203120b0001510b01907888590204485005503003244030b03c0e425052008140d810700c0114014441c2c0d03c1d24a040c502c451049001c5001c03401010301502c10700040300095500e050100c540d000b00b41d030008102050900d403000d8080c00f1303038120030150b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 915808732 1250 915807482 915807509
    0x1c1716020f07030302060c09030102090405100f0e010b0403020402210408211b09011b0f02040b010c0b0c0922060906052b080717070312050c1801050d15 67
    0x5402c008030703034150f4010401e030f4943c6c620b0013669501030030410307405540030004003a041d19a4054076002c2c00c50004072411051500740440c07000c1c00c05030040c12240c40020300400409061800769002d0700d404640041e902c030f081c032034a600e25110348440c8070071082001040109008205025207014021100a0320340c041c0300041141e0750341d0f012103a075282014482d510321800d00922000c2c040744079041c1441030802084a4600b0103000200c1c50441701c948505c0d0303045045060a0140c41c441d074a0a003000d40c5903200503a100c003c1414014416800318401007440340480d940c150803041c00298005121441500b8650502d001e041c60740034600c0184e00b40310f40025281841c00c00ca8105921108420740a0117401d46403040c075960105c815140002c040c020840810765280d0004115000e0060b03881e07464041c0c0c6405410341c0000720078581540d01c0d00b03003003103030b45c00112040b140c21040c1c5101600c89841102c0050341c4d14010003607a080d81900c0d0201650000030354520300340070740c1c0c0011006071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 915809982 1250 915808732 915808753
    0x709020d0c0c02032127030c030616050f07020a17010b03070501050a0815060f1b010c1704140610080c0d02180a06050d0c14040b031c171602 62
    0x1562440c2c0d81900070b416501417040b8030801c1c0a14642180b41d40440002645802d100c561480246401407151281d0404851181c982030b142c204807074143c140c1c055014204500d4880e50342c202c580d410b051080d041c044001008070350000e81b1011070345441d41c000d2001000d26160300000056650032407090301c96600e8080d4884092400041034000c9900c1692404e14002e1501402c80354108003030301c003c1e01507501102c1c0c0746581e41d44070080c141c1202d900c0d45103502e455150034400b0340c0b40074114414443e0f0349840c001404156100c0e810011700551440e494242d40c44074034140020f0400c055810340c1030f025800070b2040340344244061000726801c0c802161110744024007080705c605401a0025030109503046c8514040020707040c4070764401f0001c500080d8a650f100089543d050f07421900700e81c000e0400784203202d1030311501002196000c2c26241041441e050030017103036846a0034000800c2241441c880c0410380c500c2801503041d120404e00c062085030a040c1203c03060400c04140c0800940900e10004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 915811232 1250 915809982 915809987
    0x30203160f020108090a0b06010c08040f03110901271e2a030e03191e0804350309010603020d080901021c051e0405120c03060702030a020723030709020d0c 68
    0x7446c01541216208886460b003000560f81e0760420b8104681c00308060100103015114040124000c6000b13104920f04401c50f4001c101c10190160811800912411290701c01c013a5060305490b84109109000a05c2c2c070b00c040c02440301400a50302c2c0c0b00070700707091083c501c0c2800d800c010021040d201c07480700c0c0e0402d1320700241c0640580c0c009001002e941d90043c004000c8c08061032100441d850036a04080359034030441c802d03040c8040400d19881c80400c01c800c1c1800108031541c00503242101d80c00a40b851514607541d5545054001100b402c1121480800419400d80c020745c00880210760003403900c120300145113402c0301640c001d9400c4c0c9015006034002c06494050003034500300788104075500c65180600054804c013031810030000e1520b51460502001c1036a1b1a681d05242440c50b082004100c030900c04010185040c1004142e442150018009003a0083d00082e9032815110009048400d000846c009600c01c0010b54001a90510882d84006100c854545c02020200c814010a00200340d404a06 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 915812482 1250 915811232 915811243
    0x20a08010e031c090807110108010510021f0f0e0c04060501171803090d050102120c0a020d0e030a2102060601030b090a0c142b060803090d030203160f02010809 70
    0x1040d0141e042000f01041d01c0074000021800075580610000354110140c6988080740c0104000b1150309a00e071001c49601d40e0842c032002c3c0101800c1340ca00003d840c03d1100291100141d40191001c1440075010701e0038100640c00c005c11700740034150108801c1d000c50701c4042d50b401082401074003c51410102242e47d51140868a401094003002610691140340500c4421800078a9000050205200d501020354031a000c404c040c5000f0000540c8541c10001c100c540c60381e014001e41c8500034200882e00741c050700802e4241001c04103040407040344060401081c1050219a801003502a4a144090149600890741d2103000c1107030303080398440c0d510302e030040d01119044c500c116400034106000813804005504203a120a0305468000601200d0022450f002d811441c140d45c1c1c500380144840810702c401d00d064400030f0003242000e00803146041100d40d22031107031080e480c0c000e440b040b00c034505060007001100c02d18442450703443c407508810b080040655160700c6d000c0340002c4074075000c11011800001e9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 915813732 1250 915812482 915812501
    0x705222403080705010e060a06090b0405090d0c0203070b070308090624060702060d050114040b19030b060109180606110a11091909080c120a081b2203020a0801 70
    0x2801000d5003140c40300d00c450340002070115295074031100b056041d003030280010350092a20b040e004c6800c40c1400003c000b50307200241410b02541c9080100109070100046091050600c1d0809903509030302c900100341803080c00c2d00081418000011920101503001d40818401d04ac410240c580036100c92600c01418041c0c4100708040b4644811440800d1610078024504148000c2c00c103171411501d074150360b00313848090744410062011802d0840f0305003400c0c0100000b07403808903604014405443d440d00c4082c0b040f400301411000c0c000300043e0660b4001c2d451200a000c9068003164040d0001c0300c100040d000600621001170b9004440403d80f141c009046c0310b0b400e6020024611550920040c4100700600038004411923185003c1c4001d610303075500c1440c1780940150180360351103c140500c1e5203088020500208800c1d0100300030010940d2085155403c1024480441c543c00b406480503842c0c0d00400f42c108243c28000036003084c00d602e41c025441d0449200b40d0701c01a40e0355541c003109081b0350100c203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 915814982 1250 915813732 915813791
    0x60a080f030306100909090c0e01080724091d07090501090e0a0f0f060f030507170712080910020d0909060803180301090b012d0b040b0c070522 63
    0x40070560078130b000c003a80604050a8600003145a668414600c2650540642543c0c20f81e03a0f034505001a03480c14103c1400f614004c00140f41c480e140ca0000a00140c00d131030302c148220760150027080c40782c0c403502000c00208540c0758102c1c210302c0841000815090b098030700c00081154a4000100c550145150030225400342c562203410b40c1d01c140c03040c0064146030030080300e16a074031201e8288446161242001400040741ca011026045181441c5080110341042440f90000c0c08042282c081c00030702c12098814512009410b0280da2034800c0650054645803980069030140d0000c09540c00039001900140070b940e810300c180ea03503402d140111161801080e400d40c004108030405500c90140764080c10101800000f40b62189440d03c0100003400e130043d449000c82040c00301c0280b41c010104e00480c0d20f00410f020809460401031002d144a030780304000c4211004180b804a00505010700d40080c8800340c01c00490040041c01c0050066082e88101c0c881c07442e000d0910081100018408410302c81e16 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 915816232 1250 915814982 915814987
    0x816030903050a080a1b051806040b04030210050f0d0212060103090210031e14010510030606050a0c0f05010501030803011d1b0c0f030d0b01110d0206010911040308070b060a080f03 79
    0x125030840711310308002c00a2900544a140010051081a1150881c140b03959100c40d01e8420ba540c1e60b40d4031800740b104491261710240802c1c0700302c010031800c69007102d60441300103400e010310a505a83d030340103010003c1c0c1083d4000c603840c0e0300d520701034004007110741c800211450aa0782c1d8100540032164890b101a400806110707905520700d00982c0300c00654004102d094054080d814100000e0726031a8681a9011840320010051402c1c50008a034080321241003d0001b541003100013481805401c054030b003040307210f45084050003100d1248507c01030f040030082c4900e68480c20110a1980203101c0c0c47ca00302c0c02d00ca01c60990b070004941045c000d0704c0704005154580c41c0882c0c03052031070700540042d1216010300192201140d4003007005000f004038000000c034180394180c0c005884224a600c071881660410b43c0c00c0720703c1d41d40c040b500300d065a44c45c1900159042d40d52000d4032450040380c000a011748400070b482c2c1e061007034001d039040c42071a013140d400301003a03100c0d05580c4e26901406241d0550380d105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 915817482 1250 915816232 915816247
    0x5100f0c0b070c02130606020d020d05180d05100e0d09082d07030311120703020607081906030b1b090a060e03101b2a030c21081603090305 61
    0x2030035141d084511480c00f442d803101c8940014080030106000d08020a58520041048a4044c0007100c007400c9103002500111244032000342580c444e040308680f80d0640c58043c3c5195948000f0203141a5410030704031100003200c68030801c020180102040001c2c42100110304003188900320010541d140c0c01c015200c18201c59404941000000c5640041e028484030840180d110402c2418000c40c0070fa81c541d130400c002a400c1c2801d1003085151402d07040000c01c01d140120b07800003841604000d081c43c15503040e50f24400c2800c60558030810036081103051100010510090b07010302c0340241c98200c00d28020503160301c0e42c03082c81c0c85480607042d003022520718108081c500407141d028040700301405584810910700c26420031507151100c100700ca20303a4000395280ca43d51004001181742415190f074042a1400c0d20130345202460f20200030304008038050780750104401c201180c03080304100566031440401601d8060301d5030a0403187c49009180003407461079a1407180c015a60320a805495585c540841d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 915818732 1250 915817482 915817493
    0x32a050411090607020418121106060109170a06230a0603030e0d06020702090c0d15051c23030a110303060a06030e01140c090102010605010c050c0909070b031005100f0c 74
    0x4020000d82c1d0083d0b40300c1c02c2c038201941000c7c58100310342c8100c428107120350940310301804900d5031080304c07e425408801044460303608104c00400391b8244031003c0c800b4400c4003500070b107070070303200c3c40010103190400d010640c40015180701000e804040d4001c0d62055a03500b014801281c01e140720180008000018554070750410104110341d550141c04058500440c980100742e00310b070169203584140d800080ca1041c90030140c41002c0303001ca4000c0c003084603c0e20b4000010705580c40082d4581e1020340e407000c2c44081180a0004282600b2820707080154606010a103603286d410207070300c0d100803d0b02703d400c02281c500c01000320382c494100200413040103418220110014060704000103c0e42d0340c4c911092070101256064075200b00300c50038405a40d200b0304030009094812952010b0305002c0a011b90000065020900c44110748081d42c100071965a140d01151400c603040d882103542d0742e0004240904d01c40c1c00b094080661f4426142c01d01d413549002d0703040f160201804002c80000c1d40e4a03048000091 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 915819982 1250 915818732 915818737
    0x50406020705150114010c0b04080c07091104092301051c0605130b061008011e0e040501050403230d0209032d060f0c190e031501050a08070308120a06032a0504110906 73
    0x70a07c0bc202c3e10556101c1229104075080c030704900307507003645c0454100500c82190003994400c88c460141c40942406400580c81c3e03059040c05036034410407210b840d0003070032000464207403903640e004001480310741005d454035041020342000070380340103001400094903401c103490116034402c0c0907542c01483da880d010b0140100c550159003140c0385003d0402c00580720300b5503084e041c011809880005128209440c028044200d210100305d85102e01c0c070740c104bc0020402d002c0c1d464100c0c02080150340c452081c1c00113410704084901c070710324102503030074030016602c80841c4854404150301c08035001c0e40c0b42c5101a102c00c100072251461206001c000c02c01140300354241042d0202c0440c182220344503c900d00107030800e020702509214468a0400400c103525160140e0402080304401809409081d9214a4010311441101d105490f0248001c40c08010459100b01c00454104014034280e102e020f05443e034040c074924041e810020a200302180510b41882018002d4208d00969450181c0e424113020030b54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 915821232 1250 915819982 915819997
    0x20105101a0d020a030b030f421009180c03020d0c0b0313110603010302030a240f0509150105130c0e03100e210409050406020705150114010c0b0408 65
    0x104014800b0740288036407400a80041c201c140c601048000d001e60501d89042c41c41c081100c65a40f001042c0d41600d20308a0520219800b09001c2e030001158008540d81c0aa00120344001442d00c072608000235010a80401070036030304c80036400d00807188078107001e4035041a211005090512805000c00043c030b40b0302d00115041e40f10300850b907062540d81000b61010340040302e0344a81d10040c481d66508210b840c100c540e40d502822130341c03181554110b401090782c60240700c0c4014820f00e001c0d0810b50014640426400b0110120300083c40405614041d150240000760361b608660f204012035080747e505098001c0317040e100b0140c0210103801c0403903520405880e561141b40c05002d56040703080560703141805581080d001c0c503000444d4030311601902c2c42c07030803042c0017108030300c1c00c03511000695480b42c0710110303000c81d0f000d89008202604d450900a000b40700e01440140b6610516034031089249200e1403c904880c440207006004103001e000660382401d0a9034004c00140d451000503000440481c05807800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 915822482 1250 915821232 915821279
    0x506031302010c0b07110c0102060108060105091008060106030b01030b040e15070c02090411120601140d1103100605040609060b030402241210470d050604060602010510 74
    0x6443c0c1c0f6440d903001e611000d03150500016040c01e100c200c120420004085000c00a100405180d8580030b511030700ca01060080500c5a00c07051f010031041d40b0160a40400351100ba026109503580d6840c1c040c008100298003e8042418a0345c0c03603200d80f4181c850404804409409070030607144001c2d90700c6440d50010020024070001020850258543d003011a1145118980c0c0c1c8521648031010000c000350070385900a0030fa8440c00041c0001b248010072041922025988162007180502e4003041c81c2502e01030741074040c1300d15500c00a1034242030300414206c500603141005050f480d041d0200948145000d007400880341040440c0040c01e21a5000074102c44a541c401e040000c002d5030410190f002c625a4070942d0344100c2441086510b0414241c001d001e486207003406003c0300c1d0a0159011082c4000300007400d480030340e810366103079021019042581c4552400b6a1288900d84040040a0070f541c2c85014616000010500d0f90051160501070300d181d5103120307100c0b0300c0c012141c0200c03a1070012040c030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 915823732 1250 915822482 915822497
    0x1410091203110c0603240d0b0a0c180501050f070503040504111209010b090109050714220e0601140307030207020303160605130b150f1e09010609050603130201 70
    0x88a40001004030a1039109588101400ca00c482d00685803c000e5081a0701c540780070420301451302c09903c041d24030303c4421740003c0c001e002c0650016004c010700740f501078582084101000207102c40f507485032440c00749a03100e1200f0380c4100111889468090302425011030801c10000081b80c00400103011228429011280350988900208050342d1602d240b000f40c6840100b10500c40c0c400700d160443e405403420b070007013000205500004014107018840d0041456484000c030341d08501c0b40c1d04088080b801e040c0120303035846200c0080e918148041c5000c1c6642c045a1002050200d2080318441c0101f2050b56203915010304144008004d62029060700c051581c01c121035401130314103001030440a180c500305010100078900742842039070030003021602034102c01102c3c90001002c01c119250040c29200000141814a0011511001c0c0c0051010f5007d0391001491071420201800304544580560741110142d0340da14081e5031000c1a07000d665403050b018000038000d000408044014240140b400c2c59 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 915824982 1250 915823732 915823739
    0x102090402121e060604060f0c02040905100c11031902160e0a0e1f0b040605031f06050a241205190c1b120507020a080609100204141009 60
    0xa040381e10029040d1440c1600c42c04020540c611409026103581d066078045000740b401c1c10000342d251065000d9501404800290360241c644249812425180c0c080c004000326006802d22555403540d02d001c10002c10308101544060501c103d10040380074036482c00860134580c80c0309009140070f0305110b14208501c140b0107921529801d90540d080100302c401c0c86149181441044541031f00c17030f2040048020f030700c0643d0110450210910b040c2c200c0720620030024458036101c0025016081c50b6008030f51601c1401528400b0000b0303601442103076503280ea0204000e96850060040003502ca110300c51109041d807024551b441c0158030810400f100310b1401d100500d2040c101001146c00994600710081e031112100340e9100c109104484445030306062141e0903502d8142e400d00c2c0000d01c000c008004070500c0081055103401281034920959000701030f01301c410303141c81245030744d10b8044038980a18419070702200c60301d6801c2e100700c1d0150358121000541c0191100c09200041207100055801c02c210120000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 915826232 1250 915824982 915824989
    0xa200a031509050d050a030c050304080a0c050c03010204030308180106030f0b04031701061e05040b04051201060504110d15180b011223010905010806131a100e0907032003010209 78
    0xc815013010b41c1c032580d40758545000010110703051101d044091184c10011310003c69210301c1501c240942074902080c5005071407910600700601502520b803d90300201d0701004041e00000120701c0b9019400c404a400225480b10300c0c20386203180300203480e0380d00c1340c880300000c00c41900d8002e42c454048e040030354903142c0380044003203011000d900102c0060b0181661415100103e07503140751000051801600b4641481d40c8035010b8800c0d8402e09104140d0410040c1700c1d81029000b200091030300a10800000d18801501a50790340f0200c10720841c05e24181f40c2000072101d9980b44000d40d01e9101810a101071000700140040205000d468140005402200d00805440c0294150205a0700890ba0b00c154003801d0300c604281706805c00480c240c20140103116481000403800d9204242c0c0c40101c4803482c803810720707908030381b40c1c00c010800700e590b04001c000c2108030880e0070f0400c49208544551055541c500e001340c8038442030100810300c0d0031540c80c0c840c4000314070104030350b801e500500046c40d010014002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 915827338 1106 915826232 915826243
    0x30610051b06181507050d1a192c0f06010e0a06090602010f1a1c06020f07030806030102091008191b020c010f0e04020a090e04050a200a03150905 64
    0x3400c501c2540c0781e00d0540d02303c3c054024482642c640c02d07810545030007400340c1e035440d40c00524680c4030982410003c0e00180c03a5070f107403251207407504a500c001d600340140210b0b040000c0604540b03044d1765010003110051449032515882203181140180c00c2d174010a1602c2d07041c030320b4030744142c420090082d02c100302c40c03c0441d40c0c00301484076205602c050240040c009030900348086080c1040049250081203442d02a8841050568a200c2014240e00c43d0444040d08035000c00c0203e8010b900444c001900103042e1035580500c52280b100322000c0358508005654124604d601e104444ca8060140072144282813a1840440700711450103042c1d00c104203659405190b0010303062424074810f01040f809021010302a407418145070030015510300e1100780907109a0745241c86651140041045c00b00b107042c0c06842450305a29584401c1c2c40300608a0340b00c50a55204d14180c8001030080c0407 = true := by decide +kernel

theorem cover : BRFrame.Cov 915647482 915827338 := by
  have h0 := BRFrame.cov_init 915647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 915647482 ≤ n) (h2 : n < 915827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
