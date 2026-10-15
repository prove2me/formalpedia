-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4710
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:29:34.953974+00:00
-- url     : https://prove2.me/submissions/8225d10a-e6ee-4009-b04c-31f652f951a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 846942446 ≤ n < 847122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 846943696 1250 846942446 846942487
    0xc0a0312060302090c0a12090c0605090102120408030a081602071a040905280c050412150c0906120c1b0f060e0c0f0414040209180a05030d0b010e150a0203 68
    0x19001b0f1b528102440d02401c0d003103041d4400300000341000c41c84030116145a4803402140d2a604109544010000040b820107003100004e03c5a902d0228000c10907400000c040c0c4a00035054407032a40d151184a10601c00041c018454001039100b910248035080c5c681c041401940070f0400c1840c20551141040d0702510000c40b105141204180703141c00c4846a0140300d010203a908040402045640c400024400e104900451414126240b160400c000c0086010a2184680c0030104840c01c9030841c0104000041e00c201c038005070000601e03840090661140c0040358541d81c4620b800355040124182c1424080d0074155416001004040f0201d80b040c02400c4801e000000945031042c1035904114808002c560164065482c20a5841c00c024079030541c25000fa804552100d03d590b00c0d034440501d0400001c0b2480c045000c2c0041c9541044000005050f5903480160280172102580c0011151100c154014a60140910480404090007400204112103452050360b181c28018043d0102e9500e05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 846944946 1250 846943696 846943711
    0x112080714030721050705060c2521081003020409020f030d092607050f0f100e130902010f0e1212120c0f04090b0f0901060809060c0c0a031206030209 66
    0x120b10007044d05802c4803c07102d0394040c080c1829420241d10380c80700ba0791160f001b408030418a60000700701103c01039101802ca18103029054040e081d02c42450306021100b14602542c0804040010b40200380f070181c0f000ca403042c004140300b044464034580801020741980c3c00d043c0d0308065441c07050300e107503181070050540000f400c0d190a0000303458202102d501c41c2c85251558a200e0050712f0005850074041441e8044660803181c0c50103030358040d80064400d210f116161684501c61402001e41030380c2020940301485c0e401c8a00303562015a4600d00b80584a070400000c3c005a00100c0c00d4084500481005000400160240c100360721071200031444d00c850781d211208a000003154000e41881100b040d130b43e1040d21101503508020003420140554011030181c82d4405403190380d44003958071200240561020001d009003e1035a4420011b03002c0442591124140c2c081e0b003000030542018102180ca11b01e111380000c0c410580c0c6034900f1500042600e1027010947e8031400300001682e40c900780b882c00f50b0310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 846946196 1250 846944946 846944963
    0x10c0c090e0c03010c2304050a031b0b04031101050a0e04050c1213020d02120109050328081005010c060608010203040506181204090903020c0a08010b0a06030501120807140307 77
    0x1000e5618038018030082c10314032a0381072100400840707030301104250000000d20f0004120000c12581c00c465402180c002d01e40180402da03001061000f107081c086a02488003115036042520f41204a40c80d214600002c2e1100c440700400350314a502c200c0080800f1002d914010720201d900b013001509585068542d5100801d000c128a900a440da100554000000000c60320071480036a01260303210119220292040d107a030760b101031003604203412044210780d0010580e035444d204695664118880f0317822270030304a5001400204410301030040303503004002002d500c0c130180b4608801100e40c5800c4000490b416600c0750320001d48900c09002a41c012071181c0041c06082c40d20820155003608107500760141d5a10003042d40090030302d00400c5500383c50010348085892007031802c1c00c0c1d127044048001240c00003080580010b000b90194070403030700001c007168122803055441900301c06960080c0100d012121074181076100080c1782900902e0554860200c064000d03807e0740341c09085400c56a4181c1c1c4800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 846947446 1250 846946196 846946211
    0x507090507020d031a040506030a211e0806060f07050102040f031103070605030c0d06050d0f06050a0c05090d110904150615021509011b02030c0c01080415020702010c0c09 75
    0x2a0140a03d0744030100500e010000b442500c0e903568400c07101034541c2c600865503040400c0c0c840c0c600748201080c06401250a042d07500440600e004161600210300b070000302d084065183c06001c1030740c00c40752003a8a650f03802c903c2e21b030705040261540c80701c0c03003041c000b000c01c1000300c00050080c00544010720110500d0b04031180b0310305050480c052403414840c4641c0002d8400d00a2039000410350b80c016107455881512203d803030080302c004020582000d07078070010903044d500c01c000c1d42c2c030311018413603110b008e0500081d19449120815500d10740c0141c4045001031006256600b00001c003003c8460150308044010000e00340801c981d16001d580540701203c0c100740712140d003041c1c1c0c000d4000401c0209010503500814104c02503c074801d00c1c940e401c1c041045000719005003400d40213080b8030001071400508071400044041c0da43c0d80003190400e132500a060f0092503a601640303600d845507400c0450003200900f1452148002d500c40714080341030014240308040030078403130588200a0001003070f0001c0ca04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 846948696 1250 846947446 846947461
    0x60803040e07110304120c170d320309010603060606080405010b012105250507020109080a030816030f090f050c030c130902121b0907050c030f1605070905 68
    0x3401040182440000c8603e5010403000004603811506980c0c0e00e030324102c4451900080c0900e0b15807295144042d4030711244841400400c080222140da502c88a0781103d00d41c001c4019890144000081c1c0f09928241d1032074084141d0055900c0341c104000081c0280d2a0b56614003120900d41000001808c01e030f040008100c8244907202c0503010900304110000d103002411211649501051500740e525480811800d005018882880000c1d1200c1280c1214180070010080d801814080c0d00144126100264610011604242039a0075a071180800e0751800c490020400400c140c1c02d04160390f035610000c000d0340070711944840300c1c031416202c2c0c1c0040050a00314a81500403030304500c240c1003401240c00a43d61488000700c0c800040e030020030b404400c3d00015180d01c024400c04000b9000b1901100890007070302c010296054022030f2010341d50b40b00d240341110540502c5040c0070381c41d40100400003105503640042d0400c001130741c0d185a10724929a48160900101c0d130b1001c412181c469080c001c05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 846949946 1250 846948696 846948719
    0x80c010c030c06061d010b03040c0506090f10032301030503121e1614030f1f0302040216060e03030c03060d140f010c140a0c02120c090c090102010b0607020310050702070906080304 79
    0x105107c0310700e0360460415481c4c415a180840c452030340b04000019500815032140c00c92101c044000070004180e800b60051b024000d040000340d80800e0500a921203145405040354041c180c2ea00720b0021410706050a10303074200584040c0001c0c0b45c001c583c24105030070301541c0700c00500c80c0f1410840e6084007161058060040848030b00c202400355021701c2001514001004401e0b442802c01007480380400d0340b14407111010345e5030f80001e5002400058480d001c1400000d100c19518411003080114011008070f0366241c0c0400ea98503280d054040010501c1854040e0f80011054000c035450020300d031107014000c1c80c1c00c0150240c0c24a0340d448454204581d500098040011699805054a0240c0600c00208010840d2000a00c26201092003502c0444100110b252000008e03022000780e051080c11307034106800c00000e903030044d800d14040d0720250401c8000d954056030301800810310300e0100801400500002003c100851040d2100051004400e016460040855102440e0703a941000c099090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 846951196 1250 846949946 846949949
    0x10b090601030219080709170705100c030f111006030f02040c1d042304030203070b060d0f0f110306102102090f090f0714100801080c010c030c06061d01 67
    0x500d40f040c030561070703040211059140703054200d2805c0d05842e5110203096448080139048000c1e41e1700541c40d41140000b00082500548100f26810084c041002c40211040450000300400296128884030a054000d901407008034241c041626108090400c00c1ca044400b558025100040c0c1009083c0640c20503220315040002c184c606010758400c84448424204d14010549005c0d44c2da8510301c20704841c1d03460380c2812a00909000c2c01c150306240c03d000303541e900844030079100d403c051404a40e8614080e8400f9402d20340c0020482640c14041c0c441000c441001c5905480a1150103d8a58150740a000d1103111311b28522042450078100403a00744507240001611403141d029129031005030341c070070703516070b6001540c02860010b0350786030f101481c00d0412030b0000c0191403003801da0200d00c1c51001c0458000b81041640e010b08041440002201d1204080c4900410364001e4101300059502c03e81c40741020324040d003044980007141d0342e581011241075034030085000241d00352804400980803107150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 846952446 1250 846951196 846951199
    0x1305130b0306060f0d020a06050c060109050105011e17040b1b090d11031903080103060e0a0f1101030228270608041103030d050613151503021b010b0906 67
    0x2040c0d810314000710b40c2c1c0740000303001180301d8803003c2a0b95040b680e59031980c2c81e107140e000e480300381c1c407564481014080790404080c2201601840e80041071903130b594418641240d0341691242c0000d03014000c0c0004100ca62070700c10b0104240020382c6401d250010202c54010b52041d019141e0901d44035a440c0b50343c054400740c1c501c0d002c82c1007058859594980140b2942142c1180d020501800c0304030029140030b50713640307603140d8a2074402001c03c01c0c190001580c0d4100c901880301805946a6805110703152514000000d042440c4405040c011501c00c02607074a0380e201c1030500511b0892048031001c520409004007030a4021000d42c4103c860342e00070712840b468001c0101011100d0b04100013a484082d903030140c0320400c402500000c040c088a5031118500020180941c0e5071a204130b400352002e44022039026005e0803103400328401c0c07045a0700c2031114107150303001a40783c5a824580c03405654040541c4c040c003016024070a080805040c198280a00546400002540c440d20310501607176800041489 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 846953696 1250 846952446 846952451
    0xd06080f060a1a0f0603130506090604020405060f091303031e0603120f081305070b030c031015050a030510090e0303073903021e0f0705040e070e04030203040902130513 74
    0x104841e210301071a1200c04c10201e805603202d9030303600303610107403142151030181c0203101d90070600580701d50110390180254000d9078103205541d605428011ba4102c00c14511f90404010400160441c5501c2c090340b1140e4440d240100e146400c01c0341c0219201c4038103069407907041d901e550410801803080340002145415062072940409860360290030f842005005411494201c0ba400307082242c107002c200003a2600e900c00a032a1b044c9100b158081d0b41084603068503502c2c03002000304820310031000b0400300d03214070b680d05031909500220440c09864090442c001c11030980707001190b014001d00403481007942c54002141c0b030746400311008085004550300465031059104a070312580030316000186200b00350829070a0300010700d16080b442c041920300c6e0040049100d9091103070725000814084250125002140c0b41e00c0c0c0c90740100300454044c0903003007009a01614040007a889501603060303000d806401501e0809540c0c146c2c2400341e034000e411905a20318405000c0c0841d01c1c0a414a41c482440d00004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 846954946 1250 846953696 846953741
    0xe01060825050a2c13020708130512011b030c020a0209040b0735040f0b0109020301060f110d1b0828020c09040206030a2301031a0702060c0d06080f060a 67
    0xb01135084460900500030320000d540d00700071340c3d41c030340481d203403503501c00011541e41480e505440d00321750035030040a02c151400c2c04040070115050140002c52030302c00908a4140340b403420180c3c0100f500a002c801903015000007000980e0700c0c40c60b1544182c0c040c0095070b10318030744000000c00107084a5034261402580850701044180743c071818a103044040c0611800c2c80c1c40c3c44c1024540c9030611540180007517000b100120750080c603500694121813040d1280181600200402e40304071040320341c0030105500454a08080074030a8150307060f054201040060582480e84071021113522800090014121508207800012480700000d0710b004c880388040c200060300840003a40d10100540040c0c800c43c804401706502c6143c550142d4120701c2070650381a0f150181c0308421a20070024442035444a84604072450f040f4048025203100d14500d03409080c06907166500c14107260004114230010599074100441e445804004031144240000010710081c44d00034000d00a9035410550000d210004030007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 846956196 1250 846954946 846955007
    0x90f030803010320270903120606180607050f1c0c03140f1b0607031506080a0f050f15031b12030903061e01050a0e01060825050a 57
    0x703490540784d000d51441c240c030072018820041040752100d0303654000a1032140210154413441c00545c22038060055501c1c0340c0e120310b420f984900070740340258030501c000030000780c0c586000b034000c0108030307401c1e103412070244080008074000f50011601191643d02c400c00c80c2900080c02c0018100346c50400c94200200d01c12004014107000400d0001418041624620300d185180102920300c0740190590b00741e29048034100e42900320484050446e054020580491605880b900891f0171200070964140c100e0ba24128045030f0440b001443d00e03100039a81d4080e588140421302440380200100305c403503105070411200c5606060080d071030302d52003607110050386000902201181c80755200c04590590002c1940088c86040d032158040701a45400b4000400c6100300700702541c2000003d100030322401c6a0703220028049088403602840d8900e81c1c0311401001100d204940850380802031040c52404902002041460b040005200d8004034002040c21a41641e0196004907505415520842d001c01c0d0101e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 846957446 1250 846956196 846956213
    0x21061e0513020f09060a05030d052502010509061e270102012901111203010819081c1803020c1203071e020d05070905070905030d020c0f030f030f0a090f03 68
    0x2c1040d0080c461440003603400c1c0d8079014054001c3c4005230503502c1040c14081c00a01c2a881001c04a09000512100300c00c1ca0154000e008281581070711181c1c81c0c00c003003c08002654000003103103000c040702c101500f242c3c412072501501d180304c800040701c40d50004808203002640740042405045a24104105000e003c1800030807800300c0250f29082c003c043d9510040b185500003600d80a100d20400c0c1c038a01c0e0241d04040194120394040007918047e9004d15205d401f00034480b035015083e540c05024000d245042c941c400036200550050000e03403043da03054030801c0c6045a81040e0051781224040800900b450205a9905006000603500d464241c0d41c403d041d55004441080b1000f48134280384007151610310b078105403a0f801c241203551480d611071580c0050201100d240e800107211410000f01c0e0f007800208600c0307407280354005e880032940c204184a0401c0b4040c1c00f81e54180325030204001894018002841c0411f004841c0903501c4880c5100a0f05100d003540c025150010345820800202d01c219 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 846958696 1250 846957446 846957469
    0x2040603021809041a061c0f06060b04060c060f0612031116081e160e04050d030e1005040602160b040204051b0712022a120d0921061e051302 62
    0x800903030300c5c1e80c8951001c2403200e0752600c41d1080f0481c060031200148401d0300d450058240c451a8103012150715100d10b4103842c09540300d0b000204104150380400691309411207008180c4213400090301d1742d40c403600b0100d007043d610404c1e40800c480102d0b5a01500c0c05210310b44c1c240c1d521350040c40c0c5d40d80ca4444025030fa01036944030304400003080c3c040140341c40c0d01400400c910604c00080030b08041c0c0c40d0381c078511409400703440481c0d443c460800c116499501034064078181d0726064001e132510b441c50506050240c00018403c946080d0b00b00b00d042580192101d85c00036490003000c3c802b07a980380a00c18003044a0b0003070412001d80035804000c00c92150b00c0e908481d900f43d4440200070340c0c030300d88100c01da00e000d488070804030080d44051012a4808080c00ca008403c1604445041a03031349020a520b1315140ca0441034400550309400900203145c2c0003110342261012040d01b80142141600c03540304583e44d1a000020040160752000001c007401e0203107640100d80381c04032604440d15540040d12038041c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 846959946 1250 846958696 846958733
    0xb0d0b0c1b0c030a03126f26241909020603130320190203070e0906060109141309050f15060109080a02030309150d0204060302180904 59
    0x4101c14120311549508561910382c03001c1907040e40c1c1c14105100c2440b26840c100d00000307001d19941d040d0b504107819800c540c6800400d440341c5205030164282482c5054900d4809002000079080002d1240480490381501018440e400c004405801000c0d07820300e220360200209e25448005008a548901d100740c5400c101c40c0c451291840c800c4900701d03005043e208402030345c486804001c005040f02800314903036100307100741c2c0e448012007003200d030100c0002c080d80f110700040e40c004203203450600600000c8003c0503000138115403d0995543c060f160313020080320a16001c0e000031060011550b002030080d0003800070040841d148074103175000700b1014034112820304c0b44039480d401d119040c4201448664039918424003602c1414000941c4c91800e543c00341e9090303000a1031804000b601d54004200100301070750040149d8608800342040104201c0501c0c6600c45205040000088004040c0b00034002004181c60141e119402d00c01c82841414258a50394011f0115004201c005030f40c04005241544a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 846961196 1250 846959946 846959957
    0x10060e2d0a090c0e0a1706160309060203040c060f1706010503060109080a0b0423030708070206210109060603050601021c14120406050106050f0d0b0d0b0c1b0c030a03 73
    0x20500c00258406025901c80340d1094a0040c8000e0442d62041c400400c92000fa600c80040700e03a41d461311501000500c0e01000d0a4124402065004402c43c2e42d4811118483c50041001c0e00141c540b102240d000380c40c00c84800107940300030410303113421444510803a800d90800d43c3c0c0d82e030128a8281e40562006100e141001400000902180c0c025000480a02410822076a85c1e0469180404100310162801d41e51001d40d4008109150104000036420607000c802440c00c2c80301e03994404140303800100040341d100704144196101d03280407050700301201e000e54407010010b514040d40c0710111340c0150040006c0604001c10014666000181d071169990381c0d10105041107038540040b10100114680281d91b240d00249051502d020020182d0089000300d108010b180d903501015110b0303108540042484d00010f0008000420301d5912210070860060420107100e8002d43c6c0d440c424480813581032002030004110b41240008013030191070140b096030000c080d0340c01d2200c0002c1e070b10440f001c0c0083c100318 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 846962446 1250 846961196 846961279
    0x6110f0d0908120103150b1219151b030b030a020f010c03031b0e1305040317090a0209042301060b0919120609051b0a03020f061210060e 60
    0x551000c43d01103949000e454041e0b540c4a1401c401a801240340b00ca8078242842e417410342900c1c2c50403d00c103030b82520300000c3c080b80100707900003100c1e00b0001c1c205139084002424850301c220428041c14114a03d00301400101e280342d160301038215a220341d81d45000c1c0d408500444016100d0340c017020b071494024200024108502d1908401401c030040ca80d95000302d200b01090610f54010f0b48020b44800210f1b80c0300407440300d05052008840d4100d8001e40024041520151210840d9007106e4202c815503003501e01e554410b40110b84901001c0d1000c031150208420444009001c98207144c0300103550200a1000030b01d4a1440d4110317019400303490f4800c1c0340f0701c00d20252450700600b1030002012040501c0c03058507003c1c01d00d800148003005099415000b6216280ca00c000c40700b10180f4503d20080588508500715028840703a00107440100d03400074010000c8200701d001503402144614885410704045a082c820f0081a003092103842e94003d90100d03046142480072488081c0c168240d64910410b00c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 846963696 1250 846962446 846962453
    0x30712140703020f160b0105100201020705210d05010f030b0a0e0706031508011b0f0801231203030a06031205041211040605060714011413060c0e0a1206110f0d09 71
    0x61061107208041c0c000904454000c102240041b1412504219000000000c01e0341e4180c3c00e03446240f00080c52900b101e039440c1b00300800c490070210030003030701580e140c10708200b00c00a808594080e0058a05501000c00400030052108401544049103100c18003c4c020581d440641e42d002d40c1c02810240b40e210260a0078599101d030000c001010090000d0211804a03448211441c42504603907000480c10408a62044d0181ca035142c1250b14001017504840e40c5001d030030b44210708281005503c02d21000c84040300c080d04001441c001c0070b60305400504a40345140015100441ca8020418003100b880204900c22100e568480a0303078010300d040402b200d09500041c001e00d6141c02484d4007600c0407072050140070070050743c460403c1c4480000c101901c01d4a00c20040e6980032244002d65449100801d000034242da00071503002c2445041241904240704005010120241c01904964000c090300c0000c1c441c0a0003043d1400c0c8039010b00341d01d040300c60302403400c10f84a020300c5c44d040d003605e54a015080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 846964946 1250 846963696 846963727
    0x50f0901030b121b030c010309021011070f0621180209090f0708060709060c0c0501050d0605030102030a0c0201060923180115030203210a030e01150b03071214070302 73
    0x4010003d0a40706404009074140000c400d15280e01030080c40340c40c0e0300e140343e9400b81c4243e14940f81c004101044440e9240812182400030f80f0040f1141e006003600041c04042810800300500b54540f21141a24080f90031a05044648400c0c2e290310b5083c804102210300d280c5c0c02540c0c48680580b010f82007952208101880d00c1520340c1080f2081c402c02c030002428520108480d809415207546561145542d000700b218a05000d110103440301151150030082c030f41c02000100700b8400000801714030300d80d40320b0000b402c98204598020545803038804d0001240d0b4284503880280410007810001c0100c407110606420f01c0000c1003900c0c10301d0180c0403507031132441044070744103950b00c200083c441e503000ca002c4101d00c0042488200c0c000d20071030120202d03940c08000004801c03540d0b03a00050802100f030750120003404040d00c000c0ea55560300c44440c03422407d4142124050404d45203c903599081c2110001d0003d56100c000380c500301e02d41020b6800c03a4074010f80003508104d9510f409a224211103016501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 846966196 1250 846964946 846964969
    0x6010c0b2205030a0507020a090c0518040f0504050f1e0c0d26090906040c0e01030c0e120706141c020304020a05040510031214030105041a0901090b040b01050f0901030b 74
    0x11444085032041e03082e031780840113000307440c408d407880d0007116903492140782a10008003811000c54003c0c40650512500350392880750154000f070002c180c1e42064a811411a041968141c0d4690001d4800400e0010700700200c145001a041aa15400180100f0241c50706c01070303044a88540040000d00d82070000d10b6150448045a844d01c0c044001810003e00f555a8050030910f401000300303400040c42440d04d882000038070007454640750fa07900c1a0400440003080c12070a600c05220000707000c540d107a11500c01c000b0001d4000001028244d08015018040401600d40003048140c1080a80701c900d142081c0b804010050070400768072900c60340700040e010541608055040b626090030040b030914542c08010031603004800401d08004825411181c000340d420400c1078a6004000410180c11b040d80300311a00c51106401c1c101504804001512151080c1e0202442540b11240500b0501e00740c03040c0d403403044003424a01d1405240500c001e000e40120201541030683c0c0d840c0b0b00300070f030320b8219540790b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 846967446 1250 846966196 846966203
    0xc020123040b1605010c0e0f12010f090807061505060d0903050436111602040e120703080c13060305072703060506040b030a0f05030702030604030903050606010c0b22 73
    0x60303d44a80344882107010f0070088050322250308180712280ca00340142d48200c04490080d1034042401e8029090001c0302007075503965061907503101c007001c0900500d442003401c0305104080300c0b59101d13414240a0140e9905140d01d0180c5242e011007080b00da502c00f4100c61500d8442c01c070124050106084c00d0b81e2070300441d403002078003070316481c0280b412803081c3c4030400310b00e075040142040c1118604c006900b140c019803010051789800b04078860145000d15929036403a40300500c0441d1030660f403424913040480702c0c444845c80041c0841c803641007582040315650300c0965110300b0790070401e41d61032803142420340d48038070400c0c56611400f0076580c0c0c1c40340f204072880c456071810f40034084140b2006610350710980d200540340301d480c0c540400c03920301d0540909254184010020503210b101e5490f00081d9006036081156148405c1150b0310068600b8082c81d40306030300948450300c1c000e10714280a41080002000307241005541d800304030008002c0350806400c001c0003502c44421400018121710404e880b04c0019 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 846968696 1250 846967446 846967469
    0x405010f060605030103050115080318120a06060e07021b0d030309171806030103261b030901030501090e07030318050d0b070905030a05030306090c040302120601090c0c02012304 78
    0x820840c3d080f0004504891182c8000c0089000766006002d2148036800385140b180c04c01c11110403040035030000c800a100300201907440d0381da010f0700c18520705000401e04640d581e440e00e00802400d849401c0341d681c400c0383c2e4009011000e445c0c40841d008032000404075841503400c20941000e1510039402503801e194050701300c4a0061410303031362810350780000d428910250b40002900340c0504041d000d490489a000080c00b00300c0c1c1001c0b00c09140340e8212000c1456001d02400800804080c0d034844aa6480300c2e00c001d140c2c0c2d60181d07070004040da03205030408680c3c14240180c0c500c1c10030740007842c44103c81c0c03d450400c1e20700762303010000301a5090700d50056501003200c440c4141449103101c441c5008410300d440e070f1a102d507a50f80134903403a03c014950180458105000280c024200300c03801300d40c0001024855881c203512a4000303100460002c2100385564011001888009018807402904507143d00305005c90103250f5000070310f520030b01c440c000c00b055207031040b0410841e41b940030388000e045c050691 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 846969946 1250 846968696 846968699
    0x1209080a0e030601080d1e030e07030804081614040519020a020f0f0604150c021c0c0506010b03150d050c060a081005090f06060304050a02091306050a060e0f0405010f06 74
    0x414441540140300d129003c0c260000803072800000300034001c1841c82e1100c0310344003960003001d5a60040d0350a04424180c842c00d803041c0e118020b00020b009103102e64030580d200c0b4240781286203000d0780d50171810007007034248030705108405050120b4010080704407804030701d40da58140c0c1d05032002005400c07041000e00114074901000e4000c0f480030003ca903420100c540d4078962050190f507514086d41e01400000607003080d0703e4007201c1c0e034204a5210340d41c0c0c012202c0b0140015810440c903442617003060001083ca906400411406100c014014801407601a0541c103011600007000130300f5040d000c0c03152060108a0003040420f10902410840041090703844080d00e0b100940f00c1d140481c0c2503040f6001d004000b08152400418090103040200c08416150380c0e29024404194800341c41580c2e144984008030006030303580010140b14400c081c081000c1110300d0319002080c0d84000e0100b04205007410707818007801500760f00541d0b0183d40300d100419a5255030074224010440139042842c0d05080240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 846971196 1250 846969946 846969967
    0x518060a0e090a1a090f190b09070f020c090412110c060f040608011e060e2404180b0306040611070803040507030b18061602070905091b09090a03120908 67
    0x10303407000200c50130541c88a8107524104602a03000325040c1e0b085090302000b160050401000840300405541000240c03594400001954410f044030060001842202041425503040c011090f50003015240001241050360341c007221071440004600402c0080c04180205100030001288080c0d00600043d40e9454008489542a4080d000c3d04020545070000000c4081d012401810f82024902d15101031604245044401c514401c0c5450743c48080c003500c0d4031141d1001035201c01034801007028996150320f081007038000e031903280a0303d40700300740703000f400082c16200030801580c4560700c4400050082c0c0c0544450900b4001c4090117049007001208200030010009580c0c1c0581b40a8a182c0c0034660301c4003211091002d80000865140e002400440c8045106648031104110940160740000b51251151070807200119030340021075128075541c42002c401c441031500e03038060070355000e003840c500042c0503a034039190f113240202000310443da04150b07180fa9078809190b02c0d41c42400b640e522000b002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 846972446 1250 846971196 846971201
    0x92e0f06080c0117060609040204031a0a0501060906120216080c030c10110702010e0f040c0305040b06040e0d0507060603080703030c090f150e0409020405180d0518060a0e090a 77
    0x164445520540b55048029030241030405041034591001d22582c1c0d5a032020311400e0740049655a410039000e1101200140056400c04d00b20100040030311220318201680700d00341c91069000d6001e00001400a00009500441c4a20101e070100c03070141e500e030b0b04102443c039200d5031040c01901000d0041146011a0408001041319260030401c03690000360300300c030785c0e0b0485440020003801d1400c00c110140041d40101020b06130804028030030303000907002502003030a680385601d003800000c2e43d840c2004104254140710a030041015030381040b100c409014059921407142c1000760a10802090780002c01c0764940014015640c84080503407a1800c914029000c0d0030580c4c1c40c1c40104104000100354080048034120441d1600109222014415202901d950040080c01d40d003054483e000300c009030f26070f07025080c0159501c0100d05120790f11022941d040c0f038000c84410782040801c019000c00d14500e90003001c520750007202d50f1a982d42e40c4c41c1003075840b00c5280c034840350081c1162013042584003096 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 846973696 1250 846972446 846972449
    0x19080a0507030524032806060b0f0d0b0406031b0503010e030c0601030b540c0d0305130605190f0206070503060d120e0406090b130e03040321030f05092e0f06 69
    0x1560702340310050720754003540d045002c1c0701501c0304113550901141c2c200301c4450700151620100940f00280c1e40f6102e88402030040c00c1204681c0c01c00300315100404c6641030900c120312040c80d248024509107070113210800e0b112007061101510904441c00450302d00c0921032148610303007040d6010224007946007204020aa40e08611170381e46800f80140350001410442c1d03000030403048080103080344404c4401001009108901c05070100074007405048030b0001082c0184024080d240c44441c0c03910b840344844010304140c84190402c000c1081c42c0d80384207980000d1019005040da003040b644a585840c040752546101c1d90020707200418901002c400f0035003086040c140301105031030a12450740c0318034800050b95000048180c221000108100c402c410a62004041c000e01d441900d1038035a0340d4486010034000402196240381d06400ca0405083e010310444132400601501072100f0303d060390030113485070011200d0321941c111140c0340386504c0c84081b80c851640f4901d042c0c02c03c141c0a6000355030000f003045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 846974946 1250 846973696 846973703
    0xd02060f06060a0c06200d020705070501050c190305090d1b091a0d031701080303070e0a140d020406050307080709060f051e010519080a05070305240328 67
    0x140c03400304110341010011200d40c40310540303c0c070024069654924004203201402072040b40d20001100780c102042000500c04400a65400768542c0380900304641400140e90001c0c2c10710100b0004405084000b15518900464900141701c5642d26414143c0f010b01c1803481d210343c03040b07240400204000454540860341291212400002c41c4c440503841c0031164850f21003e54000990b01503a4245004640e0307010315440f0f880c14008203021100d4000c041102038000c1140c0390400310420081c603501c003102511440d030131200185000e250401c0c0c4490b50540140f50b5005445030500e42003551529004400103040240c00c54010701d40c0d42203a10f854031068004c0910340f508005000869082c0d5a41c01419510000e0004c9a5000c2015074840550100316002d0b05000301030003104000f40c04442050aa88001e0700c038403030903203410020b0fa800c5400040c0f01c0d10600d46041c0611140c1275031448000c14070b50541441601144580c40024a8800c103070441c0b40c1c4440e10210580500f88242d030416104511 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 846976196 1250 846974946 846974971
    0x110321040b07030519230f071101060b0301052403011d090312270d0e01120c021209030703020303070f021f020d0c11210f070308030f090f0d0206 64
    0x703540b00e088060b42da013601d1040810504c0700c1e4900d03010756250305c500c41c404c168100181c10403884c03852800c0c0c0c004007204c114180c0710780c0b003040142c034a030082c583c00b083d40340c030360300030444241815405200350206010b11401040100050040f0180aa00315132800f00010003081d00c96a48402c00042c41909030b805184a05094011522003240041543da00b08840c04000007603a9030654001000d0011004100112607508200303407015800707008121b43c403501e40c0d554044542003e40094504e8141510030148036141c0454a5400b0b40e01085101040802d4611265110300c0e0000080c9070000300d1b00040e6150200248450410041d03000e070143d4180b003642c544503406003460414078040c0c10302c2e03400360258120403050184544114540020207218040c86c0f4142c5030b03070b40b010810b0a07001d8000e40031a88190024034035101010060000301c843c10708000c145032030455a60700c483e404090001c1c005030106001007900d03418240614081c0300500c0c41120295114a02e0081d5194000d9542032664403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 846977446 1250 846976196 846976201
    0xa06051506070218060303130602010c142802010603050304140a0815040803061c0308010f0b0405030a02060f041d0a05010e060d20060a021e07060c03110321040b 71
    0x80c04001d545002e0b070000c140c2070300700180c2004002034082c01031183d54140410090141115082841c1802800d240d900004280c405e100025009100410924a00344000e20815031100c03400415441903140021200c50820442c900503805800c4541009041c2c4c04045000310300c0e0030012070ba0940501007103400000259403250403546545120706404551210000007401050001006607007142c8003600440181604001a40190f422100c00310006070300e00b401084038481440c1028094005201280d00d00b610f400d001903a9490040700080c0940303000b1500f0349102041c801079400a1021100e5800d02041c0310301000396120048810301e0032a4035003030001c980501c01c03501c00b034400c44003d010060400c00319120710895001100c10015107424000c0c0d50307407290f01d5150150006501c00d400178020025084045500000b200104449642c0034880030400d080d070200d440011a90103041c00ea0404042444080c110710a050962107100070083d1100240c00c0380b41002441140111000005374 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 846978696 1250 846977446 846977449
    0x1e0207083103110f0618040b040c1b1a07050307110102040510180302040218090612030f070302100219032315040608060c130609080d0305090a050a060515 68
    0x544402a01e00d148980ca100c2840002e0003040181c1c440032004245400c0794001400080046e441070f0100e96010f41804031104060519014232001030004a42c244201011390034018440d04591001c1d116001c0081d03e00802d000000414542e4144a24209180c41c81d0001d0003408550007646d1500009001d01d2b6620891070061003542d080d590010a0200d03c203480120407a440018405030075031100c0c80440c0040180d071148000d264003180154013070150090f07041000340c850303001000710340640b009404c869041e11004c000c40700c1c40303001ca0660700d8960342d039414224604600311b428040010702c009103e0400d00a80051f140003400140e400344104c80c100100e075041d25007101c0103498403150348400b20340380d840c1d10400c420000c04c01400003d145640e90104e0b514150007a01c5003e14410001340006d811000e40c1c140a01501d01424086074262801910b02c0e40c650740f44034a4010140d4a4003c107004640c140b1007290000c0d0400304440c3d00600504003003004100680c2e04505001490b040141507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 846979946 1250 846978696 846978757
    0x806060a0b0301031e020301020d0f0b1203280915021c030e060106050c010b060d0207020306010812121e04060e060a090c0e06010c0c03210c0506040201031e020708 72
    0x1605d6101030441032012036801c1d407140310320013000300b203074155000e1000d4100d140c0c0a104000512111280104e254888c4405000440e9400d0403081c519070410003400805107031662502c0d00148180e8110301d803100d001b444c2290450f0b0305803c1001d6581d02c9100074205039500041e560701424820101109104105030700350102c9000c0135200c1c5440c2c0142c001000b40a0141c1c0103070203080500000072509010150000d15681c0c040300440d0001a170105d60241075080c1006000d0150048200420300464450100301c81c9010700c070300c0014881d01d2103001442d01d81a42c0554039006280e000450070a080038a03000c000b401c041d100303029440c81a0b0000031b80c444183c4c0254100b15800036960140a424032441143ca10360082131141448a507600c6000098440401c0ca80114059900107041c0c03065081c5c0c802e060201c1455290400654440c914007040010440d9900315a09003000076207040443e440d0441c0c82c1800341146a40c0d84080740d120144014503006040c0141680950341d41e0f090014440243c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 846981196 1250 846979946 846979949
    0x60b0904050a02090604021b030301080d090e04060203060a0504050a02220501090306050901020c240703021309020a0905040f0f1805070b0a11030d0f1d210d060806060a0b0301 77
    0xc1d41d800b600e118805810440c0405404c014003420240c940b001a20254218806a600c2040e00c1d61000004110300c0c0030a10001082050f01c1c130f04680f10600d04000690b0b52000940054035032035000000c0b40c81903590901c036000402026000340f060b8900686810f000b500989014200715002d0040900381c0900000444150390b0140c6611600a040d5210200100801048030310103650821900390300040c20401c841d2000c046001020304008441c0c51503000d0000602648141170046c40394081c0340003950000c4081e1002240010303100c00701c3c0300742240c4180340380d80b0081d089850700c00145182c1440e80c0009020a1280c042071010b0001c84504010b0001000c078090f240c0e404c10101070014405a00090204500514003500480351120801e030551b803014040c442840e030350708403030341e000402c3d8000c00510301c0300011009401d003009179a840e1610800b8417202050305200c2da050600c0c40e112016241e0030582071000300000707521001c02990398841528a14402c04a2030703c00034581caa070404a90 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 846982446 1250 846981196 846981203
    0xc0302041a01270305060108030c16080c0d15360803041b030c0e040303060816062f0a0614041101030513021305010e060105070209221a04060b0904 65
    0x2120354200340e80b441c624030607050552080f0791114000001050003003041178060100d481c051503484e00c00b80c0303840e4500800c0c142d00c940030316800c80d810049410086448801c0c0c41095072091100000361a01200c8004409200c6c5180391408205100c402d0201c454070314a20314440f45540001c03051042c19600340c03d460070003000c01c0ca0420000d8002510082c055000d001c00e0340401034240d4803580c81c0307000c85d000d5070410682e10f6290001c1005155050140c18002e01450010b41203031010b01524900030540790080c003081c031a202c42d10880ba940c4003180000000c1e8031f484042c40510b00200319a441d00c10646050b143e150420300368440442100b41420700aa600108074012140c00030015006440d0040600c032491104100c42c5025803030364803400d02050f901c00e000040e55818468408007804e4082d140382d04000003030001c0030060700e400f0102c0d81c00c4512490319104d5400380a0100d0380b108040900140001507000c400c243c4542c00600003809544111010310990340c50400f40180340c0c20031036018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 846983696 1250 846982446 846982457
    0x20d09060c1113020c0a12030501150e0918070f090c0f08011703041a0304020907210203150d0c0812070803060405090109140a0c080601151d0d0c0302041a01 69
    0x60341c807840c00eaa40903551410f079400160504060005141c14134070f0040007910740709005956a06007039418429923016111080d06000c5840c14180700400b02080c51400c0380c007030f0090401040c4e4800469001c9a043c0f07041c071080f603400316240c1442075451102c0d8031a40c030783c46050800c0048101e00034100850b0401d02a030702d800d800d0f803800c040e2902c0c40182c010340480d6070004000c0810407143c48400840c88210f41c40324242d03a0304007481405003120004140e1420460a50103070080780038a0b2491101039100c40801503105c0d2180f0b080d070540403280c000416801060510b100081242c5400d58004031150103040c1c0303403511521190a1080c0c0301c0c410380104183c604100040d281d20b803d910003a0000b008030000680003403141e80701c005081500c1d00142142d8403198135481001b100e0241d0002421310000940321a501d4034114002ca080c0c00a82c0b074090000541c215902d5441648599030031440041c80d1039507481306c509140000321914042a4060760031300e038900f00d0095140c044800c02e42010380d1203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 846984946 1250 846983696 846983723
    0x15210607050a030912081509071b14191a0411040e0102220f09021606050402060f0712080a090c030305030606070213021206120c0f011707020d09060c 66
    0x2101c1d40d030300070300c0c0c0e56051580d00c064000c08599162081030380c9080d1501c0300c40311801c1000308070300e484104030201481a8030700d004100a0070303445032000341024001d02412202e54140d04d412801d080f40301800345058031641403903e002100e04c50901c034840340111aa145502c11440440a642200f00e401902906c8140c0140307030b150a1075446030892844500c001400c240703075041a4004000c00c141b550048d00c010400511000c0c40460010f40148442c80045140c04010840c000a030100407201074910b9130303a07500140664803183e04440c02501705c01a0950f43c2c000906c6c1c000e21405104c0c070b8120004201d00009408411144a022072030344c1c0106a0b035201d945159022107840d480202501e4100c2c605000203401a100c110007200300e40c0d0003440c0540c4071741c035040404001050090046204070048415480c8401000c101d4034182c41c2c1c2501c00d01a101c1c0482d00580f51511308851b44242050248200480990f02066050b0401520740e202182c0c16500c80301143c2c80a284a000f4180d104c56000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 846986196 1250 846984946 846984961
    0x1203010608041505070201060806010f060c0f020607150c14041d090f07030f0620040e0703110a0e15030c0a031d01060602070e012106050717152106 65
    0x3030541d4040c1c03290041003001c1001c41c05803c16a40240e800e803000d44c0d1a440203000c094028808140034181118020301131078a0554028500740c0900300141203611101120000d5465040031282d42907003120b0450205859161048001c1020500020000e1259605040603031507100844080307800000448810104c101e1407180c0d1044040e011095a200e440000c3c085268288400d800850294102c0c51400c84a41004d5068421412129017001c5142c0c40b51301201d601c440a40b020f8491a001c515225a541c00d802d030000c0480d0303100c94050342d80210310030403a144d002a060b1056041502c0c082d00c803803518100e0101c580015150541104424041711408078480d600080300c030594150750001c0b00f14011080e5084802541007500143c0000b1810b1000041e1045101c0c010503074041b90028482c0150f001005a83c1c081c44010441138588010418591089501240c82c20030702046044508204030082d00050b00740442d6030041c02c2528051351046083c1924a10260055025146daa51001c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 846987446 1250 846986196 846986207
    0x40f030c170c101107171005100501090e0a020d0906021b16120f06060f2907080f0c0d0509010f020307020f09091e07031e020112110708070b061212030106 68
    0x641c2c11124800c403c070003c1c6041100308206e0100410310058020030521941c02c0c01501d4008007412409514072500308000d0360301850440c100d23a01010b1914031a140c0c04d500d400a40710784903440e0b038007506042c0b0f0b010030b000300365004146811508107000e041c40d001d00509900d131241030581031102c0c440902c00b0026a084510182c9100b8030071060f0b0034004400b0b665100444000e50004160402400406e0020610310f2211411101462800c1c40b41d020040c68210340910844c1402418480701048000704051003209642180c0601402e5403484994950004e0640c0c10105e1128002800e42200301310f094004021200d1041d0003038101044a015003003442900107011341100c42c544281e035140304440e0508000c600118040c03030702a0030810f2950503c00e00c18010303a044286202001400580180e80000702035070941009003022540c4007804030700f1041402085000307483e2000004258041003c20910b05102c4c1c0403c69940e584404083e410035030781d00c1507071005e050f20442000140041c90003075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 846988696 1250 846987446 846987467
    0x925060f2d030216081305030f10020901090302061c05011d221506030b0606032202010504122406061b1b2403270206040f030c170c10 59
    0x141009864000c000c141303521016402081514841400700c1c0150182c0001000743d402450110010700c0d0840121b5000b9460307100c24220b5583c40c0d640042c5504590f40502c641d03400031138005003059120b0f1540403c900906051045ca1500720389030500100f02e4083d941503c0031001409503c401007591960020700c40c81c00400c076070340b0120203d0f40641e00001c1d040c0a03854031b513007001580442d1242c518600242c0c406006400e01c1c0c498803043c002c00c04144d0001296290300c00f00580100c002c20014001a83c1910542d002000d000640703869103410b01800c848003683c040034032040c03000030699044103101207513054090140040c1c3e42d44c038030240c54500a880d0360300c60b601802040300202e01405e42d45821006aa000e4807001c1e6079108210684c0f0030355007018660140c01d05040c808a1207512540d003003003995442c00b88084512010400c00e544410302034034040d00030518030f4410591241042e01002100e0720440c81000d9040e2000d83d042c1d00c0128400300c080030058071802c4c2c40904a0710a07900340720034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 846989946 1250 846988696 846988787
    0x102070b1b070311011d030414030d0e09041a0106090f090b1005032511010e0c01080115030e060703090c060c0f020d020d050106030308190e060f0925060f 68
    0x1c400c080b8186400c14206c4080e103288100066542e9894803c100f10026000040b0038843d800110407404410b800c6040c1c6407407060215540e001a984619011a507150121001e625904042c0d00101d500d6030012030f208244c13505002c14103900c1e03581e51800026281ea85407450741148101400e120000c1c0078202450b00040d403420350710825040100310819a840c40080c04001402c1036280c68210f00d1b0070f208502d4500d981c2e0001c0c0c08400c25000010f00f140d6818410b071041114002c0b840c44526102e035000f24072100f145030031f440080c14880b200401400381c0b00c00c180c5209100c0720000030402c3c012201c0700d0405500a00d40030101d003041c4c0070400700840003207050b070b00950014030b800c00081d001c0c450a4051846502c8040e250b01306007440e0008040482481c0b40d00758501107900075141400164154004508176200000ba990303000c07024107110b40e25214407080341c1180000c40190803200c44400c2503c8080e90b80d00c407107000703076030f0121401707041601401503540f0346c4542c1c0154040094801d0449410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 846991196 1250 846989946 846989951
    0xa0c1409060a3906061212050901110f0f0705030303040b0609150d06060e010f0303120513050703110103140126071d0603120c1f1407020102070b1b07031101 69
    0x40c19006101d102501c030f004918600d564184800801c00c07144201030261032503001c0d400180d00a41e5a035080d50b0b00381c815240a100000c10780030750300d030711400d070101d14046107034107680401003000180c0382c0e900a600e00c440e801c3d000c4d003400407500b0300380001600d00c250703000145055140c40741824011030035009000e140031030b01c903180d0390002c58481300b40324001140308200005080780307061441c041d15201a0458140c4940c003070020004240d003d4640f40200010b01c0c00014192151020300c4141c0c24125801041d50286404c000140246680c0400d94008280c0301807003071500d501d60422a8080034041e00007004034001e0000c221707805d580110340100d031100c0c0440ba60701d5111035040381d210f191011035200b0501c5481c208605820144001045100030640740b03402d041140d4036140c1c1300e0306140090070303101c102104686c41c00c41c0250490b81d09030601d1031000380c1904101030024040c3d88283c03000c2d50030f05810790204000d000b007206040d003000c1c2c8007850305040c01d034542d40071501a80400c0d4040019134 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 846992446 1250 846991196 846991247
    0x901230412050c0a090b18060a03050715170105010c030e01020a0b0c040812041202011409061809090c030d050703030b0907020a03090b040b030a11120a0c1409060a 72
    0x107201501d004460042e00140140c1109000304900d00e682a00100c0146081c400a481319443d01648907040c1d8814403031076141f541e200c0c40441d100c4042d55101600520030504000780e80d00e4180da402500040c2991080641105072011030100079007031242e240094100c140c102d0100348600e05a0315540d20501c10380d15490f2568860404051013610200144100050108515235080000c2e8801c440c80440484c00d05192081c1c0140000e84184042d040c030a20900484c81d141c080421107502034001004c0c40c0d1102102640f442001449415580c0240e0b00b07400030403140d00d000114140d0121009000346078582c8a46000c9a0a4011107011428180c42c0d1074000c0c0c0300d40e02d880c0f00794070a6240741e0040226040a04000f840384005510412081404100600c071982040c0d0407240e0192040a01080c1410030203089150743c400c40c0650401c1d0a507150500a1054683d080070782804042d40d41d4440c00e840903200d05d82c8503c5018241c3d03500100800000310310350300940a90726016a000311720305680 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 846993696 1250 846992446 846992459
    0x1406010c02130e0c030c04152603070b041e0b011403010e01050103140d09140f06040302040f0e0d0201020c0604020d020114070302010c02191a040206390309012304 72
    0x80343d0406408400b60013a0410711100c0c103040101058100c4126414011911a140d030311203442c045001d855812072a940596000c01036100e4030850a15924003201da6840c400d052405810070b00380c804440b8030008001c0040c081101c0011120743c5500490518000c0e481c0c61048541040401c0020f50555200c40400e003903074200f8855103000303600035100d40301c110080c4028503003048418400076090088000c0305200c200030742010b4256002c0f064074030801050341d00001404900a0340d00080d40a030500200711042403007a0424a844028175086850a21030307807400b6400d03801402030304000340d80090005000f5291046c0042226401810000c8040390440c00403010340d40004003e6015070345a400d0391000c15410462514917105040c0f011800810b40d5030380c0b210400c480161b107115400050007041c295502d1008980390034100713080c0e0004900b081245075064950208401c070010110303c0040c2c25041020040b01c904840503580d5404190002c4101034002007140080d1000d584240b20110b2070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 846994946 1250 846993696 846993701
    0x60f0f1d060a0c1401020a090b03060d06060909030e0307080c040b0f03120a0e010215010306051e01080703110301021614010917030402100c0b16021c05030f0a1406010c0213 76
    0xc03400380381c0e581d64203c48a424130202682013150a040b084e84100106a00c00e80d00c403290100b0307110340e00102942c9803034440001da820340e407418016156501d031440c0040c111116600c02c40c445440307916a41445c1101c40101a1150860b208003105508005410030440c501a40300d200000c0d0000e100324220418000444d00c0c1c0800c1b8580341011610008680300d0050b00410074005141091000b800c03403042e00e0343d01e00540c42c4180303c010b001b981c4540205251002c003520100103400106d0341000c8941c1e403442e03125030b604050310065070758415121000d03515003818000c49210f101d040d041c81c102e0a080d96030340220784c081001d45889656a9100e01300020f250081c14000811070168400d841c1e0034540108800003040c2c2e221501403000942030000040c050420545c0d00c0f4088922201f5020041e6105a0804461821407600415602c440b41e2a06800202450044010420702d000380e6488907105002c543c043d12406002d50384110024180e036100d000a9411315102500792200351002002c0e1000703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 846996196 1250 846994946 846994957
    0x1d0d0206190c1103071b090c050f0a052b150509060111150a02120a0c020d0f0309020603010f030303060b070c23120105041403070b0f090a0c0618060f0f1d06 69
    0x3e01041100034a003840070709202d86e0001c1e0401403010400003602c0400034000384981401c40c815080045602d9800314010819940b0b0400506031035074411001200d04c2024078071800e803903001a0f2420b010480840103c40c0d000f4180e500181c44040300740c0701d41c401903465001cdd10200c0c18403407240c0c148441c1495030640906008064100300581c03201103003c0c2700012008000c212008107072408c2c0c0b000c03d00301d0380010f001c0300b01421414080f6a109000c5800c5011b0640913038080d420070000000007c002401070115401c4030f0003039500b084500c5e210305428406108200c40584030b034102100c14001c1c07452000340702d0040a90103041999290950004c036041300940c00c0030b503043e03956a1040009000da1020f6207140c20300e01c0805145007e047da03440448180001e0a940a0000c89a0010f05100c5041059010080c0c10400130755080ba515203000b01080c2c1d851508a10085001200150b1603011790050805a21982c607403400124035044101c4080003c00d4800030300003800486003490f910307160001c24 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 846997446 1250 846996196 846996203
    0x62d03050d020f1b010503060f060409020f030f0612060c1c050406091a010b250501151508010b040b0307020a1212050c0c03030c03090f011d0d0206190c110307 70
    0x3c8004010845509002040640f9a8100c0e03403003440e641160b0f80881107a80c003c0c4101c03085100110094080780c4203002e80d07005038030824400560003e400051501a611900e03050440100c60ba4910040c4204a070658141560660210000c85c000312840b1020b003e01d04403d8070300541d080700c19480d42e800c4d51030568040e14503030b503226039250a000c0311102045200e400390990100725407604490760728a1152030f244d240c0100d01c482d10b0010300358003020150f180340e401900920603c542e01c46292001d81003441440c5540c0c40345c0e89007409090040440e641200e01d4a100c0300e08113071070900e2200581c0d00040071502103000707104881c4001243d609a1b004070000341c0e035500b45620449161541201c00141519114800c10b100d03103032040c100002100d071711201c2402c0c0716071a5101c00c13040a290003034258403000071354240310301c4828009901c05610000d044a00865a102c1030f03500040c0e848050540e2041d0b001c02e080d90150340d040c5819041030810400b14030300500560000300711213007542c10050084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 846998696 1250 846997446 846997453
    0x403022b1e121215050105030a0b0d1a010513050f0a0504031707030203010f05060c0706030e10050a050601090e0402090414030906030405060609011a030f04021f0206010e0703062d03050d02 83
    0x540b660180c1e4482c440900c5404e03002c0ca84001d0a000c0068105c1c0001002801c1c00d0362286c0a80c120f60329494010407005078480049920380400000c120414036090050b28003070360382d2080c0440380c12601c0c000c1da40160b44500e200c00440d117030705d29aa009098028010340501c151081c0f034064800000100511500240d54016106d5041502e6624812019030249216000a0012003407520010400c181111518107001a80c001840c500506000c0c40000d004041ea103040100700742040160450f41c030450090340c0d807241864030364400c444003490a50b0040e400281c0480007500041d050f10120b031415000c0421682000c02900000d803455104690440e4035800c0343c0305001316410306d45a03690141080000314030520340c0d4490200e0b02400002c2056041541050100e0195180c010700300500e04240030010f00e45403503010029584107820302c00c8cc0b00140052001030301140c821300c2404103540481300541c00340c501c851880011800c0a80300e281c5030751040304000002500c01c03c60361007480391039000b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 846999946 1250 846998696 846998717
    0xa08012312010f1a1f09080709090c05091e2505070b0723030703020f04080c0a0b0c1f02090301141006020328020a02060a02030403022b1e12 62
    0x110240c0d13a401d02151040e031400d00480e841a984d20101039924a4030f8140c440f044242c8020485000195900851b43c07405a080040b0300110140c00004440c0d0003400f400342c03560350f55018807154442c1228880307400020300003441c00251081310055002910044003901030801d410740c1a1110481c204660040307440001d4800800010f00c00441d440303695410460284030940d44d00c9001c40c006455807000c2034200000090601e4003907419034dc101e000800015072615210850729a5510143c4017052003032a0960001034090940406c80f000c00c2c50410161561103400000280320780c5624007000801078007445552a5901c0911071442c1d0a038120804076083c0c2050f05811074120b44540204045410400540101c40724903038801d0b0341001c19171408244c807021010220304260303030900001d602001c00200b0000c12a40000580700366402100e00d1200c092550110700c050000d81c8131107440030415202c0080c085280c80a40040480401c613610306021007542d14020b0016102180d01d01041c9203589 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 847001196 1250 846999946 846999971
    0x90305070f030614041e1b0b03012301020355030b0102030909090a0c15021608060a110f0403060515040218060a0522060201110a0801231201 62
    0xa00110000f501e0300d010071508140d280c040c000f084035664102071b48400c0301200c013007004c042160540c030483e0540701255192030790300e00c0b140f541c0203100d001541d441c240301d0202c48000e848991448071405800a51419800c000c070341354000000310a10f44e07500c0c0c0e01001d0f00d0f00d0b08404410700c0d2902128540c0e10459462004030006510302c00d020380e2040600c0c1c802170300910390b0008104d5511200481b40c042103503807003034061483c10b901c0c264000c1c003c2d061800000b46400c90415a0700404280e0f0f000c1d6075441e00ca403a40c028000d409485568071079480200440c02c400e8003581720b416908110f40c032080c54210702c111401010341c03066108942c1940c0c1c4004104401948802e03000e24507404440543c6000c00454050b0001302e881c3d04080e22070702c070006000241e18000d000b1070fa0107402d690a074800c1d00408100034142c8814910986025509045903a0b00b03011200d8100d51150885880700460361b42010451510705691858041c100000da900044481e902c0c1d02050303200341014400851158001070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 847002446 1250 847001196 847001201
    0x20711090c03010308070b0a090f12020105090f0723120d0305010923061f0c150c021507141602120c010e0f0301090212251a0a090305070f0306 63
    0x500a418a041c18030043c40020b07218030440d14210740100c5071403120744501001100900310801d0051044a001d0481401c20211000341d84001d225034000300700c240d444442141e181c41032110f400c17407550044001403100245c0144803103511025507007400314440001e0301245844296901d0103200780e00c000d2152031619450700034240500190344007807102c85138400c81c00142101d20050700401d41803000004040b40c850941c9200072074201d06401f40304207208500a403001c2c1044500340caa1010b81e00746621885014010020034200343da000f0080c001c15940c1c20f00c45290301500010800c84800e48a49005031201b016107007010300c00000715a110303045e10420000d030a4410301d00c00b40346c012003070b00704503a81c0018840030480c4080c2c6510310362040341000a0300400301d80d20001e51280300584450b601040015400240c000840411a6503106110041820399100e00ca01507546201890140e89106c114002e860561150f040c0000d2550312a983c10381000d485821440c4034030204d0800700284a00e50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 847003696 1250 847002446 847002451
    0x211203093004030209041703010b130e0903070b0c0702150c010b010c020105090d060237020c0906010e0303070c0b18060309030f1b01180b01060e22020d02071109 71
    0x1510140c41c0302550296510a80103a2001900c50ba130745100040606c240040c290a0390f2040300e050030f40d29a120044c1040c5034001d0a10b109280080e8800411602c100302c0311640203455800055003450302035075038443ea0020041446d4035500040c09810016141c10040455400e4142c0c0c9054803580e50401c15421070701c848403400e04228501c030720a4003603600001180c002000907502204500340303506204c0081d00c1005420814240d60203001007072001580c00303150014105800055181c01c03c624100e82e20360030740c074000c0d40c4400140003040c1c2640c0500d540301c20705031001c1c06407800e281550f01d80c082400d07656440941c124100154900f00b0400b030741c80c0313400d00f480f003102d89500b141020260030f5924000c000c04c031200507000013600d11000702580c10030309801d10080f000384402c0003254080c00926000800489000c0c03107200001c030f511405403424150703141d005070240425000e8481c062041240600440c041107600708a00804881240000c1c01143d0054a4103600d850a000c00c1c0100031100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 847004946 1250 847003696 847003753
    0x9080702010e09061806010c02031002040e060114040506091206090a050c0307030308010b0705160b090a0f0513150816080f06070c03031e021b01110921120309 70
    0x202c80820840d6540d0707503000300700340244e2483c0150a56506c001a6150011124041e45c075124400744040000c40f0381d0000d000744e40400c1c034010210340fa11300c01516900b540c460400c0e040d80051005200c10309001000d405408001042d418401070701c0740c07a080c2800c90039540c045072908020ba0341000c2c0f203010401e04030780c040150010082d680c65a1001080208103000d03020703039104001540c40c24454100030629400c0c0302115800113541da600d0385603000f039120203d00c1e402140c080c400020154a696107048c01c640340030704400741810344070003c2c10040203a924002c001d407002041c0451030b0027082141844041035900340035031907801d01c400145032002c3c1c580252174a50054003040001c1e6440299400000d80c14140419002d41c07100c0c0e5003100d105040980da0340c0b0f074408120102c500c039000b03060f036481b400d5034002000b820361200b81c0e17081a4841c03244929005691700c1b42d000503a001e01c0e0034031071403030316000262881c0f01c68903008500940d105603810441d0354003810004586048900c00b20201494 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 847006196 1250 847004946 847004959
    0x240403080f07061a060d090515070908070504063c080f010e07120f050a0b0f01091404020622050a120b0a1b03092a0f1e0e071209080702010e 62
    0x1303941000034003a208103212200320a454038140b40400604006130464000e051005001c6454040d0004150340030314403c038179962240007c00601030409101e400c046c0c84500100005049513208412034250701920320030344614a6001035003074041c0703515403c07018180881c082c12001d0f9034004500c2c2900d15090300309915401c0760500b0095162081808001c450780b0002280c1c98240e541485810040c80c0349016112078a6402045001041000e05506072001e11030208800403180c3c441c2e1142140442e030084d081442000220000070703032262811020a18511441c440546a5021075842c50300c5134800d0140c401142614402c01080e0400640d100c803c507030040100c0c80c2104106405c800d60801558141513607a64540c083c404203041c01a60000e0201d03401300c0e1a070001c03542c010040740510035104c01209400707021581f2450407030908451b00f6641c2841500c01e00309a00401e0040300a007406051010345003d41044407443e00401d400907002e000d030701e51142d45600002d04603450003d101e503c40ca9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 847007446 1250 847006196 847006241
    0x13080609071706010306110c03040f182003090109020a08100b031504170d0e0d231c0e06040807020a050d0203100c140d020415030b240403080f0706 65
    0x140001c0184c1100c0d0081e2021032100c0031203120b0b0f6024460901004400c1c0800a00410100e50f030055081c1290b44020403801880c80b03a48000c0c040b901e0748540300e0401060050100c1b50401c20001440c2c0150f40e16000003503148140e400190030b01307415030009500e80c204810140100f104c901c1080030001c416000340c0400c803e46a807071035018a0040004001400b2404540e017100c1e440000e1390120000d8080c00c124503d4940c2c426a944c80d480541a4006034450a1444030080e540c46030280d410001c03d1114249000050403070020fa9000d42c3d10002c0581c1c40c3d0003209075100c00c00c6501e001c0c40c0030711542c9560f01c1d00c0f80180010640c06805c0740b030258903e141c8400050b00d0008080940c0002c4e541c000410301c54171207080720081c0450844102d030000100d01141c0c01c20b2540d008000700c4150070407250301d801d08520309a09840021100ea5801098000b1a2a8401c00942d81c54150903280c0c5100346411788954681103640c110503002c09554401140317000030000903215140101000200c1c250450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 847008696 1250 847007446 847007489
    0x609070501050c070909030c0605010b031b042702071b06030f0c12020702030c03070b0a17042f100306080105060d0206041406040b160210110303011a1308060907 71
    0x2004c8500c255000140d84d04050000e0500c2441e801e5580ca5116500b4000e80d40d5401c00c098182c3c1082e907217160341c800002c003010042c59550044400b02c0d131019a00d14440494440c030300e02001408140d91441940812103003000500b2814440e410101e4a04020b2120741440c0008049405d4a031441554074600149101581e420607005040e01c4003145001d40da030607242c40401d06004010709156014070a100c0007041e016524005045501d902c0d41c0c91104031004010b003003844c0300c4142c3c0c010700034481d102c0c52112003000455814101088518050442212000c080b5001024880b1200c00190f9030380d80610040e0340030b000d16a00410112094080c020894000510b82e202e24810030455000c2c64007040210340301d80f800e0360002e0031603020301b031348540190903018122425814128400c1a40300a0300400e030707001d00a40b40042901100450039a802d00190144c0040142a1582500d03814410340030b0011103604004064141c00c40940760900f00588498645641c9801c99035492480041d02000b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 847009946 1250 847008696 847008703
    0x30c0905091f0b0a06020607120908040e0403110d02100e0303161805130f0c1106070302090a0308070c030b060102030a02031e1201030b04021503150d020109090e0609070501050c 78
    0x10181c5031010311500c500c02d441540000c0031820851034101103100c000188660300481d882c0d106c1c0201d92134622010050403c05801c40703c4a040013802c03820b0a000600c4a1480c100c20760707038041d101381041000803200c0248070f0302d003421620300350b40140d0042c80c282114400c1405141610221400250b0540c204004101d085005003c068000c000c4402e0300003440d5203010400078010b003030103003c0302c40325404600f803800a007040b011072981c214240087e0000c00c522070041000340c44070f010003518130750712a40b5044029510441c02e196005e1182403021000c103000000800e409071190690100d05441c502d09100040340040c43d56040d5082401000c0400f03030048102c400c1100c03107080400800141a00441980c01512f034640102580b0302c00200402c07140c45d000b940601e000f15145000e00344c0c800c03240d00042c03000300e4036a0001440c1200310201410031481022000384141428110651140c005000721a064520001c981e44040d00740072900c00c0912401c00500820f285c501e00d4071401982e02a907 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 847011196 1250 847009946 847009963
    0x3030f090c12190602190201020d060f05150706060f0905060a06090f060c0c09021605070519090c030f020f0d110403020102030a1d06070807110d0b0703110d060807030c090509 77
    0xc01c8044070643c1c0c1e003004070300d5040300c003414050100707894941c0d0190070090003508245607020b036072840c103400869000d500c04d20303c1c400c44800811050048011041a6030190040202184c40a03100c50000c900c964a0046600c09404042000550380c9401000c00400c840c1540c080030a2010810040c02046e02c00e000801c00c3d42e5107810b000072020603519051010074503960048001c188045003183c41c41ca141044100c0703a5002da41103074100c0b516001003040443c580b034104609042d4140042003203406903040b4101e030f8101ba04000030a0501d81e01040d042e42c0c400d202c008a802800222041001071512507400908516040981400d041d030f40081d540348241034024007407000c6e003074440c007808244480c5070320300c900b000e4141e030744506284c6000d2519801410301101c00614401d210a098103241104181c03264015002c0c030201d4036070f150160014010009404882c4c1300400110304664a20701034400117100c40d0008208407071030b40c1030040702500c958000600c05401d00090143c0781c44001001310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 847012446 1250 847011196 847011223
    0x30507030b04020f0a26032106011403060a0302040c020f060f0a060902070f060e0a0812150616021210180605090d1d060702090403020c10141e0c03030f090c12 70
    0x81c03008184444c903601d9070180403005440881d880c0060a502001d0300b803914046c0c5022f8a940003c8540c04031003c490340421204036030003070a08201000580f400d50001440d041803401074440346000641000d007040401c546818480000509100854107140f240e10b0061400c0c107411810615140e80c0c0d240c0a03002410301030581c5413944200baa84000c1808003800e041d0384400c00d21f07035a5040c45980c507400300003101e2074a81b200000442c0d00045c10280c04992456a5280020350241601d500b080371039036a1034089201445010801c1d40840b80398410036070007100484642102e150203181840659000038044440d5402ca8086803001c2a080541c0301071140e00700705000b4030450182c010074264001d00710060350001070201480241030f00801e546403032140542304007602203c40c01040d1244c107860300041002002c10050f80c00c00203145d44a1103401d50517034000c4c920302a503001c1c8680c0303590029605051b442c0000014495817040400180940f80c00c11707128072140c5c1d000700304601e44070200e426240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 847013696 1250 847012446 847012499
    0x70809060d02120109050a060603050103050a14070b0a020715030603030507290703020d060515121008070b19080112080706090203061e1b03011e030507030b04020f0a 73
    0x5100c014281c059540f02200b826861001d580c0d14540b08024003800d54008041c10301d490804240240301e801103034140ca400070010701c101e45982ea101d900d10f000d40000c00f02d01d4040c2c1140403400d80e07805001001a14402d50080041d5420402e10200c0910311060503020315140510030000280c0040c2500c148540080304104030410f031084503110000740d000d81012054054040284041d0503901410340300b01030503020031150b600c83c0309102c55a810001c08840c141824001c4e1401c40d02000380759540b01c0c5120400e041102d0b52080340c1860040c4075004111214004034210f404d80108a40c03080b081c1c002842c2200840d4900014401d180c1c061050142c01014002104014407034150408000c0d15405411a50742d441c1841c10002c3c0c0c045043e130103541c0d1036402d2021810080c2890410321014080211161035a440c0441000580c00c0d4081d410740fa12001500001c04100b0510069000794000c0351b0410907858a4410811801d0141100e03d01c00d840c0c81c40c0500c003803030801003038020400291400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 847014946 1250 847013696 847013707
    0x6140108220b01030320070e0a090533070f09090c020313262409070305030414090915041e050105010b0406022a0607030c141c02010207080906 63
    0x10700200c07919280506100c0444000104260740070a0b4010030384810a01a481d58418140382510341000348603030707000714071140041212944507600c2016913034030401c1220901d01d01d0303003440070b150032035485200b40f84d440c00d05207104800d8240c40b000d54440181d150181c42c2800030503020381180e03030b917020380784030166199540041103008204413a52411100060540941c0c0c645505d8840064541d04c28000e141540a00544440019052268004a152030a82820360326003984e00d0800003401d90a0b680f142150010101d4001d00050019041207810700d40e008400c8414013407500c20160800c0c86942c0b12680034060340c0085030302250040d5100c1d81542303010402d04001d2104443c03207240a4115440c0000000e04403005070000c108880568094450f42d0305207040e003860380d990040075005c0c80700c19281c07000d100e854414000c1032081d2003420107004500305610f0301140341c40d00044010310341c0d12801346031400c00c085e405440303030700c0c2e0301032000f5450101c0b079a40b05901806000c030b4560046070003044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 847016196 1250 847014946 847014991
    0x627010b030a061806051201150308030408090612070305011221030f0e010501140402090901120f080c0604021f050405010e0303090411040905090a03090b0304020d0605010b0d06140108 81
    0x1074001080403213200000460320030084030003400c6603c50188202c00c030211401c00f148041c050302ca10001d11203c0701e5206440d40c0c0329051b4560006000301d40e000c0d020000c4456035516400689188808184802c0c16492f29801c050210b62041c0c100340f0351080c007196400001000712607001c0380050340c060700904503440304d182500500342148900d5012814191804000e000c154001c0f03040310380b4a00100c0c240074510060204070310641d03012640040c1c03500c0046c8800e811240c0c40c0d42103103204004103d41124980c0b070f8421103402c004980e010b40d82240e0284000c0d03280c50700700805158076440300d02540b080d081b8009055072083d0301c2498140001070000c10ba0030340d41441030701c21091000d4400e0042134440ca2400060b94828020400001d280c0b1001c40c0080b01d001800341000e0380e1640751030b1034060404401c48401d400090089910502700f4103000002005801200d00074540420110b49805000030344909487e00c0c2c0e00411540c8890300f00164442c0e900c000e009403c10003d10207682c3d507001140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 847017446 1250 847016196 847016201
    0x315030b01170c041b05030417070c06030e0616140c0610060f020313270c0201020d0b040e060f040c08070b13050105270d050a0501050627010b030a 65
    0x28005089012000d00028070b41400300c6070a030a120084003a9003084a0000421044440314200058000c18030b100000303016015034000d64019000d060711270088500c807601c00010f42e102c45822107400b003c1580422a190301401841c0c441c4105c18007600113850301c900000e034440d90315040b0030304005000b01d121440d40c0e51701003204d864010071810744041d844e200142804501131489080005030300e00d260110001d00c007105441840d070b10754a480b860b203850444900c2c0c0711451603035482000281c038400411004618841d4115000480d000561100600002c4004032220b040656015900344044013400501c04111242c1c07003264400740d4240fa884504180103020925000300c03090703100b603174408902c0c8200c41001c0c04800c8603401c9580701185d120310044800f03010f014503c0c025041070071020f440c50500d001609101c02400341c204030311201f094440c103241c10740c3c2e1542518542d540f8000e2085034108084074000c51418081c48044501d4800311140c441d400500c1006000d400100c0841c3d02e80c0710a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 847018696 1250 847017446 847017449
    0x3081504090b0907030c1505030f07030e1005011e030803060402031e0a060806100305030909190609020310091808030702010626010e0f19020604121419080a0315 71
    0x614190090710303080c401103035100118002924440b0303182c1b84c00500d00d07110f903c00744d241007440c0c3e4641d400e42e12511500403020101030036940a058480300c1102c00141c0c20003200e4103d01301008081115490610f29041141000182c1c62900f50b0302c44041c8085049036080340c0e004082507e0041e80c2e0781d150b2264140840b0f841c0ca14408400e000070920012000640000302a5080320040d02c80341d444095508100004e60b20004000c1e80080c041c40784507180010400394460408000110703030051a5884c40215003454000a00d0107a010007400048101450504058507140707104002d0381c0e2002c2c100b800e100346c100301c00030030940f4004002030300f462007034110344000c240c20100307031070f01c40b9445800c0103035040350306d107446160341c41c241e18001c40850000300401504a4040544001c4545598a1440140c6003800780c0c1c000c00d04001c001401c2e6001000f00101074050500b080c0302d031460b041c0c1c59080030842d8501c55201800d1030541e0001c108060b0440e10844145e090004480071b5001c3d01d6190f16215 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 847019946 1250 847018696 847018703
    0x5102601080a1709010e0409050f0313080609030a0207152a05011a0f060703021501290906030601031d0a0302160e1303050c070f0803090108090a0308150409 69
    0x64800014416100145495081e48a080a00410110000d00c1c105502071080d02c2d0b40064003949200c2d600e820268495600240100184d4400c14180d0010b070b031031640310551071543c0c00d00700601000309907803c0c0300c402c0d00004000059468807040c00002541c070002402006040040c480c0036801d52401048407401d80720480500c202c040280d00501c58142c150b4660548041d403c105140c0d01c481e9034001c914201b40001040c1c50501c0914209114aa4010384412004d41c440c50140c00c240c030100c0b0111074001d00d0810142c0508a03008006500078024848841005500c20b1059000c19a5507400b580c1e4060b40030301c1d001580b00e42e101c004824120f49048090128002c0e01c2c41d81c0203150307001c00c004503414041b4150194540e6108452110a4070031514a002045400e01c82d03400a0321071001003e8070000682103551131a2103035000141e0b02019400580f850f440022021007075600140482e82c08004600038004034101510080e280c504000d0080c180140142030480c21aa500c0c0d2104518680 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 847021196 1250 847019946 847020017
    0x40b0709080703150b31020d140105010f05040b09040207060b1905011803050a060902010c0b090f0706030506280b0d050f0112020d0605100b0a0507110102070510 71
    0x580b401c01006080104c2c2c025614681080e0000e442420850304401e1200b48200303124010007211b80042d05c04208100c41034417401e8003000300240c61501070107075403543c55240a10319890352510b40054401281c124500080c06414032041104118684c1a540c07854019540540d540c0c4262424000401c0c6801c8115440a104440c1050201c034410122041c0c0c1c80a0302c68004100007080e5880c44070025200040c110340c0800a200c000403580c0c1c000c814524410f05101e42d000c01d0f2a620b80641c1d60f812140d1325059484002e8842000f602045040003c16250408010318181400807a5240c90300c22042c1c04102070840c0d034a8074803850680d4840040010a4407151903664116074800580000d480d21600c8220920010401004c2c07104040300c81c683c000d008401c3c2d22b55660b1144080c2070000c0011084d14899280001e066480c0001003002c5003055403080e603520740918005100c1510040424110340c01203005101130348902c008000b03200c07a5400c0c02d46e407910469210344001d015090700902d1400707 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 847022446 1250 847021196 847021199
    0x1081909111002100e030f091318051c03061d13080f040302010905041a09040c0b0304080702090f151519050903100c0c140c030f210f03040b07090807 66
    0x141c3c00700700d40c003825203905002d004001c0c10990080c0d403401116980486a03004100c614168580030341030b01c2000c1d62403007000c24110900312540b00107851104058803150400e1081600d11481c1710030080002d90941801c201b014145070a00b441e180c10704002d44641c44845010074461000c24408a1442e540310701241d64034400502c0c410745580141c031040340400c41e4000081051303e00341c00b03128100d81c0a840c02030300503a1500f00308105c0c00c50190060382c00c03c01440d0080385030f409260065115500501d512a40c5004c244144988090001c001032002c02c0c2460a00c0700905035400d4081c1504411541c179140d0000902c21a17480d07100b6480c1c04030024100a800801c1550030030042c1505050880c26101c61084c0d9003a00b809445010a0110026150204090014034984c1c041d8194200e0082200c05062030a0003082c60004c1140100c60f595002507090401e0002c610440d52801582c405954140980078030808260701000c0c10040c06121100005512240b04004035001820f900c0120780c04d0b04e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 847023696 1250 847022446 847022479
    0x1b0b0706021b0703110a050301020f0f160803090a210905040f15180510350105040f0b060a140906010c021f091202101103040b04080c0a050108190911 66
    0x17440600086000b6111103000081c586818400c0c0e40d0085038885045140c14036520740040740b58404007814201c900b40c424040c012401100140d44a1104040148000d0925003080700f04124030745980d0031060907a03404180c405900451320012602c0076940031138030b1141d43c4442000303041d0141940c20103c401c3c0170300285040d03401c0416100311408890030441030b220414180880703c200d000d914074024948404401d8160709207003040c00c560000020190740b2952401c140d003962000e803026a0603030180702041c0240000c8a8116800190488072040d0b01803400b03400303050b481c2e490000c1074407404038000020947c4c0d009081400c202e9600514011940d415664040440d142494031000002c03980c00d80814680903c102c404400d5800030807603001010180011249030b45040d5200700c45010600c400201d440b540e0300904047d158050242135540008000c4c010300502d5a40a54100a0345d0400d01c0b0082c0d441c0581d21228032502280072400700c00500b0042240031280e012560030008443d6466644c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 847024946 1250 847023696 847023713
    0x4020f12011b021612170c013c020d0e150412090303080f04170d02040501031b091503060b161103060606031f03080703020102071b0b0706021b0703 65
    0x42c0b6100500e820420a002c00100eaa402c0420104004038600d00014401d14008480c9400303d00d20840481c105d50320908018081900f080c0c80c000c1142e03441e86844940c1c405a1451485140403900c40800d452116045201c2c0c040c25125860000c10b0780045d01944102d102c0d04200c40100c070160880c0c0004802c1c3c540c0019071036085070280c0702c4e6450b042603100c03103603c01c183c11021039816544103070032500d4406103011825805032007210000c026158506807504504041d120b2036044080042c0c0781c501d002c00160540b000d480c90b1007059211780402000d110740001c0ca24050318000c0d0f0f03c413400120701d1b40c410340080100d500109440880400d0b050b0100020341c0c1c20082c00c9103c4c81c405241d0003900000c2c540d5500c1e05a070810351020051000030200d80d02c28100305c4101c4810800e11554607038a40b0794403a260b201d03041c241c006035000113281042c0807210b80e4010000309030541451403e0b107081400d2889014901e0300410780c0d600002c4003101001c440e9204581031b24108151503000d0f6591511402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 847026196 1250 847024946 847024961
    0x70302120c01090f030b060f03030c0115060221070311070b030a0203060f01050c0c0f0103150e0114010819020d0f020d1a1e04051003170a0201050114100804020f1201 73
    0x802c0d0315000704814207800e1380001286d0b40505a685c1e140c4410041000c0c1692084541e50540300600c20110070300707c00d01a00ca004106c105a4007460360030000700a044c80c400362200e80070003020900004d01c000102c0101c1b0116901458507030b1940c01e20408040c10f21000d98040b882c2000d01005115040301a50b00947c000c8000f15200e0703200d00e2203c4011344090140301007000d41c83d004101d4241c000e040c50000e0740034001052400103451046030441c0b150980f03144c4c0094039a86550401071102030302c2c46ca158422030b142400c16071840d14003001801e0001750510f00f2021095004180307940088495000701d1492070658100703644440600340090000c1c00a05480c41080d034000843c031455050031032140078508000c40e054400301044005000141c00c018190b00003420a11f074001001c03814060b90b0103209044041c03100d6580307444000c003c0c2941c02c1030308081c0301e144042e06d00c4ca625aa404043d451402c1107407d0440d00c40d03a80e400004c418010414070b40c2e80180c0c2c000b10410600b00706500c140b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 847027446 1250 847026196 847026199
    0xe010606110309090c040f030609052517011404030e030607030b0d0206130e04140f060105011d0f100c05011406210109080a2a12050705070302120c 65
    0x102160360348400720369580031100c400090390010404000c150506000c1c4542c0000e00c00703485441e099a8000d1444650141d42c0261007043e650b40c0510704015003406407581c0d92101208a07440a40f860f0a1400d050b6040c1c8100080c0442d07048120600340f000390401c40d0201c0c400c004030074880c60942805800f9409204185200340240d0300080c2006000748240e048840c8042c00403000215030382c4c24042e02c0d43c44030261541c612401e00c000111300c0c0100720640c0c420751040804c400c44a4240041c2071501c042e00c920500650031000042c40241d0b0720140b13501a00b61021100c0403907a16810100784000311314481e945e003001303107868000701541e0003000041d14140f1a0700204418030070b151401c200c00d8400d80e90103900100080124005000b2003e4820101d4130f450000a901a82035035100c42c0d65100c1c40190340411020251900110407816041030f4100440401529601c0d0980e40c0c00721110700407003920180300021a404e0240441000074101450b0b018010340c0014243c4098242c0c0d17002400c0400707 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 847028696 1250 847027446 847027451
    0x915090f0e030301210f0f050f0a08091003180303150e06100804080d060f0e06120d260103060b15040b03040609060e0d0c2904230609010e01 62
    0x400300c940161055140441100c0d0146055074203146144440a0b18501d95070a00364007a10294007284034181720010300c80c030400d0390350509245494902d00b0242c80c10007030300c0d440c2c02400408c40403c1c42030301141c0c001e200444081828100c220401e80040695005190300811800318010406802d47d07c40c0504103038684413100400c1d921026003400d681c04684254101c0940c408034001c89000d45070a940051140140a0a100d40314148034110b5506510086a02c15021810058002c01e0a420350304003800ba030f4a1911440700c00506956042c0d0b0017400c1c000c01071040045608800c8254078043c11005280683c506945c2d281800c1000c0d0628940d03643c440c1d032400c54610a500f4503c0300b110100c8801d0458a4116030351901c03a0b00c01410350010035101c50352190648640c3c88801e02408540c0ba88644134450510311900380580c000c60b00d8251300c94480c10306c800610b09000c1000307010ba80940c1c002c09042d00006e00304141311041c20000000c440904c00c400500036140c1040d0004003054042c00001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 847029946 1250 847028696 847028711
    0x1050403110a020f19150c110109060c02150c0d05030f060109050a0303080c070816060b060c0709050901091b030b071701091805030d02040f09060e070c0c091509 71
    0x70b89521500b14002d5000c155003103200d401d400d148a500b4100000d800882000d43d59504d509545122488403140005845600070790801c210700c00c03200103000080c0b070020a00d9081c03080207450b400c11040064401c8400c1046a80084e2006c0111a4024441d906598402161000103041340c1c2041d1200e0620b110454005a49541b05400d240101c68004210000c440e03c0c40c4c80c16966424042d010400b082400c0014602040c16500105250641580040d1044c805401c21710101c41c00e80840d50722030201008800104100080d80c48180c0754484c0c0000396640396411000d005007000140188012500207414004468540410040300c0c0114201c400342d03038600000700d03404403d000003021035a40800c0180030381d51305503002c518004c07680008055a0105515000d184d44c002c03c0c50b4003c0030790001014031404030600080740050010900900606042005034805402d0081070081041031a600c2c03801405003a4442a00a004100040000740c4c03443c0d070880804c0c000c600401213500d052001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 847031196 1250 847029946 847029977
    0x8130905060411030f07090819050c0102011119120f060312080606030103060b030c090108100608011404032102030403031b020609070302210313091401030f03050d110a0201050403 79
    0x501d10001168515107803841e500d4079803041c07071703800040e09020400640e12004600440304100d4000d0001d0000c000c3c0e50709400f0341ca803103890256080343d094116410306401c01003c420b000140c0b00b00855009000c142d00082c6442290004605042460a6401c1c07183d0300501c2011903100009490180d806408808103091060301c01c4038080d80d0060300403104000400109500d584a03122001004098a982034225000a0080b0100780c0085000786c100460505c0c15102c00e1180342d0041c1a100300034440d0300340300041c9280540c2c0050000c0d080c4400911503100e64000803144207100b0400110844d00d80c1003d04008009148a0300080800b0541c00105039100b400000c806c0d2241208500030800c050540e824000c100c0c40700c0000900751042c0706814011800244081c00c01307902ca155003c241d10f490070015206942101c1c003c2403020052000500119002e0700c11031202036010300b04680c0c0d801c001b107694401002004d1060f0b110040125003041280d506400c0345024901a40c0d5111800380d2505 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 847032446 1250 847031196 847031201
    0x3130e010b1303150209100f02160e1519060305150f060304061116030309021804030f140421170a020d030b06040317030a0608160302061303081309050604 68
    0x10b801254103034500041000400e2400e1140018000100140c00d001c10300c0082208018140419030129101c80310404016604208200da90050030101200301864090303100c0b09075001400c2020300c4840e40b01c0c18080c9840d0250301800c03450440c90300500b1a5030390300c030003030041c681503d103c9011280e84600394142c0c90585545800220700600003451504d6980e06c0d90014542c8001a0b50000400d102e0b0000c609030000e401e00055000b0741340030600d1800c42c410018a0b08401e41650b011042410a20001c654880d54155692000d0f00b04082132010a590360b409038001d80e40b0002c14605000c2202d56000ca29020b00301d4268440c0a03990710140700840451000d00900f002c010040c2d10125003102014032030303000384c4ad0700d00020b80a9482c0907101d85544800445044450222030000014003044101600c580001098020060100000d05000b41c80c9100c5491001074842e20001c64000112020342030074400440c1d03c20201d551701c9007140c1520345505082d20600180502e010001681400e050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 847033696 1250 847032446 847032457
    0x504030c0501050702030c060c03120109050403050a1805130f1d061b04080d020109030206090d0c080f1306030501061805034602210709020a0201020c03130e010b 71
    0x38810300d00c0c49041400440d43d60f04511000d0740d052103003070400c00350761703d03010000c020050f000d1000e580d82d0140108404401101a40b200320024035103c104800301781d020058034a510164030f8400005a81010100c40300050b54110543c081070b401c50310310360307001943d205861880407440c0030320881d0900c01500c10b072000070081c18503050b008200000c0c440e03516040400c40c5000609903c608282c2c4503c181850148101018001f503075580700240c0a041d010031901c1d038000e5042c0001d018074407003007000600383c00f41d185000b0502031002c0781002c101000d03181640e0120a401c02c1e0000700c1c40c0d40e4440280904404c1c801ca1002c26001e0688021103041e845a102c10b480014005100c898100400e20a2148240c940307800640f41c0d010b030068490108001100c1e5885140d0742070188040306004100c2c1110b000031141600c00180007503c200c0c020003040001c112502d1440058075821107010070ba000e449410500b0341e42d4040094002d03408440ca07100b1005803111030710007860782c1c1e807107008081c1725200c0c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 847034946 1250 847033696 847033703
    0xc0a1b0f061e060b04081e0c0d02182a210c12011d0a2c07050a03150614060417100501170d030614040b0a0b070b0a0507050403 56
    0x100c10101c0c4041e04206004150464070300d40401c11000180d0896440707410040352000001010064444200849030502c07901c10350207070742c5a1321010215580c100045159008a464000c64001c1d543c82031a159000409040c80e00708614100c644a07010003401c41c60550200200740500e503652301e8080a80301d0003d490440d58194144200f0b0021032a60000c00d07000a120040044901c0710040781c0c0303824020081e21302103900840140d000f110a180c3c2c0103050304c05c510b140507803548074488004405c1241041010109a800c012403105c5810030441c0d42080f07030448c0c50004c000041001e443c2d4106d42d01201040200890f035101d40510400300c615040b4140c1c0001c00740f1041c065484c5130010414045501e1080341c104d644044900030079502c1c26403007545005855520505000c46c180f1400500003031514040100d14105004041110305035441c0c24002c41c0d1301d416a0446481c0d03c5140d502074411401515141c0d00c0a00c0c000710800d00844420b4400b0f810900800c1d2160302403010707103003500d50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 847036196 1250 847034946 847034963
    0xb070b250e0d0c0503010603080c1c080c03040c0306020c1f0603031e021006061e08040201210902090412091208030c0705031218070807030803060f180c0a1b 69
    0xc42400c00040429902c02601d088065800008180e40c09104c6d4100440c420080252034002482d0810f003001803500c10200703240c01d01d908000d02e02c1d900210082c0d20140b443c058035140d407924204210103c040342c1008080314400203c898030440c000803208020100c425550380b01d5200b0040d07030002c0d01e000b40b0008012034504050200303c00c0840c0001180c001d41441298450ba03031000445040c1c9240d40c1c0100d0202c2c0818503003035110004803000440c96a90760400b01c84074109640002c00c00c031007842040124101c510420140726105412500e00c00750000c10f515041d040505008206c0804c1440103804070303021500002e0b003052030f05154100240c201c0141401c55680c03168001090f4800302c000c035039038002005004000042c0b402424011040d28600041c000030500c0302514002840e00300d02031541c8031840401c00162880d046a43c00f041c141c03500c451340d0b4031400119000c02c014900311a1030300c82d00f00030020429010340140c2140081c51f80e40009181c503084414421011042c005080740c00d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 847037446 1250 847036196 847036217
    0x60519030204080c0609181014030303190b04020c0f240106050a0305040c050d0b060102070801110d1505130e0114010e060d0c0b21010503010b06040e100b070b25 71
    0x43c100e17024000b034100140151183e100c450048210603042110111101e50941c50700340324041d01c02d01c101c0d4410300140d00941c07650503d01400001c0e0083c444145580d141c40701c01c845415240d6405a5000302c0c542c2c4c04452042c003600c141e1546401c4c1c896246014030341e410080f410b0060385501200d04807841d6446551130700e845103d0032000340c14000c0054404180304c160000d907a03180d0000c0708042c18020084501141864000207084c041c480c1e10105c66a03040207100391540c444181260020801220001080940300104844503c800d43c40f20790701c142140000e40102c40b264001841c0441281c008200d40c1203010700809030131310207024000d50210a1000607610342001e007a426003903801040f44a10065480c1340e0300807561300c01403d240140720701071041c0705180e078515a00c6014180c110300030b0002c0c8241c0750115610b070185214030799903400440041150030b0400f903001c402400100842e103980b460182484a03c0400a0300c0356030200030030081c6003a140641036045500c44001384c0d5501540c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 847038696 1250 847037446 847037449
    0x7061205040c0522050c042601110c0d0e030114060103090f050d020f0f0c0607081c0606050406020f28030e1009032102070303050c0a02030106060519030204080c 71
    0x10030008208459001d8269804103203541e030010342019140c040c070b10307440842000190040503942d018040c1c03d068a01803006000c01124480c5034241199032000003590382e0b5040c000d8030f015000c59024051461400103406d0036480700452110619050340d110001c20303d100c8002e040c00c903010580c811800c009000c010030705039842500079180d4940034a505010009050301c441d170070141c00d03410301005a400040030008400d01442003480c1d66041101a1207600b199002161b060f200f8508010f080400c001880100f0074003040c910070882443c0c0ea010010544c0f51007016109603c140100d00140c030400c00100312540e0000f640c03c40805a085545011021540c0c0c8099281e403d0f960441c1481911a00740e141b41e120b1400101c41c16219a42d54441e9500d94101161603164410402428501c20300300d1741d40603500041c089048962620b045940c8100040c025414200f19560080d815424207000051140e03002c80a03050342c503000c4030104c44440d2500800d5003244600e03c5441000c1c0c1250b1280c045a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 847039946 1250 847038696 847038701
    0xa170c150108011e1109060c1501080a0b0f130809060f030c031605040308090f01110f061005100905042d09060c0c1e0305090301060f1403070612 64
    0x11011400444201454061a040d0a820300340c000c25450780d0340304000c4580051400e84880107200ea0344d0204032082140d42e4055040c0f0076161410302400d00080c0c0100003800411010341c3d46041c56982125a5840c0c5818544070a2079100507244c0d1000b03900406d0764100200001130203107039001e207081400d42c0d0607541c0d0100760304144000b503840001030108034a007030401f0004612a40c00620400c1e81d030b10b401e00d0484180c04110040f503003001418401800007410800840e001d003d4116402c00000c1905d4004a4000d0308641541e07050b8001c2400000140c100010f0150117078a02c8513000d00b40a407907100f401180400d2032a10800179070f50300800c010608250748000c194244c20110700b4101465101d0841d1004c528070a20300f8956640d401010a108541c40f450007082c2c4145440d40046803a030300d8001461001e14845403200340ca00d80944100340c0120201d50248202070024080e4950350712002a910010344510b429032074400020180071310700852820709842c031607180d0031f8200d8815444c01c1c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 847041196 1250 847039946 847039957
    0x50a1d01050d020f0304050106120c14030c060a0305071d010e120f0607051305180103082809050405012112020a1a07020114100501031806060905010608090a17 70
    0x51020400102d078820007039000615078002140c4145969060074902542110102e60001c424500040c51102c00642e007514644201c404203241901c41c3c01340600043e0601c01d800720440c3e80001c001070100082c40c0c05401091040285450304c0040c8080f2490b02c00302d070800750b40c4050002d40f2030a80d00910b8904070a0b840c1d40d8034411011603102c0d034242c0190a00e0301100b9981e010219130040b41290300c8072032800c11240a040300362000c84a8610100c04500c2c00e103011301006160a60125003081c0003810b01007943c00280182040f00503c880c1508090010107050113507034012030403d80085400003541b4400d0509584211f032107042004503481d01484103d003034402c9805c5001d440d11600100d0300d070080072110580c2c440501c040c1410f16200103800c407050610312814007a050020002c5c2007080c000e0707a4048a40c2802d01080c0f20300c18854901c0d01c08a8a94020241d501c2d122012464110592000f81030360309540382c0f038445442d5141465500e40e0b2900380100100d070582c001c800908114409001c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 847042446 1250 847041196 847041199
    0x30e0f100f03020910051c0b210a02030a20010e13090203070803030109020d0612200102030f0d0203040209010b030c0711010c0209091b0a050315130b04060c020d050a1d 74
    0x608041085000481d818170f45115803000540205210402d1280c400501c40e8403094180c0c20840d03107100802080504001c003c240c043c2000310300c4400802d0f00c06120b0062183e034010700b42e0329000240c2c54402c00b000d060748586440420540ea03005a1540070b00303003001c0c59000081a1403101101c040c43c1c0000f03400c0300c0f1800c070b0b01401303101c00015090074108040c602a00c9802005610f400070071640908452003507104207051441c0d44802030100315204c00c024050318610120303035811022070300141e1851080d10301d500c119250004520710f482c00a0b6024500441c8201c07140080c6036602c4004080d2800161146d10403400100a0100062020040b440300d0303880c181840c0c420703039100d50006a103544044428452a0304a0400e0b001a04a0203e0b0714600c40422103a4118007400c14020139134900c12540c9144800303460102007054030441112202105a0054084555161507e8a40c0140460490031400341c0710381030341800c0150043c016074440c0203145d07075003040c80315000c2c4c41101e8003d450340c00b80703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 847043696 1250 847042446 847042451
    0x60903060b0f1002330403180b0d021201060212180f0409080702040c110723033003010312081503030d090b090105070203091908060103030903030e0f100f03 69
    0x1240359480740042101d01564039000307840100ca40840c4181000c0581490005e1a50309a560b04030f840304c4280190341041d003514050010110000c3c0104401c6a1904100030107440410394520303203c8507070000d01600c4101c001400c5280d0341e810050b40e07113807048142c05416400c18404943d0003040e0a45148041000911540c8410791b20408201102c8020b0710a0303610160016011703003035003001d000f042c05c2c0c0d404c0d0340307001b074540350300c885495403684242d000d031603c481c00000c1204140300c00c0c0846164142d6006050344d4803048a001e1842d0300702c160000549a07020b281e042403200c04501000d80703048a030400c0f0181d40794880d025040301c160b400103001c0360820001c00050f00c0c05807810400b400b00d40c8450301000070348070464204400c40b428000c0554200784c0c1070001700074010390b020041c0c800514003513a001114004000c2c42c9525240c1c80d03040904684504070002041c1a0700c00c00d0042128080c1d11981308031054001805401c01c40c62035240c0d00719a410040070811449808905040c07505803400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 847044946 1250 847043696 847043719
    0x8070303021303150e0c0303190c02060d06061202040803070b040615080c010e1914011e02010b01110a2001050706060b0403060b12121c0e06041704060903060b 70
    0x11250020310b0394005035203d41001100f01010b105610640300b0400c014001007030a5107165000941c3c1e0b202e04c0001500d9070f01c0c041c2201c20010302400c8903030000c81c0e0007000a610b503040b244c031210003851503204440004455003040d00305c03c210b910072281610060000f452070f001d46511101198070001e0403c95107169641300c82c8111250801070440076010100190808080120006000d41000c00800e442000c0211800c100b0b11888505103085076400b081d00203a500ca054010f843c102c1841c44a07403203014240c5480704446506510002c0020400d807a05d03004807041d13140703590361b5130000a80101030b202d0500540e4464520585414220001454600e00d40b404660f11113081c1c941e90360041c4540c4001040500400c00702e4010321816a409881100d0f204100700c28840c0d0b50403042d1100c000e20b140c0040c09070601c1030303081c80d5180944030504061041d0110005419030340c68003190181e5008034801c881c8a45001e40e0811a000c48001d0780d11018464196180c0c20020140b11034400d03401283c1001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 847046196 1250 847044946 847044967
    0x6020a0e0907030b0a09021213050a1205070516030b150301060f030809090106050f1b0a0b0708090609070f0e06030a060c081803090604090c0c0204051801140c070807030302 76
    0x1c0e00748280059030300400c240300648140a0703007020540000709036500600c2812a21207886100035802030307800d0f41030118800c01e4100035081c0058010090300f680129642400c140390020000c2036450710403030454203020221283d2100300e0b5580e0100420180b2800701040156000042d000e580450040001981a5a81d4011070b0381c5d070082d5004a03072030b110109020b0b08521f44400c10398014040c5044c032503d82020301c041840786114040440100c00341821403007520307581c100300701c0d0010741d4441280c0300c00f03003420b1002801c1000e003201d80b081d00d0720880d8002801d01c040031500f441216801d960300d0030540d0801c02c8065206400501c415003510031038682901150b0300e8020004103800340e0712034103594107058521100d0b003c10110b0b080019801002003c7d625140e900440d030854998100000d42b5280e21401191210720350000a0f52003820305051004600d103041c40040016040da008108180b040014103c07000c07011221000c0f13030741090018002141d5414001c1080b64428070b80145002000c0ca0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 847047446 1250 847046196 847046209
    0x8040206130503061e0a02030403020a0f110d060b09130507060e030a0f0b071101090b1302010c050f0f0c040605030d0c0503040b0a201504021309200103050105150706020a0e 76
    0x540d5040741c2c1c180021088142800c4441180e0001b112141c1589149410f440281da0780e451000018011a00445a00c2c14007084119100f2030301c0c1d004080680110003030600d074002e02490650fa038030840c3c82030082089081d1445880000d90361000280c50001e2078000145d0740300810044054250050b9080e40000442d24070203100e05604c20305503401c590410300002071901d4046100e10409a1420250030046000342040f16480000910708078a40501c1e440100c901d622500c900802605c0303641965040180d01207003081d181d9080b8021200140403801c00c1200340c0c1c12600c10190140c0003600340c021150f1103180700d2109540580101c902c2c20340d4070034144441c0c1c0d02c45058440050750307010051240c071110140c2e05050822039801440e516041c1e00c400c454035080500024400c81c078143c0c50820f882029045140c4036604120607440020703100d44040418800040c0103400245010008129441d100b06190340181195170010f09061555a030003000390300c0f40c1c03081c3c1c040c03017000918480d4564500303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 847048696 1250 847047446 847047451
    0xf040b07020f0f071a0307080115050c191509020612070c05030a0801050901050904030f0c2906040501170d0804032015010e070c060914010213081005070804020613050306 75
    0x4e00c1c051707182942421132161100b8521040c07036410014031481c2030b4007243e040c1c150360704220b60b2200007140c5801030b01c261083d6684003540f809501100d254192591b51851565800382c204d442c0359110b015015400c070b41000300004d5109209000604036100300d1201550300007414204070790f4690454540360310359008144005c001a600e0f50041c005803c00b06c1d106401410306981c242402d0401341c1d005462a08800e01d25020015580c503440f0038402e00380c80b0305499030080581c0811030b01074a000030b840d80a040b00e906005506040000540302c00c2d01c00000d05545070341c0050b11141d00207103400c548003030380230340203800f001440c12503d11200340c20f002c0e0510010404005140b0050813210700b2002610590140e41c01d0300d04201008509500304140200c00c560203070000410024600e40030284150300700444405610100341440c40c00d500008440c141c0d16842c5c100d40d503210b4142020380c16150704540220008004002103801400d2500203440f805524100303031411251140c02103480c1407002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 847049946 1250 847048696 847048723
    0x60a0302150a020c010311030f07090302061306270b0a0e031504060b0d1101050a051228020f07140a12270e06010c0c0801050412170f040b07020f 64
    0x7400b54452501001900540701d004c0c2000e0180072010040c541d8a400b0081ca480303418148900019030091044900c030002d0b590080c1400e0b1a105414030184540ca070900490380894030300749070006402c01c0ca81b101c16201c25a0781c5d4111680382030091030030841c0c0144890506111810f800b00c6141ea0b4244002030b08a249002d03002c94a01d0941000c1c2c095882032020726001d5030120a603000400c9070410007003c00803007030038000d958116468040b5000c0c4a248181d02d003002d040028004042141c801062203040034400307008514005001c0d020491049820503c51100104000400520f8200300c001440f0150006e5428113003107602d6603448600a40c400100095041180305d40c1140816601d0340e12410a20440004900707108010049034405005079043c01104100c0f00104100c1036000b0300034101c1e00000b8003007400c3c42c0c54009007800c2540160340c04180314144070011044000f01040c80344290b04c2c28030240d87c907251604031022501a007004114014101f0712080701e0420000e400c00e0000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 847051196 1250 847049946 847049989
    0xa140102090906011e0f050c070e04050606090c091e100806091509271204061d100e010e0a030c05040b18191407050d0e01020c15060a0302 61
    0x8280040120040008000d0f50504c40300190040e0b041c09030003100710134482e2500f412841a0046101600c4038003078281c04141b0342c411220301146034840304408500881c807642c11192540c480008000c0b182d80b0031030346842c0204c4280064003c07441c001c11080380d445c2e842d40e2464081e0741d60601040300f0500c0101e06d500071901040034080705091841c0420b03444201c2c490413448460300305000440004025005800400f0900e0b14455020b01008584001c2c814010481d092018030511130b1440c0e070800c0c0704400c081204030701e040100d6142c508050841a80051403a040d5500100d001d0b580c1d01708100c0300c0c604112220920b044152544141e04000d94060071204602c3c6181a04000981d804400302ca4014807000d00602060a90700c0042d40c0c0060b243c840c130100c4443d00a000400401c0784042503201520340718140a101d82e0408000e240e00e00000390b0511035131107020b59a42c03e0380321700544c1c2c0540b0340c441c51506170224510604190030060041015068690326000a40c3d030240b5804003002c25403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 847052446 1250 847051196 847051207
    0xb130b180706030e0a08030c0d0603050d020d0f0f0f02120d0f180b04030815060304030c0b09062a090916080f07090909020619050306030106082d0a140102 68
    0x58104555002440b0501d07090041506400840e916150442c500505114022000c118181c1034482a40c8091070016800c001c0103540c0c0c280140d50740409410100580142c1d100712000c144031b012103e2180c1e400340c4540107952003403401114803800c950118030450065120044000010034001c05854103072620201d11124104010812200c00c0c10900001001c0e1410850010b07040c642a02e9001d90581070404149c0e440e0815000182d690305a00b60b403020001082004240e0400904968135025000303002c52541e489500310b560b20003d40f01c1183c0c1000c41c151544000b20051020f80c0c4285055094500308005203020450a0006407000425402c180700107110241d4032030a11a8021640605204c00b4101540301801e141124010f00d041240c5585440c025034540104890bc00c55100b200c1d2552808850340060454100b550454420750030803e0002c1e000e540003401c03080540d03c0003080341024100d61080e5950000688074400070307006101c07205021461210301881218203101c00569910b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 847053696 1250 847052446 847052491
    0xa0c03050c1302040e1621200702010c06020a030f0e0601051206100603020f040308030403180b07020102030f0a0207050d0c06030b0411190e220506060c0a0b130b 71
    0x42c440e0740800311881444108481d0f4402000300c0e8000c0703644000304070171150b280001c50f00c10807900c804900b01c12402420614034050781c0d0000e034a83c8034003801d1000c0c1000d40c041d8400a889100c034082d0004404100d14000b06107940e000b01000001800c0003d80030188103840020b42e0b0b580440d4074a282c20020040120b41440001ca00c110b400e40c00203000c480c940345401d6448805c8901074003080550100d10303071500e1a144000c98018541060a0303039102d03e06490000c00c41d0b51780e01c000a25105100c1c5001444a0b00041640c083c40e0f816005507040980901e030003451074002480000461040c840d001038162140404c0c1071005c0c0c0507034580e40c3d50710b090000150540341c031142010300403441c0c0080040b40c1e8102100355482086410003c0000361041074044800e8880e0380302e1241c0c000c1030400c6850001e9a001c004240325511500b00340071680d2803030100301c001d00a60191070955040f00002d40c0004800181c56644a01d024610185668094079041800b881c12102c0c403800c0c0c2001440c11222 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 847054946 1250 847053696 847053709
    0xc0318050c030f010207170a09090e06090c0a0b12150a060c0524062707030b0109290313050d0e0910440c09011d0c0c0a0c03050c 57
    0x4a00c02002035181206d10b5803120910024010281001c40d00443c0744090580305442000041c42484400e0001c0c4042c0d0f18400d440742c07000c0e510198148981503a8140301c1c1080005c14040340c0c59034001a0400c0c0f0003c000c841421001083c4c84007460b080e0409080c160b4482403400301400541e607070070340c1035051881c2681c41e0600749510113400303042204868a00780c42400496a20200680d28124102040000c80407a41007800c144075151613040d041115090741680310b880e054400342c2e100c04a69658080d040400c04012040c02100d049c04080090446042001550040d07035500382c1c0100d504450300c03228140661074095000041000411800c00d103040c404c0796800030840c25103040614507040301034422502e03414400d07840d804824200c2240e6110000b400104d01441889144080d500414180d00c40100900b007522a4580c0ca0021424110f000307011051000c030016005600e44510068410a030030200074072141e44512102d40000804065103000214880c41c02450f00300f4049040010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 847056196 1250 847054946 847054963
    0x10b09012312130b0115030f050f0613060b1803070806010f14060a0c0312180605010303030606080705090d06110d050117010c0c020d020303040b1306020607050a0f030c0318050c03 79
    0x2e9075072120107a000404c10a5800c581101e5008890400b1443c22141c158042c004c80014000c0a52401081111802c003200000703100d46021200440601a0314400c10102d50344c602500c4504913003484583c0346407100005446a05000400711080140d031204000e05d424000d0300071600e501e05c241400c0000c01c0000405031001c0030b00301c68950420b000d0304001001c00c040e184d80030302004210002d1002001c001c0c0d1103c0c0c1c42c07000003085400038008504148000d410207100440000b80740000006030740d4807c025a40c0640700595940b4a8107a5200030020740d40c50200c070580d04103a40c1d0305440c41069040c00146802101c02e90f000ca2650324185070b0400450742104540f04907410512000e001d80c0c1e101d50b09500310741c0d0443d010400810700d400842d1440c081c0343c104203401080002c8505408084800d4002112815802c490071079840100c00c481900034405401c1c0070075680c03255a41e0107406500075811014035842d00082114040c15000041001820300360b40d0f5400004580369541414000d415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 847057446 1250 847056196 847056211
    0x7020f101a042f0d141f03030f120624030c0905180406020c0f1e03040b030f090f0d050a170411121005011d0a090506010b09012312 58
    0xa8411400148908200c00341c1c01810f4150350306509500c80c0e40f4640a803203032245018400c020040f000c085034a0204829102d180c8003142141d94000c1c42c00b80a01200240d0b681b603626402341100783c0f0410390f040500e41d2100d03107229032101e0002c101301c10300c141031501015405c1c081d080c00c0e1200e80e8018040b101c00483d040200000b0380e00c180580d032203080d000150401d40816903149682d807420410000d010342c000d1440240214215800d0803c00040c00019100780108503038078804406d6042d43d9248a248151314010400b4000614012a1007502e50791000c11102914020303950080380c1030500200610302d0300402c0000c6403524015501c00307a1400c45202c800c0001a160810b07450f40052405c042d10300521400c44c4100c50009503e0900050b99084107505042c020343d40c46004560701c050407008000b95120015001821100c02c0d03000350340c185034105000e420241d08010440c04140d000800881c1800380440c00e6070400302011030350f00c480c0d000d2545038a4072003541a000c030001c2540585200b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 847058696 1250 847057446 847057451
    0xb0f010608061203070c030c0f0b1809150a06080a0c080411040e03040f1d060103090b04060506030a140102180102122215030903020606010c0302060f07020f101a04 72
    0x5115050704521890b400480495000c0c400300d83c000005861441214002410001c4104001081180e0440311340203490240d00722141182d11a40b41e44240e0040b99042d41801c49201c0a043c030b503040489849030029241200003003851141c8011a410f040650300c03040c0060b000c001005000e0b000c92145019609075440c1800741400c003922151242d03120302102a20503070b0303512081618240d042003114000c000030440c40e803040b9915060003540200b00070b40c00c08500b40c840c000840381d6100c2d120f1480101d07405040301072152510f4913820001e21006200a405208254121000c9000b0184070b10034860117000244c1e82c1c044c1700320000c42210220040b82e05560015091011280d91502950b02c40b611071364407140401d6801402041d4000b0f40d0380b00c01103615440743c098004907403541014060350b002c1c2c0c003150300760345802d40111404112400c02038010b07044a00031800c80b1a200a1030b0341c012441e0710484500c00072007031030981070108008a04000d039603111418007410b0001400301c2c90550045404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 847059946 1250 847058696 847058699
    0x30306081207060c111e12030f15030102091207051002060603070603151a1e0f0403200a1707060203130e04020310050a0f11040b0f031009090b040b0f01 67
    0x201e203a03001d0340360000c11240d210b100d40d0540303070710405520140b2035400d000c81d5000c1c05030900c2d1080094814210f507001d4054070026508071424002102d010310340a10010166607108034200034038210a12040da81035400300304200c8030b0b13a01e505000002040c0f05010340b80b11407030001008a40083c0c0e81400c000d5401001c10088075650102e110000c50306c0b00d050106034044041c24900c920300d143d80110382d44101c22048130459040311400342a03150345005d508203071000c56020300041400380080904203900c08200c21300005100b084004c0b652104081c2c1c815980c5891000600180c0c4c10341c00035092800480d400c800d50356800c01418006001c540061440c04081101500684586018002800c156440840d045460401002c1c0020000c440d040100e130400d400d01034003501414007140702031420000819240f0b811402250f084681c4880030b1881d01c81040001401038000070100f000d00148940d000500441c14068400000c1c801c0c0c060590741e1a091500590aa001400c68006126030800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 847061196 1250 847059946 847059973
    0x509090d05091306030c030c031b0b09040e03040902030405010b031b031c1e030c0306061b0b062407022d1903081c0c080910021b01051303030608 64
    0x8071a40003105540710a0140345820009014040d20f43c8020410110070000000f070007122300c10721098900c246018403966840b0200c540481019000781c0b5400c14040207000380310300e000e903c01000110000192820950384081c900100d80080b1002c1c0d07016511070384807403603a14040c890f140d40c0d0507001e10f0307208074100d40303c0110703641d0511009070301c0c2c41c20504090400d6080c0240442c030701704150712011212007104000d0050240c2041d00391100864105040400c1f21405911700b82044102100b880c0c2003140ca0352200e0f002e010000d090b240d00003143c0d15040c10810b4400100d0f1904400d00e588442d40ca10b4140306110005d1086a001081c0c0c485004549042e60041804011038400c111340061006503d9041d4a502d1480b03640300a00501c4002510071208051071a082604804040b00300f00a10315944143d49480c0e0071036000040340c01500144906021940c090285626125500051a151440b255084540580d800460036a850303000404050341801240b0103015181c1c040c10039003a4411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 847062446 1250 847061196 847061207
    0x506030421030b0402031006080c043827041a01080403023307091a0f09090a0b090901110708030604180b0a0f0c0c020f040912090509090d 61
    0xc0a030502040c552100c1940389209412614a8080091017156030b0b040110400950400b580301c0c5c4004035604100048070071446034151000c4a00800d1450341d150711030311113076106c1c10301c1010140150510003120700100b80d0b060301410f1590310200003100c2028034401080a0500315070546882641480300140c03602003001c0008c0f1241380c01303007010b0085464600c0d00fa405e180d885501107040624040d0300f1700c5800f44182d005001c8185903005040c460f156243c040340c0800d083d0145c9003402c210701e92141c40b00b240000c002c1c00001e200444850410300040c0000309032250503508e07a0501901d0350465016480c005461940044040e0020004030a841d4400f0450307004c1d03400003801d040004000a0320340d0b00c0b903400240d072102d007000b150f80b15222240f82c0f19800d0302d0141c502a07151494010002500d00a5210310504142036890b0401c115040b5030800548040f000000342d0802c0d00c40004500040030702880c206d02c1c441c0354641181003030070141030014a01c1e000740180e00a5200440c04061541c110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 847063696 1250 847062446 847062473
    0xd02010e04021c020d02040f0506181507150203090607020c032e0905060916030c05090a150801021b06160323130b15090711072105060105060304 64
    0x19100541c84040391080440c14501c500300c2c0f00380303e03400000d030180310182030342c010800c1c2c800b06038140c000d803034440080c400c441c0121800c0120740001c10340208800e140c54085008002c10411070f89240c003069548259140e40000c114559494000c03003030003144181031181960204480c8000e084050702c01d0b0000c0d40d500704d5401c00c041c5008201072080d001440c0c600102c002140c070502c06102646462900c282d4404080700c03440490700a1a091034000c403101c02c001400c0765001800d621480e418181084040c0f000075101205080d55054400d00c0d061030900d21500500000000588520750103041c00e040002091103110345400c04403c2000c00200c6802c0102c0380d001c1403a000908030b4024845494400003910b55800e032620f82c03000c01c000500c038202c80780645841a4a4004c0640f10443c60402002c0495012680a0881000201014400c940102d40c07a0a0781e0201e606440e80d51a020301041c80459420706402c1030343e4038039003c0c0041005414018001599507034a540391548640303107500101c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 847064946 1250 847063696 847063699
    0x605090d03030c09120f020f0a1203081e090106051521040303060e0103050c1504030b0f0403031508150106020d020a06110712030b0f03120a05070f05060f04030e0d02010e 75
    0x3d07452190b05491160183c240a4021415141ca08092900746000f120306000001c9225064a81000030f09041c4952128101c0d8404418240001c0719598196035440c40280180c00320340b88140526407409208180c40d014a08543c00011100c0c109000d00188459122003144500f00800003484056120078244a403050240080c0115131030700d140442c058804c43e030001c2c2c403041a010012062000204030103e04031005c8846807980c154000000b412801a448058044620040060143d441e45900381d17610a201780b0300020707000d003e80090348200404d0b8101070200c0c0e12808020b14092103200700b0a014104600091201034081c41c0000e56480c03000000800d00e1707844800310100c4070403c00c01d4480b8140d000020305030300d02407400010b004110000f001c07846030741c094408a11030305010035072400e002d0000201514190b0056401d8485900860f01101c40e41240c500000c003180d070511041c3d010700984203072840282424100242100c0c8801c030001e100f90101000e04d80141c1c0c00c0b5000c1081c8440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 847066196 1250 847064946 847064951
    0xf160509120f03360a09050a0b0312040e060306090616021501060c03020c04090b13020a09064a070e030109050c040f020906030c03060a090c090f0605090d0303 70
    0x9032000c0882c01e0811003030715500140b0000c51402042046042440c2400c04584540148031034565802c4a2030440d900c1c1007a003102203400140304651458020325030048505101003414118000400d10300021885603074803800d0042414415109980008c2c0d41100c2c048006040da400e21810302c07501c4040251020908007850503013020010b00074080d42e6080c81d400102c05090b503a440d00c000e00b205481d035400701c0c01406400702d140c2e032520781031041600c160303009425014940d84407102411285c0c8500c5060340d000c10450b90000b06d050850281d500540315500d000b0400d01040c549200c5080b21250700501811200c88048030007003038007050740307050024402c01c54460f40c0381c1113401c6c0c0c0c5610f0002c601c0c940550900e520442441000150f14001030802d41e42000461120b8401d0303412405030100b541e42c0000d00300040f99400c0345400c003440c0c11440041240d8810780e9100c03e0711003146c14002801c804201501420041c0c21901c501010017020182041032412500800050725640b0707096004045c5903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 847067446 1250 847066196 847066219
    0x7030504030c0503030921072006090d05010f06290d020435070b030a0f020f161e0b0a053d060207050303070303051b040e0f160509 58
    0x10b00c5500001c40c0b1941040607a640d908001240c551505090920031032403e006d181482080e45040d421078401503080348640705a582c0c0c2d1130701d4116420304001c203140c1c007040c00d001b0520155034809040414a10a000010f0078074144c08654042d109240d01070b404010100100248248d0300701b00b076100100c42d44e200c007035840030b0400003d0001d0040d60800180e18148102c088840d00c1c98000c3c00644040440b0800209007034a0b103216542c0c00c05008080c010941803020030004038a0b0b800000900180410160800f100b200224040350030160501c541503414458101c00e00144001305100714032311400120b603800c4140c9a4140c0c150b00941020301581d0b59400140c3c04429844054411002484036179041c0c1e145070740d8440c00c07005410b038600600061014005010340c0000780c20b90485001401560a180030b90700c00344c0040c080100052030f20000901d4040051119a0080016151071450050701c1d04010b90b000d00045d10080080c403102d00c84a803500e60007500b040540c0d009034002c071086050711 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 847068696 1250 847067446 847067453
    0x90e070503012322080309031c020a0e01200d0c031107060e090a0e030f0c01240501050705030c1006060813201c0506091902010c11010513060f021207080307030504 72
    0x401c04c8220140c0501004000d01a84e404080f005222100c9a12484c00c10907903001800340491107862106004181045240c120f9940151004403500a41840344c500540c0d920901c181800c000b40501e400140b0140600e008240c2c000340f0300b0100c0440383c0d000b001c0040c01c0c11005090515040c4096104091100000d03030f072101680c02c02200c01d0301540135a0380f035107000c000c02d59140c0c20040c9880411350070401310a032188103140c52815880000101c0d603480c01c1c6000010740d00c951201405580d140010030002600d56070401c140d1515404a6000041080c07500d00c0040a4440140c0701803080250080c4c05800704140fa91004040c1d8850074000002c000304200040344203a84007112000030380358400e82001e0000201d49940f02d000c0541c20350740d20303410203103001d0000450040c00a000c20005205c40012800d0061080d007c004181061403821503044542c0e1100e0304250310200000f81d8803164031040c40d13818415035070340d144d0ba503003a10b0610100e541d9000f00c5010003822282050740d510001410b2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 847069946 1250 847068696 847068751
    0x12011b0302031510030c110f060610120915050c1e0d020d0501120b280b0f030a14100b0618210a0c1203020a03080c04090e0705030123 59
    0x2e064010302510b81400b400710054091b0041d02010b4022030344c075614070252010049980019469501c01a0140b0707036070784080040141d101d5201d40b007006503030208884080d50921904c04040d001f03950240011455000760030aa0340c00401613000010b042c000d42b51400c01051140d400c1820704104d0325106c0c3c0c0c050740c410009004d14030151000d5810100001900110000d0032160140a070703615228560b00c69002441150250115409000e68901c2c119018140e66122000558000f8180080a400000041d1030030302c03145410345024a5500b07110002400411801c007400041070814030482ea044330008403207020304088100d212240e8040d00005a95500e51701e200b1050710501581c20180d42c0c2d5041e07a981e07500010031148410324002c042480c0015a04001c02240d05070700500302500583d4084400701c4024119110b06202403102150074085030095a030441c070391100800406107800109829554030500d51007001c4207085090390340300740300c0318540d40c440c040342130001081018000e07003101c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 847071196 1250 847069946 847069981
    0x91e1f0522150203090a0e09070314100605090112030815060f180103020306091f0b19020c1915050702031207030e0f030d0f030213030302070512011b030203 69
    0x1111041d880078121400150112000c0c0c4503024008455500445000d0340d6034031550300c07129804400f4403030402485052100c82c076407116404041c0c03107019640380e80d03110610103441c4454500ba040301c00720083c0c1d480103115500041c181203400007015494100076040c44880050b0103810007400000242080c0030460400e185800054111951569100c005903006d0300881030501228614030094a42ca621a000341c038001c0d00010440c0040d40c407820042d8035400c1c0740d80c407951070171841c0080000d085103008024102c8070350081421003940c1c411843c0281050070341100b0920038103914a5280b00d03030000b9008101900d07035006202c07000140c0b10300d0540381d5000e180c50096142c403442c400000383c42410390203800480d1294030349012604a060400444071126114aa01036000104040b40030384600c05000c030b0808141401450a4920441004c8100c4550816409a480b001c0208401e08025003d9018540100001c021035440000300d800c1c0d4017081e0301c10b0010160040085540b02c000c4030800603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 847072446 1250 847071196 847071217
    0x28110c060103080403120f050301230a180b06041508090f1603140109050d03050606071406040b0615160215030906010603180c0b0d11040b091e1f05 65
    0x2041507a40e883c1001860380300e40003c440c012140400b90604c5e500461030504c030701b42151501429030b820a03220218180320308a11f04010024a5100d03500b5072a02400007002e41107402c40b1181074000b07500d042d010b0310381c0107046c1030251104000800c046040d441031640942500c2c0782440464540c0c900403843c00b184061a00302a02034070000c40c003064400300352501100e114060100000c510a0301d406e00300c404149020303120350800200d00c8d0f2414443da10051344404018403143c03c20351a031b140c16404410680d01a40c0c158010428801070040181240d43d00c5001210240d603114601000c0107024010241c211804010304d14030441190385035058070794102c01c685c5982c1d071039141032071031280da4210031f101d5103000c20b04e4803814400c0c5504040d1002c3c002078005d078960085510b0401400e0340c030b0707115020b40207105a0341c55603444541c0a102c0100000c00c0d0600c22030762a04850402c0120400440c034840e40b60207038010580850b80c445010360b6103010004041001850381111058402c0d108098440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 847073696 1250 847072446 847072453
    0x20f1506041d240c120702120a0c440409050a1d0303062103040f030b101409010311030c030d02010c1e0e06030703060312080f28110c 59
    0x410000c9400990f0311480602080b100406a90b02010300350300c008191482c4004200400c02c0b4103208207020551a0484050710403540d01c02000418540582c100c1172900c800a40503901000038004844600c55421207103619a8100c03d81c40e88091000180501c0c0c803222092001030b021840403080000c0e1401000404010f00591400c10344c0c07103008005442034131101468446091b901440b00105580c0310700400b1300308003820000012101d90071207c1001d640c1d01880308000103d00c8800d14400360000318410804c881c16824008000b041601080e0030608600c04030503507000d80c0d0303a07403000d52a044031b8014030140030a0540c0e002107814102110700180c1c140c8180351014201a0703056000088201580e40e401207200c50031040b29403852101c0c034040000495540e4900700500e03146000390340007021400c00180c801e681c0d590300440804031040078408549190208030120544c0412150300c031a14420a2044030003007030b40100b50780741d0510841130055560b040c0780a048181c401326000b030342000088 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 847074946 1250 847073696 847073741
    0x40e0a020a02072c010303030f1b0806040b212404020109090207060f0e07060e060304020d02040c0c05060c0306040c0e03060a1d07230319260a0f0f020f150604 70
    0x1e07000d00b210070315202c0150301d000070703101c0c080205042e40942c230ad0303141e550481107441e85400c100240c4641e201055000c0310714540350744c0c10701d10940318818040300c240151000070107909103a1030b50a090b85554225010b10741c1000b0041c1ea000c1906e10035109070200060301c501150030002c005010110420420074035180f50b504c4d81000010325941103c04a0f80c60441080c0000d0a1000078042aa0000e4100007960202401031510307800402160480c2d1038050b800420300c2d101c1c6490308405542e103443c0000b00009001413402e19010312224080701b0704000380041d207180c000c00c0e540c1100074603d800701541d90214240d074044800c404000754142c05c049808454407038960303105c00c4104010104050030135410310040c1d4200412010480061400c48030082c8d01c1c96159403007204c0341c040e01c101d1190508844603034100030450140401c0e410a59980c4044240c00c50054220010180200150350086001928030480041c010000103440705040c29542c5500e40820043e20340e043d1444500c3c10315420f07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 847076196 1250 847074946 847074953
    0x303070302010b0f0301060f0506090f09131b051320040608090105060a0806070509130903031a013e03040803131a070605100f0803040e0a020a02072c0103 68
    0x10000030050b04030340c4c240c11034000004050032141c1c1881582c0d00021046c6041200c0c2c500b8901070704200342c002d40b118032130703007081c400060000f138044511510501c0c02d6042c500038801207100d40d0305418400940c40700c0d202d00340b1000174030b6210100f000e04100c0f0b480f060740400401d600000b1358900354440c001c09840b075031034035030283c0000d0085413400804d41c600000180300d450300019500803201c655000e41603d03240c20b103003112261b01000390141c0040100003980c920400360700c00c18000034040e40c2c00148041340f00391504a0380c10400b05445c104450803d82d0202c034600200e841c0341c410001d52941e4150b040e4034881221101600788800c1d0a0300010500180c00c43c400b0006040c400446059201032a03150100303060742c0350300312a000003100d40c280064800980745911a030707000100a41c0e81498241e450341445100340c09508000d030207401c04101041451640d1101503000102c0c02410760500030801002540d5111900c51081495001c0c0001c40e4032071560010070b43c0c9040c4051804a4a45c0c407810b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 847077446 1250 847076196 847076201
    0xe0106170a140901020c0c0301050103110907030b090a0b010e04110316020a08030f160507030e062206030204090c0207153510050108070c0303020d0e030304050c03061e0a1109030307030201 83
    0x101a401c01d80100401f1415600d81842854182d0364088440e50741c90343c040d014800302c002c0c014041c405155480512b04480c1da20740740d0140c8141404400821403500c140001000c000e03a88555901890418802c5140c031621281500c2d802110f005070000e03540d203080422458202c4080001d424402c000017400980c010191400d4441c040e01c44400300c016210300b03c2110584984007014000890840c00880c49190810040501040200e4580d2098207240c003808030310749055000e400400c1d8001001c001030703041401041c020501900181c2455864042000900380300c45040e0300410481c0d05a1a041c1010040001280740c111151400c28030850704c050004124240c0b103203403400020750300000302907124400c820300c00c4101e66215036800006580503006074221029501c6460f49800503502541010006107100754050002040700000603824981010800f4040e86c00360303031600000307c01540006240e2070700440c0c45034002404100c070703a9100500380036501d801c0c0d60501000940d90141907054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 847078696 1250 847077446 847077457
    0x150203010806010602060f0f0a0f1d06010f030503070b040f120201061e03030f200307030512010e0f040b0c091512092806021306080f010e0106170a14090102 69
    0x1074126405a42c80701402d81c1d40c2c840071210044038501a400044032640c09500540d008400385c400421403412900c20070b800d0391002030b40305a00620051550205a0007040a02c0c0105051443d03102c8160861312440c0c2c40b40700c0ea0030090001517100000c40c040041c1d01191034052900a500510300501520000740038100c036220390030031081283c069000f02030502001804890380b68032201c40100c0120030656400c440700803004c081003a08404030000800a200401d21584242d541c5991010420784660180030103800c001508404481004406154403d4580d0043d401610014281daa2900d107081c4900c181090b140d00302c1491070b9090650390844c07010b043c9103024013040f08844c0d40d5102c0030380c0e5655811001510100700c1c4810000c8400e140354401540203001d400003503d0b01462070b03220341c41111107505c0360b0b000a05400070022108000145c0e18054510901c1c00c01ea0b82d45810f1004100d404d4918180c81c5807821400441d802e440143d00c180140601c40003031021516200540d28000d4014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 847079946 1250 847078696 847078709
    0x30c0305070905060916180602030904060906030302031e09130c1e1d0411120103050f0c06030402060d021c020c0d140307054b03070804150915020301 66
    0xc880e004111040b560240e1845401d0140c5038013030340d0341c80703803200c4001d8003400d0030403030038481203000b10005204005074420281c1000d4000f15981c21000c000d0004a40035944032025440c40c0140500000c3c1e800300c200e83d00285181c0c100d19440705071210b140b00b588980c101d50390703121400044540311402e480c0c200c045007050343d845020441c004000c1d46420054180c1c110b800040c090301540c0040c012070340c0302501d1200060400564201c0c0c0c0e030503108895001707440b81420410314200400810400700070609107820318401a001014410000c182280000341000b4410140445c40c256084441c0d41039500c0644500d911940503001105850000d5000542d45851030082281c070694003401800d402c0307042100140c1e0702e40b031652040000c0b601500f24141062081a031440d00c1c5224108100e91400b0902c0c0609542c0800060a0581d00c480b0405180702030054009104104000381c12441107070f4800c1c0c010280160001d12110900300a0004a00042920125081c0340214030107590155047c9d410307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 847081196 1250 847079946 847079953
    0x1091a0a021615030f020c0a0212030903010513050c0a14010305040212011814030a02070b1b060f01050307060f0806040c0306121a011202030a081e040b0c06061c080f0d06030c0305 79
    0x80f601810310680c447c5030b0b1030383c0c00d590020107808014100307210315081c2e990300c1200340c0782062510000070b03003956015101000300c80307240036510303041c480f042c4294008020200e44142d061880c0c10f08001c2c80c04030360a106814075903580c0000341951241100901e601100800030041a9112139049800100c030302c0090783c100d03e90300d5510303007042c43c008110b0b6817144032a00141041c42c50031420304c005910100400120581c01c0000300c81c4d03002c0400c50384c0d00800e480219007010750b04280905207070424982c00300040010140c9010f000c10b4200c501941c0080c01540c000c40c20700c80010f01a00501884d9001510401c520014601880100801c100600709080041c00c46c0c1d907030781c103858407403090309400195064010458800c005058040180764030032000e05811480c080d1440d0f9030394140c01541c04591a41800500401c04080500c1407640c000c1c4101d96131680f1062042d007200750403800010003010b07481d002446918401ca000281c91020030100824092a41c07a40780195070f442c9103104c112418070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 847082446 1250 847081196 847081211
    0x15030a150501032904090606031208090102070b0403051321020f0406081906060f0b03150909030f070501020904090f030210050c0f030a0b0d06021801091a0a02161503 73
    0x43c484c0c0a02c1801d141d50340d110001d070760030003640b4452040e414600c0543c05544d40008400040a500400d13008502030b0149044213410007001612655004084107416481000384070000b4100f24000780d001a0945006030315030440c021001c4105200341c0195441c0a00084200c54614400000c65101442a1101b0790340640000030700050b500203004005568020b2030300c03d080b010480c3c184800343c50195002262203640c424005000114507000b1043c4d4010000400020301e07a10300902c120304a0590301954286000310784941c6900400c914909070b07050014000781403260035010341d07850082c014410440001e00d403030566140c80c80c9982c21000350050250f9030072507909a2142602c941403400c0a1480c121361880e5812543d40020a0141340a548900c00f840582310803001401c480d120707880c01a60b0b404484181413180800000485c10010864010b20804402c02001e00710800d10b502c1054a0f5880c541c0c0507400c0c160202455281060b00300b400089000c1410303c0b1000d46041030b24200440c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 847083696 1250 847082446 847082449
    0xc0207170d0c1b0602010507090b09100302091311070201110f19020d060f05090c04091106131706040b060f180703020d09060207140604021e15030a1505 67
    0x940e000200e8210580000510145440c010200340350701c10b125596610400840c10500c1980c43d540780c000c100180e550740104403415404c42102c00252030300400132814074002400203986806c031b1404040406402244180041e269040c030028032050041c0d05100480c00d40c8410445d54118480590018288143c10310307101c00042090f180c00d076030300c401505540d07101d8600c282260103059400ca810019194040003c40c0e01480761407100000e140000c034140c03d10b407040c0743c6803075080426180700d40d2800013244000b40c8020060402044c09662140c0c0b28060345a1300590300000707a10140540d101080340308544600451104d00c502c0c441d1043c1d10305174840c0c07400c4c801d03d401a002540d410000c11003600c1032070600d1660007944504180b401500d072600901d0014156041014100d0703044d900400c0800410924016007803c800a0074001c0c01149072940006a0320b658058840789145405090840661104841c5502e1951a80c000513030780e0510f000070344001e280580010f1240308106601003000e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 847084946 1250 847083696 847083719
    0x501050f1303020618100e1b030c01050405040906090501110c060a06272004060809060f0f0a180c080d020c010816020a0f03030237050306130f0c0207 66
    0x1002d801d50f000705070381e956203488071402c0401c81c5400480c6100f503900d800078030800d6010328421901680040e0036940c0092800e40c2184450000b000d11942000e40880031590f80801a40e08441c02181c0103d100341c800d0a109004001d070b0b1201800315401d21007150b80850100004004840d007200440c4c486540343c602e008200d071480d0042803060311222004112004150490450070591107400140b0400f800641624a8049103240381d80c52130085000c0082d03039001980d5a5000d568007000d80807501d00b051075074811460040c00b10910310b25034401b18a001d1100c0d400042d0a09611080c1003400c2d0b002c2c01e0070410f101c0c0c0e61080b4040c611a030359091007120300c040b880185101301a103548003a92502c030482044d80c200c03410000118441e511380c20010070100c1213811025400783c1c5005a40d401c4240c1c03104aa1040300021400d0030160010071a80c0303288515410003650900e00e841f41d142d444050010f103802d81500002c1610074102840c90034070220f661f1000000303e090360211000c00350340c3c480c1e2203503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 847086196 1250 847084946 847084981
    0x617100e070f200f1509030306060a11150a0515030a020906180109150f0b12040305071506050a17250803130503160e1b04080a0501050f 60
    0x1940302a40814a141d020710754030151003000d810b20903071000d122140520a50780c21001c0d0b4080b0f82c89403941041c00102485100200d01c21025001002d00c2d00780c00850b039910010f0013545c0514400a11794003541e110340000c0301c81c04280005d0307074441d810706080041d0b0800305892040c8128034280104109103203119008122800103000346c80c60403840d0f02008100380c001040250007149904c0c0c81d000b440d05848005018049103a4005480f50b00c3e82010010400c407a000307401044907040e402c2c44592405419240e000140c2030200000d5a11403030111854040d4010080c440d096150b1080401e1903190800800d0711020b81d810743c15142d960149500404020086030400e400c04202d5211080c85080c080407040440ba5821101a03a030700c48107440c5600c050042c08035004601014416843d0500410a120f04c501d021a400130b4103207210300200301006030490f016038086190301407080d40400c058400510303200058404560084c01c0081c003800d01280c1304000b52210070700041007240010788861 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 847087446 1250 847086196 847086209
    0x1314030c04180f06020f0a1206080f0a080f1b030c011b0e1e120a06060608070f03020a02100f060501021504111215011d0a060b030a0b040e07061710 65
    0x5040b64400d0b26100d54032844910252003213a020800c1c0f80402106900500030140c840d900e50410010a650170000c84146e41c1049c91140c200c1d1080c0301d80201d000801191140e01708450990710300d020048180301d882400303500c02d182703106480780b80c028810120150162001c0c0c84028007880008a00c4500303030110143c40400400e004581ea20300c103051038071051050f03482c0c5804015182d8141d80000341e00e140300c1040380030103911020a2104104e01e40c002c800c003c050034249003500d418601c0010f0030020b9486010710030940d0108500b0b0300203208014143d80c03103500c070804210742c00c500414017000e0902400f4081c00b51090079009c01116116000d514803880e00a0410310040b80d210042241c10102501c8040883c400d0925520741c0e85c802c1403249001b008884806402154010b00c10050b90300000c040301085d6203070010400c50004260304503588940d0000c03000561030b247d040000c00404446450360b00300c2c0b040c000d011500a410024680c1c00e100000000c210a81c0c0702204204249018050341 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 847088696 1250 847087446 847087481
    0x50a171510110d050705010e03030a09170705030702060901020124140105210606040321031107050a0221010203010f0620030a050f070b0a060302011407110f061314030c04 75
    0x904200b4410000f17440c1c513501c1000040f0f4000c215a040f203256400c25600c500c401940d5001c20f90400c580b40407001d02a098040d962703800c02055407625500d90280e203070040d01403080000e008075a81e00c00e40c8426030003152042401d01d20140a43c0740d0240701103a000d101075109007500c64402d50760241064800c2102c200040c0515500b683c11184c40f80071000e000160001d005000c0030000074550034404d00c01c0c00030f00310340c2410b64400060050664140200a1030980b200b0048000404c1021070900e0301c181c2c06445402a0084e41e1302181c11102c0000f4000e5201c1d4400320000c50f0301c020041200045a5107941c500000c001c2c9242e80000240450401e046203a00401c049075002c1d0044000d04500d1415015090406981e0344540c036105804442d605401c0c0d98841c0306108540e000b4003080f050750300f004942c904150565640b140060121183d4501c590007811075458580d8940d000c56001c100c1c1004a48d11059803030285980b4422a800454480d000c1c4045040382400e00748a9003002641a4002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 847089946 1250 847088696 847088713
    0x10f0308040924061d0d080313020f0d3507031b061a040c11030414030f0d0f1101021e07020d06060602160f0f0501050a17151011 57
    0x80010f003004460182000e084400250509100000480003001252200350ba076a40000992082100100c4068801c2c4c150348081000308081c2029070394001c40341100700c5103180003800050140b06e80d10340c8881d4000201030708032040140c0350041c440f010039408049200c03c15803031701c13601c01100c28100d448440c03c024400c0d080442d00c15124070002c030094116902410030661512002c0c1c034003400f044a070b01d0800a1040c1518201489001c103005011b281c0030b50110369000025031284100d10450701219801f4440c00d000303a4080c08414071384d00d101d00032240f580c040c00001900a500039000c0001189070f00501040001041c001c4503a000881c4910161a007440500014507030082030302a40c10040c0344440c0030000e042481240d01034a403917002820303164800c5d2000108241c0340c2e00214800301002c0d4041040002c941c4051040d02e20909141e5201c161080702103a0000c101141282d0554240c1c1c14000d88805401d20315145080c251900b01112051181c2500c180c90900d002041940c0f00c482d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 847091196 1250 847089946 847089959
    0xe0309011b060b06040b071101141803160909020114120406050415050c130f0b040b03130501020a030b040506030a030e10050d0e01020d0e060405101512051005010f030804 75
    0x1184441c0c640304420010342604060086103503504280c1114001403000207442c0184402d003643c150040c102440c0020100d0311300c1601c1d1009000300d58626030b01110040d41a401c65a050110401c04c0744403494442d841d030b90311803410025200c00c210a074045510030a40d2201542814102d80010856002c21320031610340760780b403a00400f0000e00a4502e420410fa000c1c07807041c040d00070309016807003440e14075441d034100034041002c19010303500c11085a0180903040044055400070380b000c5070324103603880361280d0f00d007802d1101c03005001d031b8014065407000924a100c150503510904002c0810b490410059454809040daa4682040c1c050042201074040c0340c094900502841c42583c0a45491410010ba00c8102c0301581c20642001070b007030b500412050250062407140320f84900ca06002040141440d84a00d0303180c0c4250135482d40d03550f4580385444d0100317188002c4000103105c0720902d030070070413160700740307183c03207124020003a0b0f850b034100000006c10440780c4030480e068907004503441c1d02e4a0320340306 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 847092446 1250 847091196 847091237
    0x5010c08190504120b010801050c07052d0304091a09010509190b2709031c0c020c1f1202090a230a1203020d021f0b0a050603010f05040e030901 63
    0x420900c1040340810000c00c2e11007004d0340044280d4070441d4000d24035414140a1400c0d60f0f002046403900500521104011950004a40342c4c0650b10400c100c110b18913601544108034400c01104c410303032000140010704501d1550001100c00242252400211034410400090000c2031050560012031207003ca2020121402c1640c00c49654010000b4583c0303405020941e2143c1040700c8140f4240e4a0380d039410001c04400480b036121076450061881c10100403880100e2062003184001001d41e02e80709142214002c1181c0000100020010000c0160706002080203020000080001403c0d50011318101310b80b50080c1c0302d4a0000520561b9424100380300820309441c03010005e0607a04488a0000b0a5190218003101030714801c08400c45120580c10064a0460030448034411540082d0b010280311421380300e10241038a04120220341c0040503c00240d592240d50801da510007400400082d043d410500044c0c105d039000d5400f40950f0480a89403038407409a031444a0205001516a84040d0140c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 847093696 1250 847092446 847092487
    0x50907051e0f1203070b090f15070203040b03040b010519050f040b04140708010305250608070c0b0c042c01030212070e1302040b040b0d060f060e10030c05010c08 71
    0x282c07980c0105084040050072a400c0c0d140b40d071465410002d412010701241ca000c80d036120f40c91380010081081c15403806581da400b40b0120307104c840310920110345907600c24000c480c018000100c1140c0c90f81090305045021310700078421680f003681000710003000540c081c682c1d442102d03401084201180350020510001d0001d00305882e078495581c0384203c401c2e065804400e8081c00c1c040d0f864914030360452070303c1d904c0e1034112450150032342c51900800310001000495541501d4051a2621498403445415282e00403801d80c01840303207941340100721241c2c9122000c0d00481d4020600740045d4406480c13612417001040d42080800d0b04524010302c00350600183d040c00200703511046944040c2d4481414180c94002e681c00303074020740c51444510540c40c00380640000c030301302110100043d000c0940080c910030740504000340043e407240c503daa90702c2c40c6948900f0050100152035412446c0071900c0e21103000590200300c403280c02e810740203c0c0c03d500c510501d5a40607840241507241c414100008500100796 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 847094946 1250 847093696 847093699
    0xb0118060315080f061006180302360402010207090621080405030d03060504060b03270f01091a09010b060301410f030f030f0924070501050907051e 65
    0x200c1c00c00103c0e0300301040340440090904004c0c124a00300b1001d80b108000c0b181d0310035400c024013060354102c1c19208585a00460b5070443d00805524035100c9141da00c4145070042100c141c4d40c541c0441d11900d005030410344200d200741e080d21034050f282c0308038008513075a03030007040320201014840034081c0924888100816024656007414180c0c0c1e00c7c00280791481c0a01c80e80e0000e41c65010801141c10a400f4a202409003401d10905501c0c00121507501c0b0a80c0b12402200d995901310024000b80c001d0084000c2c045c0190b00a2109100074241a440003d1340c0495480d41e00c03100d00011910501072260551480004224600d542d103890000b226035205d80b400e041d10448880d12214050381d140c2c144d100540342a040c02003813450f00340200218030300d4460209000340c0141d5280211140d021044600c014242c51006868258000201e40005070506940030140c600e041c41c11080c012000103020120302c40d60080c0040c0d51030640150300c1d44003512600d604a00c2c0803204140041031900e6a0021050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 847096196 1250 847094946 847094981
    0x181d03090915100207080d0e0112021b0d210c0c03081b0315040b0a060503060415090c050c190308010303030c1715010201150506030402060702012001020405040b01180603 75
    0x325000050f00c04144003840c00056071103040c04101c80e82c0d0511406200210724249841513140c030100183c00c466001c3c8290205a9000420f501420640c1011242c201c410341c04640c00208910006004000038450300a00300703010021a0510848501403802f8200540e40d48560141d0199804d5072904c1c006045900400c032948001600d80d401240514170460103048011203c4043e43c082c171040710141184540030b103039010010b04c0040d400c68112500404160f80001303800d02c404078240304040c0c460b00b10035001070401c650a402107a020001e080142b01c480c054a1554040440e0091151031204006002c201d2100c01040841c4c000c0d4408061070259040c04203190715114907241c0c030824111550300c2d01c40341c00c18000705156030902c01c040c001452507410603205824540012500d000042c0000e03c40e01000074901c00316442641c4820052940382e504c0c20140c404642d50700e0103500540600e0f40240c1c5403d0f61440203601c101c1b014050620303c032090700201420908120701501101c082000e0404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 847097446 1250 847096196 847096231
    0x910050c090126070914031b060c07030606030b070e030a0308040204050618041a07090f031103011b08040611041512110a2705011d0118181d030909 65
    0x18400301014815880c0d41e4821100c98280580c1c0748a600805010751f02a40c80030305030640c648000301c1418407101c0708880150b2202c01d58940b140c500305040c1c10050045042440020400c007034407100d58000d10103911911041e00e10314007070583d0b84005210280c00501401c0114026040c25030199400000141c0b89800d0000402c03c0d01c862a1826642101c00180e506018501c0c40780c0048000d0300902c280c51300c2e40210b86410301c01028044580009402143c500201486a5400350710140002400092401a68520f22005000c1090448060321094240414038181594080803a000d803034910312500c40100b800c000840301480704d40144d20b1580d1ba252001005150004058500042282c3e107903c0500c0300240003118078070300900d25000c140100b80080c41140c2c0c10011900c6c1d6a6600c900441e503010002c40122400c05110a0780480100b0109020840c0c0c241016000d0305072410200a0000c8092580450854400c0348181103040d0070a014000b820b03e0524100d6411a035100806256003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 847098696 1250 847097446 847097507
    0x2b030c020d060e1c03020a020d140c06090a050f01090308150f0913020f0f0f0105030703021c0b04180b161103030709030209130206031620060910050c0901 68
    0x2188540c032082110b60003050078090308603210450084004c0603150960410290b420080d40e40c0141c21070103001d1044150520b0b00b82c400c0042500c414080d0003084031854140480040c6d122185140143c801d400340e1005401050f40501030181010b070315580342c0c0d5855440e2030404a0604d8a40f0b0320560048a03050485807030b686404a0030300500c0305501c00d140e001c2052040002c10301c86580498050b044040014055a803001000ca10138802070822030b907250390766a4118000d10548081d003196000609040350704405940c013520004800351010000d00922124104282d440b4410040070f000d40e00f40003070314074000f942c0d080420441c10306000c9000c605c0a40302c28159000ac540c840c0004040510030019481d0201d5070540069002d201800412201d402084640c40000c2c00e4400840c009214440d10b14820101d2000301e4140340c0b58880c45468482416841d0b40d001e0766140c6991281915401900115114040c06402c460380054504500c40005494402a1401c1c6001104000c480311105 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 847099946 1250 847098696 847098701
    0x604090506010b18030604051209011209050607030e150604110c031606061a0906031512011506020f0709090606030b0a2705030d09150f02092b030c020d06 68
    0x41c22210049540300c6401a10004d18000d0718140b4070f00c03a50000d01440085240890003072000800310342c900d07030f40e00a41401a92145040c2000800c203514240740401880b00125050f80141c032540e030144000f003c2e4409144d0745981d40e15610b4400f4804001050052500d64082d0481662401600b400d140000343c0281c2150132003e01d074407a442641e540c00040150034030480f4080c00c1608015100303015405044052400f540f4000350250000002060403a2104540d0440352400207000f0329400d01c1c490703c600c2c0644007051358207503000c8101202040346400421100c1d0b44080b00380041840c64504130418014003122601580c809075250b00200c04940c2047c0220320510910303202080100c146c40e5282d1a0303c1c025021001044007900d07200f40003c8001c4215038a4480e01c03940450046050306140e00312591101107002c0b021701e0440c02c00302103c0302c3c1e000340c004000229007030010804440500103ea1603d001c510030724010005504000902490744021203d0000e0015425041c00c1c0d5500c004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 847101196 1250 847099946 847099949
    0x140f0312040e06100c26090904050114070f020307150b12030711040209060909060307080303070201090c0509060120070902040f050310060b09100c06020721180e060409050601 77
    0x2c115036503041068034208403030b40c0b42e40d00700300b46416400b105158a50358510840244000f81148074400c143c41400c0b03403481590b8440000400c1d00d50075007441e1030709034020000002030004103000c0e00002a01a4010b181c0c100204140e9000307546461880c2c1d503000750041d00e40c1503925001c0e548801036000c80d00d035849080c805940190065985a080c3d0801c81c1000461740d00e220702c21401045207400030703181e4400b0344140c0042500d00c00000d0700e821000904100b882e80111510703101c04020041c81c03d50540103000d503580528031469803644c40d281400044507089030b00c40d0200b80440c0e84002803c6091203014001c00c2444141c2d40c80da40c68825510030b80e070155118500342c50019a0a1015241c103000c0c1e251707130702c201d0002008002c2c904404013405016120f03205200b20711062205410714010029801d01aa01002c21075441c1400e00e0b205811024190a51200481c440e0807511914029240340b40140908130200901d00e10780511060104c40060070550016115141e40e030001c3c1d802c001c15030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 847102446 1250 847101196 847101209
    0x414370b240903060a0621060e0a030306090e0f0604290a06060e06072307050a0b0c150415111b010e12130b031b0d0e0606040204140f031204 62
    0x5030b5444a5804041c940580a0042d0210390f04d403010420a41d031140d0244100300401e00210b08040e0701c5820240700030414a03462120900824034a01704040d032580c0f2080560741001010405a500c008016a8500c0603503d4007400358013060105000c10240003643e008580041c1420701680030038041d800f13003890f050300c0d000c045603103420f0288001e542201c19031000060039201c10b401c0c07020b80c2c2c9810000040c510b10b100b409070020400100d100c1d00130302c101c0010707240189c24207084603942c4841c412a40c1c4001248401d6003c0d0b048201c040030100d50545005a4100d51089642020121604000c10314220051401300d800c015000031141000f11042071440107200004903001d088180701d0404a03c0c1c07441c6210310404002071001c1150010000c01582d440140302500c980c1c5127030848200100440088003454800300380142d40e580760350082c59213465041c043c3d4005465a00500080e40102e00441c208901c44010501450418407005052003100400301c0b0100e00c1c2031201201ca43c0e100b0740002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 847103696 1250 847102446 847102519
    0x6030c1e0405221407050406080309030c0904030507150f1802030d0203040810020c07120c14010e130b2d0a0f0303050306130207020414370b 62
    0x1403000c0c5050b10a040e4040c50b59460903101c00340d5903804500d98810380314010000c07040c01c026940c840104111784000b404000d04200412500c4101072940c0380c01c0509468840d108941010515040142c03042c3d000d954940c44140c2007010035641c00c0602001c1522441c2d00076552400780c9490300480c05155039007800a5020180840c40e030050600b065000c540c80c40941d401007000f0000c0716000641072019518081005072501481c881b814103091135a400020340511808024040c444e00107070b25800c80d040f4240d8811000c0d0100c0054421550410781150300c0120068004a44445500f0902d07400b00000c11841104500352072800d202812140c0c40c2c40380d90204020f4000b58202007100310b02901c0c050007000105031860b0303002040b51100619140c01103550300103134402200705406035240d40c0e0707000b442405540e404984c02c0a80060403140300305e4180303082c070407100707c4140d07000500501314552081030300c040403002005002d82062051f4941200352111024090341b5904480e200190382032141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 847104946 1250 847103696 847103749
    0x10c14030c030f0c060f0403080a0e0703080406050c1510030b04021c12031109060406140d021206100507020315060d0c030b070215091b0109030501051f0b090108010e06030c 76
    0xd6480c0000017840c1e101b5003007510007808046500023120981c417004400000c90a020384465160820144c0d5000525420001c10081a40307600800946008400c060403030f0600344001d13141e02071040c4246c446000704050640d080c40407500c82c4510603070050000e0621a81401940705a014105009200380d68a04a000c1d048080c0c81d814010301c40c10134403544a00b820f0170607170000141540b0540c402c2c801441050320000c3d54096620040d1250605800d000319203a803981501d603140c42108680162180618102e01c0031424000e2040d90203d0703401400910b403107031540200c4255104050141c0d6407151143c402400020300c5c601484000c3c44c0305603400042c3d030500441c041c3c41d0420b0ba10010300144818410020012030000b030020746800042103401c00f04500e031005840c1c120b603e800151282d402e103002c01843da50400ba402f035080040403001031001d56540da604083d400b900c2c803e81d00040ca0301004209160720204455000000142940c4928695000041c500c0d107144c02c400b02640810640c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 847106196 1250 847104946 847104967
    0x303100311060f091003110703020a021008010b1903150801020909100b180d080c06150301020309120c010204050a120605090c0f010f020c0a181a010c14030c030f 71
    0xa801c01d00501c26500c090030b20450031100c480a0207080e5290380241c4804c06004117041c8250404800544190740d4980d40e402141402500c9a10b074038003c0c0d006103440000c10850354821144607040b0703007c82880c2d81c28452441b0100e4000784852840008041d2166025142030721002104401058803100069803a1008001d101d01207000400862000d50407907420030200030104c044680d00c852080d0352041841c0c07208006005884010401340444902103540c507800040001c81c80d0040c10729128900c00309600c40e04240c00d03840102e899521507003140303170403444084d040340142c229050031600140c18241c44801185a1084680c01101200e1444000c0400d220b41440f8060308000340c400a000070f2403441c030200d19500142008141048945090841180d00c00d10241d0602c890003006c0800290fa104010007080200d51010b440e00c80c949440e00c00780e4841104101e80450040e1281d643c6840c8980f14080d110b0010310204031580010807040c160380c2828030003000c03106081e0880c02d40b40e028020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 847107446 1250 847106196 847106213
    0x150309150a09020109030b19020708091206061c03020a0602071b09020c03120a1e0209031002040510080c070b0112152903032503180303051e0c03031003 67
    0x900c1e401c9a1882c042da82c20243c0d901030049025030303030841c10766141611212000c0078542c0304143e10b40d4000b4030208001e010044444014201100100d0310120802c1d4038400d6951508000c0d10744030b030f004003100c1e9490b0f00354000040c041d4070140640103413050140f260b104c010503640706034411034404116242c1c907511300502c0c00031000039204810085061484912040da40e85c0b0410141880c0c10741208000750850071541c0026210a400c02080864880407590b080003942083e0078161081c05608584a02080d442c4260740032114002c01070300b442c020081003503817041c0c4003603c1e091083c042040300c400440d140100c00b500806240300d000c1d46003881400d080c030140c0c0002c510700700c0103424024030300720088100d024511340844507070100c0507000e495800607165203c2c5034200e48a803000400700c2403888071004001c4009501948401320702010241020499001500001b000300e0801d010160f240c00001c032807491403100c0c01c41d1181c40c0060024026245810889800303440002011040c405c10001c2c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 847108696 1250 847107446 847107451
    0x3040503010e100e07150302091c0f0312090803061201090507061707030204080c040b060d3b2a04090b0925062102070c0f0f050f010e15030915 63
    0xc0701824020781001515106c1803c00c1c1c003040c00701500880d140601c1d43c0c1e1221500426100b17080e070545568010728007107800d02d04815058000c503100780008500c41a6500400c1e082e10342c010329451641d9102c0c1e08100110281305003403000c9642e22200040010070030011030f405007100e611095942000400c540c0041c41c0001e1225003010b0060000700140d42001480c12841c0d1000c96011070810200d10101d42daa02410300c041d0705444c02c090381003079032001400d070300e80c18401c4c1d00c00c02c0050b40070f00001c52040c60074000c2c00043e15600240c19000107c81c6501000e9200c0c622a8840f00b603040e038500051b055420085050b5104e0600c1c0080c04007030081040401c02e4500c129940100d59000131000c02c0200c0518800d88080c40b022030300400020494030401d040e00c2c0c2e40883c085444000034107002c0004505030184580d1000c0c44500440d80c074035600c2585088400c018980c0864031091001140d428800c40005500a103143d007080718185000d801451040d44080000d1591810141c4c18a5950710301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 847109946 1250 847108696 847108721
    0x307021818011103182521081905090904121205010e1b070804080319090510030e1608280203120a17010315060503030a120b010203040503010e10 64
    0x18a0312141c0b542d0500429070390301004404010060400c0c421401d0b050000c1281c9083d41b6919202c80201106842c0c0c07807a00a6401030038040340401c85803d1000340e00b014038140606032290900c02e042d2120190180500030001900e4020700b410004030228082d0340050b1801c0b1151001020203810155010b415042040780ca20030a200c254500030f58190041e0015205140794020311800f80650921001110b2145034031030a031580d0b60b0366400d0900d40780d800c0100300100d00100c05200c1085184070710050819204001c00e003034200c1c020101c0590042240301c019641d24042e0f490200d0b404696581c640c80208221409800070100c000d040303550112003282c01440480b0000c1140d000358400049010900c20001c914a60700c4810704026100c01405c0444110354041d50310002c0108449841e1825202805442c00d03c03805445204050b201c0c0946100b01000800b0780d011044002407a80000c0021241030055920b46a16000883c0c00d494070038a034612282e0124404042c1c1101c80d11032503800007013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 847111196 1250 847109946 847109951
    0x1080a0504200d02130b15070302070608041109041101030632030a0b0c071703190f020408010f1a09040201120e15010e040b010501020706020c12030702181801 70
    0x5041e03a6080d48038103030030426061050002d1015086858015960465540080c00b4992920349082640080d100c0c41410341e004869400111204228400580b00440e50603000380c100c050038030904844031600103000396510300000074485010384400c0141d90189000d80320042c034441c090b20001d0706958190788944640c1d00d507201a08c0e1102c0658980c180d6aa50642d10000700304071800003c1d00d07001c1c42349005006090401c0c2402207241a400c01480520f00c140c0d842220000d8400075840700c1d010450b41d03c400750100300901d80b810000d95000c002c0d01404100700608180d1503004039800c4401450348652406c0d83d130035030b10340790641c500f0000e080400221440c012911307003980003c1001c0d000d0341014a00310340b60070b0020240c00341030050091681042c5101d007035070760303455203124041841954280c40c110b0820b000450254804a02042941c1460300100307980c04c408820b0000301c0351424020304450000340010304c01a030700c13800002c8541c510100150346500705080100000b00910007003203801d070b2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 847112446 1250 847111196 847111201
    0x150901181413020c0f060f0601020304050a0e0601030905030c0d0e030604110913080a05031504090305030106200708070518040201080a0915050405061503032d040f08010501030201080a05 82
    0x2081c1c1e00c050000d10401e8400041141c80ca0040d2406030140d0f01d0524428014181c02903a01d441c001846071154040d503102c15410303102e030001aa1a803050f80240fa8004110070003d01941c03c0c02d915058000a061600082405143c2c8909065410501d5066899013285045010082c0d01000d00c80302410200d01070151420241c1d01c030000e400d08001c0460280c0254400038482e0904801e08480c050340012500760f030380550420080956104030f442d00c50708005190101c60358105031040750803007940f5071103462446e401c1103801d41c1c842c1c80c290181c4442006680c00c80b003814005011190003454120010600d85040104105070803818044910840c4d241c142000090b0f03a2190130315070070030b4901c107000079508410b043c01c80034100140c0401c81d9150800f0144000c201c0c0c005411886600030b4034196105c904010700305600d034851900b041c002002500c4207100140e02d000075010b00a40386108492800307949030341c01d4000f00c0c8290301c200c9407130351341e20010029075801c500d01031b501c014003400821007032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 847113696 1250 847112446 847112459
    0xc020c0f03120d050903070c0f0e09030703090b0c01060918050d0813171611040b0a050d0b13051e0607050a0f1202090d0b1005100503010e09070515090118 68
    0x41c0100c0b410244621340b5107002c651402c2090044816258000300c2103030175180ca401c9035201c002c40b41d1050425112000d000122821400300940d10030b42da0650faa240c4a07850308151042c0e98108160a2029561700c04000541004500c03609040848020f41c4007101126800d007a801c01a42e20102402e206585042095404c081c40803040c400303600c00065514440c1c0041a9001d6001c2e0b20300c040d228525a440c060207000c1070700031080040074100c5060003100b410340180210801c1c18030030700344c100d0152001c1500080c15071030080d611003107000548048850540300c451910004010f00b10b82198082014241d20000780b00c2250710089500700780d807a102c41d0a80c0140305103041d041002c200f110440c155151050a901240d03a5890000c0100c080d0030000c1c180744240309410f0301c1c540b440c1e09135a4000112030810031540c600c0303140d06445042c1160710f04014004600801080c2c03025500852002185954401450b01140000411400d844400800c00034100c0d08004805010011300004100445c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 847114946 1250 847113696 847113733
    0x80f0606010f1e180806040c2106020d0b040504080c0705100813060b040606091e030807022e08070314090303011a09031b0112050907150e040c020c0f03 67
    0x1404241420305403441d0020340304843c0014030550348480300f104c3d24400600070320005070090081c4d00070f8140386116580e030303400810180115110700d6200542c02441501040495025051a00c20030300d011034900a2000058201c9504640071100110040b4002e600000c1c10005500588426240c2420600044801802c100740050400340c10f1000311040d2070400c041a08800e190700780141080c051a81c0f50000070300552602e01400c1005690b09201840d00402c2440680889400000f00d6150544540920001d0480300000d45215424115209042c40c41e0f0f103c0301c0109080bda8801040b414030390b80c01410382d06404503100540780050305000c69a0300c0842200e044074411189101500c550640f1221079000302c205c03c5a01d07014202903441741c42c1344001f0000c4202030903038800110440001d2260304695058900b029141e0060805210b12071084881c104441e1950070a00911000314001070f081c2d588170307203000c070041e001021f0710465030a1010400d05001403c4028001450085408404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 847116196 1250 847114946 847114967
    0x108060c1204030c3503011a070c12080d0e0a05060a0509120409020301212f060d1b110c0f0d05061e1b090904020609040204080f0606010f 61
    0x155240301c00c0c080ba041501815102001560040d42140c0c00076140c0e00b4a001102e4000c01d440041c001e40c0c40040f00501e0100450303069805021a592800040b84c0311100346030000c40c011140c032000840e001c982100744011b0140c4540c460010960744910301d00c44003044d140003003098603065101c10044800540081000b136446042c104000400d50354080c3c07520300e8100001d81d42c1400d40d000060114001d011a0000c6041c1c0380c401c4225042c94190410509183c100701001070326803059020b0000c0d07032109015402107152000300340d100c8481100400240558001005100310a0380d807021011808120fa040120308401410f0203910b1920000d40180c459044a40c1d080c4076000007100c0711415916040d240ea040c41d040001c40c0e4451401d00c01642c40000b041c0e50300d1003104503840c006804460f51841c0200300d40c4204009904250051041c003441f0280030304201e070700660a022201c0c4549540c4042c20003806000014084481080b03401c138103241f80503280a041182a03026568455001500c550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 847117446 1250 847116196 847116217
    0x15040c09081906021306020604120c05031b0c060d0c080903031b13080d09060806150a0e04091202010f200f0c010f020a030c17010e19110c070e0108060c 67
    0xc2c0a036071480c000000384207018a20510803800317000843d025a0004d00644560b104618a4181e50b600c0e00c2d080c1e4009030041001845c5500c2004142d500000842c01070004808460441d500c041c48840010f0054001c260110003030342c3d540c00100b03103481c2d00612240e040036000c00a186035082800c000c254000740c1c0403600c0101d8100048400c42104200781c450010034840303060300c540396070501000301020094807c08000805510103c0c2030b92400351180d40d0305050b00c082c20313882c02c0d1501d03000b642c0700c1081400f0b40303600c035070780b50300b801c0208900b01c0d564070740ca030402d9000140400d1588005000c580c00510103441d0003802e4000e40740d40c0b0a0450407038904414007405c4a4031200b650f500503001d1b00320101c0d101c5209001040c0c04201c641c00d6004200300e0120b607290a41000351303030400c0d00c00200d000d200340c4a20145a10104100004030070b8441c0704c4034884003010440314001800031490368401c138074401c0140c0c404603040080c0b007943d000e050f003d4002c000207440c80741884101050345020b01c80d002c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 847118696 1250 847117446 847117483
    0x6030905031201060801030506090114060f041803021c0e0d11031011120a0e07050418022701170a02360708060f1e0a0e15040c0908 58
    0x1060203010000e944006011040341c50040d0703100d40c0300801490003840121058803c1b0004200c0440060050140c007050b1125404210f81d13070b03607003040034070301a568015400a5031003104040128816816145090094000302450081c4c4407034000c1d0a800c018456003003040d9280d4a190319911500300d200c109401c240e8128a04540b1400681440048814441c11602d42140e480d03112180b00c1c054002e00b00d18140b001490355400841c00281d13118940307940d00e1034020403024003c42c81c090f404000d24211a4030032581c005401d034041140d842001c507034243d0420848151a80c0c2640c442c00302d60143c408040c01401b60600c102455641d02e41000f00244900201c1c6402815042106600d01c032002800178081c40b400101e164007a0201f81c299100c01c00140d8001c0003c1c010304043c00f000d040c4a6020740581d81c0c15001707141c14175140b184a20125440b1108010004614000000302030151643c902122a02140c4400304401c481c9440750490a02c681600c04104442021072032140d4002da08016 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 847119946 1250 847118696 847118711
    0x206180118060f1a0112050433060f080d14160f0201020706050922090f0b0907090c050d02030907050a0b0912030f16080412030e1801050a0603 63
    0x440d0140050808080501000c041280d05220440d00041189440c20404009182040c61446042c90f0600c4140b0302041c0d20015554a110641e407107554014003d00c00070402010080c0d840c190900d68200740303038200c640c00c1e01000b4044440e22942009007400c1090398003281c40c02103855115503510b010301d014030925074480808809004200ea2050140d911407114800c150728020f419041d507203000382d0051007008000305815015170129102540000c144000d07106000301071101c1444042e10411b1029181d101200010712110700c2c1c00d038403d11540d0785e6429854607000040c507082041c0d0000001d141042c1c9680300345900441100c2060042d80d0025035a030340c900c0245031819116901094114400000003d08581624081c2141220490b2411071258030703009d0440c1d603070050784010b0021180402280c1e843c0402c8001285249128041d05410305950355032802e1280c19420098010941105c8100114070f060a10540500c8058807500c01c1c650410007c1240c0d1020380c0204001d05550702d91 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 847121196 1250 847119946 847119991
    0x210a08130b0307031a030609071208040906120b07050f07031b020306090c0f0613050d0f060507051e031e060103020c060c0c071706040f020a05030109060e1b010206 72
    0x308940507248603060181d0307900302000020018041d040200700d000c1c03181040034040f86004122180601c849800900d90241031202c0c0c1c886001d0301c00b0085a014a040000107501c031b80c2d81c000c0c0401440b6422505da40500c9609004001c01001040f48003040020402840158418400c0d1641c0581524181e181540c10090039080001103c5010f58548030300c40030066190000501c9440250054a1070310340003007040c0038041c05004003103240007080b6405005111500b465030040079880d024180e09110040c1c5030329542c003201c0017694141c001620006039803a040b0799201c0c001e0401c2d040040c540386189066441d11418620702400c65094205460201d48a07a00c2901078400c2c0ca01d91a0664406051151420f9001c1c1d00112880605004001000400b41e100000134800350746032102608960ba02c3c0e0f62418440301c140c0e40126400307181c1c0480070807240c60074810038a0701441000009030703003000e02481c035143c03c00c0c184039408046000c5840c02c1c210799020501d99008501e610f08d50f4143c03500c142 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 847122302 1106 847121196 847121227
    0x130603020f0a23040908040f050f01050922020c0f010504020a08071d060301110c06041b06020c04050a0b15120a020a0c080703020c030d0c02210a08 65
    0x443ca8410311126448480740345001080040e0350b84c0f01e55241c218680040d01302c0503114484110621642c10803030403404e9481c0003400c060303003012541000100c1091803480d2402c004002d8541240380001c40350143e0340d000010100340d8019400f00180b0b0b5000b044125030503441100071000000380d049001c074548050b20502680030171515034226400e0a80345000e81542c0c0c2540d0303540c80b41e50015004401170080c00a40a0141c0114105410b0409020320300b03c000e8030000600280403c01d03150001401441108141c0d4080b0f0199601003601c00140b900010311500410300803120f240e10760f49800140426202e040c0d441b216900e8003068034048ac05100c2030780000c6062800b04034017003615030029000161007881214090100017001ca4100316459052401041901142d1800c516000c0184102d8001c0b0519030103044201114050780c3c1c4501c82c10180060000003900c072440180b03203 = true := by decide +kernel

theorem cover : BRFrame.Cov 846942446 847122302 := by
  have h0 := BRFrame.cov_init 846942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 846942446 ≤ n) (h2 : n < 847122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
