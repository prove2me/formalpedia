-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3468
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:44:59.377525+00:00
-- url     : https://prove2.me/submissions/1d63c2e3-d929-4fec-ba10-180ba901fefc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 623561151 ≤ n < 623741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 623562401 1250 623561151 623561167
    0x60f3a0c030609030302090d06051005090c0d09081e0d0f11030f060d140703032d14040909030507050606040b150c1509061f03021012090204090b0a0c05 67
    0x8100d41000c8a5011400058901403440c095020780105030600d503000405410400500400c2d4001c01d106100c0170107003034003640d241c0003004216a8240d5410290250a00c003401002c103182c2d03c08041c1c2c0f4020710707840741842c0790141030000d03040e003036040c0480185c40421004a07000d070034020500300d40c1514030140941000c80944c4a80e03404010300f611440d08805d00411480d884401064560a81214aa003452612410010b5849c42c2e18070040f400900c0d25400180c0b423450600c14440b9210010603032094899441c04c040303c07048a00103540301002010000001c2d1440d283c410051054420b48034181c4500281c28400c2c24603070002c3c100d07405603003410150030581c1c0d07030046100a01c040d4034a940ea298944070b2000c600c0e04080c02c5035031000b071650300240301c010350001071083d00c50408101d0070244860700d243e070007441c14114030000b5000000001d150000c1806034203d02400b0000c4000003600d14030a400103010340300c811300c05803440780b000028414610024003e00a00002c1d03820154500380f0300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 623563651 1250 623562401 623562413
    0xe030a0f0201090809040903121407020d021c0c0804080609062e0608100f2421020a0324140607031205090718020c060106080103030512060f3a 63
    0x1c03441031700c1c0f00b1a40c405016040502688140495901020007001003c0b052042071544903030640e203400140c0304148400901602c0021868460704500c01d80e410702d2050810705441890610804a500003028000480d4001d801c1142601c1003001c04000c00240c02c01c902c400c0320b0050b204c60500401c80c40880c94290f20a04101c645003151854509804295150514400034442680001c19485d070111000222000460480d10348a8035020307e2080c0d215101105071001c0175900811115005201504071080c007550780500b0784c42600307080c042182010700e0400c810522000d0200648807a544000340500701d1140c201c081d20307079415501070f4984202a1405010081039500d1244000e0700d03140010b09006061182900601c4014941044d110305050808003a401503814290544164400021110320403007566048a4143e105d0500d082881c0b445007002000050002d0782000c0c0d0075001c8465626116004401d00030440407242c1030400300004581040010301c2c0040350719802d07480b0071000c940 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 623564901 1250 623563651 623563657
    0x80a0c151b0e0103110c07090f1418032a0105010816030f0c0b04230f0f040c03090b010b130b040812031b1204030e10051911010e030a0f02010908 64
    0x401c1c10142418000b8500481c0034044c00c8061403060f4a012500204000c400a090340958034003e009010044181e06120300301c400c86901c14541040450110b0740c940e0f43c13000d220452041d20415070345040710100c0000d6041c070000c13008100c04a01b14026035103000e820b02c11980940514406003551000300b00000d9002c000500000d04545d400b0301154042041c0d400c11940142100704013591229920031221960007542000f00c00c506000503204445854005851070807100d00404200c55a4004411710000748210100305080c140d8442d00ca40100f2000e6903a20300800c0ea240b84a0781d1100c84242c8075050005580c005e244103c0180000c0c410044040703114001194003d0740c490700e980c4d600301d00c1076100419460081403284009881c0c1c5940c00c0c3c021203188102d000313442e00800c640317050040c8400c0840c052030080010b00140304000f51605031103055070f01903a0500e07000a0340820300c0440c41c00c4928604003652190310004282e841c00b03810840c02900c0003410700003000700400c1902e602c00584 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 623566151 1250 623564901 623564951
    0xf02010e01060305070512011401261c0503040809123307210609151e09020f090301050a1a010912082a07140d0f110d080a0c15 56
    0x47c05050f0030007000e04254008c220801c801c000c68807095070340e4810210030900300c1071020120b68404a070342140c0c81c0006801c017000c42948030520414910070100712160340016000712014030381006084003e5440607400c1c980e0302005d101600c0480c003003608010041d066400c01403080820440102941e19260f0714565010500307080010916400e1240e101c0748000d00e007141d01c0d41a1501c10003050ba0305c900e61120542e1100302c1030140b640c6445d6240246101002004102c2060140e032090145c1205900035200c3c44418003d4035090141080c0080c2c20741d40c04a8101d80300a554140e104681350103400040300e4081f084c01e02800a41c241065200a104040b2010b81800310016010900300052000e031501c09081c1d680000030044040852a15000d084c03140c903050b00c48010320070314107250015201c5403c9a01801d075104248181d81c23601088800301c2500b46d031001020401501040840c00100601010743c5d41d14a815010703071402514903041103035002806031420340212620311801065103440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 623567401 1250 623566151 623566159
    0x8180d14070f02030f030d152402030c010c03150f051c02011b080a08010501210905010906090c03030f03050f15030a15060e13020d0b15060403030f02010e010603050705 74
    0x5510141090801c500c102c040c02505403182040501c2c1a0301c0100140000407082c42d01444058909143c1d140346803800d006010031260b1140d64520242080d8505070001251401031743d040c0f07460200081c0c2118562240840466100c00190980c1910103047d10302400780380b281c15008505003404610200100520003d509403503480c8082568010b150141900c0c0040f03a00402e052050b01d809030316500001041c1c404564603c0c00030075258000d41d1074024510b0285085600102c200301020094210b5071405c2c1c501e0b56030b0b0b010600c04900b25020b01001180100c4104450900c2d41c83e00038038140744009107104043c0f1b80410702c80440c11150180750011400110404140d0600340001c0c02c0004a48005002490405a41c10b90000a800c00400ca90401c10020740301c0c1c0c2c0d00101f0440d40b13102c07400001d601ca1610302d01a070004408500d0150894500d04000c00e02c1e840c074201184440e80250000d4000c1401c3d01048500c1031707424080e0881e11060b03403000b481001e203142d40703036070f550607840c000c16100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 623568651 1250 623567401 623567407
    0xa0602030703080a061208070203060a060602030f0d1b0302041a040e0606250c080d170103320a0b061206160e1f020705031f050709050603040308180d14 67
    0x15001c4030390003c0e07025001416001000d8202c91410181300d48c000c0300c08034083c0c0549400114041002e110b81004c4640303d8000c0c2d403400ba80d180028016900c407421200105666000019404d40c200843c80d0201080ba10300507680e40c148149600817005646004400c0c40040000340080705241c20910380100f030940d02951100c00380ca020340010f2000700d0b121440c009000784460207004140c2c154108030760300f602c1542c022020700d000071111140b41000e403524820952004000140d100d4415450500c81c00411801c407600815406a82441c0002111603d5002c820488280188420510340091044464607a954034201000703454403401002c0051107441c600501044600400d5480c1000c03e00919002d121140d6401002000f004803030b00300300510130400049610700300000c1800c01ca1400901c2044a5880d850510740a030200800540800c1320f090000a00c544800c1d010f103010754885c0d01c0d14603040c40d2000c0c61008418020010400030350080940300441c0d904004201070180701c114800796 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 623569901 1250 623568651 623568661
    0x160f0c020a150c060501090e0309090612060a0f060e1e0705090a090608010e0a1a1510031a031204050114160302030c010c03150e060d140c040b0a060203070308 70
    0x7903064041d4060314409004141d100811548011514074803482000c0410059886040d26000c03211220a0b00081340c0c070030014540903142a0290f41c1d442100100704c2032400700b20441550030040d00307450512041d0b40b51101406540d0702c5000701000351940304500360786454060b031541d91a807460b42c4c02905103582000482d01045c455400c0350802c0d400a8003050125582d40d040c28010095486107071211752800803500c100c1a40400c214081982000407498a00b50300011304e010100060082d203031808590f03803000482c0e19a82204450107130315442c00128460080c3c42480c003003880c0840c0c144641c0080e4403400344441460b00340c40c1503030b0003031030081c0d0329502c0e0400c202c00c144202c841440d0b80109089a032002c00d540040144854500d0740024010200da090040d81551103030640c40e000c24001c81c0e01409010150322000d984001c2c002e0800d0703003c0e643c0e5242c1c0303451584440480030040e00405d02000b042e00f0030b4000d00b0290310b41a40c0c0220303080d01e0210000d40780d001d4103000400b08009400452 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 623571151 1250 623569901 623569909
    0x50915040501080f0c0405060f090705040e0408030f130b0c09040207140f0d0c0b070305040204021b07050109050a030b16020307051c03050a0b030a060507020708060f040308160f0c02 80
    0x1200480098000c001c5035840d5441c40f9076680189003000158420141102100e00340f600505010b03c8001e00f01c0075040d40c01c3c40402110300d100505882c1004010f100c00104106901c01c00c2d402107008041403581c0c0d080c0414690062900204940c00340c03451010300a001604050045512080c0741e800c4d40d03150181800050082e108840b0302030448a050341a0311300f024000b043d01003400c60714004590346540c001009403200458404060a203c2c8a000010f9519002c1e401c100d80c840c0c030041c80149400040c010740c034508140b01680c4c0c4401d5211714424080d65030840054000b0302412200c480b030036880d60f5580440036000905e10713107102d8080103940b090faa00070415181c1541e07001040c0e481040c00205158081c83c40c007900000007904107004180b10000c18403030080c103a075000d805001741911540f20280039003000341090342140300740440001c034403205022140c0112001003146405040c5420020f254080242008003080d40c042c0080d11810740000400d14500790904040c900003066000107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 623572401 1250 623571151 623571181
    0xa02040b03160305011d0f0a03030203060109031e2a0909020609030304140a33050d06030302010e10050f04030c020112020c0102030402040c0306050f091005031c09050f06040509 78
    0x30201112005030702008010064000940e15088026501506d40c4030008566030f6868000c00004c00d60400c02142010911a40003140d2000041c10403c19260340c0382d03201c02c83c0140c9120701e4050a0030240048013042150300e0301c00900715001e4200d495030311200807690304000c030314032558854a03524a40e207000c6440c1c2034240da241d00e030001c050700e4855a4580829041d5002100201e107e01d0220070003080c990889180c07110b42200111410075031b03003c1d00590369000c00800c110786040c80024462070514807820b002d0b800c041c1d0b200f6800492490707207002242e40703840d17802002c0c0c0c1185402c00c000c00c1103d8000521560f40250140b038601001c80c0c480c001070722540464642c0510140c000902c1e010041c005400941c080d074801c0d80d0801c00002c90050880444820740505503200000b130500c0d440c51718054042e9500a071540849488141d520800685404060b00650000c0c04c82220302101c0103420180f8400100b0082d508120001d90401c005030303182c482d41c06030038494080707080412040c01140e801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 623573651 1250 623572401 623572423
    0xe280e04140312010306061a180109081b03010f110712050c070303030606080f0702062e0608040c080c0d0204020a030f090c0801060b04180e1504030e0f040e0a02040b03 74
    0x3900e81e151a00d40707840082003824042507070380301d0a05500042a8142c00401f020300d40c84c10441c0c0d8105034001c3d880450740c0f01962050788c104400be04010624101c01d1102910340703090a009409615070030000d16081d03449c40610354644a180c1403a0384811003100b0121818030f03501051000c441c00d203020017600c103070041e41d89640c1c9a02c101c01d030210070160980d0021381911a02d849080c41d03030f13580c1108015140750844540d4010f070031040109071040000f10040d2800049405520103024010b0034003181c40303c0b0360f80408006521001800309008480d9500300c0900010005803540ea409440450500c2c000310750000e010300c1d8001400102544258401e03101c90440b15814041302d500d604200c000c00c1014010b003c01c03946001e030001401c001e0042110101c0c2e08618030540c0c41450345208000500c60301e26680340901820103110405a015060a40f040340310351540c50403480d05000340080c0801145420340030354500f41200704541c83c00519010360b1541210003003411490703800820b0074002c1d2101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 623574901 1250 623573651 623573653
    0x42a1112220f0807061e120513080708120c0a0516030e0d0605010e07020703020f060f0418020304050d080603030304230d08040209060d0f0b15060a0e280e0414 70
    0xb00114031071002040c503c04075105e075941c0ba060120800f00c214141d9510364502004039144400364404a06650409588440c00d04440c10b0040c005450302c20680e40032400465140a00040d50341c07034141c018000b190003040d0f00c054181008180040a0039520424115058a14610708207004140c4100c075816803912000d0b001c041c0c014240e26110000e002c0038020078007007602e1040000c05c407a10001c3c2100889030002c05090320030b01c405051050700d5210341c0300700c2d1840d4003c000100e40342e0303091070554a00d94114040140d0340e00d03041c140141440c00216030740040122602c140b2489540000c203617a045600000410540002080c4000f1214424480e260040c01980c80b80c04025800641c114445d5009403407100103a950801000310102c1e0004009180c490040441d40c0401c2d09081074541c040d0391070f0201440d6a003081c00048213500180200000150100030001d100d040c43c40c40d001c0348a102e1014540c0144d509144401c0c200054044c0c0d5400301d103010000303018030480420107200395070442c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 623576151 1250 623574901 623574929
    0x80714190902030415020c03070303110f0c0607020c0402120c0a030e07091401050d08042c010b0d140106020d051617040f0605070b0c0702042a111222 66
    0x81c09460103500201c80070b464800b0b01c8009404d081416000320303140031000d2005140350107e2503038160014030005030818a05d200c1030011405c0c04022800a00c3c030100a0001001545403c000080c40c4c20112a0315034021401030110799411031030302003c1504044415442d03130301d60303014080c210f00800600d0054100c5115004000440c840300764015103140e042900486110303030b00c40b014480c0c1c4001018000342550030411080107038202103070750070744015014807107110f4130400c2da0a03510707000600380c2000e11000c60002d44004000128800d0285c6501820701121040d85000e80103520b98607440640011301c040080c1400c10080c031211002c640d1540110b0391914411042400d414a401c18050a0358000303480b4408030305503000d5000d5409140d4081c0d0302602c10303660b1100542558100d484201c0c1c0154072001c03003500300c1527540c80c150982140044070303008051417444001c3c02e100010a41da44140c124209620042030524216034001c041500c95102600790b00751143c001144a0380714542101d051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 623577401 1250 623576151 623576159
    0x9030903070f052b030c021908070e06030a0f14010609020d02040f0e0903092101050f0919020904141513030810140d080d090803160908071419 63
    0x514401c280c81c0103480200c942031802c00f50b29119203800380300f030003007440f25407071440040d00c1b0302140c001051002d054660601804180400ca18245402c017805942221000740280003800c50400c0e844141100140b03513004c0c00340c65000781d4510344180900f007030076518400e401ca844250061401003407080301c1107644040031001c4500a4005d401500701140312101c1c0007030b00d40e1159034614001d118960146181003000b8003040481502d06500c405207030241c0f881c072501d103042885002d02c502c141110607a0b00380b0308400c2190070905081040c00130140380c000c00002580320750b00704603407095100c044013061300b105209a47c0341001c003000405945002da000c1220000309603604011161081d21450340b1900c86420000c031251080c0542d0001c800d882c10059a10310700351440440c00c9005000c01c9180400206428040d101958816990180300006100008003c251280000d100740c1c0351a10303501d030400c0e80c0140c8588244c85840201d5041618070500307550350103840e03c0c0c140003000c00d083c499075817 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 623578651 1250 623577401 623577419
    0x307080a0e030a230307051207030b060703030504020f030d0905090a060305070602070e01141513030510022d030c0a0201060b040906060201140c090d060b0405100e0a0905150903090307 81
    0x784c81100d1100c0f0700960303d105850030038942603900914450311001e050002d00b40138540d0107030000b0b00a00815403140d5402c2d407a0388441004212140c040d60b8049002d203454010b2050402090113068020b605c00c0340c0741040079610168070801c0d90811030b0011255140d1403182e0010304659003000c0c0043c007500fa00060815000182ca1044503003400085030f2030703030346d41060b114810101a6641d40242c009580c14101c0400c0000900c00c0f5031007a09a80d0806803030307480d0301d0319201d030b041c0c441607919500103405ea4010803c4000c4035120316000c4940d00004041612640040c040501304c000048800300b1007204440c004e4118802502c54540786980f520768034003141016182d41d1140d20059482d010700038102041035140c040c410743c00c5550345031074001054113004140300c00640139100d950f50b800d0a03040790360ba2802031f80d000b05002d5241c0d55030a400c02c02001d1810700c01070964031815203881c41103000680041001100c0c035500911807515991600780d007900314800e150506905010728075001c50301e448 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 623579901 1250 623578651 623578667
    0x61b03070f1206120312021911101b031404050c06070812040b1006020a0309060f050c0304080304140102070f2304180b010f0303090b0307110a290c0307080a0e030a 72
    0x8000c0d96000c04400040020340c00300d1084619544210a442c1c201e43c8d81203014461558210007554101c846044003048040111041c0c404062400c4284c050b102a840740c0c0360090386411054940d000d030960070725645090b540e845290229000e2540440c1c00d1080c4280d28095524040f002244090945424030705046801412598110024140000458031610001d100d215203585a2202680d050a201060700c0b810b400128400c2004130400083c9034010301400607000501b0700c4402035440e681844080c544580707001c00114119445850304002d80c04400301071004a4800d27000340300b49030038843c20390f00268104c0d00c04c01d60824280300c0b09080f000c1e501525441076600842c031010716039803245142c4920441d54803000e00000c4054001b80306241c4200c00440e000001814100302a040c0d01000b28109600303444255041e10245010060f02800407690f060119070a4001078018544995480814003001d09a0f00401c031000740043c1c45030034a41e2250740c108101c1c4044070f44132500001c00803c064 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 623581151 1250 623579901 623579903
    0x40b18070201060f0b07020d0b061c0f02040c030209090408070f02180a0b09060105071b2d0602210304060b130c0207150903031b08070303050108061b03070f120612 72
    0x700145000641e03225400581b40310550043c880030581206454049a15601412455011b4803a00d40054481d501500a20380c043c4580301070141c02c2003900400003140e00c4408542d003414010407031020b0540d034680e500f541c020313440340883e6242c444030304101d2852000f840c1d0081d001300042d0910f4007107802d01c40e0414403901d14a60144044448002131103650f8009a0b00b441c0811010f0200c0c0000809422034021014200c80d00c00702c3d2941e0f41c0304460909541f0a50000c0302a03003001c2030b03a00340940300c014640507081c50f0009181000350070035501030400348040e43c500c3c1080040042001c01c42d558000c00828040144001680d40400038164010850702e0b04207801b501c1001e03400184040740b220403510b130800944484100c24a1924260380d0314100311035141000c600d0740c1c040300000c3e40c4d00002d86642c038020b80d00010390b0340c18141c08900d031000141c041a00002502c105c1c2c1c10110b01803045030b502040d680303002c1d80c0310641361005660308000903820b08900741c144140401d00b240c03600101802c0c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 623582401 1250 623581151 623581169
    0x37032003010f0611162d03020303030c0714030f070201022406090411040e07090f05010308030a0203040c150818030313081608070807020a0b031302150702040f0608060c040b09040b1807020106 84
    0x6d9000e407021036a0180c441c0c40f0003501a0000c0c800a40c000c0c92120103400e00c14092803d600020011002c0107046500594400144000108030141507590400142c1c0c0e0f88503c0c0c60000d48011054242c907501e040c00180010b1048900300002010094a00c46425000c07002800030701030b80104240396078441c443d5000c0c00c0c081c0362400381c90382e0322005c5901885040303d81008040d0700d180c54040010010317620040c0240d404465103007002420b4284150031320a80040350f40c0e100726604140d8100b800791300d14070085022a60060050103241700d41d40d4006000190b00078482d44d952001840840220000c01c80d02820f940f10210306c0c1c42c1400b000c6801080f44a01c2299890000d0741c84044021850005480c4181c2d00401041110f0050424284030303140c2516000c02d45040030401d0340001d05607140485003415058403010100032004040003038035005082000100e040074188014000d40780107ca8020b481940c0320f1542c2501034032102304035505072007004640401440c100402902034081403248034a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 623583651 1250 623582401 623582459
    0x60a0302160b01030b0a1e090602090d03050405040c050304150c020f0a050304090506190611030706091101030506100c230703080421020637032003010f061116 70
    0x700c0801c1d1f1050311007a140201c102c040481900c241c000051004110889000c0e90070020200070b6a64030b00390310f00c414480d035201da5807035040a041c0f1098a410602001c203000080c004e00c80000c1085060017084000c02c140082e0395141000101d103001d80c0315041c0c07041406005100411710070040024025a00421400d220300d4039000309118403031810940c1040c03205581c400070300c4000c0c4190004550580e040c0100c83c1060b4050b00c1d01021111141400c40c7c04c2c1c4c1d00300425071115601406120b502140881d48950181003202d000b40c002c989184000349012224034007010141c605082907181c5084a004841c0e84984034036006126602c28040d900a6105954001c0002075840441e07944090303010380140e080040c58010040583c1d21030342103020803032100c03804480582070054050a40303440e40d81c001c150307850313507400303000141550390320121002d40b080005018400003014241c04075a0107140c0500212641c400660034a446040d0060310715203044400075080c0312846006103030240b41000000c07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 623584901 1250 623583651 623583661
    0xa0906060806070c14070b0d09053a02010906182003031801050c0f06010906090e0a0206071406010909020a0501050a0207091a03060907060801081506060a0302160b01030b 75
    0x1a50b60001ca03450000114400d80b004000741100440050001407402200d07031094444045000e00d400000000c0c519071f0796a614802440310400280100901004510034100084400d00042c003183d12488410402c001d8002003c1d54401d6005031003079500400100000c09810800d40407280c0b20b000306641440c6281004040c0101c41003481c1d085520081c0203500e4420059040e044009076000364505124062184070300b01e0000740b280d4100138100700d020300201c0d0b04200c03540b000c9421039040300164510301030b4160b01c180400984808480c0d012966140c03a4a081c0ca020100132040c4803070b42009008000000400c1c8885804c00440d591080300c0c04500b20340c89100454540c0200080724005901074201003200440651100340441d0300128698009034500c0042490004182c0e03070b4188542c4100b20801401d90b02101c0300e8090030100740a018003024290403100c44010141840f44918000556032010714042c1c3d044a540d088003020400e14600c0c40c0c10b003407440d42c409100a07038001004100040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 623586151 1250 623584901 623584903
    0x10503010b090f2a03090f2815090c180b0913110a08031206040b03120a270617060301050601020d0e030a0501360209040609021302030a09060608 64
    0xc1c40703035000c40050240390381c600b0383c4d0a03403089403000c40402e00e40b0081d01030b14030302a05200030351244254000070481017829142d460b24120038402c021f11a01c104002c440800c14801201030b0400b0f03006652488000109500c5800030300303009000424a00c000d0000140514409044031030003913585408000001141c0b0500440e08012601c3c000940040310b04140005d41d6903000300201c1e10003408902002c2e4503a02d4551955000c848402994038003402001501d141c68001c2e10040709041d00074011f0000e03400c0c4c800804e070040508810500040c1c0c10251079050305000c140f00502d180b070354605d0031503580f004c01402d60065080b0303e0340e10f515807000107003060034140900b60048506030300a04849103034000c02c559814030404195071500485220f100416001d010b000b104e400c408070740301320711210010201100c100c00e9080701c4926410750010805a0340f4a80e07050350041e004200807806d4107803413002922511660001c80e42d031030b101006010321100141d00107444940f0500081090070f03180c01e115 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 623587401 1250 623586151 623586169
    0x219030c020d1e0e2805030304030b0f07030b10050703030b010c080409180c08060618070203040b09030102070b04051f020f092209050319031b1107080303010e010503010b 75
    0x980d020600781c05200518142c03404194010311400c0c601043c0101c1e50100044514800781a462201240c0d0517a007a8403031720440b1040300500c405c80003585030915641e21400709100c01802070344040401000111003a000350415510110014103040f20206030280142a0350010601035001900d000700c005200d5014680702411a078000c4190750401c0e2409000d00007406070703510314850b00810403c002e400241a098050081c5c1401c41c0a0092032034540103014000d420518402c59941205045c0200707170390040221401e64042021242e13407052170074080380c0a44aa140000c1c1494041e4003003000344800460141c03555801741060704c0400c403118800e80c080e40643c046801c0380040402c4601050701d04010b002c4220154000e50138442c520350041c9a040340c41a00f801d8515800000702e80c0b1400841c1c0c100725500101c6800c0c2001010602000706050740582c0300800240320710441c0c0000449010008103004101c0395081766600d6845900007029080b0a0dc00c0600070b42c01c01101d0802c0e46000000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 623588651 1250 623587401 623587423
    0x106030507200a06050910240302090c1c0f0e0106050913110d03030603302313031a04120e0604050d06091101031116150219030c02 58
    0xd694000c4260324890700384541070b544082041c071400d114000001c40707601403d8442d0301d02002610803003445240c164160307201101c0c1c490851903203001c981c0b01014201c0845042d40e0b0141d03800340b07456941141505030352213102d01d03403040c2c840620104038500c3c0304c5130000984082510018003500c0300b10a8014240d070001e00886d644546150000340d20b0040400d807404402d401801403200e104040c0b00450a1501d0041d0b06800180d100d010500500100018204e0170a005013000d6040d101d4580720300803590b550819210800040108518182041009089030341c0961000c265032184400145118070000340310440344107441031072482d21000c035820300d01e00c919042881c1c0300e8908540c1000325142e041e01882c00707502c44806e0001140c551200302440c1145849410b002500c01c001d420945204948040400e0405061170142c08034024064107680c0382c42007030500c6d07294540031441d003041c4020300c14142a0b2528408600104c103c81955a40c0c110064262010010540b01f0003040f40c4030412006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 623589901 1250 623588651 623588657
    0xb13030e030c1509030307020a0608010306050c040e010605030402010e280e1b0a0c0c090c110a05121b011803140a0f050f12010f090e03090d120c0b0a05040b0106030507 74
    0x2901e8003c0082c40018144400000c0c00d403840d01034154001081100c031030308480001a03401006004008540c07040c1500034207449951410540b80906010300c5103c1405080b0800c000440460b0459008400d0411031801c020207901404180c401540c000080c4084107031107946c260400011104141000300d0f02450446110000034200d5a41808590348641400410006001c91072000324a0381c02500024000c0024046080e01c00004001c0004281c0f104e04003598000101c1000081c00c0040c482d14007110301c0d01c07026140c25034030344a040d00c2d40729940180165400c0180746080f0710765128100c04900e1103902c50041d60086048243d520b8000d4428072004251180201801640200094910301c4d01c550701c460f03d00f03400c4107840d0364a450701b0380c01040410300e145410710802a0a00071a0841e000b004001d5060a02140c0061b0480d1903800300034010140001190b02664451103010380856040310209502c0c0c14407801407002020300322000d840840001c0008644c00d0710902445028100c165 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 623591151 1250 623589901 623589919
    0x30b0603010c0507151116060515011806030f020c120a181a0d06360903121d0d0c030e120d111603060b03070602030f040e0a090b13030e030c 62
    0x1515045c0108804412032494000078802d000c0c80c482c03036004098065100e442c0110305420008860748592b80d43c2101c0e0340c1804080c0e98103142e0301c3c0c4000d0305101220581d14000c00c01045481d155030013481021032145450090490801c081d2000760014104415180d952205090100016141c0d07040140910315041d200c003110070100d0144100580160281c002c1c0c0042c840e07039202c503003050620450b0703072020140c905e0200024065910040120f007200e00e60b4800e021080f587e80d002000340040c040d040c41d669a03100d04c00c4200082000c0c184d20407003840802c880c040389410001909100001008070001070010801e521203042200c20f41c0c04a08010004104010b028070090785e502c40e01c4268450b41d0300c1024003241c500c1411034000030083d802200e0018a0031804800e041c2802c4c410f03003056081d176000b0801c0c00d668115901c125802c4841c00304201070140c076031840c11800f0b45401d2201074009008182801450340c0d040300001c0989100f41c4a6144414007030090548134440681450f0703004c4415 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 623592401 1250 623591151 623591183
    0xb060f0d02090d050c1f09170c3703020604030f03020a05121c0e0703020112060b0318370c210b090a02030c01030903051201030b0603010c0507 63
    0x46000d88a030030342000001d03061000d110045076040220800030780d210380c003041d054041ea04201c1d1800c0c0410b2103c01c030044026207144400740ca140498480c80c80b00c1008000d60303044a650500c114400514018400556118951400c40300d0130303901303480c00f8081040c501040c1c100a001000100403a54050510340c00c05103551528540010f000000b40c00358001c045040700040c00c00d001c0280702c005080c80c9191602a402c1005407128005410640001c1c0780c105914104070002806604807642468018541313540c060240000d00702650007a48803100c040184203c0d4010324200032488500201182c424800d01070810401c21550311090503401c1c0c80c0c3c500004a04144220098000d0148488400055440e400600c0c0741081060941401581d070a0b40010040341250941d045418400140860565500003e840e07481440180303040c103603500341101c205401036040d85c421000040700345c1c03582e40e52420541c40032001150118829480c042d03500040501610580d01043d8100c520b45081c401c2c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 623593651 1250 623592401 623592427
    0x506040b071709030c0d09081209130203070e041b0807050d0b15130e040c061d03010e1e16030b04140a0303061a030c0a0305180d080115030b06 63
    0x60001c81c20440c041110030b0807011a103140a000b411000000d65807045000103040c1402072140454082202c02c08041068400005142c03580c80d000d511103a950342180000a004024800945508035001100304190309401045a01c0380e80c0342501d06000c50040440519079042c040e072010004207001901080c2c1661080d40603009400e201c48001802907405e0002501d801c150345004079503c04001510010704210105800041140031104180c504282e51110615042805000101300040199a04220103c240104c0d5403102600801065080500c040d482d40c044d42214148014034214509807414006581c45d080c1c0c0c00d01c400c084000e800d41e560b1030110407002c0d000381c41503091043d05001185091181048084c4640c03400501d1500d8019420400301800c0c01b4032040100510410503083c1da404100d4003550598540094541d440009034058180044418160391103503520040440303820110140c160307108032205d05040704118100b00c05542e682105a5000001402550032580d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 623594901 1250 623593651 623593673
    0xa0507030b0307090207150501050d06150e0903090405010f050a030f080d020a050d0f0902011202070c0b04080109030e03031e0304051011030a0c020a02100c020a0b120609070309050604 81
    0x4000d00e80840c08084500000f49488555041502c40c20350015640c030400044126199130101410002d104941c945030000b0720101404801030210341d110b000d900ca00206940b114000350500802280761030915141b0241e482d0031014044c0e0090345418004030f0044034000c1550111400100703600a014259920f152181d4078400c01240d00603001d01c0100a136081078000b6244907140f5658072074442038903548210607500c80291407000c4601e050314140250360700407012800d6800030100540d50711101d18045460792501d50143c081340e0300104000c11145010f411461145020f6612003032801106810580c49115490150143c1200b02540800e00c0c25050702075980103008105071045810151880b509952070401c082061031000000c00c030340c45c0748a01c100800c80c0118030041031201a00d901060f01a50031507035100074000304c0c980c14002c541d030750240200079000046205440c0c00b03400c000a10601c90a5075940d00c111380200000d03070035a2080c0704500b034164000005000503106d985880c12421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 623596151 1250 623594901 623594911
    0x906010b070804090507080403140a08040602090d0218180c030d0f110106080312010605030f01030605061201020d050717040b15010525170f1222051506180a05 70
    0x114043c4000102d10b0b00d04e02c1024403807542a141c0d40498940b514000344981f10a00b00b901500c88184100c600003030f84040c009900c241c1c4104016030702d401c4940080d40d501c3c80e50100075070002e5004840d5000885000c081d90080f2260341c2e415400d26459034040703880e4084005c0c0300340c1582c05001924820b40c0700d0b0f0000502035019081211500d503c11288a0075103002d03412441c141d510004e00541c455212008075401003100e454514114202004615407d107418400030303201a465202203070b01591139400103500003003420700031551040348aa03034402a02e01210120085002c505014600e500a408143e100d0350b4045c4400000340e41b1b81648081146101c2d0b070050420006000c0d9034220540e81c5021040150500c180d03540c5005d2524016210280901c01ea540301c10040c400052060389001c1969074100c184054095940e0300d8010300c0520a2500310b44c45e01680d98000740d60103219010542e21440418030b151910340b69038003010300558007008042c8050131440900068402042d55000b01d81207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 623597401 1250 623596151 623596163
    0x3060f06050114090a1e180c020604060e030c070905091506010804030f030b0d0f05160807061d040221070e010519180b120105030a110d0c050409150b0102060906010b07 74
    0x6581b50140488031907615502039280e0f4000740000e1118880f000344035050b59580140c14400d42c659880025101c41d005080145016200d8100e401108014001d13121b400b2840070032544000e40c2da41c00500a000c007034a007030009008000540c0c88403000160701300d11600068440303da07507031600d980c11074016000c1c0c418002095510380841d0003617a50400d0700445e6602501031a8001d0b481030900d142030640c94000215440c49501d4200000b80b00862800c044034401e0400a64841502242d031080c048146072035540288001034040c6884525102c000051a080042c1251030b50348040c04d0380c040d001066050b010590500c080806082e441d01558108403c2d440c1c002c02054a40e08040400e04154024800003a004501030710641280494180105800c600500400c0b615031200f005006544040a01980c0e040d0304d90300900c9010101c0c04002c042c05802000509403506041c1104940c54501e0036203117050001030055584001a000c1c09407139030f40040c054592070100c1c0c6030165485000d04a0b00c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 623598651 1250 623597401 623597419
    0x100f05030c0603040b04050304030f0f3014090310061706010506040b2503090602010c05120f090a17030f130b0705030619030506060114040f0e07050702040f0603060f0605011409 78
    0x503900b9649040554807032441200c0104183ca0103041410420100d41c0070050b0200000110f02c1c07240003202280b081608000f4200c1501441c12150fe100d4801ba042c1c0502ca0400f800d42d4a442680c80807003200e40301e80c1544030310f03140810300545079102032060f198841c006100500150003180024034003c001c1e00e01c60418440325000c0910401000201035010411000f41007205c0d03502070003031640b03d0540345005461306159417440f03800031802514a83c4054100c0f800030360702e00010024501d2003a004004007041e9111002e41c9500b95204895842e8518500d4000c274030b0700f440c55803c2e200303402da000c0305140345ca03614113008860607000107015031f0348080100c28002c02d81840462000241d4007031000742c102458680005084404070342e000303a0f80601c081200f04117000c180c2c9140000e4a52a000031300c0b4075101c412044030f82d802103c40107503111345050800a5050007507030110044078410780003400a00300100c0980c2c104c515174418140421520004451b1148418005040301e020040136504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 623599901 1250 623598651 623598653
    0x608060c030a0c140423030a0c050f1519030b09010b0316031a1e1e09010b0a0c0f03020a151e0e1f1409060f06033f03100f05030c0603040b0405030403 66
    0xf15012a001064034100d00c2720300306003c0d5041c81102c9403102c070825210b000c00e20001159601072440f031010310000301c08625005c040d001c2d1198104000d0800000c101c017040d941c503900790600c0c0e40c1c42501c0340300e04041040c030f101c69054042d01074010180e00d46000c060b1031132400c0091042021003c0082d08070000300301860351041ea5840b40d814840c1200942d03520313458040c4000d00944443c10781101a1504040c020520320681c0400c081ca92540d20175417203000300ea030610b0240c0c0b800c201c1010041c040b511441c07500210448541c01907103030a660041d04010f0422000c95082160f140c08220100d9030403903a8240c0d5040441c80b0010861881180c0c00141c44200084200640c0b4081d030350142d20781c01c01014024841808280c0d240c01600403405814006d41035a2507020140080401d03060024050480c07805000785102d0761454801c1c840d004699900d800030380c0bd02400e020b8000c035819225000e1000c10307541030004501a1000c00940181d14507220740d12034086207a00140b007111544400c00c13000c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 623601151 1250 623599901 623599903
    0x21b0907050d0c1707031a0f2202040308030c0702030c10090603020c1e0d0207061b02090a0e010501290c1015030f03030507030614031e010608060c030a0c14042303 72
    0x14450170055030002544104d940c0c0e4207441c200d800c0307003151082054114a404a550703004000c02450f240b00391030b0440481003001840030b8012680068010f003004401c2001c0300d60088002e2440b240308505a40580600c0010050301c508008500c0000410807501448024000e500030301c80c1e000c10a0854807a4943d180c1c142d00141d80b140c04c2009950880005113002d04e0301005100d020340000e0801d03540c591505508204454002d440c06445800808007103200c0b1069a404290010107650003813102d0741c0c407a0040c11228000c00c0e085096140401c41900c80e00c8841400c1d80e103004842d5024000040c00003001802034401c8040c0c0d101c04001c04280000041e002c404c00c01e503070f1842507c01050904e00413201908231142035200d50f1321008084582c40c071a40d80800d19941b41c011030810361030880d1420307045500400164014103081d102d40428012100204009148125403070002800504030f0081d04403481d00b100700024015000c180403e200d011069a04051030504404d41140d194000400007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 623602401 1250 623601151 623601197
    0x405100b12060109091101090614030403032304121803061a03031909090c0c06090809040908030412170f090312131b1d06060415021b0907050d0c 64
    0x911031036172007800a040000030b6540804c1d4100900b400c03500240345c0400074107600b412896480c059000003000400302b502a501207607040c080300b100420990503d070b190080c0380c0d02c141c801303541c81c1d25061100c07903150307105502c566080004803818078046481c60741d40c1000b41140f20795019101704502544550342d00c1c20405404a000074800c0d14000740210303c0003514280c080c0c1c000e51035290074504103a0716290440c91036402c40743e0091000880340070900b01b070070b45030080030f00d032076482404c001070f282c1803104890144d806640100c4013014a40c2c2050f106030b41481c1851950500b01000340c000440414049081e20740c0803c0c4902540d01e0100c48581c0d4052140741200c080c1c40681101040340b09001c6030502d640700c100d5907941d00300c00c00390500030000104910111044400c800c4140043e0098a44c54186d80041004c01000102000401004ad40b03501540a400010703000d280005001458002800e0f4000d011036118070380f500702d104144d40007a00c410200001401086000b030600b042c1c1e070000d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 623603651 1250 623602401 623602409
    0xd0f060e0102070b040b010e0c2205060a0903020102190c0e0c0c0610030311070b0306040b01120f0c08090a2402130f0f080c1c0507031205040e09060405100b120601 72
    0xb10280d45d16240c941000d0501041e046041100b4442c1c0810103101417120850702404007204034910b00300c00c280e80d88441c840c1180c000a41080c808100410160341225103841528800d03000c0c0c452120941008407880d8180150191203001c260000700640320385490341e19080001c4c14102890002e003503020510b0312200340d40303000680900c01410421316502549035040c1c0f480d0000038090b120725201596045020140c81c03030780306654030902041182e0280c036000d003000c41d20306000e10003403aa050841008040701148c110200d0f084000158080c0d0b0081201400154003c011078034102403201810000c500300f10607880b1660f0f0820400d0b11a0150b40c883c940144140545c1c0607a46081c03038502225007085500815160340880541041c594641414056a083c201c1c100382c80c02130b09081031442d01c0025440904000405400f020a26074000700800a0714001c05600301a41c944030002c90b5074103c11034010f840c0e07410103d212a40c8070020f030401120524002c0581300ca98021280700390502d0002c0e44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 623604901 1250 623603651 623603663
    0x3070812060a0806160813020904050c150c0304032405040507090c09060e120102130f0618031101031505040c030203041505010f030605091c2007050d0f060e010207 72
    0x304001a9240501c1c100020b800240050310072030600a00400310020b41c40501800e0140690001d844030309003400c245840b940003422048141441c0c1040358030382039248521409030750400008002261084102d0b451109400010762815146440b1086c070441400044228500d00a030002c10341d002501400d40a039000303501902a040c03900701c041040340e900e100100c0612903804401c00010350000d0140900ca1029185071900703860b50000030307009100c2e050180480022001020554650104801094600a03140d9806008200d0091030b008100d034030000708494001d510640341540300360855085249054044007240c1c4e11000090203a420041100001942c0402008240724000711b01e410300c01c268050410542d4109072620b00c200f0343c04c0c00050071300c50320381c0007003032440ca400c2103c2c1d01c0000d11080010161144010010034014403800b0400e114000d91020b1129140d011400c01c0c22201d005040004a003443c0d900c09005140c0c107102552403a60320704000c00240401e000500b50544510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 623606151 1250 623604901 623604937
    0x90f0506090c0a050d0230150a05190c02011407210921020a05010504080910020f0706260f010317190c021c200303030c0d050405030708 60
    0x70502440d080781d10008a109492800c0104840d0f201c0801e9020341035015100608000c1c2e6008540441a02400c0200c0c0001c5030701c5110071035913001142603942c16008a80104c29500c40388405426544195994031043c1d03150226440704018035840f00d0203050351400045190070309011264005481280d1a030081221b503426060715501c101040c40044c140c1d0030080207400c0242e1a800030404050000d600d181c883e04094009041c02040850021075000c402401149898035143c0410b40080b001c044c042c2040407208408103002080100c10f04081d1030040040e02d207887c8003100c020700f0f603007805035014504040030801035440340c41c214480c0c040410203403074139403540c03920322503104406100880b41c0e4000d200005e5440f01503406100000003a15244900c01840e00004003041c4213560b100200d0901d4491200c10404000f00e2a031040601505007003403824041c05041d102d200c2141c458400711401c0119000844071a03000a03000ad002d0003c4a0400d4030503600d01490350303c8100e00210b030910701 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 623607401 1250 623606151 623606161
    0x6070504060912050c060921011d03180f01170f040c0b12060607060f02030f06030f01090201080402060705150a1e0207030c14030d020d022101030209010612090f0506 73
    0x4002d03424010000d1458420603001651244c41e1548025240a4807412000548442e150740703491603803180d2407051084020010024098074000e0013802640d000040000e81010012000881524100900009050f00e140d05d81020030512208180c2517506110908044442001001e14464480c600d00d05007541d19040c1400e003101052041c3d40724040d01282000321b206842c01981c61160000010b0301d9490700c07104a07292580c090701d8182150544280301000b00407000303400705110390041000ba0180ca10392120801424243c070303d06000680800c640c3c0c4c0220b07005091200081840c03900800988049005c0030010403030113103041e80c2c61007031543ca482074001d2001d1820543e05810b80000c078110700e0403005030341c081c24100c40044060050b00903001842c107400c109004071403003944000300c1152b607114640070040094200d0a0000c410303000e0a820011450714400301141a00c1d00100704590580c038210007265154482ca50b0b1003941034a901c0c036903000520003040c20300040e2103000504994500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 623608651 1250 623607401 623607407
    0x708090f240115230403081909090203010b040b03040f02100816020105060d020f0a0302060310031103010c080c030702160b07110a030314090a0e040b040b07080f0601200607050406 79
    0x41a00108050700d4840d00c0d41c2c5403190090b000881d280000d0702ea00101600c00304c00e00d2403501543d4400b0701511400104000b01d442c501d075401440c2010358543c48401d41e21045000c003240403d020710003109004200a10211f902800a180d12174421910305280e0401da50110b01c0c0460215080400b00e46510288504094013900340c9000c00140d01c02000381d481c00800042d0348100c450006030251039801100c460903240c5990341d40245401900b40c0f40c0c1c9041070001c61300c6a010b1b034401614190380d240501c1079146018014809490055915112662551440d04886500241c6107106601c510401c00250300d50100d003140041000034000e9840c5e00b89800c1c003000c0c000507000b500c0d206084804040c40000d4102c880c58040404c8108000d854001a41c080b50000300c2c590400d031001101c400800040007140c0ca04036118900c20907d064803500c41c4402911500c01c15140c0c5040c1801c440c0000e48903503c00c071440c86c1882180e222140303c100013007090b01e0410f1021380e0350500240000805012031380e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 623609901 1250 623608651 623608723
    0x9030d050a1d0f1507120509010306120b010e0c300601020c22060f1712031005150706050a050103110d080712030b031203060102071d0708090f 63
    0xb061001502010302c100003100954283e14a0313100b5182204000c0113a15044160759416a108540d82a40c02030300c2d101602c2d036000550300d83d0009040500c0400d100105000244580358489000e852503401d044500300300c208000c001e00e11201c1c040c81411005024040d00c1e0210703480d0300c8a0b030315030720819200104124500030306650665214108403640c60b15400c51034081c001d0306120301881e03501c1714030b01440035002e294045554201e01400105440c14046d049048800210b0704441a0f03240050300902540421903001d00701d151203034001c00c12418101c071130005690503406160b180000d04c1d0748980c11a00103694600c1019610001442009005090300b4091311080724802c9880019503070700c9910788103000000f003810840a5403480a45d01130340200c1c40c038220080503607040c4090340905215039001200c50701e0051265620000348110300381020014183c4e910301510a5a0318001e041d1410748000c2d100300308600c00c20341201a119005d101c105041000d81d154051422808011410114 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 623611151 1250 623609901 623609927
    0x4030c0b040e18070801060305030909070e0d031d100305090f190609061d0a03030b0a0b16050a0b010b120117030a110c03060a05061002070509011a09030d050a 70
    0x1800c001c10302058603000307441c90340880b081c0510712085440071409400d024107907108505a40c20031201004006021014244001c010b6404000507078407400101c42e81d8001a0005030440072001e40400881d1141c2c1030b4401070013100503d064401900700108a0900d512252040040da0314824080d44100a0011403c140c0007403009002c10f4020501792680810340f420700912103542c40d03148004224443d0001c0d05c07522908050700b00007081a080807500c501049008600103441c20194018500c7d01c0541c400a407401000c070181444410300b800c1c0d1224118030301c25145441070381454000a0f410b600781a018005010f0710a485600555000c884103c06030840c00030f220b80040c0313185200d0000810b403111045103152031078041c2d8030409200d06000903618619018001c48003003003244030103604003034003c084c1505c004001c1d061195080f40c40350704500445500c105031000411180d40524414101034100c4200e6500c0c103650080024070340310001d81114003042c8042040720b2640c1d0005030903c104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 623612401 1250 623611151 623611169
    0xc081312050f0d090902160503190801080601030c030312021306120e01050103260705060c03062b060b0f0a080c03062805070318060b091f050f061201030804030c 71
    0x482e885280141058404d070054004155010039080c580c0c0340c1c0d03040480c10158000d03054a40c1c0741021644081c0e00844d04900361302049071440009001540000c1d414100d0744c00050192050342103903422115454600703201c90840703409001a280c00080440000e005145946484107c5d6245081200944040d01c030090600d9242000420100c1d01c1005107403401140454100d083d500c0c65608c0459130f0046080103841803240000300403d2801030002540905401c490303021201a240003142d101504c0c040c60b03652000c00c010100c400094140c1c00c04552080d0091505a40030110030100792034050580c000c49503544100300e4404903044c140071060b007103032100c07101d0317215001e800724040c200d10f510300c00d44240c2964540c0042c0000f840b960140a0b102000d103d03015855080e0f040050261620101c0c10348a458039034045824a9a030890841c200125403425004592509041000020300c0e02c0310140c01803410002c1c0c0c5110015007060300e01951148480c99110390440c00e0406000007207401c4000780d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 623613651 1250 623612401 623612413
    0x150a0204081b030123090610080307061a060c1506010201020906040e06010e211c1704050f031209071d0c0d0b06030c090415050109060c081312050f 65
    0x361000c0410704040001502e1030420440342c0107004a03006014042e1214000d60300c1804041000f000a103045014449034400c42e6100d440300c03245810a40e28a1003a00001c0d4410410600096a030760040440c0c0301c0000c00070000310564002181880c1d0056075100002c5d0000000c3ca00c0c1008407800103500a403080c402142000100c0003c61500d11403800391881c0079075075000180441c0c0c440e10075440c1c070040150192804603003c4121a8101000f0100100c1c68002c03800382c2400141007000c0d1520002c4181c4c2c4a80809500209450b517449000c1c0c01910036000340030300a006c0c110100f00818030100702c0c0204610314541034130141c0c2001403641180d901c996124041c0000400503d64140e000f4481c820025625082d94001c18000c250314070020341c1000012042100a82480020301408a0151000d00140c0740080003e03802000a01030240071a40e2aa01403043c10b124003622081c0500c41d012407072030300300e010341c1c444400410380e031020014001c01040801000300901c14400340c1003901d0001e02c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 623614901 1250 623613651 623613659
    0xc0f030b0420060a03060e0703051005040914060c19090b2a070806060f010e060d111b0106031a0906011512060f090501050904050c220e150a0204 64
    0xc45410064400342014158204808004442e80c0700c42d0340c9180002e010954904881c070000d4007804c40c07407245001e840340c41d000048885000f805032500c038103144818020341500340400c020003041558409d59a0610321002a811100d0400000b030095074085400c64582c00140511041c80840840d520304000790910b040000100110540e0038940c3e130650820b8a09014115106030070042d0f51a0000782d115010000902420101d00780380205025501501840203a00064420481e6170300c0389a040142001240d1142085900440d5800b60441405140020501d0603100c21001251440c0403130355500d0040082116191076100283c50214030850b580c94050315468403001d051080005008050401001d0381d48207801d02140849040c4041180c580c0340d00b600112031031180035184070070b89844000f24080c603103015020301c1107a0203030060040802982c08e0002d056800500940f01c40c042c02040d01c07510b0a1030003550300c0040246e0080540a4006001d03140510020b032000d4035040c41080144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 623616151 1250 623614901 623614913
    0xf0f0905091b010507170703180605070203100e03070803010b030106020c15030a1109180109061706010308130906030b0402041a032532060a0905121501080a0c0f03 72
    0x140c0714400d00b8119203a40d65400c18402d05000c444420f4a00c51001803147d0030150851160b280d00d03030240d01b000c000141c0f1141c05880e030b0b114040010358564003a801c3c040340e108042d0802c00710710b0000001c3c0c904005181c4d0f40c816164000ba0130030492689c0100061160a43c104514402e00d40c00310b40c4902c404035103a00560240c8006000b1025454036580070310740c01a218021110f00c0007004e4040001e0451010020340116428011000a582014000505204a003c0c02c3c510348945201a04090f444c40d6218821390740310640710015610420000203042c5103c0c41650700950103100031421a29140c8100002c6a41d4220340c19182d0440564840a035207001a00442c291031204141801d548840002e1010403090f40c00313864980c1a205121900140c02e1602c4007041700c0108040000d00c85c01e004211060164017010b0303001811848040109141810111403100c8000080c9d07040081140ea0601c0c0101c0c4c241c0020005511240c4d80c0001c000c561101c110040920805a00c12141560766013 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 623617401 1250 623616151 623616193
    0x122711030106260d1706010309080c0120040f06050a020f070b030a14010e0a0c03090b040309080706051206090403120e01151d01030f0305040f06080a29040c090f0f090509 75
    0x241203042c0c0000014001da40227900c0404800c0e00814155203910309805001d000c0d000e4103a01b000f4254442a80c44149885070054505503071000c0c98408016040c544111150742003003440c881144100108440780340400c0c800500504442c0784110354920301060700500750703014944280000c0601e02c00412030152100c2446030000c98035a0049100d10101008502074140020090300c0e042500e41440105a00098160300300e4a8950a80716030307598481c0107846a010740d240c0028101444800035417107182c501c0600d0350182c0300e4144a00101f044212510403100c070f0030141102c03a95540c540c08000808c0240e040c3c000c0100c00b4000191585d103c910340500001844002e007400076020101c0105070041c802e65000d086510f5030380c0003943d5100740080140720259240030141d441d10540303400380301c00040030150f0000340501c1c80c40390910010034000105645c801c00c4c01008070701100410b814641c0f9500000421598100c0340e451801c1413114001c07204081c1908030300b544114540e9524107140d07041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 623618651 1250 623617401 623617427
    0xa0305070f1b021201110d06080706110c0405040320161202011b080708070506063607021c12060f06210902060f0703122711030106260d 60
    0x44500101348600740c41c00f4003101c3c6507003989880003007040b04e000b5955512000031070b12800300321401c440d80e90000751030003100c103881c09505400000350b84205043c13680055401a01c6454400d45046416076032a050003103802c90207005400288402a40401d80510240940401b100c0303000c000255a0000e00ba40b841c1000c81e924461880329280c0c14801180240c95045800c40c1c02c01d41d4502d200d00e81207445280860f01c0d0341c4540c1608003c5035500b2580d000d61f2625100c1070708858950f940701100e11181150040c071041c218482e8400b00321b000404000108981ca8003501d401a81c2c004030016242680c00a4001c2c1011080301d4100708102c59010031940169000c6118103460f03e100d40020501600400c0b10194204100040b031034070b4000f13043c00404405000e070b50340400064225402c20251090104040c42050109211020064000031810b610510400b4407806411102001c01c0c20756010303a0208a542e982031705484000c200506111052140b03803000f500d042110400d004c4e10844403a02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 623619901 1250 623618651 623618659
    0x91212020120041a160803010303090b0301050d06020d0e1006050a050d17030a15060c0219050a1503020c150105030d031127030a1518020603060402070203120a0305070f1b02 76
    0x25a200784090800844201c45003211149159051710b040a10031940203210031800182100d00000350140000107490684100400b980011045500ca020280d00820035811341241c1d2591031014041c81040064507040e0159008a00940f17450200180b5406982c00280950740c0086004000780e01042c0024070703428070b140700c180c407500e032090741400819020002d8080c4110150010501039002082403c61138400c032806818118000101082d1101c14419650030069040050103122181c40c03058220303800500d4010304107442c0c288040e01d44240514621040c03160740300180040e080500030520b5520041c10f0520800d66103a41c03501151140310304074007202140071030307503d41d4074914001c0c89040300e80101107030003151341030502095a1042c482e101c8089843c0c58240c9803604500805403180c5038008180900b07507a80c803014000654040d8204a81c540135100700c800524078070001400e59420f81d907600080918140c0f0000d00005600044001072016142003191158001c1c0741c98407039564103031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 623621151 1250 623619901 623619929
    0x1a0d0f1505121204052704030203121303080708060d150507030b09160507060608010c030501080c0406180e010608060403050304060b0906090402101806110706180b070309121202012004 81
    0x400c51084030944d1155105c004100360038001890789c00030161010b080b04d508600c401d5100d000001455005401c0c0040210304680300080303066000e0190168859000b03030401c84200c0165448000c1c40340d8080720408555500e4042c40b0b1000d82c1841008035441c0240d440c444103082c00c0046000000205282c07008101002030100300300500c030f400500092100f00020310000a9512000e4040e2509000320034540c0f15480c2c9250703251034240140400c60391000120001200a28480409011211040c0500c0c0d0348644d0001003648081110510480c0244d880300d403039007458540001911420304d010341c4150042d60903ca040c3d0340306494580c005030b044510304080c2d0300702c1c8000e80b0040030448840d080c54000c1c41d40000c0341500303d0030241c910685401501e2401340c0750f20058800c1d08548804090f00142e441c3d09000740100c18000700700c5103000e401c02d000c580d5035804901c1d01d41144003c1c04c860350910030500250640d0240541212a10750b009160b0802d140410350352080d00581c80380100c070b11415 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 623622401 1250 623621151 623621179
    0x708061c0602120403081902130e0a150b0a180b09060a03060504051f0e092802131b030507050919170f070f1a0d0f150512120405 57
    0x356045a030180b1508641c1d604529190a0151008008076201c0f43c600f44c4c40240092a51100d100b20b80b03040015021060708141085840804ae00f4001c2100c50780c1c40d40d4140302100b000e06034020030000e00c05140d0f16035407a01202c0c0300a295850104411036148240f0200b8408040410180c4500d41403c1e1003082d100c40444504401030421a4807840d00240b13002c09201807a403a00c104032000107083c005050780315a03180e5002d0180d42c8201e0f0007882513005600c0b8001160300b072080f03000d494000e01c282e0600c1e140d66900000c51290500500c0d100c40341d50f5641001d800d84d54000d40c4000703410941410003c91606480140031882001a401d110b13251400086c00c1e4910a004200090405109074004e0800c0e60212555926280d80003143c252050040020303064100303540003000c2c0d54000764031b015000003101100d070090308030842d0481480c1c0c84107407440c18256a031098035a004104014800020318000600c1082110019581125013007071400010700841031017203400302c51050316000281041c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 623623651 1250 623622401 623622413
    0xc0807090b010c12201e0609060c07080403063206280b0301030506090106051f05030c1603020a0627020f0a0b180109050a0806040b091903050c060708061c 68
    0x200d071142c00711116402003000d046030000d00080d161b06020003a045110000f08100ea680e14110745245031540316000103400c00d42c41e1000740c02c1e0940300b07011140c10240c40707a80d203505a0f89601da418001480304c0c010b4020108603076209040e00f030112603281c400740c10910082140c0f48021040000c401e8100540d012001c0040350484c1d000b0107d024270f1079200c3d610791800a48138074003620701d40803560034410041994030700309420512182c401e4084414022203038000761199040100b00c2c03826010140400060400081d4106010921941c060661070500e0310b446030441d2800000d8129090815400701160402c080c21640d1a0b42c044640806610300e05002030820003060300048980500840c9040703440c01d88506002c00b40e40240c881c21031580c0c80300c081c801100500d224403e060f500038008034000c16002103138207800c09411030a0b01c552201103045900700188202c001c030700044001600c840011010b201e442d8000c03ea40c6010802c50820b0030005200c140200000b20039006d8602c000010845 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 623624901 1250 623623651 623623667
    0xe220b270f03040504060e010503031b01060302040e0303070f03020f090f03120f03011d04030e060a020c060417010609180b0901020d1b0f0c0528020d0c0807090b010c12 74
    0x38003a01100d1051403840340c810340325045407003114026400c00034081800380b20040b1440c1030710800b60003581480322042c00032120840c940404046956200713000b00140c0c0342c0303004d01c240c42e008078801103540713082003600184507100002c0400e0405105018414030b180e40f4000b00e03210280225600784442e440f102c000303410000c410b0350901400100050404d46108910041c5040380c4407032445005c489003090043d11070740c2c0115002030002c0c840001e07c0009140001c00750000200f40c0c41121609843d041c0451800d5010360001101110041118003c1181c24040c02c0c0107001071410a020000041c0caa60b4030b00182c00e00d005003491160700c00114401800d50568170f050403610414090906044010a20344088107580300021700d269800100c0c00303015003d8040000e91010040102c100c1c081401641d5540b00003448006003294003000f000341e59484c09105402c0d0050300790101141c03404000500e002c0e40c65002d150640e052811200c003581e044900e065510f40c01c00f245407586444440c089410700307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 623626151 1250 623624901 623624971
    0x12070311070f03031403040c0e0423100b0a0b0702240d0207030e1008040b06010203120c0d1404030906080a09061d0d05040e0129040e220b 61
    0x3106030400082c803151070041680c21640079032142c1000920710045080c45200c00c0b0f40c060800d8070501802c000c10f0941c0c2c03c0141c3c3c014021100e1019011115a2507410b01c24020100ea0312580320300b5503e1015001d81c42b402c03010705805c490052600b403611900701042c3c021740501a128500704041c40110041c0300c9090045c2100003030440e46d0310910301e111034000f074200351000d4001801280006805003071078881d5100f4480d4a48a42806640e40d944003845440d00900e4141103010501001e800c05070000744007400b0322801681da43c0c9036450011101d048513071070301300030541d0b40800080c4004640c0001c841401c0c4d40d018a0803c3c06035840038000c502130030300d00800030701441c075240110942c0910300000e5900c0e078a124080e50a0f80c00c00300804c44c0e49004078001e140c00212500010011019080c49411844016041c08440d9200c213207080001c03600030743c1c0501c1c00881a5000c20400103418a0703506503100543c80e07030454151261b2200390700d00307400801c50b80c124913038800c1905480e291411055551 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 623627401 1250 623626151 623626153
    0x2030601060207150503061c02030705130b10030c050d022b020a080109061a03090705060310030317072f10060905010b0f07020d1106070c05130e12070311 68
    0x5940d46480003966442c55120741011013007200c01c403c00380d030b00c80e200300d82c01240000d1916100240000c4114500c0000751001c0b41e051182c02c50009960b00c50070640d0944401010f80020000d2202080c000502d41c0c1140c4034003011702d400c2c40040260341000c01d031400224013600c01600d03404510700461148151f1800c01c100c075a00025280021200e030b8004210301803040e074030315416076602d0030150203488071401803d042888440305460340501843c0519404038103e4211960550341d800410002d81c07080c0c1d0f2420b41d980d104c0d40709000307150f0040c103815511043c410180c069450441c5004202c5500c071881220b40511440c10098014501c45c1c80c0b04a003517102c0140c2c0c02c0c0000c260320003001410148a83d01286080c04000160440b60609403145918181d03419481c040303190742000341c80c5440b0300c012a011117901d8405c441c2c589034400a441118400e040c1c401515003440e040100c084404242074050b21304295030102da2100100d180c03211802d03500d60854440341c603460181c0340c131b5070795191108603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 623628651 1250 623627401 623627413
    0xf1e050303030f1005040212060f01090e0105151b030c1203010e010902030901020c12030627070818072319140121050708060303070b062103070c230f15070203 70
    0x603223581d060580d025002c122004030183e03000c8001515000104d1107410301400619004006900301400b0b84210410f402c82d00c28036040b88080c0310740c25001c1102e5802c15961004c40c0400010343d040111421450396416041c0c155032500d00030a1001c40e05003d41d001700c540200c00301c0d90291094058a01d0344038190306840d540300b1032581ca0100c0303404c1218481c0c420000849000751203124003a00180c183c10320040b448495440310001c0d0703140c000242841c07001c500105d50183c030043c010300c150340181150360044845150510b860f4620802a440c000d403003010740d244150080b02c0c144103180201c5001c1011407084180440042c3c0b030050522007081e02e40c0d00303086601da10848050703002c14403850864545541588902d030a0660360300404a00404d44149907012400e02d1a1a5808881705411101300607010075083da602d90450700000d9040b14880c1c0b1207441440000d0203007501140081d074080414907005410710018179030022a001041c000c0c2c0030f000c280034175034903904211143c6540142c1107401d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 623629901 1250 623628651 623628667
    0x60207081b060a06080c0907020a140106030302010c05250c1706061309020a03140a080c0f100c020307020d0c0b0a05031608280906060f1e050303030f10050402 70
    0x505680e410448025001e003100043c0d5010452003100c0030380741144000c04016140b901406481d500181c01c25065100b03402c0310900080e4403880c0d40705040400030010400303902d5458040d003581e1510a03000240101805090032000e032440b51008007960398030281c0403219860611251104031900b1643e1540426581c03045180c0000070080c0c01204140c2d50701d000012401d078104201d8040441c025401502d412040022a400d000300e0440c034a0420309030b0700c81c207905aa60f042280c1c06041d80c1c40c03903900640405e11070440140f182c10700d00c080f410020b04c101d03084848000d40f244640c18000740305040c0094603006019000c00f1ba030b00581640201a035859441010152042d0001c4880303000a8040d19030242d0f00e5032040320752500443d240803640640a41d601000350110700ca10100320241681c40c48200042440c0f4021000241200003d0b0250507041c041c289900c01d046ca03007400c00103940040100b0039a01c0004c2102c4c1d001540a00b000016126001c031003040c0c01d680c2c0e220070350040c00451080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 623631151 1250 623629901 623629927
    0x3120e0703140a110603070219030c0317010e07140c070905040c060c050303060405041407060e1203030c2a010e07050a1203020607030e21040611060c04060c06020708 73
    0x106a078029020200402d0980c14500d41d1101520002868104d0b0f006a0144504000003c0e6411000c140150b03015844079034102544d1036004c000136400142010444001e050308801403444045085651445a606044003150b60703001c013600b02000c026000010081c203010312002e5410681c00d11043d0b80b0080c1c1d13500343c40005804255000ea512844a050000d8414002c0b00f1141c1c102e644003001d541940c0d1540c003040010000204242c5000c0075001014886000a00910001d07164bc1c2c0c4941c000001e4660600c95105c048442c0000c1d140d104205120708507203100c003504c0100108000c0b03407000d40c440ea000d402c1c1405181a46a80035800c11004c940c00e80c80124404094400030f45d0070358402ca9032038030642c260280440d8003034003582102020407031440c405c0e00708018141e8200211044854044403c0c4808031011410312098070002c20b06003c015804510140701e0a400c03001040c06040403d400050b5101318440c02d81840500c004020801025405807004541c1103501551070300d040004103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 623632401 1250 623631151 623631163
    0x903090932091b12150a0c08041707060612050d081602060a05041407060518150a2a050c0f0d1205070318080a061d0d030b040626070905010501081303120e 68
    0x904040d09000001141510901030359102d0ad80200705911510700b04820440940d0150009607401034548201184a0360b0110001c02041d20441c000c00300c0d54408040101f00030009001c810540248403440d404c545d5002541613040001d030440045c061310340f481e05100c49490180580d665000e8010000360494101002c0c1c801d1880a0300d01400da40508000c00078a107010b0b500da07806807075043c00303040039280c4156140c03661080303004040c1000007a0500361070b4102c0318060084406134040c81001c2568140907480e064102c1c07080c0c07602d20046070313034ad074400756220300c4144140108003001c038451381898890b010b20451104050741c03048000c0d40780c103149600c031410401c064030141e091000740c031403114492200a03500480040a05000006038000b1009000411030381680712351100008100c0c08609a030446260340300814072040011900441810310308554460802140750000400c800d0f40c1206030103501049104c036003546441d4901c0c054031140040840d40c408a490480c941c80251000500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 623633651 1250 623632401 623632411
    0x906070b0c0c16060903030f2c040b0904080a1d0901060804020f18130c05090a0203070809070f090e0331080601050609040903090932091b1215 63
    0x107403042500c54180510f26424103119a00010301805002c10100f4886c40c10401071840074901102e061500361124241150400d40d010309603681950001c07141d00d020b224180c00c80e1015541c00c006c40c40c2a455940c00c40c0a011785000612882d01c43e41390007401e0171211200d104400818410103035031280002071503800d04580032405600084014002445d02402c4200e11041d001c0019095a0b100d4240a503002c0204c074003114407180010700410181d4403040f4151003200d0507540103803a0701e4007034401404d41e8000380404a081d00040c1c01801024564509801680e40800001c20205000d118451851040c021203d40f90001031902500b0003007200310f00022401c40010030521540c4450003680c43d18028850540e005038200a401c3d12800c00b17401c0f24501074040d0a0a0400340d035150b084000b62025120740d00d5440b1440a1a0740d0181d00700c40201014141da00020380d4589410010140d0320070301c034480d05821034a0307c0041035403540c0f410700c400f20300c1102c081071700c1c0300f000d080001d910466020b80d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 623634901 1250 623633651 623633653
    0x70f080a0b01080318010f0c0b0405060601020705150405011803050105090a23070e07210f061401052a0703030e0a060311040b0a1403130309080d140906070b0c0c 71
    0x145144000b05a5501c11246145501c17101710000040d5442c100200c115028048001c000e071003c640712001c09403080d40580054030007440e040d00024101101a0080c51198454034500b41c020742c820400d48041d194207003001d00004581210b03601542425030f000034007940c2004100298050007103081021540306e20400495040582062081c80790a070202a01030351010404000c2c0140540348150410329034246507810f0715008044540c03036003d50079280c841070349079215080040f00b60b10881c0300800503007034540d03e10351403800000c04030300c6510046481c500388402c02c00c0600d9040b00d40e113041d03100340720100d4211660b2840c002c1c02120031130501c2c0c1d1141144130701c00104c05002c1d0042e00040000024403a20341400c0060582c1030303420200300e04042100c0540c26442c107203041e13070080d8003c1c40c1544501c3c00300e0180d0b20b801010323401960062140341e00a0002c0450341e50b0482044081182950401b07a160041400810f901d80074040c0060000380c000d5060011144c00d80005094074210b0710 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 623636151 1250 623634901 623634923
    0x813170f1218090c0903030318100537050a0b090a0e0c0d06020c060103080d2a0f030b09040c18090206030604020304020f09040b010f0816051002070f080a 68
    0x11041003401110000c2ca030410001c04081818905811a80d034800c03840c910090130194110082450340e0400c84030025524034008218801c00b40800607010200c130381c6c01090000b85811820700d085c1c550880c0d000703070444000820031456040e40c0c40b18891600d848080c204900d00d42004080050840c04907075034003c0409902003a81c408044c02200c10030754010005100310f600d01c41c1480b0f0b00001c0c406080d03544c01d03030901c86d580504406201c2c682c003c601942d10300342c444600300a503500312104c44481415000c0c84014207800c40500c1250186214224185114181d8240d807050b005085280301199110b03090008000410485495a10696041c041ca25101030355580c020340c1107520031040694030050a000060302e9141a400844c1e00901c003a1001141c2082c40d80032803503036041078804940c101c9800005200b11403040904900400824008001c07005e501c8101000707280c1e5034040c00340100903509001c52440e00800406000384040004140040c1e178611050351039070040c9000700c904000342 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 623637401 1250 623636151 623636173
    0x1a040501060515070c1401050c070905010e0a090c1e08030c0a0606060c0f0602090a080f010b0f01090e0402040504051c020c030c06070221100c0203031519030813170f 73
    0xf0000303503821103030f01100807080141080e201550780440104964100001080312407440303581402140000c001004000c00c1950411800060f0351800400c0d8580300c500e46100d00010030580f501880072115405900041c1010400c0c4010214400c1c1c1c100309018400011004012240001c0080c1d580d0b01440003040b10584952044412600031400540719140c00c1c0180e0002c12410f82c010320a4100080840c608155201805810200c02c00c0050405940d9000171440794209120300018500d42468105031880c10442180c404500240010340119036983c0050200303c0208601140303c1e07c040a08901a419030800a5452403c0c800c41030103400344210305481411b1a10640700a20741c0148034404c041c8480d401004d41510300c4291006921074080601d486001910811400c0a1691f014643d60700d02100d000c6483c0044035400c42c003610410702c000306004a0742100f501a030380e00c02d0381c80f55200200d815035040780320282c000103540d0120000048107620b00164021a480d10703038003507405030020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 623638651 1250 623637401 623637439
    0x18010e1c0c050d050714060d230610090e0c12100303090f18180c0f08010605060301152007060f0e0103051614071a04020a0b0310050d1a0405010605 65
    0xd05000500d2a444005c0900c4805074003143c08074030f100c02900c9581440c0e03101103904107450b40c140d045030106903c4507200030f048400d00500d42e4040820780385089110380042c402442010940320b141d00005c5240c3c08510070098842c00c079451000340b650a0f015a05080320180350b424858071048000c1032001e0300014000702c004402400300d44441410741c0b094404804603001400600b035000b2814105290b0200009804403d004003074040f4810f0011410705140c4100d003100c2164129920a00d0144010000140e8001c0c40300d224041520340440003041003188000505160402034500b402043c1012407007944c80714406080c03902513503503403032030803000c0005400b00c82056840d0a11071140040803c4060301801e000e2010b4030b4281103103480d0138460b44604004400014030420000c030444180400c2d407820880300d10183c4618050781d40780d4145100c607407802c000f035845498000c0c0c065207492804d00ca003000c5840032800043d172070454646002d1405034004d00c3c035400b45601c1480c55030924401040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 623639901 1250 623638651 623638669
    0xc1403070905330f0d050a05150f0616020a09020307170a0504050a03051308030313050f1504170f070c0302040c021618091a0907090504020618010e1c0c05 68
    0x200c4100040c05400041101c11950000c0d0404c501c02c8810404482421010303c41c1920403540c40c080003500b8103145001030f04e10350140d000c0d54462070300d51100103903a0ba05d002c119441c070008090b416005840600c003040c4000c500d540107419551002c0200100aa0000443c0d0350010341c880508015a0341c0c103c0480c102c6406880190260780130b0512400068000d200521024002d50610114290354504441c5180d10469012044a92020360311041140c2003001c1c00300f80c15001c018243e204840000c0d090381040c020300c0078081032500144115401d803403404440d154031180c072600da030364076044c00e001200001130310007280500d2030002048207041c8041040b808103040710444400d182d18140341c031420440181c8041070004e03560428040010245040c0c0501044081c01c1143c1030302d8400403680c1444a41d0340b1003404141014200401aa00ca1084803102c04800c20517852160a130700048443d4001614000d030000d80d01203040c1404002003210417900c5216407840b50700651510709004c03101d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 623641151 1250 623639901 623639959
    0x31005061302032406090a0f0e01060206090a03050703210207050708061915051008041b061b2609040b10020309120a0f0b010e1503060a0c1403070905 66
    0x20062002c1803e01308404000d0740c001c0e15004066034100094440010300e00c00540e4444900c035480d204041008481400c10b60b4014030702800549407a1818040981e02c84c0007906c8010300f04030000035603030101350090461703100c600c22494043d4860381002021170000d501c0404180c441d8070410310002135a010000e01b441c4100a54011484c40560074004d54004d0152004c1c100c4440402c00e41c041099180d2a81304ca1071500d55039254012402c09081420505100f005d4103d401c9215280034486140c1120300010f040804a800c042c2c3e0070500d0801c00c10911140e032048203004450500f5014858165014100c1c2e00c1084408001c160b05140812000c4501e5140380c0016801c01e100b0f0080c185071005441d400030f00305030b050321007040551f5110321080fa45c508040b9043c0780d0380c4006120424807003070304a51050b105803d1030101540603002950f540001403414103100c1c0c947c242240102e11445849140850541d6500e480781801c501c09044d040311070098034029000308071b0450320f400542000d04415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 623642401 1250 623641151 623641171
    0xb0307091e06021f11030a0b0a0f0f050d051f0c030c171b070b0a09060b01020a0f0602160204020d020c0105100b0414040b03160e130c050909070503100506130203 71
    0x440c08000c00b8507114125082000070704e036a90200702844494180c0114420ba030001c0002a081401c00100b06104d8555040118600c1c8501e40c144000c0e201c0481384400c2d660100c8044a03040d030399180c0b25241480407a40c0300710746207080444c03498048107508074140d45101a10240580e15084c14116082d0a03a5002d04ae02c000c8141c001c900a1030403680c11007a4404101411403510b0725031744584030410b01c1a510015403950390f480400030300189100303070030010300c0920261404040c00c1c1c80d607400007400d503003016110b9680095044151420182d085401c99405042552a04440c0705520000d404c0700310046159420600080c030f101c1e0b02c0204140584108a0303889041608083c800540c107d0145103240d0041da8803080303400c03140d504114407200d2698480c0200c02c0c2034102207030001e10040c080c0001d14941c06400c641030005400748500d204be5401541c4c0c03070340f035942c03043c1006182c4003859000c10b0300b40c003418540e107070000e034180c1025100d1101a01c40041022080605008922046a4180d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 623643651 1250 623642401 623642413
    0x1614062e05151303030801055503140106060302040305030a08100f08030318010209100806240307020706020703111c02041104031703011406130b0307091e0602 70
    0x300d152650020807902c0803225010700307140003403050301000721040c0c100ba008502c1c403200400043c54480000854030720510764508c141d08401000d03200400700700c002a007a41c0249c00c0280720b03282c44030301c1200000410382c0c801e10303500350349041204522000c00e500500550800c803012035214064002c0720b003103d0303011005503e0700340c0e5950300300c03400309002c0c2110b840e2117030311180001c00c4140d41c09603038083c18103034000d5a924284408000204040781450540e82d034014001a030442d43c0750103c12910034814200000c4c240d48180024840403201074001e020b81c0d80300801c0040e035214403400fa41c4a14125001c94990039142d0109aa480c0c400b84401044d06a02e02507200e214101414800f24411010620004036166507002409a6805100754613064602090400038030240502183c0b5169881e644a4a154104060070010a550b03c40c101d02611f000510020303030524601e620707801404010541a101d04000c027004150030264850b440303940c03d00924610704903c00d1401c1c00111412a001054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 623644901 1250 623643651 623643659
    0x6090a0b01050607060608010203010303030c112b1e020102040515030123040f0e06070e06040e010e070212072603070905040e0a050111040306140f0c1614062e 70
    0xf600d42d03c18007040302c516840e1000003074602002d00140d40614400c1d100403c1c40e13130500750300603d256461107036041168440c200036042000144a041140300f140c03442d41c070626100e01c0d41990b0200d0300810070170b03441e0315426080000550640c00744c025a24110b070040c043c8001c510211840740070a005042c0c41621150a01154071412111141d0b035580107400441c15265880403141101d1104484110542090003008451907018503e00100501254803a003004c4c00c0101c000c123217001c14043c406080300b00d0404246680e001300300140c3c041c00c49041d580d543d504245011501d20421800015170403042000301c041581a82c4182c901c280d545070750700c80100c0e103044c0030407024040e188000303c42d074040c1100c0b42c00480c1081c000c50781403100180d05035503114554500b40c1c048402145010a11043c1007081c040c0010340c100740305411019184100b40c89030351288045062040c8510000c1440c040d141d40c0f04801540800c22070f11514500880c442204540d000c54044030105420644028640b220240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 623646151 1250 623644901 623644909
    0xb040c2402060a181e0c050103060b0d090c0b0c150a0506010e040b0109090c02011a060408071e17060402090601030513321c0306050120012c06090a0b0105 68
    0x4420302440c0a422410205a4a45101e18030301948091700382d0154410182c00d100030350a80b08010070b02864104503941c50502104014090003601488240c0c40300c9544040c00640781c00240600f4805620950300c0d80c440d99141d030f41d41d01041d200e10401d84014000b840c511140e2180520070481a1500603440d000d9a0403c001404030f102c003503060040800000c41c000540744503420074074001d40c000043e58801d0380d2500e80381d180703402c2d222031080400300806c6c00b5958011032804200d0f0b500c00740c600c112849112040032a201d00c0e800100c0d607502107a080500020000459501550080c0c0b108913480c1c4078070b001103058420490300043c00c485680b0205001426942d000b02100610b40c540c100c4801480131003841850011080260b954010002c400300003812904140400380e041c182002200d1410002030540138200803003045035400001203000f820b40a4000c861f0404859440d402e946280400d591007036260120100e03003600c215000121010ba00261030601c4075005845884280e103004200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 623647401 1250 623646151 623646161
    0x90c030406091203060303090b1303080f070807200a03050714061b1c08160c030c02030106080106062307020f0a0806011514090f100c0b040c2402060a 66
    0x12a04250b4031844080414030048a0a020140c1139601056141c69810010507010136a0802072664408029043d1103c00f80a200c004aa5000100c6034031500030031a403014030b02071641d0141c480c020003d107000820825044241e4a40a03c00b885a8440c1c14042842400c200600009085500c5510240100001c14119480070000200901d25040509052031310384184540200c0305a4032101006510100410f18000002c0702440c120f01140740910316000d00003400740e8080d0501070a101c8010a01d0703c5a0a2141304d03031707000b82c001c0c8059503440c54114001d000754814440000c10a6075421080ea0441c01c1d026058580e02c1d404508181031030b02002020700344050071035400101c0020000d5034000034050f00e8024202c00c0c00790300207070550b1540a088680303c071820905070501002003100907030340d00800d90030643e810780d06208259421750003500c080003182406030003c842c0c00104001c110850303901c402981e01151500b9505040c001203c2c5034121700b280c0b01e1015030130040c00105003402039404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 623648651 1250 623647401 623647403
    0xc1e0618090513080d0b0405010506030c040608180102031008060c090618060c0d0905010305060a03050d121e0509012003041e080a020a02010201051b40060201140402090c0304 77
    0x400140d500f15944044103030740509505007480c0d8450021800600c0c0c28414140101800d440c61031952601190702c654520460250b141400941d40c0841c507241c1c400d400421612010b04021940d0303050017480c2038440f0071a84102400c80c0301d058001186012220282e0790444406410035080440610589000d0764250f40803e402450034044000b40d4101008003000747c9815899541c1d100707080800040c1a02e400800701070090000d120704000042000910415031190351a100c04c80c141d201c0c2c0f50601a051000103404501e612441c5840350b10440d0340160300540044002b00502074402c002c101c0f0340500b910030314081c05014800070b404101ca20700d441e040600c40750309a0840500550b110700c1603410030407444006a01c0b07000c0241c21560248506500700003100001880c6448032800c0c0742603480b400c1040700c8241c003d00300c06110311005a060070070b10b811305025950507071514454900414030511400c401582410116a1516200c104c0035016030740241800b10240d4520050b06400e03407000e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 623649901 1250 623648651 623648671
    0x30070c0b150321220810110306120c042d09081603030f05280501080304090e010605120a0516050105091c0210120c0806030d0810030c1e06180905 64
    0x250710700303045004407180c40c040c0c0d02c1010a07100034104444d03149840b00c90190800b1140c5447c074041c4034802c1c05825a603210204846941100c101081000e0800090304002c5030020f081c8080e03290501680800b80101400100c0740c5c0d00f2403548405003e064840c40d05010304003003020400030b200039020310380c070800d160b0080c00c0114454a4400143d011143c0c02c40d401345108110b80f032074040d40714000701d40c001c0d00c51200c5000c0c4000d504000c00c50303803288254401d82403005d558026441c0512400e411420081000800c20690107010110b0700c0c2d200c13843c401381240c2c00d0280c1403d90440f61100c8140c1810b41b001a9035080c1401002e10920414140c0008502d482d81946480d500050360f0f8604034018250180d500c045400a008000d00150ba88410704542400b542c50100186600c001031080402d214500c0c1186103a1038112000950f19010303040078101031000c41002c64403410100944800c0201959000c031800d6494108a41d0300070400c40c031680c1c0b2240300d0010800608070b60000c136000701c0181 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 623651151 1250 623649901 623649907
    0x11041202030f120d1d060721051510020a110f011e030b010905010c05210c030a0e030d0908030304060c031508102030070c0b150321 58
    0x4030460f01d404035014180c40502800540c039040c180560107444004805052244c0e0b15044004a00c0d4685030028000010030404e04481c3c4015a5004403141e14500200d1040010342000802e041c400180c40c0d240502400300c00200c00f680030300c0041da00001d20342008800f00c110041030100850b078841c1d004c2c1d203070420111440120b08403e0005480054060603100090322080407400274280c88190ba000c035050200a00d540e4005c528042084c1104590756400c08510104816244450f40209002e582031071101058811840b9088008001003c3c02141107504009200c4d00c201c03007800c0320b4010500140c0050000c60001442070b0800c0780a940181004920f00c08091051201c0024550001c1c1c1d1035803014907201019a207034801d4001180c10303000701685503120f1703499520843c400c061000c0020407600060740251840d410009415103907510780d010842c10112001481d6450346103041d101c0803410700114140c900b140000403090f01000e400343c84101e03903051400614500704076041038800d82c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 623652401 1250 623651151 623651173
    0x5031813020a020d0e0102120f0304020303041508220f0f020409171c180f05030f04030803220210030c1106010b07050613020a03060c20060115031104120203 69
    0x18005820511030943c0104400044444001e20745204601070606642001c10071030007032292002126003500b1891703180307640c940311880807a1452003664000c0c076101c220344082d502516403203900207002c0c0342d038040090144445180d507048840182c20005200201c0800010001480300c049001064001800011032910b9511400000b440600700200080000100d10f040d1103c189884140f022201a04100e10030102c0780300180d01c0340344c0324040e0940210008034010004100101e90383e004c1c01d0190300e5290365480c500804641c0048d81c41401480c801c0e16901d103044031b030074107041d4041d0f0010a0001800c0d900c403010f9004080441821041141c1c2d039004000e582800c2020500900c20034140f565940541d007000b9090801c0681504000081d10200d040940e13501c502c41c20680350015000130301d45441c41c03810f4501a03500c12100c044264141800c0250030404501c081c1281c00200070f84015002124040b07085a4800001d105003001c2030109010402000030340c6440984068100d903951558 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 623653651 1250 623652401 623652439
    0x19080d0924270b0a1107140f061e0310050d020f01030e0c0603011202030d020d3504261201120602280e0a0503030d15090f022203050318 60
    0x30f03400042e0816800075091a4480c0e0119100300d055483d01e01804019003000d0309400170b00000c036801c42c890741c0c1a0200c2c426541c0c82d5070440e000e581e241e11058001c8020b50b44446090340003110314149112005e50700203024140140412150b940c000c080581d802c968000640040c038018000300014441c10110100c00e86604000314060849800d5003d000000ca1041500e042c14004540c81103410883e40d414049802200c0c1c520500210002294210b80041c940709071210140c450035100c0c2d2199060200740702015810580445545c0f07191440510780003800705a500c58a400c445015503681d00400107070904c4001025410720504025181c0100c6001c0284540341062541c20300a028444002c2c42c0c40c1c0207480b40c03032244003d4481035225032818001039160300602a10980060b240c14650b07845501d405400d002800308407070100700d481ca450303850780f00a40180000d4000d1212202c0c174080c0e09060342e46181d003200d40c424001c5190100c08060300703000e0b01d09001c0483d0400030b00101e40c450307000c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 623654901 1250 623653651 623653727
    0x41d1f030312150e0403030218270c03150d02030109061508100605090402090603120415170c040302010f022802091b0a030b19080d0924 60
    0x40203985000c609a10342d9035501c01c40e000360041e5900e6801c4071100304000e0718804045030b07001e5010304005880b41d00d088500d0320b06010380d501080c0d00851010381d40d851414050307800200b040074144540f80c2550b41030640406032006440a0564400c2c2c901d410507103140424030301d141184054008690b0351003903a250402e41d048540003040c05007121205210f081d030200408070b807801c4600c5017407103041e03d00400710300400000380004e80600c05500008031161420040390700c0e81804e0f5810356645a507110032560070b003036540090b00001110f001d580d5481c0c2c44500032036030094801c4005540303000d00c3c40d030040d601e100c01c0c0e000c05010f41c044c0980b9503844080030005009081146180c030941c413000f86c41001400e0342c00038aa081d800c28600008010310288905490b5a0081400c1c001140d0704942c0001d410a400503118088c0c1c8180c80c0000b140082c4089900c1400f01c0c2c0300c1c1ca43d01750580d12103040c1008801d110108500398040d03401c1a8442511911307080a4206241465400401c0c0b00540109010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 623656151 1250 623654901 623654903
    0x20a02220f0c1e0302041d090102190f020c190e0405190501060311091005060f04050904080408070806131101030b030115050102060123040b010311130303020c06041d1f03 75
    0xa442d259001d003201035440e442640203c1c50300d070861906082007800010b081d05401e091901440180024941204c254115141480a00c0c5aa00c0d1036160520041814581070b4a2200501480c446c9001a080050314140d1241381102d0002c0d00a040ca01800705100008206550520400f2074041007520021075200d101d44c0164004034100381941410440360154401ca40d00507507115003005110410b44440d0803c2d54000c03194a0355808020b04100d85900a503044641e11a07072032010b001c20002140018070484513640141d031621030b40c4900613600c0301000c035403046181c00307290300709000100c1419442e505082c0504002908010440100c0c2c21146008008060b510400d00c0600896804101c1c3c10700410100d800706a5101650b03400341d40c50510400158010354482c3c0c0d180a02d40e00940240d910440030f00842c5890f403504121031240154584420340240c002c4a6240140e8106401204c0c01d81d500c4800b03080300300b101280c1000d4010340050024504e240e10800d07202803080350314400c1c4025 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 623657401 1250 623656151 623656157
    0x201270e010b03270f071409090106210f1e0309170c041a04050907061103030f040f020d05160504050a06150f110d11010b01020a02220f0c 61
    0x4103050100c8940811410381250b041e20030107004122400713020302a100020b00e14903010350501070680312000d1400159806000c905e014103400400d00c020403085680480b402103c074003c090301c1d0b500f1840d00300c503014081ca0100b400841a01807209160300b00c6103442a114007801d030050203041d100c10b444d1350704140210740499108030b00441072640c80400e800c081c04800c0c40d031241d03415200e003c0d69565a452844240a01e4444521940310f80460398000b080100113402070240c3c1c940303520340607100e81c024011030001c42d10041c155414400c0c0042075901ca8555200003100903104c50708e405c0309001d849003040364441074400500c4006030051002000003404c48c8840d044503410a02080281c54000701602c2c031107840c1440070404061148410f0750946c0c094103082158080e01601201c5210000c4044a0b251051026591000350701c0006c408083d42d541000b00106081d5600480c0c8805690002942c8080780050020114210188100c800d5500306000501c21a080f400401a10203414a41c404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 623658651 1250 623657401 623657477
    0x60d170d09031e050d0f0219030209010f0c0f0f02061c0b01110a0503220f0b040e01060e10030f270203061303020316020a03080c06060a051c0803040201 67
    0x8040d00040410f1410800307034207410503440340300d100034118040c5000d0380e4281e0342c491103c0c92440d001c6504403000c000c0700c01c4214443e40c0c072164019000e940030340e440f240042d00b26a0488801481042141c41d11540100c50021b032004580380c0d0102da0000307a000b039910100421040c02c81000300410b1010341d800c0000d0202d010003a140014124a400545000072038110403206d1001400c08000c407100910f051281d80320880a002121005118036008140c05017024170011544594080207402150060050314800b03a8907600c003140e18508640c04141c05c000d403040301591090280d000046480361001d000154898480030441c00d400700d40e07030307082c403202d039100500c0056003001d0020585c03060f4000d9401c00c0c9800c06070f400035901e10654500786200e40503d18041c0865490203104801590000d192a880c1c1001c43c0c4c00e103441d100c05642491188070356000004c0c01d03040540842c65001c8009a08c01291030303454984a0065100810403410015103003444004801d02140320100f05a03c4010414 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 623659901 1250 623658651 623658653
    0x2304020c010c0809100b0d121e020f211e1c0207020a05061201140d02060403031e0e0f0603130b040c0e07030b0a060c1a070530060d170d09 61
    0x4c1000852505c010301c003802c0c204d1498090700c0304500e061244da40040c20310803480e00140c00315403840004900c03484114854030070506680e400518040702e48443d2040e2600504145d0884031800c05000b580e194104041c803141c00c0703c032228680021031006011240780b914400083c61100ca0300c6450751105480ea010822106504000c01a10041c00c0300369a414502843c3c00c0007000c1101e014420504d4045040e0f01c00e0a02d91201c0c0390300f4215640c090400c42d1101d03143d240242c02c00541160810f006441003108403030701403068041c113070440030191850b0368090074001485600c0d4002054810140c0907000c440300054811b02a5500c150700604c11148007600740210a01142c8025000004150402c0c00280560399140c80031811500c040c00d140400904900d4800c207820100d0700c5024602c40d8640030002036507045002000381d1250440c150000210000f80040046e01d0345124045600b080750010701541030046125050318003451041041901ca113000c22103d6101c0790850709005d481d0395441d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 623661151 1250 623659901 623659903
    0x1803160b060f060f070c030f03050307020610060f0f0905031e10021312240605031002030c0301090507020f03030702071d0615090a0302030111040f0608012304020c010c0809 76
    0x70341000c41191190044040c900004005015980b100a42d44800045000030044410040002141d02108070080319802c2e05001d002c61b0003c036100710160207400001240e03e0b002c3c0502c9400d640300754039240104000c0c1c803c01c2b180c1c031840028400c148a4184070100d0701ea60304100c8004c400041a6565926800e0000364504010184200f00034107401485001030003100c080e1a84103440138034601803401101414203291180c4201a83c0038a041d01c6128000e4810464000e6001d5400581c00c8030820305211b8100c0080303210444074500c43d0031081c801070110a0b8550401038101c15940304540310b2034900c60b2070b181107900580303440e0b0260340065070800c003904c0b0361643c0d80e0715040d00c681004040e103481c5010a020804a0381c03001510795000030341d21095500c141c401c801031a00500200400c0301c0850440c40da90380640030f450080071001c030001030075501c510241d170b06840100440100d61411005c0700880e01c1105486c20794000c2d028044c0e0b180e505024454000711403171950320421542441d403019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 623662401 1250 623661151 623661173
    0xb0303071b050a080d08070e04020706060609050f062d0c0303070e060c0a0b0c0408010606020f06090c010f2f0a0201030e070f27020a051206010206150603180316 71
    0xa140111241c03c0108060348011a50341e2601e21103044c45d6955680d016411188121031166450380144003044210030710016611038801d5511540750b174210b00752583e00b003145455024002a9008a0401080651042820440100e0800c5000515801002001d0800d81f60400800a6100d500c044108504076a0142901c500000140e0300c55240c04081d00b015926074078109405843e1250b00c002050f0160302c600d041310010000c02c0001c20001e80c072440025180d034044002e001c03280c1314620209021032000310310302032050301c140c44400180c1c00403001034541d65940f03c01e4403ca0111004058040d80d4401244d500264156018000600c0548009005c8541201c10056660700180f4241300c107950058212090314603004201000054601d9565001002c580802c28998004a01c103440b16401001810500c220680da42003503942d800012030f81e60a044525003100b000c451451209800c0520041d90409840e5200e040400d041d110340070300d107034000d6580d03070000000f00e600c110500016400d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 623663651 1250 623662401 623662409
    0x51e060d0207151a0a2d0603020d060504152c0a1b020609030904020c010603020d060902130c02070b0a0e0904031e050313120c0c03030504140919050a0b0303071b 71
    0x1a584075210720b0404102403095600030030380200303200c400c0f1608070240c00b0b91b034420b0b512a0915800100b030f1030b50f2000340a900000c40c6c0d020300f941400c1010495107014002d43c0d03c440c210742c03080030b0300514080420100d180740250132100321560300c0306416610552603401d4403e140000740850000c0900d04481041080b071181c201c11500320310309100007040040201e0b00310403012240981c489050341c02c19070062040f41e100030b6005044002030b808004041c0c01c0a00118001c4078035810850b0200c1000003510a04604200141c0125005024210300d40d4007805030031550f450064080707000013010401a5034150b4044c0e01007400c0180c10380d106405a00500384104a0785001c03419070400d050f2143d004228417500511101c0c2100d22001c19038030172112085800d07000031315081c1c241d999050140003540f080c020314030002e514100012090401440080c060442950504004281010030764020031015004ca0601c1d034031091030403000d5030f00300082e29806000b040c0c40c01c442c1c14a9003401c1c409890030340c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 623664901 1250 623663651 623663681
    0x9090c070c240c02010206040b0603100915061d0105190503010e07050301050c0c0705090405211903060308090904020604080706020303061017070503040303020d0207110405060a051e060d020715 85
    0x2d0f40400607640801c8040d00190300c105401c00795203984002034208503810020802c880c0c501003625050005407401d5201d226125203081003540d403034032088003005810000318501815224010000b40c103142070455406007400c0399942115482c0c100003800d4030f034084d240c03111a9104540a2189150038440c46400c243e4a812241c5044102c001050f2100c00b14411140305520f41000075042c400c00b84000406000100c0080100c1c0349000c640c00c41ca80c10002c0102805200d4001061010f0f00a00c1188281d9800034602410308a0301001c00110110013001281c0150b424040050502400c0090001030711141d0050740e26440c00e0030521481c000d030360319854104454801041305075101d00c0d2980360022a6440c0541d5666510f04080d0042d1050b8898001000d00c001540c0003400380000104403641030458060210307840d224100010041d06010340f650020781a4800200b1000d9205224a00075000c8d244600700345051442500b240c008503c2610074030a822400448058503206401200702000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 623666151 1250 623664901 623664917
    0x19030b0a060905181f12170304210c08030106030204170a0209160c0215071406250903021c0213050106050f0c0c090115020c01090b09090c070c24 64
    0x280014130080d000404007140c0790084002c6010703450750410080d540c281d403131500040280d8408003403040081e410019544900361109028025007204122400369411035425004004203492510742464000c0084042c01841c01d4038400240044c1b01650091510351801a02c2d1450014a40c0c004d2071010491000c0385c0001e0f140034016662641e00302d8000384d6172044600b50744ea2400040d01c01c8410040302a5006003008095505800001d0062038003e1086540702014032219800658603078054a0009600c8101200c03081c01045580442001011501c2c04ea26103640d243c0210b15040d00403800b8006031042285000290b0510507614880c00d880200108099031402d0001000e17405008040804002c1c00280c032420100200a8001e15640c0108642065656040a071502201c01490f0b103001d40a5070540c0c5200d0b60045000c08101e40c00c2788901403804c2c41d807008120b20088020a6020011020704c403d00219118030340c420043e00d04500d007c0350480d03140e801c0c402942000e040243c1000010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 623667401 1250 623666151 623666159
    0x20d02150408090d06020d0c1b0309050105130e010e0702010e0d02060a0902040b2106090115260d02011e0c230903030c01060510050c1507030219030b0a0609 69
    0x203000e507a402508120000c0d1903c0140340020f00522100e00c0291605d030021502c007007071055070362103050342103440c1c0c44000f648400c00058250070b140e07198020700821401c4004000f2540903400074540000304003003400e01c0369101d084102c1200800c0e0490301c0c00010300801c0202694091089040f40b5003418018846036803104002590782000604240001da00d51a2510454a468000300d0707108a0041060005000c03e0072b0b030840c089200809420b00344100d50100301498030600c203120f00d201c0514200d01c0c00d00d0a20320b505a00320011558160030001d0303441d06100d484801d200901d01a0b01560000c0342d500345c0820400e520003c4016a0300501d45032044a980311600410200401c0840c100080700540e00400c0c44080e90003001400c0707070036000000790b0850340030781903020105462085a0f00014619069012601d41c000d07941c2d10111a8000d6007809a120075001515500070828a0098a015480c82c036040c0002e0840703e10340c0c0400c1c2c0f620350710040e500c0e1500445010300b10a152801d0031500d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 623668651 1250 623667401 623667433
    0x2030c010c110a0e1b120c0a0311030f040b160e04021b1501080d050f030402041505060409020405040501090204030302060601111603061d12160c090603080a090b030f07110c0406080d020d02 83
    0x8047d100b903062220000d11001c0290280e00a09040b01d0162003c50301c0e40752100502e00c07201000c59089030750360050000201d01450500f100d1150300c0301030381d0706041d045402040c04020b5005210300d6041c1100b18180d242c03a4001040a06984698682c00d040c0c04e500d0090140d01e01a00403412a052000030b02100040030300b92010340740d0041c5c0484c1c01260300c000b140061103103440780d03410254124400082c080740010740c0c0e4006108840341520108800da0340c403541c6000b00d002d14040180180c0081c408141150312954010104090301000e03201100380918003044100b50b01e600403181603449000d0202c01d48040b441501c1c0d0b04588002800442d491641819100d10135200c841103a03814801d841024004000070100140c248200104480e5889042086448e080100b40b0400680c0c0c0c0c00001c1a001c44038810f0f28000c401c007850b01d030750310f1301c403a00191804110041e0201042c421a80c06200c41d135241d000e1240106481700c00f400340308824a07002414010050407250955000e03004610808031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 623669901 1250 623668651 623668687
    0x60309070312080417030c0c160639170a1d010f020c150c03030a1401080d0e060306060c16081c080a0b010207080a0501020414010c02030c010c110a0e1b 67
    0x17040d240d0503500da40d5580301400d51301450107514002c4c4208040d07002c030310300c4000001d0240c1c2c8880d11404021090703120003503001403503c140001c49200c0082c5c43c0401d10307400d058100c1070394480c07100070004240c0b10f0030401c1b941c0c000824041c00078401202c20081107105e1112180c034084d00f07180000c020035245c08040e60301c1d140100d004ac041d8041d854141032025805041d20103ea0103002620340d2800c0001442c00600895820403400300c0304500001410344c1c0000b82a200e044040c0c55040140c0500750802190f600014516904608100807600b1151021700810440751222410380150504040d8010319140380142045039010381100001e90b0f03190880111680a1411f2801244800c00c03e03004070b040c4580390348000e05a2040094074010000190060030941700b44e28040f480c400b6001c00112810720080c1800b0b90145c01080c81050254441c040000c01e150044148441103040200490400202d5500c081c548036004418400e41916501381c49039124007040d0114200301c422440084007003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 623671151 1250 623669901 623669933
    0x105040215042115230c090306070e010201270c060302160602071406090a0b090604020a05191a0406090503030906030f04030c0f150516051e07020603090703120804 72
    0xf0940800c0001c1110040c2c014a04015000303040c032401030609011100141218014040034003200700007a500c01030241614a405801401404981c50b900405ea0b070701903529840904654860b1908408001014000002071181082034128402d5034201000341d1802e81c0c00080c00c150042010f02d06c40b80840160450040d0010801607540c880c030300c0c8c601401c41c003482c0d5116850060394100004000003103034040d44240134190040c103681e100d48000d52150700448000f5440090302006000c54100704400f190b000180c1ca1480f000191660154082080300680000b03039000006803e0115540c000f04220041a00382c009600f410380c0c003400100745000042002100e003a20b840043c0625106010070b03201e10703030000b20010fa500d4803400d00040f408040541c00001508100100d25a540f1441d00c100303989480c0e40e500745c24100a180c45100310107c0c0044c5801540051103404050f91b128401180241070110050410500d1407600c504c880820340310320410300030842d0401021841c00036210f0355030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 623672401 1250 623671151 623671199
    0x51006150e0d0b070e03100606020307060507030f2c011514010c06053309152809110c06010b0702150304030804030905060a02030f0703090e0702010504021504 70
    0x7840103280030410503456518040d0460300c84074180112650001030b20040c0d90740607001c2d01c5400b0703158000902500c00030711600e801a403003000b405000c5a501d5000f070340c00242a2034040b496205925240055400814a445040d10503203420006c01c110084840e40382d0701090000d01241c0c0d681040d100100055114102e00b0044540e650f0280340c2c401c1454a221075840141000765042801001c0c03000a006c8008220003c80c1d052a00040c1c0c013031203600c03c0f200c00000c000c04400d980e00d001c00c911110704010059004490000a00401a0404000c10a542d41500c0c011a80f82c03424030344409072180d000c2c07184580801040601c229100204080d4152800e148865a5036160362010900f20815010428210003000c814802010f074000221800f45002c0d40c0c0750b02c0c1311612602000128410040100d015900030884034091052910107418194020705002d02d106036294480403203a01c040b00c240300180d44d18030401045290100b4141e0000001c44699420b150601c404038031900c9d10500100b400b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 623673651 1250 623672401 623672417
    0x31080d140c071806050310050f18120f120a1104140a050612091c170903070506070825050702012304060504080f01050f01060807021c050705100615 65
    0x944030200005030003422142c2440720f0042031200d40c03800504950103400d202e405207200204640c01640255070169000141308000b0351200041c4041d14645640c03da9142c6c0200180e12480c187c9003800b6210041d01901c0e010303500d0350354034201c6401000040c01d0f4203000d45000882c0041c00111410f850a407040e0074031203c000010f900001e000f03c1e00e030b5400320360311000024001d48107484001683c3d000c0c0d0b542c0011249a180d6407880781d81c2404180000e040090320340404110421881c3c1e124540002d0204244d900d085510786446051240848410022070034600c1071003080001241c80d031602e0746014000000040d14190010100d02c55001c0103030400030009280901070324112001d50491350701d03000301c564882e5542400351898000b81710f006480e008130881500030720410f0290074829071010b075001aa0360300300802501c0051018020b10b0440c030520003107140408103000240c9564119889136070700c400701850b009140001d61030011602c141001c03400c1055081c2035400c0d801907585404d000003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 623674901 1250 623673651 623673667
    0xd240305062415220302060f0708040302040c0207030b0c0c1209040213090c0e0405040203060a09050a06020409061a2109030903190c1a0d050c31080d14 67
    0x110b070000c40c8800581c0064520200140b22100d10300400c041c3c004888041804080415000d200c000e5503c0040d40124041102c04440c02d442d00090691a1050b5043c9081984a40204046810f400f071614090380c022002032091181140c004c0c2e034401c1814108520b000400102e603500c501411034607412203080401d1084140e80c5540645900c0c2c40ca84183c242e06913035034803000020345410a802004501c00c4801e071072003070609000e0140b0590b00078004028549841040c00b000741214007027a101d900540240c0340004d01140024002008510400b15400d07050458011172000c402816199a040412081c190301d941c4200c00607600c0051400003940e45d4130004010b040d41b00701c400580e03142c0103100c0e8031050003017202e00d00c6142c1c0c1c0c041c9489680300d40d283c5450f0b00580010901c020a0107000703000d034400071411904050761001d0794521050030f00007130752042c0188010315080f0070307040c01c08040088080c2c000c00d01660001c0401d48007c015041071400f000d020300e019401c1d400e4044800149440d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 623676151 1250 623674901 623674951
    0x40209010b0309030d0209012106090c0c02030c3105010501080601030b010c0b180d03021804090503030a0207170315030d0e18040c0f0b030711120412020a0b0d24030506 74
    0x41c880e42781c058440750368402211840003003045000e20321000f0b00c0c10f0b52003640c1e5440b9549003104c50754050010301138115000704102e0f001d00401c04d120529032807011100e04c07090401e505100e0701c40055801061950400c400507044c100001d00c8941050300e401c42c10302c1da0b6a403104010512513040046031109803558a408100c00f42100c0f5110354601c103416461074003a038164001c082920182c1c1c02403c20000d854100401d843c10070708007070219801800801c90700c031a280d008001e114401d00800c00010501e2040040302e400480e00103040d000b410500280700d040902206040100c40d00c0c010704141e100c6e034002150180400d2041a107800d00600150401c480380b640304001d0501044021801950f03451050141d6000f103880100094410305101d41c40300f00021041034074451003024031705060901c6603061201d00c101c1402d9900c404031180000c1c0d428440b4006042c41d0401010100d60091340e6190030f144102070648118052f84842c2d0104085600866090f400c49290a940c60180b040860a9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 623677401 1250 623676151 623676167
    0x408040e040f12120e0f1f0e0d09081917070201030213171207050706030f0f0509030d0b030c0a050105090d0b100f0b090d1e080f03040209010b0309030d020901 70
    0xc10200407200890f041c282c00810026660041d0041032212250300b401440d10741070400500c2c10517600c0145180c4152007030244e03082c1050046440002c0000705006c02d02c1c60034010b41c4094010400d070b85d0007070000d00c1c0c1c01e001065a040d42608407a0302c0700d107595616610107a020745403085002c8089054011a8400d404560b554200000d400364455102c00d01640100400301d20300c80035214524030a080704007034000b950780d0b450b000350140007401c0c40c2c04000d8003e0f00c44100a908441c1d43c840508050b418148585801001c4407002103854001d01440e000482d01c0711000203100f070780300f030f800200c41c0d81d00c1d601c0d9a0156a800e00e880c6d916002c0580105100c9500c4840c001d107a2181802000016510896650300300e0f001400841c200e1a500d81c0414450f10806110a40002c0c07500700303141c0442e6441040c40c81220071001c038004400002d8550304580d801c100b600b00d64442c400010700084d0b19006400c0c50240040201c40c0f0b155041540080390b0b00e106445418036525004514130f80e441e070280b107003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 623678651 1250 623677401 623677403
    0xa06120f090818030f0c04090c05030d12060f05130c23030703050c07030c0b0c040b0d05011406040b04061112030f07030608010507020d080406020409150801050604050408040e040f 79
    0xc1880003080624000b01e068010445400c0510f507003806040301840c0008940600c00c8000c0c2c081c2c0240403100041c840030300903000c8140d4401e40c00240015042d2010807103411381c000c2d0b51f1f85038014940d0249105040d41c0d80c56000c241c0d03045060710140714a80da14814600040350b458030005056943c82c400342e450005003000031044c0583c203801150304100315070055200e010103a03010002560307100c100c00e55600410501800082c0314801e0300c0d0000d0804022903411014603044181810760f2081040c0869100c0c0c02105001d80d00ca40041012054480003c9400141102c415007014100420301985018601c1000301b0010142404602c503003090001005081c45110f44594910307154000c40a44542a10804002854000700262444042c800e086c096086c50f070290425031402c800c212031005000c5c0096030a26402c2000047c4014940300d10100a000250081c035010314040c4010b08440c4d00900550040e4101310411001980041c1184c050b58071080004c02540c499040030b43d446204020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 623679901 1250 623678651 623678681
    0x81003050106030f050105070503010b0d0222120b1003050d050706180308012303250e04050604020a14030303010b070501020d060e0604180b070c0201021f051e060a0612 74
    0x20b0040148140c509442e056035006070003e21190b10344071000c46891100744640c40074400207028898003040301f50014250100340700d221241245a044696804000d40ea006101c1c020580283c0c02c01c20840c1280150312000500c0d0124800f46107071078007603d413242c0744240e0b810084009800070800c50568800c66041d07407145002c0c0315480491070301805241c4203014003160b503150b0344c10705400c0d11241c008800d294400a80a425514055420206000118954402519150040802d020340101410b17031056000b800101940d060a0060080c4580c80e60840300841c0103020510201e6100041203904442e40c07080390070b5443ca0607085c41802030081c54a14400b0740c0c100040010070700e064041d02c40c05180304450803c00c3c620301960f018214000080010101c040b1000050617490041d0803100d0918010700603034810010901c00500020044002100032a41e2482409010420950701c02d552000003000040320b820705c4000950300c1daa00744204800c1210460711075114110a4005400c1282c1c410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 623681151 1250 623679901 623679911
    0x213120f12050712201b010302091201050408120601080f070e041b0306080f030c0a1103070513020c01060e0408070f0c0f030503090f060301051e240307021c0f0810030501 75
    0x244005166a82d0440500b88079401c030b170a80f6a0a220101e809100c4542440b4805c00e20310400005602a421440c40b003684810a42c405403a142400c2c028180318a12481516903540d45a442c0246246005460f440c100620841000f02e00c000320310186030800c00b07a050100901c000c1c200000c010b4110b0420400012410310040e028040e0180c00c44020f60700c01c0400da502e0304a010040c3d603a0b901032480c4044042e805140071030081401e0b552036040440c4060151040e19407190013062428085d40604a0072650008103c02c030300c5021311403100500810b059050840c00e290711295000d01500501030700c03d01c03000c0b01207010001c03113040000040c50350000da03c1c16140d5904080b07490703810040380d85020b20801800c402d510b00d400f00c11281a074600424000d41c50301d8100325000c800289600c079981040d4100d0450b5082000541d071f0303881c80d00460000c0c5a60b0302d003001000303013407901d90a0703203e80004850501c3c420040c2c0001d5140070240e0a0305d0305110341d94410558515003401640007030102c3d4030700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 623682401 1250 623681151 623681183
    0x41104081606050a020312150a2309060f101e0e01170f07050c0109020616140609120d090f050a1b03110f040207150213120f120507 58
    0x100350800d0740715104100e200d625036155002d0b0f80900c186045500146c20030409030700807810b41c2d81201e0b048041716110260040000f070228628041a421481d40755030520341801042c1c0e203c420714002004280c0e6400303203904105010400d10000e8007003141c032444000050741000c0b407180740b000d03142220812800f40c0a0000b00005007400c0842c00109000480c800709240c3c04c4041c196840b80031f19428100e0b44960350b02d202c022070b03254010140d40380c069501d61560704096a1200081c2c414a52000d0121020710f02603e00340d43d15444a00800720580c01c420108032040030007103000642984504407250780d034800684000001c0038250310040050110180100902000140d901c1c0424818040d000260451b02c506140359902c40c40000c0c21100319801035411030801c03840350441c03048082d00160612010703940d069500d002d0307000010007941d03000c141c405541c0c010310505802401c45003205200301296407110312001c410040d002c0c0281d015130301c4c0d008440d882502214103054122011440b04544 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 623683651 1250 623682401 623682403
    0xa060818060a06051302090f0d03180803090f030609061b04032001020f120403061a120a05190201090b03090a170702190501080406050601090b0406090e0a060e0103060b04110408 78
    0x3e180100c50045141c10f0010784011058802c0b2410144014104010712110000300400810214000ca0402c00384031054910021046802d002600000002d0364a5650f003005100b070f02c00380394000a12031350204040c04404440824000d07044040d03c9990395200c000c04122841601ca075600c01002c6480488a07210244079403000759181c4c44090f8262207c6944140c020342d50361900300f04401909008010400008a034ad40c0b29202c01c00510300c2034214801400006241040f1855942c4015000030307100074100901800200046105045150041d1541d500024491141400341a0349440c0010110f8260f00080210350f4100d0360200c6ca130343e103248800d4200000354211210413800f59807020b0191004030190344280b010b0328410b0391030070b4041d6200d84940e40548005000181800004400400e0181c900e60040c8007402c0151140e203210340c581022039503007000081020510b10300c0c0c1642440241c200d00404c030304507070308100f0204410011a0006000300541400c1444400c0c0000c1e00082c140c41c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 623684901 1250 623683651 623683661
    0x30a08040b0603060705040608060112090813080613060902030f240f010e070c02011106070c050c030a0807080a05092e031505120316210207050a060818060a 69
    0x440307191045065180d40d814181d40b050169500400315400b41f0007807001500c500d0f64641d0010051402c00300141c021800003048a00d0780300280c90346000010102494035040d1060320040800400410707051809809a000381c0c80d4880004000d00d8503040280c040d9503041294050030b16481c401e407007521890000c4110025089403804640c0c0805500003501d00d401034242034102c42802d070409174284e80c1c0800491310088206400ca05000c01c1c00148000c0031420001140f1030400c0e030f10381c9000004141851441c01014400680c402d0740182c0201000032980c0090b81c01c0c05902001150703c810701c500003a01e550082013800c50b044062284825151486001c0d510384441c04a45c10f859105114507084080d81c00d01f4140b042005140c5908201c9418100c2c02c428a10190201b9241000c165104840da8030200780001d89a0301c0700b45d444201c03d890290074100d0546810300040c42814a004049442c00c6540c0c803c03101070041c3d400000300d01e05600c52807444040c50000551340b09240201c40400102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 623686151 1250 623684901 623684903
    0x3032a211404090618091a13051e0f1b010c150f09030f1715060702130b0a081c0503131406100b040302130209040e06010305060105270604150503030a0804 68
    0x1040c00c1c0c0803c5e50307100305000e01e6086028483c480c00a1800030a10140140c00c090006030228100300200b401401010008061182444120a0b502c1da020b8a00081c8920060441c0c00609061140420360f0780340e000002002e0a0600821100d4203201d01c2207900e40b010215a1400c01b04820440d1500b980110080c0b4843e032580780304c24200402c00c0b01d02a01c2a4003034141c10380d52601082c40040c032411441c2030b80d280109502d180c81030079408645920244070095419603190a001c14442c41c04100c0302d0040c00800d4020201207401c3d51458042c1e0000c40e00500038020f000022078800c3e1180e9100c00a0a45c010100512041201041c40d54450f8110b0301c3c5c8610428501300801c8101c94003040f80d040302e80090010740702d00320003e00c0e83d000394403034440968031a036160300c00c8805600510442e13000354002d4002d001150703d400184070181c0641c0b0340742181308202c80700f140202d084a0b91121342000d001d40e00041c4038030341c1c0466881c000b40107400c007642c5440702240c051181c95100c03514511507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 623687401 1250 623686151 623686169
    0x50d0c0e16080c0c1b060d0204060c0b010b07030807030506032d07050a0f060503090712080d11090a0303081302090114120304050904081c020403032a2114040906 71
    0x80d54074110f04211900034144460300c1500400c5c00d5015421030407022520350702000b0103485c40c0c02c08440202d4103ea0040d40100c01203492644540306010350201403500402e2842001440c02d605980e0003004400000d2400c428140c0d02c1c170206d45162420081000c134122299400780c00388035030782e0185440340c00c1c50b03481000b28842d0400120346030410032030340e80868800d0682c203020141008c005840c3c03500021719400d114414041c0008030150540040380c00036000c5d00c100c50350f0321000c40e0340c44191403815100f00c40300c3d0820400d820710741c4c07036250ba204102d81d01490719410135110220310401c3d00341e9018010b540081074500200b0508500c81120251901c200c1d1a10305a004800045890703015a115041c1e0014a000008000c100c401000380300100c440200045041d8200101130101d0b0003d80080c1c0000c1d000303615030030010880714516001c05118518100f1403100c950b440b01d04c145000420711220300007004210340070501440790482d81d001e5a0595039119a114041c1388000c2c0014801c03a28a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 623688651 1250 623687401 623687417
    0x120a0507180b0f0609120f0d231809070c0b040803070e0a03020a0e06010207180b090a050609150301020702131407140a1d090f040228050d0c0e16 64
    0x1440c40d10560301543c2e810060200d5003498101400c00045803c110507222450084000f1076014250500110f40054178a803a04810b01250142c3d203124114a00c81180d4a907030304018501084900f04801e0300845070440f4101810b6884241c122206910b141d00103000c418404144400c1168080140d807240d0104d030f681d241c0344400601004001c03070700c1e480069001000405c060102c6032180d0302d0160710280600445207015590b403100c2100c400740f174021108031586c403d128041071809601081d0401c1200e1410b00c00ca003005000200003000c09015807090a101c030071500360545003901560340380394004002e10320f00c50f105101c2d030f406005030316004c0350040d020701c001640302800340c004a040d00c008103803c1030030560502000c1c0c444500d00c3c070326180590301c1400e080c0c031150350b1454428410882c0c030f01401d40301c0c2010300c10302040006050311001c0741d24000c6c40d1104007910303101d4480700722031044030070045050b00ba00708071083d00784503004117070101140010002c255164021500c42110580e40301d90b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 623689901 1250 623688651 623688671
    0xd110f01060308070b09070302090106121a1e130e010e0d03050c042106020c0102090909010b0d02040b0f0604030b04030e10080610090e1303090b0301050609120a050718 74
    0x4200c0d406800300801a80c800d100340703004617541103401c81e80301082404482403162650001603c00318264000710000b01c003101e500400320101e01a901c0b2400c1103184983c4608174440000d180c1d15000f081010303200d130b001c44500384c8965501c1540260030074030304403c0181c4c05d00c2c0d80b85a03020703042c1500c442140e031182c0034220385081d100b40f146c1881031240d40641e41c180b9091840d0006014860081c072500d200c40d06804002041c1144018007450030850001070781e440d00e101c24440e00400007000078004e40d00d01a101603986c0c0b1082111452642c2c11100003412600c901c0019039200c1001408640000000c135010007082a0722001c580924004d4982408081c030890410082c0440c1ca004600003511a0002c10101d04012100c4408040941040182e581c0c55401280c0d0108048030445040c58011a03001e007070640112030000504224001e0070b15540c11b24010400b203124500703469015007280203910890792400c0c810501143c2d40a81580c04c06640c07a140034600400160001c480c0500d0482a45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 623691151 1250 623689901 623689903
    0x90726010b0909010e040f140f10050919020108390c1002160605060409061506090b030c03010b03060616242c01090f2102070605090415080d110f 64
    0xd885a90700040e01c112000c2c2d00c0e80c4014903071802423032804451282c2c41c00c3c080405c50910402c038940c0c201050024951600c10911403520203090500c0003944001002170015036408603006074020b49040c94a45051061101f408144170300c00804200c5602c02c603049010202940000e0035828489001c58401d00b0742d15040904a05c5003490900313282e03041c0091071001030b040d5000103071301401c02003001542c111151203c1054414428441c80506070000c003c2c040d80c0d420034610b0001d00404200b0606502c3c080150074100d100600495000300c002000103041c56903034101b1603080c520109070100010f1213510f410701702d0100010036104107002a64081092000c00d21840c90b040c0f04620121511140b00da0140c002c038072404200d100c80b9500d03528036401250600d206ca0252500c44d451207014000e01054045160f085840440119041207004001d001c1d803190a503650640c08540011f90424109509000d1090740d0340030311818003e0744010700c1056001031520f991a102002600c111040012002d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 623692401 1250 623691151 623691179
    0x3031404120303050709170d090902090603040f0f020315070201060902070b06010804020609040c05030105180609162001020d06090507050a030e2407020d0806090726010b090901 78
    0x1140600701c00811a00400d1082e003110360420198288811426111100300049606281382d900a41d8000300c0407650099002c0045002081c1a40003181002c00c680c0000e58107100c0640080c1c0440e01d90118001480304020301d20080650084c22290392008880000201410861314900035500c0c0807000038120146008899056034006280d4400c1d40e507a034010340b00c0c00ca006e40700340e030498800d01c419007242c1c54030711516460a220b41c5a40c1e071250302d85010030400c03000c401441e103910a00310040c010b05803500d02c24140c00402030380d03101c0d18030140d42d4411202c50031001071030003180c0c01900d8406d0403690103600401220300460030038480f95881c0c1c601c08042c0d0350141ca8107000108100f203021000ba12070381c4004500d090060036910781088510408140f0911141c8a070301c480c0307a01d0103000d011a0104243e01d010101428100640c2c9000400103d55040061691003031100910100104112003080840d02c4440c0d1001402c9a503104d5101c0c49890b0070824100d070041d40303090004a040c010400315 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 623693651 1250 623692401 623692409
    0xc12020112050a060306060605040e0a150b0721030509100e0c010f02030706020301270e0601030803041406010612060f0f0506131d04020406090c02060c1602030a0c03031404 76
    0x640d41907641c00002500185070040c407180015544d010040002a000d0003007100419032559100e0301c8074284019080f447c031002e4850349119107454030500d6440d60540025007200c455111040d158520707410b107140350441440041c204080c9101c404404a50994490340c091400882203e00f441403144c0c0e4a0f00711451500800d0b51580303c690407810300d40c49200210514001441980c2c1020115030750401680c0081e04641c495000004a001000f44036801c00304452080b64400c1c0241516110702c191101c606001c0136100d4040040048c0902024044444140c1440000c842240d80e60b44001041012000040c002c13103030034002d00103100c2c00d00c1000309080d100380111041010781792030200007080e80240790204d60b10407001030000d4509d4461107040d0890345007246035a01803801e84100300807200e04d9040100703a05d02d4076281510b0a80d0014605510016044240750360360409003d80d4041c2d1800e000c0258140300351080c20b41000b01961aa608807486031702e694103101404c0000302858001c41c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 623694901 1250 623693651 623693657
    0x100c021506100210050a02180a060e04020d0204080a0f0b0c040f050d050115120203010b1f1202091c060b0301110a0c1a091e12040b0705030f0a0c0c120201 68
    0x10208010b850324401c50025407441d0b004135200c91800700d0490069030000c851302d80b034a070b601041080810a041450b00000381080380d61035034007400c286014040e41d128000c3c19010b07660106e401401c83c00540c0c104c038060b2002d00101d481180c02450509502c000f0340204845150f85d41021602c20719600068a0a64901c180d01030f20960030f10050000310a0550001d544642d01d0380201140c0503141d1250b003003c1c01020500140b941030714010302d8252608409084e0142c040c404400c186030080c400c0d24600501d481c9000c00d8a0100d5511002c0030307000361318100d075020214404115161140d03a100c003403401d200f010305010a156030810075080340c00e4400c03040b1001c8401c000a40403580700d40b619001192091840e1080c2500c8008060200c1b45e0407a0120764a0380942c45c40160b94880c41c07901046103a03108004d103003c0b04410140410390080d0301c550145050042010341c100b100500680d000c0b10080300c0240e4540c0b0200e440200f08400c206000e90301a800500081513070b521845110001c00c2c0c06031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 623696151 1250 623694901 623694943
    0x30207200a06090503300a02070609050d12120f0614010305010e04052e11071a01180e1002131d0402031209190312030e010b150903150405100c02 64
    0x2c01e02e40c0401c1d14100310301c0381404104006d18059400405455282460f40c000c041c441e00b0110064030713008054010700d10950003441a08000346207104003088031041494003500c0012041c44481c0546507014507001c0c103904208010441d0400308800d50301003082607905100303d07665441440c407240303400d55000d41039070400403444095200503494402200a282029152117a410708003000b1078042141d40c0d4030005c4000b410006008100f1403440c5100800d15081c0b0440d45040301d249210b0b41004110240075407514a126091241808042c0c8503001c0e21000703554460150040d41c0c0320041c54002c02640040000f150403184141c01551446154040c0052144401211281031660001c4119076402452410607501c802d288502d000011b512501e00781c1c2e559015800040d003500d84441c12807085a02d0401c03005190340c0ca050044000520480110f0f80e1800070602203410480e040d44100da00100010501080100001d4080c20715410700c1c1c0c1c10020030075548400ca8407410450b220950054000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 623697401 1250 623696151 623696173
    0x50c060708040c030b040302031905181c06050907060f0c0c0302010503130203100f0b010e0d06050a1d0f1204140f120a03080405060609010f09050601030207200a06090503 75
    0x180711181e00180207100304840990389a84007564118111000c42c0142c20109441141c0d007002c14004958101078107003203082c0320700704a4034146240012070540c4034010303250041c01d28440a51304842d41e01c4c0c0103803040c016443c08554543e81c8821074410003002502c0c03e0710713a050252089420703094007544a9810140c03140780d60011070b001d400187c0b1000e030b5601c61001100040c3d5041041600304a848800840c44c840c502840e40225002d02004034140305500310085190380d50382d14015101c0ba40030000190645034901c08100901d0751845401e414105803087c2c00307016400090841c50f5540c1001110200c0d0850003411034280a81d21580c0680d0b0790090542c1045d20b040030f0146000340c0c028007044c11010722045003901d40211518254041030341c1d0300a1109000083c0011940008280c509500b90f5150020540d401d811910505140543e21004109540e201e50112140c05030403855114581c1e40c1c0d11503980081c2c405182c900d100d452140d40000d83c290040e03542c9021100c00402034104400701d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 623698651 1250 623697401 623697407
    0x140c0109061b050f0a0309050c06070501091a06030304050d1e031709030a20100203010f031a0f16020c0907030c08090705060405010f02070914040b01062c0f0a03030519050c0607 78
    0x11f507000485090181d6880300c18103884450141032072a0080e80041180081d80c1002100484e00a498040c0c0e0020101004125180001203d0442d9800d40c1c038420340c05424140303032813103403c03841140c04804000c841c0b40e400d143d44031500c40524480e80405644d1615028851940d070b100301c41c59640820381e20300803c2c065688034103201c51440a0181620342e41740300d203c5184100da0090700f00d1003031480c09243c240140841032142034050440307040110081e0900d280400130710840101041c00741c89086003c5000c0c1c0348244070203468400c0150038500340c1c0c100042e002e40a8407807401c0c10800140e2030300004a0203140011604110f45014011030b240c02d0509004503a00b100c0c5e4901c2000b903101d40386002440710450320550141035003244180d5664146840c10800010b0186d01c4402044600001006a9003050f0101c80c04040202082c00c2d580d28810089aa910a40301c4615030000b44070300000103140e0064001c14107601d21041c90101e150050320141c400e401b074211001501e0740300100007151180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 623699901 1250 623698651 623698661
    0x1020601031707050717010b060f030f041401020a0203070b0f07080c0c03040b0d0c0306060f2a0803180105070c031e02211c140601140c0109061b050f0a03 68
    0xb0740c0030441c0d00c0d01c1880d40300e1600e4181154014070351420a055803c00402007803142d81d111070001c940e040d1400d2032204131940d40d0b00005c1c02101d05134640002040c00c2201020160012250000003552202c40960029441341c00815042da01c0707148040020b1810315508440741c0c8200800e0712009100d40300e80c0085000da03040301014072418803080001150704840d680107461040781c0e100c40031544080081004081c2c0703600d90b1080b010b0100412144001941000460704010700380742c1c0600d050080c16074900540e640c020802703004d030175001040c440728541080a50b445004c80e00c000380030135150200122440c0c070716214064000f0300310954a50101f03820281000410381d40b48110b41d41818611030034500e012001015201541c4005041181d03038110750888800400d25400800103940c0d81900c48004190080c401c42c108a61603d03000d403400841d0007510480f8a030b4100030008a00d0503e4424001e0058290088400710382520494055124008407001401e00c13a8186082906064083d00544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 623701151 1250 623699901 623699933
    0x40c0f080c250212010c020712020a09020409050a0606050a05070209130507060c0507060e060a03020c1e03070b1f0e090304080313090c09051c02120703081b010504020102060103 78
    0x10748100701c103510804800003054895220b5188800c1c2c01c600c81d01c100a0b990074403003040d42d10b40e410014101281a00410560125440c0369216900d140c0c4034400161054002d81124024901c0070801044850711907001074400c08000c40308202c101c0e150a01510720b4010020700e040010390410140c3c0043c107004011903081084080d00c40b020031156a60b00b428201c031900108000380b54070244000740721342085060024601410100341040311200855124401c00190310706054000400b10140c9000308010000c105c0040c4180001190725407080b42c803640100000d9a1400d02180800d01100c4180340c46c0e6103c03045c410282c0d10780c0d4031305400507000000007009104c0760b000501c00080d554074240014040f404500e001b241c0e102e0309110034001120000b19a640c00c0000081b414030007901c0e1802020040044a800f0000074600c0d84002206040400c070740503141d002d0700701c0000400001002500d21100c504203d0002c410341d510301242207820841c1c2c040d005a10400c010030200ba00005000ac0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 623702401 1250 623701151 623701171
    0xf0f101d010905030a0f091d04050c100f0f080c09040507140a0e0103111e0f041707060806010813060c140316020709140f0903090d0506060f040c0f08 66
    0x30100226803402c40700001000d59443d04006105c990296205850000d00c2e003190500d20185410940c00d0810300b010352065048601c868404242408410441951050802042c01b44810b0021500801204040e18039401207600c02e0410152940030300240c1e032040c03030107418403400c4c00c4501c81000090030018080c801486000fa0042d00181c880303000800b01c0702c510f80c4440d04c11303982e50382c00181100c1a80741004a4880c0902460007050401c810460015003c0004180c5400c60141d035070080c0e100c2c90307201c00180800c198010004000105e00700c011504103854408055650600540c0c2d00c100072070318410340856040451000813903640c403401c41c803d10b91a02114000300c0f200702001a900940c0d0be407155030f2884000130030007981000424064000b11400303021750650760246080182003c0c1a4000b545000390000c0c85860082007650804000140000e01107280c1d41401601c1f00300c1511118000c44032a4107248840c00c03e03003d0344d42c4a50302a641d03501010200c400468020748003900304080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 623703651 1250 623702401 623702441
    0x3030f090d02060f2805030406092901032109091e060e09210a1b0b0118050907061d0f030706030f05060d1e0305070b07030e0f0f10 58
    0x140c3c0b20240503021104d03d5045940d650720340c10030851880c034004030045075060060703070381760528544c848245ca80150703101e6001719080102380780514504201b04599400900785003540386086010160ba94103c034050300b85490300c544407142028000380d0f60344e85c4401040e94a00f041040c0300d0a58400000e04c1280d440c031140103400d8410300c1c0309a445c41d5001660b240a8441440203000081c00380304d80e40c002542e903400d4031003141907001c160f0b80562030f980c07814040a1b5858804180311a00b410300070961202100c0381941e100c0d004c018900c0d404802e01108035183c14001520070b0400110102900c1841d26014114010020401460442d440481ea0408001290980079860410150002c1c120a8030b021400200341010241202d8009000d18842c0b60752402071000f06040f40d41c04503d07159107110022002d24142000d603040e10404c00020103001c92442040000e96040d40f20320200b05404066480344c4c14a181410303609c2c89501030400d0740741c200c605081e2183d21540e000800c40f01c000320346103070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 623704901 1250 623703651 623703653
    0x105040206191407030c0318060e0d020a030611030412090b0417010b1003050123060901050c031213021002011a1e1302120c030907030201050f040503011a12030903030f090d 76
    0x1c0c0d40e0484d1000b00c010920702041e030f804140e0003281d007500c80010204021350301e41c603100380204100d04440c0311900030f580c4c1e10500c4065440c0c41c45828081e6803c0f034014005900c041003a000550f20840b030540ba031240c0072001c02501c0d4494080e0004a4a500c090395061078200140f44000a407000d840c0e140315962230b240300c10700c1e0302c0d50039030001d08c125030340c500140c0d03585802d40340c130380050b01d9400b02800b403040f440845180760f442000ba194403060a01e4034680340d40310024014510b102d01e81c2c171108499044001c125640450b00915002e492007640c0c01c3c484c01c00c0e405800e03804e84e40b903445d2070300124411a11006d06410300940702c0e4802506a1000c0c034064a0302e50208580c0035000b0101c040f280c0d0002900c0c5100c5100a8216811201a1414901e940340600d9255160055804001e040010003d0214520a00102a00c0203007038005c2c02005490030341d000c007440d4070307101c80359041c000e0804050410581d0004000e5032091000940658502075200b5907008840d401070f19203030703803180240d28220 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 623706151 1250 623704901 623704937
    0x1003051c030e1006090515031905030403080d0213060305160e0a150206010e0723070303060306020d05070e03030414010e03070801020c030d1b0c0303020d14090a060e010504020619 79
    0x142503d0902e8400040d00c03420240d841c1c064880060280106540c241d507421320588000940f5007010890001c400d440101f20700d00b007030443c429544003411041001c0f6424924000300c1d8010140300c02c01414195989958890503025100101c94240c005008481c84003007940c0141e511001800000340300880d410744400401c0c156032003112880c401a07005030014041034407414503140c1c2107400743c03c0c080003082806002840d4070120881c020f405260205040f0205030190700148051030f4090002d41d11a815043c03010000d240880e11640064192a44420242004022241510080c20480e0000d0600c880103541034903510f648a90148101c0d100090150400c0c805810002c1c4410080d580e00c0d8a60320305481540c00e40140b40b40c2000c0c1006a01c2007013a0811400500140d25003070160326a0502e0070014000c00f60940c841841840c17150820040c0c50f400f20b6802c5141d40701e50410001d0b07030034204406089030f80c104d4009400441c10000701c00c1004040b0351031285081c403441d254074107181c2d0900c44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 623707401 1250 623706151 623706163
    0x902130b030a0b010815150d0e0709020309010f050405280204050a051006020102041d1905070e0411040506071704090908030106110610060302092b0b1003051c030e 72
    0x609485070b4401c0b00301e807a90b03440041c142e0001406044082804446e000007a00e0381e0340d2001c410304000d000503003d6240c0c4600d4205140500713103801aa00c2c40b950318000d2a01039030003114050710039480c1018003014a044c0d8421030b800b8540000041c81e550301d1601840c025084011002c80325510030500c1c00380141d80302d0045901c205c81c140c0001c42c1504043c0c2550f0001d009a800030015a40103010600101306200c10080b0349808054540d01e80b40c030381038400910f000c2c8461902c0b41c01030400d8200400ba9411180700403450380c040d5400c1050303d280040c428202d0040b1700a030741d03000900b0000340740818094200011003c10354010f040c60550344102c80412188140c1c012514032102100400005130804004085443d1140c003070411480c0004165071441c045c1c0c001c8405040c1d001c168101d4681741c0c41d40b004a40c03100340d102003400c500c031685c031070414504404003122075900413000203140b0548a032030f80301165446001808601c1c0c001c40c5901003445801c200300c003010341d2040c100c05088010001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 623708651 1250 623707401 623707411
    0xc210a18050c010905093603071109061801050405060a081e010b0105071a1902040e1501050a0c26030109050702150108030d1508070308041e050a0902130b03 69
    0x82c0700541e1080005410350f20141d01c0240b04c0c640a004010400305080024240c992400c2c0f01c0503180686c94862a403405030007103d1810611021a19404200303100701d241c07012440172503890301c0ca552007804000e00c401601c2948415010399500420035800c01e90081900004000c1100200d40d84981420340760401c0e02e15025000d82c0040c802010040f400c0c03240b04006042071034101c0ca401f92030f0705c3e013641114003075508000210441c000180348001c018481d1241d020010390941d41c45170740d034204c1c201c1184140c62644000c1c64500c3c2d0015550b00500c100c40c1003117029180c40340e0700ca000382c4540c0f08600c108409041181580310012101802d81c10055010f0408880c00184500b016403000789480301c8000c0000e00e0066410061184130000000c1c0c602c020094500413403032800712031b808200c420701c6a016090910030880040304112141001d030068a0303880311079020905c858141d031441220b2078400c007130b00320002040c14404801a5001031240320904142c19011a9483c2da0300c030895841103034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 623709901 1250 623708651 623708653
    0x1a0604171e1507050f0403150f050a0e070e2206020d02040f0e090111031f0e070206240d06020901020109050601090f0b010207350a03020a0b0c210a1805 67
    0x2d107030182d00c042d019400f600200546400c0c1c1c10114107088400c003510880c0405404a1400c2440c140004540d130000704030603000001c1842181010041c020103800110100000c0c2d004226003c24104010142d280c842c128082858103841c0004003071482606400c0c205441c41502000003244101d41800204000c12040e12030705107103407504030309a04840c1b0107080f040e11a4145118809400750703a0f02926000781c04500600400e040b511040324080d030f401d50000f2a8008103000300081d107500402c00c5481211784070030068102d440b00a2010609000340d004a0748905101319445c08185550701400300c10006000015010402d83c540e9407030000b09a0014800e1621010101280c03c000d00841c00000000e0008003441d42c1051510070000c190408102c41400552802c00070f413140d43c441d4901c010305040140c8204902a040094546d41c030701c0e01c00d076018941180071030000900e080484a10003a50a0700d4801c462485c3d1507079202c02d202a180365407854035112480d640d0003c24901d403501070f01c900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 623711151 1250 623709901 623709913
    0xd0503010906060c020f06090607140303061005190c0c08100b0f0303070c09051f0308030916060806010c06020d020c100c050a0813051e101a0604171e 66
    0x7001006940e030702c0d00548100084264200c0058450f8040700b5082030b0110360054a80f1100c0c0f01080141c002d914002c4c11041091300d48001204008c00114001d49054400618238140c1190035551841003044481c0d1344103a00d607801404ca0705c180c111b03420310382c4108541c502140c4e403410390341d24282030042088002d683d10305803000e052610b0010300c00c030300f4825005181004080d80f5015075405252080310b8001e83c480300000d0400320030301414003d200098000440c0c1c1c980300d00381380c0d15580044426020920428424a00c007140c407032070000485500b0342d0f030301d68a9a28100115900b10b040c0764101d9143d50240850344888003d0300240c0310600c40c5400408a0450345100b21081e52880701ca81c4091080800c112014180d206640d07070b50092105291050140b042d10380755207000800c3d10381040b500d1844000c0d401c003000103e03014580c00200f6205104412105c8100160011403440460340140200f004200c003028456060048103035000a848a0b03003a08800303110701c10f001d407411240f903801c82 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 623712401 1250 623711151 623711159
    0x20304060b03070f140103051812030403080a1413020a090606020d0314011a1c05040303020405040c020c03030a230409020c0f01021603120f0e06090d03090b010e13050d050301 77
    0xc203c400028403130381d41450445442e00744501c1525080300d100e0360405440f5400651810380f07445d142d01210001204407803041001846a424a82040c0c404500042862000c1000302a0741c1c00346202020f41a0b81e1104e0039140d427a44010040740e8040d0880c7c00c454000b00000e2003245621880c0020401a005000019428a0014200d810030792006998921210050000200c84e6200030003203c06034062a1380c9a8102e08038a001c181940c244a14850800c4200000c15a0603000b420807030754161414000c2010503071f0240e0311031210100482e0140d000307203c030070100c510800c0321151008410f05c0b0070100b0f405029100c40e10742c2c450380240c000c81e80c0009200c07501100810641c525415814000c604240d143c10021802009025000c1c080000a0b4400c440380040c07075004406003002d100d410000b103400808001d03142c080445910700c5078041c1c0050f1070400c1d07000e8040c8586481d4803402c0340e000ba03030a1480103a00c00c1e0020309106200c20340b181c440b00000b9010800b09008040c9074680684030341c58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 623713651 1250 623712401 623712403
    0x902030f031809010e1506040f08100c020f2802040203040b150307080c100908010c170604020a080f070318050a05071a0304060b0102030d0f02031f082a04020304060b03 74
    0xc02d84000740515222801086003400d062811a001041c1114407071140400c20001103d500642d00070f400e11540c044000203e103440006d8410405803000c005000000600b50107907190100041400403a41008190028003214180820940d20345211380350001270898011900b20303001107404a45c102c011f40188007c04201ca91000d43d030320802c500030041f040c00c2138241603d07199030b080200c0c01041603400390f038000c41c00f8810000103044180000c014034502104005c18070b512820300300465108500114440c1d04180c000c81c4c82880e000c1d00c83e00b080c2e44a00b081c00d4a0341e1002400142019070300e0903400e07120300c40c00c546000340c0b40c0110014202500c041c2001400d140d51540b08070300742c1c14654092400da8004105899105401c59070008080070782030300517030031840380503040c0d00058946140c07000440b0482d40591300480441070b10002ca0840360905402c401c200b402038582c40e50040114048034107000c0307403e420ac0c05010381011241c2c2020b50100b42a070304192012989a03407141c4c6500d0090070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 623714901 1250 623713651 623713687
    0x606090a06030201090e0a020415020c130b0a120203070e010f080d021b0616082b020301080c24270f0f01110a0c0602070509011413020a030902030f03 66
    0x3420801000460b185900180250046200e031614088821001800c0401c1e01e40c1039900810b030500701050b07038400038200207480700f19030951240b140720540c2440c00e0040b40c511409114100140c0100741c4075060614100d030000240904070f905118105020442424a0306024001e040e204500752100e814444405d052480c04031a030000c40d40701440140400310725800c5c0950a47d010340348507070b845090036000c910154205002400401c0006105091105540102c024440d035005090b05c1c2d8085900c1200d00f6880288a9107040c0d5000c806021550b103401c500c403103440d0b1003000c4401c1055085107a081c6180e00a161500c984030b91040400030701c0254040c921100039002c40700249100c10351000251205c030b500f603203141002000c85015600620030040c008107590440d00b440d1541d5528a402541c81185000d001d014110150002420320301c1003542d012a510010141e5608a180c20000002500b003814000c0400d5124210340700543c5041c0910000515104099940d0b820085404140d40c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 623716151 1250 623714901 623714911
    0x6060c0c08030903120d1506020f0115080c0405280902041407200c040e01050912040e010603020a09150309121706090402040222030c17032a01060305060609 69
    0x900b08001c4105140d60110349081212461002c0d951130304180441c090082c40c00360300c2450314094034680421813640000c0c1090420032424003d0054100d800e842e0020302e84584034040316a80302d1000d601d82441c007500b10300e9000140d41c11100329009003100ea200c003810304240c0c07a40213030b545080540650a00e800755909000b01502441814101950000c04076445524078a9010101c40f00680008506001c1d03800c00c01701c010402d00040225094143c020101036805001520640070001581802001514101c45120440e09060303840c1c0340c41034010b9403100c0ea5940c1042010200070642d01d0420348004d07001920f659001520000900d44000c03d9407030500010240304040d000b81710543d0500148660126050f2035118154455101090287c040c0080c040e1001c102d4403120103860240000ba401107038040d542c1001119699000e80c8025090724802143c0c54004002c035030589003980d5540c8140f48a5600c0c94940013011b1070041d821101150803c40310f41d00000d0038440b6501d0025001a084 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 623717401 1250 623716151 623716153
    0x4110907110a120504120c150305010b0703110c090f4006021b0a030224150d0206030a0b01270e0403171914061e060d06060c0c08 57
    0x4164421074540d12100508001e0605002110a0407102d2040c025a401425400080301c2640c1e07981c0f0342060440c404d800f0300341840340d449282500003407203801818100c0d0304041d511803800900b921f00302d83c00801c880c500403071840746034070b0882c0d280c4501b1b9402d4410b070242e0b004450142043d02c0c1001c440102c0c054140300c4a00654429500c2e403943e00c0c403248109010011103030031840d00d8036219010f40501690800d0390202641c2d8a81a0745010843c400d101c0d20030f07401d41e03801c4514405110307001e086180d00d400503513185000191081d207480b80501003100c4000c0c942d0000d48030b030768001881a841151000325041d11109101c1032541c0000905e41ba10354031540c1c0c1c6080d40d8507440ca455031803400307214046180c51303100302007010300d03004a4411000d1224003046140910304020480c202d00413980e80755080c5450482c41c03510078235100e2000e501031b02c2e005003070840b1340091418000740010045c2116600c00300030001c030950b03045188101c200401c5681c0f50205641703420709004100951680c0300c0422 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 623718651 1250 623717401 623717417
    0x26010e0703020a15030f02030a020702130501030f151b0203041d010e1b07170306130e060c03150a03110a0b03040816560c16020904110907 61
    0x40e40c2d00c204040035113a01c07885151031a111640d0440190622041442c0a107100205000480c4495001003408500a44a00504d04500c0344e14004031402440007520b000694a00800000e00300001c410030003451400c085050f0ce5184200b0b24003040c603078202c0c009a440040c0c20800e9042c075007a014003014190040001a43c0b500920801080004150607400c042181140014280728001d40b851540c0008413404c030250745820340711060380150ba00d50301c2081c52200282c560410b40c0911045005520045d205035241c544810101e90005810100755001039002444151114100d0342d0003107008040341c4a44642d0f440500c00304d40169040701c5a0306004000304004101040c0c2103070349440b50702c50340b4881d4a883d82440d043c146901032001060b0b0385440030020030700103d40d10307504061449a02e10a0501c0071103000c1d07110165410b143c03201c2a078002c40050f401c0072111018214001c9621156104841d0940c000385070b098084a040310241e10700036110815003450021694022a60700301400c2c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 623719901 1250 623718651 623718653
    0x8010e0a050c0603100b0d20091008040201020c120a173f07020f060109020a09030b100321080a06121428060b0f09061926010e0703 58
    0x81c48a480000740b50040d40008041024221140e0582c001020548515526800c3c1c2c0ba640030041c0035941e801424280001e5072031150418214100d81006c40d000342240702c20114114191450200100242d0540c0140b0385080e8954442500012a040c104006000365068030702d4540c02940c90b03266152151a8107205800d410700d01c0780d03002c0d40c280c0c410b01034120b0300b00403c0d811841340f000d400048038114680f12050012551b00000c1c80310000d0003079015030300203a03200c00c0400e049003e050340160020b104070390f080022804140e4615000310510b100300407040c0d00ca4480340041158103111440449510f5034007848107500c5900540c02c0704004002f0f01080d407410210070b19100713280801070540c1c03803001031401401500300004826003c0600c070140800d0300a851000c881424003500340d694904240701142d8516020174400000903004000642540b50b03070f414001d0480560480360b80031a00902c001c42d041010031500c8030350328000d00d6414a00b50300d0070301c11402c1d5071480d9404500365103e958284 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 623721151 1250 623719901 623719903
    0x13150e100f051506030a0b031507030e060702060c1606110301031a09060a020f0c0d110c04061d0702071d010f090912053106020f151f150908010e0a05 66
    0x4481e0f4141160035075100d03191003545c0c00080c040c030440c41c0e6044c40b423039105003911464150914410342c034a88027005400041801540c442034129402001a004900090419440c0002800000903101c1d0135101d084640c0d034419040300c050041040c81c41901000410411903625210089025524003041c2d0905081e80200c4d601e40c03018040700742c0c454010400000c03620a800c00d48040018000c00c40c0e10030410701e4000f512182d0391030b030503001c1070103800c1e4135010500b000d00600c03044856440102000b641190072803605140050000011401801c10004240416040840e14845d1030912041d607949004c210710340c5012035602281c0c459081082c403001080320b40c10386401c03081580c1081750b56416001e14403804080d0141c1582d0143c0185091181800d0401e1050f03c00c3d9012902141d01d064086006103592740c501c4c01c01c0c3c015666050380043c0c0411291a80044000c0c28034190070001902c4115803042a805140024000b41c40c0007410841028240a40b0554418003000307003c042c0781a0300c2e06 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 623722401 1250 623721151 623721181
    0x1503020a1d0c0a0504030222091101090501030207051b120304030302010605010912050c131d0102090411030103051b0d0c09020d140c27041e0605031513150e100f05 72
    0x19114281403088034030241e41d5002208c00286910340104682c1c6002e180c41c504451003403031501d00040c10314502141c1075009200f1100e1807600031008000c1800d5035aa40c0c4030140034000c105801030340c2100da1a8880d0360400152000e180b0075000494401c2c10000010040c42a6071320000403841c0510352000410008906a10f80c00410f070b5a800300d10807413580c0e500262503103081c041e40540c504140c2d040c0089042d0701030901210112814804000550b00d02e038000e010a00002d0000d40082144104003406862074101c0001702412400441d46140c540004154047c0c1c0a0688150001104420010319200745101785903a005641200d080c402280d0800c0d00840c036802e800e40746504410100d0b0707004040d024110aa0051040c411264410341c4250400228549a40560308081e00403510b8a0b000c19624034406240141225543d100c41c908094030381124010344460750b2107444880900194000c005800e01a80d0007003d00100550049040741d0100d002d043c0c03000c0ca058240b0130300000728511 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 623723651 1250 623722401 623722403
    0x19090507020d08220c060e0a050f0a1211090f041401090305220f0b12090a031d04091b0503071d0601030903121802090603030a121503020a1d0c0a050403 67
    0x2c000121a0109070b44031111081c1340058690556081c001881a50280c821404600213583c6220416074036801d004a070f0b50f212000342d40c001100306082c8004074141c140510b400e40a0040c410981042c030004c6110701005a9102d182c0c440300b4820002400a500500d40441480344000c2040b4802920010038900480d9001c803a605808008001e940489648402c0030f804018500d02d0f9a42da1124004881d03403004038044444a0701a00095000001044119419406860349004a41c6080d80315002500c65a2840d038000e03659800400498101c0040d806402c82581c00004000d0a04c010140307084080c4c1c1c031107520941500707111007025110443c050740228081c00c0c041078101d000c0c03509413503d44c2048000481281b8202545254450440e0070741c19090003540d28a40b16200c0301c060644070f2142e60b96a20200300c18003d9511561039a07448000300c4e20403011007220300e988960000390720345981d50140441ca00b00c0c0c001c045e00349504034522a00201503070f500b1881c0c0b88115001400074011840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 623724901 1250 623723651 623723671
    0x2101709100e06090c04150302220c090f06051303140601031b0503190302011d0604030f0f0818101805010b040b0108281b030506012c040b19090507020d08 68
    0x380b0301f40c040e26082841c4082c60303005019200d4030b07440f40300204031900306805460081342014401c619050050b006081524440c3c0c14000060b400c0850607030780d6900c50302c840606a050100d0010100fa02403500080100081307015103015491410a500c5154880c1d2081c02814142c500810440d9000a0030041000b81d00c0301041c0210703014141a401000d1281742d00310150390800c00d0000801c40490254841d07482038a41c600300c0c0202140803100212010207050200d550000070030030050340820700c041180081c1003181c420300381c020800d40a440084185e140e0b10364100d20340c081080030a02461a6185050f0740400802c1400347c0020003030035016140c201e1113500c08004507043c801c3e48007202141e0440710001e104500b80910f80580c40e04020b010b040001c5d141c1404110158401d070000380101c51905d640506055080880e5200c82d404030155590166480340c040c00f454490040740071103200131202180d0300d00e00d810348110568000426140464000080f122000741c1c0100d2000d4010038101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 623726151 1250 623724901 623724911
    0x304050108060d02100c1401050115050d060b0a0e09240616170723030307030b03010605041103040b160c030507030c020a0b1c050603070302101709100e06090c04 71
    0x44085500c180403d00081d40116045505070303502034108240000040c4280700b0200c6070200c08110600301c920078000c46800ca848034803481007440c07059001e0310f000f402074100094250382d1070582009550110403040e01045060703511407802d2814020159002544502c4502840e20f80703400c42090541d04d01055115803000b02d040d0020b1404400f800d0800b030360201e4a00c40815900d51203642c00c0d0414801103850700327039050440c803060031200603031074185480304003c505548911070706170050100c0c0c440c000c0d015940d0b903034002955600d60060080f240c0181e040c10395070341028103010501e408018031082d0795000c0610081041c1e613000c84c43d440119010f140158803040581b8084602c5400010040d5114140c40c1020401140c131000401c1c0c081020420b0410041c106d01d0a5410742c0c000300c44042e03240d000040e0800143c104440b006c8415100d40c9010004a4010b1240c9948641c040c0c2d20301c101c82d84800344282c680585882400a00c1c00303d48001c107000d15043d0000707035442d084408250b0144c0d03211 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 623727401 1250 623726151 623726161
    0x71208032815170115060f410c0604061509050411010206100803160602090a150912110f12010914070b0301030b0c3603011d0304050108 60
    0x1850200c41d0754030030001444480044505040048003501420141504030124800050014030558410040701034031510704038030300481520803104507804401480500800d41036682c6884401c0f0703d01c4080e000b80c410115640540e640512004003c1e41d001c03a080030000c011000c800081e0f101c0e03005501034408240848046a403500305981503004000071410041030100b00010052464107400081e400c44032607546000308041045654800c48810360030801940e0385900220000507112800f07020050300e0401c03040c1c0032034040581c07948544000b09490036044005c66000481130000d2109103000d000e095000d80712403a00c94403a03c0e01c1c034441c007100361018015841c0c42c807a00807001c071090300070440501282010f140a4111480d0087c0340d0040c1800850782c2c4201c9410340c2e0699030000f41360580303580d0f0190481060781c00001c3c03900c5a845002040440140713030803d1b00320519100e814a00e450b4820b50180340c02c0d90801410079410034400c1d4458840fa00c800402e4900700da0003440c00d11b52070b40711 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 623728651 1250 623727401 623727451
    0x3031407050c06040e1f0506092b0803090d030b0105030c0705070803040f052403160306031b06030c020d0e040f0908040909050d02010908031501020f01140907120803 73
    0x1a0703200c190b0042d030f0128000614015912030144282d4403a4554203c055042c0c0c0c1d000140035013400349550244052015002c5800c0040055960125260040511520500400c100200b4011003141c58110000070440ca01c81d0600ca02c03081c08880e13007002c2c0020140d184c0043e02c81d00004024801e0210b0201ea443c05124040140b10700400c003401c1a02c0e6501d40300c0c8807040f0269944c0c060a03014100b5404540c0d000c550b181511620060702d0f400480c25521510070800400000840f400c08242d160300c3c011001c10703a4000c280440403259504100c1c09454260054181c587d10301086095400c21003032540402d0704041c00d40c1b19514100c40000780c0740283d8103018000d20071054054252480894042100c151350741c03004520714015412a201c082c0364183c200e080e41c42d1213000505440051001c264544000c284000c414801401661001182840d0140c21102102044100040c2104c28498066802e03c9001e0140c00380044500201d4402d88a14900307100c06480112103880208030050000d032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 623729901 1250 623728651 623728663
    0x1a0303070b2d01060f20010608190c0303030207150e031c0e06040605091612050610120b13060203040b1f03021e040b0303070f0614010e04020111100e150906010303140705 75
    0x218684115006c1c0f411600414020940c0b03020306241d61082d0040001a5007203a0041ea9801b0b0380490000002411903a0880281d00a00c0c0e044a042494610f2001c2c51600e41c01050740c1c2648401c0119214080640142c04209026402e0b200c1c441c506103442d15080408101d1690080d00441c000c40d540c2c8030012005c0ca0095080c0d0102c0301d1503400b5601055080c14213862441d0030380503400f25236003034a54500c0706640400302d100e030745400003e03100d04400095403030101c036074000e40001a54161449036240d942c1660310455045428241400401500030050020b540c5028520981c020b58141983c0c04940c080d5010650500000914880038180743c0d21500000a0840d02078241c03074407014079203044d05c0702000c1c04104595490034094803908842d1440c10650403140342c0c9a00c50020341307940d001903604101420341042c0703501546140c843d080049004880d025400c100c0100022030000303900c0008240301410507a000d4018000410100f42d00c4814071024081608035580d82d0102031500e107240507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 623731151 1250 623729901 623729927
    0x30a1515081b1902030c01060b031627090b030d050c101812020d0e030613031d1504030b06060a09230301050115031503050607031a0303070b2d01060f 66
    0x42c6200c4000c3c4200d0f50f01101031300c00c14045100034061551501004000b0340801c0324040c0700006510681154144034183c0c8803442405000d000c0c1280055000c409494045500b00c1c0f5680c1e9240c0401001a0078100b0480c490b02c821450000e06000380e4200150b1903100a45604981704d80710402c3c4c400506e812000c11000c3c40d03110b0100340303071600001000b0303441e084c88140c550701088080203001c17103500700803441034415505624500039956031581c00340d0f006400e00517484819050b580c00300030f071900c0e0316194120b803a41900d40d0035260380c55450030840500004010300d0040c42d06201101007643c2041e0504140c40503420301240024509807488400041080d05507403640c2030100000f40c20032411440115503615540502007580d12010203c0040c41d140710040842c2e100400041c03000307100c0d074002c1c1403404001491021048000d00000d03c1c41d00a020300380c81c80b2100a092088042d0b03025030bc00d0441d940710f68075034200c00d50713030610307940101c814030402e403d00507106128111030344295650b00240c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 623732401 1250 623731151 623731177
    0x7050409050607090e010803120723090f0303160b07050d020f13050108250c020604170106052416020405040f15020c0c10020f03030a1515081b 63
    0x61980c203000d603880c2c10076100940415500300020489500d510026410b0b11517201c011494910700c0c08001407000d10040c003000422510440c040c1340102c00e03500c900c05402061003483e0312108604e04020b1446000c04180340301360300030031603044140303401c420259440f42c0200c0c940750507580c1c0d078000361080e104054030071207c10310001c5e12100c07146842000e0b1001c1071684880c4d80b105503d900065669010a03600300c44108100c07290107002034500c12602541a030380d4600045000110741c046240390304241c000041d0880103140d8044100c009104000c000c00e000c80b0385521884001e0003018038800c540140c11601f003c005010311a036030414018180c5076901810400c40c034941130410841c8011514401c80d1090314031446070070552000c0c000e0725108144007001c0c0244a40100810145106480d901c1d002c0d802915002940381c6402d0002d103100b200c0c000408030b01070701007108031990b4a4050300301d10342200b1a600c4007000c1c0f642c031900459010b485103044110041200107014041d0154618106203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 623733651 1250 623732401 623732411
    0x604020d0f12030203040c141807031d01090501050604091a0907030b34050a0e180f010602010e030f04030605070c0c0b0a081e0613020d1503050d09050108010611070504 74
    0x1038aa85903004620640c010303010030b0119a15120b409007040f01000d005980f140d403404581c422501050680b03504405607090016445500c1008cc22071021010542101d030395680320080d00b44002806241d030703ca8002c4504100b91852559040d0b11940386030041918441c490300016120f410810015016540020b451019450100c0c0c2a43d1030024440c1480541c6007000c0d01854081c0400000c6030041e038050311014180480d60000300c814100f0711441c0d0360300c441d182480e50f4002d1000780700305005600c1c441405402d913040120203425601c1c0189600d840f58003c100300c00c601e100d55007ea46c142ca902c00b8020441c1c0c0c80781c3c1c800b01c0e101001c000e03002d40b0344510002c001400ca1210401400080c20701d44075101940e507110004043c10f40c44850401454030980e00040d0140740c10080040c0603c4026401401c1c0b001481c2104119040030812450b00401c46030b081c424400104540d82060110f40340241c595400d001c0003d01d0301038188682070a0040028200e1507101e407d01c0124054803002d402000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 623734901 1250 623733651 623733683
    0x40f0204061206060504170309120a030906020703150e030c0d031505041116140d0e090906100e130503030a0c03060b16020105030a180b06041d0604020d0f 68
    0x10003035009124180101c2c444040c8100e850126000710380440361140c0b00c4600f070a01e8a052000020512000807100380000c10183d01d045d07035194100822020000001c0000b140c07141b03005894000c55401034029035102410400000f801900307400e4040c0b0240b48082440ba1590400c039155007d9403c1c0303005107001e440410020f199150748100881e850a29968507000e0b900d0702480f003100c141107805849801d0801421059007561a04c00300807078445d901c0541c8104003100c24908020184104d940028600c6030051000d1514925440d0080329000c05400d0501348005910320302009413007074511074080c080c006400c00e8891203400328415004020f403580d80c82c01c0030741070300204100211840840d281440208901c04160281c48412640c000c1501200d843c9400543d0715400c0284210704071074503039440c68800b4441203480d800c980c3c41040005140c1c10702c01d0070030050f11030281040741c9044414940301e00c180c42c0001c089800c036805481c8141d5141c22410310542d4030b842001c0141c480003810030108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 623736151 1250 623734901 623734931
    0xb03070c05010f02070203071a28090b0c0a030f022d0106090c02030f030c0904020f0a1106090d11070806071832040b0a151d030a1202070504 62
    0x41c03107280200180898503003100200c3c0280307080650580d000e15418403009078200d4108940c482a19603981c28210507410418014804c0c00c2445004518508040005a00060000302409a4034034a508041181c24100e03910b800301c1c00040c08000200000c201154000d02c041407610720750ba0210003601180d44115540303038100c0660440765601e82000000c1403500f52156000041042e4040c41c41c2018045080c8410b0300058020408160104000b02c400d6896100400c502d650303000b1003640380c0e0342e8290003400320050301c000b1800b039802c0441000500f810100300040c031741d2480c1c24284002074090042916005141c0c001101500c01c0c1000d00528640050341d401c01d80203001c400400458496910f1745034444880c072910090307184140500d40c071005107988100b8085024100041d40c00b11040012544000c43c1d200e191610144080840c80c298048402c01d1400219031842c00f20700b41c40350110b0f659410454014000d0007a076041401e41b1740c424080803004010050043c002d0940b00040c103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 623737401 1250 623736151 623736167
    0x2090108090609070b030702011e0603020928020a050f07060516050403170307020309190611060f070809031902072628080f04030b01052b0c0b0307 65
    0x680424010030015285550024401d4454481080680711161074056910b0181e04081d1040d005c1d0f548458641031400c44103480192000040200419150704c0e42c0107101d012000548171b1005040343c0c10b4645a1104960a44080e802030380000503641c40d0500b600726018002c1043c0b100f1007080c002014010300c048ca401c02c034001c0889d00c8036110242c890700740989052145100003002d00c1c50700041100300048050146900c4200c50058908e045020360001d01d0260000103100c500e00e503503d80510201d40d01c5007102000701039000051044c1c1c20031690444070854010207000400c21a08000b820141c4248103a82600071080740d007040c2110400401794560016006402101d08078200051407050400c21004000203444054603c0c000d4601d0380c11a1410800500c00d0748808240f0382c00000b4030040004c01390003449442e01c2d40c0f00c07429854021411001070740702503c222170b5507082c0c5e140b15480030030100b003c10b001c0c500d1003490001454907803400f8640f6801000d00b10070100400401c250800d100e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 623738651 1250 623737401 623737417
    0x1018050a0b10080411010504030b0901140a0209061602180406060915031e03270f06030507050d020c070e010e07030506120d080405151e01051507082b02 67
    0x14404669000148060403242c401002d00280c1550b000c100420204002c440c2000010700d8607900c0c26442e5112028051410355034140d1a130b41d950903620500e0b200003003494103d10709032401c4d03141c0f40303005001070894010741c480c64001c00c0d03c05e81d161085540307070302c94200032440c5821034158a00d03040c200720009120500c01c5039a864140000f00e41119035084152007500e0303210300f500f100780914080c41c003291480382070114188804200760b00740c045243c004074031080080c840096aa01c0c10041c0002c00000e10768008418103061800748550b05411200342d07003846020742001070301c41311002e4210346410036540c0140d0031031040d84004213070300d000366100d58400d00c41914248000d40700c200a101001c0140610305045400c00f01203040c05c00e01c14042960404d0040e8111508a00340640346905247c050320a80050040070409101d0320340c4e22826a070051104940001d00e10f0020901c5480070f20424000414004000503110755080e83c0e22074509043d09a510406036154191003444003d502c4460 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 623739901 1250 623738651 623738671
    0x90c1106060a1a07060e0105100f0f06080c0703020309043303050309010c14120304142b0c05011d0f010e0d03090311060f1006050703021203101805 65
    0x8000789480c00c222041c10101c4146000c00c158091505031014466040642d040f9103140d2078880100318100240103250068000030481c0e002145007511035840c2051a03030005c40800505a010400c1c035420415640c0d00c180000000e80da250320600c3c04908500ca0350001035030203440c0013004051702c000c04031483e042d00e4204100d040c820000c40f40080c90a00e0510000788250310802003100b40e1751042481160241c45540c0748507c007a01e484015041c000380c548810301c13002021040005100308803401c0c0d00001c0b1400007519510841c4482d1503800c070460072202a4541078102000c0c1e01500ca003030004c040ba030b0003c1c02009000d1030000c1d650140d0f064010014a20300c03071401001e50951040c07180c18051410300c03000304400d011481c0c00741e002d8010450140c0610403c0e14504078092010b002c2036110711a42d100400040c81c00320190001c0300300680080c4c080000500a01700001d8000401002403060f14041c0381e10390344c4481c4111545081e940206480c44585c010704001d40065402207409214910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 623741007 1106 623739901 623739913
    0x4140103050a17040f05010e12101d030901170406021c150e090c0108090f1e060f06010503010b090d081207090501111002090307090c11 60
    0x103032007511960400040603042003408500d140d4000021100c0c541401d0600304568030488090103114103000b00340d00301080d1552080c80b00000300100038115820700b03001100751405800c03400c001c0d00014501d0748840086180100640d03021800c1179491002c1c0035a681d4900b0000319000d002035171066420000c44030240d40c50b540407520314408540c0402c0c0010852240744070900b4651001242d4515402400740002e40441c44d0342c40e07804246004910358a82c2c0c10400c0c00e103c20100c0c602003e2181c01c1100e0314000080c003011003a0084c01d002d840c070b00d9075809800ca01040045a00b50f0005000304014400100c034000500150a005020074440311101e50b134012140d4401442d1848a010307020811007401e40c492604001740800380307030982c0c0315451b0aa030203079079003091018180c2c61074001c1000c0c1040e031000c000c1c84004040a80b01800100d088030000307400c030f00340050120042e000e50 = true := by decide +kernel

theorem cover : BRFrame.Cov 623561151 623741007 := by
  have h0 := BRFrame.cov_init 623561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 623561151 ≤ n) (h2 : n < 623741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
