-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1525
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:24:20.031993+00:00
-- url     : https://prove2.me/submissions/0da7ecaa-523b-4535-94b6-59dbd36f6533

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 274100719 ≤ n < 274280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 274101969 1250 274100719 274100737
    0x2040c05040b18010f170609072001060801150807030209190f0b15070206090603090316050a110a08031c0e0a0501060906060e012c131d03160305 64
    0x240e4186540c9128641d200e40c0078002c8580780000151216140c0d5800540e045504496810003083d8201e0441c40e0300e0341040c3c0100745900c100071300702c0803c2075907024042e583d0404210204061444902d0250760f80a0490392240b01920b40ca041d22017107050f0303c0001c8500c00e9800c0d2030050f0088604d1030702000600c20001d4a80c034090714064003085c00e914170511590001031034041e40442c0360b4181d50300b009001c6c04144101d0384603034001c1003142c0041e65810102c808e00c8030201c0b40d8035165280c94612914500500c80e072000c2030000c1d540000c090100000b581640c452290710616070442c10b034810302c11b02c0c580611403210a94014401c2034401d11a000040740c03452020000041c070070291071640f624007801f00c40103031216551104144440002401210042c10040c10400c54030440100000c00304400d07032074904a004515041114000b44c440768514010034010044000d4171202c4445100416924440c00c0451000e0030703265850020200c1658240d000c0c0c200000e064071100c0d10207032055030001c000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 274103219 1250 274101969 274101977
    0x1902031e150934061202040e0112170406080103060f0e1608060c34050706050c060f0603030d0c0e061224221806020d230402040c 57
    0x421100d100346105441070000c4002040c3e4003070406850200780c541181a60043d0302110f80045000048100a0007141d8241c0740103030301000f601d40441d000340a1034009122040743c602c00041c0c003c07951421460498020740d01d00880b040460003040040c8524452003000c02d00c2940100041171440e4010350a042c600b0002190880500f8052810428049070380d05000e00d460a09004005080064039402260b0301c044030301e05502c0b8034404514238910712281c40100403044851185035140014400016071040445003010786801015100381c01400c82505140b0a11001929048401d44240d0183c0070150146290000001e0794a02500711400c03003109200140841c0140d81c1c23a0100101400b0705030228207507603070a00150a00454512600024444410700300c603000035030380c104030344a403114804d9030460000c00d4940840003402a401500e000300f141d5060040920241d50014824490519420400d5824039209a140031140742c100c0310040c000040000c006091591100700c001c3d44a042c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 274104469 1250 274103219 274103233
    0x4030c0306090327060f090e0c1b07090209151303230604060b0f1225050d14010e01060b030604020a02030408030c010204050a0e0412180b0c0f1902031e 67
    0x551380d40c00f80c0090b2140d40e0760529800400040d544000b4084840c0540e00d085280185040e200c040b040a016102e04681c40c0002500c1c6110840c4982e8000340700304040568108680d10b42c0180000d4010039801030003560801c0324141d081d18060300311219034040032590154142152a00d00d45204110505010600d4001040040b48001c00c4890b00c0b50340324800209501c5200000d210310700d070050340d038280500500740d10800707483e9010594041ca01c0070b42c80c0d0b00c0c5002c0c0c1050082c1907a01c0c002d500142d040340b00d01c000b507024000500b494044c8c101c1e48400900090129548070340c03c0340d4151160600e94030b420b00c0868003a01d00b6400030040c2814a104881c102916440d505045900040d00705c1c4441c0c1d0300040c00c202a0502d140002c0c0140506480130841e0300e003541710303051250714100501007040482c44804000310082c0098030050000c0301282611107484c3d10b40a5640c000240d00d03018503229980d1000c0034019030314998202d50740c0c05000b4140c0000e0003004040c1d80403110401c8440ca0103140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 274105719 1250 274104469 274104497
    0x6080906070807201f020d0605040504080a0507020105090a060810080d02030708090d0c0e190212060103050a111605010b0f010c080309010f05040605072006150a120c08060106030204030c03060903 86
    0x1c600c6200503c1d817050040e43ca407403a02e0744001b126a0365210707030302450520781000040792151059406411460810301d40d02e50790380c4012251481074200803039110329400404078840d903002d000d5910a4592984c6900143d0b105c554260f9542488000d060040c6c0c4104503042c0081d6602d0007600e109a8050008a02c0d010640d88000701d810381c50700b02a01c200c00b55000c01080103401c01d0011200c5140030f001714030f0710b44c8880c02c190100300010b215505154403940854070a020b954800c12405184005858031400301482c020081c00c000700f0b041d030380ea40c01d00d641d903021481c010703540041e9080305842c0d070a0044007907038901c2c0007500000c1042c2c800d5542c4803268205000e007802154401d0748104000201c07032401ea0000b40c0840000290002391082016101c11030003000103101d0742080304907100a1084c0c0126001030100f80c2d15070060300b21038019103482c030200401c85e03912505980c0c2e0a801e032641c81c0c1c0c03605411400ca01076803001230404000d00b1000c00205240c2d92260b04024000d2a040200014031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 274106969 1250 274105719 274105753
    0x607020d0c09021e03010b0322120503160e030a020d1e05071d0f01030b181b01030b01020303090a0b2e0e06040e03040306020a020102130608090607080720 68
    0x81d804080c00c0c1c1d0f00041c04410816032458203100d44040100700900303650526009070903601004140c04581280143c4203030100307041505d0500c041c3e80c446940022040e102a00070030315001990000031448800303030850003081c0074142500414801174020449149903400700035140c2000081500c02c40c94403c0c0300b07061404949800e000907406200108041898501c580c070651441c038402c080c118100c030052041c1a2300007080b07681100d0700081d454240d03884980c0801100e0341d8000c8030200c40e102e412a01825691080c560110b5614241c030104481c140240041e40c07a8072040310b5114443e0844c0303030150300040c034100104e81c1003401b5a07100c21044540c070b40400c1408200e400030a0802d40030103c03c1007001190311910703038000c1042d41c060004ca800608440e50320b00450000500046d0041116448540f00b581502c0301007103d0464480c2c02a500d284c0900032001c16103400d042070003000001807005005e4000540640101c3d078800740d15810790759000c0b0340311002c445804414021b0b00c030001c8006ca51 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 274108219 1250 274106969 274106993
    0x2040b0402042c0a0203071b060b0a0608250c030809120c060901050a1104290403080705010e01021309091104020f09090108070305030a1b150f050601020703020901050607020d 77
    0x10b0280b1424164003001490843c0a200820341c6a0090041040085d100e07840600e07144018040208402840000d01d040700143c8403406850f0b070003070210f100008056610404490081e003022028400d0401e10740082943d00b900c5811078800300d05083c050b00e001a1080070403960040620081c2d1b4143c92582d031040116611407400307d10306501820610055013820f22589410060408041110440e0041005074500503813144c00d40da00411741c1c080107082c80001d14402c403484802c6180c0e079540e490740fa00307080e01d4000039415555981380049441402c841407007103443c040020600201e42c18603000140d806090b032900112031072000300e81403241d0b6890310300182800701d0140b401c6070b490780052070a201c540c007816031002203241d00c922001c2022036004030448007030009a26101040311000c2c91800700600e01c800c0300601d001d07140c04159a61841c254440310911010380018040b640300d0070012a40e6050601020358402c41441c0100b025241c014002c1c4205840a0722100c2c41900946649001c404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 274109469 1250 274108219 274108259
    0x608011406030c09010501091a1306020d120209010c15180c083003060607050d0203071a06090c09030c09040b010f1a0d0b0409060213031b030f02040b040204 69
    0x250082072003028034003884400b90981081d00c240381e031907143c00002040401c8038403034400044010480114a00c03c118112410320710b000708900341d4a0341d6544000c2d501c140181c9a031001a20381a10503810b885d1500841c0c0740614161341d54aa40c16464990b5408a4605a0100091551030344280400707070303000c08290500c90191400c01c1c1078901d400c00d0780c1d00340f442c45240b214604c40503030012103103820b03d000b49401c0705848903e0242c680d9200d00c0850802d114540b005011803084c000c000410a030f0000003411401e01c12042103401ca84001009004880140c40341e55010002000091059407041c2c0580000c14004040b100c074025184082440040151010f139254000c0100512002e04c81c49281d100a2004401c00e424208070100020781038042c00b4000350b1040d80310f0700c1181785a526a00104200d9801c40307800c565400c6c41119925801075544400c40f502151428503a0401e550ba00324081265043314103182c4100c1c00d80c4c02c02006007054895907511990070311000c00c0410840056404000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 274110719 1250 274109469 274109501
    0xd050a030b01090519140301060305060c090a1809060b0a080307021012110d060e060901030f170a0f0e030111041a04080d020a0b090a021807090b2a010203130201050d060801 76
    0x19041c0106c82412010600704103010b607040110810008000240040d440981a01d01036100c40105000581407401d0b032784000721800b8600c44480c249101540024a22032040c031007040380e4a102c40034000580e03101e2040f1722a40c0c0040c8202c0c005810011240030281c0140c1c13034448480c500700300714101110044c251224040d48045001c000410f524420341000c0d00c4655100032980ca0207000184901805020050400b445034602c4020440003090740303c0c002d000c0041460310381c03004210040100380010401d60020328000400e1145040c180308801402803041901f502c0c0c141090f2083c41c1c18041042c160365800c604010026102a05101710007003900c903a4050100c00c00340d0700780154a00d4018094559603007000401c0d80c01a0341d0382c0c0ea4010101171051510000c0c0ea00c01d14183c038041c8140d8801e440c502000188101d405d0b2400d50307a52501d804641b4012040d5049040d41c0313081b40000c4410502e8006c40c280b03034002660080c0050701031038508000c0811000d40b140745e020f00390395000e543c0b0300c255 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 274111969 1250 274110719 274110769
    0xc0f050325050a391509030302071a09030414030f0304030605010f09020306030304050108130f2102010203010b09061b01090803010612140a0c03020403051912020d050a030b010905 79
    0x2da5000e101c0c040d242140321107800000d4a406860b1440c3d000000102c034640204c5000d802c2004030007110400042072541042103844070500b4054065030044200326003079a00003444a144030341282c0b070940101c40d403c006608103424031041c42d032843da01c10b0709964036219080203840b0307964040008102135407041c18040303019490310180c640c40d00780da40c01120b81540144200904ca0714000f00340c0e0121202441c1c8000c06461b4856409002c022104010740300e0b81c15040502c00b40b04c800ca00b40545840041085136030044003403001c074200d01003800b0b0096601c5040188072464034000c03010303094403803c1e50b038080017008600380c543d421104405000c0302c502c0b50100040200c50340008208013515400c031003d0000d4844a404620301e03050080003140140d560302d004880040c031036415100a940c3c0541164181b50718918000101110404100c03001140080b85c840e140e0710200d9103038000003240e00c829040c948516010340240a020050a04008510b080042c3d241c0c0c03201644195004508103040304 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 274113219 1250 274111969 274111987
    0x30e031c05070825030b0d060504110111060105090601020c0a060f0e27190e1b180c03060d060c0c141f0203101a0310090c0f05032505 59
    0x240c5034002d0401c01841081d508104103001c9180340b10900014000c5800800e0449490580082c103898a0075a00013000054000c10804140c0c000790160b0302404101082c2c10040004643c01c0410b540d0350f22054106200410030790a004c500b0300c0d04102d0500659120b0b084074070128891b41602d600003000116001040c1003442e030095240312050200340c91084000418510035507441c0c2ca00040c1c02c400c0307080c80c00081c00700c02c254545680b1302002c40c14180400c1810240390340d520410301508080d0b0080d50364901c1e441d8644100b402c0c0c20448001c00c2c0070140c1d50781e448050100d810040c61a50010000b00f01e000005220344030303031260a1003030345402c1303807400309400d00c5412901d0f8600030a046030701a100c074880098825034806c080c24441d260250f513a595090084c00b1441e110f500104400b4162080554101c11003400345104210242008450540e60361009056844000140780455000103110301d10303901c110011a44040c007041c041c1c44506001e007017009a00c05881c10540000e00220711000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 274114469 1250 274113219 274113221
    0x10030227010e0103020916030e03041d010e01081905030909070c050f1615090504050a06210206090103050603030912031306030510060e15070b011406031b0901030e031c 74
    0x101400042c841500503604642c0400c0c2d038030307030003a00812542c901c1002040f0814403940100c0c1858451505a903203880e5900c000c1c1064600d00800c00100803604000456240710a69019040fa004e0390000c10140e69140e000010309800303280162150301040207061354686270000e04070b003d54265030f60b900c1440101e00380541044181891060150403074a801500420400400d07000d88107201e6644417203038555001a100c0c0d40b05a40480d81007400d040802100d40380d16805031084480508110f0b0184560340c0c24081c64440c4c42d034009501c0304080c8040c1001c0d502c07035404240c0c49003020341105c0c549982c080006105070085d00056030150300005001d0010402d00000000901c102d003414000b40c200005d200b6245003c40c000d0350108880600c041e0071035640c1c0c4070804802c1e1844a0510380c0e620184c140127041c000300b40507030142103e43d50b1a542d01e07420300300110386c4030340703c164003650f03d400e070003c0364091a60250901904254540c1c046581c1540c00703000030034031400001840b0090304250b4030548 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 274115719 1250 274114469 274114471
    0x5040501080c0f1203120a0605010806010c030504060302030c07020607050606040c0f0804110402040314010506150a0807120e0f060a0c0801050a030b04080412030c1a06061210030227 80
    0x154098020815000e50358450f070110f002400800c8951a1072002c0b80110145940540010f0280c5c803c0070382e082c0941c100c41e50b0700c03980c10380b00c003a41c500c04283c1e036400040d01c1080311424003c0002d030703081200704509442a030240d0303048810407900e1450716402d80c00185c1541c020803030650f1207410500c14415603207850711884004c0c1c942828454074108100002601c1c80c00300820103011240c0b882954a09035907a94122800f442d444807100c0340d9010108612802001d00300d030b00a0188104a0b14078000481e1081036402504507070b550a81c0c01ea5800b031040301c1c800c01e01101c04450a4480c444058408018040680d0b40c0042d40000d00c0c26240018091013035480e04400380e070500014000510090f140c069903038090729000b045500e510340f26840c0c8400c90348a10740c850424541c00802081c1051303401038116071186c0c000d01d080446041c500900c1c000c129401c0d0780f084e46c080801c10040720200c2c40f02d4800350303001b4405801003138040c0e543e40224021285400c001c44030542d10303c44140c62030140740089 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 274116969 1250 274115719 274115729
    0x40e06040923062401050d09050304031b060305100506132d0e07080402061b060705070201021011090d02010507050304030b010e130317130c23041b08041b0f05040501 73
    0x6410003814240070000213451010106040103400161500511445e400c031002e8681d1142c2100d6440e0360340d08103003c10000b0b808820003982034520300011014840d0107264007502c801e19441c20501c2c40c00042260980c0054265107075070b41c4c4a0b0300040c0300c054409641e80040c44282c517a4220641c518000034400e00d003500244004480d84081c04400c56100392040c1c1e0141d8141c41e642c0e0780c0c00852003030b842e13a0030513001c00c1c1103240710311001c00c00b00b07e90100160003014401e80803283c1d00441405184140c0351440001f1340341420602c03a590080c5401010041d960340113052192031703c140303030b15202c0c1113901580090701c40c0714003c40100440382d884401541e010605d684801c041c04c4055900418401e003a86c10b0804511680008c551040403409200801591000c01a041c3c00e544a050075080800640d110b200184d10b900d84403224201401180303540300c0407042010f2465030064080d11000300c05001074a810b000c14821005c01782840b072489001c0e01100c3d141421051404040005564058000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 274118219 1250 274116969 274116991
    0xd05072303062112030408040806010810320a02040b0309060124020d0e040f020c1606030e03090d030302041205305703030903040e0604092306 63
    0x1401c0070f040130070703008099202010b80a9407520341b42000e401c68060b5411408190154100020300c03510005a83d080710900600c0502010a01490003044810a1041e09039080304242c01c20440400701f00c2440c0c0d1206a1078401030070240ca908042000b50003ca4080706250302040043c00300c1281c000a00c404a04407041c3c240035100c000c50000d44400424202c3d406120b242d205540b016600ea4005158540790b004045455a807107c1e040707995a0080046c042da225070300880880c000740b02e406221380403210b0500440c506a0118140550a00c48140607400c15a003844081075840c1440070418002d8090030060520b200294502203e09004011030005183c0780d00403403941e99090002d86080001006580d03411254061983c000c03800c6149201c1c40d2100082c40c100c40e40b081070342c080c4036800b03070100c8110012061072080c981e80c0d101c04c1c0c40702c003d40d5000744030401580c0301400840d6402a00030300003041e103080c0307aa200800360801c40702500038148c0a000000e502d9004000c050f0740b0100e1204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 274119469 1250 274118219 274118269
    0x2019050c04090c1413050903121602030405090a060f0f030506090706080109020c0f0d03150f061403040512041d0a0b1e0415080109260d0507230306 65
    0x81c03040700d040c940384141105030202e01d200001315600c14007007031000381480c4d50522007490002043c80d2241c0c02400c400503144000008180d060b0342c0c0c601343c42c1d80c400d100e400540c0707014204030400112000c010241c6504d19126a00032580d58002c4c80110000c1214400e40c1d41c10a055240203810000000e0402c3c54590200318200907442d8011b50172411924480b00059a8940100110b03013010b0142c0c881907818130a003810500b80343da00d540001c3c0e56100fa07100c007041042c2ca910400301e50420600c11000020004034442025000f20f400544d081841941154a0500c24020301d61558100c1e03404922412031030034600080380003801f0490342c0100c0c0c080c803c0220100f500002410b0110800c00074044100c0c1d00c4546160751202d501000440b10399002c0ca801040c0e07210590b0b80070700002c0004550208018001c1484000d1004640c0d405051560000b420091030713900311802400c00508510400007565503540302c26820145010003034031503400d041c5e981d01e0b0550070b0040c64039000302c040482400b402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 274120719 1250 274119469 274119473
    0x30f0a200a0b131b06022806022d030402012709050901020c01020f13050306010311040504020f060d0c021921021606030b0103060e01080309012019050c0409 69
    0x1c6110440d480c0d00c10007503652a02c40f1007281030654068032005050400e4144010b42050780c0c0a02c03102181c426600310788101081748102911540c0024982844085080a500000300680c000c0c041700c040ca44802e07443c44070034400b41c0342c2c1740200e04c21144075903400005000c25543e01540700c05c8210458620401940350380c2800c4804081c0903c1002c1c10295140d01007040007100b90121101d01114500035034440c80c0801340b80115a00103507401c0b00c5151017100000e0f10b070401083c204d0483e6080000400a0000103041c8000340c00004c2c0126440826101c2201c000e9036900041d11307800d001d40400146c042c03100781c0d019107098844d0078040100e0f11180f4851001071804500104000103064100c0d00e411400b4000781d2a010250580c1550701019010100300c55074507a006007178101d001d9900f4408503588413142400801c1c00c0c004c5020310b4208002c40e042c00d5008071020303001e1000036002110710440424aa078209044d03105c0b0395001c084102446014080c5c1088a0500c00c2001c8904201c0344c2d403ea = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 274121969 1250 274120719 274120723
    0x504020415030b150f0a0608061305190f0f0903050706060504020c0d18050607051006090b06040302060c0705040e0709050c09010e0d080f03040803071b0b0c070c0305030f0a20 77
    0x9085000d0340d10011510a05511035880e40d174111000900032007005c40e11610098003440c1e044960074043c04c40a83c414190505502030710f8050950a440007400091840103c4040c20300c50004641c81c5843d80d4030740704607a203180704041c21a0301907620551602c00e180380004c01d851080e407219211703900501150700c80400100b00340d900a949401c0146006002441d09030b03041c1203c1c0e0009500c948086030840500a02042100e0800e49000b400c000746915410460b044901020206401003014003040c0018240080140110b03a6104100d8400c0c603a21700014003503440140f8900c0964018000400884619018441c0c2100a41e500c250612980c3ca000910f80d40225201a125082000c1240d082c00846000c6803a0304030b440b064203642e4a05410040481d61041e188000014101842c2001c1c0d0391030140300065a80e4406c0911001e62075240340c490f010382140100ba00d08082281001001800c01c00050503100103910303c0680f21400000090005040300030108170342010500c041c0020303000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 274123219 1250 274121969 274121971
    0xf060e0105010e030f2e090309090203040809090403050c010b04061d0c04031a18060405120f0409020c0a021503220f05010c03050f09010c021903030e0601090504020415030b 76
    0x10a107400003001000c44000380c030709003030001d175500c0078040c5040c3c582d40144140480451204005407180d107060652044101321828510060005079520105118801541d0000c40c0c006004440481c18200c02000240c996802520b0841c0858000580507165120030300414294482c100c40401103285810803040680c003c00010031022051000020603041e030075402d84014503001242c4d10708040c000b0380ba0015400302550200c0100900c50072000391400000f48180c86030350b003c000361240320041210000240c0010540c202c142d6003d000100d44040c43d4809130100d6070b50003008014a65840c010310054402a083c284104a001c00030000803c0121503c6030349034080049544d603120184c04c000762000c14010000b03080c1d5003021490050568140c000501461901c011404a500c40d480a9400c80740c03080314800140c3c016900030400c0302c2d108003d20312604d000e418040340300211141a90f042042c260044440c1d0740c2c2d68000d200550400303229010301145540124410715046848409683e90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 274124469 1250 274123219 274123229
    0x201081e0a0b01090b040303050403050c060405010c06051008030a020105150105070f0807021c12120e07060804020a0510080907050d1e021503070207080105060409021f05040803040e0405010f060e01 87
    0x20716442c020015921500c4030100a105506100d61580e4517490020b0459105210a60300f900c500498070f50300d03151000482d002c0303850584030746000300d40d280c3c1c0b20805040020950b520481c01100e002485000501c0180051805540005080d01d4182c0304000d000f90261a203d040200038071801e03000800e1400f501a94541144805485541900c00180301c0f4800c0300b0f4507070002c102c16445201b00304c6407040800403030304280c42d4003400c0c42c03109800500b11386003541800c105a010500400c00355001d00c03034040c3c0050000e002c1d81e070714036129004a01260912141c66002444420400106503070030b000e805e02030581180c03201412800b40d106e200400203420185008001c20188202c115500c4085001d64283c480c03d0050712441c0801c4040d444240500c035040c000e50806002454500c3c1501c00c240c0c1084c3e0003890002a14102c102e1304504034108401d86c418080204408161508100003400c000c01740044408464641481c2042c01d4440d03210610210358180003081c02006500c0e40316a054038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 274125719 1250 274124469 274124471
    0x9030a050c010f0c030c08070239030d08011a0f0a030c18081f0608060a050c0f040f0303090503060405120a0c1e0309080f0a0f110910030201081e0a 65
    0x1d10314241c000c0c0146400343d81c07079543c1ca14110114200b250180c100c030180d00000d1320754a0301540c8649007603850f05c0c6100c05014080e168102c0d48440e4503400800768040300c0389000d10f07243c802118008680f80c801d101c006180400c1d03290004110003004644000300041900c13078024200078614801e05804d0041184007814103032100c1e00046510b209006085d01003201a00000855075144415074650300c001d0302482281c0058101440d00071030a000342c0c4112164540106415a114010b2400404002c0e01c00c1d040e815041140b00c10050305503003d00050404c0124002445255140103003106402d980003038000d401172010040866008264100100607109880d592141101c408480d44912104000c01140c411030500460751049018410130b49e200e40c5075500c2e12501c541515541c1d14074080b00d8030f115408174500400040000700d001d0324161042103241804c200b46000110f00e1071040382d008842440d410707000c00c00c1d0342e4400036250300042400480381d420080d07541d061040c0e14000709050011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 274126969 1250 274125719 274125727
    0x30c0302150a0f12180605040c080a03050d05070c02090108030a0807080610030b030304050d0503040f050105040806070f050d050a0b0f0108072304031410111c2301090c080f09030a05 80
    0x84915044010801d400b4181e070380400707280341b500c2001032006450942d060951108041080180000c95a08040e01500d840c0c0c1801b0f01c4414040107410020501d204016010009500580317a41095034040d0403d00059a142d0944500003407050900078000020002500c0603c2655121010342d20360f807545614010502009450200e851840b890f404603030482d84d6090b0b84001e02c6030210144c010f0703a400015003001507503200300440b5a8044c3d070050b13903016001080854030140c0507500100e01450141000341c108074580c400c00007296000c4401d4640c80d40c46240a1f00700345031090050740081801d081014841c148124000c0100c2c01d003040603001c0c1740046011741d084031410340c261001503520012141c1500000324505440311241c0c15080401400c11f1047d90b00c240c1c160b410f030341001000040811680070440e84440140c0040c40c550840300d01c1040c1d440c5024802014881c0c0603040d14040030440000070007004082a1004000316054040402846a001d5001c0215005030303500d40707801c0746c40e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 274128219 1250 274126969 274126997
    0xe0f03010603021306090605191707050d110f041e0e0c03070906050909030c0316031112090a1403030403020103020f160b040605091906020a0513030c0302150a0f 71
    0x5241c5a00301940c0309401c18581000811150441d90583e0062082071141640d500140f020380300600300204801c3c59666003d000310180c1c030000f5480c2c030445100b01c1e040030703581d0b4001c10031088042805903a6540c06102c2824142000c2009039030451003610104041e4058074200f1b42c02203610000400401c0c0c17180c40e82500300f502002003d07841d2500405642d07080790b9034113101009203441e114050144844100203180484040309650305880a02c01962401c0300341d10211040c5031041004606101d14803070b04260a40c3c041105600704041000c2482e6643e01d40010020201580d901c40c00e0f2202000304407010030303100803084d00c2c21281d0a003005030300e85443d001840454081c00e070703451111050800b00902840520704025009500901e810802516000074040d140c00724030700001440a0143c00c1e8100080f003a0340180189045803030071604200c242412400712404503401a84c1401c20b04a00380700794a045400d40c1e9070000903444051428610307040c050007184400f0725103c14000c2c08d44060740b03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 274129469 1250 274128219 274128221
    0xf1205120a020115081e0610030b060d0b09010e0f070303020c060f070203030a0804030e0a030218190213080115050319020d08070f0605010501080702071a0d0606051207020a030e0f0301 81
    0x810113800c0d481c0848540c0c0c95084465451501d0501500582c4c5107030000c10b00404045405801140038200b024031041c207640768082a414007608164205290030064000b003a0441c1c0518000c8510078004502400717452842c034540140b0860001140e0864101000025000140342034981c8050722070031f4032420305080304c81e514002c00c3e2010307400d03000000d641100907238840d030603a04c1644a030700e5200c69504681c0c24025000b090b40030080d0000c917031802d02800310501030360660344000081076254030725940182800a0f038010b0340c41c0c0d0100084462092003d488207010f005129010075918a880e20300d00000290785144010100a01c20007810040b000e6480300c2008490898200000c2e41d40c4100030318180c2800186c11905881d154904030001c540b56208000b541c1c05900150300604406040010300f0b6056060311076000040001000309440c40155401040c00400298403081e07180d503031504043e40c1c641001000d150440d00841c4051000039004090390707480a0064134441d01020913000424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 274130719 1250 274129469 274129481
    0xf06220e0a0308041505010506090d020d02040f0915110a140c06190b090108030a05180d08040303020d110601140117101508130b061c06060f1205120a0201 68
    0x40d9019807541402496080728805000e14401d8103041c244200315850030040390020300a0a902c408200b01030b04091034200ca41650082c0014952801e0600c140d0000381100c045401c45611581c403a010f100601c01c103a444a004040008400d215a440051044901307215032907a60007805901c0380b2115083c5401c03000c2c0ca56a03100c0ea0211440c130700380251038445074072000310b080f58181e0403d109103c00c0c1c1082e01540d07040310f07a140010740c100000c8074401e4901d504114550803100d40c0710300c4056000e5980703004455200e8026140703581c1e51400c604009042c039a00640f40ca05100744e081c1c2c6003901002c005440741c1100c4a140030340088103200b40049841108a81685039034014600030b03c403210f80c5142041d011510550101c60000d0341004c0140d810000c1214412402e04e4001513950102e05031071042e65104000a1a40305404c8002c40d02030084000b0110a54580790b40300307014024203112840041c050305401d032480207400311a50f15a80d82c3e007902c04d0808221900030600e454a103000750010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 274131969 1250 274130719 274130741
    0x60307060c081c020d05161d150d0b01020114220c09020d0614030c0303030c031b0c0609070905190c0210020f070b100b1219050408070b0f0622 63
    0x3c480750b510140c94100a034002c001c08840080c039100110b40c021420000200051310745440e2820b01b030034510600d021454941003196000051100500701080000e80200b1000c001040e0008040441d14002030860b010b0720a0300091000c0c81e800c1c0115214040c0c1050310041c000d040c1c1002e20b40062402407410030041d440007040c41d0000c2154101c012068110109440b40e0742c8844003103004100070585c0e56010360b540385426802c1080032034640201d8030020355000d501d07507246c0784e1001c80703080364003132154040d8141100541100d4103020000ca0244106001405044010320080c1040d03280300700d4160302690a04040380c2d95107d49a26640207011503404a03000800464869804038800c44060780144000c0310f130310501e04001450611783c1440201075480301940182002c600c50707101c03100c040e0b000e408259420400851040031034007900440344500d1081018640f61090380c07510450402c00607101c1302d02c1d040418104441c070b80368289095458110180c102c0c1007440922511740c020103d00c60380c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 274133219 1250 274131969 274131997
    0x1c110102120315031615080a060b0403030f112a030c1507061508030702060d061802071208010b0a03090f0506040503130609060e040c260106030c020105060307060c08 73
    0x8200104058a007600031400707064055441c800a0100c2000e82082e1700c0c010003500201c56605006100e100e295025803100e900c1c000005c002d5181c0c2507030f6405401c0381d401103000400208490b0704440d8058840c441b10288440200b054299845603100c1d81550b0100703035000c5204100c00c03040c856808100400341d54a001e4a07034070f40c14000d20b0032a08603a000b65000d854203424030015580040080f6109011075107544007550801406a08020701644074008010030a0345488000c00d0610070065004020b01625800580d507844038989600c0b0074011119041c00c1c03203001d20042050580140171035032411240e10340012001e81c107150009090f0344582d006022440340d24100400c002c3d0000081c205800d00d22104041c90303540b80804c86504946000b4800010405481041c0c00d040a82041007200300314100b41008002d00050840150000c1b401814100c86907001000916003603c25940002001c0c0b000344070a02e40031000c0f81e920801881080104420907803034070f090260000c2515440301c40680 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 274134469 1250 274133219 274133221
    0x7020f1809070519050d0201110a080c030405120a030e04110f040b0307030e070311011404170c130606140304020a030b04050a060536030c0703031106061c1101021203 73
    0x603041e070b031010507000d542c3c0203114400d00398000003805842d5000b02e610041c00701c0b290007001d500456a800c88000034240f18810300d0f14400006202c0c40280110030f062500075611170f843c040030000d00b5180e40f004900150440c451940c0800d0f8019400c213000c5900361008903030704050880d501510310401101c91070915020401080e40a4400020b40c0151140d580a003c924030700320215807200c030b0903c4000c0034545c03411100c054075400b801c01c00103100c11048083c3c0c1050b680f4065135501080c00030000c01103410039200360b022490889006078540380501c40c208845810300402920202c00e24400c02100480403000070210b585101d02c83c00030315801807422210b401c10b0b152640d91000d10b004200d0b0142c2c10400062242080d00280352801040b90700584043c000203500c0400c13030584400000c0c0705000401030710a8071038040042600031803103030f6644682d582481d03030050305040010b041d60344038850390040860644291000c0503000b64005020a06440400300140e1824603d42a0f0410844002c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 274135719 1250 274134469 274134481
    0x2070605040c050a180906143d1208091c050105010b07120815120304141002030f0a05130905060306090d08011203050708070804060f050c0307020f18 66
    0x50489405a8460544503000c20f4886003040810351540c041e015100c45005032240c02c41e04543c0002d210180920400520300d0208200384541e14408c07101101c0d00d080980c00b031480441941c10080500301845e101c420030507500e4440320114003603403140364500080500350038148841d9030102c81e4091001010f00465140c040120205100482d03803d48095203403100020b003512000046031911607000a00403c0c4441c040c6003510140405481c0c1080342065001002c0243c603181019500054440c00442e115442e11241ca50119205c8130b801c1d01411000c5443e4081640000c152f80105180784c42c56501c614400e80115418080c842c07100521645400c0002800903d681c01a409000c1c260b007564a255a00d040b00c4d6034a42c1e850b001d09001545a4004000c021290180070826038441d01d003140c0f030840c40340c0301c0c0e4190350440c41080e11000400101004545d4001c0c1000a0102490800a080c055100740c00b503168000d840300640924100e20400e5001e98820080e03004034a001100201642001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 274136969 1250 274135719 274135721
    0x11115070c03180506030c07060f051924052205040606050a0e100b030603010f02030408031609081203100b0c0f01060b070c170115031119060503070e0102030d020706 73
    0x4054020901c0c080b9008883e409524400064540141045155441e4030a10030102c0d48a800242d80c07e560740c1c000b8200500b0715004290245810013810f41108882402503000c95510210180b41e01c501d5800d8400c0101070303100400e0484104803107245001502484455280c00400c1c510000c6624100c00c00080124651041043d5081030b60024041c0d62a402c0855042c9411781d050701e807180d4140020002c04160760000c0da84090040c0000c00e524503c095900c0c20384e0810b90302104d04260200400429019038151201c24000915260002620301030601d0349603001c0400b2003145040000001304e22043e91110351b4024591800c0701c0f5501c04810308210f45811040f07401c3c2d001035082080000301520280255104d10b500084a11412440d010842c060f17064610214496952610700404d02c030301d0b83d080d20100540c02001031f1510301e01c4107001c21981c80601383c1b030b030704030710005020910126500c401681d92005050600790702210099005030720354000c40c40500b1710729000095000c108513031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 274138219 1250 274136969 274136987
    0x1804120c0516090c031a040e07080a030302030919020d031209020a060f030e01050115050702030a0614040303060503030a0e010f0c1704051212071506090c0c030806180601111507 78
    0x4850f030030003040e08409070890581c5d8240c04c0c0084001807031a0590280d2600b0780c00341e28100301100c102e821055646000500f09600100f0a0b00441c2d800710820010100c1400a0104c00240400280c0d0700d0b1455400101340015100c4050100510400345070a80895071784101702e03285d0001c04050390785079549401000d11042c00c07c0c01001900b410364100890005010741410382d016015145080c0c40f2840046030950080d4005903450303c44c0d51a0500030600500c113004a940ea00010b01103d071401d82006010340e0504d41c8113902a501c200300101825911045c000c0e10701350b0900e0b25003401d41201e0380440721414a9080908200310844508514a1030354004104581d42990300c0420001946401d5883d4000c440040c40342d9042000700800143b886034540603100408080021190b4840c6006403c41e9144160303100030a241c1da540c0d0f0141500146101e91081003180c0c180940c02c255014040800c502400c201c4c14400303141d83e01c5002c0c00090044843c0c0150084480b02c031481c009074001c041d504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 274139469 1250 274138219 274138229
    0x603080a031a031c14070807020a0b090105040909081209010501061b1a090708011407030f0b0d02010e010c0615032108070804020a03050a030f0801051804120c0516 72
    0x201d070a1200d01e01181c104002c61031104014007400c820f40c0070209180c82681920b00c610204410006143c0000f106034024040e0140104800e94980119205000074003106400c0000c844074240140000d0b6a442000c84003078410303441010a00210030b292540c02c902a40304880d2507110300204000d009001540541d049840b15911854505800d108168004100d03440103030580d010079100603410005441c1050704079008000f240d48940c1d44140c1142100d8035448654100b102d6201400750643d4103020b00c01c003001d0031007404c000c80d01c040b80c0016804c1214003802814440e009001c40b41c1a801803000c0100603421000900c0380e581041050140f00c40755001c2203611a1000200c020054094283d40540c0b60a9480d45a02030700c64040555021500a00407030b403048001c50003000244080c40112280c51294880150702402890041c080c000d0580149000b1080b10750326141c09450101c000350403641180d441070381481000c00442e01034803400c0c0041d100d84607104504107102a034102040440f9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 274140719 1250 274139469 274139471
    0x612030309060f0c02060f130506071d0109060e0907051e0403020a12030207031403070213020a080108010e07141f08180c0117071107080a02030c04020702010503010611010f0603080a03 81
    0x3c5410242c001110710140d18003006030311200000710580c40074460150003803c440e1032045a040e050391050316058040f5000c800290343d020810b103541200014030b80f0100424200000003a042c01c10044c29100b1601c0264841c5107400c000c100484d0140d012500b00c00080d00400540b804043c044d20030551003480300302c1c054403800d21b0024900e41c04880c0e541916525902800d1003d2039519006148180c03900c04550ba07000030458000180d440c11030b41108920242400343c1c035490203c0020b0720080b01644030312280d9050110416002c8070208565060340c25541d031004105485d000403d481900c01e0030500400c05202481201080d0440d42091003000031003804407520380c544c503034140c413445892174035800300702c006400300281510440240c0e407290940c50b0482c252140840b041d4a0081c142e440a030254002040301810b600b0107005c00c2400ea40191015481c0400c1580002e00e60b1005110f0441040a440c100d83d6040b9001e40003e548205801c45c14402c0c1d548a0800312440c3d4400d0172820086 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 274141969 1250 274140719 274140731
    0x310030203070e0c071202010f05100312020a080a050a02160e040b10080606061b07090b19031a0606041203020c090906100312020c0301090b0106030e0304180f061203030906 76
    0x144100e2805907200e2002c04d00681c0c14507410380d17260000d03004000700c1c00042d0354171040480001040c501c42c0c4d5118240764400c040102c0e1550400c0c000e04580451f10b002190480214100450702440440300005082d01d4019135036141d2076002c90510820158448007a149024002040006000c07081d000e640106041078541c0c076070035084081c0440ca48075203017040e084880004c1e400e10b84600a03222641da605501c00f5515102c041150038404143c20440c0c2040d682d59619240342080000c4054402401480102c260304544030719604107015810780241c03c0751003002880c141c690800380d8004143c07038418055624420325010707458a942100b200d004029602c00201584400a4030900581b03811403e2003040d811038584102a16410340010b0540c840c156040001b80c80034456510114022462182c544d4180f403030040c2500c9001c081c0c2c4100d03900c1031005100c0814003903030300d098800c0080c0700001c00361840f0380c0314000b030700803a07104003940e04c203002031f0006054160f08640e400f1f620842c410010307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 274143219 1250 274141969 274141979
    0x609011115041704030312020d141003060513050618070302120d030b01030605010507020103110405030708030c0f0c03071e030b0c0c0c0105030c2a0f160603110f0d0e03031003020307 80
    0x14500940c071004e400284a141e6500b5a1141c41e030007802031a80c404400302e0ac2880b20018046522400c0e03a00c418503401c5c1c0d00082040c01117038405c42e50040350207041c00102c44526191b07030ba0340c0c0c1c02c09842c030080c520b403203292514019010002c000007554050400d4501c2c1e151004410b0301c409074800070074082420001c0250585d8030078481d042c10f581058485c2c50611005800442c004c00640740c040700340d20410000400c1c240d80030842c400040c070048009540c3c6041081d5141c1c2019801841080c0031ba000c0d42c11408541e4010407018255481503a41217896031400c3d880400340045c552010340a0410750040c0450400c220000f418102c0184003142c0445000c140111000c0c4400c4410301241c65050040c036006100240c01002400741d146454680645d007458401d040105490f4560029449001404254103541242c40e0040510b402d0400140002c0744c1051050300c01c0c1c80807501092000101140050603640c850340d0078020f104101c0340c90740340c10030303440340c2d8002980001e038801e1260780e4001070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 274144469 1250 274143219 274143263
    0x9054309080d050304080d0209150c0703150e03030402060d0f020d06060e0d2001030603020a09020306150a05030708180d05090325121a0703020909010e1302060901111504 75
    0x3005c0c0da8030403080d61810318047c901800079040034122076070144500ba403855008120001605800114401070510a440d41c40d20240360070b900e0980207529410f010b01005410004005e0742d074400c0e0143c1d1119900c0302d4402581c1c0c0100400c24080e50002d05c0442c0d02506180254445e6054844036200d002c02d2541007002c000184c891484024109c04258076401081725000d01945c1985806040108036180c5030f0380010003d007031581001001c96408010040585005003000400340004401c45260440e0001d0044c89844020311410030310042c81c0102c1d0003001c40510a0000001d100b00b0307034000903500c2d203008115500100c61584a84951483c4042e2061188040a4070114030502c82c11124a092400040c03029100b6056440304840b05540d800403405c11080c0d40f084544e030380d005a4071f0100c801049107038001030308020340c150080c00800c0016031040716210101601203c106d6100c0035903500480d4171440040075410380340102c0008900500300c20401304c3c02903109081d01c220102404581c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 274145719 1250 274144469 274144471
    0x608060913060b01021501030b060405130302060601080c12070806090c0a0e0f030102120a050103050d051c110c49030e0709110d0609054309080d0503 66
    0x102900300c2494401c0c0015806a004040700d10301070040d12a0441e4a156080e05030f40240e03c1658140305003810000c081c9403034451036503c600e402d1034100b425499510025607aa00060566050288410202e0b840951000a440c0903607440c10700d19500346444a00100f40000540329a40100d442c080800c031145224416918040090350b510b94a6040b6242001800802c0707110f00c0f501035608001c000c040c103000c20b1519101c1c0d0313075054000ca0b0a51440c581185046801e090402c01c1080134400c1d00c9022010207400780342403d038200d0128948850206030030701c6200c0d60030150b4140c4550b038072403000441c6414500f00e5030b1700c00003006500806403001d00110060b004150314561100c0014000f1228003e60190400f40800c504a48030305454504a408665949800440051011502c0c2014451a0180401602e13400d83c00748110308017044030000c40005030910b5800e100140300140040c07540306c0c0302c0301400070303082c00c0500070b0f02d0b040d200c06041c140c860300450700ba5000d40d203584202640100212 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 274146969 1250 274145719 274145731
    0xc240e130504080c15092b080718080c011d010e061804060311120c030318010e090c1903140a0e0a140708070602070b0d020a021002040f06080609 64
    0x1031014810380180e800014540100100c414410130301c002c80c1502d004010401c543c00001c1400030040c00e103441030a25246d4010f10715280361004122280032120303405403010805026042c940d0480d2101740d07042d20000102e000310091604c0320080010314201c00150480c040e6000e8130382c1c1411f442440382c80500b100c0c0100390140072440c2200303041d101d810b0240045c450304002448028203054030320005001d40c2c40c02e6205440d04003048440e400c9901d0010240044000c8080041c402401c010021035201e01070f01a098030b0701c403028551196540d0060442d51980c980040060750749151403000b0725915000074640c0c4a000241c0000040414024030a41b24609110280401c03580c0e0f81504000140c407041804a40c40e00032441418002400021620396103010701025002140c10404200c1c42d280b00d607030041d021580980c0d010015200940100d5481c0c0c10307001b03009070b9240000c80c0c05a00e003000301c8800303400043c80000d0001d81c2c4220000024241c692540d52150f0607118541000003050043d144 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 274148219 1250 274146969 274146979
    0x105010e04091703060d0507080606090906060901030201080a0207080d05010611070e01031b030b0405010b010e0a050d12050405030a1a01060302091804060e1b0301110412030509010c0c240e 83
    0x40c0003581240f00181d503020a000307280002c0042d1640c0c410b41860070ba6070240300701e50703c01001d02611b4600030501c582e009081400030101441d00500041c0d030500d061201905108151010500ba940c031174044916242d080101f5a5031170112008510080c4424890200001c03010605944000c4000c905c3c142225040400044ca59003140c440090301c40160003441c45161507888004005800c904007203100e1760084000099142140d070014148401801010703202e4000c2901c00d00c8950b40391200c00c070130950014420700000300160340c1568503100ba900000c0c1e0610039404001c04000000000c0780c03501703202803100e5501e039a85100507004c0e8040c0314031035035208290204158503e089070180640c014020300010a0030740030041010f040c6800107944841030007100c079043c0d8050401f40030b0100c07030b07100d21b0000500d440c0c54509159041640d074040181002000220301a10341c0c0b240c20941803ca812003800c489403680c41000001001040072000d0700c1e0400c1c5018400c01c1809007140002d9404043d103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 274149469 1250 274148219 274148243
    0x10312030203010e160519020c24070611090901030f05100209010c1203060906060c061104210615180e06011823100e0a020304080a080414010e060105010e0409 70
    0x1725080346800103944001004003d0020038598851415241c0040600d41c0103030822140000c14801c21140288512000341c2d490940501c01700c811004a91840390407080001c1d82506000c40c2c900729120306006154487c040d08004810300018011020039a807140f41110800a0210302e0345050340143d02c401c13408500d035041c2160101b0120001402114a0381c0790000f82c039600d42440504844140c1c01c80303070008210041030400c00c00544108124071031b10b415480d0420b4034040c0d02051090a08440ca061102449485401c00c40c554020200c1d08800c138843e280031549848da00180490b840c40d144c2e1304ca504040c6d041005040218000d8180c0768081c48500030110548402c00c09845600740c0800e00c401e0600781d44c60000070224009010b0a4512800c561191800d9401d040040010744003001ca90310400910000980d80c2c1e0440314414400d00384460b0541d11802e00e9262180b512150350303125400c141e910507101c3c00104529041e6070090301d804441c103038101300303200841d18200f10060006400207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 274150719 1250 274149469 274149481
    0x60a030b0402041b0206070207050402030402060f1c05011e06030c080a0c1407150608030301271d010606080c0f03041119060507030f0c050303040b0613090b010312030203010e 77
    0x40c0c80158028000342c0041140808001d0b00300c1455814005900180c1219003402041a0b0510006c001031100715015410360902e6000a4110300c18034484018006c400940c020344071070f01010aa00680411208000755030b580e038500030742d02c540344285140f4402c0c0041c02141b214081d1003605118603071940c0c0c91031142d0b00d480390b0500500245588005005885404550b07410b0294014040d0501c16103011800c0c2c0f540151041c1a5195500a801541c0003403005001d030405081e04041444801c0e482c804045d200b610041004006110b0703019087c6021800e11587c1300415044001116180e6858441981e559940c00509009a803a001c104000400c04036002c1211511000202e000c000c001c0c140306401a401d410512a850740a58003041c030124901e401d26403c542c00108244441c205200e2981140c0da071507890307200042000b03019100c1c0d840402c0c2d8540701c0c95410030940141003001c11401c0003500340117030000401d2001b114078815280c64103e4091007030083e60f049910716080e00110f52204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 274151969 1250 274150719 274150733
    0x210031505091e070504050a030311070e07050307030c120c030504052e0b030c0603011d250810030602360a05010807020c0d150c09060e040f0b0904110315060a03 71
    0x34101314104171050201240a981e0b242d90030000b1403090300d400540b150034950260a0800a503c1703103400e84010300c10003c3ea280c111080340e034040598a000110300f040c459041c4d885800b210385800400d40f90406502400e9010780c417042c016800390301209c80c2d0700c20f0003040008080d41015903460205035420800d28160280c0c001245150004003a103095180c800c010503190740091b0b2040c8d0140080c54150390f1a840e8a48495800641c03a54081416044a200224884800b000004100840c880026028501c8401c03050051a40448155a0b0741062904a180480d0845101d007041101d801d500f02814900100075400045c041c1a602e6141d181074015602c0700c0c0000c000009500032244010f909a44014155414510580c502d01c0c418401010000444440d4200755062010540741486103a070800c0306804021002c9402103901440d1100000c0941381e0008059080020201404200320105d010980080d0003602101d50b41981d651a805c000076043d503000d070300588a4071051011400e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 274153219 1250 274151969 274151971
    0x5061311152205060307030504120e030601030f141f0605063c0307020d030b091e07020c0619020c0108100b07021516020f01051309050a090210031505091e 68
    0x25041903030400b40e50703c022800540c011a00761001941c0d6404010401004144c4901e24a29a14010513010008400319903a0b010601026145030b05040b1203d08202c4103400c0d0f494081a0b1005558188014214407601040102d94030f07102d89007440300114003820140c084c1c41e0a40b0005000620600b464460f00505880230701000103010b80d13000a103244915840003c5004010b15401480a06103560004084600c0e0980c3d03507125480320400e02c030202d0a01c0d1491888051006004200380d191004140d25202c0d480305080c0e0001c20124261941d40a500003c05e02c890f9540c0a40d94445880742c01180c118800700c500d20210300c8a0001889140806d50180003d0340c809092a0204045605a1040340d0800b85207010041d1030b0400c11401c40c00e054801c4091b010080c05c020341005026841410842801e0095298859403140014180710450b00112412500508400982500e14400134007502d098070002003d03084080001925040c080351652145200d50306244a01c415001141c1d602d0344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 274154469 1250 274153219 274153267
    0x7062c040912050910030501081507030b030d0210050702030304020312030709210c090e0705011407081b0d020705010c06090609060f0c0e030706021207030c0506131115 74
    0x9610480d000008007004500100900d00783c54041e214140351080256021705004280200b5041200410600034002500707800b4031107880010404d90b544900480003488001021541741c8200d100b00c44a03181c021440242d000c90004080c810343d030365411700b41c1e5a8402918001d41552000760100c03407011500d070185400807035130316102f0744403680c4030185041d201c1d02070031054465003025101c1081040309004100204042e6105115038034000072140d032100301c28441d550502c10115010018010f0820450342c80a0740702000e15118111540c0050140521010780310b040e06c03c80800d988400c3c00040d500e030464005944031881564203a0301d0f00050000014122912602d60301c0b0700000450038090000c0e81c0c1c45100c40019070060b01000101070010000c0c04c42c0c000c1d0408103013440030380c0e40400d80c2c0c107064a03207074a4141d40d200503160444a054000601401d140580000d02851401904601c4070041c09840f00803602c06040007006a402500204c05459140821008075500204100408017007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 274155719 1250 274154469 274154471
    0xe0106020a030c14011a09130b010b0901020705030d03090203210307030209060c07032105040302131e15050f030f07090b0409060509240c0a0503040f050f0c0307062c04 74
    0x1041400e01c403402d4680602c2040c034241b548429882081c1020034043d80d2000703a00c00d008104059584400c601000103000d0078010110010304404243d00800c4030400a15018088409641ca0203800600910350319000f20702c280106800c001c1c80c4801042400b8000c88040b44041c03440d21005010380013580001c1107a5084042070004a06442e003d2282c100218012800030900f01e0324110a00d24a0102c8800c40d400e00c2000e000c1480541c40307140810302c01c00d001e240b00180d004046003400c400011501680c41650381032084000703448020a040c00c044a0307050307500c1510b04003c02c0816881d944001c949180075408a0030400c20cd0440b034000c00e9040402900c00244103c1c1d40d243d52098800032100251031b81d100e20b02c185c4581c104010000700f401552503880003e030a04011004003031090011074010810044045410b22070103103d12480300b58000111a5039090600640703843d912050803840c404d014145c000a1114059041c41c518203030b1510030409000c0710b01c00d5118006a250340381c0d603002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 274156969 1250 274155719 274155743
    0x60d06060e0f0103030206010f06020c04050403090b0d0b1e0d0f0c12050f0706050a09030312060e1302040c08090c060309070f2304090201090521031c060e0106020a030c 74
    0x201e01d4003160180ca044219180107604500f0003a140142c182e04c00091050340c3c0c0d00c100800c55010541440f603980844000c20551200d0500701c844812270307049403032072410000c1e82c0201e00d4441d500c121072480b02500c41e250f540d89403c024130180e204500c50960040180403078440083c0480300c88004c07041c0b094480d48411a1516840c0001c049009012103140c0c1c042d070042c0801540c1000391000030b04152074107502d03044203488028004403582c800101802060042500395030029000000075042c855800340d9245400e01000700e1244600c0020f80c041c0b441d06c111015203038412041d03144103234400402051040b9512081c001a50f0009100c1d102c5070042c9a0003061190100141800420ba0b840c429032403c002e22406056008a0501082c422407038a403402c00181d8115070241c080301c80c121813036019880a00c0a4031031050000800c0d1006002c00501505116448146280f4948585108000c6152140b0200300005428040d81025030300086503000000e114a0005e10054891201503000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 274158219 1250 274156969 274156979
    0x60109120609051906050105301908030106030507031a0d1b06020d0216080606040b04090f08130b030114090709090c0903060515150c0c0a09050f0c040b03060d0606 72
    0x4003019003541d01c444113480d00034001480814051240903010850701081d40c3c0c002c600100070f80182c105001a600c06032040403e02058090200c1030a60942003803551030751102d854003948650090054101103460407010869162180c03003541481e0419030345922103a8203800410040c078410702012121000c551310b20300030f00d0711520034840c01010150003c0c420f1180b01d0704042d0510080c14450842c3e40110740c01003104000020b00280c00c5041524001011395140c40030070054410042c015105191586611023040950001000175078201140d8071401511181e90900901c020710403495814584400c0014629001a02c41d0f04174040d403c080d8151903680a400091315500c3c84c600000c01c1400e0f6040040c484140a602d9000c0004151012248035a4001500007010703c0011540c582e03011400c0140003004004180c02402e00520010303141e130781c80c0070711005040100c504d008210182e101188101c40741005903026103d0006400d030465440030103006524004103001d440942d194100012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 274159469 1250 274158219 274158223
    0x160e220603080c010b060a0c0209041a1008010501080102070b010e071107080d030b0429010908070b07060b0105090a0909050102090907080412020d02030d15080d020a03120506010912060905 83
    0x15442681e8050f10748076907051460071103814a0b015400380c6010461140c000b0790102e84102c401c4c3d8100c0b40441d0540f120b081c100d0611000443c2086951a00800c0c022001e40c40301810040b10034101c002e20860703032103c0401e4203038020740b140144160403860050041144c0300000c03d0b8400424500000c228020304d6000f440e040050342b0110680e04000c03c0302c8002a4180240185c0306029030301401202c2c070b003103880303a00703200501c11404a00c0d102102401442e8452103110008004840c22201115258040c90340704e44c0c01700e030088410901d010414100b41d4080d009503039180308001c0481c9000e03864070700031001502d100304044805550821203e025540d644800794000d540980d83c0003850f00e01480c0980d607856007001c250b0309651211501d441000d50000807150001060700c0003007072010103002041290403440e0080805405208002c11b1125070014449100703a0095958040b00c001c103884000448400f92921130010710038032402d025240e180c00c00e1880f140c0c402c0071300080348021501d48038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 274160719 1250 274159469 274159481
    0x421120509030c16180b060403030e0d0501020a091805040b1902041e03031803240204030f080a02120306100c111305010f0603110a080601020708070605030f160e22 72
    0x211110301000010710199848100ba172081e0a8107503802c1102da80d80d0000544a8003031440000d0400100030b1007120745890760940c0300c44155200700259140c041006020b0045100c6015440d60300c003001d01c2440f003075041030241c10b0240e500524080d10076280c1500b01d4040041c1841d004030103036020000090140103090034202c0411404d110507038900e007140b40080403803403c0042c07101c080d004c0d40f50a001084c01440308602180c1c24a90800c2400020480354002e40038644c005031020074a51480e8041c040114000c3c030482031182d0a4500d40b28170b103c8102c10a000c1a41c0041d040035407400003441e614003640800300c81c01c1c0074080c0c6120f44003100000910001442104525098070344004010004100010348058960750806004c10541f00c0c520b0380760b6019050507a800c001c010742c04500369900038000e003809081d40109640310b0507140d040c0a4200d43c001d440071081e20821100040c01c80c0c81040903002c4441896580c11409820807007040703c04543c9041050313200c40329182c2c0480c940403e200318 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 274161969 1250 274160719 274160743
    0x809070e070f09080a02030615040603150e0c010c1709061b1606110a020d02041407020f1911040507030b040612170403080f0f040e0702060421120509030c 68
    0x71031201241100040002c0f466512084466100081c0c80300169000700740c40780e000d442101c05400e900e04500004000c3d0520f68000380900c0e003c1c1d550208100d01a41100b00c0e242d00038800c850007002544011211038284920261030840a402c868140c401d00c20b00034902354500416090400e441301000742804940700c031a500c8aa80220003003035480101d00e070020003d081504161402d010070350f031036507115515690001d110b03468110b80241150b450f036000e00c040e20401d0002145034034040302c004c0d58039107101145044d80e100d803c042c0701450f4001c1c00e805003070a0b400340b0381d4006240210144806400003801500a0540318014104039071180c0c400c2900500ca141001203000c420340c188901d0030b0114007018852003100700400c0c800300d003010044840c07240c11a249035079550580b8010007524010743d044521055501d5084c854019400107840340624003990100341c401060000c86600402e6490180012980200810001d43d0580e030240354004a20803d4030310b4a00c4096825003041c8006a035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 274163219 1250 274161969 274161977
    0x90c1205011202010807030501080316020a0915031b05010e130b030d050901080108070f0506070804180905061614071103071d10080705090a02090a14121501060809070e07 75
    0xb03940c0c1550f0b030281c83e56401c0b2426013403c02055040c12001c41d12486003000c0030f002034040c45054011500c0d010080740040032002d0341044040031210034044000002d100c1074946903622660340c140740800e1240c0000300c40050b1902d041c4245020b0130f219070300c0c45802e0004482d5607074100109150703d0511070408420300c076645003980c83c0034450003d00500d0068210310f019500003513060000701e13940c0005200780d0344102c401c6e41c0c660007245060905442690401d03010750b00c008a140b6203c8d90746400000d1814420703029541165143d03041000c102a40d050081c00007207603021241d6000440b84001c2203024040c44410b010010b503400400d1809030103900000945ca50810120b0601901145090b000700e10301110312003035454031200b60ba54a80c540140c1c0c1c42191690082440c400f0a0350480c1c01440004d40030507045d503a10702d2003c03201c180d00c00307072079000d030154007402400d00c2008201c01c080c00500b0940b6001c1a42040c10450f04000014241c02d810b1203550000b240c1d5000030304503070748940390030b0f91 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 274164469 1250 274163219 274163249
    0x9070911040509040201050306060705030f0307090909150f0204053d08070f030e0d03060f05041e1a1e01031a01050a1103090a0314060708040804090c120501 69
    0xa544011140300810303200025106000c280040d65400340d419400c02d030246851034680e11007000180840c819020020924403002034100a03a0707920401961042d1469210800706580d160310a0096420001c0001d003407000c2c24aa51004550320350004080c0aa9958014289900c0f4004520004901400c800100744452640070b0001d40c0983c81c002466000300045440000151000d084400041c00f26018454401040808244240c0c001d1003102500d5040b10040314201c10003800424040c00307050b0010301d0401002c1981d007844c0c00350481c001081c51030102004100c8900d00014091070054a024007141445403210340d0340c11600d00464062800c40d0f02c0881280ca001400300c0d00b5a41c420360079543e2802d02442c0980c2c010081d940481254101a1800000300e10b0442c203500c12000c80ca64001d408030404800c0c00307100c0b01c449258902040407524540c4510b601696030500440d001840810100028400212680c0040942003058280801407640000584095a40903003020741440780900c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 274165719 1250 274164469 274164479
    0x4031a1f121e0b07030222061817030708090303070503040b0c0d0f0c0212010912110f010203060d140c15030406180503180d0204020d150801150e1e0907 67
    0x10020810b030524042035207807038140d40d0b5541c0a145001080714040c982d0109044644401003e072411100d01c00d860032890340b5846a03000740c00b01d01c030210708518440b4070312800705250070740300d441000b0304619000a50511318581c1c0c2d00030940c0d001084880d0140014001000081ea0070000307403010b0f120520100c1d4503010044521403401942c041d41208201d0720194001802e5003240070b58400c1501511000100c0c1e144d2008103015200c02c103401801d0040844000c6000d991210003425583d035148195400090500e507100d00341e010582e00c940d4040045121200052450a03d04005000c80d8090340c01080314040050b000052010380310820020000400c01040b0461041c40c2c45125191145401090350b9240c00d5624052150720705820344850460030b14580c1d4000404200940c014419940c5032060b00d282e5000d004e00343c0ea10700c8818500c070400319840780180201d0608261402d6440f010525106140041c11800781c80e42c045010303418001c000d91440409101e200350350b200000d0680c0d81c905 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 274166969 1250 274165719 274165733
    0x30310030212031c09020627010201140417030405120c0102041406030f0a05090109050a1103061012030e0f1903020a050418021e1f0206060604031a1f12 67
    0x40403545800811013021100c2d2400c00a060400e070441d0b0000d403000481c40402d00d10310174100700f94100b0034044460000d0b2088214602c11844080e80280000411356040c5903c02d041603800070255900c2c0d0603620708450300d000145a1040c01001155580400c02c405070f0420b6000c584401d025940009040c02210b000d00c140b0b021903041550f8051540c80d00400c1104d01d880040d140b81245516000072540400c4250001034401c1e401100781c943d80da41500d00038001d4600107003058020b000340320001d00c0e0b011002240d00226011204c60f0000d254042c1d604079206c02d01c84445590009000300b40c030070aa01c1d0350115282c0020040a0b0040c464290700420698807050750040c2c2c400ca043c0041446100c1c510154928042d50543d490308450820a00d010340c1c201c0340604c0c2c0c64014500c1c101c030504014503151501c0c0d01000c0c071380a441d0a9100d8106005032441280005080c0800141c02d200401d841d011115a00c07407501411040b000075002c1107003101701059030290034007000404240c0140208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 274168219 1250 274166969 274166989
    0x50705011104142101060b0c0c06070203060711120720060a02030a0c150e03121609231203040f090b0d08070f05060103080a08072c120303100302 64
    0x4440102e09240c03500070800080b46004518074011624459a138030442c80142c2c080903400c0400c0024806c0310b0721440f034000f8940003246480c03070030310030200240350740c1c00d041040b501e81d035070060301402c000e0f900e5240c29502e488500c01c5030308032485020030300e6200000180150020605c01c144a04c2c1001c02c0b034041c00207410b801080b591141104120381e2804a400200719021078905051400b00c4070102d09100700421a13840ca510740c8142003c0b0554000080440141482c0308480c1d08848203456950350540c1c5900075662045c0810b1820000b4851401a1200c102c400384c40c10700d54201c01e64035400454080b5541c180e080780b003984080f60602000020300510400741010794010042008000700040068001c0000a884143c00144c8102070055000b05070780c11640041c2154035959691810000c55400103a4440004090202007181d43e440350044100c0d420109005080c040010709a843c0032a00003001190300800c108003a807080360b005d10240d8401e6000610565a607482d6006016000603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 274169469 1250 274168219 274168241
    0x831032607020327100203040315060303050904050c0d09060c1704021f02070812070c24050c0c0306040c050a0803030702190c0503010f1a1806060a0c0c030305070501 73
    0x14041005141c0740e001080e40c8001390340d180e0a200e04108901903101c0d0110326403d094002004a1900d51074940001c02401201c2c4145000010244051984021980c083c0401400524100b000303c2c40c0c0c0c03409403c1a50012401803851303140c450f403203c0034001c540440c102214400d0f00c542e140410682c04c11410242004400103010145c41c0983c006003841e01e007503800c02c0360701e041c0007003448074603100b0061400540040b00c11650342d0005c500c0c142515822030345085440415a00c0c0108402600c1203554040b0301c0080800808102ca60105490507005421008000c3c41600540030450390104041e900807401a040303079aa081c1404c0a000e4007041a0f042440a68410003d1080c0681e00285c0e28514020281a41001d640180f070a1004104075070b110301e515600300200c0800c020026889011074000240075030204910300d1041c0001301d1011003500e010b5036034500024180d41032500080c02201110b20788181c040c021075543e4502e910040e0020340010700080f6003401081401d10900e04048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 274170719 1250 274169469 274169537
    0x1215030c0307180c0e0603040b01140d0f02012304030c0f08061012080d0204080115081c121b02030403110a0e1906081905010f0c083103 60
    0x42c00e0040000c001c1646103c00903102e580d80c1103a25141c0d01c1440c00d0642c9500c018900f943d01d0600e030402c1d01e0b0142d800c3c000e17080c0c4a40340f00c4800c002d6140480c2070782100c0798004408802c1d41201d4005650034060b660481070500340c0300304599400030890006002661003040404041c6081a0101d01d050b003081d0051b526a9004c4001e01070381803100c1e510b00741100d81881361140c14200502e0100594000d000310800340034004140481c81c08010341027800a000100f8040e144281d44140141d61081781c0e0008424603020031800c0300455201d085000c003201ca69a20100d00b0109a02d603009010303100011090041c1c10128080c01084025008015110350480b03c10f41483e0424084004240c0080c102c10a6282c40c19001c000d100c055401c240c00810742841a07942c40040509100512502107030110780c40d518100301072480003800d01c2020215540d5548200c1c6555903035600300501300c2500c106800102d210f10b00303982d403104949150b240c02442691036280041e03404240e103005941c1981450f045d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 274171969 1250 274170719 274170733
    0x22110f22120206030703020706050a020904182102070305070b03061905031c0e030604061b1706041e1506032703030f0204030506040c15140901141215030c03 69
    0x7010491452a485540403142c80c2d03500d8842a5003600203214554006204a04100810041c01c20340d078050411450281d60900c40101800c040820340055407000900b15418100d0b558003645c041c1d03110b1042200c040c0102d07048a030301d949400d845c01072680d00c40103004800204108490920106480d2442220551504003034180720021345c4a081c0d071000e400f20f4425015000f03900c1d900c07400300905801d901805480340e500f060304212014020741a002850300313071402040d0a801c1d1241000d00c01c17244040c1241039079910752004100261003c0c040301c80c07107207520a4031081c0000d1103200d14929001040c0400c600740d45001070140644903020350b03505241d82d41c2040368858284881c4080b94003a407501c0d000903801c4603201040d0081c056a0800341c0300d03208050402003088042c200b0582a00c80f000b044200413038554030700b01c03141002c0701700ca6001401c083c8042c0c4910350044030711280e01440c9000702410204e107601202401041205d0142004218600d4a0449d040602c058500800154040c0c600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 274173219 1250 274171969 274171979
    0x180e01090e06010f050f010909140105010e0f0901030605090a020a0803030703230a0c05040b1206030f060108121c020a02010f0b06040b0f070602040e01151d22110f22 73
    0x704500d01c10075015040c1b071801c038046a8401d40c048005040290800c1105080603140c2005d0120300b402090b0229032070b54541151460310121507c0c080c0c500501d0042d040c1c0c00c5a9599028110240001e1128442c0004440c0180d0302c040c141d201a062510040d03880340707442070000341591046408a040f03140c0d003084c440700c00102000b01c41d03400500034101059000000e001250644102e43c030490742c00f8004501e20042c031603160708903400f603c1d00304d0488201042001c0c016031103480a200d403081540c013804031465081981c3c4e02a003c14244031212228443c100e1804405903030042280030f0050b55102c0008800c02c100e8800c0c941101030550f90203050a080100c8012184a03c0003030308604440490140b00b00103417a01101d000c0c002004801c00c2a5a44681501810060181c2c0c040070400300485c030115041d98100c1c0151652000303105074504489050711903041c0d010400c0140d805500c4804404192030788c54010018110110342d0b50703a503030009455040310b021520941c10b130035480e41d24007044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 274174469 1250 274173219 274173239
    0x20f0706050306090f0612030a020a03170c04170c06040906030b28020d06080a030513091a0d021908030318070e0412051606090b09030304120f180e01090e0601 70
    0x1034480110040000c4544070440021390201d1003130140d550074400042c9c41d5041030b40c0890900c1c0750520030f0701c5010340f20813802c6201441481c00c43d003400d59040c0601042108900c0c0740f521800303030440503040c1c924465150b40030424960040c0c11103040359482c7d85080080180c8107203401d900c401202e001000c2d0085080c139006108040c1041e8600d1260040348002ca00b603001d500030310081482900310303061406945400303001c64026140000b54100700c100000380070001c41c02444030003000f200001041c03c030301c00d0411240e908031801c141d0700806000c10020f00ac0d01c1210a14014084482c021921307840c010000600e10031346614200b0003034000820402c0745c1070449040c982c120b6800010040da0040c07100c0104c400d8021920104c1e1007000c0444004203210203030b40840c121600400010300565508060541c1c1c0b44020359005058005003011040010303c0303104244010041c4d0300d0601c00400380d08007500340741d021a400410740c0b0211840100101c103210301c18034000d0b009140141195602d03103000e40d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 274175719 1250 274174469 274174471
    0x20f130b07030f081008030409240e270102120603370602070c06120c03050402010206070c140f010b10090b0f07051608011e180f0602040510020f070605030609 70
    0x3006000540c030118103080340011903440a404404100d949030341d5a6110300700907000b42d81588d0001c00038003450580300d14ac01d01441040c0c51039440504110b8072030041c0740059490084460140c0c5101090120960200f8001000030b00c547c409030700403608000302010700f00710b02041050340020040068076050310b40710b0000d8800c58410030542d5a0b1203402d0411001900c41c0800c0145555048000481c0803a08071058803105c80308c0050030004042c0792130090742182c10950380030340036a004200042005204a103149842d610031a0702d060442c086914240c6407040c01c1075041c1d40740e51642025580742c20300342d2130101912118034104040703034602015210703d0300c00e100c140491942c001130301d9018000c040009802e403441e40c03030301030745020f944070301040c028140d45004840110100e60074040c0c2183d24000ca4003000a80a40f110710700e034a607520001103c0100a0885420303400f1301c0001416035603404000d00e140e101c0c0d0040c0c01360306040d00c0840e0400c4a240c2021003403100600501010b41c4580080c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 274176969 1250 274175719 274175747
    0xf03030e161202210a03090608010518010b070c15020d0e03060c0301211205040302100f080105040e0a0501090f020901170309120a1403180f030c0409080409020f130b0703 75
    0x1442852080342c4441500480241c861082c5c0c4202c588110816a04c0626482200d03125a00c9001e2030741c0791010040f600040303004000c001d4803000700511840c0910401030411902ca00b800903902a1b6614030a2140036030b20072503201613008031071103092b019081040c15072104000c038040c010034640b00b20800d92502060080108640c818441411040040190380b03c220f44c0041e0801c0c900528910000c05950142c00202d0044a28481400c0710901411560320141116111181642c0c285801c0c0001007900c4d071454561071265030500360210b0028800d044442b4012804801104214011720a0b58241a0302170390f000e110b41c00c3c0d00c20040030301000b03545520604494a56492500314452441c1100b6080050400b1000d99003007400c500000008090501010048401c80303010141002040000500c190350590850110ba4000e443e02d03620445850303206184032414562a400048102e0308011205020301000007503c01c160702c032800803000100040ca18542c0340c40c20315a4000d144d14052454 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 274178219 1250 274176969 274176979
    0x90e0f10050726180303090703030f090f0b0703030b0102030c07091104150206060406060c080708130e0c04050102010b060313020f061608070209090c10110a0f03030e161202 76
    0x10614291198008003000f00383c01c00d0401e074101d51076880c0540040c0681d00e240314544014001800c0079004030583c0d10402c44c440c040d090702d03491a01c00361140d44107407a0728010000114400302c1c12101030000c58020740b1030f071100c094441c4882e15028040700d82c00b4000a06540c41170244000d0b00100299903030a54040c0d01010030216280e840c2a8041d01454200740050404a42c003074200c40d84c009402441076404139000d0041960303440e81641c3d210580e40c4050280da20400144000c112114018044240c41852070740c005559041003504441059400fa0b42c103200000e0204129a8240151900340e41e0444e0200d146007810340b040f0703490b00c100d410024050040480c0c0c01c0001d07a1807000b80e03810001c05c1c2407003460306851071400040035846954220706c28044a800b064074800c3c0010f10300e11204010f807490003103008070101901c0071990030681c050244901d1045034001185864080441c41c402c0d01c02145901905414074241071240c030103508503452580d41000184418080c0c0c8010b1a01990 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 274179469 1250 274178219 274178221
    0x92a0f0412050303060114030601090b13032901090605010804060b0d0b0c0c010f0b010806090a09021c030f08041101050702061201030c170102070b07260a06090e0f1005 74
    0x6518060080740e0041e809080a01d440d402441004402903208035000d0f030355480e1821841003020218001514a54000b40c40d5000912400007032000601c014a0010000e0404640c2c0b41d0320607441e581d0030101340d45151110444442840202c1002c0343c0582010002031002e9418480001c01800b07008001030000340e03e800203c2640d882c0e42078249242c541211001d80e1500e020714040403240d100c2c00e040704056190500743c20384100700b4400ca500c21034050b550f102c0356460740000c001030010041d252200c03065641a1510040e035684022000e907144140c83d9810399030660402505c2880d0118401003070203070110410001540080c01500c4903102401d04540700c40e0300e4008152107000c5c2c0400c4c02550f510030302c004030601c6a005445002c60354041181401c101002d5065401d03801030341130040c44034407000003003141c0030b0181c01d042034115640100c0d161803100003403c00210b100107a03589801c3d20303910314050000e07007614090070043d6444a07004120005d5407003082980c0c2c8552a040724103040e0380d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 274180719 1250 274179469 274179487
    0x80f0a0f030804061506080106021b0d0305031008030d1e05040317070210060b07330f020f0d0609060501020d02061605040f06030606080a0608030a0f021218092a 71
    0xd840002c0807a00e2480004205d03031a0400130348110005c0c00307810050304c1025600513003507005145040903203d0280c00d0b2000c2102a075420380b06a00050110340c404001103901040c820010406448036800342d04c00812010300c41c5043c14040350a540015150a080508000119800401c4a030070510010102036240d41c80010072410080d000c0008070703201c1d00f040d4001420326802e2000d0060380c0d00500342d0b240001c4030482c041e014000310448079030009144440200090300d06900c448100c1304804000b505d40300241411540c59800301056280c0e80e55101418070101c0032500c1a03501901382030004004560107150080d644d11340042c05101070000c40302d0035000440c418801d4500a1580321418500aa00c1d06000b50180c4442e000703580000301e411000900c0d000040c01141e0444624801440c40d18580c510700b00e481410440700c003415407103003c80034501048004004c2011885044603040c0000b06c04081004142001d46044003202082504021010a841210700c4220b00d0b250f0789039841e80d0f14 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 274181969 1250 274180719 274180721
    0x61d070f090f1d0711071a040302040f020c010501051509042304120f030507050f03040609080d0906060503010e0c011809090309050108070f090513020d02070c080f0a0f03080406 78
    0x20b03420200109410007000a500c9050020311034009501001207a9265600f4104484503041440401640c6e80714000401c0304c7c0041e0170441c9501c1e00c1a01c0c80516044d01d0742c020406403441c048050352642d0b8001255140d1a10a1282602510382240c2c5446070702418130110b82c2c50b018254915104541d11038805000b00480750100000138248225080140740504102410261190301c4c4400704540c000f900c82c0951180c0b080c2c0b441540d07952580790502815070554485500024001ca4241e9600c280b40740c0400e01c0840070305010102c0c2c80700881c2600603858401d00307449450740040d010381e060485415401c3d00109806881400c20f2034848a007100c0c1500c64500d414999010f6076105161035410400e155002150348143c0307000ba21001e800d5141c4401c00c81d40342140070311480008280c844103100724504030319205c07070554a0b26009818043c0c40c0001208a91110f241110507072038000c001c110740103052004107110602603002c3e01e03c00c03210fa1112007001e03400060003010481d0040005080001d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 274183219 1250 274181969 274181987
    0x50d0f0207050604141506180702030d2a14030c1312081306050a0c0615050310090203070b0301271103090d020c04020c100b03030c060c04030303061d070f 68
    0x40b400f11000c2d0304060801d0f084881c3d07000c2c164041401000f030728400c48003c4a0031030b40101d030054060b807401c0304c1d40560808020303000b030a0201140410061410346e060f2601801018030f4040c08000400d44c05002000d03844403e60101710240b000004d540031056035000300ba0395000b04120b081e281e4a42c542080003100207050703005905162100301040003030240c484040c0034200c0109031140c030080e84501050354035005402003180007452009030440000c0303c0c2d800001f21008241c4003891046c0d211400a4145200181144025503807040140c0540c5404c12804000700034603ca01850755040110b00c0c0808001c900c0b100d080400790350030400c080300d5150301c42c8143c15507a00285441b41484000c058650103a1a1070074014071803041d00305010b00c2c1a2080380c24440d081d100a04140c0309120400c0040c050102000e0303818041404442c0c100d05050180600c544a8004c0c000e581c0ca040d803402404443c40307500000704046170302092609103420b03801d14680010351400d08502e484044401101e5a1036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 274184469 1250 274183219 274183223
    0x180602120904060e041a010f03020306040311010e1510120206070605090a0204020d0203070f030c0c0605100e0721090c060c17040603020703110d020604021201020c030412021003050601050d0f0207 86
    0x3804c4000c000600900d0045007080720241c1c0c00c58080c59a0354140c1c6485032140c0d00007c0d6044e0021000700d0f0000c0c0c068040800d000080700c0020450180b0540c4caa81032411030f00780c40c00c0300305200701080000c11124040101900502c0c0711014080303110380200f1a14041c1210003000c20742d8070004260a03050170000c200e079880e4014010741d40e072a0410403030000b80d081540c140c0003168800702d21721103481c0070f80038881d01d03442e041e43c2e1000603030441d848543c00b038103025004403560009000045588011503220504c500350903150451414007550b145a221001e107600e07152054940700881c4002000c100084085030385600c1c0c0440441040c1c2441411050980d0010b061070a001034009159909500901900c0340244c4403881d403600004503a80c0c592580d036201c0e40041e0442c0e00010018580700c210040b214144600041c00c110350703030b90114910360080d04166107181403580c4400861070642c2c6110f00c5411186000c0c0010b05007135001901602800c0103880d1501d4640421402c032981079810b80315611303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 274185719 1250 274184469 274184489
    0x20c0603010b0910080105090a090303060306050f040525140f0409030207090b06030103080d05070c0501060332070b0a0c0f0b0a0e06070e09040201050c0a0309050118060212090406 79
    0x2581d508407010b1030358040900140214900d111044003280601d080e24101d4601421103003440c0e403100d4944000f0609010700f1020300d540c8010200c046034551040038410f120414000c991030505062603440d1a00b61007101c210304070803002c00c445c02d41c21011309200701d03401d8801d15820320042d080040d84082400940c030780c2080c6003490040034940c2c0000d00604854200904211011600041c40304a22007404080e2140e03400704061141c405c00c41d48180d81c046c0a40c03a080384007001582d516400d60f0304903841694007000001d40c00c060001104050300c0100c44098035400b450308110600340e2140c01c20301c00c0325070307050001ca0321002160103154000035681c0c6c07226446842144916007801156400d8a4102d01246003e0245400050010f4034078003443c0a910f51307541c00c2501c50b01300520641c009000300d0400c00140024188100c0401c184591103220b5143c46000909107800140801c0c982c103601d03040c040c0e000204001d2031741c01213442d82c3d881207840d007842d1340d41446074082000340400d940714140c55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 274186969 1250 274185719 274185721
    0x6091507060501031b030203030f03060103021201080c0a06031b08090f03040617010f03020a33020a1407060c0228081608030a0909050901090507120303050a0501080319020c0603 78
    0x50a80c80641a0b91091000505c2010ba51440301740d60401070000030f405500c10401d00030710b17060090245900c40e00500d0098078000d0040c64403181040c0a0744107006aa100d9031103e030281c5000000c80016005a280800c00100b0080069550320201d52145051000600105880361000d004002c100d4010b01c04507039459556000040c400b41d989500003401380100341c0042155001d46480d241100c0c7c00610105159040440e00d140a0580c504114203140004200175540701801020410f02c42e5140c0180c80030448504107190381c60a188404220758210340000d014003074224000c0c912803901a55101d500d00c000da1000714001d4441000e001c0b44c2c008000b80000d2007000007a840b403140700c3c1113080c00d00c000d0741c0c2e02d0b51540e00c0c098603000c440814281c5070300340300c0f914050340314a41c042483c40c0082250075207903c41c02d042c0122074101c110203036032540c034040925400d401043d410903001401001290724042c01542c81e8001c244820101400c032214081e6464801c01140a502100801c66641c1b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 274188219 1250 274186969 274186973
    0x4030809150a050c01050609040c0e07111203070314010305100c0302070c031b1e0b090d060606020c04060e04050a03110f0105010e0a050a050601021b13090f1e0f0206091507 76
    0xf0f540008440800c1c944c2444002821801c0500c01d05005643c045001c404050600c41440803590780200600c0400c4012030014000c21000c000d10600e0080851010303a0300e090040004042e1030786d00c01c40400030702c0303440e00420000d6800503441042c1d0601c0d01000030340814400c030813400b81c41001400b8140b106d032610003005002e1003802c0e0914444689021800650369101c0040e56041300c01480681d40c03a5040041180002040041100f120020000803560100f80c0e101c1c011680b0070f421000043e8800402d10002e030a151180801408c290160340d040da00d000ea545541d680800e00006040082c9000c8441c4052800c0001d5038007000c0c020000c1c4440c0da1560080c4025090880d00c0c5040181008081204039007548141d500407074043e400340c12400b0080300001c4100340d0030a42107812012949541820845501c01e081d01d40d445003210105c00c0c60070b802c0030007404051001d101c080c01401d400000001d80d502e101c85201030740c1a00e6840d201c0c20200700007182c5034290f0406800e9101c00182c4001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 274189469 1250 274188219 274188227
    0x9031b05030c09160e0d080706050f071103041e0e0f09100e1c02122a070e042a03060207030f0806222403030318030504030809150a 58
    0x106544095048441444140c0104041c800003581c1451850801c01300841c4460301c504030b055110f00020303200500c00c140540d9403101c0f50b444060140c0307850390780f2414480f00302914244c2542003183c614000a0a8101d1500702c3d88900c0340f072146c11040000303540c211000308400090480106124041071105150404080c001c003142224282441d001304c0106000300d482510420b080100400b00270203240c500c201050b440d030f184c0040f10100307600c180385040d00340001a6000f000303141201c0c101030b06421801580304203207414040d1803c94a03004100144440c561006003e9032050300300e415030f40803440011420300980e02c40c4c54040c009000c0c0302004014000e4503002029040d03c03070f98070f1503103c088082048509a0007034030225440340a2050001d034001e0846001503918503052000038001e9004444a900c40300c400c0c9a10741c5c01c003c506400c2003890b8140c80740b280703c1c512450050460540507030b1b0061240c845c1e400300038011100410140b109031550712a6135030044c0d605609555511410354040c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 274190719 1250 274189469 274189523
    0x9060a05181815010c080403030f0c060501060207030302160b0f030c040b0d0605090a06030302030405040f1404052a010804021e090403030203060f030c030c06090d320d140a0903 78
    0x10f0108641c1001403e500c540301d401e0407142c10542080c10142107540456000c581003040d04100211208500082942885418006e21450300148044c40ca10300c1c0c06030030603107212001c0c200da501c980e00030810788807004201ca006100d551401d50782c0755110040351030780e4080c98024110503440454500000001948240144e4400b183c803003e85a80d0580030200b500c0141c000240182c0091104000c641085e0b0400814240702a4000c00c2d40800c560480c07015840403107040c2d07025400007403214282010003046642c1404002e42181242d84404000303408c3c8000a04000c0c007408146205d0406a000c1d494183c01d501d500030141c00c064109410f00070003940042d03803014440d80c1c500c128603070140350010705022503100240c081c0c003500e0b001c8001c21030240c000d051082e80010090304402c00042c603612240c001d81d01c8180d050312003e00c00c1419241070044508030b08840c1d40c0318402801403160002804940c80301440c0480341d4507001f20a04465002441d84028402d50b410300c541001034107402c2d406 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 274191969 1250 274190719 274190731
    0x903080414011b0507090f0b0d060207060506030307120e060408060901060614040f0524030f0a0b10120504060b030109050f121c020c030405121b010509060a051818 72
    0x3040d00041c003c0c0e44000f020b49800038416031048030104003914154106041c0100811070000381038a0304008201400c8800e10110740d29a400940382e03041003000c1c4a01038002c1001d4000310300705440c0d65039215200705819100310500c1498003e840590781e40004640103401c040c4192170709410f0003c1d4641c081c241074066200440c400c08840d145c0d00980e01c00351001c43e203aa031058225503142c50113102824070340b210140e4000601213002d032111b10034440214043c0e40c448508490314a00b0381102c1c012242000c01141c490034035105400c806580c84280d44400314440c41c40081c0580322441c00130300070100c031080c075501542014400e6091281c08210401c2d1411084159803004d5103605c009061481082c00e1260307003c02500d90078059910a90141c8041842c00f4112480c140c0c5610000c0d06ca2400710011444c82c1d803000f801d48040040800b266a00a1020f0070304600301854000010070602500c05c1900c100100450707600340260072981d081d40100005402003c48109101442e01082012205 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 274193219 1250 274191969 274191977
    0x7120f080d090c08030a050d0509010b0612010611010507080606090a17030a2019050f120c0f01060b0a1101060e0901090515060a0e0a090c14040b01020625090308041401 74
    0x300090203135000c0100c51142002e562200d248c00440c07010040180400380880703100359a40d5101e0070280d103c0400400e007101c44003c0013500381d0300d0604020824001444813000304d9050000703110b01c0c90307080900b880c2c00850455480340c5030300c0c4040106107145050340c041240c0100c40e9180b005007540c08070082840000360ba440c00e040c000480355a84000c51406018449544210440c110095141c01808401303881101520b0a1914030401d07075140a021541242624100080d50904108200718003000c2c0f58546000384600f61078811608064003858440708240312600440030001c038429400f000140603410701c54443c50800502d490700034001148120358038400d1080400d00b11000071351003442604028413003240103003404180740b1400b602404012400b5210201840060b000c09031440c00f800003c03d540704400e6640040100b80d0b01c07480c4110f4107640284042c020340f20b140407900360f0b10f11602c00c910708650030000c41c1101d804000f80d00280031140042004200c40c2d40f0190300c0000c81500340d90f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 274194469 1250 274193219 274193243
    0x306040c05101106041103030d020c160501030902090403031d0109050d0e09040b06010f1e110106050411070b0702120a050a200a12030b0621070305010807120f080d09 73
    0xb005035803011440d89201c0443e032142000030002850b0b50f9091400c3e21010307007034a041c10032128204042c0c4c1c01c8002d148059030420b03a00710300c904410307107940d84c0240340918040c0079540058020900c40c41c000b070400780816481d0f4800c030400b21100c1b01321851b0414071748002c00183c01a41051501d550381085c1c0500090702c41610800d20f40742200310907000d07a40010b940171403511140015504c04061940349010701c8401962900e4141c50100540d505860b55241c0d001000c01840c03585003111481c2e0070040c440e510b0a60000010074107401541c5055a100034000d5890b100c0341d009034584134044801040000c4006076400120307034003801801400b5903e03140c150a0f0640c0c1d080e041c03040103070403110301c031160f2042030b4107000300d15201101c0d4000d2540b402d00040700801c000c04918640e1141c031049880c1c0500e00009801c00480510159008082c2c1c501000654101520070381c5a0700d840c8034500400f00350118407028020302c101c0341e2003103507071015030a030f540e40c407075260172010380300480d41a181400708035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 274195719 1250 274194469 274194499
    0x714010209060d0b0117090d0206010905101206110307091401020a08070f11090a0c08010f1203120209130915091e1103070902130b1e0306010c020306040c05 69
    0x1009681810740020140d0b400d0015104298005081c16134105040001081c2c199514143d040c1000340103145c014090801008143d2010f8a0a00180d00ca903140c10302d020100880b03021894510b03c1074a40d000d440d5100805035043ca980507022a14803c580d10000005008803a03401c45030981c100c40c1600d041c4104200d054005a882c0e84104e0720140084000700107031400144900d0149d8403c62103459101941001503011034841c4004680c8040b80c1940c89203080d4a42c0d400c1000c440c01030141d100e0700c041c00703401e0459050048072505402000e01c000940b440000300c00e1074041d0703503590340d01800051010000302c03012005441c0b030074400d907058001400c081036021041e008503020242c00c107a10100c55403c00b0300c1c0309040110303041f0941c5e8028032104002400c4d40c0511140009003a03103d00540c9945e02c000c2034414103101c55214a9402c88100321320011001102c050249400c0e4101c0c41a850b41c0d15a001610a4011608025454050303e8108401c00103070b0010303041510800d0f509024202001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 274196969 1250 274195719 274195721
    0x803070c02060d02030f2a1308100b190608040206030c0c010609150509040206160c2304060605211003080c03090a0b04080604030302090d1e0b0c090901050405091207120e0a0e06010c0201020c0a0b071401 89
    0x14dc007407040011106000103000d41061402142c22402c2600c0e00351415458040140c2101c903c1e1304a9065a606c0e80d188004070030f0b803039a501303010b054200c070381e040c0c1820a03070f00080a52203140c004105c1a0044c030000300034880c5440d035000040030070780114840e001d10b0300e070180c01c0070228800882c8643c1c034095020881d60f2041054070103610840d14500c01d000f501020321402c3c03000c010700780031100c0003045c004800034a111001c0c1850780c0c2d0348001503481c0d00c0501c04000d240c010300c1d00303c46a00c0301c00b0b2100700716041c8006007181e041609070a006903506100804a044940c0610002e4040310f44140c20078840008403092034501030240c40455425118000c40e08102d202b8143c1c0303035601c24900350060100b80b6080d0f000a8200201d8400c854014100d6810f036051600642d20070f503000840c44860548407038009089a01e1140112000b1025070300300301c5000300c0040f010f04040c0c108050310310080c0071a4000c03c240c00c0181e00c0140050b04299880c40e5032902c540c40103100301d95412603000156170081d01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 274198219 1250 274196969 274197019
    0x301050115020c0d1103070e0a0b060304120503090109020a0b0a080c0c0a03030b030102040f0f03030905010804120c0f0803011e09090b01030803070c02060d02030f2a1308100b 77
    0x3039806040080009030070000002d0913502c0aa4003005010302c540801d50b4204091801060803a14901c4913142c003c092400712101295200e01a000c20401c200002d010200803040b044500d0800726105c0c2c07918054035004100c40100203402c00840700c40802c1c0503195002030a00780c00f03075544c5d80c0103580e600340306003505000303540f9603132650790140c0030140009029420004403024040c00050030030390350f0451a00e180d203403540608500e904203c403d00c01d05d50700c8240500502020700b014199420b06584010030f070f18060b81d1560400c1126001e210801550720110303102c0d25040031700c1c283c80c0e5850f40c450350481c10403198413a100d100c0c8900d000030184e0190182c80e4402d0340084286842e40e00c0d64440e01019800202800100504031040e080181d40e524060002c440341040016241c1c40c0c50364030349030982d5000c0c00341c1402200c82000702e004942000902ea14002d2230020350383d1540c3c810251703190109026000840c25010b0300c0800c0c0ca03c90815400105a181c0c101c415480c1072a000515102c9011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 274199469 1250 274198219 274198259
    0x51302060405010f1e030c0807080c030408070311060f0a060e04170a091a0403020f0402090a0902092121070b0601050a0c0b040b010e160c060908041205030903010501 73
    0x2600744010001036001e034040c0c8142026a0625038035495031811111107420300f034815000440e56801e80d800125034442882c0d45c0c45501c81c10b2007245030030715034620701c0342d404014801003005074000b40740010948a40f842c2625080c1300340841e5040c1c200001c00158010381183e00c041114580309000841c0e286510506005039041015000201d40740f950841c46507200302103070000d2201194000401900706844884c000c0035840015484608610420500300b1581c0b00e0711b803007140180090b606940e80c1d40708050882e12240c400580d0780d410940818040d4000381c2c07081c0c540c2d030010300d03200c0e14090303020a01c1c10201e80c444c010441400b4410801c0529401400e10207804d440708140054030301d5000c0e0005110700c002a04081603508040e13039a43e01c0c01d180c229021210002d640300108210f1840fa0000c0e60003080d0103103880100c1c28040300082c02c140000704090001d980b907074000c0c014404102c04131000b808208036060602c05090420035034170747c0103d698602079840e10000103030303681c101500211405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 274200719 1250 274199469 274199479
    0x20d021216020c091f030f12020c100e101b0b04050106050103051e071b08190f050d240f0612061202060a030f061e0b03040203060f0405120a12051302 66
    0x246410340170360450b00304051102c600462070207010012803542414100814400c60741078011400b4400c00a0a040921030001d0040c4010750300075046039000002202545c4080e5074144140010701d0b000c882c00c008140c00c001a841c1144d41d14018000c640c02c000b417149000350000c3c040650740303200440c12203800712903c4110540c05100080446400542d064005045140000001101c0300103454001d1003000202e849050000305503242007908075009441c05807504000b503074000300e0100a005481440703e0014116500c20a622448051813030301c04050145140f0380f29110b03107c00d4a10341d000d16500502e030128161482d032000c000a6400b68000380e03510124415409000c40c1d00740011908540903440a240c1caaa100c2505051944100001090313070101e5010210060390041e05c106110303030404e108080b8100200009618009100c5d608000d4180b689121642c2d00d0500d60700f0804031907074000048100107100c4000b9540320203181111120700034100100e841d081441b950003513400310025081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 274201969 1250 274200719 274200721
    0x1050a0b040e090c03122203080f090d140c032a060304082106010f0311040b09012106030c05040b0f010e01030207021207031217010302040b04020d021216020c09 71
    0x101c03904061980d040350003001200d40001c1c13050002414402c02d0141c1c541c1d80c00000ca40307450308408500c0b031712410200c224040048a4115280c08551744524070309420321010028001010343ca90901d1220150b070001c0b40b00d03500040006110b5200e05004c0d03d480d100c1d21030444c4460313909806440780d0120003111440f009448004000780592904010000e4034a41d03801d20200e218141c100e20b601c0c0d200c10000d14691898a03203180050414050040c841007014031b040101110152000120b600350740304802100e446002520040300c680500d040c0084c41851000103000f00e55146403c2801a00d110340f040189050703e4009220854150384810350740011146c0110b100d5501800041120b16010b26001d4600101350300814101111903111141d01d074064041003040c490300d9100c0c88108802841c003490800194542810f80300818000644199510500c004040c0c0e11903045840d000b090840075511003441080c054064082181e05418103080105510040741c404100c1c600b000d48024500a00c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 274203219 1250 274201969 274201979
    0x3060c04090c050409020712030e0307020f190308070c240203160602160521070b010e07021515100e010c0f0203010f0203010305030703030b01020c010e1e04020f0d0501050a0b04 78
    0x40d0070b0700c41018050100402012444003030034001030190030701454115040e1606000010f08440e0441c031984400e0300140072190050303484000b4010200c030304940c000e59aa080224144006c600c65200904c020000a002e0080048080c103850864240c0e401c02c0174560140d1808040d9400040b1000f001a04108841c160700d682103450300d1a501d00070300b001401e010080d0320305141048094010340366a0b10070341052440303201c410118003d603c4960392181c101a82d960b40d40819503018041d10034500c040b09d001500d428820044210714000190b80841d5600b4280c1002c003030790a840000c1030080521441d0184210b0203683c50109014042e900d415100e101d0352580d20000860450480e495520750003051035051244c0043c43c003a6024602959071030303c081c607020341107a81c8a011541950480c42c1d0000150ba00403042c400d4954003074802c48100b40f8050071030520b04410001e0194401d02c0480c09104440c191400340000b820302da402049541d0700c5008015001085200300144008200001e00c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 274204469 1250 274203219 274203221
    0x3010e0103030518100302042c0f0702010905071d06010906050405130227180403091502101407110106050303031506040801060306020d060e061e12060f090c03060c0409 74
    0xc0d80e582c2400750f1040481080c1c0010f180040c11704072600010f900800c0c244803001400d120094159251410025514429845202d1122000b4031182c2082448400100d000d4001c0d000820003681c4a01950f1030203441d141368444d2075100f0200813140c0d01d2440001f90b4294040e924000a6903510f4030f403582003d241ca400c0115210ba508503403080a5000e102880300b805070301001d0b41e1880d84100c0c00111180804044c044130802410b54660904103010920021a41158003981996800340e070604264141e07000591401000780699a10549400000000d01d801004401c1c041c010603600d21500b64952104a42a03c829004195058000704042400307049019885182080090160f130305040e034a02d501c2d402c66072254401d8540c0703034000a040108800a1242401405a00142e0001802c125012984003c8040517481210030f080014402958640394550941c210f003c0480f034107407a160002e0381d441c1d14290b031200e03100c0c443da40401c5858503010a40d01c0c480c0544891560a0528000320f0310 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 274205719 1250 274204469 274204477
    0xa0c111b030a0b090106050f0a0e040303090303021b0a050d26040302151003120507050a060f0609020d0b030f01110a050f1e18190e0405070e240603010e01030305 71
    0x680c58460b4009810010b06810344541c482c5411000000d4071074070301030500165040ea4a0300302c0c454030014005001038041407080315000b640503d00028014154642600244600d04400b400134241141701a408580003802a55140c400d0b4150f03800a0650a4203840700a50303201f94500c04c0141140d40a101e0000550042d0700030701030300c103c6580b0f25200c5060100c2140070359280c0403481c1c03501c40600078040b0b6402810301070903c0786080c501e0700e8101e46540f900c2c0c404106006150303030780b2140c040c0919120b0b500410094001441e045688180001c0814010034078000d1142c003a010b80a04050000390601c079031020f000c0440700e21841c0410700d00c02250258058162042060f409000c09454005c00350482c20141d44000c00d45030707960b4030742c01001041c0f101c40800d2510421500d5a030000ca0ba00309076220b0212040d1102c00c068640350751815608000d503030b800c4070700d0300481d840821035500c0c6100d100840d05400c807080ba001450200e01400494402401210380c42c2511500410000344200300070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 274206969 1250 274205719 274205773
    0xa140a0315230709050a03030e0103050601021f1e0527070306051810050603070b09060f0307092301020a23060406150501050412260d02030a0c11 64
    0x6460b41440074044212440850400510300c20391082050540e0000c040302c01502c402c03180c00c800146550303401000d131080d1504039410540c440e008143c50ba4000c128080302c0380003914452580c40c00f41d41403100200344445141500c0c004021107451031200302d20a86000f4141c4c0040d083d4030704a021401c5907501c20341c000e00780c42e62144a000202040f4030384156809880b01d1030455a00a041b42c5041d0310b041c04128200844a26040900c0802d540000303429040b582c4401c00380f40c81d0002d4000180c141e008003044140381400001c20051800ea00015031000e0f9081b110700100020b00124a01420070303407018490340544c1c0510f11f2032021681c50b100c001c100781c0a0b00007541c0042c40302c01042d400c0c94000c0d42d0803910b0a840e010002c0c02406c01034203060162030286469130400f072800d80600800000120060300001d44580d40b82d0012401080c4000c04040300d5a0540e51610304030f102070001e50003151700b0380c045448d04141c1c0000301c2c80792400018065120004080c0449614218811132400b00c0308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 274208219 1250 274206969 274206971
    0x51504140c030631140603060103020f0105040315050a060f030512090a091b0e040b241306020304090b060702131d0109030c0605010611100209060702120307020a140a0315 75
    0x825200c03071a494034401c141500c0d409a10140c5002c80a2460170f899815903c1130601142c5820417805490001e82d1a04503030301150410019107034980140d542c1d20441d04080c00c271801041e00d00e19080d142d80c00041c000da04031901000403a68035412803084c03c03400d0200038055000f000307913184900100c1010301041c0b500203004601031030703542c1000012120704000188545004040b00720b1107a0308240d40f48540002030700c3c1401441801d000184d21004404038484d25002941c0c4900801072005060b80d90740300e0001c40c01c03089180c403820060f540f03070010300c2030f54910381c01c00151403040e05245003919100d65019006104105210748032102912051038011564107036030401608001090180074800e5021b5221034003101504d0400d0030903201c05800507418000c000318040b0907120000307007048890741d05200050719884c1d8032001480b980b14803032020750f01c441c0b00d04244030702e903c010005004643c400c0f20041341603541d440070b45415240d120241b55200c11450010400f242c41101030b40e08011444070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 274209469 1250 274208219 274208239
    0x3061e06061209010c030509030307090e040503091909060801110d0f110a23040b09090424060602010506010206060a06030e0705060c0c010210020c0a020103270501051504140c0306 79
    0x10b00350006601203e000b1100d0b074480800c090070981501c01e80f17400c003002e24003451440c034150308003070700c0c0020b18400d121450420074009018001c060045d1500c1c1d4600804023081c01005030f2458000c04124028207007941c1c0f030180001400d01c2c0510465180408040c01141000984030182d07000300040300d4078083c01a207503402e00e00350703c0400d2b0080542c80f07150f480b01000303900c0082c00100348070501d28103080c4c1030800b008180714200144c0155468a1030403190711000c1c3d40c0e64a003624801041001d90041c0c0d0305400303080c81c5584140e40008080d240281c4c0204541c2d51000b00480c0d599400f0395103190420790307520041c00305501c80d411401003032008008841c003141e904c0300441c0d1700782d108240307220700da806c0790030810011369060154422800701d84005504206032560980d884100404000b03051540d01c089401c0100300440206d00000003405170407522001505025018083c111100c0303400c10b080b401802503900c2c06102d140210881d0030071000250307a48002c15006030f800607145a90004100e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 274210719 1250 274209469 274209487
    0x71119061d06070e0303030105062218050414010903210209130b010f14160201030b0d0f0201110706050f0a0c02120109020414060d060506010e0a0e011403061e0606 72
    0x200c1c2607080701d48034200400c00c900c0e103418001e000070900c00381e00d84250420001040320b0359480701a540d240042841100100303a00080c882c480d084a0360050490042014030682c0c1d05040c2e81c4807600c903a01558811584c51040000d10b800c0701d1842d58000c010032070000c0b08c0450300307040c002c4010300500f401c18018038120010000410405411042c01c25680d01c07001c07a40401d581c000c100700340165560521244000351490010898096560a0110b8415101d0074000b968440c0d040143c003540f004d0085680410342c0d040401602e5010403041c0d02207101d02596015510000503c80100c401a0ba140741c209804842c07910803075480100d0358020001400310302809662030114008003860350100008500b0590f20500003601e0140f581c514a00c0450403c2007031584a44e00c201044035405200003807150340e82d10050395580307050300708240c00c07070050040030664610075000d25040c2c51005400c0900703401d8400403d0b648000448034070001d407079044032030122480d2605180d5000040108840e04041247e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 274211969 1250 274210719 274210751
    0x120302031e0d090803060a080d020a080a05091c0515240d08040806010e16050703050705150112020102070b0a0504290316030c090e0106051804020711030607111906 72
    0x3c441c00d072040ca400000b40070080c80d08030681401080940301420a118003520f010b034603210b9426000d0401071001034200c2209108008450b02c030300d40203001c41010740a43c0050b210800c1c0e880000c175050b202e60090402c41030b03403844510344590280012240701504a0b40310a400154900e0b0a81d0024000500a000140448007410162900000030070556241254900340d441015100c41da14084800e42400c1441d070100491758802d405061080da13a201e24a40383d0300e0000d80d40c0d03841d07170180e01c00702c00482c00d6007806d00602600d9000b40d0840d03541e2a166401d400e0360b880703007050010204900b000b00b0003250000400d03ea0380941c402e00e2440080c0c8980102c190300741e20484e88425500e0400c000d0040068141c400c1601100143c40e1082c00941000c1018079240e40c11302480d410301c413010030780790f9013840010012956520068025500c0d5004ca140c500289a02e10352902e21a000b601c0000301010301c50f00c2d500c008004844001c01d11070304164845030013582c003054142c4d00c450310395144601c15494 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 274213219 1250 274211969 274211981
    0xc230306010e0f16092d08070503010c08270a0609060207141501090f02070c080105060f060c0a0f1104090c050f010f082d0106090609120302031e0d 65
    0xc224a6000c0e180040d600031045000400101400c0300c0140300070309140c1d0080c131a2060710f11b005141101002c02d42c40c284d6400f400d0351100384c6a412281d80100340d105022440208a960640080c00100e441c500c00b55150345045900103940307404132040c011000208818007624170f465005440382c07690300381c8600080e01c102110554050380c0001c2c281c001c124100a003180310111500c01382c01200c204e1400650014011b00c103280c903054492280300d001c0c0d0f441d54120b60440b90700c403595a00c03e503501e011203800b03400d00b110890b106002c01c59128800e8180007040354000b074000400b81201c00740c0d80d034985c043c44031105025201160030036121072040e15684540300c1c0c131901440ca11000755161070200581c1030410310005041219003154004842d40200c10180c1101e51012547c041da0080c03100800709100708040b40395120308a60000449030f400c140c1a0056448507a41d0541e0385885003140f440400c4070010040050b4810460303c0c0fa80204c2c0c000e001c8201861025440c81d01080c55004815510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 274214469 1250 274213219 274213229
    0x11b1406130b070908060a05060f060c070906241103090402160c090b0a0504051806040b09010507022404060905070810050a2703090e010603050601030c0c0c23030601 73
    0x1000050007020720012a00c07041d801640d07031400c42290350a00304142e49a01c030190460120079141d2010403110350310a070a00d0b0a030fa0020f82a1030b2181c40345180c07a655402c55204560380f851414001080c04682140800380011429842c0588028100401ca44212503500e016603140000d0103e01015900c90005040506a1480200e2006554108104404125403203203480b01d240031078803901515605c0703140c03044800846000035980e0361151b22001c611543c1c07600301858042c1504200c1000b0f04504420b000e074540d80c0c000c00c01e0756120407040c0d90f80c0c14103880102914164086c0c0d0500c4507090345110b584240318680c0490814500d9032002e00e40342c2c441d000307583d40c1c0d048090944280d4890388500f60380280c010030b0a00c140b0340841100c110041461020702200c0648242c2d4206050160004c400105002207110989603500c10b001401401c090320218006400c1071024109140f00da403662003255006144e4003c002c2ca401d4820040d14a440d0006003400301d51018030190395824041580240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 274215719 1250 274214469 274214491
    0x12060f0622020d090b2a090a0e04030801081605130b010e0d06020301090b1c080703050c030703090f09020a1d0114030103050c011b050304120c03060513031d011b1406 73
    0x400524010981e01c00050140898465125400d1800f10307031518100568294046c2050f0f4038051900820060003840d003058101c0514002804201540452214120385540007500c0c181454004005080d103418820580d000e08852401480b000c00c9074840e031180f0105040100000710700a0200d00c0c4071409240650b0066404401001030315040e019183d140c58048034102d40302d40b0400744501c50320004400142c1a0a000b02c0e070b01c41054000c2d4100c510340410310b82100c0d140ca415150003003c14140d070040030500c18059034000f500803014000d0b960741400a4407032081c85603c0d1481c00e8003140c03140c9d400e06d04001650fa0030000000885000314082c501503009400881e103580c0015161060a02240202c11041d820030700104d103020042c0c906540600e5003240400e1180d084c00313541c1a10680018140c58a098244900b169201c941c5425a0344283c80399450380168403048404050008161804580c451580d000e0180d040b6950780b01d180c0c8501c40f4080259901080d031403628038116146c00010f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 274216969 1250 274215719 274215731
    0x50106110a150b03240a021e07020a0b0301240c021309020f0a06030b1002031c020304020f1804031e090311040f0c111002030408090607020a0510050912060f0622020d 73
    0x664111760b8603035203c1c0c0030141c1545081800e21084a40d13a1a002622006020102d817800c00c65a43d144000010b00a110002d84c69585a24410440000d2030702090010400000b16071f0311940105540d5a405030011300c4a1580c844458045002d0072600e0400c903800b146800f0010510f070b070b442c5070b10406041c140d6070006140031000e0910150800d0000c041055501c140850042c0c500204084c40e0304032003003400036849403103a1020500c0b00103c50b10303d40d884010710701c2c030a4062100b95100b511540c0250345010b030f500043d140d145610398000705241d00242038400d050000c6841850310b000c5461000d400043e442c1d40ba03c00f00c07006c81d08201503010002d4048280410580c20400030b100522044810031841c5081541d945102c91040305480c1d8028030380030528900b59038070b41910364010325010303011b040107000303010008105a00901c0e105208092954201850b101c00050311807054a4481e811030507525044104007620400b940000c060480018985241c1551070000c1e100101c3e16001c01300c1d103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 274218219 1250 274216969 274217023
    0xe10020c010b0f2101020702030703030804060f0b0303030c07032705100201060b1803030d06060203040611010506130b030733051204030f030b0301050118050106110a150b03 76
    0x1d55a454840c94030604622505030600d07500c0d003145a11030300c10304c2e100c0001d00c8a910a080d01900403d54040c0d81405046400000c3c16003002e00c40744150b101383d03810040d4119080c80d0100310f900035084107030594000d0000509a68804004002503400ba06240d00c218410520400070301096002da0041d0003440c00b400c01403410074820740f0503c1600c500090000d0740c20011480d089009100d02c1400c1b00070904103000c840d0b1011300440c1c604200c510000d10980c0e0302d854010b0b590f603025108800001c0c0300b80c0c2d10702080810600c11365008403001480c1c001012108402d040240c48203500580d4140544407000442d4035210070980c8182003007000c031440719840b06080290300f01401c2058400d0190070018229003c51840380264041e515051805c1030704103512040740285020008c20750598030304000400c007410442c4601c2f00c00b17900424140426a00c0350f80855040920b10342107409076108c4007941d0000303000044900b0b0004407071500000c030843c8400009161801c8610140c44c2034080c4d14100603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 274219469 1250 274218219 274218221
    0x2130905090d030e060c030a0b1507051b03010209090a0f0e0708010902010f030608061305070906091a0f0105040b0d090c15090806060d080d0e0a0515060904020105090f040e10020c01 80
    0x244c060880b401a00301840d000310011003510004240ea07000d507035180c070003100c140d54600f58042040c41507810640c8030041c42c500959240b16000400450454940c2080114541402210200c1c60040e00b80d044a8845244c611b000d8441e903445055000c0e15140094902070741041480d00600200700081011062030002400504040c0b01074001c260612100303100c1410b0010340c0c15004001c9001101180ca0300d818a18244009500002c05440c2440350009403d0025000121140030201c0c0702c0642d003441500f0015242181a032041c0490002c2c07208204400d401c0c00540340144004802040c541e03040d41d6680e101001e1600801e0100c2c06140a8004595105a615014160100090000381003138000039483c0e003017128008008510008171b117082a442a085000b1020030344044030042103803481c000d81ca60111250814a000d511070000701c0b40e10b44211003034007998043c1c4402d80781901200500c2203a0341140c0400360416122100070444000400c0070380c0e0401c90b0100d0050b100c010303030041d0038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 274220719 1250 274219469 274219481
    0x1005031b1306030c17040b04060b030613020a0b0c0705120127060f090215130905070f11070501080a09020d121107050603150f030a0c0303201c0302130905090d03 71
    0x400c01885d0282240e03038100ca00c000681098000784810b0701681c0c2c0b80303043c2020706035602403a900340c01480280300f03c121140c941468401c0c8202d458001460701c40c00656a117028100e800c183d10b03071020000304601e042c41a8000d4034104004000304d41090368240e80508207030700b10045c60171310326001c41d0034051004030311030090303c0c1e168014103015012698001420700702c5040001c40749141c0c000381852070b2410f1480300c40b0003400c105001b8003092600d444081c1c44090b01c40500f0011030360b01910404c034050080b40e280140c400c141c50f00e51141c0c40c0c4003020030003012000e2040340c109010204600118006400c41106524103550b007200b0010480c1070031f42084080d500160103103d044c0f051007807003501d8108001c5444016502c4846500c0718000186c03500f0422100a01401070f07400700442410741c40802401d25000c0360150b103410b07114002c0f0440d5a00490f251000c1c034903a001c001105454030a8001b011340c07910000d81114060344400320001220001d491682866010380b107244081a0107000701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 274221969 1250 274220719 274220741
    0x30f02431a01080c030718060807080d1701030b27030309070504180803040206030a020f0d02032208030601120b0a060c05070501090302010c0b0a2304050115051005031b130603 77
    0xd000b20b454503002180d520200ca02440b02410701078104462062503560220000307200c01c03c202d51003070f5543d8082f81d0315555401085000614503001c422200024aa5828104da500a0401070b0554480d007d075506203c072200d403010315400c4928000f0074414200080c500901c035000c00b91100703610b0002000103ea0366040300807000100c032050729004c101d4000a507a072050701610b1b00d0f542c076581d11000e040203204000c82c4014a40020446080000301d542c061807090301108400042c8030801508241400d021003c020607203d0100000740c4154800d0340404102c0c2c40c1c2c41d60105020203040300007100700c40380380c01c0b800000d08000c8250050103010070220f0f004200a0801070f54480c10360300000d010985100d000307040981c0e0307c0701041d9040e8060380241022030004e9440e6124078659089a921360000355002c0c0c40c5036007040300c0c000d415181032550608070303a0018103000c5a4030b06c5600984485e000209800c1321100d10414584103036000303030010180c3c028500d2040001501b080740c05802c8951440c08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 274223219 1250 274221969 274221973
    0x102060108060730180b0f0c0d09020a050a12060614100f0203120103080711031f150e01080a0c0b03010501020c040509010f0f0606030f02431a0108 65
    0x18404003640000020400c800400c4c42003868242c2e1003a440703441061041140c4c28107240c06000d0b007910f81511100c0c240c1500c0740244110a4550f20524035a00d10251490003084400b00031000b442001c541c4194a900c2c80030f000c004031243e407040010140b08003580401e200341c00e4880c00341c08000041c0f00d9803000c1d04210140e40642d406100208001220f03880c6034030700303108001000340300c168003c02c207580c01c4c0c501ea01c8146c3c590b03685915000c5040c1e04a0042121602c02c0032907642414580868010481c091078072128010744580303400d03903010b0180140b1050625004040119160b90007046160181c41c00070020051100140341001c40072041e60300140031103409000502060703a01003050201004216030105681d10350840e01401403480e11518080b50303240c0040749005d010103400500450380261010401030f000419940300b640304451191a040941e03c1040c103c8219a05c0307080c40c004041441c030300d02d42100100b60405295422070a4030101502d10020381c50110100104d0b02510070100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 274224469 1250 274223219 274223221
    0x3031d040b10051905040e0106080402011205070903112d1503010305060708060306091f0f0c0e0405011401090312110a08040305070501050403030804060b01110102160c0b1914190806010206010806 86
    0x147e80e0340c1c0d041040c041c0008201494007c9419a807045c840340c0221103082208105a042c1000081c2034540fa0780700c212003c070605180103c4501c2d02284803240c2c00c00c26080008450b0310b19200841d86000392100c1544440040243d80d581012100518040c42c4144000c3c8003030705203490050200074000300164441c0d03100c40c0030040150400b082c04801d00342da201d44604032403c0380b8500b04c042c3c941150400003d03860040f01e840030380c0d441240c2480546081d1030170040b590b00c6007046c04605801c02442408214214420400030310141e6812600003107d29060311210605078046040200c1c019090301c80600101d000e1082c03240500c4500000e01c42400c02919041c51640c0c0030389018070003400508120b81c1c903c2d4002c4264080c801c0e0900100302e02c8001c5668855820442c1c18102d01020240c4440d1445500402c07540c0c011401c07101c48590803070129105000c4040116440c60020a514180540c01d0220964001510005240d11100c0c0c1d190f1120070301e0444002460410140e1240199500c000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 274225719 1250 274224469 274224479
    0x10605090a0e031207090e1312020c0f0f06070c0b0717031b13050a17070504360204140106030b030d0905010c050f0609030408120403031d040b1005190504 68
    0xf048503680c01d1404080101940c58010a440000855000541f140449010001e0a4010121300d940d2944101c0600c20a020f0a00302260345007502140c03607803c07442a004022152800300b206051191005200d00d18011076556100744003c115030000e40e10784001702d008801c01803031840720800e0080048240e4210714010721040c1261040010142422500103600340303207021115036013000f030080980145001caa84000010392a441c0c039442c40c80c43d0103944000b044078503190144a01e0712813641e0003227440302802e80c1e58415030406074044e032079084841c03140d110043e05d6034044d900c081910f0440b26007841d0300d4554084d0555610071000c61181d00700050a0304201d410038075010a8510a1030310740d2043c0100d2410b107140501c80e0002200500c01c2e0b008100242000100510030340b41c2c4081520303c485000d1004040602481c00024007040c0c50b03948040001e4004441801c4200700144007048154800010480030341344030308003800240c03002450504030010341c8540310304403100d40303050307480c0903d05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 274226969 1250 274225719 274225723
    0xe10050c04050108090313080c030d020106080601091d06090a0201030e0c0d0b090a080d050403180303050403080f19030603020a1a030a0507110304091b0302180904140a0302010605090a0e 82
    0x2900860f07042c82101c402050303001d581007040d00d680035003140d810240c03180c8a402d041d56504404030160322911a050348803000f42d1040c022202140d14980c01400f6590034200080e001d001e07005504c0300503110032100e0741c1f81400308100080c081ca4200b0042e003040c0c0250700005041e92032070083c0d00480d5104002c40d0603980c4909030a07246480e0810703c00041174030344000701400d040c090140908036000115805503c00441d43c84a80079501c25252410448045040400c50000600c405804510140000c01c041040c0354000d200c0000e0310054107150803d8900315200380107149200c1c4c400641d4801d814000c500b0401e1201c000381130380b07040c0003019090310100800944002000707070614071340350808101054060803882d059001110140e079141c5440d903200c0d40c000e083c940c150b44d0144007079045038040180244200c0e010413030f14509110103480d1080034171aa5860207041242c100313442115540310150f0a10140401034802d600114140385000200300c00806c3c00742900246510b0318a01003c04400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 274228219 1250 274226969 274226977
    0x5120c01051501050d0b1311030109050601020a08122206020a0905190b0c070518090d0c08040311030a02040f0c1101020c0d121104120b130c05010c02040906060602010e10050c 77
    0x9100008a1821b503800003180810b114111059800c070b0403e4115121800524050360607203205200801c01982c0705c1004a030303500c55021001d4480c2804124442c001000340018550050b00c104401d284116090303058541c0942015003507410681c003280d4070784031a0740031822000414044455a403107219124400055503a00c2c85482750080700041c2c0340d2400b480920025008200007001040300150515005031f09a1080300c1c4040123000b070b4071822000e14022015040440e8005113002c3c141f03401c6944a0301d00c0d40c0d40090309a070501c1111030080050383d0f00e004000c94182e4801012402c0c00b50080301030700000000c04201b181d64018408034920010010702242c3c0343c142860410f2074144000308010080454401542442d280001c022840c007a1107502c86d10030390700c25035800c1d07650750700d0300382c250286000c10500808004245204118075841340b078071122501c1c0010b02c001010101c607592041242ca49500c0500580d442c1c81041e00c0e880303c1845400d030000d48011060005203030280c0c0001d010b00c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 274229469 1250 274228219 274228237
    0x4080906071a090c0108070212180f100201020c01060509041a0601111615050319050a0e030301081501080706140a0905091f0b0c03041401020a05120c0105150105 71
    0x1030042000e030305014180e07002e20b0760401c0c00c00d403148050820398851038840101c00c2006020411030390100b40e03080c1c0300244030300d10f00001041c0c0d5420100780000803d50144100b80d0160300544101c00701107142d40c2c9504140784e6560310780006035140781c0c0009450940d44968403661007021400200070200340c8103150034014511112140ca0b0503030300d0400507a400c09081c81400000d100b668481d1042c010790031100e906940820815048504841c80201d4241c4021903c5501048004040780075100403a00310b680c00206285000c2621044442c04501d581c0003644501c5190b403040d0261003003942100d15007805004118084d00082d0300b03106000d040100460304015001d030700002c18144180c4140034200241074000c2440f1420b040950701c0c054014103188070700c07a280c4400c800004010015070704036520650394802440c2003070310b008584042500070902c26415800750f140c41100142080c407442c80c107404445d115a4581d449440c11a0864000411014181618030029000d580c0c2140a550300301c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 274230719 1250 274229469 274229479
    0x5030c0603091603080703080c25030e0423010503060f04031805090103080d0b030106061d040f05130b060402070201081807030503030a020417120a050c01060b04090e15040809 77
    0x1c0c07030b1082814a000c0007824003003000403030643e000c01013040041c0280340403806640c6004154a5001540490f8400d07070420070303c59070200304400a0b80c1c006407180c8118600030b040804d9110444070210f0140c8190b80001ea42c07403e80c0314044641c0c07001d50710301180505401d5000388440d26143e4610360366060003038006400c0c000b11707071503804801071030f10b15a102904004d00046d100356541d2910110380e8218410225809003866140426410144030303800480c0c0b8507954400e41010942402c0202010302040c2581158944090503204c2d0924058103004280d89040c0303c11002950800c021512006803005214078010010840035130b038407554407038002004122281e42d0003074030b4969518181e0117520080c141d01021003000000c4866601810844032204211440d0b0140d411607103440311011004440d02d50000d01090740128850ba000c0e003c00c0500900006040e03485241d284101d42103030340111a075540380d402e241c004e41014401c83d10341214003c02c0e4500e031b05195031070500c40e00840c4d520354011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 274231969 1250 274230719 274230721
    0x3040e06190306020a05040e150102210f070305030f0a14040b070507020901080c0a09060b04090e030c060406061403010207030e01030f020706110c0105011a04030f0303020f13030c0602030405030c0603 88
    0x10070380c85402200115840b8038115503519a03540701901325003151150707803400207000300001c030100c0c001070b4440100a8145d01800c464115025000780107510340348072100502040c0840d980103c4041c00400030036020b0b444980d241d250180244441d041c0040110041a0504024035408400184419041580001e0220341c9a4039020101c0c0d1030702405402a50081c40741000007400180810900300e0741e9410f0fa44000c0b01ca44500758001564441c0c030a40c249242c041208002c0400b1903846541c070701c001e00e81564903240f4240b05081c6441b0041c0c40c2503da641c1e590b03004101c0c00d05507150000e50310301d09070029030034441d40e034030003915124189c620b650506450700f80c207641c0d40b94039904490416520202c100042410700450f0005d03904001d013203185c10f628200001c140b8003183c80401e50016581900c1a241034219600c02c5d0780c2c0084003100314241502804038a0744000f405001d80890340280361500c403042d255061803981000140d00807802e64204100922254801040c0a0101e071029648143c3d2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 274233219 1250 274231969 274231999
    0x1006020a0b1e0f04021302160b07020309130606020d09031109191d010522080904090c1202041a0328050316030f0e010806090405010e010203190e03040e06 68
    0x19941c0100205a0a08903a0040054032804443c0e5140200d0095401101610300044410f04a10403228400071401001150300000384507101c02540c80a01c40c8181c0c0d042040c050040f425010010348070700c441e103494804c24000507904000c000c00d1640d0900c0d02b80805031039a1140e5010014443c81d680c0500002130004510b480040745561145442c004104070a04070700c000ca440448498034103a64071750038400400c41080583c21801000d044c01034042040007007994a4102075440001280d4125031540d000c0000311b03404606200c001c1000343e90011201600740f04000403a805c90700d5044455400c0a001c00b480e0b100041c224907040080108016114a5000000394610007280010068400010954910b0281810190b403c920075110301c010b04c0e600724401e5a503080003030130b0a80000d0380343d0b0002d00e0302d00e4102c00080c3c0190080c4000504614145581ca09982c001c80f099410845821039811444105100d03039980984042d028608080c2005a5003500c0480078107814810454100c441d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 274234469 1250 274233219 274233241
    0x12060604051518030d0e010e060c07170a02090a1a10090510050c0706090303080f0405062e080304051305060f1504090c0e120d0c0209100b04030501090b1006020a0b 72
    0x3e40c22000a0441d00c0e1003081c0b680051119040400f00360000d025144591114201030301510400031065002c0c043e41800c00703012000049030402400d2a6200d40350700300d005a21060307007490048035000310201c1d410f110320110042611001543c0c1e0b0154188003c1c000616500542c20030648100311490782017190800310441d124061031041c00103034014294001754507a00310440008407032094840390100e6032581e84048800e5405c0b64043c2036078106800182c024076441c041800e4001003181e065044c02c442800e80002400e454001d08030a40c0001400d000310318012408944134400024203110034070b482808199103420070700c0d8a034080c0c19215580d002c2d0240f104103413805450b01c1c51013008517040c00301004000c203000165190080000d61040019030002103070066540805456200d01c002c060f609000c00b4003402454251103400d07200010500b0040c1400070402103016134004180794a45062049034010b0180803060b45c070b01560010070849801080c0a201240c10481035031842d030712402058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 274235719 1250 274234469 274234507
    0x304030602030c0d0c050712032003090105070e030106080705100207150503060a090b030a1515030f12090501020a0f05070b07050a050c04110f070c0801050c120606040515 75
    0x4241600200400c14000d0010f406400541d2000c84103128029502d00203403035600c102e00d40075000c4000350b0802c140c610701a421100d480c2480405003001d90404400c111256003041c0c0b02508540d4440c81804441603021071141c41205080300200039651038440200e13941c101a20032540501485404000d0050090107898024030902e0300080e103400f96940c0c02420343d40104c1c1d081e4840d0031194804a8950035500c240001e01a000d4010003901440b0740303940300642c0c8205102824240c0398441d410322100c01041160007988601c421300c00303017020382c60714030504804800000200a400d12082207180e034009400003180b034201c2e004c00c030401103600307001c0c0c1045170b6900420000345000980700108100050070344000c0380184199a01e100e0503604120640740c00404030b41080d0001d0003110018400300004202d079503c182a1100d00644d07071301c8002c3c2520001c65041c20040701c04a4945240200c0010042e4802c4048a080386410304200002d2860b0b100301c0c03440e0614200100303a5004404440e0002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 274236969 1250 274235719 274235723
    0x4021603030b1503042d15050405010b0301110d060b0a08010b0705070515030a0f0b030c01051602031509061005010203121806040b0106021002040f0504091e050303010509010e0403080f0702030403 86
    0x7113652407500b4203207a103003144005125201070500f20701840d690205945030607102c5500140c007541c8000f0740d0004001528001e001558903543e1090340a4040e5800d10071040c1d10002c840040d42c540e01019040412501e141d80410141c0c0f104200405031182d2000500307043d00c082d0103d168481500781006490078546800c007582204552044410802d00c10015600c9003000400030311003146154411826a10a2107102e5055800b61247c2045580140050002010a6480c2c81c1c200140c03600020710300f4042c640c82d21a090400c00910092881c2403140780d83c00f00c80d82c090303001418a802d000039034078400c1c03020002080c0c1500c008078201820080040030300e009c6003011210715003420300f000c0790500c80c2031007100054816526000350040306130007600c00b114044440354002070306c1c0406220107002c2d144400c5400342c515107030f0115a50806100c0c0c80441d070240e00107507101e6041405010544806230010461454088200000294080b00c842d038801840418039030261108442645580540d802c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 274238219 1250 274236969 274237009
    0xe06032a0a03060e06120c2701150e010c11010507080705060405010b040b180613060f083720151806070b010b1606060303020f010b04021603030b 64
    0x401c2050740740e00010162501c503004661a912020204101004108400c0040360007038600c0c01985d14001595510260141c003414200000108030045805000d8100e2039030803030006a03411005600480c3c11181c000c080c21700b80c9050000d034540c1c03052591960300c2c07207042080001e880e0741000320030701c01d4441569000342100c1180c281894164040c11455540a005034a00305050100e482c05031140300141007815050003542d01d814040c00540841c5000c00420551900c90006000d0180d04c1c000d001000098040d040380e1650f00354202821003030303c010010130f0954010707130350144941c2d110100320a41d00c03480041c01070030320300c00d600c0b5017600c131101d8a60f000000700e10f1a0721025040c0c005140e07000d004801400002200400c00c045401854800b81c1006600f070014450113410310000e00840400d40213031007800807159500310a90700941c0080300142c10581702814407100902400390340c0001220107600300f00402c03000c0500380e40031500250801da140d001001850300c0e840440ba19402900c18 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 274239469 1250 274238219 274238227
    0x312080c2d03190b03010203010b1c0b19030c060201142d0106120513210201060810091b080d0c0606030b011509061404030308150a0608090c010e06032a 67
    0x307911025031080f542c071503281411080c5009290601c21a07041c0d5404580d000d04003207245282c03007480c0d01e0507110300d61082e81d1519061015504c035407104000290b5444528072060461920600c4500a54000d07802e580c1030041e000036652507141c145504c40a008030410a5448a00300e4031850305a2487c00003a4031103810010540030391008400c4200201000b040c1704680700c05461850201c090003000c0c1c80100f001460403107030001e248400250a00c0c1d4800403400540310481103041c0850300c0c011110984d40c4419030300c204229600711201d0b4ad40c6480c42c45012520382004c40e6214000000b4102c1004a6912000d0410550354072040c05990040c3c1c202519603110303520501d10f00c0d1072404500115503100030000e420f510401c1c40b20202c144804150b41003510311b542c00ea41800001d406100c000c80014a100190b1b2104600d140c028101c40ea07406540703040100100b8141155042c5041c1000a5104451081d8541c1c500705c4e83c1140c80a882c440412149041000c41a031821110f240342e204001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 274240719 1250 274239469 274239481
    0x10e190615030c05130605031b04090b10020c010f0f170c0903070b0f040b03040609050114071103040608010e0a090507091a090103050c0f01270312080c2d03 69
    0xd400760300800382528100f2030704034440026a000c1c080e49041c0080075401100512050f8810406103070807140341c02200310380390406da1481c045030304290000070810740d0312150103180d450011001c0303500c08401c0c0090014040c581000a200d1091641d40c00c080c4516444440c101c0b900c124848003032610041c0d146e180509250f5514002a80074284080c8284188040441c00d1600c1e01e01b00c0c0c000710411070407185028503142c441d0f00ca9810090042d100d85545803400e134086407080c01050018001c0e0b0084040300d2400e1140a415104401c0e000c2209030300a0006114190b0400501c50656440c110100542c1c2d440801c2c2901404215600070100d02aa0100141194450f04101d40c2d40c43c070801c40b2000c6000007001c4c00305600d024030010f400c55200c0e0180c050103003400002c095100c00189000c1040542d801c650714440c001c0c3c840b02d005281d0540d1010014004050b2649822409600c0c15000e40d09001103041c06a004158055907006010b6403a80b960440024242460011b85450540c43e45014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 274241969 1250 274240719 274240739
    0x1170403050c0d0e1f05030106030e030702060409020d0509030c0d0c301704020f040207020103090c0b04050109080105040c0312020a020423090708070b0901050d0f0912030501030308010e1906 84
    0x18005401500807800402d805d040703144054007a417000f07940e200d0440c1e280120440c06401600c5096248c0c1c04104401000b68480d400100003900d9038800c0542d4034fc0f44106c5400403500300401d0000341da00144410074039150041880f0740c00009030b00e8503252005050400155861030031545440c140101c49070418010200d0004420708003040c2c0790300d501c401d10058003007650901140e0003540004610f49103a6a450290f0140048034010f2400241421651f0385020078250704d50481c0316820b030089000c101540c1d000c80c042024015000082c0050704059071001800d481f140001410604c0c8190150500c0d407080000a0700303d030f0000c0c02801482401c609510301401d005000380341c1900a40b00266000748005006001c0303e020344001d00070941740445031100b0f500000051410400304124504104180780a1000c0001d203100d40040c81c64010714000d07110319030101100341450304290042020a42003811141110b1400b010726850355985005440c4e048003c40c480d02860b0702d002070100e049000c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 274243219 1250 274241969 274241987
    0x1140a2607060c0b2404050c091c110d0512030f040b06010507020109170102040305070902030703060f2301140a09030506011d060409050307020913170901170403050c0d 74
    0x3a40d030036500207a440315000c03622044940c81c0a0712248000011960350003140020f80e10400208501d40034285441d0005001d507407081c1c4a2034010302c1e0210350343c038461405480c44e1000c1c494400c40001c0da0541030380c6240154290340d1407031b44251820408401172050921080b498a4200d2030340603504e141010b65050040c0341640c0c03d4401130407000019a01c2d500034000c13103000c0c40c1c0585071001260326056803c10309400700385040303060307540034440000050f208105001c090708084401685030301e408000282262203d5100e02c80248140c0c0003001170801070380d88006000c000ea20030203440d040c1800166803110080011510f1a4000500c030501c142c1d1150084d000c0d280f0510a503003090360396000c0208170308002000c00511100c0c40020800f1440c0c154001102c503441907007a00e00307003022078000460041040300c1194080000011110400c10f540081d05076169030070400509211100c6c1c0000c01c8101d5142e001021020b02c0707030224040c14003402c1600c0303080c100034049a0000301e13841c50091450314 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 274244469 1250 274243219 274243289
    0xb0f091203070210052703030f0a1e0b030712050607081503191401231608011203090b04090617033903030c030403021b0901140a 57
    0x80611401000e4420320440740504002d80c0240b0030060800001001801c014000d0442010100061a241c1e035404054580f0131804101441d101e1406444070889400c0c01804111010701d004c0003100b814044591003032003e03000c1407000806111400120f0300d080e01d04e4100300c0d1091148003070700c1b04204002445522500b038655448441d525401c08140040741d520041ea689500119034808036030b0140703c20400d0383e5001d1484029a15181800d59085031984140342e228000103180392801c4650365041103030408298000031421690812000345540da0600030a56214214003000307040c10f00c07500201028003d503851060f038a90f5560200001005144038002c20130201164490b80c81001000780e40c8551054110b00c00314000d2002e0841c0794003003281c0f2075201c0d40c0f111482640c2c40c032020005540304840038500b85581e0308041c200a03142950006030391404904082c000400703510b43e401414112003919982a0003072401d400011002403054004060303041e1443c08003543e680d02c0d540d41900c016 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 274245719 1250 274244469 274244473
    0x30512182401140307030b070206071d01170601020a1505060406050402070f0b1f0905011d09070608091002072307151b050d021c0f09050607050a0b0f09 67
    0x704018404a1000314000d1241007003181d644010420080c4100507660300c0d460040540c0c1c1580d84130703a07402c8204001924501d005034001020007411a030004bd10543c10b401101206e5982d90811000030100c500300500d00705c107600d200001c00c6135070b4002c000220700300380e001c0d00712544003a0b20a40e4100401c2d044074201c0c4200d0521f01c000526040501c211031201d90064480d074900c900700d0700d60940c400c0d000f41c00c85d090711101e076200809202c450740c031250140558400224455251030103500a0000852400120100390400d102c104000054a0411a41281400c1a003962030414a44c01c007000001d403003885600001d01107041100781401d000400a0b1b008e22078440b80c000d010480c1d40e4201d1030188400c040e00ea081c0c00f07404036018a900b44c48500c0003030009007000e140c9580e15400d051324100d00e0000f40c1e110301401030003004d4011118100c0b010a240c0802d5203c85d4540c01484000c40384145070040b41c2c009844d0301403101c00d000d9a95480c2e00a0402012801c00c020f04800c5d11500319689041c2e8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 274246969 1250 274245719 274245733
    0x3112101061110051308040906060906050c0c011409030f0309040e0102070f030305101a031503061501050d02040306020f04090b03010209060a031d0607050a08090105090d05030403051218 82
    0x14034010100c40e4000c40b162802841502c2c160f10310300005100241c07254601c0b1030908031030000100000c004001405003000049241c40c5400700142110b401904428140401841402001c0000040f1503d00a10910b4240c401e4100400c18051a204c0c00710b41c0d94144c022084540140c1000200a0040d0f140a441c1005213403240311030a4201d02610780020440d000504443e00030910030303080150443c01f0f81500700c400680c0d80d159a0b084102d6070f9460031501c200481000b2295541d81100c0b01400c03400d4014040c603140071b03503c40c07110a44941a00c1c3c184040800c02541040f002d606071005590301c09421991607520444195068201e803162804480c28081484090b00f41070003900e0003c03102905260514484841c264094098203500305034092544a1f61203084104010722402140b07951a100c0e60360141d10001403400c2e50007002c07402141c0c1000d050004043d0001240c84003240c0c039151450301c039103840c5400c40f40b03840741081d0500621051024000307501500c0341444960002c0400310b0b010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 274248219 1250 274246969 274246979
    0xa141209090711030c0c19030c06080705160b040209070c082b06030c05090106050a210f1a0a0906030503030a0905070f0303050405040f0e07030318050301140f180a020105090103112101 81
    0x7e50540307000c0102a001d80d040100032081c010030311190010300e541049030a01c00483c2521038407000c0b0314001c0d01e09090110a100543c10440340c400e80000e140c0c500b80d64241c400c0d45441c0000d2060f549070a054000c40c05121b8407441c1101219401102640820f04c0301da9a01c2c100180101c80c0c4d0300030907100d00244000080c7c00c600550031511440c8003621224190760005440e03251100018844102240c1c48292a042d002c10a1048400c3e21600b1100c0f03440405069060082e040c22980207046060702d05001400810800800d581c0d002901440100b800c03e482d2401a0070301c09654040c0004010040d004010190080054010350301d05680c20030030b49262102c00425104000900e250a81160740b06101191040785402d01e00040c05004119159495000c01e01b10b500b08491600c00940340c20610914240d140c2c4031581060810545208412070f03141800d4544179802402810712500140400159000b5004801031608064409890780c542808240300c45414845c0c91908005002c00072038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 274249469 1250 274248219 274248259
    0x12010c08070224040804031203060611010e19030c05030a0801090507030b0f400c08040203120c010b09010602010f0e0706020a0303020f0c0703050a141209090711030c0c 74
    0x6614004898621802c40d041d202c070f20030f0b0014000742d803192005c10001c00401c01460b030180c00c503010750760005022864010028022000101100190703410004644100303800058501810009140c1c1030600307905515040d555890180c100916a01000c1900d840c915001480f19040302e0100006100b60356502008404450500c401d05a0204202c0c201802e2828000341040c06440f80c42c0e2220703081c418a20443c4074030040090b02c0c3c0e68001e240c542c0102040182d0061a480c000e540c1402552801c082d80020f0325030b260301552001242003c561021034240940080e02d5011000e0301d101d22658480400034040e040d01140d040c1014100044154101d80020300c1000b22902540074014944a0355402c4010303500c102d42a5161640c248101c80501d00180440c100951258004200726020343c54040b010003110010f030074541c0c0200d000390000a1084040706d0417100d003201d1020302683d0700c14007581c45140740005420130384404559900902c0b8009804220b2440031580c65291a186c40b0200c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 274250719 1250 274249469 274249483
    0x30507080d17010b1c0f0b0f0628090306020703050301050f030f060a0207050724080703111c14040b011d0108030702060a09170d031a0f13020912010c080702 69
    0x341115211004001078490b01c03000d02036048154200203000d0540034181c0341686c8210080ea401150740c0c000241040c035150000110a620981c0d255007403076030042c444029103c28440860300203c0c03d03a07441a1140c07107200081f0185034810811525101c4509000b0310b2074009010b103034000c8003041c101801030300c3d00052880700400b0400040609a0307a802c2030401a402c1660102c41e588150040491810300d4001030617441182e150000b08184410b4200820520000e80180149464203880441440c490002c0707411052030b2741405014141c1100071031000b03000c142c68002c002041c1b1070502c410031200f0054107048490507204400990031160420300d070210b0038460103106034401c00c000c1005052810103402d1002881c10a14141aa10040d00c1040401c0e021103101540002141409842d014454042d01d43c8032200c5c02240e07401d403000441c1e0751055041580d803007013141d0308504001c4542a0112401d0100c003a198002480f1001c407114040d1190140d4503000c40c0140c1c00090a01e44002141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 274251969 1250 274250719 274250747
    0x13120b0604020a090b0706022107020d0e010525020f060a020613020a0b0705010c030f0603020906121204091a030109081603030b060c060a0c0e0a090b0303090a030507080d 75
    0x118180c98010801000350300c20702e580c80c248101040009030205130038010704050b5014140141e0307100d001300c02144410140444602083c52028107100c4415030008102c490030005013400f051807122103005803a00c1c001c908001469102d009041e0898080010741501020b2080c2c07668110b4100c04403c12185009807030b102001030380050001094464458948218140060060f240c40c1d0784a2640c21480e5001c8801980c09a441c4e86041100b680d00d0b1081c0d040002030700b6800c000302d50070342d030008290800161802c2e2003092400c09044e0781d8102030000440610f050202d180c1d45540c0e0346c85910103451080b901003007100030f444482c41542010b005500103135a0204916103403001c1400040320800c00c4500a50405545a10710101d07915547c0040c0f10b0003002900402c210b180070101c00041d15111a10b410400100c54004107a68890402000a8034142003001c0788410210000c01c0c5103000d03110600350b01190004002042c0140403d900c01500c400310b00380d070841214243e065030303205409442 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 274253219 1250 274251969 274251983
    0x2040c03140c03070e010e0409020303160c12080406050901020106081e1005060907050a0c0203030307170601020a05030d0b120703030507051507140a032405010e090402030a1410050108031312 84
    0xa0300d01980b00c0c0c503100b01f041c4030081c800515810943c020a185070000315801201c404d800300f04805001420b0101c00045c18041c201c408a03210650315410303240600d128040520002007684621a1b0003074020301c025120040860301c0c40c007500081c042000881d41c03c40800f0340183d00030b0041c01c03002401600d00c508409420700a09840d1304204848582c0502589400c00480204450050740d080c0000e43c014100b41e41e454074860410859040d140001400321415075000c0540503002443c04000d89001120142c80015003030903c00100e09040508a40c180e0303d401100c402004054102001d418003600420461329181c0c80002d00d0404101e0a450450124890144500000103c08000c010701102c3d4a4003052003540c1c4112007420136000c0e0503105074540c0094040c0f01d1941c0c400b601c5003a0302821110406c0904050700800e4a803006180040c160264120700043d10160401a0b210090f2100700100041d60350703540d0950700c0e40c2008103030300e6400020580001e15864a020505150b44e00410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 274254469 1250 274253219 274253237
    0x2d0315010305063006010f06120e06040311010b1203130e0c030112141c030f0212010e0405010b0d0809010f05040b1b10061d0609010e0c0d0902040c03140c0307 70
    0x90b0399034540015800450001142c1c3c07034641c4d001e030301c1440114002c201c062402c1900a08201000d007a17045554000e00c0001e241200e10151840b0014056401c250141408011043d9001240340500340c02040180c0117450182d1601050301d0020041c142d00341014004040c3c551a0b4034022026241500c0b4801c2e054414030050001c0394a480489401d14819502e0304840e11580b030b40181402000346155080718250840b040d02356801d80144003040b1000b010461401040c01819003025106001c2c419900406100107000c0000c00d40c081c00c2d401900401c0c080720803005150042d403680c17144ca1018001814030500c1c400081c00b81c030541c1c050320314024000e07003420783c1500074000240880b6400c03903092003039403143c0c1d840c00300901c01c090140414054648002d0807100184010b07513009052240034030055001005950034100407180c10064101c01e10f0758070704e4031000c58400f4003143c11020394000c5c07804e0300d4115090341680c81580c541180710202c0b0880c0e50b0b20008003035a030008881443c0031480b042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 274255719 1250 274254469 274254499
    0x30d06080601080a030e030a0c030b04051002030126070f0f1d0c07030c0318170c06071119030b18010c1707030e030d150807080a02060a052d031501030506 68
    0x1b02c5030650120090112255804151990420158990310030b40e503c4644509101c180241031090101e03407000580d00394074551600c0306002406401d6403041920f40308204000005400901100d801041c3d0404d01d01c41c02602d4a041c0b141d082c0d00d51250504810204006c1040e201d04505071500c551301c050034840c01c0c0002510143e541c0c008040e400c81c20861b440542060541220b4201c101520181201421010481c4011890000c00c0c9032014414801449400700198030000c8149038030b4415602502c501c1d4100c0c900f02c2000842d0340004140c410036004020400c500c82003056003941416000740303c00c400511301a10b2150381410800c004592110001d007002e0300941088001300e0304142140d10341400c3c01c12010031900070014070b510f800d6403c0c0d400c1200420811034400179103c1c1c08003606060340385900040e220300c2072140344418048040340aa8070481414003604081103031114400c0803d0502c0b06a00381d0b40d104a4841c0341803100fa00f0030700c01d01d5101e40b04180c80740c04080c2150ba1200300d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 274256969 1250 274255719 274255727
    0x30307080d0e06090d0f210c12020a050a091e03020910030f0c06020f030a0207030303270302010906050a02130909051204030b040c052d21030d06080601080a03 70
    0x908031842401d510349210301c0360072100300b04941c42107969601a01c1030001c18140100300d08840d41e0004200440440182d4958099010303503141400e821f0000603130940804001da81d55420507011440e0340f4408140001c00c180c0000061600c3d5085640300312416444810114610720740304140c49910401000500044c10300250b00c0307800201d4050230b07000080d84d951300d01501401e00c1c08100c0381d0713042c0c03040d041040310780400ca81c2072a180c031400910304049a01d10001d40d114a10301c4007404150b151407003552403026400380c00000000c012159201a4404c0c14007901900003a502200c42074a46400188890001e1081c1c9041040305801488114038111445000d8501d91a0a45640c090380c0560313506c8807030f00c0005000451007902c581440d41b51a04280910582c294042405a020340003905c07640f40082c841c200b407103203a400702d050b0700c80c40000100d040040c40311801c080030118800c0f514015940000940002d5580c0d00080c0a001d80790b002e85503c0714401c4c41500b0041d441002e41710002806 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 274258219 1250 274256969 274256977
    0x106020303180c040c09140d03050a03052203030c0f0206010f0314070b1c0e01050606042312160828030c080406050a0e04060614091908011b020c03030708 68
    0x403810840f0414150100040e0480d5094144400801d034007103001c020304104501004031301c07a000c9441d25401c0c107003030301d01818520502501c00201a6100300280c115038000c403a6070441d0b0785d4010041c030600124030307000e0010581003400c031020034442c2c1d100c074000510024030103050310304c50500e24800d0b51a5a9800c03d6408000c100301c051400341c10000700c0c7d4041e00801400720b0030780320100701d000020030028080481740f42c9812203609906007810400c10391101c00848049078541200c6100c58695080c1c108882c0440203211513024034086580c1c468440005100d1200fa101c540d59801e41a940314186503884e1020215002e4840700102d0b4100186450308120348a5806820702c008241d200f65109815540b042e04a04040b070000b045100018ad8407011800b400310058904011180c1021800742012400060290080c80006140c0450352101b40d19001401d0301d01100b00f00160712440c085003c0c05000c0500e41036945010a088245880058008458040507010750301d400300b0b5071121040f07a44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 274259469 1250 274258219 274258261
    0x807060513090207052a0901050607030e04110301080f06040c060f0927060e10050907110609010605030610030309050603061f0e1302130b0a170702030a170106020303 73
    0x180074000012540420f0004002e032511410292988101e070900503002007500041000101001544580060320b0321101c4c541980d134200d6034a52555020700d130858003103030120075550308103041c14900200840581c014505a600d1a8203075110364903503060b40703603440c20200e50280c241030305001c0c00c0006070300440400341a1807883c40d00419407922005040f5000c000c0402020180c150002c2d0910000c00c40d224100241a0040c400c8985040c03540ca652035441039405210710510030345000c038892034000c420741071140d111901030714120729046000c0d5000f054107104007130190040000017903014559014640c25654140c0b24810b5140c00c00c0244011b58200070109500001100c030071508018105101030031201551340c1c0d0131000e00800f0140200c502c0319510342d100c5203005000d600340040b000d8800c44107840c00f58001c3ca45440c1f0607172045810704c0414007500001d00d40039041c44001903000c00105101122500d80310a04c60841d0740300544e07208240700740d0300107030028408540140030402440c03203415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 274260719 1250 274259469 274259497
    0xd020f010309170a030b010809031b03130b180613170703021e030c0a0b0f09040204030b09030a18061b05070b0414040f020304020108070c2d110301050108070605 71
    0x140d41a42c80c04503088200075000020440444e00c00021039041c043c6480d0302c102071070234601c2030a09450f071a44c0c03800364446145281c00000400d0144010070400e8983c01c44141e04103070b028956542c0c10200550041c401c0c070000d60403000d400100c07403d07c541101c5505090071020301c0d03154134010003038001c42e005240720000e5015801d800005a03803012a9200200c011994010eca046c1d90002c15150072420050307940205c8d0350740d80c01c01c002281c4c202540d0700b140c1a511701782d90b658480030001d0300030701c40e076007004184040074403d001200b4000005002a500a51204035503070226000c078844680d000d1152400041180d00564980040c480d40f01c43e009104408986032300c0d490321000c0c250383d00603400c00c40b01941e5054051107185407038001e01e410205000421895418580c00003010790f10001d007038031b06200c0b921700b800d810851010382805140804000a60050191107002d604000307a1010542c1c1410200354412030b0303843c0610503903040320603d000810449140c4102503c1a81100308a50f00301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 274261969 1250 274260719 274260731
    0xa030206121b030703050f1006020304061206050d0c03021003090210050f070b011401020d2a0203070f03080a14030f04110604051207050a0f0b091e0d0f11010309020d020f0103 77
    0x89042c0b4014500884090720301042921b812102e00c020210010060380031419a124200211078011007101c042d10840c4c5459060185209611805044c0c141e00086c0c00c5800860a01c081c0300c42c0200410980340300301c070080515004c050089081e0b981d4a5400b03036100000081c101c50700d5005070002e100000080990303d0a00e00c0035110011009800d80c00010503d00302700c0405110340c2e060080c04402c0c19581442070012800141458124620600c6081282c04245400c01955801c000317646c010441a007803405240d840c1d1501c034203d03800110040002c5401148142840440d10381030720311415070035940340f00642d101d44807004040c05910500b9080602040007003402c1e110700700d414000d900404000c000d5103103048140f020300c00300780c0e00140f8205113026003444000300a07802c894030000111903086480007502044011090140700659018401d00310748000c004603852007070811402290207180301a00c0344015030950704410002503004e40603202040061804070140e41c4080c0040c9400280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 274263219 1250 274261969 274262011
    0x7080a0503041e210501110705030405040902060c0703140115060c02010818010603080306090907030201080c0c030d0f051009020307090e100305010e03371d0a0603090b060a03020612 80
    0x54081c0484d611260030310031800001440002d004690510540142c824076000c05034035003d441740103500842d4403c54484426500b5941e480040d6510007095034182d40500d42c1d42e14062002481c401c030340c00c2180d420000100300803680180520112070722525020001c06080d8011659910000d01c01c11301c40002c0030a80780d40d820f003482003001451040042c01e1790b078207001302000608030008242403038580c08a0000e00040c3d034030108c41d5402400300608162200703048400f480c21401382d410030055103494a4100c01e003a10700c07500524001c04004412000d11500e60b1000c1080e440101c0d41200410b42d81c01c1e041000d41f0b51200440d90280004100c00d00d0b407a26a6200303130940700581c403104159030001c19080030000d02051040d004e0310100705000f2185100d0980d5800e0000c040b0002c00078080b04030385948200c94041148020408010206c0540e01d8a40f500600180881b8000303840620385400091080c0c100507003800180c03034005080d141441c6044071718031070a5200404880700140b1165036504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 274264469 1250 274263219 274263239
    0x180a060816050414130b0a240e0a1b14040b0c06071107030209150120060702070f12081c0c05070b0901021c05070905060301030606030507080a0503041e 67
    0x48441c091000101c00b49000c0030402030381c00c00084080e214103100c0600000501364515160401e84c0200458040e6503603540c0c002c000c08a4400c10410703141546640c07810b00e1050413a03141556000d828428060302c543c03d07000100c0350303851100e11030b2b0782081150214190083d00300800025480d5800380c81c10b0340f00c607000b8065421103610b808250b4008014000035903001807406418680403002070025501d0f40d00000c2400a01400351000034889600d88026a485826504828241e54002e140301400c200b800d41d40d0364904036580d20040c064400e001c80d800d40b01001250858074102c41c903c8188c1c0003511440074076406008030301d07202d00c40015070341070310500f9014003000c9281ca41c8816484d0011402c03da092148001c11110042c0d00c100107108051242d042c1e01e45900e000250f00094070341d01c54006464518480d0406035110030007000000402805070018003d40c0c0c03040301030700c000030781d01d05860b50b0361207031014014035941080c0802e0010845186500c65502c60051446a542c0c0e03582c28128 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 274265719 1250 274264469 274264483
    0xc040b040e090705060c0607031805060708040308090c0d02100203190201051e04051b150f0318010c0203071202100501031101030c0203091804060609140405010e0c180a0608 76
    0x706640c440141001003a8805100c81d200a02083da01c032460880300b1048030340c40383d000800762410726995500c1120311515034007100b031140e42c0c40000c44a4904200030083c0c04120201c070110005001540080e09070784010078000c141c010007074500902082981c0c2000a58004803000f601140b0042c80010070103110400886c030031801c660000606410280c2c0d054400c10010144203a00801380c400b07104c002040054581e4484403e00041609411a0000182c003107940e0701c502e0600c0391022032b09848040140004500035030399500c0109049a40d1607140d400d8869191070100560424401d030b0000ca204c0000d0240e1030030300340c8161041101c824510034100c460a07007094903900001c0c0070001203560503100b60210b4800a0000b5803d001d48000001c10311f02101491070790800c000c2020400b0000d16810250140c03d0070071062140d01c4810020140801d0216002c0d2a69800c02e91441d04845010501025140001c1d2040f00c840e5070401c1d403900c2580c0c002e02040c00d4251794500000d0340180a000301c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 274266969 1250 274265719 274265729
    0x6070305090f03060f10230415030203010615090f06021203072c120c0a180e03071a0a020703050306042c0706030f020313020906062502091602150c040b04 68
    0x2441c0c044c100210111b00b04109504141e010481d4107030115804002c5045441d000b22081b40c02190504070011407444289540e88000d400d9070811402041003034400d81e001c0c3c5010010b0307448505a65030340003040000b548a04c211005a00701e0000b21828804d04401540c0c01206800c01d030b003100300c20313144444e2806a400f50842a46034072500d603c8641c913080d8010b0040ca440a0300070035484424000283c007181d04c51042e884030307000c1100d100c0b40c080c0154102e800c500e0810400d6075181c0e0a90308081c02c14502440c0c0c000025481040081d000002038429a1090f0344c260340c03014119507400c01848010086410181b224003090705100110440b500306040c0b4800814010780035a62034a0390213400d545040001c03450a41c010300070020218014a8110540e5404a50001c50780c0c4410010500d140320711101f10081600d4081038041d0006040d2103160300d10b20a403150f41c080d950b218941c1c1444500c00c0c0c030810050b08031740c00c01d4500408054100303410404c07c1807101c0c50580c2e18044d80300f65900035409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 274268219 1250 274266969 274266991
    0x305010302010f172a031303030608030a05031302060c010f0f05010801090213020a0302090604300308130311030a0207050301060503071203030f0f020703052706070305090f0306 78
    0x500c11540d00c100507003081c04090a102400c41c500c030055400601d4020600b03022480c0f03440e18180a03c1c0d03195001c84020004c0400e00340d03a42020070701c09410883c0c1210590100e801e2400020780e118000088981800d0b4075034a0034216150a9040300250341e074a081607034001401c1c084400c800c4070a20a0410001c800c41e40060480701500c180d0702520016031121409034904400b143c09621103240e68070002c46142001640d440c2c180b50194000c1c01003120b1aa005040420081001d000714540e001e04465040300b02e5034204003403080844132417103030140200016019804500f8a964020942951500c2410710100201c0045421442c541108c03c0001c01a80050010040c1d42000c1c17040da4050034055016040c0681092040751800700380e07090040805954010f0300e5481c40080e0301c1400d024100c8030f020741d99101c260078020708541200585059032150580e102c140d60304e41d6280408410005030100d400c1032540c1d101503500d604100141a0007400c41d500208141da405e0040a11501c0a002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 274269469 1250 274268219 274268221
    0xc150c03031d0a080304060207060e15010f0b180312030a090b011514031503070609030b07090303021f110c01020c06150f0f0f03070806060102010c1404090207020a0b03070305 77
    0x2001015240b03a20b81d8111002000103864241020128842c015030781c100300320790f903261160b1400c10002c0c843c6c000054062460a510051a4a400f00b24003140503103200c0480d0071a41c0303500003028040020310801c0b040d01000c209102901d50300140799100c20300020241c034098a04007105000c5603204032140c2010300d41d140c0c8408100100f6a004034058290381e143c0e40102c2600c054054403810501900b141400d0020000034494404800082d040c0788015040d54043c5540f07842c058580760f1140421540c44007407000042002c1d01c1000f500003100c0d09a07005241340c541548a03a0007000890004c1030340b82d901d03504186403409900008002d0000c0c1c060006030780384803402207a070a09502030084149560001011000ca944101c0c101954040840e00c4000c00c815000c002003d00c001500181c1c5c05010300000080d41b00310105015124000030b80003444010f0101c41c3c111a0f40303028001e041068101403000740924031469000d080160701c040e2424810341e41310b0041e46801c0c0c100f1104030340041d444030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 274270719 1250 274269469 274269473
    0x6070f0c3e10030216050703050a020f0414040b0a02040515090a0807120213060e070c020316030309090509010e0703120323070f030213080601080c060c060f040c150c 73
    0x564a102440000c0c1c000c1420580a8400030b07207a41464100041050707004552002040603400c5d8990007070740d22408980501d0b68130701d48030392078107522501a0710605800754072407880c1c246070080b05461a00f060320325100d69104ea5410410080140c91224915428040444c4a40300c0c100c100340302c041c4c1ca80c0d003581c0b5100f409003000b94200442e040102c468110160400c01d220000200012080c1c0c12a52040c0340036540788000003d02e8107500124074030000c24288541c0380d40124010300154000d9050b664004040718051404554511008001031402c400400030207415600c19508550341000200d0301d60800b04030305144c44900d420a80c1d00c2a8402c50607074440d40c2500c01d1032649022207403c140006000450401050801400f010912103050038004280e03106c0c0d4110b0310804070709a85c603041a615080c92954a0303209015505451003018054032251400304107540004003841c00818803540d0b2009451440c60300a4801c4640000422002c162003c059851503050b0f862070740e4a6114030024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 274271969 1250 274270719 274270793
    0x1b101d010c0905010903200a060e2d04180203070e090d02060103030c1b05040204080304031401020f1b070b2b1505101e030902010206070801050306070f0c 68
    0x1c9112001404090202000540d0700306500c9012a80c104020194401c8000c3e0881e502103503511034540c0c1f00100143c00b1640d10b030000c1030011070400680d04810803003104c24800800400b40c40c542c41114901c06030552640c0b806030041000d888400d0f0048227912501d0f80882c1c5005100d40200315102e00c1c0034104040d041040220f0411058244000d0115502d035441c00340400c6111880548500c145140c410103c9400030303009030080001400840da1075513500c05598498100e40821680722500000c4041c0c0e0f10014000e80e401031103905007031450a04010500000784010b281c11045038044c000c000610942c0f084003074003003e00e01d0303090902e2402c0351805000a206040c14148210781c074120508015404000c0100c050ba00e05480f80c80905212103420340740c1c198a6014400000962004a00b817a80e041d000661264400e0302154041c0e104c1080965151a090007000d8041c0d1013880001c1c040b61050942d418041c5090600064a800342d4403640307850b0318540e1408a024500f10001c108030130103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 274273219 1250 274271969 274271981
    0x90207050a12030c0c080708090306010306020d0c03090206040b03131401061401110a030302090102031e131703030f0604020c060901060317121504060512071805010302061b101d01 79
    0xc1d43c5400c214001c500c81c005000c0700764202001d840d40c81c2c00300d000001c015081d400c40b404194014216070702d41d0303903924080019600160390f00b4400e81c1049600020140680182d440b02580200018103103810881805100c2d000201000050a260200781c00414041c11601c040005510000300c1c005092a8405000c0c0e1404004141008450940e5042085021821600f9293f0500c1c0141e541c590380c2d40100e00d50300400707880c104101004941e15041c84080340040041c5240301e418020030503500c00940d189602d0319403450942d5041040010b54038420a08a20740c4608020300060508401c00101c51501d42d04403075006450313642c0c0c6000d0051140d491a030340c050380c1624001c00e241211301e80845102c0c0c0c2000e02141007070807050100c29869542c2d500704102a1401800049520010307011450f550070b60303403244410034007960010001e07100060040a043c0c2c3d13000b0308050302d0100c00380b00f00c1c82c84100c0c2c01d000142901030400041c9821810340514000e59459441d85d8904405072a1000e0850344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 274274469 1250 274273219 274273253
    0x2702071208041b0522060b0a02030414030609030409050406060f03060b01110c030706030915020a050406030509070609121113090302120306031207081309060602010b0d110d020604090207050a 84
    0x107103c8000c000039500c40060a8405900d8131317010f20400400010a0b0181440390800729403108040740603070001d640000504211500d100c442526222079409047d203440003070350b00b0402038100700001d10448625410040e0054410003000803400d6884444070142495504100c0700941c540d41d8003002c40d03078058440451149900301034120350990320002075481c0c05500c107000c28140c40d4401c0c601842004103a0031390740c0c00d03c55019503580c1c2c05642d008016074014080da10101c2d01d03210110354a150b00082d281d0944640b901c501d80c40c241014240c0c0b01e00014884200d818903611400030f0040d0301c406038040341b241901840842c0011017450042e0802011350b583d010340a2040c010006199030006003000200c40c1034558681c2c0d6141da041c100001c0c440c070f0380580d1001054002c000b4200303000740c0c026411104294020007100100508001c8140101113014142102c2c2c0500303144246003019a11050602c02069907240581d03565820040e80c02800003a1a40d0700301e05500001d0011096000403115 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 274275719 1250 274274469 274274513
    0x1e080d09061b081510020f030a0809060108030406020a0b19291504171204060905090106020303040b0606030705090319031b051923060103031206270207120804 70
    0x12030244d0b010726142030113031030281c130a1481c0160781c0100c50003441501d0031900f1003400c0d20394074015030703802400184041c0d604120b50310401c070002446100110540701610760300c1c1c1c041c00c100e0189403100c00c04524040c040303ea50308014010440958182c5c411181a980d107800904040e51110103814100326a03840c0090007000c0e403400001071424664221025602140085c1603030f00340b14200c083c5070812012825500d0a40010003050319138000c40c1050846000301c407954002d030380b504022a1240002ea900604079a40000407400c14500354001d96440300c21450068140a11040080e103421520700329182c1240c1042d15100c10306038040e4000c2051162803400c02443c20305641c800366038080c020140c09010a5004410701008179017032031008101d4164a004404100c00202103845500a02c03003200131944903050081154464050340c400c031480600c000481c0685440206c64038a10203500d461696030801045002583e030499040440c607250b0fa52601a1130107143c10b4100c4090800300803685 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 274276969 1250 274275719 274275721
    0xa140a0b0d150b0a0e01151106070e060910091e03030f12020d0207050c030f0c1e03010905011410050f061b01060305011a0405131e080d09061b08 64
    0x90703107404104480c02540701c400105000c12020454000b01002030140f036002e00420000100502c1c0d824455050b601c96203900d20801080c454180e0f41d04003804604052500b20b0b42c0001ca055000300100781c018007002d020f241c50526030b440028090080c5003100c2c40858040c0500b40301400c9481e03201314801c003030311800b04001c0e421a14094455000c11030440f04200307026002000994450701680c206008680c1c065440e10f110389046074441251b80c00d051301901c00d1060100601900051100c102100504400345000c0d40340702e00e104074440020110341540d00c070361020000070424803030030103d0040101000c5050401c071281840c02c051940c0910700c0341d00410030000080d1340d88011100c86040c4c05000c0900d0340c031242c00c0341e80508003550028169519003070080e6035800556840359405441180c0800c50703aa21007a981c0d92081c241100500640c0c1035031b2000700e44210102410a2060040c0c040504101c1d4005414080d00e0380d882c001c80e46151a0050500490720640301c0000b00103103410142c10f2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 274278219 1250 274276969 274276991
    0xa0b01080627010b030a03050d140103020a051c080c0a0201090e22030c14160b0310030206070f06110405101b06021804050c03061005030f040201080a0b090a140a 71
    0x1203000000c51070301c1881c090741d10142d4592800d6102c80f841c400090240c0b240c1c9012803c000d041500400c4844404608100e034440468501e495014140c0303500810b83c1012038100030500844020107018030800d035841d0015800441c03804005842050020300040403100c0b59403000400c9200b0541c03004000c00303200c40a001107002d071001503504600220000d51005055403c040b03038200c074458006403182c05065810b546a17a8041405046840080c420407102a65040715440d10b201c100c0b480f89002211100078070051030160004c0030080c2c041e04850202034403a42b20700c0c04480d444040503400c00b000040400060805005403070740c110140c1800002036603485526100c591038030a00a000550000740365000f40e520b01e0041c2c154603409441008545403008607105554801d8801d68421408542c40020480c858811a8420170603440360309a40e4480b5401582d4200016244141d110303102e010060554403103201d02845001c1082005c28001d00c1c040307041000d244080c00d8241d290f420090f040d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 274279469 1250 274278219 274278241
    0x70606060824010507061e1b0507020d02041409030a020d030c021c110d020601030c0b0a02101a120303040201080702010605010e01080a0b0a03051b0d02010e0f040902040e0a0b010806 80
    0x1c640c0700e00060000602c40800048849128040008000515102488807103039a03d04034203d03c10302050040005280716005141c42c403090f00002000910100b10f00d000505210b4614503495201030320109079600d004410841040e02110a80c03101e505c0031030840386003941045840e440a007941020042c145507500025200c1e140c140f0412040f1000f01d40c4a001c0754801c4a46200c00c0340403006449400c00c1943e002511554203200c1641da40d80c2c03401c4082501c0711044101d079035600080d00180104514003940c1d602a000c00100300d141e030f403c0749c61450b401c1c0c1c950900522215919101565491801344005840f45070050200011685400001e2109982062020301459002d0800c4c81c00c43e600d003107051000c0c200800000e0b4024030000400800c06c000003400c0b18080d00b00e5402541c5841c050014020005003116005c2e00240e0450103461442c00c05032014498031001030b10106000ca215000303e81503ea03418104400c03503022606290034800c0b091170560150814601418060500340c514003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 274280575 1106 274279469 274279501
    0xc0a020a0807290901110f010c2f03030a021819030b0f070c030302070204381203090402131208030115030912051c110706060608 57
    0xa440d00b02d8180f107080a0000b0110a09102100f0300444050342c1c0310300550030340d0150100d000040f4901b030068402d02c144545850b1030841092108484080c0305004820008514240010b0800700120031a904403441c088091b86602070094000700341c1c486100340c564081c8826108054141305c288192007203c2c041c6040d41419a248600e18850038811154540028400700795000064060347c0542001800604001040c90582841c0114100421407550365802030004000404940000d407645020b0241d81607482031014010260343c900074141c007280300c0d0340c0114540e031044880004030001003001c00403514040c64503051039001e641c4280286001e070b884141e8007600b094040d0203580c030607507070041154039299901d2104541e42d8101d090001005003030040000f11101583c0540a40210001c3c01030369600d545103424400c903961035005409124841c0100084035901c02529 = true := by decide +kernel

theorem cover : BRFrame.Cov 274100719 274280575 := by
  have h0 := BRFrame.cov_init 274100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 274100719 ≤ n) (h2 : n < 274280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
