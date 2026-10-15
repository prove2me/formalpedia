-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4526
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:54:00.11782+00:00
-- url     : https://prove2.me/submissions/50499e80-ef46-4382-aa57-dd5c33c4f7be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 813848920 ≤ n < 814028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 813850170 1250 813848920 813848927
    0x414010c200a081e07061506080703020301140114070c0b0c1615031107050307050d0f08091c030e1209030706141e0417010c090819200a030b07 63
    0x101c0c042000c9035801802501c0c0421034000072506086981d080400702c00c02003408000940c82010380080017980303000f102d0401c803006452984241c0301d150303440d05220341343c019080f410f03130100380507400014441c2e5109104560250341d80c0e0854611700c0d59803500b00780658460b030350080c80540c07000519400c00174920500007000d202c000d82140c10301e80403003440c82c2400044049200380414850500d039903020003c01e12154032007603448203270340700d0220380e0b0394802c40c41d0544c0c0340d03d81301700c4070004110a0058401c5284c0100c8185102c1c05d00340004000341c1e0185d0181207003421102181d541850f60b140115401c5040a01c90100d4500d451076030b407541c0e14010350a0600c1c0908a40c0840c0800c155850219800c0f0740e0002240c910725421152030040d92100700d00c80c5054400c82c1e02c4007008820140070581208011340261407040301e00d85661051710307a6001d106803980b09444001d0315480b00c8114050020704041c8021861000b0103603903030346440f01240172503ca609031713820a03601070311000d0410640c60b52 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 813851420 1250 813850170 813850217
    0x6090907080c060306030307020a0f14060c0d030515030a030c0c1a04060e0307050a060305040203060f15060304060e0601182f09040b1e150f0306090414010c 69
    0x650a004081440ca04030016444a4400140c28821140040030424a9500300b003900ca0640e0000c10707000b800d0b40c0e00c900c0521180c500c1e101d81c60b8000c0700f15643e600145403107026601108c8465010380382415503518120002c2074003c011840d21100405010a151420041e204015220351200a0035070b003542403400c030318005544510504c0d9006d4684030702c0d021003401540c088425604210280c541c443d40001e0425240d0340116400c403584410005a255254108600880c000d03010380f00726842c0c40d41e11108055040360512000b42e107468810490382403210003545d01c10300131800000c1490701400400c0c2403d8080c3e104103002c820710f41108200101600c035400c03425040c03900c9006030344004510310309000c844100c0320036407010124140340c10362500e030441c84c04c0e103000a0000140c81040f618074132403a1132191000d800380130795000c01c65010810004484025030882d611a0942e5030f048104062428001e2003194802240001c921402100340a08841202540c594a1182c03010034405448141c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 813852670 1250 813851420 813851431
    0x201021c0515010f1103030a0b0f01021209060d06030f0602071b05130203070203090a1701060f12020913060905010f050f0f01030305091203161208010e0a0b010e03150609 75
    0x6103444140b00c800711006140c42c040350350a0034000244030304200140c80020040b09101980d0200008020545810350702911110b0340848031039020403d8030340120380c1c44503400b080141c0c2d05020000304c2d0651604030b0240c1108488850b02044a42d00c0ba61a44141064600100d44450700460110300f001100e0764804150182c15000110b2240b0300000582e43c800382e8800c12040c594000040f03100300c0e2080c4100e031200000a840b80305041c4c2e0760350f02d80072070402d80d140c0c1515a5103401d0000c1b86207115080400100d40001600c2c1c203d60400f1b40800030b95174000b9001140ca0402d0424050000380c690251010703141c0114000590030500c4241403090360740c005c002d0700c02450071204200040310f2010500c0d0540c0d405203045030711490801c0c00706a550b91604d0142c03010b44004249141e83c02200d90001c035070a03102e006050f907050b0121380c040c0e484400c02e00640d00700001180000c0c110040d00c0d4171928901c003052400241d6140803e001c07904050800d46090f80616008040080d2801d0440303120b81c010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 813853920 1250 813852670 813852727
    0x120c060c031201270510170f0d050a05030103060b060c070f1a04060813170f0d110702030709050c0f0d050403020c1203070303420b0a05070b0a09050d020102 69
    0x81483c5188004445098002d0310410703917071080402e03004148841c00401500e0035402c155030310040342d00c2d016640d424002d440301041c4210701c030307444003284108186c410620447d00d40601f540d08564458020b030000c060a42e4000b2014040041c0c10003080010b08001c0604140a82c842c0d4105100c20052449020710500f142004201c1080380310b6000e00f21075848107580081c0404009549400306009842b01500d000703240300841c1556040614600030500384058150801c69040610005a0540546140a0350541041c042000002a141c10090344134400c05095441c0450305d0318484800d400070340052039041d580f10208810140c0411580352a0030045450900003411100419034900c2411001420141c9416814004110b880845100c62000c5202d42c130000c01108409007400c0003039002880404440e030380001e150320013007003211058142070740c0d200e2610280307031140c02c4240000f03040a8906941c1e01c1d108008550140301844105210313a0016175542c0101e0394041114960b40720f01030340c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 813855170 1250 813853920 813853949
    0x807050306060904030c140303070e1206090604080a0311070807030f1403010b070c0503030c0d08070c05031b0c040f050907090605030c042c0c0108130b0105120c060c031201 76
    0x42c2d0b6514801c269200c0d60603d0a801e010205242c0300103104101c001e2440c40b0b100110901054641041500c055074900f070700e040b6020303041c448070a684e8030b41c10344920040f0703040781c0040341c0843c44040c0181801030312403c011515800341d00707154182e5030000500b0755400c0e41c007041007001c02d94490000c689a00413490101c03c254490b610044440c0300601c1410034078000010018100000010301d4401001c2c0141625104c281080380d82d5103a205c0b40004000042c50711001886c0c0034020880c04a140350032070025030610314070404103d28801c4648c400055440b512045038034070b5030385001e1000b00c014070b9040801c880c28041d0b640b030301e02000741d00708081c01400e10701c0a00c4070b6100050b480d003040008441c0401c00012004e0004541000c0b40e11509002111141303c2c10110000070704500b5200007a60b510310303180e4555000464004201d0401410420b400d8010000b0f4a450410840d40c0b401070800e441c4003940803c00662158495a9015269000841d0405c003810202600500400c6404119040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 813856420 1250 813855170 813855181
    0xf0a0506090c090d051615020a0b0c07020d051009060b01090b071b030f06020301050f0f031e03130e06030105090a05061308070c09021803070807030f1406010605040807050306 77
    0x10080070041c501c0345510408030b41c0e4842950741c01c003007015494102c0150b60039041c0c0c159480c130b0101154003d0b409540f2007064000521031000403100350300c94005c0307001d0103903885800d0306042c5a80070003c16a0302040201403000410028842c00443c3c80d40d09174001800300c8107213002010758412100349814815590410000403046404449034603070b0201008407400200d80c0800c924850613017000c3c1003a00140d20050801c0744079030045048e1101152018a503400d02e100b000760603511401d0441d0550003509801d40c50051201c0090340741c04680c0b0650741460301380d0704031601601e0141d0101d1039407564442803125504082c80b03030a070002c8500700500308095450300c85565132103005d080c070744140510319400303030034000000d00303440c038903a409a5810040b0b030351204406c1c0039411441b0083e4007402001c0d003030049031800144a0302200c0d4140f0180c0300c0a451031b250310100c06a600300598921002c0701c104000380209102c184c0c081c107505e445d41501c0c1c1741844007461410f0141c0c0c00c514000d0344000107010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 813857670 1250 813856420 813856429
    0x2f0318010815040f20040911040b0d09060e0d0c062304080c030702040c030e0c2b05010209271b0306060a1808011e090f0b0603150f0f0a0506 62
    0x210000b094401083c010703084c0580c0e00082940021300b030112200d584031801c0c421110001401101c4420005002100c02d640c1201c0881c03049105810486004000030100300e503e68100c020524041c01e80003500302c002180060500c03030141400da00046075084101c6c1004410b125228000c500000344501c800810010b00070003500c0034001030424940824080201842003003240d102c5513019200b1f2102e1003101802038003030a80100010414010040c5110321401c201c0300c507840070200f5118000e1050019405082c0091000c1029a0655000c100c0f2482e00e464220784c00d400c17071498000b40c44c400e00c5040b41e00101c03644081c0ca9003980d03100c1402040900700d411001d480c0c112804890040c0c0c1c03814844400e541c41c03024001012203911401000042c4004191b00c03401d01c41c1c0c00c043c1c2c00100d8603d81d00026084034481c0800502c010420074001c00072412a00e8007a6108102500719507586010b011180a82642152050110711405c01004601d00d140481550840307800c00061095050020008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 813858920 1250 813857670 813857701
    0x14120a05010f0b0c301c0b0609012120040e0c1c0507200c0a090b011209080c070806090d05072301060b0a03200a050a2f03180108 57
    0x200c041405c100203035821540006584543c00d205540c41660311405410381410074002029600c4800d0300c0c0c00400c1e8000d08050303040740c0240754165100d02100c1d201c2e2062623901041c0555158229550380d900b520b0400f5904541c41c4091280700303906403141d280200010703105034000c01010309070341c040c0030b09545045004071072182080c50081c00320b415516010215021005040425a281500340700e100c08998003103244040585c081c0d446154840c0ca400d500c600303441c0004400b50000d8841e04584500c070743c855021804652060160034a840809a101450850b41d9000312801e908500140588903408010f520483c0720113050841c2404c42a4490100380b05295200d0740100d902c60f44c400e031000c6000c3d80600c014020503038007a80c8807604170318014000d04038210074000030307212040020f61444070b2205030b880149482e51028a80744413010111040460201c079590340f40307002c1c03480b5512141e11400da58001402a80116221000707085050490000020480d0500c2108414400c05698803902d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 813860170 1250 813858920 813858943
    0x213030f1e031713061d1204052124070207090912120906022209051b0f0706061503230109021803010c0c0b010801051614120a05010f0b0c 61
    0x500c00380e90b42c003001c602480d410124010b100510b881440c0e08406d4122001c00440c0d0421800c8442074200c81000e401540329501070140d20409042c283c0d841c01000b60203050041e21440b0607911080c2c1d2102030307102e070744421101c4c84800c1401c800400842130340c10880b1034028039002800780b156001d241c445207500c0703003181846070030410400c7d40d0300303007210181d04030385032003640210b003155205d0040310078080e240f40b400454076030342c004014000340b054428024030303000d44080c05400202081710401043e4a6101070195041c02606005d100017190151143c20300900c6001000e0b6040c1c211040d004084513044084642595041c44410846044903912541540d9084500603074a00b035a1088101c80241240da01c0c1d459800c1410519076a6805490982c0340e43c810000d03034409980300c017002c9003a00c0c1c04489504180910803110082c0510404a20070400c2294a485103021450250340140329000c4070018492a1240010000c803440f15540d0070007071114103001400d120341c81500c16181d202184c02e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 813861420 1250 813860170 813860207
    0x30f020313091a130b01020705030615010e0d06050114090105180c0a21060602010b03070608040b060a0e091c030c051803031303050c100f0509130213030f1e03 70
    0x1c00510020340040c0319030f1408002d040a01c8200d0300b07013040014100f50414180140122100040e0b1030500184603401129009542d207410701f0386500440d1020486030900b54010001005000400c62610400d4040c208010040140b03000080600801c030806a2110340944255540340d0411002d030b0014642200a58020359036810b51000116600b01244181030219000d12541c0b0001410325440042140c649400031310941c130a070020543c50701028802c0e40d0100e91a44001000038002d8078603d030780808001d0003070790300707689603d198072003282d00b1104024942c3c00300c072070501103821501c521040da404a01c0c040c0142d8000c20300040c0b00e07001d80700034040840da82800340b150550701401940c5283d00c0c03a44280303d10703550b6400c01c3c69039450410907060080c04043c1011044912a910912103c811502c900b0700c1d0180c0d440a20001080d02400c11102c990b080c40a0345143c00030100c082c00540c020700707040e44454500c0c00e180c42d00074521040444030040500f01c03040023a03001104050301c81c41c82103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 813862670 1250 813861420 813861431
    0x207210201080f1801020c0709140103020d08161a0405210406080415051303030e190809031509030405130e07060c14030706060e06010f021f1b0309030f02031309 71
    0x4c03042404000040740300b42294000314140302183c800040c000200c1da07a200303050081d50403113490070340c1d2481e0030700010750000114083c0d6000300e0b2440c0d00905110500e00007014888406850300390025100004c601d500d24445000d10090010400c080f100c00f010300480340d80110384c08240c01c0d40f103200d030788a20000d0082100020b014424074224940324000b6083c4180034034a461101c0310030303c41e4182c40407004a89080007007280d5410006101602041d8414000d1010f1104c4d1520056604000f100b80d5251041200000040002c00071283c000d4404800840d2134609203c00c0042480c0000c0b01c5829051070000b910103007500028a84007203038100d040140d5012030358280a04181c0c20105501510f200c006a0303007081140783da01c080102d8142101000498403150011280709562210b000016449904042040c92068440640b4501101c20014104502d51010483d2841c20103a94001c680e60f141c1020138540c002c288101c0b250f42c58806985480304000e100c0300701e04041e00803a0002980c66 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 813863920 1250 813862670 813862681
    0x15031104171c0503060306010f080604061d01060612180b0c09060f040e180109030903080d0b04051303030501050d03020a06090c26010b030a0305091516030207210201080f 75
    0x144800d02c6805140d4414403200310b00242c01405690055840a02a104481c00000d40c0380c3c0b03050305001079499020140400d5162612900043c0280d4811540d4105011004a032452400d00ca65801044983c5608943c8520404160121408494019050721403ca0580002807882030900d038031004020096468901c0080455513500030f1100c40107000078005000b0034040401c1d01c0003481584c034240130700c64900100860509039180300c2001004911024000e10001701100003502e0414004540000d04200c0040050180c3d42d0940b0120103880d011300d036050525a160141a0143c14142c0d40ca5140c2e10030340d90000c2d600e04082a000d4099a0350b00d4440c0200224201002c005000303200c1e0501040000030480c00c12640e0b040750700d0031150710304100f0408070b080100d124214107403d6126141804202c600707201207040b9a10414202003c1001541100d541400704a55884d01030750090004a04040c07180308503110080c04400e0b1210315640c2d060050f17a100d0390b480d81c04130000c00010f00c1500e48 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 813865170 1250 813863920 813863923
    0x6040b07020a0c09140105010c110103090809060403060501030c081c08090316030e032b0e03250801110717070c0f09020c01140601020c01080408041a041503110417 72
    0x140c1401044050f030400d0004034481c154100c1d661a1880180300b46a91366a1001928808240f1400070300f010101d18044c60301f50301036408000058002c1012a1904074032200045980d44143c0003190712075a80c0005000707205084116802901d003410061104134451421101e410000e0300d4110204105c0c41e0020302d0b440014030a5942040004514400810003440d000d44a48030741491940a84601c0d121042e05d4280f0000340c4900c0d2843c480e442c011100c11a0084910501180c0725039018810380030002c40c20000e20416190301e0300c100316070302003285c200b0912600b580c0c0780c48444201c20b039040c0004004500101d03100000603e80c01450303581d600c071a107031400a0b00401d60202c00a40222580060b44c403e1a40040c0100c5138690020030501c40c3d00380d403aa11410054821500590010b907035001154007901c03c0c0c54000f40645c26031030030941c0d02c189554026030a01d00807503040901007401c0049801c0540382c07110f48007d9060070700c40d0343d407800b1000280d40100c0c40b031400340181300301320252000d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 813866420 1250 813865170 813865183
    0x12a080310140a051509030a1721010e010b090f03100c120519090507120305040311040b0d11011209050c0a06090e07030f061701060608070c0506040b0702 68
    0x5110004640300c0c5455401e1240d01c180510075500c1c6045012890b0381c1c0d03860b220729200c00b501e20080805a5001000c6824003031a00400d07021390b0548505200c402c0422080500c0c40792030301e1125001595400842c4e002110185d0b0041c000040d013058074018060084802030107419541e40320300760b9860701c09050000c1c0310040790040310342e018043c3c03401c991401d04480d0818130f100701607130f1648801c00c00701d162010301b2101d044442d00032090f41176409103002c1074260040f88800380a0011104a1515070f00910441400c240c2c0480118400180800401c1003500030f101c0f545400702c408000f54140032000c41d080c0c07280100f0050904100001c01451a0b003c0c230341d50152076120b14410840c810f01441d20603900c3c03089c510f55030f00c40c2580b8840054000d1107041c85030140d405041c03411100340c541d91310950290413107950702c504180d2118008502d0035100d00c0d60510620403a000460040e00e030550107030202d030f4083d1880c4204001324681c0740118000089040e0407981c0704903039030341903a180081242440c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 813867670 1250 813866420 813866423
    0x3040905250e04060f14100329031c1b0302030d0f020c100c0c0b04020d08031e0a020c0318040609090803180303040f11011107080313080c012a 63
    0x48401620541d0320402c1514180020b541c10490740c0d46510302101000400d2040d240d100c007400e000340c2e0803070030300031070010614005040100c0d8041d0581a94039401da22084122803003054141e146100341390401108940c052000c410161090800c1401041c0c079102c10011802c0e40510684d0904151080048403100d40c00000c0402015224070300c5c07200a5404000c400f0100d210742c280d110413680b07146c4614085c5691940b02c032a500d0f002903403141e06110004100741d9001c1c0e1307041a120081905a07001314410600b01146805d0403820460880803504060018029075106028804a9201c0042152405080d040720100c522400400081c080c146940000c80c4280c1451003c208022514020b1030196070244213a00304821317807280356540c0780411280a04a0f0780c85021507004500c07200d10040900340f06140c040f01d2030f00011140d030710b414659403000625900014a03005140009400000904103d401520400b00745000090102090300b5440045100c2542c0e4001650403000d610800d40303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 813868920 1250 813867670 813867721
    0x1b0f05210106020c01031103090601031e02370f05040f020d0903020d17061807031b020615060702060a0f0207030f260313140f010e0a0515010803040905 67
    0x3580c40b10750007904da1107130220035400b0074102420b6040c40d160710815240301d4205d007002490b45a103540c480402c0780110101000c0342d4402d481c20b040144e183c004d42c3c00f80381d12041020011220204089a10740d0134050810070100c1080b00c0e05220708041070030004121102102c02044000690600b030000344511081c12440c0d07480c18841c1003c00d5004542c48042c09000d849040c0084074020f00580c00c514111041544050130104210b80d43c503440c04203a800c150341d498005048100c0c60000c40381d085800d082040540d1245042281c01810558602141141640c91508100f620390100e40c00b17008001d000f805100b50380700403c4140b8803c0240301c00664220852610341081414443d20004000c100c85500e07510880213900c0144030035080724043c0c4400d45104910b005aa02ca002c481130511074030b00c2e4070780104148409007440c02d0203191029800c00014000789201d44c58a145130040d542c0010b0344c00b9140381c004206d80403000c400d40f0101c0d000c450b0085250768421075002480424195421100e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 813870170 1250 813868920 813868987
    0xd032c03070e04021002030a120f0b0402120405060601051e03060f27060a08030d0b2107170d0906140906030711060a270f020a12061b0f05 61
    0x1280d0102030043c0958000d58007150302d1165903000700c1c4c59100d0012910045015248051081c2c060b84c0d201c0444072079100300009a00400c4400036003a640a00983d0722020603035414441404000d21000f03402030400d0814a10b000540d41d43c966181e0040464041842000b00c001141034032400d000040d800402002000e00c03200b0340c440781c00c1100c0500e00f034662801c0d0000000f1524142808000c041d220001f000794103000c0c04580603c054011b5401c142d801c060815204140c02c20b00403207840704901c0000140c00c0983c141100072020140340200304a032544044416040c06802c948120251034052400c035404400e4060590354500c280e01d003658010707500000b04280300d680030b0700c2440c0400c20706055036202c0d16007000020039a100d8600501400004050360186440307000050003045200c1c68004900721b0311078000585454546d4005c0001a034040b80d46010408103100b40303a0268001d4524980300c409520380205201c0700e40440c0030034403c00003401141c007602c0301c0716480100d43c2034003060b07417 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 813871420 1250 813870170 813870179
    0xc0405041b020610030312200406050409050603191b12030e01020613020919110d05100b1206100e0d05010e070e1506090a0b03040f020a050d032c0307 66
    0x46907501c500c0e8018010140840c9985552036820011603400d561150508082d0b01142e01c020100095480c40d0f069444403032050900145010300300600c450b03100d0135102c1d4a000c88036020780f10300501162003500456404511001500c1100c00040d8201422035106070032039584c0c183ca40b0b03598116800d946000c1000c2c00c201039008a80035591107007030b4252a036584458280d003640d0135015030000e510560071400510b2030441ea802c08042170b4001c840200d440562620f0703009103070388804103040107180c0364010881d61072550034807a0014811a800303180b4081140210415400700a84000e04c0351104010280181e8842c0803603101000c1d004026031401c3e10b02c1e1800d64000c013404248807440f40902e0400083c5800302c030400a101f00c4c807010146010003100e00411040307511011003507901103001040424415042c501440c030035445010100040c5400e80100102d000e034a500452180c800e041050000075070022101c04c070308446000b500c124540c400c1c0700700c41d5503848908043c0c05d407080ca240040c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 813872670 1250 813871420 813871451
    0xa080a050c011119110a0605130c12060c1b0206030a0f02120a05060f011b0317070206091219200102270414040b04030c1211010609020310050402030c040504 69
    0x14044210990304005800c00001941c1400b071700001000b680c0c0005001c4000b19219070000c560002c0d442035041d8204c01c1035540c551100380720f138002c52a581d0501260b0010041144a50a8001c046041a170040181c2c020b541001c0729100c0f400074000c1130302001050202e0a50340005a00a161800554443c0d041c0d030500c0001c030604070344c0540c0c42c1e420500428400c1c00c01804d02112403806a540c0711080c5c1c141c054202803c281043d080b004c1200242410811040300400c041c01040c0315800b41400b030070040c400d02c4c50420b800c0b00d00f40411070100000f1220100e071520000030842c1600340400c922004080b01419001900e039214915400000c03c2950155001d00071460004009940708880c8508824081155000682d039141005400c0104012a01c030202c656403084c440d01c1c02d44005c0b0102d0f9540d01e403103444605450b0126032113a070120f004034070078007442014001081e02141075107040d05c1c00740d07015840da209a501907079000000c21002951a0102d40c05044090410300a03000da0341201c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 813873920 1250 813872670 813872677
    0x306043c1401061806030536120c0d020c010519120c02030405090f01030b0c1b03070c03120c1e08130b0a230702010e01020a120207050316080a080a050c0111 69
    0x80724103031140742001c280c1078007d106076405450b00421004003050700f10750145440380702c441d05240304142c45c04883c00d032030002c000c80d514a0040c0d800d45601c034019000380518015030550f140341550011a03040050303076400401e480d500080ca58281811200c40101510b65041c1902d2201d0854201005088942e400200400864100b56004481a901d44220100c0e0032000c3c000100010006c030089030707444841c01c02038400c1c5d05103580003043c54000300c11002d2840e440811704682410460300108140b01910074002c210035202d081a1061803917558540300034102c4541d080c0e0300d840090402c40c040c0300c042e805580c8001065400c0c408040c0d100c80901c030303041d041481076030005501130110307003501070181c0400886c900340035400c10b04100140d4015140f030b2100c420950b0445c440e282000011910100c1c12200d10743c2a500600b40392400c2c41c00b1b16040040c3c07450808410480c3c1002000000000145140d515400c946041c0d1140300000c4101e8062181407a90503140d801d0071a24460300404c034008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 813875170 1250 813873920 813873947
    0x11e1110060b040306050712180b060609101d0a09050604060515070809010c05010c0c021f02190203120c010506040b04060b1b210306043c140106 64
    0x40340c1485200e0112842038903814041c107010100c00348003c100045941d04150340041c141d05041c1c070500c06145a280c00c8030800c40c1c540c002034044c500c5090910842e8010550000f4064450070720340341c80c62001c618001c291403c654104010a001202038140c43da5000c0707142c1000610b80e40c0300541d1040d00001400059444511462a0042c000341929040600142c20411015441c0c142501901c0c0d8403015000011600d051064011038800000c20a1044c880003044a03100c412900c2c0c198014084280380f5a0241400c08070354a501000f8a900001e08c00c00c05400405050001c001314800303c0d050180ca0300d029040b181001c540302d6040c0c641034010300d106103415502006041c540e0b1040009841c801c0c0308050582c00200305130281400c1c0350300382440e00c0c2e2560040b182c401000c458000410003a0003580804460040144050351805000e22482031807400d16080345d420303d00c0c3d41910100d28005e403090207424031a01138000c00410750048484400103040072055507079641005020340b20044c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 813876420 1250 813875170 813875173
    0x90b09060f0f04140c101715130203090a080310031403120c090a0305060a0204180507021518011d16060e0402070201030e101e0606080c09011e11 64
    0x281c5200409050a104040d001c01c10645a00c80e03440300e0301e140c0101107041504e4010070078206000d407100048402d4034800d940c2d40c10f01b14560200c3c10141108090000356240155a00c0c80304907030b44640c000728150240e031000599035101e062015241490030a001001000d0110401c00700c031103906410f50481c0d0117020100910075081c000300b41c0341e105043c00941406000700210700c010301c1c06c0b00940f110034005481101059225150140342510407100020034540003e4140205011846050320f110205c000c2401142800c810103500d030440c0b0410070310384c00d0107000043c2c40310741142c800400001c0610003c00600040c5100c880702015064a4140140714042103540c4c120074400c03002d000c44420307070f5600520603551020440a50300c03160342070f41050b45a2001204c1081c1c107110360a1041c0040c00c00281d07188190b40034009000b40d08101107592032504000300080d131782000c49641e114824000190b0b580240c40010b0318048452505031000c0f071100701c0260001da402c003071000c032001c1c00c80c0b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 813877670 1250 813876420 813876433
    0x70b0421030b0102070611150f150301060e0105100513060f1709150709091e0c17060405100306091a060a03170c0c1504030b010905060f22090b09 64
    0x48054041e5910010010f005074442c1c44204401807003100201c034088107420540307014008444841140c0c1000741c820f410716442c40700901c4105c01600484000d1034074190300134406285811909502402c05207d0b0134003580d40f0710882440144103108413a44a111500700b186516200d1000078a0707250002c2005000c905002c1000601e80f0307014200b1031060b501c00c2e00030040d00d40481686c45003244050704803414040100c40104840300c0900a0800d0a001a050fa03906021220040d1040c3d481c050b02c0034003400348c40b007a443c00721502205507603805407051740c000ca281e4448440190450486a1014101914096a034020081c881101c00c541440c0e03005005078070b032100703020481c9502c0c0510008051006c41c0407100010000301010781500050320007660b40b10032030340000c113000c2010b141c0e6880403150002414010000091501c42c09000c00034820850703440c240e4045010041b03100301c481d205080d1132044000d45082c4007000010380800000034031180543e071038492500302058880000078051b00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 813878920 1250 813877670 813877733
    0xc08070306050c040b07140c040e06100510020d08041a010e04170a02071e030c0f0305010c030c0807050c1c031416050901110c03030f1804091104020d02070b04 70
    0x502960145c8051020292034441e095549048002c244084040c0350b0081c0e0303c03411102c1d9a21f2103603010900c1c80c02c01404181c0390036006e40214205e2908628480e00400c0c03050b000595001682c2500e959542c03d150900791543c1c10605001d11140e003040e244019490000300349455003401c040d00503841841000010040011199024058414a83e0050740b28520821501080d50301c159822100c1c2c00c482e81c0419203a4035100841d074610f42182041103c20501041001800d00c201c1684908900c4e00700208005090000d08501c8003620b070604000010426039120102842a5611028102d1041104450400018000c1d1001501103415040c0790320008015861040380c0c04a02250340d0341c3e45140c1240b10006540318202c003c680c01d240e1094150407c40d0340c0f8100010545400a41c00690f159513042d034408002c1c103810042a4050b5080c11801000642103040c3e8401c140e0f41180c0158a07080403488640c002d018005003e0109200c0c94240401d020000b4100464900c074a00a058094101c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 813880170 1250 813878920 813878941
    0x60b04090b0d150c030603020405090706020f0313050607150c030e0d0905030303010605030c0f031f051207170c031b0103060e1b091807030507020c03160911070c0807030605 76
    0x60320805003401908812002030a6040da00c43d001440aa050001c1c001f500c0f030300810101ca40495a519980d8041801805801d80401610b407201748640e000f107241c5056040e1041400341c071407081602a40d00410101d04008130300d0591050350590f00010840c0d0b1b000940c0003406840300c0070345403a95000d00d0b0b1107088980d2040800000b910707400740080d45164a0300f40b04071000d60008200c012002801c0c4191466004240011801402a1740040b210002651040b10400c1004c0d800140718184040f40313040d441e60045540811202c0e180740407030151010450541c100311510748500d5141c003441e207030b402c60120131305144034204d2420382c0c0800c215070300c0e00588906031009031120035040c40000340481d500407040c03004240c020f5000d8070b4030800081d0300018481c1150f041d80c81c4000309841e4020060070b17540c1042074401d41d0000300c00a00380c0054080c8100c0100d030281c0129400161903030409800949040203d8400a502001c0c3c081029580e898403030f01c4100902048a02c00d0504000c624407544 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 813881420 1250 813880170 813880189
    0x10b090c0a0203030f0a1b02031c0608060411040e150406050115080408070309090507050c2a0d170f04090605011e080702010603150b090a02070302210d060b04090b 72
    0x1d0603002145540c41c1d94002244842006048000d00c50311052681181c100c254044031003440c076a0019904e035a1624210503100221007208101c281c80d0401c1004070354000903046070881c0c1c001c1212541840040c001c20090603c03c60070680910459241080502c2c404080511490040004000c16600c0715006c5a10221014401c1d001480d2070000c24081010742004104042c402c4c01c0030640d241c0e8402c030300c1c0251801140d030712000c6080468a0250703804140480a292050350072072400b040728605843d02480c0320314100c14001d641c0e0525000c10896240340114080b103915007416190b0200260803040c9610034011b21040604202002a181d40030344086800208c09440c10614540881c90450b0768100052140003150340b500c40000204d15048001d1081e01110340300440c1c09540d0a050140c0480080c1680c05051710411004002c60b40c00705240484141090b408050a00e030700c2044103c03402240100a1164601000001d0303a080800c02441140c0703401800707000404e19502000000c0c074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 813882670 1250 813881420 813881437
    0x915090f1e09091603080d0f11030105032506051806070506041b0e13050c0a03150c0801360c02010218030d08010b0c0a05070b040509010f031e0312050405010b090c 72
    0x3003004820700006c2e6034a0301030138081c1c000070800560a42c10200c82070075600d05140c4420600d038000014401c5003810701002028091a499494a00500100404008070507129680400001180f102403904000340302d1004490000c0503103071100d440d82409a16042c003a40d0032200c1c90700c0f10a070340c0d031002051402e000444810403070941c1c0750750381c1c4030b2413440500c041c09089903140038114190b40a079072410b40c1031014501402003151044040b800301c1d002c880e0251910000d1043e948010044810291264402440329040d55401510804052001802e480c1540c42e091400c101c127050b2031507815805042c986960042da07100c2441d01c0014036032101e07030409071240081c410780c00500106c07100320000c0800941c1401281d40c00040364548070f04000b565040900c2100002a08011510f00044074501404141860300305a030714603030300c224052100c408402d91402120a910040c580290442e03450502c010354103110701c0ca821f14189009200c0c1004c10f6118811107004940200f000c18191040407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 813883920 1250 813882670 813882703
    0x803011707140607020109030209090a03081008031902030f0307050c0d111e0705060d0e1204120b060d0c090902010f032c0a06020f1206060915090f1e0909 68
    0x4954001400196800a44c050341400b020b540e0000068030350400703552040e503010014040303612151900400c00903000d0485405001c0c095018080040c011084441999908000d100d0035282e03c0400c0c3e003140141d44c40720581d40804020040440c1d0007500603e2030348959420750b10001009141a01c4607440c2015100781079002c0d40ca2099030481048480481401110171203400c16524000207406510803440c00035240d494640d04d0b10034110401011440030080c5c00d005040034100684401c0341e01c20240d010f03003090104004100e00c1c1e00c40c00c1003d01001d400016800996807112040d002402042500324001340c4941c0307601080c3d520034415000c215144890380c00b0007101120401d030910660100260305409000380c032900141d035600c0100880464442c0386600c0302443c0e02010986c04004000034003c110404c540d40d520380d540500d00f109441803500a1340c544100f40041816040404c0c000c0750409400510010401c10b0342c4d600703000c4d03000100c4d522600c55985404564031b52220340d002d4600f9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 813885170 1250 813883920 813883949
    0x1602060f0103080903010b12010e100b0f0d030e0a0609060206130305090607020102070b0d0b0a0b030601362706030213090812070807080624090604080304030803011707 74
    0x80f8407800074401e8810080000c0b407810306220020340c010720120344921642e9580e49214500c0d410901a010080a80c0a0104030b242d040402081c1c0d40001c2e808045e20410840c500d182c01c00d030090484912203034001c2d240c8981c040e2a44030140110300c080c0a0710000d84106000600402e010b405242402541980c07071900b004003110a0203080e80121008a040d4065403501280c40f102c03075009480200c82450300030601c0c0084031b0a000003071595410015215104004000d45640c101560a06802c26540c00546841068080da094030304000c2021000c0c14090750300090034201d0401248020054560b0b0a100d088071521040865890344030080d04480e108161208000156211142050254034868540380300c507440c0e105043c10407148034011034000c809014443d5440401c4075401602614501e07072420030502c1c000d08884c000503050100310000207449a003620f500d81503070000c2c913401044a40300d90b26407510002c1604240660f02c5c61420302805c0030405400020f0903401c803032502003103141 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 813886420 1250 813885170 813885173
    0x1703100519120b040215071707110904050604030206010807060c20120307050d1b0f020f0a0305010f2a1d13050a0e0102090a05091015081602060f0103 66
    0x800d0244041c8001d070050303001d000032807048a0703100902d980e00c00c0c4003400c030fa458148100100c0558141900712a21401c2c000080050000d4107090340c50b4101450307132916206245007a511506100022035000884007080c0800c0040024420380101e210b9000e40b05e05030b89501d0640d85d161114071032400001d000700040404180d0007500c40210101841c00b4803141c2c1d1401c40400c01c41c0310304455034012640f00203600c100f80001408007416203d03451a080c160b084208005446a0208030405040c91968040b154115640c3c4040d1201640f409064000200d54a003012802000303020101d07030700700e806d00c0308103070142c3d560004040b0071541e10030021290610b140d408860b4400440341c02650f5612814101032503030388200d00c907510300b0040040820940b914200380402d8462000c403c1099a0051010a02903900e103001001550000c0e50303c4580783e500d6544070781c02d40300c0950001001100201144003070a512520091081c50038820030a0b40c2c0b464044100d035203c0f0116980e01d00741460340011300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 813887670 1250 813886420 813886429
    0xc0d140a140c0105041208100501050d0b0102010605100201020c192402040306090b040618080412020d02040504032d050f070203030c06090d0e030a080a050306011101150317031005 79
    0x14034280c1849400781c20324580010140c00c5074003d81d000d40c1c4410010009150031607102c01d011b03a00c0700d82201f00d1008a440c10380080c149008100c0c2c0d2031200c40d2070b0304240c21036034801d600074802810010484003280240c900044d000307500c002000c1216024401034280540324902c80207032002d42c0000c2201580340a01800300c00d0701d41e0035285403403842e0208000004102180501c007030050050141240e54140381c50104221001e4010180c41e400d16455054080340712042950102c0308681c0142440e00c07203a00c0026494156514000c4d03225240500340000d040d405090b0704140d111040018442e4490401c84400c0340e00c100c1241d40008130104074500380049850054218a8800307000c0340d0500064400f402e00b00b4a040f0f900106943c0400c983e443c07003540c0650703100e510307480c15030182581131034540b151202d500c00c080c0e0f000c0501c01e0000202d41a80d103d4001c00741c40780164802044900361045040748880c1e82c83c801552210010320300042160001000c90703028850500203100c8031841c01c0d00f0700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 813888920 1250 813887670 813887687
    0x2031333030623090705220306140a051308090301060f080703111c0204110f0705010e0d0f02030909040c050a0b030a1b170712060801150f0803122a0c0d140a 69
    0x20088000002c41d841003025090442d0b400f0310f10070740000c030f40a580c0c1c901c0c1c03070503520f0000c202c2c2f11aa8140303070501540040500e41120311581100045590b03500083c04039001d0800c5034050024040f81d440c00007054071021801d9401d0313a114003015113000d6211020804180b85144100c0082c0e0303180041c200062400340e1203d0300b613492040089082541c19110b400050b04a0401521665161151524450b50621078890314003841c3c148000c2586042d0002540c90259080c141d00031034290011900f440041c0f0445d000612004107880c0105450300141005504140ca404502c20f040a1030036551982d0160701c40300c00c4d5005d41d501602d035889100420f980c500b0142c9038109001c01c0a99152130001c2a00940011704149000460f107131004510844203001c1e03581c051155100784030b40c1032202c2c0c18080111001c0200c04500d1540a40740c080045a100403043d42000c4150500c601c1103204190000c043c107614a50603041c1c8902001d5040309854810b03109000003052442080500751580c01024a0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 813890170 1250 813888920 813888937
    0xc0a05160812180a05091305010608070f0303031d0102070311241522090b0604020a0e011416240c050a0c0f0b07080f0702031333030623090705 63
    0x180344c1c09a80c2c1300450b1000800f5540755045c0c0c0c0c1500c41001c14420300b40a1600100000002010314a140a0304180091a1030000a041684682169865280380741c165030215075a00c000715620046440d0203042072509101d01c07112802034001d030304080302c001d110340748204070222003640082d43c070307031b000703404004500001240e008806001c014a2402c400f21003a01050740c3c0307800080c20b8070b414102095042001488584110300400c100c2180b2a40600a5101003500f8240100354950310041c4c4840f034050821148003d0190303690500c18085001e40020038001803c2040e520b44881042407402e40300f044141401080d020800c06070101d100d40000480280540010804010140c1d1280000321061f603c110000d0030380d00501100c004081c140390f401c64141e00056240c4440064410204801031041c03000001d40d0703a442001e0a48201400d0442248105401c618102d0384000030340100030310700920a5501d818825003044002c00424020700120007080580d5a96070784404070f0700340d03021144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 813891420 1250 813890170 813890179
    0x30311010209153007020f03210c040306020304080406111903230c060108010e0703051c090806090d0e0105180402130e1302010f0e10030905030c0a0516081218 70
    0x984070003090701e001402d85070071303074525000f125042c034590091405001c080d1040040d0810000c812081b26240d1881883d40d4401260606607902d5601801e00c0c1e00942e07102401d5140008204401c02c08030341e004000341d4030592500016914a00c03105075071503800b0400360a51003800c0c1c100c0004207005451142074504403420400c08102c8040f10080725401c160304245059000c80b005020034070080c040e417007481c03400800400409213140c42ea2561035420407151000341502607044110548a11040030281c540101124143d0801d8032045688100e103400c04d0b00091020000c1c1c00b1103601c0f81d01200c8101001c010500700342e4500e0002c00c4000e5000c4140020055554400012001c41d8044014402c2c901c402091507041118000075060014090300001001022813400c01c4507910b1255200f215981d42c80c0014452405c0d00d8400d00d14442c0700540c070640d1182028a03000c2000000d00c0160b2000028001e00d400380d613849078503641f001071400c0c5802e201010300181c64400864101d414049000a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 813892670 1250 813891420 813891457
    0x2107030e0a0b04080c040506151801200618010e0705010503130b01030f0b0606030105060711032e061d01150201060b0d0506090f0103151d1603031101020915 69
    0x111100803030f40b241c1d02900350fa0f00545070340b154601d841c1c41000c1e0f110400352081c000043c3c401d140c82040c0d02ca0218180380001802e2440041e503440354400b508030422035008400c514403c58200c0e541d42c0c100319855541c1e106d9000d1407040031075042c0110030340110203a0041480c2c0b81018015074482d00b0040c8410020714a8113100c0c0c0224041e18a40c50086000700034040c0715440074241a10318120081203e0300540c030030001000580c540d00700f207841c050381200c501982800782000007420300c0d000ca81c004070a824170b092000440312610031804402c604803c0108070b03550303440501131001c040c180e00c01110600f0010042241404014506a1544061000144040d1981401c441903005105644841c0303075900100450340c10410341c1c980e00240b00c150010001d61459480900300519004400d410030384415403078100c4004083c1c6450004454403d4550400c91072500e008241c00ea44000e90019890005da40e140c031506200302c4484500c041c01c10220581c1100300d06040798460100c950405030301c1da = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 813893920 1250 813892670 813892679
    0x101d0f010c0f0e190f1a07030509090402041410060f0305103c03060606080907030213021b030702011b08030c1e0c100e0d050904110412030e032107030e0a 68
    0x100509026251701403684410a040640c1c85c00740c20382c0001151a000300400071203011030f4104054a07446032080791600745590310381c800704001e80041d0700e5a11040b000207091141301d03141d103034101c401d41c2c0c0555100440e03812829802c6081d54810781c1c0d101036002e1480c100340490303007144624003141841582d911014a00a03460220805902181048840500f0005004118440c040c0d1002001d55103400d802c9070a000d08955280d8907984070003440748441c001c040c0314808054042d28410170404010095041014403030a07142d0b48049422400140784410301d00c4c441d00719030655440c0c0c640010b40f8504503542c032800c4010035800b0440d0b03038100302403078034560f840000e03010000e02140500a01034560b0200c810b074454296035500754620000d41010304901344403a40803003514100101180c020410f8180c119188115100e907800030045407a00400800070f154000300321044824080d0211882e0021190240c066803140718140c000150f401c101c01008a4414034042e0191500104208081035a0303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 813895170 1250 813893920 813893959
    0xe0601060c02010906090308121b04030803040c0b0408030d241d0a0e0c011211040b04030b0106020604080a1d03030c070911070c17101d0f010c0f0e 65
    0x364484030028141c10340d6030085503400241d0100030011810031000180c1103a4403001580501c030401d18615000d00300013501c0c42810348082400c100b0300d80c003103561103480341466001580308440a403456070107480b000881c852001c0032903084a480c00301460400f4042e150800c05801c5400d900d03131100920151401c00c04210315009002003103440c0140c003c015420880c05050380000b400e01e1091407410226940c080ca01003071200148009181c12500a401482c8000c014071781c50120341204400441c010490680038401032042d2401002407915a0b0b03601c02007280d9400d0100c40080c14101c2c14003494100ca802100c203606440507806000c2e00906001003ca440c1d90400b0b411802d0a5102e030130f003082000918400d0713405001e450804daa00d41b44007501c5022544806100b29400c04000380c0040041550030310803085150643c04040c0300c10f40c050070400c0388090041b040c1c0b104ca4012811100c011603414400d02c0350310342007521085000d0040c0407040e82c1440b40750491a400400c5c2c01510303800d8088 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 813896420 1250 813895170 813895183
    0x3010e1314070801061707260607080403020d0c02030c06371d100e060705012405011e0c17160c050904150f1805070608330a051f020115180b040e 64
    0x1c150340c0b01400ce103030a0030b00070700c3c150707040c05a08180441e8502200140e03c001c41c50820002c410b445041c1e4031017400c07495400c10090208000810541e5111007102006107503051045d07901d440d43c515943c020070b9190740b108401502c40856100405401700f04580b400340b800d00403482d20080c6401c2c20f01c0841d4454bc1e007560703204d10117400ca50440c141c010f245154100f00d500090002840c20f03501d0718140001d0800100c01c9044088140044040c00d0000c101c040c5007210000ca0a03070070300b60785a442080e094264811500c0301120b841d50483c03404101c50420b4603081c2d20403a000016070056041c0d045801c2c00800108482d4610309448140007034200e1455410302c2c0c031030b1744a000100a22440c1076402440002d01811203c1a0028629042d0240121030550034202188040c03a20100ea22100021030340038503544410b0301b00300c00b181c0005820245819505020701103070000c3c0901400310304255200400c0780200100d1414000740c0301c001400c541c0c0b00c0e440c032a101510010f103002d0b80e810014640711 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 813897670 1250 813896420 813896431
    0x60f0307030b1504050a090e03073302031909030212131a0405100302031f0816051c0f110a0b07060e0604030503010e13140708010617072606 62
    0x2900c0d0310300b40110b4248007078140e03900c90807424038030b0620f4100000900198000d2264155080d2140c0a400c074640090044440e415440810f9500100704d02864207078000381258440c03035050700324a542004210600840703100d80380c18038078010740c04030407032300d001c020300840405504600c10014180d0703001001c02d0081960545500180074103520704050944010100c0218000c0c400084c00304110540b545424030240d0210b81c180503890f5580c1d5200702c50881c00084182d411009105800a0041c1011824030b1a1000c0140c0c50001c136030f01e6509000c184003c0d482c1450158190b000c4034808242181d41d100f0615104104501e5000340782c50010b070000c912a000340e0043c4070000b03050743c200080c6100d035845008506000d00228502510080c100740014802d6a07480e00410000500480c914042c500c1d41c00d91200c22150343c814000440c80da24a01406009040d600e400300104480c1400e28548090301c03190001009a1030502c030803213150729030034100c0d0b202c0400c040300d000c0d501301401d209045c846c2c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 813898920 1250 813897670 813897677
    0x1090f0f0c080d050d060b0906040b18130f0b03060c1c0b040903171005090615070b090607031505130b0d0510050403030b0415140d05030c0c03060717070e060f0307 72
    0x280e41d001c0558041b585158480c20300342d8410844074155483e120240d80440780c1e58100c0a44884015400c244d5001800c080c04d45c2c0f21131450600c804400b020341c0105108030010034100302406130f14080c5030380d0341d00568002da17611400b8000e480780030b000d156204203c8141e4081c0400c80a20207004241a2282e450044010030804c00c54038040c29005c10ba201d52104031021520070003490301c0041600c210015120600590000c03504101f400b00e01c000f10703250b480e40000d851006181101d861a00c41030305503640ca0000341450001128078103600c40e07250039036400500381d02c4003c255003907800003001032480d101d80103401d0a0941c004a1014804400140e041150110f1a80751500d40102100c0405c040c0c14401c901d403030503020b503121014903c1d206452940d01c1d4009201c00c2600099418468080018081e110004080002901c04541100b04090541c100d401c40e80b04c1c8a03058a210b800041c5203081014002e001841303a903c00c0c0c528800f10b090207468545807842242c004c0000c8e07030040380d80c68080f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 813900170 1250 813898920 813898927
    0x612010905120c011118010c02010c020319171804020c010b060a03090b010911091513031a0106030b130b010516031d0a060210090c080a140f01090f0f0c080d05 70
    0x4052080c042c5e402051003082240746848160008000003c0080740d50604102c200781503403045901840c0700c146000e03001402c60390382c0c01c000c0031403821080d8100c81c00c4a0030701c880854a00b45404490550f02c22041c610700728480841003500b408000e4200d2521262259281c00541d00c2d1504d03020001d1100c0e14030350b600882d02408a060030580f048040c2c0c01000d1441c909058854001820003d40b050b5040403509413000b42d4000d8100f600c18019160003000800c20424008104101a200b08034a044240d014690030781e03031070005034101c402005401d0740003543c0a03081c00c040b4280764003140030050141000c505001e100da0030070908002644013100480c000010360f50502d0200d804180c0c0d0b1000440f0035640c01414000025290b88540e071400340c400e6101d00385281001000464203028011600840343d031541c00e802c20131580440c11410f4001406583c40d041c803481c0c3c040c09421030094000b0469001c100c070300d42d035450940c2c000d14829590702a040c2c801041401c01032110b00b012101c0c55681c10b45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 813901420 1250 813900170 813900187
    0x12200c060a06050a050a030609060608060109060509060301021303080307020102040b032d0c0a031505100f080c032203050c010c030605030d090f0501050c19060f0b0303070308061201090512 83
    0x4403145a0040f5200c0e50502608200b03035078807a40c103002500e83c0004041070300c03012454140003074070964014070340c00c1c003400c0c0004c070340031029901101c2114030460b00341c00240c80c3c01061500301d10448940c1d000d401986141440405d204400541c0c01c5038151000500c1e1580d90f03601c2c88016003082d203840c0040d60941254a94100414802c1c1002c800b041e0341c244d00500340610710590b03070b00c92112888281501d0300020150301007000b000700010f08001c0c0450007440d480b00b00042541ca00c07034540f0740c080342d08000420750140c0c1c000d040d244580040402d020f80f050810b00c038113050907035204040b4200402007004400d00ca0080c01048030303007003c540700420000d06000816040820281c0200308100032010304004c150b011186000480c3c00a003003403640c901000e03400a052400902c901002818010418403c05c44294803d40031549148010080d00c482d901c20140ca0307110346c07100540010340ca403000c07481c84e01d0000e1313205091f050040700005806050350307501402c0034440300241d81100c00214031800d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 813902670 1250 813901420 813901441
    0x16022d09070503060916030b060f07050105180a06021e12010302310903020c030615041505101416061a0103060e01033203070515060112200c06 63
    0xd801c20481d0038507030f0440c60288007003140760100409000c1c40c001035036081d50700030340281d0120f0300040d0050b000582d03888084505034019801040300b02ca41d903103400b00080400c1d1071864803c1e100c3c80031901a100701c9442c0d0303c0700c0340030f50810840003885040c240101c03183d0880c00801030076550784a406002d010340c5180100710090042540985c40011200c0380030400500c1600b43e8000c440038202d00044003419420201e1400588030721180e0140310300000d00951081c481180340c91808202c6c2d0034003d03c0c00304107822800034010700c5107a801c0b184603100040418018011038100001264055080280d2010324108030b518100099414542e520001139005040c410150300c00071088c20144a02440c0068600441c0014440a0b2980340d00c880c402145445e6110804082480904820901020448030944a501003441100e50340b00300c031000032121031003080c90b920541c0d05840b81801c64907801000000741c00c0f45d12001445103c0b0b11840d1441168007006401c000880400421092038409034a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 813903920 1250 813902670 813902689
    0x6080f070e060d06021303050313090501120b012d0b040504051f0308070609081201150f020d030b01021203010b040e090708030406052d03062416022d 66
    0x9000c0784005504011480d2079081e07002c2c0366680d11241c0180d031001342086403200c100d419000180700740000100c0c0d500c6581708000810903070354954410001a6a505103101c005040b003500105605180d0004101c0413154150480e144030014440303c001e10002d0b80380e17601410207600400000180813606211a080c28407a00e644100517400144004011030144600740791709100c010044580021288204000c0f41c102a040d00d07440400c07a80c9840f6061212070041700c003405049220402d000c808a411403182801a40542440e00542120418981c01f203000c0c16140c0e4810741503204002020784004030400041d8000d0000c4c210480d103490502c610300c1291180a04041d0701c540c40030b0800d03c0b107403101008440854245007000c88d40d40c6107544904c40307244181030030340c0810a08580038000380c2401e100254032905084408090b10750b02c2c0c5056045800d150005941065424085d1010f00099444080303003650008083c03201c0310300c24018114514801780c921f811040d1640700b92901c03e09014114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 813905170 1250 813903920 813903929
    0x21c0201240f170c0405070210051003140a02090412181e05010203120f040f1203050402031e0a120926010b041e050406020c0a06020c0d09050d030807020c0406080f07 73
    0x294240e00000f1081d4554441d84a11510f01c41c4c2d079640080f64105e80201f00052511581c07580c01d00851404040700704181c012444151101f0704804101c040c000700c0403602045040d402408509240c4540e146c2c003200c801450612000d016450518100318549030040c1c0008003410380f00c14201007000001540c0c061203540c131050566005006c1001b800b030b94420019445060316140c80101d544a0500410307010100d07001404859803070350300560f84c0c0c0d07068200754070840c000e070201c40300c0c51000c0c0c10b1441161424100100280c000000f50000540f003030301ca040302905e4924092034040c2d16001004a030841c42440f000c030030555100d198081c1c107828098840c402008482c108104080c008807101c001c1c1051032111450ba940f4030004040203890b50545e0707084aa507404a61600c043e81c174200e4000d60040c54452098440d50034481012481340112034151075014041c5505000c0c0c90342d0507150710700c1c09402c05003075000d910380c4500c454595100d81c50003051070500034203d00c4885160141480c0e8107810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 813906420 1250 813905170 813905189
    0x90f041412030907060c0c090203101802520c0e0f010f0f050d061e02090a08030310060c0602120408070b070207060503070e0d0b010f0f080a0201021c0201240f 70
    0x1100c0740441c20401c040c4c8106c8c0c1b4003450141c3d0304d55922070b01e11200411600310404070b00352804a6040300309903038050000e1110103071400100719182c511120740c100c0c00a0000f10541c950b00490803903440526020054901950078811080204c0d5803003944206240d000503280005c41020094070001c0c1c0f80701d05006001c2c00500207142c0741061482c8107000901c0c00740900825080c0c600200b000190f038403014a9030b1000c084031a20309c42041018010f0b60041c46c0300f40c0b1440341440003188204010040b00c0c0035690794421091100e0ae412029205440d043e2820385403564284001121a024800c000380305520900380b065032103020f4607100c41030f002c000d4401400c5510030001801056007000c100c0342c000d5010b0410b050a103005d000010300c031117489039008104000e0a0000a406100d80c841501541c4082c4007444030345460704061982c0d0100b000020f401a031144010f40c1500414035002200412548004248020303090750725245d5801d075400c80e40b40c144079948108106001044048082d000040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 813907670 1250 813906420 813906437
    0x9150b03090c0a170a0201080603030d090b06010905041505210106030302010c1b110f06040812040510051603031509020a1d030106030803011707180b0109060806090f04141203090706 80
    0x84a450791741e00d1009000307041c8103004000c181d0b6075804000b03070b642c840d840c000c090110780d8007072070324843c000c10a44005000c00c6d4589400300d16440d0038090300d00803514442c0503a80340c0d07240c2070030440d80702d046041e802d491001c3d201142c100080c01f0b02490b000f86010f03400100369444600001031040d030410b582c2107107000d102c25600c2c00113000110a010038000c1213030400040b000e07080000d2940e11441d8090304242c446c01d41036502110041001e081203a10450300c0e05040348002c03800742ca80d880b8142c0b20480c501280c01200340001e0080e80003a04450044c3c0b0741d42f00b01511082e044080303a000308505008901c04448081c01c040cdc400c603852811403001e6000780441d03072441d42d0704091800b060040c0d000c1d00840010200004500b0081ca000600200c20140b8100400c1c0c2ca0350740003040d15001c10340c00600c4121011410328001c2e80e106020301809411618155a6500c0f000c0310f003035004d0001c1303403813252810740034000042c10020040e01100c900030301aa00e04180070485e2a001456004005110400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 813908920 1250 813907670 813907709
    0x1603050103020d0201140918011401020303271c0215010803130311030309100f0f090e070c030324081504020105120a0e03070b0414010e0709150b03090c0a 68
    0x8103d4800c03076550a007860b00d802c041d1407011300d43c80d000d0300c2c42494000c0101c2c55080300540c035034006e0314100d0750b054050000c03584c03060004a80b13070310080300d8003030b100c05400c1551103940b00354124a00064514070152241e0b5103c1941d030302c1122085400180c0186d00c44200002d11018880e41c1e1801403004100640c038141e98030300304801003101c51101401e401800000a170f0203480500c01c0f10b5807103000504811400f486c200002d000e64009035404030001d205801e10f04a15030040321040280d42200d6511640380e55180800c846110881608600305926402c841d0498491214036030100140038081850366401e2001300e614007171080280c0b086d8560784d0414000540d820034204d40303604010800c8001540d4031117032084064030000806040c58071000032000700b0720902c0d480050103107200c3d503601d1395080204240242a80c20f1502840c1068000c00b804020750141944402082e40340116800c06d542d94485075038030640c00840300103075150010303243c0c840303949817202828002d4400c2f10400304071805103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 813910170 1250 813908920 813908929
    0x1c02010210150807060809160e1b0705060f18160b1b0a03020a1406061305150a12030e03070f05040510151e090305030f0a0504030206040806160305010302 68
    0x100c281503800036a0361810340004400c00030310800a06860307011031362004c0e9501d01c01001044101c0700d000702400360285035012106950001c1c4111080c0796003540e030350707200c801c00d2015805424110640001080081c2d00c0000ca06022061050180554940321498a850003590340e03c1d0301c0400d045c45800c0031a81c010440103001c0e419040d03a4810507010b8607001c2c0d5002c1150301c800d01d10b00303c02d4a445000d001d0000c00d40d0000f00c0440a904c83d0310f00ca030358142c1d43c0e9241a0340e542d00340d03011640920407107298600da440d80c1d0711166211a8a1495440d0240c2d440f000c61182e010a4000c0c0400c0908000d682052503000703103000c0030340c0c0c0c0190300034040c03030340b0305076083d100b6081501400c0d201341d44032004103071402a40ca5418001d0202d1820b003070b000010401d0b014250b003611000d00c2500d0080755501d90300f0503000d1402102101d40140103949003a04030310500c0302540c001d40d459028442e05110210158840c00301a0025100040c003c114504010ba14041d02000b03000b450307000c243c100001840161038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 813911420 1250 813910170 813910183
    0x3061308120a0b060706291309020f18010f1d0408070c0302040f0e010b10020309010e0316180e01090c03030516060f0207031b03090e0702070b0d0b1c020102 69
    0x20500c46203003071915160400c5000d0916207511903413084010882e4018003805030300048018004d04104083c010103030000350b401800003051680d00980c0f40b600ea121b0f0120941185031203030310042c948580c1a11410004e10408c080007020048c80282c10010b2060480003010745010b0102940710b000d800d85007911219040c2002000104002c00124400b410485104c07440d0000e113500400038451b070500244080c00a202e5080c1a040942c248446100c07503080465081c480203406501552a2106039001550b20200500380c2c1e64261082030240003070726250641500217013110682c03800040e44c1c909858402d596070894040c038164035013900f07040090b08004403401180c0c1c1c181086a12078180c42c00c0701d6240000210041d00e130700d040404482d00d03c0c00a13401003158a20a4860050740081da081c3c1e00208074151500402086004000f404402c28400d10150f126450703204540a2a0301c5402e101d1403500160001400b450b10380388109000e103010101c5440380b8651202070749841c00030341c000070350303600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 813912670 1250 813911420 813911437
    0x50a03050f1308071b140f01080411040e03040e0106020f061e01120303021b030c0d1d0d081e07060606020610031103010e0f0606010201060e090a030509060c010c08010503061308 78
    0x100000c1a8040042134030511704c4607680403004a8440381d0341c90b010040781d141901228801c05518800182541c01101141e000d44d42000240c070300c0322000d0051100078408501c506105210038407000951101030310042d401380c0901c1d4060407000c010f40c00810310340350f0050b1091050311890884c0948046500403642d044070150562035074481c42506060b0001d100b074000e61801103929251954903100000020419001c013031040790b047d01c0110100729440e0060b1880d90a0703d9040341136410a501e4449401240640524519071500c0c000d15480502d04c40031803150b0301d00c900041424000d00038940f03d680000c00403800900843d28181c8142e100501c605d000081c141410401034103030f562800d40c8035520642801e0129080c10180303542403030b5a410202c0d141c900560030848041040928000d0407030265074050001c080c1185550b50a5640390484032103160050400d009040000c00240610b01c000074442d1a002030350750416080c5814600300a01c03c9100200009414000507640401c4803040b1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 813913920 1250 813912670 813912683
    0x218060f09010810170703050d0912080c010b060d0b040b040501050112050403030b0a240f0f05030406180602190305100e06190e1503070308091e10050a03050f13 71
    0x1981d1318644801c1e00d8489412035038244c400c1e02000304008400103546811349005100312440035001c114100c0d015102e9009908810b09805a03c0c00000d01102c00361007003007120b80000c50007811250200b607180d001012943c045a8951004d0300c6a400d251080d0070034804d080e2000e2005604220010b442e04038a41d0b05075007880c2c1c0c0d800020301450722a41c0300d040001401481407000036512025020750940c100394510800020034641360a060103200b4040603810700d501d0303800e003490051109544a4200500c15a4096140c54004441e02c03100c00c00410064402c203c0103807a00ac007083c03c0052610001c10b110107051403c0300340712900ea00d0640180c03c4403922890440c403580c3d060085501b130a00351fa00c50022958a807404600302080300c200c94445e01c240d84540c120069240704056454950f0700c00541059001c0160768410f013004034000c41c0c00d08148058811a001400101e980c0103126100030b80060404a280781c945540b601400b500500d03200325400b20707800c04400490408031802d0008080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 813915170 1250 813913920 813913937
    0x905061c02030a020a091508070f1a091003090b15010813084e0a0f0905150702071706060d1e0f1509050601060e030a0605010305010218060f0901 64
    0x3155010001003091513409000c00f41c0703c1d80e441e50044082c0c1180030302d51100b044a5000410701f0540020150219461074602220b00d9142c460061441d189980620000d02010000c2e00300c0c0d600c83c0c54501754041c219031f5000609a92a0500c540b9001000d8900d0140700c07003203505000141e1784111010f4014239403103548840d40000b458a07020602c9080c4d4280400600d1100d030050044e01804030121200001c1090040368494056191f20100c110185a4803030030314001041c10700803141d10501070000c03070800000b0030018030384841e4503110081410728491810501002000c9905001d2280200028002010003000012045440d03010007440c050260007030140090034040031199900d120750440d00810000205d0341000e003e0410041c8050b9000f10503210486a200007503c1044038158000d006440c039a42804021140490001600d50b03040c4100e1004201140751391050a00070342c4510001a03680c2c001c080101412900b00b120a1311402060040c10341ca1000c180c12944004000d1030890070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 813916420 1250 813915170 813915173
    0x10e040e0c0429180703020d06080a0b010f0807030206040902070201090509010f06140309030909091c030608070b09090a02032a071406010501091404091b06090905061c 74
    0x5411103003507220381c2c002d0410840083c40110342d01c916046801140b440b444640c084014402c0c500480101c140311600003200007200707988a035000e4400701c013805102055040d500c00082d03183c81c2d00040300f0b4600d10501c9004118511001400381c0c000c0c002040a412400c1c42e5800142c0540150301c50640ea480e000624002160b01c41e49548001d4180100700031005d503110043c18610a48501542020031900402110225101c1c025644245003010040d032410400300c007400000e01e0f0160070b2032880d200c1c074110501201c14100e08090200e0080d600025140d1801066518054a907442010030b5202000b0700303600c035200c5071140d5030700610100c00036980791505c10196000307084030401c000409071084041c0071440c025500a240d40c6004031000140e8000034042d4a481d400d0038456a4045a9584820892030031060710440c0e1408004000003800549621081400354030780041804d203d00f031100910009030040c074140060602010100107a1810b5408039419504100081e4034840001007802c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 813917670 1250 813916420 813916423
    0x50906031905070f02101e1e020c0d170c07030f02030403200f011d010309061e050105030d0206090d0c021927090c03020d0804030f05060406060b09010e040e 69
    0x200325000c6024200b00c1c625042800901ca4400d1490386001400b5134140440305c0f03940c0d409040840c041480d10b0303050111246d00c01c0b4004109107880c2d0070b000b0106214020400000d4806000c66000c00030190882c6c13050b005009160702e0a0100d210181c0d840b460500229110b402c007584e031415454148a00000350500c000d034914052079000410046025003020340d10220f140328103107040c0c0c06075401c103001c0006000648404076248000c500c1d0035043c2e2a990240e6209030820b40c00315001d40d000250f01003010300c007158901d6210140750450f030f07121001000181010006802d458055102801c0366044c00810640c840b41002e030f0b02c4003000b110520410039541c8184a0b04020711940a011350055551031241e40d048000b400c50040361290705020100314803c41c084c10060940c840c2c2e5854243e030955007005200b8088e07840540c0c24440c203000104c00615005807078110b49000310700030610b5261615000094580390f42018004c000c041c0050031050340c100b020282d041e50100e801240d169404c081d4035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 813918920 1250 813917670 813917701
    0x615030c02190f140a02131a180906061207050904080c0610080d0f09030f080702090c04090b101d0102032b150303050f071a0c030f06010f05090603 65
    0x100b1078039140002c82010007840c1483e00c40160700c96450004a4611500d02c682c4455941c1000780d0091842e000d00a401e03481940241900300c0c3c1d44100340b009425a030b0114442030420514038450071089800e000c1100070411026070300a508540c40c8056908201e0106e8580400e84240c42c081c8440d50b0104042000303030400c0e103200e02212400c4640034540700c16089511800b91003011214001c0c84011044548140c1c428005694a9203e440303095245a9a00340c026480c000c050f07954000c03d1051800507620211400d0240058204582e05d40382408840402c0354005d007810340c4074201c4114844c990540041c0710720102c01d010074a2404440b481d000507401d6104842e04403406540b0125549210481044068082002e411040000d0001c1d030305600f00c154081e010240100710140310342050716030704200921109105082d241d040c1d500381c400e1241d03101400e8030800b2000c8004410003d0b0706030f1040c025640030000746032044281200750340150862045010045c010400040007401400100d68503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 813920170 1250 813918920 813918943
    0x1903080a090b0d0911090903220801020406260f180a0516030b010f0e1306020c160e0906040c090b0d053003090c0609030c030703060f0f0615030c02 65
    0x1259486400141c064002c0c059010304494002032010f40c00f14070305141b05c24078400c4120100840c5070960880d06282c85044440c802c07200c0500c03618000c50008400c0c00500000c10650b01c507910000d21500c04541440c0c034071140000c4100d02c880c00c0006a685030b80804d9040300e041c030b15414502c0c05000f441c605020f05010064854814041d5588081e041d402500084900031481c4da98035980b14803444107101e03003071f11406a2280010000c94000b00c418580c42c0381451051b40b00616003c00610418145451806c025410046610082041d40c205c80d00301a800301d80e19002c1c010510b01a501e09806142e00c3c082d440f09684d68070218142c40d220003400c200f5103908481201d181901002d4401c11102e04000c2c0c1c29940000e03050b01409840442098901680090b40604010311030744050080c144c005a0a0769070500c90076603000c031280c400f80700b400d001e0f41c0200004606290740e4030518041d10322415500d000d440c6859400c000e9034115121070011961246008100004500300880ca0202411807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 813921420 1250 813920170 813920189
    0xa050a0c020d2f1e040509070e0a0b0109051f080604021b0319080708060d06020d0203190b0607050a0f21050316081501210e0c03010b1903080a09 64
    0x2c0d514400784214000ba8040f403006200d80111084030002c2c014200b04001c00100054083e0001d43e810b490580c1141e039201460a040310159a43d4051540001344241d07101020b469451500c06840c0d40e100700ea4030007810b4140e540c0307510019454041d03800c0207880603883c002c0200c90360100b8503996498046454401d250500b11441152500701c0548a074082c1c00c0f062800d0442e03001a402c858000d900882c80b40c6010b0300d03000e116a48000501c216100e0400b01191101d03804c10014004400307500c0998003480226580321031182210031760b20215854490180d01c26101031054100117400010840000ca6010807800e000e074029180c11541c0e83c0e000c1c0c0541400c080c1042c00507500d03640c002c2c0610301c5850384080090004180314416203c2030703c265803007041c0c0b4003d1020345e5013a5025004503030342e05809100103550108034900e00002c4075405518001c4d0340c1c0000c1c40d000b040c1c0c9000d010b0050700540c115a0b0500c05041e24000d540d022203140300c02481e1a1002c6542180a80200c10200c0140301d880c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 813922670 1250 813921420 813921443
    0x1915031517100b090c030a050c0f03070f09170709020c03040522062c3c0108070521010e1207050f06220c0f09060e0a020a050a0c020d 59
    0x4200070b85800154121190043c54040c2010043c074011440342e0052603000050ba10303545802c203a0b40050030004205040c400c42c10082051040803500055105403841e80e80e062095808420081071007505a10071035550000200072124190086015012102000801a80d508072003a40f2400d5020f20360007183c0c000058242c44401d010405000a43e0440d592020400f044c1c82d40c064290140c40009045d198203442110b40c81094000705050390084032808401000340c12203070070822003002d50441181e8849040b41c1130511001d0000700300303024213a1400034261560410002ca060023541c112081c041c14441000165070200a40c040c103483d00650007501d101406100b000702c40e55006400446262280140b4415003d4001c01e105000b861441c44c011502c1c0c8000c50044540f07103d005090b00d048007280f60001c1d00b0401c403030b4000020030701c1b540041b8640e803901500d611400030062006114500401c054442680e200f0103c0c1e41401150400b20007a820b83c0c0082102e0394207080d0010f00f0000c025 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 813923920 1250 813922670 813922709
    0x210b01050111100f0b03120a0219210509010201180224070516060e10021e01110d0f0b01180b0a030209090a0e0105011a03040b1513050619150315 64
    0x6811454980000740c01f1203100d001c000e0244146441114030f80401a00003107603080b50540d1440c8640c0c24280280301944c240682000b03001e001c500910201d0f8041840001d8080e0f80f960207006007480058050314212091400350041058049469010603204a45001d1005c5549074941554102c50f08035084810901001000361600e2a542c090a00030070420500f558a80c0380c035100f60070710161564094401d0383c1e00c212402e01140342980140c1055502c468004507400b8a500c094a5210079022010600612104401c0100d030b0b00302640e541044440007082090290a07055041251100d85c403403540c8000e90401140280511504070b41d0044d180800e1040421068002c3c0c040d081e1403800030032150340d80d2818041c4050052011080d00e000500006021504500c01d0552040c0001c40a41c9001040000540300011183c0c0c0394110395510300038800b03d42041c8060300c01c11403107000000303045c1d4241400d058030341c4030340c945000406460300e0801d59440488070101000701020910f204900c401c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 813925170 1250 813923920 813923951
    0x70b010311060414010305100510020c0910120f0501200a02010c020d0903080c0f1504210507060f0b030303070309110d02010e120a0b01030c210b0105011110 69
    0x80c401912121441410510305160041c01c0314102c44030f80043c1c6490110703080c015000342500800c4000d80e42c10100b00012a0f483e034402001d81c50071254040d00070b0b54000c0081001424015140c0c801d8000c0c054000d02401c1d030002d00002d82c90b5080b141e110394421062400b64050a6255803d82e400d0404a105031a02d911100c0a4080006240c009211a00d6200d400700d030f030384640f00040e00c001040303160100081103008000b040e4101c000b0080e0b40d00a156808907610300103c403006084550042002c100030b204000c100f20303030410304804030402911109800104a80030f036000260541e0758070b81400310355515561001c48101c0c005000d4a403649030001010780108200a020344940060080003043c034501001d4141c02183c0c143c560643c070000384000e1180d10b030b041c0c01c44002c4520502c1c00071030203d041400054020f622a0a400003441e0a087c0952400c000708441e003050040b000304264000307500746c0704071410365500b803900403c0c54003480309041c40c00c1c0e284440e01c0042c80c5800d480c003898054 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 813926420 1250 813925170 813925193
    0x60b030d08011d151c0501020415020709060501080f09010212040b1603140403050c0708060a0902132d021209030406080708011d06040f02180a090b0901181107 70
    0x1103201011807034078503030102941031241c01c0781e802c10200c9020400783e81c42c1c81d1024900c1030794171030f405d100003044074166101400c90b0701c02d8110081e1400500034810b582a81000b41e00d0281c182c42009011b0285880c0002c0c0040c0b0018040c00c0e80d074a002800620001e1096041d603070b00001e00360400c2902d08040c10410740303036078043d1000d022850109254070312050080c011344401c02041c10072503210369103c0d00e0441d034035040300b0282c220314000c41c500050a09400c00c2028060004040f0006030100e0318070401002c40d001400320901542455410b1101e09031000c80700349840603078400048412000ca00d500020300c110780c8001141c42c00d14050045e03000d0000040d1055645503100d0b5005910341c014141c40c6034400348610074040b402032041006200c04541c031903800c10000f40020036112640c0900c103050340c1082c40702064a4102c20341268452506890880040c0701102d030800103820000702042180405000302841c10043d070b0303d00940541c2540c000d81188144401440d118200c0d894002c1001c0c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 813927670 1250 813926420 813926429
    0x11b06050a11041a162003060f061c0309051302031005031524100c03022e020702190f0e0c03130f0201121d06181504060b030d0801 58
    0x10301e0b003400d40c11007044802c02c440941e540001c480513900341841d100354440d4410f407070124000100c0d00d0b600000610850513404100d012100d0f4210300050702042c58a8084014070341c0c1d8402d0000420300c40365403103486c2315402045503640a41550b8000381826500488180d0103035400080d030b4500081040d07816405140203402185250b88540d658404141e035640d500740580610300300303c1004c2048040101849a0345a05841e8801000082ea4001501142d2030714100004a15581a440105070b41400040400b801c0102198810600198a42c1d408001d20107a448419400541d202c01c1d075440d200540c1e07149640b11080d40b50369484149028071200f00f0b110340014200e4440104003000303044001d881c4a034500001181001041b80c854420341059030400780c0c1442800003516032052400c4c000c0c02425040c81d113003080c1c01c540d4560254a405801410074403100701e0310704d695000e444089082c24000c0111120303002c0d40d880d00c2c2405070080c166450040d0381403055908074108150441c800074100c0c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 813928920 1250 813927670 813927691
    0x1e07180906140f060318160b070203010e06070f0c03120513050d02030f0d0506130c0206090d0504030f03030506060c03070b040c210210050f0d0b1f09050f011b0605 72
    0x210b9003d1003289045548000d034088400d200141035000140d4440000c00781c520112100c0c620711490051407071180341c22800a0744000206082581024000d400ca03110088004101c3d602e440c1000070302d51000c0b0500070013040031000c4903509040c4100301140500c070004800b04a2801c000403829428003440701d0854690140d0b00c0b41c0b021180c00031050360000032100c10030301c1c548215280c10000900b07008203481d030b11085100e041980003107588101075565110303400500282c28102c9103503203007000c2c009020080000c20481440005c00c020b8802c03030b1450f8941401324098444000050380c5005035903664209100125101040c0003410030700902441c011189401015128020078029401000700f00392031424241c42c110050601000104c020300f4289443c0e0b050100d110852000e5610441601241603105c20100c015840c004003d612040c4078800824981f010840024100b07200e02c0c810701c0e125003907140c0b00c2e40c07440c0d000e02540d4884c1d82108100960180c000e00e0048010301080d80c401004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 813930170 1250 813928920 813928949
    0x9140d140c0c0d030c05100f050a02040b19031b020a0b063c061803010501050f0a030f0206070b070807030b030c0a0b03041703070207080f03031e07180906 68
    0x240c0d2040390072254201c412034058001205060107012002d410742c103084040020400724100842e0b02407240d0044203501d1040811020034144500042c0c0e800909075020880c410482040b400c0152011a4040301c22100a6540e01000d01c4007500202011030189218562402c446070119038041440010745104401c901516282d40c0c0078000b19003155203e4141601920b00c01d0012030141c0d00001884460b003e900c42c04020003803000c500349811042c2216860385004204034060314081c02080d01404003030b5440c40c03c3c5419000003d031240c02e031b480050980c810003110603056403100d0088560304d58003c011204a800c01c02c000400d9a0b0f170849901000034604440c4441c28074021407100a80303040100135841c42820140f120800d41d001400c215020f03003419408025400d07101c3d0165202e980c2c980c016060051a1400c418201940d403c08034510b03801c2081041150b050000c0c444c208511218070f1007240369250780c020b031055600b145140d00e0380030046d6000101040d03560040030039981e040a10a54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 813931420 1250 813930170 813930197
    0x5010f06030321110a030606030e0303070c1209120b040506100b0f181e150906041518170f150f060d06020c0c090c03070c140109140d 59
    0x440e030a50200400003011030301d81c070001e030600845806040300c00d428001425030000a00341103d41c020100c080202e40c4451041100c1501442030305100000743c8003561442c43c00c950000c01000c0c00f00d00050440c9844400c06100910507081c49002e0030380301c0085004100c0d2410142104202284c08a03154415240040c50100c00303a14210215004000030038203011150041c07034030039000091003028a8214a6482540d81d607030581c942c20024141c11a1076402104a0521404000000007016808402c01c400d565a0302d0700e5084074200c90703d49507209442c142010049030382c50916407a03224a483c40c030a020074405035526500140c00c82030b0084500200660b40340c2510b501c680d10f089140d001401e0005020a4114503501c0d40c0200010091814002175907562001c03600004000c08442d40402c0e0b50030103d00707000c4400c41c0c121105d013540e2415454030b04802880d242d81a480200780c46400f0380800c4060000f50055200558003003c515141040200641d40e41e070508080c4d40002115015844c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 813932670 1250 813931420 813931451
    0xd0521070e2b03050a17100e0c0703120b01050702061c0b010c0812070905090a050f0c090f01181a0309010b010e0109060813170304020f01090609030f0507030b0906040501 75
    0x7070110101c41c40d001002e07055a102541c00740c02c03c5058200740004400204d09130503060210720302c108a0f18500c91a00c60501c00211004039000704840780d0200100b1148001c2504120852480c40e518600855192140d00c01200c580c028035400075045000881c4020154a407507090480d0180b016804200310051500110f90a01c0034403009016404104065021081500316055002045041100701259200c4c040340c10301008a4550181a5451040c46007107048144010707040040303800e181d41418250750020300351032000301c40903040c00b42001c40050721494005a0714028202141800018200ea8080384025841243d01c00c0c00b6500e0040411065030140c520801c0111040c1c0d10000c0c142e080140543e9145000b91000021800007401344000a89403100800180d004002c01c94072401e142c81400b80d040194401d403414030003004001e114dc25030002848003242c3e0000098482c0001c54140309091411036080030307001c2c058401c01c0282102000608601481c85440200158404400f40c031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 813933920 1250 813932670 813932719
    0xf06040b04030807050c03060903030f1032040e0d200a02120a020a1d07030621230115090e061303020309100e0a090e0d0521070e 57
    0x14100080c041400070070903040140c00072178421411030b2042e000560019281034400c44060a265200100f00192000c0b44409141c02006454900880f24100000c0c86200c16408000d659609840340303104082c02001070300e40b15a100041c104200c282210200941c503908411081000705141c0e107540301c80402c0407141c2c0c0c00d20803d00e001503c4440b085908000041c24141034400306480b50344441c3c00565500001d000090016040c0d49810300e000d0300c01c1001e00580200010149440e0020410220000f03510321500d2820034003244180c502c1500d41401d082d410211008041c500381102c40c0c1e080b89055009465002c2c83d400c1030400940c0d10400042034407074003200c041140d000600411100c944040d49901110300c070380180c070b050029007408602e610020b00b00b0040041c010880b180054109418070b14081c1192100c10311100b0050035056039207406622110040002c00160084071060429143c0d10328580c0c890281e26070b00780904001c12643c1c0b1100c81d2031003441022260a0203c072403600c2e2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 813935170 1250 813933920 813933929
    0x1501020705030a03050703050d0612020405070e090a240b0d05090a03020a0f030e0409050c0411090f0609150a02032101290412150e0708061602070905010b090f0604 72
    0x503c2c144055550480780741e080400c0807814004c05102d824241e01c090300409000d05418400c41c84190b0041c01000705035607000d41080d0a10001552600c4291920202c0c6a07000198002c045038400541c81541500440c42c0071220181811348804106031150100802250b404500240030603224031083d541c07503407400480240513070b000c007018400082c5690190180c135406410701c4644284800c01040a0781c008103407c80d1140c0107800300c180c0302d152610580d160540300003036140c10185000f0106115180e040000c0b403142d01702099003841565283c44074607041440c1818551203400d00b00020b992504812a0074041d5800025640ca140c00107220340c80c1282c1301003000c10502040f00405d41044200c0c8814014010300c10000820000b01c0212610001c41c484c2e00184410242005440c0c121014801011456041040200704880c00000c00c3c82e0001d190304124602c8a100542c16803414225a0040707281500b0040002001c5018030041c12112806075507041030f65841108100c243d02c5036014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 813936420 1250 813935170 813935173
    0x5071a0703112b020d1e0503060619091a190e0d08040b07020109081516090801110d1409071418041103070b0f0306040b03160e150102070503 62
    0x10030100748038052414004680e41c0c15124400c15102401003c0c42c50034201e8040da07401160855030340c0c1d40c10405c0d091801c0451030038444040c135420510314201054405202001408004600c43d5581e24040b100034014900402c015801c004401030420002c52107032203000100c240070400c0e9034542e10215041c41c100109401101d0203001000c3e1401724030081a03035002480007050100250843d4000e10180c100e80301201c2c0c81d0300e160710004010340b40c0307600a002d0f10381220b00c1880700d140d03c001d88650801441e415025050000d4101100c80e101140c1c0034010942c00c040c0036100490140b03000b4219880d0f808000d1140c224032014800f03c1d5881600e14002c290b220a60401002910380d2200d203802c00010280c881d24512480020072055040d202906d400c100146d01c02602d140030480711000b4202032044508210008a41a00c54040100b03050300503621819030b0302155605106d841d540248039000300c1000340c1c45036228504202c04480d051120404007070f10001c81d43c00040c102e0204d8030000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 813937670 1250 813936420 813936427
    0x5120c042d0c0c031d040f02040915050a03170c030307030203010905060301020306092a0d1a01080f0f060409080d0c02010b0319061a060403031701120f0f03051c020705071a 76
    0x507401c8443d50200305170200c1c030002d4810061805d5030f580c040d00c0380da4810706202603225070403c4240d104a500e482a00d910034140c080e010010f5850f05110070703080b00d80103100f0b45200508420b002e000e502c50003e07919a9800004100820b007034056010b075041c0c0700221020401596003000380340c00c0707120a031021070380b2514203000503219181b00c83e07403a203a40c4810159050f10310000c5041e0380c10703508910052901c0035100c6004050030951401c01c0b52400c0c0c000d10f42048541480c50401d0008440584041c80c0d9008800001c1c04a803034582000d98100c0d400003001d035444500340048001400c01a01240040d403c00c40d848060f03207000245103c071003214007003200114810b50356641c0148040d1012229001b4a14a029038542da014081d0005501a4403043c6a9001c803000d180000c1c50b05811846e800f007940c03900e01012540c035007a161081c81c1d0000c0c8040c401006401e080da03443c06144070b2a02c0c0d0781101d51000707034803841d20b802a1001501c00c2044800c62500d448110b20201d00f03122035030758402c5060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 813938920 1250 813937670 813937673
    0x80c1923160303020a0b0a0507091503110c060406050606211906061106090613021003090503220807031a0a0b0306042a030c05120c042d0c0c 62
    0x1000310400325151400c03654540341100003074001400756842a000b41c2c200c1000002480354103442241e101311071103010001450403040103451005e0310301072407810302e00d44040c28490b01d0295001400c1d404100c0c0201c0d84501252003140c0e6265001c0b102158200e062101007207460804605a4212080e185001c4070094200302000b00c58900040901c03007001003d00c3c8144050540d403281c000605505d90360000c0c00c103280c1300168545280540740050030740c000740c200403540030402903055100d035046072181c03c40380c0b59040407000b602d000311001d45940000940e801070101c0b49522540d07144000000040500d0350381c0c8400d52624128440038102d00e0080d80c2400300c0c2c2c84a02c05056004030316503c0041c01202c10b102081c84c1007000c0307404491060310341a0513950015113042ca09950108068a80c11507402d59071a81164042d9209450058041000001581c1d8040c030602c8032030072003c1c0c401c00106400403c0303500d1043c601c02c00e905040c06480c1c807122081c0458090245142c205441da0004030909 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 813940170 1250 813938920 813938963
    0x3305060a05040f0914070216030b071814100908100216050a050c131e0e0f0307110a081209060708040519060305070f08151903080c19 59
    0x300d8108000e000c010101e441c104140d500c1c0c0c0035020b4407600085210042403200b90840024141c0410755001040c0164241e01004110341601c0c0d011a00380207a840e02c0b041580c40c044001b11680d400c81d015040418001c610074849882a5421030f00750000c07002556059581c7e041a00850003146c1050025068804181c2c0040a11080b202000d5110008507164a0304002e503a00c0c04031000d0300199607605c80343c03a042e941841c40b03400140c3d041100b403e100c08440c151012002e807180205440b81c0c0da0158011050195048211002040d2070b6201c02c0c40c50f101419028108403035104080f1400d011a9000d0000744c6000c8070180d0194052505c0000d50070480d00350042c0350200d035031724800c21001c02e254540c1500310796410884074410070320074140360003e03007928002008041000020300d00001c100750b00c40306458000030a14000b090703945588000c6a04d403005c0c12840014070740780180c00070422114000403c2c100d80305105407001a0021403921004844401010302458500d00910321100c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 813941420 1250 813940170 813940177
    0xc1b080c10050f0408070306050c04150c080915210c07140c0a0b0c01060e150d02040b090c0703030c0912020915120c1e0604150903080d330506 63
    0x182022402c1c0030510115120030f034132a8101c00259004036008104004082c002c07a9089840d000a8a04040c280f1200031468080c05c14410100007650300032000f88242c0504951081d000a00003030903c08864590703250a50203000500c10203d01040928507a800c425500e41c0959520142149040c8181c0c8440300b1070004091040c1c90303400f441191045130754504004200400300c40c8441c3d62200c19140c000c80c03c503840e550201c03c00c22111005c100030a04840b020507460f4000300c42d01c1c5540c8060340089801007000c7c414503504014a201400b6206441002800c1414803955060040c0910824116140c00c42840791101c01d000c01c519030300c018905038107666070110340d900544945024100c00102c101e0090448800e45422442c5841214204040148200e16082c0300d44542c0710036140c08a4541d105030f21804000c912a02e80c1084000d102e8183c002c000c60b008801c06403102d600160102c000c00c42005e208154008404120b80c203260740d211381c00310384011240f030072828502d842e050100c0c035030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 813942670 1250 813941420 813941449
    0x213030215121026070b03010e04030f0c03050904110f040303020c0909010b06030109090602120414160f0506071a0a0f0612020a060e01020a02030a050102030702060f01030f29070c1b080c 82
    0x103031910200741b0809410103140281085942c2000300d04203410081c1c0740705c001401c080c040000b588a0900800d400c102100c403500c0c0103a4002800414200c1d95440c1070050000802e500da800240001c1170640c005000200c80400302c40300c403d0740e03c88075011401c9901004071039030010803e100400840c0d64580c840c00c2d80c540201c82c090b2600c0440b83d060405401e04840840b010384451454000800d41040740383da0b05000300402a02140c04c1107405a610709142c441da500c91000047c00c0d408001e05c050140c01140070b6100d2801813070030b02c0400d29001e082e4098a0106040c50300710005040060040c03604420f0780c001d0f005080c21814843c00301da01c281c0c540d803540d0641c411910b00c0c0005860030400c1190385401035000584a08081c403000303007041800389c000c200c42c540500040c004541014900f00c1420307400400002c04c550002180103a110a01e511800c54050171001c1004094010409130391240c030032410503080182d10921070301d1002d00e0340a82a151381c401c1c4030000c29401d007440c0d06107110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 813943920 1250 813942670 813942673
    0x6090c0509040f030f021203010b09010e03100902100305010501120905011b0c1e02011e231206061c09051908040609081f0213030215121026 62
    0x5620340d80480c007024420b035011036042c1101062001030660021a6042c070454610140c25860312043c1089203500044c020702100000000b0402002c0c1e015501c2040141c4024065440c1511000d040c2c1004160741141a809004004051482c240c07081c8601d50503207c0586510740104501c0442e9402070500e43c0040b1400d641c2c5551140303520140811000c94140c80d591002e2040c25540f9000002070840044107100b54401400c110060317800180010503500302c00c94420710300321000e208491805001000c2c01e01512603401000f050a0300300010060350044100201c0140c0b103410a001003032240040c2c0081d03401348070f0040c000e44005608001150381c001c4044803000c0c0030b8080000401c180c03940c030031500190005807c0140c42c1d00034076208000c205010203040040c920f842080701c068075005103410415030006803527000388101a82c64024513005411014080c0800d1665100c030350103503441000040b06074000503405210a401c0c1420b480c6c507801ca0300c0c15807450985840340e1080411210525 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 813945170 1250 813943920 813943943
    0xb090c03150a0b070623010b07030909020a09090e0604030e041a1206041a040302031921150f0b0a0e0d0602070b0402090606121b0c1006031a0f040609 66
    0x41d41d64403039900281c5410340042e030b0389030102e141580880d06c120344903441d9542114503000014241e200350300d0440e1030f0405150b035582c40b14901200c00c0c207080e411880020b032001c1055000d0940c02021202607a401c0f400070085e01b0003d210069850300c04450050009141c00c00056603402d094004500500e81c20a1085106800500203142c0308070440304500d8503840582013005019038510a240802c0c0902c16000715400c054074003d40340e100d425403a404200580120860b524481c010340300d00e110714603a019a040c441c00c18840040c11001c6200c885014002501107a0200b40ca42c0301d108031192803e03901c0c90300e031103500c0642c1e02e45048c64804e50f2110b02c520711140898000d0000f051214418458125145484d1040000700c1c0c0d00640414003e000c20711945920030b00f0f08070344030307001015040130b90441d46003018108511303c01e1444610781c9008442030f010100c00c43d5001082900c0c868441d00a9400e082c02983c50518801c88603800c200c8042000725022601c03c0d40002180c0b030052206860 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 813946420 1250 813945170 813945211
    0x70e010c0f0f021906080c07020a120c0305070b0f19030216051f050c120411060a111b0901120f0c060e1503011401110f0f031c0b090c03 60
    0xc000300221080d9001c0070300c41031040031071412288189139010b2500e0258111802c2c188018440c0400600c0c0b441400340015400056585510050000349404001c40a084140d03241c043c448216a101c115010f01c07440c3c02c007090110302c03803041d140858203952a03242054903501c017407005200c4403603003030b070501d5400c01540300f8088020100c0f04c4810f000f01c6c02041341c840341c0300c0011010900d00d060075440703a00d0301d000e004801f48000d0444505021003038a1003119151400c6c00309264200000d6070b503018000060b441c1c40c0070341001408030600100d0042c0d5081c1c100c1325060700b44000f101d0404a501c28180c40040c800221110f00c0c20719528002e003449040d040c807030340d640c107a04403440c0c118101042e04158080d41c60b1410a507491070310890b080e407085c11549000c802c0031005c0f20320f10300709040c000d01a2480141c1c0c80108400c10f41034a0035001c56a04c54100b60150b505c990200ca10004204000982c40c1d400304258012124529000740404000355100bc00080381b903000540241980d6440492108 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 813947670 1250 813946420 813946433
    0xf0b0402070f03020c0a0f123206010e07020a15063606050f0409080d05010f0501200d030209030307020a150e0d0b16050d11031617070e010c 62
    0x2192845071441002d000c2aa040c0070349800c0049105510407802c81805100003a074440820007155007100140000d0149031038075410030494480010074824885071424001c1c1c0142c81085940210442a2032503030740c8a82301c1f04d220000c102e803a900968403d01030034000804000b4200790241000000094042d01c460f13041c2c040000c02c901c00f10015520129003460030307981000003500074000080400c1200e241502180301c070000e050945106987c1d0303070b03c1c2809102c1e075141241d160b4402c500d0200069a182d08141c0d09a44542c00384e140058100034003c4030782d480715110301911101c210b00401c0c084000c7d4004a000e98450510035400d4082070001d500140c4421180354050310001008a06600088400800e0401c010781d0f10740c4241c40405000700880c4076a218140c000d818942c0b0b5138012035141d60284c0c1d1038072901110110452503c01443c21000140000d1030050212200340e00aa011001c4202c44109203e0f900325540b00b50403000c284914010401d11407015818104255813500c20380700da4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 813948920 1250 813947670 813947677
    0x90a080a02060f0105010f140a030f05090102030907051905090403171e0c0715020f040302030604060605011407030806010f0908010c0c1103031317070b03090c1002060c0d0f0b0402 79
    0x1140540d10030000e00c00c482003c020000d0242c030b03007803034034480d80303a258480104654400000c82c3d2049200040081001c1c1c425000b0407207995040d0018403080c10b0920141703000b0b60080300c441c01e03680900032000c60280341010080c00c2e1034001600700b1515600382020402c50110240c01101404005400300e002c01e5007460340180f00c0c0c10101e01044400e40c1e05200c611051000800c0e1040b0ba6904100040008022000d680c00300b6030320b910300503142c003031001c28050070b40710303541002e903143c420b0000300b104010954024509070b410070f0380c1ea40c00814129001402c24001d08000401007528180014041e500c5144861040115842c1032201c05659166460031103440c0080c510001e44d120000301c0a11411501040c000b40007640114034110340c5e1301d600794280001d4012044071203c02c06800241c0c1d42d00300f00d8200039011100403581c2d2824008040ca0f03803203403440741c05402142d01f070620681c035600100701c1c2c0303200c0c1c0356410040e0310b48494241108000c0c8003101c20340310100d0741c840500c00780ba1614400b6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 813950170 1250 813948920 813948937
    0x90a020c010b120c01030509030c070918170a0f05030105100302031e15010216140105030c2206081303020705100201090c290406140a0e090a06050406080c06070308090a08 75
    0x1604492013084001000d465005102c91096802007001070061240000c100c012620301c0f132400601c080d0100f00b000c050749920000900003420b0394500c800800741046c02371210342500c0c2c5510326102e841404c00e41301f80c0001d1107803940c04001031540704090360203034004561003403e6001180c40d0000c009142c50701840c003035401010742e0072844680225960100714600d0111881007510a5007490000520458242c8484180c100b042c0400802c9449250301c041d0781450000003046c03404024003414502c1e02910714441c0351700240b25000441d601c0e002c8584003100d07171074146d405800381c00d0030700702400003011300c4543c100e046643ea02c0b500c502041070214030030003514160388030740c01c48407030844180039071425180d140ea010881000208030041d00000340c00000f1042a92081c0c80e11403403030040d2104c1d286c641d512604110103504000381e045846d0300850580d14211010040d1a4441c0380c02c0341c1d54031031a482150040707010040100801d006c1c085103075000c0240c0080703810004281d80d40c820250046002c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 813951420 1250 813950170 813950173
    0x70f0e0a051c0b240607021c02060d0c0e0907030c0207210506041527030c0228092d0b061b01020a09060f021011090604120b15090a020c010b12 63
    0x2400c10b282c03100203006844c00c180c102c0d00c40d81450180d40002c0c071914100072a03602c500341201c2c050f0086403900301c145c9182e0410110100643c0f400181c001d4544020703180040d10072083c4000094040303010784503150b9904030075030040c0845030511b1401c100d0031441500080c081c40000d40d208001032010428144200d01c10a40505103209000c02901a81c5e450350760300128040400038540300b0000c8030403180d03003a0341600e4034400c44180713800032646040454002c4440007090640d601160405030701c80c074003102d0000104002c4000c5405080c40c90b072500c42c0b40020381420100c442c2d0b0307031003007250450810301c10000e044500e03100f4602c05000300e1041b4a4602c0d00c0b1039402240110321590003c640800911003810140c81100130300b0340007500c0307600040c410041280d484a123100441c07204c4d015154140b4001e0308585e80c0310b031104018000034000c1030003111460702c0100024085025100100d484500150099160781c40303d00e101c2d40a500a50280c2042c2d40d40c0b0340400b1255603600c203201c481ca120600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 813952670 1250 813951420 813951451
    0xa0b0307050d0c0513110a0507020f0a0303080f07020303100b0306060d0203070c0611120c07060b04110714030a02190302031c1a04110a0e120312070f0e0a051c0b 71
    0x14032198400040c0d5a40b01702d81307803803580421901034500301c0e001c2c0d0040d4503041f030340d618551000070440c0c4800c281c0c85410800c40d60020080540004000340a10134000482003581c1d05d418041340e491008660110090b2003008040001e1842e180146400ca10010801ca05006a491000c02240c2048488500040314010000b0510201d032107001640005001c90728640140e020960b88403403009015405c0001c4000386003800d000d07031507014441d07410004109006c1c80b9007040a500d143d411011098540001c00080c20315809400421a050410a0703000b0340b040c103400e2081001e00c00120001a419400104038403600d001c81d410013032505903000000090909a034076403181c18600d1110149000e18078000100c64120540810385110086a103805405d607100100400c2a00001b00d8102d111803101003005030031581c00112243c07046140e540d0f41000c10407a1f0350100d54071265410043e0704008404005e100300c1c1840142150452480c0c041d5000024107551038080c40c10080302e40d18528500316 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 813953920 1250 813952670 813952679
    0x19122102010203062b020d1119051302030411010c1a091b010305060d1e020901080a020420030403230703110708070e01090b0a0302060309030c01230a0b0307050d0c 72
    0x103205000451910401108030390090502c80001d40c5d8500801a00c96012a0001c03030400c040c45c4074448005101414440715a450507070842c41d412a90301900784240b00c50080c0d44201c046c5442130303030320aa41046401d511009010010340320002c164405851040e00001000d0682c03203000c1d03c1c04d018450400003044000d4011900340100001589401e04050400003400748a0307842180000d6071b1908800549041060728020801c0140346640094000d0400000003d040c0408510b24211a00039107043c4a428002c05501550609850500503204024004580460b20403d203801500340d41c054030541c0c2c10000d40d4484e00700e400c155012000034400d511420342822080c0803001c01400381c14001d022460400620007030605050050568980e40c400040c6c000d95a0390801100454020b01030940c1c0b400e018000e580c981c2d103c4160010310b5800c0070010005078890410409200100c4000c1d9011070301c4042c0140c1c00340c919489107a034144100300000c0b44965440ca4804070b0309216040d05500207291 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 813955170 1250 813953920 813953929
    0x1e161a0f010e040b070f0203041e0509010b07050a030f0210061401022b11030f070f060501050d030e0415081c02011d030f031b04030b0105010e1912210201020306 71
    0x5820502e42c01c14000d00740300010340440c6485130801d5040c10201e20320710141c1c004a01d140036543c0080344038440d080304018032240e1600c850060301d030103496040e8a130f038031010a0b86a500c80c012008240341d2080b550300700849c0c4140f86112800d05c2c01c0c41a02e103940c5030f100c0c405081c0c40440d04107c2d09902c02482d290340e15a010030012000108904100d08205c440d8800c0c1100100000c41b500207106d8504a150240401841152004101120714a03210380031420441c0e81118940c0b801c5402c145000c00215051400c1803042c0681c503816500c0103000e40c1c844003840003030250302c082280048440e1001040d4036006003c240d200c01c00549141000000881c4000e01f503959680410071401803015145010900c0402110103407405200d90341d41c3ca85038450449101948034204211515002c2408010407003040c80b02c40c100c80c03091f0f0700c440b61885084c041000d131010940138132011082a00b0108440030800c08042195400b4900c05244045401c02d5050300b2980c940c0c4450040c0d6002080103900d140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 813956420 1250 813955170 813955201
    0x207091406090c0d0f06050415150e0109090e010c11010506101101151502070f0f0911040e091c0e1f020f010e07030507121713080115030c06051e161a 66
    0x100904110310107460526010441004580ad20b002c10094000e005c805074000d07425180208a07000040010038820001c10307001309814810400001c03000990024924014045c0500a0030010821030440c158a82c2c20340303580c03501520030202d55481e902c0f5540f00a0030030000d400100b25100701c0c4101d910550300c00a04020054106180d5950a540280001c4004855410503210340f1040040d400280c0d00c1c1e0442039000303651203100c5100910040050304000403404019606c51400c0c100050788203c0425a501e0f203030702071082c1c1c0215030b401181c0060804000c6d900812201030055803550b0380c0c04002207084d103a0209400c40c0720342c030810007007041001c01c2042e40300908076000d08000c51210781d6038503031300c100805014407a0703900042420800c271101c000011005101c0d8030003c1101a254507440b40c00d1480505c01560760450100f00041d40c0750044003110444140c0514802a111a041492040ea0082d906441202421805c074000041900c7c0d0340d034043c07030114405459549000b2424031800207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 813957670 1250 813956420 813956441
    0x1e07050a1e0b010e060402090a120b010b1801030c050d060e011403010231120b04030807030614040e03040f23010e060a031e020301150207091406090c0d0f060504 71
    0x200800070800b05141c250200d055850350242d000480c1c840a0001d0040d0003003041a581c40140120006600000701884140b054824200f0310b00e60307a6244502d014074014060840121a09076440703001ca50700c81d900010001c981d42c103215003010040e02400d4201c584681020602000c644014401a030000201101140044000350314104020ba0070003483d1420400c801521182d40c10b5580000c034040702920081c3c080300300300c921801c2c194140406048002d94056002c03c2c40000442d201c5446406040241d40340800d4400d0f070712a0a4050100030075041940c10703158001400b01145010424030408020040d5080c481c0e06031940007400d0324040d140350b40700d0341400155051031119032145070644000300124100003610035491100f88199444602510840c28400000410019603c105a01c4004480c0d400c4411807925014681d00b03c1e800780844505140041d0002015072402140d065401003490031414140070140f880300c01600c0340312881208051f1203040611541c20540b08411014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 813958920 1250 813957670 813957713
    0x406080d021908070b0c0703080a06030521120a060609061b06020d24060f0203030603150c0c151b070c05060d02121f06020a080f1e07050a 61
    0x110580310000e9aa102440c2504861141d0000ca000c03e11a000041e1030300190000c085481c01c0c5040109000d1690164000700e010a045001141c01400103100c0e400035694802c000b001d02400107494122003014401d4480131095080040c4107180100001c0c060003113250003004150181402d8010b400c0300556000201002036508402121400c011180304e01c0f0354022400595405800008202510980e9006100e198108000014036803944581d10112416651600000744460104a071240300940d01c03581c0c143d001881c90601c424174120710030740001045491500d071160204c2a541000c81c20700c903161000310783c1000c005884048070721140e00502400c0240740f81080d96030b902e070b4034440b4038000c66004120124542c980d01c1c01c03030f504582c0f10f2000350307806034400d00d0b10420714407000001e80348503030172030f280714800054582c00011084001907201c0a03080c107201120715084c03900d80000701e1070400e10781c04003141080c040281000b410b00b14025400b0701000111410301c400010b042c0d0402c15101e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 813960170 1250 813958920 813958933
    0x9042702120f1902010c02031e0706050a0503040b1012081e03010b0a08090c0634081206011b0b06010e310207020315160320070302070e011202040608 66
    0xe000c0d003c12002c642074265280343d8408845400100e074a4120719100070340510034003014018203240c048000d06a003e440040321030786520303104105c07414000d440c8100003050003800410006042104070329032103c00320043c048429602c1a009800341c040500c103503120000040c1030518030071140c1c5070b108001c0d0301d80d01041c03855140c2250020b941c46252110400c000d0a007012400eaa0300511011450b4000100340688802c002802101d40d0f01c014480c000e46450508030590307145031030300d00003440a40c000010a08040d13400d130301c45e205c0310702c02400c1f2410080c25034094030f2241e0405001208080c040c03803500032a032801c000054002c01d40c402c00705100764005070201c2c041c804405160951a015000b003020b030480380c440d80802034000c417800250f15000c0c41d144c0b01705400b07242120f41d114201d4145142c4141301410741c19400c440c1071a140900400c02c0d0340b072099408a6040040208521030700c1229402e555400200c14a600280c000b4100d98034107600000035460540074483c090121080030713209 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 813961420 1250 813960170 813960193
    0x90f20010c0317090c0405070201020a0306050a050a0302061806070b090610030c090b030109060c171e04080307120f0c021203150d0219030308220f02060904270212 72
    0x200200e0790703c0340d600b00301280001d9a0f1113001e0000d03080f12400a48180428106028064042d4001e842040006490401c0000c1d4034904030f80000b04480000d00950700e0b86042d40c00740310b6070340c0c404056201081d060120540203501d0f01001040001d0040c07000c8110fa0421003a02c0d814404042d0001071200c0c4a00424404213601c1150003003100c0f1842c3c8002908001903020034050b00c4c2d070070700140105d860319190002c442e810140001d055890019110826940c0f000c0c0940455600281800301c04801c500140c0040c03944001190401d8150800c0680310036890300f08030681c6c1004407503010311500e03402040000b0741c0400c1800c01d1154040b00150951030613442c1c4c03001c1c100b01c11815a20031408442405c0075900d451004071320103280641c4090f80180c5900340504030b0740e0141d5104c4501000c007450450f00c03c11108116800070707801001d0f81c040d42c0c15502040000e410040c50154420390b2002c10482c0251030300d440c2b0550891b480c2c15038074580c100d401046420540d40d41d0b1903840b40c105520b07424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 813962670 1250 813961420 813961427
    0x303170609040213021e0309030a0f0f0e0f1513080f010902030c0907090305030d0614010504030b0f07050d1802030d0906170403032712051305040b04090f20010c03 72
    0x107030384d40e0400005840e501a4008907800200718511480d00110002c24015a080040014042c100c0aa02d4400d035000c00c0c1101100d1071415500c0c4a40064440040c980c41c83c500301c40520762103000103204d00d001d410170040907d4954080910b0b8604050b1541c020400c0b4030b414041d200381c0c840480000c00403103080e60003081d02d8080d04440d1911440307413540042d02d1300f4000e50041001d1030700041200c2d01d4840128400d0020300c1b241c003e0007412000748280c0c450f01d41c4510100e4040d603034020503403003954a41c0d41c3d003a0141c0001a0080c07050100510100b00c3c01c0e1440d100d0342e00c01808065a06044030a58014103081c510000c502d8001c102510b08113012035900500d0110041c01150f05012a40d5180c0c2012801040c0c8501c0030601c0c2d01403001c20071f440140400b80c2806040c01280914001e40358100d0996241c03050150003251400117070010060f6103410307800207a040c200500b0210b000811555170b0b654010800e01c08a40042100390801480b254004501c0d501d4027080c203111000c440e4039200038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 813963920 1250 813962670 813962689
    0xa02030c0d090b090f1804031814010f0809010b030f0a060510081e0f07030c06170906180c03030a0f1403040201021b0103090c0b031b030c030a020a0c0c03031706090402 74
    0x45005d4118074800403003580b03451a04440e44c903402c1040c000c0c142098580103004040d04051840114217800c804140d141c1880b520840c40c0b0016114481725510f4240151003540c0014080e807010b550368503040180d505c00307100426185400340d014200094803807529a0440f8405001140036030b017441c00507c000500081c001c2e020b0140c1c440344004902d00701c45003910b421b003004688a19030041c02c100004002075912704505551064495401025084165845c40082140d4940040d072118020030003840c1d00751201c04140c0300441c2900e0210603c030000c40c0c45c5a00a0201a0000e100122001d82140d4040c10301c001c2c4084121036580b031402c003500000d58595140400c810700d4508095404140c4c0e019500c242c00d01ea030b114040800140e0f64200305c0800745c00480e844807140c142400d011165001e0441100d00c0344d4180c03a415400e648408003140d0080d0411071300b40091020360980e02c800300700110040c400942c400c0d5648445881a10641008040c000c0c200f076004017040e60500005030f9407031031075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 813965170 1250 813963920 813963937
    0x6060507080f0c12070807020108221415010f0f1d0f1905070e03060603010204030c0b0d06170c0307050a0b0d05150406060e090f0103020a0e15060a02030c0d090b 71
    0x500c2d02d69800c00307007044c01c094440b0208040c11000003040350401c4960700c05491101d0007602c80c012a0b40c2e4414026185040d1000c524202c15040c00c1c0b50000502500c0c1010490b0800c8800c0f622101ca1080140305540803e030002d0002ca0021002001008240340b28100a4100c0700566005850b055450f112400301c060b250400480d40c01000592440781c00001210802c0d9035a0207022070308180e0701c00f0341403031100000f45001c0d0107051300040e002d08050080302c0850383e2000d0f01c0e0070010b1514041c916903400a220006038162544030014201c00342e10b200721000003441004e440c2004400b01010310300310456000c41d0046092040c20841480c800082c1d80700302d064504042500c0d505c1035154008403440004141d4820b14101010603003540c00401c055070700340181c55851054440d07402500100078240710003948084640c0003441120320800070103400142901081005501c4000016030603044004810010780c40480c00769174007542046078141480041c2812150b9038200300120000c0e210f520f20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 813966420 1250 813965170 813965197
    0x910030c0507020a030803040203010609020306061b0102130e1012240b0411070c09140103030f090e04110108070e0603181f140109020c0a060e160305010606030606050708 75
    0x80d454124003880c01c54141550042003030200f2600c0349440782940c5c0003950268001e40c6040c0d00400c4103066442142e005000080106043c420000c40601441d2840d00000180b55000c0c0031684c01000c0c02e0405c140a00381408504166280441040201600d19400904014140e181080114803c04038007c40410b408004944c92042c1c1c10142025041e9140b02a8200380b92000e80003040c80b0b50301c050964103104882d0168010f0740c2e4052001512a01d145284131040c98000420009004201702400001030b41000014184e0395402c0484c0710400303c40642e4401c19a5440403155a882020103500042908000301c8100f1100042800e50100401c0c1c10182d03105285106085201001025042a480f907200720b10300740c1a010420280c050010300c86c0d9601005000480d10900310f0082d60310540b5024003c0c48442034584500c1d0141ca00c001c1d5202e41d601840c0784400701086050000c0c000703140101c0001c105607150201c010100c40580d4840c8003080803c0c0400400242c1070340840c0c2040040d840c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 813967670 1250 813966420 813966431
    0x115030605220302210408030901180305070b030708070c170a030603081308010b06190e060403080a08070206070207050102031614031b0c0405010302091303030221060a0605091003 79
    0x10203045402c6a0180704031070094500c0451000c00d03a00044100141c060410408510020000340c800140900d00407980203400a10004815500c5074444141c02401c55455000450340c946440d03040c207445410054045000000300100c1039000080c07540c100c446890080d40e0b415080c0c644400419800382d9240c00701c5800130701c082016129800c0800915004000f481d5980c41325440a601c441340b61240750540c4d401d004140c00c480c03426106079040f9501100d01e00c0713000184004100c403808800260b00740d0054090001001240307881003d00ba8015158a403400c0c2424080c9001e0700d040f04c002c1c02d5404540c400403003807103140d80c00b000b80d9005008254003400c4680192a0411000201d0121a006803001280d4528400e00807009861010071400568004a40c24001e00051329824040603412404440c0460312451000c0303c090301c640d010b4600141091241c1c4034079100d032140e8002921103203501c5400d1010500c1e1446a84005040d40e050103881e08040c0740200b201e04e80080710f4401855511f2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 813968920 1250 813967670 813967681
    0x509131121100806090d030507021912030f2c010608010903020307060c0203091f0e030601060914090609042d06020403061b0207090209060909010b1b0115030605 71
    0x40c1034407081d0041d040ca00d1628022025440000c140489070355020340307101c02001440f0b20700410440e01680380c18003c1c00400070351810070b501800d00035100c607007140b00b13601e10f405003001c1c1c2c010480421351045142007074101402d040101650410024000d10f5031400030364601a181c80007210a29044941c40c40340d4500b0810f00d040d0040c03003940d102a00b10750070010024105540130000740342c40c6114070010000b0b4510b010040341c4d00c2c0140b01130160031107640d034540c0e8603500c1d8a1250f90320008051404054106280c0c0119062503030a1303000d0b8010614040c004d1007004010100c0e072242d41c1042d03a24005605c2d086001031810300014101403c080c0c50040c4c5840d26040240381d0350b171034025004560700c00d42002d15201c002544584815504646400191b0360085c10000418016031007d50040603801d08085c085002035208414040c1d00c120f04019800701511070048013802003018103052501d42c64072075200ba5004070b5000306c92513164900040d011250500942500a5076080b40c80001d41e40d0381e0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 813970170 1250 813968920 813968951
    0xd020306101d0f130f020403031101060503060f04081b060709230f0a08151005030c03102c0d0e0d0b0406090602090612060109060c0b0a0507091a0c01060501050913 72
    0x40300784e1400c0ea2801c0a82507914910181c00802c00c8920076520f100b4030340340c141c604034201d400038026103902d0b0b044100854000c18211440a400c01e02401071249003d030740c2e500002000030038000e02da106800c50020000c2580d0000b680600610003e0b0000804516409540080d05041c0c2001c611030780100b4a1441d00e0b803240c43c614000f50900300c0c2102c85120780750805200c00b810403140310122000d68a4040342d04e0402050070111140060010030b0610700041c410006007031428281c001c01c841c0601180a029051381440c015041847c0107051201b05100004042c0d411380b03000d0500400110840b04001501701c009584e00c5900480c000070191a00c0c0750541c0a8400d2011560344010f002c5039618441400c90020341c010a001d0b01e80c8022544d80700f900b6908010f52481c0504200d10400005101c0a0141c000960007030700c03854840503954480f0120480c0000c0d0400ca8401c81d00081419034044109104500152009080c00b500700b016020006014500c01e03840c24450b1512100120f151485 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 813971420 1250 813970170 813970189
    0x60f050907091a36130f06030b160509150a05040b07030e0306150d03050304020a031a0906060603010f361e1a0108040f080d020306101d0f 61
    0x1080144100c182464440c0341519070001c0302502c80f250f0f102104584c0c45440d400c0110f11444030444440d104030700c0501000b580d160100b8154031032503202d100c911110803040c46400003851289424411504150007a03a142c240112107100c00d1201c1041901c00e0b940c2c0381c4103200003090503080c0040c3d48104002c401c4809005a030b0190813101d1022640b40f04050b00038586402c02d0b8400d608a4030556148414154040303108148175401500b61010140824442c200550b44240082c1c14100c42d03c2e540c0c0d48000c00c2e480901c0c003d48030100264103016040b9002e0040d10703048002198140d0840d4101009401041228440c500400c1130b01684041c0f0070303041e503901e60b06144a0010814401d445016100007030440c81117161102c00c0d1110000c1900002481000c042d0144e00709060310700000540152142c000c0034001751501410f9105050000d2010001428454410a0003680700d00b040790a003d0301096004580090100d141040b580c0c4e00d402c0c961b0388180070022502ca2102103213000c0400d04266 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 813972670 1250 813971420 813971429
    0x30b0f070302072f04050f130c050d06270512180316090f0504170309030409050c0409060b03091519090609030e150702010e041e0509060703060f05090709 68
    0x6058a00c1c00100c102e0340900030102c0c0303a000c0900104410090304005c00c95504460488650f0110760205078401800315481e40c0b245e03c179034640782c840c40c0c403440010b5803281d00c0403045405c40c0c1c6801d019600250130030500c50901100030b004050a50382d40d92400d84a018030427440c580e85002045558a4407201c014070301080308048e0640d0010100003c0c10b082d0100300f4029150b0a904080350714120800301d108191095801000c1c000c80122080f202800c0307940f018104141e00d1209020202e05030303030b5034031440e0700680c24030000c280c5e540e00e01000c40f801d0310b00c1d5512601f5582010f100f0018070440215051480444c01d080130800f9940d18080681203155000840491515003092882000507075440084414001d4507010001948003040044800c1010348541404000703200700740041d4080c2ea07107a000e403d0001d0010840c2070300401a54138a90f0a28511040281c650003032150009050016a400046525040c0900b0341802c42c40802400240f254034040d40c0468000b03600540716180200140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 813973920 1250 813972670 813972683
    0x304021807110f0c01050403060b0f1905030d050f0d0518032a060603030a080406021c02071112031e0c0d0206070e03010b0907030b0d0b130b060a030b0f07030207 71
    0x2410660401025524110b040103520b1051940800c1c144800060034080c1580596485160508580d2804090520002c205411030510400005581e6400300410b0300c1000c48045085c0c058500810580f90416520500050100800110701007410704800c4a059000040c2e021a060301c40c1032560b002910000250b640a000100d03820b440305400403101c28034407403d40000101407200051070707074440d0b505540880d0326074810040c421385c441c000c0d81410341c850b001e20401828400450002880c89160000ba1017425600091480401001106c805070184007540c00e0000b0100602070f05076a0f00c1341c030281d920940c14402e42109529426401c81c0e41c5441c2d40e10960b82003440b0100040d5031400280c1e00c51011a41e0301c01523003006d00301481a00006180188008001c1d00c80640c01c3e00100314040e2003980000c0c040c2d400001066841d00814003440164040001c12002402d018884e904080c0c4141c1c854441c801e0108041404010340d190450080b800c0c2111988813228180c00902c0b410380b004048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 813975170 1250 813973920 813973969
    0x9030c1212062e11070f06081303110607050403060f05010302090c18040f0203040507120203100c0203160308150f100e01050d0905010b10050703080a05150409050d03062306030402 79
    0x615032102102c4200800300046079460360f12254060202c86d51405150001110a800164071000403100e0328100c90203420000d24021030441600d052440c01c8440070f020401c009403c000b007042070301c40d49a014040c6d000400903541140e0001e031101c00c02a048240b01030010170600350081021032403285418000300104002260307e09010041d42040b00c094500e401066070002d50001001004801c0c1c1d81e00901601107205d503011004024080140c4840861100f4000041e03960349c0650070100c41c50003a00c0740403161611190301d052405640c500d41e4010704010403206403039100d80082005292240c10b10f041e2a403841801207d4038060701300d110302600d08008024050080640c008132400d1030540314018140310612080d120751154501c01000500c0baa000210925019801076401c0075404104031014240c0c0c400103000d80344130003805d4441b40c1010340c0d041c00040e01803107408001e040141500c0141e80b641c000c3c0302d03210140c9003081340c081d0f08000b000904640e580201d0701410312400d181d48a8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 813976420 1250 813975170 813975259
    0x503010515240706020a0e0603070c0b150612040f02060706050a0b151e0c0312011e21060b040f05070e06130b0c0307080309030c121206 60
    0x5556075060301e4503024082140030a55012440301e07664120312a654181c80c074156051380c450b03009610100084c410825000c2180e80c1650704c0900440c092812691a592000c90a05110700f201d01c02400d1138581080720000d0f0300d81e903280d840a0702c6100546001c4450035545600340007180001d410002980242e00103088820014035034070260060b03920f89010030012640f5002c1c8000741c00458005a0b00b10800e101460400d421407026400300081d40e8451820301280301e42481c51600328141140891445600621804540340f4540d092186590318160390280703451000000c0c101503525800311081c604504000388900d41e00210036050029108000020780040b204000305025640d100020b45014510036036072601d00c1c26160001600d1400405c20740c6480c0c01100c0360741c0000c2041c202c1d400144038070301c041461074029521400030140a16a0340840210b01420a0a0700820034241c1d0000d0000c40b19000b8081511680b148083e1500401861003504401d00030311307070801900d04841540080701 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 813977670 1250 813976420 813976441
    0x130602030c0609010501030804120f200f0303040509041205070804030807110409081c090209130201090602010203010b090d0f170901030b030105040213021c14041202011401050f0301020405030105 86
    0x2000c550880c181c1c0c142d900d508000c0f40c00d8a03400c1c440034005040600081c0a00d5841c0c4541440c400d10550011403a90702603500c010348002c001350745141d40764100500c400d030f81c208840c941180c030b0300c00c501440c901410072000612840f40580003518011003501140306190080d011100c0640d0440030881e103a99070f07450154555403100d0700884458010340d00f8210903046c00e0151000103030b800075820b030070060104800709902038513184c68510152150300c44009030300c0d08807801d4043d86842c0c42c00000c9a03d03600004d0b0a20615074040c0c1c0c01c681c0b040004100a40c04002601c5202c1c07411141d0814062142c24030003d00d00600c14050f103500681418600714003190001403550b1035081c0c80a000d908041d0003090300300c480454008c0d4010307500400010a040c4254010507a002140d01c2c180c0c01d02c68141441e0f0121034007551040b559040301d80600040c40302e000442d003560002c0307100031700c00c0000400703401d42003180c184503c0b401881c60480c100883d030307003c1d01598003801010b4000c10a91400180d0107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 813978920 1250 813977670 813977677
    0x605150306030d26040f061a0a03031b02040f02030405190b01031b05030d0201060501080901090c030b130b010308040819110f0102030f12150a0f1a070c061101051609050d0813060203 80
    0x1286c10314075205203c1200c41c6401300c0234414000c0101541c0501d842c41c0c030b00303441e00300a01049448580554102400503601c2d842420311141348030f0750041e12841d1500d0700900d82801c9010040615803040c1c1c010000950624000d4156a8046407107500c442100c80051070300e070016040b166240c02035484101c000340e8151320100485100f66150b0b0615102e00722000d00301c854048000d231103c0c0c80b004013400481d080c040c42507000030f03800010400d0051207446003488d4003001e820440d5907900004041100d034070201700000a00d1034207240d9075141d0340d481e80c9080e162600001068080d071101a01c0c2302c116070091040d0b502c41403030038071055981c1380481005441908100c4008030325075507a50401c0828201a075001042d2408036080352130660030050454080c0700d8240101d000c201c01001003100150300300e4612001441a0707150f140441c408914401d0070350700c1c001c01e400e6000c0340386070600c9404d82d0b124800344203c071010384542da488130407404c200100d0f2184410321070900d050500001840c99000008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 813980170 1250 813978920 813978923
    0x3090d020115061211041e0303020d090f120501090606060e21060f090111120a14060319140618070e0106050403150b130605150306030d26040f 63
    0xc205000404541c90710803070301d42c0201d0700010341c5412000ea040c03400e1703888541c1078280d44124034281903540c203e04500c00741d80d500c0d010403114484000c10400d40c04120138101d101d49800c20000960a10041a411104512410074041040400c09080c090290700900880b604038005010340d41d200c98002c0c00c0354024810150046444508400421003002d540008a01c9058046c003030b20385070030703012211081001d03160ba0004e550f00c1c00d01490b00d00b81500104510001815084050b00e00001740508035100b2009180b0186803000030442507a0700840c600301c1c1070580d000000101c0b411410070f5812000411601d0103d84601c02c184401030070500e0311300200000c2c0208a95126803510000900c10340e0a00c61580410014041400010391440c04241c0d0140c44104c001040c080090004e02040303503140302c0e207004a81c5d0b00f03403e101908050704480701210208038068594104007000c2507440304d09810000c104042003806650000c02038000c200c104d4811f152071140d80c03e103810500c4c00001368880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 813981420 1250 813980170 813980173
    0x70f0f061d0c0f09060103110c03130e070c110105031506040902071407030b1506071a0402010f0906211b0e010f0c03230c03131a09060711130203090d02 67
    0x261408500c3c0241501009490160481c6195101e03040158040c3c0801864802c1d220410b0180d55540d0f002040645580954001810200c92418100501180000d0100c030304010300780554001041d80d003121185e03404002e18000d9501e41c1c030020301c41c006d5030401c0d02480d444140060000341044954011700140c134010b44000c01c6408070303040e0b1a980c0d02810312004059071816000290340301e039039080100c48000090852440c10f00141c2c0e9a08000f001c0740000c0c074040c8800300030300081d940d003c101c25810074001d0901d00b01060411030301604000000c030804d140c003a18400384120b8582d96810110900c0211806c42d5040314641c140588404010703040c0d140004d00b0800c1c0341d9045481030848000c0540c01d0303100c440b19005415901c152a03024594000302e210307010401c20103c04070410050200d640000000b140d62400c002c0b404c6d82d0b80455000502c00040284441d0310165250300841e4400c9a211030703040711070300480001c00c4d005c0640100b1103011600c0402049031482010502001003002c1c1d60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 813982670 1250 813981420 813981433
    0x30f071d0606030f31050a140102030c1602040908040b0d0f06031101030c022802130b09070507050109020a0303080a05090a1110110a06020703081803070f0f061d 71
    0x10180541400102d4510074140107440200b9105108000d03184000744940346801c0314030b80005d4205404064010003200d031035100d190400184101700341c1c450019407a6030020340c40d501380809240703c40c1c0280c0007034041c14805013000e0411036507030313502128000364001a00c580796a5600c0450040e81c010010802c9214100007145010150510400c82038030340c4844200c0384074003507000440c024074404405000f94420b81400240d411840416081180d4490b03494800c101800e01c1480400403000107200340250501180794001e45c0c61034901039024640e031510700d40b01c1505003401800b40841c07801c040c1d0061030084010007410351144c10184038a5242c00309102d90303221035015940c0c85210050143c03034288c88100d0346a035440c2000000200344100d01d480c010304040e90158a04040d012102121000d500041070800c05411651490f80400b42240000800c09021100b075107074484c0010080c414100d00400300d0030082d8501c1084016030300010b04100d544055035411800000d0664003502310321521 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 813983920 1250 813982670 813982681
    0x1b11160914090304030201050301120f1a1617070f021c020309150c0a0204180821011505030f180a1a1f05040b0105070b0a0c030c0801050d11030f071d 66
    0x3c2220100c907410380d5142e181d07a18000b945070740032801210454015000003684004a0b20084202000d00a03c00e80340c1206d04040c1d01c02c05000c01c00c21024802d001c9202086d40324031416104c4150300c0070712810403001c05a54000101d0a090880840a1043c2d00400c04100f441e0b030300001070000c000e01655034510000d20b50401540c03c1c0249102c2c00c5c3c4503800703e040c2c0d10040c103003034010001005080d40018454045c66460302d05542003014101102d800200c001c0034542103441e509130040010a00d0b03001501039008000b40588001468103440c1400354002c1442d2106034080e030f086001015081d00c0c5003c2d103071b20b08072a41c60741a10350103946112603804034024045641187c040700034010724902e003142c50070b000d210162001d410710f1030610205105010200d00c0081c80f00340700f0301e104540002c7c4078006030005000c60f41102103840c100b0001200500040e201c02e080f071942240c0000e000e0749241c04081c0081e262250342d041c1d100f03032801000d0002420000c0b44400c000d54002440404510b50341e003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 813985170 1250 813983920 813983923
    0x11b02160f08030901030c031d162403091b0b0d0510050303220f030f1e08030f0a0e0709020d0609020a050901080903040330031b1116091409 62
    0x182c1c00795000e00e41081010b0040c941c0280e0100c140c41c881c5090202c3d1421160700182460780d40c3c01001d10854018140300c040c05004000288050f00c0e02d10512514161503185044040d05580c0074a01803643d104010010705c0024280000104500300b203a144007a101e502c4600a50440700c1a4940d2504100100c0c0100c020501c42d40f0590380c004d001907007009515500611410301440a408041c00820300100d040c5c10010700e0b10b405580218401c81d0032082034a00030545041019400b40203140c5850b440740040d0300d00045035040222615240c803640c03201d640b45001002808090f141c607110b0350b900041d1444003900a0801020710341d504100995031071035850203911031050709100040041213084510360007488001d42001104080b2400c19807255a401c031030308114042802c40901c200d400c440a1041c41e0781310842c00b1030924040c4a4441c030041900b02c01c40c5410703803042c20720042004808420000304940248005000c0c98201c443e540c400d4824018400a406649003078101030004201150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 813986420 1250 813985170 813985199
    0x309150e04020301060536060a030e071412060103120c050c0405090105100f050a0e0c04180b1c0f0209130204090c1e060f050d062c0109060308040314011b0216 70
    0xb003034001c2101c0300100c7e104101d032076070209003880e0a01d40e03604405040080c040100d40c1c007404105201100d103980e41d600300f01d0046880c001c01500d9a00102c0140001414809064092251400c200c40e0002861418500f851185114150840d2a2500b000b01000781500981c0c040d121413411040b40c2c50b292101152069101c0c01296040380c0304960403c5801005248261301c1034800d040d25003003070307190030480480002110402c2c21042d160202c0503824500003140300d0010361403000030740300241140d0340c0c1c090b586180c0746e000c1e00c2450071200065800e090701003c40c3d01e06500134001c0107405207900c0c01c040c2e04111402540308112007040212211400f018080050314942c0c0c6560018440c4203008840d42c1d40519030f0400da65840380d500003020308032713000f0f45141040480c0643c40c803190004403165007914141c0c0240f41c0c0c1824500c0400c0491040c6049034103903600110b40c12920300c00701d09414003414050b4034100005002e031008210300780d07003c40c410b443d410f03000702c05a696903a07402070001e0401c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 813987670 1250 813986420 813986497
    0x10207030c26031924030309060e0108061201020408011401150e220912050a020c0f0a03140c09100e3d0e091006050402070309150e040203010605 64
    0x1200b003010a84148000c00d02c1c106001810401040f401011040000c05c3d01d2040b6242c91090000b031003c1c4101508131000340043c006901e408050403951a000900e01c4101405071406001d1407034070303525508001c0d01203402820300c2c040240410b040d61402e40c0785e407100034403c0d510300d4000248952000740c81100b01c0c401d0309100400c1740340d002440e12a001e208c0041d00c01e40d400200d541c0c904950004240c0c3c40003550303040d150389441d91030b8500500064280030480c00030a10918501514200a81d034550080058139040400c0d20710301640b486840c0c1c031700314000791519404010b0000b000410034182d8001740580b040e10300c506080740c4a84412800400c02c148060740c45980c00220415046900d0f16814000415403510f1810259582c1e40b00d40d101a090b102030005800c0080c00c0007054059024810080c40140c804500d000f986d518014141d441d2402400c12070300051886010292180d0810002c020008004541d40d5030b48844c09042c81d800040c0c40704000c3c507015480b010b1084030301c900801c2c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 813988920 1250 813987670 813987743
    0x2809080c040e06041b030524070f120e070f0b041802030c041802120415060807081c0207030c060201090b0717040605061206010e01030512040f0603020d020c010207030c 74
    0x792100c0d035440c1881c20141251121715200e044000020450410034400c00d000300f142c1d200034413010081d001c2511440104988144140c03102c0c26401d107540030740c0020241950b034800003200d00052000300c1c180040b661010b140c0c90740410f00810784281c020001d00c100e0705603e48120010054810000580c0000c80300a001d100c01404104141241f00d000c1000c1c6248440005180110b5024032171400101a40d0688540e40144c03910090708401e40300b6800a406007070001d02055280c20000c90b528203452915030b500c121004501510240200301c890301541d0701550b02400980c80700302c000c3c001c1c00d41010a03504140854086403003035004542c0081e001e0b01c08980c000050f80c80e626500040d200140078103030815803400d002c2401c22000c0c05494060300011a00a40a51450824514060701007028000000003048100031307525007801c081c1c003241c10904001d41c03241030030440c000080c025141c9504a6500001d001401c1603800307500542e40502c81e41103503001c0c01044e648090804800900900300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 813990170 1250 813988920 813988933
    0x11060405210138040230010f05030c0f1f0c050c061612020c150306030f030f070b04050307080406020d030c0f022e06032609010804082809080c040e 65
    0x41c00030a0010f080407110252000d8a00400c81003c0c88006882082c08207028485601c003040c202c90030350019006002000294220fa0b0600380026215140d6180f0f0720700c07a480016814546449000c1250f44061180703020310851111018003038111011500225054001c2c0c1c00040e8044c9405000d076991901c4401d160000b44503103540741000c0e00f181c500848290f11410301c2036041b84d61069100342c200407030480020746074200340d4145450030840c0041c880c0590418000303402010b0b50041520b401039003142881e11745480d6800d0450561003108006031100e03c0c0000e0110310907400180b0b045806646540c10070500020300700850304245010414001a00b202040c000120408105004003072580040284c1038072107290b0305011966154421140298110703040c0d261103000b02d006514580e01d00200b80c0c03820101e075000800860006000406a2901043c01606190a0081e041460030802c4446140301c00400c0086c3c00c018042c46110000d10036114001e0290505021300004204440300802d203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 813991420 1250 813990170 813990251
    0x9140f043605010b190e040516060c0302010b040932030d06061e080712020405030106090e06070e030a030804080702032d030f040603200f09040b090f04110604052101 73
    0x1b41020141094a00f072003080079045102109043c030500074403003038031100503a40251502a080d01c400c2c04a152265141040500210f0000c0084078070340030301402e0352030000500e400a407d9030700701c1c40b580040302d10010540900e00300d0b003540202d040d1985038441030000e140c42d00222444950589807180060034650100d00c1c40d9000f001c02003d4645030f0079026040076220300c0800e0861f4483e621150b40b280e11901d40d07000f5104280032490300000ca9141c000e04c00030310140480c2d61402030a00042c2001070400000d41171043c05000d480d440c96008098800360b08000d5082010183c02c0d080e0700a01035540e01001011003400000c40d0414030b0480c40352410940b4058080d002001004852107040c048064421400d203412001804285030300150561a000300030103000480b1120303955a40110469428400d140c11241080782d48a0741c0a0409444580c40c01c000c2461070213194425a0400040c040d2081207065400174540e0306003964000300318000881310a59821603e010440c01d0f60703800d000f43c812 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 813992670 1250 813991420 813991439
    0x105120613060b18130b2a030a020d02030a06081e0c12120403380f040c0b0c030d0e0601060903032d02010c09140f043605010b19 57
    0x2d02d1488004e06500610616a21a216600040301c50454801910304200d0402041c4600a0b800031543e0100d030200e42640e40806940f4003002c01e045c0080d080c00300000c2d00c0598103404a528125900c02c0c1035403282040c64080c4080c00f52802101002d000d00e1440d032941e080100b4032210048040e2005240701440d031f106011790000024032000e400d010340941c41c0c0030100341c0d5000b013000318480c0d14142e011140c3c01c9141d062285022074200c0c4d0f500c1c0381c501606074446200c6c5605d504805d5001a0603c11780740c2d8035254203201110743c07150f01d0342c84011032403003074000f400700160402c4d43c05a0400e02c86141a0b01c440360310b4150900608004c150b908005002107403142c00c0d03029400f0300401c034506100030321044560b40c56440b541c1e610010323910344640c001e1960380321004400909841c0c01101d010101e0f0000250041105585540629a00d0310080759035804001480c3c1140460082600d000102c1c040c41a001540e040c01078540350b080584072189810000030f04c559843e1203007022201942040e8050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 813993920 1250 813992670 813992681
    0x1050d020708040806040506251d01020115150e0d1e05010e010216051624020102160c06090b0a0c08030916060905100306080c010507031e030203010512061306 70
    0x2a50b08031024000410b0000b820003059000f28040c80050240b840d00d9217000700169a0909120440021580c8110065800c95017907001d1800904040d204214900c004074010b0110140790000da905000000601c001e41810002c003840840e9221520303000303400c0a00c044003201c0c55000b8408400c0c044401e050b41c1c4e183e10b96102c40761040b0004035110b903402141909907013041a10f80e4018125071804030802c481040302c0810a8420503182944601d049600341d03290011140d82c51384c800c041c280203007603540b0030341c100c8504541003861100c14440c075007003020b419903031409074030045182c0c010085134013030b090001d0b00c0d00c0014540d115200c0c4203159548110382d0f040505079a06500c80c1c102d40900300c51001d10000c0190240d07980b8000220b15000400c0405003900724803400780f42c6401e006114030b140107d600400c500081c2030195640185107000c07030708202e02c05500c4102c0c0034084405401d080c0e040c2c009504a400071074404c0341400603480300a864000540e00382051600c031003144400a04c01d81c100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 813995170 1250 813993920 813993923
    0x60307030f0c09060b0a090504151703040e0414010c05160f020607020402030f0403080c131401110303010e040c0e07050319061203020a0b090105010f030f050c040f020a0807050901050d0207 83
    0x100e142203039126003032001d84119421284210001240025180d0303401f88801009203822203003400a4440d03a009030010030070a024000b50164808001710f00c2d503a04004030740040407403014403070061410f410400080e5100342140030065091a40b80ea03200c2d485030b4180d6070b220f00d240e41c0d129968501aa9041131031500040204d81081003030020340096525403000c4c5100e0000071070348440c0743c50b03d4076000302154030041c03040756010780034022500d0f0110401004c1c01030381c0400161869450100005813134003000c0114900d0580320010011801d540c0411200e8020343c440c9106012031501d94208170f00e030a80860b20781c400250180700040380c0b0b0000313224080740060036540026034980c8448001440c1d0380e80100a6000d81d201c164208104203024801039440071482000300001d5061540c0740081c0c13001c5200242010500c05084801d100040c8444003ea080c020300c108002d41411204201039000403541ca00841d001c94001070100d4011402c0f81c00810b0146d441e140f5003ca210308080094100050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 813996420 1250 813995170 813995183
    0x609041709240304060f020c0c010e06121303081617190f060e0f040c120519030801090f0b06030105120a020d080c10060b07021c050706080915060307030f 68
    0x2641c10001c400740e0020441d8030000b24901d642c9140c281801410345082640c3c00b21524410018481c0d000004036a030704d180d040034640f00c2c40c0714209200098031402080d040050401c454070a01444001754102c01e40300310300c02c1e10350224070f42d0b40c0f22100b031140541000381c0c0085540c0e1001116000295144290700c220032001d0311950340b40984a200442e004917428211841e82c0d11410702c0091200021907900c240007008d4a0420701c0e1560303c0440c0c101c0d040c03080c0b6040649555a140400c1010b012444c210800782040040000c16810000d181c140207104045e803052600131200a0703840b2500030074a6024000d071030b0a00c0e5920b0002031001e410349a4001d9000780c082c03d91003900681d203007041804034134020f01c07440b9200c1081000c05410310029842042c92685000c80c10030440c3e000318156040305804480948603815420740030041110040c500030300900460b980440c1b1140c002c002c5034002c0b542c44c811100540440028400703100000d84449030f05601280d0204002001485d00151031480ac01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 813997670 1250 813996420 813996439
    0x601060c0b07140d1a0a080f030f03060a150905010e0609011719110a09060801080d030504080412210e0307090f020f03070c031206050d060e071502070801050609041709 74
    0x114140c04482c81d030440424094080855180d10381b40c0100031703002a00414002c6d01c5140341c8000c03c2c0e0754a110b500901010311402100007107856a03813102c078800801452091600f030007095540104080483c0c051280403c00a0455402c90f04221056409025060b112142c0c150110000c80700302c010002c1100d50113403004003d01d40c080c0b030280280300741185500c03241611814140400f901c2c600c1550802020040d0101c01001854000941541542514140042c0580b25820306500c94800c1d0f4001040c1705040020030010005094050700d40109441447c0b00400904201201c0007600ca0038071690551003e0800d01c0619901e5118464041803441d0061402044051400c52500f00300c882c24007048500304000d00f41078003d07d0103070100c0703020300080141c1e5041c600021007072714a901014041c25a00d003012644810108203c102500705000203c0c0c0340c801c2c04600a41c3c032007060080c02e07595401d00700851715900b00780c42654015580042c0e20100c0c804460706035500e40d000704030718036030104c0000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 813998920 1250 813997670 813997687
    0x9060f04060603051e0708150d1709190b0a1d190303020105010b0f0d090213150504060902030115050a030b06041d090a0804091806050c030402030601060c0b0714 71
    0x14400d601c014410741e01e000c6000d242000e41c11020050101641072008141001c00c1445da5000c807840380c0c410100b01c840e810091201c000b00c1d81d0910600710042100466048504220b82d03c1409044068011241008140d2903008010048242849203000e090001c1c04103554060040030255003050415089814103a5141c0001c2c09408800030b0380c038a107019516003032003415828052240989415090140340004015001c525849072029640c1c440b90755a05000c119a5404211390440c1c01c19107050105400f643d021040300400c1d0311030984118607141c000520301c6443d0003541d04844031071419100c00900d002058800d0762000048504040c1c0d204807400c0b2035580c20000d0b001402c51080303065000c1a028000031a1160080d009000c180c0c051560400001e9a0200b15400e658060002043c18044c9520300800c4002c041c10043c4082d00381010010310718501c801071031082e03008504903011a42d89000c140e45000c15404090a25107140340052a254018040829001c035412001c81c548000c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 814000170 1250 813998920 813998929
    0x91302070206040312020f0d081513060f091410060309051207030e04061d0105011808010e030a1b030c0b04020d0f03081515070b0901090210020705011403130209060f 73
    0x9404c100c82403040c3c551088115a130421522480203045801003400711608000030340300c0c2500a202900846100d0030070740903034541400e08040b01c2c1c9006014443d103522281c0d101d200c626240100c40504e45440303151420442c407001d405009100c0c1c4818401c045040180440c041c00300100103903610300c140e402c41144294823400030250300f4000d907038401d00341c01001c040000ba1101d03a07000d1202140c0402c2207014208400c1011811200c007404d202071034001c1502d5800d07059003554403030400c0d54640a402c881142d00440141050540c0d6581e581401da0310114008032a04890000f1b80011408030003440000e00086004d82c000b40024020b158403003443e41c462031813904501045000a03070301d10a01001c40c45004920b10000c00803a03c410300400346010000350750281003000340c01d0703901c08004a4007400c800e5200d8040a41c0103850b40d20085101880a591101c142c4100303400a0b00050b4040b042100c080c06480c0147d1952100c030303203549000d40802032025800340060303910104040406259548 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 814001420 1250 814000170 814000177
    0x3070b0304030c150902090f33040e070f0b070305070822050402092808060f010e0a0605060a1805090a0e0f0a050d0f050903150109150308091302070206 67
    0x11942d210f0386a802d81e403402d4101a0708080665000c4c070304084c0c039080180d82da12007955000100d515081c400381d0300c02202a4110381102040c00f2600c1249049245180060150720070700c8005807418098203040b455003070741c0c0e1421407180d04d50a031140d510034000340d118140101200c0d4003900c0d009043c1380b00380d140c0701c00310b40c03040380e498400030b03082da001601041c1800c1e04d0600030402260308504042a0342c01040c00c011400354a04e00b620740d140f4111010b5020201400098001001101c00520388907910040221003030243c400f11200d400c00003081e611040c024802600c6010b4a010f00301200c106054600710540480000340d0354150324007054a49461201621804054101107641e840070901c0c2390420441c00500740c0079400820300b403008100005802d1081041c545440100d281820f481102c0b1800b0707116441d030303060088038426040410100382190603501c2d400350170415501d140c110248080324034032008151180901001555213450301e0048a41009091701615002099000400380e50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 814002670 1250 814001420 814001423
    0x1f06030203070314070e1318080307110d05190509030109051c080c1b0321010302210d050a12091208060607080418021b01091403040f0509040203070b0304 68
    0x2a400700802c503586a060150b80241c509004a61041d81841d1034010000c00c20102100d000710b07400b2904028160180d8032018090307a40958803c403c21007403034007401961042d6034842c00104000030810b80484045007100140825407a00c41c82c1030081c8018843d5103402503941c0c2e007405000d2080307591989080c0205803500b0f110f84040c05404000d00c041d0440388810012076010010203d04000c10300001d04210380d0002a15081000d44d20450300010b441e510a075035401f8050420219504020550700107414142c0380708498954140c80e21818001c806000030a800e50a07034400c0000058080c05500100600034032480c1950300c0d00b030102d0a010558001c444107c1e6820041d98000c2c5100d94080d08154014000b2208589003400e16221454240540c0c060700340c00c01c1308524841034012550341250702c1840011800c080100003400d01500905440c42e041e180e005034103d10b10f8510310040300312000e0301d03850301001c42014200014480c18100080080786c0501c10614041401d20380c4c80301031407183c0e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 814003920 1250 814002670 814002677
    0x6030513060e101a0a03020f0303092806050a081807081203090d0c020303071104091e020301060602030c1e07091113090c0e010807030b04053102090f1f06 68
    0x141c0c0080341400c00c0f42c003024403251948040c0c4c50001190360340c41140303c04032a011150300086401007000030f4190310400c3c001d2a888400c180a504615452611760101d00c8205070301081240da441070240c0d0f0741c0c4185503013100000c00c20300004207030300d41e410394550400ca09141207580141c3c4504506180080180c0c030805d59607008010000c01141c03c016401d02e0440514049001d29555404a41d030703400b50640080451703028440000654a4a6200d06075242d08203000c7c1c0850106000e050420720201c0c41d0076030213942028030204282c0d000000b1505c0c4003c0e014001c100c8903501001c91402c034141090042e0140c0200180050b1a11303440c010300301c1c60001c44180c1583c5904100c0d5904203a8a10b5000e0b403502c50504905900300ca4005c211079074610002c0c02e21000c9030fa01e42d40102c2c01008155441507103e440c09090160b0748403900c20191410b825079031100004060b125495648100491000754081e8a00f8006509490b519078203640180b8144032507001301d514400034903901070940d04181e000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 814005170 1250 814003920 814003933
    0x31103040e180a29010f0302060703080a0e0a06020a033605010605031204080706080f0c0a020115090c091205120702060d020a170f16050901020f03070506010e0606120106030513060e 80
    0x113400c040f4076280c0181540080f100b42c082ca140e001c1540c60041d00c1015080c0102ea500050000c11540c011600301111102039550b0b003101464820025000fa4132244006482c052581043c60b0b00203e03a015201448600c00402140c4451f032503080c00014501100e80d5525000002a00d440401c1424603007000c1c11703403075074895041400040c51f05415074002401c101800050115440d140c80031280c0154181d5600340e0344030001c0005a02422562604c4100368940c0900043d443c9500d40c09080442400c2d910007242a55507091481c011100f4240a0700d41d4110f10495400100080020082e0713520144c11340381032142c0e0103c41800ca8001400620201c0c10340150301e00141d5627241010b9114032409074110359820a69194440100c80718602020b000002640e5401680208910750b00201c0d00411250f640780d4614085845071001e100300780b4003102000c0030500300c2c034082d416203080c06040d181040c0560b1802000b00d006e024040c19000450742c3c96803c48021070550b01503092804501d5000740750 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 814006420 1250 814005170 814005233
    0xb0c010608060a14071b060b0a0e07030c020708010207030e0f0a03080403140705040e100902010909090312060603060312030504060b06030103080c060f1302060f120112031103040e180a 81
    0x390944c02003182040140d001e00760040c00c0401424900101d03000003000400401450100c0c03080c01e0550004a008580c4004002086905800c03480400703500d58282d400c41692202c486090f80a14100107010800042c40c10019081108070451030785001002c00c61150b64a44400c6204c1d802900140c1e40a1a291051060440f00b00495802000b041e01e00b0004544103003084da031121021214404011340b07031000d40096a00c40c41c2010007411105004101c046060300c1c0240055081d0610264074504090380007691501034862082101e4102c0441c1c0e81d885002c5404900410006008aa0050340da407a503a5460311100c0155018512a0240a07a101000705855280c45802044810350f56028410081e40c1c032600d4240d180180e9050300c481d0b4580b03400020f101018001d412008180304450000010700c0305528803150400d0b8020784a0810308102000c0d43c0b41c0701d110340d008001c1c00c60071250215110802500301c000c08114400103035840280c2581e1241c00002280300280d50896103590a0350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 814007670 1250 814006420 814006451
    0x27121c0c020a05010e1515150c07080601140907080903040815010311120304091d0109060605100512070509060909010906140a081b0604090507021e0d02070b0c010608060a 75
    0x1174070810800141124005140381c6004480c0007042c0c400f0600c0ca504900345203445000154400c2c181c0f002d403254580401400c51903130b4000a105604031032140000010395404200b04c02d0312080000740c64010715130345486080e2001c1c0b2002d0441201c5110410000445000074012041070500c0940324a669505d9400c0c801548000c9031542c4d4851540d0070390300001c071080081190101d54425074042600072000c9407041041c1d601c0100c124007542882010001c0000fa90320100556001320741e84003214405143c121030b2402a40c030b81340380048103080030030b016a0254028040380c10f0024102ea01d0031400002140301507200303078001820355858400071b2103030614020800883e9503099070003030f40052030521440e41d030f0420060780c81002500809165030303e89907881101d001d450345640c140300a00b01094000d40d83d9201c0100080303400911560799040c1d2001241d140362907240365000b00882820088046069480b50440d41015941c07800000b501000900000b031161070074580002d00d0352015403008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 814008920 1250 814007670 814007681
    0xf1003052406060309070911040302060d0c0306080a151815050a0b03011401050f041b020f1005164e05040b1902040302060409020327121c0c020a0501 66
    0x70f2045205000704860118001030500450740b0069010425503440c030320a16552190350406500700b1800128904403900c3d070780000300c43c014650f60030800291f440f01c4142c1c032005101002044103080754428200c01a0541140c21a000d00c100d4140e40000203540300301e40351182a288104642d125400c100b0b80c9081e0b41b1a4440320842a00284041d410440d401000b80c441401031038800c03a215808485c50380c40d20f034040c000a02c2144800d96501c00701c040300bc0c2d44c8076204010b03005544200300328985800d8440c002c980c00b980306064039101480c0d00810a8811403404003000d080800f468061204041c001c1903c203940711202d4259409851103508201c040f5071003a080450b115041805110008040c00f4035190b024460403900340c1e50342041c8428202078411030388040d6018401180115010180e54010750250281001d441c00000030610500884814500740414030b81000074510700006203803009080a9010058501c204000d0880c2c2c0e100b05c40c40e000c466030069001c0d0003030700100b040901c00c2c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 814010170 1250 814008920 814008931
    0x9020a08040c14031e0a06060e0f010b07021302031302041d160b160501060302030106151107030201050f0d0b091527010501030e030d060623030f0f10030524 69
    0x5003060350f00c00008265988022421040c140f402e89650113800101405140400c0e075000905010540e41d55042940c1808265503210103a4612400016843c0d0040c044400c03040d03024085580c9960f000b60201c00a4000404019031402001c5036500180c2c0c80f8800c80082150050748000051108031500789043f0400e5001ea01c20b511204050214008036001d8038444180380301e01a541001d907241050140680751b10094056007002000f0500c0400003889000c2c4404030b0359455440710080740a01d0352100b603031201a01185081003a141d8050559004040029100c42c02042c4c00d0560070100e54401c07021200343c10702d40400b64a0855074034120113074905409215240d200500345400031940560018400e05042c160780d801240d280340b0b01403064030458442284200700d110f07960180500b8a4000b480e038040f4482d480b50711001d030000743d201034a0003003c00c20100b251a6072405000d26100c0f5010f0040020907910400010000d141080010989400c145102c0c91914003d4421440081c001d402c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 814011420 1250 814010170 814010189
    0x10b0d06060f061418011205190507021906050a180c051215060f0a09020d060807151b050c120102071a010303020c0d08040f0801060e061c1b09020a08040c 68
    0xb884801200c0d13200a0b14640d03807400d40000046501800146c0300c0414a51625200600b400d04110420b521100780d0020383c071800c4018040340d520f540e4103d0316155001030342c00741403078080b4840c004510070740d010075408081c500b00003030006246c22000c0382440c130614003100c55041d20711081c09103044c091440400a43d44000401c1c508a86d07c200d1b481e00e01c0000c0c000e074080d111082c000819a0703600e6010740001c0101c810b003150784e03100100d0017038040c0200d0f014200036841030039000185155008205032020100c3d550b10030411003030b22411401c01361090002d50b118442c0c64650bd00c070342d0312400c400c0110000076000603940c80c218506108000782800701407204d408594010000b180d00840c01406000d0700b110402301004040c90104024095604905a440310117a0041003201c01540305a00b075510304441d02c412641c0780c000b00079401826541c031003a0780348844228400509050481000b10001d496000c50f070b1501c5000b03010487c0c00c012848000900c280042c0020301ca40115100054a451003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 814012670 1250 814011420 814011437
    0x2030d060806041b120b0403051611400b031914030301180b030a061803030f1109010516050d030f0506180c090406051206161d12010b0d06060f06 64
    0x80c17042000d84074840e00034060301c1100c00007a0415101700210b8030039821044010f40321001c03604015882401d5100c0060186000107895000304040729011414511040061030310251507402285d0a094070340c2c20311040980f60014640140d4003403200040c2c800340d40a200c480620141010048854040d14240030382c1c0042006004205415503001e180c020302400208003c206030300860b1400400100191826241c20004496151031185140d00c141c0650380a014652011540e041240c00003004400040d00800ca4210954001c401406403010b01c80391048441440391911800c01c1c40310b180e01c81c0044e64074884150041410f01c247c070341241d01510784d1601c1d05c8641072028039419015090f040a8100404c1c0e1040c1e594842c2c01c580040c00014160321030500c82d090b540c541c2e448013910408403403007040304514070940c1324440031601c6032003000c035070b43c036107000d0f076050080d01021104444034075500c552400300141c450785443c400040c80b8000c000341c2e003072404a054a50b0300d182e8029404011024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 814013920 1250 814012670 814012679
    0xe120a05030f06190308031501170610090b04060816110a0b060d0c170706020f1504150218090603011a0603070903150c02160b0d050702030d060806041b 67
    0x40d0540b03501c40700d0049400761544420380000c0c8000e59441c0c8046805400e22008000c0190000145000b202075482c484c040d000c02030019540f01c040c0503450002203070048000b07892443c00c0c4401d0080300300c4d9402c1c45400c954070b07001c070000c03541d0180e0084008900702d202406900c039842c00e800390100000c1d00c1d0040300701100310709460701d070015010040c207490a0b041c041021542c440d420207585560101950200fa543c3e0110410540f00c0d00200490900403c0d40014032680003050402c0ba1041442c041d02d14600d42e00c9480907000c90180003038030806000b08400108420b0b510091107002500803020400400710810807a108600a100c24000e9042040b000500520b041c0180c9260100b2074045881f070361000c604417189200c0ba0310280c01c80e0121002001c002c03a0b81d41c014540a00703554203440100038240b01a007004803207485118a20401000724070340703604465101031380100075841501d140200a0031188103a4091744c08c0b40940d90040c20a01c010400a4a010510911f25a4910f100705152 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 814015170 1250 814013920 814013927
    0x70c0218070e0f011e03050f1617090c04060b0306120c01140c0f011e14190c0e2706190e040c0f0e0f1302060a1d090a0e120a 55
    0x79400010300943c03550014140741d82c001e2034910706190401d03102d42081d54518400402030502a0340e80086510700001207000c1841c4050080300806007500c0300291110003014107460150000d1002505008040451500380e8441c000c413402401d92952590b03d03401c04904000c003071100c405006d91035501c0032000303100e5660000c0c846e15402c16241c1d404d5440c1c3c140754203014204031600c0790f51b400c6946081d01c80400440c519003078207480f030000d500c1040892110400d00b0f001e101c047c1c1e006800405040101c4480e103020782c0025400c4d941a00d0310716030002c1d40b41c0c00b00724803201d03842500f090442d654204442d03031035a1494165101c0d6003204d03c030841d00d03500306e5010355506840c0202d61958a02c0c00c0000c0c00c4c08440081034006102040714044640da4070306415180103800c2e107600e8510380700140440c0003245443c01c0c07804101d80007403c4619101140b241602c0540000029100e8004460300049941d91080c0a03184204407030ba00c046a00300c2c0c8084501d050516800340d10400703080074010f07442c1c1c0951 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 814016420 1250 814015170 814015187
    0x6010806070c150e0717010605030307061a04060305100b01091206020a02033705121f0504020f070302070608090601150c02040c090e01060306050d0b130b070c021807 73
    0x29800c00c1503580140741007860441c501502003a8015003000703000b0913107a10020b00b02c41203c848034030300010145040310090a80d1030910625906510a110380c00c042507140d03201508411141c2580340d800c6600102050544007030b81e00c1590a5000070307040044068860040010910091a181d0607a900304a01d6580d03486030344030050011940442c059415500801c21269140d10382c8401420a001c0c071000b4035180765140303c20b641c180310741150072101c0074014000d60f150407401c440f070300019a40700b00303c44a0011002003030703842404620000243c0703070b100e92004041d840e02d004401c0da0303185010300b4040d1808407141d1050040000c002c1c104800f801e0081b821606441d4049110b0300c051594201c110360080c0c203041d002e90700c070340790007400038515400000e50802c9944070503200425a80e909000da04a41e040c0c4142a08401300900f02d000054003000d400e68880d2600d125400000c0d00c0703440b60071044004403412000314516503018825494245011350407055815070a04180c40c0c015030092680d80c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 814017670 1250 814016420 814016431
    0x405090c030a1d030310060512040201111002040f0e06010e01020a0323030702060411010e010c021201020f0304051f022107022a01120603083c180306010806 69
    0x580120214004640b1500500c108201c42005400c40d00c003041425074996005480c0d4294500352024005010b0340100150b50318044000c2d038800c483d0380c0710380064881880c0c0a020302654000d01c00010702a08291010340050031075044d0406800d400c0c085000018a4064095814010203080c2460b0b140c0c0c0c00111040304543c10301d49007c0322014105003600c0001843c0d500603142c507011040003205903000030220700c914020303a0a085040065001074401006940031940003800e121406400350611840d001090540c0c403000603d00500c4002a9545401c150b07000c071071075004000d220514541d0359a80e40181011400110700d003003090562030585181551102500d8a00400040d40440c000d1003012182c1e10a0840c50301510f00601c1c0d035009450044101c5404103001c19200724030b04500348603040560750700048403851310080c0741c00c141c0140c0001c1e0240780401d000c40d0f1a00c06814103a1650041c08812400aa446803000d085082100f500196081d01139444600100011710300001c41c00d8000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 814018920 1250 814017670 814017691
    0x30c03070612090b1602240c0708120a061802031003020409050322050a1e060e0d152910030b120102070c030507050a030b2202032a06040509 62
    0x20b603220003030000c1c0c140b8480c0500741c010100c04102d000918044011881e007115802d8442c45406411710801c04400319a4440c60000000009004504d1240050101502445585081000d8100480904402242c101540a48664041050814071101040044868241036003545420045a0106004c5110207403041e41c03120201070170b0020900807500c045600c1c440c980c0e80d041d484000081d5510a910802d401a0100100015404480003007002000103d090a032000d502d000e40441d0450408660954802040040130340007584911034045142c0c143d040104e03603121011020355540030301401d4842942d0f078040190700c0955800700d007044068494100000d80605620101e1002034608401401070740c4005902d00c10701604001d9101200d100794121040c09845e402402040c00461000070449110503003c51000c0d011a903003003566280391030400f2003c450303540000c2d04d40700d00f00070402d83e80341c01c481461454424000742c4007600c0006403200d0f460546803c1c0802c4002070002c0121914 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 814020170 1250 814018920 814018937
    0xe06090a1b05040f0b030c030c0f04020c0f06070f0801050609030c1504090f05190c0518011202030c0c0607030606051c020409020a36120f150b01030b030c030706 71
    0x80308074800e00405004054801c0201d40e20b1250010010410003118501c01c2c4a4418410344038580000d0884280358094030080c40704000b002808040d400c56000c0d03160034007a070091202c0c6d0340000c01481384651216a100071580440303680180c4034400c103800040c0a003504210200d021f8500041443c807000064503907440c000b06081401d40540a036800105401c1d00303100508143e1161a0801401101d51400162101440d03d402c1000c441d140d103081d10100c0d90030b000b0070800c52581c0c1c044107088141810f224520020035015070b422a07000701d90f49040c0310408101010621010050280d00c0025800d0400500f400c0000280080c01400c9004280a18007034442c2205242034041e58000e1011404c00d5440d19451070002d45a410074520a02d40300807400d50400407150348084c189410350036028107a11a604000c512030072010944020365180c01064400c000040c2c504000b02d10061440c140026101d94400004050b40c2110006502c02c6e807184401140070384d4041801c0048074410b0814450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 814021420 1250 814020170 814020203
    0x30f020a03090e1f150e0301020a172208071b0621020c0d0314070314040605090307050f07080d031a0118090203070f0306240806030c040513060e06090a 67
    0x5030700da81113411102c41d003d01c0d180001c3c3d619042c0e4041c1080b03d40c94813001200c2504c0c0381414200e0168502c40d6001501080c450604c01a07000c3c40d0f02e40041c95a181c03154024490b4520140d0401c1d02602103440f0030b400101f10342400001500700905422020590140b1071825030000c11002d10700710b10440001d103107004202c29200f10760403503440340380305d40c00d031241e64440c0d01005e801030056042101d0800d103a04009010a4464400d5108100f1700f05d88130285500c4a0321340f28000c26000741391524500c81004040b003c21001c00104a01580c40001498203504140501d804c2000070135042007454204000c009520701c2c440f05042c0e10003420318010710991080d00a80c4005e03126948168030040c070000134440309035403009080c00c0d58207003500c0520620b5500c0c20b502d1403240810583c803100b00c0c425001c01d238405100d820200d0700884024111140c008448002038229482038849003035080b0501c650200304141c0e405004003c0b100000581414900300c100d0f241c584001503001801604289000903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 814022670 1250 814021420 814021441
    0x709080708010e0106150c08090103021605011a06070c0302190e01090e1b0102031615060801020909160206070c031701080604030905030705060d0509011b0c030f020a03090e 76
    0x1001401014121a03506996422041c0203000504924200b542004004038280398800301050041c506a40c07540701c40190350312080410342210314140c1c10190200802741c0032041c1400890000f600420000603081500390360b404282000803141409100c041c8004000b003090125508212074041d100f0543d8000303400480202c5845a4000b450300070b0b40b6000104016441c1d50040215000841c22034801e40034940b542c02c080ea10780800e4500517031080041c0c1c1000c55598603820b030180c0c072420500680d403500302c0d0b846d010345402c0c0d0041c440c6a075001c1880f1500d46130036030803982c11010920350701040c000b181c01c00a44036000202150140700c0c3c0d43c0c00880400d840391840780c9816100000c0621300f96140c1c2c0d551070b150b803030a0b142600010350a00000c01c0d1842c0120f00b0750100da000a02c6249002540300b201806808010040795903075585000e0742084052040c4007000d00021582d503c40d9001c5a45400742c8000200b54006003158040c800e80c50000303400c020180b06546500f0303e4118180c0e580385544 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 814023920 1250 814022670 814022687
    0x702012003100515180105130b130305070b0706110f0306010503180318032e0e011103090a020a085217062a040905040c090e0105090d030507 62
    0x119001001c0507241d02140f5030380d601401715050000e04071007007950399500444103401807031051250a070000104004030003c850041c210f5240f00e5480c1c540e500c0d80c0c2e8859a04042c103903030000301210070016440040002520401d4035138000c600101d4144824030003419070342c0c003004060354103000d40040071980c0e0307136034005034020300d1200c500480f540e07441c0503114402c8074028100120301a12031180c0c01150340020501001449604e102c000021030007910b20300780070709541200690195692000c01d110218000010b501c5203003443d00900c041c80c203520600c26000c0f0994821100341d04140805c0200c140702c594008103100d61404803104050030091514411304030319045004a1424005022001d90602245400c80d80300324036402d901520113210a8035114100ca1003002e10a01100f002d1005043d172050003842540d248000e400d0988652000003150340640c0c0c10b035280c00d00c4010402940341e181c0034a078100d500e1600240184d0400c0f90a50340e50f0302900000406140c0c0b03c2000030302c01072144640 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 814025170 1250 814023920 814023929
    0x10906081203190c181418070c03032714061e0703050604021b07031101020a02090c030a230114040c021b1f1d0904080712051b0c030105070201200310 66
    0xa280321203070f44160102c0c1490b031000802c4c1c09001d10801c1c00600e09480b800c81fa00c0b502158a0b01e0f142d000701903804500609200c6003040d0a4000390400302500e07107800c20081c090f1407241119840c14000100e0303144ca054402004004111070450400c5921a00034034034503082002803c020980b62038000024002e400b0340310403081402e004a16607110041e00189104c1124043c41c920415110000b004a860301d42140010b50031854001c0415002c5001380c006544c0411300040005408600c00449885401180104070b000741050005020a05c0c044147c480b001c032044604100c0140d9030f40d40607440e00b0482d0050384015120071070760100c0d81c9450b8441ea10000c034400101442058041002d841640840e44403502d0a1701d202045403d414601c002d42c1c0180e802c01035813400d2098540c1c60802c0c0c0803614185000f040001c0c00000401007002c4403451900e0b2415000c2c004d500305680501d421917200512480c00c40e81403507041d690300202d41c11208400c0900282c0e250b80e0790b4602110440ca4600c6600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 814026420 1250 814025170 814025207
    0x10b0603070c11010318111e10140f0403120909050708010b0702010e060301091509022b020c0105071205090d0e010e01090b0304111002060105090a05130b010906081203190c 76
    0x101b01e0104140755401d0f1304030010440c0c503101608200c5031035070800b80710484519006410181a140d2550040000d1401114040364103880c2c0540c0da001c0c0d0a45800c6135208442c11403508160186441d0002c90f001c0140080000401c0540740440d0010f01544061081c0328106200240d030b01c00b9644107a40307004400101400041da40d503500c2c4484002440c0d40300409414800950001c075440c4464000c8649550041c02e058084d0030700b401c2086c11001c091503900440c1c7e0750800c074256440f1070a0261a103d030b00180c407090310031a201e21030202528402803003544a6040000303104031aa400c0241c1003400a420701e45041001048001a1000d14480c0c2284105d90b101104100c10404001c003c05000707041640d10603400791440c0ca040e03948600a000b542d0f4403841040c00250107880395032240c0e5010b40341010003000760362140c886c40c04411007078020307110b81d030f480d0481445a10010172000010302801d410080c80e5191468070041c070886c0d2160350042d6951a1001940c01034407a80e0b415518000210 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 814027670 1250 814026420 814026461
    0x30c050c0106080304060909021e09010908060c07020906040905061504062303070b0a14070609060903020606040b01090503060f0c0c0316030311070b04061104091d010b0603070c110103 81
    0x80035541c0d0341c109111b0080010011403003c51442220300a84140101451402803031115000640030150040443e0354100099120001003035801000450b0040e50469002a43c0e9100c0d4018890070440050109004900301103910002905c00a40b480d840a0307215210342202004000090191006600031002500c40040789140505003011020411000314104c8903c250394402a20146c05620503d6020901c0440440d04400910300100140740c80341d140080e100c407041d6030b0103003100d48a01c41900182e02c16800c00a01d030919126080b8511401d0901c03100075440c0400095854030020180c88100480c0c0740402d401300503450a407100c2640d00c00981e511031306800500e985c005600d11042d03000a040504081c41c4404a808440180c1c1e04200c3c035461550711030705c400f13014103082d46c00794070308134402c01c00002c07440c103140f1680b00b00c0c1a150014405a01c040d40d045825107401c07001c0795104440070818031120640000d40100c0241e4405040ca1588640700c005070000c2602082ca400190a9030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 814028776 1106 814027670 814027679
    0xa05071706010b19090b160209010812091203040f0b07152715050a06080705030c0609120a151e0c09060c020607290f040f03030c050c0106 61
    0x50604000700b0760f480c07028610070380c000304140902d00400c4014108524162649e40d00525499004044c801644e141029252203100c00b898820121340d006110218828425107004000c2c14222001300c176541c41c2c50751102c3d888100b044415007804a203031605d8002d02d108844607901d000c0081140040c6241c40c03a0b058a034580c41c01d0741d801080f00c00900384602e0758091742e4440d024140000c545036203003014952420b585900503500c00d40105040c003c5540712042030302d80d00c280440d10f225400e43c445203200c0c1400010308010b40a01c08103940c0381050700e110341108028940b030015250031811104e544904460f000841c01000a41c40c0f0810006203202c3c62107080c0ca00e000800310b40c07621025039a00c0c05040008a1008003505010140c0004603440e0019654401402101020945481d036520000c1d8a0100350007000c0c160b0700e028a140180c403a0050720000c11001d40204940b9845 = true := by decide +kernel

theorem cover : BRFrame.Cov 813848920 814028776 := by
  have h0 := BRFrame.cov_init 813848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 813848920 ≤ n) (h2 : n < 814028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
