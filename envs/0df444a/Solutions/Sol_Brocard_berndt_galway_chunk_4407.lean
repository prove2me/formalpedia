-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4407
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:30:59.837621+00:00
-- url     : https://prove2.me/submissions/0f5f51d6-89f0-4aed-b215-5d90c10a22b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 792446043 ≤ n < 792625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 792447293 1250 792446043 792446099
    0x3120c1e050f0f03010e01270c050405120607020709020f03130606030b16021b010c020f0406090e010603061d120c030403020a0b030a050708160831110a 67
    0x15034410016282c81c8007203141640e940c1c03601241c035404544c0091185545070707001c09001040b480c5e030842c80c1100340300c001e2896460880450701030101404940e201101048028800024140c1c2e600441060000303954004d0402c0c0d040c6800c0085c01c080c40b50f0410640c1d14010400b200001000600f101d5200611501c1c00c2c150048501d404000f802d020b92000e88801020300510220040402000d440b42000342c007142d0782c048480015182e0302c0c08100000d404100c1c2c0070a80700c003500b03189100c900641c1d80108000360741c90712044140f0450300c9003840007510303a55035038013802001128410440e40342082501c00b6500503400319001e50743c1b0850030421101d10070200c0e0585050346c0c2001502c4c091a0700a141b00003040d102c8900500641080701d060311a5070406000c80d205900070b5003228000c42c4900081c0c1c0b03100c4442c607815155102c000e042d1110302c160108101225141c41003094241440780d200c01154034040341450000100350306c0245202c1c0b00000360130089481140a0280407001c281d4481c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 792448543 1250 792447293 792447347
    0x70309140121180c0f1e15030e011a1305101e0b12040b13080f0a110a1a0a140417120403030b030d021b09091903090303120c 55
    0x900a0001c0506050851295503c0c800801624a6224050b1035006403034100d02580c40007901d60411141901b00000d298000e020b001d6080c2000c0c042d1070416290034041480d828500300c01c2e0840c1e08513904020f2151081c040e1101516240c282d0f1205550094014445420050b030802c144030082e101c1c1041c69120401e43e903040c24180489600200681c0021603190b04100031207000b645412138045589005a50010380210040b40e42c100304950040861810680600080103075944014901720600c21024120005100100000b00c00c3c0382c801c4034054903800302a18598052034001c1c2c910401d240c1849180c840c0c100000c100f030303070b80b26400c64800000644c0140b07008200d4455911021482680c0900308000e158060700140c00044054040300c20344410f021013242c6030260354800d0039074000c1450503246a0f16020700c0303181e0841141d01c03c1e03452200000980c0241214100070131800b09030008810814183c0000a50706400c90360381c02070003a0502d20100910091028445038040c00180d600c00e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 792449793 1250 792448543 792448607
    0x1f080a110d0f05100c0f1e051309020f040303030b1c150204031b030201230304020402030405010209130c0201050105040b0d0b04080408030406110709110d020a05070b04080703091401 80
    0x400e6003020941d42000228820344c005401ca141124011498500c52014080c2c441c011054007800140828603052502d04001c40c0c060b4440344608112041911000c54001d07140e10013040c440804000c0540c1d21461890301a080e80d4407144c085204e03140b100c883d1a501018048101400c641c4000b131030280041e88440c000003401641c10261110445240200d80e1011080c0d016090364000d880e040e4040392a445c14004d40340d550141e8503407150003440410010308240c0c01035500280304d40005070620000340082007086c0c4204213040340ccc00362502c1d0707040b400d07980a109a5000d400103807001d0020010b00d01c00308907d051144401482c0c2c40609000400b445415410ba9004c0c02114095a6845694401c000e02c100300740450f611403401000000034040340300e0300c10407120a1020118a090890f09807050009421800b41c800501008201a000050b02c0703280103445107201d80c900f0ba88407504d070f0400410071901a04080515203d80d002c00e50589c0c0c209429440000c2690b080d40302c110002010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 792451043 1250 792449793 792449813
    0x60b060f120c12090604260f0c012403110d02010c020108060f04061401111506010507060e0706170f0c0f0a1e030507110106030312050903121f080a110d 67
    0x10300403001c41c10044c01000180071550038000c0b800388582d14411141701310920030644c1d06850030941001c0800c6090103400300400940094480780d40000f54002e000e8120b03030b41020490900c0110749030908010701c2009000007148410071401d40d60101e502d075690b40040e288101251000e414402c002000401d643c4c2c4003080d00310b0869000c1c000b0300400381e440a0050242d821880c169000c6243c24426032001d20000812000625031176150070b015071036100042d00d10341d01000b026940240c9071b141041c000c2c0750400644009058a44d0762004c40f48035150130501d8550080c0030304d000140c04030b082c8003001c80c41000362030070451900c190a5070b5140c000381c26034080d10f00099260800140000c18520650540e00240c86a51541c6070042e001c102000168200c6a03240001004600010300b4200703410a280d20203680520008100c0e850715101c170170390a2680e10100c0700401c1c00c1c0b0201400c500c1c0759012040c5440145641d0b0010039403c01d5030781c3c41c40007513103850312120b001e5425148884184040710706 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 792452293 1250 792451043 792451057
    0x11010c0213060b1c0218060708040e090a170702030705150d050903030406061a030403050a110307050a110109030b010b090a03170a022e0b03010f0606050403060b060f120c 75
    0x4100480c3e95031858403140d081003010b0b6200350211281400384001da4001c64803180c1c41001c0344000e09502c90b0400c080c54008410583d0b510009000110715410500301343c5000c0c25030030004040440051500d03941c2210904041204504140400c00060314005080000e8543c200d8440002c015403251400f000d004054080b041c2500784014401001c1001c40258050341c01440103000d16a1941e01da2140c480c008914261400001c2000a0100c0e128902619048601e032030302c03800c036079202d094a41c03a40c1c02c040360685540c0c0010881c80104010320308a8030391490700b800d1651145145460b41209004144a2403d030054000b46144503541c50104850140d540300c88035814035410140c1602c0141c1100012102501c03459540300380e0003903001c10601c08041380034a600030225070b640410025105504c1d00c5905503495050110040069005210140040d6900c00e0745440c594200365065402900e00d00e400380704100204c0c41e602d403500d01224020b48111441040e90f4894032440041da205101c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 792453543 1250 792452293 792452329
    0x604050a0e03070812011502120a180b030a24140609060f03010e01051806040b1519030f0204051f0504030f0c030b0609062112030a0c11030711010c02 66
    0x2d03c440070400c41c07501500181903110b001140d00d0381c0341c0c401008104440c002c5000968031840b6103407516a087c10042c03404413001c1c42c2c640c840100c1481441200103c541080752040d0700801048901e0b48188941704040c0b10750140c403c00c02d040c2c880e00d82d0f500c1915010b06080c807070200442d10b009480755400c4958440300640036a81c3d0b131307944c900e002016420030301800b100400d10382c00001c2c45143c05420085040401c00c0040c246845000400c002090b80e03030324150f081a00c405200c685007601202410000c0d4401354007440c48281030707600908030b4503c2004110001d10611040c01a501c1d402c1c0c01d0000020360514001c810b03541508282c909004550000f02000e4010070342d2001c02801005000403648100208151502d0b40c02c1000310001c0222541504988029403c001540e03800908021043c0a501980c0801482c5081a41990710031036006003829202d06110707074101d0340b01129444103558070000c0c0d42012901d0391100f10309110550b0141c10000c0710a07501040d50354031844003980140c84 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 792454793 1250 792453543 792453547
    0x6060307140d1a010b030106110a081b1603030305101d010e04030908070f0e13030c02060d060509040c061106070507330c1d0303030f0c1303050f120a0203030604050a0e03 75
    0x81c0c2170241e241d4404d0082c5070000310400b0705103804910020fa10080030b6403240045050064070ba000a101419000c1e804295100344050b0303d2402c4880396810000c1d501a960205480c035100c3c0c100c0d41d090742e155011018400384c0916801c440c130380c080900d80c103446a80380c10842c1c54485082c126041d642c0c0e90440502401100000100000181c64801c100d4222807146582a079500c065100010110310014010880095030b4078011710b81003000740540140144001a041c3d240c2d80800c80500c0e080324201c600c120105c2c01481066006200507400000d030000801c140e240505000308140242040101110400b1b861345600d0f4214104542244c210b0350a02640300070002c8080d0040d007150301107200850740824000d160621030319a0040000d0001d0000c1d861034407150254005860300401e4210140d4040c80503610f48503800c0324841c011801000180110034020400c030b030400a1341912404000820403a48100c81d40100959521000459001405aa418a0100243c68580302c05044ca000c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 792456043 1250 792454793 792454799
    0x30112230a02131a010c0305040f031506320307170102190206100501050c100204032006090a0e1504021c150305031e040807030c060206060307140d1a01 67
    0x40c0901ca6a00031242100c0b82c400e209803003070441d20502c0c1560703021045040c40c0191940120400b0410702e1080c50800d24283e662041c8695102c440c0e0030465a150901d802242481250302402000d4800181440940501c200004483d004d105c0d4a6147c0c00c000e8240d00d1402c0d5806101210082c42c540891480448408010a000f540040650600c0c14405e29000700c803a44005595031013114104d51518115060100660302d60b0003005100c911803140454a180d02c2c06140050001540702d94401c40303d8a40c25050704041e5403859100340d000709004c1c41101e56982d01c80100d8400c81d8180c401d0f44155460b071003281d03a0700d041038070b0420384c026000280000140351304500300509110605000c20000f004920030b004845c41703d105c00341070340d4400e0045034100107400c054903030340100044100c1d00d000c3d501d800807800c2189903803044e40da050854204004031a0103001065001e0030840282002500301220500e105400c0019640202444000b403c10044100884070200c060805001d55540e9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 792457293 1250 792456043 792456113
    0x40501050909100806181c0206060d0804051e030601210b04110301150f0f030b010b0f04080d0807030612120e040e0a05010b030c0d240b120706080c04050105030112 72
    0x181c280b0105580c0c0c46400100352100c0c0d4445403287c6640030305d9010b000c0340d842c5d1408210708010700020544541d502007100081c0360303449016550300f0520030400c0000c54110b2000b09424600164040f40043e0b8402866102010031541101e01e0f090380f142106186843e01d09161030f8601e0140d078a035030550302e413600100101000410b100c0803600d841c2c0c46001c038140c60700d16488068816201c01460792400b1001404400641405000e464807481032090409a480815034078041085038101c020581107424400b078160715014910140090400c0e40c8014501590303920244c201403485041017003038407209401c01f580c0e65042480e103050200112500610541840d900070440902c2c41032191040c00000520b40c10030001c082691364001180d0020110400080d9000008a1400f1030180c0e65528522113155a121188000001c0130070080c4000c80c10a10301a0030700c4005018500c4201d070078002000030340e0b8020212819108102031800d10246107140c40442c0c020031402c2910500e1a0b80d10b0401c05074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 792458543 1250 792457293 792457321
    0x30c05042115090b04150b1003140c071214041d090f0d08040b090313081005071404090f0902030106060206091c0c0305210a020717040501050909100806 67
    0x41d0040e10440140c181c0d6481c002c00301d641c40e80000f00503400190004022401c6c90a842c4441241540b010881000001c0001c00700c40d6482d2242d80882e968984111842d600a10303400e5100102007a100d00d8008551142011501080402c00410501f03d8202200c1d40d55881500c0040c4a84141041c0d200700c40100485800e108440c00901ca2040e241030303906031040003802c07414100b0603442c6c8501c991155140d8805c0d01000607c4154541710801c981010303070f01032904943c010001032000e415151103240300381c01550740c0a403604041149003401e007038010f030030388040764100c64640c14001100c8118040c0303d4060303c01c003613010351705521300388001400f1900800c8680c4552040c07410b481c0c2c900c00310608162540d08420000d000100010441e100080c00b84e001010340d40c80c00c0e1410241d0f040c585c905070008010844105500d10f0700814000104500034071901c207a0444a6440c9043c9070074000001c0240c0106c007800e81c0300300e03024400318030b201a10310a0500502518800d0347c00c140340ca05c062080031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 792459793 1250 792458543 792458609
    0x110d111e0301050f1e0709030803070c051e0304270908070c0b0711010e0102030c0604120f090e060105071b03030305180309090a020a02010f0e0f061006020607030c0504 74
    0x25401c180c00941103004248103144100410b50444207284801025910917007002000d940c00d00840c80008004945903001852086000da039a9181110145c544942071446034524244581410345404030800c1c000300c1900c0544a5000302014040340c18804643c00100c000343c04401c491500019100b8070865000400381c0b42d0040060b90b280c0c03591a604030010381300e240030252980309a141c0c249215071055040342002c600501c112410300c4603048441c1d0070000255000c0354141c085172640c2c0031309038200c1e80d0701807810500e051884620f4a8030851090302240140780c0c42c10440001042c0c0200200c030740c80b1580581541c08a019101d40307900d40980180b85c242c1d00760b1f20310180c110741c40b00c4401c00001110b204007409003030b40c0304036110802054080d40020012000b95500c4402151164820b8440c0e0620710800c00020450050f18006545c10041c0192000030242036820082c400b03d030300080c4040d08170805290000f888110818115018081e07a009440700070b0b5000b01d4209211840480d800c1d0b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 792461043 1250 792459793 792459799
    0x305010516020303040c030b1302040f090618031709120703080f010902040b0d0b0f12060a0c030e07120201030603120513150e0d110306160f0903110d111e 68
    0x10700818a0401d80e0f40c3e020889000341a00010310082c000100c82c00846074011200c4942d1021b43c82141c5c2c00181034541c0e060222001319690310b184c50903c42d01b80118650000c2c001c082c4804e02141e80c50040003e040c8010f03c01c2140e040e4004180c0e5084100000d01c80300d112425015150310103850018801d100c15a04010000c0d505130020900000d9842202c084030000b0703200c43d240100d543d10031400780c408410401e9000d0501c02558640b610380c459400c5039950f645000c0c7c0054a4000514011600e40d059103400b014540343e403d0707483c0301d0001000300903103d1311400c02000f20800d100480140417130b50401045505911400101d490b00140600b8800401140d00c2c098207440d00c500100b5400d5001c04d0300c000400e1928000300c2410301030700704a8554041c007200d11a4120700742c04a032800c10282c80c105038000103031400c1404560300c0b054203d004c000d14070f40340c45810b203180ca850a407190020f100b58441c074103642c000030402640c25204107020700007400c0072000b00407845803011040c41100c280d41c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 792462293 1250 792461043 792461071
    0x80606010206070903320c03121206010804150207211e12060312020d1205010806220f11040c051327050c09100c030e0f0a0b0403050105 60
    0x6403907001090403889900c0343e03030f80c08000e81d144d911001e0045030003580060185814001410b03d074014076a4900c42524208004c2a0346003a900038540350540800b1403089003103040c000c1707034400940b4440c507e4000b40246030050450300e40d410840d010501c09165000213910019004003080300301100500084c20381e4440c0d00c1200d007050f1b4143c800c420b0680043c1d8074134003049990341c0b07598002c5030310401c00342d84d0b10704c00107002e501c035541c448200201c51100405640554a0010070b503500000f000042003001c042400319516000c11160348840c040c11045010600c0100e00004010742c60440c0c8e0255008260303a4400502414890340e811068244940603508050ac019200c078059012221940c2d07020105ca0703005850101141280611103c42c8003c10f05526075401c47c0140c5800342d54012404020010341da111070004205010107030144100a000e800001c450100c1d402144481800703070140c2e00421030002c1180055000142c0750800546400042004000d015055000c20701c00c61091044070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 792463543 1250 792462293 792462301
    0x708010501020613021207030503030a06051f020601031101140d05160201020a0c0b07140a050a0336050c0a230904051f02090a030303020a0816050711030a0204090c0806 74
    0x80c3c0b0b80a0407942a4415003880310002d006080041703ea1030240700e07010a513036443e6100e5030750b0b609650003920051985a00e03404c0c00d0105150481561210201030b074401ca15150040d940a5116001444042e01d4200410f01151081c0d00915226080b487c0960b4404d50f201c1d615803d0b500144006d4511006088140311700c10103040c0144200d500441054a0741e0183c00c135541d8810b916240020031520402070218044100459800040c01100a840c0c4a20761039002c110401802c5961111004140c8000b070440702c0340308020401034650001010707020420003d21410f0807481c06030014106130b000f400c03c0e0000140700050f600744010120035031502c0c214400f211420023f076810265009803464200d4440b19170b08a20003000030200b60043c960250070034030320790300050448175250320540129030006508604c2c950f11980066000c80502541c48280303c0030f09000f400741c001d50300e0080c092480010219400c0e60200318411107a90300a005103c0d5501d645012039104a50344291074a0303216003000301e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 792464793 1250 792463543 792463547
    0x40f0c0201051008191b030b0718030b01091d06090a0c0e100605070311070e010302031c02030306040207030333081f1a13022508040510091d0708010501 67
    0x480031a41c10900516004203000e10b84031680383e10f41c108071801000340704d48000e09200c030122400203500230780940e61185040070000c0d00e2941c080034400d01c80400c959060000071001c10f121750560704070740c40000d107100246540700c0c80c091144030b03140c0c510f10526040110003000058039000c0c0e18412540000780669820742d542400b40250ac4103060007141000a0202610039806410141d000b85004039010810744c0358281000b04640101a202c4080700c0148250b090420900061400c0c12400041618070300600035101d00010340b5007481650002030a40503d482a00b2400c498003501041c02c00f1824203c10701001e480c1d0010001c2041341c0700200c005030400020070782d02104031908098240400e01500404e00804040c007000780d854000070f492070025260f00e05132050078001c1410069403a00f0080600840500c0c0c400c83c13440c102c80400e51100010740d01c0702a581105c0317040d9400040c200f88103a080c1d4040d40c40e034100580307a4069a2613807510a898014003401b4003070071303141e600181e40c8035001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 792466043 1250 792464793 792464821
    0xc0a061a04091109041b0b030f0708040b07050c210301261009022d030606100903080d0e0610050a05010905010c11030c180916180506030c040f0c020105 67
    0x41c0c100e40700f003000e0302201d003845085154000e04c965152074541d811200c20620340340c0203411100301030704080100100c1d900004503180d0800d03801d040c42c40941c50f00f6903890f404000010454020810301092140c5001c200300304942401928021000d50250480100a01078009105400b40351808003440c3c070348000400d000b4034001c0405805000390008a180e624041c024595040b81c001d00c0303490003006a804480b00348690106007103120030f00c20302035804140c90b00c50040d003103600c580c0400c1d50708000d46070400411003c0fa58405083e6440d04500000a0002c0c0401c512000c40340c01013208000800c0035151020003075801c102d40c0b2007451510b420044800b0341050007050b020600399402c4c10045021364449200e40c0c5070080c200d8101d86414000b26400700c044140d0000340442850034031444000610205403000c10110890007110724103005002c0143e07000c1040d159041d0f944004c9181274400f0300c0650b8a0394030151040c49490703451125407000b0310702800034000551074035011801000803424 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 792467293 1250 792466043 792466061
    0x1c091209081009020102030906030f1803030907030b04080c0a0305041d01181d1006050301060503010c0c1214030f070e0901060f140909040f052814030c0a061a04 71
    0x2008440d07200d060450043c01003200903419031105101505a65851000451040b424540c00d0f250a04242642c1c00305080d14015800f1503400500c100700140c440080c2e10745c01c403904002030106031748441c1020609131103503849451250140301140030038540c004d00104229028072800c901e2004e00750041c10030150081c002da401c840c1020351aa051201240c01c40345841c0c0e112000321056480500c01a4900042026804500c130f4454400f0842403500303100e001c00610040d4020b00c410000104003d03c203043c0c0140c010603443c1120f400140140c40380b8001440310354028420765590825022107111998100c4030200021045060100e10b0b06101200c54102c46039901d43c0310891034512415240d001141c942e42c20000014426191141d45011203540135a018001000000c50f5500b0400d05010700780e20704d8556080403582c08145219420391000035031b50071504021138a4250031480781144200e080d81c1000d4403421082006020465001e1360304010024020b0f00d0400c21720381031000380c0b8130381c4c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 792468543 1250 792467293 792467309
    0x213021c0c1b03110105090601091d0a0201051b0102030405060a0e240c0c0304230607030915050d0c0831080d020c07030b01050a06080108100906021c091209 69
    0x82903120902e000c07282101902c51103401d14140030400001950308440003211ba0f403a843d0f000d00c0c0100180020781c0f003185e000228a518100130b07c680710000715510b101038000241045400a8800c014010a18028442818900003950760b0304150034002e40d9440b058410100062402404007542c940015905000340044104810041c09800e000e054168005042c81500b0030f0030051412680400d00041019001e030103240041000d4442d40003c0c2030b07800c090414050041004003002198200031407100703e40400c0718103148100748010807652402102015000d080c20440000802071300606000d12400d503051241404901c03822980c2c011584404801c0f5184100e4000d402c0812460402000c0303030100302038098035001803550b07041c2c40e000041d44141d807541090401484585400c1d03c441008021a14110100354103099155461300000c03046084510380d038525400c1040150b4041c3d43c91820002c01520490660a40035009000c12000171540148001d03010141c0782d000b07030118400d8907e00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 792469793 1250 792468543 792468557
    0x6031812040617010608041202010b040e0a171c0c02070504110339070525090f02030103030e1c14030912160302090c07170406110f1b0a030213021c0c 66
    0x684a80023007611040003101155221f25001505848501442d500005540002c0401100700d0800340c0c840c40e51a02c003203121103c200304011080c81c02080c0d8400d1100300c02030005e20950303003010a074907004a9034000382d0814100745043c04c0002c81c50340590310900fa10703c6a0b2240e02c6052942450450401014000030303441c6100c40c00c42e0615500c05020020310620032a201711040146c0303104600702d800340781e100d0303881c400c10f00b405020040c0c01510404c6c81c64400a604550543d070f03024200160100c07030640034045140d801036940c90800c22500010360400034414591030b400440c1a12a0312007419980205801e40d8624007081001450313043e041410070042e013004c0c1c2594204074002c0301c06403101d08690024440540400c1d0301d45c41075200211007540c105e03071340c074500030018040190603202002550490074880850480c00b1a03525a401e5036040002c205189030f400084000d005a00043d4000300b12845120580302554002c2003003c218003040c08400b003030441d074002501d8012400b00002100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 792471043 1250 792469793 792469801
    0x1618140f071b1a07020d08010302060304020904080d0c030b040e07030206160201050415170603190b07090f080f010518030405010806060f1207080a06080c06031812040617010608 78
    0x2290ba078030740c100c840d92440c034010152a511201c031810324803100485031803040f0090026442c0c04102d081d2201c59281495030180d8915000690240001040a0300502a07440090100118117044401244105c03104100c0e000c89010024000c0501e10342c114080c81c070304007900314100400290035040b664004c10711890700b01c5920051060b015080d070b04906108080c040429500e66282c294034035460302d640c5a8602c80d00c01144010880000781240703009802030f41c0d1240400001c0d114030f4544a030042c0e1415480d450b01c8104a0b85d21101d50701400500d01c030f03280041b800c13140110313000c02041d00c440c00038421a09c50540a00c48111003412244180d0720400c001c01165020385911980300c100144024148203902c0b090044039400030b00019001c002c00310030021019004400faa81194107a2400c201c45e50920a680343d4614640d44818411180800000c01d1603005000c44c50248000e4001e80c1d4407c691110643e000d40c001d4050000401c9560440780c134500e41005a65040340d441d0350302c82949403a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 792472293 1250 792471043 792471047
    0xf1e0c02101715191d0a06140409050c03030409020d05010b0a17060f130b0102010501080102091e0604090921030209010e040213050301060b0702030610050108181618140f07 76
    0x303c0300740d107070031190542d42000e4800442e4280001068000e0710303640000c44241448044520041904010901d451001d0055541061000f01100400d54001540500c1420940c0c90181083c201c0b5605200c000340201c0d86410301d401800301c500b990030301841140d80301c07004400d01e401046c0c64007000603c41541c5640480c2e0340811182c000300c0242052170086a100c010800d02d480b55910450410b81740e21040d2284d5a0901c40e00d80181075140086007003c0030140020500000f5041c1c200c1c1e07a8603d68410030aa0b0384d1701c4101c800402c0074140401040440380f400d81003c100c40440c1d003050481c507031540040e081c0139008075034802c2c005075242c0348a00314200c1080002d402c1951070780c558001c3c0e09000f2880f0344091089801030b00c894030313500740c481020784105450280001e20074034650309007100410940c1d070058100c0d074011610070100c500c4c1000d1006001c5c17034a00089009001d00c0c001c1000003803010030b194070344841940c54500034040f4a46101140020307a905989000140349001c0c001661a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 792473543 1250 792472293 792472321
    0x90e010605040b01170711030d020702010e01180b090301110c0c031902090f0c0d0614030d030905060a0203130f0f03200d030b030705040501090b120f0705010f1e0c021017 75
    0x10741d107407d101110013402d07050645075800503040d41800135070000e0725409541c0c022401d103980c44000d281090240455000d011442002d92080314101d441c00325021119940a4201248000c0170102d15a2242d142e0303440c55542c2c0050b1100079000e80204000c0c000d403502d6440f040200e080e0040c1000c407240e2076440e000c00101c0790013095440034a03024009030304038481c0340c0241c1c0020000707c0441d2412681c114105800c041d40b0442039001c0c94a426504000148081101940185112401a226640c080c400104444010001080079018a0000d130030001071079180100e4502070b98402e02d810110f00400080114030030442c0c20254003984840a18034881d40140e00354640c05402d0321001951074000c074040e42c0080c0c104121080d250749403480c40e41070000150546150410082455031101d0608a890305800c1c000d05040020b6200880b111034025a610200c6c4a00c001e840d8501c0300507003070010079030401c00f4800c0340326240c0c0654008102c0c3c80f407800c0c0c2d00d50001c2c0c1c02e240c090320b483e1501c00e24008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 792474793 1250 792473543 792473551
    0xf0103081207201b040606020a06150513050114010c030e150c030f18010e061c0209060304060b0103050c0c15060a0b13030311120706020d0902030601090e010605040b0117 75
    0x3804000f8183e01d1501c1c43e14880c10b881c070040041c28210392503d40790081001d24603080e8091407421008000503540001e0304112641c101500059440e000f140c02100c07004039800c015000250389501c50003100c907980c8018100e500511240401e0410400116aa58135814001e00028041c0d00c81c200c052074900d0b11213003c10b403845426890240072030303e00350a40e08808002910601702244101c0301010340078a040000ca42480c00c00f07408451030001076054002d4544002c1003903103518a044446181d81d04a0b031500100401d0a40c50b860185002d41c054018154442e000904220200300400e00b41019038031400c2d91017004d0514800142c1d0030200c109401001036902c2424401c0c00200340313401100400000034080d0400c5059030542c1800341800c803c9503249026544041d03686a9080225420380f900075900400240e41c900340d0006c4080a000c107410b010354140248400007501194641c04440300e030f04550024801d01d81d6900410040b210400212404a10900700e090002c2c000404c60b5030740 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 792476043 1250 792474793 792474797
    0x1502090301061703122508130204090803061c21030b06040609080f070e0c1602030601061d06120112150c1808030306010e10260109050f0103081207 65
    0x1406680c1c1ca000740c0c160308800f0510740c0301e070000186201d400034042ea445138050748000c0780da041e02540c0312011918030316000000c400c012035003010a41600c000d041300c011483d0010800c0c00181042e013003152050b402650360704c0c03240050301c94003040d5041c04c0101313544242c2c03c80300704121801a0b90b007007801c481c07000f000c9004140e6126109d241980da0180540301901c0b055480701f250354240100c4c5464200e481c45000321562007280100300e020340c007070314490348000d40080080d15131010703421121a1421003c4001c1d070600a00c800800c0950f40440500f401c20500703200c04032468803900900103144621038520350024001d10061100210041c1d008401d2440f80d00000c40d808244070040040701c10010010b00001d040d8400702c4a407403510800003001d8025a0b02561450801c072001030300181d801c1c01914061450440d1034040ca902030b00111410740c00f00d400300144a0014000c143c0708003024010b0112961600c80420701c3c0d008000040c1e030503a584640c100d4a000c92500034070030000300051030041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 792477293 1250 792476043 792476051
    0x1020d05250b0702150c0d0b06040803070b06030601230409030e0612040b101d06150d061715040f020f040603240c0903151803090f060203071502090301 67
    0x1e15031140352000c01c166405003078185040d00b0420070090401d241089081c03144001481400312014249080700c284c8000e20a0004040000c00c01040c1c030303800f40340c0c00383d2800d0201140c1042448034140f02ca0344503020072025602140e8841c515200c0300e002496048502c4030242d80015624182507020856941c0241096146100020002141c0b42d00102c2caa403009c5940340700340f0081081441768a500114012400801c480c10300d20071614100e448410a186080c9040201e8415214420030f40140010161542e80c0c4055a40d0300b403000d4100c500c51660003152007103040090300700203c0c2c448141092900058410307292500c4120100e64911401c0e07074490849100404103076528401c3e00001c500ca2095050684088401c40a0008100c050004003e040c881e220000300c0c0d00c10404405c3c1e1b640110b0340805410004a0302d070040610456480061144013076032001d1503001046002110300e41d041c180107842d00c41c2d6080b40c890141d10b60060545003039030700540e0a1800b680181400c0e6a0180c0001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 792478543 1250 792477293 792477337
    0x240a020403020406030f050606150f2a0109020a05030120180301020406030f050a05160c080919032006070f11030604080d0c084506100e0601020d05 65
    0x8040350f00c117501c101c4101980143c074000f00041801103c2d1321070700031508040d12908025507411544034003540030005440001d460b00700d0070b840124031017041002ea040105010864002c6c0d900a108103c010782c41044101000119403405001c6e010b041004c074a510b000b802119810300c4026080400b1008041920102950868600f4801782004041ca554042000410340c4154011102c020300a03000c054103110400c00f01398006443d044603011240340071154000d1a06041900c1c0c020380031015400307000160307000503000c088014582524046e40380308025555580d8403541d1040e000c503171941c201d072060000201240568000c0e0250714040d822400002e4003800009041c10340468003110402d40110b07280601001c113120700c541190440c185030700c4074104206014105a210001b076110107084c10404000c54070725550b201e00702d4841e6810131600c00c1c0c50741c2000e501e40000325140102e4285130000002d40e0342100d06d15a00a54041e00130345038003c01607104584640c880400d0140781e44040c5030039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 792479793 1250 792478543 792478549
    0x6221b261c080423061602010209010c02150705061e090a200a030b10030c0f03050601170c13020a12111210080f030c15190b040f0c03020318240a02040302 68
    0x96040d140c4404050005c0340762070003802090b540d035190100b045a105204020300761340c005800d01070040c0c0444055143c0440c0c030503581c046215000004106020b40c80a000a0084400c00d0003003038010f82d94200d40c0340e52203005980c0e8a03a11600007401c00b00d070711000900c40226265070b11449800281c400c18415450b03445d2071034429000c7d1041c200554143d502001403104207240400038102d40c40440f41151720b907031550380e607031a0180070782103c660441100344040d00c0c041042004e0088060b00d0380a00212001d0010002c0d0805890240450f004101c100761030150f609c107060710f40b002100f0440c108032110460100d4080c004000290616100b03c000c905120104030106580403500d0045035500780503d115800c05000e0034a0680380040c2a040c088106905d0740440300c28408a00c00140750900b5100003806803072468010010705e4a004d20504650303a1503001140304000d100300103032040300404a01913449580f414807107a12141004092070031842c0c9881c01d904941e1066015003441c0e00c17a000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 792481043 1250 792479793 792479843
    0x90411190b0c0c5b090e0702150a0207021503070905040c0507320304050a2313140703051e15060a11030406080403090806221b261c0804 60
    0x5018000f0448484c060340e80000c00a0250020502075643ca003040c0c00f0107075980e48000c00081072948100c00040a51001d541900c414a40060031100c940442d1603800449034019600c106c0002c0380d50304046141d00300b60040d401220f5481d9100381c904500d644451126101c1004500500d108595840042003604803001030140707020780165603a10f2908041080d0545294090588941e442c13000307449035003210359900c000000035201d8814078210101c011300100002071078a400035180f8002d12001e41d6140d072005100f000000d141c0c104a035400414858041e00440da60000714070280d507069602e0620380d01811182140b030a00015007c002e526041c1582c100d80c01c4600010001002c001c20315a010307142100900d10500a040a0b08102c100f42c1e508045aa422030000040b00d030482042286541005924114010b11501102d4641418040c0420000c21203400100342c0864011440c07008a80c00d12000d92048030450090042c0c10156580c0390001c0055a441103080102401c03140300c001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 792482293 1250 792481043 792481189
    0x16061b0302030108010b010908210f0c0a02100c0209040204020c0f060a0906050612060c070c05030d020a060b03011a0f0a0b03070503040605100302090411190b0c0c 72
    0x2805602c0307605003070350349007103408182c14141001302c0307000c0805c45494080340e01c07015901007101100c110004826906420300c034941c0c1e00d0540e0440000e06941040380860744c422440d00c00c0710038080c026204401281c0c941c071201006948480058045001898540e000b8505180f00300141d031001c4160b240d449042c814211000c0003e15181c072200801c20010f88103117540590219007800c1e891610140c4541d517514000d0401040400c0054000103002d07992101000400004080b50751409480d03100079110703412014201d0305079051400e111079524040c09140c010303da80050340c0684044203020420700c500410f245507041041e181001c00e410443c0d100030340c415800c0c2c4d00d45640d0390609181c0b04044420040c46410f0960004500340010f0b6a1012030a4015400020328241c13030304200c3c00101290100751148500b44505140041c00c00c0c41c0d10007414036554284259043c0d00c0d586414410704c20600c00501440c4204403200001c0108040703024400100216914001c07501e80340b51100700581070711 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 792483543 1250 792482293 792482297
    0x30302060103021801080601121505070f03110f07170706150f0e0c0306040207170c0f070f271112250e010c170d0507121116061b 57
    0x40148194100441041503865040c6840f130015890641a191038040602500740c0040b034010040c418008140c80420703d60481d085d08200d1420030744c40182005140c980c0040c0483c2c00d08101d803154804020940780f4002516103042c0c0f0b44240c2c1d030359400469203805903c1e00941c5052000380d001c41c80320700c0b0701c50200c1d2010031740088150410340240d5504400b0750041d01841c120b4400c0044207648807003600d07002002600c01607280e100516114082c030003618204000c02c039011905c0c1c8059a00021000d000c2e4840d00c1c141c400300380e101d101c1a800400399005030f800c0036200400b9654035814141c160140c8001845000410141d5143c0300c00050384030000c0650f00002034001c1c809800c049a000d480c56030000000741c483c650030560f02501b00c01606c1c1886050001904c40e00f024010703000031499500485080059550744100e41c403400820342540c60b00c0c0051300304038160b200c1a0b004d104403d4140c0c42c2c0340c0018102000000d14015555444404840864507611481c42040a0154444246400ea = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 792484793 1250 792483543 792483553
    0x22060906081005010506040308030c120a0b010e121c05040e01180c02031309050c0d050f0108060708040309261606020c0409080f090303091e0f01030606080a05071206030302 76
    0x80300280e40390802d2840da0600a5181034010083e03503848004036000c4030f502c480805d44070750742c4040c020f4081c01600d0028072614208010409009603030703800501180003d8850403811100d1a0a12000c541e659030601500d61041080000b00790790010341200040d042c0c90643d2604da100d1516940c1804282d20940801c0c00c8111b0380550342445000b81100751030144020340c103040a6082d10411103031a407195030300080d540c20200307509a030140c040320702860340f040c814400c0303081c0b08180181c00b110034400c50a05009007008105210310030002d00b4095034056484898007802c0405000183c0341140c2e072030001150100301a4071200703050201c4400d007140100c0c03840f6840d02d04080a402c03d043e0b0000c16100718a0000d503480040c1c641c00580e03d5884441ca5010740764034849010070300c2e600c66804069070010001d00c3d03100650b90904181010401d00385c411403811501e0324015001d40741c4038082c1c4008a020480000e1207035079290305c0310b40d02c41e09600d04001080c000f100090b0131070301507410076401030b000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 792486043 1250 792484793 792484799
    0x12010b0d05060708240d031806050c0f030301030201020d110c0904050a1b050607060209030109020607050a120e010e0103150e070926030715110d021908060a0522060906 74
    0x30020107648030117605102d513031159010003100b021480130181036101d03005010820302451300c2084000040030085d1740403014282c40f694098039942003038040002c0c2e880740003420b4041a43c04004d03a81200d506030002c1030180c5021009458201c03080180f0070b1148a0b2071503c02483d559201e20303501603402440070b44054440fa00388255031413054841001c1006d81840100700747d8035004100c03407409070468070041e22600c1080009024010795100654007000c0880c0d81c27800d000002c41e1400e9000d100d89840140000c4009058502110004250b808150310a903582c4140d4041d4008816603005000b03510052502c2c2c0107a00d203414010f580d944001410450b080c0040101c1e141103600786010145403150a05007203d000f66240f094150051412072014944c4212640541140303d904540c46003154450110243d844000d4100100c14002d0031404d501a0850786d0040749041d0103408017800d07440039181081d05002e45680d080d201100c1003400114220384400309441000040c02da0180c010400170b10b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 792487293 1250 792486043 792486047
    0x21318020d0c030c11070806062106010815130b130f0b07031d030f0703030c020a0c0603050f010603050412050c1e0606030d0503010f061202040b0307082703040512010b0d050607 78
    0xd400480c5c85c0394400c26062020002c0020b40a074485011a6602403600e400c0074025030540d0051060340301441030000124100b43d02184214103081c01c1c0241203030507a030304a0300610240c088440582141c4614010885480500318000c035001d01071494014959031903510107525050440383c031000240c2d182e02c00c0c0c411008039051a03503500541c8004500385094214021143e11442e1700080525969a60188480e4000c1c0200030308da0750040642a07416584a03400780207410200ca03207000649810002250990082c0305050040e600450f106101c02903141d01503440e0391161014080318440d4604800d081c0360115048044840004040c060506028040c1403030000394200c03d1050210a000500981e50088855822100145040240c00440a004200038807454004020121000041104550f00451201d010f0389085221043c0a0f0290160303214002040034103030903c1e042000200424500001001505010000000780c101000c100050341c0b034640e9801100c80303400034070410107290303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 792488543 1250 792487293 792487307
    0x2060304141908031801110a1701050111030a0c3305090102070506040609150207140616021510120506040506070206010f0509090114010902070c09021318020d0c030c 73
    0x140c81c4070760200550752aa1054544d000041caa141d850203150842c1c00707840001d4000800400401f2499540c0352819800149290118111808244140d10001401e94841e082c0f0b80d158841c848043e605144412208480b446c0c240182628079074000b10018140b4804035a8400d105401000c040901584514540050702d0005040c0d80795030344144041400b0450214503d580f183c0d0040d070008004c1e0301441c00200c00384680011000183c030214202c030800c1402a00c40800d9018501260f0352540c859404102d851400b50701103005801110000c000404084e00f05a00803104988800140d51900e84400c1c1e5880400c10555640c0d100c0d4052105001040c0220b40d04500240301a0541c0d40c14824920070090251007028000d400e00000101e0440080d40300086014207440c00841d50b5039110315040203900b003038034191411414134200042480c00c42c400ca4075005001d0144020301c0b45828013004803035078040443c00350380c1d0702041000032a05084c4100342110844d91000104007641d440010250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 792489793 1250 792488543 792488563
    0x120108031305120703061407171b13051005070c06050403020f1522170105041511040b040305150a020315040b04090614010303021c2a0206030414 64
    0x140d0000c1040c1ea4000c05aa0000010341d80140c6010446168480146241903400d90000d0640c901d000b5001c0020a003075031100f40560030a40d00c1e4004a07006030911201080d003519400c113182d0100030032081c50a080000b42c20001d00c0e5200d840482e0355102c0c0801c0202602c44c40b1000001d900261100c100700751001820050505441c2c81410720b805c1d54003081c0d054031810102071103140401141071110b824a822a00e030031142103000210802c1c0c40040540c42e00f040d005010160003524400ca030490414419a407180e81c0041da82400200e80f0a030000040ca07480401c143c048104000200e58884036500034070042d4400c50051820b0300b64a04c003103920740f2024101c0121f1500420601004030508a140c0c5081da8049800051000720030700020020b100e40ca00041405007000004041c44089041035030480e03001e45c0030b031b030045041c90003079a1020010441e0003000c50350103c5800071031b41a0140180c0401c620071203194400b140c68000805c290402c5901703d81131140d81c0403c441205c1c090200601c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 792491043 1250 792489793 792489809
    0x70e0a05010806070e011d1e012a0b061f02030d0c0309110405100f03050a0b06030109051e0106210c08060c0a030203090a02101d180105040c0201060b0c031201 70
    0x30314203040d130008046120440400781040030101143c08102d071400006580307c40e006144107076a500340700c80d280402e9042d039003480c0441e9503035603007000321608403003030040035a08030000326484210340d5900c0030611405099a5005943d0950720725036540400c50322500202650001e61320303507040c1400c0600b920382d00c025060806003010204000100d0070050714051805c200c40218983d0f450b0b0b50b541c0e511380383c1c0b54003e00c0c55441d080000400e001d00030403a0151180610a4080e56070f50710030a16098441000740104268424008411082ca00700b800d0500b8065540010414580c1c4101e001c00741154116203025a480700d220f50802c00c282d4800600003421590007801003490010241c24141c010b02c5d40380d40034186c000001400010060041a800c40e03801000c1c816510300c0b1100041501e00001315480081c50421507201862900004480035803018030703c4030300140e00301003e1101900c801c44000003559241d801c04a031502c05500900f10b50903004c80110b031121045016003101c9801a0300c0200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 792492293 1250 792491043 792491053
    0x230a0606020c010c031224060801090b090106081803030a0e0f120a030f0902030f1522020d0318030b0702120f0d021b1219020c01020a11040e070e0a050108 68
    0x1c0e0076600525214141509406c05801e43c81c01149840041c100041c011031002e21855403001c19284020503800035034565580d04241e1b82e0321a00d07814105c9400e02c061035880350f9030500421102d4890000c10f648004c141c913070008400d000d280e45e5407075500140c030300c40d184903140c19807004d800c90200503007210980c03090020412120b2701d000d2803107039120f46400001055240c41d65650550456000f039a1041d070f0145c1240c0181c0e4003001101d49030014030a4803503005807204040742068513541e251060341001010141880c21003a820455032416504003201402190300840c0180300c0c52000780e0000714006e01d0100181e2038441c00080c10180c5810040516441c24813650503c018280147c43c4070f808945001a55154500307800e500c01e1442c90401a900c1c07042003400c804100e071510261003046803511003949400c40c0300d00c2c160323103074420220a60f0050703114605000c08900c680112503030010001e0400180615400300241c2010303000e8020010a406160a02c0313030803402840f8240c010040000a02 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 792493543 1250 792492293 792492313
    0xa06032f040b0d0803360606010c021305130303050c0a0c080a0507080f18090403021510080114100509010305031917040510061505090d0501230a060602 67
    0x89812004580441d0196540c0c0d98094407a454001582e1603443e0040c206603200c1c54030707169104100001c0c010b04003034048004071035148002030200644000c460389020300016504e00004641076200c680707050340c0c0b0091124a0343d24114091044900072104818a04480081d5090103016900c0240038424811001c02c09034a45980c06400d1018150b880160503540340c2280c00125514000c144001d0011100020050040c4c9081c030000c0208051103007100b6403084600c010494506c10450300940540c00c6032415000c01d9195820959201e8500c024000034035072a14116400c542c2d0b900d5140740000d10b110705101800c4039804482c8010401203800e402e966040d551901d450740150b41c078004c0c01c4c10b20600c074074001c1745c0604242c180b520a910044059842e147c20195618a014420103400c24a0080e010a410104d40005031420b030705a1200d514007880e040a0228140703002c0402d644655131034600b241d02d1170115000880c101556143c00c4181d041000d086422214540d006100b55409000302c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 792494793 1250 792493543 792493613
    0x2070b0f18010806181504050f0f0108010c0e0103020702031e0106050418051507090305151e100513090b07080402090c04050d03200a03081f0f0302060a0909050a0603 73
    0x24178804d0002804541c0142c4401d4500007100200040490b80903082c0020407024440000020348181c2850903d071441d039030703907111240c00c0300c00300054140062150604100c0650080c2c00503c082c502c040e080381c2c3e4010704818003445500031900e004030f041e51220b400304094034041c0034034001c074107400e15040600502c5903200703070740d9640340c80b404500c0130f6027480000c018038000e82400000b1038100090b1241052000e11031503004504688903014091714050050001c1000c00f59a03106401203218007492906100c200320192414217081817685464001500000304068031880c0200c0480c0c503841c0705d50074144100f0503804801840c103a815a81400100015501d0751003007020140c040c100089031030805d00807944031101e00d524005540c4070300340c0c0380d2080561244d10603105c3c04940c55000c1c1d0b9090f0320354a00186c040c40d80b20f0031581c82286101400580342010081142a0080c1400c9a00d1a529200242501c04c110340c1c603142c503580d81c601002802401000038003608910350307083e1400a002c1c9a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 792496043 1250 792494793 792494809
    0xf071d0a0909020d06020d0504060e010212070e0604031a060f190513141f06090e0f1e0403020109054b01150311062802070b0f18010806 60
    0x60408082e440c2c281002c25925031891020401d90172500070741d03036001050b0713031000036203406e0360101c03040381c900fa090000c03000701882500e420b809000c015200da0f4403844002c50318050512800f03039010004100c00030005400542107038268140051504151038024101701110104030300c0c01d0b002c1d41510240300d2280e00804a840c1c02e0f40e8045441c40080020120024001c2c0b800780070309001083e000c400d2110600b132120040b0781c80100000d8103002180c0700d110895200113144205030103944404042070640540b400300300e0380f040d44600c828100403c080e4400101d44003d640550141c0d42da0f0820701c06211080c80780359600601c2010700903c409500c1030040041c401501c021011440301c61003240301c051221000e80d0101503400013401841200c1c0b408422803030b51032000b12210b024000440c030941c2006001e841c444581e52550114480c101403030801da4400401210b400c600910601140985840014080c1e50902600c050380394100565a901840c1c10308501c581840445030030000f1681d16660 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 792497293 1250 792496043 792496049
    0x50f010905040c0b040305251d0910110a030c0305100b07030306030203030a030e070e07081f08070303030603031d03031b030f040e1e0910051302090f071d0a 69
    0xc002425a41c40c100704550403095045000441c034002000001c0c450001a0280c00c00c10260b090113102c01c100c03050700725801c59881011202c10b84400781da100500411225503214841000750b032100c5801ca4490300403a5610400303540340c00301c08110703681c070f481d4144603404c3c0c002c007141410000740c202207802c070002a50300d205654200e0b000081c041e040610039000203004650150440740c5410079010050060410303170645002903c03d00c7c1d8005183d08106414034011030440e00c540d5a5500d48156200056000c044001c070800307200c400015000c001000150011800fa03600028500d08600d0020b001105403000341140042d0074140250581e404012540102040c0074400302d494100c1e0301c0c441c00d5000d070222410000340042000580006c806104c648070386950008107440043c0113594414010040e01c202c071384c0d5401442010340200c041d81c4801e800c01076600c1104c040307000f42e90000d045020201e822582900e0204e05000303903a5082424020a030460410642d1141101004144026441c2c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 792498543 1250 792497293 792497309
    0x150b010c0809011205070201051501082415030106031505040b0f040507020f0a0f0201030b011b060b0607050f100c0c0206120a02090a06030e1b09041101020f01022209050f01 76
    0x1e86580b59a00607810f00000c40c0c98104148203070300c0c1c09940603001b40750841c0c001050f6181660900301641c0300d100314078821481651288040074101807650582100e4905c1d894100c005031121034a803031101000b44d4001c0c400d90341d010481c1e05005040c560480710326408240280d0811880c0022039032441c42100300044142c8001075159150b1208a180a503400e84001550003450007001c1400070200402d41c0982c001c0c1ca080c400003000c4401110180d122402c2900d001e04280c80f0b00000441c6038000f0440c1d504010001401c0900b240c07070726814255080c800020a9111403aa00102d41c00c03405618100601428007034041e0a0507004254103200d46492421451000d000207101c44840350b054414004000c2d09442c9802c0d1140c1010b401468095002e5a0502c55608640c0c000ca4918040c250300c01d6000e008425507817559030ba40c00c0100f8088135258154080c020280c2c4e503590003440a855140d1200988610042c0d00e5094090b211203140c024025142c04c100130010074031716480c00301e41116070f04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 792499793 1250 792498543 792498547
    0x619060b0c10151d0f100e15030307060f02120709080c0906040615050d05100308190c0b090c042a14041e08010b0d05100b0f040c080103150b010c08 65
    0x3410351610a0002c0e8000c03c07010132034003c40d11010403506407403a114400054a5240035250105003198100c4140300ba51480d501c0440003075900c090340000455802c4029048900701941756544405442c04400c04101c51940460829118800143c050350000340d2400c00343d14260a080119840c1e0350000380c0d480c0101030364400304d00301d601c6585c46080245031079109958504950b003001091907002e0044c00d00f9042c01d2201003030720051440206000c4039440340d4081d00d4601d03441241c2c00054901c040340300c140b01844502d84080b0b503402006a100d0600000a0003040310300904100864280031080078100d010291080c002d07107030161641c40001c21904041c500c02c00210303190703030141c81140c129a020600b85001c211580070002ca00e102030301c0355007000303010624003401400032292080c076018110340e1010100740e00c10442d0f41d01440700d4803c00341c07180303071035041c44804581655181c4e00441d0025500800410904c05282d02c0d03000d410b1b540c0c8800f0f0000c4101070300024804000001e01030711f00040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 792501043 1250 792499793 792499811
    0xa11160b18060f040b19020601050108060103050a020904150f1202240d0e060711030c0714030f0102040806040201090605030f040209060d060e2503170f0403050619060b0c10 76
    0x3a1a094420543c0001400d90751141c03660f045401c0383c0c11400503280b1852201540c50406070001c210541a5141079480406d503585000046025120191100500310b50822008885880d1401148080411520750440107031034103445004150a0742c1c090181102d0b40741c040070060b07540f01404417055040f4201c4003d81d80c140d4506090314454079218200c180d143c9034507400d45110100303100340310382540d032a601082e6001000b01500ea1044040b00000307500311250a100130b00c90b1040c40d18074a00003504940d840d0180c1c145403400c9a1042d00004080d500210411045680c080c03e441301070130283c600765081d406e0000000c6416007001e07000a104600540000328291070710103603800c0d0070780c00180c144041d42c400c09007140c4420340c0510b540e801f0b400c50350f0344504514030003840318100d81c1c0c8040e81d481c603c004491411000d400801b0003c01c40601004000701160040040383e000d042405100c2e0719400d41005030340102da6803980014055002404021411100400e2008500208000100384516 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 792502293 1250 792501043 792501049
    0x1e0b040c050a15140703021510140405070c03030c02010b0d1406070c1e110a0b0c010b152b09080309010e1204140d02030d0201060503011119050d0603080a11160b18 72
    0x18030f03e19006065041c01d0200110b050711465100c0884a0600360a070042b0180024402680d00441c0c03204007041e4600b00d00302c0080e129500c020400c1109100000e41086174500166401005038401c0d6801550442a940040030900515400038070382e0400120080e201c6d900e108469007940201c03914440301042c40c6052000c02c819110103071a000704042000350f1981011507003900405080d9031258600410100f0340d007001a9104071480d5210b0304581420b0031840c0400703e103400e6841d0030001864032800200402064045d941500e84108103c5480703140420317405007118010300b8104401c0d440400701c00c03056001e0f10119010b903490072170000225224840481c00d82038403140300940621a10a07035150303007941075000c14103840c000c0300244241d54105c0c1c0700081c18020020011560b4201015045640f4003030030040071184401e210100d04030340d0303e403100300050300403818940120780c03140610400808240060000270a000d00465011810041d00005da400f50050407501e91151040e10b5686039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 792503543 1250 792502293 792502303
    0x3070e011a0c0d0f080a0b090604020702031e01061e0506030a0b04090212030307030c1e030c1e0906121505040c020c060f040608011a071e0b040c050a1514070302 71
    0x10707001e030044907403959415500502404030f00511380002a000c0c8049070281103603004541072039400810741826a1504000c0200940c0560300490307043c41980301804590910280c40010b1803020340000a02a10782251480403c240340100a501010031005106580e5080203817500085d22120000301d8201c00b00201d402032103520b030040c0d070003c082c000344010090f00100951055881d540c05001d110450802504d040c03402079607410780711300031070400c00d1514426413000002e03010303926142031000c8030000710100c010724030880680010078917801400702ca60130001c8403a040915400c10007000024800d110507a04060107443d1086485001d00700f0030b5442007000b141c201000804081d41e80a0360100e044080e4000c0c801d039000301d178911000140051901960700e5510802040841c6000411360384d010f0303070b80d0610504a0499070b141442e50003090491820522403846066010181820101000780840a540c01064000d60a2200c03000c41c43e84101c1340a80e40203404d1500351128070b039181c203070704203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 792504793 1250 792503543 792503557
    0x3020918041b050a12080f070c031209050907020606010c0213060e10120b0c0f0409020318012703050d060b0c0a110303040e0f0604062103090503070e011a 68
    0x215406050205100d1248803440c1904a180b80d00c0c1c0c1559500c40511501d001d50344a66056281400a01d001184444001b0001c03c11425811482c1c0703000342d038071005007501c1074205440794100344440c44078068002c6485000f5003011601d060052504c5400203507a95002002e407410029040c003503000315141c44041d4400b15400e25418030030991101000140c0400c12220f804044542000c0000e40905140c0c1c00201d1039007045050ba03841e500d03501c140980d40e000c405030000e840820840005c00c10220710195004a054041898036280c01c0140030f03080da600742180310b00d2181d0120007140c0d107541c2480341c1725246515040c419107540a00c650f40300100040d40c0400307030f1100000380d844000c01e004114419210320a003400c1509450320010b1550f280941d0081c02c903104940004034000c0c2c294200045d034803078030041c80815100e44403222011002038681d0b01846d07a0301100041c40c01c05410151034000b0700000e8004108481c039122071603d051006100341c441260100e1950502e400d9900304494003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 792506043 1250 792504793 792504829
    0x17010e1618091e050c1503010b0318011104060f0810060f050d0905010606110708060a020306030a1502040501091d0a09020118060c032a080a1b06060e09060412030209 73
    0x8041801c0d600003c000b0000300448a03809850100c0c210f42c5043c4c9a4640c5881c3d58120840c1540c0c206041c0e0030f825030010f01b900021400c601040024800240194000c064a54800d180c5a0b03107407400240c90300e02004400e00503c58102d00300704240c1c008055903400c80c0d03002d1502d02c21601c6030000c240e410b1304c01c020074000c8103400c02024205110054202b5070032135020b56149a90390001d100c04c2900c0e00c0342030145100075080134000c20070b20850741c0c000d503412010003001da0300f10149540c0c8203042c10208103030303d0000c80d40104042110f0b42c3c000450100910031091307001000f0385548140b00c4490310051043ca2020ba036054008190f904c01e00b010340c00b24440001d40e0b1011070b12480c0c0a0700342e8284220807000030303000c50b540054a4030015062460b140c1454141c01c040d00031507607103110f550018501c42041004c980c43c50ba0b21010b0901d520102503014000c0001c4890401801d8045800e0043c0754000f554094410311001408001014410b089a8500180c40e0a90070001442c507210302c0cae4201c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 792507293 1250 792506043 792506063
    0x2070312050a200702030c06030403090e04030e03010207030e120d0c080d0e06040b0402040f060321030f020d0905070e040302031e0d0c0e090105040e0327060417010e161809 76
    0x440850100804c5107038022011180d828403000200201c2d80300403a001000181d50a2040040800b0b800303203160051310a0902c203807041c01d404040307400c981001c4816400141251205070081c1806501d20344407501d280040c18145600700000303080750954203402020f450b00010207914810107a8800e8dc407582d42e030300907078a103800c00d42004185074800b84c6081c0d114514000864400046502c0340d1012a540044d0104040d00d40c0b180b0511b82c601104180c505168440390421821503152005100c00d181404000461144a00f03255140c01d0031074204042d003645072414080840d4001007078494610700502e401c129800e5070104d600c1240a110760840440c0c1c1020b08503c1110b070001f501320301009050f42e80e1811603030703550100420340d8020464040290010018140107440d5014070f00c151400740c2c00f505007110030450104046521507407040030303400746a00b060100007801f03005110303d21a0349402064032280075210005c03408900c0c828031300500111841c21440350404e82155084640240d0400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 792508543 1250 792507293 792507341
    0x120a0503190e06070e18060f04140109200703140d06090504030302030106080901050402010f0e010201020c0a1a01140907050a02010b03010c030f0f0612081b030a1707020102070312050a 81
    0x7581d8000c00e03260380001c0b8000481400c1c0e0303401c1065150071790591b1b13407180c0829a21044140300004180001442d046601c0d444402e0044942c0240c1d14000c00345560000ba02107060710342d501a030502c544013030362011810819000480c2d03000303c0050081184000d115601c031061a0014002c1000d50302501c061403d04023084245600340c3c1c0918104c851544405c190780d0b603402003141c00c99008880c004d021510342c03804129803d1140309035001315101800010301d845c5515800625125001c041111500100503009084400034040d481c010701010952a120040b000000b964902d401450f1800b00174000c03500f400580d1003500a98000c0c40041e00070407900e0000a4020080c000c1809140c034580e003844425006035115119a404590601e00321401e4a00310b81c1e03422115134402e04180b0804c12183c03030365840f080300c10310080c1140b01c2e4580347d0074503422008845041c103010041458065910600407480030980000b0740400c00c0d0b0140308001495500c06280800404420f4002d014141e0101902 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 792509793 1250 792508543 792508571
    0xa140709050c27100503130b01030b0603010b010f021b0109090f06030203070506041202060f0f0a02030a0f0c110409050f0102071401050901052202030a1208061002120a050319 77
    0x400c42d22403c040c0201e0200c00060b10303540001c444950160f089103083e5030f86000c451260703024540150002ca0701d40160304450b155600a88400c1e0000e650030320240b000d0108503d402d2058840701e00c021300300a04a200d501e18065200c82d91500c42c80401e0b11403501c01921684914050b40141403001d804000c003000d580f06903402071003a030004030f02a1103041c401040320320f0980151400c9031241743d40400c038410f1035401e01c4400e03004419100e000c81802d21040d04a00c2c80e40003d09a03400d9079034001d5440d030007021030061521400f10030b10018440801000d5011640c0c0c4580d801140701e05580104100b4003a2400c64580340d04404482c11951020503041d0800c440f05541000002901d40203100307940303034004980c2c02caa40a0b28800384611071260001c40c11890380b80c402900301c0c001000e94070044803580328000800703801d82c121400186140c0802c58245400d000c03c0e60006240e00c02007004620b000303c511503a00c40e280e032510600001100050036005c060080c4030040104500038007201d400c8c0040303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 792511043 1250 792509793 792509797
    0xa1712070614010509010f050616170d29041d1903030e010506030309010f0203071a0423060711010902100503040b0c07082704140603010b010e030a140709050c 70
    0x184038010b00100000281500c2c140444606845500b84601c1c0301a00c1d09081080030f40c0440401020741c8000480300b000705040845e41409000d0b40840750796111600c010f000115808203549811128244420118032010f14420b08000c0790199000521148003c120344680540044181c482d4400c00c000d02d034a401d80300d02060035940c46a1414460b814400a40500340e4008640280e00350303200f0b0018a4040d84034094660803080c0e140103072458040240c0307684180050090780410385142d52824881041103040481e10b4031410046800c2d26030b4060400c00740c40b10405000c520410000c1c040d005144c3c1e000b94042c000490f401003003400e0100d80d001000d041c9402c101c034140c4e42d40c40d903600008c000000c064101d40009a10900f510701d05000004010014002c00d241c03010f520151442e20300c03840d180c9115000701121402c114212074680380c02050f017540d503480c0806040140c8111090b480341c800040403090346070702c00600d2200111070a1001d00e0640158400d881d020f0900003400206001200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 792512293 1250 792511043 792511061
    0x100e0d0302011d060f07050a11120910030504050705011404170a0b18071a0d0f0b030d180b070f020306070503010519030302030a0e0a08070303020304091404020a17120706 75
    0x70040300c3c0603060594030b648544d03048490848081201c1c000801e03280c4a000140030345003803421300c489500301c480442454010a840c008158503070004040c100c0d45801400c000191405180601c010302d0269102600da030064810141481541c2e00d1603c00380042405440242a401403900c84004c1c140712019950101180d003035803074039101004100805010f48500c510015040c0080c0300b014601a8850741c0180820f18030700d421030081c81144070000d02801045134460f800700000c100c42d070380b017001c02d800c0c0b03640c40b850344052040103009450301030a000d4002e422681c04280b0303162542c50380d00700101d90541c080002035060041c4c0d010414403d8108000e981610410b4500600c1e11400e810305642588103408081e025034800d12000c4105881000c004000380c01c00340144008681c1c406007a0b150800c00d41046016070800b041c00d200c401800e00c540e030008004c0f0303510f0740c0c01c50401e1307008100000c0c0030303001c1d00f803c0540350689016440400c00034031a283c4011945e140d9101c0860034404010b0000c15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 792513543 1250 792512293 792512321
    0x21b2b17030603030f0703020a2a0e190b0d0b011d0903120a0c09180204241e2a021017070e0d02030d0801080f0d0806100e0d030201 58
    0x10340302006038100e0005892045502400943c07070000c0701e50075030000d03400180c81241140f181000900004001680140004480c1c07060070100455113001c1040001494001220606480040210b24110a550f040c00d4ad030b001d17540090040318000c003165410303180c1d6a01500d18000580000b611050320112031f07841c1100f030032406160780c46000184d9100d00ca148902103c0f9a03a00d000b040c2210040d078407401700040e65007040542c842e6648100d1001d070000851601e2400d42c0070808026501d061000c40004c1c0d690740c032a0002610800c00040e0101500031046003100c802d40d10391440301405044500c0054049890301440903a2040d180b000740d00c1000401c80c02012202000012680124000715100504d480100c3e01999001c100b11a8410410951a4400610411a4090384091151000c0342090707560300401076040038070061800d400402d4483d002d91080031140c004940c02200b6680280c1e0850702c0551503803460b801140c0b00c212150321203901200807250f201c01c1680540c0b16401040180b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 792514793 1250 792513543 792513563
    0x60815070f140708032503050702071a030a09032106031202030304030e100c020d0f020406150f0e15121b0c07090216290610021b2b 58
    0x10707400c03249100c41d03001c02d9a101d28148041c1000a0906000e154404060041902c4220500c41286600150f0074041c03804241ea8005000403030782d0600c5140082e1640550303251000c0080b031020100e5100052001482e01d47d80c00004007010701c507180c640f56810b20050b14841c104210358040004040070310049030803a1400929544450011050340c1c0b0036a01030311200322045140701401003400e90502d940701001044984e03c0016030710034101440450090020051803051441030200b25555604400102d00c9800c100c0c00145a001d003c50040c0fa0340752510500303441c030490100c1c1d075000100190410549001c228424134402004000d4030a00914007004194210300c3c1e103036003103482104140101608000781c20301c8203403510f800800c088050001044e021203410b403102601026014404a401b26200c4044402d140300b01401a400002c22034074501404480d82010350b840c13030226001822a0320382c0790308051550b00d8215440c880a0000462414140715009604828403441400c40f421128 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 792516043 1250 792514793 792514817
    0xf0213080c0a0f0b1902070b070c0504060b0c030d020c190807030806010305130206090d0b010e010608010b120106032a1713081e0f0d0506040b0d0c051306081507 71
    0x111440480c201c818800d4110700d007407a40805e02c68071031000402c0800717502c1030100019401662000405520f0302540c681015035042c001000b0079104c80d680300900040f824460180c030f2440110071510f001c20040c400680d601d561064460524040c40314003101c071017800c0c00c2001170003680300040680c680320390b864561640d5048019001c9075400c0d02c0307040c52541a9601e40d401070400b50024540c1b032400608101603130202d80e90307691208800b6001544884c10b4413004000e280e42107442c090241c4424251a030801256500642c06080148140020552a0300d024004240b001d800868005890603d60120500c0c0800140540e43c4407046d2a44000b103040c0000d9031275583c40e03440b5040384d074031061081c941140004280180301c80124500d00c0f80004000d001c0c4040309820007001134000508020882d49032200070401292140c00c90103000702c41e41445240054080c02003102075540c11150314813041c104420b00001440e40d50810b016612401c0c00410f00c404004100c0b601c00c226590320750024101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 792517293 1250 792516043 792516059
    0x30203041a0705030115050c0d2007030803060906060d1d0d0509030604030f110a03030516030506150a1205040f051905030910140d0b040b1c02040f0213080c0a 70
    0x40c101c0b00701c0000fa10910051000c11102041030034003081c40c2ca0140c0c100707030322868180d007041d24002044004c2510f00c0000854410040c0c44d903662a4800405000e0840c07440e201c840640c40000c00703552086c0340200000f46196600030544042001003581080408003260350b10b44884035400e520861880780e140105c030105e01c21011140e0100014000d001c4589641d034069400e81a000c0008091001da41c00005204c0d40402c10441b0b011b0082d030b8003241904103600d10300b45040c42c040d404d80415003402c04005080d1200c82840c185e540c40c0c008903a0b0395245002044954075140c4001001440c24402804144003080c1c02c0701405c14003580c00c0d18038010200700c10455500d0b0704100106141c00900541070b0910300194600142a8141052010700d500030404003a5a80610b01d17141609503605680701c3c00382402d109108003624191819031920000f02c86022070440103070402845152070369000c8000000300e4050b5581e80f21006802108070ba11003000c030f03072100610b480f4180201403491001500744 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 792518543 1250 792517293 792517343
    0x7030c030c1e0605060f0d0b040302010603020603160f05030103050d0c020f0a03060b03010609090c0e07050910031b090503030d0203041b03030908010b010512220b0a02180906091f031203020304 85
    0xc04010444030b1820b03000d980c8c0c541c0c400d00040c825801e5550312078001000d84c89032001944200803031000c0c8540e00c240c08074080c1c00140011602002c100c000c2c001440002c0c400034071030030500c40504050300c1080842c40000d5045001c48600c680028024400101300309048d04403a40d0000c04038000e200c8a503c4d032030050203d44086601511346000c1940800c919420715800300e8005d0306034540346181001c1d0601103040e85017140c403464000b95440d04c04000034944101441000c0b0f6441c0b81001c841440c0100007540c90052442400060340d002000c6401c00100000880c00307103041440014002d40e072418041c0c42000d4178030803072021354204140d10041e503129130102c8404042e045202e40303150300d40c80400000700314007840e2192801c50f080024004660a01d078900e1040b46203803000350780c03510080c6401e00d4000f51000124026891030050010540d04e440c08641d1203100d081e10403006521012511000c171000303a201919000c04040040c100540c541c004600c1280075034442085450400540e4402c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 792519793 1250 792518543 792518569
    0x10c030e1b13020c0619050f0c030a0e0106081b100507050703030c050a0204090c0810140105120a080f27010e060a11061e100b07030c030c1e060506 65
    0x141d654001d024124503014054445801c0160001410901c1d0b4900151504800355800445a8003428054508001a02a00d40d021500e002c01c0340c1a810f0010143c1c05900003d07040c0e11045844074040b003603001d0254840c0000749491300888961044040b44280c4694541d900107020301030664014054078024022180941c4c0d100e00102007251a41d281110101c996440c101c1d218000c00711610701507501d6020700c000070fa0151791404d80d5549400b034042c0c50b000464051082d03490412041602518400071450704444050380e05164481c10304540a00344074124400420380c103004104040580d40c22800390a99544d00d0000c000c0100031104920254507451485500056000424288030300b06040078204010160800805808000700907504010b4222102079400405046060254505074005500312900c640c007140c00b541000c03404041449070700005001c7c000c0724484141011320900c03141c0c50140e004900302c0d07825003c031955030626019182081e20f82c5420440880c0003494104c6181c641 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 792521043 1250 792519793 792519823
    0x2812020607020a110103021c0c08090c010207210203030316030b010302070b16051603030902040b040506090c2206021b03030310120602070c15030f090c0501050c010e0f010c030e 78
    0x70301c0343d050b5507000032410050303106410550240300170400e00d0929034201c20400c4204801090f100404000207000311001401641c032a80301440046160340c000c602c2c9010364030000b00d4103a104484986100c1c0c1c110a10500a400d8440082005045420035444030500d5240e43d6007401815010b0004405038015a01c0141100d456480800e8403c0300003e858081c00d06c650a03c0b030f040a0075814080030f001c848500c01d401003038860f0300e60700851400d481004250b035000c40c2d041000d820000701141020000410100051000280d11018a9800c0c42c1d014901d03151085224021512004029212001218040030060420103c1d4800340340200c15a4422074210000a12242c681401090003600c8014140e45482d402c00c102e0000c1034210781500c014040c4004444c60300c3e00c2070b4a0090880b18442a903410661821138070000150703403500210111082440c046803941121400700f8010118000520700b28411030b0b64101038604190000c041580701501c1c104071001140c42000e40300c200c1040ca54003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 792522293 1250 792521043 792521053
    0x6030607051801020c1c111927020414011806020606010507031101050c0a08010e0f0408091305183c0a0f0c051c05120903281202060702 60
    0x8401c2d240d440c003101e041e5051040f10203101d6002c001c19000e4821420724002100c3c0141e0b10818401074a481d40c01d50f003800c4d00c4021150090401c132085a4889010f05a90490815a41500b01020595140800c940e40b0411569161360701400c440b20b41000b020a40172401c1e0034a2118040c000341e44c0003048400c4c64002d0000d59840c040116900d9001e071200701d0078418810803421780204244141c07445603004002455640803a00e0f03000d045845c2c141c0c1b10300044091603003002001d034910003c080d0010b6000820b47e46803001c0c5e80005160246034080240c8103803610381048040400d0741c0b00c1c428403049603001e075160103081030291120038144101c41c410390b6600e2908184001c0c107078a40018540e06200c255500920165103610152200030001e5442e50340a800030701c007928120038054508118120780f558507030f2440d642c0b1910f81c4e02c808400824070b2030100b20568103440c00d1040303002000145000c0100e0344000103144028405800e81611401c401c1000e02044500001e42c4034050749190700100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 792523543 1250 792522293 792522307
    0x1505010e01051c0e07082a060c0a030215060303040f140d150203073009080c0f0f010c0e0d08071a070201020a0f140f030a14090f060603060705 63
    0x154218400815041c10010308100f01144000700d001c50025100c11400c010812440d4800304134540203194010402c0764001086030104030300703d06140b4010b204010041c946640007003001034414000e051280b031950007184030700c004150303003c18129003c5540d5003945405071aa5000e15030340e4042c83c0296101c0c2d241d01c50044c845201d1804058000d6040180030744985803243c2c0e1481034140c0c00100140b03110b80c021050040c4540c104020740502514100c1107003401d505a04080410b072500c1e4544040303603946045000c01e1144c1c20080f60040e40780c0d0b500702c80382000f6110b40613654800c0c41c0c2c8254440c2d4600000b892a0901c02d10407019500d00080050b81440801c0e10380320040d42c020f200c00c89002d04141c10407846080d501a0700c80c4104d0b003e400050301e5003841e00014108824004820003081040c0798141d01132142c010a803030008507036000c915100e545940d40d0800905c00841d01d0981c070b02501c000c000c031543e13002941c01d405d56195002d0b25203a844483c1810355800c0d0030b42e110780200301c048c403001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 792524793 1250 792523543 792523547
    0x1060b0f0306010914130e190c03030807020a0b07110a06060f1409101a04050910170f07060309020f03030325020708060a05040f020a0807060f0e0604050603090a06110702090109150501 81
    0x9090307c1c00a2060380d0381d601851224200412000008440d403541d4228100b09058008060650000d101c0c006054040000e94072080000401000748091248242d054000310f6800c0003010710b429802350782004071030303201d1000500e00520361044d83c0c00c88401c1540b02000c1e0402d402c95500800218443c610303c1d5007410040300d4504015061360b5050174092000040550740d103c8842d004800b150a1070000f54108014091043c004002d40b55603036014142004c01c0a000080801c1114014a0006554010f51000a40b00e0507a8200d20703074184400310500048449042c2c0840040c1800400c40040074403440c0c0c180e0319244184030356581034025000050b080d5000b900000c2d4400d04c684079261000c021303940014007042180d0055111644810020f11400e0f40120342c1580786503a60421070000702c0008002140d034891402070718000d03800480400c00301c2104008401c0d85a03070000080c00010000280350889401241d4240d02c2460302c10300000b03807041e00d0b10074140d5080b82e21082e04802030501c001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 792526043 1250 792524793 792524801
    0x3070f0b0118090807060b011103040905040b090109050601030b070306181b14070602031b0703020f010c030b0904020d060e10020a020709060b221211031203070512070201060b0f030601091413 84
    0x21f0506014400c10310210344501800100302400284d0310008031030a0508084000d0b000041c4a486140e01d001d42c00008154000740007811658041a811010303075940c40114040d007065480300c800d0300707081d1b0300e2a108202d42c1d400400d03524200700034280803944210300855032040b842c0301c3c4100054041010743c02150440d00110307840603001100c0d6003001c0d080012145286d0090310309030016004940c90203100b4400380a8052481054a828801450307550b002031b400d501d015100034801c009a0813036008000e04c0d500702c000580c0c0d015043d00c1000d241c601042c3e01030750040d513070040140101e4002107240d8180348140810f44013604928ad0820000200c18040c480403a420300412aa440000248846070822001c41543c8a040d502000c0000340341450329182c218a40c44c54209004e000704280168880c1c142d480c03404003c410307003e250310b4000059004140542190122820010b0000034013420100214007511007a40c90b0212030350780e10341101e21000d44040c5158084003c40001d209034403107401c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 792527293 1250 792526043 792526061
    0xb09030a0c0902070b0907050105300c04030c0f0f032006040609050306010509010509070804060e0712050607030504050c0f0303090910080d050c0c011103070f0b011809080706 77
    0x2084698181198945000c0020366500900d061500083c04800f00510290129080300c0b810000303000305801c280000e4240c0c000c40105a9416200450081c003002428110365040050044200c0080c200580b0601141d481400305680d0742c1c410540000e000552070003840304403002d003003d001c240c60841e5100c4030b502e0103c3c44040011003034a4030650440d40c54500910007892540c5410f46810301d1320080c941488016803260740300e015510010005525903804a0364050351510f4410303007581d1103103020401414400480da0087c032403003d000c00e80401b036220604884c1c0c000c3c4111034090342e0b0340e0740c21410b81d481190014165001601e488000d41810900d1074104040201520700300702525000c21030428045a1142001d0600b0314200401c1d04c05000c1c0341d2080c403c80c078050345801246100aaa10385640308a18100940310100c03100680c8140142c80e4002c0d0b00042c102500000782c01d000100540038000d0b52040b00001e070901c1482b036006d209501500c0c0d0f2192145042c0701242e2075020041072080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 792528543 1250 792527293 792527299
    0x304020307062607050c240604020c1009080d180f06020a171e1b16080d02031302030c010c200a0305071d0109111206030c03160503061303090b09 64
    0x5002c0b54201440c3d202c185200c0c0040d0381d149a210142c4c204114030f01040180415580074210a40c800d019000d041a158407000664005d41e4468512403450b1810001d8602d10380341c0307843e0121000c104102c480042210319150241400804030541c50f1504017105c600004041101070740d00c980000e04160080d001c02c06560411300c0803400241d81c00400344030119a180110380c8203448103e86201070088680c1c116100c0042184000503401ca128100e216924013440340702c9644540c00200034114080b9101048c0c4000155200d051844002e4029900703008228440e010303080340b948255108a280d00346064220301d003811141003408582c410102c10f82d00a0b500100070300c00c04404104104480c0b0010500a13001542c05504441c0c0354000e00030607003040c5c4c849418003592042c2c0100c0a012742c2c601d00e200c5201c001c8107440f1940081c1c40d000b0301203400c64050240003800c0403040c00300341d94a005c5450a0341990180d17a200729103d02c641b400a0700040200b4000181406078181820190107241c60203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 792529793 1250 792528543 792528587
    0x60d1b050a0602030310080c0a0303180906090504051e10051008030309031c021e0306011224150206180c0a03060e100606020705060f04050405100303020f03030402030706 75
    0x25601290794100950031100160b40000203014010b02034003103100060690f18050b01f00303c802900003405c0c1e4071b400d100182c1080b400d101003003044454007220700001c121a12003004040c0c1d86850f2980a0482100d0545031070003004100c607070301080042c3d0914442d046a01a051042148048c0d50051801501c22020072118a20200306000c04000450142c1c440c80700640e00c400180180e01544260070160380030050052140d807546030a501e0b12031804000f1000c0a07510390340e68800403a4a019003900340302030309040c8060468204c1c1c0600506030f072450110f518120396a140d8a1034103010310300780c0d410030040e40007000190303401c00c1031000d0f1f040e42d604a6090707401c83e18194000449011654006880346640c0d5082e8030300104041000c094100440101842410b01e03240019441c2c051034490a0301500f800520a82c0e400c075000222005403d0060080150381032001194800d0015400114058172406c1c00e48803801c140041030383d200780d03030040042215a080280403135600202d56403d1141c1c0303002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 792531043 1250 792529793 792529799
    0xf0503013003020a1202011e05090c13020406020d03180f1403030c030604051501021c0201020706090b0a2712050702040c020a0c090204180b0d0b0115080f060d1b 71
    0x315804180301c05029900400a10480d4148442c2103800303c020b54040d0ba1401d0119590840c1d00300d00c3d540391341c0a03080009669a6045509800c03c001054096030103c05030b03001000110250b4080c00540b4996400c4035200c82c1c106100380c0440c1d5800307003410417a0500c14640000150300412188400e0302c100901070203800c0e040d9034249035420a551a05801202008016041c14107205d16903001030014070945059080c080041d407184542d0710103091a184030044401400d000750103c800482d031000c402c02c8080382d2401c084240310010394040c802d5a0409070fa00c3d50341280003181c4c5c034400e151024205100340305c07aa1003c070703103580e146025420311109000f2140569070300d00c05c000c1d1072519078001d00305a00c9546068a686500741d045a07007450301c140814044150000c2405003221070841000030303004401c00c0003a032110940800107105080f0310340007081c408108044041450001e40341c1c101c0795100c5002c0b000c540e0078121001c0c1e80040d0788a440d0340100e05a0b8504002c4a50300041e4180b107030781c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 792532293 1250 792531043 792531119
    0x604080706080a0c05120a0c030b03031315050a051c06030204020705060a0b060a052704110a030c0504230409080309031b0601140d050106091a040c0f050301 69
    0xd25601800c007040c01c0034100805801940034803000000a03242951400c2c280da0442e5a98000280c41c1401c1aa614003601f03100754025800117111401c014200c0e0386a50910080821800b8a40202507101c54408010700c032440c0a0740036142215099201c072400c100c0c0307006649100110718003120040e183c4500c800000358460384028030104d40900041e000520f00194050151a075242d0841c0c081d000800009250a82c002c3c103561b4015050100c5851060321080c021662012035aa0300703910624100381c030030700340003c040102a00343c01034400703026030403001d0f200362002d0045100340c3d1002c403a40240c5030b0103074201c2c281c1108210707801030000894454644070301c3c066800c00c80b1105070b21f61001811000da00e2040300e42c00490450b01000b00b5880d070500341003929846920740c0e850b0061080381c02d071504201c001e4005002608044000304400d000c400001c01e0554400c11000d030081d4600081c41001c20300c01c40c1c0c1c00d8040b43da607881d15441c1d81d18100300c0180c1070050107801d042c613405d1880d0981da505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 792533543 1250 792532293 792532303
    0xc030d09030308071e0e0316063039120b030a0512180a050d020402030402030a08070605010e0c0a0207050910050619170727080a0318230d02060408 65
    0x1c9030317580d5088040f091441c181482c1a2501011103030a04689000b0005550b0180d510001001d441040c0168208491400418041d501410360103040c00c1c841e9a9000490440781e540304d514000384c0c0740000d044a66000030f0b0307891842e424030780042c0944440b0103040209030080d000e5400050b0845808100701d072a981c0c140745806410900c24980015401d00f444043d114044080b40200c90240e0028503180018440001c51807009000380e030003000080035547d0a0000c15a083c1c0c0018100e40d40e801146080f400030704007400780c60b55008245001c80d0809421406130b50004050f42c0007410210300740410054080ba005002c0c4030b03903e400e80b00108142d100c40c0080c20903c400c401180f81c3c141c0103000f018040e203608a401000c03c940702010403a02c541e01600d5800c02001030201000e034064609020840c000044d0040b10580c481c44100100701540070b4025649008680c0c10075801d6511030b00c13603241126682c3c1c6046148903440d10f000803185000385015260f0303840104014500751b9220380040c01c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 792534793 1250 792533543 792533597
    0x1112070f020d231603061a0613030b07080708040f02130204230607211403070e03060f0714030606071209060224191d010e0c030d0903030807 62
    0x60044907100c2510f030150700385100041c000200641140c45440e80076460503601d07840007801084c2c49004420960480400c090395a61024200681e504c034089081d510007000341c8003c80310420010300083e405489104034a0040c50039644503681c980700d94031280d01070041c500090fa84001804080d420300d40700e610040c0010803c000c07070305001d00b0094101c610300020a1000301d00a41c0108080c000003a9203848054410320b42e00c1e178407185150010400c0301c0900303415131100c0c404400001072001b416000301404030264002c504132907056484115080810720305503007000202c1c041001444030f90701842d0142d68070440182005080a0094a80004507008840ca00d404185000b00600c00039506005100702e500d1403058448000340c1a580c40c800c00113000300701028020260062000c500c0103500101c0341040401c880e068114401d03500380d0b008116008183d100740c421582c5503802428007007201c921107009030300c2e101103940c42d64405a400d1180203100504004194841034250320044070030340d8003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 792536043 1250 792534793 792534803
    0x61206130f0e1b0d080d0204081e010c0e060a0c0f0b010303180f15030507021e0706090909020a0302010c21090f17060601030b041e0b101112070f020d 66
    0x11034905403080343c00d02c09000701402500394031401118032034503102c503c0f1078403540c04000c1645d290648508180240540c3e00041c401e4001d040d0b070748a5040b640c0c0328542da4030803003000800c0340810504040d60310b400001941c50b0400340600284900c14040d201034010507000c1c6819202c0f0380459990091030400036041107020441c00c0800190744240800243c1c080d185070382c0c00e50740c00e40c1401081902d0860084440c8105900c1d60001100c2600c2400043c3c0012402203581007181c182031303e070680b20703d00750103000002003c4200c0010101820b0050010054002e001036080306c0c290b4004440c403084440069507900c01d1401c000030b090044100708030304807000380d4403466030900303050115200d0300813a440342d00860f6094202000c214000300e102d0760090003d00f000507800c0000c00214010b00800d1b0100401481910841c40d0400d010340c0020345038000c01c6035049150742082c601920310549000305030b141684041a0203041e0b0340303401e00414040f40a00c030860404010f076400289004071004044030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 792537293 1250 792536043 792536051
    0xb13140f040e0609060c12010510090e04231b060d021b0601082a010e0109180504020a120f030c0515090f1c02030d1505041104180902061206130f 64
    0x2000c4000c1c41601d4020038054061440d05240d00c810000f03100040c02010300c1801066110700c82c05028500c8013008000803881604cc2c4e20f09401e0070b015200f262000c0300d4142828602c032400c820302c08202e00c01e002d011140500403403990710081c00603a8111380c0f00e00d610a5401c010320224040a01440c1846010100c0182080d604011000742004c001c80550110244007454502020031a1402030310300b04828a06101d0703400d403403001222076940c3c0303070700604828940607403000361142180c0080707100758020360719080515038840d50b15015104c0e5030000b07000340448640d580b00213442a0402d01c0914000c5041f66180b0410590030403142d00c2c02d581400c40742c0c0c080c043c08000503a040c088000c0505200d10741c1150f2003c0075902030748a105070016400051313541c042e4000a0300310103250002404001e88100004825140380350070b00c0e44a801503030410b440564132100d90040c01d00521146a0b0701070146410158100a4014500c05c007805c4039501c2803d10310f031045400410302c2208030003000254042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 792538543 1250 792537293 792537301
    0x1707090c080105090403030207021f0234180b031524030304060f0306030c031a0f0106020a030e010e1315060e03061518010608010f0b13140f040e06 65
    0x4031199040600148111000100a41c1c0d44a0110a40c440d815080c0036135070740f0003403002a202c41e0140e0780c25400e24804024026296500140c1d010400005614001030a00000c804040b44800c80c10341c2000080d1a1105000b00142d520340c0c09105c08800394045034a0301c00741d000908150703071308114036440c0c1e041c0000c12040c001c3d100301b040703000058000c200020090060110f0785a1046003c4c80381030100c002d102c2e94005219900000041d500004c01004481e16031034580400e080064180301685400804240901e1504648504071540c0f50000e100c158180e941c180c0d40c413140381c80010f042c000c1e500c5070100300b6200e6200004a040d142c000015000319a80c8111132042c080d500300804004010703003c031480761400a01700b0f801416a0707080700c1540103c840000c0c0c03042c00300e40620494a062a000194243e00315507070a050303c14011081600c180ca0320050b12103070080c800317030341130500e8040b504000d0a12030742000a9519006001c500340804580049400d40b03840071901600c03640a40100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 792539793 1250 792538543 792538559
    0x80c0606010311180f0d02150a031401120b040f061b0f020111030c030c040305120703091a072607050a02090114130c021e060f06120706181707 63
    0x4245a000c07100c5203130309080860102905803140070344120f026441041c1d131003001d5900c1c8420b07207400700d9004100240412000f050f030b0905030400b40094010a0a008071050164411285181030f16220f822501d0345501640b51103c0190001e802070341c112048a60b0b00e070200e08180603d030051199214010444622190003c000155000d45c070011640341455039485000d0801c00ca0f40c11161000a05031179848801c0b00755400d203c0d907480148240f282a8a810a0005940103000c24900940310030103442d5880030100010f02c11404407a1178007108221b4200007507003402c80c05007204100303c3e00122100c044482d090059014041c1074410343c0c040800c0b0011440c00f0008a8050304851001100705540000410341194001210001d0f0f44d0700c4001e40341c5050b100b04540414400a14010b4515403800c5459a0316102c055400ba0a0701c14010300140c000d09011001c3c11000400500038080c251400c9000c4680306440e80f4078102c1840e82c440001949103043c070440c401c043c3c401000d401c01c507140c49a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 792541043 1250 792539793 792539801
    0x303180b090601050328050c04020c060f1312050a350907060206131e080c0c0d021e040615080f07020c030309010c02011701090f14090a06110403080c06060103 70
    0x18520036407081d0b4442030740040380240e8107800c1c100d040410001b60700e03914005003800d00c0c038183c042d04540b01282c2030600c020000380240c01840403401d11400ba40f5443c6201803d504600c1000d03018804270315141002d0344c4904001c0c680d1500b1450300b0030440c0d0f18566802c4500f147d01070780c5003440100d9070800000c0191000b2081d008100040140b030a94a0544080e445010040c80c0c00c55036400320311154248004404e243d440036100301141d20710f4107002c0c40c1810107130700030124410151180740c028819600380160442034854006151312180e0b01c5403c49404020640114650003a45070540014402c400101413540700d4410f0f20f9061061401079559981010000c3c00c500441d4420301424455490220846980507070a10306122941410b00042c2c0728410380d0440c00c10b1700b9031a403000084200710f41e40f00c109025260101440450001c1c18800403410007a101021103400455010f000151954080038503001c52130035007030600e039594981c80000d41000b03000100c160844c2e0b0412200b5a8184a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 792542293 1250 792541043 792541049
    0x1803140d0e010c110303011214030f0a021e0303100302041a0307080c1906050a0c0606170f0c03150a0e011107150c0f05190e15070c050612130303180b090601 69
    0x4c02917003558500a0030300740b03c3c2c0d0362200240560103500803101c0c0f502014811245100303040a099542c50030f00c50b4009540c0d4a813443c40c80a540161110101c1805010040700d020700e00751000071014904540802008211508400b50340c00000c040071000c584092085500030300c030880160408401080510002021245000d643d00e64403103c140003164200c0140c0f84405454075180c088401c05181c80801044c07640c0000f21030414994091501080000718012510721010681b083d8080c1c15040c0759940582001151170300d12402c0010399504030b9903203d1540c00c96450004038118403119046000790b404a14240c9208041010082c4020254007805503040702c02d25140d140c07081c4d441802001e601480c1015441c5081c040c4040410341d125400101c21075000800d00c00301c0302c0b6088048600d640c49540c0445c0e10180b2403000045a1502c40150303100500000ca070b03090140c2d94410440c080500504045040c50ba80d0400041c000701c80b5000010742d5881030244003481d0a0a101d03103403610700164 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 792543543 1250 792542293 792542327
    0xc120c032a0f01050a110118051c0f09230918070501050a051c110d0f15030206040e070c1e02040e1b0d02060904110316031803140d0e010c 61
    0x20a02d4120b0b903401400c42d011510103142c11079401c0345001030a03025000d00ea1a0490b4500904505e41c00d0042c04595003c1524070890580c400261405c0e06980340c0d1003200f940d0000c40c0e0700102c100070b2086040c880790144410050013110540002c000110645401e480c0c4000a60344014810360b42c050403c2400094a400d00b00682090b20340b260052283c42080780c0840c000240d84901d80c00901541c03c94000810300840150721582403900324402005840c0c1003010302d03410a880e1140302c42090003681d05407074016080070b01e003506100c1c0480c001c0714083e00780c0c410032000302c0403100414141c0041900d5000b0043c01d000061304240100410740303400251075043e9800145042c0f07010049a0600003000078141c0d08070f40140c25900016109001e0103d045400505040b08a44aa203024008600caa80246c6801c1011204200e00300e049400340f054200d114200d980c1c6c00d50209005440f06110001d40300740b520316001443c2021402d82d00c644002c401c4a139110303c0200500350b0001e0100d040d082c07000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 792544793 1250 792543543 792543559
    0x6080f070b090a090e2406030709090b0408131a0a080f10090e1905010203010614070f06020f0405060d15060c020303030a0b01050c030c0703030905040603050c120c032a 74
    0x2000001d404910a104e0442c1040d603604680c81c801364184503450000c6104504590800400b0428052050701100c0342440b0380207107a004600f60718180315643c10130f030300202c44a910381d80d29520074000e98420465140c48142d1100c001880c0344c8261100d4101d1700100b489a500c643c60314102500305c00003d007104c50100300913010800c81d2a040201401202c2a5420100f092800240b4083c01c06050030001200045504600400c2c80415002541210880d5031100780941010803045014011100b0090640c0300e60891400400d125401030300082c0c0c14038680038682580d482c00038141c0d0788100d10103070107692100091001c18840044100c0102603e00f0031036400541ea81c0040c1d00e0741710042c450070020342c0e209802c0c0f00d0742e445102620f10f90095442166901c2c002442481d030380d8582ca11040340011944070000c00c16003032a00801080325408401489405544820400310301c0362400000d90030f100703032000c8401e640d40c20801601d4030701040c14140e00d10080e1108000c01d980d0004040c0d17001c5c5c040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 792546043 1250 792544793 792544807
    0x203122a0f0922020a03050103050f07061d0312030901050f09070522060f12110f0108040b06030a050318090a0b0307261f0b0307030507050f0402040906080f070b 71
    0x6400481d14000d904580d00800c10060014003610f1400c007103207003419948045009402c0036015441b030782c140e90148089589003080481003550b9001d29000d080000794110a00d260f139480312900c0110000001419500f183c42104c403030030240d4204030713100b00250391070f8400c1c0a0078441c50a18030b074210a2041c040c1864034101303004108001e0b640c0361100c0b0034000204400d0125803843e44150301030078000c0c40d0450320903a290840b030503004a6110036541d41d1101003403003070035141c6560340c40c00308003040e1620001c2d42d4854417250300c0c0c40381c011f0a054250003040540d03800107100740002c000005486800c0110000d0070014050380110050282d9002850b1030408405694001604000c0f60038040c1a03000490f03001c400c0000c0409901c050040c0e900c60b02d04500d0700400e180c00f05003900d4010ba042040740c03e50003004c269840046200190a6800002003072006003000301c0c04c0d4107a144017401c094601682c4004107000c944c025400920640c01040700c00852030414450040105040c0d0302250034010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 792547293 1250 792546043 792546067
    0x2190c1101050708090d2915120102120403031b051e130f060302031918120507140a0c06020d050306010507111f120903050315010203122a 61
    0x10355105994140032001c00e0490400076050708454110358003030305d001c82402492618450907a5111602a8400360540501c0041c9203912482840781810b00d0399405440f0044042c0285030210411040095400304018a54640e201303a00034007c61280d41c0c0010407140701c4070180790360340c2250b000404100c0c0800c841c1c0307035001086902c490f201c01036645040e03840b040d0b8030442131410b440d0380c0040c01211520700d00141007900740d8050340c81400c1403508100840000303a900401c551207000a20305485000c08240702141100e90301020300f014508000d80b402225072299800e1200041011540d640b00e058110304200404010400405050004140d040d2201c58054443e000041c58141009408260081404a100ba2065a095002d00030301c0b10803800e50a681041664010480082036404080c01900c081600c034040d040b83d056640d00b411034580700b4410381c0c00103502928074114031050200c00b420b0044148084c1c0181a00d187c80ba81d1100c00f5107410047c0440d044042500c20f400303002111000d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 792548543 1250 792547293 792547313
    0x31612050a050d15050a0e0906060f24090402070c081902010c03081f0b030a0606090f0b090a030501050f0901050c0a08010b03040218010b0913020a090303050c100f02190c 75
    0x10a8100f400305180100c00107544103084503510595000400202c000340d505c0c84e16000038043c980b1b4a0948256a07522002d100508505980c81c94010007080c0502685210306492800e0080c540d113070080c5401500300c000f40a98000e100c0c1a41e09000d014030801c2644070400004a10180340d182c1c044090b0b1041d000600301010184015090100001c002046100780d60080c00d0b400c0036410717004c903500f07440b10454071154104443c10318103140303400d50100b8140e00402481045a1016100b42c0f07240f400d040c09803019030000d0500c02d070010032403440400000c0f001e0064600c5030401403684481403810600c0203081d10006800440400020401104080c0c0c1c880405815a860021050b41d20f440d58400b007001020101e810060900d171400c008101080401c0003032515040031110514000101c2880c24200c3c0b1500c02c440c40801d000c074000300001313401032000e000d095801d1002e803910381489a010303105a9104002c03000da280d83c00256110913040313883e400c0351110403d14103c40d00c00410707502c1c2076500e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 792549793 1250 792548543 792548557
    0x5010302010e1c02150a0f02061b090d1a04050d030e100b010e0d050f10060b0307030e07031704180c080a0506033a080f040201031805031612050a05 65
    0xd00c6142c03d20460ba9142080804007aa8068841241800300b90108500d03a0042c108107030000c0c840c0e04082c104244000b0311280115070301819014403440750907910340c4e035500540500f40c00c01c0350072034024081a10340c001100341d9400745808003907500e01841c100d410062103461440516103004480b0f0074040700001d00300c60309110b4040000d0220416001600d0b215000349401d5030040b1405440d100304000414000f0662454008482030100484006030070340d41640201c0c1590b810904c0084e043c9486600501e0881882d50141e5541035102d440d201d400030751448080010890024040001c40e022407640100701960b0724041003c10091030009001c01805480311619903250004500242d8040c030429800c880031010040c0c00013a4040707081c1200001d200c5114846688045034096140039014003441610180341125141d61190b00560091403031030303513625a01d500300900c000000c0c0108002c2585866100e120804424185000c1c0d0b9200c003207500010811000740801020207400500703484c46 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 792551043 1250 792549793 792549799
    0x603050703111303030813050c15040807060203031f050f010806060408030406021c0c0302122d1c02041409060d020303030103150e0c010f0503100e07021e0105010302010e 75
    0x66840d8510100d0181958100d07100304a000050f03181c0f280c40b030003244141103038425201c001d80c6646a02006480000c91900030340103400040b800000c2c0e02d85025408808501c942c406400e160319010368074580380c1103030440009640000305010b00124494070100c4400400f003c2400c0c024184004204a40e01546403d4184603511001c18190366404059801500c11001101c3d116a91540000d41d00d090034802822101c07841c101c40b2000d03a01c0703441c501c044e00740c05070002c00d0281011100003c095005a40b14131714101750841101003e05e9150b0314031240d00c13001d6050341d183d011090181d00700340c02e0301d2030355034840d88104410071800c1c010142c681c558680843c0d84c40c200e036640e4408030700c05812052000b981800008008400c0000f9541c107982440c68003402088609048200359a840a10340c1c3d0b40313404104441020001244240020759002107441055076910b035840003040b125a43c1130303078944c015802c500000c20345042c0b00d61880401c0d028034002802154910380000e40300030102505280 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 792552293 1250 792551043 792551051
    0x3030313060b0f150717090f060706020c0102040e040210080907090c020c0a0306090b15060412050109050708030a02150f04060b0d0c031a060d020108061c0b0a0204150c08040603 78
    0x3a269075a68803d8080c040041d0440304d2898071001c00d09101d070300c40380e0200c60f048855004600c0100c80d440980d0303000000a0140c501001e81c0400300b04072a006024101e500d55000c010141c0140c00a002500061851451118050410f8410002c000e924224180304200c0000d08014141900060313a40454065080008854000c04005c030b080c034001011407600945800c00000c01c010705603000660141c00340700759a01944912002d50980d03105260000d5201d0003d000a000e40d4145036462200c00307100d1800001c0d42e81207952880d003414040c0d0b02007a00b40c2c0010941040158040c8101480070302440704142161602040d011120710000e40040c080079540c04448115450ba03518081c41203801000c813045c0141d90386130104020440341070180283c00d03100702213152070410394a4413881540c16100c1010b42d035a05014055403850510400130440304010401010404038942c441c02030b1415200981c0c1e86091010078281c00300c01d1005842000b02c40c0400d40301140c800402d4402342e400919000c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 792553543 1250 792552293 792552311
    0x2203090905070908060c0a0207051e010f0306090e0106140d0309121704080f0705060306090a1a060f0d05070c020a0909060219120b060f0d1d030307080103050c0303031306 75
    0x29a80002c1e44c2008906216410520099245540240140444c280c0c00c8401403901d5005102c45135492000318a01591030000890044d8010954650040058a800141c940c1d859400c0d405543c100740110f01103964840c0c00744a400d6840c1011401c90030280d5580300e40300041c0da8004c0c880c0c1107074400c40f5041d2140918010403c04c00b0752084401c07854a0110340e0302c0b00e03100c0d02825101d64a48980358002c0c420340c02c0016060034041e0a0305e208450040c00c0f0300499481c402a40017801030a0000c54003058030309003080080d6640b82c040e0982d40040b2081d15140c800340403a0b2001c03190f01412050a01010341d00480042e5a01c007020410b031040800c0201e03001060b0300d00078019008400781904a02501c1c422030078442c1d4040400c3c01721140034207091054031010b1043c040184100e8031010700c241c5040090410440003508200020003035464210701c1404030440c22821030f00192200e400050045004206001040202c0c49041c032044000d10700e541040c4401142260110350010b05241e2121019 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 792554793 1250 792553543 792553547
    0xc1a060303040b0f191e03060321090b030702011a0906150a0507020418060c0305090304151701030b0108070b040b12150d26030408070f0f06060305010203220309090507 74
    0x344501d0b05d00c15510302100700826002414020010001408405400f02d2030f559a07807080c003c440459420581e00780303050700c00c500d80d108244200c44000b01403041212000659148400055101c0c0c0c02c00d900006130080401109208800d400700c0d540e10845050081c89240e41e03444003030707682c008810368003a03030784548111094a40340030321341010754401d00e0488020800d804984940c200c5c1c0c0c0c403c0e1810413102242e0305c0241c1c02c6440c1542c06086545c414002880bc003d600140c007140c9170021309091100e040e0b4101074461070702c0c00340c0007101c808800800410022508002a001800000c04200e0070942080180401801040281942c405103a00480e10380060078940c82007030b40300a0f2002000b40c200d03043c05040c00168a40c3d80051100c00d00480d0800c00d0603200f501d01845c1d019101c0e034903280d8682c880b202c540045013419900611103100f00d00c0092080d1158100640c45031002688902d400c6090000d00445120366048043e190b03980a00042d901620340b900381c505514000400c2d032509581 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 792556043 1250 792554793 792554797
    0xd021020030711191707052125050c0604031707110d060902010206090c0a030b04060b0907020703031403010e040219120c030b01060207060804060b1309030c1a060303040b0f 76
    0x8492075003d14150094610000e04c2d1072008240511000c4407105000042c07451a1701c1000c0000e0000c1c0c01165910b4810741c4032540c02c0b150441c100850382d0420000c0741c4003030301e84030844488160308a800b00c48141084414030400c7e0300080210343c080e040900e151a00050000d0f0b140d500030380b001c40061840100500ca081c054011603005d0000410840d131447c201d002030009000030307400740c0709540014200145c001450030080801030014800185540d507001d9089030054011581d540e210412030480d911a410120f02c1001c07268020b101031460f506020b80b62020803102c1003918501040107200c0303600141801038104d641612404415032003006500780801d8160010303550102d0b03500209050080c0c80720305d401500c0c0952040d04a81c2d0b038030602640d40300e03000d10070b40011608200000d0081402075104100c4500082c150303810329002059000b0860b1007000080300452007000143d428007040369140355007940344180c0901c60303081000000e42d680c045c602c140146400001680742d961101d0b901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 792557293 1250 792556043 792556067
    0x210c1009020d120203130b130501031d0f071a0306010e10030605032a0915011808070f140108010b19120906090314030f0103030e031606020d0210200307 67
    0x782c038420402c00b040c0d000b5101e50000410191ba42c14410002c141405075100b29065982d8030032801e1411442c010040d00603000d00c44941c80c048c00b41442d80c40c00900144800009101e0800251006a046c0154103201810440031030031880c0040c4100301440c1d8208114000a590403180b400c680001e12500300d025000c9500401c3c1c250103210720100c130440c10f044c0c2416080306801c0228445800d50b2050001204003124901c20011050402c1c10300c41d4050071f40028000804d50032144401e846020312440d0001940c0062403a03901e60307100b003251025100400d078100009180101042d45004020b04c01800349081400059485603020120140030310512176601d442500c003031120443c0b90410340001c043c4901e0507804108001c0c1d41d1031b0301c0c1c151001200e210f8241c0200c03100050f400c1d9142242c007d0300742603980b034041c4141c2903803005400559080d040144950b6000340003001440d80c00900f84040c2968810540341080590340015029011460410a801c0000381c1c4982da842c00407038030707502c2001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 792558543 1250 792557293 792557303
    0x2030c070e0402031c05191103120c0f04060f03050a0e0a141914063301030204050d0c150504050a0b0c03090d05031207140313050f03040602210c1009020d 68
    0x4000304517441e800002038004014145180d1006400a079825503000c5000c1030f581c0d005410030485080848603c0f10500d40081c2e0718007042c0d0401811605104059000c0d03040300d4007103044110500049a03150003090360104100b03100340300800d09205560355030306480b04020b10b003204003000940d11420410150061340c2d440643d5500c00203242c1414101d88400c0000b40415004500000380001486100b00071007621a000c210241c20040798040320090f0107014690406800300700025182e5500050488902e0007454001c10461500550549007541903d601062180a0101300b010b5580d0b603624a00f2200c4940843d942d80d41d0800c0c00f01d0562240c02d610684c13003004502144184800000a000603060f00b990032041501c82c11016580f501e0000c0841289040c100001500e2080d41e400b1b02d021248500c0842e070309004102503460039070b040b640006005910108034601c118444540d0103c546c1202404240b03445051109644c46200b030098501c0d010761105070600440d202d200b002c03600279400c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 792559793 1250 792558543 792558583
    0x103150315050c120a0b0406180f0f0c05181503040c0303020d1805010c110a1509052707020307061109041514040c09050d11010f02030c070e040203 65
    0x1034903121003007480c08103034115040e25040019262040703050403030b04191400804881e6583c1c4480341900641595101c4503009515407000003812641008160401081c0c58804500c1c04c2c880341a00d8122900072200d8400103007000d080c01011a00301003102e038441c806903207601ca881c1804005c0380e07000b003003a424800365290000400c42800f0350000554141c074466826104000f034015000c0f2204a400e02c20400005040001000598051035424020038480c40760140d480f0224030004021080690104036203400a803403520340158054600380c083c19080328010503d00280018100595520a03902d201d142c0e0400841d0209000301b0954451540c03101092103c541141850104c2d40c03c5100d4040c021070074021014140884403000b10103071030701d000c03150f0b0b1110418010403001c3c00201c0341040501001144c045255150040d00d03220403800759400e0b55003020340740c00040a403401c4c485c401c404c6410520180c040801e02007400310440344200c100f003e607a1601e00000b070810005008600c548540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 792561043 1250 792559793 792559799
    0x1a19140d051e0c03150601050405101b080d0e060f01050409032c09010e0702120919081501050901080a080703050c06130b09010c020622050604030c0c090b060a0806010315 75
    0x80010b036040540c00071383c241d544c5099815901c5211400984815001c0740041c0028001818200704480d12080d66282203c118041d0382041101142c80d60019501e0b4040025050040700040c00f43d407000707004140091400345403540d0340000c3c48106024062085031101c0900c81818800c0f05031042419030104080b01c00ea00030702d10801c07110a5105124003c45200d80006050242d10441512800164000d00016980102e600005034086101c19510400c000d020404143c10410454003405400d001001c0706680076140543c91135050340801d03c075101a000501080c2e80105403540043d502108643c0c54040394a4180e8050107000000c00040c420340041000c591030718001c800101e400380401212a07114005614240c6041d11507900142c3d1207900800c00c1c514010204030803100560700d61b52088100c03591070300d007010019581a000600340407404d0302030242e9209d0b007500804890344104400319803840803903140d0189102e403400f8880b03036500040035640240c1050100b6055071640d081441c1d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 792562293 1250 792561043 792561103
    0xa09020d05070c0b070f022107060e0f0d030e0c040e011a06180906060717190915030c0e0301020c07090b0f010801030f030c061a19140d05 61
    0x3140341044406800c140c049002c080c000c60488210f0380e000711154106503903119080e03030000400307102c5100314441c00380306080c10b522201400d02d81d802d03001701690351100c42d4100042a554805990f0f04d05030808607080c100f1510000303101041c0c0015040c041221101c12000d0780c02c0c4480d840d5090780103420190151050401903010184103507890340c910903101d030540b06005850003220f00716880110421003403099446d2451800d50b100600400301480d0101954410507050030703110304119058400b01d82038411400112900140d403015140a02403e0701e4200400c550580294160341071640ea84100d02845201d030072003120000002d002995120700d00d54100741c1e0355403113104200030b881c80c00d80c1e20a86850910079000c019501659404c03590390958541001d09140c11030114203029001802c00e0005685018030032514000602e454010b1680c50140704041420030060324401c45040c100f8050405001901515198191160b000407425407501c2f62400e10080d00d038400c6550320440702100c20f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 792563543 1250 792562293 792562297
    0x30209030d0c060c0201061a0c01060302040c020106080601060e0a1818034a06070605040c0501140c10020c0304171b0d0b04113007140916030b0a0902 66
    0x2030300c40c00d420005082c074621300302d089a8080c006d0501183d140784141100400c50800b8000841e00f1400008285580e5400141203851a2041d80c0150751a42420440030701b0a014035401085d07a0708007491092100400684040098001c1c0d102c1c5114892000c00c02800550017600c042440c01d041e1801c1c03101c0c5041c0680b00d100b4000f120f0500c5a004103042c445a550301d200e003412000c8030000b039840650f80c40c5441102c1c2142c12035068100d0414000d00001c58843e0299030301440c0103061181c901814413000420085859420f10070302c00342004070480d07000d00042d9403260306100020040c1c4942d000c0d9181429485154802d0014040a440f0440841c402060307030a4844150300c5c2000d5500448000d0025146c44c0c075101900381912100050b012a003140c0b01124901d10050041d050035400c0040e003003460340c1e001d0007c02520301180503900c890300700300300c0c3c3d9001d0a1000c0d0b529002c6400c1e180001c84c500070080220704020050840c00705031034065000408140b40c014845441945c82d038081d030b0025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 792564793 1250 792563543 792563567
    0xd0b03100e060901060602070b0c011e0e06330a12110a050a0b041203050d0204031208090325170f1c090c050f0307081903031b08070f030209030d 64
    0x39010b42070116100c3d42e414414042102d0194028140709403410340c2c0c034040b9401c18008014903540304c000f00c0e5841060031049680c06141004e00003203006880711100d15207a001415103a500d40005454020070411400d15039203202d00030844811004000b010408481c940d034006031086030107a49010821114036203402003100281c4000d0105071340d0b1800c10100d070560b80706080b5140070420080c4407142480000444490082c200380d13180c1590b50a01074200c1e8025427081c2c1d641c0d0591211a5019070340302c00850382006c1550021414400e42e1244089000c40803000c007801c001204a000f010414440c4141c4441802d242850361642c4050f546030141d5400900441004448032086001e456001c0c8580310f0b81d140c12110780c80e80d650401d024402030b50402a0080d903d80b20f10200055100340030445805088103800703607652200110325001d4152458124070640311024180480c861981c400f4440b94002114038103007007000030410040d070003440f03010001070f050f000b01c1504400c040c1e0440043c0c910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 792566043 1250 792564793 792564821
    0x4030203010510031214040308040f0e0a1e0c1e02010501080f0a05120705030d0903030605240703181502150a051b0c030c0313090b06030f0a020d0b0310 67
    0x65942c0e60340d01d1120351114000280103030105040c501c1c41606c124400008400c000815070b15040d10707502e80c11081e0304135910191050602c0711040c4400002036024940000002c3d4003441848000600c8141d1100c6901103140072039900c100f60b0059603c10b950541c0c0b41992428005d907074080c4100c000b40681070900482c0d286202e40c410074003e17070400003911010aa040340c00741c018150100441400790303005101c1078855100602005440e0f02c00c0e0711580b09124031a840011b18246403200340b0080d0301c07848060100c42003005184204181d640811540c00a606140c001c030a20305100d610740f10078003140c01000f260b561001c203c1106540020344141c090182c1c0160300c81d69a03d0078044802c0d80d00c200ca40c0c0964107155015134098126030b0000e1712080305081d0540e070414242d0001c4903d50341181e543e2442c01c1c20105070401c814045442400960441583d04070319514100d00840b06d6410064807490031650b00141d401106810761b808210031450080071b80d45a58041c215070300184c91035850f0391070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 792567293 1250 792566043 792566051
    0x204030309050117010306051e09010b0906060c06011202060c0a051005180d11010e16031e0206040608061f0c020108010602061b0f1306050d240506030621030403020301 74
    0x241035801064984c652220180004169a003035555a001030000a440415950811361410605030001e001c4503100c1c40f45280001214142071302000540040580454000e140070045180384c101c000c5031850540f034801c01c4805c03030b40e489071020442d80d101c1e00e40f140d038640c01a001e40d5000c10002140030090005088403d000d01c0e01c074180c2c809201c2000d00070a0503070303601801d00ca100b580d008071400481d039207030070000207000000d9400d03d90402c41e01ca044982c0219104030305108200c04180c24440b071812117012428003008940c0412564450f5025010170320208a000176103a070740e0341c0e414550300840603105010b0142c6600018000244c0d1807001ca02043c001d10011075a1440003981c184074514548081000a9010f9040605030740058054082c800007000b040c1840503414207094020000e640e02c1d980d58156a825503030032903952032000c860b100742281c404107032942d0006100003600c60480b2019076075100c020018143e11800600509107000400c800380d4a040044082c4c41100d0096000b40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 792568543 1250 792567293 792567299
    0xc0c01090803091005240d060c110709060b030720120711030c031b01030603120206041a07050417012301050319050d080402121005150603071409010c02040f0204030309 74
    0x4000c0d500c08842d80381908540c81c1c000300020005500306d02540c10060074030108143c3c152600c81c180c071709060301c441c0801c200281d05240703000104039075401045c6034101007110b1404e2086154140c800900400200301000300320050140006142440c119110780490b0549241c0744450b807100c0d00701d0901a83c0d49a00c60220098500340815010106040240505402d40019040c8400500b01480c110304050b503961021000a208201d420b203510682d40092000d894103240038202640380990313010800342c01030144000035410505035002e07102040d00185032202d075860300c540100060b0031000307003c003050550005070001c4114498141c032415000e440801401c1c0140e0281300e40d9001d002041540503d80401c445441104132980180c40180708440c604051002d2a243c00c0c034031054400e0580e6600706120300d0368a100400e070003002080d0f03605410b6203446e080240018026016050f4030807000224540d10b81e204482e2030721030580c020803c00245090104800c0250400d000460204064007008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 792569793 1250 792568543 792568573
    0x270f0c01080912041d090a11040203150603010e0a1b080103023d0e060406020304051c02090c03060306160c03030e10020f0702091509011503020d2414010c06050c0c0109080309 77
    0x24003601d4001c941c280c4a80032344030901001b5031000345160b010016024480c00c903507807000d005500a1802580141107400c1121000302250109132440307010b1040300c0080414660850385139070441e07404450404401084140c00a00d02240c04d00901581c400e400b103641d4484100f05000704d210101d0340e1a03c9200015400b440171910480c020003002d41c0c0148800c00151030142c1c4120718660040080014902640d07020902c101000d46004a910390040708111702410200501d5078044001c0724034035103010b0403110103400c01c960108003a04168480a00d411400c0007000010300000c000401159604c89407034403110309800c0500100d1040341180d01141e520101e44c3c0c4803030b0f481b070001000c807141039280603240402d11f460144548141038080c010743c00d40c207415102d2000e02814807060300746c080c02c00341c0c00c6080c00c1e0000d07001214600260154010a42d901024003a000c3d54001070014464440351a041700d94002c035246142550f0a180f041030030803074803401850150784241c007107030900002c000d62 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 792571043 1250 792569793 792569803
    0x41b0e060309191a090d080603030a05041824061103181e03060a0207050c0103140a0f061518080319050a0314270f0c01080912041d09 59
    0x440040307034803040f94804a82904010124242c0c860319841e000326815034464443d9180c21600c00c02103800058200b4100c0d03800c0f40c40300703502440c11009036180c03207022900030b40a0700450044191140216503131907480421365004904415140108800c21810310b040d65104c0c0080703016040002e0880c682180742c502002003501d0300810007802100350315400006000c0c204550010355045001c07000c8100741e40340c4090200c20700078030041c0700143e070341e200c80e00f0010300e480da140c1030304d904040c903090001d034016030703003001080d0894400388011400c0104604040c1c040d140310740003030703c4c000d40c261040e008103508102c014010796003040420b0940765840d034203245c032400390b4010520100114000031600910a400a000700c031094140020350705a04e80c03608034441c1b42200d01c0c40c06101d20302c0d9840f4509900c1d60400c1084803000009120382503502901c20b0f1030b20700e440c40482c14442042d0109102450501c41c0900751040f00c0085601c40307603208003004800104800800a807080007010440040d00402c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 792572293 1250 792571043 792571051
    0x1e06141306051c02130c050d0b0d0c0b0306180a0b0108090a050a03080a1d01090201020f0a03172203030507030b06042402100608070503072103030e0c041b0e0603 71
    0x1070f400c0d95000c4401c8034082e602c0c02d86000c0b43c1c803198018070001d043c5128450701640d8070300ea1383d5031511030503040c4c8500c00711400114024400e100d20214100001c0b0605005005d88803000f491940b40c1d1074600100e040f0010656162460f49405820011144060760206d811584261b035144100d486084074107803250300906001d42260170503501d9030f022a0040700f035240c005001c9a000501806c8030000440e404160b486003001503516200b441c02550780c1040710007840c1800401811000c069070360301805030a540c90f101243c4001b90f800041009042d410b140f0003c000c40c81c0d605000072039625000700203103803c56070540403d10f0001d048885041001c213884c2a00c14003441e04001340c03000c610001c0c100300c51a42c0302085204642d66840c0d240c80c5805044002c100300d0004001250800c0c003010b04180150708403002000089807041035040410303c0c410101901800c0001d2644c2c03021911505000c60006602d40040c1000d15030441c41c9c080d0051141c07407d981303540e1218a040c55000b007151b00d03c4160b03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 792573543 1250 792572293 792572299
    0xd030302070b060619030e0309040c08090714030d0c05010b04050414150402062505250812040e1003061406030105060f011d0d17090316050105030a1e0614130605 71
    0x10121228000d81c044140c92041c0c0c7c007180d080c1150540003d0a0355032740155000002c8c0040240210700c5c0003044490060a21215026115038400b00403990301c5849078408010840c44034404001e00000703511400700c01c40050b000b4420303480e25081214454122907241d05944c0305801040000591180f5014040c55008221f1854120a0291182034444200aa0690500802c6244000354007000b00003000d0b0391050b442034001d10340610301380b01d039283d0764060b4525403c002e00030007030008a40d04560650b04c42101e40b044c0707521000b03980b5200003040d42004140e540307011260714a1901c00e1004900c00d032401c600034000c07580d465050084904410494501007158140741024403051480f40101200f00944003440981c03083c0c40e0700c95003641c6030002071054500001d20303981c80c2c14148215181010b800b5000c50801d81b07000c1c0000e045100040c1034144541c0d030759040d46120120041c442140d064020703c10300c04a1b844042418000032a610360921030044819401080c81c81405154101e642c02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 792574793 1250 792573543 792573577
    0x2203031209170d021b1b0909060601030c0215010803040905011508060f0402120a09020a0617040b060103060b0711131811030f03031003050d140d0b0f0d030302070b0606 74
    0xb41d400040d0b03580220b0400c041c1c160702403014a00425000b001d0341075404145d4010710031000f00b01003044003100020300b06070240d21443d0410000c007a001689980101003840c000410b20720214049042070780003000358a180e02e52000000da0550004054016500034600410280e41e036102141c50034114650203102003003440001589601d0990510001e03808003030005440c040c10f001c035982e035404045804101e89580d07100404198106540d40d1000360185051084581c5003003011690071501c0100000d02e00f1101900141899110b03400c03110040c9407620030030b038842c0380740c0c80c0001b21070038600c0b40140510b401c0441d6a01c80da0b29070245505c000c011a1017101d03264072070b80312004412203071741c82c0035018826074184100c0725000300011481000e0304611403082c0c40c110305e00750f403c0100e804086010804003160f209011103202c4100e400605801500040200307624000c07807840c40000c1750240d8001e40c286141d105054040d00140003251040440140682d91041000b01d280103010164046c08a8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 792576043 1250 792574793 792574823
    0x5011109010e10050d110304140109020d15060b0301090203041104061d04020303041d0906010603110307180f06020309280302190b03070306061706010e010f03022203031209 76
    0x3c08101c502c4004038520b0100c2c41c0c41c001c0340d02c550988885040401c2c2c2807400000b008144400002c100000401c3c04000b07118680c00d50300010f04201c240500503000100700240c5209204441c0e00c402e0080180c41c10503912036039107003103690094101b11810f40d92998a44041ca0003440c0370711130321041d01c03a04040d601e10310600b8450001c3c0d802c40103000301e81601c0208030104240c0b00407220407086000e2200e03861100d1800507015402c219041c0c2c040001e140c1803264032140e44503c502525848245442c10f0300c07500151072a40107901c01943c1c044800c40c3c20381c80000c942c095010005140313804085c1c0b01400c0b06001d0700d41d150903c2d821405140e0101e40341c10028001403820703041c103c0342c0d850880341d00300f070b01038640502415550058400e80007090b9104400c00646401a089820b001010580614185031420018048904401c038035410800d42454441195001e0b5068810500f005040011030100b2800000d0300302040d4042640800e12101d907030704c81a00940030342540c1980c00308403003095482d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 792577293 1250 792576043 792576049
    0x14010e011401090903030b04091212020406120c05190206100b07021f020a061b1d0d0204110c15010806010512030d0207020a032f1c1119060c05011109010e 68
    0x4040e84200c01b05900d5002a511680e130300d000303410089000d200d0300c8051003141c44014000c866010300c03078044076006000411559030060094001580c01c90b4021522210001d0221590701ca88541c1002050410140c0d01e42290300184440c4140d0300d0b400c0c07010256454501251040c040d400009501951304441c0d09015860018141c410000c1c85c011114926078558920050341c1070b100c8003080c01001c015003a003040e03912469079500d008107030011800400d01ca60220740035101015010340039175141d0840c40700b5060081c2c1101d20785480401a201520362100c07004080b1403007880b4030140d0344a000b00114040c0b0740300e07120b070781d00082c851300841c54012785480410207900241c0d0241e901a0360000004040b440d0030206080e04010b06040466180340300c07500d5803441c0326007031085000d07500c041903502c0044d80c4503c02e129019003021040c0d10382400c0900103628030b16540381040e80102c89070000a0710540099201e007a00b4400c00c0244080060110007500c3d600400c1d10090000d0554883c80c42d13241 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 792578543 1250 792577293 792577301
    0x31101031a0616290f1501080705160b1905070c200a060201200f040608100504380f010e15040807140604120308150a0314010e01140109 60
    0x200c00381401850111080d211251090808032804030084403450b85400c0070094906865444010050760302c1172801c101b0840080034144a510340d06000c500808900400c0c00340059450b1300000000090030114145803481c2c0d416416149400c06070b002071401ca011711818002c1c0d0303105603041c2e615000128469120300d44080c00000507641c1e50403258562522617296402c48030060b015540001c105072942a100340070013100c0070b000d0b002c104014481c0355501d04e0200c04545c101c1e080361a00020b540c49a2200402500181e800254081e00c2c14413403040c20460000c0d410343c440803c1820489219020003440e00518003400d2103070740901d08500007511903015440040000c14007a0010301c0e0222000e400c0f00080c0e00c10342001c0101e500480c0c0c200046010603845449143c0700f941e141c2e083c40c0c90300c1107041c1343d06004500141400721150014a080003400c2600002180041840c0e460340d41d02c1c1003c510f12000407100125550070b10011713020110050241c400000c604d01c000011a80ca80000a0010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 792579793 1250 792578543 792578557
    0x203010501080f220f05061e0106030b032d060718030212010e070e06190e0604050405030c0d0512011e0e06181608010608010609031203020c0604030306031101031a06 73
    0x801e5408a082552080c0040641c840d00c201c00c8445c84000905010346001001013804c0b450a0039907140c3e45000288017803050440e41241408119040242c0c0040e00b04210820422011900c000110320341c040c4004c00007800d2403e24041c0d41d0a61101e05d400c88010842c00500e2110030071a600c00c00050800094a800b20b40e48103000085004500040340e0420071141e00c1291280645420300070145040c55040503020704104101407002e14041c008c030383d414801451588100d075141d00040030300c00188101c1d42004410010340c2c6142d00401070207840350700002101c4469180f6080085403010001d00a022142007041c0208612442d218444e941410014509604140b0140d064140400044811801b41c030f0700601103500d4400040c4000d0030480c050b070102d010400f009004020894010714060103980c0c1103220103044002e054003c1e000391250703011340e00643c0b080c00104400e055141c2e1104040d00d02ca4640c00512541790f2b001103040e144070541034102601002c80000c0549080e100130215 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 792581043 1250 792579793 792579811
    0x30f03090b070f0c0506070506060f01021f05090d210b0a0518010503010c050406200307080d0c0e09060105090111010e010c0203030f07030513020118080111120a0203010501080f 78
    0xa256141c000d41c2005030440e1000b2036810595450355000c1212010000016220903510b4030300345212501c60b55540c41000c1c103400c1c0200400c8080c169140d00c00c3c0301e030703034100349e00c00a80511010f41414000000c120888000c0c00500885d69440009882103494141124400030440080001c10150500400361002d03059401a41d002001545444014a1040c4060007405e000c1c469031410003411300303403503081c035507481005020001401980e07008600c0f509000c0040c85441000314011504502d5403142c500d029007100301c01700d01c001c0044400d812802da111a5030303507081c072480054010310031100410f51756940880c03000d0004860b02e51040c41404c410303102010000c15400d10070b0342101d0840b101f1300f0072280141c200004001e50000d1481807240c100a041c5820001e40c0740850030741d0079560380c5420003410041a00320018a00503001c5204008d855260f0082140c42c48003406c940080e0320075247d01450728510000528148154800d481c1210410384450944d03549d00b0b21348809680c2e0040540384 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 792582293 1250 792581043 792581057
    0x30601210903030b06030405031c0905013204051b010207030b0a200a141b01141602070803030601031104031e02042703050901022b090608010f030f03 66
    0x1001410082680c60148a0040d001030040014107005050f5640c02c140e0710b028810030000d00000510000c21113000b414500006c2c46220a04983c090140c81c2c09030780034000750700703200c210b0071000c80c280b002442420301d195020442001f0a500300d8509002254091b025800c018151928186130319a9443d28110501c1641d04643c1c5a0740c2d00c5600884c141d82c00d260701c650710f445034451645506100103001180c00e0406003404900e1000501c00c003402c40b20010007501c0460a0507114603850003403074600321031030024800a00c40ba516450011400c0717403095410300c95042514441c070b0000ca81d030020380b0501c0000e9840c580c3e0f1040150060441c640960030301080400000011866641c2130401140d00416074594114481c01003200381c92107201440081c2108014607104004403456841d000c070340c0b41c20700607118184400140e0500c1e00900e400601e10707501d03040c561200024480d4105a8504c03070744820304159100e00302103600710300c240030700314200081c210b003407021801010078403641c0f43c400c6c03030220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 792583543 1250 792582293 792582317
    0xb010e011e05091e010308032e180216050a171204111206070f0f0f0f0804060f060b121302060f1e040923150616120f0908060601080c030601 62
    0x841c0c00a0241e00c1512494008018066110201d04148440388900502c0107000000c55501c00b103034074512b104005101c0000d000c42079011072031b41c0581d050301c40b10a009502c240762078107005459284466085481d1100082030540d026010016243d8103c07055041070120703512035444400003448040400e034400c42240c100380952208004030303882200d450303403a624510300c4030b507001d003e50318126403050a0250864180c0754255110119070101205842c100d000784c0c60301d0500100900c0303850950b0548030700b0250007203040b0a400d00244030121403400d200780c40d9518400c2036008060b400c3c1c0000e50010080140e8000071304100c4c094014181e820001d0080e8890b161054a295803055009040e5246c0b01c0ca40960741407081c0d002c0b07044030800c0d151091551301c3c02032801c000b401840c3c18880d12030400460f001049011030032801041c95030000b28100003035000e81001d450f0316082643c1d000000e001600c08258420302254190080406031071305011a07d03074440020b0031750001041c0d00d04001d4811011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 792584793 1250 792583543 792583591
    0x3060e0f1c1103041a0702040915060303090b0901090618150806030609060903270315090d0c020d200d081b0105010f05010503040804030804030b010e011e0509 70
    0x4030540c001d40c140c0c102024074807080241c0b000c03821456103031583d0020300c000c1004204050161515000b69000c15035921820310028000340303415078001d0004e140c1813114003640d48071a40400c003580c1c001d840c0e007408544c3d60480c0a5085c4a500c141a002601e00c040070011603000d003c010200010410f45011000d07202d560841ca590108510b4000203851141440418101401215000324000001d42114070b0460b4200b81e4903c6199100c1d008180f845070620700352407428550180900e002025512a100c40c11903036000c103581544d00404501980c02018446c1d40a40d03403542c0c034241d01500d240000200b6440308460303411400c458544c1800c08020a90303050381c480a07c40482c0344540d40c910349889403031200c2c081c50211949a01e01030381c9408014480b40690401c408100e030b0b82440e03d5541c0769520315015070203001d80d0744001c008041c0801c3c04000c01103102d1265040c0c0f5854081035140b60390301e550314421b55a8952900c031244032486401e01c5103003001d56045078040c07091500a056020f1540366 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 792586043 1250 792584793 792584803
    0x11241305010f091211071401050c15010819170f0403141c090503030306040c0912050309150f07060c021c03140708190b01031d15010501050c0703060e0f 67
    0x4081d43d070b218950b0420140c1000d0b0840e6030070603e0302a129000b5481015510040340c02006100c1707641c2094802260b10a8048a0302040940e09450990480020440c840c1500713000d881d09034000c21416180401184c9207040c819500074802135003007040e142ca025410307400071820380b00010701080040041551846e41061003640c89008081c50000184041c501e0300c01d010300b9904112045d8020001c0d40e07000070649800072012140011140070b600b03020b480c110f034298401004180d2104150040c841c0c0400a000203140035030311001c01100d040e03541d100350f1003981e6241d10340c20010300030138000c292240e104803d412828011501801c6000b04400503075042002d4100000741c40e44a07082000422940c0743d90030a58504102c038080c1482d011003540c08050b1184001c0013036031180503003403980c03080d0004800d141da02210310001d1031030003282940b0380110180c51414208004000500e42d4840d030103c03103840e1074500191888034259601c450150846010000451080002d1007020348030030300c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 792587293 1250 792586043 792586061
    0x804140303370221090102041a25032d090311031005130c15020a02100212031003030f0809030f09030304050a0e060307092f0d0504030206071124130501 67
    0x134500d0304000c4003604028010001840c020590340144400c100510484400344000407590f20780584800400d86908418203141c0e8001c40206923103081c0005142d00604820411520702100b4002143d8460b04a441205c03140b080c14005040403404201240707407500300c03950881c0001d0550307150703562150552064603410b46104180d040168070b41d9042100c0c9400d1301004100807081142e4540c040c1d00003070740b504081000603020f1001c0a041041c103d2091003031401c5640c5002d4600d403203003045660004031001500003140440d00c108070700c3c10100e0041da000d51150150790002c41c40c0c08bd040c0850070441c0c01080d071340c0b60140310500c800f0a15a0fa45156800a08245034114806d403425000705407800e03072580d10440e4400c0c40c000e0100e28507144490100d00704800461020000401811800d02520511104c505101c0c500710a100416a02040715400f621036582c900f80e02ea030039280c00c50b49400e4807a0404050300c0c0c0b5401c0c5001d10200c042e120f241d000782070003180565501d540d11510b00b0750f09445 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 792588543 1250 792587293 792587317
    0x60519030b1f23040810050108060a0b061e0a080f1003171201030609050c190504090c0315090204150b0d0e120f120106050408060f0c0d0c08041403033702 68
    0x3040a200c102c800b0441c007403006c4551401405154541000b041d01c410020742001d90043e2605001512a100c1404032107250080c00c1100b031016241c8a8500001d4002014080004103220042554030000c8141240140b01e000341600103a032443e43c94000408134441c00a01860090110078450000141d102d8005c40c0606008905659240b41507400d103984a2811031059001400c2c43c9042000807226070705842041c1c4000600c620141001803842c0725030383c00102039408080500c5010100c50300b240c6221442a1000d201c007031030072a800d600c0103295004000b0b089209202c4205c0c5640690084048000840191100b2081010410229501991001ea281c804c0040c0005000c000352000b240101a03a00c2e21904140c1881c00c52a15054090502402990b40001043c04200c5100c02c484054401080401c0078018800c00545003203011501500e440150640d1f000b83d041001c000c07030348904110002c01e001c07200900304041000a904010005030314452010346000402c500c02008541085 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 792589793 1250 792588543 792588547
    0x3031e02161d07020115060c030215070513171510080307080c0f010b0f0904050705040218042009090907090603200f0a05101206060519030b1f23 64
    0xc403241103000c10b800f40552085a146c2903a2180c0138568991100c2540c8103458a85001c200d5800d089182c031501250031600200143d090110041e0401d00401142c070b4403460820006513928040d003020f06591040e141160440e1881c00c2d400302d803141040d503009d038072010003803a500d80f40e2148510f1a000428201d034500c1c0c00007002046d50208104450140880000a00160000e603001c034aa100700c0140d440c8c014204039000c03c003081b2061144001900024108540300c1c0c0070780e031a498a03600620406409245401030484030100214080f030319100e090b40b00d50785070180c2101801b04880c002000d00303240340500c440116a0707803803901801c0000e6010300710401c1414280307000210900b0040030f1261207100d9002c11a451034072000c3c00c0c241200e83c21500402c072411b507003a081d24080d05002004564620b4040041500e0380c101c000307409924900020318000780840403058045405e20319401d40c1c42102e11003c5c5409681c2d00710303801e003803129a18041008000b4621405502c0030070710790100f810040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 792591043 1250 792589793 792589829
    0x2030a05070b120123010804240609060506030c0313050f1c080f040209040b0a0f0e010e01060512100f0f0f0501062c0f030f0a03030915020403031e0216 67
    0x18030f0340c0038050001c00f03540800c00d083c3c80302c0082c042020740072a9414024802d00013030502c01c0303115040c000000381403c0c500c441100d01400c0c0008081c24007a1019481c0340c10f20106542c01c05401303407072050390b41102c090b28540f5200901e0309094840d44c3d00715118890010a90305540050184030b0b90301885800c2d802c1920031001018000e11402040089034440c2c180801001d0f0307541410158010f60403940882c0c0c0350301c52110407006003440c171603441850303401e103042800041e00540c0300d40d080b0034141e402004410b40320005c11140050240c40c0c84090307403010303860f00410a001d60000d2442c001030000041c3c1c1c0300d150940c1d441914942150720340b14580d103800410083c0d80100c2000c039141c41080d06042c1018a00c620720318000c942403501806840c000d0503c4031503407003c1019000481c1d410341201d41a9000340ba0081c06003810b06000c80f90040b14030075451842005009550940354076854820842c007015400c0c000b0004d803641164114442c280c1004243d2201007002c0d005028840104903280c18 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 792592293 1250 792591043 792591067
    0x60f120f0a050c0304020d0507080f070f120804060e18040f0209070e011d06090a1e050f0604050402030403030b100e03010b100c080c0f0d030501030210170a0902030a05070b 76
    0x20008040054660400c0c0403c0950001c0d0400c0340d40c495812244111142200d00344607240a1060308222034503c03450310322204a4400045034400c680c15090707088400703070b1610920790f851550f210000b49000001d0000b07101036805054030100344035000e0b162040444102f004000c5c03030031040d14195500c044c0302c0c02c91425070401922255001c50740d400c200c01c800d9000d000081c10547c5490119001610444c042c42c0c05982da00226410210b0007003281403100c3d01c90f03c400080c40c0300302c40805044201017000180780d0030301c880281d0ba03a03d401002141080c0c540420302c406580014130840415036500d41c030201c65542e0700c6820020345004e694084801150500381030840d07140d001c030284104119541d10341d030160301403030440c00707503600c01030864680c1c24102d1020b141509140d03414003640102c0f10007191079035050740024101d0340210344089a00751101c0c0c00340c400e42a0a5505003445540b00c0c00030741f13094865000031007902d2015044502d036080944560342484001d820100c2640c05c00114076030544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 792593543 1250 792592293 792592321
    0x6070c031a07090b0a02011107060e1b010807080601020f011d07061b06090f0b07020a0c050618091b0f030a05060901080a0f0f05011b0f020d0203030103060902060f12 73
    0x1c07803a0750701c046550400741c201800090140c895035650900014108941d64400c0d040f081e492459a0032440e16441c1d1881c1400141260329a22405813007002f003102410411148460b241401c1a12032202a45907240111103000d401002c0360306612504000c00034140c024440c16103111620007114681a00c0d0a140d5400c0c040035500110401c0710840400480001d2012090111035000030001000b910504d012040c200314007001030040c2d03038050100b008241d00465500d842034420300c4603100d5142c546003002070300d018803201042100d005030b903001d03403d082c11005d03150000b029002600c08414001d5a0a00c0c6034418a030000c1000802300034081c000d50140551a0041021940101d56606200303126071340c0c000c920000350000240c8695441802000d07801010002d4001c0000e02008070303640301149807840031240c00341c0052a40b0380034014440c804660310740c5030208d650103145540d06c1d5494810180131000d209a9002c0070800c41d00400c2507120780144a009001241540c040c40c3c0b0b462040626 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 792594793 1250 792593543 792593573
    0x12150103031e090e0403170108010606301d0106170c0a0612050717040b04020102100e0c0f1810030606081207030315091a0f0d05121806070c03 63
    0x100740329640a0400ba0451240070030741341c402d031040c1a540e84504080307401c042e10b221400420340e03000c0c0022031494019000f05040e180d031521a01034101c1c2c0070f010380c265110340c2c64882e034401c0c0a0b55520100b00503260007030a8900c00090000004d80d403090354841c04c4a600d035004c0a01008801c00090213140c0c140010000c140c02116284a61898001c020f001404921060454155500c0004030603074090030f4078940110541c0c011500e2072a1a00d40001094415603003a4098480c1c0d2100d0500d1070080e004070720f0001e4201014011046018041c404400c13008a1200e520510341640c00c4080710b405c118591107a00c42d070303504610041c510708141d400c440031038200812036000200f034800b103070300341200702c809080c0c0c10301c2c0004480010f0110f401c0901d10a41021440904102c0d05000040d02d01e00501440311049030001400c955140810005d4028010000c0094002c030703d40181d908803100c060a40300c41d41c4004800320791a00c00000d11142e0000004458203a9444014014480072100c0e031414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 792596043 1250 792594793 792594827
    0x405120604030503011a0708041205010f11160303020d15260c01050c100905011a09060904060504021801030506070f0f0c06020d06030804120501110a1d1215010303 72
    0x1441c00c05440050042c4414000e0507013100c0310303000c11015031540c0001c4450454100c80c0c820785494807090f0360200345114907010794482d820700b480076000e00071910075540c0c0c903011100c9440c075000d003910010950780040c0d0426801d140d0b09000b40c101201481c0100c01a4407040402030081d1800c0540c1107050350002c125001000a41070700744039860f100000c921040b0102401c0258403401c8841c0242c0c0742101111540c1641820700b0410400c01005401040180c40c20305010035485243c5400e100100b01c088820962049414002c06d0100daa1507121540250001e07101c014480c02004590780948801e03030041b500fa40c048000c210310564018031b5026801640d240c20b02c024941044014850001a00080d00b02540066100c03050401d039070218004692000704161260355030355890b4203668808406a9265003040c02e0081c10721000001c9540c0c000240d11000b1080150448445661160045c999005003020015000000e420030482c080342c1c0000030078051035811850014006244007402c019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 792597293 1250 792596043 792596053
    0x2031503070e0f0103020f1201020c0601080c0d02090a050406090803100e0a054b220506040b0c0906040b180301150b0708040e07050c0c0f011409030106081002040512 73
    0x4050780707983e80e010341100e1701190f0a8180381ea0400c0080c0c24080d90300110f00c030f2988001503003002c0c04004991310b0304a84908094903283c41141050141d40300c0c0c10400203622128000004900d07424a5000540150140720009041010707555550219401950341451042c1a15020810b0320b032142011a032004070114140b20f141000702d40d400440d050344d84030054a0100820f15010002132694030410b4017000030b0810508200b5003001c102c0e9241c2a00c1c000707004880b143c08030220b43d064080c0c840c4615400f20003440c29907a2512210900d65028245d00c66191080002c100103503540c001500107410340300700e00ca80e41c0181ca5000650040340980e11406a4100b51a8128485907405204200c40042c14441d64400b81482d03e402c1030310594200c0c070104030008050112941d4400c01410099210504503200c1001d40020851942208141035000a190b040c00000300b1000502a080510024001048642d2519046420058803540c0c0c580316503400300302001a407030020300c81c8041c610400d020700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 792598543 1250 792597293 792597301
    0x207080f04083a110318030601050306040b06100507020a09390509010302160b1f0803070212030c0d030e0d05031504050402030a1203051506090d0201080901090602031503070e 77
    0x3c0c021000c2909501d20381c2c85103000144450248600080d40202213064a5580c1501111198402811802c05e80280324080c00031900c0c1c00d000032214041c5801c214152101d607101820481c00c6541c1200a400f04082880003400607200c50300507002400d855000030628a850b071800448941c0f4001ca0b50400c0f02e2104c055000c1800d04070401030720702509241c4503988203003001c0160040d00c22030b6408818013000741201f40a000c1001406401050041800700c0003c0c190003007544541000c3c007454250b500104030a43c0146026400010000403941c2070700c1c1865a1030790f0040c00c0001890405007c60b0311240e2103920032105004005201c511402d142c0c1c1941850481c02d015040706802c041d004554030341c082020340d0750804c4141000c503444a01c032600142d4620009000e003c0503181c1041005207400d045209240103016500c00c010b0281c002250000f69400441d21a2400351812409569036a03800010601600056110b800c1c042100c03001c0340341840c117051804441b079201d0051404824184 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 792599793 1250 792598543 792598603
    0xc0201020712030c180e01090506010f0206150406090507020d0201060603140103140705030a0f05241b0409020408150a1812030b0d03021614030a080c010207080f0408 73
    0x1460329807070310300041d44104e5441c00350f4440b014111803241c4d40045640008081c4002c6450506940042405200a03118000155001980302031120096001503000034101c3c003007001036041d4114014004507801c2d98881141040780d5040c3c3d00400144c1002018511a0f03409001e20320052101d1718042100c13066034231210381d030108103010080c64007130005450128410100706d6070000d850b00400352941d581c0103280c01103121880c1041100c540c012802035000010b005003c044010149240c0d2a0003941c8980207043c0c005907510481c00310801c1800b0201d070700710042c4003400142c1b0303121008000f81c1c3c40444078507620800003001d283c0305c0d0f800e144d0b801242c2000c1c005840e810a030b000c2c468811000c0a14829006010744290711900301c00701100b81424954005400c20900103500300c81003819403102c4c501d60380d07010100c880b9601a480103540340001544800144000c8980d140014104600d641d07070303a078283e030182d441e501c031500e0082005e100c48603062021500712076500e44040b541c00d42c00d0b010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 792601043 1250 792599793 792599813
    0x60601200706050903071a040f080703030e0616050d0509040f020412080d11070804090509010b063009010903080a0605031b010e0d051b09100504110409020c03030a0c02010207 77
    0x1c00c2e0800c0382c045a164881d4404000c40070207071180e402040a9501c50000c01c0340250480c0c41101d8824404c0313400000d46600110701d01003941d41603620a1108038040d0180030550f4090340308c2007001220198904042081400f0080b0a040c02d681c42c9903460300c2080c108000d8411250000c00c195204200c10020881c02c041201061503004180c0e94403100d042010f20005c000300719403414580000600c00701000348180061007076500d044401c01040d210300c22954200d44804000c80d0300280c003004038030b09040300b10f070720941c1c404416003000c6420415140750a03c070244c140d4a504980e9142c028402c20103401030f0074594010740da440200035a6141c81c00083da41d4603010002c110400601c001d591059201e10303410446400d0140c028110444545011651080e5090400780b4410318007101c07030300300c0c5401410b0078014140b000d09a5401e80c20481084020070742812000721140040000181014443c0054841c840c4000040c41d1240b400001d0503080c0d64081001604591042290708000b82c000c0c60 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 792602293 1250 792601043 792601049
    0xc0318140a1e030f0203031501082205010504050105090a03020a021005122802070809060c01061503090302070501210c0917010509011112040b1302040903020606012007 74
    0xc460404524124006081c8501c4050240c110500c90039030380b40c0d001420b1001502548a590380240c15104203200b02e0f16400306542c141d6600c104a4217481e0650701c0b889403541c204884200d1903043c00c22605050351072001c024000c9440365110700c10807041c04820b00c2200e50003a2020050000050643d400946990200d80b00030300c21070107841c240b2456481041590102612001c00820b90304011920556208000a91030002c07522824507074440701c4180284c0c1e8505600c850007e0424249004103d910f41002c0420002503681d6000010104455811080f81502c41c0e01e00155008481c24003d0031300f482d641080e0306001500060000c076880001c1303407a032410501c8100190381540e111049501060b1076018102c4441002d0b800b022120041d0b00080c080c80d09000200148a07260401c03540c0b034050415203da4000805001401140c0a014519441440c0c2404020542c0d0313107030300150450341082400e9005034440c00800059580040c4240564801400305c1060613091000d40ba84d15a1140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 792603543 1250 792602293 792602303
    0x31009140307022206090507050c0f01200c2103180106060509132a02071202030c0d03020309040920011e0f1e020c0109090e030316110d020d030c0318 66
    0x60300d032505030b104640c491001b4000403042070000307080210700284280c116000c604410b004282d0300781d2440074144034402c0880003e0740850313048880050072104640140601035010300840ca21000040144100c202c2c103641c0000b00d2580701d0030600d0b0b5488424034510091107040c2c0c903004043c000c2c6074020040e00e00c045403c85890042035107000342ca801400c031030790f85171420164100e046030b0010b42442120803556080d030308690615613690b0401d21000b0b040c3d400650150001700c40280107007084d0840807000b501a00440c0d25000301200031a0840b0040c050540700d0f40801140901b400042003260211610b0910306144210000701400b481d90094032101c109001d50480d0400322140201c514440c2d500c288522045200043c01010b0b440d85404940c06e80000d42c0c0c96404a941e2001d03200300c00c044406d00d802541148d0f91010640149242c4105000502402030340d42e1050030750401004844d1421507024150083c003e03203020342506c281c01c006009040c18600460b00c4009140b0488981503001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 792604793 1250 792603543 792603589
    0x6060e0d020d021203030601020c190306050c120c09090f06090a0209010e040f0b150f030a020d0b030d0e0918061918050105090d0f02031c060503100914030702 70
    0x40d01c009000c0b55000400290003140940049088107000b00280d44104420303000d0ba00304684d440100030b80410681d524140b40d40e16200c00384041409a4000c07a80400158020343c03400d4014407207100350940445008001075000101003401c0d04041c2907003034018444403103000309402e1030400140c0c9480014810300c1420fa0104001c20183e00c1580c1400d2281009041045800c00303056060b8040c01c400b902e51402403c503050315003415070b0b0300c0d02242c0d000003521020380e0030b5440b01c0e5881c001a5000e6980c040a058480d218010643d800380f10705140c00303141d031701e0300c5005009400903c5000d540040842011000c80314880e6000310020945551000f1406442c5c0400c424550442d001804011407041c0c42c05c1042600200708901540258002ca81710300442e840034503101c00c101c072202041c0148100580050000c0c1900d054411190004c2c24400c0801017189515000030915080203102c4110102d82c4171401c02051080c500500d003d07020700b40000d18030f0b00c909500801c041c0f007200e1707100481c1c54800d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 792606043 1250 792604793 792604819
    0x41b0f0c08040f0f1a07021806030703080406110d0503060a09020d0f0908040905010806070914240901090b12010509100801141906031101050918070207031506060e 72
    0x500300b19000f5000000e62201d0030b03070301c914928507500201e002d00c034608046502c0070190140458140e0b003070560300904074070300001c000d8017002d0b9103100030340060381522a003200400062402c0015001a1080d07944003a1802c20311690b02e440c080006014805010f0100140429512940d43c090103860300c000003d6900c0d102c46c403490004080d2034000302c066901c2e024140b010008440b00902c1141d69045c424055643c0340c1d070748203840e07483c140d40010204401c1c003010030a802c210304c1448003100d80103084011300b42e03482d0035202508800350075020040740d0004141d541580c12132520030140c02c12102180c02c0500070303058480c07854418058181305283c0280050511001003080902400b5144002c1c090b80ea0003c00c6941c8000d4151602443d41da0040199841c019644c407031401181d4025020750b18408054006490540c400300c10107400140301907107400c50040c04103196010360300c43c2e80280a40707465030a210965803000070204850700d0030010104000b40c0c0c44600f040d00b510044540101005d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 792607293 1250 792606043 792606053
    0x23010f1d16052d040218031002040b1b0307020d1b0b030103020310051b0409050609010e0609010612090b160e0102070807090b0d050f0601061803150906140114041b0f0c 74
    0x3c00c842c0d0368044c3c0005460612200181030820243d81c05504540c10080d42c0f06018059000e280909699104244016400741c01e020305807000ca2100704007a2468440640c011500314a0601c03016503403048406808640d0003e1440010024082c0003011803e55040d03500080d1507503141604070100513201c10204444e41d401da1450002d819503003180c00d0380c0307940d2004800050710302118400e100ea03d10100000303d21001c004114441c01000b40316070544e0f802d017001903800d449501d0000c00115614001000050007010350b4600550050038043c0c906184654000e025214540080d8115002403030204030a42002880b20f003624801c25002c0b503030041241c003040c804800010b019200c0d126840c00604400008554a4180c582c140d50b80302e0b10036101c2d5080c0070307880c41920008090030f841500c1c04031020010740c09601458400c06010545d082e2222404809040a0700400501036070070f030506200c1c1c605032041f07004649804100c034a90550700769000d081d001ca44c460810502412151038003c000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 792608543 1250 792607293 792607369
    0xc06150503060106080109200714100f050a06080a020307060e010519030b09060f0307031e06020f21100509130803100f08010923010f1d1605 62
    0x14007110803561391031a00504da135078284a100d02440c58482d103880c0010070044a00051440c1004040c0f0b464103903a25441c1140d020500d010b864001d000229100e40c4d0316000d0810541ca494001094a0400500c5841118415440703041c0d1548180c0c00100140c8001c980c5a040700e006052055400c0000d0005036000e1040c010700c54450304070701e003100c2c80590301940042203418098070020441e81d6080305001803ca10004110ba0582c0300b09802c00006110b40ca0030f6809041a540c0207800b01c0150303803110244d82055420f0208100301180201d1380440e142025140c2900c0c00308500d046081020440c00942c081d030141602803145180054920f40c2113082c00c500a41c1d100840036a60700d03140752010070504041c090780025030442900090719600500a022074540c0080140201c0c1c04180d00843c84021000b88580003552180824240e50702d880c07007040c000122403060444640b1443c04560b051001580c00d501030154403030000d014a4844840c43c0454620030541041d030308214480300001d003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 792609793 1250 792608543 792608549
    0x901050a121b03051606030b19210f1a0c1207050c1f1a2407050f060a0b180403020714030a0b04080406090f0b0d0c03020d0c200304060c0615 62
    0x2403241d032402010000907000900111b41e140d507400c0040405043c10070400142c80341031a00307181e815030024040c605081040c0c50040d80c201d054501c900100e542d55010051035034400f90f400803001c1c000d270355600c540290f10317035030050480c0400751400311400b500584855000d80544100040444e0b03210800808001c1001c0210044e00b401d1082c3c40b40c800060081c00c503009000080f2200305001e4856801d094031115141605180e0180c03954100c0b880d0000070b9088000280c0d624030810103240300c800d6080c40032071b0240d0001c02c1c002c52140c0c0c03e1410702920420354501c101018451600300000f203a1302050000507528510f1046020b150b098000902d042010764020304001414400e0208128040f4010800c55441d5180c0c103295964540851042c41090710a000c16100b00b0000c2012170002544030340710622540c200141020082c464007411942d011105501040c10b00901ca4152500c0d2070b41022040d040000451419080541c018901091003000529003500e8411900d6003010038208a009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 792611043 1250 792609793 792609803
    0x30f030e011d2506050703051e180a050303090609040b011e181215090309050a0e04120503130305030c0421060e010b061c0609020a080f072a050705040c020c0901050a121b03 76
    0x1032b0b04840a03da00e50100d100117092050205003400956810f02000340d84c2e04242c0184a54109804030050201a1a0203007142d8104181d00c25000d0399a000e5070354010788004156607810800b10402c0181c1c654600b160010140d0343c101c807110f5400140314040c086403a07010070b1008510350000b03141c15501c2504942015074400c8041c2008187c03030751b21303401c0c03184188e004000380b080307044010200351100e10081e210000849010003420300881c4c0103000942d0407800d0034000502d0140d58250100c600d040034042083d82101e080401030521546006a161070031824008001c040714103400140b1710310070008941d42c1003210a5500c0030300c249640c0048000e0500ca001590340704940d0a000b84198400c03120f01003500301c7c0c0d20105580c540b09100c11450243e10b8010a403507514a0a601441114520b0007203030288943d40001c603560710f0b213000700191461260010982d02100c242003040302103050700700034010198000b0400608005005c0e10201a42106540d0034907004460383ca881c642181e080541 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 792612293 1250 792611043 792611047
    0x7051c0c0516030c2121030f0207050c010518030a060e060604150603090c051207260a03140706090b01080f210f0c19020a0e04030f030e011d2506050703051e 69
    0x11b4070040f0086c9015010605982c10000d00c0e0500303488808074003135040040c219a200c0902946554000c3c00144a00300248180c1100450850300091800112903404c568054a0340410b142c194000c03c00140c00c1b040880b0f090001414880a501807c2d909103e48401c05840344801000c0c8085190100c014101c0640a0b00120f403050081da0342c2e45925200f81210301c52004c54000d405403c074805041d1185003000907144a070040d4900300c80360000c0000071000617104010101c0001c100c0e12440007914882d000a0a80c0c5d0315000000d13040c207120900355045038000c18602c5284d000e00403400e038103603000540b1164482d01c4e0045085550b00881034031000d03500c180046014088044c030300d440040c41c4210740c0d0700403d036150001d1030595203042d240100400d01860100382d0141c080c0e001000c1c0f10310402d000140ba02c140c0300d410210845d031021489a01e03000040c51040c2c603041d0310100d280034600c1d0b0300911502c80c58080f0061041c80b400002604101c4042000c1c03d40b00b090071109103080b998490855 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 792613543 1250 792612293 792612323
    0x204051005060f34060f02040509070c02030d05040515071a071d01050c0c0d1e030804110a0503070e09010f02071406072307051c0c0516030c21 63
    0x354240e014064004c402c081052001c45102107042501c035500140c90b0700e6080e000f80300d039183c40c0600045921482d1241d02440b000c209501c40162710740c8544c100360741d4600100c01d40c6c011303d41083c500f003442404202d01040144040e031140e1004c1103c11409010150780d440c1a400c06031041d0840701c9440144a2a00b02800001940011f1141c5000d054200b800901c4c43c0078070064031144030740c5100700c09030340000c2807107139075842d1a048074401c0c0c1e80a5510100b9480018034070940c00704400c0c0c42200400d03050810310042c404420750320116080d050365444081400c140000b551221903101e01190410b4007000144075100a400c25401d039040d01030250340710049440c0c103035403108100d03c000744c1c58810200041e10705c0c0d100e68900c2d900702d5011040c40e015040070008a2025501c028400d030360a12440c0008064141c1b408101c00700940103548000f81608207140c040d04100300c126503124841d4032902c0a00110701010818030440d9041000c10600720600c02c1e201000c182c0341200a42105a084071326 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 792614793 1250 792613543 792613567
    0xf0602072406030309290c0318060301030515040f0b070905120c0f04090c051801080601290a17040b10050919020c070b13060e01110604020405100506 66
    0x581c041ca6014185281c050349400850212002c40c84040e001034000d030310420158000c148104d030b982c0200c08004d6010b15442240701da160b4001041100c582e880052015404010302400381554442129014a10b51560b10b5040d918101031494400b85415074010504215042403a141110b50002c2c0580301458451009004404580303c1d8500030820703000607001040c0080380c0d0f0804034800405003043d45441509000041001c0c0500325a1440e06007000301c2c0c2c1d84c1d41d00c00c0c00120043c11001803000c942c10049003500b06541079024032050341c0c41c1800700d110040003074202403188115011503a1102e002c15000c5a022070351144651508400006110034041d048107034a118003403820103080c1096a0341d040c0018503100311901d80041d032304c030f4810940c80d0b280c580041c856086a442151501ca407100a842c0c019030141100c0c151145140f20100905c9400c40c92184064400f400c010502c500001065030722041d00400c000d02ca1f640c2d44001480e02001d198004000d080c010f800d07181c4488121000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 792616043 1250 792614793 792614813
    0x40b28090b040b0a031212020d06061e08010b07021c050c030d090b040905040606170a031d0603060906131a03061305030d1e0905011e0509190f060207 66
    0x181240d4542072011072601400c2600509a06140241c1107050191039038030740700442000f0700030b100d08100c440790014603c3e91440c0050602c3c000400300c001805450210301901c40c200085044101c620308101d040010740d00445841d0440300c0004026540b03021620000c2e201c0002da429402da03001d103d03a010b0042c032078001614003035007a082e402ca40340f1402c428000e442016884c454000d0102c2c042000380601c1b609030700842c1e0003500c2000003061b0a9210040d00b0b0b1004040d020a507503590015002d4028942c5c4032100c0c0d06540e04030302190400000c0d01002c1000c0f807000138400c41c0210642030110700c2c0ca4888080c02c00702586018402c02ca83c0004079200d0182090700080c41d41308ac401c40004c6247c0c6005e070400a28170a80c024015450f00c5a06180c603c041c007415003480424400142c3c000c0e00c800858003942c40301074843c900000341c01c0c61301d510b11407484581040c440c0100c2e1a04081246100002030012003400c6181c95828402540c2d1404986000540b90004c0c640303400462404104191030b030f4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 792617293 1250 792616043 792616049
    0x1218090a050a0f02030c07060f0b0405070210111e0c0a08032805130f050115030308091009020120070504110a080106020c01020a03030e19081b0c090105040b28 70
    0x24103104070b48029284100345c0c00b040d01c170100007442c1000380710700060165000c550000014100491601d0218001404070307003086a4501c0941c1005a5042149540344100c52000018200650034100c43c4980d00c0b108032400e88140311b45500019480350041e004001c0d4514240e404010a0f9480c0b901d0a400c0d02400d83d01e049605c5a68110301c0300344610038503800b03181d1042207400080c0c00d81c09a90740324280850002e10382a01d003035588440102c5200c048643c060003440c040e0b200c42da01410f005d40e0706842c09564850b41044146081e56440050b03900c065450255040981c2c41ca80c03001c00d0394031040c140003c03680110751003403511110742610552400138100700b40380381c0c56034250b1340e90700c00d4240e0721102c3e50750803180142c0010b0340d4100028000c1e03100c0840d807900c0c80111119000d407210b55880400740c2207010340d8044004a0000404250111811029402c0d00007504070100c1d100082140c0c3c11040c010725100b251280003610b941d0701c075076100a1020040c3c0e13416180031019161030816052042c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 792618543 1250 792617293 792617311
    0x1020c243d0915090e0d0513030b0a1d0d0c0201110115030501090c0f0605040b030c0403140a02030c1909180206040e04030e0103050112060e102909091218090a05 71
    0x24002420403013a101c0c3c03d00d41c0e5a200c0180100344001001211075600c2080034801d1a0758805020010400490289104801c9400c0024840c00d213000e180f104502074164aa0040e4092007a04071107542c4600c451041541c2030030403035000540042040d014106202d41840010f4400030000240901500071540080c040e445560f102521101c454141501c0c1d070044002113441008100710820403880150b40c40484548428109a00c0c0da8480c5850102101e00b040558407021540055103000d00c4000603d680407200c04403a0b0780c40840c4890789009520a980e00b082e502e00c10040e0560301c01d008850919802450384d40e4981e260340072003e00c03113800e4500754001400103021031a154020310445060b555104040098441390b5941c00c0c024124194030070500d030141174400d95000c1d00d24010b002600e01400d080031000c0e1040c041100c49001100c980e50701c101608810f10a40280104100c0c0340f01c03640c8002d49030382d00310b90380b47c1d000030022140043c1d4105452204010001455600043c000c0c0100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 792619793 1250 792618543 792618581
    0xa0b0d0b0a1d15010b030702071404090b0c1206040209010f05090406030f03260114100207210b06030a030804020d1a15031c08150d0501020c243d09 65
    0x6030540c1172580c00112011400340e800428180511000840000c020580052000c1050982d03551f6044581c00182c5000009100125208030030340c44c4413188551000c01500d00710304040040000074594420415403e051040003e071060194649030081c0004d11f401c82090201c2c0805031074014545141456aa14040a0121030744d40d0742e22181f400c7c2d03040310045c85c801d5403001804420807414540c000c0c01001540b040c41e0000440841291091908138a00f0030210341d05521810144958400104410310035000006110002034009a41c1a04142c041c0d0704124404024135107c0c544110400320001180e45050402051001000170204820b40c00d9041d034605801c252215410200c13074140c1903020481440014000e101460301c1580000c00090142c080020152903c1c1c0c01c80c0d111204080850300702014110b400010700201a1aa4403440708144041c540700f00030b5107000102243e15511100c040400e18001e5800340210040010001205805207503110313041e0b0002c021104940c0040054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 792621043 1250 792619793 792619799
    0x60518190e0706050a1107170c0603040b160207080a050106060f08040c0b0a050d09060207030306060521150910050102060a020f0f0906131202090a0b0d0b0a1d1501 72
    0x1890052075058154900184141401c06109650582201a004080102080c030002c02c1c04410041d000040102c0d64400007800c10b0890340d11b05180c0000c1e10540958404c1007808005001d960a0507401f00c100e01c809414075083c01400ca041030303a1984040c00a2248400c2081801010742c0031404440d00c0c0c0e210801d01c5405400241d6000504903005820401808800c00102c2c005600070302e408000d600c2d15901d040d41103c180c4003260f81c1d0703071425120107a0209002003010b4040c4203000262200e8144981007140328045400c1c03040d081194410002d89000108511800170710907101c0010f030040204800d40360800f8a060441c03e82c3c032506005114540201e10305141f1072080341e010f845e40586140c40c0840c0c13a000100d40e5404041c11a8200ba4104042220f40d056040100d024220100c06200c298401e40108020500050031041a8a2601c03844c5280755541143c05001aa408040c107101640c409581e0001001103240904103074408060020b00c058000c1040c140c100100d078544981662 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 792622293 1250 792621043 792621091
    0x307060906020307140c0a060221190e010210050c19110d110c0301020406110c10080609040606090e01061e0806010506070807060612030e1002100906060518 69
    0x4440c0705a10240c0c104000e910301003610204011041c3d1100b00448061031949004201035032940e170b0042006070007280440d68080b406071065211481000303022420115038860b184c82c9043d080e810074040c00502ca218400a900a0042418280307409c1400c001c2882d1890612036150f00100c41e044000030f020f80c5201605005210001c4c00b01c500b00010000024030003425a24020071302d100242c5881058405041507800340024005022a56112000442040c8039a480c00b0ba04640b0b01d440346044503420300c0c0103a0b1140303000c2d91242d0304407242021a02c2da41070000040c0555084078140c84e052040b100440101500a02d04407641801f9912219507180c2d401c1c1d82d62012806540402d8002000422062030510080c2180c5030081c8056441d222050782e609048070350a0380140b1030070010240391418181c11400d000c002020566a1210301c981c1410700075102d1040c4542c1c4501e055841c06050184002a40020302400019140304c07101020800b11040360642291481482842079000c02202c3c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 792623543 1250 792622293 792622307
    0x3071203180819021504260a0c0605070c12090501020c06090603040b0415150e06061201061b201512061c0b040f02030607090f0302040c02030f1206030706 68
    0x10b820a15050a101d51a541c9010a0306944003620461003160390501d0f4481500300d030726014034030440382d044000e041022507100c104114250190080c50a01500e00ca964020101d8091180d025000046a50329200306030342070340700c5140c00b808045400090102041e0020111b04c2565802d80071618010545c5c400c00a0501c100e0341140d41118040c0040790010b0505906250460312907110b603506201b11a901000f02c40c0e40301c0d800001c0c035140c5c0c9000c1028050483d10150081000c4d5040d0740742c003e91066808024006105000c104559001d02d04004000d00c2e216810003a40030908681c2000032540500c0c9403004942018400c9a4440f00100d20703106d0902161550343d80c1039100001a5903400405c030071032200c9e0b5450888580f12442d0600090601070800e4400c1d4450070f00343c0f20740703900c500606103080380040001c8103000c003182c014440302e0f00c155212821070b5411180480c041c0300c40d800c101c1c01c1d4010300c10307806607101022580207280c1d150b0301e44443c0f2400040d02185c280e1959454100c0c3c5075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 792624793 1250 792623543 792623591
    0xa050307020d1e0b0f01140d030c020105040812030a05060103060302090114130c0c050c030f0c12030c0106080703140313060e0d050d110715021509010e03071203 71
    0x6540104214030040c00c1100394000d0850158902e074001044003a4102c1c29001d000710104e41d1050200708100702d0501c89545540074201018000c00420511300100e203000c0c602e88406400d11080e84209401c42e80706a045a02420703408058a400c0d5520030704a4020f03400a84410314640d090400103281c0e54480e104907021070b43c00401c2e020355070f4642045184402150520241c1258120152491801050040c1d181c070441a0750342407132280d002d060850074810503d02d0b4520a40101300e00e11403140001401c11043c800445485c07040200d01c02042d461071207041c20441a41d42400000034405202240443c2181d004d5068410140c500300c82c0700c0d440c4d110340c3d0054031010b482110280501d5216171440821180702510841024045403a22031600d4102c0c440d800c0090050000d40b1401601803003540020003100d0341c0c400720b91000181c080d480d1800f6000301c0702102c080c000001e10641d07094000000d41e034000320130b49685024500307080c061070100e842e0401c0880d041801e500000354004000e5651 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 792625899 1106 792624793 792624803
    0x6150504081e07090c1b060b10050c030409020c03090d0b0106180503070308091906050d0c0f080103062003150a050612220f0c06110a 59
    0x2d0002007400303842d010b42000e02d651002160020311038040e280c040301c0c04200440407034403c030768074907006182c03050314240340803a0002c1c8101603100b41c610050503640741042e0881c62000f51524461844030034119441080100f0400c00d0700d40c00707440305c038807180d00b43e03407a141d0000c001414104c2c9000f02a41d14461203001004410780240440501d0480401c3c0429114508230000c0e41300d100c2c52001608620001070000116940c80d8034800070158008a6207030000c0c1c40d100f000700f068000d03150300000c051801d0940c8944a003d00c144070400100d070b40e16400c0a80c25540c80320054444c080301c007004a58004e90102d5502d43c0503000c4c40c0705d145910250780401c3c0030070040180c409560b91143d400b4032000c001c0d4800c0c1d1031a0b480829440164a1440001780000341c0008000d41141e520180c400e82d8130b103003540100101c0300042c0b070031205036a03600944420418043da03104c41186900800d = true := by decide +kernel

theorem cover : BRFrame.Cov 792446043 792625899 := by
  have h0 := BRFrame.cov_init 792446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 792446043 ≤ n) (h2 : n < 792625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
