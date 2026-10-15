-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4330
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:16:25.108203+00:00
-- url     : https://prove2.me/submissions/a53f6c6c-ae21-48db-b50b-8763b10d91f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 778597122 ≤ n < 778776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 778598372 1250 778597122 778597139
    0xc020309090c0306090105010813030c02030712150f0902010207060f050f19120e0a020d1103030307170903090a05010320040906030203061501083709051e03041707 72
    0xb1200c42100400000c20044145040c1107041c0c0504400c0c40e14400a141010040c150b019200f00e0160600c50464030880465400300719410203816804001144175155181490300101502c02c1c43e050203043c890401502c4842d0710500014a40590007803404519124056864000a40c14030040060400000103454160750041c41e41c4107212190b00328612440e10020030016140f600341103168240700071040385400003c1c028070400d804075050803c0c0303140c0b40390200000228001e25509400080100950241c000d403084000c00541c9540c3c25056a402d4401c0751640320382e800c41e59000030701c038205001c60352195001589407000c5a900190008520b00c807101d1a0b04280d22805045884003024821402d090104503000040b00001c2800100e0140019103030040c000c0c0795460051400c00f00f80031007004842c911502104045061091000d00e09680c00905423278007090710544a09000050082920020700038201c2100000d58240b07030404401d00e1804038002c2c002e4000b071041c1100803981c0349 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 778599622 1250 778598372 778598389
    0x6060e0103031716120b0607050d020d020622110609130b0a06050304021005091306090605100503040c15020a05030d0209010306080d140f040305010e0a060e010204180c020309 77
    0x50080e107401e0f8040c519411522880c41009001051400079004548034054000136448000e82c2d400002150708024480491303407d0140502c00b070400d1140069441102d44c001c00c00484d22582942900c2e406d0340d90007076080c000c4c0ca0105600524600000c03005c1c2c00306441c150311301c851007001015145841c0f46100050310099a80740781a0719165101c15a001c40e2502401d143c00506c01400c0c860700f5450144c0000e2a06040781d80460309005000400780042d0341c3d200202c4080b4104480c4c1004403a48a0f00042c0013003460f0300503240941e024100410582e0b000e034064038455070307100302d6401c80c550070072040d0403004c109452948154490884102c0028100f84090a4030400c02d610040c1c031100c024000505079940c079849190a03070080195034032843d5100c81c00d4007004d152581e00d1999041004001d42141c440c3d0703800900613520704410403289a0001c500940d143d40906000d20041c121018824202d1050b44104c10007103524aa01c100b0300895504400e04e00341050040c1d03404c0400380e40c041107080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 778600872 1250 778599622 778599629
    0x3110703021507030b060904180c09050a0c05090f0f01110703053304031b080d090318210c0b0f0403050d09030f0605090703051e063106060e01 63
    0x50300440302d550420203020520990040791450280210803903400803030243c1c4541040a80641d440d400038080103541c40404d00401503001c3d003800c0c18107503509111002050107641e2115090b083c403005242081c46482035480c2e203038004005222200b11502040002400302c41d0b01414003d2020143d8003801e07040c031141c1e00850041c40640144990074a001c0701c00000c00e02200706070003000a220035916207242c0036682c8a42e041c00c041e4051054080c003540451060840180010000542200c02c84299041043c40c54480d48070324820399001154410681242d004221030909685a440c01c50610003a0012800d406000b81810b0251224403406880d442416421101000014104204003080002c0346c1403e14900c0e10404403400c0d503403250a0f080c030300c00028100c0c0780c5400c042211800c081c415030f030080d94800115901c0341c40d4641c910304500543e02c80100b55016910000d142030101103a0900c12a41c00400c0c03c3c0484003060029500f05808042511403a58840e40400e1079014011868060b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 778602122 1250 778600872 778600877
    0xa15120212030c1e030c211e040918020f240d1e020423030309040c09210f0605091507020a021002032b0b0307090f0509030412110103110703 62
    0x14984c000d52007421a68845602074034aa2003007001c0518500041040c0c0140301603105242c40c0214115600140e50050200582c440d11030682e560b0349440300a0008c004840c0710700001e1001000c500300c2907960404040d03020307400400e890702d100301c01e1400983c1c404122003540041c2c800308110461a00c0c2d95000b05580c0c011060f91000440303d0303038442c90b4103030200410f50740f010b40c0b0705400d2080da500c040d01015006440360014510100342a0f500744142c44040740003a00c200852100c0c540c005081c0c599510038894031b21f40042040e104582552008082b1941213010215036221a9a91b040206002007800e00700e80280c040c3d00744401030407200c01d40198450f41c001c0160070428010003c00c034400a02080c01c0d580100300c035041c0f0044603900d1003070018a40810702c0c072000312200580060003600d07004036814058501d000c5842401580310900c8900c21000c01c104503034481c0402541c82c482d034000da6003904100410f1000052070170103080703903403003041c9008185201d407800b4004d590340020604401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 778603372 1250 778602122 778602133
    0x605040f230703061109090906010501030501090c050702060306040207050f0106062a0201180b0f0c010b06120f040515070203092407020108100510020a05060a15120212030c 76
    0x34841e25000c6041541160820030004a415201c0599901400e1000030032154651995088810361201030b180310344c1c8064000d403a2842c007100b07295190030742400303414042881c000c004240780e1054811810810700c80d0303da00d45400202d408110303140d040102840d5002c3e800304036a0000407011301c02040c1e141c0e40103001045807410000040d0148043d003081a540340e4925681e03400341901102c41c04151a02030811101c607004ca4105003c0c1c0e0392541d003110b0107888000640115155807207006080020040d002004058109410041a8403c50b0684000150315001181348445c010b10b2494110b84141d0480301c510303036140c2c102552180d00301e0b11800541c101103180700ea68203002c0c2200d0780c038a905004010504c00000030840da24069250040d04205405000459554040320f103400034000c0200320700302e651280c4000968504842ca01111907016080104802410350b00036000c40e6084868030380d40e0b00c1d04100409908410080c802c1e42d201407104031a5182c0d20050004140c13580d0390034041e04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 778604622 1250 778603372 778603403
    0x40b04030b07080f04030509150a0c1a0c2502090a0c1706031e012717040e1501121410050303090906310203101e17030403060504 57
    0x30300460700103102c8018041c25100308002c000c0102442544980e241c20145d8803080c01001280380c2c03208004030f80d031080400050098485802540e090092031282420060303034812070540d5601018255022000c990051001c00c0000040340b66440e500c0d403007410348422540f030310f0f00010a8002c090303500d02c150642e52144007142c2035000f20600d40c185a0740e1040201c50500360082940c0d04100440722642c85412a40d5128a000030b4000b000050301114190a00a00e44070000d9001d8194960444a036000600504908003003242070728105c800307001021144e65580402480c21071f101c00b40044c1003007017400c41030600003d50720a840d0031400d03541200305945084480a0a0345071190800d034417950003405214403542c1c40824080d8003080544a0190740300b1403140407030303004c4d40c005d48492008000c10244a44031082c0d5029610035000d6042c00188643d640717682e249400d203000c2e1104a600c804600920a40301a941903c00780250041140c0c41c1c242d0f26100d0388200c55043d101110f0000340c801202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 778605872 1250 778604622 778604633
    0xf04140d0609230309030a120302040305100203070e0307080c010f03140f010302040b010e09130c1d0a0609060b1b030903010c09030b010e0c1210051201050a0c1b2402040b0403 77
    0x662100340d5000298a402c00d05c1001035580e1480780760081061b000049001c29003482a01a40c3c0110707841001c86500403084a9600041d41007160400002031070360055000a150000d2114216035104026185c0740764024011241141602602003e0507121216820410718200720284266200f4410b01450b50441c81004240d50450701400d04101c404541003641c1d594540700150861030340d404641958001c0c1c81c00c1c1200d5042c2d58000b01c001036500c0b1204c10103000002041e0303c503035500e074003c010054590110b08116003041c000d080c180c4100344000c1c100d2520710000071303948000380c000700c0c0d040c865090006420b590403403000400040300300343d003001000302e00000705016140084d41e4486c1482e04083c800c2c03031802101d20407520910008040f0300500840070311040500303005000903642c105241c0c42d0030b020b8402551485145031400d6070003407141d4425010701e0603142096442c00160869034840d0002100e4003c400d49450020b44090680f0088500c010801402030041e0203444900d581004d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 778607122 1250 778605872 778605923
    0x50a060e04020f0d050f09060c090d1b0605040603050c041214012a0206160e060a09082e0605010f26070921020f0d0f1b090608030f04140d0609 63
    0x403402664800c200780070712115009c0950317220341d030141c814900c140c00301d0a00304c0d1090303103040009a21040d602e4000c00c1d090b40c08001403044c2c1d096918213200c183c0301c012810695229a11403014101034003042140022618000240e400300a40000304102c0e904002071410400d00170768802078401d0415003410900e405101c401ea100101600510b480d115561014000147c601c1145202c0d0800042c1c50617598001d05846014006400c1100c1003007608003280b10a240448000c05881910740744080800e45243c003542d8203603181070755240007030b9075440826105402c801200300f03005030240868403580c40040f0f602ea071280d003555031a061010311f010095141940a4181c40518103949011400544c0300c00e40001d60041c01a2800001074074a410180651582040d00401d031409a21560800860f044146403e556440004100d12552125403980c1c2c0d2103040e401c0629407000b8071040185002c0d524244200794000380040c50340c2581542e414007182c280600c1140d8140092000300500550f0b07080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 778608372 1250 778607122 778607131
    0x5180c010306051e150307030b011205070918020720041b0c02061c020a0f031b0903080a1112030f0f061f020c03010903030e010b0a050a060e04020f0d050f 68
    0x20200300083c241004680c0e00b00c4090401e4804503441813400035281c0b02d00c0e0315100719030406585e440d00c81c1000d03180200582200c002142c000350035040b40f0091584248545802030a0a40f91013031024a80305100c01c140a01c02c2d40c0c000c0d855405c0c0b1821012909024030b09002c81c0c034582d003062072080028108422910840518205802d5040010b03440d42c0d0014107034840c00b501101c40310389807462550004000b40030490070540e42400410401c0c00e107a00103c400d401820f0b1620240055a0f4007010803c4e900703092100d450000d280800d081000c94241c40041400b4522441c190b0b20341203400d09220b25005d0515818801c80c9070000804c14855141c064007030300034940861002060804c0000030b12a5182c5060180705692940c505c005880d008101d44110b1101c090008d21107000c1c0750038098000d1901301f0200c4515400d02c00407803000e26000c44801c040c1e403001013950308031509144046518072040c0604c203810641c00c0040d1182d10410300b0150000c40e0400401050500c0c10f00d250038880c590190 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 778609622 1250 778608372 778608377
    0x22103060a0e0c070b060406030204060b0a0906031a0f060904110301210b0f091606091a0a2c130911120712020a0306050f01081e030406030504110405180c01 69
    0x70f001456038810211040c03207810411001c2c950315040006402040700d540007d6000f80b074010000b520018100140640c5001620782c42403456460304141d056030101d4011080707480c0c4603844040035103014404850443d4002d401e036402c28103502d000c142102d4010704850a107035008001041030070100c0c5210320814008519510380c0030001e07510082c06c50000381c0541c04810314100016203504081000300301a6003a1000007106664038200030313260113074a002c0c1e45004001404c201c204444900201c50142600c1d694000c40190a40303085083d030b0803910288603401e40d03a02c3e05024182c0d102e0148000700c9096480000f2030f801a45032440154405105683c010030708001d51442040c800f00300f140480d904c0f890010752400315440055800c2c100e130f40004041915007401c0c4480349401c0c2034454103070b45090088802d0107000b8469a03480080b0b0301e070a80f210361700801092201c0380c070030b0b00610b0f00280704441500c4501410b40000342a200c045072440514500304070000c03d0703110108a100542d402c01e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 778610872 1250 778609622 778609649
    0x90b0708060324040314160803060a061809020322051b040c0903020405270303010303020607020f3c0a110d1e140a05060402090a1b0f022103060a 64
    0x401c2010304543c03000b48050148005880c0d80300003909202c003210940000200c5180308144649016846500150349050060345506400304600e400f5001080c01f402c802c1c44804503c2d0718009000b03000e9800107003000c05000d20030101e40c0c0307103503140d20003071525601c100c0c0a0030000b20007020950b0010711080181c1d22030781c06c10502402c040e03009060841680d4060b54040b41030380e203c001d02440c0e01d42c1c0000c8003801180008000c102124003002540c1a244280c0c00d4075015103550300c1c103d1b5504032040071070180d9000a4a460712000091000404050ba08101300c400381c4504034902401442440c1c124a564100314440d0041055181406d154240e0440d00e242c9002241e454070800005400307180721621240e01000c0042c4000a80c0c0b2140d960517020882e40903490340d240803a25036109a404034020399060004c034040c00c2090256010800c0c601490800b49954000d04660034040d0a442e04103500440107101140c480c1c4814a00101122003480d0755070b420208117009503d00d50b0b901564198010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 778612122 1250 778610872 778610923
    0x8070509090a0c0201180c09110f031f050a06050a080f160804060b1c05010b03060705030f1b0d150519032d0308160c020a0513090b07080603 62
    0x1200700303141d00001003820000b865444141d06a00510441340480d0142e1003001d901002c1001c2140d540c01560040b103018081c2400240340b191140c02a40a810500f04051000481d00c070708940030b90710203c044294480341c1960303070000709800300342c0d42c2c00800c00109c00107005101c042d080310b03c09400424210070076102c0d142c0b0b224002c0350188250b02010800c180c0700d0102d428460076410840396080b004100c40e910307111072a00440d05149024044816500344601c5944902d000704541d07114800d80d840d503e14550f00c03900141104074000b44054161a10301c1c401003424074512015066401c094500052020b0240c1144003481c0c0c00b903408548540d0042c200203451950900401741101d911000100200300b07074851240b800005524800e030072919000850081c15440358a041c00b5041c0c0f00014040d90003040310489071500103da001e500007043c540304200c17038100700112244038110a400061205c4481e55030500010b029902071000039240018018035140901041c04090011007022014441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 778613372 1250 778612122 778612129
    0x10903150e010b09270a11090601230c1203040f061107050d08060f1f05030702030f03131e050c0d0c0e040c17011e0e0705150a08070509 60
    0x45480c03a95120035140c0048039181d45003500300040001000b00059004e107007402c0d00c12000c1c100c140c1d1003400520720302c81102c1100c8010505580060304125903050340d142c4401407261180700500310701e04002d0030712810000300c48603940001131103100c03400b00e542e00d019011096207800c54089458440c0d10082080c04006980400c145000c507070b206202103401400b10300e22150764040d14802404070300584141d0514a94054002c85c416030342211200119071401091051402c4456201a2a4900d50004145030381c0075902840d40308010313104491a0425661a0001640064400052901c1c4448080c4200942403401150310603d03c0d0760000040b40640f261950b94021580721405104180c19200c14000124810000781a2800e61070702039060902c1e141e2400e038031600c2040a0068080411040c0800c10b0085156041c0c89109940560804048100040158076034540c503510400320000341c0c1b42c503802ca6020455114803038407600c500700b000b0003821000c0010184000c005082108001030b55 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 778614622 1250 778613372 778613393
    0x1e150314030a0e040902041409060406050a02070f240f1b020f0303220f03020d030b040c0e040b0d0b0712421703090f090405030a05030411090c0309010b010903 70
    0x4584c007240280041c000300b001001c084041c8103950100c002001100100000c8a500880c80b03002e0030801681c445d560101203006500008183d040100e480001003844031420340782c003800c040d4052000300c000c40c6d03240b01142c4c00d10700c90312040340e100d0302512103083d00320f07031981903940e00ca00141015111000301103403240300007405441c49090b01002070032204804620141c640e40d11644034001c0c05403506001e9a920600001c6000107400c10720b003613019080c04c0c0140d405c050055219111491801020031029007400e0480c2900302008521600118054002080c010b085a03202c282c41c42ca503101951003a150003241c4070000c100d0080c16203118203181901510b1001e102c80c03041e5a810300d0101c107885160826407045260740305195010b9550140800200190310040701c4000e4074042e98018858840812034028005400c02d01c4201d41d1240075000440e031051040d00600005040c1200147e0201d50945440302c820341c0100070441030030801d214800540009090040526107181d44010a48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 778615872 1250 778614622 778614647
    0x1206061a092103131e03032c130912080c0417031606061d0c040b1e04060305180610030615030b04140105010f080d031e150314030a 58
    0x2403500960000d8845001e00240c2d0302415210107980d911494002d80054091903401424086054650201060f2802d1a122021030394192150200c4007483c0070620030044c182c0581081d2400700040401841e0307134030036400301038640d15600016910340354244114002e1410040c2000d018503001400080c207100c4c0141c07000c86512129007802080d603a04150f003035000e0f0440d29030b0002c0304910300c02c0803ca4a50411015a03103949460091540646442903c5200c01d880750040204100006e00031028040300600071205151021108901841d00180050f03102d0340c80440040d5603802070214005441c44c1540111401000414940c1480c007020208441315100080c201070390b8040441c4043c0c1e015146030000c64000031038034003900e814104401c100b6000c0081c04117030352030034002042481e00640b100040d03401c01c03001003a03070302d0792018184c00504000100a010001440c200302422315140148004074034000302c8500c01901d5480c3c16602349045859400039030f00103010080201e548070348070200b40c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 778617122 1250 778615872 778615879
    0x5100207050f0a031a011a0f0405040c0504050d03030501240e130b04060806041e0b040f02041d03070c0509060102121e030f0403080109051e0414071206061a09 70
    0x406070b50300002055440d00d0340c0000c2010240029010001e0f8000d002107040300c001340c000101c01000710048018510440000840442c0300340709c01c1c0305509041e0310042826840741041458551a00001445114000f00480005e0344501c018070090600d44032633a0071603409084224210b00c400d402401c9050f003840c0305405110b101007198410885600006c0580030b002d0b004101d030319201c40410703444850485041d240719119003c100380c08042d402c1501f4a168001e0400000c688940d55421510b00010b5004e03644651100ca1310000490718124101d24490003000a5a566480e45030110f04002964401d511483c503c0080049a0740c0100f440d440c0c824018045a42d101d40000d0400c524014811042c47e8011010081048543c400600d0320f014602030746070f40070140e0341c0b807c02c10103640085400c20003054490000d0300c4003020034151941c0141c410400700303564401340581c49180244030b42c4107800e5004640d009000344102441101f001c0c1c20040e42900300b1aa100b43c0c480c0d11407003141c120901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 778618372 1250 778617122 778617139
    0x114010303090e1f0603020903070e01030b040b1320010806041b030b27011802030709030609050a140303180106080c0d051f0f0b0102010e0a0209060a170303010f0510020705 76
    0xa4603440c1944580c040c04e0606003408903070711840001c0080d00f05541c0c06010344038000000c1412094181e03400d0499501c081102c56076134840d609c0c07150342a00540304060321110000d0b040f0004100c0030343d417440621a00350240740040e0550005107849030140407107001e0fa1030203001d200f03090000300e10070605601500380400c1c4804440f02041c15039030b0002d01000301c00b5100c0c8040220b5803500d03d5150403a411444c2c491313000c0c4000048102288401c2c0c4a5602280481004200064031500103001050188096513820b0034140c44840c803140c0244000d41045e00000100b0190130326004560040301c004c1030080160a0900c0c881c1c0b0342e0351403010040e5109050040514003001410804030241c0511102001d504041d854001e601408620881201c05810028003d0087d44141310301182d840e041002040140d8454003071001d03030390014103180d420204459000c500310181c2c40003007040ea074500b001595658945015000a02e1035600b200c1d101c3c0c2e40c400d00c038908065000642c2000e84504892445 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 778619622 1250 778618372 778618381
    0x7030b0d020303030c03071107240504030213051b07031b170c21030603060a090c09020708190e03071701151d011505250609080c0114010303090e 64
    0x1200c420110030300952610001080010035420080607501030100e580b6240010010213244039100d29031800f41c040c0710503600305003401c0b1802c20090403003c1189818064030741526a008250385010440310b0000c410744820903c40c0b040c0e40c64407155020040c1e48025414820700755001407020b131000c000e4501601c600340040c424000304055502994402019280c0d0340c0e000c0030780090319001c400c3c0e0030210081050b1004610760000f141240e1013030304010003508a6035588030880005101010095030a008114000310b542c000c0c0d032000700a250701810007a40c603407007084a101a1003c90207130001c10044c800b45908071301d80300001c110b400d45041460103c100985094514010b1035840b5aa43c031390345540b18001031415252103545c0c40201100803400c5540c0c1c8690518901c030042241c99400504108500d40760484104102003021400b90f02481070001035468110542d00311031070603964490f0012340000c041c0340900c2070a00d41780d21a1002c01940d8510344014105180c04c0c80b401c00c100d6482000034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 778620872 1250 778619622 778619629
    0x60e0a031403160f1407260f0106080129030a0b130605070e030d020c01020606060901110a030521040b06040f09170a02070b090a09091b03051006140907030b 69
    0x3c41148200c141d8204075460035080204050b8007240e02951401040e0100056100c0d000c01c1c41d0051b25036034007224020b5079100c140d44c401c507046002d09078014058140360b40d8642d8400e004883c0200f00140001c103881d0810441d52811050380707000400c400007108190320303090f20080b420803103850f000405072955036140c825514041c90b048400514aa142404200c059900b0845000e4941026001c48803880e1a40c0781c16a41d4040d00c00444c0d015034481c03400146071b07240c2079000306688a070614041c160800094411481e000c0b802c0070850109d54013040900742043d00c804000001300c0d2555120604d810181c8891a207d503001d44003d0141c1d40350800c004100351180c10628a0580c481d11202251090815131035480e040740b03110304018001c10400189440600040c0c654400c4000d2807014000c0c40d11080c1d5000300000b4004036030080001c803846000e00785101d1400300650080c03003e040c0c0d10012130480340859030550440c01004962250214050715900040c543c0940d29080000e202004000007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 778622122 1250 778620872 778620877
    0x21090c210611131502150a0603031715130915050609090a08090402070318060c0c090c120506240c0f0d02151b04090b0a060e0a031403 59
    0x4404000000500110800042003103000064001d200821545101c461400c01c02e1203401d003942c0b500d0f400b84009220078507840c00003403c265964011154180404440e103040781c44100e9106000301e680305000c000b41908804850134400300360f1807c841d07030700e0842c50340d02407040220305990050307515003e40b10241481c0d5104440050300000702036200c3daa805d0146002d41421102c00f401110028041030040701c00141d050303c4c4a50089280d81001d4415061000941140c0d0084e0704204800d01c40303812461703400580101402051340c1d01c203400e096038101101c0100e120782c4a0b240c442d280803586c2d42603a60000c030b2001040310801001c1101c1e1600e01c00a040001203402082031031400190803040c0306000c40051600c20310308400c1c0c5000c0030004500d19220170b240144e030805a0070640601c1004a407031081e465200215004a264041130034507044100e41150300115152551603a01e2402444e10120380002010540740400c6508200c902107003000440380f0000380320811a41d42e0f81103018040c000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 778623372 1250 778622122 778622129
    0x3150e010806060a0807061202090316030c0303031103071b02281d130b07020f031201060201200a0e061c1509020f0304140f070801150621090c 63
    0x41210440d6103072444140c8500c82038604510420450900080604012035640308440701902c13aa20004003880004000e5480103e41702d07414000c2108400c0601141c0d1905000b030750091030541241800d600c0c0c0542155040a01d82c03202c0c0d4028020008159030064820500c15544800243e8045141c804607007083e112108180d9003054030095901e105400804900448001e101c1c400c0400c4605400443c1030b000036030700b5004500c030f108680e401041410040c0e6401260510440c6c00700410444040e0840e04071321020b80f45040c2e010010041658240656a44108056805028a408400800c03050720030131002d11305001c101000d0028aa07100404e59212081c99485061011415001c0d5001882c1040324969405040a0301040c895414400d0721b4030300d15546003003491500e441c0c0b101601e1303980c42060501c9600c59901c4081308910140724807030052110000210b004014002c4020b41e04c1c0c030325000f250401642e1601041c42906107852070035064001320002814080b03074181300503e00d48580 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 778624622 1250 778623372 778623389
    0x206070206130b030a0b0117010e060a030510090201171329090a020a0f06080a0b0d0f0b0a1d03180103180b070305010608190c0302090a060801140301090b070315 71
    0x400081c150700d40400131441440c03111001c0041e40e82c50710040d20311054813010340b41c098074030300300501c509120012078130b030030080060540d114135641c0d80d44c030351405c1039100c0000c06140c1ca58a4140c11960031a1080e10280d4124041c400c0c01c0c5002294104081403080002d4441c02d0206500384507040c11503102c01030208400c40c030080c0c0707240410045980c0c11149030124050a0854800902441c01e61040410b503026030f030381c071001500c801d6509009044201000356000350340c0320349140003540c0480501e003880e210794803085c103a1a0405000c8115207114450102c100c110b490b0205042ca4040200c56609003c3c0000d1640c284c1644012002400000a01b81d40710603a83da8030014401c1c95400d1038410b103100e5030184487e030b0b02d504044445130000c0d036402e00d078011603400c0d00c40c03003c000340c1001424100354640182040a210000364a9145540c01140410074080c01400880c07140b02d50030701d9203801503009004054150b90340702c074000c07070040c8100b0805642c0c6040704091013000841c60010078252 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 778625872 1250 778624622 778624657
    0x91311040e150f07020111030109020705121605010b030105270c03070e0907061e05071a0109090302010b0d0b160909060f0503061303090603390809070f030206070206 73
    0x1140c10740303035102e4195081c0382900803400006003200d10500410511210301104581980d281c850034101941107407500301e810380200c40d0100c1c0c1e040c41c0140541501d0054101c8203000c900c00c1c0c2020341c21510361012040c02a414a401c005200742c44c6a0082c0c1c1e1092942c20040201a15092440c20000c0100c48581d141c0104903000503c0307440c0182030350141042c0015100c000740d46502c2598503400801003100c2d9480501c1040c0501750040000e0310b106801540040328003038440700305854030f4000b600001d4050703954400d84018141c1c24421408180300513100d00604980644803000580f1008281250f01060702903102d6801c0d104001e802e00400040300d0034400680c071140c8145601c0750300d018180c0240f0039007001881c07030180a800741c4003243d01038907154856820214210003400c42801c12038001c2c2c031941a8004410400c2c6002200040840c41640800c220701c500213108640c00f60482d160796004190600803098149100d1080303942c1105c1581c5d90300c1142c0b01142c00e0740101401e0340c0d88402030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 778627122 1250 778625872 778625893
    0x503010203041101111c080403170711010f020f0322150501140d031d06091f0e010504150309060b09090a020a0605040e0c1806030411010e091311040e 66
    0x76100c0f509180b0000f40c84240b940b203c1d079644e80341e4841c0070120000c100d0744900d094070303a041e0040400c150014001c1c60f000b81101d1041c0381c0ca48400c0000c0e140341c80094103200c400610a1420711030706107107200d03801d42540b602040b4044007a0300e0001901844102e81e00c00581601e1988a5a141c0c0580d90f002291a40b407038030080c45940144000d1013050070000b000c2c5250442ca282811a2084844e03240e22100b075034090013500c50342c00c880c1c20488990441c1082201240f0303a80d0748139402c1c03d081608002031010b44122a0000c01001400000b241402800c1c0000d0160003062040b00c0948109850300003855401c90500c80058014144426041124181485003009012582d00c0941e0300a030f9100c088107680311400c8400d03114910424038482c03c0302c404144180441300080400020080c0c05440c03200c50040012056842a10102c52580140c000c2c0002560458902c0000c5001140d881c03c061a0990000c0e80b0000c2030b03000180703079008003800c1a00e6a40e4980c09003151048440031a440f0302007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 778628372 1250 778627122 778627133
    0x41a090a09060c050a0807030905011d064f17030708060306100e1003080c030c19150b040f0f0221040203152a03270601050d0606050301020304 63
    0x10080c00c10b071481030410300303a021524000c404840e01c0c144141c1d25801c1076501d924084000b000d104804030707540e5403661ba10742214100b0184004414100c41c003d080203041144100b080b019020515200b8041101e204500b08a5203c210090850f002040d12407118140b11010168205520004048031a641c1e5100805100030780a5481000180c0710004643c4648007050b5070350108590b8004981e1030b0762400e200040f81c0740340c1ea0390030010f141043e1440980f69070740c0108607003000210f5402c1c0d9001003880301c11050108038083c1100800043c2ea014000d10b500d5031030309080c1281c00d04014a4454929050a8489074003000d2041808482000540030b2500800080d40c0919074440c1400034104d91000e034040010744180c080c560003002011082c0e0813990a0211007802030101d8600700308101c1088031180f04d01032030781642c00010389403543c911b8075008688a92100301000c4180c02030303107881100d44c00c200280c114152002100d054184444510340100500241d4200640550001c000d0104111 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 778629622 1250 778628372 778628381
    0x509010902040303030f15180204080f0c010207152c220c110307170f0406180b0307140c010e300f031906080d0903030906021902041a090a 61
    0x2813099905000da080044030032829641080060744031405150300070401006540323808120b4280a030805402c00d03580700050790811514941252250b04a0160f076015980d040c0310703141c00342c282e00e90781c0758080b041003400074000c031110000d40307a600e5000702c010702c1408501014100c1c0c241d0000c140c8450081d141c108502000182c1e0842c124480c03c00e10111600c0b0b0003540034502e0079051400070344c00e10700c0301c2d280e2000400300300002030702000081220b209a5048280204041c28642d00d44002c0010110854000b445d505d03030001c1e804400c14400d0002080c0e2081c40032142d006941d030f40035242d880014100c0d004200d001088003052007a00220a03a018510911020054482d6003514031400d00b1214090300d4841c61034551089801000000c1e41081804059162802d00c1038000130f486440f09031f041d10740b450036844800400d01e0300c0707010410180c2c02280e0030041c0c807080c800792048540803000f41080710b540d0032002b03125070344804d42003005d0304102807824043c910003000b8001174280700e4140c00c020f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 778630872 1250 778629622 778629629
    0x1302210a0b0c070201050d0504020109030b04050703120c0302030a03050c0d1a040b01020102070312020f13121b050d0807052803030f02040f030b19020d0b1801080d0503090106050901090204 83
    0x150001410030103454040e54074440c4c0603150589080300078a12a0010040100300701c0c1845012800840400d00002c005403143c0d204034010010642542071214206541c64500c40800019054200000f640481038594001c61810085440c0d191003441c24100e01070381c070b41d05000c10b02e481e0161140c040380c2e120100c040c4505550802000e4039000c0120300b40c0c4038111000c0c000c0f035960f44080ca80201030394018150003003145200c2e814041c400c5000c0c1e00c60b00b02a0703c01001a152190800148504542d0f080312502c621920105032614100215001001d013280140c1600f42c003044002c140402403015080c0d0b041803481803103c0c0400144120111408803605400080ca071800340003541040c0d100301ca040e42c0c00242c19500041c5140d5031024409401440c00e104804071401880700005140042c101068030000082038044100c17043c0700d25512180c19140c6600c1d248001003006403800b140c940ca505a00749091a40da1b40c1e40640c00b405441c50358096a0031075041000002c2c3e0040c140c4c0900250f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 778632122 1250 778630872 778630883
    0x1e0a1704020d060e03090f0d0317090f010627060807050d02030109060903031b0203040e06040c030f050a0507110601030b0c22060503040606090e0606060a27050a15081302210a 77
    0x1447c500014030142e032100c0c000040105985010714103c0c48601c4440e1030b4400c1000c0121032001c03c1414601d400e440441d070110002c0f80c041d01c002c0f500e61001168000191400c0b0a0821415181c11902c9a54166500c14a40a0b031003040c503260641d03c0030341001e5035407a0404da040c0f001144524000b0010145110006000a1159002036200d44080102d50445e800c07000f9240a984410017000028140b41c0e141c1300506603070b28428990800540036240c812856483c000883c1c2c40c0842d0090005000f0040720038060b002180144000340e10048002d400544c07203920691100a03d2040225000c13104003200004402d081c00040c0417a4400c00451103548140e0301480701e9940c92114400380e03410034200d48482c5d00100001401c40c01d11202038641e500c0c480c030380855071103030449980c40c10b1141c0303503050080382148034402d2009043c0884614000c200781030054031950805100100010302c05082c540c4131000040d0554255a22402c00c18400410300600c2400d40f011585216038440003031404656 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 778633372 1250 778632122 778632139
    0x415090c0c080a0f0e0d060606021c141803030409272a0b1201140102060705040b09040b0913050601050901080d03050c130303051e0a1704020d060e0309 67
    0x202911501801d800300741c0c012145800d15041c18020b982d12004034400001700b00688219140d1075a0f00c9440c03e0700c003801071100042c646d08118009091020400d0460072995409070701c1c1501c2a80849000520140c41c80800d0705c8903400821881c111a824107031550601c0b02190110700402241d00035030300b540404a21950121441e0412a4504050360026140d21190042443c0604c40c4086000c1120155280320b096141c9a4290704040e820915443c440e0303008084c0144611070150b00a2468440d0900007042c861410040040551281c0d00a110000380701142d000c0c040d0715150000c91000d000203002c080ca0b40b07044828507021104d040380c291698440e1200005040c203011000c141a0b400420140c803404030399441c140d01604020300407441c1c2800810100600401c00d60740040a540b0070750b942c0755079240e040a007038070740b000d20030342491944810415040000e40001c4039200c182098402036800382d4070740c0000b81c95012a120040d103d0350030901140d04020700030000b003c0b01e0b80f08565104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 778634622 1250 778633372 778633391
    0x130e060130020f0d052d0a090b011203090803070827060708032a0a030905030702030a03170a1802040b0102010f05040b0a3605120415030501120c0314010b041509 71
    0xc010309400702100d1880f0540443c2c1101c51b190b40c0300f0880d40720710444004a0303108495038580880600c00d034003400358540a0b8400314200b5500c0220100100200030040d824115241c56101d007600c01c09128402e190491180081541d4104414000b003010040c111a20f0348003504002d2015030040b201350a84034408604080558020074940d040c06400b04c4003542020480c8030160000d09001e4416030350742c0b006000540c0180c0d01009030f0103110384030f5a40ca41005a5580700c0c2d02110364090042c000c01805d04d102420b00b03040400c02422000d40480d8003140f070030a13680040c0d00400f901c0e03040c03130f400d141404c042106104400b10001d01a1080d00b030208901e001c016848100a02c40d03050304c007200b2082e0b203500e59044d41604c0c40c241240d80601c1c00da842c0c0c8040041c0f40640f5901c2503000b0340044010100d41c0131550b030188141801030a403000310b140110042c1d614511040d17014000282490b44009000c036007403009502a980741607025108000c0300c61186120f1b09804800e200300380d0b085080100e0302 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 778635872 1250 778634622 778634641
    0x23030a05130c05040b0424170d1d181008240c09310b0d080d110d0204080a140c0919140408130e060130020f0d05 50
    0x581c00c1d00b280d58001400d080108100c05000c1e50a2259401a1a148582202000c894180b007061110381d000c0040c062a041506620500d400f172a40541e402012080c290150000a54111210011361071001e180020000035550090b40b009801d40c181d0300002c200c00480c15003031282c01d070350310401101d01a1088410200f000381d40a404440d20b40403200200352262003402c054241000300810f10714084404400707800c2c08040312500c480100751a0920107a490841d41b10b0000b00060a9905100c50710082e103500c0002d21800351780640d005d43e03410441003000942001e40f03c030400054001d40d0750310343d240076407640c40340b4101c0c050781c0b04528943c8038017030b04c40005100040ca2601074002c0a8a640d05e0141d04480148040c0e003000c015120141c004103030b44280301851080384a070310090b4480c0001640c410440180da00305070001c10181003444900e0381c0091400020703140740500c0401c80c80d20b00c4140350300e4100e040d61419240380040395018a411418020b0809081901c00c00c0140b681c0c0c00909 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 778637122 1250 778635872 778635901
    0x2d0d0c0905030f071208070203030a02030717040317090a210b09010c0c030c08090303030103061a090c030c071b03030309050d051305010507062a02390123030a05 71
    0x701615070040404000482d1180400b100090040110307d060a00707035000f19045501031201c1c44016000014268100f02210854020f106440d01c415070600c0d00f182d4070030600d18958840708026410208428031075a0703504001c1340240c030034003003110303a1304501285400940c900500101d400800f080700185d9406070510440c10000310039540c0c14007600c42601d082e5000c491000c416106030038204040c10036900d08100442c001c41c407988000400c2c80d00314420003081000310621501c502800800d02c440918020242d035002040d480c5110754503001441c040b41a880440c4907500d50090418000080c5505903004c5d07d54107020300e065030010000f2400454a52094071001032005909003c2030105503c12005400038522510300080e01480d00281036651601212034481401101010301c0784095040c000644162000c040760818528075050001007900c541c2d04400419404800c0dd000c1e9030710903421055410b0b043c50090048001c6040c18406c0d40c0c0c41111401000382c00c1001007004140304001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 778638372 1250 778637122 778637143
    0x1051504090c06050f0705031201051512010618090504120e100504181d0a0c0501020d090902030c07020603090a030807050903060414071d040c060e062d0d0c090503 72
    0x10b9080b012410000c0549070380d00401c41049100e04240290000600200001c00d40d80c00f0510785d2007015850401009054030762100e0b5a00c02d600244540b002d00f80350158120705450700ba090076080c80d14031071007a030703180182d991004d0220707814a024041440382070301c0c0010100c03150ba501d10320390703581300024082d03840c9165400304c5c00910100130401036840405a4802d98021104d0b021032203100300d80940c0901514590083d0142e0004001c550070400403481c244000e09081c006440c106d190100050210300c1940b05d59941141c00100084180041c5000c0703c8016600500e010385a042c190341c2c040d81c0d003140d802c00b180451b001c440494030141c0548150381000800800030122a40c56075105100440c20104c80c00341c40c0f050100200700068034010030703500208803c0d0751400c20328240c103140d003244125901c200d0600c41c010420520584910301121900c190011103201c0c01c0070f154243c0c42c03000c4007a09030743c004e042011695120300300305900300828030380490351141034840e01d070000c15485a40c46c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 778639622 1250 778638372 778638383
    0x30b040311030904091109011e0902130503010221010e010321020c03062802031303081306051006030e0c090a0c020f1c08010f0f090218030703050105150409 69
    0x18000034412601044004404025642004854000b080176a0f6166800300d030140030544001249041c101e0030140107107041c042d101c1c0708c0c0182c88110031012a0a0041d00041900020ba4107004565144201c00410300031340210355030702507801c20304003244e111103c000041000c540002010b501001d500350580c1c0e001800c1c0c5030b00c83c2061480c16858511004c1c1402580151100d01c102c541e81405803511500e80070b8120350560700303441482c040012000c481c0d03404d010f00c14000e2010761030454a450a0613940b41c02c0281c11500c54840702124081d01981c014140b504100c00c01c210075680c515501b0445080d52410300c183c1e900d245040e42c4500c0c090501c84d80042e01e1500045500400760888013413907210f0b00550310000300e03010303481e41410303405240c180c25023281049004c4501da101401c5030040c000484040910340c00d112402824542a10400e0040354021419101d400c03200035040c01d6502008045801c01e55403468103d02030101100c0c2c4001414400304480094100741c0035003042d050f07104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 778640872 1250 778639622 778639643
    0x90a0906030201022a030d030c022a10020f01150905060303032a0d0207060b01020708161e0510030501030b06060f040306050403020115030c030213020a020c0d0204020d060f140a03 79
    0x1e892164072612202c100c1c0001721540754040b030143c1c0f001d12408810030542d5a0201e401104901c010f841c4c800c403031010800004c00f00307110740710440700941443c1c2040c0781241c0901d104194100203c0c6005c80408178007050b540f800ca459900303000c2510044040b10051503040c020369448004044e22030000b102c0003503a4510801d02c11603c41d65160026150842c03040d60181020140e5000740c00300e803c0a1700442e50f00740d032041041000c1d85c040103000c0060010700002c02100b0f00c40100710825401e10300c0340d080340010b00740f2440403a143d200365090150401070014180c1c0d4004580c014043e0000b80f2003620250280004a02141040c404031141c14108844441c64580f4640c1d5040080000600681c110f560b141200a10b60100410610045000d01d05071080c0c9410350040050301f48080140d040010f01c1000100d000c540c01060000184000305c0c0d4582181c0007900225000e0721418042d88201d5140c10804901126411603040648103030380030703045198896909006010686010290540b02c0c007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 778642122 1250 778640872 778640893
    0x2060a0614220f0906050f010b0a08090c060c1606050c0703030503090114010803121e060904020f132f0f070609060c050c010c020d080c070305120c090a090603020102 73
    0x82e0307407a045180c044030100c0c800018900340c100308071040099248512038590180764140290307405415008021030446801c035500d408120105803041040ca0004d000c80000001d84030082409090080400609000d42e600002001700c1e803514140c3c184180955003d00703020030903e2003403044d9060411401d000f0302c0c041e0709589060b10107070270050881d4825074079428100704510214000c98002c1000300019500c400c2c141d07111f41d00d100310041600751000ca100700c0100b89064805101ca03000035095a1180b030907101ca001048010200004944d006080a6000c800d520803940c421a000404110404a501d079038402514901c2000360041c0400101403200340360381e0184034010014a442180009a6050280c3c1c550080e00d400c608803001040d400300c1c2c8014408403e02a130402c07000307035101400c0c40780b41a0704003406a94000d840e0005090b008120750040600443c01c507032000c1c610300c4148105242451803e54503501001750907016942d80703000007894070000d0107041d065039030503000742107070191 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 778643372 1250 778642122 778642129
    0x150d05010e0406510f08060108060f010b0c1e0d030b1507080306061306020a2306070318050601030c1406040305120d02070b070f03112803021201080604020102060a0614 74
    0x1a02030010740d160110303c0c0e505200740e86a0110b240100003506941417000c1ca005141030908105130311841c842c0e0000c0c010824003502d070036182c60640342e040e50b809846080190184d45040d074601b040011079090a00a0300210030001981d9a9500c09030303605100b141a1002131041801d04001d12010400381840444009500300029551100e0040c0a06040001c803450f0440c0304403070396100c1c2015070070074914481840042d90104c2900385d920b69841700428007001071070350b5904004220340e0400daa1003071044140a0b00160f1800c1a503005012600b07156103d08000342224041d1090302c8522402101d000000e0612000380c1d0100c9070000c02074040d4004281e4000d20325800080c1840c005a1308010a00000340090300c80e50048007295901e41c82003921300d01c040c04030303450a4505146e960040c03165281c0d4292400c01c000b4014240031441d0b61100d82070005801074083c0600f9005143d000d20004282c20000065071403146000741d007212040e8541c42c54400c00c9074610b02412000b08000f030141c49450031b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 778644622 1250 778643372 778643471
    0x10050403030902030a06050403031109030c040902060904110c15130605090a08030c0d06092918071d09060109030b0711030406120b0f01080105150d05010e0406 70
    0x2406070a010500100c0750b8002410040241c0301140c8950346c505c140024580d0510804ac42810900840da20740151030700042e9440d03204411003889981c50341d180c44210340714842036580c41c07100504248405800322000c1c4132a9008280454400d04c5000e420120300750604441034007440c000110900030b5840d60b1540c1016100c02850502a4032a0005010014004400541c8145150380c1c1c1c05444508004000341070b580240c3c80030706541e0404018083c6095207840081d00560130040390b41300d100f01000403401c0e20900445110f1003a20400c104108142c11800f5025109104241071079010031010030802d0502c0240d40803800201864410b05c00910003e4081d80c10584600f030400280f1200c0340c0c0c292455209402c80c00c0080e004412120300c05045000f10341114104032280d00e1400b4070310000074000441481000e1091941c90785000d403660385201101c112948a450500007581c40f0341c6420b10003001a03500302c030000d1a0070705460100c44e02c9480e241301c0810400300c004003070780c40c480b4109650 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 778645872 1250 778644622 778644631
    0x20703090302101710050f19060516120c050601170706050309010f05100501020d09150e2403060901092306180f0103052e0c0c0206030411030d0903051005 68
    0xb0a01e413805038030859011041c10f2240030141d00c1c00c0d015504141c18020421034051609014440200d500050501418020800d0310780d10314000e0345558a1685080e641080f41602901413402e12101c244165448000c0081c52401041121496640c590081c0300100c2c80c5007071503c0b640c0182005001480c400d00046401104110001c114080181040001c0300e0083e6103003107089018a000b0051560103012a01c11303010a4107000c900310340381c40703030100c0303500070950b0854100b00e030801000140d950340104204402c00c24422030b55035800380800751941a84280c99251003448640c0001407100085d004091210f50011601f070002840440f4a00c004200500503540c86aa180074004401850003000b0348a10014070240c2d0641d4590b05109043c019020960f44010055080c60348a403015002e2240c2040503980000075403283c0384d03034102c2d401c0295140c0250f100f5400010300007400f450803c041c00c0c52030101c0c140c0d00e4a0918101c281d401c5055032000800700d4000c1003074480700e00078907070100742c0c413 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 778647122 1250 778645872 778645877
    0x90a02060a0e061c0c110c090c0f070602033313020c0307050604021302040302090c0a020313080c030706090f06080402060d0c020d08090118020927070509090102070309030210 77
    0x980714000001000fa03000f40802d006040d812a40400c1100d480740155840c50304103051806080c0054100203490f41c8000c5d03211406000c902e00428400d50011007150900243c40c1c2c003640e1103001529041010b1341c42502d0035014140704051658504010918094400c40c0c0404c0c29010800b506040c400d015a000c1210031020b5400d11903514014818401850402c0c490f074003514582c6880d01c108220086000040b207611441884103000513160b4800203900102e041910a0b181c0d00c070980200d00d51707c074510026243d80e40345c2134000358840c2c001500c010103400032010398140c1d513243c4004031003022145c8266003416040e8030080004a0140d980c0c0d642190000e00719034a0221004000c6007500c0e90502e252006a003c1856844a1544184c1080d0004801c0000b440800704051080300c12901c061300180c803c0301d1840100c0c03811441200a42041d00762aa18104042c003400d500f80c1d01c0b005140b003941d001c0e400f0323500094040c90b418400c59074491341c107485030891907046400b4005401015040c1ca800e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 778648372 1250 778647122 778647137
    0x9050619230a02250b1b0a0204090c05130c0e0f030a1e0b0c09031e0307140606040608010b1320030c0403060b010f0807110a081207020c09090a02060a 66
    0x707060070750030007000d01141a030010002500412a08400300d90803107441645600783c00000c1c800b0418020413074240602d00c4034445042103a41c1e40780d90a01250b400700070362051070450760b9001c229812010a08030f840c1110b031103000f00b000d04103090540d4040030104001454800c13403508246410400c0c146a20405811149082065600c44004424682e60280c035900d0580a06040210718a240c03540041c01e02c45080c2407046075404281c3c2d038104e9100302982500c5004000c01807103020419161125082100201c500010b8402103464500665442e800b8508040e008900c403141400303817040425000e00a01c4c801e241004a1400a01344484502c00c0508824003098403940c002002d58056544450030650f518594503090044842c0000c000341484079203900f00203419040241140d102c5820305140b0b150f8400307181c01c20306104846600602c441804213440700340740800142c442c0329901c540c00712803820480c0f00420a034444220740b00c01d4154064100e08006090400c003074561659941030080c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 778649622 1250 778648372 778648427
    0x51e0c091305010504060506070f021302190822030c0803041b06021f09033e0f010507080108030a1d040504060b03060a1e020715090506010609050619 66
    0x1c0d1048401c0051016064542006000c285440c2c41039030000d00048074024601041c507a03e0f4030143c03614031400f0341b013400140100c50842200d901192007140708841000c1c4414440b141c00fa00520050b1400c0000c035100704913240c80d010140c06a8500c144c0c050322801154072090b40d03642142e6000034821202c8070410b031102d2420407809002d0303001170101703500a00b60407085a43e510000105515135107507028107120341c0c80d002c030f500b107031440c448003000a08410301b2458003c03600c4108a0794102141a201f07201c07982c800059008a802c410301c01c0408001e102e99141e01104440012080c0144e40c00c9400403c000c2c5c1140d401840c4501e1400c1e0071014034110380310031400103411607108850644050b61030780c290200500d2f040c014180d200305030300400c0200e001c0c1e86e8450395000c41421010003019600040720b209000109401e0400b0b01020301c4207005100c0c1619100b500c40500388900f00106098500204441c03625505607440e2100d40d6a80704580441c000049076406100b20000404400c1140141d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 778650872 1250 778649622 778649629
    0x318061a03071d090109080d020a020f070b04050a090b2d090c0c0f06071b03050d0203010906210b0604050a18051c030e0c010806210c0112051e0c09 65
    0xc80040c84544450300e1441d4500700b0700480d001001348850f0141e4944110070300043d501005480c4200c000d80300050b224640c0d0340e030030f0385000d0108050341d0161241c2080042e1000b40c0400400959006407500c00d85981c2d5440c0701c1098814445e2301c1e5a0107452002e194070709204200360400ea0002c0c1d014540c60f843c14100100e0302c15602601c8000c01e06c000040c185040b00400c20002c5100c0c10010020300481c6040c200c000c04000d141c00540581c2d25404140c0c2052521420540d5520348842004554950b503c4415900600b0244079054080200283d981c08103582985070b101c0307045d04403800000583ea040304002c02000002c10000361b26075903e001070609124041c800e03118902c120000d0040043d981d04a40000c48890a410201410001000c182c0b407004500001908030a0914800c01c5e10303064000b407800401c40d440000c9520044503c2c140d1610000b441e03448102d02a2590b02d2004101020711040d0761013259206039400101c402070060141d000307805948001502085800c124041000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 778652122 1250 778650872 778650883
    0x9090f1b070606090c1806081807080303010501030b06161716110a0f141002072111090c030411033306120d0e01020717011b0318061a03 60
    0xd40c2e29680d6140188560711242c4120001d0202c9030812241484603080300416105042c00344c0410010401b003c102401e0310b845a030001581d0403002d48081c2030311902d0142c0d0301e400911039640000e08102c14580282894821101c5000300d020312080c0203501625407141e409551511844000400c01ca6206c41145424200c101e0302d119081061080c8050380401080054a4001c2c4a404070540d108118a41d5400c5100c219080259602030240c842c998099041c440c403a4883d1040081002c00580641031210325202d0180c400c507804117540c0030103024049861011104182200c10400105010407008441c03041044001411190301b20360040c211019031100094442a06808803410b04442c041d1740c040b1640f200d015109441c0030007043c5105603880039012020018401d94002d007141a03407082c800ca00c0501a100d2040745042850300c10b160092200d00d0104083c0c440c1c110290a94501c1b034043c5403100e4001c0d030590100041503468030701c0200007403c88911f03245010041c502c010384040c4003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 778653372 1250 778652122 778652137
    0xb0a170c0a110105070219020402090a030f1203150b0d06090c0c140a030c03120902060a080a05070804210504050406080d08070206040c0303080403180905070e0609090f1b 75
    0x40c110344035806040c010340402c42c00c1c4031080080e41031034104101c40e58009946105840002e841862900d003a00100c1d00912640102c2c64204202a0010052200b503000c4882414420141406843c0c40007004070119214400d044640d22100c07001044451a56000f62008410b41100001c0707d07596442c100d822580307490108004145000065000c1c02001e1103c0c500d9280400d0240621060302c1e94020418074940b0002410b012801d14200244509940a50421503014020594031903820324090030070082110b1a04200e0b00b49000503c00600c1205401d0069030300102a43c02c10600a0440c2450f00132207481100304003060100058580c0e40e40500b100414000e0b000e440b80c3c8888800c002d10510000f032043c8107540c4440e00f40000160030719140c4084a03090710b44206030b9191860101c0b120b0981c0300b50740b503503c800301c0f0303020034000d0540d80f1203030103a0f40c00c0c0c9444841d5400d0b401803180c0380c0240f205136a4403031080c074001041c002d545400c0c85d03071100b074181419141000c640d402080c107400508 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 778654622 1250 778653372 778653391
    0xf1202250603060b09060f0f040e28090f080d0f020f070209090601030f110f120c0f0307030b040605060f0a1409010e0103020f040c020c1804050d050f040b0a17 70
    0x1040010a405101e000044c0040c0200ba9180139140c002042ca90b203c0c4081207250b0140c006110307854018100140e07070107082c0d44a04407400381009078800400002050349080d10858007010042100c0c980e2040b0107a05610184a80c6004901d8450300c140b0340001c600780c01d105440ba01080500242c5200800e4a4000807206607202e40090050000003c401454000650b00c07080060002c6428401c803080e010b64441200d40c003d1b18448003050609516004840e0409e6641d50040900080400c80500480041d5150041e120f00d140400d5500c2c00306100192940510b18042404191150001548200c01402501941c0c01c407501086041d01164002c0808158070982c0d0381251509103042401001003030900155941983c00056502800e040030910581d41e0740030307440d6290700911603004000c60043c907030002204805100d04517800e0440303086880d8000e16080780080d90080042c0c07541c0c1c24112a010303081c0741c10141c0714801688410300a5082c441c10b0b620904c1c07401c03511900144245a0794 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 778655872 1250 778654622 778654693
    0x1e04200a090c18080c1c0c0b0f031f0515070f0807080c0606030c063901020703080903071e05030424020d030c08070e06070b0a0204061107030f1202 65
    0x344a40140903c10390000c03030068001001c18649960f408030311003924252130b98213031810141450002d0001d8419400b0900840e4080f42504586900c50050340c400c483e030511488440c140c0689082c0d900d082c50041c0e40d80002090300300e400b5400020090302070684510070050740c000c4162140070700c036044254104c4615000242041c940c4c10144074850700810190002c009504008001a807a8000c10360905044078100003178050b100070a0580f40c807190800c0c41502141d00c4103886180c042d6001e04016008185040c010810b1500c000044400d055048150b003054106d124180049584642c3c400365000d105c18080861280f1483d00341801661b4040202020319070802000390906c030f00014094207142c90000c0045115801c06000d81d400041850401c20100350200025994011404042c1170070042408106c00d46004e0741c0200141e8815850710341802c2c030350707041c1c95955560a020043c43d240200b240c0c41c002030880020342d02d00b034996006079900d004a008807600041140184005d401c2d604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 778657122 1250 778655872 778655897
    0xf0f0b10020a232109030c0616020405091c080a0506010e310212072d14070b04031d010908060c030a090206121e04200a090c 55
    0x55200200c00d44450010304000e00e40c0340c6a4011840021107004403107180120345aa65641c01e1000c111074038901e803980f40c088024400e07482041d810a070171190103441815441c65071442d04074180c4102942c41c152403c404000303642408064140034001f0b03c014171901d19941d00d82504903070442c5070070742c460740c8541031031130410502000d403200948001d0600c100554511000e46940c0c9182c1b90104111200b03040c2d001171a81c5441c1c42d0355a1040001581d4404100100d002c0405145240241c80700c0e5100300e40c40e00ca048000e0340c00120b041c40500560228481c0022080c01080210384500a00710018109200e90b10741d099809030407100ac80c0014200e001045866102003045000d50401380f81001d2000c0c101300c0c00680c0d89502406c01600032401000250310100ca503003000e0541580584042e4a410716201e1040c0395034400c0e900c280c2007a079401840d0f500f0600c40c52200340300d03d402402c42c0252500712482c0d0324149414104468000034064000300d4024824080c0c0c00c2a0304042d50f490f81944030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 778658372 1250 778657122 778657129
    0x3030902090408180a0b03180c12010204080609010606091406090603090f0615031b0f10091415040605031e01080a0228060f110613062a0309060f0f0b 66
    0x90b280d441300e00c6154240c0d414842d800420742503a9008244100384400000001c0c0400d140c100c5c00620680d0025145450700100e04043d0080c00c00c0f100d01c40111107241d03c80310000c034265003490096100113013185038200404040441045291603002e040149085950004140954801c030781d600c1c0d0690050a035403240d1b62040100c5980595007170b040c03d4031101c91000090300c6445072800c2e00c112017040d44280c80d0076600d500210340804801001404521141140540303203c00c81d118580220004010101e50750400a00c0886058041010b01d8503083c142a03003030fa103613000034044124825503001c418611502a8000b01e0107840e40310300500c0310003041d20402c0441032040060210014120086206244400000e01c00f5195281030505950030326800072221100c01c47c41490161090078203020100e10580540c21080340200070510095000c440c4025020141805041c40890400c40000589129901c00042548140c0c3c010031415004511541500c411014414400d6a150003201c668907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 778659622 1250 778658372 778658407
    0x4080d1109090a0b0f0d020109050301090b0402030d0509030a171603021018020f060a110102070c06110a26040305070f0f120503030402040c26042a090903030902090408 74
    0x44a03d401d000039003c0c000810659030b420310782076001e00c00c410401421a030048040c40040d0001030700810070076a01c1d040450354080300740e80c2607002e400365024803904036215004851041d04003400422150b0395960b031b43c0c404120400c02c500442c40041c005502e5000a840c0b04449190099009004145091540340e003290303650030740c3d000030b101e1541d00400141c42d11200c488000300c0454606817150b00001017a00e480440881e27420741d43d44005207501c100400302c0d04c2c01007a9070869940d5800d9032030500101d03603194060030300070b010399910a0b020542c901b4013041b2070010540341c1c112141450760700d0303489070b01c1c043c081c0d0070481c0f803010083c0c024860a0016809900104504020641c01c480780745c45080c0c99110180c0042d00070390700c84808a290074010f128050140520342d1070a0041c0342d00d44030380c03e07030194151012103412058a2040791490342e03a40d0507415071a616440203850603e804040b0005014a96085051507250596000541d1700c252265100b140641d80c410b50326041ca43c1d1001440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 778660872 1250 778659622 778659631
    0x120a0b0402070201090315110c0609010f050c18060c01060e01090b031f09020d020a0311040b0f010e06030624251703060d0c1403070f081504080d110909 67
    0xc034818007402c0d0150303920101c40e50460740c1094002400b6003410080c0000f03040301c4c2d500000040340000301c0c201201000580e1503c12800301000b0030040031000c86c003d00340c0308207648101030004180070818901140f80c0c040d5400324001012140348c0180d00030f6040c00e55456a01403d01d0443c8400100246400b0723015070040040c0450250030f0012540003060405c21603891104079240d07540380b2490464130340c02d50318819590028108550b803507907494005102101d803080f440c01181031036110026030070540345500c03100c08140c4401d1070400f0303a4001c5c00b9081c0c0004107480d0780608205030401100070300440003809a58100c04d090781d98404280403a841c10001001c1d54144e00c01c6070980000718041e41110b040c0024410480c0c0c2e80c0303460b003400094801c901888082c1410460385400105410a82603404c00f1600503800da07040c1c107075920a03031380c0c0144c1140314050603034024141c000e0114038001c1c8250390061090328024288040c4502c54011526182400d1859140000e4040210f15028480e507510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 778662122 1250 778660872 778660879
    0xc05090606041e0305100603051608031801020c0a031b08070f0b030c07050d03050601090b0702090402120f06010e07032901120f15030c080319051e120a0b 68
    0x541003600201d001c0303104500c2480c0400d55540100906102c83c2d50b040c00c000e5400c44102c6040001051100009142500c0101c0d451300c01c0241098002c400d80034540b04552420b40998100182405d04450002004010314110f0040c4148508181d58007100c802c091030044400717880c0e00d4540c00c0300d0310844007143c115208d030f0741c000d18040000350449480c20741501c180390300083d282c1e01c030765220208134000c021008080340104804d14402d07650581c4818403542090383c0e003d0314540e07500b035154030b42c5c4200702e0040d42220003000050058104412321800070703552078081341d051030130a8001d20304144003a0424580c0a0b0720f0b100740500305901d0300a44400650401c00d9980a40c0c2c0749080c6c000b02c048003000319041c46100100b5900c81170140e405075440c5003a030034040c0070005031040100c4aaa68601048070079200c84070700481c0c4102c0000c1950300c0e40620840d0f885c0319a40c1d1910981769500101d5815100d407811000da03070207920600003e40800d5030080781c2c401082c00c1240e105000d8a08202c2c10600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 778663372 1250 778662122 778662139
    0x417060f0408030703090f050d0e130605090c1b030f0703030b06030609060f01030e0f070f080c060301120c121b092c01140103200103061a0c0f0d0207030c05 69
    0x1c80d0003401100e40013482420300240c1d040c07040c03601e114035106400b00501180101ca80768070b180d681100c10481c005104a511014000060403040c08030790035030180765003146041002410781142c0000900c14600c40303001100d0300c0c1003601c1d02140355070b0001d1141101c12101064070820541c06004444050b00304980c001c1c00c6281000204450680040802d84501c3c0ca520307149940340d000354452540461801c080d80e00c110b141c965420f0b0740d4001e5110760890041c80410000e9224404212031001d00001425240b0b5a46422141d0050340300601c070030fa680c40d50005000a80e00d5645c0d156070322051180380b4191814103031591100c401e12b10343c1d1207040c8083c01c00182d80d102e00312400100c5a50307100303000c0c8146411860000c01740140030015820103800e13a400008005d0000000100c3c02903c45400040c0f02000c1c1d402c011010344030070f886848604098124507100480250000e400542c10100c00c0f0f44e07070048890081807030224006000700150708044024801d100030070408002500c03055600c00d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 778664622 1250 778663372 778663381
    0x706270b070c0e071719090203010507230301030b01051011070f05040e1501150e0306090601150905060f0702030a1719050906070b0601090305030f040e0f040312020307140417060f 79
    0x2117442900900f40000c40030440420304003c0c1c41640103500c4290060001c028500d00030710f000c0c0840c03000c421030030144c00071032641d5070410b03c1d0101224141ca90000340030040b80d00c0c1c01c051101b4001d0b28201d05083c407440000c0c4240d03a80040000f44010401200f51050301458101844203d03010a4400241c9400181c54a420451481d100c141100d1800c3c00820750013101a004460302d81c0f815000d29810f0180009000110b03100203106d5058440d800c14280d844444800192100c00f400c1c401c4035003111040c440d064182e11200090130381103002409903028809690f644010b8000c500440000302113010400440a0000518511908000f070510502d41845240094214050024010083d003607810000b01d05900c2000e1140040d503200080b251a61042c01891601d41c100740950341d143c10300800000c10f2070b00c203405682e000750f4258503801d0b001e5054607100c4010b544000c00342ea081c4424608400d2041d031445000340003c0c0281064115401c03803402d04503060180142104041000c42c0c402e10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 778665872 1250 778664622 778664657
    0x50105160f0216051003110f0304061d0c10030608030a030c090b07020d060f0225050606011e081f0617060d03080c0a020709020d0902120706270b070c0e07 68
    0x480c2540c000705c40b844600f0b215044224040e0000c036001c004190b02c081181004040d143c0b000c1c602880c4201400d10440c030905c040d400c0c41c0940d0740e170000d88541c044030413054a401c10061260200c1c0b5030380303008a070027030f21050000d1035a0300403880030000a656040b00410142c0c4204a038002c0e2080500da9441c020041c0c000030b28940440c00d01908007603035802510717400c801c6941221001c5441c000082c05012044040300001780d00b0f448144c1d00e80c00780070002031056209680085008404100e08600e9508405d002c582d900320080800e100c50755150712002c1c5100c544102c0900612140d620317040041004484c1b00140c6c80d0140c02c5500942c85d555515002a0308141070f2580305200e068090341310440004201c3c40c1c5003240e4445404544001440b000c0c0001d641c1007c0385d0540281c85003000c081501a00c599196600d100d40000111030020380410804540140f9441c1c8085034100a5201d460f0b10140280f54454902101d00d446c817901d08106100c407403030b9496401003e5090010b40394414040c42c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 778667122 1250 778665872 778665913
    0x70318060c20010507021b06040e04030c0c051c12030e07140102011d0a240504080705010b2409041d0d120501060509090c070b0108160801020903030a08060a03050105160f02 76
    0x314005507c480c5101c1581c1c80c1d1600b550000c0c00468151503040c14941806030410603020303400d48600201580c041220b0902d40403500a254400b00b07520b022140703945800f80744044282e814400c054681b1001c51100c203040145001401c0c280540340010319074003001908544bc0100111281c590450f4031300001000400c0107100da40e007040c0340c544424001c07003050304d00011038040c11040a10f004244004e2144e0100030b04107583c41103000b00f040312445000c100c06414040c00301e18499a51910740311008807040090b01071540f000e04041040d9a200590080204055a02400b03e9104142c800125507000450900310f001c3c09800300801c1d41004030040080c0720315004c0c1030052041a000c11002025001107039611508884400080d51b165501e0030b403106042e20005546021016010a208206200710350380114020f0082d45000312000782030301c880a00800003a07012883d608008007007802801803621944544058282c000000074000d8110840c00c50800b0441d031207098240b1817407555818 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 778668372 1250 778667122 778667143
    0x7080108190f02012006090307022e0509130203090c040b09040807020607030516140606010314010e1005150d1103271911041a09070318060c2001050702 67
    0x811040031720f182400003180c0b07401d841800043c0e200e24010842071010110140204910031503900c00c040060001c03a401215040e03151584022542442c5045180a0700080075813400140002c3d40615254645e4000ca80040380e240010750042d084658181c60684142600708100f200d24240509050325501c50701d00404030000e01500001400390b00781070250080c0d4901c0200c1c8005940c1426951a000111032643c402c2c420807441100c0100c0c0c0307650300901031070000d101044000c070402c0e883c0c800083e0001d103003e020102c10b0b04a0f0400840c0d26158190010000e0f6008101c2594404907030b001981100c01c1718964640c41c0c0001d02c14055034180f8001c0e0301c103d400101014280526141000e1030403c1d40390340c03c50003038807142c507031a4041054107056080036405c12981046a8981c4004c0120004000a0a06c0d0310141480000b00c540c0d0080c1d003c415080070070109840c0c030700130729507c040440764884650404660020181c492101400c040002034100d42d000a2045046c404400395681d1550030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 778669622 1250 778668372 778668377
    0x3061e12030d050f13060504060b09091e0615011d041d060609011202010f0e131e090c0312030902040f1e0b010203040933082404060b060702030607080108190f0201 72
    0x2010800b27025a07500144141000104070413424106242c2e51941d1745010b282c0c0164850346005100b041d070a0101c2c01070f00c5030340017401038140801c2c441e00440e011100c644d0420b02840c010785001f8250340b240d110b140c00d0320750004c2c1c1b00d0344005043c1c00c180380b0309071000b00030301d02ca4280000140840d24032110004281542803c25079050b841c144000e5442c9007020560740d4102100c040790315030502054120040c80020000c1c000f440054201e00c0f0f500b0b8440000f800740030b185120400b080060a408503510142c1d02d9407800240342c98183e80081c0540b902c0401000300c10b6286c400540ca280c080081c4002da01407203500400c400e07144100082e4507405035210b50500039680c0d07007a20a10903113004091040c00b410490b1400d03040003904810804480c01e000d2400d0320301c525500c0904a501e51314910043c545020300000ca55525070f5074003800350503000e0301c0580080d0305200d05001a01c081040030302500c46a200c08295604080981c2d103401c40c1d0000700c9000141409000021510b100b8410710b1140d02071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 778670872 1250 778669622 778669631
    0xa050a080d0f0c030203070f020c060415020f010509011a0105120c0d0905100e070b040605040b031504140f0a0207021c08070206070f031205070503061e12030d050f1306 74
    0x208118001c2c0b403168880c010321400c0841164015074140d00551241d0120384401c5804206548103d99545480d07240b150400c03c100802c1c0b00700743c400f00a000704a40e09204441485d0488101c00c1d003520020b0f0381044850391184030b02e01c228042800440c007403400070310300541012510030300c201c481c0001801c0030500d0a0002180c0c40411030342d400c40900706421408a95502c40c244000500410200c40c207a141da00480001040354402c400444089824a95030a8205810711500c01e20541c0080c0004030450040712210f2925102ea0291b614200c3c8400300351603003403500c0181502501c03001001d014825104000c418016592031040c240d07040510000807086854900d40201c45102d01e00c0040d41c00140441c4000c01c0203886040e1803000d038070a650b0281c00401158040040d610180c411401103030081c00015070741d00b03041102d00a010044402c540c9907102090208164007840c0d044103045400000301070a01c1000c901903030360001402041c61030a40341c0003000502d501c00c0c0700001001942c45 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 778672122 1250 778670872 778670887
    0x1008090d0c060605061308060105040605010210020c070e010e09061f140d02060c100b030606090105090916060e031903050301031209030204060f0618030b0612160807170a050a08 78
    0x10b40e0020f4060480948240c0d0365030684060200d003081c140c41106032074071600740007003141e05141c02410112107041c4c00404c100701803516000c010b50400d810f0b11045103d41d03800021001d008500711402010307000441c480604000003518100a00140b051060300005030100b03282440000c030325412500c22200b00d50004800b04001340341a03140402c007a40c032070404140c841240101007001d001d0500103401c00c00007060414241512680d044482c294010f1038400104114280310141c241d00440b02001e8860001c3e041c0000701032502c1c141c008000080c0020f1201c0c585040030420308403800c0480070400001d03c03180d50000c0561205003c01821182c9004280d0b880c203000d91071440c05541c1c02802400015160b084a4048810500c10300340001d07107144500342c8440c41c140b160b0080e030303070001d40ca5040ba541e40003d01c10003c0941c003000102d8031031414a12341070040145180c0207400d0080103020281d1a00740d404180301c00c0518032003400c2c2c00c100f910100184000070300ca0042c86d44a450702da110484e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 778673372 1250 778672122 778672133
    0xf0608060610051b03121501051608070605040b0a06081501031212020f03100603051003021017090c0f030f030a030f0e030a020d090f050d1b03020d111008090d0c 71
    0xb139072190260000d901c1820320f65418000c40038005408481803c0d08440c1c0d2030005032284000962102c5021407000c00c04040301480341011260114020741c0703428a80462503581e002181c4089500307503042c0440005110408030b45004600041011900808404501d145203240d14841840b0050200c068000500000c9024085403141c100114504540303401080c0d00c00d00041e801151941801c101c680004680d050080c45654000c4401d450707030186150469003031103420495801120b051110a09401e440d020f00d103103aaa00c00d6544c140030308012901541031000c0300701100780700f900c01d1300404a50b003030300c0d9400000d0703c003052818600422170b40c5800104400405034100c0140d06400005400c01031070ba00001d08070f84440c01681c9041d0800d584480114404d0b00d54010f2950201409044001003440c40640d907045021070241c10000580c0c6c1d80c0019072032480900300311070804c01c006520f40239142a07072403c414038006041280342440e111003200d440d41840c041d484140f142d001d03618400d010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 778674622 1250 778673372 778673377
    0xd090203070b04231f082716050d020d2004020307170a02090a03030c02040f021c05090615010c05010906060b090f0307080601030f1106030c0309010f060806061005 72
    0x2412510043d0344645407060106a9002144c91800030300b2020000da50b5030908a001210059080d180c400210f50340000460781210042c4c094489045000700404004103410400000010311034010003482c103c0313070211038482d0f42560000344100e400b08007113030150311903500001d50168020b92410300c26074020b0700900c2160080030529001440841006003160700940c5003040302c06001070f114803503920400510281c1c8034428240745c1001034040304200086c090210f4840ea01e100520225004030640c03001c4007281c22049040c03500510300e20428482d400c0c5c40c414140c0016108020300038034500300e598486105100d09449040041103100c40c0143f20b020350100c41032640c443c07400d004036540c58209401a8002d400c08900c80c0a0507050706d2124a00018103104840c210400340030302e81c4c030b15103030340000300c91030300302515410144074032400e1594810006500c601c43c030380d6903070b6207905003030310414210388145020302c41151030300105001070318000a600d54081d03001c0320166000809010108c9450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 778675872 1250 778674622 778674629
    0x501080c071a040c0303080609101401090503010f0203060a1e060c0203030913150e100909021203030406090b01080303060108010b0a0210110415051201050f1810050301180302030d09020307 83
    0x1e80c101d0003800108424840c042c13048034003a6a60244c0c0d521010100f0034203182c02d880412000c03a6400040021410001c556000f4003030504007580c40a0f03850700403a003520131401411720304990020412000b85084610000603116580025520900c0c40c0d0520328044000e003e1102407150b1aa01c0908560741041100e01042000d415010300c030340da00384040050309030280442500a0741c0d40300450350300408001144640549034900c0451031920340a0001040407c1c000d98100741c40d90304094003560b0810065020328400ca4002904c4001d604000640d42c0d0181c1140c4980c0c3c0040080c40400c1e80d002403003038191030b0b42c2070320380340c1c0e504074450140e1400140799a806662800c0c8540c1081014095001c3e1044a152008440c0a091078020803035031440b42c0204600c00e0246000180601d080805007a0030041024160f410000b2024140c41e0481408640e640d61b0601072080c1849030341000e0227401c4803d90304c2801d440701011599400380d100e0084080990803d40c1c0c904491042d5641000094001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 778677122 1250 778675872 778675913
    0x302030f0d0f0f0e012313050307050d020309101b02130b03010f0b1504060c030e01051218070609050d060b030304120506090c0f0906010809010b1c1502040501080c07 73
    0x4440d6010040e00038002c44903c00a680d403a240c10b0340000c0ba10420341451b02c0d15207494490b89030380d450000d0b6810043c10202a101c510061000000045d4204025003036080d0540040d511007903014104003070051002c041e00b042200350743d4400c500980507480061207913411201d800307030041140c6d80d00c401002d0340503049034075600745204018100c0c01a0b01c02500e40009440d00c0401d045100d404d007600c1d104920400d00090800c0350b00001191080001894100052401070f1030001182003040f2211801d884017400c014910750f9044031501d081122400a04140c24840c002d2860480055004801e81802401c06038441e0039003241960f0500c200c40207030902010148203da5141445607440508544404191160050403d0b0320300d04480fa03545418401082070030540c0c3c6400045842400190a14030150340b1030840b84115a2250a4840b10784e1070001071360303440d00003420700742c1a800001490180042c4100804d201c07699219506507400b00c030398443c0c503030340795040d203018005c641d03449409090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 778678372 1250 778677122 778677131
    0x91403030f1b540a0e04030c1a0411131b030b0310020a020114091209220c050910090f05040903110303010609150305090c011803050709051e040302030f0d0f 69
    0x16034015421443c4881004510110061410062020300c980c41e0080403510341e071100004002030701c125440409503201d1b82c844800c824140040082c142c0c8291070868004c5034410460005080885150110440303201c414080b4010824007104a115040005810961100391240d01034604000e2401c5144040004565903c0c582c48000d0085c11010882041c008030103022601c2c001c0c0004032940d0441d043e4610501d8003020104000c000220030618148280c00d20b50b45001024040c843c50b9a0410790f5200d865075000c046080016103045031032004148003c9110602c14a40440094070544500380c0d40055045824107040c0d43c181300028107034460341310020000c944954090503020444401c0c0540c01d4402c0e401442c10740503a501110001d800354007900450340258424500002007040404403446c16075265180d40d4180a41030b00180b02050b1241c0502440031650144401080a150260b00442c01e00d40e6000307440b481000e403a40042000454544000c0115030700212114196510411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 778679622 1250 778678372 778678477
    0x702030717010b03070e0114010306030516080f010213140118090603021302071115130303170f0610080c0d020426030f120406091403030f1b 62
    0x1480d19204601c028030781d500301000700c03400c1d090029841c41079500c0340080c1800e0743c1c00c251100390740d460320038038990406450781c000002044003070003020710304200004426811400c0140052900c40500c0d803c203603903841001303000300c12100e1014100544280241d101d02040c03014004171202812060081e0303c807511840d00090382031a030341c0560100e074802d5569403200d40c001b03003905049019280c4013501480d502419850645490f04600e0000b101c2c260503a030500040780d02c0071402d0210b03600102d011a00d2508000000342440070125032094001c0034101c450300d0141c001c2074001c410f0064481c140f02c107140208101d911207206a40e03e51701894421512180e032a0700402070142c55802e6900a0f41d00d61035401028040070048078000075000404900d070149a80b0001c01d00c0c00e005005440c4981d9580c59032000500812001e008a401c40c1d00850701c9040a580e6001c032413030080c14102041c0b5a00a202c4510344c03d40b000e8602900b00011418614803200100300c0415200d44601c0003c5203104020a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 778680872 1250 778679622 778679639
    0x61e0c021f0c1506030c0b0d0f02030a061a0a0f0f0215040804061701150e120a0c150305010e061e1504060f090803040522020724050411040e0307020307 67
    0x859018002c460150203890704443d50003c81d16139001c0640143c10320310046c40004100310080005205440c4000344031003040e03a840b0226042034a00800d030640741c8004010308210711052030510500032a185280c00c5010b00c0103004819080c40d14420b001851042c1030b4420300070f0242080c2001c1120520b4110300c1c0c2458940c1407603000b80941000b003032420100c02c1c0e9190226116505072584000003401080d22084242c4603503200450307547c0e000d103a041d490000131400b8082d540402c1d10607480d2a080c5810501d10481c40c9031254209000c041ca0000104120315600c60150f03040501614003801c90140c14100d211014610b03020550020400e441a01820100c1e5000380111103481c0c0d5410f0030803100c1c21003142c01e10315034441c1325135540c070901041c05180f03002503041c8410402c0000c844890700013010010117980050714195194072058201c4071000040f51015030182034490420421460b1031758500b65a1080b100d40e007802507a4a01e039160318010208200c800c0140c00904403042c050752000007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 778682122 1250 778680872 778680887
    0xc030c0803090112020c1e160b0414031c0305040218070216080a053a030606021029040e0102160c151709010209101107061e0c021f 58
    0xd0b40c001850b08002000003d0f103482551104021240a0404c10004041c10741040c840380c2c5801d05c0c140510041d031080328200d10b04110040140125042d140c43c90988401c8840340042540c60094129140f4806400851501016140b9050600151540711030001c01c041d8440100c2c079521041d400020310001580000307030791442003040840140910b49a030070071901c0740c895500082480d8840c002401e400140f000328054450500054403002e020040230400c00045000154004266507010030302081d60b040c0f00d42d403024400b10000b0302111076410b00b200a0724006d02c1e0084494141c0380f031004501e41d181c0d00200c1c00641454001c2d91614002e207422800d011044604072101a14528002050f00c01403003800030b000ca40c1d0311130b21000480c1007102c40d10040c0007002065103550070010002107a442c100003852081d960766a281640002114992038a54660401401d1050705810b00383c1c011a1603500883c403000500e05140003010350f1000c5850325503c01c1341c1c0d145160b9100203141c50302e0b0b4040d0310b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 778683372 1250 778682122 778682137
    0x13060f1e0305150f060d020c0a020301050c0c060108010c050d0c36140f19030c0e180a1113060e09010207054b0604150b0f0a030303090c030c0803 64
    0x244414a06400410005218000d42c11135400001c28030030b480c2d00148581c05007160244c01c8054518144051380000c0c01c44201300e4007501000404034074650018020400103002d0302c680c90080051608900014000d406546507840c4156190f01d08045000d11a84588a6030b007602400c4a00148540d04208108036080000041e9140141d000084d440607401c480c0c000c0c5080a04601064115202071200a00c0104012084e5034120071002000506e1842800d0081c03001c848a2840d50500c803078000d114040f00510160f0b503a00c50307030300807000c6808043c060722400713030403038902d0041000c8416407805816546c0c40300c1910180c0f04104a41c050043d00213055083c401d1094416441041154a0b210710007054007069030390400d15040d14403130241440c034008551105041c82c055810200b00e500d03108084800322030321101c210341285040d1181c0524040d006080307500706c00340503e0001140303109409220150400d500c5d01e030707130105000208650402544d040018941301d00d0312002d8050340c90340000b2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 778684622 1250 778683372 778683391
    0xf101106010602010c110a0b040b090a0b0702060a050106020d020c0402130503123001150309021f0305130f121112181806040b130e0601080601060513060f1e0305 71
    0xe8160031960300450f152240341c0d23000000c07030680e440b580c0316000c00d440014621101d038801c0103408401310b2008059103100340b106600400d4140f4000b004c1d02d0a444042e0700010039913000c440c0c1c0010254010070351340b08480d800d031401030320740418280c2290b6800c103030340c0a680c140c001d0104002c02c140c407140041c41001030780709001007507120010303080f52a89450409191a91080c100500020611312100280c00d181450f020860109540000b110000619890090351000d00d1480a1068060041d80c1e4011982e114450710018140c45041d00c03194034000052100500c3c1c018104074038080d6682d0715030201c441044951500036881c041106911201c014100107005c000700040c14540800002d10200b14a88080103a4940c10305000140050f00c0100e580181c0104d004019900300d40305605050440800030300e41c0c1e500d040c1c00759040c02e03010703040001041000c000412941019802c1d0030704860440c604564402594003044444200a100d41c2901d0401200c034200041c0e410f4010a0250321450b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 778685872 1250 778684622 778684637
    0xa060504030605011d01030f0302100614040c03020a0f051303050a1217040c1413020d0618092d080403110907030e0606280b0403120804020f101106010602010c 70
    0x25011400d14003500b000e05c0b0104910400140001000e520022184a100c0e0040b00d124000201c480025546036402a0200032042100a05d080c546402070303201b1490a41000c43c600700c1c045100400345401d61001401348040040d80004c000c160b50075000c02541c00c03605480c04900d00340303000009102208644400518070440000c0414a159096401940c1c4800420186071401e10100003591400d003100b0340c040d80034a445c01c880046400140182c0d00d426000044141c20549810100c0803d6030001c004545808001000581256400348605107003002481c4002035185600780c00d0b40350301c41c0c02440140041030010800c01e035650b1021001004481100140c0d440752000ca040f92070b038103d0340b400c40d07001e8008034034a424149000c40c000c00850819204443c18a0040c10320040940e004000c442000107042080c40009000d00100c3c03a030380d1801c3e1034070342003d4000492401c500e10503d84a036800f800c4150760640104842030382941c041099440541c0c0d102c50290003080c0c0e01c0c5280b400304401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 778687122 1250 778685872 778685879
    0x305120c070806070e040f020903010903050405120a080403060203040c182901020709050615221d01050f0d0b1501080a0903051204030e061306090b030105090609150a06050403060501 80
    0x1040d0340b0720030104c40d13131404a29802e0340c0030071020301810584c641c100b0f5420050050103407400c2c0200b410441c0252181540e5034640802e0101054012a40815603000581c400300010f0a010454040ba5006007015886e40c0325401c06408400305a401045c1c4084d100c44034104003c0d0540081101c85812610417030a404000208103841c2c001c45901ca0040c3c0000c60140140b100d40e610403604440c1c054030ba10f08502a2041400302c070b5101c0c10308286801409001c5450034002c2c4500b200113461201c1d03804003040c9402880c0381d003880d018002c0501c9031082c4055003c09840d148014403039940c00c65940800c9090071400e1000500c0310001560000e85960000703000c0910b00d02808601540c1075a603249062103042c1a0f0908a4002e0400c408200b041c40e4010140d075500d1003c0c0443c4441d071100000964604580502000c1443c0c1c440340b00200140010440c43c4e4075021040c0d400340d82034800c07401a03039501401e1a07030074071a20991540481c0760039001c01c0041d4001d000d0419a132086104016036600d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 778688372 1250 778687122 778687139
    0x70501050301060813030905030f010509070b091f03090b0c030a050105060307020703020918030310090b01030603030509041505120d030506040203010305191b150f080108031b070305120c07 83
    0x34000c0f080851154400300701000a806950b151031406071401c10080d41d1174600180c100501c80048413016915a402d001c84c2e0101880000700410f05c5880361071034000c000c1c1c08070325141e000794120b01c443c0f40b0b1b40c034442c0c0c401c1d0b01907003101803400d41c0001900514913080034040a2900180c484042d040d14000021815080040403a401241c1c02c0c1c0040501502d50740c2045a1402e0082c010903040c00101403004803101f0410145000c3c01217090f0002d012800c080a000844040d20707a8641054100b08040002c0380d0090106c840000054901041040680c0b03640f5110314060752240360086a1000801c240300381c0421207000241e41c6590a04c150384402c802c001c04e0340428000039100790066400545041e03102c0c00000000d521550320000c5075449d0200b915010356066101c0082c1c0341401240f850942c1c1d0000d070b40410410705050080842d410010f0180d501c2c06400d614508959603503803c22810903041100d80010f540c0042112032500c95100200c0858001a01c003c07071354400c08101240002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 778689622 1250 778688372 778688377
    0x709030b16080a0e030919170303040c090203060609030706050c070608040b22060903020601060e10081b090d05010b0910060c02040b04020409140402270a0b03120406090807050105 79
    0x110340c0e640c00d07410b85426103d8002090503050b0040a44400c1008040320344130001102601ca40460080721050700d060207407c0c81c01050f603400070554000b00200130021703100f1502d50082e6a4004c0300162079071303100d9000c5101d40c45801c1545605105401001940341e52240003080303504101419280c800e581c500741640d1000c0c1c1960001c01100800e40000c00503071394448840030054622000c0c0745601d405032180000c840105070186c0050300300d580140001d40c4c00c07200440d00300900345c5040f10202d0414400400c00440a4100d60340101003040030441d9048502c08d0b1548400c0c02400c64940e0100b40c80e1031030082450700308481c043c400d00000a002940b0f04d42011084594a80300d500e84050542e00300300c010201c050a203a0b220303a082c0f1002c1401400d43c880c40007280c0c0004044a802d05050041282d4607441443c0034000300c0221004809400c411b60b4a146c10840784000410a100c0c0c0f980041c0c00c040d861151001c22003004100042c007207130f01c00401c0040f11010f505692131203031603100444151 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 778690872 1250 778689622 778689661
    0x70312110a0f08070b010906030308070e010516030905121c030905100506042c060609010f0b0c0f06100609080307030801050d1505160801080601080c10020102120709030b 75
    0x1038120340c400d040802c803810426080a445100011311301041d07565650700030b20082e0414040c0d1680c400003802019009130b41c80340c0015140c00c02e000704001001c0000d055201e0030315000150f0704852140340415000340c08a02c040c0030300400c11101c1b1003090003169511591807a000180080042500354580d00901c00d06200c00c0e0403030043d0600500c00301501010b01405481e4a400596581101003910f2002e40f071286070382206035200c098110680005454082c01074542449030b4401401001b822032184070715800c440c48094140d8807404ea054010f414402039401f40b00040c012801000780800c2110340240c15030788962240c11406407100c040079564042c4000040214031050014491391400e101c440300d140d882000c860700e0f071031b000c04140c9042d04d8054860415001c054000201c0c010b4101c40614058668000100401c0d8984141d90b581e400c010741d80240295000c21311110308902c00c3d0110341da0544207002c00c441e81c0c00d14480007030010580b88020385580500b0340105500300500c0e46a007240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 778692122 1250 778690872 778690907
    0x20c0c21070b03090a05150103060b0109051e010c0606150f0f091202041508010c0306050d020f060f0d050c070606090b0a2615040b0609011206090215030405070312 72
    0x201d80c102500c400441e4405448040d4600c6142c00c0c05000401c20041002c5000c4440f515001c00c3d459450020142c07843d40009506005018105100c103882c0c84c8040300040782d508407407000328195500181c444206051024001c10304001f404a1450a1021840c00c0c00d12195100c141001e04d0800403600500303604504030010b49142c06c10400341e110340c4141d8454500003000044d0802c107141e1007412090751907002c403410f03944074032039004120b8142c8600300040c0360543d181d07141031031507a0008001286010940d84500000300c1c07420001d074a02c1d401d907030205000102c100018289100d080e00b03d904500b01c100c2c0c071103007070501c0804c00c001d00d8020f00354098800340c0341481d982d040010b49400c40c031000d660745161002e52000303405e80003000c005145204111803070f400d02d203042c6414140c01909000b841240540130840041040380314407001800cac0a6000040018240b0a034800140b04098410701548004004030910050150100e9084116441411031716000d005485054812801040c0320200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 778693372 1250 778692122 778692133
    0x132604090b100c110d08190225060c2006161e20011115270703080306030307060905011b0201151a1207090303080c0405060912010f020c0c21 62
    0x82c0d17040103a200c200a61103501403074100626140e00804819081c1c11000060f8021002904490006000060a44c8042540075107060601e1030141000031001c500409260007103030401c0a04c4140d04844c60503900040400f0f40d10700701c10050300b0a032000c0100c1981e44003050031303030203404891000d030381c0c01e086601032542c0302e5605128990340a10410b01c0299418402c500350503199556041c03001441c40c1000e1030020a1904151441c0071009120001d0350f540f0344164040b0701211040060444116a40800c80f00e50300c1d9600d070040390560141d45801000300b0b0524420b0400c000040d0010a060b2100d013180030b0f056a041d8000b00e084c0e41140305101e03c409034040d4144000142c1074201c41203071400380701d220314103100b08603407005002c02250420001100d44e5824001c142e03000c0380d00d41e0070041c1d50540c1420a801c000c000780540c850b4044503446180c81d000c91442012007900b00c035203103a01c0c040b003c41d10b42d075482402e80c3c0c82c2c101002d4183e106483d440000310404140394000c00542d45034100a21 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 778694622 1250 778693372 778693403
    0x204030b04080a14190e030a050705060a02100606120b10050306010c05010b150c07060504051507020d02040504060b04150e2a04080106060e0108132604090b100c 71
    0x407031039021903c19810402c00110411541c1403c0c8018146074000c859505028a0b07100c5008113081320008180703200c0d8002e4580c072800318900260540c1a150308840795035039000302d28010b900c0c00c49840103210005082c9180001e01a40111458420800e03688090100d203e02908210340c0840503401030010401c240007040880d4810301c0c61058040c4a1000000c0c030000d041b0000b00507500241032030740c4800c4001880d068418092000d032000f01201c3c1080ba08040c14040001d104003600c944000105a0103d801130541d550b5403118041a9000343c0104114285818550081e140340c000480c0500e08000c1100a0b0808460151041300c88aa0400d4000c0c0c440c102109040e0b44244030014000d2480540101c2c51030f050401040100701a8000103103040c40c1c040e0240c00402c000b164507040c0134104041103082d0284804901d4400c0d8000710342500e86015003500c1c5500d40181801440706000800e01040030b500c07035400300c030803000e0131074882c0707000982e442086480c000d44101c020300003451000c1c40c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 778695872 1250 778694622 778694633
    0x20a090b0307091d01031e05060c030613020a02070f060c0f060e0f120c060a14040f03111f060f050109120303061203020d0e01081b0318010615020706030204030b04 72
    0x8540140c202e00d0407255035562034607415400a0940080032804d44040c0c0100304100040688245050500c10701d024034039110345806031a100d000f40302c6503d402c0000009000c654403804d51aa6950800780210f4803101c01d108001d41d203260900800c0300c009001800860028010400ca8003055800b00707141207488003668800c00030b8a02c0610218142c031451411043c0c1140a2000c5203100b00c0007200076482d1980140001d24062020b45030440c07052030602d03520100329052300302c41c0d4041e400c801a0000c03d4401e180c1145e010b88480c1c548070b00c5002d20850400c00c0c40701b280703400c071103140103410600450341c0314000f450342424a442124045001500700700440040d0f0f0b41d5400c81140a42000110180d0702e000c80c42803e91104021001038001c400c1c1b1035045600150304080c000c600f842e02003181d181c800c070441010140c0702d24110403400080006011810074480c071011400e483d5000340211680c3c4c0344c400c08006803116152001d4018028041000c1d48244282d808581e00090400d12648864441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 778697122 1250 778695872 778695877
    0x5032d0106051c0605100b04030318050301050112020315070207030201110f060103060b1c1106070c08070306050403171b07111504090c1b060b03190606090c03020a090b 74
    0x819115500e40400045a40d075040d0201c40c8006646415058062646010302c100c4500624801c070079903540209010303a115001c25501a20350506107002171a10090359004000c3c82540051362542c00c0c003002148031050742d21210707681032080d02116010160300e0340e0f28000c1c0004a40d04401a44034102c1000035610070f031600802c5200c580151040e04028039005d60a204098200380c9240d07460b4a0a400c040c00d0001280c419180c4170580c9442c0e4400994889550315184500e0314850100401e020f0240090360003800000e0858404031140150f403850500c000d400d0803035064000c030740140395451841c0781610b1502d00c03480c58506034a22405074110100019080b00d001a1140704078401865095160381c26000307402074490041e15100ca203400760034410788800102c0314042010307240144c00140d604076014051243d01003c0412420100008a8600703c6007945c1030f03c03903550302a0703918217102069021809903149580e0a00141103001c405500364810207004bc4006100303241c0c2049000078500c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 778698372 1250 778697122 778697203
    0x1002070e06092d1501022d01020d0204140a05150703120e1911010302070206031902070b04030306050a06090e07110718020c06011406030c030726040209010503 70
    0xc6050f4207010102d5411043c2c0300b030035408520203400080c41003400100c4203021099400748000c0c0084210700703036001046010208004c07101154000381c050001003c2d01540c600100702001151204d65032070241c4100905445503038080d00e0046000b017606e00f003090b60b185201314103441c2e442c5840601d640c112141401d20002c0e030005030351903520f00c100384e00510450b20348000c510040842c2070f003a401d102d003514004090060625104008100050f2203ca06590740308038070311008070300307071029076000f9001e881008001080340117502c0402040503050ba200c401914410380d20203203940e48458054409078000e0051510311888030000480c0640f2406140c808813030300d502500c0c66555914218112641c03114421802070360003091004c000f82042003941d00400c0d0910700300f030809803a0408500710b880041e2492912010000018404034007030380c1c240c20703142d0081949040740c11802200d40a18501582c04038802e500d980000202841c00058015800c074480b04001c1c40c507508402d000484106002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 778699622 1250 778698372 778698391
    0x102120f13080309011d0102100e010603060507110606030c0d080315062b0504020604060f031104030605070f030509030301121103011103100801180f0609061a1002070e0609 76
    0x8141039400741d406090100034000c0d00700030340d00c9904e4040090107104000c1e41d80240d000158401c0462682c0c001402054625803040000304101c0105005014241581028040d07606260602841c0e41e0701c44480f0050300c1c00300e42540e203561582010540c9070b82800102c6940f103030005c600d40740813402420081d908030f442150000a0b540c9008003040755904602d0300b00448440c100d030000d5854007101d82083c401c0f604c42008004901d01a800518680a83d004090800c0344444207403622501075070003500c0c12415034031407907141c1d5078901c1d01c0c0002e0401215144005101c0a10240000d80030b80a0940510003039006103041d0b80c00c4c0113211840842d003910645150641400c000c615440a124680c0400b410341402075882ca403444000803d918240e0000427140c1c503000d5802101c0c0781d0400b9040c01c1540c0000b5501c40403040b410300b5400b81650740b6010300701e2490040c04100c1b00b101c440148a155600752080000d000d04c915081e611261540b0820242c940b4003000200309150080c1042d50007854107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 778700872 1250 778699622 778699627
    0xc08282a080d0209030f010f180c09050c1201030c030303240510020c06070c060e01050310330e01022e0c02010e0f010e06010b071a040201270911090102120f 69
    0x4100092030200c06409013090b90759110f25811892380540540207210080c0d88815000121360754030040065007511495138025036407004201400d80301d80031a8410120070074054002e503100c0c00c0050301c81031588002c401207460240c9804a4848098060600d004d9032036002210230f00d4a400e12044641c40f2800c0011802900310128043e85e03a8006803071114080ea40c1c5c6417080f8101003001c2d040704c0c40c0b802103c5c1403001c14401c11000f10000c0c440b00c019205140300b4060380e0416031640b17800b2a018174261561262840742c00e1080154041c0f0400b5100409038203d03030780a4007140d4000041140c4c5181c0c4080054040d00ba890390355030741d40005036414694800084c0c40903d080106080c1000e44a040840765100e070203225400404022050140030510201032801040f5604c048200b440c00c0c000c0e002c0c0c941400c00040c190780c040c3c0d80194003660004c1d4001a8446141002070003800d00780603100e0003d152201080c00841c062050b140b01c624180c0090a00b41c000040d68141c0b0b0704190200103622004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 778702122 1250 778700872 778700887
    0x31e0908041d060a120215130510110c0111030d0902061201120c080c0d0303200a0203040806130b060904111003020406030f0b030d0c08282a080d02 65
    0x4440c1c0d80c01c03084810b445052898200b01c010001c9503056540480c2d201d001d00042840940d07221500100106160280b01e9646d10102d00e80984001c03440d40020380c040c904100a009150308400025018040304c4107944910509000544000402c5609001d45038402d01648490b03101c150300c5880d03554001002c542c10320002d044078800c2c02c4d07826003142d0108400450709908100010724014050309034480a00f0440c400100810349203082c104000d03040648411360f0f80390184000b503210149181c00c00480b561003030113402c0690740342e10501c501881071281c1000285542d8081c03c10034440c50f0302a00100c440d031500d801308013400b00090002d0b980b9008820814686542d8070040c00c80303c088036203002d0b840c1c1c4e14005015040f2014008451421070030400d0100c029600415035000190071414042c180000c54240280903006681ca140c00001c00e000c03502d46038000c6c40109023009515035442d180c0031600d9040c01d030031601450040c1d0810300320744c446400006030750801a0a00901030301c03006090001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 778703372 1250 778702122 778702139
    0x1060e130822030218061c1a0a0204060212091005220305150f04120807140408150106210b1302030f060a1401050421020d030509030607031e090804 65
    0x44007407540012120481d0200110304080a910b501d800b03030310031000c896142c07880200307d2441801040d03510160b4009036450803c0189a00380da621120f460301840303103241c1060210029802800360001612800c944200412803040c100e8585000203050840f81c0c5002990070384081d0400592070680da2025004040f181209a50312801503001d60002c006042c0044002e02140c0c5024050030848164402040045010b0800c0001c50000704d1401d040c15a481c22004c50f840d0100c0344201c1000980010300103000040042d2006090b4007450b08994a0390740c0b41700a441c68620340b40d03e40310446041101c42102d18042e805820712000151012940381c11000c003001c107d9004807a102102860301052042509289000001800000c003110440c00c9070580041c055005070700c96440002e04803c8050745004910b042c0c034071255405085020702c039205103006002c6030030140b400c0307001c0c2c070901c8000707a4400c0c42802a0201a81050b007100052100c4c042401d0203481040411b40b0b0080c0100000500b440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 778704622 1250 778703372 778703407
    0x21e030a0507140402040620070f080a050d0c0c031b0e0103030f2c3f0115060c0b09120307200d05270d06020307030e01060e1308 57
    0x344201c001e40340c410304184504401404407294940900e01c10710017402070580200225100780100c00040c2a18031600310114900340c02038000c0506551020000a00b0000002d80c0000892260044d41c40d440d000407401ca80d6915041d0015280f824084420000b203028010092200c0e0384040070070016a8991503400800a0203a00450020380011250a603080d030225003010b42440443d5569407446040f40090501c400c0ca520700f6101d1400004003110f00c0d0102d50704600b0551403100710540003125685000c8900e00444111203d9500300b16440350509842c8800d43c0a480715602c0b505010200c5840711030240c03c00405509042c0301c0c16044946019100303004d5485102207540f106039907000030411490750729107a07030b841d5540d6110400c017495041e00b100a492404031940911307580001843c001d01086003451070710701d4104d030000503680c06105241d002144a54440d80b014800c01030070004c051f08a421600c0703003da255141d48003180201c292460a81c00c6240120a02800c10304620000324694 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 778705872 1250 778704622 778704643
    0x140c030303160305070207061e0507050706091d09060f0a0b091512031e0a050f0c03030403081602520e0705092103120402040e030c0307021e03 63
    0x300c0b11060289040d036858041c440e0303c100644082c0c02554909003019008440215151444e1a10a000c0ba680c1900c5401070f2404103030030004407204940d94080c0038140351090b0041d036001c03440c00c2509150852511403454050b003240c1380140103569400700c82d803800610107081c00e40c109403a000d00c00e0440e564000c05038054440c46521801d420501c01c20010707495118480c0783ca00e600b041c0a0b40c0c042856005900c3d100d40e8412030b44076a140750038102101c4501c104083c200c3c6c500000300d0200384d00b1800001031440756102e900c5d00c01050b01e4100300050f0401608208000503800316503042e280c102d8800c0800e1600c0841c006070780103901d84110403184a04c006624411060b82c9100c500c0c0d10150b294048401000f00340d4130850383e81042c40c0000c2c224403820707503484e014a00c1c552840d950050104000f08145880c201500d0b19080108a522100790b000d880980c4500c2c180319801e51005804401c80765007006a80046142c06250f50034050400c40f92840c44842d10000f003080e2000303440521628414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 778707122 1250 778705872 778705891
    0xf092d0507081303051b1501030503120a0e030307030b0a05130b041107050607050a0c060608010504050c01030606021005090f070e220b01030201080a0605030706090e0108030a080103140c030303 85
    0x5481d100030020400e00000f4202a10901081e40d948003180d00101100c030700f0502d901513201640b907070304040342c60311108000c9001220b50540c00042800b0012015002201b0b500031504031540310070414106680c05480e0000850700100302050816000364000c11000201414003011a903880780050340c0d8090303014507080c25a031102c6504e1642e141ca44102070880b00315114180c00d102241e00d410b80d40d02d10051402c42400000a0f0f05000180140741030742249603c11000e021058071064014007805064800300c0c0c1c240700d046000003d56009028076000c1d211654010682e4020f41241da80140034080d144d050240582003507030b00408024048840503280841c08601d8905001d11105e500d000c141c90840c0f10f00030380c00300c0b0400050000181c181100c0c0c0902e0302845c96240c048103c4000c0011340d0103c0e0b45446184000140c507500180c0134422504545824072103030f0780c3c4062081e10382c400c420b11000083e01781c100520015900a800c6202000c0640441e1851410384001c40e1444d1300a5915021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 778708372 1250 778707122 778707131
    0x9020f12180705120a02060a0e01021501080d0f17161b0b070e180f070212030108030403080a110a110a0803090102061501180905150603010f092d 64
    0xe036464400d2554000310701e124100e40c0300d440c08801c0d503120415030194a1082d03103506000021048104400d00c0c1e0150000c007001c2d40d5602c04080036120032692203806015005900c803d032a00f0080385106412525998080d050440c5955021903a2000c520b02880c2400006112860301001c080d842601c1941c107684120a24801420b0191400d82d410060660f802c0360081014005020103000603000045c03800e000d4030840c1c0117400503121140c0c540201c1c4100031700380c0070860303101d000d241000d000c2c11468080d02c500704c64404211400f48024007449125510801080000480d000024102040c252900e2540705220030318003401c004640c602a100d9501541e07034181d10346854100d40700180704150085151206810010751240c00080541464201082d002c0d04681d001e03014541c9103404082c019122035031034010301300040000b903507201000c140380d8045100e07a0a00c0c9046a0686910000480e41786182c03040c0d0380d01808881e24011441d00808040c405250940505c40c500000001ea0106 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 778709622 1250 778708372 778708387
    0x1113030c05010912380403080601120204050306040b0a02071a0402130504120c0c0b0a050d0b090106050313110a180c0e0a050f0307150903061505061b0709020f 70
    0x104100404d801a100e8160107100c0000080c40c10880944590000c030314000040d0142d24070800c0034003001d9000320f1100b81c910200000c06034054421440341d1803d0301c90303406c03008000540b9800c0b03000d58040c8980580c8a6400704010400c1000780e558021100f001c050701d480390b0343d510703640000c4811132414615aa0300b81444214680321125400030400c160040040b49444e13101c00c0004020050044140040d50f0008024003050302500c1000e440d00c01e1000341c0e034134440c0c940140300380e1003031000d2100245401426a03c40c6403003803100d03040700d4050350361307508544a80314404142c61075a401211402e40c0b80309640d04544039000f941008020721121010000c804507522405d94100c003000170200591041034030340c030b542d40c6000e400c2900d600340c81480d00c01c00004003003468072155820040b0507445041c8802c6c0a541c3c001070a1050303922444040c420034103030324071007040c60002d40103203035114005109241e0043c0043c00d8503503a403e044422a481c0c0f0f41d0320350841040380d00030361810101840000f01071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 778710872 1250 778709622 778709627
    0x4180e0102090d0b0405072304050a0603021e0103060e040b040206130e190f06050913060b04090b061003110a0e013b01020a0203071202030a08220e0907091113030c0501 74
    0x10000c10f506507108d61240070b003070141c0361078225840c41c0170b1090344d80c0c0010402056071540001c01540d03001e882644551809001203c00c85001011070b800030f801e0000c0800d4210300d0700c0b55a405980c0c40400240c0ea030302c45900b0802c0b16040b04021914000d0806000111080c61103d082d0007a000003002c50b007500203801c001c00684110007042198030317017031031020811034448820150340808040c2c1d0100305000c2030310b044800f4000c2010311a81c02400d020081c1e003413080494070759010b000100c800d07000d41c07544004140c0075a0f41e0050300d400301c0781051140040f840d0142900c810741103414502403c0e035008040b4008140e204c1200c8130f9803149908010040000c1107800e80104454090009280da5056940040c0da00c0886000380901c4c01000720121045403000c00422000686c842041c507201c1902c400d00003161060955100d9200c0c1400340002074885a2440440c090803980002d00442400c2c0f9080c40007800c9289521080c59000300914480d0349411101000030314130510b4100781c01450315000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 778712122 1250 778710872 778710883
    0xc0102030a051b0a1d0a031b062006010b030c071e0b090f0709020a02011b17061c02091b0d02031b1603030510150509031204180e0102090d0b0405 64
    0x2040b100300c0080000910b02030700001e0200100103c80c4070b08071035244020124251b00d00700d60000b45440c841c005801030006140b00208155400c0395501004618420084140400520b28012490700428014444428880002c6038411a401030891520b041c5940701e0320007000d04101c511441c590600d1702402c110b50703960f507181c1040401c0d00070004415010655500d030b080600c030b101d07030407540021682800b600070740020f00c8110912802414083c048100945502060116080750700c0c1c264001403401d25010036000a4240c0345c850b403100c0b6001a600740001080060044040381030385c8040c0b2104621814011310401d0b400d00409078881c10207469040b01a201c0c244101501402400400395180d2440d8040c0c0080380c05160105160b00c8a0810354005941600036100d00b062020325001e045420000400c500001036040b20440490048000001d001d5400340c1140389003890b400700d8100959822107a45007406100061524000c0c0b030014030380803130500c0c0498900a5460406c000e00034244003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 778713372 1250 778712122 778712161
    0x1302070204050a1b0305060d17040e091209010e010903022101050a06082d0a06050103050c0103110405100504050a140102060702030a0e010807020c0a0906091a0f04110c0102030a05 79
    0xf00f48042011854080b0070a10101c2e4402d04041d40c400010b15650798181034242c0903600413003030b0001d190001310b244900d81c0c806c1c091301194050b480081607100200003020711241d000d07002c5090900000c01c00440f461500c002d440350410000001c04805607840c0d005480441c40d13a141542c07078900603c0c0159096a200800c5603445500d0041d003001618ac0104a0038041c040c44ca104407400000f18581c1d010664001420140d03512a240040041081c19070140f416030380100c0c100d540a0900c0780044081d10710b07481070104000c0c0240400c014504105038420003c0d5040e0500030f003826280c0c07001c00d10500d06a0b1000c0e4803035040c1e81f0041b4041d6010711034142c00480e280b0285260805080b4040c0415181e199000e04102498000900d407034400d005030002804001d09984005035244001d40140c0400d0055041c2c1601e0002c43e006000c00030170540c90803140c05449a980001c01808001c02410869406881850100081517800c02d0030710046101d0902030030005150708000c208400c0d811211130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 778714622 1250 778713372 778713391
    0x11041526150109090f0804090c1e1e350c030f010302220905070503060606040501090306020c070f0b0a090504090506042301020c010515270a060302130207020405 71
    0x1030380c0070303505a4914003030540745040e40108085085103800b01008241c0d440180c0010004240802da141040e0800200030100355500c118106c4003030064181c40e6111960600400c05082c04a1980c0c09600c4e50b005071a0280d0408a241d45200e400001140c0e4141c00d01d90f00c0c01d1038110a00b501c00c520050280c1c3c0144800800302c1c11450003196401100106001c064424501036400b510441038044040301481103030181400365181c1864503e0b6201102c2c000c0c1c40c401d00070413000903424201142590100d8078140d60b0300303045500c3c54507188003d5100186801060054040214400d14000c1e200d60047c60414034413562450302100c01040c0d10490382026100760704240303007640070500c0000c9094101760403800c81741d100300c03070380d010340342daa1001e101c2201303d950001c01c01c0400d038001035001c1441030341c005034540c07580b10b1410100907412103140b6801c184192000c05c000b2b801d10800038004d5000d51951400240710b40c8940005590038200c5440a4002d50001400b00860070107001c0c0316008242c46 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 778715872 1250 778714622 778714633
    0x18051011040b0304031809062606060d0f0f0f080c0606010801050a0b09010909052403340e0a0b120c010f030c030209150a0816020a11041526 62
    0x240d0360b082c20b10000d0009010406443c41400003031510b92142e0f0300415441c0e004000e116501c107000e41d00801c2140e0b808200c51800c0200356083c020102e0b9491107a800140360303003203c0145039110030014540361002c1e6507030107220202c0c00028544900402001d4000c40150303454620101125207040801050b80d810000d000004200030344507240e0710b1741500c01083e60a0b85460040f40103c3c0c007000140d001303e030718608040500c0341403901e001848241d59100d28240d9a4140c1210030315603a02481030303400e6010361032003080700c52000e0310302c07440c4c2c210400d40141d64516503514118418403043c107860384085130359191070808841c40c106100f131801c66078420251100366000c0380060581c191819540e0f00341515490340c06102e038800d904641400c0c1005008581c0508000059411b941061f40c004020a040c03002181804000810b00e1349000c006a0090403010314664860410203810750740d140d01f10b0b07200c580003d10740411140703c80241c07520882c0400080401c01036026164881c51040500e50020b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 778717122 1250 778715872 778715879
    0x51f0501080a020721050c070b040e04080a050c0d0306090e06061807021e0d031d0304180f180524060402031e15011d0d0303050601031805101104 64
    0x400981c00b00320340700d00503103d04a0381070031440a20034260700b141c4002d40019101009401401410780f01220104840d040c0c0d46038042100d85204501030101541d03034180000340018000c900400c3c0da002240b0b041c0d4245030101d9103480c0340203566151200400d440e94000d0080d00c0e0544680511000004014584c80c03c00034081401a0035005000d58120007560010342c41e540204440840c1508150382d40a9921240d1030058865551844100c00242082c185a060081c04072096020090440c0950314003482c280040d41424810700030a95019110702d00b001d405040b84c4240c075811100300444100980441c0381c29404e080c9416840e82c0540049400b83c180c60382d5101030b40e42c0c03180c0d040c0c4006a4a4690f500e0302d00051103501642010a40880c0402076419a824200c90122000b030301c61080c5c00c2c43d90000a481000703404d1405070040308060b10500400d10030b8001c10341221042c1000140300384410b4041d6400301500c142030341c9581c45103540c00c00c030310110b00c1500100c104071102d181c10301c0d05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 778718372 1250 778717122 778717127
    0x90f012306090d02030c121e030304150b010309061404030e0402030c1605251401030603030507120c060f0c120603020109030b1e0f0103032303010603020c0a0503030a051f0501 77
    0x20b003021560240456035031040c11520100941d080d10800103084400b11064100c0701036603032209031729908407030920324030b4801c151b080001920300441d4031020798083d980c5080c64070001014034241090401d41c0b125034032004a80948a541c0404810701401c00142c0341c5410003030500d219481605000700d10410802003100b0813401a80c3c072070200014400414401c6051091421040560036602d0860707003061001c452443c8010502256807010f035440411030800c006408aa100d0300c00030340031600400065001038030609003588100c0700d50800c5d2101780300b103031603e104561010314201401e9275180c521114043e0841100d00040c00c1c198018440c150440c3d000074088206480010711110010001c2401070240725205198610404408621843d0987c6a140c907132000b0b110640100d418a0b021032506040c00c24803c2c42040d40c141c0c018a56440e204048000303503c040300c0e0032054000c0d41060b60000700180001d42c002c0113110300c041260f041641031102c81c0421004581c0c01c08206032020402070741c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 778719622 1250 778718372 778718377
    0xe070c02310c0e030f03120702030903071710060906140603041a040827090a09050d11190f0201031d0a08160f240c120c0e090f012306 59
    0x55a00300e0100da40c0c4210308007035500c40c000c0e54030507034503003e0503c2c10300040b00000003030030001e00d41411101c1f06032600c00c02070740c80c0c1c401d22003220b4040c0c0051105200700e94500040c0d42d03d038100d0004544c80d088000707024204031850342e0444061107444800412101d034044481505a50b800c50300306107181000e0f62503280340202e0300003c1580b0362a01c0c0004007841560303c2038a0701b02040d6001d4440c158000c129101e800103258007001d2051001c14041a0000614468800042c0d80702008100a100c1d0300003e441d40706441d0114815440340c10611030b00c01c04090045103000d44222888000d055072480090243c900c6003061400c0900700703588494502a000801900d0706812400b003d41d61110741620b0225140705200281c00007114580110811529601056050100020414170f40d14130902803410f40305444da5410000e82d440406032480c64007640301c09104586d42c20015905015a030114003420400c562814550030703108010440008103856a42c41160719444035603601c0c01e0f6400140740790 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 778720872 1250 778719622 778719709
    0xf0f080705120a0c030506160309031d030708030a1d010e06040b2104121e0e0112150e0405150606120a0b04020c0d0210060303020618070e070c02 64
    0x42d80900074006401c0c000f4042c0007142c0b90001c500e04c0216450b07040071907503507a098800012038041d074513504441e41e2281c86042c1503650305640e0207101c444442c80181c003800c3c4c000d41c035136814058801e00150f52003017000101282d85582c0c88006048800d4101103000c032411003d40c3e4140208442890704590302c8104980c1070304c910144680d01c0760b5209460f04003212540e4420711b0000d078040248010301c0030003804980b000ca000d565425070120000c49022039581c4502d0b981d004101a40442e00c0d942d030152540c0d00a901482000203481071031380c485c03240c2e1000d00c3c1d4420b8aa85079080144001e20400388001d4040c525816084141401c016011948a1281d1081c1e1200d600744203012540032a810741003030030b100c40001c100359181d01d12007494a4540030301407480e2015220f08000c0c410310861074010241242e4042c1c0181010f580d83c280302040203114034407955030500a203d000b10340b500e40c503101a0b0103451169904a640072441c410701c540b0b0142149100030510480548140300c1c0302410601454 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 778722122 1250 778720872 778720879
    0x8030a08011a16031707140405010c080c0304030c030201110a0c14060c06010603020d1425090f030c060305240f030a0b012c040f03081b0d060f0f080705 67
    0x11000d540000c411a000c3c002c1c5500b540d410101d466001d25a0004c0410b038000c8242800c01c104d511080016121602840a400020030060100300015030041c00200b80c0e45020f40811464107403010030180c2142d0182e0021160540c1d003510500030341d640400c50703809001865008190f100c40d65107d81d000842d4034480c401b00d02c01341e101e2164164680d0700968540030400011102d4070358407800068040d40110700c01c0c10080c0e2408489141c0a03a03400f50281c003519803400c080d84003006910003c100d0703014180c0307204140004208001880c03c20000380303400860049003400c03145800c052004042e614043c003940b000c1c044c9404007800c522080c80d02540c20f41411a141c003c000c002c90042070421401041c05465080303524000100140d401681303004805403c0080e0300f00d907002200c0c02111040603900504044032103849100020300901140d40c12250101d80f030103648444112046442e440050140c19007602d035502000b2003401060090003038a0700250180e0454100040569248103c0c844c1130b10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 778723372 1250 778722122 778722149
    0x80a0c050c01020715050c041a090604240e04020c1b270109140921072301060602060118020d06080a08070b0601051312020f100c030908030a0801 64
    0x5125029034119000690018025516036499003032114685181c0b03500f811a1506180000e000800d1030011501a02c1010030103c4035500a44195652a040036503041d41180e4100000318007410b0244160111380f24000d80000c80c11071000e4010102d500682d45076000c1c0b4014040091740800205402e4001c2c104041d401d11100c50060010380100c00c0d61580c000c45e07110100303c0401004468044a0607200600b1090020220b85440c00680302d070211035502c81c0d070300000d040004c80c400555141194a2142207881c2c20201242c40360004040201e280e0703c4146140b0700464062002030003084011718150000c2c0c00c40c0e42c500714903004407140341d030311800c001c2e030780040c804081100c1c0341c0c1301d4400f07005581c080b100700318064940503042d40e000e0401511818001c00004d003656206038200c40500c00380d009515550b41c901517084400b500140412a44801c44142c065110303104c420150401c17070b00680d80d4451507031141c1030240421005421a400365041081043c41c85600500590b0446041600910 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 778724622 1250 778723372 778723391
    0x1814040812060411192607050a02010e030d0911030a03021b010504170309150c0a243b0a02010e010c0f080703030c03020903101503020a090e120a080a 66
    0xd00900403130654200c07400c0302043d12600e5a4a091500c02d0b070b02100e80700c0000031500700e03596201449603404006012090b800001c0c00192040d80904041c00082c00041624400217048a0030b54000c44402c070306061f0b542d0071030030920031002c00109400d03000341d010f05020426900d00035110a501402185440340d455400146a44580119001408051600f0b452620380000c220784a03407100d00e04a10230110b100c110b0024440040854402c43c0011005000308110380e91200e02c412070402c103540ca4864440f68810008a00e805120301e440c00da9441c0120300181603046240007202001c9040b60800111001c0288450010724015140d4090030b02c41304800c0d49000403070b151143e00c04002d140c0000c1050290400c54060050b10a45100791000c3c001c2d40c1041d24118224090aa50b00754540d01001c0c0100c800c110b01c0d40b00000c26230b41110041105600c13900070660f002007130740c000e10200d648d0301c0b421003070042c05001e0040c680030910212490602c0d8940008e085c500068031041140b6502c000d4030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 778725872 1250 778724622 778724629
    0xf120e120f0c06340e09040f32120702090405030c03210f060f010f0e121509071a03070e0d06050a050106050a0504032307181404081206 60
    0x1584540e10680895031503150028481c00348074085041002498019085030640d144e00020121070f200c825998000c041d66510100076560710090020380710b0340c1403a54041d01080354808c404d40703600240c207800503000041074040c0941440d4a05031110541144012240c803206103011642459011289c48001d40c4a80c1041d130306522910408502c1071000041c428100d5450010323240e1044019100104240e07101000d5103164142283c6940e4850015035801c1015030003810140207418a0307141206001c20a00c01250900300a140410000e03805a90520b4800c61200e1381c0950000030800542011441d080e10000d4588000351120041ca8000c400150568400c600d50031072200020410700740340140b42400401020300b0703200c103159603007403e00104d005400b501c125400c0000030360f1005e15151640d00c2d244801c860517181d01d150030780c105000c48074072041004028080c0895a8100c1032101c0d44182210888050007424a603031000d400c200070101d4400000d0340c00c0c8100f0181940890b69030180003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 778727122 1250 778725872 778725877
    0x20d181a0c0a03120e070b0a1214070e0a08030a020c010c11031b040c08040201050a05071712160216090504031b14010c0305040c09090212030403030f120e120f 70
    0x3034001c2c890500030805056004c40c0440e58030f202d61031304200907030314100080c1e00d40d02a80184071800390300f004000111882102401c1402000c4100014001c0c00c2d10b00d100444901514000000b071006441501c080ca0180405001001484c00551600c040c814000e5200e090311240d80341403104207804502800201000603401041c0141690080070702c4405504960007032203030032070060f40f80944441c0080e004070002405941c0503101c0d942030885007a800c407160352250404540b55040e0038540c002c2c40003294040c10003240c90f1112099985810a200305d080a60a0300c49021076000a0b585190030b1544800c050681e010203001241c01d54843c14140c0c2c0301c0c403203516030805a1123003d1051090000c80003030441803103101c1c0300920a5400d040740c100d06541080d24050070440b00748800700700040440c1e010003401072001d4007600703e05084003862403c6800c1030b4019400705240320314000381281d00010450583c1d80c4050200b000c0f4480718003a41e602d103050341c804c921a001c0054200c1c416005c2805 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 778728372 1250 778727122 778727137
    0x6100207090c200a0b0a02090f1203030403111b1908060406060302010e010906170711060709080106050a0b030414010213270501270f050412020d181a 66
    0x1c040c81503008420b0000c3c0381140840b0341500c44880c6001c16000800c0110311100b4582e0402c1103151180ca6501101d0000d6018401940c0d00400040100d00d2a80b512031a81d041e00052001840c1c0760729040c10064041d54a40018000c1a00a0109005010541c0010440c030703481c107035003070080c004d50404d220b40e406207a0703000004a4840e420800042103816000801a21702c01c0c0e8641c0030b288074450054402d61814011a408180d1118030880203101034100e041c1d00611901d0512814000c0c410300b5030900c9002d881030000552f0042c1c0c02d04c80b26809001d0040203190503600d40041c1483c002c0e103070403107000c0074000a0034103000c4501e4000b04071094058400d00556184441c1d5169621a00440d41300301c0d104031030442c1c2103000c00d9403000340151322500b8100c4041c40d099680b0342e03d080d40f212f180b00240314101102680c1c0c6001d407400c07001d070074030945104500c18861092001e0b8070007806407070300050b042c0c0c0b0020440e140d0703002041d014416a0071011980c034114480300c0110300012008030740c0190388 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 778729622 1250 778728372 778728389
    0x603090602070b1f090501180e240901110702130504050c030d0306031103070302030d08040c0b16230d0f053a02041208032203120b1806100207 63
    0xc050080340302c0b50141c135203e00445044142e25180d6105d030058241e403c240705d4500a40401d0640300c1e080c2130a500001e04940c4994140c9650461585040c0308914a500c0c40c803442008003810440c40c1074003441074600c0b85082d80901c1e070401c4082c0d80050321640d860351040d5412074596020a081200401181100c0300c0000c003603602043c1541401001840c080c817058941c003d9101c0d0108050a01042003420f49801402820050072000d90549428201030012140c0d1900c030300e400902d0b00e1111016003240d40270803019202100c114209600c00b403003145c42100e43d140345422189201c030f0000802014203031181c2410200d5280c07a1a0503a042d00030035081070a0440c1c0e5600070030070542d0100c02c502140001041410710078500d050390104a00844c0074580d20762040e902030300041045640078503403041c1c045e941d0900c0901c0c58a41112400b0340c0da0022408035404c6015818401d4081c003400c0c00310f403001d803149255002c0d5030b01290b0b00ca103006846c4500901e00c0c0c1e1a20858184248450030141070000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 778730872 1250 778729622 778729643
    0x507020319030201050601030b0411161e03020c10050901121107140304030b01080f060c03060406170607080a02120c0702040207050304060f091203050a0e1f0203041e080601060309060207 82
    0x50501034045c204c101d50700b50000345015081070141ca002c1c42405221211504035906040108686020b05900c00d403069a521403400c02540b4000b64007045010713428443e038060103503042400b05010505c03018047d00c03000c0c003c1c05c3c00f101849980c401015024104802c001095448180c8400006445019005840398200b003405503000d450000060044a00c0f44d80c030707480a60381c0d031a451a00e40410044040071034020708085000850a01c0285402000042001902640d41c0c10070408140f40c03003848420700d40010041003142034100036142e600c44454001907240454804442690020007070849020742402324212096403280e80c186c901050b1b20400b126580c903161640a40000000c02c1c440c40094030012000c035610800d440313405081941504c6450409040d240143e034640c1e08100290b40284500c04100b803480d039403d1010700084555000f466550703003080c40541d500204800300100c2590201300401841d400090164115142c82c9000640401e0a14008010303120b4200c0140c10f20440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 778732122 1250 778730872 778730923
    0xe040c0908070f1703160605071704140d050301050303090d080706050408071e080301030209060111071d0109150531050f0f010e010b07050f0102031512010207080a05070203 76
    0x500704000d00356000407244407109043d01c01c0503552813050219a0a00c40b0840e20551b001405580015812140c0303030410000320005c444080001c1c0300b0498041d036801e0f05402d5050000802404101c05542c101d1500d2031031b56042034003296480c8604100240107021030000c000503c04014151a28551301000600481c1002c0c142a5100c0d04103038825a8015800401c4511041c2080b01c0e10220765402496a07086030700c0c1d9000c00c052b040004201a0500c000c2c4103c2c080b002505002c0324001d00051806000400301c041180504450140c02200880b4a04405000304425401d80f407002c0f682c08485110116220b0b03038451200c00450601c40034004c0e0a446c560380322031600d40000d8492a54204035003050307034a92134040401c0800380304804894132588018807031607500e0300040503064010000c8402454503011250b089038070880f10141c8060000c40441114a8251280300840c40e11000039070800c99240c984484601c00c44180b181800780004550045440c1401401441150f20076210200c020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 778733372 1250 778732122 778732139
    0xa05120111031005100c0b0112020402361507110307030c030606030b060108100510030902130e120a210e0d02060703050603070e0a0b061204050a06050f070e040c090807 74
    0x2441d00516100303007221703a4409455071142000122454001110749881d910f031031000701d44d01c80d00c4202641c200780c08100804a90b0b07030300c102c0381d10041c1a034000a00214506904402c0c4034101246561040f1440304440e681c1042e07510640c1c00b425040300c54050341045100c0040d18042a651000b85179000403c0c0000c14068554000001c5a000d4041c0142590380c10b0011142d140c0d0869149131006000582400a81881705103488403410300e0400081d04051a0001140000d11800e8204035585a043c04409000c05100700101c0741c10041c2c03400d091003071218001c0c0061406034965264003104004d000708c061b0f4141c00034901642000242c51184008000c02510741d00106c440c0c0c0d01123410440410917074180099140100c600c0f034001443e4a4030f8981c2540c0c054082d0116042d804807040c030041459100049617a400340340700b003009000420031403a00105480700141100c40c4d50501c0310811501640100e001c092a44085400091242e0781b0751040d6940d56107604000800c0c0700d445004601c011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 778734622 1250 778733372 778733401
    0xc0f0b0702070e0402010203070b04061d0303040c06031e18060501092004140d08041a0c0c010c030e0603040c08070f230a030201110a02040c03050f060103050103020a0512011103 78
    0xe030181e09440c842610358991801c010350581c1c1c0240168420800070000c2003000c1e280c140c1040c0b00c1c0601103000d0a152040b885c0c0703041d031030400181d00e030800020300c010400c149021703000528203030400303104902141c840c911070810020f11090440344c65041c44007104d4400802c0c500c845a001204000700d58548440c0801410440c41910074611403012141c00c0c0b000e10720940d0115044038078883d16044809082c003136000300403c0201c400840a000c0840c65804030060024030340581c581c0e0720b4948020b10082d42c903100a8603062418003054100e000d003c40e070321801d85d8603500d80c240c43d076564075203561402c0070301904694403140190007001c4001c151210b050401c4012140c2c00d680e000c044040510341a1600454086500c3e0301074182d40c0100010350160b54880301d401050000e40d0b041d14425000701d82925101c100b200c0000b50354900304070350950340d001040d410240c207180400c036a6046a0110703805091900465205602c010300401c12400d0940068105101d11641113031039041180c0a009181c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 778735872 1250 778734622 778734631
    0xb040504110102010513021f03090606140306130c03061e0c02061503010e0607031e11040303030e2103090a0606080c180f060618060703080402032109100c0f0b 70
    0x1135080c1070101d036070322107004143c4003850b0300105001400740c0b84c47e00074a04e220017081a503040c16205c0004402150491190600801100a590308046c410004050810740002c0000464400c00301464010494443d0f219040c0d80d03021100051700d081410000240840c2d14424070546428800f000702d4a42e40450350034002c07003240c03e8101c6c06050040c10107007665050f81c5034909551200000841003032107500f00024102200e4801d100c5e041c83c0007520020782e9203000c0004c4415000207020001c0652511848045a00f10400351240c4004c0f5022411500b01112007128280408404140d600c0c1c0d003400040d1080c1e41c4000100b2149aa0300e99142c0c6800411580c2c62160000000242c90300100b004018880c0358840c10910080e60344808002003a08181c4c450b040602c034440032804592100401400d915001e62600251071038544105841c00408130b244444522141c0701080e807120700745c07065440c5184125070a20b040008030300101d031511902000580145480d581d604180324041410b10300a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 778737122 1250 778735872 778735877
    0xf0d0f0e1009022404170607090506040b03060d140709140f100b0a0c08041733060d05010c0c030e10090501111509010218031605090a0b0405041101 65
    0x1000c1c0060341e1080302c041100c084e4102551403038200703006003000780c02d06010014044050800381c035a0010003030110720301001078003039100c0000d00460300d412240d00b03030044c001114038501d81402c1c810203460500010b0001d60003140003103005010030552500f0440200314283c1100c0c0c100303641d011018068404542c4400403034030034001150302c40f8103907401e00f8451440e1207035059026240480d94200c0750703c551594010070030903180400001d59041c0081c0b000306044604d601042c5480c1406900b007981012116a11152403d00210841607080540e11115014141040c0c80e80e50940829602302c40e41500a09035481d281c1c46410050b002004025954000e640b010201504001031240078480460a50041038031a44100015031244010410420001c0b080e44d682c61020501e10310132250981d0303c0d64450b5008034001030744585601620064000c124010310300032040c030004000050541c000e6030f024035280d10000305601c6564108400b0803201070000c200034a06030034070180105015081500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 778738372 1250 778737122 778737133
    0xf0a02280b0f0924091e030706170717061903020306131b050306040605040f0605040305091206060f120f070e010e070f0818070305070b04090c05040b0904020f0d0f0e 73
    0x100207044010481905003000d00075844c144201e0304000300c0038100c400c0206e00b00b20741c01d074004c00c6440502c1080020102c9841d00290505001c80407240303000000c118508005200310404120011030b1b0040781c100a099452404644854040c00f00c8403c01ea040a5014410030f0148100306403031101304140307280038050140c281c6c0b00e01d50710f000184d01d05100b22a0b00d03a0040c4041000720301c1070303404070750402d10500100d100039609940310800d0300c01c122829004150f021844007401d00f07102c0071800d68017041307801604607841e20600041c13000ca0140009402140c62042455840b10200601504d240348503040f11090b83ea151140d030304544090003085050414039000c0f0364201c0c010600c140741c908060b1a0f00340355903100c10203061034140e03210802c90a441080c0001001c0f43d001c2c44204e02401039500e07a40e41c2c03181400444001e507140c2c544411704001007007008001300b01c452815209a080202d401607510a948000c41150380104814494621714142c550300c1018030076846040003e15a600b640c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 778739622 1250 778738372 778738399
    0x2030c0a030c0f090b030a18030f020f0a0209010e0705040816050a0626151c0203060610090605340c080c0a030821070804050f0a02280b0f09 62
    0x5401107810020440131404107142400384084810146031301c00001d500008580036445106649841501010340208032a130303c00c2c521041c2e045c03142103000c181980c0185100c80081e4040f4070394000501c50f000e1000c110030046407410307100780100e5008124400854148110b0445c1900070034100380314040c810300740d45d03e0000c2d2480c003645078440312096142a444552416100700390b00000c00610340c1450b404552440411541c032012030440614140305850000125841450319240700a00f000380300d0110884500b4040d54080c0c0000213440c0a81b400f036807504c1c40440300542480c80c0c000e26900121018107030310f5074101142001c618041c054021444203980d5405c07071540317504280360350ba40c110b00342c00313028000b06039010018054004400100048081c00110030f4540c140255858000101c2480c144018040101b1022980801c04c42c054000261180d0005d16101940069013101c480301400c841d07451804100c44000078072607468169a03032245c20300320b030a5030b0380800056403141210300c1104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 778740872 1250 778739622 778739627
    0x606071509210e1e06160209010803180409080403170403020409030f020d180618030503070614010e0609071142090a14120706020a1205070c11060c0102030c0a030c 72
    0x10394081c0034400d01c01007622481d0601461b80c1c0712603507040220148460040c016100d01140500804680000d15162856609c144007224110201a4880ca00b41600070021400038406ca4048035071088018040303030201900e021050007180e0029520511702540d85060540002440e881d00945d6800d60b540c1640303000c2c00342c2d4810040d00740f038084d80300c0080701408490702600f179090321000307600c1c840022540c1d25074400c1d00d1980461011250300d5101d003031640c56400e41e81c40d032902400803a040703001203141000114562840007071010cc104416140c0c0d011010105209922080d0b804085407140900b26038000c1c48526407142c00312043c030101020000810705a5245540565950f00c040d00b0000d802d84c503644042d51001107502854001d1000700749092012a0007000e900d0f22510015132520b444501c00b8203410054000c110f084c0d402d1004000400fa8000e0349404c8180c7d012000250402e01600441c184e03000d0b81c1c2e038a240c550b10000610518404020140200c5019580c060103000e0110404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 778742122 1250 778740872 778740889
    0x1109060414060f030304081902030706050f0a05070c080f0c03100b030a0f050c0d050c010f05030c0304061508030f0304020a06020c03100f0f060e0402040b090606071509210e 76
    0x101c040724500c0468094984401c2c118404500242124202a00c2c0d6211130f0030041c121980b1214420210001d40131414103110f440300401d50ba082103400e0200306242c0e0f0f0020700c11040078008000e0001803840401c42e0940300c1c007018203407490849405171058001281c0d207110541e00944244034540d01c4007200183c0b4001c1c41d079001806009084581c18940d0b48103414040000700b192140107a58541d641510703448a0102395a002d8002410040f80140004d00007604040307603403040180c02c00800940e103802c142107d07000381d48004000f40d410002c0c420000307440c0d00341c2c100c1c0007103000c0010349002c2d8100f005c01841c02030303000b119000e10060340d0b00760590340d0756148100710360103412901510301140002c7d07100d04210b10f81040045110040b90802c107040324901c2c0c02140d01c1c851841c00744029801c0900c41d0701070001c0d01740c40c03075505818200b0018029010b020002851110f08521071302000350b564211101540c0c0c00703811a408041010940300c0303104002040380d40040c04200244000d403510300310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 778743372 1250 778742122 778742141
    0xa05040b0c011e02091f0905010503040212060f01090e1614031f020d050c0a080601050d06080703060504050c0d0507120c0504051029040603051302090a0f060503070503030306010e1c11090604 84
    0x2594500a480c008c0151038940004105030b034460484030310540c5240d014070070355100e1031075025041060740c10610b008007102c0502d034881800380d002c1040c07040350960b080000020303910f280044405003c5401c000902d00712001d528025500d0302002404208005900607007105070000c0418807141c0c0e151131071085d0074001e84002c440083d119001260080d400b0b2001040d508002c4c040c0403820030b032261074007807514180380d00c1125403659440c20402400400e2108800c0400212402180c42c0c0701501c585548481c1ca001d001c0d03003010400114010825141400002820064818043c40c60001c05400100d1030301e100da01507044c0f800d0360754002c0f800000c8107045495082c1e11514186401c2000c1140142001005e40384444040306091002d40e41d00061030b4402d484c41c100c00f182c25501400304006880250f40281e0203580071100030b00c00c0d6a0040300ba40c0c1c1c441028030b0100c00c01c002823400241121070a5815049806a0302400e03402c0c4480398841d094000001d69500d010394903082e0030b00048a04400303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 778744622 1250 778743372 778743377
    0x30c0d140d24050f0d031407060203040b040312141b09130c0806090c2208010509010c0207050a0b070b060307031407080c06040e0a0c02120a0e0f060a05040b0c011e02091f 75
    0x715a0009010f4841f180081e1340040721b850a0070066902c003401c0341d20507201520b55907a900100b200300740d444000e90000e410514001d107d41d520b15145000140790103451206c82503409600981c400c1501c4003600c4200720003c01040700b00110400e01c000600390004010b002a02c40000108142484401c6c903004500c4e03425101e10302920707070b685140c801241c0240f8454224101c0c6002581440c24014540204010b400008400c3c01486000c1c2c90310509511243c050603901c402046407440c0031068840302504014040584c0c1d441c00c0c002401c024858100a100035400203840c41710450001c0d228050740d20300401c0b80c100754440e400b01f008502983c421185880b10010024800101d25085200d1000e0113004450448660b40050350003900001025000206075210840c400e2600001a500d020815903280e4608003007028010200d11440c000e143d051040000e00d903c07440b0003584404640301d8031091588040071060401c401075401000d580d8860301c8000d02070905004054411814008140c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 778745872 1250 778744622 778744639
    0xa090b0a090f060e041a0f06031018080403030815040b0f011b17130905040807031b0b070e01020f15060f0103060905071e02030c0d140d24050f 63
    0x42114050410300304480e006a40702c03e00014501c2d41c3d2100d007030090340f0503d00e03219140440c2015443e1320030300030700c00401c1c40600380034003a25407070110f00c4143d0080c2c032040210b84074444407420351b421002644001c3c452503000a000041c235900060407805280b00d2080941c42000c06d030700700030656860885183c0e000b03038007a5802d0307036940c0105040d1207200c0c2c040c1032000e074807170441d2581401180000188069002c0c006403400c070301e095101c0002c000d4291001c0405c103d04003625110300b280074040c03004003801080140e0620040710480000e8146078082111856480c205400a10031100641e0303840c0940301c4d807072551282c20740100300386110b100c00072207121780c0ea560081003100c0c0560002c4410b050540e00d1001181d0203002e8040d481c4070305a00c1e101c0c507007404042e00a08454400600a43c82190414440300010f001c0c080340c0d03007803041040c0c90320070300302802034000052920908400000051901550b0a0007032200b41da65940c4081d401c65103005290380300b0030b00c0b0111341b080c00a56031210b05e2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 778747122 1250 778745872 778745879
    0xf0303040f15090b0f09251403121603020708010e0a030306080c220e0f01020903160b04051e12060601020c041e0e0a0c030305031b070f0b0415060605090a090b0a 71
    0x503030300107581700344010b08450b1102c854150007d0b55801e004044117001808a45c2488642009034484601240c04d4009100c1d20360041503660b03079400f0f50200002c683d03d0345810b58042c103200704044005410180020002e20516041d4541e60301000c6100318007090800c41c000980c02c0d004076140d109a040a40712000e10901c8041c800500840400003040c56640da882c041075504040100076107040b841c5c000140d540c414031041600d00f0b40c1c0000385042c262883c40b024000c01c4e26500607501100c1050340c1001160311407206d241003048803158043d0f0013420f9801c55015034000040d020f80200020380955140d94654024803050b601001c600100b0031149001a208e01030030b50303221038100f003402005d685200407035981381000300c40f0580c4190000340340481800b011302110b0310740051512484410916040440daa43c045052102e84090324842010001a040c041d9101580c101194604000c115190f1940e2002e0500e07000200070a000c0c5110324004100041c05200304425900000d0124000526 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 778748372 1250 778747122 778747141
    0xb03240409020609100212220b0c0a0303020306010905041803030e060c04050f210d09090c0c030c0213020c07091a090c0307020109051006081c1409030f0303040f15090b 74
    0x40e44101170218884c610348158a10110405030040a454100071508240420070240503211950080c6450305420042507810030000100c219106074135040c00340c1c490b174490005030744480c180e03800141c03c1380c1420803600c2d60413400c100301c6580a02c02c1c1c50400c17001004c1e06100766544000c445e0011940320401c0309000601d0f11862503046024001d040301c440300f40003444410054640800402700341c0c000e0340d01109230b41d0044854001b50505000410008409420007803c00c100300d034018050040000c1410203640701da407a42d2801303d0486100350b556184101c41d00d55208024480c51940a20705500c08524210ac4c514400304804000c05c4d600d49034481442c2d0201030b90010b07107220b081d9903071880345c480024014440c2c0440700c0030740080001c0c0c141c90000ca850401251125080a610b84510142c5000f90894103091000701d40450f4182c0722401c030340c0403a15081c85044060550321000c0104820449000502c0c121548600d5070100640701c0c2e1070a16041c0c4580d810010710188c50b6400003441c008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 778749622 1250 778748372 778748389
    0x10091a061c11150901110c010503040b071b0c081905030f1c06061701090e060c09130603080a18060e0d02010306050d03020a0605010f0b0403060f060b03240409020609 73
    0x140030b40c10440500108000042c2c03404002d20010544210100b9240665a041041c2c6960440c0220240c5000e6140b880001e01502c401480107000d0155940071440007840b64510300740c10207859112912040140c204401981290f108408461003620120381081490000f107442950b44007006500301010350f03808004a03004041c000620780d40788080009402164044e2074000c1c00140c1750034508226507030043c1c03a00d41e41604030285090a0600140d404440020300d2548030f174200306103e8984101c0000201c0340e4000242d2001807505005010007441401001031524140680b584a121685400c990720b0341d0915102d0b41c8049500644440642c0c201401c0014680c0c0c814074000451a40324400120103606000b015001039100c1c1c05c3e504200540e074459940503040f00c01c2840072451900d0080c56083c0316030b01009080c20307160065910517a55940001000e080a181580c0e12460410384000c240d0741b9440c8884a1250701480c030007201d04003031140c0c6403010340241c0024503060b4008244001038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 778750872 1250 778749622 778749679
    0x901140c030f030a09021507050c150c0a111c1a0402010306050d1203110405102007081b0a030206090909070911070209060a060203160c050310091a06 66
    0x180010401ca00d24001000002c40c031070210f4035800150b611722070051240c41141c101681c0d18106080101402144c40001c0c43c00d5000303011110080300ba14150000341c418051800e4030f000034401c014520b4104a0303d00e20300e0604c032109444c8040c80706000d18143c58961a4200b002d0700c50306c4542c0b01512101103d0440d298400d0041c1400b0030416075074004038100036526442a542081d00b03403a01d0304025807500a501c482c000d264445801d1904241c0014201d0920181d03ca061100c0c1c040790a0705000450748905450810070150f07140e0b1039850166584039040c0c4101c2501c003920b000c4000d4001d1800d41246000d80e81c0241046040c4510401440f070741040280140f00701d4843e05030001410754940c003a000d03e221041000a454286a1040c00782062004d0a81d41c070a1422141c240030507a030000a640032030104403410303420700e075580c10840e44035140354000039014001c01030040c40140c01c0c0d8014458241c40f503582095a8803040100002101342500c42c207030301903042144500b400031102c121312403c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 778752122 1250 778750872 778750897
    0x7080d060b07030507021008150d1a040302070e070c050309090a0905340305061b0415081008010c0207050f03031c0504050606090c190c24050a02090114 67
    0x640320224107015030090b0008400141e4002443c3e07003141484c6d460807250003540d041226a90a00c001502c3c540c080c000781b4240100110001d03841848042082d084a01d0b804805005040c14942802925040607009920140d040400480c40540c072a8540c0940d4a41200195080094039010010500d0740503100b035003911740360b5558001241042c085000000c1c414641199a00504000e0300002d0200e008840032124420504001182000c40c1156201c003290800340160074400c030b0044081c0c00b81d6003003008107852400340300751040c2d0070a2449000f07501e100c40000c01c2c2035075920030b03030300780e80d203080d0034000507000381c0e0f410801410040c8020709404802010380342040e90251300815014124003050110300d44842c2401b0601038140100d03608640240c4111042d031a2045043c4454401c41ca413134828040810144124644600120200e45c2d034801600440d40d581e10800700b1540d01e05a08880e005840c040200c0c40d40c80480c403c0399040e03001a161044410881c100b007030220342112032003186 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 778753372 1250 778752122 778752131
    0x1c0525030506190507030603020f0609180f01080c0a081e01061806051008010f12060b0a03030201090203010609060501020706110c0603010303120c0203040f03080c10020307052d07080d 81
    0x9801844040e20403c1469004200840c0000c2d034101030703a4015001805040c0360a409002585400355a00c490000c19200c0c1d40c3e403000180082541c680c9100f1541c1740b020402424451052000307800c05040301c603100204c1d083d030018141001008196031103428400e5100c00e2483e101c4c4d140c220341d100a00300d4811300010790941e032440c4000e001640192900040380d510760701031000d0700e00101d400300241194078142c199507050494011840650703000303c20303044940d02e44507800c108503a00080700082c0060030b000c040c21f90300c2c035000c1d02134031400508034840d509110003c42c0c1c0c40e40903c281011140705034010503d032450114280c4006400440200c004c0c020b0500014840d101c84005500a511030345d142c100c050301070440d001c2240c0d00708a5403400c6401c1007200b0080544c45034100d0302941e400a00040c5e8603504c00c0c0340e0500e82201070704810034943c004410070801680001c003401510010005900183d540840c031162240340003401d540944400340b007003501040c04003000d401301c07031848040060b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 778754622 1250 778753372 778753379
    0xa0b0d080307030b130204060504210519060e010c120f0e190312020301180f020d0501030c1a0c060f040f0c0803041d04030f110c1c021c0525 62
    0x80580d4800c0b200c9801003070f01d942502030541069014500d5582c03081c00110304007410107400801c1c92140d03100300030203a80745031031003507480305441011a0540c2d440011140f141d41c4880d0013246071601c0401c2500c00618004e06190a010103000707200303400004d60b44050741105c03d8030001004003400f4103038110440da1890040100307242007114047c1c54140000251001d8050b2500074041000384d4a1562400d0052004000d41d81e1040310003003115040240100740d14200f108180300034012244118421401c09000109000b810680081030340d101010404080324031200b080004c2c45aa00003403034561080000070840080112040e400a21810403041502c031652900700444181d0342000da0f56030030000f410011849a84c02e4003d1500d845a25800389180070b032030280c19560302d04103c00c18460003413105c0c580c056042c405520410002070081d002c01960107803c2031003000b00c1c00101c1c015030654414141c95004100c40c054920fa2103802030151000c01040c081000440b048102003110000c0c1021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 778755872 1250 778754622 778754633
    0x150e100504110c06100f050d0f1a0a0c0e060909090316030e01020115080c040c0e03100b0406090501030803130c0b0c03031f052409031e070b120a0b0d 66
    0x200d02c0b02105051158440507400c140d40e080c10000382c0520100c07184138000700f11018907005c84070200da0080350300324101c10042c00d040311002482040107000100d01c0b255440c0d00c648020310540141e03080303802001052a11201964800c2e4101032040d840002030100250b1843c0149a056020320102d0a490600144030300d810404511090124040b600118803a156541d0901c602c185805502c500212010f150050311034440641c1c2c8000740c06603480d40300780616503000b9072610209004c041e00701d03048030001c6e031031000040401d002c910788114185600040e04041d07a0080a050b00d8110a0061031070b03c8501c082c800c1001c8405e02102e14107011400060b80f40f10a80160a00006000107180d4a1400783e240010396100403031002185041c08009100d40d40740ca01a100007040b80c800b140c00408104100240035002e000c06056041c402c640c01041c82141c441031494075030100d02c044444054407a1100b864a0140b80c000e000180e00003c005240103507241c11108041801808111141d0442c1e100ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 778757122 1250 778755872 778755881
    0x30912040e0a05060904080901050c070312020706020609010c32040b03190606020c0616050a0f03020f0609030901120216060501080c0d0b0612070e0106020c13150e100504 75
    0x1203100074504804001c0350008500820f50320100407160303803e40745070558a0540d036004a40c4142e0410001082c2d0b00e01e01e00003008184007554000e03401c04411360004000a54911a0780600d0740103004a070045071001105024940c44a9415110202e5260841609401001e0600064003070003540406481e04103c45800420103041540081c903500d14201c000b040080c1222558036420921308581001070a602040c420001001221415514491104135146150b80414007a01a001e41d00142c0c2c10041206a42c00e80c16203e50242c4170659812940300fa01d44804481c9101035420070000008030b50700c940200c1d0f40f504c83e2400014102541c15442098400000310200c0b1056a2040140141c000400180091460403510300c40c403061141c0c1c0700e072050b54010702094043c024401440031203a4050200300301800f4144d001158075030b500e440081d03890b540080e205009400c00400801040d030240681c94040c0c4490001d14450b51810000d03c60070a40101500510040c945011550755914002d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 778758372 1250 778757122 778757129
    0x10507081c0b0315060f060d0608030c0106050a0b0a0c03030204120c051e0604090209060715020405010905011b170915030a18150504061401030f030908030f0d0203091204 75
    0x15001e250100c1c042000448050284a520a80c450322440114a55814031154061003e84683d001000c403840800c03c01c0c0070b40a9060446828450081402c140000251010041c044000d01c180780d6940c040c03007141c40d058040c602d402e0b541000040320b00341c0100b843c4046644286001843c040d0780d143d403807501c1960340390103c0c6c103244956000c0004e45410795010015800c2e07651064402c02c0040e0000762188a680310f0022103580208103c2e460341c0d80c00d0140e43d01c15402203452803000d184002c0c0340e40258001d004407804244072010125483d441500c002260245400490150034500d031144041030003082c26120b94088200305000d10ba0311421640740703d007840180159101d0401411000070703201526082c2020101c00110707640464007400c41a000c00d0004c140005c0c85481e00e09201c40508007141407541c8080000d000042040045d1001c2048079000b50303140c03400240c95038109616032041c0d20706142c100006200d1410303940b40c50f0b8001d5801403428001c8400023581e40024130943d410591 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 778759622 1250 778758372 778758397
    0x9160909050f07170907180f1e0e031e0d090221010f0219080c2505100506060d0b1c060b0901090b01090303140c120327071401050708 59
    0x1003d000c0c0203038000b15444010f0b4064460b640d0240b0b000e0a0641e55076801c4d00c1460600c0702e0454120610390000d51020055440c0d5078000d02c07003180c006c000c10500300104090ba0002a140c80300560750500701205884040004c065000d642095481e2010800e80021648680c00c070ba4a07040030006942d9840e07444e047e0303500710007822103c1346015075607401c4556498100c00c4075170041060f2800e1041c43d001021032000d043c1402d010310703100c050015800b40100c0603550780d8001381d0401c4100c00c0c018461a440c00c0c500c11070407227070030301c4c0c00017026401d44406950300d94010308140a44006e0080300d030030003080004080d040c5400900c0000301904084070254003615800d81d42c1440c212113045c9141e106014101078181400065a0180001c24012031840080c04210060141c176414010013030407103000203c804102c0300610030083c10400d4580c810b440c1f520440c2c18542c4410950740001ca6102e4015164801900b0318074509204000040b142c0e1210904215041140704002415070010301498100d20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 778760872 1250 778759622 778759651
    0xe040f241a0f03120306090405031903020d0c021f050c07023d090902030a0b040f2705060a021608040e01050a05150a0c05190501020d1503020916090905 67
    0x1078180324000d070440c081a4000e8101454415011003440200c1c2c3e00301c0000d803440540c0360b0b11818060b0660041218111020a60484640d0786940c9034003d0100c0d030301e070321008201040f91103806076511101040d000f6a0080300141c07489c85118142d00140c1e016060381c4085140141c0740d40080c02c4c9000300010b601c90500d814055942d1060042705031100c0e500c102000081301e58100302c0143c007450b03c91041c4d1203150b40004c00290061580e8020782103641d8041d00520141c507003201380c1070180c0f0500c2000d007020300003400020340074900207109500c0d07a6046405000780d900c9420114001c4d5000c24940380742401200d00f440c00140d030b0000208014442d1280c0ca01007541003e0030094184100d61200340301d4003022030030003643c000640868103400d12900f080450b011135882d002e420080d1084404460315161180441804810b400a01e01005103210400140c204110001041c03500c40c040603400030b0842001402c02c01f01014444608451420001e1a0607075070704407081510000c0f01d4020750403411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 778762122 1250 778760872 778760921
    0x40b0a0b12060108040218130f2603011d0405010204120c030c090c050301060c1703090d140f0715020f04060e0108090109240f0f020a090e040f24 64
    0x1955115400c80b0302464842000c0c00c181d00080c50a20540b450040e03029072400204010508103103800c0b0b01039078002c00014001000c5e041007044010f80318050502d9102c00304249201d84408400c4034141d4500c0d4000c0128200314400307004d50001c2c0248221180e6608200c040340c001031001015281030700c5240f50503909821403810100310030742d90b84070f0f4101608003140f031640141c000c0c00fa00e040da0018a890016007056042c00c401e007480207103040ca18403000006128404801145105100c099070300c6003104900e08002c01034252003062042c80c0540018082d150001f42c4044036224180d4a240c805400c0c500c0c2c617242202e056000c2e43c03000c0f0215045200502e6156004110268080a0071000700003080d411b481e0003000c5c03001407003950200401c442d42d00e420405945d010602d0800040001c0002d52003d03180d440082d4840c60303100000c1140340000103120b0158a50151041c0c0e804051007040c020156a22400c510441c4101c01122429103800443c940c039a210f00342e030900c80760301a050880c24 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 778763372 1250 778762122 778762147
    0x8041721071e1a0f09010617060c1b070b092b0215220305070e070e01140d0e07030b010f03050c0f01020a050f0a120e1e040b0a0b 57
    0xa00a0840a5240c14081030000c950300c0002c440d050944210301020880c2586890480c1c0c5081d041900c0f1052000000c0c00908008540010b20400b0300e2002001441d0700d55a1110000c841d191103800f480e486030001800014404001e4018803100b000b102c080c0c3c1064008007070030100325030854440060b0105601c21580b0700322241000011442171010761140000d003840701410900500030b4098200c1c5040311f0615411354007103400310035010507440f50251252441007207001492100ba03d50344150f210103d030000403001c9080c000c000d0340d20b601c1c0c0c18142550046d204010b0105404504100a000b000c200701402e01401a07403880b8103006d0040b04d030079032501886140b81a002860048800f010908c001000016a84c000b10011203204407146007480040303240c0783c0414002440d50181c0520385400207000131b46180483c0c450100c5100500f09244100c1e20410490700f80c031350000780e0340840c0c400c8030768508024078110000740003c0b540343c0020000c281603400650146800642c0041c40410000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 778764622 1250 778763372 778763413
    0x70309050901080a0c1202030c01030c021213290403060c021204092406050403061a0a060504090e03030709051210021602040b040b01050301030803090325021008041509080417 77
    0x840306079680214031b00d50003103551240d02c481c80c43d05042d6a040045407140c02004161020701740e00c0021031307030341c03403802282500160b00b0b1161440710001240305040c0d01a003902c03201c4103451002c40c201d003064a182c441c00050042841850b00790b010307942d0300d423442e030b04110000e0005e88516103010602034184888900d0f12080c06a060849041045060100720b40c408100d5080342d4119801240c540003845c030b130210f0045982036881d404800f03900001580c0360414041d0041340c0c0001c00400010005c4220581c492000300d03054800a803495606220b14034100341c8a82c1c1410040d0304481200121b0354004080f070b0b0244100001040c030031607020f011890329003e0391070040010384060100f050b010001800c1400180001480c950000c400200d0b121002c1082e10345000003000160f020b92001c244446104a80840c04d0f8085d02c00310440140e81801a194140a16448103c80d40003980244001307004140304a41103543c10410440090311640460440801101c00009441c100400011a40f141c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 778765872 1250 778764622 778764629
    0x91208060a0b030a2a0c03020d03020f091201090f0c0f060342090c091d1b042606070809120d06030b040b060a060201020c12070309050901080a0c 64
    0xa40005000b070000550719800d81303810000018004c00c803c1d0342c0ca01e8500322884900b2180119520000b0000703c007543c4400741d800e4a90007a000d0300c410000c202000c40130381c4038021500c0701071902000445e09900305010185141000700e80006640da1030742d510b6680c0b06411140c180c803400d140d40d005001e036a0402503102c009040d00d08080168840d8504802c100f9040440f501700c60880f8002401416607803100300d0f0400003550440035011a854140f40070050400e000e0413000034480d804003040350001c540343c0036030900c101c100d41113a540c0c1b07860608040320a00290342410400500002130b554100070700c01020103146149560070b80039422505072402d0801086203003045034013030501480e0071001c105540701e1400305103459a0f0308400024400606469840108100c91100820080c0071003020924090041281d00c821440d6491804034203070f014a0b03510304a5500400d11000e11605001c1c0200511b038403905184030fa00340e13198002040180260f0050886802c03120041c02041000c020b040c019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 778767122 1250 778765872 778765879
    0x706050403110a150e030f1c110412020d060e0d0509130912052101081608010c120506120105010b0a0f0c030e010f0e0306070c0501050105090103020d121209120806 72
    0x1d114280e01d40c900d12503d580d040084c0a0380c3c62105503407801c02813044a01c44001c2000850351500705941c002001441c0e5000350002c11310707200d8007442d1400840222000c4070464950b4450094464003002000480003000322280703651501c45414108060010010405035074039419110004001804441c1d901da0461301080380c6020100b60015066840e2111030000914103152a0048561004280c100c1420194040540d65000103640c0c5400100800c41400003003855074103543c1c94141074262013002595001051400340044151203ca0f409950300c00001080d42c128412206a001d003168401c1c2c0108580c00000901e002485170001804140860b0710b01d4075102080700f5480083c42c600c0301c50141c504000b407880740080c4642c4160701040b044c150050035604d00b8140b606001d000b03508411021903895091200004685c6400300520341200e4014043c210301321407541e00d001651061001250601100d840c64241991580c400c00c1c1b0014071070041216402d1071080090440c0c14000c06080c071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 778768372 1250 778767122 778767133
    0x3020915060f0c0c19080c01020601030302071202010e0d0b0615091c03121e060b1905090307350c0f12120706050a0b03071401081902070605040311 65
    0xd15894240031600101c41d11140d85494110003000709007081ca0802c4000e5001d098810341000e0341c08004102c03c1210080011902155582001643c4412003440050050f070030120082199a01c600c07541071030300780b0506d4640112111500010840501c0c034030141c1704000c08504100240c1840c04003a081503020141241c1480540000204540702e1003042c0700f0524504001030342090b01560000c4c403081645030040c002620688038041c1c41c11044841e4003011421b0a200007003580418003111135108500485140c5050403a1081e581a070003102103e070036200e4403070001406200746881994200b513600241020102c4501002c2c404030441002122980000950070010307510700d8000010304c20f040c0c80210402c0c2c0d48400050074007c030701300704098102d0300088420400c4190ba1141d88501c4410344100409481041030603541c0846000c2d8078404c2e0b062040c40441c1c0d6002d4080240c1c41600d1080d608441e0405028060598100321003c03204c40e616203040c08101074001c50318030100300e0700300c0c002c1c007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 778769622 1250 778768372 778768411
    0xa020a0321020703080d110f03090a15020408060615040f1517091b060d11030f091f050c0d0c020d020c01030c1706031e060f0c07021008060d0c0f030209 67
    0x651510541e810509101d50f601900c14a51100381f080d110412500c042c815224a81045203d8803441004e03002c940300d0b400201050000d00c3c070761081d04c0030395882c0c1000340115070722070f030070302a0f40400704070f4444190206120002e54010500380c901c02506585503007000d620000c0002030240b180c0760110080c180b0b650b4003003044000c00010015051906140ca4a01200203100841c00c2d51003041e46e03074400d84d810f010304120035954840045000b11b181c020b83c0d0300310341c2e560078115884030600e0301c8103d446255052044110b682c12f410158111200e16a0b0b146042c940030703260004c0b9410050300c1f00141c2c019521039018250140401e440e096021f0805020024070020000c04000200c4080580100c6500c04950f594900b00170083c0b000030b84200c20a00c501e0002d0b5443d40d034001c1211000784c040549000103114090810659040a5003d4510307942007008a4003a0b5207008010b088540003d21414400041020590f10707030014030040d0b480b2203a2600718014400d2802e002043c81807240c64401c1000e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 778770872 1250 778769622 778769633
    0x20a180b0406050f09040f020a03020405180603030703051c06060801290405060a090902180a091b0807020c03100515010518090601051b010522050c040e0a020a0321020703 75
    0x350504564081c07500c5d80d42910000040080c0b03801000100082d20114403003103d540c0660051056803070880e00d40700340505254482840107400c695081e01138005000a900003800f0364090840c10000e1008955602c6085c0000f00461721554048400100e11070010031401c420760781a00e02d602c407580d60041c0303407020395581003d49201e10310807240510b4001483c00c9078244200d19a10140030340342000e554500c41c501e05401c01005c9051040c5c4075107450403000401360b07418801d14502c6110510714003024099140c068803428001817100041d8082c01c6411480756509102d500e41c4220341c1840041e02e81420700d85410244001c00c2114180807040007509480e018128006441e60402c030303102d40032179035610700480e858002c202400e076010440c0c0c061801b0070f50041d0050b0740300b0780010840c61244000414800c00d17100c1510406003081d080011428007138145500300e0205507000c01c0443e01613812640c08104180c034a540f080e110796110b500702407010948148081602c0401e8401071000d64296181e6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 778772122 1250 778770872 778770877
    0x80415030507031b0f110709110c0f1c050310050d031d010c020102070302040906021b0c010305160e0d0204022a07080a0b2806061d0105030112030806030a0204020a180b040605 77
    0x212400d001e0511000e44210030204807c2024180541d000d10004000b24100d0526410508407014240545002544c8080740002c4140350b840c08420210385c0540800c10a0318a507001401513080079020381408035068442e00704129260f4480d9503402229502a00d20300b41c40c100c07040c0d030a0304100010001c5009072303a00050b02020391340c0450340054410075601c0c0410003841603c0ca00b0350762241b120074518801d0404206503d9010081c1c90a000b15a40c8900e68611a000111200c1c04034060b000200110f051419401c030034588046c100628003030b55001404840c210603070f2224184c103103025010b680c0300014412940107010b04001043c44545a071384070308280400a141c0801580140010800c125200c80080c80765003c040c0b041100c26203d07000200345803900360680510002040301c4003110751095040341d040720322140e010103000456a0b0304868184c8043c0801794548071340584240940e4417440140300c01800c50b120b1040010100d14040d101041c19400b03a2000d0303805200c10800300b17400508 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 778773372 1250 778772122 778772147
    0xb040204181802120a030201060f0b030a02090a0306060f1701200d110301060816080106020c120109020411041a0315010807020f070312180b070609080415030507031b 73
    0x201054494820400c1c840b855699040a913109980414083c0c08600206007141120f0096000b80131740354680b001c140003823a0a20904828180c208005490804141c0c083e000c514001001c003804180d0740d48076502500c4054002c4481102080c8003008005120503050084000001c000c0c098509100342e503481c0d081c0801d9440c4003a00d00081c602d590300216a22070b89600c840c2c400030315240d584410340213206a204440d60302403916041a0b15041034065140507040b81c503168014a14030508005200907200c05031820800b41d92155904d60060380d03240500b48400f03000399203040e15a03180040407007a0110202000e240040c040003882290390155903090900c00d0203080c4200c0680343c1071001c920301403008039112420700030b042021081041c9094041c0c3d44596a03039178040340001c2c1d072468240b01035003485004581882005060000386075504181c0c0243e004920301d07410305568280021806080e10303401400a503440c4100a603180c0c040c4a20300c010742c3e131580c2c100b842400d403000c05004200c40303c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 778774622 1250 778773372 778773419
    0xc0f0604020f1c0c03110108070c0b0601140f03130506010f0b040905040206041d0f0615220f082a031b040e0d0309140d12050a0912080a0b040204 64
    0x2240004104645103d080081c0c1d880615090400d40d43e040000d103c4040c203072918001058000030815852140a40840903500080507505030340318040195800d10800340c3d50007582106001c0c110100e004400554803401c0b80104810501c00c2ca841c1050810704143c21a00b00750311003210600c002d00400080e44c0c16140c2c0290b002515448a00002d482401641d00ca041d1000481c0c011b07540c00c0150241050140311180405100ca0b10386d00100b0240500103442811650400e10840764541d0381071b0382c0b21103115074030201c441031191180701c0c58446115981011407698088c80c039400d10b0030b40f50b0b83c0c01d800300d2284800c460502e074440701c002611006c0800340000740c121020007251183d51141c0c40051280c1d05c0070200d920881c90bd000c0907000c1c0a0400090b140d45071301490013090b00340f010900402c28410303569a10b8494003106240c40081001030507506070943d03510245d00008415561841013505240c480c10007074a8050341c0340007034841c486d0265005500502c002c02c0070202d455400241c0e080c0c0c08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 778775872 1250 778774622 778774639
    0x150106140705010902090a14060f1c1e03090806090a0804140f27010503030306030622020301050414010b030109021f05090a0f08160f0b1c0c02030c0f0604020f 70
    0x242002c2d400741091040c040d42c021054004d01440412941c0320b480c65000c3d10b201888690703101c604004031103480e044101d40028a40c0c078041d0b0400c60080035002c070035100d0411002460a4a1500e274001000440105d0106c0c82440051002000130030000b640050040020034816055a4440429003c0c601c181d1500d140011944419591103010440070b10324007600741d942e0425280100990b4009000f0a20655031a0100100b0142000300481c5d11444000d001403000b9110034001110345c4e00401440c4000240c075000d500d00694081c0200b40c040d034010b00919005d826940302d09030848a200041070300c030740c0c9410780801c01615003045080054800e0b41030000c040c6000c43d41542c051183c0e074030865208040590104801454501c4072068400b00812103e1160044101951480c138a0181ca0f824000890040018460510040c001c40480302e94502038800107d641c00146c03120100c801e800360b040816040014441000701c10340f91444c02c00185954101a000302c2e00c0003170001506409110345 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 778776978 1106 778775872 778775887
    0x5180711251226071a012402151302040204120c060810090b06070602120414151303020708030a03020a0e060301151215080c0315010614 60
    0x32076641a00441c110b10405821401503c0711100c3d008100312802c009420076001c00d00d200090070070181c89504251042d4482040c0c1000191203642c21800500e00c00e50019003040c0340c460b040b40941c1c40780ca41041204080e1903508010790010300009000940e0b80380103003142612805007066441d680d03100d20080300c203c2419a980003010b280b545080c06445881e50000c55400d4004204d05d14060042d959682640c00c0041050000c080c0c000c20041401940010840309000c1c6102030021820243d80007440c02c0d070702924039004a0050259030081500030441e80c000f80401d00112900ea081c50318006010b5446800790030000745049407241c525060450a584c16903290094440410300320000c00c507128034168050005881e1030b500600148241c1d005d8190292003003102500d8981e8503c0149072034182201c6121102c0d0b001c030f400401c4601d030f009400e06c0c50101c440760706035507941a = true := by decide +kernel

theorem cover : BRFrame.Cov 778597122 778776978 := by
  have h0 := BRFrame.cov_init 778597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 778597122 ≤ n) (h2 : n < 778776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
