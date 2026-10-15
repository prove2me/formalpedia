-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4243
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:59:23.426501+00:00
-- url     : https://prove2.me/submissions/8e3f7e36-09f3-49c4-bfc3-1ff8a477a5d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 762949640 ≤ n < 763129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 762950890 1250 762949640 762949673
    0x307080a0b0105070f0c06080f01080a030518190e0903070323040e100603050c120a0c030216080c07060201020a120e07050d060905010605060a0f03240320011b 70
    0x3182c50110542c44016180200050a1b207940030008401c0103050b034041886544000781c0c3c4070003079036541410000c940707c003120400a0108003000c1030000c00004040e07000410303800010300441c0a500b40f84801249004a84985c02c000048100004c040d0000403048034461541591660495072070fa281080d00c1e200d42c00c070300030051201800003191014911480a00548004109408140c5820350041c00e4800003040304a0031181804403401001c010001d01c3e410050104000c1150700071883d0031070007400b68401d0450302c544103107220303024401c031280140300310314600c0141d500090702c40c80164280e10401101e074002039004060707207290020a60200700b40c600403505079007807913964400103030002508900c01d450381e41d9100c006a00300103007440382d200108800d6401c1407e10258a202400c0020b0312003070b40741415203d05094804000c40d205ca01d5580030030304a039040301ca03203034240315001d00d070b04060440500c403110751000565130003525142c1650745400d0191040f05400d03031307a02004424507d030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 762952140 1250 762950890 762950897
    0x909030c01020301170d020c011b060b0429120606100207090212061216050d0510050c12130f12121d010609020708030109050c040b1201090e030307080a0b01 69
    0x109009415007800114020001c0c082400c0000800419550600307040d812000c0541d88991031001c23099810a000040d1340b0600555541400003505254000d0151907070f8040d8020b00c2c100c800c41d00c2c000c0c2c0b000510f280b026291124144240d034002840604901f0500850135076011f070001624910340358002c94031a5149106607860150750b8440402642c1120a01549010081040103180d047c00d02d15610f0152880d801000c10800300e020110b595252401042e02401c11581c41c00280001007020743ca40043d90320f0304100a1400308101d0006810000c2d02d004200146004a0362913440c0702101c441542d0801c211002030711036661940101200329183d0350134404002511614005148900440814001a100c42400d600c2c80300b24210f806a81151902a1040c403203400803a40c030500b52410340d103030540c0c00a06a100c252404440780120f50000307419410010710030010201480320107040b01e48107401888a602c0e00300400b5100e0008075058000070314102c0000b82814071540080158150605 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 762953390 1250 762952140 762952147
    0x1e03180d08070606031109070f0327050c0f06030424140405150a020414060a030e0d03090c09090f0605150d0f0b0a0203130b0a060b04090b131505090903 67
    0x1079655500e0382000300c00340d9202d035461508005000b00860001d910210464400c40d052800c1c98010344080d124041c09000c056444d501d020340950803d80c0c80740e01041002d40500035200d21f01d41166030702c035a4400f59003c2d0030f180501600764100038056038043c2d07a000303d808401596199030150a600d05004001c004d81d101c0c80d5640b064841c4c2c544440c001c0340a007002c0c1c0a800e00340d9602038100440139068205003031041004018001a15000a0740f01c401261130641c0c5140892040b809440c000d070b40d921b4503006000107490040d8240d030180d40814070505103624065510070101c03049401041b07014040d0481c50310810000307846a80010b034011075140ca290818401140070500d540c5540b14100c4801102008101c281711410603050390140803c50154035600d04ad907220030765840271940c000c1c41002ca02c1e022641800c030a411000140a01c031990039241c50303650300301601401c0c6111803140603d8000c141c0004002c018056500000081106892114034040501407800401082c02d1600c0c081030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 762954640 1250 762953390 762953393
    0x3160c080301060206040605180a0201050702190803030703200723010507050c010f0b030d080a18061409120319060317090102070807321807021e03180d 67
    0xe0000e14041e001e55802481603203028a04201207038000360069414080604010300c02034000203020040743c0d420302e48591100e40c82e1001c682e021400b21400f1010700ca06041c0441c034904000003441c45403640781e80c10711140412a82a03004094020407040c450b45c02000b4010119a21407411303412441c4142204004081c004000780c00c40344203595010005400140f10003c4c490240034604102050100030844526a400001c3c2e5034458820b030103090281050004103070800316405201580c0882502140c960383c82d240c01c1c030041a072202c0d01080314004001007206140005060200240c10f079a91030b00e19100c040380821207031104080001110303212034000c00002d0007001c4e40b80600700c52410003515440e07481c0002e818940380c1e4215402643c0311060401c030701d040020042028920503a1403001d9003030312480b001000401c43c105541c1240050364a0544105081101031040040c0da0036580c4100c5d05203c00d1410b902d2907000c1c000c1b181c0c418003c0d14032106080c0841c1e0840180103054501c031302d055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 762955890 1250 762954640 762954653
    0x1e18021005031506160f062021060d0b01030804050a0e270705031002070c0b030c0a050a091212030c03020703050418061d1b270f1305010801060b0f03160c 68
    0xa034071b402c8402c1ea4803510550181003000700c683e0782446900c0860f505010090900c040401c2c181c5c9a00c0941070b07502c4c0e0105516407142e80c40e0070354464004110910540c2c481c103011030a43d00a1051a00480d01050001920b034000003005000760200c0041c034111a0701e8200b001c1c034840e20070211052038002d2400002d03c2e5a01040150000312034610056122626400c10792150420b07a844800b16100030001c01c0311050b80d0f002103550100041c14019290f0704901c1d822209490250843c075404c100e21000f4105104041100134021201641c0900c40c01c0000103045041e070240341d10080215509120601504041c032032540d01c034148480e80001e00f0313a13403500030719400040c104001d44c0790202c0c0800d024103d880021401a444045420302c1d1130010902001c403844503034180032881128404005810755500c2311030320320040e90700411642c181907440d006100201420702c0360355501d40c6070100010354084540305440d54604217015050942e5200ca00142100121342c003890100a8140391f4800001c08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 762957140 1250 762955890 762955913
    0xf0b070203250b03070e1503071b061b08060f0f060703030203150d06020c0f07050604060305090102121f060e15030406090b090c011b0b010312050403060c08010905281e1802100503150616 82
    0x4260798de4802c6081010a12480383c4000b01c090340142840c3c500720310152100c400f100c8010350306143c0142c2e01e03950740b000d500070700b4000450180c0c003804000c0f0900c02d0001a03005441608081000d992000208141695840030076100e106d0300702e8002c0c042000345c580254041c82c1d001100600161500000c1030302c21124200485010b40c0c0f801410208850010031090380101502c61400c10007013850310000010021400d0382c0342055110800030008003080400d41243d01c6143d0700442402c107030300b0028089500c9540c004441782c00101000014441c0f408806070310000d2640024103010780e40d00f1900d03076003050700003501150180304007008000000b0701c0368460142000d64035602c4400b15410042da801c02c0ea040a0240c1aa001c0c2c042150a0751100c80d02c0142a076150389600007641034441d0550100401400000300c081619141350050091003404002803118400c542542e2101c20003001035030640421b5030041c0e10030f001984100c18508002000780a001d1602c05508000350455032130ba4420070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 762958390 1250 762957140 762957191
    0xe0106050a02070e06010503160507020405040c210210030527100b010201020c0706050c07050a1806150503040f02010c0506100f0b070203250b03070e1503071b06 71
    0x4800088050740680e040c08540050411041140124100140002c0580c00017901c04a9a146480d00007003030540a00700f200c81b040c1c0c1c0540300f40640e28041c01e00a046017200c2c80f0790f558003904d1254190412910b030100c8010a0b9000b000315420321a448ea0403001844001c00c4000c19079005000e801c4064601a000100000e00313038002e11a2138140680c0c3c1064400a040c03030382c15a030050000c00808540030901d0016505146009030711243c01c220620b00e4100d00d503000301e4011421000116203c03840800c0209240000301c003d10600355100c6010023100150b8021100042c414000705000910b0301c0c0c91407440d103005140c03880f140101522440e003030030000c1d5031002844206a104020a010310b8a200c0c00074808001c61504101590300813076210340b000d0f950541080220003807203003680e0403104064040d089141e1119203a2602c06000303040304d00c070880300502c02c10104082d084a001c10100302d9201d5601651920802103a400b101080030b803060004450064544c0d001c52071642c2c5044e120303034024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 762959640 1250 762958390 762958397
    0x8060a0504030f030c080424020c032206090b090103090602031f0608090a080306040603120513050609150a030f05070e09010801052205070305070e0f1f1e0e0106 71
    0x1820700740b5002d403100d01d01d01e1116080c0740c01c01d0242d6144540103031034680d015030003000340a014854081d601c041c0d2051841c54003041480855183c4483c0000000342540c05038802d4a03201e421099400310001c040b06205d030740001018240e051111510700c5020f8481a40b043c1800700300078007140d4880301680c200f200d143c49800c070f82840c4580c0260790880424000d21803820940014101451041e0301c5605410001d84108000030228134140c5981c0e211000940d08190050311760040c0050040142d40302402204040001040110301231601600312241100000d20100300b01e003000d80d0b80c492507000200c0407014550380e000d0443c026425801803074802c0c03900740ea44040c804c4801c0c0407c07000c650181c1009045a14000402442d21a030600d620301d03072103850100090b500340c4c601e00b09260000383c2d040100203004410000504102201125015016800b41c00350966030303d0a94840022042643c00207a42c0031400070040d051035180e0302015071460482d8881c04503120a003003020315a0a13484030000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 762960890 1250 762959640 762959651
    0x10e0c03071b0c1410091802160c06110708010c020d0e0301020909040606050312160323040602030322020f010e0f061201030b0c120c1605010c0f0207080a171308060a 73
    0x2d117040000003050b80424142404194141441880c4c44580d8400c424010f60703000620042402224008980c3c107540700f44046042070f240d050003080c91089507101980c074421024027003403840040c0100d18041401e80e004100d6a40f20100440d000c0807920701c0203406550812000c0c0c01a1641542a0701c070700d018002c0800d5070751414092600d849203900010301100c40502c82c56050b448c0803080d5039009605440e142401482081c00c10402c81080490002c40d5840001d00190041e0040041c603c920030340d401421345180c201d0501c030300d0340d003c56800a601c559420762583c0fa039800b51083e1900030358054588001e481c04600402c1d07803680070b44500c081c5680048010400c1180c0110311952100b52407200a00301600300d405510035520180548010710b0b40401c2040391565954681403405410000a1101141200001c0c00840c0d080c44044014064104085144000014080700b0301e0303400300c82c0360a10301d181031942131140c2101004510a010300703d40020905c5040003402c2c050f201d02c000c0044c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 762962140 1250 762960890 762960929
    0xb1806150109080a080f030c0417010c0201061d07140405040c0c0203010f06150807020a080325020d1209020f0306281109010309050f0f1005010e0c03071b0c 69
    0x60b500c055202048507400703000310000180719101030f204000003075041b03940c132505d4070341032070409008030b412402042200040501c4001d005412a04002d00a034000b0400a40c03903100203440801d0861400444103901408211064444c80c0070021902c40032140c2401c198903100001e05460103882c1a800282c154920001986400e2003016510912036102300f0415140040071841c28440c8180b03481840030403400101014002e004800440303901603039150b0780785041483e078251006072030351b40000800411010300405000050301c40100030f082d241e4400c4000d0701f00b040d00c0689142c400c00c0380c05c085071100c0740c03079039417003c0110b18002e8038202c2c58507100303180e0102e50504580c04040080300c0141880300146140c030494003140c80c848003e19020070f1551072802d000c0d1400c820200e404540e4440c10311764840c3d03003601140340202903445039014451640c0c1c13811148508a419200070902c13440410125800500540150b40d0001240600500d80d0b01151901042c1d1021039014001104220300f2401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 762963390 1250 762962140 762962147
    0x30d0908010b0a0f0611101103070e0906090604111603020102120702070e060918060f01080c010201061d190c02010609111e09130221180a0b18061501 66
    0x10400b00003510000d48003850401c2c84000c040c26071160340207002e46c1d000d171966142018480c00542a84e07002d8184000d5080c200e0300c070302c164001c48402002800d4040440c03640d140c1150002c0c040e006c02400040241c580382e0800c0000e0030510120451040c00300300084008400003c8030340c21038000d400068440090041d04980040001c042e40f00b10741004000340801420f400103250050420f032008885940c610080d20030020741070f255083d45211300001c00052100402495040c1c4d408501658074035110070740160b00343c590500801c9132507104d220b40080442d03a030060003580185101c002d43c00d03205081c00d80e40200c4500345a00f0b80140d469210512041d11140a22100908210580d9182007000031012080c249103002454500c1e40010b40c00c51176a8400000d80b00c800100402103640c2d1044144901e03000d180c0c4054040c40d901048001000013507504a1071b000c1800c407078040e0580d80540c0d5508203168000400003a000d881c080740c808143d800800800b4410b811018a10313110140100024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 762964640 1250 762963390 762963401
    0x5040f0207030e121519020714070b13031119030b0103051e0318011823030c1804030912030807140901140927180c09040209070e030d090801 62
    0x4902513603806201c50200b400000303010401000d100e541d0003090703d0349420000110403040d20250040d00100701c0c42c0038890721360030222400640c02c1c02c0b940c20590300c80340c01c0e4581c01062206144003080442c1000032584102e8a404409002828400000084030402c540390f80180c01c156081d8138004014400c029040200980041e03c42240600c070103890340040d942d1f0303c02c0d100d60b0084203c0403803000240341d0051400078203418440040d071003419201c044500761031241c0101c1019849082c1941011030501186032483c0300c0000d002400f442c6e0014081a42041001c1c004504001d1800000518400424150301e41d0b0b81c801d540d101410b0610007030040004020b04c41404c0100030400101449a070481038142c22210310050950302d0701c04000024800c05800244c00e07d02049500707030089002c0ea00780c0c003103114002c0c0202c140c020320000440b9031b40d142400649641c200c200313040800c007d89480062154001250f1811102c000c0c40080440d00b4801c03042a54004200e90000030311401d002801034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 762965890 1250 762964640 762964667
    0x90d12020702100e0f04060b130902090f15090402030408210603280b0c300f18010f0f0b0d0206220b03070203120f04210905040f020703 60
    0x941c206415500041d45084001a814040c48004a620300c900d49442c076071405160780080041001c40d9503400b07400003a41c00390140e100d100c284000046003840c480d100395840320b000644806030740104c1100703212134410f040b64420f80613803091181c02466601c40c001140701d984210142c0791102c0208a49813403481d020704a100d84819030f141044a00d40b8009000c040007440b03501681204034400ea044080c02c2c1107044080c00064400041005076481c0300c0041440c441e4200e2915129281c0006030060600340004260303601000b64081500c1c001e243e2a400c3c3c004441100d81016011308100706400c50384801a00c10403103448004e11411035140f841001858601501c0c1c0c41c0d0f04030700316070018980340309003002d018000ca589181400354401601900e130180c1002026140d41c0d0400b00c2380603569030800301c032040103100540c00140c0007020180b840d6001c1c5611131020304202c14039203081d0354003072518038010007000a2014005040e0341d481c05949041c0d21007080042c1e40f80070f40d041c003c0600145201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 762967140 1250 762965890 762965927
    0x210c0a1514060f1e03101a100e06071505070905010e03070605040902071b1404050c0f1c0e03070602040e0901050403050d0203071b0b1015020d031a040203090d 70
    0x80040c40d85403040c0c404002c0108031554024600c04d030300a84000d40d204201c054042c800c200c007803000400c036a44049440c90050302852500c900b800200071021000e600c0220010f031030a0000442c5044c4100130308004c0f4032850032084800c0e4901e02140c00c40301d040780e994000070548141004956000310800440010a502502c4110704050b4058507d108903c56043c007240d00041d0310b0180203280101c01c0415500384210560f4664840c903079201501e44020a610481c60100800c0307600100c80120b4004d20001d00b22541068207217880342000d000138408002c00b85403141030401c3c8140e0140010300031988608401604d982c140752010260800081000b01c55030314000500010a81050603a000c0041400300542c1e40c1d6214001291000360714400c0010040a900b080c500b000340f6000c40c6d85c03040c076210600c441c4e0707982d030f548018890300c0d50960070700d0142c0c100c641120f00c0a44250008601040d001c100030800703042d540e000c54103d070b008580c0d1500640041014420241d480542520306010440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 762968390 1250 762967140 762967181
    0x30c05040602031e040503010c0518190302060c07030804090e012003040b0a09020d0320121b1501061e020105060609040f0f0f0506150c210c0a15 64
    0x507000c2d54070700c074124506141d400140213100164200b00112806400e01134000d02010400c0c500180068100c00352000508020340d51510f0705d814400c03ca546001403c3c00e58001c3c191854007031004507486070040b048180074540000c800300e640c00000340700030704051100003004e4140b150b00c1421030300000c40185014034154951514201441c0a41e600150821000352180c0c4070490000000c0c0780300240250003003400381a06091540000071519021020503103160050190055691602c1d0100e054007100316050100c0c44199505440308600c0450401c02c0f01c02c0c0005120800c200c2c144260301c20b600240103413881c04200e0b81405080301d50300803140000d0107a400c24a00042aa020340703a02140541d5a03050102441c0300950444940a00c60250400c1440b04010801e00a00030845100d40210500c03140b104401140c113080f1884881c1840c00340c910030060000b04841d806c082e02c24400d15602c00c3c010126140e030107018520714180310b244041c41320080000007c0a942c40880e52014541416 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 762969640 1250 762968390 762968399
    0x1181d061005062a0f0706021e0307030903030e0d05191b1202040b040b091003060c020d02121317030d0c080105030319032025050d0f02100e0d030c0504 67
    0x318041d00c01004107030554900c01d21135220285864071940c0d61250741d204410001800315008103c2400c4254151403448480c0c129840320340d034074070030079074020005904008200042840744019100c0103400400400204249840e41840e10107442c212403e0000e01d40b210a041060580d01d41000e501c800c0725501c6038518214a1000d41880800080c1c01652a101108415650f43d070000b0a0503c1c003e01103200343c1040114200b400c5114001106d5091401044c682e82c3c41c0000359085101c5155801000140d11100c11220349820480d441038025500580c041048110511002c1d0b540381c16100031911880350461000c03d0352082031032842402015001404681ca0220841c0d5903080c00c8444071040910749401100140448492008600302e94580e000d541407100004000100010b0030381000403200c400145035094024400520741d034011141d03426801d0140318040c04c10051350058800c2c80c2001f24103481030319440c110784051500142c41c656a608d4043c03041c007030381b5041454014101402c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 762970890 1250 762969640 762969667
    0x2010206190f06090b031005010b1b07080102120411042013180905060f390a080f07020a08030a0e0304030507030c051c0b01181d06100506 61
    0x7918031801c520840300d0301d007079080450300406030a09619008000080d52940304000074070015440398464041c105080c01106083d00556043c0c0760b651802902d0700140d994800b2200400e0780c5450440e01989030001804a820710181c0040c0403800c11a600b249424a0010642c1107949010380c801c9250100c2200c0c801100032904000280d1164901ea5503d84000301145107200c40d8000310024210f03030f52072244800c0c1500042d0800e446101260825100c10781e201c0e0801d14200c8040c540c4a86400c441d001c00703e4101d080354801d844100450001214641c007441d4a6400083c42c000480c14103010701c89007040600441c0d600c040c0c0e520281072006299030313034000244000707004114101e40307c2311002d41e010401e200700e0300190b034400d04a4001179964500204c0340e204600c070740c5120380f030b18071700c00e41c101300200304100500355100241d80c005a08090040c050684000d6540020540c1c5844080e00948040b031204004412100209510f28018880b5006040306c2d0300141d00801c014001000e28920 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 762972140 1250 762970890 762970903
    0x30103050a02010e060706052d06280905041a0f060d021002070b0d1508160b070f0b0f04050d0e0a0512121309060f0302131109060c15060904020102 65
    0x782440e01004013040c000c00600341d070040c1400984082d25110034011900001340601040d1076041000340304e40340588a0002140008554240d0480c03060f6010b0700ba200171030308d564034010f000700c0206910b1a031506107040071078604540c01c031070506251440d509101e4035036031000c0c0c0c04484004484481e00d00311002c9a810402d005c002402080c100c0c510708003041c003e0090f50003400403e00e015484071410f0454a015000080c400c4448002d403000201b80c0c0207000c100000c10ba40d4420307140074028641021a8120360051405440a00c400b01810000803005405039002d59100040311b0312504090507d10304080d10012400305100840042e43c64548400c1c20040c02c81c1c0d0100c40b40441200205111810240c4981030100e0100700040c0014950b64450405000d5883c0003800f00003083d03e9104178440000c05000283d8030001c00700e039001c0b146180d5000440d500c4e8150b02c0580c20595080007040ca2a0804006d4801540002014042c4c202d51000c8030759006204660011782c6041a40000c0d44441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 762973390 1250 762972140 762972143
    0x90316050f011805040e0a0b0a060b04060c17030a0b0405010801021326060c07030201060b090607241503032c1e2d090108250b160b010b030103050a 65
    0x83c04521400030020030f070048000303050140081c00291030a00086480340e200301c030101d880101c1c400208502c140302e48100016034030b0801d1054503080c00e2983c2a80d929801c5207080b0f0380050b00b03a050792441e00b8464051405810401c4010139484404000c000030385a05820801840c0c0c03042c0002c0808030b41901d10002222081c464010002e141c0c050105004600d0001100c024170032102400300a52040d030041c16030902a60003000031585860030044948521441c1961126040c40340b0004500d8080181c3c0580712040e2400c041c05d80e45600301c60a031014400d9641c55500540410414590410550514078001311400346041004140140f5006c2804d00380d1401920010a17040000b80510300f110043d440040c0b0154031011482d0650710fa03284003000315609160400a9a4428144910000c1c183da56030030140030315080860411280b050480e003400320080714a04001030136252500180414a4064010218860b582c201101c10180603880000c0000c810001000800c50120300005e03460f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 762974640 1250 762973390 762973397
    0x50a030209030705030607080603150702120901030e0d0201021b030f07030509210601060f020105070c12020703210f171311040528140402120313060302090316050f01 73
    0x70103004010074070385546500003135050b104c0c68062164440d0041d80591188030101c04580d044131807a00c0301011550143c0f80c11015a01201d5505032101550000e00b040c15018500041d5055150303400310f12340156110b101001d42d40c001005214182c5005851440c12800c4004510300060f0042c1c54043e442000d0b40a4104a00450003285a030b6075641c04004000d0104819100403440e40542c60310381c0005c0c411000460655900920b00f0b0b401070054a01c107603006d45400c450403034981c5601d01f00d000030741074640450080c10701c0031000942e0803041c0325950705c440c031840040c0c060100340031f407400c0c440322034030740c02d00c01c288552701010f600011400b0351140400e001d08106140030f203095203c0c2c1c42c50003901a8070a051408100a509955060404540322900a0740004209182c888102c81c042d200c0340d104105804005000740c06c3c400500c0e00e0022940d0700312071403c0c445a90948882c400d54100100082d000503441070686400c200091b0004012416090118500400070f403c032003070141146d052 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 762975890 1250 762974640 762974647
    0x10e0d060b09090d030507090311040b040605030f070314030301150f1e080a1a030309060705121303030e0a0b041206090c06030b010306140109030b0a020405151209010b01050a0302 79
    0x3000940c0d0408028514041d01141c0c0c0b90030b1034205143c0310f000141400c0c0c0080d10f404002041030744a5100070003200c0c0c00124141d107164145c01400042c01c019908260802c0e00d85800045036201009200100d032110009010120b0840c9410303018010300e0000b502c0c16034001d00041c0500d001031003400812980605160300d000a015200342c0c1c00c50010703030940041c01521281180c1e21504107000500c65104503008100000907078003d0314900702d564952580542c01032154680c542007503002003081601406c1151003500382806d05081a92043c0b05102c401040c841c1d04004160300964503240c90003003213460141c0a41003241d100034074005c40c804c03014184800700802090010350b07070141070220340204d100c0724440e480fa003001e0007038401d001c40540042d1400768001003c0200546024803114165034504495285440d005940100079000d00c1d003042d4200000100d07a0780d005120002000c80101c0140c6a11503400311040517400182580c103164181059102c04e41c1e404011150340c40c0c0e05080060300c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 762977140 1250 762975890 762975893
    0x80111070305120a0e0313031b0303140703031d010905100b0607020d02190b09100c083a1407050a08040830010f0501050403080406031a030a0308061e010e0d 69
    0x1610786044c2411711030100152940c0c0c10b0074819900c0042d00d01514420403240c0c90031481089c0080588805070001300031368070b44c0392140702190043c100783d800382c500400c55400c02810071107030b249c2d40901500c450395503181700f03401c109081c4500f2441400b420005c01c1082d03c07450110b4214415100021310075144440000d086580300d00c10303440700d8003c08a41c20115521564250701c2030b840054002d00c82d036140e44c0742075001c030f01c03c12007202c1041e4000200c0d4285001440480181f00714681c1458004a0640405200d0b484131042c1126100366500c0114001c81c0d41c1d0b40d036560b4680060105420042c003005081c20140e000701249030801d50000044c0d40da140701c0908101449801c1010103828000344040722492500d1003a8075060742d03411040001c0080e901c5005461503c603601c001455000c060008200240c02944a210741c0d02d5154015100b0070f41c00300000b82450f001c0d40c030450104e148441480910b0600e90b2516009450302d5405ca0380b661017500010b00f031100325800041c4121030481c80c000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 762978390 1250 762977140 762977161
    0xf0e06040308010b210708060103060b0c07030803060619020102030604181101081909230114011419060203070b01050603070e040e0c09070206240d020f0315010f08011107030512 78
    0x104405c80701c42050501307090200408180702a160f09001a0070042c0c00b0918007500d40886041c1072034240106000e0f071131030b0b661881ca500300405107984440c080c000c0201c400d160340746010350b4200396800140e072494001c04000c200c810189032146840019407011000445000740780300d5200007400c00b101e075035540d07030000a500d89130060001082402d180850040080300703900c1d042001da080c004803900244144445080340c4100b280001072040c040d0042100f0f0080302040e100a440203080540024103084c001d40d58204582d01440060380000b850070140042401418050172044400d6440e41c181000010001075030303840a50b2169903218810301a0380000c0100304200c1402500c0d402007841d00600194075200c08950030000c500c51801e035a0410300b20841c101010b000300a040301601b51540c0c092140180103c4a403036014800c070382070786043d04102052a4002c0890400341900c180c2024222030175100f00e4402c1c4600e00c0b505218800c006a0014151240f07807038181d144841d1542c0c0c80102a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 762979640 1250 762978390 762978427
    0xc0807060f110c041109130b01020a12021213051903171b070e010e13052107051f0606050301050a0302010503060307030c0b19020c01090306020f120a0f0e06040308010b 74
    0x10340d002d4504911740310700424482c090710074003400700c0300c2d00d0300c1c050040c4126041d40c4440c808140140c10140421000411a080101521080784120381c0a850007400100c1540c1c80070700d09a0002d89004820489032a21b015080f1090b051085401521031940c0d44107801000300a82c1222110307404100b485a020742440f01c00c24040d5003808450406a4688a98480441c2030250a8100c0d0001e800259460690404004415403000040404a02400c0200c800c415405110786015400308008400302c0c500300a11710030100b98025415680c00c0310181c207000ca801c168041d9051200c01c0c001044940c0d52814001c0c00c90340c080c28103583e05c2d80c0340b000083c1005103607040200399011070710300880d10841c6400a01444400d0f005003011542690805076926184013691500003a0003c0043c000541c41c2e401420400c0002c0300c0880c140340380c030300e50318018040c11107100300701c141c3e03951051184c052180900411840c00101912540c20143c40c000e0195005000703824401200055000464030b000440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 762980890 1250 762979640 762979663
    0x120e010f050d110f0310050604030c031113020d050601020c0a0e060f0f0607030504030c2102010f030b0a03050616030b0607031112032409010506090d0c0b040605070c0807060f11 78
    0x240d54a09803d004450035800c240e4001c50540342401001c1f8507070508034215000c3d02e402001803100c4c2891a51039203526820f030090f40e90000b007600300f410140d913164009081090b481a002080ca0300e40400020300d819a05095030744540320002003044002041c00c0703299000402601c0c0481c800740c00c10042005918800401034120f003001a03d603080c5540a0081d10a69110301da0101e8041da54010000c4a005111b900d00485840320001200541c0940031102056845041c0400c0b503040d4480010f21224280d48180d4a07900440d00b0010003000c07100c01104050980c1c01d02300500c10303400b4082096805030520040c00c2c0841001d007002c041004010404181e48650b0026940b8581885081c0c00542c4901045101e16000c405000f0186450062241a180050070309400d2142905c10800100d003e401c0a680d940c07401322000c69200000d900030005400c241e111030f0340c0d03504140340a81005405500c0030b240740d0801e10082c01440c1e40565990340142081c0b0700030303440c111001581414440345000c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 762982140 1250 762980890 762980921
    0xb030c011b17070506091009020108061c0503041203320d0615030b12150a0b0f04050108011d01180807140706121103040f062a0309120e010f050d 64
    0x11240e01300304001814034801c0e04140c05860701554010400340c15a218182c0090114400c440041d83c1800c0c1440d00c46c0d903500d04c1e6000d18000310843d4480c1c50446d0b220350020b4840b09950341081043c503400000040c1b1150558004601d865548024141c0765040c4485020714884001856140310740d07941c1160002c0c254203956080b45c001240b402400401211124502441d8580101d0306994004611003030f05501c1056281410f036114001e25000341010f804a641c4000409590f03000c0e901c461007468041c0c2003170000010458070040071180c80b8040c2c5d07681d00c4079580c10300700802c00058022420340c40e000e9009120a4170340400380780c80c3c540640a45aa01a54421818005500c40d404a0290104e8403402ca080110200300001d40215110440b409082e9403190b5082e140003c00741d500c0300c034004004044111046c505604040340814515510000080d1251910070900c06418144100f80382141000d203110540900040c00031824600400148030000c2010202404160022004880d0400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 762983390 1250 762982140 762982147
    0x7030209060121061814190f0207050a060e0f10020306040e011505130606082e0902030114041404030c02030708031303060f06030203101109040e010c02010b030c011b17 74
    0x6030300c2002060a4170a8281c0c1c2d0b941c4000c90300d62100d05219038120042032800915540e42d55085000c204030745402c101010955601c1036411951013480502510b40c4644068010110b19040c4032043d13646011144217560030410b440355170088000784651103168003402c05a20703913642c0710024004010304d654050842d42041220250103141965810580d242240c150b8107800c0840d402004441c0140221004140c6890100300b007505110306000c103001112460242c2407512550076010039001d9400145540d030040014441c0c0e0184140f107072010b03030041d1010403a0076028600c1095501300504083c0078412200e140d0015510140050b0002c0e0800804499a501510a01440d605554441514800e14244503181191187c0c022103007244d40040c0200046d812021480005166201c40d041144c0001c000090705501d0318050156585014800003c082e100d0700000b90070348102d100384d03038444e401804031540c03136a8203e03802030402c072103407070700400845290314100c400d0318110304e036800c1040d8020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 762984640 1250 762983390 762983447
    0x3090918020306090601081b061b0615060a170a09120c0507080a1205210a06051314010b0a05040308280203040602072102100e011808070302090601 65
    0x403103000c0c065a10960840b040c60f0345104005445200c00e00451a054010004002c14054111100c3c1e108500003490a49040b1041410f9001c00c440c4120345002604001c003044810032510340c01400009007510030a150809214009010f0031035210b5040268102da00031800717200c500e40c803084289038080e0015441a50f0406d001d880c40d20421400c0312684103509c0003203900c98002c12040303034981d031000c20f01c070701e00c2c89900c000da80700e03041000b103c8116000c0d0501c00e28a5090306244501410364104002481ea0a00c2d00340858141710020bc4000c150508255030400c04c11500d0060455140303562041e15070085030011520b9118690000d000440b01041c51500880c04043c05a00d140c10514020180800c000c0240c0c3c8900442c07040d038000d030b000340c0810004035012603a6442408203040e242c02c030030b280e04d0340081c101400b2981da140008a00d01c0301604203503044010700441060440c442841e0702e141c105030729540c00346030000a019103000c0011500507405084d805041c20312504032580e0010302c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 762985890 1250 762984640 762984671
    0x101206180516170709020705160e061302120601050c070905041407061d011d13090b0c040503102d02070323030403080711030d0608010b010302041809030909 69
    0x902c081c00c59038408000c0005080a912690f001c01481010160414901e8220b103c070003504542401d0301c5e02d0041842c21240d4440c104000d002800d204100c5c400c02c0c0c203224061180c11419400b540d0201d40c8100b1054404040c0c00d4403007540720509192050f602c4128400c00b40c1000c249034088004142044148402c000c22480b6a41c0c0201c0220200c0e04c1050342c0d6581214522021004680720116030542c075450380d44240c101600d07840342d143c2400d80c0901540003290701660700159001d4000e0740d4080c00c0301000030b41828941c00052a00d00b41e82414102030005e512204101181c81ca80c0703a4842082541e9030f2541501c8404a55000c040d076450062120a04003070f601180c012000905c6840c1d49180304200c2c041c8100515010310030080c11a03032145e40a54090070040c0c01303401480b514020351010088104000c00c049501200041a500d20b081c41c1c2600b502c0c22591014180350040c03000740190358030010f06100103200c41c4000305941c003c0b0709054414213500d410031005a800c00043d080c1e52131a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 762987140 1250 762985890 762985903
    0x60117181209030c030604020603040605060609100f020709050712152408060301020f0d0216061e1406030a030f140a0804230d0c1a040303050708010e1012061805 71
    0x550680701c000e804c0104043c0c984a0882e03009521050600209012490b10b5111329401407014181c54a4a901d9000260910018401050015007e00ca561440543c180012402800d00c0f00c0144180e05100c5000780c661b00f40301c004032141c0d55688948044581189000d60300a05a00841c6c0c0c4032041d40f0301e1440c1c0041103c0c9070320408140108042902820140708984080003142c504d1801c0c4400080010044d50180c02030b04207544074640c5c110041025480b40408071180c44201a0a0003402d081d0300007030b03c0c80541d51003031414000080000030385012510306030150340b520b0b140303c400d040208103580d40351020780d01041c0d81d034012405600c1a03410481440c015030249000b40380c941e8095040307a03c0001102c400d880181c20020b5041007860061644a81003032003004405503140025080182420003114103400003034450381401080b9410409503400741c070300240704a02503e050402e00c14540030911a50403c00342c03182c004030034400c0c1d540c05011444440075406520100900345076a8400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 762988390 1250 762987140 762987157
    0x60e070801170a02010c020105071b15110c1912200607020a0605090102010609050a022a031801050d0e0708100209030604081b0604290601171812 64
    0x62440c0004120a80c20070090100d4486080c01803109003d55401100c1d4800e0a18089050080078400000041c1140390110100a24048a204010701d040740d080c61141c40d0740d2003a0280b10841ca00256054004a0200040d507010f135003c0c08001d08651f0031104092071a4807050303070390300c00c455030340b080000d0b400308103e04034107001080c4003a100850030403c0c14070600b0f000070341c840f6a80a081000e24055809802542d405000008400d0303070b0360300d0100940da4100c0d24041c0d82a80024004010503007050300c464500b18050104010a90f100081d5942c0d21070381109000300f035019403d14000e60310840859000301107210b81172107541c0a4001441c1e44a14502600415001c0c0b41c09040b10b20f4014401c1d1003607840020000e14030b5071590384540c60075900c07400346210080e0100602c4210072008005040c0035034880e104140c1c0f80d8052050040c00c0403445203550400b4070041c3c0500686d84c1c1d10030000d245070386441d01c0801c00380e00e0b546100320036000c1c2c501d03843c196401134840d07109420361034030040c10a01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 762989640 1250 762988390 762988397
    0x21210060323181b040b0a0e040b0c19180b032a070f050a1205030705070314160c0e10050f010831050606030a0c0b0705010b04051302011211180a09060e07 68
    0x40040002c11207e40c0c140d00401c0300301300b03a00000501048403a0132043c2c00601c20265246045440071003101080c00940b2900e010a19008074100300340441d08a000041c107034148682d0442c102102107034045460300c2c0c10710085030024002c0b2a0b5505150040354601c40e400001c424083d511481d0132515a015014203580728403104a6001d01e01c2d0040003220701c20a8580d0b9850325204665409581c948003402c400c0811174010300840d0b901007400814020298040e04402d0070083ca849444022420011310703100c1800c42c92002080242c55078480782c12444001d007080d400540e80d802880b0212040e8580f034450054803c031241d000b2003411460301074581d010381d059030f0003991000207040e41e800c40c0d210010300c0045240c00801c4407100e20300c00b9050b1203101d040045240b04c4102e0010341a9281550f00c0c202c000c0e180702500c01190b8109000545d2240207140c103000e48416100400010b00450800c18810365070004003182ea130391400b440c04054070905800300a0682c5651942d2503155003180d540010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 762990890 1250 762989640 762989651
    0x4150e0316080f0105072f06040308041b05010207120f0b150a0503120a1103040e01080c01030501090b010210020d06050901080604120c0b04020609010909021210060323181b04 77
    0x100c00c2c18010a4800d2440d51100c6078940458040d4580c441f03207031684040e810b502440c0d54000c00790b052000314005d80c040e42d00d03121603081c1802d0070140b000460300a19a0702c5140c90081001d641c020500c4001c5612541003012559030f00d003040b403900000c207040100f420402a04000c0d4000382d400c04000b801c10b0a9480034511504da605056030744020400508402d10140205504240301d1031007450b03640c18400640342020741e20007140341c10b480280c0040c0c6032034000342d0f040c03251540d06104641c01450b840130244081c4100c2c89c0041d444501141000300606d0300002d140074010801d802010081202401c030350100c1da900c240305502e5101c141d5085500b606015840d004540c465400b42c9080d5030000d84011540c4c4440d0300300240396212103840d03810311448030000101a10710344090200d0100c4e91002c6030740b914003060156002440c0f40c004000345454203c2003014400e9061514003445420f00c000b0b03206840d010012003e5006901c2d450708248905204d0700300c178419014a101d400e20301502d00703015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 762992140 1250 762990890 762990913
    0x60f0f09111306120b0a0b09070c0b07090f08030d0c090308030f04050c120c0307081606030b1302030705070b100303080604051f060c170f04150e031608 67
    0x10360320140000391100c10074841c40d403000d00d445540c88142014035040011020703034890706180000b2480c8000e4400411180402c81502038a0040d40d403c0281120800c4142c907007028081c1980303c2481c009170403110804000f070112401901c3c0030001c0c101072075600026980c0d80343e8541e034a5004400c007958081c1005410a9264004c4600354203503580046a40c0c01d6a8403401d008840440040c03090301c2c43c2c8a8032882240c10388034542c4c0e01c190a45034801800703d500203101407614082155010341da4550000151508410324000100281c034075a00d40801c214208800089540742d500c42c92200192001081c0000b00d0703000b00c01048414400c1402c00f901d940e0750700c0b596282c48413a00c000b80105460000080c0785d464030b0b42c440b552082d081c07080d2003101610b1008a00e01c03007100d90818030105009034031034401e00c80c50000c02c103960100340f48000d00d0101c0b51011904c0a005511610544070031581e0303055506c60040c4905a8003c00150841d400d4821a9202d000998018404c500c29070040400048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 762993390 1250 762992140 762992171
    0xc0a080106030312020a21090618060b120d140c010f14011403151f090b1c050a080a0c081305011e0c02220203190b1008010302010c0809040504060f 65
    0x906c107218584401000b6003207014203a10b44d03514102001c506698660301c503000900c00744507a19001e105141c94120340505850514102c9601100c0117100324440b200761580d03244001510300b86140185008038189000e000188c030540115489281d00f5400e2240700a50582c1e594042c29405109a084e9001070b665211610750300010a1035954040e044050001910320b10200160303000341e110485a0fa158055030b088101c001080d4004007a15510395010075010710741021a401d804010252607010041107941e0320b03540e2180220010702841d0042818201c580c080c0024000c45508480b01603074a01803075103401c9141807580110790214070300e0f5441c0b810464035000845152034407902c0b98510148240c080007584901940c0c03c281480b01242a5160310703a07640040c40c0207451025503040c1440d01d00c4114002e50740161840d80c050300d0300020400c0c031603a111182c070341181d8080c00d09064480060502d41c045104071024180c0281c1008144030070800c40d9445001c103000540820000e207006010400f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 762994640 1250 762993390 762993397
    0x20114040b0603120c030a0e060d1a0307140603060f030c03030d1401150e0915040e07030606080a120c050102160b04021207060f050c0a0b0c12070804080313050c0a08010603031202 79
    0x171081d54001e112426180340074031a02c00c540c00703005004d01e0030000d045d60710f90161900955000c0500e1201e222002c01800d0810242d00a00003000d0800b43c40345c505404509a4000244440d10600303074400005140d40f020301c041450840050190b83d030740c980b010b04150140243c28404a03003100b07030b00e0000641c404030204415002c0c20301e5803030b40801030490b0100051400b0203400c88030a824048180803481c0c0d5148600e12185400f0009080b946256040041c221005540300c600310350061022500001c03484590107002100c05c0c00c2c103d52000720b0f130030900d00a0081d070040d10311540101500700144a5042107451041e4804c4030400100c00c4a4924103403584224401c80011900c40302d20350580c0b41c02180603050856203581101c90599040d1250300c402c0509030707291111800d0000d001d081c41504160240d61040041c00d1600940c2419501d1b0441880010100351000c500481084200070b800e02c603202140d0300c0180a203800c0340d2103050b050700070b082501c01100480c1061046900358441030096 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 762995890 1250 762994640 762994657
    0x80c030303060d060507111e06060f010c02010818030f03160f08060609030f0d05091507030c0609020310050103110a06020a0b0609090f01020408010c1b020a090c020114040b060312 79
    0xfa003590403001d94a1401400018200d003090044058151400103010000031044181c03110b044105048010002420190050441d50160b002042c82c2c01541e6006002c0481607075081c648440310356a44070a142c0303403140d0807084c000e82d80000980032450754010b4014501990248188c8070304d03001d14030b2054422010f402d550401043c0365200060092603c40c0240003295005819104020003103001c1034100300c43d03035546001203034001c1586546d83c20003060304a41c8941c071050461411101c0d44014014a021900040802d034a8034055000c41d00c091143c0803101300b07801000d015551b148e02d8611440018841c4140c050301d45041d0000300340d88000740200d05a03800182c821065143c2009020003039400800788002807240100480b400740e0709200500040c01410700000f0183c12407880240b000710646000404886c003040217002594450725a43e08841c0510350014405000702e905034050701010070300070788542c507610400050095400305544a15000c9040e240701c1840b84c1c0c40103c4500ad000704 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 762997140 1250 762995890 762995899
    0x109060e1e0105070605010e01060e0a0b040e0703020c0307030e130b06120a0b122406033418050c03090303071d150c060702030a050a140d15080c03030306 68
    0x521501d00880c15010060300300603d005444c4c0000b9031250819641c0a910038140820202c00410480c0e601c80303110b01d1821400c40b0501041032810301e01141d20b001da40a0348d0f428940c1940412280c030702030fa04031241012002c0039651650010704025000f0090036601078092641000440908d44040c8540014420003c0c055420181d140700c116a0f001c80080030044540e07035030030b5130b085291b6503030003094100040007005001143c00c1e00e20f039040c28000c1502040e034100d0202c0c10f0042940d4041690042c41140f034280c60300031036100c40b43c5180c003030f0300c145070329a41160020041104840502c000030048d04c806014010f5880d0121405082c0c40111940c0d0079542081c400b08180c41e101f90b030301c15a1403560540b0b02150303d0320040005d0050414080f0f1410b00000080c142d640d0700d2040c00800c0d4021a24000342d402e109414002821303622404068201b0030041c000d94082c4900f40c0c1084c0c54441014900400034514501c8200d82225014028078016200366180c25989140000440e4490b800240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 762998390 1250 762997140 762997159
    0x90c032a0906050717070c140402030f011e0f090b011704020906060c0a05030f0306100c0206041e090f0b130225031205070906090609030f0b062d0109060e 68
    0x14219103070f8000c21000c5820070300517a1120300d200d501c3c001600700c003801020034001040c42c00000d91003122170701000f01c0c01140140200325885096020460440e040b0090413004444005600e51180059400c4403070300f60002000800c019406a000d0800084280c888126401c2c0101c2e10000407101224004e5009461a0000e040c41c20004040d1045003500c03001c440159407280d079010b045801481c0c00d8200320f0300200c2000303c0303890400b460400544c030508025040342c2180d008101341e803040e4040d01c2440e901005422005982c82c030140c1e8000c01000310200140d140da400c1d040040d15140141e01d119104624066144800030f2003110128059001c0070424241c86601c10100d011201e00250284101c11280e5811176031300340903452240a0a0341c1e074111003810100098040c0b4625017060082205514080c0002031090450064264214a509203aa40c1c0c1c1c1c4006120480c00c500c2501c51005044a0007404a0844d445c120005030242c851403811601c4050440f240351040410513800309111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 762999640 1250 762998390 762998399
    0x15090b040504022203052406011409180c0a1e050306010e010903120c05010f0e030f090d02030a0605011a030603191104110c120f0a030e07090c032a09 66
    0x9900821320400808608902402252070540900348664420384039034000d02c1c45940b950044280620004019151900341401c00c2c2c00001c041c1c06a82e010b401e07985000203070b291403540c0c030702c02e440311006e2038520800300c00e10703003842105084c0e0400904240030403070203040300490100c180030001c58441680c1d101030030f50b03550200444000c0d03100d105103410310880303610100c00328100d8444030440c09241d4031003020b1100702d881c049003102c0207008854146443c01e5440d02d00500b01000320381100c4040e056498a900c907203000140c9254910750000d50603c9122114002c005550708120f04803a594000c070700b1911602010000540320403030f039043c0c1c540c1281c003032105416044000146014021500035592900140100e021140c40c141d41000070071000c200d8034980402001140900200d0306411420139a002c1002d4806024030503480007410b44030080511040c000b0000c040083c84400000d001000756450b0190003414050034168000121410480c0704001c51980e0110b2444a0f07515011b45901d172 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 763000890 1250 762999640 762999649
    0x9030225060c260d0203101e0501030f0f1409010c0c02060304060f0b1201090212070f050616020409060603050609061006050f0408101e0e0d110a020a06080115090b0405 74
    0x1a021000079103100001c0021044075030502504c220700112100594a0410740826092201c90364071046a80303a8042d086030000700440c6981088036800e00700811800b4588260718068002c0301402c4071582d06d410802c101c0d00c61007036030850244011000811103000341601c11140424030310006508090100f02103400502d8642c0a82a1952103c0b800698a2030101c002421003003500c40126040e910303481c80720b080d071400080010fa4000030310b00900d507852a04400f0810400301d0b01c05c440c4a200085030022000c0d14810003101596802003041104d00f4030341c903001005003c0c601094a042c031078000060149500001c4181c0101540703c00010000d203001002c440f01d0344607244054800b0420310001445070000c00107842d140154520118200c801c90307030704941d904e030135402c000e00250500140080380c1c03102103844c0445204510f006a0980a19051980761000842009410241443d0001b0701079038850b42c900e0513220800340d0084030703d02002007202c440c2100c2c082d5000c008410001000203161 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 763002140 1250 763000890 763000913
    0x5040c170109050607121b110708010b150901050d02030f0a050c0711040f09051c02060c0f0a0f030603020913120521100305030d02040f05010c0b07080406020c0109030225060c 77
    0x18100c070105141ca224407e800e180e84600651002151080f04080340143d03003842070801401102000300b04ca10283c0b0300180e02d40f00820845450700100282e0701701a42d2242c001c80702c40d00250705080d5964202a402c4401800d01204e0300d07003900e4548000700b0110b005100407101c1c44ea03004141e4880c00710304041000000c0c001d0200c0840c81955508203280024018440c0f00c44200315201c240714451249240642800300040104103440703420410351036000c0419050700c450056900d050700300b103005188140e00401050300080c0d07008844a080108028180b4070f03605203d480b4040d210360507000780030141d0729401148046401e0954591840401700d102c0941e255001c032a0500f81044c06070717a500c070035003941d01c404400041d82d500010140240c40c00007002030020308003881d0000444405d525807000e01c500103005a02046205008103050240c1ea40546502c9840f040007003013280c0e03051070040c0da11300e07003442c95052110070b10f01028103494100380b0840884001c0d8071a2898480e0310b54420607aa43c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 763003390 1250 763002140 763002167
    0x210306120f010c03050f0106030c091701022811030414040f02160c091a01080414010b060f07034d070306140901150b180405040c170109050607 63
    0x201c1c103050744503001c109028540501000e40c600003504e003440170880c1034485c0140c12103403c0c0740c24044070740c0456a22410480c2115800050101000a490b44150192040403181604a540c2080c68170000b44400321451910100b9156800445da0481140e500e90040d44a201810b4030140180340c03c0b070906070010128901100c03030040c58042160404050100309000644100301c0501e030a00c5228882e116062a8002001c210082807114400007803d5020080c002400304503600110982c00f40c00350020104110002e200c00d8507020f400425809039081050113800048001030f07410302d40561404c814800704082d00381e4940c44100c01c60700c1d501d2000a846401c0c40c100d4081407a101ea41c1b020300a600143d44035940c04a12a05410700100141d40040c00c8004103901d080111061840b143d05400d0445641008540e1140440701030030840344001d83d40b00d40c20030b00380410002088540412101500d80d23000d070580741c1c40c0c0450b078620f0882d651440002e24582c00b003c04603901d43e008054088405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 763004640 1250 763003390 763003393
    0x60703050d020a0c0b070809030a0e0f180a060504090c0b0f070605100e06040c09090b0d06020c100c0203120105150c03280f02150403110d080921030612 67
    0x10110401080340c1c05200340380d00113285a50030200308072006586a810001c01e107440080d40c180021265102d105a003044814484c003820081d0941d00e61054840131844010110040d003040c1c4441614000c0046403403101d60ba14040c07000c5094a4244900c2c013941e0741011040c0c082c20f041c100c405026621103c0c040400748000c1c41340c5030000d405030040510442c200c50308065498509042500b15010142c42d00e4400d6040030322302012a54000f6100c81124041c07900403813000110808103100000780d81c0094510b45c00040c2ca10b00342080058400d01041e00c5070380400981054650890310790040c903d07800c1e0b00340020001045a031400461030f0f500000316040e610725040304070b91007501c1c503440003a0080410098662480c02ca01520410030b640034540d0031b01000d4101d80380300c000c0d150b04110202240e044141f0300400e051610610428020b0018841101c841c17941e65075000c1e212000c11124040785114604106401004e40f01d200c000c811080e1286500316202c40040015400c8800d42c10b0005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 763005890 1250 763004640 763004647
    0x603062202190e090106031e030509040518190c1e03080a03020417160e19021c05040c170a1a0a32010b0306061204110910150311030606070305 63
    0x10f041c200c6a18010a10100002038051452078101c3c0c2c40c00f0440c0342440901c07200c40252002c070380c200c0300700c600540040700c0c009100d40c0d60700d032011072001c004210340119100e0741944082c070300c2220003030090b000d02440c0900001b554445000e8004c2a40b41550300d40c0c00c2801908100058980c0041c00203141c0ca4100503003000d4460b100c60300c1145c6a42401c000c0c641c8161410020607040490f524040e200401c01c0c4101f524243c0b804134013404844c0b103c91380f40c0354000f500c15245c882100b100300900a00c0b00c01400300781054242180107081c24062902454441a00004041c8001030305041159103c02040b64800c80e04e12032881a401c014148407007603494610002050728405100089611206101c003c54550500c0c181d00700310058114a0002c0c408000f400b00c542c0c0c48400755228648090040031f5140e82d20700e4490000f00803904032a4128803a01d0600c03071080c034690280416120949014000c09030540011001e0310000254400d4146003000802c5950a0001c018a0b40c14000c0c28060b14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 763007140 1250 763005890 763005899
    0x4080a0b18030a081504200c0703060609062301231e0d180b01030b07051e040504180b040201050c010e0304081b06030c040504051305010c08060306220219 68
    0x2e40e48150b0401c00011980d00401420350781c0b81011090f00740080d00c08200480c03140c0a400ea054a5810303c142c0120401b03d03044443d102c00300170000265611440900c4030580e034103021005491140241c04800c0352941981000d0f042c541980a2504016910200910107107641c040408d1381d600760303a0380c00e180d0070085142c5440b031104944a18945507002d081e07881840c68a000700b02c0324102c410000e58488407281c0da000c91540140c440c1500c1d0000d55110464035140307070a85051280311000900c41c40c981112590f010040b0f40980120781040c0c40a0010745076040c0c407500110f030b20f00f40051406089502007405544254060120510030100000d40c43d000c07a000a03180d4bc10562200c1102c1e4410540c420425004103102415541300307803035003800d42c2401111407a1500850060902a0766a81d00184401400000e100306541d007000c0200140400e142000f492480c044400900a22560f00800c03201c2c0b0040fa014440d504c1074030001c2556840d01e03030811001804411002805448101001c80c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 763008390 1250 763007140 763007143
    0x211303120531022403191803050712050403021e062101180204030b0106030902040605060301090510050316030311070306150303030e2d0111030a02120c04080a0b18 72
    0xb50101aa6040784910007260b1040004028001043e480d2244c03056034101000260002a25003102c142000602090100c80c090b2004064043e81d0080103000c0c041c1c1e40041c03541280040549134041d041042c0c44182d00f403070607a824496488003e4100c1100840c0c0060300c1c61440b1042e0007588010559842d00728201d031509140780c03400c2012118148580d00400c034100043c1c201220100c200300b025400d2601d90340314400945014440e04003410380f034060358801c41d41c0b184c0c0100e0180c20024803084c3c681d40c43e006002d0060200301c540d80c0041e0611400814249000100c007008105407600a0510300c2c1140c1c0d040302c1d002c1c01d0039003150b00e511a22002000240e6107002c6c01c200b1002100060000c94510b00b801025141c042c04000b00c01e0300305d600e00c904907441c5602084400001c1d101b11400d9402107001d12401000c1012520039484000300500c0740b804070340c0d0000c001a0000300400c0910b9203510021241600c43d522802d0307410b40c400c00420f8000342d840007c05134407850010340d402202c007080380c146 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 763009640 1250 763008390 763008451
    0x30603070504061d1b0421080703090527150a12080a1205061c1a010905060a0f1809080403050715080106020a0b180f032113031205 58
    0x480c044040c08401c41394180044041540682c10b410203580141065203450790521440c000c011032140c040960344130f18440504103149a5500c113100c640e0700c13a09130800030712445030341c001d443c41411200c81e00054032040e41310f03100c1d0340c51040201d45200d8546010032803580100e218105d402069000b40052101c0d0020b00b07520f4140d004600040d0b0300d81036a46c004024106224216038210329120030300103076840d115016440c1c440351806032006085a030030400c0c404603640072108140e040c40c000100e961950740d0081d034099007003070301c8200000b81c0303071200c00c5050034480c0036500c018de005902e0051541c9582d000503d919001c1c1304540c0c40d05841e601c8543c03c0010b41c2e0400741350114078200401015a00800c0c0034010841e80c8040c0590450740d640d8040901c0d4068000d0440755401e5009101118081c880b0580c0c001c807001c105c0382c0d20501c124401900c1350304090900d641840080018044030f03401203070f80700707c0e5a065450440002c01c0300303a0080208409013180b094507040da01a141400d13401c0840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 763010890 1250 763009640 763009649
    0xa050a060b010f180b0328060821030c031b0403030806090f1303030e030405030114100b03060a0315021204030c0203061b2a16060201060f0609090203060307050406 72
    0x4109940404000f402458a108040c0300300000002050744204030441008180d0f01002011656070320386103130b602c81d203d000c041c844103110b08051402420800781e50206040710050425901d0b01c0d1560300415811011a44913141200810000100e2013603c52004507401030313100012003003002c0440328444282e002508100c011030402c00c00e0014907d0480000c642c0054841a0a9124507140e00031459a80c15050000d0906440b5400b00d0810b00051040d5405020050000c1004401c4010782480e40785054442c3c10898030304841c045800102107045921504000d043d0024035407469840046041c05080c41000a41d424809801c441d0301403041d13980298001d503903215000300076004150400001401c0d100e41d01c154400300030580442c66040d1a2804442201660110f40d80a040a07805100042c100c841d400b4500316030022851f24000d00080d40c0880c2e0003004500d4a0f081c011504a0701070244401041c94220200094039543d0010742d031201c0003800f03403181a540c0d02e01003802e54176035811 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 763012140 1250 763010890 763010903
    0xc33130c181107080d18021e01030b06090307060c06150f03060e0f0d0c0c090603050a031d010203030c0a0e040c0320070206030a1d03030c0d11070b0c0901020a050a 72
    0x4071501c8111a0041c404585081c1c0d207a00d18004440e0b41c0c1070010311031200c100200603103a440c00200200c0d198000826650003501c070380700c840f0041e1607020f03001e00e80e440d8544c042131900d036100c10541032123400d66004140c040e00600350780381001d5054404207001c01c400c50f0f109172103120715018008070322003800003825660038480855041d49030060a655120070304503100e6000a982200450300025407100c0f068440c00c103040703060f0550600d0072070102140c0102680b203040c60b00000401100080f00c0322558040e41d62038000b031405403030a60a40c2001910580160700500100304115684401403601c200f0718100a02c1c1c2440c0301703011400351005e0b07040f07901c00320350398800000b4124207070b80102d8812128040100d2070401c55600103402804080d1024074400c0d42c034004200100c811840180340c220788602241e450745490345410019520010709108090308041855002c40c03200c100741d648456000903244240d58881020b07507255081143c0b0311341140b080c10300c50408102c0910416004600414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 763013390 1250 763012140 763012169
    0x31b01051510120e100e03071a010e0103060b040f1406100f080a0c0314010306022a0c0d03181205010513120503090a06020f0c33130c 59
    0x40c810351503809518129800340c1d511451402e40c0c940d02c480c0d4903900000030740c0c00107030301401c1c940410300c4d050381749074080e80d501e01d4413010b1513800308000043c0403801e00c0349265240803110301900f00a80c0d43c3c20721480101a0b8010014030005a40e80c00842010502074000205244e00784981c5055401580c10420813200c1c80050240c04e060ac0803403c4800d1800341070002c0000d855103402007081c0c00003010844889d0ba1502440d038400d01c640c02040c1e4100341440f2030702823541c4070308021000b903001040c10055038205150f100c40240e600099108103400c09009003003c18010001d02c01c0221000740300318100410401d100d1500b40490b001d50018046000310000145141d10700107007102e40c041c110160a090324068000040c4542002880750b104520700f494590303c1d4400300910301401001d005151500211308061100e58000207001d0054000b400c8032000800c969002900c82c2039542d8002c002c00b403c0d4003c03002d04050602441d00038060f903051030094021911b0300c203c0812180c000030108809031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 763014640 1250 763013390 763013401
    0x41a0703020a0e061306080903040b0a0203180418141c0c03030b1c080a030b0d1203290d0c09020c030a0f0203130e06010507021002160e010510030509031b0105 70
    0x700700c1601640f041d1800d03031420b050075051555004140c8251010041c8903400103815400c140180e80007062202c81c007030340b5282800006174032504500508011940c07000b0005002e45420f0061180610302c3d400315400c10760060322141d8052101c43c110b018103109000610a00e510600300801c4100c0e80c07543c0302410100c0b1450000c1c241c030101d00346584503c0428003041e601040d0b8000e0b24500c0c617485161907a48016801c0b05901400c3c03d14003240c0c1c8140f81489130018004d88d04014038050703a0a0380c00300710911040902100c0042e041048a00344035003204410042d040540c29504a1f034001d40f404020703280d8418400741643d100c8641038035240c00118503000e0b203a41041c00b00300124400c3c000380d400c0c00101d40501d80c0c14400c512440d1114101c140115155034010070440c0e0b2084c3d0080c1040c08042e140034400381d0303281b000714040f01c03505400355000030f03604042006503416154010101c030003100401000b1000342102400ac44948c1c0420010743c800a00d004c07201c80841100341c0300101c0d491900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 763015890 1250 763014640 763014647
    0x913140c1801050306010e04140d0c0308071716030216110a050a32030a05060702100b01020a0b0714040f0e010e06010c02042c03040e0105030106050d0b041a0703020a 73
    0x310311001c52220346100140582ea50208441e4196246010390345010342e0b4074182490100c07843c689404150103400b29581103581d02840c0c0c40c982c0b03030082d240c1d03400c1512140303421203000804140380c0320b2103c02000800c0e03a0204a00c0c60404900207440c0150814400f00c650f18808000e6000c101c0d484000c13060811898205046040000c03d011624001d04514009014031815803401ca46500448a808100a41548600e101041e03840180c100c51203c4a1f07490415540d42041c1e85250140c800c00b226007454000390b000b040344e4204182d010b4100b603000d0f66030700f5042400c05058001132103200b2800c08051803140c3d0180c002012224000c8a43d00e1418000c41301c0c1200c11f030461102040d1007010010203076001141c0a0301240e05460020350455055900d40c2c0100900c50b407020406040e094104008000002410640d041c0e032200c552942d0741c660804d4205d410b00d10a460704021642240e1021400ea0080b0715809401000c003030406950340c0d2050328a1a0b01117070608082a40807030346000040e407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 763017140 1250 763015890 763015909
    0x14040531020a0216050604051c081905070c09050118090c080d021e0304120b0a0b120703020906121c020304180905060a1a0d060f050a1e02180913140c 66
    0xb006d44034607107464140808070f2002907150340152403040c1599a031700c0400000c4011202035003140e141150ba0107646c60f2000341075a02c00b80c42a221184401e90101c1c3c078080500c2200d04a44460b5010301c0c80c01c1504403880c020384403081045c0d840c0d40700100006114081400b800049411645c042c0bd032591102c001042002c90142910400c0d6006000621603e10890f007810041c0b6000681c0303500a644e540c0e0560060b0407402d883c5038101070800880d4645000000300c0505880c070844100340039980d100240f1110318001050400305500200e03c0655898951035555500441481660f1406071039500c1002401a90414001925503c10228052150601c84a034102407401428092030781c0c2c84100401a030300007408517110b0007200c096032041003d564040400300d00011014826172401a9000000701541502100c451001001c0120488124421600b00d0310030740394240b0f500d5100c401400301041c0001d142c0b44d244904540320001240804030805a04103203180200700034101d11003031001020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 763018390 1250 763017140 763017149
    0xc050705070b0c1009050319051b15040803250521091209060702091302010306050312040915180e21041a0918040314040531020a0216 59
    0x14144070071000003c000c980d95040485401000c00c3c0c61005082c50341c210701c61140301101d82c40a082c103035014550400080c01900f241522807005400b80f80c2020f90b120540c40c503003100c00703254a000140c00100940003035074200106115a4001015561400d0180300014007100702292000c0b03803031901c00d441210b01e112032417003005459009051044065a452038001c1080082c0c084c00324055402d0348900c801e03211426002848aa09810440310030381c00c01243e004141d0000f4144800452541000690480007010704660503245c540340c00702010090902c05000e0411600041e000581aa4117442da1035a0364040500044d4040280c80c200340383c8900303644400c0d182030a501140d1404040401030b81c0c111040010398904030015042c00e08858400d08929590024800302241118214112424801c500c40d4903066000c40d00e40741c2c24091030150348034103548042400302c1c080032000150104510a51201d01000c0c1c2c03880c5140028043e40c000705029001a03008003110550b00100440e01030040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 763019640 1250 763018390 763018409
    0xf08070b1003020108041211070b0c0f060717060301090f030e01020d2c1203042c062d27010f0602060601110712120e0a08071202030f010c05070507 65
    0x842c91580041d0a5a100030005001d6402c48a803903002540101001c8400b9994001601c2c4499100d100c0d920458000c0e0000c071080c1d109d4109101003424000954502506c6aa101e844100c1609681c0040c1a0030090556416540f14bc01c064005a5549020300105101e0b0302e03107031425200c040c002450910100d9848042258039154491144c0111410f2118030351544c9140900100120210389488400b00c03849032540710010b27000900c109c058100101e50800c0c0030507580103542c2c0410790107200c407041e81c3e6264440c41030768444840300354040d42504242c04013915103500300c03031a8000488148044c84480082d04140386141c50240c044c0020902503e440f180d682c902c2410414003c0d5150401490503061041d80304005d07058040400c0410002e0480684810420903903140c80902529a080d40501158101e007488507146090950314050721901c600034410309140c007151125000d10641c060f07030140a6500001d103036060030b0048404c64242600c566564102170b190a87c909105076010743c250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 763020890 1250 763019640 763019671
    0x90203161706040207050f031201170601030c09020a0c0c08031c05090c01032403060b0405071b03081f0e040b1f0b09011709010c0e33070f08070b 64
    0x702400a80200d0300841c00341c03001038560901d031400c00e1524080d00303c20007480c070011540046180c02d01560b14180c0700c3c0084050060800c4000040c0c0d1004280401814072049000910220300c69a003d00031040c22442c092418140301d0b10b40b1410340b1000d40020382107401c0040c44040c4000348071151a811207003040c08000358030708031030001c1d12400d4550180d0b0416403100340e10741d40e010008028501002d00009950051640c0e45032881c000c00f5010006402141404c0000c1c0c1d0007030041c0e030072007104540025130704130006060b030301119040c0c0010900c820140303142c11851103105148520b9006410359100e415058149030504541102004000303000701d2990200401d4483c16284024003124201d01ca41504c4146031401aa106800d1f00d81600307210100c102088210501500142d1008040c2e0300c512607542c503074400380047c940c005150f00b40343d010100c4111045110105101c2d83d08080300701203c4c2050745642e1545140803000c081900c940001142480520040c001815004544200305101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 763022140 1250 763020890 763020917
    0x10110702150901030b1002011b0e01020d0305180a0f02030111090303040b0304030530010803041d041106071a06060a140702030a0b10060324050d080f0409020316 71
    0x3600200c0300104008044040b03440552a40203810501481800070406282c0002e2110002d000b040065000c00c500c039102c50368603804c0742c00350300c0c0c00c2c009590682c054295100000d17800e5000d004060100c042c0042500d400c084100b009004108500d44201d1800300300004500404d07003074400c2008002502002003202c99403da03000000c550031107980b0100c80d1380701d0f66181426252401014a42d0f1101010b041030390342c071a01401c00064000454000c0e00d9201d07600c42003038950b40c0c0a02d000d003401d503100b1502c401000d12451400c0903805407040304c0c1201c00d8000000800c101c1c0e0000320080b2208041241529400400e41d54002e90100d800d64040f800c050803544010526190500d01c40030908000482c941591014808900000e421840504080c01c0032403009520301060302c01d4000081c9401c4000d82220303950209000c481d28180e0701ca12109051100f0030a000c0c0c01100d0403103450301c08200c0c607a04454032101800050102c4040140c5901e4070310000cbe0011465024040d0821030049095175 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 763023390 1250 763022140 763022149
    0x50d0f0221070f050a0602070b0603010f0e070512030f190906031401030213090f0b06010f030e060402061315030c0f17070833030f1c14091210110702 66
    0x58202d070700300e15036142540742e509140b803e060003410054101800098031800f40034010300d015000b10030640c004c1105119040300310046450117502c204098000d00d81c100b249103007003c2070201944030320055a25280d0b1305901c101081d40328400b40400703110f909000d00a0b1a0300615407000030000380c1802e201ca40e0403103044a94407601400300030700c1400e02c00140255501154454482c2c0f650299008000e0b151034203240c040200220707070544c001840740c9d858804c814400e001d100d11002c4404010203664582d5420025150803c106c02841c0c40c980030b90000709682241c1c0805840303001502c0002d10042c2d13004004210710500840074050048020036900b80c00071500c5807950011852801c00c2d0941c4603442c24104924802071640110007000e00c001c4010101070600142244044040301c00013144844055210081500707640d01805100c00c41c0100176005036008d9555030b5190712240c0c0341c0316440001500c081064070354190740798050b81025000e01601d20452104000d406072280c2482d11650004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 763024640 1250 763023390 763023397
    0x2d050d0512031503011409010614030c1509060403060533010c05030f0a020312060d030c080901120c021c020303090d0507020402130b070c060504060518010c050d0f0221 74
    0x100000800080000c0309003100380c040d0354041400030000d100c1b43d2810800e0241e00481030741c5451882d40707032100001e4002003e44c6e000c5090000070307001d050249900000c1002543c1207401c00300000300100855442ca41d1000c00901c0070714410301001a15082600402c034240003e640510340d013600d50200c3c04140c10790502a040881c1c424a0410000c0c2414507041c2d00b11300440500440766040440c6401c042c0e50040b01601c0c814412001c0025681d803107400304186100d4506e406808a2090200e1002040034a030003401e010106040041e034080c0511045801c550750046810010307040b90b01340c4460001450181c400c04c054500c025820f5081030400282c403904120003036020b00c0700000303d0b113045494540640d00c8145800e020002c0d0607582e004400c80c40da201050071980303c00021004151b503030082065800742d440585c0ca103410315101101c1c030721126107603c00e040d0500080019410020f14100480b5a00c40181da854008010480030040e26142002c02a1541e000080c40307405003203080076054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 763025890 1250 763024640 763024663
    0x30c0b07150b0a0b0327030a050f1b06070f02011a09010510020106031202071a03010b0d0509010b030f030d0c02120a2307030e010e09060f10092d050d05 67
    0x10b000b41c03070b400080e601400d998002421000040100704004100410682c01060070031040a10402d00c556070b240c0b04d00c1140103200102c0c800f44640e0304403003501405051070409500d4048001c10588881a28140048801c0b80014044041c620380c07196080c0542402c01711b548203140030030101200081c0c00300384140902170050104140c02c00301c0354800d401000003150412202c880907808164000e4980d800f40c041c0d0070700d030f018100e00995160245001c42c4d048031900d078812410240300704103400282001414064080d27491350080104c0342d90a00041c140540203800865603141c0000c0510240d511501120055401260f84e030600510f1910860700a010580b500301071071459420740031149505149010001000440c03404100b58008101c01c0b4a9002600c0b1140949402010003009140440740c02c3d402c09059002d00a150402460307960640c0c0b802c0c1007508120340ca502c0310394680b00404041121108842440c00810701a10411a02505003652140c0102041ea1034640e84e4801700b600c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 763027140 1250 763025890 763025933
    0x190302040b0103090c1509060c03021203060402040308180a050a061710031212060b0f07110307082d03090d0f020f0a0608040303060e090c130b040213030c0b07 70
    0x401c04140ea119a0101c3d0b00240d1000c4404e024903244c030300115650100e5080700c00454480d000102d21180038519441507268140d005041c151000c110184490304058a410380181d02070001000041542c4044c15140d1044c0000d00c2d40c543e5030100f0880084004e81c00140941c0c0f8408060281d10351050380842c070b442c4440040e6082da102c1a1401c5048070240e88041e280c0c4041280101c1000d5200c031005070038a18800050040584954003a01d240c400c00c01a25038080082180000065140b4070000c45c07a4030040c16140129a90001c440c2001c4850956020600403022801107201500c42c0d40d9001404600045081030003e0012031904400c00360080d2000300c27003500f203000310350703408101c2440c0c60809040196040c0c3c2e5a100505043c00944048010030305195003c508240320480f15842588184000c101480c0b004c0d00740807141d8600794032040c850381c48142158003a01d0f03071300061500d043e8141002003650300c1c40c20240b603411981d400003240d0000030080c0001080d1202c5548011203130049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 763028390 1250 763027140 763027151
    0x100c02091b03190e0102311806050a0e06182d0609061012020f0d0207080a0206090d050d02180306040303020c0c0a1203180b0d090c0519030204 63
    0x304588103030390091034403050200002040006500020304030441401002600303008000d04d004480307080c0c3c003881c07075260040c83c1006070b00e91080f402c8205072804401c2002d4100307541c5440d9440e00e050b0f200800e20140c00291500c4041149042c200c1e520340041c40c00c90140c3c0094200840080d0383d1500100c1600c0d03030420403001240030042680d240c0b04498521650b50031405c121079488102009041b9142c1e481100c3c1c0000041e250304124500d0f083c10103007556003034226030301c05041400a400180d00c100c5032890900c52001c8286040c401030500714003829139540c90b50300b241d000900d003850041010481d03030810301100042c5500702040c3c03809840a50b1002d43c40d041500d4403441d20841c05001d1075070611526050106154140d0700a201c9c504600003a9006108002c0c01e00c0440482c5218925004004e00040004a485003400040c110302054807070956642da085a049142c100e100ba454440e81d4890003a020002145241402442d003039a01100896080030345a20000d040d1201902682d01c40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 763029640 1250 763028390 763028401
    0x1020d0908070e18071202040e1c050d02070209091c1106010504021602040216060f0204050108062e02060106030b042a02010b0d0609020306090309030d0c082106040605100c0209 78
    0x814904d51906200d022119295615140310380b0f200200384050b8000c41c502407101045550201d40000d40809080b0403a800910340c10085840e0b1380018401c02e000d0340e0901c03a010059640d50044e40c0a2107481d0003d00c036010140f03e0040010780c204030001d060140d0102600340c0005c0104150b030441d002213400580f1070300d5041100c010107036020f100944c00780c030005031001003031000649009a14011502001140000712946080748180e0181c10f000c9040080003994918052902194107041c92600e00c3c00d03009101040b00c94094000350840258100c3c100621003160300d4400d50803810780c106d400f440b041c0103800800121340b041607450b0348080355081c85002c0c414002d410003040b440c0d01510076250041d680c00c0c110300030100480100e10a00404002c2056100d00005589017001300a01a1001420085040c1d6104c1d01068048a00c10000d102c40c0011003800300410302c00b4152102c105103145006010082202d80540040e0b10815845481c9184183d101f414109030303e40c1920544100d071100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 763030890 1250 763029640 763029661
    0x150304080409020c0f0f01060614090d0501050412020d0206060d0b04051608070f050604030c18060e0c04080f0a05120915070807051203060d0204090f0510060501020d0908070e 77
    0x702d420010b240b03400050803c106580010703030590460510b4040d0f440844d608040e1909885040c81503900144141310707404c0750707403000d80b00030300d00c008004000410000e074035130b0b903d420f48804460960b011700c070000740d84149680620a5100b4100702e84007030074661400740c0c0080c010154034040603080758140e03800901042400c20074105000d00e4034403c4c800d0243d0304da807510b6440d1164026200604100540024507041200c141d0342560ba004481d51a010306240441201d82507805040c040ba40d100e0800040785251500307020f0140050b03010240e501c078107200c178441c603000c11102d044000b6400704161a011440110360301c03444440c4080100d031b41b112041c0c00030700c124580c000d0b50031446800268640c1000580401407800d588034000741d486500c100742c60424107010403a074a54105010f8122400146400c3d409120740c24400d0290203400d260503140d041c50700709002c241d980e04076980d1109104546e0108041c100c005545d1402090303460074061800d4a82106104091301e201c050707404110380340076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 763032140 1250 763030890 763030897
    0x80a0608031608120f100b0c07171501032f01021b0a0b160b09060907030f03140310030201110c0109050906011103070b06101409210111090f04020301030215030408 72
    0x80c085118200c1e818140c10b94094103c051700c646e085102d0340e80000032051806015602d07200301030320142400340d240c0220108000050f548800850289000c04012100e81401c0e980c0614003480030465140c80c026244000d0484c845801c8001d0700d0519400a13850b0f80c0051041c45081c42d11101c21a0070080c1c6002c03426169641d040290603105c0450800740114140780e02900040c003840810b030040d250700c1000f0782c907420b0559850480313801c010340a2010031442130091103490b101e0701d00a501540d2109032107a240d08143c42d0b0811003111700608005640c0d0002d8500d404051000c09408080c504a0000c1c1c0b88180300e204090040c40100c0c0080c08583c00303480821000054182034958230041450040c9000c04210740c164813405440c42c203261150311450010348840d62000300f1516050700c1070200100950000d2200f402d40104140300510b0781402c3c0501e403401d450210015031950108400c0120303c194036810f2501442c41400108050307982c50840c0b04a060310500115501d441d5401c0000e1a0320 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 763033390 1250 763032140 763032157
    0x10b090c09150f0d09021e1315050603010b0d0506010e4203040b07020304050108221211060a0504050c10030b0301022b0608060c09040605040608030901080a0608031608 74
    0x4804030b16401450803642244810386d00c01c40d8080c0c0440200d80814400078000c004207a00a5078040e480b051072840740c0c4c80728900300d0003007050048080da0b41c400070341c0540c0700343c002165141c404610322620340e07220300409030080024240700c3e0141a0000c0800c11007101401c411810409403844440b03800340c50140c800e0b588402c18010210030b0900401151194800d48044406044000020b0300e00c900c04401e84d801ea0b4416502d0007072503241c03103113415855030001882c0c01090690b442d0b0500040e0003001240d01c103103001d850312a1400c0c1031034009410440c00400000100f4101020800000c1011401815907001107a003001c4d03422941404030001e10415440c143c040d031000800c2c075104100410070041003034402c0160220400307100c2c550001e507107d42c410008a03038400c1c0007007100c862031900600b181250141002800c40e944100247c241d60b0302e0f80c86502c036508005496059946e100c500c540e132003410724000b07100d1a85404000b0780d403886400388090305500d00583c060200030250b0101e5403802e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 763034640 1250 763033390 763033417
    0x1e0d1b050d0e03060709180e1e010e070506040807031b1205010510060329131103010f0b040b040504090204060e25090501090e07030912030504020102010b090c0915 72
    0x8100340720160202d207007046890f01c00e2113035000155040d0704c103004090a645e41c1002d141e81c60901060988094000c622040d1002e00686140005014070310b040940302d4844040040b07218420f604000d07003803404a41080b401510204030a00111030002052000c0340e0b0300c0320403035a103040c004920204900c00c58000c2c420f00c0304402c1d81401400300542110303003d01610810005165035034032098080321014134450f10701d01c2e44040c4030a510500e00710300c0c0c40120805400850200f403007800540c2210809034920040d6400840144540d2142110306000340c120300140034903140c103001008000d4001c91041c20320440e00e0b500a0411901c8541066009050ba4444000542464062007182e0708035944041d613802d802d112176033300720341c45004251708407801a19030158040c2000b0400080820080250b0b040c9901c65207801c0002d94070080240310b000a5580c001040d04162000a0075980003641d001e04c10400d00003030006540c01d1804990344100c0c2100c91000d03480d58802c1a01040c091000d104800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 763035890 1250 763034640 763034653
    0x91d070203120703060e0a05071b02150a020604110d0302030f090301381c0b0a0b0612041704030c0608070311040f0e0c030c040e0a061a040501021e0d1b05 68
    0x43c0d54141e040403044c1c41c0c01d00c41100580d654110200200e950464110000942c408883d100800d0415020b440050002d41092400354402240490b554131903540d82005902030010801030011109610588102c1120b24290f20103094500039541d001703034a00b12540c942c0010303034600656400d501c41c2143c0c0c0c0034403842e000c1c5010001c0d40601c90300f15842c0306020424580c00c400610b480c054001c001440e10344440c0d0182030696440c4c549910744001d0800c4846a81c640131190b031540c5000242a0b580910403d45015140600d0241214402038412071031582c8144009d000082d03009801b4410344401e480d120040703179501c50301100601204a501064854009004a0070804441903202a180c40407591942e5031a241480c0015200840301500040c04c2800140306e0f03004000c0c0782c5c0d50800c0301000c001c1916900c460140e200a01e0502d144442583e0010b000c110950701440f11354103d0032034a01c11a41d003078440020780c0d103c0d05000500340402481d14064400c034000e1030003c0703980c150804c0480340c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 763037140 1250 763035890 763035901
    0x31f0503060103080a031a1c0303091e0c06050703050307082a0405030d05070807120c0602040b120906090a1e06020c07170d02030913020c0a03031a01091d07020312 72
    0x204d640711000e920006410444002c41c401c90710b050f1620242c00151a8003c10203181c0d490310740610600c04100c0426856a03207000201e240030307412540030030b103100504402c84c0c40b5181105030071019520420500c0b60074410300c07010a8020040e03d0744170000741041211035560300000d000010b00350f0324084550345910031884000883c0c1000e00282d400550407100c000340c020b80c040e41e6500030408004d11064040282000089041b05515070030112401d004180614035135444041e41c2040e0003c0d90704580206c0c8034406c0418440e101c4e0b811070088000f82c807180c244008420749440210b0b0000c0d20ba402c0d4645d820b96030791a00c040c4422600e030044011501c1e401510030140d200d690034858698480b464580402205002062000342160150011882e10342494188200c0d101c050940c00e180a80c24442c00030005002c2c0704051440d4800e5500040911110075003100d01800020a1410000d100c001800040004c012540d08811038907800100380d80c0e9003008074614401c4021000d80688480c05104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 763038390 1250 763037140 763037153
    0x614070c0321180305060a0e0f0f030c060a0b0d200d2619032414090901110a0c02061b1c0806011b03090b2209050606031f0503060103 59
    0x982c94000b555860000002c0b602500d20b40048601001e080d90300700300c0224981c11920341c4242204420302c13003510061600081040e05117400c0d1000700215800000e01280185e40038049282c0c01240e5070b004018545111f404030707041c01d1a401006008400d15409400c90182038150141c2ca00e02c01403125003a03405900e060032030510307041601d146000c3e06046840050088034181c480e000b5002c4940705076403034030590031805421002060a41d0707413103d45807244000700f100300340e10240081c442509911740c01001445921140203043c0513059143c0070003c140007444408580b00d0714103d1a064aa001080c0005141c03803003003840c090f44200c401c22070507003241d8000c20400350420000908100b20405d0060940ea0102c003180c0b4540017030903100355482c010412802c8007240030b010f4600768030707100d48821200e84c456021440300b607081110005585d016002504140d00074050041c0148000d0828102140b0701d4000680703084001d40700d85605140000502086070700504000b01105c00031b594904100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 763039640 1250 763038390 763038443
    0x3060c25150e06090a1a1b0d06140a150509011106160f1805010c05010212070e040b01020a230f070312030501060807120c0e150c0f06010614070c03 65
    0x250b010b40030303110009120400100f0f0440e03e19401030200440011114010f0314a2580104107044041508a0681c001030014014102c00011148005041f0b41806580110302c1c1040091078890f580218061084200620f0390104003481420900d0301e0342c216100503210b2030040c0a01001c5840740d20100166001c010302180a030011175180c0480c81e2483e064126100b22261500d000140da0305e100400071940b02d98200110360780100001810019001e145000c41c04055900341d000ae424200c80103201d152902c210000c4090034001400340d00029070f203441c0d488a81c04400802c0c0a00200c00351210702e000e004034036003903403e04280c586031601e900d010841410002140000030345850000700b032590003244264011229510368000d1148000010005009440841c1c01000340c41c0c092041d070303501e4080d001000054485411a01c0c2c60201060520b00400800c0340358007940041c1c010032105c3c1c0c205c1094602c0b06828201c17a0768505190920885035403131a03100500c00c8691039034441050b503070311410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 763040890 1250 763039640 763039661
    0x9020d061b0507050703081e0a0305040510140109020714030a03050406150302030303060904030201061d010305010c0f0f0f02070e13060c03201e1603030b03060c2515 73
    0x700982000e0740904499038041e80e14010240d600c5200305002049100c130103001d90700c0145010848800e41030858041e01c0d000000b122020075152024041044004d0140120603512004104500070000040004000c010302c00c1c01c007165400240c2905102c45501009034104a0a0803a5941c450000004008100c200e03000c7e64050f02d08124035004125038104002180c4d0000e00850454840e101000301d61007010f00308a0a566880c4800210015840807040d40c00d100403400400641c0746091440c2910703041848641000300602800200c0740d0040c01081304440c20345082200032a50120603803411040b0b401241c42600548100120007440b481c0d40071480744191814844000b07485401d905403000303040c0026500d629140e94a8480440a01800c0110114404040c291078901070180403680294210040e840100811a042c103801d401394001d00e48064000f45102e19000b0b41401103406844088080382103c4060309401a100140211003203403c501e1950b110040f0455210050290341b12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 763042140 1250 763040890 763040921
    0x3080d0f0212010303120609061401120e070b1b011a030f0a08030a1503060507052701090614120a0c17040b0609130f031814030d0807020109020d06 65
    0x200003048a928000e407680340c1504030360082940d00b140e8065401003451340b851044981e0301c3d00000740303140c1c640c0610f41c01410500440b4210701c440c54001402c500008070990943c03814641c8c418402800058410300300c5c0e9088010540710b80341e1107010341c515142d08151500720b60078020000000780c0504600e1088510440480300c000c0c0d50600306603100c0c1003240014000d04018000680e8042894112a2000e200e50340d90030000c1d41c5039038680302200c1090300e05100051b400318400d2030140e500107100380e2201c008420002c0081981000a01d840f501d8000d010170800003125500030403507400240c9607044601079000c9110320381a51031000900e80b5144d07030000600c400c041c5e000c0005511210034000d9070026000300c825039842d0203000448802501d03e01d0704040480754840840d6900450342829440303591350703001c130032a6035200b800070b011160840194041c060720600076964000881e855502c1c03141c02e00103d9030380c070740c0b205a0060100c0440a90003844006d8580100000c0c0d91080240c0c030740110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 763043390 1250 763042140 763042151
    0xd1401051006030c1e03110c0709060e1006050904020412030c0303110f0304060c090305071e060503130b1b0a0909180c06030519020c0a0201022e0915020403080d 71
    0x25800ca0540e030002d0a0480404d11000740084e1817005200300c0d9440450130306001c03c0c48121104407a0682c1d04c0b400c44050385400550080c0001d040d40e01a41d0001e00c10600315180d00e041421820760308a50314480d0782d00340f200004083c000b54a440d0142c400510080c0c480b218601c1846c28007414858404104800007407030054030503c0c5080708820b961084001c01a014110381c0d84e541d85a00410a401c2480d0901c06800400000544100310f980e01501030818281d4500c0102201c441f5040b8a42c0c000c4010f0101c28010001d80d2580c0c0311010407580c0c0c0201c2000a1910343d0071211100c0c410721840c5808600d8002140a02181c024401740100e8a143d05e08005a0001504070342d290795040c400200008074900301040900d00c2900043c3d000030070000e91010450b103403518802261b0080380c0c0540d03990001d9807060295a018450140755480c0340080e0410a1050644054502c1d82811400961035036102c20000340170400500c2d50350481002d100715a580d88a0070141450381082c0484400300e400c14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 763044640 1250 763043390 763043399
    0xb07170a020426150903040609090c080c03060a0905010801020a081605040509100b1c0b01090b09060f120906010e09030901020303070e0111390a050409020d14010510 73
    0x38070884040b2184000810050b860b00710900708030f02e2403076452801d28442c0780409842d045805138080d0040c0588401560344a24019014224070440d52001d1546450400f50030038868106040c291b120000c030b1710142e070326954400058a00200ea8100145852a00c0e0002c0340c601da05600074103a080c099140c031061a5214001c0321304024103450014005102404108120300305140e91507041001c1201002c10240c842107070186942090240b121648409404e0340031401c41841400b00008080c40c100014600309050040300c0d114402400c2d000c1d5000042c100602d000000540d210100d280480765143e09101d48010740e654028011140d01c0c4c500030020420040c800812203030401e4068000d5802c43d6030300303081070b2200b201e403543d000c0c1070288854214001000c28041d41405015850a01300d21280c0700c01a03a02152440441846029407500d651a1701e507180e00001c801c0b02c90032680492980c40920100b404c1c9a030070480100048105c03150140c440ea4103410541c400c40d8902800d84080b5030342c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 763045890 1250 763044640 763044661
    0x60901150e130b0618040b1801150501120f060902031005030601120209040f1509200102071202030309060724020a050307080c160303060e0a09050d05070f0b0717 71
    0x2076070101141c2c00c8a8034048000f8811201d804c0c0d010f28028030700e0049901d03548400498550494040300e0740300e912010894509601c85141c0324025901000300702d0340d1403068103840320101501940341400000d004542c50071525800088008242020502079075079112800e001a403c261001400d41c82004004511070400080413412501c1034a0441c46d204016000d00c00320740e601900540c1c0b070040c500e141c20085220341e034600600d9007484400140e03421442c24a402820780d6041500b8807840c00811940179aa8002501001e40e41d140a246c2c2c008145480000d1540c810030b100380781c206c2d4010a4400a0000c60781d0b89260300b1580030300c0d0300c1404105040078001c03482480440380c082201031010611080c4149942540120340c1c01c9050300c1d00b002ca004034410a09000070440009071612001c0c051101040411608112814818404088213a0301c8540f612140d41d908003c014020a26000384081d0943d0440d82c56040b841c801c1543c01c20500013040700c0031011250b07072501c15800c041208280c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 763047140 1250 763045890 763045919
    0x1180c06050306031e010908030f090129040e03090d150c1b060903031e0b030c060906040e0705070f1223030a0b13060608070807020a03050f0901030e06090115 70
    0x3c00030064185074240404615440c045418150381940da00e10032540040c01001c011401005448802c0d2200e14140152a0a4450000380910140d50540761004000a07003407501d402c2540484001c00c0748000890024034502941009a50040703000c0060030500c850010000810700b48010709000b185804002614140c1c284c80e00484c4d40b1241380011000314000b03078041c4224503c82e160100c0c2615004c0707034019102034040700200289644031080e852501d0100400742c02e030a8142d904e107080c4210040028018041c5100d642d16040442e8005a2010311500450300c05c0d030f60043d24248089a68100005800310550907000451645210900c200020f1000302c0750701480d02181c2891962031f115940c000d4146c1000164101d00042d081c0000030b0983e011344000f5003020fa80e0302d545440c00b01c00040103c02e010301848255048034120302d02180d03218040f19034101c41d608000da550712114004900620905803803078400d004c2c034010300036503031010341007000e241c81c070442c00004660700c0d84401b182024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 763048390 1250 763047140 763047151
    0x207061d10110d091113020405130e1b190603050f0112020d080d0603020916080c0c07120804120308010611030a0206010905070c0b0f01050301110c0a032001180c060503 74
    0x80c00d200300268806213400400809100701650485500038801082d48891040100c0d8600c0d03030003050502071802c01e0f04000c030103840c1841d802d2011140030b03150203840b400041044401d10007200e405564546603883c01c0d2043d040001c0076121000d83e0b030342c0c00800410b425240c41581006800002401c0040048281c8055030010f0800596140540d9804045d0b40710011000840d134607000c0000150b51250004d138482d0050080702d400442c400c003402001c4401c01002c98295110a00140254100004583c002d4900c480c0903042042c00c075082c03540d00790140d81c0c071030f460144241d01410308241c1c1c0000c000d81201d04070b0b10341c1c0310245480e058058072405241d800314010307805000108034440e900d0300025040040c6045c0520810320f5929190400b6404030b903070103400c01c0305000400c41401e003407040b51105540310032441c3c14540180001074440280000c003604110703c0d07052081a40c043d040950002d0785140000300644541c1e922088036419060704180c585410000b80014000c1c01107003224440e9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 763049640 1250 763048390 763048421
    0x402030c01031a10030609421719050a020315010b07060b0f1009030309060302070837020a031709070506030a1803030203010e1f060e01030207061d10 66
    0x3100ea10042c045181c3e90034041001701070f2107500c0080d5502d001d2103050a6581c403000780446e01d00d00c5d03680308a050b00944040c0442096140c200400e2000c0d054010026908110315100203c0540410146401220081c0c900c1c0503c1c041d4032a0300f008800074051400910076070a0b075445c0c031522207c840c0c080c2c40c2445903222480c1c04210080008241c1e5004901c0c5400042007003200f90504404605079201c1c1c2c0c10180301155a11500703009054010702100c005010a180561410311555113500c400e0240c2d60a04880040307400a0681c10a80d1404c01e061141c40c814543e030404c040300300003c3da6000002c006030082002c00c030340358100c0c81c1c0c6403010900c1800518001e0404901d003400340081030303100078aa1400b450785e52148041d050f2480f02d00c09083c2d40240e402680341d5060102c5100401d002400c800b8000c04141503a21074041c0034440e1030b007103d900d0304096000d420340b040182c0c00b81c480c941008100c14941004d403044606800c6010700e00d1304030300003260042d25039014000115160300f0751141d0b11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 763050890 1250 763049640 763049681
    0x1e0c030c080a09032706090f140d05010f05252606130e060708060d02030601060e15032412190311030d05040519110f060f040902030402030c0103 64
    0x98190340c00c04454548a460710500210f00300117442e02031905100461021012800c0c01c004441c3d00807100c0000e00020554a0b031900d14103001e400070313090400c03145030140c0c8142030505c3c1441420b42c018040c040c414181072085e03240181214413a581d446401c0c54100a2000c4a225100c0c4500e98001020401d40c8845841340c2c0340324200310741d244e4018040d40d400203880c41c001c28210043d003d00355602004d00300610450900d0786025000e03440040c00b00d4001c0c0312a40500015076400a030150445d041410485441c502000104078040b501c030700c6c000001a8008144013210b000c604081106000cbc60881d181080d54103410001d80a040d9484511030364030441e441003241365a9041c01c140c0070302ca42004904034520420203400d60700320460300d000d61541c03203013084107102c414007041c501004c8450f10940c00b5203c558503a0078071000f00f20348a003c1d81404600e2982a151801107070007803440440d220b915150b4502c04000a90710446040f4068040d541080030994008e0084c00c08080b000d0504150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 763052140 1250 763050890 763050901
    0x19091d010e0907150207080714012016081b01030e07030803090a020a03030f02070f150c020f150a11010513061a040507020304091506050a0c080705011e0c030c08 71
    0x58400d0042c2c10a4250f002c0c04100190304000364000c40c2603054103401402426262205503400c0c92615403001143e401104071800c01a03130b00a51003090740d000c00141d0043d403840d001c4003a1030b000110508201d50310b4100f1010404260018200400a00d0130100007100110a001102602d1010b45180f100d035001340c0e400c4c800a400c441c0070316403200303880302111145145038002502c0f4507081d610540105001400c180041d80d07040c4000300180100c4a081c00c01d00d89018103030360020320100300c00406c20138180a484215900e1f0a44070b00340702801003001e680455203004008080d40000c110344003249000c400b401c03c119041c0200303841034020041c1d801e640049070320354034080c03e1030241c4142c03000140c0290f910039589600c10540a6000c5074021a142d908112440080340e20210044404078501070b41000169800310444550001c50303e04902c0e0311005140891250040c2040203003d5400c102d40001c0e00c03401c84582e250130341c04182c01481000303006542602101c0301c45101070006030f00440000c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 763053390 1250 763052140 763052159
    0x129060304050a1e0209090604022409130209120c0907200604031d0f0d030c0302120a120605041e0e0304180212090613060504080f19091d01 62
    0x603800740c040d10a0710a042d02d02d540e0343d6aa084210f41c0f06410042910a943c00c0d400c025003c160300c00071060080c0365030306054000900c900141c0f84940b00c140c0c4400f155106d402d80c40800e80b000c00da405020540d40203050740d0b8a0703002e50000a9014000c43c084c201306e80c7c48402c00103040d450310790007502110b855103481d0400c035511000007449080b8212901203414040108100051040c2c0c02561500494880c6c82d000c8481c20800c051002c0c8285036a0b540c0303004075a20900c000414640c58201510303070b007825150607800d0240c0c0700701e800a01140465210515500081c010b012401c80b07010400030303a43c0b5141000100d8403241c01e03450030500b12001203142c0050581c030181c030550000c012241456a01c0608982421000f1032000c0314580228648903d4205400950340201d41d00024008074a02100505040000d0758005003403151070364082020721405a08803803007030b003074400e0081d61050b00c0748042c901c101401141c6e400148080c0000a0007000351101d038035554007119080c00159180c9010714 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 763054640 1250 763053390 763053397
    0x90a17072c160c05030a1124180c09010f0501090e091c05040f080a060b0315040609020103060e0705090a090e03070f05070801021b060108010b100f200f012906 70
    0x10a211280f80200c01046017003004d01503142c22030b5240b40305400d4072040b240c104903801c07850030b03441c0301440a5030f09441200c11100340d0000940c0800c0340a540d801c010b0501d0a84000c90942e041200071001245450340003003204285d4400380c88a41109039500403c8400b0303901140c4035841504803440500d06001000d0140d4040c186616001c0d0400361207141d5001400d00d01c1d444031a8942c44402980f0811207075009144001c20b0480103008002d6101b0401d0f500c15100900040031155209100703c11a0b000340c1c02440540140042210381d80b80c0528060302d680c0c80b8007070301c40c82481c0d59200000e1192032400303202c0680d1803034005142045070907035403c01c0001411404075198040e11a011500c61800d01c0500505035500040514441e03640320780c24107008040c1c0207100542d04202010f08180c0b122428184a640c0516000500322a54001194500b140c04ca403090301195052080d003040d44001400614403090078020040c6c1c0003107600c0800c69040020400350120392007103102005141c204c016 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 763055890 1250 763054640 763054681
    0x40c06081906060207061b0f0210050f0f03092b120219030912050a0912060b1005090109060801051c171903060605030708010506090a17072c 62
    0x4401c840c02005200c03106403402e98200e003006902043c41084000c1e440002d075001c1803959840d00c0d1001d561a00e803d8900304903420064000d220400d0900b60451180d02100c2e060001d10b103c142d00d4245800443c20307030354425121030520740b1804460ba244050905c00b07010390004017072040c01642d031040c5001c1d1800301100b450301d4500d540c00d01c030310001a030010000c004110001d07900010084d12034580100c0f1021500b0440d020008144060018690843754500644001d10b02c444c403030100071b2074200d0242000c40c46154200410000f8006170b0b42e0003002a00c0c010703200740c8030020869281c01741101d04050074840c3e40d40c40760308501c0016515103a4001201c0441c0181681c1d0800c205040450040e0340c4010f140840c0c000c1800a2182c0c2103906209000140500e880e1052440c202400300509450060160a104040000320f0000317030340c0d9402d881c00041c501c4410044191340b1080403143c40310450300c1000391000030030700c0200032850700c0400944800302841c1c40507000d0b251482481c902c811f51415 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 763057140 1250 763055890 763055911
    0x6011403030c1c09170705011b050a1109180709090602120103121409031c030e1009060605040c0f030b0a031403130f0b1206060d0504080d0b0108040c0608 68
    0x168202540c418000b0149804454903c0c00481062103c000c280d0b24142d403040b100c24091700c1c00c0200310301010484600b02c81c02480c0800c0e03100250002e00d5034078158000d004120f4131a40c05031004000c103410704c07240c03992070403505c601a03580e90b5208840d04c4105444449520381000780140502c064541c0b1130038695014840050a068841d0541e00c21020203070000c0d100c0304580e84290b14590b500000c1c3c17401e21030580002c07500b0042104040307583e07000d040d000411741aa00f035052801c0361f44607610041540000800302c0d0317005180d0186c0c80b401030484520658902d0b0034030101091a082c50300401d400f0140300d9070346007031281c1420030480003000815409544010042000004a0000c10302d00c844000f10201555a03450b0868042c95080203580c8800040012044208a51603800068450086420074400c440d40c0d01c50002070122701c00d0b544481c04143c608014002403000e002e014001144580c2001c0000005050040da120700b07040b600185032401404e8140a131034403624409400640044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 763058390 1250 763057140 763057147
    0x5010e06160c050301060e180706140d112a0105060102061b0f040e1801091203020706060801050a06030516050603011206021e0d0612120305060307090f0603230601140303 75
    0x10021703094500c0b036480492010b00d00824011a9041031440c170800f01000d07002050041d2814a0143c40f420903990303001b0313107440702240440d50300405070040000208510501682d40c0c01020703a00d1000011150240c00000c64462030045448051180e0341c01004160010a903564507066141640f600c419542c09000d1000d205842001c011900079102030940e091000040d172420451010700212201144505681001c2c0824007180c0ca09000810b051183d207000351380d410f001c4c2800380c040c01044e4403007880382d03107071004020301c1c41903561140060301c0c403a005440c052004c80350040030415040c01003960040702080100416520b591180785014410701c4098100010103404011402e0403541c201c07400c800024400c002455503200d000c000d46a20fa1070103120707082548405a428581801d40c03414140c0d00c4000c10090354080003088001e11f54080e044c818500107141020280c0540e1004654031610380104109002c00c10b200300101c002c408004010a81c6414210760755128200b50254041c002003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 763059640 1250 763058390 763058399
    0x1a0f0d1503050105101d070c060b06070f12030c1106010621020a030b03060a0908030a0e0a29061c0209060a050d051509150103030804020a050607150605010e06160c 72
    0xe0140b54410b0b02085480106285480b403101c0b1b00fa60400c504460708281c840401030740075000141e000800b034000d2000100c2006a0021034034500c924038015100c120038000c0c0404000170308808513210041581e007402443e00e038510070b81e03030200d0060060907560840c0e401440100d102c0d600f0a03c11807410960984600e00c1410f40308200c0c2c2c81003c0320700c0002d40300c0e40c5103d07090804110036a042181154200058400c2c2d441e084901c2c08090211a0340e50303201c1c0500040c41d04c0c100600104250051022000c401c4010280d070301c02c002c28606041c600803c60000703075803803429040b4800044002c0600302043e4065900300205414014045a4086201d25002c50151544400e18003000c0c8514000c0900210740d1205030804800182221010351007080910040e4a00c51903803411654036050010362500c41c0d00c001140c04895400003500b0500100703010341442000c143c40c515400b20003004220194a42004442102503689500c3d0444c3c001c000c0e44145480301d5408080c054041e0020850032502c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 763060890 1250 763059640 763059643
    0x306010302100c030c060f0b10050c031213020303031806010501030506100c0512190201060f0605091201200d0509210d0e03070501060305070e040c210f03091a0f0d150305 75
    0x800c00d460035002d5503648c811070117051425003071140b14002e06040e0300700303100d600740181e8070300c01d4042c0030741c042254001051000aa00d040c525400703038000c00b500d4580c544650400060503000c81c0701055446030b50000a0503500a1190030301501010305001078104019406a881140400b02141e0391b12400c1c80c030040c00941031020389081d003203c0080014083c0c10701c40007800e440464000d42103110060a04000854001d401c483304428140d071280902e400c41204039005103240c8030b4242d0180340b996a04030b400381c03030040141f1f029040b9900800607034542c81482a51001640414909030f128124041106801d1101078078025450070340100b0028659a4040d00f1600710000c01c413180d03916a1028010001c0a0002d00301805aa1007010007500e07158135115455a078500c02c0384100b00c00054a580e8010b40c00f11058095a000700c55042001c406140003400b00e0114840e440c0a03d10744072070a010a03c080048030901c03400b00c0320241c1419001c0401c03800030f02c86074518011032007a801000000030320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 763062140 1250 763060890 763060901
    0xa0e060702012c0114182106010b09120303281515030c051806090103180f02010e030109020109150e100207080c040908160c080f1b0306010302100c030c06 68
    0x1100004841110f1080024101c45410101042d40020611061070644240711103240c90402c1102c405c608200703001e10320b03800200007045d107542c2c074001d203030000c20300071103410051084031425910340d201c030300c03c01d00c6180d2a070100352275404646d004600c840b1600030040c0c1c04030103400b00030b6400090300250350808804654065000480c1354a030100c4403e9195058031420034062414104145015580d05044296010f98000184202030129144900764420791002e44d03d031310700c00700703007800c0d00c205051410b8044031640c001c80c000b5040f041182414101801480061941078441c122528104034001d2148440d403030311001007000480b409145995429181580000c85401500280b41060451400e00d0022940c19000328200308006000500e00030071030b088440003005060024100b482c1c548168141a440b09080d441181440042d005020031f00c94045041045050126441c00090548aa80900c00030750300c51a80c2400c1410140140c0601700c81c80d200745000c0c400074441c0d998050850783d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 763063390 1250 763062140 763062197
    0x20a080f132903072003090a06080a0b03070807060302071104091406062b061404030c110109060914010908031b10090203190303020c030a08010305060a090b01150207050402071a0c0a0e06070201 85
    0x43cac83c0c5e401d20181c00ca4034400c00e8513000c0164060510039051580319944c0d400e05100d15820194001032180c288102e19400c142d00700e00040c424004103079039091400c1d0452122030118118004c54002c07409074613221701300c034440c03d035481501110000c0d4403190904044000c20300360f50007a100c0c0d510742070034a065030005105512948030040c9940450900c1d0310440114030005062048059090215640180440040ba203c0301b140011250002e40100e55990b0164850302c285c0c417021810040003070030604c0260304e15603a041126100402014000d00303940d1203440c069090340140c8071600704401544421400c42e402403c000d860b0811460006186501000e0307203000041080c4018010017009009843d0400312516013400f1074600e40d103503446804810704c1800c40004031014007a9000c0d000f40150001070800900c00c5460700c440d030502c0300740030f12103801c6000030303440b124006085c0365100ba041d40c0200040382c0e2440d4050001c0424004154419201030341440000300d000904010189280b11100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 763064640 1250 763063390 763063397
    0xc030204050d030c0c1a07020402030402011e0306060228060c090e090105041415061c08030a0506030d05070c0b0f0405061b011b020a080f132903072003090a06 70
    0x4004c0c0c14441c2268036a6000032040505284d008503d0880e9101a105410303011180103a4944491005a40304001480c10b001e00d40e01220341d901c41c2507010b520032004c60b051602520489100c518002100c0c2058840b142c0d801c540c4000310101080507a0702c07032071903000c1e6403c021100b6901c441d8202c180070f5044501d450703e03070345540c02c0204000c8000040071000710384400501c1054041d2400c1110700500800d2540038204c122001c07032000b1091003003585a180c2040f05a41c0d00e0078030f001c031200505401c4807001d0091040c8403010300d8061242c001c407080c0d030b82c2240c00351005504143c8a0300c400d0307111520034181c0d00c00900000c40c0380c0e95260024558048203803003070010541140400c42c29500482001004401040c51444009801082e04109140e01c803607201e0b69186078020380c0c0e220303000780c0c2d01c2c0d509050400b48000c68014954102c0d410b070b580c64800240381c04031aa2021500c03a21089a90f180025191210358041c464a01b10841010040c0d2080d281098120400f041610703c00754001e4002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 763065890 1250 763064640 763064657
    0x2106050901270209010e0906040609140402030c030d0503152106191a09131415240919050c0a110109030509012d0503040b150f01030c030204050d03 65
    0xda4650a42d8480c81c2071491030294100304062001070000e02c1411075040c0a807800100140c140d507a6030707000e00c0103019031000c00c002d41c0340b085440e000c1d149404c480c01c900901c18201d0440c4645030002e0302c6c0742000e516580d802d286035607154405541e015001c40b566001844e84002c004440c15500b22103081d80e5070140100704034940021441c02000c0e0602d0307902140e80c83c2030700010085504034010b15a015080d21521042e450780390706412140d4141002401036404480700640380707100800d40321140503400c072208000d922510040381c1d80e29800360f000040c00050046c20001803d00304159075004000e090024100380b0600044000e1304c00c111610100440c001440134034050f0403034103215488040c0701c003c0011316819035014011344140b40d200b505020255000211600c0d550704484014000b94800f2a04081a144045c0860700305403011502c441201d400540848040020030055070380c000c00c12203022280f00700550050145441d030504041c5c08000c0410320b511204080e43e01da51180da81d0300f89 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 763067140 1250 763065890 763065929
    0xd06051c140f1f15030c270204080309030d050a1b111002100e3f070f0b090319260f0103030e0a06050306012f010b0a152106050901 58
    0x131501c0c80c5401c00e05802001c08140b020480b004010300170388038414900c46003440604030840c00c400e880fa03151504c403400007030040b03a00d04000c0050111800d050702103810445030248159110f001c0c0c4907010001074480c500061070210b101c10720308841800b802c980010f00110710082a02500b9203010880941c0c01408190301c800301c03d108800f030408003035000c3d008904800300c000a4128014a07001d2452032003913140c003050794020b100c003501ca101600c500c654400c2d59181809800f0004042030380c1010203900000e41e0204080701322400c102d200e44580044884500c0161109036000d8501c00d282c03803020b4080f042c01c0c1000004d850044030f00b0f000151303c6625518004041800d07008046015119403201000b41d0740d04141035030342020090818201000302040200c0a17231421a105094418021280c504003482c1035200d104050001e885440b00e454803103501c9a080300b00c1b01c00240002d4000d10111122009618400002414603440400e003181da0340005000c200082c1c10001183c103484c2031119 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 763068390 1250 763067140 763067203
    0x507080108150412020c0d0b041a0108031c0b040e0703020a08010234020d0605190b010203040e040503090409080c01060e151908120d06051c140f 64
    0x38014452a40209038001d4100c460700318034074000d8402003000b010301a50301302140c003d1106c852122005007810400e64464100442a800c0650302500d40c620065155580c20750046140b0341a1135030200103515004c2e040d44031b48800b600d078000d42840725548000c0f04440d95210b000d88041c203160600140089c5046004000034031a0b203a00184450b031042104012030340c070038218002d03018400044140d140d10221074130a241c1440a200a502c0741196080800704102076000354000c00c2c0e06010047c0502d90100c80c00f01701c440b540c11042c05a40240070030040000000b0341c041d4828401c0c0c0590b81030001c0600400c06a509141c0c00f25080300d40030902092400d001d1091100521303c88280c21a5420404460b402c0c80213101c40036409145800a402e4103001c0c40480c1c5c5004010b080200c031070350003000500120301e40001030207451440c2043ea00044514144c01840c0440c2c10030719010441c0441651460034528800303800c80c03440c0c00b580e00b4094420303205102d00c52002820f41c0d1042c601c60780c2c525644 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 763069640 1250 763068390 763068407
    0x4050a0b090c150703020c0108130b04240c0516150203070c15050f01140d0c06050c0f3d09081305100c0204050a0b03060c0a141215060706020d0507 65
    0x20649002c18080306000c17981c00182080f113110282441c2c22903840d42c18444000c203481c442c002e01031b048910140010404081c60030031710500d0b040c003544410001c407100d507401c2d074084443e4000050740600114580c03e140e80c112068841c1f0400c49003004034480000901a604101c4210011030460200c2c0300500480306240c0801010059080045281c0380d0000c03d5020410300131804a215150444075107902d9060a101205800c286d92280c6181c1c4d51800410541c414001c0744e040e405010024014840001490201c07904880c2d07013003084244499014841c40780207840c0c01060301c121003402c0001015071242e1000f0f94017034854941d84d060543d0068600011580c4080d000d02d040508406100398040f4500512a0341141c0129903522485d800780080e1601e600c1c070660600800d17040c4022071b082e038802071161408076141d101c0d0092021805d4145130041c80300400c5280b1560740080c9005030b1101c08046a110020001e03030405855484400881e04004901c00480740e42c0e40900c602c603034005011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 763070890 1250 763069640 763069669
    0x91803180806011202040906091103070f2301230a03061734081e0304080304090207050709021804050c0a0509060d090b04121101090c0b0304050a0b090c 67
    0x4180c40c003854902220398420051042003511100010300c1421540c440d0492040182c02c64411b2104520f13904240c90041810b075034045c402c0c40f440000103195000c61488400315046102c0d104404068400103403940501c0007840c84c100005800300565003804625003103101c86206070b0701a11207132440c10184c12100039401c0000300d01c0c1298002c1d00c0703044000681101150b101005d0481d0098030500121000d082c040000b002410301c1c0a002c1118240020800340d03950035006207881e201078070081c0170b0303d0b40f00714011482940c000700b000340300e410f0301d80d001071802e1803080d8100c4040b690340d282c0b200103d820220341e1401610950200001e207207407600500e6007261030070f42c03603624204041d0800307031551048401150041002180b11000825a50300c05946660049800c400520301458842c034072151003010203010035000054401c6404051240010075a8400035994146003450881411504002c00c00c5a891186a026038005108410080d019041400003001440b000c2410032550405c1d0140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 763072140 1250 763070890 763070927
    0x10503031e16150e0613020d030f020a0605070e01030c0212031f0b0301060c030f020613030507050115090e15060a09020a1b0c051c02031213091803 65
    0x30301c1100105414100d1078000c400508196034800d4200e035824152803010024106034080940e5000c00316040e04030740182040041a144183d41d400c14420420300c400c10040d4201200d07441075800603000d40059605000309004882807104c03a075454a05458040b1b99070000a50304200c984903950b094010340103083c815001520403000710414441d4103000003080c03242e11865584134642000c22126441000d01030032aa5151b07250f0710307400d010380082c4418004400066000f102050814408900b60703000b054083c130b02c0c20754683c29840c2258640c10205059944c0c0d5030300c3c01c03085045001e90303080c0c0c0020051034002140d046040c00046003020b424044099103d40c1c60350810030f680d46c030341030100d003034034000180181c4462003240704070b40c80c880d010380c144181c04480b5074210521a4000588044a40c125841c0c030b040e00403144014080a0613890081d0940d22418502200200712006001141c00b10940d5121750b07640c9580e401d00342c0f220705614800c0f82c03006a07420018181d1100b9800c600c21403441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 763073390 1250 763072140 763072147
    0x901050315061009050402040b04140d0507060e1201090302070f090204080a2a060507060501060c2f0a03060e0c0609060406080702010902040615020615280b040f06030501050303 78
    0x2007400c01c20001030540380702d003010081c90350149003d05401805040d01800031501d40d80c0b598050003d91b0301c24004c1d1b01e006290b01c0c480680740d1501028030912241c2c880050112240790000554030340590b00d081c8e82e400754901c02d24120b508024030a00c0800350299006241d407910700b000720840e007010b03500070740d007802d004100030320002c0000500300cd44664820a03030000641300d80b030101002d10b5003c080c180032040481c0c0c005609603001c4007820405000d03010411082c0d076103100c107603103e48a041004001001c40d020a200f50340208501410505500d0003142155070031030300150301c2e0302031a0022a66a55602019005420100300c5001c00210a4a00711310344141035002607180d002c0d6206200810500d20002180d052003034000742c00c0c00d81d01610501401d51500311070303403585443c1d04500005128110000720142111241c00390b54000141541c40c40c4015096191080012030442c110700b102c10f450001030032840d030801040113040405051703c58a00300722000f42500c0d01a0301a0780305c0d034403e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 763074640 1250 763073390 763073413
    0x170306011e05190f0f0e0301020d0513031d100302031302030f010c021603030503011e050402040312020f01090305091509090f06120a05060705220f0906090e062205011a09010503 78
    0x855425110846040c040f46e00b42c034440c0000e0181c412050080700d014241003e10421801c040c41400103d8465250a0b0840c108422408200c141150041e54851075051310f110744039000754000c5400c001c0041d07040360220002c0e00820f280c14282d04448255a555044c207828a40c1d040c490711001c0c0700312864500c101495138030002c04a00060080c81d0b130403078294281a0344d0081600004009040c0540155101da0343c0c0d00b401400b0401880244000d40620303605e6a542c1c0d1410701c6095003241d459120503081c0706c0204144200c8107207011303c40722251800c2280894030350300c3d042424868807525607144800d2415009004840d100041b898042d6071100400c100003980200e409940091f0501c1c0403911480e4150a000c4a0704046c500c40421600c014008206210b01004070001d40700c901300e081c00324540d141c840700101c03000711107003030300580103840408c8515905240c0561203083c1b10049190548140d1070b002c4c2111007454030308003000c400394640380030b50038a00011801804200d0240020b45400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 763075890 1250 763074640 763074647
    0x806220503071101020f0a050601031208070c0611040905010e09010b0108090606090714070606030311030906090d0f081602030d080915060114120109060909170306011e05190f 77
    0x71482d00528204040300c0350baa0366442000010203000741a8200d6851041c80d00300103441c0c1c0300a0105407075010410348004440c6005800440c0540d030140e03039252205000307403603450003840d6241e440c450b524010480002c0b400318034050a4007801011405100a040221146086960078075909050015407000c010a481012036070310390026082e22031001e0750f0b864400840d1882800f04440003550004103081e01800a95400350050724441c0d01c0703000003070a02c41d0280759240540d0500c81e83c404c10400c050b4000741445614110040d105031001501003420303a40e0f02c3c01f1508407000040116401c98043c00651408000003400300707a650400440e64100b40908580340c0e01e248814003460840b4801290301648151202800b1210056005032100100240318083c1c0d0420700c15040762600f0044089104030851143c200d4443c0d211869880c1060300039403200d1140c00042001e0306100d90510781348081c2440c000a2105040385940b40c0fa0343d26517117600010510403080d6030a04014850300e410844c07a41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 763077140 1250 763075890 763075897
    0xc02010804110a03120c020306061e01030e21120f010b0304020d0f15060603110408061801150603020a02061b0d0f02090d051c02010c0203040b07030e0a0806220503 72
    0x800400c45640c03410b00e0000b1498045040c1d200070700514484c1100c1450643c0600c2c09130304030b0f200703c05844040d20f50508004503661030200140600e200c9140b8014150301035882100341c003800000707403003c2103202c0244031605041007000b44907442d8001040c1000300161521260f0000f40010388000950600d2a211003a01000f40300a0058086e00d001c84107008402c7c81031740b8016444a44613003400083da1040000d0243c1e80304600119041038104825005041d05540555405000078141961101540f01d604064110703040c0d40340d50b813200c2081066201914141c060045910013580c0c5401c210f000a2a0070130081c0b50050740d80360399204181c5a8480000c540441014040114421404000d884000d118017002150312620a407250410080046940d00c0121075031b102030076a001c01480c0a80c00c1e68a80034a0b000180c104020500c034800c94072000c1c5c006107009290041c2211280c002180255103180c01c400380070342c0700704108100c80d043e140c80c034401a85c0f507409688906140f50780d00c035603a01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 763078390 1250 763077140 763077143
    0x3150507080a0b1c03110c030604050318010908101514030d1d040207060f140f0105010c0f0203100b090a02041406220e070e04050105180405070b0c03040f060c02010804 74
    0x544600f42001181d549000c0c4e244206043c410080c4198030703a2030043d04100030800c4c03440d9180180340da8445c0714580403e000d44039a030000d01031442d0000501c80100340402c1d5130811414028442d4001c40c100030100700300c41d17910201003800100042c080890411088003940b2650740c00d10007000c640f01a442c01311b9000300e0a88507003000914240c4403074820301d003406101c100c1034000d0301c0441c84d41c00303003c5207810031840b0f044201810407002c1c14524030061100030442d00b05010059410040189511540c803018800707020740606030a4a0117540000d08000920303805003011038a88031005414500324030704642102220701c1c0ac52620341751103400880d4518140655100b408041291800c1001c8809034842400034050f100010302c0c0c4a0801b00d80c4014160384000004031014514080d5080910500d8180c034001003900d8520702c4404101c2c3d001d02402441101c041c007807503400141d2030320041c01416001c90b125006c2c0d502e0754104120906418000d6019408200d8207403207250160f45c10105007034005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 763079640 1250 763078390 763078411
    0x8070621090312090804050d03261b16020603042609010f050903010f1103040501050703110712020109051c1b0b190905030d1a0a0e0a020c0c09010e010315050708 71
    0x4c450500740a5242c1c05660300003034000c031491186408155000405008820b0024411500510075008140e02c22904540440c000c03080384400300c140071111800f80c4541c10002e103d01c4070300000d650100d07203150010350303084840c291038011140740c40841600820000d11900e500e00e041c1a03000000901482d100c811030030070b20900045180c000d49082d04051008030032075500b440242650100744001d40c0c41114261400c1d407034180851a401e01c24020342c0b850940e100d106508020301c3e519881100c89041c003450080d50760310503400000074400d10102003e1855120b401e2001040c011000d09149150b400f80c0c030003001002444c50009500140c4e09811050100c807014404c0b801c6003000d00141807154019040d4440491031034000c2c881a0000c8940e000d000041c0034085418500b0703c0465041c9000c2d41203048a0180050700e04a1a035001e001030249240c00c40d802d101c01c2c81d001c20381001003a00b0040b40c3e40c4c0d800c1c2c010320a208c00507803c00d2105020010401080c40c10342801000c42101400b2078850 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 763080890 1250 763079640 763079651
    0x90815040b18120406091809020303040905270105010501091202090a050c0f0301230d020907081513061a070c03150e0105130c1406040504051008070621090312 70
    0x9800c0400182c01d000f020340311083d80d125182c400160100d4900d104902c0d54111801c3d01110444890140608403030303000d4011410213040c1120300b805488028120364901507410080d50840c0c24404100c0c3da0300c00140000a119410400010f02000d49500b160020340d030003414000050300c5880c441030780259418000103054640c0340330b03800c0600c150302d61942c417201d010001042c511669045156032005c1807914003001714039501070007640502e081010794000010030008580c54044c0c6003c3d0b92041040101c01038800c04400040c043c0c40407040070aa03c0341c4c3d036420911641c2d400c1120011110141c0342020b08208050f960001452300c1800014204142c14107615014000d07034001002e8001660024400e51030907000c0068032182c0d50300142ca0001c00c0c0a80001c19101c204585014404090441e030301c2c15007480c0a000150a005d0988640c08011140002d0b603004c0900c903c0d0003500d8a596103085030200d042d071900e10711520714405032200d803402030002c0000c2c0e0400001d40d4410404a4041003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 763082140 1250 763080890 763080931
    0x30608011b05041203030e16080c0d0b15010e0303040308030417040f030f110604091b091401080c0702090106020d0306150c0f15181b0e040201180510090815040b 71
    0x2400c01741f441e40c030246c03180300120004040040007003419120684201c418a0006204008030208a140047d1a000c2028007142518000020312880c201040c14200c160304c1011020903d55400b82e80207071420704011050004108019201010040b000d5505504050070700a030400c0307480003440014070301d1082d80701010400143d880b080c02180c0c4014089522a40e44e800042e01900043d0040602c2c09400d109669119000b40b041409070b03400840f803170300450440d80040d14490006040c65442e0781c42448000f006903200203d06010f03000b594060302120004160241c260390340d540111300712081d0041078469031541b094203100d03219008031558403462210706020510868059060741d400e03040081c0c901e80158100c04041c1d15030721500c02200668440d82c640760f403a910500030600751221003804200550312410088510b941000c2800c14050390704c2e0300180450f003082000034081002e58204008401c401c1c08002c102118803c900103ca01c0c0560710403da240d001840074a0200ca031000b40350 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 763083390 1250 763082140 763082147
    0x120403091206020a02211b0c030a080a080a020c030f030a0906050f01060e0108150f280f060804050c1507150e010b031204060f050c030a030608011b05041203 69
    0x4000c0c8410905500008402d08100b07000e94010041003000d44a1182a00d803821084660a440c80780610f00d0541000d0800740f1204840d0b070105501da07400e12450001210a44e810302c101c2400d03600c00c413074203a99584280d00c041d141c200d00805000c4403910500000d20b26203004421110102c40c03189035190340782c1c3e60199002c024100100040d010341d142c0002c1140441518040c1030503608541c46022085450b5001100c041c142100c0c01c0c040d60610058600b014242144416080d40d0000d20a05021091a918080c40c2410b0001c200714038452060030002a0142900080646094608540f642c5800d488503990366644400c001e0140c0d103503401074007140200e07030701f940d0002d035220341d000901e000e802c00d81b8000341121240000c519460260708002501e00014448400708203501003505080c523201c0180c452030302c10082e500900c01d0420885030791500a1004085000064900084c980c2c104140b10f0700312408006003c0c10340728004d000144075904141a41c0c101c0b030310914513100e0444585001c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 763084640 1250 763083390 763083407
    0x3030207030b220303051f18020306041d06102c06010302190201021308010c080f0403090905090609071512150305060709091a0d12020114090a0c0e010b120403 70
    0x1034030080c110341c400d404043c1d241e0400350168401c90900c0704441001c0441d01fa6000341440b48400c1220405010400461190040e5500c840002c00015908002e985004502e8002c00c0215102d60811820841c1040c03103000d003580903148440c8100144003070f2900940e421207010003600d020100c0c0303c0c00603006a110303804a03080e000d80c06418800c0301048181c003a012750004100d006000d9020300002c51071480c1445540d4074103d140c0d8801910b43c407680c5030a0040c01014000340c0070411005d2001c50806c0442c051540a000b8140090a0900c0c0c010811410040540c00401d2240ca43e03a1507010b005c0d60000c001000261602c000181001e00c0311419080150103510080890060404128110390082c1c0d0038802c49403007042c00c2c02040b100b04a0307001c0c83c11498401580c0410004044030200f9040005510014a2400001540000b0a070b03001c4000604841c0a40346a000040580401c40181900d4000b8040080d074001194104006007a45001da9683c83c0101c1c040c0e5000501803500c00c2490 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 763085890 1250 763084640 763084681
    0x70e1609120c030b0624040812090307410310141609081009140a031b0809030609010509070e090604060207170309031209060f0a050705091c030e030703030207030b 72
    0xa030b507005c00301b200311051242c0062140510b10300507041081810142202214440c041c01005001e00302c1c20070f11000c1d042a00c3c100100c1e0480114004d2480d1410a1005e0205520340e050301090381c0c0c680076041500d007c0032152481402d03820303c200d540c0c007030180c1c403200e0b1f400c1108001500301000004c8403c03140e051043d0712500c3d4601c030301c2c0343c00001d06d00c403a407200c01086e0080c650440790400d1010380655034142207000400198048000004000f201c4852070481e43c42178a07802c0c9894000c0c80000d01c3c0010070341d5400003696403601842061401081920003c00500104844c40d24060b00380a0b103441000b40007401a0b81c0008001c4104800644610b00002c0350b00c00e001d4990800c1c0c0130240da43d4200500b8201d00189480108001d000002070151042d02c15440304140c0b0b5684a0100c005070401420141c01d00405000c00c02407070f0342d9420360720500700c5400e9503032808030780e0b504000f400704e001200c403540a504099010b10100b580440c0303501c03e0303907009146200c890310340b10405c0031a40e019021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 763087140 1250 763085890 763085929
    0x91503040b0702060f010b030606070f2f150418090c08030a020105071707030f0b131e0623030a021201090c08030a090504090203070e1609120c030b06 66
    0x40204004103200d040b070103200a9030858030a551136001030a04040d083c083d600060500748005045850042c0080140d070b4440e20722280e001140d41d8545030031010f180803c00703244030b82280106145580c0310003074220010494000201c240c0184031100c603481140900c0c2035a2001c011452880d02e407035000102941e82c000307803a0141517900e1020300e842c1c1d08100f804800550034880480c9465115400720740d8101240d009080c0c0d80d0710b034003000750002d090111050308965161041030900d40c0d0ba58060b0283d10441c44004030f030820010f480da44492011051200c00a8a0181c0600c002111114016081010580048818440c48001038500200260002d61051240304100c11400b8103400144440d0b00c9194854145034480c642561280202c4844400260f00700104205a241a401c10104a40041d050b01c8400340c0300d40075944805806c6955141003042248a5200c80350301c80407200c01003c072071400900c2040b85954070342d6041003611000e0100c4c1c1056002c14242c1d903600d494851106234609 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 763088390 1250 763087140 763087147
    0x30106140915210607021c0c02010c060e0304050319030206061507320a050309130e0604050106030210090b0d0209040b03010f0f0606080402061b0f030a021c11070b0915 74
    0x5940b1422003c0442500b034040c079008102501d0001503181c1c4020304008000070403001240040368980350300401a410807804a101001249482c411440c0300741c000c002456984e0308050030316150003039880d48035004038004e407001c81c0800e80c0132450130303081101241c0c1041610202d40b22680031f8010410040c0c0443e0410018180e0300b01c0002d0442c080e1900b40401c6d409030001004c1c41030310b074403404a0150250704108685911450038007081900b200d80140d000400c10944000245000400ca42c210f41a80d540d9a041c81540360441c1040f03240010740c0b601c146442c0c00c003400c0a4607802884400b40070306802041d181c215a9a6421944481d040680200010380045040c0400345c00b81842052020345000d5001c00d0051040c4540d034400c0340c01a000501d003078820b040360680444991861401805001c90601c04000240010440141203600500d000d8100a01e200c0650b051420b82c10207014581074081c10300d55022959004807004407000c40c0e21010030300042203a01c1d1a40140300031080002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 763089640 1250 763088390 763088419
    0x3081602011418150403050615030f1c1202162f06090603060f220507030c0f030507020313030605181501030b34030b030106140915 58
    0x801020a40038000d03070361a440424502c0d8500081d02c03a07103220f0012082c00200258450814000200e0500c0e80181c0b80e0f8502a80d1f51956400c041d400d6800f40c4040c4d4402d000c014141c601040780c8500007503284003400258054078070080286404815035803e1180c20b40e490002c1904d2070341039406030104004504410509031510603400c030b212105034084040c3c00303c1026007084034121552100d21300600500d1400415108100f815040145015413000040c0508541034440c0c01c85030400b8602c18050800da03105401708501039030401003148040614140d601180d265100181030400c050b1410700190f940c6803007004a045205240481c0342c087c245400020400031181c0c05144a030b21149030000c9940e080d505140d0702c0c0d0320000d1200541030030005c01400822820140c1c1c540242541031040c1d60155001800148802e40c49000d07081d408011940c05040c0f60580a2003141500031402003080600f4400f01010f249004542c55004892840001e0070a6200d112225803800c0010220aa0303090311 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 763090890 1250 763089640 763089667
    0xb0712110901030e070f03140703060c0f08090105070c06020a0e04020f09120102041d130b040309140312030c1804020d050105100c0f03050f12010801061d040b011205070308 76
    0x1d00007050000c4c0c5860701000001c40c0c0841e1000c1170f41d207952003185402d807840d15a500c03455004040d042c01400b42200c00400a040f511850422411079190501407038100c14001d0700c4240001d00780c45480e4100303820827003440d42c01301c40310b942c5c903910000041e02d541c0e1101d4101c0c1c82e00010304411345c0107440050030710b05d1100c1c03d00103044c9200c0c0440d0503003500c460750b1600030b00b82e0040340319002c42c01c1814000e09607a0030000c03898070745c8100c41000401019400f500c90305540704c016681603000c03030650582071052284012404108801c00d400910004414401003002d910004218514444000c55170401b822500c860118000ca40200150b40765940d803c40703040102020711401e807085850503444003902e8013441c0304131040c1c6e4003e01c00c44800142c2e0f890942d59607100746d50f8119440410070800e900405814002c034040e00c03800c000015a1801c16100f0102c0c8442c030b0210000000b83c503030401001134404118181902e41c400904000307003029103003240c9040c01a42008100f000081b40340c40c80c1105 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 763092140 1250 763090890 763090897
    0x60c03070611040911042102130222080a0f123506031f02071a090601140d0206070210091203021b0103111801090513090213020c06040b071211 63
    0x2d50100170582588103000350a00c81c1e4401c0400c0c2d1040c10108803c482c1d041074241e08941e0000e06108000d0758060780d0b00301203071300442d409103c0d03046043c074242200d1054100d1101516008005261452803038945030001151200010074500c4c1c000c8003100c966100301884c4000c0040801c1c1d00d03048403c0044818010200e10f1214040d030b400c28000644c8510713000440010042c000c00e49100d1f00004810b045000c1e51003602c061b654009002c0000e2161254904054417034103100010f00810b50602c900c1d207100500040c51a813040700d8408402000d66110780841316016811280c24808035082c2ca4280c0d21240c281d4007030501210300da400074041c1500801d940325002c2108500204560402c801981150008560150301c0041030209160145001090840e00c0105051603486a541e9000103801e440c01140d10600d100d8542c0700e5a011800c01540d0000c0710b601000080d030903c00c1198150381c0d20500184003070549c071071a00104031b205004642e5a03c2c041c400351028005103c0b10b02c1050242d60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 763093390 1250 763092140 763092149
    0xd081c0e010c0905011b08040b0714070509060a09090f02030609030706110406081915090b040f0207020312030406021213050c032a040204050a0e0f100311060c0307061104 75
    0x50070302101c119034074070542c640f038103455050f101d20241514091491143d1450080100c40c0c480c0200300215420285030050000f80c1c1c46110340c3e4060741e80104005080086503405940207991080a01074581c3d40c680d8142d041d1f038456240010b10a209060400420002c0c2501035014050300c01400000ca41c040024900540104414000b0404003a22046648620300c121000121414049185a14a1502000c041d035040750040b4101c0404a46c1c101c190318694018219560740b080c0001c60780c1000c1c02189405860520214180b031010340100b510303002e40e07551100c81d000000000a040000c01d50544049810300c202c051401e2030841c2c4407a250f4080080151410f01c9030305140d840911340083d4040b40a600018202c1c6031405410015804c000315035902d0303611680034000465951a07400241000344420903001cbd070a824000c1040500c15006082240d01d40e000319001d00101d101c038041c0c90604030095840a9480d0000e840e40350440c022503200403d003506082500840b02e0785400940143c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 763094640 1250 763093390 763093393
    0x8031b10020f220501020c040b030109021305011707050a141302070b060414040f11150304060b010e060a0806130204120309030201020105310302070308030f15010302070803060d081c0e 81
    0x305043d00304111050000e1141a00580c00702c070421185040903040011210006400422200f00b29400250510f44100c44140c00c1c070b0790b400042111202d10051a0003104c140c030040c01d2010b05000c0400c113005243e001d45100360310107900d4445580c607195103485007248854001c40d203440480c608071200d40c0702030b996070f44180c0c200840082d0081e03000b0b070054000c82c1d00c5203410707035031a030280e80b144402d030350001449500030140410095a180b0503c001c0d40300c1c42c8210760001e518410000054203054441c9685801054180130310807280303401c035404d190401c0003140d61400c0c1c10f603251111b04c0a8440c0d41c00130b0420180d240d1103242090b0708800d681c000d583c402d800030322039a0303240d4014242c100070030211410f45000308a184500c40c0001c1400c0d508581c040e2059a03c400e403a038031001c803290700585800464442072010840e403503400038200040390409103019460583d080d141e000c01d601000d004a40b085460034502d20420000e2410ec071450010659008440384588c058500284952803002c4030301e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 763095890 1250 763094640 763094677
    0x3100b040f05030d1b200d0c1d040b04080c031317010b01180e0c21090c06120109020d0b120a031d090f0c0c0106030803041202060108031b10020f 64
    0x40170b01405011003420040c1050041d03a02044c0c69069944441c40c0b0280224a181e6803414410384901011803c2c0c180910090120146003210407990b8030441010400d0022101c8180030010351103003000d94000c0d0300304255540350031410218a0640c400d000055100c0201924000b62801d44c100d80c40d440040490000c1094aa609006482a1402c2041c802301008403800501030300d108c2401c0315402c00084c09600b4140800c522419000d240b0174440703054251245402c000700402c1c204100046400300351090703805e00801d030380c208030130b010706018040344070fa0003099001d98005030364000302032840d0003800c000c0d400d03132400c0910307445106010382a0002504103481001c4014a091030903281039000d000c030490ba0382d4421680756140005803510480700340401405024031804d009002c00385005a00c1d80355281400c0c40d03c000c142510420b81003d54001d0b5004202c0f000c03010040e50441740c00d20034420b0560b80c44044450601c0c5d48400340041461010840700c40b52070010029144041032141c4042e007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 763097140 1250 763095890 763095913
    0xa0e0103110909030417151e010803070201050301090c0c0609060209040b0406080604120c0f030e040e0c031509341226190c0c061b020603100b040f0503 67
    0x3410b81c102d41007515030340104001c100c001c0130140d5291031040600300341c9419203204103a244c102481503034a0f145151604c1100341104041130005030040804a0080d1701e011001e0340040c0c200c0c00148100c5010a59840b105007505001d0310f0b4811103250700181c00c000444042c5442402500400b03812802640741503e61041800c043c883c070015106004001e2800399aa9600c1802c00c0042c0301c408000c0100c210801c50005028010f0349410600c2915412049054a02440200c84e03000d205520243e00a05942555440100380c00c2506440403141031000d0b51103084092070040020300040000220500300c18030382d0300c0580c0d52131416507002072608100d65103a8a08681040040c8054550036545021103482e41146400c1d1050038070b038003d800d081203030b003003c900300c8100c2c00b452510101e00801c0b8402c0400c11218111406464241007044e0001d00e403c12001c01c0c1014040000d000b8200000414210480312071054001c01c00e4814503a80e9545460b40034a016540744510382c064400d41d031b103021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 763098390 1250 763097140 763097149
    0x6090605180a0b0109150b0f0706050f04122007030b0603060c03041a040f080c10050a1e02070c0e04050d0f090b0f0d1b0e0f032d0c0a0e010311 63
    0x114030341d0031032800c900503400c1500200003407000419000b01c1c0011241c0006c0d207da03c403000b501180c081a900d040c2c0b168114100300d416200b00074008038460800008110006128030700348440b1740d0381403034000b01c400c44001071183c03541c000308651002c0d40f18000000042143c0c420071188245000d40175110309456800c0506900d000c16100200f524120085c0c0301001001000d101da4041d0150031112036039042a29032441c07941c000302d200c02079a0060340c68501d0840c594050a0340040104004000003562540180c02c011844004102016000100142882940000346002c0c04015900d044181818a480c0b03580e070842c40072900c045001c200144d8050b40c00f4107044801c59041012851801c1c2c600b04802130315611174039003402c0060b500c048000c9140401606410062055110f50b1042c005c404100705004803c407414034429800000c02d03400c80b500c10782400d61845d880181440740c17006810140350920f01d8040503141c01030300c2180c001a58103800c2c00c605040780e005200503c3c207000643c040c0b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 763099640 1250 763098390 763098403
    0x6170604020f0d03090b030a050a0515032e02130501120507170603100f060603200f0f07170d1a010c080d060f080319050a09140402070609060518 64
    0x396125030035800b29542410141d1000014501c40e140c030714031171503c55501c03640c0340e0015652001c1c050b5617041000400790040c07041c01c3d00491100714881303101100c6000030381d65099101d840150503407001c420150b10000d0344290010b4601355482951564002400304c5000c13001841041c1c000b4544801012482040303100707144c090010ba03a602660306100d00c40001001201804aa03014820850514141d06070b510544100d0002d011010944a2170500000c0c00c0c1d4004c1240c10f07561562010000803460440030465000d803480c0c140c50743c0c41c0e0311204400c1c12207000d06840a4101c00c4840c08101c0d440103960010803810088403402c02c0800c03d10142144120000c000a50105803203010b41c20210b070714100540011440c80d40301140ca1a161142c0b22402412a40820b0099102203070400700c0b02050324500301401c6003440d140f42072200403000142142d03410310540844541c1c02240c40c00341c1c0c48030780444010f41c0d00507106002000f00c41c41c0c10001054221000103000c0860301e00c0489581c40810031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 763100890 1250 763099640 763099643
    0x15370201061d0406050c0c06040b100504020c0c1c021f080c09031b0402041d0412020c09070e01050f07080d0509010501080a03082e0801060e100b210a06170604 70
    0xc1c1c0d182c6a4440c4c0c0c8490080c500a402d00100f044180b180d0480c07103104000507031240b4820703035a404040c245200b0945440b502d41c3c02c00ba10690060007204007000000031542070940007122603d4010035641c0140c00c03003286001000c0d401a4040f41003240c40070080100184c1c22000f9078500e405a600c1c0304040813940076517205658941c100300503280c1641c12951041c9000308008100514055513980d0400f80201008003400024140c0d40400007070222050100c19403280c90300182180003910000150b980c02c00505440074098042142402039100344181c0310b104c800d140b01e26607614070030300b09113025400c00520080214203190014210030418054103048900c1e5000500d20141030307540503501954001e101d6190419a000c4080003441d242c0921000b00b00ca81410040113030414a8846c00d5807132542006400403440018002c000e02049000c0003120010903071651250b5041220031601e0040103068605030802c0c0081c08021089940040100c40b0100c444c82c007c0d44c400403900e45c0b0b80c00d04030340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 763102140 1250 763100890 763100939
    0xf0f0a0305030613060806090106031e0302151312031b11100915241a0901111c110d030b0a1a0c0d03090c141537020106 53
    0x200705141844211905480c0919001261701500d9a140d24900441110b03200c89a03034490008200340300007182d031807520342d998480703500c07a0703080a88002c0d541e45104001207031916a0100010a112488100c10003129032000c00c49008000c0c031800200540f2036007040d202d0242d6281031200302940034007241047d0400c010094030414500a41c03900081001c4807041d00c0000c10072299030480422840b03000b12200a01d54180190118014083d468086a130088800b00309070a41d070038000a501e00c1604c082c52030910740f100487e00004203007070920a100e894040280000d04400b010150440c400c104840300c48070484240b0f17102444210143c8090b11082a0001d403280020704c4403202d01c0d0590f004000b0445c003d180340104820404c2d1400c2450060400020769407102c503020403680d0b0134854024102442e0101421140c01c3c0081c0a864107401c11400f9042c000828600c0d50350302d032072412841507445400d40c0030744c51018600e551211000340a100154170b02800440c51401511145903100001c00c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 763103390 1250 763102140 763102147
    0x5100b03150609030a05010501230a08030f0703030b10020d0305070f0c060c0302220504050c030c03060f040e07090501090b10090e07020c0a1805061203070318090e0f0f0a0305 77
    0xe206456212004844d0103029015105010035000d0181a00824003a4000d1903680c0e203402100340c4c4c04001f000154820106001e04100400000040c0e981d60004610050354886d079601e0190b0050102002c0d20341c000e544125611105134020801100400d01d9407400e000b55642d2100c21150041d0303840f4080041011085400c0204216501984110b1418100180b60540b070000d5280c02000020340d00001c1603440000740698180340c0176050f00415210241821414080c0c0741109070300000f01102c2c002d810451424900e5922600018181c850003400d03a546603440c0c1c04590080c100034003a1502860405c40f003400341b800d0526030440080b5095071920351846c02d00c0c8580f410752501900c0e040440c17040c00050890790b0780303440168005101041c8401d0303c02600d0150b4005403100102064401c51780b84d40c0b80080c290b03000c0101d5000703a0780748c90405815401e112203c88000305640140540d18501900c030700e4080070008001401007038502c211241c110300782d045c0640e28031060400400082040c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 763104640 1250 763103390 763103431
    0x1b0906180a0e0f0a050f0c090c0306030a080c1608060c0a0f0210022a0601061d010201020412030201020c0601080613030822260306060f0a1b0605100b03 67
    0x140c5196004000400d010580d22040541903181807080499403015401210240c4200101008290b0790b628003000035180908060001400c9208000e107540c038042d60004c00a00b89075002d201541e80703594047e840c00e444400356041c2c1d81d6214900000e400c0c014081c00b0b40421200300010b425440f6082003281a4501002c101e4116500790840ba03501d015442200e0040e41c00c0901c030300141500c500030000e14a40b00b001012805c2e4400d44201501c80c0b02d4026600520000354814010784101180c500c03c09811102d000040f402071040e580035a58034112912a1420140e041d0020400071801e00d08403006079072507501150700c0e6107090320110b00c440310a0400f0400a4001d01c221640621581d084903480c0780c80da440c0c00d9940c51403c0c821034444607200c441074009002c0ea40d10f110315080802d549800e40c9400004a15240b01c2c0c44541200140081013006410b0b115544a10742e0007005010030885d003e0900d032480107044c041c0c4042c600d0341e62201021a030801c1d0041924444e05a8110610003040b94 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 763105890 1250 763104640 763104679
    0x13060906120905210d1b030f0c0806010f0c05030f03010e0105120d0c0606081510062115030c03080301061d0102030702121c18050d05030d110702040c021b0906 70
    0x1c1381034924200d0300601c1341c0221421a44640b01c07030f8002070b180b4020444280b10004040300c00402c00e10352000e2074000aa0883d550206d4000d500c05030a0030030703103e07001004006a1b50001d0000c0d0040c110301c000a405a04c0c0304005010794121420008030b184141d072a8820031040e0062088400c02276841080e40084403841045e85000c664080e42001400030340300c0300440e0500980515030101c943c5000c00780021490103c0c006001031480d450b2031080348100c8092101c09502044440106648030400181c001300a0300c80d81c0015503100856640782a66840c2100144e0024420140418040985540040e564401601304003005030301440c41d00310701e42d080145080d149070001c2c00c24801c070200044016015807050602c050795031a842c04004010422902c200c245070400c42c0105091994040007030700000980c0d5260300a43e902003044101a201c1da20940514100a0b502506114083c074000b5008118010040300710485034000c11a0781042c04120001901c0c2d2580183c0352184c1d114507102c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 763107140 1250 763105890 763105933
    0x3150b0d260d09020a1e05060304080d150614040501200705060f0c010b06070201090e150402040b03060117040213180507090501050a0905010f06050f13060906120905 73
    0xe68005846800c40e0301040614035801440c61026995500c0440c14190300e0280b245c2801003c0c0019035180d101c80595064070402498407074280624000b00210702084030030401d1b20980030800c842004180b100c0140c003401c4c0c1d88540b040801003000b000c00300760b091034201c3c111010703a82c042e110300411103000041c96080090b841e50192017401910300204640c0d40b002d006118004864054903140c0c05683e40103400c417001c2d00383e00c82c803c80c410012500181d170000340c008100c6603400a801c41c00d59801c026074841040070703454a5840b0384001030205c1c85008080240d8083e003000e07616a405011400584d4142030410b4070081c0d841b080303241c0036843c0c5881d2033b000300c1141c1403107000310140040241c0e40c0768903002a9402035414075031980d0042c0b0007070030b140c0a04c1000f001d01c00418015545800e205003075000880c090401002400030f404151400800304942500140c1c1e10303000d072465074946000300b80e620140520380000d6244110f0328035010b16030003482d12203034100000c0d004d0b10802209500c0f00c00c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 763108390 1250 763107140 763107173
    0x8030f07241d070503060105100f090e010305060f090604030c0210022103060f090c0a03110c0d08070818030405131407020a17160f0302030f1303150b0d 67
    0x71648480c48425881805034540300c81e5182403410500c005000704030705001d05504503a019078004401040a6074844a07003140543d014105041242c0f03003148210307402c001d10b80018100c02040e000000c204140010355602c07909009082c0e12458880f0804591688000d440140004030348007601c101603d041445a030f501e14182c0100d5a400c01004030300d8482040f2140e46484603d0040100061400c002c7d0f550320441c0c008a80d05040d91400344040710542c041c1d00900000c150b6503400c41c2000c424508211402c0003002c5007110f080c5848240c00610010b8102e410100046851010030581c05140d03031500d4100c85404091410181440d05000c10740d2060200c1c4410942c46200201d140910b0b0740195001c3c1161b580a800c00d403c040c10030381014960302d1141050190104000b6001154103c01030071b200c1e038000880c20f400280c1d410102d10b54045c00e00354810401d000611203038007038004c0181e4030807a4450310000b1080c04001c1956001c680b940075100b41c0082c3c0d0706c4000400182e04071284154032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 763109640 1250 763108390 763108433
    0x10b0703030e100908090f2706030705040f02030601030e070b0714160303050a020601050a1412010e060a0b0901090c090513021c020a1d1f091203081008030f07 70
    0x1880301c02860140c41d8410001d035860140080e0700d1010b410101c40600d00c4500941c1c0e01d080c0c8c00700d00700300c100301b0801744c000005140480b60085881650180000f00050030024401c0c400b0151420300301c4000c0d80305503009404285805c175603603221440843d002c0211804003001c135043c0b10490b1200c0d0001a0300968000e814003d1144024021081c444150050350082d99410f44600200038041d144c5101a00403e21441d0180010410240c105403189001c03a01503c1c1c041da6406900c0360a4050501115508420b00640c01049500c4000b980b00880c005411945107005036a40c2d82a64100c41d2560101000140041014085d90428003540c0030b0f10800b2003801840c2940f041c06034170860100710411004290002190340391140e21007401c40b0594607080042c44e41a0941e40021f03070801004100048031100401e03000c03107240c01501490b000340100302015a16810502d0018a1428219100d5181d220f1144000c11480c0c000020b40c0c6554031000c2025180c0880d58503221102a008082c2d042c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 763110890 1250 763109640 763109653
    0x1d0c18010207081926040909081b010c09060c0b06040506031906062d03030806060405091008011d190221010c120212010306020304020a0512030904050f010b0703030e 73
    0x38400d003001040403004030040b00300402c000038a0402c00707815140d1442d901c00d803150b003045c840040d80031088500f1242c03484ca00007840f501d5450900740502400d884507042548060a20b00c0541741034010003078205141e903c0c0d05a090300c46606860100807200003800c60b91040b00050702c5420168400d640119009044562503040c0c6020302c06819543c003401ca580c0c94450200300034100ca040105036145070f841014503c4003086c46a40b60b40844a44000b5081000b00c80110394151100710071038001d8078000e4110b20040c5819044581810300610403900e03103600e0514020000c1103a0546032554044880c094240741c41c1c001810111801c0000701070344c1c000340b00200500381082160410100018070b00002c20302c90280d0402501c03660401101e40302882c0108840c980550014981506696010304010307265201d9002003000754030a601b050b50026600c056824038807100001030400703010102c80c241300300c0c1d0b50640190b008030f0081c0318128101c80d00b400507400090094021030601011102125027 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 763112140 1250 763110890 763110899
    0x60605120a090210050c0105060a03051f020c07060e1806130f0b1807080c0406020c010503041a0108060406060f0e07031805010528020c03071b0b03040602041d0c18010207 75
    0x13007001d01c030090040428000101c2008101b02030052550020085038040328980c07564807196101c1d142d04400541c0703144400405030765039a86a040d1040e50320181d089503803194070b54401807e490041405940f181c04040800c0441c480031149091141b40d001d040d00714884240003d500243c00f0b80c1c02d811084940b240110a65900e4288aa4500d000410040005424056000781c15030344050b1865a94a604000130300405400141c007181c6803600f03103061940c0b9955402d0410301c0aa80880e81514000c403500001844200011420b010741e0042d0001c2010503602e01084201107424854811400e04401c0054078003402940080d1140840344035407925410b030342d9074450071584101d80d05c101c0c01003040040032100c00080810107c2141001c0c00b1460080205030180e034a0142c50700040601403900191b541c0c1c0482010f448008020f40600700742c40e82014a4110042c2d0814001c5e0b0090000d6101e02c1003010351209041809100b504043c2ca2505650090072400540c84050f010306600c00c1c4040000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 763113390 1250 763112140 763112149
    0x403032a061107020f0d200102100f020a14070c030f06090605091c020f06011403031207030203060f010e010905013203090705150a200609010c0909060605120a0902 72
    0x2003450b6a2038000c2540d8000920400001c030b4251940a070042200001040005086140054580000030301080c40c2201d2400101c1c985480d80c0c00301ca00d41410050040d800c8032051b00a003000c10102d441d295a00c905144d248402802250310241218a24010030004500c4881c100c141c51030240e00c0215183c4125101e10b000d41d403081d5000c2c02da50b44104960414a4085a0000055211407000c0d0442c80f0000c518550b5603d010b01a501d05000d103002e0481c050b541c200115842c008911803000803a1034800b901030000e4100711031340745c0100c8054078481503941c410071103c811030505840e241800c5d03040c6401110000220072401ca0141d01440040c0c0b50440d102c88201c21841800c81d10541d24075140300390a0500a007544603500a6861031140c00802c9165816550500118603051100c20340d40360300c1c5030000102651445150240310700b8481d024a0640129500300020303120a0005070b85c850944044505e1031051000094050000c00284040081c3c625000746c6040b401040809194002a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 763114640 1250 763113390 763113401
    0x6051512060610030207020306220b040f03021c051206010527180f01060f020c090408070204050906092a030304240e090f0402030a0b090a06050105060403032a06 71
    0x34851648014100146498071200c016001d500d00d2800b942043e04690100303503a03650151252001001c1c407194440d040c00f80180724500e0f65009070183c00e41d410b040c14900c0c40200040d03804c0c0c0060094411503550109541020703d4100d049a0380c96140200303520228081001c050300690400400300603020303c54056401c0a80e0058040c40c0c0c2105140c00142005014032152503210081c2c0b44400c01c0110301404140518110780d41800d1154070100005800c0b801c000150240300d920514100a002c280304584000d4103140b4425101003020791900c14003599100000c440340b1039554401001c075000114801d5210032080300d440614165030f40c604000a085030460781010382d5800301c4800c01e0b007940700785111942c400d52050801c0304c0b00800c03060200d401d044000b803039003400610044c00710341103440400c0900b8100341c0150801280d0f041c40007440e612041700d03060955000f403c280002c110361618404640459a25032034186481340c0c01088a410b0108a407260025081c1c5200717410041303503550054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 763115890 1250 763114640 763114669
    0x1060306051207032d021003050910140c0a05070507290301080d0503090f0d050d0608060f040b191503060501091404020418060212090c100903060515 66
    0x420124100320601c14242c1c0703184078446066001c0c3c241040402c0700c0402030301e8030780b403c0124589640c45d50031480380c504141c240c2c000e4001c11035061200c0303083c0d0b150740020301901d0080305a8000c48000c84c400340c262651116404942c010b41c40100d02d011204034000d280300041410214200302c00d030744586080800e40d61010940e0b1105502c00020307100300e2154080d40410142001e41554100ba009035030312250b001002040c4040000440c0703440204021210714006c15008a90060005900c000c000760002d64400d880c0c42c0c1413001c00300d000038001c214071b40b08006240d119079481c1d0300d03512000540382c409010140f04540d0500741d840d03400b15034007800040ca18140d5540c0071507031441c540344044400580c8034110303040c03030114040080600411241d0b00b10303404650104071861000003440d243c08000000400c05480040c41d0000c801ea14184540f0928002065a09081198041c0440b000b41800400001408100d082c4001002a07010a4110205c400940c15100f442c001003007940001104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 763117140 1250 763115890 763115897
    0x203070318110a05030a151a1306050a0b0f07060b060c15041506061b1b12021e09071211160b070e1309050a02151306031505010c03020c04050106 64
    0xd0b008090524000d45001090b013500145034414207074a800500403030550000e071109480e594090214904031842c2c018103940206074120001189800c14000c0445100b200d008561400b0b0016041c9126401c0d90f00708007604600601c1c046542c0e540d032004101c070504665003c4414003822071503800420000c000720601ca0803d2100d400c060400d45d106074207602d02c042c015828040140415684074400b098403040040612031208282c1c500f06045038004000070314004840000000ca5611520b04221031a0007070381c641c90f5806034400420715150180c0d1120b44c000c0222808142c409126003008002c076800d4000000d1860f42e07018100c4a40d07407207090382d072142078604001e800a00817040c60683d00411a07050444803d60008045116403028280322035916594044c000d060103018400194429402400030000710113051803908550231094040d0380c0e01d000d040303021909501910890501c0300600700040d03006407501c00112001050307148100e04500540366451400e8459004641c081e243caa05c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 763118390 1250 763117140 763117163
    0x6010e0a0e030301150e0a03050f160e040816050c1507020f010806100f031e060303021207020d06020d090b0c0a0311040f060806031f0f06050d12030203070318 70
    0x2560140e665811801c6410b0b04108010000002d10300740490701120181001c00701079803804d0005070840d1403580094a0f602403c0d4100d6806000840d604c010b0b0403915402040003500d640e207038003016000300c0d4018203001e0200444e50581110300314800440e84220101d58460600c1004500d082519070f01007030340c2420118460702185000ca03c10b040c0301c502803a01402a240c68400100368a1188088101380079030241d1483d000340c480d41000c10660f0a0101400c070000f0221a0800200074521060307006010782d074403480c0804801800c44038015001084141c1642e00d03515240000c1d07128811082000b0b5031780d04400000340d451b040c010b100d00300e004802c9845800100000c0c007a960b038920804d9504408000038021000c109070040242c0e101450650816944d00780402e103401106c00c0290300c3c04030b041ea008a441501a08108c901c80d1807185e040c00925035030001c0c0048142c0c0d11200922041c1003044560800d8441d80c05103074800390624000c224440c80c48102401700f00000c00660381c400394034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 763119640 1250 763118390 763118401
    0x60602150606120a0c02030417060916081b011b0f0c05030c010c06020912060a0c020c040e031c0f09150506370b0d052707030201030f0204030506010e 66
    0x201096a01c01d0041d500c1c0c0385007440000550031800030040925403580e5885100d50402482042542d000d00505042c0d04000c0f115141c9a580e40c010440d0004000d00c00e0101800c0c03088000c2c41e080045030000e8005001400000707411070302c0f0312805144d0904000002403480740400014426842d881d006030304c0040c01154900349411a111180c10641c0254000d01000100b42d070300070604807240b50082801a1101450800150f04464030b0904503518810107007400390614441e8031140014015400f1180490359102c18002640c034180c0400186400c107020042280c0e41e04145a0f00c9401d01d04000180425500c02c41000c54035100c4003034900c00c2841611842014076449001d400017011502000242c80c44100440b100d1305040c400328aa05c041a0041300b0503da40700118003422840300c015445203942e810110003841c00311200c01d00342c05a6040c0075600d803990558419040345001c081d112180c15038005402400141d00303c004a264204400404100d040c002c00e800303050a0200e405071410f01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 763120890 1250 763119640 763119673
    0xc0703300e150a09061101020f0a02060717060a0e10080f0f010e070b0403080a050903150a05100803180d080c06071829190e030f0a080405041806060602 67
    0x2000b41410010030800203c103400110150860f4458036080c0c408a400700c2c1011b01a0040c2c809840100d9404960050340c19000300d8810b104e030101c3d5842060341c440440040e8000141507403101e401400144080c00018139111015600c00300313440884c507070a030b510010540f910004030f460700351720342009000c101264030a019285662203190001c0c00e040d414030705c01170f10500c294407006141c02d00024489481901400a07141d402c0c0e8000d007918103036246030140c10f85910f421158400000d00d0800014400300103020302c1003d0360340120086062004a1030f105580e98008500300e40d00010b48071104001400300801050104c08007030240619060130040980006103040107000702c1c0e21500801d10038407602801e03821030f04000060181c50418a41ca481c051407249080d8280d042007111803504401340c108006004610058007141e690400e100880381e210540c815006022400c02c00007000175103810303000200e5601c000190490301401507501d0600700c031410f920a60240e0030418110340c80020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 763122140 1250 763120890 763120909
    0xc0a0b0a170f01050f030f030319050f07080f06120a2102060c1903060b1303050c060a050409090311071e0603020906030601140904140415020c0703300e 67
    0xc000214580c50305121190502d0784405000302405501e11a1401c0c15580c0c040003100810513404040c1c0b40d8a050a00c61000f4028030001880c0030b440c24800440e1070030910010207413240700a40d076508110741b02d641e038a400080c800303002160300c540d215001c540c2150090261321156803241e00c4110141c404015260b07001c0a03461410010341d0800020000c1010401084a505403c1403e90180107035200000b079000384240e420500444501043c40300b11107030740c0fa0904068a0240b011244100740c103804108251040210f90000228184010000030340c494100c0390600380b00382811500602e095241a1800e801d82c0e1110130b101d100015072801c40c04007800f401e4050041442c0540c43c241440700801d8280c800a08214100195034203000344100c4140305440c0803081c000c4c400c1c00034414515031030400032030a480a482c0e0040c100c4500362580390038801c80300f031071140101500540b4610748884800340c0d51181015042d002085801c084203e01888500c400403c589a0b14881080d48060054111 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 763123390 1250 763122140 763122167
    0xb1b060f13030f020102040f03030c020301270605040606030f1b0608040209070807020106080d1d040b0a03150908072109060e2211031e01060c0f050c0a0b0a 69
    0x8803490601041c04228242825407540508154100c4084070741c0480c028861988515034501560f07101208140d807041e12300740c01d42d00807402030080161202008501e1200d035080d01142d20420b00c07469000502a81029620034020b102c0003138800e9072070300c59001d0138000c6a1300311100e01d940c000441e54a503803400c1e1a400384c6034920301003030365180940c041208008041c101a0510003a2070014024a20035080000905918400d0340c5014001182c05846411154040d0980100c103186110050030140f00b040311058008240301465451a2a840d07140c1056241c0c501903240c446002071701040410b00140b21180c81051590350080b9503101d0401d034424050782075010003035006410420542c1c4000d41a10409040351150082c0641049880040c00c150079510301d8107041000704400c01c0044c00246102d03600d94040c04840c5c1100440e41c05c0900e40034043c2c040402c101d50404000310b10100102401d0520620450304010522400030b03040188071340c0101d200e000001816001c456115110300c1400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 763124640 1250 763123390 763123411
    0x1060e0a06080411040e0f0f010203150d0507090222080a020a0e0609071404090e01140601051201030f03121d0d0c021e0303071a0916060203030403110102040b1b06 72
    0x10700301683c0d81020b81d040132075a54826911800700749606041032150174465444c61048400007441d154505002c5d40044800a50300c02044a0031600380c20180303140b824141d4880041e20100d41400c2d03d440017034200c401004080c40d102014140704d80e0035035a0100240414400600d09000d40d441000f49148454000c4c100c1c9401702024041d071501e594212a400c80100e040600101000843c50303000d81c003407a0302409800b8203010307550146401c1984503a050300d664003081545940c038240196110b200e001c506200780501c0380e00400c040f8100500144015200e40b41c0030308200c1480c81c0b24400c0da1204000d02519007004281403524a4040005404078981400c202c03200941503000103044e10842020021040381c19809040c86d95824000c46120740c0d0f1181c280101203070070b030140d07506021007215015094807914404451441c203050701141201d105138011844c6948555044038401f1a1310f078070184942d001d1001103068011000a09580c961350814a405c00c101c24406901d096000b034a0078104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 763125890 1250 763124640 763124657
    0x120f020a05011416080f0d0510120507140103020d020d020307120608070509181509060105061c0902010918091109010e1803090d03090905090f100903021501060e0a06 73
    0x4100343d002c251030807030002501c01c110f07540050801090070312907a42a405214400200c1ca401e41c022640720074025030610091815140c2c42d61007944410307507145409072240d40a03070820031108942c013080c20711121042c0f4015050122005070700e8240d802941c61040b506030044200444294010803c104240c4019030501540f46449100c6444c1e000702c3c02014043c0041000241014105254035401c10341d1140031100381e11401086025103202c00e5400205a00810300000b5061034010155003500405210b5402009107074100c7c2030040c52400d10407414000e00c650001900b1401c10032117266010456404600c03003800c0d240424480406071b10342031043c084080180982441140d0256000c40d0003010080032008070344200c1d20b5402030340401c580c0040b416440004040d80001e0400448611083c02c0c00251140304034141c40300700c50707014038400e03a0002d215200c1c0e04c50250822104103002e40180d5800f0780d060442001e140c2c409800c11b5020031446070000c495810b2001c1d13010020901c0746071000e103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 763127140 1250 763125890 763125917
    0x1401060f090c09170307020a12050304141c15060603020c060c03070c060c120e0307021f0c1a16080714070c0504020304030f0e150405060a09120f020a0501 68
    0x1125200d030050140403507407403241508150041e0010405001c1101e2210325490a010806070b581d4002e01e81207004240c20720b0300160141445601c9551240e00401842c1058200f0300c0301400c101ea58403000394080e100301d401c00100148100c0d442c403091700404284402c0355590703d039182500c446a00130300c201031041203211898040800d4a90f0096403550301c1d55525103e0850849800340701100240c6020300d0003002d40351440d0001c508281c0d1010680341805081008141c1649030701508102942006444d0074134014605070302c910b201001124102700130744041e9602d4446016240ca9010140c41e240d150501486d030981d81c05461208030b66281840c003502e0548001403450740d103098600701d0b0b85000300e10482002000419072000d0f1a025100b1034407488c4c01e0030004c00700c0e03518021880100e100392004e440315007000140700445840110a8a10b420310344403c3c4400da5100d000c50310100002a103000c140c17518400f607600c0f100d60180c00c0c2115808103600400c0308640c1c191384980c1c18050384504820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 763128390 1250 763127140 763127159
    0x2091215150a090e01060305031305030105180d030b012a0b010e010617040f0b1302040e010c0c020609060403050106180e011404030c0f0c06090305011a01020312041a070804140106 79
    0x425143c4408000c1401c3c142c0751003950250030b20f0340004060717020210314003855800903c0080200d0f9800c40c0284815115100c1b00c81592500301c0070300620780c200c08000780943d17010b50000382d00004180751185260411b6240989030210581c00c0400710f0f010300400c1e405002aa460311405049284c03090031a651404101906580d0071040c054401021000041e040c06100030251800700d401034811412807802d00312021f810503040204901c110700d405a80d111601c414401c03420004501d4845844035070840d020412584c1003c071000c3e1340704c01c08120100004000380180030040c40402c0328200c001c4080c003900f03001d03a5032420051141d6854841045600e4656014450300a40c0500b04041c00c4171050800340c00018015a0160403081c0c44c2e2070014549074424441811a070107040200082c0e88a121195210768030360302454010390041c4150708004590b500f00710b400611a024001c00c404503850000b00103402220180007050628080009000807000641e00000c10329000304005410b052044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 763129496 1106 763128390 763128409
    0x90a020a0f170109050d0e041e021b0303070c232b03050114210a05030712032f0c2506050f040b030403030209121515 52
    0x201c41e440b06128101c10b10341d011020b13200c10605074000300d401e440c801c0403480c1c0c89540c1d00c0000c03040140c071a0f890984030524480143c3c076813003138840078100a00c544848002c290020802c00018542c032215040e40c9680c0410b084030034100003c420320120035050020026403151387d0f2081e030f24581c103c4c00422480c40c028030417440c03440241d400f00c094500a20610840d9510011400d03d1494484084a1212482d1200a2a20341010b150a01d00060054151780c0c0d50000141c0740144190100142400e03481c41c202030080b440402094060882801102c000d0b0401314110701c02291a24801c039800c055200b0100c035091035100640c85c0c4410306903514070074911054080086c40ca0300500503120101d400018140c00c0a00d0710310b41810075031005100b20101079007000307100f1b43ca90b20703050401c02d5112008020142c1e0f8488030010002010044d08a4450843da013070540000c0d9120ba03c0e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 762949640 763129496 := by
  have h0 := BRFrame.cov_init 762949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 762949640 ≤ n) (h2 : n < 763129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
