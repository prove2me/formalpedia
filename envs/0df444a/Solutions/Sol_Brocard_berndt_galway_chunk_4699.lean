-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4699
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:27:16.000021+00:00
-- url     : https://prove2.me/submissions/5582d4a1-5dc7-41b4-b582-bf1062da4ae7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 844964028 ≤ n < 845143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 844965278 1250 844964028 844964089
    0x903150612030307080612030705060f060321121b0d0915091202010f020c030301180902030d05030609010b04081b37080c0a090e150a0f0c08100e06 65
    0x5c4001d8003900f81601c0300c070190b01c180a406540c1c1c0c81480c0014203564403070800100508040c40c1c6030384c0d115002405540c03a218103840300b10348070100340d15640100c00000c500b4201c1111000000380d80304004185612003400b000061100610500700c101030f28648454030702c018002e188298040f20345a907641000340f1441418996105220444600015424050b011010010b43d009480e04041e03103001641c503507440c18440d25240c0d0381910f005900d072911681c2c80d00160340d082c050a0009501920b419540746421400c0181c000c0d016000746041120a010500a19000080302030b00035200602010104500c0c100083d080144602406401c05600c40090704281401520b040e0a0110b035919114087d03c0e40343d11511400b02c1c85001d5006a0b81902c00c10080009400c04010b1003c100d0a48028009001403100c1c0c2034000c403110160a5101e00782d414100009100c0c01c0c00c0b00c2018640340314141040c0343d130117000e41c1c2184034100c2040751041c00b10b001540c81d00d10400402002140d01180d061894 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 844966528 1250 844965278 844965287
    0x3150f150e0a05061e0d14030a1806091203050702032805160b070b0a270302190c0b09031e0a0b01080703080d0c030b0d080c120903150612030307 64
    0xc0b9080c01c0520b0401021822900703002099800000c0080f0205041081c14014000225983d40098a00c1d4a0b5101c3c902c01a80c8140003c102a0a0310f546102c629501595200c0324503030f05502400c1003181d00501084010100402100601d50603d046650707400c950000070b141c076070004549000240e0409460491021100200f024030b8400c9080c1c480c441c000015001c0b15103030f80e00c0359a68010041201e40005000000340ca540f00081590000e40a6804c2101d15181c40100212811100d2400c28201c28540c04101010201c800b0728400004402d1f03507139400d02960704a2180c3c1100c0342020900c4885550107104100450300468005628455100c4507039503502c840d041c040e14148440400420340d02c40105030301003600d420540a070306c1c103c4101d8203c07008040c8003480d0810035a584480850320380c0d60700010001c003400390080c20307110706185140f641007000e40e034014103031039000b0805040c7c43c1c2c401054088800707500c14042c8185660708000b00d03242148951007280580000000c2281c0035801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 844967778 1250 844966528 844966531
    0x1c0b040e010c030f0209060901030b0102150405070303031d0d1220090a210308100527070e130209030c0d081c29060d060b090306070903150f150e 64
    0x1969020b21584c0c0326030503034a0484c410000c1d2a608072108000f00045035002e50001402d440c011b20440d101c868005048000302070090714201d61503003118070100141035040c0101017441d4006041c00c0024061b107001181c0d1094000850003e11062010401203424a030303001403064a00c0706a118503c1f01805008001640412a464444c4820400205109140690341c0240d0f50a504540c41141c5950300c081d508a803006000c40d1146120300710105a5450b00c2c1d0781c0d131007201c0046020b03502e2500511851042d10200400c0c0c00108101000d4181c81661034035403035405207240c06001030ba10000381c000b090802c0314000c1c015411074a17031990f04041102103802030800303984081103103c10a81b100c0b5144252485c220903005200072070810340b002000900365141d00c0e07682c02408949004589000c11054603a541e00c20444e109001c0785102d503d080620030107504c04164500140c03c107045948000a07084540c00400f19596500265100113000303500038445801e001e0716502c40240d5680c0e00d4520403a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 844969028 1250 844967778 844967801
    0x2010e0709060630060b030708010e060a03240c0c030f08010f090203060a170c0f150a080a060801060b0702010e012309010c08031005120703081c0b040e01 68
    0x10303406001820364654820002590483d6880b140c03038051015408107105801d20300d2011403d051020004410907500c0340e0401040d010000c5522881c200030060300402d416842418003540d000100300c010781d00c0241843c190b81c1e00c482032140c2c0c50a030792150180003e901042c19015460480e040203101d42101c600b0000c18429665180c0e2040c100600b281c043c4400c0c4551260760510710f00c103200d1440545c000d9544000c01400175542d00d41e65002c0603001030315068240c1c00507040110046032a08010841881407941601d038480b0314032032000f07600024400c2140301030030040000d000c2411039060b600300c80010090301000380b260079103411000e02298840c0e00300301e01080e4820440d100c2540180100b03076900120881e00c1082c06460031f810111a4003c4000a0412450002d0380300043c03142c0c1c018501806c5404800b1000c0c504100505c250704400758802d50040c0e200704010000a510f0340300300c0300c01c0d444100850380c02a183e01403807806440e81008140d0312606083e10300340050030560010102d0760 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 844970278 1250 844969028 844969033
    0x50d0b040c0207080f030a2109050a03031e05010530030c0709240e090312011206110c0307020d08190e0108010504060608040b0c040810050402100e031c180602010e 72
    0x314110305050340c0e8071030806041f0110741c2c40b2444407441e013850414038150a69902c00401c8010b040c2d40c51710b044c8095003000f1808a540c90061594018a013050b0722a1010101c400304500d50420340000ca00f51444600d841c0500000806007000030b4001c6147c01c40c004140c0d0032a074440501302c6481d0340b03520407401345c24002458044030200000d01c511040fa02107083c03610b4004d101e41000d8022040c0c10f00101003509500c020091504845c0c014400780b402001c203286410700503007030351501348192056040c904d01401d80c00e1000d100e4501d00407003103c210a078111946103d00e841850301c102e0138000c0314800180000403102070021933800512219a0003805daa035484603a8941c0200002c44101e4090300c0006500000003500060406024030703084004180e0880c2041d554101c01c91828101070020040b60b5141c1c0244821420400a16038441c40b06040c220048010080441c0d03071450310311364030180c8039203504070004464011034409801c600000041c0300c0c100c0e12800064080d02d100d0f845100c052 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 844971528 1250 844970278 844970293
    0x10e07091a150316051306020f0c271b030c0a0f1b060b030307021c0605070945060f121703150904030c060e01110406050d0b040c020708 60
    0x510708080b40304250064030450a045885014040c0030000410698070140001000038a41d20102603500358024a011f60081440e046291581e40c03c196860580e9030082c10303200d004a015003485080c00c1801d000e0380d0280159a43c403a40740f80b5040e0190318450507041d8000040c4250101c00b000201481144d940720b0b003048860030501240c502c4440510318440c4c074a5217100c00c0004100e40c20001003004001c0880381030902c1c0340c0014000203406001d030701d02c1c0c1c441c0c055402e08101c15801115070140301410324040d10783c03a1510300d40c804c1c01741056515000300914400c03201c3c10390080d03150208030450740ea00055550b00502c200000c0059001d0740c003c500e000100018640000f114201441d80c0c004117490041345101c0da103200c5900081c0101a00c10b8540041030000c0c0c40e05004c4500ca203010b655425908426424084100e68000c03c030040c3c16414600160184a030340c1c0d080b5021604070f1715045036580704d0200004010185200c6483e40507042900707110000e41d0000f0340009440e8000e0035603850303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 844972778 1250 844971528 844971581
    0x90b1206091305061501030b13230103030e0103090f0609110321120402131b03050c0702010804110a0504020403121707090521010c090810090201020303040f0203010e0709 75
    0x42141c2c010000f02240d1201c000203000109443c001285d2070740c18100401d680743d480b030018021440c1c0000402c2c00c2c640c2c440b61020b00401080c0c104120f42d003a0001c00c00e8550544e20300170240a1218001b50505884140c0c050400004117048507115400040c10002800e0038a40a029150380050603031085c03207803440e40692118412514141080c2a900c1a0315129072040142c000040041c0103981c8860180300710078041100d405994490142c4d2400c420007408440303005001c03103070003900f0840c1c1d4402c18020040140d8109601d260003642118000a252017003000080c2400225040650018000f00d0300000b04040300410291702603094580c401c2c0030071418240c403200441156551b00040b00100c0411441c102041d014580d80c0403140c0020310b441c003214410703080d40d210610180c00192101c0007001040e00610849201c0040100284100361454000070340c5da00002d000a8104001941124115502503010500020003001907030891641c9426600c02803003d038014a03514812002c40440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 844974028 1250 844972778 844972801
    0xe0406050109050d110d05060403022e051b1308101107110d0206120702060105040501080d14160c0e13020d0813050a0f0602010e030a050a050a090b120609 68
    0x40d5041a50340c6101d65140038104004c0029a100c1a50100c4070942e0050716902e681c05401c0000b03025800424841c1420f24000345441551810004010910003800d1211898290358841da000303e0000883d070b64443d00c03180e01e085012109620b468990004000314449828030b907034401ca4200100350750449010411000665020340d2044608070400c1002900141c0c51582d2952106000b5000701041d51482e40030900661041542150740c1c40010f0402148070b504002c2d160142c0411340307091119516101445544004004c1e0000a0020081c80c05070705500702d07010b84540c018608002d20417208503007444402410540942d10300d048078000080c1b075480f10140d03400d0b01716a02400211361900d2070b48030007040350429802a540d8441d4100006559903c200c0d00e080134000030b44178a0b08140c94400040d0840f403644643c540c5641061203400c01d060303002029116840c66a040c202e58551840c0303001c50300b400700ca03002146403050100d80a048038131a418080e01c075084c2030f0b94207079150326446503500e0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 844975278 1250 844974028 844974041
    0x90b0a020d09051509010f0c0605010b04150f1d0303090a0906080601062d030f2a030e070522050106020a02120609100216020904050604030305010e0f0a0c090b0d0605010e04 76
    0xd00d03407141000300380c21715481400300028404141c98507200000883d95044140c404c2a071088186103400b0400340810b070f40c070b985003040150003170030f00409400300c50001520741c0d000220b1050443d05503000c1421143c5080c42203a00e07401008090680b155180d044000090440d03000c0d1405030320030400045031503801100111500490b03818030314007060582c81c054988840818200c000c040c1c0355000703800103502e5805907a08c41c4800202c82403410030314000345200602d031100304204040c24446205000d09011800406403942940e200c13291000800709800d24980098484441d641350200000d25507502040310b51002d0b100f11880000d00c0c01c402000c0340e030391805881800040d00075002e1f10000040c1c6500a002d05140b15070391018062054000411800d0f003220140da07240c00036020402050340c54890b80b0b024040319100070840d0304190021241801004100850140e030360030032000042d000da041d02000700420540c0c5a07607981c0c0020148081c140f00d1188502041412400c07100c14036083c0500e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 844976528 1250 844975278 844975309
    0x90607080d20041d0703061806080d03090c05040c02010b120f07060504180906060f0311120a0309060804020f150c0f07050d15020f070804030c0e070e040c090b0a020d0905 75
    0x10604e682c4403403203c0c0042c0c60044c100106141d5151400030b80c038900400c00031400035610344000364461034010074604203801400403504042c17808480100040500b03105009840c4180c0300080e041c1c00b0518180e00401201d0380349607001c00c190052440d840c10004020350300000b850203844800ba610b40707013a10307039000303074014071400e016249540c22464805602c0b011a5070300035580030440e036507111003045800d01a60016030b81708000401400003810100080c200c088a403030000c02e0f05260580700205280c109010f52010401010045000c0d96503450404130001001010000625103070001400f41da802011442040d004002840484240200d40c0e0030888101814844035045950754603000d217aa80c02500411035800d0107030300116901800902025440350030200da5940c21170610f00c40c2c03d0443e5002ca180207a818040140d01644882110041e010039070f00070030524a03241095940c0411500208995100482d0899045600050141044003542ca030b840c00d032511441070000300e001350b00c0079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 844977778 1250 844976528 844976549
    0x212090a030f05060702010b01080c12130b0c0c0c1221130e0a0c020706021f090c06091e050a14120109060209010e0d050c06070c0806070e040b03190602090607080d2004 74
    0x11010602462443c1d070000d420700b21134a40095a5035040413200043d20608071440d00420b194443000e80c10090028800d604450449a540501c045240e03510070041000720040700083c124400000804159200b220010030001ca00355103800e01007080500440d54048d485003040d10040c0b0765400400d1420640f6007e074007410300700040c198200205c0c819500f25101c0140d9036401940881c403110311210244c04242e440509403442d0003000140c0210400c40c42000f407a405204200326900c2d101e2020844020072000a0018011000034240741d14940c2181146d50030941920208130a55009242810b03090300d90f400381441420510074541c42070741c00102541d009141e0544d1914042000d0484580b00b902e0007400302d516001c03880d0401c8010f44e512804210051001c0c0c220345880c0c001c07030024030b00a80042281d814951041041d01c56906000381c2015400110303401c3c0c6413188000c44d010030b07411022580c0c1d00c1202008080040c98203000751050040c0705d00071030341085604000c4600b00c41c0752850 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 844979028 1250 844977778 844977787
    0x5150405190e0a020618100f0509010e010306080307061d19020411130f03120302030f07140f0f0301080601060c02090a0222080a050f0606010212090a030f05060702010b01080c 77
    0x40500042c4540346400c0c0c620711800f040040140d41e0300f4002c0801056566540c1d0803c5d17483d4003402502c0610003940e000703100e60f02d82000c815071f074420306545121009107810a1102030319001a8020b2889411031031160200241c2b1100303005450700590001c03c071125404000407001d504244d202c3c0c09070320110b22108040c901c140050324281d00b29016004044503803900d490501c0ca1501ca08900c694401003495010600c00c10a10148001e0031900c026203003001d61540c54945c011011070b0030028904d0060010449031081c0301d040b40020b032a503481114100540d95813041c0242030440d002442549543d100380800411181d101d203070822141580038104c1d4045450300004003001e50040b80b00c9070116450f0b0f40190002d0341d2950600c0c001270442001a00682c0e00d41d0900900304007499692201a13405601400000c0c0d81c00204020490110440e0540319220761002804075201544040c001d0310442c613086050002c04555180150420f4008100d100581d01c01034a5130769040364814070f014810300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 844980278 1250 844979028 844979071
    0xa020d0e03030d050406150e07030f02040e28110c1905070e09100c110607110d11011805010204050901090b150c0f0d08061809030723010f05150405 65
    0x10800303134005d440f5040200b00c50f070483c00f82d113014109552102d1074805450013444541c81e0184664000035805100551806040c140b01c20304d103880c0908944c0a4000120100d50400c4140c1546084601c2041c03092046e8250780d01155040d4020b8503075000c65003d0820110388010301e00c510900940e13401009840050b01d0811030700300c0140020300035505070040d2040b400840c41c0912030300c0b40108458071002558410700408524160009000400b840240d141c115012000081e007404000c0303141c90110f020714008001d00e40503014100300200c281900401070000c214040d0083e10640301b0948900d555a039807030288109440c1405415a00600070140d064640d1012000074401d07881c0c403008031105a01c202900c80d10f8504040c1c10100020f880500380000c5140001c541e007800e203841a440c0c4400d042c0000c400361684150703100188810042d0621560643c900c203013503050491980000c001d4040d003240000c02400c1c045600042d4180c8000c0320b50000d20301032060701d000e000790241d40c0400790b0030385 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 844981528 1250 844980278 844980281
    0xf1d0108060c0c071d0f06100207152a0b0702060106121a100e120a1e02180103080406022a04090206370c1e08041a0a020d0e03030d 58
    0x8003c041100d0003a2038012a03480d0710760340c01074900d20a00010220394503154040c45010b41c40a4140d0f446454802180803d46500007646000e5448504444c80c2d0144900b206031000480d41144451400030040000c2c0e1007003084070000348840c09608c10441c150345450040362503000034000d40c00496025080a2625044d075032140d84c9000c2610754406145d034005000410840010300f4100c001001804101020300f003101c80460541c000400a00c4c1c1c0000d00c0c1d0b91020841c00051a09419900d03440340001036580d03107518196541d0f4044156009540c407030400c5806544140102005881211500e0b2285140342c01d825014020160b982d6443c90300d89002c10016180904c420b80e400041407004e110002071550840c0e08000042d4040c1417594010001c4200e05918421160280800707060f183c000f150b41d100e00c040744012507540c0040000c0c540e107080c2d0804e0160f504030070440000c040c180321640c03400c5402000445003e80890380498020761084400030049604182c040e00144250040c15105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 844982778 1250 844981528 844981537
    0x30c190c180f05010803030a06051f080c0403020904050d031505010f0309060e061303260c0d0207060c09090e1c0e01090b0c0a0c060503010e01050904030512010f1d0108060c 76
    0x490200b28118041d075000265002038011140725000002840f11059203842003200074141568003160284000c02852040300202c170200c0c080c0f241c96000508a980c82008840203194020000402402d10741009079582441c0508070010a2800240c0701d0003e10a600501c22284c0503034840d152122011400c40107085114000c440250301c44c03204542c0c2c2c50342840810301c80e00e034482c99079190211504009148203011440c0d0030414420803440300184080c0f040d541c1c2d01c02800b030826aa2140b0a00d10503000b48a41440901110300e0b00c036104800540c010419070444481c3c01d000d01401480588681d2603881444040c0071258208242c50300040c06040d90180c15a4141025034019680740c501c000d1640c01f11004212a030819a080800c02010a0300d030406031a5900d049410356040c48440c004088040c05403c0c0f2076190900000d0800d0b00c108200d84820010080240540d6540c0050044046c02401200320481308007409044c41d2080154080c102ea0703400c0014403407601c60280841c4181e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 844984028 1250 844982778 844982819
    0x1403011404020c190506092802012706090509070e0d02091e0103050102041d130b0408040b0d050406050106050909040204091112030405041503050312190608030c190c 73
    0x1615481d034450071340f900714032550180902c01401e114a44140420304010340301c0600c03040844804da101d10304461240800d2070559082c01c3c14042c8080c1d46404051940000c450303011030348000c3c6400300d03a00307910584100c212007043d80c602455840e90081601e00d6800002e4454012101b00c2581c0d0151070194000c0790003541d211480301403100124110301418500740c1003134415a40001e000c02c48244610f103202034051011180900301d00700140900ca50301c91103000540030083d030001150034417600508407002410340c0f11004c2d6a422103c2d91000207080c04032400e40715107240c00000511300e40550704540750407800900c2c0c6a810760359a804c1000402000005480d07240944002d00002c0e158081c100c800080c540004540391858007007040186d4448144503110300f40d42e2042040000c000000f42c030110800320300e0b81d00d66980d41e0340c034050880c3c8040045000103400c04074000361010001c0000d01a0901c101e040d204074020300700080200d040780c040d0050400310b440008200c0380704140a03c0c100200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 844985278 1250 844984028 844984033
    0xf0603060e151201060b18010813080307140304110f03061302061305040507050c1b01050a030c03200403020a0b0313030c0f0b010e1909030504140a1203020102030402011403011404020c 81
    0xf0501180c210b5080d07400c0359060010001da01c2144030380000482c1c17100d0b0000d10740a945458106020a40c461040344010940040407002c20510360090801104050051100c50b440b0300d01410180751405080300d10354080c00390002400c1040c00d005c10301600c202da407202e140694072032641c00c1c04400c1c0d0107010052011003401da000304640e500c500556002d107075651340e074546403444907042c41c1c00c00407146451701c00c0542420a07120f059030080140d8821415905001601c2803641400f0741c0a000754030180090340450f280710680300c407001030203882500e000340c0d0313441301c52a01d070b0448880303030b00c42a51009281090124000c0001e880703100340300062032081c407072110644c0741c80e9607a42d0040750031780201c10075200709030402c851011440031154503118656014090300c1d00585010300540702c0c40c041d5001c0030ba610381c00741e8216203400e842c001c001c10b01c1c51030f0480180c515040081c003d4209a4080f400a0a1a14035251701c3ca510f50a80e41a40c001000042038184803038100002076103c110004010b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 844986528 1250 844985278 844985299
    0x20060105210f03030f09161805070c14011506090803122e060e0102060f0a0b010c050a080409110a30020307020706020f0a05150603070b0a0203040f0603060e15 70
    0x5a400d0002d1401411004041602800c00c5511b4a007000464103004061000050b0b040140149050784021140725400300000c1c0354581e40c2041f00e0746540c9403000740011000122800040105621800c14802d01c0058000c0e038076100c0c0f0003202d8225640c03050007050380c024049a81440715039101b05422008030490f61452840c0740303409120250300c0c1c07c1c0389206401034400401640b6008418110804000d00c0500014540003101000301880904038503580c42c0d581102c062240d014001100096410004640020f00c05260500f40c40e400303406160700c09414400b02c1200d1100175001c0c0c0d5003022031515100400c04401038400d0840402010500450741c900b01c0407650314015200540c024119640a4581c0700e08050000e0318100d005542604243c0c0111403820100310040b0b8600c21080d805080d080d20740c4c8540000038648405a000700030007040010780507c0d075035000002041228005985800f40d0b40d5103440c03d038202c40e400c8c032802e40d540d03152500190000c02045072940040740300401c0300b202e6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 844987778 1250 844986528 844986553
    0x903090d0302030a09050a0b03040b040222050411010f05030a02030a020f16020102010b1906081b033c150d0c140415060c0f0804030506072006010521 66
    0x5256011030150007580001031404411540000380078090501aa0680110742c50407011b1051032000a1005c0e103000c900d40e02050440d629204004000c10248071494014111003003000700810b41074400b15040c010142c072200359940220f900104029042e10b0705415696440d51100c045c0d1f000500072031040e0b40c00c008d03ca1203044c005000c4e005c03480c0d1807680c0d440c10349000d10019086614103525107106070b81c2d46c600c4070000304401d40d403203040c0d94041c580850b40e0740320030700c91a209610a407a0810112404801c201c540c00e00c20703000100310300f0f440c03a0203000c009110040000c5401d020003014559404440000d45c603940c0e00e015070039400d40c0942401810581038a6004c00480c654000c0c0c020008441700d20f85441c0b826000701d070180440c603103410304500d01e006c001601c0c4608032100181f111803200c07040d80c248011201682c2c02140c001d02a91000d241950005000400d603412103a428802c20b120003848600c0040e2180c1030703480281c035660350400d00c0c40d5469060141d00820704c0c5148910748180d2103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 844989028 1250 844987778 844987789
    0xf2301080d0c050f0a08040e060306010524040504090f020306011a070303090f0c030303050a0e03090a0501030c0903061103041403070c0b09030709181a071403040609060c083705090309 81
    0xc0c5c441c042c50741d0302d03152428641074100070500600410310a60003d0700600441c2d8800111824940c041380e40302c00400146d0f00080803e000d254003030f5a12034509111032050015000310158800d1084080c2c4985a80700c3d00200140a41c500000c4a0b041c410f020600009000381c0c80400000c0c0951007030890740645544030030348090190011070000351100207025503e900c5002d14116015010301850410354007501242030303a000352040e6410076450703403070040140e40503213194030141d50409030501ca401d0540b400b00c001e661041e0b400b03c0e901c42049a100b0542c001c0401074031040e50307101d80568071461500e00d01c03c0a9421040134550305004100d000100035040c1d1041d40f80718107890340d10b072202c10600c0c03d00780d1849542ea541d4070281c1e00d4400070003445640c0640c0c1ca5201d0600e2160058403a1070b6030500c0c0d0f00401105000800325442d0126103000c0300d400c512124030803003c0325259100030840c4076006203d0304024071504c0e41c0214010214075809500c1c0c001d03552082200080f0390070460030800258 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 844990278 1250 844989028 844989043
    0xd090b040b09041b0f1b030c110420030712111c1d06090d08011d0712020a02030d0b030708190602090307180f0506010c060e100f2301080d0c050f 64
    0x315002205050100b40c201e000720b1803140351805d0019010600b03890107040b0304e01c0d0010091278802007032031140e0756503190780c0104c1c00c1400d1049c00404030031520440c800641d0040e1800c1e4046280d098000c001103006015a198072566000181d080500100d80e20080000c5100620a01c07a100d42c0d47c0c0100600c8004407020440500005080c01d08212000608040d41c0d00724000411174440010702800034045e0450017407100380200e00300d0036561050110ba070700c1c001c44284c0310004c2c0000f03104081aa400005404511744109041103810144010140e03170700c0303a5128901040d0840304032040e5002300d81584040d1240102c0c0058584000040020b06251080c0c206400b807440c035042400c0309046501c06c0081d005240c080030416401c11800103070071200007202c000d050035204c20f84404034003801d20510b9a14a2141403c0c13280000c05170300d01020380020003401084044800618031000b03c402d800c1e504941d6480c002e800c086007182d904640809940c5e0381692203201c1c0c4500100c21032010480813 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 844991528 1250 844990278 844990331
    0x30e1503160e06030c04060804030903050d03020d0c030e0601140112060603020316080601080f0618010b0301090c0c11010e031e03120601081e0a0b0d0c05030d090b040b0904 76
    0x1d040080110700282c054403403802464000d1000f4405c00c00d80c404000111004e1710094140040540c0e9245421500098160070081c802d01850008001094054010703082c6904483c8040c0312900c1412012000c03180320925440d1298000e40040100701103900b80c0b0101414185442c1110151040180d01642c2c030542c42080029800801c00c039100b0b906034108c1001031800d00e800c11f524204240000c20708100035056044040386000400d000355101c01c1510801044e4014000035507940308039100c802e8200b441a00005801c024080030030a10448a141c0301c2544103c031610f20758000b000440311008248000e6130140b10303200d00c4444409403a440140c2380c8040c07000440d0b640117006902d15a0034000742215041c410120b050046101c02048581807200d1ba24029014a42d6212144006007240c502115004541c080990301403040ca24014805d8403000d90489018040640d0122000c158522400182100600040c000050400700034040070340c00034000314040d80c1d00c03451144058840d8010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 844992778 1250 844991528 844991551
    0xd060b040b0c0d1412070c02101709011104120c08030324040e060a0f1803080414210705070e0f1b09060f07061103011805150d030e1503 60
    0x807007103003850401c012100d0b50f505107044154043c03181c605004501408240d000c1c419074180c00118498850740098002540091102440d109030b814090b2480b00c50031504814400400d001401c00780050049035001c42403c560903282510707003c00b03140c00d81c0301c01408032443c50003100005001042000036500402d400e4440c6202c5411b54164504c01d04d1315603590300c1c0a01d0a000d00d81c05066808254158405180000804c52410440c242401410040000c0013403590b5000b07a0001d02d903000c00c0451003140f0070b11300000d4412075280e06640da0720140200d8021480308100300395000c001c410142c00400d00c15821942c0540e1280101060318100711000f90440c518181000b096034142090503070340c0817182c0481c9281000440224080e84100304512400040c0018064100502a802410f40200e69001a0b4076540c41d80f0000e605001d00c1040044070340e040a001c19030703290011030748002c820001400d18880720810355007601e003a4080c8421540c401151084d1110040c4000001c500c5090002e4a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 844994028 1250 844992778 844992787
    0xc1e04020307081f0b0d05040c170f060f1003020120030a0e2103090d150e01020c15091c022b02010c0207180905070b0d050103020406080c0102060403050d060b040b 72
    0x101101041402d6480408144100c004000c048071140840e1319010301100b02003a941e5550500c0c000460064ac0300300c41000038403082c03805030340c0081001d0844002d818151100c0703442d5140040f242100c291a1106991030b0103d041006601803546a40c2c440141041070320f00b8090401d200e42150001100310020401d4801090490700d440c0030564181e203a80102c4030166501c0d045002e41e2405280035090050448031169800d00c819942c160400d00840c1e00d007486148010b0150502079040051200810310460401c0115421080640c500c185a0140100345407401c0187c01c4d1103906034400c21500794000c8903039180d0f07140d0f56420742100620301101a40200f49040380c00908413601c0203c00c00854201607018030282c100241080325801c0d1040b0040f0701e2a82c1410443d04110382ea52110ba0303025000a074402851905402450480b80200c40c2002640e40d00c4075255240c22110007003c0c01600b141c4000b400003800360011b08501d030701c11f4000040c0035072102c8040310141e000390000c01d188440443c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 844995278 1250 844994028 844994041
    0x40e120301032102160603050603101802040b0904080f09010302041e1701200c1f0b0f0d081b1e010615020a050307060b03010906090b04030801060f020c1e0402030708 73
    0x10401d00e1002c60744d100620120580600c40521520036000d24003c141d01c81003c00c00f80c0c2d0b010040d05080c2c0d000c0134401c02800d140540040950004100f0490207141410030f540349901e00111144e103d26080b0900a00d07000001491040302d50041d410325040c154244400b1401400300d03003075030030004082261200141e0406094514006914512a00aa0404000c0520f6043d502180c414666038100859240d071030442d01d4a042c40350f103241d0780c20038000c2d03203000c4006402c0a030000035030002c0540c2c50f01d0201d81d0403001c0c03141c55614640d0203004600100300c4c16103840c06a001038184000c040056606548210b501114140e1421450035181da4480c1d50030320500e10001c4c62182020384900007090244119a142501e900924401401c820759811300301c001c80c0c9013900840c40d40e581c402000c009401e60381c90f0032031598070309980a4001480203800840c80074080c401d03801c0784251070b070000c0450590510400032802c00c040c507103882000c200d00d040901c6031564006140544400e4990b00360038078115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 844996528 1250 844995278 844995323
    0x19051c0b01110d0c0201201c0f0e010806010c0f02040e0a020906030601030209070f121b0806100917030c2d0a0b010905090c03100b0109090b030705040e12030103 71
    0x1101c103010b181e0050340f44003111a4001450440c06642820300c201354501640d200141c4003c3c1c6c291454881c054224124561081d4204100041103140c540315903204118000f01d40c1d15280042060208a035200428a41c0d0b0140005a0400c1d208400014905a00b5030109003030750208054074420368001c00b2800c0c110f1a154401d25408013094005001940c91a000511040c1c0080c001e5024007004142c0451b41a100c0c00380d8021240c070341c0c0c9052140d000c65020440690401462030000155003601284562618490505101a540d81c0f40306501d414448215400d00720700181c41a24402003100a904007c1484541301d02c841000f1500f04603010300310889805070043c51054855002080c4540004016003003080c1907942011000545d036480c10401441e29469400c070340c0d07041c400c1e03200c0051081040d4211300014a400e907900c0055036950700d000d00c01c0e65650401203034142c0044d001402181820350204111a240c40102d45009850b02c0001d407141d8001e80040d192890484051b070350040c0c20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 844997778 1250 844996528 844996547
    0x30806181317070606080303100e0f041106090d0b09010c050c06040b070309080d05070207050d03051608120f2d1602070b0c0c030708030f19051c0b01 66
    0x44501511a62400e4031000101d45210200188240c02200390700c85003180c428261a0309540c4203000b0000343d42c50300d0a040c0c1d6904200d402d1045460300803030110716480340c113039154060022543d40d003540751100d43e1044103500760042910f41040c003c0c0548002a91940300f624503050040c03e4044650521800e034509503044007079541d00740301e02040754017504100080d000364400e80007580c6c0c1c5840d88603000304802074410524081c220000104829000c1d488591205004900d19003c4503c0590f5903c1406601000c01c00701130089141030003600800e0540c041c0b03400406100d06055032910700c1409808000400580d1288151101c07181003241d401220850b0560341c041d40580040030043c145013007203d40d5002000301105030407a20710526014000c100104c00f400c500c0c00c006481c1c02c1d03000c0e2800e9480303400d16038281c428801c40d80002000300000c01180d01415101728081d1038440c1c0a40c800803583d00d000d001c0c008008040000c00850004100c2c1c4130381c0c144403174002203041c1c4e001a0004010112 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 844999028 1250 844997778 844997809
    0x610031e090213200f0d020703030c1106010602191502040b040929040e070312021b09010f0323071d180309040902030c0405090c03120f0a0e03010f09030806 69
    0x607007003910b02e07009420402d1200409455a1301942c510101030903032a5409603085020744035002003040070030960190055000e1805550b00d010301010520742241d0b85107020b00c1080f01580000341945004202008109101401707100c82400c803220342c0d0074170701c1213034001c3d401b0080342a00030509218882c07c5000e5111960140240340381c6190a600c1d105104003c00300c0824400c2c0e40d501201660a1702c244048c4002f140c04c41d1040558503100c00d0f019403200c40500e00fa40c0c0d0410201940341242c98131f00050f0381600c0d40b4034103002e0030702d04541d203004031a01001400700c01c1ea00002a1a520907800b04a84809041820646201a03014010300d000103000901280c4050304a080c50f46808140001961480c0d1030484d4041f580c403066001103800c0c1600e5050158202d0301745010440c210f8000102419403010981c2110900c00c3c001503008071602034840e5111030b521040007560f0101c0d100e254242c6040307000400005094116450b0901200c2d91118101d004c01d0000301044058a030681c003c81144a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 845000278 1250 844999028 844999031
    0x1302040506180112140a0b09010311010c0302120f130b031311040207020d0f1205120105150904050405071a12041e0818030c040b03060610031e090213 66
    0x6041000041c0c40d402078600d11503454001c035441e01c089038443c0d08000c0c282ca991800800a280982142c01410502250701031036060500d42c2c5101c95080c000c40c8207040320b4024007221107092071030004580c4045409000e4003144510080c5000c0110a48010a00b07101c141c0c3d40315556900c48240750420f151254000c03d000b0000384104201d8203046610014240d41c004000c1000f805200c00280083c028910301940004c030350b0300d900c8100410140043d0115005503581c0c500c2024088c3c00712110300c904004445d610054070300420450400019024461501005150070a1203000104080340d1013141c00355010341c0810b030200400d00c49551403800503d403214501e46001e81074603004583d03020140005044290b82d02280c1084d201c0903641403a0240d020b001070f692503010b0101c0000310709031010307050300c03c1c007511404018528113445041207091001d4040d0415694000404c40400719121003030042c55281c0f240c580b1040c41d490002a081c400d180000165540d081c0140446002204604100e45 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 845001528 1250 845000278 845000287
    0x1b0106050d02060d0c140a0324030213050406021905070b06012c0a050d030f1710030f050f0d031d241305120306040e0a0c0b07080403021e1302 63
    0x16140d1030122249500302c00d00204010131740610440d440ea5100310303045503100340802c4d00000c50364582c00500702001340d0010105641c1e0202010868050307948402944414410312310490400c05405c003a07070141c0601001420500081400c20340031000078050320004400250000802030205c0c82150400d40030300c0d0510100703405841c140c042c84441c00c1c98039040b046140a4009550f0741048080c040c08020309020071004192a01030040b200404468010501221030565401107d0342900c1c480c46a03010342181031131071030700c8051141e0000001a00c4900540d00082c040100410644030700300581e5034000f0700400c0c1c40d130b942c0c0b078902c9890001e2030044d00a2204501800901d42500352045085103a0700b1243d100c50050040510070210001c0c61400741d440454500c2541a01451183c0003d44052050101402d8582e48401c9420002050a40c83c11341c10b205141c0340c50045c0400034802c49103a0301c0c10361a0340000d0b6901d2141c0072142080005040c00d41160704017203110203185901c0c0c81040d03003003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 845002778 1250 845001528 845001533
    0x70306050310290409020d0c03140105040503190e04060e07020c0603060306061203070501090605070801080d0c0605060109120b041202060f01060f120c0801050f15070204051b1b0106050d 82
    0x2007000d04003108110440d8480d0b10f1410350f01d5130b11401c80c00303074002e140300101c0b5820324105406041c1448141e0710301c20700f10082c004190060142a22940c0d00402951400740704110041058440748001420007206000c14411034890b071003100b0203041d00b860f90740264035009000034644240e02003504c0c001d080a006114207504c001030100e8100c14100c6004001c2c1540041306403450140d000f02030103039801c00030308109000480e4401e5000d0103050b51120703096a21213405135035401c9849010300000b40000400008103040d5405941c21590515101a440341d580d0806c3c01e1040300640b05641c2c0610101c01e1000704150701400f0f00e05002580003a04852518210f948d0309000e0500c00e030003e03c0350011030f5829251194a0f4000002c0402404000ba60442c0c2c0300141551424001c290141c410076035101800e28000e0710101302d04503003180780703440c00c10560b0a11010b40780103810038030780e080e004130a07403a000c403004c014001e84846607410044042d600c1203c0d0b0f080d18002d90000740076201e0005000003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 845004028 1250 845002778 845002811
    0x8010911240f0f0c060c0a020c0904030206040b060613181802060703030c03110d0c1205090c120304030b161b020f1e0a0f030308250f17070306050310 66
    0x1880b400807021900c032074034600c1004581c440c0c00c08480c514050710040004680100d0040c08038100c040d400c84180e004000280403003980c06a0300540564005400180000d003491459a44580040e02e10790030708001c2e41c00c05807207e060307070040d00410759a1802416410198424240021507252808454903459000b01e25280b080d12006000c142d01c5511083d903550094200445603119000d01654844000c2500e00c000c0c0081e103107442c009001c400c0741e40040d00300f1b401541e01906d801005801e0044080c42000360f0580725090012460200340700000105000c8035109101c0e40e002c4626910076000d088008064001c9181c5990000b00b07001404070150302c901d8071b4203140071810784900248080648200724698034050709160700000240010405104c1c0307046180880707100751290300709a181c601c0191001c00c20030100490300b1601c40d064a00c0c2c3c82c450345529641e8000b5060410040c07558103008041c851080710504040f0341c659074108040e00b410824224002000c100411044405850300134 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 845005278 1250 845004028 845004037
    0x81609050a02070222020f0d0506012706111e030301081c020a02220504061b030b0906010c17180a170705130612060507110d0905060d060801091124 65
    0x805280220300c4052070b00c01c00c1d4120b47e00c41c6111025242c80d0b0690401580180408542c564000394018041190500c107201c00e00d440c800000d0392090f40581410401c96410441250b005810b02c1104c140007070101e00201003800d0429020041d6941c0d41c10400345510301400761011290100c4807000c101ea80030360100300740641544c110f4154a181000c000c2449090070b8142448202c10301e0300e024441003150340e5014802c0910445170b0100c01e202138407130940c12141d482840c16005005000040e980750300c1056030380c1c0e00c41c0c03240034002503c541d0010034030000c1d0043c00210139038882c0038588008a25210420b80010945044018500c50041000907207032030701ea03ca024042d000e210216610041340d0341146010f000540c410f500c003020075007450350103442c041c1c030b800d4040350800c0c50f419103100001c50900380342025911400c00161404081c081d550b409400c2c410500756842c100070484030428050100081d02480c1100840b01904042201c412480014884514880144030a00300c85080c26103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 845006528 1250 845005278 845005309
    0x50c0a0605070615170109060c0302181201140406060608241306080109080d060b0c0d08130210020c280501030902030f010213090c0f05030a0b0307081609050a020702 73
    0xf09400f81c1282000f014151641c01196205401c810180000c05055202c7c996242c01407906100d80ca14000e000d800300d01c02c004014203202c4e0301e0403006904d820940000e070b01d0130015100005940b00c403070012080c0e40b84141c9044074119203035042004442c0e8081e5110381c0228000703407510130780b91405038a505019464160b940c005e440e403000545555040d640002e00034004400280311154561618505583c04182480540c1d85080b801180751034116050300c545070090801001c2c101000b00c81902c44450040607051100100c5081ca401622a500300030f8003813020380c00a2400040200800c5202c10f14110103150b0200c074004252844021610300304100c6e4020f0078001400002400441d0409074880180b030340540c00001c0c4908100c00400e8030400302e0b1400380c0d0406c052548400105e500407500316010000890a0011a00d295207661199a91303170001400c540545a03a01d11741e905090f61103080003000080d102081011440d28011240d100250050031450312185a000545103038941c2d00c030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 845007778 1250 845006528 845006531
    0x7050601050103053c150103060b07020604051c0512070b0703050405061801060f0b0901090b132304110d0f050f0a050405191212090f08160b040f050c0a06050706 71
    0xf049080411140c0d82d05e041500d10030410307652030188000b0700140c0014034030034000b0b885c01c0d0f000506482d4900aa60340154011b01903854140f5000c1000240e640c140b160040c6011003048103000a02c0401201c50f001403210049620394107103082005440c0402400041498144401c100c0024004034000c0d90101042d642d80c041d08070b80004060040ca9640c00c030807001a21844003007009080d000c040c00e402c1c0d00985e10866201d031100740581440c010300d0301e140d4040120000520480b40301c1d41b03da2010362000210500c000c1a5800010191074828060780003101380050303c000c101000e4000c1540c006800002400b090400302402514070000070202201c90340e0342d102007020000f0911200e20b032420700350021a250f01460400c0054040000c41003000324030054101d00035008640540b000c0c4035000418409a44000d0301c6618403a80243c080c063b044900f02810380000d0031803a09035004d6402000d40000440d000e25100385444244261140305840042007000042da12004695a060340900b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 845009028 1250 845007778 845007841
    0xf0b0f090a0b090a0606170c03030703080703271b080c0109030b10170304080706090612090203070803120907050402091f0c0c0603050a15060504050f0a0e09030705060105010305 78
    0x1e03e203043c8035000c4c900070881c2d410007000007070342c1c081da00d00a8190510308007502c0724508020300301a44d0f8455400e00801107030060340020364042c001d40c401210000702081600301d851032010843c03c04003e2003c21034030075041c002010501d902d4410500041c0c003243c0d004000400080380080c00300403641c40014445001100021a00c005002c4c3e940014092041004800c0c42c0001d440d640f2074009006000c050710600070b0029003544101c290100700c0e40d0944607d007950015151500207004003280070780c0c05105403140042c900e80c003080202400d61101080083d107041001309142003843c2e0794096413041e40140610440340c0d880c420240d001c0f03443e00d805d1900156614005503010307504414041c010761404070001400c00e4141d005507103c4d01416404004030954810f80c0301c440340140c0200d8000440610040c0302600f0070040d0f44a88050051041081c1a61102c0300b510131070040310f0b40d181c650804035503803042210410405016140909041c081450103600781880303441d6501c1c2c0181b45481088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 845010278 1250 845009028 845009041
    0x10b060d09141603050114061c0f0b01080c0103110901080711010b04020a050306090f070e040c050d020301030f0308070c020108040b06010e1807020f07050d0602031803070f0b0f090a0b 81
    0x2c980b506000880000d6a024500105060340c60900500c0103541a5082c40d0440081d040215800ea200e0348005040b45101030220044074010540250110707031001c0b4404c0c0708c03004204401c42403402088403000600c01e008002c400101924004070360800c3e582c80034048010b2580c1c1101300b6543c01700c1c0760326001e07409501c009565030260000701c98158020b1320005100030403540c8400114410356055407013803180c0d25206142038103400f00310f6801000803014000144d1526140e08012807070086413034901d060098034131042049a200f079000311550a040b200320317010544c0115030b00c0da00c5403050425400d81c0e2a02e0b0006071100400410040070250000005940c0e68020b094503039000401a0a002e0210050824200001030995400001d442002103031050b0b01000541e0905a138000303071070004c440d82240d440c0000303504081c06405078600801e0203498600d900b00082e14090780120000c4003d03217404e0510540f020006412480e04107803200030800e1650b8002402d885459015003240c03443e541c0c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 845011528 1250 845010278 845010293
    0x30f060408090f180103030806040b06070b0613022203020109080619090c0b0a0c0b06151801021504060501090501061103160302012324180c0702040207050d0e0102010b060d09 77
    0x1e035402d812407813124001301c2455230200c4c0e00d61040e4070550302045459548003c1110500900c02e009041c54801030001c0c5241c02d0840100080708910311300982054911038030b0f694010421110b1314622044400c04106543e0306c040b05600501c0030314054080ea003005103401100c2d003405500d00581a0f15980301004000b4019403038001003007008002515200045801840800c2d0a0b00c10b0742d44030440b1000c20a9454a100560314201080340d0710361500c00c40e6640003540008203030616040d402544540580c244c031010510f07126521034200082d488d810300c1100000c8800c1a000300040040035202d50380591000401c50b0701549003016013007241901442c0813405014034070010302555500012b980100c80c15101198003600e07002c014000c1c40f6071403051505400d003108041e04c1e8410710044a8040d568203140314540c01004200c0e0319850072440d0340100d03040c3e910248084405034000580b40f41d0155100e0907098110750300344001d024068524002844c2c80c002c0c1c103941c0031080e80e650039040c10409107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 845012778 1250 845011528 845011549
    0x9040f1407142104030207090c020307020118050306040b04150903090324020c030a0e1e060a0306080a120e2202090a08010e060906010f0509010b03062d030f060408090f 74
    0x44000680034412107902c00a00d00303c080e14101d01510940d04041014211402200c880b404154000d50802901e50011181d0a038540c00c0c2e0006020100c4002c5555201800b41c2489070703004104055407400d041c90481c0c0c500c03840748184488545054413030400a98444005c40c00c0303a07000740110f000011110031038012103170b440b04a0241c0c1480000c00d0311a240010018014006150b1513070000c11410000b80008614044280034401141d01c4446090740381000c042c1105400c1807600244607600e03071194a150041c9641c0941e800c18a101280c680d017035210190400c4003805640362001160b6240b18801c0c20010f8009a086060700402c0502a54503005009001414044000c2c840c1705005604991100c0c4142d0b4200c00b20f000f41030000c9804007145c00600212070703015007007944980c038005080c1c6407a080582a41d0f0300c06c51018006908413444c01c1c00140020703e0440d802d07000b000c0750041602c2c05d034034103c0803022a000300003003001040b1550140d440c610740503511000880052800140340c1c010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 845014028 1250 845012778 845012797
    0x12011401210b0d0b090d05040e13050a05030d0f06050105090916141c240b030402040209040911090604180b070509060315041d100915090809040f140714 67
    0x411080341000e1003c1071004d00e005910b220240e8140380e000850072121880759000380584145508081104640000e080092140c0240160340c00c0745225a2820308562010303c400c41c42a484454600442d0020f1003048020002400d0043c9011310b1103001c0b4001c4c5400602070188240c152409680340d0303009605100480d021480caa5940360801c8d4a001c0e10505104145884149810840101d269010604080c0c048070340307920b800e08a01e484013620040e44002c1c812030b0025001e00c000c400342c3d2941d0091b41c0e016072280d030104800e4078480302030242c01d49004000714031a5041640f240b03940c40c4c07c035134002a401e810106110705551078207016102c9204641c1c031150001c50000410070300b00602101183e41035412201400000346640d0303030811120640b00d4605040d044003004d410f10340401c0d03104131180d92140010040903a01c012081042711044402a210040c5c0042c000426203070520941c18994074040040110200324803440380107071300c01048107080c40a40702003250281c8564056a07180d11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 845015278 1250 845014028 845014039
    0xf081503100510140a03120e0a06020c01080f070c0f062301081903080c031906120611071a07020102070203031603200d0c020a05030304090212011401210b 68
    0x10081c0744000020001102c50f0a140d981d26030b0041070b020000c4190443c8580001c00d0504480d007180c41e2050905080030280007840031110880c00b00f074035081000d10081c52180c02514804403030000141c5200f00040641c10f0350070b00c00382000150b94210050308806900a0b0340d404a80610b4a4030f00020030312103d01a07001ea601400680071445c42c6d44942d0305940e91503046e608c070703060503040404070714405550090214070700708002044c0d100208003841d03200348024a1641414042c114003c00c03180c41c0d40001e068403405240b000203101c001e0142010b01841c00305040d1414a079a10b400b458015440e0140c8000250a008114028404d40542d1201d42e00102070740d61f5038400114010300e04490b10030803000b003440c260740041600154250014544458005000e03080c1883c40216500b40c9090f0080383e01074051440415603480400240024060100006a850f00020810f40e840d04050344802000c11020f51410301c20b076807100030f40601040c4c4e00b810003001d00665484501410296181d40d8108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 845016528 1250 845015278 845015293
    0x180e010603080403021302040e060127080609070803340b15040e01020910180b040e060f0d0c030303020319020a1e090302031b0103091403040518070f081503 69
    0x248a100800440344202c4226140d06d0480c04a601a40240e215045091840c42c0020701c4650055003082d07030078404200a0b201c480400130415038010a95080005a54000403c0045507441044414003a20f0f08600a50402e5181c510480c807810301440e1000e18501081c202441e54440c081114080c0d550100c00a88585402107804203540d18000005e03124a05140c18100856010310072610130784009003003680a010b0001d13065400c0c0400c2c00b614001c000d0b00c0c001c000752900e403400181000c1d28082c520b41e505403c02c402003010030040181c1007445842c1d8005a0400901d200b01c07d83c048035450f080158590741e039010f20320140407561550884140c0001450001d4650100c4500c05030b081a00000003460f9081e5000c8400040a000c0250103501000d03000c0390440c0322a010031220390f814500450072010641d1101041c480d16100000c3c1c513440441c040c01245805418000380c440c40c01000112441d0180340101501108803980701030040442c085070141b5004055081311800c06030494601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 845017778 1250 845016528 845016533
    0xa0204060f2615090d02011404031b051207140d110304030b06031002070602120a1b0324030321150b0307120513020103060503060103032001020c12040509160207180e010603 76
    0x5d490030a1040d60055180108461800070140651400b95405503108006908030713940b00d900340c8420f0717041601c0c1445000d00c004c030b658440034002c0045a110300070805100040e0f0508500d00200c16400c0b00038802880340116a041c400020345040303a8101290352010303160400803d0034000100b041da03d500d4000243c03481030029680080564407070b150000d04650f0340d103910880c1102c002040e161b01280b02c0c51402d005a51294000e414030314428800c21910b510300054450740d030681644210003181044a4002c5002d0803c6501c0b80c420708642021302840098000032481017019000b07100201303c0101c040b40d44203200b050403074000448141c08110038105400d4480c4240364000307040340042e0901c6004580360401050076412260300d9250030303540e05495500012241800045e01240303640c20f0003000700e000d40030000c55070100c030350f2000c3c150b9460400c8184800300e08000c1440c80f00c51240150741200e0760740040c244d0100e8003000b5650128083c2c036426280605141c40503140e0540c241304000c801e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 845019028 1250 845017778 845017783
    0x2107110c0307050319211706040506010f050c0102090405090601050a1203020601032a061e030204080705370302040b03011b080703020c06013b06040f0e06090a0204060f261509 77
    0x1880c040b40c7d020358a243d580ca030401c000d40300103c6106000415126913001850300981c0a01640029800054101842c80020600700d80080703071809210707130240004204900700240c01c080540004010205224582d4034041c0d0760340c0e010310005100104e002d610440e0b00701d011003030038086074883c03000400700d0f60380d040002d0080520500301e4560311090b00314182802c2c040e10807501101d5512000e0038001e4600030411100d04613a00e501c10740744411021240c5000013240304040c41022195a00c04100d00394014841111080c4411501a030f01d8221031031003c0e001c201420b944080d4a01c1c1038240ca603144d071000c030041d00072030381c03211003601c20080086900f041d14849044041c842c0250640900c01d005250034040c1d40e40502c0203a0f00100d440400c2c1d49051a411403226110780780c10201e15101c204000c0c41c039100045400041036040041e440045103806d006007030042c0403580b480100f4074201a19820080f41c00d1075000401c08581d8441c40c12a03d05200f60302e203004190807494841c1c50024202034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 845020278 1250 845019028 845019047
    0x71d091009180c05121b031f020310091806091704080c0306060405010f0909050c0d290603071418010e0103032a082107110c030705031921 61
    0x94450079644004642810f1003c1440c0b24170f040240100711680c07601d5940d0492001c0b540d0035903018050300701218019100e240c1102007040d0745070300059807454805290b402103040f90300b018007030a040010300c89003041a049500071554008400045400f054604a400c45484142e1011480c01c0481c0c0020800004100d81c800c5100640a40b02185e40703400400007220f03000d0043d4841a412144103100f07008603548000d0b0350a22800490b1150380060700000c031584000302003200c48007450a1002101103005552024140c801007001d451400c02c40002900d4455500618014800c0816aa17219540709204228100d4801414410950f15282401d000c801d013400242c02140c075541954043c11044200301d25180010351110340e0304151540c0c0c9200e0f961080b5140080da007801d0311902c072002d048896043c05205241c0354900580d0400d40140e05003042440381511a17001070340d0402464a010401030b581041601c40c0100d80315040c5060045125004842d80d103040d881c0f59142c174150380155004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 845021528 1250 845020278 845020283
    0xb07110a170304030611072d05010f0507030b0307080c13060509040804060f05190e0d050717070f0e01120c0e0a09030e0306040515101206090b071d09100918 69
    0x170300000507490000710642c070403214014110040e002d104c40c0c42d490b04400545002340f0300213440031603154545410b13003034032850000740c0c52075942c030814400c0b8103400d481007404600c3e00303802410100d843c0c140a152203200030039416010b50f52000385001020b03007991001000e000e0003420904a410a03041184690b0403034040c610105142c400c0100083c0d004405603000d0a4100303030480e041c00300310a01121031070003101000e074100c0d1140003818001003003401004084c118503040c0b8011381d01c0c0c80d58003d18020031944201c804450041c42071040a0b184104141580c140b0412a004005145010b180c0a042c0780e0018444441480034014501d0140c0c018820403800307540d030702e910804030004054031a01c094400501584c000c601c200c0c04c5040e9400d049501c09590045644c0203540e40b1034502c201004040201c44041e030b1814210f081041007210a41c011010789442001090080302051390384880c040703880e12603054138000408103e01800c841001d4002c000090101c0c003d41c400c0a290088131300e404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 845022778 1250 845021528 845021531
    0x1202130c093f1e020d020303070f0213020703120c02121309050f16181a0c160503060c07080906070b090d0f210b180f01050603010b07110a1703040306 66
    0x60200006900100c01402d0b0b400c141d00f00c1c800140e25240f84614455024100d802680c040000070140c0c1d070034806080030314080d4608010500c000d20401c021150300d448070562141c8107215150110f40c0c4071290405040425000103aa08684002a032034200500300c030b0346c0c271a1000100c9a00001205c40701070111020310006201c1d030344404500c10340781c0d941202c444e0101d0001001b148145445142c4840004080c450030800050716100c8000b110208900408030541d000950541003600c2000440815040122808410303410a000680c807114094118103000c0e101180c940c2c18801c881080b00d4425030700424259560b1200e180c28800c0010441d020010742c000c0e0150a000c51307000d0810303140b5080c215912a1054101110481401e01d01030302c04140181d40d0300e4452a4a86401d100b00112501c501d2928005140003540162245816004140200014401000443e6540b010749100d076074004100750369214500041000c45000c0c0e80983d0a514202c8900c0d444048080010015207010300e80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 845024028 1250 845022778 845022869
    0x8060d0c0605120108120712110706050a14030f0720060a1a0406060e04180503070813060201140708040302160b09010e010203040b120402030319030b09011202130c09 73
    0x2240368455800f00d01b000b00e008030811030300740014901d50032180140340c641450402036490004030ba107003100a400640c003094000444a180c140c2100b05030000100d1040312a140d86013405000301c2500d8054400d10500c40040f08502c2d02004c055282103084040008403141c1d0700e00880d0b04030151a1100207424a440b071300849004030f081600034241030351a1525500e06480303040c41440300800c4980c1c2c000d40c9208041c284e04000a000380300925a82d4010703015039842d411031004200308401a43d0200043d6850241d200504020480c6900c4e4860703030f5414564a42e0750703181000d0b41030a00d03111080030410351481d804a280b0f003461014010001d4280e943c000203001ca1401a41d491040f40500781202c5c03401d1040b10b42200000700d51a51051001d020b03a400d00c5000480c00c0c0e181c000f04055600804e807031700340310900f50810b4807a0500400c441281440700010a03000719840c10f1040d804c000713a680c0c4681000b8613060160603208000c0ca4161803960b140c0c05c4090003050a0050000304020b180c04013803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 845025278 1250 845024028 845024039
    0x913060c0e09091c270f051207031e0201090503060718090b091302040221041101050f070318180906060603050610050706060315050402010801051f08060d0c06051201 73
    0x80d11290318030400700b001c0900b000424040c5c501540041c07035a03032075030440c0c11004890340722800c41c0b04c010281c002c4a01c1e500f600b400204007e00e802c048049410b07500000040021a080710294500c44000d8000c68504900c1d42c00100d031040f000c0e070071140d0907120380401d2200c0203030712001174101e0b5030180744100501d54a440c0c5480c1522000c490315903005070004082404040451030040c0c42610050006140c0103148070038261030213201c801c00f8652020707130f01000240b2850b0038100550301c00919285250141170360070340d1240d006000014040001c0c0500303108118161303101c10300c041c007100039450b941d0b040b9050810007d403050020441e40581815400201603000b40100d034043c100007081d00011402a0900b01d40b5600254400c2d54040d856a50001c040713514a0310180400d4062040030500d45850b0001609611042c0e0142c0e000d840b10302e04c140040c0305410712040c42d480e602c0c17800504a0311490001400c200110b003002c1c01d0440760715000a82c0d207030400000c11084088031311006c010303a60360303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 845026528 1250 845025278 845025283
    0x3030a151208031306060e07020c010206070c2003060118230105061809070906170f06100c05060702010207120f0504180216030e031204080c0913060c0e0909 69
    0x140301d0112408848090403001440308005968022030a0b42104020005900c40320191010340d40001c0c031500b04242442140369040c0034585c0b02410070b0000300180c0c21303c0d10004006542142d800341410000005070004418960307600344034034400030100d4000d9616203010200c144212010704040a1600140c0090b00c110380303e000700107101e981880321450780b0b0b04040c450380fa4031400c080d01d01c810b11190018020741e00c442142c0e005200c140c1d03800300c216045c800040c02c0481041c80f43d04541c00014100302058403e4030300c140e40443c041c0c1c0c0264040c0c100d11015030b10b1001084000304103009a01c10428250740c1507024015050041c04c000d52610070104007a00d052442c07010103800076400300428003449c200b000b5540d4183c05030040c0145072404000480d4414140030f40e0440c001089400c00e8140f0745000c0028030143c8100441292500e86401e03034049e60341200000c842e01900640c40014440f4440b400782d400c845412100500104806100050844c108014581c2c030480c0034402040104500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 845027778 1250 845026528 845026571
    0x1081e0a11060c10090c0504050106030506032a0303041d10080c09070c02031617030f07060b211023070e03032a1c020601030f0c0f060203030a 63
    0x40351009100710500818014180e00c003a0012500740300d0210081d02100140c46850354582c05100304030031050810b01080140c880c103a0001e000c060034070b0240801f6030b4000c14031850360b000c0400440348296a1540c0702c1030000508450a80c0b43c000443c3c0014a220b44041e042041014242801ca10ba542c8001d040d2000040f07000305001c1e540308101944641c10b05041082c2c115806061260074044642d00003482c3c413055510b03a41e58a100c04000b00000c0ea903001c48000000760302d034013560038150050007086040c011140301500302900c92100d440d0949450196100c00401c3c07400202c86081d03802611682c03080c3c1001d00e201c103549880541200c00f80303081900e0180592101d66441692140c8001b01d034059200511365515010412141608612900c9000c4100e1141d1190310045d190003400e5900304500294142e1506131200d004000140d0f000c80d62070b0561343c3c00041c600300380e0101d017806c0e1110803441c0c00a07181102c207100c02142c030940010285105d01c2094409101d90701031035600551b14182d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 845029028 1250 845027778 845027783
    0x109030206011a040b041806080f0d12022203110303070b15040b03010c022107241806050a05150a060e03030c0d0e03070e0f1501030e0601081e0a 64
    0x40710005222410081481054031968020540d0909071100c00c0c00005520551011600803e1205568800b01c07035801010001c0c05460045d11300b0406004c841d80e100d40420100c1c4080201d01545640c031541942c0c10380362600d180e00350705c404005d8248107111323010400340026a030040a8001101c0f00746000800c0312101540044681c403030361070b00c050081440b455003507890392083d11030200310f00c9074609104001c070000d196401045e56406c503040341020056068000042e4890400120003c81c07107203101c4483d8042d040b0710a150000403001c9500c010b016040402d081d002141814400f030240a0f0041030240310300070790400c569211129545403900f4a52030041c1c0003200400c042110a00640c03031600c400c007010f42503d2402e111032300002e040070349403481c01000c82c0c802d00c107a000604040015101400180350320741402d007842603860006c160024101c156501440600030102e91207904842910700c4408111280b80d6111010140c071380c0031290744c08502125141c00e4004800f80081d640c442d00c0d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 845030278 1250 845029028 845029033
    0xc1a0a0509060f1204080d150b0306060a090305030c060411011e030507090902071a0105010503070518060c01050403020f060702150c031008070314010c03050403022d0d080604060801090302 83
    0x100307281448600d410000d8210060328091100807100050314480c80e200d00c0c8112503651745d80c0048180c0070704540c10803240c50601c848490043c0314580200c01205c0d0001c0c0c040705c42030744407814690308556041564000810030b000116070640c0e00d000000e00700b40142e11411070003211010440044a59812320380707400c48003160420503201a9400396011a411100a15280b0641c0380c41d15500016a40031090444d0b032000440012640381004003142805004240b800c00c0c550708109074000c155000303d01038090640c3d030281c0f94003032075503072042218089034002000340158034050902a4462460b21605040e074002c2400180300c80384081000314104d0400b800b03000b601d4aa4240c1e104903a0801461511807143d003c4010800c20300801c11040110b11801c1194804210306a4403406c0d54084c910100c1418200414440042c0c0c0204012190640c040f8110724103801a030650150042c04404051030f60003400100b03014190b210340301380e1061406403030a12003aa55020550302f2141744400190058 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 845031528 1250 845030278 845030287
    0xf051005011502060403140910120e01110f030c090d0b0a050609090d03021b0313080c0a050d1509060c180b0f0a08040609170d0513080405040c0c0606030c1a0a05 71
    0x2806100390250101f802852642081c1581001c503000c1c01100c0010808110038004c4081156028040c688141c0e403c14000d020642440102100d00c0c05000b01c2c004540e1000310004110100a800b919110680100112620742c3e00782802030011006440c03026801d81810300141440c10714079111030003840090f00414500300004001c40c025084041102c0d0a6600f08605400100c000c0002d0041c03032044800810b4102d1610908510f0807002c080c09034014603101c1010001a40c0d4290074100e800c1c0c00107030b140c1d000b616071001480180a11113006001034030348a010a50380c0c6d0f0240501c030225a25000e044803460300c87e41804854019622840d0a840f81000034180c407074802c01c0c4243e00070b03115070340c00300e600c2516030b99591007905021501044c0503004a101c0c104141d03180038032600700c0300701d500c05901401c0079264440540f00d14015503002d580c54901000c895031081c0052180140c0045040011544a02e807101d07244685c1d00c5008401c00909038880c000f9983c54085410000050300c41d646030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 845032778 1250 845031528 845031533
    0xd0f12020a26010b030a1a031c090905100b070609060615093002031f0b0a0914071404030506090f060606031e04171306020d020c0a1202030a0f0510050115020604 71
    0x40c040c00d9100d05061f01c003049400c04c1c507407010404404c1c401074582c40100704131010340000700314141d998031a43c6814141000d04c4039250203e03a4802c250744441e000982d1300c040504041018100c460700050030316142c46030000301200c242c40c04034803810035555200c000c240c1e1005030181c01c2c1031045042682c1c1c2541e030850810325282000d0413110b24405030646034079101085042d002d2403103030898158010703140c034040b1000d441e0000c5085c0182a000201b041440515140f250103030b20001e0111081c80300c4102031102d0103020005031001540e10404480785440c0c0312615648500701d5440303078490791180e0b5021450078605082581c0c490070020b984040c0a402400059000f000c000e003003512841c0810f603e107018807166000030702031100d240c00c0d10500c2c9407400030001d05e000240c003446001c5401c10314030810140c2da03881070035080b200c9650121041883c0f40c0002401e200e00007900810320350201d2a0001000004035039100c80140d49001081513aa0344c0c07201c0751071004c14001060041c2c00482c0002e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 845034028 1250 845032778 845032781
    0x18050603070815040615080307060e120f1201060c02030d03020d091e110103110417010b030a241407030203090c0915040e010606020d0f12020a26010b030a 68
    0x6001000034110341040703644a242c0c43c1481c600031643d9084185540400080c030003d4084c150007551000611000f00d4684103036107440780a500030040c456911500c01c0106050104280c20151408091040d1f56080c006464007c0e980209100c100e03980c000d100004009016a58801e04603401070068040c44481020403402940009815410140c3e00c425103004140b1185880c4942090884220005503103401c000c1401d070f0000d01014101421302e4a003801c1d100c0c002003510300300c803140d8035030310103035904861014098080400340a4161044e4a01c101c20711810854100403004011220004000d100b03031400c05469450254ac3c01e698229004103d02511a6004583c00f55611048e01d13030841101000660b03890055030034075800c510001d1205121b00e814031a041000f00d9450080280c14034100c40a0749a480ca10200340c1030181100907050664010304040605080c2072804540d20340181c3c00240c0340007180040200c2c00708100b812003024848800541e8142c42e846010b0302d0030b43e65100c0030b0303c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 845035278 1250 845034028 845034031
    0x1d0d1211071a04050f04110d0c110d210e03030c0319050a0c0e0109030c060c022710141509030109060504050d03180b0f100506161101091805 62
    0x10151081e82030004811000049199803515140903041d5a240b50070208941c480001400d41c1c0304a01d0908200300201400c4121072190a54010102d145c501c000f0054811000c0510246030b20b01404c040c1480103940304121701440c0022205440302150302508500440b2a4094218895441007022818440c504405103500040f4030b4442103010003000140400d07075000755800344015407102c002c07240300c1d500500f0403003800c6000e20740412482e02d15210702e42700d044d180c4281e1007400b913004001020741d00d5541c020240321304204800d02c0141d01200003100c40ca00116202d0118007807402d408181162088014403100800402ca42e0301d000c0703282124207082c0d02c07810550741d05640c0c2d40c1107240050264000c0340c2c425402480a040d007065118400360983c7d00705001415402d9009058100050000c083d684d000b0311880000022030f99000380700042045950001c2d64444d0340811400680b01e020010200e200703103d620030b442c40200942c01524100901c0c01640e5210302c1d590344051907060740e584001d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 845036528 1250 845035278 845035307
    0x20a12050315041d01051e0a09030e06070b04020f0a060e1e030d17010906050d0605130b04081902010203060303090613030b101707060c0f061b1d0d12 66
    0x1001d0101082c000102129284c034140c1d410f0303c4003441c40d065804000e1080316400781061106000941c0140c0121038208401400c07001c03d59a500c0200003030620850800750002c4015040030759942907070502c4080c801d41160b08a128981c0b8603240c01450818a012030200d480715141c00403002074401c00c2180e07000c01c18000031800b00785151003880c245e038104400c1d81c0340e0920f521550540c0140d0705182c00d031410142c0002100030b0030410100079079180d40a950143c07940013840083c2a4840b0380702d010021382c0c0da4001524240041c81400b0502103032500900c090f142116190030442004642607081c1d0208807215907150304144009081424144000c0009801c400300c1000000d03100ea444c2c140388041075036544040c004124051020040d40b00e0443c1801d00c80c0d4004008480c9072060041001510040003000340c80c00c020a281084000d13004070300c81d20b1041c04c0c000030040a8400041108030380e15a0050f800c506802000200d0820000004105800100310388034400c05c00300545074480200c40700d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 845037778 1250 845036528 845036551
    0x615090b0f06092e031a060f040302150706050c0a080a0504020108191e0507020f0a1101050c0a0b0c0a0906030e0303040314120109060f05191e0b0d02030105030706020a120503 77
    0x2184041c00382c040d2400464400b81c90000da2200309007808405041b0040440d4003420042103990300303c0050100b95411250b04492021214038800c00355851030050000040142d4188024000c4406404001e00940001a51800c840c3e64800c118102034510a84c1c003c0e010680d0700b00411100e19030100c2e2149110340d141008558041c4107d0301c9000700030350800c90b810300342c0d4903800d200e110b03a03060000751040140c0710000c0589074165102c51441018014a0300e040c8500000c4010019200784213001c052500002c8100d03061900180401c400d0740b02c92654800030300500b001044440c002d10840d1001d8005100131421692982d90a89403031038210342e0b040303843c0400d219200252000c00c04650180156000110700d15290040c041d01001031038020314800c548103d0b10031050752800c0d02d0fa03021a0240c010903840e40984040b844d9410031075800c41c4e144000c00181008823400b09030000c2d412071f0380c29000c6401303e560b1688100c2c0c032001d410790000c2c80034514000380611310f0311400c09544c101c0c5202c0721 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 845039028 1250 845037778 845037829
    0x90a0f0b0603091e0601031a100b0703020a032006010b180306130b010b181e04020d05010e1b0a0305071e03050406050610140f070615090b0f0609 64
    0x7501d2904100c611240ca6400308400711044030b42160340985821594000700701c1941965106600d0441060b10700900c4440c01c0b0004912301c014810641c02003161194a9a48001c04e040082d1a1a080e80003600421124104044000078a10505400ba0b104401030146a401d03d202e00c0310035489806058440d440c0c41c0b03c1003095540500c941401174800d000362101c8403082d0724000c0c034154016030041003008014001c41c00e01101007100075a008400304c2e8500040c20640032001c0c5080d2004500c282c22501c0410540b81c00700441d400325041c0d0700842200c907055a1421450100130043c0700608841610522801075954001c0d00683e4120009050411412414150080840085000d1000000c6e02d84c003d10040c010240306158121100740d81c0c80010048035100540ba110406241b802004800030b46101c5030040d800c1039503140c84d4000340900a10100c0e50f034002c40d4a405010f044100d038501041c103071003882c1c500c0105580c0c10014040754104000c0100704050706400403584146401540b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 845040278 1250 845039028 845039051
    0xb090a0b070f0206120703150f0b030a200703020c03030a050403150609090b22030f0c060b060310051005120f0a0207020d081b060c071707080c010f0f0b090a0f 70
    0x5000000c554403525021761038640c400070295100c16201a011003d401d0091010281c003103920340940d240008050f17502e84ad11105600140060003881148485540000e008014000c00420340342d07019600700c9072241d40b0401055160300c0744038000702c0031684c108000c20010b454241aa844c07984954800038500d0364038105802515440308089070203400513004c014902c1d01050801a0545c919469401880081d0b41c0241060700560298018040481b030020204080f41e00056900f2401400264481c1440480007000c04601d0040320307c43c5400c00c5000120074442c00c03d4039a21800810001010707251084140511741001e400303803441e03607000c010f0100540c60f800c207040036543c401c0c03001c40e660300110228402e542c08c109030320240680080043c000e2008410090b0342c002c607002182d808001c0342503200310b8024483d80800902058001c110385900f0001035010800c84600b004007484546000408072080b00c0c1c844118039808003140c00850f031003070785507402020040c6070180c00240191105 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 845041528 1250 845040278 845040289
    0x17160e0607060c090e2a1b0a050d0201060e0702070302040b061603090302210a0b061807183c09141503010c020601061409060406030e01060b090a0b070f02 68
    0x1003d4a10200307040500400210f16884c84035640002c1034040640b400ea00d4030113683d105034140000e46200b5901080f0b90700e5004034081c0b0030040800c0c22040310081c03d007500c0c203d0b440311203850441000d5442e101e000906424401c269030320503422a0301038201c050441d0b007040024040308034015003103070061291425203400d180804281502984400340903510310b10400045060700c11040740d000004c0c03029075800210008668070016440081c000b01c076980e060200c2c03c0d2000180f14054441512003c0c00202c5400c52842c28a200c0c201044054054982e00108141500b0307042e2150080034491201800c1032035024081c0002c444520348a81c2c0596a28502c8140d500c1c01ca00162080089018000814441c070640074248030b046e0b00a00603034050040194882105110340018007210a1034100e0303005d648012a50102c034020036040d00c0e1501c401c002801440b00c60104000c41d071801d180480d240603840145c4440001c0140700403c042e0410032800d2180d003008004841c40c0b00100080801607864 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 845042778 1250 845041528 845041541
    0x501060302071101022e090209040f0605060301060f05060a0905031b03060a0b09160912030807080916170309030a11031204051e1c1217160e060706 65
    0x116540540c840c40c0a003400182d040c01503c50b503056503c2008500b070499030118245440400103824821480000d9a89130060900e0000083d8010440005c100c100921311940c02d8096010300010442c1c1e645581c1030500700d41241c0914402035421102c10051458050003d140780c44844c034150403416515000309192011102c200f01c0b0030b50001e400c840c80d5041c1080703c1948100d08100501c03403d00b84002045c0e0054014140121207400801c600110030b00034580b5200401c040150040f00c45100c0c10024000300c3d0a5440c4000030f4440c00c041000d065001954021124903649451540c43c501041156544640008054640803d021a218550b0140050000c49006448080c05409944205414042c00c910755142080040c44144030741e44a8070038452000e640038080300c1580400d5070003da4012050420320300c60f216101000340403c403845a041030582c0701344d00d0341c8101d2140f101031a07205040803156200c000da1010030302c4041c18402d03614041d400303002803c80d0345841c0c85500c0d4001954407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 845044028 1250 845042778 845042789
    0x105040311010c031512023601060206090c011b0b1e0f0709120204140411150705060a050c0c030a02070f06091202040b0a0915051f0c030c0c090501 65
    0x124884038045114280200b44601c90f441c80c0403c001c211003a2042004031041c02600b40c2035002c0e40c040401c544980c0104003050740070301008808070b02c45032103150800310030f0b441c204081c04290340002407060001030845d004030303101c5c0d002e40f13010100c3c200111200005080140740d01414000170602140c1290281406031828000504001080d00780495008071b001d80f000050800100c200a0441ea02a00704e00c16541801208104c2d1903841c00024098140255261003c41d218001d000810690184071310314880e00762480f212101c1045114a00740c02000006040b94200000144070790945030700555114107054001400e00c80d50480b171620390f4001c9800f2102681c0800c1c4244207262800c14940d00030810707071410009540c248110303000301c1101094000c0c0141d448400000c1c09a41c0d000008014060b003880411a003000ca9044103211415071180700d015a0030703502514015400d44103194a000d106844604803c0c00541d0100c0e400e00807400240c50201110001040e01411402610300a00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 845045278 1250 845044028 845044037
    0x706110912010e060f06030d050c0c060a05180f010917032503020625051c1112060607050a30081807060e1201020c070902070c0815010506031801050403 67
    0x10800250613140c144068442c1d905000140200003440d980040d11000a0304145021a12040d2030540302c2c3c6010f140700c401507405500890f0340c000017036000d03028004100c07141460700b80144041d07003844110403448110307034001020418213200c001071074003a100b1220841d1085a00c0c01403810f0300080f00500b012468a03400c4000a220000d05078108102c9800c600b040004400c41d84000c0203c80345540c46910b2101407010228030001c0c0714207085044041c400d044032041c0300d10302ca0710400902310fa000c8900b613280c0720410404074007541003440c01d40702295480f0f401030070891099240e400a48040303100b0034030b41d01c0c0b50100e12884903c40548100180001d901c41d80f13038a041a42050451011000340080c0f2a4000f030310030062168030005210290405644951803010220101800b86c401c0704030040310792091000001d1000a13550050447c0d5006200b0301c40400c1d150b205c40c684440c0d502610f0084018481d00620051414400031a001400780900c1a0f003c0000303008142500c50494058002c117 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 845046528 1250 845045278 845045291
    0x70b010e040c0906150f0e09090f1506030d08090304090e03040311031c0806030a1704060905010f080403050a1b142401150302040e10030c05040501030206070611091201 74
    0x200102c050014243c0144240800c908095280c098829224400310802ca203108910104070300813103000441c030201070002c800506c0c24003107860f541c00b21100620740500c02d010b0303211240420244240e001d140e008014010700188cc49048414080142c012061404204800681080c0c640300d950100035060001c1c50302c6034654280440c0e10b6408190b902e02035040f00c4907a000c402c81c681c84141010109060610080c2c480c0c0340440e150116220f40101030716009400014140c6c4040702074000c4030b849560b005c0e01a510f9030011200d605c2c100340070001003481c01010500003800b89028120030905c82c5481e680e030f05c0a105014030384c0307407046030107840c41c0090b001d001201203c2402504901111b0204105d01c42c500b12440383c801c000140b05082107038054002041440740b017601102c0051000c145d0131103250a150036513550034070303084c401100c046001030400603440c04d06002d0541280c0d00105402d00f011016214000641107040004581e0341e01044081526591039030907041c084d5400c1c0000415 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 845047778 1250 845046528 845046533
    0x1110309010e06011505030f0a061806090b010c0302070303080c0f04060503061018030f1727090c0f0d090605071805030c21030904060608040506160813020105070b010e04 75
    0x40038011380180254295803d400181700e030300942229008040c3e181c0b000101d54400b038600009219a400240407d0150032203a940c0c0e9006400802c2545d000810801a0345003440040d2000c5403581002005a04030800c01c00c003203030080261a82c000710070100540340020100310001c040d403082d000b001c003003200841485120308048006218407112400c180c002c5641300c40720302442c4081484024101c81161810b03074108540904d200302c100e00072610a0b078554050171000b955101d049802c03541d0049083d0035005143c40c00c5100603001e038218000003440c140c103180c4c488c89141d0015154a0030103441d01040f400080c001e1182c54855800c95480007412004510000c6e01003801d50b000a00c0795020541e0340700255a880b00d8851000c0e8514000d00d5032024484501c0d003140a5181c040364440c0c50401e0015650340c110710b080e445580305405032200d580d15103120500b0320717042601e200001007500c0d0005e0a4021507030035904445005040c254203144d100d50340e02c407041c07c098102108800d07280c0b00780002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 845049028 1250 845047778 845047783
    0x5070e0106270b0a0e0a03050606031b090109091407080c040f0902100302091203071104051303020c1207030c180e070e0703021606090605100f05012001110309010e 72
    0x1c01048502d50004280c141803900300b03403050030340516a000b9078009189024903005036100c0b1007407103024201c54051359480c1030075a124102114540d006c0c0c002c031400360381d0402c00004e0503502001d006010491036400c0540d036000420300c3c3c810071128031081c601410b103803107801c202c41c50041c17030140000e0030103604040c01c2c0310644d01620008840a41403824141c0107907200c00c2291900b2917103250040e150790b141070000b020411400000c0501d0700001808406114070b06411050900042d207060255444200c4100110040c1100140c0103822030f014120b001d00c4c0507101c4080f40141d0340c04469115440380c6500903035006981c008880c110381154244000340703240c09007600c440703804005012020f140c0501c801e90041c0040000040550001d0458100200100301e0b030607a503000a820409a400780c684140100340545400e40c01005030b01700055641a0700d0b007810150340341a556400c0d13031382810028181418001c03900c0b40142d500c42d18030200700b00003030b00918440c0c400040041400300420f2960b50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 845050278 1250 845049028 845049047
    0xc1a060f060c060c0306220f1a0906041d07060201060810022502130509160b090a0603020d0f090305040905011a03041101020703080d0f060b09181305070e0106 70
    0x60080c81c00703010a0059400114000e94810120302009699540314800144603080020708102c0c90f0f0a100e85160414980ea4806421680b90f0401084100d00c911032411440108034807465101c000d03580000c2903400c0c180c11000e14042026041d80c038800c201c01400d4100390983d00400c0040c2e5480e10104210700c0d003081034542005440c2c104600c0c185121542407100c101c07100001c0d00d003145101c90760741192514042e0703501000031400b0402260826000003911b0300d503452088008000f15890209110a008048440c03c40c40180102c3d046864600c1c2a4041e4002c105802c1a00741e5480f030203001a41d03030f070041c4800c95210303544440d51541000d041c0000c03160306820440842c41d8150342e954000c00c1e0101280e80040c6c001c00703102c035407035034000040740390142c0c1d03420040001c00d01098007000b84449820103c100c100585c002e000142d01c0b14cc07128202d014071845a9404607210162030300040c2d802c2031039508441803404100040c440b98031003a2818a136544440010039400f0010000b099000c0d0800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 845051528 1250 845050278 845050309
    0x80c01090b01090b01080708071202072f010915030e06011202091503070612200a02010c080c07080913060b0d1b08010e0a0605040f061427070c1a06 65
    0x108040c0c4c20300c100081885030010504030a102c041e001003104a400b038400110782d400c4d111425036444c0c9140c9040d1040900218144558000340492041c048918080400c5a0301c0180e4a5601031868003a80810281419030240240740c1d40b1b07841c01e00c48903c02c0c40500c1c0030708810b6000041d090300c1ca1041c0840d1410050649039445c603500180560b5503400315150048403601d2511000d4846203c45041c002c02010b0410000da04548000c1c07066907100e4070141943c1403841d0000c110003804521b040d00d05910403140c08048034003c0110f5800140c040020f44182c010141c514122000105940d1045032182e81017442c050801160300c1d4a100b181e4015091903c46c941c590315900c050b201740141c01c1c540180104407800345104002244006180c2c881e030001c145c018014841d419240e400b4800070046409079000c402240c0345051b00c141000c441101185205440401c0300899050600e2000c000c080c15032070800140d846944007040c03010081300d024081e000d0103541581868410040440700c00080e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 845052778 1250 845051528 845051531
    0xf1914030c090d033b0111100c11070b070209010b0406080f0411030703080403290114030a0f030509102109050f16150305010f061209080c01090b0109 66
    0x421084140c2202aa41c0e00d8905441c0e00602e50a039160540300d11200700b00c0040014100c0f00040302c00804201440c040d06804440002c090541e01c00440f0004180c0c60b20314000d5111505460302508c1c40d0f40711201d501c4441c0341450303106000000080c02e21350310f036202c81032140c00401e01d0b0007540303044400d460044c0440f4001503d400e1400c41d010b05840c4006000d51040400c2100050a1040764503031404181e4006007070300c0440f922850289403d4001e800300b03440304e07041b0640300002c480c1d0551021030701500da980c01c02a2030303103003070759080350302900b8070a40c0c1e05030044041580018420700080c1151034401d4540689a00f40c803014856000d40204404c02002020300e00c55000103884110010861081e5002007003110541c03e28074603080d40940700c600a031060010001016910724000300546092440303426040b86403150031010f0f501c0a0140c25132142c4500b504021441c010241003401c504032800204002607580c4407030425800c001c4e0103840c980d443d003484808115004541c1409403162580 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 845054028 1250 845052778 845052781
    0x906030e0304061704060e0304080d1409030c0904060905060a0209040b040c1b0602281205010308033706090e060f010515040e04061d0c130b060f191403 67
    0x1001000c12200c0c082c0c00d09428100c1c4045010b004c070340c0c0c002000c00c04006049a2751030b40d8504a0640d5041d0319000e00c4c001030003c06e40d80810300030300d80413140780311801001404a28142e07001c1102d0f022001d40129070042e0317600e03200800280d00740b11191140d80705110051304c3c1c0814105102c161000064282e02c5545040030504040d6002503001c02e44e032100e030b02111240d440500e08200203105d010460f810041c7d50980b44941c800010b851147c80d00305503a9414404d0380c1410890040c2e48082c0401800c01c9001d20000f81103c54440840480c00b4103c1402c40070544401140800341c4010642c1142c0552200010b0150304010700403c01a611004c00803c0b5520b0504038840000c407040c005c4600c15110a210414558200c00654000c0e186491014095080600c1c10078020007242160030010300c2c0d4000c500c400c0300c201140b2541e40900107014100f049810750058001800c0b1070500c160b2003102800840711990f0300b00c01030900c4051b00000201d0302a8942005001066410001d1103040360410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 845055278 1250 845054028 845054039
    0x3090506010911040302090f0106030e030708030c0a032901090621020d15091b05031e040203120a272403110c0c01080601030203090a0b1003120906030e0304 69
    0x40c0d03050466912000000d09000141d076640402d02c115070029501c552268180445041f804044074100c5400d13480c10403144420f1000d2548901030010054911402400084d0030030400341d00404011000b407900080e5101090038071a03070344400c00450030382c99400c0c1207074651035608002c400c80581418140a00c21600c1058140c841c100c150710003808054009c00c51911003001500020003c60070116501140e54075210b0320310041a1101045140c0d1500b01585280140502c0440e40201a03002401340c8000401c80a2640f522005e04120382510440c0c580802c81c104540c0905400c82d542d45c0c2d01e080380d10000310011001d12000d0503500d00341a00712400c0001c4920800d00b080c10701c00040c0b41e03c06270240303850258024801030341075014032140012214800c400c003144450500000742c035168055100d5100460803404221040c00d03031a071251038035001107404800381642c001c90648400d04e0b11a101c3e0b0754002403c203403181480101c0e01909080c0004d9030107000b0020910811001107080c203240a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 845056528 1250 845055278 845055283
    0x5010305010923070b0d090803070206160c1101030506031f140109062103090e040f05011406010806040b060706090507050108010b03040312110c0f0c030c04050405030304030305060303160b16030905 87
    0x148240f111440d4000340e06000351206030064510b09422a00c8e9985030310740464040d455101c00c607001241d9102441c541071030700d4010011000480d801101d203210155015005400411016080aa051290032a0311820441507420103142415040c40030554401c9889a0f4015500603046003d1050502d0780510200941c94110340303a450808040c81c4484001342005c0c1c8035143d00380c10068820031b071389041100340031100300d551840d03038420300003082444c0c4200000008901d055964900042c209000f04426246c15000b040140c0b0340100b01c0c5203814410303039401d02105d07100c1504907203603044610100b0003503070011039003401000ca1400f00c0e8134503d000e6400510381c07052a0103840d105030f80d544007a9000f0003101e05650001c0181c8046805200e00ca4160b56a102294000c2511a00c02e400003040740303040601035540035550200c01141180c07a035603800d0f009004c0003840700d42c140c44140110784e00c44030680480461503008a2031040d40e0309150440c1c00d003015040982c50145802d2403005000035070b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 845057778 1250 845056528 845056543
    0x1181b051c110a1e0302010f031a04023a060e090c0409030e03030c01050a050105010507050709020f31090b0105181201020c030309010e0a080d0207110405010305010923 74
    0x2280702e14150807a0103001070401911900240320716107182e98462542c012043c0028140e038003d803112600d001c0e11180c00c50070350391146411901e400c600c10542c140e50074607030060081500c10300f241110b80c12481c00700000302900088a0003010a10300402ca032840032034410306000d4024050b0708081440c00104d5507545100d41851a8002e590b90300803002418031407220451804001025255510342942d00c0e280a4034054940010139440e040c0005000c0d80200120b54085502074007500c03220345849541c00094100403006a81e18601700035400d0506122000e00c41100300d10b2440584028031480900b0041580d504030300f11481c5059285030441e81c001d02540c0c0b20f840f6512001110440540200d201480d00c4000e00801d5800801c461410410100c09548a025020300030024807403c1c11000383d440e0078060025002000802152160403000c0d0001e0880a02070000380003603114480115044030400d81c010365075a50340748007030b00801c0281203603560030415a01c01c1482e00d02c3d04034a240d8980b0303807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 845059028 1250 845057778 845057783
    0x30106050c07031401090b162003040509040302070602060901090b010e060a03060c0908150c0a0f180306140a050f0a0e010b040c0201061707080c0f0301181b051c 71
    0x40410408024032040110708080c60703004040741ca031302030304000407406000c80c0f0300d089607003006220024070284500614208030949076610400c48805140b001c0d44101360f412603030100c81c00104000300303540e2103c800142c00f070340c0300383c3c002c14220317262101c000e061090141110049034181001040401c6101d0780d40e0741550b0001c0e205441c15100d0f10000b038912151580f0040145040c80c84142840d42c02601c4e40c03007100d90000956400504103d14180039010403944860700c0841800000551403140c50301e8406001142802c801d03042007010141e000b141264030071542140c0781d001c08146600d60a9100b03401505040b000d0200341040100c1400c0e002c0024040030056130303680692880d5900c250040e1065101c0508100603580100700000e003c2d2255005400302d80d86c04584504510b00006a06d4048440c1ca80140c148646d070142000407000395030802c241d0564030360804d1021088a031584145841c80360344080d40c00815800002c030241625030003280302d400109801c0b1049070005904075156039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 845060278 1250 845059028 845059037
    0x7021014040231021806091810031a0403030b09100308030a02070803010e0f070f0c030c0c170d030606020a0b01051003020c030301080a0303181a0901021b01020711010c08030106 78
    0x210000e405600b4400c2000b80e102001405100343c50000c40e03d980101442101400da0314040c0e00c1810520080e482440d11040c1c00081c803022102040241c642d1454128107080342c5602100d03135070b440e4070024824403a2945007542c0f6100510041641600c038440102d981070b502e06209240004800345403040700e200107495554000f00007079540500780d0440301d5250740100402d0b1656110080207070901d1013101c0d42c00384904202c010604250145400365000c01080c1d035490180484d03650101d681c580c1c07038001190311241c00340c408101d5220607851a940300700d00b80020b0440f1401c101e00101585c000758411801d6411000030640460700107045d40d810b56405844111408081c80c0d4100c00a01ca031501079071b00e502010001148800c4042484200300740a40e40030302c5564807002070380e1803403004040010140750003608211400c92903940d045910050a600040c01c00400c04440c10296402c03854050690f50300282140c1045042c2d880c4a00740c41c0c0070320b08500000440d0382c0d00c00eaa480103024050a00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 845061528 1250 845060278 845060299
    0xf180f2a010c020d031119050f1524060a1101141017070317030109050604050c07030c150501080c0109080102250501020903121b010e0601050f0d1208070210140402 72
    0x1500414448040f101c1d5035046951000000e174144610100c1c1440840b0780740035408003c20222400160103d41c400500c0c809285503d42c0003003160804bc804025a04035a120b642c2e1039441d55131a4003504c08400c00f40c070346c00110012048a682160703007075492180c1104d241c00c2070044044e20f4442000640e002c840b4412514058414a5407030500a5840201600b800241c4540e002074240042d50484070451801c5c485916150200820b03038204643c0b4075001401400483c1c0460310915010101c0c074010f44080b15000781c54401102564000d80140b25940e0140c8040901e44d40e0014814006002d075030021030804004c840b86044001c100c0c280001c8505204c09242d041c09402c1d41107840144000301128010085011041d20302d0f001034440708400703050304030207154032001805020203800400024003201c1c0c1c2020100031074104030b6800a600407995810400000e00201d248050340c20454030b840000345030a9400038544082d11402d00d88050505100c100c0e0036580090807078100764112064440c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 845062778 1250 845061528 845061533
    0x60c02030f1203181c091d071407030c062a021230150907050a09050402030c0c01140411031b01080613050a090611120f180f2a010c020d 60
    0x4001a00150321903440e80104850180351b0804502c5044841404c0f1140d4010b10707400340300059800407994900410384d85d00661034507050410050403020704c282132203058415591200c00132100c1c1400c400d00084009015041d0341c1e50600503100c003155903440104042c00302c509e084040ca00030642c802d0360030381c0c040391508070128400085034400b141c0e0f445008164a0040402e00fa40c0c2d003114500d600440075000800c0d402c030700c03a5040321001030680c1c458078034007490a0140002075100070881400c0010500c110020307100280154503003030492141c4144a400c00782007080441c510000018421350003500c00c0702609500d800303644d00b850801d09195001f580c804001c120908040740340782040610b00001c2000c00d04003980074558240c0a81030401001c83d281400ca0428440c4000c90000d41d03002c04001050800e5800095034042200d10703407000c6e0312082e1070703605d840c0008007035440402d03401640ba911074101904a8550800d440300c0004090341c165000060b184000e01c11000e802165503440c800103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 845064028 1250 845062778 845062783
    0x150b0c1f060303210b03060a02121e04030f090807030302010209030c010813031101180f0b0117031b0102161a06030606012001060807080a0515060901050d0f0c060c02030f120318 78
    0xb0382c5c01001d000d072065071500501800080d03101e000031440c0348643c8004214a54041034400a14a42d1006a100142c44940b403d0300ca04c28850120010801003440200b00d00106000d030038000e500c80c0e000541ca4503600c0741018103084015045904001c1e090040040e00441980d4803980d842d010f080900c0c00d641c00c04c1188e07000d000f001100c80b1089420085100404c0800042820f103103000e903480800b00c3c1d0325000d403c4413118103080813680950050101150404403101c1000c103c8070010001482d28124050001000020a00a599030280c1c0703060000c2041c809504264461b00440140c80545051000a081c43d5101301d02c036211405214500341851000758004000b900501007150780180d40c0c2d1100719510301d5038100448560086a00340405038046546a034041c01c001000072117917a00704418410328200c0d8003001e541340500b144001002c500d041070007202808441e541c807111507103d4018103180c900e14800590300c5034401d24900b1304250070001a250000000c0c6224011070f529460b541c3c0c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 845065278 1250 845064028 845064041
    0x161110050f180d141b0306150d0b010b031009090201050d09110d050705011706211002120a060b09010c060203061801091b09030302070603150b0c1f06030321 69
    0xfa041146500101e06010101900d41c000045200441d100c1628648001d0300d1580c00d1a000da0301036001002007240c0c111001c03841000e016000c0c101c048e440340681c0f210305200c1d82c280d11000c0c8030321002050006074100c41e2440e030054a602c820a112440c00e560000b403640c450101010080303035481340144200701c8900c10140e13201100030001400c030207041c104203840b00c4003031240b140403c1c0c02d8401c002c8800c00f5a88914814040101204103801c0c0c100b035504800c90403039941400c28003035841142c80421f6030f48050902c85074082658040703444d1800e486002c4516540002200b4601840346004a07030340b00c00520302c540d03804007000d40c50b902c0e0b07100440c101c04101541c16900e082e8030303400490f106a41e80d001c090043c88221070b03200607080686058070050420300004c0c00580140340e003440020b00942120404a000b030b120384030b1441d920089801c2541029441c108650800d40c031040f01c1550702500304280180c9810708101413841c641c0c000d016040003402c802c0f450031102c500e540700788001e030f40b142 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 845066528 1250 845065278 845065327
    0x609080d0f14071a100b180d0c060e01140301030b15130c02060f18030a03020c24061005090112150305120c06130803071211161110050f 60
    0x281d195501c0f0724005401c1c1094181500182003001c001504a19a0114070000c03140500303d06c0c1c1ca0840100c4550500d503001041964204404070340480008221546410090003143d40751440101c0c00c0c0c00041040651000340090000f0901c014008140c641c5500c0b0340105000209409151a000109400303401c21508480c8141c940901c410f240e40e0041031840c410000c00307241030141d5444040f00500c202e1085e54002da00d90082c840d4038110f07070003a40140800c1e086841162070b0f030007440d100201c11040107002d0407040c0007000c040c00002d0800c203070100212949030914508241c0c3c0817000030601c400c03009420146030f0b00c6003150380002d5002c8081d10091500481030321880c58000c050030b20558807400d030041d240e201c1c80c0c000900b0100840d401481c040d9202c2c40c1d1034078685030740008959103101d070310354030034400d43d0345544001c044c0d480401084e902c0220980d03126200c015041c50070f614820341d5030803802920661406c0b900c141d4040101c80030340c8800c1100381c3d183d00703807140d85001220443c0140d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 845067778 1250 845066528 845066567
    0x504140a03060c020f060c040819060f0c0e041d0c1017270c09071d0924010318061d012405220c020c0904060e06010609080d0f 56
    0x1060700066000c00c1171000c0e030200c00225a62526090752498052140e841001c1a50b0044403004c07241c00d4118451989942c00743c3d102180c0c83c00104002c0c81122921074006005c50240b1000d800d0b542414000c3c5011740010901d49008212104e841645412400310b4840c0b10396122401c202d0b00c140078402e1507005021101e041c2c01c5520b415080180d50403090481c603881c0101e0456243c551040004850b11142c80c041c06030000b0b9103c40000303540210340c5401d0074400b01c8141c11303142031075140c9210291083ca0300c050f56080001101d101e0100b1140c503440c40c7c904248c1071400c0035041d80d80740c4205200356a0f00480008035509041c10414006207600815141035081188444858242500c000340c80d1010000f20000166104200540d409400c0703604c4140a01c1400100c03240040c9038801c00b011250b50040d200d1036034482c03000039080102210111a00c40c0c0d0350006400829003000003a01425141c18141031150034624080daa909440886d03004000c91b40d82040c0320341c1d04c50369007100041554140d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 845069028 1250 845067778 845067791
    0x100501031d06040c0819150c1202030901051b04061407060e15040302060f060906041d0109140106060305060102060c0a0306030209090307170f180a0321110d0504140a0306 75
    0xd1075005a40c04d0f20801120340300f0100c10040090103501c40c8003195a0150b00040c508000054030030203031000c01488000d1041101381c0700b03003848c02170008520890703071040002007610f800c10f02c601d00c411100314448000070040c8020f10001e5009181c9418102da0040c40d90384407962450003001801d0340b61103600c07040c06820105030312081502d8550703010704e120750246d51065452040c03249003040115502c6511181400c00305140342003da0000b080300d01c203c02005210841012494291000c07502c00f21a050941e4a60611201081c45500007414181c6024042810100c0000350760341030160001c00380440002c1e0104540d40641e012000855016207600e0403403810864990b200d400a402c240c4071803402c22811030304800312800301d42c0000c2460040a0500b6280344007004002610041941c10030010880480461240b250b240200d907044025101d450844017801003c0c900f81c40d0741d00310658000000181c480b600501035501796000c0d0484c0102c0000c009c3c0000d0400d03811a0302c003500151800d007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 845070278 1250 845069028 845069033
    0x506040e1c02010e0a0f030804021503100f0f0f0302010809071a19082509180c14031909050118210e060d020a0504030512190305100501031d0604 64
    0x25507103000300e10240c0080182c00c0ba00004161100c00310880285000201030705c0c840040d009144581e04540085c2c0310708131844908060101e55030007030b01d0855041007103400822070081040d004501800e1102150148680f5005104010a40ca400024148001c4030b0000d25200c0080100c0c900070021542d0519240581c00c04159459000201c40c5041c0c1d4103941c10400c1c064010194240101c19110311011010308481c41d050740544800d401c034017000003070000007071100e0050210380500f40103074200007032802c4144000780c210308400030a00340c030302028001c00c43c80e0310f01d0b03400907141d0b103041400201c3c000304907141c403900404420650f9994000d03100c1c1d9100610152101030080c011a00301c0d04150302e03182c4407080d610b0f20b1990000c90790002e01004031000c10203560300078003029440b03428028142038a82d9511400d04410b24481069000089000a01d244641070f44800c04000d90034200714500b44048100845171340d50041505154840841072514000071542c00e15105000c1c0540b0264142403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 845071528 1250 845070278 845070313
    0x4030f02040f0203161407060e060106090e01210c030203100902120f030304120e100512060f031504110612060414070f11100207080d0501090209130506040e 69
    0x9880aa020742d1814411142008281c400c0f81d008652503000d8120f20400031000702d900c42c65140c41c039130f030002c01071041000180860003082c1c04100044080c102039818402c0c01044030003158842c1c03180006100040200e494901c1400052650040141c2c40d004200d04180c03000c0704483d030009405100e88441490b015459600020006108540c02710b42403120500699440a40140703110494004001080000d800510818081ca049007400150000401c000810422403010401e01150300007485c91304000e075403944142c1c0b1440071548000c046c005080403a6803428030206054a0103400c0d0042810f100d242591000da00394010030403599094140e03504030ba4180c05480b1140240e0030308103c2502c0b03d003040400c0b0710070307030740c565a000c00d0a0f562901110f04030700d070481220481c0182040e2902a000700c0c001054410f019801103543c818100d10400102c0760140c2c400342265205201d2285540e8030b500d12031034107003464030340412141c070f1300400100140a00f14501d03015126a000c40c040c0c42e42071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 845072778 1250 845071528 845071553
    0x7050906070c15180510030b03070e04080d0b01080c03040201032a03411e0a0b10021615031d1c0c020a05150702040507021e0714040513080403 63
    0x50b60344042e280d0b10032004814000300a030040c00e074484580d2656181c1c547c482d03408450304080c01006c4501041d42d034115504144015a000d4484c0034000071020f500b0301460103602a280c0f402c0c40d103040f031460f03c403603501450301000c0c1000381095118214000083c001d5444207540c002c10a0b198454804070f440c000d0000e00c82d60039000c681e007400640311100c40c500741e500c0c0d00f820035140001d556111503469025079012002010f80729600c1c020b00d0641c1003180307010480c0313114594028000542d40c10070020001a902d0903404002154000c1003140c00e10791100304103104656401040517024601240d098000e081c54a20f01107911001800018420100041800310710303203080010080100001400c0341c040c40c00b070b48080d401c404070803020002401d0080142600224440c0d50b5820804180d000034280c0340c00703036141d5005a00c0038a6000f0381c0c401485013402c40700d03640380050940f40d01c2c01202209020542d14514071032662500090400c50410107440301c1503601c0001c0320754a0340c070b9180c1042100038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 845074028 1250 845072778 845072819
    0xc01120f2406031d0a03050a090b04030b1503030c100b012001050106030b090411010807050f1303060605030109030903110307050a0305030c160810050415060f03051002090907050906070c 82
    0x2c00315015508900c80d02c50001c40701c4184e0140c000d000c09520701b42c6250340100e5070b040800c88500e030001290010580904081c62042c1002ea40604260300304a101e5500d0b0030130300d4820303041040103180c4008006a441c0e400400c00401007081080040141d031031095500700c0d103940764803000d45201e10003010b41c0b1850580307005d500c08102c4800c03114180401700200f141e00400042050b10720021541c003501c038550f0710005d00e260507454041c031840c080030301d500b1040143c20cc00301005403d008214107801400d0240c142900200b2082840340c0300100422040c2c48050040101c12141c1c84d100d407411300410010703001c0a81900c640642d64540a0b55941c00121201d5040c007617012448a00481c1e01d200780f0440b01c4a2004100740e01030810110b004082c0604100e4440d00d420441048200070f07401030400800c00407024403a46403550500324100211a00ac0c42400c0e841004569610ba8501002c0c5404c000185021500c500001c0d000c1a201e108109011b4080640c4800c0003a4408042142c2041e20743d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 845075278 1250 845074028 845074031
    0xa060501080c031222030f14190204020f09060f04030c0e0f0a0e0a021512061c03211814010c050d023004140c01120f240603 55
    0x3a41e5110094480e182d0001440d03041d00019040072061042d04054034415100d0200a0f41d0001c0e502405c6000b12043c3d401140c0030f51070780c005002402500c0c1036000d0a41107072005054202841800e4121061500100920560740411b1100c2d001070b440c010380f000f0140207480c20307a96800d0000780310000d411a10085402d05501000411342e80d6010040a006a43e07503600b401e2141c0304d0030a400e015000803c140409031003456100320150740e8607009005402154a611030b9120503c50140090302001891b460151004880c20750010300d00030980f0356050741510308140901c010b624807014100740d004030a500076003000d45d031300e00b510a20440c600105e44100d50b035503150344100b8002d078240c900c00c41205000ca001444840da400c0102d030002c0515540703a42518000580340c0903024241c20f90522190f41c8004081c08010410116550a40b1404125402032010b1400440000e210802080066412980700c4004001603140c6130001c0d00042c2118a800180c40f69440040d0b040350642d10640300000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 845076528 1250 845075278 845075281
    0x9040b01080706050f0f160f080a020708060105061603021603150f0c0207060807050c0105160f0c0b01031112030d051909031d120706050405030c12030d200406020a0605 74
    0x540135a04031800c00c51324000300381c100320b00c00d0301c802c203150000c1020030f0651519001d10780c001106100101c00071449801c00c55218a00d0080003803a08004d5000510320368090300061055030303100020341c2e0724280c0500160029660368a0120b0810300030080854103040380c060040100041940306021402e9401c0d030800006a1440f0060b00361514518082c001d030f04081d01c00d000d43da203d055501e6004c0314a003800c40c03030280c1c80c0e60b0b80e0b0b00310f80d82101c0c540154488400181310541d40800b0420440c4810728007481584003540360100815018031000b4403801d00040e0544058072125803521b81c3c1c4404009880e140c0040b9210b060181ca0100e5001980b52441120b91810302c01714812400c030107415594041e074000c0c1d0803c4a503030640711019a154441c80ea03900c640d51080d410410040609403e941b0a41c60303070b00d48028140741040c0d40a600303100c1c2000c81410b01441c0740c00002d44040c5002c0700c0012400c2522810081640e5a00c0c107032048550308000f0b0085003280c0c00142000001d403145000304407070b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 845077778 1250 845076528 845076539
    0x106020106092003060409020a0b0a0804170304020604090f1b0f180f090b040e0a141911100c06230603030307091a160f0302010f110d150509040b010807 67
    0xc412001d0900b68000042c80817446a0a00354052501d662000d170201300d1030360311101000e245401848403040040d692504201c10003402c1e00e00c0c907021301c82c0809690f0460900390300207a8030f401035000c1d003c101c2e503503036150482d030911135081560300c4411007800416000c00c008005100f04071681449010580c03260400030007200c0c140700350044800ca082802c4040e402e04000c42c000d032140900940d44680c40d140b25522404090101e0041035114011084154983c202c01c1400c0007041c840c00e1429140c5180300750301240212500b0101c40100315407144244030303064030580f40002209800740289243c0b8400318440b91038200000001d0360300d20483da8080e950b02040590380c6c48122401c01c006008103500300070800d03070300d0508641301151284150410340c0c221170b40c4100c10103207801a01c1240e10491028240b507028844e082c10041401d200340904034410350040d40300d00c610b803064141c0c1e41d910a407a50100a60410010141100900b14809800c042c1000764030208203004003000307802100300000d42d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 845079028 1250 845077778 845077811
    0x11090a05070e190515040b030108030309061305030a0f050d15140d1e020109030501050705180405060f0f01110118050c0108092107060e0d031b020a080304110603010602010609 77
    0x7001c3c5010310824244504000510102010030b4101101e611410b20000ca500008070f4041d40c060440700000b50385900d4070302a60743c5420000f50000d40900002120710300400e4002c000c07030f10b1000690034280381d0b1401403417044800d44651003000844502d800c030500d03425480c02e0810811540120000300041d41c10f4010440c944114600040c81603484012000740c91a6241d2518030780c44c0141071200c02203a5030745650b42941c0048486000041002807440180741d0303503181c10045240143c90800281c070702030700030524000c0c01014261190840c11103c050680c8113049070fa0703070400100700a0012000d5102c000e08100d8848808030b8660055201c3d2140c2c0e9481584043e2003064200300504a4000d040004a552482480303030b004005020040e078000f0401900941c200382e0b0905006107013110700190000c089a004110100d80c00070155240801c0c940c2c00180301c00155000802c2d03a48e40e403254546240300a07050172500e9007012001c0300000701c15806500c80d908448440b91709100c80035841e0000070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 845080278 1250 845079028 845079049
    0xc0e0c0a120b06090a0b0702041104081e030c07091b020a080315030703060504050307021e060d0b040e07180f05012313020d02070c08030711090411090a05070e 70
    0x300040c507041c0000d440c0d190700e80002c0c2108101900041c5400200404240101010b030481820303044001203503811030420f4403ca2510b0043e600310765040c103051940300c1d0b4071407d2032440b00f613201e00c020034100301c058014011600d8144014007200d03101e80d520a4a50040e140c0100c001100b050015003080c003080c0007048030408280d0020120b0b141d69a120912480700c2c8076100c0c0c042d01840754040c0030001440c2071042c113000701d01900095417203140354810031940c030001004d0007104403010742201d0b4407a2260015215800b00c1c0d554040740031f0255002180c000c00c46002c0d0030802d0300c1040d00c0000d1120f5121001010106654003e01c44140b2401881c0151072080c8a486016800041110080b56a85240c0543c6100041c55100d504204007602c100384d8100d203000c002c650303500107090307010004a2000f41004041c00000303542006942d440e1101250b00042280340144038050014040210380c0041000c0c4ca08000c01c8070540b8204180c0d05802881c0c00c0394050b010a481b44030404103803500300b6920 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 845081528 1250 845080278 845080297
    0x103021c050a0c0e1512090304030f0308090f2a041b09051c020d0b04030314070e04060608090d050304050a200f0f0d06020a0e0d050c180705070b07050d090c0e0c 71
    0x74500300c0d190b1b0b8841c0000100910410840c0424040480010030002401d03500070b00039510a041070502c500b0301c3e0304104180c40380380313a198050000c1d00c011014211498802068251841c00017620346000b00e8090421421001620052003010085e050741000c0c1c03450640c4c0d030940c0c0248810640400580c004071840c0c00c042d500a010803200c10028481c482d0b0254000d10038038020130722a030805258140340c4410360344000807890014403450542071501c18003008099a20b842c0c66a0305040c03e11940f01c03506000a1000c200c0000700013400d100e0b04011002049a114066030a586c1d50f45c03c0010100d125101005d00c2801030600b80760b61441d00c140c0100c40031600405420000b2034685e00c1c04029070000c003456003800200c4403820321540c0e8107504800b00364060005814452003980401120040321840d494001401c0414071200307075840f60513114013543c00429454551945842031341c0ca8040c00c074480c540d00f420711703000c00d0070016480304003001c5401c1c020828040d6215000f00080900410b40380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 845082778 1250 845081528 845081569
    0xf0108030f07020d02061303120f051e07020306040f15050702031902070906030506010321020304120309031e0b07090b1602040608150106020d09140103021c050a0c0e 73
    0x211607081d4428002409014401032a64071310340c00e65800309241d50001d034200142c0c05081c03542001844000d800e80e0ba1160b1403442d080030255160b40b40076082d80141a1500300500703400c04001e680d00508011501010b800a08460307103032420f4588441c81511420302100d040c00348440e14605a45680222401000950069420520360103803071003800800b6a03030081148100c0d240040d039264188103081c0030b503002e03034041e00f00c640c1542451252800c0c010103402e64010041005052a9808401d5600740c40250384081c0c4100d880d403d0484521819404c044d0640c2c100d0190010641d4000304104c225600c00c60400040b5511008180c501e41010310038846070680800142c0d824880c01e4000c0c40b800ca00c010000213041d9124100f0602d0310114281110301488101d00512505804101003007010040b03151000805040c09604041c0380417140d90241403540224840042401c0484514801810110100310602d00700e654580500000894030020500c1039080560b60f0038481c000b0504201400c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 845084028 1250 845082778 845082787
    0xa0c060810030b01080a02090f061008040521030411040c230712170115021e10050a020414040203040b060d050304080f03040609061715030c0a0810050f010803 70
    0x4180d64a40009148a1144508880110002d41d90101c1c072030107004440020440c03480d0900c140003414001910504c5110703401c008100040d598154007403141001850446102c0d2168500180b0340300c0c1e000d0058001e0740c40d601030f01c81c40c0341201d40614825401001804100079161003444100d51000082c2000030b0700c01841c0056580c20080d0b208141d2103001c480c1450600e2036200c0d004d8500e509192400050f02030a501810b032421885003d0142c00180d05200100742011000b96075420f4203641c0410210105010b0384410381c05105001410060042c14001842d080050784000e41c0306001d6030700790411100050041c0c0c1400e100741c80c442d60380035900c464507894000c2002008461520708541d20f1008100104007404180f060307140c00c050f45c00040da291814030001400c14205500000e0800c0021014540c010200706141504044000308104001000d8004682030809441c0b0881c2c00400c00b01d000030b41c1081c000b50b0002c0c0c14200040401c06500c0b0a42545003242c03081c821502d00d41e00030701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 845085278 1250 845084028 845084039
    0x604170327030c07090605041407020601031e0218061509011215120b060406090506031e21040f0501210506041d0102030a0e030a09060e060708070b180a0c 68
    0x1408105641c161070882c2c0c00c2807440c5005500d4020180c03c1020720341d842e084200a942400d00414441041c2040080e9092501f1040290f440c01d0520014010850b1041c2040c2e1a81c803140002c40d03200c3d0064143c03a02000090140c800d03075003060703c0581c02090000e410100c05c820110030341d4810300c0160340781e454496021403810058400440101666004a440011070302d01d006204060030703201e1071502006140440400045403e180d000c13a17180c60500080140c1030358086208070060300504140221074088181403841e00c8103171902912810900403114042442504c00b5000b1216126a030580861304d420044a40c01a101010030030f40b0748640c48000c016085070040355101a001d07100180300007403501c10406688050b503c015850350300100384000321071ba5000e07400480c981e84004505c0d12800c8080140000f002e4401d8104001da16a0400115610581203911160304410990748404d0141440c0c0d100840a0307644c0300003400e141c89448420680440c0301603640d41c000c8c000d500b4091520 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 845086528 1250 845085278 845085331
    0x50a17060307090e1c0c020a051909050108100b100212030702160b0c01150e0a020d0b15131401080705181008010f0b07081602030a1406041703 63
    0x5405580d05002d10708002c55040468803540d01000b28800007841c107420500c190809100302080701204020545402d4009a290383c0100700c02c8500039030b00701140e002451b0b103802203450180c000b0380c07507142000f00000e280e0301c00003640507003036003031a00401000701c0704000c11a90722804244030000d60091000c0c0420b0054045c0a140d00c14484c0c010303240652404080c680b0000e4003904201c0100ba404034621881440901c0b48454514240c003510710210f0804500d4a0201c800800310340000e80c000440c1e0b450501c03140c00185c0d84840203001913040d18000c020b040710790381281e094803038290740400e000226036040100c40387c02c104042e160b402032500d0700c050445103030b807141109d0300c00c0c0403441041c141c081d21541030800142d09941c0d128661941014120208400f8580c007410355030405000484c0403507102412989644c0183c01025420001031001c0380c00c1c006030103006000303240703400002050781001164441c03044d07202c0c04c100420b005807006074ae07005000a40d0012043e1403041103184d03a00805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 845087778 1250 845086528 845086531
    0x109121e0203030c011107170c06221506030219060c2d03030f0c020d0e0405130f060506100815151b010209040c030615050904110304080910050a17 65
    0x150580349412500c92130075013525032032003e00503070302000118641031140941c2e000f442991950a002d02d00302c265100075a480b5400351800d6007102c541c0500c289400c2d000018412843e52001c5140c02d0204007500d0392000300000c0c0305c180e0160006200040070740c254044103000780c80650319403a001e00c04940b03510710801607154021304064104030500e481a001000808455846941c0201d09500c03454440820344400010708001e55010304011101141c00c05079030b0395101c209950004681d9201030300244188012080508030030300d607501d00030a02550350002d501c90201601c03180c00a2481d05001c6800c44001c4a1307821000525810551252178007641d450004010941c200c0d091510643e203c5210b0304e00c5444000d820303980058102c071a1704040c0075054a80810303050400c1050701d0003585100c0d0202840c040ca0410000142c403500f140c0e030725845010030109051300c01d5120310b000c0c602181c40354444850984190300f9840015612886002102d80c501055510340c54500240c00400161120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 845089028 1250 845087778 845087783
    0x40837020d0819170112060e03040b040b04030b060306240111031902060105090618102301080f04020f24030f04170a0f1103070507030503090109121e 66
    0x100341d0350101055101c005044800280015182d141e03071200c002074103200030442e401c0144942d140040024060b50354000740310039001074000c01c0780c21081070780c03034110b12660b00003013500000031030b020842c040000040d0003a207100310150009916003404141d40c5c0d000883c1c0345101042103a110106150b20000790200082040c14540340c0700c030f03400c03903e0343c1160480705010b0300508169003034850b00b0f40c0c10060540104000d940c5818542081008a00704d81c2d43c0040501c0030004400105134447e0900c244e000c0202507203012440346441718007039295000300c00700043c1d00054001021441304050641503a0040350700800c030f1841c8400e0441888044881002082d603c2441e42c0f5032040300380e060070300842c031a102a408542c0d0342d280c140380a0021041850103403a8801007030041d00d41d0303613402010b05e00075101f4a050400c100c2d8070b0b2806443c41d511901c0b4004000c1d00510b84000200a030020280031881e00907282d80022644480d8521113001c064074028001e01d40350180b03110f0303048525100305217450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 845090278 1250 845089028 845089039
    0x3031e10091d01051911070f11011110091a2802040e0a05070f110d0c1401140703050a200307090305060c07110105070f020f010210060b04083702 64
    0x1500c07442c56800c4840883d203815500307900211004e10041d0780c0c8940c00c0d1881c08100c405081140e140c88900103030480b01d50050184904d80c2c00c982d000d82c0189090024a1142c40c11246030303442c4030718410702800c0d00b02021609480003c10f03920704075000c150080c2c031519207900040383c1c1d000c0c010840351b0140508201d45840542c2000049007050009000500c65180c0d02d00c080b03814140210014400301350000070b0410400c010003241710056000c107159a001e03046181800d040a450b080081740a44442000d495031b601c0c000751003d205003103103000c0c2c0c03181040e070f142040295184038001c402e555000c801244d490004003000f00191504401840c2c1040040c82d01c1212551283d40b46450801d059802a44007000403401900300250b022201094140030300e002400d00e00140d654170051049090000d2003051000d024601e6644200301031100c010340c2800038040780d40d840980300080d611a0150100500a00010000251100944185840c04c000c282c0264844445664202d4130000350204d0f13000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 845091528 1250 845090278 845090321
    0x90c17060f0411040e0a0203070e010e0a270506060a05240f090307230a030f03030b0d060f0b0306012408070504151710030809060702012003031e1009 66
    0x151945d1244040041c1c812000f454013010301d0040500d403401c2640400703514003014006000c090043d030501030300041070101c04982c0048250380c2e54000c0c2008039400d158030340203880703c0d0140600040d6860059030240c0c0d44d0034551307807100140030010031010410050520104001408903400341d005145000c000004241081c031741c0350000341010340303d40c41452800345076070715442c0d481c00c140142080d418084460008803813035030340d0352040080c02c1e00015007030503614640300c15203441d0300400b4001c0c0ea41c40074080218200031000c590003010710a440a02910400c0004070300b40295942d580c003125001d24100d841c0081c0341d8021218510000c000c4010040240400600300746840da40f44003011b55526003c2040c0003100c0c1c480800840104500424680840104085004142250380711402035071b569990f107041c0d00050340c86590b440445000c28000d102400014500030002d18012110010012803400160054034010303003003512503d84100b000802000108406c1d440902c401d2011b1b8100d030307007a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 845092778 1250 845091528 845091563
    0x7030c02100c03020f0a030e0d0204200406020706020a1a041407030303020a110c0a0b09060c0a0b09060601020a0b3c04110d0305090d02120d03090c17060f04 69
    0x20711071012040008203298200c03000815805001c007500d0310650100805c01e418854a00424155041e46500c1c0034203650303811075043d51103e400030004840184440310640020020b184040e92041c490304005000f08031000c1002880450041c1c203864000000c1d01e400038440b080d100146202030030446865803400d0f00c080045006000c04001075009480042c0c9071400814080d001e1003503803002031920341000d03007042001c1c1c0d600d00c105030665050281a544170003101d0701051440c41050000c1245d4440e141c0040d0030008a0001c181c0304440150a40c6c3c450b03180e180043e40e480505081c0207144040e071a000810020a40b1078117413060110b10704800b030180f0346800c0780c5c26144c0940b20784640f1407602800c0000303001381d240015280c01b60079030b03081c545407040c1c1e03c0040c9580034148206100700d180e40d4030703001550341c3c07420213440b81010482982c209602d00e0300050001c0902c442c08594030f00f5440400950040003281403038520314410b010700480e5440d60400164000002c0080b1024544040301152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 845094028 1250 845092778 845092789
    0x51203040e0a0e1e06041101030b04020c030c100b09190f0e010b010810060912060906060f0306110403030503010504090309081b0a08012a030204090f05012102031207030c02 76
    0x2a036041d03000050300005501400d042898100c3c031480c4942050400351342014000030f0f500d600540110441500c4c0d400240102c01400500e0b40d03595001c1e0000c941d80d000c1351400b000800301c150200048569442c1d07004402015075410016240e445a100380000e03560701107000c0032021111404c040000d4a001400b102402c81d0b22840c00031229a540c1c03410060039503004203015800000c034800c3c00780f00318908a401401a1070501400300c1200c60401e44031b0400c51150086417209901c06010300205898143c6c8080081d00c0c0e202c191003481c03d100c2256084c5d4003010031102980d403da036501d1b03c1e607828803050001910016400b10308012200f80001010072042c4505110780e003081c0030750300e60035080c001045003c0005070001001649001403013100111030b840d00b01514058640311480085a60400703400900940d44820300d85428a03031400281c0380c16034020303811b036090303c0b0141243c08469807071850324202c0302400030340544c04085601d005c0c1070f8503c05456514424681020502c4090b404607a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 845095278 1250 845094028 845094031
    0x11409030436061508060a210503040602031c02190311070c0f1401031a09070c1401020304030f08091506040f09050a0204061e1503061212080a06030c051203040e 71
    0x19055a2150240030244d00760f580c9041044040c5040e041d030b400d2150000b5600f140314411900403030b581082081e00e010100c000c04000503009401e4030f4440e0398480c000f94880d4044900210001c0709000b40a035100704610036182c11001c401840810391044a005030010005004d84201842d420f0180f1800034501c0b03450613015200603a1960a818030700400b00001e0803031241c61034145405c01c0f0071500e140103034042c009500c88080340c0740f00c542e403078028087d14095001c04001d400841c00c0000f4184501054000314000d6200781c3daa040480343c1c00000300e48112042c4e41980203600702100d403100d1600058100d40c0c0210740244001003090300d500c86001141c2ca10301c8112501e401c0102100d05514091060800801d880c151116a9106d402c0110180e040240244500c201049180da46414030030781c800405070510071020010301c103007414005201b8030a00c45a400291078074000481c1e88000d401898100da0703005110120070b905100420207003624440c162030aa02c01408005442102c0340d807003a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 845096528 1250 845095278 845095379
    0x40c1539050d080105060c1b04140a0c080a0e1515130902040609060807060809070515090a0f05060d02160b042f01080a1d07170114090304 61
    0x245901d100d0302d40094441a0164019481a201400030a010038000304402280c0c40b00000130503800d003680c0d800500205121300d11031040004032010000d98450a6000080143e0141c85044c10390f40c901c1d055105858034134a00711001d0304015031440c2d140c4801205150040300c0c2060000709a12031002040030300164200c0c00d2800346c0c4401d170b02015400e040c40303520054201d040d01840791905107019903a032035000348241001c010140002401581040c0000000b502005081c921040c500007801000e68200b8401a48140040107000603c1c1c60702e01e1500c0101c40c1d0160000d400c00401d03480c681d00a40100703203e038050301c1102c189507000650303109580344250b108042c4241c40c010007007145c4030340a80440c0100d91007200c0c0048144036030b0b04a281940c1c030000c0c202020480406402ea90703007002000f101485050b1041400c0411010f680c94000c0c8100d0314604001c00102400030030300004004107a41c200299001000140210350090050f20301c5010356030700c8074000101000b1690400110310168 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 845097778 1250 845096528 845096533
    0x1d0303100f090605030303010315060b0a120c0e030607050a020a0b07020d090602010203010602030417010e01090b2e0306020708040b0304060603030e061c021b030f03040c153905 78
    0x14400c030008440703020080d00305032508110240c24a00131039034034030040c00054484000c94110001d40383d01600315802a103030601950344c4031080c052009d040c80b00320b0020342003000d0401b0b1081c144584584c4045180110041c003d040740e840b401810342d456401700c491385003180102c407841004100070425540c020340507a40280a0390390705110003405101c85412507011640108010052039174004242e900303071400c024030010200e002080d164010094180d40020650a04003005d050000e2941c88a1150103c8141041c4100e609140c5001840d0f40e1020b49040159644003400450019406450803500c9000000d1910791242000146500222401c03540141c485406108041c0c0c401c010741e00e00141512000d080c8110700220f03500c038115401c25161480d034003140d0840021203541840103e50805000d6175620140d14010051b80e600c122400d07181c6c0c000c0140000f50100c20101407041410f81a6074280740305034002407140c0c0601e00700d0002c06100c240e2512101d610034080d8622010315216000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 845099028 1250 845097778 845097811
    0x30518070f0f06050415120209031c080907081e1e030405130c080411010e040903030f050108030f0d1a0a061d0916080a0212040b071103090d061d0303 66
    0x600ca00c20000c2da03081103080010610040052490062041c862015035050400d0b1504440c1d0f10500280034030102280d1500c20041318000c01c03011084101c0703001032290b5031200541e1b61500060b035100d4952241e0902c90740300303000152440c4004a0440070003031000d402d450242150444c25601c4032181d02d048030058000050030803292500317400e0805880311849043c0408040700401030103140b4010070213010000607401d4601c607684244201c10209100030f10402c00311101e0f0900030001c2000c116101511071a11001240d1203c00000340c803a2000c00d1646940303030102420681d0080d00c0c03035420102c40d851074605c000300075070340e14410305001d44a07903a901e401200c0c58400c186441e05103000c0789805509100305101041882d200080034080e52410450490b4640550300c000a11404a0b11210944003a00344400c0080d0142c0c4036000b5802540d656008202641d2100e4482c4900710f403180d030040c510074a20000a4845c0c00158140444107a9003100440f80c0d0703c40c90440e0b108440708a09a5122203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 845100278 1250 845099028 845099039
    0x100504380406120c0c0305070f0506010803092d0d0501020d0501120506070815041505030a0c0f06051305040905010b04050c0904110408060106110f0d0801090f051501030518070f 78
    0x4000c4800000002404c0c454000e00100c0508400015540502045030001c1c000080c0500706400c0501290f000089035142c0da500c02c6030381d480ba00701a1459100c1c1020b6091600d107000c5a071038140c01d1005400c6141c00b0600201d0812050800d084400c90302e9540a1245148489503485918000c01d209426520038032200d00e416130400300b00500034428400c10398184040056245610051140251000101000005103010620305540d0005905100c1e4119800402811445a200b100c2c1d49010800801c0e072100d200751054020900308a03402008040b0400541c5415044840064081d0340001a07014042c80414140d5104035280c0f2510000000c2d00003050415100f05104c0000082501d030a01c1d00b425000340e181d040610500301000682d0100192980c400e10002840110000c03c840c11500c5483c03001d08000e000f440345101151600d4015030300d4030340500a480c415500004041c00b400742c10360040d8000c0001402c00d00c10340620384400300c1201410440340010303002c0280c0c030b00325043c0b404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 845101528 1250 845100278 845100287
    0x8030916121214040801110703080f1b160203031201051905031c021203010e010609090204060c200d0602070b0c0f0304060b0105130e0601030b100504380406 69
    0x56100d49030800c2419145004180080b852031001c8038070345003403068003080461402e03c0c1d00464000282552070510341107240da920307500408031a8400d44842c0502d0740d42c588408070141d81203d180414003407400400402c0f009140042c0748003030441e0319003a00a08590003191958021964001c0207410b0600103101a1420a5240d4105080e070962030400c0c60070400801d856001404913400c1c2080030003224140c2c10b0080c05411280ca440007059510f96955100c1d80488620078420007000c2000800c000c2400c46003402114282c074041d481301054000035555600b00c084580e00d841e00154111300490440380e80e10100420b046d03001d40f0000d6150325107810445103099000e030905240740401c10051440340071200c1a29131007a005840010f4524103400140d541d0f200b0510140d81d140c4a0090200354030014003100b90140f9808e98041007010544001d01228584115507080810400c0c4010085030071aa40c448a000881080c0b081d110b039030205001c02c8090116103a18680c03000418148040c6501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 845102778 1250 845101528 845101573
    0x13141815070c02120d0e06090a0b03070c060b04060f030f03030b130603050c0a050d15020d020d0f0b03060f0c22032108040803010e090307050d2708030301050616080309 74
    0x1130788081e00c10100741c0500604144982a1424010040410482169075442440d64001e11022103455907916203540024283c01c0544403c4a900d854030743c40f8089405e041c0700c2c5078280d075060000d81c3c44007410750310b421100c581490b10442c101503c0e031400602c240c6412480f1100c1c1d8120300302c042040c60541c5087c0c0c4c201613100c0000341c044d03041ca84c010407682d50f41104841486410007008840c0b26940300122019200d04400387c20303e1307800050b0241c0481d44d203900804003210f84150401c10300000204241e11094241d4054540c510b01c2c1c404212203203042c40003801481208000411482009507200141c0703040396009886602c10310200b0401c4c21111040c014151442d480c007a051460140d880e01d61601040c050f00340d21100110005642a41c10402c5511a5810604582a0390794080c001042291141c07003130030360034800b1410111042d04028000007580c2c1d0303190107541107a0030a001e1000c150000c1400b0a850703400a00701901003001c5c20700440c040c2c900800070b41301c0704011500c890050b185 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 845104028 1250 845102778 845102809
    0x10e070807061e03020703050c06010e060f0102150f09071e0311030303090a080f07060e16050609060403120c02060315150c19061b0e13141815070c02 66
    0xc00a000440d00348050f03844424000c060800688032000380c2011107160103980c0100425220704400030401c0c4441e0403e161003003d0840d00b0182900100004980f15907856120101e0211502c01040c04000305881480d8084142c400b1155500d0755481090424540302c41c041451078003400060090081886100c000d44070250002c52079400d245001d26034819240401910074280407035409850240a4101d41d601030304004240324068028445c1c60710303001d50701003034019200b4415000641d030910100b5160003c0c00100300381d00302803035622200e03a000d0080c82020304026207910035000503075a600c040c5000780c0c0603644880c2058407440c03d0000d42c030140f02400811030390604c80c0c01d00c2d0040009150100195040321800a103041d0301d072640c05400010704145400c8906c1d5115a00c40354040c0c92414035250482d0420500040e4035039140854510112980e9421844170000303070450030764950020040b0a0304110341501280050300f01514405891000028401921107015480c01810b160050b20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 845105278 1250 845104028 845104037
    0xc02030f060702070e0a0617030d150501090506030603030c060c12090a0b04030e010e10020a02190b0324210f06072f07090507110703020609041d010e07080706 70
    0x600e0b4001070754812040c4511111040782400099003035446400050051101007040107201c42e03117034002034030b981240d41c1e6a10300503d0100840080c00800507042c08030340040c0c48000b0139508200c184030066000070006a05880108940c90051104000301d42c4207140d40e29680340c95946140a44003917007c0034020103996130100c1e0b90a40811030126201d0340007031f41070404c0400b940c400c00040e506003014100e11544880d2110b54218125008926071406a1084038166010414401c00c400150007a00400201180500004541d482900384103008a00680404080c2c50502d000184000c2501040c50703211b10150a00b1580401c8200002c0392801d440b80080c15151408a0000b403210380e003110030315402208002100009844402549140108013081d140810b0325041c205014040c00d07584900001d0b0001c18044082c0c4000c1515000d5903401803410345002d03101001c100103881c0390190580844090841d01c00380913001d200d0b44174200c41200280100514080006051101c0c0f07600600500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 845106528 1250 845105278 845105281
    0xd02091c0305040f090c0f121503140c040203040c0303030b01140d09030f080613051b0c0d02060105030a0b0705070212030d0506130b0a0b16050f0106150c12081f060c02030f06 77
    0x54004081c14802e428510748003000c0580e423214034000e4465008114008070402c20040248510143e0b80022030328044200c444d12a400400e0000300d1004075805000e01d03049801c248000b0307100ba0040c200381d03901450244081e01c0c0b046c1c030f003e50f6a403244200e00310f45642c80000d02c0c200364012541d07412401c540d081840d034514041003c1040c81500617480321006591344005603407012280005801620518051034461a812040c00d51741c190602c0c00001510940000094a20300018050f005980c0400c3c502c1080e220220196055001070300d04a80c80032845058101c0c001003000a03000710260070401040905054080c80780c000004507242d0905800d10026084a480d040c502c01c0803a07140d590f06542e260044d030b00501c10241c40c000020014011541d0464410005410142c10307181980f403000c464108009098650401803e001010041141e0310416100d000e03d031640e5002080c0031450b41110100001d2840c8010b01c0e4105c02d0208400580d55015400c040020000c900d45500051816 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 845107778 1250 845106528 845106551
    0x10b0405010b091804150c030e0705060306030706110a17130b0c1b060c010501030f0b060604030c062d091a030f010e0c0d110a030515060d02091c0305040f09 69
    0x283c1c41d11300f801624001d00480454200120000d599030f4542c2401000c0040f4420400010302401d030100e1181602d1280307903c04119454076008807402980d00400030415107180c58000d4800d03120740714003440d140c090382100802184100d180440c44a607820074542d5101410103444903000041c0e00b02c1582c0c030400340014401c2041c0084e246031031030159081c08055038500c1001230898841c4210308c1005500b4000000100506400c01d10b144500c582c1d0448440d64540090008a002d280301c068039000284000b0803006010710034210300d4071380010030524082800417000031002d00c9062030200003503030044108602120500010300d1100882e40f414030b1824400007140820300103000e015403076100c507400704402c3c2d0a04801c858066440100600100064400254580d0850b400ea8004281040c00107500119084001c0300d9141c4010107050800b542d02000f00d0003508a1500380b0b410142540182c0c680342003402051500c9442076460558a83c20300000c890025000c0d40020b0080e07082aa50856 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 845109028 1250 845107778 845107789
    0xb0c1606141602192108071403120c0d0f02090f0f01170108060f06010f020703030f0c05030d1b180501050d02090d0b06010801170636010b0405010b09 66
    0xc001c94081c1a41c5560409015009007241024001d40c0910b1403030084100314412030500040f1052a804401c2c05100c40610340185052080000c0208500301708820000d400400101e5008116508590034400d00c4280c000502c1c20a40e001130f619040130800f800ca00c5542d005400703480440c100250300340040d50002c41d071034095800c6443c0c8600b5142c002100c46900c40ca0174643d241e860182c21012a595440225458100503603001d0b4845903010f001480310350081e000c0c0300d51034070564024000749145403011100c001403e01e004042144440e2044049001007014180305081c8013800106454400713282d651211895283c1024890301000e240205000701c1500c0c01258400c0c02c0480d0390f0103800403900f000740b1072005440e520158045501c0107001140c0c08840c4103080a8843c280583d0722a03100400d1084540c204d002c1c654070110005010301581d140c680c030307141c415072100d8020204c00840d04c11000f840c4c042c0a240350307650749907034801860140561030040080788216491705060901151 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 845110278 1250 845109028 845109047
    0xa06051e15090f06131409010b1803010b190f0512060f060d08030106030c032d0f0e0f0d080f01050d030e13050c0705060901060e040b0a0b03070b0c1606 67
    0x240e014012600c032250351a0f20010302510100140001c1e07844c4001148400c000c9074a00400c0e840340304802e0001a0781c2032004085045c3c40c400c407a03103414000e00c201c08504000c0d003022030784e40654a5100c000c090f901c500d05002031500c0c00600710f0300d825052451052a18414cd406584100303241000c0030410b40c004141140c0140b501c0c202e90300c040d603841002c6610400d11900040482d10008000a4425415807200d001c0801c255014054680000015401da03258001050000202003c40c500180d03555809040c0200b4000f00120f03e05d40d00c440340c1030038000c0d0f0240740010384c0c0040c4011200c40e076100612950048001c0440342595051101180b11019200001001d0141d03500701400c0310781d20512100e480141d44a4140100c0c501151030034542e400121084419200c5d800219078050418010881620340c188208a42ca69660b10f6604041c1030107003920014550710b521030103081e01c040c01180094140109055650a1100b014501c1d001c21502103101104d680d140501203070341c1c400d4029 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 845111528 1250 845110278 845110309
    0xc17180f0c0a06111603061a01030c12091b060306051203030906161106070513060201020f03070c0c0e091b042d0b060310031103030a171005090a06051e 67
    0x200382e288404c01c0d10703407401203c0c2180070811941040d0010410681d9040300d1912520b114a0060007501100103500740c4550021134004144400710a0340d00c6140d65010030b84060040c1880084010b0500828650f080c1c280c02c1940002d4568105200e581010203901040782c0030600117525603e060000d503030716580c02502415040340b0715107103651003501c101014040c1c0c070072107026100c40781007442c4040c14aa100c258402c80c00c4000d0600056000d006201b621036013281c65403001d141d65200902290706000c1014121100710108030041201000c1001c19445021083e0017000e041d0842c100c00000071140544542c46542810250840040d55604154040c01ca450b69042d440c000400d050024114000c042074001c0d030080100514014540c503d070040f00c1c042c6000c0400031002109042c1c50380700c3c401d07182020a18020f1092160441d162150350700840340c0c40001004c03510356000600414003583d040088079150f02051001c1d02d020441280c0304401e0094031003070010004089110320355021800d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 845112778 1250 845111528 845111537
    0xc012003070c030c12020a020901091e24080102090915010c020d1e0c03020909010b061b10050f0f06040e0c010804060b0a0e0405011407120c17180f0c0a06 68
    0x304400c144c0500c460201d211350100d224954211108002940d61070325007000d0b8481c11445000007917202040c41007011003804542d4072980508410381c0100a0300034092032660240122010141e0800c0f10625840a0010200007503a101c0b144001c01c030048802a00b1580d45904090008405a8101e004191800e40c142c0740782401e2010f43c1000800c100103410726200f4001400b035404100080d080c4031b042502c0c0300311003085203519120750160803101c00e442910f400c5142000004180301000e0b5149070701501c480101c90031030307800da540e0000345c4a054507417070b059810381014407100703080070203505600400c295030800501840f210003503a2401c50b0110141486448000701d401e000d829003203000e490300060a0591903a07070380d40202200c500c04030303030556040d482e021003400d280e0360743c06045010300000d9541c82c8980c4240c4801038001c05c601281101800240510032250200550825101e04110240e407a8541144900141808034401e001c0300c1e15040411440c481e42d032455035030010303101c041c0341 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 845114028 1250 845112778 845112797
    0x1b06090d030815060a03060e100f05090a0e030a0306180b03030d0902030a140a0201020616020c040e011518111608030c040b0d0c030b09270c150c01200307 68
    0x242e0014403c141c15129070422400642002442e4142e08040c5c22525102c24003207290380c41001d41d0a07500524000c00844010062040085240011201d50002d40540001450306074051580345540d121911130008680c48800c00c01454260b2600c8006460031340340c00b400000e502000283d100e20aa41c03025542c941d841d8002e5095480c10060341c0c0000e980400440090420085100d669880c0842c04074018842c540c0007805070010443c900408803401c1d001031044105900802001d0401241c0300c110565843c10b0382c24400f48030900000c018601c02c015840380b65010080c01c815140064007070140898100190526482c0c1150048100e5070020309490b02c948907103208140c688181c4d40401901000803070512461511544210207076001a207040000d42031650071b01240550072200d528404d880120302a83e280300c2ca00f000010a02c42c10151808401c06031300050003240c10451035074100d003010030703010382480e800d01c41c1051502d40030300022440c1d03441d101c7c90102440005c03c90810447c3c00227 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 845115278 1250 845114028 845114041
    0x623070308191401080106050a1502060c180913020306070329011e0e04060f06050d150f030b09100603120e0d020405040b0610030c022a060406021b06090d0308 70
    0x707008000c10b07aa000d4000c41256920b81034036011f8215806103c0c4544400d000000701c110700c174203414041c24481c0c1c0161082d903681da01c210580d60400d500e03044488118a40313860056484840c1c59100707940c040481c0351403803c1801807602d0b246000305504141441d1003c4d14540c40c3c40380d00040c4103040d00100f0b44002c1c2d2241d50040b01c180c05030500e000d24000000c0e0000c620250071142107421580156010041165112503100302101148116404607904010080020440d03411030940140120229070b020f40d540c1003041c07035006107a8002d941e0207424506101d0302c00028856003802c0d40402e4401d00c010b43c2143c56080d113644042c084503081c402e8101c0690344640340c080341a00d456400a01c2004207103454182044030079400c860403407048808452900100d4060b124100440d0b40035402400d01103c0002c019407240712840c034810720300398500395640c200c1c0d44180040c070103440c059001c0c01841042a42e0781c0e409032115885103200701da0900840000d40c8410500100680d0503185c040d03680e41350b45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 845116528 1250 845115278 845115281
    0x50411030705031905030f12011706040c03230d0507050f0a050730120320031b090d030507020a1a030a180507090c0e0f0f01050304021306062307030819 67
    0x4021f850242170200d41603128820f24807009049034030100c0f1000e20b900c2c45482c000e48624003101d00034025403901400748046108008403031051843c500c01940c071155028481842d00700071042d0080092000030700e102c10000c0600c450541c00d0040d000401500340550364058850b21507005032001141c040c2c1d807181d182c0540c50320300764440209007a803c42e845002d040c000c1c6400300403c1075030042420080c810703610440e098244241544007040d03407030541e11440c41d02103228030f204610615039032003030043e00d0290ba94948040900c03807094540036a140468414014441010342c440135001000e10002c9010300c000c80100c0b40d00c141894000605c5002070580070f080c4100c1880080c029214000c804181480b59a001d9081d034082074640d01c40300307603101081000c0e00c0200c120147d004240340a07250721950003103000d90380191005201507107401c0729002080444181b80c0c000390024902c404180020421012002c10f01917403031843c01c0c64080d00341c401030310078400541503103000d4004c00400b488c2d40089 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 845117778 1250 845116528 845116537
    0x30201031e060b0a110313060f090902030c0301080d050711041d0d0c1515030b04020d1416061d100e0301060303030f0b0402190806130c0305041103070503190503 71
    0x2000802c181a02c0b181e6541850b00400309600105401051165501e0400410ba0f01d00c507003065803624903242050401c07140c00501d410404144009000702241c0707030034680051882010002071850300e946c50100e0061801962410380c00500c80c007000080080b40e940f100820110700d041c3c0d030210300302d46641000070550030340d008015941e000e200c2000781400d601c020170101c9203024142e14038000c1604079681c3c04881b81c072247e892070410b80e02c000b000041c1600204076401800245400c2154016440d01540360802a100700c2040d080041016200306080b000c0ca0003914003803600028400c2d0340901c40c0015408031a03010300c13644070f040440301420320a01500c0d8040a000d0000c0c4001540c07031038050090503010000e01415406c00303880001a0420388262482130741410000303151034540c80b200b0b030307807402c2c6c084c0503607810031120b20328000304648501805141c130303929aa000a0920b07160034541800106090180d10903007000700f04221a903000102849002070015100500c9192454624554841c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 845119028 1250 845117778 845117831
    0x1407081018090c140609090a060f080d1707170a0902100c0308010815040b07110304030b0603011a130c17010f080609060412050304060b04140a060e040c03020103 71
    0x107907201c2400403000580088040a100e0320003240c0c4280c5810112801c028501c038983d40200041c403e408042c50800c4000d5080040c000000403d6500c3d40e0b0088040a000c2d040103c80764083c01401480f01d500c040c83c0203081c1c0c1c6102103940e0724105481d0041040c100030452030b403460004c001103460074035980e00c00001070341d0080c09600d044421000141040100d24020744c00b164440c0b000003418940401c11402d4403010440480907561140e40b001d200c24000f904c0c034010030850000030b016200c1c3c200000c001a42c06070011070094603200c02010300350350640e000000a083c0700c1a40074040c5c1c881d000c0f00721002c5442080810712802c0410b003210b120703040e1001ba40030040700000000301c20100325600c005407607885007912115030f6030580160b5101c1059400a2070041d0381580014214420009540c1251145401003035543c040030000301650504003c40e05a00400b0341401280e003554803991004082902e8030082c40d02d400e03220040d032801148400382c1455280c1c2256031500303140142000400c01d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 845120278 1250 845119028 845119049
    0x120c0903150b0a06031d150406051803040305061503030a0e011407060614010e0d0c06180e09010c0e120c0d1e0f0b0c04080c13110d02190314070810 65
    0x84c3e4901008010b02602c01d807603000300040c50b40d51403450902144403c20100e1000703006d41240c07140d6446a0040c1001800e00f14101070070040072030304110071320041c0000c0d4003a00007001c050030240710001c0301031381e0442a14402c0c0c2c020040700c9a900e421107000060a5000d003010f11803408034040b030001ca03108840005042528041000c0380000704a5541103481e64207907203034141231070480d040c029041c14002d005010610382031410090070388100c44030550340c0c1c1c2d11003517560441ea9940011402210540f0752904694460742e204005680c050701c2011441c20441d54540301144808410780ca41c2450800d49004064064070304040c0601030024040780b0089001c0c10900500742d0801180c14100c10f102180c4101da40404941c0590f4500b013030380c09445800016000f418244801c00414006020005130303040c0c0c49000c130003a14a01c110240489518001002d6500d481d025600d004101518600c0c90916207010f20482d0360041e903000c050b03030168460401140316203038600c07032224462455200e040000b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 845121528 1250 845120278 845120299
    0x18070212070f15020a05030103060906112107022a0a03240c08010e0109090501140a0c02160807060503180d12051b0a050a091a03040201120c0903150b 66
    0x12480c4404102c0314010381e1a0004100e028001d030040c4d100c1c8a141c900020b4040c001400030540ca0740c08080c03810301c6948000f8408030b200d001c0f04a41c1d0030071090000e100406101e103042406031409450340c480d80700d10140101e1400c0a0700e90304240c11a40c0248034a101c06104500301d40c0314294440c0c05960800262140d00005080c000c0301240f144059448913810004000e18050007510400c0c143d46c0c03042002c0e001c6030708140860000307046412080c0e40543d00d900206031502c0800081d0f81c043c4403104c401003298480d05102034035002c14121402181010000100034540c0045445801d551052074007950301c0d1501040f442545514541e6800c4a014103a0740e00340342500042a410030800c210028407059031041c4c0301040e0060440345481c41c926041081514151180f401001c0040690401da0f00ea00e44881400700844502c8460003208100001800250760700801428101040d045081c4004c15100100400c00529480002d00d09214000410100003054103c031600840103803400490 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 845122778 1250 845121528 845121533
    0xe0103120c0b0712090c080304060219021e0301140406020309070b07050c0d020a1e0f062c1504091a10090b030601030908120106110a0221010212010b1c0b1807021207 73
    0x8d0358040d22448001d4800d10f03000820726014800003900b0107400a11400d400c040300103601d1400801c0307115441e455566800d451505400320b891180c0070300d00075400141c03685000b442c0a440d044c0c0903005a01241010b2220078001034000808940c615420740305a42013880510200d140320182d40c00000c202c01c01d22000e4282540da41d044081129802d80c602601e250b600c440507581030540c40d01c05181e940702c50180d001c800840d40a4450319100c05801c0c04500070b81080301c14200c1c2c120344c210030700c05525050403c021005220281010324000c55601c018003040700c0d009410305050344240d022055000c4006811613002c1c1d403001d1183c6402c24034550340d60900c2e00c4009101e0400b4010803000c41c4040c00c000301c122a000506130940d03540501721000c0781e854240030600140060841142940d000c0002003404859003200500a00c03030502010b45892501c1c901d190389020140c05446181c0c9047d0001c0d40303d54418400c180049000845040700c1d0b260500224205042036050f5504200002201001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 845124028 1250 845122778 845122783
    0x10b0906070813120807020319030f030b0a1701151d15130c0c210e010309050c100513091406010c0212010e1e010513020616020a0e0103120c0b0712090c08 68
    0x31948202c0540d02c070200e201281c141141d40c003000190000d0940cbc5403503405640280c2c0600c0b01084020100b4111659544404030b042c1c2c051500590f003651039044481001c0407030b80e8800080c01624080c0c9010f0700d516407900010b0302009140398078020a842401d161900c442d084000e14018002091005104081c0084d11120038020100c030090000c0c2c0e1740c0c507082d254076181d41c901005566900d5071140c2d03450340110f015040e444420b07640c6021b00702c648451940d82c5941180b10545e141c45040d101c10040c0d40d540035046a543c00814a0fa041410045961846103a02c540c80142400c007882404028000b05241c091440000c441c2503181031a640b402c08000255180490a00d071038003180321f20391085041c2610070036143d040041400100d407000514002000c0c000d1404510107a00218040350005159100c40f503211188010089006100740701201015910601c10350030f008141c02020359400703084c2c100003002c250400a0441c900c44d5000a160030141c03a8540210b01000707034a4544da42141c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 845125278 1250 845124028 845124037
    0x8040b03090d020a0203060a0b011412160e100309030509030105071d012d1214100509040b0106050903010b030102030103080c250b0d1d0a030305010b09060708131208 73
    0xc04610946041842440c800031304080380c540e002d13000c0c100d661504894107014000c401e207503a050018900580030300d00130f440080c1200303031044401072285041040f0388500c0855050191410084903c0c1c00c0c8002c2c1d00d5094140007007818510b8001415545402c0850f0a4007540d048141d0550911081c0321a42d035201404121806a20b0341c00c1030800c005200651720b0200030602c150040f50989000c500d5610618031000d1500e07002d0400c88803042103c1245821243d003098040700d1a84000103028142040a004001a003820384103101a410140c452103100841480381c981000170019012640f0f84003034020481d0a00d0160003507440b035840b480d0881d0180c10211007440d0078442d004501c80c100c3d01a051031408002080e00f104580c50910401650661000c80503180c0c1c0b41c1c43d43c0310280d5070342101c0519070140c001d039030140001d0000c0341b40c000c003a614180d00c500311a81051020012030f5546104980c64240e114810b95511907800b11031ba80c4018156003c0c59040c140c501026060001c41c40082 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 845126528 1250 845125278 845125291
    0x1120b06060f070b0a0501170601050907020f101a0d050c040f02090303120f0c090619170103080310060513170a0807030c050f190602070c05122a01050f0706060308040b03 75
    0xe02190303888e4030702c0009039103080681444641c40311004211904000701c07265082601841070350303001100e1203462850301c0c1203a101c0c003200a5403000754100100080c02e4120304418215640c41c1600c0d500d444a6607039501000d800e5106650750300c0f0120119004d6070481d070602c080038003929203030300086401c0c08031a03608039500050354a80e40001465500500111a540c0e040208001e0400b03500ea640520019800704041060002001c250b201d601b80c4100b04500843c40f0b008040d9880c64045c2c9117103500c0b070003580030009205080c840a44441406509203082d117035001407200c240041e42a030399117400b021400c00740100394002108002d040e4448801e0004078000c4040314010310221000c19581d4050300d4001864110402a00c000034075640c0051000500480c4841030b0341352a480040d0030300200600d0811150321004184814210b800b28a01c000702940f04000300202008001a101703128035160700140780310004600082158a50100002d947c201e1066a246c40c0c8801a1030010391054810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 845127778 1250 845126528 845126531
    0x71e0e0906040209100c080403020402030c07031b020102210409020301081e0309030703030c021201051501030f062603220e010918121715010f0801120b06060f070b0a 73
    0xd8280c2424002c0310500800038104c2e01719203400b0701007196001010042125203800c00c0000101580c1c842c00954000c414080707500c2c0e603030b81041c03801809a00703542111880d001e10f90200c02000d82e8002c944020401a011054140e030082d1040004051103140c0000b02e04510101c00850b1841e00000e224825030555503039101d542c1e504a04c261f1790b0b40550240c89505602003442440081d1050460750a42403028005110780440039152a080d54030890720100386085140c00c101c3e50b903a02d4041c0e8615140c0300703081000021b041c0346814100c8800e004d1a100c804480c410702c10aa004104100d4050140c1d0281040049040c00c0044c280d00005101c0d006044100c84004119000b5910a0916003145140030011441c110b03580d00000301c0d4030007500c009000b2760140820307004040541d410303c0303006050307904c11400c003000b00094054940c0c00d15070320400c80038100520044802007d00c5075000e4000807204000d90b144c000080a6110b91640403000c44070100d520420044050b0006e0b005408441c1e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 845129028 1250 845127778 845127781
    0x30a1101020c090f0a0f020d140601180608040f0f0b0f1e0124030b100809010c050f03070c0c031e150209030c090901060b0c030a0809010b060d05071e0e09 68
    0x402050610969040d006804c805020800e0459960310200000e1503002c8058100f2401405c0c1c0000c448400c0d1000350605d041c402044081d61340801c400340043e1025041420392420320400414116009000810001510b280741042c00640740e4015001c1d980440d003007046281c00010490100e90940e6a96440c1145a0980c008403070b0343d0b080701e810703105049140d069a5010311480014071042801900a02d507032584d03400b46984030700100c840e130345035940c844010030300b0001016400c581e0940341880402c030050164441d2014880c003180c0d004040c0d803a100d07034078010174282506000f026601c000c242c806881c1000103404204007000380864000e810b454043c00c002c178211001c2c0c1c8610401190716030003600e0504503070b2406a08071600a4450b03000000e165440e40090b0141d9846007010908a034000f060482d000c6501180d00c80d84611034000900c03881c0da501d0007252081c0075138105000c07004c0c0c6440008000307030f100303003180c031844141c44d0382c455400042e5103009800c1f801203080450050701000d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 845130278 1250 845129028 845129053
    0x30c2a030615051825020a0212030405102003030106032a141b010f0209131503110f040c0e03070e09030f0306310506010833030a110102 60
    0x6142c10308a52000c0c010424002807400912014800140025241001d10418083e07415240070507940411940d0010420500e0390300401c880c50031040b890000d160300810090003141c03202507010351205070344e040c200403641a1100384c0a9400308500c1c2908a40300c040700005000d0383c190811440d10302400380e9131a04800f5003641c0680b0f841c0a0100101003055404500c0340310210900a004410715550f0605070590b009021a00f550540c0441401d180e4000c10a64850301d00a4881c6003080003080080000c0702241d660955646150303c80a0514410072121010703d0310ba45462440740d42005100b042003140030305010b40381c3c08403181068007034410990b001c03a10340104180c02e4000d200701d100a50600c065010004c100d80d000802c860740162100400e82d01c1111524100d02049943c0d000781c00300900440c007004201e8030001d1080d030401804100348101c03d640c0b080b04109400c40d4807440f4420503074100411801140400243d134241c1302d01c0300e41e5800c1c080303023031125013282009a0030381c2c04003032030312 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 845131528 1250 845130278 845130311
    0xe0916050f0a23090103150509060f0411040e06280204080c09071808010f051510081b0c0303101a0a0c03020a080417010501080316030c2a0306 63
    0x9100c00c81c1c0040d212002440819180111403010340b048103c841e2a2a04640118120712401e03401118041c1c80c44070000c851103c01e0081c103038071400305001040d5130704c0d00d0611481743c50780141c005071501c1e102c890328013480d840356003011584440080440c0e249007081d81c0c012041628030b031072800c1c2201c1c481c042110500d0903070003103038101c5040328010660420040100183c0d0440a0b20841c01c0c44503030040d880d526000c11362203400410140c400080d104888128a034241d130002072a80f0910003850151041980d10b2250040309885c49241c40103069071007080c104080700c7c1c0c90041400c218008214020040000002103200d03440d100319940a180c3d4070307841c0054509220070708840890781404181001880303001d9489150340680b049880311855034841c0481903000703401401d4843c46104003410b424200340103090042c40c901c002180385c842c0f9050001000241e2440081c1004682220182480310343c5000d20105a2221950005446450f1000c80c40c086188812288035041030324200c01103554 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 845132778 1250 845131528 845131549
    0x1211010f020331020301050708070915080a020d0e071401120209011413050607060912020c010801090c0201060305030d0608061b0414030f0a031112071a09070e091605 73
    0x2501001c0400c01c06505183d291101418a18020b0b050074018010160350309000c0e1601640031174a90315030f42d04149400800141f0755410200708a0500840c0843c0c581c1e1201f11650b20010110005031640381c01411080540050707101240c45200d40355021400c80f2001c030183c0030710300c4242ca80c0d15070782000d8000b4506900440303500c2030200e04d0b400c03100110803e02c0c200614140204d86083c3ea1865190000511240c011903001e031441c2d60707558100020001440d220484030b820500040240c0c102e181c0008007010414003840001d2a201d01c00703a1515030007500070390061f5034884182c0f40c0700c1082103c800c1c02481d20744100d100e28442c140200b180302c81034403082044042551903045c64a0b041030303005521a071400c800c05405114410001a003440e080c80340706440c0d0b110b5603800c80e50b0a80381480d1403030f01c980702c03400d06a100f0042003103000241f85204040d84101c503c0685540700d503294a5410304010ba540e0100390300078110350030004161000b18200c1c2c06a2001000c0e408120385450501152400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 845134028 1250 845132778 845132791
    0x80603011d0319050403060c050d050609090c01111504060509011b090306200c07081c0c0221060c0d110408060f0408130303110d02010507090e06030106031211010f0203 74
    0x20810010f1852800404522031240c1942041c038a055070303965403601140e01c100ca82e180080c0c07010540030400e50607402455000841207500306040d041c1880b042d03440e155205025414402407004504100d401480f0018001d00c109042ca4a24917042c24010068502101c0354a010b51074112219416001c2d40c2618000d400c41c2e58600f0003050031569258001d01c040d0319050b801d50b2140c00c0250f0b2201d0070200a00c98944401d024100c0245051151490300c5000e550611103215080e18441c9000e81c408104282150110307a40390310400781403011800400750440514043c02980708004820703034914001d101d00d4006030410801300c100d80011440c24003550040b60050340003400410303940c0350074500e0030303402c2405244481d207014620041310a01e986154011400715003c0e20f00b601500c4000d100d0800441801e0009000b01e01d08200c00415905150007a03c1402c3c2d07200b00841d6a5440961016004c3e5a001c03c410b8400750750030314054000310394107004002030343c203200c074000300e400c00341c02074034010744 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 845135278 1250 845134028 845134033
    0xa02040b1909092f01030c03020a170a0e162108040b0c0705040f0609050114030a02010503040512070c0311030a0c18090602030a0b0a12020d020108070e040903080603011d 75
    0x2410009000040c0c18007440a40d070003240340c203138030103083d10f220010090451507041615140c0440400901560000c221040602d48140503804103590001d2030042c0f61502d03015003107100e6484010031001010340e84000d407003a10030544c1503a1461001511407099982c01c039003c1018012140460780c0b28105404000c10001080c441085503000080140c1111080401074800254540c0d0104003100c011125000d01d0a40b2102c04202c1540103205880c05020410303d2504160051400310703603100ca45100080c1044000030010307041c000103105403240c0d0306071818015550500b42c10b04410203125400161105c4c20b8810800c681d501e0001030034042e1a9205e11000b03441494201d441100400483c00020201d45903c44000020310f64070007144110078a41c0000340d030071a0306050001d00340007a001801018105001c5d40003580e118501c80e800e141c0e091a2622103965507060441f4406444050180c00a040400788801c16030403c074180e210b0701082c0c00802860945454000380348109a101c000390740c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 845136528 1250 845135278 845135329
    0xa061d07051917070305070f14070807020120010518010b0112051b030405030a11031e070c05041806050a020423010201060308120405160e070c02040e0307050a02040b 73
    0xc072603040b04054085082c402ca0070803000c0c01c80c0f00d951030101c403500c001968540401a50f40d8102c2019401e4000501d0080b0040c0c0803001e01d181c80744242c1030044c115040104150085a02c1610490070642d094507100481d00d9520126601030315003035607042c401540b110b9024091030700500c2800300380041651505400041079000c60000c00010b403100d407034000644d0300760560b080c001e40298040c5120300001c540c0c41c003503494001e0000c8280e8102c03050384d810800c100d04c10000d04d00b40f07000080b01c8400034550703030310f82c0e5151800d0035102a904c001c0e00300d0f040c40400100e150300310585110260140380d041c01a030380c4a203a0641244640d02810005400c0c0000b451031403a800d030130034071001606000000d0650348984036844190005107040b403140c1100c2080100300701003070102c0d801c1120b50500c1b02400340c0c1003800c05900160f00070716000c00c00101141c11800d6580d2500079107214210001641d0fa034025908119888543ca014181d02a50501c15000b0850802003c4c03048009501c40420085 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 845137778 1250 845136528 845136547
    0x28091a0d021e03030405041104090605090702060106181d0a140613021c0e070f0b0708030a152408090705090402010f0e1c050d09051011070308030a061d0705 69
    0x41402c0c0b0601d2030303098032003400b012410740c03103500c0703203005100c003a040c07040e112840c0484100c00e0b2000d58000e18007881780713401400402900000c0b040c3c1940ca09003003030010400040c0004500c000f250b40101c0150000b41d4644030407082e02e81c0c1281c00b403086500c09004207103160760a81c840080540d0b00365041501c0c0d5084150080d01503001d001040524058007914502001008040d103a950104001c20b40200700104580428041d11000030300540e0312003030400a0580720b11180d404001c001c8041c0c07a40300c1e2414128891481c410001071326129071180740c1040b0b0010400c980304442403d11000c030740640082101291300141100c125403008005e00b03451b42e60f0b5401140c1041c1d2280012060008145c1075500c0359990380447c801951240d00308490051060801500d40001c4140c10011f21115050600040c0c45a44d911b0f544041c480c2480a030440822a005107003001c260300c05041050040144031021007207400102c100c0d01d0380d03003820b0041800d01c85441c5040400740c034010085141004000203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 845139028 1250 845137778 845137819
    0x190c110309130b090c0405030d0201090807060c1808011b0201061203030b0d0c1d0c12010608101d04050c0a0602071814090607030c110c28091a0d02 65
    0x241c0c2c1503038032001c83c10380e40312008160121400d5480c0000b0900106081c0000c0c20100401400c0420138402031040095544449544e03100f4414090039480e182c00172240900c0c05803e43c58031003c2034202d50034585661b6420b5900a11039400c1140300391402c03150131580d803481401410280e4280c510804d00e0544555025001400f00340c0c15103800c0f003650014880442c41d490b0812000380b000e5030401d2034881c03103003d5036405103100812810028105102c20402002c03d014650705580303103420000c032030b521903680182094500741e1101140000d500c90750b942d00722803019940d0003940700f1001ca8141d185103108100c80321020b07002e10801640003082c100140307c800001c204591800000c001656a2000300b04503c1003000c403240c1000750700050510404650600c107070041000c0d285801c071208180006141d88803a400d403070031881088c2e1041480c4c94200c3c021010181d002e112a4641d400075a03401c01000504081032644840f5014481139048030300788a8199000154008c103c100c1c9961a1280140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 845140278 1250 845139028 845139049
    0x3705030105010b0c03040b0d09140d030c03020408032b02180a0902070302102a02011e0615031d0a0507080d030606050313050a1707021c0305161a190c110309 69
    0x602c0f5503103560300c07040401d04103400007030000c403801c1c0a400218541480034083e41c0c800001c020415204100070000547102005845802090082c024441100025900000f80200c044000611710014904009018194800008a2090f03580b842610303501c03e0720404900402001a016800c40d00c10503115020035441603645a8561407002003060f101403100b001c0b00c64070301d021400340c0c0d51449841c1c049800030f0004400c11103020028402c0600f40365800d2a0b01040c2a400030502d500c409810000040a031241c030000850002240c0b41d1442030704185036207080d40c0c0300d0400103006106c0d82c8030685101e80200c2090300c004c5d8480600c0c640700c0b4049101181d0021038165005e0140c032401e140020b99a00f030810000c44d11072100c07074480c040f13030040150714074546000003010318182240c580000c0d00b1405842c1c200c0341e004404e001501481c20100c00040e41642c007100c0d800c1c0b03040c00b0401c00d00d80a6049000c0e02e0001d080811206118500c19149140c0d002584c00c01a8811b10603c503d501d4092401c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 845141528 1250 845140278 845140297
    0x80a23070312170705121f050d0629100c051903050c0d020106080c03010629070c091416231b24010b0304023705030105010b0c03040b 59
    0x62100b002c0d0601e074825110320a65014000607000500c07101ca812400c40300c2e981007c14903c031844050500e465061610002e4450b0f103002e003460a0085013840615404680649405080600c00200044007400c229420030541c80c492145024414501845041d860320300a038001c3c0184150300c00c250380d6001c019125441281080707801c001c0d42c50451000c0c000c0d02c2480c2c21a400110f211414030b0700300d90922409480b041d029a03d014020080e90035400c82c198400d080b00c0078846044011100802500d20840d44c010b0b0a070450480d0010b0b8603103007540300941402030034401c114070fa00c3d00c00c084407560f0100000320000503401c0c08008114403540c84c041d000040d48800e81840c00585040240c03e000f98104018038503048241c000303040c260504c410045d400003c0380d2078185981040c040000501003e00040d0250120307005001648000c408a4030b100088236024a44275160000d242101803418001e042c003950030314000040b11303c0682c094031204070448010310300b03040c100318419400740c001040c503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 845142778 1250 845141528 845141537
    0x3010302040906020c16030b0a09050309090702010204050d0807110618011206080f0708070b030603031803010b06070f12050316051806120906071e05030a0609020301080a23070312 79
    0x22003080204000c80c1d441c19411b500c03145c11151840c208040e410310021f02c106202d90805d445040041d0b804000c0b102d002d0750840f1840c4681c0c80e07061040b402402550403094011408401e4602401084405841810300c20410303c0b4014100e502480307424010601400035080301404410020340c0215800c011203050a14000386241d9100c000314034000c044044030220341c00621040c488038070305010328400340481005152a5082c24004a9603078031843e00528030100405022042c039a81c00e402120701100000c1056803544490b042c4040110036480086500c50300b9500b0401d040741c02101507a102d464401920548524050025a025030000803802c92105000e125002c2c1d0355204000340c4040c40400841200170315281241c02d1070180f014101109101c42c0d014403a010b4001710403809801003c40ca441e039101d0f103031b00f40840b0241400360000840940003000108224400198100341c5a00656041b0186000302c28541000e0003400d02c007400300d41020005201254400f001210a0082c0b440c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 845143884 1106 845142778 845142787
    0xf1818051008070501120905010c0e100801050105030117010b06040602031b160902280e0112090b0f0c07080a091a0a0f11010209060c0c01080f0c0301030204090602 72
    0x9013904000341c1004220212030507400c801d82c0c2c20b038060000d0128030701190010b0314507140c50009d0380c000c620090310708031080d1103100c074141260010384070700f481c503403c001c00c000c055150b1007010240e540d03e6032501c03030103074498800402c021f14141d4044c6480d40304007510711a5600c800101800590301c2160115011110103052108498410200590301c04080111101c034051654484010316a510005540c070703600a0000740413034009903611914480140c1c4000d0403201c000b20050281c8c810500016018021441d02540146000f80200d080181c0759541d1100f0340c5c00880c0303010020310075400070031071285c0c1820519510002800454145402e00000400030102c40540d001085030840c0d117082c002c9003e50454a52140c00b4100325a901c13000440c0c240d6410505c0300301d0340090020000912110400490240904e484480e8a0302c0d5034603540800c8040c2001260030303591541d0030070 = true := by decide +kernel

theorem cover : BRFrame.Cov 844964028 845143884 := by
  have h0 := BRFrame.cov_init 844964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 844964028 ≤ n) (h2 : n < 845143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
