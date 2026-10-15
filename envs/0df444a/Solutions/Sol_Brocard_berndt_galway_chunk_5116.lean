-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:47:45.691009+00:00
-- url     : https://prove2.me/submissions/80c8fcf5-679d-49f7-9a20-c547eabadda2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 919964028 ≤ n < 920143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 919965278 1250 919964028 919964039
    0x1608030a15060f140c03030103080d0b0d120f02070b041e0b07030f1412040b040308070314190f110c071d0109021c0c03270c06030509030403050307030207 68
    0x20a5080d18580719841e10075142c58008040d0684014020080801c14010b280a010304421012100c95800300720450f03a4070b41c0d490034055081d40041414035201400c28a41c21107d00d0400c0300d20b04040d4114400f00710044425106844c030071100d141c10819800383c0c0800042421240018000400000d2161882800e050b140b501f02ea015030b422403402c540f07040c480d0300040f1364042d001442c14880340c18410109600014012014000e19000820950421080200704030307401e01814011442070b1106095a20351150036002e5030500c525003d10727580e417070001a00160071110314401992100300c001645041e02c02841099940c00380b41500c3c1a403001642c4500e04100304103d80052503111400203d00da0005140035a072074062140004003070b004034012034040c5002061404566a040040002084400d00500a800c1c42d45281c2d40034903401401206810100440815455005034803813101400c102c0154001c00000e0529590f500c020721000c0000381c0100002d215250003034000f440240e2614 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 919966528 1250 919965278 919965281
    0x40e0c0112050c0a030905030705031908091c1d12030702210714040b060a120501060509011e0c05160e13150506190f0e1f06030506061608030a 63
    0x420300c403003040c2e20701001c02c180d1030300410540310349100030b01c2d01207a254000d003050744c91400740d80c1002e4001cbc08009480b961040c98080040700900c4a511b840783e1b203507101603013203071104140d55806040c54001c0108519080c07003071a07811062000981d9007401206080c0209401c528500c0020449900006504003540b80c9148034140074200603007407801c2428a0503800e921030000f0300c195402c80d40451010151941c80d034108218180c0c7c0a8105601d0345644200100080800d2030384422252800d00041441c622403800ca840c031041c1038441043c0085025020355518211802c01820030102600003000100140804c11215810a8003035803158101110000003000203030400d0980fa05006070800000e15103502c455049400c1140020560346810106d103207410326107420011100d102c000801d0108042d800c0034252a48617600760420303070321000400000510303080358602e140c10b0300804019061080d0850780c5e010074040c01c1c0c1c03401c10f0007000b000d194121100744112900c003404010024052480d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 919967778 1250 919966528 919966547
    0xc0106080114130c140303070b0a05040606050f0105070209040f0206030705220e0115110102040b0a02010501140f1306090f020306040b031c1101020705070314190510020a0e040e0c01 80
    0x410030200e088000e41d144d2108403840e00c5035118070400034411640550b000e0003aa40c0c1181c000c0e110018900c0c1a6807414014071003200c048424603d0620b011900c0d040400c40600d8021041e116645000c45a80801000010003001141e0700f107803000f4001d005884200265018000313545031b0700c1c1c0f1400c02c146490180307910300100c034025015404003003101c00742c80110b0344d046407460000412000d44000c4100d881c0f2407251001840c5600000d0b000031440c40e650000c02c9002000d074001c01050340ca40c020281c40151301903401ea4000645450070100d4a810b0f000f85000503802e64000900d980e0303800c802c1c0306036588600014090f40d40441003003100d0409000700210300500301e002d06100032a00215202c0d18035899895001c0106003001403500241c03d50440706210380150886034240d54902d04900343c0c44005a820f00c9034006c100526500345000350703800c04042e5220000d002c01c510307400326100094000301c02007810881c400c0c1602c00c9644072442005071501c1e40e01b0103011405004000540000c20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 919969028 1250 919967778 919967791
    0xf0303091809020609010e06120f010620060c090612041104050c120c30010f0b0a05120709090e1c183302010e0d030209060a03110c0106080114 63
    0x2002c5050005039542c1d01121988442428080800080c40c0c011940728061a0f0300018103002d0407043c04140882104064102c07416991164200310039920003c0ea02c44203101081100c2d401072001c504440100e9018000a401c058000f0f401c02e0020b5841c4d403500396040e07405503040880c205440003141860f018040e4000c2081c0e00781c0c4e00e00000c0b0214038841c0c1000824202141d54007040071110400a0144a803901506d841d032010350032010704440801090a1141080d40440c15000040038441c510543d18040180e440c2d40f4200b106070315842c00420f000a10300f03010000303942c01c0802c582550b4400c103d0042880790040c000b0326070011000348041c18110442090001c04440c651080c0800c80406007524036098148818030072a40120b03900c4000a021050303640014090320612640c1540b1906000f00c914084412100c0500030540491142201c0c441d0803803010402076050500036000710320419910181c0d640b82002c40244542104c4503600002c400782d440e25101d0320b8555084008030b800c00d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 919970278 1250 919969028 919969031
    0x30106020c13022b0c02070f1203032c0d080c1b01090506070c0c0e100b0a021e0c0f1c03080714030a0c2709090c0f03030918 55
    0x14101480030795900c6458070914421078030790556603603242c42501a02e60381c09500c14201c9203903580103103243c035156224500d41c041c6860305506a001510020700041103034580d554854606040818035160300084c04c00607801e040c1c48621103a0b441c622606081c68a1105480201000c0040742c0e440f4145004000c4003070030092443c06101d04044888110f490104040041084150b00702c0030060150004402c00b030858001c941c03c120060b0303002038010140b184100f00c0034004503142d041d00c3d81b04480c180d82c81001c0d5400400140080d00541c0024424107500d4012626020100c504c4034042103d82c202000094200075591105803c0c88113941c8442001210300c06110040e0100f5840c6c46107a006c4050100f040710008074201c1c40c000d41c0d14035406140750700c6146d504e1404e886d45070b01800003140c3c0078000964204154a0100e02c190700411824100c030340f20604070b45404210006009640000d0b07942c3c01440c440007440c4903003100028025442030b10f610900a1500c0445c580649201e000441461b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 919971528 1250 919970278 919970281
    0xc090602100e010e0307061506020f0c01030c0309051e102a170108010b01260f071101020408011a0121051005031617070f0e1e13050d0503 61
    0x6a402060305915011451000104002003080890140122018180707660000041040501405800c1004c044644070405001c1d03664500d8200e030381d8510440c4803919500002c505025641c0719401030503c0c081c55240c08100a60140c50300c5042100d130701603110f002c0d00c42e00d84807a10385000303004004246108180070000d00107100081c4006800c0759603942c0b04507103d1210748049502844046080c400204510080e82da1205402d50080c150b103014640818220312002610a4291241440f10000ca80b45001c0c15250700800c8083c544001d41060184408110000c4660a091005e4030040601d440089031315030002c03880d25201e0340b00304030050402548100b0404c1e194a021050f03500d5541c04507001449907a14210310f441003125402540c0c0c580211100901c00480c0d80d68400166040c0e45036403002c80c07110232f00090351505184907824002106020820656605a044a40c4490381d0308800d060390052540e8031800c150100e400c090500e2060900c1820301100b0007104003a240c9034201523186 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 919972778 1250 919971528 919971539
    0x60c180604230f040c09050d080c12041805060117272b090b180d0b040308061f050d02160c0303020601050d0b0109090f02130c080903181302090a0f090c09 68
    0x1e520150060030b0007050f40c015008c0401840c4030071510003040c1c80c0c056401c005c0f02c40e840d440d2079038094801c45070701d6160800c441c0c04001c40b07403083c5030046005841755002d04000d111500c2408100030b04035a0044590302096041e0942001b04c1c144040c041805842800c808181e03103100c69100d00e5181e80c240003c4144043d00c181c1103101d40058410030f200c000e40703808a441e0624903110b100c07c040c0c0d802c50001c40d144010003a590755018001c620039241c2c848a50307200070500c61003010740c19072404054290140a00e1a074003c500404400451900151a21440d181c0c4020b040004400896003007040000030014103506020b030703d001d01002c0b50540b48101064403140001c1c01c0600030341e0b21090b5501d000100b04130340950b03000801c0c0e50141c00c8612440140301e545008002d540d010343c010420940c00543c8548000c011107c203807200c89400001103400d0828003d800078500b4198403039907400c21081800ea581c3c0025a001007010780d040320401070034205607500307503882c2d29003032001d101104078140302 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 919974028 1250 919972778 919972787
    0x90c170106090204151206030f12020c120d03020904140c07020907020109050a14030c0d0203030703060b040f03030309020a09090b04200904290c0912060c180604230f040c 75
    0x5c1c2200c062500703494142c280d1850000400c02540000e007040c85000030078040011044081c0761811154080e15040d00c912024482801e0703940755085000c0d0000604200754500a81c0a4442050090b00000c0c0c00450a446c030444000162403501c20303c080825410110301d080c40f4440e512980e18402409203e0f030729601c807541d40003040f0008100c4003c580304580d0000042041e60669021142101c5140d401c46802079240c2e4410303114140000d0420714080340324140c0c2d1080750201c404c1400c90a10161450b1411802050035002c120b900c0180d1400014245446004809186010301680ba10300e051034135012010451a94113481502c00300d408030b5519a40c0c80c9001d541c0950000c1110702c00b41420741034040406c1403410341300c51412000052264012036003004c1c00b00307181c050321070140c804429400c16a50b01c0e0111036661008008010800c02140c080380d241d070480781c0103003400d801c00303440f10000f000f610400d0103d400422460140c8107401e103400003c526918030700340c60401c50a1040c290061 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 919975278 1250 919974028 919974059
    0x80a06050601051602040231050f0a08030d1503080c0102030601120e0303071d0301091a070305041214070b07020c130b010203090f03071205060f010806070504030f06090c170106090204 81
    0x3803181c1e1f40822103421302180c1c0c042c41e58903200e0b40e46503100385160b1011550711901c44c501a940c01221a6034429405003440c4640d00c0c141c812840c02541080d0005003007034040d00d4a04151007000144820010003d20000050021008841c0c00542c59103030120004002c851304244000b1050304000c1e038110311038008030440e40c2200c42441c28185207040000108401c40c0180720954242d072801d14484184400300b50001e0044000d5070303080c415901d400713108605a40041c0da0141c90750b011100000030303482c081d4044840c00074454129500700b18440c2c403603800300700c8200d0b40c00000da000f100c102031240c074100f0400c400e40c0c858004108589021400000d55a0044002aa024a1040001542c2e6660404c2180e008000b241841040101c0c1ea24202d51580b02c1a944502c1c1c5440741400032901d040701241c0b0501c0b5050301d030b865078102441c5032100c00800303941032810f5410036a1590310788082811100d182002d000d50000e0071001c000340d400082c0c21140154002c41000348180700602401e596600b002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 919976528 1250 919975278 919975283
    0x20d1e1406160507030e06031302040e16050913020a090506010305280b0f061306081005010e150c071403150126030f121005180403110c0a080a060506010516 69
    0x100d4944c04246003c0da00403c40d01002648020044100018050003507040c0c0c01c00d502c256401d0242401d040b5003659a00030503901d1808540059405000d64100700500e2544000c00195500c0d042100c0c0d00415100c403820741018100756103030303810448156018018142c004002c64044d120303030140328048502c00c0c400d030103110150580300e00c5000010f50395a40760341c16040d0020701156544072040c4003800911028401c40022540200000d900e8a000320313400030171503206031207441ea5070015404111a0030480350880484000a00400704144000c104600c06040c0c000c000340b10170b2400d08101031410f540b440d400030340444510014090060405040c084451401d03040d98104841c0705452400e600a00b03001b403440100100c0c0c0948011840f03086140500000e100080c00070ba1074070107000c00c40e2091004604150080300101300000d104056190f07038118035100352210342c030241d000688100c5581c2e10035060350384904401424448a44503d5400c045c0c01d0070250b00c0e00d0300100003151100200e0001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 919977778 1250 919976528 919976537
    0x31a03120f04210c17101d030c0d14070302120c010204030803040606030303060906080319021608071e0e01031202070506030a02120f060d0f020d1e140616 68
    0x21101d1485110585000d000f05620b520061000f801450b084904889401d980070303070202000042e43c00172401d440c8910350454000e00f0f00344414003d030754007801401c2610611440303030a0181c260240c0501c042c00d901c0100070043d0a06c0700035900020640308901032213943c107640403c42000040c0d0000752010400e404040340548604c0d900c18150300900655001800a480c0003040004000c030310761121056070b00c0380e1420081031f502c0c2d0721400c00f120041e0080c030850758010401c20300b0007443c03076000044040d070504c100c980301c3c01c00c0384848a00f180c95a2080b0080d500100c024840c04220000400307a00310007060022900c0c4c41c08920010201042c44040c21141e2006440d103103d51003440b03218040c0102410460307481c100b01c1c2c0c4220082d0b02c110030302e5000060242c00b0445031300c00650f0b06402407600070403003100b080750350712174182c407080712101203038020000940800003c8141c508062220686000349403241c2242c205004a05100c00203d400340d04080c3c204a0002d103ea40d04d0b2080b54542d251 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 919979028 1250 919977778 919977787
    0x70e0405061c03020f0609010c090308180a0605041809020a030821010f15090605091903021003050f1003030203040e0c0d0905010c09090b0a030222110901031a0312 72
    0x440c1c2141031035401100d04102c49a0000c050507000035800017251412001c07174003560303240e2841c14200c81404440c80c0c00078480d00410000704101030090002809400701c4150003148550005286131042d0b03115170301144020030204461440015040703403c8101c0c10341400035001f581d000642c81c14041c04024040c01003c203180044000c034182a181c2940c100c0b000740f299503101c800120904025101c0c6000da044805041010715128942d0182100d1140d01d96a04048400e420401240e260030007244c084100a0000409642c3d502c2d4601e505e02065100091a402d0a0400c00e20140f0000c0602080c14903074802040007981c000221800c41d1b09800046415403220005c2006070321415400714126410b009000c01030040c1076010110030515a01d80c603120f01d80d145010b50664100b40310351540240d610383c080015061019180310104034540d19103000300350400020080340c0c2036544840d84981c003c03410070a0780d42c041c451480d0101d90811141c0308500583d000a50705c1800b902500407100b404036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 919980278 1250 919979028 919979041
    0x22020105030714160b100b183a110102013e03010e040b0f090601050402090d0b0403110715050409111603090f0b16200a09050a05010b030105061213140303060306010608070e0405 78
    0x9c0003007206d001c843d11a401c400c00134013059880d03565009016036002d400e03500c0810141d030052107031945520003102c608040300c0c240014034038080447c242118030365400007490017101319803100850183c40210160b141074105420868100403004104204005049042c403c9030030001034500c3c1111021500560380311400740100e804c840c2c0c034110040001c030344030092000b0590420014000d41d0300300070494004603600c0e81c100c90184075040102021840c20001444405643d800040c0c1030450518040d20b4510084c3d51042c0b4151904070070340004103411000d12044091764040f1000f08500d144035420f08120868040c00581980c3e002840098040c06049104100700590854290020402296581d41e501048013501048501100442c903110000c104001c6803410303603058501c042c02030790520026440080118601070b21120350301100c44000d90020306611614403078803007964060b58413070502c401410b250004c11780285003401141c0080010b0103601600301624000111b502003410385810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 919981528 1250 919980278 919980319
    0x10e120403080a20010b0310181b211101140307050711030f0313080703121211370819020d0c030522020105030714160b100b18 56
    0xb100d00e003015800b4040030b07141c205010f51001c11126001d4060384c0c0c214592030b100c4002c5600040e18107a40021481c46440840c0d1818070684450302074001b00d400392b6803035046030a200440b01c481d103010341107004011410070850300d201500c981000c0c2001201e15585010b80041400300500c1c85003000307004a03100090040300c1107040381414000e801d880e4152900c814580c1c40354031010345c0c01550890a170300059201c50008100003100e07003065507502e070ba21046000726241031400301c0c04900d0544500c400001500710000800891806515005021400290040e0b072094640240893f541c903540d0400292078200c030b002c951200e82d40589155031038652101e10024021030030102c080c0b0380341502d151209a09603104d42d001d40c0385003462500d00b80cc80c44401465a400102c005c0c00503c0510205541a004000d4611400d45200d07249003040480903440e41d416031400000d8a900b02240c060180100541c40001c014049042c84d0318a80001c507549240350b9070060f86805e000b11a40e00a901605402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 919982778 1250 919981528 919981547
    0xf0e0405010b151e1e0309150f04020925050c07030602070b01031e0807060507110303040615050a061706032a04060b0c1504170417010e120403080a 65
    0x307000064102c00146001450342211029803824111110404981304407034041d964000801c403400c5500000e00b400c403a91540020308082d02600c9000c0b40311403810040c041c928820f40800b04120010f02c1c0c1401004032418000c1d082900b0540707415a00a1984150a4207200220382400d04a9840c4914860207103000c0c142e50025060a2000c580b090802080d22902070480703004416070400e50410442680030501041e13402040b25808009a00000d2129009154040200e00b00b182e1003003a0b1068181c2190f20481f81118131a5a03007440c0c3c03600030040950400900b8054403240041070074a100035100307560f1501c02c4221404007000180d49594200003e5242e1424020080b03005030b6010141c1c0c010295a0741010f220703e007003820115484401806840d05460220014a81c000d603805200c40d41440c050403e5825030300040e401c0312105003010040008024a440218421202c05034940c210303403540518400603007086110110a54a0505540c162030f00b103160395550b0207520100b90b405204 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 919984028 1250 919982778 919982801
    0xf040f03120c02030405031209130905030d180506010e060612090c030313030b060103180803090109170901030b03030721030b030d0f0314040b1b09121f05010f0e040501 74
    0x3030400d03642c00c0d558080050421907a0550484100d0205a01d5004050145400468001c07082d60f00020840103207800c0a002c660003403056074a03082403005d440046d110026555885103031030941100c01c1007000c0007030750300504007178a05091038101200001c15620485004801010960340400c8501c0780521007401032410007012296140c107440c140e94194030039848182c5022664100048442d4000e002d100303110841c51085141c140c00c65607914015400140001100790740e1202c04000007001c081680d0810064284160f4507854200d00050a448039400c11602903003003448038000040c8426811140b51005008030181c0a040d26021002481008001075242c40b4003501024406d8203c03110100c040095501842019102c0381004032541040d18000d10080351040001d10100e00d070804d803880c40b09422245450102c40c1c0c030010308c88c44000700d200c9100b90403600c00810000c99644020001c131a4841003407081d985003410794110340a5900c503242c0d20411005c0007030301700002903128150000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 919985278 1250 919984028 919984031
    0x5090f0424021204110a0f15050a020c031e100e3f030a0f0507090e070905090108060a06060c11150405041407081003080301090b0105071202030703080c030f040f0312 73
    0x140a042c80640041720a032540d0003442c0100007c20b49048005ca008195400c00003110307102050071a048909500a06189046004585116201d95028801d46040381364801e140703910b59030b80c004454102440414000742184c07030102000d03511103020034410890400f2a201500309100604454454019584022034400a08003c240ca100c06200074500600d00300400f04985031504503280e08a40c0d045e41c412000c5040a00708002c4000090602607004240d881d0002c0c200340d484c804242202d0b07081c0c01c40a242d40042c4100030300c03a111845040024403c0d4900644050204d0f101c8440401300c40b0780b000c0c007800000504180c4c000c1040700f02c030010700c0d01820802940d6419515204500d00660300ca00024000724041401d070000000d8810503a03402c011045c0c556464040008014200340c3c0c14a414001e0900c800c202041521058482d141e5145d0040d40e51410b2500d001020600000d000840102050013481413004c544003c03254801c0c0c0c001c040d500e01c00002e040a8035114a19039903d44000e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 919986528 1250 919985278 919985281
    0x12160308160c08060f1b19031e09050c031f090807020d050307140f07090506150a05072a0315110406020a02010e0d11150705070306050105090f04240212 67
    0x43d0800211070703200c1d511841e120195601c40c0015840c000b000e0f500b407103000780c109000d498400b10400d40e5a540d078800c1406d001882c086c03071504981500010100d1000403d41d2140381c001440011301c003070851001c2c02ca010f0103000c5800441d0f00c060000c48201405031540d01c026450410002d001107404460f0000d00e0140807072903520702107980758082402182c4103152000c1020b2091400074029080171131400c041c158107410100360600404005110030b83c008122410382c40d83e1840034004020880c0d282d919150340d0841401c19503005005100192079001ca5105c1d044030400702c1e840f109003580da103c00302c0c158506154a550000c1c14624859052308600040c001816035000900008500e200fa00e512004880a50070022000516640030700319000c81190380155280510314244002e4868007903909203441d0340c8a03140b0f0562250411200555258010301c101c0c6080500294803080c5811551524a0b0990303c1010003100c2201d8810b000070041d004c00800300340383c2c05540381280441c100c80b105 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 919987778 1250 919986528 919986539
    0x90901060803400815070206070e03010902060310150509030d0f02031201080c040605010302030f070804142515021b010504090218040b060403050c060d020409021812160308160c 78
    0x43e16091242902900c1506203a032880100d85450b20b00c0b0712516000341155a5800360180c50700c1540401c03440e45035694041940060340d43d4000365006403000f548505a15042c02c1c070304a4100c01c110103207000d100c401d0110b90f09542c0c00040ba0103d00c1c40d9490141c801d9207140601741e1942c003480303482004206000303001142080c000a03281d0f114071000c0b10188032241e40c900040d0105d2100323503201c0c6440106500001c01d502e01481042d50001d120b190b0f100740e1102d1624480381401e0402510110b80b40c4010402c0c044410050b4425001d86507544c9900c81c4500c50b103401075602c81d004002900c0019820b81c910300d45a00540c00c1c2c400a0407030710429550b610280c4d0081980d00e2440d1041482580f5100081e4524101b0406039810b803603000006100242c0d1090030005a07402407880c0c010042e40030800840d40c0700c0c10b40060402030124400ca4031750080310008100c5106e0140040541d29401001509101d0440404442c01c6036005015241c0c1c0b080e06902e10070310001120409003c101010310700045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 919989028 1250 919987778 919987897
    0x912010b090c040302090c090a05031b0414060607110f03010905061605090303070b0c21060a0515160f0f0b040309080d1d0a091a090901060803 63
    0xc4a008035900c44040d9154080366416010300d01010f034001d0020000a01c046e11404000c0c400e0b00c10043c09800c2d000d43c0c400000b407410f00e24101d40600720000d540e41d00b0183c200307400f403003000080340c00e56613a45203013803008070f1680d000b800b2001c1c0c00d507040920201e4454503605410b10001d500078000f440303441100e05020780d4440c1c080d2150380c028116120145c80c5284500c0136112043c0e07006016524101190f1600181c0c450302508060451a040241d0f0180300500d009200b1000801504180315103003074410885032a82039031080b4086e084031560003802062041c102d880d5010800050000090203041000c2c014003904002006000035050a00c2800b00440c08203101c0e070b04ca40d42d59086681c82d0720810741c540040c070720740e1000f00307115106c0380c060380f44101d8850701c98034405130884403e55030300d814003000d80721401c441c5d0708000c2084001c1400c0c1d05000031455403041650300248001e0b4603100046551f84100b8010344005660000c0c3c840240d01c03200080e2140e02d1212420440001e1804040e04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 919990278 1250 919989028 919989041
    0xc1b06021b030604050c0111100f09030e03150106030c020705060a08091204180c17010303110c0a05030703020913080c010203071209031709030708030c03070e01090b1e091201 77
    0x1007a11030040e1070429881e00081d034920865120b405008084403803001960210441c46860565004602c42e03010560024802e5000b082c5030b0940204003e00c6505000e081e017810880c40701e0003600990540a0100403000b840c03411945140f6001410310254135040341040a10740105510400008686040079440700c0954060f41e1490141c0d805540b6410701e0fa5058440c511900c4814240703008011040c0c3d86503440900c07030380094280b82c0344c545140d180e1800d180c8400d0b002200495414004031000c400704001c525003201040e90b00c04459030401c0700007556081030740b100912800803000081c0744206401810814035921140e200c0d1517008091400d40070b500b003101d072000000d1682c5104244200d203401224580d82e0151166200304040502064045100034041d900340e120401402001420703200041d0b11070b40d0502d10079512810301201c01480c43d43ca031482c450422002410034819542800d04a40e4100d01c0c500e0072010310744000c03007143d4203405500705036544500c00301002d4032404819007014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 919991528 1250 919990278 919990303
    0x605010611060405070306181505090c01030204271103070f0e0a0b0a0807090b0f040906240c0c0e130606090c0e0f0d0803131502090f010c1b0602 64
    0x780220707448052900c0d6149401c45014050394010481000411900c0e440a1000300e00121020b1308000303140c681e0782c850344c4a0569441555a15010800d00400074803007241480d209280c107614240c50120420380d03c421101203030400e1520801c5640f910a0180d01015030174400c3d90800f500c910b0101c0c00071301110100032a0340080390b0301e200108481c1c5424500401526820f158260811107600821104508028072000510610020105504a68078050200011000794036503071039043c00e0456042d5600c41e8030031800d980d03103040562407090322100c2c00c2d044640c5901d808090700b01c003030601d000b081300f4131344c002002c800e103444c10300002d960aa138a12550314056a0300344000340d920103002042300d140442644c0040d455600580c15131900801148642500410440307400905459000791940143e5411408400e421101c4080141d54120000c81d501504011400c0c9040c00011400300401182a6030401050210640410030300c01a0300320700c00e450b81105500e03240c40d00f1000e56a075082c1c5050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 919992778 1250 919991528 919991537
    0xe0303250c120f0b1e011701060f0f031e0606141e10050a1e0c050706030b060301332c180c040b070f02040f0504021f11060406050106 59
    0x400c0b140700c1d02c4025400c90380d001e0105410302c50542c0301c0c1041140f0140400b03048030040c00c0c40c0302e03100d40241e62150280540321003c55050718002e07002c90031245143e22200c03040460710400c00102c0001960074049a4103c4031065081c00c0c50440c00320b01d0000c18000400c005d01c3c299001c11044445018059100c4040e240d4901a001021031038241e9450300300001d600a8040d542a0031481c03107000540f00000c450b0405021140c14a00c00031108454040000300040007541884103000c0108900c03401400641020811900d02401051441c4414040c0c1e21210030020804e102a5001c0d28500d4000020104558040c00402500410540c0f40d54014600c5030800071b01d00111100308404142041c170000c100c90250641c0078045d040100c40200340c01c41c642e2050100258020715030006048041c46a8402d4400540c24070410045071104001902c0c0a481c0504000040c1c4a11032a02260301c00c4828250000c40011411511a10a061070368164096401400300f000f490383c1059040e207409444 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 919994028 1250 919992778 919992803
    0xf02030402041d0a29090109050c100f05071e0c050f0a0e150307080d0e04060617061908070303030f0e150a0207050c06030f070801090e0d0e030325 65
    0x40f0320a40400e038890f03107400c0b4907682400034509040a0155582611000600310000300b500111100c080310403007596515042c800342009000d00102c1c8661404480c04030441050300001005025090101803c1c0040018044284485502c01c002da04a06510031403151070249400e041908e014071481d07009020130280420f46141c451030b01e4040e1f030139808440e07031143c1e00c2c17652848002002c2d401e4035405000e400d00c003244840c0140601500c0d045144ca032820500054420f0100300d441652106081181154408209040014025400001c00c07104000d542e6050030050514a845510400c010720402400204258243e00644560000d4003400c2012189480200341c88421480c50709035481c900100003075403103059601525030707680517008a4408207072440124200368400d85851804e40700c1c180401c1400740e400024a0302401840505001c0b80d500d0000340c035a1041100d609406002001a407084140c07010820b0755110114100c018014030001c0c03004410344103900c007060701c4900001d40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 919995278 1250 919994028 919994051
    0xa02010b01021c03180204060b04031101030b0907270801090501150b03040201200d05070b180d050c16090e1002210a0b1009090c0c0f03030c11010f0203040204 70
    0x80311100280400c80e043c8480300c003074070300710018104240044601d030b0741c9000c55405a101c0d0f1103158041c0c01d01b100f8042e5201c1c1103083c0507524070b03030401c01c05040500301061300d6651307184d81500681140700742c1068515414290f0000420060321610060301d0395010720300003034604054000e0028140544000c10241d481c480502d2290320060083e0b8882c4902000420015440740000e40605014021b0031540380507404840f509101c0c0150f1440000790010030020305000702d401e21982c01112a9103441110700e04030140ca900c4071400c00ca000d083c44004980042c01c0b5005205000a8260003004034085503200c4103140c005241d140380031200c1c1e10604000710280410b9108031489000882e2416120301c54121552000c5400100340c40c1a003911945619000d403600c42c400c030010348898440b0740d40d203401d10828030200c5030740821420420048960302000b160341c440e242541079425107408540c00c803c0e54015640c2400d42d271041d000a6280c004600c89a4000f03078081e40c003032442154284910500070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 919996528 1250 919995278 919995283
    0x60b1206180a0503180d05010f020a08091f0b03160308070b0c03150d03090b03042d03050714070e010602030c0c060f0d0506040b1905100503071b08040510050a02010b0102 75
    0x10b401000c5500070055140d080070102c4088017500e200822405d02039901c2c0d51824252294440d4903003889802080403400c00d60007501050380094010000d204220000406c108030071040e441c80210150f45007425801d54501b03105810f40aa40b00e1505101e82d5a00d1529000952141c4001d96080c200440401c4018034000c0480c0e0140c0d1030301c408481d008080c0c00170403030f500c10410f100b1828441101c00c0000c40482480142d4403c50241c840450010000660790001c80c3c02415076440c429507010440000a030444180c1e500103400801d281c0048415040715490181140c10080e1010a81c0000040c20b80d400402061103405003829240516145014814107000f08001002c03401c1c4280210040e0301c0095006a40c442d500600101d0100c0030000858101c1400025100800e80c07204d47c01e00c00c40c02d00a02241c0310703c3c0549807507491860448001400083d89034009008007818008401c20700241100344d80141c8402004050202c144c0100906564009201580075500340580350640390f001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 919997778 1250 919996528 919996543
    0x2040b01030903020d0e03070905070e01030c021212090f030f1305030c0f12120301090b091003031b0c0b18120f0d030b220902130203060f0d060b120618 67
    0x54004152215140d8025500241b200c1001500340c442c8a80010381c0c0382032030194502824403521014076a200702c100040682d09001056403d56100300200c03890501610304640e00d02c80d801070031130000d0303c412405c40e051112003242d0800b288408603644e21905d203484018101111410302404d451a40d6406050729145081000e9520607a6203003901c01e281441021000075070402d1064400c5100a1a144c510300e410a800c412401c6648482520032810300200040d007011103c03259801e60f900c0d641d0f00a0a81c90880323a8000075035842001c1e0001c0040801702e0402804070031001c5502c40c10180c400915410941c81c00c02d10511003581815403007440803d809040040341c0004e81419035415000346c0c0a4801c1c0c40c089508144802c5070f41403500c001400c1e0040036181d18101080b03050180c0108580c200c0ca070081d00381c0d07151040050201d07643e95842c4110200380d003920b5001c60031703c441c01c0c441c00900001058603000601c28040c08550f030f0380819031500c0f0b0910b041c01d0300c0f1042d5814090b10380e506030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 919999028 1250 919997778 919997783
    0x4030e131514450708071101020d050705040603140c0f0c0a1509111c020f0102150906011d010b0405090403050f0c060f1509040f080408100e0c1c30090302040b010309 73
    0xc01707804201c019200d0301e01344d02441c0c943c0c8005490300c148032400c40c00b1507034201c40e480300082d004501807200c0c542c91301a03081e11803040d00a604090500c030f500c0c0140c510403200018660340c4005802503003800181310807603c01c2d07006007030201c0c5a03903151070140c0a0205c5030703002c1702c125070000b81100852600c96100d014185616508244c40d00c042d50031f0100004822802906600c41c03100ca410041401c8030351540301e0003641c800b811455140c01d14011100741007001413400712603140c0050102c04d46020130340c0c041740e4044507080c0c4c1c0d545603401c00f914036101d02035241d81031070b1000a0206c180140011564081c2c0081060320450740d84521103185035031110000564009403031808500440c07820182000d2050081062502d09503568003000e2170512180c1d101c1c0729080d100c0803c25420f000038030800710351110a036074102c4400f24031200484000d42007900103000741c92402000142c42e011902402038046001c1185003049214031000d05009180e1004034460341c2089038941c00b9504c01e0007914911903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 920000278 1250 919999028 919999037
    0x109061205040c0909050c0306070915120f0c020c011e050405040b1513030b060603040f150f15051e030c0603070c080304030e1315144507 61
    0x460109500080c1ca00074000b51012034004001040702c484a11a95004c9881440100b00c4800040145420300c0c100904241c1800710000003005181d040c840c0134008180c80313142039071075035200507008001041c0d540c4400d5000352600142c40c40268002034402403585098036200303102c4092031a840150140d40f201440052010702c01040b20f0300f040c2d003250115003002816a03400b402801d8041c000354000c1d4070070b04a26020f005040041c0f20030125405d81002c0300b074800900d5490262030700d4059000c01840142400b95512081400c10142e5001051825500c482400700014040403201060039030b0180c14840c1384d03007410f030b10942080081e81c46180240580a858000c68101c104429038000900b03160a10a4415002e4009400030300214030644c801e8540d403004072501401d1254050140340082c0c41507142040c207081e900384d04004141141c140d051090070507141c8002042502c01d031004012100040501c10240288a406c0400180303403605049540401c410411201c40c00e0303040d2003d0002c0fa = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 920001528 1250 920000278 920000297
    0x4091b14090301020705100510060503060f1002150c1e03100b25060203010303081305060a0b031009080408010b101b080c16060f020f0705120f1009020f010906 70
    0x550540160141c45001000142401e83c02d85400b030404459108203980103a5800070064618168038058001c1d0040303103000b07400c600d0480049910055540c1d1054824440c8400b00c0d410944200054170080e000000c0701d1011303041501e0f035040e0729004143c2c10000c041e40001c0c081c014003101d10035644910140c2c4400b0b140f06190030100c803000d0380545800200c04042481c5064555803100040391594403910f00180e580d855414000c20f04003015080224542c1c8511008010070710000b81030b90000407500d000500381c00300b400080d1401541c3d541e41d45049040c500710005000380540540101d0350b440009000f1079034582c01b00230300b00050307c00500100b128001003240c44132241682ca800148942d11032031403c6034140707031246440314081d40d501d02c1032500034040c41026480112440c2c507680c1d6000429444829070805500c9800b140507150081ca05100507034586407040182d04240e040520540d840c0301c00500d4001c003d411040d400f64040c44408400c0c0c14a075108602510440303201340d032140d016 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 920002778 1250 920001528 920001557
    0x2701170c07081603111903120515030109050a14120d0b04060f090c18050a12080d0213080705150301060f140d0c0e0414040213020c0a030504091b 64
    0x75081184160780c14402400f0b108016219626566185800381e196a08003400401541d450322550300c92003100e2200030f102c1100025089040145002030540c40440c0d81d81c1c803c4210f07015178412807501075066080080810500c0000b06c0c8401c0307030074017680c14104550380320009603a0300c0001401ca0380b011402042100c40c8a40b00d035010300c02001004002140300d0303603101d0207034000203125080031303103030556031038a9095507504003d070106601088154100c02900d4240012145146403255440ca4040c0010003020002558101c50145800b41800c40d140d481307019202000d00600d0180b042c06200c0c100022070986800d019080070010b48a00048c03942c0c0c03c0c200100c0e400b00e50b1424001c1800507034002030007007170300e040c0151015003080c4c01c0020b00c5440f5030134000c000c1c9c0c0030030741014091072a05424644c02c100126901da4407940507120650600d0070700d10984002d10030200c041016000d504010340401d9070200050040b1544940f00b4050017419800b030000d40d0f1690129500800c1049060742003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 920004028 1250 920002778 920002801
    0x30f0f0304030c02130e0606030a05100207020d080304080c0f01090b0121150209010e010e09060103150803030901020357132c040b0604090206270117 66
    0x1401071007490110000001136020070b00b010055100d024242c1d0301c5150782c00842c0000c00c441680f0140840040020240c5510f601c1d8886d1041c00d090750344507400143c1c150664035100d80b880700540d40008078582d24585030818010f1074210152641c640e000d00b850845004d40140140306d80300350010405602640792481d2540c2e600c17100c0000c0312600919807442404164460300078100700300d100300f01503a10340042c400181851340b4141c40e5814401d0303150314580a078448200c5035500ca1401e00300010a41410300801d00700c221151b03c024103500c000010803640312010740256006039040980d24141201001e40800321003000c0c1c201d030b841b401c0d0058560601e203070005d400380c40111032809040c01c061841c0142000c254051044181d0001c50501c0030803901c480c859503031100206002031204481c0034070100c200e060002810240482c400000851042d036901c1c1d103e61046030b4010111030b40d510b908201060364207000310301d00080001c680e4070300c2e9a03540192007040a990f59084100c001e0354401c86d4203031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 920005278 1250 920004028 920004031
    0x90e2e0f0506072f030a0c050415060c06020901020705031e01110c100f020f0d0603020f030a050d0f1707081f141c020406080604060e0111090409211101060503030f0f03 74
    0x800c1c0041381101c1c0322141c40030300240000c680603801d80e001075800c2006120640c2d08056400004043c038176010003000c0c0d44140083d02050b44240d0250b941c4031640b0040780382074000c1d00080d6250186c1c1c4052503c0782d039584003204010501d94004c0c81508840d0290813000e005034401c2101980044142d003540940710380c42491028507001d401828041083c1d8549819082440c1d1401c0c0076135281c4080c0158600003500c0c10311030740120b00809010102da82c402d6200c83c44170b9400802d2080d41000140a54082da00380e4206c0c1c1c0090025607458640210010030403001a038842908a0311136600380050303c1c00400e410140c3e448040300001c030684d610705000c41c044107a1610f400c2645400d01c3e00005a540740607180041c0105401004c80742420b05000f4111811910191181ea161a41d00f000258103403084e1880a00200d600140582d01c0d0305010104120590300304036103c081c0380a009110750065920103c4080450080206945401c18196244211085c07281d02d03650603c0600f40b4985641c0046 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 920006528 1250 920005278 920005343
    0x307020106090e100506060a0507020d030905041e24051009050411030103021801060206070503090f060a0204140906030a021c0605010608040b09010507090e2e0f050607 74
    0x40785952440500200c425681c03aa00d15500072007070480729001e05006071900040101c5406160544085e00a40303288280c0c2d00080c000c02c1394588a00030303d4000c0491100a100c0503100303128406190241d0410400c4038110314041ca0314040c0480c07204c034820f14120b50121218100540b005080408010351031401002c1ca808016405401048035101c0c1c1c0201c41d01e210081c1c102c83e0301d1754114810450320a80803c0302c00c01319107090004001c207690019080c1c0d041445420211340c1e9441d0110303c0c40c00c040022903281c4451280c2d00501c40403502d190b004004030303001c0403140e004404844080000c2e41d0410303505540c0c10350200392940b001d8a40207130907900a0350402000c0c80b104150b03a076130f0000d56900b64000404500303080204000e009007124001c0e448480030000300b01624101c18060409003060155480e001d4400e00010b15900455040101c02c3c403003465107802c030521910303980c042d484440c00346a01450b403840c3c0c00a42410840e040d02d05c071560246c1c1074040b0110350443e2828980820b540d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 920007778 1250 920006528 920006531
    0x50603030c0307080705071a1608120702150c0a0509120c1e0a050d0b16020708161511030a0c0201020304050406120b0c0c0c1309050d02060907140109030803070201 72
    0x14500e101c02000105101031051541d1034442880e03041c040e0a0032480d621001001c40491800340510303054404540118002445091141c0c0c1e40d414209003d0181a0500a034a8210700c01d00100b603400203040b0285140814044205503100c1040803164002c0d0f0308504040380c824488000c16144c010300055509220a00315451003401c1c1d00010200e529029043c0d5803003118244a00080c01d1100041002c1c100603151002e401c03100b0380d65800780701d100901d0b00358840c006002d03c03002c0d01c1c400d025010007441c000d0304842d45070320341d54075802a452062140711b50400c0c0c084c010b00c100c0fa01034210301c0000c0011001940c10b100d10307550103440381001e86104a0450000b000b0205d0391307980d14450303e4081c00000c000340240c0c2c1d501d8641142c1180c0081d00c000008034051000c4031003010300040950560710107442200b4000751061500e0007a00d040c80d801050340c0503030640360207415400640180b003002c10304201c940c9150350701c00344183d0080301035140d4001034042109001240c02c0a00654001405100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 920009028 1250 920007778 920007787
    0xf011706030309060304080d06080703080708090a150e270f0406060e100501020d0c0c0603090f0203010908030727091112010308090a0b03190c0210050702070e011d0a05060303 77
    0x1249588101c0301200c040001088c4c2c00b959420358481c00300500020320007026802c1c20368440700064021401300518070440021000d0468071515002001424240f0800001040303903103024142d00317244c40006000e00003007950781244036085c0111a0f007a82c0b485001d5000c0f51600b0b0340c9601072040081082d1005170700c3d03490014509020703084071441803004e040c40c0d54041d420030f0002401c041c1a0b040d400e00700f20b242c501d0400807a001e038600108136080c0b03050000d40001c6074944141d102404000195140d407070000c840c0c040c400105c0003144106001c0c0e54004580e030100c2d0030116000401074080e02d120f1812582070280010713560080e18082084070000342441066511803101c038100346c000300d8400d400030919000314244540500058000100c3c0c4600710700d001902509140e84599562040c0ca07290189a80701a0091086074105008404184114648820003940d80d0712a8425039a42c03544001c00002c003111443c4e64a800d071010350b40954003a4441d8610038002d88409004107a25000401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 920010278 1250 920009028 920009047
    0x3060902180106020d1b0b0c0331061b080f060d0f030f02011508031e1608040305060106110303061e0a03060615020303010f18140c0c0c0f0117060303 66
    0x149424000c01e0f156009000c0310a44507030042c40d552844040a5240050420810005204221856000001c8000b0300d85035a9440030300c0011020404960ba2034042c01c1c450a2000c032101e000800300d440c080c0b00140b00300c40d032094101032540a041e00703036400111950040381c01c400c034466017590030060040405c090259544c0f19810200c00c2424200d001c07540440c2a12200c81c0c0a00403991410104c1d111700c08510300e01000b941d01d0b44640381201800d01034a20202079074100900544d404d0b640b001807960166015440c03c284ca560103404156114032400700001030a034441d01c0c441681d096840d015505648405c802d00c0107020041450b50b0f44502c0d0000c02c0d540f107807100e00c80000250302903407000c2307442403804000854030700c111041c0d07c1c119042000103004440d100b054802c1203c000580c10000c2082089a89009041c181c885c5085104c0d10002e1020759095a0040c0c0340541020068481042e224403c00240d4441c8240c2117002c00d0300c401021580c2c480741a50325501c09806820780c2d140c03a0022 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 920011528 1250 920010278 920010319
    0xe04020f1801110c0a030813030c08060717042f03100b040b0a0602061810060909140a0c050f04110f343306090c03060f03060902 57
    0x100380600c5441c80c0c44020030340940e40041c0314001c40481030044c2c0f6140d40e40c0804155900f1140c0000340c41004001a822041400c0b803d840c0002c5402810030349402d500c0300d4010380c540105880c104002070852522241010305c0b80019801590b002c03c8066070703522840c60f80070908441218100840070003d4406000d41c405100b60012a40c041070001103208018040204464a60704064001d001e444014003415400003440c1c3c0c3c110b1248034664502c2c0ba01e1500c801d25084040204c1c0d0451401c0038000a9035030f20075001180c24a108441811a40124002e5940d0b1102e04001c05040003030b50507070401080c00c000c042c00f168014064000b042900b0710300c846440d5540800140c49010400003921000043c2c5c2c8003074501041221001c0507020f681800c02c4280c08086e50a0142c0313108420740d81029000706440f000003229600302c980c00020022281d40d8001410341c0e2140a01e20340c1004144008180f1070311034501034801c5da1545001d100d08544a5000400384000d040740c0007003d284c40d982c08075904 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 920012778 1250 920011528 920011537
    0x21030c0d090302010b1002100e03070b040f0c080a0f0b150901050f030109230f031903050a27050105010603020703092315070507060c03120e03130b0424020604030e04020f 75
    0x4e400038234000e40c0c0f0405c0c02e8101e0b40340c14690b003c940c100340900c100142d2a240c1842e00203402488551024041c1d052422000c0d02d158010045071090407502d104019070072801a079514010200910341e5a981104494a07403240f40e54103501040705c0d8014019441d003c4404c03600428081c000140048a50391007843c030b001020007103c0304c1e44c1d040c5c50b800c2e8001c2040040400389003084001e10300701a1180c0d0084101e1941c0c40002040c581c5a0002643d420507551002d06012030305c682d2034414039800c0c5001c0308090812601038400d03508000012070761a00a000300e444c2d0541c07507640c403d8003520f000c041450b8000100030540b84456250b2107000659a0502c01040c103a00c3d5a41050755850750f031070040c5ca842001c0c1d000c5014031440c104000040b0703030856900d0900f50202440440d01504864100d806d40c0729000c40a65517002c02400841c038100c01a024100b1750703199203140516900746040c103501841030980c0d80d00040c0e00100003e00000e200c2c140560540340081c20141c189035180c60600d045411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 920014028 1250 920012778 920012809
    0xd1815030608070504060608042409060b0103062322050408120708131101030b041b090509010f062102120406140f070f11030c21030c0d090302010b 65
    0x111400700340b1140b00d050144038000d1108403410440d041c03800c0000750480340d00400c0580600c003001640b0b648451112484041781151f0b480401111040380f510074000c103544086a80001e01e801c60105d112802158130310140d507170004c00d12080d022a4070801c040c3c6140700410040036000303d84040c484560303900980b03016510556070a51510f03400724005c041c544000b442441046085418444100d0540c1860a4000d4000c000c0c8048d854041c00181c0c007801108507025005032400307010700360030502c2d04103414581440703588032104c940d91201041000718080c02501c568405045003000407502411194407540140c8404050090b2845c15404c00c03a00304a06458000e80c1c90010081009060701c505000e035020100f101e007540c108184902c0c005031004190100740103520190b030b8061400b49805c00e00445a0f001100d5070b03103640920464403540d03000c580200200407000060030b51030000d41903a20543d081f02c4424104010380c20164050034403001c0070340965503900c510445c00c2d141d44070615202007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 920015278 1250 920014028 920014031
    0x3090a060903021e150703030213060e0f030109021503090a080a02060403030e010903140f0d09061b0203030c27040516080601050c06010b09041533020d181503 70
    0x1442c50051041e40000800785228090030610158130701c0c0c1d03030580d0300401c00c10203050854072100c0300d28041e4000d1190450307030200002072500025405070b202c030f0b00202040c81919240a02d0b050f90007403500740d1b810f480000b9844680220140c0c41c02c3c40c010069a404480c034002c641a02d00e4940710044a0b5010100d040c0058002408010034160907000d07406242b98680002c02c04ca41580e00d0003440c3d01d00020210b43d00a40008035054407801400c1a541507031150b81d1300300b00b54000351030107030014201250f1000c03d013140012110711160002c01039a208640b0f580e01d5a20b00300114000c840fa503905000d40030403901c0041058030882c2c41c2c40c40fa841c4699801c00d80c041e4011100540503000c050300030320035030401c0420820704110f1413010512504681c4440c8200d0303200c2c0322190005000d092403000b41d0001d40602d034000a000c480250a030729a1280a5075031911a00140d00d56090a8a40281c9080541c0c041a82c0a4015104044104410003091f00d85091283c8a40c3c0d95014070003d90700d0500000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 920016528 1250 920015278 920015297
    0x21308010902040515010e01122c060601022b05120a0207060b0f060d0e0a0602191d061b0129030f0d2109080706091119051203090a06 59
    0x41c10700d0300c21582c001c0c1d480c4a1042142c1030044c0001d04003400309541f10b0420140c089010002d000d56000041c4000c0e018190a142c0c0400c00c00c01105040c000041c0f4840d403003030758081411940040742c611b2031090195000030340002c01a0008000351854103100f02000410854001030745d0141142a0090304071100140c1d44030490b0408006444c19202d0b07141c8192031600c0f2800307440d40e602c402c032561041484c1d40818440610b1003c54144200300b040075200c00c5c0000b407981e40030a80b11480810002c010385031030700001d001c803811700ba0641a0800f0705420080400041c440500c2490340580c80e00c28040002c203e54084100c24060840428a03001141080484848640c0b800703004203e401000c4100070714101460400080984508652043d0f2420f5200b840641561080c3c020080ca82d030040c1c01c00e03035200481d244c014002c11141c601654a0082e07a402400c00746440200840884007000781c2d14105401e040411580910700400c480c141d1004100c141100d03195161841e008000039113031354004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 920017778 1250 920016528 920016533
    0x40f150b1303060c03050412141603141318050402010c0b0603030d090b072601060810080105070e0a0b070302071509081507020c060301031e0614130c0b0c06040807060213080109 78
    0xa1723840d0340e10f8102480503030010b508101c01601c09403104006005401c4210310913508056400c07071904071b14170f6560140040d08061030000c0c5818030342143d89600320070300010f801c1c0f40c5400440c0e005a0b8000e0004400284000204048100260b007101005003941c0c0340148100080086880031141110541030842c10071410503002611480c00c00c4101150a010300f11510000005042c1401103006206010020881070f400491a2401801d5410001c2101d410400310140c0040322210f0301c00d2060b0107240000c0b4039030301103c058642c1180c0c560020300102d07091a5041d829a04401c204404008207110001561035040151040f582c01000c2502c4007420302510090600c2d6003162202c2c00307544204010000200204090306440102d0302602e403004143c0d1500c04050056038640400c070b003924400b4010460402c1d520700902600c00c8032512001561107803480100c1c042c001401525030001800103002c42d010328024224903100700c00052500341200403c1d846800240c01000c820780d9502a05800c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 920019028 1250 920017778 920017793
    0x10921020108151c050106091e050a1b050306030d0c030f0806012c0f091612090c03051e07150c111815150901031a09090309040f150b1303060c030504 66
    0x143c107240c0320a100c03e03001250626000325100043c04201503503803000850910942e07204c2c1c801491920000030340e0500b0941c00031b12078ec000307843c160f02c207000d00f40b82d001040b40190307500321a06506464001c140005a2005e95103480c0061045040c0842142d0110078403505015105407100500c00008039541650700748001c1c068020038407030140c1541000c1c4618101c008650b2481d159003403800091080c4012407000207812203070340080100303003c10004800c005010468013009240802c0000300441800061076940d1840c0c030400180c00110141901c00c0c510034803411320b0540c06403900800300804140895840741500c1e90b101c894030042d005000180c49440c10000d00c08004540030b160691085030400c1c403a10504103168185a500d840d190f840042d107082c2c02e00c1d0504c004005103c0b40c0f40c5189050746030703132200f6004d6110b0703464841c0e039024a201e0303403040700341116105000b090441c0c10603000f0300d11907000038081027041002d01000000900326010f510b002040035580403800b070030f00c0e192078003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 920020278 1250 920019028 920019041
    0x1608030c070b0a0606020309100327060e060420011808070e0702010e030d0f1d0d0e04050f0103020d03020f030c0304050a05010302210c040e090c010921020108151c0501 74
    0x80303503609001c4c04100a03030380001528000c807411200c2000c0194603c6069006280800c0c0f08040a1501c401181031002c0543c00f401e102e0f801403106001c00101c1210070398170b07044116802407940c680080f0000c1503030301c42411140d011030f06044c200044000c03851444103020b91580a22203e03030040c0810f001d03c60714a640b2940007201400203101d400e07404c80d41680c03207018038100b420000342d455850b000803c030185c005450031002540c0f2225884102b0243c00d8079407688414040c040b800301400b000c800d05042c0b03c0d09210b5214132526040c56401c0d42d0800860740b00b072080c02d50442c8540088900d080c4414401082c502c08070750021942e4514040034080b8081d240c2d07019605162040c0070140c02000d041b144040d041d9800303049074106507a810380040060250741c01c03211141e001e20081003010355000550b00b018003402d884800ca016614602d0f903071003500702609000e4540c01d070782e580c0c2c00550151040d02e80090b40c2c6000a00100600000b141041280c4c004220480360314043c0402440030a1180f80c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 920021528 1250 920020278 920020291
    0x6050411130b2d04061116141c030e0108010f080a02040e011527020c0d0c05120703020102030f010f061425051f020a020a1506030c0608091204031203021608030c070b 73
    0x2c040c05034400b210a0180141f920071560004c0201da0b4240250b515028000c5000e48113020313a032150002410300a001c0c0e8210b6a0700c0317020806080010a0b4491454100011542c4280081418506907820b02c406000782c444004510340d281c3c903042d0b1800310812501c01c0642601148c0381c0c1e40c6044c3c0b1404000742c080480e44c0f0801c0314810403820610110110b202050b900607414414400e6080d890282e00e020075454603203e9a000c08503281c001c142e070640045000c1d0145001b01d0316541d80703a4404c100b200c0464425240810b036182c480301c0345509090f01134013480d2107a42044000e1500780c1e00f03c03a07103ca241d502c01c036055000042c420300000c00c902080510b104820504500700148141d01a6541c06407000c06004540d41301c130f0481540030a5001103015540c881c0240c0c3c1001d03500c401c013510b03e03041074410342014001c0da415642040d800005440c01c403900130147e004450040b0a0550081d400040140d0700800c98120920104005000450050031604581c0766584150f0501040f6418094040c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 920022778 1250 920021528 920021533
    0xa150216120e091626010f0f0f05220e1507111b0607080c011103010602071509060311190509040605030105011206020307020f1006050411130b2d040611 67
    0x502c039006600c40300602040a00d82020807800824100c0070b60031580040140920911031400402d0105248850a0468040c104c150706e00c541ca801d103804010509c0e004507078010703254050842d80442190b101030801d540c040d2002904200007460030f42004071020703c1101c00158942440015580082c06c1c1c007030140228007030015070240310443ca030031540700c0395650711440300400c402082c005244102c4201e5941ca40003040300500d100803039001500709108040160054031000603084510410a000760f111954611862038200102a0024080992030036803520301403080c00b06408420b02c0604689099480e29601d4100c1942040140e030702a400c07081c080c0c3d0400004000486a1480003122942e120001613202d03070315810102e142c41c01090b40300546100d600c1c042ca14900b1168441c60950300d080e0340034040043c0390f03503a21807284190701e141c03044110b141e0010065079403040041c0100440d0420326007040300d400c2c00e1000c03046010480c4000c12100000381040b1441c0c014038511511540740d0007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 920024028 1250 920022778 920022781
    0x60d18020a290d02091e0f030303090c01031107060906150801020406020316111f09060906050304120201020c0d030204150905150d06030b190c020f0a150216120e09 72
    0x203040c0c1981c0a4075030750442e0500104a61520348469016204120409000400c00c103030485101c040702202c0c540030b9030050b00494146006403c01004480c81602e040c0018200003514100460083c1440440401555414000880041d407180a04c410140c040c420200c5c4041101d02510320002455106244036841004100001c0c0d8003c0265045001d06031020146c1c0c107050b081240003d03036045143c0e1b03844030f4100e41e901c1d15400b091400000300400c13955004160740e00e0340000c0c1d5150409005078801314a0501c0000c000031090100781c2e2126140344005800e06e400c40c030b400741c03504040c1c103000d0000c203030041b0302401030784d20782880008803100d2403070b0a1101c14a48004155a51028200c800302d000000800310040061070700110029130344460b4a41440c98251014400050542c210001282c1000080131200c0d100082e018401c80d00f940140c407055415580e40b031101c0480000b00c00305207400b40f02da8056030400e044001c0e22640a5217000f01c8450726140c008202c42580c0054600c01e844240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 920025278 1250 920024028 920024069
    0xc0615030c0d1b0608040303050a0603030c110a0816050111010615110c180a1803090b0a09050303040b19020d09170a020312130803071709060d18020a 66
    0x3040d000c1e110042d100c0740c0c4035a0043c2401030302d64400c101c1c01c0002c5016030714005011603104000070311070340c040d68040100351a040c13082c2040d81c10350304c0094002004981804042900b001c40000ca4800050425064a40c4c1c1ca8201d0700b049803480d61943d9aa01c4000c2c100415600802640300c0801198000c024060514054500c1c12200c03010400030420180710f0f81507004410402c4485958000b05070840b00c1c0007000740748020070f4003121042c0c0d0b1213060003c14070300030b804040c1c200341d80b56068031018551401c00c036a0007070300d801940d090020880700c1000040d064030b00344001d00150410510007036980c1c0300014200f805055000d0740310210340c0700130101103c2e9544012030406445004803584c04401200c08000d14005000380040d40c11300582d000c02c034194000b00000d00d00200078001e440259a62252110745038064480050440c0d801c10000744910880341c0c6c01481a04001409141003800e0000d04038101c550b00e07206981e074244203601c81819450b281c5070b520300409001c0b40710316a4a1200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 920026528 1250 920025278 920025283
    0x6050f01020f150702030f0316030b0402130302060f040906150f0503010f06050a0509060d06150e0102120306030a080a030212012301080601051608090901050301051e040203071a0c061503 82
    0x4030041c0401401400030424080c4281b04884000000e01c0340c264603402d2440203040c01510345001000404c0c80e0407088139442c1018000d0314000c0c2450060004850300e15024061141d00c5542d10800c06c600c00c110102c0c01484501c5620050b0034040c0703200588034000100134002100300705c11a01403140c1030004012503442d2240340d1090750003070703e0856116180e07404292064014210b0b26548030901180303960b2552505d612040c126a2902d003403042c407200d03552085da107182c0070516560040c0c01c540c00d980c41450941c401135810190160840b601c1d10710075254440d00350800004200003c0d000546080500441240b0501410001e4202422409240055000ca1110131841410310468034001707109070b03000d40b064540783e90050028070921003440c40d05a50b10340c00b564045224440220000c901810144500c0748610782901070b883c100c0405409400c0380043c000c00490b4503115004001c00d104018503180c80c450a004589603403141d0901000342d040000040000c480303101901c2540c0b905a400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 920027778 1250 920026528 920026543
    0x1704231b18011a07060509030c0c0907020c010c14070b1c0c050702010305090c03030c010f050109050f13060f0f05010312020a050607120f1d070b1801110a050a03020106050f01020f 79
    0x121129101c1502540c0499004013200504a030703152904100060101000400900207284155041c014101d41006132801d03040d140000107038040410118254003409c00768a003180110310032044241213204540c6041040e800c10780394840085120010500d40d00c030004540b030582e15051119502e403800090a9000307400340a410517483c1c5010410814082c41800c0814034060203580d61058249903083c064041203035510325551401d8000907103620036204040c0210024101d52200d9200c60210134804044084c05449056035902c512450b0140c511030400e03800d03101712010945614500b031001d03090741c4c0c408a0300159080f056104d00003c1e4080b407550b0384040942000c00c0304100c02d407500301c01451258020f540b05c82c5071a01c2d105564103039a182c0003a0300c41000881e0341c115220944501d05000c2c2103a69201010420f26000d5698001d00d001d59a03841684111100d144c100d0311443d103403502040702900543d40d248424440382c20015407140d2142001e000500401c000c501216648400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 920029028 1250 920027778 920027789
    0xb07030509010c020d0b0106020f0f070317220e0601020102070f03080a0e070b12070908031606020d050a0902041d06011205030c100212010f05011704231b1801 70
    0x800140c8050350343c1c011444219160303005001c808088130301e031400c8501d2800c01e01454015100315120003c5001c030015180001c1000d14014100c550300d565150f1582d40d5081c95290703a00c0310107007c003003c5001c020440040962905174082c10861400030317120404000500198110b90041001c04042601030a6a0700c1155040c9000300869030f41c055950010000089011214050300c0340008008100300003604c460a5454242c241503110394800352007070301e040d2103100d00320b401c10b0001c400e40034070191084050134000e00c0e000d8540b83c0b2050101e011220201c80e0103c3c04c0f59150744490a40c00c0c144030741da100700301c00c9440050f1060201121560b85805101f413500b95007078042c45400300075050040d90104001d280880e4908280034507848003a4100c1c601070a02c40c18050000901c0042258444049407010384600401680009044480d0300b4010001d50340d80c46220541450700ca0322082510342c6044007000380203614081d02c0000882c030741c410007991052000070350b0301082c40c1d0b07a03010450462340c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 920030278 1250 920029028 920029037
    0x109020f04020903031e090406062d080c030408250302071e090203100b03070504091a10030b041515021204051503090f48240d060303080109060b0703 66
    0x10f4690446c81114416a488281c1003400c0c0400040c0140c0c01407506c440102000b4080c4200c40782100c8541c4400072607409010001c1c0b05240442c0c0c580c1705a8005580050040c5400c602d002289424003421b20a0001041240d188000c000307410700d541400810041c048a6907244002e40d190003e0120101050050700200d41e40003000c1822036032225007000082c40c81e660b00c0c98076460308440181c0a03401512400c08210b0030006903900c001d900654180c102030004058002c140c010420440090142180d0f0581107a600c0350681146640d1010301c2005019403044084205081d40c0004d04002c0000c495007030800d8184070522456441e040d0007070504604526840e16a500c0448851a0986042e044c4555005030541402e81270f203034015040a004104410643d00c0181d180740b29422010007200c581e10200d4160580c08030f251003030616000c0f01b50aa4040402200c50f0092221035000740e60310480c0c2560b0303090400030560040040343c01010000d004100ca02e2800e5104642481146c00080400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 920031528 1250 920030278 920030317
    0x80f0c091003090209010b030f100b300108060a2429040803131205060a0e0a06110316051914040305010c030f0506040911090702010e030c0109020f0402090303 70
    0x4034481e41c0401540f40e0024504011541d41341031000b90365205490164000700b8500c0000c1d442d00c0001000011640d45110040c60b102c0709400070700382d003051074680110403100c43c0c411441d40b03002100c03594060100040682400e0608482d44c100710343e010142000c40c1c0040b040e107608041848600030086501003403a5600c018110145202180100c0c103c18592800c0440e0100e40e401300003014003030f10341c0c440f010b4100f080c0e00c0314030f107481c408030018000345254400c1d400124050310f1074100701c4100c1200f44c103c545030815131307491809076070090b0900803101d54040100f0070b4015a0008064119409080c55840c0105880300c0b03070041c40e070341ca81c0c6d0720620000c1d84040100c0c1540d0b4003101c1c0216003083c02044203a030046001400340c1000782e03120650908000c00324101d072a042c4116004036500c103d509880c0c507509024081c0e0040c0081405080d5582e0341c10501c55140c062000340011410003000094010062040190340780c2840360790fa005030b20601c42c1c028951000411101c0f10700d1120181c0303000d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 920032778 1250 920031528 920031559
    0xe0106080a2a1707080c1813210c0506070c05060c221502210405040b0d0f24110904022a0a020a140a030f060207060504080a080f0c09 59
    0x440b420783e01210f54880038002c1088000e0003c070b0303820103a80080094800b208181e404000d1302110281044102c10b803001d010411860389407c40c407405078480c00c510074074400c1c00c094460141601c0300c0071a010641d80703481d10040000c103108490b8030030001d042c442c019942c2d58a4856032107c009015032501c800c0002c0741929824071001c10391105084918a007506d6440d004101041647c0d1502c0f4405403094112011680d03a2480380303603012080e40c41c216403c0c5480c0a040001034442d0f4061160031503407120341d80c00810241c5a42c411801e02400752034041061030a1009101d01408001500051400020100e5451440d0840d980c0c043c048402503210303c80104c000018194158100001c0449a01e90141c040804114161010700841d40f940c40903680c1c203402a08801224406980810084021b000144040b445d54405070301601005080000550310308040b68001d49095480c2c0c4004148050215440022558850408520850b0328200304c0803004483c003a10404522480d4503049a000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 920034028 1250 920032778 920032853
    0xb09070507230a12020c0f03030d272402090607030e010215181b0f04020a1b06140a0b100e120322170601060305060f0303030a0e0106080a 61
    0x49a440040a8030794088240c13810081c084000000f500c00b601449540114504e41141c1200142c400600607515280c1c91102080007011000d544030078001c00d90b000f071031006000c0c84d00c0604152190403402912000b800b030f0144074900500706120510300420004c600358440c0019100b080fa07041c02d0140301f00b030a40d80141d0922800e6001e16520954000400052044000e582c0c1c03450074806c401e07640d10007455110400d42244805a00c0d801480310300a2445504107a40284046510303440c00c800340442d50a8040c01c08101400190b640648400c0500f00f810a000c3c40a500980b00c10410400400c1c450301242040324518140420b00260703c032040d205441e45d00d0b208071a403140109403560f0b14452840c1c2072407285500c070394600104144c032001c0368964000074200e0300c40803460001c0000745e180c040d0840c00303044018070a54114038488034102035030700c04001640c091025080042141c80b00b550480c2d0841c2c0302070b440200c81d640803000341401300b5444440b02c4000b0803032580940d0007008500e024603 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 920035278 1250 920034028 920034083
    0x15041401140415030b190e030f0319060302060c15010504060e0f2e030c0f081c020703060504030e090a0605060d0213030f0c150e0604170f03040603020403060b09070507 74
    0x1440360745041c00300085180d0300b0b6482080c0416100003040b510b14410001c0d230f42ca0080302c07a41c2d40d822100304003040b04000c02c4140710280903000304000c684180c403580844c032686c009000b002c6041e88144407071118002d50701802c5c0c0c05070505813405c102c0641b50110390486243c024140d0021141c1180108403140c0c250940540c2003200e0781c0701030b4101e8100b5076042c0c030301c0c00103403109407141018040003050060410117514215600c90006010a6003031900c54910520b00e0300c0700000b5403065900000c0014440c1c041c1d58030540c001c2e202c180001021a00748000031000801d4107090f240b5040c0203100304d503105400d5407513071501c0d41e00050311400b80c40b080c0349003004107800140c00c1806010f206020800500b05540c00e4a60071f914966008110b200103450344242e0741c00a40c0d025a050000b40061142003030000d9001c00c00000b00c988940c2c071014428210382c000d40180c1c001a0300001e0500c10311680f40941940c101099400c42d65901e0f10100042039401541070061446428540320800e4500950404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 920036528 1250 920035278 920035283
    0x70f1e080f040303080108030f0318030c0a080a030b1009060c0c030209090303092415041506030e0c06040e01090b0a0306050c1201060c0c15030e061504140114041503 73
    0x6640c1c45240d041e818910303070414801280000d0b480300010581c01d6001c801d9404144402d2220703800e6440e246040000e5298003034049400d848180000d6851a404000445031785004952140d40c6a09410380202525282c1c00d80310300520390340007030b2070031607034059440c8044500340e2030580c982e04050302d40710417220415800a0340c05000b5506004002201000030340c06000c0100407100609604d18040f01c10001c50f8030300c040410a008002078400e00f108848651514000b03100207099441c0900000354054039401c5034001a5940d1141307409c4040820000c69400310440b5540d051030719000741304000402c14001c00440c1a1a022504916156403480b50b019542c465001c1c0214545800340d41d2035500b04d4000c90000404220000480070b0203481e0f04c0d07001075000809900100d042426a00c92045000082020183d43c0d00c034005031400140404c034018031980d80000e5445007050200026942480c07106944104100010084a410350031110391a46040d240441d880030301c803a0354192440c842d40301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 920037778 1250 920036528 920036543
    0x1204030314090d0e150c0304080c010816080c12090601061209110f010306121514011d151009080d050306012a0807030309050609060106121d0a150b0303070f1e 70
    0x1100401001f00240050300d5000301110504240103004545644040d6003000c040c0003071407503144c1c0c41807103041c019502c9401c59600c44e00c0d00c54030400cac0800b42101140c0300002030f00044010f100e026030010071b0160102c104942800008620741702e8035102465024424030a4000f1f401080c07042c4d00980000b0b00520303c10f40000740c03108960508044244050420761249413500c1c1c1d00f40003041900f03d8071810303500c08100c03400c0f81c2c621030103912412410141c03050300056001d4801c808103035a00e0030780c88910085641c2c3d000c0c000340f0305070a8510b40030303250310400e09000e07041c0100038645c1d0344102ca440c0360928460b5400000c0c4d102c08000240100c035100f0192507440001540300074960160000b44080e44a00104d60060303561903201380d1179034000e0103100c0001d03024991a1480340a6904400b207690101c10351b8040081e1156003240c5402c40c203280c00c80e1194078500c3c100300c40388841d1144150499081d00130750b02d800044c7da82c034982130302c0342e000041500d00030040400313488007111032681e14580d100d040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 920039028 1250 920037778 920037787
    0x240d0b01080601090b01170a02070c0302060301060e120604030f1b0602040b03150904030909020f13030b190b0303190e03122502060d201204030314090d0e15 69
    0x440a84481d400d001301d6410300c1c100800c5200030352280c0c800800d4110160501c0c0007940781d110f6114060750050b5001e542405a0103000310140c2d03640002180201a00d03181c10810022200512844083d4404441c001d074100504000c0801d03000000c0b180c4240316490320182920840c3e50300c044c420708281c0094049840410080742c4076080b01c00543c05407004029130040c2601400400c00201e100703c400400244841d101080401780e42c0d0060194212804c071200d051804691403120340c04041e038801e8851004510074003940c000031141c0d2509049a1040a03c006070a500109542c2e2044441031002006281411484030b80f06014504200714001d0030b48508420900a0340907a40000b100340a0020000515055030045241c071145500d5014050702d0401944501080c0100075000c9651140840724021011110186000781403064940700444a5800c0500300103003100c0350510140d00c00c1000005100e2070748800510390b0314103036841c54098009041f181c003050700c5a540c68050007645c8001325 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 920040278 1250 920039028 920039039
    0x1a0a05010303090512070905071211090906090112080306040612120f210b060c101b030513141905031b120a03150e180d08240d0b01 58
    0x401990480340603075610340055450b4010040c5c03040d150448606690b00c40441084144039030f4000708d0303000d00341b402c01040c0364852002c140151184520210984c06000a4011540c5060042700c1d4000600b556545a15030500e81458008200c0e1240a881010301000290283d982c135003200002d0034400138402030101c0e039460580060715480701142d000c0b070135541145111700c1c494407010307040c3e2031202d0b030201160403c13200d40f10003490800741280e08030340704100c907000042c0308208800003c41902c2c00010010030070359022a10362130b50200c8808040c2010280503404070b040800c0f80e18250441e106914080c09107105138608482054015103400d034840c0e087c4284580800034066070040b11b03003c81604806005166180c0c0f414400d031b6140301c8030900104d400548203500c20711085051256540c0c00f1a1500304414414508542540d69520b2800181d2040b14003844103881e07107003160501c2c0d88103081c8150401c0740307010114002d01d50400c0c2c0e208101520354840c180440d0458220700c0c01002541c454 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 920041528 1250 920040278 920040281
    0x6020c0604060c0201151e090c0f0201060b030105091906151d04060302090103030f140301090902270c0a0e0909010510060212030c0306060d0c26010803070803041a0a 73
    0x1c55080e12600c0c584114000040d0041c058030300000b001d5410f0320f00701410401022600364101050707a044010790103010070018501d101e501c0f104001c0c1d4440c3c03540403050000c000e09683c800e42094401c00c500740010030070f0b5219400c0e11900102e8207140319012075816400b050081100c0d501071004013110700d0946070800e8000b0234681c0d070160380204102c071000c000400d01064411500c07000f03400c162044010030110340b040f401c030035a40000f80303006034070350070001c0720156242c2081c0c1103104071969540305401185480000104011401a440440d48421036080951003d00611580a0400008020440c140704900221202000a0003001641802180c0500a10302110f0300800c00141c03001c04119a40005011980000d9034030442d4517503034524596244641001d45080c3e0050000d001e0780d484d041c1c050062180c000c51555840603d40440d20703c00c0c20140380b1a240c1c0c2862014900103208200c07000c0100d17014107811081c029565140c616160b030b80e900316202c168110311010024024403c446 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 920042778 1250 920041528 920041531
    0x9031e0301171501151101140f15030c010e121b0405100305061302040e0d080f0105060405033315030106050603061f020f0115080d0507171606020c06 66
    0x415080c0c01c90401030304925590440c8002428021900f8401040301000401e001302800901d407800309003050814941ea0f003583c4586800010f099480000c000050031901000380d8480b020740401104000b44101003601d170340000c500c180c100b10b001c5a1a80d100e85400c01e00c01c03100e000742e5044900751101c0010082800b550740103041d00c500d04000101f404803407880101c0040d0707078000c400b4110a03111001d45095074041070000720303003064803a8015841d0b14014080303c0b40005003500c0d41c032001d01e000c1c0c25a020008050704000d20400c014401444607440020380003543c0308004c40c02101c0408202c841381ea0005d0006240da00c01c1c9090010829a001280b0f146010b02d0005d800900c051f43c0c83c0c10402c11140011244150440001c1384a141c0800e40c50b11001c0d4210740c50300503560000013030385181c2e01791044a03400003481e05803403208121094040000c5c805000c2c0c5441e00034106403c642c1e980480d403490903c4841c03100004240c80340344006400c200310703041d0b511201c2159200f54092440e51a42c80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 920044028 1250 920042778 920042789
    0x1113021c15080105010b16150203070c1b120b0415020304120201060b030c09040924020a0806030609030301060518180105012303010b071b08011401060903080901050309031e0301 78
    0x103044400541d050050044d039058950802015003408000e010424012800803001d0301e14401043c69145401e50900c003c1d8000c01181e5190b0300300340403500305001401703201d4010756007045a01a0030410002c04003001800c1a61000250031140c48900384211240d006410401c2010720002c280010000c28681702400c02c13100e40c000340b0415583d0400c800440c00216200c0203c441c04101402c2185082e5101400c158030450283d1406500070180c1655400d06003941512240c2c0040c0000030300340c20802d9142e004004078018070061404414054880c04180300e41010300c600894004a04040485000d007001d02c0a00300400244003411b80308000711007840b43c94041240d1000e00e4803401c20780c55984c540d01c0da00901c09881c507443c0850b2601e031030340602400e0790070102007420000c0120b00004040000c2041800100d80b0b202d10b06499804c141d4182e018800b80020088100005841070090710b80505090a06944940c0d41e8030030b0f98107504c102550b010030b003158050000d5806c02910042c605030380 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 920045278 1250 920044028 920044061
    0xc0303090418120e0a090c1b05030d0f0501090e03030c0d020912030a08011d060a03020f150f03010509070c0c060f12090614090c010909020306060c0a0c030302010b0d1113021c 77
    0x80c6d0341c48400b0111108100f1020000d03031a00c10b0025101d00400301d03894918450401c507460130303460300f800c0c4041f41c10704101c10740c4d400e440fa03004229201c0903000b4000060407940142d8614141614484003911401c0024211140c0200c0c00c0600c540c0c440541c2d111140c1600c05480d6280030b0a03000404039042402030f0407210107202c8040740086401003000c0c1c4260000b41107007400909540030030000641851080354441c034401014040c10202e000944100c046509a1036140d50418040211903400104080d04001e12481c2c0d00d0045031580ac03032441251521300b026401c6030300d035044c100c0d003403a0080d407030281c2c0c9414903101d2400c1080e40c0e4404000d046201481a039030f5114100e0319600c41030215141e5002500d25071051010103000d900071600190000c10707480c5041c0c101c0d40c030a82005820001a0342441c001d0000708103154080c0201002c26008071440303584050660344070b44a4401c140c0710680980700b4410014444105e650498984000300341c040f10108525407480405060b000c0703014800c0300c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 920046528 1250 920045278 920045299
    0xc030f021e01270b070609050c180a0e0a24140615030a06050a0b040810110406110c0310090203100501060806090727050f030c0303090418120e 63
    0x805041c01c010782003050f0f41e0300941003080c1601c1e58151400050b0716203c07900711000081c904001500405070184101070109105581e41850b5040011020100c1d001e2445c01c140b1030505130070801c85950225001c1000500c0b03000c00c4243c5840e00d100da5900070880e507030002d621002c038040c10303902607040819040c00b0b00500000110300c150010003900c080d0303004945a00c810000724446400f540d840300070345c40c0003d9107a5641e03000885140180d486405145d01c005000d11403081c0034801c148440e50300318003d000300c1d290f80a1100051003244510b404104010304201e040d16030038815403c0303124004089504260744412075400030031401d10224424450707050b0641c0a140c11303010b00350488405444100f1159100c806000f01d01800520500410010030f2800d605445060305054013003401e0a1a240001c0c2024148100c6040c10700740d6038400e51040c44220116980002203449200c4260b90102e550400100d50700c20700e14014800504411103142a8045980c6c003200b4140c0c0ca280489561214 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 920047778 1250 920046528 920046559
    0x30e24070e01081302040b0303070303022205010903030e060d0e0c0f01020a0c1a070c0b09010e03010207111003020c011a0907080f071b0b091b10020601051302070c030f02 75
    0x701c0041d00c40160100e800340c1c00242e00000302800310980940050408103082c462080001c0c2168800101203000c42e50215440a039607110b0810030602e40150810520081c0c10a00007034403808640c44000d0030045652040249600c4690a0b1409a82c20721030912220209080c0261501c21150301c0c0c90203903071a00d012205035840090000d10042c1c00125a51011341419450400c82d00003d074034000c070150802010000801c00d107020740080030040140c075203034041da6000420f1404803403c1a0300c240c0c010300c10030000c41c440b03c408180c0d28004990755494664416400d130083c0c0108510100c69510b031a08031034a41480c81e40b84c81c40440d040340c124501e45d54440e0159103a59094a820b0300344a403041c006605940994194180c5400c44d41c90741c07022000340e99852031806021100d00416070041c89003445a100c654420b0754540c0f0003100c0501d501c029001000399a049c051043c40c0c424040302510f40b01c18411507048071400c64101206841c016107a051902e02500314030304c22401000070309481d0b000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 920049028 1250 920047778 920047787
    0x30c0105120f070504050603090a0b010b03010e0712060b120118050f040602090409080a2f030a1808011b111b09040c0807150801091812030e2407 64
    0x541e40030215039007900e07880e50146100c900304010300031814050204070205469483c400554440c01000e801050714810901d42040101c0e810b900c42c07180c158080c801480b88190040349503900000c00d1074201c60280b00403010700084c100d903500641d00e540c000078940c00021440d505580c166108005001c1c0441d0031800d8040803544205d5401e444020fa58000c680050499002001d000320300400114010207640c49800703041c0d000c80c60403030101704802e0400e14000b1307101d0101c891024000300310800420103210015100d01c0781040b040e041103002c0030a0b040c03100f0400018409400d42c00002c00c001c3d100c082000b10b5080201601001140046265017086040011a210b991007806071032040d031101d51080c404001c0c030107482190f0301c0400c42030105551304200014402048100410700118082d000040c0007020180c0041c52581d041c0300501d40c09210f038081e00d44441d170703101316044414092840220000c10b00b01c400f050300c50003180c09040d8240c194202c140707001c015400300740d0b5442d140c09900b40d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 920050278 1250 920049028 920049037
    0x71707030b180a02131509060905150105180607060204080f250315090f06020405040c110a020108100b0c0c010f03180b0619030b0907060f0801030f06141302030c0105 73
    0x10950301036205100182010024001d10007212000810b40c40440706d10558504419000141425642c802c200309821580c0a8a50002c1c03034501e40c11034070b0043e000000d15502c11541240a43c0c0300c0c0e0422564640c8424045450703003074010b0400c54681e600c2e814119224030000b40c242d0003601c00c103c411981c400803880300b03034001040d0308400311800f807841e51188490301040281058103992a00d00a000c111100245000c02e403164100594a41c1001d017000300300d44032014402c00300040388011541402c40018511005902401d04221070313a81c9128540c2068420340014041c0840807412850b00000054880c6c0c2041c400d80320300c00f010b809104110100c5500c40d020804110b03002c1c0014001c134450118231900607001501e40040403400b0405841002c8007603104441001c4280c0800c03007560018010b40000e4041440c1031403842120010042c103042040c00050040792000001a0400800e60312009030b542e8100d15941741481c10310f40c14206101e0b00b0405901034080c0c201e540c055503205100701c6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 920051528 1250 920050278 920050321
    0x60e010501210b120f010605150c030d0f150608010f05040905030919170606041a220f050414011b05182403040620090f03071707030b 59
    0x449a0309015409140038003240464a40c1080d100c2203944d580c20802e0040d0040310a402c1c0020542500d042e003484180c2c141a84010718032441071105040205010040b90030381042c900d00490a9804088100300500c11001c1c00d0081a098580005079982c02c00c201c0c0d4101c81b4130034160503d055854040c081a280c1e000c030018040d0f082041034041c0780c40c081405821000300304865080017501c45070703c0f000b0800d01e000c00746041d40c0080d040200514060244500c1101001d414040354000304002c01d402c03a0404018402c0100c3c0c0c00c3e4142601c5071a58004418907900420611450400741001c0c084200c4200e01e0065550074540500c500381c0200b411800c8280f000d954152a050903540000c06a4004107080d0b544504803076420071040701c204031a900d81864000742141e5a050601e07001c0308684041c0f0403e65800c0300c0c40082c4401800007406d50b0001181610f41040254180002a003030491540044000030910a6a00d400440000780b22050320300c00c0c03e0000c03254855900b03a445524000102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 920052778 1250 920051528 920051567
    0x60e030f03040204091401020d1e1a01140d060b03040317091b1503090309012c1203070c0e070f0206010f06030c120e01020901090e04020f040515030f01060e010501 72
    0x80380050030143d0000ca45140607003611006d85c43c82a002d10f003607074800c5c060f138130301103455402400d00340101105010012050700c1041000503620383c0000c0c0c0307001d441c500d424140540446a00040c2c5c42c3e442c103d0301c54214000d020000e5544440c255846608107030f40c154001030351340c118081c0314075034044618000d03071140004180c1441c4c0400e0140c2c444510701d0785280c00141a00c0039401d6103402c81d01441c00303503400310041e43d12350070014001040c120106000300820f030040002001c1305d10390400c0c0c402c0c0e83d41c000c1d1000e0386020903d07510540344d4464020005e16140740d80c0c2001564144699000380503030f04c60f0340d42504161010a00702e82e100420b0145422000c580b51040010a000f42d20440d035842313060400d200e0800c08104c1c02e10454200d0030030100141d400241d0b904a0f9a4010040d07030103051181d0b46502d041c101038010981040c45800e41c0c500a580c3c80c0042503200e009422001d810400080458481c41e011495281c0a00130600c584100128901c001203940d40c01b4400624000000c1e454 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 920054028 1250 920052778 920052781
    0x15050109230f090a0c08010b0111060114060d060302060c0601030c0902072a08061609091404020f0103020415051305091306180f12120221041a13060e030f03 69
    0x3015404004094412802c134031840743d50400082103200c0c080c0080400200010701c04c10604d0014248480a58940c1c113641c0180c00107200ca06403500c220750514000744d42c41c58071564801d0700080100b4042e00701a501c140c01140c41c1c0804440007500c0b5040e00d1261a046041a94420051061340184600140f0326000c01030b00c80c2c1c0c1510300e560250460141c06c400d0544103a9542201410440c0c1610181000100e40460305000c0f50403010440082550318030401202030a80078200241e180500000d10445880380f0003d03542e0702c60740544e40a40b54039485c0b045401c1440d10003a000c0d43c0300520340000311700300402c0014140380036a4140e01c604400c69440c81d10a00d07a6075070303400401c0064160000d650800c141140482c9100f000d40d2600382c1300f8586200c0a044842e0301508002c0d003030000d0241d05004000d04800700844200980340d8040c044400e200c02e84407031134414186060309c030140201c450b0800401240c0c44800d2040c8c015180a200b04200c0d00d43d0144501c0e440740f14111604695150400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 920055278 1250 920054028 920054041
    0x18030c06040b160f050304030b06010905280305100e0f0d08180304180209030f0106031e14060c0918060d1e021003050612071811071505010923 63
    0x100204600c3e40302607614000c10b10950f607005811103454000356116030002c501401004203038032400f9080700003403c041d4550703442d0100181802d501c403080c446103503502c520309442c3c032140d22030a40061907100d410703140c000104402080007000b03110241c04262203144801c481c0070b07001180b010a1002c0c940d48002c103550350400441030b16944110420039510040000080b0302241e102d400040003403801e005030f580d45203241003603d4901d0b0301e50301050691500404000052100100e0343c50481000110480160039041c610001076071195942118091681000709010004004201c80c0c807080350b1401800d08000700358400090201c425a0304044080100c0d004600c0c104034890341d4030261403910030442403030740c04111068480c02800000c6901ea400b0300000d45000c08129000c0081400200103036450030b45103ea908a68606180500b607441000d02c0e180d1014404840340715070000c8140300006000f0900c0b9004010920880122501d8003030000c000c964580000c02c21413500d941d10546c1602c910 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 920056528 1250 920055278 920055299
    0x709050907051c060207060207060f02031e071814040e12030a0f02090319020a0b0a05120604140103052b0c02190f1d0705131401021e010218030c0604 66
    0x2075005618901e0f0340c09040000910382d000800300c4601c9440c0250300e8003035919118041d520302c1d503000800c0e24010310400800c2d00c02a00140c8240344143d4480011f51107030b5100759030300740e482441d90b400c40c13100c10400301e00c50310281c2c08031a0018056604008141e01d418060382ca80d88003c07900001e40300b0070404909007500c02d0700100000b0700c55900044c034200c0c038003000901e00740c1c119040c480340309240d40440095141025440000780070294001c1d10304655500010414800c0b07205010042d00710720042611916150f00c03c41007640d1030a40c481455840c0e007403840c1d075051484c0500b910340001a1000002403000c005408400002d45c80e005010b00303840e400c003ca10307240c2c0c0e80302c06d0301c0704140d0b0000642008007d500c84000c19900d900c20b1842e03000401c1d0300f50075940c001c2584050110401200b20713403524500e4810100c802900341903c80c8001403004038100071254440c0d07c038881d8280703842044113006500801e129982d41a1691101004505042e112444890200c2d80083c0901c020084891032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 920057778 1250 920056528 920056549
    0x20c09180d0818061e2d0a0c2f030409051806070e010e060c0c0406090204140321130b19020609070302011e14070813090203190e010f0f0c02070905090705 68
    0x1203a413039007114100c80a0201206a980d4403071b0155102200703014443c1014071032420b05048619007403988404980f507519031007080180c500030b150030b000c0e840c40f0500030900503600501900f810900445c20701030b03803841c442e061100981c0070030700960010943c00b5004603c0c04440c18410385840004142a0041204580050a24007024029a110a0015900c0b44180000b8141e098401030326141050180f0192124030310ba00c9002e50312071008030b858014001505007441052a542a0740c0e141500d0014030b9140003035101c145c4d809404640250841c90319460450b8852095085913003603580c1400c02503a0300f402e4403029000c100c040c0b495003e0034896040d001440c409074101219081600d0782c20244503840070805981310500032481c00c0382d0203c240e451a0090459a2080d800c50401003019044200c09244005440d82e071002d114580322070a4000601441e820101040f0780c0ca0b15624800281000000000042c014040e01141680d143d2050900944800000b440030504100038810300045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 920059028 1250 920057778 920057791
    0x304021807030209090f091e100902150a05040e0717150114070f0c05091e0712020d06080607031503060e160b04061b0201020c09180d0818061e 63
    0x4007040a43d0064544195007805540030040c6c419013032815031902420900180c0300e0030031355900d40700e04a10009000031030b525411000b260000742d2403a14400207902010b08844500e40100c003007000311581d50018013400454a08881021196903180720403280e0f40d0203150643c10901187c00803445401e20304403210311148041c100000240501d11541e081500810021500904210090000c00959001040050600341c0d903800c500d040600011112031814112001d10364070003400502424816481484804040c1e03408565a5100c01400c902800540c041e00c296031045001055500784603100344421380e01d003646840d0100f4203554501d00a0860040700800a103c1c00b00c01807181c0c0e00150f041001004905115660365140100c042c100c070402c0350036098000d03c814103090150b600415078100400d81104c6521507680c41103070b54503140502c5200400d25100d20601d4403070403078100c0121406580b60105c0f007602c000b15041102e656010854002031148801154402044901d103c034503008070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 920060278 1250 920059028 920059031
    0x14040305070b0606160837050a0909051503070b180d0f120804050c0306071403091e070602060105121507140d06030308090a1707060209031002070b090102030402180703 74
    0x340c042e01105d042900c9401130b541c4500006820b50540d05084058010101d102c008032014603203143c402d20b5031148091154244200000c42e00c0a052080c18a9000b81049420812113400c03c0c070070802c0b421020012460080c4070740180818440c20350000d94070b20024140c44851102c01c0d00c4140310202c0c800607801c807504000308801d0f20001e00c06d5070101643c50344130350f84e409146c9042e0501d41c0c6072401380003030f20380240c010809020b11554840c0c801514548003540143c0d483d00d900d05024030308122040c600d68003500c4c1041140e481c41d400f2610700f080341c80540c03c5902d07590300c0d2410440070300c104142d034690300d074421b1120100503c01070314800d81c040ca883c200441c15107000003680c51990312000c3d224807801c1d035402d0180700b019049010f2940104820300207001e100900e54803854445105035081c41e03180e80200340041000840d4044500d921400740a48000000162881029402200c400ca54034203800c00000c00e8400c052003541c1c0305680040881034030b00c403286d19407201408050174400425 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 920061528 1250 920060278 920060287
    0x1e010f05040f270203120315100c1b06030c021614010207030b0103060f0509010e0604110a091b09210303200a20011a09070923030114040305070b0606 66
    0x14001d8444003d01c40d16140c0100b18450064810941006850400656544002e000384441899081d41c030030349102d010342d20b14001c24080c0300250741a41c10000018030401041c0c00c00300040d020640c2c0c0a04441d0662401d00504042403020398550351035821919000740c0c58001040f8040000520710000101030050b0395203151241c4921400c0ca009810980c6c1094880c24030749030580c0c4a11911341d0003001030000304061203011007001e84824001d4009071400384911071180d103e5585050640c0280002c3e842006280d0300240070743d00300b5007410124004640d4030000011000000d003801022402070041611000c0000d64003500203290200d41c104a0344002d078401d8032001ca4810007000368000603210070580325039800040300c01003401e02c45c400e46641051030030048004444040444840304490382c2c21140d0b0f4050003100c68034041d42c466101a0322054240c483c1c503102c86014807200e001500288065458018011100300d070950340200090420810b44022800c080c80d80c0c4c0e007251008002c03a150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 920062778 1250 920061528 920061551
    0x30603020f1302040b0f0c070504060b03040b0901020409180c050d050a150b0a17011d1005040f080a090f0602031c050403090306050a29220608151e010f05040f 70
    0x5c2e41140300c1c0d2518019001602ca803400c0380070486040244000c81e01400b60904080c2c0031900c80c00082d01c0203014140b800042244c00e002901682c01400c055182040601c40d0b40d0022007800c10504016100c8000c07900f00401c4506200c0c40c1803088580120052192146e01c0d62981465031782e404516040030354405001c80660396150458000f001c0003106000e442503060041da0843d001411071200450391751840040c91800440c9424007985260300008240c1c1d02c80c18440d01503403880200030180d440000300c20b40e01c5d9400c292210280c41d000184031040c0c03078840b01d083e60340b807185a00405c211203480d40408140c10507504210390007880303403400c0b00180d9500c2e610790003552001d031901c0b4242c54451091940da4820307a40030000041001c0c90340010790459602080000c145031825a03104a45803001c1a881c90068004a004062a02c200c80100d60140009a074449080c2c440c0c664403c03111f10b0f5109034100881c10b06043e14115200707144c0d0245803e04010080984030010380625807112500b46c034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 920064028 1250 920062778 920062799
    0xd080a120905060703020d050a0605010f03020c030f21090a030507021c02090a0b010f09030b060d0206190e01120e070512240a0b031b090606040302120d0807030603020f130204 77
    0x10355105c3d2005a1154980500c15046c4e030303001031450800d5031426600700581d80c1d1203404910708083d0750400694950414901070300350320a0809100300f224000a142000b0130136455440208180d0b440024201e45920819503100c0601e004d0180c00228144510800340c98180004046a0380d071113149448941c2907408984254000c4a8032803045a0300d41c0e03881c1065810402482d40590140780c01c2c040301e815962a50501c5a010b025240141c41c504495411034071072008840203003081e11000c02d1035492141005040002d0060400c0c0020001c035074039444402c2e02d002e10340307011403207001034071200782010103000c0b584180031aa8450b40c842c40d59602c040300c0031001c8404c044050321f040c9460303e140031000d01d000e541d5183c1c8000c0c0207500141882c0c411040184503148080310444410320306499840009174980550741020794002100607003184112000241d0b1841000c0742d40b1095460350340d210b01179048510510002e500800c0c50700e507508251400f92000040c03403400341d800605058071303400d841e01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 920065278 1250 920064028 920064031
    0xe0109060605030105011202090103080a020309060d0b01020115031e020310090c1703030c0f0a051215010e030d050412081207120f0606090621180b060d080a12090506 73
    0xc910580d901410300040c102070150b54007415038405040400c0d81a9804929881014400604241e20203e9880d4a02c0d200340111000c01d240113040d1620741d0034900003c4010031518440c5809980303450744011420414040d04802c694010102c0d50050490700100fa60000c0d00140803a49409010700001c1c421249100d051a614003174004084094200780d0000310f686407c0d0791b0088144d100f0720400c0150041d9808403020b445100703600548420400906888501800703483d0000e40c0b030358000704100c04150040c0082140302c241d840e41503000100c13060603240c0c1e01140060340010020003003407181c1100040510403051003100c182d403610502d07103814a0344440984074400021741200349002c42803410300034400d5048008400304801ea103061005402102c052252900303010925803480b124130700c43c6440c4803006680d14000e02c034003521ba0400030002d4a544804980030255503021031410f0421010f00181c040d441b0424900c0e258501409454054003941c5148215031203075a050005002032000301d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 920066528 1250 920065278 920065283
    0xa0c080703021305060a1e0e071d0a150e15070506010e0c0c070303120914010605010909061a07050703050f0a020a09140103020121090f03090b041d0a0e0109 69
    0x5128960442c41000b0b1144020070810a410381808140140b036542c0c00401821034490f4041c1000741d100090280c0140113031540144000c10301c4004110700c1c43d801501c254041e0740441c241181da14050b008001d025103660107012940c174a4201c40007585400340040e00301041e0b00900b16500400300011413880c99110550486140c1c1228004000303060f19070401607044805030803207074181040e5148042c2d41d01140e11026003081601070341400030090560001c01c14a80040140d0512100d10900c01d0181c40389100e4035000a5a5030000602c0240c035225003000c4d1010181c00c1002000007851501d42c90304100410b42d058014290b0001c00110100b00c8110307000c09540140c15a03141600410001c8165075200741c1005080c5164101c0d03040c441c000032415242d0900308403400c442602000c402881030503a0069945182030010802c1c4100400c44d00d0015110355111244a5241c1da00f078010b50040d482003440e40e408001c0c0805181444c03a00c1140e000110703640000319910f000003c1400e56141040a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 920067778 1250 920066528 920066533
    0x30a020c0f07080d080108120306060702042301060903150504110603010e011a03090a0f05010b10020c0a0b130306020a0e1008090c01021c081b0f0a1b1a090a0c08 71
    0x10003e8103000c2c00206145003e600342058503601d458200c07602d8000c2010300074201e401c0040050050356404041c0c5190342d070040e01c00c201000117810303404040729404003004000b40c0c6c000300004080e8805e4410000340c95002c2d807000300032040c0b4003904c0d0261501510481d41d00c0f001a6003165561202d40c0503500801e00217141d1b0f07503503514043c01d152a003070001c0b07504844481c0800801c9508400001c11040c0b5662121181328483e416080850040c00d8119445074401940400d01d0f51242c0c0c0000e075489a05000c031089a02242d94640c060168801c4c8000c85a2005181c401000460090390140020020904040c0b01010b041e030001800740c035201d103180000c11205001c0c407200e0783c010012031741030540a000404500c10f6500100c80c1041d00740341403004201ca02800200000310080341000100500d0030410740f11102c06122000070381010107824009110070036000c28030f1503030401da036a249030090b80c0311090916401001d1103030500105038802070701c01c0c00410000a0103103c58100100b83d110701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 920069028 1250 920067778 920067793
    0x90c0f072f01090b070c0503030c0318030c102316032613080d06060206070f09030305042c04061b0212040b070f0b0411040612120302030a020c0f 64
    0x14200400900c07101d1505508002507000325243d820440f0351040d01e03062050703540c5408483c0351840000c10316400070b40d01408089107014202c503000020b07014508003078101e8030344100008107050b071350300c0002c107202d44c440f00c443c8039030300314074090914000300800e480f0b21680000030881241502c4e901c07071100903c010611b80903410605921038800b69101c242c561809041e4008111501203040c00030700a44a19007250142c1300811a00d00308a4001e400c41038018441e0580d60320029489007003c40f1f81d07101144520502c000040d01c154100c0064903815150f0034146401d08010f5403800c4034894208201c2e2440c1070182d0140103041c03500031f10803446848042400031244581240c04901c00141d07105560040d442015031b010f004080d203094480c2a40b120342c8846003414001114040c0c0b80e000751140206c801440b0502100980d00940e121040c0c40901c80035a60305d00c11040b2102907000905009042141907280e18843c0e001503401605040700503061002880c40315090000d5440d0101d4103500060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 920070278 1250 920069028 920069063
    0x30e101d032b20130f1503061a040b092b1203020c1b1c0303050f0f060303090d03140c10050609060303041a040b0c1005010510020705090c0f07 63
    0x186541d8440d49201e42c00d10102000c0303685000204100080030201030000300b4800c00e4800030401d1400289101c0c445020030301d9851426a80c240400501c80d40000e04090000c6203202d200d4001c8551480c640420a181520300040d14126800410030300e54444814103282815040440d02050a802035484d6041e0b600400c0c603015000034000e0a12000f414010b2008101169021990414110544003180406031001000601500f4100038507025007105040410606915500a62103a020303181d0301006034441944202880004656999140e4030400c400740150500d04980c030382041c42806c001000c440c138180e43c3d240b5500240c4500025030300c21030300010380c0e1041d8081c0907002030b000e4030b60222030f09050b408603440b8440d9020301520447c44108601c2d000d101704d400c4030700034032020b84c0460302c50740c420505030380322608106d481c41c60038105000410940f5021800604251b9180c0040510b50301e042c0a1000c9110002c250300c008080c280007007800e03400e07080c0007000402d1050342c50740035070385644 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 920071528 1250 920070278 920070337
    0x8090306092d010e25061b02010c05120c0307060501090603170307300507021b0d020a030b070f18080604150906060b1306030e101d03 59
    0x10001d21007544407044240c00200310a8035400104a140e018100382c4000d007500601600d04c5000d000303180c1c8240060022000b071941c24424180700048010703400e09a44490490b0500070080c80c080d0300407404440600150b0103012441400707481942a40d0340012407540c07080f10fa8200024012254000207903000810800740b0406014118445d01041424107603102c5800e81c81c0e25400c031000c030031000400310fa00305002d1800140c40c41131240504014030803000103040001c1030101003541160614003c02c003078500100300050380000003d0303400c00c11403010080090030400c0e4003050380c100041000110100e6034102c0382e544102c401c0d494514000c40202c10051540c0f030a02c1b0503005403a000881484074240c003003841c4e90040d400c074240400c2c800524074408001c1c80b81c810300030b094600d400f000060040300507000d0106155120000a003540e5605015000e07a900744589064507084601c01c042801110ba1002c00d107032110034401240c415003d642c1c0c615542c005059070014542c2d410100d0030032001e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 920072778 1250 920071528 920071531
    0x13021f14030c040603021309050705070c061e1d130506030f1c0507020f030a050607180302060f0a1b0803040204060603020f07230a061b0903020105030408210408090306 74
    0x39500051641c40c04240418241c05280540c5041580000312201020b4030740800401a21000301c00f0403003424a61000381140d400880211040e00340c445000891902804000012004034180c40d1a55210160308a4260707503003514004444038529458002c0d81c580c0c0503030341700108801c5000a91400c0038bc04140c40c21a650240c0000c41e84003081c01c00c00502c090508460300101414485d4403215544009242210f000f00c0c1d20713406100b650090342c20302c00d000403207a01407500c40d100c5041c0702140a6882c0d0116240d800040d401503001c01c00d1580ca05814401842e07098490324060200f001c1002c20b0303a940103000c0100360741c0004041f00744029481e0030b101c0c0710020312184c1401c40c50100242c0220156010700c80d00509516002600712000140c03280d404414001c0d00415103503024200d140420042c01004100609a509041d456080a000d040c00c8000c0c0c94050719401c2c00c0d41c0d03840da18402d15034803010320041d100e40412400001c6c400c041030f40d03e000d00d2003030b90015110390ba01400d240c5890740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 920074028 1250 920072778 920072807
    0x11b0b280917091c08041d04020a06030e0307080d0f09080a0f0306121101110f0d02160807170109080a0806040c0c15090516060c0c080303090706050313021f 69
    0x20000c1501640c4c0326066a2500800702c1180c0300c07082c01c3c84c2850700890007240d01c42e400d800c1c5200c0a0700c0d0002604445944128801c0f44c6240b4000d807991070441c00c80702600741e4078102d0f038420081000420600b902030100700b00512008241c400040d1860b80544070000d60490300b000000c1060180d40740c00141d200143c4400d0f00c0c042040614003c418000d81c1850703200130f84508a0460b401c140759118007a80e811003110700702142e2219581072000c550b80e000b9904184014020b054449541d03025040c000070458400320024110a424038088803004240e0410785a130640da61049540040c8d015000740100a4458980100d2890321030280300548130344800d010204031318800074200140030302c900c10a00d643c40440018101550b4541149000c062211040c81411000700024081d5400320175100c0c0603108425400920341d642c0d1916680703010903a00c80403a0b8000e10018880144681c01440e88081d200020b0700380011942c01040c081030449440340d441391707071041d040920300e5000304c05001d8048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 920075278 1250 920074028 920074073
    0x8030106140913180b040c050301180809190e0106020102031005010f1706030a170c01110f09090403140307081006020a03091e150804030e011b0b2809 66
    0x41c88000140c0c3d03009000d0030a100c1540d6801da01d181d014034502412a079203504c002c12185c903041504103803803881202c0c41014429800c108400b0301185c481000e8000159210b484e40741401000001c10070b80c414403502d841d02110090000103904550310b60658001e1030f440d0001a07807414800c0e08900c050030940c00260500040c0310250704000e034492400488150110b0a01c016071311500300082c145440420040c1041c01d00441101684185000601c405419100200b21101c0d1500034098203005210281c5c95a104c00d118041d8139003484201c5590040c0b10345862603152040240b13544464005646079000241c8490800092b54a4000e850700070b40514002040c085542d84d400a1070001d4038016a260529504c4041d5a03004c0d448103640040c00342485081c1c040d0014481c02000c4402c00c407007d90000342c04000080055002e0303a02060a001c2d10b00c580c11650341180c403402282800540303100031040c0005140300c246080c0c41a806400012060003050116241c1403841b007801031035243e0240d21 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 920076528 1250 920075278 920075287
    0xa021b06030a090305090a03030e1c031b050a02090f0a0b121218151e03060d0605150402190924080c0903030409060306050f0903180d0c030803010614 66
    0x103640d01015a03038015207085000c100182d20b403404942c14041d4007892034000c0f50080003c000c00da040401c00d80066000e45000c5d500f11003c41e2112703440c104540d0054082003401000c1c009401c13543c0e010b91031403405401181c00c0141903a010a504080843d607407440c446043c1d050001902841c01950072040c41207640ca1900380c001144152159581c1204102c0040d0004030f1080c003000445d0550080c40d0010700c1900c02e02c0000c07003803040903400709102100ca520754102c002000c40703100c81502d02800025086501c24000c594540d001804060061030640b920382c01009419030701c03800200340c0340752650017600481c05801e5014002c1c4900f80c2091a000302255010304c807000c00001c0040702d0b40030714501511103071203850200760a403140c440026014080010701086248490704007204036480b40f9001c00c2656913080141d8503849007540c5074045c3c0c1e0010400c2e902030030410710321280c1499000341051380820081d81c7d0360911a0306c0358400c465401c2c01200400413640c1103171482003110300061456142 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 920077778 1250 920076528 920076583
    0x121b030b21120901090314010e0d08010f05090403180311030c09041e0201090f030503120105030a0b01031b0e0f07021903020a031b12080a0605040e060a0b040e0d03020a02 75
    0x86402205566038400360100d030014550380720345117010080d03400c00e16558031400c1d81a10384c2d020f040180d489180b83c0c8034a19059008a20414425048401200070040c1d128202400c0014110b8041d0080c0c0400c005038030b62074035480c5440f0541e00154401c1c0c0c910304080000034289400c0025070742042d486201940700f040040390b2010704c00b540c2409110742d0243c0340e0075103200607143c1041c3e5070480742070080c004030040104070000000f040194880e003900340d4560f9981041654411101000a02d01061a40104001140076044040105005543c0740aa9031600d01018840c00d0492b10403203410118414001580d0b014440c10b5500f501008074000510f100380c60207584ca00d002c6130014104403000b081e0302e0710303042c8134032404080c2c0381c0c880406080140700040007010064156132003400d20f4580403000a00d483c091007a00395062010001e40f105503260b0b0054001000107200c069005034440458840c2036100748141d4942980d00e80340180c54400e05500240b40c292a5440e100300d009041d03124034007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 920079028 1250 920077778 920077783
    0x512070602190b010509180d020c400204380f0a230711280b0906040f08210307050f0c010f0c261303121b030b21 50
    0x641c0c00698090b28240c07919080c40c252104e0307c40c6505100c0c09100b24100c0803c0d804500d203002d0350808c5450f10107446034900020102c5c45d010140b12511511009000000086002511140041001c2c0181881e58490303116003900410141c850406c1c4100210b0040c3e0b44400044110308814140d40724106014910301188030b115014840c41404540c00c170b550420400e0998003d0961001e0000300e490310020301e4084c00c200001c2000910500440040d078612071040440c2482d052030041c2441c0205e450030200e1405544016140c0d9008181017001003a20a00c29004900401d002030040512030440840011750f4031582c1c0494809207805c0050244145d809070540f9241110740d0000f95031507402c00d913014014a09540c1c002034140c01d2000d4000b266421112030a000440361845506e0440000304000310143d040791a0007100100903001c20129120780585086c035441345000050000a031040608410380da420780c00e00080d103c20002480d4100710480a2280d048030506113411046900d180d80c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 920080278 1250 920079028 920079031
    0x20601080313030f0501060b0409020406110d050a030b031c08060a09110702100c0c0303030c02120c1915060906090e0c09010512120403050318030601030c0302090408040512070602190b 81
    0x2c2402c48018006002d2080039804038000346107a110700c27540c8941e81c001d10b030041d4000d486074001188419000000c04140800c1c4028007403c140d481600e06030041704c05400408040081c1601449080b4048201c8650204003100c24205525044060302e445420003604013200e4201e00c2c60389040c0003d0130ba61039080000c1d0f83c0c2103581100c244071070f995540822150b0804c074040203442c184420800109264042d801842c11042d180e0a03070b0300c0c075601c02e01102c80380d204828040d0307034076449010343c11416554800f00400541c8500229030075005072020f2802903c606410501c030280e0b85560402c484100e03442a0003000d01c0c00005801150700c0100003a040500c1403081e035020713868001280c000c43c0c00030300030100c5080c8000301d1662980d4403811f18641d60381250700e007200e000d5041a054141d03843c001a005048982c800f605c010341504560a002c0111000351080b140840180300120342603485c1400f90805401103001855014075006009113040005a640d0341c0209110303410101091401e100305 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 920081528 1250 920080278 920080283
    0x60711070b09040e1f0b040b0a050d060e0a0524040b130309081f0e0c0603070e060702041407031a03030703050906120106051201080c18060a051302040602060108031303 74
    0x2240c0310120b900c08503015082200ea41d000a0003001c00128410300c031000900b09400a0349001c00c01c1000d1501404101c0340c188a002da40708000301da0030481403034001001280310388100f601241141c10300c61114074150301031804464a811241034112a040c0d16850700e103121380b0320b00164030b05003810b444190f20382401420089410701c0c428046018140504001c1c1c00600140044841c3e04883c04240300c00e030182d0300b140c030b02100c0c01c1268000740d20400195000114800420107855500e03100c50903503a0b0b5031800401c5404c0314007403040b41e025a86038420280d40003081180c002070347c50500c200a013140c00c0241961280d503059040c3e075800b902c1c0041034031407003945410220fa4414100c1c4c00a0540d000716131082c0420343e000700021802d2980000508805e204a03070740b1a0459803503a208540b240b03203110b0f9094110b44c07101d044498101c200f92010350002c8003d00030041040d100c00100718081000044401225000201001310503030400200d4010010b03840507600b030503030101c0003490900452101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 920082778 1250 920081528 920081549
    0x310060327020d03140a0e0405060414071b0f140105090106030c141f030b03100c120f1404051b03060c1218030a0c06060b0307120c0e0303030906060306071107 70
    0x24201090b0107008660108403001c60000d84600d08010000d087c402c69010701070089040c0400f166030340c1014040e85c041d40001c04903195403039a81e10400c03074841511031300c0320241c95514464580030482a4205054003030080061070001305240b2412030130b6800c00f0b8030551203685001010408a44050b00420a5840340424104010301007000540c4c0c1c010048401c0328851510318170309100a8040e4070511021105030203807502d20320034080301001c5415000290020401041d080c48a8001552041c56201c03060200018030700c1d5403045c514083c20b400c840455990b4000342540c00089542c40310b04c107403510304030000c040070700c0c00d561461458010178110500000c110008140410000c2448186110750481140d8403076120313a000400000410b00d040c1c441c5480e003040407510300010800c81e4414090b0b03494078126812010344260040032610141400c1040341141c442040d07a05200550083d2142d10080034a0f0800b5810141481009401401800356185d40c580c1e6229020032242c0465460010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 920084028 1250 920082778 920082799
    0x606060c05100f0207060e010b0a050102071a03040c090216140c03150a14040f0309210210110a060506040c0903030233040f0309080c0a2306031006032702 68
    0x2c161001e4050030b84011b02c8581450a0211700000c150721411948404840c1d8400155648c001640c940500340158040f00b90b420b003c000c5000701500003075030040d218608441d211a91801c0540403038102801080d4580c12500d100c41c180301d00124884000103c034405012f01c0e10042000035540c064811f0719035050074941c4002840f00096900105600702211409111841d00b45040100f404a2941c01c9000c500641e030041404c5119210341d04070304043c00e000300b03000e401540170000001c3e0403116030303405c220304074520380c5040350700344400042c0521a1710049060f0800b1000c0000391200c448002c3c00700042540200007280d0300007100840384164401c0381d07040d041494840c0007402c0642d120394115114040501c030030010034411001989029a44030f020013501d98003481d450300ca50700e5100f07a012010085c140884200e0180764031400800c03440d1f40d11f02c2c8000e0700109406401c12a0b401c041b8102451003005800d80601031101d03603030074400c240c407401d01c01e928011130354000001000c1d0140681c000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 920085278 1250 920084028 920084051
    0x60806420a12150302041d010c02070f06110f010c03020702010311030906041b0e070804020f040605060406051c0612021813110d0203120a141204142401030606060c0510 74
    0x5016001031341d009041400001d0801105800301030400b1080c100315882d00307c200d0750048c408120201921205000c0020981c41c040084911400603540e020050043c1c01d0b11080d0250248200072a010b207030f4402507241c000318000581110305101400d00050b40402c00c01c603074007001195590f806648084083e1040e00c038178624034140203c80e08814002c00c42c2da003d205001d900400c403948510301c01ca1708070200c2d449002c00e110954440748907042c1c21400c00d02090003000d00410140c2400c1e0399030800141c0d50300d034468010043e0346869115120703207450301c40c4007415428100305110000c03242c010590040c1c204210b07800d070940075035a0003601c3c03160f07820301c2180320b030755416814040a03400a084824954501c42500907650202d6140ca010640f000704104810758000251840041d00c80c2c132101b1550707038680700c503002c00c0320041417194207004000e0311510a0158880c2c1500116801600003400c0d0b06515065084440c2500404103000c3c000c08542d0000c0c0c000500c01c0880b5400c01b0011032004030300f8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 920086528 1250 920085278 920085311
    0x309150103210302211e150918060406060509090109022d030a0b34030b0612040c170c011b050715030501030510060b0702040f06120812130201020601060806420a12 72
    0x9d8151843c18041c2e20140000d0120603044401513450440c0c401c1c185071030b412041800c940c0c425030700130340001c2c0c00300b0b4000b0510108010540003420110942c20313090f6108000030f00b411410b140884111955400780860929403070100c401c40707415245107409809000c21504d100010070502c4208241c0c1380c5829031003903101c182c2507034910b8003450f40b0100e0504041c540b14145500702d0107040c008a0450f840800444000038459800184c107031500f5070046403502250f940403020f0314003a50248540d40b40014821950f0409407401000d65a00003980c0d41545001c5040c0101d402086500c40d08004d818845d1607058030880701c20175030456000500020400315040500f0315a84890601c01009080c64240304207003004003007582140c240125141d48a203400d517002102403a010380103a024900501401e03020360145500840002e00c1c0c04042a0015804011000b0308680920a044140314640c1016482e61010540b031021041043c04d0204140c0c000301001500e03204640855207550204040a045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 920087778 1250 920086528 920086561
    0x1020304030602040608041502030c180303190512100e07320904050c250c0b1612081603020d0209150309150103210302211e1509 57
    0x3144043d5203903540d845002e0051541190103403000401d000402980312254802c413882440400e041d80c0c104455070000500c81e6170f81c6150690148010489941c4070040391007000b44a00310782d03a80b250385a0480da0350704000310014028549050240000740010f00d40b001015a00c4125031801c00c6244009408281d60040e40b09903201c0680b1441c8007400c10500e180f1300070405c420050b0381c14447c42c0c4560105c2600c6110740e02c0c25000e203e0440480c40c0d103005900b100c81c0715060056803e0000700f03481c1c0c4003d007025400701a103120b00c160341c441d0071010084407044201901489040000f86490034044005012116042e004101a40007614bc2c0c5d601c0b5003075042d40c01410340a803d420081c2c41200c00d1861607481920015018411140f100d15000360b1043c003123059a501c8050115414080c005004016001c00010418150240321000c0c030003903d800e02c5010882c44c0140e520041c1000554040c1d01d4490303a28089500e00c905042140d40c1c0a84108081c107a007042e507031441d05903500f010020b1550712 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 920089028 1250 920087778 920087783
    0x12060317161a0108011a09010b090607080307030f1a09040210031104090c0806031603020f0a030f060b011d0906120c090405060709060509030d080c0c071d0a090b150102030403 77
    0xb1591901e001152201c00c0da81030340c082d4002002249049100310a88400045074240c0c0005244014170055040d14050b20001d400605118104201d658480300726801c01c58640b000240e8403020116811040d000d00b80f00d003c41160910304042d488008a4801d0741d0040010b4080c09a2080348a0014401d6008219100119840680f07840d00c035000d81c8040c02010303d010f00020b0351400132a28a00e000309014111b90050703c2004101407540e0b00340507058204414050313022100290010108100a4584200e58440d05001580c0800c036070024010140301c0f04c40420710185005480315545952040c1508079074122045040300c0c0306040035a18101a01c0c58540d013000c000c3e01403000304800080c0d0071f03018082640700c284025031680c43c2201c4e0b900680030f290b58941d0050402c445100d0040004d01d800c9240c0341406483c0c0b20f0700c030140c5071808a607644503000c50715030684204641d404050030160014808401408202e5180d04e4040c0032040203401440008111443f20145a000304204c2e00190b9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 920090278 1250 920089028 920089043
    0x2a070b04060c3c02270403030c020312070c17090109050f150a020703060608060c030a0c09051e0102150402030705060d0f140402100212030a0c03020c07151206031716 73
    0x90b1000f424094564180c50480c0070307a602c3c0b01142c80c0140458041c02d540e040e18501004244d5403902c1c1103014040140948096010400c045500c00184440c0141304014540702d0400841d802d14220300a20000405010001303410f0014000c560303070101864049544c102c0d60b200000142c08005861100e0054032052648000500509484d801161020480b4060142002016555141c1070f4031805e00321340d07507140090204000b41c1d40b091258401e89246e282c600d042c10351941c07540c011403105034214400c03d50760300990105202e00e60741004030034407803140609048051f05240d408a0742d104864000c40303205d00c101054150140c3c05542c441c103c40446000240060314002901a96400003074500740d01410f4100114804070380000f440c0040034400004403403540e80da030040d4800608801300c108003050780030001d090301c042041248602500880015007400300300d428020305002018140d060f445801d02c002040410741d000d211114907450b040b500c560750701000c0315540000209203001070450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 920091528 1250 920090278 920090363
    0x130c05090a0b1c0f062d02030a0c0926251a34021203040f05150d0b0103090213062d0315022a070b04060c 47
    0x1e030030030742210780c0065055840303a500e035140404840450314481c2c1d0140519009800303180003c2d54a03409400f10500d03040c150004502200c000060403081180c403d2010744e008070510048401e02d115001c1d600a05040507420301d4074044d1592002500000c001c1d4082074140200c41d002030060044004000c1c141050310703101c0070103e204654098150240f49880c0805100d0f003500b0440380d01c05c585e26010501004e01200b440080300200da08103040001d0804200b41c00c41c040161600409000d01ca2114805036441d103041100d210102001c81c0e02c01c510a1245881d000190380c0b40c00301f1a60b035049542c0c00462489440001607000d00344501000390040d0404003280e6074111a688030300305590110f0200400c070440c2810010285400c40c26140e040e100e400b80800c00103040110030300a02c40440800743c10541d0440c121021034146030340d84190141c501d00c46200c080410302001020300a8501081c3c10141494002080c5201c941c6006004c8032480c1d00101c1943c105c0749084030003070030800040000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 920092778 1250 920091528 920091541
    0x180304030827060d2a0201060e060f0105040b090109030c03052a0a06110c090f040c0801140f060a080f032709060d060e12030601020f0606010206130c0509 68
    0x101d40c006120001d072602c581d4040032800e920003901a142d480003c02030750600b41940f6030940200f690328020880d030300300071180440c1d00510b400404044e00454000140d120714207070308024032a8001f080c40b1b00c03030300c4d00840100a603a0040262000e60301d84620045e142e0141c440160b81d08202ca4101a101c0d80c040e090000800100003078040505041140094442020a060b40c400c5a003881600e6403261018109000691007401c03103040c400790140440c4d2440d11a1004070381854800d43d43c040c0d140094000304000c0c0607107100702500a00c80c1c0b20080003051040c00d1241301e04800984100380004848000c100c00b90354400010340580000010350348248910341c1d1496580e44600c1181c403110380a850801d500070710001c208183c40c10050526405a5200b4040103031b00340704c80408882071a030310034000014000400c201382d2000101200c00c1c0d520700344800003914001d44114414a91341c089030800070f650364042841034000c28904000c01d152245880c1c12103050031181c00c02d9800c0500030041158 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 920094028 1250 920092778 920092793
    0x5010e030f04090c0f1407051504110109081605010c030c050105070203030901061e09021308030a080f062d06071505180604030804030503130b18011d0a080318030403 73
    0x2180c1c2d00700c004000030241e11000b55041d02050074214085501501b4103800746400ba4001c0c241c0500c00e105452070030b25000b00445074994240c0341034039480d003041d0f0310a9555030005030301d038040d01c034003001442c1d060b40c011030440240003103002e00340c1081ba5032411842050300400440d5061335203e8002c7c805454542d138020355941040704c00403410360a044000807803c124414140d6a0300c406000d02c4507041c100403401d03010350700c180948044840050070000d800f01050010344183e400325a5000c0043c2030a604214003440e021340128450760303001c0e03180c1d07081498106001c0d061034000480341c1d880c5800100041c503540150b02000e030242c7c0070b10309544054038040d8071283c881c003014021a90000c0f00410441d80c2c070841150020082100e4802240c04a80101d0246510001d402d01400340ea0700b403036580c01000d0070306039503000d13442c1100350980144950a0007070b44c400b8010401910001d40031500c07106d503980d0036000007501d581c1000003c41c04601d6074290740f4001c080e081c1e0469540b1030f80c0f46401c3e074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 920095278 1250 920094028 920094037
    0x20c0109050a120624030f0213020f09040b060c0d090f090632060c030d0f0e070e040c05030601030c090f0c050a031d070f03110d0203031605010e030f 66
    0x500080355100c001c540c07464146282c10070348003c194511091000c03aa00c0000800400742c000ba14022955070030300e00e51400144200c06540724407640b1051204520610810b000c00307a10200c1203d005202071600510254244c1c3c080030001c8401096011503040400c1d030710312a80c19105150b01030b1040c5001c0b040d810001d0501214a030980750100c1b540c0d10341c0a8401c54003d0f00580728921003001030b100e03409416440c05031105681c40403070380b0010010400206240d201c09200803154102107202c120800b202e200b0482c04940e50001070080c0709040c4c08081d11040c050040302c1251403000c010500344488040300c000500701c042c0c11100e4950312424801669192442071240b410b0610340c4201d001d0b0141c1c0640c0d0548078094540a04100408d4400d502034004041199101c086104107000c60500402c0410f006000014102c0740b5035003103091140c0d0820f8500c0e0458040e4004402120068400104440300711145482407903034003a0926040d4003504404a2031103603031001041117190400544001c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 920096528 1250 920095278 920095303
    0x21302040b04081b181806040606150c0c05060f04050607050f060a0e070e060118180e010605101b12031a030f120d0b1309060b010c080301151103070302 67
    0x41c0c40142011001800c4c003010301d01c0c20742e081001d4289915200307031090f0540d5001004100750102c0e507412808003900d00780c07089900f51525a281c0c5010862040359206407440d2507100d240401c43c80d81c8a85403520441124444d2500950740080c000c41e0600d0034100b0b441c081d0100030241961841d5a04081d5924640d84039007a03028010745010840204040c4140d80d20003000030040c3c00403d1070450604a4010020100b40c18010031407614400c1c09114150000070b802c00c168081380f0041191740b003030308869101e41442100d038903004c018084d07995600200a256441c41c03400c401d000402031040203440041c0f50b4020b0108034080050801544c06820400030082c40d1540c03100c80e900341100301540c462500b140700985800c1a03c1984003d41280c0081c05400c07a020000700741442e03000e0221340030b074604142444450b40c0d214200010002c0301d00400300100424608001002500c2d2184d01740c500c018800c0e240a10600c1070302c2c108140c001e04a4518140313803a01540e03142c042ca402c01039155501603041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 920097778 1250 920096528 920096533
    0x2060c01050105280303050304020d05030304140601060302040f090207021f0c0611090d0f05250905090d08070e011b2907020307060213050d030507060b030304120609021302040b0408 80
    0x1020084d20b11801649800e900e41d03a42e0780f0b4142c034685041c0ca03141e001400980e084510117600a01003501000194000c610914400b154140c007402c8407414a10107800040805004101c2003080780701c10700803c1c058658400006070766001e240b0000304855034031420001141c40a0b0303201e40629402402d81d0340c2c000e0249205000554404500813200e104109485038007114007090140400c00c03000d4a032a26600c01c1c421a0300003840c0382c0500200300002c50f9504222000602c0a21105405005603600f00007064018010804100405020048010000403c001414000b05c0c1d0680c41091084036003043c15002000040040c02d2900d085a1b04a010700701201440d00c0c03000b10300090544140c0b0800059010b541407141590700d08000c5d42c448103d82041c0740d00c2d07031404102a6903406040c0b01007480380d00c0d103540c1c076a81450000305542204103828883e420502081100b10728a01802030000c0d401000020490014030008044999103100c03444400c2c404540071403500b031820f00070402c0d111a81c04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 920099028 1250 920097778 920097799
    0x21507050d0207080f1c030507090305060c0703031530150b0f181503010e07081c08190e100c090602010f060b0f030606040902070302010906060611070303081302060c01050105 77
    0x7030995246c03540c034640a01c0440800805180e144264480d580041d003a1030040c514503030ba40c0381c0c1c501d002ca081e01e41c42c0c0d00001c0000c0e110101030b0180700d00030100064000015100746401111101058115030301d0000e1889950951890104c4a80c03c5ea181ca901c5012100702d40c60180d40c0c0001070001d800d0711801114140c42450081c0351050703104d0300340540c50441c01900e69403404124920542c0a80ca0303030305903494880c5200c4011050003014050308520740102101c07100c2e0526258192600080d100920007401d081c041c00080480d20700e5001c540114000c030306a01c04021440c504990301e000500024544100c0c001c4941c0c1c861500401c43da440c2d4024054042000c40c2107084418a105080d9a2081000026055084c001c003850f8440c0c0000c003c181090341e103000801c01da900c1a28102d0050750354124440030804140304440c00317400c1c98030704520041e9080c120123544410501001d01840441000a00c0c01d4004810240b0013943c00780980d52030300e01c01d100143c040c090a00845101c0d80f030311003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 920100278 1250 920099028 920099053
    0x3141b07061b0c1406070602160201030615090918050609060f0114010503041401060e0403180b03074d070e0c160303110c1606020613021507050d020708 67
    0x218040c45240c1080810f00b0881c5007542040032076001294042d0850028004400811a6032000c5d01060158000c02200c80f4854800182112202e400c076004031051f0040480440b07501c58401c1064412842e8001401c11003c03180701c4020442d14001890381c4110400c001c030342000816102d0140b1107030448015140d1703c0d0f89162001d0041411081e00155051001034041240d90003400e008060980c000180d40740c96021140369081c0403203041e008248412208507550701400c501c0c000401380d080304039085050841c00103200441020015100541c0d5021501440400946101164015208800c01000702286909104d2007003020501035005920300011404070810040d449010740d110801e1030300c100d0410301c5400c00540403056003010b0707423402c06c21856014100100200b0451000400c09030000c0100c00740c001105030016002c640181d4244118001d55600140d02182d040310403204401c841d040d614100d024114003e000c40c82102c81e003041064011940340255040c0b5410380d100800c80740c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 920101528 1250 920100278 920100317
    0x6170d0e010f1b0804030c0e01060e030d0e0915210c03190f030210060f230a1502100207030c170f04060e0f030703060e0106120b0403141b0706 63
    0x61420003c21111031602c42032103101c1541d1920f2500c40c0811a040948036110900900c016401030b961415507400180f00c00e9800c10001c20303014504400030b01c401082258000c0103045010305440c05080102c010640304c6a40c819103111400c0082c007101000c10803c81a5140300d242130b0b40d00d1410b8011811040880d080201d224500d100c0e801c010010100340b555911501e034440f03440700303908501034009202110185405544010002c0328420440c08d8203001b0811950105d10303506080220103244c09407100d488140d29071044800014a01c4c149264a05043c1c0c1480002412040040c0c4001030003400c00d03410080402500d070091901c014901071007224246d007840383c4421a40400018807040026070b1040071002503e040281889800e80d02d82d00c0400e1400c0c90541049810b0340d212030181b150308400344942c90040400b8035443d03408541c80c2d1600080c101e0301400150030004c02d85d04000785560b00b001100c5440c9041d10992201c0b14129401c1504c9540b00e02842c40001c3c02c5042c3c15100c003060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 920102778 1250 920101528 920101547
    0x170307090f0305280b0103080306040609020a0806100c0204050c0301140607050c090a0e030304050703110d0c0308130506040b041a0c030d0c0909020c0102091002280606170d0e01 78
    0x448020841414501c030883c44001c694004801d8158425004134005500340d00803074025449540019146d00749a0b003003105858440c0c000c0c0300725a1041c44100c590300c5c6d002441d107410140a81d96501c010146442c101c0da0b80e104840083d40160611003404290804040118100c40300141821460070010301001003a106064018003030f41c0c002030000440d481e02c0c51800f50009020240020305005000c0a44c0c01c0d60800c480507038154002e140c04206000100450405003001102c80450840c125070311030480301801d0001400081c80402e290110103001a80710000e040024281c50311550ba45003071104644c07040c0a00555070f04180b40c0e102018a4140a9528a1078180091f500300700304114450004c1910b510324904001200f8400242904e2601c004c003404040c03400050390b248007080c140070304050421411030071540303c40c81c414101611002c54100c2400561040000700120307040000180026411031020402d218042001c10031000800c684030620307a442d4002813400e904010b4a9040380c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 920104028 1250 920102778 920102783
    0x2130b18040207030522030f0f02100e0d0615050d051f0606080c031314030c0c1203120c0906040b2104081608070c0e0910020c07150c170307090f03 65
    0x8140010f81140d4103400c00c004101451445c000d201b1a40c0b6101d80400701c503482800c0e20b0a0302d4600056055080100c0850380c0089181482c604c092034140110300d850328800c2003e03004641d20035200003d1011000041e0007070400622000000680742892616009000d404d80104240d5481002d00314065000d803408aa05035201c042c1d50341d41d148030420141c0c0c4002e000759980740c14541c490002803120170498030007803001401144c541c0c0c41205444e18081c41c03105044e100781100358494048800010440f008807030150160302080e103a5600d4440305010f015000365000c200410042400408030001c0c21200000c2c04c825030707500d45a0125110508001d550281400c14104034447ea0140b0318030f9006080c6103c0c072105480c00049440c0c4800359031158110022001c022014000403a50170481000900c450f49011407a00e028681016a80d0a142c4a054110400c100318100d105010f4517000b1400340d000008122038124807002601103034411102d03040440d01d00e070340c0820308008004002c3c00f03170795 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 920105278 1250 920104028 920104037
    0x1b1805011415130b0c0f0102030f13030c0b01090f0b06090a1401050409020304120207080303070f1409180a0617060105150c0f070306052203110102130b1804020703 72
    0x890441071041459070090b40c226a00c0c030400c05041e0f150320000104004210015025441d14501d444035400c0c2011211040c015038018024040901d00048400c0c0e00076092080c69010114a890241d649681c02c51000c3c006d50b0080000281d4141e1603001408550242d00080040c103190341c003003200b240942001160801400802840b1715000a5422803140c40141021801e00e9620a00c442c16a03100700d4040310b00c1d0005241c0108004d404000702800307041c0031009582145000e84006003081c00f421014805c115001d45c0c00d0205000030740864058440241405035403c0500d14880000c0740c003655071004540c5050b80020b80718104000c0403915054400c09484180d1034001000810340001d00ea85403084020845403002143c20803510000f17111503406800740619608002c8100e43e401801e03141050310032800382d02c000e00d64207241c00d9065807500344034900346d07086454680203006030103091503c1714a000c004140b203a4201c0240c41c900c0811110340c010340000074244000c0e0702405034000c0129 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 920106528 1250 920105278 920105309
    0xd0309030503042a08210702060d02030a0216030309140c210709021204031b0b0403030c030b09090703020a05031b2211030106030b100e040902010504031b180501 71
    0x4c0c00c0f0804d03107004040ca40082009603050800c00c03140b00740c025402282d941e03101d18543c204180201015442d4681c0c0c420500d42000c482c1d4000c114288038018102205650000008000d040107905135000d40c1210b0030801403654443c5800b60080804410507544039480c0ba000601644000036a0091001e010b0038603420394401706d03904852068158032140d2540030700240420000100d1016011a00b10004803001e10b0030f0505000d44094513800e90f0003581005544c1000104a0110741e05400c198185800500548184000c400800d4143c0c070701755101d00c030401480103101d400541e02098a0080b6601c01050f03a455040503691425004a00c1060300c044082c5030051400c4200544250040002c041d802d50885589404032154046150600d140100041c085180e2600c283d0885070019154141105200c0e40c000e40b001e074140c00641d102c0c070307221509041164454025103000319070100e5407803400c007240d0480005d800c04a002e16007082030b10b00d43d12040c044040c06524101e40154001c0e1061 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 920107778 1250 920106528 920106533
    0x50f0103020a020705120d08010b041505070f0b041110021b010e0d0b0109050a06121104020d1401030b010626060d020d1b15030902011202210a0506030d030903050304 73
    0x1070b41140030044154014000300142c9602c484480c05605580480034080c0d004100401619090043c0c100d00040da50501c4140001d1801c0380c0d2607107a101c1c07641009074994110f031402e04010118480010404001c1c1340501c401c010394003400803459041102c2c1c4001141c40071104903a265030300850ba60980c0100c405814407035000e194814103103d40500f6241c02e0500b03a8803400c90b030311000e07072000e070072540c0ea1000c0041e60341083c03240c003018041161006120b504140c5030020a1020040038510480e4002944208042140e114031020500b1b022085902c0d0780d2824120342080e024803411020510a02000420041050b86d500070f104414040c05c0068a92409004060111240890700305202d8540580481e64040645482055031314044882ca0b0401000840c2d281c0b064001c1401e2604041142e0010703a00304500042ca89000b03440140c560111301070806210864200c2e5035441c600b590180410700c000d54014902c1070034144c044072007071240c0850031800c6426000340500001c01c2403011800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 920109028 1250 920107778 920107781
    0x7080f010b0108270a03090e01050604030f03081f06180902030609010902070602091c03020c01050a02030d0f2a140712050a180b09120714010f0c0c121b050f0103 71
    0xa0508140755034201d2114410785903407420b17120300429004106c01032020000e444404401ca0b0250000350791090034945981d45645100305600d40080070b11181900040400b840224a007219030484804101c2c0c0d80e035110701c00740460064144103944a0307034803c808a2040e00e180222406000003421280c21030303282062503002034020000c2160344039020082c1500503900c514000709021484c0000d03184034113680c074019241014160340340707040c030406000e21a81e40d900881680c072030700c0c00c2c40c002182c0000c101c001c1c04010702d0208a4200b031846032040700400c4006034201c0e0301403a802ca8039000303610003074002c1000550050322002804290704a04200e44c00d48560f002e040240854140030010424a8825041c05090f5401c40101d1000c081078040583c07030040c2000303030a484150007502040e820940d003840c43c8290801c855051120464080052602c610710410b07015411550750520562182480c10f0200c0707840344240c03107030002030500e01d00c0b0007814450310007140c40003002d4050720745007a4010740 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 920110278 1250 920109028 920109061
    0x30408040e09010b041406010201240501111e0313080a080d02091f1110050906071b051603020f06090d02150d020315010306170307023007080f010b0108 67
    0xa941d5413a1a0320313402070780b04c0340a4103002c2d003a007038503404407403500d50f000a0840b940e0034004d030903400c2203e0494401823031021640302a22400e20308140c044000c90340561800a588602c4441801c80103907207515200c010014160b418103e0429804030fa6643c08a80d581c5e4807030324000361406104020490280c0740c0d590060a04403009044464a406120100020402c80c02062808240c40c040310015404041c05400640c22904070100308500300068040d43d5050001d000c4410b1064100303d2038401d0341083c12103080d181c1e10108403018008800e9001252104622049004416440186007680340c58020340e076004802030018140d0000c40c0e000c014410100c443c011002060401211200101d03078001180b050b0800c20144254241d41c4000504a840b44d500400360712058036680012828040229440385070101d503e5004003000d00c0c0d209503828420400c0450703d50110b01541c40914022407a58100d034580026500b42c2000b00c0d010900f0b0310140c03107000703001078000c02c0050b4400046a4854 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 920111528 1250 920110278 920110291
    0x51e0d20120d0516060f0f0f0207150b010c050a0303090209060a080c0411130b03060f04020301030b0403080421020609060a0b010e01050d06030b010b071202012d0b060406091a030408040e 82
    0x35140c41351380d40c94442c00c80b00d14100c004221038881d21005034080e1175004120350103800c101c5c00c52030510591207559145a240b55514070a80e100c411060042c4e20642c803505006801201303131803040b031041c580640140b0b0402d50032030081c022040080c599180000890003150194000b501c4110a035800b040010705c01c460f540d4400710300521841560a8174140703403802074401e502181c2c0d07407410309000300803500010b02021407140d80104010f000190383c8120341d580095050410496035292844d005040c1d03801a444002c0346481040c0e0000b07080c0c1c0c0060154001e0038840c0646000d034680d200704d4401e03a074000c0d00240c00300e403040f5845100d551140000b800d086500c00c0c800078000e500c07a980c262a04600780c0c089096894081010024001d403194201075802540c0001c02c682104580344050f11240e4420681c2d291004c4034446110b41c409800200d6801070090041e6a01d07610340304040c1c848281c5005000038254007600c1080001c016404490250b900410b44074109860700721030380701040b40240316 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 920112778 1250 920111528 920111557
    0x6230c03060d3011100902010509150f070b0f060414151f090f0906080d0309080c0a050d0f110613080d06090b090606070c051e0d20120d05 61
    0x43c001c059907511188040d80440c3d039a00c80b00400c0800300c1501e0204203041101400e49405507200050380c00508455050a042da54100e45a003440c1d18041240512903100a201c8800908102000320360f08a45104020506941e88680c850700244001c56a640b00e8200346212074001080112150003031800a0100c0140b1121008040d510754009071a66030038000082a1945818000c12022074071074809850351840402040d4a000c0c0d036242d0780c00c0c848490310280760380c0e40c0900081c80a01c5007107905601e194022180580036515001e540e40780c2c200c02280008000b80c1e240181c0d02d1043c40481010260700006042c152121072840c8408940008100d612000400c9114801c40140c01500c000b080340600008602e0110028480c464070002c0104d440381c6410080780000559010400c81500c605444ad03151000c50320341c150080f440041c61440e4803011445022080024028213100700800300d41c00c90300c090b02c1d41402e01030382030360040300824150041c01000401c18820400340c151080011207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 920114028 1250 920112778 920112833
    0x150c0c0b0f09040608060108070b0a170c0d02120a240b0903010605150c0714030604060b24030a0c08190e0a14100605060c0d050706060306230c03060d 66
    0x20f8102e4006900c8001c0a4100c0c1c8010040c0700300500a190040c6130803d0030500e0301c5210f050041c00700c4101030806100580707210129081c203c2080c141c1c0d1454031000000c655031500c0301281c019950003101c0710059079003042d0480356070006000d01d07003a040c002d4610140d00d1034104a0388228503008018116095981c1e08000074040d956045590030702c10704403603c240c0e00d03541078038060f04000907500105100c00f1000341000481c0c03400940c4176070150b0032140001c0c00d240d10707800242c100c5603006154041070b104106c0000721030240f04000e5001d0f2103840350800288983c1070040d031360304004451604004600e000ea103007850032590089007040c030808065412010480c1d6031980402941c043e10100717980130800140d00461507200f400c01030704080390b00030f080a101c0d0802c0c40d90782041c003046000f0410081042c3c42084043e03000000a503a00040a01c0b91000d002c002610829442100e950b4000c03080f4042005507031410700300ca0080c8000340020030682d00325115144518082481c060000505a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 920115278 1250 920114028 920114047
    0x80612060709030b0f01060c03080406090c0b0406020115030c03080d0e01020a030e01050a1e0e070e13120c0b0f0606120906010f050a051e010504030c030b01150c0c0b0f 74
    0x9514030400e4503031030740d0b02840d0030344c20a0000303580b00800d94070841003490010710025400000c1c1e10702ca01c0d494600009155582c0c40c0000107480c00b090010a40e51500c5004900841224080d1003038030b074117038001c10049480b21503000080da11031002400950b44c8100500201742e54100601e41d9583e49100400c13000e40360440103003240d000741c000c440041d41c0c640c2ca0300c04c103038030a011b0309402c507010f0300050280004a40420900300c060508103401160f981d090840c00b60002d03c101c42c0202461041c3ca44d031443c04a100c4400340081d00001c4500040360440bc8440ca0b00070000d0780c882030382014a41d10995500c0160342041d03039000e00b84543c05401408803503030030984403c29610442d402c001511555242c80c100031074801154200c0c500c594542d080a2081e6102c1c5107680507010b0b4040f500070441d00341b25006991620450300041d01c1c80107401340105c2400072a0030001c0c101c80c0400c4018143e5000880102d4640e41c800708010644100e400d000c02100e80c032000a829448981c042d030516051124 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 920116528 1250 920115278 920115283
    0x210507081917030907090c0e0a0803030f180c01200109060906060f030515040212061e0615070b060f0a0f0f09050f180a020d03030f0b0102010e0c01080612 68
    0x40307800281c601400401c10003120710054070122071814031815402e100313240c55210601800396002a6540307075040e83d05075104541010040501400c0b0b02c1361240c8640188ea01c1c2d5200319441046c0d1220003011039440401007410905c20100c00c2d0282c40800059401102c1800c0414807941d1002200c2c824410180c00c01e1185032901e0b80b080200158543d0280790000640d180d6038414150081151420400b00b40007082424002614214100c02c3e0f5480c1d10026030032074001c1e040214203200e0282006047c80c1c1008200041960041d0302c5026170781d801041100b100507006072418001414845400058860002c0ea600107000904112080c000030700850f611000c0e9603c40300c542183d40300108004080c480340701c00506000d4400340524038050781c00e40704101000d003200018003040ce001e022912418004442c80320703802821800b88c9c845c20705005009e008040d0040f10050703c1c0c000c005001350300510078a14840d400f90007410b01901c0308001500c204000078956034000f05503003800d410340d0105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 920117778 1250 920116528 920116543
    0x8040528081c1b021c0509040f14040b09060604181b0812040f12030804080d060503120901020d0e090a1107060609022d0f0c0f011a03120421050708 65
    0xc0c40c10510f2040c5a07003009181c07075986410513685084c800c0a00721003a0b40101111071119041d90049042c002ca1001c681c02440300d01800d42c0000030180a1008001040942d1401801c4400883e400d0307440c0c20040004076a12030151140d1300281040d400002200e0b2428000c0142c1030006c0c40d501c0c942e9501344070b4204009030004480514001a0501c50400b04405200280074618107840110026540280c40204040c0000c0c0c040309010a05110507411508000c0252801500b0303144420500c169400c40740c2c10000c05c69016005822119484030310445100c0490300006180042a0b103440c2e00034001840d103c4241094100304102030008145240246802098103400c010381d14201309110071441c4c411f003031942e032442c0b1207403075003002502c207150641e128a05d10090b19944c9503214009685444103644103818a5420b201607600340e4440c0b88148030303111406509503860048041c2440e10144030340d025150242d001e484c0304070b02d0801803803004084140328400311490507407101b502c13a291180e13 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 920119028 1250 920117778 920117801
    0xc1109010b090316050307050f150d0603140d0c031b14070303030b06031317300a020c0304140d020d2d110f0f0d0308040528081c 57
    0x40005006400f41000c104c1c8402c402c0d884801c035150107080a000035103a01c003038452544035504404400e85a6a030302403c004c60001101c001c139030359005026003070014102ea44019241c649aa92407150850804030321064030b0034260303039607040c0076041e5541030f42c1c42100d00300881001c01e07048800f000042d049130f03003107400c0308001e2000708030407495842c2c010160342c400d03914039015041c20710501c002c5140a860b581a42580030059400036403180500c45860300512080000f41c0d00ca60001c01c13140c40b00442180900315810038182103503559031120200764469201a503503540d1040004000e88800c02001d0b280b070210082145d00821003a0b00003c00c00410703030100b0755010303103900c408100c0e040e00c407414005907041c250341007022000151075a00040c4201554540100205c480748451581c0301104d1480c3d604004102c00c060f00b4860400a10000701210110313182d01c551030f1307540b844c240302a041c43e29022900a403204000419911950941c00c925103098407521300a950092076102c1d070059008441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 920120278 1250 920119028 920119049
    0x20c01080a1506052205130e030d050115270b1c0c050307090501210b0a24090b120112110306130b1e0114010c0803011e080d0507030c110901 62
    0x4070000c0c403016034018142c05c0b002101c20300f420208000d403500c1088518902c4058070010f060b44c03800e0b117500e0030751240200c6040c1c018035040001c2440c00b03410703902031074540c010359901d00008014103c0201b00800b010003041d02c1100d8032000c001041d0480000c10307120b149501641071411400c00f01f0b1040e1002c8050340b0011490200c1000b10140c3d00c40030000c0100000d1806c00c49540c40042c20382484066000c141620545502c5803103642e80700c0c0094a0014030310f00d880300400c50310800d06030100c1010062041c00188007030341e001845040c0d400a0b5212400300400e044400d034a049201c10030490301440031920344103809400b41083d903080c030080c0e100f05200000c0303000c04149440d080e0400c0d2002001003540c906180e2070700401d11080d00b001810748080f02091201e42c501003005035201c40108200130100ca40010022441c240004000520764284900703420440d030700c0c0d5458070344a50001c480c0000140701400703440e010038868241c8112440c01042d0034070501003880007244500c8426000201d2b07a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 920121528 1250 920120278 920120287
    0xd0921020d0609060b03060c0403080304060f090b010e22020303040510121406040b0d03021c05070203030316030c05072a0510031a0a140d0c080607090f09050601020c01080a150605 79
    0x142014400347c0c0c1e21281d4084044d19050440e0398540036400040e0000c2c000c03d40ea0203e8124a0110744c1c000c1039070341d801c014404410740e521900443d1111045620b000381062a46400151010540120300e1180d401005103082605260074411018522103600003000306228003140e000010f44a00c41840d200d1203400c0c91280b810900740801d403108404c4c0c542c0140f91251144e80130950215801100c0c03000310101110302c0c0a526812503ea00448501a60500000003448480710303114803054042c8155403000d0149080c240010780e074cd40240b0380064400350386d0340c01c0e01c00820050540d4288001c14054040035168544001c0b51441c2006403041c0e0100c0e40d1703103110840300a1585006042d00c04100c82910170319081000d07810f030091a0300c1c3c0c1e0301d00440754041c0001c2000705080480d005011030701e088400038503182d400144101c0b0b1910849000300170f5820040350026442c042c0b50f21606040c2c004240c080fa28800440b042000108940d034850341e070318444040004803040030381c005d103c04d139600e6454 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 920122778 1250 920121528 920121551
    0x80309690705030106061d040b01030609020d060e07050f18061603022d0a0816020d0b040b0f0f01120f02040c03020706050606040e04020607030e1801080d0921020d060906 75
    0x85411507000001030180d41060101f0010a5607800d540d01c0000360b501040221840005902400301a0441d15100317001082c0411203000541c4101c00322403289a0a102d0b98445060070703121440380d000b2159000034104a96550011400d0a00070b0000d80640481c0ca01040134031076190052054000f280160010b0a0000ca1195040c0700004a803000322015290382d80d558860350381e5140101c10080c0b0710000410300044d50210258044601900503051181d03112052810380b01d0316030304550480784034000d00b007c0786038052108401e5200f000e1041c0362042c82d03402e01110900c0c40c681200102ca040f0514001500140c65a004030f0a0020985d02d001d40ca580e00c52810200391000104003d00403c410f20003000001c1c41ca1102513001a01aa1310540e1000a0304088034180b414540c0326070000307000c1c030041007a0464002d5a504840101090720340e00100fa8800b10740d9420144140300c88590f040780f402c00050307800500c0744c031040d10003002140d202507196241d0055800c80f850640d0038582d64480c0541 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 920124028 1250 920122778 920122781
    0x4030e0d24091506060e04240e060a14181f0906060f02030f03070302130e091f0c080417120c03160c0803010612090803096907050301 59
    0x940082459084c0019410b190b0700604401032680c0b603d11442c0c984107030249018810010620318820026100c0c010364803954249138521b401c1da070850050601d0303040003035416403400105840368170003402c4020403910414007858a590103021611185469408030000c007190035400c8000f4141c00c034002ca0300915182c07000e031003611142c1d404c03829900308000400301c0ca00514200c1e50b01c5249401c0041c1c4034440e0007540d640c507107100d4010354448203440003804107001000641c1c40d5240c01804189120128203900c01c0c0c20340302c0201202010444280101740003c1c50210105500520b03428943d041c54010b01103004207200a4961a122440000500c40035030381210044494001500701500041515540d41700d0746e04c414458003041081c048a0008091005e802c02c4050980240300c4603200c1c20480c0007291607100301400c015503000561045d503940030340c9200b150800d04070742110247d41c1d104c0c11202e0201d014034100c00e442c01880070742010788980f00d140c03c0542e4000480001e040c058288800c0c0360 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 920125278 1250 920124028 920124053
    0x30822080d0f020d090501170901060b0703050405090a0b101101020c1515040507020d050c0705060c0114010f0f050103020c0f0604080408012009010c03030e060a1e0504030e0d2409 79
    0x1d08005c03001d1130900441c0d8100481004801d0200c4003c0741581e038102e1041c2c01491076070410240000f0000707515003459030240c090001c3e00c0701141c40c0c00e02911a01014001c40315030070022500b10b90510a030100207401402c000f845110780e03c00141c94a030b1902480c03400c0041c9001110b10503120103060040301ca15858903802c4070030068400b00b00504102d038020350ba4403680c0c40d2010030030400007041040b4400600c130400c0144409820103032a0f1441440c468042c1100380e03401d020310941040002169084038800d142203c1c210b02108446c241007200441c00fa45c0542065860352042165001c14440b00b0800b05114500031452140c45900b480019420354030f4505d00f04170691518403840040004a10880da4510024200556a2059071406501801400091308110300070f0408100340302425070008880210071190200d100c0c014800d0700c404483c01910064001510348024041c14100f07a400958018020044840d11010107400d9000d984c0e4030801440d4140d444c1d10a05041001c88940803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 920126528 1250 920125278 920125303
    0x6060503030a1b0305040e040b090c150a14041203080702250e040501140c0a0f02070f0303030504020d05010203090c18060d031d030a0807020a050a030822080d0f02 72
    0x20741c034100d001040107109481080303407940c44101590202c401c043c0510112801040100b0741d009240c03500e0f060410300c0031000c44101250b4080d0514000d0549044181c907100d0b07081124042d0b04101b0b0540040380c054965668216a420080001107641e205c00f001000d201442981c0c1d003042490610402800d001c4880f008041d90300d082c52904240080849401f0182c03455280600b04c2ca60300c41c10042d015200003001e50480390781a0043c41460b982e540b00419001d20262a078030394422031103208070b0b070f00e28680c4107103813100703450715400d00000b03110742c000c0c1d07411500003000e2000e05891034840d0b908aa10a840ca42010b82c81110312518034203040058512600e0b04502c4014145007030700110700c40e0303408120000c0401070480240003241000b610040d42c0c03400084c00322541c60520385841422903202c0c050070b072712030940341000052070b25110107104c00341c03036200d1591814041a254070382c0280c01440c40044d440040751201186070743e820042c441803403030241e80729510080079000207800c200090442c3d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 920127778 1250 920126528 920126533
    0xa180e01111602040903030f020d0614010504030c05060705010e061006031d0d031d2401080102092d2d04020306030c010806030111160c0503010522020112150306060503 74
    0x14804a260380b036070b148100d03540503540071407000d40d149002c400170000c4005082040d40b002c00c1d15840b4000941c4010b09949010785003910900000c5c0040d643c40c05584801000e0000c403410a01c83d82c20030902030004144a10004128425600981418a0300842e2540b10700c81880b241000039036410301442070160101821001d0f41030b50f84418a80382d10000d0551010705840f05d4031030040195103044640700902c54803e4580360008400154141d820011661450b03c02d80300020441c15011b102326100c0300c50090100e02c00d0700c41584c0100303a5204110700383c000aa880402d03402951280c0d04c1c450341100c070031408410302400c0000c0c01c00d000c00a8428080c01a03206004000254800280c2c991101d142400c0c82c50041c2c0e204400a03001d04a640340d0400b40820109105c080300301d44003010b029452060599012041d1a042854203c400864070410001c03a04161034407460524594075403c14010315040149424504045055503240389800d0b00005c50540204244170303140c400c0c01c0203020101c1c003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 920129028 1250 920127778 920127787
    0x310060309032a05011d011b090e092103010603180305030a02090a080109060203040b150102030a054605090d0b130f0503030612030c0601060e0a180e0111 68
    0x600030f1010301c00c0068284842e5a042d04240030107042c0100201150380034000f4040010031100311a82d6140300e402c050640d6080904010079150150000c0041d0901965000f909600c0e28401c00001e04024102a8440c010304800881c4200c1d081c0b1800d00d03280ea502c035030507500e5141034001412507041600700f200c00d180038204040000c1d8030404580c1c1084030307080090385441d020000501111411744c018400b0303618080c0c1e400b0401c29680c01451080f4001c1d0321102d0306544004101621a80c4084142c0c0140c00030404c500740c450040b0058030100062407100000c010700b00c0c0c80e108074118080c5182000620a00e10281006c1e201000200e00d0b0340701d881c3c600c0c181101070700840e1004a021038010080840c6100040c840400034500003d081d03000300345090704a1081c144142c61b0350041d14464001c1c961880c2d00802c00000000b254000a0088014000d6030320305441212000707110300b40c190f40f020450704006444240003068110a65061000007441010300c62810b084030071100e0641002d000501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 920130278 1250 920129028 920129033
    0xa060c110112020f071a10080601030615031e0605220f050c090712060b0a0e010e0111160e070c0f03141204050318040519090804030204020c030310060309 68
    0x500a00c1041028203140c8901a031240b440b4000c0e003d01165074601c03520101c2c03c401404800d100300b020035680d80c07500056648955405907010000707800b03905101d81c44200104002952503121161001004440c00819030b26555100561202000000b018041502680c018041c0500c1484c1c2c00c860783c0a000d80a00200040788080100c0300a0050711203c4000003003428000306100f4001c0c40d14005000c12a640340c15400502003051051035580320f9031600d500825001510021510080300c9500c801c1c07421041e100045402020340070409042200601d0b50418090041140d07060030280c0c40c02515603241000c011410202004080204010a80008001140c581514143d04a405241c1101c499180000051f110b1094a212143d1481c21204000070300201201a05440c80c152000014179861802000240d410640d10700c0c0c080600c400d090b0705c00c10800d600c801d21192242c5000c80c03c0594075000a0200d0b0000002c440c1147c0001040003035441800c28080081d0003542000c004028654 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 920131528 1250 920130278 920130293
    0x19090e060a0614061c180302010e06062211162f0105030709120c08010e010b0f061602030f010213120305030a021812010e0709050f0f0613021204020a060c 68
    0x8a8009026000c0061005c0302659403082614850300310503030500058003241441130803094030310b038142c0c0194601241681240300c041036460040c0030040c04da2062079280c0c5455154480d030f0802e928140b9a07a02e80d00d04442c00c13500003401da00000a0301d20501014039003044403403110405204003101c9031021448030500040140d180c16039200386811503ca640388081601c01c440984c01030031003000464a040100b0503800c0c210400d444c00000244104410134101e80c0c207840c615424164008120001c0c0280790070044041d001107000700510b0015402c0b00e0b00401e0428024030403482e9943d40000b901002d80e241242082c00608520f075078cc2d08200317550307200100203000c05040d01a009400040004170b00200c41103540f08103900800101c0d0030113407400c0c4980241401201c0b001c1d680500c00d0006003c0b081031050901c41c081e07101220080d40c4e05d541801c6842c80300103094907484404001940070804044c4040d296003094001404500c1c1401e004018824005a02c4a010030a41400c1c40001401d071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 920132778 1250 920131528 920131559
    0x7080a05070219080c01030e010c0801031b090f05010504110705060a15050907020f010f0902010c0210200604030206060d120c02010905040e0c040b0d0b0f0619090e060a06 75
    0x1a180c4640c451500348001040b40e070501400800800b950540443e0640004c1084030440e6000d80b4200420111080040e007650a641c0402010902c0040104003041847c51000c60521030709510b0049151641408421500e90100344500c4030758620040c002c5050a00c982110f00400341c04c10380c20511f00c0d030346559988000806d060429921030000140c02d5000b41210000307000010310107162031400c1c94009541354030703640d8140103640c20401d400301c0c2c0da20b09100380000c1580682d10b02c40e0555050302800f04c108801141c041c00c00c107881552400013214041c0c0885020154400361071182000d040007071138a0006050b0700c2c400c541100c4403400044a0b00c8511041c80d101d400c203003000c80b00380c0c001606c00e0385103640150b401900700b44e07000306843d4000c00c600f000c0c1201280c04000d441c010100b84401a81c6092004045c0101c01001c2103a85102e0400c8603445040280f011521f03560440b40160b03140b0441c1d1050002680700c40c2c124400010500c11254454144282004110f1030b100c540d1000080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 920134028 1250 920132778 920132797
    0xe100504120908070303140405060a030f1d0a030c140a0804090c02010c080103060b010e0913021804052512030c0b18100209011b030e030d0507030207050405070c061a040b0301020708 80
    0x40310000c84500c87e100d81c1a500281070003003419880307203035440d80540949500790006c01080d01c0d0842c1e8114450410000c0c9520203000c00c01040101c1d41035405650003100301c041503030039200340d049082041c2010092111460300c210216a01c5038030740100c00d000d454105c0d6021095905010100203620b40c40b6a4540c1103c2d0085004501ea551260040c0c4402d08400c0b00c03682c00080314800c220040b10340040c0301030811301c20f545a28500c407005070200c40021f001c1d10f00070006d80040716460b02c040c80070800d405500b00c1462414184a90f907045482c00d0404c2100d0441c081103040340d0020503c42c01e4440250300456188603c25030300c0703c0740f4195482c1c4088a02c40c0d001a80d002c00e00f201640d124841040f0f860003050b84e070756020061070a02401103e04a0b54091191099074401d0300c11520a0003a1902c00d54150007c000d00340c00e0104220141c040204500200b000c0510410b000c160b55024050039030588840801c1400083d038140810340c1c0c3c90303100d034600980c0100b0401000681640841d000501c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 920135278 1250 920134028 920134037
    0x3070201030b12100213060507020d0206221517100e0712050906091c050a1407120e0f0a080303061014030405030d05071e120e100504120908070303 65
    0x881001500d081880c40100c0f07124400d000c40311640004690050003030a1040b01c06807407003a07581e1811109885607100c004e42020480c0314010041c1082c4010741039160815604440106080d0340100707403c8500d900206600c56120201c5040c540c001d103807406600d20301180950540340150486078a084140300d00700829041e0800909a14810003403000112004141031205013040d41d000c90781c8600503214401d440c059078603500d5480200800100c0612000d45405046c250051015509110030701000742c5d51007420000400003903d400b041142c100a9519403141e000300c010203022150803080030700c9000b810228814011804e000040d40e074895401c6840200004003141c0440c2d40c01080409000103040c040180400c1001c040090000030602c07041c204465030314018221116081005980c1c0401e1003030044030a40da22a0001410b2100d000002050180c420001c1e5460500100020004103603280140300400078141310140c01080d81c1d240c0b036010542004407041e2144090b00c402024407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 920136528 1250 920135278 920135291
    0x50c12010f180b0c131e0306090803090f03030112140709090c080118020a0e0406140106020a03081b0318150106051804060605092101180c0b09030307020103 69
    0x200250031200180704500030500240c030302d803140900e440c004a20220b412541620000b481d400090094400181c0c01d4201c03550710603e8516911520151178810300e040d14a071980c00700200c0c26500481140a2042c1002903683c40d01000403400c110821240c0205a0001c0004001c0200c2e154100400c840d0040a03031a8122601c015042c41d0164550260542c541054410320a0013032503402c060841c0c122100a0006480f0158200080f0a038517000a501c124408001d001d850581c6c20b60395841440740400140b90411206c814291001c26405080141e101d0400c105c101503220881a400c045450700d420900742d20708201d0040c40c00010403008940880500c0c43e203d1850801110411b20480040022296120700000b00345e94040040e040d0034150310281030a25041500c222401c540807a6181b90902054404000f958500f00d0114000c040c0650020701d17078101d00388503a445070256504000394007902454042d2080c0a9580180d401c00350900c0142207986010040721441c603030901c0c000488 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 920137778 1250 920136528 920136559
    0xa05090d0b0109050106090b04080a0f150504050106060207051903110102150702070e061903060c090803040807092733090303060b040b070f080903030d020702010905090103050c 78
    0x4400e40c0c801a1107421400000074445905901a5060311441d54592024a440b803031600325520581c81620665070007034005402160b03088408000c1d00348911150b0320a0188130001405599007a46c083e50f20b07942d246000c000c1c00d40c0400100300106001d6a5030a100f20b20344010070b0b0b0341c035418031001d0700c140401c485094480c1c0c403d12124031290b0194040c211203040c41d290080d81c2e0350940c09402c6900d00743e800410000e14140c1000644013001e250080310150540d69480c01505141030760340180301c0b4101c1c010801d03420620103032002d406034030014102e40d07182c80d05000030740c2d1440105e0840ba08403000b003550304c0300f080810035010035001221001182e00100708041c1c01484039071104803100f400090125021155040000d14501030356050018a45401c00821a4410741c42000350100c0100200e2000a9405101c1c1010b81c0c0203524003801c1c50581000300e401c0d41e0020301d004005580c00a00c100c210340e0004940c40c01b0304800d41d0f41c0003143d03040d540d40580d20200740986611078040294954003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 920139028 1250 920137778 920137789
    0x108010e0403030608060a090203010c050313030e06040902120906011a190c0f03020615271305030f1c0c141303050d02150a0216081c14041b03080a0509 67
    0x2410004100c0c6c541e0300d40300306a680144440a0221f1080d420f0940002c6420302c104281c90140020048a000c507140c9540c05840c1030321002003083d00501c081c070000444800a10203415168060038104045141c41c01c2c0e12070500360140c010028405007006031080501800b01590018000c420039840d034640580c809403500400340500400d24079503018203904061b030200303041c5e0182c0c10800443e40c1003404041041805c00d0031a550000c0040125030b00d0580b5800c5040d403540203a044003011903400141c6c0c44060035641b1800ca91004010001079465400b0503444880d11b000032048820032072040c941c00e00602501c028405050302d0603010039807024142d48440c00c1c40082d07030700c8002c4592072501000003a458440c40c9451013030403000c4100244c0315801c60b00031074a103e01c0000c490700c240889659074024035004400e110000b0110144040030384841449610360540e00308003001c0c00c0b454140b0b0310940c0031036100b805400b4611068010030020350020245e0303003428018200300f501d030500c400c0443c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 920140278 1250 920139028 920139041
    0x5070501080c041a2a062a0c030a0909020a0509040902040b040c020d180e010b0c0322150e150f070c140f10020a06110c0a111002010603020108010e040303 68
    0x12801050100d4002410f8040041c104070644640c401142c68404140ca171802110705400490794004100181c61044218240076945180001150714004280d00e0403010b078018076007098865100145080e665900446608000c10020304190300d00740c1803400040c054020502c07440c0c05161522a8002150381710741115194180150080003905d800c000020760b01e200081d4201c0115085900320f0003460300544441c000c0d1550541042c5035a440d001402c0c055034007411007010180414007551001110380d0038500d400d42e0a484182c2d282d141410300340f03900607105412410a0003241d2103000402d445200800d071480f0031641c000c5454400502842140f845650b41c01484814a10008030301c010f10210095900c0360161840e154000140301806440b0b800402840e01683c0401e00780320000b040d90300040c40d10090078001d141030a40c440300c0c103480c3c4888464125610f003202035140c01c150800980004444040303100074801c03a880c0d074001a0951506001d040d00080b030b0900040c0505000780c0012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 920141528 1250 920140278 920140289
    0x2010320121b13030b0106030e030318030f0408070e0c120f04141609241401170103080a17010f0911090d0f0605060402030408030a0b0102010605090a02070311030705070501080c04 79
    0x96030382c0c414035069054081550204585185c485000410054400c5c0b142d01001c3c004000118a151546a07004225a12028407502644010800341303190300102c2e00a00000c01602004240c4a0308041441d401c0c4100248040007100c024041d03840300506640c0032a4000503184074001d241e4030b903401c0c202d9444800260425051040030500d6203800c4034010068100d440c085805c101c0c0749003c140448490010030113000002a645105001203d10304d20400303503072401414101e81c084401d0240904a0b01c090380155069600031841e44895600914a00c05c0302070000095140c03581007110400c01400f8600034501140d0f612008080e444200008035041c2d404010b141c4c000c10403181c5402ca0001c06010b0040700c00e1814500070406604040c004d503800341703900c01201821340d690300c241c1100030070380e5041040c1199203c070000102e036214000154046e07242c0b03c01c003682d20225410064960306031001c40c480c5d650b204109080100d0303000703d4007000703456092802d0100d68417442c0c09070790305004e1500704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 920142778 1250 920141528 920141581
    0xa0b2206051807080f030a050d020d050a0e10050f01060c150e0c030d0206042d0f110102011401080705061b06010f090b0105090f091801180201032012 66
    0x41c4070b150468010200c02400b49072007200d40d11521a410709480d0008013202c42034562003882241c104c18051400380c040030485080040c20f002c803030f0301a5000d40c1c5050b5601c0d1001961030341d1199a43d5802d105111480301404c0050100381800c11107c68507010522480c2c04005c041d00e2200c0c100240000959200d40c1455000e200364801003821a4443c140114110b10910401030080b00c05400420b00501c155004203049440304561201c02904480010b512101c007014054624000b1301136400360039005002d401c1110488150a00190031030340030364408401d240b6800c0042056820000b4841e05031407090725680d48400d08141c2c0c401486d04034080c060054090710b400881c0209000211000b00c6602c9075050011410300341c01901c81d40b0030341035801d070049a000444407181c24000c1c4503a400031018820300f5460221516642d08490f1110101c00d9500070b001c941c81c0c01e560f814018903080310b180f03031246112440301c22003408240c8108810301131000880b6000408110644003000002c0c24000071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 920143884 1106 920142778 920142781
    0x9080703030210110405040c03051f030c142103071a011202040e0c0409080c1c0f0f0e13050a2f03040c050a031b0501020a0b220605 58
    0x100c011007513004001c002466280d038412004402e00740e590000311030a0a41d500006d0340900d00701000101e2401c00d042c0080381e0b240c0204000c55144405809040980b900843e1221544183e0950810b031006050200da103008001441107a00c5021040c2100c00a4207000000c01c00a02505403001050480407005080c15401101040031b03520807648482207280005095a2000c0412a0008800303da802c3c0c8102080068107903441e6a040b1180310456036510050400351541001010040c00d4681200c4040c0a0600c5001005010300640d616105c1c1c041c4000c040c03c02500c030186903d1404034030820f14203c2441c00c0b100c0005040489131003458910041c01c03250000392060321a0008200000f07440e0b900c0c0003010004511075a602d0310303180d040480c503c01a800c0f44d44100c0c15900554907510004003182e5005a0114240c1d4581215001e4407400410010b409540104890318060 = true := by decide +kernel

theorem cover : BRFrame.Cov 919964028 920143884 := by
  have h0 := BRFrame.cov_init 919964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 919964028 ≤ n) (h2 : n < 920143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
