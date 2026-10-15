-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4873
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:01:01.126313+00:00
-- url     : https://prove2.me/submissions/91d04205-19fc-471f-8546-9e83680f604a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 876258992 ≤ n < 876438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 876260242 1250 876258992 876258997
    0x30f1b0f0c0a03080309011409010906051506090121020a020706031b17040311010c0507110a06051c090203011109010f0c08030c0c190f02010f050c0606090a20130902 73
    0x8a0303403110344118148085021325014540c4613007000000201c2103048160f80c806d5201c1128685400e0b0345490038241006464041c0c0c50f001005001121320710340701d00000981e107016441c10541005120b885100c00300011410540070000031110440d51003c080790000e4413400707240035660119041070307520350082c80d0100459902c510a580c41a640030507455011440f010044c20950410004000e90f030301c0c801003842550500d0311076841d455552002460b1084100b100e004003a44105480d030303810804140c103d4116203d440c10300b188001c1411080c0741c0c5000034086a40301a406603c5d0801008500c11514020300501d542601c0746429042c003000304445604014400401c0050240003103269824541e01921400c2071400603120203102190a00c182c0c2c401c050000d8030944c40020344013096580024200c003103002d07140f4090389010042c95405030341e00005001140a0682c1100164251940c3d80c07121070203a9030701c0c1840844c2d41402c450350072660000c84007a00c540424000005000703005108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 876261492 1250 876260242 876260263
    0x3032110060503010833071e08040f06090f051005010f12020a05060f04031707020a0815043003050106030c03140f0a090b04050604111806090702030f1b0f 68
    0x811015206030010005846d124550b0b14440202200000412960070750b454400e09180c0e40302c010034452810002e200c40c0c400c18500c001c0c4800300c000d01c804210304208845850390804400302d00381d035451900c8100c0030a030b41c4000d0554015107080042c42e140301d40040e8100c0e60300000c991f5140e0748915841c2d070340400c828002544440c0b1200104141d050580150182454855007141000d40d25140d03c090000031204003a91800009510811072406c1088100a010844010b0011240540c882070f680f80014001501c0c90001d2200500c0400c400110042a1400d0201000918a030004080d0141000307000342c4001c81d0820034412100c0d0311a1090f010f0309080b03d035004d11b203602d440d084c030903c640010340344000d950b44452008020903007080c1c05a0140b8859001030059240c070381031001c103015014044510641c0c5404840d01c004e0a45000d80c0c0e00941e04071124001034941c100e0507403440c4100f00c0000c0403024003050140c001074140c1c00c2d90b20085107030700a40314581402c09400f43ca501d1640c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 876262742 1250 876261492 876261509
    0x2a020a06170726100b0f0702090f01030308011202040f0e0105070f0513181113060305010f050a03020f040e062e080d180f142713020303211006050301 66
    0x60040c00c3c064401107032a001046060055041d64a90008505a501c030030713948203002100040c5030046040029045c3d60092a641d907000c0b072941141da00408098040c0b04044028107003001a205640d82e69025941011100600304030441d00818054080c020440e4600007007814904003296550052003100e03c500411900203100038100f86105080050f800c3d41d1010705c1d50b89500d4041e101d954107000b0580141101d0b408020640380520050585005030403c62480220780401c0085403102207156050725030480d80b00318142d001e500440d0003404140f15803022072080ca002d002c40e0303448800c45454112000080005c04c200d003001c3c25004a1703407520504101d03501c0080c40078010344c481d55843c1940c2c40c42080c41009e03150f4884460402c1e00c8903800015034140d0500208405142c41c002c045200c00300c110f40f074940e80444c0d07000380c01e6a2000405100ba5501680e4000c01155424406c66000788000309201115100000603500071200480304010b2041c5203403c00329003140120142da04950801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 876263992 1250 876262742 876262787
    0x301030605061215070f14070f1407050a03122303010510051204030f090e0705040e01090e1f0608060103050d1115061519120f060302012a020a061707 66
    0x4040b01c404041c44000350410200c0c200c04c0394009007c40080110b94000d002c0e0002c408443d00b030402955035095071a20b019802100200b09541b12014040220398000c04044046007004200f0382c0c6504581a40070485041c04421600c145062000340d41a10819181400c40c43c480300801e440c0c91192480d02815090344000050000703100314546000c40070185444e03400c4503500d441c6149c000400f61125804600c011805105052400c00c819004101c1004288020715400d100d50b0703140d0003244450761079040070010003010891701d5000100100852800c440d0b2071360f03403030508580310345800d96a8000189902c0c43c0301c0e402580010701001ca03c402040c04805034661004000e00100345641c8480b6422060040000904109008039072220030358480c1c52900800c840c3c1d9204a13a600c1000951072403402d1810b10140c1d0b8456421200c106404030b00e5000a1217041b444031041c200010001d50007007503604045540c0c1d0f80152000061425110003281980303450304241c03000900d4004c095100000e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 876265242 1250 876263992 876264001
    0x1060614090f150304080405090609160807030e030c03030a1503050706080403180611070e070e09060d020a030302030421030804110d02190509090601060504290301030605061215 78
    0x9000e2402d1040002001c6080802c40c03040c61101a80080b5410341c0d040c28003140402c40b0f4103041c1c4009074414000c9074811501e03d00a1010b030300040d018801c00040003c46800240b03014081d038428003481c00210212a1200500740d8071503500d500450304c40c259a030034400c004c1c0454804480250540c3c0c1c0c403202400c2c800342003000486050310010401c0d400c00070480c64070700100340c02414000180c10395a0f11141d240007540c912034609072141d40002d10360101300e41001801c1d079108014480060088407100e1803501ca280005105049003d00658003500c0c0356400420950004014000c0343c0780310b03440c8284c680000c0c90b45003003c0f91211000d00070495000020b40041c5640c6404810210001c0c0030b0034240040340c01003003088042c034402040020505200740150f1a103581c01560100641c0c000700059070400e07500405d42c1c0501d20400c80e548000300c00c45408800e02c803068a507a032500040301901c9603502d0909001500003a50400d0140b0841c407450b10160720040303402d150000250000b99890b898 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 876266492 1250 876265242 876265249
    0x9060506030c040b0a270305060601020c0303180604050a0f05190e04021c1401021e04030507050d030903060f0506011202070f08030603280b010518010e0408040e070f020106061409 79
    0x482c40c911004c000030018111040d0406c9603a900c0c08041c58004e100080703085240092038000080c2c2642c0c155481111b03442229a000004c4544a0800000c1c49000084404c04601030b80a281c2000ba03224009c50710120b00343c0007500d104401c07100111084902402101600c0d01c08218902034000b030b480e01c6800003130140c20000070035460001507102d520500025031300e4207090300032141002c0c007a503500090700101d1034800000640141040344d42c002d14091035270b0b07200f07551440c03681b282034018090b80d88044240360181c0004030080da0072040600a00d510181d907807000f0071084031843c0c007090750102c3ca02044401c43c4243c1d00c107254060b584171300d4102c0075110425070b600010b0070194984500404a1100307459802c4e0051500c0d0b00301000f80c0b041c003207480c042d07a020f0302c160000c900403000c0021429260a59812690454100c2c084c2419291a0790402880500c43c0e904030f00710921074a0144900300703034081480b16500403141e0080003600d841e0301048402051005400300b07800307800d1108180a24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 876267742 1250 876266492 876266497
    0x307050403170d020c060910060e1501020f030c010e0d030c0e010305040501020c070f1a090105120a20030f010f0503281208100522020306120f010609060506030c040b 73
    0x82c015072124100058151500e060380d00014414103030350040428403000c071404105400e141d813011315042c07140e03070b042006800c1da0340d000500d9903003181e818031001e0740b0302d900902c0080c8040785040e041d603590b1044680068040c0140c4d41c48910140310300b42c0d80c03503080c030b10900c40c5000100032951504e40b0300b4034000044000c0c040c0900240e88655082044182c0e1910410404008003c002901c0d0345041c644600810181c01007202340509610400c5042c2c56a0703404001c503005408402d100c000c403a00c03801100001045600b103801090f012260080c40a00138042c007441c440e865441941d522aa00e07602c1c07083e290a01031082c503401d64000704c030081079141c1c001c46c1c85105818410000c5e40d4050300341c07260015803000b100800d001c241c00006010587d603a080d2503001401090340c45039044211000c44004521925130183d11841e40070010603403954900000c0d10f0400004400c0380c05c1046002c076000e0080400341704807036030b50b880d000c0c0004203402d103402520701c2001c034084d405040501c7e00203d0b03405039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 876268992 1250 876267742 876267773
    0x40c0311221a0a0f0f0914060607030309200301051303020d050c01240611160302060c032a070e0c0405041e02041409073b0d0602120c0307050403 64
    0x1403902e01880c251030300c81c4a5010b00030140404641c2c861454000c0503083c20245400c0f0003001414100000c005600359600e082d00710f41e041d03400c207959286905040300284600036000f44040aa9055061140f800c04000c5403202c3c0101c0081150362640d030a00c08004041450040168000c4a03a1044150003280900f85c0c184804c8008154941c001d111400c3c140042d00040d45c0040d0040c1e01401000d50210200a6403d081d400405261918043c40c1d01c44036602d01c0024400d590000b5040401d1105009440f9044103041c01c80c1e81c501160300b81e52182400309401000288620326002400b0314403c10340d40c1c01403000d1254a8a801c0c10041484050b1031014150410703001c602c81650002d400500c0284003d18500140c00c1010811104104103400064800b504002d20000342b00c0d0b9041c0c10080340304030300c0d8040900d035940d90480901d8580440d011642c0580c424203190301102440025001003988804603146070804e941d80f4620350909000c1501e040340012001d000504c00903540b81d0001c101e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 876270242 1250 876268992 876269021
    0x10e12100c03110c210a0504090c09090905060106030b030c18040602070b01031104060e01180b010e060a0c0b060a0602101a06031806010b160605040f0803040c031122 73
    0x20303180904403c0d00c41d48000000ca03c990700403029584a1400c80c035030f003011098200c20062410400c0c1c07500038201d00441c00384045660303403201203030f400c1d50040b1182801418811400c0c4000d00540c18010384940003442039101090901071003a0300d6250200d013964010000a100c40030511502d0643d0303990880081048406a508210782d20110301d501800c0c3d8021445001c100d44250000014030040e241503901c0002c05002c08401408030700c01d0403610326800c1c84401d9000030304100500049070340a0440f0041c9821100c00551600c006034030001c4041981c1c02031402250390348400c02842100766044c070400300144c100840c45d080d40f41580d0040340e491100502c075509081e4481c400614154010794501c0d203144044c080b05500f42206101c91f03401041004030b094184502d1140d101c08440b8a6440186401d50340d0000408010346e1004030040360ba0850341c1142c81c2c0c5001d02c5c21a041261500095036032421104039440e0700c0c0350107040110015803c00300206030581c000c0950b0050102020428070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 876271492 1250 876270242 876270251
    0x6150105040609061d19060e060301030b01050906030111030c0901090b0903120c0307151406040e120a02120724150e04140610050111030903070b2a0c010e12100c03 72
    0x2540e40d450714002c500f400410130b0080c461f4542038001e0b00c0e180c09100e45502440f01480100041604442d402c1d04445051b111914966a0000040c1c0103100e0116405800000842404032494902000e07103000341007a241d20b6540b45d00c41e0340100044c081d080c0c4241d40f603132003407076000c10340595980a04041c140301c0089a0a210039541c4d000004681500d4501c1185d9442001007451001242c03d160021000c0d28100006001d0100c02e980300c4469078103010241800050241d50710b84204a0166050700424500e038039003800789400050070031010f0100643c4c0144a20903403001520344503d04002c1e02031100c1e41481403502d40d540c1c08a4030000c10a88625000400111018005004507031042540110030403855007807600240c00b0100c003200b00007040e8400d00100d9510740303002621000791013108829548a251040c04600034050740c201c0710303014460703030300024070b43e40000110081140c1003601c40109405030041400050f0b0b0304070040304610b90054500b2400900b550340300c0700a42000c7e140c08903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 876272742 1250 876271492 876271547
    0xa0c03090b030a090c05040c17100e0f0703231f03021305061002070503030912010b1003060305011d100506010509060708270d240e0615010504060906 66
    0x15401d0708203d450380092a10740300c0c0c60042000050942000d064211800c000d841000c0c80001c1c5072941c0308104010281d9208046200c010614005000601081c6071551040ca4003040c1204040420389440c00842e051441c01d1f10715102c510465001204400d035034200542e6090207580d2480b84000e1500900c5001c1e003c0031000da12045001c81d5a0244103101280605291040c0b007a811460310740d440854100c441c0c28030490340c0200c112001d00c07004076100e605c440d40c12fa20190041090100056010040a002018154058000004581c041c10080021040c41006594208020a2080035940000d0707020f1500d05041ea12881d00040d06140c030318103010600c5d01181007580700307070401c0c3c8402001080051913144404100003d01711201507924090000401143c00d2801008008044000780e90700e008840c01c5404070b075140b140980d1002d01139486e0072543c442e200d05040c0e8002030b0704a0020400c040f55401142202c0071900c00380d69080e0800d14000d0300b251074070841e0ae4102e038000c2c0b05140c0c20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 876273992 1250 876272742 876272759
    0x21903120e0105040203070f140409140708100c0e060405010f0e03012313020117090a0f0c0302010807080105030607120b03010c091d0108100c11060f09070b0403080a0c0309 76
    0x71a0145000340000480c1d041c98010146001003640c4422000240c2c400d05004980912007114007403101510007240c41c00c2c09142c120313043d1401a40100a034401d01e0310020740103d0001e6280e605d101500c204010301c50b54504220f0b441c3c010140c900c0d40241c000c100401c07040d4401c1e4451842c20000386451810040200006429600350810743d482d414070801a504c2c1200120000c1303074108074905c010707400c0941550700203405908149000e80140c804040003501c100b0b000d2108846059110070001c0c4031400038602030342211400c1c00140d00259840d000184414010082681030b101e00400400165444905c2250658071072156082c071076407a03040d1805140c60900424001c41c42c1038032940c5040d0b090820013141c3c0240e0040314200d007007980e0010004c005000c00d4a07050b00101d0b5001042c0403440400a0700d070320680d05d9289209104950030055450022418207000302c1a4000340e170304050b91540020418040ca0201801d00d8104000380d030032190242100302c040c24030074205450000c1c1e40315580d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 876275242 1250 876273992 876274001
    0x6050d0b070c05010911030f072405040306060f18180605220b09010e070b0a1817010e0601080d0518031c32090f012304051206040302190312 62
    0x1ca4100102c02012099071805019480c41c006e0030700010724485250800300c200cac0c0e2010400356244020a81c01503020184140222000742d41c02801c00e00c1500d9494040828694040c42252a010098802408400224041e00d804000e8460b0740544d91111600c0d060000c0c000504144074503840f12103503080d005014012480854004e10800b01503240110701c0f0340c2940c20a1800780450b412112051040070340e0b24041d5010072030203103000300c3c5544103007450781622820741e0041203490b04815072110f11140150806513480c1c010505540305030742c0e1525519916a8944410808101c0071b11040c00ccc6d540c0e01002c2c0919050006007190a451117074044484030144c2aa2060006001410085c80c20b0003610405d4451601440445103400002c64071121207001d000c800501c50390841350040500d0380725101c0c0988000800140103400c1062500c1812207a02510030140500d1038050440400c020114040d84940c0d0160054254034042e0904403a0505044108600b808100903040c15404d200303105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 876276492 1250 876275242 876275261
    0x1b010c030e1207091a0a092304030203040b0711030d020c01050f0c030403120215060603040b010303080603070f0b0a091211010c05160905041a24040b090406091506050d0b070c0501 79
    0x8010f22030300346240034411043c2c0c0d0740e04000750490420f0080d903045003204081d101140204002c49809889d503250817800c1d48200d0b80b200c3c0c035400b00031039600c3c1403003c00342080c081c40a00701c007114000700d111803003a0b887c0d80c940d07c03850b80072900500900180c0550107000348100b500001c01e507071805469651f400c209244100140006038400c142d580c11705180f802c880c9812401c01c4600d00d046140656660460f494140002070403c40300501240a544040114a02600551a124000549510040805030410104d800004000501c0028003603000140c0880f00c40d0010751480d04c20341d02000540c1c003509110b03411070b042c0c8500e114800e56070750000d4209024220181d400320741410541012076414a24486034210030354900c1c24400c20b027824001442008100c110718039651504040004c0040c110807003041d40000300d04e030401042150790341c1300001d05442030a130f107680c5000c401c006804440310782c040c054000541030387c40b4020511041100394070020f940f4207006134020b42c0c6c1d94203081d030381c00e05c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 876277742 1250 876276492 876276521
    0x30c0206011403070306060b1c0501151d090c03090c0402181c0f050c0a0816050405070c0209090309012d0c060207020303211e0c0c01110c1b010c030e120709 69
    0x9014002000c01d80400d8006275604200b4000c9504108a958580003101420002c0c805808810280c106030b11002001c2c05400400004007460f01300104c2c0b06c503a00c1158a02814001c90150440d00d113007900c00e843d01d00c84150080c00c0c004512106010324650b404034200c1d0482d05200c40000000d040070300400c0050310442c00b4020b4540920f0900c841c060719a00526031903044503901c000c103a813515120a0441c1d40072240490148c4540c24143c6081c010b040c0003a403c080c0741d00c20007007080000402010882800c1c1d039007040002d4086c440251040c0040c8448081c621036502c00080184200e207140000c500802c401454001035500192940e0b0002c0303800c01200204421000458840d03403411039112800240104c101c0c006411f030f8020641c0c005129460300b20010600e00c089004c258003800f81e050b00c1d4a2541d139102d000154140c1e9030304d16411050003d00c450203410390f603548180303200b0710039a41c5521401510800101013110140382c07030340e4000f5a807040c0c5500240d10009801032001c5100b0a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 876278992 1250 876277742 876277747
    0x150117011107060630020d0c08030d0b0a0b03070f082809110411161a100825051c0c0f030b0109060b190509090414010c030c0206011403070306060b 65
    0x24003241e0003540000ca580d2103074411701c102190700b03480310025003d0f0390f0704440407514031140317141440790350900d500014098440071421600c06103071030f0712101492000b11012607406550740d01035841ca100482d142070001302002c15003541280241040b036040407410410800f000c0c48c00c68154004041803605007607080d124100a42488400025000310100c00da406100e41e1600c20728260180c8990b484000c0780801840b445400c1c40040d500c0c005101c111f2404080680c01c1c0030b07010554003143d074010a84079024a03031584419480c00300140d008404403a0700228138900d06000c0150026040081d5103004140c260100002032808900401401031240c1c24104e190460800940e1900140c0109500c00c1c6442001e020303098514081d1254842807046210b0b00c4074810340215900e0044001c01504142c02100703100411010062000c07030403038003a0081007039502e4040103d040d10b1040200d03401507041500180302c40b04d48180c60345800c0380040c1c2265481303a901e540c3c600c04c681c4954007081c10703203401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 876280242 1250 876278992 876278999
    0x305030a0c06150b0a0e0109050d05060402090c0c060103030e0303091302220807030624032102030a0e2710060f050408030d02030402121504030206091501170111070606 74
    0xf8400c40d002c81006a002402c410705121500790f4522803c04200180300e5004505a0180e200e58145405001c015051191160b003501d050b070f030b8502060341c08900c07c2414400203403485040b8004c1e1400c040b0b14200030303e441e903e180c034160340c5840d04021240d014042001072102c00c0d00c8030001e03256007811036003005035a2004003400c0e1100d001d08504258003182e42c19410091054001200010740b50402000035000d0030b81e013040c10440c100075143d60700701c8803d8800001400500c0780d4182d0180304240b180060b6500e0000100d880e8030404080c10041070783c2c08001d52181c2008000300c1e00c030240c0102141c072090640303903030302803103050842d040082c600b5094414001aa4083c1d003a014100312400d104d410f10b4203012000740c036401103803900e640071a80440007409540e902c0c0300a040740b0392043e0035100e102d40f550884003a901c2c0121000e40151041c0d1000c1080071400180d1000c4100c400c188c035200607400c00e054205104400e4800f007043c0d40d03c458400080c00d2110700182106482a10b000503041c1c034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 876281492 1250 876280242 876280253
    0x30603120801030b15010c08090a0f0303030c030c0305040b0f040212030d09021003090803010e1b0c060a110405130207110907020f0106090606120c1206090213080102031512070305030a0c 82
    0x74000c00d20314010202510380d40d0b45d03980003160034030266802010540c417090034401080c09180c0d2075000002d0040c8100e4000705058050340220b821807040e60741031148440d51742c415015200141c40040011181e0344c0004c445000403040260450310040a18009103880ca802c103285801c15810000c2e503c1c1c2d100e51050451500300243c40d0801094102400400a00e0300c0d00042800144241c0b00081307031000000d1901c0080c6c8841300ac0006032601403d844440e041011503a030380041300e07038250440c41d00b0480c040001e4400141d44c1140c038010a0710000643c0c44e0840d074060b41280d46d0032580e40200c2903071840d007135450301540d5100b04015402080c014a407a000c050075030310194401c1c1484c500e0080248001d0f0313070100f1a11002000c6d43c00106042d0a5030704116047c1100450b0b803c00180350100102c1c0da0001d5400924850f02880c0c45030f83e009407121491400c13840143d030010120040c0320442031325420149111562501d682c426103e06964984400d429a4402e420490000707000340d00c0b282c10040e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 876282742 1250 876281492 876281513
    0x40504170f18030d020d081b07120e040b10120e150402090a0207120509010c0b01060509031212010e0910180b1e0a020f0c0715090618140103060312080103 68
    0x180704500402c41140c0c94034002c6d45928411041c64100004180004c5802c0054088680d998a0707000c2c0d5542d0310300982c00c05800300c07140c00283c9130005402c4042c00f41d0074a070600500d015403100030300c060032030340740020240d81c0c41d001d4041c481001910360042c40000e0000b444040445a04550f80b541249498810010403510040411448034414403054010400406101c640400c0c0c904204e07645480303000068504184500c0d0013480c0250141c00410282c1d80100035100050080d8101d9080d000c000c0584000c0d4000d994580300d4245803500100140c0c480c003090b10344c0082e061019034004d102007801030000e5171520380082c94180742c004584004c1000b4004603551250320994504040000b40750100c1c07a458001d862034084c9a0049587c03010001c640e0200c032015025042154040d40c0c1e50061281e510121350115400301d40c88820000d140e40c0960581c52100035a4801d400c600341c10a112000700015070100141003503030340d41012000407162140015000919150045198554a041e600d0326 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 876283992 1250 876282742 876282787
    0x2f0d110403050615151c0e060a06080f07061b2a2c06090415091b1a0f0d02040b0412021002032a01090f0308070e0a050f040504170f 58
    0x191845c03c4a00e8086000c442035a910039240402000020341965002000d0117011104c01400e011794070a10000000982c8180304170307206007081e00d80c07000c00c500c9555100d00403446110301050580050f800c04a105916240307031148621125508040c010448084c00d06d03004500a070440c8a1583c144540c0c00c0700f44006580c80d4014041d00074030310070103804400d6100040c21060086c180e03a40400c00f00302c8580390303140070340c001006c0402c90000103003040340700084007129011116100d00400314071a038a55101011204000c4c2d522450100302d184c034241507901001c011481194280408980d40e11030310004c00044c00c10389600200050240104400400d000d034410066600400903030040d08800d456034a0f01c5c00044680206200d41135588602608034408002c0400200d43c200740c0070140c00007801c901500c4280c0d18281d03540794038401e2084016050103403c0d44141c03003209800007450145c01255029110b1511440c8016419200c00010307040240c22040d1108042024115090030790350740b403840f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 876285242 1250 876283992 876283999
    0xa12030513050316030b1801050901230f040b0a29280b090d0c0806190c2309040603051c020106030b13080f03040f062f0d110403050615 60
    0x10b4140c0e40405900f004c0d01d61200825042030300001032039660402c107650f4141d11440e8024891803801040d15030080c80300003c0124914034126107050014655000d0610039080000e080009072070326104c2c03200402d4003c01400700181c6503014620b484180704000e44640d403640d55010780c8400400308212441076132016440d52107003034402c480801208811400200c0f0b00a0244651f10031124001c103c2d4107680d030070090060a544000000c400000082032071280c0003501e4114240800d41e4640e00a840c802d4402c2d800260455414240b02c1c0544000e0040441030034a06601d454002400b05095510652080d141604102806101420b0318900455168075030304c0204281070444ea5240102500901a243d1a001d4014940c042041c9d040031112008000e0070490b44078503043c41c145a50788030130071085655900b00f61000309007082c031001d044070384a000c0140345031510048190b0719846c0c221003e006545525402c0c80c81ca94885d441c018030240d4011009004540b9103454400e03246c1c0502d0b81010700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 876286492 1250 876285242 876285253
    0x1201030308010b070302120a0909180c05060a02061501171f080d1b02010c0515060f1203030703051f060507050f030a050414030709140f0606090a050108060a120305130503 75
    0x3980031651058845207151400e0708c480c10400c0840d13000038160801c000b1607240102d040d00301218890b01c4040103129503020306106848005100d00d80c0194050a005a0711003c04901020110503950803402010324200301040d100071401600b12000340c4d60384c05160040035030419942c43c43d0415001800c01903004100401109800404416601d5402d8003031000f075007202800c40e84511314140c3c045030011708607007541c880d074440c80c0da426405450700c0340700d1001268000c0031424010583c82004409030003440c199640c0700300a50150000174003601c0d110f20011054811a801507101b0005880c2660340e20b51600d41e1340c5005403801c42d1b0805000c000303a02c00d1121600031544042141e00360f07501b0441800030508841d012924100c0b003604010300d542d0900c101000b00c940d0341c41c2c2c45481003044001d1440780e070b03c03001c061025038481c8808082e041212441c080c415540034501e100c0e0081005843e50107080d6440008210520350203404400040000a5505003a031045d50fa42010300400ca01604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 876287742 1250 876286492 876286507
    0xf090c0a060c140f010615030b0109180f060911070b01050901050a1208190f0e0904020a140d0f050d09060816030b03033a0b060307050c0f01021201030308010b 70
    0x18041e0508882c02440912410b28000c1c180e40c2c14844202540540c4009200d0301d51207548801a013005c95803400006480d03c028002a988500910b90403030360031001c5010f000c0200780c100d801038400e2a0007808a2510f603200001c42184030302c154500049500180fa0710b80429240000c10070740180c0c4564403801c119001840641d4807001e1480449003580d07040503443c48286070501c141e024101100000941244008502c150001030b00c3d4512074003580c40c10030f0120300500f041710500050381e0107034004040c3c110074484440c6596805181c0100148a0489840596144112904281e034103d41ca904502001c001054010241c05c2c003520840c14040b480c1c1c60104549c4001c48100c032481d00816485035210303041d40d142403040b19190f0012400d540c0c03040410308009000b0844481d0600b901d000d81003690510311450348104084480c0c002c008900d19202d00c2011a400d030021a0500080d00030003410301d0004200340b0092400c5401c081e4001e0056140d41006010f0010503404016000f400f0400175 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 876288992 1250 876287742 876287747
    0xb010e070306090e060106030216140a230d1107030506010b0408011506020d080a110a0807020708012007050c0a030f0b061e1513181805030f0a030f02030f090c0a06 72
    0x803419500c481c60b005840f01a1429034503c644ac2a550140150050305001c00710300c0004915501d03c1030088910001d42c081a903a04100c400c03400d50321404035003001c47e011030118401c0340182040c0c800c00044032005600c80d22824103044081e0300c402e410b0880080e08100d01c2d03c00b80124401f0a03105600103042d9407618902a40318882082074604000900c0002042c100055118852120021200c02c0c0c454100d10b601506c0c24805545503800342c40b595000162165050007601085605602e905402003000010700c81180c100c220102c803240110901002c1c941c85900c0b115001b94003c200800e0092240e0404440003078000e04510b01840d1702c9500c10707005d11064a0a600e141206071840c0d82500da40300d04410340c80c0034041841900c00c00c02640020f030713200e00801c50121500d0031581001100b00c01c00b2641e019070100c00000307209030014400039401e1203600b40030309428140d9050100e550008541a5822a44111880d0141101e2a01031011000d001c0101035500c1c1415102e0100003828030201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 876290242 1250 876288992 876289003
    0x80c1201050c0f0d0603080a0309030816021e03160c0e070905091611010c0c11030703030c230d2f061803070b011412070f0513090b010e070306090e 65
    0x110303c903108000581d08100c00865220500a50300304000719140c501c03c11008001e4262180706600242d00384c0081410032140711103102039074085400810564405002c3c2c2001800f660303010003018003003030021074140d0b2b40c2d01c020b5088042c480e820540ba620f041c0103010805110280840e4108980084280013a848981409400141d0502d01c1c000f080640b03042110840c016040f100e41d15400c090110704003e8000c6440f40180b03100b0050358008400c1c40e000c0c15564059444007500103444130100e44003013215454290490054402c403400b41182100b44640b500520310001c0c4009942d010801102c0726402004aa07400c002c11540c1c0c11042140e441baa58802d4050003003118040301d4000786585034800c000310380c0700580c020b0820381c0a43c2e4940425500b214100760701801800302074103140300d200307000c070b60f20042d0f4101603400c005607400c2900b0310210040900c01030304506d43e6111020080b03105241054000c20013070108185a140104006094415a610441e2800c0c02c0c0030346410242d001095 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 876291492 1250 876290242 876290257
    0x50a090e030a0507210e15070f03050306031608060f01080d0e04020d020918070905010807020d0e0a0b071110090302031c05071407060e1c1515080c1201050c 69
    0x102031380c03168064185003402d0304104802009040d02004410241034104030501d0010f8000c0311018005400c030000c1a20a03c02c45400601c0c0c816a000392100083c01100a0350b003040018080761a20030300e2089641d500b41050b0080c02e49580088100401010701205160141442c800035095022124501030686c03010302c00e4840c0701366004203103ca00100c0da40e040e40c038682d200408800b01d0800a0900150351401034030001e00080c410040451154002d800301c034050941640200240d4681440c1154078400501d1000c0e80070f450140001076003038483c00900010380c00b80c0b4407161038038082c45c00c0110442e071480041090140008042015030b802003a940007400304452240f24503914203204550740e108000c3d0080c49000c001c000d000302d2200014050b01a12095140d000350f4039403200403c00810001c1c0301e0908120040c00040001030800c129000c40c07440c1c410740200ea2511410356900c5500c0350780d04080001d500c0000c201030249480071004030b0401c0004000c0116082c1219848030a1095a2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 876292742 1250 876291492 876291497
    0x1d041104110304330b09060a06050f090d080a08060a0e0903220f060206040606090915020d0b120d17090601061d030613060e060601021b0105070f0507050a090e030a 72
    0xe100200c940d400d0280c40a103040c0c13118401d0907460910070481c008000b07601c011801420b20400160060800d99154000e03514907454042c01c003450801100700e554440309042d078001410f810075000240c03144025107010803003521164880d2502c00240011080c66500c0860044007405c2400310500d4040108d038070800080e0194541c10780c00032504c0d8402501907000040042040b50001038190740840c101c1d00442c0f00300018407065580c7c1c07042d03101fa2440084080d003040c5c040c0d4090380c03001040303500509035038000d402c010844004c0c0c80001207084425040400b40c58200b10324202189a0288412540045900030711445003081c03168255600d405003d00350078030860604800e02d0746e00c002403149615800070200d8132a440d12604480d605986080200c51013414030020050302040032445030303c1240103a0082c04420100c10172901801c4241959505001e410400f400200c3ca82c0000640c60f14010001802114074000c14070184202a0303200c4080389281c8a18100e615002008aa04000051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 876293992 1250 876292742 876292763
    0xb13020901030e0a1b060c02060405040513060f0219031a0f011206060306060e010c020d06050a0e0703060608120310050d06110d0923030d151d041104110304 69
    0xa1005900400540904005500c10601c034007081022105007040f1741990550408030785c1c1e03512941a00c2101300800000e40c025010f20080c84242415404180e2160310b80c0d0213024000203e031148070403103a02d51f0040ca0f0007034001560310200201c1c01d03000003440b556464104041007880010040b003403104400c085c82500910344013043d5030f20858560149a03020f070010041540d941c807014009100340e21945000c244101480b125035030044201448454000e4034942e0700607215a641c0c7d0051000030180c0017015950031400c5240c1808001c08409540f145000152a508060340c907482c015070aa2226400b040420401076000031740a1030008071344081d034042554000c1ca2500300d028002c00030f400c0740314000109410072000d80345e400038000075000c0c8180c001c0805c9410000000c2229540e000d00f1280d108000103442200d4030350203d903007101c01c100080d2a8030f440d51403a42c2c904003185c802e2880c8800c1c4000707100c00c2c8000c4c0c10000c00e00c00d1307003203c0c2080341a20822003c021404000e01c064a41c0900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 876295242 1250 876293992 876294007
    0x804090209011709030415081e090f0a052103091513080d05070908070833091e030306010801090e0c1f1409240706021602040507030b1302 61
    0x2443c107450a11461030341c218203600c0d1030036219540350414820300600e015208052a4104d0244441e0342c0181002240c5800285200070400d5502c07001030502c40c47c5204042c0d0300c040c13210040c0010f4040d0740c880c201815264070300c1000c42541c414002e20b0196403180800a0040300400003e000e44640304103a00344003990340342e0102c0501f00005500c090000c800c00201c01e01c1380c8083d6030080e446034413070b503c1c0d01d6185600da401156032021140191081a0f0107041007004140c520f1242044140340b008500025800028000404c0741c41030721074403095400180304142e00c3c045800315500210b50720b0000d5041d442c2c004002081d41c0418452890f409550b100141d0a00fa814406141c0070000074202d0041c444205000058004003c4800000110414102004000c010b801c40c0d402100051030754415020218191400c0320203e40401c60020040140700001881400030f4030302c00700c20094498070741030503006000680741300400101c02c052618034090001d81e580c4045940f0280503c0b40180c0310a50b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 876296492 1250 876295242 876295247
    0xc0f0b0909070c020919050f040503220b040303020319050a050f1b0601060224010807051002070306050c030a0b01080f010b0c0a140c1002070f060521090c0103050c07080409020901 79
    0x201200117500118164100302c01400d001c0c5ca4000d0100748440100050395800c10f000803900e000b5603005115400401503a01e42018021030f0510300c00506450303918a46d0f40c0d040070f01003580180c0c0100e0160f080820540404504450144c079038201900300036103003030309030304006040d8400c0110090f50100702080e8446415201c04410b0b90381c100c80d00071034026503141d81001c0c0d510350790010500ea0f002001004120000c4000011904031000c03000284811800c0404104241c241030b40c0e0a4118818807070b002001c500c0c140601c43c05007107010002c66907810651070741d80c01da48642d840603043c800001c0611130444450918103044440f0b1034440c6884810f0b44020b03504001400c040503181001c00d540f4403403082c00104032030001c00d4044031010350035200ca0a083c1d03200d050318407811003484c040800c2008400c0c0502c0081403803a111003424108020742d000a415040c0f41500c2a840d1680418404d088950b0148607040e046441c02e2209414140540e9a50b045031150340982c110040d008191045d2590 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 876297742 1250 876296492 876296507
    0xc12060a1503050a060e0106060302090d0b072609060a020c031206062b05060d03091403011407050306041406030a170906031914040b06060c0a020a09090c0f0b090907 73
    0x10343c8901030340c80368001418010040d115039a0042c1240d464501d0002e2420700a00c2151540000a4052072180e0000d84800742d601d440103244006011200c09492801c00aa100c02501e546d44445a507415090800c00709140603c0140596459441000b020141201c0001680c0010305564500c521aa035503c011990602a1481c0001c29000180100982c100e0000100c40d00781c1d480ca03000c02940e5220760401064904002c1d001e408070b030180006002e004041c403103545414402038004201e03080310b035101d820785480c00c9604500041c0e01005010f900e1910b401155140c644d0400b24046605040c070010f0340b500341412004088502141002c80e18400c9030050b52440b0350000d100a4403440c12840c52200c00b01d01c1c06020303a0301450002c1000c444004605500e018a4100800720300c039556643c02d21215a121a600c52541e1040e08051401a9100e40520380075140180c030106240d03529107840340b40c02d4800c0d049290041240d407403e10009040340d0980300c402ca41261042040d449512003078801b030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 876298992 1250 876297742 876297749
    0x60609060d170d0b040e0a031b0305040b0d020901031b021213091b02120327030c2a0102010504050a030c080c01060f0e0a050f01030209360c12060a15 66
    0xb9001250181e00d00140350b10800341d40b40c083c0c50611a00048210310b60702c0d5403400c0380050115800c160307603c2c440e4503201007078201c01f03110303080141c5001c1e2140c50200c4250400c3e01d200e100c580c1c0000c0d0801ca60350f414010020305000003071442100d4840940041d4440340780814900b016600860300954170401e004c0880300900c1070407010060300c90301c5903c02d41d0800d00c0100d0a0003600c240b10350959080c1c181030442e4441c4080d603da41c0c9070101051100c0c80c1c02c40e403800c803c1d0410b110a00c41c2e030741c5c1507070141300f0361054800f031480314021100c80842c0580680000003405041d64500390402021030404100d14007010390503d0300e400140700758504440c0d103008000d901282d030340c6003000110b00c80e20882c8941003134521090002d103155a6080a0fa802c0d135100316014151000c0300c80040005007480b660482d040f8400c030000000c0420b00c03c001c0301000c071031135020481c005801d0002c1c0380905070511801010314400d4401d0b1840d502d051104956907070000c0c00d0054031903901c0a84422140050984d070004d03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 876300242 1250 876298992 876299033
    0xa0216030506010e010e04030e010e0111010509100b0a1206020c01022101030302060c04180c0201020d150521030307080604182108061c0c0306020705070603050702060609060d 77
    0x5294403400c00303996031242402821400c400000011407180b0b83c20800034466581076a601c5030144900004540036190201154140300e0f860055043d5910213000f0644107540210041c182c840b54148100c4c1660b141c2c1c0c50490041d40b041c0c6091001c2c2122140c41981c0c80d4100b05c025955010040101780244507a030012000300014a0b000d005568658144070f040300e01170307801c44407075031180c24400e0078a20851182d141c0f1710310240d4aa040d01582074001a01c0007403140001804d20b00605400341c1511440309100c62520811201802185081c1140701a08212444082003c840301c0b00346603034911000d0300307007414001c005001811076699504169000c03030f40303140c0c04141c07014986002030340100340310f4024030b01c1c04650a081d01401d20515074584a804010224000d510b08612000a01da4443c1d00a5400c008410000720114015000910710345200710010300c82c43d80703082c00080031200090408011904004203008007550b944c1e00043d0080c8085600040d8459140b601141400001103001003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 876301492 1250 876300242 876300283
    0x9010e21030712030b0d02010e041103012607060c0f0f0c03030c150c0e0d06060806010b090901060201020702060d0b1807020106082e180f05030d2f0a02 67
    0x100d840040041d00314207101c3c0700012aaa0507440d0207074256401028215080401400d00c00d0144d031007034118040140014000060200c44440300310300c0c83d8001d8000c901a12031080d000741003400782c10aaa040303105e41303601521070141800001000c1c5101c0107009410540420356801c140b0800c1c0180e21140e650001c2c210144580d01d15002d01200f034180e01c145c51921814040080070215406206110601982d8072440c1d80f000f001000304183e20001c0aa4003d682c40b00c000c200840708000072406170441d48040c5880319403540400c0703180541600184210790040c4080c10042e02c919042d9581002c1141d4040f40e03101854000c02c0c08404e0b41906445400202000c0c00889034065100e03e0a80d440c540a80c4c040e00c4800c90303c0c0307488500024a074403559031021458030311440e181c0d202c1c00600c01e200350b03074021852258880c4072080b0340b00482070340c6940000416002c034601512858681003064004032a02d06020101e6511810980c000c00002c0c95002039040000c030700c24428500c00790700312a084403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 876302742 1250 876301492 876301549
    0x1b020120250c090c2a1a0907050d0506060a0f0e01031511070f02040f0c080610180305030a02060703050402030c01030e101503060507020a02130b18251409010e 70
    0xb884600c8165025100c001700750722660b0700400c1c0b8005c8000b42c0d900710040d054a0b203042c1c135025a20400091521004d07001e94940440c4580e91864a525082c0c029401000b2606011003008541e0324298050520b074050b04404100c803480e207a616504403a0007000d80303455480303030703000507009805580309110a840000a40104000f2100c1c50002c101e4000da60401c05c06464441c01021034a85900c0f400110b4088000030710f2a20b0f0400415101c412140750858000480801d4a00a00501d401c100c40030340022850000d915810041103620007103620702481181040d8000c00d40b1145907a41032030401da02c40d00440c626200801c90340e08000340c1d50104002046c080032034000042010b0100329a0340e410000414090f0781b00203070000201c1d800402c0114420004101c1000408a1480c402c0d00120082d05500c0c094034429400b03440340000b84418404071440c010108520b01c01508a1300070302c8041c03850641103005070810380c0c42c82442070030502200491600043d000ba4240160321021a25002142 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 876303992 1250 876302742 876302747
    0x9051516060606021b040b061b010209180a0b100e09270f1203010b03010b0313060c0509010816210f020c03130f1406030601031b020120250c090c 64
    0x86401180f2558000a411800000c00047e105101103965100009002c130f619224403584450408442d020700051410050750046280c0c0c2203c2c0350304c4c1e84295142010410040c000380900b1103030003401c45444200b015505005071045026100403401151140c00181400716003680354840440704540c1806d01400c0300007036654803c0408840002030050710f070001ea580444034152810303112480b00742411a030a14290917844d800040260a80b0080782244a000c640c0a216a209241d0150b6039255034504d11000901558005810802d104040440140c001c660108152041c54403a4030050301c44001240e10038080d25041000e040d503030b440042e500c00035001c000b0088c5155802e890428100030b560f200c400015415070310545080c200035424504440c504000110b902400c14140004c9081040e4a4411442c10300c07131409025130340d0f500311413000001541c0716a0400000110283c40c25040142440000750b80100d00f08000c10301b04041010818900d0300c0c2405058509401c225046110710300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 876305242 1250 876303992 876304003
    0x50c0406030f15030623040804050a062f0c1903031403310803100918020102250b0d0218010306140112060f0e01080c010905151606060602 61
    0x50358042803501d001c041c4a035070a80a0b2040109000710340081440c519140d48020b0122404621110071043c5c0c030342d00c03d40d990000d07580e0160740241c0074140ca9500b01424491842c9040d08042c045c00380c162522100103040e25000341c3c0d020010191080400760003110030346050849070180e58419803400c8000b00564004158004403030107503941980c3c190920310725403400e100c180d03003611380104200c14141944210f0f14407061031004801400201c0b19440e111030307e0035081983c1c040e869266200c0f0800099031b00b8080e5245000c180c8418107070b15000740d80040e43c0c520f5000380030071003423202494107418410706024501c001c0c0751211440e5a501039044480e4020351104e241e400c81c0040001941030507500c2403203000e041d41d00344010202240d1060005651681c4c0040c2d06440c0e0070f448840c04140390904c0c3c03044c14010050400308102d55418000054200003601c01094100090007038200030700da503070103440304901c07421b009001d960710120a40804425962a0058501414060f00055442d80080c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 876306492 1250 876305242 876305249
    0x314041703090a050a03260412050c01020d05270a0902031e09061905270307290f150d0b090d0c11040b03010603021507021201022505030d050c04 64
    0x5400e030f451030303c44c401c10100c400c1500015014060b008004d00e840d05440011800700d6503032540726810141d6800303200d8084032040c0c0c41258503800002c40090156010450348190805a08002d402c00d0094606038101c5103074105502601c0010f01a100080d464525800e0054a00340c88155074a00e005811070321650a1300075401181440e41000032088840030a0290140840c007800e2103001c50283e150802420010744100403415048005202e01c5001c0e850280309048840003035a150031a508087e00021014204500081804a19640300300c0c0e441c448a80c0c0303c1c20060a11980d515500076010100b01d0000d495501720b500160080e05104180403060721912049084540e41c40440e14100e4400f100c03244020003c1c0800506003c4615007900140b502d804007400000301103682c1c0c1c0006100c20052048800300190015043c0c0941c2840d22050428011031402945014003d40058004c1101d80d4056645011200b10650802c60280100d49100c00e50950034403080c2041074a51040d0b03800b610 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 876307742 1250 876306492 876306499
    0xf2b05090d05040e060904051c02061b03100603200f0d06061b11030a05060114040e0307030801090213090218040506010c02090f0705070c06090303020d08090a031404170309 76
    0x81c650001644244101c900340c1302a140c51072855180d410601c0082c50004d0400c4078640220218200101d022102c08001644564001d02da00d0a00110f007041684000940301d030800030400c09c2014405a204240007119058070f00010f070707160041100038003560011410088840c001a014225150a00160030034120134502049010303520f00c2c081d180c0071902490051040003440140300480c99400001000800c007174180e800010b0b490b500d1505105090308000c06052101e100b161150801d48100620758907000011443e18003075490190411074141b02d0038040c1900000c40051103410f8050f000010806204190341721284010742d4070806443c0050240118a00400541c2d1584a2500030300d000750040c003011003a4440d1210402e0040005000c00d00b4094104070790000500180301d500c006200c580c1e99600001e00790701c0c0003401c1c10400d03802c840410854505010003004041402000141e140c28000305155a400c0d00e00100d000350b6010140c003041030702e008c02105001200510100030102c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 876308992 1250 876307742 876307753
    0x305071a04030f14010b060c030d060e01030c092f07062d020904111611010504062a021002100f150501051b01060f06030f0b060f2b0509 60
    0x11804003020740100e11019240c03586442000010603c00040c100b40400d20784004680000c43d800401d1181d0b100484560076540001804518009280b01b0500075044ac0080f95815500d161114050500c4a00803040300c5550340c400c0c680c1280300c081007603841101c0862050740031914035044400d41d401402c015914a400c0c80c0c41413501c10b4020f9012074000340705c0d006140b10740169038003480082d044060395542142c0e03111060380801c003514015001c915040104030301580614501000051101040141400801d01050080980120b0704410005103120001d2201441036a0004542c18190380603401c012000f01401d0125804603001803160b4040b8824800004d23060100c1003241c07422340c60100403170b0b55140240300940c807500081610501c110040d00102000c00d41107800c568542d485100d58042282c01000096018050301d00c92428042e410020f015003907000c075000b44035240084221140001d90305000401513040320492032070f03004c0c4c041d849a10582e0b0048c010901900c0140c0b103071141c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 876310242 1250 876308992 876309029
    0xa0e03011e0f090807053004150e0a090e0d020721150f020307260126060a1a090403021510080a050d0e0406080c100315030507 56
    0x14001c111500890348031601c048506451040000c14451103103142254580c8100804544004050000340f800380001c2c000b220380707104c440080b0340209000ca11001a5240f0316a0300c04d14070342e096a048800340d00b50ba80c0c80d0100b0315002c0320030100c40750007160f22140c41c140219284d50590300c03e6460071124011210405e150780c4040e6510086846004c4001e040f00c140b14000800b10460080700512814000800d0445405e803641910f01c600f61418020b54080200f1007602d40c00300b0070b00601041900c0c000b9620b00c5034154030040301814001d00c03550400f403448040030383c442001c40922145100055441500b0000045001f40031052141c04a030110081c00c07074454503001c040e203401164150001d20380d8100400b8003003c2c1d001c1c020105407192110440000701602c0c140006c10240344200701410524a00c2c200240466207102d1001c0d00451500c1c00038408104001002d61707150340100c61800b03181d0386000040703001e420402d01c1001c9054095000200b00000000c4000a0350a807403181d4182104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 876311492 1250 876310242 876310249
    0x9060a03061401180312030b0d0506040b071d0907111b0f030d080a0f090c030305120a02041d0405190309030605090d12150b1c0f02040308030402120f120a0e 69
    0x250301039902c03503820841e00c0401c0000d40351b4642094a6605040c0440c88000c00000100340342c503901010b5455800850801040009055000384c0c44040750a140c01702c4c0d805600c1c5400c3c0102213401c0540590a141c010400050003500406141a10030b030840303581080264280e0304085a1401c1d060041d0b2012801202e41e16002c5800001c007001035503615030a80e50a01150013800d01e40030741c108400d40d0340c1c03600c1c008201c041d030f0884091170180e00ca040d034600e800003004071407440040070f07019840e105003c02e0007d15942000208440072083c01d170045900c0d581081c0341401d089072030840d08031014102100405070050b0074201100e004600400040d0f840450031925081d407010035100040aa8002800c0e80718541d0240606094000d07609007030b0350b1240d40c46002a844803203181c4d1081c174611006c00109401740140402d880c2d5a1500b5401e1915641e5080b0041c0805000240701304280300e60362169a400700407242c442c114a00071141074605404205034142d1118405000244000c1000c200504 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 876312742 1250 876311492 876311507
    0x80d0e0609060702010c0305090613170c0108130201090504051317071109130b0702030c160506040302271e070e01020604080d0b0901090c17100504090809060a03061401 74
    0x40140c0b5080c94840e2a0b4011a501120240d040701480070910001c10395442d6030b006446806a00a01e40c4012400c004d280000310410440f0a030b41035100c9201c01d042070341e1041c0d44641003040e800700301c0c000c0c0c000c5200681c0d8124040d000b0541280c0360804020700e0403d002030702d68045001c4d40c4450604991000400100d2148441c054102c01100100e051b06092001c0c0d010780c00041540308024508941c0d5440c130003c4400e54001d0300507170011483c00c22007441030040038607070340f51402111281813504020840501413440040d1003a005085031202900c00484051003880005910040b9490004220784a100da1a1103a4880b608800001100d6500500240b480c2c1d020580090049650365607506115a00c03004da585a0b403a1a02101d42d42c949482101034060040d404020441c07034400764004000c040136807400c84c40b60420030117106840b848864040141c0b40300791004104040b80d41000142d61040b6081d041d00039400040100c40c10b03605622a4040d03e500c04289400d0b880d04500468064 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 876313992 1250 876312742 876312757
    0x1a060a0320041808090f0103020705030d150f0806060607020a0807060206040654111008010b0301170c100518010806060d23131b1809030201060f080d0e06 68
    0x681c04105043c0c80345400e403c0c1b103400450514015140110985c1c0d59402c0d030304240912582d0716207039400044841c1d100321401c0041c1c080d2880c100030140c030340301c8501d40d02e4401421031805550002100b80a5455402521010382400c0341259140342d500d001c0203503910b50441d000d807549840c062002c01688061103550304030003070b25101014500d10340046092000b80100085400741113106c0c1c482c02c40e002500604810740c1c05110b05086102d400006d210311400f481a1210030410040014415103c05030260b82c151003850401201000900804514005010710301030340c0310808803100541158032100414a1406118203414114403500054403031b5041507039050382c0003030700f44842e403224a09a4044030180408142c01c40d000d201480c0303031003480c0f00241d9003c80c0141d15801702100b4803007841e0303030851018041100a480e0515200104000310558000c055520b5118015003041c103200b500038038041c1c00ca10994100250352040c00c2662404c4d580445030109074071040105080c9054000d1319081c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 876315242 1250 876313992 876314003
    0x150910110f161209090e2e23220b0105150d0603030807110c1309050f1c02070906210302030408100203041e1a060a03200418 55
    0x8104608180381000d07004000c5980440a00381d0403080800d405408804008405481d0130003601c1c289003030342c0e003603501d50101d800d100d0b070001483c40d400e0002d004101401ca490302130081481c0300081e5404028203021401100a000542c80b44544d40000c40d92490060140801a1400180e5006039401d4100400400780241c04044010400340c01c00c4010500c20000d0a0b400c54a4580b90062034030132140160825000601600d042100c40342c0c1002c060102645040014121041c1c0000085c14540811a030240c400d920307500321904000c0708018811000c065181038030081c0c4a5640707003a2613000b045150b000180b049420000f05480b0750702c5080156890111034440f0002c40d580f0600754601c040c2c200310304601c020080002d200070140440541d0310303251000540e490620b4100880c01561842604040314010507100d000900d08400ca45802c1c0310a00050300d584d40c400c400101c2d00b0f100380c2d0015120b0325417801801c1e0050343c0000c000100c1d4100701c07803c101411034021815002c20340c4403002040c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 876316492 1250 876315242 876315247
    0x7051309051203190216031803050c1e0d05210405060d0b060408060f010905070509030c0f0a0b0a09170a02060703180512010b031b0102031b0c0315091011 68
    0x2e22075100065a20603240b03071107002ca0414031080c49089a00c403290084103550f42c03000c054105584103080c94400911440e000104d01e040d81c80e01915100006120f1344260100d2040300c02841c54101941984034008002444885517030a1540d00c454412a82c100e5818160301c218000c000c020307059900b51040603141c141030264007102c92000304000c03160150700482c20b00000651000420504d845580b0721985a503075035150090540680302c000e084103043c04000d20a0002c02d4800141050a04104958890055180b074000c1908517000742c01071400c8200018003198203d82000c0d41808840070410f40240d12214022032a0302ca0101c40030083d445601044400003091140c15490a040103650300900d0395031355000061066034290000440036519144c4a001030b2900303112070000d1644100203500303402d52800000751a4480d5803400c0b80c0017025030780307504117807c070801c850000084086c04594402c3c0c0c0c01d1065650108084441286078400c403007507000800c9050099071007a4050345055130 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 876317742 1250 876316492 876316513
    0xc040b041b26010b071403180402130306020301090209190b1b0106080102041d060411091005072901080a03020a030f0c02130e010c110712150606020705130905 70
    0x103900030040d030203041282c4041d1035400c2c00303041031481c0c003070080103012005aa916400d2801070628003009041108a81042c081d0401464616000e00c0c480312040b00c4c0141c0d21034501000c00e95041c0140c1000d44098230100001c10035a20590050a00b1042180c20b400314460107003c207030050b4003501900005100520a0007000c1c0104030300c0500074600300d800410130a803030f0f008c054220381140e4442d01d4003a0f400002e80c0709004010030010781103001580e0910804540ca140c0340100d03c0b1380c49140c1e0148000342801c10042d441401034407242640121458440094480440c07812880d080d04400c10000e40c0000003001c0c41c001540011840c0e061300500420702c0240c40646882c40e01d842403009100b040a03001d0700580d140182044488100340001800030360041c1c100342182c0e200c42100e400e11600303000ca04503062001407020100c81040c481c0d0342c0024401e14190744120400012140100e082640100d405600494101c00b82d480c1910140d2280c3e40d030340050010303600407234000742c00b903004101440c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 876318992 1250 876317742 876317747
    0x10110309070b0703270f08010b15090a0503030f07060c021903031a03060907080c06131418100303080604020f0a1d130e1c021209210c040b041b 63
    0x7450f22500a08028842601d10a034005002d040920302017141e0100304000d019001283c01800090203d035002089042104000700e40c01c80b8484401c003000c40404a201c0e8201d0b62141c0e8000094403000d8103a0352120390050a664080d00060380c04c076411824517406400d1144005050851441d0b004202451484180c40c25801801001d030600b15000c00711144000d6501c0c1040094000d1201c2e43c003c0c210a46001c200d10300706164001d141d4400e0b10200020042a04400c0030075054a03180f251340d03182d0910410004060388000c0161074007445504d01013004c0114001040012a4001c0d01c80742c1c00ca41d20384d01044201e1091000300d0701a80390902405a08901c908444412100400c00034a40f0300c612000041c82c0c1801c000b03030701001a840d8102140c080c4030610a03414200c01314010444115900d050194a40c04110043c0001004c04610035805507511041446040210f200d06490702540035140740e221404ac401003800b8904040140d2054203191080c4a903503007140d01c035041a000c980f4001c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 876320242 1250 876318992 876318997
    0x3030408070206120f041101021609020c0124030516051c030c142805120f1e0a0f08010b0a1b3801140f0d1410110309070b 54
    0x240c3e000722003407001003040d07805890264050228080c41501c5441c180c0360210320286101101c5046400038a00f002501400182e1542074900d07034035001da129508010103900514a01c85945541c1e41040400c000d40b494030070a1005582c0036006850010400791000202a040c0d4802c1c1d0790014038a032011880d450082c0038040300c052007864641a2842d1030f4580d003950060300d0400c5819504121f80d050301242c80d851500c403000c400810809403001068075615101c642048a400c60381c68006200380c869040c02040f00e0501101041c0720100c50b80d0b00c5600e20f01500070221501c08101203080305d5042030301901606040392408400d1500e0f144155604540c1111101152040090300b411001c0000f8036214a0811420152410462510000c07420308100c40032203c41d84040d40b0344000501c00d20301c0e061410b40307245105403441d160745800100405c0340c81c00e22420103403103c0040b500d0040550404204201d0703440e52100700b4041941046d0700d08003103110584060f0242da105a508110081a8102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 876321492 1250 876320242 876320257
    0x7051209010906230705101a0f0a080c06130b030403021e0109020f010f210218011b03080403050408060f090105010501050c1009020d05070905190b0f0904051c02010e010b0d0503030408 81
    0x9583c104105c00242106680e40002306c0c0914030302a0501c1112400c112000c080314050843d07002030b40d02e00c1d1050107510b0b80601c49249024010010701000d05004441c203603c010021942e00c01c0e5030346001d0074029158a40c45c02c102c08652280508103066003c1405071800e003580081c442c0c2003140c00a80156072000c20001c000c0e09205600390064000d007174800c0c600c49a54510701000d6034404124504046101003040c01506005420801440c00311060404c2202c00303901d07045c104069120390800b594540195445008144944400c102d10f44504507600c1b8003906903480240b090342d80394001910300740074000034240c1d10f90058603104441080c5400c1241c0503030000e010842c80c212540c503400d00b884555000091015120302c140034034040316820482120030840f100300210068080050328004036000c2c560320070034182000c101400001d1010000001c80b91040309004140300d0300284c0642401c1d4000e1202d546480010078003418020308003801a03034410061490b603031f04ea540d41407083e0003842 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 876322742 1250 876321492 876321503
    0x60a08090d0e03100e070f0303050909010501050301060c1b05060a030b03010608061621020a090810022502040b09151807080c0a030e0106030602030402120d050307030902010302070512090109062307 87
    0x10001031f940104041d13000038500954905030740d00e1030f850074045980d6069115a04100080004111207a80715000c6003085034030400760f901d035440d50780c00e601442c0501d4202070340c071103000a02408803a4040e803040e548104150028450199200d44d081c1c0c807041c0c00c81c0c011200b10906c040940c0317420b1007045280466400440ca00c07624003259070249007240c00545900c4085144400140840705003081916005503072488203501c0c10821100c207404601d2030550040c40c20b154a04c001c000c41d0f840f03400100741300101800c44101c515120b403d4041498000c3c0c240c50040350001e4003003000d2001540c1103807140205451b820025141c0f040c041c401a4440c000a030300b019a03d031804440c0c000280504e40085005a03005030b00d07070415004220313500c00c210000c1c001039070002c009441802d8110042c0c80d0b220103103081c0000c20708998001030b0003a00c24840014180d025608600d04009842c0019040010080e621115059242e03402620090207071040e555610036500009441d4901c0312008140303e5210390f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 876323992 1250 876322742 876322753
    0x50309100216030302150a0605010c0204050a1e0203010f23150f0f030a060b09010806040b120a0c060e060a0207270c02070312030902010903021e060a08090d0e03100e 73
    0x890b11400311500c582c00c00c400607085640391300e16046210302040e030082a40c0d0800c108030f503d0803001900301642c0100c001d004984903c0003500c0c4030800d42c410305078160712062441c0c090402031140e000a6101740074000746a201d91401003038250003500c2c01394100f0300c10380e41c80c0c420030b40500400000030050055410020410003030700711140102c030081c00c0300406e854007886c0c40b402c080c4040e0040c0d8800750003000c00305805100e03004040ea405506290401420340c4d0002e2580000804034030b4904a140d00d100302403003102c80240401c01d0000c1d8000c00c0b2200c1d50f9a00030450f082c1d104212861041d24650001a400341c0f1040c400c81ca443e10b200d030f0002c4113050a8445d01490604410140e0382c4580006000da08921410014403428034014208040d00d071800308110051a40064441140d500019000c0c81000714103200800aa603290008400021301641d05c400344d0340001002d01d98120342110080c001d1b9040100c0307031801103010313800a1070010050030303060945242d601c006010060b10f032803072071040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 876325242 1250 876323992 876324013
    0x20618030d0201230708161b08030610030e060c0c0316061a031618140127110a050c0c04060803210c0715020f030c0409180503091002 59
    0x801907000404000c1d000441c200d900c11150032000074031141c107981c1c4100907208200d584c85e03200d00f10941c05079a24801c55440c400742201124031000c00c8440d40c1900720009425000d01c003051001c4e500c1380e1000c0360400854000d100084040d00d0281c013043c2400e52080b4041040302303140c1e5029200c0c81c10043c0483e400d02080b0a84030b4400d480b803103015942c0036a1800500750341c070032403944008045429401082090740034880200341407960b20400c2540f00d00781409a215041e903070050f203080200354000102c030b940c40329070340c1c406080b0741e0740751041810042c83c1881c44c290140c01591030400384103098608040c1e002c0f000740c400d94030021030411940698661240c040d038440c82041d000d00100401103881d000084440c8034031000d08449005000104020408079469820803603c04940c40703100c80034550081701c2140040d0080150f1800e004002000b004103080d00d001c040c2048941c0c040d024031043c003038030251614811a0500113411504200100e00302c03418400e4803141d00710b811740f0403913950006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 876326492 1250 876325242 876325249
    0x15130b0f010501030506090408030718080d0e1e012312041101031406030a08090a0b030c0d1118010305061212030601020705090106080601260a0c1103070f020618 71
    0x90440e494454915244018012542d05100d02540705c01c0c1580c90010341c1c14203444415a074000201002c0070004040c92007540d000948030707220000d000100c1201c0c125101c18101030031b4081c0700001b46d4002c1c0300341f52122986e0200c0000c1e100039400103171900300c0c145101000340003034040040f4403140066010400e1a4030140020361031031007140210500c003078924904000406445900840c1045a200b1400380440d07a074003c0364286410798007500f01981c50358000d01154080b10715600c031b4512544040304009000c2e250030010269044c1da018100071100a50074064940d0040400005c84600949105c021a5011754090754103c40002c10700d490203054907408a00e4441c1c40c0000348151000441849155601000604081c1c40b0441c0c90300c240303604218004052100c02001d503410440c2900006105814418405c40b103421806452640c501d0701c080410007900000d5200390009200480984454034080261440a9440090016107001c5078081000c03e4210142452084103e41041040d0380d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 876327742 1250 876326492 876326513
    0x3011a0c0313060201060b0f0906091804030c0309051503130201090503160f0e01030503120c13060c0b070201110708180325060507030f1d060a030f0515031513 70
    0x50b4081e050320009420410300a007941d03d10381c0604c000d8441480f601608a80390020354400200c240c3e201500c0b48005400912198000420001c0b1108800c0c28002403540c404961101e240c000c0c2c5510400039680e41c148030142c501d240d0348100c4a10140003266020501400c00c01005d8014500800c07210344550000c1e08081e61010b2180c6c050284400801c400c4016039000d030300901180603030382e00c258599100d498aa100e070303580316610301c990080081c01c1804010247c5a110310700f0103898240c1c503159200a826505000740545001c0e40060028180780e1050041c0d2005034400030740c0904001580d0340c2ea0b149030304024074440c2160b0340690078100300e4504021211146041c03026000035030003400c2c0d020074602041d400c00c908000b810801d04000c41c0d04100c1c050040d09003860700c13500c00540c0c90000c000406c9804811039100340d0000d1601000d0307526400480d04091442c10801440e210840b4044e903d220390202242c05070440062a00c1d004850001280d012146d45015080c1d641c3c90b41c0c58a407800c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 876328992 1250 876327742 876327757
    0xe1b040b0f04020a031a03071212140d090219030c060c02010903050105270a081209010902040515011107030c0303270b040e0609131104090f06060306051b03011a0c03 73
    0x1e0f40e03410288840c410000480c3e05400c6d09078003a00305c1909200d11007001e6449404040c15074000c0941401c0811700c20481d003a080d4050707030725142d25455050181c402408402030160302c82c040301c18420308034810201c462400ca82c1c0c044026030060340781ca003017528403031400c076001c2c0d042c0651980300002141d800e005040c1300d1000b02c005052410701c4501c50104c540c00b1400b50741050345c0300e9806d80b000500d10504540c00f014441c0520a125901c04030754601410346014004e42060410f01400f910b10180d056000418200362521303c41288440e141940d144040d00c00070384000c40100381000480d004020350080360f000c0580b64882d007020703003100c0710b202d0019070300284003104009010400e20f05685149a004001258910172600703010b03026904911001c10050728295141644e1802c5a985a10080764240c0c0640c51043d803c00030300b4600c0061400e4401600c4240c14800000e071000c000307141041071001d00140041c1964200058191116021076281681d40b0703041210f0a02e0f2842000a00b640 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 876330242 1250 876328992 876328997
    0x210050a05040b1b032202040c0f030e0316060c0903020307120b011401050a110309180f09010b0607060b04201b060108030904020319110d0e1b040b0f04020a 69
    0x1503041618101c0c0000c0030051203408a04c0c951050700c200c607202c43e001c49400070800c040500c1160110002c0080152140b40000d510618241d1682c1306182c22064461588005850800103090030181158683c421b80d10305002c081c2c80801c42c10005007590f0300c07184040c10399181c10301d0390740d860390b000c01d00e0811a41c000c0c8189600f81d056050070001c44030182409402d5414007060354400802c00070b0f0070350203502d21240502106400c139600c0410100b05a0342205402000840d0050101400d48145001035440300301c2ca1441e0000140303200014000c1c40411a80030b05181c0c54560243c4450006180855103140e009448a004940040c804a0303110242d40181d0401540c68a10382100b040c510303c101d01801b500c0e0403a000401c4061804020f4505206080da40075951303503078035580406010250b0100d01a0b00786801481144a801d00020b0300c4000304e02e83e0208007c010084025a0f02ca489a0041c1c880c103010030385040c12410107410010000c04090310440c01018248005000da81000064000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 876331492 1250 876330242 876330251
    0x3180506072a211a10060909050702031617070b15330c0d050c0f01060509060d03020f3f0d0509120f03010e060603060f040c0210050a 59
    0x1400b841d0b82548181c2003404a0361009468034015698480d216a00082d05014a00010f040e007800002d80e0010820704d00104e58203110f14141d40d01820740d0065010f84000110159800311721401e036482440e00aa00c10b4000398108028410070500c98035240d2400c544400503032581003400c4d1801e41c00f4001480c03149462441614012038049143e200b1a0407503840341d6961007145600e039000310141c070f0380e6030f8014241c50001980c2039000d03171700c3c2d00ca00c1d00304824901c1840d0345081020303481070240900b40c0c03036203095512911000c0511400c1c1c0311180140d07580b00c20b9500100b031305450300d40b02a44480e4400c0c01950000d0060715107903801d00c030226500d603000100703c110984c0c200396198000e120f0005400041d040d80090020f02ca11940114450520001d40c2c0d00c0104034030060800a6003980e60001d030840d87d40300800c50080c11960028410300101160712030200d012882c044099a00c201000391400d4070200043c001c000c041c2803203140c2c01e0194054501032030500c4603503006103480f58950440115 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 876332742 1250 876331492 876331523
    0xf0303040809012601030314091203030619060e010f0903080d051b042d031202150f0601022a0406030b010806060f13050910060e07080601110a0318050607 68
    0x5080c000100d000ea030b1941904040450f20801c4d0940907030544c2d400d03184c50494000030f52114002e80c4507450603580e00481e04945100c0c061000001948104801d4840604540100840303540c910b80a009060210b03001c840104059417189460703201010040c601200c038035680762500f6499a0000c0d0040c5400c036220020406d800344850b05c0199a44e00b28402c843c13030103140c5040311800741c501600101d071061908018418461015050038040c0d900207a071044402030301100a036440704490410a41304c0c4a1200107804071001800903442100c040e009003103010b820800e060702142c07158440f0414603009000184080e00c5d01d00c1040084c500c03071415002e45504055005161074801000144540780c10700c50f02132246c8400c00c010030380340c0c0c0720840480d19445102e44c0c1400d02403800e22001100d0f251941c0041c00451113031000f070150b041511259031648903140110381d2440e170591070b032099500c4100081c0001e84640c120210310120300c07114910315a107800006480da07010f00d200b540c0340400c40c40b601d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 876333992 1250 876332742 876332747
    0xc091801120c08160306090614010b031012020907200f0c0307050904020a0b03040507210209100e011a04050a0f050a0b12041401020d09030f090602061909050f030304080901 76
    0x42c400b5021a0008000000280d070b00182c00c4180c901000340030540b250a1042002180d403c60040700c5899070a1142d503603140c40d00203016400440754001d58440381c0100007880c074021541c2221040d00500321a4560341c642c0b400340ca20030301403540c188107100e4071000d4a03030b40d0506109015003a40c1d8000646610410401014507009140d00480d00c101162018000169203056444045503d1409070710307103c1c1d03181c1c01c0040c10180d680e07014842c0d0703102409200c0d8040364001151170303030315108840b01112516810103241c40c01c1d036507006d44010072a0860060001ba56a1140e0401c45581104a1440c250300d940200e10102101da11208180c05154801d120074540388031000e01400305010100d00b0040004642c0600042c00351000e0702400090501240e500d800390103d07003a40c03ca81030305200c086030b0b40c81e004124084013200b070000510b420130081201d520102c2d0b007d010740450f80198486022120b1000300510140004460342d118030210324000340c41c00d201841c8540d029030b0550f5152408580003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 876335242 1250 876333992 876334013
    0x9071e0906261302010c0f031e0c0b0a05090c06040f09060e04110d03030902211c0815060c061503070522090c0914061f02060c09180112 60
    0x46041d140a050390102001c160049681c3c2c05035108079030082c2039201d400141c601000c2c450024110313007190503a100030305401c1034601c0c40300011083c0002c250031511004840307034600b0701801880d40c180c42000c0f84a1880a800054110f0544002d58850001c03c0001803981d500980c07010f40030310080c8404000d1489507205801c000d12200080d02124a0983e6880a0b140c400c0148075114520300407a65042c1842170f40003440c03159007d040340c44860340d1400b94441c40e8554a00c05c0d10b291054503100004c090021220030202e0142e605c4038001d54a4a1010b412081803051641d80c0250040c01000c4990100304400380c0142181c3d14504141e040c42004e0600348003075074228500941510030422020240721a00328001c85e401400081d43c1040c0c0e02d080c070000a0107502050250741841e840c0c9c821300365400395072809140106c88140d070a00c0c04000120784401d207040b4400c0941c000390002010381d51008000e000740300700102055500913140d0340705a22482c003030708041c01060640e60b0340801c204082d00ca = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 876336492 1250 876335242 876335267
    0x204020904140a051302010c030f090906120209010b041406030a0b091f0e01060f030c0c021201140f0c0f070f02090109051e090304141906020d120b09040209071e0906 73
    0x101c1324003200d40340d00040d20001623410002e040200110b102180c42e407098a6040c0601503580c01481004d41d14002d841c007120000609034840c1c48850000281200d40341d04544c00c6130940e4041c035a2029980b0100051a00020850f0b0301c002e0b150085103600340d4a0740e10840c415841080c0400c8000700c142003c040b508150b820200c0c200c40050f00600c04150010781e004403010480c5404100414207031070445d010780c00240000d4000c1da85052840d88840b0642103203d60590561629009641300c413101c520f507900540300310b0700449081190007680e070071b1000200b0b000c6004290303080741d0641541c0810410303130f000d0b88001c0003996698244000c1128184402041e10020360a0a001d800c1041160f51a485180315000903070008041030b076611784034945c0081c001000202d070192640c3e0750f468080c1d100c40604045000064030784c803440c50483d19030b01c02e400103004050002c2e04560780d03560030b10404000241000b82802150521a400f9422451303143c01095120742e14000b10614080000e010403201d280d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 876337742 1250 876336492 876336511
    0x1e03100314010608100203090109050604050d03240b0903031e040f0902130504152c060303070f0201030b0409050a0f120509011b03050c03030723030f0406090204020904140a05 77
    0x1401c01c1341c8500055294041d130217007030006a0f00d40300d8981c6280100402100241103015000130401400b402051030400d82903561028410401c0c00080058a600c40729040101250140c4050014580050141545402c0503003120318045a4106024044640100418124400040030b10901c88a2a10a40108001c907001c0d0b04107a040e0308012030b1940701e400750500440c1e5500c03d0720072540d120108880104000004030329100da00d12800c0d6081c02c003c0b0660b04c255107072040812601d04000003101c00c00c42d00f103903030128500c046030300460150100c103007901d0744942c443e2032003800700780c0521400700541d116003c171011070042858850300c0c0d4110003c031f40040c0711062100443e21f98100b10f00081c4404124058041d40b489441d05a40c0d50160214010710b910011042003207950f006902c07210040d0001105008401320f001400901e44001c4910b03c00030840703080458001651901300d61030880c4000c00160400742c403203003c141100d148205100c814850001030000c42c507010f00c52550004c0141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 876338992 1250 876337742 876337751
    0x304031712150604090903030509070f081f02040506041e0f08070905090312160206010e071d010207240905100207053703021002070f05061e0310031401 67
    0x1409420a104000b440c014030b0040302110350809030b40b0082120041c10405c00c04008803901c5040080050004481281b02407042d61000f00b244500c0d1880c00d011180c2420081503021304500e0000302c1c807052820110005a000e0101041d40e54a00c006400581490031102c400f490010240d020340c64000e0340f100d050b9981448080c0300c400c0c804920502660b83c0c13a10003003130f5a100d071101d15182d4460104440c841214480c24083d040c002030186425540c0e80b94221a0b803179807184001880002c2c180c80d446c0c046401000d1502c903034000c20241906100050042d180400c0d82e64401c0c81d000b01d40f4400c8900301e0b9052698208501c5d4116070705101400094507561883c00c4912406941c42c21310b030103507922900401d041d11a440188181c03010300d0800d04051211102a0040440c2e0554120300040b40b14002032480c001e821031002800c80c046400d480701c1000b15074908401e1010340e0b8000703c0c0c0c04007080085010741d5020100b100c01540103030700440d2804c01081c698202400409e040c5204402c480e4140f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 876340242 1250 876338992 876339007
    0x316210516110c0616020a030807050f01150e1503010603050f160807120f140601210c030b060d0c12060c14040b250b090c150f0708040f0803040317 65
    0x1071040f50030070055611580e1980321000c01e00041c880e042c80254455090702d404000c00c40c030b02002d0311045105101301c0310030307103440c402003401d0f107209040e08400031703046c2a420404284c09a0140b41c200341d40c1041e051800d807641000c282903503515001603a00340c2c070116102c08412005c005003501048090013144202d410450040d4039901c10303201c0e801c181c40c0d13654015014440c1c400041240c3c2030b80030201800011400c0140c0b51510024031524400201c400c0000c03800041d400d00760081d19602042070f210440c2036507158030170b81310041d02035500002c0220072100050804c2c0c0c1d116000d032403080c000c0380002c060351a000041d1400d0309001001c1040c10404165455551410788041c1c4114a1007241c4608205039100045040282c0d001290003c07a2881814801d052075014004c09018050380c2c401c070070346d0040c0484050341c0041800302d00004c0001840301411000507100c0726124074400c1e8a0070307a9542d8684160207941c1c002ca80e039604001020010041e25290311401d034034880742d10604100c00e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 876341492 1250 876340242 876340277
    0x30307060c021c08270f1c09051315080a0b0106021006030506060103050417070c030b0c1201090b19090203100504180605090109050d020f0d0206190209011202031f09050108030316210516 82
    0x2200101c1606c010f407641101c00409250341401710140590330101c81c00c018440c240b03601e48038428402d120240c0500000400c040900307009160a03681c0200081205856450044000740070041042c0c41071034500c00d00c2491058030000400f00f15003d801e1040c01a1f045040103044c107800548940c420f5102017041030103000d06042e0041c111200c19000042d5105140081240c4a800012100204050f0140400c000d090307179000c1c41c01105410782c40e840060300d078810700003219451401460390151410a920020b4150782000340d1001a0800114400c09596141031800c0791041180025810110000400100810214203001b441e88014407141c1444084240c0101051410000d00c4d07800043c1d0740c0302640114040c940200c0c003030100315030328030b045000040d4902d0345c1c0e100703030031f600c400c0010001c0c0900d46409414161381140010f14034580321007020b05914040d5420f001e00340010180300040400101d00072526598040030003280d285851001d602143c88041090700c2488102c1041c41141030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 876342742 1250 876341492 876341509
    0xc1309020f150d0f0501081e0721050708036903060a09090203191a0a05061c0f0b07020c030307060c021c08270f1c0905 53
    0x40058682056403a101c000b01c03840c2d84181c4050048250510400184001d610742c0414101c4074184103444040c03420f81150100742a0300289000258400003060000303248080342d08001c0c1a46108900f444182680c40a00340b40440c0d126031450f07040450b2800001c00400380b201d48040440101c0301d811440350080c1544600305e03131140e0210f102d00300c0880504018804589203940e40130004914041081a01044154811140c0c203014050b49840003803408002d0207096107203540140545000007407070140c8102c0214410099038030000a05101c80b21407140c1a02d0350103075621a0300442c0c00c3c60698103100c481002e10130035050170006c0001d07800100d01c10054402d9500d900c10500740740b13512600803c2346803c5243d0300c0c03035038940000940c2504000d4254411040d000303090f000d55020203120391080e00244a200301c003e02246180000400012002800304e85501482201016a0b0075403c401071a1103074442101d120b41d40540381400301003070650a01c9011515510300103860608003400b089080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 876343992 1250 876342742 876342769
    0x806060412110405250e010e1f1b0503030604090503040302130c0e0d03050a0e120d050717030f0c0d140711010609051302040f09050d0f0f03020a1d01020a140c130902 73
    0x32a121b00c1c07940c1240c0c8144101b68110000506001c200141031400160381d81e81c1c0c224120104254143e0704c0242d6501c3c00c8400c0c841ca42001c05181075680b07210a0101621802c4811140c078041004048010394441c4a03000003401d05050024080c81c0780500030b46035104280758184144000c0074041c0c0000e90040442e0400441803601083c5c154030301011078020000b945a8400e5406541c1d0f0606a5035440710142c4203c0e40070f06031200d0000c4040d9002d0403988000d0382e04800138400140020181d03054840100091400c40074000b030381d501c1482410017440c80a94a03e00050101200041c815000f401004058049000c0811140c2404002205903881444d8024001e9031035040000c0c1d81c0a20341d220303036201600002614001c50304104018289290306d4841c1000c144c0301c00c640d1550a03c03a00c25688c0c6000c094695600001f2034010f04245080302d0084281188101510a030020f00742c3c007002184481d00500411000c49058100f1510001005003c05641e16002d640000360780c5045043c1c205 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 876345242 1250 876343992 876343997
    0xf0604140406091104020316030b04020315011103190e0f030106140d170f070c0f080c0d0828020f010b0f040c09090923061006080606041211040525 65
    0x49640c44c0ca200c50052400e0307080d42c407610200802501c01d42080d11203c030252a0b40c0d040065440d10002c02c07040b40415a0034044036001c052448070154058103412100e0764480701100e040000303904680021121441c0c4500000380c0011b003611084c2020342610708480b034110000c0c8807a506000c2078040031103040d000e240c030072626a04043e003403002a0441080c0c91014440780303a81d802d19805c41e045545c0c4503590440300b0340303d03071030000409030305040e190021340d07081101602441041e4000c11000d003140100550307103080c0411052003403400d15103942c66070130014103500b4405107032204042d0600002040071076081c0d0401d042a0b0440d540c2111a4004500c219030010b0049a1220100c40f14800b41c0c01c25151070346080000c0083c80030b0501e49628602c0c2c200049502c0920901100340c496209447e44c10a050719844103000d254015400c00d6407000010f80340c0e6040c99559905080d10201c80784095501400610608440b400c00c2d00034981d02c990070b11030103003420240310300d030340d00b0b039802e01085008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 876346492 1250 876345242 876345251
    0x4170319050c12090a050c06090402091801170f060103060221011d13031e110a0b15010f120c03020d1d0f060705070b040c090608060f0604140406 64
    0x2180304064103201600e440490401a42c90701c8810202d09601444000c10703620300c0340000410501001034540342d040d600a0240104000500a004040d040b4402c01d5900c1502802031000300d0300c0e040400d200e161010354821011f035243c14084885c070254000c4d403800700d41040c0d0024080722400504581180c0d400300e0010b80d14502d0220042441c0b18894800768000344c0340c00002071241b005401c10201b80c03240500784036141c0745c848001d1540c1c0801d050040106402c03050910044550a442001c20003140c24041d00034240004481d0804024442c100e6003c0340310000d06c800b2840c18070b40514824000e0806281c00601118040c000c00d40c4208650712590710384411420a502c0b94040e035580e5040340105000d80d8410031101c1c078103c42c07241d181da401c0f881808040e102040740002d19038000e11498031480e28208280d04c4440000000401c1620820305214001401c9541ca12402001b0b2001001500403814041100046c1d042d01800701c92003a42050512200e261403213044a40040e0302610008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 876347742 1250 876346492 876346501
    0xc02071a09030f1f0605060901090e0402151b07080d1b1505250f0e04200310170a050714030f01063b0402040504050307062a030203041703 61
    0x1d24004418074008003078015001c48900040e03116510f202c413425000030600007261210300307000781170148588242c00544c1602080002c04003249100fa04030780043e14000402d882e6a2600c9032a03440118202c20b0780c0350420950022600c10b20203113010b030454030f010f0014120030620051035180703120403801950100408041c01c210b40c10300d60280300403000b01c0620181c81c10482d405c10f0186400042c00010071080c0c010b021607481030030740c035500040b10b03101c44401c58125024040100450b00401c111400e41c07848900c00080410055441061140c501c04055400c29241305001061b03030320300a10607440301640100040020912070241e55001180c10580c1c155030740000c0c6030034401c2d082d00c0d071030303500c0c00302c000c188100105800c0e00188400c1c104001d0009110020300f010300d800ca22540da000f1095004580145455080250080e019800b00c03410b080c00c546981084821001c6031411220b410000c0e403c2500159459031800805410110708528003a00c3d01103120401e48a2072044031030010002d0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 876348992 1250 876347742 876347749
    0x30609010e13060c05070303060b0307090315200d0e031e030a0b061903150303020307060c0201150b0901120203130f230303010806063a0b04050d030c02071a09 70
    0x20002d103400c82c10501880c90611005802075200d01d07000d0f80024100100410441c40350130481e801015955104516986161500301c003140459000480c00717520781203400490720040d01c4422880c0d0401d0358003542c0d50070209a1000302c074040038401c03130b03c1c3d041030080c1c0c0408040e04200728403403880c041145a07070360f03904041e080050640d10240d50b0b20030707070208980b800d251794590f07035190344c0500340c87c1000428000042c0e100c480c0c0f0188070040c0164403c00c00000000c24680003000302d4403040c0004039461884007814503070f1000540086c0000400030500703000030f60f406250351403080c880c1c0800710b165040c440d24880041c0100880504404074400e01c68080000041898281c0c0c68080d502e20356100342d00040c40d03102d078800e200700005442441c0100300d2601e03040d020000b2640f404003204201090030354140101080c0d00709a94510750040c103081d00824100d5403401c2c85188201b016003254a1590030140484185200c07800440d4040b19062154420342285590182e5186c6821600c8900b4803002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 876350242 1250 876348992 876349021
    0x40f060204150e0f0415060c110409030f02010f09020609040509120d0f0e0708030406080c0412081909030b1302040b0303070c0e070f02031824040614030609010e 71
    0x312a1403000d5550144807594072480882029104031510484e8058500402056600c1b26100700119020072070208002801607036941d061a03c20090b201f10b0315607000c00201100d01d8100240d0114615104095100744d0a1103007000d000e00090042001c00440e4001c40c445024055019004995442c0400c0b20760304108141c0d0380060b0f441e02c110b55501030b200358400180c4400c1010021280c2019540c6460702004a05602600c541c4401581001c4c0741550881c2c110700003400310000a681003001040518403001c8610b405800b90601950341e00c0140350411503104580d08a50070000501018400610385100860f04403100070210800702c0c5c054000100240004510590325120008160041101400c179130b4003101c0c80d842030041a075840143c02e850f111444884000140c004001422801c4000c01da8050b514001900741000070340c05010a04850301a0360906254100c04079007085140d500002a880000001c00000d045080c6600400c1c240c00d010300030b840a00d02a0340000d426124000300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 876351492 1250 876350242 876350249
    0xf0f03021e090a05030c030a06090c0b07030c1110201207150b03030f041203050c160f05030106080c091b03100608130b0f06061b0106180b09040f060204 67
    0x49850325030400c4190054a9014802c5030f030141654001c005280d01e1302080040c4a80c80141c040e252184442d901c420050101c2081210078144c200b00101e92010100050b00758140710741c5130410390745a64104050780030700c07004600e407040055000c0c0036016a449010b203440c1e11101048100e2072404d60100f00e040103e12400340d59a07440c040744101c180400c000d03440303a2120711348400300500e04030401416200e100c1e0030740981c80040c042000304200d05c07104241500345070081c648681030103840c02205080010303100c4c0b80084030601034014404501405107010043c0000c5000704002031500c885a1348400c51440c500340f281d0314907030000e000f2044a085410081c0300d940302081d90707440e01c00c0445095041e18006e804c001418100000e40104031661036048140c4c0014001c08169100714003a011844c0007094542c11110078040c580c1c903100310303089100707880780d1001c008190a410629a03c81c01c61010030b0450825092038080c80751130721404040c07500180c2152040710100a2801e082003c0d10a603070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 876352742 1250 876351492 876351517
    0x10090209010f060507170c0f03040e010614040315060515070c2c060d0606060f0215010f180b03070828033f0506010e0915061305040e07081c0f0f0302 66
    0x9202d411008c0c040014002c1d00c0e10b0b0201c000361644c0303d4004940a220050326100d000d0341c00c1000b480420b90740040f03c1c144044020001c1086601c41c4040358480c10310503070720781000b40d006c00d1030420040e070306066401030102440e010300c3d43d52141181000820006001003104070000700402c0483c0c8903c0207006619410a500b4844980d507210010446a15548103100500403903100f07a1543d4000c0c004e1a0481d6034404411844070300348410700655510704100400b00e99981e003170811040c1c4003813120900034141d00d400360400d918910317403440d052400911030b02424140a42050006504040b0b040d40c1d91544002d00d07a9800c07040008003074102c244044900b4200b1070420608914007494200600c5010284d84070140c000340002480311202e000c0c3e400480c2200034010365174031420003501800c0359072180941c007005a95204082011034554456000c5035810800050009007020420402260040e80c0b9140a10300b000000401135182421104100300d614003900034481d2090b010b59200205a6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 876353992 1250 876352742 876352753
    0x519020a0b0a0207380a2901050d060e1b070b0f070c140d0f020c0d020906040f060e041103070311060306210703120f120e010e10090209010f060507170c 67
    0xb40300200f4a030301091040140d000301200184282443d40620401042c00c4004160b4882148805000c41f9068070150b60402c00b040c00942420291070103048010a45549038603031301c1c20035001203489000ca401d0701d00e0b4129000c0210900003075007124031030f500003110060f1807415113890f04212880080b00c1e41c054482c140c1802c0410302560b012441014071402074603100390103202c503403060341c07141007113900b242d440410b40c10f40c0805800c00003c0e05074001d0005000040c004210b108100c101c6003075401002c100c50f00b41041000700126405c0c1421440ca080300107003a42031542e65075903402c40f000c181c0540030745004000b081060303d030240403007064000202c0000c010ba0641070401da44424070300c02911402460b80e0000c01c0710307005042c085e0810380c07a95602c102a0902d030140f41d01920614003101059075858141c00d0a02c1024042c5512403100101d010035161a00d00402051000607000a00c01c0d02e1500d00c1001800c4c6c114007210b0307280c1d52004a25024498111050049000d00241c0380c03010b0161 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 876355242 1250 876353992 876354053
    0xa050f030109080a050409060509040506070806060409090309090c080105031024170c0105030915090a020907120605150313032708070e0c041208040f060519020a0b0a0207 75
    0x5d00944251103130b4250820116a1f5002000000c905c00c0e00c024210b50000008200001d20070250180d200402600c0f40c1d00e420f40e1440400300f1039004100560010b201e0703920074800c0c2501350141042004852400b10301650606002a80301c03401c00c1d440340b210741e984030b60800110b41ea01881d1680703919181d07081c158283da5030600b008440c0c00480c40705514013808000124560060003628000c6400d600104000c1d0030600203000910009000e402c0c5a114850301c04005039504050f5611407061f503501c83e83d5801d4504645400d0b10b078141c2000303100d241150083c0156080000c140c81c0e00080326044549090400d003001d071a040072072010424000c140004840d11103285000600854402030203c80841d039407030f0480914000c2c00e1341c0c0009881000c01042241302880840b40c000749000b41ca01d07a240c141e8480101d43d2010140e40844046000801d100300c5d100c00c045002c0e128650342e80054442d5450b1551445000034001b0800307124142c2c0030801c0c1c000e01c2400d070501d100941460100f4200c1c2c101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 876356492 1250 876355242 876355247
    0x60c1204120506160f0c0515010906050907031107030c060b1518010206010339090b01111b010503090102120f33040218040f0b011202090a050f030109080a 68
    0x100000950301c0d4401c3c040841c0349241040c1c02e083ca98852030340c983c420710846031000c661000c6003071011f8a15110b030206d0380c89135110321620b4038000e10005100107410f03480c000a00c440030000408a1046c10316100c441d0924007240c50440d00080d44c1450119200c00991504c00001c00c50b168900e82c019103e40303005c0f2188000307900140110700700441180200440c0d00e00480e9103034024003009005000407103003610500002030281404220010b003004180342c0850314100c07030030302c00e6000907030564656416502c40e50304002e441254040d050003405017191003440fa08090308251200a040120000001d00401e801398140c0d070008407203203031702d550b0b50034400c403a0101000c0565a410288005410965814030113a2222080843c01481080b00c80d0206007040000e402c62006000f00580800c00c101d919552481b9010f920310050000040000d800030005104c800200b107a088558070400c000a450307076a015220f801c9078800c8800031030190801022178050441c6501c02000280042401e811968 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 876357742 1250 876356492 876356519
    0x6025a07060305010b040317090301021209010c091d060112150b090f09040b01030b060a0905040503070b240d0503090901030c090e01060b0306010f09030512070b0105031605060c1204 80
    0x1041c03a038052180f070762038452083d001e1190344801060702140d07180c3d40e42d5904006015011000b0010001410041100d081440302c1c0d40446620b1000e940d240c2c20070311695042244e201c080d00d541074290181092031050b00e125540043d080310706100003010040c11514540c1c0020b00650382c0000810b80d001c7d075550621405801005078a0712070f048450210001c0d0800c09841c910503074104001d02100c2e41fa588490f801039201602c11500002c1c0d100010400001c1e5016160090344180029565418681424503104e2005400c05000c0d0449000880300200200307003e20460004032280c1e64151240d20b09a440c601c1001c08090300804900700010602c64440802012107920701002d201c0108442c01e404e080b54801e000d0700c503181c4400d002041903548a41000240d21f0514104407562944a803291450000d100f0750804010b80009203d4042040c0700400d01e0040c442600100186002064007a001680f6805024010760b0040340c0c0134003100301001820f101c1d800b45030100f03079503e455410318408907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 876358992 1250 876357742 876357749
    0x70f08090a17121302010e061b0d0504140d0c051c12050a02150408030403081305071403070806010503062a03070e120312190209040f020406025a07 65
    0x1c10030100021100404c20740401c4091754140d48240340c480c2910100321194124080c280d2600100c04011081c1000c00c0041070070351582c0f0344400e915903147c10f00c10800405600207448c000d11000054100280c01e50f070f441070583c1e40803641e80b084c400a803284100c4042154801400402e484c00340891403540190040c44000c00341d03420b4401964145650300c0c0385c0402624020003410301080000d01017481100100d40014600c402070f28044569110342d894161207811044945407130310085070148c42d04110800003400b00e00e01812196140c580083c0c1ca03104010110440c3c0c8503514141d071070340b07100002d814184640395402c40e40c50382801c1200034005107a4038545400365011480038405180000117880f04690a84040019030355110101841c2c8800308c505500740c0398090001011540d03d038010300d01c0d0341c0180c641c0140c80f1032030302a0003450400f08808850f0100314010b00040003542503007007038400d400e21483d02201e20f8000d40c078500c0c0035503d2002c002c4d144c0a40b0268a1062100811403200300c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 876360242 1250 876358992 876359017
    0xe0d08210105030a031706130207240603021f020f0a0b160509220e07030b150109030b130318060f0e090601050406080a14100305070b03070f08090a17 66
    0x507030702c40c0e040c1541c45910400c0600800d000c85080300780844120308481c0d01c1200500184200340d40003031001d0607030f080280103c4100800c400f5660b5600d03282012281b0700050120300703010ba039145801081140314000c55001008801e4210305440600812203404040d00c510304070307816841241040d00030180c05680008003401c201c2c08500e1907a11039415074824010080c218980b903c4880026488180580e9500c450300f500c4071034401c101c0006106201c0254007944c03c2c001e00e45031400d241081d0080889405051020840051000c40c206024050788071510000b544401c6000313086c15030314604094045d000c0001c0301e00f008980540c1c0030305440001c000c0758403129488212402002602c2d003040b078016000503c01c2c04100103007441105a1908400c80c110002040324900c0904140100d08580496664000110400402100b0000c0c0c00041104c2d04440e41181813000c030007804607a100b0344440c2003083c540c020070900da50502c0070030241c80d80281c8007828841c1c545208091908001d103003215 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 876361492 1250 876360242 876360307
    0xb040b040317220c0801020a0203211b18040c050901030506091501121e09030f0f050301030605071709010b030c0a030f140a061401030b060409050d0e0d08 68
    0x490102c081c1c0c00900810803105003184500d20841460703803900c0701035410b840360210010002400e01082c401000703002800d03030107103645610340c0e00214035145080903200310240c0040200201440c100050041800c0d0181003e95602c10f11640c0054501158448944c01441d03c4404840560003100801c440b40742070b281030041e0360b00d070700410400c80000c6842d1204420340721000080c0f036101324140420f100c1e001c1d400007410b0310011140c5a8000742690800504da0750340c100642451707040010325130100d203a0714104810309203940c00100130f400f0600c0000c00311034840700440e089501071030401905124001c4842424900254138902a09140c5e2009009008041c000c0d891400d21361b40441c00d030f030303089580c6090009030741d82c41104041c02101d2040990262612520003c3c4440c051550368410f1080075100f1035056050080c13035500c0c043c0880744078602d0110101c0000e5008a020001c3d5045030800780445011702012400c400102e500c000e11380900042ca00360b03010207003514003200614034012804e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 876362742 1250 876361492 876361517
    0x20a1209140f090402090c040f0b0307030e0616030b06211f03030e0d140322210b0703060f092901020312040c12050607080603010c0e04050604090b040b0403 69
    0x4180b0480342c079005242c100008025080c500051031f001203080e41d405250a50f40d01005640000541029402d882c0c004180f240781342d03144c0510320100c0e2038680500b1407401c1c100120504030302e10000500625443d41042580380d52140d065420f40ca0700000c0035140a980e04e280004e0380303501290212081d203401401440c4004d0313845145000e07070f585600e500141c00440010822000034580d01240e036803569000d00b014000d000d0002d8051010500d002613440100b000034050b4102d000c0e08070154208c0d01040800000e524913610010303c540220a82c11a905e4a2000b14054002500411244400e00400140e1390700950320042e401854504414086280700c8501c45042e00c42182150041e8821f00030003030103035020300f1882e070400e00c903600465480d81d84152104502804030070613102e582003142005082a0803551856021104400030804044846805003110103001c6820380219076070000074030b40b5201c0b94060310105030003500301010380c501840d044c5100300048030304034000b40e500c034041c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 876363992 1250 876362742 876362749
    0xa0b0a090b0105040501030f060b0a08150102060708011206060905010609030b15090105060a0c0b040c050414010f0b1b030c03070330020706020d090c15050301030c050d03020a120914 80
    0x4040300041691494581807030540114058032140384100300b41c5275989000030718007450b840142004c20341600c1c0c40e0040e2601c80ca00350324130350091490905540040007040082c982c0618002c1c1501c44071148420b100318503042c04001055a500308264552400c000400c9090700003244c0ea00b141e104524405080d61a02100100c074010108265004005500180260f103041d130050b105856840c038015400210303039101c2902d205e90940d001d542015030b150090040c2e080501800841501810006800354946008490025454840e5881b0820f001c50040e80c0003040b226603480c18403102088070f071541000b44815840c0d900191084010500701032440c3c8000904030a01c0700b000c0c40c4070382115a80d0961071610784c081e50000f0030440d0100c0e403c0021900360a218420400b006014540c081c43c82070a0400031550346180304401810b11605100410000c1c04034041103069600a81e500c28400141c2e26040e0b1a04c41c4048000f0859104040d44420701a44045091304403491b80340c00040c0ca0080d202131 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 876365242 1250 876363992 876364001
    0xa050a1b060311090105220b0702040c1b200a090c08010806011d0c070f0506040201020105011d15270907090603080a030c0e0d14060603030a0c03140706050a0b0a09 72
    0x1e503d8072105102400256004130b01420741d169202402d46030001e071075150340035081003d8000c25000c19000c0340f00e40560500d489a00b80d00b901c0750400a00c044a128180040c490300f2000c001c142070049483c00c0c01c5101050400810a03002900560886413500c103e04060003d050b0940d002070302c4c81c0000030354080c0000d8898129104017a5689000f085070002c0015100d0007007102c50741100c10070440f00060011080c83c00414040d4000d0441341c2032a2000a0070341c0c5041c0c0c0941c8000329202441c01945005080c1c00c0e4101003042c20301ca00729000480421031002c000c0318100d454a00c00c85410714151051300d041440784094501b40c4100d07644a0107110220f0382c590001602c41c80c0300b880104c41040c080c0e400031819403c282440004491820005941c150300484216440c120201018220401c100501c03600400102d0255081407540440140400c01c1a28080c04000400684444404400044824568109809008a140035200319000e800c140c1e8009004001c00c081c00240c00926105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 876366492 1250 876365242 876365261
    0x818010804231203011d010e01140402300703060e160e040b03030f070c0f080c090a09020301020d05070e0103141501030b09010603290612090a050a1b0603 68
    0xb0002810000c07120080848071503500e180320074840c008007041e8000002001d18001c10b00a041450b43c0d1400e1802c952280e90180e018500b20840f6800621503440740104807880e409041d03c0040e10341001d080e24560390003c201e1400440c034507100c41d45900c00301c444c405510602c0aa03c003070202070b90300e5003105440c200c101d80444294485007403504025209000c1505001070041012800951400009003581d002c400704021b480d8000070b00c0700070020000c10303180040020759104403c503884c095103652503482000e000c0e4480d106400018510942541c404510741d500078000310340300c1c44c81107407000c0100010741d91840072274100e41e02c0d01da06610900070400829101c0788403450944900e26000422280c040c0000d05040e1954860589900d441410b28002c200310381e03001c035101c40000040c5105071084018180d40500103a056022502c4290480701d84d40020200781d52541c2e03910700c0c034600341281c842008000740070f03900c40c503001d1000400d0040e904c4034403120b8000e0042d6443d201a8103c80c201e81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 876367742 1250 876366492 876366503
    0x60920030c010302071110020610060519030c090306020f0936060102150408181008060118080f0d020d05090109050f040912030218090618100906030818010804 70
    0x340e0711841075100350082c004a5106902013454202901e0004180d4001c01040000590180c020412040103202d1200018036041c181baa10b030403996201000a03c42042c260028940c440741c510754a60300c50307141c01c001142c00c000e04544503c002c46051001398400f050381c900c108010f28400d01c03691280c400010a0140c008229042e0340b03107100c030380911100020000d03815070103410300c040f80b507401c40041a4421885400c240d9510300c1201c41031344425000c00101401080b038100e0796110136400108054010209083ca040c40003030281040b80f201d10640c0040b02c1c1801000c1090500b120000340a858404054090b110440f0304514111624016180700c0790000d143c0715402c00c002e00b4100203c810440000d003001c109450b1f161076250446c58041042e00000ea80011000c2c00000c7c007048003039580e907003203544500c01c0c10908000390b0f90a221218008020008201003154a6a04580d4400401c0003c83c03d1041c0c81d03403800c01903101d41101d89900c403250044c0340c01002c05d602c5000c400d84030f240d211 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 876368992 1250 876367742 876367753
    0x90703110609090a090201050c03071a0c070c2d0b09010305061210020319060806093901030b040c0309110a06050301060f0201060531061a0f0d0906092003 68
    0x1500c000005e84000f99044e410b02030b003000560075100c0d00b40000c12500d4000e2200003030801048181c00105400186680780c080404e200490020341d00c01d26000450b4013951044440d00d00c044405150004a021003090f42250b41600081090182d0041c00800c17078241c90401c03d80c1c0c1d6030350501a0b580e091000507900c0e0b4102c902804c2d81101281e025580210002c3d501c9101507403401c000c007007194401d42000d00346602007420003104034820002005e00040c0d600110050b003030072071540181c0b800106074002086440d0100b031107aa921a501c6440d034480020070074003103849540409801070580200a880e40e64004842b014182000362249044860507943c2525607803070308400301d610f11138079a921001c554031a41c00140b81e03514100c1c003079400503107040b03002c1d4104005802c01c8a0010038420241205040510821001c3e0038049000e601d0848805817aa642521032541103940c030850103848000c510b818001c40c140003840d8446142039118016076000350f20002a10b80b5a5807901c095141d15134800c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 876370242 1250 876368992 876369001
    0xe060103080f0f0405040f0912170f0403110a210c050316170d06051c05122a030a0306080a0807170c0604242f040e09070311060909 58
    0xc0c00c001d100348641d40d0f210600303094850300002c0c00c4c0c034513260300d03042c6d52522079542c2c4042c80840303031485021303452034244030f00c42c240d509040b908902c00c0100340244950002c03002400341400b0340300700011242c501099440990b003e190074a050401225107515802c2030a01c160a0710340640303240d40e59640c00130001c42c04e05281c00b07902c48111604002c103c1c1c0000d801000401113002c440040c2810000c107110114069042505000c41d210b48600a10720f070202c81c4e1240004100c021480c410f4942d80041c07415602c904080c070368246d030349400074140707000b00b4040c001e00c07505140440a040408280d603014400340c3d03990b22204da500c4200d241d014010a404006420000e240010380420412010008504240800043c00e05201c000c4074152141c40720540241b0340400b0301500108a0882c0340b2003004001ea400150b01810720345203040c1c0880c4108c007020701030b205600c0c0058400520020390512014500070010989a0500c3c0c44222030480360140001d0716880d11b8016954400b401a04808045d1344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 876371492 1250 876370242 876370267
    0x605030411030705030d020a110117040308090c100c0510020705060118091e0b01050a06020304050d020406030203012d051b0702040605030d0306050310060b030c180306010e09010e06010308 83
    0x2003907800a505104441e80000c0c561411b0140441480481d005010b69043d00d060000c00d40c422400c01604011a20240b010002c0060034050340141d0103140c00c454542e0b41110243c0f0705001c41018aa200c0354100c0fa42c03c110340c3c0104044419403246d02900c001c0034141c43c00000b68001c0b1603004001c0e82100c00144900c000350880d0000c1c81e500d199000c03820403460380702d5011007e1451502c0c0c50f0310301041042007c0c040c0390141c150041c102640c92115941c54513400030b44070b000707600071503100700c04000d80402955920341041001d190010002c00000b040111800080810032800c00b100f003214031005819100e00340f1410340300307040c0ba182c400841911603007c0340c0142c1c8415401c0f40e1242e0748039170114154604000d034040c83d405c40d0302d0010b603807070500040520b81151800711000c880c0c1000e0041c0400755806043e6078000302850205078407800300c03900c51348000d106070042c40e0b00751141c82e0002404643c60003169000b83c0c1c4640003048841c1c00d40f47d5454440c8000d0001503c002001c10042d0468007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 876372742 1250 876371492 876371513
    0xb041503061a0d0b1f030303060608060f031903140d051608070c0332090a0e0108030a0e061c02070c05190509070203090616051c081f0518010f080706050304 69
    0x1081109419101c04000e14017050071a641d800c10390020f941c0326414003401d50420f40d181c6d0400000c03181d80c2c00c241c641c5030010f03503903003040c5c0c03140502d0030749030102d5038200340c02908100c450010500c0240c1e10303401c0c40040f9000901045071741000d818240032848003018022071070540200d04075076401d02e4100d800d8900780c40030030300b0301000240060316492802c68246d1102d088100c2c1c1d4007004140307598980280c1000700070304040c1c0103098042040302c010409a20000110f03841e030744540c00c028100c41c2c200c500085e107500130480d4841c04480d5040b5098204000d66000f40320051062240b07903000354071001448564014205440d510341b201040c02e100c60300d0003101d101d1740b00401d481120310304404500441e07440c0d000b0248043d0600d00c41880e8204200b4184030203804c80282e048645082d03034548200520000000d892405d40b25100401c90400440d0900c0e518003408003d4040f1034800001c440020200030244034502d0301c0d024590b0041100034003c01d105048401c0d41d9141401c40d2144d1300c2d902600c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 876373992 1250 876372742 876372751
    0x161203290616050109050109020a060f05041406040f0803030a11070201020d141603050706050106030b1c0305041a1201060905031047010206010f060e01030b041503061a0d0b 76
    0x2031029210b1034002820900406880610a01c00440e07400070b10702c1448046c1040b500080284010481c1e040c1241d07030300c032741910b0407500b8560013210301c0300821001c50524407490b008107100b410b14074404104400e002000314007510b881c03d010802003810081e014000d005400000b03006030020880e149e40e8078862031003070b00e80c5148469590710b01705420710200d008001d06502180455408500f640034000d03140304141c0140058101404803644110001d40e005410f00c5440203102a420302c1d0009040c4100191005010421901d01c1c4802100c5295000c0d5000781c126080403440803000421600e10501d0000100d81d409070040100c00c2c2c04042c801c010f07014400b07d00b6050024070700300b4654107800d8a024000041041c0603080040300500981001c031281c4041507040d903111600400c005400c000312502100c842d461b08010601c5144012400341c08a5400d440c1c0c41030404540301c541d1165100352004403403180314100000007200044829040c0c0603c0724980c04400c614001001c1640310040b170b03620 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 876375242 1250 876373992 876374017
    0x90f070f050f0609131b200601030b0c0403060c080103061506080631020306010f0e030607111006090c17060a03080f041809110f030a110301021612032906 68
    0xc082d04081c00c98219003040b00c4481c240e6088080200f0303250f42259074a487c0c40480c018604495240c00d03150707a40c0702011b2000500042c146000181071704101c400b903c015582c004801c0c440d0710052040208000c1003800b0030784c0c40700d00d8500b0780441e076000c1900d03690494505441b240c0c0d05a4a01c820405103109540c003145541040350309000040001498003481842d20690040e100c0c10014001807600c401810003030180f0140c0d608042c007075900011625803024480c64002c109089003090385041c04254010030740124200200400c10700c4031038100110800c156075a010203103400401d213400e50340d002d0f1903082d003050f818a411303c0418107080c02848a202d454006601d85542e071102080407254075104929a40d5840a56000700126400c0390340f05214100c4050105407501c1000984800c02418003d1240c00b40340d45000c129282901178a00018a2040c402845691814180c406000e010900b0000920380040c13240c15046100399590541c107650012420710503040309201c055405200b85441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 876376492 1250 876375242 876375259
    0x51c1b200409020303030f01140d0503030f0408070b070905150a081302010207050a0608010503070b07080a0f02071517060103060f030f0602300105060307020c0904140303090f070f050f0609 83
    0x3d030b1070400c0194050701446c3c0441903690700d0110520082066038a40b644102c50304a16580481c0000060f079070883e90f807100c52411038a841ca0003c0d00c6114850006200f186600100b05090380c0016027402210340a80b990080c104142001380b20314480c8180d00b8001c509690085040401843c0000107881e00c1801190300381611440060b00d00109548800006062400140a00c0c1014020343c0300400c0d4501d21581000611791725614140200c1c48600100315641202904161003040204000c0402c4171210310b041c0740045004000d000c089526500690014020a11f1544280f040d0004c9074070030300040706810708680d02c41020080c0204250350140e000e010300d2145210800508030080601100644020040902c0501c00c00c816071160b881103400f40308021041c1d03004075a0512111048500e0340d419903031440d01c4d9440c86902181841c15120200030003500c1040010290002168071741221422507a41f14106540b0b031070b41c05119080901c108091846080450141c00c400100501d00d2030b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 876377742 1250 876376492 876376511
    0xd080a0603051c0908030f12130c0b0c15010f0e0a0609110a1719020d0f0905030702180412031d011a0f0d1205070f051c1b2004 56
    0x18030f0f0454604041200003007205000b03400c19041941e50b402040c2d61405942040306501102040c1d000302d005580c1c00d60042c100055031203840340418030644c3e608c59403204080c0e486020585440d001140b5102052041d4000440400420103a5604841030020703103003001410406c016092220107840f602d400ba45860780845da15003680038064040019041e0380d034807400400802420650135913500c580901100060208403078003032101e10815460080c015994001d008019001020f00e000000a41ca1030100300c0e8003009400b10041020743d008441080d0f01030021000c0c0d000d40d07101640e00602030b400314800d202007140650444080003060b2030b100c904900e240c040e41402e66414540c1c5440c030741d01420454131545000c40341d03401ca2400aa03131807550811540e90380d005903520b0003205024400c0c0819000c081005a0407e0711220394001c0c107480c1d03490816000ba503824100140c5101c04034440403548040c1035501c03a072440920350005c010110700c107018040100d020009032940c540050f00d40a802 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 876378992 1250 876377742 876377753
    0x380105010f020312090c041a13022d0903060108030a0813030e180403020f0c010c060234030801140303030402040b01050c0d020304150201091a0604090c080c1306080d080a0603 77
    0x103105031001750143c00e0076202a801c02c0f084540070040c038081021911001c2c942522840003440081c0a461801a62003807041851030245112510303d075054400302c01306101e8070111000ad40702c1000c00384e00f01c4a5690725044259104d0003091701c000f00090007000001c910702c1880f03a04080c0b05001b4100030341036050f6030300881c4801e203207452903982ca40b034244103120400d80e042012070f001c850302c10041e001200b602d00000308280141b248c06070450b500450310000314003080d144103030440d549080e8071801d24030070000500ca590009606a001c206d580e00009130b088407142a2000c00030000303020794650b80d1641d003003000504440490904100040c0890000024104030002440b1000d40040d40c64610f4914800c60079030010f800f540c216418450a600003c0803c440344d4010702c10341e02d218003d80d0343c2101080041840762406891142000c00000f510071010070035101860b000c0c0d9898000f20540032880043d14407134450480701d54407424a01b4000d511509003640c01020000020500c00d540380c5aa = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 876380242 1250 876378992 876379027
    0x1d19060201050f0702011526030a11070b3405011503020f1f2d0306080606180c07020f0603101e060f2604380105010f0203 54
    0x181025039555070901c404100300c00380c0c29610640d90300c000d0040c40c10070040d504440c4440c2c42400300e40322401c2403030341c1e113200c42649014500c40c10f00201c81d1038405105e00286608600086070002e030049440c0400c0f5070a00d001241c8a1210341c040b0700c111039881100024501040303e081c0060703803034000000400224207000703c217030400b64840c0c020200e41c254010860140e0866206900c110401c1072034000c2e00041030740e90b45000d085420700a00071200102c501081107800040303800704ca0100305c038030103406030503038401c0003684c202108a5030f4503515901484501480c140c0c0303000409405000061000401e01c00400d101c0744081d003070200319643c94000c1800d07500b06498401034031181e403d0034440e640c0e0f41208491210729800c4c519248030700c0d00d20098001c01092402100b00549034542d8207c400c0343d60000030782d00040aa104285140c40d003030241c40e0560324481940c1220b2031103600e07200840002000346103003400d00c0c03489903141d18000040d103a00341c07442030840550100740440c03074a100c01c4564 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 876381492 1250 876380242 876380249
    0x18061d1306033804080a1808010c0f0c0507050f0a2402010b03030f070f2915060c03040e04060b09010303050306010216030f021201020f0c01090c090b011d19 69
    0x210b845601002c40c01da0f8502c1c0001240040688000310781d114640c1061a80890f00150490703001a614405000110b894003400d031a0030309650160300d00011a513005501c500f40114490b5601007040010030740c1140c006540800c00352580d40403813000d11039854081c0c501d00710350754000e14402c02980c3d6803c0a0f07003c40803000300c1c41c2900400215224013980c0a00413900200ca04030083c503d444030041400c40305010769440a440c5c0790a4046071004c0005c818140080b50880d02c4444100c0c000601c03482c0310f490011100010300b21030ba00740404c15400c011302a00c0c00c51003000301560038103050480c2c4404540f8000c005807031245d20740c002c00c2002d07142c003030720103000e14041c0e914151b503443c3c060006071a00d040308450b4074808245400800216108005500f54a03a040fa580d83c10f10000d50842400ba00800b10300c00c100b00e10004160082880550009480768070a84880304000d5071001c185c000c44a0800c030f414003049000a0900c9003054181880480d43c000810305d0000b043c4035203880810364490341 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 876382742 1250 876381492 876381503
    0x1505030f0f280b0a091a07020f0c1011030f0703180b0f0a050a1106130b090f070e0406020d14240604060f02030705060408040618061d130603 62
    0x2070030000100501102c00a140500310000400c00080141500044240005814918400c001c20722405860300440784151b044504143c500b40b582980c0c00c0d0380401660682c0242c468001c0301000d4050201d01005000350081041240d21007104060b640d201040e43d6001c100d01080021820000c880b40203001a640a40e440558010400342c4801c0100c4840e040642507200601800510040290031613034114220f2510f07035115900d0312000e580109402c0468046402044100441c040600580245a038000e50101100707846407500c854890b801c0c1c040d0800a504010b03010301c40342014500c00d81c0c02510881c001441c000d0b506203030780104d50001560349440000c01c0300b0300000da118011030403404000501c1c0740185603c9580001c1c0c051195100d26410301c0701c54480c4024490080c015240b01c2e54010040c1d13880d91415141540c1d840d40140503990108a01242c02d00d1141c2d5001200b00c16100192038a61104001d44080b640c0c20103c84400c41d03102541c6403506820380c80600a20000b144500d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 876383992 1250 876382742 876382753
    0x1020106170a0b09070f050f0102240714070b130c030803070203040906240e010302040807090b041b021209120f010f0b0103090b06120307120804030206010f0302060d1505030f 77
    0x3e2a1200301c40201070301004c000d6015140520801081c00707581811034400720f42d00c00a40300c0c0e000c010307401e08148054060850300d8004021081c3c02070b980340306206403211780e9030280703440d9841041c54481c011460702a00685411000401c01c0301040c4000070320901403210f40103215946d07030b580000c9a104071051801600041020410402d81c1c0c01200c028090005651008811444ac0d018000d0204142d0000300b0100721402a50350b402a41191b02601103e402d03140340f01e8945405c58060010f02c051140524902451201e10b04501c600c00c07040d00c82190301800d1a8450401c10880c06d07042415201ea020040d11031040e90320f0010004202c4184c0190000700d1041c900170088002c9403085c05091b4141810000f4100c001071520500c0c0341e103e1800c60724a02514458081700b0320f140644a00203042d010184841000c0c00d81120039588550720036401c0b6213035130381c80b0214071804d80050712000750080d1050102404520060700180902e840284640f1070b201e560b000068a0000791005054603034012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 876385242 1250 876383992 876384013
    0x1502032a0715120b060d02070503040503071a070b22060c0f080c1b0705030627070308030c07030c020a1205010f050105030c010c030302130e0f09060121020102010617 73
    0x5100038001400b100405074400d00c1040c20190036506100d60000d461a580c41c00d4010a5582d030090714110b4102010454032488103140c0300d5a80e507c14040c0c24420b1144480c00515160840d41c2c10000c582c101d02140d050240c0d07940c4408141c0c4018000c1c540884003040ca6100400120310000c0b052401100c010600940214000c0c1404003c13800000400c0300181c1000090031200c41140d0080707c0300c0360554250b8680740f07039031070070144c40390803890345400303400c0078020544031862188101d000310300710001074a841c0c8060650707142c12502c0000d140180c01c0c03000481c06174100000d001114002e060103507032030010b07034001a110002c0b174200394000241404c4030000d2000c00d00c41c90045400c502810801c550505d00000d5440684021413810048044800c90805200760103482c0c000b038464114124540c1c07a41e045485a29044683d6185440c00c0c100003040b8640018000d0304840c9030182841c0c4003000c01d14000501068440e05a05541d02c03840006000f90a0426040034105140d0141c00c0f2602e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 876386492 1250 876385242 876385327
    0x30f1305010806030d051e0408032d0901091802090306100923010b130807060906110d120e0703050f060609160212071a0411011215150203 61
    0x501034030190185d8001c0c443c40000036004811a1902c022035001e400e070041a4000a070541c0c40b994200c4006404042004004111b000081900c0c90b908012009000403900000081c039014005041d40000d2440800300301d4030031050000d440381602420094a07081c4228082071030070006944034039040c11072403000c12840c00540300d40c0da2070048940f105030b81c1d0340c0c90300140e41c04540103001e1103d071100000f0303100a002c0d0a0384a20740c0141003c109840d0415590300b00030704144083e11841001c180c0c08262030711001004601e5130744c418059211000c1803485006840010041d10101256034820001c010011810070001d1080e25030003a4001d0140c0c0c1380501c24000b0001016244421800d03e440c0104130190f00460310945108000e0301c01d68651034a401c10020b07495501418a00d81b031106018002841902007003009045001e0326442c290f000103044e41c404071800e0a00c6441c030700c081c40c80305109041c0281c403240c40b03003211481224140421041058603201d90500c154401d0f58100c02c0c00d140d800c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 876387742 1250 876386492 876386507
    0xc09090b040216080c010207020a09051f0605030a0c030b060409020714030c06180c1f02011514060f070c1d06011407140a3e03120a02030f130501 64
    0x108165801c1d8140403c0c034100c0c2409090a60005000c54004034101100900940c142c0e8000f9400030800c084032581e580910004140270ba600180405490704010501a00d5100007070481e0340d29500c0d1483c41e40c40e109518028800301003103100705038807800f003000955104070180000d00086200160748109a1a083c01121004081d1082d40e400034408240d080e41c0c04150154072014100e03603080000382d0504c0d1141030a01c420340d4240e00000722032040724100c45013190111243c0e00c0340c000f0402c83d43d0403c060a0b01c43c91074804c0816130340380d000c0c81c1c488504014025000d501d80012245092441a80d200011210541c2091308181402031020110001c0746001507082142820400d50071102826103800610900002420404180030300b5100c481c410000351154580101c0083c50031091200d0700c400082e078812105100d1080c800c1c2624a0001911881030350b420010028845103000d41094071954204034401d034194042403040084051410700200075a42e65861940005410030b0005480325 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 876388992 1250 876387742 876387761
    0xb04090f0c0807081f0306141503071206020c030f03161713081219060e060d020919020703120f090c0b0906041e09060b030408040e07050408010c0909 66
    0x1801c00300210401c0b074102c842507403c94241d00e030003400da50350840700b9155030104115110200341101030010600070a43c2c001c140603e00800354034a16255041c40030074600c40c000310f569040e000718208100c1c0244080f0900d62191080b4005402c207181c82c240c150840c0c20090001a070614000108024800c1c078444036000302c2c01d58101003010b00300d00b450001c0c01040c000c02c180391102000f14980d00b4004031070141c4000d5076541052460394540078942d101c600c5220801e031242d01d81064008a1583c1d883c80c0e41da0f1152101901003104d00e00c69800b0010718000140c03640304882030455012000b1011400142083d41c06030300c8105000032103500c10b400311a9086400b201461421400c4000910380040820440d480b65118541f200f11041c00100d40344940d034000320000c1002c010680c82030821040f00000c80301c4506040003120399858880384a07200c1198000c0c6101c00410051008020200810b900810540381460900d51140442400c40b041c54071264041055108c0c01c014201c0e041c001c1c0081d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 876390242 1250 876388992 876389021
    0x70f0501111f0902010306180606080a0c170406150b0408061e04060b030f01061701060504020a050a08070903020a0618050a061209020d0f23010c0503040308041a010b0409 75
    0x7600d9400c4280182d0010480c901c110054485031031a040d603220b83c0050028104004012581ca0007840180000300b0052180b400450751000000d81214072a219402e1403030a103803640c08406142c80e080070109240207104551090742d071b004407019569111021b0026103c40d64850703a450307003007550302482c010004106152002d19100201d0741135101c0d0400030381066020350045882d24507000000d00b4242040680a015031a081001500c03046241c0115070001c4264004c1020342d440d90f0520003a8810200b4007070200d20f040100040d2544180d550710b50007141c51415400440d260382c001904000d5036448040011102c6819140c1a0845800b58004050455911060515012018000c0e440c101c80d9800c030325560303106000075034444070080c0c911198441826841a81c180c5455070041503642408240c8048040c1501003180b014030038402d500500780c940c68110765550741c0c11240d290008000b100c0007110060200303c1500680d82117800f0308041990700d030300d590900e40f41000f00e8030700e807007080031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 876391492 1250 876390242 876390253
    0xe0f0c0d11010c0c0306111803060f0408031803120a0f050403140a110609070812030601081611010f02040501110309150a0207180b010f080f0a02030601020c03070f050111 75
    0x2590500d01c4403041d002070800c42140c440c070341481071031111181e00142030349082c0919640c1e02400d0100400514030308000d00c1001c0f0041c1d200307240d5215001c942000e0369a400e00302141c00b14142e07801030341e4850105c2d47e0034841480d1800141e411034200c03441000e056a141c009000f66908036003d4040d11210030b140c200b00a00c0d20352002828a0900c000030b0304418400505043c0710340c420000c540d924100e000840743c1e58100641d100e99070350507503c43c02c61280102e009034a058840081100e0060005135a1980fa944034030004100d40000d03120600140a404504940c04640a0081e0300b00003038640001a143d900e0100050300038901e0075010f04664008000500d502c0c0e951048000e003004410115a84440d18a1402da203070400f40e81140c40700039603414048503020007582100c007809200b03a85200254910305002d5418280a64110020002e01d9000800700b864a6024551043c8144122402107410f0707000309041031610b4000814001c4466400c3c0010358202c1c21800580341000010807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 876392742 1250 876391492 876391519
    0x1270905030a0e0f030c010324030506010f0819080a3507090317070f0f0605150a03051b03070b0403062f071b0b0a02010b13021c0f09060e0f0c 63
    0x1d1b158143c000d00c017414541c0d02c84400f0101c100003050036006800b485080c2003519140d0500329030324182480f0380c883c0034040783c20225200f00c01140e08091180444002c90351190140da4800c81d40e000480b4000030001101856100207800d00c0c0c855140599100440d1182d040d0703202100c4000400505040034801d40305401c000181069840c03118801c07070050714589605403854120310081d0041006001c2c92605500072003031040d2648068069a20300c803010000002e29014002c401d10f60b84000b0748a41c000c4504003010000c00f80c503401d003541004066583c46912108507011941090b001640c141e90348034484c040c1f18503034036041806039407c81c06c14580c45000c41e681c7c401a10507004020040640411015000d0072600095005001e0f8070107a59200e448a0344000d008000f8140e201d403241002142c0b90346118164400c60b02e040c5040800c60300b2090200600300d000d000c09400381d210300fa40e06c0e034481011440a1060001101c40e0324060b00b440001e0410941c034000380081c00d544503910a1241d603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 876393992 1250 876392742 876392749
    0x102060603030406030f09021017070f090e15150a020f280c0e0408090108070e090c0f070218040203070e06090114060d0c02070620030301270905030a0e0f 68
    0x460485420b85400318000030506d51220140503c0301c4000d410050803d0180341c0c45820440f103c1d203035111505200103984c0c0d020401ca070311070404140c130001300e0700c0c1d8002413142c04224018943c3c8800303c244900010308004021646c00038402c40540c409881c0480c902c809160b045c0903000502e2018002480c010001405004500315204400030300801c45950000421140340d0740c1c07a0003040c146003080c07064509810440b40030b500c1426542c0c00030b0b14210011f07074840c0c0140d1026030882c5002d0b00002c0c0c40d650b644803490b030302d5002e400e503c4001c04003401914010390302c4030210b00403821250800c903050309207071041c1480c0034059040100700f48101d504110075a1108441c3c141141d114000ca80b105420510104080307120700c0840c02c64150501d90180c04d26a000031340b0b141183c2c071a55403540da00000c1e0035040d07000000c002c685040c0e80c200708010007a45200b0b086445400442400c0d442c600c40400848000b03c0e542183d08542d29017000c1880c1d5001e42d089111152000420b0301c14048086101001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 876395242 1250 876393992 876393997
    0x2210714101d1c2f01030221100803070510060503030c100c03020d2306010219062a08190902030303040609110d0b0411031c050d1e0903020c010206060303 68
    0x15400303003040c00d0102e6502c1c2c0e00c00300140d5100313800c84090a4140440c1214229421161960090310b44010610340a594400d01c00c481443c000c070441d881408541c600407001100001c0d10b56200d80303a07801e2000c070742007030144010403035180701d0b0004000f56590340c5207100c15600241e2000d44203030002d00c5907810121010a500c0010548150001125849a06d0540081c0a4022026880d62814200380154401d04e110301e500c54204401e130440e155074035001240d4921850080c44460580e40c1c903903400081407600b0040301d100110000d0980d2421070342600038101c10310760320344000960103002d000525640902307079210b82c030031454180704201c00d640104e40d80c1c1c84043e0000313081aa03526091001d000c040d180d500d800c2c5500400302000505281000340303140009a405030f514484540540d80c2c10329000500c030355400000f4000c07011071a00f12030150740c2508820000710321581c49011002d0a070144540301810549141000a10401503050083c608003290483c181503610060a000701030f5000004d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 876396492 1250 876395242 876395297
    0x30f06260f013c050702011e06180515040e070e01150f080601030e0f030c060609011d150307030f0b06010c03050f0a031407020102030f090d0c0221071410 68
    0x8500107074480d1458108511070011000441e0343d40b40c103050008240d41900725559241801030b4115031a070020311003204442c0b45110300f986801110392896185104c540040e40e0007030804c8a640e008528000104066800745040e00d03810340c000100034480c8440d400461405480c0110722204101c0c03d0180c05080c510111500ba4140000c100024901ea8400d402510a202c8501d069a044000c2110345a80d40d4002d070300e0f8114180105400507001c1d04101400c0d9040b90705290301c49580400c0e8680000156001410440c00b85081d40d10111a5480400c1800c004510600600d00d030304e05241086082400e028040c1d41c1003021924840700800c2d031090545d040841c05018aa03600c60b05800180d00a00c0c0c070444841c0d40e0742880f4104041d454040d40558440d00380c54050203055a00c203a240f9443e00308508001010855600c9070301c1c0581000030050710301d001085c500c8604031501c0c10032a403514106912040b001c60501c85801e11508000b1640c0c0005001d03401d0107000c0c141d48903038088031850a002f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 876397742 1250 876396492 876396551
    0x3060a180f050a2f01031e0b270f0609060a0303030c1106010f0503070510020d0302030417070606030512040e01121a1f050a030f03030f06260f01 64
    0x10030405000b024010000b0083d400607010301101c91079104d8030b05030b0f90081c5281c0002c184012840000394024040d00300140d07647d040e03184641000c07102c3d49004003c115101908410a803d003001e08040c00342c9035180c880800441c00d1150302e40000c090a1300394000384041d0042c5031800c10301c106a140c011454080e203500d4140460491200e01c0200d80c05044032100000c148925800000d400280799480d10540302c3c00d8080d9003005859030188030004107444138030302c0141e01019500e01840e12079400b45422902c12003030f903c22072020414104090b0041c090603101f80d41c0e07480040003004401c0012806907a042c407091b6003041d150070061029801c052007400c081851b00c400903410841c1d070640d1494106240e540c000064101002050702040e82d2070b0000709000c01407200801ea43c5004400c200c22281d00c41a01c42d0176500715a8110054407022442030b50264039298040344155154a5018410310b00d9108026150342c02e46541c0c1c80d007400f001c01c0010341d9140001a81e5040d050000034610b44c507001d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 876398992 1250 876397742 876397763
    0x1406070f03121d010e070605270d0b0604140115080405030705060f1008011413050a05010f0209040b040b030d050f12010e090f12040501140903030706090203060a18 72
    0x1070409a614116039000b2007540e40c80c02400c10101e041020718070f01c421441c1002000b001c2c20410455994052500400000c1602030090f03490980c900b0401c0c030b00f0124500102c0c400c803541c45000c0364800340041001c403030340d180b0a010001d80b4103142c0300d0b803500103621500010081d4505100d04101c246481c40490402920704002801d00a08104582c1c0c101d510000f140d8a5290103000b0f2505064143d50403611504442c0d40019540014001d001c1c4d96003d208420b80c003030701c0c1c400c00f014080d06500000c840d44d00884820002054003841640c13004054404017681d00d1004608210845001c8903199214602d444400c4030349480c0003c0c00703030044500b4203099513104440012001c29002e54030341000030f42c01800003ca1400840c1001074010a200c2080310040160032070078603141d140c80808040c94090601c0104055032096482c0100c1e25000900306180009250211341554081441651711980341e101c107508505007001001c1d40002041010022240440c90420024019402c043c0c044060f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 876400242 1250 876398992 876399023
    0x60b09151c0807050705101e0c0f14071703070804050105090d0c060c030809032704020403051002040314070e0a050c0c100906060512070b070309081213140607 70
    0x30240c422030300c0c6030440302c020b48500c0c881c0f61050f503941d80d81c0102402200c1c100300c0c40c40918060402141c0c1e40c038508110002c12801000d00319081080800c050b1071140b20241c00708081000c1c0040110070301e81d10ba000d806283d0409618a0480049020f10405913000700500004189070000342e40c1034030001d01e42550b90700b040900040c6440b500b10005031a0624607000004c4040c1c0040102c007041c0d07c640c44d50302c02c560b94015402d8403801102c58250190111458410b0104000c40e5084280310004000605203900ca8071440c0c60190000c000789543c2c5e80c00102401809050415401c400d01e1840c01800268103100d03044222510242c04c40456540b41c0020071072402c062419600c44088040890748824444800c40c00a4924100161009071400b503000c40c0d281003071004000c0305c86a840041072802e2502004803041d0348102403d50400105160105101002f07000507494103102c08241030711020403c207250915411a4802c0c2013500415440f041c194031410b058031500c1e900715003e140d80e00c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 876401492 1250 876400242 876400279
    0x70302070212010c03050a020f07060b0102031323040204081506040204050d0302010b011223040206120c03070f0216170c1306142403090a020604060804060b0915 71
    0x30880029400540450844121101584102c05803180790ba41845962604403001c0304a00c03c88400305540d200810a40707010480c01d4011001c07c00b418070441e443c0402110421b48066401c2d001031020202c5681000b1000c60f0052081500783e608903401c524203850070030780580d00c0d002d02c011510401c0400700018125503c65058500511018010b0342040c1d5542c0b41c024000c21004c10303036902142240700902c0c00c0f22040e10403181c1c5001c6658640c0d5540001404ac09080030006104070b038888002c01c544040c4840070960302d80189000b0b1000358503800c20500c054442d060444000046601413561882031411807400402141d0440700b90f040b019842c0c6a8180c01c1c2140143c20399000840340801c1c4a50041613404082102c5a4840e030541c4000780604104211802020781d044e01003503510303082e18100494000311740041c035260480d20704800d15800700f002030304598020400304803000204000d01281d0300a00c1500541124a00e5091400401c0116603002d0f0f40d208502604048500503200c08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 876402742 1250 876401492 876401497
    0xf1508040b150d0c24020601060518030102040314120c070e040f141011030603030406031515020d08090a03230c060c040302040c2a08040b12041110020312070302 71
    0x22405040300c1d01403c142e042c060314803107030713441560030311118500350b000d1142c1482400c0041c10185d074041c0c142c603441d0420440311500019400105058103005894a0796024802800210301c81c3d441400d681c0030754071115040898400002c04010001c00101c4030481001c07540c1000d88144406980e0141c07228100b03080300144504005191100611024085440010b03441081000b2a003050100e000c480041040030300060300d68a0b050750040c4024003400b4080d07008181e02002c2c0d80c2d141c00459035178400800c42e10342c85000c964056000204c0380c001d00341d40b0400c0c650b8060400d00043c01c3e41c18a5075402407082d0501034140800032800207103010480c01400440d50301c0c2005001b1034000c1c0c18804254201d03a0f00c284170480c45640750400c65180b4502418260660009026030404818032619200705a02400c80c1c0c00c90f00500c04120100c0c4100701940038012100d07600f18040d01070b14041c9040d0a51010300d65041d8132a0640c4040501e590394008121029003c04009101c0c4544070b03910f00790083d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 876403992 1250 876402742 876402781
    0xc0315061903050607090506030f060105180316030b1f0e0601031118090f09030306040b2404080d0f0507030e030a022101060603060b1b1207050d090519030b041b0f0f1508040b 77
    0x14090c41c0a030503001e5200244c03200c240c9004203114000ba40f0360360340300c1c00007a164a00211090f00c2c0c021040100c0c04e441c0c281681c0c084010b050204004903558944809a407045c0c0340c504800c21002c0300d001031410301d148800d603c0481c1002d40c3d003003820944c01840e568000103084500c0740392141210031854803040e0403d100000b1100d0341c06a8590035079181c00d89078100e4003480f2030502c07681165000103031280e0381e000c60143c6aa00c41c945810690b803000c907600d410781105290588941300c0f00a00684819071998040d400c00d1003401c90707501d08900103e00356000c5034000c208140c1070043c2800b90701740c031008580051801d40540344080300c0800040d4145401c19491855085c0c02044805c01d008001c075119800751039654441c1c103129164030400540c9007075910a401d03500500c40741480001c445200783c681040c0512412120f40020010072601d582842d0400800c00400d01030401c00c443c0d14000640c0948004080c0780c0312a80014070040000000030800341c5850f146001142030841e503078004500c0c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 876405242 1250 876403992 876403999
    0x904020f0409050d0c0b0f061c050312130212010e0706030e0f01061203080901051b1b0607020d0905010e06030a051018020405010e01020c0315061903050607090506030f06010518 78
    0x584105500c00380c803030140f2120071b849080c80c83c4005a8445030000006114180040c1a0110400600b01d03034522704c0c00848044035907200070032001d0110000d1411462094448140c0422001b01610601150702002c0703182c1d800580c142120400e60702c0c1d021a455090310301134903001401400c1c0d04045032521055901483c0340c3c0d4681040810b045001d490f00c41c1a41d40251184c02c100d45822240d1070889808940c1d0869803400188800c50303050f0303c400203214103450584c000d510900850f11040c102401900c50300c0140c0e02c0b0140032500940c0140090005110908100e0203101c034010124504d0301c001842080d140b0755920004400521550b0348801070403007080402c8254980c0c62428000794418000e180c049107900c2021643c42d03200180c4800840c4000d000f5202d12180d00042a695460240107a070f0302003080d280e581000a582840c03000110700800007480c10341403194000d0900c200940040b80a03c4d810410002c206243e0303103156410440070320301035a40d07480d02c0180901e00149d841d000381d407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 876406492 1250 876405242 876405253
    0xa0f02070b010e1b071719020c0103050a02040f15090e0406021206060a021906201905090a060c060624020d11100504021918050106020c0904020f040905 67
    0x207000c800d44203281a503418652848031500c81d161030600b82840c00740100303042503082002c4400a404a00821031213110840704a08042d1440b080817030103030311105030000503403107200e0341c030700b80c1da40b5010761504000c141c902103140900b001b0318421448010700607104071807030b4400743c50426031203120504002e00044450001c00d00b4149800c0703000c0d500a0040300c070000d00250102c0c20a280c00c904883c85416140c00401c0c10500c120130113140f40100320010b8594607524a82c4a0040300081c00c128052003da542c89580e039030001080610401004070034508008007032018040c070340c4031241c42c4020340d003080c1050040d10405203410300103864240c11000803960006218605205200800c601c3d004981d0250766040e1442401120552a69907001e02c4a0b4400c2c0701403400d0151035800395403c2800030b0402820b41219014040104149520050310301c055051141d042500754801c3e00d0142160f8406001c8003045000002c400040c0038002030300c00c01198455403c20390300d80d0300c23030304000d40e0080945c0c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 876407742 1250 876406492 876406507
    0x12240e091518010b01020d0f120e07060f08010f1a07050f0a0807060e062202012c01260103080f13080c040f02070c03081c0f1d1609050a0f02 62
    0x28072900740b4001c1040039824840c034408070b50f0010a011304000480d5036640d4400c1904c4504881c03004140c5a44002d003907075010385044880042c804c1c60083c06094036080420714031103100904803003059022400e10f21000c8400e0150990210114091241c070410702c0b61030f0200c40c103160741000103003940e41da187c0c40b481054030101302142002c1c00c9194004c1204020340407080360b4464403146c0480d11024034030505080c84940150a00ca14410a40103160515055402d607156000b10074000c44c06401702d030041a4100b84540e03102056551455001640610700b4040c100d01081018042c04010420700c804a400c61100c40c840055414040c1000c424101017991b40798090340755401c40c0629400f40d41015090210300c00c240c000c4a500a50180196211070300d1500c0380301540d040000c045280d000101c5ca82d4040c40018014040380310801c060024440b0036100000542c1c0c0c0191486c88019000100c116a07012070034088a812118054800301c1e02c1e40d214041d60006050664090003200d1000ca10789 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 876408992 1250 876407742 876407761
    0x3070b1909110901150c0212030903060c070c060f08040f03030b0910080d03021c0b03030f0c03210f16180807080705060c07060e0d020603010612240e0915 68
    0x601d940b85041d50b107009141d80b0b40b1941040884014001408a02403140c050300600301081c00c034401180303a20590381070503e810b00003070a154050310070741d68501012440e0814040e02c5004080288181c0c100440441320401c3d0180010f00028006010741c81d20780382c81c030103040c020703003100615240c02804294181b40402c41000541c00c18003901000d031084181400049010340700f101c8040006402d0020369030b81802800024008088065416010070710035100f041510328003500901c1d042c0c034080e40d1540104404044c281200300b0b427000c0c00140c036000784444400882c2080340c04c000b22a880d181c1c0907808580650740201c2045003144000c0e108040042c07800c001045c0102a00c0802e416105056070701e100b0400b26020315040b440700c1d0b4003c01e6081100c00d014a1092845480c041c10700880e082d01c0d500007a040c3d070001d9100ca00426602a0503100c961040d1060703d020307628850345c088508002440c1c0140011040c0109a124840031011441103034042215416254280d81d4041841c5400c0210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 876410242 1250 876408992 876409013
    0x13030b0901021206040c0903061a0901031410150504050402040b06130501170103020108160e15120703060f2d060f11010203011401030216020d0809150c03070b1909 72
    0xb0200055001d401301e0b100740f402d400394220043c0340b50f442a0301c1030b0441d15020700800712048210420301e030204015225031151303c0098000e5010790340c001016429101c009040c4082c00034840703846490284180c50821060072240306441042c0da0000c0c1e00e0b901c4d4408100101140800d00c1c0d40700e400820312403415110f4a0008050300c0007070340c80140400c10811982d49142c000c0c00002e001c120500f000843c002021000c1d82d00c690f496181528161002c80003250396036410048054100c4400160205040a103015413504100540750801002d0329040c18141c41c10520b00032010000d004401ca211803050004800d0001e05540c0aa00c080a980d40005800c0040084002d40803401d01030807203071110b6041c42500c1c101d81850380000500d24021004600035408500303021090850360310f145000d47c03103103425071a8491080b411a039031002840104404103400360800403001004201036010400003200383c40c200e0f9032000d40846c603602c54485119500d00807400f58940a0328059a800901007907100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 876411492 1250 876410242 876410257
    0x1c0b061c020c07080a0f022e020d140915090d02130e0c09070e04090804092d060b090907110a0302070501030f0506030a020d05121c0b0f130213030b090102 68
    0x103c0707509654a40300281c544100d00005030080c4050181a400350604102100d485c4015801149000980031601d4500c054050b04040c0180d00003060b2404454212010440380303c0c00b2a00c107810b101030000001e00385043c00d10095058900840c02d01900d807941043c0c44030f207a50061480000b660032052900c0100b000210f40f508510400030440b20341d05040f041580144e81990b40c07500c0704d56003181800003a20b054a400c43e000c02782040300203141000751040812002e20752100ca81c880300310070703416001c81e2080300d422041c15280c9441001030078080004c036050108190344442007903a54480c1900e02c1002002208840d001c2c0344880410540d0215102007522800d0724100070079060b24200e0b1044650480e21603030168000c12820000d45403003c404407203940315400300c1d24000c1c0744c030686a10940150304c42c908900d000030310240301224a4007420042482c1070f10708030a101c1490b1b00040c030200100e04150041c603030004403150404100c0d1040f102442e004a0b803902c10741024a1034a00030740c403401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 876412742 1250 876411492 876411517
    0xf020c12071e03122c06040308090c0d170f040b0d050709050603070c150c0f090504020708040608040804090204060e04200414010512010f06020d03021c0b061c02 71
    0x70070340b0340790780c0c08650a4803034a90143d40d0321003c9008801400d0003050f03600307072102c0100c0c00f640320303500304521040c0c02c00084003402014107a81c0c00c0c40d02d805040300501506184098000300d0618007192103000f501003106400020341031b2a03208411610506200310b500103040e2070300024021921260200080501040b080ea08121a5031520021141c440880c042d0f680d100d0010008100c901d40709011520800e4001d03c40106481e84560b400812140003d0010000c00c2078140c04045c1070307800240d0040107280940d4194500050796613101c0305c5204a0040c4000d00502201003000d002a51040d0f4015141d503034400c659641d107523a0040e02012000640358071031410070b0440185003035034801000b40310f21003180042c1014100620304540228400c025810410709004c5c030980d59a850380314a00070f00084212a12203800e01e20006d080088d444102000e0500402450f0301a0b040c40c1c102801c070715031144000170400740c0103002036818451582c7c80c1c00c104a40e8810396886401c0ba0380200310022450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 876413992 1250 876412742 876412763
    0x806280314060a1a090601033b0105090a0f03050f03010311040b060711060307050c1e1c09060e01030e01020a02010b030c0f0306010b070c03050303041b0509190f020c1207 75
    0x8506010643c2c030b0a24807680328610308000d0200c4ca0414036041c941000d014100031079440c680310040d144448000180d514200140c0070914020700c40c0c030010100c0c012100000340060b08e00a0300d1203a880c82c0d00b000090081c41d8824290042c1482203013039500141800e00d521fa600d503501c1c01c2444080d410600f040d4480c1c2e18020318080b0902e0800210f40007130342d00036094a00c0d410349004000d0240c1004040300b00380001003001d503400003014000c0604040001080300d00005803491030b49e00e005c10070b2042003840344030704500c0d12002e50400c000c003085401520b0724261403142840101c001c1d00741d100ca80ca0f295800840c040300004d406410001254405504640b46094040d08002d0607981c05105181c00d50404001840319a00d414020130f81d50340900b500c130240950766514203207541d10460b0b003034600c1056a1400309110001c030030346900500f021109107001c1d0270054100d1000090951070f2600d00c0340d130307040900d1a00c14590151920b40240c402070794402c00460405910541c44050102c0302c10817103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 876415242 1250 876413992 876414001
    0xf0307060c031a010c030e0312070605150409020619030f0626031e0f09100503010905011517040606030611091513030f050c030d0c050105090706080628031406 70
    0x2030a484501d0f0040581d0303268450096a1010b9419504040b102a01401960b00c50080010240000d2505603c2080300080e40d01d0524030200c01d00103401801d40c40b0b541071251000150b944c500645030388a202d1500c101c849504104180c0080c0342c0d000340410b400741041c0000440d484010800000909401e00d036044413680303401d5240d00e9100d00382905136100c14202c0100d00e6102484043d001c50f460705500030386000d54910028601118407222200002c100000512011055008807401403110b0000442c012204c018050001000441001c040c202c0810008040c4450354100034001c2d9000340040069030100340c1201041c2d80542d134854000c102904100b00403104500458010b4411000246121819980d80d001c5035030000409a480d442420320503039607030794188100ca0001d4550b840d10708000006242c4982580c0d001410421260410041000301c1e0b81c014540b542c1c0a10200d0361107050150b00f00e00c4004582004111040302c0d000c0c82d81c04400c001a0320591031072440c91104591a40d940e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 876416492 1250 876415242 876415271
    0x16060501150c021c0f02091824070f0c02120607110f070510050d020408031309020a0e010e0303040e043906051c0207031d1c11030f0307060c03 63
    0x451a0003034104525071010b842d9000080581c004141c417030a05004c0d03074a843d4001039000e480035161120302c81200754a000c087e41042001c0c2c044600c0051000c0c40136940d20001050b2018020242000d04c050a4070980c07550b48034261218850b64010f05030507038804003041d002d5031510f007129001c0118100c0e007144030380d41d100010094245920b000040001070b0410091081d2203c4611384103003408000c0c01401d401c2038980c00a40043c00a00f07005507140d15001500d2001c1c0c13841e5600c07001c24584100103107182e0b40d610a80100f00e003c020700380f000a60031030002007403640c8101e6000c0000d908008003800100228a40d82c141c043c0040080203000382040c00728020080c0030141c01e0341a80885c02d50400c02680200c0207000203044136040c00070841017290b6060180d901c1010101c0010b013105e0651241e4107812a12803901110a5030741d408038004541e03120b00750780101ca4024200c002080d00d290203e640810541c07240660040c2540d4036840c10781341c180054901354194101007401e10486000101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 876417742 1250 876416492 876416507
    0x180207020a03080903120403060c02070909030815130e0105040b1b030a0f020403020a12170405030a020103020c01180c080601090b0105160614090a03031a03031e1606050115 76
    0x6400900765584945103507580719039980f00f01c40fa25054090603131034079a440141c030003404c0198003130300012076040ba4000b402400c22943d90071514015217130856041c0402d50000c1e41c550b0100010100b045405e0031940000c0000c0c10707400613a420181001042011180190441401680700d10f007810125114101130588000c540300d91480c46203014400503100d5081a042100c0d07074a601c500040c43c00b0b48075000b045181c01d180e0000290300c12280400c00030021410407601643c1c0d4036038045c0e41050b0404000070307160581c002c0064109034020984400080e400c1d4080709401c00e944402034044120b900d401c461030340d03076803190348041e004407000000c4160660180850802c0140e40c0e1900d84044080f1001d01c6025480040d10456960036000040e402401c0d0068041c440d0300000300324109440c43c0060544024400484000301501d24030001c9440020603a020440043c0c084800b503440f680403c0c1c0c2c28003d0010480e0600307400b051a906000c01d5071f0020341a29101d1051083d800c058580585140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 876418992 1250 876417742 876417757
    0x180803190e06190507032a02031b1f030608010f0c090927080d1a040c09030b13150911091e04060b030c06190206061009030b07090518011802 62
    0x740100c20012004074800d070700170008144030b414160001109503445c045c89001898075054100500a02001945400c0000541c00f850100c0b100c40101c8008011500c40c07814a401103500c40c00c02944200303810301980100e0041d29a10000700030003161107914034042c08084002c400803c0100101007040151401041480f044104081085078205c400d070610b480c20780242910707469024000328440182c0c07070040c602d002c07030b0501260114084003002c000407601c0d558124018404881d41c02c100140c5400261a40040d901a00e008a80d02a040910080d04880c001d030300c4041c81c01c8501d004100004141c12220352003a0340c010880c1c1d03110300c0c400078018020301d8013034510b00203d000a8002105600f0803440d100e8040c0c180e82c088240000850340b031f90070498201d100d0495441040c041c103541000300e1540300c07000300d5084095540380715002d4204211400054400040400000c205c107019440d01c0c00103041c080c1c10110301c102408011000c800b020b01521860004682030649a25114020343c0c40c1d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 876420242 1250 876418992 876419017
    0xd050306090c0405090901060f0b07110d051c080a0f060501050d0f0b040f0615020102190309060902150307030b010513050d0c1a0d0e060f0106180803190e06 69
    0x21030310380c10100544404014407000d809a801c0001003016214644054007440f9150004a50b00d814940c460351280c0840c0c2010840807001e1000f44c010609030703650004503003020b4400601d04000c0d801c2c01410704c80c1c0d141b40042815010340840054560000000e0b10840440340d04101c2c0b500c0b04203100c402d44000b84100b0340080d10922403403110203126030100022031003410b00000e00c4c6002c01d0103d016643d0a40c1c0f100043d540d101020000c2c14016101d42611407005c2c4000c41c0b40890350452940030748000c60074542090781c0c401c0000d00308083e030703071116041c103800400c8107041400d004000740c00c50b031003140c00701c1c0046e061081c0f12001394082d2003a503614849144500074214241402d10a14201445003035580303413481c0500203030000d192551862554914844283e03910300001441d01511503104801080e0b502c8041003109201a048040703040d500c03245071000c2442030b240d000340d41c441c0943d0042e072a40c0c003000800010b00d0001c03140b040b04c2040213440d141c41032208070f01041900c0c041c00100328013 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 876421492 1250 876420242 876420247
    0xd0506040b130b06010f0c120e0312030f07080a020d1802010f0201090305030a1512050a020a0e1302040c05090411041406040302030703060c0504030503070326312a06020d05 76
    0x11150301074800045511541d05c0c108070702c200c40c8d440380c21210b2008500d007400300c1c011043d000b040c0c0c00e0038802d041018000c080041d1460625512512103100e004012008000500011601807a2680c040322501e82c1c1c041001d200945c01c6510004072000b00a0040307002c5541c0e101c02a0001e401801502421a0980c85850540e503e511050020740345400000207060142e0b00301060078098440d4107403246008500520b6900c00c81d10600030114005d4014101600d1400c04001c24400c0314155448015810790b00840c2d42903401006a0755401018002c4d40d006080c68141440840d124018004503480003030210142c0384080c0a025940c8036a01001c2e405070070901081c000325100f6080b9800390846403421500e82036076602c036203056800200b0200d0004514840c0c030004c0c5071904d40c420400300faa5685049050504c03054040b24206481c13034410300c00382e1035403000f10880710300c489081006400c03450309002c1c41c08680d020119207420107040c03511400e0815002c5a01840012807104d40d104d40c0d1101c61 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 876422742 1250 876421492 876421501
    0x15080a0501231903140c01080c0310090c0536010327020a05090a050405011415011d190509070c120e150f1c18150b0d0506040b130b 58
    0x3c028103031214079405804502c01c0000024000f81404154562000098014200c10300001030200402814842d441c02040c41030200c200b041090070741c2141e0444000161200501c3d0007503902d0300034001154407006180540d01140340084582e21100300b2030542e445203042920005404031640504081054454880110400360181e1b0000300b1550004103504101c0b170361040010006601140e109208036260b5090000b0000709014410003611003602d031031813900d0801041c5400d90701500e26541008069844407007400d0350324000c0c00c026540a00464880d100c0030307004140300d9002d031288a028081e402d001030321061240d403d592a20354481c0c1002000c401147d0102d0315a50380009032584656038144010381c40001400420b4110b00c0c0d1440c050b00c50002c1c0e80511641403454401100f00b5013080710f104039840e5041944402d4941c400d150100f40f48030115a4001400c004201e50342141001c1d0240e41440780016286200e640301c1c458078541580c0303e03080c07000c400d455030b540104001228000306 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 876423992 1250 876422742 876422749
    0xc032405220504140105010501080402010c061a0a0f06120218061c051e0601020c0105030a180507080106180e070501030c030f0f0e0705090c040603050403020715080a050123 76
    0x103004000e0182120040c1022464040102c401c2550200d90020b400110415805800e0081d54014003090070105640e14054002820784201d240f03009080556451350b56081c0c0703900d0600065580d034003600c1c0014013a110260080c04402c00d0080001051800f84034a45d600000d00844801e40d4015980c0c50780d01901b5400c0c8407003904036002461a01c103613407205e985040b00300e1041500c210a00401640101c03900000001e03004405042641190042d1000d4422a40c1140072240c004e04003490014003124880c0c08441e084000b45030040a60044650004840f501500090140c4030800e80c0562521445c00d10b680c2202c9401f45560038907000a5402c10081d0301950007008040c0807800c0220702103802d12301030821501c5188078480070a690700302014034002e00704590005088140c0f13410301c1e6411f006401100d280120320881c0c0c10191100e0018003014401d01c2120000e0010992034811952002c5000d01011000ca03441ca0707010381341c40d000144441511024104004420f103d0001d490100004d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 876425242 1250 876423992 876424009
    0x2190c03050f0d2012040809220f0e0d020c010e04020715060906090905070317070b0106020102030609060a120303090c080d081e062b150c032405 64
    0xd4003802010321042d0307591600c4030010842103100d4140000c400510030070703540a030750f034090000d010700509015401600d40c2205039107400a4100840c6c940f00c2c03503603400081001800044801a00303403000031a842140031504911030000d5003001c1400a0400412201c1c1d4402207800c000380160700c4070f40081500d50050820408640001e00f025180184a440e1880442d0b040088030b144590345850400c1001020300c5054040c1c5002e990174025401c050300d84036550707a003c0c00058000c10607002005001c20000b0700300c0e000d02d684282e50480c1076941c0c0001a00039002121458099100000000e03090314094000405803221a000b481c182244c9171030490050042c28400c80e01204014004145540b0800c65a400d110041d52010f405140201300041100403403104242c03910051001d0101960b520602c0700c2d0b44186030184100500d1001c2c0c1c2c541940f04407001e000c5c2692082224205410b08540c0140c0f6070540031751820b102d5413000a000050f9403000001c2041031901e10201482a864182c01d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 876426492 1250 876425242 876425267
    0x30e0d0f0813110d0f050d090b07061d0607050d0b0612012d140a1205060c160c060906020f0604120e010e09010b0a110a050705060313140d120219 64
    0x1d01d000d039800b4a03c0460500740240c501a00c9070000744a440c000c100c2e0030400c0000c4581d4a1a12202c03503440c14840c680c80340640c000082c603440d280d034141280d0702181040d0342001031014080300c055050404000e0066400315410202440c1040140d0310719060010450b0001444c1c00058110342c3e181403c92203109041090300c07400c5400c8944000c3c1d0080218140c403000d40b03d4a4108071034000f0390b40c200a0006101e600c00803003011019980408600041041a8440b0310b5203061a42d0301083d000c804a260885400140171004100d80402e9156010b9000c42c00c2c2c1e02150200c0300a0702c1151030706603481100300c034010710032442440c8512031188a01c140084010040c10300800c02002c00b00011b2070548243c004d02240034020861520696100c1c0182240888000c003a000984140d2a1581c566400e40262406007000001258101a00d0452112460b811000342e40f04016500507040c3c40e18140100d160018403a0300107011203512a10840d00800803d44080280031880f0400b47d540201002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 876427742 1250 876426492 876426503
    0x1605031b0d0b07020601170109020d0f170d09030e031902041112091605241b01050f040b07050918060a081b01031803080420030d030e0d0f0813 63
    0x20200740011a4202403034020821500034058a60400701c0722456603080c0103503a1300da60306094a69000d41c44100e000c410031a00500c0c18041c2c07040c01e0510117892000249844600d000010395001060100e51212180d10b2280d0b0f10049843c15940030940c1d40c1f10500482041c00500710249001458a030f1b00454000c05285005d0b070604480d4241212295811241c140c0c0d00e0b04102a04c0444524807460f01d000703000221007400000310301404403d600e001c2010401a100000100581e842c1d0f032400a51000703001e0113009100b40d02d044002d030f042c400d00a540c1181d803500c940e804240a107004200f507580c0218050298410180d43c1c83c405013040030060481078100c2d541c0c4d00302041001040c0222001841d01d0020902040c81c203200040c126403020107000100c012180d11a4000f95210612540207500803e11a0401c5d0384c400c2c0c030a07000b4407035580481c3d0520902c100380902030f13010380143d1020f10166094607035841030824151035a1089000d941c001030b8200c80010b2203094a0010068102e01a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 876428992 1250 876427742 876427759
    0x1a04110310060f120b010303110313090b010305010905161b050a050d020d05070b01120c09020c011e0b0114163314070c031704060203091605031b 64
    0x51010078140021000c495280300d031910b1081c08122400001c44008250b500204030042126072652201030700103000040070099901500c0030001e100b0020341c0d50148502c0c21080226039900e0020000345014045240403d00340b0000050040c5036200c0c451040004d9001e07010324a01403581102d00c103200c0b1090061901da01c044080125500308200c00700b040c403441c000d040846900d8070103032601ca43c0042140c00c07c0380800c4420006002c1c4441a03044410a40140f9416000c0c0e10f0f06040c3c0103140d4201b10038151000c24800345a5030150003410035000d03134140900510020121310403d171986101100d002c01c3d0088034260102d16107000a1103042d4440800903021f1125945041d00ea00012001301582c9000d1105032107a42d0443c403d024901d815401c08000d03100384901d078605001001801c05052101c0c0030071490a15009406500d21f0315040038001c9807501c0c051a20a009400c240d54001c3c285c42200314511188004000c88425900c00038001d001c0030f482d1751004219241400c080395040b0400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 876430242 1250 876428992 876429023
    0x501060e0a0602032b0e1e0a1511090d1101030b030114070e0a031707021e090417070816050c12060c0304110409030305060f010e0a0302041a06030408040815041a04 72
    0x1481002d0b01c006c800009090007040555201059070302c0030140c4009070f00805040030004007214445450000322010100781110045ca00200d00e010380c000030380e00000c00300c0401c0b042100d0903050072442c2d2400d80302003200d00002c40074507080781e050074150141110344c0c84c0410041402a1004511000020301e681c070030549036036450750084c42e034000d44807850f42c01040d441c0441c680b040503075000030a03494800048900d50000104145809400500f854a008148034594030310305044030001a04644e00c10780d500340540110b02d070f01010020a454a0044148154041c905980812010040c42e07005011a8603075031000b01d031960001c3c0080b14238461050f00040c064a070750240718802c034001c0c0c80000386440c01500380650701c010600110304004a10104520725520802803c2c150713901954006418004102000c0304074000d0303032110b580000040100001c111651008000f45d0750403070700344c600c102c0401c451604220030542c0d00070038607000e40342020765001c1020f10155206010341c0720b11100c90360 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 876431492 1250 876430242 876430327
    0x1b111005220305040905420409050601051003060b04061b06140403031505060f0f210106090f1a07050a081809010b030105210a0b0a0501060e0a060203 66
    0x70020001c901052000c2000c1204094078403c4030380c03100c07001a0703440c00e02941c001500f2154495120740c820300038842401010300000d03030100204d440c0025000f008010030505280781c0e9080c0900c92a4030900e0364880c49815107103c0c1c0248421126042405410542811000e89402e001c1c2003050101c00308510f51107011520781d014040c0d029050fa144082c0c10304082c14000d0a4030940c80d104468000400780801181e25043c044440b0f40c83c0c040a0681c40c0c29a680603000e09110f180e088051075114202c20300c81800036101414129021a01c90007442036070b270400e81c0300d40c41443c0b286808001c0580118a10011240c00408509200c0e005480f240d880e60340d180711071500f00c141c400c03502c05540c00b8a1140e0f4184404901d000d03140316100d40707041d0341c5801d00060f6143d0802101e14400031a2194810f0121400c101c01000300f80d000303020608901d008080240240807d02c41c034400640881500c04881c100180c0c00e40c00d0301c03d140d0186140c03018503260803c21032602440a80d803100c401e928181d9040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 876432742 1250 876431492 876431551
    0xf1410060303030f230105010f1112030601390302010e07090b040c030e0a06020702030a0b0108010f0f1505151201080a02030706050414040b06070609061b111005 71
    0x510a031400126404e110030500300715005480e168240e16002580200745001211045046980918180c0040700c0c4201c0e00b205c41991003440742e1603d100d8040d03801502004640618171071a0280d072007000000e1141200300c40c1090f500071011064104690440844605000c3c0030000d81c0280008507140051100a600d0701405901141505d50b46e007031003540519050007075580108840c13500744011804030041076241d40194200408061380042d040c011510300b8800d0304056508045d80e02034940c0c0d6900018040d0440a0080d076140746030030200104000d503486007407405149001700303009517030900d8207102d0100741d080709040d036094040c0104501d00c1070f4482428042c081e500c028045414003881450f00d04542c540000c030500c1303000d0000b0301022000c0030040c618004100d41c00f0801702c0d00d03940818403d1003007550103003505080c01c22007400e04c00c580e0400071240c611100c00030000600600121003004804000d40a2a000039481d0950200d5582000750000c884480715600b81c4010842110b001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 876433992 1250 876432742 876432749
    0x20103470d0605041101110c13091a0a052401141e070c081f0c050909010617060102030301050d03120624021203130f05010b061c11070f141006 63
    0x43d140d508004c1000200340c2e400391660801c0c02c081005a03240350302c00d5164040d5403821400b41c4040104070181150321f81100c21119041501c04400283c03006000b00e465008850030500306050030017107000d500c850388400c01c21130702403c0b20b28140151180115600358801040c12030f07282d030520528500034000303c52299146800780145a45803003600c1d000c00e0360841036002031002c0e0010003e411421004506000c0440b145a200145040200c0f40940d035a0241e100300c03030f070484000707070004c1045034024034204001c204041c44084076075940001281e0300d20090049580040c40190400c0009004e5140114581080c844c04125140c48010008011304007004520303d140c02c1000510f00d058040c0200d42d1036155101000b0321750720740f480780c002c840c00054100a00300c9100200303c006000c0203512000703c40300001c26950395a101c00380660154900003010210081c5420242100c084031082100e840300e070b01600d41c480300c0125413948504124503030007400d050f015000652a2001c4144a102c014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 876435242 1250 876433992 876434003
    0x7181406160b09030403050c12071e150302090f040504050c060904060e09030a09060201140606071b15020d020a0f060207081c0f06050f13110403170304020103470d 72
    0x841d1b140d402c010307150400e221030b2140210814981c04d0f5100e1404119401900d5144642001e4455000c04d51001100c040d0b0202003410341410840a14a516400800c61a1011200345190118440411048801c180d40c002e18070361200c800c6405904240c409040000001840058440d90324005072800d00d8084503c0d403450741000410007101074026100d400940540e10080051441060340201030140141100e4031450021031035604011401c203441243c1080c4000c840850346d0b40701007040d0340009400701c0070094010020703c01a810320000c2c0d458556a00a0a0303581102616100c17900294010042600e007503800b040b1a540260444415100724850340c0380004022a044107c0d03c21111560002e900c20408007414175440d80c2c1d0030304003000ca4201003000049000c00c880740741c2c243d4441c1e503000078114800248010141c401610107076110344d000f81c809100007000c10f6022035500f241140b030603035484221507403410801c1c00360800e103150005c0701d8245828603403594000f410f4201042822601c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 876436492 1250 876435242 876435247
    0xc1009031b09060806010b0f0306040b031e061e0a020903010209060301030317060d030509010e0307080a03090305010b09010812160b16030f020c0709090809060c0607181406160b0903 80
    0x402c02d449058018018113024020079410190400c1441c8030b5009882100070010000c50907503500c03a8800c400c01c880c010111001081816603103400301048099401180c05a100002c908000071a038510381582c540300e4a1086a507007a5000380250480030b2019010b40d03091043c15805d031075043c02940a980291900301903446407224030340310054000c040f203003d89070404e40400040d8016094032280f0b142401e2540400380402c000c2468125198040b6825108110b004014160454990b000352030251009000d5608038800380060507500303200310314950b8030030f100c1d0071013000b07455010340080c184088018001d45015190102d000d5001d943d150507809044201114580d00352207076401c851185a400e6003842078403d41140c440056118048080d80c44100d5007082241d030608841c030b003034001840c0781e44541c10000e489944140440c0c011000c20220742952143c076000179403840031a01d0140d800384501e40f100301030019641201c0000b0409040320140c03034000440c0e04502074402c2501c03000464 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 876437742 1250 876436492 876436499
    0xc22060e0a06080d0e040902041514040b030a03081308040810020a020c3a02030d0e0a08060c0a0e0d06060303030e0d110d110a0b04030c030e03030c0c1009031b 70
    0x41c102e4400d58010740542c1e01c40c081c20000075400142c00b52074801d08039800196090745d400804c001e032200f034411109030200f124001c900f40c00c24240580c1e1401c0296020890b650300b91051554907810000090b0100d203503100004d04071242840d42c60803181c171442c44a8209940c61070a145050849001031072116004680c07030410030b90420403a001c41c81c0840709000701e180402000759505c0110621150184902c9003a82811540d1042260035183d001c1c007181d01681d50000300801300502041410301c10340c5204800640a400060b000c3d000354401c88461b4a003006050041d1b40f40410350000d00e0304040441c407802d02184075403003980011400b940340030404415806003642005c3d0694500000c1c01032800c2801c05020f40081c1d40341d10f042135810040c10500e641d58050b071800c2151030f401400700e00c3c0e100410081517804014100c005219480c0e0074181440c07001015200d00510011920329840400c0c0210345241864014660301c415040c20004c550b102e03160001e0f800030b425030b2001c07141c0790201e040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 876438848 1106 876437742 876437761
    0x3020a0f051e0f0909071d0409030c020d03020127050a12030902090a020405090c0c1c0908030406030e060a020c07120602120411210c22060e 62
    0x40d03100e03043d00503010590783c4501c2000e030240400c0c030701107810039028007420b80381d00c0f08003070300e04100021040038000108508503054080040000c00301000d80c4448400070340d100c2c0640e0002c594501d81e40504101d10600c1c003200b02138000d2400b0480d0200f440851a019159800800c440c0d80c2061f0301c01c103c002d000ad05070041c1d40440b00c5414013910040079801001154070540c3c2e0034000350749410308600e450150510501082e004140c10340311000d9061940421b24540e410300c0110aa1a0790105246402503040034022a682c0c03140c00456242c00c02245a10001500c2d00f98686006d100740c09468441c5441800311898401d200d0a040140d01c0d0180c40d600c2c5051815840b0901d800c0c05c1840c40c8600f43d00740c150042800c4c11203000105c000401a105095000c40109240c40c10041445480d5005540d0030300c041d4101070482c0420951401a903004042030b04041c080c2d4240941e15 = true := by decide +kernel

theorem cover : BRFrame.Cov 876258992 876438848 := by
  have h0 := BRFrame.cov_init 876258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 876258992 ≤ n) (h2 : n < 876438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
