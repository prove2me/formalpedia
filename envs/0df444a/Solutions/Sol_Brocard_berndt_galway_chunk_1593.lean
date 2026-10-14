-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1593
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:45:25.163195+00:00
-- url     : https://prove2.me/submissions/01ae4f45-bf5d-4e41-bce6-0b12e1bf6203

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 286330935 ≤ n < 286510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 286332185 1250 286330935 286330939
    0xd1b02030c1f030509120706020d060e0123100912050109050709020403061103042d0804030819090608160e1f12151505480d030e030d020c030d0f051302 67
    0x71401d410340c000b500201d0040c10031010433407036541c4640010a04c00596603003030a150b2014249241075142900704090f58049640300c1c1c00390507007062011a00540010700564584d907e40d4860310000b2020040000240a5240010b03140e604502c0c1101c00c1d03603001510a2842c0d80d0500921011400030007074a000c4204140d040c1d90301034541044003801078000100640002d0010400000780038280f0002d029040480020442d49224500296140042030040900196209000616410598032112911409400e28000c0c1d40d0858000588048ac00e2240c94030440c030f0241076108071508080e0089400c0782c2050103100b01a8018000c010740c2103244182c0003151160100300302e4003800340342141d05230b002d4603211100b844c032154030540741e04c010a28100085081d20100707406007420b400e112031b03080b070114001d0440b104d6440700c120f004d04000210207805000030082075003012458402000b05140600c043d584038040b00309a4004c590040d810304004508040402c1550042543c0801e091581 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 286333435 1250 286332185 286332187
    0x140705031b09061504030605010905010905160302030603070e010308041e1206020703260402090a0b130203060a080d080702010f1802010c030e0d06050115020d1b02030c1f03050912070602 82
    0x5183c00105003452601000c03161660008000c01488910303000a81030303402100c402d009590b6501880d80407154201c9440c0032440350a507882c00e00074442d030000e54100a00500f1110314070740ba102c004966403008c2c2d0003100e0000c000a02040300700e440207090454103000c805c010b60074034500402c15890341421200181050b900249202c1010b0140900c6004800840c4c1f01d032100e40c0c524a003080b0305130b20950307042c1c1c407800300c07500041c00301c640750300034482500b2000e848628106407011424000c0e4101616483c1d00c01c403200340119030700b04104903034000e074800b03540c5030302c514108204003908580411400c00000390034502072501420b40380701ca00355410349c2841c001c8030210803030070708032403202c0440d0410b64000d03400302086040c0000e581086058601d2100c80004000382503409a070b41d48c26160010012540b140c0c01e6041c030508100096a6a07400076056034514442c0314002202c0c01302c01100d01c03029550282204489a078184111a4040c0f100710061504070b0324070403c044580507155000b02400e030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 286334685 1250 286333435 286333441
    0x105010302040f0219050d09201e010c080d0204080102030c03040606080a1101110c03030415090b0a08010e0702010b06070812070c0b160203161101080703230702011503140705031b09 80
    0x1581d44102340c00380e00301042401528500c0605a0061a12101c0078426404c0d80c3e0700720201075a490113560a240141c4900a12074840e40c0c030552079800c109000d852203075083c013000482c140207000461086d054a4240341e540e240c03501c0e2202c2194050f4002440c40da0200c081d2000280203034241c400d0381c010074244000c14a000710f03089498507814400e0709030940004140001d28580f0122000251b002c42c1d1220324045443c0e0344504400d00541d2032190000c1d90b044010411101705490780c40c0c1150307807032002080c4910100e0108130035500c03802d001c44e8051000101c11203c41860500503420600311324209070101201c0d2264010031034003400380d04d031510041542c0c0c06114020401c603541030592000d41440b03d645800d10320901d4107802900f0f404036684400080c1c44c54480e10554071501034101c80d14104000c081012815994010009415507607a0300c410950b00b2035201e000c10045101d016284980d204a65540e4109502580118003d5005000c2c5520b101d03d404c0034005500c80c00d07500000da0307035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 286335935 1250 286334685 286334707
    0x106050304060b0406290c0303040303270b01030b0f16030507170901020403120801030c031e0b1006020106062a11130c03050105010f1b080c010c020105010302040f021905 75
    0x3c8941004154004e00e070071400240713080441044012524032070102c031845000ca0510703081512030b0983d0b02603a41c00400000f40040d02944c408002d40096200a450007040c0d1a6807910b01030504000ba01ca41c10b0540041040011a202140d48104210303107a2699080441039a80c1c3c917940410084103140c4c5a00005007100c0c0b10340d07840c3d181d14942c001c142103141040d00e603980c000c0d44035000a481e4000044c0b00956101d015100060480b80d1080c8011903151842e100c0900f15110748400f07080d0010b2840085020800c42200e850140380182c060591b850310f80640a400c481031075001800740142d0705903403100300e5038901c4021480c101500030b01c0b1141c0c4092274085031300e80000c810aa84040c05028130f1244030900d6200003140c06003030b04c0802044e41c0740d10055502403591802440000c08441c8071802200c41244107600541c46044104d081401d50100142521000840710005030b55810040013545802d01030301ea144540d5001c11403070028007c003c403042c504503445030340500c8000a006c01071a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 286337185 1250 286335935 286335941
    0x503060f1b12040b15090a020d18030509030d02060606090f12060f01150203040e1611010608010c03110f03060d0813060804030806041103010611030c01060329010509010605030406 79
    0x2805103100540da6200c07000321402e558401d0b5025078048501e94000780003265100c0743c801983d400203245035040d0b6900c0f155800a5400480703000c800903102c0005071078000305040744d03041a602c0f98545d540c03900c1c507500074546440e50b0412000c1c00c56004000f0b100140e101c80e0105c4660f82d100796600400c80d902c05011640e0504d03c8200140a4411131301040340e000c06003c10716040e00c07648000b40b00e107800e0b815001c903620301480c080c00041d002e6000c081801e0007042400c5604400250a045881045140c511070850303502e42c0c481d5140d81d441c0d01a40107007517450300c101040b0120000b0703094104000c1e07080b400017601008104500580115001c1c6060200d0002550510303615191a00700064072444002d003110401d07203044010659a50200d44240341a018000309041004034003419a0301e444400c81d6844203503030282d51280010894001115000e0080b24013070740c045c624081001511513181000100c2e4807925103005000e2000502041e1346102c0061704407585444e1407512038842c1d091600c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 286338435 1250 286337185 286337221
    0x20607080a051b0c060d0e010b100908070807180203060a030803040f060501060e01020604061805010e0f0c030a0312110d021201090b06091c03030e030301091e02040503060f 76
    0x1900300401c070310100301d5110008003428034107403480c442104449800503548065880b070181d80300f4004c1c003020740b00361540da10030017001183e880041480ea800300e0102e55003d030410b4041c0c000424141c1d0502185504204102c0106140d40040001038030780387c83c040700030030125115825103030004007107034a90b940d88400b100615048500640d8905061601070f107007055101d402c407001810080005080b0b030203007804aa042074103801800480d5250703a200001010f4100c81010004200c04140010407002d00c1007841c0d0040303841c020301440f10040c0710380780f810f41c0c185441031080d40503a60001c002035001940a81e500318003d000302e51003d0130041c0e00d00394021100b02c90202c500c08680170030b95020f0010b01d14100d44401030100f0151440714103020040c41102d568070b41140b140c200b1070900040058981002c94020f18002403c560864045825070f8820b80c458108103480712030f4078001c6100d1503600355088105031000c600d058500700109890b0a0000c0c14000c10303c1c0400c0c0056070382042c01c0c4880d01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 286339685 1250 286338435 286338443
    0x601030212030903060c0703030c030b0904060e010627181a192430051002160b010510090501050307030f050712050a05040f0b09071d0702060907050913020607 70
    0x200c61800180404250700002808d50000e8180300f904040c60340070384544040703007401a02b070004070307a156260741001e0442128070326890b66854030002040c6100d02042d00503100c101e00c3c4100314546920304c1d0020303686032002d581c000304400707075821000801400c600040d41c0f02c01d000c080c9031550b0f054034411410019484204400381000d5080c8600300840c3d400441051140e11041102a00c6012055214425211000341d0081c0302d048402009518440b01c0c0c0094410310487e450b00a800e18103605a030024810068086d105900a600308110344580da405048191032071402c0030700d1000c00800000381071003120705102000011441c1d5178032a07044000c035000b5071442404070b4103106c0d9006111100d040030303002e0400d280c840405c21001c600d004590041d44c1251001d4a4440c4948034812521000b0f80026003030b10965a000030f04018000340e2030b61074881c50b20410024500030303030040e09004e4010a03420080d04a28400c4c0429990b20213180d0b00f185522821004442241c400700381c080c42017410141c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 286340935 1250 286339685 286339693
    0x1060803220f030c170d022104050a030506010501120e0a170705161802040503030405010537030e03030402010c080a0212041202151804090f140c0405090f0601030212030903 76
    0x100038840c0c69034035032048034036405170080c030848000282e82d00c0741000d41130400160060000c49200a100401200c036410329000082d10740341d0b480001034400300e041d6000700e50325005640101720340e68220b40854000c091261043c040c4207014044c1075180c50207204003c10101c100c61036140001c623800705488205900408036458a452800540f41e15200c500ca01c1c0800301e50340317421200c00b415174029101141d4002d001942000c4c102001542d45c2d8018101103000000000d0b054170a412248a0b64800c0300c4454010400c2e013583c1002c02000e45e1003400451003103a004105000050764000700110b03c0031b0b00315030640e0300c40642141c00c80c1015210010002041000b00d80420080c150300002950280b00b181c0721a4201130940e0071144a003d5002180308403820160100850f0800c3d400204086114010004d81d101c1c00e5074400e8044130211404030441d070301080482140f4240f511841e508941c10304024217403103803200c07040d55455105000090069029000c0100ca261003042030700c0f0b0b120070040c03c1d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 286342185 1250 286340935 286340939
    0x309091a0307050f0603010e070c1703010f0608040510110f13140a0602100e030717030f0903130b07060209100c061515030e070305060a140901060803220f 68
    0x40d4030590085803028480e00803890002042e161241e03011094410180c18103086a2070b011061001540040c058000e201100b801e1100080d06802110800010002d1094aa50400e484106887c01d1030b0022004c0c08042028803021540005681000c0170103c80c01245040e000d18501482c3c0c040c4944200d0110000719940650000c1003403010145c90806010315000035001c001c101c5a1607041c801e0b02d0150b0041a107615600b4165085031500c40c05e440c046038640300d043c2c4d0300c03601c5100b040780050400450100600540301e0000c408150040d100b031000b503041100601d16880c4035841445204200c400000f241740402080b90140c920340c1c0e00040071001014136061028103407a0030010700300c810f00c0c41c00c80c59034103046030f1009a8040c1c54500c8110304444c99801800e034000c10800c81d04441078802d114000002603010040244205045ca0020030b50210780d040b005111840900000c40705d90403c6018001d0740d4001044c0c8030b0f01d0350116041106a4203e201110980002d9000000c0003401ca80c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 286343435 1250 286342185 286342211
    0x42d17180409240903021011031605040e100905060109060203091306150c0b13030806010e120106060e030c04091208100b0c151e07050c0708010e01320c07030909 71
    0x105122135402a003d1311004d201400101084a42c00485140458001d0001c100440b804503100103c0e4034840c02e00924103501c03606141800d4100f1101c40406540705c2400340508001c502135181c004800382012004130f814124041c0d22030003101a03083c0112160076810050003400e800401c01802c260407640004072503450014201503e44100343c8030800c106012860714400c0d102c120f510b4603016131b10021140c540100444100310304c0c0200e0340d0f2003a10000c440304544800e03c40e810060400c0c0c0c4503580c484680c4000c5c5410031005000ca644124640034600c40271900e1000c50f8a518040ca1501c0003407980c4a00000c001040316810195081c017010410444048000811520712020b01c455000c0c0f5549004023000c1c05004400c82161441d6200c0110f44c2240c0640050001c1c0e82714170301581c1000b515a41e0881c01c44500c83e0aa041c131341e454071080740e10006001c1200ca412003441d4030352541c18403940c19841c955040500b150060610018106007072510030349851002e0190b201c410f001103c00346803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 286344685 1250 286343435 286343441
    0x5040303050f040f020904030e0909070302120f030d0f02070b0a0b1c030f030b01020c031b12030f04061436030f0d08042d1718040924 59
    0x404802180c6001c0c003162091500c911414811a070100a041da81c026940c02d020000030042c00840901508481071500340d40d824449506c00c0300c0e02d01c0200046403640c010850121845100f401c0280c000c83d0041540410100c00c445001240c503501045000b036508105c4004e21400c40f015218003207807001d02005044036088426005000c54640180281c0034102c0200702c080c581c4004e000c02c001120100c1468041d400110101105005494001d045400070070305040003d03001d620025a00a40c0000741e140040b0001a051401001076051a000310100320003072055001d01c0b02400501500300e44018519011102d10122341445041c88040c00369100b40035801c248000f505686500a8a200e02d003000241008400e03414001040c0e003421444054034842d0303000c0c02c190b032010300206c030251140381101045180c0a036070408980c8060140d080c027008182280d03c0b9000e00d080100050300c688a60100401d10519088600041c0b50b1030a1428049041e1803061200c400581c40f0f440c8d02c0c0070030840e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 286345935 1250 286344685 286344691
    0x30b130609121805010f0c03030906050c1e071e15060b0910110c01050c03070b0c0304020316080a06110c01050412180506030a0b0102030d050a02040312050c07030b07030204170105 79
    0x1440f0505010140c03600422401c680e801203d00280043e0030020f00a4828904006264020304001448952644400c000d4490898520f4000d03480015041e206d9007000381c0004100e07114003261810044266540c0d00c001950030f0715036540c080c1018400b401c1c407015441598031002048070402100366111210030700764000c208490303c20461a8983d442441c003c4900c1c8a40b44400c001404c2400b000600644194012081d0022584010320525000071a544240da0040c1200c48203982c480c03400344101483c00390710905291414462110070002c00000150111443d540140003040c2c0c064070090072116400b880c15002120360804080c441402003d00781195140c06955031241c4c40e403601c19a45031460035a105590700002c0410004610702010352201007484414810f5a01e0080c88514007001e80d00c0a80f108120306500290400410440754140c007800e03d154144241041c00b94844103071141d45c14880503100c81080b13000510420b00c29070480d009004800b200c00b90344008540101d009203021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 286347185 1250 286345935 286345937
    0x120d02070303110105041502030a0603020a0306140c160b0612011a040f060b0d3206030c041e0509071d04050601050901050a140118090902030c040b0307030b13060912 73
    0x200f6948031551018041e062140703800c00c40404070b464003045442d000f50720043c091078203941d441201100513524500300308011800759034085403010401d42000150640075098030b42200040148a000c1c2000320904a11185c1006211525035a110081429000400c2c002a129441c0039585c0d0a11a0781e07400c0001418000d540411104034964003040c222811402241c1800c4824448180d40f40c52903086450721140c1c408010030300d0380c001d04898001541e241c610503082a860307010801141003c102241d4100412a4244401c1000302c000114643c42c501d0b0b50400c00c0c1c2c41c2e000190303100b101040010300808a0381c001c825203003030005400ca46000e0a940807105070086000000e51490012503480c10703610000e1090851501c4d181d03012188020f4483c5050502c0a50050448030b0300080000f07000031304510f43c0105100304d062040500705404601c58501c035a144c00000e841d00c0d2800102c48043e0f1380d000d445020641c5440e0608590803c01d03010041426080a010f003041100a040e070701348207001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 286348435 1250 286347185 286347197
    0x3010b030a0c0e301e12090607020d2105130509060a2c07030e0105072f0114070c020117041a07050c0d030c1b050d0c02120d02070303 59
    0x103031012910768003502c804903481301c00c2003544207001d00400e2562003181542c00e400c00da0078a103806402d0400c442003d0701009115412103070302e802c1c4004d00040e10003020856001d49003d03d181c00080d0306000b054006400361b0381c0078511004002c5808809261080d0710004d110a0340c040a20003030030341e8003811b01d08064000b860000120307414925040e80c0100c200614070070400c6c0c100050307015107841e90f0891181241e03044000c0610600110501406100d103583d0100e4910701c03101e0032600307403940a044942004a418a203041445c54020900b294124541107900803203809030342c4c0c5014080b052000340c243c0018034240240c50350800b128840240c400c0c1c94006030209004001c644c400001c590144c003500ca000386110000389112059507008200c1d003401404c007020328540c2440c0040305244400880d0313440e50754201c07250b00710400301105006001d21030f41c0c600f003990b985600d03103840c8801c0b003080c40010000901103580d5000421042d03a10b940442e200701d5040d4500070341d1000c0b5031009a0100e01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 286349685 1250 286348435 286348451
    0x70e0120030918041104050919030504090c050a0c031d21010b010503010e0f040c15090f0b0711040903020c0d081801030b01230c03040f0e0709083003010b030a 70
    0x40103c042c0c801c81d0800411124908550b00f80009450028940e1403640104850081038070078180100c91418000d50307402d82ca680c140f0351020219500701c0e010000340f010502034001281d61043d00821142d5062610000780d0000710124049080c20400c6240d205c900c0ca525070180c200d0743e40c5012015041e090080c050488040300544551000b80900c0610254040015000c4801c543c000764209203c5c07000100c807103565040505605180c508100002031222508105030b40c0400640c4028109100350720b45881d449a481100c40008048141e004603150201441450300a01944001510283c919152800c3c1468003016503400510000c0042c00e6000c1080140c0d442485400c0d85004181c4480b490511056400d102c2400c0f0030245245001c002c20105842100c14005000140031440300c00720498140900031018202c018a840100030028500700b14041f0b0020f8000c5182400010850206070700b021905440a01d003100c82d10100c1d0000000981c00c4240b80003144210407a80e02042505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 286350935 1250 286349685 286349719
    0xd0902030d0c03090e0402030a0c090504051005070f12060503070609090c05160f0c15090305060615030106141608030405101e020a1101150303170f070e01200309 71
    0x420b4410140024107002e606000320346002440c2030304540001c046035031000a41d0348200c440d402d00d400207108070351102c085c4004c10200f00045ca4032141d05020134800d0b4640080d004022400d02040c19003003141c4006485a140025031028002d0280a0150b803a011380b600300181c00c8844034482c200402c1d1604003402940c0b44500241c0d840d00e903019040c0c11906045480e60413614400260130b64107070300c4113000094424800e100300c00c41d40046455181c90306285041c5141041001046d45001e0351901c02045441d0301d03a04122410350311141880610700010504041c0304e40180103100451540d012109001d000412000d18851840341d412522001d1091400b0005d0300c000c1050000102e410340c620034030288541e0081c01c0441e6091900c00c00d02c071207101e15079081d02c426507610200101048424000d0650114000d011007806200540c507a0070709000258481100802c074008212000c020b00d050b60388500c1d454698400164004142c040038808425180d501003c1043c0c801c021020380441030f4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 286352185 1250 286350935 286350947
    0x90102040b030703021b01151e05030c1c2406060e030c09060d06050a0902010e03030c0703061d0d170615070602030403050f04064b05040b0d0902030d 66
    0x1985803988480e0940e00c0f500003e9001e0340103200c00c0c500700d090021401001110034400c5036458400141711201003407038501c40c1d021825005aa8034002c4401000c18086a200003504030b80404099600c0300c0d0440000c2868680c403182440c0c0100a080207800c0e110292640222100403801c1c050810841c580d0744030426101c02850307910300c81e01504031450b292501c0c5053340004d684400e015100c90a00342107513484204840c4100c4110000640c0d8403100d00540d40e015000c820014801e030015442c100c062000190b807154244402084140ca039850710f654801114038507110604100d00b02e4140803080075018000074030081100040b45210000114a0724102e01505640300441e0b031003038900406500c800029500051056040c00010044c200348200074030010001001c01c6d45c1c0f02400c40d007912040000310046035108049455010415810100c2c0c0c412107103c2d6129820b900c0c4208a401080a0301c8501407980150801040811598001d450b260008110603108505960301651264400d03142 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 286353435 1250 286352185 286352189
    0x1101080708040b0a110c010f0e060106030c1b03050d020c0303090f0d050703120b060403140c0d020a0b07030e12010b031002070c06050304030207030b100501030509070302010509060702040603020901030b040b09010204 95
    0x3c0000c884040f40c600e07200ba51100d104200c01180003850300180c130741554256184042c0b6200803650307842e8201901c00c13040c0708450244c0701c145001d22141020100c01020f010071503034101d1070015040d5040042500400403208103c4c4541d1055499042802006403203070001c6901c05080d001c0d0000d8841440c82c0801c2031100440781c1e4880c9420b016071614103e82d400158100a01d400c0c1d40c40d6100d105541e21134014100951003003018070390380340014880303900b056211501d10340558140e8a242006941c0c2d50451001d8454203000903031170780c1582c24221a401003c1c030300150070040c2031440034442c06040d00880300f006400c0d02100c6841944080031400c0b486060340180155076038100910106129100654000b40a8411621010f49a880310f0200803c140c07852583c0caa0044010003103540c00d03003e655440030992001c0c0c200149190000381030341c0b0a103082d09100701000070b010350455813190700a5018503005810040c10b5a10f0b8605898001019102961070340b8090f800690080c1c0c0500031036003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 286354685 1250 286353435 286353443
    0x1b010603020618040b181f1802030702010207061506031112010e07201006080313030b0721020405040b06040617040f081801090603020720150403110108070804 70
    0x440c10443c001c0311050b490781550b110303078005e468404902050303880c074411006000800c02e511a5506059800c01d03600e1b55031420080141d0b0550100f0090703000344c20320143d4211150700c005a526540c141d0200e0080c8145140104a1031800089407142d0300410024000d880c41d40e10108007030204425030f003009004070172110309400d115400601c04000c14104050304040710342050b107060341c80c40304040005409040d0b004429402091030210300c0e9803030702980c40109407220185103061840c950111585c0d0040c000139055505880120303001c203100b01c600075110b14402008404c02e620a80100000c0d510911800744a10300b4919020b109107007003001c40c0c0845440351038010100001f20901d9140c2c0740014003c0c5d4035200510295800310303507190001c1c0710032a1902e40c124034040b803400026000c40e045411802c00c162040c4603280021310390940114001071055042e032590200503000904904030000010340100012a00100700041d44c00a20200e40090302c0b8049103a40e0303588101c070001c0d01164094 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 286355935 1250 286354685 286354687
    0xa030c0e0d0309031118040611090607050a0627140c2211210a110304030c050f0105091209060705030a0513150c06180c1e08060f04080a030b151b0106030206 69
    0x340001c2d170627401401104403588409080410a100003111500310140955207070300000b100c6420800307a8856190a16460b00c0000d41206500039a00c01002e0556002412030321211010308240000300182e07603c00400420340d18510380c41c0003410b9000354003184110800c41c108040c22444510a10a60388034415148180d4114054010315041103000a0580d8441075038603840311215007544001144100d02035100e00503006002e00d0b0a500c3c003030310001482c40356403501e424000181c00102e1f16248a003072a01c00c50340c4507581100003031814810b240c2e0040103480000f4a1f02c21a5410402900030344481c01ca041c0e1200d0303640c0e210840608050f04080700043c00400e00800010b005500c0900ba008040742441c1c65582c05690740441e1941c1034210001c0142114400001d940710030103150081e200c9107001e009542094110032040607400361009080d2003021411541e494481e03031014030781c610300a1500144002125880b5044e074840301c1010b5a0314015507030642000c005025490440750301800d02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 286357185 1250 286355935 286355941
    0x200c120f07080f0f03010902071a06010e04110409060f051e06030604180b010f1503060f0b0c0f01050c090f120601051c14030a0f080c0a030c0e0d0309031118 69
    0x4101d45034803070402076000c10301c1403001c4407501504d00d000c0d5000e0300180f1401651051141007084803051340c181c1c5036482d418081c00f00101640e00480d000e4100c0b10070740340411444c001c000780b01c02602442e003120003401d00d0901e000036100c00c6411004225242520401c0021019041103a24415814000390704a401000865840d04140d4401d0241018550382401d540e00309588803a01004203901160500005da103040c041c0c082d00390002080c841e55420b08004c0b55261007110249098030384101e0707002800204a005da003010a01a5040302501e1b0802002035203400c10040d01c503500326010340c40c02000c000404c0c40e0b0505020050484c695410802050b9503841d000400481d02c03ca042001616500c00003010700042104100084c04000803010b59168201004010804184c0c0012401080540c0e814003040410f1b10301103c402034200d180100b0f040c3c000700020340d55074015510850b0048007040e80d0360141079000743c40310150b91040c031a2040c1ca8004408105080f501c08003c8800c20139040c1c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 286358435 1250 286357185 286357193
    0xc030709140406260c0a030c0302091b030703240602060f0703110a0e0411070b0c091c0b04060501080105190b0a080726071404090204200c120f07 64
    0x75850a001c4020310106a180e210000702840524149072405840c121030403101100d9002d1107580e800d01700645a55000754607640364005101124403001e1b01648031000894103c4808090f00c0781c50a54084226680341003110004005040110342400c000b15030300d07034110304281c0c0321500700110340d841e6005140340c0e20303109000411990b01070682e806140c0d56032100803401d145e403c090882d502107902c0c0e088020f8920030500080d982c07401ca0303040400341c04000150010b60807108498000781d0701d00324103403264030600c041003904030402c2100114440003010a030810002a850302d101e103115000612003070360380b909101e099500c26150740071558a05603109241030003d60040d025594014144601250f580b42034030301f00f01ea550018607d59408071000801c0d0059404041d8a0001440080840750f24004070070403011394032500035220759103400c0a90250b41c1d40360840200c0030100d814410841e1307400390303102030554000d800000700d0b40a0750a1a6074041240c40541d000c1400c001c5480c3d1414400c0e0755 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 286359685 1250 286358435 286358459
    0x80f0c09100603180c3002060304031803020306270601030b0106050a030f0c11071205060411040b040c030203070207051e010c140604030302130b031e0c1c050a050c030709 75
    0x260303140e1015a44022240403440c0d070140c4000410b0098180c02c07406c40d0f0209484156021003401c0d1031210600b4401c0c0f030040e100c00040342e600c541c05241084141d010422101800d100e15840698188200b2017441032400001d4400c18041c80c02440c0c003088140424401d40d00c40c4001d110140c01c81c01000010022103022b00000d00f0200002d00d80002c1c03415020300a001103c80c0c2c40211800110511010024401c1c10003011000d0070007041d100d0160b401523a20b060b91001300606c010040700b00380064001c56211900b20f001c2d0000000c01c14021032450010040c000d4108681b00401031041400004050505e4000c030841500c0c8815114245e0141000540d400c550961044400c68840c6458801c10381040c015540154441e64001d40c4c0d601d100d071002003e98000740c00800c002d860410602422202042c080411100359450000c0941d540003804034a44c0910361184a91000142c00c22801c482a81d2201e403182d5040d1034100443d8903403068000751400200c0d042008644511001c1c803071880b80300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 286360935 1250 286359685 286359701
    0x4051305040c18020f12060102070602120306220507180906060207260a0c050406060302090609120106090f14090606010c082802031801020624040605060301080f0c09100603 76
    0xd0050b20b000301764082c0041c00c0d4005040c515400e901101400302641c0e06000500c000c004610080c01000d10702075420070320340300191506e44150f4600481d035000250351004035400c6842039404102038502080b000d0003100c21a8000341d0400e40424010034044168425541940c120380d006002d42070030300804100c2803004134600040d002444a00040c480000c110018100b0310580e0342c00200341ca400c060005580361600a1014180140710003550b544a4400365002d0800859100c2100301c40114118010301994004030000781c100b04501c030f00c468003600000c204c0c0b03103048150146a40c51709041a02c0711010b60b03805000514070468080807a00e4080a00020f0008a002011031920360303903c1c501c41c2c910041c0d0303a005604003146845400b2002c003a0306400f00020b002800052034803898010240303040300e00e1290f0301c04090b54907120540301c41c1d119402908010b80301e40ea50f9615026841d59880710030903028214441c00703181880908007003c2c0c07913004209003890031840a09000041d0040c052071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 286362185 1250 286360935 286360979
    0x5041a04120c03050c18061909020310051e010c0b040611070f03030e0619020d180507080f010204051e04021e1803060c041505190504051305040c 64
    0x500c8040340c0707040000c00c159002072181103003841e01455850304074206961031810500c9200220901009001034089199010000b118410301c1d000c081e46040b074490a40b07401c220b12841c0301204108041c050f8001132400c0e80c4003150300b1012590440301e00d030030100c99207182900203580038914400003031080d14410b030451711414000c41c1ca454036030035980c0f86821040096905c2e400c07403600c200c01e150701407140039a074000c1200500201e18102c01401c072060013240e03900c180f80e60b0009a01038140b0030b1f503002c140d00c412440907041c003c0c0160704041e95201543d01038188030b0f00078001d042c02514030503c04c440445502406000d10340c506058688092a11041900e400035020006d2041d110307859580580301da20f41c10b0036a6152016000e000003406030300346d080c42c00f80e03004009200a410580055808980b820540814588040ca5084500d4003550481110a00070f04200712969604400500f0a03a1001e40e0852006801804440259281902c01070520310905406011202100c1c518401d82c8040d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 286363435 1250 286362185 286362187
    0x1110409020a11061603063302010212091e061302010c02010e040f06090b0a060804021002010b03032b02030411040e0327030d14040e10170d03051605041a 68
    0x468183c40d424440300303c850100d85201026aa29100e0b018030501c0094040c0d0303080c201030380c00318150080e060109054208580f02e204040d15070154801d40443e200500206540e40c01c0382410540d00e83e0300c0030580c80c0d941e18140441c8a4201c42180013800c00d1182d2044000c5035144000c0e0707001900d0765108078109174104520110161040d03110b40c03784400e00c1c0c044850009000707150040d00002c440202c01040e12421500c00308021503076000d40e80540168040307a0002c0c0750031424505a004200c200c0500d900740c00007180d119091101c20a6414008050103e40e03040380005651000c1284000c0b100104886100c103074520081c04e00364030481e810b20040b42101c1c41e2130005205100611380f0b01c2c601c0c0d104405800342182c81c81c00c0a00294603404901d0500d01070001c03e030f140e1000e0364042e0b03010f01d06415180d400001c0701d102040361080c0050001c4125180000c0d06410b045440d0703104004108003086c21302c1c0105032451f84013140c000350805140e49150400d800c0c0441c0d0b04030444025000288518 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 286364685 1250 286363435 286363457
    0xf0b0315040b1b13080d0f0905060f030604091415011d010e0a14090c1801050105040308070804030204050c030f10060807050c0102040302150a14030405062701060e07090801110409020a 81
    0x1d04071004c48080d1050100908100b44c14200060003880740740f0b078080070040d008900b0042a1107640c251a038043c40440020745aa9034a00420000c100e10f0340083d02018070b41d42161081d1102007651620440044c403841a982c2e00c0f05410303100c035826910b6403801001c2440040000585000303c072500b2521681001c100c1441001011140260659035018035400c0380c2c84010300c6140101304030071201500040500305600d0940040c0c494012444068840d010004000c4200110101103030b000d50382c000c00c01c02107030610030355440141c0c0045860f0420507000c0740c00305910700304078550903044039110b90300e9110039a19400110f417250001c090300007466409210110060717a61441c186805141403a0329611543c9400c401042c4100381d50210800c400c0c100306000c042180071400c10360103c1103918140105c00c0c489031160501c0300301e190000c01075280110100d5010381d9071a243d03014070701d6030303440c1000c0a444d007071014203c4040c01c0354410750840801c020131940b5407980107403007020a581048038072a8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 286365935 1250 286364685 286364707
    0xc0a0803060d021e010215130f0f120e04050c07020d02040b120a0b100b0418020724060e06060c150402010c0203060c0a03150b09010e040209040f0b0315040b1b 70
    0x8801956191a44c080e2a81510f03e90350303041107108807041405144c03141a09007030341804486015102d000c0d0414180c00f00b89014006440c0c841003010760300044c4120351909110700100b0b0f410458429a119a06140200344030300304071400d0301c1c9501d400a00c2d40900c0343c4941d08100c02441c03003101d4690401458804000c5402c1c09001914070580540349108592038403010a4980542a8000c003000d0401400f05106140310f05150319550219080016552102814494518600180108070300080940221242805a00000f0440704040614001512040100030860203108000c0d0641d0740410b035541a4144400c5d0300541190060410501640b580d40210781020400c441000a104002a07142841549072180e200041865007003050098101140c5150703c0c40344181c1d40341080005203a48030507940396411502680e00080c0308211301844401c6902c09402c1d060040d600c00d00404d0807000c0c1e040c4100c40818440e9501c00140c401660f03450301d1150710451000c0b103c18000c3d2040c1b03c481680 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 286367185 1250 286365935 286365949
    0x60312041202090912030a0207030e0402030109021b1227030a05071505030105060a03050601020f01020c07031509050307020d15020a090806070f2003120a200c0a0803060d02 76
    0xd8241e12581c503407600d89500500c460610090800c0020358429000d000100c4a880280c030340103c4240005aa00e444070f080072aa03540c94041d040354080d10020000640ba00c0b1680202102d106590064a84100030b17070307203152100600c40030250401402c01480244000507200300c0c0345c685500e03c82e0000d000300038010030701d03201c0000c2e03007241e80740e200450601041800016200c1e0a45091070960720755814940440c429004401d401010f050b103c4010520aa000b404408181d02c01c0e8002151108008040c140d82c5004034442500e0b058900144600440705030b0084a038440d030008011840c0042540c24085901101942516403018600c1d40c44c00c148024002890100d100340d03540d5610034140510300c0c0c2807040203801c4505000c40161041c0d50b07103401204812212000d41004001e0f9071041c5141800c40c4110b4004465402c4a001003014140345680290001c10030f000c103000801d0403006201d1180e106400505409500c10602e180001e94014002c44c2c1c01764016100085a103d19408940d0b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 286368435 1250 286367185 286367189
    0x90d020d06061d0901020f0d090201020f0a3c080702180108030301030b130b070305062404060807090612270606090510120f0503130609060f0e0306060906031204 71
    0xc440d6401e5200315900100000140c04c0100c05008502d030500c0c08120340c8040c0b10302043d500c0c2c02520303006880d081d0b80c001c0c091105807040c45004e0741c10644842c1303895090100308058091001408001c01c14003003503c900b0781c00c025089007403520540c0020f41c81d50b00c2e050f04614030899101010f240c0240d8101d603c9011280200000c400454603541503150003001c84000500d000d1a00214460200100d804481c007a40c01000c2401c00080036100e05002c1040f03450310700d02070140700e0040a0f40c0d0081c413000d10300400071501990ba40100e10703102c2d02e07012941e040b0b81d84110000201d00050410761141154003003001c8042102d8400d441d00c007641400c85111b818030301c0075205260340315020058500a03001d01c1b0b5100041c03000c01501c0c83e00f0803001565421540d00082c041695201c031b0002080340400480b00140440b500a01c1019900c0c1e00081c00b0500a01821f0b00180c0798400141d0f544d4059020f203854084010003030140352b9521014801c0528008260300d5061145018103045411401d0044c80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 286369685 1250 286368435 286368449
    0x2190308043011060105090606090409060e0a150606050901020a06020c031603030e1e03040b0318010203010f031104050403050d1a0a0b090f0f01020a0b130c06091e0b090d020d0606 79
    0x8420710310b03d0045410982c05030b00c0b0500503070a101c200318807070791000b0444541c4001102c0009408280d410564010092092329040920031003040409200c01105203030340448029005000c84c54480c0c50884590280c1c400c203e025a020840c4e400c00904142c015140843e08941124100785550301990300038944a20180d0119a40d040b00c5401d01405000b004a4490030120002d003840f4003411095a900c01d82c400c1c1510f1807808804218186181c055940b621401140250f40341d5031100703030501a455084c4404c44400808102c81012802c0601449114503050744885081105414071080a0300b44006080e80030360324080c030801940d40f000d0700038002e01903801c819a115031444090141d081c8802003024407a42c3d1190035180140e81c0010341d03c0360607500c44511009901c6840300c029010820282c000c0110380204000316105502ca0101000c480b40490340b140740d035110402c0050f810080b40030f03400801c0b108010560305401c01c601a00c0e0402e2000d400c0301e6a0040c44e40303c1c0c030115000c64100320 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 286370935 1250 286369685 286369697
    0x30912050c1905120903010f02041d0a0b011d06070c0303030c020c030c062212030f0f0804030c0201050a110f01050601030b01020d09090f060803030a050403021903080430 75
    0x220103440104908055500b41201c00b03041070b00a038440300e9840b01e82c0007944200310760020b0701801e03076202074010751422289140f06540f910744400010f40c026514074403422030ba0070050005a0308151034002d0780b000c6103060711418140303005130a4503c4040c02c032103051a0400c10400040c40020310300611b407002035000340d800080110804c9002401c0040f08081c031846130b44450500686951a40c04031805580885035600184c0b00420320f0600e941d10b01d41c8800c4503120241205414540c0040d503014001c0d007242d8881d035110803104415282c1102c2660058006082d5052540055010b54005c0a051030030b4148001c09034807141403079280090030b4a40c40d045944980902c5082c0d6094041d04440c0c100c24009801c1100c0fa01400500c02103481c03044000305c903220300e00d0f80c0c40c07641d09900071000303002c0c3c02c0c05580e40c92034103003a14000341400341c80c02c80040c407070006500845ca041c2c9001c11a4540d00d551400d4142c0ca0342e4840318a0722500c81500c041d1040c8600e01c16483c005010f02a00760342641c0d031108 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 286372185 1250 286370935 286370947
    0x90e0618040b09120403080f09030a150501030302060604050c090d021c05011a0102060f0a05280b010809070b0919080d02061801200d0e07090e010510060e06070303091205 75
    0x3d90811100001e2901412800e000a0000903104005d4a105010b08c502241c2c4800d00c040000c6e2070410700c084090002490780400c0e02c25140715070003003410780b1b002c3d40803102c1d640c942100344000c071402202d6259600d8001d1044c2d408030300c7c119500144e405d000402c100941c51015112111092030603408441c3c6a46d100c40988042490702010614140c0174005000a40381200d405041098010b00700f480680d503a600291450320100f82800e88c2200310180301d171094480105040041003081e055502103941140090018900007a0050a58013039080081c01c0640300802d00c040d26084000001080320311300c0001c03401c0d40c020406203a07a0742032540104400d08002c00100c038680c0f03c4020b115900c0c0d040c4050315840380c0e07446084c050031522481d40159a904110078500c02008504140101c038090356100107107801164200c0341035010000003c108079102e46110001c54185841a0000f00356088001802ea140200160107841e0080c00c01043c00581590340032200c40942040c800411000710311 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 286373435 1250 286372185 286372201
    0xc010c030b030a050c0d15020307030506240406030207020105091203040e1501020d0c050f0d030509010e01091104021b01020d14180a140106050306130605070906090e0618040b 77
    0x201d4402400a038043c028500aa4440c26200c039464480c45001d00030400424080280f0b11407210148201c4650454582c200110003e014000070f640b0203125101300c100b814070300728003d000041e20038802d18607145402d240c1b48055020b50421501a4140030060001050a0f00d50f03002442803100c205001d595201e08006ca058401038010b402c2042c00701074142900312a980026081002041c00d0801c041100342d03d1601030300c4e0414190b48042c950040740c3c41c4045aa416800c458050b000c1c81c40203000c1a202c0d0740c83c0d00e0888056200290450f80403507207a4109083c1603000f0102c03070148104120400c0e40a02105099a10038400b40c8a8207564255408611a04415150700944510540c81031040760008103070b5189100000030b0001094141d0b03000d031100c001d6000d94000c1c1409429640c042c60051103032865002c4c180701c103a8180e4101400138011b20700c1018000141d80c110b44456101505141c82044501c0c00209443d8000c1d030640c800c0c406810210050504c11442807442440c6440e100c80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 286374685 1250 286373435 286373441
    0x30a051308040e0c0c0a050120120112060608060f0f100303020a150e0708030c0d0305190e100203130606050a0b071e0816120c110f030c060c010c03 65
    0x400500d10034010220000440480850741121159030354280c25441d10300c240c0c449441128000d01041c0308105200c020000d06411410b00c0d11800d040c01c40523082c1d10910340b041486942c001c2c08401e4019401440040051903001098a0007084001b402036140c1c1c3c0141d24103002610f507402e644011404201c45500410802da034021130350407031220410300e543e4002c6e644e0300c6000c03001850320703080c412076510f1141d4692082101100c1881129542607880140d1501ca6200c5110030b540c3e8003450080c1d00e0140c1c024012280a5100040c942003482100405580100004000d43e01140282c2440c10030b0300c062800a10700424503d42e031410400b07054a405421284558000c40c0114401c6000300100c0c00c0d204240c5105641000e407007080d40045401c0809030950b4007400401c0307640046102000551281d0f105030440d445145018400c82114606030383d141851000140304d1000d08010021505200440d1000400b000d400c0b11542541c178400203903c0c1d0018940024581e540d0f41200c0f035141d5242c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 286375935 1250 286374685 286374691
    0x91e0f0b0c0d05040e0c09151306140a08060d060e2d16091503050609010c020d0e06070311030d050c180f0904080a02070e130c06170403080903091203030a05 69
    0x1080c104e02d86440d1100c0102c20b4a0300402d1413540900100c0c4440300c41c0c8900383c4041811090b40030803580c0303030184407101c8403040c0c6078054100001c1c043d042c050701c41e5600e4001c460401c1181d8950640e1607480c00e041008900034204110740854030b42810003090710303041000d0440540e000c90440c03000e405505d5550441c0440d00ca2140c083e03880410058502210400c2070f2003a1241440041140040c2c513a080880e0409544020070324132906003002812001075020316400c0546501355030f803403805400103c031004aa100f085038000710410410300041d00980b02030b048440d669050302d0808900c40202c40c103c403021030306444c07a4070001943d4001e22980c801850044001160000c89a030b41803008502d0f0701c000100001c050540021700c10300124000c001c030500800d44901c00350211316120f44ca60104413401c66044940784038285002c114030380651034004025007401c1d200000e658035900c08540000015102e103406002c10046404280ca91403610000014002d005650381d0401ca074200080707130710007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 286377185 1250 286375935 286375937
    0x6030105040c1703070209090604060e060405100f1419060834030b0703060e07090509190605120a1401110a05030c040f030609030915091e0f0b0c0d 65
    0xc2000042c0c0310301d0030310705035290042c030110803602000007146580308031007019500072000c038104040c144002552501c1188902d500380103038082d00381d2141d80c0d02005c0c1c0d00202582c10400316032582e034019501000d1030104ca040080740002030818907070350100c416903551511205c100c088000e910b940340202e40080503860014854052401e42130025400a10920482c620880b05000582003008883c0301c040c641042c403454260509c0b120240007050305108424001d15a42c0c00151207034050703030340c4808485010b04107000f19641c0031102c01d81ea0114880203d0391580c0c4040c045542c4d280c00750054014090ba0008100c0c00d1000c1c28500040c003403491803e0840c1c2e050039034000e144030b07101065070444101803c280b0b0701d0b40c0314050a030f49580503e4001e510300600b617450000a104403600101b040d6806502c42000081d1507448035444041c5000781c600c04580c0c810f034104041040c5e130000711a1084074443d001c03401c5480707101415007040e542c2c2c050341041720701181b41110b41c80181300100760300e001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 286378435 1250 286377185 286377191
    0x6020105150a081b0303040b030c03011509030b04060b19090b031b0616060b03010524010c0b06130216050f0712030210020a0c06060e07020705040902090a020307021212010e060301 79
    0x9007551265541030b03159544100369003200c5181c14145c07010029039000d001c00e0408580c0782c3ca0402165804c6810902c26a8194403d91314119040e80c080c417001c0045d607400800303003042641ea54689030050f210b40c802103a0866080103004500d0f400c40c210040240a0760b90002c1208004442014a070441c13030045001408821400c40e00c04c0d41d503450858a4642944110b070044c00c0342400c20200520004070304607055401c100c2000541c4d0110a01c0c0c00c0c003096006401c0500251000044940f0f585441c0003c0c0071a003584080349051400e03070407040007110001c801500e881c0d0403806a10b0b44201c01e2600f00e51582c40741950596030340d01440b040c006807000641c48180b07002e2546000355100758070069071600c941d0018010205502c500c181d0b040d82c94103c201444a02d50310015802e000798211356240060059030008a5141f505000c5d107010190003d11240341500c0b4150010001c0d4409041d00055204000310f8001217003ca03409001c00304000c10340b580d41c9625003c0e06181400005110901c40d1349 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 286379685 1250 286378435 286378439
    0x109090b24132309031912060e01091b02071809171b0a120c030908030c0a1401110d0b031e070303140a0f0c02150c0304091a01020304090b0a030c06020105150a 70
    0x100000981d10584a0303070314401003c9103002d170f0964601f911611a0602c550030440d000c11502c030b280e040ca070304035440303e80d0401c10220301000c000320340302d00d0307280080050b0405030040028104041c140b520300e541c80c480005103103040c1d558040001e4105a01646544e601183e1689141c02250101000f007189a024101c403078082d41d00c8256804034030f82c5020511400d16001024148100c0c403d1001d0002c0b902102d590b040580f11070f0b03564102c4103400300c81d02c43c00301e054128101d0040c003801a1400101002e1400c002c14066076001811a003c00240c041c0324120710000c0110003100d82c80c2c041948803024048190171424000c3c28000c0c2d003000d8141512081003507142d100c0d44001c000c0c190700c0310791a000ca401c20f0144009401814100d1a0600850020440c0342d44404040000c10072a1b00300a0100b0001444001e1131206141d9141068091303002840708009136400d40e04145000d0000410450304141c4070741d0b4240d03400410f5009a40140c6d0b50300e0400006582071503083d600e05004450300541c42d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 286380935 1250 286379685 286379701
    0x140906010203070f08130e06040b0f0a180b190303021b01120e0a0203100b01110705030d081005031c021b0603151206010e0f0109090b241323 62
    0x120460000409801d00400d8050a024a010031764080c03e048020300e06e0200c0d0b88540c2e04182c1401a906a80326900e41030ba0b0740c0c01840c000000c090003401c041c02c0f40300c0352071030b02030030380910442460034001003602d41000e02e0050703440ca5004040d40d004641c4070014a800e60074000d00d400009040e02c5110020100c590750300360380200750141100c0c840140410700400030706450341050510f000081d0540300304161f1114001240d006881c2c1140b0a03610b004d0300081c0c0714042d56a40e06a48650b5416410880713001030450720481c58140c1c0700c01d66185511802d941c0390080381c907001c500001e114a15801c18140c000b499414000725040d07403002c1c010b401210f804140044e14901c009080d48501d0f001e002154541a25004800e1341c208004605403030840d030b035175150010425011030354400d02d03001410000c600a600b03440f42c83c04858001d9809070081c0d951407030b804c400e0703107484403500040b1058225004807035841000c0f2052055035074001003030442c0c802144000c0e165084075071300c0d150000d03074040121030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 286382185 1250 286380935 286380937
    0x1305181605180f03010f050103030306050f010816050702150a08010306110304050c0616080712081f120c080a11040e0d020a0b07090803030f091006032303041d01140906010203 77
    0x910040740c4150b4008003c000290040000a0204c8002c1d03050100010615406500a10840b4401c1c0c0b00707540c0080b01d4100440e0040e4007151400100003e24003441074061164020b054490b1000d4034107050302003220101c00311504014101400502040c0043c4100041c9001d0484041c4260b10050700794240382d6281030303e50304030028040c010207006c41e02503a040103244007110040d4000c440c80781c0c2d441060820983ca81c4005109001103811000480c2a5400800340d2141d2008049250900305083c4040408041d25407002902c449402410101d0340788000d024821005118480d101c1010900710213000036506540c0603e2115000800e00400c06071700810310b0154960721203402c66103a41d400c2c00c00d0344d44444d2900407200610002c010408443d08070704507140988809011181c803648840d0406040d0b03050380c00002d10389444041180040d03088022891342201c02c4005407410551500048500e01c080502c08040340394042c1d00400410044039020f450302c1c0c40945880c0c06600d000b07000070b51360b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 286383435 1250 286382185 286382227
    0x50f09040f051c031a060708070b07020102120a05040302151306051308040e1e040f11130e01090b0105040204151107030501090b01030312091101051305181605 70
    0x24000c0c403420401c200310301070061960f4008003a50070340e010040190010000c00d1315851401c410600a4035a12a40c0780100c103990640d580000034074079000c0d10f0381e2011103844002d4490f0301550340034456540ca03e11911000c5104421000001403107180906000386495544480c2c142c0898402043c0884010040d1044044c0340d0401800314141d100d021200002105042000d0022034000c50003080d44c40842d0040c07800b80c066801c14040c400d00301c1d104a00008010340f402003000e4490681500021a08071518540480040c03c51034002407009a140c1a034040c030708066006d035074480c01501041541038005001d0602607074114149130411144042513580e11041100f404422155401100c40410484000d990310900030b0180601518107000c0f036500c00e00007100132650030030360004141001d2254002907500071610880540b62040103590642c0490b40b135422070755080340041603945072041200030305050124100268038001401820f601d0180345c0000404c02c040100a001c00301550007140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 286384685 1250 286383435 286383443
    0x9031c200315010e100c03140a050408150702030a110a0b0a05060a060215070c0206040801110a030b0102031303030815030f0a17040e010b0912100b030708070f0306051806041506050f0904 82
    0x1086c0380c0c00e09136511030b080c1c005000320820008104c040305074000058001c6034502c0d030072038940700b903a11540000910f084400c0401a8400d05c0359190091088211082221402c003da800c020410b40340c02003101400c813040c1c4079a41c1ca50080c401c6504002d944070004117000d201405d01c0021712089203000e00005040b810820070412600c2d4250341c2e1700c104650061807800020003403030780c0c4000c1d03d1006030040404680840d2a00000300255400801150b03028507043d01910b442d1400c643d401c2d00c45040252001a181c1650543c0c00280e0b10200006029920345030000c000b685103a20f02414880e03c04038040c1c00544003440100050085140302e617042d11fa401d0b0055485064910115050240c90036a02109101c1c03005000b014541135803003a418404181c0c25121104e0325003038200c1e520041441a010301010708074041021484a40c44a5080742a06500000e4001e6101c8002e04e0042e040e981580e0900707002d00300c180342034443c3c03040400402007031754659002c000600001b001860b0041c0050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 286385935 1250 286384685 286384697
    0x21204020420070308010906120308070f11010207050721050601141512151e01050c0a05060115090f0302090c0a021606111509031c200315010e10 64
    0x21442c00340060107591024900e5542c02d40300c054070b00740200036883c00e1140703507403591400c000424980909100c403040603030035440326191030321141c004440d0300f080d0081c2d52003001003948400003079542c01e0000f41003440c0584000d01c0b4003410950708202c845650408d00d50045150002c15001550118815044480002c280c003040b6113400003059403500c7c4400800d22011b00023a038000c124080440450042c100703022082c400318002d07001e102c0c1e51b41c00041101064640c8500554103584514001c0070a64030b040151500c01d5142e50341c007031600c0002c0e0018041311079a4080c000f45e0551200d040d800814400034280e85c21495a008034a0b00003000d041c1c284003120010311500098000c0160846c0d480c815180100f09958030403000340900c2440341004214011500860410442002d100340200305220140d894072940c404840880d05243e200c2052894845202e0030082d20400d0303402803040d03012200383d0380e00e140c246410810801c003021018140a00c04011030416150a0001c1a107084241099 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 286387185 1250 286385935 286385951
    0x15030b0403020a08040e071d1e030a120302030105031207080f0d02090909010501080d08060f0f0d0c0e0402010e0301020315010503090a02030f0a0303140403020a12120c0f0f02010212040204 83
    0x22030410194200c06402d138140041d0015100c80d0354030405108107090b6482107a0700a030484820800c000500c08583d20011003c1000101d12540f44940307d101402000c6940c075500d95a10900a030000c01c1c01d150104c3e03404001003046090a00c81494060a03071000c90340f0700a5150760300d0800b401445000380b400d100100319021051040c1c1e0403a100400002c018200914001d050280a44000d01800700d05000e01201002000c0c02002008d01409000f40710f0518026200103201051403216280f0390300c103250b0044c003000300d01c1c102140400f60040c0c90f500301c41440c207070001410242400c031009000360310400400c80480c6e90400b071a000301c6000d02e0995541c0e04c620b03a1442c5486041840039625000e10081200000e40c001507014a440c0300f61002d020142c000b0310841c080000458028015802c11011400040c510a0040d021205203003030460802c40c0040c3d6000440b030302000c412000c01d0755032040c4203007aa000416500c1c400160301c000e602d0403100c01c2e070f0b410301c0c00406040203005035145c61903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 286388435 1250 286387185 286387187
    0xc0f0e0f0a090614100b0c07230a08060403080105010c08090103091727040b0901031103010f1b0306090612062f031b0405060a0f0e09090d020f0115030b0403 69
    0x400c42020b900040103124040c48003803804d010350b5007510743c8244c429080400040007040343c000e40e243c00d0400400b5120251518041c181c54142500b180071190a2182c0381c0107050b65a01c543e02e010305030820051a4914091501800901d0b040c0c1041c1c1c180840318400d9800642d9280c02c44400c43c0003840c1c0880d81a640f868407001b0300700d4075114660301c420007090004600385480c621440b02248944004c0804000c1d800340021a0040024150003240307000050010440b6800b00f81c10300e46c03016000003074000f01c1c42214000c603a46400c0103140b81003607001c0041466410300072040503140b541c01c1044007500d484c80540301c1101904000748100d85551503203100e041c00049007604500c01e04050b901c0074a034050302203c0d0380d000700c480280c203203940742c00c8002e080520710503038040c1e840c05000700d0300e40014074105841c03104124080b982000500300044088d511138801c1e2501039400c110061080c11000e103006824070b4011840720742142c0c50034500100410020004104a940082603c41140c0315424 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 286389685 1250 286388435 286388441
    0x10c0605090c03010518060f220303020c060a0e0c01120f0c08010305070906031a15030d0e040f0e1e03041a0d0e150610030e15040c0f0e0f0a 62
    0x5006040549031204100d404080410210700d419801c400810141c2e03034403408020b840b00e1000030026a40e03c40d4000a41ca2088000c109421071104104d102804504c0c125520103544001401c03000640c010490f1081110708020050300403030000d8060003001407500a942e5144c840740c100321f040114030b020580d41c0703002603070100c03030303e1500340500b03120040340101c1c0601510002e1100300c076103100b0900c0001d501e20b410f00c5080d00b540d501601000f00f40c0e552900000260002a200641440c1d060b1b005040e0342c1e80821001e0b0003018152560740804040204220032541d08451144501e4207100c1002030b4800082400c00b40d6201920a94003140801c00a4500e54025a080207031140300d54041c500401468030702402e407401c3c01200a12024440c101840c0d21800c0b021103668102c205000031808600d040900c102400c122031900050702c29426000f14606240c6410360b41d444899002407105125488a410015000881d0102c1c0501c0c540000e001c1c4104000300a04d2100c0030400109060740900d030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 286390935 1250 286389685 286389707
    0x303140405060a020a031e09030801050907020303190b0612041707050304030206030c12070905090709081b040b040221010e0708070503070e0a08010c02010e1c1b0f0b0a06090513020d0201 82
    0x1200c86418041a1f00d501c0024054582c0c00e82c00b140100740002218605004030a03c10ba1042e070103541151100c452100d02110000592800c282c0c6a40fa1620a0f8585c4009041850701d140001d90090034203080240901c0d411917003048107544200410404500000202d0b000c50b603041d0b0300c2a54907619104208014007030040e040381da026801c02441303103040d8080c9162061350030032681402540c94194040d900c51000380319841c1c0c1508026402d00380c91105e40c4001030658005040403a40942c1580018100c1c1e0080a1402c00b0602e08000026101700d034050480c0900004c240500d19801c0800e0040c018003002001041000300c0080024501d5205402c40c1394a440c01504441e011030300c840205002e001a041041c006600e003100400d1504800500e070b24042c02e5120b42004030f0541d04030200c0d01c000384071043c0c1070800d01e44944000092044000c00f902d81c3c0c0144800212130910410800075540607502c1220b10508181c00c2c820042000e001c4040200e504880d0440380650920058130604692 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 286392185 1250 286390935 286390961
    0x203090d1a010803031b0301050f091305030a0f02070b0301030209061504030203011109030c040b06030a0e01201c09020f040c0c170a110703080304061e0c030204030303140405060a020a03 82
    0x30600002d01d9000010256015021b401c21070313205c42c810307500d090189020921490350300c5401d9002b441810b0030102c100c0d54221054643c1081c04004903140d003031944d80b181d5000000269400c450b102c1c0e02e5410701c1050044c0c103800c800d0500c2d652441d000242c250501801942c459000e081c0c03000d03420141a03003198000d40d400f07002413022100d902c80030b4039290815a0490302902800070f81011078601403182034212000104281d0840c0c56500c80c0100910740d1200b015140e65030f502031541c00c0c125101910718000009030515a640b45010500b01101124102025210303060802000060341c810320721407080c1d2400e81b000200c41c10f000a085030305000d031ba84c020b03101c4801da40c1c2803500d04c64210000c0182e0145915005400034003840e8460380c84000f4400505502000c2c4003044c000342064000c6c7c02c88503020f6080350910b902c0500c20b503080740c0c01c05110101103503002070700300101034040c000d810304061503a00410030307443c00b41c4910780c80f0540103040c0100980d0000706115401e002c0da002c2c00580c010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 286393435 1250 286392185 286392233
    0x6030c051210060303030506040e01090b010303050c0307170403060e03030708151512061504060e040b0301140f01080c0d050c0d03051e030421120c1704080310060509010203090d 78
    0xa05d0070007400501d02654070500813400c1542d4185480700501510100c0c3e40d014401032080d070720315101210150003119040d801808204007600c04210b991100491050b04442410380c1c451861910000729042c030150b80d40503400510401003010b4001108a40c040c2d14040c1a030000841d0000103000054420542a800200414103402030090300040ea84204002c0c5c5154002003e5001d00043e40d0140b886039200080c00703a43e00e400c3d141402e40000e102c1800180010070b9500c1c3c41801c40d4100350040f03c0c19103112410b440100f04000080000d6143d0100564400d138540a0300e44480d500c074040e4008042c040c0f2110701040701014850021502c600445c074101600c081f09a0350205d030541d1054409031503e4601d02c04020104804040d11072183d0400d0310307042c3e000c0c0c0c00c02e640c1d400a081c60390030b02d00501c8260721442c803000c1c0d04082d04070320883c41030784071707680d00c1c589090038100030b0540343c11242c1044400d10030103040ea40c001089901d1403e0480d0090301010f024230f071910780300100000c8421300300d070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 286394685 1250 286393435 286393439
    0xa0602030a0209040e061501030f0b03010219030b040c0801030b071107090911030c091303121a120606061812010e030a020d2a0203011503030207080f0106030c05121006 74
    0x203003030b901519400c1421102880480311418101d6074420307054031408003008040300328004c01d40c000e611413001046004c2d400300346070010360300081c2260000c03c10310f2585002c850121031840e2307241c4140c19290320211000c0212401c00c1400a01380700050000034800f800310800300d08507a000d25104404e03000d09000705c6403410744601840000e484151801c41d85801d000b9540006441c01284d600b84143e00a490414a6603a5128117180c01c941030f00181e06104003200300c810801024000ea410100d05410203811805465007805848030001c0d4040e00980c00c1201408a160b03070b814100c1d01c1340e000226104030051620000900c1c46001445103c40c10741ca440000b070700d40c10002c80079000d1340446409440500c03034503240a4a01a07a04000000c0e035814a4101204056014820482203800a00005040a1120800810748085400035809a44120070401c0104020081103545a43ea40002e101c20f0f480e5680300c8441c404103004061080c228400300385174225040181c400c084101c1103090180359 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 286395935 1250 286394685 286394701
    0x20a02031b03120313020613031e11030303240f060d0c27060507030504030b1503070602030f0d0e030918010501030c030e2a100306080105061207170a060203 69
    0x1032603071501c080c000e019400c520421062000180c0e84140c8110a1089007014176500b0050190306c4250415a07058448401001088411103e46c020010680d0307110070f00005401e14000814504501d0381c4264410000c001220000e0b005040740c0340714000311740c00745d407166000162404403007420031a080000802e0a98884500b5044226800f0300e40e21a10390001c80ca0324210400005911030a802500c40c02c0700300325183c440c1c0c00400941c0e0281c075107642855207c0d6260303025502c0c02c4d20108911a01222050380780d25042c041d0a00400040c001507281408200031543d81c2d00800d5403920302d49a0741c01890500050071b0040b513884a000030007451035034404803441080c21000b8003d507030009142c030310240001400f91080d5510417030560f005003d1042d6007500101c0403041c110f1a40d16140b00b040c0c0806581e100c0c503420142d9402c0545011131414209a440c90855000510043c807070840781316605201c03003001c541c0078241c50310707541840168001c0040c0e840c98480c200c100185030601c000108240a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 286397185 1250 286395935 286395973
    0x30305190f021201050409020a03080c070504020406050904050f0106142a060f090a0209040803062b0203060a0911092d060120030906090f0409081309060b19020a0203 73
    0x1502458400f41c080e62914144030454a400d0402900824070110030310124880d00068648440c42200315442d154542020905a070403540c08000860300100300000a460140038160b8407980e480c0c0c004002d50314002c0010201203501403d00f10f1910009808089404c14160861a050382070792080c4410241425407540c1d083c0840350719030340c10110b1002c00d4601d6004208400048c1d002000c1c05040c2e11142c440c01c081c0da00280426038048804e0b440c80c80400041c0b44001d1380541e000380c071250401c00b01d006150620100411840060345010052000900d0a0031416560201918010855515030a5911014030b607144020117804040003040d460f900984a00707841000207036101d2014003080080c042c000190080c080a49410a11460342c06003000c0001e098450340c000d241d08040c075442c4011404540903c0b00682c1d4101e000640e4680a204008108000384440c0b003040200900d45103c4d58060f00405ca8038050341400c0d4107003012000d1003004200c400e15002800c0c2c4021016080040240c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 286398435 1250 286397185 286397197
    0x1d2503020a0617131101030b0102010902090a020d0608070b07030302030613020408010207061d100b010c0209040b0901060b0f090108040212011404050c0307050d080a030e0f07050301180f030305190f02 88
    0x11016414001950882c10544d40c4044940c0a03400c404001c64900042d409050555030440c1190750380d100341b501513a56102c0d918007445c4101e0006035603401c4150803c0969402d80c102103c141d00101c4108a0010f529040f201c0c495094900180c40c0e0701c0d4840060250b40742580316a214500204005c01c40c0c510660051040342c0c4603150403c01e81c0400c03a001c1581c1c03405c01c0e9801c203150300001c2650180316070540104450340014900a030000c441c5a0001c0c2160b07034281e0702a01c024014004100492a00744100d00160510105050404100d00e21081c2241b00300040710b070400020070007140031529000311141400905000900c10715120b540c903403031909000c440c203546910410b8800f0400c0d080118502040c1c40002e03056940c00c485a4803040b00c2680002c21b14010142c0e9070135541c0c00780b0000d000780c0c0d0803001030300e014000d038901d42010103003074403c0d8a10960807c2034100c0c20f000013803180c2c0031b040c0703259605043c0491075a1b07030907208403e2220160040c40132507041170340b6044c200e00b13280d0003064 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 286399685 1250 286398435 286398467
    0x50301050a0908070209060609030a2d080403031206180b09060603010b0409020702061324030c0806010c0501090212070e0f09030703110c1509041d2503020a06 70
    0x4100da9600301448142c0d4180000903180410030061400541880214030b039000b040500194501128000443c1c80e00c941c0c128181d82c116161070654001031764100600a40d80f004039070300d0842e60f00c1a01c80900c54410b520004061110005801094940541000d40100b1a406d8121070300120b08003208003600165940741d1040300418001109032816070b0540703040c0d5034a01c000d03d08260400740c6000081d8410322050760300c81024401003c4900c620305040300940f507000500c82c0c180c1403d10541c110001602c070028141810a10765a059580c0460b143c0e5103c0402d180c010104031007401d01600503d01103c001e0342081c004400000b502900140e03607011105030200b41e08995a902004516280090700c1c1200c240e0000c00c80350000c00d200d400c12806503490030090700c0b040a4400002410710200145019451001180401e0240303441c2c0b148800001900720103100c080302c1d002c0c500b9146c010911045050308000c420007200f018010003907001455000d030a10381550b8580e540505078a600c0f00c0100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 286400935 1250 286399685 286399691
    0x50a020c100f0e0d170a1b06060501080c03040206030a1d01061707121104020306011106130209060f090106082a130b0412060518011404030905030c01050f0c01060519050301 76
    0x802c190030204480c0304490303003040c04d4542c03008040030302c80800e50045406d0820070a902031a007401e40c240000018401c2e115100002304a031905001505c0341e032005003001380c4441d0034020000036032a014216503200c8621040002c40601c0405200341203400e000460003198644840402c20342e420107080b902c0e0461410480c0d82041c1d580c1e036064216040c49100414809803003410704050b0829401864205005041842a0408c400026440c004044800c6d04244845020b4203080d03080450405400c0541a2103000304445042d0210700034510622521003004409000036860701e4410300c1000d210001080c145022920032445505c56030066007200c0d8800048200c005203901c15541282c045075541e807294002542640c50307100c01402c0080c0a4841080b4281d03040501c1e100a10070750035400511019008035090a0030000d042c5141c0b41c004034002e0348005c000c00304036a00b01c42528400c1070422091a42c501c02182040c0c050a00b0f50710403500001a020446150009130b02c3c10819180164020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 286402185 1250 286400935 286400957
    0xf3307122c03040b0f09031e01020304030e010302040b0304020120030706051b1c0b010909050c0d0e0303010f1e051002210909070c06090c06030603020f0405070f050a020c100f 77
    0x1642c80c1c0c400c501c14031405000810034211940d0040000e81001c01d40101915824542c501040307041d60010010120319075800400c0004040e0450540c03200d001c404c1ca4118245828050340ca40540720281020f1306002180d05018070307800407400440328249141c0e00740c1e81c940c4401e00c1c00c100a04815142c04041c19880610380b80212a842c00b541d01403d407030000003000c880c04404d101c006100030212541000300352840030a00e05121f018070b90283c52040102c82d6a1580751403c40e0446140c45842099a0020801001100c07030304a00c250030313140200e1b001e5542c0d450010b22414100c61990190f070300016202c800481c01a00403d81c0b2a04081441d807140010f034000c030f2010031512921036401da101d80f1542c04100007610454180b040c0c40d2180400047c42801d40d128447e41c00c80310307031143c5d000075240c03c0c0520450911381c2c1c0000812078190360510150610001c0500b120303a41065800801c000402c0c48011705108000e0b0450344000034080c200711142040d001886015005a0ba401040d406808 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 286403435 1250 286402185 286402271
    0xd090c080607020a0b15030604110405070309020f100c140303010e10210221030a1b0503120c04030807081803160e100b03090f330712 59
    0x41e10344106940d0707000c0c201e48806580d4041890002030480c070b010000015a9500c140c0341001014080e90090701074032188000b00c0f04000503243c0041c041800c050402198400503100d0702d07145145088101e40294805903500e40c00c4542203c0030310040c0082d4004c0b4284e544842c1d001c0000c1d0305071000e0441c0c054156864003050000c0b0411841350801c4418007040ca014056120b007028008503100801d0181c007201c1c010a81c0131340c01403807040040c3c0fa800000e43c035041e071500050707940070316007404100580d811550f45642e501c2c0d00540710421002e41c0d410380000c140c03140190841c1c000c0c50f8000f9001c0e03107480040c01d141c8541e41003daa0301031501100c038181d0019140025058a6890b114407074440da55080525081c17421001501c048a4458400740102d00104081c01442c41030404800a1110180341c0b103074985406121403c43c40e42d080f64000c0801802240c44061150180502d00d50985407541c08080b00d803840700505410026141280b034034a5000c00c4000b2091115000494004000c0c103404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 286404685 1250 286403435 286403443
    0x8010b1905010503070314040c0f060908060112110d0503040e06040b22021e0d050c0415050a170a02070b090105070e0112090b010b0a110c0d1509080d090c08 69
    0x42400c64041058404101c550710a000841d84203243e450302142d20321003020b19110031201a07500f00c4d0141d004007400e0007640050341005009005a00c0c2c401d0300180f5010940f51510010b0003020304011290001c48184a011102070002d0840642036101501c0c213802c00030f8581c1c00c54091030f8220030515003c2a2145020301a40140c601c00401308408501229080c891030400e00311403d04031a028098109660101080110f14044116507242d0352000005400e04949000b00100d901c03241c01c1c002445030340e00c000c0c616003603101c1c14200107644040004003540d614840e54400540c3c250710070100030555445070080c29080307104200e4030800382c8524418500780da004503840400142d0135620380f0010f62042c54010003090900000042950702c079114801c40e04400d0b0415110702c18001010341d829680301107202c004c0b42e02200a4810700f44004c0000d240800ca001d405000445681c05030b21002c04681d11034074000340d00c6a903043e50342100035400c101808c0b11032400d0b9504030039908006000b100c00304d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 286405935 1250 286404685 286404709
    0x10e0609040507120f09110a0609170f030a0906030c023705030f031006020601030c03030c080d1b0f0305010b04120c0e0f060a050d05101113090608010b 67
    0x14202414090008188002850700401c4402089881e4402901180203840342c40c02491188401095684c42c504058655a401855481c000c95110000f08075055004500b602915191070b040120301002d14246480c02100494030b044c14007001603030080301031304500d01408a805544050043ca1811a800d80c1c0b9855002c0640401c041000525007002031205240118130110111014409801e40c0f20a072954201c02004000c00c5000000d010111340e090303025400400061008120319819940d4030b081d1118648001428440128900300401c80c0d56000e603004001e4080c02004407210080243d001140e41c1600503000c201001001c6503500c1c0700e4020745042e60750f080065440d00d842c0c007029000d03044400c101940c0708a80c040000c6600400400d007103000d0701c5c03484446045400c1402c100310341920345a010f80c0c071541c0760002d4903000070004610341941055410000031039000142d0f840a151096118001c2c1c80c0383c140e000454801c0b62680140191070f9114001c00000741198240302920b0341325 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 286407185 1250 286405935 286405939
    0xf0316080105010c11060f0409050f10050a030f0303020f0412030e09070302250507151707050a0f0e012a05010b01090b040308091504030f0314250c03050d09090b010e 73
    0x42241c1d0307400c3d040a00081a0040070103100a24050340c0e0114201101c030b0a44001c06280bc002e001d02000c400103140840c0500380483d0520a603502d540c0e0f890207040e078604801011b1640104a8019104e01d18040c0c41c01001c039001294044101d6140040503907040184840c42020500003190344107100b4429076030b1a02003c4120901d401c900ca04200d07190440c17040450b581d1081001c0487c0100c0c144055031560501074582441c28020306160074420140200681c08000c802d020740384035180d101d05c0506280c003042c2849101561500012100103504c517040025242e0a288054a580503450f24685801c2c01480204040794103d401150b039045035200ba64294501400b051001c02c488070001c111007540101250400704080e1070009464100e640151145084083c100c010305400440799441820f5441750305141840020850b9a070080480c0640c0a24031094982000c10100a40d104091900002210000101d141780101030610f9401062105410a50b641c2d202d0350181214005000d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 286408435 1250 286407185 286407203
    0x30310030f080705031b01111801120b0406080a030201050618012c010f03031d010801140301020f0d23010f060807051603120c0c0210140f0316080105010c 68
    0x2841c0c07103072080290191402c0d00d44400410070640040e5003080144010140c090030401544129295242180e2054404848420341004200042c0c039160780c02c162091400d00b4815104032440d811320f00180031420005d074005181050106200350005104251588268004d100940d40d075006c0c020402d00c131000d2113080e0200030005000300503d4003c0c940d141050b42c40e41e2003410500740e01d6599807100c280c1c443d0344000d00410083c020300d41d1150442d600565150705d08201542c4950000f44035400c1407142c207c200c0000f41002c0c01540d4290121102464a206d02503107815440c400c0c0402402200240715003082e0500500c00307407100c40c0706041e040b50004490b01c0c40043c0b0f04442900c10010041002c400c004040051264030118521205020f501a13545d401e040b000841804084a0000d0442c40a11444540190050b920084401c080301c1d01482c0c43c00c500c20440d84982c1440c0542007003480490004420855401e1050899030102092951215582c1c2d0f81c600040d91800100d110203420381b90 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 286409685 1250 286408435 286408439
    0x10e0a0e0a081c061d0405240402010f0f020a020f0114070803060f0109030f020f010915030608061506180f090405030706180b1503030d111b0118030c030c151d030310 73
    0x1c003070810103034032600070300c1514500e10b042c10b8070005140c7c2394031031010310b0368004e0103120070365074084420744506503182815001c0104206019660313181c1050700a110b0002c005049101d80d00c5201c21500700340d0214a182d0701c4088500e4034a806810485025000e84404140c03070080350310840900c1d048903046507107645020303000d03000c0c8000c5401c00a003160500031390010000d24403101c441809600400360341c00051050a1401c2d041c2441806003080c000a0742540301d00205641e13200490306640e210070b11181c032412150303011844203c10244044d0f40010b00b5003c11040c484040020b0480d00e100c0e0908105500c800c0e070a030b44041410003005049102c0060024100102101101031012001801c480c05c001a40241d00c0c242c96201c6000001c51501140090b0b01c10154002e00c405a4515002030101d80800d1400030844c02c0040c0025040000882c040c4040c98020b000000042d90828030950040440f000903101a152003405031903169111702c1d02c50501c00021040e68000c40c0d40c50740340144c841c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 286410935 1250 286409685 286409729
    0xd030b030d0f121515020d0f030614060c21070b06010c0c031209051c051509060f0a0b060406081f0b0306010507030e040203010905040312050708010e0a0e0a081c06 72
    0x84204c40207140e081301d040740301040b242c0d11582035520000c415801400100e10f0814000c249000c0c5180c001c0c02e160034031009002c003040403445050300b0401681c1c4180c5950100e002c4925240744584444105105684004111120107005040e054014410a80c654a440e03004441608000754041c00103546c01205000149030b0b9541e00390700110516254042d81c0c1c0b5640002c0320b08007801c0c09090841111182e01c0d08101c0c0501c4000703801656400c0d442124900503284540350a40140001000307000d04000449800351644082010400503203429141d9031603107070182082100f601c10803070661500741142c0b149521140e0f40c005407980980c100b400d58032480c0041da4607400030b0004034107110301a907400002d034496101940c003c0034440740104507800c26090250006c003242005d100a903050500704041c0ea90000106411502407071001c59003652903401640003489044071030551805410700303080a00c00148050159400c500e036a080c480c4020304103d004a410074801c500c034100c15100100411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 286412185 1250 286410935 286410941
    0x90112020901031e0f23040602070201020a080307080717060d0303051005060705070e06090906043201060509090a0b0c0f07080c0a050c04020c0c0904140d030b030d0f12 74
    0x150018180801e0038000c3d0a03080308100302c03001c4c1445801c0d50b01d0491601d110420b000c1d02e03451861840218056005004a50050728001000500040c1e000101c1500b1644200404070085801c0314403192681800704008021040c1580c0900c0015100d0911000c481c010310601d03030090704c00070940d00071099681d4082d400340c0001844260180c000d02000625615004001c0500e5031140000d011030320304000030f16100140260295015018400401c001d03100300052950b00207800c24001101c0c2d07a1210f10244140308007460b04004031846440b1365072540e1054004105460702121008150b81d105c00016984403d00b02010b0422803010380402c4c8100c01c403e004003c400d00b0340340f54924190158581c04010b40c856a00c00c0b6070390703000c055191705200003408605080d0208a4055282c40c0c00040450307074406900c00394a100e8075042004c41c00304800300b0f00040382d103908a070642c3c855420240000d401003800c000098040d000300441950180d10541d208d00c0800400c0e12030741c407041c265071040802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 286413435 1250 286412185 286412197
    0x1050f040519020a440c0d1406010801050f150c0a020a0e07080109111902010b09091f020a052a15041a01031e030504030219030b01060509011202 64
    0x107204150409451141c90600050881d81102d03294084076201c00008070008640045c40031144481d039680c40c4185020f15008035403c10b101219555040d16140140f17200c503c1b8558170780c01100e1800c81d00f15080c211840c1311501c5880c00344c03103030940383c0c0e40e84040c01104510f03040c10560249080400381036502d4103102605026000304100d030b03c400d1682e404a0074600306034000c9020711029400300300045a0200e1403d007d4840e9a0b4244104482c62000c01020302a448020245c070b0b084c40300c58034025200f540040e14a034070003010805c2c5801e0040d4800d0302c0c0c0341d07102040c0c0854580c00203050058851802220300201d4075603036091130301008621744145000c191555110b0f00710078100d40808202c0c10820452900c41c01c2600169506151500e2600a150044841c0010740c017000100f010414100c8641a1120380640c0103003209814a02298a4407a9400083d03000a1080100c0c0e092052106284103803031240f070007218582d0301c2d480d00381c54a008040700940020102052014010050780192007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 286414685 1250 286413435 286413451
    0x41508010b03340f061e0504030818060d0518100e0a0b07051204030906090602160e0a0603020415080c1801030305070c03121119050604110d080a1206060801050f0405 73
    0x2c6054444d84004291301c2c05520020000d600c0400307142c10554448511105807440f030400ea86001d00d540c3c0c1c2c012130b60050600d0b80300b20000c100fa004009403501001c403407441c0d071480000c101d01d161205a40c3d950141000e600f209610a800f4012004501c40c400c018030f00312080010303d5041d4055603140c0307035031100a000c0300c10044280300200c0005e081500325801103110b922200e10b601d00f003907801041c0050b254050130856110111842c0807201e4420080c1c1903c59a8641076010350302d460100303015081981c0001d4003d80b610a060b103c40940c407035101c040d41d2005058500b41d9403100100880060308040300301c1490b40711401000002c4c0200000c002c20351040f0320040e501c0c1d40e2a202c3c500c0d4820603c41003030204801740004804804144501e00c0324034035400c011603d420350340d202d095449a00070b000400019440d04843e24030790f05c0d280300d4003003d640061240da5403400380c94000c14803103100b0110780302c00d410210003181d0701d40030703280d031505a8402601b180400d03015201008050113010700946 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 286415935 1250 286414685 286414783
    0x2040b0301021603020304081b061c060b070f0204050109050606030115121418060c090d0c0f03050703030801050307030b06010c031205070f02061620010209041508010b03 75
    0x440140329281c43c030304980681c025649441c0382070b030000d06225060b01c00840741c507000c004100c40c4e5039400c0c00755000f0803110324a08018039141c3c030303500005018a400040c00c01401046403003c0091100140032142d100360b40902c8141d0765903890805890b0155040c3c4d41c03001e03051005011802001130100603001c180e15200500e880440c041e0f100307c1e0a204a90600c203003800041011b0810f00b10fa20402c85081030004004600c4c0406408182d4001e000306544a2001500c41c8000c1c00a03c0c99400c02406000100c0445c96580740b4196641c0c85d000c2c80200c0c0810b0301c1000000d1580b41c00300381e00341200e07000315840c18556100e00045a01001500e001c034180401c4405d2006d20904078410548100605d45915960f003d00b400c029141050040002426403c460481164a0b9020460b400c408903000900540800500c1e4100e019016060019401c01d2500800d001d10540104101040312100b0000f0405035003200189900c41c0103900c000141d200b00c0d02c0d40c84450017580c1801a10040f1180d10709 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 286417185 1250 286415935 286415947
    0x6080f120c0a0204020d0b030c0d0302060114010504030210081f0f0504090311070b0d1d0c06030705070503030f0106090803070c03030e06090414070e010f12051905042f0a0302040b030102 82
    0x4d00301d1300042d807981455507884d0340c0c66640381010021501d1b8407800701c8504a035400315540080d6202e505004007501902c048098404603409241540c01071039000b008011100b8045000030403055040f00c030000d01c010000599031914900d03441c0c031800d0342d038200c09940045041c001404043d10940d101203042107a140c40003840e588090101e100034005541042d030344c8404c80c2e508002907640071000d80e0610f400d89448209170307038000540040a1241900c6030340e00d0350b0b0380201c10365aa0181d8100607001c0e000010400c01d80e1a03400703810303a041e6003003910754400064807800d000342d0f28000c490004102058410042c400310740650600daa809400a10061515109402007025180c0003035100d82c500c0c04030f43c180110701c1e420858040c02a40300b844c1aa1000c048040000d080a0641020081a80c1d0700c0021482c04e03841042002c0d982e41429809010358100303458040b45100e50200e000360030700340d885102c020001c4c1c1c0308084075000302c0040c0682da643e400c5400700b00050000c2a1001e902d03660820007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 286418435 1250 286417185 286417189
    0xb09130f0b060a0510030b21100c0c0c0e040b1605091e120a210207090c1e08161407060213030506040f0606151718070b0d06080f120c0a02 61
    0x2005171030705440c1e8005c00c600014405010401e5052403220003143d8000000361041c0d100010b0294800ba03c40d4008a0980c041d4001500d06a411800244c620f4509100110f0725110303442c24140194802c1c1506a9540c0c1c40301c00d8621481412114240061020001526603161039240321922001341c02012141014400014036604080d0480407104e40000310310405000080c0040480c654180c204c20b00c02d0061110001e48130388080c02458000c40d2382d440241d22451041d2000d10356484824040c0c01e5001d142c0401405000c0304403103854003480380b0340c2542541c1d0b12425003520320805006040c0c0c201356080e03455001a4002d0075401480034440350000004c03410800255001c0c0740949410f1907103901d0f5040c2072055840e0340e004484c040d00f443c20122481640302010044044111906503910345038009000003035001010001e20a04c14041c006c0303070582d4010300070504803800c80020070103666106085907d81c0014012500c1d01d8008905030081442841e000785138064001041c1d035405849a80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 286419685 1250 286418435 286418449
    0xc06030420060c0f2104051e1c12090807172803090e190203040f05070e0a0e060103020d02040c090f18050c07240906020d0b09130f0b060a05 62
    0x1400340740320751212406904110080c0f00385c140d01c1c102884d00c00e402c40e140400c00c007601c3c030951290354003034940c03560303008104d620f102c03400b400c0c54400074011144000c3c1c0c89140b0014200008007910031041d0000c41107401809100a00c08407a03400002c6d05200d0318020b45541d074070750880a038071200d0007120445400441c404181e181031900da141482664003040c24000c000c2320480d00712450711324020081c030151861140001d4000091446d000d682da40d114580b050702103010200051851052440c045403980c0e004c5031b0640b0604bc070410800c81ca40030421907540c5e580c028400603411150142c038007005404c05400084010070982061029150348180c40780003101240c0c4985000c0120445408072548540552a00004c0042200340ac0c0f240f99200d11001c00040081114001240501144004595001000d0490f00290211f4481d1101001c103405000d544c040c0320701c84c2078248000344056001229003056280c0005000c01107041c16a1103d0139a0805800307142c2c001c2c3c0000c000681680c07900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 286420935 1250 286419685 286419697
    0xa0c08010e061003031d12030c1f02070f0b070c05070602030a1202090906120106091118010c0302190c17032215140409020c03031005030c0603042006 66
    0x54000254000641c41c0182441ca000d800750203c00150001080401d80c40203030110000a0100c1c201c40344101d140002e02c101140b1122000b00c0d010206820745681c84c00305114412010504c49580c522051408001c00c82c803900300002c1c03089114600001c0461142c4992503072000c1345007840c403007440003a01ca01d89480510b500000040e0700004141c00010303881080c04001008509056040c628807800040403540c008284c2070142c0d00a200380c0e02011b1094120b41c0003001000000c00002d602d140022030542e2000d44020b041151fa8112421203521a078050058645c050380940031120095500310220701062100b560400b40c00c48000c1244015241041d02e1110b5800056641e0358018481105031100301107054084100101e0400000c1d1070203031503030403000d0306250401940074400c10a64085c01503401000805101080c1104030300c40001c020b40c0034102c203152250209a0315070400d07680344180820550000000c1c00854006010081c040071800d20b202031a034007044000010820741e4000b5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 286422185 1250 286420935 286420949
    0x606080a1a060d02011215080703020a08030406091e05090a0b090f04030203030a0207050709060f03150216060b01030207050a05010c11160b031812090a170615030a0c 73
    0x11501400422940321851055620249a4a1101d00c2d000000800c080d5500034081d0500002c0313010744002d001c0540c8000302c3c201000c09110010394030303003100035030316262400201d0040900ca9000303e091100003080d81c0440e001580c651030b81c0c60030a5000e488032481601102d0b8410900c134004280350342e405550030b109410306040064400112003c00540c600003600740d1095402200c07c0c000840e80c0481220340c0002c01580142e5246030314606140f6001d09980726445040c90448042180006100e00d8000c803402075003050181307065480500124031818074031400c0d00c54892a6407000410ba41c01041141038141001070078850326464650610200326001c481d540d43d070f81d0000c000c0ca40c00041d10200200907200815101005502c2e440d04d00c0217600565581030700c0400000c110810b000c6968034101001001c0e01d6202e445150256195003001a84520071215550b020a181c1d50718410108100ea9840040c40342c0d4468540b00701d501000c0307a50b840d030540600f03034508022a01c0040704500030080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 286423435 1250 286422185 286422193
    0x2061b03030f0a0506010206010501030513021c0506010b160318050306072706021020040303080403080708130308041509080301030b090f150702100606030506010f090602100506040207060608 84
    0x412690701e00b0b0804000d2400801d0b0b480d25007886041d0760300184050548000f82800202515040c0001c203551410b04802548102c41c3d81016841402951000b00c909103c1d0f01200d001e662030f04002062030040f07890741c40000790860b0b5030070040b03440750030152035007403c09481800d100c2d15031002c80d007003410444150010503881840001403510350250744c0c40707014441c44110541030421500035200d02c01d080c00c0001841e100d142c0c1d14100c01428900c0f08021603403280c2e03580d455a4a240252404500705d50603800700d800080020300d45ca0280d4069441207516403101441c180c040d0740c0a84113000702400540d014034600c448500b45102504c52200034500400740641c0725891460051040e041c010100c2c0710300c6d08002c0304101c510b00c00103030224050b07400414200580d55100b008a290045c4c1d00300b256909030034a4000a400c03034050b03001b00d000304007e82c2c1d86c2e40c03001a0040d003514050724600c19440141d0140d1700d54a2074030000d070301c20354118030001c00241c40c1031200c0c1c80d2601a0368580d0411156a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 286424685 1250 286423435 286423441
    0x40e0a0b0307061d010c1a041506092c011103130606050f010503010506160609060203070f0905010f03020c1903020348031201290c1902061b0303 64
    0x10701040507000600492400031404102e07011303c0038601d114020400d0601645554a1041011402c0050207400c59a10992940d10b003e081008000316054041c81c456071801001050007502405904480d0200d41480d40101c2c81c00c648048000ba80919103e1583d540d980007032001104140056014041e10b625644110200d81418421250351780c0c0810700c55007801319111101d036044401d40f4110b441c110380e619240e20000841c02c0c06003140707800041505203031442d241d007006929800745000d511a5541c00000380c264440555004040b80621030100721607525402d6000d10a400806451201809803011400300040c00b0320190000030b0100d001d1781021603201e034038103403007140034035607011751381010f01103a10820600c0c1d15641c0d04e141e1004500080034582501003010800c4540881c0081122000e075a503401e510600111a0740d550609030303054585000161a201080d01d00030701102c8060100c42c2e4044100c1e400c0c0320304881c0100e03004403042c01403480800a0090b0700b010000402c02550340d901e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 286425935 1250 286424685 286424689
    0x209030f0d090b04180225060501031a1312030608160603050601180308030c041d0109180b0f1302060706020405190305030703080711030d0b0f040902030a080f040e0a0b 74
    0x2036654200d1690040240000c001c1006112481750110000d840b00503a15140610050b42619140b10320804246941c1c02c9807042001560009048034024400c031501c040840110020400c030543d0880b102d035032003405144c0801d401108140c0c0d40c80080c00d00041040c0d03640a0281081440960110300001c118010400143c1501900e039201c1c0c0c092070488548251804100340c0c485d060b0201510906011000413442d00c4400111001b41008100000820340030840628488600f40511000d00303041c0200d003105108210500440f880c0c0c024041c0c0311507907460001e05036071140280ba48803016a984141005030320b44200030104a8041d100c05641c4500345028042c05c129880e210a100d00d4414004001041000c019502c0d0aa454a4885004c1c0c41d181c2c2d08440403050b55608904600002841082011172648414045401034038100e4079055a58108001c4610500700650581c2013403404d840016004002040d84140c0c0c4880c1500b85512072908210100301101c0402289903070380b0003d8424 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 286427185 1250 286425935 286425947
    0x20d0b031c0f02070504021c060503120d0f090204020a08011e0b030c16061505030c0906031c0507050a0c031406072319091a0a020706050306040209030f0d 68
    0x240150010048619100040a40d401c10105110200408084690049442407140c0d03801001c00500c03d43d01c1c1d1500d800c80080f078000c1003a1100e0f24610b41000003030a810f001c00c5055018100c000f40d0750402c0403030b80c1d800000c4d240d00206403819664580310000140da0318070140400d807070b459880c082c05605142c4204030b22845504110181001a4010043c0081d41011264401402c0c00c220f078480780c47c442c1d00c0180801071072000b0601410004105484c110180302c120440344200c1c1226100d01d10f000600c20b0698065941d42c0d010b80089004407484100c54810981100d442d00e400d41c500001c0d902c60300d082034102e22088a01e0320300d6582c00c0003400514000d29580f00c810201501c030034281030384054461403600320500ca8010407800240c0491405505807607182c0b074110982c2c4607444003440010175030750303242c00340700700810340f00841c10700c000c101e40d0688602c1d01040c0c00a00e04142001019244c581000344070070b40c095002c000001540c1c03018403500e6103900d080002005a00389415002e0b241c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 286428435 1250 286427185 286427201
    0xa11030a0908100b06070f02030c130e07060302040b0409050910060801050601141206120703060207110306070207030f080304080c030703090501030e010207030e21030c030d0b0406060503061207080f01020d 90
    0x203e500f0081e203007182e655080300b00ca4a07658058820310301e4031003e1001c01c2c00c200451216643c0a2182d021003120104960006200203800a065038070b0a5100c82040d01280214024000d1551040c002800340042c158007158002c00118201c84a00e0f030b0040601c0300b500d420360480c01c002d9440d201840030311350300160464104100c1e12642c605207401d01d0590364030301340c0061101d80309080c40010040410780c240815005160802000c1d56071307200ca42042c4416088591500c0c3c0030344180400100c0151000c1910400d03250b00c0412595900196140d00c9007541000d0420b6500c06002c010b4024506030410040141c0740c0300f5254903d8103860724001400310707050191840c0c182e0f40100002d10010b544500c2d030060741101107982c22100200c10402c4100c400b414840009180f0002807465807182000003c0c008002801c0014008040c000c0d080c4400d5031a60711448011903018400310345103160074039108030704140d40000c613051a0355486c8107514010000c0846c50059600044090514055000d0700341 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 286429685 1250 286428435 286428463
    0x81b010f050304030c020904140d1e0e03060c0a02011b11060a0203060a06110c0d2d03090e090c030d0f140f2b15060f02160b0a11030a0908 61
    0xb0440c5010740740601752000c1600300078482e000c0300c40000c040203640b0240c440c00f84554012101d1403000100050600f0000d552048a00c3c0c1030ad12030095801e1062640305001100a4090311858440c80d164200603000101007006554840c02180441c128050008503210740c82c0e0f407214034650038a41c2490a101300039055000403401003042018a0b107505240d00215092441c00c003040381303070605005060000301d200180d4412059100a81800b4810720720440ba18192181070010003101102c1e00800d2425580050100300c01c0306c0100240107a1450045c0e0001814040e191080004000a8100400c114103000030a080c003003000001c070340c0900150070812150105525207004101809000c0c003943c40c100c0144200c40e9000495000400300381d161000600f001072044044042d404558031055008200010340c18091800070144000b8100c0640305146045c4001c0318144000440d480e03000759541014401c071003421130018481000144029810303a0b6400480c1030a00d1071440c280306010140d02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 286430935 1250 286429685 286429687
    0xb0c0307120e190503090d111c0309140123180409051b01050c010e01050f07021504080d061802280504090209120604050606040b040c050403021009081b010f05 70
    0x9600000e00051030704021034070340b80c3d0001e03910380d500c0c001e480d500c0f03408410380d00044842c840408100c000202d440e28402c04407070080807480a05009001046400c10140029149500400800c1d2080b0605008190103150848030b801e411100c50010b011400c001c11115000003500307140741621004240d0500a085400384960a11500c42e00c2c5d482c03040c000180449a50b03c1030f4983c450f03001d5004c884011000c00d000340202680d080185008290880d1007640d4480540c000070308052020540090344081504000c41c1602c46840c0c45001d0f40000754074881082e60b074100400c0d640c2088100c100207000035040982d803091807142c0318501104816202c40d119210002c40f100b0150000103071401d03103020b5100140c403100440c002500d01007001c100741c0e00d14000c3c9410b000610401090070f41c03141c0307011380c0c0a1041a01d20743c00d22080f41d5400e16003d00158080c0810300045c13401c0032039101d034aa181d02d401a14180c403030303100a050483e0340d8030054029800d01161700c0196080140e9810100003400d1072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 286432185 1250 286430935 286430951
    0x603160501410901090e0412140c010e0109050706171315020403060b240703210c02030307080c040b030112030c0b0a060f09092307030b0c030712 64
    0x1902806120000c0c10300d1150811400442008031409060125004140148580c08590b1144019400380f102e550005206100125605003c00350590089500070910905400c040e20101c491821040243d61108010042112090001d0203042a0030180e0800015140c8540c60031a02e00140c83c3d000c481407004201c3d246480f071145590711036002400c500700e00346035005442d0500032841e40b2100560b9480c40071802101380681944800c1141400399502d50448205109115007944a03141001510700200035000000f8411400700450710451120004417042003940075040d54003440c40c1e0001680302100304004180e11084503a00b090205c12032314a454106034006925200c14016507400d0003445943c5010944202489002240c0002c1072014504040007080082d02c1e6a200348a032a10714000701094900d5588100341010341d0000250452540c0710301c805951540d41140b001240c026503000201040401c032859104440c058480d03552490001030180c03100e2031680456000c14034085007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 286433435 1250 286432185 286432187
    0x4050c120414030703080601030e0f070501030f110304030842190b0a0311090f12120703201b060f130305010207060e0a030509060313020603040b0603160501 69
    0x1121900c1880d403140310001d5540d4286a2a000300014081c481403000041d050141603000c40700d503000390300c240d80a100708030320f801d405641d410a1020351a0306400c140000c00596020368008070b4800362203100815070700b10080700441d107074004a90944c08109060100400450701080900c030740d0744a44138051800711580e24140c000304801e40b1000c8881d56032031301e001c2255139850030080c4808080340300c8008144c40d1740ca10040c1d50400d503082000b02e810702d004441d065488206a8500d40c80c0503200800056106040011850304140d0200240c0a0350f20307500c07036040c800001001c100d802601c0d86000301160303130390186a0a9001c09000340c2500070785542c4050300305c1501c222804220460b0000c1c0c4030545042103034141d225816142c501e50766901400000c0001c10b402520000303008072002c000036444003107402d07110000020002d001034820048009540383c2200515000700c0d003440c51031070802c61b560108810b5801a1011b880d140d0990080110714039041080061640c02c0420500d000e81c94000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 286434685 1250 286433435 286433437
    0x5060105010f030b0907021506010908102706050105090a0501061e0905100c05071e030303110d090b0928031119080a0305010e01050619200709060504050c 68
    0xc150400c2008411000002e100781c00c0002e8101d401002c001c1c1360f0506943c0a5a10000150000c0c48040c101e8005185580507110b40001c90380c5103409441402568803280300208070712906031442e08056015003600c070000e880300e42c082500c01c0704000b84d1941000200309001c40001c20901c2c140f4204801402869070013030f242d00b21070300220350708141c81400740302c2a101c14941c0d42005070850002d00d0b5004900b5030181d0030001050250301501d08550300d40605c0c0b42c070450500344110300c20010920400000e4800c0e884041d074031550303210090905400c54140c80540341000801da407030f00118414048114024020311003a4110187c803a08091015070030429690701030a0047c2c240b0440c1b01c00c0600303104091002104c0005c8890f6010000625441d1000d02c6030489140e40c07001030b241000114060f0721101d802410384400400d0b840c02c0500c4a800c0c011444010b05648042151450386c01010501d40b0300800301e1425000042c6c09c16a060058800c1202c1442c0d004d5841070781070406006811031944 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 286435935 1250 286434685 286434689
    0x11104061d09090721110108100e011203021e0706030e0c0303070501020316080603030904230403020309040f060e180708060916120203060a020d11040902030702150103050601 77
    0x2003801041070100c0c042005988901049241d0404019010054841d10108202055a0b142074580008481ea8002006100d512a00040c8617000c0c0400a01156020b40796055020902c0c1c04d2400211707458000800c0361100c20380c004200d69092403010010517405000314005807442d41502d44006800d401030ba5650545845008107265503202d8142c81940188101e040480e0090f040380d540d030368103140c0350b4002d42c8201c4440c00088690800441e5181c4548107444c09003e00600440c1402d440c4420000280701500001881e403070b060b100700b120301a5100b0310a201c0ea010f40c016544030401c101c1404243c0341d104803851091480c0190901c24045004130b05500801d5000d0b11110700d12402086c140382c03001a410001c01381c4038000800c00b41901c0010080a0086503c207001201d40c4d40e4072090051441c0184020741c19000200040d5594078a5805800d81402c0c0f0080420569060000c4040c15031154000300c104503000020402840c0d0100400e1421400c0d00b03908051561640d242d05403115018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 286437185 1250 286435935 286435937
    0x20a120b0a031e0303061710150504090b07080c0f0f0901050c150a0c0503060310050406150803130f050a0e06060918040203010c1d0d02030f0d050a1101110406 70
    0x500080d64040c0c4070a9020303806541e0200702003801845030420002c015501e00000c8002904081703010407030702101c0390342c075810050180003403401c54904034040000e4003520755940840e00c1640c0000960b03603210b000e0040b445018000d6042c190400d120010300c075210003440c04100d600100301c4518219000021900003000c01740040b43c4030b540c41d4004031190700c80c2424240c551300c650204a1040800c0d144080d00445a8400402c0020031600068403640000c440d056455007240229850546c155040340b030b40700f803180000003803482c0050420b20442c2416005079003141e00c0402d03010034840c03454603200701a010030b582c80101903240c02c0029915100034011400703000e1a0070301007141910b50302e042c1c4118030401003c610421b000c030400c244010324221400d074829800c0c90309500e5080e00441c5640300303086488441c0d01d01080e038442484100002190126010710810208050800c0f044c0305144410100b59103042e0364119013400201078854003141c01910340d14142c08a00b840c2c13200002c481c125061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 286438435 1250 286437185 286437191
    0x201062304020d020c1b09040305030a242c011413140a1b0807080a020c07080f0d02060708010b040303121d2104030507090509030d021801090603020a12 67
    0x240000c64040c0c016540d48032a041d001007420a09407001050030342c0301d12059610780011b00004010020b1244041d14054003043d03040000c00c0342192150400354490b0f0990400c85030320340381281040001700495005552241200001041c81556040c105140c000c01e004082510b504010940caa15038500041d503100b100b081e248002c1d010110b0300724042c5446804450792240c070b0081c0001010f01003c048281480c0c550650448072a8001c1003d5400741c07aa0340c0e100c41c0b5550794001d040000307604c03c40e41481c1c00d2051200010b48102c0400405e410030380c1d0345010703207070703118040c04080d150110150560f0b05000c9680d00511210720010709480469406240400782d0100840c0c00c03c0082981d07004200c1c550112456518a40e103000408110740c00002150075008003c402d1001e4035401540401001500a414200683d0380e0642120390010040c5069031f2801208129a0041b43e10600c1d04003041c501a401c0c4403031035078000007448010a04e5090540c6040da1098004040983c500e00d2000d030301c2c2e9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 286439685 1250 286438435 286438499
    0x601060c021c030915030515130b0901031506060906170a0e151503070f09020a02031b0106050405010501030b01020d081528080a0512090d121d01020106 67
    0x9904889414140d0b40c140305909041554140145071a0f594080c8110301c0c000b200d10102e955100b0b00c5000d102e43e50701d5900d01a0300104c10300300001040a0216a00d00c80c0d140c10141d8000da545140b854000c5105450007003400054a00300419134241e40d12440c10b01c00040400c00c00260410070301801d100c4041c3c070501d082d07510442450000c2041c001340442c01e1086030820012a403603541990b0107124001d01e0001201050420551303220741c28000c101b481c0c0031311801040400540c1d006821805160b00690307042c0058011114051050000410300b0341e0b458803820070450429201304d6001d0102841c090080051581c0040d5841080b00c451408000500d00029034501084807510b418640041496008880c0d000e0302403854030440052040c40d0304150000201c041d400602490320350303800400350003000c100852500c0250082204150004440442040001d8103004141c00784030180c3c40350440b035140c0207170030404030842602060640e032400409010f6105110508411681c600b02c0340d1700001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 286440935 1250 286439685 286439689
    0xe0613090f080a0f0207090c02030d110f070309030c080a1e1a1305191a0702010b0d0c0e1311040903050729240108070216030b010f05040e0601060c02 66
    0x901c0000c01420305a80800d0700300c00c0c20b601c0304040e000c280031a0308440b02140c4030040d00044030060b040304409079004004000307900b04d40d90000c000c1404250721490400d0340d20841c0e0b005a601020007100090b290500a000300808015510f014007070f9003000300300d0001c60707580d07010380345d061060507203600310300b42010404001d0290621800500c01d0781d009001401c003040e5510420704e040ca4212002d005041c10058203645c0034140395035298100c500d403401c50347e2410124000c0000502140115502c95404100a032540058a00000c0c071800c2c002d1482c910345042501000030142c071000500304000400c00114080d5070000c40411001c0b180064250340e01c5c903050f80c4511541400501120640b500e000e5420303643d0854008005070045100540e0380c03a0010306100350500d6a480c80e03981038070b030300821295105203807244d804440fa0049603144080d1a078000051151039208507032141c0d44a0051180141c0d00313040344010003060b14203100e0761b08409052600d5840501450702000404003c941c259 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 286442185 1250 286440935 286440953
    0x602060c091e0f131a120604060504170703021b09070210021602090903040608070503160c03050409020705060105041a03060402062a01200403021e011215030204060e061309 76
    0x1c0c01004104d860780141d00c0399600058514907810418078000c440030b02080c0e0426002000840000d500600059659036a03448002c0001030420347d840500840500c2e1010024001480902d0180e00200404c01c1582c2d070300c882c0074680f140d0483c050200e0f0800c0c08012a00011a6440d0a00003a4007580760303418080d00c00e141d28840400690300c081000300388002c8290203c000c0055400550700c40d070042e070718208141c03041c1c8015035070002d403c4a000000c07442c40c5d1042c0512100781e44286003079490580d40305103a100741d0b00000c02c02c0c1c03501d80005004205903d0306106071200580786c1c1d013219940c2d80203003001a880e011700a1000e4020b11001030000004441d9801e21240007981c00c030f444190321b135583c000314000c00c102e00228010f4600d400e43c00e420705691405640c2144d60062650b01daa02c2c0071240e80c3c50104504000c2d0307050120303400d4400c07048045806190440c00512201482040c51070040009031422940183e458800c080140315494540e1408045a41008400444c1c2c08002d0b00c0c045d411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 286443435 1250 286442185 286442209
    0x4030201020c0a0609150203010e0a0903051c0b040510120602030a1b1713081b100c0c02091b040506070503070602040b0405181017030c0d090602060c091e 68
    0x55000c1c00d0f00110400c901a401a95124010812201d205141c3c20300d407012440203000d000741007e40100000c1c0001e426400038642c0d5403080c6020750505030310b240e4a21051450700040c110075a103c0d401244a405d180c40790540c4545050000300b100c0d8035000304441407000c1d100e07020b4241600000041c43e0076095810a850741c46a80c903a04807030100d9000018842c1d140c500e9045403000e101d0012411903c0e00c2c8410300c04c441d8010030071501c0c210f160310900011080b43c07292003213180a80000d4003114031103446000000303182c3d912456103940003441040304000004200c1321220032024840c4c50018500c0059030240c1c1c030180c035555500d4000341803461445c051800010003a40c0009800b0402c0011400900308132072059070310380803072101511030108481080300c9821015004210800640c03000940400d0821480d5040d01c3c6021084c0c8080c40c100171540d40800301044402c81c04021040c0d040020356809444454410b040c444000005814010a05008100341140d0701c140d04865547e00b901e82a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 286444685 1250 286443435 286443457
    0x316030605030f010203040506130c050108040222020408120f0a0c030516060b12030901020d05090402040e0f0402031c17060402120a0c0f020a171e03091501090915050403020102 78
    0x80c20140d004010344c080d50044900302c806024040120b010b500d504500000020303440004c503071080d81440011105000700078000e13a407004462a89000300a04443d401014510350030300580d45038180010f1a01d040b06040c0c0c02c44021200300802030305030f00907005640e0003003035600e0030b124044039a04044440e800b9a4100805000c0300075201c03010003a031540142e49844c2d041c0e45855030240c45042541d02c07030155049150151f000324400c051100c0c860001441e6600e0001d01c014200340c1c0790201e000c050740003210707220302d208100400d000642c6020408a40a020041c24000350742c2410800201416024180850a128648003094180d41c0390b4040d1079204a0744024102c107860901c410101800c0054031450104944040200351a4808501164181d4000301c10201000d543c40b80e10390039038410500407030300a12400c00c03400c0b0551880015400703a188400102600c000041c0b2268602a06a0160f00e001d8500903038000040d154003038005c2d6003840310f41c00080594a50909070302a121b0740005d50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 286445935 1250 286444685 286444693
    0xb061f090911030c0307120e0d0305040605060609030709090303180f02010e06030705041a090a1d101d0612010510030c0902090a170309030706090806100b031603060503 74
    0x2040040d40402180100c40d0650014001c8070341190101c0c2c214481034442c000f480b40c00300700241c661406265a420740901e40368001039175601006085060101e60030384140066154001c3c030062050034000c03503810a508441c01440e12052000180d9110800e1148054441d103c07c102018503000c1d60200d400700340050900504105180b41a0880c244424400c03400300b14807942d20f11203800c0c05010340303105000b00e4a481e85800d080000d480c40000c0386220a80280702c0821003090b150700c46150b6280200032842007120126a00c1c00e2450f0250002440c54103141440e036010000d015291401030030f49420741da001001512014081400c1d2242854100d055600f0301c01400841802d608080003220301402c2d4120003d03448010300400d03841012401c0d940403062040501012107903007007c2d2140443c80084a25064404000c282442c2196004101098602d101007100d20028008298800c0548030350240660030195200200d000140c00201048020700403111241d000c3d1340440c0103001700504032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 286447185 1250 286445935 286445989
    0x6012003091e091b0414190f24020a080319050c0901020c01030203040b072105070201060f09020703020a060f06120f020117010e07030504170c0f120a05070b06 70
    0x5180341c80e90b0608440d00500e0418002100d021000190700180076100903584c0c42d0603d0301c4d030b41c81403d1850014140d070112014041384039921000e0482001080115481e0182c5464422143c0010480185102d015181c204000a00741e5002c00c0d100c1c100c0340c3c0483c100d91262036040326890192003001c11030279800e19110600460308124006031441d190240d080300c0d410300140c40114142e01064074000d00c0052002c020a44580c0900240e00000d80c0084c06180400203198101041da003058903940d016175500e0701c0c00d00c030b01011203200002502081a09501d4940d2a58009586004002028084556070b10200f61482011f8010380028204100307016400840b03403c010051510150089003c1901900d14803804041228020b04880130025540e42c82d603a100004d5020381401001115550145012540c41c00e40034030180c41b0740c840c8030004014032034139401c8503403034510506480140e0304020700c890625540e1020480b14a140e10400c1d0b41c09039210309000c10a650f8480c02907450241e5030b40d884c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 286448435 1250 286447185 286447219
    0xb09060f0c16140715110309090403050702060721111005060303092214010e0a09020a260d02060903041710050c0c1b0f01200609030703090503060601200309 69
    0x141c04251170030000100e00b010354031541550b0407402c2034506903042d0014850912a0325004040f80d078003500a04140d45400e40d16400502c15a111003001c81e281400c54280d00c100c0e9060b0800b6140440c0703241050050400d4103404181e0350001d140251100c0741d100d20000f01552800e1098442c254401b90544040c1001940c1080a0110303001243c00391300c4c90020078195000c1c1400440e4103c0e0a440762802c12600c454007201c018012006059821a44a0b18002115211030f441d908900005150110b0700760f40c0340c9c0d4814104a0311880ca032003198005030610220100c08400c45044440005000c90404207026040f400c0501c0ca24122420919202c200010180b000000f443d0f00c801d1442905e0f80010b034014040ca02c1c1c1c2c0c00503041c1e904030203401e00c24915540201200025004004228402072105404891800d24100d6404400350400300398501003582108040000d480c00b2406005145001e40009000c03141480300c5c0742c40214410100b10318031000b40111303094150f000e81040720502003444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 286449685 1250 286448435 286448443
    0x60507050c12090a120c0f1404050a06030203120a0309060f02030912040602070e04020609030601180e0a050d140c0102071b050603070e1207080f0601030b09060f0c1614 74
    0x200281800b982110884400314842202c0c1c03503610050209643d5818589104450185020121100b4030803910118102005040322001002d400030000000c080301010311050b58030141c8031805681c00e0000c1031006980204d042c40004040351000c2e51038600b030b014100c001e086100d002401440c58010b00416505141d00194820200b54080310462851482c0300070f214030803882020010307000b02c5c0080c000703d0320400540e90098002030005007001c284000090910000380d00c00c03400d8039101c101102541565000e0340302c640d500c14015000d00d1140e9110180c8998040c10302000704081e040c0f10302140c11800007514000f8904034001c540b83c0040f032a010240030741200c030b9044892040d050000d01842c205046a00c9143c9035690007048040a0003071000000750708105180742e0160302c00200d22280d0401c2003100885640e00100501d5141d03081c10480f40101a0101c10b2941041040203290200c226116801040c100380e080da0304c8034100c06c48040c0800401000340406000c1c0134556070594006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 286450935 1250 286449685 286449697
    0x21c0605030c03280303021b0a03080109090b040206030a02041205030409060906080d030c050d1e0e03070201050708161202010c02070512071e0e3306040e09070306050705 75
    0x7408546840c10780508144e51103000f1520110081c3c00b50002c60800200c41c0c0610743c1451203800c0140c144402d104503c1c40841004071749644960010b841d160500d41d0080040340107056994040214240c3d89d02c4820000b030300104068000c0710000086203030080540d0454009105042440448880c81c3c0740280d02c2c1d80c071078807502101d0b40c00c00038003080d89802c500c9840101da80540090146410700e4200354090404440c001003809818005001410402d0140507603c041c0b500100c0c0f640304682c00d9080031104841081c0000380c0c0203001c5100140d80080031202042c0d00180c1194480b00d44603400b400c401c86005000b05182e400510442d40d50360150800c0e4600300803502607900254684007800760404400b84590007030703800301104105902c03105248004004171400e8103c0b2031a16405c1c1d54620713076401d840300c84e41411a442045095026481c0c0004411886002c0c88020001c40000030154000c0b400b42c0e49050400c2c001240d01e21078200b124100555014105100c6071503c4040a40305401c90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 286452185 1250 286450935 286450939
    0x1804110c030304052b09121b0602012f091306050303180907030b0f0d0c050a06050406110d0c20030d080a0b01050c1e030705070e0a0c0507020312090301021c0605 71
    0xb9294484503118103001d0210700710180d544d6115054900503113000300d00c074140808c1d9100418080801c0454031005408405002d00345c00110b0703103182c40074038404c00000858129002c0d0b003802502c1554808242c00300c850540f17007260030b042100380361400d95000b07120581c001c0394035101c0042c0c1c588032105601070300015610704550b10242c955840c20306806440d80c544645a0142d00000783d401a407034441e0780848411b010720b200c0d030003540d16900404c42d00f0303080b50012070110740301180c20002c069200e810712a140000002902521340ba03d000034103009007103072008056498455220424a6503184585081e990050131102449000700d0090803411382a220310580302e0034403407442c0042d405401100c1503649034000078000e00401c2c03000007400b504840415a940e000400c841c102052040082a000c4d04460194600f42c0c205050807804540d52000d43c02c051000900038400580c0c0c000c60f104030b0711644207500c180da5811a2000a0080c480c0c1548401000c2c02c00e0f13060f110401c22a840b0105075841 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 286453435 1250 286452185 286452223
    0x506030d0333240914150309010b03010905060108240601200102130e130b150a0e0712050a181203060f0b0c0f01090206160305041205060f0109021804110c03030405 72
    0x31011280100a0203201e0310740c00c1250a003004100e01b0700c0784011940040004d00000d00401d044000030f080d281e40307038000d8070958014801404030752002c2c4034260030f60403406102350500d503a00da104032401e2401444203043c01020851083c0d81031445c810010b448005000071984c0b4156102d0586840d01c003400740d98078407120400011122301c040b4011501c29500b24a03000c145588004044120b0fa03511074040c0c2d00403080c01800900401106451806469035882d55418500629902c10071100300034584c0d074000d401c000c0246441c203214070074001b00a0b00a480380808680a440c160040e00d56075010551030030400000003080694030015003032081c0411300391515035441c0742d00d1300c1c20303030b03a00286c00382d8003800400140c01c40d58aa9850b20060368843c1c10070382c6c2000d540750001601c2c280c1071001030b41c80d5004442045140b20a88540d240500b1031050110f0611080312108040001d1161130580159504c0491351840200341054400000c0300754100c03540d07850b040c0790840c0c0310190082e1000803400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 286454685 1250 286453435 286453439
    0x3010b030709350304080303012c010501090303030c0e0a080a0201020c18010e04060902060f031806040507230d051c11030a0302030a1e0506030d03332409 68
    0x40415590b01c41800f040001c0651034580000051200038034600c42e6901e4881040006904841400518000c141c2d0f40585010f080d85040000070b40303038601040d210740710642001031280f6a0001d54070390580e0f806140c0040c0203210b000d400e03074041c0d180310702e2941d100f985031400242040300026141d018030300c00e03030948545500c03800502582d6820078070342500201d00d41c0014040302c1c0b6000c1e041c56015004440c0414580202c1d00030034115803040080d640c11520000800c8242217007121000505051507000b46044e203000e13107601e9101c60080c01072040d600f600c404655110a030360540390059100c02084508000b007c0c2c1790003607540559030001c4e0305040800c11041d14540c040d80f0388041d2281458061450044c10f008118020351001300b100c00309583d606030b281c030381c1d20240014019031600303840001814240442010f02e40b10a05112a0401d42404454039480e0655151070b0300d41441c035070142441d072800c16180c0034114410381080c41b54500261441a69030300e2a0b408030710074440b80d01d0344c0210725 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 286455935 1250 286454685 286454699
    0x6080f07060e06180a030f0b060a0605030609190915090c06021c030b01200a03031a06040e0709050303030702100c0311030f0402012105010503010b01021908070c0b03010b030709 78
    0x2104071060254003450a11030040c000707901840d030408803e0000c1010034050741baa078481907540500758003682d1503942c1c442000f5080c101803107540003510307490600d1401d61401400080ca0307103200820301c1d01c6031a010400226a1000c40d04407818441d40410b41e091120601070445000b0001090142d4200c1041e04000407035034004144451030400c491007009101615020540140040e815014100310100d0145104220f01e8410780c42e81e603403032001810200381c607410000c05503210f40c05980032003441c3c40041c101756900c00046900301c420010030524541e0f00ca91b000d841130742003644401c1d01030000100b04440580c2c0800d00d41071a05041c0f4080284030303054070084080f030b440308070b42d500072500420210301042200403049910901c14074040140031411500008880940ca03001e00b0144d0b00e800051000380341c01c2c041c1c0b280921080c0f00800101908141d401e00342c8600410240c91524001040018001140c400344050b203004121183d80307503910030540400340d004071428800240580c001103030381 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 286457185 1250 286455935 286455947
    0xe0c04060b0327060c0c19060e060f0709091104030605040305031b040302062a0706020106050405010b0c03030705180631080309060d09060510030c0f0501080a020708090406080f0706 80
    0x5543c40c0302c01071416a0b21940c10107095480f0442c81d040c107109041400d0304007454900840e44080c031440c40415240984501140b40200192682c170019080c0300800c01641e038444a040c048640814000c503071610401c152066610507900054902401c01c4100018190004019806050369013220720781d8040402540743386001e09d0000951000081003e101c0c41100003d644100c00300c0078070707132a0320101100c241070303d42001135100501507511060100850324140c4180c5005007005034040303140c60442d403209902d03403100500400a10101003400b82010820080680c2050006030486070745074030488115013444d0701140c964409000e4107103082c203583c009400300c0701101c91840042d410314000c9020051280c0003810581d5039140d4510503040810303e00c0c01824001c06c80c9000350b82c1407030704508040c60030340031681010314811a5200c0070455a40c1c418002c41d80000075540050b20703000e5600d04906240f240180c0c007680b0a041c800040744550000c0341c6105040e401c9821a02c419990754826121 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 286458435 1250 286457185 286457251
    0xb0304030e0103020a030e060f0a0f020301050f270a060e0903090f0108130516060311040b090d020d02060a02010501060206071106010b0304020a0e010e2d0a0e0c04060b03 75
    0x41085081c84041d50080e006003090070040e040110309009a024040d02e00502110701002054082050100844142c0700300c07011180f071024250328641c180004a4141101d0032754140c040c3c0c2d4580141c10300c5ca50410351000d41d00c00d46811405560400850701d81c0036000a001c1c0e6081e503640c650100304030341c10000480d900c841c409444101d0040e041001918000c5000f403882c0303e2560420034000000d002404601c16030b0f09500202030b0100c1c00c14800800312107000000a007072800802080c0489100c4005881801c802118105203440d031620102d40c560002070802900240d02041c1c6240141d019000141685c00303c2d421140340f55110071040352003002820b0400e030542c01070300c0107002c84040d802c01180d010740042c2805042d03664030340b1207000e083c001341e000b1580719803202e060103c81324034550503a1407051843c01620400300c07583d116184c41a07018107403040c03031991120000c030060410300045240d081c005004001c11681c1707a06002c060761088818182c0242586080174400d00741090b0204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 286459685 1250 286458435 286458437
    0x40302100c03081b190908071d0f060102030f0c030909070e0d03110307080a020a120201090803062403150405060a030f02120715050a12111e09090a060f0b030403 71
    0xd15900e0311001e419030079000c0481092980405c0051300c600740c40303c0e080520700420729521080407a00d801d80e0a805d2031000e4000c00380302c8070003211480303240c101c104041d504000720116049540e00c81c5401070385140b1a410305a50004000308049180b10404806481d8100c01034800b07d2055035a40c0040b030301c01101c441c9050740405040140c20100e4490040b0000205c010b00417680350110703a407910885608400e401c00c00503400708191404010301d440a102c14800c25000a0002000e561b40b4407556010040015010300c220041001494400303403020074040944618117a030740e0524215510040b40a0707003041d405070f070038000450417078201b49001c9401c40740c020303480c850803503a01e5007004890310f0404c14142652055001c003180e407540c0e445100340c0440458580c0e03560f85d2184000500b050200c4450a11903503c0c1007090078003455040219040759008074080e8004500c0b0340640003850140d40e40083e005181c80e81002110b1b10780368441300640d02c1074002d0503000c690703840d4006050322007250020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 286460935 1250 286459685 286459697
    0xe0a0302100b030304090504082808061219030302090f0118090b0105040b280c110111123103050c0607020d020d060902040f140613020c0304060302040302100c03 71
    0x40c030244a0790380039404070100101642d00e029035031050081a14001d030f8054818440c00202c03003208149a41211002c5d0904800f41c5d20b0307030303000c0c50405882800010724550007074050b06016040c80d0020700c40109103c0345029144410641400c009000390019480e840c0201c08155100c1d4156000c1d141c1d60480c0410612000d41c00ca080ca01242c003d8000e03285032a0610500707010105101e02000d0240001401641641c20300141010040b031890101215500c1440181a41400071401110100f43c0b07915080c00c01d076200266900d110362402c801c64029682e422400320b1300006200d201035140b030036908460122000040d03411441200002d032440024200d600000a80580342040405004003d0000f8150703070140d0440c1d0003180d5a07540c1c07820200c49071681c0300c058030f0441c83c0603c50003c0301c29a20300c6c00c10042d0784018480b405000c000e0074035449080d88049184c1080c0290701140d4068690700144c0b521540d0380c90029000e500503020491068070313880d65622000c0c1c49403580100341a055502c00b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 286462185 1250 286460935 286460953
    0xa08010207120e01050f040312030e0d02010504060c0507081b030d02040e040c06050f120717040f1b080c1309050a05030d0f0b0904020d06060f060e0306060603090c19030f1202010e0a0302 82
    0x100084800f1160f49c01c203050710f61590141c80401441400c2c40100c4a07000480c6510705450058100c5200c00140d40c28010140411070214004100341c804100d10400d507005102c10046c200d41c654084d000003180282e000142c0861101d492a05043c000e51181e010300c081d058444e0001c1d40c1502a411861490300e0301400b0a20228080f816200e0b0440e41c6070030032000c410700da051002a00503003110140c699000f0080c04d0b408010030904c5003441d8525100d044a43c00c0e007032070400394403113101124652040500c2408486051082d5005022695001d401c8441107005882e010303403250408401100c14900d42807880c61021042d004046045100901d03500c01e59a40307074208121400015019252150380d0b44002c20024584580403010304900c1c0ca480d241c9034078050815280000040201d40514814410301184c48000075075204036a9088880d0440b001580318140d0425085900107000071191820b10000d0103001014003607000e07019070003031004003232200800c3e9440d0f900810050042e4071041803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 286463435 1250 286462185 286462193
    0xc100507020a0b070c1a01060f09081c030b030601060f12020403020906060304080d0f1d01090b07030207020d06060b030a06080604030207060807050408010e0102211902090a08010207120e01050f0403 87
    0x1644e100740f10342000f580142c403607181d100701640903034020404001c030f600043c00384540101d8246061502440c050100d24100100152907419800121007102e611502c4d8017001070090300003070400200601103c2c000c0d0b948803c024040c3c0c0c800800d580c085241400c0c0d1380c4051b480307030084806407038014181200d10b0b281d8005000d0141e200500680c0c000c0c13020b0110044611150041062020704040082070030885000303c0301c03642d0308120341842507078540301540000a02c001595903000685040c0103885000c01d0010990103040c0c028010216884c00c000840c91480c4900a140100140e0350100401a12241c3c1c40d580c2d54010743c5c0140140e40512420462a03110743c0c01c80e680611a032402ca418240d950514500303440d48441e081e140d603500410385c01002c6100001030758000038490300c0c03111a4184542944d070381501500d1403c801030b40000746000981c50316001d4500a160450013196960210b003000303040c03103103000460b40004000044800c1198420026076141c0c0340800a0a4070341403550351 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 286464685 1250 286463435 286463453
    0x1b030402100e090702010b010e0301092d0206030901090623190e1b030d02010b1c050703020a06031e05071709010b0a0305250f0e04060b0603010801020c100507020a 72
    0x1c05904004200e00c403850161240e00080d801041c11343c001042451a920002d0020389414034414041e03858081041d02181000d210024031400200045102d0400c1c0c0e1001c00c000411170101075042180013091000c0ca560550041000e140521400c000900741c800300140081e944142c81950000d071000482d48442000044554210b460140043c00c600003c41183c1400c62240442e4501e10a0710b00c00344081c182413111014110452000300290f1411400080311481e072000b0140d09110100e01c4c41c0200301c81040f00a01664000f0900c8905c1a81d8020090182c00d121000703c1c6007280708000b401c185500c41c011580244040d8540488107106540c0540b4200002000c0020039902c3d540e82030304546502120102860250b40a0000f402d13f40b52941c0c90528450001550b00f00448003c00c001008903e440050703e0800c0090046612030f400c099000e80030b14912158000000400080c4003481513000300368460540b0181d41d10844040202c40c215901150a400540c12a656000c00203601e14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 286465935 1250 286464685 286464709
    0x712120e040603170d0b100f05070303090803190c2c190b130e01050d02040905010e0d09211a09030d050f06010e0f10030c0c06090602070303051b030402 67
    0x2400028002d40d0302c0e103810312014400fa040c0d00c164000020481400c07600c5005020300c0c02400d0b1141c8020911300345008000d854407520300b4040040108881c002c040c803030b4018030005070f0090b01454403030a04402d155034040031102400580c61a0131414046107016224901740290780d023801d88081000400416150b0800c1200c10340c2c07208512013520814078a11030f20101810000c0711140d1501440c0002949000007900800b8000c41040010030080c2c0c8c91805840080f0790544002c40c070210301c0c1c03605502400c0c0921001c4507602500508c9100140d00c451510103c5600e14000b01d0319040441028050700c0d182640036214101440502c01250308080c025074004941e081140c0c41c28100c0002101280e60a0340c0f400507085142060180a43e03001d035103444c031920101c889a040ba02c1140015103100c000c2c0c0c5041040c56242c02d0001d103040e006211515086401280520030b69009241c804000c1d8010407003140420700d810701044074850000c0c0010800030704020100e1035500c95400f049440710300d031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 286467185 1250 286465935 286465939
    0x5010f0e100b1e0f0901030b120a0f0c1706250818070f030f1203020a0f0c020f1801030b0a090c211e060507030e07050906150304050f0712120e 63
    0x144602c50203c1d40500240441200701401a44862401c40010103a85200c01401d1203004601d002c4d040a000200d03e00501952018031307210406014500f415903c80640d00c03c2245011601202c1c21309600421041d21075081a940021546403c02a00f00c464a4000c0b1801c00159036500003960b860401c2948501d1200000031603001981d04c1d06126040882c94100710746112000000317204100b03140d881c40e0060303040d1342000d5040842400c002072581290104803010400302e4444031096499211007010101c0300036120940591040e03148010300310080c4001c88849032407500203202002c0d11b208540705107031f0040f148004c091a0542110030a24000260000c0402120400b000207000b40c0c5442e0700081e0404411401c558541460b80880e00010b050307605050034030b04144220117010869105a45041311565104e4540c007001c6444110390765441c464035140001804140240010b1030243c42d40f42d102160f91041e01c0d02c2400c0c03e040c4040000a14111000c0040d40c51580520740c02c011000300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 286468435 1250 286467185 286467217
    0x270303050313120c05010e0a030f0e0d0506240301110a140d05070c110301061410050c01050c0301030203071707060503222607080403020f0d0c060305010f0e100b 71
    0xe440c0d00900841c100341c540702040200500c401044000c0c020181f100300741d2800b401c0450a00e841c060318070188644104100260b91040304503d50f1030f854203c541711b4120085442514000300035820210103030000d1814a205484220321529050148a0b4100c0d200f1080d1418080b02040644075041c0286842081d20802c0c030901c14a01d820b80b041c144210450b5550681518103070409141c00e9041c0f44080b27000e641001c100b80a2900e0405142c40003e10540d6105403400101000302d42c17500402c83c80b0203c40d400c2400784040f00600710061410303640220b0558585990302d55001e900469946031044403a00121010002c05010700c000e10750144c9004901106402d1005002800c2080c0300d0044901c150342a01c3c50314000c24a0f03584a802c000c04400c11864008151200c5c50359000d1403000a1041c5405202c03824170ba1101c0e10800300700c0707901407110700c1c0e40750710b440d40503014200902400071501d20010740000d04101600005004075151004007000c2c5050140c81138a9500150000c0d1016807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 286469685 1250 286468435 286468471
    0x120507030501090308010f3201050f16060b03030c0604080d0b0316080c01210c210f0b0d0f12110d02060609060f0102330a0c2703030503 60
    0x140038003440c1c10b0f8511a0b580d2101560600f614410540c5007070304000b200d9004100031005d409500841a102000140d000202c403004000040700c0c144124444442c0401e408035981140000e00040d00420358030540080c42091054401d05a690095500c140d2043d481000810042800b4000916032007a11342c4003c5244d42c00d0720046894400408800004240d4440b0200100c040a001400c20140309185c40b40c40700c004091001003014422400c028001d62715480b44c24158003032040035840300c3d9440c2508000e158007410b07000c018602c42c00819500d40c1000849006498404440c0c00015030006500f00d440c007080d2a9038031481c40459004090003032400c002404000204000803091b10540d0040c403003445c1c1801070096020f806804140122200c51907000107130780108000c0211580910180425005050701b00c8203c0380300c8103880401200501400101012500450784840181d00c400e0f0410030180074000340d0315000c03200c0d0110321844102c11320001c1d10550003150082940c10800304440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 286470935 1250 286469685 286469693
    0x2040302040c0f17011214211207030c05160204111b070b0f0a051e040e0915160c06110c0601032306191e05010915080712050703 57
    0x24900360b1101011a40c640c0100b402103a0052003104181304019004a25500d071407080514100200c200410785001d0121071645540c0401c8002400d0303401a2500c03001845140e800c1c0c1141e81f0a65820720342e412100005910325001e40100c1c0019521552901d01d8401ca444c000d995444040b0001c1303a00a80300c11060100824003009840035025903840104581030a140701e44c5410325590000c0340c64141804540070344400c00c4242c1c0c4c408170740ca0034095a03c0b001c140300e40010154001c00c100c803900000c1008184c107a000c649640c40b94a000088542a6101580300c0c0580c010840c2d888415103440d82c0002c140314840d40f0038900032885070f1008a4540f5940b80c082045412840400b002a4403e000410038006855a1140c8825112800540726503a00c8805503c5401c01840c02201d041442d14881c854045a44013030340c400044450f1500d42c81441d1819009040207210720300c40d031410706090b0b01401a141c2c8920084541590080c4a254501920004070359510b00c01a1202d004000f0000046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 286472185 1250 286470935 286470941
    0x203010207060f0e0106050a0e0a0b0a081507030608030712110c040501030812070c050a0b0c070206070c0602071d0f06040e0706050316092702040b04060206010306060e0c030705030a0204030204 85
    0x48440c641c0201e01d514460341c013607003140c00030f0f803003117115151130003080204010b0164920f4000102c45004181e0305501c102160243c0c00b66031064940c1d2041c01c1001c0544940c0340c03480b5000700c0b070a42d0280a100d40e01c24002d942d90040c5c1c003000d0031084900d5062150240142101205820070209403003590702c072100010100c03a03090380291401d110001d12a550020b2194007150700000905004000107690749940d5910800218000c1c003000644012801003402c0f40c00391090f0960052000d0f5030380400d480e016595102070300c102c101600c2154404038250550829100b0048880e00e218a0955100040b4204280c1c0140a03150842c2e1b0340e0030815284001030000d940500106d071105070352800c0c095002207012004031f010100b0022005d1081c03204180c44e0002c001000304e078010420640c02e011901c0802441642d020f4122101e0016001079030503000324074503040703c0c09040d0400200b03607a410090000b010031100900074107020030005030380b0380c0100c0c061600403401c1040142015161350200d011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 286473435 1250 286472185 286472201
    0xf0111010608031b0d02070b0304060905120d1a010503130605060d06061508060105030105060301030f03200c010e03061513020c0d17060f0f0f01031407200c010207030f020301020706 80
    0x4034051100c1504401504019039545045c40e4401800058070305542c0c410b850002400c000c00040d02d4200034000d0241c204850201c0d109500c2c1d04c0340c2d0f102d4521107494002e10700c0c1d10312000c05540e0714040f0400340d8026400d0300d20a400040500000100959500b401041e000b48016844904100c1c1c4070003190700751107403101030911150940003a10601c00041c0c04620000c22a5041050405c01800142c5400d0300303403811280d1228560000240c1483e007503440303081d4292203000d031310840b09645c020980c0021741c1c01001075017a00c031000201c9101d410f068558100325044440401c031802006620305000c2151405d80c05040340040c20f0a030008412414640d50000341000114001992034003142d00c00c4020340c00800445034980038490780300200c2e03c3c0c0c1da040c0881d5031007101403580c0c4000c0c6034043e070048202c644403220307039090910b408400a81003c41000741c03c21980c00f25800f079240500c001480020400d81600144001172841e910600c0ca1594030404a8055409102907000240203005d505c003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 286474685 1250 286473435 286473457
    0x50702120106211a0108032809050108040305070209150a14030a2409030e040c0f020a080d180602070611070c0b0f040306022703010204050f040f0b0619120b0f011101060803 76
    0x23548012604800c00d0502d6500c04240c1510012006030080b0b58102c90400100c0e8000c0c2040401c41e9a141000d0342d1a0043c104040d40196800c42040119250b401b4550390006003120070002c40b6850359501c85560314440f40d007681651000301d505001c941d40203511a1381036040040101054003401070030341900e002c000d00b10080f425600b1400b225262901450031700010034680555040351034030000355074042070500640031071400101d5515013099500320340d120301d0508070703200f41140f601c0c40c06200a510401e02601c41500d444c000d0859690400c04a60620ba0000070006030f0909041e28042a58000749041c0d100c5041040004001483c3d800980414001001610785a10009501c4806451b036103c0040c402d920400043c000c5980300561810360302c1054800140c208605880b0b07030014070404000b01d5108101043c03032803402c03030074000840300c0c0d40c181c1c1d0715402c0e603512001454083d24000b001042e40017079000c0d036481140d4407400741a002d504c0080300101da0701d59600900e50859001070030f091 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 286475935 1250 286474685 286474687
    0x50d050d030b090609070f03020c030f0403050c1c11041b0c020f060a0516080705010513060b06041202060c0109140c191212030f02030106050702120106211a010803 72
    0x58880340c15101d10400010b040d102920035291200006002d242c00400c504180322210350344042c2c4c0341c03199040d9075440c1c8000e4100c03565100f281a02200300d4025101c1200c070340c45003200c3c40b001400c020040810304c0340381c1d071007110795109280d840054000700038a8540d003259448140d0780c101079840030304450880d0350761640c01c108020307070061040008004000a002d60300411806405039401011146c3e5032507690170000c00200301d880e041c070481c4500d28010b00a5070810090ac00d44000034510b40800c9882001d0130018400b0702418415540618880c8002d1540040096009414030000170120701c8411800019112695a5002c04202505c40005240c1c0d001404818060034030713505a19010850ba015102290b03e0466080b1842c80209401040c100710328801c4a8418003e070402510a10944e0080d51a581c680c400101503411406043c1c1c4603186032414450745034010302c01d07901903031500d281d02c13407604100c1420701842c8070100c801201e00c15140c049035100785980319030140c0a0454a4041c4d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 286477185 1250 286475935 286475953
    0x40e0609060102010e100b1906051308070f0e040812040b0601020f060f0c07030918021e03060a030305030c0f0c0c010305071b02010807090816080d0c11060d06050d05 73
    0x80020400300414050640e0300d44160511512000210342061820034180804c00000340b0000c80c250103580d07075901800544070f4102190ba6500900500050210329140d0000d060791444000d80d51201c0b845a84051583c160050041062265101d58082d000b1041c403803404c4070020480e808114129415917400d514002440010b40e8140700b104200003a5400610340e900385100c01c2a403c40028204128020001a0450406018030b1b90b440c000c084594080b90101441544074003c0c0d8003c002c5108007440d0b8010003d99514800251b9010301ca0113040a001e45080d50b80507242540302030002e14008030b040c070880080c4900c02c4c0060400c00c892078050720b06007030844005402d458010300a9800e121000b44049680c020140c040d28446809103005d98050f21189420b644540d096003100070070340644000080c1c1c0f40d0329541124112038a0310300b244d440d212540d43c2215003448000c40100301c80c0d00607551101500c0c0c6840a41282c1d842e01d00009a5a962500000c240302104007048505810100234 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 286478435 1250 286477185 286477189
    0x41509050915060d0f1401080a02031c050a0e1c08040e0c09010206041203060e04050c0a0e090a0609020f040c0c060b010f0806012601170601080d2a08040e06 69
    0x103075581042d01962500d04180218002030b07100e02035001c1c0000120750707132100328841c0041c03500000c40c000984045400f05503182c02d025034075460802d005034013910031008408002c0600b07150300c002d0b444c40c0743da42d030381400e9a0800032507103100c00d0302640f684030851101025407040351000301000c0c02c0c40b4a201995031441d05643c01090300c4010211408450140a00c1020b40d070013003011075019034805d4540c560004600400d8000b0319054104070984c459010070081081000101011500b50490350540481e503038150720304100c01e0844200c00c1e00d0b00551408000500190849540e40d807008112581b2075007004045030850b4180c140010001e10f041c130040c400e1124a01c20284a0b10003882e1484502821080140c815400609160304100d95000748984414840d29066424141c40000031640d594a4501d0754040100007030411040c080c1c40c0000401c0c1d607001400c040348100039200c0c0c81c1c0c1c1c2811140e14145200e5415101c04400000c0201ca10004001d0790040028100100704281c6030309144c81 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 286479685 1250 286478435 286478449
    0xf02090a080106030c030209040614070e010305100311010f0507150519020703090b0f07240f050f04020d0510060f0e0601080621030d09050c0405070f050708030c04150905 75
    0x840070055034900a800e00119414020900680750140c4a818150329107142a1004080e09900100b02c5020034060142469100c0e48034441d54000340d80030700458845954010b404240b5206c018100907000b21950102e500a1212180030525410070070b00b4007595403140703405100b445c0e942d098050340d103d00304040d022070152445a9000c403460b00310301341070440c1d41c00342c0842c0040c0980d004008002ca6042c21901500c801c4a4601e80d120b10466140d041c0713410301c040302d801c42e00c900c1160241424841d0300714503224032446200d030b999280d039000a5110342d0240451851001c0040c0c4081c003030103810000754000f50103a0401854403c005d0102c00740f511185020b401c1c0d0180000303041069110520ac0b85503110400890303c014900f1440300c9080034087c88618520a5203116490681002d044109001c0040380001142c54255000d100a03650080100c501c1401c0d54101c40128009101c0d00340440ca60801956000e0043c04140e0303c0d26407070341e03014081074120199884c0002d114402c10b204c281042c00d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 286480935 1250 286479685 286479689
    0x40207141603080d0b1c051f020901020303010b070201020c09090d120e03180f1008010e0901020c03070305090d02060304050109060b031c030e071212020f0309060910020705040f02090a 81
    0x1d5141c0c40e15038107650781c1e81d4461240300b000b01500c0d5100c04001c19507954403250000c0f0401001503164102d042c91074034581324590768a0380c0051030000102090700c85442d000b00c0f00301c1e02059000c0d514580c00c040700c0902c46e4001240c240e0452080c0c1450810548a9409450003030359148000c280072119184000d01004c44140c460030098203101c1e01c40300074000042640c01000c0d64600c1c40500d910a40c021400301180c081b0510340c070558130304034807841c00e80200429043e14600904c2514607501d21105509134410110f8040c42d03a8804c0207803801081c4180b001d070121400050208a070b41c541600084c1c1c1c1900280c805440b0703a50740d10110020406036100e09000b500050703010b000d80740181d0540b00400d24079560614189615146e542c1a14803041c01144040c0c0800800c100900c070070360401d4040201d01a40c03100c01341c442d00210798401e56000080d9034100388020400351034007203003005204101050500d03140a40c8a40340e40420382c2e07501c5000300c0301400d15413140142c65a0040c070800c11445099 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 286482185 1250 286480935 286480963
    0x903080108010b06070f03051b0124050306010e01060503040c0503070311100306060203030c0a09090c02010c0206070c08250f12030c0c08030a051305010606020d031406090105041a04020714 83
    0x10417000c0300143d2040d040405050701420465121098100b001c030502c1440000c400fa59460800340c1da441d011034030b1490501c1a00c0c88441e81c641038030b030010b0695030130342030160325402b40c40c0c00300400c0198800d00045501500c00c0d03c075003501583d1100460310b40402508102c9040c0106440381e1010700345480c10741d00f214960f01e01804010f03c2d00078048d4036840068846040042d0000f5940c1c50207000d00c0c4503400a11b0710050400905c500d101d0020b000301500d0382c010005010301070104480c1e03440b800066030210313006600140340503096034a800005014102c8010448040c0680300b02003201048540511400b0b0358513119201102d0b0001402c50b1b00b600391100038024407003a400b0201d8046000e8990110b451607001480e91a070b03036580f01c0d800d028440001e01035802d00302c000c10941d07808030b1100d40c002c800b070302d00388402a5081c20548203260119403060b0400c1075070004202924142d000700303031800280c07000c2440c44110784011809a80c002442981d80307040c61070060100003010050440c0c1c01c00d031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 286483435 1250 286482185 286482187
    0x7061d030a020d031d091e010e010812130503060a0b0301050603030403050c09070e030d0f09050a03030c060c030b060c01020301081002071e02030304050a0303030e10021813020d0903080108010b06 86
    0xb81e00140f080c51402001a04011407107118031504032580b03404d180c030088020310707001c043d14040600e6202c15400130703100a4038102e03803000010340150000419041e44c200901622204000324001030b605e4200e800030b030000121846000440d0340341030100134014540d14102150882205080c1420b441c005080703c0d01a610070001080415408190409817680884030703158a501c60030310031504014072204e4941c0c180035444100440b980c000b9551594076a0640314189202e40c4c0d00704124407210355210240100c0d2801a00c1000031705103074400c8503d6100f5080000d001900f00011810b030f45c103d81584005690300000501c482c1c0002c000c2c050040440c04c40c158a891159075400c5001d2103290100298a80310000c22002c554083c01500c015040190040701b440f41c0d64100107003d07020420b02001180520b02c910030010010b4001c55105e03414400c40c1071041c80c200400c1c0070b841d080341011101c0d40f80d4240030380d0301d25000320301964102c580266103406043d414a0207440c211400b0f0401c083c82100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 286484685 1250 286483435 286483453
    0x10209041407140d1b080a050a0b010c0206031e0a090303050a090c1a0705191e0c15050d1802011202031003020f040f0603030f1211030c030903070507061d03 69
    0x94080341d8406280407200342903854600084009010b00320f41c81171840041d5031a40e07461003643d0f00c0b90401c2d1198844200074840c0b521034554007411900c40c581000e0024074a21000f03005810500b00441c0c02c44e00c4032241d5588030344a450f00000e00b14058419083c0c55455140220615a044c00f8154103c2400702003003001c06050b40d035001d48641d0b140b1941150030508808550f03400c0c070100030f50b2490b07900081a10030000e003000910716541940d44081f04c10040c0a02d19801405459514003200d59008100400050030111800c0c7c980700020b41c1c050030050f0800420341034409500601c2428420164501c004050300d2001610030b11541c00c00740649031040c020072103003491000100d002c880e01960413401c04102c25010170003428000240340a2241031440002c10554800c086040481075540c2d1180c040c5031424400707050300c03020444400841c4040c80401c0d1103008100096400c00700440c1228a0700340b05075141070a11600740e0010000c103020140314807e005041c82c1c2c01f01d640310210b01801e1598 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 286485935 1250 286484685 286484687
    0xc070b0408120301081b060d02030c0d0c02010b03120310080f010e1510031b03060212060a050105070201080f060a0f0e0f100503190c08013306020a0f03120e010209041407 75
    0x45002c4111400f100850a07542001e902c0c7e03881190451041c81a00391758a2400e81501c040903441740703001c80f0050b49082c0c07082901f03170b1040c4070702010000c000700509541540296800d4181d0000b5160032007881044c0e00c0058040070821200402c440710000108144007141001803c02880105850741c0b50481404c0040119080b44820150782d031042080008500035002c1944c241d00d16040105220701c000b483d02da9080c10000304078400d120441302d001025440e135004440034000c0000007404204254042500c1008608140b42e200c140a0401b4039259031b0303460180203140c640c0d84040910540001480003042c11fa1401c560f010000142e6020820b103050b001c259220075408018440301211a456001c0080c10080d20340105030000003400a00c881c0c08010194681c500f01d00e1035188810703000540076240a10342ea00894500360003400310646c041e22079007150078041c1d804908010244180d801c00000910607008120b00741c038001070311204400240f20480f0342c0001d80c040c010b1404001c014420b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 286487185 1250 286485935 286485943
    0xc060b0319030c03030b0a08010f06080c060f030a0b0402310605070b060f13020a180f05060f090418021c080a0e01050409060e07081e0103170c070b040812030108 71
    0xc00d80c5450141c1420b000c9003405c0f0020050720b204285e1112402c1000202a2015041401d03804a400707020018070780e55503106942e0f50711105200e03811941c28040d80c0c180401e04000340d91b20103001c1d24081620512640003a08985c40080d0b40914907289405280b0107500e806490004121803411011190703007482000743c803502a42d100105114144c00024031a5105c401c1020f000f020041d050040013001d000c0000040c0d04120900c80000c0e005000311440112451119421520180c00411b061401c04c82840019845841a1106014100081001350301c941c42484040b80081154868650300c510400c403040e0700c190f00c45030701032032807181500c0810001c07400c9480c420505d007030009090b040708006840d1030080750710140080d85008800614004640d042071300c10b810f00c1c1e0f070302c5400d503541d805081082c40040e13154040c8070700e0000051000402481e095a100300e800b01e499401c000002c0b14152404100c7d030481c100c41d1034003080810141604101501d5040d41148085007190705002c00c9a540b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 286488435 1250 286487185 286487233
    0x1415060904031b031e0206040210030e120f0d0501080f06070f11070b12010b0a08010506070c031e0506090106120b040204020c0f010207291b09100c060b03 68
    0x820305050010504150184840a040e28080c0050101403207080c20040d084840480180c0311300b00044480e900000d2012805a2140364020708046034044180c07070807401405551043d1815204003501034841d000f40401425200c01144d807429507400d400c001d24001c0d00e506900c19481da41c04141d03403a50820002c524503074008150300d0450300700340e00c02e4021038140101041c101c0090141030b9002c180c840201004240400d0ba801107241e180c3da03039549201036441101036500c001451030b4014001450543c00400680d801403107003015813512500d0304000e120b008811103482403c000c0d454010404103012642e44803444800810034607280a400d05040140c80b200108880e99000000f01159036035815509104141c1c4116244c0d255505c00880c000d600c1000e0035150241d440c0034441c040840d00c09030700d42e8800070540c2040e036a1a05e00c400c204154590007134590b20070044c0100c60240d01c4501e401c6904c1d40711651034290011071400e14004a4541d040924081e4000d00034010042c4000180d02c48 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 286489685 1250 286488435 286488439
    0x50a080f160608061009050d0507030b1005010206010306020f041d090c01140928032a03030e1002010618060e010e0103020603040b10030b0115110c030705010c03020709090609141506 80
    0x424040c90b5004546d1040340e030300711030f520080d000c0d908030600100061600982e0b10626041b0504c3e01c0e0013003040c00810891103418016440301c40140001030050300a00007600c48140024140b80c0c4852894215881242c42c3c0d1460400d014208046804200942120080203080040c00103040000d0130002c3d22410100f60b014020180c2181250404e00c4c40d805581101180200d4030240c807072400d95000d18040140144614264002c0c00844552210380c001312603064650168041a9600b84061181481d11400641d5a20000099044c111f4a6108140a940c1100194040c2410703000c180a0070103070086481908010014001038407141c2c00c480d0400d810040410b070540d03507210864040c0c0781d6600001d1401090354000564266a04540075001401d80c440904002c103105403580d5500c51040801c0c0e05a210b018108865401480c080c06154000d06c1624150b64641c0b01030001d0307580450003140e0840d51081c4800071700070114850300c12001060041d080c0440080b00794690640081c207114 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 286490935 1250 286489685 286489699
    0x506090c0d0e10020301080304050a090b0303120601180305010b1309050307022b030804140a020a0b030a06081906140709180207390e0a050405010204050a080f16060806 74
    0x607860b201d04002848010610560030742d500d68440c41c2698a03034005108460051085034800306014840d401110480320003e0020342c00c1401030159500104009080581841006207085404010034101480614050000482e00d5041d40040c000751a2030000700080701807400c140c0200150004c0110b0b8000d0b078044034200040081c81c46050898104c1541e09040d5009090105041582181402d27208a006847c09103504c810702203030b0f603228484118000c2d44001d2000e001d21260000101845d000201c82000040142e216002503180116540c03100b81441e0f02c0328101c00402c0424010384107514a50781d2000c0140c04c11690250032090740e40129911903d2025410100c1c40c0e90ba07040d44c60254001c0703100314120740d8542c0a02103200c41d10414039a01400d20b4511001c072500c0e0034048084a41403180c0e204165101b107a07400080c08007403c07c44031550204000a0b80d03585046e0000c02070180318002e01160645600014600360300c00c2d8940050004202041010380d40101f001c5900042c15141c207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 286492185 1250 286490935 286490951
    0x60f150d05060a120534120605010b09030c04050406020c0109060504020f011701120303140705091e03030901031109150a2604020d150519060902090f0d050a0f0f060506090c0d 77
    0x498550b206642d2962040540c036a0002240700c10151f0081020740103440070001c603600c51800d40402d00c101c009030781d010360017031650400ba801c1076401642d115001c0d00f8010304040741c4001140c25244900e01c140c95290322a01400151f00e8006407184540ea400d0030600c00303c0440e00030b10300300d0100503ca00c90400320320079045002e150281c1c0240c15400c0b9036040729406850000c201a046410180d40030780207540507406041c0e002c061549205158000400444c01d10340c0c0f100044010740340e4482094905007041c40048915107071107040c250f404030700e402840d07103039401c525008180c0c244043c509548500700080c00480c0c4100000d050b40c00c560190b414505000d0203081c902400e6200d80c00040b8601c2c900000c02082030782c986010350300e078040c40006000f0140c0c1d5280c448280d0041c0a4020352248107403041840034039010785444199440307a001d65a1448603519854100706c4e003480103a840105482e040741c204007e40c41001d6020034226071740c008500f84019031301418003a03840c60081240d6a1411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 286493435 1250 286492185 286492243
    0x9090a090209010330080108160b040909030c14011d0102030708221703010f060203130b03062d0a120f2301020301030609020f09040803060f150d05060a1205 69
    0x1417916180088980445880300c0c0d40c0e4000c01c0a80e01b4400c041050040788001c4165101d05031030b0100312071000501c14207281c20301241c90024810030000300c0501c0380d650290740009500303a00c0340100210003c000a8560004040070141c14070540d5030100a910400c10801c1c0b09030017101c0d0b2038014003041616201081c5035420f5140c21101040d000c1d040344410195007503080350000c0114141d4800c88441d2a640d5550041603035070b03001d0061100c400c078805150a22041803804045c0d680a5801410320902c1700f2013403111072104040058000b0083d02500204401b07091400c0c41d58010190562008030b0380c2d486841714804034a0480d4001c0c4103941034021555810b05080b80300b0004241d61000310b40d6941c0d640381c284005d0103000c5c2c04074020045000940c0301844c1c1030000034130858000c045c291455585604019a225042102c0c643c00000c1c0c1c0c4032400ca420040004d0400e844070520002090b040c49410466002004d5000318007507840040c00c50300040e0b0115a06107804003e03100403a5400304818 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 286494685 1250 286493435 286493483
    0x24041b080a0609020402120f0103030f030608030316050f0c070e01050a05101107150e03061609060c08120f18070605090609040e030a0206010617010f0302010c03020114090309090a0902090103 84
    0x305182645140300c0c10302946c07051548803c0c9c100c1c0d100761a1529400403403281501503401c18840d840c1260018000900000150f640300b488040c99450300501d80240d080d078142141d0001c80800c106540310a070103014064514050340c4c09401c08a51044240340341000003660b44000d58200c00421088650005a20400b0410540641300445009101c00c0300704100505208007070100510a03c120f20100c0c44024219440c10042c100c0c542d107000d101418880280d5601d800401e0480c2c030340a080101c140404190384805001d03010072403401d081410182c1040b02080018008146141c00c5110308000302c542040031680364802c2551025103a980c1c1c3c0000034000c149444c1c118140d400001070130801c059020810505841c41520340244460014512241908090180002c80b0403800c4050015600400d4070b508050310910020804c218541c05902c0004015940100241d1000c0b8904000d85016190554400100c2c0750400400d1116000a00c0092042c4400703032002c001095140203a4228003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 286495935 1250 286494685 286494697
    0x619150e03010e1f1406010c031e0c110a05130b0a0302040c0f110c1c1103010c0513080a0b0a0504050327010e09041709010224041b080a0609020402 65
    0x20000c0042c551103a540340d0300c8000100311318180c2c4070f202040000040c2c1a1181c2c180140c415000c14905681c2c41005440b075108030030080e810711044540130303d014984003165140d101540e5445041c01c034002d140c032091071a5120741e07003403240741c4611041c086d54450f54204940900303540030201c2e51070161000b2038403a0000742c00194001f400d01c1d0107110f00c141c01c01584111148030380d8850404140d110301d05629002c41500b8540c0c413401d54400c003a48550880e50014100f401115600b240c05203103000a0f003100c2080708520046440842d0401662100e41c40c60382c014460a400b50104c3c814541e00e150741404001c207195001035951000c5801d0100c00c20135601c12903241c10b104028285100e48001c00050308007109400201079406043c601c4c00c6c003110340c40c00b495002c880d0380c117041c03208070105070640c0050b0350b01030451090070103182c002135240c80d800c1d42504c01e070700d080c0800d401c1905226440200080401c0c441041414041068405c009203034080c484d044040050881001e20000d0040d120301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 286497185 1250 286495935 286495939
    0x1409040b180708130c05010c060b03150103020405090708190c050a09050a0b040c0509010e150409022503050f0d11181002010c090311060405061c050619150e 69
    0x4801200d1820030700c0ca5460b002d1086501c511a05075241011264032200070b280040ca07264141ca800c001550052250b603200358400c2d4804154030b0a07441c00700745401114564a11808905001001981042d1241507008090500901409070520505179070714018284100f00d00b44c070650469003031110210000c03001e0f01c0e00404a050656a9048090245c502039610114561505c0e100100501e407510480b40b0f00b8001d510341c10705100c0e24400648400264001e11508090b41e40a40302e188010f40c0c00410160103002030058942100362602000c0c04240c0300b103903620002103012100400e810006039908900f5010f802c940c0e5800d442a0b00001d020018500540301c0c0b0003144120307a01c032130742c00100c811240c02e6401c0e660404410384103e003602c200e001841c001c5802e4900500c04509035401c80305c144480541550b03e000c2d41c52010580c503a0024074000601446001c4c0035184082c01c1c040d15400100448800c504a11500460f5004034000e200749d9000c0c14940000107070107406583d08030070358480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 286498435 1250 286497185 286497199
    0xa0c0f020301090c1212050301030f02010810090f290307030b04060b06030408071b0e1605070f0302060117030a0215180111090a06080405121e0301060903140d1409040b 74
    0x600c4e040e140f5070117000038045540740f8095034100721b003500c00d40c2964120b07030f00602d8070802c654039600151061140504400031483c051040400e21103078a001d4562520a40380001428a100302d00f88200c1100c032540300c03200700d03103030140200042c5d40000e1001c080c0da8000c00c40d1015500c071403030401c0040c00240f43c09a08032402004100901680c0405051207138003440f80801c00704803101056200c071281c2e003d00c0d842c5080075030210b064202c41c009800041034203400c02625268803a00c80c8a51b440301102d007180164012001170120100d1140c520350218034040055042c01d1102c04040e4868440100000d4800c0d10480014850b40c8208041101303070507550020840692032001f0381c0e2060344030080c0c29000d0600143c001540a2195000c68400d64001d009858014038001003284a42e0105110351540848d1403000c400c1180d044008500030452605c13103654041c07031454500111b14680040c804650000c0070070402d0640c0010a01c4840810400303915502c10f000000030380240b17030002c24141c001039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 286499685 1250 286498435 286498439
    0x108061f0e09070509010c03030e031c0204091107110d0204140a150f0f09050408070b0a05010807050f1c2303040906170312190513060509030a0c0f020301090c 70
    0x90044008a01070300142c50410b01561a294260b80500c165040180080c414004c0180800c0c0309074821070a0130390040c240d900d0410983c3e42c02c071072200070740b40000d80d1030360015080021034107610801d2812103000381a2414007030162100c2140d601c0440d11a03005040d140070400031569181e001c2e4070f0281c504800307200541400d4206600500130a21100034444040402060a03400c4911072421500003010481045041c400b845010f0a0007600c101d42040c02806511300190200c0ea001d0300c07507881035400151540c900b201e41864070590382c0c4154000c0c01955141c034500d4841080044156150049054403070007903140c548080c820f00c0101c0c001403d00c0d0443c000d9030f01c10120041c0200caa944806100c00b50310f83c401c1b03600442c5010304c0410194020040380c00b0000c80c00307003496032000000c1011070403100c4001c0e00c02d0039500210366001214603900c0d1075000700140da10500c2d0f0032541c1080114142074000388060104010244064a103103a4817500c031003150f800350414011281d02981c0c1c032560513 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 286500935 1250 286499685 286499687
    0xd050c07020306151003021b030309030c0c0a06080a02070212100905010e0607022505030109030801091a030d0c06020f40060f0302120106020607111204050108061f 72
    0x6004214120300c00d0140302c000ca40344c5152181040543c04004040e50305001e170882041d0025030080006403082c910f0f00084032410303602400610304c660000c8018599600d1201c0c411818281104482442000b105009010159000d0101e561010192100583d00e0380580001044c0134907049500e0094403841000640100454004000300d0788910002e000c0c003c2c0003800c841c0c45041c02c8810800581c0702004264100c2d03039250a0289400c030542c100d89402e80c641700802d003942c4103290203402254444004108511480c850710131820204041001c080d842180002c3c0c07519288000c12007003000b040b0340172007400125030440f80012103005c5140e0b920310307100b4000f04035044030840c1c1988201000280c03d1440c11080da20312131800040b01c03203060785418020705842c0101d0840041080540c20300031140350026114009010309200d4001b86090300c0c103614001c03e522202c610482c00d030b400070030860f82516010030030303101595030908001c5c000d942c600d40800d80307100140b03111200b10744101000400403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 286502185 1250 286500935 286500937
    0x16091e020a0c150617010902031b0a031202030301140f0d030305090304240212030f010e15040c0215010f0602030d0513050a0311120307081504020c01020409020301150305071d0301020d050c 83
    0x11445e414040088070383c555851401c071b48201101a4054001040c001c0383c107540410b80b5030101400070700d01100303144c60b62a03142e4041040c0018070003680c0000018400e101c068801002c1000045541590350068207012440591654000605240d140c0c1c01041c0394407014010b9078050702c50249640342c00c48218a0b000466618056428094003400d80c00f0000115500c0499106000c003800b8007007541d103041248081030200402080050680100e10400c41c1c1c0d0341c0c01241082c5d0807a900030710000071901031009000c001a40040040c40c44100102f003e41d03000b0080d500172001e51040002c0c1551801c074405007207005564018501c0c000c4a084604054016801203640503003c03040303030b0a640c6421000351151000b40c401e10f0110781d60000048680060342c2d101131341d56801a0001d420701541c800d0716400d981058100140c01c98012005003c40380500007071030000002c500d0144068140007102a0800840cbd00c0403480c40da449003001c0310143c909404481d03006003242401c210600d808954401c003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 286503435 1250 286502185 286502189
    0x1e04120f0b07080609040b070c08120a110a090303030e0703020d050d0f0e060301030803090a02060d1d010903080c03040c030c06030207030e040e060c0a020c1216091e020a0c1506 78
    0x71007105100401c0246105004882c402c4201410985007901d071600c070003442682c001c1021042042d19203040300050201005844084890110720480d81406000303001a070320041d000c030700019400d000e0800c0d002d40c4203820608070703034050800058007d4540c0096003003111070741000c1c1d00070704c004100408100d0002241c034901900d50b5180112207424010881d0003c4244000703c0d0710110a00061000c5035001c0021500500000121442c4085a5000c64004d4100e44211220360303980b44031b01103c20030364102141001449000800c9001d0f981d54001c0c0190f1805495450000b5003c400101045404800000034681145c14205d03078980c0c0c2c10009002e54031040c0200c0024075600d0001e402d60616006035107045558102610865940c25030490072600304201d04030451160200480490326140c0c00300c0b600d501e21102400c41c07028040c801c506400e01681c0203921031440d001100f040850001012049651094400340e5034000c0364004650180b42c3e4400a0f10801408209039000c00300350f0301a2007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 286504685 1250 286503435 286503443
    0xb0108061b07120e2d010809060720030301090c09080a0c03022407050f0606010507050606013504120302040308030103060b03071809031d061e04120f 66
    0x180a07941c4100700e01140c25025100300150005015060002e01450703a01071042a0500d0031103010000e0300005020700400e13040e0200306414070700081c0c8540d80d480050508140c000e0903c1c602500300740314156901c0500404d11402c20107414090b0342c90302200c501344416042d401c02166181d584941d40070004114100c500004601c4080000400c6640810760200d41c3e0f4001303481c4113280d4555001c3c4000540954450524010000380401175850341d5000f0b0460240550024650780411040562401d5800307000c450501500303016420008000060701a8400c001f860003200303006a040b1094030405040a10241c0d1100b0f40501c114540d4000c04118452400349407880810220000143e040788078030700018110f40020001803004c11004c1d00301c0f8413040300c060101c8003003540d9480c68801321034545421401403500d0f141c0101c14180d11031003090800040d40a242e000d4200c0d980059114811502508038499480f50010a40000d51040d0342c0100744c2d102c04540d544901d841d04022020744e03640102d07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 286505935 1250 286504685 286504693
    0x31703090705012f121309061e140f120d02100c0e0d0213150603060504020f0d0b030a0212030d24061805061615110f1b0a0b0108 57
    0xc2541c45040d01910405001c5252014001c0c1c400313082074542c1c0410001040c03403041e402e0a140d11030540c1c3c000d014944000d4401c04007141400c600320141d81c100c1d40150240b640000010a02a00f41c089071022155a00c82ca50300100700c07140450f015003004580c0c16440ac2070f1800000c290350001c5418120300b07a441d03003952183c09505c00e4000844071500500d4000406244c008181c40c20300325070640c03405000071301140d48402c0c1881044295654515110300785150004208040da400d402620040c0808440a60030b2440e524004071980c000c0b02d00d02100e0780e031a601c550240e61014859410566009002807041510a0303210715541d5000480039400d523480c025130040c4900b1401f6200420007400074203c11550315080c401c90301d566511038075400341010060001025543c01d8000d00b41007002c031003400fa05180600b0b2800d80a102c0c144400912801c080341401e0b4135003e00100c1c0e0340c00c1452040582c8400880c0c15024000900f0420382055100e1262080180810303190428102c0e82000c0842d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 286507185 1250 286505935 286505939
    0x204021201150c2a030b010308220503030d02031509010906140906030a08070206040b0a0e041d07060518040504110306130804032402030709180908031602070317030907 74
    0x21202c01c009000d0141003090130b85916a50344101c07480060303410351a0021400c0d11601c0b0303214040701980c01e9200f10381c0f0f40740c00240503003100318810500d003c1c4000c1c20440e1000604e0500465100d201e400b00403500780c0d6002001401d51007250050b04062280903010030100c1d078544005800910041c0100800c14441095943d42403800d000314074404e05d0050042c091005d05a07131250596001103200301d82c0300303005020100e42d130803851000c1c25a140495894500910000050000f15012044c880c00440d03180d44a80460140002d0214104e030035500c0c180d07548031052406c441c402c85040d8410365100303040100344802d000d13a81404540e540f0080301594420344034401012440803060000800c40c0105100c03c00115030141e170300a1164650b030395039009100489c4131002c106d0340211080008100140c5e0184140000002d84040d05000e1801c10804480703d81c9440c011030000a00d07902d00401d058900d100d440f0320030b210180045a004003a50009081b4020544641e0021109800341e840348042c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 286508435 1250 286507185 286507187
    0x60702120702030c0d030c050a1208101d0405190c051c0b0109090204020706050103152009060d0608011103090d0201020403080307050304020325090509031809040f020402120115 78
    0x8a40007541e008000781003801180c001d025a0040350001501400340140b078000119070248502060a441754581901c400f80c850006401d0030000303001e43c00a01c0c0c5a94092041c0845000d6924041c00000b0100c066076445280c060301c1c00c450700501624070707520b03407003004104a111055801911411a00e081100c200c04032421262001e5030f501401060310a00100540942a03210341034a0340003400140c0f400b5025225002641d8080c0d10442f0882840b2400390342850540c0314540304090102449000c1e15400c20000c0c0b202d000d1080068460400080c070360158004990141b0003c10b840b600034402244003480c1c00080f0b81044030800703914042c072854942c3c5184184200e40580381d000000c40e0039034540800850741600f000b0012a058851603924142c1d039400480704c500400c030351030b0302d00300d006080c0b55945060711400791904141d42d0080c0440013081080c0841d4202d43d12069600c20721035a01d505000307031540301401010707400c144000741030800c50070703030021250585030a100260104400064 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 286509685 1250 286508435 286508437
    0x91e10090611010c02150711030304030503070e0405060f010f020124051201090206180f28060309020901060f1416060501080a0c03061a04021804060b0a0210111b06070212 75
    0x130b142c0c00581280513012040504075018a4010783c06290008038a02e050302c035585140e001351070940100f500481009015580302c100d107010905c094074103018a00705100441c3c520812a2202d80c1401140980c2c2d2030105c0c400d61003109042e002d0896980c10b00701130503465650110a014180c0181909803420b403c5040c1400b0722000154060320061800240c508083c00b41d40084606551024058170039404a640345001ca54409405000b690066841c1071603101c400c10180e031240b424541070100007005039540012290441b0805d09010415a01c0c101c005c4456003000301c03000c00d003071602140c043d101d40403003001503801d00c0c821a0708020300e988a94907039556101d2481c00800b9950390780300030300011344a034200d1903885040e0001a41c011541ca0000303001d0707800c140800036451640c4407c0c1d100f0380c80c00b4026031006006202e4264500140000003d40b07810507038250101441d15040d101e8500c0d90920100e500d0410f41e0316154501c079810b0f450685d00c0c0d0b44152007900041c400e80075441000c40100c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 286510791 1106 286509685 286509701
    0x60403080c010c09080a02031228050406080a060b1902010219030228020a060b0f0603040510050714180d1e03020601060206040305091e1009061101 65
    0x220f0001c0c0b0740d030f50a40c070001d040e5100c5684400940c41c0840c031141c49200c110b54240c1d0302e40300010380b143d410302000002c0902e19298222407404503070210240c020703265142d07214040d03a25038414030401d07117040b8015055400d404001401740c101c0c5c0d0348455283c620881c0005402d146080742c4008030395405c00d81240c0401c0e000030710015410320a00c0000013190032915800c4407080d00e010001c1d5125400304004080781c0d680c5c17152820b0307903503601446241800014001ea541c3e1030546401c545649c81140e003603108904183c00700d0303460ba004000d0b0399418218140c18500307101d04485d41c105241c1c10042203541140c1140c00f83d10220b0b27802c5080400005125240000d800e22928001749800c60582c070103011508100240b1002907131220444614030421541c0764800c0e840c000300a010300308090b078040d900520402c1c801c90b0880d08500c0040c1141c03032541790303003204000032995242615110 = true := by decide +kernel

theorem cover : BRFrame.Cov 286330935 286510791 := by
  have h0 := BRFrame.cov_init 286330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 286330935 ≤ n) (h2 : n < 286510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
