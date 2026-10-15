-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4636
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:15:18.703226+00:00
-- url     : https://prove2.me/submissions/1642218d-c15d-46e8-b0a6-bf281c48e5e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 833633093 ≤ n < 833812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 833634343 1250 833633093 833633111
    0x302060d0b0303160b070903021c0f08030c090a09090816050c030717010506040504031b080f1b07060305060a1707150c0318030803071808030c030918090c0d06 70
    0x7801c0d03600c0f00c07540300004042108084c040c400003c42e00d41c2c019065081c00c608452550380407a1f851043c0d1586171544540c00f01c0d83d8400c0c4408003010741b0344284d111034401c1d80d80c40c000d6481d68068012440c014042d8800d10008108a0054810074000c90f80119035281420084582c1c003100d1082c212003202c0b01c0c0698481c0510588007002248003a00d40040805c201d045120212400c541009120394410b03030600080c400420f403c1220800c0d4183d0020740122110313490b0500e42131500c500074000794102000114080441e0b0340015241840c1268000d9403071417943d840080303007a240240c41b450707417100c0b402008104200c0b0000c680d2200329100401d550301c441e0744245240002400c00701042c045131041c000c40d410035902c480b14400004240ca0030211450564a0344042400000c0080050000d903070728510040a209070048003e06c44e07001180d40c1c0d610b41560725038036500030f484220301410702c0d03078107140c0c0041021191303d10515000c2d0042c55039401d02001c105483c00368036030a8594603501e42b514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 833635593 1250 833634343 833634349
    0x20307110f18010f0302040e153c06330a0912032001020f0a030e0c030706030e1204030f020405040c03060203010b0a09060f0e01030e03160605060f01020706090302060d0b 75
    0xc03d000300700204440700e0032403a40c01404140d8500300d48906040d001100100007048646044035003061803c000084100090b05000d2a1010808040d410346a01d2980c059581c1440c43c4203a481507a003a64040e08440c0d00420064001c03801500c4ca01c2c14500301e210300f500050903940985001e09040c50203242660740d40e4070100301f066803904103400003800091260070380007415040604605811000b10f00c0c00c02e4540e4040340c9801103005480401d43c45801005554004011101c0b05c100b00a058a81060340d03190043c006164000800c4407034040c1c1c100300344060448a096030b0440750480403248030031020360708020003014020b0003122035010141e40400410040d10286000e0029a502156501840040500200560380c010004c100c100c0300340c181c0540d07103c1d00b80040500c082c24049080315106030309500314015a445200142c01022503070041c0400c641045000f5801911489070910186004a031101040d0003006d000c11a0307150104014201385006040c150003a142c00640f80c0c0b219400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 833636843 1250 833635593 833635639
    0x9070f03060e10060306060c0305030a02070c080d030f0b040903080a0906020408100e0c0a0b07140c1c020937110d0c141801030914031612020307110f 66
    0x3d40180070481105102981d0503210f11400743c4003d0600341d2404d2180d0782c00801a2000404e13a40230281c0208580301001400061180980301c0503080d1100c040000b00020010031a40304d80740d0055041c07031090609801c0610404003d2501503030303010804e40d207008030040038040611007141c605508000020709042e051112148403a100fa2000c00e80400d24000300d441c1c8288001d045104680b140350411410b100c6100f00ea40d22076000d1b4001540b185440c0c00d1604191940a5241d0000c03072088060018903580e00d01c0480e0f951084403002c0d1035803210240204141e00003040d01c075540003021060301c0c055980b82041c60414075400760100e2000c0004014022941207040f20b50b00041d01e82c00390010300c03604540120002c84200410900f032020b1200c12001802002500505156882075040140074a040903041a100100300b12642d81c103030840d43c0708548290ba03800383d46040c1c0c503d1110010a2000c8112017005170404424840c4540039420084641c82849900f50b00c1203040c50508011000201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 833638093 1250 833636843 833636851
    0xd06050412090e1302120f03040f05031501080c3303091c1b03171602060906070935010507021b2407080f0301170c09070f03060e 57
    0x1403101d9a5001102010b002001e0319004120003110312400c008100020308040d40c0710f65011501d201c1040b0400c2101401d09521306000d0300c60307010000e000f1400031540c01842c000c031103042d002c030340b07032410040c03851a036102c0c00b17005030319460700800c0803420b051410075200781c440c0e43c41d18a40c0b02030001c03481000520001c40764880d600c21030003004010321482d040c0b203064042030f40e2003644001b050348030f4001401010709105440d07007100210000c2041c503101e40d202e4104d0003a1b1110305c8840d03060841102c091010070300f1942e001845460009004190007080841c028242a15014041410b110818200780e070f00e5580b54010b00d0000b00d80e800c16610340660402d407c032304c200000800c1c0c10709100080c100a280382048810b00c00311001c2180780e448032090b56988242040021504002201d11a00c2c83e1180e0000908054004150303114403c1d40c210082d41210841070b5202c80729003d1340740ea20784445075400415880b200c11030000e10094001d0090044244641c0340006045450311500060000c040d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 833639343 1250 833638093 833638103
    0x1505030118020f0303190c03080901050411060307030b04150314070f140d050a0c0e1302010801090f0204081203070206180d08041e05011a010305010b031302130c02010207060609060b0d05060d060504 87
    0x46c105c1810b0700f002700036401c090341c100288024070705529529400f8844880c958001c610000008034a180b003071b848042c0e12500107009000d20300401e110940c001720140416641c504001c421021b20000008001c4200c600000750b43c0b0207289045500c1d00241450060690031018015140c00010018040060702900c0313100f00d031548504008101c40b055070020048154844405110740143c0e802c820304034110361981c0c4020440b500c0030f0601d140603024590009000d4841c0300200b15840c000000030798440c0082d40c2c01c82d0090380e1400c0c4154146203034401410201d8000e00015182c60f0700c10441e466019001d4005103120420341e841c110300d136000030303a0b040d44e06035501d0b4214102501b1102064030807031024130f010301055040500c01320003480003401d072150307900054466104545414880755242104080100402d64a520029000c4e5108003811216030346007040200f580121886001c09540c1909425401d106551074910010000541215402a00c601c991000200180a0503105901ca0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 833640593 1250 833639343 833639357
    0x60315120f1e0b0f01050d080d0b030f0a110301020f09010c0c0f0b040905010509040c061b17190c0b1306060305030403080a0f081312030213091505030118020f030319 73
    0x40d00b405408a4800744c07007074003900e8200004211070b0b55800320324170026802001047c0c1d203101c0029000f00500c401824030350140aa6407903084d41180c0840c0c0200c2c2140602e40d084000c2514108140c200c0c45045110f5284920a020008065108401101c03000744034005003c000c80c0c0f210100c50710f11440b9800071300606c42c002070074047d00c1441d0040030b00400e0182c8199050342030954448544460900400040080700b00a849106015598071558181c100b90301c003000602650500b5510b601c041f80184104010700c9401c0710070b40c030654480d1409a001007202d903a54907400010703c18200a210169103450300c0c2d11010003c107400740001c2004510076100d65568000a60000d009190702000c294103004804c410050640c013000000091140d0045a5070100400147c09030020b00880019143c41c20b9881e03004120000160b000c110080d40c804001d0300f1260b920700c101800d0705c0d09142c501c10212001c7c60075100609148008800c2007400900b681d082c005855200c082d14403140030458000307262 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 833641843 1250 833640593 833640653
    0x30712081c0f060503011e051e07031a0916180933080a0f02060c01051503060c131202010903051903080c091c031101110c07060315120f 60
    0x480e114820013410250000c1c0915000799007030100030401000c001041030f89400005444842c03d0400107900d4022200c40380850909440040041682c05c1c2207511200355a40d0b001c07440d2070542c41092191156518100e418003034584119104d0045040821107402158004540c2a400c1e01901030603215040321032103440c8000b045d26100e540c1c1301c0450707d00012090810701c0f421201042a4066540010008100d15500d2011807800c1c89090881c02c0c640d480d00c0240001c41d100d014401500c04011800c5411541303c40103008400e2007400c5103940015081c0604100804640101c0d45140f40141480b24510b546ca407105414032074140b1926141d0b10300c000e010000c06410180c25a0003d40c0303c250a41030119403400700311143c0030040c091145900c0020000300705886560741405580002000340326480c600754814030607400681540025000d50301e00411031912a01ca01d40103903070b41d0b003452040c0a01c6c2c8010001c4103150140d06076149560303e007800c000b140c03c202e154200890142851614010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 833643093 1250 833641843 833641871
    0x50f1303200105150906010212130905040605060f010f020a020d0c050d08030714180906120313061e080f190212010510090803040611070e070807080f0402030712081c 73
    0xb0018501e10700c110545c000344a081d9900103041d400440d0910701180e40c07512074246105800c603055100b41d58076410601040100202900031030b004540035110b0140c04000303034005491002040c03012200591258034200b001d40703400c0201c4d2841c60301036041100000d44401c01304800c030070741420648000c0c10000034080000e80c8903900d041402c23400700c241070402845030000000406000f450354402c1403140003052241e5260100c0241c0d12074050100c90b03407460f10b012030380b0b1107408603c030364030100f14400f01c000b0b22603003403500300d2034010081da03100e1485a50f1100d01312a0084003805821604103224840303951a6200c0c4010164000143e070310740e04540c5060b0070004214141d81903c0100b2040c214104107009002003a9800e5410605100d14480500c005080c07424449030f10000745151501d0a1005035600301070b184c0e000b40d00c203a5031500103642d144101d903801c060503500250140d2110800f000204041300d500e400c40c52050b10705515108801085d80c191150034400c0e1294140d56403c82c203a242 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 833644343 1250 833643093 833643121
    0x30d060503150405030318010e010c26010b0306010f050f0403050a12051309240906061107030503040e271c0306051f02010204030209130c0603050f1303200105 70
    0x14084042c9402d03c1c0781c19900c07503071680400f6085e003482c100502c002201000d803c0d00608100d165050081100c0d001102d030013001c484440c8412b0828804030715030700146a00c0c1c540310074162106c0100441c690b0f1074050046803240c0c654102c44c0700b0040d051210301f0002516500402c01140100010715007510241001c1d07041194030f0000b68203201d41002b60b0003012040007003003c206c40180c1000255400c120b5818000ca248104100009140707001000c941425194090802e55100e9030700e4520041484400f25a14441070101404588c018070040007d00343e5410401d500c00202c85114020741141d068001d182c05c0109071405450b0040f680b40d00410b42210b1040440d80000e1138140000c61401010400007900340d41c00d0201c0e00f81c03074030710703c80660b000350100d070300035030303015040e20401d1603c0c40d5020f1424010400480d45548940380c00120b581c4a0b001d5540034010b0421034040a4441041245080d041d02c3c0041b400c0c032410071980518124505c0d49515502a50f0001191920707083c42c1841c661 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 833645593 1250 833644343 833644363
    0xc0320060c0a110a18050906060301020a02030f280807110d0c020f181f060c11120703080408160f0e0106080411090a0e1c0e0d03090305030d060503 65
    0x55441400040e4021100152480b400d5400c101c038881d5541194001c03a03e03001c95a0082103d80041c0c0b038001c5040308465000714802c1d142142901c83c180c46190415090307109003c1e02800690040c84520340604401c0010009034209103110402a0484040058910711862101000c55819070800080c10340050801c00248140000f5084050752840042c05042000d40042e02810f100000c148003503c511480090040304200351214500c3c2c40c1520038060040d4010300780c0e0280c075440e8009801802606201c59182d80a9841c014140c1804140802244044070103c2140f040c03d02c00008550a03400600c05407110901401000013500300c4002d0303100080d070026110802042e020001225000d109070306442182c608a0050788480c10b000707081a008a04046d88808800207000318564141d001e0402030b20700d041076a07084803103506100d8031b20542503005400700308806141207403032400c50300b00a50326100381401d82001d920f03a182d16281d50050350a52a446030780f90030901aa1804000c031100d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 833646843 1250 833645593 833645599
    0x1e05010b04050f13020105120a150815060f031009061d030405060f0a0207210308010e07020d0f02030c0a080c0f0a0f0620270a06090e040c030c0320 65
    0xc58109254030800855004103602c03130312051103114600710781c0b240f0112200f1811140d00840203040c030803030a500408000c0104070940302c40b05000a44800e003c11205100d048210101c0d04507a650414081c444103d00543c41e40f5000307000c2640040c401f94402c511019001d40340c0060fa0000c1c800c08000c034140030300c848420992050004114503910401103a0501d0038050b4016140c0342814016480c004103600035040e034030b4030202650118412002c000d00c00c280240d99000c05030f41e039201e041101034800e5402d8001600b0000d80c0084c02801030013035002b28607291040300d107050302c0c1c41d010310300b0442242e0044a0950780010100d00d41c0b602001b001042c41d4900018001c03d040307035500c410502030040310013040e10752074030083c5110402040c1c1c60000084d41b403180075a0781000681080454060101c0d8802d0440000e2040c04107040c00007611050340c01c0398941e030407801d082107100765004000034021904084582c0000c40054414800c601c0154030982c11f0101482179410200e810f01842e42a61b40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 833648093 1250 833646843 833646851
    0x4230c0903100903050708030112031808340b0304050706141e070b01091407080106020c150d060b0a02060705120f040c0503030a0509090f0402031f06031e05010b04 72
    0x840e03603401058800c0c1d041c00040c00000c4022403858182c855014445015008090103c000030710030f034039020040303040b074440da0b912001d1454284ea460744141183c010044245e0148240d2440ca0305c019181c40400e810403034411002c0603200d020f408032400c281e040000700300004401d100804c0400c000040140c80141070020780e8036038041c0052035901502c035101c10303203130039401080800c007030103004603006103801800102c16036071944020740c0506200d0001c40c031013860b14800581e00328842d103042030503184540d024120490288c4108601d59107030411080b180c2c0030400582c0d4030a00b603071041000900e0f000510316154000001c001c0e00f03010b4010700c0c10003840b03070410140b1004599040c0c400c0d44420540c0040e052912582000a5103442a0b0001070701880b0005110348001d410402030300d008007080f107001400b59a00110b000314203405540003074050340050f046400800f5884450b14041040c0b4030006845680c039103580380c0134400c20164038441f00c8418044802e0000030b01602c00f14210a0360280 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 833649343 1250 833648093 833648107
    0xb060301020703021c05090d060203070e040e0d050f190e1002150117150f010f0801110910023a1805060d060302040608010209101106011e0504230c 65
    0x194803142904031400c00107103001d6441e00801e0054068030040c0724023030b024051410711403900302e0095200740e0322030020584c90851100305150500075003440701c40f1100945400c86032500281c0e1f0a410000c16101800c4c02449900302c00548810300c4440508207964440100400c1c03801d1084071146c0c01c034004215044286118070410654154504540035241860714010003403203038031304210507584030112015140080c40700c0f00040360000c1d8161440264141e02c043e0b80d50302d481d03080f03980b5094154007000c8280b10240b45442c202c44401d501d00b400d0300682e441d0301001100700c01c0044030040040c156042c0000703a40103d00820383c00601030390850030901c0c1c2d811801a0149078100691090b103100b1000001c209500e8242034221358011540030f0000c1c0311454079001403501079000602450b0084400302c06043d1740500c079142541504128801402e000e909103132148042145462100c0810404203400048a458071301c54050601859241c00081d00311280d0ba85040420240c0300000500d024842e070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 833650593 1250 833649343 833649347
    0x103020c12071b0e060d021201020a0e031b01020a0b2503050906010e06180403180b040503010510030f06020904111206040e0303191806110a080f010e0f0402010c06060609030b060301020703 83
    0x40d94010a0841b028114424144001001c050000f28481b60715400410006d401a0704492052111401103054505600d2041001c0845294040c60180180e000351104404a070410a0a41d00800c58040002144802408031440c4018226000c40040d40da202003000568043c001140544403130f6032000f2003820b0a500060703021210b5160182030f508650041b4007094000c00c0b01d207104000303001000f800c141d42c51803d50420f070070900c107680c081d500309000240c0c08030400e000807050b66807013148440050002e40301c100094008401c281d40242e42e901443c0006d9100901800309480610400c0d040c42c50100207000076114081c8a2808903030060040c01f55480340201c9400b002945134800082c0d4450880340103404c1301480801622151500040020542440000f00920708194980c0071543d19a00d40200c81d0203408d200310b4161000c4040405c1070703440001c0c6501c0d0032a00524201c802c10314580c80b80c4048451030751108001c185c140104008001e859625160b204c04120000c508042d015200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 833651843 1250 833650593 833650619
    0x15181103011503060e072708062a0d0f0b04050702060c0a02070b040303020601030b01120809010c0303090c0801061a03060a1401051c0f050a0209010207140103020c12071b 75
    0x40c0007501070840c0811490350300c00c1e8130080081c0301d003d404038254180807801074070400380154108081d07000a510900008440c40200301240c031100018461544c0e22180150129880120b6004c442d40440d404030420f0590005801c2448084800194249840f00c0310002c90b0201a28640030760f04280400019580114115910030000f003002d507515a10303024204c1c1401c0c21504401c041950100e4080f00341a80040c0c00b80c140ea02c11503000a25903250100c1c10710800e00d00c800280010002c102c00403641d440740d038205248601c41d040200704102c0640c0c0e4850800507941000555070343d2814100404800004222110710461100d14550705000b40450f521841c18003d407200308500301d02125003a44110101e4100d900c80c0b41d00052401e0160120001800c645d01082c601e09061001085e007070300a6200700c440c5d13948143c0041c810286441960b0350030b5103811480314141070f400e0059a0200740c05000b410888240c271038885503140070520385179401e102d21a69010703d03200c13082802e00144110a107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 833653093 1250 833651843 833651849
    0x604030e06130815040203011808070609031b060b011413090e03090d1a1617091c03021309090206040308090d020a031b090c091205101518110301 64
    0x44895848070540c05403405550329034803d8100348a40708101d100030328100d507034a02991003100240402658901600c1c5110704c0114007a219a80411611000840343ea00c0207412520900740215041002c0c0c0c1c0404640c10100400e031206600c64030000380c42d60303010014401000016886d11b04001c080d14400c0800c00c064000d400d08556640b0307030031540d11410010750b541420020203601c0c1400c06407500500c550740307505840d9648200c05001c240e500040e120340307076615002d582d0f5200320f4041c8001900840000036040c5051800340d0314210102800740304074802c00c01c80d140c80150f954024007519003124040d0b07034002d290b414070f400544401031f0b540e0000c9400f243e0700126025141c2c038440d000074080041c1104000d510034505030001040008407860000000301d142540101c2550300c08180c001d582c0c0f1454010000341c1e05440c02d1004050300c80344000741d50301400407207840c040d5a0701d07040c0803a5103140602610394507920702003107203445424210a07101240c02090140c0c420a00c594006400180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 833654343 1250 833653093 833653099
    0x70f11030a032708040906061713030c05120a0207140a0b0304060b06040e060418030f0309050a020910050306090106030314031e0103080901030e06010e0402060912030406020304170604030e 83
    0x2401c90301050b1034030110059651503401000380781d82013450b245580e03034000d20500180ea410500000381c01c034040d216001c5103214141c0e0042c407913074403601c841c203800301240c4003203062004d000f424a010980030402605100a141c904556644014501a1904241d544545041c0c90705510141158540c12103400890302100c1c2000e442c0d840e1031800ca03020340360b038400e0650440008140016200d03448402d65000741001d135010000400c07005400f0341e8100d101000a40850802118420124860303841a52060b0140781528805223060b40041c2d540705043d1001c00a121810340103000301d02c0c0a0041e1034020801c0c0380204101da1950350090200001b0641c0c080c8640c03008000520350310b2240c0000006200d07102e000000a43e100e2522009982201c400035002034030340001c82040a00000d0080c2c10b0f28541d0411500d00d94603030b400c0060035441101c0e0607420000980c01d01d00e082c2001c20181001c2c002c5070b0040c689035420803010311440900c150392004242d00c480113000101e500315258460f0b8010030707 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 833655593 1250 833654343 833654351
    0x302010323090c09070806010e13140c03060405010b040e040b0a0e0d031b0c05120d0b030a030c15060e061003020c07030515010503030705071502070914070f11030a03 73
    0x44284041c07241400d503003844030000d090400c003280c4808102041202012038a00d01c06031100c510407240c0c0e5600721020340c0440d0350780031181c0c400c0c80e14a03802c0d0b203800309810700410400a400000c100d007000682d01001d2541c400300a1001600d03240c000c0307a02524130a400d80d0305140c81c1c40005001d19030007034409840742c03031760002284100704140c01042005a80c01c2c1112980502034400030300801405a02501850016100613055031044140614054011000301010b0310005d02a00c40c580c000040c210030642c1e80d0100301c60688080c0072880845000342c032000c0c843c20107420010f80e00d0f001c0f0021a94180d243c21303414001c0e02032200501e90009415203402140c40030b955020780084c81010910348042c4541c10b800001c11400080c42c071010400040c0c00c2078280d85c3e070307014540c3c4d1f40114000104640c0024009105282002480e20400f5925204541e0007554600d40d040840d40007803142030307100442404008903240c000788030b845040c143e1b01c1c00000c0c14000049040d1a0b00418031110105074071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 833656843 1250 833655593 833655611
    0x60402091614040b0a02070503030a170a02071e0302070b0a050307201209030f0307051908093f1f090605010e01171c031d10020d1a0a03020103 63
    0xc9290b07a98101201c4010159882d078440c180030829400606007000103116142010455090100071362b14003180503114101c0305680ca202004030710000600050171981e01b8486240445d4038041c40b421603810003c0405a10129420001d05000c203030b402182c0324000810801c640141c1c404201c1c3e030700c569145002c000100b4224104848401c090f00508083d108117200f081b154410b42d0024074403044200d044a007240d1400e00140d860340148980a040c7e40c100418a007032462100301c880d08114860748145203001c01600c005003000b0301c400304038900400e03a000d58004d072290095601071041011911814034045202607996508004203800c120450000c00603038a0345000c1c1c01c105185644100c05100780e41c3c4034000407a40c0d071001d1007401c2500101a2004045110102e1040c02d50a4001158548502100c2e0141c0191100e4620541d006410501d02c1e0f0440100b4482401c4900c81c50102696402c40c035003004084d0750b000d64100d07519003a0400254402e039182c1151008036642802d011580e240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 833658093 1250 833656843 833656847
    0x1090609120f2105030901140103020607120c080a0906080619060e0102030c2a150a030216020904060b0a051c060b01050c0a0b091b061c02090316030c080604020916 72
    0x20b452448100a00c8240a410600d811501a502c45e4210a000704900d850f04a1010138031580ae01c0043d412072810402c0c03801064500d10008040c5841d810810560302d025903410183c1c0e4801c0307480d500041d0304201c0900c54107601c5801d145c0c00c10801c079607402c041602280c004082d117030a03108410034007006411040e6264024410303105c50810901c00d03640c2e808280d245211051070354101c0f0f207a0781c05061844e0055840c090703041c810300c20840b9080328207103894a08182d00a40c0444441d010980421000ba001a641c1c4c23038a0381d200c0c3e40f2441011401d100804140002c4044a4101c1481082082c0b061400140c4244a9105117500980d010850040000041c0c52520074195022003a003c0c21030154184100c012185000320101011101c1056200080a00f41c48290950540c86a02084a04a50880c01c00650014140c8030001803a08540e50001381c6410420700c8a0105042c00c141c040041c0060322544030001c1051001810551130300e0b50005091704001000c03021004145908110341c18 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 833659343 1250 833658093 833658113
    0xc0411090108190e0105010e0f090d0e030709020a180f0503151b07050616030506181b03130c12080f0c010f090807020f0111031b100504060204030201090609120f 71
    0x54180c043c20020311559944032800f0704024000d120b000390201021407040c9072200d01007480341e50f295024040710000802c00302d500e8500d001c03182c2d5161141440204100000348010924041140c440d2804081800342201c03d801043e401580c10052030700c0e04200988004c281c80e030b1071010910110f1180d65941d0204c4030100c00302c01483d222254045444800c2090000c0e00c039001d600341c44040c000c0807042107011020703650211101500003014190b6141c0001c8104000c940003600000a14840f640601c0020340c207030000c48140c0c01040a13180580148100d60310144050300d441a1440c02042c42da807101d01a0303100b40c1c8a00540840300140ca4283c40c0003e611003041c01c9400c04090040a00a05101e8802d03007103204168403071070710b6001c607030305560141c030048031541c0c1e003030340618140034a40214550040400c81d9011060190309562032054800f84130700380c41148510401604c3c1c17411400014480802600802c041c800c00314801e114040da1000e489545540c440380b00e81125802d031500302d07048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 833660593 1250 833659343 833659381
    0x21c02280201080f010312050c031b06060114120105191701020702040e010c080a0b0d0204091a100f0302240310030203060601030902090f09070e0a0203090c0411090108 74
    0x200402000c00100940008400215000741e072039045588409050041180081c807000300b09540080c1c10300400c1f4001c602130b21401d14020140c9091585075544101044040e5000c80c00642010080100641e00b240d110f0404c441c4540185040480e018070101350f10f03134180a100d03c100d030010002c081074003c04a458000d444a00d460b48890751340b60030f050307010750007640089201d03a00340325100101c964140724000070300240390759614180d154040c0020041c0744ea20001074001040301003090258917140a81c0d003100d845561031080f10030164400300c82041000d0441580500c0d4480100802481c1c04d042c4410b40e030b0129200521792035a00902140c0c00200d200d41c403103102000c0b0401491002040c444400c9038000d405591003a6034507001103089801d091002540306510802051040d03c5075400240d01c60b40402c00c407071640344c81d00f50028031803004941c41000141c0000c00c0041e22201401200800c007800c0e101400321842180000c41213020b21100d00341080b110320005903c8503c41c040182203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 833661843 1250 833660593 833660623
    0xb090a080408010204090c030c0816030b030d0c050c040209030d141209100b1903060209060f2a061b0304170307030f1152050d020c01021c02 62
    0xa26590b07078240601070342161140240d0145031504541e05680207000f0030b9041e6059540315046030f580e24604131000d01d052061841010f076918a0384105032400c02a200c00103406850f0711008861924205140c1134100c940c00d801140140901c00894030001242ea81800c06420300ca51780004000c20701800340280325611281c10350403c20300c0140c2002040d01c0d50712842104d01403001a12410500881600a51528030340302c40c4200108042007030b0394040d01c1e0754180103204919117002407030380c46a60380181c50031700001c0401180b15460307101c1c03480c00102c41140d002c002e802c0f80e2030940350b80b414102c0490031003848a03000000040800042036000304c4074001540740f2903224240302c5002002840359000c0f400c4d103140742904d070f406a1080710302600c1145140c81d050303070f00f0b441002e1120000704410212112800703600c3c8000300c147d40c03036181902515030011080360a01d104a828902e01d4602c10031a080150741042d4a40c00d550f07680864811404000414910010504c211080f07140114000510341 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 833663093 1250 833661843 833661847
    0xf0418020c07090e160b0a0521042f0603010306050601021006080706140f0306121929330d0501050a1104212f0103050108030a0c0b090a08 61
    0x28003840c06a00182c060916103086030082c0c840f07034040c0b10845501b0b020701500088107000343c80c801441400201030b0f4100401080c154070801c000c42080c050000e850440341000080c6452030041d08034801c2c90020314020001903521178002c80800e00510043c04050042a118000a02d181c2d00030001109410b4440c1410040681c2c1e0342500d64071020785024010008055410742e0511205180030748901c9443c0c032116516546611003003001300c0d0b0404081c1d01640c094004e03092541048050040ba45034020300003800d03002102e58080c09a00400042c3c1802744000d10b09000c505448401010f030315044100c1100c21207001c446586400245030410550300129201f020010050107411040c080d0307004450500181c3d401d40303401021409a80945600c000705950001d0300b0300100da0850b14085d004440c4194001e00500d9090b0000f10004000c502d00c802c400300070781d0596070511a40d401410300c10080c50070071000340da0041001c1c074100b10107400701250701e000c103041d2441030010f04009680084525 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 833664343 1250 833663093 833663099
    0x70305160201170a09021002010b01140918011203021c0e012a03051309050103020603040312151409070311070206071406090607030e0d21061a09090c0f0418020c07 72
    0x1070098040c00004a000d9000404121f0046005004060080c94140c40364201081023084100498101f2a104d90340030085a02c19101c544000300e407180a844820b0700d0098601d56800c01a2500c0c2801d0f07032482d0b52115070b40d5003001881d448034038054034031000d180010142c0450001b202c0800d0980344104032a0300c2608240c0d082640000c010850b1041c0245205100b07542d504000342298001d00c07020350410310800c0040d002a20070b60301801d004402038130002c0e02c003070320b0003506403030204c7e640190040c55400c1410182d6440c009165503130003081d928043c8041c1d0005051104117004081000340504004501d1208201d00271a0044600300c5c0c00c0704440044ca404c540c0155607503415035488000c0f034038107501c502d050300020840782404107440e1076031441da10486501c0001002e4550100912503a01c02004c900c46c01540300b102000410100c180d81c8411a01b4108551110301402c0d10a01003000c10810701d0403088082078800315030498550f00d0500c481c0c1c00c01c1c040a407150583c05051802000004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 833665593 1250 833664343 833664361
    0x18050118110312070305130905010b070209101401030911132a0c02010c02120f100f0203090a08030c1605100c030c09231f08070507030516020117 64
    0xa010031409a515061229080300a260b1148a00300340b55000c1c900402680000c64015402071404468501c0c1c2c40352129075a036103032030485d8000e030400190301e980010303060306602d00280d090b600709040900c0807628618240d080040c168581560a06258907102004140b1054894880c16007a010703064a000034201041e0724000e00310401c10503c1c0c51007052604100015005c3d104803a4078080c1c8038050401c100d074005448411718200100c3c3e02c14056036142612a20901c140552820707420018000804d0802048081d40c0c14102c0c4116818818070030048152000100014000c0c0c2080e0308681d00d81700d200e55501e0610400502141c120480284d12003008400600d02440c80001081000403004008046040e103107a01c02080c0042d00b400c1c828051070a440000c50601c0031b5260301c7c022a042240301080c1a1070600c1513061106e444030304005d0407680c012b52003607808042880e00300d180002607640644280942800910050300711142d45045901850100d08080002c15688103640f0300341c024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 833666843 1250 833665593 833665631
    0xa1b0902032a0c060402060d06031203051005190306020a0201181b060504060519110f2802010203031504090606030f02030c0603010518152e021f180501 67
    0x2c02884000d818040b1404450290107607918812207a02408242d00c9a408000f02134002c10740c21291990b550070004002000c5004001e020b00c841d0f1800700302c519003240c05000041d03180d4405406690201800e41c2032081c0c0c5d4041e141502c0e8000350050712a0302c0560124010000b00243d854504807255a96041c001a00100c00502450720780c0c60f0100c513110241103d907802648507100110b00c4c18031800c482d441c04014001c2c1c102c4000d24100f905c03204100c41a903d01501d0b245080320310380004140c140001a5011b001c3d20101c0300c0d0004164009581c0c0c0003c1d41c0f07101c014401c040038114684030594580d02c1e90010b103400c5400c03020600000e9103034140120036503817180c070132486482603001d082e0300b50800506aa040381c4009201c441180b0b0300c0302e500c2005200c010070110781c541c18455800b00aa44d405407460040c0303600e0540c2c840c0308400a9240b01c0090b914032051082d035201c20070b80c082c80640d050940c2c11254010304081034206001900d94103250256000901c0d9509001e22218011442a0303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 833668093 1250 833666843 833666881
    0x3160602070209190c020d120e0a081c0f2703090806040605010603050601090807050609191e0905060607030e01181403010b060c190f050d0305190e0a1b090203 70
    0x4d800c200ca4114660180d03610721204e001300000c50203407115481010401d511440c2ca0706050002d0f200306414965480d407540c1e008441144902c0104205560890164441d2a100c822040740801488010f400691a038030400f4061015030785000039001c08240c45007001c3c40040c10400c084941c06d040c1443c02074043c00c4240190070001c0d1030a030018919600c1000040101c03800800a403192034280380921182da448074900c260000c00b440ba100300d090700c40c00c0781800100711118055113000ba4002036200c00388910382c400b5000c9070800341804a1031382c5542c2101c5036107034141030040b5110381840050329000345403076482040d00022040052554511545007540003000c40003004404480420801e281c02007102c00a445d60200e42da10720400000d02e03070114520b0080c1a4600380d03440e155146407801004007168800681c450051005500b1150990540e28280080910040d240328512035a6088103070b2002d4820280e0901e0f41130400300c4007651a000c0d01d240e08080d5076a00d8100418119045202 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 833669343 1250 833668093 833668141
    0x8010207060903120b01080109020f09030a0c031a070806060901090b03040f0303110a120e0c0a15120b1c060e0d0e09011a1b0304090e1b060c03160602070209 69
    0x5000c4c105004a0703440f4078922500c0c16141e0103d90f03401c24405030001d40194100e00600c6204010413802580c04001c0c01312124864007003c00000d04519218a0001e403002c59503004940140038811517a030440c01c40c1d07900410603205a512640760f82c0040fa1051007551204c1000b04000060109000d01d04050711200c9019072414886600319102001c9140306181000c00010417070b404180c800c40003038004c1c10100441404941c680300040e00040c80702d000a034056800c140120000c60076458109201845441f40e9200811000a41402194809200714151110030114660716010004a42e10061094000e1811150040300b2104043d0071880516030709482001c00c1000000d10410100c0a40c2000d130840c0c05131070404d4519144622180c600b40000c407003500040c0804510003005114040317078486020001c21400e40030341c3c9200e18259050304010b0080300701b001072044168001046610400c01c0b010200521215800c0c50f000034003070703c0d00080d4484d03080c04c18448043c2600c00c0c020a840484 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 833670593 1250 833669343 833669357
    0xd14010c0503090a03030207170a02070609050402190320030903071a061c031b080442030b06070b0105190302030c090402010c0605011509050a0e0a051008010207060903 74
    0x1110584240c041100c80d80d42c0f0307511804a4100186c1b02e500501900740c4102804144841d1400b0f4900c15600b0a50503413005074407807081082a140c0c0214040c000300003d0f281185409041d03045810048410703400c5009154465440c40510006060400181c0226403071168881c284507800035201c0d840208180d0b052409929a5000c0204401000e03001d403800034014050203070a0745155200c422841c00c25014041075500031143d45030483d0040c5142441001d0541c1c2e1241410a40c4618141c2f048060a0300c40000a40d503282500000e6814507100e003c200f40381035480314001c110040c024140042d034003c480403408404001502c1304541c10303075008032040031080d40c0c80765050701d045015100c00380d41907124080403403a9007042810b17160064010b03d4107100140301070f2101015a202a0302c2182d40d2a12204859911a03003c41c5000c080c01d800c4a0b900d0b10540b60850f001e42d43c810207800080f245982d0307808901c003000001c40d410000d0010000a5440c1d04403410840000c0010710341c02d034041840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 833671843 1250 833670593 833670611
    0x1c02031201061808121914070f02040c05030f070e06040b120103020f1c030f121b020c010c03020606060f0c1005040b0a0204031a0c0904090c080d02030309030307050c0307020d1401 79
    0x80810b060178182e810600080c00c111041e0031040038681c0c007038100014000251035904100101000516010b401800c20200010303441c418042219a683e0b0701208021007401481041c00d001394129400ca00581b41c142403614500740000d61510a40d409040288400039189603440407806009048034002c50341d03d28903210110034000104c0d60b9840701031081079441c41d2000084d02580c1c1c495003104242c0707460900c0c2b89420b00407200316601c00b000000044010315400e030340c2503410401e54420440a02e00f01002c8496650043d540d8000909410701c03c1d2030100314507003c20b4129042d0794051240600f00d070326050b86698644024401920b080d5000d900c00c80014840300140e008590840c1d9125140c06412251002855500704015060480c041d0081244000710340c0e65000e01070503107004030070700e40c00c091070620103620b80020100e884095400c20b00030000280e201009484c2d003d111400e0295640d184216000d00714410660001c0d40403100400d020305100c64045203440781daa46000130014005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 833673093 1250 833671843 833671859
    0x1020604020d0f08070804080f2a221b02010b0d080d0c0903020a0b180306010302010c140f0d03020a020c0f030c01030b030f0102210a06081c020312010618 68
    0x501100e001e5004074000c0a804005440c9030b5014499602941c5010309080c03081d5540d5816903c142c2c454103440e405540448a4142d0a00c011a54001102d5a105049020b510440001070f20360100380c2c400c1441d40c80041000000c102815520030074007404000161034000c1014a8030302c0c01c405500150310b080d0a8110505105020103030003070304410000d052211a59110f406445414500c900300105520000b0040c0c03646420b900240840318200c0e0b4841c0100d18001014040150255110b68404001000941d800010301d410164001c014081030001104000d0700c0c0400e40c10b10b80d0b4113403040b6807454a100e0762541c00341c10300442507400c1d6582c2102100811411030010b041c5140e06800441281303001e580294003a110760348000d4240da143c0c07821100c1d04e5003260400041000091000c3c880701c4a1041d81c1121650700c640c1003201081498100380255581d140380322440042c0c4040c02889a4078203000304260b485d04030384104044010341e1981d50051030241c10303c03444d0008103003081011035106 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 833674343 1250 833673093 833673103
    0x9120309083318010e03031506030103120503130803041a06061206060d06030614150901030c03060510050907210612171608032d06121212150102 64
    0x140940910b020407105007402c075640c400707010b071001001082182c0c00c6612080203008000d010702030346002d541c8a2808030548860f01441d4140248219020401071000401094070b00c3d203148040c1c98003949a075a011001d985500f10420040d14400c40401000204911000010700c001d40039803440b03d964641606001981c02202e078040d91850006000403820f00305000501f030051007614000c2a101d03500d442e01c00444001c05400158012100f003000805402c41025101c80c00041d5401c45da01c5d0326548440301480001d000c014205903c410200e035041c0d0106210300302400b0001c212901c5c0342001c1d076000e07000e0099441c07440401d02c2e560b11210b4440d5440c2c8584400c440060040c5220002566180000b001612408070381c6580c1c11321541c0311401c861598000424070079000c0036034a04000b0620802c03002034042c092040030220f58030320341c0c50745202022604880305403203600c51400b4248000c0d042604c4031400c0b540300c000c0499108508009098814005c500000240c0e1454915100490b1a5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 833675593 1250 833674343 833674393
    0x90402090a0e1e07050a140d0b06150409091401020a0e0d3e030a020105040306050a0608190b090a020108070f0201150b070506150108010b09010912030908 68
    0x218420800042425500d6000308a0401c418010380e80f51600d0000401c0718030240e502c10f0101580605002e102c24106810084080d0000ca50031284a21a90300003d418446000008144a00c903002088881c1c40d1681200d04408a101070705407142d40310241d1000802c038281040c0c442442c000e0084401a070180f08660075008150b5588600030304080500c6404400d0042c04c50711104005103000c403165030301140001000009030b401101100400140060602d07003a03070148684c01180c48100140e030040d04880840384e1100c004102652007140010007041c0d580c4c003007091070066035000d0a5110495444141c0c00723220f0070201c5a25110350f50305a95402c04664020f002c0bd602101041200d0b0040316410111003e6200100307815070316901580001001d58499003035610081404001c104082c0001c0b58000c01e800303002581080e006c000281646010301c83c80e025a14002550841e591041d01c1d0700c8c02070892500d03206100300061500412548241c0f04403c0c183c000c502200b41102c0c070b000542d00f11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 833676843 1250 833675593 833675599
    0x8070809030316110106241107050d0213061e0b040f09090f050a030903030f030b0f13090f15060501020a03020307150b130c080a02040b12040606051503010303030b090402 75
    0x460ba184000f8184036540c9000d04424030440c00300d9558540d10900804000d0140c010001c10b100c1220300180e00d200e481c000e0842c0600461030a0900c05510002c1c5550454800312030640c031070003d900100e0071100310040700c40e88050a250b8045805200503d1681d048904016042419903417042c0c0c055260107580030b4940d0f4a145041d041181800640045036504c1c020282110412019610149000c0c05c14100300d0200e94211402c009054004d690f080034901182801e00520305040c00041d02a021192070b54401e02c400001011155103aa000c80340181c0d2240002c0d6101c40c040c2000d8400010000306d41d0191030410a001c150f039440482ea6444165040c0c00442c14241d90f86d443c8404403001003d1160402d60b01d41c00304141c1d58901c810b0303a9142100c21000506840134440c0240300f2800206000e8038240104000c120940c145405c1b44c50b401c007802c1019520b81c58030b140c410050708103540001c0e8003070350000020060900b12001141200e210391410400c80c040380c82448641c520480340658 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 833678093 1250 833676843 833676847
    0x20f07120b06040b0a12030c030e0603090a1704181e06260a0204020a0809010c0e010f18090c02151509010b130510020a0c0506090d03050d0b040c050306010807080903 73
    0xb15a0500d508030b918030300e00c0208503980442d21000c00a0140d40d01d54401c0d030000302d00340414002d244d0810340050b85000300b074912030711310700d05224525560240100d00602001007814046c165500c0340095030701070102011203612901815410202420328a2420f40340200f40386400ca82c0340c13200d4414042100c0f0350381d19042c600d281d03201007001995103984540c4c8850084a0b14903005a4607403000342648003494480601c0c508207500e00d282100c03003580300c1509210003180512566030b0000071100e0454502d01c1e20002d0f22020103865246108503504c24464141000071080c522900418000c9141c410070300824856590381400420500303844400c183c010b05110014016219044000c0a030760022481c3c014001c0c1d0f8500108044405041443c40140c020f6085070301080540d41e402e00003000225500d90910040d480000c42c181280e4a000302403180c005010043c0c01c0b00758100aa08000041041000d0808188058029402120740074001501c510004419034010b5804600400e84440258 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 833679343 1250 833678093 833678101
    0x80d150e010e1303090509191805120c010e010c0c021002030a0c0809010c230c18180f03070c0303030509030c0c04050910060306020c0d020316020d0f0210020f07120b 73
    0x103600400e0f004003641080401e500110311354544d000e1b0540141c100600b040c1c200d4458904900032105904a801d1041c0d078000b444d0000700b07000040c10000d0990481d0240d03079800040c0046070041c80d12003c03469655003050143c503425034019190f806000d00070744141003062010314089880c1e1092050043c0441c036803001c03a80c042400c40002d0b101120042c100780c0d542c54001c2d203642001322001c03c1120b149076003108580c0b00e1040e06000360380c5110b17410398005104084811000340141d0005041202a8014200c406480703001004203c0800041200752907444820b410044080002400280d0100e4108404219a09000001c4817042c406041c0a481310799080401c03c0084c240140481c0518401e82603911518071680c0f24802c01140303c0c8170b00691b640c0d02c102c3e516061242c1c0c0314010055400500c40b941300d044030010f80740091342d411103900041105525140a20f500114006500720406c840400c0303030140c000500d075500b80061021101001d83e141e041e8041c070100101c000340042c051101003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 833680593 1250 833679343 833679361
    0x40e070509010507051f0c141b0a08190206070c1a0a0e0d030e0114060616030c12080f01080d02030f030a060b0c030a0315050d0f0f080d150e010e 64
    0xe4001d0a005252040c43c184e0350f0740303810f0302d0640015040d441588400b000d460006115202c5d0181101090420909400f11a400d051550150561a42c44403a40444241c0c01d1041030100003510755100c2c1180c0e8a8821900c07503c0341041140d030704003015100d120040380c900e034010f81c81b28110303035805090f4860800d12802c900326010000340400d05201d4450850002d0024180400b03070000e041c503940002da5440084100c0d0940c9e031911070b030750019003440701884215114002210864143d40da564401c000031454100d8504c441d200c0d014210080c068041203070030b0750041e90140100a48074507080d9690701c403130105e44c64404180c0e408000d6401080102e04403000e00c2e0155905c400700341e000140e507550307441180e00103601c041c80030034aa400c005a0204402d4151041d11445c03c5480d24085c1c8403400e2801084442404010160040c8030055440d030400c00c108045510850f4070004140d22401003441d000d000d040780c15003251020a0000c0085802c0009024040c1200c40f540b02451941d2204604 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 833681843 1250 833680593 833680597
    0x2090a020d0b03240a0501060c120909020a0e0f010306061e110f1e06151e12030301090c18051009030503040f051309031e11070306090b0606040e0705 66
    0xc48405180c0382c0c1100000360f40d05001260920180c08a0380f811143c0a10842d005500000c100c00c1c1490715103001030011561020352210f09540c810101240728400341c0c01134480640d6907102031411030000809142450748000c441c45480c0003520100d04120701703180103505850b40c9028500c00900c0f17110100c17032100034480203d02c030f00a142c140441d050403200b540c54100401001011905c1c1e100e410062403008007080c80c42202e07004100a001c0d18141101103d402e0701c640300c0420f104122004005000300040070203501000c00051201d121048401c0b002d0342c0741d80091051005107071a2100794001a4040c0c002a07980c0440314a11a583ca8144000c1110000c1001034070030810042c0500440019001c0000f000504014001d2a810b00e01d07000070000d40e215200f0a650781c0304c1c01d001c040000a90000c90306c10034070070142ea00c0c000e43d000f0035208441d03a8200b07040c5a9041c3c0f043e03180010910400d0781c008100e81d40901c06101c50750707941c1c5040c07002e81d120798461030307485202641c00506400e100c0c0340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 833683093 1250 833681843 833681857
    0x6030e1f060905091b010807170a0219020c0f0103091104090f02060a0c1b08150903130e090d050906030a0203040302120a0f0906081501050d06121a0c040302090a02 72
    0x440012481d0700ca190150444070f00301c0e40c120469102506a40ca40c240a031588011088240307003002c0b503441c22504c001d040e0f18191805281c942000000718070b40c401c5640555020210802801f410005000d6000b559203000a00c8240656401c3d40c0e1100c40e0350bc01d000e030705240c80d000ba010701452040b074424031004020f102003d03943d800482e84444010f1b03842a0061840c02c0e140d554007003110a00d421b000800710741410507107292038108182046040b101203131100b41903031044e10300843d65035101a0142035119060118506107000c1401085004880c642c45005100e0b62080300c42c02c840198080e1010301c0351040031588500c09000294011200d03800071540a0311074410f0f00d00403030304a24061010303000011000c000c290002420032003954000d041038000d046500d405046810700207034980c8103c000100540c104030000421421910140c1c206800a01c80d045203840580b407a402c0c01c0f44813201c504a4100030fa0200d20220f406c4004070401c0c3d505403034006140034116280d040700f035030081d44101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 833684343 1250 833683093 833683153
    0x10801091a13060902130315050f0604091410060e01090911130f1407030c02010c05160305070b09070614281701080c0324070f02070e0109060f06030e 66
    0x2c43c01013203070203041c0043c010700c0b10032010000c842415494100f0404070b6207010610035a2610003040703840040c1000a035000074040d100060004d070035017041400349141c074950106610845840c1212442c199015a044403640301152103980d0700e50f810394041d11700104000e03003000c060821420f83d91030401c044015645183e10001006642410140c042d84c8507400c48058a00c851020041c0807a018003411000301e03800d100802030300032540c4002d403103802007107004805810801c0e81c00082601071811030741915008189002e592505c00b201d0b40d507d0000740078840008811015403070260400806646040340300031204042c0b8070b80040c0c940303132003a51240039404104c20862100c182c1907042d01980e02906420020341a50308503802410720f020042003040c03080e202c140003541201404040b070203810003401d141c2070000041401d400c0b840e01c0308a070003442c0e84100d0040000740740b03059640114101c400c1c01a500340b030319542c0c900a17000c0310b810a807014516001680040480060310303100d44c0c402c182d40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 833685593 1250 833684343 833684351
    0x60809152509080a060204060f0203030402011d181008070f0f0b091f02061005061201050904081c0b013905070f0305010204090605031c050c01140f06010801091a13 72
    0x5a4400c41c9400d204c62802c2d5462940090b050201d01d9000710003548000b5140000e5148d4101580000d01d1030300c880c1980210200c50142440607640c8820b401c0105c896001090806414451190341540e0400c2c4a012304030300c103051001680b44c0b80b0503010000c41d5140724041c2441480e2503c03055850b40a11001c903407041f0381c81004550326035049101181000c0642c0142080d10b05104500304146403600011312995080c0701001814010340e03001c40c1502c60a81ea240c602c0d0710340b403034181e2040c011800b080021074120241483e80c40c0450b840b40c03000d000242e80b10a43d000340d40741c01000b5110318a1982800d1310b454080c4c0f10485600e00c6034029041c5c402c9044a20079a92046810507010982d0801c403500d03500000c003004021044d0241c1000b40100b24060010031401800a0000d507000e01e90560600c100030411103001102980128401081d02d44001114a00b040e807217030980384200d8265010584250001c1000d0b11035100341603040640d81000703031107419002c00700b0a844d14501603642c0d07443c1c0c1f1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 833686843 1250 833685593 833685599
    0x3010e0a061a030a141e06030304050d081303020913060b150304030804030c0803090c040b1203030f1e070519030b01021e0106080d110d0822110406060809152509 71
    0x35800105102e0781c04242d818032406e44000384a101d00c02e01074000c610039801800140702c0d950310400c01c0580079501c4541242c3d904440b01110f45400c485900c040e500c1907141c3c0c03c02420100da2a9035400341489400308100540801c4100900c0c0b0b503060001803082d08007400080e0000f8011031905422034042d0030f080d52011990ba032107070700c5640300300d504603a1601b00e052031181c0f034282401008003460088a5220b9124000c04001d9903e00000f096030403010180008600d2021178140384804030092140e5146051030700341d02c007404580c400303031b03290400d02548030503180b007c2d10034071641d0a03c1c0740c141d010305011007000780c0550450094552105542d5618000015003680400141e0010709a80d1108501c0c03a030f8003e829030800d854a003291007804244810002040d6201d802640c0001e40c1c4841d4410389074450030003041f0b030303c0114080d581140c5810700100d041e40e013041959215861041c1207c1711680c0008414240c102d060361850950f4108603c20900d60344803d808200310311480c0f400c9014199 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 833688093 1250 833686843 833686871
    0x902030915041209050108040b0406200408010b090a051302212b020604111905221a010e0d021c26040602190305040f030803010e0a061a030a 62
    0x7400d0318200c0360804440782d40150303d600a215203005200900b030000c82c40c64030351525888503000402c001c0c0050307a100206402600c0c840200c814405480044984498072442c1071402002e02184607481000d81000084200c07403940502480b8568840f0380e1440807805502344250f48106142c2d160700c2c20349603204420348403003c00500e5058440705c440f0446400c01e41241058036140c200700c070070841d00200108030124180c24500c200d162402d41e18084c02c0584105502c00c0e681c250782245603c4106a12a03480682c030000071200c1e002e0100380104814140399000c501988034000320580840c41c00103500b2038928040e0900202280041c3c1200390040224900008405048100302c90913981d01c1c0501d000c48004500807010106448010340c507040c00c1c00800b035038640c445030112024035418035050040501c6030042c2d07801410b180800c954041d89070300e02401e16420034029010364244d11400035410a615008a07400c54904071407410b20344402c00c0c4201800c0d4801407410240e07d4a440d40ea1703c003030f4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 833689343 1250 833688093 833688133
    0x40203031914070804050f09070504170c040e0d081609050906040f050103031205090c0904080c0709021c1107030e011107080d081e010e07051e0703050418090c09020309 74
    0x2c4c0306910302c6a80b58100003c104030000300450140c0111010700401a003d6006800c9605882c00c0150b222490030302e94008510300481014000d03009414607518201010000071b010281d94059103038000f85a98840851444003982d17581440090300d40324003008107082c04810545c1095003d4008210300560307911000035140d0030791003180051000343c4aa003c00c0410300c50950840500340181620b448840700113005108044e101800c1800006451580c1410410a20000f0460500f05644599400b6243c442078444402042e640c9814065010032103141202142c0000e0f41c503448104007000400700445052801e00d4000344640305100c3c02007210300f01000596044031440c1d0b43d500542c07520580041c00f4101041325204240071034001030001c4450800d45941c0b00700f00b40750440c2c803007134000d40540c40c820040d189008180d000140e82c0041c942e0001c003c000342c1301c02182514242003103900c44c000701e0b1820900074280c0413001d0f1080c0070300c550382e800a580000a1400700c484100f01250000866 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 833690593 1250 833689343 833689357
    0x6051e07050a050d05070209180a3504081002070f05011b03061203020c090c0d05100e090304080a1e20040b030304380304150f05040203031914 63
    0x542d0021240008018007002a904010f0182c035102e8208210b0b9400304d40c02c4d00016045241c000751410954090307010070408070b1044e0780c1158000c0902c580d00402105081c901c1841c02483e9206a0020b61809100d0000c40e82101e8010005102c10002c1500d4a00250030000c3d00300c8160040711035640c0400d03030901600c1300202041a440300c820b420b4444c00760440d0501c0d4003820881c80607007040008a5008074030398a243d081691000340d10f45c0c6011a10545218141150031010310302401d0080348032660403414292101c08240c024203458101e2110703507a0041d403213046003690040c042400020482e50740015407070b9550502520714030b0665035008900c01d12000c1000c00c200d0450308541c40e0302d05801004c488030010382c061481c03d030130b0181384441700c03050100c1501180380f400b400301c0c084040c008500001700c0144036030039202c3c280b41c5843c440c40c503655420f2082441c1070a891400d41d200503c1424021503004004500d01003071040c0030140145c501910405111602000b00d06c010352900c000d2100c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 833691843 1250 833690593 833690603
    0x60f0a030b0415050102250b0f090306090604050a15140903090a05010305090c06210117010e010c051b15151201020313240903091d07080106051e07 65
    0x4540c1c903081804212400c4070041d0396a050520010406a60003040d0000140ca480e0312460070b401c1500810892000258040f10003018000360101805c0341c9907000e403c10310803c0f0140c0d1446d4440c210401d0b580c0c941641c01402d00d411170400e07400002c0644240d18040020102e001c00c1e6804d86010319014000211400c90254000086134501850724600d000040d04007420700b08407d0404920490780d83d0400350065000d00000108210110120b80c0040720480c0f40440d62017007076031140400320200e41c2440c0f08088035130070a1501008804180140c026400c015550380d81417040100311683d4204044440e4107040c01856200d01107101c51034609072007020380d00200d400d810a0041805489081d07000b1429441c0d00c1030052080c04042400314682d1590000e61440d540030109809480e135410300d010504102d4a4082c2e8001055042200c0320100ca1041d01541e10380c0f086014800b022000440d0100d00003054040180710860151001d000881002e580102071003001d01e103801c810390320580c2c040ea1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 833693093 1250 833691843 833691851
    0x25050f10050f0f0403020316031407030e0123070f03170c13082a030f0105010620061501050a0c05070803040f051e09190f0606030e01021611060f0a03 66
    0x142c41890806440d070000c0700da10791407000f4505030320000d4070790040c060040380c0c810003a0115010b043c85091000108034500844994034041880c1c007030803810003403d0060119001d07401d10317510061540080c20b0b107090700d01ca0b41841c6c0a0a40d480c130507602c0442c0750850501c1810042400480040007039903100d03024000d1915a1040300380c104c400d0150890b40403006a92008820703940b46288410000401c0c00d02e11088103444052800013030405900c2c0003403100c1580703003c0c000541980d0001018506040c41c0c80200c09515000118a031205003c540d40707048004250003845642d4460b900a00d200300c00342c5050491008665101e9040a5480d40400f2082c0c2c03000c41d00b4411083c0c4410b45c00000c0c80c049414a036209030301ca81648000555a26451003841c0d40340c006000150480e403062507071a0240020001c0c80301201585004050034007968001a08d003140c0781c4001c1c24144210b0320114158008191244425500c42001c0e007080d4145640006c1d091007980c0d81c006e40580600290041a02d02007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 833694343 1250 833693093 833693101
    0xc010f050103050f011517070812030103020a050a080a020d0611040311040b01032703090f0b0a1814041104120f1a010513021803030a0909060b25050f1005 68
    0x580380c480e1500c004c2400d0b924110400052200c0e450200d411518040c118140800b0703980d403090f082c4483d5a11540507801800c80808038100008000d6060724400c03140b04a041c0d8070340e002c3c043c41e44042d009900d42d5038090f05911002d86050090825498407442d008594000c64442c1451642c003e0b81c011907170390707511140540c5546000d00501d0492030342844c08121500010b400c0617900a061500701d44c1c802030402c140d80600d4420602d54000e00071011004d000d040d9115119800c6070300035100c040c0041c14060310003c988001440c0340d8110344c4420a07041e8138038400c1c401c02c03004000c50780740050800410400014172501e24000301c61400d004101d41c0d684c00860b418070a0018604000c0072440c00d500000500c2190381d51242c0c40c0040d4400400103071100a10441801c070052280b00c180e03494400450241000349c0d01c201101e042d684518010310a595552402e12118050b00900c0c00354505828000d1210740b10300c1c02042110360084048640c0251049040e500740741a1610094140c3e85400401c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 833695593 1250 833694343 833694353
    0x22206030b0f030111030609090a0c060503040605100e1b1e040e0703060b0a05090103090c03060e100b060414061c050f09150609180304080f01110a02060118020c010f050103 76
    0x402c04410300394002e102d5a010000c0041c860722000b003140340305c0c001170000704025078010050561516441841c41c460a5103840c0c0140c40360308112011103a0343e0908001524048030758100f41d00311440740c2d18080c8a074580301521030380040081e010789003541042c0011210200002043c1900241d200c802030303038540c1490650070b40c604000341140181410b0120030081015000c08a614500103440c1054440c0d0703020004a0162040d0b42c4064511503028034044148202e59200540c8558281c003210260070603480f551080ea92045055580840c0504c000c00c051840301c00382c02004c0800510340c515080d011034507030302c001e17001015a4002540d20401c219100b00c2400506802405000080c440132010b000c94440b58940242103e0007110302c800841d0303010329014014601c080c11542529102e94540513240daa030380b00c6151084a075820540e180b4030310140b400c22921a000c0c10342c090600360b0309194050166558107080184c802d80d003001038014501080c858207442025810000c1900d502d03600300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 833696843 1250 833695593 833695609
    0x603072d021c02030a2a12080901090c09020a1b110102060109090809040c0207150512070e0904061806020406020c01030f06050f040902031002120f2503022206030b 72
    0x80461030b920041168846190000255814001e41c0c0c5400b000045030b003d40d040001031032040700c2402d00c200a10050400006500c038454070005540c0b1041c80307695901c00c8600781c82d004035014011304241c60090003180034540082c0a502500e0500c034050080002103103040d1800071078161002c40d8001c141100075a410b01c02d4500501c407868050000c051251180405442003850b4248a03540d5a80d6501c4c0090080c80b0050007005208141c4070800c0441e400940a544a1014062101e4040f000940701034010554840c11101c05002d5034029681c55888900030a0f5801d8200c411070781840344200003819900040c40174141c580c0c0900340c1d10352943c001505035030766403648501035800c08800740b1031034944d8103240d6185081140c0204501c011800840d040001407070240c44070a0000440501c4080e10300105402904c00744005081607442c4900c2c000100b001c8030b41031001c00344811213030208603c40c2d0050818543d41245641da0340042078161250b01c034540e0722507000f00e9103c0100040c00d1a01041c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 833698093 1250 833696843 833696863
    0x10516050d022a090c0715020f04031502030717100b04060f031506020d030902010302070204051f0603050907031101270f091824050702060105040c0c110603072d02 72
    0xf032031003516a84040000c0d0b803082d0042240512003000300304d1070180a00f4000700301c140d8004070720440d0b903011044021485580180003d540102800d060014030083c80d1080700d05c900f11695502c00058400c4684800d820070160201620b04101540441ea5982e80d40c003c000418294441c11807034964000090166881580c016081b801c160408000b045d07008100751514210a280010315070b00503100580090040b1100a900249050108010440c00b00c0d06140d030b000c03003108008806956000c0c2101038078011038004942d50031090003000040c00240b082160362005040c50340591100100319841d150030030722210403004a01000300721942c5840302c4d07a009402c0c0c200d802c1c081c4130700c04200703000d000084030b8005103204d00f000c442c5c03045d04002d805510407002202d1403e01c101c0c24944030080d81c41e5401e001d198030603483c0c0000c51411902480c0c1400c5683d03800016058958500020000e03a41c100801d010b0a100102c1c40c18000c442080211b190710300300b9980610980100002e0007807410f08801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 833699343 1250 833698093 833698153
    0x702120f1c020a0f03050c030d1803030b0604062109021c1103030a051b07030f06140a0905100f0b0301020408071508041a060d21110615010516050d02 66
    0x20800380896045a4820404c1d5018200b00d5a80da44010810340f0b14400c29800d10001880c140d9545a442c01f006258030810b8042d0342c0602070008544e0030001c5520a91082d1008183e08041039120507204044004000c0c0030840e00007001c4405801103680c0d4041088920800044500400d04018688107500003902040e0000d506141c000007001c0c1c02c0340304900300e84000703451204401000746003c0040001a545c801d24503000d0086515120002e04103003440411040113a0000410b00b402a10640c1d029507000300c0140244c00302e10011000a00900058001c44e50300c8600710803190300c090000300300410300407008280562400082e0042c07240c0d02c000c03600070084a10203100c082000344030560200201800e080740180c80d660000744000303642030b000401401c102c004114002040c0220880400100e40720081c0a6281908454541204403612071100c0d550b51241511075120300301410341c50002d40c025819400300c40d1242d41c503001100c051200168010703921060010701030b0820000742c0c3c146d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 833700593 1250 833699343 833699353
    0x20c06570c0d0309140d0c0501050601140a030b040b09240907170c090907031a03070f15050d0921020d090303050a03142a1204080702120f1c02 63
    0x1c0d94445180388070b040300b0907407a80c5161043c00800500621440c0440040b1040f00118407000b600b00000c0520a84070755107080001412540200f620240c0406003503206441c3c00348036001940180417520b5882e40150b0745d1107029045807101e0007640c0c040c0685181c080301345c44560300340c502c04a400c103002d24058040c40050005e4507801000790401400c080700f4880b815956074031803c845014086009a000d1000d4040c40322072a015403102000e2070007074403800d1102c8c003060141a0394500368071500c2c07128030014404000416201008582c01103076460300c07601c0c200050301001c00342c403041402a1011400040c086040140441c182d5101901c180040d001e50744107040f01400c204068032019051010008850b10554401da011310981e00840c00590100d040c8002c001181001c0c028002034100306507052108486c4104050300c040c1c90212103a2555a610750369452150b410011041b80c200301d509540703441020041c4100032070540404002d2032050a1860703540080544000307070101f55046 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 833701843 1250 833700593 833700607
    0x7020f0d053c070f0f060b011b0213020a0c0c140123030705030c0d021215061206130e0615090a14061e041518020c0657 53
    0x40d03804201c0029041e90401e03119002428160090912100000c1c008468a50900200031180d40300c504824004c0c2d94a0104000d40b00d10303582849c08800c8040d600110404400c1e02e140400c1d00188265803081c0707000d02c4071141607070b64032107001504c1d0008858906008070000c401d59002010346030f034020028518804181591b803142140c803024048604111001001440c4403000c40c08444043c9041c003011982c480361a46002a020070030384d50032141103910401034807280761240645102b100e5011003040140c44450401041079004d84d0301310b072131035203480100740e0804081c40701c42e11804074650011800d40e02041044001003001380200c0b45103191100e41683c44d203070005410351104d003c3d6440200440040d0030320b1813038881e00b490301c0d62060800b0705d810001d41160480310100ca05401c00034140a40c0250090706a006000c0e40c828558070101c00540d82e00b2104100c5034400340c0c8500c010450340550f400c1c80d248084c0340d001c1400c002d44496840b0082e40b02170035041c080040000111810004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 833703093 1250 833701843 833701927
    0xb09190305070c03171b1c210c081b0403030c030c0219121e020102060417070507090b010e010e1309061805010b031605030309040507020f0d05 63
    0x14040802a0070000d02003400c0c001c220806410304055900b0088484210056071614100d5510001907100365100e044009004420300080c6404145004400c10341c60040514040707500d5040c0c080900c013890707030011501c00301c480c1c0c1d0301c60304028a04651352000c00d80b0b003c8010100d00d4030b40511080006500b0441080880c0d03101c0a80d11940d58180f0b020741e0920120300000f80c0c240401e2215940c4951501400900c2c0c0b00c07090b6403c0452440340741c0c40140d0700059025030401801400b0040c0c00b42e00034800107400980c030f9502001160814402075070800f01e1684400e843c020141e0056082c0c90398400f04c282c400c2d80c1000d00c203da4001c0c24038010040d400300002080c403891510405c2240c03641c9482206041122507000842c1e0700c16109a402e40021441c100a406004c038036090900901a852869908601d10b114100580360003400451178400d00c507081c4801064018903200450040c0590045060014049a102501d0384c1d900c9603103403335003108035200340d11580e0840030848404030189070051b5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 833704343 1250 833703093 833703133
    0x1e0f15140a060f11011113060c020307120212100c11160603110903100617030712050706020c0a030801030c0b04050312090f060d090507060c0b1816080a0b09 69
    0x1e019882c3c02c0070f1040c0c403181d0958003220b003401000b501e5400c0c98000100a4290f03006080c00190000100e030000307503561030a03280c142c00034001940681100390240007141342d04941c851110320152800140c000e9800340b06040c5410a145115060345901030484032a51002e080d081d5000007001405800051511819000103144204c00601d81c880145540070441c081c2660416140074007551405180c6020280003041c0d0703402844207880380c19902507990003000080d10222035000c00c42020f004107284003528550000a0125140d40e001c01454400441c24429500600d100762a00e0055504603d07108040d5a04e82c0c100d184505020311040000d07070f0780090b20010303020031a110b5940d154115008205800c0300790040700d4015100080c9255020419402600ac590040d0240c1e50666103a040c110780125005401410040003000031420a1401d13000e01e440c011030142c01c4039503240c01401603039544402980f00c2d03030b03051304111048018003c00100d002d41c09014070300903010407002001401c3c025 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 833705593 1250 833704343 833704349
    0x20408010c030e251d09060709320a030305070204050a2915030c07030306080321130c0b0904150e13030203040b04320901091e0f15140a 60
    0x16040b1801344040c000c0d2803e580030308960200d071031149140228100c51458180c2e0401c20302c0c8a1880003402c1c40c1d11a12408003038030021b815000000f01d103084c601d07404050001041090496110742c00040b6a2101d800b007000398030a4403481d845a403680100b00840d030004011000d024140040d10400c592840c2405441c62054002c2001240d203008c0451454615409405204034000041c8409449450054480d86200c5da03018028030b0b441b026095224003400c1341200ca901032000007811500ca0407070314198014460240554010040c0d12600900f403c568848035854200142ca402c6900b030600880792091102480186454a03241c010001180c000b80700c1c8000380000807240040520a00c2100c0c001d01ca02c1038116100c1d6101c0c3c040c41c0001c0c00302d140d00142c40b041039501c0e03100030110382120709050740024250130b0aa8030b0041904081c080420402506402c0003031085c1020115109130154600083c900040d4540560f0389145e500150750400c2c0f01460010114003120b80e1810307103000039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 833706843 1250 833705593 833705623
    0x901050709030224070b07020a051c1704020409050a06051503070f06180e0735071809050a020403020f01050f090f0406030812071b021509010918020408010c030e 71
    0x81d6280c1655092450017800d4004004c00008003d1111103640050868101350060055a40d6180e06003880c50046a114809602080074007454001b0514290301d0a07521500150000c101d1000540c0c0740d40c10203881550840300d023503465086c000303000500401d415a228041e40140b600341e00341b20456035413a1207032160f0030403c604510424030820310854020000e041c40684080c46040c41d5102801184a11750800c6000402d00c20f042444400681c00382c20101030902521081e0300e44941c00c03900d03200101d8a40e646e038692600001030124041c49418801d54603440011307219401c5104214a42052110850401000703010744044814440202c4158810071100c40c88810f44ca000854090442c60b0700283c04020003003142d194510406803018071894140c0d8949000b01c20305580b1440000d00b00c0c0000c0d400404036403245c01400e0951000348004034050420120099507150044c20340d400041100c07030742c0c07a004602089041400d0190034852140c0b800d062100e0001c44028940c4c0310348400020324 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 833708093 1250 833706843 833706889
    0x70f090c021024090603032c0f03010e0f03040518091002031506211b0403030309050f031902150601120203060d020916020606120a080a02010213090509010507090302 73
    0x40b44035025109804400910b00ca0390380407684d140100001041d0798442680401e090384407400c5540c660710a09800c4078040d105000860310300505104002c0e107011016a050741da1141d014403161002c11107044c0c6815410015607480d4208000e20101242d48000410340720661414003125200c040b8480619104070040140c40f544d601e0102d0b1407240e01c170580302d40c10120008011480080d86061001110321094108500b52200791680043c1700c1a101d0780d01420324140018400203120b504241001070140003101c00130515040340f241941d1018100c0e103040760740219100201c2d501840004221405902c0900e00d920f0010001307024844a44201d07000950f000000407060768440d40c01e42d903507030740203040340005141c405c944400b103101c43d00140000d48180000102c0d0740ca481041c000c086141a0098048801e1302d0b0391f441c5490700072201c580c0c01c0d550244000300c200d000c00840d04000340125580820f442c14262886821244042c01030020402041001e00140c0c46002480024490f0165582 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 833709343 1250 833708093 833708111
    0x302031e071e0b1804230106030c0504050312190810060c0312060303030b120f122a0a120203070203070e07090e01030807030807050741070f090c0210 66
    0x41c4070111141c01200590f040400e804041d14440184900300420550302003202e010042039610003440d0704480200458481c100601c28540700f134200588000c00d0382003003401d10f0b4481c1d0000342461050781a9400d03a81d00858505071001203012048035201650a11804a080141c502c0740000001e000d4507043c00805004031040600c10030190840d02c00c0d00204002694403803800501a081c0761001a20420641c411200030800101b141d4003001c0d941c20040600c034240005088030f42e00107800c0589015070500c0c0030040d50b5556140e0700424080c000203000700860603c0e011a141d045050707400c045600500120005032800100c1c481503918904c44412580c0e21003108075410070140c0c00280301d50560a0000003005007240250901e1740c426242d804081c6e403284800ca68a004040016008610305245010001c3c103d20881720480040200c004e40b06041c10160520000c14102100c065400184100003006100d41c400c0080d021090301842a00140da000a650361004001100d0680d41c40e6101d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 833710593 1250 833709343 833709389
    0x216030816090b1b1e0f030429091503310605220503071a040b010e04030903120e0103050c04060207090e070915360509010e01020d060302031e07 64
    0x103c003c44028800b1a14170784c1c1c010340c150f60b074072100140c1d03000280301c0c00d0a800310314500841034505a41580000e14038014028411100272102c81348a000c64050400204625854141c3d03c01142d12901907803560340d003018880a80d40018490fa0040205240d0a054000c500e003010322105440d003210010071a40c94000603160401024441c902c000d000e000000001c00c200031015105041c0901c0307281c2c0c1420f00c280703606104c606040f00d000341403400754001804260441d4400c10b0f00580070740780c290cc0f1503483ea40d0769224020b42c0c00081e004518052901051503902d40106603100d40a82d50b4681030910b403107006944c0b0401806921285500c903014040c0c182c4040003980008d14032114144003d0300209501e01c143c404500881c0700300d195030440008103801801c00342d104000c0c40036610255548403d80c2000521014240001a540303510401c52519401d00181088405210001542c54607510426180c071050549106218044041c031007503500c40400c0c02d404480684242e000740301459882 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 833711843 1250 833710593 833710627
    0x10504210e1e010809070b16060209180412020f031801020c100c05100509030f0c0c090103140f060c04060e1503090c0a05010201090507031b090216030816090b 70
    0x225030b4009201c1000410008001000e804081d002a01c484405844a504498a4031031901410001e0903041090b40c0c90100e5401c00011114004e000c014208003c20000880c044102e00040b070103490640140428040c09003172041c1c0c07020003400201514032165004039100d0040c0e00d4880c801da00c030ba80c0c3e0700c80c09034024840c40403461802005068031407101c0e81c0117005017610003001d480038441c070010240011128401c440c0190500c40c000d5040000c02035440c83e0329889201000050f0003102102901621811035150203503100f0400c00300e02c0042e5403046d61802122300a0255642d01020511034200d0141d0201c03004d8541c0d916110301076081d01800715039980e04542c6000414400041042021007003c00c1e414204a41111054a02590303140120300742e4110600181c110740100108200040341c103184481c00e01814291145410b9682246a08a801c805180b407040c02642c007000c1e080651148240e9401080c7c1c249205440700209401000143c03540140c4200100029480c4148141554 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 833713093 1250 833711843 833711867
    0x406020a020f121f15080105070906110a06020a050f0a170c2802011812031127010e0307030f060c0c0b0a0507140301060e010f0306060225090c17060301050421 70
    0x1040d43c5d90f96032545c5003402071074102ca00707000040c215040803501c00e204a001c03020300c800c840c00400203001d481c1c445900035880440201d0602004128203006c51201c01c1c003500079001103845a11814030403900d02d4110142c01000100003040c208081d88000311051030010305ca10842520502c1013500c00020390060082c104001c9502da8040307420713402c00540740086508265907980901c546001085180a540206180360445054000c60301c14400000c000000c0758640514003c90b00042544c00b20f41080002c0d002a12100b0300303500c002d814007a1500403121500400c0c900401c021002d5118280204d00c0500b0546a01d0b403104042034480703110b000c608001c0010540c0d059943d5a40b400054060030b400341c58540401c50500e034212046000c2e12952080380d031360390094051540110f840275102060f15012000c5110640e9010900150324455010300032400c2e121034100c102c218244100b040c400405c0c1c94441c3e814642004005000340b020400c00c02c0103100398001c2d00500d45c40035030f030f2140c1c000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 833714343 1250 833713093 833713121
    0x3030615070609170d0b100509060a0201110d0e1506010c080717031014040504030e0f01110706050301061206081002090607020301050a021909030b070e0310020406020a020f121f 78
    0x1a040361801c81384000c2811808617a81040210707039500c240082012606084d1021800a00c101241e40c20004000d1624100d5031000140f4802e072828888103e81103900361031121a5584010401c0040401081200b14500031580f445803800400082c2401030500c0000c001081c089801c40400c5407015000b1000401c0c4241c10b512890049900f4030300580f584941c80180a010b2000505400c041c803d040c003c40d00750b03481c007901a201c403041c0040e100080d414070341001405204d05145403000c1c072401d0013506181c2d035a03607a607524007600284029003902041203814a4410300700045a00081e0900803480c2c01e140168072403200800040c0a0b001e50368001c0e4040d428102085103540c03081e40102003c0d524008941c11915222508445012050100502d011041408605244d000d0710b589104207400070210307142c005100c401c02081c0d81090384a0303405680400501c4007103141070400d20801c0001520990411540e03000460764504000f100346d00882c03070f86400c1d9003804849800442140300b1700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 833715593 1250 833714343 833714363
    0x30504080604030e04050717150f06030c0403020405090f031c1e05090106170606130912021606032f0c01021818010602030307050a05121e010803030615070609 70
    0x781c20007801951003404c50314405e515110001e900180078800c1170720305419461003203401d0f588560901000c02c480000055008205c06880300c1c99594007401503204004a080301500c40f469031041c04241c602c040d11121030354221122450303109000009a64040b1401e240d52803226070480c074848006d00300c0301144060350000203002035000c1c80b2504814040c00140c0000c220207503441d0f010000170000b1041003882a0085804502e00d45401340c2031101c0d030381130b8100004c0c1e200c07801d5848140041c902110381025812020062a1402c4d020111704c00410032030070188442424084204440e80602028150005105089200403d8000b0981f0151011740008644e14100480c130b801007201d810300d180388035550454040d000794214800f040d04071811038004500b036272039150091795550003982c011000c00c001444044544800b20010318041d0704045c04645403401a5071403c024800140c110412071f90003003080c4100c503254903038203001c00c96980c0c9109449000d103182200240130030090140c06101d203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 833716843 1250 833715593 833715601
    0xa0c02041e1e020a0e301f0b0108180f1e0606040603020d2d060c080f100b09030109060203070f020712020a030b250206060f0901031502070305040806 66
    0x650741c482120400d884031052001e0040801d01c0c003d0784a1411200000b605000c014071081c24920100c4103070055a0503890460701401d191809480d005802d00e11103a07000d107403074880b019041d401401e15803d40c0081400501440c0300042c10150000c1c1000300f140805089650302e091342400140d141030310000c1030702c2c408007140c141350013484552683d05009009003004540d4518041c0710b50b00440c0d41c06884a041d2018a450300d2506200c00c0a50000c10094056036414020f01c0300318115840e0710401e40000c20240070300c002002001c4c010310034074400c0031034400c0c0188144001404022648117400c0303103076202c8280c00441e001d004c0140000388258004030520080e10740120700482c44007250f030700300c40495503540203400207460f0641010f90800720f0010107001041c540010140d0160380001d9600003421100c01072103004e45d00001c03070001078004505100c0710b45005e00b000c1001c01d0003210420180c1d41076441d184507003500c00015110840c2c0c0011841c007050300402c2038074024002700702a0380031860 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 833718093 1250 833716843 833716901
    0x270604120201020f1b1e150a11070f0303080711120f0d0603230721081c061a0a080a05101508010305070b030705093304030213020f0a0c0204 62
    0x440100b4081c812840c0600000340c0b06c0134140524030785480203002011020080344503403110351080204a041224040e0f40c5500280100315160081c0380100040c0c50320762070360900401580c4040d01480400100300c104490340d00002130f00b0704025500f0744820342d865180d0390301d4509511940103403460f80c03410b02c9000414032a4022881e00f80142d1981e003100303e01c00c0210b8864a030712060080c081c044511381010350304c6441203440c0c4005a8850f41c58646010801505c0e18200d240f00301050600b0754444409000090741034134048034181e0f03076100090801e0150b03038010301180002401651825514000140c040c1c00304000d0500070b00b04000a901c2c01200d07101c009101600c2400b041e0b0f524802e4100c0010090b04180840384606166914075040480c0c1404015440c00300b062145403140e200080040b007c011403ca855144420031f40b1240d0b260301d54814018843d039040940d146c0c05105005010301d003400301c0d00b205c41c01655850b1070480007200b0b10008009200a160000c001d0480d650f0241c0041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 833719343 1250 833718093 833718133
    0x601031e090507060e100309052a01030b0307060c0b0402060d02070803150a03030c021c0b07022d0607122c0f06151509031002270604120201020f 64
    0x50003001621a031603192541540e00b0008420712070b03004107422510003041b80c440c3d0b1000c0320039441030040e03407a5954081d21000d1003d4001d400607503135527106a1700034141d41e0980b00d462004081680501043e51404001401c85c0301884000341898000c200001c08560f244012204506c1c080360045483d00c1040c00d002c0b1803604100c0315800031000e03900e50f000d603501d08400410101c9901d0358401242d04041d40c00c0c461211a80c1e01c406042e842100c2002000a1244441c50b00c00c1203590300400f401c2029014012505100312402201010f1400e0302540c3d840300491915409003c0c0d0070401d0051840c0c403540b100800030b202107440c0c009a0b9140c86540c030300b841c1155030b03440b40000044660300b40710403035816204d00c2d0a690404000036a4030b80c02c0c0300e038144441c80d07034a10160240e04178100462800440d040c0307000c109003080c0055000a8400c0d81032504024092800321004000d0034400696010407074038071036406070359105810040344200310380c820006600c2d40b0031a00245c602170344d10007032950b00d94 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 833720593 1250 833719343 833719361
    0x70b0c030d0f1e020705060a02160b010305061506040b0306100c05060a0209090f1006031e0603050c0a15020d121112060901060309080f030411060301081011071104050601031e 77
    0x101c0c02c1101e20700b03c4a05000f501d20309601315018100340d440791240903000754010000751020389c6800450f60089000c24219900075805140036004a1401c5184203491880d1910f001e48030340e42c184400e0042c104140d081c0d03a4404026540c001c644055840260780b071607081d1000802034890b40c400c000320012550064900c401080d40e50800c5031b280c407044070a8040045414020440c0c2c00002000424071a0300b00e2992060018803d610b020100354910064500075001902c0d9030344842840207403414218582d2008003490792a12440721881c500c000e49540c5c40c12084001c210101d4a404150792055200d08808036580d01c10030b80c1e408464111540c180d404a0b8094400c8941c2c000000701c00303001e40100d46860b5484042d1b140b610610454040345900040c20654403030110402c4819962600e8000b580a440185c00a105160303082c01a00180c501301c00c011002400b062017000001540e140c4500e166140c11038000c00c071740c0d48100040300101704070845070541788541030034200c984c0015803040b540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 833721843 1250 833720593 833720621
    0xa0507020f161806081b01140711030609060622150e270703060203090c0604060215060a0303200c091602010515090610090504091401051008070b0c030d0f 68
    0x2c45503e4040e82c1140d081c4d00c60300000360006100c00240c400d6200a504402405050540c1c03003401d030030349617200c50300000e41c11070310100c000100c0c03921458104002030f8000950402064a4988031010620340b00fa0420454070004111007038001d1003002c5d8026204005182061610342569041c420f405083c00741c0d40c83c040b00c0c00152440200030a0800300c0e80340811604010001c0d107140d43c1c1e4060007940010007102860085501c400155031b5200001e20080016034003c00c2c4c841c0010110115840014002520882003480c08000203500300c08400341200341d0036003460b040d5103603061141c00e0215081c4003e900420943c200001c4c40002c0e04c40446c40d1120340c0c000c100580d2000c01c166810302d1041e51807540000c4a1001071030781c2c500079104940100345464484c2845598070085019207a950702c044039101203010b03016807044030921803642e008480702c289056580c0347c42c003a65120000d41c000c0a080c0000051544406174040045414201c0c0c0981d00304450042110b43c1d03001419401707003841c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 833723093 1250 833721843 833721869
    0x150a0b0f040c0905060d060503030409060f0e01060f11031605100c030515150408060406050a0b0102030a0c261201090e0706021c031418060606120a0507020f16 70
    0x3800703060500c901d564203a09510740106513030400341040400c0d0041b95010748015121100810b06460500c003400c000d0040050100b45c40d0305000920080942ca50065030400b0b00600041007155801032101c1492840f5080c044213020f0118026420b40c0b15185244070100e16020106c810000c0003c3c02850428004000700000c14001070120b0a48905039001103000c0191018000719181424140841e1040b405646207040d0f031f602092801c281c030460f02690760540c3c84e000c005074000d0070f01803c0c06160091019502d4102d0b0360380c0280c05501c010368041c082e1103484011601c80701c2490906d052005600c0c0c0d915854011545503614076031802d010f800c0f101418001048003e281c0003c004041d0361480d0007600c004250607a85030fa403049000744200130582c0700d256610410080c61006400384030b1900742540204a1800d0103481d20b08040d0080b030160000b000000030620f00c050f03410b5040804150007081c1500c440c0000c078901415044404c041d0f01640c003000d2a485024000c4000312071081003031038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 833724343 1250 833723093 833723119
    0x302030a03083312030403050d050301030213050403050307110106050604090b1c0209280608031801021b040e010b100c05060c030f07032d0605090f01120b09150a0b 72
    0x449004035440c1034403e01503018002c8082d0328110003444c45595100044a00b000d40d81e468041c0781c420320305158000710300008018815824070780100110000ca007442400b036406d02d590020214030000301050100004010490003124080d0405001071100400217503c1e5603d50210400030812010f01c0c41c85042d81c0030400a9a03080e6496030245950002c10842c0d10341d55a5040403002c6d401d200307035a04412114440c42e418265188200400340c1600d40055403100d440004401003481250310503419981b01c1c100c030801c4078101c10300306c1501c4502544d0100e28100204036807409403102d00d4034903500000c54210303e045a54400403402119002d00301b01e07107242e05c2d8500c0800303507440255640205c1801480025641d117019410001c2014001040c3c19480c10150002c40c1100c400308022000300c0c1d4a0701d0040020703140841c1d4075a00007c0700c0103509001d500d4400c181e4840507503014002c103150900000500e4041090124200a188000110000d840d2103040384004044400455111b0302d0303020890 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 833725593 1250 833724343 833724391
    0x9011e061d01030c05120f1c020607021609090203030c0601090905070b031303030b1206011e140607060b1c1a01061b0303110702030a0602180d03050d090303060302030a0308 76
    0x154100c94001086a00681c10035090103908020251b407170b4824400c000c841c5c2c2a82900304020b01d04075580344141c88040c24081c00003410040b02410b120119030003031607048414600003418504403098911700040111003840424294007650800400600500000003080c0a00b034228941140c454000e841c0c501d501c8410b003c0c4140030540380c8110f0f0944540000300041d020381d001400002c0010501c0300f1f141480c420492421800741c0082114050082c2c103440c1c3c4d241504401d802600e46d044140100f203060704003240c901c0c000d04002030445615110b2501454481c0010601031079110112682c04ca21076042c1404042e07500c007c4464400d4101c0000145944140364201d401107c80680750b0610407151001c034050403581600c2c400e5070200300505001664100003042c100f520a190250315040b81c4451074140d00100382c401801403200d0242500000c0d0f100007260792112069000269144803030a04500401c5a42c100a405104413480c0006041d04200d000f8400c0355007602d403c900700310328002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 833726843 1250 833725593 833725649
    0x61206010b040b16050a121b150c09260d05040506031807080a030225050612190e031201060908191b0f0f050108010e0f09011e06 57
    0x1d0025481401e2100303106140b412002040010b25000850099060300e071951418210550801c403130081d120102e00344c0554000b4160710044400951070078644025444200012011032000ba4115540360b0850710380a00981d50000a000000e90000c000418401c10902065443e400071000748141c1e00481c141c90302c40c008407003e46201805040c15070315600c0a51751100f281c0d14101715a80a18140480d40e03650810150182c94040c1d80209046203030300d62104502071a4200d1451540d00300e5100340030513294813044652403031001d426600300341d50341720182d24907501e49540d01d840d40381400c000a081d40c0000000e059103c15142e82c564090740c0c1c070101500c0700310051089103265000024440c018030030b10040258094001e8010300941e4003804034a07810b10800d60080c0c80c45c0845c001082c01b0b41c0003002d820002500080c00c0000f815410801c80c0c10104130014815001c0e0720444c400240c00d000f00303402c5100c900440d0010070070f00d40400320b02031b805030100c0d00540c180c105c024145411440700846c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 833728093 1250 833726843 833726849
    0x115030804062a110406030519060f14041e050a03210c0e06180a09050103050709020c0606280e16020a0b130f0c060201020904050604230901060810020306120601 71
    0x9144803050f0741d40d03554801c3e01c059040a40d548540d50750000008290140300d42000c480c043c81002190382c03007a01e89002200d1000541c10b015510b020980106c03080200300541e08070b5006070b00704000c1d1040b80c00c030405021304580010014001c0da0000790425400640302d07034070130076540c01000e0088045413520040715022080c0c000040d4604406402c1420110018140c10601d00b103c440303c1c0c0c04203800300d01c119095038458500749a0740c00041050001c1442600041c1c403045005501d400d600220a035a00c0c40c01800d0700e07201c0c1565004a400000c410320240c0030b180322040a81010554501c0700706403504040b1000c0d06a9a46144014051072001c90488090f591003419032039a0380344ca0326105090f0300414007c80700b07411001400004620300740c4880307000384000c1c0d00169440003601e05000903500007506450240341000d002d94400d02120304124803002c0c82152680302c90b510442c01d907016000b07503448441e8600810392001c180d014960006c5115050540c1c003042c51250319001c156860000348 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 833729343 1250 833728093 833728157
    0x110a091e051302030726010e0a02030c191a040915050307141f0507050f0708010f110a03050601050d061205071502030a120605130203041a130b0603011503080406 71
    0x280b045c046d10341844014000d444521181900342d22601d090607003141c603001d0f41c25200d41d000c08980780c11481c040140c04045030b07054a00501060380c540e45d13100303181070700d000b032517558000c0d002e885559901c0403044e500100798070350042c005007801c54881001c4500c180130342e0b8001d0040d040080781d510f20340c5103c108036010161580b0b0200c101c030010072100e1803000b182da00130420100541400308104001c1002c030245490050160a1b1400710600d08680d485446400072604100d400c4081c40c0c3c2d402c0682c1e00d8016241004200303980c1c0c0c41c0048450f48910076001c2552464500c000ca802d04649014070006481141168005512040c007048020602511701c1c006a2007005540f56652003880380c240442603180c00854040c0c4c90704002808078055820889004d80c0c00320801c018801209100b51403d03902842584403820f00c1d031050040000c02000103040f4030407a801003502d03501d0960026070404500c1603107461007502c80c075020050394130074821980014104608481070071100310240180400d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 833730593 1250 833729343 833729353
    0x50118020c12030403050c06070219110103060e16020f01020f0304120c02060d0506010210090c092a050a080a020315281509060504080703110a091e05130203 69
    0x28080201940c0310120203602405030000034010308071642c02450046100c1d89a00741c444850500803444c025006190f401150322090000d443e1507408103680c08007a070010446204c0855100050740508070560000700c440440e241000001c1404000c2100c905440703a00740d03614443d0058040c1c2c00e0340541095049009420004500000c603840c071480c03003181c0c0604080300c004051b40c00040d00c4e9003140b444900102c3d187e4040000d603690520100c9203014441c102044880680e803034131600c41d5210b0245080e01b5941e14610401e0000d014010380e50341b01c05026840f4107048414004200e0303000885060089011b0b6004241c00641500980340b00d0f16005101c110074a6032a4100a140b200300d0003115081c00c6e480340214020801038981402a0001c0d1000e4807012202d41d100070881001e0750f100e0300c2080000d110900208102050713000807280c00c104d100590500000c00601410034a50007101400d20303040a44d200c0d41c1e6041c1500000403680b2104105580e40d801281e0400e001306040254185c200c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 833731843 1250 833730593 833730629
    0x10f11040509060f210102070c0518010b03070207051903050c1f0309020d060f0c0f1d0d17070507090612030807081015171b07151103040b0402040f0501 67
    0x11500d81c600070454000c1540c0306030403c81e001c0b82480c06085c21448040e9400041140610601c810f5020051806803031403c214135000a05640a107418013414008610010110781c03130714400c20400025000042181030803440c1340c89d040c840b1100b0352004860324041c40b074080da501d00d0a018a600c080310440020708005803002d500301c00401214000b2039200f441002c502c1d020940500c681844812100400205000340b90b60280502c0390104c24541005801c0003d401840381089a215125078243c070600c681000354070700141c20151030f200024005001180b507200388400080c1030300172590b0036441000310a4841c207003120703912004540500440cdc501804950350f0b5210300300f195841020502c403e49140c0e2910841c004440d0702511090000b00c5815241880b01125101d4035041052a03000795010140251526850b01514002410180c0002d403a00301800e500c0d08503401c0600480a850b0340c078503262601207440d1106840990140d0710300711411306141c8103841082d059400429421015400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 833733093 1250 833731843 833731849
    0x207030903110105120901022a0a0f020f030a08041505070c0b09220e0c04061a0c011b11010c0806060f0c010207020a060521010614030a0e0f010f1104050906 69
    0x104402d0b049040220400c603000510682c007003c90301030714803e8005640d0750b0000c00406090740800a02c5200000092280c6000304000280941c131190300a84d5484000100d000041c9035504400d0b01725054010746102d8410451060001c1040d41d14103c1e0f02c0d012090a000121903a020381c0200a10400111609203c0499840c02506002e6801000c0d45000d00d210b142e11280c42d003003e034110038625102e090351041e14030203100410251030b00360b50800210b4a410002403000000a508407011200003d50510300c0e1802e40044611801045281c5610011008000c10314030701301c1f0300510f60b540b03002560740040d480381840c1b0f400303180002c00d641d003014480c0e0201504c6500109104220350740c00c100c1c0400584480c5030020082c00c03d51034464540c14200b141528101c0c403440c4100b80f07212500014440c207030b0011071600c0c4096203d290f1549a50328212000000e040840043e0a00e100b80e1b90003030618401508040c40403042000d0038000021140e43c0041c207802140116644064241c0001d00241 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 833734343 1250 833733093 833733113
    0x515090609060114032a0f12030d0209031009030806011b03170601200a02011e02030414010e0d0b09070609080601150c0b10030b0105060306131508070b03040c08010207030903 77
    0x420010161040b00030800e03942c007503080d40ca2581c000030b213490b01c0d90541c03a441e24050042400c5000d45d820380c964160500523540301d00ca106d038060b0b007071580480c550780306840070060132600070842c500130070100d5850f0030064805403040703039000d0000307a08144140c443e9117461481c031a1281c0c55240c9800841072201d51a00544000700740703604000072071074601e00116401641c026454041c40140001c086103000050020f030007404107400511b00d1400010b400c6034000115400c803041e4224558006005000407525010603840180c1c1c4051205800400e0240b811001400707200800219010255907150aa40d4280b041c42242e6281c0c0103540108446807031b10070010310102c02ea25124240100554541c4000701098411404a002c2036809000304584e50168902401c0c2c00c4444508519021002443c0811000303504681c094441c8801c00030003450080c01800740019906a0b0703070480d1210820056a08212416911941848000100280c061013103843c0503402d40c0e06c110300a402e540302c82c1841 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 833735593 1250 833734343 833734379
    0x2070c090c021507020f0a2003070f0308090117010b370c15020c03030106030b03070b03042301110702041407090302091e1e1605190306080a05150906090601 69
    0x150190503480440f0340011f012203a04184103290034000f25004051141044d00301240107400399119003420300400d8400401a001c4079480000c050381e9095000040381c0c42d02ca00c95410081281046c00402c404034000003516040b0b01508080d1020700840030007201c0c051009170700814030806402c40e00b00b4180301e0740c202c00c415800f808100c202c801510304500c0c126842410301207032641010006114141c0d1500501040c0d103000c40080c400d071410300f50515014030014200902604c3c648020813240124400c000072500344c4403008014910f411440030b0b16a50280304100d04c26440d108680c036009400003031082c003c800a5840081c03d6045509214110a000c6c4c150011b05100218035049030710f02e8440c2c184070b840758610b20078007100c100c030200300c4540000c0c28103000c0e90400d43c85500c01c241c3c40b800303680d20741c00100360346441101c40c840c0641c028186500709808601a15504105204001510303002c054400c413254081541c1e0110280c0d200c02043e0388410841d00301100400054200346c02d00840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 833736843 1250 833735593 833735597
    0x120515060d0915060302010809010e0c060c0109051507030608071401030b0303040e0702160e1302041805060a02071a1303120b09070f020c0114040509070203160602070c090c021507 79
    0x40e4141d02d9018200f4504003103032540036120340c814411560701c080765a402481d001c0007400801040000780761a2072112015078003a8401041100900d0b00035048203204a40242c00c1c2c03082c4182c0424040c03c0b04004841c008086811b11100003040e1000048000403901d5010315401c4864840e0011400780603507804442d4144030901000c51403c041c480400d000c0d0025800620302c81500e42c1007185040e00503070220101101030070400a0365500d54a641283c40e41c101c3e00054007c906409400b40401c041d840500548a1a030030025440d1141e8010243c05024658000c0368481c040070b01c4510303040032520004003511a00154002a009100000348841d000101007100e40d00480450b59003141211400b0000d40c0d14814028030136014444025017140c286843c035920004141c10007028455841154003130720178200001c4800d4400e0040e240100d00f070b030500304e941d2501c501700030010750030880040c1c46414901e0b600090388035051042003255416a0054010700ca85940b820a600a0003448070003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 833738093 1250 833736843 833736851
    0x21207110a0b0f0301030b070903020117040c0801020f030a0b0907120902150a02030a090608090a0813260601090203010e0c03060d0b1003031e08011a04091407120515060d 75
    0x2074407034500702c05407401d00e5000800e0394981d0300d90b0030201d90016001d4240c44c1400340310101400540d070311040104201c07400d2071100070180c56030315203a8081c00842d40304400b40c0d4804a00345a468403044015170155005103800c2c810a04c040e4104248070a082c3d13034100103e1440020300d640c1003c80c0d0070105000740011720094070700311458845010303503112511600c0142c00000e0701888540c0c01880030009420b032494450340302d15045000d540e81d2600640054542c20f00880da4034029103503e85248051301100c21074170840d0b032640284c00c64540401900340c005000c0c50002003640d244520a4034101d400d00c1d1016803c4d40c0303030640307045150b51021b4405034000c2401311264003ca240b400f501da015808410100400c5481c40c103005022404c03001c103074800218018400540d141c3d0094255054401c4011083c0384681134104269092107a64000c26409045c080c00d19009901010842d01c070b1070304c83e2134850b40d090003000402c0c101c46045840c40c1c1d0b10311201d900700c840c0c0d04000000c1c04600d100c40100107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 833739343 1250 833738093 833738099
    0x170c0904080708030f04030815010f0302070c1d180303270a0c0609080c061809090f0a1a060306070c0b09030417012304030e2403070306090c021207110a 67
    0xf83c80c0d00c200c42c1c8055140c1100c081c801019880030183e0342c03100460304421036070304412000038015212200c1d01000c140e0086065030902841a454200812404152019000b130b9008024200704086030551840c0084031040c54a0301d0700402100d12640c10311000e09500c00d002c21749400c0380803214400e2032043c800c41d000032001484104003030014100c50749680591614022010740b500036402c0400340160800c0c086100b401000e04101c0d00c004108842c0d440711580c950780e540b80380c80e101000007a01403296000017003c1c00200c03031040b150009880c00d03d01407130b5146424580d07140390aa4450740020220405800881c200d508000e4008190f101541d1502d03a4400728000075041d0340c40c000070f00b65500c1c040c0003c001501c48856401c0c1062039010700d014501910041e04040311014418021414104404c114403403aaa06055601e82018000e40301e00341b1944c000c0051006000381c2510034500001e0007030036800050720902c1e507941142c08900e414103070350360000440340f08940507030842c80c00d003404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 833740593 1250 833739343 833739353
    0x2104050d17010f051c2406081203271f0f09020906040c02010f0c050417010b06040909060906020714010b0312041406091c120e090408070f050d02070f170c09040807 72
    0x410551000186c6407410340e10300300c011001c9407000e5001c0c2c2060342c0a210000d503600d000505403580052440c20b00d0300c02403000d45c0900e540500040803a00a4001c038190b800e40100c1c050454080307032140c05020071500d04041c100c1004c80c0c000001c0a548111070400103200d43c07074507400c0000c950b191880045182814900440140d4050400d684045803000c14203000c00688444050240c401250007800b1130081131020034100d1250340100e030f684c03503214040282400140d801c06000d050748010219900c3d41142400c9402c4c00c82d601c0595030303d500300f00240b003880c0340008000904603580d44d2001c1c681481d0000881c007416001c03030300a400c10003d01429829030342d002c2080c000700000e80d40283c50b062580c0792242010741c3c01c3c0801014072000350341d404101d403a000d9803154850b0340480d5144d550310b0281026904115407020080c854407071580f5102c0e0071030380456600c048996800440300c10359210640041010140710920019030321507400348109240601049070064014003000b40780200503264 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 833741843 1250 833740593 833740613
    0x3060614040e030414280b12160206130201030e0a030504031e0503040e071710050a090921170405010c08070e010c02062104050d17010f051c 62
    0x44503850321440028022035042901490003011400700180d0302c2c0504080101d02c0380140440014021070b112060003902c44010380f07400322011035510b041030056030740303020a0156501079100f50408405e40c0f404907691070140c2ea00c2896000a0f5009002c042c1c1c0e0b685c4900b86149500b4400768101503d0700c0e40310010020034800030100c140261386141d9103d055027481c0701e026540b58111810103c00010740d00100350048240d900b0f40c1c007165031105450303c800f10100c4072a108248880282e2614505115070034140014850032a00141c40c1058440d40c0c92640c94125840c40300094004001440c00c040e0354075090310108040041400c0c60b191a60b400340300410110801c0354216081d80d95100d507100490b40023100540d1000380e40c036000d0340810030440020458014100000d004400109055400e241650340c3d00c401c115601c0710b042c0790f030300d854188944e40311010364054000c1130602918040e10075400c160281070f102011030221240d8903141c24010748400701e4098000c4100d460030400005a0280c43c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 833743093 1250 833741843 833741849
    0x60524180603130c1203020309010503150603070c11040c0e09060301020c030d0b01021507021b010e06070807110607080315010e060d0c0207090c020705210f071e0e0c13030606 77
    0x1001d54016006403400340d0342142c5940209070820310441480380081c0c7e0000464040c1d1600307281568580c0c40d140c0306002146c02180c00c984e40610702204110615038018100030600e40903481c80070314014210b05000c202c1707000c07140d00d600203001e24642040c20b00703140560507041900a0001480c03c51440d8806086400851818103001c2c0c0b0349000410030b40e070400c10703940600d0048035000d89908203440081e60343c17106580c11b55070300344c4900c8616100f603008002c2d105402c03501130708180d91505213140c10300c40f90780b110104861440e484034242215050203800e449109501c800c580740346840c0c011010140c601d17080f40840c10011550a030203401d0312258050014101e0350300011456a81d03000c0064105602e41e00036240b5645004043d0005d50390014595003229000e81c0c4030302c081d62002202c0c1c040c581d5809802c014a01c0780b18003004c0030802c000b1b1101c0407241c4c1c0d01e0b060a900c83c030300e10826403012020312811000f074070b41ca4003154141c080b5100400101900ca103034080b0752a5665510020380315554 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 833744343 1250 833743093 833743111
    0x70b010e04150b180703090203071215060303020a0201051804022b0b01050a030c020c0603101802120604180b0403110f0303100303080402032e060524180603 69
    0x2081c0000c0041c0c0400440c44041018000e200c0446401c02040c01c2280f89101d16103600c6030783e40801c0c80c0d6130199001983c02078000e030a849599450b04012080c1d55607640d421039110b05100e900d060fa03100745200e29010b17241e069010301030300411071b0011229a0001c024840710100d00003160a09652903200825441442040d400c45481011101c1103850052001e01000181440c4100c1d0860b03902c107048403088103550400049500e9061003c80c0b80900140e21320ba0482c0000040c0a02000811098000c4440d00102941c0360340d03665400d88264000e1082d20801c00f4150401b0695030f2825401c00c41c03400d00452400f1110ba225903c50142c1c103401680c00f40c010a401c242d600440301d000303004540002c95090011842c500700f0001201310100b09100182c10840c600340403c00b1541c0610054107040380e0012045400c04c44101c1000c8000c201d4005407282501e494400140f60508441804091148008101c0b02d5a103920303038050150b0003001e01413114540808e4141e002d0382c0f040080c6000300006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 833745593 1250 833744343 833744369
    0x1106060d030915090e070e090f091009060f18030f03020906071208010e010909020a030611090a03060e06060409031b081b010f050114090408090117010803090312041a070206070b01 79
    0x442e1003030550011b04000d04201c42ca0302d458440d03407122414140c1220b900701e0300309081d0f40c07400301c0c407170078150030561940015083c00f41882c1800350a41100c100080d61080401c240e01d0040c00701b08940d40107501c01030205002d610381190b020300940c00350040d000e01420340d030b251078287d41d902c0582122404990f004034901a0051100310900325903e4003405c2101c40070010079066400180014001e440014041c50311412901c20030b0844001b92043d481c00070b41015000fa4607854000003515140f290300038a03125110000d030a5240078001c880420341c140e2200c2c0f2a04490308078602d2003890090703040d1a0050208490b0751803120301507100f080d81d2004400000c0942020b1403034810381c1c0041e40100c104100c0b000b28404140c3e04c0c41c260640195001c0116640d80880300016140f0401406d8106036100d0503000010b00440088001d01120310210140c81842402c40000c0500d0300550003030504014595070791011a280c3c0c48014585140010b203038604120072556810300281c400d030051a060011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 833746843 1250 833745593 833745599
    0x51318090b0a051e0c1b070815060d0605100b03010b0a03050105060c12180d060606030e0d0912032c0a12080901051c0905030306030d1106060d03091509 67
    0x803400340754000540355001c1c0010704201501144407030003c4e61464141d85800080303007034400100100e0300c00c0720560080000009503441c0e040c0e06d4901c0d500c541b4409000d100004440300c64500303210740c425100204240e010300500d8403210000c201c014500002c5140000c004138802c030b42407001e1030080c104d884001da50303148035250081c15200103901c0617014541c02c0c040c0c030b0341590740440c0701710800301c40034015034440d10460009444044c10baa496030700024a09030b24018000c058200c802681c19644080c070107400c000400550320030030f81700c0040018080300c41c2800710342d0004403000700c06030280c40c08822242d0301c81080304402d8450a01d00e004419010805105030074198841c1c0028180051501001d500c1a00c5044991065981b814104000054050013151481710704141101030070408120f4950203250a40e90b0358800d5880030300ca4800c440c1540c40c041c1c420a840300a50800300003604e21070701c0340d40520846001c02c60045061000e0b00c1808580103444420084882002d0365640c0d5500e45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 833748093 1250 833746843 833746853
    0x12191d0309010912150b150d0207060b0904020f040c0e0913030e0303070515100e0f10091107140102121603050f06030303190f1e0608190305131809 65
    0x8907030784c4010014070b030300707000351020480c01c5c1010226043e811201188802c04040090064a004069141d5100740480d10141c058010750180c065940704000400c1140440c900f004802c91007101c0095001e0080650f00c6000e0401c0c0d041103141c0100d5003031840d9924000710028a00307520845401d0039100000d2101014151b100b01201489041039003d54541002601c1c0c06840e8511250625004140e00f000b14003a01100203401000b072a03207080074402d43c1090401d1446041c02620900d521a605002c049050b01c3c0c0da2248200429480004500c0d005135680c401000d084045031801c1103560a001112408100314a441cbc855085403800c00c40344c0342200d00c09022920050314085540200f42d00704001ea881c0007084907002030200c03038981c102112941140018205a0b000c042e0100d00748500d8610440300c0003000e0150000e1007000b4010662105001e55564050050000c2c1042e242a240d00109000380000c0007108032824680110340c0e25021315150520041d00e4103041c0c141e42c0c00380f1105201c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 833749343 1250 833748093 833748107
    0x204320f040515100504110c060c040b181f0503070305090a11190f081e0a0302150a060504020708071101090f05040f0213090e1212191d030901 63
    0x1200e10211260a003010b0b00d40a5950420312180865a0606000f0918180b6101e01c01001044000c0c000d010618681494200e140c0144441d00a079109990124900c40d99510907201030f140920b0300141080c00684042e10b1703144031150226000004d6400115070498072004820445900d41c035030750740c3e82c20f00f070344010221030380109100d4198000e036000f8400981d00b5138007021081001c0301c21078411024100810540d12581d8461911911840b8001518101c0420041130740040c550b150400203511006158590304075400040060f0010300344801e802c0900c091650b0460131540300001d0b81515400410100d0f404010103881d65035000c6444001c0002070b4071100c2c0d0704142841c254107003601d07011f005448070340140501845039482d2102c410a00c0c41540c180c07580c0d040b0541d43e000b4159030310107030340c0c004100c0645105142d00401050b60302e0a030200c1d007210840d007040e040c90900c503940c00510341d8003174083c40003214003540c8600700008402d044007030302c0100f1090000555a207505c42000503140e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 833750593 1250 833749343 833749351
    0x2a061623043602072102150405070f050a1d07170f0402040b040b031f0b0915150a0e0f0a081b030118050c060a0e030a031116031509020432 61
    0x140100102c0002a04000c2050101d00004400c1d001040131703403c4c04e0742804100c0005d12190501d0108001c01d0140010709a403c035541044002c0b403013501c03501800868225800303842003440501d8926849490f0b1008120f511000514001e89041680d4402400580d426192885e440c0b06050901c41903150600c02c0b035401c004100c0d4104107c0504001282d115681c840c0008062450801e40d601200c03101d0700068249400100b50f00028070740300010700c0c424601003000c41e0203140d142541050101d400011146a08000c1d220710016001c2d9100b0001c44252b1110090741140c502031001904c598200030003c00603141319070862a11513000181403c5901c54050f59001c440f2000303105000c200041980e0144d0401510b4559a07201d81040580702c7c07000b510001238151141e0403400d005e00d90300c107500720395215090090300c3d940c81c3c041c2d0352803480350228040500203254403104845040f2559102c400c00710710180c8041105201d0054a0440780c60800c514010103500358100b04204640d085042c0d40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 833751843 1250 833750593 833750699
    0x90d0c050102010c09140d1b0303080f060105070b040f08190201020c010c03060b0409110c03030106110609010c0f211104090e0109080306060c032a06162304 69
    0x503051034401b01c0c00600410b1a4918029800d0540c0c0c041441355401c040d5400b82c03105282d900366155a480c0007401640201c420041c0000c5000205010390312810031110420b0f0002c00c0c21359182c4450b2100c000180d80795400b00c0b80180c0421000507000010203007a1000c070300036000161518421240c040c20750b90b54641c0e903000c16191080034003a01e00302d0026102a5000c6603000500340c011034214210500c2200113242845c400070000260640d48406200c2c5003915901c141d8026854203248282a90510b4440c500846e003066829151030b0310071001003240d0004200c1915101d58480b03045801c84201c10201040ca0344006030912140d42e107401442034051148008000300002ca071110700702400003802880c8076074400240320b00c00c0d103000c0007550380481000403680c10984080c0700300e80c00c1907400500c004160040c0f01c00941d00c4c0415581281e40350040340c80c0d0034020f507000e1001c1d00c1080440021003141c94410321012a045403c0304112981810103038103883d405000d0400d10302094050a40340070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 833753093 1250 833751843 833751857
    0x61502101b0309060f0e0604020111030f0906030717011701140f15032109090901020711040b0301093c03090902031b070c300b0903090d0c050102010c 66
    0x9610445002802034a4105142c0012000034074502000501000016500c0389810300100300c000c0c1c080030030054050780c401d0300d401c18141c039508202503c0b806000740750b42d140c5005002c541c41504100b401140c2c4511035290490f07401000803018072a04400307070003400c0d10302c7c620403120320444001d00c0381115110080146461910348080c0e001c503043d100912108503910f0400c00030720300e614100308480205503140540320010008544000a6800804421303220b180840b0100303480c04418030803a103200742c100b481c0c0b803440344882d01844040d0101c84038258156603503071707040d0011401007400055940100b54001e244030852001c0c0c01c0c1808074480b2920504c500d24400a0300103508481c5e11000c80c0c900000242e1a543d58100142c10410180d19058042d00001001010014480c0038030040d90052074841139403032224540c80303524103621154203030355801104607180801c80b5041c40c6503000310f4a00450341f8180310880030582c0000c1244085505031240d00c41880030750780a026a5140e4002894000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 833754343 1250 833753093 833753111
    0xf061707080705270a02130605030105090a0b0f031f1a090a050901110a020a0201030c0807141b150907080d0c0803090c040c050a0e09270f0106150210 66
    0x5071100310301d03c5114400c182103488500301610a20070250107481042d10011a131900f0b0104101960055240d24011454a107012802e5401038059906a50700649440616a94203070b0490060609205503503004c0d0400504072020f542c20042c100c188800c3d008809580c0b50394041150944030041d00745402e66034841d03200344050301d904000d564481c0b595580440d6030748651f404640106202499440c0780080003502000c81a0002146500d080c807e0383d04022031b60540d242118104070075a280320018515000c40103100040501414280748000000d03144e82c4080707134510b8039103c404580b2030401121541000b082c0e003002e1041074000c148600c05822035041323512008260701443c03400207001d8107021020034280d550401c001c0300c0c011005041040994910709010300540c2160181d0000501c22201503819424102030150003507411040400f060010700740380703000442d840b4181000354852200c0d52083c0301002d005120081c0440c1019040c01002d4420080c2811030347c3d12461046400d100707410f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 833755593 1250 833754343 833754359
    0x6090f09050c010507080415050406081b04050f030c0616120309020d02091302120f0d1e21090b0103120507110f18010e16170402040c050d0f061707 65
    0x2e1030030140c00d291881d5116500d24007207243e40280c2e00701c1c1d5100b074000c106030b400d8280c100c801401506d18513121042c550703441680100003440f02440d04800080c05100c100042d090507660140140401000da51221109102003a042c1c1c0002040a00340118500b80800340100c190310341100c40801d00d420300c150905500030840c50b850701c0c4402400b45810b2400152525400810f00390b88950081c411030982c500b0740130f003541d50035402245001e14043c480c1080711446c05042c99084800d1000000c3e4500401520203aa00010440c0111451540d038132680c15416100c0c40303140e800ca44100d00c101071550541c01d11800c01c03c690984141400b90070015000811144049070300c000000322917205d401911032020825000c2401c80500a11140c4400031400028940c0c0e243d00c00c0062204140a064820034102d4900248610148060013500d01080143c10503400506281407075061251411100950841c2101c401310401350785203a41e00420301601300b5000b8805074201019000709041d078101130306 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 833756843 1250 833755593 833755603
    0x504060606052b09050a0302061f0501090314010b130905060703060b030a05061f020105220309031106040b180a171b1302160c0806191a060c0106090f0905 68
    0x48192142d03c03040301d51000f6810b641088400705d40c00025212051400d00c0c010756600410390b0018045c810703448070440604034208021040300d00503516901141c0ca9500e60031440f60080c10700c0b2085548507001c8065644800550791604c5050840000e04040380e803c04a00b000300c080c000a0806052100401001114409580d0856040d480c0020300342c41d14000100280300300f000d05059246040c596180c10781e0103500c40c81c071138a01034030710320402210390482404c800c04c0d101c4018081150f01e041070011070f00b601c080c0750001c1d4010744500d10305a01e07420300c100b2541221014074503a03008803034030312414205038034500018940342901c0000c544d075209a0640350b44076400241803800844954681c0703940c444120030002c0400c0902190359120202c040701301c0c11b40402043d2410114004002400304d070014900707100b1411176115400035a40000e0807800307004a014042010200724001c40c14503680d18004058008004000003451490021000191801d82e201c95100d42d1030b0060050102d400412 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 833758093 1250 833756843 833756887
    0x230106150e030a12110c04090b0f0912161b0305100b060d24060512010608041a1501020706110715231e0328061701050406060605 57
    0x102000d1070400c000200f4540030385500041c0c804480040040c00c4103400030b044105141c0c004003a10008a081d2003400705481098200500c546007600019441c542c0e01075403142c00c068580181c40410200200b00f003603a4011600260240d030b9042e2980c0704102c8203480110440030100407400b001440d58403180d071039141202c420411aa1a03010510312542d4107001c94400d0ba03107900c42003020115a8881c5140300c0c020290661180fa100980490740307030300400548924042c0c0e050702c3c0c6003d80c00d01c8812140110042c200b150302e150160054640c840300e5200f61440b031104815000349058031800020b2804007560b01034800e1100b044442036110348082401e50650380544c0010f41d510803151021149035443c10060b00c00124016004510103a4902c02003c0413100e150010141005c5203004050500c0300362403c0309140300c4404840c250350084407a4008142405d83d00103071980e596006000c4150404420040741e966400410041014a02c1440c01602040c50068108443d00c0004694446000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 833759343 1250 833758093 833758097
    0x5060306040803070512010902090319170703051c0c08010f03170a0c1e050c040506130c0e03010e010501080d0302030c0a031e182607060203090309030a23010615 71
    0x20320f403900031400c80d22036071640000c6c4015580d581142400a4200d14a101c2c880d0042c0300701d500059143c04440d1841a0308201c4100e00c0d40e510a9442c04203620a00045040c400c0030302c02402040400c03180d10004901d401c001090314901071b40c005050050580001c0e1107140041002d0002c40d40250000040c629070130101d541d6103080c81000c0da40d69803452001842c0340c1d4001040c000c0704000410180301c2c54400c0c0116091504104104016154100d401a07089070a048980c900c80b6503a03004865084000d0512040c2e00d49a079000c41e094030b034000486001030791034000401c02a01c08105841e03800310316207411819420000f84000d040e22594506508140c1c039030100c1d1546002615028540c101131140410070b902035410715007002d01e020300003038507105080103065150302454015208890208112a860318056540d108003c0d00098140c1050744006d021140c0b160300c041200b8100d541c01440c00d1203040c09460556448401d0f01425120700e40d05081c001c101c0200c0814040841903014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 833760593 1250 833759343 833759347
    0x90a051504020310350318100e13140603030a090509041509060507020c0102011505012d0207081e0703030806040f14060f010207080601061b0b0a1401050103050603060408 75
    0xc4c25000ca4200b041d504800c242481d40f202080710314511055051004000c02d8610004442500c6801c1e101d00629400400040f0b000340e07401c0061520700386409100d00a407d00c0210b1110700d0700842d004480c00000150029510741c00d0310001007a130814107502503c11401076241043c00c20009040c80c3c5c15108550048665002003010010610f011500c550300450040142c241075081c040060441030301c1001c0580520340b000000c951060103800b03242c50615074219621407034180110f80c081c10300810f04101a514250081c0044005a8a00101d40080d8010300e86c40d8108001e56040c0900045910305041e4240808007035280c000c01c0780400c4a40600308045280d89170300206000e48078160003021602c0c502041e48200e49001e8002c40e0050308107503400f08860714808010ba1b40c0304518010345c05154020801004030174840c0328421a400261054182015121741c0c81540c000700c245c41c0c010140c0c1d21190015202791000c0c06d12070041c6001d103000c1c001e038101440480c2c5c42d098050000b410001c80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 833761843 1250 833760593 833760601
    0x2209020303040b070c03030801050108040b04110103110f030a0b0604080601060c031124060402040b04091a0607030903031202030f043908060106050c0d120902090705030402090a0515040203 83
    0x70700c00d4030001c00d2600006903584081d0310f400704503140c00740011030200310300c000046915442022031078031403036210001c120951034540381d10020000d9580480c1c101a154003000100c55080400b40c4800000c1048141c0c80341040312000b401d80308400304850080509000403c40300000181280c1190020305000c00040c0c650f0408840c01c0410480150f103500c645409044215640300719403900480701c844111039500e0b14030421040c0e119600c40d4091400f1309000078400844035a0004202100040300107a60f2901e060109425030000d21007a408a5400380040090603000411b070901401e40308801c5203545010550b1107480e000203800a4604102030b80d0462281e084481d000a0405003410004844200202d80452104107800390748690b0085a0000460342d02440a5540050469001e414041000c4030101d40c141d03900d0300c152010030380b1081618056116804154080e000e1640c820344e41e4641350051000300c031800b0304039069140c500001c000c01540f40b1800ad44902508460259507a12 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 833763093 1250 833761843 833761849
    0xc0c0f06120702160311010e030f0d0e03100603050f16050a030821090c1903030207062d050304060b09010608010515070b010b091e010e01200f07080c220902 69
    0x1c00007801c44120340c02c040001c818003003501c1b4844d2004400f607030344642d485e403103505041d107a03000c41e50707120410380c0722403186100c403806602c04101005020302124082407840600c00c003a11900e41c01a030340c603005804050001d40d414003d5010b64014000e8207a421450440841e02d1180b880c440940030760004a4103801c0c0b040783c00d040305000b01200e00001103e06260304400d848203001c40d51540314041c000c850b00818000c1c0e002242c01c99070150040d10a02c0d2a1801c01d450900011011504407004140825070003c0c0e1002a03c0c0d00d900c403595015100d03e0145019400c988070400b100380710f0a04d850040007a0360344008080d040d070740c080e03030511120300d1030540e400700c1800b52400c000e090384121000400d2001700700000c0c00c0360180032160b2020101134494408200b40304400091f0000b8600a04e1310007a50094815401401c0c05406c1781ca40e584245520034206841040d003c0c4040d00708500800900e0010800c0d90b05210048421604580e02c01441740c400703a035a009699515a120036503c0d0640d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 833764343 1250 833763093 833763103
    0x11e210e070603150609211a04030206040b01061706210105010306020a3b210a061521030216180c0305090d1d060a03020c0c0f06120702 60
    0x85403440440c0d18080e100d580141c098103104402580b80e0302e02800c006101445885003004940040c02001180d0f00385621806283c041c0300415980c010f50a2094010500001104ca201d00d001b82e01419071401c1c00d141611a000c0d040e4132040810009520b45c110a041c040369203a00820304480c1d4210b401e20400c0d6200754038150340c0c40c070384880d442c0400003c1400b815800038800050640d84501d510b0492003555000c044404240c800c050f14100888511032040c2d004070815204000c2280e0581c103050380070303015000000c100c10201c90f00144081d0301000b00034001c11300c014202591914083d814011202d025005440c40400610551007400044c1402031081d0345130700d1242c40c1c610280030388901d46d0042098410f2540c071003e034503000400d03501a1280c031805004040c00790192400044100d01154078040c5505400d0110300b8035600d2070400ea0355000280000081504c0144c0c652030184070050408000c268000d0003208160300759801903032041c00b1900d61300452071100b8a00d88410604034981 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 833765593 1250 833764343 833764361
    0xa091b0810060918060c03090206181e1e0619051e030412030f060b19021b03150a0609060b0912070b04140d051506011e21 54
    0x458594401180c000004280741050290502003409907a64903c10501112a0710003081c1031800b001c2081c0c8001902d0780c0000740380051074500440c1060079a00014421741c000540b1403000c492010084000c1c0c1010f25040a59514254500140c503d402021800401d0000c50400003102c0760211001c00c0d07541c150690b031141e0700d12950654410a031079000b40156001c1d1802d08401107207a90101c48001441084920807a400500d00c10710b1140ea60341500a04200c6400c58056600d1b0312012404a2486000e00f0201d000001d0072181d11000da10040d050003000c22a42e4000094100503120f152400100c41901e00c5100c181d0002998507100888020281c40c0c0040410702d08010000030400d200c80054030503014110b4890103008810f10141c1c2d0303a881a88074083c13076040300f0f100c108600c000e040c17240f01c0a582c0c05003000d49044d100d940c2c0d40d8101584d4070b560407540343c00d0005010003540e2160681910449075a0248054141000301814122403003011440340b2070041030203094000250804a40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 833766843 1250 833765593 833765633
    0x1a0d020301120b0108030406090501050a111c18080c01052a210a0818030c01020d020c12160f031110090b060a060e04020904060308070803060f12060a09 67
    0x803940c480190600b080c000100680311044602c2c000724110001100f118200c030b84e50b880b600511494003006607032a400c800c4d80034092040311100000d4859090020300030610121841c100f4904801e0000f5281c012400780144c10310700b40c0700e02131220b207100080c2c2c650681424207285884510840d605844900868a040340e0f880c4000f146001042e000180c00103201e2450700e131100b55040c10303402000e49015002c5d08800041c03251f00071412900158140d03488810000381a240341c403980c0c10a02d0700317a81c00400c01030641640049c505e0501d001c00c2c080d410f00170204a14051030021301107800254540b804d00090007100e03131900c5040c1058018405110503507034550580e5107151524821000402c4040d0040d150f40050000007500e51074000e50301015565261200b850406a00e07060000940200c842203411130b17910340002c400300e212400a0203691384a0010266240340100c1405401064510b006004020506c402103501c00041201c6500c1078000030001403810076070611010592030250b500f09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 833768093 1250 833766843 833766847
    0x41e05060c0604051002070f0f0203030c031605070503061006080606090d05060411010f090909060e1606030e010515090702010b101205060d05030f03070c0c3506011a0d02 75
    0x12090700c0c04140c80384560b000390162451040e40343e60031410707842103480c014100d010120a420002d200040c0e58108240061700322800e0410080400e8070710384c444401010014142c00c515000c010781006100041c01084d00a8800d03824104044c206a050034050a401c2c882080005402078403410280d40d2841340041816200c0e070308c80c0c10007030744640c419541982c145550885040e80355018554851b01100d039030351a110044c3c90035400b1001403c10707a4003113402070b071100449992980c2c10020300144c1e00340c03012219049490b2260180884004200b24035169061400f00000e1010003c1c038100c203110159840700312583e40e0743c000c90060071032006042d4004c01d401d08000d1611340c00034107a901a0b40110041041b501c450b8100680e0b9206008000c100b039004102c2c039440c0e01a48409540c00420710300301185000d0f0a661444020342d0250021146d2a2213100320003054240480c2150050b8148001e28080810001c0719a445ea18140500c15445020081701d10114034800d00300c1d00c1030710a4900440d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 833769343 1250 833768093 833768107
    0xc09070c0b07090306140c0d0c020a0b090304050108090d0f0507060e060a050a0c020303224209020a03030f021203040b010512150f040804120530041e0506 68
    0x500103c00078082600e8551800701c0fa0340e010b000c0352041a000f108441074070703401c2c5441c840854001c3c014020b19070b400c500030180d002c000180c00c64806401040d565020b152202c4c1020300040a900c2c009017102100e80c4440314111009400000112508081d80340450750b6080700d007000f001800c0502c035078403030b81e106801c1081840b6403154062806140312010500051069001c126170f2400700f5107081c1c18000540362907451a103c0080c5040c2441e11031440345842c0e22034407a040880c040900507800c20104541410800d815103601250fa0409103601d040086904a4021940104c00c50200030240868070b1b0119000c24000c0000d203021f044400c40d015aa441c1924107440600c1c0284246130081948415103003140c9800b180c0e0004d0340020191070303005170742c2e20104440f0701b25000c0c2c001c1d6140a0304002c04107c001c406841032000364002d0008207000020542c07090003500a0309006010b00041d20300b584288820b4000310b030100c03203203030000000c001200500400d000311250302c200e0f40084001190 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 833770593 1250 833769343 833769347
    0xa050c0f0a03031b080a1503080a030e1903050702220f06050307290a03060e0406020702100516060b03010e01060e090111091c033b04020403050c09070c0b07 69
    0x11029040c8640e42c1400042e0300442135a8041800c03031580c0c80492018000550420143d501a61080703268801c42568156241c4030300e12580d01449004001a41b01d545000281c001006140c00c00031030042003807011003282e1401450341c050514021300c6203c807502c0e0121440c4032012403c0b1003c498000130000281e80000340b00c020700c200d03c00c0b940a400703510400600c0034141f100080d042c0341e50401981403420781000302102c580c003c0c024034061680d141c0c40400d1a07500c3c0020305210314424500141d83d0b0b8207600401c81c1c0c04483e840d07540100481000a0f605480c0c0390201089920350282c0d020407035a04420009000d0001403031980c1066107007840c0050602403410900c3c0c050485003000300584107881d00c40c0f40542c440d411030680c00c40710f4510b0021030072a00f1071280080314041e140c000300304035500b01442c0c10480948070003001121a284100400110085188607064044500314502440c0d5075071203442c0c50382e04040b144660813460018101e00d00030700c1b0080c81d481d03021a03152500e181800c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 833771843 1250 833770593 833770603
    0x110c06160501090b1305012a120e19060b090c0a121b09032010050a050913050a180b0a050403120531031e1101020c0601140d0f03050a050c0f 62
    0x21b58040d820160104a0039024450140e030003906103100c28402c14881c42c040da400d05ca0b540c15040c1903541c420a48140780d2040c08103401e800f48450482030502c0d00f0703003884400d480200c44158403811030704050040070308a250440d654040d00703007004146021030030140c0b802010503100904039103101c2c92040d510b8540c0004240140c070b204254a483d00c4000800e0740307108461400c0f0050b0898444220f28840398020340c00b604080c01c0500e000ba01c0c0144660101c0d0f07210b544c002080c0d00041c0c4803030500061083c0d038080e210301025000d203007400700005900c6852003100040c006411039960381d0040703001d25200310748803074550700c11207401d0040d81400300301c14006558a9001880d258800d108d00c07072000510480e00d500c100d40660b02c0d008072400d00741c11074001490b4150240c0c14030058100c000d103001d40c2030001d0700903103112070040d001c0e0390315089003403460b00d030f990050500c18400d000d811400a440c428181c40050b805151803501e0b00c00000d0203440501c50b840e1108864403504808150003080014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 833773093 1250 833771843 833771881
    0xc0906050309060f1003051014090d02100f06090c020705030f03180409030509060309060702160b07030305100816051504031203020c01151e080601150c0204090b07080106110c06160501090b 83
    0x25694079030b540301140bd03150003001c0440c90047c0c0180e80845504500c540001c01958508100055030a98844109081310300c040041c00c00741c0c01c100010002880c082c8221407100981e00d0145141ca50118420350350b01d21807002e61032141d41d0f01e848000c00d0610450039200c04100c041c1c4000c0c1c2c1da0038080310603541c5140071a19000148503200000175810160340f0031008486000c0f07003503030902d81c3c255015006401c004085007a01c20b01840300048104040142c1c07034042c1c2400310b129203060704107824000044d03008607400c0c12400b41000100700061040b241e0341c81c80300d5686401610740c0c0380303031040c14050242580402a00c101500700411007950f01e0360310b07014040310004044030481c3c0c3d4030045504c035502481003000c0e66072103c8003490b1590244032100141840200000b920007010303a24440e044105554080010307001e1001881890741041c070306800050410006c00b04040032000054081c071504000d00850720034119604100002508100c035110b901c0a85031a00e0b00d0410042c00780075070608 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 833774343 1250 833773093 833773121
    0x54003050d0f17150a0b0d0e06090304171f060905070315090c020f070f083906090414160503060901030b0c0c0304090c0906050309060f10030510 64
    0xc40000041402000714108424490310fa41e2000114040000000036000b00f00722000c811005a8600d42d42c3c030600118082c02c60001c0b15922803440050801c03c0b06c080b618075049a82c401c200740071010800200791801c40305e04000b441e41034490100070a04026000313000141c402850300d091318000095401a50588003100010841d80e5103003070084040d50603000780742103801c80c8941c0031310841645070413085034404a4011200c043c0020f6840c1c80c0f810a10b68402c12402090200034000700303402b482301000004207858941000c041c02600c400d010820030782c1c0000511050b40000d22540c40f16000c0d6014840014820090343d904c40c20884400034044a0100c116001d000b0341c031501d10f014000341c0303000d028042c0000e0504da080d0794668080290140213030b0350601090011004403102040140094009000d002c10f18240c0600061702038030161f00030600b800014810410707200000101030380d04c807400f140842d20a44442d480f09002140503007000d809030292441d4260032010540182d09a0000c0d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 833775593 1250 833774343 833774353
    0x23040e120a0f1b0f1211061e060909060133080f1b090d0807080406030603170f12061201060303031505031618180b06090c040605400305 60
    0x3650f0401c0b0041d0103450061940c2c502410000205204886400450f44182864041941c5102d610703441c01504584032154200281841d10749030702411401a0010010b50350501581800040e15485034070501079200c003102c200814800010320140113074840d00081081034565030101f5001041480c003210004c0c0300c0058080401ca015103801c1c45415500310b40e608150030040c80004104a0300512402910610000e109030340104451500400041100c0c2c1c5002611910b1498808401000440040300031401406080307003020300c0008039600401314040304030403640d8080c0042c17911a8800521540c641c6456030100806426900c0b8a00e40081d50701105401d039030300c90030903a40d0100103c0c0d400c1c0765400c4140402001c0010b8003202e05091076100041a01c0d09400d171064514200c10703100303540100b480b4050085600b0030420071500007003d0b010281c9040e08090700034005215000454030881c101402001c009010000040c0552241ea43d1109502c803174110000c030703080c01900058a0703c2c00740d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 833776843 1250 833775593 833775617
    0x13050904080d0c020c0109030803041104110a0906032a0c0c090e1606090612021204110f242212140114060618040c02030c0723040e120a0f 61
    0x200e1340700342e0405a40d852003603411582c0700002798002900445100301d03c0100302c4030302c0d52280101c42c080100c000d6040c0e140c3c052000b0061501e4407d905c220300340752400261050411404190300c8001103560b0200c401051481400c03a1345008000c006004140c40c580d002c09c00440c0380c0c209110740150754084508034902d0000c1040f40d850548243d01c007080f03c640c7d040040c240600c0210f07003440e01c1d6242c010705007424410b03c242d409104603002c950b44510558002103e03d4801400c00c0041c005603050070070710202004040007000e41e1019207520240101c1d01d03948842d05103600006020900008110b400d03030341c0e4280031a995006400b11010003072136058411001e0144240100c11141c0c90b028940d0381c03144824400c1c9680005130043c0210050b51808809482e40c3c06910508500e5900a50b92402070301035950034100c0b507420200c400e4034807922000e10300c4030303a03405601d0542040704c0000b1002032000945160090281d100303802c5a60101d0143d5007590000c942d41e0480c849511003120042c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 833778093 1250 833776843 833776847
    0x306050f06070b06030f010207080301030c060507050703080903030c15010e0c1c110d1b120903080c0a0201091e05060f01060c110f0303070c03051b06070813050904080d0c 75
    0x40888998000d0014042c940105a2901180e03800c800b0103000e851000c1401a4050300ba81e01262098070010f00c0080100108560194120010160740c45c26a00301350640d0380c0e641c0c6454080c800a00068004103032120f141e507007401101e1120110000712111a45202d03240300c60070030b0910a59100c8041040020070444000b0304480c40c01c2255a8208090804034030301c00c009003076100780303101c00100a0140840c6600940b044a02d540204144107001c461448002060080000750b803030b01c600d0420b10640000b940050b12550000d11403a00e0340c1c1c56074070404040f030050003428805400ca40c0b2102c0390039074101d4403500e45042180640242c80280d070340c0fa00d01c0886010207119102c0000c0e800b40780900030481c4411120b5402c03900801c8042c01c40d202d40002440c5404c1140280da121040e01d03010010400100014144040180e001d01001d0380300c140040c265000d020340140000d27600040001040009803406009404002c08c2e4288900745030602e0540340d0803034008800c01a1400c180b40703524138 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 833779343 1250 833778093 833778109
    0x12030b0a1d0c0c0d0f120507020f46020406150809070f031209031407090e0c0a0513180614100302100c031e03150b090f040902010e0405090d030605 65
    0xb80c400003440080c074101801c4800340e44505c3d640b0200400c04680e001040c0d024002d20b0301075001d40c1e00030084480b91100c4503080ca03903282542c13035504c58003074000c2e450300c1d041c1d4034050034081c0b0b51080380843d040f64600c01e80e49500580002075009240010200300842088491024450140d54409095482542c0140d40300c2031b0b401605504080a40104001116002c0020844c062460004d400c04d507203684540703454080c2804480c40d17401c0340c1d001307101d078511a105881d0a152000010b00c00079240c072001c2192080140074190240182c0120101c1d40e2030741d42c024050014103801c1d00c009140e11820001c000b041441c841d90b111040c0c40740441c4040b45c880250034143e98000f41418602c0036054003d58006070b0292044062215034a080c0311500e401c01d07ea282421026100070440160025981d10301651a41003013071a04070501512038991641c4110210304c400513a80028041c40741e00040e943c0000c01d210744c5a0050512080180c402804281020500c905071428003107070b900c60013000401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 833780593 1250 833779343 833779357
    0xb0406030c0308120c0f0d0b0f030f0f0d030213050d0f0c0602031e0a080c0d0f051003031106100b1b061302040506182403030c241312030b0a1d0c 64
    0x1072582130040c4d2281c9405944101034100c0001c02c03010b0485207500100b130918880b08039540e120b402410840d42010700a02c20090340c0c005504d030450c83d0401e85802c0e800b1b8449217004036070050080303868001c1080341020b0115009c50308494000003441c1c1e5036200960360b6000304000b65000e4104900114050641400c0d40c070408440d0300c60500f0340d80c80e8000a06640c003c00301d9044540d031260b010300078007801481031502030909500c00760701040c11410040d125801c0c1c6001e4046a030301c40d01c10419007140c141c00000030b980740e4040b007950f2100014448070f91650805d0f10b04605000b10b00c18042c101c540c501c4060b113203a2003554148507a030707180c50400080703400744002903405164050005084510805a8500d230b81606401d030301a030151140442d2440d04021541c3c84103a000f6400c66582d282c21460000340020280e103500171510f0b00000072901c00410050081c24031040714095103003d80030fa00050a404400740c0103c054540d41d0308001907024a40c02d000645488150104c1d60f0400310300d04803020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 833781843 1250 833780593 833780617
    0x90609150804080d020a05070203120901091203050f0406030507030b010f1b0510050408070302060609060105120910050a0c1814130e01050a05060907080403120b0406030c0308120c 79
    0x11190403000580364100002c1086610400030425144070034107520181c954110b05984044d140c0c002c0e4030500d17242c42402c409103109201c061003299696031307010cc60380e0151211401510a0804940340660712406100d0289104580c007040201b072217079155104910984080d036003401104180b90041d05e26003484954140020343c010721000740c1001507141a0740300703403040b07080340c6048004a000d01c0c201c1d403040ea01150748000001d40c0d9000d240e410002c954000408030307032000c01414aa00040c15501c0713015402c0311a60500c40000d100344c1014400e00c01c408010704003c0c411450110240300041040c0381070030b40860115806018182d4480c1c136142c00b603031421500c0011700781000c402c108400420403c0d41c09000c1c0c9070101c00300c441500f0301415004d644801c0c00402c09040072020840100b400174214800c1004070b50401010039848480e001e052049440c00240c0f50304105c0c0410040d01035600301401501c03120800104000040000f029501b07840904c4454a07241d00584240078490601c20b80b039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 833783093 1250 833781843 833781869
    0x60306282d0507050318071d1803030c16050c120c040608030f0f0c1f0902100e1e0a0b0705061608040f02010f05160f230a110319050607090609 63
    0x252003000540c20b64001d010106c201c646c0d940d6100d841c507020144000403208041e1026040c0408030444800d044000c0d07070501c0c0650b00710329080d0718402c25806001c0340088001c143e040c40c8014420180319110700c0113006401903911814482c00c0c190303075001c11088a0b01a6242c030400180c1c04d1004400d07540c01c11000003a191402d080304031a0b409603000700c5500c4c9564001e07051006903001410b12070b001d40c400c1507080860090a0360040003460002c1d07120130420701c0074085210a0555402403808501d20220316520410b02c000804152148101d80099183e90b10004144040c803c001400d244191107140086a140402d00030895140d00c2c01d8030b00800141003128508015030042c140f09103825a80c1c0341507070422001070403801d448200c000c400c0d01c4040034074510400780f00301016824102c2100f1805100094415444030b80e4440700d07044043c04001c424000c240c0203035800e1240c5e04482c844d00c0c1c00c0300c00c41c0c4400d00b00700d62680c1040c3c9a03000403502134000015043d025031503540480364110a009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 833784343 1250 833783093 833783101
    0x411030705010e1002070e01080f010b01050f0a11010b06040b030609091c050c0c06030112060b04050c040e0c0705030705071d040308010b0a020a170a020601050405060306282d05070503 81
    0x4a13802c52041c480154001d18601003210403281c45894000c14441008200030110030300401c3c215070080c0401c2c1e04215081242244082c101e0040303c0081c03519280c9260818400c0207003900500700c1c14072240d0b10080c00500050121008409140594021103520386a522062441599421100b00c9480006106100c0c0403034217003c1c40240400c00404011340b001d20460b40002152640260011a610030403400c100090200500c42c154880c3d4043d91300b00494103040745c040e6040e004601ca21861400310a001610381150b010503152690350040c1100d884802903d4002d44601c1d190042c00b503541d200e0a03440c00e0140d8030b401c48900030754140c1c5401d4040e9007403421540c02c03940003030032120a51080c030402d40000f51a101105105141d200f16403074941620328802804c007481030340b04a00c01ca06003230a1000643e804075000303030440f902501056100b140040c0d040c85400001d10040c49840c43c000c041c598005070012032815038401400383d800904140540d5600300d4505a0348080045c42c140001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 833785593 1250 833784343 833784349
    0x1030c17010209031219080106020c0d1109181501030f0308060102210406020f012a1205040b040210030504052e09050d080c0c060c0a0504030f0b0411030705010e 71
    0xd0a5004280030000d8a49807209000c68504003001da0b80124104000402d04855002d2148202000c683c03031400d90000e52600314001e590303441c901400c5e4031640b5846201c0007000f1158500302c24080020f80b290180b8030f0310030290300e10203101031700301700307280c02a001145861041d841d10503041c1c130752212038010341d04420b850860759550010140c1d81903111300e1111626480c0c00311403a101000b087c8032001e80d51401c20200038108040308951070f540e07a0521413585843d0442e400c1181c4001074160180e02c030182c600204a44060000300303130903410ba203040300740800d11403035102c040e1081c0d00035205440011310340380d0111f08403001100e0161440d04981d00e48198500500e40b4000d2207922415001900b5402401d0001102c21850044840d81e0000e1200c43c8110b0f004181e45901c031000c850701504140000e007549807650b1008289840304600015900121405181924095a00864145198030035480c2140d0700f4603050710143c99001a00e6144441854000b5000c001e4030010b07550a00408404018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 833786843 1250 833785593 833785619
    0xf06090307110f1201090c080c01142a0709110711090402010e150304060e030c0d050d090f03020c13060510080901110a0215130b0c071506060f0809030301030c 70
    0x49500694a41000449944241e4820b1103003180078000103c6d40407070714002180d202958043e10154005042801c80b9031380003a0303040902c501d031620865640e038031070078142c0c07040d240c0411000541014440ca6111002c002a4030030607200a02e03c2000901407500c1d4050f4180540c010062540344055201c100310300b0700d4502a80c10a1060405c142d40340e101800165002290420a0103502c17000700411090000a019881d04a01803901031481c1840740c00040d030300d4201c1655548140b01000400303054202040d48001082c0707802905488110300d41d8a40292141e4031903940d948075207281842040162014400c18044400c01064115002020002520842070044c48a0195585c904c1c4030f0300400d103040003e25000400350f016003c144404c40b02000310b0200503012000f000e4800d640310000540c0031480c103400c032901e05e0015484e51040d1a000507076a801e21807050b03080341094400565140c11451050280040d80c64034000c6548001d10503a0b40d000911000d88006211002000b210705030800d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 833788093 1250 833786843 833786873
    0x90e06010513030506150901121101260a09060b0f03030922060b03100603020901020304210507060201050a0b190b0901170112020f0d0210140706060f080f06090307 72
    0xe0803000c90343e520f03190b45013841c1c0104c0700d103441d0b903001000d03001d404c1ca400d9191030b014210b44a4000d241d03880c107841d42003034501c0288c03c00d41441190502e480d5600c01d01c45025020656012a1003c01d1525440180180981c8101221002d0414011509038a016051039510010140041d0305004407201041100910511944850b017001f1507440c0402001c0e0192070007800044000a5490030542d580440c10303400e030390045c0704151060280700400e0380c2c003004440071244d040550802c010208107a000c503051140000900501c2034490006043c1d4043d040325200c1c019041e010450420000d0030320004d498200c9001e032072140003070801c0c030005c0414800341c01e505406250102d188090000320700450402a0044468280e2002c0500c00b14580800c0651105070151406204c088080d8003080042e9400e180342014803200d041c0a461294210050314100c0e60428003d101ea540d4030b00c5010300c2d00d0307128012140039010f2641c41d00e008517000101c0c14090059540118604000c980341c030004a0a80b01c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 833789343 1250 833788093 833788117
    0x1a01051e041a0604030c030302120a0504030602090a0b0703030b09010512122b0504060605060f070f03120f1b05030103030503130201120e2d0709110702150a030c090e060105 76
    0x180c0b0348a15a01d4000181000d0340c840c9003801449800c50501920b05960450400c100e14020040d1840705903000c0306403021694010030141e1601000350000d5085500380d0030030714103140c001c2512000d040e4503403c0207856100c107554188103a43c0b40c0c2d041c040100e51548842e001c80d070100c01151148140c0704000c2c4020307040400b21002c0c00c201e541e0031802c805641c8081c608604c5d00c85007404140b0803144030ba280100300450356107160011600b2201300500a4150190aa82948985906144c050b1180d403c840404030070030801c211080c8844402407038900048424500710b8550401d1150141c000c682c141c0b41c041c0c0b03d50f0306540d5080b07201316000345140e500302d04002d141e501840c046a030714000c810000a4a8014003150030b140e040c41d00b1403040b05448030452960001e22000d800a0102d0b524080c0c60f07600c0c0e070105407010a4dc1415000d807081c80002034016500c00d81d4641c5c041116030180c00107a256907002e0200380351203002222074080b039004541d2142c80300d401003225503000e0301c0204210b810761 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 833790593 1250 833789343 833789381
    0x1501020d20070314100b040b01140c0a080d0207060e12190c02030d03021c060b090f010905030d020f0613020a182c0706110604060902060c07031a01051e04 68
    0x203a03591083c00104d014a021203a881004e1050342e4901ca409202c05403241541e08104c01c40300caa000801c0e4040303202c03070b0070350300500001e00103801007090054804181c5c01803505503884101099100096000c0707442071392040e103811010780d2001808140300019190451009082002010042c039a10034948454400d2181c210742410040e20144260180e4003413a883c0140c5600404454040f0b10ba00040140503162400d10140300c089001015102103100541c2d05444042d04a00141c80310f203099041070344d240c0b01d000c07020b40f1502d90000e104d8a52520110a88180303840c0c8940e603200a104012000358802c00308c00c030902108030606040c0011480604000c150f040c03e03071030760420b00d0142030140d08504040c0c03207028000c60000c000a00c0141500c2c038020440c48900f03040740792a100c0c06440100650f444a810806540e0b4034810b071003040400c10305442149a4074600f070308100c004685200e000031100301c0001818500152101c4000c4500b0788155054583c020412000740383e8148600d028000c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 833791843 1250 833790593 833790599
    0xc08180d0b070302190203071203180f0809010e150f0f090d0302062706130501060503150718031a090709090b061513141807081501020d2007 62
    0x824010349004038600d443c0140d90b01320001c0389a030007031807044003141550700c00c100c0c0400040c00414280d806140c0c0f460b00050000701035200c540404c405240c05000c4800c10701040d010311296600900c0a403009888981c0b009031418103100d000d502800c0c402c402c4007414801d5171701da40b0202c402408409001d0009600e06440c12001807031480c0701410503801030f03010740d04103c61440524680d00101d80da810500403503030200341400350b484030010080d100701e029200914040001c02d41000c409440e00074180d40324800824502c420b07041d002c442500000308056005107036038480c252050207403a00700000d0f540c0c010000c08a11071403c400713420040b1610401e0000110b085240c0f05501206100300b03080701d82f5042c1581000000c07040c89004410f07e000400c4070340444a40700105604039a107180c240000d40c030754080024000724140044c9200352480320200f00300c50741e10021061042c0e548440301d0840145180c012030340c0c0c2c003203985080c0c04a0100e400724a42c802088608101c840c08120032a401561 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 833793093 1250 833791843 833791853
    0x3080c090d0b07080f0c04090e03040f060f090501030207030c0b040c0801020c010b010305090606030c0d031814040e1506040e01180b060127060c0311120406020c010c08180d 76
    0x754816204010325409100c1e180d980645245e80245d0003a11045003410584246800d5202d1445104015540d42c440c15000140500c01d8400515600c1000c12145654843c0945601c4030400e1040019204190205a41d8000d100f907a000f1a0182c0d294181038405a03900058468058001d9400da4456040020224400d000030001010030000101d204410a0005015039001800c02d50607034005004014690718005405206040d04a5060300c29560505080c0d81c3e9680f0880004589000c0c4c1300c020401c0c0300c034038070041c9991300b0035070741003000743d410540c0582c407954880d214440790764005010840303e1620350040104040ca400001032200d0001190340d4007a04240412a44864400100942c030360f00500d0003074a08102c100300da03a070001450703d03550200700c25004010074407582c142032905040c400c0c0c50411040900d2001c4400070710840c2c52701815600284500e4005105901c1c81c9800b5501c1900091079103980200404d082464100c031900b5442c130000c9945400403400603180000c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 833794343 1250 833793093 833793109
    0x1a030a0219030c022112220f0c091a210a050105010509060a18020a0903061d160602060103140307120905090c041d07030b030723030d020a03080c09 65
    0x92426240007070220001100a41004280c03412a800f070b040c2d00030a160b4210544040300c905c00c0c0744a03010040b47d9152084049503c0e1a400c405450301510013024080000321800d1000b12070203502c0303d0ba490303507441c140314007039130511800340e144102c00b01a501414100b0b40c0400500500c5038104080380307001a040c2e149440c3e00050f09075041d0791640c004105c0350030301c88030712500080f00b0381d00740d40c84070300f4030000d0800014074182c018170f0f040e400183c14003820b200d20141d50166903c40da080c010b150980075010705440401c1200e103a140200a502d401c034194581c11042210b040350054051a840c540b140418070b03921214801090104010030000108034429102400109450740c601050404e000e010040070018407051002104010a020000028014415500f008070032606aa659600e0480142428200c2340341c16210740d520100e81c400700c000d10b44100810000b4203081d10000c1030205a51101c400018102603002a0716010110784200c00346ca51010501c403103d4601000200030030056 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 833795593 1250 833794343 833794387
    0x4212616081e13061b020901090203090c0402131403030d05071e02150a0207111c06140c040605070503040e0114190b0415021002030f07020d0203041a030a02 69
    0x1940001450300c107102d01240380400400d5960b402600f00382501c0c080c4040c280c000d000d80814072440004c1c55409010380d504500d4030310381c040d0030b00b201960346080e4100a07410540c0c104a49020340031102c6042d041510a0300e070045180842405900d140c94003008050211120030380e0140002c00c61110b1005050060314000d09240d540c0c4004501c1c40050701c48441c2c00800780d94115048240c51400c80480c42043d00d400501c0b180380180d81c2d0355a4942400010000079105801c070b0f0000c0140b04000c0f8495158000f59809074509210040200500314003519084403150b8400740140818480103114070041c10a81c1d101d0821a85003c0e120300c00003915030003d0b070141c903119491000001007030a2113044813042401d600d42e4074030500d041100081382402076010f0346412030b1400c03c00130441e038800c06c020003280c010013008640e03900300f503040c0030300b07840d0308980c00b41c054815421303148042c902c0001110200e8250810f2075140e2910b02c2e800202170750001c0c002c49105c40d000c1c00f0490171041e00b540c500c114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 833796843 1250 833795593 833795603
    0x100203130302070e1e0703020712120f05040206071b030b0c03040c3501140c0304060b0105161101171602060105030706050405040b032104212616 64
    0x38240c6150003442c000c103c0d008440e4241c4031100b445010703484113040c9001d04400420b110511354a104045000f40039554001e0440e0980304540030681d07070060312815900c00086001d1040310512101a02501d40540303009400007020401c05010a84005034071001d00c01b071100c031845240e43c3e038461215010060701c10a10445001040c030003082094401d110081c80f004c400c400c2880100c11550940381c6d03a00910307000349091044080c5000b00c0a41c0480c0304002030b1110070009041140607074100e40c108540c1100c1092400384000e05940c0a642903c19821180e404840d0f6016a0b40c1c501c088450000c8407241840202d0005194604c64003003118402c0b01c140803019039600c28050020b15144043e80868040e8002803028030101f41d018044a0685070165004202c00d9803120209151521505e0708941142e28014145694403c0d4001041240c01d041540d03841c01000f01c0002c402e5604144006011030041003200d40700304003072010310013400c004000d102d040c524a41d1450741d410511003400c1f91 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 833798093 1250 833796843 833796871
    0xe030f030a02280209040c0b0c1c090510050c03040f0e0403020105070806030312090c0d0c090606050405010c020f011110060807080c06030103031b050a0f1a10090e100203 75
    0x415810003c4154403100e0840900c0c1c40004103001d11400d00451402900803450381000030180300650070684024a01040f405036200380d8148115194442e039500c00088041204078190950b00c6845044c0036228010034510040c0d8000005035501e80c041c21700300841d40000c4c403000840300404d00141c002842d0028401d9518a0070f494001d003105c4001b0540c0041c031020700144a6103403400030650b24442c090144d030b82040e80354005010b2034816400c074a5603005c0854041c1c0b90400600007114402c0b0f505c0d000c000e001c2180c03200c4050314540503034010280003640c5d1010310300141c039240c0078131040e810f41030500c940c43c4951a100c1741d0901e0900c160b2208950344a01080007a410100000001000c4d0540540ba61030103034000644513120600c4003038204610f0b80521061030b4090444100c10980c41400c6440c8045240744c0b4054156152005555020004920100e000141c0f40c0d058410808505108801402c01605000800c0301946007402445140100d0307031744000c0c610003140540140c0c59005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 833799343 1250 833798093 833798107
    0x1503010302011206150e010903050d020a022409010e0f0d06020912191407150201050f0619090203130f0c032a05010f140307030c140703020604120e030f03 68
    0xb41807880c02c8800b100740d0500d401c0342003000e842d410791a040040000d14100e03c050303041800403110b5200c2340d013014129004041c3e00503006900041c03601740440c426186080944042140c1002c030640b49413048601c113600b0468075042c3d40c85816101d003420001030400000d0038800c000f03d103c1c5460180115a03440e400503204005140065a603d0342490500040c00c0035140d505c3d00da09141c0140c14000c0c08403c4601074940090014007200000d4074003030ba0450700c0c0300070200c0028042d2005031000c079075501091003c2065030510a50300002c200d007444402d0102454050104002d6200400c0412410140c107603a40010703282899900d0b00390b000b24034500d202801c505240181c2c0c501566105901c500c800c3c9846180510b1a0104003180c1d800d00300980d08181c1404251024030008c0c0c0100c841e60400410051055050b40c0b00d0110b1000c0b07580c429003c81540f145100c0035104208015000d6440300d40001e002a04001d06403003022081e24002c7c0100078448046481c0055440101035944c001003a50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 833800593 1250 833799343 833799347
    0x120306090609110d020304051216152d06080a15050601030b010801091e2405060a02030f0309122d0405330c0a210806120c150301030201 60
    0xa0019000c2c00c802007000440b000c42c0f203201c1d44034043c455040c094000c80020140f010601548406541810313034940d4543c51b0100c2c41c0944607080b0022a4038280c841219400d03c801445280f512035026980100190800c110140a5010f03031658200c20300e842d10300204045000b0f11400394207a10030407039102150035080c01002510700c01041b45041601e03001e03d60300070f41c0c1d00c180380a044904461002480e19401040c0203200180e0445038003141d410030340100c140148400000d5030704070044001e00300e03071398445080100300e204820060005034000d025041d00a04c001c0e0040d03401c05040d00494600c428104410202a0420300711101541c00141181407800401c4c90280f00d128007450029181c06c0c14200000c00c0c0c0100100d680c4c03e0141c810001c600242d1a07030109201880f2509111a10345c2100500b0303503640e00f6a0041181c80c40d03850301d440d040c1908401c00011927560b8540328901b8581d20b01d405e10468850018040f4214410007840340341e10f490703142d0064050307148000500e90360b40c114000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 833801843 1250 833800593 833800601
    0x501150f090507020303040212070e0c0705011a0105090f1207060216081c0c0f020a030c05040606111b01090b03090d0e060a08060103020d060807180b09040308040f0303020712030609 80
    0x505102c00c102c0441c1e808000c90f503006604030703076a03124900001c5140349481e6041d04141c8210f80725401f4024110380e1400503141e9248100000d200200c6c1c6c19090030b0f414032003045014003054061008154600c0c5c9090314a14540380580030218841440206510345611a400b400250b0001c21003031460201220366603016040510080180c8880700c2887d079461100e24444004002220324900c00700b081044031042850f0f0001c03c8484100c0e2a4100740e000440701d4881c01d40b0940c075111000503180e0180035004440c0d5002c00140071014143d01d000211400b0020f400d5041106d500d001027143c54222001e14000d282b800d0042040000c03404c809030401049507a000d12802050116244459001280ca80d000f07000f0718016841d24111800704d4050845500106641c0c002c1050101c1c44803a004600075202c6480720082c400c1146200500c0583e0b1002c0d900038001031100780c0040c01051814490260082c481c2c50014038200680d2108094880141e100000003034842c04100700c8005c0d0303400303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 833803093 1250 833801843 833801849
    0x70204110c012007260a03060608010f0b0915041a18010806030a260c250806160210050a15051203040608060402070c0b03040c090c090b030604090501150f 68
    0xa9038155840707000c03214849400781943c020617003440003104904580341050600086800d000c2e107030340c4442501401134003605660042400090b0b801c030000600d001683d0840040f180038681031440c1c010000203011007d804c9940d610036102c81000002001101a1781c10411013407a0400c00f511500001205102c20143c140350f103040001c0503042c4400b503900030800711102c60780901d40071811020030402200803c04445488218500800d4100c22640013140c80d99514001e2440415010a1400c00860629a0340100c103405c0c1d000d0340c0000c04080201c0041c280100e118012242400030a2100b141a01c508807030b40c454483c0c0702c0b00c10300740c060f0070206010b01804003221000c4d50715070306401c0e46a4900440c4184020000140081030040c0c4903681290005a0040104901c0548500880400781d106480840d00b60040f070100041d00744c80d0341316a4002c1a1540d40304208a07192028032601c40d0006800c0b280c1c0b095603520503100240d02403080c0d144032854103182100b214a000141d8a00c42030540c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 833804343 1250 833803093 833803121
    0x2150301260706080a0c020c0306160206010b0301031112010204090501170606030c101b0b01030317011202010807080a020d0c1214150909030c190c06020a020a03060f02070204110c01 80
    0x30b080c850b1540200501c0e034801000f8a0028007a903181500700d1404100c0b03c1555098000c500030700404440428180d001c082e8103408440c1c00366603404090945110900c0080c0488402080082c400d10340324200d400b1840b1002d00160805448010080884800ba40f06281c01c041c41111b01e000c00e1410310595512642c210042c040070381c7c440020400480390f00e0f1805040140c2d060465002c0020220803a18881d04507052010a60712071a0240c0304900364902c410340c210211000040000b900e00788400559410b0f500e04510f5154020280c440c5c102c080d0071811016000d0050b0141c8050b81d10942c0c03002000341d602d0040400500310300d1f400f01c03109400115403480e100701c20407800464140704ca2260b1041902d25098543c0c07894a05421030140d90324688050140050020781d0011000c52040100c0c0944180e102c0360355a01c01c2030383c0d544007221000350005a00002000881c08a038005048200b00c084c01514102807940018201d0b00a0780c0b24955031000130400300c49180c02449460204013000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 833805593 1250 833804343 833804353
    0x13021e010e0f010504080f0303061f0f050a0e180708060d17031503030d051e0423120408071a0a0210090305120906160f09060c0215030126 61
    0x500000c1c40401d03001d10260084600c0740c0c55820030703403240040310f0090111805661204401408250b241d500c00e07952584900c400c00000c80388141c040050080c44030907621010581c008180041d14250041c1210800384021b0318000c8426807200041085d00e001c0d50f18000d51a80f138407030750281081802030000d0b0300501408007000c0001c5d800404280450790f0900c0301c01c0d02e955a01c25440c00c0c0c800201c181e16014000490010b44c01d403c43d03000540194480311100e6040203540c800e4015021044401405480141103d21141d4480c0d039806240c00400d401615020f0883c000f014420703034407543c88900b076a4800d05040000a40329142d4004070003413a03181c6460031081c41c1c0000d6842c04031407022005241c4d203444040c1010300400c229603041e00965040500b0b407070b0a1003030f251502d104071881200040c0c07021101c11000c0c814103100c07002c41810b49031900b6960030a030f8100d51031030f529003080380c0189030703010101e02000d5000d01035070003452008000048002c1c40c3d60300c90001550b01c43c0b40c106a80c09 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 833806843 1250 833805593 833805649
    0x611121b0a0905010e0d1703090105061e0108190204060f020f0d02030702011b0c03060f0c110714041508061f0506180d0f030806010e0109080a0206071a1302 69
    0x2101c22901d045400900c0d0001c55440c0708030020342641b10428004210302c2000490642006071440034611481000c40200446c0d83c92009005070b17060100e40101d154040d0f10700006440d03000b040c50790f400c40c40c0c001c000c40d409061241c000b0200c2e1300c1600200301003481002d120581c281d04024080120390440c1c00303000c240300e4828010f50f6074080c01c1d0000b03050052008085010400c02103100d004d090704199012a400d5aa05150004140050307500080302d041c1404024800e006503038401000c0017000c02031285a140c145080715415075001c2c4154070940350302e200074450620704598005003001c40e02a00b580c1c01c144100241a030030401401031f004041c203c040010b603581d001521255800008112400140d400c000788544c01407840c024005200c0900f95010315030b20400d90b500c503070303800c0e241c002a4103403400c01501d02110391300c0b915003c0c0d4000c109140050034181c002d004514803602007280b00008125000c0a50b220032175901029118005090042d172805014002c0b914054000103144611 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 833808093 1250 833806843 833806847
    0x708030403030e030c12120a050f06151605010c090f0f060e010c05101401081216080403050703030e010207170604140c10050309010f0b13090611121b0a 67
    0xc0c0058185966611021040030701403084402c1a54964183c855903804d805460340c040e000f03601c20348220382000b800100680c9042c800c1500451390215210010b5a80c2400c001c40354007050a000e580c80c0c401e00c00f0720108544100b40c014018482e1001013208140100b004160810310b80c42103016240381c10042101da000e00d48181c060350304a00c0c12100070100345006a07211445020b00030101d02c10309100c1100204127921901c00e0030f4402d0403091640e640d86c5101ca82d100440e58422920072000c0040d030b0207080120044078081480b0b01e019070b01f0329036640c0ba01800d10009074070a4000c901d0090700303141e45607410302c522000340404403002d904c0340c000112010358a03000240001c1055503180d03c5856498400c028a0712030a000804140464202610040c01c503001510712000642c00d11b44110016a800d0142004143e4040c0254542c000070340b00b03000203401d0140e0259055940c61025112507040f007030040c400030303000e900148c45900b031861296030202c1820132050940b40040c01100d80c499 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 833809343 1250 833808093 833808097
    0xc040b0c1c2604030504031a06041b12091a04080307080c0301061d030106090e0a060608010c0c2a0905060316030b0601030e01110705070e070c0b190e01110306040608030708 76
    0x4500c4400d02c420300d076940d140a442d24030982e000505900b20030401c81e003140c1900c19440d4030565041e00d081c080c03d03c010080081d103c081d65400008110589803621030354555502481b13443c1d008441007404121000d404000508003590182d40f041800000c00810030f03040044550801c0b000201c0ca89150715040009142601c2030700d45600010020b40d0410f00307039800350001005052120010401480260000c654500000200b02d07503050422400245001041c840c00100a000c5d4540482401450ba030b0225101c03211a031700d00507900c40750001c0000403050704140c801760101c9040060b20b070030404100362070a6251401c640049a401c107080c03001446110010760061000c1c2000300f00c2c50303881c0c11540e024049002c8010500c0f0b10100c2c00101740080083c50700111400130444046507225008211201c0d4090600640210000740c042810100d40d0b0003445000d00013030900050600040322040e00f5100c81c1c0e00b4002d0400400f0080c44001d15203403003030b44000c2150311b000710b20323003511582c804d020741c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 833810593 1250 833809343 833809397
    0x117030d0c030b10031d0609060f130f0510060b070c05100201020706110a090602061021060c09051f140706140405070303020c06040b120c040b0c1c 65
    0x551030360748801c6460b0003034010b0300c01034100600c03084001496040060041c016889a0051020b81c100c48254080c000705805000e452607101621042d0340e09502d00340500300141070034901ca2111140c840105079806901603026104102404503141503c2540080d14032640080f88500010001000001c035804184011181c003070324603403458498442c050b0b0090041e80301c090301e41401c2841d0300b092100c0500043c40440c00d03680720030030100d45400d07040f80d81d520112062031140040d0003040c00b62035424600101035507201030f40c22010190301da1f9203100340e50f58a00c04202045d04203c2c2844145032100c0b000b001c800300c01c02001c000c003000742c40042c60042102c44d0001d01800010700c0009100032504840d80f2440028900c282c41d040c00e18040d035451140744403d40041c02030a0752040c1c1c900d00541294100c41d0190307101c0303081c2507105a000203408400ba081106480d0100400180610500060b225000004014102c4d000b0103070281c41005010002d00c9040010000895a034001034103d1007003a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 833811843 1250 833810593 833810617
    0x809060a230406181110030203060d03121512060e060712050406060803030403050c010b03010501030b040201051b0f01090605220f0609150501050111121e09060a030e06011703 77
    0x9a00c40341804001015440d110245404c0401400b030140100255003121054083ea800b00e01c281e0072403000c404070700047e00c405600503043e450000209200c1c09080400c881440b500052448010031130081518180e0701c407148248030503444d0001d0016502c5251901c500390b4002c1c01661400403030080800c01801c45403100540e551001c9800c1c80b2f120340c04070010b803403a401201e650b4107003030070302034183d820054030603000e90f080020303420079401e040c00f07007038100e0354030032001c03180c507100c80e4019500c5801400e010917181030701d0788581c03004007402c000041c1080c0c0c401c800092400e905060250907141d0040400304144442c0300c40c0c00ca40b104103808205880c2d0814050007444240c0d181244c00303010300b007d01a05900d04400703140c580215030350000e4100e50003600d40e811166400755015850b90940c00100804240500441301c501c89190b5000c2c9190b1000b000c524a404081000200c031500000120b000099840746d031403091900070010180544400c1c4a489401c02d00349007200e0303032442861500a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 833812949 1106 833811843 833811911
    0x1a010f05060f0901051905040801060b0306060f0f0d0203070503060a080f151302060309100e0307081e04031a040c0605120609040809060a0809060a 65
    0x1044820103840c8a08080102800b80440d030032881006050001c200904180003003800355000146150f81c8420341c0301c030304211600f03084410940003210000d204005200103543c0e60070984000400351302c04039076555516600c1108600030f09030814140743c008000d00125540040245108140580d400c140360b0b55112a03165890701050350704100c642080c8016440303c1200c480e0703182c0c404184e00390300c0f08030141580400c002d60710440b04024141c129203400650f0b2541c40c000c00600c04a05001181404d44540701c0e20750301d103c1e00320070b1040310480001034050304a0b031006842c01107030024181c542a20780c500b079004c50000100e40031143c1c1d103194400421414007600944080071034290034000240d130303204180401031001510076a5074041c1400f00c0c008aa0750035005004420040ea07580c00c2074100156001d103819809000005000d0a000d40300428000c05524200d58210303d0360141c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 833633093 833812949 := by
  have h0 := BRFrame.cov_init 833633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 833633093 ≤ n) (h2 : n < 833812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
