-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5470
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:58:01.348975+00:00
-- url     : https://prove2.me/submissions/486983ee-034e-4cd6-8dd3-d6042a0c1303

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 983633093 ≤ n < 983812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 983634343 1250 983633093 983633159
    0x227130e0606190e070f050f030405071a250206130801020307030f0902010c060b060d060902120f06010215040c15020c0a0b16080702040204080a050a03090501050a27 73
    0x4000140000455480c1c600c4001040141e48501844d42c10900b1071802d891030590040c3d00307640601c2100c0009418041c0002000140300c804614074080d940303201602c648840705507200903254080c03500820504030714526038042d807060b440100c1c1d50492014220740d080c105221152001003400d60300940603650004200410b140e458800d004070200039100030040c4da02c050300000c144582c882801041c0e590742e500c01ca0001e60750042035402282c09143c0600c01c0a45032040d03030010b9001950550f103800c100e1030200780000c808080d41440b95030103900500078000c0840e080852130902510954074228541d1000c121510201001e20190f03019400906181000400340701e1100c82d150700c4480102010311482580650107280c01010b04d070008011703612a441400007500074451580100c0c0c1e14801c04001108000300810000340040c00390300e841d200e075941c407801510f440c41048510000541040600d1000080f1004090f0200000d00b05810b80a504e8401c080000408290840c05600b2010305031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 983635593 1250 983634343 983634349
    0x415051311040c08060d060b041506031b02250e1008060702070b0901050a1b030c02180702060c03220503041502030403020f09130b0a1b02010227130e0606 68
    0x50704400000d50301040782402621000300100e102408051051410440142c20b01c05c0c9038001003044400240200a030849004040d0005007a0340300780310100342880303802d04100c00d4085a11160340b0090300541049512034400394441c1ca14401c818142c00b00d566030100d0f684200000c2203208101540d40e0003072003400c0118543c42c20100404480441d800320304240b00f00303003990040d103014181c207081103525401c041209a4061405d2001944460414190708040c194810101c4c64418001c3d12007800305140421100250b13442160414056480940458503031703c041c1d002503600122080f40d00c00b04031140290250810a8040c095407503a00101e02845400d05c035102c10840d4100344d0004500e042d18660202d40300008060710310388030359004000624030351010495515103550108040c40d851a024100078001c4c40140c040b0000c9030a07400081c843d90f4014401c4905010706070000111060540c06991174400030260070580180154800d80380540980c01001c0c82140008068440f40c41c181041c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 983636843 1250 983635593 983635613
    0x30d0f020901020d110102070b0f0709051009230402070308091c09030f081902070806160e30030409050f04150c1b03020c03060f090d0804150513 64
    0x5119440c030411000740a42e0700052409005041424640c9900b0b5860403c40d00a01a44201030b00d042e000700200100b040e0800c0301648106041d8542c1c521254132030301800b009591103161000803400c0400240070840380c210018415005c9801070000c104050004641aa0484901240818064001c0c092100c9041c0040303000c00c8021000742c51b00300140c41c0300800951917440091b14104c10030002e4000e100030481195214400c291080400700004903000b503883c2c10310b1140760150300480000c13860f041050b46240344070710f0303055030380105d444207100070840054540c207072141c14003101d40c1d08610001d0901021080e05030040b009562283d2800b0010410b83c0c01c018400c840e0b002207081007000140604600c40300f05800c0210000f03885105000aa503003141c203810011445e841504600205980002c8a1040d144280d040d1106500c40d2121003d100c901510800383e183c0142428444041c4501c0c840c0d5803090046076a01051620040e001c81180c40030394103495540c00031000d10083c001c481c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 983638093 1250 983636843 983636861
    0x111002120406290d141e100212160923030c0a06200c180103060e01060305120a020304050a0803070c06050f09151905030702010e0a0b070e0d050708030d 67
    0x4641d4101204219009a00d00301d026041d031203901540f00450a00c400c01c5c901161900c440b20031208000a580300c0341c0f0403490b104e4824001440341c090714080e0010140251000c1c001b2070360b2010215102c40e85040b90145681404108001480000044626059440d80303951000c0308100c1c3d0110a07104180350030304041e4100704c1c2c000c0d0002d800400080da0b1150314600006003000004c2c2585418454a9040050002002e6440042c0c2e00c01780d2440c01c1e245000c0d5040301d110340320030802c207806003002600703071030540c070001d0075542043c8040001220010010441203031309105036854252203a002418019440d0404115070380049411000c100f10f800c0244050005414040d0401c134408000c04000d200c1ca180301c5002c1c0d0001400c0714440d01844060340c00c040490a8810310860b9415001801a0400c980f04001507081c040c0c103001c1c0380400301d01c8449054012848210503030719500103440d02c001c2c01c034001382c118814000300c40210320f080c010b902c003a250a001442d5030b007203400c0548080e518280 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 983639343 1250 983638093 983638121
    0x2306041103100b070515240418030809120d0f0b0a12060f02070506130b1305030301090b060f070f051204051c02031221010608090607111002120406 65
    0x82c0040d4020905070300040310000402560f840c081071a02900f06006a070311740306045400710910000300341028004824828030184030486020340402c00042d504011024a0245480c2c0158030101c1c0c0705a0800e540440400216400b040c504c0418281e95488031805040040e515410458103e40758003a140c000035046420f00c071846c0c14000a60010341c600400207002c555503580c40e0f000e20340a03070160b40740f0030340120a848080ca0642c0c18182e40364a14942164081760746000075001480c9400c060751f044e034000c0001e500310b13803d02c10b4440c001c008418540703a01c207005000858882031180000c0181c0c6101d0840201c28410302d00c1c2c00b43c9000009048a940400c0c00e00c0148207980354413021034600c11100300c0505803501c1a001207810002000b0f40951040000114030322207070025400018081c00c1084c00c0c807641c1ea031340d880844402105a54050082d002030380440c42191007900d400c062007084406541880d4441c032050301c01c0b40d1001e00c0304200030f1401d10400c002e0100c588a0301081403015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 983640593 1250 983639343 983639347
    0x1203040203160b2b050c09120102160b1f0f030c09110d180629030f0309011d030615010e0a080d032a02010e1605090408090423060411 59
    0x100007040064055041c1500011030049400c110a034401015000990b22484e800c00c110b0030032100c030300900e80c440400207010b40b015854441204405108443d0a40b504840a8918201907501c800400401a110881c44409540f040f01c2c0041c1451115009180c070800f0420303214554601009800d080342d100650301881c02c2c25502824540c5022070724000d618403400500701129404140c1440c05403040601b0740303071400b884d80e01e0130314000440e800580a80d10f1954044075040041595516080406681940007400a4945940a010b049602d10002c040c85014280800d000c0f07480c00da411203a941c0042d00081c00b030161541c011140010380c440503100c5504407401c0100113599400480914810143d0b2104114203c581c003003940d548400b90340484c05400740c0140c000034003a080d50081c4101d9405044007115400d22a01424000c4800c0a07142c88035a40e1140c480703e03a00d42061080c0b13900a501d502440e6003002c0031820807080d0350071201e400426030134141305000842c1c80304005062203100c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 983641843 1250 983640593 983640599
    0x905010e040308180a2a030f0b0403210204051206044b110d05300c07031202010204060801090b0d080c0615060f0d0506040e120304020316 61
    0x304540ca03803080c2c040c101a8001c1d00c5000c2e094582c040307a4242c103100ca01401089070200031608022148003800d03514825507903440e10805e85100065480001d00c0e500c0b44003800c0000900001034035612a000341064160941507070484882c0088600741034803d83c0c8c5c001030520061810070080540078001c6401010a0316081e9220746890051a28151011116107511585032012504000035042480010b1480d0710000d5200c84070072000140864016214081c0c00c0f000d8100302e07030045036694114000301a59040300e107003056803400485801d240d0000310f584841d01844640000c08110040e40e0041c4000c51450814403440241016100308590042200300b1103aa40001c0c01411340315100e0b000614241d901000a4403160440801494200d007c03503858042c43d4081070040c40790701075404c0005d040010800700103640c450740440c410030081c00d0042c00740c07002d4144e100c3d80c0c2c09180500300007041c1d0929500f80f480c01035081d070034002181000003007004504090080502100d894a540051141 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 983643093 1250 983641843 983641859
    0x20f09130627150b06120405010f051504051b04030303060306111c0905031620010e031015050901030c091109150901090305161e06170703141003110121020c030c03040608090601090501 81
    0x5000303400140b00307074ec0782c070017203440e075001c499000115868403c0c10b2551641c1d0382c6030240107800b00d80300654481d85842c0350b841000708030304111000b11300015207180040d020106688002e080e48c0b403060700e55100c18010018058050850345c5001070145440b94850040c0c0c04900f10011107100c800b90410655400d010a1902c000400c030880c4440c640300416400484001001403d24031781c0b0181d40301003400000024017815032004e0040e103010b0322080c4440010400c0340b0a19205043d46a0340004042007107804128050001d061a42014174000420070f070390703403101450108503600008000d1030100040180c0c2c1c00c60500107040c1d01e2540c0321002140e2801c0e1003d083c244181005070b008060070383c005518103120303900c4420b9101c40c0d403205000398200700c100c00c6c03541001408115442d8078862209500c41d0700900f081c08901b1030b44441001941c00c4016860003135002446142c03424402070081807070f01c0c01c06001600c080e185640e1502014641700041500c1c004042e400340311041e14010060280e84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 983644343 1250 983643093 983643121
    0x6010c02060412021c06021b03070b0411120d0906180b0d0e0a0b070c0308060d0c090b0102070b0d0906050612030a0804020f09130627150b06120405010f05 68
    0x80d00440b00300403e41a00c1c00450400890841c080240c86103400c2900f0400c00783d6809814050b003005044100644000c000a540e44600000a00487e41d18000070300052041e641c00d06400c80090032290069071426070861a0480b28014100840d4400c0c1c014441c1d40d600040f0141950040c0da2286c2c520313450089038000610a4000f034074140c540b605400c1410000401409500903402090b0389424600a80c000b841c040d66601c08500040008011818502e0b2952014000b582c0004a125255207400303262001444000e2440c0d056000748500000c507075860310b018041c043c0807840b001c22500081d02e4110300312180101120b01c0342155640143c4044030000a84003040518102040d0503191400040c05445a80c030185900400c0c0d0010848880c50b803030040d143c524031403a003e100f14000f46001030320030301500c180003070480c001750b1900c80030580309103041410f410350800001d000c80c6102c001c0b420540c04200c0507200c0c1140c6405000070014244074505495000d00f00c00c10050a1107070704480380d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 983645593 1250 983644343 983644349
    0x3040c050303031e0a020406120c0912110109090212270f100606020a0309030f080403140c0310020309150406061a0a26281a0a05030a0803060d0302010213060507050606010c020604 79
    0x415940d41171030080c05d000d0391140002d442d161074807003849240c500e45437012144011025002504c42c4400003208007035802039520155003090403180b21f55030341070500607081e46000d1100c5080719240320a20714002c01d21407588443d02d440013818000c1894408001914000d41c0940c0c115805144c0741c030042503101a200055075031001040c03186800702d0410080782d00032031304003421000300c61240948280c400030308404840000d44c01e0b00c00031482403171914101d010855a6514a40000e12454500843c88030410ba02502c100000108140c4503c14840700480858020840c64400241101090341000c200c85610384a0361910200c810b140071000b0f0310f8000585102c1100d00b0f940900c0707400007100040401e094000c000300704076114240b44030540d081400000c1b28040c10002c0390124803428046540381025820540007440d41e10f9080a10000600710700095045550030701c4800e80c00112040342d00010041540d4040d1112806e05116040000c0034001c5070521201c03a020200507220300d801d0380c0407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 983646843 1250 983645593 983645627
    0x2301030b09030c030f030406290402090d05070905071106010f0509130b04260403020303251a070f210f090602070812060d0f0803040c050303031e0a020406 68
    0x519220200740c60318501804a0f0000980000305080764410708440285200724003c1070240440c4100b03100ca034038038502601180d5942102c0d070b92004100d0501d50001d003a494005406000810403035100d0508100c09134000311000d9031510140441d0f04d901101c0d50110030340100140c00e4651411001030410707481e80c801c0c03900400c01200050428507100e0381f00c0c8000d5401210895882c0b400d8038255000c402541d8580c401c000d852005c00c2c41402a6106a409403640074005514080e40411080c4002d0300290b09040080c100301d00b41c60004a940151503000e07012225588900e0901120262005a0751072040d02003103194449443da940c51400300609500f44c24900150003040002210064801104080c0845000007081c1c003c02a0742c00003808502180700003041507884d214100140c12500103809490020b19452081c040394850300250707000f9210350006240181d236440468115001124400001512042c4000c202c000c070340c40060b07000b5041107046150508000c0042c04240e000500c20f00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 983648093 1250 983646843 983646863
    0xa23030a140f0a03060f1a0306090c1c0501180515150408190204060806061008060402040e01060206040201030b0907020717010608030f0c0d050304020a0b031509070306060201230103 80
    0x30241101c00c0c00ca50b40181d10042c6681d0300d45020301c0184c041c200a01ca410302d02e1031002000607000401e06c8220002c1503c440c00e8a00d180c5500041040980d000f91900051040410901e05504a010440170f8580781d002d002042e15850710845203520500c0e2290501164103110411103901a540691245004101c90b40da4909015039491038550080b60021502441404401007280048600b0b4516640c400c8030305001c2c60b51144081611b840302038030500e40008141001c019400d016030701941d80004007800040c00d1136940d040380c8882c0d42d0280d00030b102680040c002d108c01e55a04d80103c85a001061342d9140007800c08903402507881c00184209810700c0395078640e40f00c0070042900805c0c0140404001c9a40f01c440d4071000c3d441c6a031106042d00c403544500302e000c40c5003d0089090301d00c5950000c00c0328509078601256240c003a400107029aa10501880f425042a6101c400e543d001d00c0859400281003400c00360003900311900c41e0042c0070107200101e01a80c04100003001241542d6004203111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 983649343 1250 983648093 983648117
    0x9040c0302240408150a090317040f0c03060501051e030304061110110c0601061d040903110d1d0603040b181203010308130b0c250302120a23030a 64
    0x181e560920150806091001800083d940000030307200c1348803582c1c1c3d80e041c50552250324806d4115585d03000001c0105c0c1002d0034a0080c0407407c642070b6401070003601030814041039075450b40006041d50b007048841c81d540f000180b140d4180762100d0295020484010012180c42200003550790245125000400907986041090200b06200d11918008101d405008003280e020341d2044c95000043c01e0f013098800d00d000011020300c54400396120030300c007100e160501d1041d0030a00028221075403045c1c040c440c0c0c640902d203d0080800a823079001c001ca0780d420320846400b4020300030f107110140d0f4461060900340288004181210015900f0114000c0d412a409107000042c40c01c0551403a0b40318003150300800000240310b0024024034500141c0811000c600742c441c010401a80100c440146041e0322030310130141303c60107513540f481401410b00711034100c0540d03903030000d0302542100c03100c40c13800d801900d400c500300303c480d02214100150900e849589058890030459503809072004170008c000d01d07030101c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 983650593 1250 983649343 983649379
    0x5070905041401090b09070f3015051518120a051c03110304060c02031b0c1008130b0c190f08010503070b181c0b011409040c0302 57
    0x2900050a001d030050081001a10800003038000904c0b40c20445400c0c1228041c4500c0d01c06c000910171695502d03040c500302c418403003c071030b04940760f05200e1844071184045441c4203503100d80700c0600c40c0c5030340380456503500003880040079464644c4924000c40b4042c00312580034404c0e070190307211105946000d80300c880c10b0800080130551500c025a0303c5008107a5554103026010031415400d081d820700c000d4081c881900c3c11070443d0400001c0e110000c5051012800164581c0c00ca410480350506c1100e040c84038052103030341101164040b04085600c085201c4005082a0140300581d44190500ca46280791002c1c0d8000e40c0020300a0003070980e564a07001520100800e401c3e42c00f4400301500d24007400c1c544190203400c4290951100d0003141b141310002405180000388101030301e124546250502c0349415426005107118960594014060910650804c1903131901d10515030150000380010b5140060f006414031128145038052010301003007101261800303215000716907058a50000a5400700d02c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 983651843 1250 983650593 983650607
    0x1b080c2506020d0309110d12231602210a050f0d02031e043b0903090f0414042f03031902010b0901090605040f1404140307050106240f020a060507 64
    0x1011f5000140c081c0900510140100759008441d1580302d8140104d4500e482920503044030b0483d681500007040140c0581d40c1c004c07401d12000b4406410081000c5a50300c9409208480e0413002c861548a4041442440810880010114000c2010303240311646080020740700d00c80c5002003044030210702c1e50251180200000c5034020004820042605004030440c900c401c2c0c0c0d0140011142021380803000500045964903034083c00412005510700030341c41c0184081204007016250b030290341c03540204210300c66031190300e2145101d1032610901d4030aa4102c102c0000400d0080c0d805240310070390200c3e07192000812541c0300704070003124401c21916010100d000d0b00143d0b00d00e941010140000044000030f681140d41030b214112003e01c00e510f000d00c04101254259102e80c200003d8140c0840c0102e103043d515004c1601c4000103980c60043e403038440609441c01079008005001145251002158070048560701b070206038507006a540820745030003036490140f0360014203050b50718030125444a0007511 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 983653093 1250 983651843 983651873
    0x3071202030708010303171303031508190c120b0106050d1d011e0b060322021e03120408100519060306020c0706031b1b080c2506020d0309 61
    0x2000359501d2506120040440c1d03400c2c071084022401441101e1480c5444540d907a126909080c4110f0f0304d01d801d45c90403000b801d60080c4010350000c0064000c41c0350102800503c1040c2110320b840581c1d82241e28046400304190341c4810311080c00510350900013800b12002a04442144c40c0c0b1940707544404485000500000500f110308030f1128160b60302490041d0460804152080151007200c107018000d1810354410300003050b4040f20810000e64001c0b0707140d6a098000103d911000e480701311aa010808841a003440b0300d4501e50f40c5045012503203410490b59a61180030801d190405203480c4a00e0b503908840c02ca426069a102c1e4006200340002034990588402e0000051101c1da0340c0381810760007540400e400c640306001d180804940b05d8040e000c2d400c090035400751202c1d00981111001c4408280904100c24842d0241000b0000300e01a40050118000c400b0b0241065405540c420140042c0210548255030150b01041040c00d4000c00c0158a035200d900340803c803400540340010081ca4248 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 983654343 1250 983653093 983653127
    0xc03160c080f1e01020f0a0f1223182508030403080d05010b2701032a090e100302090405160314010509010905030d0b1c080a180f06050f0d060305031903020c0a080307 73
    0x100c080b41c003940e07050300e0002d840300864003552001d494104040c40e0b10bc005824040c05540b14640e040841012245048011004d00c129041000c5c0c45610b581e0075903205a20a50b080c5030046984040c00081c1d1090500400001d41260f282444a040340c60224200c0079001303801002035002549141d0082d001030b0808100c480901020408601c0c1320042820309600c800005402001701055040c141c2180e2405a60000072850303003a4550b034200028070a00500494850290b1411a21740c0c00070788148101442c40f415103000e105005d20100c0d8210394000b49516043d80c1070004050200303802204403480c6009070000440c04400940220b264000030905000c07a4007041c00d00101030205100180001000d035079640e886a03820400c1e0f46001c404140591142c00703051503410807405029000030001e0a41c110a81420142207141d01d400700d0307485d40c1c0700342e90035040000c000000e8000741d2a4003084d190b8038242141011103802402d0394424070100001d20980c07001021800329809403042c0340450000c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 983655593 1250 983654343 983654351
    0x60603072d0803031905060d022b08181915031d160602030307120b0409120f020c04090b01030f0305070f0c030b010b0c03160c080f1e01020f0a0f12 65
    0x1902c0055565402150a40403122281c810141c2e049064003400c1d01070007004010605003000364007008084c2001d402d085c1001101c0014a000070019a0041c448850295a60580f00d01345400d5101c408001d031542e5a02c940589920327401280d180700300120585202401c404204c1c18868000d40062880c0d05810000240d13500040307008840014041292485681808081582e2071a05a98902060796144085103100700f43d0f0241284070382c0703c3c1400610042c000300c1d808203151645c040811701000d034000040c1410725200c141c16010842070200341070a42e010049a0071944891000000c1800b005040480000d050b00c103052080d000c1d214400e8028402100c030a0384c80c038150200d491184011181600d5010001510710141d105480e009012030001c2c614158400145008806110b001251803481081c0041103552003088904900811b800081c442c00400d14008014007580212402da6680104903000b1150072040690f40700ca00d0b1401c005030f2440d21aa41900c6a4200c0344807042c0031460 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 983656843 1250 983655593 983655599
    0x2a110604030809100e01140309070e090105070e0f0d060905030706050f01080c01030207080714071a0a02070f0b04031203270204050f04110d170c0f0d02060603072d 72
    0x40c0b01c010b00440b84200c2d0b04580024030100c0685280555100080c0407403a0f0304643c054a18a16008540c00101c078003e07200d01545036100c05160840542d56400f07182e5407002042140b44c3c0142241c0ca604104880079520321040c40d002440c03603202c078980100045d40b1608142d0400c0800c00545041c99072200d810700ca98a407203040450b800c02c0912606c00d0501c62080c40c2c0c10254020704c00c4415968000b02000e186c0341180c2c6410259078042030700d040380c501c0340c1000069450148001041c028003500c851030b0f562190800000e1604501c0d80250403904141c00d0100090060300e4202c80031a0b5101e80c83c1e8004100c0d0788003c1d0000d046d031503009004040240782c000380321341c00c40400c6520b080c404c5604101680318115030506400382280d0051003250f02c1c02030100d26103440c0291051442c130500c0108480b001070b401303060507500300364484591075001504200d54000184482c0d00500c006200410252401d1800a90740f1640781c803c45011205c03a20140c141e03404010502c038002c4400107040914166 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 983658093 1250 983656843 983656853
    0x1e090611031f0b0a090b0a020a051c030606021609050603070902161e0203070b0c160909051504031b0215120604200301092408030304020405072a11060403 68
    0x70490454010307070001c0c0e002c0419030100c0c2e0340a41d515448181d44011169050000b4140d0b0342d400742d00440290b00c03415580e500001d0f001c000001040760300558401505041820140581e01c082d041001590428062145408410f003511021034919000124180c1c9a5601190800090303030421750106000040d01030310809102d8403180020311448603e60324801d5400030009462050390020740c1764114080c200400381003032014054100e0701d00d00707482c445054407012004410307071580f2180d81251110380744021300a00344240c42c070040000601e40f4061800f55130003044c0d480600e6241c20301144a00c100015905c40e10400000321005e00340c0c8913558800940e411100c50030844240e48140c3c10500c0514201d080701181c200c00c1150315082c01d041d45d0030320729001c01803c000c0c407007524018022590695200300b29a01440102851405182e1328182030041c0825500002d00380c4051010648207044000c5a0900e019640041d1802c045503643d0903180110540c040110003d03400030b0003003008010700c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 983659343 1250 983658093 983658121
    0x20c0603070c120f0e0a150f02070906181103040f170409090b0609070302041203031a0301060f08010c021915090b150f041a060c1005070309030e01031e09061103 71
    0x14504d07032540f2400442000400484243c68096641d00305c404404444c0c85d00c0c000c0c2001e44082950340190b90b06c41d6100d107100000c45041e075116400250a030780454012220034801c00f40205040c100091440c54551151400c0c800c040600400d60811503004180506120041e140a800e111405000500d244c0c2407030700d00084180c811500c00c841141c0400ca4040c040e2084404a03098040405100c014a840036001031004000122070301d00c000c480b924407607800b03100e251b01030081c82000140d4103041c13202450846104400c41019503000003102160b0301c2000494030044c2c0d03400040700d92407103020300c40340020b404809402401c04048005004284004a500a160309021748120503444284410401610448410000f0780f0009602d03005407824544001c00d0307031000000c02c80724912441003c600c11107a00311804000244d480e401c04040550002d0003421042d401d107030600100131060210403203a0280b24411302d41607507400302c0b0810082d680e00300074445401541e03803d889103041e83c00307200c7e86 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 983660593 1250 983659343 983659367
    0x30801050d08120a022503090614041509030b011205030d181b060f1805010c14030c070311041407050307030e06011410050c030304020618030613020f10020c0603070c12 74
    0x16603032140151200200981b500b4400c150140e860820032032800c0010f4421804422041740d49401c10400442e250211115400401e90710742d86403100c05195051021080c841030300324611400c0c8418140e0041100081601e101c010400400915182031442c065041100020000c140b4a01e5500765552610210f24400c01c80304140ca9250820320441c00899240038080040745003410981d00500c00b81d44507004106156100740d500c0940600d401e61100d140d0f030170074000030903a5480400e0500c1081030300e078180740750000290f4040c40340f6007140e110a408050010511b02c20400048001070f80240f00c0d4000315240306181054030700558650b14056003601c00003da841c061007001d02425200f41c400d504503405005020081c40c11511160f0070425541d02c0865107826140c240348042c00241d4060001d94010030070902c01c0450051544140180645003400442c400c00b075844041c1403990300400c00488170517007201c0c40c6590359240070042d0b890500030400070300300c20240c2070300342d0301e6070b801c60b650001c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 983661843 1250 983660593 983660617
    0x411121c1b050c01020c030d1d01020304080a240c02101104050d0b151f0e130c020f0106051909090206070b0106020a06050a181202010f022205040603030801050d08120a02 75
    0x210545010506a2350b4518802d82d100081c108040f0613078549500c9a02810140148150703403400382da0b084810b01d00090460306031003800340780140c05904400300303010050440e1410760034040660000000307500c80f081e013409030801d280c945403840750b003010240450b0003400000380701099502503400c0c0107915410031148880400c800c42c01c4503e5030700e003c15030b22241100c0d58a03101040e4005a40031078109050100541e00a001f06030003201a840902807050001aa42d0052044c800540780d1142500c0e02c50f4440d90050000c04000900c0072805401001503400210001c11046680d1010070783c18481c0b80c0c0c000d4140c0000900209450340d001c20034203c041d00900f018403c54a40d4081c0c4011035028101055014841001960011300500f000700c020303c00c140000200389440001c440305903403010f8800000081e031040c0a400416030381c28004080e22056034101f09241c2160740103059a00b060003600d1248907040b40003000c21504008403219122259640c00325030510484500c0030350054088808 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 983663093 1250 983661843 983661853
    0x70305010612020f09090c1c08030f04210e06070f050111120c0315010c021305100504150f03020f150d06180c020a1220060411121c1b050c0102 63
    0x2001e20748181030a00036039103900a44501c7c00d440e8104646010248925416940060000008a41c0000241d8814101034020f10340c641303007500e020400001c1500a64094845c405160503c40741d00000488180e441945c030b03140d0700c0b9041d00b000505540400f0b0700800960800d00c139120200301f05c002601c440e811228076030300303507848403500782c185400102c50707007141c15403488850401588640f0405215074000342040111f42c201903a01000d88804076114441d1032000c12040116003818810480c084000345100d49805007007102600014406210292180701110b164032010350700d4008407000c0d0144a0403240c3c0c0c40c0180e0f81204051302c00c0d8441d5640e1465a1740e56034102c02c0c01400f82980748041a4054003079a0b10640d200078865410a11030410400035950300c0400c1c1110140100c10100a4002042c01d490700d49410079522030702c0944240104807103d80f0fa40601400510403401055500c0c0d1210941041c0100701c810343d0500440da080242042040800c0c004c000c03600100700c01e000e9003996 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 983664343 1250 983663093 983663119
    0x324010501050708030a090c0e0a0614030705090f3403061505071b080d1d030a05120f0f041d0601030b060711061902030a030c1403041407030501061202 67
    0x1690381e00030f041018004807000c000161510b56a0b45c0801c2e21f5502c60041d0744404d0385c46031450765601204440e1003001c00d070340c0c090070700030790400c0714641866000131402030121900707101c04274441c144044c0074885898002004240d03420443c1c0002c0c55040340d06000000b5284010382207aa040b100e84940c0c402203480e010010075000056240f41c44e00c0501c03510b80c1e9240010325681c1e204003100c0041e021503030005040021545850a10103808650700903034900e0040b46c0c020f80210400c2d03020b00043c0e4440e03403180d480c120002b180030801a14004c0300900a54884801c0101a191480740ca101b12442040002e00442c946100d604003204043c1003071810441e03039032600300540c200d800700ba009030b42c040c00501041c0009113858003d400c81800160146040c1020303801d0301540700700c6a8054001681022070120001c9905120380111042d09141484042103404424005444050400ba00110b9080040401801c0800400c401541d1280c001c200e1255210502c00038040300c10030892150f40c04e8600c2d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 983665593 1250 983664343 983664347
    0x90102040b182206090e0706020601061206080a12080906070e060a09030c0303030e060f130b060415090501060e01021b100c060e01091721060307050324010501 70
    0x5202074485800e5160700d00050050540340c00080c2c1d08855502145840d440e80210100b0214002030f8044440042150381c00d041d0a0003c0d50441c1c0100401da5200e62401c1140a40c000384060449610b814503210000140f95010041c2030240c00480f8076216042c0d042080103092880301b50390f45c0701550341c0b83c1c254031442103084c0c460006950300400074400c02040503031440c1203401001240e605003450898a13a5940d140340106030664000d4010a0341ca9001d028075035014440daa6003d2603101c049805440c0078002034006000d08040031705259050400249c40c0e072503e0f80610a5585410f220300074881c1c1e42e9101d031024200034025140050f141c042426115400041c9101e150040024004030140c0c2c005d042c4030303400258400800401402d42030550110b1041c0c418980c0300c000200c000316000207035044c8072040400c424480310012a0801203885054080c40e040980c5400700748505d201a140d1100091070041503410095150150142c1b66550b16400b0040f0210101a8240c0c4c00040c2e80c2e407401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 983666843 1250 983665593 983665597
    0xe06060418030e1908120d060b04060921021c0203011b051c140c0d110a0503040b04061d030405090906060105030c090307030c0e100e010503101a0301150e090102 71
    0x100400e080b441c40141c981342280d07a0500190340407034001c404a6844610910349000440c82c5212200c4c0050185032054090240340090070f841032090b032a240c50b144000300300c9001442002030040e19070f8003101199200e012612100c0350010080304d10000a507003016404151450200d00c29071038041700070011300203040203560030308080d02c400341444846c003441c1d204101c00c40050b1860b03030fa031500024049113040d2032440c09800c81720b01482c1c440600c4003811040b12000008030203904401d0001000a81c0d2000840342d105070302c00020142c0303440d140341a401602e00c01c030000c0c02d03705d0812000407884031f001008c1c001325281100c420b24551205400207440d0101610720b5070010303004000107172488030308100600c07400382c0250480e2000750307482e03c2c7c15268007005d4004520300c00c40c6100303000a031b4030f050318200041c1c140320348040519450800083c1e6120020146040015111440c055010105091140943c10082c000b80f00c090a20b40786480314070440d0141409418404001c0b03a608107051013 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 983668093 1250 983666843 983666891
    0x1203224218020111030c07270516050a170112060f050402060f070f020a090e010e011e0b030a0b042409030207141309081e191803060e060604 62
    0x92101c095841c0c98004480c840c54400000040340f10401000440200400010004060b4000c400107100051113004c0c40c13499070728203221041820603092013405540030311180c00058a50030545e40c1c41e0141a0b055a00304003286140170911881000092484442c020350000b05d84640300c04c000c04200d06440004503017050b10041d411003003e000072891240072000505640e800f40d80034443d08401940000d050f02c850303411203400d10b501c6802c2d00e0b00c80c200034007881c3c14100405c2c1c000c1c801d41060b4528030540d400c24a28807005141c0364002c5140c82e40b418881e043e400c3c0d13000b0b044c0314010719060400f081c510108100f010b01049240d915060082403034401d15008560540c05840c1e00c03854429012030111070382c0700c0280e102000449006d41c00400d8425058813030b00c078000d031507241c400c00c40848203c0d0a0040041548140800815070304400c604007030403010280e410007202160b8032100c00c0d81485200c1e00014180c07850040c101000da1000034020748160001c5805212900d51280c0202042140711 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 983669343 1250 983668093 983668121
    0x15010e100509040b07200d120e0c0f090a0b0402040306200a05030109020901051c050405070501114c0b010309020609040903020316030c0512032242 65
    0x200100700e0041c0306030a000640d5015043e218801004003900c5801c0130001c11102004c900c61000c08c1090b80054011640c0c41d21004001e0882400c1002c0032441901d00c58026502c2480f140d0300240411255038030400780520007030421503c079a160714009004000501456a00710303c81406545d501401200301c038119145541c44504591031b00c0c4014020750030082040f81842028070481c04002c0700040150700741603014001166505050030704608090392500b040d8100820324100c62412000010100030b1682450006017001c06c90361b0300c0164002084081c0c0501000305844a4400700c61214000c24000404000308015800040158201c84c11004002e400920501c00814246003d43c0a640d0341400f07401580e18001c081c001541c1c00c088900e004601040d01d6010b1070b42440010030017078040e001501d03285450741c142454000100c1400ca41ca404140000c0d600c0703e000c019851000031030341249090500c1d503242da500c60002e040b5154414221550080003101c100301d01090003034210380c0d02c0784 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 983670593 1250 983669343 983669363
    0x2202281217041212030b04050406020310240c0618030f090905041502130e0c0c0106050409020a1203020a02060708030712090308060d030e0a0e010e090c0a150215010e10050904 77
    0x15644101d40f05101911301414180c0d1205541001c0e1158040c0303502c124414003005990303240541030f24600d0402904568000749121707440000500a4002801440e000c0e07003003e08690401e4075001c80030300400c28400104650020303520041540021411130440001d03101e071031203140c88955a208442007250050002c11403512207201d8884154000e010250490b440c15075016103852040215403c10b0351800c130003150011f4110340b00b5100b803185602500c82110705112504a680009054515a000d200710740c0c807101d514041010300070040b110f42c1079400f03440a42c492006003820b8089404c102e40c500007040801d1f00e0010048030900c910315200d07905485465840d200c000600405000401d000c40034000710030b40c100401e1b69444a0180204000700d007420003503041c4a10803411002c05007070044243d210151704d4241d0f030388200c11070064415903100f00300d125800d207004920705074003911603100c260030300750010036101e080024041c410321103410350b0303180c1d241d80c1d80602902850459000c0c0900c0c8032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 983671843 1250 983670593 983670629
    0x11b020f0a02042304080a020106080c0604050910150e010806010f2a020a1211150a05090d120305060306010621180c060305010608220228121704 64
    0x700b6440103104215030380d02040e00701302501407408521425101503811410105445410690901892014103000c070013a01c040e0030380202007070060040b4001c0610a600c8640040c412100101442000340380c400d061504141c1c200340043c0c58890102080ea0006540b000080d10b10b502600702c144506040b5a20114a4104110326500d2503841d0a012000781da200543c11000d6582c14803800c1c040e003c5038558848103051494250142620703034290a004418441c02e0050440c02c0740306403402c81070310703080c110350b41d40492000801d8600315100040140b02031088070001194513500c224400c03071040c1c044805590300c50030140e41030314000800d0f4075207520940b042000038002e90407012840c1440040c0c291450015903035110300c0480c0ea00b112000139a2140108201030380804010740041524041c0c001000d1720454a03610091080c4000c4c1c0204149400d0495403d2040540890b11b00c1665002140d5903c41c5040f0900d203520080641e403d03e03410f00600206182203007250100c0340b40c0030311030014900d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 983673093 1250 983671843 983671849
    0x1b161a010509092a10090e1003020a090b06120405010507110c0609040e1c050d0b010e13050402190603090b060405070f180f1401020f01060f09091b08011b020f0a02 72
    0x400c80308032904d1901c040003103c070740f96110011700c41c24054441d0368503076061a030383d0780059100412000299a284000b000540c98900000381a290440c40208040320741d800801e019210703449040000383e40d0002003006100c3c041d4401401869180d4800e549890058421962021004403e550008080110700801d1416034010b2841c0c070f45060584400d25110100011045c01a2041c03401140380040c603902c2c6080309108080004a0034204120702090420128041c64190394a00c44000e586501140543d40e4a0404850f0300a011603e0f20b491611880024041c00d409241181c0e4002c03084007040b824940303030180c2d9200d04440e684240351613909500c100c0f01c60580200c7c2c625000306180d002328030f910b202008c48000e00380390003010310304248074800203250a0417aa01d61031541d00d040000d01860034518907080890352442004188a500c0d41000605035512492041c071203406414000355884045d001174410440c100451079a58503180342c160388400d07001c00c100030a900480c0c8108018a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 983674343 1250 983673093 983673133
    0x30c0109063203040c080d050301080d0f02010e070b0a021b090c1b0304030b060907050307080a051b07150e1f0911030d02070e16081b161a01050909 65
    0x500c588000c81011900c04440b410303402038805a550718103007502400210000c01c1404500e06891600c6450756150110072510340036042944070030024020b00b8000034074801d41120342c00c03108110a64404980d28550780b5440da001e07240e02c0e00580901000e64030f01c00513200008550a1018040c004603545001c40000150301c42c1843d0034100b1401404000306000c00c0001d0006544124a40c90407410210100100400024808810400100b0401601640c400070309a00240f040c00701007060380f2001d4a5580a84003e036000201030000302c0d4080c1808641842003180d100099410045200c0186038103071a0b101c0341603841d0b01008040c0022143c800c035548060401805107400c0300c00c410200d80041e0900c00303001030187c010f90014400b0302c03940181c05546a00000c2b10300c050900070b030743c81d00040e1601000421542180c01c006060140901101d400c4030108a8220a2020500e1591600c80e44000c0034842d5140000500000070500741003590086001e080048000c000501184070f00c82d40758 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 983675593 1250 983674343 983674397
    0x510050f030f040b01050d050a020108070e0d03090509060406031703040c0306020a0503092817070618030e030c06180a0504060603020a03150b1e04081209030c010906 73
    0x2150821414500d00819406035004298800d108011400d1509069070a540180c0165108002c441903060000341c00141e82454241d080c20100c8403075880d030340d00f0f9401004015600d500f0501c00c1c6819010194406070f800300380c0c0c4045501d40095241e0a050100310b44640c00020300240014010340580c01d800700c0a10760140c45007016818080d10f80d500c402c1a43c0044003030001099021084c411201c10502078803801403007101c102c00860704001004803031802091006040280c1080a01600c20402000c40d03041540102007880910780c10080c84c0781c141840b060035000103c100c0903078002d52802088000c0d226400a2407542801c101c1c4422040c040c411030603c55022002d5400029a0f403114080d6034002d100c0b40d1001629141d8a24000c2c013070314291390000d01101c880715424019880c40e072060b185e48299070800b0829644c20700c9030b00c460512490700210085d109036202e0a41d8540a54007d0060312020742c15580056a0310300155450f4080380921000701c0c40d124152070a09412180309541 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 983676843 1250 983675593 983675597
    0x903070318050d20061c0b01030e03180d0204052502010615030c030f091b0902090907030914061501120506030a0311010b13050109060501020a050c21030310030605010f08070510 78
    0x607100700340010010381c4080074013602036a8850105051ba107440c400c030b216404085c01d06100700c60414948a03103a00c80c00b50803202c414051a0485030030b4540901c00c403c5140e0142080081d801c202c40c0603001043d400c441c44900d00142c0501300a124810300900d01100c0783c1c2d000d00c00040d1a042000d8001d03242c050403623010540d07900c0c07079000700c41032034010242c4042c0901595850110050740188140e078850300702005017401008004100d032640c011969004e041482c2c0015645c03014507116207044074690a0380002c0c81001e0510440b004540c018103140502600c8500c2d0511700039001c141561301c102d81e116410f4203c0306140011a014400080110b0b050304000900607134194005401c804043e0711240c401551400140042d411512403c40500003d0008010a400c0340d955269140c00d00705a0398002c41ca02e54481c8148440d107800d000a040300c41043c2ea0306da20705141c0b1944034000b6031106446044c1840000210300401014045c1620180c0b400380044c541880c0500c00000711600340d07401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 983678093 1250 983676843 983676893
    0x50301090c1b1a070e030606040203060f0a080601080105070c030804020d0510020a05040504110f0307050c0a0c0305010509070e0903041a0903030301030f060c08100e07030f050903070318050d 84
    0x4202c9900c1d0704100c0300103200f0280003c10242c407046019107490010502e00500c80702c0089000c0356034000138401e43c050411140540d80e503035468040b4000102d281025600b05221180c00b0642100108556050f10b2441e0002c00980d030f81c00c03100b161900081078024010940b088017160141c10300039483d14a0341d00400440c2c0b01901c0c01c0c40030b50100c0e408541c5080001e0701c041400e0109181c44c1c0558004440300e984554241208541032107200d11001c0d110900703000d000107600080c400c2c103020f440c00841e0081490a4400e0341c0e030a1003800f800049855030b52501401c50045041542101900d000d41c40355002142007509003000c42d10003058800308800b122609020000440d41c0810003940614402c14040319060800d01e0207400341c0c0c81c2e00f2001018014508100140c900c17840c400402204c5030100340f402d5607200e040090340104650510031071090b04280400020410000003003c105101741d0b2180000f43c1141100e0ba45c0c040c031806080d034418180380c011400300c5c0d422042d041c1d0f103140d0812541 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 983679343 1250 983678093 983678117
    0x1e190f030e010e1c03080a060f0b030912071109060a060f031e050103030f110309011202091909051b0301030503030a090318030b0a1118120109020910030c0501050a050301090c 77
    0x18644c0004205030265080ca0411110304040d880a001c81d04091107041c140089801c00c904041113100034040c80c00b02142c080000b540c0303803030304010389424000081412a56a00c507402d10301249140d941c0d40c60300031040310300131407007500b4010381420460f1010303a20440c4007030361080d00b10081c1800c001d5001641400e810050b1310801c480c4261402107100380c8528420b16040d480260079020a0721050500fa081841040035a0f60004036108a0480003500141c2d00d2002e480015001c01402d10403410058140801180724442580300d2800ac04044c0d000300e090103034070301c8070805600c42400028420782040c000705103484c115401c060306c118460b0420420710944200c812400c0080e561059800452140030f20102d8000c51051804802c0b1400d465850107924800200081d10354400e0b003030103440c0151040508280039404604056801800c2d41d03036500b801081c11011240f5800140c8500d03000080005c1d403913014008035403498419031607107400c41c0e00c5c0c12a664020318440795084240f1410360544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 983680593 1250 983679343 983679349
    0xb0a080c130213032114120606072a06110c1507020307170a1203050403020a320a150204050d061a100201091a0105060d0209030f1e190f030e010e 64
    0x800300a4016100c124510020a1000305804020388145001078420413900021f5202080e0b01940703c4d10941d40107550f043d180c5848880c100c14510021460407405415807103210303002c8005411540c055a80301440300601060030740350701c1109102075014144142800c0b0a0700c05901074002e4a00080a5454a07a40c40074003010b0151406005038040c2c0009103000304010300c11b8441e01300c0322914901005607203440c0d540655141010040036001c43c0d0309044048501b0106000d02d5124940007060100407081c0c2b0342026030f601c100d444101c076012804644002d04007842d00c01d0750103d540083c03010051503102d45403080140501e504a84031410102156001611280c200050191466000054404017410700152014400c02000e2800c41003a00411241c2d40c0c036402d036000580104d80043e80c5600750000130f45042611048282d690040185202c140e441240241600032815415510b01340c120180e007113103000c031034403000b40600c000300c0c0d0300307004680300f1802d1321814003040c101240080a01000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 983681843 1250 983680593 983680613
    0x709050405100e07181a120a060c0905090a05090a0f050f0307080408010b10052703060705121b0a1b0c0801020918150f0604090603060b0a080c13021303 67
    0x1a2260f6500c03148081101c1400100145140d8120140c1045010411120500802518440140325880000f8079814911050180350f444580c4030b00d041150300080302024003458210321403203208448810004400d24458089c0511600b09000a0501c1c03500305d076503d600120014800380c91500c200240011000381c01c0004018260044005944962030501c0c4d0900307564000c2c0c0118000c81c4002181810b440c0c0100aa030038952482d14034000b02d510b1800f00f810030046601c030181d414480c880030f11800c07070380142c0286415105507210220a9a03107800070400514107007a040c0b4030030420000207800070301c6510300441e51507500c0c40e0600380c00f1568451600c428005d4004242c0c41e58001017018540c901100012030110046140030240c2c603019040c08419500c00d00b003240500c0328405c09001503035038041101c02510a6281c01c001c1e4a07228103010004000c042c00302c0c3d01445100030041000980018003482c02c074170080c49403120b03da801c940c5401a412242444008940b15400400044c0300350403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 983683093 1250 983681843 983681861
    0x40e070e2e061d0f030a03030b0d0b13020913030c0204020f04051f0206090c01080c1608070303050907241206080d0815040212040b060d3201060602070905040510 71
    0x1598a040c0102a4000f40b0340c0c00482200d18898a02505008215240030400c240426098107000500c4000d00300820200200301130000c0000c0ca121040010500240b0b4980070040c0c0242c3e403203030075a620100d540f52450049800580400c440620040042c640b60700200324925141d10901e0401d036841000c284440c4400016012246000000b1510a50304101a50340250144002d008041113600043c00031040a04241c980d90400a1510752104d441c10300a0704180d4022070041d500c60309418020f0040c132003900d1040c4d0700c5c02140340020310b8805580360b00341c00b49127501c1141d04e40222441d01b5601805034540301e8084c5905c0d024006124001401041c281d8440741c0c80700350562500007042c1000c4c01c095801c0c240f04910611a092400384c42c1901690301c40c0e0b000528452940721000040c20810003a2401800610505060600014410440c40090040d00c0d40302d450309a24000c80c0e400e85081d4001c100069002003000c00a035009600a0341c0c02134041cac000d46044d80000305000c010744944030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 983684343 1250 983683093 983683097
    0x806390d0e03040e0f19090f031404050f0d05151801060f0501080604050402030f06091006080601030c03020d0c051c030e010c080d090c03021230070303022a010b040e070e2e06 77
    0x8c0400c4040c0b40d04540310440351900014440c0c03802d0f06180000300c903841003410f09409854070b48810020044100549402d4000308a840c1e907031842c10b058418200100010000d00030750900d01c0021703c1521040200d01662016112400e40c0c0d50b84000340401410001d0083e40e0512400c00d4580d0140024442603000d9030448028200c1444684e56006c2581c0c01c2c6c0c0d11201440d07000c03400400200701d0080d03c14003500d078103c640400300301042c101601e0429080d008075905c0246002014520400b0490079040d4622a80701e080820b440e410055030350041206000d0100c540402441d450100c05503c201030b010701c0f61042c022036a440c1c4c0c011030b0b0700404964881004d42c0c000c0901c55418601005042c0c04040c8444019000d036413241420142e03030013403000003424181c0105d2910702280c2103480696042c211441e6100d080414070f01c641d0301030104070304924015858010b052110078808103c00d001d8800c0b5140d4048142c4400d03050207402200a420f03e0480e4030f030f00810000c2e134240850304c00b009203425 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 983685593 1250 983684343 983684363
    0x6150d090b15010c020901120c09020309010b0f04020720010201060b07050a03021c05070803070c15050f01060311070b0c0c070305160f0806390d0e03040e0f1909 71
    0x507103580794030b10400b15a80c1d040c0009420142c0c016962842254103540e0813a010850514051403d40e24094031500000103d038008410040311260540c13040304401c034100e81e001c1c0300410141c1800100e208188018041d2072541c0001c039000c03047c803410301500e51010b200006a031940c0307942d400c00d540c11200c0116415080380d2921b005042d8104908c24420304034400305040c0006040d4040c1551140c2c000081c080080400003640181c0901d040105990b000460318142c551014062801028101d551b00070b04a94000040741c02d42c030900c151811042d07400007661030000c1c00d4458044506000304a10030040d0100850005810103100440045101c1c500500b022015034540803091010b64220341c0c06520242400c1040b640d0020b0501d03044a1807a034040c8402410050f55080500070104410101d81a420310303450304103010000304032144005004014907200b5002d110744a03c04c5101c5e01ca584142c40020480400040d62100d03040600380301103200300034914041d1002d07107008000640d443d000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 983686843 1250 983685593 983685601
    0x405041d010c020705061c0603120201090506180a08030a0603230d020d09050103093219020a060f03090b0115110a171b010608010605010906090e06150d090b 69
    0x402d0180a500062500282064a0400c8045032071401120040c0754040c6104104c01c03144c0c4040c2d07015502035500f0014540070100030343c0000c1d0103401c40003002c6a0034812000042c0746800001e40f280d03540c0c4c00c03131170180010243d039448800f41d0303800241c41c18543e0355507260000005400305030000103c07104040345070080c40035410b001d4180b00070080c007441035400c94010a08034540c051510003c0d81c5090030000791020703545c00c00a119a460188900c0c04500c025440b0354034040e0000004030710709586044030506e46020788914022507405000942002504100344441801000c5044010f0031038a00040e6081650320389019030301302a4080054a0005c1000000d496805408151044680d00007455282d00aa980d650350111003030f01050482da01244141a42c0c44890321081129038800081c8800b03910fa00149000b4451840b51602252031000001400c9004900c0b020460340f0745ca01b40480c589d107420a002021141c850102a804000c001d00d4030f85003024402c14001034000c902d020080d1030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 983688093 1250 983686843 983686901
    0x10b040f1e0612021c0204051f1d07050c1903090303080105013e030309150f0702030f09060f03070f090f03050330130507061407030f05040504 63
    0x2045840846a140c01c00c502408040b00c0402110383c07656040e10700c0c0c1056000c0310941c10303076078846150080d402400c0030140505030079403615130700c140c505160019203866038803810307860000c3c0180182040b0104140000700143e0196003d0300400e8046030075995060700c0c141800880f40d50041046020551881003801031540c07101d044d50241c8030a0800d00740003950510251541104410b40c0500101400c1249600c14204d401030010080450122601c82c14003400d01512a81080d2106c0c95660f80400000d80001c4c9010444e4068400d41d001b80d4980095185001515440110707038640000080044030341a811000040d0b10a04040e40c0780304829060460003094802d0540c0460b0903582021000d001040d0003108032042281c80c06c1180d00c004449050b0311030020201c0c2c03450308a0722940c4003001408040211301c2681544a48191503400d92614800d80301c6401c81310b80311076510700902001000a024902d480c450500d20b00708642050750361000036064851103582005415440005030300300039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 983689343 1250 983688093 983688131
    0x303051206100507020409080409110304060f091a13080c1606140a050d061a03040524010605031f0b090f040c17040816060203061009030b0612010b040f 67
    0x8400b00c9001c044a40e445800529600409034003910990b03488002c40d08101381c3c501160000c1800140c18408000c4a40d8104029001160242e90031414491a110b00e8100c51140340c0c1426409030001c80c1080098010300c5000000520200210b660501d41c0c0d0003249501c0c01810384502460001c140c0c804040140001c04500c50f4848014401e545500c0b002c2541d0410903103902d0030041c51302c661640920300124000d0051580001d80180031903c200000c50140e40045104501441c110f5904000749000c103030031695045414060000c02c40c0042c854944124015a04440c8000411580d90152210070130100801d80c00b000c618403000810281c24103040c00c400c40343c00310031075040283d07095200d000381c80c1c862090a0f08688101110000c2c08110b0414207590008000100c00c8280c1c485600e0510003d51080c2c3c1c405e407280d070014000012142c419483d2000740ea5008030314038031944400090080c660315803502014a5500c0c0c4420320344c240c4880c8201d0744200c0c420f00c1c01085034003059010740d00740 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 983690593 1250 983689343 983689351
    0x90c01080105031c12020f04060f0905222c190503040605030603160f0e0a05041a0a02091e01030c090e15040b04181b0e0a150302060403030512 63
    0x4450310300c00410240d9004a00780a03941d0010842e03910103400800c0803643d20080702c00c01780d241403020616044c00144800600f042e10300e540c480d607840501c070550545180c02144a1641d22643d841241408030642c210030304070800b0000c00c0400e41c011707000340e4a0002070034540305480070582899030745510803040045560b14907503c081c8100c001c071191505501c03880783c4c0c01103000380000040403034010b4900300004000580381c00d4506640075154580da01601e52075200d46803040c0c0c02800401c50305452841b6080c001d070b50010103103103204041d45000a48020040080700c01039070911200455441ea860b4120f182940c8008480a240c15040090b00701c4040c1c0a82200704208070b01c1c14031500003036a041c0c0d0340100b0806000d8810b00d03440000607010b40149400305400c6801c0807040c50351004c441c801c1e0b20f80940f240c507004010032642c00c02c02c070205444e4464501d1050f10320000c25150f0790703290b00c1944410300c4002d20820f09600c031313004590304d13512550003240003e00004a4850440602c81842d801c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 983691843 1250 983690593 983690597
    0xa0506040f15170a050f0303150402180f060408030a03020415030506010206070c050a24060603051506071115030a05100f0302060a0e13061806120b040501020d090803090c01 76
    0xb500000c44450908850750191201401c665802c0f00000fa00411000076015449001c507030241c28003451781d540fa50400e42d50203c0c2403800e5440130656291900030388200300b0a941701d050404080703000f08221184520f075001c3c0c20003000c04c00425070160600081510003020740380580e4440ca003140107042000c03410074180801d4a0201404510380c0e0115030150060b059140a21494600d810328a00380380f8080e8004001b0b24481c41c42c52090f00601181104000103508200401d5070341c5d44055042d2402100d030302c0c0740b0b8420803441600c149405409407180074059550b00e80d001d64100c000c00c0c86101e403103284080340034000c000c21120407128012554800c58410303d000c01071380742000241402c070080c000248950b07004038a03202e01d68820601e55039454401840d08124010032500c1c18000c248074010407034911041c1c2d80051450466001d11021186582d07940c5c900c1d03101d04d0f22020501180030340211001e5400b00180f402c0d48005000300403102d406904100c0c0d9034105154030610b17140c0400d00d00b40c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 983693093 1250 983691843 983691851
    0x403021302072f0a060908060a11090d03020f071202090c190e04090c0b091201150b09030a060c090f06021b120f0303041505010e0910090611030a0506040f 68
    0x441c2c0485010000703e411030504202c2c1803030484401c24035011442c407a00001010000540a40e000e0300e0315089031096800d8804079250401004160340000003c556450410008490a0705090781078420940c041c0c4107650100c80140340543c01c1413110345c000a60b1003031503420f10b4103628248441981242c0c41040c150320b0f1500300502c4c3d800e04036854036180c013400703580d41140032103450359008402c0d1070340d210001840040d112100000b91303400944000d4001c0c2e048800c1c010b015030051181d81c001e000380e9008034040c40d14100d0702c442a940b0200006030503004406c400000140c0394040da40c050805900c0c0e04596504001061640d00d1041e071151007158003d4495868a400c04000580e41d20800d6865600000b00800b1141c54642004810301252200104200c203004041c0c840c0c488440b111082409542da0340c200380c0d40703500c4040d5034440a5811820200c0b03508600e90344469015446030f10007003102400389003020041c0d00701b00e0b6291100e5403640d04000091400b88102c0101782e02d02d540c104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 983694343 1250 983693093 983693107
    0xb100906210201080601030615020a060c091412010e030313020312030721020f040303080907090504020a0b070501060b0313050106050102120f090a0b0c0f010605061c0b21030403021302 81
    0x88825591500e010307040c03004e0103012840c05d07480b9400c94030241001442c4c2210b400460007009582d40800300060f5462460042c104020300e2049a842003100d051070004031081010408000c1e9504d900b034005007942d0b40c0d40f4450003a00c1b4091002d58070807501075000d401c030700c2100c0c014982800d42c46260208460b0b810010444003a41003488062078804134110303807184640c10341c1684000c1c861402c044c4204040482c0000c1015480013100b81b0a03d940000c0c2c0c4c2d03700b6903541c001d03019a00706075070003544070a07152801d00590f504003014008180c014000450324940d03ca42c85d05907907109071400c0c044094000c24080074070500740581d41c0101001c0c40241b81d50700b5050710741d9005000388411442c4400b800100c41a01e6598607080b4800f912540c412545c0ea14040b10aa5541c2c2e059400022019401d00c04000740c4d91030120150b071820103405508045004402d00e0200007051000019984000d8500403128003070f400c001c0326008010700c58001d6642c0e03030443c010800d2950041c007202ca0010300401c540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 983695593 1250 983694343 983694389
    0x5130b130b2a03090a0605190f060305031210030b07120e2e020c01060f031e02030c01030f1b08071209081213140123090d0f0c0b100906 60
    0x8181a890a4460b242d1a500d601c512181483c9121501420035402c0c40b06024940015141c03804844103c5942000765a50041c440030a6402070f200c0a8500d8009011081c0f40f89403e44000da40700c0300300842030200c81d80765a1a10901e10095a2441c00034042d9036000b400361a20b407003100021440e0340024011100310200c500c0901c8507081c0403404402c499072888800f4000303901a2a0f2000582000303001448d00e030a14070410f5002c41c4406e95803000b8501e044c007600c2d01114605103c42e0380103006081380c102075000550140c040d540724142030704d542d05041c02114000313017207808203003403540c1d1400075a0501e01d030018034090340061240c080301d00d8040e404000541010894900359895001000f40c0e1303448000c100c0d650228110040c1c00c81d2420340c0c070b8504850041d40b0461504c0101c8006000c880b6030440c2010719036408490445a034ac0c0030210580140d0700036a8481d180704510304c0d11a4203100181d80f54518000290341c540c500082140c4107002d40301c041d0040c03001400c05215050002600d07000c130 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 983696843 1250 983695593 983695651
    0xe0c090610020a0611031b070804061b02030109141015091d071d0c04060503040605060604090c0504030c14060301090b2704020108010f150305130b130b 67
    0x14492107150032840c1414003a00a1107080a11900034004108034107000c02c40e25425402164117000301c1c07800d6030b0301c0c0c3e00c0740844e5800d4030315181d0081042c50038241004402c0d512540038034801030300040704034625001a03400f401050740c0c6a11401420b00c115601e40d00c40707403a200b03907070a480000c0d40c1006c6401000e510400f9011003103408508020a0084945500010a0b401c02d050020749004044c0302007002181c4241c121000d00460007004c6070ba503510001e80b40680260300070f01c000610100080380200d6030343e801150704420001c1a00707141c03032b030340d81c0c8518220b690501c07034500420b81c042400c10610040701c1000f0001c14021080048e00d034507a000081c0c0e0f500c0140518032040750f0703e16070a0381c691505010703420010b9640c064030003140c5840d2804145600115006c900180c001800801d80c076420390407207021540b140b132201c03a50031911041034002d45030080c100d80d04800982102000314031403015040c0180104608145082410304000f140d81100606400c40e250840700703031b05000a1202c103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 983698093 1250 983696843 983696851
    0xa020a020112151e0b04050a05042d06050a050f09040219030b04030309150b011b020d0b0f01030203070909150b130606030f0e010e030a050307200a060e0c09 69
    0x42c0c281440c0c4400344800d0000c0800d460000031100c2caa41003c203c2c131040c0480c04c00e000c9002040411a40c0d070380d085021042c07086000c0c041e00007100c1401000b881c141034011107070f40091038500700b4183c0385009085440c1d0890b104842e07582502c40fa0104a075081640803000540000d9030240928007401006c40d121030000b40c8000d01540c241da018540c8416a618600051503020950300c4c00d605182c10b000303010700f42c0020b00f0740740101c0c00808122014041e2141240010701030b10b60500d01c070b91442c4554007003031000000f43d030003d1213004c002c0d0004e00400c040301e00c0b956071003c1c01a004d50650062614041058009140c1545405014800b01e501c0001d9006448801040821144400008202c0035003600c002005403070308142d4046212601600300c80048010494104200440340c5001781c03d885001e000d0300c02c107810130801040140d105034000c540c408001e05282228442500784464070303950028501c00350740c10442030744c010009540625151a09210024004402c0c0c2000007642850050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 983699343 1250 983698093 983698097
    0x206150307030f110310020313211e020f01060308040e010f030305071e05100c03150b07081308070810110403120305090c1206040c090509100c0c0222050604020a020a0201 75
    0x5006051317950100f240c8030401840c445c080d5144c2c241100140c5060943c030300216050008004440e01202102880c0004d2100342d0355a03185600100800d501000d80c4112481d0460143e051301040c0c121003402140000c41c807407041507a490345083d46031440000182c00600314000805410000300740e00c078056030790290b0032403118249844112401c0803d00741c800383c0100341d03008034034010b44c00d0345040d40000c07155581501c0901c0800240c05405a50603100d0040202224003800b81c907010070340182c0600449401031582c0044e00b602d40050078034000041e4001445d03507204618000704161140502c00c0070342c0803401901c0c1410300319070740c4001120021205008041d55540000d44442d003c0000000e8624080d002004603404820550b0301c4890883c1c040e10806200c1100044056080c40307550f00c505103210203000310080e8024010042c2100d01161020841401841c42c00750b510f46124441e04480402d44418100300c01c503511055450043c07660344500d20610a044003690003003120320080f0740c24 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 983700593 1250 983699343 983699363
    0x11b15111b032703160b0c06072307050f0a2003010b010909090510060f0501090e04080a1d09010902040510020c28120302010b1912021512070206150307030f 69
    0x800d021030316001c41c0d00f83e4070783c40301c42644c0001b0300c0100d880000d01c4c10303800504c1924856a1791000507500314106030313003074104a130100715080407803520000508226442030f0f06580d8000900c07582c1600c0c0900e041025580c00e40d80480e120b03a4900b0078a00e090301c003070041e4001d01414034440d002a00b120f81c18414050b0a41c0c90f0f0340035030f04008003400070710611200c226040100980740d004089094801c3c0c01401e0200fa000c14002c01c40c84421104584141d5011007040d141509100d011560f51f00070007410701d40681140f640180701e640b002043d03806824000340068070350340380804001c240003468400c842990001c0c0b180d020f03641c41d441c00142601694a03001c5200000d8070440208480580e03000c030008000c601884010181e040d001201900000c5030080d40200462020005440551003282204080d4081800060400224100941d902d203403120b410140440c28900000c00304450210041c1c00c0320f8100180c1644082801d4080d003819001408454250765908145107804030380540380c1058 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 983701843 1250 983700593 983700667
    0x234060e0a090c0512090f01110a030605030601050d06020a020a080f12010e09070314031e040e0c030f01050f1c0f0b180721051b0a1202011b15111b03 66
    0x108100e810740400c140c02003103030420389c0d100307a03103190040703465a000a030034106d00041e07038a40083d1a6041c3c5000800c4541103030300b5a5909002980314040f00360660140040d0840400c0340d00700038103070013028151507940e5001840b0201103001c02c1604884840e5803030400b402400c047c0042d0b20010359070712555107030b040f002c1340300072510b903002d80c01610542c0384000b0800106042110058411a0b012038030001d40c9480f4070f034040c2a1400102ca20f01c3c4005003250042100e4a090721482c50750726009000e84440b0b020300c9404a91003000d05000351290000c96809074208241e80c40c80d69071100101c0d40d40b1110052142813161249140d00c0303a4402c04060021042c11081c0c64080b1591700c0798060300f01d40d407105e61b84034020b0040f09a60061407083e00e0742c050001d02d11000301c2a011410b68165202d1900d218018040c6103401844801542c000b11fa40105000307800c1a88688604250751510702c40d210144a490702c440d01c1b1446a042040e03400901c01003402002d52130055001c40b401c2c61980800144c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 983703093 1250 983701843 983701861
    0x1707020708070914090f0d03110906030924090a02011d041409071401090e130c0b09130b0a030f0327090b0901060234060e0a090c0512 59
    0x1407904514000d0180c0180024142c96592009401c8440400b4005403980c49100c0f10303458921854600782240c01a012100c652403082c7d11044a980c2241703c203500b012224030104255410032201c00b001170303003c41c81340c43c8040700310740b00c24105e044200071100061514a000503200c3c80341d060001d041c07011a240c0c0c466100b1031404c621700c442d08040c10403c0907e80441b820001c4080645080925004028000c9103e0018000308104180d040c1c40c0d804860b882c04440c543e03001d41c01080c94203804450002140007411036070045000380307940d6210390380380c1c10a902044800c1c0750641c40d00362014a071100a0813a074440480400450303420010f1004110014107003583d400040303032025480c0880e000d1019010300c01c1600010260303810304600b08902c0d4000307018051280c1080c0607030409a13100c003000030700d082950210344030012503181d0790945030804061500750810682e0405000301e1b411046120311400e007402e069000f000e04540074002d00080700006040d91003107070300c0b0704450340001c0000380c8510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 983704343 1250 983703093 983703103
    0x20c0d32041205030702131d07030507030b25030b040b010c05070e040f0807030206040c270f0b0d080304021206100504050c07050f0601150e1e2412011203170702 71
    0x190050440603207407001f21440c000610000020044200803440c008070801000200030040d130354404001c00782541151250788100d2130040001100c40103040c541107600049940440b80030f60307142c80104091800c4020131080d11010004581009284103001e40840d20024440c0308458249081d110251140c0c01e1002c2c8050180c03101070202d080000b8528101540010564031450240061b2280c02d600d4441404041303440c2c0e8031a8202079840c20640038448140da010340d80d0311084190001e04031810341301040c0c910440e42c80c02d4800b20408400c10017541002c1e00c01c00d052142030340c041c01440c6401949a400003000380507180c00303560360b080041c000010600448a1582d0450300b105d10b49070110084035990703034090103804204564880003a0380701e400b442c070782020120010424032850341c14002141e8070502d90020194802881d40690415401c5002c0600c83c402c000c1c40d00c40c2c0d69094070300c892000a01d040c0e000707101003114142d801020036031201503030314000f030281c000c030801c0c1d1101c0400301d20385 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 983705593 1250 983704343 983704357
    0xa05060a05160f050c0f03060708090705030f1006090b06180609060f0a030e0c0f131103090a061104120b04060603050f010f1b05040b030a020c0d3204120503 69
    0x40e9590224000d10200c3d018014149204000311880768244505020910401044a940540c054008595628020409030f41d0102d8100e0031a901107950364000382ca030407401aa030780416080742170b14400c0a403050040c000904510764003880401d501201043c0305100300084051001c090300a1840156074001c2240e254200040500c0d88400054084075040c0c1d02c0642c0001c042032034050041e8034088045890a02003500501e51750310103c2d0441400b814a43c1c2501d40070f440e41c2e449a10b907e659500c04091406150304000404c4456040c2c5003960443c0c201c40c001e00103079078050104114200310780300308859866000b1105840c0b03440d41e00d406000f91a00d904020614003800b010004408415409144803440046061040018882410810b00710202844000440400040c000c6074600c200454001c0e028031001864002000f41090500c0782119220300050390230002945010000151031490143c14180c00b90036484c0c250804400e0b02c2548900307690340c0407085038442404428015030b51a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 983706843 1250 983705593 983705617
    0x61318020423090a1401180e030a03061d0906010b07060b04053d03060504030207080a210305060d12030f02121f03050c210a050d030e0a020a05060a05 66
    0x240080c1c2085100c08062450ba41400f81a034100029450f407000c0c0201042400d01c880989496401c0c0102d091040800380b100110180c0c80340004012854100001d1284454036074000a00c0c0e810b0000c400c1c21170000d40000003102d02100c06000740140701041c1c0394111802001010f07540c44440ca800000f0340040d04600ba800b80c9484204402c1201d44072100d920301052000c102015900003200c2c2d500c049a0f080700303c468440c0440f042c000605294040f0f40c1290007070044402c0c003030751000c4003482c014020001b228810800c030004c03484a0f03500040c80ca01d590b45030806001d140b82400210b0301c500100d21001d40001a01072a01050b140207600a0381d030039201c10401c0d035640903140300300d044802b81a5a402e0035140620b5815006070f880c00c0d041e106413540000a03101202e999010082c4245100c000b2500078200d1030710009101100700040b54070395100e00b0140c080c02c1c000d11400760449181607400c60307964010480340b800503540d015441c01134403001c98140b0785484e50624215102e004403007031000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 983708093 1250 983706843 983706869
    0x30a15080a12110d020a110f0a030c06080f2203030e0706030209030705060c0601030f210810080705060f0c120721020106060504050f0f0301050705090f0613180204 72
    0x740030b40214026041c4241e030b1148980c00300c40891880d07889500000f0a001a0048a8030300001050340710141401c0500400140790407001d00006804c085581d4412a1408071801d4100001a005100c5540c00745000816408a15094800c48002e02d00d07a045409000e8506c0803030b40c205402a440107000b0810b590441b0a56a2580c402900075400248117502c0f83c85441030001d01440c0207411583e014032060301a01184c0d207903030343c1c0c11500000d91710102c40d00208c015071821150130001c2c0c14103902c1c1c171036a520340e0f003401d20041c4000d560645402000300f641000c4c40c2405151202d00440700c0b1820851415580c4140d03104555007410062101c210200c03000158403002e110611110607600c245107c864a8001c0080009a080700c2c400d1041c81e010a40070300c8204803628004400324141e5402410000589158800207404c5420840d0b4200200da00807ca40c54a0b0814682c01038041c1c805698481c5403445021800c5e00080e031510400d40c480a01d10300000e640042901590010b00300700309002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 983709343 1250 983708093 983708113
    0xc0a120606031a030f030f0c0c030d0c1511030c13170307030906021501090e2103100f0b030f1812030403030f0b0f090a150305030703081605030a1508 66
    0x34040c2c94640c00e000040c400f651000c040e1071402060012130700c0b40c01c100031403522403030f40300d560525004425218440e01408860b020300e510188000b1004034019903030b00d582100145810110906403926003c0300c14035010f80341404491550845c0d411604040c0c00903140c103040354a8481000c15600300b41410107500e0007800310484000044e00800b0f10035250303036960039110300c0200c1e500c0006100480300320319460010850f44045a204125600b80c81301a1080c07000301e0041089000c0301480b4500006900008002611894010301400f40c2104080d04001901d40044040140406480316030180101ca02107040d0340c0c520f003030032000c0b4482ea206a440040d01d411004030703d50422202907000c6420b01101c2155140741e8424908103600040c10001c02c2d501b01006d210003520010b04801800343d45546004a8112041011008500c15001990707110702903d001002040045d0050700c040510030090040d01d5003040c2a030382c2c000d195070310004611040d41c074001c6201015902c03c0c81c040c000c101ca68 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 983710593 1250 983709343 983709347
    0x307150b060c120406020f0a0b0408030408070b070206041506060203220305060a0b0a05040608100908040902070c080714061602012d0f0503070c1e020a1d0f06090c0a120606 76
    0x1070005c81d000e58095501d5951815481e5441d101c7d075900081101007424006400291050702031500540a5400641803801a80d10407840980540e4040096445003041004000d07050b005141440c0c1100070134080240b0f000303c041e60300c1c041c9a09101e01391014041142c204002c0b828a40c008603000345c100c0e202c0d41000d84041000305a034101e164003c1c07880e0032011400313042074001e400440306080b004001e8010444480d6009007a0035108481c0d8100070800014420041c2c0003070514070340110070041c5000d142c8480a468182140e200000c04881030803900c0440ea01c4200396003601d036120041480c21005440100e840304401e41102d2003c0d07518181c1d04086031020303a81c0b58440502a01c03000450308246c00d068072940011a200b03000180340100e25400903004440262010404040b41800e01001e335002031400c11058100e18004442c0181142588901d00c40180d04060f600401c5003440c2007490108105840041c0707500c0c0c0a08000400001c039912489030000b05200d238035810000b8984030320340 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 983711843 1250 983710593 983710597
    0x7063b0f27250f09090203070c0f03090e1f1406041503020d06090e1020130b0409020307082a0a0c060908090f041e110d0615030e0307150b060c12 64
    0x80f92001400c04900400c084050f132007124000e01e0640c17607203141c40c2003650b039100754003000080403000c01003c80c60015200404c03000d02c5000704508240034161110140d007c4507564203e50040c007002c030144c00c4003103184d110710302118282d501d081000028402103d82c00d802030312610600c8445607103001d40000b9002081c0e803002c5151300c42c03242500c50144454826402780d48000e01f0300e4009440b40c1c100b5200f444011b41c0182103030811181d946a4095030749030034800a4005034086461360303030000f081004841d40080d01603071050812086814031814490350030450800d44090940c0e02e600094058203150150500c0d50038503902c1030007400101c0140c03900500d03540010400d58003d0714200415151464580900b04c00740341040d05402142c02034880510141103004011081d03100d0801c00c25030070308828043e65010b00191020b0440c031050841d001002c44100a0401641e41c00074828140003c40d1036a6a80c0d40c0c1001c5140404c2c1105100300088030303845083e800f00000d1140041844815100d080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 983713093 1250 983711843 983711867
    0x12111c0c060606030218040203060f04110c19050709020d020c010509100b03030f0904021602090f25081803040f0915060c0507063b0f2725 61
    0x14042c454503503a910190241d01031100d00071000e180c4a11801c41a05080d805540d200200820300007000c4a1803010030100c0d0380e00880d140e0b4070707900001e455451042c1003043c01400f101c07107440c8011214a0391541078a60415005055106800080036180001c282c3c05903080041d02100800c00c609082c43e48a503500301d1000c032030700c00e02d050468a10041c6400300560700011501d0404614007000201004000d43c00241180342c01c1003440b0070000980c07122a9120311407040f1351346608007030400b0010245003503d0110310091070007a140043d6003803640b1a01140d0801002e41c000310780305004403c1103080d80540c1d04018180710303040200050400d290b820a001e11981148000c21107621281e00711502d003041c2030080d103640e020f00420400300b4800c001c91640241000c448101843c4401101d80401d4120151840100045650400103140444980f00c078111b00719844100340382c00c0442041c01050788150b0700da10491110018000c43d03540080302c4c80d55800c102c0c0002d8134000d00ea00207020012010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 983714343 1250 983713093 983713103
    0xc0c02010f02010204060203041e031211010b0a06050901360608010f03050a0209091002040e0114030f28060c08091b18040201120603080405040f0912111c0c 69
    0xc81044072290040c0b08450030349135541c2c080c62409042000c00b0401280c10038452054410311400000418503581002c0d0704802d581c0c0e100018016140203103425505021101c03031103046456010010f45400c582100c40001c02820102405280c400e02a414251640c1412a1070250449504041084108081c040d2141da4560340401d2b602d41403052010451030100610550200b0034040142c40d0030084640d006000000300c944040214081006030382255014040100040c80144052121a003aa103c002000d600400c20b04400381035003a40c40aa21146408285400509000d4800810204000940c12000900122100000050011f9000c0b240000c1038010034038600c3c4140c0003246100c1c0c0d202ea00901d0301d010b0428444c0300580c00c1c030f0b010740124103003d07600c2901080d0040c0b500448000310700448045407694540000c1c8000c0c2c85003160014002488d0000c0304000450f03e20f003901040c1a6481c0c02064004070200092600c100c01c45038103198000781c0c2c00703071906550188109203018451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 983715593 1250 983714343 983714357
    0x1727010f080903070f150f020711090609182d010513051b120a14010c0e030307201801052d0f01030f0905010609050912040603020f0d0c0c0201 63
    0x314800c031524082600c00c085150004c025140c00300d014894000d04490152104100145a070510582150765101d007038a0104e4010942c101400481e207900c1d03030311410540c3c1010440ca808400a000c540c0e000301020362082c4064010200e0100410041942c42ca07026032103500681000705000584114141384108c81d8201030019400d04203007004280354590240052048001c0384569400e40c5c10fa134402141c021030340c0d0950240400b000c000c840003240c040c0840d0001c140f09181d00501350390403000301c0e40a00520074040d0071789480000881c0e41c2e00b0b400c04551508181c00f000d0ba00b02410b142c95409030f0003228190b4401a8020f64041c1c241200c40c100c810300e00c034070210082c000030841c0c240a1400c0540c0708500081e49070420085183c01c40e08140740000c1e407900648402400c40ea1101c8007030381c0c1c0c2c0c0c0d51401d040c400308600c0d200c0e807500030319104000e050450a5059030f030352a00c500d0203014200360f00814040010794162044d0750078141c4400040c0080514684000c03c000300b02c6c00c00364009441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 983716843 1250 983715593 983715617
    0x20912030702060726030414011a0a090b0409020d20190e041104020f040806090f191a01090209100309030219020303070507060804031409030a172701 66
    0x4403103100c1c0e03003e0141400c0c0031807600ca200140040300b5030788098510b8100610990181780c001548200e01c01c4440602d00c2224940705030031a00f66100c4081400400c0c0c0c0e01c44140d65412001008444a600c80882c42c4464000450090880b050300250812085000c910820038010303000c001c036201da000884485400300c810403600c0c0b190100000742c00040c10a0900c100c0c441004e010364841d010310702c05220452994082000c86c3d21990f50150384000108061000350002d00241e508080500018010701c1d0301c003010390742c035a49448a401d1301d40c40180c40580c200124031581c0c8100120f204000c440e01c2d80e4034405c04010754020b1084500c41c0a4094043c0302d0507010b88508080c1c0c2d1341517402040300400c2d10580710134820704001c042e41e2510013400164001002004940003400d81944c903041141040c0c85c0c090001181c0d141d0a90300e4202c140882882c9840000b00c0201d295040104c5806400d00000f03000040d03c10b000a401000d061018554a84294445954401d040a0380c072542004c0f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 983718093 1250 983716843 983716879
    0x7030e120d170f0115020319020c21030d0e1903080a0c0c150b1903060b01021629041d060a1406040909020102070e2503270309180209 59
    0xb4116038880f0074032018001030210100c0c0c51410003004151b401103074946111a06c0300048190340d403c1050041c1d025060b070030341c203081c0003000c400582174040c400c3c2a00d54603141588d48a00403602140340c0c0c181d44560005c04040104440190700c840695045c1c0d80701c0c0355040c010246507044800c032007061b00f040a403480180c8500404180c2d9500081140c40d8259240b03480000741c52200c4940da0700c25061440b02c1911100b5190a6000354032a0000258106c0078a00282c18004011a0f012088015102c104100c03d800c440103519494000c810311800d58030017952640b02e020383c0d08034180015290b0b0311031140c04a500c1040340a00801c541f04010507542d1440c403010311200e00906604454144000c004154454002001c01c074414016039003034940340c07a40c2d03401c001c03002c481401d880b240720703412140c07444c0e440f01002000000c03900e4180128000400100c6949016188191075544c1c08920b05003414450352011015010003458800480b03005940a00603402c2035052621842d00248080003480c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 983719343 1250 983718093 983718137
    0x1e0709140105060909062202030603070b0f1909030b090c090108030405010c0303050a1404050d110604020f0f0103110a0f110d090501080c0c0102070b1807140607030e120d 75
    0x410040c0004e1074944a10140854a840a01500d070003072140c41da660b08811043c507205600e184444801030300c9241441c00c042c5000c041340d201c145600707010020a92240114030031141c950100902101400d08812411205e066a560003d4101d1000d64240001c001001c101403d412200b1201e4003007598840c1d50107500ca102d81d20903240404d85089040c40003074082e400841e0301c544203020005d503896410101c400204001c907411520750300541005a04650010a845501683c01c0d00800d12444d040c1c1c08100b51101c90080e0501c103143c02e9108000a0788650020704c4803030961b40740035880d9681a04040c0941c60f00e040f00342c02041180c44400803000000502c900901ea41d69103c201d00341c070382001503170701c25000380c42d14016000030040c240200c2d50074002440b0807880f41091103890b1421044064440c6070300ba03a040f01c1e0342c02851041040012904911a03102e20440f00c05668036603030b2600b502e40c825010360a40e0007084002001104807408601d451038860f05031250304a0304031145039001c0c44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 983720593 1250 983719343 983719349
    0xd0f0602070f120f083c06090a051e1510020d0905010c050606091e010b0d061706160c020405010305030301090c02120a03110f0d06150c050604060e1e07091401 70
    0x181c0c000c00025414000d0303582070303422000c4501c0c0c081600021400c02d444214070180300803211400c006c0070f0188070708007090480d502c800c51540c10407540c10031010000d0300c0c16480a0050f00c05c2031600200b18903e06000c60000c40200003000040a20701440c0041d46400d1b1712003061021520724071002405e54055108800003641c02030180072666215004c00c241c01d00041c2000540022404049075a01c0da0b030032103030f400b9140c000240e5403542aa400c9060555445410440c0d6094078a885000205000030f915604062a079840791000c007030f0300700d084452924000010390710034140000001400f5001c4015070603036001803130a01040e07a0059050341d5400f2441007103010181300304a00c1c00c070644640e0120480c2c01c0c95203501c42c0b4003d0400d198030380030f411940e461006c080eaa00f404104212009040320550209401e1107004060b0700c0e1103e070703103800380180040d000da03840701c40240000030305004082035040c400c009581f08807851082555501c0030ba0081c0000701e440c00c00009880441540e0903412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 983721843 1250 983720593 983720597
    0x7050c03060105031902091b04030b100f03020d060b011b060f14072007090c030b21030708090303040e010e040b1f030321180b010f140d0f0602070f120f 67
    0x10542403a03007408540d01c4010000c2040b112440b400c40030f4235040d0f03802403000310301070342c0605a07500700541505a041e100e5401103081400c1c000d0704100680f2106d40c1021020741024000444000200c01a034610603004841f03d100000782080c0010081d25600500d80c0b44204507041044500d4102c640043c18001e0300c0e9100480c14421460400010340c1200c40c01c8030a191003a1450150355204003000d075801c903081040441d44890954003d41887c843e001c4641d41c00500d996140f003800f03042d05469101c0d541001e090001c0001d0b80c04101d4034100101d03001030002d04412400c543e03441c440003141307010031b440480d030800c900004a120b0004158141020400880c003008000346159402d880300d95100140420b0040078142070704481a240c416055003d00101e0a010821500e00e40400b040701c2c160449003000c0c1d40000240143c61200d4050700c4410307015180390340c5004a83c00c00710a0b940c9140002020039000180c01e500b0492140b882e140e40a1252508130881c900640081e1143d4070328100601c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 983723093 1250 983721843 983721883
    0x20406030545070906150c0809120f0a03030603031803050d0509010c0b070f03140108030f0c0f061302120d140d060305030d200c0709021e07050c0306010503 69
    0x4024201d441450494140321a41d01c2c065010385655541081d0050344611280d03669880c04000f03040d005100070fa0b4007500c9141c40510480c007503540c4020360080d4075045005001d0019801008002000010004486101142c261060300e1038024082d00784c03404201d000611461101101c0d501c040801d90076250b010024180800103100102c03000d40142c0240c5040050844210000ca03590b03040d25402400290f5405618158060000c0c00381c5403030340c1441986044010040084200200985260509a0900c00d13512070702100c0030f501d00080c0c0305008082e80940300510542000d0000080141d40c030a48400104000d00c1d00d8242e100c1c210240c1c26000300d00c180c0d9004404e14444401058003c642ca040000c8590300c80d2206442c503085003424440340755071900c0a1129011218410018034640b0414a1400300d4040300507803558030505c1040400c80d0042203400c58068440e4000120000001140b03481e000b00c0d0034116a02c2e20701c00600350090203014000315281c200801da80c4001c48241c2c03d00c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 983724343 1250 983723093 983723161
    0x30714060306060702062110030b1305070807090c02070905041a180114040b060d020102190c050d050a110f0a1e0302040c080a0507090303080f09070b0408010204060305 74
    0xc03466100070402d035071220b001c001110040e900c410142003500354040441e40003580c600000c00c00c2c0c140241521009005003403003040000c80c000b106a501c41a028540d805494485c43d200b0f152950b541c00c00c0d100b6000700b50000c20f1f215503ea20585483e929030b800c65184070781e00d500050071140155009001c3c9042119503013403085a910140390000e81c01e8550b0b00b52005030b06940790031242004008003103400104180300c01d0140d82001d02d60046421551860354088542c0040d65603540961008403615004880c4407d0000b20f07104900100340260401f01913660514009407101d0081d881142c43c1d4541c0c0101c11004d08040d080000805406045c00d040709050443c1400042c0350840243ca103140c07406008801a2100e0156410520054640a005041c1f502080064400041c0441c04019502c3c2007000031980c001c98075500035041000d885e0807921000031a0303040c8030311074110580d500d000050008240105500400407a00b09a074104401e8859000c50204901d8140071031000e481020300507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 983725593 1250 983724343 983724349
    0x307020f030f341805180102030c0909090c01080f070c050d080402040515060a200313030b0c0a080703020306121501083c1015210b010e0606070b160905030714 70
    0x4ca6000f04082c1c1d4030000340c0c3c1c0300d0582c447c2680d00842e0880d1f41c1000108603486a401c000c0741154204080401034044000381c24002840d004009280700d81001c501c8000ca0b002a001302d56001e032554000c4240d5200c1030003d1400b4107041780c03e80c2c080b40500c0c50640018254400c0c1d0950842c20710b0000c2c51640391a0000380111001c2c050420303210301004800d907a1342c0103510204014a41c0945c140311107180780c1c3c610f007041c12401c00010440780c1c40180421010518590124a490380b0520314200161203844600c085448541c20405105452080006001081480116032412a68440101d81c94104980304451030764150b03070403800004a01492061000e0b00360406480048006011240d8440e01540755800b958078084094466130465141402582e10342e640c404440d80900d821081503221660f900e41356184140f141c40d00c80b01c040008030306940d03205801c540f00745400403424243d0f41881d00c03140707014416842000d00480c24000300080d00f4180031030320000716140e45481a0000001c1800c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 983726843 1250 983725593 983725601
    0x1614061b0d020c01050a060302120f030435060405010b120c0d260702010f051c0c02071203020f060f100311061303030e040b120307020f030f3418 64
    0x1100c0300d50203100403c00760600340f00d03462080754609000318a01d460341c0103100400b0036160082820360060b60b0581002c1100004403001c50765414150308910081d030628066152929410301900c20014000324201880012100c3c000d03406103000700a4100e40004100258100340340d0a42c4135005444808407a242081d150740e0720034014489060030741e41000700c21302015185510403084500200d040001d6503400400c0f0a4007050074280280303004203c0c44201041c0c1c02070b0711123051341a1a40402c80b0114030038000007006003a0b03565401c2e1326210b54030380691103140c04c0c001000907100700c100260f24038414000c0c550141083c020405420740c1180c59801e9200e0b040c481300c9400c5541048034a0f5000107019401008502035901d9403040b151000400c01a03840f210f503114800c856050107107030780200100840740d81d6981280c0c2a001000c02d4004203042c00203044408400340034078100461002041081a81d01083c40301d6103c40d80c0e0840c0a90440017901c40c05030080050f6044461004000d207544 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 983728093 1250 983726843 983726857
    0x15170d050904060e0106020d0207061d2403010f1e0509180f0a06020a0201150302101115092803020307061e0905030406020c06070803061c081614061b 66
    0x1000c2502e035113903131900e0701c4000f081c0d0040d03006034404c9800800559052150070050f12181ca42100705500c4000310000640c48050224400c2c01001e61105600c141310001c01c10b9904030080d40c0d600d961b507644800340619414850f41440d040e80008009400500d1505403040d0f9000410130b8800c0d460b0404036540300c07072180c82c4100861080c1000070850320000c000e20322001c5d00c90000503a5480c13108400030300b900d0794070031040341800d51040b007400141c0e28480c1e6002c20301440c2c901510912109600e40d0310304904448182500c052080034400c2c90100810100301c140041040c401580e07400103e00b410000790880042e00503003007842850300040c41c0b07402000c0540881880340340c0d8062016141c03803c0350040001160150b000283c02c00055805001520706803400311000c07410414142c40d0005a80301c0281958850245c3e00000c0125501d07400302d00740143e401241c06a1034140e48201c94901ca00690410f4a0030180d44e400c0401c8030f140010920b12070f09030f991005040084501d91000180c11880e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 983729343 1250 983728093 983728099
    0x24041b0306140403031d0a0201030e031c090204240506030403140307080406240b0307030204180527031602030c032a0103050c0a050f04050603040615170d0509 70
    0x2800002040303490003618001c80c0306001014190400c0c0c075004d021aa003501c01070300c1070b000501d01644418004208420500e40a00f004200d00c49540d118070b085200d20003550605c00211400360f02c026a40390301150491348265010003502e1003e100b08a00810b003114007195040380c800c0c040c85a400c1032006550800e200c0d040c690396199400340302c81066007088030344500141000341004103001c03450081005081c401c0e03490310030528600e08040302c0354044d0b00500010940005c042050035220754102c0380200004465181c1d696a00d0b10608060501640c42cac203424689035280e44078030411405001d05d0303061400004c1d880e04c1c0c07024080328081184600e0690b40741c010f000041c40c4a8409202008405402c800e500e10000321faa46410726a44d00d641c900340c101460442040b1044400c0b03030454001c03103060705005446444020307001d04203200f00e17002035421444c0801440200030071074101d00209111000496a0b0b0354a400411450080b11040e100785684804c2c11021020f0185000b001242e40103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 983730593 1250 983729343 983729393
    0x63204021002070510050d110720010f2705090f0106030605030304050a05011b1401151211151e09030f0c090a09030c060c0203091201060e010b031312112404 69
    0x14000110307070300100419950ac5510a0151401c0349501e0741d1150494801d090401100307810003002010114000e901081c460000845a00c1d1000c544400703200420b40101a050545003200e0344481031b8070284607900200e800c000001c07480b40741c04010b5805407030014000f2801c0070f00e01001101c924244038039050380031b41d55104103004149074a000a00d1084034900200308141001da601085034402e0b4000141a0000805440000e40b601419102000c0c210b40101c1a004180902041031048a480c3c584002c40035950040c4c1201500141110705400c81c15540d280c411546c0c242e40301e001a40c500c503031045240000800c0c901c5903038032425034180680381102285409a03560f50803680c40c2205400503900204e0086c146140c201445103038011311400074403601c1e20302422000190018040d00d03108050100028441100805074a2040d9400c0030410b004c0382c8a101018160381c00b04003441540d07004040311003050840480e04050450010203020b1081ea55a4460461510200b13180811200740 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 983731843 1250 983730593 983730611
    0x41a04060b04060602030a0e03030906040e091c0c110d02090f0a02040305160306061215050a02090d0309061206081c0306081b1e01020a063204021002070510050d 71
    0x140f4070801c0081e04c9180c00035a81d450883c10040c00044400340359903c2944108035020280e1602010382c0c00322000c502100e6003c0d26084025070500811440d110340746902d01c4034030704c0c0c0b5643c82a0160030b502c3c010400d141000d07124005100004601c2c450180d00701e916600861356510340204180d40c072000e01100181003035100c0e600c0608003280600118800024072000340b0a01c40365100f440010820048000082c0c516603485003208007041410710034040d80c690000b40880c01580440e0300c40d100040114410f030b4803a181c0a442d07500d1b01e0013520001079102d00980c2d0592a035200e0304c020340f01c02d94005c00c1101003039046000002002d0825404050f241d4070002210441044171200341100624411094a0f5010510011124200c420480010000641c084503600884da8010107504170780302040e00803200c0d5002c901c1000e06070009c03003200303000345101030b81030710031064a8050f40c0308684100001c00c1080c0200d9840d429070094aa000482c4002d0120a6000308014816503081c42c10102e00a00303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 983733093 1250 983731843 983731849
    0x10602340306150e370501090e01110a0e040b030c040203043009090f091202011a030304030c170a23190b010902090a03020a120b090105041a04060b 65
    0x600c5a00440b8a1511810502d0030202c0340f000200c0542030011031030420346040c0703000745180245030720f60030241a0509400c031221240c280aa00c0c1d8a85070700b0b41030040356942d40c401c0c2c00400307140710420040d501e400b0341820039003a9241102c00d9071a8950358880c1c0f60581004000040002c0b2050365418458200c20054079245d60020b1807256004828a4100000056010306803e1025a42807000030303400d01040c11098100c806030090300c207600400128007020400400040c690050040c0410182903400c21b80e03160b054100444101c55070401c500d15205c41011b0582d203004d00e00008140403403c2606100000b0300840000c1d40381d100c4021030341640c40b251508050b4440340c50708078500400d00d00440104150030002c60301c4201098920810708400c5450711800c5000c11b010381001d81d600000d00b02c1917542c45a680c01c000d9500101451081a51340404940000390024226176000704040020707520001031080501c203079081070942d1219025000c3c081a1007030001c004036407056580f43c40201e2a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 983734343 1250 983733093 983733193
    0xc09010302061e190e03070e0601200c120706020c04051909020102030d02130e0c0a081603061703030a0605100903060c121a04050c09150f0f0706020904050609010602 73
    0x10001e49605020440080031b141c101881a040301e400f1400c0c4c44288411640d00c6100307030201d040c8201180f5040000c0c50045801d26111012090f03108001040c902075074480442d1060803111a502101c40c400e140b5000d00050b0b9100b240d1030801c80201c5064515141030640103082e540d807051040d0391528042070328400482e005407000542007030075a8001d000304103194881541000011000b182040c441c07030f0000b011400c00814070090310181c441c071117500c01d000ea04010090800c081c864680302c4680c0c2d8009070ba030340080710382d001001e0400400040c41d0a00c0c01c0320a01160f155960300032060b0443d25003030f014044000c0a181000715480303072107003c00035034801d1402a4583c02e4a02951020301e03800c00003511b00250400742400020020300d4069a284140d0b550880e5a54901c20b494292440b001e83da54001e600c54070091140001b440e02c00c00c03080e64014502082d0864041100707454540900c4080d840074022100964418860000c10144801d41e90421501615000a0008004440030307401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 983735593 1250 983734343 983734387
    0x160209040c0503010f0e0c0f060409021c0c030b030d051c0606050a080619060e0307030b092a010906050c120a0e1807021e010605030d0f020c09010302061e 68
    0x501c500d400c00b402036160038042c9103940702046000380080750a014485407a040c031850703840d200d0080002d1a040a4031420309a0b00141891882103440e81040640b0794440e1070507400380311031246000004050704c2d00031b01c690100d15102500074800000242029911584501524114200080c0e80c9041e00c030030314040c1001500440e40c401d030701c0340109580502154340140400d84903003140010100e40f6001403200c0001c460580c035107982100c000a020a00301902600050001000700c41008083c100000740700c0c890b0900c0d218004000c60403051020140c2003000746e041d0005045440c20401580700700d02070301010b59810151403400d200400c004040758004035100f00403685035200305605140c05da40d000c854a0041103002058070306035900a440784000d202c64105145d94009560785044258014405894043c00300c4002044601000c2c1c44001d02c6d1240c54014800d416409070641080c0c90a00e041f40c0c1d010303140a0030400c1d2454a4000380740580490800b18909100031009a15890801c80784 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 983736843 1250 983735593 983735603
    0x31506030819021b1302090402070b0405010b010207062a110d030324050f01051b071409091507050f0d06030f14070e060405041e0606090c140f16020904 67
    0x10910015006400c01030342d01c000d85001e611081504c58a52a139164110807842100c40c0103a0b55242640000d00030301800001420302e80d454000c0200700f0005620024101009130200e1b40c04994402044401076940d103901008025000f00e813a40d244100050001000d00c01c0010f800721030244c4010514010200c001a80026202c040d0000c90b00c09a01d4549224078014070f410003007a0601000c074202ca000765139a00c0c1000400541440014005104220007011481c251500c2503030740c0b500040c1c1400000d17200703403144000c580030501b0b50400181c000304011041c444c0d54410366440340203440c035401c224200c070000c500c100010700c1c10b00e605100c1c11014501c2078100ca450084141803148000030400540900c9a11035001844043d042022040d404401103601040320b5907285489109503070f1468055034014074413805070b010000716412910540e036000200701321015a07404225100140602106c401e00e0040110380c481e40c500d032000b0001060b10b4143c1003070076201d590124040e06011a01070390 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 983738093 1250 983736843 983736877
    0x15030d0215010f0803030c1308064b0720031b010603030c060207020f0901090b090609010b041e0f0609030312060509011206110d061403030f040315060308 68
    0x745444042040d2809441401c0d402d01d2881d0038030355407a9491001418030002000045014418100208440d0340a080c1540a6420904100300700340450034960000d8528020400c15030180c9032203c20010b40c0d071040a103166090001343e0220002c1c056405800c1e41c0c1040702500005042d02d48622102c0c01000d0741c00011541c403489000d15500402c4201302c1900664140001007000c20780c0603a041000320b401002c0141d807400244000398010740284099600000c050000081c401d250340d115040329041503400090300c2c2d0b508420402c2c065400d00407151300d01018442032040c00846060901e299509901205401c0e40315030303800084030351581c002d000040001a05008050f4413072031000351000f0400c2d003880318605100c0020072100701406400240b10078883c0781c40a00c6056000480302c05280d41a071941c503248009440040c15007402510500c02c032101d401009800d0010854094a15030182181898103650301c0314402680c002e20300310f1a60303c030100440814500c0d00240302c9101e1802c2c0c069 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 983739343 1250 983738093 983738113
    0x100506090402210c0a12020102060a0c0203091909090c03211b0204020d05040c050a0602070f05010f02030d0903350c030403140a02070311061c0b0103151e2c15030d02 73
    0x92824400901d00c01005033840c070401c1c152900001a07513950402101c9996603404001c030322100000481e130041140304c4c2041261303070902c52900c0b02c02090340c1c01440d20301210844407042c0355070368142000600c0020043d940480081e140160700900c42480108050b203440c0c94941d40c2720070350740c0c103450640f08200e003041c0c02c02040c980500054020032590018000b250328144103801e10207503610881d41440705250052100c14428011140d9100044000f040420082e0500400c144034402c10141e8004000788809059400c3c0c8824444840e0031086400b43c0c4c2d0388031110302c030740d42d00701500403814001e8003c1074007141d190001c05040074100c90707401010020b1460600072686003098003010300904007001448424068184240e0841122100104180300c1107c0101c0040020001c0c3c4ca066900c2d80501051900c0c008111f49410315502c842c042d04a900e441024250107101700411615110105051603a0903580040581c0072b0f960300042941c091007a800301e4103006100440500580103d1400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 983740593 1250 983739343 983739347
    0x1b080d052205060105060f0d0f090203070902090d11220c080f160c051c05040f0504051311011e08102403050a02130305100506090402210c0a120201 65
    0x680000641101e501084a50302e8940039100c0d44180600303401000002402e10003600c6443c100c03030028074016800c03c809081300390100000c00421000302e21a000300000042d0752240d42c025100000c00c010220152907800765580124480300c2402640c22003804a804a000041c0300401c2d0112006000049038404141c10000c2400c40018004220b01c48030405100320a100440d9002907103905007012000e030841410101d26200388040810b001e82d1107a9060300350641c0c000080d2044908003900c99000d240c65000308802d90b00101c0d00074031082030000c054804240e04010504090303006050602c96204000880051544081240c80210314902d05006100040341d9483c0d000380788240c5001c2407050348091517540c51041100303240406d500d5501040c031700140380d070440340c1030003000300c1d503401c141e41d617240c0740e6100d14084010611807880c1400080c0a820030080e01172045500810408821643c02e580d50013080c2c08641d030303410fa84a81c03100c1c4100c5443e05c14003900909028001200005194400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 983741843 1250 983740593 983740621
    0x506040e01110a031b05030c0c1c1709070821040312030911040c05030a1505060705060f09190303091e060501090608120910230301092403031b080d05 66
    0x1001c036007070b9094104007403174903030100581350450040c809031603441290715065480c0c58403070382d80d40a864451242c03183d01280c228440d12500d01a081c001070f080d580700006151100251b10864500d600b00c48100c140b20946003201c03d00d10402c841d040d6080035100d464070710920101d2400301c0c011075623929400060258103040802c40030b40072182400f1218003c0c1e0700500e140406800c02d4801600c503100c03140a5190f501d80c00c0090071025010340e898801500380741c1e946007000e0702c003000440540004204980340219440c0c4501825516840c00c440413950120010034103940c040d5254448006060444044084081140c90040001241c40d504081035402101d00e0380c9c0c08a0016400341c805206d0710b15441c07046c1c400b5008104e803004072002d413806095030490800080100405503030420003483e003100101440c1a1030003400704001e80c400440100f03e03031036202104043d40c0c81c0e81d2481000007903c605010007010394440c0c4a050301d81000c2d81ea888803170f00801d548021a988403c10440600c01b8034003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 983743093 1250 983741843 983741861
    0x160906211a0a0608030d1d190b10080a060c1e0e09060301090f0303020a02010b0105070f060c02070f061d01081003030f030b100c0210090f090506040e01110a03 70
    0xc1000c40180e05a880c04558040900100364074440d050002d00c41c58010b0f070200008000301816255907400340303444c00c4020071138028620038200c009550b00314251800285200d4114025240010210003a21010100c060041a220780c5400c4d1442c0852114402d0100700a041d2180300080342c04440d082010300300c5041c4c401d000740c01500c074002d150303940f51b40051381c0a603520341524151401c0c3c460b00d01080c0907000115014040f081c02039003c8c0105507142d4024641e5444c2030f070081200c805c0c007000459140c426503402402c0d01480c3e0700c8034400301c1c00e81e07482100ca1010f2801240d45907035565030091140c54242e4410804643c0094114044100c0f08043c0718a00200740b074813102c60714001d8614854184a03000240c00c1100da5500101e00600980c4030000307100780108403461031144414014410501c19004a000e4254506404030030340c02002c0020603144a500b450408a04000020004220040c111031f07215454240c0703852048020310a070709a010082d0300302592294400e90190130f03554441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 983744343 1250 983743093 983743139
    0x20a06080a1406010e190b2107021b01030506040e190b0a020306060a080a0b0604180b1005090409050c09010f0f06090302030705102001050105120f0a080705160906 72
    0x700700111a07038442c8006030300b0403044403010a00104100000311461b401e4108441ca08800900c450007000d00346805155260301c45c4003100b07144d03600700e0200d03149d14412081040c400503400b0101220340c041d070410b81e805280900005090708000f030a01313180619404c44041c03003c6c0060b4407101480700b0101540c2d40941203010a528604000300480c146203e001c00c42c008000090002c2003082c02d040e0028240c00100030300d403503240c40e12010040c030384c0c0440c0220555000d10f0039103140300b00d09060138608003a21550f01d82030305116103041400b014014040003254140202048440695242e500103400780010b203074031001d414103000300c0754490080340d00031308184204c01c801080180e500060200544030309980c240b02d040920102680d16000380d200d000c07044904150080c503420300560011381225002c43d91000c5a0710710f035280ca6118888400e46070500e4016040e001c000c103411800900d842031051040f500b040c442481d201480c20440e0300a014a5a1900410090411010081884a1595 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 983745593 1250 983744343 983744381
    0x40b010309021315080703030509090108013605030705030306090f01121205091c0314251a0403020d0f031b0f02030f0708070b010b0406020318040603020a06080a 71
    0x607000226060380c1035914210311a203406804c408107010441ca84028003000b021900c0568823460003602c15000b1400e0b040c00b40800400000d00d2010500031080c2c0901d00f04c5841e0722018502401c07015007013070368108040500c25450035070005030040004107038407400f90029503240c2c01c0440030080c4140d0090140c80c0c0d003194450050201824112040c1c0e4610760000780c500b0002d04c0c446044e1418050308070510390044003050100d00192510394002e01c6180300b0360b60414941302d4041010601d008510001d051a043e03402103c0c0f682061400710180a801410a0403c0c1d2082c400346103a102411582180180c004440c1c401d40141c2001221110100c00c0c01c1c103000c201a541e1004a110005500340e100300100c105800400900030b0044650712102d030340078540e49500e0b600b070050b19070740880300460b0809440c0c000001d64802c02c90980d0305980702c0f0382c007440c0741505c052031a4041c134007039410050b4441e50340d440000059030b6985005005143c3c50300c60500528000d0558812a401c2122030105041e034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 983746843 1250 983745593 983745611
    0x80307020121090803131416121502070c080f151303090f173d140f09060610021c020709020f1317070911090307090b040b0103 56
    0xe000a45015a18900d66a02010460380b101600c009070700078000440020600c40111004402040001d0140c0107629801001c074030203542d03521410b0750f003030f009030000b060a00c44a030703843e034000010074010500381f40551000c035402d100b20381c860181103c200d0401e0384200945079041c80341c1000e4088103400b415120140100b800d601000090124103020700000c6010304045c05040907401400c0d154001080454441c030780100074541c0ea10612015201c0d03070850400039061100c0e80701c5802d040e4120010320b10100a103144030781803161a424a1b075a150034103000144881c000c1141308050b48040150716080840c051820440d003e00580d001e507120744000b02c5101c1d000a411750702c10b54001d908040d0709020400880c1000899045420720754000100e50f5581c1e490840948480110044070103a2a81d41c1c415001510100018400e2650010740c03041000713480300d601028146030141d440030303e400c030910003390030800750b03800501d421030781d400ba07250701e03070400b40b0800e1031008080c00d0401141903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 983748093 1250 983746843 983746847
    0x111010c12020d0e014b0b01111002031e04021f1b110f09250e03060703060905160c0f0c0e010b0702010201050a06060c0f29100803070201 61
    0x1d915850300340d00c00d0b0001003060a03074441d41e101e2808010414020460146c84100d00a20920b0390305202c3c40c011101004801085404659005035100e02e8003088011001080a2000f401c0d0842e030490510403a0341055050144c01d1011100201d41c0d44401a5280790585954202d20460081c0c40f8004403841c0c01c100c0161200c4038900400794041c1441010188520411a200d40d814550f80b11601410302c082401c1201c030529005121104641c41c01c5084055410700110000407164002004810602c04400742003050a285e5541018906250000b400030301082ca00f810039600c03d80080d6035500300f00005a804c2c81440d401486601c1101c10410011a000b00540010540601207880c503101e208104101802032000510080250021a41c0c6d502c28844d5250400318003a400f40d420480010301860561142074141d4440b51101382c2646210307114800504070305030049810344200c8685200b0000808084826083c552a111a20346403240310324058030070903800b400307280c1e006000b0000103070303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 983749343 1250 983748093 983748107
    0xc081b06070b27030d0501090203040503041403030d0e0303180f0a0305030613050403081806010f1e090e010e07050411040506030405010b09010308031501080103080f0f090a090207020111010c 84
    0x394029501c001ca58407200c1c0c04108040c4000003101010003660198002c610000c4040c0c001e50b8080d610800c807d070b90300c40d40981648000c581c02007003a0002c00c0240101c03402c0c443d040c5003400000d42102d0030802c414045000b1124030300b40e81d400b95440070042103414286182d02100c0d81c1c1700c04019241000400d0900380d0b03104200f94005060000200000300a0745581c0d041c40036000b480c40040c80700e030400d41000341408000383c2d035100e44144890780c00c0d80d000b480040c1550482e6424484100c2c00e52800124400081a010602d5488031900340c002580340d41c1402b6801400f00000c0000400c1c3c0c00c94280d042c58202284d11143c00740d400d10080749030121489040d601281c000703035080355a0765200d28043e40100b070809405c039408400c0c4030012080c0103005001e103110300000303001450881c06a000640d907000c400d2000600c801c1c0b0402100345250242c0300a484224120f64145040c404505c0000d0b14548242d08a02025940400c1c0c071015580d00c107051410f00313540078008005044103c58014086 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 983750593 1250 983749343 983749357
    0xc110a05130c11010609290904020d030c0609061e1b0f21020301050a0b070b0412050d05010825060e0f28050406140f0f150301030c081b06 61
    0x3aa54a0190000c10b6008103100600d110088000300241780d1280007803401071451400340310f119000740100420103004840c0e000803901000b45110764a58507035017003103443c00e00201e00301e040040d098900c80c009110360040b820010b1007040d02042c07524070280710400e1007074032041d244042030601600812600d0803000d41c1da5242d10a1520303040796000b50078203541e4407040483c2e1a880c03a030903959600c0505004c2c2c3c00365051320b80c100e03200b00d200340d5203c0b00c0b60540c4c094560090485c0172504045000100c05443e034140003105400d10a04004440440c0001c8030780036844038619070080691846d9141c0e51184003454020b8410800a5540c00c00b40b000f4001c00c080b01203103004200748030300303400103503203600c07480c50303080d010402d0500190340c3c2c030b00994140c4186104450256040c003601145052600c1030384081a10080c0548054117502c400b000800c401554140341c002c0c07064103004a286d20b400f0700840c041d60103910890071071032811420701e141c00c0c80d130100d0005074040540c080400c0c4d95260115451 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 983751843 1250 983750593 983750629
    0x51b060a0e0f241c0e03090d1115220e0711010621030e01021b0f060702041805061f0e1e0901090506010e13080309010905030a0c110a05 60
    0x14030300d482c40225040e8a030011880104002d940342c0d115814040c4801841145502c00c07a00c80101c0c90385040a00355140298007180542041c400c00d801d5080c1a4004001c09024241e074041d0794203102c000c191025165400c2c801a403074000380d00c9000640300c000d4140f00b000a140d6149a1618100320351f901c5200152000c0c081242000c104040324400b50009030151180c200d5030300b9907045108101c20b4802486000b02c01080302d85043d082d040d03002258601032405000564450b00d013a09040006e20700007440300c40d0740041300f845800096161441040b0030071000b4131844d050041c003030400c40d140180007049581c154254510101c00081c00c0540c4900300d80144020074411b48500e901e003800b00814003807518800e010102080302d0140c0540100805601944c19584982d89524469800801c201d4907081e45d04041d011280005039207000855200c035060b030001804119513a101411544854044000540c0c2442c0075000e118202400102e003003c12a80c44480901d0708002c21042d0250f400c103855 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 983753093 1250 983751843 983751859
    0x513050303010527150f01020a05030a0c15060f05090a02030c09060d020d090b0105041a061603091208030411060702090c030601030e030708070309050607050c0d150207051b060a0e 79
    0x280302d2844d001e00c0000451107546101d0340c0c0c900340c4019101400c15004040c810501c50448411650001c22900b0400750043c018625220b001c03981610000c0c0101400c41c0c2d5500e0b0704488042c02041c4e80b169101820620610340c1c02113161004108045001805c250101303807040090010b80e46d9104100d80b45200c0603204079460700c0420440034020700906d900d4a0b940760401c2c00e0f403c108510103c8003810b80d40c00f120200010000100e98614107176801c40d203da0041344c10020301030076040710b030324240c00944070340703054801961540803085091034004d0007100c0c0080c001c0f060008000030400d4803040b61000b61403490401c0c0707241d000180381d0a406000341c3c00c2c44100001207540c69200741c0010700c095000108580d520219454594034a5201e0082a00041c80d1800041040d180440840308416000300c014402c10031144101709070b0349441c40c800c4403541040b00e080c3d5181140750014092560050003d41030f860b028190603000c91210008441c8540d0b02003108000942e000386100544100a4480d10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 983754343 1250 983753093 983753119
    0x5180415031505072714210a0c1401020a0b0402031614030f0c09191b0e01020609012c0a170711010207050112053705130503030105 58
    0xe00380d554201a101c03840b86200520104581d0708414001c111076511780350320780b0543e90140c228450300d0b440c80e5000d0800030002c00c004920321051140840c0000c100d400700030f9002c00c0d0400640c4100103000302c0d98000c01d50310401c0c401101406402004802504803008030480c00003502e8090010004252907020303408a0f05640702041311034034000c0a41068001d00e601c60b41070030506080a10480d2080c8103445d0301028540000c40c4107414280b002d0001480c540b01c1402e0740001810207010010480d0359501907021440714640942440304c6075840d4241c3e06120440024103018008095a01c20380c10002c409541040c440200315041134581e68424a10040c0d120807414490150b002900c03079519000721a14080c140002401c000c0d1203803082c0803510126200680e104c86240c421035021a08803164203405a04c1c81d0000b41d031280a210882001d041814003100ca0081d07401340340415002160304c4174041603c0f038491030b038001078401c104480c990202d0742d880f648d920050003558000c5080800c10303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 983755593 1250 983754343 983754371
    0x110402041a07031710030c0b070807030f02030d06180518030d0e150c130e040f030c03020109020d210804020d1e08030108010b040b0402090918030c0f070602070501051804 75
    0xa141303181851014805030614009100510a01d030005590344005402c2c0060503802250454501e254440e00e160309028043c6c034140d410800c004416000d4ac00100300c201c0c0301192a02c070b00e0014010351818509020b40b42c500400844400800a0446101c10007184940c40d400206880c011640a54085002020600100d04002c090290380310040d0070301050003d10f10410002e481500041401103030b1003980c400d0790350041c88040d64040d00e441c40200250000c64070400f807803600c4501a00000c5125410340e4040740781d420128000351152807000c2c40a9140f02001c0e0380815280c40d035850410b0050400f074000171300440d4004001400c41d804004c401800c1c12441c044514565003000c2025120b603034500100313000e0809101d489106500c4c0054001c42450300780300382d409415020300080c00b40e0b5646078058a050164100760115880140034580d021002044038140a03403965000c0c0c8200c43c0b9120b0701900d0800707150041c5050190901c00c0c0840000100c403140f6403004211008100c05140a0759 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 983756843 1250 983755593 983755607
    0x1c05181302071407081603030c1b121109090c0a0905040303140a0e06070302120f060f03030d02130608090a0b131e02012316080c060112110402041a0703 67
    0x103000c03d08400b0381c1c482c11480400c1d1001111540c405441400c40300240c07500c032401032408018040b0f09001906408200341840705c08038a40001c04000c00103455920b0b000c0c241d800a00d00b02c0354413007605c1011205040c04100d0760381102646000340b62443c01d0340c002030200c40840c0141c4803016540c034005010706201c0d4000b0a622010426505914202100e1010203020410b800124a114480c0400c403c3ca100344200d41c11741440c41566103594071040d42c2c905140e0406401381c0c3e4802c000ca26170b2000c6a90600052820070032034080181e0320b946090001410350745590100050200d03810400c58810408070382610300c164080847c21555403244210100640c90820103005801d09040344c4c03130788010351110140018000d0b224501403078284480c0c82e0b10160100308003034041030300380030345002c40410307494000007603201c0c00d4902e0400c802000118a0040f003640540000c045100742101800080c0c600665401400d4400350300e0142802e421074200040c41002d201e01000c0000c1c02c1e004d062003000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 983758093 1250 983756843 983756857
    0x909061803080a140c0d0f141801050a05070c080304050111040e0106021506010f0e010201110f040f1a1204051911040e01060e2d01081c05181302 64
    0xe100400c15241e0900501000c4111840320450340b03030400c0c3d542210030740350f25103110307084103030009180013108064000a0400064001e0200d500c0301e03002404032981c03510302031081da00c000f4001900c0b00a42e14590a6a0028000949151500003407203031550b8484080642d040c0c22822a5a072607d551814a00600007080c2403081408081804100701c0700b03d8400034103d62096003111780140c0100c605000610303040d580d06010921220709251502d00980c3c800e0040e0344c05000000303041561000c102c1071070b40001c46402502c40300090600032a00d0107161076000d0040300a03000080400148441c03414801d0283d00c8040300681d40024080043c1000840410086e4071151495910640341c1f02c03001d02c1407051928812800c294443e8220401403003240101e407500382040c000754072450b0444500c40b042d80860f0403058001032542c0c007000844010580203181201c01098040c0c03510040c001c030286404441c50410504108503000f004a2060404100100b1101002040e041030000380003881094 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 983759343 1250 983758093 983758121
    0x60409020a020105070f020f06190209091009060b0a0e060906040302030a0609120c0503180d080a0c03030f0b030303190b21060705120c0c071205030d0b040510090906 73
    0xd0807a0000d41c103402050207050305489904000c0d00c104400d03600e44030401c200032025807101c00094403840b404040c3c0309030003c20403801407030810708401050b90f5080c01c8919410301c5070808001c100d83c40061140e4001402854103a900b00058042d00030003032100581490310504000c00c144070b844c0d4400702210003c560060071165510040d140001c00750000500540c0c003088a81104003815014141c009491760348600610b14045400c008409200c10b4140c0140e08128411000c100182002006082500450720b54603050300d600c0ca401415140da100c0c03081c00c200c0c1400084401505c0c0081641c2d04252440c1401044007400c0560600601110308100d51215a41b40310303c03144465800c9502040c0150000d80720321359188001035a06218000c001040302403030100003503010b02d403031000e46072034104581910304040da0352124407110214100700740c855410000b460030790f920540c8160b1303140100544081c0506e2a00d400c0013603050380320380300e1144520b0b2101c240c1420884103612141c0751031030310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 983760593 1250 983759343 983759347
    0x60f08210301060c031812050c0109060e0105070c0e010803030a0f020901090e060312180a0806100302010c0c0f03030333051c080a0207061202030f16030e0609010f2d05040206040902 80
    0xfa07140952190440c0b50107035090b022748240080ca43d40329880d101c0655402c0d8030b8400c14449200e004480c9170b404014140c4094500c003c012642240d1a04102d00800b4018025034503410900040030440b0401d2114140c254810841040c0ea66000010300b41101ca030840511000c1c0d0e11600440d060580300c29004190000c002006045008031604492002d10103503554210070f40c84a1a05560342e0b000c1c0d07a40750601c40120000c00c01588030b0717113044101c944034805040101e9034403614103e48200c550000c4000c691624180c00c0340d003a0481e01420284203c0d96070281c0c000007000d028408003014000d190050105a0098101c800c180300030480144c0c0c400081c2e5a0780016010094941040c1d000380c03400a0880303410009031080c90700a80f401103144404400c3c4584845e1b01040090143c2110b503428191280c04421446070240b028034810240880042244d021480645007102d24154441421144800e0a100e0214410180745403c401d031040c001342d561154000641940500d0344102071483c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 983761843 1250 983760593 983760599
    0x2011407050c12041802090604080a030314330409170c01050601050c0304060e151303020f030d1407050c0904050114060f010f1d04060f08210301060c0318 68
    0x8030034000e2003810070000030f0760101c442503260041c007882035100b54080440e030b8442e9040f40310b44903030060020080042800786496a40d4021504085400d0015070200342d4403030700603000181c40314009600c80c01d0000004400b00302e4240c2a44400c0c1c2640207201012160401c41c0c00e076071255400f80b542d9641003540e02030000c80914000401c6d9004a0340d41c03100e5401e00021821550090003501d00c440d0461000c0d506140c10000100c50955621150702c0d1700c06800f084080c000150040180b003081100b10000300d40ba41140148030303a1301520880b05000e94070102c248100954032691002c0c0d1080b103450340c1640d41c0d140d0f081003441c0c02c640c1c004260b404500001840200103055200646403512030062004035902c0c141000202400c9548042c04601c2014407050042e200f4400b91030000380030340d0004281e07441030022508440f20750700000b02690952a080c4090041040480c1d041118100c043c51814251005018140018840c000a00c1005860b090416000e140344808110062026815a0355 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 983763093 1250 983761843 983761847
    0x70f050c0a0e100510091a07020d050c040c02060709170f0f060f10030f03030c03090c0b04170a0f170f0d020711011d0121050412020d08010807060f02011407 69
    0xd01030350f2411004018180c0060307a41840c403584c81800c803082d207800d10402d00c0c142000c00e08407644519240c694104000c0c1c0c00041e961542c00c4400280907a0003000440302003001e01048030f503c1d207072071029503100c00e0411a00300e134000e040c041a1105044084148030a100c0040d207003407500d401c1e1003040d0040756500c040036540040c0745072203040c10744540c0c07050703480340034031a1940500c13804054a403a640a0b81d00300442d0090300007191198440c0b90008002441d5280e00c0c0a14540303400080c00300c00300240801101c11403040c02402d280c19000030b013094007600e564140a6a0100c24000c09210501c0318402400100408bd10804001049016610007900f2074130002075000d45c208440408200d4007040c0d59500c21003280b014120b100b16032a526140c1c5c0d10064486d00d2101d1021401180d5104040d600c4c1d000600ee82400380c1d22402c2281104814070102170700782074a2007031150400c40f0040040240f240009410f0007100c000781001c08401c20303c3e004c224054041542010811707a009400d21181c00d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 983764343 1250 983763093 983763119
    0x503060102120f0a08090307141f0b03070303230301090c2c151c09030801050907080703090309030b070e030d032a05040305070e010801050f060303070f050c0a 70
    0x260903400c1d9410031420304085180350150780f0100e0b8440e030090104007203030f5000d10b41c500d40148541e0105ca040c03100c141d90388000100e16001c03613409900990810f17031501d5401c0b003400b081c003c05400c0c18080c0d4145100030035654425880701808000010941041101110362907515000540d4002540d0b0342e1105c4103030006c0e180c6219098005504088500c071043c0c40703420f040d80e540c805030401d0448803902030100450341c5040c2c00c030008080000c0180301c0c903145000e0420b5001a44c3c5101c0400ca0680380e007406440380905038070090240e40920100400280d00c141c0480e480503075401e00095079019802d04903480e07011a08014201b84070ba03014054802c0e007103081511030440880464411041542c003c40031b54954203030420107001d44c400c44441214018040c04c6280c0502d00d800790906036a515001c1c81c140c000c0d070080c24204031840050144c04000e00906600454034a03881c80107080920111ba5284558200541110390b072803020307410071000303010300f6000240091280340c6803a29016908950 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 983765593 1250 983764343 983764351
    0x270d021908221406090d170c2a15070605040309031202010b1201201c140a0c05090a0902031807090213140108070f12090c05040e01060311040e0a120503 67
    0x7168243e80c0c500c0a5140c44800ca400301e00010300050941c4401d9034400a0645907c2c000c0401c1c4007017802150b440349410001c1c04000c4070b8582c20029807000304482c440c1500580e401442c002c00e91207221610078550722040f0ba461661001c0002080c0e0b0713413030a00b1200c200c1240c000812680b40074140c40e911560540101e10141c2c811079450b480c03040680409822680840c1702d8500100030740c144000b0785082000038100e01c03143e100c1060300600550010004962404c0c00d02602050303040180140c0104d280f1421044189608049146c2041040000c0c6148802d00c00e9954444d000000100c010301071140441c5032006103800c4590304c0c3e4655000e0300c003940251602c03800e03040790114000384210b6000309400b004041a100c5184585800c0d100300d41c01009078171643e00740b0070030780c500a01c2a401c0d80300300140d07a80184c46000c0d402e03040c4400c220030b50b17200240c0d0640d56814090306101040381c0c0b92a1084200c811240000d40c00c0c076140c0414200240d43c1d5001d4070005004070310f420a03a81160055110b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 983766843 1250 983765593 983765609
    0x12050408010c0305010f23100c03170f06270a0c0e0a03020f10110a0803070f080f06120c030a0c030b0112080702060702120303270d02190822 62
    0x82e910644210201d4100340704404500041e19810080d180601b43d085241600072600385030609900313008280410420b0f1052400503410002c00d009166000000307001807649019803000380c0c100075869440f42c61000e02101e04c1980c191701c080b0510110160710801c0c1c244034912111044c50296115002003403c1d0350400c01242d9000b0b040c08162510036008411740e68018042030040c6807180502c4262403407111458240700707003106065980d203010000204041e20551b401940c0c1e00d07007110010086a00045406d0600c00c02e0b90502ca0742d143d400c1441548841700341d5100c4680c2d401090f003240b6112015200c240c05008034801441440b2001c0001003e907406204041d1043e681ca00128500400880c0042c007590410711070b100c0107250440040c5065030004020b582c082d144134102a003183d0007075407945c0b503900081c110800c01e84c078891511415080003601905000054141c003a40394070492000d0807843c0c0e078200c0d0400411683d1000c3c3c1d201018000715a28603a089000b50306e1503140d040c02a008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 983768093 1250 983766843 983766851
    0x30f1f1112041439120f0d0e04020324060d18060e0303130602130b04061707021f150b0c0322050105090f030705060c0a1a2802071205040801 62
    0x56444005800b0444d19480840405100ca054440d4030025400240c8960703100d44151442c0d60715000c200000c0400103580e902500c070a81208078040c20009050301414002c50041c010080c05106502d1b150144000256402d5a144214000110340d032142060201c071240ca0110f680002c441c041d4410102c0510480c03041180e07440401546a581c082203030255084292480c0544c0003d41d10b8020b4402c201c007040e8401c40d4903443e040341108a1b0405d41004000038010801d42000f1503c502d0199000680c40c0058040e0081c6401c14008031316280e000103004d5920345005000081c00c0442072030042404c01e0b500750b1a090044001e0340c681d400700ca5070f00e148030f0480340058031481d1203414500407035034140c441e680350001d000c007440241d042e0304040750f516018841c40001c654a503200200919018031001d445e11000c1032508000084204503044010740c992020040f00b000b0b901d80d56400c00303a40c030240101403000c8095030f00c060322a4400080c0303070f401d0826903643c10680007c00307003040d00c240c03000a02c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 983769343 1250 983768093 983768113
    0x3031b07080609030a0f0207051005030f060a0503060a0b130e03040302010207081603200a032102060903160512040e010e01080a0c060305090705090f06030f1f11120414 74
    0xc0c1c0d0b00e5400b81c42c000d681c2d03003003044900c004501400350a048074449005450000d665140000e070120ac15003a0701000c05d00c0001000b0340c52609151583e400340c000c03074010204a04200100fa520b00000f01640710082d03a8201c015800d55031580d082241502444003030001c101980308060300c94002e480103d02500c036088010401d45004a00d000c007000700b51040d2209145151030301c5840580610b00f0101d0140c001020b0255a210441c00c500a58004c3c0e00102941145080024605049125010454000c6020301c00c40c10008000c0310b0038080c00309050402c841803400e2030350034081e2490300c0313160280002900141c4e091840c0c850f203048501941c040c0906aa07103400311030701e80580020080a08500345020310080b402070780130a0308090090100e4800c90b40320030102d15440425129019050142002c22405182c1049190700005204020b4525400c410f03601d20b42c0340c0c910f0000840450b0b16220b04940c0f158404042c0c68900340840c10381403641c1454144001e44404c03c0300d1900316405a44e442e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 983770593 1250 983769343 983769359
    0x90f06051008060402011404080d1e0e0901030809030c060703020a120e060d051b160203010b0a0e0c03072d02010c0e0d112106220f080a030b03031b07 66
    0x103071045036640c0700a0038407599a5401110701c3d0f14901e0080b6000142844041010442000580103107103040d21801442c803500d07201c448074407002503a001d0800c61101100307030740f5446240c03a01e07046951000c00d082c0c81d00e80d1080000e08050229035581c2e00400042a05d505155001841c800c003a40912000103100c690031108461514188501e580c0001d41040301c600c06d040c051740000d5000140d001c003c07940c06551445045540c0c005000b140f495080810b115081d441d083c421070280d0401150703112021450489010354a04c40208803506140000c000246150b001c1d83d0440e01c603000d0404403040720740d40103005051081b8103041c4c0c4c5006611703006111038543c1c0925040115810003c0c80e2045034600f503a101403807100108100c41c2c1090a8600120004c803100e0441c0d198070b264440038103c030b840d0030961040091100d134030210fa041680549840441d0390420142492a000340e1820395909290f001030b00075120300410701c0e40521000070781c040c81402507075200d907440d078042058070420f642c0d1b9000303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 983771843 1250 983770593 983770621
    0xa0e04050d0e0603060906010e03010b040c050d1103060109030f031116080f01050408030c0912072c130807081e0a030f090c1509120507180c020c040f020d090f0605 72
    0x8172503007203604140403d4003907004019402140000400204070b528a4001041c00d0310006682240030a0011075800341010050142e140c1c861030181c002e50071482e1200c0006d106101901c40900031002c0b02c1480801d1601c100e10414009203410700b280c803106450001c220701305038140b0a03c80940519090030214040600489006a422140240c119107800c41c500203140e10095099901c000400020040400103020348801050303400d244000c6229000c084000065214802c910803109001c02c02007076980003d600300407107801030592034491b40549089125403251702c010300c0088040d807551009044001d0020f041d0010560340502240b160110906c2c291412046c0c000c040049000c820321440b502d611803045045030314908401c0040e41d400c0140890351010000341c4094010b02f10074081e94041c0b0b41071035444001850304025088110034025100e8060354100c500c2991510840c030782c801c4098058909019191302c08000e416403070718241c0700141c11618116071072400e0000107581007401d003503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 983773093 1250 983771843 983771851
    0x4260307030207061d0a17070815010e0a060503030304150606020a02090a18020915011824031506080a050106180308030c070c03030c020a0b0c0312060a0e04050d0e0603 74
    0x108543d50400c081030b20482e5010ba00995407080f003100d94119613a41c0303c0d0705e40051880a030610710041800d0951401c01c0c410b80c004107540d03800007601c100d0224038101480d04680c3d4403000c0040c01e4951b031800c4da028103041e9002d260715100100500c0284a9801015012040e00d10400c105865803a0003d03626159001d00180d80a080c98001607a5482d154000150340540841030b25101161381c1d0024a140000781d40c02100783c2c0d0f2100007030340305503086086912406a0901981c103082e10304507003808000a8240441094440c1e54810080c05009801c401d050702c056003841f091441e1240c0e0010211101102c180031803904100c0001001c80c010320315014541c00d005900d9244608503152940158800741a803030a6101c00c1207a10b0101d10320110714400745100f659142902c441e64010007142c2d28050304038031b01e00601007082014280f00007080b41c0d10501441d0300b9000c140d44081c0026030054450f0300007882140d80b01c041100b008070204600e2070b114076030b03228480e4485000d0240442e5000072a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 983774343 1250 983773093 983773097
    0x91202060907080d2c031e0d0e060a031d0d0f02061b040b031b16050105090d390c051507120c140d080141030a05030426030703 56
    0x190003103e0300e4205a030a03e079070b81840794002100c860640881d14000821000000b20003001e2a0303580b07c00824400c81c1031005503880c08154400c4000c00140e0b0501c07030081180e090644d5003551142c400101c059030880500300f0380550700c1031140c8840c0580030000120020005002e8800040e0b217201518008415820804100d28103143c1000f810802c55031025080c120b030700a2700444034810301c090000030310701e04030303103110001044210f480c0190945402400300c00d599000308500c440300ca54005903840311154190042440c0d4181102c480100c902074161441c0825100c804800600c2508000c003012a442030b20312544106611244092902541500400d010f00006d824081944103c1c0e8544c0a180190080c440b107a8200c8101450000c0e030001400104043c880100032a610b01c190102e441d90600c03400c220b032180c00111a501407084095900710344a86801c43c2d02c42510700700202c003451940b0508417a905e41e00da5018011040c0190095401c1202a02544241c941e000c026150600c0d49a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 983775593 1250 983774343 983774357
    0x190513080304050f03130f12022d030102030a0617071a030c2101090f0908090d0f020a09140601050a050a112e0b03030a0c1203091202060907080d 64
    0x3a600d8840c907500180042e2803520500b190b07142c0f6410309000a02000c40441e48506a0300d19010f24249001019441410b0380700d010b091a20140c1c990000c03203103500e031140702d80c00b5201740745100703548040d0100541d043d0035600c0072003040000b51255000200f41d031a99800305c8083e18440c207406580b0b240c02d019008042c3c001e141d4200b14080f0340b20145402003042d110040c00d05009658056548004529100c641403081c001000900a1072107010415010044184000007040c1c40300400f074070030314030350600405130713030480c032041c860503c14000300203a0003000010015501c1c008034010300009d8a103500070110a5011804640c007510840e01c0c6082a52140c03420181110706c140d90070202c2c80d103105801d0088103000c00020038032806c41100007851505540d0100c40040a40301102d940105445c007980c0200a18001103800186e00210b07254000f5036000710b81584a4124090141d28000610b03c44010760f015100c0c1e50042100d0b44601402c80c21104440d503070394952079071804180c194101003194 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 983776843 1250 983775593 983775631
    0x120f050114071b03091206090c060e0a060c050a0602041d01062c0a05041b0e0f1f090906060915232b0603021008040812130c06081905 59
    0x203000d0520b2428080e0510149183d86c5040b40800c1c000000c03001c4a43c20b035501d209404100c0180d990348050543c40c508500070042000c0450300001140c0a4002404010003c180800104014240082d036002c00d055440b19a680780048001301d109115010ba0304c051000800c0180c82035040305424070801c840700103096641644841c0740c807254a0440e0304840c500e407000c15543c586008030704056801d030704010354000758000d00504103500021164407804007003181084940d6045000b0b84001c0002c4918101510600019190521198400f600c0c644c00c003c40018555040781d081c80460301400300c43c0c40142180c600c110b5a079088044902191001c2060a20400032100c021b0441c506255401404080e0b0300050032210302212112404625102e050034021400c045804548086060815400b60b052554441880c0e0040020382141d801c401c0e0700066101103500040040a900094030300c0e0101e40302c0c0401860204d0881d40051007440d4108030840c0c0b4400c9118540c03240340700040c1c0c0c02510308 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 983778093 1250 983776843 983776877
    0x71a040b0306040e010c11070f05180907030606060503011409040c090b0429010216141014030f0423030d0518070b0c100b060306040f0204120f05011407 67
    0x400303404070f5000340d40c1c0c0300ba200402c0800d20888915070b28035105c0c250195030a01426161180e0760b004490304000480080001c0c0e00d4105a0094500c41d04c114001d03e540c0c1d4190039858440b0031703030024022030306098000442a820074011030507103102c58012026130f00c070b032014088080419070340200308556101c0e04129a400f0707580021100c030303001440400d240240c0d25007680c2d408846500240419000900f801c40c568041216110704410703580114600c81c58103204400360300c00032407404d009038101c0c0f00202c0002e02c66280d9004006240c2611600d81c28040043c82c501801114100d41c0c10504100700d554145101d1903542c07602141d00c0003035150200f0400c1c1140a00800f03010306482070f030740c0652041e500d1810320504020b490100c0019480d90800d000142c0380c48841c1c4042c1c43c1032484c4c071200e1101d5449a2088030b034003040c00d41c0c1c049614081500c4150003407040764401c1c0100e0f010200c500c0200301040003480704040c0990000d010380f65605407002c00384402a10040c2c04905910000d0140d52 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 983779343 1250 983778093 983778097
    0x17060d02010e0a051801050a05010f05181f0315050102071a2d07061b090b03061219030311130509150d061b020706090512120a050705071a040b 63
    0x102e00545000585036031003000c10f02d5039801900403000d40700f40800602c003d050952118009210910f0172103c4c1624025002c2c0442c40341c0030b011000382c0710000e00c0030860346500d4245070320381003034200207001c114008070010000d00d408066040f044184039000039075036100240340360668521428148040b00091086c25041d071001c01d40c028a203a184083c1c0c00554440c450140050664100469480c18140303840030864400c0e50100000c054040000e092080c0e1003005241503c0200a0090380c3e40c41d50300001d400c00400107042c2030342d03205010340b500c0c0101c050920308240d41d100b07850501500400c009000000c1c01303a001c0b4825116154407017046586000b102240d004201c401032a00c0c01244400465044405002d003a40d03c80d840340e60b0100050b407000f13030380340008980d440a810744905140000b450090b03180300d00e074810980d0701880740c2c900c2814031404034082040280207560700034151001e4007542002a06403194059524006080004c0800d4981240c1207101400c3c585802c05921404503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 983780593 1250 983779343 983779367
    0x170415080103321504020112060b0a0302030c0c060a1a0a0e0c160c12150902010c0b180109050d02060f01180f090b041a09070803031306090f030f17060d0201 69
    0x215001807040d50540c1444130b018498212684102c96182900014010152490070518028500704040080c00340d0102a106030303004d01d10f00581c0daa11490003601090103510f40210b041c1c0500803e001d0302c586a40c0c4090200b00784c2c25140041381d5142020401020390500c5000200110a000560b071200c03a00005c2c501c41c406100300c442c20028580b40c64101c42c13140c1e0004100e07011201411b0302404607429012a0040401c4c106000c40889640000c02418146800400c40c00e200f20104110311485d8038a00c9650f00c907680204102d401034148503680d101300f80311080141c01404003003258642c00b400020306850120f8141500c032801ca00591005144011080b070b0901d030394800da100020b219201450080303009510741c0100c07402060440301001c01c05444014a64400c2c041044200707004001c0d80d80c090020440d1a0f980a03003420010007800c0f01940c001e09405800c0c0048041541220f01209207121a503180a540401020644c0d81c1c07041c01d40c0d61541c40f14400d00d0032001584545902141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 983781843 1250 983780593 983780663
    0x3020c27010b0406020709060b09090c0d2307020c1c0213020a0302090a1e03060213051f110c060403082b090212061003021c170415080103 61
    0x3080305000d100c00c034160a8005400040780000c041180d26810451075010307100c0c0100c1006102d06e0109200c0041c4160301155000c5c0100400051b096903020090f00d900707030010581030125415910311481210000201c000900403400003160030244001540780c40303500d01910100c0c82c0014034005ca4070f07004400208903485100b248030380c0e644504600140440010310f40300962610002800c21031488065080250210b00036500450948500d480721000c0700c1e007180f001070342d03144c2c12400c01034121150342080e50402c00d1040075503184111031091014007000b030307500c0d124151240d640164036085981050b036032200090105002051001d0001e04000880311300e0500f0303002420700303a075080f070080000b07107a001da81d02c0a07048154105041900e1002200b1000380546180150980350304106500000c0e004000000c00e041e41c0d920101100390b0842d4100452001c502d140c20084d1140f030784203001e0b40030507803200d200340c925130342c09401610305032a40444d035001080e0b080303045c1c00404030f4040b80c1101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 983783093 1250 983781843 983781889
    0x6051201090b010914132109080c15160302010f020a0801051507050a020103050901020c1c180509070c080705120304062304060b03160902040303020706050307140306220c081303020c 80
    0x640c0002c2d2020b00c0d05000d491351108c210f260318048100c0e06061200b4043d90042d890940d05010102008044425580744421300310104403690408030f0042c5025107044042ca440040c44080035a04003010f0b40c102d610880c2d80c0070420000100021650003040c1004045511001c903110043d0301039084158480d4000000504000c44149030034070713113518001c6141c1d0b200035450710031080ca64840b400030000c0c5500120b050800c2e00c2c120214807802d40003030142007040980d00e000010410120200d800040c0c00604445040d01c5e071110070036060740709640132030b5003a150051483e03803a4018001c1e030103e40d2450000b03044a90311030329110080c05418000540c58001c00a81840030341150840c2c81c054965154010b854906618000e494101e15800900074444103100700700c2496172010500030840d003010102d580b02d8460740e0220f01c0642080c0014500c045c807055405103c680c1607803001503261110741d03403c9919181c04400811116491340081e0041c1c215504424082c2028900c807240d0780020f5803401c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 983784343 1250 983783093 983783123
    0x905090711011802030d092411061005030d0306080a030c05030408030408030702090a0902100f05090901080d17012907080f0d0509070509040b0a06051201090b01091413 74
    0x41c2c00c444041d45030b425408034408089055080400c0340c104100102e081c00d00c0d1580c1441c4003400302c208041c80e14449028407643d0701c410f03603104484550242e514401125010f0504081e160265455405158064410034040c1840c02d4880c1c0160822030b1140405000c0e03011083d10100c2e0311280008094600784070801000554207820002840102544000b941d1034000324810000c1c900d0002c0d000b0b082680c00c000e802c0d400360756a040d000301d50b0b080c14181b40002c1505000261841c0c09000c9480b03034005040000007410100c08114003400d80b00075a204051010041880b1201100a0080c001c42d400087c172140e8181c000030b903075001440d58a81c0030f5070501296a0703c0b0301160740201c0d20708041a00105000740020081e01030741d40c0000481d8080e01101e8101008603000c0320008101816000150780442d400d4001e0b03500103006000050600302032820b640854602038000d4802c00c0b03a00601400002030ba0070720300e102c2d100103641ca40e00420071316111014200e120b1207888106a5000010481d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 983785593 1250 983784343 983784377
    0x3080105121e03040501030e0307030e28031101021e210f030103060905060114030a021003150303020102131707030206031905190507030c0e241b061609050907 70
    0x14080b84000303600115a61820907000400f507440840d4000f50507407084c82000c00103900198194a0741c2000e44006442c40c11030600c081605d1400c060307600740581c0b003040c04410b00403440440c0d01d80c40c8003030702181c2c00150310342119462130012050310080340d00007401c4213800441d501d442c1e8111400c544a0341e42810f2055000b40c4042e48280e004490042d039690b10501005818040e66004000c08410802e8450490021039121107036128020321900402d40c5998516010740c1c8030081c1d455804500100705620f03850064000c0d40512a01303003800c030340100e0020b6010045d480590402204c00064440586154248840c50b00080c4c0005c005100d07041c1c114006800c24070540e403007021001c0d0840314160b11180360004035080580080100f50501060a041d141c00460700020a003040e18262440b00101002d881007800f000d8680060400006401d010300841100741040410540140c61a5484080c40d0a92105c020501c400209907a01c4082285d480c101c5e18203540440642414054191803e0b69 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 983786843 1250 983785593 983785633
    0xf0f06010207270606080c0a180b0309281e110d0c06091a090d05031c020301090e07060f050d0b0d0311061513020903120408060718030308010512 64
    0xf0080600c001011100c1030418103004040003009030741032040b05428a11403a00d50703445403d02450500565a031804080304c0701003007441c000c20991844035242c0c1088481c80381c8a001100683c07602020322440c20100c0e0201450b110001e0341e209900c03ca28076040a01c52850034205007045d01c0e07030401c1c005215981d407110750100b40030341c0c451160401003900b41a800781c0040551b4011a102140c0c0c0300441e18408030340000c841c0c1401b41120100c84003980b502c2c0c890302d1449000340c811200310b00b0414500701001e05401039416501003500034031270101d4042c01150b80e04054400d050010307402805c0007400c940941d00030000107039054400708040e03804202140c40800040d90450000b4082401d0f0320b40d0401c14008503070001c41d9866907015000400c400503801582944084003025800103000490b035404219200321074201105070307911190323038519454560408840e5040441c2455107112080502a040002a80c1d810b8548140303036400d010a000c2d264100015582551040c10f80003a02d054050035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 983788093 1250 983786843 983786879
    0x1814090a060504140f0a060b0304020d02040f060b071103030702090f1305070b04060f03050610031113030605070807020312040609020607060e0303100f0b070b1015050306180f0f06010207 82
    0x9240039940c20141600b900c0b40385c00900f0084418644031083c00404803c0e001c59400c29011100461101201d000050060a095036a400c00d949003045c00141d00383c052024050960144000329003182c400c0f401c0c5074480c41020402588007010310001040c8070400c00040c3d40080704005100700f055025034405240c07202e1a00b0200c00079202040401032a540160380d021900e100d480c003032240782005408a414062003040c00720134180c0300c11040110900484c01d442d038045130900420034480d03803070420400401d81607441000040300340c00000c01d501d0001044903009003606440c03003001c0da61a2110801003180d4041264848005c010480200b090390284001824040004d03582e00d00341000a00b1641d00c0c194403a1100c82200c3c034042111a01600a075410190070440b05003440d41c40007510161690b241d003080383e41442c2d50646650300c55010340035610450080d511000b1200d1064043c42c040303038084400c0e1280c41d07452000148861000c001c803540060041c0115203500c0d44611440c0900c0903c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 983789343 1250 983788093 983788121
    0x11070c030809040b011701064a060f0f07060216050105010906140a090b06130e0601080106080112230f01140109090302070b0307200d1814090a060504 66
    0x81003400c07451500c4d116002d400c03c024241001d07607404090701d41c0100c61051144005201001e14104135010310103d10403445640341d07110044443c00041e0f05480e070035080c06288000c030000000d24585041c442e00f161241003588a5842c1020113034028110380381d1112900300c070120b400340300c000c030440030b0f00208020700b0b0320071800403a9642c11308218a04407000b540c0144d1070516030392007144482c0c9034520040107417030010501251407000000801d90f00e00c00e00d141048200e40c103440000f6403500f1442d805d80074141c243d0340c040041c2d9880703000701c03003007002809650048410703050790200013900c03c0220140049044406c3d2600744c00c9501c1071b8284540140c8006060351100305188400c8251032859025110007001040381c4070642d14020b607205a503001d4400011400804107401c1c50285000e03030180c0100325514a072801103904a151a20200000c04021608501e045044107a47c41032160648640c1c007002211808c41104021507200e025081100c001d40c0c800c1c0111b040c2d2954005e03141c02032512 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 983790593 1250 983789343 983789347
    0x1f1505220b0618030f0712030c02030c0627012a020315011e210b070207030209190f0b01120c031107050a1a06010c0b090f0d021f05010e01030611070c0308 68
    0x2c00345820101c50445007412500700503407d10206404039191004148c01d864401c060314210301c0440d00c2c1440f00480c00340e200c00003148940400a42c4a21085c0f80007104100c1613007446864010740c2c0326050703070542c074a03c80381d541c007204030605501d00f855418500050840d1801c89418038200110b6034280c10075549558440500c80c000010410040010100ba1490849005803854403540d4030021701d40042000e00b180b004555960302c01c000c0c00001e19001045c1840a080401003403d42d0410a159840c2c200e0400c800510140000c3c407034603000c4003040e1030f41c554103c41c0103041801080d048007840305056a58005000d40304809014000051140008240e00609810015a420072101401000b50310000c100041c0d039034032000d0a004160b0180130f06403292180803440341030869404c41c11007648100010140c801d0b500041c0143d40c440001e2003103076010101441c5c942030b10400d0064400c0610100010000158680d101064440410740e910f800d0001c143d5510b40e1400f4035500c2903c4078040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 983791843 1250 983790593 983790637
    0xa060306061b1a180f06150d0203071e1e06030b0613060c030507021207050a051203091216090204050901090203040308040f0204020c1f1505220b06 65
    0x3900007200061090304580d9222030030303074646a000c0850942c1e440f8101d882004520301841d0307000e070704407100003c02c00d541713071410403a10b01e0740c2c0e075081101c12180d440c5441d20413180c00d00300282c965800710703005000f40c0850703810b202a0248141ca400502800242111000142880215841c65500307020008071205540b604000070103480c50720304402d10400c01080700d400012104c2c0b02e108100e4540781000c140c18656820141d80c0c4e03015124000e9000700000600c8030b0b00450210301c2405841040328501c101a0f21101807000404031681625043e07803007004600b0030741c50f0007611100c4104200085031050018107502c108454816441040616000315091140d86441c2411601400503200e0860031031501d9207008204800c0584085c211559942d03a44c82907407101e804807500c4001210441c2d400d807002c2940402018043e0b01190310b494903000c03030038a112105d001c083c41180c0c0000c00c0d0b652807459040c840700706011009110a0841c0d901c440c0f903041911650054140310000c2c0522036070400c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 983793093 1250 983791843 983791847
    0x106030515070c0f051002040e04050d020f0703030e0a0f06050307020f0319390b0a2a09091803020d020105010b03071d030f0303040c0e0105010813050c0a06030606 72
    0x8110703001c01c40c520030080466809a06042081d41040441c40d040b071442c100b1070305081448000c048410300008000c02c9000c4141a09030059100d02c0c215060f91031408000c90700c54440c4c11900300241c0040601300b000c80e11407100582c412000900c080e20980d6501d900459288459100c200410404010800516010302230041400b00d410091403400c40c010b0250640c182c24000c0031018172148044610041d010b0340f024200f04040c0c00c2a4050301c0d025040b24040070303902ca0500700c83c10340481d400110001000c0c01034421100800d000503d40000300035038860241700003188013042000c0e000300000d0080180c01656035800803144c4040c091041c60070000d01b00681c0305c4149080da07050100411601203100c084a6010515281000c0e52503c1440c8000316a020729070300c544e1621400d9000700080001000860040d84a1900ca095080d513803e100d0300d52803000d206190100e40e059000400422051001d000f01a11650591348901c00110028000b50219040b000000c0c0e51100306001c025 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 983794343 1250 983793093 983793103
    0x1b0102220807030201050703110109020409060614010521070c200a09051014060427051321030605030109150f0b0a03080c0c030a060e0d0804230c030304060201060305 73
    0x400301e10003400880d411500080c1051151440040c2040014107440b56a1a004c3d4007010b9642e60040092142840d5070500340082c0065016200b500c0401c04100640d941c010000c403190301015080c4e00c1581d400140d40c00d80800d90041805040c880c80081d03100016400d4000030350061012080b10701d544000303005001941c012600b14a4a640c0740c80244085c10170064a44000c075440147c000c210015240041900b6001d00c1c0e215514412100c00201129101900b82d24020f0901005c02c0009580d000e1200c00c011180302d8010341f050441c4c00030b042014000c6a6000e903c07400c03074280494820343d1600030030b08560501800740e5503c8071071810a20400d965006144910f910000c0900c081c0d0b00f240f001580c10301c120320008101e4007001800120003802407203241980d510080954140c19264107155001e231032022500c04d030034054400e03004011b60180300303000c0c003840d040148681031105080e40b080d00880c0c400c0d014400c5104100300558143c0c0c081000f44054900e070790002c5041461031820910b04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 983795593 1250 983794343 983794349
    0x151202010302091819090201020a0b0414160905070e0a060c02041d1507020c011b021504170129060315100e1e010e0603071b0c03030f030618021b010222 67
    0x2c2c03402d06c819240943e0f400100e410320640c0200030103980742c46524146101d0308046030a05030740d000e00036075020200100c2c040c1004803028940c0c1402160741e040300484004040140480e071110410b038060101c28070a204015a40d072000e000056088040413280840c10b000601041e0658400b640c03030b0361000c140d0511aa00030300d080c001020074003007000000e4034080101205140c03003060400481c0c00c1d955159130059103420202501c6a90710784034a910324841606180140107903007030184064405144483d402c620b408000e5005500005040c01c01c8403940c4007038110542c0001410a0b02419603400040e503000e0300301c60b11101b500388500c1c42440003140c0e1680c0352400e0a41c055a00903510313600000c0400000100701c1c0c000340e83c3c0d03643c0401901c1c51030743e0b4501c6429541030014800c003085840090304090300c1c0240c41e65400072030302d51000c406844650180c10318540d00c2d03041b0401c2c90001600640407220b103011909020440c0b03c2d403200c0c00ca8001d00120640c01900344000300c90349103144221405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 983796843 1250 983795593 983795641
    0x803040302010b0f100309060207120905031203070f110a0203010f02030720060a050903041505070204050f100302010e0f09100302190605220b0a020a03020d031512020103020918 78
    0x104d2007003100140c81c100040c110042490303260040e20003002815070484495542c405d5885046110b014802050000c542c01117034082e104c2d80c1034550000341c015058074400d0312955034030820349000801c2103030449a10507a02c08a485004016401079a080c0520710a41c910070400503100d05d06014000c10380d0080c00001052a100781d01c2d13121040b007010550560115540f0300c04209034850340716240c9940300c0ca9000704650b4551200021075607a1180040a4481c0211020f210702d451b1130380e81d40306554090324040b64400c0706403001c00055005a01000800000820071a40c1502d41004204c03005004c81d20345042008005081c42145080c1003114134075400c8144030b010300c5041a0000d00284248056400152050348a06032440d0b500180000940360310745038103480340c186910107961109004400c501501030030000a84051007071103220700a04560b49840403803071511b480c6250020001d07206904043e000c00284800f0340b121482081101e9080b92111861300d0182c3c2150001c0350482c4035020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 983798093 1250 983796843 983796859
    0x220b1609050402120c0702010e061c0c080609040b1b18041a0303030a09020619030b010f030b03070326130305100908030424240509160f050d090803040302010b 70
    0x121500308544e0f400e0340030900220007680c0e2011800140c55940000c3c4010350700c0840018143c400807030351044010b5a03600c20006110307002120790203580b204800c440701500030b07114000180c08a0345961034182c1100490704003002c0445030400e10070035a031007200c0c82e07400240e043c40302c5840d034205440b03489144000d2411410f1110034030000a070720391202610610455456180c104150b648040860301c8505110010010062502c840a000f03003000f090054045288030464549040c0240519100902d00038042d08106e4250703500c00c12121500d417a0303507998402400c1c80031070020401c401401c094941d030700c00031442d61662900300c1c41c11056034070201515050000d1070000031100b1043c0d9821690003d000d91034000c160300301c004202510745c441c06826040000c40b491410030244c0c000081114007040c83c40746504eaa00b4001c0303000042d40c0307400032000780d100d00d4102244152045001c550300da181062501c000304032180c0c20b0b607500140a03502c070100002030204064091264807403211080d54514 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 983799343 1250 983798093 983798107
    0xa03110406020a380a0b040606080f060906090604020d02070c08030c120414130b040501091a030102040506180d1209140108190c03021b03070614090303220b1609050402 74
    0x84100c21000c0240c51303c02251408291441d24035007000c05555009001040490740d20100107201e14006d03500c004100c0d41c42c0c0302080c4641008007405105e8a00507000c2c0e4460b450b00e009110003980094100100c5c02c1d8203001d0310000554034400c08000b801031000035a101e5640900c4242880a60f4108001410040004010650b001c10405591440c1120303510b03a051640f890040c05011070b010001d900501e404d0001c60103100a6100d002048400303104404e00d0030301c16090600f01d02c00c81c002c0c0c541c001c000344410f0803c2d030000509100032610161240711418016502c1c84869845500014042001040c003401340c80e035070700803800c42001c0910f4814030a0900c40019a003c05440c0e0405103800d40b00d0f1112300f080360090301201d403103c100f441610581d12403480002d07103980002078100d841c0c9042c481840380890500b403440d0302401d0003001640c5075440304188002c4103040702030014810080c1420200110341c00081d114444c0c1c0c034601a0907031415400c400200001d05980103940710f41d06c140700e01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 983800593 1250 983799343 983799413
    0x105130b0f04171b060f150604051302070f02091602060f01060f1103300109020406090909110d050102090306101503051b28090b030402060a03110406020a 68
    0x40d83c2e520651000c3c1da50f48000503200c580c808120307034a60400c030340706600c00d0169881840c5500c522500030b50071842491003892003002140d2107548a030320351080200390035000c400220750003000c7c098410761100e4101a03050740032070070000040702d54814030f6204801c802640f07a014401c00354801030212681e01c403503051079000703080c411034600201704005002d01c10440180c81042112455440b5028015807154009104001d20545030802400200724000001d00c1c44228002d441c1034488540724100e50030304081c030020003400c4041040c0c650a40c1140095403646440c1d032404c0c4150b001e20005640d42e40a0300a06240c2400505280000707011503800308206048005801d46241c1c15260128003a102d40003c92001c00d0b1070214038220590004201411400503c11034070512440200040c04204c100026a0b4244080c400c07030f1440c41040000400515020000b452040342c80c4c1070020301140711020f5921035401c01d420040140c0e010101a130244580c40a00110820108808581c3c0080c00c0c561 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 983801843 1250 983800593 983800613
    0x9110d05060d0b09071a2d0f0d020d0c0e030606040906060503190302060108010b0a0911070b091605030609100c0207081501050406120203151005030105130b0f04 71
    0x95908095a440124006a5641a4000809400c4a00d092043c105a400d460300d88005128001081c1510704045c0700060300c40050722510003109075911000a0b100e840b00102c500b4030308400340c1c0518100041c0d40d01c1103401c400380c0f1404c0c5001c60016181c8205e40309060071102d03441c15400070300442c04a03940c22130f41c00141035a44440d083d600403c040c6107601c1d020b00500181d03040550f050003494040140307020b000320011981c3d8041d60845529980e141583ea003250280d03036809400501d607003c1071100580e140c004a84100404c5c11080c070701030141c0c807100100142075410760450b8124207840720f00c040b090000303800909030031005041d550604010a5644001c2c80c02041c04413a100e4048444030381c0280b041c038004103070100031398400c4803003a400b110b41c114003400b8040c8948d1070008046159230803c00071101c06540070700207145941034504500c1c44030200801035903191707030405004038454030203014041c00349401d2401d070691000d02c1c3ca00348030b201d2030081c4840740240c40c1d03c0c104004201c0000c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 983803093 1250 983801843 983801857
    0xf09090b10030f0f0609150609060c02090c09040203070903060b190509060a0e0411040518031209010f06030501091713030f02041d0d0e0301110f0c070801090c0306060911 75
    0x82c0054406001c80320320014040300750301070091500d04200040c1700d50450704030b40004c3c0040099440c0c0b10340c649005965001c21401040002848008880014184400d4094101030b980a41c01d060240316000034050b40e004172070507800200009c500700200b100030300900008410445240c17054440781d65640d4220741071441420f10819141c000304200780c4a0321074500242c201d68081003911700e4203041c910303d180000410039010b0741c9800002080c07481030070121500c904030300000c0e500e013414001c181e901e00e10000d40311003480c1d51394000e1a1444031440c4685402980310700b00226019520f410404001e180c6030100940102d4100182e02e00950b88441d400c080ea0741c400c01039a56504240086401480c0c0b072210740ca00387d07401900f04c20006000049014260300c0503034450802e01180d60606080c2c550090340c01c61601c8040c086600300c08103000c00307808085404421203107280c3d45d8034011400c4d100171040603030b81c030401d40d078007031092162900685014100d180d0b0213000c0d00a040e20f49000c5480b61034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 983804343 1250 983803093 983803097
    0x270201030518100f1404081209011b0c0516170c0f030a0b13240b100801091107081206090a021204031d0d030914030105060f1c0b070f09090b10 63
    0x84901c505005036840302030001c848034920303115840c1528281c0c5550f4842c8c0850b5142071094130003d800d000050181400e01c8015000e00e144440001c0400c1d07818410b02402280c0500900c100140300040042000000304005200105d8441180043e0b901384000c103842540100007400c0300d2400d580340052100c03c0c0715400701d00001150b030740d0500300d81d42503102d000c000c05242684000000c00c00001c66807091010540c4010407181e0491800c1004621031503101d5008a90504010803030f1610076400284040c001c03656451809410b65500c245580c4680901c20160012209000882c1041c090481d803040900e1021450b2a840c041d00600c0090020001401c2021001c112a0540d6000c0c2215040290140c0710b822100c00901d8042c040240600403040b802c03c001000024901c1c0c1402800d010300406003610000e01c0d441d00c03c0c400018043d510000d60307501c8030048800001d02c11840640310b104150f598006650030b81400502c80d0800358012080d080c1000b000c030a044d07032881d4010012080318 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 983805593 1250 983804343 983804351
    0xf03010525052811010b0d080d0608030f0d1407080a0b0607230115030f060e0f0610031203020f0a1d04060801060302040f0c050403030807020127020103051810 70
    0x4407040b1024450100c1e4520750850040c81020a040300180fa060f2030702a40d01c8080d0149201c0c92a5402c981c00c20080170b52103040200b0110201e0035510040107800e0108102048068450b43c0b0f05145a00c0740c5084a20900002481c645018451145001204461013004114100070f5001400c2150140c00b001c59160f45a0050300540e071004c0445015036030083c0103c00c04241d40403c221445001c004401495084c0410b59104540004500041d00e45c05020084080707281d444010040043c1c510200a03072103603101e070f005503034000c020003841101d0100075006010b05600c1c00468030300303d032209003040c14010302c45040010101e809036452540f6900d042c2d1400060041c4e1400f804c59143e40c1c07181c2007403600700045003001064100c041924001d840c01d002c644ca039101080c048400d100c00210003d202488180300091040203e281c1141191001150541802502034981e4401c95242441c0c1d400c527508030400c5580501900c3da0000c00148030951540302e600160343c4410415440c030710700c5a41c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 983806843 1250 983805593 983805661
    0x629070515090a0210030e01050604180305090315161706130504030c020424050a0f03021003060807060e011107060f11010609020f03040317061302030a020c1b0f030105 74
    0x10030403070301c0281e0fa0014005400c91040000c0031b402000403144106040d420280001ca041c10280160300f030140d80c4880790a031560040e00c04640c150805410142d0502840c04078070700c07000d0655400c0340a800c01c41051102e8250425001d0406e544020300294621210000c004450b60380e604285d0140307220141c0070403543d0300c500d0b08880714071800c64025401440e0041100d240c403201e10081c10410107420040b1905a16081000100503503031144810070009590700744018108004403980e406440c2c14081009034130b80d500c0505012094024400103840019030302c07551360303006d84c07001c41400100b8040d100c1d80f400d1904c02040070444209040500c816a15002c0d8024425400a0f00400048104540b151013955046c3d807203520a5a0036000121210380d884a0401449405c50166200a10210845901c03d5800307019400042c109514a5400e02c51b20040b800103009281c40120782503c01e03002c007000c40301040200b80f25091558003907031402042205040e00c04941c00c8414030051518152810 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 983808093 1250 983806843 983806861
    0xa09090201020a0f0c060e22021e040b09041404020307090e1006080627150a0e030a090603060803130b072604030b0109050f07030e0304090629070515 66
    0xa007800013000280344140001c10b1001114045043e14074607902d1143c0c510007107042104900180c5246400b480340603041c41c6070b0404690041040c08032908520204024100703280520f500709a00c02c0030b5000d000142b1604078a06413082c3c0d40f0002c0341c070039105001e09050700487d80e184110b01507079060603039620158014690420800a031032403250014030125464414546d1580c8003a24011495000e248500302e03030500c846084544085140018250780250410302c901181c800741c51a0741c00340d9180b05a08400c0001d0006000400e2a91513071000c8070b05d0900018116040c07540042807580051003621200140d00c10450100c549515000c1d07201c00b41424512400c42d00440e80e0410050035400c81d03540c41c1840405002141c0c01034448004507030ba82d08120007a03400c03c4442140b41c1b07010b0b10029070410300a62192000418040c1100d04103a200e504000c210742054100381c9486d1148800c03c000c4100a9001c10b0601c2ca1101040e8205441c0c0d81d08d0070384c2c45204045003551180d20700c0000780800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 983809343 1250 983808093 983808103
    0x5070f11250504110904060b0304120c0c0905090606120304060e04021e1215100c08070c0801020a091a04080a150e03070b0702100e0c04150e0405031207020c0a0909020102 75
    0x1202c010310400c6082111001002e40e64030140300540524140034000403108140d1040e40d20441e00001030380078130300310f41000b01ea4510018800b143c417400783c4480400c01c031806e40720f9284502c031040014078207070074000304201c160094140b2000440d841000107002285d8448000842058141c50141e140d4520340710000c01d106a19445141c42c1c10040351803220301c00000103e900500702403c0711859520520140440001c41c07a211401040710380500c0000162003034000c007182409012400d0140c0d484410702c07800d9920050400c8009007601009004160284103604210000c40400b5844c107032400004540303d0321840e0340039101e003180b1000303032540d402036801640c0144240004d40b40c0c0c401903850010a00841601c92000503c10404d6200701410940b01308440c0030030031001005180d040c00200005003506011605603e003d01000142c411000e03205680910310a030059902c0d9510454a2815008000d00e10030841d0310240c11281e060711115030101c140c950f41000851703a500c0d5070005034942 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 983810593 1250 983809343 983809349
    0x518091b0604030f0c030b0c03060609060f0d060303030614120d0302091201020c0d0e03010b0306040b07030e15011d130206090d080a0e0a0602010207021806010c0f030305070f1125 79
    0x1940d64002100c042103403c1883c402607d00c5400200440d03194100c8030030b4107000449441340c00107030403c9000c26074a428809040c200b803401008614155181c02d209054803802d5100703c0c0400e464140a0185000d4410b0341a9054030aa84420a500c0d03030120090365800001c0002041c50341c00954400c1c10303100c2c20900c07906030144034020b40d03a031031210071603680d00e031400a103060004071051603502c0e03140f5041c051100040b80c004c1c0200890b0b203c40e1038190003008090b1186050655601107102d4a441c2030280f07185050302c0084542d159890280200c5000c9100746504c0000b2400104100c109124190f0b11884a50180c0700b050b11610641c002ca6458642160080c0c00110007142c03010400d5404071804099110580f00520301079a1400f0607800e03409940c50003540034500c12400e18031610301c0c440c903e42c0071205144c58030b004001900c9242800d101014250002511203042000b2a40c020781c580d801c0c041d943c07901d000c4074030010302184d4440380b030380b2450001548116a58550900c0b0a0300030006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 983811843 1250 983810593 983810603
    0x607060b030c0a080c0405010b09010f120e0d080415020310030305030703150b0315010503010b091e09010803070c06081302010c05100f021305090705030112061b05040518091b060403 80
    0x41c13510b4031441a620f5030120746480c800c1d030070100081114078502040e036a0380031042c1c41d0003080c102003900c20f68480501c922158403942e66112602d103940d104101e02c00e1100e80c02d0300d03010b40e681003a0802c24840d21400546082c00b030700410a0000305000442e09900702c0e509403034166160345583c0d0044001d0304c1c01c030190b0f0042440e083d0300410102c145000550083d504125042100e0781d01e9001965580002d104101505100340300101075030400c1a82404003a180c0c8444961045404001514029082c1c04c0900a030340042081c8041000c0400308402525190421803050700e0918499213900850040c028100582003541c0001c10004010000180300d200c54140541c0c202401d80c0c03002900440054039800e041c9000004070307400c107200d441d07000d012681d0324146035a0078540403440900b0500b0084601d00c0e59041c03190340c4042c0590a50b00c2601c0e40d80d41e200e6986140204005406a0300841500024503150910502d0308002809880c1d010041b0410980303207900c000000d0303060180b60300142c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 983812949 1106 983811843 983811859
    0x1e030f02160303080105040b010504080d0f110105040506010501050a050910080603010c05030c0307050918010e010f050618010f020c0a08010c02070f03030c031b06021b1207020607060b030c 83
    0x1002232060500360302c0c0564480c112803030036650070482800102080d00300400141d0080c007285032824900001d00045c07c140d2181525504103203e0b01c0e0502000280e01400383e4000d5081d50340e10080200700c07a02c1e80c4120f0744003501c92201103c405200394038040403052580d005900303890044800440890460780c1d528000d40300c0345d00c051031080d031118801140d6406030302110462406400001680996075250201401a48006401192160300d00707201c1e0b082c1d18440d00c10254a070301000d1030101c1000760700a80507800d041c0045226138204103180c00204180405400c502402ca100b582140c618543c0c607420302c005003c6a010040c00610031410120229214039003140704001c0c0d00c1c01203900120540e072098100d330f00c819051800c141b04090144031105091007201c0340c0c01c11050000b451325030740b980000c0a610582c1801080c00b5035448038004c190f02c04120f0000382d91000303480c9007 = true := by decide +kernel

theorem cover : BRFrame.Cov 983633093 983812949 := by
  have h0 := BRFrame.cov_init 983633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 983633093 ≤ n) (h2 : n < 983812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
