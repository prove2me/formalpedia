-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4348
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:20:00.73817+00:00
-- url     : https://prove2.me/submissions/2ea6d411-3284-435d-8cca-912badc5b82a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 781834532 ≤ n < 782014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 781835782 1250 781834532 781834549
    0x30405040e07031b0e01061b17070203120d0b040e0601090c11030d0b0f030d0905130618050601030e0d120b1f200a020d26030a0e1218 59
    0x2036040212441d040d12540c03500c1c42100c038844da00d4404a08918108412403e22132840c2c050643c5241200d100d0001c106c1488010880540c020320148241c1c4a4600030308031002599410b13a0002e048900c80ca10600c1c11124030392121200c82d440601303080d4034065504090090025000d040030040007030360310303001c2c05500810503281e1050402c05201420703003c17090200050300034188034400c001002c008660030002c80001642c500d6009801c450610007800307401504010845905841c60b0120482080d0680000d00407074100021210500c42504031014050b8042845104280c03010003880344416030041c1d90308601c03880100018002811291000b6140e04000603400010b003020a958580140940c402c40200701c00390b000890102c1e450341d03032483c070552000f0011510320150015007090b070003013030b101c0940e46005031024880c0702c113400d1070350801c9403600031002c0400100f03a10f0b8100345d48600042c041000440020b8410200e9441049036684222003000131075080dc5400c0303101201c10b100c10709 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 781837032 1250 781835782 781835801
    0xa1101020102130303080f01090504120e130603050a15090506131b03080703031109031e0304030507030f051005222a0302091602030f0d1130040503040504 68
    0x155003d001c1103000c040440f46541c003451190310788808038603140c4502c207414107050b841051041e041a09000110701900e940b0079203400d80f494021410b522080210300d0b2000345600f007408031440c0c01800810300c0004140c0b00b03404c43c45106000180070380c0c20a48810f9034035000340942281c12100100c0c81c090318401040000c184140130284981c01820462601122640d00c00d5482500c0083d80208141d4944200702143c8c10340106c040c105594140440d90340c86035158860005240b07003020094000081080d1401550700400311880c9949030b00e4541e030a5451194103d0301ca2054015242c04100c081c01600d103c2c00249124190300050020169003004640005456413607250030140c3c40a1100b480d403e4041710354480b4441c42c00d15500c1400782e14034001b880003220707600c46480701202c10750100443c0c60340504160060b4440f49a0b07001803004107424220000b440c180000e500d10340260300d100c1c0d0b403212a54615104d28080e400311040304846800c645c002c106410030070003401946800c0e4400d8804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 781838282 1250 781837032 781837037
    0x2100c050c100809061303050901030902060c01110c0d03051302090c0c070e16170402060c03041809061821030e010e28110d030e0405040b04051c020a1101 68
    0x340001100420028600000428000f464100800200d4601005016040044820903606240c140e0301c3c010614010443c42504243c0c540c4580d00940d61000255144a85030000802c44c94849400070380c95a80258039540040c064645861030449c00b902c203242c42180314004540c41c4040c107500b0844403610003001007801c000e040c010314a54041c1004907a01511500540c142282041d9200f0802030102c4c240d000104000e00c054420604a2154010b410607816612140c03200240203c03541180281d8014900d002c0da101440c03403900000d0341140d00c0140c06078600700014403510000082144c03032001c000c0c0c01002e850716032071035880700a0654015840140f4001485104144150307013940c40c41080051346d40e2020000200001c0e00e5a8442c1d041c0c0f032400d1640b150564a50750740031050700960803a502c140ca0b0f0313148039801c0c1070180c0308d10184032800400400491a0502d81809444002e0301d045c1c8651080407210742d00030326a54010320750445181c005180d01c5403a07503920041141c211020b10304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 781839532 1250 781838282 781838293
    0xf050705060a0504111219020102030708070c0e1b090d0201111204180e07060c0204090206120f01080c011d0414100303022e0b040b15070201020105010b030402100c05 73
    0x2250051207032074042d020881011440e410076040032664114000070f403074400d6100d02d159140c510300014401c1c03001584450781030910401800182e0540c0188400a000010000341020800c10040030102c1591641e0361481d0360b40e2100300a440e189c031001c442085101008100c0010149400d1240d0751069205141c00e68507565166509030400d00c02c54440101e03500089814441a0000080c200340e01c826584100300301c0c80c0e800ca100c3e5075002948900014081055154000d5480c0c54000e1840203402a0100b0790307900002d40603c00d8154101c3c0e516651940740320000c40e10f50404900c185210805948043d01c02e00507101c246400c0d007003800401d80c8690382d01444c085a4607142c510b04d02c40c40c41604054241491401e029090000c2c244100c07800720f0a4980e1080c02c0c4c921805e4a25500c141c0500010350030000c1ca003c1001032110440199001502d060740d02594800d1100500182d8401c1e8020f20840e640c40f416810313680001d5600940c4680070b80c0ea00c40503207200303104c0b00810500480c2190b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 781840782 1250 781839532 781839547
    0x83406050306040f06120215130501200115080f071a130302040f0b0a141f1b080a1704111005070b040c1a0307080c0a020109051b010807090f05010f05 66
    0x500301e90359644125aa0b090052480f401c0d850003422408904a88129840c5403040da1000c58270300c0d07447d6014041c140011000e10807108280811516172740d40b0400000c2060034840c0280c002e00803503911a07508070303114640469400280105100f0216403500c141c0404444441550700c0281e08800d0708a02541c5602e0000005a6030320301a641038040a84800101250040d003448009030268000e00c03111100740400d08140c1c0c03141500814140340c48c45050800c05d01d1100704440358040305044440c80c2501d5011031050003c0035008103070305641900c82210844c1c6100b085103c08904590180c9080f460f50301c1c001d01c0d42441c030b517104446100b0f460024504801ca5403010101842600d0550f04041c4901c001d00040e115100b4010320a5411802e440c15403400b50340080003c48010b003030454083c40491030340345840c000d4000042c0c503076210050ba0504000c5681260546030861500c50009120390007241005004000c0c010549684800c60070344070b41000010b46440d449a01c45004101040000e0b5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 781842032 1250 781840782 781840811
    0x140309011e06060801121208040f0b04030f0915080a0218030a0b0114090903221511151608060616060c0908120403110a0e0108340605030604 62
    0x18070101190010760719081c844018400d20050704007080141028200c00701143c0501d20381280001140340010250350f4524010a82d001c903481c00401000c0b012050008240d08a0003120790405165540b60384955510b07180c62442c42c8038044000071400c440c000c6414600707141c000b4606c400024803034407aa494040040ba103021250b0000391090b2191800500107051b40004c90031040004950b00070389e5040003580c5548070321035000c1c541d0a80f0000000c40c040d5030103907030985000304580070721030a01000405024206000441280074180a00302550a000c894106e00902030342e4248035501256902030403c0d20b401c0c4024012a40c405003c0c4021020780594854090b0300305d101d500003207650403d0010150001c2100e401c074010b1504002c00c03500c0081070590954080302d40141c4801c5c40c00da1401d000c00d414003001e401061040c0c0b0b111001080300356002450300c030501d03104005400c1902c21603e05035110700410712104020fa01500c0200402ca02c204007a44e040803000784002103001040c902d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 781843282 1250 781842032 781842071
    0x10f022103130c15140421050c0406090c090801050f070c061107030e100206010e0613110c0c1212030a1d0d030f2409090f0b0a060e01051014030901 65
    0x300740d0700d5400403130800d51040c000c000021410068900340790038040e0046611901c80c18000035280380805801c14414100304a02e001c0501900800210b0f46520400014208002150001c1817402000203601c0805100c2c0c0761040d50722860140d0a9107c03000d0880707003a0320741c160a644503900d0b2044244400032802c010681144281c440b1a800d0804400b8403c190342d41c4c04048040d50005001081000c0c070f2051180d910482c225602ca22041e0070401c0708001b007030044131a030349404020500d2440a03000184556544600311003a6012465041da02d60f42c0320040c5186410306201800170a0081280f6001030010605890401c3c8259406110b850705e0440b54101c4040040c1c3ca51450010004031803280c440f40b480810f1b0814400d20090380c01250441c1a0301c10090426502c101900506c80c5032004548125807003010301030213050401c084000780c81c19004010800030f0f40000080e8034030304036a11501c2040e1907282d00c2d00344405901104100c0d00014114240342d520740010024446030f00c141e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 781844532 1250 781843282 781843289
    0x71205040801150e0106020606090106050a09081501090b0a12030c02041d060a0f060f053c0a172e0f0e010f0c09180906060b09010f022103130c 63
    0x214a2a1030248404c00e40c2c1e42c10b910405c1503422941c1401055100c01c1e0500b030550b0403a0404507500c0c6240003049444808980c4035008601a00c000d8013030b2030315030720b0340941200c4850301d05001d020040700410275486058454007a207180280d43d0440020f01941c0213640d4140000d0001031070307481c001c003a07170150410039000b401c0680040c010800440524890240c113000203040c01c01c032150034800c0e1110f043c2014012540300c2c007a200300c040b0740c44031460304c065200b43e2452984105160031104c520b40c40c80d400a00c4620403600d400f8040313454404640c640110706001c600030300c8020160410401282e050001240d005442800c0c140080740c900d02804d01d400c01d58010010710354a0840303000d0300b140c0800300c0751300740c682c1000070100b0180e81c00480201550b505010b0b0000030003184070010000c0c010048004c1a2074100038001560700d82035170280100d198207803280d294003040310034204d8551820340c0d446c0031100e1004000382d684804840145510410140c010145000e990310f44d440070406590 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 781845782 1250 781844532 781844561
    0x17030705030708010e0606090603090f0a030507060c0c0f0f2607060b0f010818190602040905060a0e0c070f0c121b0308120a140f2a071205040801 64
    0x82c411603540c00011240180b001c080c2c800c1050030961700048062088000030742c454200400860001c2c402480b100c014698214220340020845290145ca41c1c0c00c800825107030039140070459002e00340039204410f080d5900810744145403150703603515030b51545010810b0365420302540b8040405c1e00701e0b2208241541c0500c00081d00d400c05441e00b80c0c145c0d80060740d8035008203104000e040f010307604401c1c0c00381c1050709000c2c400709680700d001d6800d00d441c40c4900c02d4003100500c00c0f224010301050350300030026100030b60801c0c0500e6465809110341c41d052845070100800d07510b800600a4100c0c800542174043c8180050100422142c07941d009400e90754016514482c40c0f91086820031000d20440c104c441c01e074001d1381c0041803540e12000140d004981040b44074443d0480001c29980741c9a0118101da9a1004081601e0600b8101e031200540215101ea043c50b001076043c0301220b9001400403001030f81484030700c0c9815410380c1d5012201e00281d00740c0c010b10006110108640f04280581585c008406 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 781847032 1250 781845782 781845787
    0xc0d021b150105120312131a010b0403060f020304020f01030e030405120105070806030a08160c050409050d02070603020f16060e0609030702030c060901020a14030408070609050a080c1c17030705 85
    0x802009000fa00007503003241c942d4802c004c0306c8000000081c500f588013040035054125030f040e80c20424034a01c1e1001c0c003c11108030320000401e801c03240f0700250050324000c84041001c0c01c103500050b0105d2200756006944070281140c1c40441e0362113074000302203100341d000a40c0c0c100b0380d5440c04a8182414840540c40c41d944030300c00c0180c2c540c1d010004039480b81d82100103104601454965000c41e1051085941c9840c03c011254000d207c18603003884003e1074041c10400c00e2003c6410010340300c5d9841303840003005002d070500c0011114841e0080d107044030701804101e071410603580c4402054403400041140d81a469020f03005020f40f09110444c4070398040703000b4658518040c4101810440300328662841008148841ca465903030025810f01c066601403000d80c40c0f8907440c81010718501030b0307a110310740c1841541000f02c0c1d82513102c440c078000c03101c003541e1300c405080d1200801ba403030790b0904100d9078104248908107413403207140644404266004401080c60600500c0399500980d10491b403040218400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 781848282 1250 781847032 781847039
    0x2090a0f0312051e09011403040807020108070e03030a0522060903050d0315030b070e0604150215040b0c160f061e050103260c060f07020708060c0d021b1501 69
    0x200c180030031104102d490b142d46401e02e001c060100703915030001c082084880100d84c0301016400341c042c03102c41d0150b1400c1141c8901e0b01c0e24045059a00c940300c228001f40c42e8001082e5594080c1d40303c0600076400601642c24903000b41c80845554000c0b840300c2d06440031f0364403841e0003002c680725640080c0203181e803540d140c54198101689045140c2e55110701700340c603119100c906030703524003515415241d0141490849440b01f0a0494001e03035646030fa02c0d03000c0000100050020302c0c0d080c2c07215040400380c090ba051041102e04040352000100c40c090402134016000828000701c0400400c800c111385c0490096a007203d483c2c0c43c9080702404001c03504a50707200c0d0580800c8904804c03201d004c94800c8020310696056682c0d540e402d04030621407000c03d070245040d03030300b85411000a80d0807034407030241101c443c1e161000d914102c1c601c064801c03001500034071201042514002c111503100b003400a002c00d01c0e0060703400d00c81000394482c0122044411080c000943e907600188620052403040034081d280c030707505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 781849532 1250 781848282 781848293
    0x130f0b0a030302210304020a09020a02010b18180105040f020f014820060d111b06011419080f070510090e040f050304030f0f05010c0f0c0b0a02090a0f03 67
    0x2d984c1d1403001c404014800c110041e41c0c0c00071090180e4034901c0003d82c4a02203e50181d004d050701c2d244480c0e1103040c40364a4068031000415a40c480c50480c801c042002d000b0001d554202c90b01034070b018100d0401d0700d0345e103009410f0005d401d8084034010f2400031018800d51201c0c6440419640700d8032081a5107507000f81c60038201c0c9010b140f0483c61454030f15120b402c20750381c0303200c0e032040400b52011100e07040060b15a41c0d96524152003104400900c28490320280c0350030705040e540400c180000c1039480303000024401130009040c4e41613030f0010540c500d4a40c500c03c104003859440080220100c4028032003c02e1000e0b041c011100c9906c3c6200003080400d08000401c0b078070004000c2d040b02000140380c820044410024190b6401503000340360070040d50301c00c0c00c0581c15446140c02c080d282c041c80d04014010054040c0c068181c460003540208030140c50711008840442c019100500098140918030703004c80c071090038041d0440c003200380051504100b04c01040c01c806080e80040502c4030000010400d229 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 781850782 1250 781849532 781849573
    0x4080705011103090d110f0f10050c070b0703020d0b1806100f0f03090c0302040c0207030c0e13060e210d0f0203060303030403110a0f2102010506130f0b0a030302 71
    0x30420041d450844c42c1115480750f4600c1e20202c28406c115007404503007083c00050145174017070a400019a8800d214500030740740d507100701d00c0080039580c2ca48000901c4142c030840648640703d0b0320000e110b070540c0314020102e0180d04150b4080201c69603500204000c1c0e40c843c14101c41d110b100b065401a03501d410410009450341844180003440850f120301041942d01404d0104d0094a0717040010395119131341010307201c0d42071503040207400c28545000300c42d2190f00007580c201140c2c072540840036180d41baa500035003200030642c0c40c540c503030060000010000d01583c0104010250100490700b4030345070024015004142c9000d180261100041d455440c1c1c841350194003414015860298a141001004030340e0f40c0c48020310140421200e000703480340300e00060201c05101c503000241d1480381040c40c20000ea4543e03030140c228503012003c0d4121103003e40180241440344000510841d81c02c0d015084030400303411400509141e040d41c03105030009a64420362440065402070780207088403502c80908001e8107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 781852032 1250 781850782 781850801
    0xe0f15100806042307090806010b04050901090c03151401020c04090c0611030d0203010f0f0e070f0e030307020901080d09080f0c130b0d03020f010f0903081302060c060408070501 78
    0x21034008a489060942240ca05908080150350004070200d4280780d00b2030411007105076080d4410359501340220990700555400945d020703c0e0030381744981d0741c40c26494598400c510809410000f208010401c038100c07603000004048041c1400300e0160005203420081e0704031a00009140d68907160300304907a503410098a00c1c00b81c030645040218031200d8841c10a031a80ca8401e900403c2003090303602001907400d00540d5a04440000c0030f648a507154a41920081c140e8003440e050003132004400036148030410350303690040c141e580350f15207a81307044c040860343c2c585002c00b5035406120400858005840384040240200440409000304c41c0616500a01d5000f50f607200c1c0342c0640c0301005422070326801040d0001002c900b01c0340800f20000700b41001025004680c0786541c0801c83c0302c411402d15401203110404851400001c11140301c1c0c200080080340c5040d00046c001071894000101e981c0090301200c0641ca000615003801c1118019015107009000c807002ca0b840364010545004000c1c09020b04000c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 781853282 1250 781852032 781852039
    0x1009090b0a05061e1201060f080a05041a0402011e03020d0b04020301180c090e040308181b0607050a0204060303051206030c0f01030504030311190e150714070e0f15 72
    0x249242c00c000541c0707070040b09002000c01032000c1e110082d0801e01c9048928000300d03114080b82c0c540e900d50001d40810f003000c041e40c0c003098030000011503001561003160710581d8480101112400c1140b080300013980c00500c128180501a01074080f4510340814880c581455550b015a68000c041882e005a4800b001c000b0300490050005000561007000b182000608415002421150843c6c01302c40c0117089030700843c10301c3c00d80804e10051607409800c0c980310f072400f9030302c600c490440da05940d80d80320b005500030324400c1d1070844802450328004006201840c021011501c4441c80c580000b41141e1040d8021004102c0019000c1600c1a43c4810140d001c20124003030b01d45042088045100a0f554001413410140e940f4009820036010790310440e02c0910f03041809445840458440501e91407010505021601220f0f10700350b980b900b44540303900342d43c2c6035003100c1c2420039030740d6213144d9000043c242402c80d0050301404150b101c0d031401440c0c400c5100c65921409824500300e544d0601ca01d00840501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 781854532 1250 781853282 781853299
    0xa0e0c0a030302030906070309180c0e0a0e0106051b010204060509011706060a0806030a140d090503061302010c032003120108011401290d050619080706080c04051009090b 75
    0x2283d0040162a21204241e400c1a81d0b42d8076460f0442d0180d540c1e03005440480c000c02c4451500c0403076a413001c3c0c0e24111399105c0c2413143d510202000900b00040c81510101e420342001803080501c80c001400e0702e0701d038a4528000740480d030740c6000e0130b980054000000150020a00059540c0e104030701500306841d00c0c11100c01c0381000000300d90140b0403c401c00c0207000c0044042071664500704030500030540c02c40354444244d10444d00c41030703e960038081070200044200c0c1001c1400c2c40c0104010b40030710080ca03c8440c0c1001d17903600568044a0f03e820a4003030003003c501c3c1000307071129807d008602212900103542d9507543c1c0300082e4443c00c0306070405041c5a04d01a05108120141d15007181900c0342c43e1112468039503071880e083c80c5c1c8054000c421080070000301d5100d4405010381c000364020801152a00b52803030400380c08840007080d921401e007031a4008041088854040d003112504140034082e01407030542c89401141840c0e203507410300400680303980b40404c4071118521404035202e80c100e60050307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 781855782 1250 781854532 781854539
    0xb0f06060f09150417010b190609050909030702090f010603061a071b0902120103050613120f1b1406070e18060a05150309010e0309010801210b0a0e0c0a 67
    0x4a560090018150049910f21968100c81090384152801404000c00408041009030380f6a80642005150740c3d010f54204011840f0b21400b400f410410341d90241d0380c03080094030b80010003284010180c03440d071050104002c10009a102c4200d000d200790304030340b1b01100c01d503d41240141295040d901040003a54000320046600303030f186017100c044941108400540001207001c007440d80401d030f442001c00c0c0b0300c00100c0c9440e941141052904903800359050b83d0b900d540301010580940300d844401401c09182004050806020301241c51920380c0628011034107004500040526039151002554060f02000c24280c66000401150b6448007080c03501c090740740d00c180c001c21440112699a42d05102040e00098603a07119600e10400404006015000c5200c0d94600d040260b481560602050350038500d00030400b035000002c841e404281a0b41e0b8501c260310f4071201103681c5a031400c505080301c405038401c00208030500b4400307004000074076000603400640c81c003042c07824181c15403083c0215481103041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 781857032 1250 781855782 781855807
    0x10504110d0219080714100207170c031905012d0e0c030105010609031e020d061e050405010c260a0b01120c020606090109090f060b120a0b0f0606 64
    0x440030480c141e8407803241d040039100041a400500100c1540c0c03100b0301c2c0c400140b0001c002054001c5940e0004007010b402d80e039a0078440c40c850b465003000050ba0040e40100800148002c42202c60303800700c41950541c421000c0060700b48400c0085540307080888003005010721600713100d0031003021340d01d1403201d82c00c61038410410b413070026404088015540e54003aa1a13113500a10401d176600340000c008000d9503864541c0500b031400c00d1300041e0360084940303801e42302d8125003010000d50a5001000340b0501e105503550140506003003103015260403040900785081c0d01070340c00354038003075480f490000c06c4501c54514020007000c0721b10107130740e03a017154450251480048610b4150300b05560080108802a1071401a55503500d044902182180381959500344194040384035401910111034120300c030f076681c605000c02c0d1080071754041c00d032000800c00e01c4002461503000e20001207010b0010340c0300074032a15401d030030101184000d440b60103950042000082410003010342c403050807161181401a0340c041c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 781858282 1250 781857032 781857053
    0x1b0a030c0311070806130c08060106140d090501020307111606051c090209280c0f0f0306050d05030702090f0408040311310605011e03051b0c1509010504 67
    0x6400d2000e80100d44500020a0041c100942610720450304c007400c00c0b820464a45e21051010703120070042402c0408d8401c0e020400e507040f40e100b9070716610200765030400038940e68440e0910000160f500d0060100240082c0082d42c41813815803108801c0b20340704030505092940b103130084064100b4a4205110064204041e00d41c5114481600d0750b81701446c040302c100070407110001a500a405008000d0207410f05410401d07078585a00070804400070040082c002c2e200e44280400100313011003a400c10302031007036213004011f0340a481c0101d500742e90344011170710329200e18005407601e4000042c80f4041d0f013481c135010340d0000b04803202540185029121030a05000b14007008060703171a100912840c903520000c064800b444421510200d6240d000c619907518442c510103e21a2400c0400000b1958041c18010520886d443c40e284105607041e00304900900c001029030f0511010a901c034005054400e000e08011186030b0000d1801107401990301120282c0100028440d030304140c200300000d41070016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 781859532 1250 781858282 781858307
    0x1401201015050a0b0304050f030f0711030a2117070f0201050c03011a0c010204050603070801050111300d0f05010302010207090908040b0d0f051f0b4306021b0a03 71
    0x2401031712a02e45152603818000d4454070400783d48408108001215202d5005103003003031040101d0010f07601d40303505060302c807580d09402801403600b01070101c0e80d0010f00740b400204c0c4000d40c90501514064948400d0341030704141c420400042804141d03c0c03526809109294201600b14010343c1598907002c000c10020016603407050000301c02081840140009406940c082c140041a0685070b01d041d040007462040c0900c03130580010450403c00b4910000801c0800f010103042c1c60007c02ca00c4001d51031362040700d14640c0d00200702400c00000c54890064421040c41c1c45070042e01003071952441c00024903011403500a280c56925280d4044000f9103200d003245c00b1103502a504a40351014400312000814a114481f04072a00b00410000d4445c1c55118021800004003403602d030031a1a0504a0f241f40102c1140010013404a5080009402c49080c4020008216208a070301040510351302c810200c0c500904541081e0046805024011601002e2001d850440014040c21000e0340b0014507000c41d054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 781860782 1250 781859532 781859549
    0x10e0c0a05040e1c080604050f150f0315010b041a0a0c030c0204091e0302010608030901020c0d0f02130e010b01110307060f1d1b03070501091401201015050a 69
    0x1050401c0038a410301c0241444110030049040880c0b9081005c1c00f14881114500d10a82c0740c50005006040e8166125004405041c002d5194514030010320084001141d501d03035041c8203c1080c40042c80000f24071034041c3c0f025103c1240c8444c5402c1d1340744002044d00b408200f00c100240103041c00b880d800860354111942501d0401c80284d01d42c00440c00812442c10007130b1580d4102a45508108608a04c02d806280300e540208143c6945600681d00d03400b03038420240c0103030054148078085140c101c4035600d0b4140604101d0b4001d000c2c9a00140d200d5510280c404000d0b6211820b200380302c40c0a00ca0200c1c03124003820080000d4040e00e80007070301c030b22803444000c05d156903401101481c404254440848000800e141e001403604110303916548850080e598403403402050ba801805090200b21070044410603142c4200040c20080c007055241c022084031070400c1b002c2444a00c0c039122000608d06a00c000801078242070000040f141d05032011071079280c5032450201010401a115a41701c0000c032070780c81 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 781862032 1250 781860782 781860791
    0x30d0c060b120c03060108030301050a050909010f140f01060906080c0310170a060f1a011409060a0c0b0601110319120204260a030905061605120309010e0c0a0504 71
    0x1480d00500400e40081d500341c0101540795501070312080041d19500c003510072001c4650503a610710700d4a070b0307904c400d0042ca500610105004c1001c4c1c10203405054211012100104440c200d001110044410706421605580749281c2480314000340a0314940c050501490300030a01d909180015010341c1c006041203c410000000083c01244c44200f10b8000e08514600015a1396888129a03900c0c07450120a0340c801d490207404d0426044a440313040602000d840e07291030000038000040d2518a40783c180401c00900070000c1d0a600d964000042800d210242c403520000b040c207041480c0461710003407100f0705100c14a1a160789562000055442002a4401d820401d150400c01181c000d45584000300d041400460081784440941280c0010394940300e1004006400d141ca90320b03aa005110070140c003040e8080c100788101d090030390050044c04102e00007402c4680c8290707a054642200700d030b000003021742c1c04803d12117042401e000d10b40c0810124070003040c00c110700b1400107907008184e105951150740e49 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 781863282 1250 781862032 781862057
    0x80c030a1e021005030a06080102041503110f0415030c080f010918020307090b03061006080f1308070b060906010534140a12031a12160803090310050105030d 69
    0x1c10200c41840c1d030303028120b03001850910b00c019245030815a4004a004c0c100440810918070520a40c0c046940b035207901002c500802000740c000301400700241c40d942804014080c000b074900b8000300000d081600010089100034000141110348035100724042206480c20b103c40403940781a154103580c04c400c00000e000300c2c2c070b003503d102d40c8000c141700030f4250241c403c00149074580c952140410070015000e6450356038901d00b010400e10202d00136080030070b102401269034410242d81281c1e0010708040000c82c006480d072603024040e00500011900000e80f042080202e04103d04142c3d0422030a00704541080c04c2d804180f07880c0000b085103075041d100c840a81090030800701046900c05508018810307140c54801c0c480d107845408800007602d10b104c3c0d240307614982038428495414a90039030744146201081210070040e40030800c0718529070740d1050341d0081012043e0b43ca000d84c001c101002c0210f0351440004181810501e080000410a519020040185840108501e80c1421044ca84444e01150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 781864532 1250 781863282 781863323
    0x20f03010e0d03020403110a0308030103031805180406060b03060604050402070515040f260301060c020301060b1309140705190302210105090a05060f0607030314070504050a080c030a 80
    0x8a80300300d0103075032080c01a160000d42d0591300820640340154416569412101c1c1404007030300403880000c126400c1040100046071160b6840700e030a2040c0e504025030541c1ea03100091094580040810094140d81c3c14401085010f01c5144010003c07401030604518003100040c07494083d81c4a624080d90b00005c01c0741c10002d0600c0001c103a010080d89071030307850a150403c0b508000940d10200e644014408510001d1202404103804510141050a1440c1c5c20010100d40b40d0401c3c5004030303015034030342001160204408000d41101e100c40184030114525050140050315a9101040d6001400d6818000030306e83c0102114442d01580d9031811500c07401000840080c4a4070400f40e1003445d0448504c0c5403040468001030407034070102d40c101d207642c0310b2280c0380c0f04803001a0b0f44154400c04c0d0701c60800301403c0c00d074041d104041c02401d001070b00910030080300109400845009000800c0001e042c812443d0103400d450103424220001c00c1380d5154640401d540e4003141502074168080c0e072111606402e0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 781865782 1250 781864532 781864541
    0x50102030a030c0c201509030606040c0e120f01061a07030f180602010903080a0b31020f0c0d0519050d18030e0918150703180f02150f07020f0301 64
    0x51707214580340094000b824600502460041d0014400d00505503031104070040c0d0802c0d105a040e00801504031a00c03440b0401c0000c14074020781106110781c0104440c441d940b00c4602c440d509101002a1580320440e103510740c2107462941000c00c2c884060083d500c00720784090b041e08c40d1503500d41402070a804140c1d60a491908051030440041400081d0100345154107400424502d8441d0300d8055440e2100c80c599404d8401070300141d6046120b00303000002880d22074580c40400c0060300020707040046a621440d040c1d0340030b05050100c003040050400c00443d001c110400d41c0c884a072901600741a80d111268504021101c0000204440410a010842499440043d003000c030801313486018441c43c070300a800c510144591901c074503100c4e80000d1029107141d44401140c60710304047c0584440c180652580c0c003c01408a20416542d9610340600b0000c0715051164240111610350440403684100076003100c107148030520507501413142c2c0c045100c08009807001103038101c41c6803c801c915000440d0050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 781867032 1250 781865782 781865807
    0x312020f0a050f06010b25031407030c0c0803131404020d020c0c0f0604060210091104060308190201020a0f110c0901061106060406080c061308070924050102030a030c 73
    0x28012407440c81c08010b40002c03080c9449500c102a101280e980e02821916401101055070140740c103041c5440c212906d6550081c0c8903446030402c1001e10400c41255034841d0003440d070032008640038803506c07820b01500a500c0b400829245000b1440d124a00e080c0800640d240d200707002c41c082403c42400031070340d25901035854806954070119220704d01d940c47c00d50345180001c80c0d02d008103c3c8090f0554a13081ca40201d409a41440d002050084941c0980b040181550101a9030359040f505141500d90340358001c682c000d60144440c0c944a541c03500c19240d4141744086803070190ba104000760405d264101e28a03084a00c80c0b41400040340d49140c140d42e041000300300c1072580c02030b070349000031800c1500003080b804403441135411a58541c0c0c0389414001254242c0c00b0b030401d0fa9101401d44011441c010006103a6a15000f4221060940e103405003440c120454001e003480300d84640485011002941d0585201c00908052000031403a040c000307505d81c440e002c410410162503e0341660403a01512003100ca4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 781868282 1250 781867032 781867063
    0x613032307211412030c2d03070c0c242006040f060f0c020d0905030712060216080721030c0816032a020f150a05250305010f1e031202 59
    0x5c0340b810440d0740815a104001c40401200f440e0019840c45000e9400e42981c0c01070143d4036031542c2c031800c40599140c0340c84001210100b1b040b100201394001c110024400142ca4101c40c2e0900f40c90742e520180c80b120b1520441c0072080c00f0003e4112200d20300060381900260071110901f046003c0307040c9075000c0c1194002072404503081403420140c030359001071055041e8000e03035510303203506440701c04268541c0b0701c03446041d1500d04110501408506203500400081c10080c0c51140e81c1e20981c0c0d5001c0322038010001c00d071192242d400322041d44241401c1011a00c020a20b000c12241900c0c4801818003c406070100c001030b07503c401040e610701e00039400000414100240c4000c441c1c054244202200b000c81100c41c01070240701040840444000380e100f005c400042d80704805030742d40320700c1030000380700081c5422481240980200d00000750034662808100313403590007007951360500c001d05813500c1056109100e001840440d83c040c0e100c0100854069982c003940003d02c00c04000e404a24200920441500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 781869532 1250 781868282 781868287
    0x80403060c110d080105010806180a0f021b0309130903050313020a09061404270f0203010f1a120601060e0f0409080a0f1704110613032307211412 64
    0x64403130304800280e04a400980e1040ca0035039a410501064030040c480c0354415400071400310706180c0b4260002d4030021030800300182400000c045241b80c01100d00c200c140507800010b0008030509094518200a4480200a00046149540003031091000a01d4100d1040f43ca403000c0c0d003107640303030321a11004203071000e0103001807030315414074480e650445242c0034851031600804a000301d8012020b44c405805e0400f040401400c07980b40d001d4840e85000c0b040342c1c50b558030840d50540314a284602075104002c4200c080310030072001c1c280070240c9074007140e05d03000351301400041014a510021400003800255444c8140c8a80d060100c0c000c3e01040380d00414100300800e10700700c80782c2c1c0000580c64900007a9203c0c40d4402112107440c4030074500341d5001c2e080c0e4043d080c07404000e08200c00141141d180c4c04002808603550380d00d0300d40030004541350417a882d09c0c10300d02103140b00b030081040f0303030140c1115440c01c00405c88030744807001142111a4000d00043d03042c1c1d81c0c3c122145040c84102e040e054a6000d01d50f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 781870782 1250 781869532 781869553
    0x150605031b09090f0c090c04080304090207120215070507140a06020307081302010504050402032502031b12180d1407030201030c0e0a0e0a0216050d1b080403060c11 72
    0x80100807501032150162071840005a040c00c400142540700201d00382c00b610340402440d09104940c0300041c104080d0001c108800207880104000400040401000042e2550000e16000c3e00d80c0800d80200c208650104000744e2645880526107034000007241000ea07602c4100d40307008043c103a4504c081003070310302400300c3c00c805000c030f80d0300198480c402c0c940e5012004d50380d41055600707040c11b1460290010314140414080d41c03c141d401560840401070052036016081081952048450888440140c0001c03d842070003440e4148944000407074140a0203e05c040c09032481094000c8070304136680b0300c456106503503254458001c03045003180c00800320703008010703201c00403907a038202840100d00182c58440e02c086484d20403400d00009002c0104503001c607e251019028070341c04050030100c00f1a40c2080321008180c0c10340c15408143e8811805004502c081c05405004205003000020800d842401c2c2d65000603582000c80b0103490340311000203040d00011908a400103d5000180c0d150700c596403000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 781872032 1250 781870782 781870813
    0xd0f030f0b150d05010509040314130915180204050609040207030c051002041e03020d2013090c0f03050a0b0702100f021330080c1507030515010c15060503 68
    0x40020f050243c0061010780d80c0c0383c0501c840004200ca010b00042c42c000074807400b034103280c401004050300a440e024100c07500c503560030084500300c540012465100780c000b0090f4107404801e5803101052900110709080c030700340102e00580700d4044110300c0f031540014000d0415000f4900050240e0300201240c105521295100c0000e600034010650175001540c9209400314190300d9600035a58081d2001041c83e026030b0b50407140d0801c4408003a82c1701e0f42c1c4195000c0c1c40d2a0840c21030341c11083d00381c010800d0f01c1d46052083c0d4441c0719030060820070f0b591310020b001040e4006030444040741d000380d400c112031340c451504074103044110790001c0d015820070300d113003072400d056401034586401c3d501c41d0441400d03501c80c442c1d100d0001c0d0002c018060300e450140d014070300c0c414040c03c10700f070b50046000e02e280ca0914006c6a081c26080f080c180c0341e412050f0103114400f60301d8880c0980c421009494151040c400d0b2002070001200c00c0c070020900702a42c04111140c0c2520b8001c0c2c001800e0280840303050b1003400010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 781873282 1250 781872032 781872037
    0x1050d021b0313080a1713170a03180f0303080405010b0d03091805150f0d0501230f01030b0c0313020a03031d0901030f0b041b060905120d0f030f0b15 66
    0x2c49036005010703400031907134034800700c2c80e01c1040d41e0203404601d01d401041480b02d902e400844100391074104440c40041d00c1070200941c0d148400a00c40039040c144402d05e0007502c1c036103445100505c4140200021b00850f44100c1080d030a80f40c150030f0400480d80e0b5440e00c1c9014085400e111500b0a404088500402d0b4114862100790741b03d100c00c0100c4100f15490510480d80119a40858845000d0881603e420198071a4540d030101610000030b840c3d007038a0706825503c07005007110381000034504146005204100c140d800c030a8850113401607514540341c2c0440c0041c0a4000707060203030004045962601c5207580500607030f0303010705203038107140d503d040c090843d00111001e0540c11018180d588098900000c003035058035888000c20707102c40000c2e101c400c0b101c00700600855664400004034034003152805d0030480100402d98410340b505040106008000811140c240c241d94000440818419045a0584103500144c6000500d00040030050405000302140c080e800000c6440c0f070310410700c0f48400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 781874532 1250 781873282 781873297
    0xb09072c0a0b0f01050904150e04050f1902010305060a0e0718050a030302152e03110414160e060403150507140703050307091d0a0e06090c01050d021b03 67
    0x44011507541d0949482554461116690b10402c00a52481c0c95130142019080760780300074000040c400700d0b04003401d02c00006a000301c1a80400201000108507040104192a040303c1016043d4003a0030080300d41c0104c94200002d05240e190780c006895174075410031640c028034481c41d0380e28441c03c0240019100c03101c0c8807803403d11003508800118244c2070001c4500103c07513140d0300409040b100b030902d50b08210310151094120380c4030a103001c69101c0800d04c210382c010308040d4206a203507285185c40348800450110f201d0282e42400c1070703500b4441d0a00345290784901c01038080c200710080158201e8190051407141d43c0d10140205010060090030008208010f040ca10204420346034200b05483c4d07512080f0030008541c8041140400180c072803009141c22842904040c02d02c1c0f612000103c10a400712a603071039000920000304481e0b41d40c4ca000e00500748040a000c2c100c1c0b41800e8560703030389504c6205545ca051050000c0e43c00e4200c2c080d50304035146c1700031600d1024107011056907101c0e142c1c2d11002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 781875782 1250 781874532 781874609
    0x1e07050702040f1a04090501061e0608010905010317071518030806030307020603071b120327080405010e0f04090308090d0203180904080c0f10060b040e040b0907 71
    0x200403803000f0b0303540c4248400c20510600c40740300c1c01c58603c2000080c0600942c2202c0c1e65490707280000314664644d0f01d07810003e034400e07849104981404401002d80c08141c0c07000e01c0721400e1a00400210340700c540a01c803078562010300150759002c2c40c00c1400103000c102803082829440d0403840250710010700c00c0303006824401d9641091507145c40040503070b00c1c002e400020b0362090041021921791030140e541c60340e0120342071200c5a803500301a201d00209140c206045000320751a0300d09070301600d150410040403825090071800e441007098860700c060340518086c0301c0c144694429864801e0791004242021404010700070700107083c01c1d1030010071071001a269500c3d6882410000380301d01e400401540c085095010003150700b040000d0800038250030141c402d6840702030421440b03050a9090003a142c5280300f090050001804070700c0368404a50150b8411904040180400e00c280b054129103036810075085801e04c0c4440d15515071103800c1501c00e9103c1d0500000403506800e1f44c02a40c04011850074060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 781877032 1250 781875782 781875791
    0xc061218050d0503100f0305010203040b091603060c050f0301171c020303060d140618120a020a060b010302040e0a050105030d09080c010804060f0e0105161103040902031e0705070204 80
    0x4031525940111050300c024000c0e00108400c0c015240300740013640d40035850704030b400107030f82d903404011a01d148241c03c255030350b03500041003200380b000a1040036006600400101002e1107500d0b08409880e03e5070000404180d140c003105d54040d031194080e00c25015030b80411540d40d59684540e9100054410080e090074001d201d004095103a0f1003043c0765110030540c000d5071441e82c400c07003000f644010b04841200c0c26401303141036041d0a603041080178420f0481d21510384500341c0003441e0741e10703010b0940c4844030f01010400446056941c0400d140140030340c0300c2c078003040780050b920058000c0d0195030002c030b04d003a10720320400140e07110030b401490403210300703a0680b2460074049400711503240b151f014034040746c0d10440301c3c1d600703c0d403141c4600f03540240201c000081550180203008291505121074000c5031707449000307020407400045070306141039245092800c002782c28000c50545030302652281c445100c1d80800060031080100700e5500f4124115134a000982c43e05010240883d00305007c280d01603440d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 781878282 1250 781877032 781877051
    0x1118030303060d08070c1701090209061c03120207021f030506040902102d09031b03120c050f151e1005100e0a0806010e1b07080c0a0c0612 61
    0x110440380291405802c2c4900103040e504c03101d4041e03200310700c11102c4107808400010a101e10765182c00110600340004980f18407240104800c0070805040301d4410700c420996506115890394507218416450b04151603d2103518403000000d008400019401c4403050044202288031700781e0b943c26008040d1820040c40d2104e605100481e050303030700025040302c0c500c9520500180118a07101c00c00b40b0b01c07c96184140b04a89070020528944080c3c0b101041000f0b906108211160220030122201c038000000110b04e180c40f15106600c840d549001071145500d5180248801032000e10200b8104030f049036030310b000160440c40c2c4154111000e41001c4140c2840540540c400c090540c0100e01914180b20305904100802c4a00510001088244407091441c0040e9403075807000c0100601e03901c009020550b24040380c0d98a2200010b2450b048494240a4911040300c1c580580d41c0d002e07040b50246840c0c0c0e86410000749007880c101809400c1e415280000140c03180e0180ca0360021500d08130341030041004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 781879532 1250 781878282 781878289
    0xc0b0d051b0306400c0306091103010905040c0308030c12130201082707090f0c2c04110313060e070b030402040f020f031305160b0a030c0201020405041118 68
    0x41d03c00c00e901040c403480803220b119070054092002444480f80005803400b00800d0000504060443d20b03825842d460311181030b42e01442940018455400103012401001d02d09002a00c014010394030207665400200d000e011101c1040c8000e5540405000c0d07036810941c46c5114150070010407007500550b0300002485080320341424120091b8183c44084264a5000b92a54502817640400500203200d04800d02c41c4001003041c0f6000b000540310000d0341c1d403148000b80301940c6c41d51200700180400d4070b10401d001005100e100c4002809410720b5000490b0000c000f60180208003068464000b0120512010014590003201081d02c55101000350742c0c03210035501d485100c184101044030005000103005030030142c20071101032081c140010b10b08941c6071000030b0355801c01d440c6100d070340140c0c09018042080810540007141d01110030110440d00e09400c090242c03140320071000c00c240d2140308042c5118001d40554000d440010810312206c040c2050544454101c3c0c100b038a0458845c1080c00340c60304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 781880782 1250 781879532 781879537
    0x9090705030d0207091104150305060f0301060f080606010e06030f13080d0c08091f020f120c0a11060f01050409060b030d020f12031302010f021009080909070201060608060d0c0b0d051b 81
    0x132348402d003610351424075880c00c1d002441c004240303542000111194081ca0741d028410340e0081c12040081d041804d0600103000d00d0888024203ca0500072458280116582c8a6007500e03400244519041d03038994401074699900701c41540001c0c40460003003005110340040d9080503d6030140381d81c1c2c0750306595030030050a54682501a0f1300d41882c01127070350007002c401a6002400310182c00d42000c0e10308440d424000c12007000403035410f0446040411854103c980c460a2940e142900700d0081025040c1010303281901041032042902c9103944541000070407880360001e0340e07140002001d895003448a8000a51250100001d0251600030354404003945d04040058a00078a6075814081212101e5401507405070718243c240307001e501c00d14124407001100c41c050544101c0c0726403000b5031202d40403003c2c890040c0000c0d140307000396410a03100b40f02c0250300040c2640d200c0d204803920210360f1114184a00a0342250300001048240001e480800608030b411060155010209071044103410780910981c50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 781882032 1250 781880782 781880789
    0x504021008040c0501030b0303090604031b0807060f0305040212100f0b01170408070507240306080a0203101508060c0702010f0804152d06080c10080609090705030d0207091104 77
    0x34030f440e00504c4154400ea01c07040e2000750240c112071602e4015000554180c000b0b40c011101c81300040202c00b034162240c0c18240040031100c0040800904014025003ca12403500d003030101a40c910000301595620680e08800e1803c00003038458403d00781c0c920001074190010070030401070601000200700e5124640480540702e5006642c001c1e52035503510105030380d102d20401e4405219840c0c000c10460440d40ca2100030320b000a80c10815103070f801002805444240d88135a199070403410551001d6200800c0602c810081d100c000184d001800403100581c4000c0c1c0c04c410140e1240c03508100750f1f031080000810485000343c0358216140c0202d50110b0f107103032080b60028001e00c4d04541d940c10b02c0e103207600081032140200003002d403921240f5200803040d1480349110035a440d1030b440d040041039424010901305000503115034542c4065040003424855000d012030740500041c00000385129402c0c492070016003130040035215907001000000703548010300d000340a02d60746040c0410b414041c00f442120104c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 781883282 1250 781882032 781882043
    0xc0f050408071521090b06040203071d06040f080c040e0f0709180b0c09152a030717070b06180a1d0601090c0207080d05040315060506030406050402100804 68
    0x40c1401d102c1003e400c1c46042e10702c2801d001040503c0010254403100310302e02e02078a8040002d0400c014140600240d1000d403944e401584100148020a07600118085400704a132910b11242103185021a10a100d9680014065a42c41e640441d1480010a204a20410840707052000b503145019658841c3c801003038030a01d5601c0388404203c2440d654000e442e40a81d60420032143d1000794441e560340381c0c0d08a4464140b0304000650441c18584403c05001e42040000c1c0e0b10b0030010106040c42e00c1007807150304a038540104842d040c420050800803105480d502c07900251030503c0003a80c40105420482c1d084601c1440a80001c1003424890050030f6030701c1001d1909c500503100d89040c08000c0898072a0b0b404031103042c030400c8603400b00412459000b00f0362410002a5104c0404000717040c0161034005004d03541014402001c4a075100741a035060340d81109030500140069013140008104543c80103401680100420085c40100c1d0b0055102e5030003991882c8a05c0d4400100702d400c2038007110010407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 781884532 1250 781883282 781883293
    0x50901140103120e030a0b01090c08040308130c17010501051f090b0325270b1207021c02160e07080c0306010504032a050d050d0e220c0f050408 63
    0x200f980c0c074400341c1e1000c0c40d50a14901d09020382d07003c41e040c144140001e413059035a042c01084001038620070060310003a0fa2810010f070741041d603002040e206000d07020901c00101c00610006120031401800018449422443c0a4031b015400c240c0c060311092040320303c5030202c02c1908160020340c1c1d803076107d1061603944458246081042c11007a81c1c10207003494017071081180b4002038808148108d2035140e005900c5007286010005441490b0aa104410035821140f41904203c080c0640341502c00d414405d038000328a41e42c544070105d1400110180d0358200648141200000303a4011400440410480b5184851182c960300c1c405c02d4030400780e80100004084a000402035000d102c043d54000c801494124038007a030b21b454420003911445610105010f8000b1082d802c001c1700316559004010a80f940140420b894030703a00c0c1c60b4440b50010700244600320040c0300c00b6036600060030b2a03000c4090200d901a0285041801c001d02c680b01c81040415141c140e000b035028000d90507217080381c440000500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 781885782 1250 781884532 781884539
    0xe010e1908041505091206010f050a03050319050c120903010c050f0a030e071806140f0603040609050109170c0c041a0105090402040b0313110609010c031b0b070f02010509011401 78
    0x100726107000d9000c1c401300304003030041900c03582c0c03451103e04020215100030141541041075061600807a0340c0410700c140b41d02e507801c0000610100981d00407801d016140d172946040360400303842c940316000c801a0b03180502d5136580c0c40035402c4009404070324030540007000210500b8000b503581d81701d0518a80d00d81502803000e081e216200e13030441c40b856040481501d24480d50359140c081c1c0c0381415104001019105e1106000840b284100c062091604540b13080b080070a204c0070501b64440640081c115a032542803241c14882c0035007040f404141d008010700c80743c1d00040155a1107400c0f60082c400325000d14040d1504070b28043c01100d100907141012203040380c01001c010743e9158803042215803c16024031002408030b000300302840c4104200a2002000c0b02c862410203424410080c0f02403254209024443d0140da0080c0c601000035414140030340d10610320902c1601c20341964600510182c081003c01541c564001031408a40f515600203100d1a218003400e6401e80e800c1b0102007014004480040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 781887032 1250 781885782 781885799
    0x24080606070606090608030d0f09021c06110a03290609060a03060915080f0706080a05040f06050408180a050d0b0606040812030133050c0c040e010e190804 68
    0x5100706442510000b4a66580e14600f200340c0b021580481724507013002c82c2180891006010b0105500100d6204210344480c1c1da001896002079610040c05440400c0100401c11a00340e104855011410322a41d403a41c41e00d0f04010040e04440d1006c2d0703400301040d1000004059003100f85059041c0003800303541440f00c404288030702900400b02c044201610748400152882042c0701d95006005512040d0302e0f583d0402c00124a00510390f80842130607400340b5020080c3d164051000c54104400b0600402c02d40c80e0360030607500410100782d000c0c2080345040f0502c030401c13030840010649a45186440c42ea0003221a082242c10707602482280d41180ba4902c074030b00058130882500c0e6011030018000340c14103440c0e0121074900800c42081604104001005100401e0038282031001580c00910360809440d4403260f14006070004c40d0381d001030040200c2c0806c4810818010820043c0001d0030030842d8102216600707002e802140c0c0e500b946400341c00001030026640d980c41210a5802003000c618013803910b00704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 781888282 1250 781887032 781887037
    0x717060102060609060607020d050705120319030b010e100e03060709080604120c051c030516020c091b070602090405070e010801060f020304090203010618050f0a0605090a09140124080606 82
    0x1642e5004030200a03c7c0011381e82c0c01a0381211502030340042c01c030f0a042500340705195510418800b03040d40b06205d084100c2d4400121040d024810f460b0105460781782030010381d48401e289007901d500c2541c146450448907880700c40c00d00107580450032a2100e44400d002a03d0340060740c010184142c0010300040d000c10700141500104105514091030320709125100c203418081c0202051030842c0144001c0307000b103541341c0209034010414032001404016540ea000c1c1d5141c0c1c0010740580550300b050005040c10780000b0b0915450301081c14041d5440c0507501d8010025800607030f01c01e1040f0b2401003c41d40701840f5500d003212004042e100d0485036400c1901c10744417003c12a14030340445c0300801000c10380700e02c24000b46009140d203444194451110303546a420341401c0f60085400b442401220440565450b0086412070b0780c03600341199035200c01c1012445500068014155180c02e108158411404001b80c0d00e0407180b41c4849040d4004800c010810701a00404409000404d440042101071504800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 781889532 1250 781888282 781888291
    0x905061504080706180b040605070605010503060f071808060a0606081003021804050328030e12030c0c0f0f06100608091e0a0c06030c0f05040803040909170706050717060102060609 79
    0x1500c1203a00d03a1106c020f142035015401a50014030042008010403a460140b01e02404044014010518014aa440a2030380080c40c20042000340018990404c03a01c6210001400111040d282c0342d1400c0300c14000646005e1013100001410600003030182700041507240281e9034010150780702c105401c98122481c98001d84140d400d4081081b00c10000307004000b60050075038034400d03801100d48a10601400325000984012666040111866141c100a00460b030784400c1d944c1d0000d0700c802c06000140d203460f441880400e44c5205111050200010000e41a4805c01e850110303814425101c08085400b400281d415410551111814003600401003820070420618402103488100081c0c984c404042c8807540940082640c68280170040b80c2d000781d45514400c0ca9090143c42c041ca841e207026540d200d039105100310542d4400c1c8081c20845151000000c01d5000c003100d54464040381000e5005102c2940c2040105031504900d400050154000b503204d100160041c181a644403418000c82c070000a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 781890782 1250 781889532 781889567
    0x1120314030421051c0203091e07090507141204020d020409061a0d080409051f06020106060f0e0906090a0f09050f0f07300c0905061504080706 63
    0x603a000248521080618421030003007601582d28203001c1c9600c2e4482055454030702c00c1002c200034009600450074545103c41568080050303490f954008201d0501d400035182d601d1a028007170300004010000a2444165003444108000e00d0315102c80c156801c6101201c1e0a1600c83c00303200040380e40c2c0702c044549601038009003038155501d00c00d500040c12031750f58200460b1b1301a030b00c1101a001502c0c490788400c2c141403d49490715117100d540c544480034012842428034079901d58000a030000c0c64082440703847e4102501070b41003075480b400003034043c1c0030380d00406c0f00064000340c3c0d071180c00d40300d203034501080c0001502500300d90300c070f110074000c5000d0000d100c180700c2030f00c1e0800084010b046209800031940903001404000c6400b00945040841800c0207160341c1c0d10844052000c02e064508a158010001100d1040d81c00e400c0c1e000c0708840c909000180503d0b08c0301c9000610415150411072182d0300032141d40e44071290049501e1154002c034050b80c29680d1141d88180800360160100d03602c4010641c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 781892032 1250 781890782 781890797
    0x5010f210612060e300c030c0604140c030606060304080a0c080d02040f0b04030b280c0c0302061b030109021c02030103030302070b010807080c01050f1b0f1014011203 73
    0x21142c108040c40e05010480c0c1c01540d03541c40160545060000c0d68141034152900d440016140d2162a0b00311501800802d6903500021640c40c84c4404000315401607211405076012843c15040214842200c1d10000c034481c010881c60030900d150103d00c807071054000804441c02c54680d80c0310b0100c00c1d0001e205840506c040c014041000c076200402508001c3c004000c090381d40c1c0d040c0303111401c040d152a03001a11a1f4003d12080c8005a6684112540a8031108800700e0240c44440e07600c20865824002c0780320185003112402e00d05034801e24401555010ba001c46005031955500e180710108119001540c1d11801d00040c8400141500140746079021805034001c03900e101507115080764820307401200829400640c800030041e031521128010003040e005011003a02d045c51054071058200142030400000041007603000e050310b4140e840309039000803081100002c14601603035a9800000c610407a200742d1146a01010550044038000825601307402d85903403030f00070240307012001e4420441c00e00000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 781893282 1250 781892032 781892039
    0x102070206070f050c180142021e0703030314130b0c091203030a06060504081f0f0c0e03120a021c110f06101a03040b1f030b0402030705010f2106 64
    0x80200f481246c100c1c841c0da21a003035151400b5818100002c0341200030032882d0481003d031042440c080500b00315980441403d402d01328600481c10702e5507031240780c0650904004000303264100060800142ca02c01d4170704005071034106035540c000c40003c41e0590f8101600660384000240b150301d81075002020040d1071410010030100281e0a140c80001a40b2643d00100411503441c020707014800041007513007829403429040050490f107038651200c0c1e00c1400d809038111180c4a0246038050705100203808030800050040c01c20091144180c3c41034a1301c079204601c0f6404d49502d5500c111102050660002c4c20f824800b0540b180080c180054920300744010b82c0842c4035204014031150300d10703280c01c0c0042c000b10b00d01400503039001e0170542c210302c00c0307504004032141040140c0400c8a4005400131489059643c44288980c02915604285841c655081c0c000104100317a00031050701641c400c905035021103465000444e01c0b82207101401c0001040c0044403400e4a0341c403107045401d10001d00d00845d01684 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 781894532 1250 781893282 781893289
    0xb062a010f02130609290702040f02220b04030201030b0301020705060106090806070309031d030a02060d09020108011202030a0b150405011410030606080712090f0b180102070206070f050c 82
    0x401c0821410920b4000503800016526500440042c00c4a4100074203103904009140303019181d00b4002c0390000040a2a4503001000d50050f079540d0f070390081c01808800c1400340c51001940014464801d511001c1c0c1c071001034090b115000380e003038942e0070100c641450710356001100913000c402405038140d5820000b4401160341480b140e4041c02080e207505844070718010010380752031401080002050703e0008038100280c1d0248a2042115a05108041c1041043c000900b0b0484007403000b980010b000449414440d0150030241506001342c0341c1c9a0aa80c1e40d284081c1c2d0102d10f8100254907400c0389411800041c4185129900018a0341890b280041c2e81d00214048520a07000300311098800a00e0909601d40104010006000740c07030300b841002c0c038188026201c048088c05010512606031031556109d03290340e10601c17100c1e400c0030030030942403903600703042442d1305041c6c44003900c0701030170319805040c1581402125581d50340548140e10b4400180c6450403803118280d4101e5541c0105000b8061070f40c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 781895782 1250 781894532 781894541
    0x22206091a0108070807091427010f05120a171905271503061210090c0503030c030403030c0206041d0a0b030d090902031b0d020403060f0b062a01 64
    0x7155418000c07211248005001c030f0400503e04410002c0030803c1050340e9501c0251001200c0090030581310440c202c10005089610440d00020400c210101c81c070b00b003e088201c501c1c100e0b0b00c046002609292507406014844100d100e40807a0b5030306c00451100001d83c0401004400d140d000700d640d062010071560000080c8121a02c03400017a0f012690718181010408400c003a80c9980c854183c84c80500310118007954071001d48180200804400903040b41c444c0c58501c500850319400303440c2c01c100d60318101d000400d2954001c1d2408955440d011445080002c125001c2c48007840045d814149199401c84409464440403600300364103020005142c00f0240d01c80200040e042140700c81031408a00c0345088490301c200c40e40c42680100f8190840c150007e0444068656800000da0b8070780c4c400300e401050590603801d1601411002070358a041c50819400781060b2841420280281c43c9040c62510680700f60399103144d0710600030051444081452786403619102c0c184242802c40d103c0d1130881c10b0850303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 781897032 1250 781895782 781895801
    0x305101d22170904060501031406010c0201020c190e0a05190c1205011d0a050613090f05120406140f031315060603150512121803030328050402220609 66
    0x840803c0d0880700d40b81600170300002d000280703000c004ea5410300c613400c000004007030841c40c1840104400e0005591003030140e1050490090245c003c0c240280e0481030ba50b00813803080e1318601c407841020032103100240c020f15000d0304200c0d00c4070301500646172409008000e0032011006105a00c1941080c49038507001d45402800240e0300981c0c0070629441041c80144024041c0c13113810320b00340421a4581d034002104020218903007001840d92400c0c5070103000034482190140c050712644c1007994103983c07140020801d0701d4250f81d499401c0071030450386210a00858540150102e001e000182d20342c1d483c071260442c4907010f91411244120503502504c00c803202d9030080c000081d160090f9111100030024840c4c0241001d80da2040c080341105880c0341c0f90444c0886922940500282c480d030217031a5403030000d4884000401380ca80d00e003081c0302d014154080400392005042c5500d54800e0950305030b481010712958000d4507913002008000b00b51b03511880702200c81c101c1940c0e2400b01145480c00e43c802c01e03000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 781898282 1250 781897032 781897073
    0x901110c040c08160f1e030204180c02102c160602032703030d0b030a0c060806010305070206070c0210020f031c060506031005090408090405070305101d22 68
    0x394105442a130080d2000100c1d01000e028070780c5210003009502c8950f500700c007000840d041114050f0007000701c1c0603218a41c4244201000540c2c40b1030511129030003101e91035440d40884802034a00b00084040da488986900180c5a06084105270850003070b215021240341c01095464014079020703171800c004560b4101c2401030303001060309401e1486102094265501e10903102c1880030b25500000d90368440c412035900c140d034488040043c191010000c032420300d84d10890b84844c603920340c503004111000c01c480d0503000a003444003040c0107900208541d4050300c0130ba03a4003004400b40e9001e20040c1706504100504500c1012000903003110240043e00d18000d08400302158586820b584000365a0f890308001d105c1e940030014051504065042d40007110400d41e4280443d644a003000b0f6014040c0d00ca0441d041410b0504000145503d0fa0147c0e200749400740d1104c1d1402d803101c5156080c4403406007600e180b1001e0001007505008040c1d00b858003c0322101409803409840ea4811514500c01d2030300280 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 781899532 1250 781898282 781898297
    0xa0501060501020d1701210c060804030315081e0c100e090c03060d030309060f1d0105220b10050307060801170a080a0305090c150a230901110c040c 65
    0x815a418000c50003200c8136864941728944241c2144d00500106200d240c100c0301c2503400c0400d141491000d00340009800446ca020b425070385240c0a00450801c0380d0450000c2e1800190004810140008405440c02c02c0020702c0400490146080750300c4c1c000c43c001c0e00c1da20500814800316501c41034000c410071081d94410420701c0c020001c0c4004280003410f03009100d502801080f685483c0c400710080896018540403440110030301b807410040611020030020301d820804410102c0d6034403561003408801aa008010b9540d071903000b019512640003100d9842c4a500d0241c4000c54011708955410200700e020b0300e000f40c0d6551000034604440d9038030410224104400402c8040c98001c050700030780840c9406440303803d403107580d0500c0d03612900d021032061541e64004608211410401c19a6140d0040d180a039101004000b21840381c004440c4480040d0390010300c0050540d10045e030b0078034000c036100203d04110f12103005441c0810120050a80b40c03144404000c625542e500a034a02c4014503200c1e000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 781900782 1250 781899532 781899539
    0x4200d17211008011104141005070c140f03010501060f05090307050904051c0e0d12110d02010f0b04060b0306040e250317031003030e03010603050106030c0603060608091507110a050106 81
    0x6082d0f805c04c098010400e202070104121020700034000c9402010103c802d80f202141007001560710303001c1c042d009804441c0c4a000803820302410382e540c1c2000801104c0e05605d210148007010709071a82400b503040001c6820b02c0108034580544085c0100c140c004003554802501c0340042503529200310350641c0c00340d006102803380d4506c144440500d4079014a041220b990281e008660722904140005200e480f6124150103130741c1c4111030709082d1074003035402d50310100342100c0000d02802e52120b02a1a1070700e41906640785141501c00e690444180c121032a05507600e15003000000c140b03040302c0c91564080e4540000c036040d116040390394040c01c41103510142d0350450a0170b9203454502c1d07500c0301403040304006104810103640501c0c000c6a626280c210a1031118001090140c0040d0b40028000d40c00e00d00c01104200206050704150b07506c603641044410343e90311301190550020b60303201c00300d504510201a0007030302803070f26107a200a503400c25004510030001e21601d840e40c40442a41c06941d03500c07017070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 781902032 1250 781900782 781900799
    0x190506040311030408030403031206090c020c0102010608010b031e011506051312020d020927060405010c08100e0402060906040b1b010b010512060307090504200d172110 74
    0x40c40070b102c442e0001c604190920440980c0c912440c00061305008503c00d0414201ca0280c1210000e015054801d104064004002960303800c4002c003000c0c055400c0180104118a051050030720850b0002c0041400708080c403140d4258141c0d19407071801e55503c2c2c1d045140d0041105803424018021a40e449580c0c03240308031402a5110241c21004c00281c0354507000d000350755804000c030361290f0101ca105050303864001860180312524030340e1094604102c0e5004400701c6012400c54803c0b400b40000b07000356004901c0442d07020001300c0705d1000d05c0350441f50134040841046a81580184094605450030a000002840a40150303104d01c2d6202d60004001318240134010303040c1c003402e10a6009005c200102e0340064641d000c0c00d10b240320384250000020b44507907420400e07031000f00b0150300c04122500741810103039a401e1806151000c3c0700c10b601140d01850070040304000605800c141c000c00451003000c3e1240c45940140d04c080b000d0015451714600f0301c0201c40c0e1050060296115a0f55490300d02030b044d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 781903282 1250 781902032 781902047
    0x9070324060803040f0b160b070c031e02120d0b210c0f06040902090a090507030902031b0a03111201111305061914070c081b03030711060306031905060403 68
    0x2078016070000d0000301701d003070ba50030a1384d41501e05141005e03440e40e4400c1170a05480c00154000b52500d4040c805000a5907000541d14007030310700980e6840c0d52000380b046500c294030500b070042001a8407140d1b1400140c034a8001501820008540200e1842840c40001d1101b00215040c019904010418148520300c10000066001c800350707103d0020000c0000010401d024500c94040d540e07400088100080d5100f0000b14068011120208442d00f081c240080c0200300c4d1041c22030086c0710344501400038400580043c031b07080030010010303000c181c20359681c030380400b00c05004640c0115941c5500c0d148170100303028007450300c0380d6404101c0d100d103541180c6c24689403c40d40300d0350080c0d0080010700c4064084c2260303414143e0742410041c0c42d041034044480d0b25481004809040b41407101e40110301e4640204064204180840c60b40706200d0a05003003548030700c0b034104003c1c00420903c2440d0200d051480c09940c1c03080d40113042d144101020000c1145010004408440d5a003000d000c01040541040c0e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 781904532 1250 781903282 781903289
    0xc0f03190b0f16080103150f11030103050f070b0904020a09030506190609020c03091905060706020307081501050d0915110c0d03060f0e10090c0816050c0a0b0907032406 74
    0x4200f000020000d003e000000c041c080a0400c81010009803200001a000041c1000750b8010402c103c0c82880c4840150303410a000441c0d06d070003110b09048160740005111401d983d00548030368688804007003044020b6111504c42410301c0062400040451010b01c0715030311451182d40900d0989401c2c501020031101980c1001c0d00d0140b050181c2422840000305507a60040251208000100c2c0c50f9800151654242d03c1154402c000003603034420481e640d005540a000f01d030700c406902d034a51340e940000c0350519600301400100203020240c40c5581507000710101d00d00448048260306070f00110b010a0300c540d010300d860000c41c0000e0350300c0028410014440c1d40c1d900d600e4204059401c003094006e036900c0e18890300210004002c045204240340094800c010101c00408000760a003040c030142281804455000b801112444041c04150190f8211a072504a100282141c1012507454415000d006407119a0510880d1004000940311040951001110307a050b00d00813904000445d055034220f80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 781905782 1250 781904532 781904551
    0x602070f0b0a0608030a0c05030d18110105090121062c1f0b0f0409020a0c020316030506131a04050601080d0302040e070f020307020306150a0f080c0f03190b0f 70
    0x103a0070440d0b04c5011040c0c885500b0780c0c0c80c10f1750748040b6501b001031843c05241c0d9884103692404181645071001d100e4083e1f2450301c1181200c1d861200036006582d180508a002404580849a1101d03c061045114121446612030008804d03071141480504ca108829500003070074046286400f90703001c4001625800700a1031142c2c082103c2d84403495800c50503070302c1103003090300003c182c280d02d100120f01134030060322101804640314050988010184074031100182d020b0b014100c04200344641004c1d10304250781d00400248855200c9400a80706500c0080c01520700300c0e0b40c410100b016880c40b81c0e1a40c00786000d58000c040d154148010142030021401500c4241441004100240107980b1541d40d4041000e09200200700c6a0b01803e904501c0b61070402035060084104001000900d403a80c916030150030790f03102030100e4131a209100c030120240296aa81c0d03004540e884501e203401030b10900c0100001c3e05880004c11aa5440c0014440095003143c500e0704240c1000302c0701c80c0f00804c0640c80085003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 781907032 1250 781905782 781905791
    0xf021f020408070e040213150b07080a030506010513031b0308070515180606040518030d06090f0b0604050f040e07060807020c010816080603030c07060c0c0807030b0f040204090602070f0b0a 83
    0x16400544030382c1d1f011024a1a0507200c1c8009030038400581c41d608010602c80000300e41d103c070140341c441595409244030001180c0b61101180242d441001a51101700c0329407001d086503419902c07903040e400310400b00d150020900308004030002d50f0040c0688001c510800040201055051980c0840f41001f000c280d003030116583c2d5841c0e442e20004400f034000d107040c2d030000f40070b80300d000c0c8003004603d2880588030130344000207080c0705000b2664441001c4650213042000068002c80300502580c1300030f400d0540c013502c2030000b1700551406084c0b80d03c400070000c100041301c40b061910315080c0905a881000400e00b9902040320b100d405208a40c0b4a82d801d00e4401c1c1245000c0c0700078290b0300180000d00080001d064000350f2940c500b0011658610242e0080b1085180d86120042601c3c28a0004580f00803075014000340328800014400705481d4400402c1019070ba88001e040e8820000600682e401502d4164402c041a41392000f0000c040c014070740300c44000d20318184480110b04c050060000a846c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 781908282 1250 781907032 781907041
    0x20108010e25080a06060810180605041416080c0406051623160305060c070f06090c1403060912220e040302060a0c08070f021f020408070e 61
    0x14100606589008507201d40507200c50380e0940e030500c004028024890b0110090220407074103e551103116048140040c0141d540301c500c12a03040c1c0054403114284900c03d0024001c98681001208140a110000284440d40d0f90005802d80d60740b00e40034510f075041582030003000c0c00c00c605101954080c5083c8600c4d90708283c00100a0b61080780b1034003003001360200e942c056500c00b030000303c17007050340001409038a4800445a44040d54560b03d50490034031484050304940d01c640e1021004481d04440500445d41e42c03060510303001d40c020710048400c000c55082c0b010028880d4401c41c07900c11b000702c581c810050b0030401801d0031803001ca11340c0c0b031007a80288100042007000007051041e040c102800e1948030301103000c5680b00d54117900c0c298040c2c10986903000c541c410800e10f0f0284682e0283d030840e021a01c0310b10140084074500d40d00540000c240e60005600603004540f03165840007903104980050710350881840c0c81d8240100f0a00f84142c00003410050b50104000000c080d05000407404181e0030b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 781909532 1250 781908282 781908287
    0xc14190201050307210f27020d030504080d080609070c12030b130501331d0109031515060e01170606122e080d18350303040201 56
    0x8100800a042240000002e4403161043c106482814401c4031045041821010a907028080411032044140e1410781c4400302da8038494048810b06070a2401100300540344e4003070060021000f50290309014082000043c80740003040010f40c04080c1c1d948201840c142081008a081c5003e0302030350800800a480e0b4000c40ca0380502102441c400d810001a9a078901c80030031403429600d51040c66541c904400007034103c06496802e503440000014400360f4140411901c8000104140703220002440704030b0b82d6440c5030062003410303d195414148000c59503600c1d40d8a203181806040c0008206072201c0c42e540c109803450140c1e001400030f87c207000035002e030400002462400c03101c016460300c0310b18a01050042e12003800301c403070f030701030400c600000c2d468010700441d0481000c1e035a035100c86180e40a94100400406c4802d0141da003143d000c3e040074503c4820450f52200b86a071202da031807200ca40c0c000781000c0c080242d24510b290550740700244028282021486004918044049400c10410000140c1e07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 781910782 1250 781909532 781909573
    0xf0402060d0510051201050a1d071206110711030d022103041103070e1905070c0305090406050901290a0509060705030f0d02070209181e0109120c14 65
    0x10a500000a9942e905002d10f81c8090003540601d0708102900d404189108040d081140f01d4400792509102c0d018039004004200c03000b0100400c100c0d00045018049415112044402240a000049180a80e00710400990ba00c030560842d9501c0036900c41d000c19080034400c0000b420345500103040d1a4100703000a45c03503503049054103514400004001801c20884030120303c0e500304050210344a058561700d0f0440d4140c003d4a142d00380b884480c10001c0d184e0800c0c00b80c280b08001690b0380310320b04009950140c50f0f42d0488010150300c44c2c1c030340c4008034413038544080b40d60080040710304c4180960001d0121030030855140440e107414040c104114030361140c100d8100c5050f00c50644103103070348416070300b085030540c002c802034003855070400036a00f5420a459005410f0b03103030080324120390130745409908203486000c080703410721140c02c054044940e100b00c1d800c00d6049041c00c0400841c0d03001c5c5603034402407481036800c01031000c02c0c0c25500c8607003070254810489040201e40c07001040f020410039980b07041c44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 781912032 1250 781910782 781910797
    0x93304090c1701121e030305101e0e06011214151801050d15060f24082802040b03090606011b0b28060608101a0d02040e18060f040206 59
    0x1410b8030354411040121041c40070600300c4903044641c5d0a43c0c85843d00901500c01600d1903081c0c9003444d076000c180030100240c282411508186603401c03441c80c0040f10f4804900040502d414003020a2565440390154000c003113180b002003000c54070514200200c50b240b1009451b41500602540c3c0344c04020f0420018064103641045485040e0b041180c03411080542c000300d2402c4205042010021703c24a8000c24403085e64117030b258043c104030300070866009034108000e4102c0011440c40100b09840b11041404d0700401e000c0d041081c0ca00f841c1a240801e81c0e01c143d01842411000100300040801c0c1400a00d4010009203044541c100b081140400c240d00c010780040c0000d001e02d00401e06240c000c101759801c100b001140a02000c0900c10f282e4003d2103103201c1c90001c1044100000c103021b190420703680030341c0c40d0a0446c07c12100366403601c0c4001c2d00004050750119900b0030020440200405c4480e21845c2c680e6401d440040302540e2450500c10b01500382103415120106000c0180d44000603100e50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 781913282 1250 781912032 781912049
    0x11041a09040b13050601090914130302030d11070c0806010f03080c0312011404050c0c0304061202130e090c060702010c0206211608011703093304090c1701 68
    0x31102a4000980240b1003540b10980c09800d00b140d1200304021034000c1489104240ca6484140347d6032150301064515407404000d4104003000001d20f40c8000c0320110004038004c0c4100d030706018080408600315900045801080a40130401404000c48107a0801c090405003001c1c18540d4540941c68a071440d01d4007000f00030f09030114015000400810958098440087d04440e42e56503840d801f61003d800c0c6016140180e00b0300340040c00c0c607501c1d4800c0701d030341800650080d4540f51518604a500060001344512803035020001b514000a1125000020305000a54560300d401e06040c602d10308900305c1c1165001d40300901c801c00c00341c0e8008040400040d01612000d42e50b02c03d00c4ca441030800761010090302d41c91716041c14424103001001910714401000d4948942c030380d8907401d01c43d00c0e82c2c9154103000c0043d0310411001c11079007456483c0724401103404d0000e503c41000c60035030122041d8800d0950740e502402150070840503409004004510409081c4000c4405140d900d041d482407050061440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 781914532 1250 781913282 781913287
    0x10905030a0f110105160f030902030607140403060f0c12090b0103020402030a09060c030c09061701060c05070b0c0a030e010c0f021e09040f0b10080703030f0302040b071511041a 78
    0x11403e0040c00101c9074030038680000c03c110315020403002c140080600800000a03040012130042c24000d1040e076596036002002000c8542e00c0d0b5804484494460590f07900c00304060200000103445c134043d41c400100c040b08049845080e40100501d042c001d040c0000c066420280e04901166228035410b042d650190350140c0e5035650a0000005032020320f000030304c498a404000c80c2c016a040d482260344802c82d42d0740400c920350720300f402c07604c5642072410b03502e41d41d6940004000c0640038082e00e000070340c4100709603520541d50b0140d030003242e007240c1c000d6519a08000040000c15071310540051b5148030908044052031041c1e1942c104660160300000c1c01006040c0e02002e4000d040200007418041c0103000720010700c0d00d858050118081c1440460b4161941e0300403552014841407150103031031980c0018003050346152000c6170003548048800d01450b5007040041207100609006100050080020723048000d02200c20408561140c43c00080c00201803205010440c0d80341401c0104000d81c030040364 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 781915782 1250 781914532 781914557
    0x1c02240a020a0306080f06040b010b07030504090b0a120b010e0f010602190c09021b010b040e0334081810230904050f0108010501150c0615030c0b04090e010905030a 72
    0x30f00620030354024043c0d600c1000308116018100040103480385104070200b10069a9814202040380203070030700100070900a00044c004410b440e403128418000040062001c40d5440011540d03580f1052800da03140850400180311620180d094a07401c4009618540c210307601d00b000003511100420500c5c40840140a21305091000ea0110300e0041c1103000400c40d9100300c01d00304511403901895250708030b9401d0405100040c54036104001034913203d20043d51400ca80c224059910360a00703006684050a19200d5145101440c3c5061010501c1035000039902e07001d10307040d880e50a010318030051040d8040c4020b0f0740c0f0182d114000c2d1800c02881015104c2142503031400903007500441c00110f804c107151800300b041446a108016048490803002042281d03200d00702c4180b000300100c080e10102701000d84000c001601c5510400c104402d0341d41d0320700b4090301c95031602d0040c0b170750b030344501c01305240450280541011841103000c1d18030307000001c0002240555440791280901c400703203000c0c40116502c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 781917032 1250 781915782 781915787
    0x506091314120c030c070b0414060c0f010606030b03010f1a0120030a021c0807080c0f1c02030106020d0203030907030308060a0f0909120e0904231c02240a020a 70
    0x46640055652110f0b03114005078105950342d030000c18030410b26101e030100004102c841d020403202a108000c411843c0c1d0301c00300d410f00803907a100c0c403603500e4144901c000354802d00c03100b0720a40014254a84c1d000c240025084101070030360f0855207031035400350b141c100100540300300c007069a000030740c080c01c04081040703c481d0b94060000109401e00001c1c00001405c052640e4045080c045d1800c0781000c0b20005003c4c118110f5044108a40007000700300c0341da0120360002aa10050b11050101c2a40180b510b00341d81558621558031006203003c503174000c030050007a1601400080344504452000754103503d4131003266a03940c0306034400030f810b124048000c42d0554480008481c042c03c4030b0080c1721002951a26690010409e509051f0303040140d000e10074503d41c1c8109824001c51394018000e028684494036542600c0f07041e1289498010000103004c41c0107481440f07000c0c100441c21030350103400b45071840040c0c1001c07150200e07814821070281c02c1f42e5a001c02042c55035000754602c440141c4500e501d201c10b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 781918282 1250 781917032 781917043
    0x81b041b1416080306040516050a031104090c0810050d1e020f0306040507060905060903101a0a030515010905060d03030504050a021e0112150306050a09080a080a0506091314 76
    0x102e035414a00100c1801800f100c0f02c000d42c01341100f6207080080d640d130618010034610155103201c00041d0100146221107101340c00c24410314103460070141c58650b441c046881125a12000000403c048a04101c0381e041d0b12004840106001d039031f01d08403c0310542c2c038407400c50068401080f40d901e201a0190554031446004001d280c409000c07204103041500700700d580d0b0104c0d842031100140d044407000c54030f408c2c0442916802c81c4041c00410f1309090400c100e40c0035140c441d4800700350620014403400140c1d6038105040c000e40c00340340038040b180c242d40c1070001c2e04803050f003014600c20308060a2000c16200c005003074150301d4040c43c0c000b8a90f01c4516216003002d007103000c040d601101d000810f01040d81211180600312100b600d51280b51202010140141c80307135034440d603520315000c00d410404511550001a4083d04d00d24000403d1507071503981202c03540144844130000f8107900c04200034188035105154201c1c504031107142c0d2600d09005010620500954000c21203e640c00103a049684200807 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 781919532 1250 781918282 781918297
    0x30405130f060b12070c020a0303081b0406030b0a0b2107050d09060b0102192001020709060b131406030103080904020705010e0c0112060f090507020f0304081b041b14 73
    0x2041c002d1650b00c0c0c211042540140d40c0007001c00a4110101da4428028070740014100d601810105180e444c6403004e580200c0001c2040e400103241c46110707140b10100900501c064525520002000070301d01080c030801569580100403140b00130841c0505402010900200c00340604a030407403a07548655080315103000b042c0f050301758241010304010030080580c001038001c410aa0840e58080d01c130050031030b01e40740a0b00000c2d201d080702420150ba003010340c080c42c2d40d540704180101c03149169a02688022100c01d541302001100010a01840c524002103c1200504940301c1c1444100f0380480000e200c1d100602c4020103d40b000142c8010039203c940544090079007100081156980e21955142c55802d0404060b001603c15000c80e03801030003910a0034140c4142800c8034401a003404907420083c44050031010540c800c01000800704d030070400041016110f214080d09102204540040201142d1014244200c0c241224070020358180281031904003111320348040001d200b6081c10065108400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 781920782 1250 781919532 781919561
    0x201200a051c05040b06060306010c0311070b13060305070c03020c0607030e060316030e0d0e041505120c03120a020613031b05061605040e180313080604021e0303040513 74
    0x1c0607010058155010741d21560217220760625695403042003207414802150380c28049514680301501083c410700c0d0300d400004445c412540012b8580c030480055800011501c80803112502041c0a125407502940d50031100a0a00250040640c0c0c0c0181d01e61040003031247c000e1b003000c501801818815035040030080b00c09480726649040400b55100900c004040080c00300703060581401110000040d1a01c00d4025580ca603d503201004007004050f040301c1d54894000b0074007843c0030a841d600c00d8601705506080030000c00461305008181414090b0051000c204a0300c1417201001c01500410216442501071005501d00302d91032600740c40d1441c01a80d10345500c840a101c4004022000811501031040403180c540760000542003146e0500c214000c22038246001c00208907003514452180c41007103003e0094030f04140d80c1039110584004164070119096110400f80000d5003022802c1c2e81ca500d1405208150a00004001c00d6903407013103105990140c00e81141c0606070500700e0b4400c03c00700701c1d480d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 781922032 1250 781920782 781920817
    0xf0e0a0b07030206060102030313141509030a03060f030c170a05030f0d0b04150e07050909070314100305030910050c01060906030c080106150e180f070f0201200a05 72
    0x3044114841e81040070114054440c02000c11034560001013513070301c200c21038003504449540640e41e410044c12000d070154a184201650a80f28240d17106549200c0d00d000c00c01143c4440701d80200030150707251030380000320468640c02d080c80800c01c400160402e6540801c60011811401c00a291620344615009444d034040891000446003181e001401c0031600010240040e41a10040104176000b4a40c0742d2500079010500b080b500300c410148030783c020400c1c203125040a5040d0007082c48110200c40550004c0c1d80c8540c02c100702441c16600d00d0704410645003000149046588540c0e40c0d02c1025103013482030441d00f81000e425032041c411070f182500c4000003800320641e580311b04009092540021500365001c2030011900701d405100780c004682c3c4a60900b8401994000c0540b0300040320a00603800480464002c0e61000c21820094003501010000250510306100d00402588005240000b10b9042c590301c0340c16030f4000f2549035401c130381241089548100400342558940301e551a42182c2c403514 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 781923282 1250 781922032 781922039
    0x308220309090b1518060f071b1d06210a260c07031b09090c2301080105060d0e10020901020d14030f101701090203010606080103020a060f0e0a 63
    0x4441d1a100311100c0b00802d0004400450400003031501c40e42c603040068105008503030194460b0a101d020381d0300702400b042d103441c2840c400c07800755030300803042507070000c000c88801c10080c01c00269000023000031413280968109080c060911440307014103558807800c44a00c40c49461080c00398040501c9120f40101c0d54060010700e407209940004d17904915215100c425201140001d100841c0c03450010700d0094540f25081d551410f80d01070301000c80b29200c0051007000b04d8410014030408802c42d0013201c181150619100080c0c1c01d45800c8a015035065680301d8100905036040300c0081d040d03030301c2203919948480b8010050030042404642109030707032241f6030180c0301c041080d900030101c0340b80c01c4e0300344c80380c09001040030b69160814070428081040104001640c144041d0200f94018100c51070701c503050356881002d07290b95403003800300c5070450350349090103021490309102d010010400d5040c00b900e44e61440e000940001006c1c42038900b404407004992103801c4c403540c1c1100c580400140303202130440d02c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 781924532 1250 781923282 781923287
    0x30b03030703020a144603050717160b0a020d06061115010608060f040f0507180504140105130e0d05030402010f02010e061f05030109081c06060c03082203 68
    0xd1802c0c0c01d448010780019040c10303517030f0302082c0303d90700380740321807400450840c4040b8544110b001c140e139242c107003040c086828402000c5a44144d10842c080c0d0f491949075100d80c105040300e2080154040c0211508105944210b0241000a18080d40041d10311602d6915844450042e02c5034017400310844d4a040d030041074440d004041260790810a40881d001008850040004154207020303801c040f0300c2c04800143d141c41d00c801850303154580903202040010001a0320410b81320291040d80100d56081041e0b043c3c9940300b0102030007040115070038043c2b00100d00e8000d45442d01070040da401880004015001c0e00d00c0c580089040100403011104032078410311000f415500161002c9000484003a0982600c0d8414001e240030f000e201d0000e07040d20b44902070440c1c0c180e000040c1c00340c50f00d100c032100050203540c00c0c49021031540c01841c64503615480e915a48020700d440308030340c909051500c0d41c00d1092541c440500e20079170341d1509052900342c440c5240d1643c0f4040c08400c2c21420501254190101075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 781925782 1250 781924532 781924543
    0x2227090b041b0602060f0f0423030306120109110d080c0a06050417030f01050f0102160b0c0106080601062a080a020c01090f0e1b09030a050148030b0303070302 70
    0x1d000b081c0016420307120501280c8030031064800003501c0704003101143d0f0002000c0b001d5a046841081e230f22400e40b405142e03180c80f150011401d424642c001104004650400c98542220203005100030030028a59a9400917844055510380b0300514480101c04204680034089410303001250b4119840e80465243c404041c00040f20110380e0240100012204201c00d40c0a9900400c1c240380340b4244c5a0078042880f0048160341c0425045124894800180d0320b040c5a40101421421541079030b80c40584400700e00399030855101120f1239000000404c6010361001500b00a8220103090b00c10041c2004500903500d9486e10026007034580c0001c941c03074641e400140000c010385003a21a0b940440d600c0121124460740e03440790304003030650100000e0b003c0000d5001302c0f403240303da080c246062090207030100345407184070130040303541da9512401c0501c1180c09aa00348030720b042d00350104d622821500c419210f001410751071408800c0d00c050840c54028020f400018115602600702d0b41c0701e20a50800a5840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 781927032 1250 781925782 781925813
    0x170a0e0406030b070c080d022a0d050307050a090b04080303060a09050601020d11190b01031b050109091a03100f05010f05060912010b0a09022227090b04 67
    0x620040100561400c00703001d0070381125040700e54200c0f1a0351300030f8103840c085d05800e4101c80c092400c12403900c84070302520103480d0801510303848c45a110381c1c10b40c54029805400322200c07141d5100c0c02e18820220390090840358003e182c0d140064691264240580d0b8041e40c5402240c0d020340c01190104400c6400406907110310011540300c9803840c2c0e50480031040340e2003659030b240180c010340042d0b01c0301405243c01c81c40100080701100d41c000b00d04080d040c03600504060803154824224010401c0c0001d02c070000380550380150702c040310540b0f403e0010b804591544a03c0c0030301d90700c42300c60348070b80e449188000416130406002d603180980c5080d16100185060ba108440491800002050005080c45884103407000a00118907202400301004120a40c140004040d5920b50107e098140c480d030b01030000501e040c200160303d8103400344041114040202e44001498082041040700d07a9002d4051030250214215111011180841a00182010000280c15420300b10700307100400c07203a5031900c0b002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 781928282 1250 781927032 781927037
    0x40617060601090812161209030212010b0307060e031c08010501020d11030403140f0a200913060c0302090316050a05180402040231060206090a0c140d170a 68
    0x39524032005582d420468041e03d4141c2d808034002200540e41701c0014103090040c840c0703859034480c25540368001a101118a41c0004154030010021130502282d04e4209007086002400842d483e140800d035100c959100711420404440010901600e040c4461026100e401da00f0440f5000c80841c0609188400c0c8529801841021494600f80d0b2203002c12442c00350304400a1803070325145450b80d11010400610400c90740c090344d14118181c08c8104502c03c00c02e40325414100e44401400c2010204198491400380210713281400c010040519121180516502290000e44002c04a008400034007641c02c0b065054800c03e0300047c2c4e00b1121025081c1210381c11030f103240b0090346840c107100c01011440e040100c0310b905d101c00700c0e006107416000303403008281c1210382d10b10703100c52200b00e07840346034080780101c06040d0f501406000542d411f104607540201407000401281c4d0595a4542101c2032511940780084450030b1415284c2c0d5980460201e0540c01071700c10120030500ca400101e19a0092401c0c801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 781929532 1250 781928282 781928293
    0x10e0a03090506070c0b071403030405301902030d0606090905070f0f030902010311120f0709080d11071d19060b09040b0409141f0e06010320040617 65
    0x55500c0c060003100c031308039800b1740d18440382468012510342c00d8010300c0c2c0c00c0390f200000c07540d000c0184900b040030318401d900600081180351a03c1e0f01f200c807209280c18483d242921b0124440d04110b04160031129038642d43d4400004881d5280c00490940c01001d0740002c80078148100041c1c0a64400c800c2416030341d003910304116a07140c60300140e561a00c0000c030400402c0d4010003030f030009400395200e907034054010706021881440c0703c1e89038056944201d040c1074900c404101030080e500400c0548961001c001e0a0140c0302a003081c0b8142e64621541d810081040a5902034001d02c6400b0b0003c08010800103036492082841f10300480e55806044549526800486000f690350525a001d641c040340c1d090300a041c40c0444680621010b0042844440c3d0000e4444001200240c40510300842c01c174607131806800c0b4003c00d08903450f603030030598990b03005141c203004000804000100d001411683d118400718003041c0c00100380790035403100a910a0303202d4649800014001c011252003a00850000c059a2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 781930782 1250 781929532 781929539
    0x20709050a1a090705130e070201140609011a070212010504120e060301060809010e0d0513080c09010b07020310050405280c1412011d06130f1112010e0a0309 69
    0x201c81d20101e404200c5081510b040c1d1982c1000f0040e03076001420351400c189000c0000d2900742446015601c5840240141800c000c00b00d9820300c070346000700b501508000c0c89410a00c1c0050f0080d2818041c440750070a48450105241d07450b4000c40f22101e03800f0b1300d80050050441940ca00808017154240c0314412083c1e010b14495104124003d09070900810792411a4244441112070b0000100045019941c0344041e19281c2c004001c043c00d2809141d44103030303076506c4030616a4000340442c0d1203010141c3c0442c16000e425558202e02c00e064451481c0c1c21500d0f8a0700d800000d107040e22461200103480e16040074041400004207030204080082d182c02c074401e041202c150301d000d109c0c0120280c01d90809400522200140b900c4440003100c00410072008052a0490705086521603104544980c104c0d01258440c00c005215045d8898401001d00082002a13215407038603074651600241aa0111224414255107112840c281c600614008100b00c0b0280071400b9556900460140c0c0411403001e80003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 781932032 1250 781930782 781930801
    0x30901030b030303090d0f090905090a17040807031b03080406080f0c090306150a2606070f090603020f0409020d090204060e06031b150c031e040509040807140d02070905 74
    0x49000f0f05144001b01076060761481300320382a0186030006010895625400281a612405082d01030152a005815281c6081ca4201e1031503c1030140341c1c1060000384400c0000710070101d002c42c21260020340342c1d0f10442000c030300d8160000701904014150440814085603991703000c20071901c5070030644c0c190301064136103100d10b1040b800b5980c941035043d482400025501c4440000050062074090f185400c100e40f2684940c1b0044640c0c4004040000004444252035208102c0e42c0c0d082440b0313080c4002c0165021200400d0464140982c6080c150002a5221180000811600200240c0c00219103401c1e01143c120060400080f00b41c2c4182e08188010540894034566180076890050007031150f04400c14442d403114845030b20445cad1146080300c0c0300c00304030020801400c1900b0b02c540a1507480c0244150541820401c0c1c0301c03d1400041031000340050303210310403010f0b089508a007001e1385564a600d0b12141020454809000324061a804103a5117500014500199410008140000c0e03030707920a030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 781933282 1250 781932032 781932037
    0x30a110307080403080711091501030f0606021903050904021306020f300c0105040c1d0105010215060d1506181404020d15020307090608070f0e09090304090e030901030b0303 76
    0x70340b548004010800000e01504000c0815038810f090f000c00d410400000143c1091086840008541c5a40003402c0c49607414031030100766205420f010800c180c10014002c2d521260006048440001609003800345400f8605541c0c0f00d20000b40155502c0c410742402c4803c030701c0c1c944242400741c800c00d04d41400c0d41c2c0c40030500088401044450842950b20f1424400c0080703c030902c095001d035030812041031a01000c0c014503204d030b80502032681e8018070301081501c5407500b4221b440a444201c0006008581c1d002c111240d00d402c0c50300c89140252201400a0401d41d90008010303c1c1c80400900d02e0042d00003500140112340c1c086222948801c40c1108500940d1b440011080c400c0d00d04200042c01480d10b483c50405050003a07101d4a40c0c4580f440d0102d0403a881600d107a008a15500360822010303901c9407145074030107664a4101c80450200724080c102c0c80e00e41e0b204521400c0c0781800201020400c20a44005000f0140d0603c5111401c0030120340b280c1c800000280080e090107615105420000f04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 781934532 1250 781933282 781933297
    0x90a03031416030b06040b120103020306010f031509030e030d080f090102040b0405120a081242030f1204050306090d0207091e020a03021c0c0c021311030108030a1103 73
    0x1e142d0b10b00c4401c0d28100e0042030194140d5a2250003440003003a00e14260014090700849621080382550544c01014504201680080b848403c5401e09100007810010022017200c50020701281610062030191103901290314065014800c0d100041c214691101c0c11900403030802c0754086150f15601d402500340d110300e000d0142d400703a081200f00007174200002c0070150082038405132007821007180d6032180c1680c011162410056140c800340f001da04400c0c20004070315007a03000c0c2c1003403e46c40700103000304056440400e842c0c0d502002007581c01d00d8a003401407130305101032041944d2888001c540d40c214940c11902646020f0f00c502c00020b840d00f1400a50481403c030250011324a451901c070000020781480d0425030341034903003208540101000c80c0054500c041c0692000f40c2c0b0b54030142c150b8000d801c0820320304062a410144a0503002c0e07000f440c005555501511275402c03a69500007820f0140c2aa000f44000c20040080001211070b8048040c054030922035a800f8450308200942c2680ca010303d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 781935782 1250 781934532 781934551
    0xa0b0609070c030810091d07060309151e020f040f050307050d08030a090c0e0910090209131e1419051b011205040804060e0d1a041505090a030314 64
    0x2c0e0000c80d018012042c2d0009031050300b032403190b44a440f884141c80f20140c41c0341c0c4800c140c100e011003807032041c030010015100901d81000701c004103031a1030304d040240b82e00900e20195640c2d011603c000c203c89980944800e0a00155920b2450511900c030650203071040710905000c00070301040310300d8081401c104a0ba4010a4103800e00c0c400e4961414660000e07004690043c0d440301040001030140700b04100078581041094468a0308107020350600888284c250112031a169801005903105449580c0110f624580b50300e080d41540380a10006081c10b0410415411400f100410800e0f00004605501158000d86079a49051148a00b0f048042000244960810b040c0440ad25441941c070042c0c00c1c5c0140b4040007890302018044d400c0303480c140c03016a5503901c0011300b40105a0450034559070500c007070350180305150050300e07400080d072001e07207203511005041d50128003413084a2103014014150544200190708004c100103a0b140e0603180b0403000700e4109041e02c1d00034404011094410441e44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 781937032 1250 781935782 781935797
    0xe090106090b100f200607080705130608130b09010e0c01020d120b06040e071e050a090506070c050a061116060f2f1f0c05040b090a0e090a0b060907 65
    0x50081d660074200030044000c2101c0050b034148501700a40c0e006010140640c00783c8010b0804990041800d0300c000c00d01c0e800d020041200580b0028210048002c890243c0740a208070703210019518003ea80009002d006891a602441002541036001c05070b1000c00c0002c070ba403e000c940005907101c0350101034007004602c40e02d00c1150003091641203820140700c014241ba00d0180c0700d400d0704074548410b07600500012403500414151006038540b11150304c1903800e000b170415010030b00061102c4103901400d4041c01011440ca000c100c5e03080c1e40c01000d82001008244c0ca50b031030340c038014010b02e07e15014480611984404203144859440701c801660425603481c032404000f5041515403642000e0039544480704d0a202d12075089a08024000c080140c01c09005a00b1a401030800c00c60541881021024940003034003994035046002c480442d499404081d440302a1030b4005114060254060303c20703000e030342040001441002c80c1c005440b51007000000d4032a181c502c103100d400d020407a000000300340e10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 781938282 1250 781937032 781937059
    0x60f01080c0c0a0210021b09060a27110a02070e0c030403031a030601120525170309041e1a100311041a03060a08010e0606130f05010e090106090b 64
    0x5080060600b000a8421210626019808100b00f82d20103059600183c115120442d420311032070161301101c500c11584007100d81003100014a04121500c00e048031145a01c40024880e40317130300b0044021640300902040010042c4a18070003560107815443d0042c003c803507010500320914024036020300d189100c850f0950740e0b1a40c0580080c811031004c1c020350140c03406003000b02c0d0340c20040039010f407a5000716071403405030619040741743c10325440d030050240b00c01c001100048050401c6410841c0c10540344130400c001400da08504501c03689008540050500140c5a00f1041c200c610f426002c140c550100035840381380c010b4a5040b600035103c0c41e07104111b01c000c07940d454483d401802d0302a107030b4036a640c81d15a0f10f5901c0344920a4a61200452003030110800403a490540001002404004020705c105a1003041040c3c54140c0100114802e007000c84021008400a9000042d11110002e0400480d44c5511203c40000e004031501c000319070070700340f0120b9040f80c58060b0500507013000c2c1a0100381c2c80b5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 781939532 1250 781938282 781938301
    0x10807030f020d061509020414010c0b13020a150503160302090a091d01090609030305090f0d05210708060a2709300f08071704030908010e0c0306060f0108 68
    0x71081404d41e1003c0c1ca5075514400313065460440c3c0d000f44044c80d00145c1d00d914207204c044c00d9814181c00030707050286039603240020030400d100c01580540c08602d44541d80351940b0020398400c0c21038204202c01c0f21606030809805400c04002c0d401581c100e8421035080000400c100d0030f83c41003c83e0150040c000c604100115450740d00305140c8114a0000030300c0318a00300f5091404c40f110f6500a80b0700d0f40d03d480d014014503405101d49508440303234602030b1403101c24000303841d0368681d070345a012002c20500043c81c036500505031440c1250080959040842404e10200050070028152009032088809144c000381e2001e44200704d140c607843e00801340704020368402c5681c0007401f84840036200d4130403510f0031200c0b203008600e40d4602000d40342850b40c01c0c9192a04000e000c0c0b00ea11880300180704d030050900603626000341d101c466642144408040540d25494202d03110b900030f0344560711540c00c0c00d102807501140070610f0031965000b0b604032a4659a0107007008115084102294007003041000411040c52 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 781940782 1250 781939532 781939549
    0x5060106230711030f0307060504021c0503040b0a020c090106080915070e19030611031f06120b0409050d0e040e03040f12031713111002030d090515010e040308010807030f02 76
    0xc100070705840c070000c0044c2c05c00d41160f006070001c6840301c1c0d80d0740801c4110b20741407907180050b1545c241c104010141c9699616503e21880c0100322a000001c2280c0b81010b00c06c000400da0080040d00342c1350703a540d40b1940a82013607002e603859000350040301c0002c103540d40d480721070600c1000750765555aa0340c55000b0030310441c44d01e51038a018400540000100210f5035901a46c9131443c00c804801d560ba02d00070580c00d86505844114050b50002101d0400040d907020000c403005c1c18440e6000640a648240000c00401810340c1c0200280520345a401010b80c000c03e0340b040030380c81a034007440720110042c10745880340f0445c055225030b440c00c80c81c02e1140b89106061101c00c80e203c0d040c8400c8141101c20504070700a0101c0e071075035514003042040c208000003128206503c00069a1800400405c401e010352280070306003074148070594801078541402020400070003c00c8003d06801159611840700e2140d41c101205c05901203825080000782c011000a882803c13030b500314040321058042c80d4200040c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 781942032 1250 781940782 781940813
    0x20406330f031d010221130203060a050c0c060106090503160e041707050f030a09061b06242c04050a151407090501020705010e0603040b0a0612050601062307 69
    0x112003c031800480d01402d00c010004c2c400303a6030b943d004640020403100390240d402031180c40200200b0451000584000035401d800c8508918040b80e40d940d01400c0d8001809045c6020b00c81c1d200c4c3c80000a101e0303800c01811000c1d51030070380c10740b80c408c51601e140c0f01640e00d25209040098042000150126030000e80340aa01a14994114a0001641c40b4503190284083d4406e140c0d8000048038400d290f0060308030b90050440d070600005001c0c0145111428030254100680540d40ba00e41248a4105505010721280030000401d600d2945800306204030303400c00440d109852003520b15518455048002051156500c01c00510a084295035600c03101c0405c031a00c030115a0702c603403a403501240034051041c416a200c1c0d0719003d840d80381400080c64518542c3c40300f410b01c0160400700000e40c40360012241d015802c42c419603101e8444086c00c20007091280d03c05203070585981c3c4000100600071a405040314581e6990807080008002d42c40701d0170204404d2111441020000301e0000344046d00e190408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 781943282 1250 781942032 781942061
    0x18091302030606100c0b04200a06050a1809020f030a0e0109050a030e01200616080c041e080303101d0f0f04051f060e09010912050313020406330f03 65
    0xc000546ea83e201d10074019901202d6100d03100000409020b0343c07500369020840c1c1215544080d618148024048e8840c03408450208441c0c062401c03080741381d0410f284003c1203191005c42d42c50100d18603a0140340c20076070b00075010508049103d5001e05050207641070305a0808081d100720b605a41e420707594551b1031800c6034144507601c48112450401d41240c49882100b00010380b2091a14000c4440c007802180c903500c007800344600900078005080000e039800c0e00e0f00040200c60043c43d5800030071140c07a0035070091030729210010405c40d450040d070940f0703400c64030b4440501d40244140c2c500d003d21080c1c1190210b40129110001440360082102201d801c103000e0000e5650b4135084040707100291314201100d85405440354820001c1c0c1e42c208480f103600420b10002082200c08558410f1401104c00340d0365000c009012000c02c1a039030444c03034900d5003603a004008020255030b503a00400404c0c410041000741d40c9202103202d0340b6031003101c3d542e030034504151740302d4050001021042d00200044c6510203c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 781944532 1250 781943282 781943297
    0x90e070909020d0903020f07060906110717010e070608091203132010020606030a03052803090c050616020402030c07051204171204090519021809130203060610 70
    0x1d140c84544000d0800c5440c090001ca00e40c0c0d518140a807400040c641da68110340e100c20000c0181da6409240c032402c0e50034078a0152010803c06008a00d060850340240ba6804c900004620204d0070540c4100381c10400c000a4441d1280e80301001e84e02c1c0002100c0c1e80c0d246801c0f4030942e8120407441d4004550050814540510350300640c0c8401010361580b04010701082c500303c08820300e5141103d801e02c4030605a00c02083e2078608000400d4039031090060050a000c070108698281035003901d40b00390b04030128141c1a1a420340010014041d0080300c40c2511101e29000f0040b0f858141882241c442010401c11170b072002a031942480300a50005009540084042c4001c2c00099018041e4004000c0d424400c0c6445600700b2264918000506100c210550300c100c2c00c00b03107560440d50035201100d4059100160580d074140b484c014002c0f182e0810140e40d44005104071807030720086402c41d0b26080c151018031507551280301c580350082a40030065491f901c0400041c50b1803901503a01285a5a646030201 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 781945782 1250 781944532 781944539
    0x60105090612070c14010207030509040f02090d0305040306140105030a020112020c10021b060115180f06050d2d090804030b0f071427030715050d06050f01090e0709 72
    0x44000100f5903182c000140410310384800d120340010311818429149000b1443e084103a54098858400c0540c4e160040340c83d40d0b140d2402c2c01d02ca605030343c0745079400303060b400c1074200e14980100103500c81d000494140c1d2a0070607c0c030441744a00f201d17a040e241c000d0000c1c07410342c1a503001500c0303840a0100c800352542d000c01100c12005014040c929072207040010142e01d411540d41002500d25030241040c4082e400320380108003410314550312549031000c82c01c08403a80d601d4500e00b820364400d01e802040800001040004d120f5a001c001801c9603040a00e08001020f500c1818a024208803d40c50103080340c950340c03281c0c0c0050158041c883c40c1c0d00c64000b5901e85592507490300309500c1308962100001e11580b04029001c2e0300705600b90382d90240c007803049140841103482075040074504000e001d05034001e0001c002c1aa02d041150344003078100c3c1d00c0c0345103840c0b8a22000800f1075000e21302c009142d50400340c0020301030410300030001038a40141c44042504e424040307076001000c0000c1000301081654013000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 781947032 1250 781945782 781945807
    0xa200a0501060f06170c0901050f090312070303050a090201090504021b0706050c0706021912050c250803040f092c010209092206050a1d0114070f02060601050906 71
    0x810a00c840207403090700d03100002c0c000c1d10100914451140541c010030171b8640030001200e071151002d08040ea120803400c400a1007034003404081c030f90144142c100c44281000c5044c007400c900c0d0300c82d0b6000e2101da9a481c900307400307a40d100500240851f9095905001e41c2c038080c2c02404040381c1d6807488071004030720a0007080c03400a184d4002004a58000341c0206500310034486c800240c85a40010803085905030040d42035402082c070b020b0030004103001c03401406407040c8121010502250b0072102e01d00c00020b4198002104a900e055245110314400a82010080706850441d0880d124912040d4544001b0340042c158582501c41000043c000c2103009081c444041402c24030304500040c0c840d44400240040f5140151404141d5803130281d001291440a10300c8034003841d0710200100c1e641d1124400ba41c09403900c241d00002040c0100340c0e44c0c46501056011440c82c40c00400c40310040e84510009560120b5404020b20060304001d00007061540503e00030084c82c10042c110318901107981804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 781948282 1250 781947032 781947041
    0x10b0906032a24030f071e0e010c0f0c0f0807140f01030b090f040b01090504021c0302010f14100605211009090b06030607111b04060902031017030a200a0501 69
    0x1d200700f90000300a000e44c80d20301110305940003480d0304242004800c44040811042000751464003041000005200390364421095100600d511000b604d04511540c90302d2000c8080c0d500a0001c01c41c2d81c80f0340020084400140103088654501c02808410860801e000c101c841d1110700d54107040d11090503a813103488400319980f00300180d561010050815181c0b0588113001039120300c02c110300304028440541c0c0c9010403002c3d2402c00801d0313444500311519040e40509840840c03080c4032444d0068100940741c1c2c1071035451280f41e016018400300c50301c400040d15a401041040401c4002590381140340d40d000e170354600d80011024890f00d00300c1c0d070341d000080c081d00c1c1014000c0300c00c20240d4040c044541420804c068000d0b2050524030494030711b449101c1c1c0d0783c00da02071301358118080d4030700c021085803690760243c0040e03e050807096540340b40000c0e049500003841e10070701a80d4068280002492180403040c0c030045406640c442c00b04681c03000103103500310f400e03a1085095000b400001c00014800740b25 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 781949532 1250 781948282 781948339
    0x2a150708190b06030604020d0e070f051203031b07050708060a39050d0b120303040201180e01030f03020f0a1b0602031306051308010509010b0906032a 66
    0x6480503240380250031038004506846039003110904040103030703180e6583c071001c0e80c1c0e1000e0103441c016110301c03032804400050104001c3c800c031140a2001d01180c0c402c0051013400587d4030944030070f07500100084005989110030de8880d00394444810010410030540002028194040e0040702e071401e80740c0c00c802e81002000e8481d0250940c0c0e0b181e60000181c81d101c030390314041d0340c040010b00c844a048030b000a40311901010710020064001804101c3d200d0513808050071000180081124641c2a041f81e03a59034004d860070780c00b041840c10043d030141450300a94090307841054448006034130307660714617a0402c91200c0880541c056080c144022240820284001501030009a034041c42100c444040b440b003660000b6085400410504411100e000c00507011203105260440d5134892000f00c444840310260040381b20f40d400c100c1070244040c2e05421820301c0c007100300c13051407998880b8801c0584e100e40c07011001c15040750645503406500440201410711510192011704403c00c441040c1814042c00d08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 781950782 1250 781949532 781949537
    0xe0604020703112b031b0302160b0405070915030305090d0206040e100501480c060201050f0a09020d030807051b032221150e01021e2a1507 61
    0x8203440135102c2000e039244120300040c00c00b0041c0c041d000300003065142059000c002410340000d400450150002c0701041035a8218881d5060340c10189880390f101c81f0316210307031042103003072039007401d07181e0a44510b99048070381c1900c0b000e142511410500c00c217600005000d0ba48007400b4000000e200000c03c3c81588609a10540f00100c2403c0c00000f408815100210388010305171a603455510710314010000c01030b07801c01180c03003c0ca039403185103140800260144c0286440c248c1d210026442e03405403c4140241c0c481c0300324208a6894010b0300e001c40780103c2c40a0350007a00c003582140840c0c003c1c1032130742c0c102101e07181c210b01d003003005004103190004800300d28480350700010300183d0300a4482800c040f98481e000d4000c02940c50711190781d600034681d0a1400c10030840c0350010b020031040440802c81c0c07514110003032105006907104c0a0003504240e5400d005c008080000c0044010301c8400c0303650280342071008640c0c500f074003d0700208000510190301814441d410519118588141c0f185100359002d6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 781952032 1250 781950782 781950823
    0x220e01030302010f0f021608131509060e01051908060118080c0906120705120c58022206050a0801050402030304032004050c13080303010e060402070311 67
    0x8a40030300c1114203074041c8001041c1b0600019165080c000391010642e50842c42044d1282d45e840c0d0307040181c844940c0107025440d1740a01c0d803200650407900362021144151256400a80c16100542e09803041243ca00c0b01c2000c85103071980e581d80500500c075046141858120401c80340391600070a071a01e039401c803034071070307071202e95600f4a61508c20445a84001c00b910a210b00420700240240d51354400d014503440b8610381c0c5030300f146480c0b0801440000400050143c900c5040d80c410b1f0900540c49102601070f104164a01c3c0440e00c101c0060084021233400842c3c4c418003841c0340c200c41c8640c0a0314040781c0c006e219005942c91740700c1002240c0c1c14015400400140149000c0400880d081d040d48081901e034181020000940e5000c010303030301100e0f08101004045043c1c000e424042111a495582e401031902040c0502d00f804500a0401c00d501400e580c0010360f2506c0415075030703001c2441504202c0b0360b00710000e0200e0420350090407400348a801c04820307816100c034050b818210610080c11090803031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 781953282 1250 781952032 781952051
    0x304240608010f0b100f02030708130e1e040209090307020405010312091205030f0a0302090d06060503060702210d020f0a0c021f0e091f08011505100203220e0103030201 74
    0xe1160740fa81840c40311041100d0750b00c40c800310341079480038031044c0d090040780202107500a00a004035111540d200203041c1d940d0f80e61043c0c010700080e15018802d04889aa00001d40c803210311851829025100001c2c0b44843c0e8640e401c120319004001c3c0541010300041c1b080500503101c90081e03601079441246e00f0001a550150020301c61100f03030b80110301d160500c00030000030440101c1244c440941c0000319542c3d404804c4000d60180c86545c0c0647d4110003605203c80c2404082e90000c4180d90040741a82c506807503d810490780d80c3c2400480c40f9100d440100001c0c84101c0880041103034442c1e404000d414603281104a0700350b500228508404165001034240840c9003900c0d09800b1402100300840111099480c004c0120500210050185852030080f9600f640103190182000b030b424120190050340b140500307806800502c11480411070000d9000c02d0b80d2070050343c0107000c1c101c550b00440c145940e00d0b0100502814682003280798075039060010440c1092580864040e50103030300042a507010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 781954532 1250 781953282 781953299
    0xa1709030a05030a0b0604050a03050604060f2c0114070f020c0d0308070305070201143408041e02091e070f02030316050c03070308040b0901051b03042406 68
    0x400905a1906800400c600da000c96002000d581c3c100c0c81ea004001a000782d013001140342ca00c40d44d005142c0c40440c40c00000200700300025640d201b02d20501c4140300307803404002500d09807481d50300c1c1c0e5070344174000c101d082e140c940441c64868480d1000138000300f45486405440020080140c2c0d1800020b501c45003d609180d40410450700d0902080da010b01d80d082898030010034040003c2e05500c00c040d100c2c0041820135100f50070441203c2c0c540c0c04400ea5a0409a1444001104000124000d80f801c440c0e0011003850310403041c1001c0f4404d440340c601c155215900d400441d16400300e0400d034089140708640150711041051445084140d80c0c0140184e02c85482890681c402054001085900300c140022158044290380e00071307003a02c00b1100752007801181a40c803405003c40000301031001103811070030305030300001c65402903002d101c5040c1c81c1d4440350f2074182658400c9802c0c0701750311006200c00c50100c8151000310741c014000c41d820019140822803210358102440c000c0010651250001e022641 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 781955782 1250 781954532 781954577
    0x2131a090315070c0b090312070e010e1516080f07060605040e030c120a050c1603110d0309060c02060f03070e1306050901030f0501021303050709050f0705070f0c09020a 74
    0x210354005046190048005011101c030713000080c40d13000c030170022405081080040d03c00c801000b101c1504640f0341380c44000c2401e070b00003008900090000e086d10f0424180182451009828908518609030360041a084c6034600ea603421510990204007444c0c4441c00031020f440f00c42d20441c40030400900e488100300648810807070402c030070703002000300d45661600014001958408842e01d40c0d00d584072228143c8003401400000040c6004900600b401117207480340c1081502e108130094440003a46005000c600c80442e0001008284a0341c000e00c09607000d240c034270604500c0142124540301c4c020701d8210f11600152540404507843c50b41c0143d0038946801a200000221841000f400d0f1900c8001030b8406410700c0041c1c1030b00c02862000c8240402901284d03c000300706d4a030800040d0303a0f40b034025644d80c038a2292005aa2410300030490b0108181c90b50381c007074102990f03854100500c079282c040843d588044225041111080c00160021040c001381c035440d16541c84a408401d4100502d90915 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 781957032 1250 781955782 781955803
    0x7031b050f0a3210021608010e03030c0c030906041404110901140c191a0a050112030f02010e100f0e060103020d080c19240b06090402131a0903 63
    0x15141c240c2c0600c000c0300d03030209038203662685140105454141500b510160320108640f80c0d004001d410b500d000007600010781c016041402032030500303101e544a9030f05007200c00f43c00c9604420380082004c43d9046083e48090b000d001424070989141011402c0040e140d50700540c024000840c0107043e1820501d41441204028200424003e00e0301c0d00d40c10008227061040c00660440e103401080703a900100c0100400302c00c09000c2e010b0600c5c600194107241c00d0480102001c40c0d241440c010001d05102d4030303070140e00d04035a50b4015029820a0303503941a110380c080c41c00c5000840d0f580c0d9803400030003101040344c11030f42d91401d18009002c01c0e0340e48055060b0340107202c11480d9607124000400c0181c41d0101811456900400c15503228022402207500304900c0400c41d00b40743d05901040c500307010400c08000d0b19601c0030703200c007070b1020724041015043d00d03138118509520003418000c0c2103045c140f507001002c8241c408082844104d45402c0c000f20400c40000710700b41c2100011401c40c0d541c0c1810800704014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 781958282 1250 781957032 781957039
    0x10050f180c030718140103030507050616140a05070c0902030610020705031e120f1201090b01171503070b090114040308030402061e0a020d09270c0207031b050f 70
    0x190000070002c65070b1030105115034080c400c1c10125064690020b540007001d19018100c024a055a49080c01030058101000c01c0e5018003400f0082a00b00d02202010f00f42c0400039118000c1e074002d080c0e2a100c0c0381c0c2000c0350b04801d0010400404002170f6464200c0005020f840c0380040e02e900744070b030611940ca2180712484065511000c0180000e81d8001a20840c0d0340200c3c00e00c0a2845d0f100c600541000b03c00445080e01441c0810700c5c0003040b8a4801500709030100d18400b825076039a40d1005800c0e529020105404980001c003d00c00003804507802030303842900c404420801408202c0401c0c940101544010106600400c107810250307030201580780766489103600603080508503251008a880040c0000f803080300000b916004c550390f0031960344600b0000920b50303078507544201d00103520351504503040c1c40082d9150703c0204814140c0d1042c01005000c001d2a0002841c11507100c0c4010301c84c00e6190019072042c00b1000001581c4103401e6012140b0074003850301c0c914504014003041d0300c280da54541c171 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 781959532 1250 781958282 781958293
    0x30102070308190b0a0306020d0f02070f030c0c120308010e0a060501080a0b0a03080d050f0a060b090f1c120905041b1b06020408011e0203131410050f18 67
    0x8240e001e40615041040e00c03400140035069001e000d0024404c850030690444000c41002051195039406080ca10841502c280318940b8441d50502c200d01c41c10800410080346d503840d91000c28032410709887d10074403984200c03028503100c02d09040e102c41d25410880000f050140144030740c40c1c0d01d50f80035402c40c84068091000c0c130305143c0040c0900000038484d40000e17a071231034243e20301e98824030810000c581140a01f55514120383c480c0d00644400c44612030f580c241140800d804c2c1e003c600c85c5408852541c5145030400104008020300c24408180060f4000c04a1911003005040a40c140c41418030034030103000590002c1201400300b146950201c1e10540c034009107540e0600d4504500402030f001071902c0c0d42200013920b180d41c0100e010740b10142ca020301c042008200ca11055100e1400d49082c80700c4a091102d05a007520700703910045880480b00e0340c42c2c9083d0400625401c00c041d290b06181e60940d5250014a0300c0c00e4100c920441d0000c4001d400301c03090111000b040004103d280c01c285e0007401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 781960782 1250 781959532 781959547
    0x170a030e0609150a1103150f010804020f040f020904061202030609010b0d12030e0601030c1409041a09122706090d0b10120503180607171c02190e030102 67
    0xd40f2407480424401c0380c01c101c00002942e2a94580c0700c4100b48100d9854191079081c80705548018400412209005080ca48a500110b41c0600b00c00c40c42950300411341000d0a100790203000242c8880089416900d03024001015156034600850000d0304041c1d980401801c0341340101450060090030503210380c1d24000342811140c42c0c1d8144005820b07003003c2d100004086042d4210007c1125011500a50103808004000c01c003000341c2040803180303419001c0c4800806c203001c0007071074035003503c0060068500781d1a5039a18000c440d146a4440642070a9a08402904040d4080c541c003c4840c4500000417901c104600482d11590001000302621710605203000180401c2003440b996034050080b001e0000058600107882d40d105000e449980300b45003060506141c6245d82c1e402c40d203c4548509802044a611410254240c9180d184c0009181480103100100a11070742d101045444849010b035085400401c0710340002e01440b4ad010002c060608900600108540c40f0103842603c01d900420142 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 781962032 1250 781960782 781960801
    0x3070807080a0b0c0406080f0c0d090c050a08010b030703110316031113050705070204050a15060507120513090c020307081c05090f1015080f0706030c0201060308070f02010309170a030e06 82
    0xd542c46239000002501c43d0f00c0e40b8112206600440440c0541503007865046130802200380074040c12030f442603c003480c4c400c0c1c9454000e4261054842101c0d01030b0300041c000c001196100d4900312402c00b002d82544d01c04002c0c4086c903c04141d541c0c0096541c03002c0040301e90202d003008641c4803403030f40e00c1480070005810302c000001c10310300c02e240c1d003e8452916040031a07407504030355205e0315440700800c0c904d54001e83ea03100c0103011500038410540c1c03c0101c074070081c1311a0f40107408840620680d1921310310b1a03070400074102c0013070402100f42400c40c40f0a0006100107030204c0020305c2c0b00c000381b4194044007841540103105540000301000840d80001c80c140ca48004d0000303181041114120300403e40b101d400c0c4104040b440658020101c0d0712601034104070511010480106841142c0e406020000640340160700303030b901c2884010250030341000131501041d5141c0541919500c1491702103118041034840400764072014000c4981d0b0240001c05403041030f0580b00e481310300040b41d4040c0440d4035000413030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 781963282 1250 781962032 781962047
    0x10f0306090213020406030b0102011a0904030f0504051e0316060e0d14010507110d0c080423040c0216120206030f1e13020120070501030b03070807080a0b0c0406 71
    0x6000c507844462401c1103540701c80c00780c101d000c001da400310740b034a95400d001005407140481c21800741d444c01c100080b001c028a00b072116048001b51180e49940c4460b50200c43c1000042c5540081140034080403c1907514422141d400650003081c000300c15084804060038034140f40300999450712081d80422640f500412540d0001508840c8440241c80904080000001c6690010842e500e81010007003065004001c4500b11101e0760100ca503130b059446401d582c0c0392600d0101030078244050104018254522030808000120682c0c103102c81c0e030102020800f9141c4084801c0d0168108000b81e084081504036101d00030514809540360016050300402d8140c0f10182c030003294071a00200140d00780b040301c59161002c0d482188410f026107402803c940000c04504012400160b68046c003114509030900381d07001043c8104040d0210614100040d402001d41c458103507054054410000340001c4280700d01c4c8020070005016103d6070100b460204800c0c0f80c0140703102131808041c0b1080c811958003114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 781964532 1250 781963282 781963289
    0x709050f06030d030b0a0302221404110907030b060d09050105310302010b060c07062d0809120c07051c0f0b04210e011814130e030f040609080303010f 66
    0x70300040170594540852403220032a0006500605642010600c1c81030b000882001d25800711001c22515015407100d61b0b84500988001e00002c0c42d030250040ca03460b1046884c0d41282003801c0000e04031203804045603464001d0360580100e113541c0c6003907005000c000c1c0501c0f0f50241091440100c004105015000c280c2025100000044895410707801054000d500010509100511481d00c0d4100780e491203903210030600071100024840182d0210402c09800b140c40b04058880b5405224402d4000844214400514132991841009400110030032140001c0058100c0400a4000203080009102d048610301c0e01c5058404c014444e08e03004034041000402c841d40d40101e0b00c18154481d420811814a005808906c48040034a001004507400c00c241c40c400c50342c04c0c0c85000c0440c4400401007003006030340c81440383c2c02c051040b8548061804206550b025140e03d140050340181e5107810624540104841d1207484074002002c0c08583c2d0000900340007011484000d501d10340c1041451042d48a0b00d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 781965782 1250 781964532 781964537
    0x40e070b0d1104080718020301030b0a09031e09060809031908090106051c15140c070f06020409050403090e16120b0414011a030c070803070c05010e0709050f06030d 72
    0x52281d03106490354024292140d032462605807a5a100e03002513031108003600c600203e002c00709911028540e00c0b4020740b07040741d40281d00d070b0850380d031000410b002401458900310f041000985070661240c11904101051090303035942e001041c4e040c2030f07010b4400940905404030651080c002c080b6850b5051402512282c01460110030980390030f840d003405400f01d80c0140c0d5004400d044412000e909503100c83c82524000c0c040003030141078040e104001c40d0b40e400208c6a5030021040000c0c94125040000e0038540d02c60305c82d0440c0401c541c5c0726002242c12540103004c0054450b024407041c554400d110402030700700c0c840c0020003402d160071509107214105140704184054100340c02f44881d1541d2068540103006001840007031960304008801c00000d020f60015059806031915900303a5440949101d600702d40825858914a52544101904000c0c80c03a02084501d032800800913800780907258007000003600a0000c1070900d49280141ca078004c005c24514200e07074003000020341d000500e560f810b80e03150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 781967032 1250 781965782 781965787
    0x703030e0f0a0b0f011e0b1c0e10060b121b090d140105010b07030905060711030a06060812090102060601111c020606030c0103020405090106030f062c06040e070b 71
    0x26403500c1d0070030951440030740307080c051a0085814000799003200d52013045800b6800000e83c1c2c0750000c079543d40c17160003200c030851003420350706000413940e40004107440d01940b000001000f00c40c03c02041500d261440e50160754220285c00607000c001c2d4060390001d04100844c0c1030402940204003172000200414038214135941e62409aa2804064110340e401c40c40640840c40c1c40c1d80314200030040303040c16075241c15a5072030310000060200148040d12a5581d040e17440400c2c852400c41044001c1e0802d00b025039511886900794401c543d020084582058890301000c100321b031420780e95600b003580d0b0002020300700b001040200c803280e0f800b0800c2540100242407800c140c2d4802000540341500e00070640b41d145604020074055140c000801c1442248128200e640740700c10784004506900852140c40c1d0000d08020041c401e46000750400d400710500c9a00028215075100d02c280c01d140e28001400c0354058442610350000031803000c0540d072100040ea800e000c1001c001c00b420f543d03141107229208080501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 781968282 1250 781967032 781967051
    0x31106070521130204020705030703080106020c03030a1409120a030e0a050603010e040f0b150a05041401211b06081602060109110c0d08241e01180303032f070303 71
    0x2000720f03242e9036540240c800c6480e03c555280003943c2c2c1e0701030740f0300f6008109031400014949100103690040800701a01450425940060640e908600080c0caa442807805000c401d00946804004000d90702c46240102125031a5007000f901c480320704551280114583e640520860b12940c0440741100c0c03040681c150159907a04203403c845c030038000010400301000060002401181140d9120300038116501c45820b0781d43c5081104440c694a00340a46c200c410004009615114114072304800e600d91480c0e281e0034045d92680302c41e02c04060182810107004809019160740140442e40c0311223460503844072526212000380d600c03001403054655054079441600d1165007550280c800001c1500300f01e03010f030031501101904000d021220b0002c2444901ca21095488c030701c0b50004c00410018241c06c141d1034001d051110754551007000d980c10b002c1a003410801d000421010000158040da0340021003c0c02c6600130320105183c01d10f00c00c1c1203000380002201070714030345084482880d810305002441e01c41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 781969532 1250 781968282 781968301
    0x207020315070513151106040203151308040801060e0c07050604111203031504140708040b0717070c030f05211b030109020d06050a240219031106070521 67
    0xc243e00b10b81001034240340080c000d00c40f0703c084058229541c0302c6c04890007811070120782d40c0c50210341c0a5410303841400b00511140502400b540c000c141c1003501c00e0044501d8441c0030059200c0e90000c5002d070b650b40c0081150400a0150755042051015031030f26051070364540c1a920000076101a2883c42210300100780c0b40c0c2d91840340c07500700c6042002e5a0f22458840c5181d10303211841045240140e0609030400c1d000f01d90000400d2280045442d5005191038540366082c114000600f00d005102480640f820381c4246195030034814002c41d550100c5120741131034024071b941043d40e00c6406205090040324244010344015811188140200c020740303030b0311a041581443c50720b1400605440c1c000001244c048440e80040c104c0c850a00340500500d075031b40c014070031181c005100344104c500c0e003140c4410091120003c90303601d004080c81210552642c0c01550489940600c1007180483c0030032074010400c180900c066688255103003001403e01003103603030000044003c081c60b016070944000004241d400f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 781970782 1250 781969532 781969537
    0xc03180102010b130e01050627040611040e340c080702120a060b0315010509040f050f0c0a080106150f1e0c11040c020d0302071e03091802070203150705 67
    0x4100c0200658804064002400b051702c45010550a02c00044d00500b0641c10317880894400c0d20101710304031210203107800c00080c05031046420a407954207007a2002c400d100035002a15030041206600d0070301700e031100d030400b83c01c01901400d0348030301108071032811352230341c5800a0031414208508103640600c0c205180b07201d4904029400012440d0b00e140d111400203503440154452441003120300a81e50815035030750160f401e240000c01c5800c005115030b060000795550405e00ca00243c0b0090081d50b5603650803c1c2414003031a04603401112154220310300b0650b0b00d0000c0c08040c00170095641440041c0b405003580c0c0f4010b80a02100b41e41100b0801e21503001d1039171100005000140200490130010a0b001d40d844007030300d200c0710040500045250500ca0144091055001080008444402036001c1c0d040608284c5241140b41008451041d0002c4c0c0011202e00c207550340801d5900b003610b900302e040c891003d4950390510622280740143c4002a00c000726405000c0401c04d03d0f070307446070101c0300e62 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 781972032 1250 781970782 781970801
    0x9170a02030304030302160f080327121c0c0b070e060403141c020c130b0f1f0810030c05042d06030506071b0602030429040303060b0c0318010201 64
    0x18480003d00000341036010038442c480140f10b40d01030441c00d60310415841c2401042c01000da2301e400800411040e507a03101000035440c115507410391916008040021644000f6071880d030280e42100905141c85880c41c42d0354001c0302e10030b0030421801801510f079076800c004024143c409101021000c60400d80d6007005035001160b00906130f9552141c000000754540140354800c00d140d03039102c884c02c44440d0011800b00350660015002c4504145030034170a90246c0040f1019503000091080d00804c2600c601d0650f0543d00c0319610308010800c1125001008154000c041a00348e80746680240002807540e0400390449208032008101100300d8860000d81e41002c079201c011441c00c40d981c03c0302002030754211204890050080c1c1d1410b69908000303860590f22620b034140c0070115030b100400051810b502854129000b540500364146003403400c0e52030000e50095001854541c14100010035905020310406003840e100050b0030b1141c07680c00113036a03000358a000481c1240e600c1040c02164803d40c402000d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 781973282 1250 781972032 781972039
    0x50603042d0323030a0c030608070617090d0c030530040209180d11010e01090b011a09062d160b0603010605030a1502120f090c1009170a02 61
    0x621410352000d0040e11944038088000c501d4411480143d980001c881c0c030f08000c110308055145a441070b005400514552018109240d9a5403010842040c2040a240500742c180c0382c1d803c0f44049203020001c4001c00a142c607200798404040741d45a5503001c2d540b2245590705003420307034903804040304200083c982e10341008140c901d488501000244d01c9030b019406907000f922181400d490744c0c086100503140d40d41480c4440c0e800484000c0c10a0b00c00c403040282d200641000050540e40e4004180c20755040d1401518036221250041c8450380d00c03004903421009010303021034503001e114400f00d500340c000d0200c0d64000904d082415030b041401603602420904190507034075968207180010b880805801c3c6010360350b00800f08002011414148100d4064030b00c000c004100c848400c3d0760b039003101c200100b890305039542c00b8810950b051f0740b06030709a0300030a58516400038a20741a08401e03d0f00a1080e05a440340586041500106070020400025070310740c61481ca02226251580c00c0c41e12081240c020340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 781974532 1250 781973282 781973333
    0x31603031b0c031b110607051203130507060507050c130f050903032d0105120f030301060306060e0301091109060d0807060c02060c030106050307030b010e100e1507050705060304 78
    0x2500c1d41d0124210b2403041c0310b522003507000380c0f000340c5245207130240c4076008041c0f40f03468201c030302c1c2864502c1c041c00e4034a101d1800c440070118030402c01001600140d41007044008105c8140080050a00c0341c500905014500f150030020140c8407a51303151040b280880c0918410101d40c56041055040280003400c10b0f00188aa401d020b07070882d690f5801181e946062028010407000c01c0d0302c032440d17007880182c54a01c007038046908000800c02032002c40d012240036407051210000040e031083c005103009000d0ba8500240c0c840c07900d140640501040da072414800c2e49002058400900050758081c0f01d06403e0765180c00694607440801e000d009640c5026101e11000b0801108020054019130b10700550355099455a07164034004003c1c500080c0100004a071082c00007810480c401d81c004164940145811100c504070304000c64241130b014117542c0c000840c581c1c6d40e52040d00b0140c0000c0d1246042d200343e5450580c494a0b855102c0645024040c441d030030020108080c040ca1401c40d00f4540e8800c400d995 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 781975782 1250 781974532 781974581
    0xd0210020c010323190e0d0c0303060f0e151302041e090c02100905150a09030207171509030409050f01060207120b2a0301142103160303 60
    0x81d0707100e001c03044182c00641030500000312009410320f030400c4140a907072107809a48480710203400800c9540c000c0600c0c16901c2d407101e00c4044003001300715010b080d0f5481d040ca4054240c1002005e03591a9005282c51340d0710942c0802c000040c590080c1d0f070001605008424103007a00c0001103001102d0440c08150500220300401d884031032040503003154600d000c0d10316030700360713595001000e560001004102581124221484449a54000701c0302e040c0b080081c1c8040c001440d00001085809803030014021b541c8180c7c3d0002c042d010450f03000a0f0200c200071100c0c810440052039035507000d0b15403904082d0305000104501c050304000707070703005004c2e04141400b0b03d00d8076605206581f0005d01c10000148640000001e40d000000c0030b402c0413a42003c0f07204080d980e0301c1400d450308040e0031203207003a038070104c640f2070500030640002c0e43c0a80044043c110040801c8003c01c0302d0b58114401440e100c10b407912120300c0051002003150321a050f29004070000324007500b001d900030007428810030104a120204c49 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 781977032 1250 781975782 781975787
    0x270501150e040321050a0605040b030a0b0c1318050726070f1808010b1912020f030f0a20090903030f060a0b0c010204091a090106080a09060e01090302070e0709140d0210 74
    0x2030117448c0240d50400002c80300741c00b003560b18412410050f280c190340d01c0202e103240b00020024603c1e143c0d0039495603401c41c0e552940c0d0060360a880c04480010f0781d601c0a01032a0f9a001c86c1c001141e2841564031110070581e02c25403003180324060560f83c1804800c4100c003444501403040658000004504607245540e2501110f01030b00101940c0e40c42a407900e101d01420039031041c500c0050b980525508041d00315590300b8030450808804c0342d1503242c45004125a00040200180310f10144a4807560000380c42c1640b02080381000c516006100b166079601f00411413100000303503544401015025072503612040b01080e0511b8160b0041c140c03241e0006072403400400150020300480348400c5003041000310110034010302101800c50039071f2001a1100420030f10344541051074203d46000000115910965180c1003283c40041c0d038034040340d4551b01074005140d01031080400074a038050381c1585038540f642c07005029211901a80c0c2c02c150307920184c0c040584880c000d03510483e81c0542a0001200d00a501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 781978282 1250 781977032 781977041
    0x606210115031205190f0c0506070c0501050105010e06070b130c06110c01091202011101060906030606080607020303090d030c0507080c0c09010504021305090406270501150e040321050a 81
    0x5980b40f51458410350b59044c411001c0340c950500c80c101090070040c0428044400c0c070203c0280c4800c20510781d1009011410500040e40101703080c1d2100420541d1500e00036094410592105042c0007000d10744c0309503525402c00f1904100e5102080100d5640c0c2c080c03038820000c41e1500c000d005400c14500110306940c0040711020072824640c00c0703e040e0003458004607100c1d9130038020b0300001404001002e0041d40154080d0004d44013000020841603280d03428a400c952044c1d000303035038081e01c0b88400c200203507080c40700c683c02c0740681c13005d14a586400c06480303558294003c0231317004240c1c0c0e0b04e5a69800314841d50683c0c07011f5911020030340e90303980449000c0341e07a0403100c4201849a40300740000203041c9018400c45035250099038520320b840d45000c0c01c024811400800682c0c0c3c1c02c0d19203440b03000071041d0030154006003035800305422043c211070034000d0031101c075015240d2503c44a07540500c08865003844140e0b1241d854900a00d28440385180c0500030380e0324500303001c0c0517420070b41408203000d0706800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 781979532 1250 781978282 781978289
    0x6040f1b030b0a180c030e030a030b010e04140105060f0f0703090617040215160503070b1b070507090207030512090d0f0503041e080705060f0103060614030606210115 73
    0x20300b44982254082000b441407038034441d1408103440d00d40c800861400942111201c008582000503820b44004070071030a69004c181842d0000e80d641c52107841135a0001c04c500300b0200b06480c2002407421070074004404070410300031140300d0304001c05c2c0d0580400b914012100300300c070313191145c070344513509841c0c080d0544d603150140ca400314442d8900510040031a80c40340b4492a00200900d0200303220f030b0b0310714030a64412050343c4d401d0310110a00801040d4100b004101c00f51288019040314a45461002003100060030b1001005c081002240c01180d0009103405c15aa80d00400580e00d10451030103407094460742c4a040b500c15030001c101306500e0000b20300400c1081c0350b511074605e0384840d28000c03141032000b01c500820a002d034001c520000345052510808051041419924204250b21103610300341c02217405110032303020480140f08101d0760f4000c04005148442814103074000035000a912800c0013004503003c0c0c150740c250340c0c190032070321031422a14400013402041f0529a4a2805511500038003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 781980782 1250 781979532 781979537
    0x50402090601020105040f030f18030f050d021f0f020d050a0c030b06090d060b0d0b0c03100512030304060b0a051903021011070e0a1d06160810050906040f1b 69
    0x14000c2d401030107890722580e408081c0c160101c2090f60151080708407400d60b0410808c00080c01481c0e0f2030340305104005980102007450300900149041484c1640c082105030440d0403500320514054481140b00108000c3c29001090f40c00300c41c512100280514a004100f050910040c010035000544c44494600d10300da80c11300c0301c080d13440c4c184501449000301320b075040303000b020510001c925242d00c455640701c2d000b0302e030100d03000a81e11152400c64003902c07181c140f008000180000d0305507400d007680007444255209000342c041101c100d81c40f404000c001814240e1a500902c1031507440320025000703440c00801c0c0421820002d113400b1341c04030039400102c1c01400b9010007021491702417900d4040b00610003008110791810400c0c420782a802c043c10001d03070303261101d480420b0118610b0300b140710000071000806042c074094440c0c010703002060040a090004071400c1c070003000c046410380410b43e0015036200d1b60a40b51000824001c03e41c00d0101c0d5503403032401d44e8141d00c0503950340404040b0354180e03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 781982032 1250 781980782 781980799
    0x112b050705031302060309010e0a231515152b0213031203020708270d0302100c1709010605012606010e03010e010e0705040e0705060f07020a1503050402 67
    0x140054070144425541e40160012445090f801842c2080046a0054039400007250410b420500d140c03500705c41c1c59044400404007560500f0030a980d0340b0f00a05212203000804080a140c860320080000140c402d00201c61039803e888020384446582c442c00c441003403241c2e030703a03900720000c91080315641c0c00c0310549000400c00003805280c45402541d194050016a40d0f40342c528540d2000c5055001840d40e8080c0b580a11001d008649800c0c040c00d26003103032040c990b0360110601080b82840c0c3c0400095440340c03a1050143c00843d9001400140c1c0144103c0c0000303a2000100742a1400c10070001000c8000c82031204001ca03a2406401031002c0b18801c2c0c840e05846c2450540c2c942003000001050300c9000071700c40025049620885481e4001750000c1c00001c2c5100d00118890b0135a40c04904c0e594485d8414003003009103040900ca45a0080c1c428000341441c18203110001e0010b04c500302c50000e00c0240030822100f590784d05d04480c00141800c1c2c82c400500c420a0801030090700003210164450100c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 781983282 1250 781982032 781982041
    0x190501060f32030709050103060f0e060f041101050c01020706020405030c120c060706060b120603060606160206072904021f200708010e011505010e030d03112b05 71
    0x1d440b00e590880300904031012615030410381000a4160040855261244c0440001d400c0f1180c0304090107075010340004102e1040d85c81d480d0041d00c1892243c0103981d4011010042072000b20482903821580c464842081d800500004030344900407200d114446500c0001c84c00d04200d031f283d009004039407081d4291031786113090004011100b010040c00d001d8035000090700b651103283c01e034010180301d84560000908151500105000d80d080114003502506144040c0429450100004c99006078122a042d2421041c64100e60a003880c8040c000c0c05403001003012010800c0071900008202c9071421442803502560406d4030072030500345c9042c0e0081f85803c00c02c0c02d030a0590030f0120989039168403440e000440c0c044030b8075841090100012a10b0142000c041100c0c1d4007800340a612141c3c00c1c00104001c02c40482c012030700055540b166045c403101e03220103d01620702044600052000382000a0840b103130108521f581c4c8100040200840c4801340e03034650451551400052107000701000b081581e59 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 781984532 1250 781983282 781983299
    0x1050c1002040e150a090506030102040f17012d09050a050f0d1112040605030901140901020a120c0215090106030b0c1207080108061b070c0b0c1506130e190501060f 72
    0x141c1c0d900356401c170300460814440400150400703a080540a00018030301580c803548403d48503040d4211810300e40c28003104042440c0d0900941c400411400ca4050344406808000c61005000401d6080001d403103e03150428400c05100114443d50004103682072441c44d4003000b6201c1c8c01d80007810001c030b50000c2c0c44000001c0002000414101c40085561500d400d011040d1403c1d040104000c4296486050f010100c20700503861b140240c0390200096110000140084c01c600c20a80340c64030210716002d41c05a1003a400280c0b24101c2c1003014510340142c90308011103015199071341000d81901095400e01c100e86240d40010b0600440e4084590556190780000710307842d400a110f810b070150301c284003060000030844500301d84041d046228520309516a500c072035200d040d40c1e01010b909980407420600000c000e11100c0c8c80503110780030200a6240020004e0f10140460721401c80c0e180d07507a00420201c0d9020400d60441100c00c0b090582003920780e1130480c1c0607000a000c0c00e8115501114005154074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 781985782 1250 781984532 781984561
    0x90f0e0f0a051003030c02061b0c040b0301110403030f140304080910020c01091518090b0f1c030e060408060a051501020f0312070203120a0b04050f041e0201050c1002040e 75
    0x9510843c0103c154030f1510111421481d80c030045ea40507204100d003043c1a03240442520b40380300800b015007142c640394000c00044a0360040c016000340d04000003e20310b554141d04984c240c981c103041003240c600c01014222408480c881c480c0d89608800130900084c0025040640581e001c00c0b00c40205803c1103000403600c40040740000350114101640504c200180040f940b0382400c0c2038035007030402c4990046e07100c0c688900d039031149041c960340701d420307104e40c0c14201c600410791841500c042c107107503410100b08020006003440282c104800d0380d9421041d41e0b20141141c0c020014002111194104450b070131004190030b59041c148940c8000c0900d440b94008115800c901403410051f5082030703030072550060803800c001c04070300031070004000103500546211080b502820b4040000202401c007502840101c8401900c192020480b040400000603614001c004180350020031400d0014414030050300d01d8012080082c1c17181c00b540c0702c6e054010241d036000e80202d1b202c0700300c41440b80c0c41b8110600041c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 781987032 1250 781985782 781985791
    0x1302100e030d050f1204020118061808010603080f072102100608060c07020f0d0203010612060f1418010e190c0506070203031b2e0506101d01090f0e0f0a05 68
    0x3031300030b0119210085801c0f8480f50700600604201c02c203040700010074182e81446410204c042000c12040d011441140d18031071001c0d11028000700002070640d01d0700034660080404400ca4050002491400c0016a5220135034001d6240e202e80c101c001d00d03550183d0bc130400c00004014451500c48005210080010003500070b85900940b80d1034403c6075000c0c440b00984200401c2d80182d0344180200041c0c40900c2003000810585440d0b001215042c40e01406849030800c0040049044c18983c88900810b21403041d00f2100c04941000000105242580500705042d02100e0034040c5442d2807600400044851000c94400ca40021f00b0988680410900b802501c40194050380309008502c90030941c031040c0d446001e001000c84000392200d01280d408031804072800c001801280c05c2c20282003910f40131b09904014101c80c000d00b60030100800a011281e0b00c1e804129000d00c0c0b40031441180d00031101c007006040c0c081180f4420a49403004c0d030141c21020b44958a80e1000c82c1d001924404030741c411503005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 781988282 1250 781987032 781987057
    0xe070f021507031107080c0f06130209060f0d15050106030f050f0601031508100c0e0f03151e010b0a090b0403330c030e0c010906090306051302100e030d05 68
    0x1c58031005400c40081803400d0301d03801425410440c00740840e129401605403541e40100910400065102040c184007001e844c85a4211640300319500580e100c0c50000e0b88000240c984d4a0003c403180d0000b0010102001c02500000082d406c2e0300c680d840c59080141603506e6918144010b200b2803a2410403928201d40c101c29030346030300012607900c0d0b209420980c1e40c0c54401d80702c0700006441d4806c0c5403e1400e0164490011769070780d0603d42e01c5503040300000d000408220f03000c0017004640008203484058202c0c0700c0c5010744502c00004d1044010b0903940320601c2400c0714501443d0f071104100ca42c5a0301142e0319401084100c140003035030b0940c0500302d03070649034841416034540d15030b0125115048c2030035203108462030a0000340c0090004a10940780341e400143c1d0040347080c5c41c5085100d030034080204003850400000e8442400b156402252810031a40e1007100003855680b50701c002c07800b2802c8440004d520000e008000d01000c0d50080c1c200c151354071b0403800d41c1d000014030b610507120380c41241d180880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 781989532 1250 781988282 781988323
    0xa12090612090f0503030c0a0801091a040e19052d0a030e0d12030b2103070f02030111040f0f0509070906050d2018060c151008070e070f02 61
    0x7480c002503000360041034403400082c801c0501c10398409082d0780044800d4010300201050030000c3d25800f401d0079005040040b400c00c00b580d02103a2600803402c10b46105030040d925008140d15141d01008a01407245091503581c0090540741341c45078850381c40d46e00540300f8425259a00303520405a003105115544540014010541107a900340c440d00a07181c4025481700c8030240300008100703440b41c1d605000505a40c0082d6007111a0200003034a05481c10401400341002c8881184410010444500c550030040e0640564030910001c2c4c090301c00b410800d0b07032003100480e000030807ca070302c030b481c1040d54004040041c080c0d8481051041071041240d030070300002d00b000c6041049500440003840c40345031100d80071070390308100c00d220703000648245100320f420342c0d001505403084624019501802c02c0f0441d0b10610300071800b031480f541c0784840072080c1c0d4040028404103010b150340c051403c00a120034010b8904c0b0642d580c0c000e80c59082e0803505100400c400c07803455500648081130701e007a1041c1c0c00b0080c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 781990782 1250 781989532 781989557
    0x20f0610031b08070906051309030207180b030307030f12090206070b0405150c13050402040f0b0a051207050304110d020112020c0a080c060403090515070201031e05090a120906 77
    0x2a001e040c0c0d14625081041c00c9002043c085002d020303c0340034151061011403031500c0d20040c460030171502c02a11402929121850000a601181e03030012a0580034500c91501600d0200f5002840c8811301d2036410700c000140c0b907042540101040348200311513100d409104803e100800e0a80340711400c0258401c204003c1c000014103061031050301305e8080c1c42201d69031480038030203030301001d000d641c101e0500c52b020070010411241c0070a000d003d080259015410245868a0720301d07000310300d0040c9103418a001c100c0d51a19882030040d81c10f500b4051400325501d080c82c40c000b0384a80d000f600c0079038a400c00d0408088180c00d0007000d01d445154180d5a200c80c41c1c0580809070025000440712001030300401c05650007103150032001d000c0c5048024050072890401c1c4c600600034000a60040d401103448541600c078078861030081d200c2e42034080c02d010035840f55881034506066003984901c110189400c041c00940840040c1c207a150386e108141c1d0045401e5400d8090301c400155200303040000b0301080f00c14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 781992032 1250 781990782 781990793
    0xa060f0608122208160321020a060906140a05091501140d020111032107030c022814030a08150319170406180911040b130806070f020f061003 62
    0x840c1105400b84852410a40ba83c12450070a04810303040c50b42c46417042c20500c1030046a00c10b144100c0c4119680081c950000da00c060b46980c00c0c3c480151501d95210103400c24442284c204024101141c04265090318041001e4401488103075403015461182c40311b1583d8032500d4499040c144c80aa9070760425206000007040320300c05c510b410880c1000300d80180302201e40781c10000b4210f0310307080c07210011301205a0100030010f210010405d0041504040240d80d2030380d00418030b1300c0f14140071102050841d4504030f40354088040c0ba1f000420780945200800d214100200c0070f400e40010f16641c0c81c020740c84981b240154500d100041546c582c01446281c4007c00400642c06101d92280014000b02c03956159224070f140c10507409940461040c02c425680c0181c00b00220703028041d010b80c04c00142e9205601110a0b01a900641e007208100140350070305007101c3c0708501c1c0207050510480300305241c0312500520540d400703004030001d44129116400083c40c041007881c0b1580c9401084a44985951a403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 781993282 1250 781992032 781992067
    0x9100c0203031506031e13060f0908190201021903020c0115050f040c0e041b081e0411040b0a14030c060903120f070804030b0403120905060f06010905030a060f060812 73
    0x100318102e500014454115624150710328829070881c1c2034081690791f00d06090043c1c803000480f1100113480d189a100008800506590034105100c04100c140c14406200ba030091044142a54541065111100010b0b50680050500c0000390009014205840ca540b629051031030140c01d80c0540203940300c188500b450b50109d4070042203850204001d00740080072070704980c2521708541c012680c520315866100d07009110f03560408076010b03d40c02900c40000c036030002d0b203102800080c0842202401000b280d03072660445050340c0c1d00204440410b65490030282204614682c81c0b44c02802200540e140b1440c100003a2150248054041c0c65100d02d00710f00d081065000095099040b041882608082140e00001d4406540318203510003040c141814041c000b012040c0111000d0b60829483c1e00c0060b0380400c415401084d02d010507155600d500c40140d4440300540c014a4052140c86c10007818040c01d600100511000038104000550711940c040d522407210002d85025180c040201100340c4090441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 781994532 1250 781993282 781993291
    0x911031b0a0816031410080d0f0c02040f0b0613030506060d152c030a0813080a0c02011101020c010213090c080f040f0f111e0315180609100c020303150603 68
    0x4e0000311300c4007900c4c640d40582002c1c2c503031511040391b9901c148409041081907024140803800e09402800450380c0007031480251900007400b603901c9134111020411603030001703202450000d01103030329152030403010900381c1e0f018070007a030b2513100780c03408140c031800c1044040112603005650801460004107480c07014051600c08210415107a04603c40343d1020b04a00009107800c0c2800ba5990b4220300300000d0207820013520803290f40d1980900140014082c1c400c4a03214052030070316682e02034131800180d46100e80b004040070365500000e07100c0700030700040d0f004008031400c0d0140c40915507210090842100c02c0307006d100010031400400f08601010010b4140d5101d0b118a04031040081165035401c9091450001100c0600c0400c28400c0c4d585411030360301c034040e2000c18142840d00040c00020ba0b55413005800b01088072043d20124400700d024564900e0003001d5182280c0250911440e83c1c1d0b5110015031481e040b651422011407852803010045a00424031205140120901541081202d510142 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 781995782 1250 781994532 781994537
    0x1b030c050a200d09030308060f1807270303090b0a02060c0d0e0a030302030601032406050c0f16060207060c0309060e03151014060301030f1403040911031b0a0816 71
    0x26111142e8010850303210140d01c1a961442400d25500d400b40c403c5102400781840b800c04046644219180c100307101c100080894050007403516280c0b816103010608040004003404052010000c1081c0328801a0032688255100e2a2540d0f8842d0804401c1c042d8070507600050300040045192030860801900b140400b0440c0000d90480d001d40440c60113000b00c1c411004aa004070070880d1640c0c06201c0c0d41480d0100e418044544010703001140c0c103c00003400743c00700340a008a24100014808c00c05200c0c00300d5200c003280c0c401900e8002c07841c0d402403a481034a0040c4aa40008501c80303111304030384000568151602c040741818844165402e5240030680740e0584900040e0403010484184458040c3c0c0c1200d0a0301040d504100c181846003e0082c0351500a4408100402c0040e526200c0c01c5001741d0805c240081c0d10105070070141c154461688103c9a407410084251018601100114054209152101c04c0b00c981c1600c542a68000c655a0a01140c9070500040150303201c00c100d9609202ca03403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 781997032 1250 781995782 781995827
    0x6010305270a0c05040c0f180902030c1207050c0615131d010b04020f0405091e090106060e011715030f030418060803030906041106040b030a1b030c050a 67
    0x391500c000303a22460700903034125030180c400030042c0800a040ca10241c102907400f44555200324a018242c0c2c0c0b1010000f0041011901017040300144260307004015001412043d907403410039100c0c954150304503d03280784810310000c0c0485c1f07403240500101d426080741c200141001e9682c07426200701500000725500e0f0044031f0b0900300d04814200e0b11031501c04569000f034201e6058000720000d0f085a42000e5210301451040200071385030900c0341c0544049400480f080c03003496482c941e101d00c4241c480c103e60510042c682d414044054019088441134842d01d40d01c1c021054100d030011034691500e4210821047c240d41c010590f02c1c05404400340003800b0140488142141d200340881c170f90b50241d4002c4440719003280344031860300c507540071318001081c48034011800d50a0441030706480b0036010300000c00c4a80104510702e03a87c4ca49030103031001000d0007040c5580740d24000c8100005460101e444030060011144041041400b80c45400e2030320b0f0391a9100d1b401e00d01901000d80c4d039009000f80741a245c0114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 781998282 1250 781997032 781997071
    0x9020307180f0608160b0f040305150403020c0f090601080601020a0b0a0921200a0203061627210b0705071403040e04020d29010f0e01080606010305 65
    0x10712440c8610303000c501002803242a002800030441e0030a41295000c0d41120130798a0340c0341032030b0000009843c18012415902d40e040f40070710803a4811070344010828010100a01c4920300b00f261058480c1d40684c096446d684041d404005442c012543c00b96404441000801e500d54031614034564401418011900b02100544071910b615504a030304c1e603003d0b5110319080d001c11070811082001c2c802c1c09803100d0322015845d00f003d4442c402c070403501042550803d1070a84004801c0101c05129600078045d140181004860340b094084a04089008503041c03041d0b101c00ba20205039200b009261292500503040c3c00c101d1858010440c6442c1d1200c8000d1b55480c1d01c01089003010040c1c060502c90321074555410842c40d108031201c00d001c07080035445d0820711041045803190782490350712543c1100c109001a6440c601a01800340c0c801c550b21582e4044104d010003082c00201c403e0682d50320b51100410b2559a60801c07803190b10034013407031103543c00600105115502980101d5009445844070300c8070500b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 781999532 1250 781998282 781998299
    0x1020406270303050f073002030306031e1009030e09090d020a17120f090d0c05060c070305071506170d050405040b03070b0705010c030b04330513020702090c13030609020307 76
    0x102c50901810115800501c0c400e40b1000019140c0400c450000c9c40c00c510305100000d484c0d969285448220140d41c0402c202400310611000500402da000204080000c90500400300600c48560500543d40800440c540660005204044244030b1340101408142540c49080f08107011041c07019600c000d10524403140400092070380b051002c0598501d851170109082c0c4d1034030b21910801814007003030504080100d0b5020810990005406441c40e90790030315403038101c0d503601c509140130301740c000e49444011001c540c0340c00200844001034403c1c903810424404180c4c0700c11100502c0408903204220404c014180358112000700c11000302900c41d03050769822884000da10508086519940d2001c2501490ba0540b18500448100f03480411554502025400c2c40035000b10070080c00c0d4840c186505410070601d0100c001525000d031036554240d0052070540c0c0031390840c2c1c0d0304078418910f41c80054140c1c1ca040007078031a1450382c06c01c00c0e1411851529094000e156150041e40c150044410111718000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 782000782 1250 781999532 781999553
    0x105041203020a1e0506451c12110f070f0b0c1201030305180319060e03121609050d030c060b09090d2a0501020406270303050f07 57
    0xd010740c01400580203c1d14010150300c0d4503485103522000c400c004040454000030f03060380e01005105030b010b4603081c0510300702200c091070002250841c0e01441010f19007640e0f0203030302030b030202c14508487c0f034840c11107144403190a2a0f1211400214001d05012a049654000001c1000c040303003c5498022080500a6a13902c03407041a50002450b400540420010120040e03014010381061803c10800d644606540c3c2010300c4054100f00300462072000304401c4030496285940e00504503101120060161014071010b04e200740d441d01c5c42d0194245409901008485d003d8600c1c1c908041542d480441107164030051041050030041d460310081080d40302c1e00c0300c00d42e20300d01a407585040841503107030542c1500c0803034039554050a80e0300c0a01c01a01d000040802c18032255050800d4806c03210280040c4101e42d0054041c5c0090280d10000140681076000f84266861540d80c40180b0701101c240111012090403020301d203041032102000460302c1384018050440e01c2440302442c002c41174842d9032115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 782002032 1250 782000782 782000819
    0x1115120403021c05090105042c10051005120417073e092a071a1e131103030703030b040c030b0904110301110c0303060901050a1211010504 61
    0x103030301841c1c1050320300707050780c0c03021400f00ca42d80380240c945255080020468010b500c40c502d4040c2c90b00d5130000381c030a1880d4019440d00b000004210841c41c3c030140900707108020744102d42c06a038a00180710300c140d01c64811501140040807603411152501c0d40d4420600050107070600754454140544000502042440000d20780007001482985458511064890018035000c1c2062014000f00100035150300864a40c4000380c00302064681c11503440c1c0c0c43e0003284c43c414500c2c0c1c1e00030000d03030384041003d07401c1d1a0801502c000300c0b2001a94501c0314160550742c00a40d40010b24202a00103203648003124801024a485280c220380740c0301444000c2031858014100c120007003a25105529660b0915101c0c0007140400c44c5028414540d60b034010401c084409800a0140c0c00f03040c0341c11010361400d402c0401519a00f1151b66623400342c0d88086a201d40041e034545100d02d5406000090500d01414560241c074040942003207041c0c4c0076654061003184a0007c035041c84418440081c002c0108608492507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 782003282 1250 782002032 782002037
    0xb030304080d020c220905010b0a0306050103140604021c02060d1b11010506150d060509010303050c010605010507110103020702010e0a12050f030301141210020f04030201030b0301091115120403 85
    0x8041842c5000790501143c902c480d401a2004d41403a01c4110003001141301c04180014000b907002800d0030078074007400c261206923401414200c000010881d441e40583c0c101c90052492275182c0001001c510f494910542d8065070240e0071343d05c0c80036000d0030042c400c0c20342c61001340741c645001542d81a142c107a80c464075041c540000d009003461803440e040380c02c03003041c0402c4034000c212a1401100040c80c04503d41d050700c41c10500840c1020076088258003000281c50001c005107299039583c50010132682c8601c5070b803407195003002400182540a4425141800e510100f080020118040110020740040000742c0c104850340c44845056104d01c8250005000c0d507048003051503042d810802d2030b101d61640e0601a070782c02080100451000c100d013080c50346008654650505003401c940034034000001c81d03085c210be44001022001d40030780c040200100d0b8401c1c1c0b003c0c08085003e8040500b29424200058440c0160280c0b0715020710340610309103c8510102e0b00386080400e078140e003440342030b02103400302c01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 782004532 1250 782003282 782003293
    0x1603090c030305070b130c0b1b01020409061a04030804050603190903082d0601050a020f1b10180b0a111e010501170318010504210201030b010e03031c0b03030408 71
    0x74045e424510707541c4501d601111304040081583da0160500f114800c0c40328660010400c624500041c4540081c1c9404d10f0000f55141c580321403901d40205403c1c8200098051011811104c2c401c1c0f0b0000e03102201d402c0f23280719050907d441c0034405540d200600817082c071080c5183c000301a0603240b140741261802591110701504e0034800c41b014000d480c0c984140c0401c12942c1402c00301042d1020194030010a10b8801c2d11996804402c0e0b00c0c004603455001010300a0001c40510f84e1a00b002e5940d05200895110300d4003101c0c1030087c0d442030440c1c100140c080e000d1040900000c10010300510001d5410325003440c040030840c0e505401c00306003510502d006d100c05040b80014540034040c00e4050000301000090314001503941c5070307503446850051110000242103d407510b81c0901e007550000d04058100e4071440c12089283c2c680d2004808c0700301e021901c1c203160001d040d4410358044d60312050180007580b820300c000135052494083e20102004154403070158907603944007400a032004101003c014003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 782005782 1250 782004532 782004547
    0x408030a113001050d15180209150103110f03040f2f090601090e0403080714030f18190303332c06040905070f0b09271603090c030305 59
    0x660b040010b0f40720605c500c80070790541000c01c5149007404101c035060b442c0081c10010641c0e209100340420f04010b03501c00342040810a03544508480c01e641510241c0e0100640ca0800543c0d403114054003840e60107640c81480040c000450703454148900314000c0b0000c03490440300c403180b000300400070395064203a10350100107183c56082c1110055002039090034010a410b0034130035151a49003000304080e08024545001c81e88040c01a00004605800d500c03000380d0b41e1800c0f640808185c01d0581e1004062800d546200001c01ca0200702c5007594915400c2c8103504400b241c4045010b40201843d8103200d00d00c210f00c40001401030500c040d402d080c6e8402c1c26500c0e5280811119409440a40c00c80c0101d1088018140f8581c1d910f000b9a0700001c00c070b40c00541c0d030381142806480c00e015500300308140703420100040b6803070341c1ca400909440402140d04041070000010131001041014403100c0c0c1c000510000b080400f40070105c00c0180b01032510740060000d0003502c500440000c00e40c801d0f4042000040e151 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 782007032 1250 782005782 782005867
    0x609050711160b0a05130803030a090218010b031b31060e180c09091503010c02030f0409021c15050127180f0e1608060408030a11 57
    0x10980000c6407800c2c0500503d00390200c1c80c10310803112403804200c400201244c00f81003000c46840500100340440c1e80300c0c940340703c10000404909905034170412040f410710030720000c0c0980e0541a40d2080110b60b0660f2940420a0b0929802c5c2e103c400c40f0801c103201401c49d11260b900840552012003043c22100d0300300e03901c80d2944004940000b02001050182d0115548a811064800c4181081d0401c001e64030240014018040c41100b15880700b900020b03c00382c0d15403032510313140038001103008010b0108003038016603aa00c900d40d800000504c040c402084900b0b03c80e07026080100d12180503000c003041c400340c100203c51522103208021403825009001da541d000029000d8000d1f40310005c8414261114003800c14626882061030f84080c08040d8030b0506425003204c0e02030054000c06002d00603804004c1070702c0b00c660310302c03072501141c4011000807000000200303d0b00071500a800540356440342d0058102502441c5c4580d0301004c41000350300d1108840311104420982407040e4502119078034101c1c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 782008282 1250 782007032 782007043
    0xd05070509100b0a0e010e0319060c02071202040b01031401030f0c270e10110405031005040b0403080705040b030903030a1d03180a05032d0102070c06080402040609050711 75
    0xb4039150018007018070140c900d2400315044030100d810049201c0380c94000480e14403e242c8820764042c02070740074450300309856400c0326038030b07031701c00c21052055500801049030784840034406c807041c03022424051005420580d00403a0880382c180b501160007800394003100180030f000e80c070460b900d01c10000000c0520a181090704068185c00d00b10480024044131942e03d08840c40181c603409590303886400d58008020081035507075180008007400a1050b001540032647c00a22446002e4096210f2310038890b0b20601c01c02d40300c0d61340003004222948503034404843c0044000c144000303009c01008040b8003404032074050762050b00300400030b40d624600a404c0c02c041e00e4050922074007004c981c00d5426a180000300540351741541300f00d007500c1d01a2407500020102401944220b4050040014050310120000c0d41841c131000007041280c004e00060554608034407562002074a409903816090003020701c00c089031908180010008905c15494081403021910140c2c0c0740300100c0d032407000356402c508080c480c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 782009532 1250 782008282 782008291
    0xe070602160329190b031209041a04150603060905040816030e090c040302030c09090d0e0f04020d0c091706040201030f0f0528091713030609050610051c02010e010c020d05070509 78
    0x250490121fa011010703d04d00402d41160f204580320900e04025a4007103d20004210340104140901e2103c2c50301800074a150b0b00554001900748540490540340c4d500406000b60380c0301349980e140ca030034a05c003281041c1c0040c60031810020b59264010807075540d907038141e0248403100c0c0324070703940c81c5548101850810111400740c0142048020011148404143c3e00350724901070810386080c0120302e0021307610200d003a0301c05030300c00e20105040224040e40c0c1d021030508400c0f52214042d660300c3e20341c442103083e4080c0a14680b80e012400207401548a80c009541c181070545012502002080d90030054450451300f0348003c140c2030b030405280c4c05007801c54041d16031900104204801441d11040001d4904500030b805000002804006860550510324000c58000004004000003487d02c5034648805540c0703144e1501c6120070104152a20b050010000300b0502da00c1d241d118841c2d801981d0401c005840141800241d8800d8005a141c010703400030803034443c4014021032030070201081201d040160 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 782010782 1250 782009532 782009539
    0x12080f071a18010903020606040e010b120d021509030f1804021620010c0f0804170705040507030b100e01051c0509060a020412030c1b06030e070602160329190b 70
    0x191600030031b402040b4990420011748002c14445080c9110134050030004c81c80341c0e042038842c0941440710038081880041001943e0995264981001e00c101d240281590440c3c9079030400c100c68042000307070000500300b0035415418501a0018000090220303042500324070300c9100701080c0b40f010848103c4404c00c0601c052020798441781340250000380360b03d5100b10010316000131701307031445d040c05014020b0f039008042c10251420500c443d2018240c44803810305c10f0f18012418000412455802405046c401d01030240c89044040c4c9000c10445003220303102402030500500b001407018a106c804069050b1a002c100049800d0405a003890315000b0020841c644013841844280607046100107101d4041d500341c038100a041c0380e207041c07543d0702e44992400e031900d000c04410b0001e203440c0c1541188860780240c4090702c206542e0340c1c0c0e0580e201e0102c08526030090055040c00d10000b40407808918a0862040c0c80c089201c3c6540c3e188040c8260580d2424840304200280e0742d01c20005004142c44c8000c1613 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 782012032 1250 782010782 782010791
    0x91512050f062a030606070609052407080c0d090203101a060c120d0e0307121704111309080c03030f01080106080606060706020904060b0a1812080f071a1801 69
    0xf88101000140c01c8051080590000000c0781e99030b501d0340300f5030305196000705040103400214a080e031780d81d0642c8c094540c200403843c45410352008415850702c3c4501c000d51034443d941d1307403101401a056480041d824400d1980c03070110a0168a08200000d0303036251001c000504040c00680c1040c01244403d856885418104034204552201282c9503000300c404410b6251101050940344018289070280f5400798031021600c00305010148100360340140b400e444581841c0c00440c1d82e200c117007600310b034040c0c0130b40040d855202c12030134050004800440c9000f40040c564006940390300980d80a000300110316070010090200d41c402041d031003401824000c1c02000000d140805050315a4001012644245008a041d005000094049880740800100b04101c556280d003182c1c40d458000100380e40020301611000514103a2800906040d15110b01c4942206000c2e56a0400c2541c00300c00c10f06100d000074028100001d01c00e5014458064000f5034840b000d1401c07a190018045000c4250401741e07040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 782013282 1250 782012032 782012071
    0x20301232410050a0c0803090a0209090a0c1502070302040e010b030607020d120b010c02180106030c020d2312070504150e0607060509011d1b09040309091512050f06 72
    0x190000c40c554030510f4145240c0754451001e0546004c10384c1300303010304002800400c03c00382c0310001c50000d0b0858801c03a400c0030142c403200f5899076940c0305840000d118200090050145c40d091480c1c0034804507451040790b007030a44076400314081e50480d010510090707440d441c18a21a16040c4261036100945100400100c2607040740200031413203100181822558600c640c0c4441c1e4440d0b80345840752038001c0c01102044204080d410b0844500f44540000030f80b4185a84140e244049000c103020803641d5100002d05c0b205036000ca90940f422080102c00c29820014031a030700600000461181c1794079101c4644032450102e20700842d051507a101403c0001c0801c0400c400c0e42d0b502c2c16170b611680c002c04005210303500c20960030b00400e210b01c02c1c005071102c10344000070855000100c80111000d6000719a254001c0c1c1c0042c80008182900c0090108040d007805111800180d40400c007141c4c3d2400c0310b850059525904000e000011002c25a4903400203014500b04920400c60b56421950400b11070808110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 782014388 1106 782013282 782013289
    0xf0e06040303051008370b0f070528030906180201090503031617091905010f02060c040515040506030109091e020f0405040203012324 59
    0x405000076100c0d1a2105103004460105008080c48441c4405c5140343c40146001c9080310100b00b0101030010f0110f028072549940240c900c151f00b400c110f01c40402c046070050912080c0304003000f65240b400c072078141040c810740981801000c180184642100603040d03101020309440d0a0100e9000c0365050003075800c0419100342c8841c104070fa41c07001459107a0041c564110081200769a9000105500c02c100034032984105c90054900910140000c94204142484e10b024070803201052101b56009480029410194002000e01e0b185c0303d280000544601d028090180030001d0701e0b030130744040900580d00500401800d19445e503854600c1c0000800c07100c2e10030764101e031480b1010344040307804c024022804d40d00504442104a01cac9802d10014102c0a0300403070b0107650350218107504451800400000d00401c942602e1181007445102c0192040c58200c0b844001c40e01e4803c0e0034554 = true := by decide +kernel

theorem cover : BRFrame.Cov 781834532 782014388 := by
  have h0 := BRFrame.cov_init 781834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 781834532 ≤ n) (h2 : n < 782014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
