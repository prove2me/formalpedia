-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:33:24.224354+00:00
-- url     : https://prove2.me/submissions/dd42c073-9b51-44e4-b291-0aaeb078ee7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 736330935 ≤ n < 736510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 736332185 1250 736330935 736330943
    0x30512210603192001020c0108010e060312030f100602030c0c060f0915040e10051c050114011e0509010b07080304060f1103040203010b09040c1e0e0a060e1003 70
    0x451220804154140031455100001a0032900d0340e5044508091186040500c02d0b94010300f1413140c0d0441c03000e1000300041d43c42e0207000814071459108002082650f052040180c0480454007087c0390b9030307007440701e21749100040780020703141d0030503c2e0b00060920041c1e48100142d0f520181c00201c0c0b90010040c2c40d01445068003a041c5100d8a03801e000c544c0d40101d50800403d20300300001c3d582c0e0340c0c03040754298480e000840090f0300c0b281020310b0400181d9000d00190b030812080c1d1020003003655441107d00250101c41c60307120b665202841c00a000d030040010141e51401030078008030b1620306188130180030302e1080d07980c0d41d6174559131024800c21413400c0c001c04040920070059100407a9543d0011500984200f00c0000c1e030020751550b0b0001c89105041100b1852000030a01095160900494845080444203040a03003003d5450862500780ca01c02e820f40c0c2c20302c000880520708180f04031030006207030064410710b9914120041400908090092081f0b8401880c0421490440710f81c1e80b0050300c0c0c1c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 736333435 1250 736332185 736332217
    0xc021504051c0c020301090803091b0f01140d0504050d02070e0903180d0b010801021b0606011e03151706100e06150423120316020d0201090b040807030512 68
    0x2040d56828040c2d811080e1018001010303844801031300c003449410030050003036a10548a04080041c18140564650071488880f41e1408907038403952200310381641d454090910800002c81d05403e0f1031540285c6000e2600c50b032500007040309020010455004400c0700f40d0944440c1d603280d03140d0100b80c0c40e054602c12440c2d0300901000702c0202c14081005005e405c000d001c0c86803120341d5918000000800d800001290b5004200c1f2040d040f041d404000c41082000d0180c40c141c9030000001384142c50a590164400c2400c1014681070b5000b5880051030480c91a81c0320400b6440d007501c200b114507100c0b070341d4145201d0300303002640e11a0010b040ba030655450740c14215161300c8200411800d0015501c120f03d080f40c0411000a940907a204440503c840c0420140c5100c075241003008444c0c41308041412994204000070049482a100b00c01032032641142c0102104031980012160482c043d0000e40084a0000c0e022035660f0380000c20204480c03141c0d04851102580c0d080f0310020f130040c24200380000721 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 736334685 1250 736333435 736333453
    0x100c0804020f030703020901060215181902040f0603081c0c0f121d0f0c1903060e0f060403020604050c011704080307020c03071706011211060c0a060c030c02150405 72
    0x1401035503409042c5070040440c1c0106860360002450520281d018a025a0251072105507601005194550000c8446840d00c0d401c00c1a0f0700c031a81b251081c4c80701414a0b4034402002046550f81c1d0311402c01e041044204015264072032603e07502030340c04100c54000d40304050440b500e15100c18001e01c020ba140136650042000f00074641620003039881c80750345c040b664235a00c20003100c8222107114101c0e5034412000700185074000503414142081c2c0c9010311302540c00f82c22060801800c03050b40900312a48404c1c00605100d45820300d60070a00201020300c0b180c040d80e01404181580041c000340030301d00070800d440441010b42c0064400401013a503820b149200c04001601180d4000061503200311a40159400c40c0d445100180c204040c581100340c22070741d030101040c0c1d80c040c10050940500fa0314600c048160f251911410b19900b031351034010307126100c00184100c01030418000500e8050307120380d0a125003e8030190180140595490f40703401881040140c0c4410f0f4403019599026907000400f80050701303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 736335935 1250 736334685 736334689
    0x4050a02090408160f12110718060302060c010603030801090b030601140303090a060801321009091103060f01170f060415030b041109010b180a12050609100c080402 72
    0x5800030400d880c50303c0244820a2010b00703180022410901c0f5070a4480140c072030740380040004280341d40303000c10400d9110001444101c00039030141921030440c403111107524081e401c0d03c043c100c3c54000075041800444c140700143d5054002e201a00e20a45803140030380e81340d140c490304540e8202403aa51552003040100b09454074a4805516040c0c094152031512409101141450141c6d03800f88001652070401042401c050b4940e41c002e0031082011840c188a8091042509044412242e84a45404407401380503d0041d0001d10041403402070910200441842e410256007040310601d000d142d850304d1120316984180301c00100b00c0c070100403090f2251039600c118151000b008060300c1c0c00540e00c00300d03112104540e04502d80210321400c920070341ca00d032030f14180070392600c03032548175000307007803004c014485541d000c02620032020303c1c100c290ba010b034420750015001300c88a60004000c003c0c8006491300b407000118040e48200540340031604c07107030600c00c02c400496540c2c811410020b003041c03010030018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 736337185 1250 736335935 736335949
    0xe0a0c0612060e1501020c18150118080606010212040305030a033b010c0f08070f02010f0e0a0b01081207110301090b100614040b07060525030f0b0904050a02 69
    0x24804100c000107010b521104035100310041030760001d640300c1c0d04000c4c014032503a041080000c84076044d100c1540440c030352a2002d122850291a00c0c0c1150404a000d01c0300364030840c0c0c07008510340007080c082001580c500c0300c2c9861b0807040c0c6010340180a0524040381002c0820111000c8a80c0b080041d031a000512208900610041e00210040c8030030500701c0c16650300c0c1d107882112005ca80762200446490740118142102c80d00720303d100c188140792504c400d00d250000925680403540c1c2c100420307080600c002c05c034010300c1e17030f4a9207074161032420720300300d040140000300c455416104410322510740e6200d10011341c3d101040780c02e0494604081140070000303181e4024000d40c072080907002044030a250383d201909030904031035941c1550011035040002c1e82c2d002104680746a00c280c68a4034040c00c003001164203114003040981080e17252400b248030520300350034141200e250b2445510500c00b03500402005401130540144440d42000750358051481c0c01030b045802954803070010310144046034288540c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 736338435 1250 736337185 736337207
    0x90907113a0c020a0b041e0803030121050109030e18100b071505011e06110a0602090d1505090c09190e1002041806090b01092303150108010e0a0c06 65
    0x421607001e82c1c40005803030f071400075006002541003060302c1d64103080c07908260160741051000c03004503030f032000c004502c0301204490540360703505115005911010fa1400301801c003102c000701198601388010091590000604060000072590721803411982402d81c200101c040d1410802118212006c020780e00d0000018603000c0d10640712002c420007402e000b2021a01d09920460114541620451b000300f0303071212990241c8030307504160b04140744000f80c01e580c40c06d100c44010f000a90019406c00c9943d40c40826942c0c4542c0020100034851040b4100009003c0644065030940314140c4004000e10700046a18072031004240d903199101090020b80f0302a081d110410fa2182c0506101c1200c405600d0004101608074503540032106011010610200c91141d0320103070009103041900b0001d80c1e403004002c011a03411551080307028418031740042c01c1d000d140c0c01240d414480c445103d5070581d69403010f0350403521041c000b0132142c03040d01c07149a162000c001c401010380031500d00030701c01c0900460a00503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 736339685 1250 736338435 736338437
    0x4091a1b1303030e09090303060402030606071202010b0406090c1b1e03031a01080c03040209070e03030a0c1403280e1206091618050c090907113a 64
    0x82410350800030010039900003414009207010021040c401c0c10f4100d00140001202500d40c4480c5180000c3d803682c80b4080946058842c540020108136203503200800d98051369003207068045441e00d5040064001c01c00042500d0240d828000300140e0001c0c00d1196540c404490344405a00c0f940803503c500e01d035030400000700c40380350344145080202902c20a0801c0094800e86000a1000c10f05c524403d00c08440d240c094100000c2b00c04010240c4040402c0d01c1e08540d0580c0c21411503101c18000791760840c082c004030f0384c041c400803c03420300007640141200321080c060484040c1070b032038912209480784200042d05103042c0d0400d000090302a04030350700031904051468000600c00030540007503904d00440b08504000d5010000340300c0d131184144483c1640040c141c0100031468540001d056000d01000c0507291066903540c001400300001310110b60f9000b0b0020450f50452800703110140610910161100c000d2003417603003080c00415601c00300c40700a0b00c4090507201050400c46183c0e12103918003c200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 736340935 1250 736339685 736339711
    0x60d0510120302060f1501090b0702010215240d02091329071e2001020412050304150f080402040e03130305010209011209110114190c030e04091a 64
    0x9011044141100007852203580548418203100c445003a500c4000b4240081d1001c810301a400396a030042c07084412030b02c0032410991201041d00050313040c110030400d9001c0d613000c081c0030030185203818024a4084041e9460000020142070306108600d00913001c020742140c1c452000c1034403400b0401c44400142d01c508040c1486082c00c0c2903000d803c0c07034603803034040c280c9103040148403203c0d800c542288104980c5010500700b11000000040007604140f00100e80800590802015040203404907000303030844034002c803400203644c60000d0356941700e44a86051458140c80c5c0c403108902c80e408100011590740d0320005544c40319001c1000074810301c5c40550344c2e4032040150720b4140402c1000c0c640118000d20006132030314030f130a0002d042c0c43c04031151402c029180002150026000e82c02c403103003545080c40e000d41d44014030005181140324100038281507011031900c51320709030791001c00080403610030f6032510b6078092100c0c01d020a80c5e04046c4001c103581d000050b54014030842d800690b03032144055080e0f07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 736342185 1250 736340935 736340939
    0x61018090e0a0501020c01050609060d030927110a02061012020405061c05010f05061804200d06020c07140d06050702030d021809100b030a090c09050f0411040b060d0510 74
    0x42d0300b2a84006c6061100e65124810400c0780d142071141c03250b02c03610554102d40176600c0d940d001451010a4003601c000608480b1a0301d45a002c01400154004502d050401c41080c100d041e8580310f403c1a0360352001031156070b00050224540e401008101c40e9448040e0303005142e241d003000044d0200030030071078122200a04041461480e19424803645001d100009952a04101d00340c0c02e50b040108003d0082244102e015005400907507203650090300b119120b06141c2c9220500c0d04840320354041c480e4410510912002841200d900401076802500c04031960310340d481c02c05100113103034034040d1a4030680381e03035440d8080794094019940c01036003481034904c3c2c40810603d00003280c108002240110101c00d450305100e05259032495003000428544d002d003140b40000742c07025480028003174016551500745041c02c02034440455000303000c40302c1d014002803a04000e49198203200721000d0783d090f03102080040417030819104501c2c480c2006001c092400c1e0150810320b0103010058010503d0000f40c13640 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 736343435 1250 736342185 736342193
    0xe0301090204050a1b0e0d03260702030c1006031e0f0212010f110310150e060307030e2505010c0309031b030512130e0403032003061018090e0a 63
    0x90903c12a480d40c400117020308802601080c0c8100c00e010802071204000929050383d86400000c0c242541c14a00180c600d56008603500b4640589024085c0000d034100902c4a481c0d00030001d40020310446088034072444020848200703480e0203200c090b000c60b550461800300310400080a6007150b002d600110301c0510300d40e01190542d0400419008280d41d0703400040c0409010340074a840e9140f04060203411070800740e042d010340e02791503c40c880320b04891903841101180a09401748010328028156900c0b46841d400240c040c0c80c4040e82c8010b18010300000c00f5115800c002039103100004103030742d000e000e400e120040d2041000c8a4055092143e0b02500000003101508100e00d0500380601d03000c011072071850a9845d101c0c450a84030130000c0180710036a4410000701c804000c54040310135500642d101c40c01d00340c0c000c200400c4100500408094502c0000030000c00a6001d1001903c1d111100e041d181000c035803082401c1c0e880c18102c12240c1b810403a4415940004212000d00d03029114584410740d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 736344685 1250 736343435 736343441
    0x306040f020c121c09110607050f0109030816053415020c150f06090c0c010e1c0c0305042903101d071205040302160308070606081501060e0301090204 66
    0x40100c0c070f8240002c41903110f0140b85400401031003440814011a1195900e03000c02400411030180102000f041006c00d0000c1005940800c4080e1710080000e00c9090800234814042212070498166501181c10380380c603c12000c5507030300050342e001c1040b4490b00c126101e5503a0010855180c2029400b146100403400c202c110b074194550f000c1c1c0069540098000c03141c10502e42e2500400003901c14420002100c0400c0821580250207d0300c90486a903146083ca0381b80c011000795049a40c070381410b200d10410300282c014102140c0d80c1001c01e62000c00c230303400c4582000c490300040c0042c0c1c040c0020400300340c0c4205404c2d008030302044004001d044191400075550400c507100301c941202c0c00d00410134a50200c003030f19911001034218540301c1c80c1860019125120144001a84941c3d0b00d0002e01498070030701604058015404c9000900c958034104441769030001c11041d98450f280841c00100444002000341c81d5410007000d410b29a8a008410380700c500040c88469015500c9006460050f55948 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 736345935 1250 736344685 736344703
    0x7020f0d0201090b040b2701120c1209260a0c0b13080a0807080903044209030302120328271e02091b0c030c1509060c0306040f020c 58
    0x415210b0702e4180324214114050314440070500c80c007e030104024103599004080d4600081084c070040b4401d504035004550074481205014444e0b854000100300b00141c20402e00104001c0c2181c034001c1c15080500c241c504e100301080080400c8030072a10000042c60071001542c0410701680745008803070340d906c80340e6107039120403119800101000100030714950070142460300001d0410041d401c090804014124441e0400c00c01e980510101110000b4240120450301da0000c0c4521648080f00042e54054080c1c0544e00040f005401400d45030141501c0d91400d8034410f841103c849040d206404204a00d12604507103902c00c55600c7e011000d84801106c8203401d180d40c0c0d1154a00f45e400c2c03160501021031009900c2050391904801203201c0035a40700079940740c01228064078803015480b143d210075110b204003402d41c1d07064080402e00a03554200410906c0380300c294801c0c46000c030b980386545989c40747c0003211000c0b1120024408100241442c1d031140074004502c1d000145450b8544d1641440c214542d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 736347185 1250 736345935 736345949
    0x20708030f0c0f0418020702031203011d060d020909190302060411010203121b30010f0e0f070302120405061008010c090312030b060310090605010507020f0d0201090b04 74
    0x203105000003810740a5038031100c00b40030b0b241048568441a0000e22951082074107200303811402400f04121a03044035042e41d402812a491640c4070030340c04181e50030034483d440200961800c001184507840c0c040d188120002050080c41208990801a0004014205880d140700c2c8400b9058903084400c07680d00c015010f50018503180c2ba0074640f5000c141c0c0c41a0200b41103410038030240c102d00e4000b0300e146401c80c8060071200e4150640914400c99400780c0044ac0e4240c1100c10003032070803100840b402078010259030b40386008503a25a90b0000075506a44103940c9051161400a20040c07a008201c9403c0b2565150141ca000c1620950102c1004241c82c140d4407504801c0502000c00c1c7d200800d1030040c09108024045051404006030000c1c50521014000d001d203520110621480707948490700d600384c01805030740c0f01d041440000180c00040c0c001c1d0384c0080d00c0c06201007410b60080c4250b4180690060980c4520710000081c006c006048032401ca0501212140205186059002610141c060303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 736348435 1250 736347185 736347187
    0xe1f02071d0f0604140a0e190b060a1a04060503040807060c1e02010c020d0809011b0807030b040501050d0f1a0117010b041109092509080d03141602010f020708 70
    0x58070710b001d69502c000d000b0a2040e494400640002c012131418107910000f04140003900c5401c2116490400901c820702030301c81c2c9480041c0c2000c1190340c03100540600e0090304e02d07a05da075484607040c04004402c44030048001905000070004244180d00560344540704002217030410720380755904800c2d909850383c0107010605d0160049030700e0080303140501d03032000d0a10003072003c04884000603483d0101c0504240401500000251414209401030f0020f8444246054018844c02500900a040540b112000281032500032100da182034087c580c182c8030700514200c5a1007056403075080004d400c10f0111f4209420380c00d00aa180c000040e40c13802041c0c078414296002e43035500c06003401c44440841d2a80b00e2032905400d515000742d036006940162105031500c41d2113441c2c0b07845840481c2d01446000d40c0204582d5901e0551650048404048a182108032107402c509044d05400307940703943c2c010041d042003140000303203440c05a41803c2c0341d00d8424000059420300d80c0340250140e0303210709c1c01541c0c074104c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 736349685 1250 736348435 736348441
    0x3030f0d0506040912120b03071509060216060e0d0c0f050103110415030c050423010305010603290109030204050f270604150b210601060e1f02071d 65
    0xc030601401c0e42c4040112800c0004c3d00302940c4000804a032280401e041280030300070b004c652a800e9200040f0403000071704440390143d890900401042100007080c00040310760800042c09800003c014424450b00c42c440d11071a4200301048855040c1c03806003603440f1038031040d404013103040d40c1d039140e010303240d010003140d112400e000000d002d442030001c01c3e580d0b030f503003c00007000030000c1c03130358841200c8a0625010136903100c0a03100b11050b000d80c0e0415440340800e8518441190450301103075401d4002a00e003802580c1ea2075100b07400710b50301d001c9250941c020309481c2c078508c240c240001c44100d0b00e0504180d02a59100d401080454400f00c039030007540041a4240409403102011040c04503680c80c0d004103080e005d802d00a520343ca0301400050461620321000e1030b500394a0340103642c07081c802070700d500400032139074289065540c10600324000382d0188000105015105041d618000440034200e40102036606120841440700940c1036021030040071800b207081031a641d4405441c560910366500141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 736350935 1250 736349685 736349707
    0x1060c0305092205161706060c0304080106090b0625170a090801060b040302011b05101a0a05090606040308031509040f11011803060203090703050610061b0c210203030f 74
    0x1d0700540300c0c0d0480078116900d448619800740d40107103828858006d92025458400c007203483c0b0b0290008540c000c2c000410003084a003c154045011134106c1c800510080e983c15040c409a03101d950015022004d100c41c600941c4400d0442009880d0f120701420680c00d4101c11402c0700c035400c4940fa42c0009074008008000e018070074041d00c0007074038600c43c00c5880d081c038690020308981d03a103030b91203d0074072080384422050090620051001d2884400280046108081c05002e000380c00c01e0b4251040c0c2000d8004511418034580041c807400e00504020b00d03140c03c6490700c607a00e800040c03c805500d003030500d00b44400e031107289205006512660032110210040d1070120b01c205c203250f100c11b042108500190701d180c41c0030382c400400c80340c02400059803034986012103810864950806010f6100c0d1406000c0c4901f21000d20344202c8050755280c00504281c1c0c140401d01d14422040030380780500c00d000a100c160a94446214840041c0002010a014a40c00b10781507820105101c40102c42c0401c400b8850 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 736352185 1250 736350935 736350941
    0x6020a05060907080c0108130605011d0f0f13020f0a0b040e0109020319020a0c021009150903020906010513031505070305090105060d060c05040f030602131d01060c03050922 76
    0x401c107004050402c1c075084c0840b6541d1650460f1201c1d04000016001c1800400c4108003050101d0b0040b03410b1101c3e60311031032440e20302c450b11880724084205c14800a020801c4000d401d03402002814801551a01e40c81003079a0001e441d1503084e80c1c02061030142c118142c1c1d455450070000c01e010020790352907901d8003450520001d8164011103800d401007007005280d40180440c0d4070884281080140c82e000e404000320354200006100a400400801146440c0c0c0d0f00034400100f241c003032030841403001e40420303800c4550060030310000350030244404c08140c403580203401500304112411051b40b210340c1d4944510045494100078620810755400034400c50a40c1405100e40c0552000028442414018045400b00341c0000d80036200581d16444c03028141d2258045800904003000003c243c25181c1c20302c40001c4d44071244891a0040d1400000742003504440303c249080a120215805030b031a250301621000da40354022410850200400c494903a1400c000240300107200052004090348084001c0403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 736353435 1250 736352185 736352191
    0x9010c060f022704050f0702070b0304030909020d0b040b03070303050403290c070201020c0108070e012d1809050112060207111507020301050c0c070603150305012d050412111606020a0506 82
    0x1002c1b02c0700c401c0120b59500090600b007103401c002031042e40e07135a031800c0444500c40c1d20f40005000c9400044d18407481c2035a5003198a10b2a811a0100680711114040568900040c0300c010086107040c40200301040340d503115408480c90500c016490303800e21268400441c0b008840c0c84140000100da80000d65904100c61100c0c02c000307080c111043c0c1002c18010b00b1480d072181043d41041600650001250f1051640b100045188101601e92141c081c601a1051782404028805204403030000146030300c4038040d050403500b4020b0540e20710085516004e0295025600c1542c41c0c807800c82106841d501d44c0e41d00780c0c2010300f00b04007481d2101c50307500c1090700391000a8955103082100f40310650b800e10001ca0400c00300e405c07a0800007841041100b903140140f02d43c1d070001d4001d500e02200519206410405155403c81404280c508204004080c20881d60107440c0038007141c1b00b806005005030b000e40564205421080122510218000c40d00c0c00044200e03049600144c210009030000c0000812510303030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 736354685 1250 736353435 736353451
    0xa0602100b0307030305091e1c14060c03061201060e1017010c02031b070b160506180304060e04090f0c170f0c040510030507031a06010509010c060f02270405 69
    0x10f0070502c0c1d41c5008015020740c0c41014460310301a10880120b41040e00d03e407012080252043c006000c1ca9071030383c2c03c4139050340740c19505100d46141100d01c040001c100e652103000c4000000b82140c403a1300a028680c00c03081c1c035040440d035907000007240810000c00854030a10900c01d134624840d0400403104c0c4072014148488040c0d0303042c0000303459850b4010042e00d00321101036400c045440b582c100d20703030b140400507405183d02d000c00140440c080340080700c0103034049008904490080d114404081c1195100c49072803540c03900140b2003442018810740e0041e40e201d10041005c110660b032078440c400740011407081101c0012a00c0010410102045001180306688030081d14050320340744540390f1551607070310b80c003841269203400041288200c459490040c6806c2400c4032480c0c2d03260318081c800f08007030300700890340284e000340003440c6984284215000307131f201a56449080a01a035030a00502480d00080004603001d11582c050b201c00d5508100030700c9141400c10064070584010700044807001743c040e003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 736355935 1250 736354685 736354693
    0x170307060f41060303130b18010906050a050a0504080f0705010206100e0402131e020304110d0203100c03060b0d0605090a060b0a0509040b090a0e0f01051b030606090a0602100b03 78
    0x2020940a629058084522606510b425900c1000090840c807401c042c0d014080c0d1940c00120340601c00d0b00181c016124200e04000c0409190001540c40d85036602c680c00000e08200402081e4a2117134002d000c141d102410803a007015207550840741420640d0302c1d81c0500f988050800c00ca00e603410000d05402c10755001400d400a2300f03018040c441d030303400244007a000b081c3c0400304000500d0f00d5400f0313001040074a299a0903600784980c480c4040d40c0241c0f010744005000540c000400e107481801ca8140541c007e0080c0b90b50304e040211038019200444012060503504c103400601100c6a800905840c7c1100d40c0000303400c0c0c1410204a0384920162031050700b42e291034000c3c09640e100408580c0b1701c14003810019100e00078900081d0151681c2d01307440350056080d0060008148403500110140f10703012096450060206448a08842d4100e41402c4088451a1185e24181900004542081c1c1c086c0c20309103001501e001003210202240d01001c01a401918403245224040c402c0d8000d10000b00c0142c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 736357185 1250 736355935 736356011
    0xd02060a0c050d0b0a0503071701061409070f030b03100f1410030201140f070c0303030c1d10020c0307030803060a0f0302010c080919030303020913020c07170307060f 73
    0xc01d40d00920000300600b90391051103c1d040c5d91041003100082000508461180ba26120241000143c440030300c5825828090f001c514030f0401286021020b00107440b00500d81d8602c03c084629043c0241d8071028165510301e0700c01117032020b0000184404c0142c0e00418038400091505003210800f030500ca18102400e41807007030007000b1000300802c490302481c0c489120f07600e50070400300600c1920040901c001001401e80b04110b0078000e200c048071300070740f001c01c0711192402055888010b100120030044081e03090031881494000c4083c25820304901c1195507281c40400401c3c58804184c0040e1185000032081144030716090500001508600c025200b601c1d146500180c040c0042c020000c0c01c8113408900100302d41c41e65041442c00300702c00d80c84440c0c12581c81c18080c000303604c04c1032524041d2910201c07002014480380200c5221a6001d0010500780b49450302a0782c4280c80510440500e000c1040540c0c042841c038054452004c00d580b50004500d000380e1241c00790750b0032803601c40300410080107038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 736358435 1250 736357185 736357187
    0xe040507120c0f061d04200a2007030203070f06050307080c210109060605120a0f020910020d0e040618151d0a0b2b050c040c020d02060a0c 61
    0x14841181c1d124a09007508514a281550000740320f5005882c028030054000201c19030700036090260140000c4610030080207850034001542d00031441e040c0404a00c1d240240c20998040040c07084060600e842c2d1580c01c88032400c4030fa0008090700c004156800f55406009603d0217004200c01000f15442c001841450303c078015000d400f00074031103002d01001c8400118040700c064111044550901d80c1c0f5205507407812405501c80d0402e00810041303c2c542480800c1d150f0184049960710203201a800201b0380c0c0c0c5100d1070003d000d50032808820142c00307009140650f2a0560510707007987d100c0d0040e080342d80300b8120040c00300b10000002c40c401c504241080181c6405007150810150401e08042400c510b400035070b4940c15402d0344402001c0142103416811540d0201d10341740a0300c1900c006006a50350202003140e119900d00c1e0341c91340b407e40054030080b0383c282646c1000340188248141c9040390101c2c0d000404441d00300d507414015130000030203c04d40b10b5061045c2d5030f210043c1d01c0c0401c404c02003060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 736359685 1250 736358435 736358443
    0x3010e010e09060406050907030c0303021f02030912030603030f0c0f0c1005090405130b010603062417070c0215071e0c060e060705030a031b030603030813020f030601031b0e0405 78
    0x40949a41e1b520000302d90300705424801c00300130b99080302d101e0121964030b150095403000e04501c50085800b02e83c10901d0806001c2c0206c0340a102e05c040100b203000d0614050071016400a00100e41c1444100314841d020300304500034124006504000d0f010140b01400c00500b810401014030384a085040e01171b656113074001c021f59207410025079000070070765116101102d86200d40400034001408100c000183e40d85d26801000c00d9882e52109841201c15000c400151141814501000f0483c0246042801d201e8140320590280fa03d00d0000700020303194004c1040d188142c40c4074110550300207400c000740010702002c80300605000c44601601ca00d00d448059072040745001c4c0304200642d800300e0400d95900c42044d070b0507250304001030300d81c0c881003401c0c05001070000c4100c104c40040c41c2031014025038001d1107200202c90701754649411070342e0b408260407074240750510304903800706205402080ca510100f01190181d4811914245005000c510981114841d58885241210340c00c0401c000a04003007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 736360935 1250 736359685 736359691
    0xa02060f0306060903010f1b0203090a1a0417150c0909010501030221011e0602281a0405010506010801050d020a03230d020709050a05010608151c030503010e010e0906 73
    0x850403549a46580000035181c1c418400016030540c00d1007000d20705100c00d41c1c03121905540051901c0ba002d4400d81c0181d0b04c0780200502942d0054100b4010000307281ca42000d01c88485102c03190a01e425296501610505004002039106601000b80e19181e580710700c40442c0c00034442c1c50755505000084001a100c140140a4141007540101e441d15664200d41c1c0740007128100f44901e500300d581c5440003e150030f5800c4a55040d502803c220006503903002107401c030381e262005490720421845203481907403010f4a08004a41c00c104011002c0d04800840407407a0144e881280081110b0800c5030005021400681100d40310390010f92140303006070340710514081180e610041561451080381e08019240c9221036901d07540f4064400d42c409213030707408114001503400c0400d080110782c0310f849940e41183c5003401480040340300d08001c00c81050000444000c800c8000700f000313030880d15002404a00209c0503204070041480400180000c0140380c4d0704902400300240903c41502e4000d224643d500070203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 736362185 1250 736360935 736360957
    0x11070b0c0706111c09170a0203060703050f010306111603020c0102010b0a0513050a0902100906022b0c140102161a060d140c060423030105040809040c110a03090f080a0206 75
    0x500341200c225801041ca0038010090005c8000c0403490060921f503c8a2400070b0807032180c054000000d00e00d17406486558020140307080d41c1c090030380c2943c0e2010002c0c4107150682c900b00905010f48038880c0030728902204540d00c6640a000b0000219001a0954410150862280c101541c4c180071b00d443c0d0401c0c608600e200218017003215221404404010710540c1406900502580514131a59400038000c01c1101c505a0850341c0740601c80c18130080c00303403c0251004140728549041103a091042c2e400c1c4041c240248120103100001030042c40c01c90b171107000070740900341c003095111081c4103112800340c0415091240005940c68081e00103074592076000380050902c0741221f5058020b02c400c014a0329400c0000c5c0000b6502d40d110810141c64519000401505140380ea50018860030180901c034000d5030b100f4516406c080c401d0081002604440341da0f6020400d4065a04008040401101d080e03140207445030802e8070b0410550f00b44549190300305002c20341c4aa00440010380701e50003121290051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 736363435 1250 736362185 736362223
    0x31b0d0c02061e2a04080303010816030809060307021f05090f0114070c0c0e070201050103020f030d020a2a150206180607030f060b030a2405030307021011070b0c070611 74
    0xf5040c00100c004e00310120444059102142c0800d075044004000c6060325480e000b1920200e4410444040d20015400010402c60707040c000c1121038203003100550b40001486c01541e01d1200704800c000755410243d050b0381d68880d100d070280b00c90050306018205280c10a00001d01c4504d4034510380d0781c3c01d00c030003901c000308000309100c0901c14800540400c20140ca0850340c1010f8905004100078080d184c203000c207034400d00d95420213140317510b00010701c4117405605030041c00c00c00905880e078032100054852003c810340c01c5c080944203840d013100041c03400340003100c00400d800d83c1000d80c028602003000f0450101221300c5120f108460714001841e65111003103140c0071640b1150300004001519166004807a46000441400030702d02c1b05401484c1c600d500c03111061508640d83c0c03150510310b074241c4945070301a0000c1101001508062a40c4501d031101400c0c64020320700b880c1c004d81e04c0c0c0206640484000c010104600b40b440320b003441120024202442d1a0740e0761141c000200d601c610000c0e03c6070841c500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 736364685 1250 736363435 736363471
    0xd081c0c031b0203090d03051c020a0f03090b070e0402040503010603050a0615050108040b0a110313020f0609010e0402030a06121401051f060825021e0a0f08031b0d0c02061e 76
    0x423280e021124902d00d03500c14010080c00740720b41b02000c0e4015180071008200c00030b20708650244240f0513401c1da035800404440d41c58442d6582510040401001640c01c40c0e000c200108854800740207a9004602c564028890b00c4002c0c00c0440c102e03030010f27401e1010031000b010200038907a400088240c001c2d41100c803040c829116a480c3c0c40051070b0302079908890040c003104000b108a01c0c0e02ca02c411550007a41c842002501ca0401c0245900c80c50041701e000c90149580c65503d42001e80c091a44601c015200150315a00c0f0a020f03544610440021100d04545907190080d114003030146641100c6408560b01001c118200595004074440c00707002e003000041c00000710078501f20140c40b45c81014040d00001c5503022141d00940f41c296681c1c2c401d850100d0b501490414140001d100ca60045c0c00010000c0081000d03552151070b0307400030700410350407400c000d00600f56402240c01400150580c0030005010b0f240d4620103800e0403001044201100c40515180945826140a843d0b101e55007040042d0005c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 736365935 1250 736364685 736364687
    0x9060f0a170a0b01032a08031b011503060227090604180606060503160503091c050d06120218090a11041410030b09060903090d081c0c031b0203090d03 66
    0x184030308009054510354100002c24045445403200c1400f050343d86e500f0a2a2041d0b0303024060174068450b250b402c5d8410404a00709410f400d084511021404002081c0510301e145501c81c40b50543e081074510660010340d039080c007203031060b803440b10144060b0250980c05152000580049000309010301480d201d20030a0845a6900c041c01c1540364020b00400001c0d4480800800f1900201c4000344041c2c1c074142003440260042c004d60303100302e5401000f845441c001155001540c05587d50542c240032042c0280c0850344c6003801401c0c003034082403100c0d40c807201e914010048152540b01032100803036900f80c2030020f0b03114082003440c12690000d40e10701c0b04040d03c402140c0109028141e0710804201e000901449040c07418240302201d0198070032034079940713070082800d807102c20640c3c0281959004100d581c1e1107060003030300035072041e000d141d1a50030030b48241018210018041006150260354881c2c41001c9601885070581080d00c054882d25040c2c103207440a5130381c0c428441110300c02c40006691201701 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 736367185 1250 736365935 736365943
    0xd03020a0309082a071208070f0804090912030905032710020a200307061101020f0d0c1806051b1903050a27140f04020a02030909060f0a17 61
    0x402d07488000d807130303a6000f20050707991032250400d400c040e2100140110320040d503000508100390748880402c00d81e152100d65071941c540d031203034004544000310784a041d07000c541c0c51005030000b01106400464400708501c0c0032b6a101340f080f0b603548141450540c5090201e40c1c0003050b290650005852100f080b01c20101601d40c12190b00107541d44500030200c49040194041100317000c05100d84d0f18440303070956402c146202c004c2c501130080d03095403008200b003064911030508100c44209080006207440b0850040443c00d0748001020300d404c80e100c028a01059611091b440700c4202804000045d90341002d2000341148a29141c04000da1280c40d01c4400307148003800503e040000c00c1c26120200e80702442d01520356008015280c0100314451100c0c3c0590030349034099401100341c407056101050806054005e02022004015044404002000c1f027a842d588000d144d81140d5070019038541c03c81c00200b00e900341000780800d0068590030041c0c500750715400e080070f0945100b0f0289d0100e1900c141c0080d460 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 736368435 1250 736367185 736367201
    0x103090203070918060b042f04030b0c0417060912180604170f030f0a031a030f0106090b030a050a0b130f1b05090618090f06010b0d0e0f0d03020a03 65
    0x101900d071104c48010071040d0850050242d1050f042071045014120800c0200d0390a0000c480e43e0310b1041b60481d1461a5000030075070107401c0007131264142a2252918006908200c0d55508100000241400011080e010300b801e404d00190007852036190070b0181c02d4032130402d01c05c110414540031524140c4c1c0e014825000b0503000004d806036407540e90312092100c10704141c0d00e00b00c83d14042d52050f0301039064080122100c0c0380403000031130301d0880001c5040740281102e0030300c0b50411013a01e0001019503814001d21982945000001c10031500f40706a0008603500c80e40d03000d10a0784020308007400101d002c02c0c81d00c2500d8000070200455a5010500420042e5071080108062040e00b05a01005038486003080410302c00390703007003004644501c1803000100050b550340e81d110031030385ca020180100d20500f407540b1403611010758140320380800045207007030030a0f0415011a03401040c4082400b4444c41914144110000201191110356100e2500c0304103035982d00c002c1540004d071040486020f50040c40d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 736369685 1250 736368435 736368449
    0x21b03070305101b09080c09061f0f12091e1403030108030705060f071d010302221a03250c08040b120f0c0a081305070e0711070f05010309020307 64
    0x1803c05000700c400e1005282c0b4000001403000c0d83c81c030680007035102e0030603c0d007611220002402140701c008104505a84010810703948070342459000c0d00c140c80251401d8140301c40d00e8541d041c1d81000207801410300c400000c1c40c1c06d01189403503040c0c0c0100b9001c03042c80060f5851b842c00401480300c9403d000400c030040c10010261413000100000e01d01a00200400e22036000300255100c60321440302259030110300b510a45c00003000704000400005c14003958055021050400501d0400c0120807048402114420103060004015082000e10302e003948035540c640311300a0051652500859220045416011801942070b0503d10020910b0103440d1840916030010421500c41d40e4540301e0355181d501494030a0240020100860184014075420764024080c403031304603040131450071049078044d0000f03144d40526425107060501081040c0046000380c41001030301c2e0f0706840c0ca800c000d0000c5034240c0c2e1014907540030b40000c0201c0301000c0c4c00300e0251a401d00c0c0100d480035003400064074018032500404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 736370935 1250 736369685 736369693
    0x30d1d040e0a0c0807080606130b011205070c14030f03070f0908030d0c0e030a0302281b051f0c0308060f040c080a0b12100c0504030611070308090607021b03070305 72
    0x9814414004990310032915124100d0386280d441b030500980700d5200b55086d9400001e4000d14104c040025084103000390810f2501c0cd0042c8458201e080c00d96000343c2d00840494a803404144c10300141b406903500112950000310710b414000c0c1202540c0d4800108003008203c1481c80c00c690b03042c41a05003c004242c0c081c00c03a6180d024140c00320006100c10700301c9a02084000355164128203011030810f101d15010707000791400a01035519141951407a03504542c12440000210380024040c0014181101808000110a60a000a001c031b45440d203040c5004800d001c1e20507400055104030000310f8564545412003aa0f11a90045154910842c9103164000c1c180b981c0818000d90041101d0b11a0403074180911071613102c1c00c00d102c0200140c1e40d0032070050700007841010034000950000e20040000c6d1500610b85a92a100c010440f10034034841a501540010200c043c5544503080035081040100034100078106640040c0d80c0d0000c1092511450005010584103a502480f00b8002981c008050f1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 736372185 1250 736370935 736370953
    0x403020d0809150c0c1008041205130e0112140601122301020c0114070e130513120e090708090d08150a080604050d020d02032d04031b05030d1d040e 65
    0x90360305c9803d0074881d280103141c59100100389501c281c0c0090301540c1c00200c6c00744600b00264007220b140d40507100703020a04080303180004401210005250003080d2098254090107039901d4681c1c015007030f00940346280d611103001400341034103070a88000c680f81e21511158017820f006021030604180f44881e80c58a503c0403a040140c00b40c117401c20b111081d812040d144840d03585840035144002c5090041390810700c0c59001c03a02444a41e40880d4100030074901c0c40420711882d55481410303580074031007040014010108100c3c0b90074120b4210f5040341090409041c01c1c944841d00319900c1120b9400340302001019404150040041d5142944a110140603d00000e4070f0304070066440d002a40d04a50341e1040070030b0076031014030210301c0d9a00100544d000e9850800c14000c203061b403000300b011200403015076600c8054003d9514000f040118440d800d4400400c05105021120ba00d8980c030650098200c0c1404c40305a44d88194540040300d00108014040000700000c68010a04a92403c50b80e200e51440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 736373435 1250 736372185 736372207
    0xb0d050115120f150311100306180e2113150f052a24100e040c23040507020f060105040f06030807050106081605311a04110403020d080915 61
    0x4044c2004001d4507141a0b000c0b87e034604408840d8244100760303c1001064015020b03e445422010b07658a9040480b03484181800c807070010180303452008044454006a440070521000398110004c2490211220046a01d0341c0301800d03048a00c6075204c02c116000030400900b03544c0d1603e0780503030f80202124440340c100ba00c4c4610b0b0b40b1940200c011420403211024891040942c40216106069105141890618060f90160090b20180045034110800312000c40c414071101001c1c2440060030041c0c00703800903d0010301c011124090a8036085411000924407050400500a811103109680000c5ca00850f484680300600454000410700c09002030040c080c0141500801c007568104420340e01c0f034004003030591584840d40e20580c0c0e0405590b0115500351008000740c0444240a02030111001c24000d0320002141c001d12141014a0aa02041405401d040c42082c100011030072481e444c00303003150002a191142510010580b000c0000c5c1c05040351501c0040440215410307040c2c3c0c0e15249a544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 736374685 1250 736373435 736373453
    0xf050d0f1b1704020d110303120420010c0c03080309031c050429040201080402010c020d050a051207031403040206041a0d0510050121150b0d050115120f1503 69
    0x50716200007070442e050140ca60700c04481541c083c5a00500c06052800543d0350030049924543d49142c1c1400180b02d08012204620429440760380300c1c0110308801010407000c021501166100e044c100061088000d0003d2007000c814004d6a030054602500e0395110403046207584503104110300034031a8400003002080003500464044c40c81524001c102c0103130460391a41d00fa003540c02404518050781c01003000355005245860304140189440100c03107100d90042400844c028404640c0d0b41c1c0700b4150102030203010b02074400300030451000c03545401840c0d02d004054400086561044400010100d8110355070b00702214010285004c400d031030115400074841c521742180030b0180385c0e6401c101c000340e0501420b02c0200c0540e9016100c210f07a500d04c0c8038003084001c1c00c0107800180f81d9501c400f200d442c01e8071140d4010044c400782110595840c00030b07241c0c10a440b41a03100300ca220903411880304600f90400ca840c000c903a040080002e031201205800b502400350811003c02c00c8404e04000b1040c054004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 736375935 1250 736374685 736374731
    0x90201080a0e1905160909020d060504230a03090501110c040e070e1e0114102001050c0c1b0d0311070e0720060c0f07060605060d15150f050d0f 63
    0x4264040091346c0700e401c02c003540da14200080d80088010581d100003900342e0300540e046030080d007200b942c0c080d8800348000c603140400b8104d0355980c0701c1d0040008055200710f00d0301c040c2101b0b01c1c00c00c02c00040004010390740c4500118541c4951f80301da51026268a041250200800b100c020980b91030424091484850400d400603102141030b440020540798854041c1c14198800508003440503e1000d00c00c86135414415000045801400c1c0540045042406201d014202d80c0340710a545085002c0c100d03181c8441c1c0f0304106c0b040e04401b00c18650f40e9441200c1c9564017a05800e000040201c0b149100f0300788085500080c00c3e080494043c42041c0d42c0c04101d804c4c101c2079040061141d202d080516580c1c0e0501101d580110000410899a00100070400f81001611546000c01e6042d1104001038080d000007400030b5104c0d9039401844589074402450600521401d10100440554010f009200a0041074620107011000070001c20081059211451429440004000844006603a100c51042d0a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 736377185 1250 736375935 736375963
    0x20f12040b04170a0503181014060a05040515010507080706020408071a0304210216031115040806010b07151407180e040615050303030c1309090201080a0e1905 70
    0x2103082050f00b84400750442d0003150b0385440d0181140d0300c0301c1302d0100c242d020400b002000e0050303102085203032842d80030714040b0b10810044001035103402e001303014100703c265204a104a040c1011721480b10100c0081c604000000e18240380d840186007010a031500c103106000b05154400178000a1001020480d9000c0e142c2c40c80d0441a49824144402d00c03d0006a034080d0070072036290440065100118030040031100030340191000d0403804034a1100d4107400e130f802501c0d068200c8140d800e00d07160a52042041d41c6c15180140e043c5800c0c104081e5032071405003e40880410001652003d01c5800c0d10390204201003010240280a00e46010804180341914040d011604440304010070410b482200030036a032000c81110301c4c507950b5844a801030400d4103240b04002e07076003030404501910184011071040300552201c56444a0604e022090121507900c038510305494002c1c0c40005071b030f11106080e0801e24441000c204103540040b0307d420405203202e21640089042d01c44000c1020203e4110412214 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 736378435 1250 736377185 736377203
    0x70b0a09061d0606040b03070f090b030f012310120f0b06010906170a02070b070503010303021501060509060711100f02010e01090320030405040f020d050a0b13020f12040b04 76
    0x18800c00e028104954002c1e120040c1c000f000003400d6070400d94004d06800c0801403c48001560b40c0c04c00141d18801508a20b40c00d0744c5508500c170346810200301500e10b01088400030000c940300c3c04004007010052584c1d21783d140360300c500440c0c5118075940068024000744600414203125501c1c00301e810f0034100004441d48050180000c0d00c40d07002c0c4d03001400b12107075500d8500d41261140c800070000d0400070800903440383e0a003e00c60105200691003442000715450300c5540c0d506505001c1d1500206280b001510714003a00184140b5611100f41d6404480a94080d61520150b29044000c444010b4010f074000100e082c051201503402484105070800c039030001c002041c2d402111781c2c20384c4c032201000b60100d200704c070a68425603c04e10b010f18000791a50309590409899100007019180d07204000b10b145a0003045a9905580d984030301904554282000c00c0605501c0700800c6c00c20556100301c80f4515400300e01611420031710411504610800b601e14810391400b031400d03904200081d64203a8038a00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 736379685 1250 736378435 736378451
    0xa021203060d1e1a011e030209070309050a120f0909020408030f0d0209120102130821090d12080403030f2d0f020f030109051b07081e07300504090506030102070b0a0906 74
    0xb0b410806d000f540d80290000d001552000300c2640a400c103031400300c5003485100a0760002c21200015080030000350b0b5185110344003484001071400c48650031181e411841088201704404000084a0034488080d80d000d8480522543c610000e00440080d84d400c104400400c107403085041d8011306442c440364200144017902d400c505551551410500d0080d0108401c03d52074024000000d0810f9000003070a00407940019542c00c00942140d101600208040c4800e0008041d014014881c0006d04a007017003200c1910a101300000e204902075182000c5412000003c0c10b004582040241001c100300c20b42d60380403035500c404000e86c42403003062590f41c544000b241410351000b182c00200c048103402181486041d40b41c0c1840f0703a02586d50082c00c8030601201c103058103404006800fa150103919410038030301201c00240b2911020b10450190700b03541a04003140c1503007140681341901e2030a50b0000e020365641003c01e0080c0b149850262004211000700101c9100d60b8010f0110b00784201c13801c0c8440c1e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 736380935 1250 736379685 736379729
    0x271902070f0609020d0c031101021b0108040201080c040b041211030f030f0f120a020310050a1512020d050c04170114040f02030106030212030a021203060d1e1a01 71
    0x201910000070a18800001d100010070120340085820394002005841c0341179080e46e43c08600d4045900c2266440c0c4416000b400560f0140041a540a015001240350440041c00280089e40062000b81030100e8500840c4a01c2c03200c2058401918940341402c0d510340d240c0301c404400b0b0180e403c041715000082550304286040104404540000c490019801e00d0440d04c1c40c80301503000184a05031002d000d1000051040c80040c3c51743c020505c8880060b03407410813004c2c449001c03c2540110b8000da62020080007100c209402550f44440c182c41e0207030741c2c0524a1601c8001e441800c04891b801d6060505000c10822460010411960088401030380c2d211200180c0e03080e501001c10100800100394002408513a24501d880480c0340700400005800740c4079400030719a03103684600c50007aa403021550071201c81e010011503148030b60403640d40b8118609900010404025100014540c405070009075000c2c03d400d00c0403c0203203034000143c0301c2d402079030f481c1e00c8850030091160013040e43c0030043d000303d15 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 736382185 1250 736380935 736380937
    0x115140a2402010b03061006170f070302070206130617100f05120f07060503011a0711010e1215040308130c0605030c0409020c010506040e030a02030a030902271902 72
    0x58a40c1040110250105007040035040d01c0c20050000390354075100c880b400303950240820b40c072882c3c0e6061409251403c2400040240c011a590041c900c8240020710030783e648480a41c03680086c0500d000341c0e48090500c007113203c0c0d00903560801217040364a8004a40d8a8015070715100000d00584184007035a00d941800c21104042c0c418003020450700c40741070120f81060491424410f001008031504240c0b12005245000600e9100c680000c00110042c480900038000c00c2002102d91000c0905104141d21444078048001003131505001d4003900700242c41d00c50b01d490408a031001c80641c1ca19180f082da041140c04000c480407000074004400049944624104461460b03070051403150107a03050010984095001400b0b55800c603e040c040054100d42c0b900040c51558901ea00104650400d041480242e41c41040076800903041401200c17030700b035400010f98160140b9803501140a5000c0d00100300ba82c16201100c2c401840c46080030781000501502c1c250080d1030903100c504003964030340c801c0700403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 736383435 1250 736382185 736382189
    0x112020405071d06030402010c120c02040b01090605090d0606030b0c03090c09010311190503011806060504110f0a0e090702010e0c030f0703060b0301113c0405130b030115140a 77
    0x1100c41e64014840582c1005806176600070310605228000c5002901c80c44075058207100100001581ca1548804505282c0602e0000711402c0c245602d21f5420300d075004d0010f004022646000c2c020f0341d40130340c1c20712484d50800c0006540040004000c2d052440f0161543d500c1101c2840c11841a404003070014200039038658100c81e0019a2414480054001c00030310303050751081001c0c0f41185540c08034199801b0322800400c030703c920311801d064140c1c616010050b070380a5031010b44140c2c0307030071444031032902c101c41111203180305c3c40c610550301c540005e415500700425183c01c0d5001102142000344007901540b1150505189000b15042d034020310080682d00c240704140f940c1c03a50006141000024030540051892a400500115542c644214140a59000b404016110041a40d04100d589030990304484450700d9440b102210410044840c680314844c91081c0d030f0288a4010103061000c003550700c050072451001f402440351201c1d0780010064259a0300960302c01c45082b0442160031700d0301c0707000340007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 736384685 1250 736383435 736383467
    0x190915240503060405040f05011b02060a4805030f1003030f030e1903050a08090f0c3003040504110c19150921020a0201171e011202040507 61
    0x440c50f914041400044c20b03000d8411160040311841c1c0070001507080c022420f201800d40f044403125014544000e150941c0600325420031803030010001e40418007101038500c4401d08500720210207158141071846181c1c682040340f102044588550ba804d64000002c40c05180c560040c0552030b1624400d80f0722aa041f480000c0100341030404821a40c0d0003504500100703c00c243c151f488101105994503403401c81c40e101140000d100040003d0b04c15041445d40750800401070081203400480705e05507650710b03d00509140b18490940710304400e880c1d51405041c1e220ba030604901800103135014015030701d42080c080c06100d10304092060404260000c15518030150020040400100ea60f01a981080d40807400f640c00d034605001c04184000340c1d000e010381c440c3c860030030b40004e01d02d942a01c0340050418402141107400c40c81e1180d015070b034401c02c2040210041e600348070840c1c07500a48040914402c40249a420005c44000903036840400d0321440010300070780b07043c4101d40e1031100440709e0004540d4200c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 736385935 1250 736384685 736384687
    0x1401021c0801332f2407020a230d0e040f0b01080426121e07051206060904060603060306180507141c0b15090c091909152405 55
    0x11144540001940000c03026802e800790711900382d01382c40c0036040c000d41c2c806640c00b40801c405c500c1c02c0c08860350351502160304111658102104002d407908800c1c0c03009000200040d401c005003801a10320070450800940454002c07031100e4001420340301a804105110b1440d0524a0f090000035005440e028030050392040c03600c1c0c1d19552504080c0a03001030b1640fa11260410400311011164001d200884560014403d54582003480f404094030481e079a01311031049005100045402600740c3d10055a0100300001c6d40c0d82d1000816524099242c216610906101000601541541c407000643c1d025510602c40c5510899020980c01c21424009006a000d018104038992070301003a4004000024004c8184040781c0340601b4403266141c60641d00109600184001c030f880c04503102182c20300a50f42180d007480c02c4801c1c406140221880d00e400342600c0450403000070852820340001d491071080411aa1004c0c030340703c400031400c40c001d442201034000c04a5420445000717410f81e8810503540d0f0301b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 736387185 1250 736385935 736386029
    0x60406090c0f0c050709110316020d1403280f0b15040e0a02040522051b090d0203070515130617010302060a030e07092c071401021c0801 60
    0x2110700303c894603c10faa80d8012100082002c07401800b5500c094428051074984a080400704038408070140242c14042d94040ea900514140c0c110b903100640300203091100b07449680d2080c0c15104900e4484088a05000b0400e803404803110b180d020850101054508211225450f000d000e0007110040c040307090302d1000e01c0100035070035100702006d1723200700402d0300542880c1e600d00100b942c00d0000100c4070a01e498941c0a85101c2d20b481c030480d50304c2070758801e810440c00e1414014240c0c0307110390242140100f0b203803214036066440c104813810003844060045900c1d11900403841e102900b085605903900c100c0c280700029070390320912642d81540c4403000036901603407a660030401c00d0351002142c84189902e561944190803010b1018070001d06a0b0800410f90a584003d1140748100800c1001a58001b0381101d0103030242c0003034507001b50359500d43d09141500f1401c0c0141d280240269080305030302107130141d641c8001d52020503e0f04039a00350403031502401c541502104221100d01095048529040203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 736388435 1250 736387185 736387187
    0xc03080d230a0903110703060c08060315040209060a12050307050f030705100f09080a11070b04030c03151104080106062d0c0c081209090a1503030503060a050414060406090c0f 77
    0x800b00e019403090810100170186803603c0d0342440b12603401a00c00c2540d030380c0c4560740c40b070708680c24070390140f402c0b000b138001951201a090350000e0041c2c4042c2c000c525400005100307489244088000d0017460511400000080c90001c5d0f60364044201207610f4046c8550f49030b902d1000100f9240c01640c4200903110301d44000300c401009100c0c8500c64035403281c0f078022802c04601400d0061000c1e010300e0b62007503c00d407490303180d040c03a180580d0300c05042d10b04108002c10110301d6550240c0f0540e54001c40c082e0654641d113203607801412424400c05440040010002083c9805520541c11240240c03140207800892144811300f65403100c0308440c91206040003c1e03240c9114a401d0801036101c1c0d003240c0e03001c503241d403542450314001a14601004100048640c0ea9140c41c404072a40030344000030034808100145910780101c481840000c0610401201040c42c1d0768505622602901c0d020304200074100d030581c4640303a8070109443c09806075141210100b00301d0414000d00e04088101d86507501c1d20410008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 736389685 1250 736388435 736388441
    0x510020c15040611070605070306051906050309161e0602010203070f0c020a0806090c031b10140903030d020703031a010e010509040204090c0206090f06070207090e0a0c03080d230a 79
    0xb04a600702c0e682c0d1800044542a600604070080c011100002e1901e81203402408542c0303940c101a21030702a0300400e42140300f10046807815200f040c03800c66140d40320710308054030f480701910440c160350741e40c0f0702d001c40c1e0040790180110b110f00f920b140610060f559864160700300e110a695400c0010440207048500070300902d450320900b88003414001d509a5160502418107009882c00034180d04403502e00c094518041080c90040200240d6140040352500001846000349000f01e5060141e21031500a1300410302c3c0990700d20b07a40180587c0c0da1041d05101110080d0f01154044000ca07183c0070300074040e0300084e03404130306001e0706860b41c02e18008214010340321900201503080e8020b40070440031966018034000c69116138445c0d0000e00b0395080c40081c55061140c10039030b007503295101c10104602c85a00048110440d240048009801d05405c1c080e5401c020030b45001404501c0e083c4000010007080e000108001201a03c041000c240d0180c5a1aa81c007410030010403c4003851010904032501c1e54 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 736390935 1250 736389685 736389691
    0x140702101b0b06120606060a1b0f0308041203090c05131104090510060212090402130302060a0c150b0916091e09060b03011503110408010213030510020c15 68
    0x204204551500d004100720300c4007109241218084510030a010031400c0011041c0c0d503a03120302e0b000d041d451502c100483c0399030081d04007903802c201003442c3d1f000d403001d860f042c998001034104c0c15440100e041414064011401640c040310321101c088012820244207110790a107296100c800c2c0e445aa240c40108030b16806080080d02c04182e8450400701c904a41c040204028001c0d11404039441c50001410500680c0c5584003c1c1590403490404020134003000c220346001000311801038842012091040f20140a5007000790030070000102c1c0b00328690002403203030000d1b2244000c2d0180744030001300d440a07902c41d00d80d03ca4112240b0004100801ea421060b03035084a95032406242d00c0f039503001a4a59032420621803102ca8003144824824a2054010100a01100d400c110714552400c44c1c4403105a8042c08420101542c030907244004004850441d001400d90000030754a0300c10000100020590505c4102c403680306506902411440f02d000740d900740700303141001d030800380006014222082001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 736392185 1250 736390935 736390937
    0x516030e10020d18030f030e0f0a0306151505070b041e0305121008030d050c12190b030a0f031101060b1c06080a11062b0905100501080607052a0c1014070210 69
    0xd055404800c2d10ac2d4040d03500118094080400d404aa003609201d241c440754000c41c442550000d80c44052a07041001c03a489545d004142900541e02c5003808000003c250840c0003c1940c0740701b48200b41503216020f080040f042805507039898858100d8402907010a108801c91034105001c030703044a6019500881e0310102801e0600d24141c02074681603c0c103001280e4108590744c070840c00100700e13806441000a00401a030040020300b9444d100c001c02d08000401c0101041101c1c454400c65920a421550003495550101c6440705944441d5140c406504c000b8042e00c540f90070760001c1c802074001a032501454000040f030140c84800000e124007944109d80300c8613040c1004d40c0d00300d1ba03a114201d880c00780041c84200080e1340030941c5407040c00e0240b036000d000e0f003281c204030043c8058100440c20a42041e010300701503680703200d909911583d0030000d10b41c40e0811034440741d0100c25060040740310f0400200450722000380f0090420141c811180380c03418000f1450003404035100500f01001c80791070198407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 736393435 1250 736392185 736392199
    0x1120b0a050406060305010305070f050d11120a121106010e0109150f0803131508010b0d0b1806090f0c04051903080d0b0307050301020a0516030e10020d18030f030e 72
    0x70345000c80c003610004da10500010303036104010000c0c03003030a00011000d4400e01c143c83d4040d41c9400f00040004680c60360240c4110170b89010800b10707035200b55440a150341d208055418106060070007003003840403040c4030004115104203940c0503000104116050380e000d03134101c1c07140d40d00348503c100092441411000100424550115044410103441801400114001c59403040050111a00c1090b90b502898400d90144201c081c42600704808038155001000f030b1948844003023176540041e01791031113015005049208000710350116810014492001a503040146031500700100103c0881218861300191042c0814060303031074003520080c2014482c3c9402c44096480380c072600030a23801128402071059580310030342c0840c01c042c0000380040c10100d0003141440d416003800ba10a10503048108042c6000310340c7c00c01014002d0814100011018040784164050204081d5079003c07140781c040045515200340b0091902d1444001060b0303a40701e030000c00c0380b2945640c15075074900c1c01c1c62101c0d07200381 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 736394685 1250 736393435 736393439
    0x190201201603051b010e061603090f060201140c0304030206160201060f090209030708010b1309020a080604053409150801290414060d030203071505070314010501120b0a 74
    0x1a07960752481c05140120080c02144032041c1e0110f0300d11650343d1006060221503440c8507219542c4c0e4041d64045c0c2020308142951548500c0c04442c140100c0e04040740983c2c10b16000309403140d0550085482440c104007000c1c9644135181c00420764042100c0050051340413000107a05200700c010b0450180710700d4000401d034103445d412001030082076a001911f2003540410b9844440ca020403565008062f1040204200b901c5580070459400d01a119a06a2a11031350440d0854840e000c5030300c01070102c4810703190341f81010f01d81a030f22040c44400b0b0a54410589807042c0c8000640c50314018440310481c44268030f10314142e20300c006004409501c03008030300324560004d0240028041c0000e480c1051407841c0f5201008100912407a1100c0031243c09103141a00c8000030b00f01c55110642c00400440314107a0907001d42c58105e16511070081c00070088103a000b6203190202581e0025806980991000d01561800040c4100d501800740300d2940050f5400d003d1003411022540000e24030f2001402852440d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 736395935 1250 736394685 736394713
    0x10e030301141809100c021905060f010e16032c03131a030601030207080c0d05030103060c0201050402090a020d2409061e0b0906120a05060319020120 66
    0x1030000d80c030000840b02003001001c03043c5462440740d805010140c03203604031030400d4000d00c0e07903d1140403441c0c60515900c2094107032060003003200c4806000040301c1c46800318034524142c4e85a01090364944a644c40c14000850010142c2844c0c6205003c106100302e0403e1001d01d0440182138041d1103060400703400e12042c00c1c40c4e038200d04942211a5001c00031030303a900700811000302c070300000e42c0110307412600c402015940480f4007003200c0c0c01250901c0c025843c1d0100c1e08207010366101d0003044040d0382c811b900072410416040b40c0950f040300c1c00b41104001514820406909a0f03004460007540414801c0c00210b01c1280c80d0b0140203041340312800010215107010b440b6403603204a400d2142c40140d003010420094902e13028003409040410445204980d4640c1c650500000314025113080000110f000021600c0e903101352901a48004883e12450424400c200b008102c02d03110b43d80280541018090400400413100300441e906075120403140c0e140516409114100d4480d451aa000d4080307200500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 736397185 1250 736395935 736395937
    0x60f1409010c1401060302011b020a0b0a05040f1212030207020306240d080d06090e031b0309041a040e1f0213031a0702010507020d090311030115170601050a12080705010e03 76
    0xa0f002000009400b90941c000901400032140e20300c0515021008034000584500400c40100d511148800351120060070b001c0d6124003c2da00003c1c42c0302c103541c5001500d2000f040c00040b01500031072106242017070500c0304a05038861120084c4d0903501580100f00790340d80103c02c40002680d84114644140d00d0040010f5040b10344e08000d540e40c0d00d010600f6442c4e0511442610024103e0340020011b6001d560f0346c03640c4a0061003d021070405008500b0f00c9901001d00440302c2602c0c0c010010008903242c0d1500745961241c400103580981d25120300340000c0000000c14804000c00d00d160300e240c030500c0300c01d2030004e0351001141941c1c8500c0342d40c0c0000010b10810380c108092607000c2070083c0c01d2504000013421a00010300100c1154409121040f0726900310b0340c02010b80ea08085400700127020322003c00d000d082c8805080c180c0380c20b80390000801070000f140004038441c8210650f120750b6647d00400ca0584200d00403141420a54420b01001030540c10042c084030380b0850001c5155400e003114a429 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 736398435 1250 736397185 736397213
    0x3140a0c0c0603060f0f0608040308190603030519110304050d0609050102030a05010513050f070807021e030c01060e04020639060115032a05090406030c060801060f1409010c 76
    0xf00b6107510007031002ca1241c103001c0e4058459025010300303040c07904034001c2003a00e0243c000340074401040e0200f010080140c0c034025040d01c008009100c11640c900c1c00030519480b400ba6803156141e030035000340500784111500351f00142d0100007141032034241410010b83d10070040c402c0311a0345c2e444a44500241c002c0c005540710302c04c05800091380d0340c54041402404195100c184603941c1ca85010450340c2200880055041402403603c8038460761421000d81c0340002d815410315502005510140355400e0010040c800315061100034004c81e540c0b45035005454000b950b00a611600034489894030030000c00b203540c1d84403e1030000b10080d4080c0410003480909440030309082e0b811800c01444100480101e40f01018228a0104841c840a074122068143c5030700d0348041c01005141c3d00c203846441602951503000b4018800c00c095035a80c50b00031800c211901c01c10002c1107842000041c11400b9a403542d030182c00d1a110b0300540754144900e522568040461241445901060744010a201080e222a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 736399685 1250 736398435 736398437
    0x1e1112030103170f04180b18150a0305070306020c1c12061505030a0c030b060d020306030606030d0f0e13090302030d2403060b03030d1407080705040303140a0c0c06 72
    0x1903254198204000142401400d00500803010480b445840350020304039000c491049510080300304280542c40d018040740007440b984004a0424040440d000080450043c050701c2d800d40e511118441c184903034070400d480003412540001c0403c0011405030340050065850480946901e44607210007940c00c880c8000380d042c001802c0809071a0401e51030711910000d42140f51190010b018441c1000b0007074070004010500582e212031100301c001d402a0404109084010141d986502c410001c8a00035041164040d02c40e200d40320101b0500d08000c282c141a0000c142c0d0350342035040781c0f000160307070321560704004035007011021002c042e4a10741403090042c1070f0311a5010715a280703054402c200a4a40404050310701c146180310303a448040234800240c080301da000102117900500000000e085014448008038005c0c2001e8003030344040540c1d500c1e580718030b846841e689540d07121a182241c241c0564000100821429048010f03a031407214007400c1250f51510f0026075410042c0c4d02c5c030b4003003000c581c4660 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 736400935 1250 736399685 736399687
    0x27090b1009050f130609081809010f050603070f0c05030f03091605061e0904090b09210a2d0f11010209030d080c04030b01080703020f0906011e1112 65
    0x12040180000030800107201042050041d0306040110454001d00a0200581c5400102d1110f0800050f1b40000744000c2e000150700361602a0300d0003e184480c5440b200d01e00c141d07144000816518054078080c0c0603540003406090640d42c1d07125007961040080103c0c1e009004401c01d10100040b000c00051031481030350340d621a2641030030410b582ca0108800405502c0382840c0e241403007152100b034261240071090001102c0d0484484107100121b206801203250464103044040051044400395203001c1c2c103c0b4011625105080480d1a030035500f40910404050400c2150b04c0c6803d10170304003440c00040407040e2080184d19000c41109002098540d180422100c10080c0b1030607402008810390700c3c0c80c120003589091216800252290038007054202403141c188003158203100075105035009954002c101c600c90396107880782141d070f071720aa1004a01c601e0b0111800c03c81ca09000b0301241c000c942c1070315421807034080e41000b82d08902540d4950820005003082c1030010140070070080e10803410f040111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 736402185 1250 736400935 736400941
    0x4080604170f0403032d080601030c030e0609030711011b080307030e03030403020a050d0f2705060a02071e0312120f0f090b0c03091005060a0e09010b0f03060c0427090b 74
    0x10704c41072425a5046c41c05900700464480c0407500285540d034030020900c0c0001e04807448540a0b0014080d8070301284440c0701c3c140410000341307400001040014040d40d60246010f00c10320044900c4240d1490390007903201e001900000264046000e950020039a043c0410300c01500000b052554204450030f60040c2c1c0006804401d0000c113100c816600c00c494600b42c0d084000307145010b0401142404414000000e818004617500b04171080f01c009890003d007114dd031007156950007542c600d140e010303584402101d2208010261581030300c05040f2940410003a51481e1800401c1d1040354544c00c0c05401c1c01c3e190b0719020f42400151150410001c1c0c60400081c0d01051409d200703039400300041015920500400510581c4007001401a0006c98105804202ca03039907034010658045651740902d070040300c1070b4140b1011580642200443e0031098036884034540103c010540d8884040e60401407014081001340001203807074404003e0380b881c0740e05103890303416100886821102c0340300099800200041c14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 736403435 1250 736402185 736402217
    0x22b05040606080f030f0702030a0816120914060d110d140c03130209150d0305092404060528090513020a020c1012050a0c110304080604170f040303 65
    0x10b610103090610010009500911422592441750029801800502050500440d64100020000d540c0c0c82041d458490104c4a0100880b00c0e0030081251023203441e0741a000c085100e5640881124060b0b40ca00344103030910b00900c1550f90166100ca43da0544484901005100740d900404400e850260001203c0140d242100354070714020b820010b0604041043c0306e94070f210042107001960b012108a82c482d103808040c2c2c0500702d5140441500103541c0000c0070141a00000603000761201551000038542d100190111031181d501850045148240018004144202c0207499408100c00302e0301e10079003d200c100040700786440c0d18440059600c440030b02140c2802c42ca2310002c442c54600540c00e10f50b114034040e4658007040c8050b402020f40c0660040c120784207c0e4541200401d242041045d800d0101421000d07108880d2240080f07000c0741078440364200004121011901068080c2c8526141c6a40d400040c170721541c2c030004d01b4030082c4a8001800b04203801040118070a4842164507440001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 736404685 1250 736403435 736403441
    0x1903021209030d0c0513090c110a051006060509090f0903070c031b05010810090207061103100806090f06180c060f040501080a060b2a0f1f020406050409022b050406 72
    0x404281081810700010b138501c08512086401d0340e440c0c0b1404034107110f503c035046883e15003a6600303480300c0c41340403110350900c52f020400180003212030005002d21500e5041c152041d20800326420b4016518270001003400d81c2041869070001c0c00802528031342a09502da4981c00601074001703035860343c108008031405010606d801e100500c1e082c2403008030340c9040e5000c0b110a04072403040140040d00010f1040401900b54021215513011a0800c1c4e11390600b89640321f41c20742c031402201c24500c240404a50341e810000b03554010900090003c04bc266118142c400c00c0b0036203c01c2c42621841110081881c44e5290805019603040318450140c40340c2c50640018403035a40036112030001841c0c6101440003d2907202107400c40c0761005e408517841032035a000ca200310035850744540a00e01408141004100003c40c0c0c4032005a00c1d4211b860382c40a04103d020101e104912880c40461030800c0104241c80d42e5030060559580081000b5141c14504c403040d10515410400020b4003d5540c0c08000402401d44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 736405935 1250 736404685 736404701
    0x1c2114070903020d03050c010f14040302010f0b0a031b51030504031e03020c120301120b1e07030605190e010b07020f150c1903051903021209030d 64
    0x8070740380d140d031841c540104400012094019040100001c1c41c030030070000942003191201514141001540059840b285403030a007950102e0065007805605503445039030303000d0500c0d1031500402042286144d0b0b07841545008000c9072400950f041d180e0006481c10a094024030ba20880710101aaa9900d20380400c60800d14107442050012001407400041da0303071041c0003850440315040000305601c840c10107850100101400340908181d803550f06c1e413800c1d8150003505141c0201e1044400c5010b0b800301d540318500003401403403005040b5428074008103c0415009402c43c1c0407240c0c1ca500c0844002a07030710415021250000800d40f618420406828588610340c000c1d01402440c0e03074140e042c42c450704102681032103042510100400d0807025503031100c802e0208000b0081c0442c00064401808070380c076070000c802c00783c0c05006901100c09008c0d02c120703e641e9501d034541c0e2210f160049421080190802044200c001c00d0344c02d2064002000e00844098015000b84d0000c1d61a0325012010100351b41d421 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 736407185 1250 736405935 736405937
    0xf01143c0c061e160516140111030f070f050712082e0501031a040906050414030301030f060c1214100f0509060607050c031005010315020a021c211407 66
    0x100d00c00d8081c0841048605130070800d0441c07918590f603d000340c11541c9000b14070750452468240c4480d8800c00922403401c0782059641c80083c09101459040729906010844a070990108038030001a0600d2040700102c400840300c1c141301381040680d0710341940381e143d08225840800e8059003070014150300302030410340c0b041c0101249980085050032540003440c5034824941455103448060812700300064181034420f0001e4001c00c910211800c204c0d001d45402e41d400d42d20360b1420700c5402d5a00c40040210f074140c0390003030054000707540c0c6030361007070010a9100f44840402030320a0840ca1500c2d4240202c214412801900040f1030601c00c501c220080c19940c80212410110442085607440d40c0044036800002100e58603103410311030810a0808400c50035043d80b40c000e07000b0342a890140c513030045041c2c1c5d010702c4103582c0d01480c48043c5412482034101060159004c54480b460042920540c04040212440d006075075040c82c454185c00010b1010055989035290440811504240b59a10703600c0002c0e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 736408435 1250 736407185 736407211
    0x4020102010b1e09060a15051803010b060301060804032a0b070503270a0512040f05011d1c0b0a0c030b180403110c1c020f01143c0c06 59
    0xc0000f80040b0a042c0fa4261400f0f40c030520000b40c4d04c1e5031a10020320040c00c01e1390740307205030000680008009901841743d10034001404442c2c0d1070305080c14410440440710140c084e070319590800d41c4c10b440b00440180300f1070400280a0071000300c1c03512082d0703d01c0c4000000310f008111507010b2401890440c0014001000c1080900411405040840c240d0382c01c0c0c00e91800120001c0c00391081d0b64140721090b90050f0907445030342c0303080b80801c900070300810856518991515520361100011952081c2d4615050a91444070125036a00d240c00a40340180101c10001d200c00d01400350784900e003400085901003c0d49030384a04c0000741d1501806140e440741c0c8101d410801380311212488030100140a0405400c024944a1504401c44200038900405400504c10b070342036400c0c41440350801c02400c00032070292040c0c0308482c165500420701c620b521280e00c80c800d400d0000c40304d030498942c0c1001d1480950742c400240506542014003070442c1d4115904110070f85e0703980c0010341c0586003142c040d103254503001c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 736409685 1250 736408435 736408459
    0x19081903090b06061c0608060714120708090a020a14040f11070b0c0c01090c180b01020c1302040f0306050a0b1e060304030e032415030a110312040e04020102010b 71
    0x1000030b0351a40c402d008450041c2c035400500000380d001d407556031050140e24604800810132020000c0c090f0311803005030361980c0444c0100702c4040400d004140c0300b0302c0c00c1c81d20031010920250154203425446100742049408504241d000a029050b96a114800c455003602505a05061601400c40240701e05c040c02c0c09222011549880c1611810300050310404524012508000060044480308203941c402401446030a08211691b00d2491050200b440580c042c041c4011005002c1e5402d00101600602000320240342401201d0007a03516113414142e00700004600030509013954030140d4060729002034030b842c1004d1040101d8100b6612548149410031401640b18615581208540c505491181d03d030b854615083c0c03690a0b07840045075041c01074030034600c240c07280e520030305c0482c800c090300b06209030f00d0f054a4110402d40c00300040750144c05c007c038001c0100b12030000c000c8110001400b1200c903240b458040c180e40380c00c181c02a0700742c641900140425503a0900403000c00d42402c4690000c424 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 736410935 1250 736409685 736409693
    0x30f15030a0803040b0c0f03010603060905070801051f1808070503010b1f260a020a1d030a30090602011103190b13020a02010606021605211908190309 66
    0x40030003400142100e400c40b000940000001b01a03820700b041314819642c0b2540c6410000d0b0150800d0b000d0b03801280d28060010790014454280581200d0015241090340e80c880000c0020340030f451580207003480b400e01c1c3d601d1001328010500c40700410125000e00701c4581042c0270507094070b5664103a40e00c5051041c803100c2c501650321080032007000d401e080120020003c41a96044540705180d0f405400c003007601041440c0380300703800410b800400340e99032551541412660400ba10000f282d241e405500000300c090005011100407810103007612900a1000074568504090300321510201d4002400c10008105c2241c0901590581150042e44c3d5825450075451041920440050380e40030340e6250340f44024981c0b500900c1245003004000b09554030b03000b0310000313800782400d4841d4100510442c18100780c6170f008550720b1410f40740020f080c1688410083c0035991000b134141902d00f0700c7c0c028180001e41c0d8a120381080d0900a108070007a0b40c40d000e030005d0742c0034148515807a1100345424110400002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 736412185 1250 736410935 736410937
    0x3040605090d050109050307111807120f02040503070305070510031b031e0c1d0d0b07080405070f0f0303080601023f0c0f010b030d020a06180206030f15030a08 70
    0x7001601c102c9585062400c000c0d000d407191001c080d20301d000001c0d0503c03c1c05508407542c0e000c0307070064604203610900d1001c0d0410101c0201d4001c0000354a9110500c03494046030014210680f1880002d410261540e0004e42000c40c3c980c411265a071008204005604001d43c14014204480c14100000d000c1c5c50b00842d0051001000c43c010103035104042c20300b44524880340200e45080400c100700f070011145026090079410034411913170440c84d1050710a181707416071028292076440180211551034929003036410070300180007215640102d500104007811a450034100404c02d8118090381d0500e1814081c28102001c4c15060454220b45040d40c041c900004800c5d008010700015008030b940c402204850484060341c04c414007400004100100c900c000a40c8900e5003040c00081001ca494502013642d101070075082000980c120105d08000b00791158091096000c22044065581d11aa0700140d51a4011604828071130714080501117102c2c5d0002e00384001c480c1c02d500900e04141c0302e483d42421 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 736413435 1250 736412185 736412197
    0x31812030105120a2001110d0e011b0c090b030304030f05011e1a01230a0c0501050627100306050705070b090c21070308040f080c01210b041d0c01090803040605 70
    0x40005084175144039910411340301010461000075149080d002440c001c3c4404c3c9442840c0d0300103075104103682500c0c3e0101228003e042d51001d1070b0361f419450b02454030b01400003a0700301036050005003c0000494400e226075020079114400000300b01c00410a50410341500002c801103681ca800c04c03001c8030815140601c0602c1d00242494400c0c3c2503d40402000b0981060106a0a20001c20103121884d04010141d4401f4400e10090125680380d005004440c024481104c4092560f0418909840340c0002483d8008003640c654a280700c0e00e030b45a441c141c840686101e070002c0d00c0000d010043c03200c152101c58010b00800c010f01401394400b000107980516a00007907207007421901144c07540312002c110000003541e10058250302d41d070351400c5c7c0c031640c1e203524400c6034020700409100403c2503109100c004412400120075801b040b5a484401e4000c000c40c0c4c4000750005d941d02c03040307011641a01034006100048030b0081000709905c4000501c5042282c7c41140690f00a01050018035005015100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 736414685 1250 736413435 736413473
    0x30f010914100905251709210a0c060203010314011419020d1d07031a130803070c0b0406020306011704050c040509070b03010602030a0e030f06010308031812030105120a 74
    0x14264641d81501d10400094030117100081001544080d4907a42019200340f00b19406090040d156456030400745c0c85e00100d40300001c6200b0381d8040041c8a00000000c3e0011141900d05490f48c0c01c1c40707a8800d001c0781d10a8006840080403400328010308a0b0034050000c1040f03642c032b03514001d410481000041d0711290300c410950642c02280189084046610903100107048000040c9080c080e03441c480d0b1544840e01043e59118010407100e00306d00d04881e44140250301c0d4404070301003c100c9d034940c1d420b079800141190307080107200c0040348049442e00d1788650103640075580040c3c1e64148840098144001c0400e4128841d4600f02004081503001c980c51000160507940410341c0c1e914221070f241401c806400c440a030060120000c607100b03500101070203600019460721000d010401e010599034258030300703009550381d11110041c130008580d4400f0307581000c000450401c0980d070549845003451f14075400100c03030ae6404001000f8030b01e003985802200d03003809006020030340850f4490001e40007440802d16 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 736415935 1250 736414685 736414691
    0x50f03100b0609131d0607090302300c090106140f0a09030b040b01050a0632090604080a02040b0901050d030f1206140f03030c1b0406050303030f0109141009 69
    0x306803911411a048070000426403090403a40210307a10085c6903202d0144007810320704062220508001034183e01807590b03502d40114591640d801c000000034407004081c00c03000c0710309411f440c19041c441d0705841c062084002c0c00b159610030050101d11041603010f48104143c0200140c0581d10300c0701150031752841102c02594038040850142c4150156520040401040c0784c01c100501895405541c10384008451320006d040d0b881c1e0007150038490031048a602800c6212050307003000f819445000c2c202c1000d035141420039400c0400074000340c1081d41720b103810350040c80740c80302103241c10722820384804003c44505040c0c2d41000003240c13902e078a0103170080c03d01c4486201040620300441400c810383c0700c9400240304094840c040c01c2c9413460030400341da0003140080c50590300d82c40e0210070707100c614041c90018100f05400711000514104404045038201d035aa440c0841d0b140c401307000a40c82500000403c1400354588030101e8111400e074903910940480c01001c0c8080810107640400480d45484004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 736417185 1250 736415935 736415951
    0x21050f0616140f030403080901060b0307050d0902031c02010c0e12030702060a0c1b03050f0d0503220c080102090102070603020a080105041d070e2410051c0c0216050f0310 75
    0x20140c0c510803080f0302042048040300300004c240d402011540f1920806c4024010380b650307000b2a0020740010354056000c18014004201b2882066110800050000f012500340c10210403030f46113540f134403045c0350340140d45031507a29103d40d400000c6641c0c100c406842d40801120f510110f030707440e8002c03072100911a800002e813140c15a40b041f0000300355250464050060300c40c00000044c107c1c400e501c021280b074022988250003021010a5022a02d2041d480381c0780b170341d070701e50311030019000c104410f641000c2440300031640410303103104500001d040307031400060781d50a150001a141c00d1a5601c542c0405004100c2c510752103501c00c070118115103081d1404501c000d4115100003110039a40c0da4002103102c0c144000403100d04820426000304100b0304180c41c1b0407505142d070181c91210722040d40d0006000c5003001c001c03134407a5005103035074284021002e2251007054490300c142c07540b9041da14010b03405078101078a14140341121f00c000b8103017102d00c3d80d00c0c0c038410804262140000c3c588440d00a42d1600c203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 736418435 1250 736417185 736417217
    0x9092502060906070c03270608010b03040308041b0b13051503011d0a0f0e0a150b03060115030e0d1701120b19020405060d050a0b0402040503150403030621050f0616 72
    0x4800d080406031040f0583d550320140607032030110b0107403042400191011b07000152f2a51090110380c00380e50156281031665645846044441c104100c0c08c240392010309400060000d050000341054140010218000c03620300300800c101e803500c0c00c8010300d40d6241040100224401c114503070451855000141d00203507111040c22004208030612883c0c0e0a0030065090031880f4041041600140700c2d500340302101c060000d00c03201300c2c0c2010303001030780541c00280140884030400001e07441d03d0040d8500403e102c0000d5032524140710300984800e000c507070781c00307800c5518031121440340e0f02500c44005140002c01c0c482d204c8003002d07040030341842c40c40205040c2d15006551582c04032005014050302d042e0361500349261000007080101da6020000e031404110a5451916000b10350455100400420200c91150202a40784101910403010700d03075600c030300050b119101000e007035210100300514800b0b8a06401c00780d040810030010403500d071700100c1c10000c090000804d03510610020740341c40c004816281c41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 736419685 1250 736418435 736418447
    0x1080613140c092d011401031a0a030b090d02010b060a110a231b030a0b0a06050907050712032c0a0b0c0408070603020910030e010209092502060906070c03 68
    0x154580c1c100c000c1e10200b002c0d0184a800b401c40719805120301c1303003d00d003164074a03900c0d5200a004000010241c0c10003030801d507100380c0046152043c2c105c01d42c2d810060040001c2c40301041c940c803c46100f101d0344104801140140201c0755042c9050000344058503082c2c000030401d1003003143d0101800f91400540041a10800c500108190302c18801200100d210303a030f0b20a210305926a01d5054440c100b05054580501b45050701000c1c1c0190080c1b00b0030f0f04a50350700d11950801428820b5003036488a00085607941c0046007030141d00316440d00c81c0d0720b00741410a00c0b003078514070b02440c040c542002143e82080d99030ba0302d00506802034443c0c0900300d4040b443d40d81c0c1046d000503009088180c05505010740f03050000c00520440d210001210340e030303d941d8101903007a4015040200d900194802082840e50300076044540d1a41c2002e00061421074400009040c209003510820105400b14108203d010070b40c5456001480050008040e145888211607999410040c0304004011041c0c1d0200101070240d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 736420935 1250 736419685 736419703
    0x271716121410050c031017060a05180a08030118020711120f0a1a070f09050904030e12010917040f031e0218043e03191a0108061314 58
    0x142c05000750309041000302c190360801d445440504d00c0c0703000c00050008003c4807006441000340050044da96580b04408001d100c001c14542d138a2880c043c2c0306c41c003044180300e00d003000380c4079075030b21600c0e541081a10420700d444c007002c580b4038a1040101002064001c02a0504103808035400d043c900c015111603030422135800c18040541c42000c204008004089484044080758600200e0071030380c83e0003003100d4400c4000040400f00703050300c500f80280c0c00d00c201030f181e20501031304100040510b40004a25401c04901c40c030311560350749030564810040c078150383d13560284c0301403080e034101402d240b840e191400a0380300080085060110500110403903003218900e45800800112251080c00880441e00800326411038591000035820141e000030149011940c0703100c1c400300b5008041e4074134041100c0c44456000d540c507200785000b10200107a07080c0514402132103000c68407108402c3c000f182091356811f82110b03409030004420000504101c084030b00f242d03600040c02007992900480304609256003d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 736422185 1250 736420935 736420963
    0x32a06090222061403031926090303190204080c01030504020a03050604050609010c03051e0603070b0a020705010e0303160818032407030c02030a2717161214 69
    0x24800342e44852819840700c801c1313454541600903040c51450800d82c6a20440c1400d00e40100c081c040c1914481c403d0100413501c40d65000d030500c034083d1110109035485000ca03030341540d540c00081008011100582d00d82d40e54592544154180390a01907007984500881c1407086c1007594503c005400d5644822080004507085000e488040c24035090454940c0001c0b12013216540c00d00300c824001601c0780c460700d40f140804d1790f070b4101e0007080482140360700c0300702400e0541d01d840b9850001c140c80350500010056004070f5001040001d180000141c83c0d422010313484c911070340041c0500b100e080100344000c1e02c0c0c02d900010701030303942d98041c2c032080c05100c513031460703d4052040181c121440703a0804055951808159a0521256501401101540e0180180c440142c100b8403044010500a1070580901c450b004000f02d0007454407410710f411031840740e0100c0f04c00421400602c1050720305100da00c0740d594404018503680d500b80100e4030520552907900826403494100c48141d1100d0070300c101c0e05a9024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 736423435 1250 736422185 736422229
    0x1c1211120403082110030f02030a0203010f0e07050901030b070827030405040509030a0c0209180105090c0a06021b060d090f0b01080c030d0206190e0f0a032a060902 72
    0x12070804100d560000c1e400b030510704d00b800000c40384641007070b80032038410140b034580e086006041d69a0021300300041c400c12605071080d4914440103990070b000e9249040c06c0c5800c001011401940e03d01d16007030055200d24001d02c0080c0040c0041800c1a03141903101c041400c05002070380340d00840001e1080503800590110a1701c06000c84d041c0004401007089403030440d8103000a88031007188503280d2203107914010210f68107611260041c2031002c4150b0703004100500490082a00184050070b5540032261010340380c00c052a410030790b203020103d020203041d1a00c018100d480e24440d00102244941c10f4052082c0400b242e02000090507030080000325070b003c0c88904003404a882c2000941c0c03028003030710f10b45000750920780259040003d10041411312a90003402161070f1000000310b100080001207400301d46440400c45e0081040143d000074140d41d00007032001c0e00c8a41070040800902e03175100d1204002c1300307040b01d0403000300c1039542c4440d50304200002076041607440080c0812000c80018508030f11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 736424685 1250 736423435 736423439
    0x121080a050d1104050d0f0809040e01020903010c0906202803020f010c140904020405150c07060801030c05190e070e03150403092304090c051c12111204 67
    0x980720000d4218030700021001d000c264010091043c0740d015901640303410954000010f80490110004448414000c0040302c0c54218240040b074140c07481500740300c2d9541e400051402150500b44036400d0050b64038035040b6180b50504000800c101e24100c5240d080680c02002d442c4c18410070302860b00c82510141038019950406a40c60990900314501a00903018500440b00c450006008070155004142d03140d458064407030010390000c2d008112625005542844041703040c1e265420350700140031a110743c0b2502e03100002042494284d664114a0410900304010000034074403008510035900122203205116814200039030704034601ea80324072001d0039500c040c031090542000301c1c8007180105900390b689a000060310001900401d4600030f0015181413000c204a00300b10791b146404c18a81d40d900305007444008001415140e292600b0342c0c04d9180f2078000c101c00d181488004060040700c44164855220a40306c034141c4c43c4440c000141848012200c04466a400b4408943e00b8100b6401c0301e0707203d42d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 736425935 1250 736424685 736424687
    0x801022718220b25080a020c010f110424051b011b050408150f04060b15071a130b150d080c0a0c0e09030a050706020f1b240121080a 58
    0x14190b82c0e450044481c0b110040403c604404111981c0130240c94076400c0e621940e5035140298410360200040f0356846804032201040c50080040c200c0e030f19600340c0d881b40d0410054109101c40c55142034140040c81c1c551000e1290004103407046020f4210b4107031080c2d100e9054044c09042091510000c1d24100081c01c104070360820050b1007a10181e0045501c00d45080a102080c03c20686a2011800f0442c0004000952980142d0b40240c006403540c904129605d0011641c0d07004070300104c072070442c40b044800028841400c00d5901c1904941361070701608131516400441e21001c0c0c08010480c1c0156500002911582151007040e030340208907a580c0c8180303594040d22a944418101e855000030000044c0702c5414040c254055030b40200a1840d20441da80305848a41c002101224425001d000000301415200040c0c0b00b07001c14424400a4565135035100c50609074150090484103035030003480301041c148020418190350070f001040a441680c1072070700000aa0f00d80008020b0103001036540205 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 736427185 1250 736425935 736425953
    0x4020904063212060c090a03081b1009031b0503041508091b0631240503010b0702062503050c0115030321060906080102271822 56
    0x3030741150100b201c5114910402c0104400c102d221100b692000010445a402ca800141030b00c800007441203044c160b903662001c0198102241c0581c03000a42c12010b51101000e00c0f200040c1e2606c090b00f00300c521055a0b002e840b4465045c406004444040c00380780800108000b124080c190409440e6826900414003d0031500d003113409074518001c1b90148481101c41100c6807103400001001c1c03508041c215110401c0e802140c40c00b10140101600f0802241d50254080c4400340c03840c6024040e090140b903401441c4400700c401c00004204003080100030591300d00080d250855411203040341c2e00c03002000180302e102056180c0803411200c2024480801d50000000c01805500c0c500a200400c1d2020f44070721002140d11014021517584203d42114907910410281000703010000051540e480303901c40302c11100b107600001724683d8002003030151a403452aa5070a003400c1640700801b0b02c0c00150201310b0400c6280101408080f6240c0800d44505030000258030700000c400d902c910500c400c1c1845c0b008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 736428435 1250 736427185 736427249
    0x60d0903140901050f03100e04030e0907021b06070201111504120c120e0d0506011806050a261f1a04051005100e0a030c06030b1206060402090406 64
    0xc1101c0e41c6614203804814400d9952030b400585806092545ca40018201e0754001003480714240b42ca11004031380e039030102040d6805035000e661903030700c2c0f481e0500a000d00281c0c05000c2c00d0540d03100d602c1e0401e1080c80515400503120082c1c4015840390761034070050f00c1881c28140d809c0110700400290110b82d048001241f84603e000d8054002413520569017604c1c422502c40b4081e00d40d200541084a8613402100b8422580d00c02408220302204580c8400d410060300380c00c0501a540210700211800381d4500540000d090115284414540340400350103004840c09064921020501c07182c1c0044003040c030004d1008894031140e070090300260b400950051084030941c80000d8051000b444040c00e01d0310840f40305d4001c02036004441820441006030918660347d852041290980c0403110540320540801c004501c01c106400f5078034100310f4040c060340c84c042e4049001d542c452140d1200c0e1880000c03119000b0000741c40050303407094904003103000303044c0ca600803940f100d04081c01d0300040080040e000170 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 736429685 1250 736428435 736428437
    0x7030311040812131211091501080a0e0c09040606030b010605120a0902060d0c080108010605030606011d040b0607050307030e04110403031d04060f0f1e09150302060d0903 75
    0xd224a900c0031140394012406489000d9001401d400001c1040000500304001c000081c4c25030243d44842030030640045840464451502480001c1c0f60705000002c1c640250f910b22140b4124000180002e01951000740100151500c0364014000c0359001d10000c1d14549014052800e036180c07500342400904224403040364140186000060740b6841081540ca6015907507512410700d440b00703181070010300f00e09001640e103c0d00400c281113801c0e4852140b00300311291515103014a601d8003070740d942107409503440030340a5000a420408a60391096503460324018146072130b8502041c417004580201004c80344180c10170400100101400400030281940b42d1095580d429400c03103040070300080ea440f00801010f40242440300b480061300a001201401507400400319080c0000f00001d4191081a404002404070410b001d11401d40714055140c05014070800c0c508003649200c400034200340b41c911075580d956603a29445175070302803101c21303000040d0380081c14540c42da049140264014092144110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 736430935 1250 736429685 736429691
    0x501030311061006092903070c06061a07021002011104230a06090909030215040834020904080705150907090e03090108061809060a050f28020d11070303 67
    0x1801c054652a002010354146075101c140b90362803e2080c1c040c22041c0b00800d080e1159520a81200c2d01b01c81380610320548050b600d40c61541c041d4208102281c50780d400c6841250068040c20107020030060032501c05540c10f603020100200c000c10124010a620100c44881800000340028800d4864008070590b11180b1041810001d00c10b0800002c0181c0303101d07000100d10001010007210501c0d40c0f01d4120075000f40140c481030f205813100007c0c640d0040720122205800400c2945140007144c0c907040d00c1069070a40e000180b04610784070041001c031040e0080c8124001000182007240742025505550b610000722140c5041401c40314021105c12a008021803169290002c5c405d071840c0074451000156002552030702c0314200045913003c1004240c141c0110301c8030105002006d016022a105940c14000b81c0902d041c203a04074410364502503c0300c9180003c07001070204100b520b44460944407900d4050360080103d80720604040d008000c00c07001c15034a0507964403000c2c1c0941c402407003054402c0e5010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 736432185 1250 736430935 736430941
    0x111005011401030b1c0611040506070507060f05070c21150c02061003021e01030e0d031a06030603060604270302011a04060315021c0606020c0f0a060c020906060d050103031106 77
    0x100202481c51000011707411843d142d420041900d951114440a8510410341d02e4180c407030740464200d9204c0142102c0591000800b004056400440c3d18441e408514100d0320340760300f60701c43c448446c0d23490085441800c560120440150000e000581407660700c80b0425100d002d44850360341c01000545442009409000001072403507200007071032810b80b0740c0203102441c030750307503046c8220a4038110840c070b14141581e901420345d00c03960030082940d000310203540105002c214400908160711310542e025020324400e20500c60644e601203039080e070000080d10005240030428011043c2c01035596241d2691a4400300c00f0000e050341074010b4262404c0301521000704901007004c1c002150100d1001030403149040d00e604280860b250020504100c040d00301200c082a1048807504550442d03001d400541d01c1501618014244042d504296910845032014281e01e40a0050318140c0c1281001317108000003000240c0326580c0348292413031240c621100b00a1580c40e80360107445c40341c125241860074410700c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 736433435 1250 736432185 736432189
    0x5090105090f0a08070f0507180b0301020703050f211006031802010e221a01080a0b0135010b0304140606030a170706140601030b1f111005011401030b 66
    0x28a16040700200142500c8405894501c4540c10100c011582082c0d41b826803c0031410802145000e030465064024845c9501030708035080300c6000b22614040d900500120000c00e0f00300064440380c820094071503035540202140c1201c550400004550444221350074461404900c084040c00da0b0002c0e101001401140361558440200c0280c0090029140025103141420401a000200c0742101118000d0350065079001c820b035100150141d102c011011480c041e45e40e405001180c000b07408450410103800140002002d00e01c0d01c10002445014074888214032490104a46144003400c1c03603860410f585030204034101c0e074800c0d18284d070000c100042e883c102044c085811070181c800140200300800081d07075640d003030103802c44110400100a02802e00428140d02405401503145481c00020703140200004d012141d00c4103949004610580c1c5610403080d21220104102c189820941b0380d0560f21000c6610f41040b00350130007109030400c00001000100c0c404145c160350b070240c80902042d80442d003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 736434685 1250 736433435 736433443
    0xe031209122b0519020a0b0610090306020906040b040e070801050604080c10051902070303090906080606060903070b0d051005060c03030f25080105090f06150a030f0f0509010509 78
    0x2a80205012030540040038030410710340000e0b10051900300340c1e081c851256510f48010214216240158001c58005003c1041c5908010703071040b0111001d5a2034081104002e20403003c6010040103990300003044902940c68406a600803d0b52082c4640d46503149e031185a4030001c103a880d00041105000003190620b45176050782c040d62240b400500081e01581d040022203144088040c003030020401000d817815050103140c601041c03486d0002c002042c0786140042c4008415440000603900c1c0c84420f20288002164441d04240225102600c40c0b00420000307050444a030b0150b14043d0740064085221001600000e214180b103140e6812130595075010f00115100c0d04210410740d800030400101e6585000700019082a803103440050396002c1500c0611002b0404100500400d40d010010459072900b801c05a60000d17141c1540d40c2b00c1d0a1060110b446091001d20b04180b040020580d001c0c800d109a0082c2c4200c00314000500c10460f003041c0004c0148000c1c1c606982d95400e01c0d00142c4440c01c002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 736435935 1250 736434685 736434703
    0x190801030b0f0a110703200304051c17070602120c03090a230304030c0e070c0804050910050a0b0405030f03071a0c0c0601230d12032f1b01050708040f030e03120912 72
    0x82c1006036036083e030a607840100bc0e05000c0403100300a1031000b00c40ca1071645805000c1c07451041030f00581c1c07212840c2c80c141c1d08400c0200b001d11003070070030000c0101c2404e001c102c041009520205e04804901c40384007030b501c0492882c000c07040c1c5104c085000000d02c1501c0d03062804076a01c0c070707003031003515110420304450b43e5400c6c0a0181988500b00420040c6040151600b80e200c007049561000309619880024035181d0f203588501e100f1003000c10180a00d10703045c800c0c030b074000c1c10800c000c6151a00c1d50381da2000d150340006070344a000c0070721400254001049030407142c0d004008030545400d50303100c0b1500740202c05905106040c0c20605040700405007440c0056144254100410011a07950740f1400c50103840c07040d501201150041a0040d40c10044180320300110001074121905c0304062510319844100304510070009a06050074040c0c80b035004003001c2d0308a40c00103c4843d85000c641000d607000e403441c02103250503105101001d541a11078038040c2c5150041103e8841503100340d11005950342020b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 736437185 1250 736435935 736435939
    0x6080906070e010e030706020f070506090a0b1b0102030f01170109030210020a11030301030f060e030304150b0612040c0f0609051c02030c15190801030b0f0a11070320030405 76
    0x4188128000c400c59088880b0501d001d418504070600480d09008166120201607404451400343d0f581c014001600035140036a107043c10400d0b0000040c0302d0a49074171a0040307000c0b0000381e4a40e134264034400c0c240741070400f030300a5540e41030410908a29071000d10800004190451500800c6103040c00340012058050380248500c00007100d521000350b2180d00c0740d000b800003c24201840f10b44c21f20145000f54020034101e500007900e81424020f4407140925054950010400c10000400c4201641200e003c1100002200a504408a41d80d80f04807151481902c681d034040004100389400c5a50540b658800c010305566aa907000f950000d00c24001e840c1d000034011112000000f50400008241d030004003110711201000002c1901004c2d42c03591440400c40c00150500c41c0d400c00b52003d0b483e240c0624203d9050347c0342d51150311300d2080c00343c89012a04101e10200e000304101e0b801c011951901c0d010010b82d00c00e02840c000d405040ca00c6441c124000202400c2059441c01000307940c100c03140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 736438435 1250 736437185 736437193
    0x1503041101111f0509012301060c0f0b0424060609060c232808120a0e01241202090402060a050c01020a210902130b03010b090c040f060809 61
    0x240041d42c52200342500076900d881a00c00301407060103011000411110300250001d124200704d002c1509440c061820040000b08901c4540c80c0c5040250030541102d20601e0003403507442503032030700703411020341c44070007a064139442030070710007030000201100c0740b22047c0c403e4109000c6e2000540d402030315001c1c81003802003284290100525070180301c14190183c4284031050071070650000800d03401f100b4120f440000d0380100f034800040007000320344503001400150450030380001a5900841c52150704d003070051650308000810340001c1c050700301d640c40c480c0720802808040b02503201017101e0b0340c80c0040c444100c2c80203500050540f59004598030459006401890b00b50f559409212032640980342c0d4004102e420064062072351400c2c400760503040310750317034986c07103101c1d0310301300024081d031117005e1000304145044900c1c001640c490380d01d5420441d00381000309019074000f0000380102520645c684e04420b00004102001c02c101c00203005036000320507a001055190f01c0129142003045416400940c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 736439685 1250 736438435 736438463
    0x6050603011802070516030308070c150c02151513060e010614040e01080705101b020114160605040219060e0d2409140c030a060f0b0a1202150304 64
    0x140d0b0341d0002152000c0ca1000340c50702e130b005c5d034841d4a0043c0c02d0300b116038042c203101001d00825903c82981a0003481c18a001c041450301a01c0321060f43c00c10700403d620321a9260450b459281c020300c01c20941c0014540400c82520341260001c1903d48032154003441107140c7d14036110306540ba441030340c041c0c4242c0030b00c0b03202981c2000301c1915240d01014840c0ca91000c18000003400c0320042443c1406008584050400740c1d2524081c081d1060041103614203000030303d20105c21102015151508090302443d044a480744607980842c60391003a06404826a04402d0003181441502d03000039000718429039200c82c058000f4400c40c0c401100a0141c032002070702e8048000d01924101d04803c40d494002c104034045c20380120044a100001c4000c800035480d216180761042c08011550162016007940140c42c8038014940003d854248694004018958401c4504000030075607005a28808014022400300e64071070609c0c071444020303184200d2251002807c54481580342105607405035902032074010103e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 736440935 1250 736439685 736439699
    0x608061b0405041a1002101b02150402190801051b0c06012304050a0b1009061b050304170307060c02070b070605070e131a0306040b1f0f0f180605060301 67
    0x410202140d002c440c3c1211240000d40d00c410449440424a80041204091a42851f410f441c03210301e4503800300007a0000c0502880d00411049006850910101da8aa0725840001c0610308640b1090100d4589800086840c0e82e05511190041e0300c6804000c808140a841c08100d0340700e0314031310a001d0b4020b94010030820180e5803c40502c40080d05600c20407884840c0441c046070b00881da11041c0030744403103c900d081c2c1040c80d001d0424000710b140c138014023410900d026020814680d80154401e141c402e0072800d01c04280165805000d80301540c0951500c01c81d1038940e00c4d04071120588600b4603241d50007107024000180c0000301c424020595081c09010b440b05001854000c20780e00034006021580310781c0303544003031901c280c100d45507034001055040c000500e00007480c420b180398003030f51011061001050b240c030501603001c0301c040c90080200d81e135207206658807143d90f84001051100307140085400e10b0020000c4040d9110449808855030481c100c10b000e8580c0c61103030365001041080140000707 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 736442185 1250 736440935 736440941
    0x110613030912170705010f1b180605041203120c05120a06080c0d050f0604140c0d050303131b08031806180411040f090b090601020a1208040f0203030c010608061b040504 74
    0x84e400f5000010710408194081000c0d1160000002401d44050340e10b06011034100c807204004500014660000e2030614501070315034800e502a100c01c40c12014407a004240c40796100c815007461203882844071010989002c1d100d900708000c80409002e00c44001040d54803584964411181140c00420071003007080c00380408201c0d03c10040e40c4c1c9028140c1c44101040c410041180117603c200c40440d408001880c00703c2c10a2440c80c4041d105414044403040130901c00000d5031f4102e4550f007442c0c41282d01034503011040100d09010381416002c0a01d0000d60400c0100c0070740552178030003200140281c408400c108031841024140d40c8089081049640fa0341410ba00c58417081000349012450a61607080c0403010f500142d04c000c2060380c840c1840300c035a04105a1094004c0000c3c00245104011030381e44821940c07103400746208000a40b0700060500004003a840651500a81926a215111031540740a00154004c00b0818421540802c81003a120021a03405130f0301d1100780d5003028284801c200c0a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 736443435 1250 736442185 736442197
    0x304110d112106091011040b041e082413150c1b060204080c0603131214120402150a021e010908130e0f040807080a11061303091217 58
    0x240e11240c00142c1038030201000740c2030045400c400106440f05041d82c0c04015681c520300416041c0e14148000c10020107003e003030303030262211203000300d07800d0101c0820142000e141e07501610750b9109245940c0103200e000c2078107a0248a400781000d1460355000ca641d0100a120f0718000c10603507001110301440c0c051640903400507200c61078084034081d103540344034031000314030b040c1628410360020342007200301c034100703c0c0c0800c804094030003501b5031402e000706550f07810009802a1442501300d000802d280c2c85144c4058980c20700c40701d0b580c1ca85801000e1440005001ca400300d0081414004000d2540c1c23480082e41c0700d10665034001c001140410648842030248400c01c8140c941d01c6188840029040c1030242104820030300803203100c5441c100d010035441402401c40c0155405002c1440041141d0500312885550001340c030703680c0d0f5076605500f1500312840b80390b140c006005d1030302480811400d500703440600764001d0342d514402640b00c80305c400c0b15907903c034002006a0140104503184080040107400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 736444685 1250 736443435 736443469
    0x14010e060a030b15090301050f0919050304090f0608160e070c020f03060405010917070c031e020409060b100513091104090e0313080d0c0213090807080304110d11 71
    0x34003180c255000c01c005131240758450340e0214000c5614502410240700303066100040d14003482c3c05003810b564541c6c0f199401c81400803e13800a0b14010144038003081240c00605400900308400c0b0803603142c1100410b454050003082d030040305071007851012221100c0e0161000f4203000009a2500b8900b035609140d100412038001801d5490030a8550382402024841c41c010b0f40040b9000c495407602c0d10281d42e510075903400b004420304c616170224003001980d0040da6803050a410040b0450740c80e03c12003a0051400070b40c41810640707540200030180e001090764103001d46556001c1000584269064062442c1085440000d070340c040111300b0711504607040c8501c0e011807003450039840703050300070954007038102d552625840050603c485040708a00100280f0148020701034401c180c2500501e40c00050802a1041040b2016805140d0640d40402d50300d03980a4041581c41c001403800791000e40080b2010f880b80100302030900b5940c10020a1021303d558040620446020150100304c80e2500045101d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 736445935 1250 736444685 736444691
    0x319110c1503060907090e0a09080d02030702100e0c01050d020304020402040302031e07050105190806060c0a033507050c03160b0f1008071413090b04030914010e060a03 74
    0x164164a9084064265614041507a6500c2c9403803401c2c0144d0380b402410441c100055590100402e25180f807032550400c603520804035030b984250501090600801c01f0401c0024400801d00c848503070000384040c0000c540d024103018034241d01c4410b646541c000010310b03000c240108030840ba201e04641c0203680c010f200070f20050802e5101d07004a0701c0e295402020800090554880c40740c3c0400401010300188402d01c2c00d01c0c5441c0020450b10b030360903141c000f40c1050181c08000f16159a644005640b1401c00c0b850485010303900d2401e000301340040e000c80d4600b0701014507070915201c5015880d83c0265a035030a07100215510348130341c1140c80364085020300300d50b8001441514035400d129031802208a01820b04040d240c10a10241d29501d81c02405803001000c403030104120840000c640300c0d044414422070140b4000c141300c080b5400c50040c01082610600d0b00108204200d444102580124002c0c0e0350080310700d4a98070004a1082082e40c000c0c0801c00100400d4141c1c90f0000003001d0001107440c1c04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 736447185 1250 736445935 736445953
    0x712020c18190e01093c02100e0d02100302070615030305161a0a0506130516180e010303020f0f01112703100c0e0d0c14010512190e031911 61
    0x11a0505c0511400d085a0f02c0b80704410440105180030f2246002c0184c200d0402d101b07502d80c0010b50401c4048000021b105000491800c141c1d02c101c03041d0301e03c40e000f40109031264000302c4000d0080d44084001c0b00c0032840d194902400c914900c402c3d105070380c0d068680500d4110800111489800d08805c00c8825071803002540317810b40081c0b22010f0042401e5000414682440c2d0301708030000c07601440071050b0783d16020410a130101303608009040700c900c45c2818104c4500d40f80700c8102c007000d190081c4442858050000081550008140122280305025542031024800c645400d8810198480340e1201090000d40031070b83c0120f14806980c118811000255001700c1c000c00d081503a0014444031300e43d9641455102c07250080400c00f00c801c01119004c1d040300540d40d503540c1c6000c1900801000e034030246643c840c1c80e4003990031913030100710341038040c4941c2c540444c180d1488140b400c4590107060030304460812401c0e0001c290741c10044c1c15100540b40005860044420244c081c0908041d4402c8841c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 736448435 1250 736447185 736447193
    0x509031b0109150c0e0609040f0e0c0405160504060315080a06060501080109110f090d02030a12020705101b02010e060703021e03072301020712020c18190e0109 70
    0x31440c11010000080b80c40d00703440c01c01559040700d00442126507030400c900d510000383d21090f10411351400300c40c0c00c0d88607486000850024000d42164807002c515102403118080c0000070215202002210f040c401591079424540e0746104052114010400900041c000e0b28001e4110300300fa0107401c1103000e5880e036511a001c3c03602240100540e90b4075a00d00d000c0c001540d0003550039014083c40c4205114140102054501a20414151f509144000b1951055640c0c480c05621100341d00101190402c20031814a0852040c030411000c01600c20302000182c40e04001415030403915454072003140302e10120340c084030b200030007460032810828202c0200045a444c8000341690310300035070081c410702200301e0383c904010380311a00505035075000703110b0480003403c954407090b41c15100350390448150110070b001c10302a00501d103006004015142341410b00d20ba00007001102004110307541040e030801c000d1781d812502000e072103e401008044d02e05084075140791300620f0400d081d00c8000183d81807107440d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 736449685 1250 736448435 736448467
    0x106091806020a14220501080108070311130e0607090618090902030a0623060a05151602040207080c1e1903050c010c0c150b060403020f06160b071d090406050903 71
    0x102d009030288a2203585002ca81107a80b45c58003030007003030070401c55a5040c03510055488406100003040810034200007510313910307400340070380e0700c0300030b00405001c111034503000766445e000b080310501d000440c41c072000140c07107100350100e40320b00c568034031000ca0550900d800500608402c200681e01817290041160014240e4415036030010360681d841c40400c40000c1c41ca242c0c03080c015000a1040c51442c40512032070f9140800703a6400310102c88090b540c0d903800660b003a00c030b051404e0003070343c418400b2405074140102c0ca40107046440d910030944142c0c5140c1a4041e0f51b034610300d4003048143e4013485500042100107a84045841c0c041c0c10703c20305180c540e007025425900c111b0081e000061035041040200900031540300c1c8410004403080c8040f041c0790020801c240210b11001c1e1050503440c04502c1951204412030b2a40c100d0b025400a2281396410300e0500104169001000140000b0440b4480a246801c01c43c1d41d00d0000c00421840d00d45032100006050007418820300d41c0020003411801441c7c2138 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 736450935 1250 736449685 736449697
    0x120f1202030a14160207080708121b070e0105150c0a030509010e091e07020d050a030902060403020310090308010b09090103020d060e0610050307060503071e0201110d05090106091806020a14 83
    0x1070311020921104c400000e00f82a89030340700d86640e074015402401018008117107040c050f11007410054031100821440800c8000007591840940901040400d40007070030596a81610b200342d5554580d00e0b800243c20816110340301c0c1c400016007005804d440083c0c030130001400c1c3c0100501d022801d000081c000203c601e141500c6141d2003007a01410498a440404503581e0311400070300181060700994807028140c0d12070034010108160b07882080c80f04558490302902c001d19005011141c812004d40501d00c000c140f1003100350081007141c00006079604a890448410032400390034514941d10355820302c503400c132003814202c81450712000c0307413004c100080003a00d2044040e4900c1c0e1039000d10300428107042c180300703400400820904008101d201500b0012030310051f440e0b05901e0804101000c012401000f4601440d00000c0c00055061440840e0740c0045001d00c050100800c1400c1c4e40710742460448206a44148a0f2055031003a000410f809a0140c07030f0b490700c1d03420180700100c4102c0c03014425601c18 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 736452185 1250 736450935 736450951
    0xb04121d120309040f15121a06300c04110d090c1215051003121209060203090102090a1d01030803100e0403050307030f090c0b1b19120f1202030a14 65
    0xc2d00100e0303040886e85c1c0c80480140341c5c2201c0c280c10070744079407940c401039290780101c00000c0e403408002c240507481c0c1640440f0405280d030300c21f2008100b030044015050034102c072000400d201c0e0003020400c42c541031044084110040c17085070301e0089000403440281c50f100c8019100800a21000640452041001e20b801c51081480e51224040f4400c043e0840360701422203210511068400c0c40000c000c0500241c1d40e600e5814a08081e4502020741400741141d10720003403c0c1d50005c0107110800030150050860900103c0d0600c004130f80344d2514100b045e4071341400c0d180c0b2049c0720004002007001500116045182105001c0038152500b8000e6282c50058804500150f0300204001e03443e6410711815000302461f200c1880401c1d000d499440d184031a0740500c0304c4841001030322542c0015081c0c9103010701c20300482074a400a0440101202e4182922000c0c0c2e01448011046a0041d20401121501b9074940c0c40b2042800094031244c0d0094000400b441106c607a500321090400c252002d403a8854821 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 736453435 1250 736452185 736452191
    0x304060315170c01080406020702041a21030409020901020f0a030c020405010806130204020901111e0f150c0d060902072d0b0c030402011b0b04121d120309040f 70
    0x400c0018445080e51164003407420120041000c0200428254250f0400f440c20040c1da4030b8030306000c0028899508000c1d40207141c202801091007042c4103805041c0000ca031500ca0460784030485007208058880c910b4059001000188107515055010304522403061044900d4503000c0405a460107070510020303808180f1610800e421441c0c180290b038098824100906807500301881004a45c10500c84000d12580d004a0702010517449407070601040c00410381102d800b1982107080c00c0140c5d0110302c2008050003900c503081c654940004100341c248910042c41680d0743d0f607503c030710202904201080d8001d0f40d120031000071041c07214006011030034060700078801030040ca1140440107080503400741c030001100c1200c0350003281404050350ba029180d061034913603030f944610040f5020322041040003541222080c0040034000200748551007288541c940e40b02c000c54218090ba90034849440b80f50b100c0d00c10315070301d599606104c410003490040e4042224100615180001c05070340c1802000ea800a907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 736454685 1250 736453435 736453451
    0x261204080c01031e05070e03070f03050114091203040804270c090f031502070501060608041407051020030a0c05250506031806070c0b0633040803040603 67
    0xc2804288034103202403e081140b01440c1006140356240700d9105200960f032440060000d40c0119000c030540d9000031700307550942d9200c620700c00041c8580c0c00300340e555610706101104d002c031048403400d000d816450014102c902940d030f21000d69074002001114400030900c00050000880310700d5244418281c8140c0307020284540700d19044616560b691810000046010842890f280300028140c0c0e801030300b800800c00556901030701031310855030300400d40c2d0701e4803100040590340301c2046400f5902c80e403180000110900802c2d03580c1c1002d4011184d0141041e104043c40b94043c0c03035441c202001d44500101505081c2540c8c1d402c60b081000c09501291070071034140100441407241c036200340344094030210a003171103800d0420881ca4a004050252100002242401180c040c1145084900b84116085450f0815000301103504414003150f9a4074580c000c2840c924006416480454180030340c60740b6640f076101d0000184030221441c41000008104c04900500240014400741855880100e0600303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 736455935 1250 736454685 736454699
    0x7090303120c12020711060a0c14030703080f06030a060603080918010e060d05030c10060317090f0105130f09060611071508060a05060c01050702060606070309261204 73
    0x101c0c55128188114601100200348641084040070707203030441040103032100c40718640b0608040a031043d2582c0310b031022816a4400743c1c4452841c02540c8500d420301c8944074640c0002e41e43e405180760083c0401d9030789001400c028000c4c6c0b50380d83e00080c014212564070404bd1603c5040350b04581095440c0000091218030900341640709a6a01010300480398540d8580755000ca1000c0d0043c14540c4900d202007961400e005041003a1200d884100d025141d114040c030b801c01004240f548812074100c0c5140c1c5440400d40798080c10f60300240d0b0041c18140741e04580100440d000d500501090900708400304001c03e00c1c0c5000c036000400f400722400005002402c0185c041c245200e06510b49049511650092241040003030b10824079240e54200540e903600c40000040d05140280c201076002a408101c883c14114150010b90250749540c090380d006480d0030080c044244207043c40074012a000c90020000d4411490740c04401c092000d482c440e02c0452810603070300300701c030300342c072603041401c002ca03041c4111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 736457185 1250 736455935 736455947
    0x70218040c080c01172d1003030e040c080402011812030c1a0403120507090b0c0c0a0e060d0b060607080309250f09180210020a05010b04020f040e090a05010507090303 73
    0x3403030908080d414403002141c2a415114024851003990307032904500c1210345400c4404841e42ea100c0c0d01b50351994a054010400030800c5840243c00158450360390007040d041500c80c44c04000982e0717031008081c0e030317a6800541f200807690207101100915100c0c00588502050100c0c400140701c0c1e03848020348025070402068079900401c40941c074040c10000c0c88000390304003420b452041c011500104103030359826030940304080107603c1101d503a980041c200780b404402140c626034902c030480361514229241d068842c03a0780c8045a207207030000340210100000c40e00d403a9101da0f00c01c200030100362a0000c5990752004680003512000c00036032000341441182403061100d41138240031440008502840c0100036801004184101e07075400396250b40b02e105210350380d03085a070115005803c04c495100549402036442040c1c1c142036526501c5d00044800c2032400d4021501104005440541000d0038600e140000170000b4091800601c20710303071401c0019100f8001d15214001580b07a0000303281c550f00340035200c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 736458435 1250 736457185 736457203
    0x70b0c0c0114090a1206020408150a1a01020d050d020f0a0c0c06030e0c012a080301061404080c01030b3f01090c381305180c070218040c08 61
    0x5800040c040c3d642d268640d055000c0480d44c5001e128081800b0b941800d400030f01c1250840451070061000711380300b5941c03030b16450340181010781c41041340724041901480480c407002403a0340182c02c223221060142e480b4034050014110b103417400600d040080d0070341d074442e40d0001c4103180210b08101c40d02c01c14043c040046070300420807070800344070304602026a161144000d000003818007103114074100342c1e0300d01001100117505244104140d041030506001505800c00d116610008446138010081828290250781c2200d580000402560944600550103007101c2801e06410100111204025900c9410600310814680c0020b868681c80e1440c4001009c0721410303180902d07810300c2140d80004820341c602c0030407200640480011103c8405002d0701d2a01072024034490700001c0003000d10b01c5001ca2004015880301c42000200c0380f55a8028041d10400210104070000180800618101403800061910381d2000b80126131506480342601841041520f0035684089161801d029000c0c2c02c00104136 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 736459685 1250 736458435 736458467
    0xf1206110301080c0103050c0d050703050f06010c020303030612031309060801180f0b07231909060804120c02040e01020d06051903081602062b0903050901050c070b0c0c01 75
    0x803640d814190881c4e55150310314040e0381010390341d5002589150240302505c50700600e50030284680e0030308480080c06403109031035100f000c80f282d1002c51035640c0954580c00f5901d9025010f581150345180c00c0201c40c451105d410103141c0810040c68010072415540180605074904000502c1410000c4203421035413102418803044810075800c0e408a4036900345c0710342e4650b01c5100c4612030ba58248007120000c604419032941c0a0070440445840505500a40200000503000540b80c00d507000040360301721414410320f00030554030f00c003180200d0b010070481740c2c4c102c5031800e14900c140ba56034049070460b5002494542c1e035075408554814111658010340000f8002154041006000200300c40484000c520000740a01c03400a28507505241c484c00300404e075030300206140e44502c1d01412104034503103044107041c1c180150043d80100d801680c8161454943c0594856040044404c0150340c20380c4100a480145d205500d00020606d00c44801407404448003c05000542e4501c0c001602d10848035114034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 736460935 1250 736459685 736459687
    0x4110909101104051c0632060414240306040c060f0e01091203231b0a12032d0f0e0a11040b011106010b071103210906040f120611 57
    0x41941e45807003801d40d0320441640900c0c0c100003880e10038010800f2400549640805094262000c1c1c8603040e0550094484a00c00e05c4a83c3d48004003c00c44002509142001241502003500702e090000521042f00e0b204110b00100c0c200180083d15120302114100c5440301292001e110096004031030340440b0100741414400518010700181c14000c040c0980e0141c00740ea103090b5000d0500c21031a104a03010420a85c041c0c03032242d800314000b654085400c00c0c152030300c0c012007686200c000081c018070f50f035040343c1000101022418210064049a405900c04108108150741d2032040e040e40350440342c555550010b440e4400c44001e0003507406541c40c00780705410003000e80005c50b1a203070341c82501c1d0303800300d90014600c18800c0050300d600d001c1c88000307001886120000310b40c0c42c00350001003500d00d00442d01015108161341c01c150b03449000741c1c02c041c08102c982c20900301c00102c42d03010705aa1071b80185542c1c2010386aa0300048290f01503030100d803190860a04c40024003034544520244140006205 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 736462185 1250 736460935 736460939
    0x1a160503120a1b140309070506030103050c100503240a08031206010e010c0b011502010912080603011104030f0b040201030f32070801060e0103060302040219030e2404110909101104 79
    0x141008150700140141c00c130000002407048001446040050840100711355160b503185d0030701954034019030f10341c07a0042001a680d03181940c00382040e05d21801250b101907881c5a6001043c0c81e02d02e24401403141c1000341001c021507440b00a00c003404003802c1c54a42050689000400104514010324500e418080000c0711480403902442e0810705403130700c000f0104c06142c0e0b2040c049004006405000c0c1c208004030f0039031031115500c844100d01074902180207001b0310328916201c150503c00c0c0e00c00144549101e142c030310001219903280c02d030b0080c014140001d070030180040080a5650141880300c0891500680368a010304487d400c1e60456040c00c0c0a40c0c1a03c1c1942000e4600c0b071041c011541071080c0c0800343d081e5603229421000255501178025501e620350283e171801ea40c2d01000003c00442d092085650414100159584503c01c014584803528005040e1203034000c03c000d0700944e5034807070350203e141e001d4480300007007801940c0c007400800200d800c41943c2e4084844500318660504002c00c02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 736463435 1250 736462185 736462187
    0xb0a0b1503040c03051f0f0513020d150e01090311011109190f030b16020a05070b1605070e01030b240f061b1c05041a160503120a1b 58
    0x104002140400141079620344032401c242140d03039010b0b40002c00910400740a81d040342c10400204800752115501442003e0680e50702c1070a9031821a08520b080b00e140c5041c0004d8a45152100c035641c1c058541c07642d01d032500f0600001900c1c41070b018400e0036911580018201a4130244030350031442680c1c000c11651880003d802d41910400024600c2600a0b07426185004c0e4201601070040c0b80142040c90b6190781c900d0101107032101241e03450354202c0020034120206002241e0640b41030340c041e0181ca001030a118200b801d6802c00ca40403203100000205210000e10100702101c09017061648240a41d8510b18240001e400000c05100c44e2941010311060203403180c0101403501002100e070302005699080119825000d5007440301c080038040700500d404844045900e00c0c0300c10b04940c0c1c0884d41e04064030150303014821ba110355060020900318400b84902c000c1d010f09101c6425030207045000c2d0309601c0d480e1458201070a11445101180c05204c8240b199100705040300041130346400300e261603e00c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 736464685 1250 736463435 736463449
    0x71a0301120206120a090210050313031101060801061403010501170601120602160303050405060123060c03040506030103060c18080316051e0307060c0504051c080f03040f0b0a0b 78
    0x100710340d90a054915803904664440003075510700151200165120729182c681c0c8409048014803c0e4021000c100442002d584114203c910171054421614070300045541d0498982c1d607000c141d50099541c90381d0120304200c080c05002e00800c1c5461070000032081120801d800c481045c0d000c482a1081103203402e80341c5101040c040e044400484c0e0041a0b0b548605024029100d1081c8480c0700320f0080c0424030405030103910180c000d5000754102d800300da80341c40500c0c040390403240e0002441101c00005441c0391411034000d01280484100381c1f800e1a5441c40801c4994000ba0011140c403a116640c8000340c039400040080300c1413000840c0c814046c6440a02902d900c61030300c26010880d111449601272100801c40c0e51007440401070038059034119103c019880b90400c040442c0d455040c4a540d0b48020310030025201611070042541548114004007101884490310b401c9611460130311040c422004800d020754456030040303015440c400444d20f00500c19900052520102c2840d00440d440c050300c0e01c2c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 736465935 1250 736464685 736464689
    0xc0901060f03020306040b060c0f07060809190f05010c1707020304050a05040b12030d0b1306050a06050a09081b21030f090a0b192d030c05090a0602030c071a0301 71
    0x4100140c4d01d803141c00106000c5e2080100d210f4002d100000c01020b01d010000710b200ca881100c01c15078440c0768a60a08607948802035454400c0390f0f100c0050401072010101400740070902c00e491141300101030799141c1e82036450680d0020f02151018020b595910300103082d103580080315101961a05044c0000a8120860350180c280165a50058070b96980caa500c05000c618505100f102d403143e0380104000b0147c000c40000501074070200307070700d1000c40b80c032802800c0659800500d0b8074801410524120785507040300145100b0021483c40009001006210501342081038185644040c8000ad0900052140e1040710a090038244109901101c03804070540c2c9c0304512448420b550b56810398001101d0520702d8018061400001072125201d2003003450841c5100119143c1041d00c0d940070050048401044c0c0e083d0103a44c3d12010082c4134540720780c0c0080140c050606045003003154050105881c2d4020350003d0016034000510a0500003081001070010150150441413407030000e0b81c411000d00041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 736467185 1250 736465935 736465937
    0xc0f0312010e1924170c0a0302060306010f02100213030309120308060f0a17071703040b0d050c22091508100209010306031703151804030804050c0a06030504050c0901060f 75
    0x24091300040402103000b40c0c1c182c54070f003541c3c00100030f031207000220307203114600b9040b549072003030741c07445d180a0078400c03868000c81e6001072240d400c55545c44015a000f40020b000b400850280b040628918007140c0302030501440c08101712a66107042d0f1401502c2c0a1080d0868121005583d1204d40080c0c3c2c40598603900141c151003079803c04030311801095000720310707412011a01c605449192495500040c1e0300045a031880d1095110024082d40582c50744030310300445d000080704010007251801a504441e810a281008151414107040242c01600d1048402c400040581003c1045a00c24500a00346038000314004082d1103440c00d450a9950300c964032010300c52030b40104a500d0944e01a0388003a0003907401480d103030003040c9042c1b01207401d6402150030209031025180140018244041407502d03d0b041081d481116886a407410307210610700400c101d0b8140b20b00001100c4a4451026050050030703d42c50109140c142854014103002c2d441a405014000e1030004001c000c2d40484c00780c401c4115 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 736468435 1250 736467185 736467191
    0x4090c0c08090f030c040f0f050610020d030c051209060618060d020d06020c0102043b0a02090a082a0904020d120203160f030315050f12030c0f0312010e19 68
    0x11501c086420803034206045c5a0003807500383c00c807a29003410341000c904844e0f0346408006030341d920740030040c0c90f10030441c0483c0181d0140c4e52400ca0180290701048030702a40b42011800c00800306100700000c0012540007240f5000001071201d541807200c2c0c0382c0d44500000001d80303190318202e00401c002035008540a4412040c6d8280304041c0542c507811a908601190001d556030364482031100d4002ca051402d40158124080002d000841d01070408003149003c041600300a8070350f039040d480690031118540c1c0d03001c201e00200244e603880030419810030000081016062040b03122780600c1408c250300341140192018010000181c0c0d800701640e15595005040c0610000303009802c902e11300510107003081c070030204004481400706034842c510f4564403035502404045506000a00841051700c51540c03c2010940c1e511810700c5c004c00038022908403042182d050a5030360005500d4280e00040e075000c26000050112168100300f48810f014058403d8501ea81d81018a22140b41280c030700031515030303156 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 736469685 1250 736468435 736468459
    0x26100903020c011e0e1801120c0f061209140d0305100f082d060705030a0c02010c0207090b010e040203010b1b0a03020c0d060b18271002030c070803040804090c0c0809 73
    0x31306da101c1c8038101422502c0c030009940e11600e84c4141c90609482c1a82d0b102c0c1c01c200d00042540c091076403030095580c2135035009101c4100b00300c400302400e41e07107108840070300350b0490800c14440200100d440408040d9070104103400d0000700c00b0024901c94010740212521a1418000301c0300015420980c00306910309403221070b80c45008450340d08503500340c1400b40d01500f801d02c640e09038004041c5009040d1301a0412884160100907030807134108030512400b5800032001048414025440896501010305000d0345904a00d03000401300d91003600300d8601041c01140d403c00d610982c0407000441500000107019034a200d881c069510300ca928091031184904240100400100e900428004070025205c5103140310082d110031034040003114509070400c2140002501c91a92034000014480d05002828861001c0845280a507100401030400d01e0341c1040740c040041d050340d00a5204038000c43d002c030740f21810422038409032000400190f023004194040d410101e146041200c1520742e0440b0045030b444 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 736470935 1250 736469685 736469689
    0x70309050a0602240f0610030219020102071e17090316030308061906050406180509070f1403010308030f091507020706090503030c0726100903020c011e0e 68
    0x10005030086a0070820007000010440e80004260381c206803544803e100c0c50915918282c20740c00d0445090000e0200100030481505003e003e10144041c0c500e030241c40d0035551782002040c98200a050342c0141c0d400508038081c003c0701d14840303400343d91502c1c3c1c540176548141c4851a110041e0901c5a11440000038078541654042101c090400c14801e61804401e64034100a000c00c47e041b103079503004542c030284041c0a115030301500d80944a894650509103810f1000072103480b442c05000390080300c2554408107aa0356400700c414818070807540c0d018207080809000402440401d05c00d64102c290600051000691907000d0340d911685101c0400308130f50390f5620007898414039101c1c2d4449d07110500d0070320840035408500e0000f0795916031605d042055550082c1a501e10801710044401e0f0401b00052210342042551030611802c039403010454294030442081c1441b461012100d205a928000001019010304c901001700d1401d08012003110021106c0540040c10304940004001103000009525 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 736472185 1250 736470935 736470947
    0x80f0f01020f0307110a1a0f0f160507110a0b0c0f010509060103020f0301020d2a09120f050f030c030403061103090a06180c0f03061107050a03081003062c0d140703 72
    0x91900a901f0b840c0414060304113004045059803061041d0381184d001840404140d019540500b140081441d20703d43d100354203c039150041392084626201404001103540c2d2400d080002501e42000801c1d558450f200c03566103840600030704000c0310b034148020018644c4020a0700d90440390140d410600038440400000d0080c4030b0541d42000c1c00d45890880b07106000c0252036905c0701d00c0107a00c01d0004404c040001da0316803410784600c00b03001041f5048900081c4945403105081b5204604031810602800d03d92403d6803c4007889080580c404a02001800365a001c2c5250038031000c03074001e145040056000784c46064011000d403a540c0c0b51103003c102d41403212064410940c1210080e960f054864505075000c00207031000350f8259040034504a0010141c00c11114902d0344080200303058200390b035041e503031018001c2c56214102200c500010201e4076501401c000301e01c03804686000a5203940c1404c0d00081980d41c075002990101d50f070700a0090304a251888400c0784d8000d0070741c4038007491a0844d04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 736473435 1250 736472185 736472203
    0x1030603151d1506060706020708030103080c060106080c0307030504031202070812310507050d060b04051605040308091203040312090e0c16050a020a080f0f01020f030711 75
    0x4408403803011960400c10680c0700c25401c2d0804090080c41c0c14a10702000e40c0c039000c50316022000404007002c9501403506a00500080e40314003405400c1009945a500085e0401d0f80103030742620002903150030416003840940d014250f01d090400c0c0ca07090a0440881600000309020705159889011406050045202c00141c40aa0500713540d500f655140c00300e00f54011010108403e100e40021840c80301452402501c1400d80088508482c90b410740111104d00352500162141d010b48000421140c9480801d4955140500004501c00200c041400222140100030a4120311002d0101c03900c0c50f0701004603000ca9030840170003611003800c1c00c0003034dc0891443c400c2d0403082c40006000010400700c0000703c3c11044058461001c0301340c5e1140e024050240131124a06c1c15030003080f80d03000310b00c202e12000810902480854954040039804105020403d4000001540c061130b40888016400c004000095200328020340c1800703a203c0460f80c19010241c000400e1042c44c4030847d0310450304000d00a6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 736474685 1250 736473435 736473443
    0x6030c0f030b01090e030715020903070303031a031f0207020f10020d140a090501033b1002130501080403020f0d05030105040b0f090604020d141806060d0b1501030603 73
    0x28555521105082140c04a200031110810745000010380c54a5901c6480400c810745406989000700568980400d030031a842038002e520b44c20310141242c0d80b01001408091482901c0004d1038659688001084204011615120307038440320300903142d12081105034803e40c907070311030143c0c46504034030014100b403a10750006030300000342031f0b1000043d50740011141074005058442103c0024494084003a500c201010b500200303010410811a551180d40000340039180110340380c6801d84441010928003008946080c008228602c02c030340c090100707010502050801480842c90410001440c4603050007d100d680d05001d1410002002e041c007e11103401e00c000120140c6d10645801403010b04281c20a005146c00b440c0340842084c40ea0a041000103060040289050895550101000065480000841c01c1c0e00d49803202d039140c807611240c0440c05100300142c0700f002c0030200d1400c01d1800f0001001148690405030706c80022503500001660048090034520f514030941c1c10040e005402e003a48028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 736475935 1250 736474685 736474703
    0x1a0d05162d030f090f0b060a1d0601050706020d021303060501080a020a1a0c160e0601051c05071b0302030301290d18080d0e060f01061407021503040c1706040b010b0c010603 76
    0xa8104540058807500c1f85204881d4070b40102d49815448502d1201c04000b01044400d050102d91290f002c1c201600c40c81f0711503140907203400c00341d04100f800c1c0d13040080c4c0550b4802030000d0620400c4801d004a0f8003500c2e03004014075100040c1c7c0c0020750000b90303c2c8199841e107c564226000000006811070307001e90b0b102421513140ca1001c0c10b045410308003601c04c00350b050102102144040d84120110380b01d4907140034403841c0e03050b00314868000415000c0d00314018001780401042c21051002400c0740c00a0180e000340d0748039071511680c80b041c0d90f440c00015a0503044032800d414114400b500340d0f40308040300c00c80007501c904811708500102c06007400c0640701b80008900442140c4660f0045104844014150b44445d1900601c61485007428062800460f003040701044008054401078510640002c12560560f09101e03201026a402900c054400d5000101c00f800309011256100c00780b075142d040148103619143c3c41f448882901801a10288034000078150001202508404080c5400000d48 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 736477185 1250 736475935 736475963
    0x3071211070b0f04060b03010b0904030f0215070504290703120b0607060b040c03110306010c0c03060c200d02030708031f0b0903010f0905071a0d05162d030f09 70
    0x46401003d0442e01112900d08000e241c4203107003010300031044000d102400d03110301c0751590784e4203a406c1003c130400d070300861013101701440c0f12015205e10240a1041c90311400c0d41e903401c00e03030f0314055428100c602c100510440c02c00300315040c4050044980c0150546000d01016040c0d1100c5406080c210305459803100700440c2040901029500c103401d0164211800c2002000101d0290203071040c0d0450b03c0307040c0105200007074013540500c00f0002028492401c0913a0680c40390303a01012070380900402c0e40000d460845440c070464030015440c2855195074000c1c03e0001ca2008000c0d030f00d2040701802041000088003040c03440369800f11103030007441040e510700c207080c0d161000284213801442401d40b00b9801d1041c080040c800b43d1042e95141070304039001e4104a0b0400c1208603401388140040661801c3c01c0000100781e0150303100d458010032465000800300804054002e02d0383c00c010101c0c4901c1e1030100381440709454a0b484100e0080d00030704012a800d41d50218504c02403004210251841c2020800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 736478435 1250 736477185 736477201
    0x1204060f20010b09060f010804080912060a09121b170906281d040902030a0b0a0c090b030c0a080402060d022a0303010b070615030c080606011403071211070b 69
    0x2c040030628050700d284c00300741c0e2014200080806900809800308410078042804218541c1c020710550101410a60f4000c404011785447c15004845860540e40c1e00d584080400510b0303800c10701d4041c02c1740780100c50150254000001c0042500c8010003c3c01240c00800c00e5140b840152004580001d28054899110400020001c902082040c008101c103600b03d16440307002d0841d10f40410b180300201c9090051000071f2000800600000366410302c6080b1880d8001911140010b1080f0400e0700c6c08a038002c0070084c060920501500324540c29401482084003a00c3e00c6e90603980c42c1300b050b140246240d100c03400440da1500c6041c1e01c0c4540d0500014000d400b0803600d5121000000c4085031640140c01c1c84940709440c0e020a00031050550420082030000c9000c5070400000c1e600d0b60714100000310b5503607407140c0d07410072181c1c4103100360303080402003210315a0400407540c0c0b40c0201520440c40c529020300d00818200002c82071030285076035813907645004000781d001d480032540c0c0301201c01110b05207440c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 736479685 1250 736478435 736478441
    0x30804080d09050402040b0406081506160605071e1b05060a0209132f090603070309152a0201090b0c492d06081204060f2001 55
    0xd90781c0046840814002441d007402e208880032601e858a1580c1064182641183c2c030391405000a00e00b55201c6205080c5547c9050082500d400030071240500840c082c60400c040d240d004180b9018008408800c014881e11640b015884014605c0c7c20716030a00c1004100001705403966001c2d0462240c1030030440418400c1e8014400708600f1900c038041081c140c510390303069400b0150354a007410025000000011125018429541508000e2508040c1b90902040d02a041140c3c1100029212443c0c6000e0100001212a0b141c1503d030007802911001c80c94035805902c20301a1a80d183c1400680940f098802c4d40301c92103642d8407100c0a40282003403114000c5540008a000698140502c00c40310300d0010342c8c41c10baa8924003041c0380c150ba2003403900400781031454010403100550300c03076400d5102801409860f4007a04400b503080e031041c42d945131014003240c00e01e4011140b65404019030842c2c104000c01680d086640e0ba24202106c480f012200725208050000006651080c1d103001001c0810190 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 736480935 1250 736479685 736479703
    0x50106050d2f22030213022b0c0e010302130501080a0905030d0c11060906070804020117040f0b010510090b07060b0907050c01050c0930030a050702090a02090114031003080408 77
    0x70f0342c0048034242004521641d401c9031100a503c83c41001e04201d8050407900a420a00d117481040d1b1810640d402c2503000c400044041c451915a9491103c909550004c3e04038585102c280303411401c005030b1900b9495002c811703014290500003c6000900500481c1e041040c0c07040c1d001043d02d071200034902c500d00140104400721004100300f4106800d107082d00190300ba100d5411600104540d13182d000c1c003a1440076010300300740c2c10030104030200b40103000d000c0003160140b80300d0541204207640505040c4000d985c10f1f004075100c1c660510041d00310a40c000031000a0391302980e200d5a8415540c039045000700460307003400f50810649400c0003407035a040000b5245620f0554001d008a40da03030055070100e13100f098104c40c0e120a0b40060f22095a914592004410610180c451110211110118603503080071421400190340087c1030300c21800d15181d00d68100100c0c0000754202010341001800c12405a048000d2500300400010802c4120700d4540d801590042c2500d9940c68985603102d03221304070a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 736482185 1250 736480935 736480957
    0xb040914071a16020a030c140102070501050a0210020d0b270c391e010e0703030206130f0f03051b0718020f0c010c030b010210050106050d2f 62
    0x30800140141060604062103580100ca1071074000f03c0c0c002901103000b80002a0782115501c0c2000c00084e18150450000c2e14045d10491100c00d40400024a4a88203400c4141004802d1244902c0581c00013115035130300285005c09616124005000c170001c00542ca14103512480c0d522501140040c24103c03c0400052000480d18079903c0141c1540c4511130b0401658010100d80300800c40c40304414410300c4081c24881542050210785c3d002a03142c080b02d00c00a150722104c644158540503400d1268105510f1841e024001442c51924040d44582e070081104100745403200c2440c00300903240c200b042e02d040d07014103500c8200c01282401003c0340c210b44944000c3c01c10104000c0102080018100c08440e6841a03110001c0340510030907010303400091a1100c81d410503c00c15907041002c8c018101e403003c0c1039800090107100c14000a190244954540483d54070304401030104681c0701044841c40443c080300800d0344603948101d1010b80b40d04500c64107042d6106100c41c0c2000341640300900704200340f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 736483435 1250 736482185 736482193
    0x306010f080903030109020706020705070906051305010e0f04030c080310090b0306040f11030c3d0203090f0f03010f090b0a060803090906031f050417070519060b040914 74
    0x80d80025280704509988080c9154020b1004000c064420740091141038401c00c03016080403070565520b0701c8c01a054010003800b5032940c0d018484d90600d4000301080e0012000140459454141c0403400c0e101c000e004030000840d880300044c181400395074034142c0a9445030186940b45800b1580101002c000c1c02400368560801c00020190314001803418022904a080d048180c803c0b540c072481880c0c2c0180c800e5030140100c00c400451640c440f0f5420080d260850014801074501c4025034402001040c2506145440e04100600103030b4000144c0d0070480d015034191154610200c0003075255820b01190603450340c2011900440034240c1d421020020344182c0035030a064070761049880582d00c00340a01c0e100c9620034812411180340101c40c440c1c0240b0702406484004000b40001002c0c80f20301022184541e850714240000c10118048a0403a20064420f81c4d04054460b600c0c2a2940d132141c0c072540201c2003090f00c103400e01c031040d8419454601b000744108140c02c89071500c584a11800a050001401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 736484685 1250 736483435 736483457
    0x9060906050c060a2f190503011d090709020c21090f040b0a09090b1f060c08030421020a020312040f03140a02090a0209100e0303180118030602030601 66
    0x4007030000c0d02c4005550001500ca10790302e84201400411304a281e244c140004000700480c1d1400c0220f80c0d1205a01042d041070360703500102c000c500d11050000b004400c01104000412034103c40012410704112820581c1040d6101c00302032034504403c68020340070b03480c4001080303400d0100c0080d05101c4071056091602000c008100003100e24000c1c07114072908a0214a521481460a0b502144c1280c000810440e121030701c0f0a02501200d000e0102150620a4242800700403200300254410040008521541c12820604024011002d5200090407240d0210100d410000b490340c92124240030040e4505150f4450180250f4820113804141d0003400750080f82c560180900d411141940c106012000c0d1382407650307036a1007948205084124182c002c05184600580c0c2d4070701418010012090051303215102a41045000188040e05400740802c80c20107079100c1c0c50100959101680c4203030800108020070340160f80b43c0602d40c010b80c001d145000c0e4003008000071079020314003914080c1e0f110030903c0c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 736485935 1250 736484685 736484687
    0x31115150315010f12051e0304030b1605181c29060312072a05040c0c02010c11040e150708060307032105070204021606050a0c0507170c0d09060906 65
    0x1030280200d0000003080c980505c0342980107241036400c10320503000c9401010590540c2d95920680d007280c0d80c80f07074000040800a000c0c0160300140c0002c060401c180310000c01801c007800702c1c401c05070302e04120320300074110072266550710808140c0d0316509424442040320600d094080d04030420b5900c1408640748070b00c41034010102c401c05100f0703080a401440702070b05580d0040700a800007a01200d18540c1814002005800c1c1702403c0200410061101c280c0340c28001000142c0b02240180b0040101e5000104003503a400a8640d440f9a00003071811820200b210124000e0080c40c0b04084140c03184041c84043c490100d00380d03a12030110b40c0da50441a8072070504040d103074005848094070815001440c030700b13408002e1000711203c4007142011032411070380780d020070180e0f040280404c011140d4103070000284900c0b4050355520400c4404100404100001e01074154040d046000d0040917030300d00d00669010b0303a4022205030f450031320704982d00700282c24402403120000e4080d040c0011035103100050a5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 736487185 1250 736485935 736485973
    0x2010b01021e0c090a15240309030203030402090606040f0e270d0503090715020a0210020c01140f0c0105040c06110c0a14040b060a031a0d020d0311151503 68
    0x8207218030240071800f03030b12010130651000140170001030035914449000c444909540c42c0700245440000303003401c521281c4064400c0d1005100c88024903040030341c8103000a07400300880e0b45c0b055040b00e000c5025261800814054010b5410000b0011080c010105402040080722407055004120640d162504503121205589050000400650189100c3c00388107000304040c40d8010100300c2103c0c07007590b03920005100e840b0440f00724070240c2c1095600c0c1d820340c14001d400c0c280c82d048a000502c95510b5280000700020307101c05400b00c640f140451041c0e10074900000322500d60304601c3c024031003401d290900c2c0d13007103a01600c00c003030208202800c80100c40c40003103901007011030002c01001c60103140c18840c0040b040704502d00b80d4495500c00300020907641e100c002c1d042c1281640d0700040d000e440440140e44440c01c602205100d101e41c52884001070303070340c0340c05000f4480d41454005c40503520036450526041c440312140750002d8080781006028400341184004c202012011a201c1388010b0f030225035a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 736488435 1250 736487185 736487233
    0x90c04061211060c0c0301110309010e010c02030d0e0703060f0b1e01080a020904091a0714190e0d0602160c09050603100b120a0804090b150403030c0305040803030702010b0102 77
    0x420072200b03084001a1400700060010090624165401101104000703400c607440001c0040c0c0c944c0011042c80070400091090b51500e00f8000020080010b102e00007940d03c1c090040301d03d00c45a100c01c0002da8011050201c1d1009545c850f40038040c869818000d1405846461140341c0101092814450000045007200140d020103848220043e103e25100c10080d600c00c10070160099101c1220302d000030280101c0b07440803c1d20741c1008109092903070004003c3c807681082c40b00100b03014810040b003100300344196611660141040c000d6001100041517040b40d813208050075841c40440c00c1d040d4140402c00c001003440c45002c80d0a503043d00c6001c84411a0026117510382c040d0b000079002000e20480d64004111a10010520f00000c109441014601030343c160048a1260011404110100c401d01800340f41400c104c408508030170900c480d00e00325004030b20014040100c0e00e4402d009260044003120040c040310f2059a603a0702c0d20020181c00380290b01c0c2028010300c150202000508850404502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 736489685 1250 736488435 736488443
    0x301030804031104230604151410090506040303110606060a08040f03020330060d0302031e040b162d080f0903030c060f07081e040317090c040612 64
    0x20600741103031900400b4007402c80090341c106640780c11545c8006455589024007070b0030102803503414503040043c00250f800103003048004100007101400030070014100303541142401e41ea18840e5051f00c0c40111101d0650ba441035400540001b804401c0c5603100c2400c1020b561407a0072103e80b5120030007400718500c582c107a010001890100441c6c00665800c0b080507000303000744102c1f400c0002100a09200c003031110390300b209411030750722095891146e588001d0f0380014110390202810b012910043c0d01d074461000b903e00c5440f03100c400009003185003415940508504265035031161038260440d25112000c00042e500d001c54181c2011300c00140b500f040c149194005880b000902c6183c0d255503458002c0d000843d100c0c403060200c0e26050300c04101405413518950f000300164107200914814003c005000c100800c05031800f0041050542c1c00c0784082c03600c0c050700280c05a592818100d4182c04562004591949000180001071a00041d01154203c04070340801c41c142d91180344000001f041d00e0024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 736490935 1250 736489685 736489687
    0x1030e01060f0b0409151a070215040612050a020a020a0b0901090f080c0f0703020a1809061b14030c03061e040e06010f0b040e0c090a080f37080903010906020313030f0503010308 78
    0x1c0181887c1c200980740052000d81061051103114004191070313040b58100d070000954074004040412203e001f515005004a1011403600301000d03402501c51459a01c060558604600818104032096021181c11500140410b80c100c00516050702940d10940c100070b0781e4841d9055240f1401d001140580459500410600120f480c0442c4110700056025103107a0540e6600d84600105440d0700480c0301080510a20805070b02c21400702030548100c81492035560701c0c081c41007018029111003220707084081218000c01a003074011000000310360302e070000c81d003090034458010744000300001c0c000e041c2c0d0080c2011010301511501078001d01c0c0650700c44c018180c00400c0200709c2041e680c80c0180f80050001e0007500005880701d012503c2d005040d00e0350314050740310b60008441582e010240e000003200c000682d0001d8a10192043c0306941011f4025202040018107460140e03825844009440c0e840780040d03440307103449910249007400c1c02d071007134021482c090b8400c88101c0c4a1400c40b07050b00d81c840034813 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 736492185 1250 736490935 736490969
    0x729010e070306080c0a051201020d051e0c040e0a090213020c0a11011b0b180703050c011205010524090d05010b0a0f06020d121404200f0f01030e01060f0b040915 71
    0x31402c2380c040c441c0100c0d55003040f144041c04120701a003031085100d8842002054034800d4a080906070060149903000700912013800284107080030f00b03410000100c004900b0142600003d0058500d00c4014003015100280900355000003086146207603000c1c40014030402010f80c0152880700c8014044a400000d481c001c60000d00910521500b1481c8086d50340203025114103401e150540941007610258000040c4540540c1d01070101035000001a6050016524280c042a14108072811300056001c00c03145202d040b4401000307503075a03018001c7c041310480c0200d0801c04c1c0241610621a4000c2002000201d048a900304c2c006044030000d60040400464010701180c04c0101440652100da4a03940c00c10045901e004805000c1c034007900915807000c280c0742000d0b0400900c10007147c0900103030542e00c13105035a10261544804000c0c01c02045100e506c03210140102403d401425502c0c0c9a8200480c10000e00c00180081c0c50321461f08004d600702c8078901d124283e08901c18140705541007a42 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 736493435 1250 736492185 736492189
    0x315090906070507021c020a0b031b090a05011101091b050109240f02070315020a120b0a121112010903080a09021507080d1b03110903030729010e070306080c0a05 71
    0x6c03080300d4402d503000341c0641005a5000905110551707000011001c408024000704110340c4400300b01c0d03484a03030440d610301101c3c04082103010426208080c10301980d055401841d8000b90072144506500030124260901d5140c4e1003c203280c503601032280024504400418910081281050000034100041041c00100c1c4000c171044820148070f40118040e5040000006441510454200c103400d1b00145e1201214400206004400b22401a0750303810060004410345441d0424401e4689503454402029131a04210070000d034804006c07500101c0903104080c400c8810b50107841298400d5035072200f992607414242c0280c410004d006584144840080c4200b5000900140090b511031025107051442c0e036024802114030340341d91140f181c0070b0754401c0d03c2c00581c1031040c2c0c4034282d1031a510324104048000400d54034021503a00805d0380441410a800700c01644078481c280e0b18111040d00100c0d03031079803009001c0300000d5a01c0c00119040c40c3c3c02050a81c0b01166810002030040d240e00f9640c0d01e0001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 736494685 1250 736493435 736493449
    0x8060f0609070212031e070c1703100b1216080f2205100c09080a0503090f0103270614070e1011011103100f0506071412031509090607050702 62
    0x9a0019032140f01000380a03849200e02840c07043c1003421a4003800104504d001c2c81e91040181f40e40108240440448005600c814054191002080001e500e07546c404818082811054000c20200711000c05c10020312000d4a104502c079103c2680c0d41f15540403405429241504191f6003000c8040d01c500001d008210000c3e20b848000030b4413070721403180c2000c540302c1900b030140c01d0120038045500d07840103c0710b07160009010802840094020036031145642c48850b106e00604e4102803044240d5000c120050b80700c0d4101d00c82070b50b869406002c14417941d0341e82c0e003a500001c80040b01e61174104401c080b4201004003005110750b245445400201c0c02d8941000024101201000240191f118148403825024450303842c1799480041300075624143703092101c0400001750b0040650040154061080351154800e9954160f4000d19115120407030030711040c10810300c854105031440b00842080300e458504c1d10070400421040c2c0d1501266110f56160303580300c0004a5108c8089017040004400500700b6031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 736495935 1250 736494685 736494691
    0x90e1006050d0807060b090a0e0705120d1d090c04060327030e280504050901060807060507081e1b01060302030c011209020603070e0a060e370f0f08060f0609 69
    0x400140c02244000107151f0700e0054850b0300d55a980c942203c1880c080c100714010181400f114083c0501030489115544c40701c00c150344000300f1034100e2640d00303100d03c030581d4100c904200074102035041c50001c02804451b00b00e44034001c002418883c0313219442002d01082000f009d031950080480c2000d44e10180c1e980d174207462115801c262121140320f4500400403003080e01180012095115038501405c100079214040d01103209179161034010842d00100040c0203040b1491818920f03114807250070001140d02480d00303415010090306443c0b0400400e0000104400380c186040a402011920700c06822a08075000c0290150300c94170070941158000c0321130b4496840c44480118000e0220780c0480c015400c2520072801203440201900210324062201c50094400c2d442e10841d4100000300149a0450015424038030a400d9202245251450503061008031000e61107282c00300e40e52190040c6860892082c81c40283c058000850780080209800340a001c1d040c0f0203000c00c2d00e41c03404211940b0380c05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 736497185 1250 736495935 736495943
    0x12180102160e04142401050a17030d1d251203020c010e04021b010603020103050f090a060c1218020102010507052d040e0a0506100309051b03070807090e1006050d0807 73
    0x3c0c0c0d54040b00c0000209003019a17113946022011952508007072142600381504281d0200c415601030710aa04030000540d0380501e034501002c07403810403c50841c040d00042c007a4000f41806082c51a4000401603803016807000c0208841507000c0da41c4000f14000440201c100031b0040e00b00304c103600d245d58400c1c1104907001c140108014501480740c0e004182d200344091049400c1d035115401007042d5038140c071074a80e000c0224a00603040b480c00c0c0c005185c850160210081c00302c2c0d40c0d8004261054424146054004a001c0c400c10840c00030034221500348041c07540c100d005608060000e40f07098403c07401e50b038500341c7c40040c0c2020054100c2c42582c16850b001c0d918507000c40300340000a4070300d0b80e00d00c206014141c00b100004040c1441c5060003104009007400d0000d060928120900140f40000c00c2c42200c0003450701c084508080c000007a04003903a652004955204000020400e08003990041100c2e002d000101e4100d40403000c60341068030030310307c01c0603480300f107100c0080007052440700140070003442 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 736498435 1250 736497185 736497193
    0x2010c0204150b04060305060f04091a04170a0206090d230717030c0a030c08010605030c13080303090d1e21060905040305040302031501180e12180102160e0414 70
    0x65900c00c1d40140c2241e40602c0020787c64a003031001500301110030580000d01500c0c01d001c0e07060291110040418401011302c00061b200f0001000e120038081c0c80058250008034060740c5510705031009544100c01e850000701e50182c0c807031084215000d403450344060343d6107001980d20300c00645441c00d030640000380b0548504000c003244074001080745000310b00c5235900d40e10341a115809100d00904032851840c0720400d020580e001808080d40040a41368842000ca500d160760b201d041c1044540c01a2640c4844d28500c0080306004003c2404110101010f40a641d061035001032182d14500300c0c0481030031a008140c40b04404481c01c0c120000008000d0034880c00800e400b95121606811140101d405800152000c2418400c51600b404910030070b504180004041d5410320120940881d091201c03000e1244d44c460544100c84018089024034800f50b8480c291118603100e09440c62105c0c50350b90074014000e00d07041c4504d8410401551064a601c04401d80703955072280d80d00d10145203140440b00075845 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 736499685 1250 736498435 736498439
    0x813031e0c121e060c02061605090405040302030904060b030106032409051f030b040b150a1e0315050a0c020a080708090a0e07021e03040305120f070f050f06011202010c020415 77
    0xe4803540481d0b40c601c19140042d114400c171800a0815102500e482c640c64250919066031560002c140c4091007000c803000901c5851b50b00c1c050f499440740c02c46490700541032900c00290b10803251b0103181201c0c0c51f0b0701d00f40426815494a042c0442c134148228990b180c00090600000301035501455000c0b54906106064542000400034260ba150f403040f00c140a10004000802402261498000022400d00001000c0341c100040e101009400385007000e04d0003003e05540c0d848030703501a90003150084045100e842080414801404007200c034081498145482c0e40c81b01807000940380c607860b81000c541406e00035075645040301750f171241580b0790b402a145000031a00b941c010340024041e4920b60000c0c00c840701d100c500140b282400d441003505c2034005200404c003194001c5198102c8600c4400c046655213905174001050307004100c000303027880001a400804000c2d0010b81800c0c0f40a03050101c69480e80d8403400e00c90903602c1e01740024001540a01d040c2c0040c249034001680684c050f41041034460303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 736500935 1250 736499685 736499723
    0x5030304030f020411030402010c1101050d0f1d1203360a05010e0736020309160923041401050c07030e0609061207020a0813031e0c12 59
    0x1800c1600280c4000c1a95040340c011440c0138801d24030484000e900907800c600c0c203600060320114480001505000403a1400c0100d62304c240e0450f14035588000d4104240780501c0042c030018800c0e004c07060300244089149041d007400024401c1c9000c110040b2039450750340c80400c079008400d609828001c0301c0200d4500c0c4080c881c80c0807070303801c8900080f130002d00e01010780341013443c21b5403822003429007540c00c990300070b022408071140340c0100440301da114054407241c40350307156040c0d9014030f011803030a510110510031085004200125100701d07004058100640302e040c400119120146143c080d1100080340310300f21400e4200f0380703a01c00c0c001c50881c00342c005c8050486007035500480303051191100019820302015000391a21001007010b40d20b6134208908500442c00c14422041d41d80300407045a0000b81c0c10074803c200c078500d09544800e44a4441c1500061501100e0003030200703c490f966001070780a001d1044d1b03003030350a6440c1c1041d100c0d1341e0f262802d02074200e5110405802d841d02c425201a5040403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 736502185 1250 736500935 736500937
    0x1812070e07050d3b190f050706090506071217070e1306080d2304030305040911031b1c02040821030f0609070e030a110a0803070804090207030504050303 67
    0x41a294071242e40d10303850740200c071049440703401d60440c4c40d044681ca0f800010440c0002c241c038003242e16002c03058075508070250503c0e100e19500c2c0007141c03581c07601c00d80d8100880d21601c41205031150088455864882d24103070740082881c001e89400a106001c410040342010340050710b80041810312148501e500603c941944d8411110a40414594a40c81c0d003241096070b59200c0d54a104641000140d080840c03003500c2e003141c10700220406c00030100000b180803401d1300e08900c03094046040b954580d0740c3d14002d041c90308140b14440246240002e02014500d844040b00e00c5242c40e51110440b60464074020004c68100441e4000700c036103600f482c0810082144003d02c080c100300d8000380144001c501034200001c0f509540101d4498042c001e00a0301030a03041019000319048540c0b0055580351282140c07a2020b801d403540d850322030004004140528503414488a0b04242c2d040880070b0340f82c0400303d54034460610010321004041100304240341c1c403640a4000a4820702e05145032a40d00c40000c3c0c61 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 736503435 1250 736502185 736502191
    0x40f0b10050f0303090105030402150c1b04050a0b060901030f0e07120c06091211150706090302060f0c0a050c0c0a030c0905070804080702010e180106170a021812070e 73
    0x2080100100380810324111649103000d02d011030046240c5480310340003c0150002a00003402440400c3c100c82c41e42010f182980d20b100042002ca601507803c0c8542004000418020503000d20725210205038202018000c1140c0010042c101d0347ca0202181c00460091406060240b40f41d80d8902e56280448402e0001c800207044401700f00010710840c0c00d00c0803031001c581d8004420310120342e108100c03d040d40d152611150340c020380c9140000703904001184443e04400c0801d03611a10001d4440100501d550040854030302a030308031045540c0c0c402c9035150420040c0e41d0b51414003001e2000d030100c3e5118030010044100e0107002d4544040844c0086031074022180c0084601c09800207050020007030f207104941d400141380c41d114502e820075441e9821148a8442d010f810800c0d41e000c00341c15921442607020b090410601603901560b5140317070081c00004203c03a031085205110011414840e194002d503508404800c9090904404240c02c00840309182003000368640034000c00010354003012096988 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 736504685 1250 736503435 736503451
    0x1214070b0706060e06240409110408060a06030506130507050a030c1a0a0e010f1808060a0b01030506060307030513050a0309060917060411041503060b2115040f0b 71
    0x180721074591030030310281c5920380c001400d0502c0c090704215959640020506000e00249803000d41d40030b952252001e1442250008403400e4146191180020028402002210b0044081d41c4441d114400c10000350ba5081c803015240358014004501c20610844244035024455403c590015594070b010900c684026407080c0c1b000c0c01488010401e1382510048244e802c40c941081528052010402401400c01c0d07076001410854200840c0010f01d001c0c10144800030007c20114103146c2c0d4582440c4da80e02003c0340c1d0003262600340300b900036880d4004e000b0507010303441c01042d850a5981e42d1500b2001400018103030b00090103d086130002217a003c0c4400d00c0454001d40d10f4220450034124064030f2000f10f5403185040c080c82c00200a00e0300d60118000c0c2e000740d0b000042803000641000060b0141620300d407201090b40c0c14440c00000c0140540c400703c10050103403003118412101c18444400c004640c40d0400450300030800c1c961200b80c048444503802480350170074400ca0082070722046500d200032030b0300315 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 736505935 1250 736504685 736504687
    0x306020307031b05030c130e18070504060b030402060306010c0b2e081f0e010c0201020d0c080f0f06030a0c03030e18010f1412011103040c0e0606041214070b 69
    0x1241640e49400740f459408030001d140852610007000043c07861000a00303c10385944007203130b008000e00310320140e4802401d102c240710070981000310004a050303458070b00d8006603214251000589003400e00501044500c00300d440b90465603140c0a0084690000300043d040140e080c000d58002410a22114021003080c22003090782c450104440d8215001c6412200c1e40d03000e03483c1c0030004c01c0c100048050000b403204580380c40711300700342c1008000307010062503003015542001a403092299056020b0240ea46502c0b0060140300c90300074007030318403010594003034650104003000500e0003000214959048207001e002c0751301445aa032100040d001507500200c000621403005214503203442e543c80032051250b0010034150f5454501003210501d420720072141d0b010a6002c0c100f6090395805a000d101c030304002e00031b01c03100c129441035a50a510446084400001d10240403607660038884c24948640c1c4042c114518042c10101c2c0b13019031100b140d4049407c5a000c030100c2185407020311080000f040c0c0c1c04101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 736507185 1250 736505935 736505941
    0xc010e19050706170c160c080f0c100c0206031005060d0506030d03110a0c031404081e0a0c05010e04021c0c1418010c020324100b131a120103060203 65
    0xd041c404150b01010400480e01804c0b80000c182c2504140c011340e80010f925a598240c01c400100842c00c8800070740500805080094075520116050541d01800c005858402030780504200f4025100744110001640703824a00e401420a20700658126111001000b035081e901c40c00079007070b540904003c140301d40c1c43c0c00c02e0009504080103204041c003000d080a00ca4280700e010400454040c3c2c0000c01c00700034800042e842410b01504000a404803e0788071a6605d40d15440301594800302c40c00180c0308004500488180c2d01c8002c0307990310704254020007c00440e031601c0300440fa003061400b43d460307009034200020341020108070000055844080700c0445d83c1100000041d088004180d43e030b55201c00200407511905449110071400541c0900300b4406040caa4000309181254095070000900744915290803000400242188aa4a0343e48800162038541c44000024024020600b080c0c0450300703824001e10131000803902d040c00a00018030300381030f40704103d41c40301c40082e07009444883d400400c3c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 736508435 1250 736507185 736507193
    0x303090d08040c0b1c2a1b060b0604031407080d0c030f0305071e171014040f1d06040b0105041b12020d020409060f0801090309090b01031b020606040606110c04020c010e19 75
    0x518107080c6460304207003444141380c1d0340e2a4500780094a0042248d542c2d00020354807030341c03503000759006180c00c40c0f41910840484401d140c0d59030040d00499120f807046580e00c15a10b8401d0820100159069551080810015030242c0107031401800500510011078030b07074010b0203c1003070340e0300107003075240d0381d50003501d4082d43d0b002091701014010741701d1402818001e00c0007035000f0815401100d400e8500060400d600010076000700240e1118061180c0603030403000290900055050049005a00200f8141da071101000200c40c1c42c0b4450110720000291030540d4180125071034940c00c45030315000f41c80c1c8800521000126030003038001e008096074401083c8906901905030f0005000900020064050603071000303000c1080600c01c0e01041c60b121500300da080d900c00d8000c0391300304d484441c8165420070311001c043c0d1204030448105004a190440c0010400d10420500214200070400b07890342401182c14400a0b40c0650b080480c0b079034a407251101800e0041001e0307100380c0d20390503442404614a1034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 736509685 1250 736508435 736508501
    0x705012003012603120108060103030f02190b15122112010b0a050f030a0204030302060907060914060c0d020109021e030d030e1005090303090d08040c0b1c 68
    0x358a04034410240018480c1d1400c3c1190081d0406564143c8003003812514411840c602c15100894131201364403000040c011000a5080c0c1a24840c0d10f130100e2440300032a040380d0340c0210031542e0442d207000c000d10390003081040300c0007a0400c00d00300180d02c0350a005000301c0d2410020800d82030135580406046101c01052000c10b819015940200c24505001c80f0450104001c0c10f010b240319480000903c12840382c01801265010350110011a441e480c003d2062802034020340b100327401502882000504884020038010141c411903116800c03254100f0107409030005d020806250000d00800c42c24005603400c10622041c08855400070900100c80c0c410301c1420142c00002000300051076800c203c06d0740e00480c02c40400a00303403500185903111005050316218603000b40384c40c0749103814184010490302000561080c1c060404a8a00c00e513000002c4455440886000c0e000104c906410301411241074003d1403400c80d18540085001d60310b42c0380200b00c50010700101d41000d207501019002488844e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 736510791 1106 736509685 736509731
    0x30f030201091104021204121803060501051206160810030803042a030809040507090e010824190b03010e031c1407050d02130506070501 60
    0x1090180c001c081c582c000b500c11181c048441105401c0c907008440a00030201150003284d9555100d5082007494003540004000c6240369045940302d00324141406540209800201c552500c81006a0030343c105540d05a01c0e0880800c0028001071090842400401c60428054980d90881442021085500028184900841400140843e0807080c3d000d50b81c6002038055106540c03c10b00081c10354138440204101010001d012060825410603904840b45041c40c02101d501c030b54030741c4181a0700360480402a486000b04e005c07510700704025003a2162844142c0c0780e8500b4503620719803000505040401c0f080c0d0301c400c180340c09034400b50300003003081c40158152601c0e0492200d0403081828220302c807500e014205802042c0b0000000340403401680c480e22424903026001081c0406900412035142840d101c500001456880e90030082c50414421000029036800c1c8076454080e041401d = true := by decide +kernel

theorem cover : BRFrame.Cov 736330935 736510791 := by
  have h0 := BRFrame.cov_init 736330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 736330935 ≤ n) (h2 : n < 736510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
