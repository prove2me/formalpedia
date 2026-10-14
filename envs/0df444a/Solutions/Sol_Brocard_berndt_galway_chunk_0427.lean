-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0427
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:45:35.805436+00:00
-- url     : https://prove2.me/submissions/f5724cbd-1994-4375-986f-0dd47d089321

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 76618706 ≤ n < 76798563 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 76619956 1250 76618706 76618739
    0xc010c09030b150d02010e04061d09010615021c09031e03080a060b12040f0b04110f0105070503030f04020a080a060203090d0c02010c080919140102010c0306121b0b040807 75
    0x96501041c1c00d01815a507500c881030044c00d80a00e40002c2000704480420020071180d0412082d200400030030244034a00240c0340f80c0700e941044000d111181c1d48a095843c00007510080b4405070308820700400c040e8250301c240c1d41d404003040c640b001129a6a88070715590703c0c1104001c40501501500c001c0900d07801403042070700040c1c1540704005240c600381043c820b84c000c803000c000c1400440000700e0103128141112041d0190000d118044500303092800010320136070303002c11500031030300860106010340c01002610181c0c1e420030301851a542c4d40241340e0900080003042264842086403000c242d0860400c8800c004a108820050b40d90030701c00d40040ca0941105100810002142603a00050340d1000004a10ba9401400c00f80c40d95080c07000940c0c6d070042c5d00014500d030003404200040041d440f2200300160038082e0000c1111841d10907080702a550940103805007040c2007a000c03c0000c5070404002201a00ca55204482607211074003210305611590124090340d0000c44184494100fa000010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 76621206 1250 76619956 76619971
    0xf1a13060c020d020307140c2101050604050c03040b09120d14060a060c1506090c050301060305071d060c010209040603141911060313050d030f0f02130e0405030c010c09030b 76
    0xd0041c200e01c43c000d64030721400000a011060720b040144100c14104501000050010445001c898200d1104006029007500a484942c00e16020034140d0400e481218018000c850304186556074546071612380140140034404240704260611071015890340c09003508040140c8c0101d0f24442c9010488115103014003807a12404c03c01e1000c1241540112481c540309034099450f401034045a1100d900802050344580d562505014100100c41c0d031110089d0706840c4180c4082201761500b010480b0240302e450b400a019180b001da0030601843d2000c094990348080c04009454800300d000881d0603949140c3c4120380130405075001082c1084103200540c03401c030303150044084402080c1c17220400544903201140c001d2030008041141c03011048001303540d40c0c5d08041200d41e120302c1500004c0017050380b507582c440c00328506015a158881e2600854010850f01c0440d884a0390600380f4410119001a1040350640f100b000103001000f8203001e41203030101c050301c500048034030f907040c50302d840400200400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 76622456 1250 76621206 76621213
    0x18180a0606050309100b0a0803030702060109140402030c040f15080f0c01021506011d0904110a05010302091302090105071a01080d050406080403120f1a03070f120f1a13060c02 77
    0x510044c1c00115080300a260000201d1040110808107003c00ca9a0b0402030071408000104a92540c00140140c101c0b0351942c420010080c009420700030300768058800075816001800914030514040e00100700c2c2c6a55503030b00007001e4400f5860000000b4403980018004d41000440c20501d0400703001c4001d02c41000c0c00036001d841400d1009440e00c00004210038140004140070240409103a490316405100180c1040c65500303180c20240080d40b002c140d6a8802c01d48120003003802c0d4464001c0da2204038000e841d040309030b1a600b1080c00a03401641c2c04504001c7c1c21300c441c43c041040d810b46e0089921152030104090350411320701c0e5040000b14901c2c0f00c20320504110070400a64482d0350182d00640600d4900c5103881c00709103140c09808020202030440342860903020320b01100182c041d918440031803c440140c1d56642c00c401161116229030501c0c00c4900c09030802250040c00c00317220062117190a400c2d0140264240c205240c020303a3f600b2580166988210700b0850700d4402c003d02d00c502c42c0001c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 76623706 1250 76622456 76622461
    0x9050c0301021630050c010507050a02070306020903030d021b06010603151403120a020705090f01030302150907050301050406050a140103050303070c08130602160b09060301050618180a06060503 85
    0xd4103d4010400380106224901c2c86224112034060041c00309040148030101c03040b1a0920300101180c100c2140416103501c3c0c60041009a80901d003203e103002401c6e00500802465a02c40030003e412020701a46c150204010040c11042d2520040c0107091f4146010300751404002c141505d8298142c00a00505180001150071198109406000c85100903004400210b02201280c20700c844200d01c2002480081000c050640d000724910f015120152189070265131b803900940c030614804c0c840900540c01216035040b001c0f141018290b4403141880441d0205035980c0302090840728226026101903170343e07905100c8001614060b604104009010500e155415612884d440f880068803080501c0081000d46c0c1c01c1200500949110200c000b070390706031650f84c130b0002175203810031500104243c69010902140c1c00280c0b0045c1d540303441d005410301d03085a00b80400d004080c0d005074032502803038140900e600015035a428600f1252900e0440d60321a60400e80411005d031410f42c2c0049044c8031081c401c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 76624956 1250 76623706 76623727
    0x41b0905040809150714030c010b040b060a0c0f0c030302010c09060507050d0e120a0809030f19020906120d020106060e1804020d1a04060903021506090a0e010f0204030609050c030102 80
    0x15030f03808035030848142019a4070342c11500801e00c14a40f0050501a501c110380c000d000022001c0c0440c0700d003e00007071141403901400c110071549050710b4285c0c0010140075482c6418828002c0000280c8202400507100031980c849005680303182d0310440041c3c0d183c80003004c00640c071050300d00042c0b0660030120305012055171030701e0b114010150303014100710003801c04920640d15401c0005c4507d0039036056a07007912890070304690035800810301034068440c0b2007000c523811034002110f00c9000d011407031811450155500700610703160050805a07105030745007032280100d982441130201c0340045400000d07420785442401340840c1461910144524202d070211040c1d00101080154007541c11a0f41c210146e50702d1401c1c13a2400c1e030341c40c0302d6010703460240200f0080104603400080c50500039022561041020120071400e9070301181d0070364100700c5110108403d140140c001d42c2c2518007400001c100c0c81e000c022040100d8210790700030740381d183d10748408a007400030a108240c800d680030fa0003545009603111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 76626206 1250 76624956 76624973
    0x803090c0301060b091f0e04060801020706051f0b0f0d05070e01181505131203050301030b060f060703030b03100516120b010806100c051603060b010305220f0803041b090504 76
    0x410a0200030b07818a115652840f1f17035a0211042002403040140c2a1544c100358002d4200700c0045510324074107808614801d8884802c00d03200406036110005850030003003810344607048a413034010320a40a021040480f1091f014481c0b08a5950359040300c440000c00004118240f00729403c11044036005081c800180c3c03420343c0340307040b10203820701c681d1341c9400028220304042191701c82e01c880c100d010500740400d54028020360481c2d000704d012200340e8a42c6000c100e410303240704880d903601440400001000034020f41140c41c5816005040e5500c1c0708a04e00c0d210180c550855001c20442400350024041603000700c042200303628088000c10151a4920000e0000003000d003465104410300b000310a14503100e0485800030b80c0c0e11000f500c00400450314450f61403501400704803040c034248800d84200354428440c25108a88410605424465080c3ca41e802c010035040203450110184e41b118021507000b40c0250b008038860106005400f103006014514450542c001803d190f0034602448085507208 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 76627456 1250 76626206 76626229
    0xc04050c030106030902130e06070f020d080f040201050d06060e03010f0b090c030c1e030106030e01020c060f090a05030301031a13050c01050f041701090606060507030c06020708070803090c0301060b09 88
    0x9080004803600140000387c5141001213032070414600b000801c08246001046d2036010344400d880305c808250501d58141d031210000285c0c0e02c00540d80340c0c006401c1250418034550060300606080d80741c6449030002d0801d45103241c0040010a0540c50204801d0800344a842002d00c04140108002c000c8100081d41101000d4104800c00401101107886102494101d07464100c000d501c0003291440ba030404855a04244140c0c804241b600b62203100d203003818000c5440b50a500c1d005090595a56940f0300004e94002e004224580f040184180c0080c2c01000294040c5000c3c5c030445800030400106241c0c10240141040c4545450700302030000290001417444410600f400c0142d19541001181005030085500122800401c40072940001300194005c8861500448090000071746422040d5100d201c1c1c810000c000454048015000c540c0c25806425030f544211100c0b442c16043c1d0b2103043c0c0c940c006952101da6a004282d02d5102c6141c2407141c54000c019401006050043c50340018071100d40c81d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 76628706 1250 76627456 76627469
    0x1511030706090201030212040c06020709020c0d0804030909063201020304060e0105070f12030e0303090d050d0207021512090a08090d1703070f090b0c07050d05012304050c04050c0301 80
    0x4960442c411680a601a980c2d80b080c4424825010300e0941000e90754181c0a21405000d40603120002c142416140222001d89044200402511260700c001316044000240181d040050f0f542010580d20501e004550040010b003051504000c00781c86400d2840c1c440741414030390180f00c0c10100d1900c0e40c01005540444025040c82c8910b1001100103807024811400c3c0204580c2120160404108010001c0c0c5080700481e1703800c000c00c022000401c0c1e80c911041c0e0303400059500ca521407560140c1729030f008001d4005400405802e28103280d0102d62840c8100701c03144456100860041c0340300d00071002041e8050301c2e003002860185a26110702c00d10b84110b8000c28012140441d00700c003409140200c0001c4207405400c0340e075592402900040c80e4844550319400001c070b140c00005800d284a10540d01c41794110780140c26420701d80307010410222000340c002c40302d40d500c50811030030111200c0c074032065403000310310000860300d014500a400c0c4402e011649110303034948401d024040e0560020703241910301c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 76629956 1250 76628706 76628711
    0x10b040c02070e100905040b0f09010c080606070507080601080d020d03050717060616050309040f090519050f030403050c040501050103020a080414010b03030f09010305010509010b0a03020913151511030706 90
    0x2d0f80803801d52646005d4004108003030a000c00d0104011507001814030400460480d1071458517400c1c3e925080c1c80e545a441000070700c0b801e020402d2450700c0f4001b0842588201c0c01c44812607502c40f0320300e003841c030240e22070001500800c1304c07500e000340c0502c1101c000c00240d20b000c018034908620b0107403051200002640070300108900250194076804110340c1c400d1018601e6205080852800c19503070303403052100034010760070300384400c00d07032003050044c028440e0f4484068040c690a042c6000704280b4055805c0c0c507281300f0720009004210080c4001d00165024002401349030301c2e0703030061105840303069002030f04041c030410858004a6002c10340ca500607a04c81d00070080c060080003000e000d04510041d441d814000001c1000c142561140100060f042c01c1c1c9060055a990314204a085c810910546001070f0b03042084000880c4698003c00340f20400803c07560044210100d01002c072042c2070003146401031400c40c00d00a0781520300000c05440024600611401564121280c80b8052000001c103043d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 76631206 1250 76629956 76629961
    0x40c0f0e0403120c0e04021c0e03041a09010201020403022101051e071409041503051b06030415061d07080109020a090b0d110c071503090c030318030203031b010b040c02070e 76
    0x905ca484030041c0004014001d54648200840d0228441c52010790400203a103006011100c410b408030540e001c9030280d404829083c4111803000307609522007074026045540c04c10000c00140d55200002d03400f262820342c500c44000c8116422070840d5000b4182180d0000d801c2c3d0f5051194071440c401962000d46da00c0c1c0000500c0c83d00040e10704502600484541c42400c100380c038a685d482c014011801c807401002101c0000412840351600068031084454000300c04100240c003080340f40882070510544036100040031a43d600318a50880b2070001040390003207500e414408491b910920355409403417144011490a003200318098205100c51160700c0c1c0c007102c0800d0741c014a0302c01d42d104554240110300b074260341d20004030780319454440d00c0c002c503e550094043c002c141c3e58803e1048018441d13011f000018194210b8909a401c02411084446101c680303503404030041e2428405081d00300d140e5070680140401140c1d246082d10710308a10b9500483c50f04c0d404450b00c41c1e000503220f044980b1002c6569094 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 76632456 1250 76631206 76631231
    0x70504030f030c06090501020d090611090a05090c070b190b040614010309140f011409120409051305100b18060a0603020a0207090c090509010e100302060a02030d05040c0f0e040312 79
    0x244000d0b85d01408552010415112401140d040054042d1082c1400c2108400d6410660f4060141240303541e00110111400d00007406c203924059046050301c9003003410038450b542c0c2c00071130690072202080080c540c0210b42c0c03a030000b1030142003003000301214140002070900f038800c2d03500b58002104c0b0b0b040503100c600c0d4809116190141030f44440070202600c1c00c4444040300030b4007034101000b40a40c0403c0d500c00050f1503d001007500c090b41032007281080d07e424a0814803c015000c09092441400c1182d80803200007241045111803c901109001c200300c0080c404100c488510010644010a0003000700b0407142c0d201080401034441e0360400503181d904900d401c03450441c441d004120303001c0c9807100314040700b90400c1100d81140e40c119802c1d80560307212811101d0075841540d1500d0842c43c100411700c014605070010748581503c0d0701c1181d0814a101e550b04c1c080d41c0054800b031361021017650081c8100c0e801c1d801040090b004018070450343d82032030358004250500d504030040200350b4416080307540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 76633706 1250 76632456 76632461
    0x10e011b0203060430050d0f0608011d0f0109050303040f1a010803190c15111e07110301020f04090903090306060e0f06030705010e06070c0905040515070504030f030c06 74
    0x20030381c0240480d9a1880e0614240e9146902d0001581c4003c50025030b24407075503a08400c1c2004a4501d0f5245803e100c0d0300210400a84030390741e40c0540c1d03141c442c0400b1032807031400d105820100140200c0100700311108110282009407810030007289074108051400819000411250001d81c44000307001500943c2c1400c04a40b549100001806c100c24400007840c1c0600002820999405910350101c1c3e04441c48281c0e0f4039802802c008140c0003070003081c20049005680a08030b4000d1700400070746050061103c000d80d68200001c1e000b07035948041444d4040c003800120420b04014160000c41ca0150030f0310310f807040740c080d0f031050175a031503220b482d42c9040500c150603000066511800500c1400e850342d244880440c0c04942036201108000c0001d1460302d40050124100c40041c1c45107005400000240400317940720500555032040007410020300051a40301c0c0901c6540114081c000401d101d4460416075000500700808100701800700340081030740f10b03150704039885e45401c0200300b846091130101b01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 76634956 1250 76633706 76633757
    0xc011d03060708101202011b03140a020102070b0a050114120106050d03050a081308030a02090a0f060305011d01080601210f0c15020703081206010507060603110906090402010e01 78
    0x105070041c0c00a100c589a04414a103000301c521389080c001c002d4076440504400c84000c1000790004400a0101030601c40c00c40040400e24003034030302050f01c8581e844d100d409960201c0c08920044c0e50005003402070040e8841d9040d004890008203000300e5240100760764092168811441c0f1481c002c001c40002d61209501100060a000e001200308003142d04024010b03410400304040414070380400a50003102402d082c1c1d85c07190340101c2950454481c0a030402c002d40015802981000e4200c02c00305808449101140080c20160b4011131a503040c14038030002c0140c40c524401c011100c080060094103804284541550510680580000300070641002800c452603c080e068046480041c401e00c000c650341c10040d18620094500d40e403001820490761032059102c068440c402c02e202d0031504d000e80100a80c1c202d0414944541886070f51740b41c04045450341c2d030088a8400c0072080d80009030518584240e44070b0412105241c903860300d038001030b043c2184040c0460402850243c4020004c040300d11280 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 76636206 1250 76634956 76634959
    0xa020f0a09060e01031110082205120304060b1005040614160f05120c03040915031407060e0406050310090602040807031a060301050615031009020a050a180501020c011d 74
    0xc0400c0e83e07a41c3c00030304203c081c08240c4a0f01800c80d040131540c01c1060000c5441c1c1c1e99a0390316003e940d602410030004044035602c0f14414010400e940c408507400300084800b100c44054016940d040c1440d00b541221600040c05000381d9100104041c0250001c0c1a00d00715410f03418000002130019541684600c0385503144405031003880f00d007070148501101410900c600c21011030780e5001c1042c1a21080e4000c41d2000185030380100310074001e00e02c2380d400940c810301188210b0118542c9030382d15040220341c3c1d03c0307000322290b20000d01080582d5001040419080b016a82081500d0821000c40c0d100e8114000800e442d50b00c2d40508400c20810303034100c50040001500b601c2d1156120f261130015240c01411070890864a400403500618040c0b1449015050041c00110f40b00441a80c84a040d0401008100f003900c00c200006110a0103000908200e04941c1d03c43ea070ba59071005003e003000d520500180003100710a40140510798002450690008090030720703980030114103001006003526034580750f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 76637456 1250 76636206 76636211
    0xc1014180316030302091018031104020f03190506090f04031803020a0902040501090902030c1204030309121707090e060d0609080708090a1703120c0c06090601051002010501080a020f0a09 82
    0xb40300341545070303002d424040c81c111380994046820603c122401041f1824841002d00d412004000040e045102c0301d044082c0a400907082c0703200c0f4003041065800c00c03075000f2110103000407980c425010510906070300c81e81c119031b110254188a40034410240740140300034288961400700a8424801c4d15480d401158014026900303a07407640c03800e03070107174001f0700c00c1a0108804e08400b140c203204a009407803140c0040030542e403c3c000c100100d0a8542c0c2c0150065081c103556040210105141203100109651a078880701c0c0c0546103800c00d0410824014507050402c020720000b4081c01d401d01541903040710003100c255042c0b000908010300209420303c0b0083c18104001814001c0250941c003070304982c0d404880410160f9911a800c82202d0140c2e440c10a168104100f13000d001218100c00640101c600b00c0141d0800040180b0207140c6030003965850026840034004000c00d141204150103e11494070003440a54507000400742d560825280013481600044c03110801605d07051740c484c0040440c060b09 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 76638706 1250 76637456 76637497
    0x1a090c030607050c07090204080d050f0f0d0c091202010c02010f210b0301060807030309031509051b03191a070c0c141c0b070c020301020d02040b0c10141803 69
    0x900780307912020b460b8481c1e0154170000038040e60309100b074604444440028249010222400b1a940c0c1d02070392030a4003030b007800e01114604541ba0b40160030001001000029451100d0002a01e40f298a600441c055032400c04c0303007030050340d01030450b41c081942800c112164000d06e0609545501e1200803141d001413164080d4190050b06400010082000384c00030890faa032101c1307009840e08202e00010f00498240170301040003941c2c1c01c005041c6070254440004100c1c4883d502c49042039100c000f5000c0b5016002d64410f0f0724542401060b88071481500c00c006140319a82d984029200b801401034905404400054a0765008005554003554400c0de0400000d4644450380241d61076000e6490042c0c012045489182400c80c1c43d4074440d40d0003c0c103d00c8242d55518013140d00c00070304c0000701e130955001d1202c03400340074583c0007800c0a006107114407515240a101c0a03482c0840350b080c801d161504001c1400642c00703038000c1c03498002049030617900c00c2c0c24000d12468a07500c01c0600780f49070340002584 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 76639956 1250 76638706 76638721
    0x60b0d1a090103320f0a0b060324100b0f0304032c010e0d050102120415090b010e040201090e090318030c0a0b0d060302030a08040e0f10140d0807060902120a1a090c0306 74
    0x9402068500c90a0240c047d03454910500da40c901c00720b07212840b004481350106513007000441241da0f01549000f0b0000700140c40308070440e00f6402c45111003c03000c0010013071204164004944245032007140441641030709181485040345001016224103010301c0346c0c0f0f49003a90301c81801042c1ca40d40c02500a550701e903106440c111805900700d80649980d500300600e464040c40d907000306002a41c001464460b2642481100344100c400604100d06002000e80001414603014026610030345466000c1d40c1c44101d580b21030400c05100f29501e51003504103001214680d03913004086803c3c2c0c1c0e40c0045090702c43c039030005c12034001d02c215080030394540b04010740030082054420050080d9018031103903038055118031000544494080c0c038080084401e00c42c0c14003010210170003c514510303000301a0b14443c45613840704011940070340010b480e1140c41d03860b02d00035030400d07601756040c21844000401c540559510742031440004070626100e10401180420015102001039041c5c0e107200400365203440c102041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 76641206 1250 76639956 76639963
    0x30403020916090e090a050d09060207080a020a0902071a0903031608040f03142122080403030e0f03010e0109050d030b031002030703060b0d1a090103320f 68
    0x40100e00c10301c44103000941450303000010140302000d0f81c640b0b02036142444903184101000030800c0c0d40c02d100d074846030b0000c110204038175803440c1095110541c141d03003840402030802d42680c00900300d40e8003a8001c440140c40d80c040102c221045400010b03181c1d007562804503000172408810f50b800110020512205100c0400190f0140c0c200720000401c05890400541382c4e014111005080c440750101c4000109001d0300e8001d0241e03001b031503100d00d40388007103e000410312010840c0d100c041e04250108503c40d48041c8001c1034407104104507000700061940e4144040c41140070042c10880d2501c2c1c00304481d11a100070081c101070080082c840018041d01c214024240704809441c10b04c50a040545203500903c6208a00ba00c060041c0c244000c0614601d0007079400645658205942c070300b4005484a8010f001e000072050010700440d00c041c0c04405010444200c1928a110b4003552004000284140c8481039003444070428001401c1c1d502101c402400b400092240d01901a10950130710035007021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 76642456 1250 76641206 76641209
    0x31602010b0a27050910050601050910031401080a05120a0207090e060a05011401021902121e010e01110403120309050102160b0109060803070b040f050709021809040302030a0e040f05090304 83
    0x101003441c030105504a0b441521070645c0d941c161a008440800d05001c800d07000703541c0c00813040c14020300c0d060a040c0850803500c9403d106000081d6648000320607a88403010480c01000c824009094284241d250140c80d007080760703142840c5040000f00503032040c0c020701680d001082d04403010403030310051a4415840b980100e5840c00309524010020070342022402c1c1c00c5280e904103900802041e14400e5030141c584078900c0c8103a03442012952070351a84003003088420072031b80c0561440012410f40717501e400d080d5003019070084842d0341854009400c0710f43d040f003542d040325004503100000f800c0d0390300c041e00100100c00000d04554000542070850328030004501c10942e100b46184440c581eaa40501c10448096004060180e003041107814041001c14207170319045802a4000d502003015039070352915280d280c0d8440ba00c0f00d5008155070006414288483c05090000d4440303640d5442c165a0003074581c440c41301d4800500c0481982c041054550340d03c0f0502c0036807120310800c694180b1840066603071b0481d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 76643706 1250 76642456 76642499
    0x6020a0f031506021c03060b0c071a03060102060f041b141302031017030415031b0309020906011101020c03130905010b0f1213120e03160803031602010b0a 68
    0x30040008480d8118850307a400f111115800b504500303007102c3e80400c2c0d40203401101c0d8201500c540f00810001c01082c003d2100b00d00c000002c01c071f141c4c07904500090049100404080102d03040c41000f4941c0d1f004580c165101c0050030040155a45a2405407a0f20347e00c8003002801076250308007c00d40c04080b284040341210304854986e03c048207881d4410982c4011168910701d60309a0204110500d600e49904420500381004d81c2e00740758507218008040802c000b03090340041e07211208a418041d8402c00555044d955141c20312003a800c1d40c01042d007810000d8990380c1005444403440c0c505c00400e5042d19501d01c940800d60b46d0754070380003043c6030703c3c2d040900134281001e141c5070001448908040403a08401e42401c4a031703043c240c8603412030040740001030400d800303a1807209104000841118a075480340310300c1c0d15440c81140c07204040c03501d02041104060041d45682c074081c0f06640000040d80d5110b0117114113455140d0000008901400b441c17050142c203c4a0300708040f4103600104050fa059982 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 76644956 1250 76643706 76643711
    0xb070309031b0507051504031a010905160c030809030d1a0907030507090303110c04050c0c01060611030d05090c0a03030f021203010311060702190b121506040e04030c06020a0f03 78
    0x185050401c04040c0c0304001e01d150f021810410031780c180140c07041e107800341d29540c0c1814581d40c1c0d29008030000344241a021340f03500000060100703044912500d50042d03425500c0c120714003664600076051444c01130020f424846002c00040d80c5200c10421122100e88a0100307214481d6052a0382e2043d4410350030136845000b54900007030045219100b811b2048007582d480701d241d076107152416284070b0303a05126007207a806907050f0303d04292502e0041a000e038600070a82513a49000303011f1682151001d800c40f00400c4809940482a1813001058418006030a040010b050701e0b2022058680385e44110802d410a91035031b000028180c010240c00c90910b05070b020380e00340407002135014801d8070090000502ca00c0340307040040802d0501c080904035007840944030680700c0480a070045400b00c0c0b290311800c04e4480c0000d082c12503001502d00350f81c00500d1014400c084c804002c00003002d50107a0b00498440d1045040054140740c41410340041450f0130050445d503c2c00803c0b00140a864250812030100c0e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 76646206 1250 76644956 76644977
    0xa080f1002120c0f04081501060318020109091e06030318061e08040615080d180e010b0f190507170304020108010e09031b03070605010e090604060c0c0b07030903 71
    0x240e008031510b01e921040461015590010b2101994002d06502580c689050001144003034040120303031000d0442075103070b015035850701c140207040d02ca40311000f000000c4807006860050360400c640e901a66400080410741c040301c0e2400790f0700f4540e07040c081182e80c0c1c20300e08000b09054102050030811142c100402407500c2d107414040e03c10b078003454454440043c44004481a803441a40d0380d94002c0d2042c0e034046505100c062200d030102e02d443c1c01c102c0c44e64100590854030160002c17884a6080c02864001103401d1500204141e91001481004042000040d03041c428176000380c120381d8000f1007010014070b80360900c02c00604a030802c04003240e240e425a040210039410400c152449079078169a020b505a081c629489107442002d05605964030051101809000c805071007443c203403000100550708e581132401c1444c15580c06034441e5001c86054000e00180040c041010b40d8440d41004011549180e101303c211060f01b82d4100281c9190804803e0260050349a003003640498080d5440d501e00c0d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 76647456 1250 76646206 76646233
    0x40308010e0c040905060a080a11012303010909060b03070f0504060603020732100207120306060903080c032a120316140903060405030307020714060304020108060d020a080f 76
    0x301c0c820749280340609414001000000ba207900101c1c0d12113030207000301e004256224215031801301141400c4500081c0d4a44103602c0b0f581c000c2c034010703e41e1080d03021a05550a00c050304c0d0f4642c80180190010261500815018070a494200d00300015000e800c031881c00d03039100182c090030101030064601c190309064001501c28444d0099038404c1e9082841ba41c499500018000c2075010000d24803500064640c0050366080c01c20b008400e80001c0d0382e81c016980d4003051030042c04002010810809143c54180d09000681d800360740013050f00d503c00200341d0794640ba00441840d40c01140942c1501c01180d606190701c02c40d50074505e80044d00c1400495485640030301e0341055500045515030103004488004000044c450620300c404c0ca40350580700352401e482031011034180301088074260f51235070001007405071007681040000300a100c060043c0d5000303000d510001e48d141c840504003a042110007004511580c0c2d8110302524040c0c2d0041450400075925106241c9400545403031201c4c9015100144640 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 76648706 1250 76647456 76647479
    0xa1707050106060c03051b07090606050909061503040f080f070819090501050d020901051605060610090b0d0b01050d06030302012405030c0402070f0507080106050a06022109040902060706020304030801 88
    0x10307a545900c3c0c90b418852120b540c1300e80c1c80e06488107c3c01c41e200d410f00c0001ca242c2d8500c64140501455030350f00b6510a101e02c1885545203003e8903142c010a0b41c5c000d8009104c00310816039030020b612040010a59103181400b2240f8082c0c0514190140000a804410484210020650802c142c91601c0c241170118405945801c3c880c07150314042102009000e007a4103403130b0300030311719034005051403400d088042d88100c101c90041c40080720103900000c18080c882c90a6080e010074281981303007074800c040c20021410454000c0440b05102940c0303440f6444810383c0540300b035403034061910900700702440d40d1781070080c0680880c00e1030818200305200c03000b9072003980c51b5110007651000b4004240c10740c1d0500a010003503001d8502a140c002e030312603034030000032002c3c0708100080c0000700004c00e075141000308002c070035092036002c8001c2d54020070305150018605100700756034a001c0068a9180d85a0340d000c5806400744020003940000c0002b5030000308040c5034080e50007540295074880c65a80c991095025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 76649956 1250 76648706 76648727
    0x61503140c150d06080105010915080303070c030315052805040b180c1215030c010503090c010e191d0705090307120f0b01080102030f0906130f050a170705010606 71
    0x1002100741c0340c101c2001140100070840c0f25291400001c12070750b0381001c41d0865a003a0030083d6029100c1a81c18034040442480c607025121404c007451450800d45809050383d4901d4000a05054503003107950210700c1e421482100406001c0c0500d0103c2140c8180c0100401901c101d1014000c40c002c40407540d03040501c40c0300e4100501510b034107500c021020411004050007002d841d1440801c201d041c44903182c0d003104a0107040b40c6c203180d8108041c89001c050812056508041c1000428010049011000141012000c5080c20490300e6995580c022603030b0b040200b0305130303100002141c00005505120510650301c20034010341800c020b46450100322400c3c41f130407114642c1940075503414004d10301e10300c2844044d58030594054803400101d035542000740c50241d2006080c1d941c080200241200c401c100e03540e01807080402380c821850030341e1000c0c40d0301c045000045c1540f2210ba100c42c00b00802081021506a04a0008190740e100010080415405404100ca9550a10b40000703560b0307000d01035045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 76651206 1250 76649956 76649959
    0x204030614060102011506091e08030a12051e010b0a0905040c09170708060c0309030409150501030f0501030b0a020c0f010207051608030a120b010509120303010614040803040e070903061503140c 85
    0x34a041c2c1b500c00d15104034000c50154828009c0003000c00a0900c80070002403142c2d400944444046980c48815041100d2000300001c0341d2008920b16440700800c3d880c40309054170786a1000548810390140101d41c5403403260403030b03038016150103040d4201a8100d14041b00b21044443c044072040081c03807829854070740910544c14660b0003280031500101445010b1130340302d01e07590100c909003070b80d03001c1c0e103000d4038121058a01d2100607404180805d580c54060f0f044000b0150710103110319491980c074007003003040060903800c03415030106003c100c20724148440032001181000075515184c6504065072038114410307119505a50403000050b40e0344020040d40c065605a4035007045201d800b5102c0e1020341240d4241034104101000207903019038600350b00010120b1450019900ca42c100240030b003407044070100c05980c10b5000c1c40200004c0c040001200c059038080d6810066644483d04103441d1004942c10040140d42884182001e544034030900f9000c69000e10200f400101c1d00010894461104d0300150303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 76652456 1250 76651206 76651217
    0x515030403050c0a0503040e0411010527030703060e0601090b0904080405040504020f0603070f2a150204030b040f051501080c010c0302100e010207020406091b080a0204030614060102011506 83
    0x14000c80e0240b00509019400401951814041d0390303126815940075808c03181c6461844428041484101b400d4594003210a00380b00c0d280c0480b820003284240790520013000307441c3c0c240c0040901c98500b440404001c40d440b100c140206071a034080961186400d0050714213003480c11400030b01030314088080e02d0040782c2160a0624107402c1505002c054003004201340d8000440c0d03100c2c09070a46540d0015482112940d682603180440c0b4000141425441e141450710f41c940c40480d034400c00c0b0320417042440342c0c2e030101c440c1d4074014001a440001e40120b5101804c40c01c1050200000e00001722030f04014a881a070070f0310800065101c0ca800c1d00346080c02074003040d42c00300c82020a103501031943c1814207402030045072031240200f10884103030340b480c808120f80d0380d4003c1040e400f1070070280100e1015108410051280c01040281d6060b003000d03105c20041004040008180e07010300d02d90403074001c1c54102c28140f111800100102d03107146015981180150310349007581d00b0a1402c2c8000b41300b6283c041e0b40301c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 76653706 1250 76652456 76652461
    0x908030103060509011d01090218011805060409020d050709050c040f15020c030d230304031b08040509101419060c0305090306160206070e0102060420040609060f051503 74
    0x2490700621008001c0c1300a0b43d40c8070140c51841c0800e007150400041c0e60400810069070702c4c41846447d2034087c04201c0d48281c900700600c00002103402c0001d0010040100052580d14400050003804048a02940007407074824030505012020500c001139030b5551400340030300d480d01c0414070450302c264442c42110b070701440e9081c801012103c081e407410070494030481e42c00480d100c00090600d884883c00d6404650720020b0700d5900e04801d05020403000300e10b0702e1507045280c281c5010b41144c03900c06c2e011a40e000005040d100b040381c418151005020050310100c0103160152810001e05058040c07141d40c8c142161103118a1b2901c001070300507840e103512041c4500c602c6c100043ea0700d07a04c1000d00300d00340300e07081c0040c80d02c40d20100803a07440b5012000300245000c0c8040b202074209800a4007205c1088000321001100c2d0740c002650036006175000050a20b1400c503040312a412050030b207000e9900a04221000480d1082500401d096884050f0103014a41d518010095801645030a82c06030342c0c400d200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 76654956 1250 76653706 76653713
    0x2100203040501090c170f01020f12190c0f08060609030703021012090602030103110d0c050d060908031503070b1e09120304080105070305160e0d050309030f1c02010908030103 77
    0x34681252244001203040400b03a601d0806104080c0c0000081000c0900d4142016030104820954004010002c5280c00b0441226503a244219140e0804141905000c15082050703001d1a940542c9004070400c450303a0701e00801084015910b655000040221f00420b65600e407403402c0b6203810764014014001645145d0034424101203600284084c0003d01039008031a050901840400f03e101e0000180c2d290704502c5c05410704401e90040b40d0203450030490301000502c0c00082d28095803400c48911402c022039244c1354001e81807041d8000c05c0c1d20f40c00300502640040592032010407210403025210b44a49800c1141d015008030324582c89e02c180007400c0f6107e280085401030004050107400c45000b9449007241c5441d540c041d900c41900c580d500d0080200c0c8a5052061581010010980381d12166081d0402001d60b08410300461088911900500811408000300d55030080051b00307035503400100c03c9415440c2d6041808042c041e0080d1030184d5003c80c4188660501c20754444046815a400e686 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 76656206 1250 76654956 76654961
    0xa05030a1709060c060402150f040303080a1112160f1b020a03060903080103030314060f010e1305090703020a090b01020a03050a02010204030b010b090f01020a1e03031b080919030210 80
    0x9030422821404110284450f21040700070700c50008800002c0c0890304151042c4039184000541e00801041d090000b10300001080040350101c907018603140311552940c0c00300c40d0050803080c0d520740f8086800903c0318401142e4a02d000c2c80344000311401c00d171030300380b1207015511010840030910020b07110080c01a840e020242d15480800d0019110f81ca5854480d0380e035204850b0703846003d41c04a60120300400c20103605004850f0300c02200040c1d80c0d22402d22101250610118002490602c03288200118042e190030500e11407041702c0490501541c1000d00d03501e6241d000b00c0c0004e90040c41c4400005ca4080c8840c000d0410002c4181d0080008071034940b011a500d401001404045540800c8000003003050030f00024080d0107002503a035590810030081080300100044018195004244001e01103100c0d2070380d958600303800b086040080c0e00c81d490100d0081086008041c810800d0300030b112441540500e54520a403030307070ac080786d1881e101e91460080c0d6003003401005005a10400d0564008071164 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 76657456 1250 76656206 76656233
    0x3010914060916110c040204170706021f0c030f0c05030a0b0307080c090403090b0c070914190209040213090b0103051b071709041803180b040b0702030f06090601140a05030a 76
    0x106449281700a40005000da0b44030b54022040000c3d10300c1c122201c250309010760070003004240020720b00d1080d04007040101101a004120403250b40300da4001c00d46003c1d8000204510b40464100300c07951a098019246d5001683d030f03400c1403071a01039450000c3c280021180c2c00d86a0040080800e016408100440d90000030012010402c0360034001800026280c050848001c0820203400303042d0901e030311102240d21080080b503040189c1000d0001c0c80d1041e11400d0480036000c0e801503541d01029002c140a40700d04d2400010101d41c03040000344d009640d5101c9041c581f02640e00f80007948805081500740070207020544401c041c1040f45100043c81c4174590b20000110961a40c1485120000101101c910101d024040503801d45002c0805901044030707100380039040c41d0805d0322401c000030304800780603034001d83c845140009219025950f00b00610256000001d0841d01107140400302c19031180e0b020f210f00d444815410b0403441c41c42c98204940346c144d6034003400610300d090040c0c80b41007418024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 76658706 1250 76657456 76657487
    0x605031e030705060109090b100312030b011110060f08060906070507060f09030e0a08030408070306091704261b28150810031a07030209040203010914060916 69
    0x300000d02c00240700b030060500030070502c1000107058103142030000030080010724134202000500030031720010300f0100c07c80d20a0541e601d0002005201e40d0f0060f180913aa441d2a40c18500c903150704403540f100c0c40d400603410368000007141a0503c0d0380d0101c1a5484c0c4003070700c1410098108100041c12a0701c2a00980543e5000351000b08804203c05c4002c17048030480c4c10203034009141144250f01c1414801200001441c091780158a01854801880c3c0c0750401804014085512041000103118103220381c42451402500c485a072282c2e00e41e5111180a180d600c8040c44d12007900d802d200c81071020801e011202110400042c00d105108100949004540030303d84d8084440c214045401d541c105280c03000d801882141c0c2c400d1201c4600140100740010502041201400f40034000980c804480511282110008201a45548509070064007a0b144240c0d0080d1021000283c210f080780c10240404650740584e40f031701e032103010a00240e00300485a02c45075000201c480c0e41554440d4811116031840c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 76659956 1250 76658706 76658713
    0x306050604030b01090e07031101050d020c0303010905100b0301060801030204020c01200d0b0409050c06030705160305091201050402090411041e0c080105060406090608060a0909030c0c090605031e 86
    0x1152800940d40d03400c15003003a2a45007101006102a071468400e00442c40c03026401031480d83d2440e070350b0102049841d01c1c101d042001c046290180701c071a40e01900c02040030031054903160368554010070014034088a00340341c10f1040700000a1403442e14001c80341070718901d5580800702d03802d42d02800b01079071105404884075980c0710440d08004840c03003403980040d541101d04942d105d4042400e481607400e0500528420751402c2c20190002d240000d422140f0714069900940b26655007a05440c980074521354000940340031500708007010b5100004294526089132034466042d80c0203983c83c201e490440b0001d4100d4410000b250200700481c0e8000c81640740204042501c2031020385894940b240700c030404091603100e00094854540050b070740383c00b4010960703140e0700f014035000004150344454071075a018400c100010803810b481d001400d01c0946a20074043c0a1604240340040c2101076500301aa500d5880403c0840c420100f8000c80080742d80040062004010288050303801c0c004250301c0001521 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 76661206 1250 76659956 76659959
    0x130203061006140406020a0f030504080607020d1d1c1103150f0618070e01090e0412140a20011503150501060e1f020a0203070f08010b030c0a060507030306 68
    0xa4080164912401c11111485405450300758080c3c028801615441d0104005000c00c2c0001e80e8002001c015181d008011511905034038141516203208940241c219030203003c00704180c290700007584102e522481c4e959208011000700000701d21b407504100880d48824100351301120300600c4a0060807450250000e04150810f003000079207009101c0c0301d8050384404400400c8501c0d50207000c8540c1c4050151108508007022400c01403080d0070042c070728401c0c401000100551644541c03520005441300602004aa040c01e08102000007002042c22000800c541c1d252010002c0340002c0c2c40c81a019034940104a6504200d00705072107003d20078120705596900202c2c0c400d604880111001140100c0714551520340405100c0c0550300140c000c2411300c44044004000c3e51180e00508070b0810344000702d05004900da04040f42401c01d5150041d5042c81004004945074500d41e020004840402000300642c1034480180350b141c21070f00e1002c1c2c1d40038611031010032816018400806006100e072070300061b003e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 76662456 1250 76661206 76661209
    0x70b04141006120c170c270103030e0310060308030c0d1404060c0206071812030e0904030201230f04110109080102040303090f060302120711030d021b071d0f1302 71
    0x4031483d9100100c1918a040d8a2082c48401060314016109411071600d2101e0f1009406580d00650903119009103d044640740294441c030341c07028440c10b441050074025503500d040003030143c8204c00d000e42c80b900400013944148951485001c1c100c0703a20905503400c644c1c030b0803105602070f008400108031040e203034003042c4c100101c060b400034895841840c00084030001c681000703281400003800c00c000e020000400c4494000513413034407800c403005010200c80c030702c0035031904461610381101c115412562000c280410503806400c001c0221480c0900e205910194a07200002924266202c10120004102003004038003004881210703aa418181050260703903a900c03281c2213920540c42900020b40402040c000442c141c9044401408145410342c1840380c0c2c0c110346020600d0180441040c042902c00b025140c140c00d10036624101c14004046480d285180d900211410800b50340b01d0050051000200300040740d14400300308203040721101d142950ba01c5403100c400c072002a101130540030102001e013006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 76663706 1250 76662456 76662461
    0x8090604020f04240b07121b0f020a080115051924020f0a0308070806060304020f040b010210090b012417040507030c14040b100203160807060c0c0308060303070b041410 74
    0x41c410300303484030b0350395509082004110b804004487e007048528118444242c0074004aa0081608900c800e9144c2a4038400500c48005660128209509140b1603801244058444a007210825140f01c210019880d034813a6041c5098000c00b41c42c10000641301d0501c0c003d1a013036801d0060b103401243d10007099403035070278500340507c030b0304a00140080c0c041010303850b408900240c100b0310a41d88241181081d030300007440311002401003800740c2d0350740449a244c1d81c800c0014000312110180c04004022190500341e40c0603109009120788000084410010104107800000c0c8000c840d60300c1078500c08041107910988280503000303894508c10316102002140b40c0f410404010070881d140c1030400f0030b05e0418001030b12040b50b4054460343d0410559841c0c4d80d0041308603056060303581005101c0b03a040f441c1c422075901946601074100c614000344400c020f074001e81c40345103040c0607032503e0140350782c3c000415591b031003040401000b03200340c00d0200c2e0008078081001d2000201020903a66000d4684071000308 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 76664956 1250 76663706 76663709
    0x2040f0e0a091a070f0804120f02010b0a0906031a0c07120504180e0606090408180d060f0203040510020c1c030b09070918051006080c13031208090604020f0424 70
    0x401c1102c44207110a49800805c11030540000d0f00b041011850661100030001d0b000c40240410700200506600026100394040310020740020a81240c440d168030f41c2200801150004441c6e141d0302c1590300d00e04802014031103100700100c20fa030303900e01991540d0302c2110590b8144a0303001c0c0300c2c040c080840e000c0005046800f00c007070202c0c0d00040d500c0306080f003985051009000240610f40d0141440049400641100c2603001c9100070883c036016140c000c0f814400c007802002c0c2500b8600b10070280b2030011034000394011400b03501103900f401d010a81c4041284112740b00c6100b607910400c1140b07070940b0b1110134484000d1031410006500c21400c00415010181216058000b8444540c2400031400c5100600e980300f42d840004c002c00d1520755200c031240c003e13074003032541405a800e000419221602c012500800c0c001c000052240750744e40341c52003001008660f080c0100c0ca03140d002452140c00060300c1031181c2e07001001014010141030038040203180c40311125011450b105103106108030f05120320740 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 76666206 1250 76664956 76664993
    0x304030c0f0b0a021c0c0e0418080409020c0c030706120c050909040b040c150e15070215030601020601120308070e0a0b0406110105070c05061b1207051b0102040f0e0a09 74
    0x60344c0e40ca0717210114480102d61040255424035100049a01550010b082d4102c01d10640740080e500d07900c504601810640400d000300141da0004000c66402c285070040c0041c6100031088a600520120030142c41d04001e0240100140c01e901c50000c5e2007040781c0082c1401c81c810308000d8a80500340000c10030068003214113491144d50801407104006080c10350100034081024880d000d6084c405005040648409c0d00078818011050503054462840e41111078680d401000c49a03080c5d000e1600d41003d8004031022405402120700000340c1e00e00b040c20304c60040368140d0356411a80c0d61520284c400403101a01c05821241c0d010011401001540060000d0300300f54941140301c1d003601039000d003500c20041920040000c21814500020400103d0942008846000300c81d00f440c2e010443d010f50107186944c0e200b0120007004d024007290400020f003020481c03103200c030314050007050141d4280e11481c425180f840308190000c21070040d0035030b0b00a420016031240071881202a48641c0b0364030100000b00d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 76667456 1250 76666206 76666211
    0x150201090b0109110409020d020f0307080426071401060b0c0c0333090f160627060c1403040303030501060818030d0e030c010c05030108010c030b03030304030c0f0b0a 73
    0x100a21480101c01e50041500d041c06000a84c80015620328038042c0d44241c0d01c0030364000ca1502c03850721554060381c81444030040c050782c076464001070007040900e061301c065508000400d010303441e10b1550100600712250348011989003407490307030320380c80040c8020100d00360656136201c0124a002090f401001e80740031190003004460355075400c16040a400d08510103108070b96500c1e00c1041c07104003480c402c2c15584550406080c1c1d84036043c0e40d05280c1c0008440c3cbd600e00030b241021140d070105c24055419a80e00307684905201882c84245688602480600454032000c40d030200070080c4242140c0d880c00340b00c0e0322100074010181001c40e2542d001a0022030100c0c1d10b810041c411942e00210090380710343c092454441c0440c610211603100e21a280b0210011503c070704400c120304404104483c85a0320000080020f81111200104160000e00491120703508015038070040c503208e0700408280c58002070255146881d90340e0280d03100f410340b060417540c0010280c0b40402040302c88404130312440c1010b001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 76668706 1250 76667456 76667471
    0x2030402090c070b131a090321060f09040f0c180608030304050a170d0e03040e0c1314211506010201020405012007031b0306060f140f0a05030109030e0a1a0a0c0c150201 74
    0xb481100c001b84927464a00088504204250b0313640d407082c00c0081070989401409444a00b044c51581191090190840809400002d4100c41080030030b81d8800010204020540c0c5400c40503440744000d9030054541e50145545d94003040d00300c0150180c4226180d005440d10140140c001c0540d04800e049081d5500089020003000d491218166840349002814602c2d01ca80d40030048220740c034901441c1090301e1074a095020949600c1003084400c40108600350900d410b40003042d6031060004e44940c0041d40460119000f94014025101600d10507150031400302c4030203c002d90340c88090300c141e40c181e102eaa840000400c40e5544696182d0f040c60000307181203829030500005441d02c6910070050342c84401810003500e031000c170000800308000c45030707081c24441c8400041c00c03080c002d410065040d440c1c000301e032003010340160100c10b0442c130950301c0c024110395498140c0c20590040c5e100e10a81241080402c0c50345104200d001040361140e606070350951307200c200000000e4500765400c40940e6482c0741c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 76669956 1250 76668706 76668727
    0x9080309010e0d081503010f09060507021b060405010e0d0807030c03020610030308010603091a09030d0b0d050c13020d090305031e0702120705010605060d02030402090c070b131a0903 80
    0xb05020303192030b000200380303c8003030240080c107a2600810340c030304840054105480695080d0001115002c5240e01845080b80508044004000036501e00c0701511401c0c41011452b00f6001d501c3d00c082e80010b0000f8146480c0c540156a92840c001c00c049d8081ca4840a00000801e010b02500d40e00d402940c81840010706803501170b00c0d1110142c0b40d40c40202d503406080000941c07160800781034032018980400e03111090700d451000100072000890300c481070002009100c02002001d0300190030016820b10100310900d040c0b00a1100c2d904000e030160b0840b15540643d03041c840e40940f540880c0f110014644070f40e158417013040781d111180803030000b4800400e00c80e0420114000c0b80e542c0b80a24040c142509020f00003035500c0d02c004604520320031001c145401400300a5001500902000d07003402d54688505081100941c0106da0881c0b10f20418000b04030b03410340e41c50503500c1c3c1c0ca07407005048005840c1d2102c0c0e2003010004813012140941140403200c0c0443c0b0180e0801e0080d80b00500842e216100c00c10f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 76671206 1250 76669956 76669961
    0x20102060f0609040f02030f07170111070b0109090201050408030f04030627290a020301051f230c0a060902040b030c060403060c03020f040b280c0b190908030901 71
    0x10207480790001440c05001c195581c00c86a55009588001032014016052002c00d04014415094503d18050385900180b000844c1041419180740080204406403103030007600c4550044401c0034001c8891100140228619613002480c0180141019420540d9076140d95266030321012503144d040a01060070820080705028104980820200b030030440c40009001e06034207200a08003421404803400d0900701c0410b483d00c01300d05d0141c600d640450921700308003884040c0d4020300c100d5014007591086011110008041b00d410015950358010350780300c60400d070919030304038410800c1d60101d08000c0c401c040740c010000d540c40d0074407030200400c0c1e17042280104000c0b43c013000c60243c080e03000304800600c141d031003500300d400340ca621000003d00241c001004030000e0040201100000c400001c01044080c1c02c2c0d8003400590303801041a00641e0082d0140c040502c00c241c42090114248440403000648039400107035010810b8150705001c10074014148040c0c4e6848a4192000100001071114440d070a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 76672456 1250 76671206 76671211
    0x1030507081e04060e07090b10020304030c17030904050106080a0506030106060e040f061a0403140d0e01050d140a09060605040b0f010f031407110d0e06160203190c0302010206 77
    0x90070100c003149001842c0d60955044000030b8030702c00004a00242c10040d0590004014546000413591407503240c8600000504500c0d07a0588644803085900d0015840007084400381e903402080c088005181040488400c8c2a0311801007503400248090700d5031352611300c9428020500340d9034200040c2032004244d403c550014005500a9040003414005c1e990030800306513401c80c09550000d41c90f41540c02c500010452a0000b41195060585014104031504094803d0707a00800d42c03000d808c1e9110b21084c0d07407010051100c0d0049168070507005110760044002c0c0905140180d00800d141c1e00d081004049010102c1c0c041c074802e565000d901003484810720906c00170700015581042091020400603688000b00040c081c10011181c1e81804081d100c2d400800b1050349120940840c2d0403d80005803078290802140002842220003440d070b042e2040a03040d90f1003102a121900c0c2c14281c1e0885140f0302500d4405a8051080c0401000790080d000c940c1041103000f07011a041080c103501c002810581e02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 76673706 1250 76672456 76672471
    0x1e1002010614061305090a0e0609011505060c2b0f02010b090a0b0607051c110a030e04050c04180e15040b06040209011e08010602011d031b01060b0f09010305 69
    0x1003010610004003052010482e8420442d9100d407a241c0c20300e00c503502204140c210a0708029000c1c2440200c00150b0840e008101c1800c0580d54180c1d90400a20b0881e40ca00680c42c1c8040c1c01d6800400180c02d0603001404441e10540c00d03030705006009a40c160b0b01c0000961414491128035091003031065115181c40c4002c3c2c03140c4000c0c405115030100145484e1005041c2d03a41d01690b548484103076944281c101d81a1582c41026195072031220600c01041d00429542c03800480c017040c60001c0c613086e0100c0c10618282d81074688041481101003800000c120040610020a001f00000b04040450f502101c4030800c2c0c044000c04d400c40daa5903410705200d0508805075180310b002c01130000207000d109035240d00c200181d40068032295103400417601a81188e0454072403015039a48c01d81101d912100d40750503103041d50000e2203200441c103821125545800e421801c1c0344c00070300c4244280780300c02d10f18142400c1008000310301a0785403800c8a15552121803180100c9000107007800301540c250088503409003e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 76674956 1250 76673706 76673711
    0xb060d0201030207080c0706080924072c090105040b01080403030509030405120c040e0c1c0c0e0a200a0f0305100e09160e06100c030201090b10030201090803090105120408091e100201 80
    0x2181548440080c2e0451071a0ba14172940010041840b0340743e0318000030118dc1c901c100000240c01010840145030070340e14013686440380040748030b090900607865040f4042c0e49101c82e650340c0340c03030403401842c01401020a90108100004880c1d55214441095040e40000b4081d020550400c000c2220704075981e44030b090f041a640b0240740c0e61003d01414030780e0641c10840d20512024030740f50340010010b0f007010500904540c180302e01c05100727038480c0740c40600309020300b042070710b11010510440c021850f8410000d402c40545124091090708540d0700000d00004030301149450b0501c400c5524401c69000c07140f030788082c1080b241c010070f44110740011b0064007040c1040381090702c0803944841c0030100d0a0103212007500d94800b098800d51109051580040311030800b42030040381c074429180d10307100903030001d00768080c04280b0040101c125000e0000585450745000581320301c008110384004d2064031040800c0c000034840e600c60722200e144184a03294116845890301e020080c80300041c1d03081508684c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 76676206 1250 76674956 76674973
    0x608070e010c050f011e230a0f1a031005090705040906060b0403060509070e040302030a0c081902030a0f020105010e040f020321030109050112030807212f070b060d0201030207080c07060809 83
    0xc07d0002c50440758203220b10b204420360301c00d0050360140c145e14401004940c82d00804d511b00008801000305002d00440a489641c00d0001c00001920020b44205407640c02c045020402c42c03402c2c0c0c3c0b10309801c91090070301040d0b41d5602d0310150102c1e04554001e480098441e0704200c0c01141c20700c11000501140f18103844103043c00d8130000e550380034000307241051224410449060101c050300ba680030568100e1078002d5604c03804802504e80d0042c0f003450000c1004107074080310650046c040c49041c1c410340a4160110798031520384050b0300d00311500a98060081c055070701403a8510f815000d031322502c0c40d080c00383c1d20b52400b024282101c2c016801142a034280d50440c60010758418a0309801094615040c2c4100c0c01c034004050101002c1c180c443c0e0420724191080307000d050898203031016080411908038020f075081408800314402c1100c01081c2c280c001000a1f4240340c40f841c1c05855500600d4018103003011940d4004441e4405c1c80d010916903c450810029507601c03a00c03980c0e002060102502c10f90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 76677456 1250 76676206 76676231
    0x603040b010501120204210b0c0c1b06070210080402090c0403030e010810120302010905010606020f0d110a08030c03190b0d03110316081207090608070e010c050f011e 73
    0x244040c0a000c0c1004a11340b884803a82c1080d0301a1170242100542c1c8982901d070001074254039806c0c2400440350340740410300091003003c41c0c9048d00c2c02161040c01400c4204514080e030a500650b08031102d60000c4103105600150301c50b4961841d1401094a80e5004d03400c103401005001742005040c03100340d41081109100103a03001240700e10011302805c00046544444c50200c2d1135a400703821120203c2c20b6480300740e003450b23415044110040d001e58001c110b220340b01c3e0401c98613440c5d08000509260302c615602c001080c883e9401c03403580c407a244150b82d001d140a5a5180c01d560080c0d07440c0f0380c0040040300380f00403181d50f03110013011090b41c144100030600000b4003281101040b00006028014035400041025501f401100e03506095188015036040b103c1c80c0001c09a00480508e0316110704540000c0c1c0014007178101c41c41552019104c0345201e43d50a02c0895090b0361422025040062043c805070000f1030403c0840140d480340340001c56480301c8070041c50a8183d100d54410f0505081040a0600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 76678706 1250 76677456 76677473
    0x1b030b0c0d0b0a0f030b0414030d0b010305011e0b0a110111040312180b160206030403090602060702150c0f070c0e1b04050a0506070813030501050f060118210204050406090201080105060304 83
    0x31254040d15032011b030764480c10714842400300800312554038040026000545041503004001520098030108496600d40d040c4098030310510b124032a010030301711800d01050600310003800e41c0c1d5466207050400101c0c8014100d00703550342e21014504104000c1414000c0005c94440300700181420300c1d00c3d804031034282c515400d14140c1403041d000684030000d4034245100c20340072540c0c0d2640e0060600b42d542e0416141c014800d000a108130401806a40e000c04c01d01440400c541d0701024003054020040d1726010f00d0303054581c1c05800c0d0158a05800c0000301d0024a001c20340030010b040511480c080ca15040c41003862640100b034203c80c40c1c1c2c40400050103a5030f128005403080d2502911525210000b602d04500c191080a440700d81882000c0d20000070000150070103886030000000448a5440d89001034496400070380c05002c0801c3c0103203080c442c0015461105840c160f44a00c1e45142d00960740105048500c00d403400d40b015912100440e0540d41c105000c40d00608040d07035080c4c55803809844131400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 76679956 1250 76678706 76678709
    0x60f0c120f0207050114160207060c020625031808010b3a06050a0c0302030c0306040e070f0305061605070f06050a060f180c0305131b030b0c0d0b0a0f 66
    0x10302036030319900104008000c1d03040e2984158080c0007081403290030190451400c0045444044005d55030340c40315142480898040103c1d0010b49038400f5041459080040d582c1110743c04a400e0408510450301e5403031400600c2c003c0070f0003078440200e20411211692000d04041d048007410b681030001da81c01a4480c0c4001403000110040054600340803010030401241d04c0002c07070080c45446202800501035954402da01038220081d0030451141404010340690204945a407c40c0b00c0c140005066402c09400c4415949010b20548003c50740303849504141c0700c2990030540e0745900103010030600c65116500085003510f18141241004a107a94080024040d02e40040407541c0b00c1c80071500c901816001440a0480c040359041d001da12400351b120200700f541a0a0501401c00240420b000c0c028418640902c1120118070020b009545030400c0000c01d0350040d640710050000000b02051100300710340e0180746101c020960380d208201c0c0c0300c015100c6c2400080e2141d2a1240c01f0410003001c60041d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 76681206 1250 76679956 76679987
    0xf0915100816110c03030309030406030e060c030a051b1605210403080a050403200906012a11060c01090308090102040f14061b0303100e040c0b1308150103060f0c 71
    0x400110001d40600300320380002c0c003d1701340c030001c01030000c8128080003401c151096036a081001d40d011b520700c5036603480252100e081311481000850a201000d81043ea4081402c00362101d0440f88841c20b4107840d80300c0006440c2d441044041c5000304074051200e14448031503005401000c0c20300c1d9624482c28412032000420606001a0503001b450042c42914000d40c0c20050190408000b00c1011880b100074600241c802c180100000e411503000e400010701074a011070100103050f81403501028240c0e04180309503210807a003000180d01e5642c1e00020a00314400000114220900b80340281c41c03c03030040d1a0803626401403009024615820401c801101c044949100c4205041c03004507507944608181401c01c810000d202c001d071a103000000390301804a81089808160342d03a00c2c490301c2035a0030b580041048200f50b074108119000f0001402140d140e010412070300301e5076049068a820a40428269604d0300c16004005120503842181000d042c4844140b11102002000501d000c01301e48022 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 76682456 1250 76681206 76681217
    0x50306060d021207060201091103010207030c03121d07060206070206160c1103030d150b13090f18030201090201030b0405060d030c0c080d03020301050a05032103060f0915100816 78
    0x4509541e02e110200040b8110081070360301c2545c94200c0240645075088060f07442c00f10a8004c50f04505051013104d000c240c140d035a428600e1006ea0381201c1c012902180381140726104c000200101b09060220070010f02400010200e1600d0a4006800e06900400e4402550492070401c01700d144422982161076096148c40c60031b40311507142c501e006500072900d0541520000c41d102032104619800108500c0b40c0c00315140803103030394100d450a648140d004020035031a00303c0f01003080d46040c1d08407001c8a420320001056504003c00f504030703000c51589096006079111455041596054030070a4000401503905208078580030f8042000a00c03d080000c4c20403020120040a0010072140c07640600904003d642d00c1440494008010790020300a240c8140044c01000a0398600010f030580a00d102895600f6020b020a94460361608020011a0085a240d184884035a01c0307103551341c41103040280c4440c403006104103220540340500404810f004c0010248109104c5a0203000800002c904e0007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 76683706 1250 76682456 76682479
    0x90201020109060e030702030106140607060e0f030c03120a061505030402010309080301080c03120a0219060b1003020a18050109050613030209010308030f0903030613020901020a0f0b0105150405030606 88
    0x40303004010030700c00901a5468005130030540f16010000300040b90084000780407941d01d030b44483d0807520300a0815580030904104a0000a22507041003c40c0c003141c406036032000070007010241c150b03440040c01e40c030b89800c00181e1041445541030520341082100350100002c1e400d00720113403124486805060180080400010b0440e80302c3d40080307500c95030124a058495a48410271544d07000e2410b5158401d0007552a1880c0c950b1049003a69000c000f154002e02c144030300e12020004032100a442943e200f5202c812005050f203400ca50506451450740d401a0344140ca458000c000d81030400300d046103104c6084040080303a034095580800c0c0d410888085641b100000c070040f0003509a584004d401c411590000010300102d84007440c820109000f00784441c1d0340708410182c89100403121141d001c000111401105121503000d405030300418011a1800b40694680d1200c159281204480d0aa4000c0043c03045003400440d0300e105060101a140c105070803c0c0c0001c1c1c640c1030081900703001c1c441d851003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 76684956 1250 76683706 76683709
    0x1020d0c1b0905010807230d150203010e0708061c0305030606210103050f0708070b0a050423040b010309030203040b030a090804030b060f0a030302030304170c0d020109050f060601120902 82
    0xa51840340d034036064107203100a41d0b966102010b80401d02c1003440c3d9000c0e840000503280780012100303810030b02003450b005040350748604010541f00002030030740f1680700039403101007000d81920007140a021040b02d4103846141c1458010301da81300091071039006038525413004127880062494036007515410308015071203689140104c0e40314015006083d203013090820110180240101c9049e0580c1e0044090b108031402c2c50b041d2990702d001718851403c040e40404002c00c070002c5018094500c200f072610f0030a180a070703101d00107510400c604000e04e034420740f40c45035030a003071402c0c0c89980804203007801e0501c4054070680300a5242c0c05140304c0c11869030300010024405258903809182a00d40c800301035510b4503145e04001000440480c0c0c078a018070100305101c031440c50001004401c0340c2c0d060340203501d1503680c0d990741c601c10410307161a900141c100340701d8009030007003d02801007049415400060300310b02e20b0400501d00840345442803d9504a4820320401d80d07440f100080c6105030002020039812034520 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 76686206 1250 76684956 76684973
    0x1b081b090d0f02040f0207020a060e03030f0c250803041806030b070810050603010f0303050d06032306010e0c040b13080307061409010e1b01030b0603041a011401020d0c 74
    0x14181d0340400000c22440c20070180d511400000740c026601003100000740c803400e20803031040190195001001c42d4081115601c1040030000e46000607050b681403602402c1c3d040100e400c00d6035028400e4010010b03021046042c802400c2009010382903000309a80b50289842d02ca1190303000d80c0e032000c2180c030340207446004036410000c0290780c04112500c0602e0031240090629009945141c1000800d0b6400140d500c1d0003400d4038165048242c801c0c050f03500d96541600d240c0d000c1c440000400d030b101c050000120b1030325003412140e2030151460006d94801100c1140c14014140c0149003802c801c8024003400500c01c81c280d801b582e01c4c4a644568815040d1245c000c81c01e001d5000c091240320000f12a000c20506030003900c404846d20955101d552540c540751403d03144040110050317030303001c81025826002080600540d65406040009080120364041507140c0e004850030b8400c20411030241a15400d030b000744600524030740c2c0340584501c0d0720100007500da080c144604c200300040783c01c018081c050800c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 76687456 1250 76686206 76686217
    0x20c0f0f1f0203030907061701060309020d0501060b030a0f05370e0304091b2f070308130501020604050709050711010906061a0403031b03090503030a050d1b081b 71
    0x8000d614080344800d6070007940c0c0c0c0e0044883d00300b20b0144940001361a40240075442c55079070302124000c101d13803c0041c11002008807044c1603902811000110010900a104990142440c5007c140d07a91401070041c0054804e08900d0321701172442c00b000c01ca002c0c108004441d00f036502c00f903040003040301c0c4143c00400c100c1210503241c2c0d00714504403004e691100c0020042c0300f06c8080c0d000902025540c1000c0707130820325003002c043d030110700b800c040302102d40407001124076819039101e289000301c020b1101c000c1c03404003e900101d40b0701c81c0000781c04850310908045140141001d200801540c9416079030a91646210302c1008105512440403c42c034a000b00041c007024036104000700b05651950410700d0240499102d143c040c00074156110a154075040126820350390035898005001a8a0b08054a22120782500b94100214032a0106482d035091004020400c078a950305911040201641f41c112056210304203000c500c500c188094040e00a000c4035444445443c001d480c401c125000607080d032140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 76688706 1250 76687456 76687489
    0xd0209040908031e010504050c1b0304090207030c0c080706140702040b0d0803061f0507030e040b03070f17060f0408071b06030e12030c160f080d0506030c01020c0f0f 73
    0x44100842c13072a041100420000da1021124026642d440c10b010459106590b212401c60040004007001070b015600d1080c040c5200040340e01d050740c0c1d22503100c00c03600400801c50028036021a500b00303110020f5460400b030003415024260702840c01c80d000d861000003610302d1140c600e02184480c155510380d07201700441c4401601e030000380c1220340342801c01944116100b038410b00c20b445680719030300e403064400701002100341c98a5181032456102a921741d81c441804070350043e00c074200140c00307480501507800281501d8900c0761a060070300380d0300c0080e0700c04802c0c2d0035082e43c820b20410400056110b10185c0103074100c43c41a0352192582801002d0b81d10382190500030514840b8000382c1d10364940d1001050081c0c50b030983d02d0764054001d800405100039958141c1703210741402040b003e244c030b000700450305074070840305220200d0055660943c250004150740c0c00d80d5070307240704004140c1428810407520160901c0035004004004001603d0007a2044006000d4000c18007021450340320315032200b100307414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 76689956 1250 76688706 76688723
    0x708040f0c15021b01080601050904060305010e0a1505040f03030b0f04050903180913030809030412030203040306060b03040c0905060301090b04080403120203040e0c0d2a0e010c02060d02090409 85
    0x22203040030600b85904240a03001032180f8250a041c080d144403c43c000d5990595a60030140c841600449a9400110149501659401e8000002202481045034070880440945542002d6017040705001c1c0c03004030701c003841701d00b007404001c0081c500c1201d07042c42991609002412500c003c010a042c0034110f400582c0151078802030100d040c1c0300001504000c0103958608208413003680521410350015140c822885600104d40303030010307025440300345d80700c070800782144d00741a80c941820700c00150b000401d42c0075800001e418014440c2070300500020b81a0144194030f141015564009231300f6680c810030000380e5441001c2501d80d5002c0d00107096681c3c0010143e203a0b800c1c07504141ca802e0b4803c1c0310881c0d1481030064a4020513002009a5041381c0005254140700c0d0f94440c12045c140c2e00001701940c8156481c841a0703140901101d80c0340b40d405451349041202c1c2010440078000400119200f81840385001c80c110050303072508101c815079900e0410243c0c80d00c1802000ca009000d408200510029 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 76691206 1250 76689956 76689959
    0xe040812131103010207020609061b0a03180f080606040905031c0212010f0b120403021e01021209030c0304030807020a0504020f0a120908040320060a090603061a030708040f0c 77
    0x90359000e0440409000e80715800b02512804109030803032142e648001d4000005012081082c58444050705020181c03404442d81c400444c2c8500d4141120168102c010981e0f081020a11030719244a15029001c2045007842d06410600240c0c3c0d0741d8802800d682c404c03038440501c003003000300c140192008510070900806e101c407c103480000c0690008001100507100700320000600c0d000d0380c1c141404940c49450224a042103400800860340c00007003050b0191311802c040d01780120340304407844075001c185600040e02c40c00d51113019081d03004042d064102a50061040301810013010048904aa80c0004410360302d0059201142c6c202d0407550069521034804103900c5520140c3c00010181001c0b25a5900c06145469805000f10f5100100c080d110000603c01400040c0c040f490411038514050321400341005448000303545580312251002c0007540360b4200704034140c1c1500500000d000b010491884117050314419100f10f000c000d00708810061880c001c00c0500441d000000485a0441540030307019 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 76692456 1250 76691206 76691221
    0x30603160f05011103130b07050a1505090f010e07091a0405010f030b0709030b0412020c0907120b0306010302090a0c05040b0d05040312020c060103140c04090f030e06040305070e040812 81
    0xd40c064402d00340800d0451100c0c2c0c000100100868902400e1078481030f540504062070310b401a04000011286031240007060b2001c0354015168031910940843c010400d4071b00018081d003040540316864170315a04000c01c000388a03101203060000d80c0c00c1d515001a003a00b0410746040048411828071350802e161000100300049022510001e41c0d0090411280c5929281d0084a44625500c0054040502403000c40c0009044034090040041c0d1441107908420038040050501c605c2622444045030030f82d074070500303a18418002c5e41860b0800310007a01ca250b1464000c034640700e1000301782da020241d44003021100c40380120b00b51009841210300d4aa01c8032161100d504c0101000c1e00c040c0c0c0410440011170000910758022a54407a20120140516034a140d0b515000c0074102c10fa00c4500d80a40c1440906030f032128854209440e02a03461903060b010b1300d04001e040703c2d054a5180b8002d4030308203c01c2c0085100004ca9034111280c1380038030015540c540c10404928012603c0c0340c02d091400b5130601155 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 76693706 1250 76692456 76692479
    0x90a03020904051006081c0309060f0c11070b0c030711031203011e05090402100f020c060c0a17030403021e030412060209090105011d0603060a0b13031103010b0d0803060316 76
    0x503103042050400010b906e8040e416944c114502858070074550008002e00d045100740c10040285110304c50101e0740c41044880a000e8071010040d410001d165a1442e4901c4038040240000800e82070303402071328152440c222a6200c1c4612400a03260103000d00703040c40241c504012240f55000c4940d1541d4a03035071100c11001040c107180d06030b0714441c56500f501059628255900b2030050754028503500c00100e18401c01d40d4640d820440440a41c003409280708415210b46004180036120540581440707405441d007004100002031803500e600c2030074000c00c400650000796544611080442c44400340c03550700212451481180c02c480d080c1090142c9410402500d038002d0300c40d011044038003859aa8a070381c01100d41e0051051079000b14104121080c04900303240c0c0045400c504041c0900c05600d454082c504296030240c3c40ca03400070b1510780c00402c14044212000000c2c1c00044000b0722000c4044c000169001c17509500180c50480000b011580d260307002c002c0081d0a404030810f80701c4c00355079202c14940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 76694956 1250 76693706 76693723
    0xa0510020f0d03050f190b09010f08071203091e090c050405010e0f06030a0c09050a12020a0905040807020f01032306030d08091209010903050109060207060b0402120c090a0302090405 80
    0x41a01c0380c202d9210459000f40126480783c1c9404580c41195910845000700e64581001c01c458001d80e900c0010b2103907255414620701800800c9208010546031411300792900300207a100040046245040c1400250f006907540c0441e2059000344001c0400303e1103200140e0b0460b071155000070f2a0138500170600350000e000c0d20413070740e098840c1003640311080b09100c18032540c42401a4042c0007040050340c0b022940d071018044460600d009100d054455000c01d034161040d8010405c0d1040d200c440e0f2046103030000c0420090400600c0500c0281070640c0c54100e503014810000748141e2603c00040642c0e4460b034041001040941c0c5041c4581d5034000d11201c0c0b4030401e461aa000f07004100038034010038007030300c0c269009824401c01040c081607120043c1030290002c1940c0d50401c0b180d40f000001003402401410791481c003030500103a0340d003c0e6150400484040303010381d601881c010303c003155455100e00c0d5165488080c000c1c156580d255a003001500e1400700e9003009502040c038030144018080000751921 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 76696206 1250 76694956 76694983
    0x80c070b160614062209020a0909060b01050c030f0d0f050a09050f0a03020703060c0516080306030c0a0501020c0108062808010b090402090c0a0c21030f05010f0308090a051002 77
    0x800100540c2d40310401c00300c1304c05410001480700141c0c1c3c940301c55214100f00300b1100000413160000ea001500c8100980c0c0442a400e1701d4050400a00846108840b408642424664070f08158042003c3c0c807400f4135240605409004901064030368040d41215820310f2914000300440d1a04611040040c0a440c0040d1440d1089000b00c08481c1d82c0015114a0603415400410f00b003861540c03020041c01c044104a41002018081142d03084024842821214400c144e410345915058041c50b103011091070401c4d205003255071041100b13903000b1501c0d91540c5030a1801c1c0e840f80c0d440d4400706900c00c2040f500c00f80007110100080d40b00c2c0a01c0c41000c015030700c413a40240214610364081040041b41030700c1c083e6204a21a0120781c203254103c00501400306281401089281c840d101c0004e4910001505503130101c650400c00003c81d0300d88504d4401010840c4200050b5041521140c81885180801440f4000000e41901e90ba41c89000d03000c002d14008052024203801d200340251244414101d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 76697456 1250 76696206 76696211
    0xa0e1302120601020d051204060902030d020d0e01020703020612070c081903060b040e0c0705151003120206090709020703021f29010509091302040e1e070e0103080c070b1606 76
    0x38001d5072000c2003c0c0e412095543c2c1b060b0814000e84071307602d150310010f081243c10704d039112034080c010f0b00c0501c00a5003100e100e8003e081800c04104d005001442c1c0c10000c01c1c11900246014070059441c4402e0b00c40024402900c034004d0398821506031504500840c0182410602080b4507000381328240300284070241a0350709202d40383e40c985211032240074502407140b0041c0d460000400741c00c5840040e00b4032034024001c4424460808088650b603090a660810019090540504c10300c6280180f020340703690148010070061400c0313907020b0b0b1900902d01a032158240c0024032402454401c1103001c9001c0320f000400e0224041180d0b1620040080203081101900100003803e06c0034814584009901c0c01038440c40e1900071810104018210001e042c41c00d500b170000103180140e151845401211040000200f849400d4209000351242e81d403d0b042c00540d01c2958184141e2100c484020304480d842020551144880b084907800c0c0581a000f01e50401340c0070401900c10304010b080c0c40c4585e8010b0b00304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 76698706 1250 76697456 76697461
    0xc020d1703070210020f12040305040e09010204050108060906030a02120c130204090c1b110607080a02010501030203060a151404061a030a06050a0b0a0c06062c09010513080a0e130212 80
    0x101d4164000e690181e078480f6000c7c4480c21181c0141203407036a0040c802e01c0c2c034a01e4103441d550840103070041590049c50f02d1b075010a0502044d60401249600200b0480d0015a01c1c5006000203642d04a49070009014070703406082d01043c00c10400200d615190300900704814944a4441d4400039002441420b03c558140100b4900c00c0b40a2206c90522803402c610183e250030254036108105842c000a8070303000300301041a8004a280d40e006001d808a8581c00800c4c6035245004241c6800c0000d8414000c451500603c40b008a04481102c0c1c202c840d0500d1660b0b00910a0000074010040c0d540491200040b42d00744042002580b4001c40c810880c04404025043d161418040002c640d4003851010390400c000c011030131402004019509031080101141941d241c40f144460102d80002c040000303ea0001058010070410200e60342c41101c07040204854035000c0d03240c1503100b00940002c1e14020000032103403017061080040d0303500c103e00075002450f202c440341a283c00a40c4503051011205021201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 76699956 1250 76698706 76698733
    0xf0a0201050f070e0a06050c1204181103010506041415030702071502030a120b0301091509020a0504021810121b081e0a0c05071208180a030f0c020d17030702 69
    0x2203440d208005441e08005505041b410707119580f1090758000f07644245401100084140c0c0002c0002e801d148409c4031406c44140c1000c010303205082d80c5000742c010180300601c44d913101d460a4404030b4402c6608012221303103101c04102400c1907d4141c101c0d2600001c10449155000144841121030051503000c007450403440c102e889000d0120700c003000403002d585800d01000706400c0307030703032a00d40060000034613500c02c0d03440b5030307800040303140c02e802c06902d452a840c00d52401d044034400502c0f00303460551510b403090f40c14040c3e00d44943c0141d44260200000c042001c0e10031003001540d00c03414401009410309203046001445840600207001440300c20010704842c040900381d0000308074207446000103071101600c0e5000350181840c2c9804210044c00b04c2c001241000c03044900ca0403554981c90198200340505600c140c08442054079142d10a000d5100040c3c1d10002c9001e2003000351520001598162000561044400a018004403102151030100082500c000c5000302455002c036440c4038070104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 76701206 1250 76699956 76699967
    0x117100507021b1f030b04110405030303060405071e030b0f0d02030c090c130b04050a15050304030509040207061e051806040f0c080304060c06050a02041212050f0a0201050f07 77
    0x300c00c1001600311a030f6500c4402c980c280c490f105020001e00c442c4c540490212440d000800d410b92100c00681c0b5082c8155040c101481076550306404907100d0351500b800c00f40482d603280f0010b05141e00455031b80f27000420b4184102080000d280300884050100942c1c200300078094030501026500c80e42000b160b0400a10300a804000700c5039003e0050280124200b080021415000b40703613099038441008120402ca072000080c41c0540807409030703a40c4a0741072030305121880c01ea60b0409203800c005050700e80e22507a0040181c0c0d902036403500e803030350703407404d07400c021401a009602c002010030b8102000603d400003648118160613449038010001c80d520301c401c20141c03140030303994404160014070104002c18040b0403130b868820301070415124000c3c1e0f42e00d003991440d4465804003001072581e0310500c0800005000381a00406048015070409083c129030b1101c45003c168001c102d40120003405584900032020785e01c80c03410503010720381c079803540d0440a0301a0000b1105c40580544240c0021015030261 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 76702456 1250 76701206 76701211
    0x9060504060e04030c0302031b060f091203010b0f04092c011505040207050a0c0e04030305010b0f1b070312031a0306070f080403091a190804080a050706060e01171005 73
    0xb002e100a4541d92019562043c0843c0c0980850008104110300480d804402c0b0703000403040f00080c0300500c3d104e00317580403041000d0101121600a41c05005059216406490555040000e410341e0350b0500c1b18072080c1c1c0d1181da40559107640c14400c5c2d40c4603210b800340000d922054029400d40510400d42a12822115035045000082041c49001d126508042c1c2c0902502849241224628460360325080e0111240d0792003200c0408054040004042e03140c02400d0040407800300d21342c01c108404490b0301560281c40c6404c1c44a150346161140081e00070030011000711f411110020880e40c0c2040c000340901880700f04c0d403e40c0c1c040c0715207540711410b00041c0ba610035090b0b0740e280c40704095a15011900004054001d5040180c0c000c00841d040540e41d9001801301a180080d5a588202d5281c0c1c003000c841050400092101040130000410108d108444460a4138640140e9031718071031405800074010340c0c2108a00c58540e000100c0c1e40c00d14511281c5c680340d0030034111000007114a0754001900c108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 76703706 1250 76702456 76702469
    0x5150319020402070b040f05100e06070f031b09090c0e0603010915030507120309080a020a03060e0f011109090916030b0406020c0d030506040b010903050a080306060c03130906050406 80
    0x440d0400011099260203a184000c1015280c040b1329103615080c640141e07003d85280c282980e1281c00c0003400c1240705400181d241062129500412540380c64840c0240000144804c105058840501c00d900c0b102900c01c0714a08400000c88602000b040304110b0b00031007111750702e80030340d0b502a1401584031242070080100650310390380c2480100b10281001140da00c01c00905031f040413000800510064004d0081c0c00d844101d00101814020f004002e04d91010703c9a412100b20300340907031580b0380c4070300560341c02120214400c03d1040031240b0341207031148a456203500e40f404007940c1d035262a00405a0300c008541c0700f281e070740787d4544a986407180c40031480c1c01101c87c0070b4100300060544140c2030380140a5a0014101001808110300300701103070002c28006960b4070104001403406118810840b08203103003005100d0306650300d190341c64640d03c6018043c040003000240381541c030b810880d0a250300c004207481d00d44507502001681c0c01064010101e0150420101041d203003800d00c03440080301c61 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 76704956 1250 76703706 76703713
    0xf04020f090d1b0303020d122306010e0406080f06160203030a09060204050402030406020714010e03121510090807060206060f06130306050112031704080304021002030904060f09051503 81
    0x44030300800401c042c9880c0101e44154007520107283c00103140c00000002c5009401134000880e075010020a2083c0003100c418030240b030071420450b003044d58040700002d54094580c003401c6407aa0310040e240e68020028455000c0c0c1490004038120102003446000c000c2e0705070840d00c054503440e00300c0c45001200c1c0d1042c2e00684c010310020311b0200490f04802c0503d4003a074801882c00ea210002328003a80d100b100d064841e1500018134a0401c4141c4807030601c0c088015000300032400c60218a291284524800620441d07450404903407201440176640c51400d20040002c1d11680510001505920340c0f413043d0703100c9008030f400c0014410300100b02a4400e40c0020861703403400e44650100400307a08448196075030400748031001700019074140f05040c042d20b01988910030b640703c0c038070300242a1000d00440d40940d0402c4800d1000081c000410740e50840e904865591703032054649412450750141a0007107500034101000003e40c106400e491000342c1d1307a040c02c01d11140d41da09101c100000900d11791039030143d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 76706206 1250 76704956 76704967
    0xc0f18070503130c060302031905040b0c0c07080114060a120b010b0c19060b040c0203070b04020f03031c0506100f090603020904181b0e0103080306150705100b0f04020f 74
    0x744910001c41c0d10012849482e00000d80760b4541c2100c1c60000d4201501003640041444502d841108807465096a81c040c01d118500c0d255540034961200075000d900710040100e01003280090030301c5510060402c420080050048421003081c84110654865006400d00c0700701081c0c0300940015030080a8222100b41942d900c3c103540004141d00164400580b4000e40c07250007034480c0d50107012100ca600454001c60004000d07410403084488840204040d50b00c10050b40001514440c001540076804507043d9003007000d95804039045101e940d00710f51484c000c00c045034032820060350040d0702500040d26101780c100c80400c030070760381040f09000e9040800c3e10721004002c56440303900204a51f5038040e0004c0760340200c2d800403000e030030b405407000c6401514520b80003c1000340c580c41d0f080201071a0461107541e52454803041454400984101d015055140d01100244072840c211680f171548001210402140d501181c402040315100310303441101400c90b0403000c3d01d80b038026640c9a103100c00b031152508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 76707456 1250 76706206 76706221
    0x3010b040510110613170a021b0409170c060c030105130b15070c0806060406050a06030c0306030b0412080105010201050c0a1107030204021b010608070612020d0f0c020c0f18 76
    0x114050621204024010034040c0c4501020b10900d17000d003070641c0518803031003440c0c542110440003160f09030301c03401820b000d10700b00f06074006070285d42c0c0e0700028040180c41d5030000c0400c01401c00000c0c040c1600588031030103420b1890310002084405443c00580f0240d88840d00e00c4482c5120030b10540358840000705011840ca1040c1d0320840300c2680040448802102e07811040100350441d55080d0b4249240800c01c215428007404081e9100c0021181042a90b040400203140c42006014050802d6950006664030714002e40c0403030060764000007400c54524051a00e14403184c64450308000203510600006910350050184500801c0000724041c10640c0c0c0303280403500c4002d01240f0703503101c3c4100040000541c9491004088054081040743c15082c0e0f00702040713003500c2d1641e000081e01d511100c000c119596102141032025042c1c0c40c005070381c8500700052034019001034892441d0440c506840c0b481829000200c0303803804102540c1c2e004d5181046410400c40510040f10702ca8101403060008224 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 76708706 1250 76707456 76707469
    0x311030c0a09020c010b040c02010b0f0d0308041202070e040c050103230c0705010f0c02011b0203040f090f0e1614090907090207150207030206041106030702120c070e090309010e0603010b0405 84
    0x104d0362500000780b44901c01000900350741c26005402d0160359115074088841c1003190515103001d5043c3d58100c500301c11960020241d0324010005058400d8030280c10703410b01d1080c00f102008044034400928242814100340118003103c0c0708282c08240341c00c200607003400140c844041291121240c001c1300d66221340d4080002d6101d8803041326139559440203c0e03d41d44407445000e44281e8141d00002d82c8210701454042051400070906066500a000c10000003243c0f200640581e111108040340c14112a606440a821386032010740c0140121100d4100325184051010101e5002d031031101204400c4009002e0007c40c184c503540b4107a04001028490465141c0081035024400c9030520f0010240c01c00450407038004038800c8006811a505100c184882003030200c2d48100129441461820071060185d82c4200720601040b1450000c0b4007000f5014050015400410140500940501d0f00000c3c0a44a6000c1c100303090100b0516031040c15541409401d4a050700c1c0c0707460400c0d10381030828040040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 76709956 1250 76708706 76708717
    0x80a0c03051b0c01140f0a18120518030a0605070e0a060e060c070513020403030806120a030806060405030a150c110303220f0602030a0b010e150d0905030c070311030c0a0902 76
    0x51036403201510990501e04402543c0300300c8080c00b4180050500b0107c031b4094601d440c1d80410f643d42c41c0c0c08454081550700300e111040c600103080c91a030300d0b003481404605c00b40d128140142e00d80a620b210409000c4a50441403049107a03503070304481b040c0c42c4000c000c950708881c015140001d4150002d25000d040032002001c0f0000d80f1811610200d5032500090030a50b0301d0030a20350003607000300341003040641064215400440c21140000440e051101c482c1e074031a0385c580c02804010300e03180411200d8031001c0858010344800b8059850741c03e002d0500e0b2065400032650442e103035140c61030900d5001e100c4c051003c82500450b000c8c41c51500d40070390910f05003031001c4000708807000c0041410006900601684c440c1403243c0380c0561a4034008000c2400c48112140007810300045030b592103180d6440791030101684e1254070b9002e445107602880355008150381c40c4000d200d40300c0007070100440c40e00014154222407251400c18901003440c414540c90300315981030950000600b40c0e061141c02e0550f0044c01c0e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 76711206 1250 76709956 76709977
    0x1110020309013c06050607110d06020a030204060e10020d08181e01140c0a0c080705010f09020a080d02031b0c09010905060a0503060408030103020108040f0b0403080a0c03051b 77
    0x200074070380c10f001c118100c9800110101c81410721840120307006000c01880080020a07a0420409242401140c00c91184000003810b003401c946000a50360707034240040868a0300036008640722007004030064000e6025002d01800b140124500880a151030840303000301002980c0500b40c1d425a22030107440072003010340307414900b5000245000c00e0f5503081018400c59002c1c56203646108580404440c00c403070301d1500e03e0040700c850008000420b505181180c4018410745012807100d5440e05141605016020000303140d54209610540b82000c250031000c0101c0c001c031030b0803003040d035038410855440e0380c0640c0110240e0021701c0318281c001c1d012041c401c1d490314ac01e429145000500000206131030340c240c00245007107070740e41e040c48ac0e03d0400703000900180605800a14050405494024890005200084c1001a036000040800000008900025501001080c024100380c900904044400c40f503031101c080c030b07084903040301610a0244d2030040741c1c4141c0f022101181982d0b41c000d158005071200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 76712456 1250 76711206 76711211
    0x106140d08031e070302040e01060305040302070303112d06160c02010e010903080d06170705090c0a0e0a23011d150f040e0108011103010f2309090d080106111002030901 74
    0x4942c40811008407900c13811599800580c1c0c0d60034440703908030400042e0018007c052070901044000f980014031007090780c0d05420a5000ec0d415260142d00d05039150078105140c1010a844203098200c3c02d03082521054001c085c0c600d00e40d58030464190320018045202c0014651030342180242d402505240304244042c9841043ca82d02c0b9142c0740745c0e691261090740307812552080c0403c16440c030f5141c0e000c648805180503001107880c1c0400035002030701c0134080e200140b4000600c202014000d4041c0c01e05000301500c1e00e071503103075035200300300a10304103140b0003690480e10140c1d080705603c203001e40d990481c400c03002c091000d001e0205110000c1460210204445020089030042c440448040c00040102800c001610340c1030040250035200b6011070903c07336410620040c1f0104165905da1003e41d80100179510421800d280f496904140340e100d41c0d0b4210700c4610500103406404201c0030f04018090710740c00000e03640c481c2c0c100c404e2a40c000b01c01d541500041042c0114150b540c00554109840b807001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 76713706 1250 76712456 76712491
    0x80a0b030c1507021905060406030b0a090e03040e10380315010207050306150108090c06070305030402011803081b0f120301051201110a21060b0301080106140d0803 72
    0x86414088a002000c0728101c011480c0c008610f0401400d580c4445d00d0300c0d01e0640c461414010412a000d14003442040c96220500c1320351507141e100c19080106034040e000d1284485995103141c40380d10600031a54001501d1001503462860b10a1b001c0403509203074440c00e0418440c0321181c1c00e41c481c1d0800030002219a000d01440030398001c02650203202c59894184030842c0d12400a0328008440c1c4c041e03800f0703403c00c1c0d00b08207440b14240d91007a10342c1d03000e0070808250341d5907100003070074204203a550383c2d801140440c40230709159211000d540304500c00e0322400011b1812949070007040c0514407006160a038100403d074141d81042980d01c0803020543c0494411500c050701060602c1c444030300706901200b000c40100f1140ca040c9544180f18400000200004504c2e00c1c00010b25101d0014a04140203075448440c040c062084000c90400130440401c01403542c450909160319030080c070402801c1d6080120104101c81c02c081c10700300c02c180040c502c4011074070a82d510030890700700802c0446400403603a40d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 76714956 1250 76713706 76713709
    0x20a0915020a06140a1d0a120203120a1506020109020306010618080f01050f0f0708150a081e0705060c06060f0607080a05090108071119050102040506070f020306070c03080a0b030c 79
    0x10150082d0040c414000c817071811011318001c86000103c03012100d942841e6540100e800822490842030300100045248180600281c1c91889401d04c01e038400e41c8001d08204903e00588c0c08a0301c1300b034207488658032070b0744c2c0da0070100c1c00d8555010740a5803680204004000090281051186c4c00c6181e28414a0155480b0901c90406800c100500501d94403001000191444400c009511804009488020381007801006210400081c0342410080d00f81d40130300c5051b03036203401c1c203401051100110707580c40801001c030b1620080760016003a400c0c45560404101ca28040d01603600c1c000ca070308024a00c5950b40c0081180d091881006141c0040c020010030001c1120000101000c100d80d484a5950f42a80c00c00140306103070081c070792001c01103e201a400048000f18054241100903458030340342c01c060741006402032040b40d10150f80903600040103003c00c0000d00880c64000c4c02107054400d03907031301d40c80e0540e19030b0040c8900600242d0001d000030210310080d4480c3c0b89141c0041e00b103e006000080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 76716206 1250 76714956 76714961
    0x3021c0f0e0f1003020301051005040b0d0507050f210a1b030f0608070308130506070803040201120e060106090603060b0a020a030f020f120702040b0d02090a02071b0303080910020a0915020a06 84
    0x241c203c0042e40010050149041280c000c0364000d02900c2c1c00c610305460102c03e55180c2c0580c550280d816500c0f81d0200761a5485a02511100b05e414000c55555a01c500512141200308030306140200c2014400112045d80d144506034034520745040b0381d075080c50390040441c000c1a0100c01c0442c400e03581c80c0c0108494000f00520005544528041542e803100000710100200084d403010380f00360400c0100030000380d541c4007aa80c20590a0070011844000064100003401d542038580b4a40c2c8202d80001540641c00445801150030640f410802c65441d5003551145104040e050405684130b52491300001b4070902d880000c02d003440c81030314038142c01d007411542400d400d030301910012840800c01d00c3c2986494400d80c1e0348500d00702c5080030786600d5a0f0101c0e200e0140101860030f07050f0f0210b2414140051003034901e481c04e5178225103c010b41e44034900030740000410341e080b401c580f198110b921070807460761003100d50090342611107200b44d034546048000c80c1814480c40c0301c21400361421a400040c410b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 76717456 1250 76716206 76716229
    0x40303030605010207120c050103230705040611030c0706080402011e0c0618020d2901080d090e01030803010504111c09050c01020a0b060d0804030b0a0903021c0f0e0f 73
    0xda0380410380519020009140000540210f5850301c0d5011042c0000384401140318200d0b01c003808c010174009400440b6041d000380c0700c1d1800142401070340402200b2603110005000b660565241c0301c500760030703a0304156a01d004603040b40b00740354880c003070500100f07002e0550103038810701c1454003080011030605200060710b03407215142c001c80c100c00044410003405028032411403000c1c14804540700c5007030b00024002d880c1080e0103002400c162549540726080f61040043e4010003140b01e50341960355000155540b40e0360340481000484060300031400404003011641280c0c0c00c62403003030459003414100b00041c00d0021040d905003108008810140c46c200e44900b80f000c5040c0c40000321603549040090038080398665460442d04041104400a41d1860405800c52415140042c49003a5480d11800502c65074101500005801c020000d040e42d40350050700e4014440d50075503450010311250044000030308182d41010501d01c2d40c4400c18144100e080d061040c10040401440000144c04903101d030014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 76718706 1250 76717456 76717463
    0xe031201050310020703120504050c0303070f1401021c0b042d060e13061a0604180606020705060304020f030a080c15060d23030403020a15030c0f080a110705030403 72
    0x9401040507140900c10a19604050343c41503140421a0307500030034200324201c0c1411050b40d1303071001c6424020100a074000c41100501204c0e915205820f20946104070f11104070b48841000b100c2d8805c101060080c4c414506000210540c105a05403010029003000e4a0441c0c115a4803940c0f111010561012448042100f17202d02d50030515410a0105981e0690003880b40108044107004000b108034001d070f00c1d05a000703c0300240a0b6544008052040400e00c036203980071034042000f00740490840c2c690394484822082c20000c0540d115000c0ea240c00b45031003425440a0300340005405400c00d200c15000310b01006080c0ca0505a07141d413844269080700c07500d51104d502aa00100c00e00e001c4542258000504945000404c2c0459035246d080c403000c101d0007110703d1490301020300800400c00540d000f03107030b00528403000d06071181d054041c940541580300340007a0820095000c3c46005000501c91065147d032011069a03820100b14003605074014900300c0c0a00400250021407024809000998071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 76719956 1250 76718706 76718737
    0xf18030c08060702060601210212090d091a030105041e0516020f0c13020c150702150a0b010e12030c120903010e030c060f0703110703030c080705071e060e03 69
    0x303040c64a0310b480001400304066600c008144125683c002041c2c41003030700c001c035080c0c01c42810018218060300489659040c0c180e103d80034411030400c04201c800280744541e0301c0c5854669910546020640e0204c504184907204200520032400c0c550001c80480144090494810070400100011554219142d200d10081c05201c0040e8503414091043c138421704074001c00320142450005202d500d400000c1c02c83c45a0b000680141480080c00b00c01201041085030340d8180c9000c10740603440c0c21000852903500c51600000680e1824284615400002c06951343c03090200038006100b5410380511110405100500610b01e808800300058a20406000c0a140c0c82d88501c034281030035550340e402400c566401c14000207640c0340f0001340b055408082c0d085e60000507190004294020b10346050010710100700081e1020074140c140d080310f000c0610320703a5811032a584081048640380504c400040c9140c0d441560720404103d000c0200030b226010b040000340d540090750300c003032a42d0301c0041c006500c0300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 76721206 1250 76719956 76719959
    0x11a0f13060806030d08010e04021206070f122d021903020903070e011a030a1409010207031701081009050309060c07030302010f021213110a0f091107120f18030c 71
    0xc0d4071020b00c5030000410350042c461400c03602c0001d81001014003801100500d40e400140039941c0b9040d080b0040f00b070280641c5c01c2c60402c0c0d40c0c001c28402c0405403510200d17010500711009200c440c030a08055080c450f0200700403407043d0010030464040b005206c4800c54007405001d40d003650640c40000c0d071280d56180103a585d03200b20305140c00c08940364000c000003122140108180b41c900d0307c989050752000e09449689a80ba51044001003506000e40e050002d07c500401054960560003404050300a13111500b1108000100a1044000340103141e07194200351010380e1855032a4204140b100d100744243c030308290044000c940c81d0340000808075050760000303104006143c3c083c0f26031044440c55480552a120070360310440c0d03a030513010f440d14507032400c01c00500051052100c822242c014006051600f41a5502441c3c901d1264034000c0404c85840d003100c040c2c42504010460310746651042241c010f2203d400f40565400c5c0c200480c610501034001ca01103030340c12040e0491005144a0442130b110f45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 76722456 1250 76721206 76721219
    0xf0c140303090c120c01020303040f080d06030303050601031406130906060e0403050910020106290706050a0506010e0307052b0c060302190507020a140d02031506091e011a0f13 77
    0x40d88034240404c5540c01012061034aa6408800c8960082d049011204200814501304c0f1076441401d100c80c0c0540d1408030701004140d490380003180515826070702400300d0480800641e1414400741c0e007041c0d02401500f4021190b1016400c0807601c60b014003000244c240e035a10001407407480c100e40440000d04005110b000601c2d1544412568a011344004c0200314140204541c1003240640e0040107400d0004040b440000749401319810281c0c41841408142050005d00c0044c00040e5102404580c503034a42d4030441c00e0002c0c101040f5070f0028002001a049a0a98500d1107482d18041d00f00c81d00605c4a64040b40180192100814140e076005075140a50080b500e0022504101d500c20080100005070150b510502c01c2c0007920444544602c0c030301c0742413000804207012000000c2d003500505000c0c500800c4000c0d03403144039210965440c0d009664070708907400c00000e000d0f41643c100c5a00c10050002c03042d007031a117150301000b603000d045c6070000c240401e10140c0c0204c5945043c01c2d00a0005000303c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 76723706 1250 76722456 76722469
    0x501110a0807090806060418020316080d0527030c0d0b0103060b0f03100f1d03030420010503010e070c080c030c01061e030305090f1503180303070f0c140303090c 71
    0x4040b0360b01d88648000d0414524a440b208003503e078500c02c5850740c1c2501c5040d10801ca11000c0036034028111041c41c50b00e18942d00303c110fa03038800c251b224000c001040c102d0301d02032011981a00050418070f0040c264001c015413400c20107801d1143c2521840354200f201c0e8a40031181c044035070081d07120340d0042d8554900001070381e103101c904a00034411950141903a88002400710304040c00c0c0d400101d0008400d60030807004000070300d401d5503019a5910700c0144030b9408002103004030b0065204408110038070309681c0c00805070001e10303400507400300010000d500030313126002e42008440c9401440c9040c40c0d00c513141d007900003256403120364000087e4030300420004d120702e1008140300c0030800b83c454000c50417030041d0480f5100140031b0042c00541000e03130340e44034980c3d0881120000c11110f4145020904031040f5001160328200c1013592950004000200200396841080a559081040c22800004813846002c1200803160180d051440c10017010060000c0c0d4840c0080c13a0082540212482c10041c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 76724956 1250 76723706 76723711
    0x90203013602060a05030405010e03040b0a090902030112080a03020909100e18060703020d0204050a0b0403030207060302031014010e03060103030e031218010f050d020a030b1f0e09130501110a08 85
    0x310084514118016224a03041d100c0343c0d081418910386175980c0c8d09049000d003070143ea0b0840a8000000d000c690035881c900540115045c1396a440c20a689641648089200c00c2c0210400c04110784182d20004244000420380003016240140c100034040020a07206017080d1941d040b85640c801d024400300108401070341e4000b114190f070300100040c0b01110703030710f420000d024503003056000501040c201a41d80c0444000302809085481a40d03030340c0c002004c054101d030008034014042c400c000940c00e48240207490040315164076807080c5030303e40040f82c00c20002c00c041803414804014448403040d42c09106907402940aa100c2004207805a410036092041640c0c0c1000040401d1003840c4428000c80041d0070054000e00f8950010803904500b40d450340640380d203182813540000395404450b070345031300a0702e0801b005483c030600c90301c210090390101014400d203880014000c5c042480d0070380f50070200241c000250007041d0b010a807042d15542c0c203541182c8030048110100051942da950b61009070a50b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 76726206 1250 76724956 76725041
    0xb04051219020118030503120a051602071202131d0706210509070f08100c0302070321020d090c14060306100e04110d09060b01020d0c060f09020301 65
    0x241200704900140d98000100d4019041002203201c289011481c0c81304000a95044800c90307485040c1c1108400041404580d211002400c00c0c0100c3d81c0520300c4007240e003140c1e0840d005059541d0400c100f040300040c0190003664420350501261910036203a124510303041720b480d40405649003a40400614201d11a44000708000540000040d106814141008600b400b03d5010400380c981c1a94203140a86030381043e100c80e5803d000005400c840050060380220720030340144460410341c84203034220b014028020340410f202540c04010b035500712101c0104a5504000103040060300c04c0c0040c225010503108668688241c0f0050085003010400c0368034211045952910314078051011132420600c401c42241030081c00079040013195074641203001c1d4000324000450311650100804400340c4104c40050302e4140c07501c101c1088079440880c03030b2907001c4016141c507c84031032070390781e0940104680d440d1884840c1e501c042e4840180d4080c01280041080070300000031700040250076210603d0240b2200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 76727456 1250 76726206 76726213
    0xb03010e07140d050f030a020601030b01050105030c0724110405010815030a260d0b010e03010903020706110109080a05070b010906030c030b06030a06050702030408100203060a0b070201050f040b040512 88
    0x1c00066010a80b103008258040d80e50205107011890210314080c20b62481202501000c9401c00c846c9030b002070187d0480e40100c45a072401e0341ea810041d5414402501d40d0001914104503203004103000820003e070402010782d03903111400031601c41c241110079401e040060b0000c001410002d42d070f4040109500700c100d010303041784094510780001e9070301c4107048802003074400c040742201040301100009542080810002c0c40e50307000e440507100b0041148506450101d600c3c40302000c81d5040500c2003112565060300205402814250160344042d550b800450066480304204000584044003070625806076031101d5459618034030b00713041c151005820020516281c0601040400c0c5603203030290449800040000c0d05407541d6000c24201140948043c14076820031041c480510fa002004000701d508039400c0d20122850b10380c214003a44016620180e10800c0d1000030301800345c45800501003544141486842c0050645440c991904107511022001c040450200014280703682017a01401024000c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 76728706 1250 76727456 76727459
    0x504050105030c01080702030706020c0a03080a0b180c0d020d0204050906030f030a0f03180309080c01020f0c131b030b01031109030d030e010b040207150b03161502030d02030a0b03010e07 82
    0x2107a50340042862030f604000c0f0079004940d40a000784210f8a000360048003d5580d40c03d01c0003e80d03540e8031607140840000310090001414800648200802c0c50030091100a02c02003a800404625002801d003c2212108024044626800b8801040d150440c0c150268032586020100031401000a15480c000e0b0401003c0c1c2d10400000f00480340c80d421a07060402909170803003004c0f002046121400e0f00208030a44501c403c2c541c0240141c8101d074840c4040303c1d215860640126181c0103169103032030056100c1d9030b4003403483c034145182c4007141070320520014003100752801140051007401110004030340d840c900d050030b65902d80640e10240101c41c045d01d150018a0020981d108920598401055611190311001c0700c0d084d003142c000424020010754607001c06040c01c0c4800310742101e0080b051890700f90b01c1c603d80d041c040787c400b0640d1014221009286c1c034211901c001c1c9a80405249c0440c0010040c0540d00140744c8003440c0118000640050300761080000c0c1030031514028425409640070800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 76729956 1250 76728706 76728709
    0x9030b070801030308010303050a090522060f1409060f0a1e0608040305160c1701021b010903080c070c03020a06090810110d09050c09040b0609010e0c0706180b09160504050105 77
    0x170b480d04403549413a009130303203c60010f002c54005506812040c0d2100900c000342c0e855017912388480d2161b0621000402401c0c2c0e0b540440c3d0300b600d40a200f5114440b07130119036045180b903c1d08030240e2140e801303450586641030420004007022010341000141d9001c1e40c003903034081c1355000c0348800a04410700b0002034a08003a02c0140c55401000c03641402c1e128080010b104200e220714071032004204844446442007401a0b040d4040e40100201c181020b03003044010084500500500c00e1803901619080400c0d15407094202075544103002c2034803204c008920000068072090328001c005c114035500c1e00303140381c2070441441c1805442c2ca4845940c2e8142400109a4101001103034038943c032201e0000b507801c2c11171900034246841c12604981c8103074440d08210a00842c1c0c510684140c0c07080301e1025103a0b80b10882600b00f034202b650403035044001442000300280c22076020b000c000d40d07542c5a044040500760703281c400c0b10741c2c200c0b62005550040604035166014000e60080589411542800b0660400c030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 76731206 1250 76729956 76729967
    0x3150a0e07330203160c05030f0705090103060506120a05030307120203041110210509010b060a02030304060902060d0e0f0c040c050d020a0908030f21040b040f0c051009030b0708010303 81
    0x12055840220081010100b0798001c008441605c020102040d100400c40d042c288038440349485402d0090040e100d100c005880c2c0401e000b4240c5000401607501070b404d607218440207003002000f0306e0704002c0807900c24103441010031840c88110320403801150380b4501540d00a185605c1e214a0940340e500501c14040050152846000500300543d10005080035a00084620248803540240b0080f9281e01380c2603400b2180e004544505900c800920400040d9814011680f080c503500c80010b800a00100d40010400e0b002080340e60300090280d81000d54010000c41180c202c503001407002d82c803a40d04802c0f40c11050041c0120a5411103040220703003420709010b40070384201409403d03036507800640220001c0c015840d20000e00482e02c12680c61300642d50300f074046a40103001d02e2442d64414622718280514a0b080244181d902010b0401c9a84a41c0e0300c2c030003190f000c100c0490b07015400f140007040e540c584c0d40c030680001e85140c0e0b0380c1c1c10441c81d600b46a404034070003401110400c41d43e07900510100341c122 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 76732456 1250 76731206 76731269
    0x4121d06030a3810140d091712010f0605070803161707120e07080c06030a2406031125020f130f05010e0702060c1308070303030f0b010201060614070203150a0e07 71
    0x1400410420002d146c2018041e44003e0210010b09010414400703a0192714211810b8806245000d2210344c1c940009598500844c800104000741c20400680140708000c0645000300c068240500c400da41d000c820785210108482000001c0c1c1581e280440000c06406482c601280140c040c11a03d403d05076125102c44420205034094030000020a110702079551104075800910113010030503600c40da1a00001c0100c0b4881d140019081c10004d181194266080341c100c43c1c14488815940000e1030310040481c0c00ca03d50a90303101d0b1303064a5011140d101e100000301611825a80090524803c0302036030300b01d0b02e0603007044680020070310070441802d800084454100d0b8250b19020b850742e50003041c132046d0081c141c000980324020303c500001056095044407034412034420062080d02004c100480c00c9401034480c0744005000418000160f044510040c003c860001d002d44204521411501d00381170f5098403140d10165407407580d101300c0139042c026180a0194180c02100c2c2491a8014900101c80c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 76733706 1250 76732456 76732477
    0x304111009141c0b0a020712030203070815030114010b0a020706140a0e1c030201020a030506040c0e040f020d05010f05040608120f030709030b04121d06030a381014 72
    0x3143c09502c0c10a00d00f44020b0842c5502900284a504d00100900e000e50004981125903862000320026464000e00036a803040321295640c20840c0e590140302042a40c40e03158490301550303550a510f00f42000d41c890307680a40402c0740829513960728050002d14000c07142d0b0010041203054000d40142d9045c160880e00007124510f880b000315440c0d0000a00c595140044502d034110281000404154040d0054040f01400b502c041020380d4401003440144c4610310f0401c00050101c060084c0075103041c4d03004003444604807600505202140d03109201320349080c0c1102c64a0207418404000514090140c00301820a038405424803240c0c0c00b50401c40e40c01521840410b400c00407000030742c101e11443d6620000c54000e03004030b82c1420582401b1106410074143d00002a0010803094101140340508a440a0780901983d20396900c18101200402845190f503a98649103030340c40d1605082c0708261030140181100f40351000094a04208529840b07040f8003080c02038280c4106a1603110006482c5494203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 76734956 1250 76733706 76733719
    0x510091811070b10140d060f0b0424090c05040b0a12020a080a05010e090a0201030e070815010806060301051003020103092f0406090e06072003030411100914 69
    0x162841900003821555210144400c0d02141d10024881d400d1142c42c0180000728032100c0c010348407045121658500c0305d203c0d401054070203800d400107440342d01045415610010000b441641000014141d90707144101090307204441c0b402161003049070007120010204040104207401c00100041e0183c0181d01c80d0120046010407401902da009200c42c00415280c240110343e50000e41e040035008000c00d5884c1100d0604d450004602c1240c01e1107198007e1030010014400c03048140d00440140c5001c0c3c4041c02c0c0c078082c00c80009200c030404c0001708148105211039040c2d56060404151400f900200028426070402e001d0113000b5a00514500030341e902844c000c212222035040c0101d50b08040740348400a0000d440843c0283d02410700c0021035010111401d00009946001d190f040e03482c00031517448281c01600201c1d12203805103180b1203a221559031001e060b42580c00255044d500111402d940408118807800380e5807030010341c48004403815081c0000313580d0602c504080e0300085656120301440c0e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 76736206 1250 76734956 76734989
    0x903070f1b08070e0a0e06010621090501062d030f0b07020309031609110301030804090504020d060504030e011106070206040305090d02120709061706040303050c1908060a051009 78
    0x2600074101e8005800e04900f19401039958090541511300112414881c0c1890205000a00c02010400a0480d009542c680c1c101105200110058030b880781c2c6804a0160755880c131000184081c084c40d4001c1214408001c00c05101c144181d004214035401c20180ca00451000d20004820310040040b558103d860040641d076001000d80ca140314070420a68144510424001c03080c5043c0440030544d5a590024003540544e91710030400c5000070b0100070462242400305121041c515442107900c14001070503ca048002600c3d10b1088420a03142a0300084000d5503560031540c007c00c2c1070718038040c000024686845e1206009480e04c170003610050400400140802c03480d5204d0203000d0340582c0040081f01d420101c0e04041e40d54103014880d03641c0d43c0e418504005040780410ba4080c51003040c8601915046d621540c045000344001411005461418080c0500c4111402c228441007489621400b64074203001040003180c01c1554000780c85010070529030b0200c01d9100f07030100201c0c0d24107040b900044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 76737456 1250 76736206 76736243
    0x609100b0f0901090305190309140108180a080f0909070905181506040e0118050610050705150901020a02010f0506030c0f0f040c080a29060a030b0a0b120903070f 71
    0x1074403d40c000707000d44c415103070b00c1e0010040c041540e47c805c0e4800c3c1c80381e10500760349601e10181e120498400ba80030503203c00000e02c410100d59502c68400446c003003a14082d01c900d03610141c0c2030700a4042c40700707020702c04241da8011b8100804d00e04d41084680c1404074005180070002603c8400c4010a000031044450201d4401d00e140c240b8148030240c018607841d1980c2d203400c01d01c21440024841c2a0101042e40d9130b01070380308214482c05020342d9020b00301c01904844220240c481d6030003000110b40504c20a038031655421502c64800b80299007002c0056507032115240d0007400c0d5640d4074030b407085c520b207400240591990001003d810321a401c1e0340d50a202c4000b03400098001025903001a001800d01d8011500541d102c4591445101e1445041104800c08402d51182e208000b4980c3c050003070340c075031071561881c2c00070181210030000d00c0d011420f12210340c04120981d009510032031403d84041428015105c90205969005005000950508030701d9100e0352107801d00f640d40984030300118030044c03030700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 76738706 1250 76737456 76737467
    0x1021506060c0c090106030f060e07201207031205091b13020d09060c02060112020a03170c15190207050c0405040f0b0108060106110d090618031a0609100b0f0901 71
    0x2000d000410304c4201c0c1da551200500030301004041c03003240c103140000109108040d501114040c58903581c8e4195611280c01c401282800d65245420252054240c1040042e045000400e000d912944d5040c0100da000c8000030300b5628041c14401c05600084000d03101c1541202852041c14002c582c41200981c400450360700a12507005260411b03810944844c0c184081c039084104441c0b4944c0c01c0301c10b140c0e80c40000035840c1d4088503000b0741c00700015008101107030300320048000320340c40f0402251418000d0503003a445c1c851440c4072006088690802c008141c10000c1265201d030801d80c0056181c400b456442c0c644442882980074480d80e60b070808101408400f01842148a50044132010903585480a13966590001d11030b0800180042c540e019100f000491601c4d4003801c00d403180c407056400e00d80c05803035861200260040180c075022000000c80e20310704445200c510751078140d1929050000a016a10304000e00204420035040c208020289031042140c030b0f20040c003501d050f201d10906004941 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 76739956 1250 76738706 76738723
    0x1802030105040c0302090f090d0302031b160615030206071205040b03011220010f0e010e0d1401050601030902240d110901030c030e120f07050304080d0e01021506060c 73
    0x405618081c1000100319031040c05205607030081312680c4050f51910181c400c241801c88d00c280d1a070300110700ba008100e0003a0007071604041218103562035075854641106894000006807109042d0b04452003080c00540e04c00d8810500d21035600380c2c61703541145c012039403510070700200500c7c101c0c001d95a481d40b24454002d640280501e203600076900d5070342e4070080302c0024000c2015a4402881910090004145901800f000f40d06031111080381d03402c9071080c0d03000000660001d0500c039460701c0f1014140d4562404514007885501508100c4842d610040d003180c000134525818103103050400300c05665000c028049450710541c003501c04489440040300c0c240034000140314040d0415187c4641145c03000e001d03194480007a60100a500740b4890102c05075621154074080c19080303c90300000140c403c01c000c010200180c6000c030300d08012580c0c0d103480c40c0d0043d07000c1ca030750b40c00100940400f95803064038054030301824401000f000400030035200d486a400341100d407103403000149581081c0c5060007241c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 76741206 1250 76739956 76739959
    0x6010f2102070318120f060b0d0618110909070315110d050a180c0b0901031407080603060a050906060105160b04030e011b08030f04030c0c0803070c0602010e0c01031802 74
    0x6454400b14500541001c40350500c400001c40c55044c041038512025109008507038024500c401c00c0c0100340c96000041611004c0c45402410111151012070411300803400500c030702641207180940c89084c1202e4440b0301c0c00c101845005001b050201050740018031400f0b594101d0b40a46030310703003000041c1d80201403140982c2c5184201044440000380564030103481508416802e110130000302e0500c80000701e000c0c0d0300a00c00340b0240014000d000d400800b51020038418100042e00e68a0744102c0300c581002200c204000803038480800165040034006660003080c5078000740164200b004115403540c1000340a281081030108601d050340c0c9039803213a40d25030781c0c200300704800508003410024055118a200310f070204503001290504001c10b03044a603d103d0700107142a0868907060440300c00300102400503020450300000031004540c813402880c00a208800047d42d4448407468a0882401070307030320800a591400c2d186614100011401011141d000d2800045c11b044039072010501090109010b03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 76742456 1250 76741206 76741211
    0x50c0706050601020703320a020a06030b03030d060b03101203050414060405090a0e010501080d09030b13080c100b04062301030204080106060201020304050c03070f0603050c071205180906010f21 85
    0x4040172640c0f4214440300d20501d40010387e1450b0b1880305541c5c2042d80320003074000300c000f582082203606ca94042e48810328024292854120214118416030b1035179002040304d0b010020a003c035541000c2108001070905400010071164a0380380a4070500480c1305a680910404110079215961881120050301000748100854240255200700030480c4510828080d0f28250012410120000e503104042606640306140941950b850f100c0051028064507060b05280200e080000e1079031000e00b00e00745500006100500c1c0c0c9040020036990340c2900d8a00803440c0072410300c85080518521090f11040303440b48401201e088004a00030302c25540f01c070015500e00100400c002c1e5041d00154040c5000b481100c80031010507003096201c004a20a0b0710500b201d0400801090740203130401680034000385c240754142000e41d128840624034120082e800106d00151141e5413607000c1144498000c8141c0b03804c1000d25248001a1950811902a07014041c1071707843c2c070b200c0c8040000b03444450000320005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 76743706 1250 76742456 76742483
    0x141b040909080d0b01050903030d020f041a0a0201060e010506030604051305060907030309050a301a01030303051501020c040e0c1e0102060a02130302010c02040e07031103010c03050c0706050601020703 88
    0x140b0140d81148a520046500740039110003150301c20015203207034120040140d444c012170750340c00a000303521100405005507401d05c800a071040480c2e11031121080c024a4046d074030100346400a00310b40d0740c4d4005d2440317901100f0051005440c0d4209582d48030006880c001041d0702e62003911040040c0045008019114490421070042004180001124425298001c40d0b54640c420490000082d002d01d020024040c64142c0c420746086420340c4040750308001e0103c00340190b40710000d29a100b41141d100b000e4100f0010810144c0c144032303665001500c0c0200151100042c00002e4070352440041e0244983e480f0b40309540b03204000d0011285032800101000d03400b0740d50180c5a6002101c880f0300d01d01501409000914054081c0221990304403a6001c04940604650054941110040050b42c01c1650b46d601200301e1f0f58200460350285000320612004207815104050941e110200701200300340c00c02d4140f1148084000565002551200c80868240c0d03411004078601522944054991807480304d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 76744956 1250 76743706 76743713
    0x2011808010b0418020303030402190308040f06081e0a0507050d060e010501020c0d05060636011a12010e04050307050604081201060906020a02010f02070b0c100506010201141b040909 80
    0x849070300c22a003920240924480700d031000e4154004444d001c3e4054104100040061516044228a8103810700c2ea002e4042d4494a50764041d8005400c002181141110306001460b08401c001d03500c008014181403c61a120089101ca08000703003001c03c03915103c00c08244410b000350306945001c5040c1d8003c001c0715507030729200ba00c2c03050280708242c090300074a00ca2400710b051840103844815003000060140e0303101c2505202c60040145440c040d49010341900034868034540300c0c0c03003001010042000100d94101000206200e80f080703040c21402c10308201c0da04000102c455500c3c115a4140420f00ea0307130380c3e9810980d0a5108081c0018414002c02c001c0004101c1d0b010082c100200b42501f8480042ea00d9120586090302207000b04030140e40040303e0301006611843c441c2105c3d101a205440340c080e43c441662400da04003440340034094000300c0310440907000ba440313500c0e488082440284402c1803158a2402c208a010701180b1184841049007410444448101c0b4001d2043c01000c010232a160704 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 76746206 1250 76744956 76744961
    0x31406030d2307240e060f1308030f0402030f010213121505040803011e0b12070908010e0309010329101106070e1305010b09130b1002030a0207090c0504030b040201180801 75
    0x8a004491034180c0d110b10380180765417045000d840011001400641c681004c0711a0300c0701300400a0950a50b1041900006005030024501a064000702110142010700c105424400072161407405680b0600400c60151000d54554084030b082d9100e5054002041c103007417440007941c1d44c11048050808041c802009040e0000354103d90140340c2d046c1034144d51006c02c0074140341d40d10510303800714818840c00c42d00c4044103200c16044005424403107001030740c4408641c2542c8207030020481c5500041071000013941c01d4010b991000900211014100c214851103114058481882d02c2c081c00b01c154a00030300d180101304100100a250048820500c0d284100420181802055600510030000301040c10929402164103841111241ba0b04240700c03c0140503d011006250306007041c0c440600c250142c03030341c07642200203400541c06580e0b01d500500000e8581161984040940e501d04488240d85c140c0c40703010b403010360b0740c0320185044644035400100e42e81c22002c2290019425800790000c0c8520055 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 76747456 1250 76746206 76746233
    0x402030403021e0c010507080d090f06050615030105030712080d020f04150203070b1b0702040f0b010e01110c1e04020a030c0207060203070b04060914031603031406030d2307 76
    0x12203002d80c500f4080c0010307603102d55860300011301040007400060300103104036000d050b115454601c0080d20405a4a6481c5400103240069072250b80e076000f407100a0400c0001c00701c6415402040601d03652405001c01d41d182d034284a9405803100c003c08013810090400103c44010921000c113548503030000c04407601641c403d101c1c5500c0701c140046070b9a600c2d40003205982d0502c9d0048039140c5a907507013060000710042d140408001039a0204074ac2070042c0c0d1540f0840c0c1c038600b964540000c3c4103422100240c01034107442c0001d41400b141d036540b41e6010303c0000750f030641c02c0e1083e9519030591880c0101c50051104001da40d951060010400a0000c0d6140c1d1107603150f05142c0c0d00320f0f0022685d6203c04d903120b10411901410041c0e251002601044080c0c220f11800343c4615803403c0e8405400c8001401d540084200030013900b41c3d550b41900f49039041c01072150b01808076803100c4044c1028400030f40d544101081520500444000340e0134600824110100c070350300b141d0181c07642e038011445e1028400041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 76748706 1250 76747456 76747483
    0x5131202010605190e06010e1201060617060a05030a0303020c0a0c0e160f0e010509030f0706110c04111c0b0303031815040f140c0a030b0f09060603190f02040203040302 74
    0x4003400c5500710507880d0648812540480e45ca000c407170301c4000c011107031902c0c1c20905c2c91f000b8051008041c100c000910a1000600b8035545117442c03176409418408030100003030549480384806000a000a03903021030b103029200d0385800c0040c1d4a90400c201c0f1424612411740242000c403030b1050004101e2050714180384608421911038101c0b90030081c0135955100e1403030781e120000b9042002000194011401420303c004000c0840f4845241044010f00d04000d0740c1086001603105410518000700401c070301800050202c50522a0300f0071900080b01901441440b00d24120107880a4011100554042b268210002d010b89589181079210210790754040d10812840e8401c681000c010b980700d04c020213000301e030300c0b0800d410492125111f1070b00d2110082051582805402c01c002c800c0e030f0702c0c0700403800154404d0048034414580101401c5c01c03410000c0c682089038020703000f001000c1c4c7c0c1c0840c3c920025150a04280447e401c9428840410070840500a4000d40b0010a01c824981c0000720401000326 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 76749956 1250 76748706 76748719
    0x10c0507140106080616020304030813060207081c050d0920031510030204090c08011b0905030c010c061104050d0f020406060f0906120e0118110d020a0905131202010605 74
    0x464522403c8440d207100d0082c0c02c0c0c2022010030000501180306691511081c811a0700f415140c2e150484603038000c03807850820194a040800540390144620401061040090803507580c0500218480991411080c0c0401c280058000000c41d01580102e81c90740c1c000351035035445547c42c1d10500c8111007610109100e071007181401040c0400d0303404414403400d0700320700004003245180c0c24080644147d03802160518a110000f1070401c4003445240040c070b00c400071004408030790000c0640807500c1c80e000680a60000d42c1c40c043d543e40c114000c030420700d40c00100012103164240c40303d00b0a000799003101c0d9004c892074000100748080c00b1001c110150003204c003008a95a103440689000310f25100b09404600f28041c01c21849000d14107036107049140c050041514800d0384907160854290040c4031700c40c0300b210890501813113020016162100b506680080900e41190005965402c030340c0306080701a510382002803090b0801d1550109001d070300c145584040340b40124064082c2002c2e0250501461 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 76751206 1250 76749956 76749983
    0x60403020c040f060b04050d0303180b0a0c080702031e091815060304150213120f05060c0f160206070209011211061c1505030d090e0a020a090e070c05010c0507 70
    0x1080c1d03100e0130382250807007612a403a02e4070348001d20051455a07102541030550329080505081d480c15001d021540c4200340008040c501300c0e0321711003102c0d540c2607030000704040d0804000c040e64000084820000b030f5202140080c1458403103181d1a403246601d140e81190b07800d1550321041c0c80021101e4000d4154400301003410203818107101c15030004440141c281d0040c01c900c1500c01d244e903401060700002c20f1180303844c010780310030340c0d0138041c031214400300c45040d0420403000030700c4014045290080400c01c02c480c90101001010001801982442c68070751030004407c0046586110071100c1490303010b0b00400041d0b940b142d908615030f0007283d0544d030040081400884038909041104d0341c0c045924003201c000764100601c1001485500d43c140340503040c0034000309041d03404115407042d46ea01035031a0101c031801d080c021065040058044510316005010311b1003440e0304103512400755942d40d60000c0040d61225400c039403000418001801d07079444d0500340840a94010014085d803401003d8075135096 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 76752456 1250 76751206 76751231
    0x70203072108130f1202030c030106030804062109050a0b090c06040b0c15040b0106020f030705030f0906040b04030605042f10182306040602100504030908060403020c04 74
    0x5040d41c40100240600308114400040c1194000e040124040b00310945110388681409008810542251080d03900c00b0130400d0852404000300408400f00307030000d12046146581e10b20b44c034000c9014050905c85040d00c110101d15102d200d16102c80318021007440b00d40c00a0a0080d211290140141c5045030f001300055200300d07000856403c60000580b446151a01d011001c0e004da41018110b94140c0c05a00395145a841180d002c05000e10701400300c541081d458160064904242005009903030f400521443c00410004000e41d40e00070780c100300d080e6860060300e000400700e103c1c58000201c4010302040102c2405901c0d4440c510451003502091418041082041c500c0e0311702e500c022070028019038403800f25003004080300e41c1007002030411521080340c0b105a5004c0c10515008401c0e000c248183d450109506060f203046240301c26203010340f0705400d02c1002915800c080f08a00b82d000d86600c0403800301071258000f2401880848181c40d034a042a14000b074444001d0b0440a116034240600e65146c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 76753706 1250 76752456 76752479
    0x1407030507020706120b0f2106010f030b0c0c011104030501140604060b07030e03012913020304020604061b0605010320030f150406020f0406090602120702100c140d020307020307 78
    0x1500d44c56128219081c410318a040f010703180c9403c109802001020301141c0c42d48802c10704a1106501c0d00d0148c502c1800d0412041c5803140507442421a444502010000b00304041d032000e41114481e291940e481d5400d001c0079014044820340160014000076001051002c10361290240010301802d141c85611a98204015100300b170203108083c0c00c00b0044040028000c0301e034544402d2001e4008543e100c0d5034200324050f0500c0c40b0031560b02140a2807028550310309040c011095043e030603801c504608090f00400c80d61b0049020b440280603042176810442d0802c40c81c005c03c07140e88080c081c031266840307240000240703d101d8210451104504011040e918000c22608040350707180c0010300c0d1407030741120701445580d8007801c1501d1450b0b0030414050030100990041020301810348842d0515864100c000b49000b90191103000c0960f400d00070400140d50f0050401030004203441e0600c0820703414100b4194a04503c00d56070050321503243c25401458020010f4100305000710f0a8039815555120701020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 76754956 1250 76753706 76753709
    0xb0109030206030112060f0e0c03010e031e1312150b01020609120a0e03030403050304180e07170c04060e060117150120190c0801090201020703060e1014070305070207 73
    0x42c40b00d41031006104000e14410941c1d109801240042070b07030726a09101c2803c17140b0040e9100d40d84d4020304410000c50509021b83d0302d80f90308400056141108000001e4000070110032009101c0100041c0448041c400d00b112401921480811207201c170040c4c81c051100a030281da12904160410380c0d590119070000c11f480e4440c00c45400545170001d108401c8008a9200a8400080c40015001c000e51030f04c0c2000034101840c1b14600440d9168180008100b00304c50040301c0201b45820044011103a900100e07406044500c80c1d42d1802401000c05819410300d00306000c020b401920380703040000c81800c001d000c940148401c1c0c0300c0c1d1200146052640f01d0390170040f10b204560420b0204402880d5218003151b00400a900c0000310083ca40d843c5281e00b405040d41070002c031484502008030034020400c81d018000c00307070314008003c0316060f81e00113500e40d5820300c0081e12265a42c01c0401c0800018049140742c0341c01d06608021450b1010b801072203485040e00d44400091814001688183c000900e020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 76756206 1250 76754956 76754959
    0x3110603090a08030901230103050708060403050702190909050a030e120604020d020a0e0a021909030b0403141b0109050c060a0816120f05060310050105010903020f030f03070b0405010b01090302 85
    0x9202c00143c075070f0f410661001c0c0142600d9035807041480740200b0300c1c0700130549900001e11140342c9545141000381c41c003455030f003110758150480380c140030019400c5411156001e40c140e40c120510f030084400c03800d0000302030340320a5070641080c000004014002c24100e05442c4241c482c000010045010711501c062807001180095107e9404540540382c20003a4011951008018a941544039540c2403003122050394251580d0340c021034400c40c15100b4210b1401c07428030b9490803000b80c0e8910b82b1410300b086000790000d41402102d10418030b60221180480c0c0300d181303802c5203041c005411154814024403945100f907907140214000904503203810011900307030828942c0d402c4410b03141c4a41a40708100d60410710b90600c401c584040010a0340ea005610384030409940c00600c0340340040c00c1c582882455169154940d2526005003c540c3c1c00a0800c0b09a0f50180c40203501c43e50300c000030038a80b0440c3d012954051101145031002c03c40001c1030544150700c18002400410b494000544601d4101d01009 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 76757456 1250 76756206 76756213
    0x12031a061303120503151507061802031207020f04020f0703141204060b09070201060602060c07030203130801050711012c010b0a0e070f092315040f0311060309 70
    0x241051038404040c04512506016000318142d4a81c0c80c0f4622800000c0d09101046010003080f400540d64000b103280345000b40c1701142d0540501c07240e040588119040204007581c0c0ea401c00040300c403034040c880107056001c0c0840c0c103008006032102c4400e401c0020304900c10010105200c00c0c0d400d050003610b04a0013000009800c02c882c03503034280d0307540c00c20a010002071035050044c0050416640300c00e034017860240c00005080c039040c10070300c108a940117044070296070401000b0017603039500042280e445204105515240d41803032030f0072411407080c0c4004854400300741b40042001c4078194051070046d00c054540c0031501c079070f10080c0381c2680c1ca00c8001075644282c0d4548510340c0003000740480240f458030f04c00040d0f944103500000b00c003607450f034110403206007103d000c2004442d040034000414440e181000d13016940341c4510215006150004030361541d181210b001d0075900e54a0030b95820706070140c5025111901d0701d40c405421451448181c8011102c807000180c242020000c4a0040e10808040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 76758706 1250 76757456 76757501
    0x109050d030c0c060203010f0302090606030603070e0c07020301050405010f050112120518091512011a100c0c060c060f09020319140106180606030b011205100906121203 74
    0x58000b480d80d640540140710306010481c00040035071000f14040c20140038100411401c1d80140100203d0007007125000d01e2040090011943e00007031f4440865a888aa5100c0e60f41c50580c2e10718a4001d40c4002034041d803c0800b808200101900304000700440c2d52070401c001daa0b601c030059400311f825400503008241034280c4000c0c00d40310360b000340501d410340311050900107415004103101c51821a5001c400c91300103401482141342c0b03205480f08816503407000380a80d800c0b40209007640069009100c3c41076500c0c60b4441a61402041c1c015141c98004c50083c1c440c5a85200241548480701012101240b500c951051055894400c503038505801500503c1d00d9201851b5000343d10941c0708090f5400c0d10680c5003080030030005d00422015107031000000c040940b443c95401e007964a00c1d0000400e160420110705031990b03020321070205621030440041015211001403810171040ca8200c1c0b007134a41000c401044001c215036886100d18800c005198603a18000c00840c00c03142d00c4214500444141400b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 76759956 1250 76758706 76758733
    0x2c070605040306050a0b0a06020615010930060501080a0c080a0305040603020d0e0706021e030a050a081317040510090501090b130e13050607020102070b0c03131703010f050102010905 80
    0x4c40d13584a400b080d00006d281c05500002170105285611610050b07200b6010803110618503000b8079007465081c00c10180d45410501340324110380904400828841c0c040009070281e0310514880c5495903000b0a01708100d507140d5001948803283d421f01074840c010340820005552000040034a0041e401d1f95440341802c1c00c0c00c1c0700b20042d44c005462841c1ca0f6031502603041081c2c50900c41c880c002c101907001014035403446d10281298004120340c41800c1d070003d0040700f02d0250001e0441d110517405244c0f10031039988590740b8071075444021401070300c42e040c441c4540c4481c000750802401680c5003215400f03400344520724115103c2c003a501810780010b4103039004000c81c42455002e4400c101382100b9103907a140e15450b900855176011115101014440c011160501c241480b2071600812644001c0d0f2401186441d0702c1018031028007040d940000003c0080d505440c441009a0090342c490702400d8074030b8408402e14490f400c28044d65000164800000620351f00520440705540e60010180044180c0a034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 76761206 1250 76759956 76759961
    0x50304020f0915040e01150602031204111201060602011d01020304020a030b0901060b0c06070f02070e010e040c090203072f0a0f11190602070902070b04020906010509042c070605040306 81
    0x80810500c40458143c4044566450240d1180d01494100003c0c00900e01c041040d480e00b62580620255001046011103001c030087d1401d40c82074209802082812548011a0118070101446040780d40381c0000070071119419040050385408010202c00d5a8401e983d02500b00d100c04d0300c0081d407140c0c101c9801c00004035500c00c8503900044d02c10000500755540d1615806591020180941c10b4009604100000d80c010301030b10018030080c402451030600b4507003042100d00040c05000f01802d40d0300c0004003013003425400c3e080a045034890039500d0f410b007000b01810b945d08031030317024261a5007682070400090b030142c405039440e00044001d202001603a100d2122401c103041e02a5503096000d9202401030b200c0140b07240b103000705820030025182c5040c4000707080462580041c0c900c1070041081102140c030500c9840e03042a0120b40c0c056540e03c035600103841c988202c1d5440c0c1d03040742c2015414910f0f5580b80b48a001940490500191625183c02d10a07440e240f96000e04404580305000a10206100342d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 76762456 1250 76761206 76761211
    0x180f05182d15010e16020d0e03010b0604060203030411100e0f04060905071101050a05060915040e0717070801060e0f040c0815160c110d060b0402030c040302010f050304020f09 77
    0x301204041c080102205800c0004440c1e802d000b0300000001002110201c081c42d0b9030003074000b1440035607040c5c00300000b5211100040b824041180c0100c2e4004030795000c0d4420700c40f2060042c103e550316692401c0103074603134108881c241c40003d080c0313800c0310503410540c800d1041c906440e941c3d4071160324030300d04101c03a64207003d43d0607400c66590800071a048945100300e900400c0e054a074500d004c4e2a100e101420741d00c0081c8041840f90a01e001c0c025951221520140c204514000120b442d40c0c01c80c1c081030092080f000700c0c0200380300b80c071800115000322092101e03c10380d4031000e940e034064440007031038261500c51007095441d03a808000114441520640c0343e030010b12403000156031030b03070303541d070483ca0108000d00c2c01e07005200c01401c0c418111144109441c006509040101d90a880340d01d0b0384601d1090240300e1402280800e1220702081070302d52104c071140400900071926400c082441400542240c001240460201d2091881c50f6000c0d01c192803040f50300410215102060b1000e220140c0c101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 76763706 1250 76762456 76762513
    0x162004140105100e0603130519120f0302191107051206010603091e05010b01120b0a0b0c0106090e0703030801080a08090f0609040f050a0b0111060a0b0604180f0518 72
    0xb9004911116070b5100005c40c0580481544400750201138100306082104202e078002700c82402e0b200d9100010701c0250729a0311000f01d410300d018140240e01043e03000c1e00c03d442035901d001241c026042141a0043c001d442501c80714000c60f052240c0b00d400f030022400041000d44843d5000034010410544243c2082c1000c80c8100e0900511800c540e03c0d01da06c02400800c11501a5100c161117926940d2280d0050b4180703419090621610440380b01080300030500703004409002c003000440c03c08059007504608024454078600700034a64145040b030352101ca0310701085000404403400002c4800002500d82020754015880c28901541c8004211545007810050360b00703c4401c0c0305032415941d40c0e120740800282d03117803804115841c0800d22082114541403589050010280340c40c1d101e49400a035482d84480c007a83c00183c0001f1440c000354940c0240d0744000c140743d20000408200c4880c41c0c06c06089810420414461034440ca90401c0c0809441ca07080c014552006e500341d01910014000035411182 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 76764956 1250 76763706 76763717
    0x610080c01031a0d030c0b010308090f0a0e0414031e030a060801020c060a0207050109060c0309141207300903030f020307080a0507030e0a0b0702280e090316200414010510 75
    0x500d958007c1c100707101740d02c207644181010404400f1414004254882400200c80da03a50581c18901c54215011016002500c0340c400105c1e0301554060801c100c641180f01c0940360b0209501a540c1c0b901c455004980a40c0c03a030f8140440002e40103414029641c00540000103045103a540b0b4000200030741000f00282c416649913810100419114407448560070300644d804500d0044a051822541c81d0640c00306d000c540c070074190030300e54001e14003c0e1144103a03c1407001c00c5001031721134a490390901d1184140c052260612622606582010f40082140d10035100c0105403600b209090f0b80300d0040d10300c040c1c03051400b00141ca51052040c00100100c52107824858004100540458070b5010107400c0010540b00001d2806c080d480c1c08000041d00c29820040070300341d920744020a4050b5010b5100c1c204c01c0500081c0881e0f88801d09005903613100508031503d080240070740c141000b00100c000c0700524091501507200700f0f01d0420b0300408401e00e551000061082c0d10704020f10202c0100040042c04000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 76766206 1250 76764956 76764977
    0x9020a031410020a031d1237030b0102060106080405070501050304081b030c01060b0715020f070f0503130602030306010f0e010903020429090f04020409060902030610080c01031a0d03 80
    0x101503c0508980c683c50703076001420900d05030b440031864504040c2d11880340c1c050545035507000301305c0003201e0000300d5051484000d4011703a00d4001030b090240a0080122501d140c40c0c0030156410341c4540c0041c80e00368200e4800d039a9406056a00039401d443c050081c1d00200014403a5501030746c021074110340302d444200d15054201d000e010740d4461940806400744c0001840344600d5000b405400b0190079800d500c00e10745110b03551001d580c2e8030a6109044aa90042195480004004240c454158004010f03205440345032810f582c82e54003400c01201171300742f40200070422900c00810f403845200e060b182e28030400981402655a129814800c40c10045e0140f0003000607120f500800400140e0b2501e2024005044401401851468643c4500803400c00302041200c1e91004802d0b078205406440000312240384e400d000c80a40940742c000703501480340909003d02c160040412008450781c24042d128070700c0b9036000440a1710b822118005940c0e454000c2c00c0824909403092000c068800d090035407000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 76767456 1250 76766206 76766233
    0x4020415080c030717150d0507030201141201140a15030b090709050d02010e150403050a060b01050307020703081c1a030106241404080d05040e0601030606050403060203060d0c090e1009020a0314 85
    0x400e0347d1008403956000305000b0421075030130455862910308102903490402040040e2050f5280c0144908108991074146510303c0740c035140c051b040a042c8140100c01c1480c20b0701c01c040c02520220f8a464010404000041c208500c940d0111041d150000d1803c0910310817500115401c100d00454545d02004a2104141211440004000542c8a1006400b010945040c078208913990702c1c010340e051040800c108002c0381d80c0860f0711004c2d25808202c05d601c440d1400000e40c1c031080d056161000d135910b4401c20b20310241714003040e035240d030000710000d01c41c580c1c03101401c0341c81043d01181c8100c2540c1e40303650040c0340f80c01645121030704c001c4075669509003030b40c4203032891405051440502c041180010148140000020400d41c45003081c01c1c14040c280c0fa16500602501c11440040c040b00c1e8080013041f4207a60b621038401c81c0c40e80250b8120a0f158655140100a100b07014400400d48034a0480c0410b032038960003201c080703d40040021000ca451512200d50b103410100c000080b03409442d0114110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 76768706 1250 76767456 76767469
    0x4021b0601090b0307080601080712030e0301021308211c090206030406240f03030509060705070f081513170d0203100311120d0e0a030204020415080c03071715 70
    0x342032582c0c0210f600f220308410300d410901507401c901b030903810a00050140c2d07040000c080040f034926842e961401a260f0504441d00000c0d01c1a450349540001040681855004901d03401c3d650900181c0b6040c07880c202d905040b034444a44182c01000b028000030101c00c0c4440d010299a0070361345000310b013201042e400241c44d82d204030380481c1c030155515a824501d00d4000da0240210080c00c0201c2c41071400e01c4000c1d00341c0c03045440000c081003400039491005072640b100399106d4a80c0301040b5003d039501e619082c050800140115486441810034118100c82c0c401141c134020000c101c0f110943d4166078442e4a003096408510345c8070700504221022000c52544003d500c10f80c80105a034100c14118506452550400d01505104424040588034480d102003581d0380344850f581002d04004281101084400320960701c040d40c050710116000544041141d0a6802905140c1e070f403065079034074581c1d04000303400107580002c0004c902d065605172201c2d11198054020041103245419025801c0c0003504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 76769956 1250 76768706 76768709
    0xc1002160510020c0609060702060a0504060605060c0a050607050a0e060a030204030c03050309030d0c03121a0d0303060f06050708031b0708030423030405032806051f0608070e04021b0601 82
    0x1520350014104c46469010b009580d005124240640110308100500039034600024110000055a030000b041c200007285d8400c000030300d409070540340c0324000c0500d015103030031000109807400d0182400143c4924400c40071108151a6070326407400740d40101082c0f241c1500a0000f01050590130040880450700c9400e0244c01544100003c6948084020616043c00d414030110000d129000c07000714000780e0450703030300183d4035080000010084280303c904403810303101d4072086400c202d18000f100207140d45500702a0a07650b000c0034180321141e441e9411140c81c0f00354040030b800c040090010404040c142003031034202107801c0310311504050590310b95000592041e2011124a6020803042d1440480c002018610140c00c101030350070140740c98042034840e00146040c500041401940c002d00707040e400d92500e2040c2d001501044103103003038005881c4100100f80c8886105141e00c0340094800d00c607800040c0f04440c1139880e034105800715414080690040c59420030104910049404080c104221090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 76771206 1250 76769956 76769983
    0x9090c03060f0c05070b0703090803070e0f0f06040b0d06050316050315040c05130216030c0215040f0b0702030a150203070e04060e07180911070605010b0c10021605 72
    0x5000600d9440d0500490781801d06200009060038241c00c0310940080507528003d4001142c40f03141e50301d4a900314014090710600410000011051180c403561241208061940c10f441c200b0034080071f2020405902111149154002401c1000348010401c4c000540340368a02c1100100e100c81d110700010342880e45038505003a1251003414200031910b41044807240b035007040c24242000d0704240d00d81c50029402030248d580070724420508030709220507641c101c0d031b5003022203510030804140a10b001840c0e0310f880001a40714211084031b400c4021000c0b41103904660a801c01c002c0c400c0d29000d468452600300c468244d031306006850000000c61075400039041c01c0d06280f50b0040c0c0d6842c1100015240415031000300f40554540b400c103001300070812030516008521407e012002c800e0141d103e41000c041c40c1c02c5903008a007800074844441110074041c0012610034441840315a803241a818450300070031071000741942c440211010042c101b0350003001c07020340710400c0100d081c8550300c58a00e401000c030800d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 76772456 1250 76771206 76771223
    0x4110d050708120706062304110f031503070e070504060c03050720121b19050d050703170901020615010908030a08010906050306070906030e030d05040302010c0e030705060715060909 80
    0x41c41080482e10522000e041d86100444000b20000481400e075241d402010b030040381c2e03503d1034254009c402401c1d1902c0d40301c0724801030356901d0450a104541c07070070500702c10700a01c100700e0040789020340c1815043c07150005035551401c25240c81c40803511680c019206405100c020800c0d1004141e4500c40140705800b40700c8003032410000340c1c00380002000844166000354000d0024501c404038602e0558000c031104640c40917640000310200580c1d514580d110703e501c1035070450b881e0108031022881342c046a00990175041d59030540a5100000e22032026501e0040e04440002126100e1004403001686018900b909600e52110241803460b070201e210000410424401081001134500545015050a070090400360529285c090240c8140b8000d0078140344d2944040001d5003401c0043e00d140c005c1e4148207011038140750402900a048071a02d00e400a04241d200c50030714140026090101c0d42d000e4a01c5181580c2c9884d07400c002c01c0d000004401e82a03c0d90f00c0080d01061601a040b030940c01401c86 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 76773706 1250 76772456 76772467
    0x70803040201020f0d200708010608060702060f06130e010b040c0207050f06070c0e0a110a0c0201080a140112020d0c031b1e0303050d090b0c090a06030504110d05070812 74
    0x6072030304045003400b100617031004c800c45d40b200d540444002c500f4920384004014080020f4903031410440140c204941d03d40ca050740016130401c00040150280e40b2035000c1e10030760744481c01074440f0090100d9800740c21580c240c0d0002032880c1903a00005071000160000154910b0b5030001905607840c0384041d00042c0d005c03680a205610300040901c044a504880ce0380c509202d0741d940442e200c00f21722516205204d03810014402e854142c1184281c0c0c0f10a8007825030350408420081d00e640c0c141d01e0140c6c0041c0f920000125040c00500c54812004a00c16825001d80e280044041b41c620344000203c1c0c0041241001000040c03000764130401861280b109003c810344207a00700c8d000341c441d03588a042d0481d8030281c4021550403040d810020750f900352501c0d5564240780d003202400351100243c0248941d480b030f8100540e4185d050041c240c510703000c940c3d801080d542e0340d10803001c1d2401070340c018010582103c00300da183d03c4e0883e0010401c902c00c10aaa170420780d65002c0b90304080302038401e49801e00d0f00044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 76774956 1250 76773706 76773709
    0x150c03010f05180411370504020909010b0a0c020303130302042304080313080a0306090b03010b0105180f060f070308010e13060504031b050102070209010806070c0b070e060708030402 80
    0x840e20301421055031519000f100c6400368000c0100007074070162951074000d006951549030050000642c040612032443d00c403002100ea91480b2000b601c160100110285000c6250f103054002c580c1c0c03008005180c0b00e800c3e4200910102103600c90403086041c4800701c6404070058809002401110080405464200d41781d40184007d0300c002600030010b032140701001c5507644441591450b0000d811415090712582ca400f402d0305413143c103e6000e8801d5101040301c0260701e074190422403c5d5410288140f0841081a040c58241c5d0114072109003c98010300c076814041070401c094448140300202110502801c4030082509540301480b60144510002061002e058101c02c05074014410702c01c10319258500b50080305030044078000010449038a62000c20241480307100003034520403c4040c03202d000807251a0980c000d50000c24202c0c007906400000040c1080f01203801ca1082009464500c18504166100c8801e00d50050129080c002140700314469901c030300d03010301000b5100c1c0c8002e9949050900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 76776206 1250 76774956 76774979
    0x30509070b0c03031501021504050a050c010302041a03060a03020a081e030708040b030a150b2101060203030402120106082a150d0b030a020909060709060518010809150c0301 76
    0x30009003100e079003007100c070320045000801c0b25031054428400042c280c51901c0104d080400100b0001d00560b680010703c4180440403031145034480c4601c040380c02c000c154400650a9014603c184240c0040d0600c14030013021943c001140d02460080820f02c0940d1a9400102185204c0c1c10001c03040c1d000c99540c440c06541040c440d40a00d0461004504050035540c680202c1d201e0742c010311446140120214002c41d10940004600c5121498803003030250f11440380e000143c000003044203d5135a081030720b89500900141041c1680d505902551459882d13400f4055501d80242d800c4030a0b65031583c001602c08014000d0302e54842c08000d8074100305c10810208140a525265507512a00f000c2d4072042c0100146021600d04400b40000441d1700601580001d007030189440d40a504241d102081284d10000070426511072903041d107031100c0e00c42c3c4403072003100e0707e00a0001103000c0350105c810105556006a5140d0703481559081190000d01400301110b0101d0020384001403035140101c0140320300642d11 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 76777456 1250 76776206 76776209
    0x150120030a110703020a0909021c0506070e0109080a02090402030709110403110103020903100f0b04020c060a060807080705060d1e0c0f0c0c0902071103030307080a05070806010c0b07090906030303050907 89
    0x30000784a61030950300052061b00841c45101c01142c1e5035450f2600311b45540c482804e0380c600155164081c00341a00700703151900b00071500e104c001070014480e09429806208a502681c5200d0001c01003221203a082c05411980980240e07414031802e0340000310000c40380a000d02c2440394100c25034485207035280220074040304842c3c980c141401071100d80b4541d2400940c2c04140800d0b10030214a4000c004000d00040802403602904a0700004203c00144000500d0310300031810b9000420240c0d94401881f6190150380c02100d4607134000340e50030040351400c2000b03040190201400004c11030008485c00701c6415200355000d0a03103445203600d0b40245e0b04002c2d03c506d081d1280c00c0c508148800c40c3e0b075503d42095140551010360768040783e0701d41403122048401d01740d0301307000d001c5968904011202500c2c80008030ba1204042d07003400006003401d44a006441d014070010707160000d942c7d02c00d6a4204005134018844810003e0120002075107280c1401842d00031400f035140040e540c28070781495403c02006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 76778706 1250 76777456 76777487
    0xe0304171027020103021909030213020405060301140f1c020102060c0f0714010213030b010306050105010c1a041b150206090609120307020705040f060602010507020a0506150120030a 80
    0x3060b25400b14400020300b100070954001da00398500d0b00a07480103800a001d0b000d0661010030244406551080d000040030381500d000303c50843c2400d0815480005034491400758070340040c0700744010440124418403400100b40d008254035091200e841c00308402c0c0f000040428001501001c110055580500c2081e03080f064031112a8a010552400c040c06842884c00040c00081c800001140c414801e605450704000d445241d502c031640c4e6410000d20b0750100f07000c00d0b90080d18010000078198061000616003962006100081c180084074010814100401c00d4038603000c01ea0118144212000780364001e410030848180c0c800d8600f0100030314100d0005c0801ca0154017840c14002071907400030380400540d94030203102d0ba03a42e0f910300d012030502c403545c1c0c000342d006400c1c000301400801982d0805410ba07000c0d80e00801c159900d1001c100d030780d07444130384010b8403581104020580d0000c50024070480e410040c1001c40400400003204041041c0d0b20745c0110b0a5040070581e42466680481403c100d01607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 76779956 1250 76778706 76778711
    0x150b0108040507060f050d0f06081603020a030809031501090c02010c09081518060a0b15030f0609070306080307050a02010305011a0a03050604060306180b01050612010302130e03041710 81
    0x601c0c0c0d4810303556074454001c1e2024012640208140144110f0444040b002040300031b1003180e16071038240e80900740e140998403a43c0505009108803400c0b000c40b0400700c0b80c004203103044051458641c035840c2d91000c880e0303d1b0075016141041c021076a1a09060f4001c0410b60310014954946850080c215503074040c6c0c039010072070622000c000c00c8100289489201c0c101d100e00065640b01c043c035540f009581500d40300994060607040040072050796008c0b803801c160540f504840d00340f00080e00d1010707100894940101030740d080c0200d0b100c0d05144911a80c0a6458140022426111882d01c0e02d19008060200c40c160301003403440085580c180541c42c01801006244c980900a400354948a40a180c14200c20107a5500c005400d0356030351303002800115001601005111428030b00a6400301400b4425035080d07203840000595420701d02c0c100c0d07459008442c03520380203900719420814154004c0020354021911101500000c00e400c0c00100300030b142d442130750390000391800c00304d50800e8490440710100300e2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 76781206 1250 76779956 76779961
    0x606150403030815030309030a03020d02010609050f04060c0509060f090a050105030403020a081305100c0b0612150402130216030e0409031e020a08040b0c06240603040606030f150b0108 81
    0xf90066401904245001c50352160504180046413031030060f21041a4140f041030030010a05401040352103010b1a550300134442c02d42c03138520f80016107100390355205840007201b0006001c1501a403100c2c860041c3c030f2074038628000a80c00010010b4003c0e15500e0081d074000606240c1070319042d94800f0080c4802c2c202641185010b450294a42c1c22a50000d45031500016a0030b80c40942e00301404050b000081c400301d56400d46280080880e00c04c040304884420b02d500126600d0300d400c4094842100d9031000400c101104564004411b80000d0000c98000341140740c40701001c80c032030014103a507041896568254503028200208544441c2c10b502c0d000368030b40304020740400d038840b42d5a039994080f41003261003050888000c038070f0312403c0c0c2d0000d0100900810003040e2001d40400070540141c00c03100701c030700640b9024400c0c101c982c902d80d48a81d503034040c2c00c45603501c0c0c1000350196602c07602800001070303c16501e445c1e03031a8655044004840a21003400000c3d0034403014460f4802540081c40c0104161 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 76782456 1250 76781206 76781213
    0x50306040305040b0c0709020d0203040302060a050108030316170a1b1d04020f0702030d02100c091805060102031c09060c0315090209191d06060f04181803020606150403 74
    0x380f065006003401d543d00018114141d1904020b418001d0000d41421551a100c21010200a41060f10101c0060280101040d00b60459000717180c140c2c0c0e00080038514507100c41d01c0300c10b1204066480ca07001d0100341e2900350301000815400303502c41c2c100480d000c00c9841e4420072610806e0001c010403014030116040d040c00c0c079032094949000303030740c025240140c2e01c88090210310b016000b2644000c0d810303c16210441e80065000c103241c4c08054140c1c1042c0111640110700355074080381d502480c844403070200b1008110290740d4000b141c0108060040e289026103441c0c0c89000010100d200510745078850401c3c404100d1603103c0c2c202241101d217001c0044011260311400c4410031071040041181e0046007210580c0d0318007020000e44440c90032a0942c040d83e404010b040180d0f4103448071213440c07407200021080d0400c041160340f01e10324036829500c0c4c03e00700303400750040240384041160440d60320b0301040e1045a61298650307002c2d000e0740041055107003030410401e00e4200d00d01d040010100034007003080003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 76783706 1250 76782456 76782467
    0xd020607050711010c080a11190f060f06050a08010e1203010b1204030e0402070b0a1a060717040b0403110a05040b0f04020721080f15010815030106030507090204050103060503060403 80
    0x542d0f0b4006103e44801444a0040310a501c1254005c2c2c9070400008041080c190004d520300010150b08054500d0807202d107210a9040c2c00c130800103030011842e03051590008070240c1c05039034065000740c0c2c0001c866882c0d4002c43c40c030100b5038004280300c1c3c0d511010b07008070354420800d00e047d94840e2b4403103510319810591108000c5c01b4001c600500300c1904d0b0081401c09d405050032481203030014200315100e04040c20411100c4006980303040758a807801815586200b5041c45920300c2d0070002d0071a618101075a507641820050745c50716464010800c0c03001048080c88000140010f500620790980d250009008000c00c10320250300c020b101e80d140048070240c9454160000103c0041114016154001810507041b490300e0482c00d007440050a181401c8600d0f0040100c40c06002400403900e42070303441e54281e0480f4400c580805021560758800520410200c02d03e00d000c4540240001c50207940ea81c0d00c00d441d0980d030381c000080444c0c0108060141d564503109500040c2000c400502590805440c051716 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 76784956 1250 76783706 76783717
    0x60c030c15230105090132180103110a050a170f0f0a0c090509030910020a020901061110050c090f0d0c030308010302120115060302090103060905041101020d02060705 73
    0x28850501104418841032140c4041a8403844100703000c242a65020142c07011100b0324641030140c2c450001082ca81405d0300010705969040c9802c4d5907001d68442c0035403e5a40360004110340b048999450710140d01d0311f55000000041d8007a00000c0f9504501d49440004000784900340100c400384000c029a9480403003004c2161841c0d90100c0403c60100038681c14001d40e0080794078248034540e41507500c000002604040240514003481a0544400d20101543d0b400c0d6505041d0f540144820724003840d080b0b00c444045a002d0048560800c09a40400c000b0a000d9020001082d40800031444210092002014001070301c1c1080045182420303909604e406086040b9001d03164006a80c03c50352142e0002c2d80200f90021740304a2915035030718004000e41d109010403270180c00f40e4a00080418414014410b10400200d0409141400e04030110000e420491817181090349031940000d0940f0180305482c003032800384189002905864001a14203c01014090704540c0140d08120f03145070300c501650b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 76786206 1250 76784956 76784963
    0x5040c0206150103060b04030803040303061502030405040b042301030308151c0c050909030901140c030a030b06090d051b18011503111206030706020c010203040b09031908070c0e01060c 81
    0xb100d0248010048000b8080ba801064404200003030206c1440030707240c05107100701d01c079942c05c1c000070341c5600008000403000342c0c91502580c01480244034505d00b64003d444412001340000584007680304100000d0703003101c40b402c4001100c010060041c140d0000c10142e10180d0039091014440f0b419002c9140700140d4910010903803c0038540400300011220404000e1000606450326401e00c00c8a080e140c1e4404010f403070104000f04030080d914815841a04c090007c84400b46092004442c01078018221801080d90302900c100a01d100d917980d4501c001e00070300e024200502d031350b030f41c10800d1007441007407034049a110b5401c0b8810003501006108040d819116480c4140c002160002c00540c05428507005039403060002003000a00164000811403117840202c084540321507603000d007a62140807140c0300c1401608200814005201c0d0540240211074000d012a9044040f06034508080070500c002124400c030300261010078003040054000181402814051040d45003010240211400790701c000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 76787456 1250 76786206 76786231
    0x9061b02060306030106080105040804060f0807140c0f0d030b0a0b0c03030601050c120315031006240c0f0503120c03010501080105091e07080912040b0406031d030f07060605040c0206 80
    0x3e00700b920300f034001d0402002500b0007403080b0b040902d01000913401034003131039001070038191150303106030310850284d03000d00541d440d82c0800c081d845074001c006078000d01e42c80426124030080086900010800c130800424135075400208100c01a040050015840c1d0029440910038400001c100001208070b980049003400c04669a00c071603100c46007020810380c100880307800c0c08010054100c2c12540481d40101c0700700d050f250042001890748089036041d01940e0f8901e8039800985030034400c204240d80c110f4549041c80c5a4050207541e515001049411084070b0300e800c0030403200e240f40c856803402a0846884540241991305000000748210700c1407190030b20078a800c06c00705100c140c206034600b280540103001388840d0702d01002d0142041d4429074601d0301501c14962000b0700344039030400ba0b074140c0d07440902e464a0540b61410850140801c10090b406001400c51082d10911042009000c1c01c91310303c1849840ea12030b41018800c0b64001d0b80500d004e1810140443d00da40d60100758580c0c40323031103003541 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 76788706 1250 76787456 76787461
    0x90a060305040f08030109050402010305010e1006030e0309150c2a090402010c080a0e0f06130302090912040609180203090a0b09031603020606030c0406050d0f0503120103060c09061b020603 83
    0x528004907011806050990004001f142540070b40c0c100c030b44114001e0300e0a0045913a00c2c030007000032410807240e0103c40d10340308005018007407081e0070400302c0d107180c20100c9044c104814002001622242031850490000046400385800140406012240845003d10f0102d190010700401000a0a0594498500070000908580c09500c4212038203800c0b180035901c40964220140c01c00b84030034081c2c5d1003048103044480c1540780034412561032035004400c48082078a90b500b40103880f600030388640070a0060192015800600201603c01060155a0550074900e420035480b82d900030300042070b402c58010400c005050000007002585550702104111007640c03001c00d06c9045002e20480044074401205c5240185035000841e603004130f07400c6055942991080e000c0000b01c502c5840364035000310100d02c140020800d0060031440c018094401d4900e0304071003000500d480380098104650359940c440c40d00d0001c945c00324140703000d45042e05004070f858907504105008000310380310003480307407500000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 76789956 1250 76788706 76788713
    0x5030a0213090e06060405011a0d020c010b030102280f142a010c1407032a0209043e0d06180609021314070f0c020d05011506020102090a06030504 64
    0x10104018004403a00f0006601d150210b65220039050b52000c1c803580c00c0c84004a40b8507400040c040c460b01c103411040d40b070400c3c6020b504000e03400016400b40c4035581d03020440d005490038002008502c050809c0000c800d902c0010781020645080e001008006032803020512444e0000c007807021481442c4a15520394a0a0041c0c030000200c1100240814440895854000d1415040442003080c81e40712044414031f17075080410345004017640940042c0c10311021100c0036100b400c1c006d130003132030381c180b507841e06800c036008103a6260301924220388020100d58954a480c1941c541c1c0c4001088d1400081301400c00d0350320354940c1402410b0443d204202d144201c0d030801102d03034466001800038059440d40c006d5503080000c0144001d2030f041c1c2c0103400030b0301551801c0035a417150410b5150034a60f03900c2181c9481a003118043c984c000700400344001c420032400540d4500c05100c6106116800106800c81c940742900c40001700c0358014025a03005001040319659084507140c213490f198500000c955a40e0308 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 76791206 1250 76789956 76789987
    0x11706010503060d021f0e0a12020a03060c0c0c0620060f01170a050f03031f06020703081602030303270109170c0c130b150702010e0409030e04020d051803030705030a02 74
    0x110310817030601d00d040c043c00e40c03150420300b0721f80b40410480350900460fa440c84190701c00f0050050003580a100c8050074800110036611111601c11245040d200c0c5102030380c0e41c4941c2d1711079034110f44045190041aa40000002260000c02221001c00b13400c850078442000d0207841018054000340b2070b494010240d60040070010a0305241c1c11400300c0f000400000d07101516070b40b05450f0004200450700e4141d000d8004c0d44040812034a20707600800c9203501d10b868000c420f4102036188035682c801250382c04050799040002d54041d0702c0d041c00da824400390740c2c0140d51a003a0112403840069051041440203d152480c281c402c05818004c07184e40d0700c0d11000b00303505010344a81e800d50b1011402c2c1d0007011f080311590090a200f40240c1da990660312202101503441e009200c0003c2c0050f941c62407070f2007107081c60307000000041c0c800c0c03e00350785080c0d60b000000c09a0b0815050040ca01e9038510411140c502d02c00070902090320f1520181d855424060002801c0c1c3c800185401481c0f0b400045000f4a03e1180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 76792456 1250 76791206 76791229
    0x3070e0303091804110d031413050405040602090901050301180311010b030a0309171605010518041d10060b030c0c07150932041113030b0402011706010503060d02 71
    0x34001e00610716050b82c56000000c01343d409859501400d11480c103070341441c816803c0c0203901900c400560b510151005e08040e0300c48076101c0c1e036604006074001942c1e1260b001b4103008511801c00942c490000c003003440390302c2005a200900c280e040444440840d21540c0c003840501da0907103081040d100f144900f05014084031007000340c1520a901011052540c4a103400c429104a803440421084018490940d6001000c140b1001c5441280007040305600507c0104070060180c03031a080c031260400c0000e412600e14003400482d520380d541d44044c00b1082448422400503800e6030402182e4209084220715020081404200303000028403185840801c00514000301500c01c401099582d1692008040e2407407442407180c008043c4290585440e0000e014505803280100b1401d100c00c110001c20015141c10260b651034008204203050800c803090001c90003541c003940c442d600d6401e26200040080c11120001e800c0d2618140600105030380c014203c6c0e40009045482c0c00303038403046000050030140c25 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 76793706 1250 76792456 76792459
    0x6180f0303040801020417010b0319060f050c0319020f0d090c0e040602070b0601020a02030c01050d0f060b0408150403081b160507030606120f1401020f0708040806061503070e030309 80
    0xc10002403180f4150000c1050361180c4904021690060300601d00b640c0b41c03000040c0e4590404104869080c0704614203c1000e4080c01000c07984655061245040320401c0d03e50051070840042084250030a038103d85462544c100401c40c905500c1740c400340c100340910600c20000d103469218520a111440c002280640290781c0c0151060034503251120007503101c03060480c0c12841d07640000b1000e41c004180901c140f500070f00600012500540112999031181d41c114802d165940a0802030114902c02c01c4064a12207400079075540c101240a4505421002003402d968182ca08220001e540000d81a4000d0342120003255044428482e41046001e411640703841d00742e54400c01428010001380384011240510000c0100070384400c984404451064400382001c00e12070720481c00503441c1d454042402850340d0006080400c12081d50119038000780702696500c0740410180481d03001801040d4004ca41240e00b84200509025240b805000041448080c09001601d210030b60302c0c02c0c01103c041000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 76794956 1250 76793706 76793713
    0xf070c0305071d0c0c0a020405060a090926041203030c020a06050f040b010510020a260301030510060b0a140a0207051201060603050a09030207050d030c05070603020a02160506180f03 80
    0xb121840c101002602e1a02d075011a40a02c0210b08054200c008a03070f440701700348001d09030301040c44d024400540000340440360000c8120300c000410708518403d0681c03071441141400307034590010080c0d02001c200388070310701c5a43c2c00810041003101c0d04010340e40301d07641e45130030042040300c0f400c4401d0f07090150b412005085d1134240010004403130100f01403a0b00c40c9202e000383c041184d03203440900c500d42c00281115400340e03018940300f42c0402c0c0228840300204030882000c1d00304c2054842d038105903400a0348100c3d82c650002c89280c860301128091500a8800c0f03060f42424050002c1c4020000100c403202c607d20700000180400e0700c18030901126000e0600034001d465615040800b45009007814404c0800291030b01021640011041c014441d100d6010f44c0100703113181c01c0c8010003000c8001c07030508405000207a052800080c00c24006070b0300402c44e6860050725461080c02c040d003018040c0380da0200307004d0f01c290207010315a034050030f4404c00301007100e416504c50150404200400381c64a501c03940b611 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 76796206 1250 76794956 76794959
    0x901050f010c1a100603140705162108090706030b010c0201050307020f0a11030d02030708040302040c0504180603030809030c060c0a0201020d0e1605060f07080a120212090607050f0f070c030507 85
    0x30144d880201c0c1c44a58003005034504c03900061100c02c605984c1d40303001440801648540a840c40403901650303005c0c2201540482c1c0c401104229080d660504501007080c40d000c12940810a0207480010999814140010310307035400000d1211100d0080241401004030200710600d100700500c01c2d4900310041141d202c1030450400004850135064158464880c1524043c0d00c9840072007981c8140c1d034031450031401d190856080001170201825440100001840000b4040c022003076036a11940c00e1800000d0440e0079420300422040f001402118182d0007003000e092603a000140070f642c8401c0d03040c0c0305512180d000404901901c115001c140510382480001c84541c08003103041e071034455091b00002c1c0c45690724400d00001d40a42d244002c42000248003110200d21150014a0070442030302e4003a4041c01c014002030201d030000710b640c03413000c018041040aa43c01c00c00030260448041c1c00c000d414074580c01c115440620840400c024819400b1070f010040080d100b003000c029540c030805803844103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 76797456 1250 76796206 76796221
    0x31f0f0303300c0206040203121305060a0c02030303070504031209050616140f1e010c020a0b060f1210050a020313031d0a0b0c010b041404060c170a020c06060901050f010c1a 76
    0x9240c20341c0c087e84a030082180c05010310320480111a003500740101210810b03444c0604100040d04100d0b810424080f80c4079000006a0703091004602c11000b94403001d849a045041544503101c100a400d0b0600c03c0810050001c0d0f580d142c280c821250f541030f168501c0003254a0503400c1100341c3c24484009110301a0440040400403a0a207225119500a9061050000c190070300340c41044c405800035810100720100410030f05081290f0000000c3c1c0100c4140c2e4905010850440b0280034848154000018221031680140940d5070009090303a0150b0941c1002e00080c60490400c040c01400e100c5c2c40b0100109846d811041840c0580d0024003101c405a51002000d00d640d00181016099510345407011401c0d18041c4181c7e03148411b00f0b481c088890ba1540e40d1280240409070481090041d00c7c480b4101101003480800c2c450500c04a0150b11600e09070040c41ca004009040c01c1e00c5600b0702801400b00d5200c003998141000024a03081ea40140309040c0b03d40960120100100c1c42130350701040100c003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 76798563 1107 76797456 76797463
    0x1060e0412170a0c02150408250b040b0f0903040303080403030f0f0c02030903100b0d110112090c030c06180501030507020c0303031f0f0303300c02 65
    0xb90000c180000c0401ca811a0042081c545a0b512600c81641c14081168000c40b2002c00000b0b50605503142a60b1303001c1c8403403411241003007000d020101007101900740c002542120b4004058202802d0500101c80100e51269070705510b0804900c1f2401c00100716070440e50159105042a1034655048014043c0c0e00703680e40c0401d888a0f0000c000720700b5403117642c1e4100d000e070300103580c1d540303d0000785810184c0011826a0b010310304004060380340c40c0d80d651400b03119403000c603c03140d80a249006803030042060b460340e11128606028042001a02d400c9802924050300c504280b06603030700822147c4c80300d440c00e4450303c2140c401041103554001d402c00ca402007101c7c01610203080e1400d0120349150011a6007010201c000c81030303991502000602c0c2c0001d4101c500e00241d101c0c0c210344018204248105441d044d00d81801140110058110b05100b45d440304100103025080d2403060007541d = true := by decide +kernel

theorem cover : BRFrame.Cov 76618706 76798563 := by
  have h0 := BRFrame.cov_init 76618706
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76618706 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 76618706 ≤ n) (h2 : n < 76798563) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
