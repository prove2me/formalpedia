-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4804
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:46:58.748293+00:00
-- url     : https://prove2.me/submissions/67036953-13ca-47ea-b741-6df1901b3ad1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 863848920 ≤ n < 864028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 863850170 1250 863848920 863848939
    0x915070210050c010e0f0d0f0c05010912021501030317190501180e01062102120601080a140c010206270a11150f0d09030318050a03030e07050618060702 67
    0x40c29403001c054200765000e80c000303010840030f8440155645489000d421b016400030191003000a005101030740e10301e070311800c002c00200c2454480c9800c540342c6a100b81c03003809008c003039802e1159051040b0803426856510a00359541541c80c010984a00407852403910900500807410451032071410300440c8008000c103010341d6131030383d5584441c0903103040341004807403e005208000500600510065595550408500c080f2503c08030445140d08901030b600841c3c2c05104007904481800428080c1a10400410101c111032500c5680d412002c441c05807941c00145411307006a0b130128041c0c0c0c02c0b01d8842c00074528855440112000b01c00c010003941064410002a03600b0017a00c049013206240080ba1a100302f051507440e40300951040807030303c82d4038490812940d2805100f5a102e104110b000c3d28000070b800c0080008000891a840001d40b1160310541c450310070180c1c14041c511075070b0b1015001c3c1100600d040b02140c401c0c051104d5460010f1400b40c80b40d40039844440603a1700c03054004103107400c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 863851420 1250 863850170 863850199
    0x3011a091207080d030917030a1103010e0118020a08041202011b020f21031b0f0a03051005040605131d0a0305040e0f0103020a030305090d06111c1109150702 69
    0x1070303600440c81001c1e0f0601078500c8808060380a44540b5a0300b03500120813108010000080161652008242001640d510042810040440c4e07000d14003070564098400d03010750400500e014600b19031030144085a00401503200c40c40d030700c425100e4015034080804a260150001c05034003401c040300800b005002941f0309004607a5000510402842c440e100382c0320815003800500c5030400411200889201c803c10109903400c40803502041407611003111582045904041441a64400342d03203040001c0d111418041c0000405a9000c010701c0b0071101041905c0c6060040303012100000e00000e44160741d5940815100b0f208081680b03d0280d0909503440c101b201d1601502c0c2d5000341c010b402505032114001039600300b400214038160307a00100101c001ca032031a40c0840e01075200100343e541088091405c3c4000900301c1c0241412004811017250719201e410008070556422804103603049418a0348203c0c11b00c0008045410b0b803c000e5511a020402003200c0040d503124440c1e009410040c843c50004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 863852670 1250 863851420 863851423
    0x915290a18050a091e200d080c011515020c1008012d031209090606020703080c1e010e1605090402040c11030a0207050f09190b151201030203010b060f03011a0912 71
    0x550a10481b03d49580e494018581207500390940c1c6001c1d008050301500700c010030700800181c0350003441480003007a0140f000d2107040c810001a448105942c10401d1522269034062150041020090b180d1000c40710802c50010300c0140c041c0314211510000e0012122220340d4100c180e0211914051040d018036503c0c6800c2c0d0103081280001c1002a141e0507011a00811a0040d14102c07080e0354002d1424905644641803a580040189102c92050381104c6504d0144c25007540102c4a00c3c0c8000a0410300740340401d424100e0020b2289500a0070b24000e11451703640c141a940c0207501920009226560880f060b9501650030b920345980f8071000c1500c6111a5000440e48250b84d016603001c01c12113401c0080c040302d00c100b50350b0b00101090640d241d420404140e4480c00c8d40c45001007140c0c400070815440d01401e07074444681d000481410302d006000b0350400740112900d195098581c00d01d0b043c2c80844403281e501060141c6800c0544045802c038009030b0060994906810080800744800b601c3c80c5840d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 863853920 1250 863852670 863852723
    0x6090f0307030f030e0315040b06060412051f0605090a020c0102040807140f040b0102031611061309050702070b0403030f0c0c1d011e06030915290a18050a09 69
    0xc13030001e10704074010421402d0200e01101c4222600c04080c0e820380342c0740d4171a844440024002600500e080c031000079542c003040c030a81d0b0b20500441c00b034514520319900740303c00c008100c5004540320f402c20004002c0c40c1c4031013030801d600402d48040181c44a813171124003401f92045a12119892142990110781c0b1110002052001482240d4111110941c0d40601080d903800d02420341c05a00240800440041341102c00380e4000e00c0344c802c8114580740d2000261103500066107040315001d04900601c00c00394644119038200501d400200221807a1541003011486203000013400c008100c121400100c2c000e0302c1441500d030b4020031200364142c03030b01c031a00086180c02c20340e6103039142e6800000410850070741200b100340c0d18240904d030303d440c10f26609402403c2034200c101ca00b56896080e0b0580340c1c60611072100c8104030801c004000903900800c50384c8442c099484c070382c40f94003141400c00601d0900080246200c0111101040076a42e070340842005041044000d816000000460070030156540d520 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 863855170 1250 863853920 863853923
    0x130b0c0f010c03110d0213050918010b0f1507111302090f041a040c140c0105041b08060a0f020c0f100617101d070e060a06110c06090f0307030f 63
    0x20410703441c2c00c0384100c3c261a40525843c00004041200031014140c40d001818240550064030301415641c00128024035812580b03680c541400c0c1201102420080c020103541441c111201d0700030b0000c02000a000000c3c500a520702d454000800504000d00d01e6501c1d2a00c110090001c0c04a04200d010800a94044140c11344900d69100c41166186400c4c03007050712034681d40702100000c66240c42404002c010b2080c1480601071071180081000400d140204600520f203c0003051505040c038103400f503503944820ba501c100c07000c0d072402e11048000003039480e0701c01c66514000c10402d44c0111148028400e03542001200d006803c011441d01344000340300c000d40c10316a80c080006c15950307010403191003000400c40312542c108070b40e080d88100403900301c84000c21002140c0c10608104c408000d00c0c000340da038000841400e402d0104015480d10701c0300301c0010800703824060f1a203200609041d440c0c1050782c951501ca50008112a0032644901d40100c4500002034125224113489041444803903004140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 863856420 1250 863855170 863855173
    0x1c030203070b09031813020906030a060911030c190c1b03030807031107060f0209180106080601030905030a1812060f050903070f0b04030302190806030606190605130b0c0f 75
    0x100d00d00f0400042218070a02d41e03001101c0d00100c040341008840001104051112902840301d250566a020010350042043c1480000d180d0b00d095460001d50364509917482c4c1019041c0200022940801c00715020183c25070030703480c2c80c2c198964047c1c031985100701003d06940c07100220b00c1c211841082490094074066222100700740d40b9072404270140d410054040301101814070104000900ca50000e070030304013540c0005800c18480b038000c610001e11030384895607105407510041007556085661103070490001e20b0f00b03001c291b20745e0311850b980344201017201040081c0c0841107400b21050301407860281c400300065580c112440d080c0200178049000406c0b0f540740c94400400c5010800000b122010742d400603003442000e5003074840c0102e40d803005100b9001c0c95020000007400c900f00c92100ba420303242540743c41d140c40c10400203061510f00300626440c0102c03140812584042030030109081100c10526019554000c1514440b441010681c001d10b240d00b400314854101d20b00104001052948480 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 863857670 1250 863856420 863856443
    0x100e19060e030708121c0612031701211b17070518040b07080702030409141920070609050a1109070302070b0a0e0f06071d0604180b1c03020307 63
    0x4462616503500c0c00e80c0902c009000c01c42005d10400c007803990400d41c40251b0700060303003d40e0f034201c0e40f00040a151003200000d14031306d41082c040c240000c41501400c80e007401d9882c1d210b807030b00140c01c0c00182200c01a2020030091912208a01441025805000030202881d144450714a20b2582d440c014010707640320307441c0062095544080c200c11030b84a075811542c06502a00c608005a4100a000e0509000c5010410020a104915002c1c2c0c07071813001280000038003498480c00b90307415402c002254a0016050040054524400d18284400e035210940c050b580c3c0d24040c64903200401506400410724000c5560603030610110225032994408191070004555035180d1084080784a220b20040c5013460402c0414105401680203142c20b00b0b03650221051741001c0c820070351070030004407051800505179028400c1a080f08500f0490004000c2c2d40d00350405040c0909224411400c42000d0140b80d65266100305e259150b00c1448400700702108044101c610301c1c20b00a440c1c2d03101076401d5407841d4146 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 863858920 1250 863857670 863857679
    0xf060516020d0602044119030807150510060f0e04050f06040c050c070303030b0a0905040c0602120a0203030604050c040f0b0c150424110d06031203050402100e19060e0307 75
    0x6c400801c50842020742c40c0701d0510555110021a540d80166903003110841c080090082a0100d1340380c080c6000d800b40507203c488070315100c290801c050041f0781010f4201014480058450304001d000e40b450744c1000c081003410f007101240d203610184c0c200e6a00c60300307007014080000341c82d18000c0c0c0104826034090190a40c44c40e07050b01c06220364042c454807a800003400b000480d100394040488604018944d100099443c5800710617580161000e03100c2c407c3e02c400400c0076540401240c0342000086e2481405c1200e01d548c00303922404010300c01401a80c98100081e000140b24044401520b00144105001525610743d25103c1e00020a011554030490080005040c15072032100e10583d130100106000e20560350401946e203a03203ca00c000c44a4a4003455108256404060303d406aa00a40042e0042ca142404810708105001e2030741450706d020b09001c007685401005038541000c600700f541c0450007110115070008441c4051a0200c0410440401c8103507100040f007179544001c03021a801103444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 863860170 1250 863858920 863858969
    0x18060803090109030605090705090a0b0111060606040e130c060c05060f0c0708160b01150e10020705060a120204092414040e0118032003040f060516020d060204 70
    0x30801d01c42d0208868140400024603942c00c03107a80001641c0075654456030319004034200c07800603115030b050180c8840003032446580c00142e1981c0990400010561814402d0200300544038500443c4c42040c0c1c8940020114800304083b181240d07030000000648983e9810003e096504045040319607024100c0403da403010300d20026401484682d08662501301640da8038040c1d9400300c0b50a9921240b14030302030000c24210100e0900801320300102200041000f40014144102d00c55110310645440250b03d900c1540000c2401c1035032000c2d124141e42d05000324040d218001c00c00e00c41c1008a000081c0412103511a4001054052180161480300d80881c0c04102000d00c0501500003c143c03200040465850940c0041410044a0000295582c010714406040011082c1c05a000c65601d040591860a08a2451941034540d901550925081542d44000312009200d90f200b007140101702c00c001d10b09441044a01c0590080482c811030b010307860014041e40262003030304412a039a454170303082c000d007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 863861420 1250 863860170 863860177
    0x1060206160f090501030b0d1428120c031205041109090a0203330108011a0105120609100b0a090501020705030f0c0d0602040806091b0a0602060a0906020c010618060803 74
    0x941c3c80d0040024105001100280f000c250860341c03001040850f0004601040d04a500010615000d0041421901442001228404448604000703030102c0d940200c0e0095030654141c0c00945009002d1801a00303089440d03030011000b0040d860300c1c103030901c82080b0940b195120305060a9074281d080d941c65003440364581c140480c2c044d401d900400081c6503040385406032030b80c189501403c650300d041c0202c0c01c02c1c2c250308004d030401d08940e03555040740c034081d840c013101c0c110f500c08091070b00c20300c0c00301141507a501d4120003600d22801040400f000c40c0904900e6452000a00b115500443d266180316800400f4102c243c40f0385030250007030500118041c1030202d03042e00c04070800380081068896400602c1500c4d0030b0540203841040d8207002c046101c04090045901400002c0d0060031087c1c03006854501d034640a0040c6489900d003010100a82600810640d0b445a080b280008180c8064101071300644240001e48596528000001c225404d011000009a124160040042030303140c030049607503880f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 863862670 1250 863861420 863861447
    0x810060915060c060b01020118080409050c0301032001032702090c180d0813030c090b0f01080402060705070e010b04090e011104032a09020702030f07150c17030106020616 75
    0xa40d00c541c643d002c0741d9943c100114441040c070000882d0915001070352802c041c9a20103d41c02000002d08004101e40c0e0302a480d0045020015a451940342d45d5812184204800e020800c0d150202601040c50380030740d004004150480e0070120144401103042c0301112100d010032031141446c0000b164918100b0020343d616040203c040c0005800710314100140b0306044070086813420f0042022040803003118501a000350300c500c41624195040451560070b48400801c02c0c0d000b5805503a07414000ea9104074081d82164040e11340564030700712410000d0501c0001c0d0408001d03101100000900d041d1188000c008407000070404120044480d2462400d96100f8081d072071a03424144424030100c1e85484140802c02c10b25842d000048070381003140540c401060b8041029941d0206203035056040600503411038417565805805043e0510034160b40c1210721090071810414110581820451140c6001190840a4140e41c0e02c3e0b6a580344001c3d5610740c110703191525111844180308180340901d010b4000203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 863863920 1250 863862670 863862677
    0x201090506150a0306061d15060702010c06140f060f010201090f1b1e17010c02070303120b1806011e0e040c0509040c031407020c0127081006091506 65
    0x161590b4420040701d41141802d168410720030400040001c005206603402840009456a60781c05006072161440800420711034a54662800a090a54550086910031a0b090030140a03640081c00d140b0000c0c14a10b800102080000c002d00942c400307040c680a02c0f070a800c036803110003ca02407004900341e84a03000018031402c800b11400d00085c270703200300707841800c00806100038401c0d941c1c1c44c4d4010350b00100e010240c6198408501400f034203d005075040c420b010707034400912080e249200029924452880041c04202103460044241882900004202d001c02070510744070f00c01c4014402440072007612818080340c2520310300040381b00101030403070103054542c80310f180040d1711f501404094501e1408000811008000401c0b90fa5141d2041c2c9a4621681d0b800040b881d162403c19542050060190010343d03214020751207840c0e900010114100e003122511026a49030081d01c80035542281d0040c0350180268072508009207180c1e4000c5048400c024003c2c0207504038803143c81ca41c2e040c0741c003624001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 863865170 1250 863863920 863863933
    0x23042303030a09050a02060301030c03050613030203030a0b060d0c05300429010b070302100204080723040618180308160c0209070f090b03060102150703020403020901090b01080702010905 82
    0x1800c0542c00f44031480e0040080d251058155400949180d01c02d03003046500c982103000034400c0c00010081c4c1c59002c00442412300c0d000e01c10348c80c041c0d0740c1d01005050001c3c29446419030380c3c9036144c03102916070010b4120800e002c005114100540580c018850240c00746122124051030b1035100780303900750301c1e9041080d0785503e6201c603101c981d000302e03074080101c090510b60b500140889502c090110300034584210482d403110100d2078028109a042c5154903040c03401030109114846001c41c640c0222443c0c901280c1c10305210f00071904e004402c04000e95885407400e40b000030401d40d40358000351155200d00f403c100c80d44041c90789c00000c500702e0a004e4005903e140004220418039640b1f0300790300b86541080854180151b0001d10250b2003260000c0c0000c010140050741c55400c5402d80c0007820180e851701e82145001d900003940c641e544088500c40c45082ca001c039542a000c2d81c112006540c01a100002d250f855114620160014000c150b000404040c00504181d20621540d50324517404400f0782034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 863866420 1250 863865170 863865181
    0xf0402071e080f040e04050c09060f121015051906080c03040f050703030e03010c020708030703181707030b0a020a09091e15091d0a152304230303 64
    0x100c56441049807840403c000c4810075058141c0500018640d00301c4030304039442c003490100d0600600c0281d060080e261038040c00140d9480300042c0c000d0700b0f003d550410700402c0d1a401c03145440303041c0360b110f001c041c580480b9101d003605410004041c0c65007620b08641802d0f000e80c1d09003407046c007845441c0024812078041625000300304001c1d0380150041800088890a549a0a0403e011580100c0200c1c01c8280a1109414203001c0c20b0451038060018202cbd0030300c0c1481c05622031040b540c0003800c1055103e422007060340d002c0d0990000d806c2002c1d200d501481c8841c655980c0c1c0669000680d042c158034400170303801081a000f15020000345079120310401e41361482c280301825100320107045140c030340440c1d171403524128400c20001c3c138000d221517500c00f850a2155001c81d2aa40c14040109920001059485200091700c1540507400140d2160668a030b00e211002050f00090f001014042c0c44907210008640f400340c98011030060780300d4a1041140041e17020121075900c114000c1e0740041c40001d9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 863867670 1250 863866420 863866463
    0x708030f0307051c0f05060301060b19031b0206040c0e01080309011404051e100503010312050307030b12030a0f02030306100810170a11041e150317090f040207 70
    0x103030001410709045062152180111207004081e10139107860036643c0018505224080c003030745401050507002000000d040c03802d0f2005038030900d54095000140305000c40f0301707184a43c1c0540c0601174204a178248000301200001c0d101d0100b40c9065541c1e4050400c04100b41c40180c40c040e040324440f4005514180384000103403111500c501b04c1944031041400f0001d4036440360140a000c442c103440204c0c1500b81410100002081401d00e000e007008001d100600018000440c0d018006415040903900ca0745d680c08114041d08501540d160041c0d051065403055410000c081c1c410380c4d485403070307941500814034000ca0303407800115021a07104508107003030701009000301c0286402915180304601e902d911000041c0880c40a05540e50207030388400b21000502c00b500c100c080701500c1c121020712150101286015812960140c52010707265200340070031441c0400383d4000c7c001c0d607010180391030280c10381d07408003044c2d00801041030060b545a1a0b00201c1d2400d8805c0b21001a0301c07281c2441010310399001c11 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 863868920 1250 863867670 863867677
    0x4111f0e0109230102070f06140f04030606030b04111002030a0c05160617070f0503220b09030a030606050c100c0903050a06020d1404150c050904150501020f0708030f 73
    0x40c0c18481c1681c070204461510f14490100e14510600b03a8a0382201d0b50002480e0104075844090907034821001032006652000c00032010b46d42a0010a46402c07402d9007858617417042c0d5000500840c5461030000820600b00c1c042c51159003d43c1c200d0401c148840140307c01015800b1005d0010303041013000051f0280502c00c50300c5400d0040d001c0b103444c400080240010141c0d281c1210010840700c01100e0040400d601159a00005074502011030606085014000d0b00010b400410400141d44440385510041890380000d2504281e07800c1c003d040c81d03002180c80745d20180031100000e0034903801064045c00303402146c0761107146400405035205110414801003e0740503c0800700001c0400010104008000b00c1a070300f030048500507a295208040b0300304455241115958141c064010400445c0500080c2c010701c8102c0800482e01d80000c0004841c24850b40c0c3ca0a075005240884c00001740c144080c1050a640c0c0c02c1c2c0840f10a440b444610031380d540440d01c85c07500039610401a00081c106204082c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 863870170 1250 863868920 863868947
    0xb06100225051002030406020c010c1a040b04020a0605040815041a09160f050105070f081e03060307080303040b0a15050405010b0903010c0912020d08160b04111f 71
    0x554800100700c40a02006000391440c2620000c008901030080f86403140a1030215600b5000440c03603c0e140140180d01d40414440d1541030000c240f800340300348441002440055400e401d000100380c645854158180c070410358043c2d000781c03400540460102e00490460b01969656801400c030909000e080e80c24907200100201d031a00300010240102141e0300d0202ea0081e134012020f00007000c066142c43c00e48098a91007112500d030541d20030071499820100301c030030843d00212506c482c507101e801c00402c14428204c001c12003061009400c006101d80710040c41c096a022030545004aa0380d24119076039001c2070384c7c09810080c202020400388101680f1044034201b06a00128070195101f002034125003090307002c0c0c00b803a0b500003000040c0f841d0a2040c0300a40d0210304000381c40f68244050f02100d0408240000e0085581d40900720038815402c05607421996000d8010001224074070340084892001d480890b910813100411108501e00b200c10f2441d588410003800d10705900b8010111800d43c4400d03070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 863871420 1250 863870170 863870173
    0x250807050f2505100c030c050901030e0c030327090c04050607050109060c08040b0708270f0a0c150314061c05061f0b0c121b03070b010e060603040b061002 68
    0x2082d21850001030750003812180268082c1420b07802180003903042e5280d8070a000c00f01403428401c1e030306c800d421605840b4000300a10300042c001000301d4085240050420401e9403501c0b01180c400c0d07001810b43c54a08410b001c816182103e442c61000344401c08406032265040e4800c00d002c00d01080c100580a444154040e000108499000c2d40341e520850b200610180700055429081200707200f05c0d18003103a0002800d00d403203803031454064007001c00c441c640075012200d19280340300c1ca1080c42d01000521300f2400c00d94192003c400b0310b45051826602c00c0d00c207540d212003044540300000e50180c4640d001254514420741020303030303549003000400e00742e45e443c075040240b0f6101d030340707021400400440303215038080c0341482e00c00d0501c0381920070340e04456031002d07035409130801903031941d440d000c10600032030f128a1304600d45541da8842c04000e005d06035840311840c0e20020500c1341c28001420315550481d080f5440e00d110781d40b00c00c400d1000a110440300078009551103070108040b41000b803c1894104c1e1140b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 863872670 1250 863871420 863871457
    0x50d0303020c070b0f03060a080a120e04060b220501020a080922020706150b1317120a030212100509060904061508010203041101030b0d110d0b250807050f 68
    0xe941d15400c484d482c176045040100412a10f0309000d5850400307170107000300074400351100b030b40d8244e0840810311912040101c200d50041d150707100d41d00f00d900500954840300361900380740407420060000f80303441451707440315a8100050b15400896001c3c50150021009840c2c01d140b501441b0450100061010f0400892008405007600da803018108007803055501013500c1e40d0710110000308020a41084401da20208905400ca5143c0d442100071905840c07040c15800320603011840c03c0071101501001c1c0c208000a080044a5143c0d0085c000030074503210f00c2c0903e842e12031261030001d08034003d0540181e4003501041c01403811000882c0d003c1d10602c0042449003000c4425031081c1490307032004019030340100502007003014452485104000030303c2c0400c0089442c800088040070340b00d40c06030411141d00c111a415451300001c11000b04d8000703806480d03c1c208500c0103c460800c142c6001403a1440c06d45070340c0094450205140035510341d948190900038108004052540603100044040c400c85 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 863873920 1250 863872670 863872679
    0x6040e0d08071403010315050a050c040e1b0a0809010e0304050a1403011e201206010516050d0f26061c02190612090b0106030504050a02030109050f0f07050d0303020c07 74
    0x3004501847c811600100444010300003081624005001c0384100b034104003c00c100d00400c6002eaa084507080004007006441d000b0003600703041c2105074a01ca02941c005000c02409801aa0840c00340407000300810030040d1481c2c00d9070303d0340141e00407558400107208040102c580c0d04a485c1d014500002c0000849045002d03042003e9030706680340051164442c010300d41080090800701426421500c101460014801181c40302010300a0060307040c0603000c1048001d000ca41400e0038502544181151030fa2800b2580c0a00744228442410b000103030148401d01c201e50185240280e00c084504843c1c400d81c0b80d100801c580c0f04240c4615540302c4907900211000740e42c8500c0c141c5020b40280c40c1e06001542803610044c800d11050303009007125410a65170307400080000500c2411145e90740380008254480c0d2614038188034a5500c040e42c950f00f40809002406004101e00400001410480b144e0f04604c004c41038691815201d5180d11103416411200464020b030014940c0c801a0300a80715600d480307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 863875170 1250 863873920 863873957
    0x20a0b071110061404050105060f0307090f03080d0b010f0804030809120d020910180308070606031a22021c05150c0409060b0403022101061a09040506040e0d0807 71
    0x100072034181c2d95141c01040080418105560282840681d4240502d40c10407010801c0c6218101d03100a0745c407c0003001a98980c400c00b40c6401a000079036074000600e50720704201d61039400100366101d1252808001118560082c66420b001444546850ba082d9843d42c0341500c0101008048030034501400c100c011000308820006e1040c000d04210042e10b4602440c14000d0040ba04003841c424054030425200c82541e407040c0103412654451125036440d09240792000c05001154002030600050301e03090103618107040703445442581c0740e020421800c0c0e88801840d00c0e01c200008041c0d004419281544076000c0e10002080744580144100c60b5000c106c01c02810f417242084907100201c0002280074000c400f0540101c100904188501034281410360300000c100600014020011003008030020804600a40110000301b01d09482e150056041c83c40700a0540c4c0090415449280f4007400108145040d100b1100b00c50301c0000104428000c2d0041558103810103001e0100740925403040504403200b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 863876420 1250 863875170 863875183
    0x4080c0f1c170a050604200a0f0e0d06051e0108150f150f0307050406060c0213200d0f330806070e010e040f0b0a080607020a0b0711 58
    0x100805500e000403001858050410310410100810080404500c040c00c0d600b85030448885240055942c446000013030090251181c102d41d50420158144902d03e568409011020700603251900614481c00044a00540200c115a4440304c469120408609503501c01540070b82e0b81c14000141141480b003080d41580c00340c0c00340c000365101100f0020154410180141c1060600b41d48031340d581060350324246000f56403045540035111007103e8803120340e402c01410000f0a4050020058142c4408000741704504050085c0d004035100780700d01d440f4600500c00c80c554404018807650515404201003012548070341d41214070161281c884164003452846030751000c1095081101200b089400403090184105802001500340020104018903022500d658094a6480c1c030366007078901c080050f0f07000b104940e9056003151030600d0002c00c0e1500c07507000c0e8031400c100311031a40d06180e5620b949642c9507021600b00005820160f00d180c0001c1c4071800550300403016040040c2c0840108a0992401e00e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 863877670 1250 863876420 863876443
    0x9080d0504050703021212030a09050c091f0b070503040e060a0306150501140a090b0d021c020c0c12070b070618060504140a0b04080f041e0816120b04080c 68
    0x2040f9010810461620140d4240c1d654141c8000d8200c036030311010900700340c0c000244070410f03481d00c51104100f04001440f06641580000f00003840f00c2c20200800420a56040ca00d15030110100d0310120307140c0540c13000c2c7d440c01c0f42e101c0c0086142c14240100d10724421000741c9919000b401d000801310016815005000841c09180080078807580741500040203407101400001c100d41701048100802a44292907000307558400c44042c1da0350111141c100020320500c1e11181c0700300c5060700001c1c8605980e40042c50000c06040c2140c69001300c01041160481c0c090400e80c07025070001c02e0030040718000b40041e18400f4091200000c80c0792039099482c0030f45207084012a100c41e0f8803000c01041001c6200602c3c0c200c09110300901041259594841c12104080d00203026004049030317210030417038120708403806454800c681e401a00c003400d518075229401c500942c002e03801040d4a04118448140c000350803591414603050800d030058686008240018006a605180401c0b9007000440200701014014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 863878920 1250 863877670 863877673
    0x1b020303150111060a05060f10020109020f180109051b0f030430050708070f0b10060216120f050102130807080d0c1b031e0b07030b0a060309080d050405 67
    0x3072411112075604050003128030780c1400340e04036085000c2c1400151069000d02031001c0020513484480c006400c4100701845075901107582050140010f906400010310a4030aa810804800c40601080800c408200101214515582c01080b000c41140c002e55000248141110460215201044010380c0010703a00d400703240340041440108074944807a03c400105d811841d4500d100d510070902c145031050a82401003042c0800e0712002e01400030212030340f03c4d80c80180041e00248078907280e00d00ca00301702d074801409120b1220028506001003a5001d00c0418110310302c15031405c0800080129403003401c10754039842c0744015900090030910040106074000400342130100d1400581610f004560f40100c041ca40020034080034054108408074a4264080d183c201c25541c118864101c0d0121948060040d0f80d10540c0008449416410b086007203004070b00034206a550b1950917000d0b03805800700150014800700081040e02e01c01e501948107640b103410941d2400311210107510586000781c1d01620382c0e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 863880170 1250 863878920 863878927
    0x30e03061e191b080601170a020f120f0106021002160312090c0603020d06050315060402031e0c0901170906071812050f010507080c1206060702090708070305070c0203031c1b0203 78
    0x4940d00220002d611401c00d291046805001020030300c038110010f821808d203148c01007903900050301c000c0d003550380310b5501506030360701b91604010340300c074611007885420058000c00f918031010302018001c0703503088030500c0031141c810000c40d58201c0e07183c0a0310f08078665080d0369465080000d000040031200400f0346540160716030344280001c0c0b0860707450b030340943e109a119401da034030301c0700c1c0703007095564000ca04540050701e0340d0ba41280800790205241e40b03182e19070040e41c00c102940c2d02e00b80c05004541800e0b40c2d5040500244072a00701d0728201543d000c0d1550303200c0800a00501d01c10841d000304a10300008000c00e4a54400b05100d1400452000b01e032160031122440074140300074810325610a4647c170700317060903061160018285110301032720800c81d18a0b00c000543c0c035031244000c40300384560103490103241d89090359008141d0074050328003c000038140408110880d2107000c04000132900180694548410702001c00790740e1043d090081c0605449440074049035500c0d6210000340403403030700034640c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 863881420 1250 863880170 863880221
    0x11202010c021203030f070e240703030b030a06060f0b0a08041103012403053901030204120807020406050604060e1e060a0f020c0d0309060e03010f050c07030e03061e19 74
    0x1a5401281e23a40f80589040c040e040880b181c5110403c1251240100c0d1554810305820b0071400380160006203601403240c0750000c42000850340c0a0402c403282d483c80b29035401e40341e6480030711610507182140c0004000c000440c003c41e85042c802d05c0c40150060000410341581d0042d40d814621401c08280384e00d1030031404000b4072605011680c1c0d001007245404e0250246070000381c100307001d01c22282ca407016280842007042c1c2d00072780c102d5001e084400300c00341a100e158540280c295001075412400b96080c031030002030a060102c16101510141e4440c480003490b03020622441d11886140e00411581c0b461000041d521039000503d640d042a0b540c000e501d001c5e00002034600b211404684e809080d0000000700482e40c00040242034900500e03004000d50141c5001078090100011035076469441c0c48203015103555054024583e5910a0f1034501c04410b881d001c240c0c5070401191090700034403031103a0883c0003070241c540c0f0640c004407040d40c406800300c650a001c421540c0300070100e1030300d014884420700e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 863882670 1250 863881420 863881427
    0x306010b041a25060e060c0a020d08010602340602030901020706080402370b040603060b16060504030c0b0a05071e0c031d120709050c03011202010c021203030f07 71
    0x120002010072498070f001d01440080700600001c12115040c086000000300401c0341c15001101650082c42c00c1341c0a504001145221a5100d0403600025200b2051910507282c011409141280c006070040e080b0741102e02e0a0b050038500c524003030408680c03500445400c42e40f100c5000400f40c86241c0c000d5440c0c0540e01c0000e46428001c0e0044010710901d4020880140d460302036802c6c00c0a201d580d5124031505491100300000d1809120b540c5121880d040418050540d00180c011100642d805000c120b690b04600301480c440c9596480000d50414615408940303e07030480f40d085446440c0141c1c42000380d46440e5590081503d529084940360000d010f41d41d54060102c4102d600c00340160828298507880280c40000402d1008040c45014101c6038801000a2003400d55101e000d021080c45100c8100030303941300d07240c90180c00316030352601021404130040e00045d0780c180c406440741212003400c1c980054640d2271254000700c0c0e206108800c1c680d141241880658051001700d080c1d001981403104014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 863883920 1250 863882670 863882699
    0x220b0304020f060f0a050a03270201120c050f0a0507020a032009091504020a05060703020703060e07031203110f0d0506120f0d0e180f09010b010f0c03031503020306010b04 75
    0x56128040501c165084c0c510002c3c00c0361044031080c04c0440e42c80a01003400e502031721a00f4801100498007002c00382c1c1c540580c4031400c1b07400380300340d90f58013002d8071154413542160060781040c80019030078080d00e9820700305400104000c1c101030030440c0c00d11845da4009000d02d04907800c00c903241c1520388a030042c0342300880d941110040040312200e8107407030801440307903844031714103507070311503100f10001003002d6446207030020001c2c041c09048260f4841c920300b4040d6550744c1a103c211603c2d8039040320100050030104070300003640d0380050b03520203010121908502414600c0c1484411110422005070080d4003034004042c090210103000c165440c1081c108407090854102c82c1c20319800480c02040f14000106050458810900f0007014010056000c0b981044555040404510010040c02201c8400c003648500c07410000c0001c0c80003001940044840c8008440c4c8032011441464201001a0003600600350940c6201b00e54071040b03039280c00080c030b814002ea100c2046201d0004050100e048420000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 863885170 1250 863883920 863883949
    0x4021e0d150b22270e06130b0603010b03070b0315090403030e0d09050603010b180303120603060112080d0e0a0609030e030c060f040311030f030408010b010f02160605220b030402 78
    0x20f1045035440d01c54030000e4442116140c400c0d94001d0003020b01241059400017001e0304440086880c24640700e100b02050141c41c20003540c000b030b543c3c00062103a14050060744035a0001501419040e4a400c0c00030303185820150050604d010184003025072500c8800e001e0b440360303000782d80225403600c46007a000c1c140750b01070200e00108002c41030244820388a030070880b41107481d005c1d0303040d0765259090078001f400030a122180e50725000c00075401a03041404000503000300350443c141ca1160b40e942c10b404c408440718a0000b08520020301070101203002c42da0201e21402c0c2010b0982d051640746a85000c11616400c1046000c22200401280030703050400c005404a4420303245280b80c121004061000342c000c52200900120010b401c64010351014052140441c11a20459489030b0722075007214080d2080a0300240018144001c1c025018400550a00141c4203c034000d400d560401c01c2c00c0711958030144503c2d9140d81e0245c02d2615640f4144050300081071011001902e03418144104104461146003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 863886420 1250 863885170 863885227
    0x12090e0c0a091401020708010617120c0c09070e060c0d0210060501021f020403150203061302120a2c0c120109020105191803050109020f04021e0d150b 66
    0x5140141d0380c0001d650825240041078180c1036841d0040102d2915500f0b800810155003401070005002d80403496208241800fa4182d541d2000c41030096a11800f900b5000c0b50554405600c142e11030804d000700a0300204a440c03e03586120f964000b051b002c2d40315940030b52260788194658001582e05000c0000800030349d41060001d1843c050000356945903ea11b807a01e52500d504021505207400d03030441303004690081500c1c100300d65180b204c000940003294060300805400000f03c00211702e43c82111180700882001400c0e070703101e003008000204201c106442c0140015440204122240c0074203510a03d401d000030709501001c0402d001206c05c060f1840c0320303580e0410140f00300607078100c02a01c20f4211034503000b106d41001d0102c2100d5800e070360b1084400c1e0700510704001c001d0150640001180368026190341025402c0c60003484200d1092140920040705120300d0903820140100c02400c52155048010500407004031101002e0f080da603000303d019540029501056810803080c1c03480400160340b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 863887670 1250 863886420 863886427
    0x2210a0e0606030d03020f090d1511041a03072c03010e190b10031b03050c0904020a050409050109021003051614040b0c0115091d1903081312090e0c 65
    0x2000c42da03a04c40c10400101403507008580c085450711001c041c1d43c1000b070010441c0300052883d080c590303003005030352181a5400f420f10701245640c42040c0102d90031180a1140030341d61058044041a003a00081c00d050100701039a01d2486030803c410001a020b000c0c81005000d484540c0c01c109800c442e2002800b1041d500602130603181004400949030741d251700079508541035500e00100403002c03409500014a00c81644104210402ea001002400d5a00c1102203403080200103080242d05282100d00030742c0010511400d008a040c150424442c3d28415400801c15040f5540081c0410909041490020343e50b0410081441405c115803001d1442e00d0415014a04802c01a9916449a4042c08008280c00a0403801540c800d41c0030581d00704800c40040d41d03098451001c5005046a017180d51190010721b10400300010002c13454003108070250b030351559050b501c0c0e035054500c10781c02000f00350005001980200070510300301d022903101c240e5a0f0b075100e0403420280d01800000014001049010061 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 863888920 1250 863887670 863887681
    0xb01030b09070e1f0f08010608040c090c170f1e15041508010f0c090b091804030c020d030909050705070b070c0606080d0918111b0102210a0e06 63
    0x3200c002c2d00316100d45020307002d507500c1c04041658413404070041c0c10002101509a500c1a03484a132040741100c1c1d60fa11014141da81d444c0803905c0c0002030307402802501d01c00008200c01205940001054043e80c1000c4a1010440940702070307171102100c46d50944c0d41c1d00020401294564040501900301c90340c0000740354100064031440b0069841c40d00f90140d1b41d1815034035594050740d900e00000300f40d180d00920900c0c19481c1501c02402c407803440180441c05c04030700450f000400e00d041e58202100502001d070240040c004c07041d02d406001d4000e07000d005030000450301503162414007a1683c1d0180d00e070110603e1811000d81700315071000b40103104000d003d02c000c100140c0503100300381d005009803400314844080360801400600940d80315041900c9009141030300305412070400000c452446085001c1c4c50034504234017050f0307594400c0194100c501088841031544041350201203190a110006080007410248140c0c038920284038549445104000c100e00c521540c0126114655200060203d0f802c00307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 863890170 1250 863888920 863888929
    0x1d0601090f090902312715020c01090819030504020d0f032115090203090c2b030c06180b01050d151406011d060a0c082b0b01030b 57
    0x3034000c11050b1501c4038070002c00d65507052503454000b05004000351002c01e007080326000713102c03244440d26820703800c080d20381d0340010f840c05242c00c00c4605411880d00d5240540c7c1c4000b204100d110842949950912011441803c24482c019405216182d2103076500c400e80b0340c40e22444482d81c2040304042c00c0a04100c016290501e01c084285e900098403100e48400b481c0540c1c015414002402c0c1d211140d950110700071501d070700556844941010a0200180c9030384500c4182e04c03003207981c01c0a55200511400060500005801000075564100442c608481d200118100c5a1450940005d03484140100c05d00030140b144002c40c1c074014881700103078400fa039641c00c110041481014451042e800d445001d0061558a22030300005440e010000644400c00340700d1940d00c1555400c0c001180402c281e0401405100507110602c0010074a90904802000443d658900350f10304562000b03007884000b41c40112410540030000525a000d060344a0560428080340c103c90a964101810701d42605001d840c4c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 863891420 1250 863890170 863890199
    0xd090c150e150d0510050f0f0a030b1e07120f18020f04090807051e07080705060307260108010b040c1209051f09060c0e092a041d060109 60
    0x142500c03000c0040b003520001c00514040c1c0c1c95020301c6141400c003044088110402040143d8004448281250000c0f40510603086072007842182c10402d000c0041c0082800b1010391503022011404807150214030700d034150b5041e54181e03112008590b00b42101d000341d000c140100d503c800c180700b00070401d504010402c003032219021403020b806808104a00c0c0540e03121900030300c25260300442c06544c0c130507041c6446aa512204060007001030014040031480000c04590342c0c00b2104104010800c0c1030620b410025640e001410741070034810003c450041d07210851200300c0ba00440b0084045081d850001c05500751481d001180344520b142000d400000c54000e048030242040c8400002041c51441c50001e10300f00d60f040402803000c0c4001e00c840d0754900c8540255102030710450044c0031640f05079000717031605004040059480f9035000300280c1d8441c3c074101d001c5100502c8000d529440038021683c40050307402500100313850000ea00052401c80007011581c1c1d0003210a2a04020503440c20f2000c00c0b4000c0e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 863892670 1250 863891420 863891447
    0x2d0b0c03190b01140c07030b0c1306110c1f08091204061407020301110d0b0f060304152904060e0f07050705120d06081507020d03200d090c15 62
    0x503550a0702082d281d00c40c042c0f5810090300085071950f11000c40000380c1d661901480111035480c01500019800b40b20383d415905c400c1402280419541c0c14004140c400c2c2e0001380403030f60140b242c6910030040395500700d00303100c80c1040c800401e0041d80840d50000d000c103400a10742c42d815803200b0345100450100d002202c049176070382d140404641030700da480484580304080000c4c0d031642c01c080f1071010441c04c2400078001d0442c515004c1080e1500c00b410b00080310140d1010550100003480000c0200d0710b06024103400e5400c41000140030f81103108210140d0f0311602c50021315100c20420080503040038801c0801406844002d505107242030783c2c000c1c031411401400b21042060200302d207410171400f01301c00b0300e14100b6109d0302c580b40c2c003140c03015100400e454411458175103c0c180c90300c841c142d0443d04541c080c44250303018018010014400f40d000d00b0060300b480b0400c1c1c0c0032041540d0380c00d2895019001751180f1240210341c80c1c241c1d081c4154005560380200003a1109107039809840c54100140c62600f5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 863893920 1250 863892670 863892721
    0x30c100e0f01090f090b030d020a080a2d080105040f0207021e060d1e110315190b0f09040c020607050909040317041b0902120a092d0b0c03 61
    0x200310345001224060f207079a100d2031600070450b030082a210059007111075113080580c00c0310510460f03403070200d036191104d10380600303220020406c0401c614440d0074281c0c0940a10105e89501c0c20122507481812200c0e807040c0030010305200c005010ba85130902900c895030500381d00940c03c00c007054000500081d0b400707ca80201c0c0c150640c2900e000c1d1640400c1e80c52500c4450020444180d10b220418460800995800038036460300c41c00001145003082036902a4220304201603e0010b11001d0010384203a04402840c21101030070001124503511009002c26050301501944607090001484180c03110340309810706540100c010440115400300640c2c000c4401164402002d44442c01d0030f5074240f002c4803c000c40c21500c0f404001c18400e041880c0300448100543c5840303c40e0b0b6072002e580072806010320454009542a005c5031208086410030850a8040c040c52004030014014040d80209044206220341d041000c26005101100a5007603026510045d0315166150103c03800304904013080284440c2e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 863895170 1250 863893920 863893939
    0xe100c02011415010f03050103120f140c101d0607121b0c0512270301060902131e030305030402090711060c07050f2409011104090605030c100e 63
    0x114401d410a282c0400381d4600311545041c00780080d4100256112100c0c0403c00b440d141840141c882d100e010b04881e008203148001c50700c170b00c10885144022622080070820308844210300e14880303800500c0d030705504100030300c1200c03003003030b505c2c8155000c0d60040740d41004603000d500024800070030b610794000168984800700b60b25141d91a00100510034404044140d020491a802ca40010f00b860310b41c0d004901310766400801c5240450b4911030151001503d003ea5a00d0404480c3e209504d0f0640f40b50050001c5046c4d0345401c42c07007080303810415a11180b044110383c1046210b269580001c40000101d80d450000c900316100a000d5100103800207010f684003900048245104e884108241d07040e0750250340e00c0d41000d0f00f0080380343c0c200b11001d494900a902040108020020b107903401006132820301407091841504000c00204002e280700c400d5500c8010b4402140c404a00500c0130700b40d41038000035500c4c01d01003810303d000c80f101a040d004180d41055400b2a5070007400d2168000b504640905c032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 863896420 1250 863895170 863895191
    0x512030c070b1b0d05090108060406140d0807050f010203061206010302030a0816050d0810061e18080d0507060b09040213020c010f0203190b01080709150309050a15050a0e10 76
    0x1401e10324003400c02c040d0040210b4000503580c045d005007920079099031070144907180c0c0b9003000200c03291742c4211a243d5010030040744140c00c05c05804000c4034015172225090003002c1d02c0303c6092800510102040c1d95002007008440c3c54001144100400340c030009011560442d808240c0d01d240b007090142807428041070000300d801019030810901544202034401d542c4903c24040e00218041d10410250a0b1440d4007141003403044410701c041100503038035004035004000058980d0b030664407048040c4d1700e070709401148980e03041188250341001561019078582c0d46003002e90490b01c0550510b4408c0c60a10244805a500c0070b4045c0e8030051401001030b504c0300110000f90041400380c40090348680040100b0818425940c8004201150301c1814000d090340c15004445892007242c2040c042183c55a0902101c00410701201040c54942400120000246c6600d450820181802c44035035108080c13400448105010300e54000c0207031072060000d450001620341d00d0b00c0446414240e880c5d6665903404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 863897670 1250 863896420 863896447
    0x3090415051f050307031a130903030b0f01091418070e03070e060d02040f06051011060f0c0a0c020d080705030c071406180a12050a14030306010e09040311010203100512030c070b 78
    0x400815004023400c805503080d18072100540503c00c0242c010138a0030800030041c0c00d110005c9411024141e4800001a0030450034410050b00a00c2554100117074060741240600f0002140d0b0107050300c1c1d00d400c1d461450005c200761515509400c5048180040b000340302064a81c8022040e5440c2e04460116a54409800610003011164040b503401100601140d4030320790130104800803002080141d4102d80e5940c5104004c03800150340d1091b14500c10001686c1c50b502c241d1050b0140307072009240410f00c04140c0c444a609400c14841910260000030b4050000e10301088841c00424001c1426000c1c0181840054240c0c0156409901041c3c00c0c1e511400f0b456075103070510001b07406964801501101a800c0c00da80d200d98600085030035103080c4401c01c140321400400e40b842044140d442104541141c0103001a5050240c01242030011185030104401e13400e0000d10b00c101501c000740540649041c08106440e0622520166107410800c101c0001c81c00201e003203402d444100c05078507038860070302c691786 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 863898920 1250 863897670 863897711
    0x1204080703142d0306010905090c1204060b0102010c0e030c061815090114030f04060b011205041412120406020a05071502030601030b121506010203090415051f05030703 74
    0x80444000050300310003d00c080c0d4222036803d60056158611030b0740030158000a20040d90068046010070104022a182c8041100d42c4100c0c51480d40b41010f04840c0b102d02c04d042c0949044600c3d503100d100154007940d09100e43c50f074800351480c0c41c0c0d617840307071100100c0d44500d40340142a0058000280c200340300d01569020b8000040050610390b035005172140003109641000d030890340007484d002d1103802048429801c3d00d01402420005001a450b03503581c11006210300c01ca041c4c1440f0403050403c0d41d040042c411580304d113026015002108800c01c4c07800b41450034a52020740c0169062000250780c15030b0942140d07105500481c0180e544d540e41c03100788c9142c00b030300030020500c4128032628170100403160051030041d00c080e201400088115000c010403810808242030b441d40c04040882c0c41a481d4400d8142c2010040c0156031401c0400d00114054600740303a03010b44018803018007000746040140019a04003034070040d06680c800c207007034000c2030380c400a03100f134003095118a1141900345002110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 863900170 1250 863898920 863898947
    0x60607050a1b0f15120902060310090c0302160609020301060b0d0c031401050f131d0703150e07121505041b060e10080c07052d031204080703 62
    0x2100ea00021a1401e1035140140c502c0906030488429000103090300c2030406541910908a80c001ca00c0c2680513049580c10400707a242c05c076642d110002e05015031984e00040d401040c0d00e01422040b9428481c260068440380300710441014410015504141c400741a820340d0b0503440384000c034800c20346000083c090412904504600407000402c1e41c81c4280d154408414400c42d070f1414440340320a20070300001c215003449226000b00b60211b1044940c80c00011001d15070b40034810000c0d05107200c2c0d051090440000c1c1c161840e43c0c0c0940024000c2c031960441d80000141040014007920903c41c1100d601d801003440b07205d8070510036503122020442c02c0381e100c140f20385000d403082246180608054012418040e40311b42c20007007095002c1007035441180c0b80092000080c21003c02c103c45080f085403400b0340144039160780101444a0000254103201107070f02801d924000e00440c55840f07003400501b11801c181109568010044c00c98170644851280e54899007010aa54482c8007a0805944103d01580c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 863901420 1250 863900170 863900173
    0x150e060c0336030115030204151e030b0c0a0c150603050105040c05091005311d07060c0c0303081509010602060117030c1905070b07060c030509160e06060705 69
    0x80b1062015051540540c604101c0e94000604902c0c010516080718110f0300c07140018403042d0010f201505154010a5018285a0740526010b60302d0b41c00f11403900b4210076900e9500c0c1220020010b0200308604507030014040704680d0f150981998000d004840c01d80b500500c20307992050b110b9000c1d003155200740000d64210009001c07602e000d1901c00c06d2840c0310301816118190309000b040010070300107035200a50300064004107809a5010300f03d0901c1c104440c40c001250300141000d801040d1038081c0a070654046808140c0d0250b05610050608c07103103400904c10072104410141c0464800100b1030101c07a01401c14504544800d100300c0d9401a01c07594076500050405c000160f4141d00081150484110348401001410b01f041205d860344144180c0d40724540c0024406c1c0000b4000030402000301340708604851300709990381060125608250415680159100c20744000701c1c0d050300039079030b000c4105000791242c06d08110103a2100c103030320300800d02d448500c4000500940c407030100315403565401c4030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 863902670 1250 863901420 863901457
    0x609080304050607121211040302040c0f020604060203060d050f0d030518030913022101061e050405090603160305030409270303200d0203010911070b15030319050310150e060c03 78
    0xa191071303e20f512511082f0b000760b107448041c03040540b0070b03c1c1c0100000310700c2d4007600007900d80d0303201c5202035000039203801d070301c500e01c194280009001007088440b0005442c01811104c504031034007034200c80300103242d25296016688011458440030040f10080442101c20300b688200d03104820300203000700c20501d07840070b410203020200705152450160403985030340e58200007031006415040440180f21072020101d002800180160714106a080d03501c650054200ca4072030340310384030f01d05070310300146d10542d001d40000405225146140c01082d51019069814654041e04c1a03541c4404960340180a41095914100c503242c01f1040100000b200030904071968a071192a17906600960080c821407401501d0002e403d102110580c0c00d071454260007080f860782c03594445008200d00c1c0c02d40021154540820004a5000d1241551100c0c0b5017820741d503003544a140c0600144440482604403090a0b4040441d110859600a00741c800050040c0d848503100e4104808540c51030060403469030342c0c00503e5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 863903920 1250 863902670 863902691
    0xa0f060e151e070903122f010606021605090a0f05181c080c031306020a020d08010e0906041709060d05041e1101030e03040801020d0c081b0d2c0706090803040506071212 74
    0x64160000050403c7d00800019540780030990751407007108035558240b48408810491480d0606006600406140011401411030ba602004494080390410380d649d0300941d00054007501044001c0440c254560381c0c1c0402510814094030103100188080680310b0f00000080000c1d0b08610004240c903800401551a070101f26006034450690022181c0020801c0c00006288569211031a014103640c002a140d00e03240c03038071907100b104404400c03c4071500b800c1203a2070300c40c0c880c0f50050141c041c0304200040e06040034582a0503070008074003404a500d01071405280841e510760550b42c0e48040900340004d000c0420141242103004640c8501c0b000d5101090000492109412200760550141c0d105816035443c1c4810f04081900c100703034141181c4090000c8008510035602c0360380105c602c079084800303249440d50544200e1400c1d000c04c00c5150001401044507541000d0307148042c0010070051802d01d41428040703612070107403001c00f80084401482c0240500c0c05224811a6040610001d0200c2d0808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 863905170 1250 863903920 863903987
    0x3040618051e0d0207140f010c0b0f070f050702010f081f080c040b011403010302060901050705010f0e190201080c13030803010f14040c020a0f060e151e07090312 71
    0x30b9001184940c014220302404052002c6064015030342c0720069841083c0c80802480110080140c0d940d040c0925005c1031000b149151030300c280301d0f161040190074985440300c001000c0c00000300e000000d20200340900001030307801035001c0080341a58500f003052940d03034000544403241e1034810402e003281d403190080381425001c500c040201a00f56014030030005000b004640b03c00016a031036050820a10041c030040c50660020801803005250007420282c0301e480703440c21240813144a0305080d9882e0101c901209003400091010450351211124404030364001909070f070380090152280d03500004004c00790008280150000d5900245250349a6840c1c0d44240e4032042c01e400761142048403409c10008626260041a080c844e140d4050407a02d1000d9a6068540f540100b080700c030b8548500100d20755503001c02c410f12000e031040c40c0d40c414504004421507034007488030616547c541000c0c800c01442c10741120b0000201e036030144c80c5100341034031171204407601107014a0010b036000e00c00c481c3c107140d1000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 863906420 1250 863905170 863905213
    0x9080d06060c0b04030e01020102040320010807142a1c020609012913020f0a03050c0307020319090801060f0626072703030302031e06060304061805 65
    0x1402010400251120025a0340764509100140000800c900040000c0e105404400540806000260505489645599100b040482c10000031000030341c50342e1072584d02455458100055080ca00180032007004080003d02c2125036010611100d0307500d49120000603466211495010401c1e507500e0b04e4400d03010020310307a024444500501c078410105044401c18422845860000800e00503000c0881c00340c40d1090280d01c04c1664805d03140c000030b10a10b590350004007119074034500e8060b902d001c13424010301141c2000d0220321501000303000f000240d81d0000708603a4121545c0030401d064100d080001c032040e000c1c40e0800c121035402d007100040d0150240040ca8203581041c1ca036244030002c1e8100c1044680040c0f5031001e6182c140e04003064a0394040c04030007a00c61001d452211506660144181c0b80c00701d20350080b40000d5000040040405581c074cc06071a15034151a0380b08581000d100141d52404054806400240e86140c0e0b1407014a100c4000040154414103540c07541d4010501e0990030302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 863907670 1250 863906420 863906437
    0x3040b0c120f030123010503060904240e0127173631091a01140108040302060c0d1d0a0606060e0a1503020417010204090c03020f12040606090908 64
    0x1107417103030707142c031071a2a404000403214107030b54080c00c5546032420080b10b06800f07003040d01c0c0c50350700007220b8002006179204244070700d040c1d100214464810041c4607013100c2d204591b004484088040a40152100402c0003480680000c0a4203040b44213101421083c458100c0345071841f800000b5500c1860180e4000c5600d070a220303184018405554410f0084007811840c280036904004441400440a185071203000e04a100000060b005480da03610485603085201d0302a104800e21300400149500340500e100c452001c0c81c0c160707d05e0400d0b6401954581019000c2441010089162100415070703a000b00b5820700c2c00700501e0340300c1188603116a01c03016002000c1e03640a080080218503980105d1929002c54400390000c055246480702c000050650245040105902080005560482c040b074540c690319101d40010781d12490200307921301f00d50340050b075041418014002d000041560100381c1350600350200d02d6105079a143d1074403400030040741c0c000301c00d03592a00c1c4901e018000407074040c0c000c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 863908920 1250 863907670 863907689
    0xe0405011812080403050c1005040c0501020703200d0b04080a180b0405190302091006121a100311182b12030908120a0510030503040b0c120f0301 64
    0x1e10032200740d8604080c10703031406850010020500038000703100d94802603101e4040c0c03a00324101a002058075003051812550402c00035180c0041c0411700066a0481e030042100740000e12045103140e56100349094078444034052200501d0301c003805600c3e00c89116844030f1303102141c0e039018909440c0c6005903800140c2401d0014446803d42d8401d0340903070410324150b5903030008c0c50b410300b07251030308210b80075200c40761070203c14a030000000010b0700c1c6e80c6c44150041e201044e1110115060040041102c21012000c00c0010700f88011240e101840050b10221010306844401645550403030990140003603034115168004000303400740541d0440d081d1700c14440000c481c40420310b002140d003184c29521401b000241007040703181100015210500c8646090383e142408946803a09454901c1d45800c602c0d50720300d16640c0130040105d441094414075070310050b2500908401410354448030760b00c1c0624050f000200f41c3c00110402c41070801c005882000d03000c0e1984035629000341680607c03680081c070030100b01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 863910170 1250 863908920 863908931
    0x50402090d14032206030e010e100902121005071701031707080705061501030e1c05221e1e09020f04080307080706112104020402120403030b0907020c130b190e040501 73
    0x22144180604c0c5027481807a401440d50401d0b1007100b9000301000d110072a800000e94000700240701c2c040c000e00074a0784413050000380524014001808103140054020b25450f01e04c40140000741108010900009110100c1a200c290b03a01c1d249074180f2401c079018200c2d20910080000080d511076130707401a0030081c1d0302402500c0008801c02d5507003d24186003500e0148410140300164483c5024001e2240821401d00c882540700d500b00100f807116420456482d81d802e601c804d00207070f100c20b40c680109006500c05d040702c664103602c075094600714059600f8141d0005682d04000f019182900d0103405883d080c0d030390311326032480c2c501d455610228044036610700300108490041102d00c2683c020005000d1000d80419540c4014650508018422680079900344a01078040ca040c2d10620b100e548291030008140311444200300681c1c8008000f60219800408a802180c070342c0c41c1012481c1201715000300e03542c50f00000203802210380306940480d04000f100300003580e0b001c030b000a0303004601a0000300f0a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 863911420 1250 863910170 863910191
    0x6150605070b150604030807080d0623090612010c0c05061605030a02071a0c07110901060509120f060c0d060e010501140901030917090a050402090d1403220603 70
    0xa4a00601c0d201a014400010025480000003101e603020b2040c01040b0b03c0c075050b120741e0b0f0f40d0910b4201520980e42110049900040c2980714800e51015116064018901c0d050724141ca03034000200c0107615000d8515480800c442d81c5400091000c2c20041c14000e000d110300c103000003018140c4c0360780b050714944925800b01d003448140b0007125280000170f03510300303213503546043c2040083d503c000000c0310600c4419a9103281540803440301b0f401078070b100d003049648000e6810806840d0f41c191014503c58203820004001c90340c4c1040868000c944181c0c1c0301668400090141d03030034400302060084903400b03200d08204a5a46c0c2200405641c802c00402f04450303a10b803c4801348144003409240d0226900c00c180d140c0d80d62041c0c0c050304480105140100c5d415403156605901c201504030403024500e00800e0300409880c0c0740706400c000e80810b88007103040000c00d000044402100721000703409000c00c08851203032008244100d4070101e14002c0b00c0e1101d18007007500c0941c084154401d280000b0b10b45001c855 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 863912670 1250 863911420 863911427
    0x90515040506060910200d080402030f0105070e01030908090409050a1203060f06032c010b010311071502032203020d030e03120c03180106080106050a0e0c07081c0207061506 76
    0x940807003000e0100150019084400d036603034420000003a80701500c01c0303003446c81e8100c00c200001d1300d0022a0f1300d0b0000750800703106251034440501c1c1c14800c241d052000300300b01d455001041c907665250074600030030340307085504200180f44280410300e40c05c981040b50b80400d000b000608c11030b20034440c0d0181c4440c42d212030012012107109d400303112241032402404120140c840d0304808007012000b030604002c0d1413051100003445c000818003901c107075140c00030005030350780511815803542d4041d90414a8059142da510b07100300a4115a94074443d40840400c1c7c0f2000e84900d80c04881490305400c1520b8901e508001e95110140c220820000c0d0500c0d83c3d40810110100a49011102d03204110480384c0340c01d0315142c4550002401c4c0e0624808017201d01551040901800340107040791000010441d0800003030040780c2e05e0541088500d40d100c40e06010504550004603600b0641041c6425118800d034040c81505c0008080d00912690000c502c01062210a50090002c42d103c0f511000f00166500d000b0b8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 863913920 1250 863912670 863912677
    0x1090503031309020f2208010c2109030e330c0c21032a01020a02120304110a0e06041b02151504020f0c0705011409011809051504050606 60
    0x31000c20b41c0100d401c020206954000d442116040c1d900c09081c0b5500c2825001590400c00190300700d00790080080100c20030030f00c0b410591004510b041a104030f80410480701d81c581c84200c0c07030b0040e0342d40e190354424036100b80149280d484000342680b400008881c44041907280942114800d542c1481d0040048103404c0201d8030824100805012640200e0041140203240001c0d4480c039084101658010544284014140c0703002064140c0e454030140ea410401c186032440791106507038030400c000003a00d42c000454803042c03e0440d800075525a103a107400c481400d004045150020307424080410060011401288074050580d0208100d8402041002c1c44140b44a16074002d41c0042c80004103d041c01d101c40d036441519207000100030703042c84021804076441110303c0010448042140c4041c800c0030321101000f02001d203060500c09202c451400d0309803144034015814031040084d80c80348100c0c4841444010302104030104150b1519a22081145900c920341911542c5040001071031441c090054 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 863915170 1250 863913920 863913937
    0x90f0c1509030a0501050a0e1b06090603070909062d0506180a030803090c0a0602060903030a0c0c0203010c0305010501021203040c0e07020a0c03230a1104020a05070203030f090109050303 82
    0x180340d0328800402034680903510000c806505409044000000f0540901525006e500240c40010301502403800705424400f504016180e2141c040800758215600d0105880c100e850440b0700b03d640380c072080002d0380d03448001d9011302062418981d0026400c0810101e503c000c80c40d28060f8a498400b401d800245151980211a802035050080744458880008042c0ca170a402400c0c0042064a0307803a00320700d503003003203428010ba94080c1210070158100101c05400800c054001810309040c01000d8170346070300000b044041d031329a1b110894407070300d44680420600c058010f0008c000f072482581c00103001e0442409287d01510807904803d007056103800459108a070000d140c0700415081410040c009100908074104501c5218205c90101745c403400104010352007081807501040d07156455500b0801410344008541d00201d0300315000c54110014404071400440d0b0059888038428400d603070a00490308040e41510021a1401d4481d80050044c0b440721000d0300e500c09500c0e5648101562441035a26 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 863916420 1250 863915170 863915179
    0x2b110109090e0a200409080c01060f06020a03030f141023011e050421020301050a1a0f0102100c0201020d05060f03030717190c02010f05182e08090f0c 66
    0x503850100b11300c3d01080e0125030b6030700880040602c5a10001c1c0030f540a42c1010faa20010004070710f01c1d00c0c83c00b442034000070000007440d2a807251030280080c4d212020340740064181070b00c1d0f01e244160b090340c55100700c51001030001d2614580c102841c401d01b08200031300039502c0c41580c5604041c44480d240b414041154030583d640d500c2c034400400b65969554a10801406100041c40049440700941106031010013004603001c22214240c0105800d480001c0d1041508514001c0c2c0701568400010140748008802e8a03004176000304080106e01d006101d902c1c4400980c40c0c1a26107645c01c3c0d040d0010714a20044050900250b143c0b0b2040040403079208080702e03171640c41041008000388502c6c0f151610700e41108811420880800a1012407101041c00d00d40042d0aa6000200310342c0c00115902140d4010300e0494100b46200e040800304030050665284a2410503a80b1381c90302c04090500c0c16059034406040d916502d16120140c00c2110035609945240190304954005100008510039507070b00040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 863917670 1250 863916420 863916433
    0x3020a1e090501181d03030c12100f0512070e07110606030d0c120e03120301050306130206091201020705011a151213060b1815030118022b110109090e 66
    0x100750100408001120642c000174644080300703114020310140d440f41561900041e50340840c0c940f16400c8605c0180001103840103039005103c60702111900b4070075110305a0b01342c109200100c0d803061426880342d120050301c00281c820010801d500480c000c2c89185400112070303e81d11a6401c15454102441a40002460a160440105412140c20118061039082241100c600f06000c00d05010901e0840c02d14603400100422890508000c0c041d4000c0c0824030b5440c02c00200d6000840e5807003034810452040000a0341003c2509003941200d054941c014000c00954041d41d08410a00c03408250080c811440c603504504030404041c201c90b40c00c825030a41807200c0e9078495160f12410b003140070554042da1f688500211a8540e04004001002c0301c01c1c0340e43c2c180ca041c1c0400d48100208130100b034000d904165944d185000307840e0320380c950b1a5048410000c0d84030306800001940411300d00e5060f20301c0143c0d00e00d5040c801c8262000d50400c000baa11511010707180c94004e000c2da403600c040840e0f60b80c80b16 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 863918920 1250 863917670 863917709
    0x303031b031b180b0304050303040b22080306042c010c08070503070807090306020304140709090209040809190e07080703090209060907050408030a030506130b090a1503020a1e090501 80
    0x20412040f510031941d0190f01400d0b1035103006401c40c2c00407141110b0782d0703100100340010b0100b00890240e01a8900ca4032411648100754101031001d50800d006200b01d00100c0404d480396129001481d40c03d48404107401001c8803550311664031000f100300d0714003e510b0280704400301807290162034410b0303045442d624a5a00c400d030382111030000081c01b0304100040c0c00000701c00a041c0b800118096400b0340c12644009600300c006500b0300c403081c2e1000e082549851a550700584403041240e43c450340000c0d1040d1503266074008503880ca0007000885102281e25803010844101c189209400742e281d0f0303030f0b070321520769916003007901145e0384094081c1d4080c0a010000e205840c000c60115404071152402a0900e40d44d0000d00c0e01d59042000c006011903182c03800c02005050a002c280c800c8130244000b40403c0c5100c90201e00310704005008240d078581ca4908c3d0b10690b80b040d1411000450340a8842d1170000c0c1e8505803000140c0311000c40c00c4400081000000780d1741000d0041c94180c0795074680f0641c0321080b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 863920170 1250 863918920 863918927
    0x40605030a0b19020f0d050411192904030c0303020105010605070209010b1b0d0e090f2205011803051209071a0901090305010c0512180a08220303031b031b 68
    0x80d140c210700f03039000c00ca0700c156803103401c024203d4444410300c00700d29401c007450240e140008000005000d11440070300b000408034600d00100440d40d042c2a6551042610b011901c903810280c10b00d41c0c0040c100050000410285079605021240294000c1056907240c42040b01c03d03200b4102c0c0603601c140e03035034010f021000c8908001c00d00700806628080b086420000d20a0409001d0b44607880454012141e01e01d06003072007040154040f8450364450154039020004c00c001c41c0c1244a4035555207500c44a11040110035030200d01443c0d03c428200103050220702d4010403941c401e880c0090408820340100304205030005508080e46c24030071040056104002014038940c0102c0710403410030600400000100340b0a12600d09004901e82c2d074569101c46001c2882445040509031075a0080e00000781c82d00100c01080c0b42c03a802d5881501c20f540e0319602800d403140c00b444651032680c014241c0710000201030b0507500c80450ae0520a0310100e00c442d0b1158290215040c184280240c45039061411845a11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 863921420 1250 863920170 863920201
    0xa051005070e1002010f050103111e032518020a0f030903140a210608011104140904020103020c0d08061311030a110c0708030c15070219111c02040605030a0b 69
    0xb030604c00020b00c50b00002103842502c0083e40b041d140441054a522101c0c00c0000d11114926103001c0e0041407400c0c072802181e83c8086207040ca01039201d090342076441004e0a5003404008010a01d83c003c4042c14114400c40258003c00c0041c0100f04d5403240a40701602a000c2c001c1507940545a51072100c0302e585c0d490b070f02680690102c100f044826a107250165892a91080500722902e0300001c034241440d080a08407210f5070b800c04401041030104104400d440889050314000c1618114000e44030340c0f0040e8041d0292803840c084902074242ea0f040840d0748900b400d88515001c54004280314806841001111072030805009400410000115139104540100c44c1d002d61112400c0c0c030b02802c0b184030604007041c03034004008540001900d80755410042080003c0d07049032340e914440a04000101a40e00c040300012242c904100011100600c03036002c140b0070100c4e40c0501605e1400120040030509090900c008a00c524548030300468281000200245032a0348085800da294480c1560b400784402c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 863922670 1250 863921420 863921449
    0x9240c1c0204090207030302131403030a0e040f0c030b101d06070c120312060e060901090b040e070f0608010905010602060118110a030e19210c0b07020a051005070e 72
    0x26002c0100048500080c0700610f84140243c1c0d005881e0340001141c04120300f025441030456210702c8480301c101d5600401244c4101b021414065602510100401d018003660001d444003285011740e41ea00d00c541681000c3c64a4004444080d91180c1202054a185030b12001440240700403050030845030030504000c04105d40210f80440e10240d81d120560080462200110005105014a94080f40c0c0d18090344001d041000c03e681514544000420302480051040212894039039460b0360315034803168070190208031030b2030a0320785003a140d81d03200030950454411040020030f00000060300c181d462103004d0603107070130703901402081c2d00c1e0015001e0003404850558000f1603440944070010900c0c0300041c601002c4541300880c8824103404043d05240740301400202015255540701c002031514066070481803481f010b810342c4142100e070100c40b00141d4580080421602c6002e00051603000520300ca100b40c4510200d4804107000034018041e07500179a5410b0224070510309030209450503030204007011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 863923920 1250 863922670 863922727
    0x30210090c182a18031208070e03190204200405030c0d020f0d0201090b0c01090c0510080705030a0b041112060a0303050a120219110d0323040201020307020909240c 72
    0x320036400c4c060940e07a1040e13004031400100c110b064401399400c085090703840b083c0d0b4100201043c0f044000300b51168070b0308403a0041c401000384040708641d0b60350b1101c031071000c8124544201a9186001180c10792080c000c4510a1051a080d8074442c58107243c2e210386035038043c000b8070400f0b520b4010301100c000e41c050105d0501c8403009d000328500745400c01914445c1c01420010440c2001410703c1c102c112030b11b0308824015651100800c000c43d810040d901c2d001180d038030700583d5969600864400800c50700d4100350b032041c00e0090f1601d6600c03d21019140000031405406116101c4000b003040f603e5080c072000700840d60902006910758080c0043d824203840484015103884903d510208020b08400e00e040007003860040d000c00380c81f10402915040800c24202080392619040602a4891904070b00d1441c01203014001000c40e4400d0003a100c8943c0d01400d04100c0341400b8050720b45900e0140d02004030003070158011442018402d0003203004504446916240014010038665101200700340400e130f6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 863925170 1250 863923920 863923937
    0x12070212102f031605090d0c090e070303081b120c030708070806012024090d0201050121050a0b181209030d0c030210090c182a 56
    0x4a06010411480280741000a100e03030141211000d020b018030741540d002c0112079610b907414141141200c2c1c024000d550301c040d454126501c00c8640c0d10411031001d8004032032100b04000c100c078028400c010307221180f009001702c42c91207424590b124010b11000d00004d00c1c82012851b00d2140700da590b010b21060712580e504e000600c0000046000d015950494622400800c2061403640187c00c2e0790042140d1500c8240c0c0d0600200003400c40302e22200d104000344004a14000582040003540000d4800801c40c514202181c4c403842d280440031594011140260090442100c0c07041c07048074140c40f082d1030110262041450007502410070076200701d400b44501d40c4128049818200303580e1040c80c010701d21034003164000d11541c1c01c103000c0c4c02810510540078003070000d465038086013403d00d00e1114684501c83c506241030483c601440030b8902c10596203031044940c00d01800315100000d882000600a20850b0760300f02500c1242c10744101090124030300d02c0c0c4260307030881388a04046150094504220b6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 863926420 1250 863925170 863925199
    0x160206160203011401051c020901142404031203060f0b0f16060c09090603021c0804120c05090606070201121a090a050a060b0a1e0318030807091205120702 68
    0x1c440c1c3c03902c0c00640381130036040104032500d4014400c1c4200f050403009010042415801309213a40d80c180114205a20205104100c0c0d45400c401c03801c0b14090b00b1021014446450440300b610741c843d0009070380d105c100042e0001128024007501046426982d14041074500d00107a10300c003034008040413240d102003004001a200b0307145580a014901602c4000303558003d90070081c06401007503000c0442c482c02c00404001607511801201c201196065907040700100f14a403001880c4600d4000c00540311090a1010501c240200440705640040e1012079007a01e0303900030003120b40034556000b030015140c5400c100301000d940d003101c101030095002071310050502c88009050117508440a44166542c0c2040028450583c014400244001d0031980d2611815400c0146401c00c01c0c4440615114103128000300705100b82d02c2820305a07500c40000316603502a103002031088105840030400501640c01c0402c0c0c0d80c4504c0230001410340e22500416445800c824180001e0f04404c4040e40c0c4201342c1c1c007860302c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 863927670 1250 863926420 863926423
    0x10b031f0b0307030b0f040e030d02031f03050604030306171c0201020d0606030b031203010b072a06200606030c040509161806141305061203040603020a020f03160206160203 76
    0x14024030058a0208690400c5006e0100032003840c00b14511031401e1101681c00c00c83d0100841c3c01c410740181d00980e503a5100b0b490324622000c008400c90003002d00c558000b05000001c102540181d00c07aa03010310070700d5510041c6000512150100310030340d810104402400845480c2e401009000340d000150810400144550840d105a4401c1022a880b0701e01c6000d640f0301401600341066100a005045504040340d01001d40145203000380750b10048a1ba00002c80b00d50240242d01501c61b03503540c01c1c1c20b030700c8040044c0700c0c00c4208070303d90400e1b00c01882503410842c0031590302c5c8a90350283c001c10320303c0c05400400c0045c2074003500031440d0703005802503041d0b0003041600707002c040c0c46c64620217010040f050381094100c1c0c02070340c031001d40114104400380c3c4965520b03051000c544514007010480d510340000040544424101401261100280000e841500360b009050354108a400703984010380180c41d01d40e224801c2c16a169284c10b2090080f40040c60b101000d42260103a207883e84152440740c0d400f09 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 863928920 1250 863927670 863927677
    0x7140912010e0a0c080706091a070b07030b130606080a0f02090604080c0a08030406050d0506120105092d0a1236050f030d08090a2a0608010b031f0b 65
    0x20b100ca60083c610352004d0040615000c3d00901d10840140b41c3c16180080040460038180281060124043c00307200d04600a501a2041c490300103044c4072041c00d0500c4041e00901d03403484424043c01d880c0029201c02070085c400c29045070301d41d1312843c1c2107036035050448004040048010001c0741d401d002c1d042c4c3c2ca40b80d220141014141d00002001c003480184200032140d07078140c0c4104c903140c7c8100418440154460f0642e4185e010508020801f0b4030b0705d0000500c2c01000d6420710400d0342ca000100014590002034406225040400303400d0740c08071103060350000d0301c03003c41c0c84680da40c40104c841000401c62501103107410094a04103085250170114954021100c032500440c52080005811050105071800c600074030701101c03a00d804441c200b003c240c45401c2251102c05001086002445001c01072142c0500380782c2c041030001c907212800741001140d041100f032a0000d05207208000c181c4c6800f444406040e660007140f594290350300d50020140b0710415442c80041d210300d04100182100c5501c3c0507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 863930170 1250 863928920 863928941
    0x120302090102071710151a0703090504090b0a05130515040c0e010e1f060c03030b06041a1201120b0114060405040c021b0f0a03020f15070302100f050714091201 70
    0x50413080ca5403454100941e40030240c441ba2490700f040b01048071040b003455100c0ca14051071011620f40085040030b460600340e0381e02044c0c010382402c00740020803580c4c0055601c60f070810481001551500100080a2950500000e10590000008807848031110110551151185103006136880d100d02e02c20025000c00c0c0d00003061161140c0030701c440c110038040b28103e280c039004041e0b00418500b0500900c0381c484c250002d0245035a40b034940c0840d450340012180a4900390400f017111988418858640d41e200103081164102e00100107c4c07601903000400140b40d070130014041c440d03400c10351010b409080d10410541c1c490380c10000021141c845001c1ca103000724a94000d40400e4900301000d080b542014400e061140c83c5600402400d50313280c840c100c054903016200a03420028060209082c0103608000410446d4003240d03034401c1650010b841024144d03003000c01d000506c001c800700c00540724140c3d415404514050b1102d0030080f002d01c041c01e01c14200816514a10011800303107403c54080104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 863931420 1250 863930170 863930173
    0x8090d0c150c050705101a0d0507050406080a05010b091b0a09080a06050103020f0102061b0c0a0503160314040803040e0403170103050f070b19080912161e1203020901020717 76
    0xc3c603805202d001d118059420751450386c14084c00c8103040c02c84248410007040d4038800e21140542c80b061240822200000e024007074020451980c0b10802145e41d81e441746c1c0129004d40c241101c002d11828950006400398072501020074aa2104100c0c04403543c111781100303410000c4420300014054800c10145a050340512000103040d411070051007a885000d500705030666000c20309106115401c00c2c2c240e550303584180850b64440d07080900700c0341040c0391204040c0040c400030a0b022002144404440e45c0144662a03014501c4100302c241031803030142e40724520054205000410402240303224203a07019200789001c00d1496084284c080701c80d042a0000d40311f550185000d5800c074882040310002500c1c2201000e030904901c0d84101a8400401c0902070400140c0b00105083d250304205c0899000c605d0900031f03849080c841c1401d8001c402440f800e482c07941841c0111411510000000c10401d5082482001030a52a0307d058005c0d40c04948680d0440c859010006025a1260503068040c1447c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 863932670 1250 863931420 863931427
    0x50c0f060705031608060f060a030b0603090f0601050a1217160c150203070c1205190302031201050105120a0c091d0a14131b032a0608090d0c150c05 65
    0x440020b1040c941c0721140080c1702c02c402c02d208840d07840301ca04800000b01103990580d11468400c04a01516041c002d250304910080280107a46402280080f400c40151080718040d0b0381c1c607410404803940354800d80303100c0e5501001d0903001c40c0402000410306071003009503a1802011428540c840c1d00410b000750b90400d1058011b1010f05944408010207400d240b0003142841415158000c110100c0c0c820350300c5482c0d501403400b00700035044c050507171316070030301c800000801d1b4240c10040e440360b018241c42a080c168400001c501503000344242d0b410b400007801e225103a40e031044000002001c40001c01c80501110b20400a180c0e0602184c0c4040c10110981410007800c0c680700c85001e84602c88038a14070108900304118805800f0340003441041e400c04030118815181e03120041c5070781815080586150a0340401004544211041501c007800110140d80b260b9a5004120b170110300903036205035160081b0b03801c812254454002d001c406401100c1c04a003041c06145110200c0b010001008042080030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 863933920 1250 863932670 863932681
    0x60a020d020c061806181c120801030f110f120f06060a05060901050f090d06050f06010309110103021b0d031509060302150307030e0610230f01050c0f06070503 70
    0x600c42c00000003020f4401d5403d20740c0d1030380c810381e41c8400900c540d400340c0000f05134040480d051851850f00070001515050742501119203c04140145003c26210b410190078806082d6205e20701090490703401010048940c0110b640320b05025188201c49035014400c8180b0440680e264001c505003d028480204000c000103031a240c02c10038002c0c140391155100040070052030b1035060840340c03a0603003403030220307075442d00030748502201e014030740c00d00e17421000488800080020315807119000303941001c04005a5682c42d00110141c3d003174110002c00344801d10081c8039a0b54041d4001c0d203c0b60381038403210540d032060085520324109495007103030000784e1240704141030b610b82c05000d0b00c05001881c400344450390654011404d0759800c55144060b0090020000ba441403095012012038421074095404600303059240016141d4240035100d013130615034400051203410440b445499245c082c4c071480f1240040401943c0d2a08407180032942400350540304880c3d4842881910311031002500e0b0141c490a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 863935170 1250 863933920 863933923
    0x3090f012016090504020604060318061802010806030303060d111c06020d050c0f0f0d0b1e01030c0203090a031e050d0504150f0e040b041b0c020907180b0a0e060a020d02 74
    0x341c0c40481c2c00c3d46404240005038503018221416180c05080107d5480480c007030b0000c00e00d11141c000340c5090304c0d290003442240c444e06000c0304001d000b42d07a02030003600d468041545a205c2940e04a601c9505000c40d2030008100344051107101070000c0101c44075a08103202404ca15403900003c03140b4903400120600300180c00c0c82420307000f81d1041001c5052000f40a2851000d00c41c56140408010001c2000c06000c00140c00c4210703008000703007090210b1001c0e000c40201c0910180031840c041f03400d0060f000401480001603072082d52f002424603481031720355100c4102124030345141034503400f040541e1402240b03007007100750f04c4810a0350f20350360340c0d80c07400070640c00c280006200c0700100182c0c03a01d075000155000328078900c4210f0482d000544120031320001fa0040082d085646507400c00d1820304081c5540000024174240d00a95810b102c42e07880000440d4400802240e50f0180000000c041c094005000e000c1c0000b501d44d0b0505d410a140040c0c00600306412610060006a0104000c0c0c5e00c6542e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 863936420 1250 863935170 863935213
    0xe13090b0c03040305030f0a020405061c05010e270c0a030317010e0103080f0a030e06070e0a080303010302180c12011413050c091201150e01050910060203090f0120 72
    0x780010124110f042607600203081340f101802d12112410b0130800b1814107040c1da4101e030000d1a008010035502c1484100228074840d61152200745145020700000c1d0000341900d56511825103561000c80c002c10038a5000c103120303200741d030402e80ca00c141d04101c40140c807442402c0c0e010f540291262001c4000780410b141d02e20605800c40c010344051017004000042580701656101d0308001621a02c5080c4003000301c0060101942c2905139102e84010321451a801c003817076001100c015100c80c42226200c40e4501d541e07100c01e00c402508030100c00201c07041b850103a165140c02c5841c10481a1401740740d0541004215000c2c0c108084127422540010020310300350300d51a07035000040c2014040f9251200303107034890b402900b103c00c0c040c804151040034181d400303611000e6071424402000d00110785500400a24510901a2500a00104c1d011034216545100001c2c116035640c0d008501e40b01102d41444a003005040400e030512001050800b0408044489880454442001080e10020100b000c010585 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 863937670 1250 863936420 863936431
    0xc03020307060f0801031202150c0405010221030c0a09080313170f1203060d1a010611060c0d02071104020706090203070f06053009011505010e09160e13090b 69
    0x80b944030303050f00d0308080490304403900100582100d07a1358640907402e25403202c1c1c0c010241140c110411003072006020240058810aa08807034580c99800c1c0c4540c88032031034140724528000c082c000150760680c40d00080c000040c0030710344419417a80d140b00c441e00d541c1100701c4e0b580101d0703290002404510b0b80c1c104025900220342004000800000c40b85613280c0d069038003118902913001000601c2c540301c184102c0700d0654000703204690030303441c4000100348071401c0c0076010000708010a241c2d400ca40004515014244104503949001d4410a6010086d44091001c80d5042e280700010502e42d030311880a441c5042c01100049030040f40b92041605280854000380145021890103010155014080d140311500443c00c032524464030440c5c00c001a01c0b9007803401a00380c0c106042014851041d000001106540006e500ca080d80707820064131520003031a0600d800c41ca01c0400074450030490050040720000c00d04004034200030340404541c08542c0400e150011513100c2e40c0c01000c00060862065010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 863938920 1250 863937670 863937677
    0xe01061d0907030c03020c0d031a03030703021018020405040605151c031b02030d020a170a0c1b2d050d0b0c0717121806150409110402070c0302030706 66
    0x6808040010725403040c0903280c801015580c2044000c50b030300a50441d001103810380708599000005200043c09444407070710411040305408034415850800206403401c0c10341c50b8000c0e10045100340d8610300140340700e2420310703500581030442901607242ca20400c2c1c00f890140d0380c0490035141c16030b40c1070011000008814042d180c140018890714a040c0c5011070345903414034085554a10710345201c8481299040080e505000b4103010441194001a031014224490011034001d0652078030040c086004010250b00821001c0b20303a03000103003880d0441c0381400006081480d1164955031582c1e84002006594a88140f140030745030303404c0b01c0103210403005010840d00c001469130596038100c0c0d0004058490264000d0104180040090364007540126800207580940c40b0314100740c00800c1c480b001c2e1201501d03200510101589040702007480d0b42306032442d450300b90b84842140c09000081c621b001d030680b031550302403400c1c496130303581c034002400f0305401000a1107100e0300b140101420700203140d00200c00c3c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 863940170 1250 863938920 863938967
    0x2060703111009060e06131e080f0c0c150702090106050304051e010b131503030c0c0e0a1406040b0d021513150f051216050f0307080901051b0d0e070f0e0106 69
    0x90706168124100a0354444c01c002001d512704d060082401100c8501c07850030004651202d004100158070010000c040303507481c00081c040711011049108074000a9080503189006001c03980c05a801190082d201c3c400329a9001c07403440c1d034060321603018146d2030b400d40d4444070003810528080400c0109120541030801940b1010400300d9800c004900c00141848005003508050080c1d034500d910003868084007070a80d9190240904c002403080e10700e07610307440740804085501030038140b00f41064072201030400480030340f030b075001c02c0f4480b07115088030306e00580300300014440e2162006e00c900042007158821030500a00510107484000548040f10400100b44402006003119031101900515501d4401c3c0c000300c0442c1c012201c61098998080032024000305100d04141e100402520802e1080004c1160361104441062080440c0746003040401d000e2180380000c05150f442505000d00080c12980180d5a0703440380600110303964441911403400c4001000041e0300000b000c0c501000c0c84866102c6c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 863941420 1250 863940170 863940173
    0x13080f1602150a1e02151906210f02040b030d0e03060108030f03041e0c031103120a171008061603050708160509040603140d1b02060703111009060e0613 67
    0x100f034403006152445079804c10341101025000348089a4100b984881c003866924040c1c6c12103850741058a0403003e445d183c4140010038800708a03044d207100d01918041e034218222a100d1004130740034000d069a109944030a821065034081004a2009405c1e071a40100c8010386030416040c010168003001e000d8200f0025103500c640840100c0e1752156000c944000c0e101c0d101c0c04500910070140300020984004501c0100a01c0801040b11003104001c40490f00f0b0300c4060140001a80980b6001c1c80200d1b95804450403880303440c8410035849980c0000c041c1c100d5aa03006c00c503280060681d034040e000801d6081036200b01d54180144d41e8842c0960401401c5800c02c1c0c0321142c400c1101c14078003000c1004c041103900030341e83d840c2c100d8002503800c9000b08240d5000081440c6c2c07215210825a004146105204981043c40344200c111081d0020a4241004441c0d02d05503003806e030740030118902d405603520540d0320028512039690820302994002901c8176850b18007924009014200d0034081009800000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 863942670 1250 863941420 863941427
    0xf0806061e030901020d15090f0b01050301050f040b060a03091b03050309210f03180904020604030602090109090906020a0e180c16051b03010b01050c0613080f1602150a 74
    0x7405040314140403036580e039500c00e00500a00441d054000c4442c1050040100c2c901068444026940407000130010b442d00319800008903008400c50a02240090004100da85048299006111f40240c008030742c00c4d00b145d002815540c04400108042a61741031901c0c00e0207850b000e400c92004124203070038025400c42c0c44083e541d029510600b4840d00b02079205180c0055a07035000000b099485080310a5904856038240c0c072900708070f05000e064400680b8454035032618079140380c0559000f501d01890507095448550180d8040b2450300d0500550b00000580b6542e140b140c0440e0318000c0d100103880d0810850000c0c142c0409602462050808135031088a2000d24a0402c2e001a18010313425990072201032204400d20f40740740082c2880c001e00c80001c065040130440d03000050b80480082250b9000000152038038020011200e00d540e02640000b035518100802030b144180c0204203040c145044900c4028080c0e00218040b030060201000300000c60402d40905200903011500807400c06030b034400d00a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 863943920 1250 863942670 863942707
    0x4060e0d0302210714070e0709050d2010080405010614010509130605120304170102130b0a09090f02090a0509060d021504050409031e18060c0317070f080606 69
    0x41082c203d0a0145158880d00d6000c550003d82c3c40002c84801c1803c4180da1038589070140b0480c00306032054400110f0143c411298181521001000700306403410342d07141c001c1d80800403402d40d00c0a4008182c1755902d80c1d01c91008041000340c6e6580c2c00c241b0715191510b40e00392075032076002110514802d41ca02000345e07040026030380c00182c01d07203020555401414441c405055194042a040b40c2c2ca07040907a43c180d400b000820644035020079030080324030510031183c00c13446503c41901d03a802c8507000610400d0f540a0041c503440489103450b50b54143c48504007011200030300405150140c0c005007a84c0281030205404004140031240d541091034110080b6126a10742c4400071f1040042c0c0c6000e020b11000300040d20080c140107032040051111515010b80190b821a4507200d0902100c088003e100348102c05441100076144207620840c0e19000341a1048003c0c0c0000320180b200f180c0c170440d130304004036541c0e80c402d04860384c0e0990030030709080c4040c4c1503000c00b8014901409082000300c440001e000340c2c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 863945170 1250 863943920 863943943
    0x611150105040b191205061b040b03040510111801020a02011407030c050607020c010215010303090e07030209030d0203040f0914012112170601020d0e1c02090108010204060e0d0302 79
    0x4a0840a000f001500c800072a5403103030100310f118a00030030114019030314101482c0c0325100b12819030b01c403a00d85840032100c201e503128942c0420402401076013099070145412622030ba0840c1c01d6660000c1a00382a0b0350a10703440f2028a0000c120010180b403101c0700c1da0075011080c0080d101442c0c0c01d4000802552003400c015032041700000302d0004242c401c640180285400009855481c10102c07030094a0f004500c0e4000e005102c0c020301c042a10060340300c00c5040301e03815112004071a242024260b1040c600a089074141682071140314250b85041c4003508210549501035543d5178203002d0108448482070b08174000d000d140c212102c00c074801908370681503440b0034800081020340c0b044074010200a0381c000502007201941a000d0043d000301e000d030007002100805400982e02c180049944a034001807010028003c140b85140d2810b24000120340c0d08080c9050f000c8c5441d160b00468000031080c0d100310b21681d40050100046a840100e240c0c80d03d0b411250041d05002d1a10000c0d40e43d5103002c0c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 863946420 1250 863945170 863945179
    0xa0902090f01030e0c0402121626040303111303030306060c0f0204090804050619120c0c030309082a0f01020913050c070605010605070501050a05090d0c0515010f0611150105 76
    0x30400344d0300808104442c06968010070a65540144000c0b80f00d2402081d11840c404d8034400e140c0000643c003d0072005424440e1003455091114400811040814013400503805d050381c5544c020b41108401c0b000703018841a840c9882d00c2c5615501d0000c0c102c2e2543d520410820803214000400110070910040e040d0350101c40c003146015042c2441d56161003607a00040d0301180014003460482e4541140300803010007610340415071040c4a00a0041d24204601b00e000a03561120000c00a80294807011105010300c018078103103410388262100d041e04000c0403130b003080140c501c03000c06128200038254203003178020300030b6003814040c03c007040303020349040032080509848000240c1c115050205079052140c0215041c8000d50359060301600650004c8403d03560743d420400010110b000601445000f0a1030000504844120f00703001c07510076a041300b007119903002d5400301c80c030083e60708406107000e042000c5110025138600700300a00745260354090344425401400c558404050740b4900141160800d85 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 863947670 1250 863946420 863946431
    0x161a030c2215020a0305070b190e0c030f0a0f17090a03082203050c0411090d050609100c08071218060c1704020a03020409021305040308060a0902090f0103 68
    0x8500c950680a20a4a0803030514500d00000448101e00c1002089580405469100d540715030801c980700c003000e80000e004580104118000030b5038400320240e02920381900140c0c4404043d0f0f1800a0300c100c0d08078545a5030107080c0041c3c03217180500c5102e103502501c000906101e0f0740d40d951110680c03415500500b0880066144440c0c0540410440785608070085c6100401500c4e4548110141c000120350301106032114111528003c1520b001c600ba01d410000408660341110200005840c42c4400201c010f181440750b40c0c42911203c440b200f505106034007404079490b241840a1411116a00c56142241441001e80c8a160001c460f160132882d03d14000d454074100150a00240c0304d4039004030040070b0800c69180038031226a100c008608030940d00e400203400303a50750200c003100b03003501c000e5846030203e9401c000501d003541c41400d40d544083e050280c0303452494040c20848108690070b4001c50980410809a031921000310b00280400200450504012034081501807600c440c1203418156030b00d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 863948920 1250 863947670 863947681
    0x60609082d06160e3a0b041101110d170414030c0d081003050c040b041b0e09060a12030f030e030a0507020a050303040b0d11091302030405161a03 64
    0x10728524040c05800100c401a04207124520035034001c0d1420702e030010340d84d600c016101e032030300700901c041c8240c641820071a07940d4100b50244207420440000c0e091800c99450aa00042d51420a94070aa000d400c0c02d051086011b000540100c0700e903400c1c05041c0d00482000d106c00b039003100301c1c40d8295420201c603113441e545a18008203001910b4a101e0380038440881c02a0241c0700001e000226074141d40d07200c0c80b4030344680c00465455500c502009046420102d8020b0041c00c1640c44400801d200810104604a11f403003280301c205500c80c030003400900e0800200d22141414114607422030410750380205030901d40003812031441e410390001002c20840540240e400c0384260010700084406200307480d030310b180481018010340d101020032409081d08060004141c5004000e403800c4841d006c0c1c61501c0c0c016020362150043c0310ba074802a000c3c407004e00c454180d41e207400c400c800089105805c0103135a41071a040c01d515068074401d081505a100410910007052070269102400c2d079003000580d143c1c0c848 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 863950170 1250 863948920 863948983
    0xb0103020d0504080d0b1522030210050406080f041e0203160f2d12080409050c030403030b0406080318040b031209100503090c01050f0c0a140106060908 67
    0x292980c240c2442d05100c02d0005000d443c40c018040010022400c00c5803088100600050480001400c82d0143c42404a82405e10030b211703e18050410417a1380089050301d80d80011410215100403800040001c0b40600c151604626655044459403d801d1a546802d070303a131940000c1107082c4100202040c010010840d02c040107803901d5101c4540040385507a440e001031882e1203413688520300e545446501c0460320360502c0d078070181c00341043c0d0008010881c00c004840c40e840c6a03080d01101c2c103410800c0002640100d503c12507008603030341b00b0038966038105814001c059501c6403210034440d910349242000101e400104445205080401c02d042100d00710000a00500c40741020382d415000303480e200c180ca5076982000b00311070082181e11a480707030602102110b090100305c07184c00441d44500004109503000300302425826424036801841c03d001c2d1128941014000c031001c42c1c905551000e40c120b01c000c01c0c0100009010f10b40f42c041505132400c0707001640d40720401c0d84808041501031282c80c10488 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 863951420 1250 863950170 863950177
    0x816080d0f020309010c050c19021f03060f0b0c1b0a08031204030810120b190f09110d0206030406020304020301020f1216080705030619051c020306010603020a080a0b010302 76
    0x165010810504070503914010196204456445842d443c001ca149021406a02550b00b900c000c40c0040409044480c10694090081078003aa070140c407190310390070421814800440030158650700810030341c0c82c005031103000c2511030308156458102401140c0081100040003040420803003c408102104100030840510b050b412690003404000740140391181d50201c100d0203180f280d5511a03171a80d50545c041251100390141901e00c2081e125448007040c5003100f40c80d08805a80d14043c0f00d401c1504420b030403100b180190020103511040070b0b03000e011006450b1540e044040ea001101403105500007105031000620042c421a800300c081801c2d92400d42c1130340e503d00e10030b1170303465a40c14004031080c030f00110840e2159001c4c1c41340141008500d00c0b03804414061b4680b51070b01800c5445030010410341d8020350704001c0c4600c1d01d8a0002441d5074910006040103991807070301d03404480c1c09006050900c2016001035090600400c00700c201290711014a9520100c1041d001655224000c0128003a10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 863952670 1250 863951420 863951437
    0x1110312071e020f1005010f15020102090d0f030206061905090415110409050105060f040909060b03330108062202210105060f09071107170706021009081608 69
    0x88030000038001c020b8000641c00c0c00403042c6400c44008840d48503d21081da0802d01400300041103410041140040c0719209d01c160000e1400003504040000307011a02d140171080c400d81e202c1101349005014960144105a00f20000752440b80070803403010300c0c0c0790030b4081c28480ca90040002c40c0c0001c0500114031780c2800e060103c4481801105d60200c0200d0b000d0b000381c02400503051500c80000303240c1c640700c400c40d502c04131003070403050a00703103041c403110000c0c00d1000080c1d5045403035411084a69a060110b1074628040881d298130800754000b02c005511111005c04c40803802e010010300c000000010710540c4a01c2d0b220314400744041e03906110006000c2410300a400074640e105000740710a1185d00101500e261308001c00003581c1e02c000f0032000c924410801341d0090b240301c1c0821401c6200f001e1441102c1c110101f00d0f100301d591100381c682d400010314601485501300309424400c00741c1c14841809016071501050203000c805841d0301c2d44910510ba04031600c030002c9040b01c0200100241030350a00c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 863953920 1250 863952670 863952707
    0xe0d0e22090302030910020a0b010504050a0212010f06030b09092112100501030e0105040308061912080d0c0c12201c0801120309150311070501060806060111031207 72
    0x1001c0754070300a03560ba04200c00840c403402240301e0000c2940c3c80050340691a54220403802c401c1d900c0d15003800b0003000b0291000c1d01140e003c0040c1c8a201070244982c0b4000c1c00740d207a0703956200c0d1404400604807210040c001d4070800300b0314140039034250001a0214010f02e42c0d20743c1801100c0190601c40c1d240301350580144140b6800e42007080c5107440700650b200312402a2010300010500c0e40815007250781c102c400401042000000c503100c0e080c0038803030310b041c05c403928002c04840340c50300301c1c031004521090350855055400040d480340c0f0754100d004680d02101507003171800b038003040c55a9400355214009504001c01815010032110f41b8180c0c5400b11034a5181c070240c0d142410311303010740010700f01204260408144c00400015507021100705c00d0f00780940642c0c07200030203810704001103506103400c540c52003015210140c108a0005000081040c89c3c8124000100070385443e06050400f100203041505001c1c14100308011050044101c038095003882200d00f85640d2822425501c002c05204d03600e500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 863955170 1250 863953920 863953931
    0xe060f03160816121a10050307081b060301050d030c02030304030b0f0417090f0f04150e011404050c2512170c04031110031107150e0d0e22 61
    0x1d4000b04071010300e1038031440303c6001e031030302c0310200020102d50203c01000d803070b182071400c000c9940708804150044003100080d00c0c01c55580b00000e03d0440d06400103402600300d8840403648110802c017190305280282c8415003150300d4000040e6405a521401406110100985c40c0465409000701c5001d564040b0500301075081202221100c40000c940480e540007403000c00c0c400050301c06003991400704004101e02182190b42080c41490b440880071203070045e48034850040800007482c2403001500c030707100740302c04e0039890701811098078101032042500445c80c0c00240a9410003601c21a54038900c20601000c54007c081c140403146011a080a0145184400d226100d203500c10521504600360a0700352400380c443e007809050701d12035480024640c00b130094050159007403044001c100d2a030313513080020300100b2004a07210716510840c000c90364151344d0488440748040c0c61041ca50059000c0f0020440c1c2141d00d1030107469000300001091080c075407140ba41028400c26031080f6425030070309100340b04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 863956420 1250 863955170 863955179
    0x15090d060204080c01020f071403010e0d03020c0d03021201060309050c030d020606040f0515011115070509100c0c0306020f0f0f040f1203210f020c060f060a0e060f0316 74
    0x9400c0b6010749035881c02030098241c41588005902d21885801002801e80280b40403040c900d4a48150402c41d09552074048a4544001c1031000d032140090300d48000d680c491144460318142103c2c80001e074241031042c000c01081c080002111415030b00305040018204580e410098980000509a50b500d07204801d0300700340640e0701044d080e009141c1500c06204202d00c2050420946404841204028443c0d852901666100e081a240c0c4203528209485c0b03000b0603441c0c03e03049010304480081c041070001441c201641402c490b104000b00003803502441c904003d545070b0010300982e2202901c056000300e40c042488032800c0480d11118013508070240c1d40c100c0c0c14408161900240309507032540001d06000640380c101210340090040d40b513901c01020089211041800311002d070604400c4a50b9544020041011403000740140b84044009280e0f514000048030903001000b040c060091443d40020008a11100707400f6030030880481d503000800034030f10003203840c1250a800300c0d9590100f40d20f0005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 863957670 1250 863956420 863956433
    0x5070306031b0f080a020102030708070f0b2a0306012304090903090512010b03120d1401080f01110408030a032301030b0406050105150306040911031f0f0c05030615090d 74
    0x142120f0200c00580c8100e681c410b0095214085168060b01580003005107400007400b0f0802086c08500c80c5661034a01e083e5900c40e28802c40c07084504000d04035004950010b243d0301d48020f2060580d8500410f403442c074016000802d40c2d1000e0b03030004241c040b4008100342c2001020190382c00f13042c500c10200850f4407182801040b040c40741c03207201c0c040c1000000070301d00d04006008210390b40402500809200b107480f819441c3c00d5104d8050310203099601e4540ca61820406088680201020030003003404105140e01c484c2190308000d0446500c4100300300070007030b200000c01a036103220300c2401d0005003188411601c80d04601d1412584a422342c04500103c10030910041041c0901d00500c010070840ea00e81040c48050500703809494041710090000400c240b03840c1c3c0000a1040c030446030310001d00060004a450004910079100c2d0121450780040716030b11a520480c460210320010a201c0d4640b90700001d006803101401650042a2200c034405001c2249411104000030191140c00c1c496034908060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 863958920 1250 863957670 863957723
    0x405060904021b101a18090a201c02010905090a0204082a1009050103090312060807031203180f050c1f0f0905090103031413030f02010f0c02090a05070c0602180907180501030507030603 81
    0x451060020102b0641c0d0801d04c070511650342c0780d041c0c44407410b090501d81085100600184180c40254013004085448003042c44018102070015001000440e64185079140e102104c440107402601c41c1c0380320b441030b02d0340b00c80701000f140c8003030a000928034118103088410b00e2030228107000d150f08112002407004000a101c4046a0052862071944881c40500710107482401c0132800d80f00488403400808111002e41e0f00c061948540100c482ca40e94130004904502205c0340503900c1102c03200040d21000740c1007500915420031525200c80c0b840e09180c0026012a41800050304108800d8000000e40d010001101c065038030382d40c48140e00954925041011a5082c002240065088040c00340c01c40c4c05598a0b621180c0d009200382c460b0b50358840154001e020040c0305408001d513124148001c1000351000380445280103041051148000c1e092000b0b001014003260104070603910b0b103203403080c01ca5100c0810b898091030041850b4852042c01c0300986010b8001400304e203a0003111044480079450706 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 863960170 1250 863958920 863958983
    0x90b120123042c120405040c0c0203060a0914010e120a09050307080714060301120b0a0b0a14031507171306110a030f020c030405060904021b101a18090a 67
    0x40851001480100f607200c2d600c0c042151102041444184001d207003a422160700000503140000d250341080c0c000a1403d0300a030749181c0e00954030340c1c928050040c0240d090202c140d0b04c80c024411000c03140c410f03e0766070004000c0d0103001c0c0d10110790384400d5072140003130f2401000010103da26064841c0001078a4200c540b055010185540010031400e04011080d40e04070350074030494450400c4113459528000c54024880c400300c0740e941158002c0c50342d030100860054604d048034a030158040c0b40501d0b00c1d00010414400c5003190a008100c40a1f60184c03c15042002c04e02418085498410800000180b0b403400240400d007000f550601d030b80120000790124410540d000d100d4406084025800ca11a8202e284225002000b0a124034100700c0c0c010490f0001c00f400051800c1c0308807014140d2000c0c1e4800390407003500071103076554006466010340342004a548041d14a119114800240303020101003008568441c0000010003628050109a0071150000001700380c041002d4450b42207003030601c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 863961420 1250 863960170 863960231
    0x81605040504030e04020c10110c1b0906130905012a0c03080a0b150412051e07050108090102120f06030d08010b0306300303010303090b12012304 64
    0x100094500c0c0c1406003a006039016221588580c100c40b05010180d840032850101c41d1040c803c80d8098134520340b20380c5039025001010181c603a0012900c1600f0200c0390b2244451000310f201c1c4018141e62100200f43e00982c007115485000f8403082150b6011b0070104002900b607528080394416a03080800f0380d20300d98010391010300007004a03041c059079075105612000c0c00003515a000220003440562100b064000020003030b05a0300315520107502182c0c0141c00140640001c40003090810104005285164140c6200d00d80100586803080b656000f06101d40303410440c114010450400007981212004900b000790180b06160915485500d12016103030507001c2c1c442e51000d003c0700c500c1160300d01c1c184d80400da4001c1c41e64403032104000c82303000c1c2e200050814800111940d151400800030200025034494040c684a61450401605012032a445030000183c20858202403801d10000c1c607040d52314102040d0b4200512106482c200900f1060381034101d0310301441c980402540c4907010746000b21408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 863962670 1250 863961420 863961463
    0xe010b0318150c0c0109020909010e2b03150506070609170a1d030708061501180602151009020a0806031c0906110a06020a0c030e0319060b030f01020408 67
    0x141007035550300901c080c808801c0c80e000007040205094800512181c0c41420001c5581011600015022902074902650b240e540c2d03144c0c00c0c225a130902041807144c03810300382c051003c10100001215500460200001c255640d03000b0600101c40340002c0020300340280007140c403030380c0625050b401801000700035030b80980000d66800f025003450044961113520765542524020390510011000c1ca0207200040d80343c01a00008a0084020082daa1242c18807a900d2a00301c00c10f80d0015090054800900c0485407014805100c01900025070408120780110384041e5071b0707145000710319034800c160880c0710b00900001e01a545140d1000030305004103000c07401d8403541d100d580f150345080d06401400d01c1c0481c20056081007041c0c002c02480100c0c1d0156401e48030184034a07603406040340d0140503424007140345002840181070780000c130346010310301c03e8004142c03590100510441844401070014486034880c9032400310354406100c1c030361000e50504000e40d1030399101d1008030b84409000d00b44600800510703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 863963920 1250 863962670 863962711
    0x309010f050114060f1b0d020a06050708011211010e040c030f1512080a030f02032412120a030e060106090e22030e0103090210090501020d02071406070c0e010b03 71
    0x6031003418104400600315803070040031980362085d40e0006d4100b000408142d405c107002c112002c0c4100840e20312654064450041c0e1841c1020803100060010b608003c2608014816a000951582080341c0c1150200013001d109600480f0204a26100703640c0250800301079105030340c1c2540183c070421051981c140406000700500d104a03105500c514036401e0740c5500740d5000b00300c0b030000620080307609140225207540c501d00711f01c080ea801503c1004005501c8424460f80504104141c000c082d4211560400030056590b0a03580d18140d4083c426040700000c0c203008124000e03484807080d4880e80042d80c5980d0703542c88018148140d1032240540160142000881c0f15803151501100304203680c18a10641d1450740342210a090031225041c1030540c0e03414854056030f152003040e44038885580e561090b803810140024240000841104159400300e0030500525225292000c043c50094480c0b6071106032609015600c0d40d403a5010303001c900840c500209002462000640c450303180850b8103000c50300c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 863965170 1250 863963920 863963939
    0x30305040f0927081209071505070b041209081002030108010c0c17031302040e0604021905010c0206130b030f060f062b0b0a1d07032703050f0309010f0501 68
    0x1c2d114111030a41580c0e0900b03e461008910080c0d46800384021a04008806044200c0041d080c3d90540c1e0640c065142040f0000c03252220990440b003d250503030509815640c1c100441e0005040102000c80600718003184074880d0f241e0b50010540c102c1182c7e0200c5810340107400960081c06802515401e0010f540350302c9000b44002e42106d50702603910004900d40032082c441942014007041d146107818082c28003d41e41d03901403807001c040640007902c602e05242c03040240070300982d6075049091a0000c01089140c0e00620903001041d01a5089503850f28164000c403610b80d4181c0000040e0038000c801c0c44505010300c0c8030184601015034040e401720440c60b0400c02c45000d6120170160010368600c8000c000203050445408020000c107000c80c10580840024000d03c141e41c2050703098540000c2041d249404030f81d003c0d038005040c0c2c1420055094109104008446820480e150307075400c6103256810540300310103d4203c2c03651001619101d007021710009018003018040090340718100b0340045456400f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 863966420 1250 863965170 863965181
    0x2d020a0b03070f1d130227031203090f0f060108070e041e0c0308370c140f070308070b070806030d03090203031e07051009080a120e07030305040f09 65
    0x66407034540740e01207000d40482d50f44480e2502e004180c034401c541312205455400404050800c2c100016844000d645150454440c0d03591140103c96114040518141c801003103c09960441c0712802c1c1e643e507a1001d103145001102d0002c1c1c8504d214400100c070001c60041221030684a218094554255403640c0070011850251030107410540b00510a12191442c0c00c0030742031b034a120f6880e00209a50f00d8560f0340b41038101c45441400d051021801d0009550488000d40c03a407284248400e60740340c06040024240b10a00000400307014410030b580d00110010410a41d10440e014225803c894480c60100440d8100b010304680c1a00302802144401d40902155440303110040c00425030b00105110480c0940108030042ea01800108510a81c400c40c001241601d403d03102416540c5600314a046c82c58810030310802d1001d07510303100301280003804480031250307000345505d80382e202070f041c100c8000e0003440042007200310b074407580800104054010010308203c409050189010396a55071421040d0b65 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 863967670 1250 863966420 863966431
    0xe040209070f1715040609090b04170706020c0106031202010e0d0f2003130506030103150f0b030102030412030507020114010e0403030e060405011b050702010503040b042d020a0b03 79
    0x4840c0c800a09040d20400c0050708001052904480412101400c1d0000c802c0c2501c80d450006503591a038061030178139000740d60003003d0307800040088070100d491310181501c014100500b81240d03044006102c81403081a5149035070040d004564403c03455400d24000c10780ca1204491006250105001c070318010b10850344988898070180c01d4500c000304046480b032170300c0b400003810701000b054030b020004071a103008003030030729030100443c0e880380d10010020a14030b4076070040303220344010401070000825010881801401740c14000c10300c60602c000700707809045c0e000c04850305584040304220a200b06600d030403003100115103007000390780c4031058100d09941d030104610034816003e000400c420700c201014241e0007070281c58000340c0210315695050624000340d900b41c40a0707464101c0032100c001d684140c070402c904036042c118500b207a81d40c0081c0140c00f00a00240480b902240064144000f10503603c15226841c01085031400b031810700d503400c4400d2003100341d0088000309008120040000c049a0146 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 863968920 1250 863967670 863967679
    0x3070323092407062c0712061803080a050609070e06090406030609080a09080d081f050a0b070b010909020913030e031f200904020d020412080301030b010e0402 70
    0x6698100340041001090403950b0040041100ca86540801e07102500965124480200c0c40f408480781e200c2440300c01e6180d00008818114810700b55080010f400f0b030071a080700200300500a441d0801d80010a13044091285480114030081b04160340300c003280c0d1042e4a2800c0401603510f5a00c240301805004460900100d41d001600f0300192410b4070103485602801000454590b03200da40725801e0700c80d090f904640890307021450340882d130340100c0004040c11040d0300500000302d00410003800340b000540f06d8103005081c040c2c41070402c54804480c101903d0094000014280c3e1501108e00300e500810041d509480c3c072400120701000769000d401e405c1078000700780f4503582d114440b8424049950360021000d03c00885000c032070544007400b482da55425401c150220781007590309200c007070b24001c40c4104040c0c1604070030703880e1a01102c400da030064202514016158804e0600f0b0b0002446203800030115000159502170401030840001d5060781d220b21010181c590ba21901d001950718242c9000303520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 863970170 1250 863968920 863968927
    0xc0201020709090828021b0d080c012414090f0a0506030a05070e04020a050315013f03110d05090607020109051309141f020d02190203070323 62
    0x216454200d004072500450300149010038000360100c1418030101c00002c41a40d88250509090301800312131915011001d4050907c031005000514400d511032005081d880041801c3d184113400754802410b1203240c0051031000d201d080e1058030071b00320350301c591515120000803414441c10104005802100454403a280d0390311400e01c580c018181c020511030701031144036449070200c0c400300a04001090503040010007401d00f40184020286141c20043c083da000c04844041c40c184881c0c281e045421070500b1200544e005000d480640754403048100d0660344000f01c20040d45407c850109001e842600c40252544000d4450764659407041c1a42c0c010030010f00c80d41110381020002440a544140b419140d004c0d1100000396a02040281454055036110919800c01c9010099158811200d01c01402200d42e4103c10b08440700749130701d10181843d0040390640309542150140c8482582c0161010030b40748264200a40e40e40100200f034000900301200c0044c405442094141d800003002502d618 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 863971420 1250 863970170 863970179
    0xf010e060a020711280e0103031d011808030409060602160b0a090b03190b011409013e060f060d0f020d1e020a0504270302070e0a06150c02010207 64
    0x3d40100805480e100401200d0400716503880f0003001c1301c0813080200424004144100e0900b0041503000301c0030103041d800041c0082074000851082c1029501e01e03400c4640c1c40c100048894205035180c0302194030303907a0804502240040050025505450401c11466130780f42c0080b0390b030b09440d03c510000204842000d114002a003001002c0c0680b00e81800f6000b1070341c07020041030550040b502c0421690710195541c040c0c05042c020b00b0303031030302092130159030315103107441d60300c00b6446440300103410b218007001d20010003400f98a07888030b02034a001c00c00340f45820354407107030309100020502c2001070b0103050b000400c0b00c4060110300340511405042c0c010b04125641e00c10b04407500885080e03a009a10b42070a900040001d00c0a00300d4101c86809103601c0100c80c8180010341e451500010f1103036042501c4026900405900042d94441c018241d40214001d810143d040420b503030007541001032104104100212680c204404407440000300c444c40c0b41c80050211100e01c0a210020700503040002c0802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 863972670 1250 863971420 863971441
    0xe0106030b18071505030a0b010c020a05060c150103062c03070803041a07020313091a0d0f05060c0a1d0a0b031f0312080609090709020304060b090709080f010e06 71
    0x400400d62800f10340d03282d62034901420110201c1d0a4810005800204020507020240100480c1140a08141e030b041089503000804081d0503000360313801b40c4408104440001410407203240c01c01080c0d50b10044650310781c00c6c6030000d824119040520140c00c802054024102c540c4902080d11451000d14185007081da81d41030b15600c00740003aa0303603450840700382c51045114041a405070f0308035001107949683ca0102040721608a600000d40d05103402c1400c5807030301008400380360504085802c2c40b4a54041e14002c860780504c41c00c060410b1181e81c04000418900c08001d102d02d907050307122442c2822a039a0040440103103144d100740c2180c180c5c1c1d8108a00c0e04000040c54000b5845a0098034a0403030822030b1074204040c0d0b1041e0b40400501c1d0403a08800c0e004540760350031041c20384140d006482c2003080d450b640d080e00c1c400c0e411015400000582400702c103a100c0c441e40c040061900f81282400c200007400541c440c0116890703405180c00d0b82d502075405206150020000c11f0140c001ca946811006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 863973920 1250 863972670 863972701
    0x260d1b2703124a0a05060a0201140c040302030105060d080a0f14130f0b04031e030e0411031503010b0a03020f0604033002030a051207180b04030302010e0106030b 71
    0x2005109501c800540000e0586840c580302c00044003900441c50203543d619550101c0280e9035455840103402003e1481d01da40400c9020b4a100303495142e40c421400382e00703d00500543d10501590703803d520600c0a2625120028000c8074000c40003030050b51101340410400b01c80f00c51005003601c0c0100095100c2a0080401020007055800d150050146000c3c0704207032903000f134001c548603a03c0b04505122019079820808054484c1c240b00394285400d41c0e850a04c020100540443d00541e000d015604040c401c0c01c03071180d0200f0142c014090009034503441060b54100307844003030f801c41c1442d501130b0341c5044c14407810345120801040115090b19540a01c084002d0700e504040e0010420840030000c2107600e4112540f00030700c030962500c00500e11300310704650158008c0d103038210f42040003903441c916400702c15900d00400d1410208040d80f07038040282c50f07050914101c1c44c407c5644110004440009c000501304a0b802034000b40b1823080c00c10703c16401ca41e6107000c010048007249011501203225800c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 863975170 1250 863973920 863973953
    0x3020f040f06090221040210080c27180c160206040e0c130b0304080415030b0a0603020c1e03030412110f0615040504260d1b2703 57
    0xe60001d030200e030000340d9100c0d0b04405003280d000503941e52440c5070218210042d262407044080e05040c02da00240a0307501d07070900c45040040080c045401d0000190848900c441100d041d1440d102c088404800606040681148504031b20740600d0070007600c04083d948601c1144802d03600c0c1461071084c0028854080781d060760842024440890322400c045401030203080e42d90709036078a034214030481140d500781542003966800c0c814414040010700d000c040d503094030312816401e2014000604100d008004003040503a0088810100041c1d050300760780208541c0d0090815101c0c00c0301c5003081c1c40d91185000c400400d45234820800100803580c0740740120390074820b034600b0101c0c006103061814a0801c0c50160701e11107800c05000d00000242c1224007400914040e5001d01003854a62610790a8816a002103100c046505282016040e02501150700d610030481c0204003080b4240780c1c024007415030b050b064022a02c512680031005040310103002060244505074020300b41980c0e6041c1031080395098 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 863976420 1250 863975170 863975179
    0x20a060606052d07050a0605092112060d020d150b121c1403010305030306090745230616060c03020d020a030b090f06030a0b06130608030a1404060903020f 68
    0x41d2100185c020300103130490900400c1c010840303080191886090040310a00603541f00000040b403048280e010042c2e48444444101628042d0751b50804a0901140d00000035400788003080032900b04001c06010415611305d641d01002100c01038018005801e54079980c50b24103074462046c4a0010007015503100c000c05a901c0c01c645904004103280383c1036002a002115680c1000c0308002c03050a12580391540300c08503107040014512220071607401641d840c0800754504002a10003029503034113510722990b810b164402400426a504481c0032842c0f82c181520701d480245001c00c50051a140b019164200e03042810203142c0c41b015694880240407000e111405c1c140c00f0302900c40d142c8200c1c406840d450786152404241040306030304005400c14001d000b10000240f0009009503520002005801560310035030445051704c0c2c0c2c400264100c182c0c0c85600200303030300f030110203d003d01001c00645442942d0b9100c100c140c8206250061560042d4050300c0001401c203c1c0400151030b10201c250700c001000342 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 863977670 1250 863976420 863976427
    0x80f0c1207050a03030f030b01020619022a010902030606032b030b03010606050c012a03091a040c0f0f030b0c031801050a05070e15090d030915020a060606052d 70
    0x14085260f0b449070b03910076030104410301d0003039070a240c150048071550a0700344054080e620344007040038000390414003084500d0341e01251000a40f205071001c188000e401d6184040342410000310300c0e001e0b108019040380a070081030302244103400d0014400c100e214006940201c0080011079000810b84403074141410161030740b03941042c6480a02c20f08000c2d203040d5071a10b91700c242c0b41d21881d00f03480e00748185020b113440b030070f00c100c0c042c00c0700c460500c2d8040030a190124034100c00d42044100d0104402011340b0184e10b25040c803080085e28407501c000c841038150400b140c2551120900d51802041c030002e081c562120001664140243d4010340c0d000c08840c00416101c8042d000740c50840f0000c0350711a0b00d880d91101030069940d0040e10a82c8106011148060000210400d030000760044c1007800d406186410714a0b401c01d800380c1c00c04006081010118403c0103c0c480c0001d40c3c500010006036066464040301141c0d5521500071503e501030001e400c142c00c04403040002ea500742c100b10140403980070a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 863978920 1250 863977670 863977679
    0xa0c180608120c16090903030513020d06020313080c0d030605011110150806090705120708100b0d050a05030405090f0108060601350912030f0f151018080f0c1207 71
    0x203804c07800644524140001c0d924042e18018045410123400742d000f07840c007401441c005a407401d107456140b03035001c8400760b02d9496074050440007020b5080e00801080010401d030008450000e1441400300550740c00f0b000d465a80d400543d5a444040c0000b466a0844118041d00d11269040705108554468010b1400340d5242c0d151803d00005441d02d140c0da80201e44100114980603c6040610f144040a07100c103616220038a552815120074045a091b1544c00f400b00c0e1b540c0f07018840b00c1298100c400c2e0f0301c6810700351500d81d40360350003401581d07c204a00e0300455260000c00c002141a10984002002d19486010041d140301031140090340301a40000c012220200901c4441c00d035805814030f582000b401c00d440402d040090750660180c0c00d400900410480f41c0e0344001c640d401c081d4081c02d001d1141c4408581003a48000640090f412071420070070800c074a50b202c41c100c0211401c400c00c5c4004543ca0f0260b06481e040d04000461095005048a40d401c0c030340f41d800c2340c0d0401b40102c11a40c180303540b03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 863980170 1250 863978920 863978953
    0x60e0a06020a120606050408031206130c08011505041202060d1b03200705061b22060806030706020c100203040f030c0810050f07050d0902030a0c180608120c 69
    0x10b1007150010354002403503403401d1518054600508158186035052a040181c2c5542d240500000b62040c20306900c041a9035440c0c2100d110201c8440900030f208884000038060421a800c2c49131401c45009100440c28070b038450701c1036805480c426454414161000e4003000165003200c640034a81e180c1d22180c901400d102844104c181c0c60341030b100484c81c5181030b0400c03603800b9032418500038680e400300320301c0001802c0808c0766503100c5086280380d0055100a290761540d40a641d0391501c0d445640044c83d072050440550500886800c0d0ba44c1a10030b6a4403000c0c0340d00c8001034440c070005680449280e004619003503010070007100483c4110780c2040d5640d006013080480b25803050751078061085042c840c21909015510000c0701da04802c1c011802c1c40c0c413070041385050045c01c078010000f002c0340c2c0c4880080b4941000e8113094005003180e801c0480b40c1000c0c00c10391000e103e01429540554110140c44056000d00c404030384a14029001c40c0c02c10301d484d000d10380c1c03000c0400c4451303005012034411010034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 863981420 1250 863980170 863980177
    0xa0c031b141e0a020d0512040f0e06041b1b0213050406050c160b04142a0301060602101d061e070e1021091a0606030105010c060e0a0602 60
    0xc940c91511418010141402c16000b21400200d46592040404255200148142d00654107075111222030b022801c0a604014a08104c0c040040000900144900341054140d050f00c4102d0540700c01d80d00c130300080000b107400540c200841d6540b07501c0d4140090780a2903610104e441000b640c0c1882c43d00b640e00043d542d00c1d000400882681c0c1e944180002e0024500c6917962103010380c04064506003044840e04062000c42a000301150410000034041004410031101c1c4510007400710f4400a8400301d0100f125140c1c01c4040980200c401655101031030140182c40403a420b42d0013a00c02c81d21035548906c040d02d00d407100700341e2015031619071022030340341040510b1288001c5c8100302024400d641c4955800c48001d040c220400c203040105904580d9000090b124440e581e08211801004900c0510380304071181c0400d55440b490110342d01c003488802488161070100030310350540c8640d100000c00050b40000c0c001d007400900c100c4040e00005059500c080c1d821344040c01110388100c415543c1d00161b90 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 863982670 1250 863981420 863981423
    0x90602060f07051b16120b13030e04060e04050c0324060f0d0318090c0906030c02100507051c0e1207083f010315090c0b0301090608070b09060a0c031b 66
    0x207000708008540d000c010103072500a040c2c0f10390810b545280ca9203400851200c003800103054411082d070008c0070580070313407241841100040c0c0140092980c840054a145000711001e480f01d004040e402006480d001c0f032445c03501044d40e0b841c1f00481d8480180401100e038001c1034950000d15080c2890035a6a8100b0091211341c843c0e59001d404041d002c0e0902c03002013255022400850400c454035045a80016442c02075402500d0b001800c2c0010403012441c0480742c040100a842c900420311201a40c060003c108003007201d5800300c1e40000c5402580101c2c0c425841c1c81c180ca81040407044880700140000300030701806000310a00304811030740400100030300142c01c0b840741010300e2480380021140c031030b504510742c082c50343d400301c075600d5519205901d00c07204824400e030542d80c1c0c441c04104404511000049c00311405126100d6031034100340e03001005a4001d155081c4504100080e25a0300c81003119025040074216a007400e00106060f201c00303064500031802d000103001e50340001c0143c0f07902c41742440d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 863983920 1250 863982670 863982673
    0x1506092a040305160807031716020a0f0611060f040f150507030209040b0324090717030a090f08031e0c03070f020a080706050912030405090711010c090602060f07051b 73
    0x103480c0c04d01c2d00c58500d12035a1120302190408041007020130040500d03600d5402c08020380705c5d40c0d6400000315102511403060020b40c4694082000316070014810140c4080e288180c6030102110443c60079165515811165680c41e00c2d5180e00140019011944560f5281e100b40710513211500191010801e032032049030343c040042d80c0421040c403203150601035284a6501503026100700755415035484483d45400d22905d013003202a80200380443d6040008130300400c4004000405034602e041a292680e1222a580b40000c0c602d8001080c00c102030450300c01220982030080d440c1c0351141d00300301d0042d0340d00f0002e0600102c00384044041580117000400c4002e01c03170b5101c026040c8007441000840748440d0403401c40c60307200c03207030520003281c1140c02c840000b40c044661003045101c09905628510603504002d41003a520b905004a1640061030000c070000450000d009880100e6011503583e0154803450300144c0c401804645007608490009402c880c007858150f02c0c183c10316400c032669105158100005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 863985170 1250 863983920 863983933
    0x1110f0604051e060601080601210501091d150c04030c03050a0611041802070501151e14090610020f0d0513080609030f0c07050a0b07051506092a040305 67
    0xc0182c28001c030b440b00c0d071051255101c00080300030366560740c00009050030b0512103a8004640b003603000e40314031a8050080185509642807034201030002d00350a104005000f400c285c10454008207210b8600400341200f001020000301c0d28204010310240542480c0c0c010070104404800b00302000844800b0b0360140340100320000c880d03d000c030100d0300b618840002d80c0500f44001d000b00074100c01c1448202030648009a01c0c1c0209040c030a0043ca801c3c42c0c501140d8030301041c006403844a10808582a281c01318110380b04554810f810300c210141044c481380c0c8200240c0008901c0c0c0351221601c40305258510450310341244d841b002e24600b40c10007401ca800700c0c00104150002d6020020355201a00c50440500014202100d0140c1c0da0b0017500c902c41c5a800c8081009010000d042004a0003080000c1c10a200e9650f182562406540b003950140c4580c0651190400a440c44449690144d90090000c9903250765031419082c41120302c0c00d01081c10041c00301c19030300d2711010002500c0618000c0001d8800c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 863986420 1250 863985170 863985173
    0x5090a0615030b031c021222060507030c1e0f03020616021b220c0504060e06030f0f07050702030307081b0f1c09080a060b0a0906050a05040b01110f0604 67
    0x1654580000c1108260903c02042402d40700494100c0308801c8100c0310100001942c0c005a0504507544041f002c0980041002129044801072405813a00300502c50700f20b49440e401c0845080c800e001c0f000d0041181c6680d044d00103901d031400e41c0245500b04800105010f200e940d000170704141e4180550050380710f40d041c8900545010120b00c00c0d010f0034002030075242000d40c00d290004011000301442410045503003015030201d080c0b001d00c10341d03a683e03003088040c4003d20007074501d4002e40100000150101c112410604101d811240140450203411800c0d03503806e8048911326200401050030888148101001030314108082c080c6144200c450503100d00c0e048a16010411145034490b400303030311002a81400c400c000c2642c0011002550b002d030324a50146105603040e030116030202c07503140705500220341070010740e81c441d4004880c115016035100c0c2c0e4808224003600c6081c020b9130341c81618813004218503c0e0a41c001a00c901c07040c14060181d80065031081d05245030050b6107003203500403c0c00c010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 863987670 1250 863986420 863986439
    0x151217132309240d1115040e0a06050f131104030308060907020114041209120803180303090d030e0109140d2304211514090a02010807051305090a06 65
    0x9a22400d581071030103e090a01c8000c201e000e640e05401806401900e0a090901800b40d2a01e95070020142c140346039914040c402c800a0b40c0203100c1c14510036014804034030309480c1805100200d440007003050200003640410850107800030115120039035503406a580041074000081c100960203516820303164074005003031000c0310303c0c000c1095085900d003049078892001300710441500143c00240320301410103106c4044c0d600446c55003101c52100c0801402000300a1400002c61059840080b0046038155170400b0503a40c0c04159105842070f00000e80c100d8a441c465400946911001d200100ba0009030b074541c11080c10210401c0c2d07007240c101c0c144200d240d0341c0200c8484c1c0d080011f0007000c0d9000c2144c0e0088045d5004034020381011000d841c500e414600102c800b1801c43c150001d240202813000140030100a00101d8000641110800001101d8600118071604455010f848495082d40d4a0300121005d60000705940c506c03019418010680d070303c0b0421560310900c0d85c1040003810074146034546 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 863988920 1250 863987670 863987689
    0x6010306170106170304030804031e0b01150e0d0503031b09040c020a050d210c02031902010e0d020708030f0f0c03130905010b180f010e060d1512171323 67
    0x2112545c003c00c02000065100c004403022a600908421801d0035000c2c0c201001141c607241c040d000380d40100000c5104080c407902e8403016001a107034080c1c04040c1e607003401142c0c400003101030910703002032000603040710300e0480c0c50f22400342060480746461011070000f4119210152410700581c480544841000070412a005c1900054107002c1c40c46000140c40c20083d5030803d421002c590b448205900300e4900030019210020042401d04a142c3c0700000b000b4000c00328002c1d2066544201e1240a59050000c140130f001c0d9825003018620b018a80311188071a0341c0324174050940d800040295001c4540d051000e4030030452982c120140e22032822401c4816100180c010310b0458a00708041c07140310301d0b03e00002c0c80b00c030426650407218017640001601c1e02120071030304903084000001c11410910240d408201800101d42c401c0e00381b6034854a4009040c3d00003d4010904d0300c090000180140485000e058490b1b08507031000ba2007900c3e83c00144042c00400030301010320844402e404403d103440c2c1d001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 863990170 1250 863988920 863988959
    0x5090606090f100603020a0c06450605040302070f0618061b0b101805270a110f12060709050f010207060309060b03190611180906010306170106 63
    0x1002d840e42071541034078542c030401d80308010a142c2e0000c0d00300b0180780145514a00650440c0d42048540050111070381c0c1c003080c0018070305889940c00500014103e0307038080ba0a032007101c11910031100c4010780d0781200034803003c0e0054065210b032490000f8044190748400d400f40409695901c03030401c101c50304001000c6290410020b001c140d204020001d40c0c003040841c015500459161041e4603500400c0e4041c1d190b50b00078a10f850501030b4162103400803504414040e0203196484005155112070304401d45c0200000541503400c050034110103d0040410701c503030841c00902000c0702410010014100700030380b08200201e50081801c109a25802502160082600707841e042c4082005800003034032440c090282e038043c903946004101c1400003692001c0c01c0c03c00d0281c2282c510300c207004d00a0800000f48441100c5060a00ba1b16071010840c110588210381040c0c1c813070b00d11440d007001c00c110240c04010f040504156541c030000a14513034801540d00e02c40c100b0780c00001c21904000c0d0142050241c1c402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 863991420 1250 863990170 863990191
    0x1060303051617031501080906040c05060c030904050f011403070f060f020109020a0e0105030d1404060c1506060306080d05040b121f0b0d06050414010603020a0306090509060609 78
    0x404001003a00324040b1030380d00e02c5209100072400c0d0701e80780c24102d00341c1d044109651580c000c0301301303d1703085c3c01d000054000d10826260343d803280d40d481c1010395848004480040180030401e20070003039401c00c1005030603207851b003206981c20403181c0d402090454204890013014100340c000104403003003900320040c0c1c00d0982035002c0c0c810181130403c00d40d120b011031b100da401004440c80c00410954401c1d0b102843c0e040e401803030017001599840303284250034000c0c055607100f1700544642c07540590040a20301e000402c0b821510f400e01c0e1a00c1c9042c1da00203c411003c0d0b41454110411b021000180e20601025002e1a24000362440c2072040141ca41001d40c210341090080821050205201000683d496900509440110303070341e540c09003800d00b4403e000e0800f071842d00080041040b80d0040701601003416101810814140d4940400c0240c03200d51440340c004518030801440300da8480d400429811010b4117021500980e2140d024048030812900a2200d801142c240030035880c2503129250401340308072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 863992670 1250 863991420 863991431
    0xa091d1f180203060c0a020109050f0a0c05060a0c021302221815050f150304140d0c0f2d1a06040608120c0106170a0201030e19170403050316030e010201 67
    0x2d012a0b03a454018112410f0700078046148a0554070035003090b9a140e81c840241d9904041100285542e000030445c12191211030706000304450800c03100742c40d460030140d66480200303a21502800b40c42c261960201c2c1032580c0030080d40101c10504100305141036000307240260300078500b1b40c240f01807000d030000703207690103040000c0194400000355410041d10011106030802075240000584c405102804600d40d184003c8104801d014610400e0051044000150f801e0f00f104c00034211858980c1c0000100000360022a030b0010401d44034010100a2810041d5815498500c2807500c00b00d86c850000c41e1020350003e640d540c035111481002e500800e0039901804000c0c1402d607000d4403850252042010b205020034941200c0c1425003081c030041c1031038624454001d0340c0d80c46e901e80b55002824107a010a08041c06180b04200000d180200034103a2032011806803040c1c0d480950b025031800101c0c10719031060001002054051006085a5512a41ca000d842d034291070054000d040742801d5905591401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 863993920 1250 863992670 863992673
    0xa02040501120b060c0d09080705091608100302150418050105060403170d0c030b120a030207150e060307050307080108161a12180115050a091d1f18 65
    0x102e042d207540e582200000c1203c1c409603010854600558100726100c3c0b0030130340d000e8400758000ba0844295140c800036034101c0d0303480d40c0134171160711400d80740b44402c24000080010114458960a608130100007442e420840d503a40000b02024262802640c00350f0000408010880382d000d40c0f1040341c072a41405218541c941800240309000314840540350403e1241458560b001c40c1d412a0000022400100100303a10a030700107000742800074480d030240c5480081d11901800c0012030740311039585a402002140c0c1440b0313040309071403940c5a940040c004007016142c65661801c0165100312420707a50b0030f0322850001c2c0c00911020069003d43c125400c4043c0303008a001c0150506000c0d40d904040b20072000c40f00608940f03651048241b41d244002c110300c1031001f000d0100440010402c1244000d100c60040c402d002040c0424600c10142c0c0004503c0c0c0800c444007954101e1003580b10500000204250405001c40c280400036861052200560100b0b000102451080f00310000c024181c4510f00c1085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 863995170 1250 863993920 863993927
    0x1140f07021e0705010e010203040e040b10120507060e0613033806010305130f03030e0105100608190204081b0301060906080606040905100e011b08040201020a0f051005041101080a02040501 83
    0x31340038150400c850501e800b0b03104e9008104980c000c20701d16441c1c004502c1c0c00d0629211111060707441d43d118041545001500c80c0100154480c910b41250240c140799103040d10644035200030115098101d0340c184040f00c46061603043d0a001940139030140400066000c0c45044401030703044000608004044072941031030143c840e40381d440b90080c2800100d0391205c1c8010800510414801041d1034103200b180810035070705812012124407180000d2003191200e920074402c58445000d2540015440f60008500741c0001c80180e04451402000503d01a1580305040c1003405004410154019110381d2000c18107003482201d00a10300210100030940c204490349444d000041c000b68401e0713031219601c505203c01445400c41d20b480c400001c128801030106c4080c040d14104c00a0f04004010000c10307864140588850f40c407403a4168080d042400b40c03580c81c00b004085801081d034051281c82010105503640740b1400d8002c6004a1030040d100003100700060070401d00a00c580809401800200310381c4c0d80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 863996420 1250 863995170 863995183
    0x306010b121005120a0302070501090b0901050304080f2d03070e0d021306060306090b121c030e1204030209090c100e040207080406030b0a0905070c1401140f07021e 72
    0xc01d44001110744446442e03041c2d1103090742060380e00801c041c98a58070200001060300440d8825000d1f00c81103503560700152101c54462003000540c280400141e030301588200021a0710602c030760130f19420411b03076601c4102c0e1a00301201484218072000c40813092401031004070801030700d240484600e07614103000c0042010f081c03254064010840255050210354422a00c0706030301c190034808002032076407450000c3c09044548501054680b4181c020303d1503003040c18201e090001c0307401c02003940ca540c451380c03c150280c050b40ca19040568989441d500903009200d41003034580550f40b96074480d4154010091452030142840702903520410340c0d00125260000110502c1030300b820b01054100010300070402174071402d000200302075400900400c0c1d254040c5d002d258401000c0c3c071040d501c0e644441c0e003101165000c2c0c9080022541c1c80b41ca40300007074440b41c080200302c65118000326070488001e020908516081c0e80743d8141d81180d00821084541c10000c515009a60014000565072403a01c42c3d0344441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 863997670 1250 863996420 863996437
    0xb01050915012a0b070503100503032701050c070909020117040209040227010b0711062104060f0f0b030d03090f0209150901140906180f06010905030f0f07050306010b 73
    0x10801d100c3c2c25648101540c1400e01e0903040765a018840c0b030148401072155108a078400010750701d503030000c40c0c0d0b070400000b5141958040390404884241d034500000413040300364507060401101300440d000707414042c001c62004040c42d200100300b10100c1d200240043c25403400385c11154a980082101682d00e140c1d040c0d41154054440d00350440880c401c0c03000c160405203034107034152407001c0005050542e90005198003070107109a13a50041500c1304000143c0f047c55080c140c2c0141c0040c403c101c01c0c00040c01c4681007441018000358040800307042205607002d50703241500312940c03a140341392141004d10003e1031003200b51408102e001c01c540d864000c0320883e150040c0c00b48141d40006101444298810800d4460040000d012580d4882000c50324030310740080c060180c821400801d005085c091900000c418840140f4800303030f590701d40075074449032008149a040068280b00001c468800b44140500900f00c3e602421003000201441c615004040c4c1c00707240242d03c8800104403032040e0070203440446 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 863998920 1250 863997670 863997707
    0xc03020c100f0b0a030b010e1612111315031a0a0306050405010b0a150201150f03030c020409080313060501050604062f0723040c02030d180c030b0105091501 69
    0x444044401a004043e10482e540d0070001603007012080c01034080180b070480e90780ca42e20480c00d07609c1140d400c205032140c101400100c1c001d00c0320300720b40d450190400d001d010700043d0381c941000d18100b031030110390f44150b008120041e0480c0300d1040f555418007132081c041104408099403030010401003480410b16200c0074202d580e0360f0020500304102034108501503031000300b00c841c900b0b807101d00340952030401c1a2080003540c82d00001e120201c0303808840c070f41221440300c10748203154515242a5052031241d0301c1240d100c0e45d07880c2d1940000c0c29600c00381d401505880c04072043d090292401b6000c4500c1030704004d10450081c030081080307991141d0310301e00100d0f8291b609070900c242c80c22805e00c02d481d0b001c19014240643d480100d102c070340d0001c560301a20300302d034901c0c03c0c0480703410140011038640d030b0960b80058004000481c00e19140e40c1001c1403244218401e007610b00110b0b181c40a400c82c4a0700210307152200303c0300420842c42d1148205401c040a000304035890703602100040c0001d41c68204500c030300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 864000170 1250 863998920 863998931
    0x1d180619050402040311011106040b010e07031415040c1e03110705030d02070201120513081b060a06090510210c27150f0b0c010902060417010c03020c10 67
    0x100c960924210000c000140080d5141d64480c0303400c00c81d210049000c580003414000d540d25901c1d0340081c5a9000b150420310b0401030340d091410a64020300c00178809018980c9450062242c0540003000318807410404041d410783c8411801003100351074130352200700c081100c25101c40341c3c05c00da40c1040824494560030300240c02c0446c0c040403a124058200b008e0094040850364802c03a41c04c0350024160107100341d0351025008440c00d4480308851056680d181c0500c2d070140381c000003c0e00300006200500d860217192083c5190301a08e50b01d85482260692070282d19000100441b901c1800340175044400c0c405a141c1c040d0408010448031051320110480000c2023101d03403c2849600061078000d050042110790800350f800e240c0a8a00c3c251015484005140c0740030115145080e000c0d80c0c058640d4541480c044030714000849000b60404000307180c0c203559685031100160b4401300200b0042c010404240b210031503400d0310740c1c00c61300720210110038940100000790980e200440d03029691340c00c00800140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 864001420 1250 864000170 864000199
    0xf0d0c0f1208043c0501170108030315040b0a0314010609020901051806040308030f040212010e1005150607050a050601140a0519030c09020c060a1a0d1707031d1806 72
    0x3441d5005010610a0b10000000b010070035044540b0081d00c200b84c0b03440c3c5241c48400080c5007e81024420204036400500124410005207440c40010000040000c284450004001415162254000c42e10210301c1544000d0900d0280640001418255000c5041001401c000f8100c3d1180c4804001d008042c80340c00f01c000c0e0795500079a00550342008034503480345020012030042020551f0140d204146048050514000c14061400c0005e0003101030302610010710002000b9100141846010780407001e407210040d00d96202418041d4082c2c1c004042904850803c2d504201f41a04900c1d02c140c582c00001949403100d900820072564103584466009114642000d1031700c00c55040201602840c01c00098500d00f0394001c1c10740c0e00000e000b924120740b01e42d006001140c02c101100c01c500f00000c80fa00f00e6a2412800541e00c00d406200d00c00310340746142000c8031099000c200c0c00c5002c50b46421401055108001440500410603110381042c0865000da8070080c1a00810452117441c0e06181c400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 864002670 1250 864001420 864001469
    0x30506010e0a110301060504090e0d020d050f0415020d0f030b030d050703032c070506040f030f0c09050403021c02060609010b0306011211031e160c020f0d0c0f120804 73
    0x50f0602d061981058880d6150b8100030116441407107641c0c0c207242840b01d141300224003c01c01c035200c4801600141050740d041d5a09a410750481e400202c003500b41404000341440d4042040d041803402a4017070020030040881c0600342c0074140c492001018a0180024440d44001840c0b41340302c03409080c8151151103501e001c03000b516900d1002104c0358001408554003199841c0348c1c07120007400400303464480b07483d00c041c4452800345205075542c1c0e07440e0302c0080011484045451a000e4002c4044c484007a480300c03280420740744141c40071801644600001c0790144501c0c00d072007010031540d1024005500b8000002140c0190600030f91544200003c08030300c07182c2c018a000d82c0c01003c006070070b0240d111a000c05400c684c00c100d40d107402880040345500c40c0001d04003150f5200c0c107240070392506c804403042c40c100c80a1847c480200d0308001445802000360780d0307882103c0645071003080310740d115500f40a41810f040e0300913441100c5109001e421040007030407000036101560020348440c40c40c44001507021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 864003920 1250 864002670 864002681
    0xc02040902180a05150105030105130207050a080309120403150c3005010909020d0602070804180b010e01110a1103030702042a090f03060b0a05041a01020105090601030506010e0a 78
    0xa511540e0800b040302c0240b103449000e0321624500314100043e50b10251038000e4001102075503070006070f00704010b114503e0710080300050b03005862001403c1c008680c0d104c0e4070b0484c0d5110152040070022040080c002000c1011f8010b210241c0452030500d460746d40d41c0b48102d0f211001c40304e05e4584940e4409800342c8941c0c00498840b001806017040b144e80100980c1c040c0410300001050b80d410b10001244542007405081c00440e4060304a40c81c1c0d00440c0c54010003900144805c40310003c0030031000894045100078040d00c0b0110060005488041e54005010583c1c20403402c1e0500900345400c0b41229000704965125136084402040c07103203020b00002e422b41c410900001c0d405890700d90302c907100400b4851074030b00360300c0680c18964074040050f401f42e403c400c0c10703c00c5200103d9044002c3c0000391484c0c00504040d00080c282c0c0d800c03c0d49490004007600c02a194103002c4154841100b4095030b42409060741007231010024184030b5040d5200c01e52100c10501400f0980c3c040d80020919000076a4080c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 864005170 1250 864003920 864003923
    0x1404081803010f020c010509010c0203030f0c0c16061b0c05040b031212040b132001021e0c0f011701090b01261015170a0f0608011d0304080d0c020409 66
    0x2088000355542480c402500001790300320fa81d620b4070000800c45041480303105000300c002d4004500703581d2560840010040020060035282e5000e01c1441ca031101c04000d4501d0b40304200302c8109a842c2032280c010080c0c1c0c0000f07443c0c002281000c4901e401f1500d4400d1100554030140da010544411341c0002ca0714011003032056001c22080061408034130300d4a916018091441361540d0503a80c1c0301c0759258204011246805026249052035904c000c2c51004000103015506006444484c0c44040341001038024144801d0200d42201da800b411510f0840c0c264030032039009090840c101c03554019900b440c1c3c201400341000c900d90f6a0f14000d8103078040c4041c0301d00160811542c81e60004040101013000c50103450800050381000000b04030710b15000c00300c245a6540d5940c1c481c000e80800d503000c0c040304014102451702982d5610346060f485580c040c02014140303070400842c0001c4410510340c468a403000d6981e00b160010300050040150210781c00002000920345090076600d035000240c0201a501b40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 864006420 1250 864005170 864005173
    0xe032802030c03070c0807051509210d030c020d030606050f0d18050705040606080601020a0b06060d09081207030c1e1707080604052a1e0f071103011404081803 70
    0x400c44e0800000640c510152514501901d001c10782d01c0007445611034601841c648100c1007801070b2106828214070768024440c040030307552500480803010508062081280c000001d0b100da400141c0c140e01041000d44450355450204022481d111004000380105039032401c20081c00101c0c031007400c0c995001465a203c23030004100b0b0704a0540b03849079482103030b849101d00840c185140091614001c0c0d09452092006801803e41c0f070041d030340da0081c0c0c03160050003213501c01818400080c50b16010b1007000c1c00940b182000b103641c1c012055082803e00802400d90040600b81910b4038111a80b200b05d85071242000070040480d0503040d401a51494400c494605403c036503039040001c81a4000700590040400b642c0c2040503484261002c03a1500e03004080140e007106802c101c0980d40c3e140c500a0071007605016a09144810801d02c40d903082c1d014048048640d4000300b808803d0240d0540c450b184807008600811480700c0d100542525214010b0010300060004903152030a6002c0c2034000c550080000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 864007670 1250 864006420 864006427
    0x4030818090c13060e061801020a060e01020714061e0c0d090303060303231e0f1612050424020a0609200d11210708060a0e032802030c03 60
    0x40380702e580e4100ca154183d00c69003100000800343d0140d200065000c101409681c41d00e802d02e0350b1408407100000b1940e0440c8100206100483d20398450303080c1c604500070015030b40300380b0790828444c3da0581c0ea44042c0250007030014441e510408550901d5030850519a22080340d40d280d004900030300460780010000ca0402d20148101a030580c032460039a4800d84904d000c490444480e0300c040c00da0611103502814080180305140d100d13103004140703100030300900d051529400c102100380541090818500b142cad0288070382400c000040d03045505003011458034908040c94040c01c2500c11401c3c040b04005d0079401e040d01d403031040c8280310807807009800036400e210180c0da41c5050200d40000c3c0003002c501c500303070307403060b62413841c010000036189500702d104000b1002c50f01c3c081080c0a88409641040814800300786c4a4410341809664000e00440015003014602402c1c002c00340c408060740383d440c3e608208561550083c241d1500490300723101d0030409d5050800380000364035600c0ba4200124040c440407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 864008920 1250 864007670 864007681
    0xc080303040b010b0306180901020409150503010509030c060109050442060b04141f030e060a0606210225020a0602070501020a15110a020102031f06050403081809 71
    0x55014a10500b40140d090781e07181c44442c0c1030302055070840e50105182810114a5801e003070030030741291100780010301d0700da07444000e082110814402a5003540792420100950300d8203100c0c00d5405141072018619000c070144096440315014002d0b000c0c0785580d50081410301100c480c107528035080c01040c0b11400c560005452030a002e4032040c8181040251003400b40199090280c05c04072020020303118205418484507100c0213551440c82e40c0c114940b200010707842559200c249101c24143e0320000b82001240c40740a06000004281540c401c1c1007101c108041a800700d0146151080038103800c01c01c1e001d015001c0080d00c211148140e0808401112400ca61910500b8043c61031007250040304460703962009a89600c054414640903820003681031002c50074800d07101d03180c1490752400284038803004140b4140d60300455100c50050394044100417081c0f41c21003c20745401c501e07140310201e85107803c42c000d02d13500c29800010f210400200d405000c00140854048000900070000310706d61600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 864010170 1250 864008920 864008923
    0xa230c030a0605150a031130010504140f040609061a030708060f07110106030803010e010512060f0a110d1d0601301b0608090f06060319030c0c08 64
    0x2070364451680c6282601c00201403500e85032102e590510701d00c100d030600313000c81029001007031082810000c0c3d407020000030062442e8412484814072a003060304101498420f603040b03001205800030350040d4980002c1d0703100354050080c01c40c0d1102c03160b9990b040607030303d525000b4050595071500030440c07030400380c408111102c0d4060410a0042c164100c07080140c4c0c440c881640c900c0d09840c402a25000000070501071403190b40d2800e50303071711024008244141e49a94903451940700b6072116170100c82050060109240440f14140c591529000800c0303281000043d10508802c05003004a205a0361082d0040c142545000c2c1c5030701d007031041001c00030341c40c055500901c20340c0f150200c1d00483c044c1d200080f81c085050b0704000983c0d0f0310380710450709030608039598075a2082080019202d4840aa4652a05444920940014103800d07900c000c0603050461400f858903d6004454005402000402c00e4644000032034248008a25070514400d40c1141015505001c480e18017070300755404d052000c10002030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 864011420 1250 864010170 864010177
    0x7140907200309180613091a07020d03180b01140a050a08031206010c050c100507060e0a0203010b0103090b0c07300806090108060f0a0e1f0e03030705030a230c 70
    0xc15070b181c1c001660f145800c02d8041000b01e500c2036201010100700320001b40d41b40e101406030381c031494a10b0400211141c90103031006044400703800507400202e4600348030341e16000d0400580c0111104a001c02c010355601c446011701400f42c11040038171260032003416540d40002d03d0040c01d01804000c01c1a0f01c9030900b50300d903840311407042ca10300403001c0807540070b5105100300403155800c0000f40044c116000104070115001c00300d81800c011042c0240d00c04a644e5224403150306400a005110800c2c0520605003510761034081141072600d8103416070086035400683d90b5012003c0042503039541041e203004103488101c0140c600741580c80c0e01d0b06c0351103282e0140c6e400361000303107035121000340350340d21010800c1c052024003562400380c01c03400108580d81903021096402c01450300c00800e205901c200030303a1400c0405880c050042c0c2d42c220b5285c40d94945881084c038001200d4001c3c6195162011024007c3d11000c2c003a40b003500e03582c1e40f46002c003000700c0364003cac69001820800d01040c241142d05a21640 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 864012670 1250 864011420 864011437
    0x91509011e05042003070e090a02040606030b130c1403040c082509020f0d151e30020112090c0f0e070914130e12041502071409072003 59
    0x3840f20100222002d0080700714a80c20f1300038010440c243c14290b80c20990794015007181c0d2284903d1001c40d00683c2c0d64016080600310640c1c00040780d03814101008503a030011001c680c0180d240c20429042642d00030360402079903044030010341d07490702c90b03145c404040b29851740111024068170441e50075501030084051544142402c082c18002d032140c0c1024203d100b102521f840b405c1003007041406c0341d00300d50403140c1d02c505054070803100659160070700c12164216181105103004600811710120740a07581c440500f000d810245862201881c071882414032041c20045e052040c10300d9290721052a1f60440b1440c0380e4008405201207a1710810314002e900103010b00b511400460340000c100e42c0c0306052004c201d91044140c0c5828800314814400000c280b06071044106444841c400c81c40d000400c8230800c41c8403000002d683d120302c2c00000d981680400e440748411034020040c10042c6000040030382c034450000302c84440e210303191181e003520b50140c03101910f10449403090520541c00c0000c0042c0c0002c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 864013920 1250 864012670 864012683
    0x20c0304180b0a1a0d0608100e0307120c02060706020f0306010f0804150b120615090603120a0525030e0907020a150f0b18040c0b03091509011e0504 65
    0x200398070005068030200303841a900308040d10020040c0c1544103c28180e24480508080e1914103042d60000c252000b03130b00604c41980c04258141d8144815220307000900c80180003440c00c0c1a110340e00c14803810348113000241080400201d1600750f68920045825155104004558584031039400034401d4100f120343d9404a000408190559801103480500c15540200802881c9401f82141402807074503610302a0070014102c1010604d0a0400160380074000351486852030200c01d6080260190000705602c0c000c0c0c011001c0040328200000640e542d280c5541401078450f000f0a84500ca0740c1a12141c498900240c503904005050304080020748481c800c0c0d031500710303035640d1190a0f40d0b00c00f4010700083c42000c1150305510180405d610451075517040c0100810011410400206500443c01201c11000d03c0103080c0400c100105007854020001280b60f02d0541c81c10400d0383e03884038035001e6045030403000040090404e04080d80a8200d00d0113801e51a20941c04817445000206021282202c0c030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 864015170 1250 864013920 864013949
    0x21c060302010215010602030a0f02071d060a14060f03060f0d0b18120403300527010507060c20030a1103030912070f0f0809040c0e010503060f13020c0304 68
    0x20080011300081c10713551507400940c501107054008881a040800005045024072580800c0e602c1c2c0d050041e220b022100300130381d200e40c240041001024000c6030b2041840c0008160007006548130b44090f280031300c43c01c110b426141d07a0f400700420001ca111a114507800f00e051111581000151040d02d80114500380a00d258060740703c42c8160b4074144a000d101c0f031900140000c100091380d03d040760b03408030b8100e403014440c006482001500501e40a40da50301040001c0b07541403000c0c0e040103c500c0106c1c2d80030080c0e22030f41a02c60000c2e016201c0c56501804994403501d2807079451b800303038034100b2130f114240803805001c1206a03406501c9070483c244110006101c88c80800c0c5000e000400e81e40552082c4c005410300c100301a5008045e58000d41044409406040c4c1641c0030036224498000014000c036401680c40e08900f00300070803202c4c030240c40b500384010610191090b036480b4040e213a2121003a64800652508000000c07042414200c0207142c81d4000946011103c1020026004541c21507580c043c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 864016420 1250 864015170 864015193
    0xf090c110109240213141206010501080417070212010b030705090609060103050403180303210c0c02090717090703021002030705030304111f08010302031605030604021003021c0603020102 82
    0xb6a419a82c014002241e60301001200d0300d5205034a500f2594941c00041c0b80c800d10394500b41882e000b90303001d00c1c0304c1442c0e03103405505c50525103100404e0f850f03821f002d05210340c1000d0000c1c02c400701c003600c0980b0080c1018581a0b40c0304569040b2000c0a1300100340e007103103d03140710b40c0078003915100c00c151f8028081e4070380c005264144408550f00804000709421400e80e07d0100450061100130b00580030410301203018804c00c003003516042e000d540260340b8200b00200f103980f9440850040d0a94000103480c000d4550040b9a0001c40d44209640c12928001d00342c4851a04440b02c4a40202030b401d120f0f0b005042c040c04034000100581124825911020704690305407041e610390280540244c071540007040010300203003c0242140740c4881c020802c42c5010310307144c100e45080c18140800c60100c2c401c1c4d001070066140402c4a14016030000710000b1b82c490814010a0706c550019000900a515000d0b11801803800790301501c264008640b54080c1c0160303802c4171003005c0e111503c02a07025009501c4110b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 864017670 1250 864016420 864016423
    0x3061b0f0f18040e301e070b1021141002120108010207080a0e0411030a02030405060a02030919081e1b030a0912051e0c1e030c090a060f090c11 63
    0x201000303045a20a840e40030702d05c002c44c4a011100c1134040003001c03c1101c44200b14106081c600c3c0d178030a000c1c0840e00c4d01040d00e4000000f400140200c00c0305001d1907020001414045d00301400145035040244d100c40703032450000c40c5c0300e0742d605899031540035295907030010181d00e5002d00241010700300c070400142d82c0ca407916802c074840d2102c007802c810000c0200d01c481138015140d06450030009003001440c1248042034100315003080e105a0754145d0000140002d1140801c00f99400c03070072201d4218079504002c8903003942c408144070110041100c40b541b04042c41190700680c0d10480010010944d01004150300d43c4090784401c1c1c113907822004210b030b80d50181c01c5c004291640719206896010707480341441001111000d007000c08031901e2240510001c0194500055a038040200d1001026400048020403000704d50541002c0310490203c02c3c01a03207681d0000f0b071309460301e030240c17a182c1850302d130f241c00b440103051541c1009080c070310f8a0100242d2010b0651010200c20000e50317420300010429102039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 864018920 1250 864017670 864017683
    0x90a090902030c22050f070e12030409110c01090309081203150d0203030d0f06170f070b0c19082a0721060e07050f03061b0f0f18040e 59
    0x294041d802003030512040d00309030b1021070050000b80d01026510f4000a02c0a05071791040f94100740e003024030360500003001e0f041034072040007000865040059090382c42c9581c0d0f40b0f005d10b00c101c210407601c030b202c0b01005c00f01d1401220000000c0720003d00a0446605020301012168031883c0f00e60b1040c42002c40744000da90068030300415030420f102c0d82980c041d50401140155801007603905000800c00c004141300640b288003a4401e02400102d0098600780052075100c0703150380c40e8010740e0403440003036104038004180310099600003c030441e2074040c90040316240504a6000e45041d840000f003200c180400500540105601c2d42e10040700021454007002c003080313500c6d101904940c00301d40144403800103444104011000100942d8030200c1c10f0302c65600b0380f8112245ca220035001480103002d1402d009031002440c801c02d900a01d1141002e030920b5159a11401010281c010040750484000c00303181c0c00c6602031b030040398109482e04041c0c1000403814030b0f04031600d8400c2d481c01041d003000800c0407442 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 864020170 1250 864018920 864018923
    0x8070203030601050f1903090215070f1401180b01231804031413090608030708030f04030210060e060102071703090105092403040506070302120105060c0a080a0203090a0909 76
    0x103181591610001954035405c440c4400c02003070700a000304840809003842821000c243c95401051610107030040c0301a0054480108424101c200a00000b08004854900700740c0c0d4001c0e00b4180e006c405070750003401020305004080b400350700707203480c04148140289614182d03051410015800d1001d04072030800f429060601c107410064841e40f00c000840d50907240c542c0306000e410000807901004d042c0c1000c0741e100c410070418103007141e101400b580007548510000380a00c3c00085107058a03e0319075650703e000040441c010102004002420544240f000d05003101c0c0d858000e000c2c1a844114181d01c000007180c1c5940180f01e00c00c1e0024903101044101d49144a148001e076150181d0507004450700d40c00010010742004035450300d41d001989070b01c2090600e02441d4035468032400c2c40e1420504140010f8211010140140400c0007d01008070000d03044a404558140c0d039121200b60781410100840c3c0b001d402418042030b01c03000d403900440203011940088401403982c0e510b44081c141141c3c0300020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 864021420 1250 864020170 864020173
    0x1e08031f0302011b0311030f0703020105091b061804050c0d050906040312020d1e0e06280e01140906060a0b1314031c03020901030516120c0e0306180607080702 70
    0x9034861350301e2030805402e000c1d406850509540034100304034600d990321000c40c409111500007613100501d80e0a1060750341007100b180c0501840107000b001030054090101c1c02611030800050845044802c10441c00c2e81c0312400342051055150052044906070864040d00090604040009250180210303046108a07816100c1207402c25072802a44002d41141420100481d0b40c1c40e0000790062521003400032800f14500301040c03440c401c2c48980c1c24920b01404000c5410b060142000c06100000400c01406000410001c1c0c2d111113045011302400e0180e81c844030040350b040500c6480b106c0823910611074001642e81030f140755515281c40b001445082d1942e003c0d8107481d2028803a8400100584602080082c2100c0510000c141d9003010b02d5501a06c49010a43c00070300c0001950301800b40d194041c20032000030000540750b4070b000d8181c40c0e8004150520315904c0a00054035801000000c2100e00045c0480b2210300d0031b20038441f4450024610100944204800980300342c4c480c8130401c0c41101c084d070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 864022670 1250 864021420 864021437
    0x3102100207090c080a14040201080a020c210a0e0d08040918060203090d091401020a1b05031605030c10020a0f170c030418050123010212190908011a06071e08031f030201 74
    0xc0d1030900030b410005000030540200c1d114041c0302080351080e603200d0003050010353f680b5410508050000340e80f44410781d0154440e141400c0201d58501d00340c4040b43d0180c030000c12039001c1c1441d0305009204c2103c5c000c1c030241c400310078854902c50005d41c4000a4206c1d403240d05115844e180710415001700704280b0340c0142d11030600e80c4001813600b14881c80c44800e112502c802c09448000081c208030038041e600705000115401000586410081c4022180041c1c0710904600222000207465120060024088102d07030b401c0c05040280c01090400742e0343c07454501c04d41320b050004c034444d141d031320521840c00c2c0c0411807038060502e40018880d180c1280da001503801550a043d18442c200c5030300e1600c0386410350141e400c19840b0b1145140042c100f005014440c0c2442e500d0100011b42054401d0308012030076032400000402100d5445180074103010115026610380c0c50320318144407207002900314441c01c2c0040403041c00411a28001031740c0075200000040d140201c003581300550b104c201c1d110281c00544e409 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 864023920 1250 864022670 864022681
    0x40c170709122315070f0f050415112505040614010c051c0903021f02120903011e06060801091103010b090607021005033102100207090c080a1404020108 67
    0xa1010341d0008208858003080c03d1006a40300341801c0d007101c03889010780090010402d101b68003059014242d00306080082d00c40750614001407042c041c500414455202600c100c1e100b66018803d05c41c0e01c1d05c1400105c40702c0e40c40c01d00c105807104484885e940c09002c00302d1004116890079009072070540340003841e151010f0054000445d10549030b003200399003c3c0222840d0981565500c900055805141e480e142d80a03403540c8144580383c03c07100c140d50f8600d0b1018008007400395001c11100b107803003040781c0c85907200c1c10040e0001c0d0050401b98038004808100b01d0303a442d03800402c0c2d0072600403104541c40c1d0055036030340ca103240400e0354107a40344084551801c000500030700c91103a0140103e800d018102a06061007035000c0380070804415809070204101008202c0520030f0304540448030070206014144d0381c0408061000000f060510007071140da900140000210b200304013036402071007000c02c00c1c42050406013024288107410b80d1240c80103410281c0c1d041e1190304c0807a0843c0190703030682d12070f200b0b13a0f00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 864025170 1250 864023920 864023933
    0x702060715061e0603090c05091f081c0914100912050c100509030c280e190606050702090402044109070e0c09040c17070912 55
    0x80c0c040700e00e4190101c01c030804903200d201d600082c0c052016080f5206031444025001e8000c0c070b62000341010300f4042d060b000549007440e18012110280c51081080e03e80c1c420340c1e00d0b1524400342d001e4610f40c44240001c0e0589000520301d9506d10302200361104400d81c0803007260102000d008020303c0c4a500d40c5404414240481c2c0b0000d00e540381d01c0c0803c0c000e030f10307441d0b682d4003c100c6110030f580d640c2c00b01ca921036242c0b52080d40221464403d00301a4540115940803c0e190310041c0c18040c840c0e17080508030460842d80c1c000c91104183c6045840c00e0403515403010785644501603900912000304042c07104581c500c00c0c8140700c290351268a580e0304240907982000b0000c07000500032a00182c0301c1010241c840401c0b16003001c0309103880d00c00104000c0103411900c0c000350340340d00b852080d0908002e1000741a000300b0030800703994a0040360180b541d2140166180340c03203079040e6607821500e0402c40e0800e85611141d04a480203942d0b0005845807a010300031601c400c2c4038020320220060900c21603000965 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 864026420 1250 864025170 864025177
    0x302130e040506070e0307031406190203060a1202041113030b10061725050406080f010f030b090123061809070b0c0a02040207060617030c150421030c0e030102040506070206 76
    0x401411240400c0d200d640781011103c080d02719412a0f88950107000c3c0f640401c40440c0400264502c0460075440c1110003d1070350400381c8500287e668180404034190f48450b0000842503200503401c0d40d403a007201652050301d007000e11068860b4a051804074940f010030300c2c60b84080740c41c5a46c035005d030100761010b050348151014107200502074a03200c1b03444401c0402c8035403840580840d00c800c2c2d1950700d058406071100320b0060003c80115034100c01803110b40900740301e0300280da0b00504040119a51748010600514000c803029030300b460880f13845080c89590042d03192050780c3c00c1d034654a5101e0703a15545101080b056410200503004400300f030089444a40c00313843c10300008811154402516000315049034010f01d000d0300c8041d1910024001e20b0300102141c0900700710540110714080e0100c010507221100d40041c145000e030702c40d010805104042c000507800445240f02c444000091345c0c03002d0003c0c807600c81d10002141c08103074600f180e0318061094408852020303081030300e8402c040e030070440d2950 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 864027670 1250 864026420 864026447
    0x30c09011214460605060903100b060c070e060f01031a0105090a03080d0b01020111070305070f080f030a05040203160807030b0c13080d0e0f010e2e0302130e04050607 73
    0x282c21143c1ca103c20744104001000381c100058008410081080054040d40c0b11904101e00450b800c01c00307420303140c40c0010000c02070f40d13402400150111143c00012018801c94598500500c101d100200d00300481800242c0100c90440c0c0703143c0b2182a0708010341c00d50b00100b241c0c803c100c4000500041d81d5000e440203148800c4001c1c2014007198032603030380c82120307045104d00203101d40d82c0744103c403600d50702485201a008100401c01d030801c040d0f6a0020500c1c803401c1c4000b042c039040000103000f04000a4245d030242e07610003100319120f14068070000001c3c04120360503440b1303208400000c090480c42541840c00e699225014004c40ca065884251602c4005480b1582e11842001030201240c21000a03402900060006d851018030707148004006040e081a058400d405e190f9400440c1e80c1c0240c000d981c10311084e201444c1411001d0205070b2411290b4011404104036401d003540c5240e4582c0c0200303950b0b0591440d01e00b0464485501c0341c0118030481b8010704d542d0101d40841c044e140291007211546 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 864028776 1106 864027670 864027721
    0x120e040216152703120504052b020c0618040903020a0308010b04060807110c090a090b16020c0118051504060e090c0d09030e06030c09011214 62
    0x500026a003e1546a26a041c1010140502610b040d51985104200300c2c61400f800c2c0640c8441e5440449004401030a654040d0150901403111030b144d100d078020445c81500c0000d0180a43c4504412a0b1580300400700707c4150b0b9450003101c0030349220f03a003e0482c1d9a11868040e02e00c01040c5c011400c4a41c040c041441160752000e1520391001082c9400d0b04842c000800322802c207595203407401d030007908032000c120304507105402c02e800c070620400c484001360b9035140214040f50489540800140c00c0301080c8003266126206c880c02c5e40f100c0c1303181200204c0e5102d0004000042c420f11920a03260041030070001d440c0c010030340d2040c60300c01392030484052400d0a9002264400c014016808a58800c0541c09061103080b580039040301c050103141d80e030308202d07031707003a640fa00401c074102c1c00261800c5a00000b00100d0244802c5c1c261207004007995030f00c03400e070300030b49411500c05142c450 = true := by decide +kernel

theorem cover : BRFrame.Cov 863848920 864028776 := by
  have h0 := BRFrame.cov_init 863848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 863848920 ≤ n) (h2 : n < 864028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
