-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1987
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:31.652334+00:00
-- url     : https://prove2.me/submissions/de27c9fc-1c25-477e-852b-09ffb023fe2f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 357194244 ≤ n < 357374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 357195494 1250 357194244 357194251
    0xf07051b090906010803090105091c0602071709010f05070318080303010f1205100c020703050102030c0a0807020307020a090b0a05030a050f2b08040c03080310060207080109050c04050a06030507030812 88
    0xc0183c40700354507104040c0c0c1e980c464100598103203c40403031315038000d0b07031804440703203280b0381c6840c0d01e000250b26490300350001c1d40240021900b10300d0b82041e071000500c640c8144c03a50f90300180c540480713003100b21030151a81d80103210214200007651441c1e20f2070034801001d0b8402400102c0080d500c2e5418008480c81a0f022a00b002e02d14080b9038003100082078000961400c2e02000440004019041c07a40490801d101c41e08007070940e40c0004140012049480002c0400d01081c0e5070741e150360748510704220f0701e1b4441d0035000b039400790081a060040f4041030b0700c11148440e006290031951580c0f5804241442400c520a071050b4010055490f02c00030240079500d0841700c03240c00c02c0c00c114501c01d07540352040f000c05a041c04200d14400014200010112004003558018124507140e03e80380c645e4245041e124005d60b0014050f25000245191050150009a03903100025012804100062200070720009240401072600e41c1400800b0a5007445050040c40c010041d0750ba03910956078000c5e001c01e5014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 357196744 1250 357195494 357195511
    0x20f0f16060b101707170702060105010216080a1101020f0109030e0405060108090a08070312050f06120106081225050d140a0e0402070629010909200f07051b09 70
    0x18000d02c1c055a04c28064100c030080c0d81201c0c07009444455040341c01c0c0400c1c44400401800020600102c40d03000680c00d8102c0750309a084400700c0c50b0328059800d00c101544141d0081c1d1380801d403403000040314866898280c0300184116885140031616441c251403a24005401140f90440301403001d003414003803e540030200382000040c074101f1051042c0d480c5004440903000d801d0101d104c0d020184a581d1003440310386081c0d0184141d0514014240500ca81034582620942000305041c2031500180184401c6a034480302814208141030710144140d07000c802c464002c8a0025240b400281588540034801400351009050311642e41c54040c220403107001c01c1c4089001c00344101d05030254044000194443d06903405a183d4540d8035086000d0f2801842d03144200908030071207403080300c1c04421150586026aa1a00d0076627980316650100e400d001502c3e68ad400002114480d5404000c004103003007402d8401181c54240305483d260705003c09104481c003200c0038441860100e180c40c261494001408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 357197994 1250 357196744 357196759
    0xe0610061202091c1a04081206012c1201020c06071803050c0d03030b04060602010c030f021303241a0a23010809030c190614040b01030204020f0f16060b 67
    0x3520014000c0c3e0600030000c55190020b400860403c12050320301c0c8800c05e03111180a54600b05880c003158103403c25030a20405c03806200c0040d04542c4503030381c4400e02d85081843d0840040000f2440318580802c1c4903801d400016540f032806d03a000e4248000c0140c04608000307020300d800c211000402c030b40700e001174000e80407006100c284007103200803411034801c4d4401c0322113101503101403a066001d041084c000c0b030340c410701d003500000b01c80703406400888000800740e4082189141c81c8404401f00e009800301c00a6100031400c3c28000128031800302440c0c02260a50200e00000880d980703000d88210b881d41e6482c0c001901d004943ca418400070311400340a40201d0340001c0e82480703841d000044000200c0c40c0c1000040740101c0c00000c414030459041c00300c0c600645107d000e08182e12944401710903011114a40b0f4402c241402d28240ea82e050700982e400045407a581c1d1960f000c220103074000c0d018140701ea5004201003240740028030024441c1036204d09001c0101c0f100c506100b000ca0b685401d01500840300e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 357199244 1250 357197994 357198007
    0x20118030206160306080a030e0a0614160305090306100e010f0803030a0c030608071d01080a020a090507120c0c1b0506090d051501060504080d030b060d09060e0610061202 75
    0x7004100c0c070703500072200d10320b03103440001c032072800c40240c44c072540407419070300500c4810000c1c11b03841210703840000c4040d160762052582c0d50f00700319514042441007040c100710600c01d16850354040403d5061142c004c0c9016030502802c0300000c1d080180584031310360721000d000000c0241c900700300820b60040091036120202075107440c0c0025100d20009003070341c2e80300c2d45c3c55204020085c025844080606100703012201420340303540c0502c130400e00003c00f580f8101194000050b00c1000050020760740342d80a407000700b285207090503180140c81c002c0c08070024400300034100368050140f44a565650301040c0d40798031502000342840950b0f0520300c64060360311009040c00f40314903110f5004642110900392121001020a41030043c2800c145084101996000d1000040d02a074480050802d40d5200b805480800c00850780690449800c842c1091f0081c05c00d01458840e01155400042000d004900220380f20074030542c840e0401e5800c94010154111b00c400034440940c3c040c0d44036074400c40b8100c00b14503042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 357200494 1250 357199244 357199247
    0x2306030103030e180a0c08010f0605070314070b0705030601080a060807120206040f14100302030121060e010501090e0d020601030515070207080609030913020313020f0604120c0602011803 82
    0x200500001e002d001d0543e10090803a01c440020b0844c1c6100c3c04603100c03060504100c0380002e00025080718001030644000070038080742d00600744003154450348429181030f00039074050f90079040a2113258002041805002e001c143c8a80e50640300d182c0c141e030340b40e682c0d29050340050085000503040320320041ca00041401819400181c080c1682c00310280752000302c0c0d061000031007500c200c0e08050032003004c00d50002000c81c40039506070200e40342112b00c09030702510030004030101d00092003841040c0002261710f82d45c2c0c086501c5480c205a0040c44c01184500304080c0c100e0039503c0c01e030300860f241c680da8560b454440e402405804046045880a8141d0b540365403120f036611030480000d4000c00514202050f02c1034001c11841000b0304150058804130300d4040030036031f10b0740c105484250284407180c41c4042c1101442c1b084074441d03074040c0740c242300c2c1000907020302019007400210550400b0b001c22011440e205845158405248209102c110030b5080c030390020b003134030700040c80c100010b41c0c10714032000007a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 357201744 1250 357200494 357200497
    0x30c07081c0320030606070203100b0901060c0b0601030519090c0302010305060a0f26060c03090622060e032a10060e0408031b0c0a050c010915140405040e072306 71
    0x2e452a40003e03280c3e1a072200003034044c031921f90300a40c544034003000580041c82580115450407412661620140c0c3e0301e50003030f00c1d4552410303002800c048501c00001c000758000c0d4080c5412102007104850358507020700c4000c0441e10040c0e003d80310702d04840707810000c560389070048641c40134081c1e900d12440c914081a0308500c00c1c2e03d0041c80740d1700801c81c103201102d8504880901000705c0d10822030380d82e0700700342604201c1e65105841303450150086c2070000c1c5282c14012000c01142e00c140c41161a140a107890302c9004008504c4507880d40d0004000c204111100d0002100c28030041c0d00c440d196002040303c01a1820008900224030035043c0001044a10074440d09036900540010610f0360ba82d82c0d511400b0076440c140b48004a07034441c049030420a2407000100d102030107100d4811111118002c1e001901c0f583c40c60b11402d1280c1c0315509500031002d116040741c1070303014610a0700a00f4146c4400008080d40c50f211180350040d44003c0042013040c60401c40039588041003700c01441044003000719165 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 357202994 1250 357201744 357201791
    0x9010e1204050d11041d0118030f050c10061509090b010f270306090b0a05010b0d110f0f070b0703060605070f0809040e070512240702030c07081c03 65
    0x107451031040c6a4103120000c00700325813161004000b045005250220402c0e0040e02c680103403901d40c40d200d0301c0d2140210410b090a002ca4241d10741190322404850211003980c480001d4000311f010341018044440350f18012280613003104100a00c003001c2e4500b0040510050f0742c8954505801c2001d080b0803030b60810f105081110081c03802c0280303502c90008484c0c030035041918204428425000020a2101c150301c00f9103003a100341b540140c603484036411401901c03800e020b0844d48400412102c040d240d81d5501068845400094040c1001c41400c4030070b10039089520710700d00741c0d4000030b800f10401800708113440e0700244906040142500344a0300034020301501c40000c0c05030102110882c2032203440c200765410560014020302901c0750003030300035484109503c10720303000d004191844280741c10003141e180d10099840854800c0c031080c00c000340e805030101a06142c1540420010034010040c1071045601524540d07004040d0a1604c01e151003500200e251905d0030541b8108400381c1300c0c00c411010181 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 357204244 1250 357202994 357202999
    0x3222121020f0c0607050d0f090b150d061b0306081902060f04080a06090c14060706050718080f070905090307020d02130e0f060a0212070c030909090b09010e120405 72
    0x325421400c185035401c2c8900f01d08034040b403181e02c08001c80d29500c44000c00d0304820020080c040050300c165203106580300084003c003d10000000907540040c1e24240a000110040c402140400c640d19081e04440c0340401d100403040410f81c02c1d1501c02c0d05802942c0003020000002c1040c806200c0c0b12820761101c2a1000340300704000105510945010301c103403409000f085054841d400000c0c58074400600ea60801182d040300600c4000581d451f0144140859500141a0310324206250b6900401810b0041c800300c20b004021340e0018000c41d00c00a403d0103480d03c41c2c0188502c1e5580c83e4082d192550640c0003a010b24100020810426004411b85804560544030041d400c45d2520000b19a55410300c904a0341901d0b041c1001411079000a04a110380c1940058404c81e0319806200b0059225144c240d0b4140b11512000c00c4040344915910041c030b500031b14200606075200c880030001d0701d00341c3d50192902101141130080c0b011080c03050b020f001054500500c0c08000b5605d00810302c2c001d91141c0792 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 357205494 1250 357204244 357204247
    0x904021008040602041a070203012a050309070b03040b09250308130e1014030106060c12020f060a0207060c020706090b0a053109021e0322212102 64
    0x8080103000e80685011b4000c40301c2d0079541110080c0b8042440d000000d043c0e2083d030901c4887e18800700402200d004000120b45c001c4011294440251903562001e00000b07041d00c00c4140010f03580300c040001d5070066105601181b11030034810105440c1504c0744280d040014020004402146207500c24401220380c80705402c2d03164641000601303c0343c041580181016410801001280070440b0095000c0e6001100c07134000300d4001800381800c994141c0501c0001c981714950140100c6c201300c14001081f003681c412101505450300110f4103003002900c003446002d80120701c0310304002d0700d80105181c024803071000700031a900e002d03402040c0c001c8602c140c01c0011400074107400024400e90880e0b031844000b000e030080c07080d1543c050030442c030aa000e05442c0ca01d030103103021400c00020f0007241c810800201401c0385a403030030f40075001c06c0e40c005417044040f01035907081d4400400d1b1200074202c0e60341c09400ca0000c04003814410b032158007410f030b0034a0100070280ca003507d165440640300561900341c216005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 357206744 1250 357205494 357205501
    0x90111010905010903020f0f030f0405220612020f012f0a080f040f05010519031806050a0c0e0105070c09111b030310060c0209070c022209050c0904021008 68
    0x900600c40004007a02d15401c201100041c90740000c0d240308006107030800c440500c0d1410029544038000c0d140ca400060504007c00c015030b10701085144c841c42d070031111002c42c0b404460340c004119001580494590f007040030310442546801041c00398180401e00305444440b4404071101c0c040340d1020112280c030a140b0102c4401040108401c2969a6028001c56521414940003400b1074001d8483c14107400301e54403020815510075400d4a01004440030307920030b2020500c0080d009001a00c0c1401e400c0c0c04442011408140c3c80c0c018240288083e05002070800c855060007001c1c440b5000c840c0341030040402901d0700040800713608004032419800002120301e07100b0845006441103000f0502c8040340404840b1001c44040021401014115440300a0b540e4803101554000800c10010754802d01901c00a071105010714418115548005c094020090170151058070340c402483c0103020f450341e030f80038000400c1020401e50030305a80c2215031900516090740000c0c51441d14820140c00c001024011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 357207994 1250 357206744 357206777
    0x4020f1c06090f0b0325060f0e0a060c020108060102070513020304020a050d030203032203140a02010f020a030e060a0506030c060a050d062715050d0327050a0f05060901 74
    0x1d4000d0020b642d018400780101c0036005019006090300280b0134007444581390310419440300c020344407039061085c084a5911349981901c0c21524405028140f14581121034440d41c0c844c80410054035040c1c80e0401c03509142d000040003000c0043c180c5066600c50078080c030130b507661182d0203182c40030039135005aa65038540c0301103088000e5550244e80c0219411201804140d0040041e522138444030500744e0240a005000359689110258042e012501e000110f044d08070b9094010160241036000202d04469403802d0b00d822a84008001c1000a65400039020356007418814990003e080d1a8184401c5c102600040e03200c1c100851624420980081e101c000f4a01a80640f030341d0a034108800c109013070f03485403405080c080000d40c100c01080703401201c1410220502c91507040d002c40040c0d04880c03500b0a81070041c0c5a0901205034240030350f0008078040180242d1301c41c8a020504c0110014240c5081c5c1400000710381500076100b0107541c00e00500c800e489000035607075042d80919103a8500a02c1480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 357209244 1250 357207994 357208001
    0x71b0f12080c101b030902130c020a12030f0c03060f150c0b01121403120103061a03100b0a05100210020a0306120308010303020d050c060c0f2106030c04020f1c 70
    0x6180b8494001c02c068004010310590002590100fa0320340e4100340c1880c20703811821200a501d0003940300e980d00801005404d036981c01030f205140755004403150174205844074101400b508200c4000207031184013603071101c041402108018130080c101402030a0801d41c0109000541e1f0048048804280300d0b5142c40501c51645424656001107100c40503584030400185883c0e020301050b940396003802002041804c000045644150158809144a9003135a442902416141858503411800c481c0c070900156404d01c02608485441140010444c6000c010300c0a120035550003288a6841c4030b003100c003a5600030414511740c1e21002001a40c03001544015002094103410080000c400d00e00d2400801d0340107000b483c10307a4040d80843e0900400b001c800c48541c4681001800305421080119800c408401d0183c01180c10b212203041c2403500f0742d04001140010262900c08500110040c003900c3d08062007900122030301550705510313000558555102c0d622490003c40b03038016800c604511408010750 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 357210494 1250 357209244 357209257
    0x201021303030302091509091302220f0615090e06011e021b090c0a03050406020705060405070f0b250204060308030907031103060906060d1511071b0f1208 68
    0x10304541a0710303820020b0094020303444060080701c9600070741e040080c401d415140c01541c003c0c5840d1441c0d80750201140c18648042040380c001400c1e0f18410040c0c82009201c2e1401814164000b96150408003060309039203051348100400c02c03004209400051b40304a18100392484689030a81035106c2c240100d410000748018800c2c41ca01038084030101ca030340132418200074003a44142c5c484200d45007042001030325066903e000c41c0d44041108200d810700980000360320501030b9500504004040d02e03460300f00708044030216655000043c0c00d22400c80684003860103010303030f8800c01d4140251040314406190091014003503101410012a04540c0c4541020001e5984100310301c0d200d00340706491a540745010b010441750202a40b149900303078100021050701c80c1c03070a800180040d4450a041c8030f0b081d43e03408819500392950705001d560b51132450207400f0b80210005021591104a070038041c0a4051070704041c0300009140004110242c80c66244009840100e800180501d140303142004007889500e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 357211744 1250 357210494 357210517
    0x2060a170412080a0c05270a0905040311010507121a1302030603011d0705062107020303010509070c0506060f0103060f080c19060203040b07020409020325090603080f0a020102 77
    0x35001c0004002909100e0700303107030700641c48194241d2102c1c1c03440400c0d00c204003000c5000500038000c00d0105151050080e42c000c480552402040c40701c3d40220707060400940050a0194542d4144010143d00c900c00c9089800018000c004a040c6418000c0c03001c01c40c005c0c0718000c030751551550300ca2843c0c06c3c0c3d500044898001d244100c64030180110b80045d4100301c60361031207540f8144c0c9851410185c01c900c802d28588203000780c0703812410702c2c3c00c000240d001026a00540440c030203401152074441e00c81039000d404150001c5840b5817401c0300300101d244e0700500b0442005000444d680006500080340d982000040784c201407018024801280104002e80c480444004201000141c1070302c00700303030241014000c2d1540403100d44a40140c0410410a02c516001644208410080a007921001c0e207540ca10040010800304a1500064a040b110074000030084031b1591a0030081441c07541400020220f0f45800d202991950b02d0300c40d8180207a941d0701344000400640004124400c0d411550707a4801d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 357212994 1250 357211744 357211787
    0x904020415110c060a080420060a0c050118080a0f03110d1a04021c0b0f1002060f0f161103070c1707090506060f0d0b03250b03070c02060a 61
    0x460320080c480c844201082d042e901901c0a01080390800700c0c200c4201c1e595a4480028a49441d5214007104461700f4003c1ca04810304c0041c0300180d602ea60040c48041d080350342c0c401c0107101d503051085c00c4a0407075103003070280d502c00c0d1503410014054200751036180c40c0704e0030450016200703820142c000d0107807640814070b8030303500040741c070900e1300140d0084080b500701300c0c024041e082200c018801240b14100325848003d4210090102d0124a500928004000600780c1002c00401b800800d4001182040707410268000a08001c52500c0b18601298000401c084030111810400d04684689005c00d9080d0200b1a01031902c00c94860204200c0e51281d80c00f209502e021955008458450030644100c05201e0203a03900004201c1d8290080300c0c000c180003402c542c41d040c0c0800140d801540300710f000b011420386515048400d5503091000c810598013421101c05402081180f5041101040d00800d4001c10f0a1043c0840541d0003030a034124913505580c42c581d640c01c0c0d440c0070303a80c40c078040720b0751144c4031407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 357214244 1250 357212994 357213029
    0x6100c0f02040b0a0f080c0603060102071a0d0f0605120109210c0c0905070f02070e01121b06031a0d05060705071a04030e040c0804050a031808010608070317130b09040204 75
    0x961703185040310028030a07241403506400401c0000d22050b03450600580c04000244240940d902d210030311100700d541c40d64a843c1b0708034400e40603a02c0c101e10100380b481c0d41342c508126504040c5181c0b90081500780080140d40490b40d03c00010a0080c1c0a8000e00710240b410040018000c0900c0c0a1a507044171040c0c2070643e1300c2c8142c1c00a40000c545040009210b1284e01d01c840e40005402029941d944500b0f264070380c01c2c01303031460740c1200500742a6605540c00b24032225081a00030a074001d40425034000c05ca08040800b010f14240f036041305039014480f1145a00c010507008074034160080014a401551030703010b82800c00d4130700108481c60008046550500c010550402e21030090503205803001d120500b08841c090380e092408036409006a0015014100024421000c0150380441504e5403140e0540301d80600d402c40d8070f5500300088990042c5003e105000910701c100d40e8400b403400142d0324001c4201a071070601016407094900c4140e02281c5240d4070b944603015900640b444488040500b207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 357215494 1250 357214244 357214259
    0x9211e04030c050424030602301518130602090a2912070305091009080c0609030405060f0c071503050f01060306050d150905120403050606100c0f02040b0a 68
    0xc0d154800c0c288150303e0445e240c86607607a044511152600c00005201c8194a0350b1100f038042c0d07104100802101406404081080001d00001c50215041e070780c0c500d043e0716003c00c000c59586220000c0700d11890030f1404402d41c4068001d4080d5110480b118140003082041c038058019025100c4140e51001c0460808102d940a241014880c43c2c00421581d182c2c10b82c0c1890f011a0703124403e030050849142000041500340690031460700001c0c40021104140c4180b5140c000301c0700c619000300c50401000070040d400c1c0c0d40070040d95802c482d001000d10701d003928140019015114030341c610b080c02c24012600ca21094000e0141c0802090260f503503c140441440001b002031030215111009150700300004180700d40309115010541d080074041200a01140d00d0380c014250140f40803080c0152a42e0b9407500241c4140000102880c1d02d8840381e46072030441c5466810310728010281401100050362540855a005400280c2141c01484440d884951400490040e110848003680c10100210340081d849 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 357216744 1250 357215494 357215513
    0x20f0609040e0d141306051305120307030e04050f041e05030a0c1a010302060a030b060c01020703020d020601060201150306050403111b01020d020303040c140102030d14040b09211e0403 81
    0x1444280c4d24072100403040d58000b0040c1c0100381081110010240090100a018000411348400e1401d01d502000f680c0d42c00003107480c2042189062950400302d00d03101050f4000b11105001a800c13601400b46240c411a00403002a0051000d041880c0da224048807801c012406c03c0840354120096a03039901c0c1c08480580301c1c2841c1c0f481154000807404861180600948e08170341a00d80c020800781c03030450300503006c5016000c0c1c00d62080d88080708112440c03084a09100428045103c3c0d00070303200710050664080e06207a130590002c4150f904200440c04c07140d46030b92109064030384c04580020349403102e003000c59690b0031008a0071014030820303e03594200080c144c1d500340b07140d078242d0848031114444a012070f00c0c0c0c0010341c1c004002030342d458003c1c40041c00e41120030300b0070304044c4122418504000309080c10368540d2621510b42c581400c0078001400034100e00c0d0b40d80104000e0052480f110002000a1000c07a200d145515a03180824460010302d92075286200b9000000700381a2103a40324280078400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 357217994 1250 357216744 357216763
    0x180906010f0e190c0207050a1d060909060a02070303020403241a1c0201030b0604090e01060e0103320706120c09060906050d110301140102010e0f0a020f0609040e 71
    0x41001030400091008014200b0521840038180040e040c6582442440c0181c211481242c055000d01040450300ea22014103070350081040e01e0241350b0001144050101502c006003145014215071800c2105c1e00d040087c980b07410030300f5048010f0b41d955560804030000c0c011900000d00d054a01500c40c100c09080f20440b01c0c50b0484418104a40c8078201c40032a00070460300c0c50290450b0a0030a000003c0242c410071140d0940103040c08506494103000045203503020f03410100303009513128000c458040f0f09110f020003a010703040030030280c0d50464a800c03000060b100c0303a400e400440b240106620010741468480c94092a004941c0302c3d0f500c8000161a12505140d6400c503185402003002300c007881048000100c2c0c1701500e0b90004141410021242c1d0783c8004022007030191034030a244120110100110300801e04c0c1d504201e85040c00b4400282501c17040300b0280043e502619964000c7e800c00302c0c2500039254100c9003d161050030601254481c003d038503081d0340c010300d0701840c60402803000c2880b602 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 357219244 1250 357217994 357218009
    0x18040201020616020a03121409030406180e0c090d02040612031206051f0203090d030e040b090f06100c020d0c0602241503030d0e0102040515120402090618090601 71
    0x845645043c100f00450807441548070041c1d011072103940c0400d0145603429062600c00c1400f00b18001a030080041c049419a480d80859100290810580f42e228007022849090048841a0185490031030070010700c2c040c1c03c40d55000c000180812031541c82803400440980e01a00901c82c19035a00d04480c446090184241c01040003685001c501b000d652040c40c0c1a224010005c1c6907004290301c0218650340038117801d005510007000b80c3d2900e03070b403600c4144500500c85c1e681c23540d0b071b804140288400e580c411188140944111402e00002e40b0540301056489035056a030407484030980482155000058038004e500485151400418880d2070710b064401d60f400c1e502141e2270106003010148040b100194529120380d00380300890400340d4040555001917170010116410a041e914070b100c126202c1a07400c0d0701c507a5001030200640d0620f03848109880115104003402d00e42281114403140c500148003d200f1808180000d2655030f91070f4080d0b0300079044886501141c039220343c0d900d546510a006000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 357220494 1250 357219244 357219253
    0x504060504060b0d0207021315180e0d0302090102030d020f071412030a0b0d02030d090e1305071404090f0807060b04020a12110418050f0105030d020303040f08091804020102 76
    0x40a040038002d5038101d60168522500e05041802008020340160000304d0317000750320000c04001100c89010b100c40307035894120703c141c200f45850a804c211040354603007000c3d802d00f41003500344840e10120360031002c550709003005656404100700403404c602c1100f400104c514070124071849071441c502d010303200d080d100d114480c1c0c501c051400e000355079200180813800228400c0000030b580c1615900603c0314020040d1644d8000a40b40d03001078100300c600100c00c000105845010001014007070003003034200c2d40890304104080c11a4071190b458004c40e000b40d4074203014501e124107182c0c0707881e40041c8200e40c2010200b408040c1a16180c501ca5100007002c1e9100750400780c2c00340940c941442110560b4000e5140d0700095890004c01c94098200940c515001880074080003403c8400213628001c1c0c82c3c4002d070009880e10740500075201180c03060308118000d0b40f0548031003a04540000440307801613002a017601c4d421415107003484061040c1401c140e042031100403001101c05024031802d0142d031007602034a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 357221744 1250 357220494 357220499
    0x102041806031506030209011e030812090c1f0305041b0f08010b01050307090e060d051f06150228020d110103200409020f07050604030c050f0a0c0e0901020c06040c050406 75
    0x1c2c040e13a060303010207944800701000401800c01900300741c54424560b11403d078607a507034948800c070450300047e2500f00310100c031700100202c2502c00c1c400a6004901112400088002c44d50042d050240e200c003801c05165030317400810248008104845a803a03034403891200c80c01d07280c80034084030101600c2000c91641c200140120f40d98002c00917244101c03020360b50040802d20341580d01060301b0018003107681102c000251000401c60903c5590714a610b0304142e00c580001502d21030048440c03175405944010030500310b2500c001d0f03010840c60b07201245001456010f21071642441505464450025480b40d04071171400c080040c000080c0352813400c01d8804101c803410001c070710451501090f0011040c3e00c0100028880b825095019012614142c03150505020050703584916206040d20243c012800010140d010030400300308018441003a00040c16940c001c0daa10044800700c070b8001e8003000681100010150341c03095050714054a4824211406400c1505000032520501d0044034021401e08101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 357222994 1250 357221744 357221783
    0x50724020607120902120601090e0f1c0513080d0f080112020d021012050103050303180d0903030305040809030115170f1b180406020301051c020120010204180603 71
    0x840740b040d4039640f10600f08032210101503005000c1204200d81c820640314400d03520482c2080014080c1602c58000101400f481a8071450401d07002550100c0d54000f02c070700381129104c50034100182c00c0b18108141c0b1403068110500b800412034101e80c10f03900c1489000c200103503000500c81070b9001a901d0b03886042e41c0720b140d00810002c0c40c3d000a500050340c8500fa02c0142801d00010394070825624014a449111925400903900207901c19200b903400401401184541c10454801c030808140080c07046c00e904500240113441c180c4070180a1640c3c820015041c45814008c43d1100440207008114041d51001344440c040c2c803e01030347c1030f8010140c0841d810200d0000350003011080050050800e4a0400385010720500c0d51152a83c0000720181a03078070301c0c2411015075000e07601c00c0b40003580b42c0d81490148800200100d440243c1400d01200d5180947d8024280b40303c900400406110403d610100c0c0502a02c038175071281a00f984181d8199101d0440b541c40482580c0c481c103200100301d1341d0001d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 357224244 1250 357222994 357223003
    0x30a0f121a01200a08040f060302041208030603031606050f0c1c02090a03170301080606060f04061b1b0f0b040b09010f030e011a04200a051605072402 66
    0x141601c280c0c8042840341d159800382d207090388000c00103100119403006a5900904106000408403013004002c40c0c14000d120104204c1d0014110600d011414a0700c2c0c0101180780d00500780014000c2c0600001080c0e040d142032040b1100003400e41d00002800e981e9190100c01003104413070207081d020655001c2480400841c048076401c404039000f2100483c485403001e402035211680c46580010040fa0000004420040d404007a01544c140e8584a626290302603041800081940b40700d0b002c1084035140a59001d02583c050b61414602505054580450940d6070800f46d000649060500000e0305089030b20b6084080c02d84103152981e81d81c2c03d5403042c52682500441c041c0381000c007000d01002c105944216603c0b40060561300d400b188070340c034961101e42154810360883c0d101c015540140241410103000315000240e210345200c00348071407040c101c20b2a009a050035800c100000480c40c1040c4810102c409009400000352601d00d9036881c0101e4091000c6010250420440603000c0580c031300104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 357225494 1250 357224244 357224261
    0x20a0605100509130b2d0106030203010609060c03020d0e0303070b0c090a170a060b06070c08060a1b0e0103050a02071a180a05060601050a1418121603060b0d05030a0f12 74
    0x8203034920b45071910b080d000b4542500b86201c0c03504d1b480c0c21441010009190450090281d91001070b541d50501e50000d00314030598110a045c800e000580310002580000d101d5100c605516202e50002110740011341140310741c00001e05000200403d00075030b0607021000f400040c1040f90030030300003507880030440e441e400381404030841c07600505030000c08994650031064244070018102c500e45803240d50f946d41c07c8015904008600d90080c000c10499440c548140f40d0f4645d51014802c00300c0100700300041041d040f8125a60406460700c000c101911001d4054030302c042e51002c442503001c0074100c0140700d069000c0324410252104080007a1842d4030204900d441290882e002c1c00559840c403005449a9010390712110402101c20700d48400d610014000d04007240910520301d56900c00305041006480c2007500d00202c1c2d401003003070840f46030101129402140d07442400480c0c55640400051034840025101401c2d501000030400c00103a440400d0140500940d00c40769040c8007825682c0080301c800d903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 357226744 1250 357225494 357225503
    0x10f0f0b0f0604090c020a050d0c050c01050f030703110d020d021e07050a2d06141014091503060106021014011401110106051c0b0f0c1603020a060510050913 69
    0x20441401340c5085900580e503054541c1c0101c0e61800c0d40d581e281450424140c80d41c10010f1b1071440201c04002080c41105a00082403a000c2c0c14501c4050740d8040a20001d0030010601d69141e500305a9030b00d0314000d90348180d00402085407284040d07a00000a0b6200d08008a0110707170070fa005031040462081500e11503504400281013040040d562400b0198074110305264241810510901c1202d0b03801c008210944a10030201c0c186034064400c0800390001b6108405041c02d003041800314016100c0742056170781d022108545151200982d401e003181a1100755030b0140650070010519680002d20010b445401c58410040078544665001c1918401e000ea00300c0084074440380030040d8450007035400814290800014010303901c0300059403d01c8210312962890700e1841907041441007500200340d20200c110040310f140c1c07910840e40030591090001d0026610078079a1000d0501d4030070004000f00340d030300040400c400d0502c000082c0301c0000c1c900c00c05101d00031b080005060108440c44001c0c485501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 357227994 1250 357226744 357226747
    0xc0402070f080310051e10020607230f071a010603090215031801140118090b0c0a3c03150302010311070b04120305180303061e03010f0f0b0f06 63
    0x180c0e503845519a10151039110314404100703001c5150346e1031042003810aa40071540c106a50480000e000d05000b0741c80004055401040c07c101d000f6801c01692140000314440d61341d03516402041d401014004e0044240e1514004110070301000080710640790b600072000703013605003680e94401c00c40075162103410080d044405a005480d404403a94069900468690010581c01c110030a4aa0864101c48403243c1c01c0000c0100400c41c00480324026406a061014240301d1001c0b5a16180d80003080a041c0141c40b000006004c03800030b00c22104000c8074210709010800c25074080031061100101c0c01c1500c5e20130300521401c41e1107180030b4820f090074402030000b190a1540b171500194010641d41240001091041000400103110042c81d2481030b403182200001180a50031300404a4800405100428052816081c014440081501e81c80107086a03145810b98046400c269444104a0216095801d05030281103040300740d0090701802241240070000012107008000400c0b49451440360842c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 357229244 1250 357227994 357228023
    0x24030c0e0c0730020604060c18170307020604060c0302060604020403120f0224040b13030824041109040f020a0c0813050d0308100f03030806090901110a0f020c040207 73
    0xf5148030582004011080318640c01e02c0e0140120011000f5640000107800c02c0003000100000313441003810755219490081140d040b42140010b50103081d0140c80307603a06e29082106000701007042181e01d901c0c0d0103083c0540b51035071044e010f049502070034811805030050b43c002444c0c03030901d8030a60b41102d0300230342841c01c2e01c2000c44c019a214004988144114040d2400707034901e40602d0703210002640004800c000c214945424001342c8600701401d0a07400000c081040070119a000044581162210508080d1080a802580c1540003610100c40c0c01c5420b000402c07000603046c2000c0d09110b5410f039400d000a60f01c05014200701e1150a4003840840c0c41140c9110106480e0383c0602000701e410054401025107a17400500c5d456000442140050121b8080001c403124195070440140503c030146c80351282180d0300034100301c00c01803101d8003a034800d4000441207802500002070740c9203103001503556040c030319138001e0145000b10101c8025108140381101c85081903c03c80d0700646d08481c0c1500403c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 357230494 1250 357229244 357229253
    0x406050d0510140c070311070b03090c13110a050313020a27140711030c0601090603030f050306030703030324060323160804230307021206150f0424030c0e0c07 70
    0x2034142119a1449604400314101c4118401140603105000003011460246c01c04c00040d001cde00002c80250b1801c08021602e01d024070826214100c0c0c3d135080040d04c80d501c00c075140e5840082444003a60001950b00c0000d15280c3c0002c8100003510310f044101d070048159128481503480c074010041c00000c0c80000103400c035100b01591807071520144141d03441c0031149800c540c58100b0a801483e01280da40074100100f41d00624402030002e401e06003a0305502d021400280c455540e8413003e024540c131080030b10480799428580c449070030902c4804541c100d8032080001d00800b0144286010800e10b441d20400210b040d1002d18841d6000301caa100d4201400d40c012100000702400c225030303006080c601042100310344180c0c9410042801c0046454400600411040a081c0c1000c07180a420900038404034080194408950460a0701d4620014804201180007021405a000e204582c0004c0070491240c0c1c282d488003c40b40a2030441000680b142c0c2428094101541c802d403460f8810030a800024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 357231744 1250 357230494 357230507
    0xe0112050705060c10060320010f0203030c0f1c0c030b0303040806011214150a0f0b09060409022403010e0108030c0303160c0c0e0906010602030a020c0f0406050d0510140c0703 77
    0x6003100c0d005d5440c00c0340c03132401002c2510074980040769003c0c40381c1c3d84183c0c0d05e00d080b035030811108001d1814185903211000060340344c0c8070140001c908144001001828000c1c079908440361201c40da900e54000c1e044104c20310b0018039030000000c0c00130781403d00f08032081c0340c0041070324140c030075035406032010740d217882c201d201d10064803a0111594140040c0c0b558036079405100810b4808003600d482c680e2480e00420000884181da60405c85071464011140625240c00e514990300400036600001d03d050140000342c4003820b81800c646062916440c100341404078007000d503048800f0b4009580959032100c4100d03441c0d020303603151100181d0080c40055208410650400440d48460821010002240d11490b80d034040a8101c0003500032008140403802c102003041038010f00c85440954145200e242001b1344944100d410070780b103a2400442440503580710390108000302130007880c40148100d00e00c0c0c40740e2079410480c0f070000290720b80b030903410254540911051090700c000c0e003440c0c82c089861f07a055500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 357232994 1250 357231744 357231757
    0x12090102270a030204021209121201170708060a0608150f060910030606030b1f051f17130c0e040305070807030507050a051605010c0f26040605040e011205070506 71
    0x520550020140c5c4a41c8000d1015a00b080c50444140c601903480c40d00e0208410700d44040900d00300107040403404008102c6043d07602440252804074403161405c1d140010640040056003d14028040d46690715840361040f94034203000c1d606064000c07800c0311031410301220034862a4070007000007801840c2202041ba030060011402d8401662aa12410304813215600110794035080003052080c9003411480054610085401da191014184000302d180080320181142810601c0b40801414038060032080414020300085042245014608125070303008111081c1d40d21142108089103100e40140c5c407920035609521801e251810980d50151b056000300344c15000c00c5414460b003000201d060003900b600c1c50280c0000c2c1030b9907501120100030020f0503030200b03050201045a081c005002650b00d2510140c1144030126080315851450500c00403a00110414400004022030700c01d800c0707401740c4184c40e031207908203110f0780c0c17035a001c10100b04600c0005402075200c403034100014030b840c1005010b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 357234244 1250 357232994 357232999
    0x60405030306150708031611010207230a060e100e1c050708040b03071809020c0606091b0418050a0b0105090405060303040909060b042a0e030c06040b1209010227 71
    0x5030030056120300c20141c00c181c4440050807c003104205589a2080404034040b051100071880d001e2640e850f4400781c020920030300003215114000c040070309400d100401803103811000c14403440c4482c10500380c0318545880c007d810b07540750016006101c100040c01090701c222102580e1340c01912084241d49039001614111050300c0c0c00c0001050804240003c1d50180d113254031807035580c0725455116a200c82e0740340c0150203018814006258055000110550000030a481c62501c0c0d403501c5511054905034031182e5240c91b1400100001d1480c074000b006811054804070400c07040d211500301ca41038407102203a45000030400e01801c030795890a0b91045411840043c100c0b49003d82d00d08011701500c24002d010740d032140e42d41c203490340340307040c01d00400500e020907020080300c15001d0281c61811806412a0804002440301c0c0c0314101e460410205101401c000c0840f0b0310b43c2c0d519459007900344c2c0040e844032005607407200440c0f1080303014025190111030701c1c402c0c074681d11412842e045072500705108059 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 357235494 1250 357234244 357234247
    0x1409060f04170a0224090705060c0f0d020d090e04030806060a170a23040201050319060302030a0b0103020f010f0f0e130906050f01120c12050a1a070f0206040503030615 74
    0x5000c070101001030003c00c80d036402502050500c2c29459200380b5040c03440560344903207001000090300000c1810003d840b01102c5098503000501c1c06a450644601c003c800c3c144900311080040070380020300791605094682e035a0700d0103034031020f410100000a44000b4081900040410f000b46000f0300034000300d80e540e141600720015489200644c650382904c0411a440e030320401c0c41c00c540a180f001d6103002c3d1104144040d82d0400d41d0000b0040c0c40002c0001d01001003040c000602c50311940c100c0d0000b19002001c03150024001d082c0004026402e2104a210322201b0b89030301400d50144002c1c5170600c41549888415034031400c0f00780c56560454540c160702142500302880224014441c03038802a01a80700000d2603e06020402110407042e00607200d0040403a40744400a02d6000c095001d5030081c544000108030740e45002450310402c0a40142490218900f44038401c151508480c494403d13581d4165002c640b649060361a19400c3d640034110360403c000007070603400c1c5101d00c3e400d5043c00c040d116 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 357236744 1250 357235494 357235523
    0x603040203011503030f180b030105010e0a03080f04051f0c060b010e0918061b0f090a09050424020a0806040c110307031d010e030d0e010315060e041409060f04 70
    0x3c0541030b05400450210300310700c407004030007030f80110410006407024148010346810701e010f00c85a400148a02410011000c0f8000c0c0c041d282c0f60000340045500000c16a12081c0004400003147c01c9030150304d004668440d01415408400c10001a405400d61245051030040380c0740d50001d8400100403a0500407050180c0c100c2d9210100803501c030340c43d10300568100d1201143d559003003c0c1c0181541328954143e0810f4482c03824410115202c80d10003649040d55401d030311000ca80c59504503803180490910302020481400100c0d160b06169a140341204400d001002c40281e0403402000924000220140b0001e02c00f4140b075804681c0d040d844e8144040000e104e642c02c01e1450b400400c086000507640c060803008000f803407036290f12010007401d1851882d101200401e41d42c0c03111481c00d00c104446450b0142d06a4083e40c0040410013503541d44446031500c5000c0985159041e140442c000c07417400d509541d03151042540305006808410142c80d5949480b07086200e2a00083d2082e5500040145807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 357237994 1250 357236744 357236771
    0xf1a01120e0d02010906050a1401060f2c01020721060207060b061908010501021504080a0e120c0102190b0c0703030b04050f041a0903091306051801171b060304020301 73
    0x90b0b0030b12003400d9001040b2003c00d45020016900c2c040c000c2031080b820048080b41c1c0c58541e0b00031506698180c580410b142207130507011034896143c1101d0415541d48201c02c2008a884100d11040c08e0781c0030703000c0390105507844000390204841c220515409001082910001402039001480b140b8016103000c0381581007540000c2e9164000b0142c840700f030b8206655041100e8004507461300404090010701440011801d0714803002d24000c2000b041c1c040c0000d0070289d0a8060209204400d1020302076900082195447d682e5840c0c40c4415140544100d038002600d01e0102e6080c04d10141d40710715151029155910702140d07a0700b2502d000c405050725540d880c1e442d43c42d41d114642c8a44210020a40181001d003040c00341c00d4800c00c2910750102880d8204002e240002003180c031390100907518180c04c03031b4051a202004080f1a00526440391985c1141c0704003410b04000301c0c0c169000d90800c11541c0c9802c04c0b020340e0701c0c07241d48480107004e440d0000340355091804502459000303001400105409010080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 357239244 1250 357237994 357238003
    0x90203100c030e15040b0f04021207090509070909050309091e0c03040b0a0b1f0509030615010e030703030905060703052101030b070e010c080306030109050f03040501030f1a01120e 79
    0x440d5000030366203140003c804201004010a102e0504030460402d003440d03160201d171004000d045001105690020800315101c03400e80d5007031600d0079000c1c1e17190180c072011050090101540c1940e041e1007580d0700801c0700481846601d030841d500400540c54003d85a05008910200a0070100c0078440d055008203141c1580040a01c40c2c48070403107059503485c1c075242440342d075900038040d034a1702403070005940656224001503081240c0310170070303c4444041503142110b46204224840707806000e20b006020640ea02c0721140611558240c80c0d66010603d06028117643c0c01441c4000340000707050316030030002810860020010306000e07160051410394031030101c0b480358074502102d0702d04c4e4503003500400c148107519015540026040c81c11408003903564000a201c2403080300c4c087d041a50000c042080350760258050142039501500b81c03596404c20544543e229009071042c40e02103070400d160342261803420301c01d0101e5180c22050005020102400448541c0b05181c00403075196900c0306a030307005440c10030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 357240494 1250 357239244 357239261
    0x50307050a03060906061a280e0d0204180302070815160e0a0f1415040f030b0c090406080f0610030c0e0a110f070c050a030507060f1206030b0f090706020303070309020310 75
    0xc4116a208020303a039803e4140c0d03800b40410b1404010322350f000b400640c072006002115008840741803a501d03090002030700800d1f040c92000c0313641700e07000c102c8010941c0101d1042e044403549816200300e2040a560101075034000c403502d460300a40c8060140001c2d00600707500103501d4014102c01280e0340c60341c1003048a40e1f015042207058003840402c40c0c0c00e6140c260038010009804041031814689043c9503c042c500342400000d14840c200c0c3c00084014161200780c945d01b0100400a001d9150740b4241107071102103518048016000d45c40001340c2680d81c2e080d5540403039a01001e1070319141e14140c5c48801c901d002601c0855210380b0341101544031698580031f468850040d902040e503403826860010301c003c2035988a680100c8030300c07100b040442c0300420340004813030f5030341400c51007406d408804450521000182c1c0c0e402c00c2ca01140031090010040381f0a1043c0140c503590711542d201c86103c0d564800d62440b178140107a10400026100910a812101c029071020b0200c60001801c840f101d400e0310b1130742 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 357241744 1250 357240494 357240539
    0x21201090c0e15030a02031b0105121807080f06040204090f02090a0506040b04110a0e12010606030b040c0527040e1005041109130602091201020d05070207050307050a0306090606 78
    0x40051003032108144143d8100f0b144200c008152451a640c01301c2d40740c41d0440000c803400801c0310420074190b40168200c0d10005004114034002e4500309400d0641c403002056142d0b9144034042011941c000700250496030300c01d9a40092005036190750800024214045007150300c1400b10301c0c1c800040c0c403258103031400b4203d000d06c080f82074500030b81400100c40c0c043c28014400d5040c4500202070241c0c0c1c0040350b010030100c0c508039441c04103403004180010201001604650303e0004000303507080c0d140e8007200604400701d400b8024084915400c0f14103009080d100b01442903a035400c1d400e10389095100c81e110740070150021038005804200c00b41020b1001c9254000280c0720b80401041006a42e094165007204480040050401c0d036144450034114940040c507295002601464039541c40d1000c0200b8808a0002e56440044580740809400107036010f034058070a6500201e418070b00400d002c001e4a80183c10710100707a2441d1030300e03c003805c0c0041040d181644e036500d011031544140d004040a02140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 357242994 1250 357241744 357241769
    0x11010c020a0201110712110a0b0c07030507091a040e160303030b100c1208040201020a082b2d06080d050a090801060f090f11180f040b0607021201090c 66
    0x141c0005095a03d10400c0022543c001c2c2c0d1061083d0021018526805134000b01107d00c0da0098001140c0c402003e5000510501000f09115417030400004040050f01e11480030343b1310041d59804105c06a41c1500b00c8aa01194442c10740d50300c0d07040540c04601e190703490108551a41c400b120b001c10352415103800550009840d501481d0044c1010048120516858648444290590b132942c142c62001030380120301700506100032030156842080304a8080780c101c601a9a01d400e10000f50810342c04143e00081d941503964003009a03109203114907580e100c106a104030802d074500011181c1180500c1000312035070b035241c00200d48200c0030007406185004540760155500c10b00d203000b81c440720b419804034816030b0400c1c0b4144011000d08c4819400c0f560802c00201c0d10ad036440d01e2001c0507290a8141440c940404500794103030301740c5e0141c2d140c3c0f401070039584012100c0c4848203102c20750304650025908030004010050050404410b03458044255200020b06100d10307035034000000e0299889100141c26 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 357244244 1250 357242994 357243013
    0x816030816020705150f03010b040608070e01020705221407080906040c0311121005010906050904050601030809030f0d0e09060d05070303050c0c060c011a011d090711010c02 76
    0x800820060300016102141c0a00d10200100250f90341901d010741800791700480f0841c885c2e00754800c02c0e10402401480f015803a03603160030070142c154000c0d00c1004d0004032010046181d0034004c1000b4040c580040c1c0c040c000701401c0000b4044600d030b102e6540300071404024801200340409100c5c031060181d110128010303034284074078018100c84e0b025001c0a8680c0060003444005000000e000080b00c0c1e0100c043d03054141c0303960000d081c4001408500d031b45405440540300d2015156030016060314031032002044080e80b1481070281c410000c4a0050659102a00600125050787c01514600700c0c014122a11000c1c50070801e41081041b1340043c000c14040c6001c45000d26040d80d850b84c2c0107100380c0700000600d1603600c40c29600d4609100c080c00384400041d4000700014203120078584464050052641c03007030b0642c00300d40244210f2464aa2554111145154561240841c0744100c0c600e481c0440942c81c0400820503100d8024281405000400c410110241800c0c020026100d2960300a00f20101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 357245494 1250 357244244 357244247
    0x20a0e15030f1b0a0c060b190501110307030503130c05030706051c020306060711011b032601050904030e0105160609110108070f030e0c030a0506040302010e01050709120f081603 78
    0x60040d00e0700d01001e0966220180c0d104214080d1303002d00c14603142c07112044031103003020710003000815529030300f01192980d00d03000360510342d5410040b604281d031400031112205001d2500c0340500c400041c0020301c2000490903111000307448081c43c50294803421007450b5184000383c03602585030300000106401194503040c107105581030952810310301d40154074620304400011603520919030000d1107100002c40c3c2c107010780d00c14031301034903e072400386003180e1101c9141c2005000402017000344600d080e07500795800d11004c10400c8682c100e480141c00c400c8580c44607601541d5107609203504c1410084144070081d80310344804064001c05014030070010340c4007410706010320038180e00404141030181c103000b0704c070000f68040b15145840c4003a00e00000d5a44204480c1800c101d204070140d0307494414400c02c4810300c81c002c18002c1c003981c4070343c008001040441d81aa030903900c4c00c8923440c000c0343d10ba0004200300c0240f11683c0c4000e92185540d1030010038070399110500d541015452029100c881d11030482090b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 357246744 1250 357245494 357245521
    0x60106030b03010204030c060f090e01060e0f0a03020907050a0c15270302030d0f090803010305160801050c0306220501031209080303010e040204090804080a0302031305090f0109020a0e1503 83
    0xd0750980c029842c09003107484205605201d445810704200c07440001c041380d144103810303400c0034280401c903140c81540e45001c01402075525100e161b10508483c00c03001c2c1e6074605510860b04480d40946030501660703402700182c502d500115070780014800a49520b000164074a0ba8071702802000b040f0000e14150b40f0115101d503402e204001c01100280c11a40a011980010941e60075130514000450070582d282000c601801d4170820007010000c0200c004000c100b00400e610044050f0003154030710141d580c024941c00e81e24185c60040004804002207955410400300c0d10b1402100504d540005105d07030786241080316002d034003c1da10320307401d0070149a00761340c011020801054010002e508550500c2c4480c182010007501c020311495a41b5068020403204105450060408800b40d590010f55428007030344980c00441410511400d42d10040360915080e4919070058001554521040c1e003031400c2c00000b9401650a44180300034490781c10259501e01007200c040202c0e11000c0c503180e0a15100c05002c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 357247994 1250 357246744 357246761
    0x90e030c1615030c021203060411120714030103031b020f0d14010c170a09030e031b030613030c14191b050301020c03070b0705070f0605041a09031e1b06010603 70
    0x101800c0000c2c0c4c040081e80040d2182036042d02c08009503594070741c580000c2c01090040d000141e041d401003240180d80700c880401921500700c42d11900342c00704142088000c6071100340001404143c0b11a00c0a031601c40c4900005a0144090820707040d41d2900720001e60900c000f801e00f10340c00c84c4240b4400d10200f0081c0107410781d142840c280300055405005d100700d000800180007402c2291350b011030304141481000da020149102500b40c0718852910350940b0300300f15400c19014003d10502d13011400d0403052007950702d1160b406070b0f903109810406a0350780f84030540b254901c8545203c0d42070007034140c001510351101100d20503545030b0943c41403035010030b4a0103a1644028441d910500040036540400300854080d00e500103803030501541d980e50242d80c5401100310203861070300050784d0401041803c0c0e0005000d40d0040c1e44040a190f500b80ca105a03049044940d0a100d8005100c6054501021107401d0750f161409501d8900f00550800c03008201d00d9000084034040e841078004000c5260944039001c00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 357249244 1250 357247994 357247997
    0x42301051501051303080c060103110109140112060806011202090a060b2a030f04060e0904230f060a06051503010f0b0c0c0d060b03011d07090e030c1615 67
    0x240ca061003564209407849903986042c031400050281044448080540255911091454451521074002035440c4401d0008440c03411440e10380c04615030280701920211407041c3c1604081364070202c0111024052110000e02e2a9224103000c00c13017001c10b1201d00e0190030001c9003c40e54083c54010403409950140407010a079240840500407401850110f8410420b25030554040e4080200c600c0030210417000041380e01e02000c1100343c2c0010503d40100210b43c106c1c3d447d01c500c4080a410002d00c05e8083c1e40080800411044445503150148070b0161203400e14001c2c2c07416100000b006600f445400c40d074001600341e4801041c02185080c03d445005618028242d60956050180c03039905282e00b03002e140100007020581d4104c07130000300002c00d4041005401e00d420000a4500350010303210000303800d4402d50a00340c00d000d8415070314071380340e814212403c010a1840d160003018002851003a0074040c290004120a5940c03c3c4200418140094001e5114405520705985803c0a1019141c2c640 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 357250494 1250 357249244 357249251
    0x702130504110f0f0603011e0e040b01050a061817250503070f180504060b0607050a0c06030e120705120f0309060c07050a02090601020c0301061d010f06080f04150203042301 76
    0x583c0358543c174044c0e9054403038009215003034900d92540e4a0420001d94825010760590a04000401040c80d42d014103d4400ba24481b210a07120241035440402105005503801503445080248002a20ba000d004000301400d1380c030a80c9000b100b03182c01c0504454100c89402a40c9410003c0b420100452070007042400d40b0754040c070341007542a0f07844174840c0c00c40100c030503101c0300441c0900c24a507010352410580142400c0d5990030030310348a03454850290703090321201580782001030024001e010b0321800041c00c0014103055160f092a46003140c101800503515032050303024014403e20f22900800420303030600c0c40c0e582c0328a03281c8040c1d49004002441c101202c0c20034416100061800079001844550440c0c0740109503417091f0040342340180180b50540d040d030801d1000141c808038810910103001403070b412003005a03218101c91fa220100c601c03da100140201001420312071112100c150058411412059020b260b004140c003640c0090b20103540003c0d41112003030030980070550070003140012a00a2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 357251744 1250 357250494 357250519
    0x81312050c010204090b10110a060e01060f090c0206011505040b0f09100c0c050d020a121515090e06070206041e0f030807030f05010f09020a020a0203010e07061209050705060702130504110f 83
    0x166150404070000600c0b841d202c2c401810f18a80379000400508180004810826030740d190348000f40c807503a000d20016005031400869011151100003030b0540a94550134074213481e20350301d071b003041e4040c02e5141e01ca03c60501c4840890350340c05003000c3d208101940d5a443c1602c0382e052004078003002d903114a1081204425010042c2c070b030182c00c0300444001010120202e10b4074105141440e0f50400c40002c0d007031410a207040051422a00b90082c5c03550100c007000300128400e82d6030b640e10015100200540e0192000030002603180c5258410b81c1c90940704081e1140d15540c6148844544800c01c40c04106443c2c104403c0325818030038031160751286c0c00103200a52519400c030008024501881d283c2580028018000900070040904140d0b8090300802200e842c0b0259980c840c1900d02800c030000c4c92003a0500303c0d81d1030502504028541100207045107a00d8801003242c594401801243c00085070010040d03070801510034a8031980c040c112000400082d041041500640110204d00c1005810b501 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 357252994 1250 357251744 357251777
    0x15010903110607020a0303031d031c09031b120e032103060402070b0a05250503071b020316060306060f051e070b07020d02010c081312050c010204090b10 67
    0x66045941149074071048080c4800450070074410428040c1d0030540c5400d0020030998517601120803110039690042d07040c0000c1c0301c1c2c980c80384184291104e10303000c03843c4608140941640160143d0307200782000c08505a1142c1002e014030b01424040e0b40c150b40162900000d00e41229110916020460290035040e40010a81c005a800f075082c5c40c2401c0004000626181c44a904440e150360b00407420f0301c0545865207120024103030484002100c681140100c2100703100301d640215801c00242c58850440c0c1d1540c4084800184071105100aa11a6a0000003688051101c41841803640382042460341c14510064180c42e86644440c04102045060400380d0354490f041e41e1155075048a0354001c41f800c1d80a40140d40035065010300711070080c000303100c115a0001200c0c209110650024040c1d8100300c0815591460b08030340c110b450454981c043e10024200070808001111582001824010490400ca00320307042a0850388e107041c0e803040d800410740382c001ca1003c07003c442440c0103085100319001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 357254244 1250 357252994 357253007
    0xc1207120c0f0308041410091101020307020a180f0207030c0b07091a030a09080406020708070504050f070c1a010807030b0a05040515042109051c0c0501050c0a0209011d1501 76
    0x40a001c12220201180801c6840911080786c4615071045403030003018100142d004100b110000c40c0e00c95007424201810354004000e0b502000e130014452140103141065605001c4205036590040c2a6102451801c0300c02610240401c0f0380250348a0301107000c03c1c0340c0b001c50030300003030705010a10214030700070007820900008005803d1061820039171243c5440540303501800d44103e00801d040300125000c511141e0005140c1c0486803000120341030f065494082c00122034040e00e500000044a4001801960203210700c4030941c1d00c100c8101c589a9240180c8491003c1e00b80c0000b0102d4110041c2001481042d904003608008040030801a50400e071307684c01d955000802660a1305c1100c40c0001c0c05003c410021001c40d080f0010040c0311b00d80740c010005081000c6401503900c03420010102110b030705099602035120070361042450400d0b608100c0190742540048001c4202031040c4140703c00140c40c1d04007054001c1004111480d00e140048030402a4480d000b482e11580c0003000c12540c01e00da07400b81 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 357255494 1250 357254244 357254273
    0x408121b0307182c0c0301060507030509012c04060e060d0605040c09020304030e210d080a151410020d2f010513020103110a050d0203060301020c1207120c 68
    0x1410412a000c5555401c410038040e03201c4101603aa6010381c110032910070000340180d00d02846107040030b685040d4001744034082801101d000900c10300c000000030380944010b01c03291105051180141200700306100130040e00010182d82500075151294003820a40201d2003c1e091490f03c060b1036141c901c021031002c03102c030800541034a071030340003140501a0104000c0060007040c10300707559a281506010b00803221045416020f1820400032074040f2260000c559021540d5501a251804903200300300c501c444041c10069071941e9601160b0440d0f00c860a16a0050090360b2100b0344c040e4403903041241e0f039254900f1800941d0024004038034041e03440500c01c14401001c888000d800c1c110000042014000b40420200c59845c100502c0841c8a60824aa119034400d81c0d05101ca044d44040c1080c0038000c0610f0304d000306909004148140c0c101c0c0d0040d5a008034082c1c001402c003000211032074601040c0e01043c070700d84080000e50000f07000455145201d024840e04004000a03415036801070380d448010f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 357256744 1250 357255494 357255497
    0x1104060c02061312030c120f02060f0a02040b0703020601050a1d13050109140a0210031a2211070b010902030c0f1605010606050c01230402010f050408060408121b0307 73
    0x10b6103000c1d9082e000e000802034521a41031035400513040c40c0141c50300844007410b9410748039070304480768104d03c100c4a500c1c41c840c0f141c0c0580010f880d102131140765140013520389810182c09204c08103600300072002070b2a00d02e000758020080c1354503010603c210007c0740d4002c190f25980d00400c0c00019030203403202075000502c4080c03940c840079031402c215005152418008141090b501245110080700262080b000b40c0201d860fa9040c0c0c0040c94140d04581181a000c0b10b000110044900103160295030001c00c10002e89a110620325002c0140c1c04a40892104400903100440c2040c180a420f2128902401c8134040440c5582010516412540500d25203081810030000c0c00d424420018511162400d51100c0284402038903864090826004850092401d601e07202c4440d0305050740c0d1040740c48001214440c030980c0e48480d001110641752400850b010711004001c00140c08004200f40b611560041429546818191851001022002d014025464010000d59004407080710440c0c0d00702a86 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 357257994 1250 357256744 357256747
    0xb0402040b071e02061201060305180c041814061603140f0408090a0608011502013e13060e030609070b0d06030b040602090907090807061d090a0c031104060c0206 71
    0x2c00c0c0454001c0f60001c40e0013500014041102410280d545035010b050319155181402950348500c5d003000c4081008160308131992041c00744588a090a500c03c0744408a118054007110060792581d2412004841800c00e20b5400750080105913100c07000000080803207031605200715400d510f0701c01340181c8040d001c0704c7c120203d1004101007003000c40407245440f402800000640b5032300c031030142021509104c0e03450244a12002c0d1004544103215030604810b00d041007190700002500079402c91a11a010a00d8243c0701003119031250099030042d012060782d16030031510071400d003040185102021031086002c1e42c0b02200348454660003040c0e0300c0580703005078252a1542102620b00300900265030000c1d09605c008014003050001680090040d52015100b4158a850703c0c3d1084404200c41c0c49200c186801413401404101d109201c2a48001010f000d401c801c1d461a10024400403019640d040070b0954480000c4000742d0140611940c48096508990030320b454034101401007080010300034401c800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 357259244 1250 357257994 357258023
    0x30a110a0819030f090b15040b1c03030b03060115021203071b05010b1806090c0a08070f03091a0603010c090b0403060b040e070e04050606030a2d1b03060b0402040b07 73
    0x484c2c2c0c4107003aa0b001c4403c050081030154140708503248001e46240355015010507110440b03081c0740c0514000004050840c0c21a080d81e4501400f90550f000412070806481e40e07199811a502041002d000c1c0c02d280c5120140c85102041c060301d00340001491008801d000d10822411681094002071402a9502e4040425034140340460040440c0d907812b56110880c10b405245c04000d040c48984951001d8a04202507101c80c610075001d405200d00300d000158406000440f0306100c0c40c0e5a9409681c20300707010940782c60a0f500e03903107400b03c0d03500718107503d2840340200130880c6000d003d500151110303820420307a982c3c100b010100551159000203001180c0b03c8140500c162203a9118800d0300b0741c000d040d608001d807500201c214145095606445920800c00803c01d186008030ba081d40c299440403001443d01c005c000026a0001c0c134420a469600042d0380c07800109600401014040d564010151440c42c2076161000071a100c43d0111401648180414040c600c4000201d5006d180c0020500c0010342c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 357260494 1250 357259244 357259247
    0x5012102121c0f18050a18060b120603101a0d290603070803040806220203121909030b0f040c0b0409090c0602010209130b21030a110a0819 61
    0xc1c181800c2c0b4901a2120208410180c0c011032542090109658005100d000021025206561350168030303840008031400700905030754909440000c20034100007284c0c00390b5811407282c0f160404001210740311050010400d8a21b400c1c00000d08141441d042081810405410800724540c401041c1c2e010310000d0807403031f0620070f40707441e8000040c2001412500b480e6603114004446181a11001d000384188000031500560100c140c509455142000382404d5580d10100c0302415001002e4265402030300c9029005602d007400b8a0700d4840c0c0b42070109507580360030901d0040302c50782010303c001040340d40c0c0b809100007140101603c1e003014404422083d0398845091406400a040c0d018462980c80041c0029008030f860b04800003150044000c0d1644a80d6036405900381e100d10010b030365001c65146012641104e0a500c0b206818402030320382080031992806000e03000c0b100501e90041e03648003044921a8641c4102021202a0710401a04d0340e6100b580d6688403d00526668030065420039449000d080d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 357261744 1250 357260494 357260503
    0x302060d18110f0604140f06040b191806140307170f010812030c1e090d080301080f0a03020307120212030406090b06031b01030203130605040c090501210212 69
    0x1109000002065016850704030852000345440070b010b1440f2080754420751800900359000c844420a00745220600c500802c05c02181800740ba07035015401380400302d1a500d0000140c407e1542011504030700c8010a00007038898901c40703074010020700c2940f5051058552205c2000b02190b0080e040740d0b1680c031070010a0302e428206400f000b651442d03900c00c002c080124041740904840171841503540c004400d11500204d807000b102c03c4070b446070040000300020a815041886210b4078039901506000a101c0003502c0320382c00310001d65001c4004001805660030602c09120445190750060042c2d0325160f80203910b034000c4440c0640b1406591500c04440f90080c068045414081c41d0695500d107814a0250010309107001e042d01d0120383c910003e00f46040015140361141303100703c0a05c0c9403841c26401180a540010076400b24000c6e071881d04000104240540382c040e91240383c24000e06400c0240880c1103d03c1640b21078101c2c1444c50210403000c01c6502c1d00c8020713a405031600c0e0700340a20304a840c0d01d003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 357262994 1250 357261744 357261761
    0x2702040914060708070807031b21020c010902130902101107030203120a0806030105010e1305010e030c010b010f05030606030109021605120a03060602030903030415110f1c180302060d 80
    0x40c0240403c0003d465808000648506000d0721070607590748400d00700b18100c400c0c903030151070102072070715031024a540504d2030410044510190504940840c222100c20380e00490400d220303984d12800305004510703000c81550005011224100705084080c3c00041014400361014824820440d100c041a40c8090113184095a005000c55046c1d800c1d4040a05040d405001d902000a036600d001c03400600d01805094102c5030819020b000039118101c9406030362410b010129603644d40d0f21042100c1d08001c0c80038009a41606000040083c6400005421100d541d9403070820404108200040c07640d400c02500d06450f0040701c01a00d4440d0346101c0440250010350141862040640309039000e4000d02c0101b501d041266814068550345803c140d0350781c05000580b60380740d001444284a000c500d60941840c008031860401d2001d00e5001c0708500305800d640789061a07070080c02100c541d1881d503441079800003078607281002008101488001205249001c0203210762800100c12403640d910fa00700810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 357264244 1250 357262994 357263033
    0x2a030723070507051507110103051012110117090303150f0d060f0608070608060d020a03020a060801061d13320a0506030a0302031803190803070327020409 68
    0x58039002800c14907034580013841154400d50130a50b50b110110215400d1340c00c0c1c0e55000c605400c01554000054020b800b004048901842161000040d0b51444400700d0211b0b501a0601072028501180010008180d540141c681101c6480a11080702d0001044950050801ca52000c4a013407481c006081248540400340d030040004212009001159120000c4459440001c0103030a555042d01e580701c1e1001d104020100300c414000480e0f44c1403c08103102502d2000300f040344600d40701d0f80014031120a40e00301400082242006205940d00000280030b100050003a0b001040c5590707000a181c032444003900101941c880301c101100710140b03038161021040b0304202900307154000c10b031510592800c4920a4899081001160440c200403d2a68110f509a170155140c2800b0384445010131001a10f155010310030500c140c0c1e0301040d42800c0010081c400c0900743e9403820070540040c00d07201d05000c001079480440c04066040c2401030104002c156064030040707848005070410103003004070400b00b0744 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 357265494 1250 357264244 357264247
    0x40f0501091505031b060903010213060c03020c09161805040c0201020c073f150501080c01020d02030a0e0604123c030e060c0a0501052a030723 63
    0x121080942c0180d40d45151048010a46a58400415594195403107140c1401c500402c01c5221030f0520000411000c440540003500d0147c920960301d80807296035005100081444110404040d03040c0245c0401d410100c0305040340d4200f0f103011600c49180d4510940510001c1c2c604e08070b2180c042d5280e203005101c018020440c0310f50000d00039001c0e43c048880a03c00380640c0c040400c5110400c032501102c4105145100003035601068182142d102803511007400f40002000c1d800050100e00300ba0111552000000c10170b0351410885902e080394001050303040d50070110842902c82d5000041d00e4124049242000244a101c4003146062240d03030400340e5110034011100c0c7c2401a408102860381c11148400101000e5241208240449036900c514a00c0041c6c80c034200440d21408a81c40032443c01807429140c00c2c6291503403440c00c1400c3c001210035035100c5080100000b0b40508602c91200c0001038410324480c14541e1010794070000344100c2c14821020104c00c4405010801e585545d406281c07601d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 357266744 1250 357265494 357265499
    0x302010e0f03010e160501091e060c1b0b07060b010e090610090302060d0c08090307050c04021e13050a1403030301030605090307120305061f0509010f031127090615030402040f0501 79
    0x145100c2c0024058031f40410503160300003a0b400c03500c80490040c2c0d291036400000d082d080c107508540f0351240e11002d484010094000302c7d46403020003000d900a24502560301e40c1c0300207501d40301c01541c5c125141c0034140300c6140c04078032507500d42210301980400c049400f0f07215200b03110015030b500780a41c1c1011f03401c2000031529071000c80c01b9901529540d03580d5107400700d4995403115119564442c000f0000c00503000300c2100d100c0c80c2007a8000e095201c801e43d90350068840c170624030149079009400082c86180100130200420f00f000418100a440c0c440b0030003442011300004603a50341b04c188001003203180c0c0c40002035000b14017030054480b41c1c1d03401100362a5000031040010090101605c44030700c01c40415201d80f5110214500c002111503050b2a1035040201c41401903c0c40600d031414141850f4491914001043c0c9200090124001c940c1c80703020860f24003000681c01c1e101c0301482c0c80c041c03c80f5505200360340d0781d1404e64031030780400800625078950b00c1d0f00c0814050480d00c0c255464007401c02001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 357267994 1250 357266744 357266773
    0x7121116080610050a031502070305270a0501031a0f0a03020d0c1e03031403130c064e020c100c021903050301121407031101080c040302010e0f03010e 66
    0xc0d54001c0711a04550f4241c162180204880141a4400181000340c060078400c02c1d098141c001e04041c6000741030260400001c03203c0f640700312603a50a02d01c00165180060f10183c90000d10340e42c0a82403e10702000a80c40140300030000e01d000e024190310030315009040c51040d640e20708542c0050340c0d000c0e064612441885c9450f1614220300d02400d41e03121003400700340703052010701a203036800c40e074043d607505c21010404040d040090340f0180c80000348110050a1030301007400412200d000708a16907403002d200b9030142c03103196141a4150300504e800b88900d24204000458500326141881c45140e071300307c2c04800c411040080c840c0b071103a0f1906000d80c004280d0102c810781d01c1299100360907001e0351040b040740f01c1451105020300d030004000c9001440140000c41c903102011a49034424242500c02035070f035440340c92420362140c2c400c5440d00381090300c003805547d02808041c0c0103210190b83c50f04060450380081d1a91200103069405000c105800c00d000c5d5400750401d10444120700240d1b955070140c1c107031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 357269244 1250 357267994 357268003
    0x40e0304031e02100f02030a0c1e03020f010b01054014010816080a0c0522142407080d0510080c060c280b07020601080d050712111608 59
    0x8040c0c1c800c203940ba02136010940140c03c00e0740429543c0c4c3c007661928a020b8815202900940420b640b42070300b400920101d070078108400f842c1e15002c1d400500b09407504904550070350b03244250035410004107002061403a440c10190031920041d0740112080c98840c4c0c030600c010600c101d5402c1c180e00b901448006224040e0350b141e126414000c0c1c2c0e80c0012940c0d12484040041400e040d9100058507074000507900603044e9010303040003841460200e2401c0c0c01805404005171000c100700c259250401000c20030f4559506140000d0302d020b69614460030612107520704522162852044011340020b010010400340e00700b00c491518821804000900303110781107104d625042d0151503558825203088405034540340307080d0f030070303440f03090700240800700c0441040614002558000324072034200192005c001441002114400c0c0c480e075000b007040750301d400c1200b8680001e403d09030b41401800c12008001c035a0340b482d030036a030040604000e20841916240140750114180741503000540c03403100412404400719 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 357270494 1250 357269244 357269303
    0x5010b031e060a050c0712030f142d04170f2209060b07020409021302071b120803061c021017010b0408060112050c0306010f15080c09040e030403 64
    0xc48529030f035080007480854405440c22040102d09008580004040c0140f21620800070700e8003241e0308507028006800d445000140064541d000000c010b00301300301d05252808900010011010f44601d40011203800e030002d000542445c215000c5503400c00d17007510868020303032042c150f0507564a012546600588954035094641c0003c03405000400f62694040c000568040000240c034041085c0d0030007004240c4004104d810100d410552042d14090344040c0c07135a03c0c0642a80034801500b40945050b0500701c1d044034580005039601034010030041800c0d00d911480c00e40701c200b000d842462000142c10300e42030000f940309690140048003680c0c070200e08240c089001400b680c1903600c80c021000345010b18082c450095001c18010410924051103408455002d039003912200c0c4502400b10382840400d0304102c4440c5030240701041486404038a4940c50481491300c0c600c54206076083e503901d0303c10030031064411500e0307100f6400c4041d4280200c80055070b00c08030700220300c14070b014030300c1c00c0040c0d00d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 357271744 1250 357270494 357270553
    0x9040c0f0b0315030c0f060d11072904050d03090201021501141e10140f0403060b0112020a0c1b090f0c02011419110702060d09060609060503030904050405010b03 71
    0x4010248490400040c1c110075845d0090a1a500d60001d00500845401c440d208500217500c80c00103e0711f00c44088001d00c80580220b000040f07020400c0441850740444032114801d0481e95401c04c00031071008188541e40e060280343c003083c001c00d50300040345806002c24005210742003000000481c0d42940040369040e10b030a5888190048050040b5501e41a42c001c0044c5c20803004a125140c142c0725a501079094441411070300d082c0307c0b1090701e10109800c240c0046030181e0b90b03607003d41c03510360300f02c118841c6440301501c0561400c000c0400081c801013840e01d0052051f100d1a228000600005130010050030740c4042c100923000107181d0020190000626213400340d4a41501001010f9003160818425145e0312201010880e41444c88001000506d0504800701c80910800300140c1c1c80030001d0204e440c0070788000c12181280e003009412900140c0c001164207103060020805500c000c0261152031504a400258039901c2e800d00501504070141e01681c54081e82c0d4120b05561540000000100c019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 357272994 1250 357271744 357271771
    0x3032e1805091b131104030503040e01061701140409020303090409030201090b0606210901020d06090c110c10053915010e2e0f090e070308070209040c0f0b03 69
    0x1445528a40311050825103504880d401340b50501c000c4894000d640c40d81c0200720701602d05aaa900e400e0b00b940c00c2500706050100b40c180040100783e50024400b01007000312007110491754540000c881041c030900c54460300403600e0f5208441556810300c2651130200d0050000d002e90825854024001d1042ca4811540d800101000c21042e06200c1c0c20380c0e035070081404c0b1001c415600700300500d41981004003064070542d003c202481d0403e08901841d401450b401c44081032202c540c00001d000d14a1305802c03511954407002500c0b05950f2442124400101142441540c0d08080c101d903c0d86c3c0110240c80340d10a80307110364003074165003003c0000721103180c440003078403010248840d804521120070b110300441e480c0386101040d00c000110b03403510035040540c80d0900030004100c140c2059060164045101c8410032041008404460300402030b1402525002d44801821940d0382d0100f8015060007a00854401e800601041003038124140a03048188c7d9019400da551040041164400c6034014011400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 357274244 1250 357272994 357273013
    0x1020702010923240a0e040c031419090203030c060402090a060e340207060e0d020607031803050f030307030e0604050d050d020904020408070806010803032e180509 72
    0x38008041d0710f801107405624504840c1c0b06080150108480c1965071084084041d82440082d03040f005001c107550381e841790320000300b05604100c2104d40c2e80d03140006040c1400a0761010200500d0740d5540150316212101001e42d0404c0000e004200ba0a002034040c480041c84425800d17000601600c9180708640e216429070700c6041c180305884052090400542021000c104d5102002502c0d0208030746400060007480b80b0940702120b41c2021820000258001c01c90034420302d079108241400c0c020f0309461031036034002c295003c0340c09481680005001c00481614590301c4d000452020f000a540003801c462000450011003901e0343c0c010340c0d03400d010a282007100c031001000070508038451078100d000b8002074043c0d46010303540c0303902a14031022900d50810813407190707540d80e04c0504094200d43c03006141c0d0300c1c140300415150210680250942e98418000c00c0070200d406050031a0100c940700506c46038282e1210420764445460300030101649a2002c0840c2c07000b46540800c1c854000b1408581d9050b2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 357275494 1250 357274244 357274259
    0x6080606121b060d0f09171e0f1201090501050916050a270602030408250312030b090f100b04050f1e0a0303050d060803180d110a08010207020109 64
    0x8405108940340c02a00307044040b001e49082c0701c000c540d0042c0100d4a00b40522140f5400ca480d00d4011080913550381e02c2c0c0c0418481002005000104103403903031407a2261080c024043d07403031000360743d582490b40021100700400d5802d007950048240c0102c84842961141c2c0000c000d00000d0162a02441c000000038500548a02d0408a0108180c8401c0e280181203d401ca48e80780e00003850000d58102d13580080700703c0100c101c0e110020207155016503141c904083e00075007031080c4614800e410381085c0851850b100100c2e1030076011294401071901401c0d50528064020b04190400568081e48030b9080000b000321010119104013007001082e00c0443d1680710001040c011800340f142c1040c008296200141899061501180d0310610f9040c5040040c20000d20010032540040380010310228042d820b0144e5401000c0103004100003941c00c24907501e140709001c0511100080c4521501c0c08140140012090799810030070003e0102c01e000e81c0c403082c0c0341c2c2c042c0d804034900304d00241c05000c0008505 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 357276744 1250 357275494 357275509
    0x903110115050a090b010c1401060303110307110105030a1b0f030e01110412060f020a17010609050d020409080c010c0f0908030f160804180606090b07030807051309060906080606 78
    0x102c8005003103003401c034201420080105000240d6a05105031050301001060001c65144980800903001240107420743c64020300c1c14400c802d020001c0d0b03005004d01c0b8001401407481500000d001e10300192a035a60300390f288045c00d1010b10340904585564204170605900c0808480041780a032000d202907038034160802d00329a001805801104400e100500100c3c00344a91981003e01404010601c090500c1c0b005c0c049a015045501c0401d050504140d0100c4004100500600300d504000000e2441d0401040702c210500c0802440345560b4000401007185a01c01d80e000d000703074900208440080c031107001c0c2c201d1034441000404141c6e10140000e081c50000110b45400c01030b1501c0e5401d000900764400280000c000d407c8950840c18440824148202810741c800c0b0742035600040b402501d40140541040321344e4101e5508007104101c403801085d0030030b40558004c4e41518040d40e03140b14140002c41904940d802c140300b41420100d001400d00003903080003040d85e10b4801a9a0b09440d03803020000c3c3c0c0e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 357277994 1250 357276744 357276749
    0x11401060513090c0e0310020703090e01060504062604050a05010509190f02060c1209100f020318150406090906053106030803180105060411120c0705010903110115 72
    0x100b010b06205200000c2c05410620013400b003800c1000301c480e000340000c0d09040c54107241e2151254045110002e01d903001070800020440301c80041c5495050210090951043c0d00403041070010701d000d81078004000000c101815041051030002c03604061600944a00022006540319030808000c81c80324840892031900c0d00c44924111092074045980d000f4030031150403810390b071201050025460511080c480058800360516003585d840d4003207003c2045209030f0540060422120711110440103400004035070130b0034500ea0020f00803400a40000d28126a00c91100e011043e001c40c0c00508070350040c1114003607916100e81440107031303252024002903005011f1a420a40070034402002d055418108204a14085500110700f050312600d4a0740c56503c1503540080d03000c51842d4284014400388030315900701c0c40803079044c401c5070700660740c402d4a03000d03a915211141d05007074089041d01400704111000f10740c0c003400034071181900b8200a00f9515540c0c004451030b50034510308510100314202003109 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 357279244 1250 357277994 357278017
    0x30302011e020c0a020f0604170307050d0201090209040303150902040803090102100c080f1009020f0403031101110904020a030207060c0c1b0501050706021804092a0302030604080c0a0b090114010605 87
    0x6003120b2170b408010603c07540c440c09a4106c2000c00021130780b10220302c0b4072503500c00e00c2d5004540d50307442440c14910301303485940c2e4403046914010340d1400680d40c14000700e410039094500810707009071844c514403400f002540003107005d510005001410040c08409003581d480c00344c0a680440b100c42c0d03c0741d401d461080162100013000d1000148a00042080c0c2c190048203102643d60b03800e468186510480c1d00060034032031f02040105082040681c809004d1050207900c000901820036030711070300300441c050f90480c184244e03000705540e40345500c40c2c1d041c2d50109400c00c2c1c0c1404414003014026086544400003518100c2c003407410019403500910150044403c180e50319498140c007500c50000a40102902e8440d007011424041101e40d560302030041440d002e206c201e000724142401c0c511803010030711103d03060b0403040c4400700003503500030422640c09038002d0300700c9130355a0f03902a0440c00c0841144004021202d904240a0b18250540c002c041c00141e100c40c000032662201720946689c050401c034000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 357280494 1250 357279244 357279253
    0xf15040c120e030c06011715101a0c0a031d090f0f06180609060109030807150506010c080f0304050313090204060806090402090a1d12031909150b0118030302011e020c 73
    0x20128a61003a02c00c01482403c2c2c07230381070a0b030007241c0030180003d40d061405c0001c04401801041855480009020350404051389000c01c000c0c1165110030171510064140190502c101182c10001e442c00c1c0b56201008004bc0e001d490f00c001d40c500c6e80841a01c80072440100c0d60000341d03041c10700c01109a00707400c889107425074950314101000040a402045507040082c005d60010003d910000549407061040425403e1004004025021100700409003410052112245408508840202c441114135410791030354035540c0381001480c612400404040b8041d68880010b80134600f43d001d001035819560b10310609448400403c41a601c081da40039620090240c040380001c1e00f664010714000301c8650002b0904100403020504000380f940c04060074202c00010005960061000e038076000e60710f00c05c100a690050784482400783d4910803c60078681d91000c04048a0380122045901d588103040710545094403860300a02070301c0d61103142030403280c3d5a215a0300070030080c002d6807242d190200041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 357281744 1250 357280494 357280499
    0x20c03070314070308040b03040209060118030602071a01170c0102121210090c020f06061c031202070c030c0513050411040b0103020702270702030a080f15040c120e030c0601 76
    0x2010002c03218544aa940c42040e00003c0090440320244c40100009035010380c69103058014007020140082c0914100701908500382c5091040c1c4034203200340ca0b0403500040c0ca0750240e00d4141d6072140b41c140d200825022200000902c0c0c1c0f040d0300d4040031702940c0c81c240d4100c1c003212001669a91904440740040c0340d814417800c04e41200340ca091660055003107186007510390782c80e220b000403103560340c0113000107811a9242440c0d00c00104026030300420f040d02d5040c1c00c001008010340f02c1510711400141003002c2e912079144102100d8054800710f6070010714050750b90f542c034030b01456915031b0351140c0c0313000d01c0440c02c030100c110046215a620540c0c01c950080d62507400002000001d040902c03015052560070b1000c040941c0300c003148210207500302c2c042e25845440340b08402142c01d0303001b0140000c542c801c10204480951021000d90842240018142641c07604101420002604c51040d1380044c035140040a801da44107a481c1c00c8404004800c001021100254940f42e100784d032035640c9580e1152004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 357282994 1250 357281744 357281753
    0x70c080d090f080c0f03040e0c131d041103010c020d051c050112020301060b0711010822030201060f1406070b06060c0703080c0d050c1c020f012a020c030703 69
    0x80c5120030240c0ca0009070725650303540c1c80040c2c24140d0000d468094000c281200540c0301003000c0a42250514006c505003490f0407050301c83d8030303401451084292808070b41c3d03102c0d038502051500003600030b0080756000842d0381001c2c000d02d507404803026214170803007600c0740d0094141803261a07170480303455020704802d0b5410001a50554409642d1201d040d011014083c030516040c41442d000e84090b03010400055000e004040c00c5d07850b03e1300400b2503080100141c40010b1900d0f03000c1c181c1410f0a0074a070055540b41d501110740000f44508600c40c0c0c500b03007080042050ba06501402c02d035915140c180c0c0740382d500c0358074011001d0801c5494a412041c03c1011001081c0c004800e154801001070040703151010f908402c034108103540d07008071652340c4081340000350224140201c00c460705007454007070b052528a40301c2680c0d955028000104e00b0b450b1403c2e41a50520901440780d80c0784403203000b40400048800106000000d81e08122403240b4850307091100c0f2440443c49203a9240300400504100741541c88 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 357284244 1250 357282994 357282997
    0x614060306041b08011505151309150b0a050703030510050d060e010e030406020d0f170a0b19120c0801020a0f140903070308040311030604030f110c04061418070c08 72
    0x161400900e00303c1c08001400003003401a460102000d6021003860380c03811051298000281e116400c4402d402e100c100602c003811103800c0d046401c1c81c0000700300c0d082c03001400c442e400241d401c54240700100194002e5070719000001003801130700c690750401c015900c415103105603003114080d141d44405030b2000c203008036980e03810a901e46c011a02c00000c0c0150114110f40c9142d00603030100c405600311040d04882c0c9074005200740c0b9644014100000c40c480d440c4290320b0050001881850b880e0f41d500c0286202d52244507240c941452026040c034140f0741c4449000215a2010800300e031b10740c48121000c0383c030100c10700982d00d0741d0380c89490b0310328154001d030019030f08010383c08810061300c6000c0c450000c55540420041c402940510f13903682c1d0742c60035401c2c0034184030100c1110324000d0f48514140000030354880100c2488110624100309400d0101d0809410040e040c008943c2c020b0410a0104804030b00c80300b0904020030840c1c224804a542c4180c1000074481100c408010400c40308840c00032031007210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 357285494 1250 357284244 357284273
    0x3020f0f041b1806020a05030909040609060905031c020f042610052203020c0103110d0515040b09040f030f11100f1802090103020d0f051504061406030604 68
    0xc1c004a4101c03480001080c5040d04210b50750002044400110f485600c3c1d000024080c2519102a110160160721000c0c0e0324422480c013a402807160400140c10701c02c982d8840c49240d98000c1084c040c04540342002662504417000b241941000d80d984500040d00c00e100315000c10152400441c01d0620340144c1101c2003015600142c00150144402d000244060040c0d102d07654031070400040380c0c00d000441c07284a0624816007840361040c00b0580c80031a80010f00c880320322409290200b002d0355101414060f500500000050003070400c1c0911260f000c0880c8902d0403600c2c2a00c0800410817080d0030098403a40a99015140420406416000c2881902d98816020b42e41c00d26801040590325064a4401c00354503c100b03207603880604403000c00450080700c5000c0003041314030360f40702d81a8000540d02801813100a00c258040c07a28201001407041800b0f0020342c00100b60f841407149040c045001850440c0e0881c4c2b124038040005c0d001c3e81080041c0c80c003980010300140629900c03682d03070380811110803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 357286744 1250 357285494 357285499
    0x801090b0d21020c220506061b06040512070c03060207032f1213050603150a0f060305011e0918290108070e04032007060c050c0a03020f0f 61
    0x49880000c90071038500044a80c80c9503111000405250034002c4c184801903068074840c00d000d8031145c5540e6007058614060030b946410000381900e80c075002891510a1a40242c2e400640b0b00311801e0000c00812050f11850003441550ae102003500c49280c40c0b8865000e000300f50103c100340c18008100c1079405440c00c0f0344a030505a101c42e00e4000c1d1000c0a0384002060190389030309d45003420380b81005003e8401c07568000b040742410f03c0c1d88100c00b10304045e22401114040d41e808000200b0807001a990000540c0c005801c2e104020340761100c00c044030181b40103110100e8240400040c0c0c1001c240425031000c80d015000024107814415004080c0c40300c0100c1000381201d400a407000f0880c0d0403801c040700c3c003034000c1c051007240340c400143d0300d1084140d004502941202d0790420200440c2c003d10b99102d6454a0068007480b403001c091075410300c10401500e40c6120710070011407055044071000700c440d4010400c0350b912620140400031072144500000390032613000c3c2680901414990815800318100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 357287994 1250 357286744 357286759
    0x33c0f060308160f08160614060303030a090c0b0703090602070b040e060405040303140a06060e04050121050f0304140f03010b030c0f0f0301050c03070f0804050703020d0317100510020705010801090b 87
    0x3e503142c2e01d0207500701c50000b946c074840f011110b030100132840c4182050708602200303524882c40c0c900c0000e502d07400300400d07180e6140d460301d030300c0400c100c50159104041c1003091501074580d91a4100100611a1401408094450b0200105548101d0410f490403528a0420280c00c2d40d548010700004d00005030045080c59118442807a511503034050203407003140075841c0003c50701c0c5400c03001013050390b4029100c0d006500d03240040c003038107401804d41c440c4007988101c0f040f001101442d041d45070402c10760b00105c82c0d000100300890142c0c414001101d89110442c1e20240d044c400104241c01c03a90906800d40e13065010076011000c40c10030b010500c0b080c0c84001c103c3c141613403540700801c1c01c0d2082140e00d00e003510400401c1162103600710000d40301ca000b69240c03203009440c06680d032940c3d40c406800701910400c5070a5412041501c5410421042807081002800780d0a009201c004000d01d40e0040c207110b01000d600541000d480028003001f01d800c141d480210f540d1820101000400001c2822038002e0320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 357289244 1250 357287994 357288023
    0x20301050117010b0a030c0e18060307171507020f0f0c1003051e06040b04020c24040b1f03020a0605030a1d070504110705030703050c071410033c0f06030816 69
    0x3aa480c0aa42107007050720310100078642b4800701800e00d9100e8020040003001040e640c6905d81002400e01c4038400200000b084070b8984c0b4000b6450560b180058001500ca040c04d80032100d04041186c101800303090352101e4015030101401d0702562421641c003404003440f0b011000f81d05400d0f08076035400901c0680009000061400845c0682c1d0084040803212307800a8000c01d04011620320522034481d80d004200c02c1750400c0c0d43d0346500000301500c3c21841001c2c10f1540c08040c3c80301c20f44140256401042c00313a145907200b1000c0c200e604101e0382001d016180105c5d50480590303100c0312a15952402d006040303c0d60038801080003e02c407904204113048024040c40001507810001408502e0181d100c058441109205007840c20302c558000006100c1c8140c0104d059454501c0100301c1c02c0490308021801c4504416000141203a02485680d64910f0848001c030380b001e1540c8410955188803000d104241c002041ca030103564540c84000c0044071b0030003400c40c4903841c8100004400384140c49070300c038540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 357290494 1250 357289244 357289249
    0x506011e0825050a0e0a03030f050315042c06070813080f04091b031406010c110901140f0306040503030402090c12160e0102011806020a0918020301050117010b0a030c0e 74
    0x1698180703002103500092000300e115042040b5a0803c00103c440411b0306003180c0d8010011a855280e107800c1c0302d00400881e072201040300300b40013615006441040000b0820984261000156040807018612030040701034a01c0041101d0788161140d0301d502c141d45d150a840740840d02c845010940741d201090015182000840b030007000100707684031010406600c502c00e8840051494103c800506107884400c6031182d402a13106039100c0b000f400e10040034910343c24194094100c08407401e521166000010a80f40b0712015131640001003070b140d5200603040700c818103540e20302c2920080c0440c1c0c0244006401031414210a9a01c040d544002034100200d001041451040030f490718548242c1c10414070032a25800005080c114000344024008061b208450740601041184040e02581d0005090700c011405896124010a0b43d82e02c1e16040842c000103403002504207000c2c1900141d9680c10301072001d160900020f040e5004058528039140804006038005e0a00c0c0408405210008120a2041c0e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 357291744 1250 357290494 357290551
    0x1c11120c2b0c090f0e1909020303030a0f1b1d03030405090702030702090a0b1c0203010b2206060806101d12010905100e0307030305040c0306021b010506011e08 70
    0x8981e90000400c6032104002e028105003856041984030506401d404c00208181003c400d0b04045e160388658040300c5500c043d14043c043c04000613425100010500c829010340d42e00c08400308000c803130708001041d0391020004d1501801491440080c410746d94004100c2140301e0820840c83c0e004080f689481da944021030540c5108990010142c0c0000c40c0080c15403c00c551b406a022003640400c214001c10600014150301c0042d80307600b025082d4180c4001107440961040304090b1005100c40300c20b141d40104485c04c92070003010005103030b08203003000440034011b00c0121300410000f0149030540d0304428007210104200203401c00c0b440380c2d46c400d00c00346032a02d051101d0055078400002c00d0700c1225003000c07031500e011804205032180ca17020409004c15008800d6076902545491702141c681c2b03960070a41840c94080d08083e0600740b000461540d802c5030750b44005049014030009200903035a2800644440c618420311040d098964030006000b03921555405500c11419802c0300c3c0f40d18035000144107034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 357292994 1250 357291744 357291817
    0xb0f1f03020910150c0b13021503130b0a0e0c06030402030c010c0804120b0a0e0604171b070803090a080303070e040504060e0105100504060b3a021c11120c 68
    0x1251758410004d0911942c0b818050f80810309503429981c071825540410004401c41000000c02d5002001244a03145200000742d401c80c2c00020032082408c00c000100d0042c200310900050a104446280446040c074001744d1b489250002c015002220001005407000d9880710390889000c1760402c000b09000b080c11078140301d01e600a003240c201615105520b60202e542131141f003885c0d903000300e04000000d600070b45031514501c0d40901d03ea0715a17801ca55040803404824200c504507000d00c0c0d00104a00034008080c05005004548034151070340c0d40d0b00c0306da84a1100b40d5a58000070412402a109424160130094005c2c4c4101d07030005507060445070503400c484044d0345143c840e4000d002d04119034070f01402a01c01800122494501c2c1083e05200d1810301e98129101d0040d20b00300844200300c4003009180380032000c1c42e0000c2556551001c4900c5001d1801c1e9809403102e841c5451544407038410301605030744c0c0b070042c10311200310316840d9921262160f400111120400d0180d80b820a0184480301244500c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 357294244 1250 357292994 357292997
    0x70212070e060109120f0321060b0c0d050a0c03031e02030a05040209010503010b01052514060702010c2615040e01050a0e010b0d0f0c0506070b0f1f0302091015 70
    0x405007010b2000402034445a408404488018006440815190144072034840d5150820640050080746101c1441c080110b0000c00e0700e00d400e000281207a004402044007400041c00e031020200b95800a0b221402501e207000f0000d00c000703a809001034000d81c0102c80d8600d01000395080d910b04201c0d070105a9004660034004207858806100441c140425a1400341c4011002400303484c282100003010f900460044080c2c0b890a24448004090590000141183c1140214280d0400103101583d0780c401500c54400540c0b85c826200c0b6094411400b0341020100780100e004019116815000c1808003c0d108215116091144403050b5a4502c6060500c019400011505103415400041100c4140c100d20300d20383d040220800c1e82d0303910011400d4006500c440c840e15066490b05080c0d0399103180350003e40d00b100000038404140640b40c071580348103102100602c1a16a50000300a031002c0c2c0543e089034014038000310510061800c0a10361343c0c0002d00d4421803000c1d5a039290340d00e0503100801960350 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 357295494 1250 357294244 357294269
    0x813060f06060c110307080a03030b060909010b030f01050d020d031805100906021009030801030b07050d0507033201140f0a0b0406300e01090f0501150602120a0507021207 75
    0xc014034070b0f0130382c0c6100608501a0520030315081e041a242c1d910088000c0c10560f580e00e680d0090340c0c0300340540c1c00040700a01040070640e1905040f03030041d4070684590075166441c200000f403501c0d10f840740160311903000d04a100341c500950380554058800300c91207020100c3c41034000c284c5864540341d80100d4201952141006460540b000e0309203803028501c07012583c00c0c0300d0403501090b04411100d045070751140d4000c00b583d481000480e9103000c1c03c0502c80e629800c00d810312900e150726800c10300b5580c1d484450b0341c004a00b41003801d6880440e42c40320b81511603814004214240b1840c0714118035184c050610b81140b00241c00040055205810202d130144001c24240300440d80401c14148071900e44400d080700c002c1078500310080909842c00d9062294840c00724806514003904581640e0360700201c1300c100503219280c003901800c0301c1008052040d284420004030180700140c140e000e5061250803516060300150102c515070300c008403d036009410108440c54a100030401d14004010118007007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 357296744 1250 357295494 357295517
    0x6030a18120f0201020c03071e0804030602030103230c010e0a0b040b0c01200409020307030f020d06050916080402090403171f090618090c1e050f0307060813060f0606 73
    0x19102c88034022900045a10600070345c3c0300c0c40d500204440410350000200c520804c131003204002074000c2c102c0000e049007004207001081240b540c0141d03042c2c0384141041711455500d40c0c0101e174040707803507143c0300390903406504070a03d594081d20641c66440302c05841140300581b6040c034094154001d0b44425248000002c070403490006c00c0c07240d2412840e42d60070320201100c41d00e100035240d01580c01a0380c002c07036001000c0391040d0300a9000c5280640c14620035503c462054111400030101c2d8480e4500440c03810b40040c0b0003080b100c1100495605c5915404e1103a1141d40900041d40801081241801f000c00141c3d04c030b031b00c0020031041c400e2100ca180d51001001f0300c50001980c0b0565880418214200031003440524450456140340c001c0040e000640343d541030a01c10024034140d03009038407000001c14443e00c0b0708068030781c18065035810b80d40100c8642601d01815a1b402d09485654001a2041e000ca4030303060844034100c01807809103101055182d070583e01041110403540c4030f1000300c6d5402082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 357297994 1250 357296744 357296747
    0x7030c050304082a0d0201020d030e031215040b0301111b0705030f0307051203060a0e061f09030c1d07120b06040e011716050d030207090906050f090c010e06030a1812 73
    0x140e081c042c4c8140c4d4841a406000d0f80041c0d03a9216008040c028141c0314002403005038420070548a080e1704d4800f11115500b00008800500c2c40d503681e2a500490502c0e08085803403c05024080c00e0070101c03615141352201501c5040c0c0ca12610106a0005010780e00d400106a074040207801a01c50000000c0d50b91201c903840c165103080907449040c0c1b0321400500800020b5031301d408110003154900b04e2400390310794540000036100b4400c0700c80b00c1c94a6500324150801c00b540003401805a92040450203640d50321914004110003c03c0380042481c142440007403201482840f41c3d41000742044401f1a000f0764040c00600700d03821a030440c20310840700c0f000401050810318005c40207200d0800242880c881c480e1840f10300d80c01e91303000d03d5014a580d4882441007601c2042004000c2c5801c9400b000756990030700d0001c003e010280e952020120204d008681141000304402003e01416151140803120710003d00c4039540004280b00d103040d5444203030032184040c40781c000076014840d001c61058a6a0000d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 357299244 1250 357297994 357298063
    0x906080f01090803060d11030604081317030a03020906040f030b0708010b07020a060f0908010f0c0e012a0206160b180c0a05090901020c030a050a0e041107030c05030408 74
    0xc8912242c2c100614100420b07000001c4075008202607414941d406000d0400e85025212001140c3e018441da500b00000d100504c400b03800018035641480702202d0b44c034104040c2d50854942c010750250401c200c48141303140290b008050399140070f007140342080d558805210040a06078010b41c3d5407050b0400b004141c650090466001d01165900c041c10152190045600c0585600442c1c05102e08440c848541030f000d0030540e002055081c00070701c0209452440c0e01c002e0000c405160b008a02907005211103503015000c409066500034619042080c4150020903a01c1050f10083e60400c00400418442c21401c54a1f281031600910b5900004d0400c81d60035411404080580d4810b03403c008041d04942e03546684440c104d81d0110b413404820345400840c107009100d03e08085103d032200040c644161500800039000301c041d2512540001007411080c8015100d00d040702404980c010800c200c001307401848036180b86409501120300307164950701f490f480d10b210b24033098208031108034200700e440039495 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 357300494 1250 357299244 357299263
    0x1030501200f0d1e020f070203302802010207030206152116030b0f070c0b06060a09151205150102070b03090f010c0c05010f0b060414010e030106090608 67
    0x81076545030001d0007401d007800740030310304040030300340e40790550030205080b100303440d03507814044890465030344003c000700f80342a0703112050890223401a15440c44442c0c10040305030700380280300144854481503d82004030183d21401e003101c030b220a400d203400780d000f8100c003060510440540006a803002c0608001c0d152480040c6811298502e540001c00d00d61a2645404820f032240c5500080a264264207141002d0b05200b41030107440d03801c1070020912640e409154050541801030301c1542e00e962000b15012041c688002c2d0000400c030010030a81c0c1805c1c0000d1030342c042c1e1464203810300740e2140e5100704ca5050043e106000242d03001c069032140ca4003880740d82c1d04180049580d01d42d1580010001c0e49415507407168011381e03040800001c00c4003c09110009801d88041c0003000009420131001e4003d850003801074a4542c688803603804440311a1180e030f090710800078032140c1010b05d86059094100440a0700c00d04010b000e00040d03006403024042d41380603181601002c14080d09003180176190980a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 357301744 1250 357300494 357300551
    0x4030605060406082112040515010e0c0301170a0b07030f0608010b1f1211031602160e0c0708040f03051204030305070803060604210201120908090d1a01030501 70
    0x4040008510005110040c3c00c40c200300420120b482100140d4180540d100d59280c501c183c02c104410000c0100c1c0300c1d105028270414030521a600c65604002804c0201e41d141102c40b41040188070003c01c104200d881900498204c5240001030703519052216000e4074400c0200c0d844180c145211203040c06414060600a0020801400309000081c8001c101d0b808000081c18a00307000c0a40e10304c40c254403034040400d40414803a18103071400700c00081d0b1044502c1c04080c4210491080c0c0d852010401e0760a500038864100308107800c00343c16440c0c0400107008017001d400104241d00000300328502400042040c4000108541e16608207141440100341c60840c252070200400d000180e002026216015004800c0b29200e5031801c001c90300c0c91285c1d0700519045007840301d21000f800151000000c000e4401c4e40c1e25049843c880f030509090b60b15840c8011b100c00310500007400b00e03050203455400035500480742c1e000c8c44030305460042400c640a80058a60b651034000304200309100709245480c10081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 357302994 1250 357301744 357301751
    0x30206040b01141302090103090212030304030207090207241d0f06090d0212090a03020d050a060e012906091009060f080c0406031e02180a0b2505160902040306050604 73
    0x2100006021004d11070411800f5a0380440c0c0f024190744a548944681d80d80900341c0610340b0f0640c0745656803900101d0702240180320340b101c04181243c141c0207803038070a98081c5003211004070b035607448484a00d42c04c1c1122140d5a51300140b22a9010034102e40d903221031100098010074000c0c64205041050061500c01641e010000b12072880380e0000c0c1ca5030000d6100c0c01c8040d01c135024070f03000444007004d03031b4030295100f0b42001102d010700c000070a80c00a41c0b13101d0b850030032014001c1c036411420303a40103e1031001a01040064100d06002050124401d2503006116619100c40100060444481d20284070300250602c0c50a21201d0380168030560300c0c0b4940e007040041d5181c03803451000c1e02e00c10340c00f86001301510b44004400c40341c4048030182440066010039900ea8680c04680500070144001c640e11815200900081080d218030490740c0c0c0c1d131140000d540801032501a90070814400c10340854840c0320700c0640708210004100c005d0040d00f014000903035203d2441c03d00d2419107034042c0100d0300c103a14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 357304244 1250 357302994 357303029
    0xc040c08040b0403020c0d12020607030608030414190b07031404030b15120d0201050907121a0907030501020a1805010f1205090c03030403080d0e0a08161707030206040b01 75
    0x10010581984141e110300d208030b5941e5545422810b00c0ca0074010030b9045594030740301c40100104070703600e9a140c20455013140d00c07568400204800b41c98841c410070b403060700100000d1140100035030b06130103100b902502c00d4161202c0c9520108004000394085110940046451000c241d440764401115009208466091608584074250003060183c1404007080420440c550581c441090710300301c01403114160381d40c81d000100042c0c080c01003100d0009441c05030500c00320743c140f41d0400c2038a05139003010b416604140c840e0782c541400c090242268500b84240100000002c0e4240000c0580c501c040d43c4100d00b00e0121002038030b000b402900414103112080c1160b180c0658000c2d62090f00c2c418100c00841d07940c95102d0f4907410900c4090101d40c050000040204c18490040010684241414070400000102d060450344900713940c0c00040020104100c10440a4202104e403507d9a009501900c1202ca8400c0c181c0c50741e50206001300c0240c1c105001b048203001400e02c55a0040c10124840c101d90300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 357305494 1250 357304244 357304247
    0x807050309101805030d0608060a060e1b040b1903050a02190c0624051503010510030f0b1c1703092d0604080c0f07150305151e01020c040c 61
    0x503000b401d06a4a65501d228801c640c10402c0107a040058001d82505c0d41e40007424803002c081c1c01117000f400500c0c07144c1d8012540302c0d501307445144116107059940211548900039403442184207451001c61a00c010300c404180c05203900002c1c1400301d605400351020403914480501541d42c002e081094079407052007141249600c801c4101080c03441c03443d000c240445145081c5000341100300c01148030001e408034401c3e0117203052984c0d4050303500c225194004402d0130620405907200900800c1c0e04180a1840400014040e8001240344080d0101c00b08a5015842c0801d59180c1000c4100413108410f04500080c4518108410b26103652444100c1c0785240c00324007a50f6a0a290b00d4154260382c030000c800030b08040740820b644101e84c0c0300055444508203410179182d0358000b0a10b8050701d0040e02d003c010007200001d0620120340100380084c0360900f0403401507000300700c004c0c0b81080e040c2300d8010000a607a503038004409030508503c2400c07603007201d4800092800c01500100e41c0118607011407581081e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 357306744 1250 357305494 357305503
    0x9120306130f02030109090506131707081905072f1e090f100f0806070c0813091e090803060f030f030325021606030c09080a080a0807050309 62
    0x84040da0100da9201c000c03150030000740000c030b62a040c401d10210011a5020300307908880340c9107000380700710b40c403a8562015850010b8140c92000780801c000c4a40c2401c13403000e6802404900e4000c0505500b40030342c086c0b1060894031701e041c800c0005800082e80d41d0404c05004940583ca215103c0e6222b00c6072008040d110840c6880071a0078454a24103400c03219030107460841e070554150141c407400150070040d64042e4101c200b5501d50125106044e40170075040c504078045003c8407081d2000f00001d8481d100203450310221800c0c2501c54280401c034203152440c1041a83c001003401c01800980c450800c3c0000000081010402c00040d041030104c1020940450030780390850b504542001c01d03000e044001901d090707646058103406001c040200b00c001720f64022002240b1954055881c0100c0c81c0c0700d070882e120316003105107101e40da8402d40240522071113607014501e1b10641d070401151258490303c1c1140b420400c04400c0b2032100000400c609015402a000c6404c4021414401c0c103600b004d01015854 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 357307994 1250 357306744 357306751
    0xc06090b13090203090106030609050706090503030c0a0f020a0302031b01020609030408060c0f04030f0809040c0302070209040303150825050904051b0a18091a060a210206040605040608091203 84
    0x703c0c0c010001c00c102c2c01082d484040259440700b4100655407542c501561108054450360010580700c031800102c0d07041c04822500302c0180f6002a05a2401964841040101c86a4180d03040aa04100440182c808200d45061103da04016040040660000a15001c401444d400e9160000c0c4010402901d00007401500800c3c07800200391504200811005240034a0740068a41050030b03081c001400001d42c01068844400c0c2e4007808a41c04002055040e44103520009400c907220b10000340109200e43d100003941013401150104180e5170700c000c0341c540111741683c81c0000040d000017240044142e46410300030401034509450600e0f140e03d5140c1c0b10003a0401640b004407111241c41d0055440807074200c0075000d01c14145850940c01c0e03801c08010140c246044468041001216056a50044800340315081c000c09001855081c0750001500c0003500050b10000741e070389942d81c4016580c100c040c001400c80e507030721941c4461915000030708848014000d11025040b8004000320380c0741003802c0b680d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 357309244 1250 357307994 357308009
    0x28020a0b060301020f0a08012c0f10050a0801141024020f0d0c0b06190911040b300103151d10050a0b010e03070e040215070c06090b13 59
    0x91641e20500402e02a100b0f00b42407660408000642142282d0086600c90603110440e2a0408019031012070706801655002203600020900c030001ea0100e6544d02c0d02640403016642c581c00b11569040803440030030075a08603c085075156010f50008000700706050f030f40301100340d403d00e044528220f0418070260000c0d06095039885519038002c0c115000300700750403441c0d21035011a070001c1002e090081c640b0300078a80484003203140c40b010808600d0a04944010307518818102000700e890920454002c01c1000105002c841d418040021415002d20281c044512400ba13181c0056542003004000205070754030300c0116003500e200502c0807502c40700c801c1e021201d001d880018001140824900020b001103000760151141400841c070b06c1c5030b280c0115000c0d04218106000c0180f0407401955840200d00300a605580096401c0104101c0600031a402070b00150003040c0c610078410075200140d1040c80c0a80e866003140301e00700b0105900000c070800034500c5000060800390207111199109102c1c0c440c148 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 357310494 1250 357309244 357309263
    0x604110c060f3718241a0901290304081908040822080607110d0c030509091506070f0c060c030e01030e030c251e0317040b040b28020a 59
    0x2d00341c0302c1c3e44868500750000143da44011000c80c4007807170914030b10b40c100301040c10040b40040070501054007101e00c0000070641403690382400c480c0c0360030a200902080a0b1400180d218101e00d500c08011401113008035600c40e40c0d001000714100b182d06500c142407042040c00780800002c590741d00309407294a004485000301040c103c40b650505500180c01682190040301c0900400a4211100b20341c410f5842d003c1e83c0b6030b1041160180d0352640c500c0006004a074041041e54040d1400964030b81d401003040880c181600c02460200ea901d400551080b5030038840070703030701000b8010305d08a403c0c01007219180c0741c0300c1c101c4030340c1e0000d20311a00c00410505154854016400020003801560070181d042801c0720401c408080300301024101c03603004008d0b60091070401056800d06d9209901000c5442e8401001907459550703a030140401000d6580c81c0c04400340800b1030482c010000600040c41401e102507280d0f82a0307502044c802c001c2c5c441c0c15920140740c10398218241c2d004240c89030340d00d8105040c1c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 357311744 1250 357310494 357310511
    0x50414100b09040f1a1921080408010606090810060b040b03090a0203060a0906111603050c010f02070c14010c020a060f0302070605090114090d080604110c060f37 71
    0x5004d800c0803502505500c0c24003100c440700140102d010205a203003115580700034a01c0c1b65010300304944501401100341c00500902c1d400c0c41c4040c0b140c45590380708941d02031900707030f450959508644480d040100021124407082001030020090401c0041e00d01c90108482440c10140392103500c08d81c440c07200003103004400a07070811400c0c854107140f40d802500392201d0746022440360b001002c244104407030a80c60021500214100744081e075803402c41002e501480c00d4070a407410384540e04405800faa07a0b40d2601c10700d02d0304450a002420826100c2d5020611035814585083c001c2920400c103d810400303084080c6d000360380e0340000c400881340c6074140390814070401e4801720082e1007030140103040d00b4101010721014003170552060741c01d03603203014440c400c035180c503c0c0301c07078450320303d0790b00c20000030b103150089420340c54561f0010440000300f00c2e0017031034203d0340c003e00c40c00e04138212291039490b448a810044e5403018031007030a1100600d803400040103485250b08090000190b000c040340c6680d141c449 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 357312994 1250 357311744 357311749
    0xf0312031b05031807030f020415080f0d0305060d122718110c060f130b04050c1e0901030627080307020c0f180402012601050414100b09 60
    0x14845440d2a03a8990700c5404440002501d40e5005513810460080c404008988440c00442c4483c1901c1c0d120804030034446154003040003402c0c4d5640049900403030480c0c0010740705e000f0041034021071a400f0182024940d1004058200d0b94000c1c400c90003006c2140b048130001d09580d80c00880500f0b2820714258000c00100224403110810b18501c0d001e4214400110321020b80f6810300c080c074903202c08280f140369080307402d0303280500035448412100e5008502103040c0021464a0355072000c0c2c3d0084001400500e034072503201d010815201030352250071940889609003400c861080644c81d15410161000b03941002040e0350107014480039050340d0340c40b0902211684c481c800d10b280030821aa101010004030308102c9016802902c9007009813203525030041550034500282683c14000605a648a072072503040b00c1850b0000500c100d04100500c4070a800e0481003101400415881000d03025241d81080306004c21246081103403000101c0100c20400c5282003400c030081078a14403d94113840d0183c0401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 357314244 1250 357312994 357313001
    0xf080403110a06020405270a0f1407050c0d181415210a060f1223070512010911060703030f181b050609010f180e041703010f031203 58
    0xc007481c50203046510014424290060415502c0440d01076207000f1041d545110300107011100d4500c0f4441c0741c00007540c809941c1d07110942c01d1b130f20044080360344008034a9446181c0e50448009022603804100e1a184110800000d05812940e0400b0010044404492060301c0c802d0301c104002801581038601c115101c581040481000c8140c1c0142c4541c840c0e000660314014068011414008010000f06e902c0c0e514042c01c812201e00c605000e203d075090540410000302c02c40401d40d0600e0101605120b000715042d100d80d24408400081c2110074140340800c64480c9041d42000c7d5540c1c14114044040f5020740710201c038816040b511030b80d8502c80703440c059018004200083c8065843d003481040505a50700840020607c940c0c65400180c5400b4030003210401e540c02100d4100c0c81c10f20400706c0650003032a859001007054205280c090030100c55881501560340c12070011600450184810064080003a201a00ca0000c100341158101680030742142110310025064200c08461034400d94002d60 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 357315494 1250 357314244 357314267
    0x2011d01031103040c03050609062a121602070902070c120c230405010603140406051003050708030d050f0906040305160812090705011106060906220b030606100f080403 74
    0x48143c072841d15041588641109110980c0d140c0902c1000408181e80481d80c10700c21903850147d548031040f4600c110580306d0120009007180c80042010000d0309403080019482680d42c526250344644940c6002420014140d00c149502070050080c3e01c0011035035007541c421b40b040c0b011002407035101800d051182e80515440310484401c07407503021068004a0082c0c51000d10241c40c20700071039a1b01c41e405c42c12200c1c001c10741f60001300410081030001d16103800c00e581109030f50f6080c004058a0f40c44050402c2d81940c40310190f40c0c0300207011402c2007424080c0302d41c418030210000c841c40c0750985501e070300c40320010030040810000042e4140c028034495420b000d400d4006803071944a04d1400c0e4030140c0380f80c065640e210940701c1c124000078958402d0300c0d08201c0c0c0401c80701030440c546548080c001102000303400907070301c0851601e000b14a8808038900a680600c409408501c00c5c66040c14507041840c05810107002d50401c203015031034180c20510204403222030780360858131503440341404c60310100c906 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 357316744 1250 357315494 357315521
    0x30209090a0605100c150e0f030f0301030506060a05060d0507050f0c06100b040b0a08130203030a21020a05220f1805010e2a04030c0603140703050402011d0103 70
    0x30107002101c07100d98418400e60720252044124607507072460540c1c4420031004000c14130044c2c58000f0403149920b8021001490030b2504980e10003030b50300b04a0342150008542d8180703c0b50040010414020308004540d000078041d1181c02d041400c140c040341403441011158a006900e40000c2501c4510810481c0d0032203811740344540c1c4035200c0107011074070365270b064842c01f042d01d0842001003100103984c01241c2c100c9103101e003074601c0e1104003541910070000003030103184111000f00d1190301580307040c00181f13120900783e0355aa44400504910305c0242e1040e4100ea4034a40c030502840003c19009401c0307900340345000300d00f6920640d0300c0c2045400800d80340c0100c0080c6131103640011740e110b50700c0d10360004030b122000c0c01c0c4016a00c3d010000415081158910b1340d285164010075501e403100480759410400c1e080b0810315240d10b9484005443d42d559011500181c0c1c0c0d07500010f10100100455600554645401e0003c1d082c80d800080855040d200500d254522000021145a00940c070448441024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 357317994 1250 357316744 357316759
    0xc0d020f040e0a0b0105030a0c140a02150c070503040b1803070603020406030e0a0c0501050a2604030e010201051315140114030f0a080f07031428030903120b01030209 73
    0x30503122603640c100d032050110109900000c207128950600a43c1c808040694805066585444c1c121019007003890180d401d000600c0d8900b101020440010501e040c801e80003842c40c245584015901c516005204d410b20000901641c40001c01c044211411194040001507e8800c4000b0b04040e0041007200c055140c85114030000c2c0740ca8140d0050000c0b07501545080265000d00300080b52100c00c8a440140405132048040c04598040c2000c4c2020103628a0300403800b444c550000781600811601d1640001006410442011b500c00c0c08401502402e1009000c0380c10451401490940700502c020041c000100c03100c1080080c50380600402c840d8410909441e5030744e0188411000d11408895000340681c0916024240d0006a0301c420030782c0c482c000600d41052440303a89100c0e001840704404009490441c5c3d076022403003101408a0020801c41c040200c54403040c940d5542e0009020741c000c0c14244548400840d420003800c1c03182041c911004600600c0e40740041b0700a12030b142465a00101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 357319244 1250 357317994 357318007
    0xc03070909090b010801050a022505010216030201050108120c0d0c060e010207030e040609050106090b070f2010030e030a0c0c03020d1401180f11030a0b0c0a090f030206120c0d02 78
    0x140c5861030303070407074494030001c210544415008c5800e1703115040801d821081c2c0c92040c80c5e0702ea0000c520482001c0e0103103000600301040440308000d01c2501000990040c2c0d15040140020300080c0820380344460300c210380c2c601d840e55030040c0d80d0729030900908400901207203941907014000d803500500401c04985000310f41d41d42c0240f03009800b0141200075a40158036152010441c0802441164103a620540726610010f21740381d0307800f80640c4854003c0314030141501c0110005540740c21400c040a4050070818000071a0764144402c1c1041043c000040505000089103081c9002c0219000c0c0c0e0407900e044541800036040c83d10140704103900094000c020556a5814090158107010f00031040390002c0c030001c802038580e000c00341144007003d4000400510720400180c0d0020410b02044e42c05807e861030ba8071940c40e180709030b440c2190714051107500000c8440106078415900c0c000b41810f0024540303000d0079034000c61110301803a2040300140194101198441d21000c060354141e80c00c40760150341e24070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 357320494 1250 357319244 357319253
    0x40e0f0708100b060403020303090607030507050106030c05040f1401060e010201140702030301080d0509030c090402130507020d0e09040f08220b0424080a02090409081317060f0c0307090909 83
    0x1000007406035800e403600c0f1020109190540854085039001001942030019102c104007195200b41d1044040c4a010002100043c0003070003100300640c00380c04a0050355262800344819183c52140941c0c11500d8080c0c10010340d040c2c6240141074070f000c1e14221080e1111400140c0c01880310000e00901b0030514402c01520550000c02035040e00d00300025102c62001664041e5290b000301e0000c260f0503000103008030f2490a000307004960060004002050300e0b005200c4003003c445041c1c03298070050b00041d10301848c15402241d03042c42e460054500d07640514194880e00e03039804002000500d182800140d0080240225000d030302d078016264418003000d5030324080d10351550300034401c41341a0392016100c111500a808050310302e1300e01940f03079410b4542d41c40e82c090009510021a2036031090b681c040130740200d11000040e05445003166240c90302281010108040c1080b450081d0003554010400c01c07510ad016114603d800175038805003d40c80c0d840d10790040c1c582054542101001ea89800081c50600c0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 357321744 1250 357320494 357320503
    0x902040e010507140f04050105030a0204170610080714061b0f030903010f06140f150406181a12070e090a140708090322050405180f0a030905040e0f0708 67
    0xf000e0036250082e9545030300707449072544c1c0511290103a0243c0140810852540a1001582e1041001038014039054441580828481d41401ca0b030b18203034401fa0411400041a0703004101805c0c44800414090b85010b00e202e0100c85030546590040b400070071802d80901140100c524040140e00540314000395091140343c0c0ca130071601c0700511075820450720848620380ac0c81688150b42c00c0d440051141e0441606100c940c02c1c0840c641900420403601016980d40030078054005080d043d5036a0511095401091400610b40c0e0421241940d94000990110200c003048401d58044a01d000d0842c0da540001604c24100546165070003001c0c85080107101400c2d544800c21240043e82d03031741256200c1002c1155103107030444011000d940204a04407510152250700341c040c1008100b8084515201c8020070150349007a161f01841031000790400044074014048500340319070160050103524026180201200f00501c41c0c0341c0a07903560b1442d031091000c1809401c20040501048480c61907079490b8440c1c0d01c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 357322994 1250 357321744 357321751
    0x140a0b040303080708070f080105061606180c23011d031f1d12071b03060c020f0d05030a052203020304170307120e030f010603050109150e070303030e010902040e0105 73
    0x15002c5c0002030b140500070058050401c0c01c65a400e14241e0038401400303510f60040324120402c000da10303102000669180118034103410000700b04041c0403550b00d0300d444044000e030480340c10300a94911031901030a0481c0100e00c078200c2403803c0c44200f120b00c0c41c0c0100140c565400b442e014002c030469004015100d2460021441040c5410012800315109544111a01e9050200560080d50031840000100e0002d031030000c1c0114101c8900c058594a0441030800c294400c0700c425444200e0081c80507014482059001c0c014400790102c10b0541c1c000405520006000d010619614004500360504c0400b0014420750301d2503c000d00c101d00d80c14040d5881c1c01a12030b0030740c98048a016966120000300a0380e10311a8441e0040140b640b107007808ad515000034200d190b03014440c2d600002482c000c02d004000007107008100004032030645003400e0900c682c81d000c6100032103042812500c0005400640c0c40b0480ba094a000079000240e8102103016201403d40070790b105c0d0402840585031501980300500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 357324244 1250 357322994 357322997
    0x3060615090503060f010e0a14340c03030c1116030210030902060f070f08040e09013c0605180105091302030d0c08040b0705010b01020f0c0a140a0b0403030807 70
    0x740c1c940c0c40042540c1c640c0100c81c1624104407080040000c40d80c2950400d41280d4521004038505070204018184480103c49800c03000c2d10a013680001c0000b8940190780c01c40040101d807030095844403016100440c5c1003070080070150b1324044030f044d00e40300300c02032680c10450800380e41101c03004058503903802600740000d0b0320038031001020b800b0041c001e201d40c051060340500f500c0e040c803454010041c0c860300039242c2500d0400b24440c5802c00076440100070405050405250403007814450422030840301d032000b215443e02028580700010381c070150f042c5010b241d4480302c210303490040c030162076010788416170089030454801c0810b161800460a4054180d603803e40e1265483d0b03441c01c400f0b5480000780740d0080d4041d089000c1d001501e0707100700440c540d900d000d0524035240035900c0344c16a405501030082661307165900c10301d041d40c669041c000155402c0800380104060260340c4000792200c19588510004600808040207041e100d00c8607210007040070420b0f1513110b035980e05000c0c00880045a5110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 357325494 1250 357324244 357324257
    0x17013302061501020601050d02150d0e0d030b01020d0c0b0702210705152505070f0f020f0108190c09030501020c010b15041212030e012408060f1f03060615 68
    0x2d040e0352000480c18126130b4000c00500034007a0075003d000d891100300c461480410001c1100b07018200c2140640e10032401c0513001444a01010070340101112103c2221a045400920503001d483d81c1c80103201c1d62243e0082103c900326100c0e90426803416401e40c81c0021100d044000c1a03000911000c09032080601841c280d0317100340345844840001c4a0103c4140005200301201940400c90003940c500008010342400352404d03407181c513a16044034800c5021942e1080d00c59641e01142400070420241581c00e003840965424140c0c40e195603081c02d440a0b13000c4540e9000d0002181c1c0c80b0303a10110056810000841d6100da0508146001c0c02c420500240140000200000e22694070f400311401c1399107401102e035100c2c400b90350b9000314140d0368103e0800c1588985610180c50b1081c808d0040203c81880b19403114038107403c003000b603a0306c540d00100309904803104000c031429007002950b0b031092408000c2c2c290b0445c2e04001c000080364a40010700001d1802c44045aa1014207400c81c02c4c421154980a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 357326744 1250 357325494 357325531
    0x9050f12040f060f090b0d05010f0503032106010201200d05010506071205090406091a030d02150a09080f0403030f03060b070206070b04060f09150b011701330206 71
    0x4005a10031071040e1030103002101d00c1005020f02c0340e13180000d40e003110310344400c541e0f5644000d5138458100701c80b0004603d544900401540710803206e040002c04056014505104a1600480404610498a551901c00c82000841c075a1003940704032468100c440207290050240700b50701c07a440e00035a502501e0f140c0f51400114503858020161210568040c0c1c2da8069610700d0402101c09030480d403041504141c035414085241c1c8614007441254a0b5502c903404484a02c0d141094034040805105000f55080426030710030b20081070600e203902c002c45003030110b4108802d10f04a0002d2042e0074120001d100d012401108159001011030074200c8136aa0a022064032140588150b1250000095011504000e0a030000c0d1040c4512907001c0d0040340700141702c1d502c50760725a00782c2d40c031043d044803481c07601880c0074085159031291440c211800c0ca0600e603950804605507400c44018043c1c3e0340c07c01d0101d1010013a45856041c0c4280c0d42600501c1d11130801842c1101a40c0e40307405843c0c4410200071984807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 357327994 1250 357326744 357326773
    0x2071a0f090a0609060f1b180605160804120b100b0306100e0f0a151b05030f07080706060e01210b070c0c0b0a0804022106010905130609050f 62
    0x1001e0003000c48801408001000390303100e034010b001c030003411200c1d56100c0400031242e1080c0e1042c3d268003507100e84d0503103c60503a404020070240340c200d0070b20b01032003101038140304d11944036055901034241d007103000a03c0c0c0464102010a4011544107241c5810100f035141c0400c0010441e2501405440d003601000030b0326603682d24503a0100701ca5854018272141100c242152081c1c2c2d400c0c1d50036034003070110601202814042192a0a01d8000850032420301410551107644051007060096860102208840b143e039625038882c410180c00345420800899a6030034014000201e0742920313840b15041042950f50001d907100c440c42440354000c0d4807451000550507080c404403804000fa03004a1807442540c98202c00d469070f411008099900c0c0c000044042003983c0318070010301100d00c05031204003d9203000d00c104400b170707190000302c1e101500e8111440c0801e07110001b10141500c4510350003062595910000c1d801401d401c15020b0401030500001c403040c0203000c29107141201d65101070700d0705038807644c45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 357329244 1250 357327994 357328021
    0x120309050f070e0601050a1806020f0c03160501050705100603050109150b030729040f2c0106080601030f050f04050c010509030718090b0c0409060f050f011107080102071a 75
    0xb20800084040001201176126030000c050060250608007540c2e101800c2e482030703021940d00040302680c41102008088441001905030700c0c50200c2c01000c508409401000d03580d00340703110b600d050250100d0000c0030403200348010607030b1152405040200644e87c0c04c20b10302909060500380c0c1c005901c0c1503811141c5100d401545895031015005104a0b840c0c210a880d4900702401090540501e030901008600581d500500080030f419000f6800c280c1003281e0400765170102081d940400c040d0480740100c0c5003075500001e0448480d810149801da44010060740030b0f0600c10f241c0c0901918203010480b0502080400d0b501030390142c81141c9040742ca0400542c3c1d01c0c031600440035410341c44200c0c10810400c0c5402c02c1031102001c070b200480d00c0022613803156291801500c000f00780050121341031140500390320070320b4000c000001d008038540c3d1401012442520200030158100401b0300c494081c162010802c40c001482041c000b10755403010740c24070161403140813030a101400d01210200c0c056417810306 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 357330494 1250 357329244 357329249
    0xe010e090609070905130213050a0f0317070f050f070905060307090f0905061311030610060806010e090108030d2301170c030706090306050a1406040e0703120309050f07 74
    0x10800e1400340c4540c410070030045030040c0210100204941c02007000e85481500900384c0c0782041001da107501402d500501011515006070340102c48210040001c2c6505460400840e50000c07840c04c890059a0744500c414071074084003504400c4010318417005c100c400550f18911a50303080c1a1482d003902c0b080340784140c50080c0d4000d07034141d006260600007102c181c0d04c95a81100400d100080a9195541e66800c00340100d5512030717410b48000a49007840740421500e01d0b43c00044018105618096400d842801c04038010399040004c8400003403c280d02602c0c141030382c800000c2c20040d8941c0e440e2002c036500d82c44a4280d5a100b402c06a000300d850181100c10f10f00661501018444c503820440014035651b07010f000c81402d4480d01d81030800c140c8082c0b15100151032a6071ba250340c620700714205a401d83c1c0c0080e0a20415a241c8014081c00060121201e604031404440c0410000000e20380d440c501352641d00301606484a07001304846050f0141c1c004882684103a0648091014543d0f50ba61603c0031072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 357331744 1250 357330494 357330499
    0x30c0311041818060509070602010203062b150b03070603020403020a0605030c0403060903050a140c06060111070b0309030307030e0318060f0712030903030e0c1c1e080a0e010e 77
    0x1800140001c41182900202420000c1000200d400c3d003411006144001d8000950342c065841052010038101403102c2805410a80000e5146003880070105030f01c0f4100311068610418040e22852010b102d42180f0b40720680c00c500c85810001a001420008060140b0b00320b00c01d102d111800a083c0b400b034000e403003c80303400401e441c514a01e84481501c1c260f000402e04c8480800421001c0005091440750000442c02650307026200c04009801400e81c140006000104507000d11054251520008800d030f0f005801780b81144c2d1002000020078500710302600400d03031108021003003100c5542c0000c069841042d1079a01440010076500c20320fa1a0310035510322001c010741e100c00c146100e0501c00000c2821500d04150140390491980700c40c40040c0c64280c50100090b2119020700c20b140d418000c42c540148000701404511a5080000d44a07048001042c84414950070145e000d04c03041d000782d144100c0079000084005031540c07820340c002d81d11811103940400c005101c804410b5104007274181d02a40702 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 357332994 1250 357331744 357331747
    0x27030f08160c080306060910031e0e0309010e031606021c0305041502030c160f20060a03050901020c0607081006020d0f120609020a05040e0a0b010f080a2a030c0311 72
    0x50742c841c420141d1008200c80d40149041204217920784900444040d008a00c0e42c9c0000c1300c81b8540511003e044c694501d1035200b034140485c1020307212003c412a9000c078402d0810b81c3c482440c1201003400c1442056108140002c00713240002e03c42e401249040c00d80e0b1071184a00184c840c052001d90403034600350f9024042c00c003c540b00d40380c021181c0c0d0003582c00680807030300c540c180802420401c4642c4040102122a8200e110b455030401c8180001030725090050000d80e520507100001240b030318024115900109030b1620301117148a0000c3d030407604417944841c191086490036104c0075060403000d8903011510440701c00002582840424680f0389884140c0e111900c01c0e011500c2161004e085600050441355922800500318105200426001e071075500c5094803186011014041040300802400c0c60314180050300c1031030b130380c00082101c0d00d00c0182007900c441d44890020900514a00010700703c0c01020b08d0496110040e144409010560542d4042c081d0280d40c80c000c40580304510500c0101b500d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 357334244 1250 357332994 357333017
    0x20a030b0603040b0f13022d0a03080a0c0212030703020d0f050307090e0403051b061008031206010507080c07030f020a0504090c0e070315150f090e060427030f0816 72
    0xc0003400c168000c02c100d420703030100c121a500003c2c0c030120f40c01d1424161605803072101c503184d60351350306030b43c2c1902049a003071402c4c034032b551240304080c495941c2010400100360500002c55885050007113043d410441120340320072080c90007070340d074001452050380031400e480030403440c50340302c0c50403280b03d107641d07aa0b00c1000601c9c00e100d00c807024078041d0040f8240003080c080c0040e000da484512000c40c0384030400401c2181020201c4c1004007406402c8000103030020840b03501c000c1c4c51503d91517000a002e10f400307079503502c140c1032002e120300845018654034040c2200000901c03040c401c02a004034004c13105180d0f25981d07a8108812244a144010090701c0b2559041140001090340c0799800502410041840a01a01420000c0003c0d4020b15104030f014045040115404600d201600b03231a8202200c0142c00c00d84200b00780c082c005c1146c0d01c03544d112041d42d80740342401c0c800c400c80105001c03035128040d945498040c042584200d120b0b40081d41d071b000000c03407000011078800005105078480c64920107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 357335494 1250 357334244 357334261
    0x90a08030a02070b0f01050114120c210c030402010806181603060503010c0206010f090e190309030605041104050705090d0620070c03060609060b0a050c010f050109020a030b0603040b 80
    0x30001000046269400e01002010505003030091303115201d440c82800c0c485d810b00e0000760143e03110140001902c2300501c031040d00e551340544e1203500f10481070b03e01ca0b03c1d80390000300661540202c2006e200070250010903c121980c10300003650040703200362038482d03480d5504400c1c821581a030b049403104400c2181e01203070148a41a40b0035100e07440e00d203008540c3c29207030350100f03081d280c0c20510500143c0c80540104034030795003000070002504407024140321050302e002c00d40d82e94107034111410f807001c40d00384244000c0500441880b8000d681c84201407010703103024185810040b0f9200c00315070113142040002031009100340d045420b120001070858040b4840b58686000510742c9030240c0304804001e580b0321008c90301c101702416010303110380380110b4042d0443c9018019500164010903080341810f01c00d1100b03403d18410340f0313018002403034000c0e29604c011854030301505440d4250303c0c181c0d10340030001c01e01612903002070840b01602d40b41030001d2a444020300003184811500513150108980c0401c5184 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 357336744 1250 357335494 357335497
    0xa0e0f0d03020336130f3602090106081f090c021c0207120c030b0c07031706090a1e0e0c030c2e0c05010507050703110a0215130b0414090609090a08 65
    0x240c551100c00600c0b006d400031044100c40251600d18a151201d541c1e005103603141c4610001c168804070000c100020142d400300c4c000080601600c018018018009400342001c0c9102210004012450084080d55451040000d0014002e00030050141101280f910009002d68241c07008075070b8028150380f85004105c22079115408011211040d050074000049040709044600880308410195640c0c54a071602420031500b80d000414188011010041c480d501c40d00ba90394810520f40c0e000c1440007490040301c0c02c030281130048008091801c0340007640300d0400100760401d100c094044a043c000e140007004000d0628040810220802c0319401c80455486a0f01c00d81400e0701c1d0402806455590340c51781d00352201103038041d00046000c140d000030b041d40005480410301d003880160000b4103075074001c1100c0c5420000300c00884007000808200d01c11202482070000d0482d41944e940300c85d11525610001d0445194480c460043e027008980030780b4104030914091400714000340750b005010794400700c05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 357337994 1250 357336744 357336769
    0x14070302101808030c1b0a0c090504231606030209030322080703030e030106050906060316090f12150b030d1d09010308070201110d02030a0e0f0d03020336 68
    0x1040d01c04640e0340c001441100958003071824469141e03100c480d014214100031446c41c0c6000081e9020800f41d001041741500c184e416a8900c44001c60540c0e101c0c14041840000702d0104c40c081403003404a101109000305026075000c046000d901551a40d540044090303010b001c400f140c0c19041080140701c918403183e11036161161201c0e030301c210301c3d5807421054140215544260049190038407520343c0382c6421310504014100481308a4040c0c10002d0100d000d5000003080090100380d5884c1030342d00e083c0200a082e0007091090850404107865500f65045214200c10032507401c007458441e21800309884c001c05400c644040d0062a00c010002001c844030503111034a0411803400d552800d500c0c3d282e45024502035401080e42603960ba00d50b100042550f4424129684e0b9500021201001d080e8040212048200d0621f0800c0d4111026400a8188102072500d544d01000b10f10f820b000f0140c001c400303002f500e07166054009066082d405550040200030844001c0c0c55a25003040240f407500c114170400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 357339244 1250 357337994 357338021
    0xd0906080912030c1e030103031b0c0f08150919080304061e0b090708070509060a0e0d11031b01050a11030903070b1c091124070c061407030210 63
    0xb94200a2950990964015202042c0a030b100250101121592246500340c0e4072190080c14503662454030000c02a51148804409484500e040305d01030044044101c4054058903030380c00407583c0d0703512856984401150740c461400b80356a0009100c41c00200741c044a44a076a03c01a0b85007403180e4541001c1c1d44000e00840346180d455003803401c50446903203500d02030034014900144007020301d002c21035664002011603080011000c00c00c0f61003544107040d038000001c1540d00e03684510803c401505c4100c210945030303411144158500040c44803200700d10b07c1550003641518048544101e00c03014080000503114046a030400c124010684500b4442841d0302c0c4140c140d900300340710a0b00182c1408901d81c00801e0340d10300400c05014007240b08140c1060401d001c20704006001c0c2941c3e03142003107801c10282c944a5003000c460880405501a600b003610400400c000d0340c0d078001850003280c00e200764007540000801c101510700100d0200001c035898581c140d0000e09907403000591100260600300c40104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 357340494 1250 357339244 357339253
    0xb060403020303040302041122030b150121090602030c090406150f080a1e0e06060a1206020306180f0f0c0a08040204050c090a03060509010507020307020a0b090607080a08090c01020d09060809 84
    0x180000c0100d420402903105100c1924910304141c0d2801d00003a04181e04207018280250f07c0c0d8ec2c1141480b05a0744001c80604024601030b0181c0b8014252910040c091300e00000821031107004c0703103000305801c1a04a6040040d1a02c500c140418001509030000224481c541c05119140c0076240351544800c001d00e000c00c0840c40c400754005151804200308a60300c2c4c0343d071210020000d090181c6d9034068419038503100b01c0c3d803400e0401c2c1ca0700e495083e80030344460350000116945841e005290b002c60110a410710b0014102a00d0580031035001f200c00718614940308001c201030819040031a2440d201d076036100b45442d102c5808010060901910805c601401001000d040b13440d0403500700c0080d4024000000e50b80360910703007e42511070081124003117400400001c40140e54600c0a0f40c281e078054658144c4840c0c1c190f002ca806842043d0001e09600c0c00802d003032100743c0c0d10108041c0b24240c01401e07655103107090b5005980c0c40c0e20710007040002c2049490300b40021071050721000d602200090449 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 357341744 1250 357340494 357340507
    0x10501171f030f030e0f0112090501060509090f0105150906040b030f0118111519090506190f031b0507050c060a020a0c061d09090a0c15030b0604030203030403020411 73
    0x84408401d95031040300c008583c0d0310b01406140d040131384107010362800d41e034030703d410907900700007e02c180256800207000d030750b8a04e13000007444000d60168002d0000904801100c1c00e0ac00091030b0b4a940606c00307149698280000904103110001c06005440400780920590351a8081013002411006034001d8251140b86000a0382c11703001d005440781c002010050201040c01814030000c1050700344445409526005c00058502d80d000040b1001200d0082e0f104a031481c903658111140134099000c250f10660108115252032691592400e80d041d0300e880b80482c2c210580c00980030b4501a03560440300c0000711500030340490180d001401c0182c4a001a1640e400d410700c001a40d90b0041026180181d0064075411b04008001c120301d000307085a821310001442c0c2d4009600060044400e1a9010700c03520030100d4030b0040c040000c0f00c500c030713030081c106d000203511407102941c0b88101c0101000040e08140d44442c207070415034111400d81e6009000b075494581181c090001070500313580c1002c800d000030084c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 357342994 1250 357341744 357341791
    0x20c0102130608160e030a0602090a0f03150f09021e0114040f05040e0f48010306060e0105070b040206040803030108010b01020c04020316080901020d0213030c080601050117 76
    0x210002e072600d07884110b002d0030042c01c400c10980c0c902c5400010700c00c0d24180303403150760740004903080b005a0000016950b420384001160355010980e01105001d0302d40b000c080100310b5022a0141c541814481c00c0000e88406c07a0580309680d00114040d4210105070340d403080440142504088000040c1000e0b00c0c01c02026403840c80760781c0240d105852003000f0700c03018441d038507050190500701030419005052000d01c4940054941c105964a5240c800000e101d110501c114140d0070180d241c450708102c40a02821184000d80e1801469502c1c002480c086000c1a00e40c041c010170f403a68141a5501801e0280f555911400c0d0003002c1e00c00d0b64040e8042c0b100007207545040005502a0580000224509464070001f926150315035a0440c4200e0040c001c100f110300b0a1011800b001ca101e00d000d044588a541c0030300e009109000302981e0550000654000300b41d0100c01c110300701c034030804410516581c0c0365411601c8450a00403030f400a1414824200c5d03002002d0b01c5d00d500701d00040c803050452024400b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 357344244 1250 357342994 357343027
    0xe0304060e03101e020705150415050f190e0f1915090b0f073b18060118090f0606080f010f090207110a03030206101d010504020c0102 59
    0x403015081007640c2d0a0900c500382014000d500c0c00d0109103203851038000c010341041409a00d482d0301003902010f002081000d159505d00d821291041401c0038141600b5005c181c035080e001d420700b842d0204002e1710b131038440544103005001442c2c040c502d98400090150996900c2c40c18a4850346000071030b007140c1481117144c200c802c605020361800c6680303041c040c03001d055a80c07020384910304410400410491720109d41d20100c8004c000a85590b00702c82901c03918030b1511090200b0095401c0319680c0b1400212400480d40c010382c148440040c0c3c1070412a0383c15800100740c0441c90740300c0201d04a9401100304400001d1034141c1076490315141c401c2501100d40c5041c4174004252210410082c1981240609802454902074207020798107000702d0340300c170003020300c55401120f0340003c0010034010b4645c001502400003e100000f030690f41d0a0080d640c1500f952050451405418000b0754210039205122400d00742c04141d6805e81e00c0d10341008001c0d08102e40c02c141c1e9540800c0104461700241c071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 357345494 1250 357344244 357344249
    0x110a020303010609080303060d020d0303140a0507032d0b060403060e1e0d020c012f0309030c0904050a1e082b1e050603010608060702012a080604050a0e0304 69
    0x140119101c2d80740c01c0c2c0007410705455a0010169070420424011140c503403540700c1d17600980646140b00307003481c40e01d0110000c1400403d104040080501840402102034200e14013503080d59805119006d1002c4000501510920b0901d100013200704405050a61542210422000041c40142007558039102c1c1410744440c1687c200c4540c101a070741210410110f1040040c81001c4c00c014006025058000b030f5071040b14491541c1449410a11900c1205648040d880110000d00300018034540549400d86c1d01c0d080419078510a003e622204902c0d41010800180316035000002407a03103059940310300303100f0784820188850300740c1c081304050080340a0100501c1b1094650411600c585d210300b50441240e54500001c82425091100c8a02c200000040004042805840008090303d0740c0c00001d005104a5001002c41c0c02030341e080107a042d4043d803001050f451003000801050740544120140c42c0410000c8030046425400440e140341415400240c2c090b4103444e0000c1c0e2080d401051514582069 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 357346744 1250 357345494 357345497
    0x120402041e0213060908060403140d06090504200312030403030f240e070e120c09040c06140403240e0601080a03030e0c01081605120c0405100207030206031801110a 72
    0x1950183c02d000c191901008048501d8855522820444015114900504040e04020191280684240c0f01c1c0007120345043d03940404110440c0e50f607202d0f5005e01821078003a01c81c0001c1d0003040e210180c000c1310b480411f0800401401019101d89880d0b02c4507000508140c040503070700c0002e070288985510603803481c940d032408502807168002402c0c41c001400b503040319000030358240c2401211a001000780b00500800c461580003051618401845c00d14800c01072580141070805000032f00000b103404600303481442c0d03030b0400c603410f54044102e0584260300c00184005d22055007601c040900d480c4950074114031881c04901640c4040140e45000e400307030002006900980039031410580c05205d8117844a40060240080760305940c0082c140c100000d202c00080760b5034100307040280e4443c9007200c0520a0351400800d003410010b41084040e005030045500840400c1500032a89000154030011654000c0c0824a550380d40b03500f60000400001d0030101d10f6480d5a401058108200040c009100b4207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 357347994 1250 357346744 357346747
    0xb0a061d150f100c02010212120106080a0c0509040f0f09050c0301150e01060819020a351f05060f03040506060d11210109150507030c05120402041e02 66
    0x1c202850298928a5141840380e00c0341c0d401d211a90302c5600f5011083c0b02036040004d203040c5140010b0741889055111411059000104111174166800700181a10045e17503662615590b440345c0c4800310307020001e40c10041141400903601e54541030f04006082010300b80040741180011084030142c48918074200d8070760b00112902c1a0340d00302407040b000401d602c0240c0e1881c142c5486240e4000d0a81030107800300300600f0b0710020b224100c0245940c14008048001199541e401e91001000381c1c0c40d900720a0101c10f659031a919581040114510302110700400c0c02c80b10384c0751101081948604840583d10142007004001860384e28040030381003001000c0443d40d924a07082c6051828030900900f450300c0307401c2e00c5540e030000c1100c460440c50381d51070035154411039158090600309085501c5202865542c20715a21508001240004880741009103100b402503480d000b0301076003a01c1440d1100c40000c0e0090211040b1284002c545a8003c2e0003c1c10000b051900d00301001c40003184510305d4a01f1580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 357349244 1250 357347994 357348001
    0xc07060201150515030408070804080a0203062d1906090504140d120b0303070c261b0d140102070f0c1406120714040807081203090a0b0a061d 62
    0x80a001d80040840c1c1903900c044110f04110029980c07038840340720318103c01000300014081000b080100d92941c1c0e08549443d032110396a00b0020356510400804034040e004500200340341c031004812075102030341101c040702c40010030328107000030540d8014075910320a00114556003010380144201c0010b42040c01c0c002c0380c14a01400c09907100c5405250314400d0380e20070140070041981c03124100007094801304001c69913900c0c520001c3e28500550380064640031070580000f9483d03c404001d905003006a00c80340042d40c4031080c4080d201c0e000d000e5031190181c1381c0b6908444078075144a003940051702c1140304907a4070020310000740c00c80c0c10240e0100c800080c0c0c41c03003240c1880080000d44000b02512105045100c2880c0f0104409024241140140040c48000304907018028420b001d8009502d40c410798655548400300c903901c10300d0744100151b6000340d001c0d800e58440c00d10102c910603948440105010002c9a0311200315a10007042d00091555402010800c40b0818032854070b07070030200c0365441030307400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 357350494 1250 357349244 357349247
    0x503060603070317030c0d050a05040506090a02100e0307030b011401022b030203090c040504030e04060e160c0302030c010c0e040c0305040f02090a0b120d0e0303030c040902030a020f0c0706 83
    0x201605541c400d5001c61000c200089a441600003d900201c452545030385a185c01c80095008040c4407a001c14140002c00c08100c90544c00944202d0103501110324a4a481480d40c0e100c240c18240a50000e01e1100c02c401c8141c000c44540300c440002400722142c2c00c0d81c1c0c0d25201269207081c0c014070171002e0f2210043c6100c0da03040107215910858000010405a100100110702d200945007900078183c020000458202050180e0b440b030a4001c0c10920080c642854010007003110702c0381403445540381107800f01c3c06d20103170804c0e00d00c1182e22880000694040c00703070640702c08941c11401c07002c40c8420001c85011160178056200c1c00401030b02c94810815194007000292a201160b80d400c0510f00790800c004919601c0500b40856015202040180c030340c1c40506019100a10609400036213864441e2524a00050000c541c94074503941d030020040c8143c101522848250341010208109000a02010000b5402143c10111038040107203085070800c00040f00713810a152820305900020010060319 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 357351744 1250 357350494 357350503
    0x3270a0c0605030c0409090201050702270c07030e09100302031e0618100e070801060f05040e030301030506040809010e0a150e0319060b040b040e0d020d030212010909020d060f02040503 81
    0x900081c28010f0440c94100d20480d4240524441c10070742d01d464160003410359004074102c90a20343c0141c4250920300005000c92000c0000d040c413881c032503101d440001c8183c4004400e50300c0055040d500e20030344001141c10400981c0010386003c0f50b110380418000700595003000245000100070000304c2c90601020350403400d2510080001120741e031180a411003500000c0ba008080f0400c04400103425950303400070070b00e050020b0704494203540c80c0c4030001c194062a026464101d5000715000e008038540c4401c1e01d03440780800e11000380b146d03110340c0100300002c00c890b0103060681d6042c909a42c41c265468005030001c01264850116880024024501ca0b40c2c480c00301c100a8905500601907a101c0c0d4035000010300c00d100c8040e15040d0364050555541d910754000b40801c0800030b005000703105103000425200c000d041c280c0b80241c0328030785540341650700900030b684601180028004c2260701e801900030107054080f404a900c0b04a01c5030392000994148101c04070b4565440c030040e100c609280a0500d00b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 357352994 1250 357351744 357351749
    0xb0423010504030b040f0303090803010b0c010b0a0302010e1216180509010c02120a030e01110a08100f05310203090f030f04140a0b0c0a02270c03270a0c 67
    0x400504100510111385851000c607002640310088201040c1e0608040b4010702411000415099002000045240c2000060400c0c0ba188000800a40381c01c10f0400040365890721000303012529012615a091a001e80341525128440b4156a422000e01d0030720100c41c280c0c0d401c071902aa0848035a8095600c4900c00e0603805a807a1008001007810484040e543d0f2517907200e4991044000551004020b1107600141040b00441c002070000c1000920301d480c043e00054030810000740310780d00003410708141d10180c000301c1e140c0c40300d0008440d0500040c0b260103691002c455800c0c01e04140c0004c4c178050303125030246044542d50001602c0f4140002d00c0303828000000c030203d4003030b40180150000b004400c005c071000c03a5145401d0100b030050301404030751800c002e50b010300c840c040007003180c0090140214100c0c4d0710078405c440c0c18200f41464009000c041078000001d5021480c500c00182004844900864028580c00e40f0036000c280142058a001e50420442e2441a08000f294401700054040c50030701 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 357354244 1250 357352994 357352997
    0x2070611070f0803060105040e010b040302100f12090c050d03030f0c0e03030315041103010e01060f08090c0d05030f07080d050c0f0d0902010903020a0b0c0607030b1503060a0b042301 80
    0x3070050076889450560201110107401058000041030090707000e14103c40080c1b2245040810560f03403204591307826000b610003a0f000385000282c00c0d00d5184210048840034950b621600745110b10f4003603110081c14410f00484a44940c00404035642e0394048401482c00c0c4070f44d0300403070303c40082440d5034103450028210005000071701141000d20790b0301100b40c03079000d480b91842c80c601884042c0010040e10300c94581c241240d10000010401036509520035058500645850300c58000b1003e08640c648000c548485107034214a611030003610300180782030083e9006000301d1381440321031106448240d1103d1011105c0400020300054895007601a00c0e41c0b100891705141d0401103509030010740740c410514080d080d10b65403e501411a80504400e40195030007605401980340c5076070440041e9800300220301b68500c102800500a80d00c280558180404050541484c806002040c40e00d00e07040500129845106018080b0300c06088401910082c0010b1880c401c800c81400c1c00c160a1011100041c0e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 357355494 1250 357354244 357354247
    0x207090f0f060905060f01110a0606030f0303060e071707090b030a0f0605040c090302060a0908010903110c030c0a09020a12090602070201080f06030a11010318060c020c06130b0702012102070611 85
    0x203440e585586e07001c4841282800c281c0465102440070303c0c1030440310003006091501d0000c020040c01a0700c18504002c074441e0b00d00f00025a100c1c0429081020204c1e841000184110500d500c00c00703004481c1c680041c003c1c14030714030060700e41042d4405038004940c0d019001d0b9035213a82000c608014050040103080640e010004454442e00040210100c1c0c00040d00803180020700b0704000e4030814010000f0848078008208000309072a0051003c640e24031446a1131240400141a13440c012584252184c00203000540291501d120903020303400c000c0811040c0844070620480d090a28007404198074802c1c01e00590311281d40c80058000003000d040120410301010070082d958500040030411a600081d05441c00c8010ba0f004902411084100b21145548084818100400742d0011001020181c080d1011a41d0140902890b8000c2c605452080800184200081c52110000385001030043c13400e02c2c120394414480c02894070705d503054003003060b0703001500a040c0310f000c0c441d9603109003440c003105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 357356744 1250 357355494 357355501
    0x15150807050105090a0e012c1509060a0e01030b0405011b050406140d09050615120c04050702071a09040f0902030303041502040f06080f06180f06010207090f0f060905 73
    0x4558525060040070305002c03000a080c24130b965071218540081c00c3c085a001d60640e121042107070300300700180089030001241c0090241130303607540825a00c1074050001090340c810003070f0704102c0c00300c0c8044c051a4122050250108040c100000c031240614061080300d9030324102031801500f1140c3c00d18000c60a00700c0403040c00c80c181d0b03019088904a80591902940710042c050780d40b0854402e040f62070540c070346000d58020400c9008500a072013425500440c0a21003555014000c14114001604178560482c000b50b072000d02d030503409550812100c3c41102c22160715408001d207200c4070004d030b20143c2d1a0114014581d8949030054641c0b00c40c40540601885005501281c1d1724080604002c203030070314030782c800c40d69404070f0340c140d40c020400b140d00c428585948902c081c00900042d00d1404207085c6031400a0854240611011a500d00060285900d546c46103141e40d000f540c060603483c1103001d0341d040003445003218003510b84012a501400120710080b5003071401110070503400402c400d810030040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 357357994 1250 357356744 357356759
    0x4060e1e04030c0b04050319031b02031602040e0a020d0c031101020307020919110a2a050d0809010207050106090e0d0c0308130204020706020309031e0f0405011214041515 75
    0xf520840b0781c007510f800744986071450040e0850145140c2d01201f844041d2218424a525400c0000c0176280c2c0400070494200e003643c101e841e841034050075103403001c051003c0300042c141540420090036040301950310700c0c0402e40c0002c0b00c08500c2041a20300f0b050402050040c040818103918880780b00340010340c81e0100b140d001c6001800d0003022400135003603c81e14007950081540045250405081005580c0c10a080015040140810041d602c80c80e50040140a880f8581045ca0b620707600310005000d0340c00b100f401207509540082c10285155001c0c0700b65000a41c003400b40501800d0303820001305801441f001e03030350320741208a40008104007408100d040800d400c801d50741c0e000000084506048292130001c50080d105d650307001850f4520010410800c0d843c0813000d450064110030701803800d40c03a41c0702002413501a1100320b19034400c080004211640c02a1328402000c40300c180045210360f03410792090a01c580c00c58084d0351041d450308406507290080e00ca180e8404c80074004400c030341402c1544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 357359244 1250 357357994 357358007
    0x10603020319050c10050c150105130b15030405010f050903032a090a0807060f140d021303320304060e0d03020726070b030412120b04060e1e0403 64
    0x31000e42011440202c8184001400031420701507002d00954683c241400008040e0381c400d5055030b4150050340020b80c842c2003000203a40c12148010800429061480001001842d0300f40441d40d00580040300d250000750403078003a40c4500d01880c000142c1c0103c0e030440105540e002465031000350070410400006400c2c522440c005a820108802d034400d203240480c0030240b0500c83c07250761007404401c000a04440010300301050703419035030b500b200b1244044801e031403103402801c00403540302c001d00201c8ac04101c0e07039018210300c41d005130f03910543d0390b0350b5200c1c000821002c0401400b50600306030119222680400359100203010f000003185800e01c1d10200810071300000000c0e42c8101403420020090520800550380a41840202d0030000040d1041880c2c54841d84040e0b00b5540c0141d44000a4003250360056a11540d04500920381c03c6600300d200300c618050500c05280344503a2000011841c1e08da610426000d03100c0d1311030b02c2002d410000c240c429010241a0b2003160182e1003001c000c002036100a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 357360494 1250 357359244 357359263
    0x2208010902031204320d0c1a0412080a09030f0b09070501081009020304060b030d1e03050c09061e2b0203040206121305011a2106070e0a0306110403140106030203 71
    0x1c504081c54074003440311000340503450116035000c0042160300040c800a40107a0040b2208c7c90007030803550312809442c0032180201c1c800da03950780c5030008c00d00005c201f00038000c22860b0078914000301120f0701c907070f10032241105100c0c040e96a601c0100800900c1042002400f010301024200b40a60346009510446215400d008004550750040041400c10245403c50380901c1c0004007550f034030701a201c20050030000d4000000782900b02c4000d03598180c6029120f918020a606070404e4a44140c21080c8080d560000241400205400700da1403103103d1a40060907100002e1200401d82418110081058010a030100b454041c030400501005903103500484282d155035844510850390307521111122800340041c0074000d9405c01188810054010303511a2a0130030840341c0181032a000b09080e41c0d1204038200d13100c1954071600202c6c0ea01402000c2003100d064006041e040c0b120344965030b000a444208503c100341c10720100d81401004102480e040715075070084000c01186245400203603880c00c401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 357361744 1250 357360494 357360539
    0x60e010206150d0611030c0a12050c03010603090323040807080304120f0f060e2a01170604200304030906020a0804051c050d1e0c02060f2208010902031204 68
    0xaa4004200001c40e0406078100071703050400b40c0c480c1b424084602e12648921200c100080329142c601a0744c407160b01c1024060980106900c0c15603090100c190000e00c6107a4082d8148845010180c502c858004a409201c103203d803000c603152032421030058035102840e08007054580040c0300c00d2000403011030b18070321007540102100c003818400d41002c21a01780114400b4003c14200b171501fa011a8000030040400001c03c01e05064101511035403000207641a004140024413541c4c607003459980c0540010f4100300000c1000880c11203d0a100e010b10081c2040c0740b44088001c82004245508054400002d0403203002a003ca84581c0d500d4903504c1c415401ba05115070706000103544808900703118910380729030110840c0c0c800007402502070a1218a601c084c031610700c440001040c154410341162a90341d03805410701d42001c072100321089041d0020300d0007000c0d00b2040c04550101414449000b401420705000000d074054083c014941006015001100d4445040204000010040d2010305e80070006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 357362994 1250 357361744 357361759
    0x80c06031b1b010c080703091e0303020c100b0a0801051006230c03070c1a0d0b031617060a0b0f010e01020a0503030709080f0c030c130e06010f060e01020615 69
    0x40c0c0700c11034030901a280180085529604000084100c15400345480c0406a03c82101310b81e1340d404101e080d0341208900070040d104c441c4e0080055052408001245440790030050f00748804107171141d240440400720001e00e541c84444005850414045100c09401108001d06c10751805c0020f607028850b0522070a4104107088081e542d5605002e4042004e03000c0040e41c42e0341c0c940c0ca07101031550380e40280b2030076500031400000010740040385007446400d50020030000740c10503601080b480010443c480c0040e0300750150f807054011400c2c0e0286000003070214039031140340f17114003040744a01e001801805031034041d01e844202c80c116a82c04d003034050300d07420034a40f80c10020700200c0100e040848407200108284804800d00404c5900040d19506a070040e20072504e00d0b45446c00c202e603172603c00e40710898040d08110021110390810a5540c65010b0381c000e40403458030600c1d80051300e8100c0076031200c40308080c0d4242c01d02c40c0c1c640c0801c1510640100b44014034940c00c0c040014071011b0f40114113541308404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 357364244 1250 357362994 357363031
    0x150a0303080405030706020d0e0115140d061407081e10050f01030f1a040b030c0a0306090f150c17040506061003140c04080705060f03040b04020d0203011802010801080c0603 76
    0x3c104103e48034907078131590954441c200780d4024070141100d005680c400e0350070800106c40341c5078906605400c8560007c0f940c04148020424040d1206070b80c2c01c03d0b0360681c1c880006c007200491800144d0b001740800c0c1e480a4480c5041d040b403940c10202540c00d200411001700902c006070a051110100f990f43c2103d00ca0706440503e00183c00800821800c00380f807500303200700441c2c0310504098182c12098286e03020b1040040804c1059110040f6024540d802002000144003017001381d070001070414440d01c038101c3c4604c0c0d10348601601e50804400305940b1515101d03203010883c2c0c09560941d0210710300901004a0070183d50f4103494440092810307000c0c91480721080165442500100c4064410180360b2496040029505544d46e1250041001910030303410300080030300700b02d000c0324100790303201d20103608588980c1d640f81d04c245405413042c3d034400f240a0307688000d82d41c01c0c8502420b041048030308120211441c4000b40400b14141d1066035039822040200300c040c1c0304c90040300c2d40245000036170604000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 357365494 1250 357364244 357364253
    0x11805041a100804030f0207180e01020f030c04030615030f0b0405030904090c1d0f1506070b0a0915020301080a031b0f030918090206070b0a110d020a08150a03030804 73
    0x407280d000c150742c428020303601da004003900070032000e014a000b642c4146604841c0038040c2ea07150f0380c0d40b00d40300d00701603045d244041d544407542c4240c1200014000152400e54050590301d810b41007601c0140007000002410820010507128404c030302000844984c1080c0e10f941c4804072055540300002c0c1080084c0800a02044410300445413000c43c000c00400800f01681800c0944174018001e01c1070744200c50603d07980301d08507000d15034480c3c410b41c6040350450360b039032101d00d0102044255040e000b042c28000c910000b092140700d24400c20f041c2500041101c4541130401440c1e0307500483d007111500c1007005008400020540314a81034050904071144040050005200070104038060404182d01940c2010540d200d500001100c410b0003080c1c0704c078003c1c5e1a4007c211008040020342c024010080d50000840405030568000e0304c0c8034000418110b8609400b04c5135029031030200f00300c0e0b800204052070b01e80101ea003507000f0010001001501c500c060100b9443c2e5454000542803240c228001410031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 357366744 1250 357365494 357365531
    0x10c080913060333060e06150c060a2703050d0902060403020d050307201c050f07080102090a08010b090a0b060c0d09031205090901060806270105010305010501180504 73
    0x2158485441e07220001442d0020b24081070414106035844000ca1002204501d5800390f40103803046d58140403001d07100d00041216964000704009100c00e400d01503681045028031107503210b880010000318001111403800c401c00e10403101500c0c0d0086480e521080801c0d40001907e0b1800001d170300008403900c50f400011b506000c0c5900c020740c05a00e00b401d0500304a408006810102d10500002001d2480142105505140c04050b107402169805010b000c00c074502100804207400340c0d050b152000d00880001d410041c0e150804040c0742c1d0006901070490030100303d030b64000d08058000f0010203052400140c00482c015046291007502c40d018901280d540c541260b07843c9513620b04490112105010213401b9078a148415603c5151170b02260240c01d001e60100e4180c10030042a14090303a00380401502d601801508031fa0b003201c0300310032401d420115008102c0703082500402c0001c00b503142400041c02e90b030f416049241080500303403a40081d03884011480c0103581048402051000e00000e44076440b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 357367994 1250 357366744 357366749
    0x9010e03191e080f1009050702070302031632060409050603060c16030c140d03021305010c0302030712050d020d1d010e0c0d1b03030908010506010c08091306 69
    0x150000140c14400c01041c608900800c1c0314a803149660080e1080702d0946042d40c0440c4040450803800015081c409003050565104039007003038160f0010b86940c10030f801c442007202c1100159124802c02e000b989410803541c50048038000da2440c040341841c990b51180344203041801c40107144005039180c0c80d031290044001100c00a4020303038980b41d40302005c1c00504814ad8955000e4050b220108500500040448402350310f1600c0141c0c000446940c22507644e1082c0b00140d980b4841071f140000021824041c1195480e6140e4015855203101c00c644100100658880ca041c8480654010300094010056500841c1c11013444541220700c2142516203205600070380a100f44000f4041210907190303404402a4000d0400008081001d4002c1c54201d034030036603c0201581c46902c0c94102c1d4500f03012030030540d9115000e06480c2400d00c2c07101071f000f001c0a0300100d01280c9202020f1050072003d20410754004000d217044240c41d0341e81d403500f990a10030484410700608040d03945035000305d002c0c2c010000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 357369244 1250 357367994 357368021
    0x91b030102070b0c0315090103030c0f05011b0201090605010f031a250c0b0a0b01090b0906040305011b02160b0706050705190807030c1103030604091509060903090605210901 76
    0xd840ca0413072803eaa056004592004000c10341003c0c0c40e60508200c003040381a268503448000c0c00458646604035881c203038000445440d074881540800c0314101040901d2401041c0d000071403080d60500d40001900c80580020f0f407600ca59401c00c2010452965a0701c6150800c5c0c0c4003014542c4410007040d50400c00c1c1d944018800300c0e45007081a00c1684882008015400f03240668500d4640503122070a541000607428000741c031151040c40180c044c00010180c003040288050b1a0a503a0741e02ca909448600c55034141e0301e0010200140040d07014044115405003150303441e880d20b410141082c166004007500501016a0381300050034150081007103648210500550059000d03a040005140c3c40741100e02d240001c1c00c01d501c582040b8007800c0c218032443d0f07244000d1800e41c1d60302401c0c030006042d0032900b0313501c2c80b110b40044071f84961188604d589a0b800344102083e001d10b1424041c141e0000b603030200c1c0400c0400c01190342d80602200e03186030030915129154010fa11100c0307649002d02801c98999a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 357370494 1250 357369244 357369263
    0x3070309290609150907050d0905070306050f0c040e13241e2903010b06160c12050303060409031e18060e0a120f230606040203091b03010207 62
    0x1000384200d80c0c81c24400c80d400c4944007040e40d200c1d4100c5104601c01201c142c1c11200b401c02140c102c501a0340508211281003000043c40074281c4c9440e0b285c074840e5441511000e03501d50a000d85002c000d415680e1001100016030b03c0c1c03500c0c100d80030001c2500140700083c02281480c0010030800b18161600e03e401d84161031b4210045003108100c010240707100e036150b5000813040700e44240f44440c001c6001d0070701c40a05006079020f440442d11040c51a20010940c0355503500c007212101c1d51064040c01000ca05940c42c13240c2c040c010325082e003583c0d1051b082162502c0c05080c800c5c0014900104680d8050020340d40800c0100803440d050ba010705038015661514507540c0304c1402a55400007048540ca41d0110b181903400340c4d03600003520303501c920440d016005241d090040c450a4141012240380f40d100398000030840019858800307844040d06071038407500c6003a240c480384000e000c002d4a45c0062049404624604110b80950354a81c0e40c3c03202003e0508800b042e8a86556080d4142c0d01c0103908032041742e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 357371744 1250 357370494 357370553
    0x90307060e030a0906020d0509060d11070c0608090703020d0f020109050402031306060e01050604150903081c051b1801111c080a02071502070f05120a030f0506030303070309 76
    0x140d140e40100c83c1e60400280c1c00d181c0050228400070311107042e0400b649035203242418074014420683d010480860003940c50340b10700c5046090442c0146640341c000e143c01c40c0c00905010000f060f0060141491301694000388007800541d440c2c42c42c0c00c0009500c40c1850621007504e05c01a10484259800250b20034404010444104032600e405210140308a104001c215240c00300c050b00d02800780603454100303d00744400c0c410316070703086410307207001e05541486250302d0b540359241c2e0310304c2d800303811071702c10340044100da040c1780751642d02030640c008401900c0c4620000d580703200d961090245020442000d030784900351414a9000705001040c4030032440594500c207180f0140090141d801403440c0c0001511440000c1d116100d074401d44003501da1264139448810110701c00d19010350000c55050b44c40c202d440c411103000900411a0300c508801e1a42c615449848040300a011901700c50128171001c0d04001c2000280c0d0340200c00c13603920100360b0600081580701401e0854071038240d2804400100742d10000e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 357372994 1250 357371744 357371771
    0xe16020c1915020a0f1e050706050d0b04020309100b04140f0402150307020a0303110d0207030810050a03031205070903050a030c061506020a02010c0203100c0507060b0d0c090509030706 81
    0x110800c0d2841d221203601d00c4158610100c0e6075110135540540304c2030305014004009000c800711091613505059003a503140040743c4455003000e55540c0950045903000806269581c1c40d80190f40c600b4804403811401c1d8940141c2c81ca450b0b00e111500509059a100500c2d4074680d00c03a0322282070350302d403815507085926100743e82c8010309409903016031040d0058600540c0803040007045030701c143c01d280d02404141c8200d0f5410b030040c012050102c0c03100c2c03005010302d40f003c07135452001d00b0603a0b00998582d40c1c28100b40000d58003010301c41c0c0181d40038488071041480481e0b00040d6034010340801c00c100081a07561040103c07134010003500001c2c860b00900420405050380090103650503402210208405496610100312040c064410300b4056080400301401560050301044245400034040d18411a03040220030111919460130401264021412000707102c051700c02c03216404402d5035038017492501a201e1801c5c038415481408101c545410014200704814015129841c0d8003540c148002c0d00380d00407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 357374100 1106 357372994 357373039
    0x10b040b0c01320702030405030a03050f040306020c030403060b061201050103090615091d030a090e040c120605060f0f1c2102070518010e16020c 64
    0xc0d10146085110000d04100d4070b9035a0381200c0300840040e42c0f2120201500a50456106101c14041c9460008507401187d400d400c00030745600d0196141c012a11454000504a030b00104105841142c00000b510503684a000306001507048803040c00704501498100040c04082e2500401655000c0c0e401414030500036100031900c400908424001c84115900c0b2a0070260b40f04407000c842c10f048034a00f011008081d01031450542c0304d200007001404103024104d00d1594070b07000305080001c280d44030702c0100104400c0c0e00700300ea40c605020707000b01411602680641c04111408160b4038100b907560b2000031006101800700e000c104a044a01600403404440b480404d004000546074560b000500f100416030040007101d04020900140241075a03a0181104200006103d0000a8165941c1c4550f400c281c0144850601c4001c82c07800c0c2066800a40080400303841c3ea0354904040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 357194244 357374100 := by
  have h0 := BRFrame.cov_init 357194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 357194244 ≤ n) (h2 : n < 357374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
