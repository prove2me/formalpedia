-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1468
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:08:04.748995+00:00
-- url     : https://prove2.me/submissions/dde5b49b-4bad-483f-ac35-12389ec356a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 263848920 ≤ n < 264028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 263850170 1250 263848920 263848943
    0x1b0a030501020a050306040e06100513020427050726070e06031305060601020a050303220c0312090906081b120f16120302060109020a12240f0b0f0304 66
    0x10030a002078110700b00207486440e16480c01d0002d120645045101049198020700100038203007541410036010b81d0030a0302d545955140c89803104000784901d4200c20f0100c520020000034007070721032804101d100e21211050081d521403134410b803030340d0300d0359045080d42c03118020ba403072400e15450366076039800001032820010340030502c0007003915a802590300d8241047d80c07280d1501030101c02c0103113070b4200000788001e200c840c041d52200340e1a40400341000d0ba04440030702c8280250400c008200c5080f90300300009000050703030380c50150441c80c0c0c0c4207201400f140400000052000081c444c45007240d40310b4000d08046507504625030045a40d40d1450365212111842c1054a01010424580503a26260041458031080c00820f82118401c0d8008024409245e594100207940410b5460440746e01d910096266030541d98103413460720b858614240b40500d0301c41d1103081e2030140c2016481c0301600a1480c100d10b619540c805400076610302030780503400c40800c0301c0304d002c3c0d283c03900441d4060302070404142c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 263851420 1250 263850170 263850173
    0x16050907110c04060b12070801060c080706090206030708040501050f060112020901120501151707090621050f0a1b1e030e010e1f0605010917010f15060f0c051b0a03 72
    0x300c44040c5c002c0c4007440d0000c40c11104509000d502c0580000c02402c0c00c1e00c0c0c07989030440090583c000c14200400603800411400e0401c0800e80005802a03401440d65469160240c40200040001c07501a40d00e50f003440041540701412480843c02104182c0d9070810f080d0ba40392820001e0b40c8985400c07410090100e03902504100144901030103090003000c05801c0080728017006050280242200310b5849070390007401225a0086001400c071403503401d011501303104400601c14404040f480c000145410082044040c81c800c402240c414020030000f00100c0c240442211803452591807210041800341c145414801800c8002d0715003081d10389000f141d020034205920342521640c5407204039540c051040141c0040c100031080503554000013003008030030301c1e00700000c000845a202c0d00b0484c0d007008500354004e10080d0003094807501400414015008400c81d40c003140580381c81088001860000c3c0004902d00c50f9003907040e025000300040508403401110140c6200300b1040c80c41d44122603000000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 263852670 1250 263851420 263851429
    0xa09050f010c050904230a0b0d0f0803060a120f030503090313030807060c0507080702040504080904021201060909020f040e090106031502270d0b07021006080307020316050907110c 79
    0x34440d4110307940c2d01d490b140141c0c20310065440f800c10040d80e89400b40e075010250006c440d032031640700e511004081030321005103011880300080144042d00d4111442c01d01014442400c0046015107025108590005d90301d0f01a21085100102e00901c010203600b0101c0102e8420005140c0016401c8241c9140150740e0b0041ea00340100342c3d00c122443c41c0e002c9203210600074544518508045c540c01c05900e0300382c4070360301c14006224109009128981d248041000d10022600356480403030040c2c02103507a24110001c0c802040800d10905e00022081c031000f090780c4090740259043c5c00130130b41c21141014205203810814550081002c25250350b1008004003181c0c1d4075071101e0f48850792103c01a6a4128203000a184110801d002081c0c506480f140422603201e01d0200c0000e10307044070f1600c0094440784c1049003050380280081c074042c1d05007040404c2c0b4042c04002095158800c404a40c0303006d4405c1c850150b160518800c0035444140880022015401080944075440c0400282d90600b5070420006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 263853920 1250 263852670 263852681
    0x120b06040b011d040b1908011a0a150905090f041205090d1e082a03120103080d0b1905090a0e0616170f0919050c041a04020309010903020d0906080a09050f01 69
    0x28865151000c000101c070278881e6412882545000c1c10940c441c2d500880e15141d41d0384a2071030012480104465490b225110b40d030301a01c0000d01c80d09141c10035082001e0042025103080d82c4200c1748126510400d0301031000c0701d140d160050421015202c0320b4840355642d0007a041c9840d0904003a40c1d1000019036100000e1110202040000c08618079519002c0f80d00e001080b8200e115030f0040281440310782c52440d030f00f811aa80b0480c42503550f03a180c0050360141c55200202600481e02c003081180314881100928241e40c410784902546645e050240d000b600c50108902e02942c022501094070214400c00081c21131015013802a08100e604d07500c0b11030b400c02180c07290b040380c4070402405603180c401d2007a40040f003911520070200c414591143c0c2d481b0716000e0390a5104654802c40c2d101c640302d0f00704851072203910082046449242c0360ba0801e018103403002e41100113001d2030301f0045406000301c840744195041342d036805c42e1564a59031000d0050005540941343c40c8a074074110a0065000d0091 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 263855170 1250 263853920 263853949
    0x105100210020c010603120507030c200307141009050901170a0c031a01080313151205040f020114030114060a1b030e03010c0e150a0302040807120b06040b011d040b 72
    0x5e065407a40c20030844c0c0c40c40c950f50300d00400c48100128804070394400308200c0402d400a000d41103048203074031038211000e1080d40003605400b0f0400001020260300c2c01c02c2001040c261482c0e20035012481c402c0300c0340700f103c2c0a066030042d051070041c4aa140340b50040e00300e048240040f01d20040003034036124440700b5540e004907011140c00ea0342809425406002e50300600b500c02c000c0d4100300200101c04082403c5010741c0d402113483c3d69420303100703d108145419828010410030415801c0500349030240302180c040c1a0f000c2072000d1003000800d401c100880c0d04a0302240c05105001104c2002c0006a034080c0e035140c804c0190107002c0d2000080703094000080070f840794803500c440782d030380006250940750f8004c8c840c010f20107031540109080d00e03124520380c034010f01c010f11740d556511003039003c1d4002d0090ba004040d0074403c2d90404034400580c01d0340c41540f54002c02c070303881c030030790302d140c208020307114100340550000711908080044045542c00c2280102d41c002c101043c1005c03541c01159080f142c015a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 263856420 1250 263855170 263855173
    0x409020a050f1b0c060702010f1d060a1808160612110c0a140f0a080708130f140402071104050a060302130213080f0a15110307030c081303080105100210020c 69
    0x1032004002c90f0030000760710004403d65030701d410260260000381041c600701d10804280510106c0d00b40ca07030107848410200301c0400801c0e00361154000e120003000030b4119001c000346118100004180c900d00010254032542e030b40e0810030b10090400e4011568411915104031f035582e103840920692211500c05000042c0c4d584005203d06a81d5003007200c0642442900c1c50b18540101c44101e10300400030503040d0a02c3d40182c880e558504d4980b41c42d4050384214401e130348118020000100b01d03140c49240030341c110b5901c83d6100048a10300401c1000f00d22034810010031203002c1d50100c910f0b80c1850703000a0b60240389000005a580d6590f0045048940146a03043c0c0726680040c060900f0480104004d001e00381020061020150343c4540c0e84e51500340340400b81485010780818903681d0004e81010801048030b084c102c0c0c0760b0400e050080c0c05081811840404250b440d0000ad05040810f8480700038540c065950001c0350b4a13290030322007020040e031400780845c0190300da494401d4902e80000c0c00d42c3e0b11120f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 263857670 1250 263856420 263856457
    0x318051f030b0f150702030309060a0c050708011505040902030f0f0120122e1401090605030f0118090f0c030b090a051506010e10031a0d080409020a050f 67
    0x10002000c4886140040d481440d0101d121441520b424100381c2c4d54082c4188143da440040d0f0001a240d40034030f0a0f00d07640b06600140b49460140c0c4030102381940fa11410407504410f40f142101820b07109101c0b40114202200141007142e480d107500821460390001d81500c006c5490b030f90b0781c54148130902c10424a680e4548500103081c2c0364810306403520503c4000f595044c60082c1c0b1010144c0c0c1c2c0090104010060141c02c0d00b101440c2010300c1c048584070001001500655408885021204088030030340440d140542c0084c030280141d080703900c40c42008814040d207a08082100b2501c0c8403602403c03102513900c508030307000505000648401c0a01a40b05440c08515610b000101e40748000c10007441078100c02419800103d002450300c46281e4a0003111010f95140c40040b0b510b2008031000c194010034402c140150144c06900140e45158aa0180004494044144044c4843e07000b001400040d08100420064503a540501502c501a151543c03600401c50711034183d0fa042680c0910440740980c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 263858920 1250 263857670 263857729
    0x20108060a0e0928030e0609040b0306070809010b0f0d1203150602071701060f0b0705120f09041505010207091112010f0f050312030f07020a12050c150402030a031805 73
    0x220221000600c9000c05444d44116507002004025124525805840c001c1500c001c80d566036041242e09100c05800c075107035460480e070300404841c4181c540c40d1141d444c001e0300c02e10702c0c00c1002c00d0042120014040c500c241c00160780705201c0403130031482d0508043c0d0390745885801a180c4148117005104907801400450704100c1e003516180d1301411402e8550b0700d03103002000244000650801101c0800d44426140c00080c01d00c5800e10038071100c140021040000c1040e0850511400b4150690082c0d500b000420040300c544860a0058082e4a01590010b50104109140c9820440031407084a030114100300c08800c0706440e46500303800410740c10b04201000d01c5000400c1c5882402441c0c21801480c0078014001c040055200280c011707150130803e500060003140c000c102824605138441641c0080d4100588000d01c0e1b5080542e001c40b43d03001e0703c15902145003444880074042c0b900100504144440d5a50a41e00713400c1c2c056002031168080c44c1c0000d00340d0750310340304c070544030007882c0b040c10911011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 263860170 1250 263858920 263858953
    0x61e0306010f0311120d080c0d060303120b18160e030f030307080903030c0403030e12121b06042a03120228030f0e150d090506010b07030c020108060a0e09 68
    0x7681d204034042e10106644003a100701c005122400c41e046c43c10407081a48801724003000a100d00f11a000e4541d00780030001082561022800c2820703220a201044020321441c2046001403419600c02c030101c1c80b41000c54400062980f00d010b0348010307400c08620003080900031030309044600c4104070341c1d41c0021003002200ca81060359107900400c680040d40c61407902c0c400303140490240d8080501000804900c84c9101d481d130240d080000f44820040305c2e40c1c1030440440105507032000c4c0740c2200000c04110411a02e4000052090249500064021001c901040b811840403694505e149403d00d182c4000000f060400303801c03500b050000d601034145007058241603940702049100000c84070315141c440780c010950021100c0f2072003849207043d0001003800320010b02c0004040d14210400f450000d504c032403070314440d0b203c140744510a0341540c09682c0e0b01c1b00111020b010b03000f00500424031807a0400015840b4000d01e43d03001400034618a425611190080004a8101c500080c02e50104410380c3c81041d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 263861420 1250 263860170 263860193
    0xb1305131e1403250305041707051e13020711062101060801050609040e1e33010b09010201180501020703021b100e0a03050a0c150305040803061e0306010f03 69
    0x10140015844c0c6282c600320007044900c0e01004204020020074a00308262040044400800c41c180c60006000c8600d20703200e450b909148a5140b10f01c0740024030f849000070401141800d40802440014407060b43c00c005c101a500586003200d03400351201a0420543c0e40b00d020301000701e01c0c5841082c080c10134007030440c848003043c1c20400612118800420196030b800e001c8540081040d2404510b44501a41052620011240c5509941c0b41c0c0130703440010f10340005001c044108400001854503c403164006682545203109400540800e401400700340303007002c01408a010180b000080d481039070741040f5130108a200c0100d4039130350001142410b040e4100096801780207009582c899003140800042e80180720254a1804c1c800702c99008440b558808615500560b04030095a810306401e140207003150040340075103540c006488190510b4280302c0c0c41090b05c2298003039621484c640f511020004500c103040e00803041221124079191080c0c6080c48124000c004480c808500c090641c5043c504110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 263862670 1250 263861420 263861453
    0x7020a061104050d060e07080d02032a0c060c0a020904080316090608150414091c0206070e0904020409060614010e03030304020a12080403060204030b0a0f0b1305131e 73
    0x40140b105000582d40d5101130000e050f40004000740d20480d0366051801c1040030f510180490042c840c4110009401000030403404850000204e00740b5540c10312054400c505000944084c1d101d02c070303510307190b04000f001000e204100070f0840d41301031314503400180442030407242280d9042c4040180833100070a1b11446a580400e400c0400002e420a00010300f00c00c001420280e48205151700d454141d103a036401b0040440340700342020218640071207042d545000700c5001f0508502c00100b0b18814a10214410340205100d940310303a03400c020381040080c104005807085e40c0c425610800703280024118030881c001403000301000b52000920030000342440c02030072840c9009820803c00c11005980794541030065a451640040d40f403203d604001142780182d07000203001034030002e40401441044010184103216601c0c0500075120b440010106035121050155006101c443c0d949040c617031141c20050703118450700f40c00070310b03444d0580740e60900c10502080c44d26212403400100c024054007022010101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 263863920 1250 263862670 263862701
    0x1103190c061812081b12041e11060304062d050105030a0b06040504030c080a090305060115052b0c0302070209010b040f030326180c030d0e040f09020907020a06 70
    0x112090748030307500d01d480a514201d040001010002d000c140003d0ba42002c5d00d6185821551105c1c800200b0301121002500e003901c1c900400d400d14600116040d103892245507109114175031100c518801d02c0710325000a031088500036211903903a0540d0090303141102c640112269240483d10940c00004111034040e00010700a42142440801140d0360b07498042d0455404c0e200000d00d9540d9040480310304030011802008a10f0024203405016881420481942d0060069400d240d903559540703900766203d0804100030800610210f25001000c1202d02100103210f041c0c0000c00c920300c0c100404842d41050300e01c001c03a5000c02c8007019818003141d582d016141c0d1f9070314180b4047c10210119400149171000804010110042e4000b440070802d8100c1410700c142c003181c40078145400340c4070407501c802200102d203200d40100e00c0141d00d00082d03840c140d030a240d1141d0030b214490800b400050401d850480940701c2d2201a1040141c0341c19548900c030364819405045003069918206069444401000d07043c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 263865170 1250 263863920 263863961
    0x20d0c0513081c051b060f09010c020114272a04020a091a041d09150402012a020306040b160c08030114130c05040503010b010318031103190c06 63
    0x8008200444100c01c001c0c0e090403130b15944002080c90300b641d403040703510017940540c6050222400070210700a01980040d0300a00c078030a0550300807401c98a00c100003003000300d6070402048982c0d60503201c02c0045941c07001e003058003003c920106454001e40d28400e448800b0503640c00c800407481c10414500034541250250712b00701d42154000d200310800c0c0210340003d60b800800742d0300b0100c40011240200b45c084502c04810700d00c02000b424507801191181d81d94040c1c5101e03842082d018206103445903038161a030070a031480396886402e80c07803481c0c9002001110001440000750ba01002040d10462007945000034074980009002c150000314003042d018403400111040014002d281a2419100c80c810b01071000600d140c00100c0c18445032441c4401d4600d00050700300c032654408004c1c0207845090b0024041c0700541401101252007140c040d4540120382ca0072a070010707114060004c00b94003054112403c00c0c01c0d424440c074175030030304684c107101180544220808000c024002d100207140300400c40d010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 263866420 1250 263865170 263865193
    0x7021b030601090e1915062909030111031518040503030a020a0903060c02060a110705060c0a0c05061005030d1e2012120a0509030706020904020d0c051308 68
    0x195100c1c1802100003da8032015a020450000c00200f044040321741007400b18880f00f41461000c454280c03914983c428100301011519080c40b08104010201c01401c070040c0302c1c0c4c1640c803181d480d00454900b40d455501e40e1010b80c44c2010040256024001c5001080861036002d01042070300000380c40702d031407000140000c20000c100040162070303009444450140c2c0e105020201180c05440d40e40005000d58135140304400030641c00105035100f513080c034030100300d0404c1096060f1194000c4c144010065030040000400a04410014292001782420020748410203070b80c2b00b41c00c00d07904840e0012100381c1004204080c0c036040080703542a000b54100a05607003c94896400714058000a52040c45100700518010410103d00001c0300080101552401542905401c200e64041e5042c00000c04400010840d54080c41c4030310b030b000b001c440000394600b042c02d6540c04080e41003500c000c1d0b8400d81c00d108002c40400c280c0213030200e480c80f40d5112540e5000d8180f1500e0b4a1600e030304910b5665111840009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 263867670 1250 263866420 263866423
    0x10b010924020c0604090c03050a0e12130b030f070e192603040f0806010503032b0f05100503060a05060a1a0705030a020d0f1b02010c0206070203060f07021b03 70
    0x8a00c0d115440c0072220103901484168a03029182d202c25400240c00940001e5100d60359002145000060f5000d0140d03459014017582680e00b0b60002401c0742d0089424003110382c01a03c0200f0101c0e1010302070301d000c103075201000000d90304116240703101d820b003001c204034151f503016074000b95912049400310040344019107401800034160103400e900d0600f929100b040200609400303010890002e0860b80d40b2a11426940601c05413445000541d00c541d03000403690703160110644840001c598040c1e11204081a46080041860001d414049541e00046200008580a80d9100f00400441d40150030b140906042c64050001c0003455414545814460f0340e640e000ca0700822516601c4c8500c41e145808100c1402a20030010700600a1000082c001c0309240c0108041e10a141e86032290440801c0c4c84000b1f458082032545038600c8541840c140c0c600546c0500321074660903002130200c90824185a001c030b40b1b8250141c45081c50b034000001008a042e43c104840401184030000040d203040900010a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 263868920 1250 263867670 263867699
    0x403030509040b01050c0604050d140906030a05181c090b0711040b010201020c01020c060403090602030403082208031c0b0f030601030b06010302070f080306130506030309040917040314010b0109 85
    0xd072190f502c40d42d000106a200381e080d00c9083c02c154045e10424141490400e0340da096000002000c100c00315045450814580e056038052071000d80103600c5c6071366201c6904000c2c50001c160080a400ca04400c4418140402c110b4000c40b403030b00340f400854503071210b019140d01566030101102038410426040002c42141e01c014a00e5401da4002c81c1d00b14031080141e0290040540b225555032010039419041c03400028514061406030700d500118584404080b6201d1086004c06020003a080200000343e5400040c0c005011140d45000503846840c1d044280c159800b0043c8401d4401002e1201160481688214104941d0403170700810f08a4000300404c0d00ca61051102511442c1703020001525640070b90101c40c401580f003103c3c00010015440c107a01160015105280074103048100904a0042c6102e003074081c0c3c000400075070800c0c52502c1000054005020708441400580c11702c414034034a03003006040990f1181540c011005e2018042c0f40c2100c1c5c608102e27604100c0c2c001004c0005500c82d0444 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 263870170 1250 263868920 263868937
    0x11032d12070f11012303010e090607020712020f060714010b01020c01090501030b040e0106030f050657041e030809010c1b03231203161e0c0201080c04030305 69
    0x20342d100f0040040c0c07120302e020750005c0f8a03641030780c1040088060b0301004505039203044048a496440f0050072507694142182c402000d64002c44040c03069084020303403075040900c000d003e10230b2103115a02180300d035080f00fa0100c6659400340d0204030a10400c0c01891910b0300c083c0700500c0d0116401c0c00082c004c1103984940e9051642d5102e40c0340d40c070b03142c070340103403002807000f4000b4806150303207250903600e107480b8000a445602404011540d94070b12145003921007060303940900308588092038256580480c0d44114078050125044e8143e290010b800c8003810841c0000401d40c40d58940600d88285000f540b41c0c08603496010041840007130a5070040d41e185190a10b012a041000d038a00040c0c00044034811f50100803080000000700501e1000d1041804002280004640188000c2a60325003d40f0038400160a080c400640815807c500d10302d40d01d6081c0c500180c0103080684030909050f0300c1d003603200006a04507a001c0175940c1044005401024181d0420719107491034034018010302941da00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 263871420 1250 263870170 263870183
    0xe10030c020304120f0312020c0303071d090a06050a05010c05030d0b010c150501052b02040c02030d05130302120313020607080c100e12120411032d12070f 68
    0x121000003500c00c00c15100603020440c29100c004945090900700c22080307800c21030018803030400c48041510a4002c4d00c0780361094034001e40c116103c0c2c903010781e40405240301286180310300301e000118999902d20040c1c0607010101c40010000e0508050000402050b00281d0501140c0d2104100040c00007080fa2314140d1050000242d20b1600c000495403200c900001504503928070b620f1580300000da03403206042f16000c07201968000f0071805002903098a00d050480711460b00010280581840d4000e594211010720541c2d1501914212010071a10169420a405641c0802030b508141d010000c1d040c2c1100c4900c8194114a8800601e4289624055009020786c4010641c60b041155003002c2c2c6581e8000601550526060080d00c1002403c0b101180d401a210700110a20544003409c110b50800d07240441c21607459640e500e1761428820155000394251180204125400300c04510f6110341503c07038146414200010f000251805451009019041c102003024100107050138410701d41c135961001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 263872670 1250 263871420 263871431
    0x30a090509060102070e04060e011506080609040c0b04091b050306030d110a0b01080c010e010e010e0114090a030b0403080604110301090e07050918010f061d100302041104030b070e1003 81
    0xb00101d007400e61036030001700071a000d18140801c020050704400c01c10100d0701c000700900c3d01c4041c610890700b40c61b446001c001c01c01600c08103240b4246001c21a91003400341054041450395490b1694071944a03503c21a20704d540e403401203444607000c04a10381c90580c00d11b0500e0850906c00700103070b00c40c14440d84a000303100c05c0c510f0034642e84038284124440760f5000050446103694078209141c0300d0200c003090301d001441ca1050511550f010f000488440d1006039200000000000d006446c000d0b50200c00061781c40042c81796050030b9130b882e85050080d5104012103116800c042c03401402d04d0402912080c0314a0504072003904058480007600d04440c0c18803c041003040001203042c2c1803030740b0382d009660444104c2c0c0c1005003a010b180102d06041c0e12060080060110140303240e000c031040742c0102111203403c0c0404071409144807039001e400c19081c06001c003046680758005400c44407060703005c4a00c03c5010504000f4400170300106c41d4010000d082c42da40d042d600000094000d50840d030604149603032903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 263873920 1250 263872670 263872681
    0x114090c031f060807180602070911090a06050901140403050a0b130b0916081f110409091a070e03060604051b031e010f0b07063209010509030a090509 66
    0x300c6810021000c0503207144110b544841c0010700c1400f080303400c0d5020415120040c4000700c00d00020301c080342c46d150301801040b07007040103400c09020309001c40b074130205c03050020380d09594a9507010801002c068aa1a64942000f070015021020039030400348292000d220800c04140d000c10b81c40c0d03030301d60300c003244036100d6650b441c251502c1d040c14200601050500c07400c1147d00007001814400d11704a0450007003100b07507580c0440d5074649070880c820580c03018044491503a40d00b90341203020484154044503040684560351a422519400c50607030ba04290702681d60356203404404440e401680d00e14103000c0c02d195480200e5524031010b07010034040c41e92040001e60209644500c00b1000808a4616a132410445401c410849090078040e1500d4200030002411400c0d851103c02181c1d84500d0360f0741403104170303240e60005044100205000e200d918035404e141260041082c00300305c240032040c98a80c241220202c0c01c51310000c18240041c1e008002c502d581d40c0d0004134032401c035403080b102c001e00c0350b541 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 263875170 1250 263873920 263873941
    0xf0b06010908060f0603011503051513120914060406050a0e04060f17010501170601120804092a0906050405061e03040b07030b0a030309061b1b0e0114090c03 69
    0x90350300c0400d10703000d28828008a078450130b14950081300110b000380102500d62a49402103440d91000078a50ba01c00c0251800a0584503413855108103441004100c0307000a031254800d44c0e140007880e0740050084030050191031910307452403031550000d50b009400c01e030800f200642280700ba10912828403200c00d048411541c0c0d643c10000282c801410302802d8560f0310800441042240407030842a942071000101e040d0440030380020764020040b00408503a4030b40140c80559100d442c0c015070703002c101000007140710005400760f003581000008500700075010300081e068004080000210410009080070051943d002054405462003160320981e0b80c040b0310b00500070138000a03000030040c0000301c100010310035500181840f43c00302d61030070720800183c0010041007000e2408014040b841e41c800510000340300d2001000366020180030300070128100d840e6241140a81119a032010205600510168006000b550300500b000c488010a0140f00320004e034800780000c0407001503000c01700007e60444ca5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 263876420 1250 263875170 263875187
    0xb06010e040b1e12030307020601031b05030d05070218070504150c06060e040c0807080303072006010803031501020318010c02130216020405060f0d11010507060e0106090e07030f0b0601 81
    0xb001000d901e403601003280600c0f0390f070301040c030b1880c458440c0c0300301c050b8020300100c1120f2082441d075010303010a0782181c2d1581c007040d110a04044211078032200c04150f13a207080211048550441d2034164460400b841044080c42e021800c510140107580c06200380603800c9015503040d20007801d204280007c0c00d40d001c58580c0a81c00c00506140c5c1402000100b496540503818002c03401003400103422500d03050180d540d00303031742e1107442c8041d17108000045881e03200708044401d600c007403c420811000c00c01d42da01d142041c00c0c0c00070100c540001003400f201860044202280b44420300295040203031510003405c10309002c8074014140800c0358039000443d59805038007480000c0e030701e00c11034459039241ca424940f005119422070042d443c04000c14841e1511408806c200346c4010400055000c036a59561480707070f10b45440300e05000c030a00501c00014100e008801c540701c05840002841c61801c0b50030416940c425088007403d030001e100a00c041450786102581c2d00d900814410b0168440c2c00040380c0d03009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 263877670 1250 263876420 263876441
    0x162001020d050c210112110d050a03080f10080705210d0302040302101713060209040c030b040518070306050c04030c03050607080601180621050906220b06010e04 71
    0x51a1000f000b40d008107100c080c0a01c4100528400c14100e0b0700b406002010500780181c048000803441c840c00003a551924200c1b0794034024161821802c05656003529004c0324200440118140500f04100000c030001c000d07030b100d08450f4030013622071710f02240c0c1d40d180d40c501d003d9240245103940119046c1d10034075100c2d4115202d079900b00d44c084001020000c00075001800124070613200b0b0040c0011140c41180400e024281d4041324040701d482c2c081a000c10b10355003484c00c40c0d54503001e10059980e550350f0720a0003103a00c41034401049042c1031204001c00c88600500b00c4100c146110240325041c100000c020f029240d0000c400182612018207651290240d84c0c002401c410f900d82000c003c218012980c18002d601d16115200c1c5a00d4510054601c5002145600c42c491207481c03080107014403c003c0382140000e10426486200400c480420580d00101c0b0380d1451507101e04c00340824041c101103092081c0043e400310088031005039840394811030000d0715140c100f0070700c0f00c0c00c1c003415988c5030310215062 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 263878920 1250 263877670 263877697
    0x150603060714090d1b081209060d0b03120a0c0c1a1b0a02030307230d020d0c0c0506030f01060f050903030306090603190308010f060e0f040c1e0503060916200102 71
    0xc031034204a4400d4205e45028000d0240105c503540040d2201950590f01c1a50009194a042001d4680c246006081040420741c3c14411809400741200d2208014610b61410340d4901100402508100700c8844003035001c100720440380e6480080c0c140145003a541044a8454010b040400d113407060707417804141080283d81400001940020829640e0b5868840d0320030340740d108180040c0001d100c0d150120050083d025070090010241703003038403851880420f64071a07281d46201540b41c40205805401c12540b942c64550075800500200d90800508034000d441481d020b464140200086078030b03070001500032401580e0031804600103907401d100f0000b04040781c0014070080c610381e04000300a83c00030b12603d0717080300d1426030100c0c103684140c40015240340050702d0865100c00071000e000007894251454006c21051080620f04407600f00000e40d0090055610591241010710811140400160a0105060f40c1c451540349541e0071410648030111401c02820f00c0c56040507485029224400302d0b00380703c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 263880170 1250 263878920 263878943
    0x60609060403060606030f0621020108090129180c04260307061b090b030c0f0f0d0c0315030b0708070203220311030604260d02030405150603060714090d 67
    0x440c0e82c9540042c0520382026810712801e40c9e1001c150030040c189081034900d089c0840c640d13401650144483c0740d00072006500005644541c1480c0850407980703409540c81c00c50300d5020648042c600400e80703981099490000000b9400c100706e40e02602c0c403682c481e4040c0c0784420084541c80d803250780041125106e000d000e03241c2e40c0c0e1440c54024002d0440582030380802d0110140801d03054850744408082e11400c2c0f242c0d41c6180c0300c40402c092a50030186901c0c0d081c500404c845031a01413024098080c2102e03821001c14004540d00010342030307466200360301c1840242180c0070404501e8004145400c660181820012038803540d01c101d042d03108000b0f0034400080140e0b1441078039404075080b0303030072280120340104c80d52062004245c0c032690103440150031034008079503160080607a0780504501350400113016240c184d00d00b5110013030384c104403815241500048101c0c14101c1e00130359503e43c49007040303004c1c0c030341c0d444d0004011b0981b02080c442c103600500017040036103143d01e0300c0d4a54460650454860303c003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 263881420 1250 263880170 263880179
    0x50d0f031209060b042a0e03010e0f06040302071401090605030a0605060415020118050706080c040503060a0e010c03090503030a02070c03150207050d02010c0906050306030327011706090606090604030606 89
    0x5413210300070b1030f07000302d00e000340070302d0007154240c60141c215034842000b56021610304400c448100c0d1481e2403950655803401503c00e1100e04100303800d8003079105000790400d4a024140641844691703442820003100d0103c5444ea01d0380d00001440030703540281032080d200c5d03c40c0c414480003004107030400d68000400180200c0d074001030b039641425140c8154024004d80d44040462481d00000041c0240158000c1105100c450701400703642c1d9000411540041c1020f03640e1000a10707001007035850000140d5501240c10003a0028000e400f0f551105d030405010200700c0d56519031382c0b44001004005003070382c04100c20003044030f10700d000c0000b150030a201d55561003088034454004e62140d442140c8520491a01081d614010f000d07000d59480b4540390309400714a025030a030340d6903200804103541800200070203c09912180320100b589200f00e03681d0b50b05160700b180050610b40d406050506c0e2a401e82c4100f0070907540b40038655500040c00d542580d02c541030f401c0451454002d076000142901e08000b07000c00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 263882670 1250 263881420 263881433
    0x60c1c180c0f1a0714030c060703020712050a02150a0e010213060306120f03030504210e030606060c030d0c0e06071a060916030e1c050c011401050d0f031209 69
    0x1802c0c1c4010400c4249850380d905502c268440d104012031900300c6007880300c40081411022213610b803020903020740b49408013110007076040c4542200e5030404280c0c04a031000a02c103040501050a041c0e03810001d280c296050406940e81000040d1540d02d1040000000d080d102d040c1c004020380c1d18490020764850012110000c403500c100d008010000b840d22900160341d100c004040481c00750446100d0070031301c00d5600c044014020050017a10030314111410402502445100b0307040c2020a43d0352000240d40e058205401c001e4042d00e8248901d100740140d10301844080210342030955055130000d00c8451051040c0c0d005514840000e61200d00402c500081c0080108503c00cbc2024448940402d9a11081000030341181551118141c0070007000e940681402079100c800d0b072904e4107044807500072114044100c1d0425003003400000440108105128000900403810300d40c100c520304000c0d540c10440850030956401720082c1070344020404076014540911010780340d81140940070300c080d110070705091 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 263883920 1250 263882670 263882693
    0x110403030c0b070801050a06051e1b061b0a08190507050307020105071b08031b030106020f010f05040b04020d170a09031208060109090f020c0a2102060c1c18 69
    0x40d14034141460025000714030130078425040c0d503001040540204e0400704215143d40080c00d0002e0054118000e0a56810540e00507181c2844050510460043c0c0a40c41505003503011300600003d014200e082d01ca9110010140d403c000010f151500169955244070a07104849003c4a54003601d40340c140210f499101004500c44d08850f0024480764a03120b1040740c0360100084164410480e0f00000340001e09550000c54014106441c1030903140010155051140d10a81c82100582c1c400d04a14400a01c28021100095140401008185425101c8001030540108000c0c07140e007040d1140c2040000604004003280740404080f87c581800180182218980d40000e490055002d00c0c40c0d80b010740b241d04540d2280d00306940d5890f0841c074000c2d8480c042d18a00740c20343d415680a00c140c1c45030f08800c104807042c0e00d000381501001c0f202241c41d109030011900d00c00d030007150002002c014005034004111491b04440d00708030200c203500f03581540c004180c914040d002006005100c1424801e04c007544 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 263885170 1250 263883920 263883923
    0xc05031306061e0302011e0903030e130c030b0418020307090513050303010801051005031b12010209120a0c1a0702190503191401060608180a0206030106051905090f13110403030c 78
    0x10107c4200c1c8040b00a58070340c400d030b402e020000794289001d20019200d8100880000380280a00c82641aa410000d05940c1c1031480c03040041c1d995154480c103443e0601540700e440c501e0054103480012103402283d00c41d4040d004403000192100302080c480d0f801100000c54203a001002d407034417544c48400f15400382c9070a5882100c40d62141070046541d15020841c4841d040380d011508000c040c41509020640348482d40c9580703d950700703000329461615000c0c6018284201c0744090714160310700f450a45501d4180340c11280c80c045d510340c50742019904030002c42e00c01e40e40450b0103055419800255540741c6c04503801c82500b5014086640c0088203000034180c454034455041000444403c0c04d58500300c6086101d0702c0005480300c00400d52140054864000341051001500e420031010b401044050b80280e00c02c000050002506c4070711039070b003d4140311448034a40f4007989801414000100306040b220001d070f105e0980440d200c410b08074030368480b0420544240e052611341d5900c0c100540b502c00e07103880 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 263886420 1250 263885170 263885177
    0x70f050714010f2a05151005030604033c0201050705093d08090c0a140f190605120108070602030a1103090a0f180c05031306061e030201 60
    0x100d907010345030314003448045041c0d48210980c501c102e0110344d112480c1d21105188000882040d201029240900340311501480007019185200400c1c4c1030703100350045c00d1810301c0320400c1d0140310595000c20056001174040c80c14009281d0009180c00b408010301c03403603009083c0c00c02881800042c0313224581c000150320760000c100c595580d0109541d04d104081000d94800e48081201040c0c20420401802c20070170010074206010005440351680d00c3d25000c4030300031640034020002a001d081001084007a411b0380c0300e110203803520000c00340007129024072502c00e4a8070320b001c25454031002041e82c1250a00358029460b2540c0b81c0c0d014040745e03c10260200000200d03c004034944000003038240c110740d010350085140039024002100c004101505a80d00e03400100300b00c0900d943d500d0082d00203800f051001446103480d217150031301031000c10300840ca4034504003030480303000300c0e0800305030ba034441c850762100c4403d0035162070040d0080400f504060609018040c1c00c03005050030310b200b241540d1007a00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 263887670 1250 263886420 263886433
    0x803040312021c0c0e0d020f060f0706020d1e0c020309012d0302030105040b04050f0c0307090906180f0b010c030e03010b0d0b0912041202190b0a0f1407030e0d17070f05 74
    0xa1107182e6404040103234002052a80342401e0381040c500030001c01e00c02c41c284071f00380184c41c1e6952060340e10050b032407202d940e15511080046a032515503001e09a604000411000400010103500c0780200424103042c41000000c04d03c0710b00300c0054402c0d4110321409001441d140c0c00c140a4029042030041078029450255000c2160919110b500e010300e0f11007151110aa9550001100300c0c1d01c0180003008020f040400060a480313103004034406440105450044028414106030840d04d41c3c20000700c903681052110316541e40c020315045607064041c41c2c82a56042042c021901611612828a8202d100500c08106014240002d0b60041e0590000c0d2011050040740d00c5549004901030000721019501d03040b0014988002c40b0751800c00d01102020a25685035100562a00984e21134004244d03a810241d100039400383c4082441c040d8a140c19041614641b0002c20002282902e1401031400305114820712505441a180e01400c44400c242e446510307240460082401520441c1e1920804 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 263888920 1250 263887670 263887697
    0xd0615020a02090411040b150316032904060f06020a020f06071205090d02040e01090b010509010f09021b01061d07080708060d02010e091311030304030803040312021c0c 74
    0x4603407007200603002010001c0b80d0320b40361034802100d28207511156029586020f03c00e00780d12141903284c1540008075040b5160726240420b5041d41c0151200c40c02014941004e032a40428940ca000e292400201036041541981101080042c030303080e00070300f6803d03501c0d000c00240c03240d0018a100449200f580c00507030a203200000c0c02094041c60000600740140c0041007681203101c1c0f8041c2611841c000c090440d2804250046011200c4081050701c0a94407403518100303014464100074014a82501d51061944c9020070400c4070400e1409280d0441d80c0000e01d54171916044210032a4000d0201c0080003200d0b919a0030551003d0000300011060301300380006240346000301a19403180788a0b8903035003203507610181000301c22120b10404034103020003c3c80298090302c41020386c0d445203030260582c040007000e40c1800d01c40d860001000c2442540300300001c0c80000c0c1100c054a40055250404603031808142012201038014405220038100074035401d04034240e0300303802141d40d00c152a03c8508141c40c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 263890170 1250 263888920 263888923
    0x314090106050f09043309030c02040e060403020c13060305010e0c01090f080c060c0f1203090f01020708121806090102040303030e0303060f0f010201021c0b01090b0c0d08100b0d061502 81
    0x211805019481481b0720a181d40308584061400081701484036082650800c404604445100c1826800120000144011820b140c4580f41001800c3c81c0282024605960001d554401c1d0f18002401222110602c10118805400030809998071800a1040e036010394000340d511580b03d001540010880540010801032a013015000e80324044003400c4415070440034000c095024144218a238407921180b0000d148050160745042600c3e2064255a4203000043c10b01d0a6a07001c29001c1e03d9104104001c0064055022610020520750154285944920501003c08038202100300c00d800740e181005110003040d8020b00c2038034407a031403c10000302200d0f110780c2d5030b001c1269080e0b0002c46114815030285000303b50421890814400545080c146d00d403040c01e0b03042c2180c0c00c242c85079210302400c40075680251848020f441810755160a09103070b8a82c0130b58540806220b2414000e81c1c001107140b2080100c2d614004d440c8140500d50358181d045203407401810076114a8003000020070307510081174030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 263891420 1250 263890170 263890189
    0x15050601031409060f1009020307030506010f02010e0303060906030a080403030509030d0306050d03030509010209040c020f06130c0902070303060b030702060f0f010609030b060301091e050d05030c0412030314090106050f 96
    0xc4910043c00165103c01d03510303409600c0070b4003620106040c0c240008034001f00c0d00081d0b104100c03559005c0f601c2d04009002405000c034549a140030b690410301c019001c85c900000f074070f500410881e03001d10301c2d40707030040880c0c02e020200e0005444020001000300505811034020f10362203a084e01201d20101481004031300311085401400e90010303a1420802c0468400d400040e040340d41d100005182140000c0081e017202c0c0384ca064180907030048060340038107000611215510915001c9a16803007407950380d130144171122600444451503404560401072501c2a403000c0f000c0e002079500245d880c1010351010b036441e441150000e03400981440010240c014460400d4101c0d41d040c1c890025070340c01d6680c0c464521720003d10080d010741d60398181310003141400030b441a039070702d005202c100e00c8151401c065003418802c50f048418070008000b4071440f05505c80440d0b0854100c040456125100b42ca81200075007024061190b496640d0700070b20510a1040d4080000c84070200d0702c01e1115940303c03052100c1d606 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 263892670 1250 263891420 263891431
    0x904020f0423090f0402181504110f07150915020301030506060f1003020c1f0c0810060c030f0216081b03120d0504050a080f0a03050106020a0c030201030216150506010314 75
    0x8900b9400324581022030b544d00c541041c4010480016030801c0d4207428800303070089848002c3c1104030b20000a1605140c4a54a000b001d09510b0501e4804018029030b40c40c0315402c0000e18003074200e455001085a980c0c00f030004030b41d0201c1c00c4014000d80b045450081d40080c001501e003030141d040030445514000ca031045800001401045440710f1031101900250440c88810403a80154044a0315400038246600c26000c2c0701c1c03500040180551100600c4003800818481188204a00511200d900104007028032030341881c1004c01e2980050003282845007603039101c500e507256288007080c41c030344c081510340d00200c4000e032009220b00550209590340c4840d001400c0317280030801280164010f280c00c13841e0312a004070200d4003096000e9449018941c0705100041180c8804610b0310442c0385d041c01024010640380c8000c180c0811680c40c3e076080b0314214440241415400101c1010704010340141d001c0c000d40100c4241d0900c0003001210000d4502150302c030b80003a2030400b45105450840e03514502a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 263893920 1250 263892670 263892679
    0xc080c03071a280f11030703150e190b04051e070201060e040803060d0f080406090f2d09020408010204090b040e070e0403030b0d050d080108030f090f04020904020f0423 74
    0x4820300000c00300c481001e502050141c84560700710380380400380203686005d0894070241da96850405401011105502050031490b032200d1002c21018100c42110b40d0400308800389841d0444102b0000c6c070052103404c0c1410380160070442045811780c135a0520107881d9804108500803652401d60403800c03115903000d00700540d5440b402080109000c180656802500586520b0300d0780d000d91a5034203c00a20034048480c20720005041c4501c0ea40406c03480e0062440500c020314150800a01180a09214171810801a0000071407000c411040325060001c010101c02103540d03a40303540e0554040e5000c1c0c0900203081c0e0a011450b0a281020300c0b9402c1d0300c152020203440348d80d08200070102d4000c0094015030406403100c44000c0c0320fa543c0034040022520400082240384e50880c0040c1002205901103901c5070001d00204010029000031240360900464a07c01c1441c10b007030016000f40a03c0d04000d420920114204000c00d01410040c0141e680c91034040e404100c05907090400c000c1c195580c2c0e80c21 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 263895170 1250 263893920 263893951
    0x100608010227030703170301140409030c0b06220e011503050d0809120f0a1709030d0c021606180b13050607110d050601090c090e06010509010c080c03071a 68
    0x100c284950305a080c0342d03002400d5410b45562500c40c1c03100d44449002c40300b0141000001006200106292944124000c1e9028001148549c9000d00304184828010300590104000242240e48442e50b445080c0c44c01584440c1c0100e0b0340719004000c04084000304400c0d840c0900d0b185000b10b4072400c46040300d501500814a03100085401c030f0b40d5140291584020b80b148002c0103015941020242011840300c14820351210050440101035030124403464a0300710b00c08080c08078100c000b0080785c5840c8240b96011403c079003d101b04926200000d00591040c070300e40000895010b03407000180305045491810019600d4440c8442412841108035024a500c03800f401008142000300160910b03c6c09015803801c11000c00d800300d0b83e96024024101c0e52a00a40c0c010300c00b0b480075101d41c0080d07200c02c1c905103030307110f0a0031851500c8110203024907061001c040b0f519292a03110b5050100841d6010104a40b6204000ca0650f500d801100040310118a0981402c0c40203200c890a144140742c0700c500071a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 263896420 1250 263895170 263895217
    0xe180c0c070905010303020307150b090123031606030605010503070f0e0103090f030c020901060c081b0c060c0a030801121220010204080601030605151302030601050403020a081006080102 82
    0x4a54844140c1a4090281c0200040d201c0240d1080500843c000d0b00519504d80052800313031100c00f2100c07500070500d0b103043c50064a6450f440159030646403c01e074022400d0001496900300c020341c5410b940d81c1842030191019080e0104048107044808540f030600185494800640c6c3d42d000440e16180010f00c62000c8692013881040c068169903010b050000d4180b0140d11003494007200c2c070300d0550125085c54480011400d000142c2801450303907240c00589014981d94456480c40740d07108408036a9900d10861070301000600800407507107001000c5a40e00c91161400b40c0c1c80341242d6000f50040b604010000800d0f0441d509904030b0181e00c614522944c0d0b003070340404d075100c02e54407620034403584240c00c3c501c2c0d08010900c003d0024200e820024043d0790301d9450310f00c0948000070140d0181d4424514695034580f0707400496070414414190140c2c0744d6a03100c0040740d407402035900c0654000080d41d07000402c0180810311418102c1c0c060b00a00085440d03220650a0307220b040340748200206154a82d15 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 263897670 1250 263896420 263896441
    0x30e12190f021c0303050f07020c03120f041e090b030606060313050717030414060a0e060a11011b120902010816211512030f080a020d1a010e18 63
    0x34210300c003e11071404008090b07000f4483e84003605088020030740d2201880a00294000c0c041c2d800b01c1ca9200404d941a409008684c840036070280d0005003240100e07110303000024235426500035007075481d035412899071040d41900e848071301407180e0b0041902d08682e214050402196061243d5070144c401d1349940c607183d10b40e200156402e501520342d8000d510380403540890240180070220021801591128100f12950b2000013805101510818003001894001c0d908034940c1208071a013110f80781e46880d048070007640c10200324000d540702c95292024192160302d001c0351046080c102c0c1d41c4c86400b021681d49e0400d0440d04002c201a004c2140c04000600d861483c0c000c2c891401001c0c500480a0220b00448030040e1400c001d2205456032144000c24401e124107140700001c2031307514603550507500d00c0d40b80601580031740b08500041024040004c0c201e01ea1940440d40c41c08440e44042100c0200580a90880c204c001031943c006070b20195650701c640f0380380141d1440078a101144a003d516040701c0c20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 263898920 1250 263897670 263897693
    0xc03010f060e0f0411210d0801151e0e010216060201140f060307050603090c0a080706180b0f0a031103150112110405041d070803030a0c09060509040e010b0d030e1219 73
    0x45c50301b82c0190098041004080c01210101c181e95159a1000e505082d9a940310703516011842081041ea52a00c1019456a622072070810517a42402c1d141c00d154100100d04108403c3c4e000d00003091111800965158154010741100154440030a95902c4001c00c200030450241c85141c1d155226071824005450704e6401982c220340f6910456401c070401502040d80506940d0224545410504003041001d800c841e1070410342c85510740140c0221705080300c0e1440c030302854680130413046000c01c941c502c1c240030b03034030251104007a10742260f100d140107012501079405098289000a428400803080c101040c000d0000700d05c90880c00d1800e05080609000007000c1c90041a1030082a1004080d0401c005000210240c00e06002440d07a0f4540381c00008241c1c3c50f003101d0034003003104038001045111313885020703960440c00c11200807444040034030041d07015100c5580065440107040414004050304021100915034040d10180710020305103005a8454921440ba4103c0000240c844030024003825a01e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 263900170 1250 263898920 263898949
    0x906030c090a020d1a030c04110a0f050909010b0d06080102340804080a0611070209040f020111010606090303031b02030a140f0403031710030c06110c03010f060e0f0411 74
    0x103080200007000c607016241c1c040c40c58105c0d501c41c200100142d0605100441c620a41a036041c008050100f1248100784a40d032400c000304840c9088012006115604031040594010240100d958503a2101441035004c5405c68001601e407100006010606000340c42c0b140350071042050420031001881c11107102c03942807842071000c140d801000011001006031028014090003004202d00d81d20b0000215450100c0007a581001480f09500581d586a44580d2056002d00b038803100b4410b80c1300503280f4038201c500c0d0304071039401c061001c03a40e59400601101143e000713980500558420301580c00030113101640d0000182c10800020055500585020b80b03040c44002d09289440c014889100301600140c00c02c40004c0c4074950704115001e4021241030304601001c0320114054034580d14200100910701c10001809102c0c0c80030380c881002030004d0341c1d020b00b019009100305460000d500d0010710f1a402410f2240a044000c40d910421081c45244215070183c503170710341d000c101410854171525110300d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 263901420 1250 263900170 263900191
    0x1080103082a100203010806010b040e15030c0904030e0a120b06060a090b0304060b040f0c0206010510020304170c03070b04061409060d14040209060d0809060901030b0a0e01140906030c09 82
    0x6201c405588108a807072804014010f00607181e5042c49810750900c10182d22500788028107000511242e5094158640c01c15080b0518690401280d000309060011a00c50795500c180c0840420061541090700c101498078104c0741c05e4005c54440e949451030390246480540200c021070000750b084c2c00c1c1100180443d1105040c00101a69901c0680c2e0301d130391040b901100d0700c0740c036002340c940241083d0003241307000080484103101c03400b0000310007540d94005109107072003080c050894600c000c0c001c0c41180c02408160f80c000300b50301821080300745d0b100c4051000c14000d03c180f11000840355101d005036030586041c3d50b641c400e03071000c04d190034295401070142e0582c000c1c0200150192a503d070300c14000b1103514840a00b2041c074082c010070010100c01044240a00e00741900700001542040841c0d1070b040040b6012130b1201d0a880040340140b003c5101d10740c02815820022034001800c00c0d2190403183c4400c030704840142c1603000c0c80349001c0c007602e585405d98000c03004251f6602d010300503c0d501400c0c188 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 263902670 1250 263901420 263901487
    0x1605180f120703120305010f15080c04080106060302071101031b050901090e0f070f0519050d060e041416050a2616060206090a0b010302150903030315040b0108010308 73
    0x203034000d007000d90782d90044401d1813034014240b8919402d8082d841c01003011015200b141845c16024070b00284807542c0c84005c200714040014007c0c606076041d03901803c2400700820a150702d444000d002588030f0320055032802c808900c102c10942c0b00307004411032461091001004a040500d05594030b8101d0110703281800b5055601003049103000001912800d8225007000003030a00d440050b00c4800c40c81c1403102000b0040141551a2a84204031001d0f01180d1500d150745a0a444030707903008003910703003100103034034208010b100900610120745046880e54070242e51a250005021905080380c0e80b140b00d41280071898100304881580c04400c00042d4101e204031804076038843e1484c140340b03030f1992941010308006800c2c800107034104001039218070194024810581c10792180c0040c60814440288038030300e00070030b9130201c01c014026160780c0d140113004c6030f45a007030922000c00a00386480381540100c1c60701680c0030340756203e40e03050740c126a0055465440c1044801900000e82e8000305000066040700c5c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 263903920 1250 263902670 263902699
    0x130b060403030c051c08010620070626100609120b0114040e0f0319032a051204031706060a14090406050612010f051014031b03040b1605180f 62
    0x161702c4003000c0b4081c0c2c0c0d6499071942c1000350103043d101c551070095107001004081d40c003219800281c039000b03452003400c0c600e480b012a10001c030412402c0080d40782e101c1b05030381c00340400d82c4040c4000c00f06854081e11b548101c181c03181d422401060035924054115014040100314503c0202d0704000c6a01000d400030641c6003811007150700d03058030394130b6081c03042d4070000711080110001c2c1f45001707919520345410700c56001c046000a400758050f400300c4000300c1111900783c40090043c0300b29105c5100c48134281460f450b1904010301380003d9441d041140310500800202c461404104503954020b0689400403061210b03204071210303420002c40642c0044d84d44202007081d998500c05030981c603444c0791030303034403958101003070104139125581c0580e0065400d82903100c1c041d85c101d88103080111004420a41381d584405880d4007444c80c42e01c088845000000a2005000c0c40c0883c65100d54420098074080c0e0f460f5080803146403048403141400340f0041c000d207415034a0b044064005e1050014499207004600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 263905170 1250 263903920 263903953
    0x9040204080109140d0f020a02150c0d0809070f080d080a0e0703060504060c02160e041b060c030f08060a090207060e0111070c080a02090403032c01020702130b060403030c05 76
    0x10319a0584812400810030104407208011045c4400741c0f030310b0030208400003400c019554040b0504000d20800c2201070440c400c3c0710300b4054418408009045030000c00c20400054050782c0c0c280c84c140014000d0400100703250420111100c2221076860003000d100f1a40b031401c030f03820940500020740e170750b8032000c0c0681842c40402a080156018010002d0203041902e030070f80c11581842900d1041d90002602110701405c603000d0101100c90300416200c4640d16480c00c03070b0300e02d000e4003208100e0907c541804242e042e0722200d0307001202d02c6a2102040302e02959020349418130220b0b40254000305041c800d20600c035150700508440b920800010615001442000d402d44403201c0300e40000210101d124410312001c01d60240081861501403e00e130107994000c0361080000800140606880300b1007a41c1050307140c000c0c0300c0d0200010b480c041c0c01002c0d14503814003075030040409a20440e10010f01071200007262161422190700145101d182c1031540d6800d9400d4100d40c10252224001c0b040d100001035003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 263906420 1250 263905170 263905181
    0x10f0e0f1809010b0a05030c15030a09060903051c1b0e060d020412120c030546020d050903100e0a0c300b0403032d0209280605090402040801 62
    0x82e0400110b4011907200c1880340c3c1d1441a80314522960015050718603075100c3c880352001000000043c079030340340d071041d02c11000b03403080391030090050340b900151905156004001c2d01c00e04050503580300207503098400750429260901d00142c442c050080d00c0901250140c10900161030001d0b0611781081082a4254100c0c0c0081c1d00414029801201120030000152003c40006a0b541440000c0a0042d20007c109001d02c121000c2107840c00d441c00e5503158080e090380440c41c0000300741403c07407000c0c0424002803441348619110143c89141c42218600f400380050b10300a0001074002c0540f82c203d07035480000b40810203450212030150320790840c0450034a40444001d40341818110404414040898143e18201c06024801701c81c0301440e00c0000e40380404a83d000740d054a404280629503035035501c0b0003a420700400c06203800d2501c07a650948030035005083d10f100200d8603101c07003540d401e0a2641020b801e0200480c11250000140300c01c50003a030203483e0403503000d0801030425490745040c2d4211030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 263907670 1250 263906420 263906431
    0x102150a140f041b080a1b05030607030903030e010c0c02040c03110304051c0503150d03050f0c0705180601050708030c1632030403020607110303070f03080105010f0e0f18 75
    0x1e20800820080c8020310350700074039649640030600d00f110b140141c0e01e034460744000402041001107011103c1c4540007d1440d0307020301401420b880081c100644050014004180c08501203410b00030803109003031040c0709a0103a00c03019103601f1002c410756400c01000703144c83c219020901da514105001c00200071005188543c3c403c600a19140c0500d1030304123400400d40d078815041150800400214090000100b1005001552030a0340c24000d80b4043e11540a00c024070b90b43c100300883c04482c140800a042e0040780da05440d100030700e9400500d07402c84a90200d89250119030200013600001b14188021503004591400441c00c141c00e0943e1a640c01043d03003811f03591721079613940b130b80c22000c41d0808188030b081d020551424205501501c0940300e000d00c0c07001902c5840c01141507414448031520401500e00000c06585e9500c102c0d1601802501d410306042c1d0001d0314050000c645940141030109107503940361940c0e003202d0030400c00c01c00c08034405841c0540110718039800f40c036401c544a050303a0280303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 263908920 1250 263907670 263907691
    0x1030506120d200d1d0a09050a0b131a0108070c230f0c100c03030902060705160902130302040525020f010c0519140f070804090c0503060102150a14 65
    0x600c1c921003102c0c0c078481d091203412450700071540c1d6420303e1760041c445501c0e032500c400c54816036200c16000912209000d80c0440340340c5041204026042c04aa840101c3c0160211072040301039841c0c101724070031103004ca54100722601e0002100031296000b01910fa501030303110300d800345511400b41e9822000f034000a50002c203080c0c0352584444210300a1142030507a05d4030f107000305080c1a403580003e0505001c102c45e0b105004694894030117141c4242c00c460041500034081c0d540d038220a10b8510341e901101d1511032250207200002003040203050080720001c0302c2e03410b8040071031410340c0c0030000108401b5000804510315461314460152104000481a9900da0050528203007040b1403142580d1800b11312070100402003021984001000d00e05e032180c070b030440c5040a13003034492034181e417440c1c864054880300c0030101003012420809540024800d8030300d180810b00150308910703416900c2d400195400d0b800340e0003042d006901c0b180d00025035548085421000310320850485040503c4460558001045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 263910170 1250 263908920 263908937
    0x2091f0804020108070e01090e071b050304090b100903240c081b070323041809060b041107140309100306051503040c0605070213060602010f06080d0207030201030506120d 75
    0x20756812510140d03020340d55007000f60400c6606c4c03000802c10302580c082c0d0800754440c032021518403803280c4000880b455051191000c0e540c03090400a40c2c035003062244042c240d0601a2014441c1442041c00c0744060654070b500c2c10b17103811544d4620a0f020040301c11402c0d01040c11080e003d0a8240c0101e14030310303089449032441030805428511801509074000034240108001f1440000c1c1d200100c41e502442d5803145800205520f01909a580300d5907020b600305800c02820030314210b005501005146200302420000100c3e9030b0240000d842e4810280c210002c0d051182c1c3d0b02290795500904805c0f50074005036031a0401500000318003105105524002940e20fa20901007400d01d40511950320a2192140d411468140c5d00c41030015868002d00b0100f09000c50303190215203854a03890b88030f0f00942d0051002c0e580310b200007402071401c2c4d418100c5007418240d0005500c41d0100702c60842504d640c0c0500055815500150081c01c005002e40390000c44085404007101414407500007002543c1c0c1e0350001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 263911420 1250 263910170 263910173
    0x30c0b01170f0f19021908030a08101a0c0705090a06090605040e030406110703081206040f06080d0e130203040501021e03010e01150507050601060806040608010e070902091f0804 78
    0x181541c0b080041025512540064032810800640c200300c10a804444216110103440402c0e010110603000161100c04443c011804160100241404d40441da640350881d5480e01c00c10000240544a440c04401e4182e109503103030241c41d001000100150000c5907901d03545d030130125079071500494405017402d5449005001c1c49505002e0880101400c650030f0044842085d14a40c07030b88101d1240c0402c0c042940082ca48a00e0f00b40840b00055802110850312041c40c4685030741d965404070742141c411442c090811000b40800e1243d4404d5406990080c0848111103d0a445400c020301050b648440e000902a55030308490004500c1503100300005038840661101ea2010404c190381c0c4030005100c140014004102ea48080300d0454950065900038104201d1041d115445460800741590081000100380b064005034454005c080a030f50401a1980e40c40e034a5080fa0b181c0c2c08507001c1c5400c20102000321540c0c40e0040d00d8100030080918007022100c0d440402194409501100440c1101c0308110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 263912670 1250 263911420 263911423
    0x210901020705040207150b180405030306091609090b010201060302040204241d0103021602060307030e120a080f04061e0c0311160f111002030316090503060c07030c0b0117 75
    0xd00003940c3c19800c03c00140d079407403401d8000020741c590490356088400030b640d50308402600c04805010711440c4904080c14050f44a51045a216000f808082c005c00e2202c4041c00c54407080d8000782e69890103040c20802410043e01d034002840e411507403254000301c00350b42c95100400003002801030380402c488251080c1d03040452840da1034414000740340c0c0e80406100c0d5014a07a2190202403030010780e1201000f50111402c0348250001e500a1800b1040001042c0c148c2e00075403140380c4ac84200c91000e02d000200800d00d00c111800d8030009421071f008a0850210404010b401034031808c0042101c8201d441c0039a2103882401d901c01e9002d03100e4000c0841c09070584a407183c181006c91050740707491601c2c121500c42c107094050041a403c503240c8880c0074842c1248003210103c2e401060341400b24410540295290800d58044090380d00d640410a216405000c0580850f403010b0040e005039564203016810a4120380c1003a801c0c400060003130400030f0a4100700700c0c040d2042500306c0c0301e59a0300c4800c03035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 263913920 1250 263912670 263912683
    0x2e030b0708040c14030106090914010b041811030c060f030a0b06070c060e010e101706030c012708121b1b0f060c0d08041202150403050c21090102 64
    0x60015000c00d100100e1040851036041d540081c84004c5000304001c04a0300400c001d50000c5c1c0868540484001080b16281491100003141d000030300c03004000b0810041151102c0740e0036441541070078a5800004c800700a40c2800c000700074140da2400700d0b2040865280d80c4112140f80d8008000810810f00c1ca00900c682a0b03101d00507600d15042601daaa1442e00c03455140c0070720014403030740c7c80b0943d02c541c4c8110741d04016610058601c4001d18a0b100c800790050007c46425009401c03801d0026480d818001800128040c0580d40c1902040f070713141111f03420301d072000b00168130600e200c4400b0407130b070030100300d451740060782e0724003c668503101091040b036010701c402e101a2068212040001a640c00e032403003064151812500c0640d400c440000180c0c2c0c41c8102c25004840c4c0c0540d401003004107400c102001d10403801404855964900780c00704988031a18411515600e009110205000c82c0c03082010f00004e42130b450031905c410003904041c030703000c600c03c0718060000c110020751a00c0300d50b811b0007217 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 263915170 1250 263913920 263913931
    0x17250206010b030f0a150f0f14030307030503061302030f06100f0206070e0604030204050108010507030501121509030c0204050405060103031107141c200306070f0c06052e030b 77
    0x90300e629410080820058400a4590441c480c10b12020034038070300c4e456122110220090002c101c555a9035010a00c082e0301c18802c00c10198001f0000083e03950140110707c4407008003c0c00b44d40352910030398003910b050300060010760700000008256181090284011405207024a01c1502d5a01d0020304121900100c4020001041814581220103d80002d4000e80001e49410710075409a00c0d00085862400380340d1019520500705000081c100e20103601c45409554641d07801d014580e2194040e11240030241f40080c0380c440c42c00098400e20308281e01c0068401d110b40360600300c07032065400050940b8000d4400345d40359040b4000401c1019084011a024000d0703610140075054074055080802e04a1880c0260081002407902d481110301200000520307a440100f009400c440c1d076011102c4d000705012424040c3c4907009c00700303841602a20402c0e440406a60b6102c0c01c01401d50303203000107070201074400d19401603103c00410041c210b0408841504481b816206070440ca541840c801101c000fa15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 263916420 1250 263915170 263915173
    0x40b0c09010e01030b0f04020711030f030906030705031e04030f080f0112032102040608040c0501030216020d0501090803070f0201060f12020907120c031d0c06160201172502 76
    0x1110403240d0b000940d07074440501c00d003400a82d1014240111301c003000000400781c3d106200280d040208246804a182c07140800e0b4112442441c0f00d88010340da03885041c040c19030000040c00024540c0303200d8401035a20588907650303030061034140800b44584140c240d4045000c504510900048282d000f0b44480d404501103c03407480c20b5240060b5000780c460f04503c05020030494031064002112750148000b95500c18103003c643e202e65034500104505003c2e43d0466194150f41d600160940c428000e40d940300707600404101050765183c0c200140f00a000504035920f5407124820004a000000a1841081e00e9100d201c0c2140740760b94020b085581d0307600185442d180c401014812070642244c400815941070321014400e4940490a4643d01c0b4000001200e040c206482100480c0c2d150b0441d02e0101d200e03000f0010031480c61021592079a1401d11111742004050003a600b650000c00901111035006050040329101e80c10b0010880729001c0f120b425542d05200100064a0320031000220008043d20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 263917670 1250 263916420 263916427
    0xa080a05041212080f0f070302070206070f060b011101090b181f0213050a08210d0c090603110c120a21060e0f0408070b06013b010507080d0905070f0e040b0c 69
    0x1b040c4c66050801500304000c050303001c83c01c40d003152600303811690304641102040b4071420661070f11030041c0cd00320324098000303050456080b03584041400340580095101450900340e5850036480180094410395803405e501c41c0003004503090006124651641d10302003170250341d82c2c65145601d03500c000c40f9800a40100e0300740404002900c004a02c1000d00e40c0740c0400f0200c115070445400900c0e0107a000580c10451902c5440d0f400c0a402406810858849071814024071002070f820714518003454420301c40503000301c44400d400d010044014101500c81e03080242d10040511100c1c00d040400300035501c42c0d259110750070b0003840d01d040001a809400350000492618007681e4405a5001c0c07410300410b510403c00c0070a40c00e80c0510018034183c80d0f00310300d03d503010965041c0540d02c4d9001803001408400040000107995120303c00f2540d02907000141180f030850549a603500901c80780c0020f44490042c501c0c00b2038200003120f481c0c0020205040744010798106820404908500a00310f00380c03025040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 263918920 1250 263917670 263917681
    0x10c02120f0318070806090c0607110118090606052206120e0a0204290901150507140d020a05070e04030e09190516020105060607050a080a05041212080f 67
    0x1007220601d008801c0c0c000e8907030300c03180315400d440e0070300700110b9849000c2c49801040c0c0c078600141d454882c5a550b021a05600d08070800d228540c441c550010b00b0046002015042c01e5014543e00050142e02001e180107165999078450b0441e002c44c1c02c010001180080e1360072803c0210441c02c01e1030004840d20034280c0d842c01802034150b010428518050648440c6520100e03034090101c0b06040341c0240003480810082200343c211a140b076503580362040e20801803040181419100f4605940b080c400d030a20681c2000e00640311608502400c0b10441c01030940340c102c502091090780010343c0150002e1441c0c502a00d402428082150003104030900034030100030200703600030020900340314180c40440700b9884500cae0500328010466144299070b400c12040c45413400414200e04408003050f8020841e9031036400401c00284900700025103698002c0307200c1004550800f0007014114000d041c00c40c40c041c0d980002ea02142101041644d490b221071460302c138907941144949520100d042d14480d040e2a01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 263920170 1250 263918920 263918953
    0x150612020a0e0d0503041208040611060c0405010e06090a0e16020c060702060a020312010314100e030a0f020a0b070c0c0905071409010c02060403320601050d11061803010c02 76
    0x401c16040c807900c441e11440c003d01c04c0034000c4a001e8050760766200070401c01c6003002c944991084c426040000c100c0d125100721040702084490041400070709003441e0030b24040044600861108501c3c5e4800c40800101c620355403000c103c003000f0060f104075101c0924091170380480030160500110195000300d103242c01c155407000200d80101d0350403205140c45000d0520304910310f004990302111404c0e80307800040180920050a00c03c0400c80504980813008400810000d40e8508000409c0642c0f0520022050a000f4801c2034102c44283c811545400c41c00d0301c5082c2c0c40b10080d10b01101240c020340d03000723060245180700300010380a0785500744140e0401c40e0009003403070b040b103000303907002c001c0800c640b2410380c810707241081940e0300200000d445070346170700b0002c01c1c0702810b0b1271110307408031601c494000003171601d60103004598011001e080d1503880c140c14401a0404100d084136030400703100301c2001d0b41c3d44503009017038011000020407504aa02c00141421246d074600384034259481904c5410f8450030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 263921420 1250 263920170 263920187
    0x3060e0712030c0c0905070c02030f070b1611280e0c2b060611010e010c050d05070e04020c010e0d020c033a080703050c03060a0b1606150612020a 64
    0x51528007005983e01c02d0610300104840ca41201c07041e01d0a020610019035404480e0f001424000c17000e84503c211004041c5d60303905002d04c10941152018492442401c0000e1850310006d40990520509102c8070000181c000c04000a5000340104088104081440034001131028000540013040c45003803410b0b208440e03000e42c9046181401d01201c0404000c030700020000c200e00d040e48000d12800d51104030281c40c00c245003410741c09562a10708000080701c814024050f140c03103e070302c078039240048000768040034000007007940d000e206001c68140f00750303100e034402045521000f2000103413595030a01054241600e9071f560104540c4084010f01e07203540c1c04500007107811110400080c480340c46203081c01034004041040784e9981c08410700c0c40d21223500496414880c0c182a5000c00c010744e10621040030074003054074a56004401c003403043c0700382d203400380040030001040c42e100412081141c0d162810ba80d50380b44c40c00b074180c00740c0e0342c200716243d007054a111031001010029802d2442400c402808600d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 263922670 1250 263921420 263921423
    0x706030e01111c150810050f2a07020901061d010f020c01050a090b0a08010617070f030207030c0c1e050306090a3002070e060102011b0f052203060e0712 67
    0xc1c0120640401a400c3e82d01c650b400c402070780021070400351360f203100701c0d11600322001c003402e040e041c0740000b20a00040c02e4100d2288002541030742480128401d08102140125442c2d04405010400f41000d41c2d03410242500030aa41c4e40c3c2d8102c401d00b40c1e00c812001d510601030701070500c503a24540074021600494051651175083c43d0054488155a904440d00100c540c1308a0301407000283d90300c1c0481d0f00900c01030590780030380c84003501110b51540c480d840590481c0e54000040441c1510ba400c0e0384a03800410071320b4028a0040b112894549504005050590006100041c2e0384070100106842004403070040004401805d0286401152241c0304c55018500805060100e0381109100486040c58612140440c5099401800350100655150094011440c00c200310b00c000422561050003803841000c82e0b84110740050f0013035002030b0303940c02410ac030040620400703018500400952040c14a070100d1380b03010085d2781d1459828aa01110501c102e00c29090f001030106102182c80074140314500d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 263923920 1250 263922670 263922697
    0xf01020c3307030e01020d061e050d080706111c0903020f0102090a09050a06170114060f01020d0807120c020a1a0f04080304020d060501031113020315060f04050d050706030e0111 78
    0x10141c504460091055480c0d01c0a941e02d01803010410182c09c1013410b100450101144050a803a8400c00040d0640d0240c01440700004001c1540004c0041d041400d102c1c0c0f803d11030a0400901485030034041c00c254000d0074070326076030742c0c03030107042c1641007141c18804100307003008520f02500d07c00419030344542401206041511100070403060203840d841131000300a10400c0510f01c112210001c0c0c00390450301c4070f6001c011000d0303020440a2900c0d042d1408802d1058004221222405000740c3e45840c0060540d000d000b1090450404c1c102a0301408a00707440079800b500720300c2e11500c0e008800002c3d07481ca01c80c849617840200125101e0899a2a0f002a004460300340c8941d203910009100c0080c0e41c0d0014410713420400004204282c240901e46920401c0394900841e03584154203100b240011140b903607150780449412951070400361300a00c001120008400d16154681010840070928500e08541c1170b80001701c10080b440d4984603030400084545c000f40485540c1101e02030035805000a6030303800313 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 263925170 1250 263923920 263923931
    0x40302100b060a260c040807062d0e0a08010606080c0408030f1602061207030c14090f060403021005090916050a0f030b09010602010e0c060717030402030f01020c330703 74
    0x442e8503081042104c03220369004810a18180740841000d402c28469076006104508000c90420f0227030300f10145040e41c4c00e10b001d80b001030000194050100500119081c0404609005c81584404170203a0240052030004034070a450060300400d040c1d0000c0607403410360024881032100050120880388000c00001000703440f075030700b048040110380d502440254454000120200410641d802080c410000703914100b10811103c3c00550340800010707402264283c0800015115241c1103681900240f80500400c0c20180c0b40d90105510003007032000080800c40c0482e444203607107411182e0550000002c0c60110324181c0002d8045d100780a59500c84051041007140e616206209600409132624001c0902c00f40e543c0d41c10029008100709403400d00d10f400b9401003240941803102c101c695060780000c3d0201002411624080c19030800b41c82281e042c010030500c0c1e504440c00340090848841da0102420841e80b604500c3c5a40421001c2200641c40320181022082422464041d0303112545040c003240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 263926420 1250 263925170 263925197
    0x18140c09040507060810121506090c080123130510060c0f060f090f0c03020307091418011506090501080105010903051905010b0d0b0103020a0503010b0a0605070c031406040302100b060a 81
    0x3206e406810449400020b40300c0801804181d4042880c44000b081080042c980c80304e44100540b412005510040707015207004111f1220034034841000726801194040c281c0381074a002428401e081c07401c10840d1500c680c280040001000c8070300009140d030b407c00301c48100080d600c01942c038480b203202070a46544d99880c04084c0f40640c1004580540c03000c1c01c09088102c83c50701000381c4806000503402449205404180c094240c801e400c01c0d010503100001280d981c1407410300c40e10742c1d1481034120315500c4d14000b40503800d100c0a080c1c060089071701c50111440c10000010000c8105038003541c10803045810405c0402c1002c60310740c3d4048403800100d81075581c0d60070b03c01c0c09048104000b0f500102048002d900348000a85604d0589108480e51400141d0b600201400d890005d001c00d944540c0344102001000c0c0200d009100841c0305250511b65141c1e80d444181da184c20382080da1195401c614100820140d042c405524081460801040f00341260004584e00e0f000e114600703400c1c489070071000b03070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 263927670 1250 263926420 263926441
    0x5100501021c140a05030411091b07060b04020f04030501050603060f06090618010b1b07060801050d061b0c060b10090620010c0201060303020d0206090a020607020418140c090405070608 81
    0x1e45500019203c40d0b5a404200e0f001801c3c1c2d0b04c1200d05a1710b50400e009031416500c3c110a0960260054509400400307038010403a006c1c55122800c1141d00356621100b04046888500182290516640301540c581e840d60401509450009001d00d01c250009410440c03020184a07005400c081d00740c80741e8001d50780344000300b8030170b0b50f55600000d54144030400000782c000511009040984991100400c101450041d081d034881c1540122404204108014040381c2011f421000a05000300d401082c2040c5210070030541038032501c04100014502c003100b03020b001590244006d0103100ba12000d1200c20303110b41c02086511580109810801a1180025005030b4601d02203450034040000b0041000d0000002c0c3c0201358900c0201c016004000700c900d80c06001180e100d11980307648001d03044032451942001681e038042c103422a8081e80e540c6501d01d0003c0d01155100d0b841d03210780c08580d200f0094021445c5041e0b4001c6515100d04051420800094008541c5904a540c6401d08482c45d407240b04000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 263928920 1250 263927670 263927687
    0x30c031315050f0108070611030316051b01020909130b07030507020a320d120c03020705030c060f060f030a0209040507030524010b09011b06020f070308040605100501021c 75
    0x1041d4604010a0007110340003280540d04070340c5c1041c12212019950300e01a9500780340a04410b295030400d000207080b90140071019640140146040c61a1243c4040c0c03131502d44440040120389a075010403035034150304264284503040505140610001d14859a50200c54440209882e0402d070315440800c041c2802045851000c683c885040b2114000300d9a11480e10700d0b4680700c05044001c4401006c24028021550410341c9001b80e072a01d000d10140e48605000d400703011404001c066080205601190060000c0c0805c2d1a000000d0801420103030240412000c01400310380c800c9100f07180c800140d40e80004c1c44a00c00798181d0300e52200d5919402c0c05410040e0a0303001030194050414061104035460b40c00380c41c0c0071418600300d00b5907600d0b50710040282c0242ca02d1103011400700d1850a900c5042200d9900000340700c1c20016103070000c010301c1c48100e50803211007100440e507440244410001e0b039006041d40190742003410040c1e41d26241c0002e5071140700c804a05200c2c48400b40c103901142c81410703603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 263930170 1250 263928920 263928953
    0x1b100f030b060c010b0a0b0309030301060e031912030501090b0d021315060f1106070c11121b03010f0b10180306020307080702150114040e0c120706080705030c0313 72
    0x4070703a2605800403070503010b0400703128100d00c034000715240410480461070641c2c1c0144d49e01e0b4011411a821b02206942c6031668420059143c8151540320121200745420303c40e18900c140408000c480441502030260792042c3c009000c0241014079900b202d444d601602d1100b0754044a801045001c4010b4040040044983c0f00b0000c5804a902162803900444a13038000a001c1d9070300a5141001c00d0801d032984402d0342e400000403032a000c400007081e0b000c000b08000110050201c59170f0381c1220304941c0303468604400003140d07101c5c1c640b0101092400780309601c00c0c4460448144680000c10000400e100c001020b048140280c0c000590451101c1140b07c002841d4402e108560340d04241c9000742c1001f0301210b19000510601c4151283c0c0c1c0b0005070f6003412900307a03a0703010790011180020480504104410181244600030801c0d0099071207064104800d28103002500ca01414500c00400c036143c0141000c09103c0100b09000c1b81d074840f0012258130603c036120380d4200a07203038a050003810700070300304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 263931420 1250 263930170 263930179
    0x1f0207030206070905060f0f0c070807050a140904020d03050d090308181203011a1905070606050301020c0a0b090a0c2417011208041203030608010c0f0c02040b040e1e1b100f030b 78
    0x30301040c41d0400033030680c1035502c1101e11328407866442c80f200d08010b06641040b0740040c03918000ca001400d0034041525424442d040007400c0c0300070720881404840d81c4040a800154121082c000e1400803903014986011010f03028160400240c4001d02041c4018810310450314025008500740003040015150262060083c0380a81401400000c00307580000d2000d95103903203425000581441c052013201e4000c034000001d0107400b4400c0d10b03201486007000300300c18012f01560080c60300043c042032401d0050034841915505070351000c0408103207014640b40650600c40240900740398502c1103070075a41150134418000035408401d00c3c001c9a580616030010300d024503c481a0420075030150004000d0394429070081040031a9001e00700c500c15a4a100d44c000700700b0112101000d41850707040180700b06000b4201092030201c081c540d030f10b0174165a06d8040328042841010f04010400d214815038000300e003071105c017200c1a44002440550074014084140b00c444201c041101d40650030402c0820001003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 263932670 1250 263931420 263931433
    0x3060109060501090b0c0c040b0a08071d1005010c0b040f081207180506040e15100512090d050d1d0f010903030b0618090403021f0207030206070905060f0f0c 69
    0x20500c4001c0c241034014240407404502000c40c40780560710540d50040c081070028864903d03040f00340401480000c0c80580c0084800c400402c3e108002c100311130041500c0c1d80040309910302091424070420f0090140304105503035242c00c1003660b80c040b102e052101d800090300b0300b4589a9151040101443c2c4600500003100483c503401c0008103091942e10030441ca44070342400790140d16141003081800d003c1c04c0e5102100784418002c4824540045521145048151800651030070002d4808c1d290a441c2c0f100249000440141541404050a81120045000b006054410f21000c0c0c074501888902d54242071f07840f8040c592030800d80900740300e000d1401045d0390034a0440c900450181594050a401080c14052034188600b0120104c962032883e040c138000780701880104005d900e01d4041c10550442c4110380c10754005120001090180b48240c03003005a44110030320300a810840c008001030b0a00c455120200035645a04080340e003d550417840084c1d90f290000f21410030f90152084101440c031400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 263933920 1250 263932670 263932679
    0xd060617070207080303012303030c06250e0409050316030504060f080903032a0d050406050c030702061f120609050c0d031b0606030b0405150702011413050c030601 72
    0x18410540e19800d0310306040d03680e01c15900b40d0fa220074500c50390b40c40c0c0d801000108491861501c0084550b00c40301c040215054400b80000c1c619048618500400e801040511040b400d1485003c102710301031141c40c0b050115001005041d00004885060090351240c201c003003000418400c580c400741c1408149112445907040060007038100c0d001c2c21002c10052049010380c01c0c0141546841004150025441c5a603070009149810484218030b0484640c180e40300c21109403100c3c0a01011400701c20000740510781410614140c0344042d00c400c450709400c009009849034007107000d40e4003014101d510700281202040003220310080d0f902c031540018050a080c410080160006550f040c000ca0441e80b00d070440074100541e40c096541c00601086020480b07001c0c0310314190b014200301c6e000380c5c000a03080b9506e44030343e02e0403101101c0854564024035030389032031000c010100342d07081803480c8000c00c100800d400e50746d024902c0203030030103003d21007a040b43c0d010090100031600003800701600392915543c0d00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 263935170 1250 263933920 263933927
    0x302030f0d29030f1603080901090b03190b0d0510051b0703200105010b031b1c0e21040e040c091d1507080a1a04020a05040e0604060b1e0d0606 63
    0x1410403035842406180394020718070100103011390710a995001178490b45442c541e6899130310fa120712021818040d10000005980900c000070318440c07003c54501c11408410518500101d0311524103e902c580055444507020560002c1d40b0911414178142c005200c0c0ca450f10410a800e81c04121100e000760300184880c20564880c0d640c440050041c640d04c842420104507140c00c0e90400d004460381103030140000360b5000001407502000d0b50003854034514144011090310800502c40c0d070710703c1c03e0903142c56440203038442c200500118900c646001c034600c503000d11848407172841341d80325440c2d401c00b0640108090040d00d2103820700508034104100507102d80d0320b00414149048400c920458003610303c2c0c24226010700d040e414410b17074061399000e001d6907940202d40002c1000314000d910540801308821142e40b81e41c4010000080a5169551030b00d00c4c1001d01d90604e4001850a400740e1704101003041a040c031401035030400c0c40d110b00b1140401e4500d1640c0d1040d40120140b0800d0f450070450002681c3e0382 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 263936420 1250 263935170 263935241
    0x60f0b07030801050406030b060105070303090204090f120306082e0c09080f010504120c030c0f0b1801020f04030b0702030f130e0f0907031403070510270302030f0d 72
    0x719407148142d40ea640c20400c800c8810600c0094140c000e0310000840030361042c0c004000041c40b82c10005020780868010a045400f40c04048800b00f0000c2d01800a00c0310601c00415452854502401a0790034540c206859100c0c842c81620100c1c450030703e18400082c61041041140303d1100c040000c4511654010541c03007540c410036007580a030801c00d039a144010b00429101d545c12455500e000e80b1641c004039805a4015010f8080100301e48400000451744250b40303c800c0d020b4101d024031824004488000765144e400d46d0040e603031040000101c036410a1040c0d808a0760840c807100080d50b80c07080107900f1481000c0d030002582c003001030f5a80c68007100c800b42100303942000400801d1590b44801e581ca80c10025210001e444e88001c900b040080c1681080e100c40343c3c200b07800d5909001d11650f50742c2c40c000b0b541100040050b20740d000709801d80e24050303c41890885443d074070303501d451036514007a42300d2103020304040e042400042c0c542540c0e02150051844403d1803088002d045000d138007481921a0f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 263937670 1250 263936420 263936423
    0x3040b0d1b02030406140d02070501180302060106020705011407030e0604080106030b01050904030816050415030203090f0604020a0e0a151701151d06180f18030a0e06030a060f0b07 79
    0x10912080d80a40d0761001040c1c03019110305031030701d07002214100d6036503c15402403280511099000c000440c0054020700072204124451501401012000d1030007905161058000e1011944460401c0041c2d0b030303110514400e0f01080721010340e030301c400f5820211040c21040c58600d130031410000300043d2660055100c00101c074000c03a0003541d980d80b11000c00003030070010f54003d000210008003051516044442d940003c1146c0d007411031401d0f03a2010484162622031540b40302180e1b0200030407a40303500c00c0c80132460315000040546140d10740344e400114240c125002e01d2485400fa00d000030a02016540a0200301400d02e81e04440603030f03500703078030400d0601c04020300920b5400d00c846d440f060541c00d9250016038030281d680904070200408105d86000009201c103600100c0c002202d08601509120203000d04842e82500c61185010381d107110341e0350b41a400340104c6500030400c419855600c4070081c00220412580f565413500d800581d18040c14040e007000440c12600400000d5100e1038078028040305 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 263938920 1250 263937670 263937701
    0x210801032f0609280e0a06080d050c12030c04081b013e0102040303020f0c0f0111101406010e0d0b04020f060705060403080105011407050a1403040b0d 66
    0x41481c40c4800340107118500140000740d01c02488526a80703442e002a25402101030103240c40c11503000c0030b400c0020030a00f0010901d5404080600000318035009499116907030030020b100041c03826080a42d9200046d141404015001c100d40144000620503103900002d020095522410002003503101c1c1d500622a5503598410340b144440c043d4043c111100036040b058485100b01c207103190145000070800c00c030340b4918000301e102940294141400c085e1482d0600800107031528210b00c3c0c0a45019000500c4000311303071200f0103081c055515451003280001c03082ca0800c103280117580c120b600d07040090100d41207960400d0308550b0b00003050303000c031031040c1000d90342c15140904042c02d005010365001d0000c2c0c43c080d05070300081c0241c100004040c028180240c4010710b40305440e00c0341820810103543c00c800241030321004004643c0d12104820780c444c500d5408529095095039299540e049416000380705622078400c12454131014016500288242500d403643c604400389403e008146620411404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 263940170 1250 263938920 263938943
    0x313051005061f120e1e07060f17061302120a0912090305030d1d0d02060106080609010806070c05030f0a0207051002120d0e0703020a030f06060902210421080103 71
    0x8160300115074140c01c0b2a11046540009044c1c59005400c1c4001c807802030344100140c032403030701140d500c0504d118040440070703007585414004018000c0100c030300c5101c00c0015049074490400d5220070ba5942114084521030244c00380006d40001901481d00d040c0526402d00c0300f040211368141e080102d410b4411200300f10400030000303041d1085c0c10035000c050040c0c1e0041c0440c5010964a0b4044c04103107039054001c0f00117404032581245040075210419006030842c40041022640140308140c000f5002c0f106d40e411076040c07442180d61407800404071010401e030400580c0c03e00105104451074811014911a5a0228034030081d589091920a00707000f1468075400410b01480890085500f10a032040640b0b044620484040503000d6500104498060200004016540c1d80c10f1100218482d1040b003641e0703251402c041044820552000b1801d500402c031940c4601c0d074501d40e6040c0384003011805891501c40d0f08100f090842c0c001ca00b2024018000d00000103030340c028134041d040b40c1c8606600c065 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 263941420 1250 263940170 263940199
    0x180203010c0201180303020304022e02010e070302010507030e0103060b030a020c070e0405030405091801051e0a0905031e07020d0503090319020f060307030e0601060503180a08030606031305100506 86
    0x880c1e1390101d0001c01c0c644e89003403400010380700c0e400443d08680000d01414a0003690740012101030002c035080c0c04a00000740f425000542c085c016500103090030000b4000e064a10340010b04240700e41000103042201000c000c1c4010b80c0070b03034417007009003151010640c0c9a04d00825000004d620815011241d40709082000a500c032040000500c219485005541000d2404051203091000030340302103021503140f000d07800b200320244500b9210b10700690601da0500c42d80401c1d2104408045c00e0140c10038180740c00007000c1100003080340c1c52840520746420105000c0030f0030b4945c3d401414030003540080390082e4001480000000ba0404500840c1900c41c2400d5078940140e40080c8902c000b0342040c000000e540740352500c00301855112002c0c1c200410090a0220701c0e0741400e0098000001141011040c8000d21006c2c50034444160100002084c0c0c0034616121120140402000203100b940000005100d0300b14166410380c0090b802000c039004054403441a0016000840d141c82c01610000503462 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 263942670 1250 263941420 263941423
    0x50a12090501110c0f160306020345162c0916050d330906020d0c080114060702041b08010608070504030507050405041a0709030219030305161e0b0f101a07020102070306180203010c02 80
    0x80e075807523301c0c025101107160090074801e5003c4003801c0032082e810b014545040848240d40d25100d4000d4002130b0070004440c04034000408120341216004084104249001030662081600c04140b01015040000005440c0001200a80740305245490910300e0300c0d01004455006042e04903030842041c4500040001c0031661a0f50074490060300e0103500c100e103038143c28800d0092144034001b802c041440b0406051182e0722188030b00c0c80741c000903584401000ba8681c86043c154211a43e8540301f4501403850b21199614200d0303004161103250b48001140c1001024240d40c00000103c409000c101d280a200c0609406500d1000340c0c06410780141201c43c5100b11054501a240d1603200c60b8104008045071400c040100c820407254801c602c46007041307070214280544109031080951075401c0c90000d540c07031940d0f5809030600c00c1d24000041c051040c25511415035118020700305419449112a0004030710300b00c1c0c00c2c0d1028000c0c61412104648058420360403040880c000c1d80248114071061a00b00e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 263943920 1250 263942670 263942683
    0x31b010c09090504020112020301030818030105060f040e030c0601030b0f101503090201091703041e080c01051309150303030e0d050a12090501110c0f160306020345 72
    0x100050141c078040c081000349034081504940185484051400c642031a00304903807080c3c0054842600118040384403c036007a998002010f4190000c3c449030030300d8804240025603988503280704580b100c11603e0385d030b1401c01c00c4e10000b520f1035048449070f594a081c00d482c5114140d5000503000c078004002580d01c8035821038401200c01905d030708203415003000390807801050541002ca0401c08100740005560742031001d00c580b0301d000d80c8091640c0c2ca203481f644038040c82422542c0403041c0801f41042010b0300700440e410440100c00c0c200359a603040564510281c0e40380c25004444400c1c07402c4622031004100200410507644603441c00c100b096000503440e0b030380d0020412200c0004030f0412980030914801c104802c458070412401180140c25983c58074291001d005003907a90150209100050a004101003290622a4409000c40100c01224209500111b00000c0d001940010110754105405030120041000380c00b140307044401103210055211100a1900c24803101c4186189201c02d40420070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 263945170 1250 263943920 263943941
    0x3070f08031b0423010203130e010503010f05040b0112020d08072103090b01060f090e010b28050301050603181f05010605040b0403020f180a2a020a030c0c05030f031b01 74
    0x24680a2140c42c6100081104c03450580e0b41140410301100c0050341c0707491118005403035200e000105c1503040c68181421600e085540003140b03400c02c000e11000c40c4c00300101c80c2c10360b214030b10031400a114900100d10107007211500203041d0840043c1490601415410805a00768422503100c00981002000c4095030343d0140003130a5070203030000400600e406030b106040e22080c6401d0065026a03181c5684141c26000d03031040c14805000140e9850303040a072904080081522540038002c070300d0b4071000900c2070105001d40380c000c3c0ca0001c04540e0604481a1a1005605550407076a000000903020491355000c60780100c2c401d03040100201c3d4a50207501560180d404020fa46401c06180d07400b00310b03030310342c012000c00e80000d09510800c031840003c0183c1441148400f102003500e103400a40c00220392008041c9480d42d10300f4103031444cc0154041a16942541c062501c0134050080d8140031020000750b40c0300c1a410311554000040c1e071100840074181001d042464480c2111074160b80e5420f071582030341d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 263946420 1250 263945170 263945189
    0x40c03060c05091c03020f0a0318080106060503040803070306180c020d030c0c260f1c0c12021c0e0d08010e090c0d03020c0a09270308150303070f08031b04 68
    0x840c82000300c0424484e68256001e441100d05e640c244010f441d050010300d200030b030005240c2d17a000c03000c9503c00020340c0c0014011030b0020030185282410003010750102820007080100000040307506a446900007a003e0841d00c00c0b4050405c03030820041000b40302200c2c00f500980100003007046054042c2c490701300e07541c40b40d0701e8020003a0060354451612007140d41d0b40b400240110307414490700014280240000402d0089010b940312031029010030300300c0b80c083c0e00c3d4001c541070141d1340311000d0b1300081106040c5003109001da140c00300300c40420040400310700b03007500e107c0c40c0c8030f07405c1880c800014040c21094065294004181d884002c1d0080300082190010002d6111400c4a121820048000011301b8043d2050b02d080011007800510f00005aa0213090659140d10714502d428061040584880000120a07022040f0070b907805004075000520340036845030031002031000c42d2024000c40d5080b41e840880b400c0c0d1302d142ca02d00702881341c106484d503a0444098800003050f41e20342c0300032034090b40e00446 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 263947670 1250 263946420 263946439
    0x7021006150f0305040210230d3309020d09050f10060509010308120c070606030302030301030201080c031302060d090c2c0c2203020907020a0b0a0606090312090509040c03060c0509 79
    0x150103035500e07801010701c88c0528070010040c02c00e0080300405000c440e441c1d40c0000c00d054484000c003c107032910041d1030420368a0000b80884101170320f888624100d82e1100400342c0c40d05049100200180055003024040c2c0c01025140c1c4540030000c2065001210f58070000c00403952039805114480c0381c00d0200516000d0208503840e2051030032030704943d00592100e0309500d400c034250780e1081968243c3d8811000751b40044010f20840da040840a640800c040460321305515092031135040b068040080a4041d60000504490344001a000200f016400040715610360741e581c01c24070203024402d4042c413003c207404d20011030b501c04240301c1e40e40505c0702a0103050820381c0e0400d800b040400003012450519116139030000050b115144042c1c4140000d8019250302c4019003017441c840074000b44803088161811780240901600708540d1000d8a400030512280400403e20039070319601b40790066944080e101081008000d05861801c0a0702e10030310041c406240c0c1030350252201d000e410581544245d050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 263948920 1250 263947670 263947699
    0x60b01350c09090606090a030f03050918040b150102071a040305210a0e03031b03090108010609050105072904050307030e093106020c010e06060d1a07021006150f03050402 75
    0x1440034168806c0001c6c8210441c60f0b407552555410f003e9a041140490000b15002c440b07480c004032144124081c101c41c981061420366a20040307d01c008155150b580c0220f1003141c00c691080241c2d10207403042540c400e10004404080e020284c0062004640074030603410b1452850485019070310814070324282107030600c2015001a030700d4000603010700b134240c030090001400382c99402402c40240300032040030315030741c00c0002c000400c0200141c00000602464003020032459902408840b642500078a41c40c071101c4840340010126070000540e403c8400002c800e00060003400b1009142d190710a07100c40300080301003814800082c04c1240c90300000d60f480c1850004e04441e074840b850418540d1020ba6680b0540390f6100400c0703030007504410a96030b568050b000050341b030401c4982d4003c0c804882494083d10300d41d071010389020101c100003018503000804286524000c00605003004402d24090240585441d100d04044405d82416800184a84044080781d8020f2203128051074002d04441f00c101c500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 263950170 1250 263948920 263948929
    0x110307080403020a0807290f071413060207080d0305010605071203021317100e0a030507141911040207051e070914041109090a060b01350c090906 64
    0xe0054003540503800e005000100002d005100880c4142c0d40c903804c404803a9101e05d501e074103c00c41c200100e00e0007001e019044614026603039000c1514903103d41803131401c04035000c9a008400c00c42500bc0c0c3c1c0a4008110f858010a00d0f4042d2840740c1d08a8044c005c00210450980341c080c8102c40100300204014408521940c0e0b5600200315a400e0151401e039845440510b402c2450b03001241d01ca01003101009284010300405403020b92045060018040403581c40340c0701e94188100030180000090100c003041851040f82c41d030410300a05840041c1c0c00c10307a481e035049002d610202c0b9090341001c0d894610745820b02c2520700e400c1e0803000508220884c407101c3c9501d07e1100315016064469140b0020340a10503009006100d040034410701800d00307043c80d05003811044518081d22800e812000c1200b04400040c9c404100d9400c0080407400c4c40030000140c07418101d5410214403031001d440100908540c6445000c00038645c00d0711918990342c1c0c102c0c008400e0040d0010f8941c0082c140307010442d0307441d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 263951420 1250 263950170 263950187
    0x5060a1505090607150e010c170c0c07050a090b040612052a1e03010605062b020409020c0d021501080d050c01060f081011040e010306020d0908160510110307 69
    0x207083c06140c040d01361075040d0421455a0508500b980b41d09501c03085280130f00643e1080b0200c4e052108624008094000b51000001d0036401290350104140c100c080040102c603008110143c0b50200715a11042c0200c0540003160449001d01d050003000101810682c81e500440b64124018201d800791401c0c5000c0400302e03a6140010943c1030709451030305540c1d901c503200941e81c1480d400d1880c07070b4481400c5c5400d40d519a030001d4808d050601000b0386004110201080f0020030032a8401440c2040340580c1c024003e13504035802d00b03440400c000d14201030004488100d803040303030215070500307480c8400c0c8220032009004200048d000007082480c590300603c080c000a1248100104d8080d40f901c40940440185500c804039035070010180c150400040d2199900d000b03900b4a00030300c1d040c1000c201c88c0b80004e0600c0000c140a500194030103003100150712000920b03500401a5903200104200c01d41c0b01000518269018041c002d0710251008461040b80d0305c1902c5900c1d11410340d91010400d84200f80d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 263952670 1250 263951420 263951437
    0x303050306011119061a10200d031d011e090c030f0c06080a020306060927270a0f12020f06040305031012021305070512010308040905060a1505 63
    0xc40115a460708070302400391513807040500c2c080b002d030309141c2d00f410020740d4800b05a40101c0d5140f07940400481c4c40b1844440710015190604511040c00c40e80c0807540000c0c001034090340350081c1c3d21360780380c12545500700244000b01880605d4a0302440c01c4200c1c01c031001c2c80c030a001c8095040039040280302458101c01c2e0914010711210003081d540b0b481d07442c0e401900e82821a04208081c00030305c201c03500880090340040e4459030440c29850f060b004140c55208242c141031003a4805100d0440b0002c020082000e180740b41c8003080841d0511011544075500302c40301c47d540449088401440d010b000003120088144c00140103207660401c0d40341c80411080d04404a8210b0241d8103132411082d07800c1000c1c6c1c3c01103210b5034035244d80b8a0302c401c10550b403071010303005505e40b80c04544408002d0303078070303132a080d0482c08800500042d2510741c1d41c8207690030b216112103101c00604c40400001481060b6003d0001c4070111030301030040d41d035081e04000c060503481c081c0100c0c3d10182c10ba20300c40309105402500c0ca02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 263953920 1250 263952670 263952677
    0x50612040615082d06040f02090c1902010b040b010c0f02100309050a0c060e010e1e1f0305040611070c1a12040b10061d040f1b020a0308010b04050a030305030601 71
    0x142d102c2420f0380c2072040304032001042000c0500c00601c0e40802c40344043c0440c04410240c00316003401da41d10241c41d5070811000c0d2103502c9150109405005940403105541610040400c00001c20304d8080d002c2c01c80f0b0043c051050389041b03004001c55000f29000003c0b146c0c000c05e024003210080e801c21161075501300302401010f9849a40400140c02000010340990080107500b50b07042c0b410000901221741c0c0000382d070401618820702003082c2c9403440140071010250000c2c0741c904101d9004519107071100d54074040441e50201803080559015031056004500810080c4403920401880611503c80d01c140140300c402d800408200d04040003141c040d12032000c0340c200740b40441884817000c601500380c4060340d10a0500702404800d00394889210014161400c044850300f4100c2c0c40441c00b000b48400f0341c0e0203181c0381c0044030301c07856040d032007040340150002c0d12000d2406940d000a5541003800c0c0210085000c003000491042850070507541120340003840040c0c86030a41e64103d8040c1c101524a9060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 263955170 1250 263953920 263953961
    0xc020111071d012103080f060f06040906090f050c09060a090b040914060117130312090303060611030702092202040507020303070f0503011d0709080115050a0506120406 74
    0x18948560b201e0010a40050001071142d414086010000d8240c914070342034442c00780e410400002c0d04680f1050780181e907510507484a9544101090a0510302c0100b01d80c414000a40441c807200b90741c0c0150255880c00400304800404240808112401a1100341c05240280301c64502031504d40014030400b009403030b0801640f42d880101c060680c00a820000c4040e4441300100d054050f40211203034846404d10b448000c108015101c50713101c3d08080c01e0300800c10041c0c03180301c0505000d01426808040303544801c100103a03030303400d00a0040480f8041c15001580002c000d8803015800816580c805030001c0c0041c01c10340720003802c24000041954806c1c0707003207201906203001d81d0703c0d889030034828091600656964900100d00620062044540c042407242c06e000521625026544180c001013610921050300e46a90000b0340350b26440e58004100c940c08c1507006801e00c078486400c00110390b4140c584207070705d0780c81d01f0800c0101c0c01801001d1651003520000500455032a8100c241c8640801c94075509 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 263956420 1250 263955170 263955179
    0x905070b0a21021905031512011e020307090503240a09080d0605090c040b0409090f020d06061e0803030a05041e050105010f12020306160306171c0206070c02011107 72
    0x5015003002d10004140c0d0219403045805100300b0180d11081c1917181003455860107100d21400040601203c41c096000501c005010113403d40c091095403451000f142e021181000c4100040e40c411203502c1c0c0010300e140000100383c140010301c556525616131600380b0240145075101025a030040401c1c80d408e403030f0031844000c5101b01000b00310480b0414004901d4074102004d0000c0740f500903041500c0c440d42003008010841d102e0341074500346c5421b6840030480301c0c07141c10a62048001301402030341c490145001501080303419400341c02144c1165100400d50744003500b51104601c07840c40381c03440703070b401c200002241002141c1c402544148181b5104621340f4035484030f5941461a44402c131566035455005010341074203108a04010305621114510707030b10712a070209840310b40140c41c60b501c140c10200128002d038081d411100103003680202c820b404924400da203d590b800b030384a0065060748000340130320b11a40301181d01c601c1154592a1100c005141d54011a41000c2001c40c400c00c83c0203079a004034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 263957670 1250 263956420 263956457
    0x5030f0306150f030703140105130e010212010f030b06010203070221070b030a020d0f0e070b0706020903100207031d091308040b130303020706230c2d010b0102010905070b0a 76
    0x2c400e40c11030352904c078a071141e409400c9130081c01c070072100100b4a0004112036901c2074251024460046404520401050034040c068000c01030b0407000c5840c00c40c0081007000c40010b28904480c040d420408090300c41c8001641c69215028012790050f1704946141c01489000282c84884812802280d00d5030b642c50150002c582c1080d02e8100d0182c0d0009549012499a4051403070340c11400c420030002c841c0d00480095590300070340320300180031101042541c02d1140c03e6040d00c00d58040a401c1c2c1d9009030241003603c0013035022a1044021540144040300a190745072402820880c004e00b040c021900d80c03000c110140032440c0720440300c1090800000c102317140030501070604e82c51000768076000749003580380107404e0210740c4d0080d40400c88800640e51191611424441d02c8001c108a0141e03500404100d841c24050103030500e0a2004a008103900c0d0102044844c41c11200c8031402001441c0b8180012402d03a080780d400601a82e22555040c400d1287c110000e0041d5010b5003441003003501c0300c02c02007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 263958920 1250 263957670 263957677
    0xc1e0c060e0f0f07080307030f05040803070c0e07030b09070509060c0307060608120315060304030306032a0503031c0507110a0308070f0f021e07080307081306090305030f030615 78
    0x40860b41140d4100051410100901c00e407201c100320190041e40d091a4450f0398900030300074042d003001005140120406e01402c11180130b02000c406695541480c1e00342100420410322502c1c02c00c02c180000030340c04602c2440754080000c001010b00d0141c4e140c6d0705040342c42e500035407142944508100a40040500100300030100325105050220710b80b0710304400e82d41000711001c2d000201c69010420001e403aa45400f420132184411175800780c681d102c44c14105c000341000c1d000140f01c0b403410380d00a4018200c0085031f45a8541507980d0308a10383d120028180c407401104040c0c010795a901c1480c0d0b0100c41c140e00035503404106803804c64a28410b0031582840c1c52107103035007a400710301c016040c0581d5683c02042201340082c0703400c1040c205d04010f14020b40e1080900071404500304614260021444144003101c01004400c0031651949140c0c10211001c0d1301034010300000e009100d1000a0345401541c0a1045036000300145081080503400078480d81d20050119a0115020403180005a2403c014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 263960170 1250 263958920 263958941
    0xa090f050603070b0f0403062007150501050307080a110d02030613031b0b041407080f100e01090b040311100f050a0b0109050f01050c070510030b10030c1e0c06 70
    0x12615050203070500d824405103810240741d0000c20031454925101450440b811030350310070800201084d612402c038400c0c0d50350390800d403104400000c0c0b840c140f06080c0c030803100c1c51a80810400590b40d0b5a02015610700f420300c51415070b0341003c481e4034003064070051406031720080941b40705081d415039400242054030840326070382440200b41100e814141d20101d010b40841381c0c0c41d944c010985603a16200c1c40c16100500c0141420995000040d500c0d100b441000e00518220003100c80000228414039140d00f844409040046d1601500c0d450058050003042007203074200a00c45106d84550f1800c0740c901d03203901c0d08968a03100307100d0b43c0c402c01d10300c9100c5c1d0741200140e05000569420000f00ca00300782e50b0021082410806104001e100658802551740074080090910700d660396a415006800c1c482d041d400329034405d0201002050160f0917820145481c80229100d611034142008164106c1e204601c421001442220340120070444040c0b0580c032460b1541090b0302d40404543e10700040d00c040046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 263961420 1250 263960170 263960201
    0x1606060f060f1115071b051e070b030a090203120c010f0e030a09060e0f182a0403020f01051215030c0a051804030c1a16140a0309020a09 60
    0x341003000360790141c0340c1801c07000c291a091014400200350965652541403ea9030881103407030220f00d82d54003e118445100300c00d5036031500c01c0340090828544800001c1c107521045040c50108940121010032000300313848030015442c0c00c41c3c81d0304107404010607200c10102d8040c032960281080c043e10390f10251051416241c0041010140c1610040641d4022444c0c80b48652041c0229050560803032202da055a20740c1c5482990b002000c0000f8102c80701400c0c806400140300708101038018440c001ca107100c1c80f4410280c07401a94a648030f6026103208100c50306520f5400d00c01800103140280710310b041c0020503d441030601c0903102000c00d02440c01e80e681e40c072910801d01c1c03106c00d6080901401c028000c0840704022311514000c041601d08088180680d1558500c6c4001400c050141034152140340d009410b64444c07450540b000811203900361080560800b28900c03000f240c900c16080c080d01c180d541c500e03160078000042016000307005040401c0381e0011580201107039810f0a4410756011079103545 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 263962670 1250 263961420 263961449
    0x1506030724021209060702100302130602061f051008040204110d09050c01031104050d020406172404020f010c051e0a031103030421050d0f0209040c11070b160606 71
    0x21400303403038003c1840e0310f40d9080c041804800410380d13644054440c41601030f9011212002680f0781240240315140c1c200304c040503404008100c0c80d500080303e07441030500510180070000304801c04c0061980c2d900c6065408000d080600c10402d1203440b0709a0003610207000030601280400e840281500700c403200400155595034031506101d0304200e50f0481003020308042041a1030361714201102e1095000d011700400d403c100301e60454446a0000c4010311381001000c81150407452640d8480080144405280e00120303200005900e01654560080394004c0c021410300036481c00644540f004410250748034082ca96002c09080c46298003028802840d80141203d01c4c41c0b454064100900c180c18004980d100b4410040000e00043c51722a4408104152120500740c1d40c008960a03c29200c19422090070160f00c1d024058454000d040c40315001c40b0140052028800221f03084a80891544841d42c0100d90030855007103100c00400c2d82400c5a02c400443c50116200c1d4010340d03150b644861002a11031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 263963920 1250 263962670 263962739
    0xa0c0615030f0302150f01090c0c020303070602070b0c030105060d051e07050901030c050301050a171213050f030118060b01020c0a030804091413030807260a0b060c15060307 76
    0x1030048018005001170019402c0c108680b4010202c04140200034244c0ea41d80080c0d012a401101c2108140b9402011a55103142515225000c1e4110600803107540d4071400200d8251203105050700c0c1a0350b0050500c0341008203281c07140020340800f60030094600000c4280c1501d9043d0060290b1040a494840d156544000c1d4001000c8800041c4000104101440188240da417807000c0942250b031796405a06084201d42c0e011780c100404100560011207001804050030143c00030b00c4d5007256411603a1009045400b400e050980f284001c2121050074a00928000220310b54403006100384180304803100c01c01001c0100c0c110400035002660164030100d03080040c00c45034050304060100304040e030442c1d4144140a0340501d212814020705002038080010f1710240304840c05942c1d142e280400d40181103440e80c2310458540c040c5c40c1341020a041c54a0000705003090021143e960f0a060014040040d42c89030140c920000940b0440d8036000c1c420300000d0803060032403040304c1040013028602922884 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 263965170 1250 263963920 263963923
    0x40f080706020c0f1204030c0513060e161b05060406050a0b0a080307021c0302061308090a0b070b0601030b0a0915030b0c0a02070e19020309070302420a0c0615030f0302 74
    0x41c000e03503200000782001b0034000684001100012113000b0b55030100d1009514003140040c0c00150003030740c96401038100704a5400c81c403d9800340008001d8480300d2003079501030940d81e0840c010b0000940250302030008500000c1d042d13404036a01484015002807200504800294105200e500c220502d03400030030914258038044100c061201c0488000303590203070300e136500651940001040c1d035800903002c03498003091007107110032142c83d080014072045000c0c0d00c2e40d400181641001c42c00ba40d41612031000241103501921502c0003694008005641803450603a180b07010382450f00300403035004010400007000428a8501c18014055000269156900107000134540704044d40704002c221003032401d02807a00c0480b5941f0440100680016036030741c2c2c910201900c0c00d0541d83c00203402500b00034030181320310310510b846a5003403120000000c01040c1000f10300301540e180c241d8812204420030002c0313011405450040e0b407081c41010301203510410000107000e406c4156100351500200c005030241010f60 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 263966420 1250 263965170 263965183
    0x1060914060906010207030314070c060c05010f0608061501021c050301180507050a0305060315100f052d030a080705010b1005030405060106081504020f09010e0612040f080706020c0f 80
    0x802d8802c100b4915140d00001d5440c01c040c44080c0a2000c00f241c1c000c1114070f51030403101c40c142c00000a40c59281c0e6603200409039000010b09032082d51805c0c82c01c1c103540c4010b0150303804440c1c5140c010145500c4003005209100b4a00c20668107501c2941c0c00800186c03607100459820f0b01160b142c603034076589080c07001150a4990964100c3c01403802d82000180e6420100346ca407d47d00c141340000f45a62420b000c28900004908058050b031501d6003001182c02d4558009415aa00014946806642c820a00081c59a02640c0100050709402400c10b4591140307521351607504028210303801e80c0400d854890503a40001d000f92481c1c0d440e1a81d005042c01c1c01405060000306925119295141ca40c07100740c1c8845042c02208108920040400d07c0010840c40710020320200800c119030f03410000c04800304a500c003241150101c0c1c4150324005c0189001c500b5140d000d000001c0c2416142c0d901c1d610740c4500c0781d0207101219880d105010400c040b03941131000d498000c50700d0004088100e403100c0c8147c036151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 263967670 1250 263966420 263966431
    0x171315020c010e10060807080304030b0a0605120f0d030e070509071814030106050108041e0203011d0303090c030304061d01030f060806060307050402040b0406030e0c060c0a1209031205071401060914 87
    0x2804004108148d0b9400030880b000c40b0341002191026880c0d24032204003502c07050740125800703e507405540d00c5905000c9000100c0f2031034141290744901c0844402d4098604e0322901c01c000d80c000780c0d820072850070101c1800e5448201854100305059070160708081c040c030607422950280c0c001c11594207840c1800d10880c03016200901307000310245450782c1d400c01e08098111104070b41e1044030082c8021034809402040d036890400c50350b101e40000e01c8500c00c1e6039400403500c4030315512071200340c0c640c10704000c403c0700c0548405980b00c04040400684001d0ba07030340f041003038034105692905c07980400540d5115140203007440c60b0243c10682803400c2014504911a040031f4447ca00c1000100b090800c004d0454003114050b041c0840c50a03d80d0800034241440ba200007134000e0b4000980b400d0185e0082005540756204220f002c031a0700d00e0744d001304c40d44000360000820781c0103428290f265890049000d00030b0f1ba40304600d070310781e03000841c0556404d6030440d9008900513030301c54251303507208540c15904a80c0312 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 263968920 1250 263967670 263967673
    0xd0e0307080a15050a0b0f0f0d4d24040f0e061005090f03010f181e0206030103140309040626030f070204052a0a171315020c010e100608 60
    0xa00001b0b000039813464070509118422003c00e1449040ea8681d000480090303034101803066a40740d04c1140e55a000c0c00c032004419002c200c00d020403411601a0402d44100c1000d652070000703450032500070700c050016801d1821003110312648582c10208205c000600182c0350700d01c052060945001101d030703e14078002d49540d11035102c07805a4904031354000d0603030396290400c40e5800d103036000840110b801004651f150030381507418648461000200f0211020310f080c03141c00e4808003980803072007602020846030030003984a0020001000455540003080030103007000070030b0300e00e02084080040c04581244d48410410710b0404584031103078603040703042c80340c1c49000380185240241c40540810075200744040288a2355035080491840000003940c00014000807007483e0301520498407050a0750000084500029500354502450b404031682d030700d0103142d000c0518203600c03100d0b660b500703c0840700f50340801e0019800d000383c0c101c892003401446c04541544001c2e20100030100411010780d040340e00f00c00f029 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 263970170 1250 263968920 263968931
    0xc030b03010c0c020907200102040527150402120702060601090503240c04030f08033705040305130905100e0c0a0c02130507050306010810080d0e0307080a15050a 71
    0x1554001624a03e080ea0445064030b560395140707415030304104020702c204250800805a0103800c0c40c150b0007441611000c0b10405080a061109001c034003140207407510145070b1807404200d1141300024801030f0b5010003032026040c00d28070b00c0e4241407840102da211005910100c10b0040a507044041000544015006040204c19000d0920110389190f00e81c0c032015406000001d80001d042c2080d10055030303100010302d404a0507401e14400c2c1c0d400c2940c407600c4203e00800003200303040031555038074103481e030721020280b01d007020300320400003460010025401d224041050304007400c40a40014081e001d05100001c160130280302100d840302e9146c00190000801034140001c07800701006607483c0f048603240c202c000d0601403022810310800c000c1c1070140390b07003003070180021550808095489500700b0382e900e140d039640f000050f45003104a407082050f207030050303c00a140e580c03042d03198810310480034080b038018a549030b40790351408260400584108507038031208402c8a00780c0c003070250040310565040c4003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 263971420 1250 263970170 263970191
    0x309110405130209040f050303010602030d0b1c08070221011a040e0622060207031e02120a0302090105040b0403030e090f0603060f0403020a0c06020607142104020a09020a02010c030b0301 82
    0x10b06180c5800003911803004e1500040822121552400c4d90340e9000040e25240d59485102035500d82003109a01c824505241e20013105090005c44020300c01c80380c201c114021304584c0c42e458501d902c00c070b0301030781c00088100d40c042c50149100500141c020f041d100015814110740c0c8003c00e4900400255446541072828000c25450001801c51700f100006084441d0202c040010a18480140380020240e81c000300f0100140340e081440107412008030209401c80d40d01c101e41c01c985905540d5061003008000b445100b100b2446603015100d07a04040c10054a4a40c42d0312851140790031581c4201d00140c030590b071003602403c142401603000820200c0c0c201c0c16040444c002901c1e003100801d03455041029200003001c0c14401c0000c48035581c1c01020f420603650f01d07924000d44984003140c807680404c4600f90b00016840c6013408454001c81000030f00314500b50704900d00c03182114041e00a9034407900c1c011380800d800119100601428540e03400009000c040ea000142c290b48881840318866450a0340a10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 263972670 1250 263971420 263971441
    0x7150512010b090a080a061a01020c01080a0b040b0406141915030f0b100906022103130f05030c070911030603060612101e0f0507020a260a0309110405 66
    0x281903410400c1c500340c40307003c5000400d020070300503402481103210390b0b5101000d000081d0320500754182d110b151140c0d45040360b001644d550024103d06400039150900060310508d00c0d0380069240c650080c000b00341c07005000009025102c680d04000d0701c01c1c000b4616081e180c07520202d84e012500d82492481c041a2a04007441600101c1140c50814151112898031007040c903540404049a80100b5200c00408403400080100040d8024400503200391b402c88172151200c00390003c00e00201c4404e180c5180e03110004d4001005e11000d086805048000f003000001e201800a0400d02254400030303c1e46074904440303802501c02410b004800c98100700706001e09034801050041d480402940d880b0081007044503198035103050304160301030943c82c201a002c0c0001890781e68007100c0821101c1440325514400301d139011194142c0701c44002d1b81c00a01e11400181d80c0c83d220386422001d603220802da0566640101209512604003100001d98941c180742c00c110038290890703488281a00e0422040c80c1141030003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 263973920 1250 263972670 263972707
    0x50c07080a02010f09050a061103130f020a0906080f010c030b0a06030203041703011706090c31060b3109020705010f020c030c071d01050103020f1b071505 68
    0x140c05100d000540e8041207000b500500d0364800e001d40200810492800d0072600d40c3c02190084800c642401490480c0300c0301d0030300760b900600f004c100d60380c0800c0003640e80c3c0902e081100e6049810444140300060b140382180703d030300020190600508480a5900fa580342142d15076144c0030180362410944c03407081e456130b2102000b41c0f241d82c1070041e580c0e01d0380c0c00e142e81048400411080070201c0040085111140b90442d003040c4081b1804480c8117456404566484042d0034030850780242d01800001c0c0359202403003501c40c68800c03200e5007200c2412107c1d0403005540ea00d4000c00500c01c0300041c8459601060346a2401206000c220b402411120300d422009a0203e440340c1c00149030089a0382c82400002e520440400300550302c00c55071845560400d645a0b00003040c02400d80c0105000003580e489001c00e481c10f8110251b003c00d01766801c1c000150003d42003013905c800c4000c1d0600c10208000c0400c42c840348048501320081c0415441d200c440b0240c00326045142c0f0400c00103000004860300c0f43d02d01c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 263975170 1250 263973920 263973923
    0x108060708070e0424090f06080604030e1810030b0105031c1404052709060403140f2a061609140303120109062309040303050a0b03030f040810050c07 66
    0xd011150b500c900014090404d039003a01071030754640d45c021903600349142c400b1411180350030010b0101203030111141c0e00301e83ca184079040444e0440000213001902ca0000e600e80840300419480d181c0c02c200c10000116441110941c044c1480c1e11014020b1004d01210707140140405ca00400c41d00d800b840303110650f401c480b031011082c04040b041205085107000e054801410014110002404100102c0021460b4513401c9004000700704002c6107100d0004078200b880b40360113403a4480000c2c10782044807225842201482e100d200d040c85951243d02d420310780103220b034501c01e4401c840c1132000c500c02410001e014003070040720348450f0008160190018502c2040b1034a41000c442198203800c04207055104852130712040041c2c40d4004650880b55510100544034401d410800003c402e501a001d8007031a0514030703078001401030000e030009200b40c1020f580074a08000c049154140711001c2032658000010414000d040890188840c001c100700d5255400404a0180000c0c104408001c1d40c0c0d109a480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 263976420 1250 263975170 263975177
    0x5010b0f011b1e03020309040e030702060a0813080403061e0605151612180e040b0604050430120605010f050a11060c0409050603060c03061009030605070206040308010806070807 78
    0x1c540e0140048290042c1102c41c1a0240c84501c0c410f6160003501c0c0d6001e1040c80d0306c43e0303203404c5182c600008000103540e00b40d5800b500003450244105425141080000c0c401584542074940c0f030400a00034a0103031000b54031668001c50035140050000084d4003019286d000f8440c42e14004028030360b40d000540900754a00001c080c4c0d140039a500480c0403000910000c0c102001c260201c40da0603070b0046201d5091030745141c0314215103488100c51707000c0c40c070159000790400d24414089207aa280a43c01590803603c51030050042041d048140703103040900c120044110014031a1100d440c0d500503500200000c5180c10401c030f001e00700000a8004030307090210a08000c4040b0302140403500510540c1003071945541114440c0c41c0202c0e0850b425031090290784074075030425001c23600509000402c0c41c0101d00d451100c50650b038032402030041d0720103800407840030080d05540c00008a0307110303c00d0b02e01801c1a40d002e00110b06c2d290801502d9100c040c1c1c4912169070049003004002d0758000380490300031f043c901c1e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 263977670 1250 263976420 263976467
    0x5010c1706131d061e04211101090623010320030a05011406271f1a03181209010f14030720070b070602130e09030705010b0f01 56
    0x8640300074141000410f02c650210744030001d500300005a618414410540f040300c200d220074401d03940b401002da4004004042d0203041e014040f6a094207900c01040525200c4190802c451609084d641032a07425510f440e40d80a160340c0130141d1244a14010381000034020507945140d4540c3c8040c5e121084a20300c249161000e28076941e0240000320800e600403000703000b104c00500c8045220107081c0e841c0c911441c400458084103c1030600c0c0c5094112600340340030015034860b041580103610328003000381a140312070b8001c076609030160a181214485006450384910300040d50590303001c580015210a5400583c01590880050046031300b404d0080c604440800b070404c009495600c01c44181c0d9910420200405c46c0c0d40e90f001a8031280c2030f50b0007880d2982003500d81c03201901c1e56014010881004000c002d0032010038020380043c1a034400c4030400b0a043c42d500c18011070400e40503290312540f40c200040310800e11401b4000c00044000c1180c49403001f03a240400a03005e072a1306001c803104954583e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 263978920 1250 263977670 263977699
    0x90503030c0601030f080c030a020f060a0b01020c0f0307150305061c020603190b04110a02010614010212030c0405090103050d0306080c130c020c060a0c02150309070303080c0c01090b010305010c1706 87
    0x41c02d440c00111f51401302c0791200c0d16550043e4031122412140328003803003103200294000c0c5d182c2c00303423503406035040e006007441503031a5003840303c4a5507050040d90144250f60740024041c610304c2d00408092036a990001e0b580c1040e5040100100000da0f0620809400d0940f503009039031000112034000951911807000001051200f0b0081c0140e40d041c030350310a20340308081941031200d90040c0002c000981c000c0206035284c0240d01d0030104140000750040e0b0111500380c54440c0060000c507003140c010015070341095038900001d511040d09030000c84a90300103c013850304154050140a01030401e1300054231764800e032040031a070015682d084c00c88180b0388840700c10030007a00038003801c40c00e020040d000070740e18591464040c0190124000403070003282581120300f410307082e900503240101d40401c007404042d440c5443c110b075011000751200c1d024075010080390340b03021001d03c60040064030505180e00c06600d035051060840d01101c0c00c080921600c00d0110f00d00240303410303d0a1b031040701128004c00c252a00d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 263980170 1250 263978920 263978933
    0x70312020708070b0a06080706180e18070605040503032505012405010e150a1103041e050102031e0a0203070209090f07210b070c0602130501090503030c0601030f 71
    0x1510028428548005404010701512400034031402d40200001c15140d04c50fa290141110a98840c4280c0e641001c8800c1c403250384103240410768040710940d801201a1140743c01d0040031010ba4801c0c00070b841d42005c40c1c0c202803060102600512807424054241403810020075264402e00a1085801d0340d143d8111001c2c804101038a410303da0444c0081041203041160450811541000da000f05103048200144540c4240c84020b0085806031203480301c41c00c921001106a08000c11748030074044080001c9d4a00d000410142008040c0711082400041003140c480320845142c0d00b0003411500204400d01d109a4585050040d0300240c1e4019a510729009000b01d081d4003500d40c0081d4815100790078007210090001c0d400d142646040d05481d0120fa440e0351103155480440d0010011180c482c4034440411416518180d00c5499820840c490f2030080d038403007049900c4103480d1840b00d40c00c1c036802e006950f4802642402b9100540003186090003440c4078950781d400502c0018401007040c8024401c0261 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 263981420 1250 263980170 263980187
    0xa0c120218100603060b0405011b0203190302060703050a0507050702130204080106080a060c03140114130f1407021f05130816030305130b0f060301090b011203020c0a1a0703 76
    0x80700c00603110604018121441015640c4282030000f400c1a8004c100388048008540444005071200a42d6220540a00031012109041640d044c0a02448003c003100380f060010403a5210b5805042c040c50303c0c080103012101e000c1c00b502004c030318100c20002100d401004490903180c04890f0b01140c9590802c003003010f48110740202c0d04c01d50a007007002032190b600107130000700c0f20b1240d0804e01400c85007503000c800301c52003820f0070b07080d9103040e400400642e817580022281100d4054041e00607460185491801e540103100e8200d0388a58814149496030014030041d50022118070140610403d40503580300c000e401b0b1200644800d80c0c45002c602000001442c010b01f6546c450080c40e2100c0300d45508450b580c02e044000d07408603003030000180c501c2050300103050000c0d0b403007201d14045490701e0314010140203000304002e030990360700c1d0100c001060200d031045000704000c1080707001e01707001e41c0b800900301405000401c1c001d600c83e0200703000c840b10b040710040041c401c5885858407451075040441c1c0420 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 263982670 1250 263981420 263981449
    0x1090e03030105010e0909160f050909060708161106010b030108010b03060402060a0f020f0a0c0f080c030a060b0409020d060f0f0b130e070b070c15050702030705040203150303190f020a0c1202 84
    0x1032007a100007400b4001c018199080f104100c990bc41e141d61044001508d900c0c2c00c854400018000b00c1c00528108602d01204160407910300e01413520f4480854694a456002c1e001104020404001084a12424040d003010715000b90040d044908082c1d0121306640107842d005001d01880c0b800003020240f08018520f486e0450314110340030f5442c0ba080030f80300c280c22405090b1002004940105441000017000d201b41c240c054014032144445403075100041800101007507210b1740303030324403075000d65910b004c240c0c1014082c0d80b0020f80302c002c60704d8100450b010700c850b000c481403c0025902c0a5560750b43c0800605c2d95204012070415001300110b800d000d82504941884c820100f115424007951541a030140c88a020444151031604041503c1c0b034011890025415805900c3c1800705040c01e8014523040401c0520000c4551b8203500042e00313503000754a200c1d000b1064090201c1c48103500030fa8616a90500d400039018920305c545405040c0140ca009030701a0f940d10804170300440d01c50401810615 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 263983920 1250 263982670 263982703
    0xf05030a023105240d1a070e060a031a18011509150908010515031c18080a060c030605090c16020402030a091115041703070506010b0301090e03030105010e0909 70
    0x1842d1503130402c02c0620303010710302c0d000c2103c2e41e038800615070800118925640e6004200c1d007420021010807190b0044008082d4000c0040900842416440d164041e01200c1c409450125050824401540d00d1821640a01e40701e041c00fa203002061541042e10035064a12898030072001e0301c10900e05946808180e0301c100c2210740c01002e16050583d2000d1914151441e070303c0280100d860740701083d400000a150041d074181c01c03441403544c111140e40f80540602489051890080c4243d0130f41d8100d82c40294080f00c1e50760070408045081183c0c52168184c868110700f01080664200004512500d000900b111700d10701002900d0b050320f80010411600060340103209541d40e1030300b00b101d01c020b8644504101e640c8818551400d88038507001448014043c44480f4a504061070f01d0003c1d212150341740d021010324001000508042001804600e0113072901801d20350352075160500c0d040440380301403000c80c00c2d80c10174401400f40e80ea000d0f1800200820031218040d8540350145200c2c18883e450440c0b4401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 263985170 1250 263983920 263983931
    0x5070f050c1903060b060a051611060a030c03061e0b0d0209041802090f15040b010504080304080c1f020607140d0606020d1b0c0509090a06050a060f05030a0231 70
    0x800b0b0a10004005480c401c04050240c00301c0c2c0d0041c41105c1c002c01d8040004503506110f121441400405504901c0c1d0140e60400d1903038986030042441c0f544540f0202000903215200d6061081e0076000b51300081c01e4001078010b00d946458003000b10340f505802425031248001528000301d11251301a40c5031218000c20030011501c41440718007148018400890085041000107003500501c503201603c1004140d0b81c0000900e0b25200b000f00030440c104055061207c2404003168201c020400741002c3e04110300140000c0390b0540822010403503030080804104115002c801d0310640c00b04845810014a090a1801440c00002140c40c0e004a43c0e03240300d21490004002504c90f400140c1d0602e00605450303003c103040503500155840f29045074060700146403010100700c0d90410084003640100c40c202502ca01583c03d80d16401036540c291400207540e515100c01b40000da0030000004018902100140f006402c1d96001c02c01410f0b201120544001c00c11085222000144580c00d00d2513100303100c208207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 263986420 1250 263985170 263985199
    0x31103160f0603093f1d090703020705011406040e070b0708090f03031227030711040e0a03080702070b04080613060f022101140109030803060307030b010608042105070f050c 76
    0x4103100b150483c1400d0a501400c80c0040c0a69484d803a403070300040b9010246c540c0303c0c00780880c1e039002602070320030589c0c204209804101c0078811010400360303940a182184c2004800c010542d0b124000b2370a4603005601c08015402480303088844d050350190449446156034000039488040c5480d49503014000084c0c4130a062814903080ba20460101d10302c0c440d2000c10040031a11800100310318a100e17402042404042040d1402c150303401c0100500118080340a0401e503404c060b40d01c10b04401092040c000d20480680602522000d032401624203820a07203022151030f5207541c0a8074a14500f4000f200c6a82404650303000047c60310360103c420b5541d40d0030714004103c8007203450503604d160260000007055041c4041030540490794140c0d1883c2d595421900c600b5410b84c00541010381c0b40c458100c002000801c8014041e0081c201a140e040d140d1819040034151030b00c200001031041c1e44c2400180d40c07200d0700201030b1410b144e000840540c4034038981c989a440d10241e02d100070343c00740c02501c1a54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 263987670 1250 263986420 263986493
    0x8150a0b0a09020d05070f050f0f0412050604200f010f18080312010f03050d14040302090c0c24070509180a0b120102030403051e070b01031103160f060309 68
    0x507904130740b030100b04141d983d1918111000e2108a0041c40003601c1008600265a2080003401007252a0242d49151070742e941003402c002040740b08200d940d03821010800c410712404295500b401404d07614190380c0d451090000610080c0074000b078030b0600584000c030311b260300c0c40b81032052484a44500c10a10035600c0e0300016589421109800603800d4600001080d02c4012200e2081260351180040c08034440000e420b884143d003800341c105802c642400000301503a216400b06002c2c11001e04111b80c1c82080c0b400b02c1e030070540300000baa08440c074422035907522003c3c20b502ca80da114245e46847c58507101e100d00010013080f030260f06c2d1490500d0030300500c43c9280b003d9009149540044a42132440b80b9150310242c03e0340022180900411b5061001e102541000c0ca1601a26100c41c0ca11514110440d90361000c0550b003078006441d10200016500c580e81030402c4454801c0e2103448400c1840c80c034140c0c00346401d40c03090244104060300d03020311100300a00b03414461004042c002002c441141c1d13450101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 263988920 1250 263987670 263987677
    0x10902071121070b09060f030c0705010903030915021606020c0c060408010b0f24030a0902040f0c0806030114011205010e0a0819050c0a030e13111b010608150a0b0a0902 74
    0x1403041d0302a08100040160b80182201e040718005044d013410032647c103015400c41d030001000c41120f42020480400021400e00c61203c40e54800d4800140c410000e003024a541c1802c0c0c800e2511091041007000c0031003000a911110b001e603c83e90146c2c0ea2503880d1000780c24600100d03002c981003603022802040a07041034110500808003030b0380d4614200910010005144005d080840c00f10610b5203503139180c40c807030000035640120000004144074105501150449550032641780115583d11044c3d01c2e03182c0d000c0480c6411401c00c500a0000d103408800c0c070b102e000f00c11700c50b080c3d54400000c111010480f0070341040240c0800d400903100801c20078141340303e441e4405586101c0401c881c101d0265a5030180c401e40c0d42d52228800107004100c11903405a5070032540c130b81c0846e0711141c003400300000c01c196405060352803060405000c0d2a2200c140c0f440e0207521502d0500001a41800000c0c0905000003034081c1500c0c1c4002c566185940325a119440240400d01250341c10940d03c0e07001086402d400d8009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 263990170 1250 263988920 263988979
    0x3162a03060b151209070e070f090f080c060d060e0115030b0306040c031202160b0c16030b130f081b0607032c0304050d030c0c08070e0109020711 64
    0x52040000700d03000c01843c440810440c0790003101c1400f040521141c00c00c04194404100000ca40d01d00c3c1d21a00040c50480c0101e0700d6000207010360380841000c0b03510141240c0101000d0b06e5240c51641007903016a102d00c03c400e20075004031004500b051242030141c03c03000c0241507554503883c803541c407820074000f94282c101d6450042410084440141d0030000f40300b07449145c126541034035190a40d52213401c03103082d40c1c1c00308046104100e268190420301c2e00c8148000e00c440e4025a0381c8003a0300103d9814455115410a40b5a19480b020004102a000116440705184480c40380f1112103152a1161301204040900710700004200c80866401c0d030005003008207410021031b01a03980d001310881c1a12200e0328801c40254091034801c3c0c3ca480c90720b4190040012401c19241410340340d20104802402c090019000a01c21405907001d01a006110314007a1a90302e014003040ca0401c404c4054000c410322070f540c1e40b20341c0002c5400074810340d8559200e01c1d4800601007420340320b00050101c15517107107106 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 263991420 1250 263990170 263990183
    0xc0303080f070504120611091f09051509040b1906050702010e1f08190911100f020714010e060a030b04050907030201080c0703020f030f0a020d0503040503162a03 71
    0x4101c503540a0b4040d142103a01d0031404103031205c0a951040040c0107020b5041c10764500030b21030b141d00c03580c0d011a80d04000d050381140c0c0084032803001009002c100c0d107912490043c02c1c0e081046010105403800c490380c20400b40c2d8080b0f00c10f60201c000c04d60044401004d805000e84003a0040b8000740c1c094010000c0b54000d90341d0341d0090040200f0004140445131070042ea480300c84010040711170050342c115038030900826180307c0701200920f805042c0e83c1d4510741250600c4c0f420403032040a01c2c2500d400701052005103000d42018840210196070780300c190054050807005424102a01d078454085c9160b07142015110b99182c3c10380c114040c0203041d01510092295043c0000640c20800001e40041101d405030341e0301065465950002c65168000e9105030214081d0b1441c241044400300020000940314000c01503548944010007420302e404082071604020b0100305200c0480c1c000410b844081200e641c2d44148c1c0405464042c07011070314410219100c1541c03910461880780d89801d0070381224000c08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 263992670 1250 263991420 263991451
    0x9190f0609080307030806040b1305010302120c010906110a21020706210203061c1a010608160305190e0a05060c030601090e071407060c110d200a0c030308 68
    0x541a10110400d001e501c8443c1c0c0244850800b0900c68082c85401c960043c200040400e044000b01d407242c074900340a0303036555460340010021800d02c01c400307400e0701c40300b0f10103441c811483c480001c01c00030035407043c0d504101040d40000003113103040c400a004107510080403010780015090403100c07044494801d40250141c10000280640141d650103820355042c0d0039000d0a4035294500340082d04094607140d00b01088a950143d908000c03506e030740d61a0b016041c3c1d110811044a04550b80600503000407003042014814000140f42c1003490300150f0301c0b942804115a6a4043d0800b503d1412034401b0b4209400d050042d01150400302c4c030800c03c64001d400750384856690170741e200c0003072000f82d41107400103c4241040020240b0656090780000403490b020300008461116200b0a4005140541da4180e40702900004141c00c21104408580d175070000c2c109414030004060540e60303001a00130000c09045140c401c0c100424000c0d001c080d60303c44172254502d6142c1c240200b91807401c8902e40d2406d03d190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 263993920 1250 263992670 263992679
    0x705010e0a11130528020d0507081008030f160609120e030d1b110a09020f04090515010c030e0a08060906011d010312030f02040e040b04020406050d0206090904020609190f 75
    0x10300500d44031700800e110038050024070352541080ba071a44081031082039420b12000302108031074091580134030140d940d9141c060420b400c0c61034210f140c660020003954000c2100740c003088813aa003a10301200070b074000300000381041d08054000c1d000b100130081024000205108550780c0040d15181c60b10070540c04c9400c000e01596043c1d410071210581c42076801000c003504400551940600f10032054040d1404851980d00e110740f000766080303034040404c5074034045030910010031248541030340700548144021103100440000b8040000b50310b0041c0420001c034209103c651111506100245020401c49070b0a10308021003d45540742070107800340c08020071444055009180117138a041c1c0b60001c070054804d444921040e4001c140010003d66202c3c1c0901c8001405280201c059200c0d50051040e40503919080c810802240c03110703003000e0710907514442c0c41c2c4d0158030ad0200355031030000152003030303401c9440d9400062050f000e4080c14036401490040000ca80381ea03245600c0044071405040320341e1160300c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 263995170 1250 263993920 263993959
    0x52d18010c0816091806050316031e050106120506060a27050a1407170703052a0c160806060904080f180604090b1311040303050705010e0a11 62
    0x30030010700006403444045002d140d401c82614449000e10708002a2840e40d40140c20002e458910300f0640960b0f45020410650a003406044c2e84040c4001402071140e0445e942e403429000001d86500501441e00842000c0001c2580b0034806041c3c4030403503a50700112841e0490799200d04440f2280142c14610001496012050704840d07d1100a603180300102840b9062200801008158030701d9252103000740e890241c00d100e800c034012034244d540c0004207681c004134041200c0000c1c2007242050302d0402041905607a20103007020aa072244407600210502507503070040c4e80640d403c1007105000e0321134083c51490701a40350500b200c82c0f04003030701c2450303481100700800620210760141c21013034104020541c0c2828400103048154030400408040211000841d50315003054008401c419941d4120208038946803200c058044020041400080c41900c60590b45d8019480000c06200020900e0000c020085d0410b41710444885d00701e503241510703410310032040c404260305075000305400e0f800c4440070b0301c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 263996420 1250 263995170 263995181
    0x406120207170f070f08091905060a0c050c09010906031a090a0b06041815060504180b1b070c090e06060102060601080c0c060115031518052d1801 64
    0x10000c0a10340c0e1042407514290360740d80180c4107046003e108019a40c0002c80f0900c82c400c545010b079180d5515059501c1c10310103207071084c3c04641074400d02501f080100342d940e04100c542036003039031600e0134105039a49410380c500701d0003299540c0c5c450400e8001040038580c0364040030441c0d000f04980840c0041d40c11072089400010b07280000c4c56003200311480d0100700200300007074004001038400079086549461340070310781464901c100d55181002d02141c40e004040c0c0120805002c4c02c0360300b0003c58010300302400c0c2255010a0040242c0304090000305203405820074002ea62461891403550b900007484c02c40342c03a20103402044081450480c01b408004400030b030451041a040e0001c00d00c42c2c030f942e1b005580101005120544000301003007a0082c500c0207201e40d9008250345032001722103604400014069403501000714202400012080004840ea13009080c0490740401001942da00c1c1d0054090031304c50a1310005421508140c1c00d64280ba8041c3d0301d0510803042c0da0580220748008050003820b851 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 263997670 1250 263996420 263996423
    0xf070f09060804021c0f060e010605040c020c1509030304090c031505060d0e0c031608010b060306100311161a07032009120115030c0803070803070c050f060c0406120207 74
    0x248142d0002e00107041030015004000440340200742070844e15614041200c5e0000c5080316240e4a543c4041e0030300509008603c00f62108031014000f4407940c0200a644445101c6400e1080c0c075005134616a10000008480890300b0107401d40e6a01c985644c801e0015103070300e004080010f45000c0d1119603140d41d610710b0400b510402070802e49000a641c2082002e021065400310007402030f04014000c983d4200800c240c16200352903240ba03103d21302407102c0e00310383c074420000c1d008000170020086a5a1114104044120030342800140c06180140030a42ca004a043c00280c4240f05d421100a01c68030001249103400c0300c4280e41d6181c0d44008048094582903414008015030307241401c3c0c00c800d0034801a080c0d50801030104140b118643d0740c1c00782910210b13061400503201801043c02400311130b244000192044000a510b00b00c016640d041e081c0c40001c00724010040810034560070001c040c0400c1195070070001c201e030918100038211015030341c0103200e84404a10f140d04900d040f54000d000713485886 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 263998920 1250 263997670 263997677
    0x304051c050306060c0f01060f170304060e1c0507032406060e060f090406030b01150e0109090e0f0d051b01150501032c150a05090606061c050f070f0906 67
    0x5403500f0f024481280c0080c0c9a5070354a0040752101500c0b00c80034842c0d41300500d89003c100f110307103151003100c8000c0380c40f001c0e004510750030801050029540040146e422018244d0746844229a00c0c1e500100004440700010050f001d680c00c00424042c140547d0545184481030610701068035200a808a032124030507003002c141712b04540c3c1600e240131000350000704040010300e0310304012400040c0c1181c0041d00100c42011038400140a566483d02c4000c1003c10b590a204501404540003e0071811a0340700e0f4000d081e403070741c045015a4030705202c0031020042c51000c80b1005030140c40054019041602c2c126103500c0340030000600040140030360b1180d040c801d2241c0a00d24240300044028010308820500e012145051100301021503065420600c0ca9500c05000346101c408503d210089000d49250740960908052100450000c52400d8000303e048030426a2200700b9091003406009000020960919007800c02800e1051540c1062040c0c0155440f039440003a0740d0019a407890040c007404000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 264000170 1250 263998920 263998927
    0x8130308040b09030d092009041e0816030207090506030d051801020a050f0a12030e0c10110d09050f04020f0406030b0a0504050c0703110c031513060c050304051c05 72
    0x1281c0d54220b02904440b55100342d915000401e0700d004180c4500810803205400ea4508001c1030600e82d03400b0012910007117811920354103003078030340c00c0110724460030300c0e010401c40c3c5a50200300004141200c00b4015540b1103809088403505002e0740b00c013140d1103010400360500e400031340b80c1c0c074000c0380151403031199864a0b8101907040b036031101c2803007080e032615056101b080c0400300818004c001440ca0307d4204802411202c1451030701204410f100ca4640040c5814854581d6010f4000304012160000c25a60440002c4041008442d10510388880c9102c41c01400c907500310b06030b44004410240d070410b40d60b0718041520341090200324440d441070008440010301c014080a032003500b04141030311006045241c0107440b01d001a04031001642c9820703818100080705000c1641224011003003002c000b001e0604100d1150200e5101c045c2911640f100201c00300000b4117a082600c0391498442c1c000d503007000300406189014281da8000d440603259842001407201d00b60140c8088112820718a9031000d04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 264001420 1250 264000170 264000173
    0x1d120a0c0b09340605030105010519020703020402030a0c080c07020604121a07080106031a0102060c0d02040b03070507031206030515040203030c10050105010318050d1803050708010c0813030804 85
    0x90110068022502401540001d46501d00e41c10f032050380c0e010020641c400d021000310b080d0001100b40383e0001080c00402d0004001c1603030058147d6a80d0030007440303d41c0b2260317142c0c0300403400c00203540c1000b035009202000303000e0285520f134080d1002e8107564680707088988400c103201c0114000d40c07000030f610034000c110600882d0030011030b010445200c1c429511b10001000b41e41d40e10f100d02100c12000240941c0c004101c140e80c075018401e00a00c000e09200040904040003d440c0c0800800600c0543c02c0000d5911190542e54100ea000b403080c0143c0a40340d01300003130024004c3c4d01502d0305a0010f441e0740c2491075052024403800c000c50350b1002c010003040030314504241f503c410040c8140c0c0d040c0018024169020824030003602c1240c5034640c006032079810500013404407004000d0990145406400210001303000140200c4003041c00d040c62440c83d021400314400300e20303160300001c2c00c0b402a5100010300300c50541111010403501e45030f5a180c1c2e6608184410310243c0040050001880c1401140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 264002670 1250 264001420 264001433
    0xc010608031e0a173d06050a0903021503010614041223010f060314120306060d0b061201052106280606090314010e03180a091d120a0c 59
    0x7450540c0f500b031002c1840008242e0000d1850200c411a600c25002101070305500529141500508a0200003800103405005510542c10b05c900440086c4000001c0300700e030306e501400d2458005e41d8010714000500c0c41019000c0b0842c1c00a201d0300b00452174005642092a0784182542d080e20340200514a100c1003035240c00100949402e203588024000e103841801010083c09406100b40c101d10012030118554900030003482c0b140380b50748101c1c2c0c005107400005980f10004070b0340c014000f02d5030315407220300c4e82105c42e000740f10b11241564054000244441140e103d429820304a030380071a04998151800100c003103201c1c060754000c3e20b00d82c11810002c3c44180520001c4c62a8210f103103070b01d01c0801c0c4000102d03411941d058001c600415038518003081008110010355800c448014000e104800c83c10010329176034018040029035a00056102c000303161034a4030900e00404a40c0030911203d51124407081008507240c4c46a4114024603d0202c45410314908640040c0503039540e9842038030040c1c4889 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 264003920 1250 264002670 264002677
    0xa020121090c0801021b1605041e020c10060501030219180b040b0408010b27070c050601090b0f0114090105301006020604030c0f03050c0f01020c010608031e 69
    0x2290669030340c0000c0c0007080d030250302c1c207000c0c0602400041c0da494031040c60030501c20300c403110321604c0c0d44490420725000081e040000c040759000d031408100c407400700100d1140c070034401d10341c119468400b0400d0b4425400c009042e5084019590040107640d49a000450692140c2008030802e03036401d0591480e003920441c003810200060f03540d03154220381c550344215490740c4260b1016915040201e03044c00361070000e108185056000b01c40d2040b0700c0c2d10030840041008010101550304510380000580079502034145106003d6210042d5a82980c40390f031105c004002d10ba1001d030041841c0c20411a0700d5003e04129800007400c080420b0801035042c004440c3c0b81e1043c1200700c0102e45012011049035460040301e6104954180006100e152659075a800d01020394880d50465200030301780300219810580001c0c06940042c080ca907a90031030700301a038042c03042c180551468401c6504c06c000400b81035028104045c1003200a026440d611082d5907542e0042100c2000e28100d20026071544404400c000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 264005170 1250 264003920 264003977
    0x60c1e020d021209030a0c0902090411030103020d080a02100905011b11072102060706050711121909081506040f0b03060105060a091a090427110f0307030c1401020a0201 74
    0x80b26204102503442030b000007899030008c0400c90700400c411009190a002d42c4210341d000c5240301d401c5601d9030b0006010020280c60140400f200000e181d07621034800d006030032482114000034060743c000f40c500107009240c0c80710000c04007480b544480d90b41512a10a451540e4058801051000e0410022880008507003401c0c012040c11001c1d141c0050b100c0a02419450b070158800190a160812016065801c4480824542d030005c44401c90409400e5058940b1070308400c0e28030512101d04481a01c060985070000074080c03140988500c1c075803080c0f4160b51b10444c410741c4d00744420380c4503c8000054072481c05a155040e0040301c014001810a100030b0402d204040c07034420b06443c0c0c0c0315040d82c25195001c81ca03098007880004c800e41c0030b007458001c0b4131100c54030781d84c030b0f41380501100305002c083d240d182402400310f2281d00c000c50980d1385030004864200c5c402020398800b641e50345460b80301c0035400d1142c0f4100032240c003e01c2c8034a42c000f1840c4141d494042c2c44d03050107402c00c070310001c405130301031fa45 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 264006420 1250 264005170 264005173
    0x150f040c0518060c070320180a02210411030f21070c0306020c0307030314040305040303030e0a0c060e01030b090402010c0f05011104060f02160f140d060c1e020d02120903 75
    0xa0611001001000006e50040160080c02c404001003034600da5020b2084502a000b050310440c40d5520151030164000c1000a0050725080320240c16008002c40101c00390b424818082840213115124003051700c1710500320211003480d03225482d1561148040c42c00742e400c8003c0b0f4085103420304d500790014108613120f0714100f0079098903aa1800100c2e00552110a421f52001c64400b0805070548941903d0100710545101c032403034650f8008186200b80d000050406446119901c4020300400c451519594000c020701d02c903a866460003455000881c828500180c20201c0325820307420111a0940200e406945400c03500c10f642d150b44c0a06c8202880840701990f84582c484000a21000908042e105661314020010409080213140048a81c0410030704020448100407480c441804d00301114140c90120060b0030780180052401c01c00303885e014001500f40100c90f4120b076031149518121841348081898891403510f41240e9501d036000141002d0383c801020408051100006000e08000060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 264007670 1250 264006420 264006427
    0x506060f0f18040b0a140a1815050709090605030309040903020f0d0e01112a031908090a0e010b03040b062206030b070e01050d0e070e150f040c051806 66
    0x100850290101c442c1d0020208031050203200c10008000701007034114560340024000203c46410a81c1c1c07400d80901404801c55845403001d00c03070620515140c240380c6d08440c0d01c1c00b070440b218003c900900001ca0340c0c00f00203070358042e0118100ca4144650404d46002400542c10940107400740402410724281c10750a500c1703a132018403180c40040100d541414295076030300541c0e2440000250100030380e201c0c45405508400080d14141c02001c9490244074150041171140c0000c0d80007003402c0031112005403100d09441001141400003407002001c0400d03054540300c604690310306188032007443c280680c095210040021170003240300490740540000700100001e0400c070221180e40880c078062501c50448585611040040c0142c0260082d842022410100c243e04950000200329205d0501c1107041a5940c05031144880e40801140c0d0141410301c2c0c1c428050305000c0907810120001550f0135125104640040c0e10303d0605014043c0408020344413603061049281d1100d0314000d121507825081071061 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 264008920 1250 264007670 264007699
    0x629040807030807030e0904020d111216050a06080702030d11090612060a232101060611010501090c08130201030915060807140306072703030e03060a090506060f 71
    0x51003a070340190302c9942595600c640307603d13000d081543d950348a1031180005100b0040503883d20000300100548c02005038224030340c84400130b4034210401580c143c0a02c1405200c2d10078910031f000c0d5800742ca004a9400b451507555100840d25880202c0d111401038109201c11100861150840001c500c0d0781144541041c035003030042078803500400a0000400300401c14407000b418801400305c0503064107050807801d024548030800300880e140d20002d00800542c4600140068281300303040d00c51405c40001d01c403040d0b484200808030403a54000c58501d51812700005450000e601c0341c00642070f03107030301c510f100c40c0e40e5a42043c2c80c03900c075564164141a00e03954694001814000f44100443c0e01c0c0d00009035031402c000c412843c0010366000078403005541c0f0301e0380040380d80004629a00101d40d01d0807071190114140c0707070706000c6c00c405188504101c075071801004041e0008045a40140300350221602566201e01c0103082e2000c603500540990001c8004c030b001800c201200c94086100940410000c0350302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 264010170 1250 264008920 264008923
    0x6030a060b0a2105090706050903010e0a0b100e0f01030303020a0210050429010e0c0a09170318030109030f05211501020c01110d030528060e090106290408 68
    0x207401201c0c00254880005030f102c1c04104054020384100781d00400851400080466590541c3d0048205010008c28403803415a007d420402000f0510001d8407580c1445182847d0802da042c1c03040f038400075a110005c105050081d104c14030540c00b880c5070702466440c1d505d099000398400d060110071402103480d5000004c0a030701803940511f1046c4200f2914940b036a6098001d142d5076076400c606c01680c00c004000110340c403a81d40c0c0d00200061445603403850004000d0361046501d5105c4241c00001801012426001002511803608585200f400c4604050200340c2200c0301040c0c02000704030082c42c54803000d482403001c1c01030704041c200c010386200c0000e800100c04810803685030044c0c0ca2640350385901e5590501c2200d410000070308044007407460b240300164580c0c4855000c43c003056a1000080c10f004c4841c4071040c03044444040c0401d40c4c08841c0c00440142c5041c0c014000c444401002090070f140d414455002124a0300300402c0349d90342d00200c0340d5040540503607a079104074414030000c12070400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 264011420 1250 264010170 264010177
    0xe0a1112040302011109090c031f120b06100503040609031809020c0106120305160302070308071a010e0c0706020f250303050709050a090504050f03030a06080f0d02070506030a060b 79
    0xe40045040d2145002e2500a095032811000c0c400d42c1078060011348004e03140c0001458000301403040c3e180e201e94a0b540458201c0c2d80302244035070000c02d85580080c43d010b07400b0701d9100c81da028440310b048075580c0c032090041d02c800303a00c4800b002820410005010440640c0200d400601c1380c6083e00c0d4001000030302801c860082c3e00a25a415400241024052000d01c1050f0080c08000160f030781000b016140a130650240407014041403c3c8250100205442031041001540e40560429103d400030304003105440d400c02070424142e81c50754000f250641907008400c1c03044400c10f15103031802c41150380d28000f80d0401c1c1c0e80e10030100f20034400d8211608980c0d456003002c4982056265408080f0708008050703c10280c6054288503200c0c00170310a0340c41c1c04034418155103409130042034949a0b80741040c509059010071700f0b541d000100c20b200e00c000c0300c0e403c1442103900203400c4400340d8818440e12501c0b29520001340d405a44184020480e80c00c0200245901c04491240095451356500c40e0710200d070f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 264012670 1250 264011420 264011437
    0x5040f0b0c04081b150f040803030114090a09051e150103081c060506090f01020a060e01052a0301060e030f0102180103060909050c0f040b03010608060a0b1206010e0a11 74
    0x4402250602c55601e04011131190011243c160080d0180c02d007004c51011860301140810a070000a04840d58080c08811200202128000c80307a9960f51b80c8481c41001c2403122140b44101d80100205810240c3c0780980300101c0d8014000d0712109806076080c0d45111401807080440780140b001401d015402d5051160085019080482c0c0c2d404118207010351660030110740504081c54803005010544800301615040c060030b40701e02e0048600d0200503481d180384102c00400140c00d001c1d1207502601c064104030b020714190001c400c4000303e003031082c0c0c4504900a0905000441c00e100401c100c500c52030341580c0001c0b001d0305450742454000c00060030390340041040241d0407125a03601c101540e1610489004090004080040698a56466032111500c010041c8602c00070040d401312561107500c003480c4404014000c10002c0c0c5d5694500341c85070400c81c1c00c407101c01d01c0c0004110840c1401101d51403036014100190040d6803e16800b25120b2402812911409580c1c140c4041c4001c000e000810000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 264013920 1250 264012670 264012691
    0x61a10051608160c050d0302100f06081b03010c0201060b180f100f0206010e250212040e06091e010b0c100c0c020f06180409050c030105070c03030513020d030305040f0b 74
    0x1d503e90070604420318007503010300c1c054007055030740f000030944c0800c400710501c82d141c1c000300d6000c10032541100039009039000700820b80119410010402780300d03900b601e136011041d07000340403015050f00d05900b2111648920034401004100c940345071480d090385407176145401000c54080c0442040401c2c8810481000c400108550340080002e03941c04009850040140208005c860b1500344003000300d403401800420855100c01c0c0d4011405030090044490041c840070010f0745895903624060550001a608180103504d8a408500504a5544503442d540b0340361141004607441c3c22010300790703135205900d50415030241403040805038800b4020310760022100e60b60140c41c0d0306140108048031341d945040611174142003011100351008d104105166020444e40042c201d5007e050650505454554450303040d440d1404120116401c1494609001c0c0603690820455880100038010314084000182d440f480103800c1400103444ad030011365100744607824840f03103c6040e03030701c05091740b0040da01c1c0c2002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 264015170 1250 264013920 264013957
    0x70501050106090f1415031510050703030e010c0507080a0504030c0b04050f10020d0f0e0909070816030803060f04020d1401060e010c0f0f0c21061a10051608 69
    0x43e1204001400645810b0b51045580c01407840002c1b10303c900c0980f41006000d010001a0104542c000394071812480503000811228503800010090b0340401e60460110b480d1a1649400150501c21070390400ba05465503481d00c0101e0700c1d80c800b2500015044800c1140030040480080c0741168054001c00807207035095203503410041001000401d000e05030f400b41c102c00c03000381d0215034009581ea280d100d00e42007480ca46501c00310102c500e40041d404454000f00b0340c1090110003480024907000301da00b10b9054444a14a80080028210291101404141c81440030a003103107407100d15916410402800103203001480ca90708000d030b4100d1101c2d03000e100026801001030581100525440170f4003442c004502d104e09542e01540601107000c0600f44110301d0203030754100080004610043c003240381260b07520a4813074050362020f5100b514121459810021400348800400080c40912807000300180401c400c0044200c2c0c46030091520034280a003103401b514041002107006200c02c000c080e81070f918 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 264016420 1250 264015170 264015179
    0x210603060207030f031406040506040f140604060f0e04110d050a0303050106020d0c0503040306020702060f03130510061d190c0504050411041a032a09090903090a1a07050105010609 79
    0x2000300044c40c80b01c145820050803000c485440c3c0c0c1401e60007581145c0008060319441b02041c0100050402d10f02e0b0a464042510020b005030038045100b81d2080354140a00d94803400e031000840518030440e080d43d030000012a0000b4001c4030741d0042e442010b0460302441d40541c50f52460408260350980c0401d507902d005208103541409040014070305403e00840280541d6660341e9a8442c5120103400d8a0b03000c2003000c01c542d00d5008840261a0741d9401c1d0761241040d110744510040c441d03204035418403450a001442c0d08280c01207004840c0700000c1d46480c440941000900320f81d0081c4003c540040c2045c0740c0315142d00030301ca0080e942600740d641c4c45d01d680c2403100348811250801100009007000b48410000131043d4504403030020150358929490b40c0310710120b285400307000401038091041d040c108684580b6114090584440d08a664400315100c004c101a10b84c032528810716000b070441d080901c070340c10702c042c22100c02d0a82c2c4855617151442a488240c00c545080e086034000654140c803c11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 264017670 1250 264016420 264016427
    0x2a0302060a0b0303041404090807050d02061302010804200424120f081b0616020c12062805090a0213020a08040213020903072c150121060306020703 65
    0x55100d00a101e0410500d0040e50001303603070703006034480c14410820404211103162526080080500d82c411500d50f10361429140c9161111482c1502038010f200711400210a10545500341c41c625806071104c07245500c440d141c2031540d010f080701b0105000c0350340d003840d03225455500c030700286000c4020384403140901510800c1c0b500074655004e4200103a0400d07d600204142c0e145004840f503021507032655903880380c80d15109003030b04130700614071901404c4100046100ca0004201c0d0701855603007520a2461050308001d5006a40141d00d82158812000601d0800381c400c250003a00340880540c56400501583d60b8080c6c0300211103408568120311103030005c6081c4200882403040208000790705080c022640200b0b010401400a40b00b90003801003000503d04580c12506142806001d6403402034a43da0a00c00c0d406002e40c08c0214243c0c101380040302154480101805408079410400012000302c004451a4041402913a81c44511a06590740700101d8440c00c1c0045116000250702e9007610705000c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 264018920 1250 264017670 264017683
    0x9041203140c1819080303010302040b0103051603020f0c0a0c050f090c0a121103100e010b070203030409020a02011b08070f080609041506080a0b0a0c09051f2a0302 72
    0x50700110000081c052048000000d0b5002140002d00350009007846500095925610a0555104201240020501d0030f008401503060701c0c001d480c2440141001c800440803214100c80d01181400740e880304030452442500180082c1d0940a203150421036145101810050001070403900303402030010422080c1004106c8043c2d20b2070480380d00c8a9031600c0046840c040c407070004490204040514003008004080c0d110b4a42064000c100648a1401243c40c0c6030301d000c41c1c0564440300d01410700004403502c0c0350044a04045d0302401450a0924208014010f90130009200040d5521410410304141d85144001c61010321a070320850a4204514043d01c09048603801504000c600002c011054032640310950b00503034440c0c1c1000800e0403101640004002d250820a0203000700300313510040c4017481c2c19541c012035003414100005914914140e802d0203c500c07c094021101c0100c2c82c40c40d46030b003081c01c400d180031802c4c002c41000341e013540c0400e090713114854881084131003250136043c10b5040006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 264020170 1250 264018920 264018941
    0x20c12100f11030f100306050a0e0c0a06020307080304020a0e0c07060b06120403080718140f19050111070b04170c0d15021309060b04080d17040b060f09041203 70
    0x4100d034010805540350b0a200081801c0744160070003001c250143e00d81e0300c0020085400500400036170030160f01c0440074010301c2d450003040b0700c12540c095540e458004851011900550021460802590754580035504020300076680810100400204100d0344080588203401000d01d040d900c100e2490030340c0482e8155011a80100c00a00590a0030351340c00200c16000f031b8140c1050390580c0c0d60007134100c5144d1200152000989140c1e8400201130044548a1100003412103200c5045440e00b001d1060a0048100188001b295140104640c0d401a81c00d08221070000301a1402582c0b10a49100541d00c10ba2001d0084212080079128018082c44003203081141214021001113568903844001c01955560890066001071034002c2e60806114041c020001107105120459441419808a400ca84128110307802424030301944540708400c0301001e00c030446034142c025191511441050240248200c3d0454030900d414842a6640c00016115070300c070300603480707422411800c01016155103200c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 264021420 1250 264020170 264020201
    0x20c0d120e06060f04020903070906080d031b0e190609050405010b0a12020a050d060b0307021509121b1b0a060e1507240f1109010f080403020c1210 65
    0x500c0d8141d1000c80d4841d00a50119010391302c4421041c0010b00070b224840d60264944640040002c0101c0796801c184101d8242c0c0c0259103a80107180010b41c2a80e0400f8500a00ea00c1c0441444e502507005034080786000c0d4001e00403110054520020515205154000700080340742c04a0401251030180502c9000d4644481c140b07080001c80b480180c00130200304031240c25140c010801154042c42103094030307508045c095050000590303d02d42241c9641c400e0307802100601990b81040d40700705c040707442103010396000c00042075005181101c813070041c0c100c0c14983c2e10700c04101034404101c0500304080d01400b8240450690340660190820054101c00d52002c0248031044d801d0303171030035a40d98242803150b270000c528460740c03882c9500c3c0000c1c400509440c50340d50a900c04c4085002c1c0c1c0d08540c0540c0810580403400c000f0b42d103d21000601d24094501078a000600100303401c48511312844115420511a00444005103c82c1000501003c28201071a09907407082146140c81901405490003030340f19100c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 264022670 1250 264021420 264021431
    0x30f0309010c05272b02030609060f0103170403150f06140a091503080c0a0c0e010b0723010e030711040507050304020607030504080d0c060b030c130b0301020706020c0d12 75
    0x1c0444584080b0400411a654044c0300e1050300344c80f515210440404071002c10780d000709884458103980f00101c01c0c164020300c0b5070000610b00302d40024009003e004000581d0f6540da1a43c0d407007841c058004041c29030b0a102c180b000000003640d0b5441803421000350100400c400c0440341a600c12900a6402a80d8215241061010545821426106485106902080c0128400f007030810945490f80300070000305000424101e0500b000c0345080601e840341010181c0c0c241e940d420100c0c3d41c242806402b1400b50100800c100003a19581d0820803030300d84050742140b8040300c155442c21500000d801007000d800000d0305004010780c0600040f5815402c0300c0402035030031306200c020114040100002d00aa2001916130285800380041c0c400410140d01190b40a070091400202a6050650111011414590714942a16003ca0041601c24000d41004418020700c4600b034060400c804006816560070410000440c9290000f04018400000102112161071000821000700e100383c400b016403800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 264023920 1250 264022670 264022687
    0xc0a02090a270c1e0302120703020a1a0d0504030c02090702070617010e0604020c070e070e0906010201141611031204030906081509061314090607050708041e0503030f0309010c05 78
    0x201040058643c036901e407031146500d095450026289603017000e548082e0710000c1195203200000c805081e41d2080d6800f603030b800d41e01c4064000c0485485000c0d940d101d414003412901c8200c50f8000307036015019160100c240150394009c00c000f1002a03500700d00503080768009101c019041611172030210b40700c1421551540c9040018072981c20054801c903c1150000342c10114404100001d1000c0c0840121404403410b1005020341040051a8014051511600040c0e010360062148003c5610340f01c202d0180c50fa40c1c2c14040003620018901c02050285101c101c044d560810030180c202044244207944250505080c0505009000c5e8410400c01410707008100f41a41e00d01446a00310b84180c902c01d085850b850f00040802c142e00c071044c20300c54541410494101600210b10713000c0c2c9502d400b0b0f50015210388100311194868104080d000d40d004110801c005001201e010100c81060304502c0c1c00343d620790000034116808420715940c041004030038407001d00ea080c450845030f58680d04140340344c0f8a50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 264025170 1250 264023920 264023933
    0x7060f060e0c0a1e020a050d020303091911151309090c08010b0303040b0d11031f080c0a0506071e2105040501120506040b03010c02100b0d0b0402060c0a02090a27 71
    0x41c40072400075001980140c40304c00d00801203803066030f5000054880c00120b5800003587c1ea001251842c2461007040e1841d81e5811450341c048031040d0f003011078000c54900c05000e107c1c140094a00030b8000c1b060800429100c0c03680c410400026111241000c5080441410000b14100781604440301c542d141c2004210b1507940041200d007180c200c02c0c00ca0782c5446100c60100c00030500c4c400720384021040001004140c090403105d01c0007000070340e061540240e4490342555034030108940415040b2104810a000600d00320003d8007045204044001000509440e201c1b000004e03d10b0854005140240b42c46c40c0b0b022080d0307061a624030615145051900d4240001c00e6404800318240c0c5141d42c07107021038201d48132500030000700300f405802402402d8041000954400c084814540264540480d00146203002103e84400e50b8000b04458003540300d03034080080d6680090070025080c4121401d5000507182e003120300b03129082c2c80c1c2d00011130300503080ca441503d000c0448405508000d2103000d500050301e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 264026420 1250 264025170 264025187
    0x6041109010c0305070b0c030a1d03040612060911070c1a0306040911120d0e041505040e0a06050903030604050a050f0a15080111090f01090305070504090201030207060f060e0c0a 78
    0x900c2c210314584101e040c1550207100c0e0080151035080724904000c55016050029805103131080020003600f800090300c00b2041009004140b8036820802c0100505440740a00310f034142901200001c2480d52484c07040111143d40d5580e10391901c020941d2010f2164842c1c0c62001029044018000f240440c0314004041c48010400340c484e95582781e0100511072818100c50300d40e64058075804c042406c1403081651200c0000c10400040d1001c0700e0840a4105400349600d081c07240100e030071b5100e09000c20440900700c1600b07442e01a2080791070a002040c0c3d5805014002d601100280da6030f403d285c3c0c20b201c15281e0040c689140c5608040901034080c104054003039000114040010b116512080890803c980ca613001783c10070740c20070002850221285004081000044803948070801081c001910000000d00c07020304070707810407001048035007050b402c0003080603c1450700525180c010790300d21040f03840401060b2405035403200c1c184204802148000d8004600260040c00c0c0104440300415860 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 264027670 1250 264026420 264026437
    0x6030b0102030301140915310b09010306020706150303050c190803040b060f040f02040e060a06020d050903010906020d0b10110a11150721030603032a080c070905060411 74
    0xd441b40008981c500324000c400c45141005101466007061002e400001d400c007039103000310303050400351710000201040c402e181403000b000e00701003441c1c3e107103481e040300035003100030f095410f29103c0401d002c000a5010410001c2c5107c0d855030b80c3c907030f100c1c10b0075149050203070721070000d07070034105100000402c0307250050700d60142e8444980c030810fa035200c0100e01a480919641c5401a0401380300c01c1c00e03c00581c0144c01554602d81c40545283c0e02e09042140c4111140b080034096040124900748280c4070304018030f01044042d0010898140355035404040b41e0040f031602c01c0b4903684e00040341091a0180c506400407106107041180e00141c4103109848415600d4014207a128117080c010030341c1c9480080c8400c0d015840d100507103500383d9090901c1e4040f442d0b10036031907142d0183c041011450203403082d00e0039650195519000c0100c0414080c00740b80c0140100c0240d89000780c104000a04140d00504c2459145030180c00010728108031002607030409441789104904007090708160029800a840700c80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 264028776 1106 264027670 264027679
    0x60209121f110307080f0a1407030f0c0309021e0d0609080705060a0221150907110c010c0206030403030203100b04090b13020a140f041e06030b010203030114 69
    0x20320041307500c0404145004049a101c0c982e02c00d91a51000f4181c034005181001d01c18005101c0c2c070102c1d2410002500d41c0390551f40035010340101c2c030200c1b1241c10180703c0b2007844da00282c801c020754030352100c0160300700d028010252782e0070040711750840d0026020010010f40c0c2c1030004441e400090203444912680010801c0d20034130b4400c5940c001d401300c0203808141ea50285080028034054400c0c840b14003a500c60743d07019544c440d0811300500312500d030f2080d9981401411400c0290081005061091050301e06025884403001c0342d40c040c2d4540b400590301d50f9024034100800499400c0f102c010000420041801c40c07076984440c181d1001240da14109000300c0382c4040a900c900c4054000007045c44100d00c02e9010498054080c070254034484504160316101080300d00000440b540c41950030524041003402c0e0588103640b440003003032000e10300c3c541c144580b00e1400c03040c1c3c4140347d028 = true := by decide +kernel

theorem cover : BRFrame.Cov 263848920 264028776 := by
  have h0 := BRFrame.cov_init 263848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 263848920 ≤ n) (h2 : n < 264028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
