-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2265
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:10.728017+00:00
-- url     : https://prove2.me/submissions/d80cc484-509d-47aa-ada4-eabbe75c3270

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 407194244 ≤ n < 407374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 407195494 1250 407194244 407194253
    0x210020a03050421020c1e0603101d01050d0212010f0906050901110f090d0201170f01090b0f0112200c010f051e06062110050a0f0308040e0c09030a 65
    0xc0b0440c0d00301d4104003090202c00c0002000c40e158001d502c0c054000b01300040c902130401044001006030f00c0818220101e003100b00c0d4a91401450183c1000040025144e09010090250761505040654016000da0040100d0364903901500d0f031309901a074000c1001c0595216440c05003890046924509050544181c10400560300c201d10504400e07000f0041d170b409800f20540703035100e64810710101c0c02d0f0a00c4840c096180c0080d098bc0f1451050403c1c58a401d4030890703010600700f08449502178040c8000041200304180d0050400b518011205010503807410350020304a10320403035041404c0c80d80c42003502207105044081400101c88610001d843c3d510b0021210b003e030000180d01e040c03990914001c160307080840389030b61421141811117041240e6542051010350340084018a0380207401d646621a43d04080c02820700031005642d020403198104018400c540d56103600c5082200340c4c900003040800d03421030544083e0360b072250500050b0f49403a084051180110401d40340e150261100031001c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 407196744 1250 407195494 407195501
    0x1e1803032403030403030806151207110c01050435191b050607080c0a020a031415010b1b1c21090f030f020a120e01110d02030703050a0210020a03 64
    0x58064200041009403038070140741d1680a00d100080105071500c0109015140080782e10381603041d10241d50703041038007002182c41180f0041e034110001c0fa043e4152845403203414044151010030a00b4820310305885d181150726200c410415401c003000001018224801c04410190000c0c2e00103400c889070807005501c007800a00020100f1a003045001a9207600c800200b500ca60490380020002d90400000e620741503c00d50010b6020344c554001c18040d100180e940d5005140950b00a041400481c10102c24292803c40741226405001c044a001013006002d140c080300c0084412600580c2c1c4500741d4004507140046881109031501c40111680c40c1055100a90650600c000c08010350b406291100d00d004039442d141002e8540d007000522100843e004809403038086240d841124400b20007074441035000c0c064887c0d900000b13200320640d00c1040d80c0c80986030388450aa100680601994804082d5507403140c010003c040c00f001240710310416009000f80c100420494500b5580d5003a8640024002c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 407197994 1250 407196744 407196781
    0xa0315090204140906030705090a0906090c0e130b060f01050903030409020306190b030105060315090403021c1d09060d12030b100c0b010e190e0c010e091e180303 71
    0x140082182000d40d103089103840d40100c4002c6c0c00f07084101c0c284024800d503d0001046101c403540c4400c03014000410b281303c3ca03184079000f281004040340c100307502d403030285002416890850004403104000319004900b070a803c4201191003100840000700162414092518150342c14040480d0000c0c00c1e1919400542c4036550842c1c1001d54500341d40310211003d82c05010351240c041c01070005201900f018002150071a440780840e222040c41c260000b1401c0c00100c9003100160403840d120103400301d480650144840321400c11070300c101c212000c1c1241020b90b100c41d0a10a5000d0404100c00c0e032a1100c9500095400128507282090b420303001801408868075141d0087c07090141c2d10108034031800c01e40d41d0540d40311024051503483d200301e01d00034505c0900170001b0601101d58514801c8041d2082e800130b815140054100008040009000e02c1c074401c11150241c0c0d000340c10045110b1781080b80074030803003210b01d42c0841c42c3c4411200c1c940000401018240d184000414004042c6d40c1c01710360040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 407199244 1250 407197994 407198009
    0xf050c07050f120f0307030b0d060b0405010605090d170c0d0c030207050a0e1602010e1525020a030804050c0907110f071a0c240f0114090c0a0315090204 67
    0xb00407026080d82652456800904110302000744078201203114490011500304c001441d01180b121000c9000070013005003a8002c49070540d075000b841020741024064075004051501b0b085051001c4440856000c1c23900d184010003480026034540826000001a109030000ca80c00b101c8001c0303900640a000811044425005442011000034152410046200c141c45801c40040c42d02d4442c030000d01c0a1b40100038002d010b5549071403412078003650400800481c2c00c05805002c02e43c1c1400361406111503031107041e082c10701d03115014030a4202e4001584507121540351038026001d035958282581015102c6100c50351064600c424880c003181e008a4498090507001e094480e182541070071542d54401d58420306ca2801d45001c000d50010056001403d886008402070b603c01c0140f05c03403140c1d12614011aa14041c040c81c200b071082c1e00b68400c01d03142c058856041d051100c0080140000c802c200c0041080e1850580084c00800701803080d000302d1807001231103403132003550303078441e540c28000e90401d00a100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 407200494 1250 407199244 407199253
    0x111130e0105030a02100c02030a0203030d0f0f060e1902040b0f04031a04030207140103060305061003050f010902132304150b010305130f051501120c060509011e030f050c0705 77
    0x240030300d0003191100c14240d000f080301c1ba10103500c48080da000e10050788243d078107000c0c0d00707031840142e1010b100a129081031404c0009054180700c428004640c0807019403c0111b282050070b02081d404410004d400030380c01c02c0701034121412201c01c1000f80c411500081004007011031440b541c3c080e5440540180d0f4030444c6600d121110300764203662080c9040b030300940107a0005404004003a03120650010303000040c5070100e60f09449407501e6284c00070940c0d80100c1d90100314010014402c0174042c0280c000350400003800541c001e41c001450a6100d480d400e40000d954180b40c180080309030520300c0020908182c0000c85e8505414203180702e041500e5007070320650922054502c25840307441660310440210010ba4a0320081e500e400e003074159004400c0395030340308681d4042c02c03040321840254000c06075594404044130407031802590f00303815503101c003081c41001c0c03000302c2c3c0030380e0000401d4070310682800c11440c00300e0328103008030b020784118965400e400d0b26040034845900c481c00000c00d03210340500d0444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 407201744 1250 407200494 407200499
    0x30c0d0c0c1502071709040906090b180d27120b04020a0504060b03040809040e060411130203090a0f150903050c011103071e1403010618081c030207050111130e01 71
    0x207071310071450000c21100352030898085d8060250041c0c07501c001e000d0000104091325550308811103009000645035400000200318050b6810740c0002200032041015240315043e00c04041c0100e940c0812084c0340a00741040c01d041c401c819200302e40203040c8075021071081c1b0924103040100c1c020a84042e8080c8803080800306090415000313180c2214904501c052441ea520380703802c0b405070000d0040e658000d4030750b00d080e22441810844280a90701490418010311f04040c20016903407881148034659500520410101000104119450a8010100142c2a0070030304d0884c111550046055035000d14107080c080c180b41d4820007510005480200800c01c60b4000910203105000449155000420110700c0c0c2c50004417106402e000c1d0a46810200140c4a17040042e880c01d40091b00400300007910340c5083c0345510381c550100b0340200602401782c1500d20011440d41000214441c4942c02e0540018100f01045030950029840c02c010000454031030050700121810064944605044660444c001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 407202994 1250 407201744 407201783
    0x19030e060a031a100c0b0a020c12030106110a020a050f120f1b0f0a170a06060e04051011032e0603060303080108070e060409030e100503010501030e0a02030d0302030c0d0c0c 76
    0x209080c00c2010b884041d0501c545035031b41c182c20900103107072281c0b80d5003d00621550110070003041e080d10001c0076001c1d0322981000801054003004425000c040d610148102d805a1109100d04050301c10558041500074138913400304041c20003410070a10544104040d4244510380442c0e449150172070030340c006180a4034503040020b417600d8a50810350100034014100141c3c0ca070510041400403940056461014040e120b440840d10b00d80d00003102403c04000304401c1000521800d0358280e81c05d4420480b003103038007a20365202e010080c0f802142040d40600a04007080e006040039001070b0450351001e0258079500e000b006031890307100031808500c2c0341002060f103600c049446420b0f1500b102600c115603440314104009005002800e0381881405601409151202d001d8a0070703c0d0016100e6560b2945400c00060485401a01c00c038080c0e0042040390006030340200c0d80d081185054070f00541c41b502c0344920310115108120361061054545111280201c1e000111900c4e56401f0b41c00807400b04139940b00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 407204244 1250 407202994 407203009
    0x20601060e0307030b0c030921070c0e07141602090408130e13021c0b0f0f07020307030203031617180c150909090118201219030e060a031a 61
    0x7009000c3d4085070006105c442d1b4000180d40d1202240c01283c1c0502285800200c0c40c81c1e90300440e414004000490034240031185148400030700b03405051941c030303240c07040008000d40c2119400b110180b42c002110742013401750380e00321160207400a0014806d414140741107070700c561240903c031501d54580c0200003429008004480d1045400460f0800501d01c00d0f4204000440d840140e90300001c1111001d4008c10708800101703210340d10680d0501b4203810101d0240741100e90040c25141150300401003040029400300689800079540039414a00036041d603c16a5482105000f804ca00100350041041c000f124001402c01c44040d07000790380c1600c540c10107000d221424800b2407800540c0820018840c3d08102c400d06a000045000001e80034440e003035a41442d0f06420015100303404684400310b56071240390182d4526040460381c4010b00c004110400d51202c29607150040e89204030600c01c801d250003a003a082c201c0d84010807441e03031840c2504029004200d402c080c10030101c40002001a142040c44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 407205494 1250 407204244 407204249
    0x10f021c090203150c0d06150905040c050d0518010c17100b030f0a0f0507090509010b180d0f0206070822050901151e0807020d031406040506010c12020601060e0307 72
    0x103000c0c0120110002d001e1640e408060200b105c0c0039400c00c0174000b652810320821002d00206180d40d2900810a0380040c10458150041d5200d80d240c8401c141c0307100d80190407920140040640424a43d42e1380002c1c4260204c0442e2070f00381c0c0d5013000ba0841402c0c0d48104241001d100c0b0544800c2142c894405a0000322828000c0c2c80b140e0b00100086003d085c2e6031030507254003250682010401c001d0300b230858419550261004404208025020b01582c80c04a1426000d0700c000c00c000d600341041418040360001d425040c0c00d0068104004410500c41102000f881c02600a01210782d039615a140019141c1d020400803102601030750b10b41610740106031b9505040380d03401001c6140ca80d00300810701500c40307044020101440075141c034840700b42a0307003941c00c5c0d8000c4980c2c0703c156141ca031000c030103070412022f00e4100c810541340004c20781d000700e0714050380ca4200405540000d296603410006a5608000030000340c403020028030442a0203074000f50007810380b1078a030384e003081d00035102c018150344245a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 407206744 1250 407205494 407205499
    0x7050105040308070f051617150c07021207030f021302091e0f1507030e220c0e060c0601060905060a08041101090b120109051e0a090212010f021c0902 66
    0x1007108001058419010f0044140540043c81210945a035150325020190b01010641e00f00801c04008200020740b100803000c40f081c000c0d0102100798841504041c400800650351804041082e90035503d42050100c0034121200485203069120700700000c010b01c805508134410350869003407100d1050980243d0305000d801500c40618003403504034040c0103000b60310103550071040c12410007410b0754410080f1424181e140140c6c47e40c50706a402c000308505610000180540c0200c10402d42ca0044420080101c1d4180000000c5150f03000b04100c980d03281c4142030b1980107002103020034801c40c01042d440d0407070302181caa000e4000c0c2e0310300c01c0c02200e000c0d001d10200440c1420000502044015034400d0000340145420f080384c075100c10049449401000c42c6130005141400140321480c00c40c0701c0d55811044d81400e030b42900c0140e2030303000032400006048112985d100e00704103045403140e9240c02c505030a12402031022010840f43c03d0005c0d0052281b10004601e000c111022200719445101000d5402 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 407207994 1250 407206744 407206747
    0x10b040c020a0f06020d1d07050d0c0e0702030f0a020d170c0d05040804050312030714070f1209170a050c06030f0402210604060c020d08190b0112060b04030b010807050105 75
    0x350b0300c0701400031000ca00306562031360b005c10080d070b4001c2c10341c420b044440260003101e503094000b0500ca14580203098201a00410446a400c1c02040e0701e200c07070388111420309009100310f0307a0f8040200d0840c042c2c42c12030544210041050014035401048040d032403079861744c4d001d406908140308000c280e4010380d81408280c00420219121907155080035500c14042e00c03003646000d603500d001c24a0720544000003e182040031092209165001d44c20031400b07400c601c062070400400751241d08181c02141801040b000340f078410f0309211801204214000c200c1152401d1591495046041d250854000125160b0003000b04031101032910106607030042411050200c80f0760340703550030720820007011001940c00c00001640c0c0c1d1079580c0100030403031083d8820200480e070b0250340c00020340f0300703000b80e4058001c0c8224407040048142c10380102c880181d011900c0815440119030060700d4400d0320540c2d0108031800e11002007150715800004000f124803881029000d0303aa54811507480700001e01a0fa0b002610 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 407209244 1250 407207994 407208013
    0xf0a06060f0507030905150304140f030a050d1d011d01020c0309040e03070803040807150b0d0b130804090b15040f06052110050102060907050315040c030804080f010b040c02 76
    0xb2910240c280d10384642400f141190721040010300c1d501c4544804d05245000004010070440c140085e224101c1640000300101c112042100340c4034000d0450007010884045040d00703080303607581c021109035000d000000801d000c0940e0b509019000340f054050f1501a00048005210014421120040401005581480c0b160b504000c09403424140800483c13200748083d60114191400560050f4459040c0c140e032001249000d0100d49110011a49601e141048007402c0362149800c0c281c02550004c0c07401100da5984050f1443c01e4984070000d84449000301d008102101c00d40d002c0d120f182011039070796540c40c0c00d680041260784228040c5e0789030010700103402c10083c1d016401030a051280208100d44241c03a605584075641421a11640c030a40311600070449540c040c0003040c0c0050a100291241c0350410011956904a04561483e04011700001506002d2448000c001031a4442c0c03403242c3e90782e0f0300e0304400d070b955410b080403e807194a81903001c8036515007440341e8281c1c0300264024000340d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 407210494 1250 407209244 407209247
    0xa03020f1302040b0d09061a0913050f1b1503060109090c0306051e090a0e0307030509060d0c0c0308070518041a030102030a09060e0a0c0b1c060b030f0a06060f 70
    0x404040850744115000c2c0008909560b850000d010b800442d1840001c0c0d150b080d00303051302911075402c850348098800640f02050f0303031241c1c00b40d941c1c4019509002c000346c20b42803410134038149030b554008a084c095105410045849480700444901c5c0460355103400070300054854150344070030f441c1d03507011030408581001045440e411004501e1980e08000407801ea0720400700e48030342040d80302001c805900c4844001c2900c0d2407246140c200300402020000780450b4082c84c3c1e900d10400c0006010303c2000b15050645680e017900700c40c4d9000b00c2c640c003400011808400034100d032801860803400b084a48001034075541c45542a2800079401021010312030341d1840501005000e08000746210780d0302501c48594a45090000b5030150034800000110805a42810b00c21503680f01004c944641100c00040c1c04202181071007001e50b0700300c00100e9504c2000c000d0100e061500304020b0b001c0d441c1400f40c005617850141c805140b01c0d012594280c820341c0d807214040350481d41d5a008810200b03e01c01301480e01c16 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 407211744 1250 407210494 407210509
    0x3060a0b0f12010b03030d0c121a04020d0204090e0304150c030203032202040e0c0a090b090406180506090109021807080411060403080f030417040b0915190806040b0a03020f 76
    0x2900040e00010b85240f4860101b0708581c01019201c0c0342c2501e4100c48152030b40d104e07403044141000c002040003000002964440d002c039401e02028440c0e0780103d5101102d240c07580c100e90052294482c00c1180c2403105040382c0e181e411034410301c4454000c030390003007110301d024000110742e50307170f1540c00355145580d0045024094031003801d00100c202915401c2a0050f04c85e8401c002c81e8030002c1000303001401030b000422102c0a4140c1003008418184900200c0341d03262078824580140d03000402007080c03908003044461018003104060f001384242410720030101010341c00107200b14000d07100d030001c44000c04c1c100302040d0000d403008000260480d00080109058268031030b540000100040c1c03806036280c5824209d43c0010304541480c075800810b000070040506a0001e9000903084010f061a1601228000034000c05902d1802141081014054413010740120b502c00c041c0b01c1c81d8401482c02c5001d00820240007258494041c0c1e280600034180c0d0303e89803401c02e08980e0b0052102146024540a01201c3c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 407212994 1250 407211744 407211769
    0x71a0a0c0b100302030f070306050105030f032a07030807020f0405040f031202090a030605060306090708120a021002160c09050c09190512063103050702010908030a090503060a0b0f 79
    0x1422021940407006a400340100c0017101c0c86c0e0001081e0383e034191f0614030110b0700c041e80711031300c00d5102c402411111440442540d055032240340383c01d082000d5980ca08200c0081d8003281050030301400b200402044440e60180665034025102e42c01c4051198040c0710443e0010341d001790125514203000d0002031b1240c48a1010f11000d1040541020b03130b20000300d1610385032500103c440c03603114000c01103e420100700c42c550100340c14004000c000e2a0003280c90b00c0d020400c24640480d10001451901c8a0082021000a21a8107421541e031000d00c012100040403a0700201d400a2218400203141821800b82d14047c501e415042403420320840f080000a03c008031000784002c800c040c000031140c0d035a080c010310341c8a40c4405888503181071000e52180b420821241c80e9116108a100c21a12090b8464a0080b903454140242d5819240c001030f00d400720150f00240183c440020818801c6a01000361008c0314030a800f111f6281c0c480718564010340b003420102c1900481000b48551682c5440c00f5885031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 407214244 1250 407212994 407213011
    0x60706051519060206060301020f1b150732030115090302030609011d060f01060c030203121504060503030c0c06210703090c060e09010302060d1805071a0a0c0b 70
    0x402070340d00d80411030900100701c6100c2c000d10300716000c01006805112440d4000c50071002189001c1c55800920081d000c0c6400141020550500801030a44c081108001041404140321214504071100510004510580d4500be51080050031070941d4540f2580e505580c5c40800740341140c0c03c02580b00216207420310003804100c4a0076000000d80c0b41840501d0003403102100119038401c80400c01c0e8040c0d10740d140c0031896075101a08008a039110b000361740e070545000c0d00e05442e0031444d608080b441e41c0291401043c1e0040c6134000d01441d42003090011200243c10fa80510266986e03000301900c90154070301c007414a07006004034000350f10f841c4000b412004041e0f5098040000400740700d120700b85048450001003075070b0f44400c005211120102d40700402032413400c0f440085420000c10042841031000a020312004180d07800f610803590400c01010303a90045004003100903050a0f5605c041e00c1c8601840502e05180c1030b00c4015a020458050f40416100c0301160280b641d52000b110000911004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 407215494 1250 407214244 407214271
    0x10302040f0b0a03141302010c062304170c1f140408091509010e100324170606032a04060915050103021602010c0507030b0f01030b060f06070605 64
    0x2409030300d0005100050b00000b0080c40e142d160700741c8003404442a075001120103858400800c0380102841080d0703840c095080c13900946282d0b03185807a5000d08084800351002c800708c40c8681030680018003280384103901404840740c9120417210030940034401d481242c0210b030001124030003000800000103052105a100020307035102500125a20940207850480b098100080c00022030301c0c0c240d41a600f484000c0550758500400c1c1c1001801d6422880c0d50b0601820300105503c8005002e44c2c0001204101c401c604c1a00030302e412000740542c07103035001c2c4094290400801d07441441c000101300c0d1040201800401e41c900124240081c1007020343d0b12018031100c0e0201011040d00c450148000904a0400c081803254034503401d180f50b0403854000604040c4180200400b072a4404141105543c082c20b1121a4807001c1c10070b5800d04251707030000380030400c1c0001401035180422301c0ca1812030f800f9880340e007034585605c000c0100c1601024227041c2e20080620802c8003007001a4881c45d040072081e940003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 407216744 1250 407215494 407215499
    0xc110703060b12160f0b0f030a15050a090c080a0501030c050630090c030c032104030602040b030f0901060303020d200f0304080709060f0306050946020a090b01030204 73
    0xb64a0620303c80c401c501610b05050f8104a03e5090105d42c0020b4001d00200c5420048642c206045c81d00005100c40c854588488140f6401481d03042d445001d0000509850388941e21210407070041c1480e59a001c0005028000103442030401d84a107a06891340149a03424051a0504104180d040b03020300c000c411441201d0b1490351596181200d43e0b80c0040540a0354601d0f10500141c02d101d006401d95000e41c000d00382d040c241e030744c000c00ca5001340d14155419804250120502c011b040c040e9070401040c4510001e00460006460030145200da54006a1610705581e9901306500760b41091200402590000a0140380c0f42d0040c0000321400a02001256072000c40d0b040c0c151a11401c0c0003603e8641d080042c082c0f00d03102c000c0c002c01d40036000369502488410b1800c11220000b905600c00501115038900101d1f082d60340900c50303103a41c101d60055aa0f02034001035802d4100386103098602501c041c08151041804081b00e0b424100950000d02e203c58031482c01015802400d50794614504041d42008003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 407217994 1250 407216744 407216779
    0x1902030405072c10060e060a0e1c06090503030f010f0b04030816050a0f021203040602061302030a02030706080919031b020301180614100510030f0605060301090e010c110703060b 78
    0x1402d00c200340340700e21010201e02e0300c68080d0800440001542c0540410000c1c90360050b0440e8845401980a036a044c05881d011071082c1090000b00d0030080400780cc0100307440c00c0c41400030140d80a403825040003903442c0d1f0307181500c80200d2070511684d00150b81c1404104013083c110700144c120100042c0882442c80f80340d40e4ad40f82003015400003111000c0b41c1042c0d8805505000c138802201703035101c400442ca0316040400103550f0301e030000d10300c02e080c4110041e00401c5403028420b41d210568003401b02e440494a42101030569501100e00400c548520310f0309030380c0348aa0b0101520110f40544130061401244100e0112424260406a37010340d200c40088000c031582001c0341200764056440000e608000035200c070481c8001601c035000b01d840030081070080317070707142c401441c4125800e05000405040440300706002d030030140c1c040750348401d0210000802c1c045980ac05104168094000c1010600f200415138400d4170820b40040e865105510500004482d644145424040144108801102c5060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 407219244 1250 407217994 407218079
    0x901060309060b0907020a020609030a0503030c1c060506032208041203080a05092e02040b04050f0109141027050306130f080a12090b190203040507 65
    0x10765078011210900c4024440d0301d0351510f048902d01514104110020350300c2c80c5295010b8407131040007a12a4881c0e03010803120102e1603002c02501d032a031400008500c20ac0c0c12100c0e01c0c00742800380200118600045205003000c1c0c0700c3c0248603a0864851100c048079a45030f0204444001c11070040c1c2c82d02045110313024000400c1d8606883c001080c40e0f280c0103007481c40144c054039983d82804140310481c100400d94121000c2100002c0a80110305980c6030803140c807400c044030030360340b0014010900e80200c1000b0004e0b100706985074101d002020004449079402442a40c1c5802030b800c0180700b05107061607000750500d0315468010b86134200d50318040840404c00b5660349090740d20080c100000c0c00c0c01d00c0807035440032030580c5054081010383c80e071619104009100404511000403500e60080c0605241002403010010070045206245003e02240c10140c503201200f0001016010f4848168000c403445654040c0150111a280822030059254100180c2c000c40c44000c283d00c4404bda542c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 407220494 1250 407219244 407219249
    0x3050304121a15041413080c031b060717071e020304050a170d0507050c091e07021f06060c17070b1504110a020606360f1008061b07020901 61
    0x408000f001580c50301000300311061045403010383c0c5400b1003045400103002d00500060340d000001c5a540b80d418080c0c0320704501c6103507040f100000d14002c140540000c0042c1d628070518903511280940b0640403401015180c08840d030301c00040c8440d08200c00c940c2101d4280c40d1660b00340c01120700300703500c5d83c000421116907904200e10000704008010203246003084014a07040e004d05040d443c0ca81d40791510b0762907102c5143c505e0f0081c0c540300c0101d5400602c0c0445410301407001144112182001103000351140e46812000ea00190b4420085401c074500f48a0081201e4071a1030b58003886842e42d40d07100c8100002d01c601398103003106000755008103085401003442420000c101b8244901c00c0c1e01008203d46034140929003905041c040000c4950b00094020b800010865006074094080280c4243e40c0e488103403440034820118580d040780c0980a20311a00508100d544511583e03960603154000680350702c5807003429408940456903030744281c0c050403a900d41165034540b4195050b00425020002030317 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 407221744 1250 407220494 407220511
    0xf08090d0e220b0406060305010503070b130509160206010807050102030406080c1e1209030906031503010605150901081501020618070302030a030906030f0b0f010f030b1806150403050304121a 84
    0x11410f07005103240c180b281001600d26424100b03d19410240400d40e039035014050000084d01c0000e00e803c00660342200e090052000400702c04c514540700740c05180c08194000c2c8003025200b005c0010541072800300d03200040e41c106030f00070b40c20545400341c00c0366810340103000b41c400240704000245a056001000d00c40582d065500c10b9643c150241c0c201945070741c0140324100d02c1c0c100b80b01d15030003944e6060440390040c0000407210002641c4600080c014006944100e80c0701324000c1d4001c1c48034107020b026010222098894203c5666031407940700c0c00802122031240144c210b20f00042c1900207564042d10b290300c400088172011500c03036011030b242200026085d400300700441020007a0b00d40c1401100041100ca110a100802c21403000c501124a01c1102c50305000381c03d1805a5024881c0d881404000801444c21300c40c0c003604104a0410700066840350701400105d141100d0381c805140032903044035800343c002c51504d480c2c62030311324486943c2501200c5e8852490340300900c00c0400c156550066405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 407222994 1250 407221744 407221751
    0x31d011215080f1609050106020712030201141f0501030603050307080a090f0603050a0608010b030a03081e0a050601031803350718051e0d03050405030601060c02010f08090d0e22 78
    0x4441000700700f2491303034881c1752102d00b00401031103155804180c000032508412082046440e42c0c0c502a40904049070100414000c2d010070400582c00004070003d59142c0151308a08840d140c800460554070030380006000c0d540208501400101100c00422800070070b4a8656111611250401607503000740e446040081e85510902091001d5407182400925044d8020807500811102007504c841520740c0141c140880d90340051141d41604400981c00034180300380310428588508200010001035a000e0b0000e80303800c40600c1c0203922160701081e02034164030b401c542c3d001c91035184003414140b88892000a9400c00d060207200d03003051a083d0084030035031a90319400c0c14102416209825030b6001074070401d07074801c0d1640500c500011140c000941940c800341d1903c5213040030b031000d104941c40b2980501c00c1800000d074543d03229034040541c5100740c2c1d9481448072490f030201c9482209545010701a0050700400c50082d0149015040e81c00d4041c229060848400c0c1d190b402103100411a120301984 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 407224244 1250 407222994 407223013
    0xc0d17040b0903010f050402010c02040903020c0a08211e0c011e020c061506070305090402041710150e0610020a02132309030a080c0702060307050403031d011215080f 73
    0x1d080c010304020240d01c0108002071f02d41a00020f08004c40c14a000e400303143e03250585000c0c54070034800c0800620000d40654117540e40c5910f100d68504045d2901c5040b800c0c01c6a4070a0344540030000c4a18215090b9444c2c94540642d03c0340340d0700e99008101414180d940c0c7c05040305034012000b4803a2103031042c03100058030745111b03081e00740c20034000800c940031041d181c22000c0001e60342d80c0c05a1b009103800d4074007a0780b01c440c4080450002d10540d0406143d0b4a0007040d4000d884d01e0024a1990329801c0c02010b00c41d510720309523400992040c5004411880c4000c4d80014003500b0003164030414030909104860070202c2c03a801041041c2c0c0b0030070f07482070400c0d2180080d0301c00000b00880300300149410785021495240c0071086513183e001d038001c050100985080800d40c800001815079039890b4001385059502e0810003030103400c07603009100480228080b10401522040031200d5110549010b860304031000040070070042c000d14040030400c100c0031900001241c00341d420442c00440440d544010100c0a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 407225494 1250 407224244 407224249
    0x405031006050306180a0507030605073207050a021206010f0e0402090103020f0307030516060318020306010608370509070815100b0a0201061401030e0c0d17040b09 72
    0x1040500c0040c01801d100e002c2182d510001103290f40b204002c0710541d13281c0708004445040c0302103082d010b450381c810f040000c4140809a40040d0003091142c45901290300c03404880130403034445038203000c1c60407916243d950b1009004002803008500c62419a001c0218950000300c2c0b4130108429496158081001405500d05078100a40507041510b9200d1151034554000b03400d1410500009000e01107803006510f007a1400c00841300503680c00016034203200c1281610f9080b84040e4801c200003e0306004040f41d00c440741914488141d034000d0301a1045030b00304002641c0b42c0300040c2003200e05082c0980c0c4028910b5041400c040704411281c0006031800381c115000c400daa00141c5103c040c4e400020b0200701c41400007900c0d03081900617210611803a40d8074403c0c00780c98501544880070f06000081c01c0a1025810b520410903502d80700541c1140e51060360046040310f640300c807240910f9000b015001170a02e030000c50625881d109096240c030070b0360721000c07880b000d8010794880c010f01903011a510f149132 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 407226744 1250 407225494 407225503
    0x60b0a090807080a350a030e07060806090a05091213150306120f020310020c06060909010c090b07023111070206040e06130501060c0501110a140a03020705070308040503 74
    0x1880804010484800c1c642c9840c03d440c1c405d01c1c0492040000181050250f88207110040b80d50090480440e44850403880041c001d840048103485190045901c0860b00901a500303d50080c90701600050140e83c0301d15a040c002c00c0d0160141c2a0340c400e1048001003800300d0401400f511076000c080c080d5407440c05080c9141c65107202070701414141084414002c00840b141030203502504145103550688544c0040f03030501c240724a00002040c0000740d900c03860030b000250385024000c207550f80c0b01190b544c071019600301c40c0b00040481c0000e910700010040c01140c06c02174090a40028030100d40304141c1c886074004002e01d02c855030f81143c200c45454540f1031451048c0030f855020f000d41103251408542c0080c00c684164024802128501c00c04521641ca803060814118005040c00f000156102c0d000900303400240c0c6021202c540c20011808039031103043c3e00707075000d2030301c2d540f5010403816036003038101d1454000d00104810035a00b80006008594100b11200c015070140107203903075841c280408e05041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 407227994 1250 407226744 407226749
    0x6091b080c0904030f120b1302120603010c020d1d0a060207050913020f040f02070209040804140d0b0c220f0501031d070603020c100e01020903240613060b0a090807 72
    0x3244220204401304c1c0e0450700004581200f40350100e02910014910303002803400d14420380d007102d11034002e025242d03d281c2c010011600101503510040d50380c0c60406090381d14402c0c81d02c006801c441036460400f0f01464a032980c0101c01d030960150584844003088034506540e00080060780035010404c460f080c9080e00a4101503449800386159155401003803040c0c80b0f2410791800303195903a122000ca00c00a038182c95803150b006050900750300700b40c24064900c1d007041c00381a01c00c2501c03082d030451902e40451500002a03002c1011806c80c1e45500250b82260802c0702c4400303195104174041940d00d02100300d1a03019103000000660418240000107088552403542c09080e5070111501644402e000a40c900840b4028900035a6400c0b40b008100c1c01d00004080140819043c401c02804801701900900210442603044070780700268010300d240c812640b04841c0324400502400f00e1607074102854031034034205624401045055440b07500030760300e0b0310021007840002c440040c288400c0c401030221100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 407229244 1250 407227994 407227999
    0x60417040b040e180316030212210a020c070306090309090920060d0e0102180906100c030306030b130c060207150e041b1101050a05130f06091b080c 65
    0x400742003011001d118441c900a00c000d0300881000258441d80079840588540040f20590740c49000b1114a4090042141c01c200c003d801010446c4803076115000548000085510079010581012440620080d5000c2e085a906070303002c01c1540329400d820010b2800031407282c41c0002d4582400c5c10300504110303450304440c034014144540710010854181128030030140a034682c3c000d40044100251040c444c40302c02d510386505014418110542c198040d00c500e50008518812104007901001a15507040315003070707880800141120442441035159010140c031a0900080c9a602ca49444030114022900c819aa41c9002c1c2203100700040c56401d040141000d000901d00c5c18284250f01c0c900c8512a540300b000c00200c48080030040d69590444c0c55a5140c09041048041c0c500800801e840010406042c056083c103020481c083ea2502c143c078800e442e0389100d844418040d58502c030302980452000d88120340c642c2c224601103100011000746010102416002e51072803d03502e5400d00140c668881d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 407230494 1250 407229244 407229247
    0xd090e13022d0d032a1203060806090f0d140c120301050f0a0303080c0a0210182303030a02030a09020a09020c010e0606030309010c03090807080109060b041e052205060417 75
    0xf80000d0b0404081c1094100400c03004420b0303500b00038981d0400c0810440034240d00f04104003194440e406a010f403007036036083c9040c0c3d80c860756021a07165464a10244142c003030b50003d0300d009031441c03140d001c02072131945a0403d0b0f8903016100003098680003035000c014075034a800000400c140d181a03040c190750780c582615450503861441e10090064000149408801100040d40b004854824000d600640310165001c01c02e01035031403d140782410b5185d1046511818101204070f0244a80600301100000603005510b1559505158000781d0400380100b4042c076199042100103135034905c000700c00381c052000016164010007001600b90341c4281040441d64005600b80502500c001c02101c1520701c00303003044102d6007020f01d01151041603942c03100139070b40540b600100340d44906406c950f1800307000e41014424851540b00b000b00716900b00951a044a007141c00310801d031140303500b100b9400440f5102d82d0f0504040e4000741144880e12400031201707030304520104000c12603841d104d61440401480c01a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 407231744 1250 407230494 407230519
    0x7030c150810090209040222030b091c030b0a0801050f1b0a090e060a081504020102161202040905010e1b0a09020708220b040803030901060501020d090e13022d 70
    0x40036920b456003d01e03c4241c0c0c0000b0500425140c03a011035103080007103415400a49154195950200780303502044881031a0b500c00304030000000074400080303d486400c1b1000c1816001c00540083c080c0440c481d401070b2003141d002614072400e109451140e4804580180c482c90302c03211443c1005000800b50722094810700010208680c807525040070303201c88811000c03e0303845040c006a1141c04d039611a045d03501c1800c00900500300c510600902032807017038007154a580e280d00c0e201007a6182c60f0082c0d11644024080000141c41c1c03e8003e402c060340500c00004010079941c620030305020810076034482109903e00e01c0c5402d41040807080004044009e011410b11019945406c4140b2035402c0f0080d080ca4210885641c2040001c1c000c8000d01060b007086544556030841d1079100d4004441c804880e520748100003d081d4008505032001940300c0d6609440b040c00c0610401c0b0460340078003d07001c4c1e0101d01072503a0050b11401d4440c2c410a1014070080406415544030588103034400303003164060300449842 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 407232994 1250 407231744 407231761
    0xc0f042709261e03060607080403140d020607082206060b04030c080c0603070507060e07032d05060a0e01020903060106030e060106022406010c021801090b012303071107030c1508 78
    0x1488210f40c072a685660300d40390340c07002950783d001d244009044801c000800004000342408030600320402407003501c20a442d54101070741c80301003c80300300300496443c1000410003588050400c0100d030042c0b5094001c5180c54542d4000c0780c08a0b0040e1501c0c0b075000505005002038900c0c0d4a0080407260f004103441501c40001c07944034000030703103550300f071041c040307502000c0084c15000024034101c10411101178542d28245004090b60b5504654802000c0b041e0262a01d54411200440243c221004007015150003c1c0700008281080c2a0f0106550a01c140c105070369043c80054001e0201f550046240d00c0c0340c1000d981001410b03840301c0f066502c000b400310a0f540080c185600307120810800309880d50b80e660016130708000d2281000f91b20034a416203000608010020b811f060701d104a204204200004e0012f42e5980b40b90a01d040743d601c1001844e050759580100103560100712032802286800d500204146040a039800c00c550040c5064411b00c140c8556401161090b0b00c0d910b014126030920703d12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 407234244 1250 407232994 407233027
    0x71a0114060f04150c0b0f060906030a030801050111190f020a08150403030c0306090c081009090305070b060d0209091005150612040203160b0c060c0f04270926 70
    0x184c0c60600c041e800e4601c076118001c030a000708981c0c01103514036191811007604481504116201807007543c50f1004107089040016500c030700c2c1c6525440303080310b0380d00305030040d0350801815554012030f204440f01402c0705150014603052180c4030b47d0003240b494081c1e00c10020380c54500d400030329083d8000086013040603000c04401e5005601810001800b8030607034070881c05440d8070341240c8213150402ea01ca0310765941c40304000c3d20851800d849855101d464403804426188080806000038034103014400c0441e40701c03803120350451801442803004242c50303804500d86640807038400d10141c00420100d0050481402941e500080100e03042200e0161ba00010307000340503070111107a0409500000030115281080004400309003840d076464000d5654107045401d40c040b0b45106c5c114044d41000c0303060309100ca8140d6032004103015082d401c2608205140003500c041023800b10030f0045401a00d468604c0a00c5402420350040ea240301a4043c0d840031700803050101d00448440010401601440d03001000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 407235494 1250 407234244 407234249
    0xa061202012f060f33010201021201081b0105030601090e131e03031a0a060c2a050103270215041d040212060702060c0a020c060f0405010206010b0310060309020105071a0114060f04 79
    0x45d40900d04482004078020701424080810114440c400410021400503d2a480c41d50a03841031910844100044070203000681c0c1c0340303000c0b4100c01c5c000d05c00500185d0189500c03410340b00a40e2400007450b03c41144010800d00305802000440c403041040c07542c14003403200c5080d80518020143c03039522000c26540c005c40d2088030104415014000200244020008104d11803950fa9004100c00c0e40424010011248103480c0400e1400b40700e4104a62820808101c01c844810700100c0000302c0d40901003a0350a05e510002114002c000102e510f040d90710000c2c044034440c0c810a840c0d0f19040c81481481d41011400c100740e0392140c000c00114030f81c00641c1070340c0000d404c00c1460b01c0310401e080c268034080c12440030750340c0a01c01180e0254403006250140080310006d03070072991a81d030780d90003254441c8000d85010040c0d8290708024000540aa084845400c0c070614140380f4003117294803100000c500344402c01301c080f45200010000350900709103903001d4020440e038131450301c0e540340031a070601c0c030451 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 407236744 1250 407235494 407235571
    0x10b0f12060111010e100c0206090613030513030303020310050105071104020c0a170d0b0a06170c040e04060c0801090c021b03070512060901050a061202012f060f 71
    0x1e401c5901c0703031200c10301030003140c4024001a00400700164680c0200000f10945034601310101284c01d100103403182c0105c102d18003802c07031a2180c096191401003411001d03420301c1020002c1001010002c03121800841c02541c00684074105101c00d5138056040350300c0b00381000341c00d0180402060501e4440e000120381110010303074407104a80f419061a0b0000c80203400460003100e1101c0002c1148000c08641060110400012443c1c0080000e40c0040d806010001150242403400c0c0c00240352015400120a031203107400c00da43d41d0444004c1443c2101c00b00d6070b041d111103d00f000250040d07030b0300340900b401d4442071000d0014110001d540710042400c0b600c01500020000384a91001d104e440c01901000c0d00c907008120758261005e03038483d000d95240c06198608400031382266440e03c207000941c1d200c8111403e13024215001107400820802081c620342c0d40b41c0c4801d02c40a0051400b5070508000440900382074640002882c038400402490380321260480a4840b81c0d5030401c403003020086044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 407237994 1250 407236744 407236777
    0x8011e092003100c0c0b0702010c020a06050c0d060303020a0303150501140d140c04231008071206090b03060604180f0f05070e0f060109030c06050d1b0314010b0f 71
    0x30100080c81d00d4400d050b82245203240c11a142c0c80c1310380c0500c01c1c08100f4007544030541d5170f80310070208138221008120140c0042c0c0007403c00c000045c0e916080789401c200c040e50128185881741000750b085079a2940300724050380c00501c5200400d609401401804015410010740c910b2034140084c00501600911000114000800f05c0a00c0b081d036000c080300345403020300b514662401e4030805072240d010f40503200c029a207c04140c0703810f0181c00451810400050300140407450f0140e41511000c6025100c00148112220030309042c400c14842e49000f00300c444c001003980300000e410b00d4280384000d8503490095003000c1d0300d00c0f20119109440f11001c0d5000c034003c5a01205800c103151051440900100750b401150400904500e8000901c0e0080c3c0034180d1034815070b00c810005480000d04c0b44001005103c0d1b40e442002490b01580281001d00200c80c80814164407070440700000c1d60100c0d01c04004255070303044090304511021445800f4104000119190101480390300d5103a004000409002041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 407239244 1250 407237994 407238053
    0x2030109080f070512040b180d021018210308040203121204030807020c03150c0906040b030906060303040609090f060e1314070e1803070503030108011e09 68
    0x5095101050490300300380318503200c0300707921828a5250b0207440c2c02d8403103125403440f034004411100d04560440365410718291901546100500503402503410040d030003500d074844400541c03280042c9014289503035464030f000210188000458142c1900a45e108085c210b4180702c01051061200c00740300d805041c0040b29036901d100203450980c1040d0040da01c01d001203010181d0007081c03041203000307901c240c0701c1852030382e1071500403a03131118541c95455159001100c002c40da80c0c6c1c1100090b403c120540d90052802c12004007003035407944250300000001a000080243c055014449540c02020860203146401d1601500403e00821070141c10301440d03585845400c00c0c0c0f01980250004d1510040d810030600d000810005109103031001600c0d002182c030000c0242800c0401c0400030b4079180c19204000d500d440b619141c030807411450b1401144405c02c03030ba0020903020006903001b0703c1c1000010800e00400400e050a6401c4800240300c154140400040000e050102400340b5980e20700c4005000764 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 407240494 1250 407239244 407239249
    0x304080c12180a0902030c1207120216060b0108040b0406021c060605090312030108070b030c16050604170f0901080a0902300c01051c0e0106060503010608070e03061302 74
    0x414112200380c2000300140c100c4004484482e0907a44900031180040031680d545454001d0344822118280c03c21070800c010788071180b22502042e0001c00a28150304201e400d074030102c00300d070310641150084442c81c1540100304111390194203110a42880c14a009080070340c2d507a04041d001900040100e40c001c585011842c00119901d08200e06040c0d051208070707074441c00a0001d610032018180031340070701da00800340034900070100c82c100d9038558020a0703403a16104000070982c001801d10000604200900100c010070b0400074440c050061002d003006003018500b242400e03c40d42c00920319481c041c0448500c000b12001038456a20b020b0a10309003603034880041200801c0b1445000798003000c03011003002e210462540b00501110300f003003c0d10449030f4010105039641d000d0060385e8002034082140581488604800d5540c624a9032404108450009040b030309641035a049003000138000f00042254543c03103c030751900540d0b2030810400707464541000c40c1d03c0300d000810041103080704190100c01c54 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 407241744 1250 407240494 407240503
    0x11160803130c0303050a1704021309030207030206040b190314060f060c01050405060601021b090103030507170f03042f19031506050111060702031218010c0804061a060304080c 77
    0x4030350004110b509140c40e880c000e48103400c8840038500185120003409421404540803c1c000c0350014100a00d0f07119520250015110200382201140201c0c5000401610740001620203024240c0b50702c0d4450038050741c3c65610008551100b400c260902035400784840314840c009412540c140c407202002003500d0040f41d16032140385070000c805c0d86800e0400c018004042148e500903c402d07401c0c0c40c00760b00c03122010360350010400a041e922001a50040002074001c900a016440c4111101c071410080c58000f88050f4000300c0c1044181c4c00008108400c1050807a100c4505995515640140070f0214903181011280762016034000c901907480c010300005800300d00d40065500007007091801510f42c0481024214500c03e01703001c1000030118070028030780416058444c07400c50780154148141c216110381d44020207030040410214017441301000d1003080c0212a14490542c60b04003c13410240f516071b04884142e4031044c400e02c400710484089a031010200d2307070040d4005054a44562400c09404d081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 407242994 1250 407241744 407241781
    0x2090d02060a1d0d020915030708240705030408071221061403030301080d08071803030e01090504020c03071713060807090b040609090c020709061811160803 69
    0x3007640880c001403203507844192891440800450855804040018400740e0b04018a000b503001c200140020007100b9441c044031501c220040842e02215500d0030341c0e0741401035520150200103400141030b001041442c2c2d00380d03000981c030b10f0928038600d85511104c5c03960040c100014118007a0038040040c0324840c207100d00a0741c011511050b880c801c149903010090820b44540070381962041c125101614010040c3d80c12680b00c0000385c01a0440c540d41181d0044c0028170b24030601104801d080d4081018041c2c543c0a0346c8039445030f009100050001400c058401d038082c0344501d004020f003000c035031000f06c1900c4003640c0c0149400c001e02030540d54008603000703070392807590303000c0d810040050100e5000c00064041d6409482c0d014003d0307140e800428151080340106004180507040400c84021a68800310950003580b054510044c2c5901801b000e0701d4095020681c2080340310107035614004c044c840e140c07981d030488032078078174200e48040b40c10300743c13110540083d00004000c400074041140030007042c4d02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 407244244 1250 407242994 407242999
    0x280c1d10030c0302060d0f0e0c031b03030a08070507080307111908160c0902030a0b151305131e05061008010f0504090519050604111c17120109022d0d02090d02 70
    0x5c400c8c61060703190f621314a00d541c3c641b2030721401c0010f42c40030350380345a540d0f0300c0c50014002d5803a029851606a4100c0f001421401c1001801c121401c08101c558001d11f0045802d540c036042c80c00c081a9400b49410403000c0c10800f1220ba001200340040c0001044411980c00180c000030007681038200411246003d074080913202d0f00000c1084800a034590010ba03208104644a02002c2e580040410301c50164148081c02d51100c01780034852440d00c4807801c4107501500b140415620314205402c560004030012041d481c5403500284007543c540000c410000c08007601d0500303e070350714052400d07484061a100d1036008990b00c03811682408028407900302000e207442d40b5281e40c0c505516100e5600c000c2110282d0f060701142d0b12228141c9040f90303030b00506491701500c42c600350318a80c64110340d800100400740c803400e2007048100c6c000300c88429054020302d00d03040010b8480800210380000002440e42050511031000034040d4a401c00f0b205440c205440396800507140c100c0d80303000c1210418a05006507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 407245494 1250 407244244 407244251
    0x3090703110a0801150806071d0103090821042f090402060c0a05160b0304110f060421060507021f1806090b100603020c280c1d10030c0302060d0f 64
    0x11203205d115241c83c012503004004580050785c45d000125144000300c038500e9100c03198000d08612562090300f02c42510303405007021502c0c2403401115852044c442140d842c040810460800003800b040d00a492100035121032500c02c3c0c40b0002040322507003184070003514860b291020100b000d40d15820181d5029520510071228007a409040c00da99484081c0c941d00f82418602901003003a8881506490040f90310240b0070700150605070411600c50b40c0c2040403030f00000d0602002484800c003018036900d90040c5802081042180c1c142407007074860050108065601410180c00160007140c1b00900e0102c10075400595403c58a504a00d540707048032000c1c000c00e0810751400140601c0d2406280107400c4907802d0300200303036a10010b0703040e80a8503c0c155400e4201c0c524110700f24075802c0401d07031511a403c10081445009558041400a203500402c481001da460041c0040127403034500c0d60001c1080051400301413960343c90601540c002c1c00028000e00c404120300103001555000140c001c03050305404e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 407246744 1250 407245494 407245511
    0x9090c210102040f090c020a0b0a0b190b04080c04090c0608041712060418020303040b07110a080307020a080115120602120115020c090417070206192303090703110a0801 74
    0x240c403130003810301440e80494038151400c550300d03000240261200358446091507855541c0c80c0c07003400400036045a0f1340c0140c01c01d18066a950340b144d40c004c02030900c00c14459244c80c00c014160b03242004000c200e90046250039158070118408211040840c0c64510b840c0c0e20715034552a01c0c41c46502403110b007a241907004a40b2150201c600501031348291029035040010541740030105081c445000c1001c0d4045c0c20400081c0555178208004001c00780c0125402d0b00c0080300d603008200504019801151150404100181189450a0035000070b01940d0f000b07002e22000d682040d06004010b206004042d0614400e070b0341000084d03016680c1c844138041c044a152760391115460410803440802200600a901c280d10301072070800c503014003032038006040d030415030003901d00c0c007080d03900c29032060341c0c13002c8240a2070282403404c14805c4400b4070395541d5410b41e10b9008542a50090303403a804010329400900c10010725a0740000da1074112034006c2d0040d8007501500c00840d41144a1b50412100c0e0b500f444280c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 407247994 1250 407246744 407246759
    0x31c02120c061905070f05090f030a1b0b03011d060f10020d081b160314280905010c020f010306050d0c15050406140c102909090c21010204 61
    0x8880c403443c0e250082c8400d201e0f01c0868441201c200726400000b090500600b604818071480107020a2030014003504020a07081e00002d14022422500f260a08142c10361440744503aa140040c005200c0125218150350400302082189150300d8011003600521400140c0103a85900590042e07080c040c1c030920700540c0b0244000d4450b80902d80c1c810104c1c0b000300c04559403051020f80390301100d0041d02228203114022b0604200d29032040c200f9810481160030440d030310002c140003004035a6911561040b8a00c0b507085142c00e4841f0031103d2f0082c4405920100013a03600201803150743c4d54101d880281d1400303c1c0c001a00281030b190429500002010200700801a44010b480e003500c1c0340d090402040210040700300c8152040d4018440024043d03c8082c070602c81c04005070171801060b505644011003800346440459002030b01c1403030340c500c1c419921154403200c04034258000e00141d4404203c1d142c0100115600c0d03004442280c001c1764070083c08940d8607808510b20087d8030800009664a941d14100d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 407249244 1250 407247994 407248003
    0xc080106050f1008100f060e040516091e080114070f050a08060d061418070e04030e0d061e0b12073209070923090c1c06060302040602010f0902031c02120c 68
    0x82c0d150190346000082401a401e10340315001002c243c0d981c0404950900944000180380c40343c156800030020080410033b41e2080c01407001d110080c03080480b83e842c022800400f20b4148503980801d05c5010011500b140b580b08602c103501c090203072a490010707515454404000d01c80e054201031201c90720390902006022541000012048a1045402c505d40316012030b48407442c1920001c020035800450b0600d1820006402c85a03d401944001980d504003011003400a2400005d080a40e0761451114468505240102c4d0340d91a4140242a60b0b4201300840340d12401101000240f4182c101584c41a101c40301c441d074800036400342c92141c46003071803030014042c4880b40c00b030346640c418001c0d140f41c1302c4041b02240c00c524882c000d00328a06900e640e030866100c1d50001d0080500d00074031410343c0d8a880b00c41c0c01104002c040e147e40c016511482c0910084c212041110810f01541c04c207103079400035a50015100070340c024040761880c54030b00b29100503403401c6e84194800004080215000c1601b600200c3c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 407250494 1250 407249244 407249267
    0x30a1a0411030a0605040e06061c0b0412081509070e0a05060d140115080a152103020615030309130204030b040f02150309100509190c080106050f1008100f06 69
    0xa0082c06120b072903031700304001d4498018140a41d41d101500082e201c0ca0b008001134544848003002d02d42c40001e6444980100b141100c098800440c9200340c001c2a9901c4200983d21200c11400040301c0b032440000541c030b090018010004101500840d0070f230307658030414424001c1c030000700010307031b601101c26890001c1e14000921a040003001400094805c1d420844400c41e46600d680d885115502d003000c900060040780b20500300d44c4500e03203001c42e00a018907081c1107044c04099400c0c205010324900249400c0000303298055006c00240d04262545001050b2100800112450218201001c642e103000f80074540c00030307000c803245006110500c0107000d0144c804600a4450803544000620b08070110b10099a009800c0da01200d812095410075901c000c0c0c0156a02e01a10011041018032504005c100e04043e00d0344200000300300300340c0800740324402c01004240d41100c84c804c051000100c031070b00d48401c2074007400080c0340000c03140c2e01406000c001030444810300d60003854441d5001000940c180707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 407251744 1250 407250494 407250511
    0x606191502010605130b01090b030a0213030b15010f0c0305031b07031e09030f0b06030114090c010917060115021231050604120602160302240103030203030a1a041103 73
    0x1041c0d5440c61705c514020104a05c2c0c1c181c4645419510f006004002c5510046c1070f20310440d0300b030042481e80140d511484000b980152024504d50403c40e0605140c11240d98410f41031011507104c411039243c21181000781ea940505040340c903540c6415841d2040215000a4901d010000460710100354100404002508030702d4020340b14424240000d0740c50b024240006402c80d141d1011800004c4c40b40c00342698030240140c0007240745142401120141c200686240507182c020b800794040e1942c0c403030000b000a280c0e031418010800c800a5040c6d455080c10300407a082d8102d24809444075174000c01c03003a0f01c0028415442aa0394231130011450700b00d541220b10300a880e0301c0348a03000e07041450000324419150003c101c0c2e4602803a0056101c1030055a01c000c450740c98080c055014905411891040c240b070180d00507011510240c0c074030b00e88651080184901d5880c0705001840840c0d400400d030790340103a030700d800091700f04801110481150700d1304109645c000d040102aa4514109801460080e03000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 407252994 1250 407251744 407251759
    0x150f170735222310140402060d09061d0c010203031302042c010609060803070317130812040c050d0b01090903051c0b03010b01020109030806090606160803010303140703020606191502010605 83
    0x845581400707643d12620303008201e0300700c1c5d004180940782880043c51030b807000714400100041a55240d00c2a00c0d2214602c2000782090f080400b555101444400024442480590b141d40f030440800c102c00c3c4070544000c2e0080b50b8410303000b003140840180442d48019626800c2d003096409140c014040d101c40e0240312000d90410301d0014030004000107903414140d064542e0750b9030300c20a08000544480081c01600d0703180c0402003000100d2003200c01011900e81c0503015031054540703800c0050090303e040d80001d018401030742c802e42c007151070b0448040c10342c0c1741d042003c00e0180450a0480340381c0942c08801008040d00401a020b030b50031503104400508081d07000744074074501c0c01c005a003220000000540410711410010f1a9460403800840c0d010300024051410000c0c40c1c03601c0104080001c2c421251000c0c004010f105164004404880600380d800500e45800100c0d030b4020348905c400b40035180512521124000042c2c91003240030b01a04c2d212520070a4a0101d0750004c0c0a000144615030040c000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 407254244 1250 407252994 407253013
    0x5130b0a12081305090106021c09050d05030c06100605030406020a1709060f0f07020a03180f060203070308100312030b03010b0405130c090204150f1707352223 70
    0x4004c645c85040b600d0fa0b401401c4240c8a00300c00312418200300d0100020048018400f10300d0350345440d043c0812501503001180c440d16000c41d01464000302a104460980e48140100541940103003120741c0541e1044001d46c560303110141c06d41d403549009540101218418041200502001030568030a4a108407052010707256202004c0200400380d642d00010f0f04250502408030b40186a0002d0581802e500c1c0314045070354221010040032150440b600503080019a42c1c2810351003001daa4114102d007d4080c10315107980d850100c0240140c40340f100381921614031030740c2ca68080d4001110f001c000383c0103103c3c5103400040ca055250460394100e4598508800c081907801e068826141911418010b80c24111400c01c4141d50029030b00070b1030002c2049216244041c1401c030308403140250f507030351900d81c1420010540096101d2030f107a40000c00528069210401c401075514440d00b0250700c540410710030710011a080941a01030723030003400c0c0c0c02000030100945110b00c04a608103002910070b0313030780341d91 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 407255494 1250 407254244 407254249
    0x3061410030510022104060903090b090d020405060d0c0b0c0d020105061e0a080a030201060509010902070f03050f0c030301080c03010c09080615120f0c0a0603020405130b0a12081305 80
    0x80300d800050702c550b1203000083c0000c140c50740245008846400302c0e00c0e0207011801d00380303452402150b0032149261104403080c1010703000040c8501034035034506290b007444600008501c1c9210398140207441248c81e1000700300c594803000151038059802500d0b11030791940f1002424600e503c0468803003010311a0155030302416106200341c90090760000c02c41c6400c1040c54001c60103581d040c4554541c000640c200008044e41c04002661020f4440c1c1c00100700142b4000811806c00b00c1607014005550041242000044400c01c0300d074011640f50900917115006020300e0a107502400c202e41c042407000000103d02203900160f501c041080443c000d010450342c0d21802c50744040588a0311266501000c003080035410140d0700030710403040140040c1c00320000584601d00e4550150010a21030308019030005130341c28800614805482c3d02d04003580b43c1841d01b00420504a00d0310114416076a035949042c0303c540e5110540d000503c1c5c6501e5400001e0068100001d26a1280304944291a5400000907a60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 407256744 1250 407255494 407255521
    0xe0d030c0504030b0901020c0303070c02041109090f07021603060902040c090302060a0302030903190f020d0221090409140d08011a04030f02030c1e030f070b191107030614 75
    0x4100750307a0715051034a195241103c903080940480480d54090009142561040015501c20300d03aa0340c0b5180c0c485150b00602c8100c80b80c0007141414218104000c0b415500d400075225000300b00310540c1c00b07083c0e54110307040342045a51001d0b1440c0d241d5030b00c400810b004062700180b030b220b03000716000c008484e4419070941e080c0d4018800207402030414082400c2c0c0318001e07401782d0f620042c0300c1e00380c03440c101840224016010014402e5408142001041200d2a40c10824800f60007500e000919100c090348c080342c00d0010f6a0170303411014580020b545401358403503030031a034ac0c0c081e0300210a2409070003149640b0b4513000000800d000040030302c000000c1600074843e40e1400500c40c40c44181c50282140c50303c88110505000c1070b43c040c0f14946442809031924110090403030005003007040c0e840b81030010541403201c080101051640640d000340700b0306d0130103001c45412014240c0040e00580c0111006c1c1d034240341e000207003040c1d401189070010a022079034110510106107206860944e0340d0321403030040034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 407257994 1250 407256744 407256761
    0x1805060307020a0210031119030e010c0909090c03050d020309120c0609090621011e1a1011010e010507030e0102180121020705010c0206090f06070c081c0e0d03 70
    0x60f0b03c61406280541001e0400c55025942482c0c00301c0c0007030b8a0b1640c810180e02c00c64624074980b0112640c90710b500d50600c1080e624406040c0203102492081d1401003513041207001d0506800e54503104d90040140c80800c00c4000c42d8050265000c0c2c840322031001e1745941294500034040d1102a22145414a000c0b03001070641784000c0c800d0307041c058140103000c80840010416600309540c241d40385445920f1001da4204404404004a5580300c1a12828001807400f540e100d8214184682480e08554140c04d8901ca800d00391400c6d0740e90403202104490030307012444040055480c4c0715120a01e00810b402141c0700c0e604030b84060219800000059080307100d801d40e04042030940c140c0c03002c20303507118560000c245a00c031040e0b0094021b03040564022a0b221050071102a03540741e018003030036034040c004030380e20002c03c001411448981d1903041ea01e601c2c00030004010803a8400380e001c01c200d0301d0402d69045811480701200c003070041078413030b50040c50008402041403107242401d01809100707005e0b0011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 407259244 1250 407257994 407257997
    0x9050105070c08040306050601200f0d051303080304170d0603230c040b0324060a05030609100203060a17030306150a0e040b0303070b0c22050d0f0f050d1805060307 72
    0x35042c85d640701d101c010440a80b4260402c00e13481701d9084042c0c04241685000c000e02000f030208105a080d21a20300b0710111849414071005200700340f0884800107022044075080744009503039a6070b0740341a100400c014441030700c00e0000498801841e00c599407003542603d104401c1c0c82d0020410718100c0e0300d5001901020311003940174072081030039424560402e5102c02e401404950108020208401925281020030200074105400b0080c5a00d00501800c1c01000160041c0c030b99400c1c5641d206894916260007400402d40000c04039060346c9410420740000d00340c0d0282000c2d0492100b00103600d130b600689a440c0300d9404085c40d031100002c0503044920400d143c1e210085103207004028400a403100c00962681400180b2a07140819100103d8600c2418107124840e59103454007481c81c00b03800c0c61303103000c03540d171500400521141c3c1307905c80c140d804580c0003402c10500b55000c1c07814200f01c107141007004200380600d04a8030700c82e64000b00048860429001d4505659455101340206404210340a40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 407260494 1250 407259244 407259247
    0x6090904030c030c0b0901021e0405090106200d0c020f0f0f13021e03041401020a02030a0c210e0a230121060f091116080d020c0a050109050105070c08 66
    0x9002a0040c0840901e0070b2280c20001310008281d00d600c0c00c07096084440090756500080ca4101c0c1c24074121241a0701c0303010f07400403804c20b410a00071401b1203005004420500001025002e0a081c0800703c0f00345003a1031100b254810072103210010110500c00c1412809103003201c800b411585032001105041d544054114043c0101c10001c000005604080002c0794603800c101140704074444d00010119107915030701569907410145058074a0440380c82c01c03000340c0d034414840d8080d4658040201c038200702152500710540d0710a414183c42000340034600c1001c008550340881c00d03158105080d04046c41c01169400b8015a45040070091036804003c103480a20340c20f0540000756020f013255101c803049610300000017038020080001164520b400410010000000c1003140300306034001d4811070b414a92400b402d03c004403a21070031480504400900040e00030544003031700540c0d07605484c825070300c40080303d500c05100e007842d43c0204040103084c0c80380e500300310004206038000d94107611100d03800000d09 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 407261744 1250 407260494 407260501
    0x315010516020315091608120706060e0f180a02060f030405030c0d0509090a14060d150f09290a020d0902060d020a080612070306330e0105060909 64
    0x115825404907924219440c030001428016032403c01201442d5a02c0340010202410806140c070325281d104441221074841064080c0900000800c855406c185840c0b500c986541062030008040d191f160060980004400c00f041018015420810b00451092058099004211103000c1d26442e0700c0c80302a400c04000c108114082282500030f660083c080e8094a040c40342d0f45550505012a640516000a40100c0d0b074a03141d1600e0040c03550408415101080080c491014861a00000800442c4500180440003050100c04280e0540a160104d0204aa82a91a8120000d00f004035080d00d075161000110700e0759400511100b844103140341c1059400d030707549821180c0039520007050b503e000f0742c803551031000689501b0060509144000c8000d603c07061a8100100f284500a02e418400d03030081d0894151564041000703400e0340d40004010548648070480c81e090281e04400a56010990381a80d02d451080c100444081ea2a070130020001c40e66030724100030721802103032400b940c00340c00d0301c2c0030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 407262994 1250 407261744 407261747
    0x30c0d0209040f020402071a071b08070c150f1202070215070c0b0a0f020f151f260d0f080c0c150c04140a0e07050a050f04062102031501 60
    0x610b540984103400341c20310f07614aa400b24041e81c000c54412610140142010040c15901d4141d195000480d45040704400f440301151040c119102c030001340240c0c2e80040d400b001e00c6542007120307001c0e020028440451204c1020018800c01c0700d9000c49000404a40a1004c000014022120000d4004080c04500c1080034446a0940c1c010002140e4081180d8000940c42c00c190015000f0000c09858030711104108449c0170f8141111280c1c0b05280d508441603800c0c100641482c3e0759088020011402c03004010505000a8a0314a40101002010369500e1aa00c980703c004003104040d048800c2d1824802c1c5441e05451346000c175680c00000c03c0800c80011241690f00010f484ca03404104c1c00c80307000389211440004411000d0392821003019000906211a0799088401038844109a8140425510b496814244100058019001c0100009802c201e1074031610540b00506d69116805550f20781e00c480107800e018024406009500b4401c01c9612205400e20940b0301c21100202100c0440300700000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 407264244 1250 407262994 407263009
    0x306040c050c0d0203040e06031c0807120e0a0c1a2215081b0a020a060e07030b1617041104201b0f0f07030b040f080c0303060f030c0d02 60
    0x31410030050188240c50312200200808507426010790041e603a124100fa081a4406070002c0400e40680d000400744101d5120288040600120a00d0022000d40b02e4402c222440c0d082400310b050858180307819801102c0f00490058040d512907006e90400990710740c0070902c40040855a80c0750114180300c410072840e0303035a003103001c2d8404000f040c10f081c40d107820602c2c10554603441c0c1c4200081c2c03c5420020000d0555203145655009190b44a0500e070140100035600c4003e5680140040e4031998031082c03100d410801c49018551182d42a85186400211255614450068180040c14071140490090240080140501e401c003980340c200b0301d0b031002440f0181000c2c60060f210920208a8070383c103400101d001d040e46140d84a55070000c0103585034418038003420b03a0300300101500006284181c05c0e400094007411030341d024044a8075540d6505084064400324107014142c6000090b00701c0340d00790044011417140c2002c07200302c6140d50058007455501c5018041c01a0080094003e4034013500e8086e2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 407265494 1250 407264244 407264261
    0x50a0c08011403030f030f0702100605150d090f0302100507030c0c060c0905031207140601051804060f020f090405070c150f111602150906090103020c01090210021e0111030604 77
    0x9041303d180c0500900448180e034000c45030407503041011003d0000301e503814082c01d500001c4042040c44010704110000300c00c500c410f0320001900c1c000050101c1101059081390005580080d107850842c85175080194840a14038400703039841e45058000348030a402031003000100c42c02503440f590311825a964100c0200f1050340020144410244001603941e03082102c151640c0c1c12661003a21a46c2d6131510b110001b24010f800d200a401c50700040c051502d031141d6131303042c0b07440b02d0101e02080d49442c203044009040d04601034a41e00d000040300103588011100801d50400c05035070402a958414200311425900a1030003000300c100f980a80c45400c405400820584803030010001e10300300c00a88030a070315402411181048404d24409806600d01549144032544801180701c0c500b50140001030118441c82080754141640071540d084002000d60150500701c3e070103441840303250084080690340310304445045841407109000c034003440806000c0c04400040c02540182141c41d05000c01001d0720940c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 407266744 1250 407265494 407265499
    0x5090a1b02030a0311030f040f0804080d260f0601051b150a0e031603051602060c070503100b030616170a060f12030c0b100b0c030d050a0c080114 64
    0x10600800038002100090300080801d400035030761020300a60140545618070300069040c8014410002c4d20480d00e28940c0d88298049003041c40120185000344403401030f42c000d60218031801005c0c0e40003e03080098100b0800a02510364050010300b945d00000c00d0007107800c5032480090a0200b401c0b0350240b400b070481d0f89000003409400680010040d0302c1c0c4510441d245c078003003a10301c090100c03100c84c034441d80b41d000a843c805140340641d05c0e000080803070b00317840000341000000140b41400100040c01600c407690700034005171392900c032201402e644007035a0145d640710b03015440201c3c2c1400114415001c0d0040090040c148680c2d0700d00d5035040401e0188152418003048100100b5003000b20408140301e007900c4180094500d04246d00c0c0d4030502d442e03400c03418100981c40c6107440481d0300010301c583c9550344041c4080c4c403580c9104c00c079002c1103d41c0c2d03c40b40c00c07005c000c100303500600f0300800174000501d00750030208907560382c94a001e0705448081c10040080303613140e00103120114048000b070b42c060b20702 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 407267994 1250 407266744 407266751
    0x1e05061606110d021209060709230423010509131104060806040c0311060901050d0b0406180903030b0f150f16030c1115040605091c05030901081e0105090a 68
    0x40b00e40240441d031014620104140c1d000560800c403801d488072094000e030b402c000a020300e2901400142400c034540c0103c0841c0303024419020313010400d5603880100068043c20074031544800d00c0c100c8114500c540c1030301040410f0b1400228042c2007040c0070070310840620600c0482c82c0030b21384034011360309000320035103070425101d41c000b00c0e050104001c00d0340650301c541c2c030314040e0740d04d1401c01410230855480000e21400c01080010100d82e404000e03203013030072004100000e48942c03440c0007500800c090f41c0300d89603402c0003946280070540d4990054400354000e80307041c01140200001c05c41817500e094152507212000112080301a01290b0103003002d4998250820b14081043c45600440e4130100d10480025051a804404100001d181413440303600036144d02d204c10214a00c001d03103078000c0b80030307200800402107250309041d80c800c80c0950703d007e1141d4402d24408e64a00700140c495104c00109400304055002160480e441400d04412141c02412002d540c0d07400c0c42d04200010b14060210811b090301d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 407269244 1250 407267994 407268011
    0x15050118150e030601060306051003022107050a021b0a030f0c0e010b070201030c02190b06010509090c0306010e06070503040e040809030327012a021503090105011e05061606 76
    0x868101d00451000d844940c0c2c400c45201c01c0500d8640160003880c20076090900400032902c03003040c14040821a420056228000300010742c901600901040010b00004014000c1d00e1b5000030080504441550aa820040703c50040c0350080340e0728282d06821040b403202c00c0011481d0400c10f104100e104401d0845c105940e40912800044c0a03000409404000200c0c80300310b40e01886454811010340c00036040b0f071200c450507000c3e1a41c0f060406030017940640b0000f17400741c1c4544201c8103031000c01001c401c42410880c80d8900c04c0c2d0001c50b01c042c081540b40900c424146840d0007980c000c1079102008628050504c0d4007404907850242045903480010710803065156410301c043d105110542c590305078550548500181010a0074480038141b14081c42c02030a03c00700302201d9859042c108a016000a4962002c0744200f44041500040540c0100911920034419004503040f280b91880c2450101c04022403207412800d54443d041d4807040800c42008200210b400981c20f09006a13070000d0740700e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 407270494 1250 407269244 407269259
    0x15070509030d030c02160303120e010b0d0b0a15030c060e0d15020d050109050c04060c051e06070e03011e0f110309010b120312190f090f02030f0115050118 68
    0x481c65010080400d4480b1300c5a121141e04100420360284c0300c14110706460300d1501d0160640d01c40c8103d200815854109454101809401400189801502400726000d0300d0a10120111098540b02c182e207003000e80c03505d42140c2045d0240d06030703a00102200c030320914003c03095441c04c802605075a048800c40700c041006c1100c0044184030710742900700140c0d40e00c444510020485805070040c036801480c103814040c440000f01e00740d9040e20502d00304003508006600344249000c0c414101064030038000c14564605000104000d0b01075640c5468004603894080b042509907101050044406a5621200b90a08085801c400c030158048a000200a040e0000c4540507600485943d43e2680d190036502010b410143c1100c00749644240c0514104083c650514510300005003000907940c944801b48102d61010342c0c001d2001c14182c583c1000501503510303280c42c02c0311407000d05a110f0702414480940007081030040d01840c403042d49844100030f00f0031005441e0b8405c1a11414401c1e844008003180381e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 407271744 1250 407270494 407270503
    0x11a030403020f150a0e06040309140a09020c0a120509010503040f02122a01110c04050613020403030306090c050c0604030503101d04060606140904020f25030e010e031507050903 78
    0x12407450b005130f00a898840040401c0d9110000000d2141e0b11a0040002280d4003032142070680304444603010382140302c81e000501d00d03061030700700300c2d0018800075000d200003c0002d80f02c1850f910030308a609488154040603242401825040c07404a42d04100040c00200591b4102d45010304c0100022440b01c5a081c000e8a09a500c0d20301c3c090b0b80003100700800c8c5040d018100d0002505091070710001e03005a2288041d15503070510b104600940e210f1001c20619980e9440c118080085031104545890362414014040c0400d84905120145400031034100540304004075141c00d019480104400e88442e41c0480e0175500091411070070030690b28000c81c0644001102000c0c0c50004214074030305041c0b0b41466801c42d40a44e02c00d03c144800c4510700080e0195a4060306e40b4084120b40058490500c0c8c04462207500c00c00c40c038148030741030101680c40030003901a03034121707600c1c025561404410054401521202c00800e6542e0303140e03101c01051623502c851003040942c011000e10b0458141807414022030f141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 407272994 1250 407271744 407271763
    0x2060d110d060e060319080315060f0d060b030c03040201120e0708070f1d0c03090c09010e070305090105130602030402040204050918011415120c1005090f0306011a030403020f 77
    0x81ca41c035900208a21030301140440d0700180c0032009001e460a44100d4844421199070f4006d24042c0b000c400107044082c03100943c25075135006080f25941e00c400c0f0070a8485540541981707140c061401c1d4010500240c1e08042c2c0f4854001c0054451864495130015a810143c3c0480658250749425039071200300703010300860000b0300e0300500800c2d10310f0070040500c00603511600311050350340103401e800d401c6a106040c081d4020008602840c2d413a190b90a4050034628002242a0406407403000001c4080c2c6008190384031b008a59420030842c1c46072240503007600c00075a40317041500c0010031000c01017080c613030065401520013800149010b03501c90100c5e0300405d0031120940b80741051542c6d605e145100f030182001440b000c89950b2650300d4101114819003440c180810b00031100030382e03072085c9181308000c0c0c40340e0100020a10303000d070814007000034599441a43e02c00c0c002c00350700060310094140012a49d06845091034102c080f0341c404d0144902a410040050f4210300c0b0303d81d0304006010050103084038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 407274244 1250 407272994 407273017
    0x204021615060f080606310c0e030c030c030c01050a110703050102040608150904080a031e021308030c060414100504082515360201081f0302060d11 65
    0x2501d61600c0d00f030f690200b10542c02039490b604170004122195954030f000c00016034100f00202c030f81d42c100c403410070360b44038500d400300d800980341404140400380c01204c414030001c011011100703600c8001c411f06840c0c1c00a2885150182d204902d01d41c8a58010000f030002858146401003060710000302c45480d2800d56842901d0342e941c001001d000495000d41401c2c2d0040040400350642c50049020407600d40c0020700c0a0103080f0041000c11106100c0e402040f11b24020160302d540c45000c90713040c0c0000f507204c60091155107924890000b8400804000d840560541030017909656440d500c0b10102c01c00c0f800002081c82c00b0384540c005a4113003a1007114000c901030394081d80c0729503000569441c500d000b5240c5040880d00c40710700e000040c1c20720704840310403c1403072004a52200310209036828804c0729410000030460045903041c5c0c0b4040052004100c1d8000d999403c49500c0703c192811141d180800d407a03442e805104e60503c0541040300003000d00307041410703001070b0070052404c015403680c020310f80051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 407275494 1250 407274244 407274251
    0x170106170c0a060302160524060904051b1503040b0f1008030405120304030c0b0a0306091103040f230a0b07031407030b03101107110108270c0d0c090c0302070309030204021615 77
    0x10f03503441c07544150b011002b540c0080c02e07070526880319640d90212192a606004080e01c84605544544000c2152400d41c8045c190302d9042074a440804c0120448020011b210054000340030500307080d40b45001c40d80300401030f40ca0981050144517000c010040e1750004c2c0d110401c0000000742c0c0440b03141c8001e00c0c461107040d8a5501045008050b00d0b40350b48981242420b00e002c2c8061080c0803000c890300558420000d4011041c5890800301d2602c01405400344001010150344400d8004686040c100e445802240f0780c035031703448100360202c0c1c100e0310014400b003805400250300d103400307644190280e140040403106000d00780f84104096452914808512280206414003048107152101203242000d003050034031494441500007244201c1c000e80c0415008208200284a00074081c0501220001e448103050615500b00000180c01078810144100e103840c106809548c481c0c8295040e4580c0750303807901c4501c1c4c5580c0801010b500410300202c50130804000d00000200d8000000402b20740d01b40d80030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 407276744 1250 407275494 407275543
    0x6030304031b091a0a050f0d050106060f0e0307030b01060503040c21050c01080c0306010309110604090b090f060904080304060b130c2c09040c170106170c0a0603021605 74
    0x1031003510109099045005411320200c0040d65480c08054241c4000f6143c04d910380a00100140700b201030514040c0c400d5181c00000700d007107940700269212000b10350b00d0380004901410f05166642080d48805080c040980340148000781c42030004541041c055040311021030303295401d403c040719411403021419181840c030142088424404003016500908000f05240303810100c0c0f011600c0018101810160703075980302c40412120310301580024501506c0d468440d0303150b510440040c00d850400510038501c104c009042003040d00001807013404007030001c00300c0707860b20341e2141e55940018108907030705034a03526622a42d4648404000d1911008100448c1040e40100050321001c02400700c400030413100d40740c4020144458510311513202056401005660701c504003c800f0201c50340180c09950852a0482c20b62001500090183c6181014800702c07211a254100e07594003441e0426034220340c4400080004030b001c0d03070245c01070b5034082583c0c642800781e0340d803110300b45040445403049070701040108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 407277994 1250 407276744 407276759
    0xd050f0601030b06040903080613060806011d0112050304030b3102011404060903170c03160203120a0e0d0507080d0c06110f0d27050c030c09070507060506030304031b 73
    0x145078011304184e80400c603a00507510010701e848070050481c0d01418001c4001e0a00504540c0301c05c000704800c50580e01203584a100b000e103642c441244001503090441c001240d545240f0404009a5501000451500307245945030b00050030300501e5100d100103042c0600c54420700201051565155010218805030340e00e01c00035280d01050640104514000d000038000350344c22042c05070a998101d05d00d0065800301251b04603035440742d08003d0f9968040440c1c00c0d0b181e20400720401c8402031080b000c0d0382c1c07502c20f1030b19540b03024000d10700b0480c0014800103900c0500d04056180540d0180507100b51004552034401d02e03854000750802d01c9000940388a8500c061101c0b910410801e41e07003c4e01050702e4211074900d0030b60580540c1810304042540c868201c201440411006441030082840b00000744003507042150300c503a0320688a03030083c000c4e0100c8040394640307524200d2065400d929407030f09000b01511a400180002000c941d0140700400021000c55002401c0b4241240d071000522203050602a8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 407279244 1250 407277994 407278013
    0xd090303020d110c2d12030403030c080609041104060305010e030d0b0405010806011703040e07050d050906190f09021905100e0d0303050a09061d010606050c07060e0d050f060103 78
    0x650380b80c8602806203001355940403c2800d140c0120f170400302590201707881013402d060360000180c003940c4203030341c00c1c1c8070780000f00005503105030b0282c0c03400c00110b615001d055130395070030440c0d000d40c2c400b07118000100061005080104a084094000142951291350309400c440c80141c240141d6800420401404001c1b4000c104c200702c010741d014409545400c008541e5000c0c10301404810301298200703400d40c0c090810070b0f20010000c203100c1000d81c0c14041c1f4042c089501c00c49441010904290004807010b03000640203001c2d004d007800c10901c15544002c03d200410000b07101c8501e1580700c0e4001d4000d40e071544c04034000700400781c1e40403050034640010030100504148d203103400c1c00302da2500c101443ea544000d40c0082505400d000c242c035603400f19150020b2004400080c22145009800d84010302854560740c40c40006500811030591a40000d0f6458000c0c0c03c00380c022a03100d21024844203100e18030408843c403001c0c02c000b1b100101c9540d074500b0074103140c04001050b486000108140700e09020b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 407280494 1250 407279244 407279261
    0x1f050615070521210103020909011e020a020a0501060e1807150c0c0b070f05061812071a040501050f13030e0111073201050a1e050d090303020d 63
    0x2111145454419a603442d00d40b03e01c0796180359400483d088440c10350581c0d600b16000f038288401104441c40c03000e02c4900401000f8003050f400b864100740002e20a25052090205050f000140c00360040c0c00d00c0c0e99000694803903e014011401505040d000217a0240a0f80c4d0142100368000c09191802c2c0b10f03003c07420300710400c000e54243e00a007804c11035506d181f042c031810601c440ca000c00c1400402d0034001c1d80304940fa40000c101d0040091b40d841400080c001801450348030304e042d1909529081c160010903510021400707250b800211091021004040081003950b2090400039400c5030031004c201414842100e0550305651200c040203a40b41d00d075205241d05c113040340520300c1d40b44c85685000b007141c8103000c5000e040c045910101c0450300820003450005024070700c1b00744011340541a00040d402c0100e200c00701c1900491400004c150b0055055840c0740c1002d55840764000055024607030a01851103c1e03e0038840c2c00c000e0414052060302902103a07502a0b1005a5244034040e0304408941c2d021 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 407281744 1250 407280494 407280529
    0x903010b030d053405011e1b05030901140408070606050a0b040519090e010b0307080316030f030f020a05090112060308030c09030c04090606030b0f040b010608091f0506 74
    0x24800702c0116004400c0d54891070900c03c07a0320090031500701c2c3c208000ca400821100464078800c0c2e0004021054000248210070071004841400c961040b0b901a04d0711b0008048840400c416a14582441140915070054403800085504104202e811450070002d540940b81d520b000582241440183c0c050b00004080669060901602e00081d2800030301690291504c9410003400c10401c400640c80c1587c090301e0850380030400001500c031024024101d5550b058000d005200001424200101c04e0b9420f090f51025a4035503030403107a40c11240b40403400f00c050207241d910040d9400981e000c0c4080d110303a81c0252901070f0782c0d080d030354005030000c0c50020030013200780c0c2800c80234000078071080103480d00300107200742c8251140303141000603040c20101c0881300d070060700d03203180750701844030b5a0042012079016009151064640540f045618042160068054064000100700300c1e48100001644400000c1c10b40b03012007421001e02d600e4108908449041ea911003017800a54035024807036681407203c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 407282994 1250 407281744 407281753
    0x30f0e161703161a0c090a050a032d0803100317070312020307020712060c0f0c03020a0210270807140901150e030a0b010806390408120903010b03 64
    0x41c104141e40c2e440b403003004400d0442c45540d607400f0012400f075905030403441c881115402d85803c42c050b100c0f5402454a413441402190f44c00102814142045010791390802c03158030a180c03101215050762940a9030010305001c00b040d188011600d01c6002c0c1d406624040c006411541c030710b081001468400501c4102800c1d01080702200194000548480f602e06500000d80c4039034071010260304080541c0e10195800782100c850718104001c80c0c1c4000c5082d810390315102c90100b50400d088444007000351005016a00210014000d858100b1000000064500d02511210f56030200903100c2d410f12120b00e90000d03800d580500c02ca00f402d10441c00581943c10620002400c4800002c50035001807041040c074140b41030148001502c01d0b400040c0c03010700902120220580d610300a10f03000024441c003c01405101e0103d02c500050034035a004032041300500070f00e055040740703055020105400211022800821001641400070700442d040b04580503100c80d181c010fa04203041c2504d50014595119410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 407284244 1250 407282994 407283029
    0x30a0206010f2909040c050702100201110706020d020906160c06180308031009060305070e07090b0a20070f0521190507090212071106010f05010f030f0e16 68
    0x3500c0c810162205072600c0c80340300c00410b43c1007400c542e1042c2a411504503040a04541c1c1c000e40150041550f544291100300c03400d84514012422940300c2a21801441002c10a08002c540d407900607203076114080000611300200207000900c154032400d0f41a4942012080441c18440e400590764000d101c01d040007800242c0c002e13a0f0082c0e100141c04000d25080000c00400c4110030b062040e80081e00741500e0820116860742052a56401180704551901d4500c000043c0311520a010780412140a030741e07114140040100e09440c0101801c111214249540000300b045400c03c0200c0802003042000c8076034518200814804801090210340f201c2a280540d02110b0b4003000810445056081c140c0f000f100d649458824201034295100f40e003000e0011502c0c0c0c14a080e405909400b5441d20385550304403107861403002d07071039400900c18184032070710460b0708011a5008155210b480d070701c01d01d0002a44404514008126204041240c16036070094400c0c24a0031291180c1c41c018000100c1c05a00418 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 407285494 1250 407284244 407284259
    0x20706300603021008060603060d03030e0f0307051b0a0b210103060c02151512030c03030c180f010905060306040e0118051204080619020712020610090b0f09090304050d05030a0206010f 81
    0x40301410f002d0040f224584d0341000d24cc400e03401826056150410740300f010b000c0d22422a030781c0e008600240c0311401040070041c6024400300c9040508040a030511100c1842d01c5119040c80d0081140079050100d000d85601b005e1500580e03885c040c5114070000650509441c01c0245030001d150346000a00c0102e40502c80f4031500f9603020481d5050845d80340300100320303004005056004490923950584008014402d40d601c0b040c024040d910480700c0d0703202000c1e919200304071740d2052a00002d40806d210180910171410500002d6a00170030182c00440c8980540c101603013100c101c42e1803040c3e2801a100740c2000c10070107200300c94010608000c50f07030a0a05000c03000761640805002140c04201401114015010b190183c5204031b03089400010b1408000c10042c0d19404200d0340c0b0b83d030344078040b4000f20701c039043e51060b814443d41c042e210200420b401002e000408002402e00c410602c000d100000d583c2d40e03500106281c0d581f080c006152200d1802202034a010010b0700043c1c3d04000c001170511901 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 407286744 1250 407285494 407285497
    0x3030c182d15110114060105120c1309020301051305010f0909050c100807020d090602030a0309050c04050c070c0801050103170904060515280207063006030210080606 73
    0x1045190592920402040302514041c0002c1d0301215458603028400102c154028003201e00200c440c0000f4000c0e18441100d512620740210784441c082201404000349022804903426400148131203028a4500054400145031007103900914031150004010700050401d20003600d140c40003000f085c406941000c80303c5018448502541142c8c50b2b40c0c1e0180024818100704a000c960300280244148607000d00c40240040c1c0c04680c494058429a8a49201c141c4a03801c1e12040318919400741d8103061440e11308502604071444240c0d01c51180300030910195a032442542d02805c11220000d90740d6540385455020512a54040c0249900d850010000704d0b65007055240e8240c1921025680d0b82e0b0034000050040400b40c04c01904107202c1056034040040c154010000c0704021032803417810380c40030600000100f40c034014403030040e041040c0c2001101c0c000c0b100c01d2044d00c01c0203220f101d000c40054151018104a040e22385400d0f0300d41200b00190304104820f14210001c0b40b411154506c0d0210120320746 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 407287994 1250 407286744 407286779
    0x9090b0f091021062316050715051605070309031104090b040c180923070305030307021b01020a030215090703050604152a03020304060e0a03030c18 65
    0x600071800000b980381010500d00ca000e40364040c404034050380680b076880038051024070f00302c40b500d10782403c4590000780381d61280380c11011079251070910b955012965503c4210000c02d5030911a0a001c03950001780c0394503000d4440d030303080c3e200012146030040103c0707112005801c0c03038000c0c054100442400319034004a44c205880d04480041002681d1001140003000340300000f411074600740e0180300800000301801c20440301485204040c0d14041d280351001c80700c500030001e01e140c0076441820b04140b2455062605480454283c4c6c0303006a03240c032224107603801107030484010b030171007611340a480844880c0e0f0306010b1428070060401142664020395100105416000c2580074403002641c1c04600b00b100001440e8400183c5407981000d241c10740d40300043c09000b500050030300360040d044407201031100d0011011840c1c01e8924a0345a08141e00944c00680281e90701d5844504d51804400c040040055151103940c2c002881c0d000b403080204905039861040d0841c0a200d40104500e40b00720070405030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 407289244 1250 407287994 407287999
    0x7051f020d050a08011e050d0f0203121204060c0201090209090d020706171801020c030a170906060a1703090d080d0507020c0d08131214070e010510050703030e0708030a09090b0f 78
    0x2619010410a401c480190f90301c42c50740008023180c2442003100f80c000000d1054400d500711792241c0d0240c0440c0341c9a0182083c02a40c0c58640400036005c502c050f0080c3c1c3c96a4050700000035410b64540106803011400c5510f4415540040444400d103941080721a0040480b8900804007647c00107051f04800005420b04c3c2c00b18170ba8000d01c00141d01c007903045078102e00070901180d03554130881d40003070f20b00d44c0301039103440f01c6104980014101c000007244052090390020642c19445040c10341c0c151142c3c50010f00c0c07251307900c824840c08959441c0c2e881d81c16800c03170107041019103400200d00010f080c8e550042110046411440468003951210319425260235400100d15850f54500003070b100a0050550003e20641d0080301e007441840400c1d003208407a2042102aa00790725242c3c00003136001e6034280700c1d052b0408895049400c00c6d0b403084001e02206886481c010822488060040c2d180180540080200c0e41001803101d11240e0010b03104d41c024021030100b0b0002120240002e103100701071040300350 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 407290494 1250 407289244 407289269
    0x80c100b0d02120c060406022104030506042006180913170a1202040e01050a08070b1b0f070e06040f0b181b0d06090e0606090406020a0207051f020d050a0801 69
    0x4030b0741c00c0103001c2e054003050040c12440d06c85a403080c009540d8940040041d00980700740b122000b4a80350031003181d0035660044010401070310b46549074010031030b0a584600b54460b541c2d041602e140c0c1c13032a000b0003090704614244402a114041080034258026140741d21149009190704001100203103520b15951a200101b511209210420341e8a036a4881a005c2a03a200003008034803104081ccd05181030364001d84086500540318022203a4031245800760700003030346041c000c0080c5054100042003a07882008141c88a03119405d80c054680421500325400800c2000c007080785d036003058403c0e14540c94450740e0038171502c41e0032400b0031911141446002401d001d1400000c00f1007506884180048003400c400990b24203803508000010842400340a05440c00e100d00d0b5120000d00003000e138000c85d0001d00501258690b07503603410095004c00b10a005600651a0000d0650344034051707031024041a104102c00c2d900c01105c000c0c14480c142c08508140401442450300c016030106500b4151003000c509031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 407291744 1250 407290494 407290519
    0x1080a09020a08070e0603031305060306120312040314120615070c0b0c0105070905010807350109110c1f060b0a03090b010e090a022407080c100b0d02 66
    0x440280040c0000690800811a4002040300c0000b41903401c8410741c8480c0d40058480c6404c25869109141101800d080322140a1080f4030f0254001c2da080400203095040041c60720410500715081003040da1070240652082106054101c2280040c58040b245007500c1d00100c800028407188001d00402e00980300403040c034460412203401c9501c0a0340203001d00322156981c0010300e801d94032075119950303154200400310380214002e06140c026a01e05840710b824179515664100c13800d0450400c0c210032400c21824090302020055020701541484406400040d81040d540c14144d5980303030103044030f88000f0041d030300341c4581c00b0446c803110071038052502400c0045043d0b14006040641c00c442c1d2b04010020303074816019015030062004611405881c11540e03030749c81513a04421000c8803002415008042290700514108601e440382403071020b6a142c1d4842d0003455030010b908070b00e00854206500142b04512200e0801c4542009050f0f26014408aa41e40000c15042102414002c2c020000c1011301c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 407292994 1250 407291744 407291761
    0x100302070614091b03010b010c0f150f0207020f030a0c050d060f180303050603010c020607110319030915020f0403063801030b0906152503030209010e011d0108 70
    0x14a00b411803598141c180801099252003d44541c070203445000e40d54121942810b010b00ca0b4883d030141c4800d110701d00c003030310340500900d107080c41110403000c25800741104059602c81c4d4401180303108001a240c034110f02c14881c00810400f6a5842a8020819500020b840c070682c1c100351401079801160302c4200d8940340c8003a00d0b4a201d0f900c440c0c0c5c2401640c01419a10f0500c812156010340d0701400f607911224181800c80c0c1c41000800016040360740090070660007450092014018030b41101e283c020031107040403020981c3c852250010303131940b140e02c09010103040300c2038004642c500308510340001d0803880c02040c4600d220040c95141c03100170f2280c0a200303d41e1103840c3c0000300940700076803c1da242c06450140c0042c0b410a80424035000709003d031402c2103848a0711031540580350410f000281809982c803904042c010a16030a5622040d0780b064051085c94081c1900c01d440168645640800140030360780c04034400782c10404003c900880702c0d1040c2841d001014820301f0004844c0c2c881140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 407294244 1250 407292994 407293001
    0x4140720010204091514090c030910110306011403071b02011209030305040b13052503020a080102190503061320040e060301060515030f1302090f15040b1003020706 72
    0x44000ca40d48089070001d41a00d168001024100a0680248200c0c3d00c4031040008211450380342a00104042c0020300d07440699002907810800840880f00e07012140030054080d03680130010740d1010840030003880310a58009288141013240b50703203c5400c41c504800001c00b4403450726090003c2800710100c94040d1790003400c0d0b80600340c403e014140100441410b014000c1e207000e1f20100c035454080000510740c032030394a844440b80c1c3c0d40100a081d4035105405090030700b00e40d4844031181c80da440100040165039681c0380d040104007150001d40c031590019a905040141e41c0110b4007400707810010040d1030355603d9480d20b15a2141d120004040f180309200140c440908002d1030742e038a000090114441410750b20790f9104220842c0288401616402800001552000e0442001301c0a2020680950706010003e40c4003400303102ca45144242c980014244103410380300f91600c02d07019018080c80420705c20b85400d1586041e2401c0c4035400c13400c03002c5038010038003200b00070400d940441ca99040150580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 407295494 1250 407294244 407294297
    0x60a0506030d230d09050c0a050112051522140408030c0c1c0230030402100e03100e061501050406030f06030c0303090816050d060f0f09050d020c041407 67
    0x6440039141c05400404ca0020180741c08203070341d00d204110218810349050000c240c1a602c0c180d49c1c200070451080d8084000e0301c4003425844143c214001d0410058881c03103940c1c0d81c880c4030140c0254641c001812900210b811221003030b0207120b00001044041991001102d421007411000d0940ea40c900132245d0b810240741240300e10303e4424031501c3c40d1100745e000134401c40c0313590f060300380c45035811401d90011120703c460000b100a207142400050050300e00004128600203050400c500762800560002c0d041081e240c50a1010941e1a1400748050004000e10340d07200003003514600d9038400040028040d40254803071602019100c5a48002000301a00031100848c0c2c420401d0074140d483c2e14003d44640c1e050702603050b4500c01c014800d1030b909800b1004100300c800180042c1404101510707482d000d0030010000142842d210b00024140e4521403180c0101c03540540050406c000031500c00070309110410311864490340c1032804854801206126440e0086000d0410062807640d4a140884010803507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 407296744 1250 407295494 407295557
    0x8160204091101030c050309060601030b0105070b0a1d0303041a091e030307080907120605040215130501030518031204031b15060501050f03060904031b03030608060a0506030d 77
    0x2401007801c0020380c1d02c0008070320900340c03000d00010416080444041c001180c05505560010f004a00154003a50001c095104189002c40c039020351a00c5481c40110260380361541203590785c104068400341001036a5035030210801451a5040540310310502001094502071401c0b02d002c045003c03501c1c10003606840c100350080e840002210f89120310385030b420441d04800032581c0300e00018001c4c00042000d2040d00c0c50003444140c00c6081c1d88031030b0000c0400800890f0011644041245105008009088115001480c044103142084001002d40b800501080c403441800c041d2142c20030400300a484101c03502040340103c0c1e580b141000c651146c40e400c04c0b4128882e91100300400d10510003c2c2c48070009400106010301c503036810045401e84070705e01c0e4002501d0320a001185040c13600641d06500103000345442070f102c40c103210805482c0384001ca400c8022aa81d0801080490010b10015511164074002040070740340040210351998200e01987d001c020041e0181c60600b90020041442c41640 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 407297994 1250 407296744 407296751
    0xe0a0807080109020918120c1501080129010e060f09150a0305070206040f03120b042f0915071e0b1f06050405040f060302062a03090303030408160204 66
    0x101c415a6000705582503003603004500c448005401e45811004101c00120b500004080c4070b8520585400c0c0350b0045031254600d4000c94100e601441c1000c0f09646c0030f03040880002441c1d8a00d070292046d8080c0350360305851100440700040c0c80e50b03a04801c0d511607491080d1031075542c070340545206064a01c076500750981d20035544061005004030320380c007501d4010344c1a107007041262074030072041e60741e64002c50740207252885980d44140020306c510743d1440400d414079004240007510b10300084c190b1305c0c02459200b00030503c0c0111003002240784514103c0651010f20946490f200c007020414001a1101b0009880b1000401c80100115013060716080c804200200032030a20900d0305404e481001d4605210380101405418070102c0c2c14000842200c0c0662a0140352525140c14080603005040c003402a1554910000007d602d4400041c49001c0081c0005441e049141c03c600c0d0744541051000c845c5039209001d00031031070314000203ea40207034020840030340301c40c020064041094800c0d000250001d08 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 407299244 1250 407297994 407297999
    0x2040203040303140112020609120c101206050a0f05040207170313061b092d080606040c050a05040b0f09031b1507020f060702040603120903020a050409080a0e0a0807 73
    0xf41640f02c2c2d5090f9050400070952640e90700b07825031402c03201d14006580000e0400c00403a20386894599035000d010440141d40c0c60003c240c4c00641101c2c490042c0e540807a400c050851404c5e41e1511600d009400d080f00d980c068503041075101c146c055401e009130b0f401280e0003d200320a20000840d500469810519040d40c0c910f00440580c1d4031803c2101c08450746800c045010161008818149100b140d0a80e110b1039079074540f40c8803442d41c034082e4845d00040c2c032203003c0200e110380752182944040c02c00d40c2c0040c04c035414483d050004071b03030701c0c00040000c0000034090340341c203594403004407801c944000351119102c4607614100b07142803040101c5140d252051941c0100340301540c14154034442411140503034004207800c0700040034403a25400940c08442d1544d010014034280c2c01504040340042c000140b1103480e030360341b808000800c4044c0400300300013503000c00c1145000e004040c003400b01a10103204101043d5690f540c24000e00c40c0b520203104002100c5080c030b89480c20002e00428249007102d504a0703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 407300494 1250 407299244 407299247
    0x30e0f070504142a1b06160e03070312200d09090527010b09070c0b060118050f0d060203010b040f090510231f020f010e06070516020402030403 63
    0x1040c4a500d00035400c1c24042d03200300500e84401c51040e503401c0041d220194036039071400807441ca842030440c8444028042117500c111640e640d03003041c0d8010002050241001010000078404803070701541040204900040c507500d02103540c1c003c40e0313400070101e00200d02175001515440140d81000301c1d0518080c04500d580d420001e1801c0303a40d042174030740d071250310b032100d07101001c0d0b030801c50308640304085642c559552240307940886043c00c2390040002544071510f000140408809440800024489007007040030b001090380301c203400c104242029420102c0b82c881004a1509600c241d03846024101450304094a03080c03400144203501c04811035503580c64180c2c880440d049805078640001d8800c2020501500324480d0718094a542408944c1d850b00e4800021001004003001960a0a4a9111080944440c030a040e40d24140c000c414042844003407000b407402030031b900b480146070305140a48032030300004642240c20000b9850202d640b081251411601028030301d00082d04942b0001c100002d15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 407301744 1250 407300494 407300503
    0x3030c08180d081803010903021c030906060905010303020f0613030e01050903060a0f06060903050c0f060403050f0c130b0f0907170114030c01050c0712060b040f150f08100903030e0f 80
    0x2012010226100e031075000c040c17600301c804071078005000d603120000e101c40c210442c85495174501203615002c01c0c07401103940c1d0001502c88a901808100d902c50005204058050215901420994000b0081071030010440344c90703607000319400341c03c1c000414401045d517440f031800c4441456000c1c0c22101e0701d052400c0e420b0020310380064000c4500380740c038401254040c0320300146400c07203030088028003ca0100c0001c00515503088408194070842c100800030014405201700541d00350840041e084031050102030000030b450900c0c001c40c0d01468036101d01c00302d541d440b0040301024000d07282d481c008d40d40d03140162880d02d502c0c113203180408055800050b42c035020505140e95101c0c00c0d8180c0c2d9510090000669150240380810f103a1504840000d0003100c1d6514000503005010702c0c001700e00303070b42c2140201e82107503174160615058075142c0c03004c000c0c0030241103420002400b14200c002c115505d00183e850715440b003807501400003602d90001b41c05061203a00b04d10122104881641c000d068100700341580e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 407302994 1250 407301744 407301757
    0xc050303070f030c050f1801030612030309031409180a0e010207230609060a05091006080c191406030603070302031203010315180809010207090f0b03061003030c08180d08 75
    0x181c10304401025180c03240098803042c1070081951801c00e00a070b1f00310b103500054004024101a921000012000b040c0d01c01c002d149400b0b80c42c0001c10000703d0400034640c880001c5c0c0070801802c01c1090300342513243c25003038100040818819041c242ca80c40c800754082c01c8420584080d0b0740c0040ba40f80c0501030740002940340110303051a40003000b103503c0ea80c00d480d0401111005030039000342000640110b0650000f0b81d2021240081d2049940c220040030211001d941116403607901040244445080c80c40408034100501e49007541c60606c0c08045291150b42550b00d58025180800419a40c5d00d0400211000d184e001707043d1040104646d20151480d0000d10040d60825942d11041944031503503c6400b881704558031480100c404503441d03400b0035500000c0300504620401d2000034040ca003030f22400040400016011402c0a120700415142c484c003d0f11b680c5c0440620310040001039045a080c03644664030a03005500c410141040b540405124211560004041342e42c0c6010003003140c000300700303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 407304244 1250 407302994 407302997
    0x302010c0f1a0c041701090b060d110603071e090503030904090c0906080105040b0a0204081e0f01060603020d110c070306270f030305090c0d061d030c10050601051303120c050303070f 80
    0x1702e50b1280d0000d5401e8405d80c01001d8000049507001c601a424076684540190340103000140f5540118030200c1c0c2c2070762045615a00080c0c0c05a8010a4400c0d00c16034003400219078505540d010f410400045e07181d02c1050003c91003155100c6002d8100010005030f070f8001c0140030020080d2a035a072800340d01030f01e0304580449440c540d00e800254407413074910a0320252883c050041100b000502c040c0303828411032401c0503481303106000095030141000d0080b040038000603503002d42c49680041c00041035071a0140c002a01407400c1c007040f44030b403e0006a4074100c07600510003180040030042d41c0c503941c445903140140342814035035009052041c00d800e407406003440b0380c3c0c00300015a6407004190f181c1412030030003603200f161048400003052070794004412804803003509000c81c00c3c1c0306400714a5a4424101d0740744640244510400030207a5115566100ca002c4c02c0c107600d0300107200c13296000b4040380c2c0001040d05420803000707000c0f03e110341c043e000440d038444100ca9030ba040c4108081c0c500e0030500b43c2d050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 407305494 1250 407304244 407304269
    0x6070c0902250f0b100b03040215090d0f03020c030106140405131401020a08010e0105100c030e19030506100501081b04090203010303170106030c020c010e0d121d030105010302010c0f1a0c04 83
    0x403100e0850100e458200c41b4101c0101e41152150343c00c008100c11101068a601403091100240a03a00d076601595524801c0b04540941071040c6006070428000040a80c860f9162420412451803092824030b4004012503000445523201ba803e411124002080a01440074200b540702101005500400c14080d0a0700c5078901c0d0b82ea03032640301e41198424040c003500003518500b04140c81d8090034100703807442d00c0ba007040d10242012601003001c0b40e500420b000d08070340d9003001c20010b01400740001c942101c4d40c12164440c0038100300001c0c1400304013500c0c804510460340502c00e400c80100c41034401504101505542d01d533501c1c03c0007030041d4258103402d041c0032624000001d5950013072250410701c0205030064025014903100568120f400038086c260082d0340b00c5510000075038200a1008a00c05a4503894255408103c800d03210400e4101903034080da150200510150380c000c0403400d205c0d5030144080a101c1003074a02a55820680070302ca03c01c43c201c0009100c5030b2030b00140900306542080d003006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 407306744 1250 407305494 407305501
    0xc1e08010f0b010f0c06290111240712020a0504061205071202090f0342180c04090c0611031213170f0a03050606070c0902250f0b 57
    0x2a07080310700300303209640883e85107844200c1160240200c104020300608001452400615640b50000d040303041c100301019428868600b2507820070100035100e1250390040c003604284038528100b46002041040c60003011000140d0414442c0c10a17109181c40b05805644238640b500c0090540c0d003040c0500000301e4130071075032001c10181c0b5104091041c01c550b642d1040e60512070141b440254020003d03280c0009a1189030000c80c0c03410000a080041c0041002d45c59200b0890300c03000003a03550b00a82c0c08140d0004448851a2410007031540000c5211200401106003909481c43c2c002e906a401703030880e0414071101305000c40c0b000c2c03403011110702d07450380c03c45101c48942c11516813141e920b48014001c071542c0450320610540030070b01d0000344034219802d01c0050921443c5141d80011a50b04000c280000d80c00103d0355050240c1c640240068800b503003450716030750364203490104602507005441d5001c03a914001000b0701040011820a0005410b02d070700d45410050030060140d4800d68503140d403900030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 407307994 1250 407306744 407306771
    0x510020a1d0d0b060919060b030411030a050303010b161a0402030105090706141602030303011215020304030c030e03070f0609030b0112020310090f060216050c041104050d0c1e0801 79
    0x20b51071a0340420b19040603602c1e0000c020454001408107032000030030242e2030301100410f10a0b00040c2c52400001900c0b8a8245444240b0a000c60441406900070501d4003000a4001044d2415a00368100017a01c130702414210400c01c014030780d0081c065180c0d0004082d080400c09806134096402500203125690720300494940e6007030940f02c4c000002e140072141d103140014510180244100540c0364a04c41c1d28107400003455600281c10540410304068030b0703007040040c01c0c10711401e041d034202400d600354a81a1009010600c4074100039080c01a80c0d94440c0041d6800d015a10251101d03041c080507285d1241e00080840001e40811501c1081403000420341a800210f8102d07107581c024010034840c817043c0b0110010380716000c400c66001c3d01c5200c20200044160014104204200c0b0114048524500b8643c0c0f50000c0800740901481c039042c402310004152400f16400c0d190b050780e031045005110325041c0c440ba0039640c001510401e0145028244600d051003000071224540d0003801a94401d241 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 407309244 1250 407307994 407308009
    0x4111e0a0219050307060507050a110a0c17070b030c0a090801090f1502130b070201021b1c030c080309010b270121140f010c050702030c0d0510020a1d 66
    0x1603405a881050800002e00d54503209401040c82002580d051036010381d2442e094520680b61740020600100d080342613654406030f40303c1012070420040501e03000d2074440c07895942070341c000c0c4203c141811110040c40d01042044000906400711040c2d500d140c8549104c29035048944620005021800002031030603050156100054020390412490141552000c1020a18400c4c40605039000d121812030560003c0d643c40040c1003991803195110464400203080c888180380f488003d603410030850721281c85444003e280480c1440702443c428a840c01d00b60340040d080c1e8002440039800104011080806402c00000c0c0340c3c0c181d50791303e416003c2c4c2e5003081411803040b00840c00644410010000400941d031a510b030b210003c04500f0801d0f11325100c1a0860040200d00f400c41c0e8058101e0010248091081e24613600d51440e22074201300e0550300298a42c5203a6604034400c1d81c403090070708207100041c03050503200c0340c2c1c021003150741e8020040050400a81401441051903a555640c0600d007850070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 407310494 1250 407309244 407309257
    0x405010302031005040c08010c050a0305070305190b0102120315090108060c2d0304030918060b09100512041514040f021e040c030608100b0a0902030c0904111e 70
    0x90107041510030703400f058002064000c000752586114031000065800c020b00c9002a058840e91700c40d6078500c41214082c05488005c1c0c84c81040500c0c01e0100244c54940800b10344040c0c410401c04602c4904904c0100d00e000b10303a030341c910070512000050001000b0508844440410140c80d0f02006a03a1042065204e9808403803900441c0d00410100005425440c5c4d03a00f87c0c4580200820008030110030000981d800454086010607600403061143d1001c0d0505440b801c955548244891424000c03402000d015508256006101d01082d2803400c41c01001aa04845800700150016140500704002c2c41101d4000c50900705180400c1c0701c02160052110034031807030700081944810a455401d201d42c21613000c2c040f24611b0040d0300c5501886d030710f0b070103404855021a60049465402c0400e1030703060800806a06403000d1030314141c0c81e025103803248500300326440d80b0301c0142c4960b1a502182124410300685503449482e00b11410896031104003c0e01d0700c456411052004145085580c5d2014440c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 407311744 1250 407310494 407310499
    0x91e08010c08010b040b031f030609060f15180b030d120b0103150b0a0215130302010b0603072c04090b190b0a1710050906010e0714030f040f140705040b0405010302 72
    0x801046c0b004940300384c0116080240140e610003802c5440030421542400c9070002c0758400c0e02c0b03c5820f004e01465005400c03942c00c14150810681035281980b5101c84407034841e4000002300342044d0340e00002c1c658008103d81e44080c041e0380e017070b9451041c020700700303032005101c0401c5c07518000848201d5480780c482c1280c0b512001c0f50102400d401d210324034440d03030040024502140b2071404040d910910304030005006e40440444242030914525019013500c42d4410300030300500b400d008101d8880ea00007108040c3c80d000d02040a5018074600100082c49514008150028140b008843c01c0105030700c0100d01c1450b81080c44208003600369500c1c010307a403040080940c06040090144003605980300c8841c82c09485408a031039200c00079503000c0580303004494100442d0002d40040000301c41c00031a49034030400901d0040200c1c13007002c800b00c03a01d01020f8a0007043c0000e500c005010040f50303030700720070340c560700207408030a140c8030040140d0780c0d4211809242d001d2800c21a2800302d07403d040c0101c5040c2e0390300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 407312994 1250 407311744 407311747
    0x1b0636120512040b07020402092701081005090a08071e20040516080903160602030601080c130915120b0114010c0c03080708040506280903020906010e01091e08010c08010b 75
    0x81b90200300183d0014100b49500c181d810010300c00411020408840000250f40d4007012580f410f141d803170030015140100340809041001708180380c000030a0041036540d00c011341c5501c50442d400d0125169003024003600d01c50208044010501007094004100302440d1080c2003d1440d9103030511054a400343c448550035854800c841c1c48903070007a03a03840d500011500c100ea0034298642c44001c40c01c18840c40039107600e6030020a00501d564060a440d501c0344401c000580340600f200707a10410f500051042c080506d03921840008564000001c0c9001001034290400750310a040c00c0580b412202031207428a590030749804000c2c1c650141c020614025007025008051038039540700d85940ba4040c101c100c1d90000b00704801700742a652034018100c01d10540c01c0001c812035500d05c0b060001d00c814542c0300e061003601c1404100582e01c24000c2d65100c01c003842d1050010450f0070040c0c0320205150480c485003030509041421500102e1510412038100340000e01282c032110740d0588e9121000c0c003c00108030030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 407314244 1250 407312994 407313007
    0xe09010c17161209080712030203040f080702030a0212010c20030723250501050f042102030601060c0c0e0403200c04050c04031b0636120512040b 64
    0xa40403101c0c0000c0303425081c03402d50800e0f8103400300d0843d00181803c0b11051008280203080c00300400d0040c0e0540401d081c11890348c04d240d200c4a8141c000c14900a001c0000000c81c2e40071074405010708900348e64054200401c0a512444480c0a44030b1150b031003001410072460f440900d1040041205545000400340d4074114450312a6042c0c1015010820405000c03051805082003007040b810192a2041510066070076000e0b208010894150384950304021042c0b008118004045003118102c036100002026600742d5200b48035030317134004598040c1d4180070b61030000400a400c029601c0549100d5030741c1e2840291600c1d600b4001c400d0564000c7e0014840f04100050314044410344400035050700212002003006800080c1580e00840e450602000085810001c0280d941608060b5680c0046560035250520b0b20041801d801d50500300f030745d540042044040d2101c001c4005400200681c6c0344085551280800c03406c0c3e00c03210004940b28499030015000c071010349002d8038250340348512070780d240c983c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 407315494 1250 407314244 407314261
    0x10c030b10111204171c021504020d0c1e050118030215040807080c010e030f06060907030f0203090303012103170712050f1005030a24090503040e09010c17 68
    0x41520349800d80e03c140b070008140361042101410041c05480c080c4003081c00c1c0c04a40c2420410303005950b508000c141d1141b20070564000c00c00e10b00503580041034100a69443c000610181a03603240641120001080030402850340001d00600c13130260040c0f58030a640d17031001190094400581640090228101880140b5007224980c61228040c025141065140c01c905420012980d0111106a2200d4641991307075810004500d8512811009840c0c01d41810712001d849090040403180710300c102a0000d89068004d5110b922034000310901151686001d1102a54a6000703004541031000600c5030004070001414071410b401c5c0d49655804070b00110f1218010a00c0405000c0030107001080c1841039201c00544a6035104140c46c0955001c0307400c09030152500c0c01c171107030030040c001d8000b11140b001060049504442c6106100d910a1a01c499403152100802d030720031008000d8000017074001103080450340c80303d000c2c851b0307030000f00615282c03a241074818a062a50908000440000245082 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 407316744 1250 407315494 407315507
    0xf0e030309011209260408061312030b12070e0103060f11041a07120309140f120304080702060a02060a150e070503060301060314030c060906091c0201140414010c030b10 74
    0x15202d069109172a10102403075142404c010381e00c8100c140d801007010000d50408000040e040741e00030450103401c80c0300d82c0310803800d10a0420b010050548802c241081a21108400032420f2000d005407100b142e220898074840c3c95003031009485541c1412660071900d6154452542e0740502a200940741514142c0c1e181c180c105170780c2c40541226020710102c00465220408251800c01c80e80d000641d03031009140085d40040500303039111096201420190206034000b450b402c400c2d021510060700c9659600d030146440c85070b0702009400882c0400d020311075940005040340105184c01050000044a60300941400803502c9640500031903807000c2040140504000c603080040030b000402e100c1c1e01c03038446407a80c0c41108284000c541c0300045200711080c060000c01c1d04110182c002d082c0c50300b41951503581e110700b00f9155101141d0390801801d03459000f50700c0300d240d1410421a2075618a0030707040c2071074003440000745407030154202000e203043c2500c240308403448840000d1820403c070700c40c0f00044611 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 407317994 1250 407316744 407316761
    0x4030f0c090f0225082a0a06021c0908040506030c0d09151121090307150501140609011d0a050307030b040c060804082209020304030f0e0303090112 65
    0x441080303008034a9545a0107050b000304410b03203000d603680c3d00f8900c80007440790116440c103440c2010601030b400002c074454200e4030502d42c04107008100030f0307805240d029944080070100c0f2a5201e200303402010840700c0c0e005008040040c980c0d041c0c41d40251100da8042d0b40081c00000d02005c4200401c0c80140ba01c41c0107944c001c84509607080c02d043c2034541110480b001d182d41654810706e4190348459200143c01040002d4010504013410204d034030a2464103402c401c6201507105105000085860404005645200790441c5603920b401c100f80503600001c5c2000e005106580b044881c030b0483c0c40c2004d10841c1c5070b220f01a520205646040c10300c0d4445801c141c52481d5000c3c0c50580c002400d43d8041001001550282106030900e08181c80c004804044540c031a0f810300c4407800402000c210403400381c0d001c213401503541900b10b00c90005501c080010319000360007580e102200384410f0542c064000b1030101d0f116115100800c1c00d0400b0941d83c2d0081c555402d0014040303141d801741c5034100d90010b401d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 407319244 1250 407317994 407318003
    0x1e070e0a0e0f01091e020d020d081c0c021005011409040c0503030d0b040501090e10021612020c0a060806060d0e0c151909030f08070c0528170304030f 66
    0x65100d00311920500b08460075012030300c03683d143c0b6031a10500410300315690781141142102c000410007039022818040c0800c0020344206d0301c5503000c1080c044800212000e07130f4001c0d82640e4031040d142441c82c0c0140b13591000c2e44018030074071456248000f801d108417170588080e440a0728000300001700b0032402503001841203800007005500082d25480402c003030715000044180200d0f8010049003840110b540581c8020111801e00c038652100d0b10780860714010540e114000566111000f071101440484055401449109441440c0f040103502240c4004911821100c401200c1d40e1703034502f1122000700360b8a0300c0e4844000c201280544950b5881080489013183c1540e40c688041000140200030100303051300030703c1000074414500ca00c588208807500244d8180005400e003181ca442800e003141c1d20300100301d48070000d03044081c0b2010124010051500a0001d40405602c01245407182c09041080b421422070300300c040740c1c0c2c2c55130441c1d00c00030714002e030010350825246032079002941e000d00c041540c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 407320494 1250 407319244 407319251
    0x912020a170c122514060304060e060f010305060f04121b050f060601111c03180b0103050c0111070308070807080f04081f020a17070203040b1b1e070e0a 67
    0x4410b41c940c44030071514100040084c0100420040e806007a01480d4403078221041c41d40d610a216031081c911003d155640c003590780f5912917603103141c003030010494501240000c0c4200307010844880c9464032168141c0748903205449880d02c5810840642c10020744000340208800c049600d0b41e04e100d10340c030804401d040d110203420101d00707803500b5003041c0918034280b002c0d802030b10822010b9604a80c1016460800c1c1c001001c02d603a11002e20f010b0514071a400130308164075a44882a0380603120411001144c0092a0703084950f524a00140d4a81110001601184c10190803140b450004184102220b410644441c0380081580c1c07507119035403241d2011200c5078410312116400e203d08802600140ca603a10040992003002841824902c03600c490f505002e82c01080399805c000d0307000300e00210b041d00c440040310aa440b050410f900b076020342e4001e40c403031200110740c1c0130828a03034524903017103210240f00b40c5602c0c1c144602c4481c03250617540c0c4443c20303d50042e4020499003103d00c0c5990b5201c100c140001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 407321744 1250 407320494 407320513
    0x90b040606171c1b06051005010c03020d0318020907081b3f04050a03080a0614040c020f010f1505010203031e130b0f09060105100c171e04060912020a17 67
    0xa090340110036000d445c0141e8071810002c86105207403116025100908040070244d0031643c0095544a800c402c020400d03844402c281c0000403010040b06003140e00402120306441d08410003411001d086803100103801e03180300604007090030300c021225100c0e4000050300c69020302e501c01c108a95610085032003009980103050409845080d40b2901491260015003041040f504005244060140201411030f01d002c504025804085211044066064801084084032100c0a0707052400c421800d55540d4207000107261142000c0e4417441c40400101c050740c6115827940e004981d40e02080b00c4440b5402c0c00b46072203a81c030480c05d404190b0b000845100800410443c2e5a5204614500b80e8030120b0040f01001804105442802424007404041c0c0d034038080c40b1400e0000401d13171614031401400300500882e8800d401d03c01c00b411151420600d0200826802840348103803003a030b01500c56840002c0480202040e91001b044c001e4010a400510460103e4108060007140090004086085210f0384090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 407322994 1250 407321744 407321777
    0x10150b04060f0f080708270607020309040f02092812030809060a0506060301052103181305010e01180b090708090d0203040b030c0c030c01090b040606171c 68
    0x4201400c0181c0d01c003100d4a4590102500034510032983c4024081c8041c20400300c40e501c071001603401032000700545c3e4402224071032040c0c070010701202480740f4061a401c10040ca500000141011501a60108180d0040c00001c108a01488000d40d5104041316101800079403d4406030301103c201c80c0108420559032020111054030a11045011a020000304020342e6404c0c0003280c1c0c0314402c40e8041c00146048800100035120501410344204012114016a083e2a105110300b2450581c2100e5403203d0300700c480320015000141c0b5a1007121000d0700c4040d501164000e1f1412224404410301143c0d00300b181c2c1c400c040c950b142e4101000340d52036011041c566107200401e80900181e803100c5035941045010281020301e1100740340300f550300400080040303100b40c3d402c1342d80c0940e088622540302c841d20320f0280d00714807406032161025800c1c808802c0a201244c50814003451060f0710801030640c0e981d00c00e401807241070136805d01d1504807060342c00d216010b800e0300c400050060303c0d200d040710061b00c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 407324244 1250 407322994 407322997
    0x110f06010905040c08030418051f050603150405010b0712021b13180b0a180f020d1403220614070311071d041103030306100c02030a0609121409010210150b 68
    0x940b0103448c2c03983d101c1070310f42c501d40304140d00194100c0e0480c000b03013140070b0b2043c0d2100191088902031480040082d0700084091094091002e005000b0310541d65240385050864010075006c1d07403494445409181c4e858000501c076080c2c466600307044910901c0d1318003003160000300a0700c50b19025403100002100844400c0f100e1504c1031107592409000d040003100b15007200c003626035000c00401040807040100704172078907101d0459411514004803403c0c82c900707242030150200c0044038521012402c800a55501904400c3e9640c0c10084216070aa035068202d07100107510078660030500c1c0402180340400d02c03039811300d4052280642281c542c16903c00814421010280345165034058407801d0004010700b1014400503504111300850035810040001900c82040b0403c1e0b81c28890514001004c54401340000c0e0320094004104010307629460a1084049030f1207c4d030680010120000101d040c118281034501403801a40285010b0702d007071a5180042c0001c010703146240c0c201c094009015a000b50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 407325494 1250 407324244 407324249
    0x5131706071218021e0303032e05060405060c010b09130303110304020105042601180b060d050d140403080f0405090f0f070f0c02031c110f06010905040c080304 70
    0x100200300c28030705103070000c200384054501c02407560304040125125a03c0700729082061a01110005e5007282c2191844080700d108010030f5030140004020009940d80c00105400000e14a001000c01d9007080070304520509110b008031039007c0c001340300c2409513040490162000c0c6100a0002407154140f8001880b51003088850760620541c5218110405a05014050f05040c4542c2081e05604040d80040d04d14090340c014500e1a00000c04c4a52900102d84c01b2461324180c07100007003103191040d4074002c410035140710702590f480c100c00c408200f640c00c02c2c202c28040306801c40050007004035903003411180350241001c0d00e00e81000500c03000c07011032407680c01000344c0c140201902741d0b076528102c240039031290010102d00360194980104496160403800040d0310544c80d103040343e403c0342d4a034400c0c2d48005141c00c010750548905508420141c007802000e40819081d0f0301c0e051007100043d085203950760220140c0b851242c101e00010001051180c200b9078000c1c1c4035581d03d00728607131550b084602e075402c00e6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 407326744 1250 407325494 407325539
    0x20a0516022d0102070b090a03080c25030212150a0209010e1305011e080a15021c0618090f0b040201090302030607181508130c0b1204020325060513 65
    0x70340b400b40c56804115840003045400c03030407030500c3d0113100091400ca00c07920018101c280c0010700c07440d0442d800d001d2080d4070840031100040800c0d00754625071309201c12f408106c0c0981d6100b04000c565100009903803018400200084c0c80a40d2130040541c003941004010505209610345803920940d078074940b003100341800c1903001542c1e41c5052181e800d041c11000c121041c429240c9824850035101241c4915000c0d00304070700d048420740c22a01540248103a04a904900401c446040d02c0140650049011100d00d10540074183d074141c42c0b9a421620340c0310b40103110901031704034a00010114040594407078014188182501d0352500441d0800c0e200300c455100107032050341c9400300302c1d40c171102c0900500000030003241040d080400c098400800036107800c68030407060402c1810049007004040c094450355044503154210070144031a01e000c1aa0124824003821f840981286449254801c00c640c1c507142e40000301e8a4120183d40c0340e404000c0c6207854100b12040410f9900050704c0356400100341 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 407327994 1250 407326744 407326819
    0x26030415020a05060a090b04200406090209040c0807200c0303070803041707020a06030e100606111513021216060f08090f0c060a09050901091e020a051602 68
    0xd10300f40e4182100100400b10a600c0c0c111640085207400504c2540554001ca0740c0c0381d9000002d04013645120f00c07240082d0b00034103040c8045030548050700a40043e96064030b0178003482005c40740c00d58800c401103a400b0009080030303609041d285104090241411180c01c2a94100b0320700030040f80c21070703104900c15205030700000184402c00114043c0c034a245018100380034181425603002507401c100502c1a0410036032260410340301840e040c00b4003203603980d05440c01c0044e075580d40e101038440e10764801e1503131740d07801190800c0c1d00120502c05402c1c4103005401c030200c0440c201d5030820038000c0031620b00340864414103014001a111a00c81c2101501c1c003505c85100f020700d01d141c02004e4240040c000a115089940400400702c0001962400d42008444071510b5030400b100454110078213504c80c0d903103c1900c5000140010450f07000403001041c040b091040c0c1404006401c040e44190413800000400030000041000c085000715a03a0910040251169031001038080e241c100500d400d02c4d404404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 407329244 1250 407327994 407328013
    0x1060602032517070c1203020c0405041a01080d02010c031b050705031303050105011a0a020c010e0f19140102070b071709030616080a0e06011802130b0d152603041502 73
    0xc4030003012001b80110800c40016420030f03035000b1344486205010600840e140c201040400c100703034154110764503103581c800d155580e41341c1443d9a41c08646210034099441c09007040702ca94403c1c002c1441210301c1d602d50b007081580390f100031501c81d400b610040e0342601090000e0034104094000751001035000b98008260383d4104440b0f801c800200b171070786101d0f2070002c02008031a40d03000b040741c848010302420302850884551005c200304600d820581303a401402200306840e00344015840c242540c0204281c142031101450059070f450b00d0600a245410a00f401650b00069040e1402c80030607200010103820003201d00301080c41c0c40c0007642c00d80c1c260382d010a0318141040d4001001c42e803020702e048003404128030800a80d40c4800b41070080b40391002078180c0000002516804458148114080d88180c032590354a903100c99410016064006c2402c20340d1401c0360303410400c8814203844090080d400c14140d024520203c03074000c14400750b40b501040c40005540c2901c0030842c03440c0c01150b000b601d0203c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 407330494 1250 407329244 407329253
    0x7080d090501140414090912070302010e070807032112020a0e1e18130218010305060f15010c381e061c060504030f020d020106060203251707 62
    0x8003c0407030598881003070004006085206105100c00202915030365415191190340500301b85005550b0719040c01c00180c00b108041e415400809103400350b40a840700c2a48174045a030f20b9842c1840040d104010a07448400340004015600070104000c1c1007000419000e0840d02c0181e800070150040421102d122820060034102c180c0081040806407401e0f45000c1c94000412407025a00001000302c3c070480000d41c0c100c10282c917882d0443e00141940c94541850300700d07060900c400d000855560040402107502070141e901d885019031141845201203850010044400c00002d00c0241c610950110074407102c0200281c81a000e09803040d60680d40340f20603d40440240030140509008012403003400200b520782c602c006401501c1214000d0310701d2030701c40404414840034140501450301c1d100600c410181c2251400ea00b039500c0c1c1e02510300c800201d14041e403c03035147e48a084050703001001041290466001d0780b503041e0700c0442d1288049180da458500110349040d820340d881031070015a800911 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 407331744 1250 407330494 407330507
    0x1302101218061a0a0b1605010b091017030703020706030507050d0903090515160204020304020a0e09070e0c0901090311040e0f010c030b0316060503060f060703030b1c0302060112030207080d090501 86
    0x3c03641544c8403201986004e803000d1a61003864202c0842c20481ca04000c10480290803110f8680b100420044039410700e07244800b407138980340c410200001c59426500b13080720390100c01c0c1ca130550f8168014001c02850200b0a402410005221108005003002440201c440720f1040f00151406540d4080703041d428003050101c402c0c000c11100c2d4051030b050062400c00c0500b001c039040c40e80d60641e400768581d12144089a4185070710782014032500010003c010310f203140010710400701c600c04080d04a80e038487d101c42104a110f04142513000035402d850900c0841c01210015a50316005000051508c5420095034280703c60a40403401c82e944a002d107000da0303a4180284880000100c0c040c00c02164201603e07405608144079203000d0040100000d682640c803404140806040588002d64034a01803a004004000e0208468441e00c00b01120711142d803204490846010341c10f40050095900380742d90340c1c0c008100760104a0451181030b0002c60021014808900e0303e5601d5215076807144e08000002d09003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 407332994 1250 407331744 407331791
    0xf440a0201180e011a0f07120905091501030504050c0a0314101407030504020609040614090c0a0210150f06050a03060801270201021011040806130210121806 69
    0x842d140b1002d00c80800003000c128115006400f903161500300310783e4102c4690161280451642e03101140080500c9440251030b5208480c580d50a0341c0c01d43c03203c04002c05114261141e007058454805402003950081c0c0c09241c015004004803619110490001a000032032500708844034103841c070410f41c00c0d074810000e00003030040120040c0181200b00c988510301d4200180031404060311680804e0540d20303241c0c01c4541d000401350080c060291206a81c0743c0c03200d144102c1501485801001541d1440c0001c162844141940e015001d000c000d407080c54050701c1c0b0040811810020340a00003894200718000308014401c0b030310b03580d8076070504881c0901201c2180d40052260790424a90b00403d00303207440c84d0209418030884011a245003400101e142c01d0b6840000d8200ca841d1011168140b01175501400440d00e051007112901e650f0040404183e030380c4040001c0d0004020840c0e076190074043d80c40c02082004c0c464002807841c1d0808629140d580c0e10340d03416114540c0e0f0b50114811680700c2c9051004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 407334244 1250 407332994 407333027
    0x301506090f021207080c0c06102309070c0c09050f010317070c0b0a03020c1b24070611120106030212011203020a060f020409020c01150f440a0201 64
    0x1c02030f180e00c44107041c040c014850740800002c0c200282c100700a42080d18045101141120034601d0b0102c0060a0003000380680150803600c0108140703000300142903403003c440042d00c292002c1e01c400c0010303188200d001d901141e06001c1c070400841d0b02005445100d1040c07000410100195241d41010042a0050303000700030751010801c917007008240011145400c8943c11002caa0b69403c503810210024019100c90100070300551801403500c0768444011010f2110440710b4490101c141003c0e00d4079410802c0c070b8031618480600580c0c011030a036a200b04880150200002e28295000d150791012075000d801c40804a030740440c4205a000e00b403a42d080c05000140040b00c620b00d5640c8010f581c4100f501002841c294541d00d11071445803c94050b60000c052004c815505c1e04100f40440c0d002c0d261050380c5016a40400000141c01c0050890395001c403400744c00d007040b03483c14110311544560710b007646c1c02d003905409102c4401c41c03012180d01e411200103520090503e180845c800101920550b08106c034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 407335494 1250 407334244 407334247
    0x11070c14120307031b060c0908061e0f0717040b1e090307020409111804061b0c0311070e0f060306070905010e13090803040f030e0406301506090f02 65
    0x40c4280c1e0008110f528498060512164040c0b514010103030703985030f80700018029810028400115174020030403030151f90750602034540690301c416032441911240d40044d1088a802c40120b800609801d020641100c1c0f245000100d80001640c1100303121000c0e541143d00750000c0c0c040109056207034180d20405960784805201c0360800c291801e9880c050ba001c042d110b113991705020020040300090008244001500580f0305450050810b24a09401c440c02c0d1035060030a40b080c0002c07030311121010004403042d210510942c2c96500c0440780b05840c2c0031000083e201e0036502040b9030700128107942c4281d4541c01120410b2510100b414208007020f40340409001c052507081c0322507030b00f140400c0400c1c042554002454141d518070403000d01007059024124400010501050280030b0780e1201c2c045000361a00440d01d8881414482100e81038072030368812612180d4a01102e400c8840405100c1500d07103503594412003503403240d1507503042d5400b1414032141d03507240c20070104480f80100001c0f511307040f5046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 407336744 1250 407335494 407335519
    0x17070c0f08060106020c090720010c120e030901082a0310030201030b04200d02070b0c031f080a171b0309011101050402060d1518090309210b060411070c14 68
    0x2802c42240a40342343e06000c000d0b0325100e100010f0455506074120f9040003442810100f21002e0411800084040c2d9201c0c00c106401c45014000000c495000c00180d4800b00d065542c0b0400c00040003407502c4c802c020049607400c094011100310040c6004139901c03030b9484441e918501c00034040360908005940070b5800c0004a044080600300080354070082c42c050310f960b5186444441000707209241c0002d14006094080c03090065008002e94850020010034141c1d01040fa052051254002c1c41241c1940e405001d840380040c0940d90844c0400d122515200d003010803101d1803038486604441c56121540c40410007210342d40e030040c082c18442c1c07550b000070405800c00e50080b600e54411090403842590700da908081e50100c06224040085c00360600002c2000304440144003c0c2014240c19000594401001710b400c10128a0b00081882620103c400c80c2e250b9035640390402100400d05584640e0320303080c2c000c0c001c200700000d0650701d10451740c1c02a91800c08021111b00c150b421116805251220141d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 407337994 1250 407336744 407336749
    0x90c0608090a0b0117030906040e0604050c0304110d080408061501080c0a050301120f0c06030b150901050306040c022d0601060e01050409020d090f0f050601051c17070c0f08060106020c 81
    0x801341514000107024407146000340101d4618443c4042c0306420032000180010903641603c413582c00f9003401c582c240030f26100c80c01030300d0550000303540262419035030380811a91442c085505103040d5104100c0a030034039955880c0107040523000c44003000342c3c1c100f441c511700c2e007036070710101c103d521072003058401d410007142410043c480e0005006141d6103071656540e80f828841a1000c501c0c02c0d0340d01120410700161181001070241c404500100d002d07810100142c030010600c2ca00b66040c400040e9140b80c107645e01c85081101410782314000c031095000d42c94040380100c0b52910608c0c0c0d400310b00d1041108003544555400d1400304145e00100410421070304041c481d80c0d00034100e4044407070111000d80c4462031451800700416280a0080602075400d080400300b00c4030980100030240940c050ba07040e41e985206210106550030081ca40d04214103402030000341c8283d5250541c1d507205042d6a040c0300d013a039078010000300550003528103103100141c01c01103004100310050150503644043d01207040550003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 407339244 1250 407337994 407338013
    0x50609011401200319180e0a051005030105070c110307060c12090e0a0c02060f040c052e0504080601080309030304090c0e033c0c061606090c0608090a 66
    0x40290400c0600d6051802c0301081c0c00c01642040519820f40c0d5072503108004c5203201d8001d041c00c003404150001b040351000844c4600400846a1a12000d00c507603480ca03200300010a401071010302640020000840c16480074803840b8803445880e1a0014141081d0401408038940c1c180402c1c400c0d03009403801c3c40441d80c8444a60003c0358002014409070584003016507100c1c0d281c2e0031038004e0412840c01c001035021150410120003035580c080e110503494240850100f031700201d03006464501b11460401550404810603000404160302c11505080802e15140014140c60110030000d140440c0034804000c050204c0d44c01000d584004510340004540405c0c0c40b80901d2059101c46907503101d9103911280110549a01a88010300b075407102d00155075031800c5482502c004515503202d810074406503c6170f24141740d1180341c113807009000c01d6480004101090b40700440042c0d034416041440d80008440b0701401030b59502c10610002098148034000380b455070010500c600c00d502000d00ca1001c9a0142c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 407340494 1250 407339244 407339279
    0x6021305090402030705092208090901080f06011e03021e0a060804110d1106032806050310150f1203020c0916080612070b0d0501060e2d060313050105060901 69
    0x47c0e03442240d640c2e00758251040c003401c1c0080c8103c03981c0d2040301010054a030004000d0760100302d03402495039886040c0c86a03a40c0f008018402164000c000501582482031405038445c1042c1001000380c1c1c1e160390100c1c0d1403815a000c1521024802d8078040c103640b4204110101400320383c9811449483c1c144c8480301c03400c400702e03002800390f0364100d40d80d010f01c0201c040030749800c0405800f007641c03410b00840c240303100303d42c0d05e104171044140c0c0014080c01c05c0f101c5c010031085400040040c090306440c000c0800c002c110100e6441c481540300c141c00144002c2a080c10401400310500f201c0030780f061414042c0c201440c0e0007a0503c83d42940041040c2801010210a00b070080343c9013010306036503214089000c4035424104c180013807040c05070000f04a00c03004002e108585a5010034041030b680c448094800300f40001d138440d44030040700c0350140e8041900900383e0b1310305070030f04a01c038a82ea9160040790150348165622100e40c00a03c041d101800b1007402140c1d004407080d140300256615050b40a202580010b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 407341744 1250 407340494 407340499
    0x3060403030906020904020a020c0123121503011104080106060309080301030803091509030408011d1f02040513240b0406030c05130801060602190c050105070203031606021305090402030705 83
    0x190380c19003c2c0169507065030104013015204541e2014a040040e5a0f000b101c0700d80781c001100203003180c921640d205200c123400d0403240ca0150038156601c15448220900502c3e06d20294580071000e4856a0240100e00c00502d01c054416035036401c10400900751001364200c81f051505050f090030000d08010308481c1100d4200c0700b0b4644989850070309034240500d00a1152500700410180444a5804001001111403100c001c02014010300304840141311002142182c507000740712912503c241e010722818801ca4a01c40042c070709034441000854000c80f622a0314082039440c1c4171020442040080c600b0610701704842045042c0c41c00c01c440400d440345024502c03c01d42c82d20342c2d9481d0700d80900b041e609149030b40c00545ea255510707522403034000c01d481d104040044c480c11951352041d02c1c41141b20401d05811a11140307116040c1340055445a120810482e0140310401100d800600b48000820140c0d21520002d0303035580b0440001c400300c04c02d41e0041807260180606000061b41c00141100c100e030f605 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 407342994 1250 407341744 407341751
    0xb090d120b0102030d0c050d0b0f10031d030a020703110910060320031f0605121302010c080d0c030e0c03150c09060307030b191d04020604090c0305180a020306040303 73
    0x40e81c004030b056000c0c0d044800d504900b85814100c039250080e02520780304503003a0040214070018004c05c90a40420041503420240303854420754068031079044a00c100007640c403030007078030300301d44d0490351071903200e1003d040058010303160074410001c4c1c00d0310f0b5041d00e91007103a582425003050070306210543c2e020b106200a16580b047c03156251840031540154400c1c05e082c60a4407482d00c200c03400c0c0360600001070f0000003041c40f1804030f9003a0261054036484142d071000b40c2c102e039440c1c00000d003005501030000d85c1880024040c032000510340000500001040b004041001a1103587c041c2c00c0d6004100f40320200d401c0881002400d407800551007000c1d501440256000e504d4060710342c5020300c02c0b00c10580e0004030020800c100742d900740d08034044d14803080c0c45d25003183c1009010000004054041d401e84101150703103003c0000b2400d040103030031078001808075141a036155001c0f4200c2c0c0c05040c11001083d1a00d0403c0f074030440c4826940c92070215000a80a45600c6500103038170707483d00620084c1410358 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 407344244 1250 407342994 407343011
    0x605150d12031a030304060302130f030c120201020307140c04060f08340815060103020f03040b070e04050907031505010b09220903121503150b0f0406030f0b090d12 72
    0x80381d14603c0b009a5028003525600c035201c04000b4065484000d20514082024500007401003903019403108694225126181281c1406241c0c1c0c0f11811a01059045101c140410740c0400c09001c10800c0100a110082c2820701c0010f0500081d81e2481d07000802d01c01180600f00300824000c6040d20340c1440200c8100b40344500c40c500700106161140c1c0300320310741401040205545070000780742d14a440c1d2007000307410300d540c54500440c03d80c407601c0c480e0149540207001040000c2d8120b1138464021105091000b650400b201c04541111004c48426101d94400b030010000e0100d10b0f098800340400364501402658100124080c0701e103e40c03030315a07014160085052801010502c0200706d00c072101001070004562604008007280b100c055a0111545042c41081e021a07008006c4801c0360b902080c2d200b8100520140680142200346009810015160700c1a180365100d11404c030184bc8100300c2c0340c60b01281ca0501640c40080100300350703500d074402290425881c1d00010f462059001400c4042110007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 407345494 1250 407344244 407344271
    0x503190306170312090c031c020a021207090f0207080307080c04090906020a0f0c200d02090109050403020d050301031106130b030a0b011107060c060f0e0a0605150d1203 74
    0x500d07a0082d407071815a02e48910b40b181010000b0b291303c0604141c104401d484440d04281c40700f003628070842d89540076078403101e01c000070005024200340c06401a07402800807031300400c50208240d0394040c59504400c0c014080c000f018490700710b50484841045040c140140c4d95a01d6610000e400c2c3c809010300c81c0300040007105034900f2a0080d10480505006160f02c1f0310346400a0340024403c44081035289403c1c4014920414450190603040225400150f040d0b81c07003510945003030398015422940a0100c440913880d1039203040d000b41484c04002680d4039003401e0080c28054820160010400308000400c046000c001d01c4518491089490640d40d16045002040380e41d540d910103020340002104020400c43c4039406011807110a0300c600381e42c0c114001006440e01c03030034050f0101040c0c49000400125000d5840200d142e00062000501001701c4220726103480700002d01200d205454500300100b508581e100c95801c00d8040e1b42c2000d07080d81c01e5580300e00ca00981882d40d010507580b11031103021403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 407346744 1250 407345494 407345501
    0x201151a16020d05060f0105060f2a1e0601060e0a09050901021c0b0a050316140d0204050c0a0e062701090e070c0c170d050706061a07110103050405031903 68
    0x40740c0c0180020301901403071600039111401201c3d0fa0306d144000000010365420f060044855491605544c549044800c00802411440c400302c03070380d1b200355844151800da000811840755241090103010440414058180f440c2100c141c024100f04444e0904541098541c00103600503242100c0c1d0220b540c1d40d50640180c028010f02c24651544408480403ea00c0803240d40500061442543c1e03001d1305030384920626544040040d2861340b00e0300700803005c00044220031440c44003004028905c007240f80a5400003810340b802030301c502d0841e2100080358540c0c1d07500b040c0350980c01d02c015a413140c104503164510040d803080300c0c0c2d0791032010219400030745202d0388076040102c041d000840301809541808500180400f40c09071040310180c0d41004046440d140600740e104c440801407000300b40da5032810300112036981040300110707030258690501203400c00c1610b1220700c0c007881c141c01050711030740141032a0f0180300e550714005060501e00010f001c08108044210707250700b40b1300e5540103000d03021400c044004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 407347994 1250 407346744 407346787
    0x30c0b03090102071a150f060d0b01140a02030c07063b090f0a0c0504050a0311010909050a050a0f020a1403060d05060406091202060c0901030f27030201151a 69
    0x300f0705200511441790500004601030030b264020780c034a80700e41c0818003803070302008420301d640000180903e81228074640c100000842044c580b2611132264102d0b070304e40c81e40040408c000940c201140400803844200400c80040c8507901e0f00841c96150040324180249021002e81c1005420050340441218580b40c04100544c016106620900d0210101c0003800702c20b44c3c40c29466424051400c2c262442201a581500c400030000341c18649907586a005840306015110306008d1481000a4038001c51720030a0320038001350300e000c649403520100d844200e40d442c0b000140040d1041c000840040d074480e0f190800c041d4007100c1aaa40d03184d80d40000ca0450000340001c02d603100d42000c200401c0065044544010b1242c070180c880040e4000060340c80e0001182c40000d11001031150701e280b5803103a04280303940c80d0500400111503100401628021030904a20040039200103031078020590b09200303c1c40700303181c2d10404d00307403141c10b05140c04100e0300b1148041c81d0700f52010030103092642c640c0d80090b01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 407349244 1250 407347994 407348003
    0x20a2111100509060109110d02180a08010e0715322205030a02011b020f0a03030215070519110c0d150c0503040807030324080f060907030c0b0309010207 67
    0x20401403003460200685412220f02246000d110b0000030192101c1c000c40143d401c240da152400c10601c0c48080e002900959410741900d4844119611261180003030130340545130319000030800800c05401c0900e031241035800f94030012140c1d02c4103407403150311119480210101c8500038800e1b05c2d280201302420b05052100d03c500b24000a28052207007100c000307a4811620140c50740d4102541c034410136403980a9040082d002c0f4a15101801600744004001d83c201803001307140001451990740031034013250bd150022000b50b4000404840008881c1850943c40070b400d00c0c00a20344012a003980001121a0b01900280030031410f248107080d50a001c4c075012040098544040791245050014003041c88078144007210740303040c00e01090b26116004481c491034000c136034503141140913a0201c005208801c075a003c0d0100f601082c003141d0300d40144200041c05480000c0c03404440130702a071401c045000e801e440055200035000c000080341c5565000071190490806070700d99654050850180c414440c0040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 407350494 1250 407349244 407349253
    0x70c050106061215030506060d0c0305010911011106040221100f06030c0618030b0405100c05030a2f07080c03031f0501020d081501170a0605040c020a2111 68
    0x182e829400042c01420a84003e03041c4443c20300080480360703e442c1c03400702910f950000c4000480905061315032801c1d103489000a120740310742c1c0381c4886003119940c000440746001c03491103089542da80f2210740b40c40c40c0007081c05440903082c0b0340c5c009403520014008a0b0582a0a0059048070010a2043c1c046100840e48184800810030f0200001000c0f80d000032204564404000f2500c14030440701003c0d40000ca007070f40030240e07003541c80e1000c411000802c11034040c880e254164440072150300520300c3c5030005896154076801e00995070400d8880002d14603119245840c58000012120340c45040480401c050317650340d494140c104191913201d001034801d5644400410312024140d90071005a03164490081055100c0d1190300480e1215080d045680c00200e0040204d030030089114500c541000050500c0001c4118910200360118012181d606105a8580c000c220f07509141c000c18140d10140d2001d040c0c90841071b03031691104014401c1c05186448410030b16103044d801800c044810903880000c85 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 407351744 1250 407350494 407350499
    0x10080618090604140a050607180308070605010f050d02060904020307200606030d030c02030a18080a0303140903030c1c140f1006020f0a0b04110405090a030e0f010f08070c050106 78
    0x150b84203802e4800310b45502180d4a81c039004030002c101079540ca41d1040183c512034031216000c50303019800310006004031160007030003c001440480148221881144041455072400304d450201e00150750085028040c940c2d9a000141e035030804440b80740b042110010b1300c80c2c880d41c3c1c3c11940e14a190508810b0320004000310541c492002070710902c540b504804862064040000031400c2d41c412080450245e4410312058203242e0050100004c0c104500e011502d02555275004103180803154007003900441e983d08440880c00100c000981d50101a42c00154514100200c0c4a41c5030705c614034860005071600b00c0a564085140d0f00281a411040328200c0005c1c00c096003901940c0c0025107108589507507801c80043d91a0000c21034010421991026201c1d02841f62100000c9100050040701c0b1081c405081401d175030b0341d0b07100320790140344035400614403140c0900d00a486c1280c5116420711030180c80c41d580b002030780d00404c6241d41d03445034582840c4070b46030620150344007080e040c002440f80d4240300c0701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 407352994 1250 407351744 407351761
    0x5030601060206390304050f030a05091302040812030903120406020a020c0a0f170c04150315140402100516080307020c0909060c030603031306020303060112050610080618 75
    0xa060103a01d02850196044061040d148101d1407035844c00b192980b50005005981e40c040000795500c24022815a8444803104080300d0844d4044001c0101140300461281c81c0d42c10b2041a01c0303260411034108500c1c0c40e007450304d03055a0b40c10072108868a01c40000009400030020301c1503d030901d0a030010b007504c030f04040c03074024040d41040008400610a8807107140a9150500300d5608a030850600c01410605050900c4103200b521449410740e4410440e41c03204a880d00d21450000701d40e80f00c8403a00540c01d51400713040000c10811215071080c14100b2014000c0300080506802960444402d1503a541c0a0004c2c0c5e0107000309130081002c401e803042d2540034082502d0003540f00c1c800a07420f4406859842c402c01119034010748201d44540e10240002d1114000b0800650708640c1c010112801d00403000754070480c400c0140c04c07035401600b02005100103541c1010702c5882c80301560200380310615001c03010030404903210742d04a041000204c040b40d0581c40300b4002500d050004060b50020b840c10000b0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 407354244 1250 407352994 407353003
    0x904030c1a1803070b0a0c03020c060f0405010608030a2a06050415110705060a090203070f0902040602072315040b070602070203060c0903060f10051e1905030d18050306010602 77
    0x1410021640344a601c00510340b004000c44a5240d402070203008a51075165903840140b481c0c2c811f840915500704052400620100500b03840388881c24840c201c0c3c1d2929140c01390a5413031503888032507113a109026644d0540e42000c02d200f69401314907003080480c481c60398407201d810a002005090f00d031412090009112502d031039080400c41011061002a03103070f07000c0c00340900c00c1520141080c0c0041c0e02240c00040b441d08010017541c0010f088031030315a100c200205991216602c500c2540d5800201044a1a0103111510040060840d880d20000140d004600054044240c09202e003400c002010882c12007203054602424002c0304050701ca20903454890b00944c040001a44244141c8002441c050480320440b156414050043c03e0561110072400c442c014002d0f041c16101016090041800c3d04c6004404100c144018210460800d0a405100c08070007200101403850751001001c2c8644c0d14000340040c2810721620300605880c43e442031428a01a150f00f2a5a25001c3c0700d000241c0b00ba40000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 407355494 1250 407354244 407354251
    0xf06130612051c0203070204050a0b09190e120406180e090d081506040302100507060c080a0c0f050a0f020a0609060c080c25062307020f03040803090904030c1a 70
    0x411a0301c40120f600301900b41c0c079902c00d680801a8810402c50005080030340065030041d03c001404185100310000151001800f20380468080c8050180303000950054000d000681018801528102032070300708210041c4218080d000a20103c0d060038101e155444198400900c40385550ba2854201002855181d03141400380c20000361003175000c82c503150304072003030001440d0300241480c0c6054599420b00c4613540619800f40305100c03080c03000c18081102130003000c41e141c1c410360303650f503079031410351440070481d015605c890741005030701000b881980b40c01c401164107007811820840c0324260080002c03483e100340d010300140040d007820302120802030b06800459150582d42c413101c01e41d5441c083c20041c603010f0300450041e0105d1b060100c074440350041404034011805045d020541e6401c12905007101f040360950000100c03084c0c01003081442d41800034802d132381e04c41c3c0050b519051500320030b03c0d902e0003540800c902c41c00c08a40452708240c001d20760200c1c0107a00071642c003004a100303103c6181d50001103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 407356744 1250 407355494 407355503
    0x18070303090f06080906270d0e090106020a03020d110f0a1a0702030738041a09030c07030605130506011508060d03120902010e060408010902100203040e0f06130612 72
    0xc0c0c0840d1403809075003140d202d0700d0300320020b05c1e40c1c1e614903000000706001032a05903140903000005683c3e1174020300600c8c1c482011a20b688441d110350b00140110700030140d0295085400920741c0f01d0004e41d000c501201c843d10280b80c89041010030038122410030066403c0c0040c07910940350541c08020240806021120105402ea8141e69688a040e601d0b0300c58040c00910700c1d520b00d02c4030b0f0404881e440031031f02c55610b034051100303000c0e5001c0c07220054400d0540741a545030b45060003140110499404403644440b030000658140ba01b42e500702681c90905004c010f05132a140c0380080c101844000642000e180c1050803213001e540c0d0307031b81400e561071412541140050070402c0010324a0030016078500f00c4a07810781d43c030905902e019140c42c00421140e00204d0422601d4241074100e5a0741320b001e040035000810000176007144520410415240d00c201410641d007040c0310070005044404041c030381c44102c004001c0c03403560320480010280507400c04242003442c40e00784045a10754071401d40004187c400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 407357994 1250 407356744 407356769
    0x100c02030c0405070c060903090b16060b03030414150f0304030519021f02090411180a0f080a030c080706020d1a042a03180b040308010b070f0305031807030309 70
    0x15078180700039a002183c4200c0868a821100c20014001c1c0d40310b03420160083c60b08403001600c80001800316030041c1c0c01c2e0b0f0740d030441907503074101070000e64801c282421400710019403800d441c000100383c55110210b0024801d003d80450300141081c10b80454a283d000720400300c1d0b0340e107003038500a00560400c16040c400038402d001400010303800010a8035008002d8000c010b040c10900103040c029600c41103042da00241c4449903011400030f103c0c05048115241d00d5503603120480002407108200450348921046010708104204140001c141035a1050301860300f08031102d1203040030b1131988190f280040002e03100140e1240c3c0c250159105280740c01624024040ac501c2c0f0000b00010394141004d1100c401c00311800040e092664203544440c104254140400c154485a080b504002007145042e5030700035201040204060340032004501615002c5849420400e130f0340c407a1051800402d100506120002010801e00c4201213400407540050b03404607140d5a4507498018400d04441c4159030b41e01c40c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 407359244 1250 407357994 407358013
    0x230a081e100c050d020a0c050708010608010e071802030405070f030602030a0b1e220e060106020d09150507020d0605040507030605060f0f1c08040e06031203090d080a0605100c0203 79
    0x805020b55070b2a2281c0f0350f102401c0401c0c900f00e220007980311042c0541400440c80c0c006000a00030300c0403a00500101c400012168079083c0d8040c2514480c841801c1590018142400144444c5042641c0355042c0840144c8950f16460400d107080b9882d000502e451050304400403c00045400461043c001100c06004072030b104d8003880016640c1c20800340d1118a410080481410020440d0400c601c8495800724403070029480d01c41100c40d80a410142908108018002c035a0100702800d90503a040c03030700d0b010443c80c08000001e0b00096001100411100091000070b540e41e01803032503210380c0c000b1002c004605291a1155803000c4502c0111100c9050400107205803038000041c004002c8054081509240240100160401c40411150220f581c1880600215500c000644064000003c02d50054240082007500d0b104080300c0013402c01c5400c0081025080c0081820b0265044504107101c040d1108043c00c0d0240416801036a0000e008041c4111103680c0088540300090081e41a40c18204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 407360494 1250 407359244 407359273
    0x60212090c0a12020637050912031207140f0c0a03032708030612031204030e09010b090103092105070b1e16020f0d0c051006230a081e 59
    0x1030510b44040e500030428421001e40208468142d40d07541044582d6401c00610003c600b8000241d036007206c00005c8012030f0381c00490425001c4100c06030301100c011030600319200a940c454640080810080080302c0e500000411f040d40e040e01c2900300c9600515031074801001003240d60f00c04546064001909041e0030b040046e9900c403100340032992203440e002e0099440d4071001c41960000e49650f030032180940c0300e0000c080c2c040c4085c003c3c902d40403403484c105050900b0010302039205c250a85100390006001000301000f41c50032100b42040078240814684a80e0404240440003500705620040c40b010b20f485803554031000601c040c500c070307051a00d2291180c400c203d40041e032002445a6450709880445c0402d60300d240191152030542c8101e580e10f5602202c40303410300241e10a201d010510540304d07201000018030034009040340c4080100300f07151401e48609402c0d128000905a180400003822820780c07140ca003001c01414400c4210751170303410690010301c1c030504085000f17181405202002001c18 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 407361744 1250 407360494 407360519
    0x3300402060f1305040501031a01140306060f0616080c0f0102040503061b0c1f1a180a0204030614100b03040b041e0b131104060501021504060212090c0a 67
    0x46401038805800d00118031012805980003004114003400e2030f210010b160303919401071a0203940305007044030100c40030034558800c0341010b0f008041469401903481c051074400055555200381d0840d0031072154840040440d10b64840c0b002c0e20b418010038510014144840312000700030811200c1e04030f4031036400c641280350807400b4a010b0503915400c80d1000c264100032140e258001c082d600007030305103450560110b0f58900344161032441d0707080780d04480f01507102c2100c3c0305000c091b03070625500112a003241000501540707102c0000c008001d24031008509440c0c0c05a042e20095079008104106040f0520369000015900300e90940043c4192203003c500031091206590003150b110703040d901070f52960703640c103650200b0360324060481d00200d11405010800400c00a4040d6500001d500343d000818200480707074014440c0e91500580c24a08200041d9a002440e019001c00b078101020107610340d880d00c04064400e5413680c0c410f0a5919041c080d40307201c04100032101c64403c640c0381c0d460a903603010080c0c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 407362994 1250 407361744 407361751
    0x2607052a09010b090103060803040608091002040b1219180506330d0605010e0403230702060c0f070305060f0f0f040303020c12040605120f04170a020f0330 68
    0x1050900004011810b03003e0041c10301202c050501243e0151074008003491504a03074001d40001d050141800790b4048103101010840140c401c096180c2400d00203201c80a110302c0540b405c81649800c00211120403404a09038480d15804091010f103080e404480f00c1c10090309000c1c1c60500802020502c0b40b40151003a1a04854a00840300c48003103031001c0a4411007003e40083d013108007000c00e10000b8010b84262401b0f02003030202c044242c00d10742402410001c24400150a8a41500d814a00c0c18220000c3c0d558580e81210b00c0c6030b4480003d440740781480044c54070100d082c030451601004024010840920441018241010650f1a04510302d594681030f1604482c0c85406004075000c60f101e50001c000c1c03213418104407021a0074894150555070f00540c0030b100019030101d41d51017440205807100340c00c10078020f140203d40c1441e44a030340c2803c000c0321750036041c1a00061000500b074000c1c80b441854502c0942a25103820701a51424480e0b400b820707500c2c9190044a500c480c011120340f016500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 407364244 1250 407362994 407362999
    0xd062303071502031e0d0b040b06042c0109061805070c08030c070c0e0106090603140f180604030507020909011503030f030e0106080714060a0c2607052a 67
    0x9aa49801007150300707202d6841c903080850008000802c50f00c525a40d0b003100240c0c02464440e6113200c000385400807103c81d900140c5c82582012107000340c0360384150666007611084880721f15003650f601100f19501c6600c1a201c03021204060002a1001c0e02d50303c000101c41c5078242c000890b0912200321021a0b0007100c0b2840801d01000e18540030500307003000f4503444040c942c1d00c03624000194072480c1001255600c03106c2d040922000601950398401030050082c407160805000070a51651902c1202078010040e07005108001700041c0100111546005056104d0782074072400d00301414010035562000b40c00780c0c041c003541c02c04039040c00d20500c15000581d518101032070745107003166400c0b144e041d0040e180c20704140d100d03424203440076800e1152000070001c2c3c6008220320340c40c10325031480c1a007205413803910030882440814003540d007040d604c240d503592207210590420003003540301e015885100d13000a0600804181c1000300f010004841c60706003002001d10fa401324840d42d0200e60008007a5441c2e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 407365494 1250 407364244 407364253
    0x6090608010e0d140d0b060c0313080f0706090506090301140901090615080c04090309051503062403010b07061b080f0c040b180a120515090a08040621020d062303 71
    0x45617040c9903004207102e24000300030310b14210341400c1e040c0c07a54000000c0018071307985160f810000d80e8020050b510780001554003824002c0d142c2440a4800b107194464280a042d000440720440d40d800c0d40096858584860005540c0c1072202513103000f0018444212000d610340709480d103a0886102030801181d500300d000703200360520081480040d04c14088101c090094a19001c6903035500c40c5200c0c0903064000e541d058a80c9460010407050020141206250040c040b04c903048005c002012a4107507060b075182503640d262940340c040e0003012150000b0268807015460382d000603a01440302405090720a490281c0d81c1c490540f80340c4544100e202e108180c0e24104408802084140000041694000c050110b00c40d5105524000c003519003004640540015100941400c0d20842c125000240a401440915110380c4c03410202c5c802e5008280c28031070008000c00b2100b440010200d21044240025511040341941c440017804003405600703021036031041c3c0717191a0140e82c40110403c0f04002c1c01070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 407366744 1250 407365494 407365507
    0x6120106050d14090d0e040605090606071718031501140d051c080906180d0804151b140715050c0c060c07031b02030616020106090608010e0d14 63
    0x1610141e0111414030300103522821448200b108108040344904daa03240038084001d4500401440340c055101394074441c03880c02a040c08580c403540106940310b4410380d0034580e034941d5810164883e2014119041d4007a80014150400448540c0c4680211030160119000f02e0200d03540281285824003403959510581441c109207850681500c0c0c038141d000304140d0744aaa88207400512402901c441c40010500a406102d04c00368204250b580c40104000c2500521b219000c4298075181d4a11011080181000200b02844180750001c0700489100100b00000801c041b81c4080c4980116101c10105115004000e60300c0d82080840d84455440111084040341010103400240f102500340341c0349105c14021902858001c010080c0a5080d440c1110348500321480c00815030015080790040d500e801c101e810005881c006001074005008441842c18004204000c034010419507004c03a8181c0d04001c3d000810326030652000341c0621019054900c5441d100f0401d03a5002010100c40b045940200501c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 407367994 1250 407366744 407366747
    0x1908061f050a031d07140d030804030c06020405040903081906140d080408030d0920210c060d06080616090308070c030812070e01180909080c0102031f0506120106 71
    0x900c404121820f0005958920b11402219050a50380c0d0041e07690003184c092214400f26061445030b6441200c0c10402000d0710384c3c2c01060f0040c007605c0141809003030180301c010000e050301a14040e0002900400c5030b0282420010000802551807403060725000160703848031541c1c2c0c0540000c1e02c14220441d400680030600340031400c2c0005106032980c80d0144004030b48080c041c8014022442030442c085101c81d42820555400507800e029054012004c83c1189100d48501c2d6072070042c44896940030003985c0340718001500344400f960307603582e0000c00000c07a148403c1095008034151004001200c45a682d11950024025a8100c007000810200c210400024110100810f082c2e0700c90b4810100081e40c0303640d0f90300d0320340001d01c242031014107034020084400c1e40007454a14210b42403070070312a0801e41d00e03000c0c04410341c80d01903d0070f8a0340302c0c410381e02800100c9040701e07401c2c2098002155a460700708e00c68400c2010044422103a503904d20000251032034040b05441d60310541d115090126440d1410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 407369244 1250 407367994 407367997
    0x9010614130f060828150e010e0f030a080f010501050f071b03080a020606040603030504050f12031b0d080106050409180507030b0a0b300a081908061f05 67
    0x4000c060b500e5030031405120305103000d800028074290008020721410310600420703001c020b58828480c540200c60605c04a036081e0a1080c080a100500103011041a05464090008100203054610a808807403048800007c001d1903e40d60703564444003552036004000c1100002846407500051041c4203840070494054028490b661040340071400040340d00410683c4a016580b042c1c0700b000000c01e52032809074040c000243e014204803010003503c0d04594001c2c009001c3c2d80242806607050703c2e100b8402d903c0e403c0d01d480c02030105104603511546e02c204c1c0040d4030300c1b0322400c10b0b2040c003032005282c80307682c05040d590741131f617400b620707540d0401e400c15007148010301e802c2e00a0111044c002001c64045201401081d000d18028045481d561500b560f800064405a071281d60003001d407644903030358502103038095a944203501c02c0340c09803104620380300600d03103040d0100107000050000b540051a000409911880c00201c1d200c1003550b030388100c200654480000c44007603218400c010240c46541c410320 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 407370494 1250 407369244 407369269
    0x2030c040e0f16030204060e09060114030a0f0804050a0b120402011b0218040309050a060c11010e1201060501080609040f0311100207030302040e01090b030703150f09050102090909010614 82
    0x1012200c00b40c189501040c5401c0c900700054071800c0300820306009500303090184402400f1003801d07003211414030348440f40c3e41c1c2d001440b8000440e403041010005a64007400002c02054121403034030313031562040c208400e0640c45031103168815801003800280b40410541507505100e601c4a480a25036280d40055032807004c0c208442d010010200491001a92410103c1404c515803070034051a9182614029041c0b60301c98018034400c0c140e06c24200724045e400f04100445c0e55120b500c2c50b030704619101c01604c0d0015a02a456801006c440d040b0700380d00c005500160844400340c5e02c001c0d03d80c840c4024400039420544014108119402103000824003a04101e91410034030011644941c841c0c00000d009c0f85c01204040380000c1c0c001408201005c0c41d2650180036003840071080010100640000e80d41e8086480010f082c0d86101c885a0301d0002c09034131806d0300004038842030040c1d14103403601038000e41c00001414414400100801c03a6080305100310010f0300c0d4820f01420303164608001304014480d402 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 407371744 1250 407370494 407370521
    0x32001090b010b03040c050301111c0605101e0305060d0b06010207051f030b0a081c020c060d060e31020d080a081009110d0c0c02100f030b090402030c04 67
    0x1040400d0028846454240c000c00c140121540c80f410107141918603000c40da4011486a03052082c810080001c500072200318442150040700ca40708110000c00280c4860781c01940e0091000d404140c50a8002540c1140285400300d0303445000c40010003901281c0b01524800d401502540d11341380050541d03814290003002c1401250500c540d910000703110751152580f0001940c152000c47c2000503058000c108a900c0110b854898450510301c032035940d80303036040110000c05580307503643e09407074005c3c489801d1141d00a03001d666200d00841260001d0101d85c803032800c4a122100c005243c940740d8100006246204419400c500d540100c02088003041094040ea800a40000f80600040c3c080e0010191016180c030b40c0b0440e0b29000001c1c0341c8820f03290b40504c00c15401c200c2c0b2601e08440c03113000c66640070668900083ca860346000c0403a040e29006c08000e4000d040070307441592040d0010001500d060b12690700f400898240d80c00c0c0b119164050320300035055800410040841d140640010f03030340e080f95 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 407372994 1250 407371744 407371751
    0x301030c060201201b011a100903020f09060a1805041a060f12031c0b03010c05030c0301060f140307030506120a0b0a200a09080d0815011107150518030a032001 70
    0xc045ca01c2c2c2120b80b184904604243c400300301c1051800c055001c102071082c0703400e0524031036266402143d0b4241d00c4c017070320310322900b20100040e030560b5448026201500300c0c4882000c1d034124044801c0014003083e20140c500c041e14086912800350f280d0b084502c640780103880180c800d1000b200303000b0112050500500a4001808440b080c8064810201c030421203403900481c20903002c4090508481540b00441d04100c030810410404020450460381100c10728600204948d502400896103003c80320180d0700c0d48030300001401800da81c5900540d018a2007110305503502e4080c4071069070b88846070980207000a4540c000a030720309a8981c0949042c59100c0c102003180381c1a9000c5110359803102d0000ba005c11402c0c5021700103c1410003400e000441c4d14203050050b8103203841e22090101c0c10001c02030401c01030210324804100c09200c880d0090400500c00729220003030304009842e681042c0c3d00d21400c211007012251242c84c00143d19081030703401d0340300c1c82d14800b141c200440c1850700783d1303800d26043e40d00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 407374100 1106 407372994 407373037
    0x503010501140307020316080a030b0a050a0905090f0f06010303080a02030114130b061b0f0312010b0a0507020a260f0d0507050717030301030c06020120 67
    0x500b02c0255072aa95010422403540c4070300700a006400000000e0403040088400151165100030f44040c08501c0c000d00501000b0010ba105055210085200030040e01125500158112203140c09403100008088402403614048851010899100100420070306500c00d03085904880c0c01d800a500e194503000620014004280205102d0000e49261031460b4100d0341c44030071008005481d4584404c110102e1401c41030144442e11071745d0198112909000368040110f402c206210343c081c1e40716900b01404c03101d803600a03032600010b01000304000c030056503844d10070307070b00400d1441d9045030001c0e078a603d010301041c56036a1450b1154811481580d040c000130407075084000251800c103494048a04140e85089201e40c840280c402c0b1300c1080d000007400100096068902421070850805c3d0b50750803c900325590b0000c0381c050211103504031501c2625034001401000c135411225681100d = true := by decide +kernel

theorem cover : BRFrame.Cov 407194244 407374100 := by
  have h0 := BRFrame.cov_init 407194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 407194244 ≤ n) (h2 : n < 407374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
