-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2152
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:48:20.547872+00:00
-- url     : https://prove2.me/submissions/ac228aea-8a21-402a-bee8-3ca0648eb1ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 386870503 ≤ n < 387050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 386871753 1250 386870503 386870509
    0xa09150c200a0203100b1804080a030c02030f040305030301052d010806190e071e050901050304020409080d05011701090f0803060f030d02030301051305130311030d0f0f0b0102030415030506 83
    0xb80c015500202120342988030020600c0081c4040d00b078262250300c0d4020601061005401110310503504588081e0805100c0030301a0082c06080d1000d10460104026180d4803401007405007015500901c000d503120340c1004103101710b000307054000300c1203100c401405112217040342d6150444c0b10400c0c0780c54003241c1c44050214a02c3e0444080c540321200710420302150303510710442110b10a41143d951103c0b10075481d4070442a070b00c614050440002c20420104403075500600056801520140c00090880b0b050b0715428485d410003882d0400c0c041c0c42d500100400c1100c4600c00e065501040001c10421159540d0329241d96014080200800c20100000e0400d5503100d0030100c2000c0080c042c0c070780c00b10007000025120f910901419104190800c00328100824601c200c600c2072a070820404140022920203450254100700f100d0110b20007004134030790480f2035000b07081150f66140c2d4080b420a5102c41c1345000d0366076a190441c1194014002000038191104148070902410b0400140ae0f458030404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 386873003 1250 386871753 386871763
    0x240411011404120b150105030405151017010203070906020c0607020d020f0301050c0d0c0f170414010f0c03060503060c040605070809100c031205100603020c03120a09150c20 76
    0x4083e5052a8081d400b40600c5a0181d0b11910403034400f40c2410340480015545800107803005001c0ba4085140c2134114034107040700d02d80200601c0d0075151442ea55030411203054481d031003900340d965008001d204803140c100009070054001070003d0890b0842030404a0400d020341000a482a01c800c403040003035407908003041480180c080c0003406103181001d811065580300140e040500340c9010910340b16644100409040445203969503032600000010100f0300f19400307041034440510840700c503600c00c0c4091141107031100d0310311000304041503442c1001e0b04881641d44818001c1e0040360821030002408421034040da903480c24216161070090520b81014001e14204540044000b0602c003a0307550001e61941c03030a4429501c0c1d60280c110792084400b650016500c00e0304491810400384000c0c0d000750003a218100d140b2084a0400f43d03603403550782c17620310240c8031001402d80d00e00c500414800100f907042d03404002d40e1000d00468520790001800c201400625100e90328a5a02c0000b1118083c02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 386874253 1250 386873003 386873009
    0x60e030a021e1f02010203011e08030a260421032a0203041706040b01050d0203120307020a0606140a0f0f12021804150606020f060c03100b0408240411011404 69
    0xf060040c5008614080d000b94070030b0103512140c3c1c94400c0080c84102c103003178130f080035140808082d50420301c0b800700651303660b1000340400c5414a46035002c4071070380c015014842c4c41070340100e403101c00752030700e8281903042c070044070405008050406c1e8a80c40a01203146208544410401540440102e0504200d085028942105894a41061601740c641c000040d0803405070f1b0241c1070181c05642d03074100f040141404004000d42503000018034100300d4a21002070756001c10507006407400341010399511030071100c45812980f814013090703000c6081c1d403e00d900c95a000d40015241c0b03001c1542072100012401c240e074820068010506000d01003103460326188006502c42045141460381014035142c800c00c0803612451140c24500000018140d01c0050400100c0704080050156501da4030b1201001d58002840140e00355841e200000d42511144000c10061a032040504400400d80545580d00c40711207180401b013120345810310011130801c124001e801a800d080844051155050039010750160354 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 386875503 1250 386874253 386874289
    0xf010507170f1308010f0218090601050d0606050c100c021c02151306241404180302100b03010501030809041a03010e010c080a020a050412050a1b060e030a021e 70
    0x30680d15820700c5080f10780c400380d9803168000c5c01b5104021244d20101d00400c80c21400b4007040544a0103581402c03030b0001d40018041c0750607481c3c420b007030f010381c2c040d14495448040040c00010790040c910704280b0251540da65511000e00411560750b600a46d40c4e482d0302516022400d048110300c01481c002c0040b074a00c1c00840740030349a240b410380e942d010003410980701a2901d0382803141900041e011070b80ca80c0030103402d04180d0201c00381046d0b0500d004030045e02c0c246402a55a030400e82e081c20007060703030112991003a401042c11400344284001a40c540c2c61419009a05201c01840050900c1c42500c0c49a082130303d000032040b60b8005640301c1815184952078055181c50079008031404103400940d030005d41501c55011a40f2216400d0040344100f58000740014000e2209001d0b40c2090b0102094a6000c1e104455010129868072440f21104900d005211042d0000c00c004164010500340200c100407400780200d10026004030b0110294076640c0c072082c03504040700390300035951540810031640c411 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 386876753 1250 386875503 386875507
    0x51f0f05042a0e01120809061306091d1b12010312091406030a090c0918120201140403080a060305030c01020706050609040528020603100609050f010507170f 69
    0x1500b402d07002d140005015030000d01c100c01c010903010800c40350740740841d43d00c41c0582030640c1c640081e00b0300002c507645003143e030b0000400c8010621350710840941241c1e4052541c031407000c0d00e80f550140841800340d000002d1054503600b50f044a000704041107600032506400c00002c03d803094040c40192080002a04002d02e0040000c07040c0310160400300d15002d0540c4400490036100c50f58841c102003030705d80040e0310283c20400900e440d136484d004208070b14822103200d18490f40b03c051007002d58650201e9841e410300e0030b5007500240000110002e100880f01e0000f00002074150000705c204003001480681400702c0000480d0340419198411002541c00c807043e00d440c1e200c1205243d003c1d500c03174a03058400c14241400704190303151000700640200da11400620f60b5100102407100d2500040881e084100e586803180b0000d0f844680080d480340001e03101c1203003964200b00d80540f46806a401c45802003030b450b0494044e51f40c1040440721001e1300b0200c50715070700803c05241e0991340300314020b8460000300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 386878003 1250 386876753 386876761
    0x23270d03020705041505030c1504030b070f1b110f060f07050c100305060a06030c12020301031401050106080709170c1f141218100c020a0302060112051f0f05 69
    0x8040780000c10f4071000c07034061001c3c040e11409102110701c03078040c050f8542c210150f100054036101c90f0148100c4c0e03862840a06003950703529204190f070811229100401c0d020707400c80c00216401400900c4001007800c0c2000c40300c0c1c05d92100809110000ca5403405502507d690400301d9440754191180c41080749001c50b030b600003902d070264072035001d24003213401115042c0c40d45002c140240200c0d4412540503204079055440c045045002d416020021002e00200480c06403d076549400190301a5001e9424510341c40c0c107400000d821600705a2150342000b1050b0140000160311805a00c21501d0b22803c2c0d44036120049445810402c50322103036070703012000c442e183c43e14101044881c0c1d1140c0c1c507070f1584400c80300c82c150041c0007441110000341c62042c0200000b80a91115180303014080000c40468400400d103210300c10848154846010141c1e002d0881d402c02c041d8100b01c030034003414604128990303a0050740d554030307510301000000110980b40c07901002d104103503580c00754100450000091140d414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 386879253 1250 386878003 386878007
    0x16110d05040609050a050108070c0f0c1d0a05150d030314010e060a0f12030503090c091014010518060903030d02070b07111504110114040308030723270d03 68
    0x4800d228600100d015110f00040e507107003480c610b604440044c0c6882185656003c01100d040c4d10142c01101d804001359400008a8220a9260041c00007200200c800c109000d801400c81c0d600102030000b6a801d2000700b02d0440306624121058140655910240e0030b100e00e000d80145c0520354449000481e84c60000605095012900d4003c00d0180c41510056890f0070031041d100100b8010b03141415070b17401e50880020b1007a8010b40c3e00c40c07402c80036a40009900d40020340c0006055a55444140c441c41081c800292100c5006d00d0042003400c0c02490a9108619451220081006280305100206010f081130303c052041391801d809043c003c640c3c03407050f4900303541400415510880001c04103604401001000911003010820740b0b04183d581f0354031980e405000001c4420001d040040c0b0b1789100501010a50140010758802c0b024a500cbc0c0c505090002e001603c007880d1145000440000440c002d04080221003110b101254150301942c4d0030045041240d50441000341c0140c0496a041e05041e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 386880503 1250 386879253 386879257
    0x5040507170a3017190207140c03010b0d0c051201180c0e0a0c08060d05030405040e011a0a05090711011b0519030203011d0a0b0d0f050d0c080316110d05 67
    0x11800440100c04030030f6000084501e0a0307003500c0340a04501d0b8101140800300c036144503552000c5142009840c2c04036940e0740d100c1e41151103001d0081640141c00321120303490300b8080d8006102b0152007900c1d04901685400809031414402c550103015a41c80d540442c510a40081480401c01ca038680c0e04020703d0719100c2a580c4103407048500102c0000045540010039020344020f40c800380d591a8400e80360082000360142402c80c0c200d070f5502c0104000a202d40704c074007810440340404400042e03d2805031040d4031001c0c06e14070701a8450902558188855a0340301c00840c0c10098030b14001c0725006c01c951030305004210700848902507a01d07211400080c564420014403000103070000444061861110580c103901082c021132800344e641203480c00c2e0103a40020860383c00b00c0b44003400310b0b0001407000459041324407600c0036200c60002101e00300c00d0200420103c10a032000c1e01d89000000ca079501c6540045c00058074190102d1808800c2d882e54a00ca250214518131000b0706070340100c0760780d0002420507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 386881753 1250 386880503 386880563
    0x21f020a050607050406080411011806050d0e010612080706090b010b1b0109020604060e0d060501030f200a0501030c1808030426070603050606070c080106061205040507170a 76
    0x51182c400050040c504c5030098404540c1c640d22400f50075181d41c0e541c2603510080c1c0048504102566214014001c90103107000c00a1407181c03650340e6910180c0d4440700668036112541011030781400f00401008240030030700e2010580000234180c5400013403501d5000b410341c150f0003408002c600070011800b90340c0103009180d241c224011640d0040001c0075440d003640e815400c041c0d0700440500c0104002409003600800b405801051032403200da90b0395801088400a0304142c0301b10308480402c80c1005507a95050603100707048080c0b07c0e080700d120400a0400c60b114042e0078100f41c1c90713200400f02513015131050f842c5010410046c08100d501c40550f165280c200340300301d0120481d0000001d07603900c03c0510358200d40081002a18096007008010f5000d010007902198016004115840c04a1301c03680741d0740083c00c1c0c00c1d400071548500e0080001d04001401040c55000b07460241880005500000d641c005c56490a68841d00c2140014020381041d480c5c50000e81030200c4d00c1c000c4404003074075005c10010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 386883003 1250 386881753 386881763
    0x50f041419050102250b071101060807090204031101080c180402070209040308040203300309070807030b0f012103030c12021303020a2c060f0607030305040b01140d0807021f020a 78
    0xf12150344400a05c0d00000d0038007608081d01c14020a0fa180e2181240042040c4010300224441d07540e0340b980c81c9000500d51011408640c0410217200304050610032000301c0c9403d284c01d180b0b50400c205821213034031851400f0354001800c65040210380c2c54070340580f841e080d0010840481803500323081c041c151100880d8100d20a001e1605031920b40403101d04000892201258520500011000140301d103610260a8200300e100c2c489000411705410025600610f1144000d500181071101e40702300e048030181c000003031040c81c0d42000282600c07001d01c1001165014030f000b1581503c0c948017070f81d200000904166095000040c1c01e900c1c240080e003601c0c1242e2003a40c44c60000c0f1360f01d20034101c01801d00c0f0824400004603090050844040b51581a0404130040030360154150f03902c00100035502c00442240400c0e243c0302000709002e024400b40d40102400ba02940d4848860400900607424014009000000c081500300075034403110304600c0407541010454400302032105021f5511880040c084036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 386884253 1250 386883003 386883037
    0x50a032306070f05210103031706030106061202090f0402030a0608070503060601020304060f02030c031c0e010c140d0b060c030403021c0519020402070c2403050f041419050102 77
    0xc5031010000301c00c0e20501207070f81d41074500500c2c0c403c2124035500111102d07040c0c06034140350603400c2413030300d6916000718801d440f6181e52503c28070030030003482001005544664986642008065004041101d0f030791121900141c2e100280300009036041c0c0c66400d1541c2191010040004108043c0e00110564950740d045845681c1e849040559922048982d14010b80080c0f1003004014040c10b0142d54031021401900d08220100b1042481d41c3c218601d003840701906244030501550503880740b00c01c4071400030001d0062964109020f8540107034101c140040308000076a01c0b00c080c800c2d61203c0c41200000708031503079409000b040e2640e40c1c0c00c0707404240d10070000f40150980640e05000031101c1030b54024050316900000041d0b00d000003d54401c180e070810303003c200c00707400940041300300e034081c0000041c3c1c0c2c0014420300106101a0000104050606d407908050007981503024215550195104194440544850200508000d0340d0b003501450089031030002820800c041d005801031aa0f0207003402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 386885503 1250 386884253 386884313
    0x30c0c0a080c10180807050708100603020906010503040c1e0305070920130302040207170706061403150a0f090c0608061c0201120e07120830070e010207050a03 70
    0x4030488140d4484200340e5a050320300800005d052801500d03099000e2829070303412550b62844075041c1030501040c9000140e0796501441140f80001e2890740000007840c107035066160076614001866198068040c4c1014101c4900c6803801d00b441c01003020f15072060036241d08507550345402c0007074540000c01c42d031814500d1041c1c1810500800c140c0d1003030940001320010440c0386400340002980440000e03600e4000b20f540f500203c162401c014400c0521540000510a2408420310001601958458403e8001003d941800450074191a030881c1c900d4000158036140090000300370408054014a20720140d54002010794120002900c83c25059440a00600540400c00d4610200101c0280801e018403c00204600d190340300e08100c0e4540c02c03c460340c4030380314a100d51000003110b2040300c80c0314001504110314031440b03110060445129203000b0401000d070380c0d81100c481004280501304040d010101441d40e00c01c00c148001820f0150001c0300c1e42d9164240403042c013140003542030442c0c1c0d00210385 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 386886753 1250 386885503 386885533
    0x303011a0c0d080601020a0819030b1507020114070605070216060906050a0507060b120f01140603060103030f1e030605030c0a0302300d0f080f100b030c0c0a080c 71
    0xe81d55504050003034584211003440984040340c0113000c075411445015001c800042c00b400007080640520141044510b00d04040281a81c00c1d100000303002d448109052440500084161034020340e09081020258081d041c1084c0a03000e01603003e030029081c1001d0024180d00451414001001e02000c6400d007600d0740019200da0300144501c50000740b003004031686040c4600040e08034644120000f007140140d072000101c1501d02c880380c003961500b02c12903400b456003091041c04a0140c5130600c81109d4a0b103c0006130320748205100c050140301504a070100303e5840741041c50061070345107622030956040b40c103008008010300c0c0512400fa10a45481180610b0946040b80450b58000c1030008112088601c00002e500701005410492002031000c1000700c2d0f06219800c003401d040d40da195003004000b07a0041201001500c816002550f0005010705c5920a00c80e0105682503030b982181d590702c44405085052140400801d024010152028100f111840051054100190403148040d03604198 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 386888003 1250 386886753 386886757
    0x80d0801030b151c0309091409030301030b090f030a030b0a051806040216050f0109031701031703190c090806160816051303060b04050a050f060d140f0303011a 70
    0x2000d00218510000205100c1c100081900070f1034020f842a6a61880250441a211206101140802c038101d40621a01c2035511a203404510307070b0542500035041c007445440d107074801030001500d041e4440001642900d010429030071107908901c200da684400100c00100140442032020b803040903060703800a05460311450030784000f41e442801c2d03410707911101d00f0800294045041204890004a0480081401440940200071007a4004030b100c0f4154500101345c0981d94012900b810f108800520214420b9141c81810f9a14062856a030b07440384c52240709030440514010300c80038200312005800c103500083d408111140d00e011035005403034910041c04180010140600001e404100081944182c071070124411281c0f81410b900d4040e011058014030101ea4109550304ca403260020405030410f4420030b0b1307011001c203074200010700b0040710b07074100c0801c0944400e00c1500702801035018020300c0c0c0d5503070240c01da0003411542c5616440d01c141c1c0d03d0390024810b4034207c02000c4401d1a0008181d02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 386889253 1250 386888003 386888009
    0x110a0b070c12030f110c03030c070e0115050313031e030902091617180106060206040510050c0304030305040c270f0b06120c0c010c0e0f0a0e01170f030703030204080d0801 75
    0x21a400e1403413410a04039040001401e5075485882001c0c403111444c0c40c00d02c000c143e03410b80304010f81486400c00034180c0111b0320607441a0003000c00c620340350302030b240d1103405e0b41d130464000c0c8144148446142011981c040e0a10801c2c07000b01009410076118a4259118170505031080d1851140c0b170340e40481080400c0c52050301d4001107100c00f14643d001007071034a900c550090300f9003074100108044019240c02c4400c0c641102016900010500062040c20803050b021400c800800384014600041d205d066404054030050500d0344503c0858208100940014042e250350171600c0c01d0b441400340440c804030005407580d090ba0313140420fa0000040a4007618040074000340c4002d10f80101c024400c15421310080c942c0032182d0090009648080d004e0042405503001680c9000c01d604000c010440c0351540c1c03501c00380c4184c0d00450108511081000c40a044a9a030404a01ca0140c007003503a42c104681c0148403003c2d404005644030070185c050780904240e4141c10203c44026500c26001d4600c001c01780 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 386890503 1250 386889253 386889257
    0x60f040b0609060904090515041704230f030a03030c0e0f060a0c03020f010c0c120f1409151201090605060705061614070b010812040303090e04110a0b070c1203 70
    0xc2c0320740d03007010b40050402c040098800908280c4a840b4681030032480503680004080c0e07101800148020a620f8102807120083d0b80ca10f0246062003401d007000c500803201d0101540344000900594030240103101009024084e100d07191f849150040040151240c810086030012840c00700310309100e02030005950019201c0c0d440d10108640642e078582804408504502c2484a00020b02c1401c0c06101c0c01c041c0eaa4840340301d44115440c2050f860400d1080307280c100405d54070801c248030b6004003883c07050300e40d80680c4c030b6542c040700e0040780c040c0d4600c0c034140c00c1604000980f1601c00c0d0070521000d040780c110600402140380c50b03004001c818030074908042c1259000c1d2000c90710b007010481216400c10018100504000c0728003066205076003082c203081d5214609c08004000061050103500c16081c20703204058a481c0c1541d42c0a8400216801502c89036481a8006020000310110b6080004001040c8101096a03005108800d42c405070040320304214588000541079005403469818513419 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 386891753 1250 386890503 386890507
    0xa060e0709050d0f02190e150f090412020f15061903021815090c0307030b091308031e0c040303030e01020f121b0f0c060c03010602030a08090102041d060f040b06 71
    0x544c480d20381031054514166841011030000801c40c040c4401e81d031004002035000c4034100c0c6410156001c1400200c2131246c051002c443e0b540440d03a441c0c13821103622130343c002c0041c0007000c2c2c0c41c0030491800d82e08890344e9800b8407075020444090000c54401d984900340842d0241d800e80c2c0200c00407580c4c6102840001c0d04602849100300c0d0300d100c99105960320060324021902540d1248001a00f1541c0a171088800414008140131205a15020b900406a1f0a4410a00c00d0911071000700342c04130302040c0500002070100c0822418220400400d8070711031407442c00390090030158000c0305581d1061008401103881c0100c00300c880d9106000740c44048d031507010540d003800419510010035460081407034400c21488010301c4110b6086201500c1900e2a0355500c0762100125403a9610b0000068101000c0143c14001001110b03130020446407240c24138600321010f51110301001d4064040c0341c010b406c0383c2901c0031590b59141c82c2e03021018460f2500712440c81ca5502005c040c801107640c0010469000081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 386893003 1250 386891753 386891779
    0x50613080f0708090319020414040b1909050a0b0f0114060301030303091e06020405032b0e011b0f03030506010f0903080f0f0f0a111c23030a060e070905 67
    0x100c07006002201d015907a018608001100000d044c003004000c00d1043c00c4d26241c140d01981414801c2059a6090401440d924142601d400380c110320000c1c030003008050705111144400301d60790003043c80d41d5441000c90324000400d240c0403800100880da1100c022411000000d0102c001901464031010b001d4907491a503421500d0883c0034000000c02a296601c00d81da403401c04005007416280202e008110050304d9505010815003480240c2c518000300250000c5550f0201154005103a0400010304020842504803401641d01040307010b02580c9640b00509108244681c01981002a85c03107984c08200c6a680c100040d99480c00300d240007000242890814400034480c00700515554413003406050504500140038100c0d580605505054600d0124100682c82e4000301e4010864107501e000c2c00440502c81c000b80742883d5032400303040801a4210b84603414423504210313403030301d6031071012031ba40d80c0c2c03070140c1e0f035100540702d0303031003908146a94240081d00f440c1c4604146c1090300c0d0300400d55011110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 386894253 1250 386893003 386893027
    0xc030606070510090615301a0a0518150919030e030705040501180f020714010c02070602030c0d05030a02220801051302100507140709060305061308 65
    0x401041150003000400074800442c00030010141489030141000c0b0f00e5040720b1802e001036440c1c592010040401d2240184900054480030007011041e042d005d03102d9071164881051036044d0402e01030300450702640b08907490000007400f2032203015904001c0c00b40da01e4116032940040703401d1000c0402c94225040d4660000c0880f40c0ca240c0125089040b078800303110380c1017a5000c84a8a58044020a11400402001d0705090041c0b1f00101021181003080f9890520f03419200b240e406071f4109040d9443c2c0d0315000c140d00550544840c9034014804444000034400c0c20360003072191a0b116000751041d0304002641501c00411201d149500c0e0000d80302101d44d201c0c054030180c0026085425442d001c3c0701c0a00c0b5060a0f0a51a009182d440d000d000c0c82c0385803082480c00c43d0006400303c143c415140e44100c015072100d200b20f0349010404d1070001d5a820b494106400c020a0400d1541d205020b40d0b2000a042006600542c1c192801501a10091b4813202d0082c1a11000c0c00c6000344200b200b4420000056 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 386895503 1250 386894253 386894257
    0x13051303090b090901150309052d060907180207060606050d0f050103050d031503020907090e0c070c060809010f0e030310050d021f0c06020304060606031d070b030a020c070803031803040e0c 83
    0x29420b06011612500a584060519520a1856149401c9415000c0001d0940011042a0500704000d0152f900301801c0c00d40d29070440e4001c843d48105009031808000e0000e5040341c409a401030340808c001500c64100411130741c030a8017400320480c00c1c15405032071038a035441141d040b2a4010010602940c403a030050b40a4421008240b4031118035610020150312140c5000f48140c0283e580c502c1c0503824204202107071075006c2d1130003c40001c14091000003801051240301990002d00f41030150b035440c0b01140b80942211142e00c0e80090078440c111895610000140d8041e640c3c3d40a440c1c90f042e1101c052100181c030316030b800380d808050320100f1103120b4080302d400c00030158680f5005103d005d0305e440b00303016a8801d43c0c0840701c45a50b00d0b02080b031954184180e00692000b00c60040381c1d26194080944c0e151140e008034117070703c100040841c00459040c0d049034090020502a980301e5941c850381c064032604116615103426420740700040c040d50b008000ca9041d01d42610303148446407102c00e0419125 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 386896753 1250 386895503 386895539
    0x18060c02010e01360506030c09120703050304030803041e0f06180b0a0509011415011407021f030608070306050603070b0309060a0221090f0c060315040b13051303090b090901 76
    0x116132000000c50541c039003000542c840c4040c0200240d644111400b405100700042d0b003042102c1d00136080600000e84d0103c01c40301103d4118040544036140c42c205403980089814400b8107000c66064244c0c02c110b8a030b8888501540030700020070625440304c50b24140e0100c084030080060840400150a007851a4002500110500d0000500040c0d9030b0340802116400c0d120f032030840b035440660444641c0e0004900c091138141c2c2110030f0038004141c6c0401d40901c00c81c4116600d103124440c071071000ca4440d9200c40f00038040d460444410135581c0c02c104005042c180e50150280c058414082020081d0404903401011620000c0c42d2942d00c0c00030303201c004d411981c0b07445002c0035000168500e80060f141009d025078808805004486030542e0300502c0c0550710074881e03009160038001c05c00150004a1600d0080d04141c90101e180706294000503140361050000d00c409514141c00e01c100c4501541c0c40031000b42c07003a03c4510300d05d6225002096103001d00482a81c2c84000900103102c01b88003d1810158 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 386898003 1250 386896753 386896847
    0x3030c1b0a080304081206010c0b0708130b011206060b040303021905030403080f030108011b12090302030706020d140a060803040911120106030b0118080604080a18060c02010e01 78
    0x40c076690751422010340c000d41d42a81d402030045540148094881c2d04030345c010b0717001d0910203900b048070750f2544120400203140b141444603110019100450310511214084d51102e1400074035078603002c8510000b14550740585030946040302c04036a1304040e400b2141540d81540092001ca204094020344c1b000001c0011603850005000000008000d1009010312002000800d91a0f40c105441d1a00310b801c019041c05d25034004259907011540c000c0c400d80d4507400801c0c0c0118481c0911704080e461440303001ea000340140e100080f00c0038000203070b41c003141c181c145003d80c16102d40c480c445e044040e280c06002c0d901207600104401c00035088140e0003e942404100c20203824141e2201443c1a064801d0b030040012a803a00300c862a20341e4445d5010340c600301040c031100c0e14141081c1c61159200b034014002811003100150503030829001c2c803440c8824454100c1603000c0d85841e5000100002442d6908038040340d4801e644000ca98000c6110440510204000500104881d1907a584620ba8101e403445 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 386899253 1250 386898003 386898013
    0xd0f0e01030e030d051f0605300a0c0302122e06080f060d02130e102a020a0209151011060f07030e071d01140a15030605040c0f1103030c1b 61
    0x510500c1c0c20b00130b08002c0c10240c5449482d4a200140f5504102d01c1d1051a02211280c4401d00e0704080080380b02c40d00b0810740f00e80090542ea482f00203800a10480c00c5240700050350000300041d107420b080d02d2503101e160700885c060510304019614090030311a80100404540c4000005003142540544103510180003406080c040c94641c0108040048488404031059110314055000c0c1c40d0810680c0c1c030988036480100010004141e12140e650400e000d180a8540e0310040b04481a00c00c00807040c00d1a0010210021420401c0d6260b410b98000c0c00160701440400c030817031003040d000701d0621408180c660081c00066494a030900c1d0800401030156051654030802450001e0042000c00e019155065200851034014580004a0034050340080d10415104a00c4000f589402c0603a804131400341030141542c02402030207601508081c0c020b00e42161400014162440e80b065605040b40555102c2c0042510320141054403884211002c10302013204001c0340102001c2600b48104036045241600c4c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 386900503 1250 386899253 386899291
    0x20103060b0d0c03050610020c010c0510110a0807081303210203010b0909131a04140d050403020418200d14010605150a120203090307050d0f0e01030e030d05 69
    0x216802980041030010f6072641e0760b5040640511500e50048000c803001018028a144029554551003aa075410404043c507020b040040401241082e101140c406105010044103001c4081c0c018408c0320300000c9411000c01d00060207240c085001d00070a080c1c099801b810780c1c4003610800500422681c4500304115403c140200c01d202547c007070048003e506580302000c100b04000d2510260080780f0021541250f800016803602c00b80080c403401b0004801c0c952303240c1c1040d6420030b0f414034a9500c2805604001d01016a1100040082d60301c2102c0410100c062810102c0b401e580400005200e010fa0400901e400310002c410040f48072002405910044080c1e901d8a0b411180d0100586081e9181c60082c0802d2078038012000141070b03800c0c030543c18000308810081460303513040220f02c61700d41e0000206400304401e008503061a5001011208401004600100542c0d941000d00b40000c00411034031080751311a024130750154801310300844c2001071040305207004000140c03c3d11501e01b55440d40e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 386901753 1250 386900503 386900519
    0xa09030c0f0b0618191d030408160b03090a0b0a020c07090501030b0717070e0f04020a02071e06080402040b010e031507090608061c08040b07060b1305070c0f02010306 73
    0x1044640b48900e140032800d0511500f800542502e0103050700c8040d0081c004c01500300d4004103100004058601e0106082c6801c400170020715640b00700841c1c980c00300260200c0ca0340d100180301c54145059403480003006540318103020250009031021541900500801404200000ca940ea048000c54400503d4580311156407032900d200782e030020907000d4030f400040082c003032504041903000d03406003040209020b48851681c0c0840008045105022030014441030702c0e110700c0c0031054101806002195138142001020756548100d10070920740d0702054548000001c40300040c1d60448103d521420b0749900e8079030820010f802e5401c40181008800811140659410065104070710070069001c1c001e03041031500240301110303640005007032010340400e1000c140c440103c3c04002c4200c5550918600c6200e103000c68242c03040368080c61921001281c0c0320244402c552114040040449442070350191210030f02c802d6030011280c90b00400d86003200007000c50024400c0300750070303803051400080e425224942 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 386903003 1250 386901753 386901773
    0x5060f0d06050a20120c1c050603060105010f020d083c090a030e0108090a0b0118060509040305090105030405010e0a080d0c030e0c0112060b0f070c0f06080a09030c 72
    0x415100c1c2a16007061250402ca180700c0e240007401464480800164141c103401120303c500d0109403134120101001454040702e5200b51090b000700841995510300c80c414180010344000d44146100c2e0040c1c40000a40350b00401901c52462515005032813201f4800005842e00100103212018008032000b006812075400484040141c0302518184448149000116108c0d10020001022944007104050119401c9241c4101c80d1400346054912940c035000260b08100603500004c0031100c0d14000403964200260742d40c840302c1e4030752008015556540003040300c9d1210907240500401c40401505540d035106800850b80503000b140086244001d0400c46032600700a41000c0d5048140482e0740440c0c20440d0244030040d40103031400344a0058252132440d2101422040c0f5418852860f03000e4900300c29581000d4000c0c03200300c04a684800100361201c41541c0812000c44064100c2c11010800c0000e00c0d01a206580c3d407991950095076911a03440c0c01401c058800780c042c42205040c0c24000384038010303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 386904253 1250 386903003 386903029
    0x1a0c0c0406080307050d0e0d08070f050f0f0d17060603040c21030908031306030507021504050309120312061c0f0609260d0c033903180605060f 63
    0x40d540d513103a030b0901c1030900c0200e038850300070807983c1e40c401802581d81c0c3c001200c0701c50300301c00020740d125460b10f045c008a00440d01e0090150003002480c1c500c026010032621002c5110100b036a030601c00d4003804175004050000280c58030051300d004114181004800740d41c0c003074030a003401c000d00c0d07880c7c6d01c80c5900c81c2c420030b0407103400201d008024020103510105850003021000000c5040c010b8121611504103c00e001d91800c15a8480000d06658820014544081040103030000d00781094244580c8030b500096405000d80315001091885c880000121030b0402e0707161641c160075460700b104000312090a030101c44040e0b88820311381008102c00c80700d44c889045c07003894000341c0c02c0d02c60715045d0003900040000003400254081c2c252800d04001d0111503403608040b8001a038a141d81105074020701511821012503a0210420f480202440120f1001c071402c595845009011003c012003d03609400b240c02940100011400002491030700201d40100b801011700501055120100d03040030380c019 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 386905503 1250 386904253 386904269
    0x9050f073504050a150228170703180606030212030a23190203070606090b010516060212010e0709050910120309050909031b0606090610090305010203240a1a0c0c0406 73
    0xd518098441c140d07010302500c3c20000b450190290304180c000d00503403d40f081c0d000e5900f480000141d041d41c0309503c154804ad1460320701c2c00b2900394506202000300037602040f40919840c1400109080c000419a440101255615003000001e00d00b480000e81da030403110648401c0038059103c03078052007502e034003140c1081c0e8019a1181114181082030b01c650b83c3c402d42802d45805410007c1ea68080e00321030000c2ca4440c510141c1d003c851903d40c0081c82082005941e081d0580d002080094031405080e00402940e9540e06d035003034581013048140c000c2038548035540100001c0421114605a401010740c030b01078102039050955420110300030304401c841c00c42268200003101041030200100b4583d500035020018a058500800400d17035040c405011207214100043e5454405403181c11000060765001c0c0084d503d0f401e14891199072a02c99581ca40741c03151444040b1000341c2801c11007482200c0501250700d08200f0a60b141c01107170392200c0c8d10158140034641d41e5a41c2070315a40a040004c00b0f0712 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 386906753 1250 386905503 386905507
    0x7020409060b19030510150807030b060111010b0303040e040f12090801060605041419030602071b150c03050904090506040c08060601080907051909050f073504050a1502 74
    0x8408010310f40a1803070940143e43c194600c1030012801c0080d40004c0c1500d10040042d501c4104031501400703140942c8000b0b098450b5140c0407003004400854940221420707207844440880d143c2100382640e403124111a0554014002000b40f000c2e040003094100340681c581013200503047e201c4501c00080b001c450800f091200c10f040110200900c203060007071415240890400b81000c1550114071648400507100301c80c0c1c40c00d0103002800c8402c82c01e004641c4160115a121210718110b00284440e070721842d521929100d0000e00d10000080342c0c2c82c81c3c40d8940d103035008218240d40c207442035000320340030741d030030550f02c0d44001c00241040003098000ea00034410728031139130700d001d40c15854100028102410040260188040e400c00020210306840048544040704603c0e41c1111140507620750001045a085c01c00303001081085088480c00380b00f8541c1c030b0940c01c15169400c41c0b099a89400640d003020348107111200110180e8500c0c40d0014426021b4880410385906c4018110a0b104440c165460740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 386908003 1250 386906753 386906771
    0x903090303080907050a030f05160f060e12030a030509030c0706121b021005090102090d0602070b0603210c10020c1b090609041e1209081011040b0f0702040906 70
    0xb01216803040300c410007010002d060101041d10030b410780c80020700e4818580745d50b004000301402544a0b169210b40c08551641d80d03900d620341065118482c04e00800c0e040c21014501d810704069400402c140000290700c2e012030380305c003100145401001d507400c2c0c0c0010b0101c500071880a014000c010007907607448620540150589004a900070f0700b4210007140450400d00c1c015401182c010000b0040d01c40010302c698900140601902c54460764036444038907148c800c020451154050200c1501502801240d0b0341c414041c96654080e44011071000715025000405110f50103004113094880c400a0f100110804648001a0f80099a040780f054000024105840c0012507000c2d00144040340c070340103141031641c0810b0440c0d1000e0000f510106d101030750040d060000d804209140da038071056198001c1c1e0b145400074003a888a0040507030750300a82d0183d9120040307a004070341d540107401402d2840c5c00d24209501320b00e5030101c0040d0502c0700b01400040050790350f5228611805004580c00700704001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 386909253 1250 386908003 386908007
    0x27060a09150501320c07050306040b09010e010606021f020c0d20010b10200616110705030c0108040f0609110901050103020c100b0a03140f0601050d030816030204090903090303 77
    0x20818104044484a80340542100c2c4940742c0704c0b0704c4141680c1429030f5040030b0440242801526040f9540501c900000e000c1040680c02c0030b02d1060a00400030000c80c4000441d05003a200c04e48641d00040c1d111050311402102c1400c1003100d40e1003011401403030410070b0003440d820010710005290126050041c40701e078030401348134071401d02d203950402004100e001c0800100e501000b901c1010812601d62081240240f200c01d0baa03903c01100001c482817440d00c802c5010b11a40e1811440340040c030004500b50003428006900410b5a1f4020301411241c0d10580044032940002802071b9100b1900000000125600307104145441d40601c0b00340c0c58001e0a201480391007030040c2e01403030405204210b40b40001c8008680940058070000000c6506e101e41760000d21510b125410103400b110807404a806c42c80383c0019404031401200007504c6050307070307074004010140b80340150140100340420006545403140407810b032446122408d0041c141900c402640d8120b903442c01040b03021850150f0140f081c19 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 386910503 1250 386909253 386909267
    0xf04020c1005090c101706060403020d060e16030b0408130e0103031e0e0918210c07050a030503040605131502030711150906091f08011427060a09150501 67
    0x1004c02d4520741d0071041145401450304403650740c0b9004a010000108440390b0710304045500840d0010302c58504045a41400402041d00720741610080c40751401e1a40000070403032190302104d40100c3d00c0070795031b5240e0701c4841d5070f9400840381c801911421080402c44401d0406494061070007981da01d5a0078180c98114918840d410101e2001e11018405a010380d030740e00301030b46500c5000305184001d003900c250142850407107011f490748039100c40303a642122625000c8001e488181c0c0382d2001c071040780740d981091103002a4940000b611582040100f840030600400090020a44e44046100842c2c0d66100c0c01104450103100e00700180c01c0040d0503010701c07002286041d00004120b42c1d45c50980b0801408450a205200465004242c040340d007420640c1c85001c0d485001750754044030306000c905580010820340c0240a81e44c2007402e03001a4150324241107400318195401074031440d000e10400c480c0d44401e45030003004907034010011100403942407014000c1c6004035414030380039081c00c2d08000000d0868 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 386911753 1250 386910503 386910523
    0x602070602100b0d020f03150a02120c04050d03051b0d0c03080612031602041103010e0f01140904031d100e040606020a051209060c1603140303070e0f04020c100509 72
    0x40c60038580c0f50a42c030b80c1e6011800540c1c581c11281e500303800804901003818130074001c2e400c0c1440103c010420002140329001001c48018508400000d9695804070700d0300b07405203018080e0000d0f603144005002038080c10040101c0b0401803940440c03c0314a1207080e1400c80440d4020b00020024a0510101034218800640281d022103550307600304240301000d40d9078090080c0f01020060210b1000c4159151380d808101c812500401040c0c1d29a150034002c05141c81c00c0e00d0f910000c850035000001c1141d00c0720740030200f001e0010900b08283d21251030856000d4817244c6002102c280c1c143c803107401940c40c2400840501c0540c1c8514148440c501d0800c011030724954048001d542107921080c1c00a000400c0c980d04801e07078040c1c01e903100c12052000c9080b502441d100786900341b00e101d800c4c28404840203060000c0380c1c403c26000d42101c0007881c80c907489000542c0c000d004240e6140c00c030013441c41c1140b40c003089240040c000500700285d02d10190b280002d5002450103d541c0e070005e1200402e4140031038800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 386913003 1250 386911753 386911783
    0x1b15060906130c091701020a0207060215130c09020d050405190c0e0c040506070f110d0803070c142d03030103120c020312030c032502030a050d0204030501060602070602 74
    0xa2440c2003400b0410039030544000e940b01903540c160060718540560002e00203440588491074400004250b0305000358090300301100548510080005c03803074400504006070030800c1242035610303251440c100180350b00800040314801d601a002059100d050720240942c4c002010340403403181001e0070a40e050022415a401d58448101a0b080201c1c01d00403410040f1511040a41e4503680d0300984140c0d01c1c011358021a5000070005840c03030500000c02c55401c42e2a0140003151440c005c1d0340e081100d0382582c01c1c0c0c01410700c0e10900c001032403540550b280b0480c03940900704035404007107001d48442c01c1030041d03400c2d0195030b400314130007a02c0010540510700d02d00000100451855041d03480d2601200c50602c3e000040008030910750046490a229022102052a118503200d0034210070407859900308540c12854402d141018071600c0b98055503184032410340e41c002e1031506046180450340d5a102c842c0162101c3d8080000100007502440385030028042039001d030000364102a8028280030801440c1c0344 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 386914253 1250 386913003 386913019
    0x100806090c0f03010902211506010c120905060f0a03060905070c12020a120908010f11180d02060c03040602060c07110111011506050a020c01020604050a030309081b1506 74
    0x2948000041e924040020032181ca550900307441000a000d4018254000d41042ca5001c4240f44c203000354484045124040b0191002e02d41e007014005102a001c964131400242c0a101c0d00000c20041d070555201402c042c0780450040c0c0d00c03080410ba103640550909200424002071601080390b051040b94050011114144202d0402401c0180740c0142e50714054212039082114244290081219a882c96400034441c1d80c0d24a0140018242000d54822010203500b8001e00c1400010b041c400c000e420b040440e100c0e814101005e80b00c1c10003500c280f10f01c0e40c20008405243d0f0141c1e07505009401892220401103581e581000340c001d00b80036001d07042d05a03450f030902407600001d00b10303400c80066171000c0c83c24003006201e4030a200c0c00b51506410340803200001803070126130207038020000d00000d00c540e02260021030218004a1707484c041104c01600982105d801540064460b03040304080700c0c0a8003010342041500340e07500d141d200c1d0190342e46549034030a940c80c006c10b0700200362481d8013500c2140c2e071074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 386915503 1250 386914253 386914261
    0x617060a0504020f1903060609050306160e040b04020c07031b08030a050a1b05010905061b041802040f080604020429040b06221a09010f0c0501140a05100806 69
    0xa03a9a00050003018415030b00404c07404010703802c0b001a00c3c44612164800140d4003170456002d00240700501400f0005900c138200420f01e4240002c8003030040b0380d00324141c2c44014000c1800c0303c0c503040b22401030f540035844200248180e510381c0003909190000801402025265260100300340050040402c051007440404011008011094034860300b00303414290399402c6032503801c0b21001041d0b00c2e8405104400801c0320280001548403100301e512070400c8800c1c9407161301d4180001d12100b041d20201410402c030a0000b01c1881000080c0c4080c001805400d15489000f032182011403600b1411030703607000030308000561525008000c1d0441300c17200714845c07410318490b20b000101070000c6840c3c091a1910b0b84014140ca8000072108005e52009503006410110f40310708206010364424080c1c00340b0498400010404c41008648500b80140c64a50030903801c86001d4406640b0804c0688465503642c0c101c2043d61400c120182c1300d1218071030006803900e07001c13100340d91515141c1c00c000500d900400c100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 386916753 1250 386915503 386915509
    0x13090b0102150c090904141213050d05190503030f0a020f0301060c030e030607051b030a090302130e070905090d09150c08070507060e031c021e0c040510061706 70
    0x10484203004001c0942d040e0752201c1030341c4140c3c0b04e13450090b500600b20b00204020300545040c0555401c0800c0141d5500c4a003078104400e490280446101248100040400041c0b81104054000718416400d07581480d0288034040c0da103964607001a1240d030000020810420803151003e030380700b071500c0021400c14101019400580c00140034003000c2c003180c4503001c014180940c94501200703900404032042c901d440440100550040140140c01d014a41421444e0f1000401a80c940602907652074038410b141da001c01071012100301c410048503a5030003a081c1d425405104000103040a484041541e0600c007281c0c030700d0640503c104070308215200d5011302c050180a003c195241840d45004a4030b038030241001e42c1c0b1807207504c01c002e00c7d910403400000f4640d0b800415160610b0f8007102580c2c143c00d06c88030710b40707a400b02c0d072003842d40182c0192410402188414075404041c50164080b240310300c1d060008281152000d81d0510b02d43c502c4014104541c990118407038401d207040c148400d0f00c82c200b00d408 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 386918003 1250 386916753 386916763
    0x40f0c0e07020d11011b020309030d09120602160501020414010e030a0b060906131a120a051518060f180f060c07020f090406050a050a020405010e0f0406080f010213090b0102 76
    0x803e0100041d403091045400c009404c481503005400000000302c101000000e0754a60000c10043e0003400f03040c4010480a00616000084035105100b81107a0b00d51075441c48025030000c4031500080c8000c04015000c5039003407001d00080c10b44041d101360b45040402c00980b09981841d8402c0c800d82c0284410340c009080403c5c106d401c140203541c52140d40c0ca07841c3c001013081085d021405c4c40d292030314410a0565000c0540702071340b40c0050b03503419000c01c420b01806032507000032000900309510110250018541400400c1d50200f000350799011002d40285000e070030404140c0d00440c0d68104801800b55501c01100c0d13450341c0e00c49801c02000c500881c40c100130307114040105450751000e03010803c1c070195110004460703442d40c40101070706074501d06840d001004110aa8000c0421494000090f0314403401d4421602a510141c41d43c0080000702402c02100910121082d80c20548502001845c45000c000550151250034005611880d8032418040d0402042d8402440039040c00c0400c0105d90300405e07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 386919253 1250 386918003 386918023
    0x5160b0301030209310c080f1c1e0c0305040b1605060a0515090901020409020c0708070b030c04030605100801021b061b0304080d0605130c0e09040206040902071703040f0c0e0702 78
    0x410f004814124101500b00d01b543c0d600c41c1c005401000b2112081c0315012501f1035404240105041900540060841c1d56001e10f90660060360744500d400d42d002c5000f40d02d03210041e4401c0c6031080c84c041d100c81c001005070b004050440b1851801c1015030080200601c10382d60f019155842c2003003c1d152a009441d10054035101d4140644094800b0414001e0290101c0b8090301922105640e1030704059056503544e600340c82250b04a0083c0f840c0448c6908442c01228014203618030254106400c5440e03c03001010040e042d03100b10004c040001815500a001410381c03202124029140040c60383c840500f0440010400000034a149460b0f149038810f00050301e030407a4005421640b074140f00c41080c3c0003405150003041d40504500b0b2100510507280d00401e885020320307035a02c0703440a8502e052007400e150540f0000d42c4040284000d001d00c010940c060b00859000780b80f80400ca002d0f0040c80602c0794401c1c1c90a6410a80d084040c0040c440e0803421107004044600b921b03101c0d0703c2c141100079102d410280c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 386920503 1250 386919253 386919331
    0x908030118020d0510051201091709030a0b070206060a0e16030902010504122f010818100906020d050f0405030d050a1103100f05010306030305090d05160b0301030209 73
    0x2011008100300c1c950305551116850b04000c11140c2090245401040c51502c41c41d48a088407007055406007006010320b4503519400100768404041e04080d1600d507410500b07a164252040704100f0021980041820340107003200e401912403800c1090038800c0d46486130300a480c0c061012401e01158007940c0045141c1c0b110113240c0080c0c40d80c214801262b0a208941c04504288c0c03104817010184081c864a1b40f80440310b0710050341e110150424020307141070b500d0104138040340c03440c0000307603d0a0038188400030007a001004c1d60b603040b900d80600411524803900a8401d0b550114001d45140c502c4e2203041e4005103600780c0b40c00189042d5491a54900c03848207245001602ea0003c66080c00c4140c12072800705010090640d09c80c074011074403565100c0e00748985020880b4001002030554020301c10007050341c2d01642c41c1d42c5440c000005009a074076004c2011940d0784694908030b030800319070404400150103224103603603595246004000d00b00d10091b041908410303401e0030550307160303c142c903802c4001e003404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 386921753 1250 386920503 386920529
    0x121e080c03061903031e0c020f120708070602070906050105040e01060e1816080a15170f01020c100e120414031c2a03020607080c0d020a0306150309080301 68
    0x80c80418492242581c43c0304900440ba81e0100c1055007044100448000d000354071580c003014820100c2d9038040884002e50002d110403002410345c10081500c070300906600c82100c03926135607000f8140c54802c2d680d01820041c0c2008909211030724a0b130050f00000c1009280090a207800c044004207982010711443d014090400c0d51100700d619245800240305c0130b645030101d00b034507185024050a21890703880f54001080e5900042d401c10044c41036102c0e04800c1d40c9500291030a258a442d04000e000c182d4900910030400c0e00b068628090005102c2c020400e400350841e1840445c90a0650b0b0301508101c900b90001d0305a01c0d521114013054900301c8031500041d40203a4051004642885e401c03c820100002c10114040301241e00200f202200c0704010b41d041c9658440819200880c03150000300074010b030042c101081405102d05205500107000081440c1f820382a030440b2402c07640300c40700d0080032948520741000b004400e0030001c110583c20303003014820b071401c07661008810f101c140030b0b4071902420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 386923003 1250 386921753 386921761
    0x9010e061b0c2e03180b0711010501150f022802090901021602130213270204031211071815060509030d0f0c0605090a12050a090e1305030304121e080c03 67
    0x100341c005000950314500d42150851660403c1c0c0310604d007c0b03900d9004200807c00034550750f1014401c0ca4100e51540c4100701200d240c166045a50740720441c456011480390f40394020034078000340400a1044000d1001c860289001d2040c0708075020001c1141400743d106101e49064411100da002150b070364101c03810100c00000c940400e000b805903014082100e00000400714507001c202c0e0b9105a91034455100303440c8000d2007490341c82a8458cd000080005808190703c1d0525401030510114400d1941d0070b46055a40301c0718103040000c4000701c00d9100c691103510f400c00a102e65603030305000e01b450340f074001e141217441c20200c0d5440c0b85404012040248081418145522401944c40181c0d800201440941412204265a003a012031709481070342c070741f500001c08a80107008031152503d072a01c0e1220480d14003499040441002081e01003800c48440040d800604c5c180002c3d032249210b0b601c40d078804009050003c0400c1e004c1c0c0f242540002c40301051007400c0350810989a403200000501568a0761 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 386924253 1250 386923003 386923007
    0x21090406090f1e0903051209070305120304110405150d060b0406080102040f0906031a040302010b1512010e070c08030a0b1008150612040809010e061b0c2e 68
    0x1599481142010315009200080749816080822020581000c0c0c9080d000c900034031404813503580200074086001040b1203a080c0301c000b10050340c802c20542c1a03a10320f9a80c0d031a01c5042911540c00c041001d00c00001b004108070f1031141902c03141400303807820466031401600355040411541511803041070000c2256003003141e103130002020041d01600c24010360b80e8601e02e40c3c0c040d4115001d07084603011848008140aa840c0c411082100e400c0304801c2000200c644010015400c094015011135403101596003440d202c1046590304661440c040350707600c5203c06035000d21004180c208882e42c2c0b80d16030510042e0750384011900f181d0368220350507a03500c1d00d52840c20001402d051a150f0740041e10503400d001c0c665005881644030345a510820036400c1c0846040003603510400f000c0190307003403540010401160498014051034803060500b8030348886000005426a000108568145198419880040d1006000d01c1180050a0750750306a00c0c200c0d01044e1b88050100020740010304140260550306074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 386925503 1250 386924253 386924261
    0xf18021e0d1b0f02060108030a081f050303070804030b09121917010e0417030907090b01050904050103050705010210050c030105010305061f02060a050711060f0711100906050702210904 81
    0x160101203054a00340c80b00b40094200c010800d01c070005405030f070300000341d0040c0c040308480c4510020b03906ca00c00341d5214483c82000040c0c540100b480002d44a40100f1141c600b0002412624010122680c03105e2443c40c001d030440b00000c0c4a03407540e8100079210600000401c0a13524800350031411107135180240b80e41151203c00c80003441e01d091110800004644201c0a1464025400784031302d01110700500703441d40301d03902c01550000b002d58401c0404020803941d0f03034801c80036240140b41103481d14903184009010340341c0c02c0c2c106540c207030081e85080005680400600c00ca002001c40c00b8041e81c50002a0000c86001c1440340303078107254480e00000d07850342c2c420140700d16100078400c54452014900d80003e50342e500454403401414984000304140a008081b42c2018001950042445a460034044596a030000c2e2503441400f60848441c04080b0301400030451900107120005000c150314100b0308141d40c006002c602c1075401c00114042100380c0d5610103059028144180c0342e607003000c000410000c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 386926753 1250 386925503 386925521
    0x1030b0a0b09011205010e0a030e06030c2b0b010201090809060c0c0619030b0604050d03120e25050a08062d07030e060105060c0706080a02040b040f18021e0d 69
    0x144298000701320f40301440144040507010b0402045030785c68181d4010340d01d409260b0043c01003646595503031560702d8800002d650084643d0f0b0040d0504444680c03a2b4003402c036109032074030034095040c0e07441e150050034443c003000034809200030700112483e9203500f060752003291000c900480000130003400b41c640070801080c000101801081d80d0311b1010b120030140b02d240740c0c80303000080d040002c1400c003860103509a4050701c400030b0003140071200316981a83c80c0301500e6801e44c00a0349444202c0c40c441824484600d000b19100315941c183e500e49041100c00504980145100d16201c003c140310003200010850b40c000c4081d40e008a2800008079800d6103561000500303070b0000050420002d03069850740041412201c031400321100e59881d2805c02c2a03a0090400d80d0580e81e0160804004552084d201c2c0c1e03400c401502d0005140c5511040031038405d034465005107020b45000781081000c4480c1161909400e4403404045007040c140710385080c00c1301e4681301e030000312030404140706040590540c000c81c0c0e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 386928003 1250 386926753 386926759
    0x40b0c1501030b04050c01030203010b0d0239062410020102070b01030804141e15160b060306100b070204052d06010201230f070c08030c031b07030801030b0a0b 70
    0x303980d60b45011201000102e8007150140240b401c900601c3d4068001d482c10b81c0d8804200c1400c114a04000308001e400c500000c5400200d695558545851081c1030380b81e10b0382d028031a075950540c03a40800383c50300e41e019004c0b40d0303000303a0300391004608a24035903601042041201c40c041404800301c0c04038064011490050401c0301c01400000030440108010000c4600d6034900d4164690001c0070800030480307110044c982c1c0b00500c0703e4a4600e1030401a520418468070404505069001c0082d071100039503083d04913a0b0204100a101e020f14040010300d07032212489124401c1c5038200b145250490040704d07002400303280c40301c1c04281c0e076000141c40c0400b840e00c185008402c412442482042100e4241d4600d0b0140d482c246960000c40182070b10340101e041259080907864031031141d04009410000c0851082000c0882010006000d4030f004500416101e0202c1c1c2e1a820700c450402101d2900d00009191802c0c100607241c006604158040d04485d000f0b032100e603035540e500083e80090300c580a03107158 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 386929253 1250 386928003 386928043
    0x305071a0f030a0b0a0501080618061c060b03120307091404020f0a0906080a020705070b030402180403020a0b070c0b07080c0c030d060e010b25030909060b0306120d05040b0c 76
    0x83c059a6000044440c811507a082413280d6a4006503200c0c0e201741c0301c941d0050b40e94003171192103000704d08132550801c00151517070b00c04da0005444004109854101281d1940e10303269a451589000c00124004003402c808041c41d50600c0030010341041c4241c8901c01c140840c84500d015240c1c2c07140e05032464006d902e207034117542e031100f1440240b80c4070503400340c0000303c0d117124041041c0142a01c00d42d2a45507210004110450502445111a802c020000c9a2140304500314003c4c101071a095540507a11a40052107800801c3ca06610041c0c402429001000740122401002c03c01202055410040d1824000401d44500c02030f0b900c5ca00c15000c0d007101c0b9200004d201e6815003c560711607021540740c10840b501e1640c86403180d00c16485a8840914403a0300c0081540d0307402e10420b00c80c44810f10030b041c03011301d040c2d442000740140c4185a002d01600040402007040b42d04050411190380025200a07204a0340c102001411502030f0b8000c0c90f061220100c0c0385086203004121004130345800c111640c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 386930503 1250 386929253 386929261
    0x2092d0607031101150807030b1902041e0510050a03090c03080a0504060e0406050619212703021c200307050708010605030304030209220623010305071a0f03 69
    0x80c0008488408601c2550721744050714600000840081e030035180700c00090b0607242e1441d02c13040241d420181480036120381c1c9075041801d1014602c010720003041925010f00c851003103070004907525150350f404280100d4000118516240c0c0c004102e0714103001700e090005000ca840d050000f5520041d07080144807501c00510684d06030340040140048036070a43e078966403140740c4001d001c10b4030381d81d1050700c0e00100140b01c4400c03054482403420728601228900101c0031901c0d9101c0d01501c882d8405484070865440f0905c03200c00e444140080820365220701c50000400c0710340d4000b5565160b10480e01482c20040350701c0e00c69036115080b1040c0d0040040d40303024021119000440d1281e000440c100c0d8544513403900000c64902c180214030032100010080d5040034919000d21503404002010550005103103113003100380c48408442500a503001e03a0700006d110181b1882d4146c540e290340000d02440420600400008200240c1c51054668031a1803030b5008130b010030001360314001d0b20000035001001000308 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 386931753 1250 386930503 386930507
    0x50c07050a06061406040b0a0e19030305030609070815011b0c03050606030c031204140105040314011d070e0a0c020705152101081b010e04150806070302092d060703 72
    0x96013035410f9208014001c0b0400e9007000b000c0d03ca94480c14402c0c0d1700901c180448a401007a01402201018003203601140e402415400a54815003044000c950084203103c001d00f0b0130320360701e0340c4010142080071580c1004405440d5051010725001d0400844c02c00c00d130f424040e0441c6d1210b080740d010031101c107160345902d0031940326002160128024810052400d4442c0303400242d107019801c180703040381d2602d410b0004151241080d4401d2905110042100000044240d4000013100d29000300008290395003050203031940034100d065200035405803c0a000c84803901644035003050080c0c0001913400c0c46240280e040072450b602c034582c02702442c9490181030b0514801003850080d1000c0c00601e108000400500f0781d1828003908500c2d03444415041400d046c207c00f440010007050401c841c14248050005c1c058541c0120010b644a07a419402c00900c00c1c10000150403580e20b05066081c50301620210300ca03c10312082180c207007010080d06130400c0c940e40340400f04200c00a8800c82d030b01c00d254180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 386933003 1250 386931753 386931761
    0x4090f11150f04090f140a09020a0b040602100b101202031512070312020105040c2903010f0612021e0708040509070528090501030f1512050712080904050c07050a06 72
    0x2920060a090042049000605200b0f0118001501d14075146d40c0d107131212803030000c0c8030480003260803840d07000d00450482038040280005260031750080a02c41c81103c002c909480344c20b00c031903002d40038000780c440140303070403108040c040042d0307441c01a01c0783d840d10780746000b0101c541c11680c1c01c400103503c21940c4003004a14501034a016014000d5117404040d001c81c201c500456010300075108194091008040390440c0c1000c07a10104035000c0e88240c61164003850303071710a82c0051909800000708000e0a500f08a10801c80c1990080450610200442047c00705c0603507601024003000c00503000d010030080500340e90140c040580b604a075450000406801644560100915840080d584d005100c2802018410010b00303540c038188201d24080041d0301911400c00d81d0000e10b6202c00b420b10743c2400c19003406008100da111000c0e085035150078094105080ca40251920600240c0c1c1d0101040160040750b03c44901690005042e54407103480d4225030054600052090280344490001c0c4865904 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 386934253 1250 386933003 386933009
    0x60c02030a1b0803130201020a02040608060709050a0f0e130501020d0c0314091c020a0f08040510020303010b0906070807061a1903050a110a0312090602070504090f11150f04 76
    0x1142c504070601041a0261004610001494414100002072900a405a080726a1032040c012a00c640c04554005000d0700d055800059060344010704001c4041d034000d200e0802081d0554425040c1402c2500a0741c1d200d8640c01002c031044040404500003524640b006220307190003100864440c0e0b1003044103000790842c01c112200013810310060030078450400c0e81840c00740a4a500602203003c0c801074040100710900e58090030b601440369180e000c2180724841207001031050702500e58482c148010052450148864601103600900052000c041c17404100c6007100811034099484030740ca440d14071564801c0d03840040036242008240e640c50380c0d1b81e0007a02c406503000c039021051240105480d505242441c0f102034401d034002040d040114400700b680001000700070b0040d9540d941c690b00c604810403070992481001550001042282590500512018000488040c8040b6041e51142c8070b04140001c0e0141c10000da0240d402c0e203d42e5519018040d41490b00c10b441d07254a403400103100943c1084c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 386935503 1250 386934253 386934257
    0x9010603051504110a0c0c1502060f070302190c0804180b0112051506160f1505090a03090b031009060609050915061207090305150412080f010603020d09060c02030a 72
    0x2404080e841c0c0340030700444101549184e0700900304549080d08171041021103400b95412405490003080818903902d510110340c0d9207400401c00c0d810a40c059010300907006043c0702c00c1520511448a44038402d000156400f000ca14084040c081d603801c207142030303200b903901240c89804000704240120101d60006003c001c000d884840311815000309120580320211429800c80c03010048101c4186030080182c4014105841c0040344083c0325600c54036002000c3c030080d5070404951114014220460041c030340d100501c04081d0141e0541c940e805000d81078940200c810342040400055150102c4141c01c2d0001d0604040c04d00000e9600d49000d85030b48054040c44e401203013a41c3c00212507843d5440c0000c8000e0014103102d15108030041001c0c880d240203071800c020890301c140000040f071070030080c4040c0b509011500020a003071624026003440520035207001405001c0c010828013a84406070b550454116050160355107405041c010003d03c100540104154a050040c0e08415400001f4200c801019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 386936753 1250 386935503 386935531
    0x324100917011a040c0c08030c091203040b0f0d1410091d03040911070b1512010b0904060c020a0c09091101020601180207060b0405090a05120a020c09040305090901060305 75
    0x1003034941c20303074060f000c024401d03082d480c1119189013000c3c4d10141c0d00c2c2e0003500e0100b004110507906d01c0d415034001e40b4194142140401c046542e45425800e50740440f010b0802940b500340380c02510782685c090701c0301f03107010070101003541079030354030643c00c212459020600c02c040a0b03d4114401c1c494040a80545c40c40f461410214034000c410401d10080403143d998000d605061500c450030780a00001d5138021800c45040c8000b800103922071401c035011310920181685401c110b90f0a1000c1010100c0b81c0400c16030511142480070f4841c0703404513412941103d0049090765131000183d14251398484000c2c265000036200061002c2d0b50b274003d1078440d2045210683c0070550500480e6251028020f8100c00c0744028014054010319500a002c0301f0320500340810b00f83ca500d4000340803280100c1b075084813500680b50180420500340310400611440701e4101341040c2030350708001e6640c116807600e68000c600540c08103091501070070503561607480003080214150f840306002805080c098442009001d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 386938003 1250 386936753 386936789
    0x110c1501230102071e150905041a06030f060a0b1804060807080316152409020310121509080403050106060c0201080a020901090b130618080303241009 66
    0x7022410345284105a000305156401c1440500c685508070000d140541d0900304002100381d034070160b40d040304616032200e00300107107000f0038801552004400b03c445190038042100f42907070b403503041d41d81100f0007c85144181c0d598030082407400c181500881ca0513030022614140210b0210426426500259014868103550344d602c00d596180c3c3d4003480c84a40c2040c441842400c40c81e02806269500030054010103804011411041303c031140c44080b8140b20b40c00344a03000c41566524503008081c1910114514540001c038440c1a1a05025000207052015980800d01880380c90560450308483c0c010000384410b482d113806c859029110481d4294204400080e886004100e840b001c0c64068507844030700e40c1d031304c544103001b0f51017010028140800400046501000c800243c041c014010307540b68007803030800d80007500758180d8019108504000c0700050000c0c0d00e0100030740342c001480394030380161207118030100f1140040105000e50002c0644481c15043d9610001c04411030310031900012503110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 386939253 1250 386938003 386938049
    0xa0906051c0c030b0a0b090c0a1d01081306111204020306070203120628080708101b05090607060905070e0c0901090e06060d02040e1005011d0103110c1501 68
    0x16042010b004500c40300402c00c042044041100e070311052100d4006201c01c08000000c40440080d00c801501c00d01c00704007290f405801c10701e4000c10039000716070740f172900158400090400d000240200102e120300f1488500300b09542e00080002c15000741c403140c0b01c50b4290818800100d00300c0b070580c400c0c49100e020402050000c021606c0b20440800d01e41e80a5558405100340790040400c101a107114030940c201512100c00d6254000d0841240548a000d2a200c101c03450303c1c00441c080e010940c584995144400d0460780d031342113500001d0912035101e149070720004071280101a00035191905024640d02004408901c04080d18142500740d003c40d225980b01440c90b026484142d404074000038400d010f20400d46101c0e50b0b0041008115a14201c6000c24500598109501030300b5000b4410081c0155410b2603501940a0802072074480c07000340c5840d032407030341c02e250007aa81414540d03141d10742c24540200704200c2c0c5d42ea007186402c4030302144295101c1104c40409201c0d01440e2000140c00b481170349 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 386940503 1250 386939253 386939299
    0x1602040c092108120f15010e0108061302090306040303020c070b0909040b0c1c09110f0a091104030f150c0e0d020108090c100807110604080a0302030709050a090605 72
    0x804000c0302d82c1d80e04040220b40c581e0040d095005440491003800032581c841000003035503110b40151a0300b070126041080d02c142e0b4452154a9803414089840e07884c0303c7c0740e40c0c01190b69a1000003102c020144c00d6821400400a04c5190840d5806000328400c0100341a010340003094001e16503000c88244560701c1101e450315006904110354012840f0003c50081100700c140300d1b03045856100c119181c40c00101c40680803014640d00d4200740303034880f09564180302d030780c90b9a100c1006064401000701258500013440104a078094868000e42d1803114031600562171054a003e5030b03100e40318812a40c0b032414450030000160090048560800040c014801d03c6402070181c0880082d002c40b280081507401034403d0031005100c8041031180f000300c0305103a070741d452014039841c0e0316031070344007003810b11032070040c0f2206d450285203c082e440103040c0400204104111403140c22a4070740140c40c2d80302c40300221001d4000c2d501260b8000040400441c000a15505c400101d4030210f0301c1240128001c0004103810b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 386941753 1250 386940503 386940509
    0x30304150b01050414150a0c02030601090c0819090f081b0c0102070506091302070f050706030c0210050402130c080a0e011a190f030f0201121419020f1602040c09 71
    0x103c044c041003084d5003401c001680c0c0e4a00040c02c00040800c1c10351101441c0e0403001c09000011a03080003e0154101031000d6409060801e10a001052402001429000001e0440480e0001c7d0450595a405666018860056004c0b442402c001c07100d05149019030004035000034800c1c6803a00c046030451002411100106040e00a84400742c90302c0c00700042a008024803942003040307000400d00c0700c04640300600c026440740404040f10511401c180d498600e0a80048080c140f50104440d4420740028a050348045501400b154a41e01c46c408a0714ac405041c8142a080741452003442c100f64203c131185201d41c60401040001954144203107090703e03040d4846a200040a0000208504103007520942128030920b0780700085954072540d10b10040282e1040d5100c50300480c83d00110f60340042081180e5065030303001e0180400401d407040081d0005080c40082ca94817030810304541c202601506e00c1000b441c009140c80b9070040d943c0c0728071281c980d60124070503441e21242041180c010380d4100d0503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 386943003 1250 386941753 386941757
    0xa02030402130e100f0f0216050c03070e0f0403031d0705031b0d080307020703080a0e030d050c030306120f011514010c23010b060c1b04180602091809030304150b01 72
    0x3d02090080e400f1300500126402d280d849450346204203d03140c1a00080915840300341c55009a861b0504040c0c0c204024004014440c1e0031104003002000b0301c4010721904426000310701003440e11031b454103030001d240b000302c8a601c208912004203a0040080b400703604030f440580507100030025442e152080035400300c4015901880101c40400411001e9014540c031104900440c0d035180e481ea02c0d1110750f5040145004006484440d003100b01d0704042c41020203061403400d009040c800940304240c1c69010080109001d0504100503a001d90300c200b00c1e241d01070003c08001c00c51859480b100031684895802514080644034000081a510908603030403500e0b00521a40c3c1ea2401105445294900080c1e9100c010764070b9410540362030356640010520130750240010304054071039800301c1842808602c10305216620b000c690f082080c0c01905400c0840394045001640d030070a00e0000f591410600442d140314004910030407007405000801940600d00613100581400030703c920140945e00644440e40c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 386944253 1250 386943003 386943013
    0x91a1e030c04110f13030b0408031501020304030c0b09030a08130608010803070503120411061b0d02011118010c050109050d081609030f0602120a0c0f05031308070203070b030a02030402130e 83
    0x200c0400c60217003068450010550000c50b55980b40c80c18a1a810b40d41507450503000024030129292103900b0f1120307080d080c0044d50505245d0b4844c40c0e20f0001500c2103030781b1385000041c241d0040d80e013400450003141c2d204001135200d07580054209204a0240a0075000c20b10142c00840c5400001041d10030300c0303a0100040d0f00e0310158002c038022450014008441304403c601c00541141d40303000141c01c101514503281c1038121003d0030701034680341420231104156450011400c40c0d490899080301c02a0302d0200c40b6807a031a01c1c160040310341009078a8094850751810914208100d004900c0c1400482195038080f070350348a501039080b04800c00310344035000c40d085290400021b440380310781500b0540104c0c80181005000c03482844d485104a0319505142c4e0780d4050032201035004030700b0680c000ba507440c00c5419441c00e400c441c020400550009840e1010208621086690800401018140022100e030b22410441c0c001e00181d00155001c034850700c0d6114000d0503001042c0304e0080802c2c3c8a100a103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 386945503 1250 386944253 386944267
    0x1d07061b21140a03150608060102070306020f0f12010e011703270603090105091c141803030c16050612060d020109050409030507060e0610091a1e030c0411 68
    0xca001d0681c01001018456296400403108800c1d201400100c400c68802240390424040340030014156a0416800d01c030700e91040c80007690340040d0040c140d81d4480c50060744c0d003961a041c0003484c050710300c51907462a170000f15084100e18803806a412038442e05400c0301c00340d88420b160300d01000340464940f5203074418010681503604c04a00c0c840e545801d11141c03218400d444000c62165132044840c0500343e0b44a8091013900c1008110700140610f03800e10740d000358001c9070001000d0354011241c11103865004905240c40f143c1c6080004110600142201d9584142c0b4502c00d48076400898091551500c0440000d00c07424008101d404a20000c0614042c0c2c1e07a4440402100c210070324400da041184110000c10161650b10460480346e00903141c05440340c08601d003040680d0411041ca6150340c0101060180043d04c12042c002600e02407400459816601c0c5041c0c1804820032583c15801750403480e24007c10782000c510300100b040d0503401d4484020701c6000380401d4480c0d0001040118104100d10f03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 386946753 1250 386945503 386945543
    0x201091703070306032907080c1206031219180e0406091401020319180201090b071401020d0914011103060d0c03060e03030f16020d0804061d07061b 65
    0x7154040c009040000e291505c90721a40b0906500000f035000d40e040504003110300319180302159a02200d64a41801e45140c01030300c4071268007a00044588040c50400419240e030b401f8041c1c050b01c41480d0b04045e0710b07440628003604c540c648411000000c1840b40c02c4203201c500e41e0101700c2080e035112202101303554440d41d485c2d200900391040c0584507004628202a1001003e00046000e43e0400980b150800c00e48400e0b030044036140c184e200452a00c1c03142480040c0d1f007008400080b070303080310b808a0f01c030a11402d107403d84c01d4405203401200d51000074000103164075544a05041d500480e42020701001c0500c4445c200c440d0602e82c007480c1d010500c0007070b1040c035191074100a21031003031b0807694a0ba80c3e2030703540c0829110120007021454101004020030310813444805640301121003003e03045a8014039019440e00c842b140c0e07180030024507500040500000d504004100d4041d08213200c0c6000c1418819511010140205000189101c0180c1500041c1e0b900b210710407500500340c0088a28400c0340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 386948003 1250 386946753 386946757
    0xf050703080c0a0509031c021005040203100203130803090d090e040320160803030a0506060403030c060f020c0a030e011206080601090b1801060e030d08010b121f030309140102010917 80
    0xc124100311082110660b030b07450030b007d821250f94468844110080e10801c000e41848511403e02d586a8542020840540da002500c0c60100311804401a505d44032100074400d0300201050140104000000b80408008000b034000490510b0355039040d16203849203045000701009950240000708003914401e0508428617941117000c500034120f8100d03102e10510700c01d8000140c0d001c0c0d04242c02c00310401800f04000e0280e650321140442ea450f01d000d08503940a801d14088580217085a95506100c940c01b13001ea9046820103001c1d4411105062706034503008001d0400303d8270403030000d1040080d842c480d001c1405424140c82c1064040c10003030b8200a030300e01c01413034060451a4841e080b00c007004407800491615038042d00b02030390744407402024801810726180300c0140c29410011800c0c0100701e181c149400b51400e000900041680039120401030080d0010694081148456240000010150071410328806c43d16400151050318100340016401c03910482d801134002d1241034070400d101024000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 386949253 1250 386948003 386948017
    0x310090210110c0a030c140a06270306090b070e04060501021b041d0708071d01030201050913020406020f16030809091f09091506060e1005090301090f030f050703080c 73
    0x2141e2091002800256144d0115070041d18040b0b514070041c448100e146e41225559181076803003400c5039140c0400100000146190f554880030a56800c1410802c040e0b1020000c40d0043d03400e11112006081c8000682010f0300c1d1280815000228841242000c1c041c000484905801500281c204212900c00c0520046c0b034540d40903a669121500b8440c4075013030850314140d2540185034460500c01720528107035003a0814071110b01401301489440011158003819a64203281054580c2103d6002c00d2800000c2440d0041890020401080181d40024086842071000d4100c512000707a1040c100034a80c090b000c09040304108100000711420300c80055504002540c00d401400c548010b070200f01b804c039540207050340540b181c0796041803100581c8503800b50080d03040304120a600d0003501804034080d40c900c850140d451151190a40c5010f402900c00c03081000c0c0003481008114580106684280302e170460101c0c401040c600b400920407403d8480c50395050300c50a06c140c030755165100c00380d00541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 386950503 1250 386949253 386949287
    0x21c14100902090315010f03050d080f0106120e10020d1a13020c1504030806040c020c0306070e040f09080408011103041203051314072909092a090310090210 69
    0x11703011411a20204007038a000b02440e0065010b910704500d040c03414150707101504001c01080505000010101028442c11907645003496000c002c01207103102d028082100741c0310894060180329060206841c1c000b85025426160100b141660195410f041e008488984035001003106030340503400e0080358020602d403100391048859046408040d5262908105d4041740040d020350144081d6091500420700507141c0b40c009840d81840c60804a9503d60000300004108600060200e80a4072190304c40362820240000c1800741040d1800e1109166002c0d103d034507071941c80d10035644c40d208004000d507802582d10214003485603084040407805040003410900c0d9100101c00b62800013520480390850031454030020b000b107903241000d000111103208100d08140d03034034004800d004407041009ca60f40c0c0081100d5040f1a52100040344190f05401c440d0700c0406007208840081004402000e8502c440080f02103415424005d03205c54281d80b40341c50020b40010700080306810031800790001c000000041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 386951753 1250 386950503 386950513
    0x20604060f090512070201030c2a03120606090f0503070b0a0804050106120f030908010b03070302010513081e0c270a200702090f0c0307050a0c0501021c141009020903 73
    0x9512103900340413201501031203806000408008558040c003601000c50507a050a040301d0880e00760300c1ca511441002c1c0e072074595000003020300401d800355000140b10f07014080c003000703100c4c1c543c14040d11411090041030101c0024080006541c607000914906603032640d0640303403c001c01031f03070141d80390304000d4400c582a5407180d1012803140c038030900d20401180288005001401c4c0c1d8203016281c02d0107600301c0b10345a41801c82000a548000451204680d820720384070355142010201c00d42c01000d19048091a030040900300201c01790210b941c42d02904842c81a41c44903418801000450061106841c044d07828405c03600203031005050b04168000f4001c50b0120b020300780c1542c108400001640031122090021940c1010740c1410f1181d5a03011802018210403824015a07400d51401700400180c100140000c1c0f0a50300d91141c00c1010788540e21100a6403205a5284070a07600002010004200c0746404450994040c171420f84500802007085c000060703d0401381010041d501651142d500341c410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 386953003 1250 386951753 386951771
    0x41d0705090d0b010306140903091912121d0112020d09062c010b09040f0309080a080415031a06032206020a030c050310052b060b010816020604060f 65
    0x1503450300c02e0041e48910480401e56041d0319020080341c100ca42c20a00c101c0c010f40800104810000c115072069504480f80b905404c1841600f0300c1094454000b40003034003400a0240030080e406107141c803e100203407600304200101146040c1e0500d03524070b00c8c41c0003074221813124580041e00c0d802041d0f04000c0d5640070820380c040d0784440c3d080d112482c081d418041c000000204460060140000c001c1803254002d02c840846040014603040d00500042c00c03004036040071004041c01400502c0050650105862018000e03040901c03080d049032059090034040040504d040512134819010b00105010780101c48000c41c0e02032210f83c0d0002040307040c1070700c00018903c0036001081101030003a4071a18016903101881c000c0100bd80d0081c81401e414844140107000700600c001c402002590000d680802c0440c86440000d0b61201011150010300b03e0034020312814810340b03800c03015440c002a2a84841a1580c0c842560100c2e43c0200f10001a00070070040fa0000e2055006420030800400020441c240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 386954253 1250 386953003 386953009
    0x60111030a020a06110c0a0b060604030507090e01060509070804030804060e0a110a050f010c0b100914090c01020c0307140301112b02070f0201050c0a0c0f03030212041d070509 77
    0x1110711462805030307104030042c204200260240c4a2622010243d0701d0038800d16032a0582d0f9840c8410009050305c0740080001c2d02500d0744002c1d10700840d04002243e0107503503500c041400034419100c01d86200d500784400031420f420b086071620700410355079807800740701e40e01c40d10101c0700d800c00a40112041c980300da48807400d1000401650000718010108107204824001c1004200052a4409802000c401d07121409070b07a04100114419504804c456130107540d44644039412070542d4109215080c5002c5c044c81d075113000c03200340920450b103660450310402204001641d681b4600c00549a266103c403509104044040001002c084000b07030006c42c11076a0104402c4494103d64000c0c80042e44054515000c180714106556030700d404007000714501805c90700c500300b07a21226540a41841000141d02400c846d08028919a4540101501040503159401000c24071700b24803003a4018030071700500b201d150100c02d003101c0444030710545040b00324818165005020708024900c81c14800184003c07140c0b62 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 386955503 1250 386954253 386954257
    0x10906152f1005090609030403081b10051501020a0b061002010b060c06090d090605070201030509160f0501170c04030f08040e0106020312090102071113020403060e07150815010806011103 82
    0x4898019107a40005502d44a088a034002d041d070b641c1d40c0c02007040c8941e245010007200c055a400581c002e0b5211125842142c1c00301c0094440c28240c81042007000d00c600d4581d00442c020340c98602a42110a80350004980d50805170802801060b100000310b1020718080381401e80a00c1035000108400b884c08000801a030840110301d000d0750010000c00142d21814849100b00d0b202c10308022074000c0c1410780040240c014514001d041c559038201040542000b042902c2c544400011701080e0a030b201c0740300c003c0401044c41140d010804800b020051100359901041c0328003000301c0824105440e40e00c844110007a050340a9071042e404110100b50400414031f40e03806402c46400950707513900644100b040030540101401c2d01c42e40b0500074000002e40e8148080218042119050902510303007903410024440c3d039000601ea40d00d0280000c84034940481c00800712450f00c10b124640e40d0942e081a0780403107044035094180505414220143d40c09445181d4004a061400c0e83c44e40e0454800c2a1075030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 386956753 1250 386955503 386955587
    0x90f030f030c0d0c1104020f0c2410050d0f020604030f060509120705100b011107031a0f060d14010209090403030b3c0d0c1d01090615 59
    0x5a00000740b000c000e610204402c0c003841c9040c0c5010650460241c036104400301134150610b02c15600060a0200c1540c600107803803914000c2001d4a0030400b21090088800e60703c024856040084800051102c9094070240f03011500050207182100007951742c2c480401280d204200da01c28400d210210104d8004541c0d098101d229010014542c180030340504d1410260350001a0060f0301002124005140070030302c80c0251002080202e1012007400040c0d03242c0ca10380440c071802d480380610000900c040700307070311803486004040078011503200d070381c4014bc2d180c01c202c545c2a005800b20014400041e40065a0502581008001810540034100054904405503001d070f00080d00c542e2102120300d4000b411101581581000640040482d0007007041c1c0703240d4003900c160b09420a88201c10075281e0b03047c040407203540325100010142e140c0d04028414440a034100c64490381d400000329140c5400c3c4100e030280c44410300350f140005020502200d090041242202584441800b0198202e10030b481c00440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 386958003 1250 386956753 386956783
    0x13090b03010923120315131407030204030308060f0a03030c03030204120f02281406161b0f0f0506071104050c09041121070507140106030c08010b15090f03 68
    0x4080380c0e1846180140810512800d66030410511046c000c0911404840c1c10081d1002d80740c400c11014480004c01c0360125054880d0650b50401a00316816030003041681c1c03082c0c4641e8420303100c460901c201c41e85901100303030300080da014040c800b0030b001c4c16070400c03a50711030300d07000d8034040d00c1d46801480d010342031000700c80c803880c840b80100c11480e14070309141409886000b411694003107400300d4019450903101d52003020020503a160341a8550710210303000d441e0030440c0021000c10f00e152851403000704040aa803200d498010104036200b0034030000c400c03074079201e84031000e007030405080103030680c032044041720b9201c1c43c80c05c80c44298603140a864032032804901d102c0e0302c03800e180317082c4025151003003104419070700100495803021031041c10000c1d6a42d0740c1c1c45001038940d54500282c81e03e210314076010700403100a2084910300001500240156032254549800d00760740e920740e03103003a41c5a50f00b400364070501d07848400107180c0c410005068040c4000700100c082030041030205e810450601c2020b50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 386959253 1250 386958003 386958053
    0xf0715030507020115030809030c040218030d081905130212010e010c05130b03071404120507060908031c022709220f0503091008040c0b13090b030109 66
    0x1449581601ca0309a1011880c0001e00c030101c0e109004050880d1a0300004083c0d01003c100c960703140c0c800300207001c1c0c60031011300115500c640e60100200051041c1c610140319200d09004d28446901c5862074902030310034803000c8481e12400004e000058030000704515038145045003194007581d40c440e802c03c42d20400c0e000000b11400e0510707500b03007540c02c1c102445060220070481d2001c000c0043c564901100c5440c1c141c581c41c0c0d10b940b2011251940d4440c0c441111450108001c1088004114542002c92107001115411a034641c010b5500c0d400c1032142641c60740050207042c862862400e040703000c01c54880e400501d1b100a4071944050410f00e035001d0308010120040610f541d080c41900790750090b001c0440c0c0b50740e900614095040703900300c0990003401d50308161000020854200f0a40d030b50081c0c01444182690340f4424010302d2404122000d40d8072440380036000914020315411501000002804400980d050544540280c4006200160950350300d6421102042194101d03200d08004031a04030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 386960503 1250 386959253 386959289
    0x11040e0405070f050a140607060219080105030a0b0a05040212010f02090f0a290915030601120903140f07080c010c020706020606031504020d050d05210c0909090f07 72
    0x1c0c580581e80c0c2107100c0f4410303149414085581d81c2e0140750100c90100c8035080108039000d0204086025106000348481d00109401541c0e01c2e0180302003200c00c945a440d611181c0e40e5004040ea03c22a0000150800031032101080401c0a15000f2643c800e002a02000f0074a10000c002e0b8210741d440c400c00c00e01c4690104d0700f0700c0180b810309103802205c0d200308c6d0030070b506134240151800c0b9201409200d44880302004950400100b00d403090740c3c2d45010040000c107080001c4800c2209552003114605d0004200045000e52503540740324451010390182c3d200181c0c041803061200304c580c040003858000c0c0bc07040c40001c00148003071006003c0c200c070701000428100c2d004d80002e89807071002e400c00420341d08207604012032610b0000e454051001c00d00700c400142c0c1c903140081404222030710030180040c09900b03600403c11b9005001001c00e4001c80719461000800001004040d40b0b090791010312810081198404a19000724a10381101c0b4038016104c070350f0a0142021300c0c0001ca54002c0340d0764000f5038841 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 386961753 1250 386960503 386960513
    0x150204050f21161505030c0a080709120b1b160209280b0a0501050301061704021c060504020108010803072316030c030606270c03061208030603070b0a081911040e04 72
    0x1e410101c00e117040ca01c0c1542005d111051490082c01040c03070800002c6000540075a04c118180402005075801034424100c450400900c011800c135000701c280904101d00d0b401c0342c2543c1003110003018400d00c030300c10610310036820402103c801074070300640c60000e1956000f5003220301510990035000244002168082001030040038156940309030306208062004122494102c022919245c230155000d0001c0d503110320000b02030850503100101c821000b01d02c100f080082580c00540280d000740c0b19000b0580c1e0303032414141c0d6846196001000003240c481d20110360b241c01411008400e501034141e070122004010303981c00307100c0d081d0300941c0c42e58520042081402024030841014299290740100f14904819201100030105070345440b035156140060002c6600c80e501260107000c07130201c001e20160f214242001543c205540c1a4460302035480d00040041c40201180c811040c2c0351100c880507620041003010189010500c02509074469a201d1000b044090003407001d070131102480c0d04c06050038100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 386963003 1250 386961753 386961779
    0x121090c09050609070c030203040905070e03010e01181506080d05030a05060f0f13110c070311030102040303080708100504060b12060f01080c130819150204050f2116 73
    0x8000701c07403a00082c00346a499101000b079008a003820991001e4183d490100e1442c442d030750001c80d031586010140008aa44984030308110303402207000788015142924090300b02c0c0c0400119801c0c18a03d0851a0006041300c24640c00c20040d00e140010460b96904550303041131506060900010000800c11102e0b031010310400303422402c1920030303034480849040400c0c118490350407014456101d90100c01d110981540010052036801203503a82c541d6901440c0070350300e0100e0700044803580300440000340d450405100b075074121784e019984c2134816140d0a10a48407103030b0251414120340c120b0388001c112601c031806080003c2c59501c00c3d890744c3e00d1041070104401d12018005510030b56400b04044c58680e030001070f0310703009841072002650b100c00140c00601c0c070310740c503601400c1d160043c140034444070316102108141030790041d1400003503203000380c1584080b0310031806596405003185621307421a0a109144d041c12010381300040d0302894858050b00d2410340800c02030096210b440d081405100b190313860b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 386964253 1250 386963003 386963009
    0x405130c02070b040305060c0c010207122003130504020903100603030512060910050618040908190801060206190b090a05160306121412130602060f160e0121090c 71
    0x1483d605107401c590f22586c41d850b0140c0000400900400d210700500020360444036555440300b03440680d07481c10134002e840c1c5c4140c040415151620401c1d20b2152000201c00c54021038603042e415245107003800d04010003034000000c140d0b054811401d0705c91381000d00e0306c00e440246010f03441d40d6455903c0010786c481d02d4000204554012083c3c4014001050500d4002c203058032011611380e03032650018240b589103e50f107245102c8d44070b402c0c107080c4000d000d1503200520a1407030580300e80006c0248183c090310000070078803411005a1001000410714101d41e00c158480c2204001d021401120880021350440403d852050006a4401c01c0c00945052800c0300c0c512481242800e00c03586150840c01c01c5600304000000d040b60018002e06010743c0703400d02200d0085003051850f95207606950b140b041143c080f601502c400342c070480c804105089410040207216458110030026010b80d8400c0440750300782159a0703a41485100029001c03452030120645140c540c240034009503007009814002480500750f8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 386965503 1250 386964253 386964269
    0x70207030516291e0d1e05090601030c1512021c0f060b0f0304050a0215120603010506100302130807080c0103050604020a0507021005070f06091208010b1801050405130c0207 76
    0x900c3c034030b5040003400766240003054401482c500c1c030f0b0032500c12109106040b03150326540e280100144100144405084000c500310703004010301c3d554042401c0d90f0784428007000d040040c100c5402c101c040340c004000c181241c0e040c50310405002c2244400c10036a005222a05010301c1130301d00b0840300541a100c1c082e843c2c1c1410380c05001861521400c2260f502c03501c80c25094410300000020306002d010000c120001d5409090381403035041c03030052000a501302580110b0b4503150007000c10024501401060f01030f84006000894640709142d0660003580100c0da04c6c1881d81c01e0803800603010710141304440c0200041d0b006844002000000102281d00050540b03104034814801e6004c216408015620620f506451000a04028550650f201d01800750000c051024401c1d050701081020303001070144901c02c1080002c0440d240c50300355014042400342c4100c485040c45051079041d44601450225201810a58903007034550002c2111a865032020341c00f45074441d01d40082466041025000426201d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 386966753 1250 386965503 386965559
    0x80105120a0309060c020a1a09090a05010515030612160503121206061b012309030c1b0103090209130317090d030507090e090d0f0f020312070207030516 67
    0xb03580142005615024081c20401c1c80302508045440300781c81c0d840a031580d1896002500042d0600070125408080003034010440b8001150826860b800b5841c141d41004000e821500001208080c85400003442654420b1580580e910410b605204007003908050004402c103480c142818140b0b03224003085030b1b03c00004100f09d488a03400e1401c1c1c03045d400c8103080320050760301d8442801c206c5008891018106184d46815035049000304050380006070300300c5503070079100c4507030f80d024105407039011302661a90513070855807c160f030000064541900c03d1405040014180040d40c000c18407070001112180f44035002d01c06c0440c1850307007107131204510804201000c482403502000054540d5980700c4000103140c0c42d003000c51545070060003c5006820742c64003800e101c0c03600e40c00c8203540d00040700c00710020071001c800c070081403886111080301f120b1041d0015840c01c6880c4240403900100140304100b180609240840041c500303111468101d0111140c081e0014284910b60504000d41c0340d12900200c14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 386968003 1250 386966753 386966773
    0xb031213030f0c080303010b0702031501030b0402121204121b03020a03060509100c020c0103050601050a271e0e0601050910030f06030615030605060d05030f030c0d0c08010512 77
    0x1504480059a03403160005030074030b0003454481864501c0f40c0080501e4000400045560b03428100a4401c00e80200d01300d8809611001041901c21020f00010740131844400004c1d01509003c1c3ca80e60340d40301086c0445d0342c81c50540c0c00f2600c050300b19400c03d0446000e820541c0703050010060200035100002c00f41d6001d070703604d19030024200030030303900c40203001c035444d10001030070000140850300e10003000080901840d441030030f0094691843c41c2805000c43d02e0700c5d011074015445242940c00c6495981c81d416406400b03200000003003848006841080525208003060b50b01d40303114030030420b030780e062503010110b42080c40d04400440300078911410000706114124a640e07441840725101132040c00c001418401c24a46c4001401030364001408150500203054000003050300200102c071701481e010842d076240c3c4020018905411400986140d00500c400030b9061140c030029500040250601c5281450760310300c01c0c2c142c41030380c01c000d40031464071801001582072003415401c031800c01c000a4485515 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 386969253 1250 386968003 386968027
    0xe06131e091d1903030b0301050114100807080703021305040c0305010f090203044403071724010c060e01020406120b132d06050a081c0503061f030b0312 67
    0xc000ca41602c0181c0f0003880384400d25010341d01c05d040807603010340280311030342e10f0324004664010100445402001e0000464040c14440c7c280070b030180c044c82c0e40c0c159064440400440c065080407142545501000344009100c1e135640c4140000001d45440102d4250b2400d030421a44a42d580d010001e550700410070480004d0791f20340c610080d400010703020350b111160340d0411203c252501034041c041120004c0c0b54903106030410013940c810a841d980b451010141c11040600b141d000303a802d803400407039880c0201e03a8008880b03c00030ba028018501300404901d01d4865406880035000045941e035800181844000d60212202c215110056421300c00a00c000000c520360340000071900604076a1402c40303250750f13006485101d00724108c54402c0380307800c800b910f0600f0080909214080c483c04504400055100f004180040b000c6c4450320102004100f00c80c0584003548004c10340d0703520083e100300d403591103550400382840d500401e0f034002a42c414204289840c0035440c481e12601c4280901c4a0210b140c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 386970503 1250 386969253 386969263
    0x27110a020703020913060c201f05040303021e0c0c100c02120309130203160206060a1707170c01122007140604030206070906030c0e06131e091d 63
    0x742c3c19079440050f0707683c110651a810010301c50040841c0d08041c81c600407140d2246401c80381c03030000c5148804848820f441e19a0b1103c502000714000091000341d03810342000360b4499075101d80641030251800880b215840d0000041741110080d40c035020490a0100030204680000e00e44180c800d6488200031000103081003161000091103002600f2a0260003801441514100400508513500301901070700610080c0d0070444142d000c0d50345485070541514800240c9a0107840003800c0806e02d10704042d284052280d014491604500c5560300c00601407003151144020059001c002e020100e25510004125103240702c0324209460074281c000c40b9510010417180640c041d0390002070f03035550342d03468032004007141d24158000c503001d0035003040140341e00841c480c1d20a074050303a640460551285016800c80300e0b07415007000041c030312109170440d40c14002c0041640070420b5000e490000c2d5121040e00742c410031488280301e0249081070421034500240204404401c1d214031341030392688030400c1e0640e50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 386971753 1250 386970503 386970509
    0x1809020307120e0f191a0402100c140607030606030506030601060219030c0b01090c1101140f180f0106050a0f03080901050a050418141e0103140727110a0207 69
    0x40d0366034042d90214400401042c900704c1c3c03191003540c50900001481624800f407821080c0d8401c80c0440c6100c074600403245409105a50017020315400201c1008100c4076a5501a000c4a012006406202c5880001c108883c80b5012035600401c415003454002021341d0b002401841c02135009070b00601069402040c00454452010100117001c2c0041c1011203000c05001006495148140c2c00031808001540042d12200410340301d901d0360740103281d070a508075007601c04030903140040c40d0301059089003040700c8150031030704112035a4800c660406003641041d0001940e20480d81d5561000c018500f01909840002d18269200c02c85e03261031070f00c45500500c114034140d07040010001d14450070340d02500964000d81024407030300310f08021b403920881c000c05802040c89511f840c80b000082040001c10442c07100401d00c110790915a0746180e580c0c18000c81205103e64141c064403001295a242001a0213240c46110001302000c550000c1d00300121081420356110354601042000c2015400040000072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 386973003 1250 386971753 386971787
    0xa110a090501140a050d021503190501080a05010501050303030c0f09010905030102121b070b192007230a1220070e131a040309090c02031c0b130509010905060103031809020307 77
    0x52036803814ac1c00000500c00814013000146031000105502c4c03c00608585c000e80b00380000c021030307605d070b6040656a0004403900610400100415600d850040002d0007001e101070400e12031158407480004c0c00c0e40c01c0302c1c058490030700a010070006565441c0151080c03032910045080e140807401d403223000b2029801802182c2414064400c02090505540302c61106080d401510b0280d0a000040c00c005a01003401030325044082c1c03c42c2d01298096a0180c204020005c00a0ad03c0003544c1d070b02e40c0a00d40c107510020041c81121800180380040c540c90400c1004140d40181c00c0d0300c1e0801c0e4009070020b50140c42607c074190708111041c00036050380003101c0407010000840e283d517640c0d4070303084401d15032581008550130305220030492110740010240442d4414807964440c40c07031240100d00111a9507040301e55002c2040e4405001d001c03401ea0219400c508a540003007103c00e059220580780c100280d004078001454200810349a881e04103000b40a403410351340175491820314580c02004020544c4607001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 386974253 1250 386973003 386973007
    0xc07080306180705070b0105060906070b060a0e010803040f08190b040c0504090b0115170601120f05040803091e1c030e1203090f030c0a110a090501140a050d0215 71
    0x1000c0d6500150000518404149221989000c54004204d03401200c01240c01381d44540000c6003d00d03190050360f250b00000341203182071501d41e444000c50282c0c040c0c011600312400e40740c0130402000c80d04070756000e8000d01c0d00945e51140340805110702c4400c82c1d400040b00d50811000803290307000300e4a8442c00c0b941c000340760801d6608c4500b000080358156a201a50151908c0b68220801403a010035604a036610580121800501501601c207000d4294103107892000440000710198000d00b800032030106003d5002074140c00c0803110408464003918103949580006c010040a048100402c090340c04059601071780c00081c0c0310740380b999401c0c0580d05610b0705206100340031080e4403d034490424110ba0310120b499034030581500d42844c1d441503600802a0050050a00c3e101c1c0e000800c6400c1d00d0020001080b41c01d2842e2112401d017900f040b103180d405102d400c0001024980303801400d020300b00450200d03001c06000030400200e0324495000078043e120201d0035002507a9001d60040f0581c648058541d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 386975503 1250 386974253 386974261
    0x21e070f14120604230a03120f060f0b0327070b0702010323010806010f180902040207021f12060b0304030e060409060609170118110d0b070e03010c080c070803 70
    0x158075164140d490b00c0c00380c81141e0400080c80106011140c042c0e00c0013160244400403410300c251541340740000a07005c21103901200002507a540e2082da0384500421000407031a4075040380e40c204003160341c064081d000d408820f02c8000b080480303403041b000e4007611880762500a90880c0b1500c894061040c6c00b41c0741d002050003415a4029080307286100c0b10b08000000a00300302c60100d04c828400e0180d10b07000d10034000049021700c5520115030503904400c40200350031540303d202c00094240c40320120b8026800340100401a00c40602d880f80c2141c41d00000c0c01c104140c410010140c12092000f210340500b0078400300a006400800c4980141d01850715081e01d00500011031b91070f22443d40034404803460804e000503440c1e4054030280c1610001c10801900da00307a4000c2d00d0907a2000c5c20310f03c1139000c500541800098818140300c0e4800d4000c0c00fa20030315140c41e02c56026011044480601180c503114004005103028441c0c0d2090b002241408001801c0201e41200e050003688001080d2910001c041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 386976753 1250 386975503 386975509
    0xb030d091a0909010305030a03060503010507021908070c0e160c0b041b0806010b0a1e0e0105070c03060c050304110103151e0e040809100309080a200d021e070f14 71
    0x25502c0103006408076445503580c0c500301e65a40d01400448001a02d0b1035400f040fa4a03044c05000d0260845078010114841031040444080d0f01c3d80000301e034450030402c02c81001071420144100142007005801031940340103ca0303400031100200e080f800700b0180003440360008240f43c80094000e50030605070f071412058480010441c22094001060a204990000030139515960003000d030180c00360307200b0031251804083c03c21140803400401d0041009024051b4a551084019001e024041e000300240741d80c0c1c03074561108803208040c0d5480000d10000810013400b0340c055591420080a02c4c040191611600030ba420011813409015028140c0e02da2070050f0110350341c80d0340d000d0a981041d81e81941800d103003000c0617903c2041720b90302615042144a00756070003403060351041c0780c00402e0309140c2003910000f16030101c0340710040240d01e543c1103c03060700003604020280004205400424151005614030f440c820b0795100c00b0311055228445c00c0c04020541402041200c2c44001c0f9442e0f030020b0700c400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 386978003 1250 386976753 386976757
    0x30203150a0f080c010513033915050705100203060409050f060f090a1707030306031211011104050f060d23010f060905010503070f1e0c060b030d091a 66
    0x442588500d008201092442020b0810000c4800020854414210783d00064443c3d02400a00b255040c0c0a40c0701000400c0b000e1849030021203907500b4004445541d919141007440160102410070ba11507481402624003c1070300c21190b01c07103414101d042000d607070303034050f500d00361250f42002c1c054011011541d40c0d1a11b800020f41d541d03100c010390300070840420510f552114100c0f0b0091021140e90041607804501055481c242ea800079805403940140303011094080c2e006200803010155101000008580417103c544001c2e070403a40c2d805d0814410b81d901c1070035165020318243c413000c0100000c100036555540c078010002c5094031281e40707540075085201c00a1810811003480750b05000c10181000c580b01c0e4955051f1190707803035482c0050f03841e004110f03140c4079207016650105008001054859010b802007aa0703c8825107000030041d560140d0440541c2542080000401c1c0441001d00801c045405000c900e4401500181030540b500c100040c461103451145806100c1c40d844002d0b10742444100b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 386979253 1250 386978003 386978041
    0x9050123210f01022205030303010e0601200a0b06101b050a0b1906060503010b0912120f070605060f01020a0b09010f1a010201050f01060e061305030f070602070e010e0403030203 78
    0x1080d9082c90840d02803050207544003040100c22500302d04201154000c130540054151000500210304581c204238444a00c15070141c44941072014015040450340e82d080700035203414020720013500007209580f43c103490035035004d840c0c2881884801e001c100d10a61040b40740d6a54201142d600b101030307285050450070300032402e4028042c10012001c01203d032040000300f100085011004000695507a2001c50300c82c04280110f04035010304001400c818030740340e850405014054819200000000301e0400000d61000c0c07160242003501054240c14495140305030313540b1101c150750f00101300a0f0301d00004c5d00d81071078010040143c0b100c1d0000c10001c81c001d611411440a4401c0704110480104a04e1800c0129480401d401503003404002601060448403841c1210300e951140700d03589146030304000040d0080c2c0311002c9003c2122500040d10755082009132000500c1c003001d00061410b000c130081c1803113019006104030902e59001041a2070a41100f070b46d000c5d416107030058a03a01d0b01004003c408000175 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 386980503 1250 386979253 386979319
    0x61f120501060c050f030a0206060d1509060f0608070806011502240f1513020a03020c07031b0b0403050d120b100f020c010207060c14012409050123 65
    0x140022442d550040030390540203000e6400c481c03030510101d00580d640e211354480c40c80140c2220010450f02d060001c0000c008070b11841d201c9a904018640307030002c0398071541040e691280c85040d006102d1500d8131400c40542541c0b000750008e207081c00e02e0a6540c80045c8a0f400c01004e0301c0c0d01340302c00c1a109221b64220030895020740e004551404460050700382090701d07017144801010011503e90408010003400f4090007400b03c0000307203c403460703207002900711000d00f006154003000800d1100e00f00b48081c1003d10300c107100a00368681d0f05030303245060840d150070412000c04204805d1004c00e500180d5a411006240751a0404420305d015400144c1a9002c074a03404c6401e248076401c506410020440c1c44080c02da0868001c00c07080d000481c1d5403d12803150314082505050802e001c2031900114200c1c0411820010915141d00e180000074016910305040e144440035800780300f45c4820740145801004080504183e092820a580c9004019840340310310465007e50841c800341c82c1e942d080701c00c0c0c580003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 386981753 1250 386980503 386980511
    0x1505090f1c03030515040203010e0402010806131401151701141c0302100c0e0a171203010b1b0105100e060a1a0903070e33030a060e0114061f12 63
    0x20345000f4000c1c050503186070b40f20403c1450480440d041a10989040301c00940e00c02000e512150015901c001000d4000b9801594124180c03440f40d02e180503c41c0c0000c0d850000e0181503240200c40c500c2c0c962024000d0040145440c1a07101c6a00f0704040e55064590020080010204500002c2c407081103c0b8a00e004001907005204181600411030141103401c004040c0400e04181d00121407954243c600d1030342c80090b0400034080342c0303485154183c1030b252041c1124440000140b810752990426405502415030015110080030444c1019a0017500034200a00c542e0805090285e008051401284400c003040d0300000c610342d6401c14682c0044c6280103114a505d80e40c0d1900701603a03031105c10001c0c040d00c0348e40000901c1d0f8001d1140c5910487c2094840d10303954840d021651480ca002500b0154a000d03403034a5075000d964203100295050307104010000d170440154142c1400d50f031140c000e041c55442008204412901c40180302080040001e13807890340c0203c00d0078281c1d0a0f014081011546500d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 386983003 1250 386981753 386981809
    0x70207030512090123030a18140d0f080708011203020a0b0f0109060509040809062110090c030b010c02130609050c0a020f06090d03051905070206101505090f 69
    0x1d0301009103d07480f030a036240d039011030b581d40300c0314100641c0322105403c4c1641000000d58035046c81c1d002d0f25048200181c24a0020000d0301c400911044010054001350031410010240c1c9802405d481444c400300d041081031854503038400b60981905108240881d1200600c81c0f0415100b8041d043e07020f81c2c05a04207c00b41085e81c415440382609010310b92744545003890110b074625000c1b5000c0e10541d4850f05d16403518440000707025083e00542c501c01c900917503140f64210321010824005200382c0740501c4c0c070301c01286400c0e2038600b550a2841c00c20103140ca0b0000700c0c402640d01100c40600640c05a5124400d00000c0210800800f03260f404542c0789071410090154519a601c014403c02000344d08407031800c04d042e2140c580310032050b2070307220499016042d0011058000c3d00440e90000d00b004030042403a03c2307130709103c0a0b910115400380058121720304101c0c55080004012000c2c10645508807203141d581c1001030b09605c030f110101c0c0c0c0f2601440501002c0d65a51611000c102c1905030508034008003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 386984253 1250 386983003 386983033
    0x24010e010c061b1d03030f16020907020c040f0b01081b0418060f0602060c0301170a08070f06050c2a210304060f1503032303010815010806100e0702070305 68
    0xc00140440056100d40c01e03c0400c4209591181e58041c000307000e503250214026001f90307154043e6419504803ca807800d0340c0f004d03944200c40c56105400c290058546030401104000c04c48481d0b540a00328113203080c2c0d4410303059034843c2885074865070b00d07040c2100190154004122500443e030120900900700300b03281c0090314413500032808540700f4044440d00240c80b000f040ea1916801c552602030b40030240010800321030500401c80b194426102510942c10041e11008442d07071055401380e9190400714041030810580b4802e8a07805080d0311183d50800e400f00030fa114106c101440036051540c40380114644114040c44981d038040c150b405030284c034840c00e00c20599190012902900c4152030325102d8027203502203001c1c4252010050704140a0309003181d800703440140e0f03071078020691101e0203107082100162000085018000b00e170001d0040300c08501ea9100c04030310582014045030402000d000558503492030078415184031804201c0142e03641d140c05c920740142c69002819034030410795021b080072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 386985503 1250 386984253 386984291
    0xc071104051906060e0909010204062c0d11090f0106020c010507110a030326010605040e0423011a0609030a020111100207061b020d0c06020306010903050a06060e24010e010c06 77
    0x1a4191b503480c00ca0b903280c034481400c0303000358440d400108200040d00c0040b51003816404503001c020314400081e60394810041802c80c02c001d003040315549003511640d41e00e0f2400d46000755002c0b000100d00d40300366041210080d2600e0340f110405061100104042d810440300582c00a040c0b68003034080c400166803814003c1c4400c8441c0207070174609a070800424103070010640d1003410381c0c80c691900c80c909850301e0348002c090b8030002c7c002c1d00c14010103000c1c014400785a031880b190500b18607002048030621a03902c041c90442150f20284654001c20100e102502d0114805076403980900b000d01032101070100341400d10710102143c0001c544001818030030480a948410f0f8440e800380700320080724604620a90340c0f04000358071100400c01e404601d000191658004540c407000616050050b070703130349580d11468100c03d030008035103441e11040b040c407902010381c414a510080c1da001118121907002c60341da01e01d0b031014000d98100b01c000e650901e210b9005a40c000c8a60307501007400c1002c2c40300100d030740c4262 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 386986753 1250 386985503 386985527
    0x3040b030f0a0b0a0608063718290d0807050a0b070905220b0a0303110c0108040f1e02280602060c09060306040e01110307080c07110405190606 63
    0x10901d043e0242c1c0107814840b040c5800c0c2c0e9500c1c1c41e40c0195403590002c100e806050140100f40d0151081004000325000200105a21721554002031091b41001d400c006400c0f43e800c8000011494800204001d070010010043c0c00c0f80030b8010700042e41044c1c0003089118084410140800800107480c0c401c00000040300880a80540b86030303c170589502004a9a0584520800b5841602e00410f20100034000310750907240c071825600024040c4640c404901c250010b0341c004c1d000304124040c0003084036800d2010842000c004d1a08204074a841e640e401e00900003004054818580d90303d00c0220b500c40e12064455050300240300d6840c0742c03c8000e0300445500f00c1c00c010705c40c80c5e44c1800001105800001c400d4040c03000320f81c1c40e81c00d081b0b00009002070f603000103100590040e01c501c981201c070b4100b0311440488018201c10149e5900c0c00c0c90300500a041c0291030002c80b03800411054002c0b840805113241000c50841f004600740c0c49900c4404c006200440340700d08410301e060300006101c0d1b008101c074810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 386988003 1250 386986753 386986771
    0xf0105010b0304051605010519020c1021050108031b0111340b060d080915040510050a0906121d030a0e0108010302180414030309100f050402030a1403040b030f 70
    0x400b0030030940511741d500907105107408140203212200824165442e820600c3c0340e0f51040760003145003100003411180d8195003160101c0c07207183d001080d06160840115201c03200500501465240806042d80c2e44150900007282e4a800107101c60555420341110260340c0d101051182c6406c5580095118804041e400342401c1040c008541181c454030342e1900b83e02030b00030708034403103035681c5030240081c604040074200da041c2010080d00315141d03141c0c0c500d0807030100c415101540f5030b0308050901002c00040101a41803023410320804d184c17103520002000035100301d80740440d032a42a54034142e026000c072075010000d8040c0544000c12842d0000080c002450096495500701e0040e00019600100203000107034000311070100319007000192607140c0c0d030001e11070458480e154100c4040300f07055400549040311681c00c024940302448186011300d1441d5103441c9030400041c00e2035800280c0d5440f03030920040c2151441c1c19510101c1c0003d10548002301254260385a80e45861401040d221300300300c0314650 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 386989253 1250 386988003 386988013
    0x815090f01090507090c0e0f0405060f030a06020a03050907030804060f0c0f11010207170309040207031e1e140328020406030917090108010b0d0207140a02030d030c0207170f0105010b030405 83
    0x20707506c0c41003802803d000c4020700714103410340e000c4080c0801340c00e00030981c540050033900312495035142080b20030180b40c040c0c0c200503103070086441d00032f0560384060601005070380080c1c003d0021401d00c208031400c9505904100c0080042e001c002e4038050340401d005000c2042c905040424030404121410700001d09a0940b045541c4850100b0706160041c8091f29a5610500460915040940c001c120701c1d402070416591070324202d00e160080d21561102c0300c000406000e4400c06046010120062200103420300c840c101400102001c158000205181610f0141c802401d1a07101c2011094240c1400640150341e10350712000054040c3c201d21000710b900d0100200c200500e0000d020a589040d40140d46000c6164600b12041d000342e0001040254110b500300001000135140603098817040240c8400340c07480a41500415040800154407c0c040c10305140300444000c1e03011038101c0503a14141000303200440c850000502e0320035070f4110303500190320345000441c0d07000500005e584076038480c4048035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 386990503 1250 386989253 386989271
    0x3050610060206150f0d08041d1e0a09030c050d05040f0f0302030a020910090c030f0c110d0c0507031e0c0611030906030402030a170901030b0306010815090f0109050709 74
    0x781e40c2c41e0100c69000c825101c2000130700c41494442034006002e00d005000c1e04100da001c2d211042617a10135800003c2c1840c6104105500c0b00c0220803950340800088110301141303404401140d0f401000401d0b40b80e00e81e594046040030103005019038018150010112074100d00390071070140c07081c1d000740240c1a0f114481840062091a1800080706481d0301601400c1d804480350f00b800170031000500000d001913a22000410f00400c3c6200d85c1d1121000340ea17000ca8125039060b0410b045412419580381004075a841040f043d84000900d2660005a4500140c8860450030b100d81480d119810080ca007141e00000c24500050a8880741c403402e0040804030482036a900042e540601122000c0c0c51941041c07149540782c0c034044e00516030080c0090103941d00d424042d80c45503420440c03260b005004000205102c00103584c140702c2c1c5c4a44950540042c0f845504103991590380fa42e540e001e02c44021044400500c1c1c601052061000d41074030240244100d2440c1e261080d11440d09004d01c03c0818a441a04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 386991753 1250 386990503 386990507
    0xc050d09060608070e0c040b0f070609080d0b180f1b04030c050a0605040f05060a09050306041b0f0b070b04020625023a030201020f0a050904050c04061d01090f0305061006 75
    0x17501504e000300c4a1b0746058a01852000c964014a5000900301014815800491060302030b14024620500d102c80c1e65000c058446d078200c4401e4602c1c94040c29440d004100540c02c2d00e002d2030780050300c0d20b041c21865625014005070601c080502d1000e0201c01003000010000075005030020f0711421981c412180391a031a0444d80790040d40b140000e05400b0340c5040107507007400e10040118204034a8000c9405031160f000c240707085015601120445500595500c0200741210540080c0030200400c1c081e00385842510861030165100281c440c91510000ca001c6650760030440b94269140b2203101d0400100071464a4a00a00e803816400340c2c0990f0128440a1150381d848941e101143c81425000641141c100c0e0758411101400c409640d400c108801034481e10001a00c1d02c0e845664a050342d9102550501042d1200070f84a2038646800741300038082103820003465105a000e884060015582810040300c51001d154403104800700782103400300500c0001301d102c5204810040c0d0741351010f0313520340301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 386993003 1250 386991753 386991779
    0x120405060105091009110d020c03030708150f0112020d05090a0b250509010309050f030405010207091a01180504090f1e0305031b04050a24030b0904060c050d0906060807 74
    0x10180601c4403007500380412045c0781e2054102032040b2400608010503110b6107422a44000300d03220841d803011080000c02075200c0885a4041c82c80c0e060000500801c102044901c01c80c0031400d818083c00e1980c2d010300b0f64103176042d40c5100c80380040c140003600b003480c000c0c0d403074283d452801e50b424240480001e640004001c0a40c4001076440106212020300398001c956982103c80c0302070401d2b84aa042d400820400c11035402e00840c03000203155250310702000a0319084d040c1c0d104202c2d56042c240c4011380b0f00701c841c40b01e42d9802c1d4282029a42c01c410080e094a010489402c041e500c80e28040c0c0c40e070144070301c1c1d14068207468070600d8030910048021160002c10032401c003008000520800010f60076000302e0152080030804803542d142170179194000104e00240540290184800e0446000c0c41c42252030182d40c00b00b002810100b01d02c0303100704081002500014070141090381c0300c040122580d4032400031501c04004c1a68100103600c0149040b40c060700c403911a5003d1072150150100e084416801d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 386994253 1250 386993003 386993011
    0x201021506150a0e03070f140d0c06031805070f060e040209210106030b0f09060c040b0a030b0d05031809070203091c110a06030608011b0c021201060b12040506010509 73
    0xc20200300340240b180d41c2296200c030310f807801003042000c10141c081d1003c0000380060414001310300e010b1424041c2c100c00301c03070980c0501c88c1310303500d201c114201240c80110400b080d1121483d0220340d803010511141c0800e16001c00041c540d10070488002020030041c6554030a880c4282e880700c1c200441d0008220a03802000c0790254421203080e4003195111a9441036405d0080d076000105d19999281c03103120981c603003200c40070004c040c01c4040208074001441529030003045403510600381070070288101081d02940401906169a07000e000130555940400140442d44c044122a0360b4950842401c490030100100c0501552141c000310f01c1e201e0021013510703d1294064003002591900442c1d018621408140c103594070383e01414021541c0d22040c488001a0010780c4020404610349a40e413802c40784d012126280c907079240003461070300c42d03030065020540b19011030300519200820035010b401045142c2c81080007440c0014100103503240100720327602c101e0081054030400e80e40d403000d003c5600001c82d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 386995503 1250 386994253 386994259
    0x406090e06010e030606010825021b100f14131413110f1308010501060f080108010501030b04031809020a0e030c060406080402091b120a1d0319020309041401030201021506 75
    0x46d405501c0780c2211a13001c20304c00c0d07015011028850611051225491440005820503c10b012507a10461400a0802c1d000c2e2080b0b1904004410300034020202860f0075410854580d5a81c05000c03103960039503000c481100303070807c8081d660380c480000c4100c2d00c4030100e010f4002c0f519042000d007964840c4000c83c1e0012082d05140104001c1e1f280e9072a44224038145d07003110500e0011034008004d21030a0702030071b19501d400b034074815903400140000c1c1d0305078001c00490381050b0050000501c000220381e00942d040c14042c4955039032107584405090141c11900b01988085584448980e0106105001c0c0d0010303400d036240c0441a0342407044603c03d5000340300208000d00042001410044019580701c00c2d04150f031001c8840004448042d80d10400407034102c403808409228030340c038480c070801e220b00014070101d09042c4a181c0e407894580c0520040302003200d0b0710909003070980b802482161400328009000308a281506000140344401c280400da00600c1a00150401c0d0014015407138040c030402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 386996753 1250 386995503 386995513
    0x191b0b102117071406101a0705100209040209040507020705211905120d020d05060d1203051315091202240c07061407020f01020a08060f030c060406090e06010e03 71
    0x20120b80c120380e60040404035002c0c1c804140ca442000c10502c8800d0080c01704042035009907150100f1421101e991045403d1180000c01030100096000548250f440f108580d01685070001900018001d0042d111819000343c10102008005175010070010261041142d052802c409500e825052201000007800b145502c4009401e1201022800d00b031000c0380725008071049840c403200c44560f10b80010702c02110351500402c03808104003c0340600ba80c41003040e2900050b000090b1100381030000750840171001e01d40e440000c5a017446440f9840302c03c094124108400d03c0c1110315031080104040e803408c1d980c0c40303020150610424070100f601d00341c0881d102c854414913404d0088503540300102511400c00c620081000c5000502d242c0a100d4260300203440c203020301d1038641c0c00a41400b4035200c120716907034810842c42d0764a6170414a5160000c1f825119454112000f2021902e4400380e02080d40c0d010001180015600c2c3c0c1c000d10358005e80c0d810403040665600c4102c01074511100e141040c503415006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 386998003 1250 386996753 386996783
    0x2316080601051513080303060406150c030815040e06041b05030304090c0216060512070905010c0f060204032a05030a0f03051602041a0411191b0b1021 66
    0x480504448500c100d1082035140ca0800f115404c400492903018a0581c2c00c080100b00482c649881050300038591202d041e5501510200014a0314072044401404c0c0000b41c00810b1a4224003925104081c00107441006202201c500e62584c8040881d404c885150b01001c0c161071a030042d07494001200c2024004500f01400c0a0014001d03012542d50403085108213003030310013101500f0361054010440b80d02c0700e0355141c410210104c0c5002c8010160028040212800c00031643d004071030004240e082410104140da19103400d4001e032042d076001401083d0700e6840c106050b0340681804107519501940703005040c0c2c0d18401e158940034951030180c400d0703a5074441c000210340544003d107840b0503044202c051410750b0f5400a0102d9001114181010602c0c420b0b40c242410705118240c806044141c9250610003130322840c1c010120f01c41c403400c04000d00c4540050f40000400087d240440e8400b555140714504841c030a00049903071f104500e00040c2c05c92010790b01d00320303070255501c480f50001113002c02401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 386999253 1250 386998003 386998009
    0x30604031409210618070b090105070c09141b0306040e011b1809061a0901050d090b1e060a0608070e040e0c1002030a09030b04020607231608060105 65
    0x41034400890600710800541d0340030343c0c0744151200c80441200c2c10481070800c0c01c1400e413410350010120780030045613180f8400540000075111080382c1090b0742c02980c50744e2030301c0100c03400e001c0c0080081140500c880c0200b099100c64125440d10b02c010390840c0070301d68881910240a040a202e107403d034150030000f007607090810343c2040d003038000504000301d910390701c080c102013881094104080001e0182c40340c443c464889071007024024084e400040c40481c1c14004110482e0340110050544090300294038003a43e4003500507070382e00345c194000400412645040c000c0c01d00b4030460300c082c6443ca001c2022161076900c04181c0740500f4002e407014a68506141040c0c80440014100d24180255582901c0d21665140a0300d00300c0385503070002d84540c003207040600250b02c40c50b14840e0b040d50002c0c4402030240e030f4080e0003401142c1d000780781621991190b00104000d0721520388080e200e04401070141c3c01c0d1a04051243c0c901d003800108948091941d943c100d072451880d806103a42c00d402c0900100103601d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 387000503 1250 386999253 386999267
    0x50a140c030703030903030f200c01200c0601151d0a050d03020a02040b061c05060d080c0d091a090405061504170d08070f03090f0b01141e03060403 65
    0x41a696121864011202031007803550700508022000280c9580d0200105035050054011080070841309000d007044507140307040c040d81d4110640350840340104090340d24440c00d400941c820031918460480c0b40307480804440241d40038004403080e500c107003000004d2a640701c4c000d50250002d20b5542c0c040302507004c4101f00183c1c402424051f07011144550125144e614040880310540c425002001305000c079105000a403550404442d01c1820244131106541540703c00a034204e40d40400f000440d50f030f070071000800082c025823020340411800300d0341906031035001882030800803403500e5100215030780b5040e15a044801d94014200410180000c00541c1130075004682c010000034418014869541420400c41d0010351121520940c4080c180d80340040500403a80302c40120326002403d450480c10140c100c0d0b00500d20350041550380d44450003403155040c000710011b0352100180303019507526180f80429000e040d00c840d119550300307035005054035644c8410b60350b5581c000e80640030365a10fa4074107442ca0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 387001753 1250 387000503 387000527
    0x31a0d080a0918020403020a0b03090d080403092403050a0506062712010203060a06020102070201020a11031609020307020d020c1e0a1a0403061415101205010b040501020d02030a050a 80
    0xb00440d0540030454507114254603c41c0429460010303102e42c45c500400041e101c080d8404000c1c0c1a0030030520041100109484440165904207034a07151141d2070222a5a00c895100c0080c1e046182c2010080d8824400b12210f810004e60742408151106452801164010341e005984081d0400550307041c1143c51070300001410f40c43e901309458042c80c1000c1503909201c00c110190507540041008030314500220f03444050201d62000314100003040d40040c1d52610170003c050039031070350a50400810365080288031070044031941a000134aa451180c0c6001c0c2d00241c1308400540100d070340102040b0300c0000c005644290040c0a41c80d0500303520b00303501580e0280c101107504034030807801c00300f50b48442c0c0703076015000c068001010381d81c7c92650070110100c442507117400042c80000701c18021030141a11200300c20040889100e03640b20807903001034502c0d001107580000e01c50705100c0000381b0b0084407000740085880030703000c0c0d0f444045022000c0340c0302d01c0744880e4540411410f001d240401e034400e03404940c01c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 387003003 1250 387001753 387001757
    0xc080127051503070b040501020f07141e1c0b01080313140a080f0606030705040603150b0102030c0a0c1a270102030706020d1508070f050d0c0504050412031a0d080a 72
    0x3800d1618000f00c0e00341002034100b8020690001410071040d40d041154913000d19014010384001401e10440d03000851040030091300c200740c04c0c0c81d039400c040e05401001190300d1004010145841e180300001500c0d421444054903003a007100d00000d00e1502c040b00311202c240b900d0030070070600e90a00c0d0f074100b040341c21110240c0e0000c031640342c00b1500910801984446550580c0201214507041003007610708030303c1c0d4106500642c1040010030000e9003016030300b07003403030000b0001145015200700104e140d4002d41c140a092071160388d102009000c2c41c1c12005080d2944c0444820f18100c000012410703a03c24060040c03840c0ca080400a60201606440188551303014030540c6c0c505107881c1c440d001070b07801c481002001c1c10741e1241d035a05a2140240520000c002100c09842054905041b04e20110b11781e1107901d009aa80004800c1003002c001c42c41d4001c8c0600030010041400c01d0308005400181005291000c603240500c80c900e0b548200003020109403006125060307400f0150b035086800d802415001c42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 387004253 1250 387003003 387003031
    0x51510022d0106080a0507030c0b04150503041a0109150806070f0c080c100c1215060c02120303010b0702100c120c0203100e100b06040b040501030203280c08012705 72
    0x554000c4c10302c1a001d220740100014802141036043c100c80c01d0055902400140354100700401151885460514003402c1c24140b041e00e80d50b441c00c0030002002c1c04150900f203000004004204041d066025803a0703e00440001c110464480c2c203c80d41e6280144c40100108490400c03040e10103100741c0c491000036214100d11400c0102014420303141240300203d96000390303154415400541d900481c42a405013911006021001c500040d0302c0245400740070b5042004041c050200654980000c101d840a428408695803903039100350104140d005901e00300c3c071550404c0c10703500445101e030b1600c2c030300540c1002d60300c2c1031049050019034058484640490700760040380e072941c07035650030352040c41002c40c801e034046c01c08016028440c104480b03403000918071964040c002400340c8040d1074165002c1d6030382030900580e603440302c801200c14118185a41600c0051045480d00303508610b4004500c0a00641c4414029988440c020840500390721400404400c881034007a25a420580003160059810201ca84c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 387005503 1250 387004253 387004259
    0x150e0f0d140a0f11030a03090e070507051203060307170601090207060e030a1713031e020f1906140c091e04150305060906062809051510022d0106 64
    0x2810840403100a48a100b107a40c03405090241d07610018041e007200302c019080400d0700da074016040348412701405294002200008600701e00500440d0f841a8001d0200d980780015078136502c0850740101c410398001d001d0b0000000d0310100f2440350203a9614090060940c603070034611440029080800240c4071542c640382c2e608844503042c4020107142c8455175501c00e1043d42007504107504100946840e1462003882e52300000f00e64060108001c80041c101e0100c0c401000f031008070b01d403042c1c00f60060840d0240f1000c10054811600345000c81d40d205086c00d000b03a0805a012810240e0102c403500f0482c00c0420900c1110f1621440115506c4481d111444e507440310300010404036004c6440c482d007c5c18010005100f440401c02c802e581c8202d031400104480e1800c1e8011509000301c1c1192268001c12804a40a101100043d06405891400d404229a181030b20784031100801c0103641a0280d0180000c001ca800c3c40400c0011103031414000e840d20401c03001c2d80c07180031002d40d00080b6069550f01c2c0408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 387006753 1250 387005503 387005543
    0x121407050607020c0108071b110306071d010302090612060a170d030e0a020a0303050a11100204140a0305030405011209060c020303090d0306050906040507030e0d09150e0f0d 76
    0x54852240200020302091400e502c02070710300081551014180540001000255640f240c0b0f800d01d08070703030714545001e00c2c0ea40f403400d050043c8041e071800d030b45401200c1c200018190b001c600c0d0504072000707041c01040d00c40803400640c120b1103031100468000c0c00c01c10a0110414a5148c1da075007000c000b13064501b4840ea1041c105400d1580a80642501d40242800800c09035050181094007507201c070207000544040ea0008503200b4070786c40b000f000d200c000305101c840b690185603506200a1008103541c3c40319817000d52807000790311034041e0306240c01e50f0f8503289c089820101200015240c0c0701e002140b910382402d00541e0310400982c252050140c035034105400040940c0078000200c0d225400441e22400c20809490a0030175844504041510304081048150b80d14015143c100708180c900241c3d503140d04908401400c0e00d00a0316a6511800b203480949030707400908901256401c5c01300741009032417203d044590303030414a5080c0c3c1c80441c0c06110200e40c0751584c4d4241c140d500c1003a100c85494040c0c004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 387008003 1250 387006753 387006757
    0x1b02030d020123130f0218040f03080a0239070f061103070b040f020607060c080a05070306080c13020c160f05120604030305090c06040b0310050a060c1214 68
    0x3030040181d444045001100000000034040500044440f548a1808108124102e4070148001d0050f20000d803083c015521135000d120940c541100605143e460181400079900ea01403000300c1c00a484a8001420080a4401e40d0248942d0280f100a4103a0a03080c04101d044000700000602c07540d046814051001000790000902d001151108000d103800406480002a0003042c541508104125000581c00c14006c942c42036000395035907850016400807400d2401500340051403149480f8090001c1074029500a00c03944601c0d0050050740d0721080e040f001d9a4403449200b41d5a400024020315501d000c074015041824035000050400001a0046150501c2003d000703005001c000001e1058003c00786903034026040556040000c48115102c1d0365035400d00900141c200f60352800030501808060000c401c404000030141d0b51115151240c000043c1d10035211030b0540c0004507000100382c10414030365011203660b40c8a101e24a4000c1c0c464001c404030107090701040050300c969607180d0300d40d0440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 387009253 1250 387008003 387008023
    0x170a050d0b010e030d02010e061005010906080a090c06050912010b0d0f0218010f03031404050906061c020a020c0405060f0603130c050603010923061e01050c01380901061b0203 77
    0x80082803910311008071034103011015118401c582b04a0700b0038800740e60866041f00441e0740c586800b001943c0d03018806d0008000850f4001c11004000b100007542581c4540503103030307062003159540c11601e40f06401c103080301c45401e40c3e0b9800c00303180c2c0074032000300d01c03900c6440c0100c1d03001800400b004404004151400b0303d00b43c009020407614410203105050b84030a5040f40240400e480301d1170b041c14100001c00004000b0b11640c03040c0c6001445903c10600c052134078100c03450051040d911034013866000381d120000d18500500851030500065820b150034410721813138a034094121451501e8011013110804410388094980c0544800700141c10384842c03008500910030800000340c1d22482c510007c0200700300c00c2109901c0e0f0042000d00c022980e079100d100f040d0395000307032040004501c8413006071424000c4100c0b03000c540d442c0118603007040040c040d280104099108041152140c0d104102a80308170400c00c6a401010007001444072038050700300d401e1413508841c180886134000b540000c2c980300300c903d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 387010503 1250 387009253 387009257
    0xe06040605100b130902031f290708090904050316030210051509060609030a0602070b1f0b07080d11070609050d23030a021e0304170a050d0b010e030d 66
    0x10100103108440b014040301900300000400d180214902a07100f0307401d2940642d5210a9002001c90a117001160440c0c0c0004518014040619a52500c1d802e010441240c0d03650308504c9940b50f58840135848080310f80c01a40041e42c00c0c00c0c6040b040a000e040c51008004079545d00c400c114003044e41503000407500306e05110764010200d81c00b132a01c04c20b0135190f001d004650b0690000f022480e1580d90b802500340d00000c1500c527191101203080c0017070b240508408001e01f03050320000e120000e0100c000c1c1150321415071100480070112540070b19030003821f0135114440410360b0620006c0005044240100300c183c00031034000c125041e0a02d0400b00307503446460100d550075521108001040b00a00921040700ba41d8182503414007101c403030820301c1e1507110110b000440f800000056184500ea8103840706500500d80c1c514440e01940f17860300040c3d00a54058860340e405071081c45d180e00000080b01c200c101c283d602e480c2801c8160300e010019107250555641404440c914028080d1010880400c0002140d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 387011753 1250 387010503 387010511
    0x30c03010312050306030c222406080412081b1611090c0a08090f0d020d14090609060a0201060302102703121409060403060f05240d060e060406 63
    0x140740c0200b02e242d041221000340141803007041042e1354049404005094151029003500408080560b0b80000b00002c8401c868030b84012031034003400c8213100d11020500944030901050311000c05803060401203900400200c18000b034880034a11030341916400641c2c2e410303145e807000e9500e4102d04054004410706400325031b01d25041024044109008101080c0950310703501030b410031804440140c4190350071001801151030104d442000704012104a04500405903810b6000e200d400030b48a000c54141000000c11000c4125030002c2c0f40e008a40740c2541c010071981c5003e4240c3d040c4405070b0032004d06c010070341d5a2140000f0160b12001d82d0001c0903a055507500310190f401d0168295488108001180c0e04082c01005000103150f0741303050008081d0382d0504070040704640341d000d0f213548600c4c19155084035001c1000020031030b080d080300f203485081e02010310485c2d07141c8014502c0750b40c44100c281244034104500141600709618031005a6009600114040d041d80380030300d00d020b40550381103400c2d03595 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 387013003 1250 387011753 387011759
    0xb0c071802090f370e04110102060a0506030a230106030b1812072307081e0c0f01030e010908160c084c0c030501060215160c08030c0301 60
    0x11041185800d03800304c44800c0114805030102c044402041000c0c12003030141c0340210082022800b01350020300203207040144074601440c1010883c11440c09582c00f40c45010041225085940030b41841042d016009120401c4a61070700c03442460003c4003802c945c0c0720901241030700701c02070040e04040c50050700302804a08105040e41080070080403015500d800040022402890007812501440e8000221621a000c000c01030017051010110b0b0200070f00c101e41c4005040a8085103c15a0704107071243d130007418002150094860740034480d06c503840101d4801d424810b41c02030788581d0314018149c0000038050304a81d40c2642547c0116241c00b42003198200c00410841d800c1c4055000d400e54001800c1e0306800801000851100340380c61101d0082d100507240e04241c4450700050364841c1c0202540300702d03410b0003913640007001c1c925011030020742000d00203d40c05000145030b010169120b644002d0030b60b9481d50101708a00c104204030100280d072482074021500100c091030151441d0700545649500d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 387014253 1250 387013003 387013009
    0x19030504021009050114030402040b060a0c0b062b03050d0f060302040b011803060c1205070e1801120b09070306020424090b0702060a140a021605030a0b010b0c07180209 74
    0xd4100340380b900b08590700b00c1c2880541d80c415840e030800c80b214099903407281c4661000801910f40d040449400c104041081900c02d980012580c00103400b89250307c4040c5c4400052010381109146082c001d103541c2a090361107406c4d200f4080c4200da00074903081c8d0a143c0302c00c0c40682900c0400454070340c082e13100c240a00962400e84a45004540b090a203150525001c3d40741542c41912448040c0003d030380c0c1c80481940340d000e04110070420341f0541c2c0400076481d14050140c80e4010358038450f0301540403545400403d0b84100c1086068840e403001501074880345590341c00640b000100003040e1030007600000000601c2c540050300181003444020554020310100d4417590100d07140c40d13403041043c4014100040e0070008104c852154069600c2d654480b144a41510b0b02c1c66a1000c1c003801a00010f80c00070450b07400701d2048180d81684118002141d030301c60405543d401000700180012502c01c004000b010203040062a804201c0020784803c00c0d40d4517210b1070340990720a2070740d02a9400099071105d40c030b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 387015503 1250 387014253 387014269
    0x2031005100e0f0108060414010b09070c060b090103030509040c0c12030204080d031a010c08090910080c03011e0c0c0b100608090f0d080c04030605100806060907231903050402 77
    0x10061200f4292075072526514035030b51350000d080681102d05800030681122420340000009550240c80c043c46410074032030007005200080e4040d50182d03d8140000341e1840c1125130941207a8050f512282032028480c1000000c0c0501040c110501c0780101503d000211710303801601c0c15045c591401a00d5514045c0d0242c14100c0c042c24400815240122800c40c0400c07020704002207580a20300085182c84500c1d00c049a0302c13404100c2944010030004110034500c018101e01c0560366000f0503582e01d4007414040c5400d03540c8a070054034501206000000e01208560f000340301e45d4901f4075140e88021090f44410b40b030000d090310861600d40c0700880a001702600a4820703a0415503c50080c10a11803a00c81070ba160809811801c08001c88280815494544501958040d640005040001d8144409100e6107050544168000c50003090009296450262078551207000705440304607003107030041141040300d25400c0c00d004045005101c20003519009284011440c81141c0300007500f4101401048070523 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 387016753 1250 387015503 387015511
    0x1b05010501030b0916030f030309030302120a09150209090a02070c0302060c0709050114030615010e03030f0d0c09030206030a0c0c0f050f1501060e011119050a03110601060806090402031005100e 85
    0x40c5504107006c0001480b82000e110301507800d4500001e0600041c5000c8010f8072072406000840c510100034407030966400c0e130010244501c41c0c07079034100880c0d010b071408003030380541c031003555003c4042800100d400307000c1d070018914a88035030542000e00da00ca500003451908100300c00d01469004c2d090500060201d0310455024040d074407041c007040d60070300000076504c40c1c000f89002544554000c062086901603581c1c0201848000d00f40c90321091036150040386a044540d2102141e8100b03a10215420300455014068980242c0164a541d481080e060042d003212101d100804c0004400900850700c1d65480c2441a0320aa01810311250705412141c40c000119100c0c6061040a100400450b42c0090984010030001e092840790103030205191403e20080210b50003001940d91104810006c0109406110902c65110440a48a02c1021a0740c0314400d0055501140244000c6281ca1400c0340400703903c01d1008040f0b49505401c0b6062800740c441c141c0b50743c40621500c4c90709010031071071880ca103540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 387018003 1250 387016753 387016783
    0xf04061e140604140d1704080109030201110901020a03301e0c09060c0201020f03041512060308032205070e070e01020105091213030c0b04140d0f031b05010501030b09 73
    0x405040c885504040e099a82c2c0080c0b05032251039a40b0108003081402d449044003078500c1b1900c46a072070f00206e000e40107206080300194a0804c000c2c0308401c2140079501c000304180d0040c628402c2a0b60191100c1103206040030074040900058001c11041c081079002c0f81c40a0300b004209500f040c146403030314124105400c06140d081c851a011240d40c0401c154086604520f1324070b4280c04a400141d041203508003000c1c015000002d8007041007249090075041c505520b668402064560700300380d000701c5020b40030051840c001040800e003400e0784114002514614113002214061083c0c0d50249003440f5070344000311081861081040e0345030007244e071890b061002c1c002403255191407801c0d2616540014515a2a0080400d1094900308020590000b031544031201c4191140c5440d0105942d4015118020402c090b0618a41d29814074410741c1d1007031030f4002c040750201121a5000d80c0c000c254031082c07408034a0340e100310401090f000d00581e0700845c0124031003811403c08203411030030b240451440d03400d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 387019253 1250 387018003 387018007
    0xf0212030703080a02031b030a0203060f0603040b01152007090c090b120c090d031d04020f09090411030706051b0601151206030b0108061e06030a020f04061e1406 71
    0x40031a410448403503001c05001d00040c1d80ba542c402050f900c51808080f80501e5047c04008c01c00c43d5009031b4001c5000700000c8400b98a2181c52070104103841c0305c02c880041c101001c0380300400946642d26079070080d82070107080c81c0a030420b0107020980b5140440c15882559071000d803041104410707520400b00b60100910346407001c1d9081c90302c485c81511903070303540c42c521800241c0010940e241c7d040a07a4400040100500c480460380d090081c80c502c0c426180e0b0f0302002040031507070210300d45842100c2d041c0700090300207828041c00c001081040d1000a0007078607000009091511690390920404c40545800e44409071659000c140e100c4900c001e2004102040d03108100501c812103001c02c00e0311102043e80781494013032400b4040078010f400e0640c4000d0070005d0200020842003c04114540702d06480d140c1d4955400381d0b45002d0840c00401d4840c1501500500c51034409420101c81094100601a05c0492a507a55401106180e0351024105000c0c0300309150501041d0f9036428040294001210054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 387020503 1250 387019253 387019267
    0x120b16030b0d080d0204030b09071701090b04020108060102251a04080c131509020c190c0b0c071a0705070602030301081911040c2f0309091b03040f021203 68
    0x50442e030500c0401500080000c1a4130300036180c59011500619400300151400382841d4650f95031302d43d0140161032400140241080054405115448070550440c988110544807a0015290401d000c0c0286045003d903080c04000b0503518881c20780c5000401066000705c03480c00031490034540c01c94164402c455400c01c0b040004900004050035901c2080b104c0c2411244074180e2240180300041c0d8550303843d144200300154030703081075014128450525003034038613000c411021a03d0700300e1820001003903051907030010301c0010f0303406024000700079001003195941e648030040c01c0c00c10a002d44080381013002c0000c43d101000000c0c0110001045e1a000035810340d4100521103032140300c588010519042242003180a00c950225140304140018008000c0c0c00030030f220043c44685904100b48203000061414041040ca001c1c40c6000c222106010714140600581000412003010b080b403500115488001c0034040c010340000c50245105a20541d0210b0a51042c082c101104446d00e107020381080c8440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 387021753 1250 387020503 387020509
    0x306150c1e0706020f1c08190c0c0605010519420207080609100902011b050732061308120a031d0303041b090908121302100e0307120b16030b 62
    0x101c00c00c02c007801d11005d10303a914025800d07081230383c903107641c4004e0905101d89506904819503a250f00d009a42c00c1c040d0341c1c2c9520600003141c030324500090750b400282c0c10410180c10850302070652080715400500040d002c4a841c4451032500081d8119104840e8042a601c2c07601040352100031b00541c406049145050303100e0b00d466180e0149116a100d4072143c02030216072288901c0442c4004c0e580f000741c105841d6040107540d0346068000d1000c0d0002013110361300c0c07860b14403610034030710400c2c400c0129000c101101070043c160040b011040040b01c5000c4040341007031041c040b0075050703a4507189554495250207070040c19200c02c40b55008105000d824140c100c0f81002c01100c2d03216800840910b066401724103800c0a4040d00d1b80300b101c100d07141c14a040104290f160040c0b249503981c54440703039280c980c551500704000e0700385c0c0c00a40c4048084a10803026018071095070072450010300307807001d480e40c030840301061005802c000c88070700700d9640c1041006800c10b42c10105281a618007001000c4164000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 387023003 1250 387021753 387021793
    0x60e1504021c110411030702010f0608031804151d061806010e03071e090e0c06040303140c15041a0408040614090301060611120306150c1e0706020f 65
    0x52400342c0c01204041400f4024580c810000c0104042c008100c00310b40b0800c44c113a240c0090700d181c401035081042e03130b401c8840700f4040c0740140c447c407902652070f240700d00400e11240c032440300e0029040343c2c0311812000e841c0800b082c00c0c401032081c50a10f1a40341101064030f1503000b00105010303c0b40c080140140352414041040c268030650070700740700d40a181441c0000780b80000e603600003030107603e40d009100546101013490030120b442c0c40d001403000d840340b10040ca4642c00406800c5400030000c3c081040424400c0328030300300000c1000051032402c1d0705501391a042650301340c04029032442000a22082214031030440581c2c6800c01c1b16088103040540e00c0c00b400d4410341c42160100f000ca4814407440901103000c9440545008000f00141030b0b40c1d40025102c1b00801000004074011070713801d01c420440800c216032265400904043c2c16204500c1c000020f0f4210561a612500c220910580ca07c00301c81400000244184002d240941c03408000a113002090000186150040d4020340180400903030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 387024253 1250 387023003 387023029
    0xa031404080c090c0d1b26062214070915080406110408060f01051822060603050607090f090603031d030a08041d01090e0309090a020f0403060e150402 66
    0x5550490f54441c00300b080d1080c09450f05154440d4030f46040301c0381201c101d0700c58240b140001e440f40d2030240210100071201441140002c104c94500c003000600d24507014001400500018071500c100d15803501c2000c0071242c454001c403000240040034008a103400100305002000181058002d002d81e60314000c0c07418001410041007942c07a0111440e0064900c415034028040b10300c201c4019180c001000a0784110078411240a07140204171a180d1814441c071151081c81503803e2000700b1030700d0320780301e0b0210080e80d0801d64002e0703964040800020300a01c12580230700829600c00c00c07420705203800c0c13040d80140d503845420104d01d001e40400c0040d070000146e22a01c0c095240074081004128042824080c000c00010040140003030f0228104003a000882d001511544400c01141c2e00c400407a000c80f45038080300c100c00d0b1303c180417500c0c203440c0030854654003046c115001360030b102460400d401c00c1d030480d03001207900d540c0b82c0c55949840178007040340402c4000c140140090a040a40120f14000f8031030b9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 387025503 1250 387024253 387024259
    0x180f01020a06090c080318090c0c061302150d0f0e0105060307030602250803070305090d0c061d030c100f0203100b0d0b06070b01030209070c2001090510020a031404080c 74
    0x31001d4050103141c00c1100000c05d003080c1030365510120100c080c040386054040951107242c161010560038254001550740754040c80c001405240c8541040c0300b40894203800481c0d0020080c5042007019481e4009850220b08602010035480e4200e400321041c1c40c10f52002d07419a138035000030000c0940e0001641d80c02c50307030049001603441d46401c60b0702240e41c127400c900c41d00d8001c064074108204590706d40207600ca024150b90401c10354075400c80f841c0e10742d844011000300141d40c030503000d4013064082c1e000f40e0004105031416041840b0034040182550003084060141e0703000001d842e104a1502d000d0700c0042001018110f00d189041d880903000030318140520411a0b2000c10200141c29040d4021440600010203807511240c6a240031002c1c01024002240103510031400f00700821302078070003211010742c407070346640f0089040203004c0462314840600c141045240f03840042c441e00c3c0d00d04910308802c0f50354080c015004907401e003d0040f00407071800c2e0f0501c0604000c100a4404049400030504c1422 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 387026753 1250 387025503 387025511
    0x15090201080a38060301030b010612140105150c0109050f0d090524040306021317030a0818070f0902130506131e1805040302070527040c0e0a02180f01020a06 69
    0x200c0c3c001e565140080c2d08070500000110034890a4490b40d4100c1c1d10760f607142e0031803a503c030719118152001c1030500c04950800c00014445468112071410030302940c6510182440148000182552502d82c02602c0179000b8940c50212014103011000c400001c41c24480356442c40c2102044d181120398801c0581100c0e55450204900b1381c48084078029600b212056441e1103c404245912820764400e00140307c19081d4408801800071054030101c3c810358440e03151668455040304000c40302e0840c4460907016040000c03d00c42c805100d006c0c00750003852001a201d4201e9038000c5280d00e22a0021413040806001c00540e8000e960202001e907506807560f0540542220306060340444990480015400780c19080302d040c1109620280c811402030303003101c0c0305c01d603035000784080390200001201c403810540203803954039001100f840e83c000d840b50440500e0a80e41c1c0180c060050800d403000d0840303940000e001051016291245851013004540d668890f107040310000c5e6031000d000308020800d43d16 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 387028003 1250 387026753 387026831
    0x31d010207030b0c09010216060c02010806041509050613110706020c011509021215130b0f06072010081906051003060e010f0312050d0915090201080a 66
    0x30900034031004680c002d000e00f500e82002e41c001030107608034041c41c42c01481852840c840088402141400311510341c0c50750002800c46030011220307040e004100c203030402d4580320140300b0304000c201e421000f00300002001509080c00c508220544415402000f840c2e8101607800c6d00b030054010840702456849070005a8030b060324000e0300d0250246120844e1100c100300300004607000030380c0003801070f01c0181c80b1a0105681d035a6501d80604600d211060700f0900080c080068281c0c1544514103407240200b00c1d03032080c40800c002442c29401948212051001c3e0200100889405007032008140012540d03480c0f00b4042ca64028144000100f1003400c0020000344c1140380003407603000c400580303000380120360031421044026025200c00d1113542041481da1000062410100c0142c500703172980b041c07442e0030040410b4000c640c207401501c1c80c058021303500c030002c20004240d2001c0c510b2080c0b0080c0e002c600c02c000e41c00007420b901c0005180140e0709044c20410321007400351060301c160440d9010070589081c0c3c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 387029253 1250 387028003 387028007
    0x2d0103080318010f0c0906020f07080607030b060702090103030e15090144070210020304080906090120070905070206370207050709050c1c0207020d0618020319031d01 73
    0x507428038800c5e145c40c1407481c4c002d0384012014140d80347c9400f1130385181110300c42e5030740d110400c0c41104815082800442d500d544a07401c100c80d0a10014003060801c1c02c2f0f50000b4501e42003e80c011400700c0c2022209060a040804092046280207609036040041d080006442c86000100001224140804600d0801d91414403a45200944503081c1d400c0c000c0ca00400751a14015118030000d1320071015020a001002e0003100d124507031092a850601e0b1014050003165040300c0081410f100e05100200c2e4a0203941580100b000075503001407138045e242494400448001500020440d0020010401b01841000408680c0311109030120401c021803940403901c0b404d410034103150140002200020700200144002c20b4a110f40070030000c85d1221982c44c401d512540c501100b001c2d1003140f048202c103c4541c080d00340d03540007400074084c0250b640d0344c440c1207a2500f1440700621211107020825420104204580410803841c41c6100151a8074003508454000c032681d0103002030168540da03164 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 387030503 1250 387029253 387029261
    0xe0406091202161e1a160c15030b0612041e03021501080309090c09030316080d061403070504020714030309073b0703142d010308031801 60
    0x790001e140c452142001d00000703442c0c021540b6000c0c0031801c0c14101184440c000d52580800c41808101c20002c94607095001d080c2040d004284900802c05010b80d0b40d040d804440071607040740c07182c0710b01a90341d820170300680703c02c1210300d40c08010185001c2e20142d580c6c65440c11160045003407c2d84607240d903141e1a090b00300c00004000010004a080c1c0020105a00007504820b2030b01c0c0440944801e82e02c40c2c88460356402480c0b40940c2c0005804040382d94002260004c2420040140541e80390841c001031929030004641d8007280d8010700050144c20003103041c03240c0c501810000c0c1c180c802548440000076501d10060080d00e2140c6d03400210b420801c0103000e04120196455801d80781c4038500400a01e44810851080d224000b43c4070041701c20b1100290400c0102ca42d80114103400100b03003200c400702c1c0c0300e401400704040c1903a412940210b000c6040c13505101d211300e0000303500b0031224401c00b00980a15461900b0b10300d5080d400520004030000c041e00d130721100440b00342c8104200b01e44101d000d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 387031753 1250 387030503 387030521
    0x40501110f0316110402070503070f0f020a0612050601030b01121806050f01050a08030a08040b0705070c0803190e06030703090f060509012304031d2d0102010e0601030c0e0406 77
    0x51100140c1500000381143c070036042c150040c1c0030480e0080009003400140c0c412400c000b0655041001140c00081c1c050f400c1e04111801742c544482101c16a40c085180b290854100c00041010080c18007440145400366940c040400c0ca8180450180c201c0082c10260b04401c0100c1340360307200e001c1c402041d8a03600c04c40e02465001002442a410a1001d12945100a01503940101d50100700429010030000c102c51103281c09680c0e490f10785e83c40b13031501801000003034140d0041142c108106070104d40103214900140807000061aa07074410700a200c071501307515160480078880040b08500b0256130701d20580c0d40c002d04a0901040302915882c154001c01c0c0c030a84024084c40c034003024455000c00540c0604078015144c6510102103e400200d10f10b10304045a00a0020b17040c0400c200d80115038003000025890017514600681c81c14200a00c0040d618110b6204070540a036214190b941e4240110a1160b90b41c202070072255055888440040c42203005c5c0c02510511180441c08200c0c0703550082c00781c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 387033003 1250 387031753 387031783
    0x617011a2502150f041517150103150810021b0f010b040f090b0402040906020c0a060b0306010905010308040b09150408011d07151d030d020d02071a04050111 69
    0x7005203a51210449006500307402e030301405400a00f0389450504008440755030700009421400c00b894243c159070703448030b145a01410032070312810451128a158604038002e4501d06891044848100001400c40c0d01207148601851220201000744810100ea01400444203e0001d83d40b24401e9400c0c084194074030030518440c1c403a9801160640c0d4041d4441a03840b8421a014010358040c8000e00054030810720000d81003a184038041001881d0035030066004074800d400240c02c00034003000b007a09014201d4416904907445009032a01440c00340b09041c058049030320b040080d5411500c03000305900445c000c0b01c1c04814005040001d59940c40a0042e5006055003c190340702e4450528030302800b03045424142c0e12000b0040c0d96120003001ca8a034060340d2240d81d003271800302c50020303080f20308002680c00050b030009102c50444641d28244a47c0399403803a141c0041c0469250620000c0c904100c9500a129040310180440642031644040f58101d910910b000341904112440c103134213003201c0c0000144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 387034253 1250 387033003 387033037
    0x903070506041512022506090204052d040302190c0b0703051803010e06131712011a040e04080c01020c0616090e01050906041d0d020102030a05010617011a 68
    0x280e0f0a0b0202e520509004540d07894400d0708102ea8000b905900608006510043d03864424503008080420000b0549004600100e403645d4140c010070100d40081d50032181014480818128820301382c1404018640d0118641e20301e0b207040c2c0c40080d1100060ac04110102030b00001c418180480e000440018203c0344101c296540034034074015100d030388600e0545040c003011400c0202149010703c07a07941021640d401070715880c1c0d00d150031801c034600c0200044030b000e400072a60702440301c0c40c807010b801c03101c010304a100c1075941402508404000c00c1d1000c00007403801004280b1520580d08a46500150f11101d8191200c3d0cc0c91106806804ac1c890110303511b100d0101003101c1c405c0322510710710074400c081c0c41d01e501d180e480c1e4031801204002409066000b88440000c0380342414594001c0350140d41c0b1038a55015214441c49250030400350712508001070b034000c4244403510189105079070041c0005e00b403401c4146541950a8078250341403160100322150a19001c4003001c0c3d041c12128071180b41d110100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 387035503 1250 387034253 387034259
    0x402070212120a031407210e0f010f0501052b0305092707020109200a0e070e130605090604050c041716080105092a0901030303050402030c0105031506090307050604 72
    0x103500b540240c200940000d040c42c2c3e91880b24200d45030154050007465541c081640304903814a8008401d002981b045a9660408401510024421003003948030810002c03483c090b10180d1101a520103130000d500c16801c0b4002c82e003a50f41e802482c011071100d40445d0822000711404d042d074050244400702900140c40c4a101500c00b4888580c00c2d030100c610039484210780d2903101040b03081320842d0000428030708407204c891603807044981e400d00c0140300060084d803002d5150310750080119001d548540202d8421100882c05262003441c8543d2b0200f1140304122883c5804001581510040c0015020f16920408210444107a81c03c6030b001d030034480c20300741401899254142d56401c54555a62984415040108042d0410b0203968002d20340074008040c10001802e0080451441e0400b4000c10200000e01d0001030b144c00c55050f0081d8020346002480345842d005140c02c041768240c00c2070411a0400030003400d0301311104801038441058510540380d49046c0003003481c16006d50007041d800308000c5400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 387036753 1250 387035503 387035533
    0x18030602120a2405010c0206041d0708070e0901030602160c0b0405031b0109150306030c090504020111010b030303010b090f03010f15081b130b0a06090609050a03020a03020402070212 80
    0x1d0082d00e0501c0c0410090452514090035a810803801034010b0001c020301300640e40c4204403591035540014042c0385001d90341c08a40303010100b500222181d1040300070812010a4010040703a50004050a0101c101004840010042c10050100510790707540410125449500e450380308403000c0c0d200c4e0000b040c0c691039130002600d9402900c20325100e40314840560310214081c10000002d01d4060b15402a010b0800100c501c100b170fa480060750426580700070000c041001050108002c040b45100000d0030305207400010800c5000e24682c446a80c146152340d11203071400800c0785d045941000403152a074003541e0000b1451543c58900560640c02c0c298901500c02c0b0ba584090303003050440c1d182130400c60382c0300b41603034a0f404010f920900440ca440712450060808070a240ca00d069110000035804844800203030900085410843c00204161350a0140b55044003400c0c01a10080f12110029881c40d4002405c00395a40002030049801040110031500da00c0d1107108081d034984207035000c0203040386c59 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 387038003 1250 387036753 387036787
    0xf1503090c0303090f0605130608180106092a1e0c0213020904050f04030509040c050d090b010302040f02120a020a0309051209090601030e0c0103150b13090c0203030c0a18030602 78
    0x10b05c10100416810004106000f24100c492040c610414035100b41d2a0a80940b550500100140310305125001202d006074801e10490700500314114000410184116183d600c940d04000800414903611103200011608005405107004030f00034841501c042c440406c41d182c04c04c11900a41000300301843e646400100d401a00250038280c0d420002d40d81e9103070f40030001b04800e68018000c944104504041e60815401c816480d0046050261415600601203000c0b1140180c0c1940c420f0b6084006104518181c0104514038001c240f095007040180601360311955800740582d210313954001020b000c41402030708003807031144c5c12106454854154121140f40703580502d890300e01c5903440354005243c560003031280c00d1105800a004043c00000d540054006007202141040043c250000018803008104020022400c030f0420300c401d060301c0c20001c182911030003840b610039900203004001c0300031388080c250741c1000da552500d880c520021849241d0a8803050700f000d403a180c000501003004800c0003007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 387039253 1250 387038003 387038009
    0x31b0c040c0306151701060302030a020702120d030e0c28031a180106030f060b220e010b0a030b0f04080919081006060917030f07050106060f090f1503090c030309 71
    0x1007204100780b01c070003c4421707164051111408500c024014800f0a210b540999030280e4039050062524495400090000041200392010755214420035281c4581c14061900d101150b00c009180403001d8000041e50052811f0740005000800c03240d9001d250704440fa40d000941e0030a00050380483c0c6642408024001100c150b0303c00b1141600a219200c0148a440c045070f0308080141ca02c0f03041039450401030009024a03d034020300b004201d03451334008010320340c0030061050000950100209025007516a0424541c3c42850144070400200c4c808500c126803050800400384802d0b900c510b4418651b0046001c00c9070040e05441081c80e01d001c400c0c00c1d0703105581e04c800454050b000c00850007402e580d43c0e401160006076280ca81044100580045c00000c004200f0a99040c401022044581c94204800a0f64240e440320010890542c200026221030f02c800c0c40d255480c41d00707140c132004510320b00c2c1c8180340742d4180c403000014003540b0980c0009a480d5100c0c03241c464003680c0342001040d055440c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 387040503 1250 387039253 387039269
    0xd020d0f060909140609030405011b0c08160f1401110a05060f010314031305040c211a10050f090a210b0a090507031103031201090f0b060309031b0c040c0306 69
    0x1030341c401984c00300050f40c2c0d00c07403220352000f14646401d000044400c1d0220300501c0840d02e107041c900b040060514034801000c0c04c290b50080c0b80d40e614010948910310740591010203061820181803001c1300c102024070200c44000c0c20044083c002011515207401a000001b401e640250301c00c0c0420342501518441c101d0b07004100315100201d1030200e0a8592082200601d01103120840030040d03420940c02c002101c007450704042602004140d401010304002c2d804660941380c1d10f065804004214807100344280c201030700d1030b10307802d880c40d2400340281c442d282074141c071404e010440c864180d54001004000e001c04505015002201d10f041c0c00c80755002241c201c44140e0304400007040c1007158415401d009030048020301c1050714544a41c0030501d2501c01041e0503000400000c0c6806611024450080140c11000651078042c80d05d150101d50490484900c64039041080c880404400002d860183c00303151a001d585445000440703280a16401905030020300344061002c2e500e42603400402224404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 387041753 1250 387040503 387040523
    0x120601060e1906020c09070201061e0f06050313060b0a0b04081f0b0d08180d030f0e01020d12050a0b0301050705041703030105150c1207080319110d020d0f060909 71
    0xd8100c00b070346078001e07014140059012010f800302134900f030154039411078014000003074405e0301d0300380701c400d0702d000514200041c140c2d410b030030482c0144494000d402000c6a02d061415804e050440c4800c05c40704401c007411054541810181c0d658460f85d18100030040700c0002a95603a842e4241502c60201c880321042c20018039880781d60b01c940501804030443c03001008110034031460f075210410f03a0003100c18140b00303080090600c0b40755280c0340901c00c54140281c9601c0101d100c0030300000c18205020030207604541090034140c000e55008410000c2720310404c10045004d907642d07443d12008100041c5520b038958204400c1c494800e401c04018005d0703522044e401c120b205129002660b0b2440284102c83d0425190303107009018850410141030008280415542881803002040c4902d4110302e00c2a42d242e00000140114100000d4064445504d80c0c4d030140711101140524120300d0064070380c1d11100342d0700000c900200100f140c4c803d03c1a0140310b00b00704050341e210380801c4000c0030f144600707c0c0c01c00c1d91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 387043003 1250 387041753 387041779
    0xa031d010504110d03020705041401030c081c030e0114040803010504061a160507030c0b030a1805120a021501030b090607080c16081b100b0109030b01090b120601060e 73
    0x1030051501c07a81e080500031142d0700e0788000f07104c042c10a0f44000e80840c0108100800c2c00d0360369001e000081d41040140d24000d50550405090300b480740c0d80062940c2c0c1c01801d03510401f110881e1a440d00300c0060070005040143e00a64601401004080c0c40741c0c040824100410401c8030800b0358141c03207050b10104121511101e501200e0003071225941c04c240c0d030034000e024102d60a0110086410b114400b03580a155880c0e548442c0f0000f1900325a481d40350100c100a00e00f110780c81103c2c424241006280c118030019201d242e1114440d00440441c1500003810f5000740d8000c0203d031540c82c4030803070100401e680d20305205040900595042801d8050382c004070318880e200b50b42250003034103400c4680346411100c0e650000201840b20040310400c400340101880b07000e104c1402c0c140d08070400d029241303914402020604030741c416500340d070500200140030b02c04a400d42180b02d040d1800b0743e0000592101060009056441c1307810a01d8091103907000220304d459200b102126044000d490910038880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 387044253 1250 387043003 387043061
    0x70e10030605190c0c17070c080303090c040f140604090303020415030e070f0b030f040c05100f0e0a12061109040c0f09050117040f0f08030a090309050306070206010e0411060a03 78
    0x866001c0e0075886c0382da41400042003c20003c0401612032440021815035480d401c5045800850703820f4525003145d03000c4075083c01d160086510489070217130104950349108282d4400038001174400b50080d50340c0c98894080501940c116000340214001506801034001170040c042c16030810102d005000e543d0b00058010703040106070055500c102482070850752804520b0030300d083c00500507980c00c4907020300042e01d510340345041c020b13501d05692581038500c01d4039170280605262941481c01a403c0003010000e00300c81c00090080aa0701100c08529a207004079180c104c1d000e200a0150710500c0c00c01c8280c0880e401c0344021603104515120040100c0d1342c0c0d00103480d90542460f07200d0085840500240009022802d80600c041c1b1031414088111000c0d101d590b041d8108031401c491042d56040132000b03042c2c11450410003840300b10010800341c544014005e480d40418807e4034483c00d42c00b0b020504000b40344503d00300e0701c1e5000d051551911030341c0741d009010301024010f40342c0c160300c82c2d400c3e541112 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 387045503 1250 387044253 387044267
    0x27030c100b10050d0f05070519080127090c09060f0e060a03060f29030f030304021c050f030a0305100503012a110313050f030f070e10030605190c 64
    0x204000b0550340c6840382c1d4560a5540d0340c0140903440c40c0540e14190003801160b0307031050314011a499036400d0748031200c01d140603040034500b903002c2d401d000d0311400420442a80d802c00346007842d881301da4481307104a008605809400001c1c001000c0d20400040418544804d500640460b0072002e00220381555900d00c1c45460700086d40e210fa0001c400100c14008101c0681000101548045000070044c05580005102c44201325a00342d0548984802a289107410000c1c603440f8038404024603d10304155000400c23164081d030b10544039464070068042406801e005100c00d40220700d043d80d5a8400b40704000740206000c0303c07554039004401c140880e0741d00341482400075070541440e042c6400c03c2d84441c0b0b41944a6010014020030001d1080d03030030034200a2000d844014a800984600321341024100718074010150092400b036404009030781c03482400001c000040300d110862050340c0ba222450070719600d84c160740002d800a41003105002480c4081c031004044100103d0b4100030a0101030400c40e400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 387046753 1250 387045503 387045521
    0x8010614070308041e0c030311010c051c02040b0a03150e0105130b0f030a0323070b0a27142505090606040302040606051b0105010609060827030c10 65
    0x900410300500700024001d1001c0c6400c00d01903401095510a000b540c2d42444d034a4a000f154140e007030303601c02c100700340c0c1110a0170703c0a421075009014854103000c004100380281c0c031584800e10301c0200180c00c1460503604840203000b68030310941d40c803082040080c0291160340c00c031048586c20b81c1800501c40003c206800e041e0380b03009011003200c4160f65081405027003014842a807044004001e40c0282c0da041184070385d03491082d203441c41460401410120915481c1c584495500b208000c00740014003000c403856440355541c9000140d000950f00310740203103000b02a10242c40150b5030a8030f41481108040321011032894401c840c7c0c80800318a00c10441000300c1858104052061070502941c64520101c5511000141002e0b0425950b0b800081c280c8102d0b900c0400481c42c00140180301c8100c9442c812031602d12080240420f500d0310ba0018012040c92140380c04210500c40450340b00c456001d50842c24080200c0391405185500344515200c2c1c0c41352208c103070702d4449c507061608000c0ea54055482d034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 387048003 1250 387046753 387046787
    0x1809030807030903031d0a1e020f01082e140117071b0c060906110c060d0902040f05091f06050a060c08040b030108071d0f04030e0a0e130201080106 65
    0x30361140c59064024180108088060588031070030110070b00000c4c45010003446042000f0300d0b0390401410080070200e503140300d1900c401da20f41070840140c0c86051000031920020b1921110b03d0ba124241040741700c107108448540b121070a94401b500d81140131054081d60380d00550020408001d100540e02e8100312408240b08410402c00140c540380540c1c20071a88005c0312034a107250b0841c2d582d48280083c03251300404080f40e090f08042c0000e541c401e000d005540f00c00c4000305081005a00000e920380650100303080d00d2034941021800b10f4440da0890741000302031180c10b02181c20309084098070382086900218106c0300785082003604045030f000349011200051b0040341d0403410048100d6220b80022000d4440520800c0001445801c02c1d000714000c142400c0034084150a046003401041c1c0b0a84051544480760020b108241d400c4548a42c2c00c02c1c2e0604101007901c1c0e071070000c500324031030503403004500d00c004100b00160000040c0704413a002c0d201b662940c00d03580e241c0805460000083c004003203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 387049253 1250 387048003 387048017
    0xf0a11190b03060f04110a020609160e0601050408030706050103110a050d060209030a02090411150304030503280e030d181205070c05120a030909020c10020d090516180903 75
    0x821015080015500035001800341d20794000741c4c00c042010340c0d81003128000241c2001a9003000c4d2541804116088118100030b400c0000c5500c0140a201c6032034000c9110a043c201c000c251180c6c00f0710202c038024840b8905807034030380806080000040009201c04e48101e5012405001c80c4c1c0f8014006000340d0b000101045541504c54403035000170340120500303a41500c62040e01c840940e4812695900c55407003045a20f13174504899042c480b246154110302c8031452814420301000a801c0400d03a0391001c1003558665120001d01081386d025a44410441c0c242442d2101c1251103100c080010400304503034190038010321607a007e0031320200716103030001f410501310ba15040d00030b984210000c04559019164098080b500e402c006082181000d5640c2c0c500d5000c04005810950410045c1004041000c5d0442c18541041403041c0c0740d0420a0081d4100d541c0010070102c42d641036030221402541010032100c41c041903082110383c405003030241203d0000d01d00101d215244036030040d00030460740340c1e40e144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 387050359 1106 387049253 387049259
    0x61201080705060315120705192301090b0d0e03120f130203060c0a0c08130501270302040203060f0d060b010306091503080304050f0f0a1119 62
    0x54043d810500030840110340904403440b031080155030040c580c0d001382109900f040c1854110b1988010303907856140d041524940a02c0070745440c3c841e1001102000313030710041305407401000d583c006800c0703210912802624102610f94080040000304109409000041c1544c1000c0095441c1001000c20801c034817150f529016005080500180003150140e00801d44072140246401c02d0748500040145800c0e21501980400c01d801907107aa03102d06054041701c01d0b2180d24403580380051243e842a000080704c0e6440f40001000d850110f800d81d40ca95400d100281d00010000382d400407203800c0445541c0c5445880c548580d1280d0381c00207900034600300150031240a41c1029840c0c502d400c0c0c002440141080d141002c1d2900b01400c9600c0e40e4851510310700e011148102820240240d014107041c8100008120042620404220141c0b050308020f220000c2002e2640d0310003020701e40410 = true := by decide +kernel

theorem cover : BRFrame.Cov 386870503 387050359 := by
  have h0 := BRFrame.cov_init 386870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 386870503 ≤ n) (h2 : n < 387050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
