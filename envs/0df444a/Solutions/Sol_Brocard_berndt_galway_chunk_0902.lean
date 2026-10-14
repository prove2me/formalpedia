-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0902
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:36:19.437117+00:00
-- url     : https://prove2.me/submissions/7ae9632f-4fe5-479b-80dd-848f3a9daa00

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 162050359 ≤ n < 162230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 162051609 1250 162050359 162050363
    0x30f0e0111090315100302060c010e0d050d0c090f090e01090503071209060212090607030318060e01060b0301031e03021002180a0611062a1b12030103110d0f 69
    0x8000c150890700041d0010303000802a01d010344141054010301d8a5180707034003801140e1601703000e24010300d55400c00c4030b281e0007074003140555502d502c6103103000c0d0010001c59410804544500381c452040c50081011070f2080c0c1c0c2c07001c0401c00300050030001040c684000070306032016500c0200344120380400160151900800c0140544030000e42541840400d0b201c65158607202e0355800d030050381d03030041240c3d6102d80e014444001e0008010b01201440e01d140146210f03032207403c01050350340040b18100d05146224400f580c0c000d85a500309c60441e82e0030f00c240341c050440281c03818215415130b12508042c1d000700d84684120303608817070354001b40350080100c940030110b403c0c000e660750b0181e000e482e0300c1d44000c2c041e0b1074040d40703000340003140140c050300115008003044d00080c44542d03240c0c1c20a09003c024480a400078181020400c1c851000c090020012031000030048414002079141551501c60841521000340740b0074030040c030025801005070110701c40b00312117003020a0344038100308184201c00703d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 162052859 1250 162051609 162051611
    0x90f0207080f030109111918030b16080a020408070302040c050c0d0c020f01080606030a1d03040e10060305041a1902040e1503010b010e010c050a0c17120a050307030f0e01 75
    0xa5442082c011001541a07900f20300c81400a4100c40c030881c0924010012691801040901c07443c9421b07108109910507100001200241c1036900c1e181e0f9a800c0760181c8049019100300c0d501d103494144c0000c0180d800c103040070411480c1a141038400e580754403160000038466078441a21030340041c032860507160130101c09001d07030f00902c502000c00f4000480000040313000e0034107042e00105960089a19603c174010240c02607295a03500a0b6a400600c03119103000303494060a05202d224810402c06000900034545842040341001040054503100325881a420942080104800034081c0c030940d01c4000035000d500c601c0d40c1c4481c030644c01c2040c14060527914040c4041400a118410401d00318081e03d19182d41400c001c5042c8141400c2e901c203050214049070010f0b4074a28254803a4600f80c0816001c2c0f02036a8100700b0303a5840380796041203a8040c0c000c0e44040c151102c140c04060168142d5040030221980c64a001100c01400328040180f00c2414195a040c01e21700d0f45009400030f8040181e6240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 162054109 1250 162052859 162052867
    0x2130e030307020d0e0402040f0302040207060f06120b100305120304110d120e2409150703020d0906051e09131506090905040203070909080c0d082e090f020708 70
    0x1c0d030318803003a0a040300040440d68417104078201442105c0607100005000b41b10181142c003404041e5001c1d032002c48040d6035418050b010880644a0080608807041c941002d0103500e04041c08200d03130152001d0030001d6040e0040000600c00203001030740c84000c81c6169160340c0c4500b001c0c1100040d010480390440308001c2068204050780b51060740b034406545074004030424401c2404540d44420b06200d44d008003940c860003c070816500940f4a0300402071100f0342c0c16440c5032800320b054020a1044000d40c0c0300841a680d116005490040038180d14507003181050b44d142003100c20030880750240144c01500080d403c1c0340d80c03144920102c8800101c0001e02c5188900090030003044803034070031440045c06516000c111000603000305806a0340003402840c00a003003d040100070400c510040700c46c04010810005070010520030138521880c5529402c00c0740c60310700e860f58010a03400c9500094514075044108404030264044810764078880c030002254208038075454002c0c400d41c40060191700c0045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 162055359 1250 162054109 162054121
    0x60e072324070b090d033b0a02041a0f0108090607080717090a0b0a02090303180105070b010807030c0e0402030604030c03180e060a0506131814090a020405060a080a02130e0303 77
    0x141d641e1395031045a400b00000340000224504001c0c0c151074884040701c0038a6059003490400d043c7e1103402071103c00380ca80c00c103015400517007140c04040040401c1c48a03680d91020b9480c0502000c090700c00700382055452483e20085050320b40030000c05140c10700c00c010010440d00351007514100802100c4000070061424100d10b0355030f1380d02c240c0004035449800c03000050304000550003910002407002d001142884d401c040d240340c0c2c81d040806010304100040c40820046014014264002d05c0842c024061041c2141450706200325140c0164408800050601005031000100d19500c550540360000c140007480c0340c1200e508440c518a5205c0d1171910201080394502c0e013201d14080e00b001c0382c5000704656280e00340111390103401650281207113080c1e020040880e074040ba407088404d00ca14005952440040303100007050341550421180c0e4030040082045003410300c525608024100c0e0ba41c000b040c03519007840d41d1105083c0c03009004814102c1d48507040d140582043c0f03c2e80558200351ba40381d01e070013 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 162056609 1250 162055359 162055363
    0x7080a0507051e03090112020d0606050406021903080f06010e0603090c030105011403151504020d020d0f060b04061101020d05250306031a13060e072324070b09 70
    0x800141c0b440e00035480703029180b802d42a401400d1200c1d01015604203c5140c00541d58542c50000161141e60200b0419552501d035103d5800540205c0c0c450f5500c6a04082e4024500b000701800208100d44820000002ca07402040d00d560090900c540704003a035442e2401210040b01480003180c00c881d0205c24001446004a0700c120009000d400130006a0307a12031480e4003110250041a415810800b0000280b40d202c4d0111a84284800050200b0580180208040360310a082c440e030300550224a000300155a0300801c298001c0d1101d040c09001e041c40c00310182c0e88568402c0405100000c88092a540e00c00e4054810b41e1080207420080c0345804e200c941c501c0c4c03a40540990a0302900c403170010f1154040d104d1101504d4101e40180c010b408245030010b121180074200d0088890180807140000300740f070113502c11508050010b025407600d040280603800320700c0b460210701d0340f040d00d05455040c1c0b1204440110102070400a9150904400320203902d03100301803000d0941d400c02001c01252582c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 162057859 1250 162056609 162056617
    0x9040504080408010e060114061b0709020a0e030c010e011d0d0506060f0108040c120212060403020c09130807110604050a060302031b271504090510050307051309050307080a05 77
    0x1112000707105e085c1c811901151921824081d00204104441d094140380c1001c00140c02e003100321b5046c00e20400680e0049500c0c080350741d4441c1c103c894001034003031041d50740701001410500341900140300c0107109000191200a408140e241044000380200320042c403a041036040c245030180406ea40d104480c10410340300c00c02151200e0142031090081d020b10b520622903244119007040d2904261030a00400b6142140080030990740300c8030600e112201c401051200c1da000d284641c008140c0100301c40140814803800800007402004503d08501c003044045080b150001c1e481009200300b01c0d03401b4005000382c02942c222039081f00294401040c80d40d01a8021402146070200207400f901c1520520340b40c521403040501100010200c1a0502c1204007442c05a058001440c881d001c2004602001030b030380195102d1109143c0720828061032400e00b020307580c050032082c2c0140c6016410000443e00107060382d220880c074650758450070790500c8000e04c25101040d070b002080329950360a143d030060483d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 162059109 1250 162057859 162057869
    0xf120207060f0c02060601122003090a0303050105011b0303110d020f03190501030825080d09020109050402030f0c0307030e07090b0f10020c04110903010603030f1d0a0302040209010203090405040804 87
    0x11600c83d1054000d400040c40740d1140005940b56000304901a00c004090700b44040350011185c2400c031442c42d4151403c010354494113455000382003803005410001c040e11030690090f418408114580c20114400600c3d1052040d018200814000f0b500c0c42446602d200f040d110310403e13840461014015141100194040c0f002c1440d111403034070383e034510001154000c0c0300c0100030907420051210400b0b07009a02e61a13041c4000515107440c0840e0301d6410195115200036410f443c0e0b1000c0410440d80c00180c440b019143c10390b411070840c81d01c401101c5150348090900c904880020000074000c0b031181c1c00c41d03900341c0b40a1040e5150185e85e07201002c041e1600350300300c1c5d1140b00c41c00d004422604208803503410008140c0c2c000c0040c000911705100c02080c580c0d080220841c002c1002c400c3c0398500f400341100841c8241c0d5156072062034041c00030f060b60889690055200342c0c1c02d182003815a00c4c41940401c0c1e86d01228010b81e64900900180d00e107100b134075000c1e0b070802c0c01c0ca0104000c2c0040d880c050803c81d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 162060359 1250 162059109 162059111
    0x40e240405071403192a15210e0703050f0c01081e060108070c0203070e04020f01090608010e0a1b081801020c060109020d111602040f0b010f0f120207060f 68
    0x2d4545400309090514603484607003591003480c4101c241242c04051030071940c02031441c030440041c80c0034070805401b03080b10a0000080c0145080280041d0020703644e021040c10701d04540e03900100344000c054611416051007502c1e80390314403481480c005005100c003c0d50300000b110800c0d062449480e490380d1a9031640d5001ca02c0490026022400415142e104000440d0106490f5a10900107440095000d07260000f001000d407004401a00c0800054010b03240e070754500b6a49241c60301c10804180c9048211034108a030580c000c21606402141d1581590f40e8518098040d07615013821000810032141c10365159401c40d02081c000641100320303035000304510704a06203403141800040c0d007030780310341880b40d442980468010058081c055002e050040703101c65010801d180c0e00c10707038000c040e00070f6200c51003c500b02d800f2560440c80d180c400c2c100000c0c6401c8040c4001a80705e0006011014041c207240280050340c0204420f90780b09620083c182c5107550000c54a40c41507003020b500401202000f000c0f96 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 162061609 1250 162060359 162060373
    0x1e0605010f050405010c0b09010f020a081f0f060507050102120f040203070504020307140306120106030b0a050108011802012d121d1905120d0e1603030e040e240405 72
    0x850b10460403281a954103031212211003030305030740300d902d20b00c00281807504955940301e1154107050031340000c006490b100c1d40c52000c1414103840b09003080e1080b441c2048840042c0a0802441008420910850b000c03410074076214170460070400d01910504d4004204980301c0810013441d101120704090149001354225401c4648500c00d1000700d1000b0303220000450442013004a00400f0500156401100035000c82ca0144545181c40d080d40d400c0d40049440d00011020444402d116201e6240144840c0e40207100b0303000e10740814030f03201481c2d64010b8108884d40c1070107580b1740100600c2100741e1045040c401e90ba003003420030007492044541c04007130881d410800004101542c80209a643c2c4126001800c0107511003100341c0703110601d840302280c0342d0182511441820068401600c0c161400d018042046005002818140310311b452140c07840030030203207007030010079848074581c1070b400d1017a00d000842000b46055075252010903810892181440c10784040c1c040a04110365001d51301c10b1080b5410303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 162062859 1250 162061609 162061637
    0x120a02330601030b06030a090512030c12100302090402010309061b080108010c02030c0d08060109031a01031119090203090c0a08010b090601020f030f0a05040509160f0c0807080c011e060501 83
    0x84d548500c00c2036910010510108009480700e60081c40441e21460841d1500680d414881600303400865080c08100350202d00702c0003400c0c1c020103040c0e220414408401040d0b04540c00582000d81c0036102a042680d5107010a00b085025800000842c6405600c811080c8103280f0041641000740148580c1b9400c0004032642540000f040c3e4100c800750b000540040c0e44042412981341200408850402c01480800408100456809401c2012400001041c3d41c15402c002007214100078125000c0c0205480f010024054415200c068502850b00560303252079076030340e0900e00b105189505500c00e54201c0009100e0005520514450360241c0d1003400541d581401a622402c000c1810700f0980c0040003455900802ca000504801c600e5081035030405403503202280c201340c8202c405c0740c0d10804006d0000062908617a003804072040701e1501382513420495803841c10a000d0302000800f00c410110b096509404203401544141203803034441002080400d4450011b8407403481034902240c01c544075568 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 162064109 1250 162062859 162062861
    0x909020405060306090606120a141819020111010c0305040c050d020d1218030b1b0307020304060c02040f0513060b0a030807020904030e10051e0a02120a0233060103 72
    0x407201c00420b500c0c19a510341003407040f00c0100401031039001408101403040b6440e001c044074010722284400050b80420650700038502c0e030016080000740e2100880b6035410501c002080250300902140402c2c00020910050b01c84042c142e0306891a5401c08890f80c100d02e0b8568003103481240101d805520080d9101d00380300409024034000387d008000c1904440c0418501c3c8903a05011103145096185400d06c0c80104690381219041264044180020300c4181891005501580d4000c00700440c84e40c18503080182d40c0e40f20710f220303c01c2401800030b86081903542d141e02950340c400c94001b007802940390281036000f0407220032108950b9a8070f420700c4420b00381007400a1000f0740390300012062030429250200805080c0050084007040141001c5054a4845a503a1102044980c60b03ea480305924600c25000c0281540c069910328014002e54210980c0040d43c54000604210420b41e240340c9210100d08002c07101c007128007881343d15551041001d20180345481e01041c02180002030f6160140110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 162065359 1250 162064109 162064117
    0x7060905041e2d0f110a2307050715030c0306060e151e1e0301030f02040b030102070c0306150806060d03031d030c0307031209030e041a040e010b01020f0f1f020405190501090902 78
    0x81c00144805501f501024010000c00d0f10045c0c0c0060b02420030a140e941c0600d8030004e074001c0f0390b128000c0550180c2c2c003a003501840800c91494101441101e00b07155000340b103414510b140740d05c207408485ca40c00e408100d400c1100c0c03160800144004009440d14076a0301c055001c20f0202c480c0f03100030fa00e2280c00c4002d030000d4070306a0341d1183c2c00e10b00380f180076020000585000e0041a506550030005140000d688103851002980700b5080420070310f54030b204803d01d22050380c0c4030f258590030901c100645a501e07601400c2c2d016074142400103d81c2da10000d107110262200f04030319090311000469060740f90002025100c464800d40c1d8003065007010800d2101900c00c9144020040b07071004445027103500e42030700f00100c40510103402c44092823110001034142c035080c21a4400a942d035031103440555a0500c44902002c18400c01040c4002028800b10342c3c5100d032550001c1070342000440440c01d80300a404a81c014900200074400e62104042e01c4192068907200340760102c2e015150010b40742440e40295 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 162066609 1250 162065359 162065377
    0xa0c06330b191b12030b060c0309090a14090a0204110c0c100302130e0a0b010f080f060a0302180f100503070504180206070507060905041e2d0f11 64
    0x40342400c8680315100641d15101c28902d0a0001d802404949000c2401860a00c54001c240c0540b881030102c0000d0111584102c4940c0240c000308082d12112a001007180c6682c80241e6410071980d035805a2070004113038084154008041c80d005014042c140000c00303e00755402110100800341c0f2028441c00180700d0324820900c0c03908080a504401c1c40c04440c454046905800d000d850b002d000b0750b101c801c081c01a040800340c03807640740502c80301074103901c40d04003013030b100b07082019200518540142185a006184203c0d0200e04400a6015259502400001e41d4007901c400d0351603c2e10304031218946d030100c5500c0c241c108030f100001c0c284000b03812000e084440c05405840c0c41030420040c44043c203203c450007a1f0021300712506d0001611154000e10005010b80041c090150400078010312a00d02c0d540020321580c10f084850351001f0b800e0301174807110b007200c1c8000556114030405845030551500c1510748801c2801050131f405c41d405401251605d00229000c1112039021b0000e42d140e03009000700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 162067859 1250 162066609 162066629
    0x3060405250f1202031606030e120403020a0302060c070e0408031e01050f010c21020a170702010816030e0a061508070f0b031f06052a0a02060a0c0633 66
    0x7000001c98940540f0015030024050b21101c1c241551016403900c566400b4100080d41c408a640302400e02b4450401c516032900384041c54140b03580c002a00c49600c1c5e0102030b10440000500034034000b010003040c002404505848407080c90079060803401c0d50421140303101d01e02c90341105c200f01740284481e00c6040e640c00a0841880d4001800112002c0004060450b01c104400d003001c1100d814111a20058507516030040c02c269580b8942402a46500d50951030b03249400d010f0500140e801c900907a60050644004070100400e601c0114042c101c12b41ca02145d9000e010740700c0e001e100443d000610161206000c98034101d580e0240240d94140c680321b405d1417515007000502030860102c0003160403183d52621700002000581180c0d69282c041c2e0b10040100307400041d400300c00070f010608e01c0790480c3d054072081c2064001c1d006064481200600c002d20407a40007801c08452402103485159142d00301c00104451090140d001031200e424503000880f800f8140306051070380752032001401c2542e50b8104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 162069109 1250 162067859 162067889
    0x51002100c050c0f0607030e0f0729030403030906050106090b160203150903070528030c2405190203070507061505060d021b03040b040506180306040525 67
    0x1a000300510020100004001d010003280340b40d042c003004100c010090080140c102400c180350040c0031299801d0580000380c1103c8002411003401050f14400c840d400e040c10141c6800c0307007005840210f0540c0311142c2000e804014001419032543c0403000b000d108501c00c10040c1d0702c0e200181c4089009102e03c0d80261010094a070701c0268400030785000601c06821030321210315184034154080000c807000405a03001081d88030030311070100702c00315040e88002c05c0d0400842c01140a10501d1012640280a0105003912001084840782c401903c0035450107044598a4a1840c5e0001501c410355580f41e00711000201d04039413411504c2140e004140c04d0312000d01d0010540e40304005014000c0e035030022004010720004564503281c0003840c010300c005e0001039480c119900711455280c0c80e000381000c0c50313000303020070310007400020111800c1d00d030100d034074640710b1241000340c14048000200d996018000c000a200c10840002081244000c407100ca0034403c406e071081c03603005040c5903c502601d152200e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 162070359 1250 162069109 162069133
    0xe010c11250503030301030305190309230f06090706030e030421030905030319030e060c1e040815090d0503060303040302040504210f020c0111030306011b060606020c0a051002 77
    0x1c8003021041008403403020072a901e000090441d00240d03c01e801160000801210074055030b0030b41d04000d0580c1c1020861800542c4414915198001c1e01141018071407078001c500f51403c204c03540c00300000c070049413503c0c608040196103410b1980310340b00c0464101111054003480200036a02a24601d070000a20070416000e800792040c0300e64000d80070300c03083c0321004c540e90f1001e100401e000e40445102021941d08010300608036807118442d0030319900000d060044602c3c1d114111000c880241042c030241410003000022103110740d52142c800ba200d81e24100c40c98600c1051458821004001030f600b4100c04034100382c41c03d100032207c069064008020600040c80c00c2e6100c180c106000c1c45000200346440000710b9400c0d08860340203804240c2318500c20360015410031041c07004400c20320b031019481c0130500d2a11390320b01000e01228144800700c01c0340c1003502d40c80503030024115048002400362070750300c0310040e486010b00c9035600c0c01001c5804020901e414050300b1652418120390041103496025 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 162071609 1250 162070359 162070393
    0x60905010e0c07030c0609030306031101020d02330a09050105060a0f0302011407061404110d03050301030b0c1e0301090614060703120b031203010e070305060d0b07140307030e010c11 80
    0x10f150114244060840c1403004611030707214030305465120307403000030b0310070701b94103115110b44085030b851411540035010f01403145502091010016001c1c6c01c07804919040c00c1c24042c1003e000903404d010540d0360780300304201080319403c003000c2c0d41d0240b002002030b5100d4000703000c003010300c9005c0c101014000c07403c1080194820b1a051151036107441c0101d04094407a0360b050191424424580102d451000078481032205001350040c0040c0c0403a030030041500665030181c00741c0030500c40601128003100020f11852864003c8484850386001060013144034010792400c1c682081c0142030301c45141007404100100700304c82480c6150401050301e402d100c1d19542c12142c210101c0d141825052721111103003900d4408203c1c2d42d41021244001c542c4030340c1800085240303442c005192000301401c00e010b20000740c560800303243c1c0305030304140340170500c1c2d03602c42090725002417040c80501042000000c0100c45a490790041d40c02c40c540038028400105030110490b02000320007550b09071600b1080308410481b83c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 162072859 1250 162071609 162071617
    0x609010e07050d0903120b0402030613020304080c0307140105010b030c0711041514030c04051006081b0412030f0f0e060702010201150e06090c07031d04021b030d060905010e0c 77
    0x403614015251a900603e40c0c4141d43d40100100c1c080360b01d40300b01c01c200b25100c2c02181501c5009a1301141503240400000b644035007518a070181c0d840d40080418184924042180e6035050340004480c0e49600918045410490383d21802846500c1c00d0300108046412000b280d0140100304040c0c0c1c01d00a0544409000017031407074007503030b11540d1c070402602910403112111000b040e269142041415041081c1400c04510440c104e100301e24140400c0b03014041d05445006895640c60802143d0b5030300901c89902081f45407000364012401300d40010420410803d01179403a12035581c8148043c01c450003581c019110360b00907008102c1ca1020f144407070819101070130341700b801440082800703101d1620640745207545030012060017001c0c0c1e040041504002c42c038150401d440744201450030f8156140200411202100102c4003032540c000010140c2c0e5640569143d40c08005000345180050f0954551342c0c0d1248101260043c2400000035260030584503540c12586000b01a403625a9188031800d41540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 162074109 1250 162072859 162072871
    0x3060f0906030109121d040504080d0902060f0705060a06050303030403080123040207080301150203040b0d1d060a05040209070e010c14010207080301060507060b0d030507171e18090609010e 83
    0x2584460a90200700d40c1c0492203080a51a101ca4a46d0002c0070251009a110f4580b8503002e03030f040c03a052000040c40700b0f00b01c1d04020420a40015910500d20000f1603038410340800ba0f2684002103880d030103001020418501912480c002044155a51024151240022034001c1d010481400c01000210603101110070074003030b9486520018603284000400300d81012000f5101410048010f005460391000c058804440c0b40c0000d5003418500b00342014075110b0000090b1002d500c601c10700c1034403401c000c0c2074009816680140e40c4a842d0042c01c000041c682124180e2040509001003005d450040e01001600311043e540e164132840b1030b0b15000710500f00d44e0390f1941e0303a41d82001000f0109031354070080d40c06045259074540c0e1ba0040e80c1801c43c166000c00041c0340c441c01585a128002075041340c01c846081c1e07440550141e1440a104540002c7d005040e007010000c43d03090792121000d582072000700712420995918404c806450710501c46410400c65500d038005801c40014400c010314140030507481a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 162075359 1250 162074109 162074111
    0x81b0904060504081b0307021c150c02030912010207021009050a09051b04060903050f0102120a0b01110d020a26030408070c030204060311031005100b090411030c040e07030203060f09060301 83
    0x166010312400d0303030245c2450301c944040d0000718041c811860078442d03594034006042408034184019440c0c20705440e00e458084100c00e07990324000324050740280191403605100502c032a0820480003825400303540441d4040788100c0c2e0541c0003d40745e902821688040e07a801801000000307003440302860003080c01030103504d01140c4180502c1c0180d903006000b88082c2507265103040803107246103015858094003800c1c1840590061100a054040d2607110741d0784400c0c81c040220356240c0d50f00059401002ca4001c80385680205550100c81e030b50001140079401c1e00c11101c20341d00100040c0d001d0340c201c2960313041c41714050040020a02203403d540103060203600440410001d070b0740c0c0364005002c51307105600842d0030305006400944245014030001302c1005007180c09101628100e0b4248128842c0c03401125403581002c51080e01989503944000e448000d0704502c16039a060600213611503030491712460083d41c07543d40001d000c46200c0d00035240142405041c0f0100d030b17048102003081c1d01a004215907019 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 162076609 1250 162075359 162075367
    0x307181a09150102060108060606270901030303020406090618090207021206100504051e161110020301050307080a0309060302250b0601020c030705130207060b10020304081b090406050408 82
    0x303650741c041c1c0180900380d200088040d00c2c01000000e410140141d009200742d4016000f040b456440b03910407105a0b802040003100d209580e46551142d988580301203a420101540003c010140c05034008c01c01d0f21050340340e144410342d4a41040b00d2040e044007110740e0200f541c040400c94800681c002e841100d20050011029100010500c0d00d044401c0759003141c500c8050004110a040c00d00c10b80da084008114825840090b01e1420600f10001074190b10107400308203200c81e000ca225012880d03001170f00b0420750325040c5142402030040d4200380185482405a5400059207900004401d41d03466032684441840e1031501c60190020741002c101490141c03013071880e040801c0d1044190140d024412401c5102034100400024505181107079002d0090341301e2001404940ea07000f060442207080c3c1900036030364203828544400584002c040d00d0b40c10000001c1010b025076000310160091f51074110442d556085006040003c0160704058039030401e601402090105207280c1000c1e510a020fa04a5460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 162077859 1250 162076609 162076661
    0x90513080c070f0605090f09040311010624020f060c0d1103040302010f0f0c02151003061d121204060207050c131523060d060308030c0703020c030718 66
    0x3140e00c0700301e0031845a04081000c1c054003410f180890042d0560740f41843c1001000707004515154010911a03108480c01c00002e4100361040703040b0001c070300e0b820f0001d102d441d56940e00c0755002040c02c40030f039480340555400b001c8914400500a022080400c00502c2240ca132000c0c20f44150b40062805070140d40c80740b06076a20f02d81e9000c011402644030f58000075004419141e0b140071544d00e8540a40380381d0514500140d015030000e6030300c504061b0344002008603111b95030304103020005c55000914542c182407115074413100c4424110b00240c0080d00b0743e02c603061006507240061258501c0e001c04c49001f2800714000c02d0b00ca5010b400454441c0c1e08546500d0903190010340c0c000b601c21410008591038800e0101c400b151080d440d0700800c04008100950411502a40031100c529002140240d03000700307a03403142e01199007000004582184001d5541e050010390381405a200c03003402d8015100c2c03c07034140365a0500080d808220341d031002c2d040380202d0362403a841c0c0181c0704441444044a080d6600c80c14 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 162079109 1250 162077859 162077873
    0xf02030706111c06050901051005070203070b04150302031015051e040518130305091c0f020f0d030207031506080708070509010602060c0904020d021204060f11040807090513 76
    0x2555264002c080c540300d82101d0300d005183e41e48881c0c6a120981025020402c41e100d0b42e81041c1500c0302110f0142c00414450070031a02030154180c065414440c5203000100e1170b00100092055603d276410040c150004404290203a1100307691b0729440d0340c011181001282d10403c51075009010625107146444010140f00104122500744c1e140100000074080155203000c50348090200440c0059030140d16090021580d00402c0703050240c103114000924011940d507072420103000390303403601c01001c0b1045282801513030021466022030044071442040903903840c003038501030400d030b505900a00fa03480c1565a0b04440c01c0140700107402041e2910304c041041c880034000200601500c5d03000302a11450207040264011040c1d000c1c1085d50804000d100c0041006421906051001d03940541d80d1116600c4600c000d06c541c00400074004000d40c02e2208004c1740350004035280388151010f0080a00480001003107101d648528045a4403000302002608501d800c00e5502c8540f1629803030180c0c08e1600ca0314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 162080359 1250 162079109 162079121
    0x9080f0a02061006020a03120b01050c030304030e2403040f020406080106080c1e09070c1a01030308040b0609151c0507060507030801060305060f040203040c0506160204180209070f02030706 83
    0x30301582207241000030805240000ca801408244001c066421031601c4c00b134404040b441040c40300544400c1c00b4610785c0d01810498010030040c1044a5603498541801000b10f0031480c03216106040c1c0d00003498214000b2040c880c503001c6000819469520756613201a4000a60b4504a0308503448140c00609031b40d00388940707001031004c2e402901e510b00d42c10f0100401e880e0b0400c0001000c4031805401c4e01c41e500c55800d0030344d111200e8144002d034240c25080c8106030581040740c5a4030f6a0007040080b04050748240000e028922414048405840b902e040054818013200e4225442c6541c1b2002c1010b4640b01e03185100341904001c9918040c0b0840d22a141460125040000031072070001d684e004140d445005a80117041900d000c00c8603040080008410303000e101c0d80c45201e03503004800319050280c030702420401010000e0050307a80348942118a00e000000010503449507251000d0900c42e24001401803059541c001d040d0009070303035401401d03501e116403507521004500c018850b078000070341e1520a00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 162081609 1250 162080359 162080377
    0x7090506030709050f09070206040212010905010c03020c0d030c02031c0f0c0c0302060901061a0a03020d0c030b030709020301050a051909050705180621060d05070e01031e050d0309080f 81
    0x3d000c500741080180b0026041880800b4050130140c400c0202d030b41d6010071341540240e4100c5d81d01a9035040b81701c40d203001d8004080054210b52030074070340150403900b42c0e004200b54460001542d80c1100b10722015000c4407180c40688000d81c20401c680340b00207410130f100011251140c0c3d40000c0c0c15a003080c1c050120f41c048020b0602046c1400c0c5080c00385a01044072680c009a410001d101c402d0900d00b800c80c55214800c0004528203002c1581203606002e601070340c61510f080b08007003200c01e000100040c082d0482e601c0c00e900078002d441307001c00c4090081c021a07050342c1f0090601414140b52905104800002200342502e42080c0c070f00105041c4010f019050090308243c2d626610350701800031a54405c480030084900c02d000801001d80000503900381d00b1b0384100180c81880e460303911103000ca404503011500c01403443c020200301050343c200f201d001d1410b8030f0003940c8000b0f8502e0074503a48030040a643d44054042d43c04000480340c424400d8100c050242c0c0710340e07001400c01c81036030314002e0300c0d800154030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 162082859 1250 162081609 162081617
    0x512031c0f0509030309121b011404060e1b0f011b03031a1e0111071205010905010c03050637090f110f040e09070b070803010f060f080708070905060307 67
    0x1101c68900060080c150030100340400b861550805108855403111100c0c21032a208601107076049020040301c0d0240b1032111141c00178042d0801ca2400c1401082d0300315000c565892415401ca000c145001030061619410070210511814042c01000f9400d42e184a403981000080700300030010320485000603d44611a4802240e032604001d603110140756000034690150340c820080c101010101101101009800c0c03c2452411100642880c1813800f550003d60500c5908a0300004000c415402551030b5805803008100d00450301c5c0d000c41c150b03142584c0300ca0380301400c0f8400600908092400c080404d03440401c0020302ea4190296840300d506981c4066030055031048110041c02e0540202d58030301e201b40000c145403000031042c0302000c1c0220b0054018a05031200021300002d410040c41d00601091038940313880300100e01d41440342d54400d0140312180151100005040b074043e00800300305642c2912404c1e0300380d9070120100c2e07019000422450801c440e8400016a030f13115000114040c10f0a9030b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 162084109 1250 162082859 162082871
    0x160503042603040620030621011b0813110111030c0a0f0b0a110415020a020306040f03020d0905010903030503060d0c15030b1e040e0f070f06080604020c070512031c 72
    0x41803421a403402d80c0300300000b442c0300c840b20176580104c0e048036804801150f40303001d41c0c002c203108007014400510600c0b5942d07203000038002c442c0c9083c0704420b68a080d19695020551b0720004200240f43c00719030010f04801102800151540c01030031180425a9110f04982c00c004010040070701d0603500001c20f07100d4050f00444e010078025482d100703591042d607030002400742c046030013480c5401c9c0c0b00300e10500051f14074030284021131a01c2481080c00d4107030001d0031074819080c03a040201d0020030b0b114003140035114180e4445d00306401580d00d0740c100e40c0161140c5820501c3d44d00d007a18298030041c50035600030041e803030400005e40d509003614080d150110b4941c0f0b0484031070358058216491101c1051040001d10499000201d00c03c5207e8004041600c001c503105022440951608568100c465147d02918501081c0d10500c52654801c071002d0355103103c8240c94131010301040384a08200d09042d40c008030410720048c00c00010041355411028205c3c3d181c05100d00d44800e0417001105e1010306240c94007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 162085359 1250 162084109 162084113
    0x1f0804020a060f1d06120f0a20120411030312070201060b0412141207060906050c0a0503150105040b04270b0102100903090905010602060702060f16050304260304 71
    0x220384000d06100c2c2000d64410510b03100c0a400c40403001d8001080e2806203d42c144c143e1591710a8441c0c4683c40070444100f414100d8074000c4510085904030141c0d8584542003040c8001a4141542d242055070610314142d64036484001050300100191082003140d1501d01043c0c9080004104c0c1c0b801325412201036050102b030081c00c0d81c809500c8415680b00030f1005011074010400b4100202d0741c00b07004402100400003640e414000d000d0144c2940c400d000c80c4410610030160080b40d1030354440c0104010301c0d40c0b403406060a901811490100060050001801c24840d01480d0200075805040050500c0d9a4482d10301c1da65215800844084103e840141c4941502580c0d11000211000d02800243d6098000035540d0741d2000c011f840d1a0303110203800003818011035004002e003110227814443d9684a07100603544220680c1c104005120700303000161428145032225000d00100003419070002c09030794088031250800307801510300940c1080b0741100d6544005c010302c56090f10060343c42d05da18082c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 162086609 1250 162085359 162085369
    0x8091f02070503060106140d0f05010303110606010504030314070302121605010b0d0f0803070306150306031511040b070809120708060c1207120f1103010f24030b1f080402 75
    0x390b000a0207a44800e005011154100448403a01c0f00d0105649480c2c941c0d540307423000607001008284400520301800403050540c41882013104a20b80c00459031039890350030045520b0b106600c405400201c05c07040c209103502c007110091000c81d00a10440b0300041c14259060320b59440340c07848220341014040c46c9810000e080c0180f4445c65801c5031481ca00f8445620b8150300f0702d4030048014204500080010011030081e441391002e0b1107050344200891a41c0100500107200700d020603204001401c4141c7e546000c4c41c000e02083c2e000000009040514040c4030f03c0142e004034100305c407542c10074440d480b51925590745003102240100014a0b0b800d04d00501d0509001e000f4240e03105c0310700100402501d4a2203201201d0300400e99260034110404140010401010640000c000060500846c280400c080300701450580c5c46407142e000d1216550703050740300c600c00300d00c603030240c5c980140700c0ca807814a000303620444544e0b002a042c0b404030080900c800101300410030200021900c108180419410700c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 162087859 1250 162086609 162086623
    0x10b0307181a0306060405090a051c0801080c0d02131d06150603070225050405090d081003020d020913050d030f050601090509040f2109050f01260408091f02 69
    0x1102002150542c8008079440d002c0061049020b02d80301c0000c680c000c042000301e104040d41000a540c2411440b9030b428000c80b021601040000380c18200108441d100421030f02c00f4264010500c0b44e441280b9428030424600d00c4041425065552074410b800c120410f0006507009000400380000c3e1600e5004a03d413003007403018032400f0343c03400e004200c0d0080e00010140084030618130a0b2200400d41e85503032421000c9a0070080d009414801800882d43d070000301d0780342c0721420761107484a59035030f2190030040107403a110103540b003495275031345c940907040003080e15400206c0c030b1410b1070100a882c0c540500c1c051035880d0000000350749015000c4201c0b0103204154108400b407078050000307450580069448600540041c000c0ca010300149401c00c4180500b401121407030440001d80682084000b60004c20148500c2e4000e0180c1c3e088420f2a600c80c504c00345c002d00c02d88242d488145802503181040708001231044500500801130381219581d480360300d440c039005600c2a80c2032150442c02c003e043c400c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 162089109 1250 162087859 162087881
    0x40b07061802062b0c02150106081b0f0c010908070b010504060b07060b030a051b120105040803010b070501150b0a1209020105160201091a040302011806021002070302010b030718 78
    0x10395507540001607581d8811a04010320900794612090600f0082c116003210300c10702c5603280b524000300800190b8002c2450002c00c208644620100d0381e886070b054606c01c1e402c070b0310364220004114945022200c020080e0046c0e06100c1a001c0c1405000400f00c0d0071100306050580c0c030761101140b01c0d81000320643c0040d015007010799051150074a0041c1c0260ba41c0580309000b0001500c40c46116416141008007070314640d0001c04a80403102482c41c48200f0300e00560b429801103880171100d1400c0c18050040b07a01031940081c0c01861a0300c0c1c14419034540c0c00911003203c81c1d54079050709190b6221038658450203006042d86c0207039544078070300c400341211083c248808817450070010300901503070b0460161450004000d100445940403032004076242d081c0c0d90040c640c00c1030080d2482e641001040064000d881c401c1e210075a0b06941800c0310712800086100b4840103a110460b00501c40c0d05640203011715070320900010a01440c01c0000034100211500820718039810074402548401d4140541c1d60944 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 162090359 1250 162089109 162089141
    0x206010e011a07080c0c0a0308030105040e0109020f010e15040303030c0f0e01080601030506040902040509010204060224040210050705150610051c2712020c0108010503150408040902040b0706 84
    0x860b445001d4201402103400141c0038000200f07a240c20004140720442d0706110081c00107840742d4403803422001035002801094000ca1074101c0010582d1014800c05000980040191044003080300046456542c212003031a08580341d1004403510130702c03c901600155200781ca0203e220034008030018074591102d181d070010000b83d81c01140340c5d40d810021740c1d034005100f071902154541d42c00c0045806040c24090080d04289404104151040f042d8040d10599140b50300b40e4254407142108902948803290a40d444103000d400440e0052600000c00c00c0c070248a810440d09115058a480c2c1c02c1c420304184800d0b49001c00710420009162110010301e50030f401d820650f0519114095406204402100c05d16103160364411028009103e1790004030000d0280640000c401c0a5161141c0440c0c2c0e080c00103005071080144404a42d030284034007a0507200041c008244030300c0d0300c0408043e1104050810b0740c0e020750411010912440f640018805015400c1d1070b99601c080c40d1610104031041d29503900d00795 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 162091609 1250 162090359 162090389
    0x5040509190c05030c1903020903070b13050f060f031302040921080702030904090f05071d0108010b06070b04140f1501170307120504051009050301050a0506060a1206050607030206010e01 82
    0x45c0d2200826030310302c1107800b410440140b12201040c3c4c02071054009540d4503200c1c1000016054003c03500403e00b50810030241403010f5507a02c20300101014800044e079000310103105c03084441082c1030140d40c2c13118201c5000e030300101090700450700b1208001d800b80e0300d481400c005290311400c1203030042e0344640c003890902002e00d44648003e403280502c1d40b0482c0705a898890800521103124005030401d500041030b01c042c0c41d55448480e018503040100e1400c0c00f5010000000c0c1004103214000250310040c02e1249400d40940d02c03003d0803d4010000c46a581c2c1050102840000811040b0f09110b00c00005109007920030540182200e416803041d010000f51056524a1003004800d44618a60280101da09200303c0d6406464500940d007000b41c11107040e50101c0030683e8400c29950884009070020425506c840d03490f001621011510359402503410400107070964859440b0011189401ca8005026030f1a4400038029030301003c0180d00527444000188003140d8036803080360041a4040008140f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 162092859 1250 162091609 162091621
    0x807081e0a0f1d010c1a010608070207090b010f0e060705060405010218042a05040b0f070611070b07180e010e090105131205130e040510060503030f0409050705040509190c0503 77
    0x1001003d5000d03810010028802810081c2ea24411586003280c0b80c501800381da1503a50081c1240002c4401000610981c1000219091607104140b279a103c1a511304051030140383d0300340d420508107024141c001004021102c08540300740324240c005c40c8600005641c1d848030078800044a102e819aa030700c1680b8102446030303d2800c401080b25072710900b24690074240040b4009072000e00907907121003039519000030f0100c02150084014100284a42004c11403520803e20f40c401c503000c2d12600816501c03400d408115154059124252036900140400007699200c40e40f000031b40500b1b9100d07070707502e580320414001d0b2504203000e006d601c03042c0c0c6000c003601d50010780c403180585052841a2428048000b480603d05807642c03403104050003000d4640540c0c0d090038035126030780e4010305405245484c0346c00c1c03002c1210f140c0802203030024113400030050b0915087ca8048801008080c0031340050100030000002c807603c0300b961552040d1204107030748903079060b01101d0700207450100003070f641000810020404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 162094109 1250 162092859 162092897
    0x5030601141f14070c0602151509090709060303091a030408040603051509131209300512070507090209130e01150f1703040803070807081e0a0f 63
    0x8102d40c150002051071074010345038070303001a00c04a418a0f0004080007404684c8041e0310458010f82e08540d01c035103c0440c6500001d106913505020005d003500c0310711003480e20403003048e0005038590070344007510340d9101315400300c03181a80101c01041d203500c07082120542c032100107050828000744840c60752800384d03110071541c0f06900070300f814103030382e140440c0601d10a0b84905110744070103401140c043c14048051586900000011102940406105e8500f44c0c49159610200c8462000c4009100780f840010306811100040810704d95419640c0c0c44003281d410840400880c85503d0281e944030303003500300b890070002c0542080c11343d280100460881c40c1c5a841c115004058000800280c41003804455405090040820302844003881030201d240d403035040b10f0004131380304100c00d199505d02e0148202d49902443c070408005410038054400450900da000b402c02501c40c40031186446402152031031300044158a002c000071001c034100d0000c5401400d0f400b43c080c85802d0140070310101c0c802d108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 162095359 1250 162094109 162094129
    0x60103081b0304180c090806011802131e0b0906030a0203090a0c0e1f0308040302012d090e0601020c0904020f01020c18090d0c080a050f04080a0c0503060114 69
    0x100104400607800c85003291211441c045051600d05803903540369100c02841c500c0c0c0c0104aa20200e0f13140c810b8400c21180503038083c00490b002040507010743c0c1e29200320940d516111117104201d468080015100c110800111030010309903a03010321001da5a40e0a00c03952411068105010b8010200312178003056561308162903100c0380608000d80c0e00e654030800c0030b0801c0210b50f001080440b51010128203d0000901c1030701c07501440c00d404894440082c02e01e5807a220901c006040040200028405944540c610540d002d200c1c0320840031408282051b152280a10320388900000c074429404c0c07006452511a994100d0401d10050070110100000101820006000240704400b505a0548bc5074000d00440c14450f10050085a40054000c00603807012001c40310034025019070a0105c4580380112141a08103400c11a854240020721105486503808440b03044042d400511001030400410420225010310540f22118850310345428036160810681168040c44402241a20b6a8844171414 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 162096609 1250 162095359 162095363
    0x1090f2312040b0a090312020601051207050108040623070c02010801062c120a110306010905040302031b12040b07060f1e230f0f090a0f02010e0a0e090f1006030203060103 75
    0x2d1984d40d9112901510340c0000c990004140301d0314800603900480d008076a540c126034059555070001803481c450340352a002c45000e101d000c070300c03128046808205a03512200151041003044482c2da424107e01c002c0110040760300303400040d80c1c140700504650341701c80a1401040c1030300301041d003444021001c4c0078050b009455841001e104480d902841c1e501c00841181007070101050381c02d030b035075581032603040301c3c00981d0790034024852000005009444c42c40b804e4403454055001e182440a40303d0700020580e1010400c12852040c441c0c00b015000c2d03480001c00c01060143d0140d6038030405494060142c0c1d8004a170482601e250513140f1810413403004051441018042c00040c420f01004610003186502100030819134600004102000c0c0ea00010207010700e16a030219082a507401a54650703803c0781c410014008001ca40525005500541c0031041c005002441d80c40104e460322400044860125903103001a801008035100620342031110042c041505c2400740321090864011030703591031040c400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 162097859 1250 162096609 162096629
    0x3020901031509060c030f060e060904080d06030b070309060f0b0907030c21061d13230111091203030108071a0c030c07060909020313031101090f231204 67
    0x811650620303264814030f00281c1c0504204800e00103410000c1c0200504080f41d140e20385882004240700301001c100c503100c2c3c040200306044680d1103a40708031085c0c10070519864000d85605020000507405403003e440f074032440c1d40000d03032109541064400d8900c0e403001810086e01e820341180294a907500e002e40c3c400260b041c04120754209036011507206108000003240c01c5a030111028050040b82c2044044a00c21020002255000404111400020b654081001c10406060400600104521507152074240b500800072507001070760500b5101c1c211901d000d15000040c00389201e18080c9550302880b001d03030001f14110341c1040a426510b8280340284035080340d81002030180c8040800c1105e004142c40c1040c1c035111740c04c1601c110703030f200c805004050200d00c3c0400041054081d1b842500d114103da05000d00691034141c5099035141902c0003c120a5520b9080b0400460040707070382418024440c00020049445601d08407003090f0450664040d5074004000c80400741c6100026102a605c0b02c00f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 162099109 1250 162097859 162097883
    0x601051002100603050d0311030c03010312032301080115051309170406080f0106081501030b240301050f030f07140607061e1109032e0e060103050c0103060302090103 73
    0x29050340b0301244200100401801c14078048104407000c100c003054404962800d01049141201c621100c0c00220780740d1800b081c0c20b100400102d400190500340d1b014081c2800030b0704104d00e03117021000940900f18231400700c3c040720041040003401d02c1200150b200b901e0035800f4007810640015512102d4105158049840e1900d60042c400e1942460103140c02c0e5140195880d6540c0001421550003203c80d10b1000e0904000020000c0c000ea003030380d01c145114824070070bc0d0700004006600400c804148a90021403141890f8800042100040d00050411006645943c540820888011020202140030b0707008812018500b1394001405010b84614504201c01c40e0080da0108101d40034854000e885c0380d0401088086800c134482c4400810464404180b01c03480d2900c8030a0068440c1000180e01584181d80e241815112090360031410541c6002501860131002c0c8501c003620541191a0040c0c1c0203400100104801000b004948500a00341404002d01d9030300081d51a41c01448042d0501c101ca81f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 162100359 1250 162099109 162099139
    0x6090603090c05060a02241308071b0803091c03090302061804111206030a0b0a0c1b0503030910090803060d0204090b100f060503044d0103050109020c060105 69
    0x70840c015140240026031910707100c110003540e03031a0000ba01f00328400c4040c801c9031b05150080d422481000c1702e07455641c0d140810341e640e4046601040c0169003060140c285040c40c2500520b00c00028208880219201c2075983e08100e400c03203400181982103d65a94143e000a800601c0d000443e60115220fa03210303c244207105142e5000c606a140c0c0c050700c1c0030301203144010800040c1c0118036400d00664500e079228000c0c550f9841d44103001800010b1401c0000d8103240b07094001034400016460a80b806084012450b04604030a0104452542010041180c0d00d2800c00c5803d01c0c0c0c0100110610400a4644030b100e5148070217000c590040303038081c010000390349a41d00b148000c2035100c41c601c40e0303904d056502c11030011002c0c055101042410040022040c1c824000d4038016a0001c80c034074182d10740048007002e42e405000b1600c585201c1740e81080c03441d5411400012429440d4807401d0817060882e0001022120160088031805105100081c0b0501c8005505130645005585001d4000f20320f13 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 162101609 1250 162100359 162100373
    0x909020d050607093b070318050102070b0609070507080906070b1602060a090809040507110706030608010b010507030e09040c051005040509070e090f1905010e0601090801060609060309 81
    0x984005407842c81031406202032960f0043d480c0c4100ca484404000340040e01d14030811243c8041000c490340360307070f552616019692218600540003070791403c1c005400e004074110000a0100a001070314240d5011504100344001c400d03020781e003c202101d440c0f5140c078013460003138144c0c0540807002e01100404074040300d580c0c4a41c01101d0440e40c00050520861521034000c00101a00c800d664006004100200b100c15030b03507000e1150721650006003541058221000e000080100612800030090803000c102c0c0348420501c20329015004940d40400c1c0181802c50481c01c3d1a034a403070030b50401c4000c20180f008030381d1011111110640c112588481a00c480c244225070507803e400c00c0760700003903c421080345960400001c004640c0d007560345a040303076152201901d40d41c07000d401c0c0079000035007a400540064402d00200d0740c801d104658440910030100280802c8030f0f000d030440e08804400c002404010740c0c100c08283c3c000d00180000b442541e04251b0b00400c0030301144115000e02d9210900d010410880d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 162102859 1250 162101609 162101629
    0x31203020f0403080c101503020603100b030f09011406060f130b1c0f020f040605030406020c070f051903050309011119050a0b130203071202010c06110a0906020c0a090902 75
    0x1c8002250307240c0b07440e41810000355001a4505520344140f95000005280741e00a08090141c00b80711207002d54655000d0141c80d03880102288000100c440010070f400c1e450001a5006040702c080d0f060840c6010030352642100e020890220391840848200489696124101c9010010120301a81c4540141420780c504070216009903060307002c04110b44800c1c0740c006600c0301c2c588040440601141c0020700e0064101e10441c0c10314651307044200300a00c05540180025500148903120061820014000d1141401c242d508060181a5480001c00c06842c0ca0251141c02c2d00d59504010f480c5860355640640c0c130721610000c0e074140201804a41c1c4403007410b10001401c0a800080038518144501d011507c4107804103044440980700c40114003070035011034080c04802d602800601c5040e00300301c01c9441049420004904006003859000009038141c041c0b416454450942a52101e44460001c1d1030100c950b0000802c6500c1015410f80956410303448a00b107600b44a0001000100c0740003107442100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 162104109 1250 162102859 162102877
    0x6060d021915090f03020a05040509190b0106080c0c0c01031109130c11030a05070308060a09020a02010b010807030b01021509031e04150f050d0f0e07080c040606090e0103120302 78
    0x4840703200003030b080050003072603000940740c0c0c0d0303a2010070b945440005208290900001c2e40054040e6014422802c19510058202c11f81d2403c88816211505c4540c0b0030380308070321003152107440d00401040381c0d540100607150050742c81e100c11400c5c0b21f243c5000a40e503103092802c4504064484884e078905640502c126185010003070000c0008600e5010440003505070f21208a000412521030132100b03070000f01c2500c03000c82c030a40d60240340603800d41381120b6108010386000e5101c00440b600140800d0b680c8010512010143c00200341c2483c11000134040580081900d81850306180c0c000e0220b0780d0120701c50300f0360403030003d002e05181c03a4165007d1850080ea00c10310800c4803160000c20111003110041c0044a031400011810046400c1080340d145010405500c04200c05102300c0d5900d444a810070f0801034041c8400062a01c42040854500400c5510410491300280c52581e800e06040c00307160090304540c2010856203150501c000e000b03001c14840a42044949003021958a10070340444002c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 162105359 1250 162104109 162104149
    0xe0603060f010e04020a0314010501050705070311011b0318050402031302062a160504060e010e06010215071701080c03070b0c0f0a030503060111070501050f0901020f010204031b06020c0306060d02 86
    0x3684109001e4000c8c0360051820b00340007031880c000526584200201c824550380300014140146c070b035a903111045012088000c0c18400f8400e00c8004c0380800c130f40002c002c64060b0b51181f01002041025803000c10703643d00031600403801001003203074902941c82e02601540d416074a250f91000000745107400300410310076100381c1001581501480315000241c7c5203002140c000521031a650b21030030403040312010312030700d406500c0603801002800d40102d10694000c2041c01594200f51010b0750703808040c081160b50f9800b00740c0103003001d03c400345104141da002d07017121001000e41152400000380e503008240304a1034041400104850640e009124503244560b04100f00c0c1c03000f000a14010b040b80e001100c02c0c1d40000d0f480c02841a00c1d80e00001d10008850041c0c5940307260224603600390150390f000060450643c4540040702b10210000d03c0200300650107035501048402c81ca8006c010741502c142c1c440320466020310715080c05a5000b11301c030742d040314048072180140000d603c04601004008405035000c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 162106609 1250 162105359 162105367
    0x1e10090b030a051009053304050403180f0f031101140403030c06050a0207110603060d050708010c02120703080105060d0b0402122205030f030a022502040b010e0603060f010e0402 78
    0x252640350006405008000d03007038503c81e5100c10158040310400c88400c80a41c3d215082c0030440380041c01001c4620203147c5e0100c0501480030003003416942c0607541200040c005000b45030102e241e82000b03001030300c04a41c40320485460700d006007a0b400950b01010b41610b08801030901168050031200300500851201c1c180c4695507400c01500c140700c1100c064480794108400505c1c205403c1c4211820300750700c00d00e1b03d02c044c2144010b00a4a4000030101908908030403507807004100204803150051980c980085071602d01c0100090904c21000a0007030014000e2216400194221504074107461041c1c0c0c600e0b4a4650f0702d0600d40241c180c0040c0c69800034400140c03920202040d4a495121f075015040041c074048120341c00c800c00032200413000d4101e40003480780c15014908000155000300b00c08501500b8048141e4032413502d0a4496000420340c29075035048405c5040601900c8400402400d04512071020407000c5401444014001c078400e080205020340d1036030040d01907200900c0050320454031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 162107859 1250 162106609 162106621
    0xc031608030108060c0403150b1c111f080f060d0f06020a18060203071103030c0613030f05040506070303180b0a06050a090c050909070c0b04030305070e1e10090b03 72
    0x400d078030a00600b40c45000d40e00001e031422219008a40441b9440b200d00402c0088040d0904010200c43c000303e54051500744001c86412035203c0d80803817481c018a801103102c4050800c100040c07610346005640004070000788070100340c120600b65070090340010030042c16540d020024010b0001584020300e0300484160040074400158007400c4003901d0740d25242007203040d82d0342105007842607100d1140182d00400c110000286500d0b007280c002d1002804583c02c1412003006079081500c100e400c0002980359500c21024140c1c8a14002e11030700540c10b10b02d00d030a0401010804038802d4440140c149078880d5050000a16610400e0102d0b94101e101e414090070018030b00b40c0a84110b108803171058080304008240c1e481188145070905040d5190145800003040901c5555035008180000780280d03041c40d100881d844950b050b1085210390307030016807031801823005041191084c01c4140220205a044c181c0040e411405078160a01110a42c010f41205c0c1e508071b40d0210310390001c4182107008814418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 162109109 1250 162107859 162107873
    0x22103130305221517160c05010f020a021506030d0c050a120504080c03160e10080609010b04050a050f0a02130f0801090303061d06041a0405070801150c170c0316 71
    0xba11001d10b80195409000041240c17071510617982c1003403030302c6802d02196034032062155060b0580c0050800c0260503845854280c02c6860000d14038415030780005030301e203180354140000c824200c42004401d0940c10b240740801d6455400c00300403014080303600c8415042c1300c02080030b4940307241d00030703c0e03d003041c03605007030052041d0068818028030344a61500e1342c010345000f1445102000c284148500943d240401020300840090300400210034100b1020604075401d0122034843c0720782000101d1010a040c041c0000c40394000c2041441e03d01d424140a0003400d00203890350400300c400005a2200c7c2e454182c0c5807030322041d62112082c4154100d0000d103221043d04601d501602075202008919a96528112070b404101e00381181e1184c900e000540310320309a405146000c842100030100d00401101080440300240c0d284004122000010000c1e00b42110701000043c2c92882c001044241903a103880e40f80030b0800c0711020410f008500400c0f0b11404205444141c5200c90121290304600d0034002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 162110359 1250 162109109 162109177
    0x20a0c0b0a090b010504060b120a0207080c0106030209060906030309010f05041203080603010f020a0503041e0c09050f3328090e01051605031504020f0901022103130305 74
    0x240c403c0e4948000140c42c0c6014401c0200f110641380742c4914203014520070750b466840003440c42c08159424000c08000c41c0b078910241c4401000800001041401c50040006a290003421984100a20801c02803a914040b0660f00e425400703007059225040e4606050300e890246401a5100c610035515103400d1540c0203160358081e0800b46c0007000101001c84500d020307803040407811400720b1000c002240004101e82da0100041e010300e00100c43c85c51040c0d54042581500758810700c0c25503114020b103e058102e88500c2a003040d8200c0c010342030a1046c5808013142c10039150411045032680207102115140c03000c1007401d05450b4110700307500d07040d003d1942014081e14000c80740114a41104056800014070441c0e01a40400c0ca4080004070707c0042104ca40d0710051510701079100c0062401069200e40c00503104d00d0f0b00b81d00c1c00c9512120310350300091800040c5681034001a0302080b4814400d030300507045079040b2034407004c2102801c45604040e1594410445101010010102c883d80d41c040c62074126 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 162111609 1250 162110359 162110363
    0xc070c09020a120507031a090601140714010c1d03060402090a0902030102070f050312100501050405040504110a060306090e0703080f0c1e060105011116180603081204020a120f020103020a0c0b0a09 86
    0x240003404961001d01401c80401c41d219070202707035200c071900741c2f0216510140a14500c00c08050f01801c4180748100d007525001d0300901c010a44541031648034070241150800210800da00811561034590005882000c4c01b41403d05190b40c0d4100c0034095440030b404442c9031603044080a0000c1540340b6004d6980e07401b02d03c08402c0710703200c00f000c120755440d000041d101300c8105944023410703d8180410400105405401261048000d03803402e10152140900e2500508164030006042803801d22004107070342034a020b07954960004a41400011a880180c81049506404007600c0340e0310740091515058090242e003111100c0e0300120785495100203000c0d4141d4a082e43c518411002d00320071156101c0506078108407424031044140f02da40d10101181020fa040308802140b0150b40380c5495100394454051800c04180c800100829810314100d4076004020047d400c0102c810180c5030941c40d0340180030000d041580028042d0b1800d481801d8016200790000700711740d018200b07104a90010094141d013 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 162112859 1250 162111609 162111641
    0xc1703040801020f03011a0414090a060905040b04210c11120709020c120c0303150102010b1503040506070809030a050901090e01150906020c0a0905090a080c06010e0c070c09020a12050703 82
    0x7c403c03c4150325800b6503080b90382c000d810790b0b50140101308100c803c0000800b402046e90b620038001500c1c0b950b0f401064011401141c500c0d01d0380c1000e007824450940030343c064910150803400007215031580061022601d607081414458144543c50011740016501c410000a62083c001c020034003c009600500584640d5030884107050110b0468031410b0003428070f00315140e0014000102106950b03401c080c810354051000007090840d51002452007040070380002900d031404801c01c0100001003100da9000402420200c5451400d440415502d200740c030580c0041040100710190700781d00411540c006803625010349002507131100e54001501030034100c000d0015204400001e04940041644852804068603039038882c0d0038000c004014000150001045100c1c4650002c04101e10b0b2020380001203807080900200d5150244000b00000c003d40301421001c0c0403c42d0400062801e0b140703904592242002603101c24845c0004c0c0c42130541852070183c50f50900f0100322026070300da413011042d14143c0751 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 162114109 1250 162112859 162112889
    0x602061006030b010f110a0c080c011206150f050405030a081206091b070203030403080d020307090f271e0b0a09060b0702040914031201050a0e040c1703040801020f0301 74
    0x100440540e03888401c400e002c260040c9420700d60303c0c0f0402c42c08080151000840f40d24a08581e40c2c80d01c0c1c40001d5118017419080340c0ac0c0440c41d036a0200b9119450842d003c4140505421b04252407440c0300c15015440600c0251880c110402c0d006000351070091400405441c07800d039407410814004d42c0700d000058105c10300c1c6070003d0702c1032900d18412405110140c100c10311202c507003409180c1552000b1416a40740c0b2081c000040028031420040500c1e0041120141e01c03410400b10180c4035a0080d00007220020300b4040c00d009080300c1000050400e80e40c00c122100100180c010200180030740c1071400c4881d80080c418041c08009034211103003200c0142d07007e4414555980c0401c085480500490030b6010781004034402521b8180c02048016025001c00c01d44048024445461230340b00031001c10031600313048010080c0d490a800041d0081200380c0b585501850305a8480c0313424075039801144900d40b044680c83e03e01080c2001510050032444000b1542c88110303440907412600240b142c10003100f0303506 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 162115359 1250 162114109 162114119
    0x1090f0f0e0c0c0709020c0f06010b040311030601270b100c0b070c051c03110304050105090c040b0d0204050403090f0902030a051003080a1b020901140f010302130b0c03120106020610 80
    0x44500c0f082c80040503158013410122120040c2d8003c2480c46000c0c41240205e400040061014500030440340032410b5541d0301e1480c0c01c1d0b101e6880c50440f18404d4200000402491502c4164184101d000d01101e03403d8018040d0080010819002800d400c044525120404250000b0603003030140d0007028020b620307035103103070084032080b01c8048014032035007003c001303185074400c0340c60324000b50130142c200403510080c0aa200401070704211400e6400b60745039414032401060074000828070580656040c00032202080c0800c584c061140002802140c0d5040050103240c80f070345480008d0b118544410468035950b020f031030042d40040e00c0d080404c070300c3c082c0428800307008000c0140480345e100c1201801c0581c011020740f00c900030401e2006810850342d81c0d10303005075251440c850203408616042005404035006102c012003900d04c100b13042c14030400110b9840700c0d141400504681c0705408841d91403031200c80c03807800c50140d24004002c1c0416100040344682d0040741d610b01c90001e0000c0c5145c0c1176944c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 162116609 1250 162115359 162115381
    0x3060402190e040b0a060203160809030d090603050a0501061e021002030c040306050f16120e07060504031e050705040f0908070501090b0705040b090d03030b1012060503070f0e040201090f0f0e 84
    0x86c071403140940e100f08100d02081d4041c0300140ba81c103002cac40c81107040c0403001b4003080c00d000100310808006603844c003090011a03014403c3d070b5000740e084c4400300207079818040c0c054401211074242a07404c040710306048020610030406818501c400440075920ba081001d50f020f50307a00280402c40c1d1250520001551a0b5070308415540326417004060480045800c01060f28460109480d07a94441c0e11043c2001041c0e408200120040c149683c0d002d035a0703072035420110305484503d0a6501c00000644140c0c010680000700c0d101a298101c1c0c0008030381c030fa80c510644c004c004006000b0034120700460302d00140311066200000e510700400080c202503881c00c0c000c6401d0302c42c41c01425226030041c0001c1109060400050761050310a0400080810b03044000070284a100d6015034006400d10445081c0d04035075000c0c020007024243d0042410504216807140011400d00408440b0301d0ae090005080d6840ba040b0354000b801581d084041c0d00e900d9402800d44035101d40110421424a000480d5030312900b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 162117859 1250 162116609 162116629
    0x20109080d09021807050403030806060c0a0b06010302120c07050c01020d0c11011205040c05030709020a140d110c0c090c121f090608010e0c06030105030a0803060402190e040b 77
    0x801280a850000002541c000614015900340d800000c0542c080320341a5440e03100600400c400e0b250341d0f80300c91540c030b070040503080e00415160058400780018980700000080f60200c140d44101d00880c00d68035078004078001d00820700511540481e51043c0280c1c0458200102103103170161043d02d000100c102c006981d01ea1002000724005030a002200c400b0411a0410303a40c0c940d0305150014003240d03640040002e4031810b4070161007031144610100311520f030411100f0b0050800c00300c1542030400c20040540145a1401000450800092a104440032035070081c05040100020180c407001d040c0407840e5070342c2d410600103005200d1349010862141088003514001042070402034029920b80c20700c24001c0302c4800001c5040d80d02c86102140119190040d98080d0040100004203284108101454400c2840207103002c2e003410070041c00b03252000f080d07144100c4e4000c54032980c0ea0b00e4180c0443c000b8032810901a00142c2e811540007882680f110074184142c404036405d000c00c0290400308041009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 162119109 1250 162117859 162117863
    0x10209031e120a09030b0402030109150c0e0118030312060f120506010f03080702010f0e0306071823060f091f08060406060e190807030503090306090d1d06160c0510020109 75
    0x20011380400c0024a0f000180364058400b40003c94800301c65a2030b1440810740c0c040401d442a03c800c0001a0750340d01504d2a0a5048246441341a214110395807244141e210b00014080140d48c55001c0310200480d00100020b088144051a409544501c00f2014044041040f0b0310b0b400745c900005607203091000208241d0b40c100402d036103801c115034015100790500c1c408000500c01c60007840c04c819036040c0702c600e11441c85134507100c800c4003a42c084811440700541007940d41c0c00120610206004040404010307060090b14115503860800444078241e005980119520602555903007109200c1d540044004000d0740d120340000343c0b00c110400095500d076001c3c00d00082c150501c041483d20700b4620b01d540910b150a03000f0113040c2c882c1101c0e810039649410980d000d0303100081554a0341803c00c9000d038060008006000201518040248200741d40203610030b1018000c2209075241c0d0300c040c1291003c07481c50010440c002810b2502e10180e2182e480342c07501c00c1c0c00c50200c0d200c0803030060141c540c0081e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 162120359 1250 162119109 162119117
    0xf150207080d0207060f150f06080c0301050103111e0a031a010206190204050405010b03041218050d140f010c0f020307020a0512190807050c04060302031509010209031e120a 76
    0x10706121104009400040c0306592143d1100400c01d8406c40318401c50281d11012010000c00300d040c01076662803400564004801c21100c0c00420289406c100141c9056072800d2901144d100c1406201c0100c500584c00103c1c000088580401050200d40d4010f02c0c0700b00c002c0e03d0a000c4030f4142c12001d004400e11441560140c2c109600241540d41c26000038091032981500050034030f80c1303580100d4101c4009810101d4209000000d21040c0845c40c00481e545c60b02030f2911020001d4450314903440710f2464424030340038950348080030f0200b180c20086c8100d400100390888078403507402902d40c0d002c0c00c807141030071010441d4400a803103040e2000c401c4403240341d00540300d16050392411040c451903001d4100112114011000d040b0115440641503d1003a03000b0242139407503966505003d41040c95840c1c1d0a4407482c5891820401610041100d41c0c11003015036801000e0380d01c0d10b090b180a40301c0d40c0c0f040c0d54940907203400032041250303604c10064001c044a08490000c0691140800302c0d20400c90114041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 162121609 1250 162120359 162120367
    0x702150103031d0102070f0605090f040213031113090b1f0f0b03090708061611010501061e0c0639140c030c1f0f090803070e0312070f15020708 63
    0x528102e0200f03c0d110301c0610407210303195a01c10320a4800200354008a00080380040c0c14042458882c4000741504400c40b402c6140056070417200101e28040c0c40010800c00d680d02a0011954600703611020545880b4410301c0118898603003000c10f02c1c012141e1000540d0740003002414102d12540001c20742c1c1c900e0240440315420020b84500680008007901c28500c038520000c10303110b030180241c9002c0c10381c5400c00d44404c500701001801500015120405aa00d050b004000e000d900c2101c2c6c0f0061061f803041180c40117400c0310100c1c1c950600c1c00c8058902ca00f050101c000205a414600401d0051002d030100070f270048880c00da00c418801c4400200280c0903031a13074595403c0700c0c4010060340c80c1c2e80d41100d2415005c0046242400c801510b4286d048841030b00000059045002c2c440c0610002c0b541008440059614060300d800060111006c02014881ca100c02d0f07101040038014100101c400315465880d103190000c1c01c0300040b201107403c3c5051820814803411180252401243d10070070440c20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 162122859 1250 162121609 162121637
    0x5041a03100905030f070c081027022107080d0e0d02060a050706050106030207060f020712081005030105180c01110d2607030e1902060405060c0c060d0203070215010303 74
    0x2e050218010780d800d000c01c00040346a298508010032055118000f10f040240ca085e0b04281010074403a5800100b07030800e462060101c017007007401c003403481444c04484a5005240042502d0040441200d41091b2811101c8100d0b45400141c42c0c0445503e40121201131300c81c5141101c540c1150814160441d003411010b60040c034100014284070500c500e041800d049158440c901552020382c000f00109500250581c00d01021380101d1179101c3c90240c05515103a8581e640700e100c89001500e2500704a02c1202060044045008130001490018000c2c001d07420004038031080c00350000c81c09181482003051400195018a103081c42044504010781040215a0b41c103440030007801c40128801d40c0d2034001521007044098a031809510142d07000120303044628461443c2441158140000c15006026080140c0c1c5031400c440071345a003034602c03945131100d06030110302d4000002c030102d03840180494418400380165010354440e0481e6400c4850061420f00103e1b181c140c00e020140000d0416004141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 162124109 1250 162122859 162122861
    0x108011113031e05071d0a0203041511040b1225021207050a02040608030a171b162a0b12040206090a05130609050f0105030d0f030209091005041a0310 66
    0x111060f8000b9040064481c0360740e0341400d115880d040019080200700091100c40d00c103080d020741c891500d6004503c1e41c01c02c1c0d1949090112890075001c012a11064800000000702c01910000c041c0a01c0407a1100d5040352160946902111003070740e003035107042e0280c5051002644021600e40a6009010450b10f480585895135108440c151814440e040400300183c0ba00d00c1407a00038284400030f140c80f10010000202a05a118170070181c0a1036801070200a10300044294210003003030031803555a24401c0e001400700030100070701900c4900d110710f103009810008440c203411102000c409001441d00c507104183d9a02440503010460640d1000140044c149500104541c40303000300419a61961040028114000c000841d00d00c0790f1100b80800143c4918000c154010503419000762540d8145004650703602c201c9940b4004010b0404055034460b4000d034119001448003a0400c2d0b0507142c42c0d020324400e10f015205150141c0e192010540b000c2401d03004048071800010080e1002101540c0008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 162125359 1250 162124109 162124133
    0x1704140406060512040c0506070f0201021501240c05120703170403121a0a09020901020d09051f09080a0f1101080609010e15180405060c0309061906081005010801111303 74
    0x946d440c1c400c84000c220307035880e280070344070b00c62181c0c6030002220000d1000900f060204203040c0c04541c1e40c0700051021100004c1d0019801c0c501075068541c0038005202110806001d0300c0203000c40c040c04a40002d40810310000f007000e140203071030700d00c030b50000c1015000503064111806000904005002202c24041760080f641d0b8040d28200c44d101700c207282c00020002c0f5625480200e903180d00184500701c83d60107009030000d1050506154503520f1500d0042080c0c201115412080e0040b07134400d40000b58080c01c0f069000c0c1245a084550001003840e000d003280c1401c035070036030b070300f98070400900c90962003540c016101ea0b20140582440c0c3c2d1030040080b60740c0710007a050b0000685104100050f988529024074650100603510f40303c5c9080c079003812814150040c10100748103804100300b241d01e0400213110340d040147c058820030400e408020040041c445900601c24a0042106014016406806c00c03410399070000000c004980c1c65402001c880e02c669008071a555200307003800c00c0403c41c0c0c52051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 162126609 1250 162125359 162125363
    0x504150e04020906120105010809150c070206041509060206161b060b1c060e0102030403020a12090b0a080f180d03020319020c070e060102031c05090a170414040606051204 75
    0x5401d110441c0c3c00101990418100440c4201032100104090742e400480c0b1908200c0c4031001d42079065141c00c00380d00d0b5840040c0280d013204000500003085480300d500f21001442c101d610b084c070002804000400c260410b11a400041c414900810302940e840d0382070002001c6541c07910501100022212007445a030700344144d03a170b1980e40051305030a072104c50b00f03000710024039a01012001c220303240402c105c0b00c8401d18a40140e00c18810403000070b40009070320070901e4129174484102007402ca070444801769950007a0300c4081d004070741030646580003c1018000d081d16064802e00d903660038075811046040f038001210640c480700900d80054000d030700545d04039064802c600b030401c0084040d001681d200d8004045d566004074810000365071000522030b0042800d1028620302070701b03003800894500c600319150288550360800f14005074800c0040966480d03210790a404549001400034450380c20611402c100c6240080004515161612031502a103610b910340604240150b4011501c4820092003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 162127859 1250 162126609 162126611
    0x708040c03060515030f010b030c0603090f0706050306031b010926030304030507020111010209090c03180d02031909080a0308070c05010e06041a09060a020c01020909090a0c060504150e04 82
    0x400700108802c0c2c041c05106022120180c4d02d03502c0094241468045440c8103039542d03174504602c00c5231940c0c01140c009200c0904450158a035110404407508040d1100681d0003603200b10000018000d80040141d48160002c60545034540101039042180c142ca48015900282c180c40d02030011b1464000034903100c02d511850711880d0940c84203000d01c3e50b40140d0382a400b044000c15440c0456038080516049400144c00a504003600c0c4808200040c001070150407000c0000302c0000c05100340303150740600323f1404038200c034210101000042c0d20b903030013541541072724a00401d00078182030040704188119004070005000e82900d548088810f00f6001d45a6410450989403100108009006135200016807101805050a007850909000b00381004020b071641611002c00c07241405c0424186e60082000c800941c4d51810b9496003402482840714403a40818000c00380081c2c0c490004000c41c400b88100740b0b00c4800d076110581580c072806144074445440180d54407869001e4450440144c0704140030300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 162129109 1250 162127859 162127883
    0xb07030e03071407080105011509050609010c020622052202071b0608160903020321091513080f031902100203040b06100f050702040504110d051f0b09070804 69
    0xa0b0b00f16680303600b0700c44941030713a00000d01409029400e218640c0107140403000360b12480109030024284101c4c0c0d1051074030804010883c880c1607401209030b40d4456034000c1055503110003482e151000e0b03074000d88143e5603090380188046141d09182640ca034800e40f41041c40c012174081e800948020b580128000c480c0210b640c447c0c01c0b43d0020411542010303040540b51101286041c0310a05041400754000a00b08207840d40d0410241e02d0106000716180260302e02182d8417100302100d06407a1094a0381c007900507586411f4070100494510113840c41c0b44240c0070120741d00d0340d07e031081540c0c0c9442140c10031070354001b00502400c08812060a0500c400a0b00603591480d0301c682c504812071304222003e1b03406809441c01c03c203181c64424000d104103055820200c4505980d004014298021008001d0069036030b07001240600800720003140c00420b0003001002d01c0745661410a03100c3c41c1e00300d016500c402061610032082c7c0110b025460804501030700c0d0680d19500c02804407203001380600251f034190f007588 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 162130359 1250 162129109 162129113
    0x6031b04060302120a050f060f040b0406060b0c0a060e0102070c0b0a0c06020a030609050906010608161103041517040203060402060702061201061d01080c0a0315170601060e06070b07030e0307 84
    0x882130703240180d580010b080c441240741401c0d81441070400b0303183d010fa0020f500301320300150301803419a0025040b200384850b580d902e01d0044010440d542152005c032001040031000c002000a40a081c80d1040c0418080881841815406c0c1d0082800092a04074080410b11212422101a142c4a9250700d400c8441062940310314080b42c1c4450810000291201d105000000060042a4124415034000d02c00f640c0340641c000e1201d40054a960302e0000b6042000380e29034482c2101041281e1184240c0e030760b0716624054142c44000030000e48002c111603010080140902104c0e0f648075580203405030600755220342c03c200e6550700c949400ca038072031310501c034007000640e4103554203002c0d100ca0380316064040b28940e0f0301915409240340c0c0c40c0c1042007840800c00009540000d6403044040c1d424080740002141c020794000360789542004140038a0f1002501c404200040c0d0f09040351070179140c003003074045a1028072402e03214040c0050701c4800f0b10380c04a0441407003907102c0c0803400f0507074041d80c3c1030a00d65 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 162131609 1250 162130359 162130369
    0x7030f030c060b0616020405091f020c0d09061b0f060f0b09060409320f0705010f030218011425050607020601230112020c0d0e0906031b04060302 64
    0x10860903000074510703a03040410022244190b407010102201c1c0c1c54145094003917400310031480c40500038051034071480801c0c01e1010030003140d030080c0d100140c100755071030788103148070001d401110607000517104643c2ca20400d9806000000c054401035038510302c0c524001207265040e041c407020111360f0607840748981004a840c1e4440c0c1c0010019040d00440c4003800d04c1d0130480c0d40400500164822460442d40381c001440c1040e850a0382030400c40444000359101c0c044820052480c41c1d13032000380c05460803140e0b0414000c5070b8401500e0003621080300b0702c070010408600301d01a254600e2601c26248080c0d0b1340660042020035604507030040307001d10300344070301140c0c00c2c54134400000ca01030100300f12030360020003105009041c1d00401c1440204042c2d8540041280f0f40e6605501c00c0105d541640101941c030b910400b02001c1c9408609000c1d9601c0040641c0c040e501e003004c141d071000055482e1807550080c07414000341070207000b008000f0300030b0030300d041ca030f52a90046243e80594801d603900e070f001005880c0c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 162132859 1250 162131609 162131633
    0x90a0303033c0e0a020d0309030b09150a1e0c0201020d11030c03010302151603080103120c050705010e1311030f011e0314010e010504080a0f0306050f040c020703 71
    0x865a0085407400030314208460402c1d1070004201002401d03900c050085680016241464402c180b000c581480c18003c00da00707010303c0320f5002e50040480c101041c1810f0b0000d581d01708481c031500d203885140c0c0e01c800d401030f140d030b0030300003c0c0c0a0b101d01c54010505041407a000850010780c040c2c500c085000c031503584041142c0313240d544040980d40214640b0b4422031203101d1a0349090701c413042a440d41c582078800c0b01c00c130300c414000248907110340b121041c040400c90b41034031101d5640095051006d051070401424961003440308032000981804000340080c8a10305614a81e6801802412101d0500c17005403030183c0304212007500983c01a086901d080c1440c020b000300108104a241d940303091614481c03a20300d81c141c010050000804441a5022010072101d208403170304480d9165404264407280d9014011204020074151b080c00d00340800e0001e0711006001900e407079241c07a604c2e180681015029034109100e4664814010b40500040e4180740d00000701c6950644192200d03540c0300c1d6228820144 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 162134109 1250 162132859 162132863
    0xb03070e121f11131a0d0f050f06040c0804020f01050c031201080609070311040207020a08030703021c0318120314070809101a04090203030f12060a140a0911090a03 72
    0x440040c20b040d030110300c0c40f07008090f0910034055481c00050880c99001c0702998820040d500340f0044a071a81c015016050707074060682184103003d03a51052003188050305c030a90355060000c07055000301c5d1041c41c2a101da000c0230741840d224010f4aa6540e001c20007004810717180181407003000c11445241071001d0005051000e805800301103a5410210f41901d0050700504501d40340d4031003001807001c600c201d8038550a0201c2103c002d070340ca4885101094400807140e001941b5440042412010582c0106072242c3d17514003800c6e40f41481c42c03042400c4080e20500c41003416054036040a81c4042508039000003000a400d0601182c00720600c0c02d150320900c400c540354000504d08805004489009100701c1c142080701e0201400080100e200a0300075030301525a080c440c40e80c2c2d086910840d2005e00c1a03a4031030310866111515582c0309001140b00c9482111715a2051a1090020500c18041804d1070121440076003448111400d080c1550010a00b90400c607012420038061000300360380c1d02c03450700d000c2d41c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 162135359 1250 162134109 162134143
    0x204150b0c03070b18100b030a08040303030b090709050a0905061f0206071103031005010f020a020907030c030501050d08120703151202040c1e031503020402030f0412090b03070e12 79
    0xf14142c18600c0015a0141513554070b90450034601d1034085001405066000840070700041d080020300000e45400104e0700b0040448038041000401e05030141c1c0680d0f1141810703600399400c0d50b2055021214803070745000b00c40d07212078184424032046946030b11140d8041c401511044a911000b480380031440354140c0b501d00140d0042003003201032540718044821044e10300d0002d50450400b40c1c410603010034140169030411203450303640c0810700c1c0f003000341840d010b4003d0402c3c403803800e03c140010064200c1403a1080070070b00704400054541800001c0e040c1040e04000c6007414040300916140e0000c90281207103041507110f103000c03201c4485040c1220002d16070a0100082c0314500d2040c8001d80c0c035100b00a10601081a01040c04151300306e080f4181060075183c0010414000400340e20350402c243c10194000d032000c800c1002103180c582006024070702900140c480c50411302002c992000560240f000d80d1502400802c48180c0203140389101080f0080c02030501074104a840c1f880d160070013070703061a50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 162136609 1250 162135359 162135367
    0x20705130501180b31061503060503030c1b0111030f071406070c08090103060306020c010209030f0d052a06041208090706020c06070c12030309020102070906060c0204150b0c03 77
    0x504a82d51a0a61901a440140004031030300b4001000880084021005c2444400701c1c10a405032140e00e5601551400e1410840951116200034041040014040110b131030041c01041501d000025581803106041c000d11802401c1c103c07544011288440f9203060040c045003007554200d00b44007a061107004034110988450311424910500e400802e8244080d1300f00409110040742e00c0400f41000759005010244d540032071100480081540b548007501ca684042152444148117400030508018118100c924034040030306613689036a00c00c40b4220218604001118190142141c3c81454180d07032402450f01201e00c0000b0350a0030800c49040720121408960310360303000e070032405094200001d01d0040110030b0170010083c0d0350f440d0f040645407103018040f03148010040d00f00402d602070200e405003003084845030f24028019019400d012400b5000320a008110200f99128880c1180d000c1e075681008101c05800f84001400503148001d909a000180030815004000041c055000300e400150341c2c1e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 162137859 1250 162136609 162136619
    0xc030702180a1503050606040b0316032001080903030a0b04020403021225050315040f17040e0f270a08040f050301060902040506120a0605030a1a070305091c020705130501 75
    0x2c4403407107190000703280020f10041c00425030024195078020000e880001c4c0c2c00b5150170000c1d2500b51410200240c1c50320031000801000103c14040300c20001104218511103210350040d10800c0c801ca8403010329600038400160a600181c01c0b403110304101400c01440d0a0710703500800c00620910901356216803202124444107030b1010700c40c021524200701078035003003403c0c0710010380c1b80c4035034602a51754107800718041410700405040541e0a542e22000241c85601e5a042200d000e80003445403180e10b43c0c1120004480282403212144a9030700d440c420500c825003400070f00e1101000808543c107070b1152450000c000340e0f0000040015202c14540c0301c4402e8508400c260a40e08550041d400460050204210b83d1300e40b402501c001d4858014007071140d80d01d51056900506c642e91100ea414070a0821800a000c2107118100c0c3e2006802811b1585554a6a00341d0503904140e8aa06890340680401c1014640400e10080000540d02c16100e00d16958030018034859082c9131054001542d40004000f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 162139109 1250 162137859 162137861
    0x3050c0d03091110110607081909030c020d06020c070807051017010e06060c030414010909140408370810140d02060d0207050703120c05070b0c030702180a 68
    0x34950200c1c41c0a0140e40d025a03100000d1001c8001583d0050310720144440700d0a0040d01220020100002107075400d19020744003c0103120103880c1c815442c0c01110001c200c0e80c4070b0303004803180190541c03500c91100581e036081c85007141e000c50381a40e640c0e03401c0c0228010041e06100f9080100160402803611078200300c20003c5a481414482d820300c00010142285258401d20440c1120f4003440741114a6640b40f002c124030b0b2041c503644409a0200143c0410000c484168581207080c1c01eaa600403225100c02c00c1004507241c80d42002244030b80a0000f90000d01d510300201004031200d0004c07c09101d012207810082c001040d540b6641c800c00b94a291069075200c8038481e40702180f0817050072400e1030684a001101e101201c003600a074900101c520035516a201210980450303110115940c0d00700d400c080e91641114001115441000081400b50754800c41b114458a500000034008151500811112a40c42004010904e00041c080040907a40326602c900814440503001d00b0f49240400740d0f88 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 162140359 1250 162139109 162139123
    0x603050c03011e0209010e0d0b040606120f200a030503041d160c0519080306130b01050906090301151203121802100207090516020f010c1713020402030403050c 70
    0x29000780e00d820001690000307000c0b110b45502c02e02c2e40005030345e220b074100100d8035119140c400340e8101d01440102c200304000303901036078403031405410704100e025150050661000202c0c40068194104000400301040508140d030610b1b450500303088010004510215090580799030007a1003d400c08038041044046403400a401c44202408454592401c0388881c8800b0785000c014108100300c2c145400d0400134100300a0414020034003043c0b140907038a00c0c202030702c0e80c01180c1450088a802c1801c03d591a4140114203a446050f1034a90030032455000f0b0081c10703001400401d42c0f40d034885800c00113010591100034040d05540025101080030340c00c01a12601c0c03413104400320a490000360342040b05a04009504d990784c1158002411120503504a15201550b00903081091410b024400300803500d01d0f486c0407120154090340c00c0071070001c008900300c640100c40640450300500031032020300b49681906500c4054800e0009070341034107402190072070300201d034110003090300041e0340c031a0104204001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 162141609 1250 162140359 162140383
    0x51f02120903061b04031e060b040e030f090312030a050720102318010f060e040b040512070b070e060304050a030807090321030c080f04031d090901060305 68
    0x40c0345000340040110b56150001000600304504014840051490100c112002103800820b5441c8058170003006040d000300504003250402d16050200340241054010007002c0b00550000d503081020b0380c40419240e90050452a5050192540c190220703a030302d0015600461000074002070915201324040d040c42c140c41c42d51560040c501101100c1799a001074405400141c80d5404240c0c105280c65040110200602060b4a040c0b42c80410044001d00d130010301c001c6007064024003050302d0101c0c00c04100d526500a011041205000050200301d000e807130f003604076110706d041f620302401c504040f03210341d002410100c0f80c041c07000041c085080c0c0d1014024a1000007286d40300d155003016610302d61754031180c000c0201405041d9000650182c0503500d40c400440d003150b16402161450700140c0b09041002c014a408a85003038000700071103116828081c071400c00c030081110720391200e4406846107690147d074400b40a01c200e04028403a00c03a40c542d0780c0565105400840d0341d50452900c50b0030070000e0361360 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 162142859 1250 162141609 162141643
    0x30b0f060a0f060309111e04110c0c06210c091e0108040b0405011104030f051903021902060714010e060702010c09030308340305070f1215051f02 64
    0x105004003400c0441e0b1808a48150030b0000c2d00c480c1c14a000d101d0108051201a4091481e403121148042107800140c040c035001c0320708200d401881078080c001c42c010001110082d50000c842c0e109281441b1009013841201d82c180800126100300280b09040d80807240d0218008012030f50103143c0c00c0c8510801d4600c0720080040303080b07108a00c00285200001040034101a000c0c90200301441005c1d030000314030103048284c1a0b5610f4582c2844014142c02e07403c00c0b1100c0c4100da20b4210900d01c90390704001c0d11981940a80b4100d802d64400d01d03035076001d071074080e0b901c144108a40700004100940342000f0b040c0c5d21001080c4180842c2c81e603400c0c068008c15040035039041c40d402041e06c42c0e01c2022102900e034542071641b4075840348250314284a2203044144040b5540071030344200709c4a4844121002c10055405110503564135908a48040000740c6a4020407084040e01c911700714180c004c2264644441e030500035480da01c000007000f540321000c01c20626400300c000d600c90294144105400002440b10f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 162144109 1250 162142859 162142879
    0x304180b0d0803150604080d080901140403080a020c0304030609050d030606140d0f05040809030607090e01060e0f03150702072108090d0602040f0501170702060a0e100501030b0f06 79
    0x8042880c0d81c0480e00000c1c8600b50000015010851029100b0213143c4007910075a180d64a403000d03d5078902c0c642c020040498440400112140c10502801102a06054003161303651101da805a85e08a8060030300a90305809001003c900c903020070151004500411010a0702c04103810150704046000030356104150406c1c030144001d80d00507031401e801c03520ba002ea4a680301022005c0000409101418900d0389052109210911010a010b803046201c00c805459036911080400d5600311404d100e04200c601401d401001010300859076414070315400f50000000340084ca0010341010070250340480d07c0c140e00c0302408505503042000002a01c0350600e03000c00c41c000c02c1d0b090050207890001c003c1004000003000361b2251075003451940d8540c1d01500940d244d44d100c0f50111544069400b80d0b90005120f030802039906d06080c5090b500a40b107a401501e0280c46020402c400780519900456040c031803400b5254460000e0b10610703000750b0044000c070509090620240c01c100501401c2d440c4604850300e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 162145359 1250 162144109 162144131
    0x16060905101a030a110a0506030a0b03070e04050c0415170a120e0105180f0604030602030601081e070f09081f0f0905072705150f040219050906041502030418 69
    0x84c060441c0d5030810904111002204006149502180c00c0030360802c001009001c010074032600701c00d141c07403811003c0d40d00e0262214000340010204444c00b4265a0001503410151f0410303a202840c0328600c061782c2075140303440c3c0ca8a00302d00b8600840000c0207501c070918840501141c580000110035541c90090558419a400205580605202e0000e10b00c0d40b2080e18005070b07a401455a280c0c44c0c043c04007601d031562410b003440250421124580856203600006403074070038280c0d02d80da120b248a040f140d50350f160884111102801c404030704050010140340810200c00c2001300c440400c03d2809122140c1e006c104090701aa101201c0203400c0900707250240c000100081b9940040e656064040c0440380602e4281ea100d046a070170341c1003c503e15020501a00c002c0b80104128442c0d4241e8103d55100c604205020492042e504d0f0f502e6042851103003415114403c03030041c0680040200703e582400c0c2c4030790f01e8110382c4502e4818400560301c001003c004980b10111211a5510300c55001c200c022013075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 162146609 1250 162145359 162145363
    0x50708100b130e090a060b15120a09080c0f0f161703040312030902030c0d05031b0a020a0e010503150702060a050a0f05010906060311030108030a0516060905101a03 72
    0x6014040100700e01107000b00900c0503100203980100882154941e450130b01000c9182c5504a0140584045080ca201105c0b60f08103c200a10401500c030022071501890b84c404a8001e1800740aa0b80d0080e01c3e08801070100d51480050312480011102401c0f0102d0000e88080c941402005032604541007499a4048545100300c1141141c10404c000c03801240e40c0c03440d2500b1446107400c020400c1c4032450501c0c1e56160b155004a1075a8402d5007201c0120f610030003017261460480358002c006500810508101c0a07548240340002000368044800e48040350780007a00e1118250070901064480c02c1c0100b0183c40c00704581e100c3c0f5074580600340b0480c00c0461000b500e6500042040d02095155401304a11a0720703580100074815421100f00015610717100c241c000317080e1034440c4038006810300000d0040e0b50000e0702100d04032403c580045280035202102034802d03070007004019907100c07101884a07000c240d15000e02c1c8100303481034018001044940e07205004849260220494914804c1d02c01040c079140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 162147859 1250 162146609 162146641
    0xd0519020109020d020405041a01030c1433090d0b06030c06070309030f0f150507140a05220e0a0e12251b0f030212010213060809160e06010201050708 66
    0x51b900481c580d07441e8109090302041c0c0108280103001240000400d0003204400d0b078050300d075008074444c0100d0701c90040010101c00840341600152508680f406480c8800300c0c404030307000c90369100500b0040c0b080b00140011030250703010341c1d140700766404010a84c9824480072060301002c549050902249480040c100c1090780070003031411078140031502c28410320200c40d81656a00400072903180c52840700b28070185c50b05030740c10b1000c91020a420710800544005480e4000200e135a200c1c2002100c041c107010b080082548a46620344228002c07400784c0036807401ea4400c1e00d41c840c0203e10444980302e034030320b0200c070301054414041e0107011900303410542410004440c0004d031401d00c5080611b0420b1302c00040031944407940b64070322040c0014088001c0e203603041140e00866560b8808031644040501382d00ca03000ca1980c44628024050040c1c078041c220964101000d1750440b914003103600c502030501e11680d040070001030b03070540410a4940c0e0900a041d44205140b42074400c90070718000fa1065160 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 162149109 1250 162147859 162147863
    0xf1207030c15110a020d030605030c01210216050303100b0310090203090f06070f02122809030503040b030103230705150c1207170c060703090809030d0519020109020d 73
    0x2c1c8070074210001e0540f034001070359100040800070342c1d410440402039600c02e14012508042410400000b60f1480c0100d660b2074881c07010f850354119840d55100c1501d401480788030403c0b40e19400e009003125072064a40000c40c40d131150004580c0c1e424a001201d2840d141a8040001c541c0c04200304040540448155011500c0880307026072a510342d100c2082c204600f60090102ca4030980003009011a0701608460050faa25000d440900b1092030341c01c89070b40b00e500d0000c2100c00701c03409443c10b08004030941c0d01c0c01214601c1c01c605a1070702d96503110f0845e4000e5215909580c0f01100520501c040c070342e5a601d8450005040b046201100b2032125220110341c07180d02d00c01c52080050483c8031103c0d10842d0a10120002131720721003d0b1803400d001c22500100d00680d0316000c481103003c080b048003011220050307400c2000305000d9850810490180118400444004070184000400e52314204039084041041d0f80311a501d500c000f0b4045420b00e2880c1d06800d003107a06118109015803a102200100c4076 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 162150359 1250 162149109 162149123
    0x14010515090c270a0915060807020f0106030302060a0b04020703090918081207110316110a030501020a02071e05060702040b061303351902010b040207050f1207030c 72
    0x25490030800c0380b660260f14422949000807100c0c444020707000070000b0710003032012a50030000381d48521040f412600f804031144e43c01044400103000441c002d20080d41e210100344101c0d070a4400070320200707007920915403040780580d00c03441c01c0c08040c0206008014440c0410381301141005001d4070b00400202c11403150562880d960328019544034a18542041c1240d008846203650f041c00707c400c101028001c840850018203c204100a81540030089410000f41c2c404084030440d1a80c80e140f198410101c1c44590202c0302c0e400000000e0005c3c0050039032494160043c1903030500e000034169508840104442140240141c10720660b074030ac0c020307507080503010307640010132041d0800810158800c0d691684421b00c0880c02c0042001a070008005404018001c258103500006208952013184180d049940000600564040191004c0140305056151001040c0d201c6a8008542264068001903a080d04406645100c04004200418405007000740c414604611510010038172603103904014140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 162151609 1250 162150359 162150361
    0x711030a031505030a0503030603010c0507080f090301020d06060c02031c0f110a020306040c030c0503152d01151e021c020f0d110c010206041e02010c0b131401051509 73
    0x901d4900c4110b0240101138215126004035040c11076070390300110b41d564425070910144c0c10f401c03480f500c10303a080c0320f900080c040d0800d054880e85030000d42114400300e4042d9802e100100106050380900c0c0c0080c1420313114103e40420318010f041c100b403460080e203000c1400724044002c91030340c883c0005c626820b0718a0104030404001402c681010440300e006981841100d0034403090118000b058401c83c0d100301d0152400e00c0c0d490082c0b50701d031030440c42d0361040b0240040c0003c1408030780070495044030342486203c1c0000c19034102d440311021380130b8004112004596840070710b11500070074039042a0b0b03c0e590040403101c20f03c80b0001d58489e07001000711311065445c4000d201c0903000300041110000c0900c291099050540700c0213008918291076841148a014050341d001c2d400440d416003e5a040000e00031b40c0c8842000f00c3c07501e0306069074128104072803548180007145040b12004e0140403580c1444e42e54283e01d04000c80440c2d400602520303c0e074905403d200e41c0c502e200614400c60441501e0307185407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 162152859 1250 162151609 162151631
    0x405061b0403060606030b100e030c010813020a03150b03010603050a0f020109091a0a05040209012709020301140103060614030a09030e0402030a090b090102040501050714210a03050711030a03 84
    0x8500a507032004000c0b0741810000310f55a90075070402546004250341c40a03803030103a018122845600380140e140c058110401c2f2101d517504c203030001a03010496103803a054010b40d55001c110072510a90040d56200030f00c0d4039844004081d40150416400101c0007400754a0640d15007a8503400703251002807514210400c01000c590084a003c0014158480204044c0c03c20407640d040341302440502c40d101c0c1900b481c01051380e2038103100341c81e0f105606075140500305245810500c0b038a004c541b814400032145c40400039581041d030004601034200310040c04a0024850300142c152040380d040300c02030041e071400b920b0b8081c1131002900e50001c407203000802c014281e81016101c0c410046041500507000004100c0c80c40500d8000700d000a00c940034076256551621040c90807030240d802007900081e020420040450030406205190401c0f0b01c0030741d000032125008286070010600c1184030351000105402d02c0e03490301407044a030700c1101d030305000c21104001c80090740c492040207842014103a0390508000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 162154109 1250 162152859 162152911
    0x10b0a0309050706020c0a09021c050a0e010c02100e0708060411010c0209090303072709020d020f0301062c09070f09260705040902060a0507060f021201031a040506 72
    0x65450b4001c01500c0b00c4644401c4000d40307880706a4582c41c000e8081090000d5139401e18821128001d500803c00c0b4085808814801c000e030a01070480c0d00405d40b5144c000c5041442071040d181000d020ba0010b01e8120718001046069812100c544c1e80319030440031040008100c082405036205502c581e400d84030141503070060314094040c0401a411212400400040c000000001c50081099031668055a510002807001017045803c58540c000c05030303071041040502c503401400d0198010100513052000100700f95034590000d07402200010301041544e824a00c40f0340490000d04240100100e150710104085081c1d000b024200c1c90801c0300d0040e140303419611500d00c0c0030203454403481a890440e0801d00603140c4c15550000c2c151903000d9200005101d181034440c2174030941d0701070892401d00084485c03d0302c0e10f8000c03040685155440790ba21008544152008107004115000d411510f0b50540c102203064101d041603c0202c66862824000450303400945035903c2b5003451a041c03080c0f0422056a9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 162155359 1250 162154109 162154121
    0x105030112030c1e030206160207060e06040b1303033e010914010b04230106050c07080303010f1706150402161e12022b03062304050c12010b0a03 64
    0x1500020400c013407020014000710054000500070b50032921151101e0304040308034003408240b040035912449080200d2070080f80d05842509000300803c0c1400d9079141803c2a6500c4044041e00203444110300f4130030160811421401c6010f18415500e8111200526040d01d040c40710b603003042c40c881c1c200202c075001e00075004070380e81a07807041503000e012408400c04c60103080c02c0065188079134103101584d1407513103202551a080070040e0000c03080d964a000400e541550120960034101e00030315001041c800400c200540c02010f131201c1d0031a03442d107070481e00c06000001913482c100b190016001d1103201c1441c5050440290000c0f02c0040c0d0b180040b501000c14103040450040c01a001611000345052811060642c0c03180101d0201946250101c0c2c1207072100341243c01801d450010321803200c0107059015240c4010070380c50074001030160b12000306c1c0c400b9410030348007500808520566a60306041c81d00078140c100102c07490307c0341031152181c528103c01a05018541c0700c00300118000400c10f02ca41c02c2a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 162156609 1250 162155359 162155363
    0x90501050d0b030d081015020a12090e0709080105010b16110109050307030b040b06030a020303031f03020d060e0d0201110901140d020c03030906130b130f0c0902090909010204050105030112030c 85
    0x84038011a1031402500d420400c854001b1441c2d1034280016a1001c8501030700c01502c001c0d4068200b88480c0e40c0c0305420000707108180307000c0000816000c5400010303070313904034020311041c0ca404411030310b0030780a42e00791041608041c001032070502005040b0308885000110709980001861018a480c0f00100c940043c00e500656262107600000406d002124219a000b1401100503145954a0a061583e29401c241d0002c1d016030040000684d001010300500c5e04c40c441d50208010b00c25078903000201c0502c07007900140c802c140d4409950741c030300000300155233060444c0d000a00020075000b0a0380314030300408168a0501202c050406151184032080f6050070300056800c5460781504810580c0e0380e0812075000c001c610480c0040f400310340c0001e003183d8100d03503c842924015603410040380c40880e10450120348512018101400003007481c400107000e05051900140c0302c1201ca000c0000d10034014000303031308a910404c0180032590384202180e0558860404aa810310404e10b000c84d0380d20b01c0d140300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 162157859 1250 162156609 162156613
    0x715060501090b09031f200a021e0c1314060910090e01020409060b040312080c040b0901110f03090f0a0b03040b130602070305191d101206030c0e070f090501050d0b03 73
    0x122106c2d0b0140c1d441750305241c800120320500e418080e014000584540d0303a110000d42d0000d080300400320301109440301c08102c100d05442d0790380340303050108401d8511440480c0582d9141c41c1c400b128412520034042e4010030407900903500d8100344140c90741c15402c07406560710840d00c03030101e01281c12094040750010640b510f400c001545d03882070590741503049804111400d91208504002ea1803150700f10900589080000034a06442d285007110300b0392140c411070341400000c1c1c8030040082d00905c0a100005014409969580d40a0741040080f40800c240140304901d4214180000e50003d4103583e07200c1d81c00088072003144c880c182c1c0f000018805020041200e0300009440c001c0580c00005040712885520138050741050510040d1141154015039004401802407480b5407442e20aa00e01501c01d0a424191648802c1d05c038404155296500305541e0001021800c208032480000d0980c1e0001003441d00442c03c0c2e0003500000e007a40001e1045c103042003000b003082e2899002c42e5010465000c00202 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 162159109 1250 162157859 162157903
    0x8041103011401080c1504081c030f15030b06041406210616120209030c0f061b010209130b0d060902010513030b07030507030218210d050715060501090b0903 69
    0x28105a072a103945e0345440c0074006070004418414001c400385c90598080a0241c102244121821003001040310020350415444146c001c94201051065015440d501040d02181904600300240d00d41c3d000b401c0c203800f45241001141059440110b905e070845000c40d14090035420314481c019450b00710702e140325103c0c001c00b41804040c0410020703a1010140c0340e260017074480a20728246089000740400160140c00030240b21540b86040d08603402d400348010007071401d0498030107406440a07107650044665030b6001401e00911303e40001e40b10f02e0460600801c1c8a00394070300700407030f0300c5108814004001c6600c9840d61000c681c051010348951101c1084a45601643c070300b8103200050041e100600401d00d04000300302c0c0c0e42e10034004c50700a1a031801844017048440b60034002101c10048801402d0b203c4a028030091070014054290381c100f1580d1103603124032180c1015219a035211600288031407034004204142d98004407003000f180c03024407005444600c20700c0840c0c00c00b4096810007100c07400c000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 162160359 1250 162159109 162159119
    0x80d02030304050c0904020f040f11040602030403020405010b25142b39020a0314070f050a0902070204020702120105100902030c030c1308060907030311030a08041103011401 76
    0x10790b1085024000311074054400e5030038000300c03410980e0041e410401c900c8400b50141000d42061400c9000002d00050212850400f0326040d00a504210b00607000046d0401c01d5190500425025248040300e180c60304074002c900100f844402494031046407a200400d609009180030580403000d8100701755840604013603000780307200846120005400e03150617071103d4401c0c0310700c8804a482c030401620f41d00d800410000351100000440500081429108203d00162a109450401580300c0c8103588a8610f1030080e060404645030451280d00c42d110702d0400c919a2900b440744112011150010b90702d00040c00450042d100703414000e90001d401a2101d02d20301015800707a4410070000c59800030b010b03242c6000308183c1c442540c00b2401d001051010520464011000305181001c2101040b92150346800031824010308175000001500174400070418076801803640c214410010010b035140400f02c4070007134400d4001920150031440c404181010310348003580140d4503400c20121080c842d680d0b80b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 162161609 1250 162160359 162160363
    0xc0c05030a03050f01060206360f0303040302010c021c2303130203010605060a05040e180f07060e04020403050307060b0a050a0e011d10030f021306090912020f030f0c07080d02 77
    0x11368020109a515070700026080b8404200c160007044500001c02e180d001c80e4110120f80050712341c2c09210b600402c0c203e0312030818200905100c0100351000b4688a01e400e08003e42118000807000f010343d000710318100100b850030208041d48401c01e003401c0e246510444900ca811410602e031071404540c00105104a440da400300d0f1032113080c4200d00920000d83c8403030600030140608803040d408281e080c4002c1c8255494420312a81c8101152521912408100a91490888004940242500500303800e11203207510441071034804400380ca0035494a85142d442941d05c1c461804054081981d030056200d0036942c0702464801010001c1440000540701d183e0185048028810700c4101980020120304281d0400c841921813104040440302a52840d120041d43d4000d5a2040f0b81c41001c9020603040321201c0c0c45120041c115114000a03207a10300c2c5000b05008a03051045020b640c800100041c00c00b4000084a40030610b000d116a150003204901030300d03058132508003074180d00484c15000354450f40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 162162859 1250 162161609 162161611
    0x21605100501140f120312040c1a04030c090209040b03010e0706020c04181403070602070f120828060e0106051e04080307080a18081c0203030603030d0c0c05030a0305 73
    0xc9400070005641c1e02d000014222000403401c41d0404444200c0543d2481c003a40001d41e018060810303246414041c40319241d0710901103d003100c60079990002030001105213062100282503a189103071801e41162107400c6080070328450f000c181d5400146211060300c030f075008003141031000b03070007884490382814010b074464119024400043c498100105040d00c1e00e0b00074080000003146948840b54000e441343c11549840c8030744000548004c015000026003644010040c8501440700d58850307424a04e0550458600800c1c0c02e07040243c810103010f064081d8a00b000c580d82d40d07900c03004000704080e05104000e40301c180c1c0441d0f01d041c00d6000020348642c205000b48040148852503070040f540e20303c0c0c00903640c001c3c4d002c1d80003658810301c081c500040b03400b001406200060304103190700c00c050507107851240d4180e41003498642c1145100550b201c030030302c814222074040c80c006581503141120101c0c0d981d000341302449072901e40f8ad07040402e00e6401040821116500710381581d6032040e8600018002d400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 162164109 1250 162162859 162162883
    0x6180916020d05091f170a0902010906030b0a050121020f09031603210302070203011d010c031811010c080a1e080108100515030109060b0a080a0308010e070201021605 73
    0x903038202e285080d84640b0446500010041004041d141da41c205141e050901840a85c2400240651079101c04031100c030b15440b9074101040171a0220f080e1000424040159000d07005060a00d540c100701503071440482d0341616020301c2c1c905040500810103412401c1280d80d41d14226200041d501d01c1351004800030014031000394122110b041c20795800d500c000b0403d120240403038045110804d030000c0b0514420280740b4062802504003009500080e086410005000c8460602e081d80d20640d0030080c000c0c080a05418141000008141c400d407043c8008500c00c01046a07043c0746002c0401e81c0580ca02d1000c03036410000864854001503c05000850000c580d0f0390f10820500c526400c09108202c0346060307c00020280094070210000c030006410050032a071280741c0d0549021030561401d11408103402d010b800c012511280d0441400026030144d00601d1040c0c01c000d0310403001c2a00070101c5411551100070401455030ba01c0d000700e00a01400c1104506415403d0a43c0c05100000401d40b0244c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 162165359 1250 162164109 162164113
    0x605120c150309030d050709030618050c09060303040b091519090b1809090c1207050a0503070317070f050106030f05100c02070614040305060103030302120f0105030a020618091602 79
    0x64040040c0c034010340070440b0344030b90f41c0c0d104104d0300002441ea908990b4011146083c00030724541c4a07a1940300342c403c01038441440040e02d03d04c4000307100b406c2080c2e0640c00c00036141040e544c1000703008a03440e80714601600a10082c0020260390f10f03160701418100300c68040003103c1d00c0c1c0b8011314486648861442800d130004069460104a0b45c01000440d0424144803000b401c0d03450f00d410900004040044c5505441d005003440c26a61751074040703881d10005003082c042c012040c04c2404010501066822650095001650030700000d1441c0b01c24030084901251001e031a0040c61501700d0900ea0701600041c00d075402e0a10000070400d50303000c00180c07944198251000b03103014801080464101200d5080160310619040004601401c0d000f42514140d1441d2407500c0d40729142c8a180110030b9108900095000910020580b0f10513007158000000c10701c0e004043d4900400030303030341b1303003e07400003910501001074401c8038200d11f00814844200003400720303003061600c1c484810f000c05802c02500058 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 162166609 1250 162165359 162165379
    0x807030c06110601090518010501060203030a0624080c0f0f0d0b03061003080d14090a05010b0102030f1206040b09040b0402030105061203030118061206021e04120b06040605120c 78
    0x1074002c240c108102000e020041140740e19040022000e4407026008164003106500d0740c0700c00c42d0080c0211780c00390030580c000f1070f5a07040c42d8194504031909544502d0300780407011070b200c8000038036510741d920b070344140d01c3c0c41c0440e0b0f26580e0031a800d501c510344502800d000700040d000c0440c12000c010307225580350424100020807903001416200c43e02101c070044811079041d0180000b45401e8007400c20307884188030010b41d40c0282044840012029241d181181d44040c0300c40080240c240200180c2445c00c1c40554101100851140c40c58004c00181012040c031000000d01341c0c0d1925403180c50401b0000b80a0049420142041e154200341550282d000313500f0240080c0d03031410400c42803181d50a80700019071640e860641000201c61580302c60324072954684600054a41000c0781c25140c0b54044c410041e601c42006200c2c0000c00111420070442c100244000c0100b40c00d54400c0c000a07540142c450a803a036a0500043d00405950708901e62010140b1000005800d0004841e181c8500c152020028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 162167859 1250 162166609 162166619
    0x4050703020f120415020403051e0d050415031806140a0b0a030b04020604090908120f061c020d0606060302040519050d121b030305071e020325020a0807030c 69
    0x40c0d00c00e0030801c08010000300f0030906000306003d05a50301901070744014441182d100c8080044e030f809170b84103907481ea10149480012000e00200e007000b03800c54a0041c000c030380f24100d001d0a14082d6200c0d181e694811801c5600486000390002d14403950a0317012020480014903141000b860030840c2c840041601c80c0c0010022440791242907044034000b4421003155265035550303000600028400c98000b0401d0100048003981801030b051180e11903030101ea25008007014118500c0380003818030500c41a002e06105850320b511400301c039001110f50303402c0a42200d50002c035055840e50b240c02003800d441c002000a445515502800684c2d00480e144048603070859040c1d91810914010b40f907000e550070b16001e00044013600c5a0300501201e090a00c00a05070609030001020000400c0d07011030340310b8041051a641c000071411015084819a413041c000d903100c003e54034050702c1c1c0031040c0c080f148004202c40341d441c8010f1b400082d600a210603000d43d1102c0102c1c0d105c1040b40b008981d02c4030082804a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 162169109 1250 162167859 162167861
    0x2040612060501050316030905030a0207050909030a081305012c0d0206060f0904020a09110a09060f090b030c0909040507030b060901060e0f010e030a0b1017060a0b010e100e04050703 80
    0x7084440503541d2900303648a03005941041484a501034050555420f055030000b00240068400942250040e00f10340d49040c0c07e000c003a5074010301a400c0358008000803c3c071550005206a000202440b210401038403a18001c0e00400304e02171071422060800c8015403440740360002c24980c5940c00b00580c2d01114082c2000c4e40e0310001585d6540e072000c056101c1c09060b08000031611b50050000300809034aa603550303000021039603031125060200b40001240144690401c1c0c0707550040c00340707240c080c403007428028009024602c2c0340500d0304074087c000085a060f0182100340c0304148402400c15072641010b14280380d80e003c1038031040790703c0b111842c005001845c0807a94035040710701c00d80b83c02c01100303500c404024a02003016541170510465252100709510100003039a0154410101600507080c081900d4a2580555111600130b1a078607240c0480c41c3c6000c280c49800000c68034020484074214030041e40c18182e2581042e82040ca29a00700c034040381e01040c01031030000143c03402c0250340c0310108124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 162170359 1250 162169109 162169121
    0x1513050907090e1002030c070b0a0605041404051c030e07080a0605010b03060d150212150f030708030a030b0d080a05030109050f01030201091809080c0706030e01050f04140f0303040602040612 84
    0x9005070080c0514000300f00c0c4e0b94008540c0010002c4555142068175a0740814003c0300b62501c04445a48860501040c00c10b40704101100c0040b00b50700c035641c80c140c2d48140d135500080020314110b4020303030344d2a86028000d405c00410764885100b40e800d543e854250160352a5003054041e140c02e41008000101c003490305080f00d01442c4040c00d400c41d180d0700c5880f02021600d5450b4000380441c0e00300400d400d0090308a4219000786c010401c4654010031600400c01c5d482c2251500c070303100f0b0300718110800080300000210364040c1c50508001ca0000d4600700000c281c00d91580c0085e100d58800140312010541c00001141a509109010841a01d40b80c0c03809110507000d001c001d0104d02e04a02c184031313451080190801082401a0101e40080390355612101900000b000c4400360b8031440c410700002d5014010506a00b6101c0020801850308080016001002410140080651003115802420180601507000410000320388c0d9901b414500580207600c18829540010100c1d1404d58208100e4003d10b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 162171609 1250 162170359 162170381
    0x180b04020c060c0c070e070c0620030a0b041407020105040b010603060b0f0319060807050112110405091305010e0303160e03120a0207080a120207121208151305090709 73
    0x10141559994000d010a504c1030010303101903c160030000420b4010348000310b1141040d55541c0b0601c00c0245444002d848001d002d0480440e0b003610a0048901d081d070a40e80e02008900001c42c0c1046942c000c075000f041d02d54001d140840c10441001001a0150403035030166205103e1b000c20782c0ea072407038214119000d902405031071160410020b03000c840c0c1807001d0340c2c110f02115401c01a5901d0b000d01c030011508158020308564100190400a5680004d11002881000030042c000b0b401c1d03407050b522403445640102445002e081d00072864449034400315240c010b512500800001c0160f121440e60f907082120442c2840481c500e240f09003901c01d10054101d44d0001c3d00404100c150501d0308210b5400c020301000440c0700700760b0700041d0b181e8100260084036004040180460f401581e00a04280b1a2b07001072404182900201002800300c45040e500f60001d80307050811034440306c1e010b8000b00200d0215641c0103015000b4448070300b44950190b40150190801c5504c201e540351150400e0380d0860b118 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 162172859 1250 162171609 162171613
    0x15011b0f020f01050c011a0301050a1509020d020702100e04110909040b0615040b1e04050a03030c020604050d060212012103080606070606080303100b070f080a0c0c180b04020c 77
    0x6030010305010900c1000c100050400a0034010840c000c14216901d801140590085a5141601c00c0c10700780308894000485c102e040c041c61400b0000345068440741c0c07140d20f442c254000ba02401c0c2261550594403085d134003c0c0012003005074100d004241e22840c5482500c1030303250440081800050781c08580d400310000d0301c0343c04242e449890301c481d01c100061559070481550080c1380e80d4500e20740b000740094005140041d40f02e074084501c07103160001084294811650420003445135682c2c00d4920402c495042c64806111111480400c5090003039500c6941c105090181c0642005007a80140c8041a2030302c000541c82ea0340c4001d0b000c0420402c0fa41450010240040b0402007441140da03158000c5014149a14011030360303440d0ba0844055030b01041e000c1d0000300a100c01040e8001d0104000e20a0303055031814214580c031072000540643c4001802410005512020796000700c40c0d65446640041c070030008107550740040c0d84412000600d0007042490311808075003910b442e1003616510350940c80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 162174109 1250 162172859 162172883
    0x1110406080708040f0204050c0706050a150302091b130501020f0703020a090e071d0f0c03010315020a110106030605070e040e0307030c210f0801090903080a0b01031415011b 76
    0x8141e443c54000352003610103001014819025031a20300401d805111000910b0365980c9243c1412001c03268058203800c10701c1d04004000c641486250304003000d036501102d0213041038030303100d5003640204056444044242c1000c80c0d0320914000c0b04542100321082030302500c8528147c44070282d110021804020340c40320802c041806507074295400115400b000c141103920017500c1d0110800100d14010041f8031000d50342d006c00008035100a00180c011221000d20b6017154159502e050a165142a02c2e250f226408282d501c3e03001e11070420384440940070070007081803507164103103070b00908001c4451001007041c811000701241414820803040d11207843c05142001401d0f070b0201c81c000c0400805880803000003d4803a00345030082a80780e0080340c15154256910001d05010340750450580c81594194078040c02840400d0300304a40903808030b108000020100c815100690082600849a14400a060007044a0b0000b89260007140302000d813a80c02c4811030310602d9085812051030020840c5074660 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 162175359 1250 162174109 162174121
    0x31003080906040306021201080c09070806010810030b0403120506100c023a030f1716090f0308031f05030d0509311d0d050c03070c06050307020111040608 68
    0x3005030980740c00041c0014a007590700d449140990700311a042418070300c110070042003401000c010b80c9201070010784070074591b4540004c0103012400000d2600713040c071000800151000c0c10201111014540c88442d2106a081c1410010084d0844100720f411407450300c1c0110708a45401d0300b22003501c0c0e6142e65503510009031503080c03240c42c04004003146000410580501c0d1a22016010100c041c000c4601100b00c0d41e2060a0082c16200402510400d00c65425010740900d2000c64159520a041a01103035404038284c0c400c542c9000180d0184003400c210060120400c2001c800450040101041038500c808042480c0c0022404600c150356059100c06a00c80b54140030b03a0103011105401009440b030361864000c6800302e03540700c0f800000c1c045010b182074045800d0900c240600c410111490031410b003a40010f4940e5038800502a805101c1e01040040ac1c41d5010002c4500308c0d9800030030184141d69403000a0311581050303c100000d9402d14034a10f9542030002c0c141c03011524150350b000e440761101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 162176609 1250 162175359 162175373
    0x6010807050307031b050301051906050d080d050702100f0e0c06030603031c020f070309050102060a05090303010b0d02090301090f03110d2c03010e1b120615010c120c060e03031003 79
    0x2414030b8010714101020004442e039027072007124440c610502d03060114903403103801201210f800d40c00240c4200e82d036941d40350101d0b00f402d06a03105800d198000044584900505a290030010002c119280c0e040030107a8580b1180798000c224460207250486211081010400003207010440b41d0640550041c0f1044403051800d0b0891044888254001031420307805200122030399100f02420341c003041c809071042000d96410456194001c0d15030b2410400c89c01e11007100ca441e444188075001d9403540215840c14100ca0340c0c0c0c1154030303030754009000300840c00c52454204203142c40c015080d400714010915141e00d410011440081800099031000b00004858880c8071510440c904619a100d11319200c000054400340708207040c02d100311004100705054000040c060840e120041802010000008001d024002440c550040d10540165091928840c0103c0d80d9940711070700580b01b940e05942400c05160465003580445004180901c0000070000c92580d480c0b0041c1d44103815400b841c04108041410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 162177859 1250 162176609 162176633
    0x190f0203090a110a0f08070e250e041d010c1e0207050d170703020601090c0e010806060a0c080a05040312050909060114210612010e120c01060f0b0c0601080705030703 73
    0x8003d2890355403540303800e900405e85034160814001130303114a4091141c041420901a03003c40b441058580382c00050550841d018603904100d007d01000e8405440669030340e41011a81e01307d84011010741c01e11909102e80030700740704042440454002240031011441d480100c03c11042d442c1c00900d25185080305210210002ca041a40e611400c02c00100c01852004020300351103000b07500030290340d41031849001c2258000d2890750184540c18120580c4c0743d03080001c15500180c00c0300c0e000d8607200c0280046e1500c9c1c05403c00100f207400d0000700c8039840d98008000d0020740f400784045001e03c01140f102a5401d118501a0725882014080060000d6224141540c0ba030a1070480d01c5040481446030365102c2001d010f5590f070701c6540c0500708400c030f040c1019902d0342100000d0081c84045104040d442c1c0300e4024691140b000000055400c1040109401070f80040c4401400401050340d9005c1d004003c1c0c00440c2866918007914000152520001508a05482004001c0c1281518540d41d010380400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 162179109 1250 162177859 162177893
    0x30c030b0603010f0507180b04060c0b060f0d0309030b011a030609090f100c080604020708030601050309010b0603010906030318050112020c07030c03050303060306251202070506190f0203090a 84
    0x1d213903403241c0d000900da8060180500c00f26140c218401c1503015010840c0c0000d40c10001c0d4400e4140801c0050b071b0740c0500450185a001000d500325520b40d94003007035003102c050480c0c0c0e0f0013a4034408042c007055485405e03041100e0161a08140380c2e40c981520b50011106110040c094050030b00210380c0525003031002c581c11005110440300600350034100300c0e00b02040802c12a8006540d46e008400750b9411100c03040c1c2c08141103174118580b00303903643d810225020103032855041202c080300041400600f580300944400700106820744039a5100210806458540411000941403044079005100b540b181c0c601618070507100c0b00c900c0c140d03100140c0002d41190721843c50300d1041e17400c0007000c10700500f0410302450259020310b81d649401c00c189440d220001e020002d84901c01d1280172600c0105002c4004403d9051405030281c80740303801d00c18082d0284003006422405410140440e509686042c8020030070721047c03d000f642c1d005206d4900302d0104a40e4585241c000d031409800003400c00d054a19902 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 162180359 1250 162179109 162179111
    0x130314030d050a020d1107051902060409050411010e04140a05060f04050a0e0d0807080705030402060c030d0501170a0b0a050c0c0709020309100c120e030d020a050919030c030b060301 80
    0x10007100d141c241529800e54050007141c1e40001c07204440e00080c05203401c000094201b051604c0182c0c1c1ea00b903525000040c2d546a42812900d15001b10b42d9100212402098180c00601071401d0605100d9042c15880715003074082400e0032900d4080d4103150150070041214044000d1295446000440203000c004010036400525000d120b1515501c0340324640c003841c5c1b003c1d0300103011b812001c1c0d00c46c5010b440c41407540c18010040e08110b49141c1c88205e45501c59103a240c070300d840384c44620100713510740503154554003240408110741e07003804000c1d4003050484540d45000d00c550800442c0342a110068042c01504440c0070200061240103182c001c281c02020100000b482c03d60f00040d001e0030515241c100c0c020240e00081805450b21040015030241c185900c070400a643d034544001c0c0c07441c40c50000807450b031900c5078a240e00c0c541d0309200342d070702c8040b044000b9903503220314103401030060744030300c032070a1184c802c07140080d04840b00120040147c0e030b4461f034034010304d42c21a2180a00340000038a8541c3c59 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 162181609 1250 162180359 162180367
    0xf0804021809031308011b09050303040317160605101e0b03040f0b09100f05060a0306150f0602070f15020705060f0405060f031504050405060619081510060513031403 73
    0x1c030194622003001881e0035400014001750b040d18407a4000c1c0b6010107d0100705410405201030754012040b2000c50342c2c04075205d841c04030110349961550050b004031040d969046164881031140a41183d4410007035035442850464032016001d4845088100f007448410508105020b8014070300c4c021508917000304810005000b043d1b46e11030b1203290441d52405a600007030b0310f107000240d403405131381c0c0c3c000411201840f49141c45004108070007801c2c80090651912000508040001c01024001074131345115480c034400d80301c58010350f542005102c3c2e030080c140100800079090070f01654407660b8440c16405845042d14201c2000820f81002d0540070321440c00b0000000e041c1c3d0385038000c00d58401c4061f94152a1700c0c010310a03000081040c821a070086041004100006001041c21355119000f119a1350021541c1c40107003412500c1600a01c21a2042200c181420b04418160600c58849a22400800340e240c0ca009c841501410007505540c564980007400050800000010046c01d2641105c2c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 162182859 1250 162181609 162181627
    0x4150611030c0f030a110316020d031b060218040603020d11030f010212010314061314030d0e06250c0201050d020d02030a0b13020405010522030f050606010f080402180903 75
    0x8283d414907501c1040d500004040001a40002840c2c0241321003002441c10400e006500f0000162060300c002c1c0300e200c0c2e0b10281010140900226070302030200a4650350921000d01d0310000961216840e050561440c4814060078605070051030f007629030180502c9280d1901c0e55401005125400c20540d050280c00800714130031100f480640080c880d0015501a1949942803210f4074001100304000300f9040182001601511088043d00d203175400105646041404030326035055010700e003c180d000a04241005403410400581c981c080c1856546000300008100340034040340c3c034000342c00804141d84802c580050f42c005c03030180c500003094030005071904100040410490380215140c13481c23250380764003600440c2442c0c080a944c01001080452801c0c0c14400040d00ca80100350441d2540d01803c0e05800700b40a2502e0804000c6510050b40c101038551131400507140d8804a8000d80001e103144e02500c081c034800c45119000d40d4000c0c100c0303111503040c0054035204142c0104401180d01c41044a884 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 162184109 1250 162182859 162182863
    0xf060902060c101a0d121202040b0f030a111201031401062402010e0f070b09030c0901061d0102030a0507030f02010632030f190c030611070302060604150611030c 71
    0x3449003d0b2040064140b4410034282c40030410364584038003801c00800c0c14070010382c001d00c0325030900700da9082840c030080103541d1240181c4625005081c10707640102c0c64507003a4020001541c0548041103042c0701c440d07040003a14581d80551481800c80e808030800400c085611801c0c80410500c003400003040d05901d8035000b44c0071a00c2c441c40e4410b01e044c4034140d2800c0715420712030004000070610141c20301d04844140c4540e50f503228050b071140a00f0025822099580c100503050307208601801e940155039440340c02038010030119002d261003040510003440d00350b1000c002c84100812a4035000c1c20941152801c407596904d0300d07403007070966594160102c3e00c0c0b0914004403404010a80755001da0781903041c69040c0c580c001c81c6e200380c025030140480c00a44480803401e0340c1300048803d10003403160064140354280b200f065201802d0f032860300902410300f101000c010081d05001e5001c650560f00c68906000c101c8024a103003020f149507045007403040b14420849001d42c01285401c41e03046c900c0041400d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 162185359 1250 162184109 162184123
    0x8030708071505010627080d091e030f03050304050109063605060619090227030313051003020702041d1212010e072d03060f030f060902060c 62
    0x14800c80300200d00c4070100310070501a0214100c0d1100103020b1075250860280c44500c2c0002c030340c0c070b072100b07407002010400301c0820000000302480e20807210303a0b0f0041c4002514554a40c0204041d9041d480c110581c1c00503018602c208407a80491081480c0056071002c482640010f0421181c954070303110381c038012a195000340900d82203000441c140d07520301c1c03065546181c10700f170640004001030070703d228022400115119601400c11b86209140650040c520715165186030001381403284042901400d00244640c00c8500f400000c0c0e2460b0462054020035030380b80285005440802c4150505100b2414070004800580341241405070405074258002800c0e10506200034180002203201580c0d02402045011181d803007142e582880c1c0440484808601c2d00c0c14007405104013016004680002c1c4500520000d90151807484d040481e840c1309000e803840d82d02d02c03c007030009041020104050402840180859501c1030181d40350b03004a542d4800130b8090450b042e030703010b10144264922500c09102403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 162186609 1250 162185359 162185363
    0x70302070b040b010e09010608031b070509090a0605150d17090a06030f06050603070807110a1703160212040512030d18050d0c03050711150d0e0c0d170a0306080307 72
    0xc10f4290704102111036011002170002e200c6a040560421a4120100403151030001d403e81c004060f290040300d00b4a407a040740e100c5508800041c0800210000120300c40c000c1ca48180000c0c000750322f4440c003c1200484000e03080f9880ba000c00c03144400107000a1108444507034101415082034000c42c001060320003158000b9000c2502c42034200a0010a80306000292a084a0040c19030408220051102d900103081009100343c0380000d070503e0000b0040c00048035401580c09840b040d403059000855001a11081c001e040000b06000d022400840c0112881c00611040b600345443e001c1081441004041e030304840d404200407a2000c1030680c05401c03281c640140c02128003015500d4032a2410a08c1311840040241003181c0d1030000b0f9014003100c28080d00807400101c851840c01c0060740c02171800ca07003017160b40340c001080107641c5903c1d0030400c40041c5280507950a030103400c00707001604624003401031484440c58005072103404d0b4507015048075021842c000883ca82c9413907120b0b2446c0e001001c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 162187859 1250 162186609 162186623
    0x10b07020109091b050706020403050601140906030d020c0114280207060203042301050c0a030e1206040203070603110d0207051c0e180702010908041211010c080301090203070302070b04 81
    0x5010355800401841c0108581d00003001401c11400460414014201c0c00c181003110005a04d418088a50142d802541c4c008003690181e50b581c00c4a0000e035008050414010100080007824529010580f0170300004160003130450511184011a5405255039200003000001d1203040111803440011601e0481c0c40b42d05501c183c42c1490000e403402c510395101030219802080240500514003480d50302101c1000390340c00038000c3d4080160341a00030b1021214103885140c826a051541c4990040080001030701d544080c80120010b464507000100e4021f5096800b0b00b00070030540e031199020441e03c028400a5034146039514a0407405d0303034000e60040d5442d40c466000b4071019000542480e0301030300b050034051081e084010214504100c8000c000d80c05840600001d94030600030741049000c282d00822466441391907244003148941c00c00819980041c5032801c49980c2d50203501c152454075000812282141e00c2c042c0d20b800603602c020b100d0401c142d000d010280000e80c08041c030500907441592 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 162189109 1250 162187859 162187867
    0x201020105010b04060c15180308060a06092403200316030e0a030c15061805010e0f040f020a15020328141b06040b190b0a0b13030506010b 61
    0x90a40d101078111520380340c02003000300201500b01012030401d550200c10400100803441c0808000c00103185a8001d4000c02040c4a08240d40202d01c13038070500d0100d030046030460f101c8004894485960003541904200c00703242d1041031150382d1040c80014a10700d80861013018500c0112442030381e03240401d81404020050085260380d203000c2d059842c800d49001c005108030003120139074428172044080c00f44030498041c4003d0114600700015000100b030700c2845442d030381c0c4508110034004000700140c0945032000202d05011840f136094010380380d04060120648450f01d92000480b41000d0032640034001c0780f00010542c44021501304120300703503005117495000209603006c1440804000c500740200d40d14603184996084541e101d000181502d8a03a10791002d44188601e0001000c0080c142b032103805c2c00c010411a441090300e1107500c1e810340b40484407000c18140010342d00304070561a805000210240980304c0904081c1c82c000281c801c0f42100079a507a15281e0800d035003a00300d0840294002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 162190359 1250 162189109 162189113
    0x702120f0c030a020d06090312021303050106120c1806090f020408190c15020a140a1502070f020409020f0a0f080c0117060d020d14010207170c0a080d180b0103 70
    0x407000c031180c410254041d01c00180242d0004898010b01d000003840075036a200d10310306052140d0350103500032000010455440950030103168120342c0c01d100454040d801c06a021542c6940c0c031001916103076100004d80442800c0540200c022150360f0396083e0032540d103540006002803039004490441c0c0c85030000507940c034100346805007400c01d00d003081001840d1076100c080000b0600e1190000701d403490700d045d80218124030022400c18a45583c0609581c039407a040c11449000402c070303007280710310074000070809100107040c0c0401d07406041000707004a540c0b004410090704080e00000c5c19184014001d0711081032000c00107001c00f5454008100b00500c211061214600406c044401d9001c24240762150410b1050450b01c040001807010303000303d40302e003c0e100c110348804664085555000304245200041d98054500035003104c2015214a4912555180d40a803541d00300d40a000b9490007038032011046454801c92a40706644410304c259503030b44950b03010410503080356481e0380b007050000c89130b52642c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 162191609 1250 162190359 162190363
    0x105040e010219050a180b1209120d0b011b0b0601090b0f07060b120607030f0f060b0712051b100c0305010f03030804080f0408100f0203010b0f07080702120f 69
    0x18080080c0d03807040101d0341401d07100b000031110920441c50010f607500e800840c100d0708010724012218540300100404070f1072650440c042c6c070520031a0541c121132956800c0030140c1e10040001c152402080402000c4004c8515403c56a41c649044c144100000000440204000042e54003a110103d0f294140001076038801c4104d8000c080840140b0305004034075284074040c0c41681001491503680b0004080c0a131642e020341031740c00710a4010f60b1014500568060090080320440009040c0360111040141050344038500035a0b80050085042000c190788a9103c1301e4201c82c0070003800014081d141314030040b69000d91003036030004007601c0800003014014040e01d80c035072134030000d060411005100901081c0c80c00802c403505071a240b03d0703944071800c1603007040c411406550f1820800160100380b07407c00240c07540d1961445007080000904401e10101280404e0266941b000c500f002082103410070310010749580e50140c641a4901400f0350f002170700c200d08400c04440c840e040000030b65450002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 162192859 1250 162191609 162191621
    0xf0615120f030e01031e051009020c030c070501050a080a0b0d05071401022407050708090306010603092109051207090c0201050709150e01050d0b030615100504081209011404090203010504 82
    0x282001e00005295403411900001400382d03c0706ca2540e00c80003d01000d13070405503007009018515007190340303500140a9513101c3d48102402e003001e1050b203134009800d511803401c884520216603a0400552600d80e24640940030700f000c20b643c03120307610b043c141c04568140000340c0140800003c1200750307260000060306114042c1415440c018001900d00c9501040303e880039445021898090342d140202e1800f0044c07402645100d542610404002003552601540702094140c0a944403402d0f201c9405940c0c207000100c1c44001000030010002003003941030104442c81c4084280307040d2000c20752585841c0040f80c4c1412079102c010703915082406807007604405164064803030640b8030b40008041140180c81a5286450b19042020002d84d282c0c031503405d54418042e13140014280c9045042ca40d1079103405410400c1c926200d850b1802c0c40d00d028078040d5084500326200d41d0050503200c400391200941c0340d00328210290502580d1528445811101c0d40140050200c2c2580142c032541044c050004a0b80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 162194109 1250 162192859 162192887
    0xc0c0103200901021207050723010f030e0a0206181014040b090609060304060914030408060f1f06180b030f06220903050304050c09040f0615120f03 65
    0x46006041035001c94100122074400001142140e510303950400100d2501c0880d07001744c4c96500380890500200080828001e04560443c0f851020a5800740409005c13031740c8000207240860038982140111901035000391300040d000390240d0b0014a080d402191081e1f11000b080d60780064080d01541ca0f81ca04080c0c40da40c0401280b615881400111100424a12444c09014130300000490007040342d6135a00101d81c5940800b8054684a0505203800d0020348421007045854418031481070915410000c240d40488204000610301516602c00e001400c0030050158151071041c940301e846407041240f806030040c0b40325941c401c44003d048503000c01500d0640c000c2c8868600400521104d02c0260442c20341054003210f0200350541c61000a1288021785c8010203100e034200340c83c410034942c008002e1441140900c050300e004c440b018040013010700048a0080401480c07800710004141541d0210780d00c1c19640d912024442e854414070038411a1010302118500240315101c1d04241d4804a00c2034045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 162195359 1250 162194109 162194111
    0x100602060c071e0602040b21190513020303040320180a0c03090c09020a030506060304020d120207030203061602010c0801080303160309150b090f0603030909060f090901020c0c0103 79
    0x42408114480070340b08034607016196a0303a074a4a21101100c03910a080c03ea03511100031036a8560320165040c80d600420501d910a4034982031000c400c00421014a02c501595403c00d0110486020701c03c00400020304403140c5800e66500c03090040c0c80070401440510300804003003010070191007428038138500e001c04841c01080d00c5015039524054040b4016000760603484080b50030350080c03004070010100060050311020051600040ca12603d82c0200b04503502d03540c043c81280d4803d41030241510050310020b4101041520200224009008210340000e4500c15590281da9940010749050000c0d203600c1d00c404682055243e4040d024450085501602c3c10103100070340c5400f445603240d00006040c48c429521114a011085100e60300010f801039000703500b8521031700b8607000c07031004040c00030b000d500035018603002c03c049640724465144a01002001140303008000d105005545101410b11500425a0f0101710362139903502d59200e2045d2107040c001a1103c1c040d441d007516080c100e50195040c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 162196609 1250 162195359 162195361
    0x7090905060f04020d06050c19020a0507030605061c0b061e010207150306081506210613080c0d0e03010606030908040302093301090f0501170a0f0903050310060206 72
    0x1035000c2812a800111910328000990382c500104008100716507000748424034207020460381d001b1a40c090309200740c20510209202c480101c040c2e81d111a4103202030615400843c04000007501a0401ea0788000040c05001d03035140010502c4010341c01002085a10b52494800c201d9181860800044115140d424a07159000b00f80c0c0040d4480e02e0502801d000c0491900412082e1400b0741c200350700401812040761071041021510f5020710101341c1e02184964091500040504082e0155100441340c10025020031317110101002c881c4140081304840e01d80301030144081c3d800e0180259042546141c4421008040c000101b500b10742080d008001810310748007030b4001281c2510169420349606407880b0480351250011600103250800e00d850041b202038800395049100e6480ea049800000e03210083c146441d24000b000d40f1030302d80a15400070b88069403080c5030007402c1d1300003604462140340015501c6000d0300410195210039005131301085c070000c01d2110943e90f00d019040206500c0c8054941 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 162197859 1250 162196609 162196613
    0x403170304020609040e0111070311061b030a0e0a02120a0605090607020d1107090c050403060c02120f0912030a09030515070e01080403020f0303190b03060105150a18080f070909 78
    0x146000d94185680a540e88640c107800c00c00c825844039001e283c90090149d1108283c0c41c0040051502c0114540140a03200c00301c0c80c1d5a0100d13290704501c40c000e29a580c11503581000000003003e00c030600321903e10135402c034240035840345045801444140d0002d00f221421505060043e0341000e803218030343c2e50100c01000f09183c1d011498030680d01251802c4c200d10074003108528030700f400701c0c0c0000000b18601400b81050b560030100500440c2e124040520625421000580e2030782200c00300c03502009400c2080100c00107104000b06440c00008200c1c00300119807c05c0945541c00420307414020031441a024404d0203c00c100c84c41240e040500d103a070140c501140010000481401e0107410710611401050403d4000d015002030200100100d94072898003c076024134a071041b0201d404202d1602014403c1e500380820060b041c2c0b4000b9044100c0b260040181d2002036000d0070030481007044003c00741c4040052900032100600001c0018207913090504006810011030b0307448004030a1904400c400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 162199109 1250 162197859 162197869
    0x902211609140a08070b09100c0b011203200d031d03040b0f12070e1815012001020408030403020405060a0612090303020415030c0207080d1709010917040317030402 72
    0x400c2e6006000000007010002e804525180f8858200c0c40b154042d0f0310022404200d01c8024100c602c6040725102d0485012140c2510915a045400361101c0303104401446085161100300690078841c0c03803c6060041d0303000140144680221810100da00504c41000d84c0d958180030706014003003005954514485401c01c0d403a601d208502c18034a803070401069403404c000408056610001c28aa80c420451800d0700b0010309088001d400203214440b005070340740101000d012464400d0809640c000c21810103240191003d887c88401c1c030441045a0300c403615803076000e0001d00020b1250380001d644542c07c51042000b40c42c1c1c01441c1ca40201c0b516034007042402e0748050300c80c440c0150071100140350600750408a01034492508503d051a403d002410822641070f88494004010741e4281c401031610b2f02c0c1e0751a05d90588030219000103010407410603095000c030040302d030000d603550f000140c0400343d5603a40c80702181c0c804012180e084c000c84c1c100207101103405078166003080b8200d014510318140e80010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 162200359 1250 162199109 162199127
    0x31d0613120305040305070f050103050a02040305031b0f01060305030c010f0b10031503020a061814010509131409030301030302060615041401170a0b03010f090201050a0f0909022116 80
    0x15000710060710340c0000b072500520440e000f864100040d00c06154444c1c0c841e0070002e0040c461140003902c0c040008000c8407151095a0550341e0000145140000300d80c4c2e070000054508031081d905000e001150165010244140c600561040d4042c640f55220f40302200d084480784042c00c41c030942011507540f41d40c0d85d113031404514900c1e2410001280010040c900b0104556600020f4109541c410302141507600700c074a14050410000d0208003c640350082000304481c4440d0460100b50b090020005502e0107235412020100025000102c080b00031034552a05a02918143c010b40c01c00001842810742c103001c6030360710039400e540c0300c0c12051303883c603c0c00040c0c8a64800e403945181c5600500b00c07141e202c2c0750b105d80b80a10711124028a801c20a540710000d280d10600f041c400d40c6040060b0b0b400c030229018090700c06405858903414808803c009803048084000410104001070401082008c0a48043c0a201815591100351060030328040e8000806c00743c00d80781d0794a01c0b070b03040c0c07d00158011324038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 162201609 1250 162200359 162200369
    0xf0a050621340903060510141503060d0510020f0c1501080d030e010b090403020c01021b0a030215120c07060507020f0703060b06041206020901030510080703080f0f0304031d0613 78
    0xb01c500c0d50324800048031484010380000b4282420300d0144070a424074283d001d0f040c0c413614204c3c003100d80503d1040140d142d031400500c5880403828030000d45685450b16180c111240a8029142c442c01c0b03260981089030b210341c1c6110300113100810540b030000800c0040f503201813240e24040540394144a007440c4c1d10000403004508040d101da00e030030321002003034000740f03403c5c1800742031a4801d0a19140294a6441c6900010300600c03400385004580540d04004009008002d44410601400c6409000f41c18414a0452800400c10040c0c0a10320201362070b010710507050660501d44540c00c0c0d28080068501c0070701014115408240a0001500d001c6142801c40b544070030009404c51821000c1840c0e8003070b50b8414070301440c40340004402e020315600105030301c180c240c0c1c0400059844010840c014070690045a245a02a840a000203292540185000410b0f4118141001594244482c1c0c561048404a000501e005000003202140c28105440940e040b01c0c482d080540100d07600e0384c81c00842c03041c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 162202859 1250 162201609 162201691
    0x9060b0a0e0a1e05040c150e0904021e1e041a03100f15060801031109011d040501090206030903180102010507050915090402030408040f060912020f0a050621 69
    0x2240d1485000e800f040240c803c04141400350b0300d0542800c0400704a1407085210221862a44442542c4101c2698180038001010101c3c181c885800384030a040c0041200d00e090042c02d00c05c4a030700d82d10b80400040c6000403a502e420103070310711000d02040e50011f4407904412841181a014151341c01701d5a0a0301d205140070001d00c401200650b0400740244525440c1020060390010400f00e034030050a9040e41c0c041d00c075124204c200340040c00042c407030901c5641e400c1c011000001943c0312504c05410380040c040c10020584c060140c0000d03206a00603504c1c031000d68400a503582010380c81c80382d182c0e140340c001d00003000baa10304000054207902c03070119158030900c44440000805401c8100361030b260b03000644115181d06d09440c1600c580e40c89400f036807040c0b60074094005000c40c40b40c00300341d05450740d620001143c0e00c0070742e007408403510341c5000d50340c0d0210406801040d41e407108009014100200d48000080e140c40842d90b024919014110203000c105070140f1100c0400c035503055990032600300e50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 162204109 1250 162202859 162202871
    0x40201080a091716030314060a0e07050f0a12050901060e0105061b01090804030b0c070309180f09030e040605060906040e0613050a060f05040c020c040b030a1509060b0a0e0a 76
    0xf9000c0030351001c40410303180000000c6030300010100c9068001c0441c078441d403030801c21142456082540d03d0b404841c056401980c2e04414021031a214261542110050030103506014284400c80d000790040d0304002d00140480282c007190a0041c00382c25049407030b190081201509210040000c600c050043e180141c02c000780c441c80b42c0c42150000c01c20103032100000c1001e1000c620b0b0406841d401071000342c07050310240340401c0d00f50304034801b00c1c0c0c880d66054071442c1d6810f140c0140b81541c03600324010143c82950701c1015038100300701c600442d00a907120740d03076078804800d201e41000210340c41c94004900580d814001d12120380c4494040720f040e03130308502d0070880725500c040001d000c7c03400c200b00d414101414030b0203201007240707a600258165407400302c0e10301009440f401070000b240d41e050311523401640300c0322912030203040036408840340c0f40026080c0c5142c1565503e558406031100030401c000196151000024060b0301c2c8074a00710480204d546c4640280b600708150000b43c80a07001c03048181d6a10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 162205359 1250 162204109 162204113
    0xe01090311060405090a020c15070206070305040c03120f021204051804080f0c070f09020a120b150a12051501081b091c0308070801060c110315180c030303040201080a09 74
    0x240d800802008084621342c0c60407030440b9001c8e4101b07001140951040c0041400321408036405103101d040b1550061181d030361001d00440c080c220142042d190015926000b002260240c8a03502c119245522003000c02c40314450021310708041d02c10003000da803c007840280f0884c0d440c00e641304040e46e0000380c0c1001c0c5485909040c07589110b9a030044244480015140c0e141c0b190202d8204100c40b401c00c019202d140d907c4082c0d5003030f80f1501e11540001000807031714500c0c44100b9480100b80da5001b402082071101400d4100300d040d4059511100420495001103035080c100380102d0358442000c0e95183d982501601c0041c0040102a00d541112207903180e0078107060002d0000c0c6c030390030b20700200b6000d071620035480d03942c0902058000c10340c000b64100000541982c0140d010350b040f10400e036900c2030303010b549454490281d0080211140e2600403e09a80782c0d08000d48489030064034220b01c0800614422005a46040008101c81e0300a402c103004000c00b60ba04054980d5000f0425a0046010f04585c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 162206609 1250 162205359 162205369
    0x15032d070b040611070501030618050403030908030a1413030c0b07020109060f09060b040603110d030c020904111201360605101a03040209070c02060d0501030b0a06060e01090311 78
    0xd401c841e9041c100071400140560344505400402143d0401355071000d6217400046058072068010056801d2055800d200e11840c170364012a8054000d00d400501c030015030341d4010095000740d58502c00140c94640e0300c840a0744010312150042c0501d404515860075640e00580140c40046d001740c094140000056442030007904200c0380950f01102c20000c3d2010788940c00c00800d9481d0054428915000301c05c40542001e00c69042529080b090031003a1408000170428242c1c04c0b040d0440800c003003180c405006031035400d00d244c02244190980c450344d007a040d06000320900202a0780d007030341e030510000b08058a2049110a002004041102c1c2408252040c85102c1116920001c082d070307240a00704801070503220484030a5510314510b000d07031492420084040c502080d50044c3d4498400c00104500c1030040104030f180d94400780120b4103010515038068102c5201340e01c10741d01c031b00300c4608010120b0703a0b40c030a1303101074201402d15040440360303040003d0460109003c01800702010328040540781d620 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 162207859 1250 162206609 162206623
    0x1903050a110f0105010603050c07110922080c0c03120d0c05071a0907151409010c0c09021804020c0c0904080f0d0902120109020d11150307030515032d 66
    0x3440102ca405244415680380203240901c11680001e10304008940f10030b04840880d000540c11180d0051101104000c20550840240c80ca01100e40c462407a4110401001150a40e56000c0c10443e910b03502188140e80c1400148031885119400024100f0300d95074a5500f40d1b000e601400301d0008030b2094180303007641c1a01c12420301034115400701e4441c2030525070b4030741060321842c81c80056840b62661105a00d43d150710140460001c03500140d010409804007501030704045605142c00c504052268070f82d4080000c03160800c9145a0700000c5109041c00c1d030700887c1ca1400420b46003140381c44444010b0644600107015200e00c85d03001f0001041c14044c2c1907080d115050b88800e06142c1e121748021600006100741c960403409550f141e80c000d5559403040c403503142e50940103001a01c00b603001355150150012241c030105d501c4107030a036040800c8000380b4051031040d042903c002889052889015180303240c101e08541c0702c0e03803007081550742e820783c035610b280100c0c0c08144040700a901380700c00303039810585 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 162209109 1250 162207859 162207887
    0xc050603090604021005030c18030102070c0f0306050709030c0330020708070b0c070513020705060a020405120105060102031605031b0601061d010804031d0409060605040606021903050a 81
    0x501005010200c100451498015842183e05e001c00b40080e01094945002c200c40129400c0c200b4001046040000450040030035802000146400b095568201c1003800542218801a0b0408014020000580f0580e60040481c0c00c2481c0c1c51442c60b038075102c40758541c0c0001400030307104465034018020400860314420304914840d030007a024181000350b85840710f00c101c5106118150000610380c051000311240c0040e4403000e04406401c00307050003408142040007141d5030350308010350808034000b030064034010400c403140540d98074035250400245030850146e951a6074540300a20906a80010440e1407800c44000e03810441c8100f8141316056014400e92880b810182052403450341201241c8981a079000307484514000503101c54030501001d1900b2468040b03088071000c04c0109014400102c1c07441a003404074010074078100082001d49021100840300c0c1c1d92614824001c40c41c080c042c0d5005450548010480d400105c40d4441010420050207000e11200041000c0d00c1c03071140d0900c001c001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 162210359 1250 162209109 162209119
    0x20f040f1d07091a0f0303040e09070e0a020c070e10080303090601170307120810090f090201030b0d080301050904060908040b180f090703050a0f090516050a0b03130c05 74
    0x30308104503000940e6035101800701c00c0d024030303200440e6500840c8101c2d4511030004805081d030b074584d0030038460035060f01c0401e42d616202c1441300190050041d85442d10401c2c620f000b6041c05032400240d13408014020f0008032501d40140711500540d240080e01008072000010012410303240c25035107030001c0c41c40f40c000c85044d001c00010003211741000144a4120b802c412846040010b101d03540649038001c4000041c2002884414a00c066110f1818140c014450001000c100e40c0d603480183d0480d0310310003100421681700c441d44419903825200e0744500032001c0d1b444101c40c821565480c3c903513101c14055248282c410381c000c9070505c14181e004044090340180c0090b030322034458081e101250448541d559165101000468043c2040708468850150180c410050b90f140d82d41d0a0f40139110041c80711013060758a01c2080089251400384d0480306025001600f8044801143d2076440850340c1c000f940941e0303400c10304010000104080325800300300b1102100c0c003820b580c46c03e03881101003980103503400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 162211609 1250 162210359 162210371
    0x405070302212518021c0e0d0327060504020f0108070e010302160c060504030b0a0204050a06050702030a0c06180b030f160c0209070509040507020601181a1008071119020f040f 77
    0x1c1c1d6541c1d4000d0a01b00100d03580442080140c00d0aa815515034040301c48058000181003402c2602030b4116610044404c0d010009281c000c02100d0b8040107e12025220b054a5030107020541c00c001010112010080c41e0030061484c04400c090a8031081e58055410954002440355000b040e0090044105034043da0058089507590001402c0d90824003094412240301302c003103400d0080311b1080b102210005800403081c40d00d03200c802d40381500081000e0740c0502030001030100250349427901c0d0300500002e13100c050604108508001706204503401042c40000e00b00184a2a984022005548611040e080c203010213080c11080740c6500341520001d400c11400800d0000300d98001d40540881d56080e01c0401c5036903a11041240d590800f8400d106528003130748220121100507420105da40e10913a000c1007501440c510104140301d080c8030a201c0011011014800c03c90303030221280319144070b100020805220b00880c254402111001c00038801d005002c2601525215608625902c6007040c0c030030481 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 162212859 1250 162211609 162211649
    0x40b180a0503040b041703070209040b0c0d06030804150e0a0b090d0501060e04061103070903030810030803090a0c050d05030a0c1403030a09020112110f0702150304050703022125 78
    0xc2508a80540160800300d86e4001c412110004142c0d030740990001c20b07600081e255500d070342d00c5c0035102904260312464204901b4490000c20b0150000540c400d0580a9403079150400b1301c5082a010070714541086420001c42800382d45000d058401c0e901e800c050703a685d4201e801c00064004800d86070040c215400e241002601c2c002e00c0039114410307401080e050006c1c0000e204011000d01c0110340001c00b00d4000c41060000c00e2281c40381c6541720056000d068040f0341c5a03118007003103800840d0300c86696404031041c00708003c42c280d0240020308040d19019140080c03035488540302e001e208001070030440c0015a00e420b11645d03180701400000c068064039030f00e0810405080241c0b0311804181d0121708021104111600304e4030030220301070342d2120441d0070942418800b1103190701002c01a0380c40800841e10111070800c040085d4081c521800003440094914818050381d0300012a8070000c008401d1040700e0b68440c0403a064450b0140c07150b08014580c1d50070f807160b035070260b550440c40a182c100100b001c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 162214109 1250 162212859 162212879
    0xb1c0209092d16060f0f030609090615080723060403020907020a02150310030807050102070209180105010605040302010f0507020d0506130302010b0a1419030609080a1205040b180a050304 82
    0x8030b84401802641c14001040244000590b030502c01c1d00300050700492804203240c424200b2071101115403a000c60340c2c2c1d03941c001c01c1c0b050b40c0c5d420000369642640c49107020600001c2075103c0300240303a9200502801d80c6002a52088002d002d0500148507000e00341d0440e180e40c450048401866004010b4a100d04091800a554040000d0120301612001009560042c0070000b5684560b06080e0180b44840c21a0f4510200342c1040608440540d003d1091800503034440440c40d00c143c5001c41d404505c1d0094404550030b69006901c1401800303420001400981d03400700c000b100e50340103400c0603643e80b502c0d03201081030f8002c3c0100103840d5026170303401d00031249120400510514080c0e4001d1124004200400802424078031824501082c03400300c4c010340e420308054001a88041135020f015072543c03500c882f81614190710088072070300b1001410020007600405410503070800340303508001c207180c540e07110286040c0c041c0980c018400c10240c2005510001c00c940000141d1100a80c0c1c0c81c0c0e542c50152903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 162215359 1250 162214109 162214183
    0x312040c15170a090c050f010210020d0509100905030a0806031c03020a1d03060609071806020d08010e040309030602030a060302210105090a200f120d030b1c020909 72
    0x20b038684540c5804108080f442e4051030400c182c000041183d6503180c8410402c0385011461240c0c154040ea20540f1406a030b40c1c07000d00940010310320013140600d00914032500b00a91810b40700812460880c0704004194000162100c406041c1000701a80d1944400a450940001c14045450100c0040f041c0901e0307064014000c100d0b001c2c1c40e0f03107181c02409103a00c0010081046820b402d584030b54002100381c64500c2040350009800d00b8000d0384405d042446400078001c640008025902120104d60040c3c1d101080c14018640c9495881c11800e00c0c0e600201803041d54030007c1c0c511034002c00441c0030042e865019000941d801007184d252010500c118a20284111400c094154a0f02001440c910070110345034009030781c00040240b04c1c50b940124504401c21084216400513544003400c111900d801e030509020766100c9001704040c4c808a280202a240300415850158075202002c41500e0b41e039801007030b0200e50407560049070303946041901d0314211700701c40d0554004441da0405092900206280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 162216609 1250 162215359 162215387
    0x90604030905010f14030a1d210a020c0d0c120b0103020a090203060618010203090a0f0e0901020702150a021c02030c0106140303160204090f0f0501140f0f04030c06051501030e0f0312040c15 83
    0x400149509c518401341d00424882c240541c0142403081c0d100c0c60700e5083d400c01c81d486041400c462075110000c0c1a5101d100030f504903007e040140050040d441c1c401e00c8480140201c4005502c0d5281a00100700c0e54000c081460001c42204d0300c034050756a00034001c0e40c00028000e00b049601e03035598140d03409810901e00c01c010001d01c80d20b01143e1010b2040c0219040b1540140a20400502c0d5210180b002d078040110601107004442300fa642d20022040105940f02155000755151807031000b9841c2103664561196680800b003035800750f9183c5010096a4a0100070042e5629410443c000310740600640c2c08002e00b080300840107401085014600400320901070360080094400702001c0c0401e298082e502d0034000d07585200080d814041b4289001e40c001e01c02d00c2e01d40304490890f5110400d4510680b19082584840d001090380ae5030705100305461210303134100a00c2c0680c81101004e440f031140140c40600c400c0d02d00005018481d031540c01e54000e0030242c40000800400e4540101503401c68800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 162217859 1250 162216609 162216643
    0x3050d020a150203010b041e0902030f040203060a140105060a0504090213170601030c050609030109060507020606040c0806100e01110d020102030f0a1a0105090315090604030905010f14030a1d 84
    0xc2d580d4080a540f080e241600c0c51002c3c10351605040c0722000c01500fa480c400062403182654020130500c41e9030010358001c01200700030f10700340d0134203204250030514010b101906252030b00c009400c901302e604100c981100c1c0141d4913580d03a0455448102d9040c4941d8010200e054000280452010810b6480c00e08451250300d4941032490001c100340c0c2c48060030711018240c116580014405ea14054001785036083d4010700000c0e0701c82c604d40d11034007594801c0742e0344805a08903904000d03807402d0a000c0c10f0103466113803420000c145440400070741551407141e50201040512244d2545a0f4025021200c1100c9610304450384800c0001009010758400c841c0d20001c0310b03a00012446d089003034062101005101101c0d1204680c5140045580750403000c00d0a505200700f0080d6030704501030380007071801100c540e0007a103c0d603c0d040c00c029200d40307029880641000604103041c5503041e4000f00000b6150014284a0350381d88503038a010014007019140d0079035803698601c41103070303034900041e0481c050103030441c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 162219109 1250 162217859 162217883
    0x50c0a080f0d0e0604082406030a0f061d0712060b0402090d140c19080d080412030b06090402040e06010909110a0e040912261b1303050d020a 62
    0x56000e840d0314040e0040c03101c503400503025142c030b0340c01480c60108965020340180c2c103050b036510304540303420f206020080000045180101c1000c4900030700e581d0040040c0d0003011600c815503282c00c8400400074000c3c19007540c40b07158042c40404400c0c00140c0201c1c50301200e1206803a6000b030424202d103104126034052a04038003034444d00300360098403680b440c0200f0180044070681c8a60b00c02588503220050340f405408140c010707d0b510010311068203c8a1a0840710982c146072840e4900440f50703120b0340c240010748040100050005102d020100101d15000c00c16220b80400b00344280180f41400340e01034004074003c00c001001e020854442c0000340e80c1d03210314a9450403884200c681011702c40b100c1041c104515004240100e182c0750200c48090300000c0e903481c01e603c600c00c2c8180c4050412001030221b103460400010800c200003a1000400d089413105d007400460002641c402c01d800355840007012038507114030b400603c617602c000d5400c1420303200900c0880e80000e440308120082100c007190081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 162220359 1250 162219109 162219119
    0x7080606060409020304030e030f030903070b070b18030d020a0807031b0206150109030c1202130b030601120305070b101a0403080301060c020d05120703030b060909070305070509090103050c0a 84
    0x281490084402a00c064901410f103840b480103940003d00642c00d010300780c03040000c280c800b0271401440d041202d000d551200502020035050203001c0e880101c40c50f00074001c03000800e040039107054001d800d0311001d00c1900b1080d07a00380d003517000d03840740d5104a038404511609074a40158400e84502c60f50b42d41041001400c01c100010902088030150040e0310580004419803003001c0c090110542c14106010450356a64802e0598495600210024480c0d40b4400c0e046003440c50401d180d1803014001801500c1175100407a9541c0030501c1804075803d04c001d40b46081c113010f403048074a920707003024450600f490b0082180501c1c980c0d6102e54404241c0600e1607450020f4000c0179203041d81d80c080300c03451a69103050022503944407400020f9910450444200c0b0019104104070724010741d080720084d454401905003d4102c8480500460080324100004e0354907a94820b03010b680240e250800181031b865281c401c03513450286050198019480000200c18800006802c403d02031080b603840740c00380e440b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 162221609 1250 162220359 162220363
    0x50c03070e120a0b04080c011409030708030408071e0c080d05041412060405070609060314070f0318050604051b03071a0f04090c0914100804050109080712020708 71
    0x4840090004101552040301442e250903002da0b0850400c0483d5500c2c252034864054440c03040c1d904441c0300000040d8204280028000c142c0c0d111803008140e00603241400b061900c912231580c0060070460004009410885600141d0b0b54454000d8a00c01c0500c40d00d810840400051440540745400510300003c0c1403440001c00d10171206c43c543c0c40780d08052401001e15418001e18038583c0e030011006040501800742000824407803400788004022092411001030449507445d0028420141011903d5001216a18100e0b4202d90790740b03031501c402c00090340201c00a0080b2006060801105103001052001c00a0302a010380c1c0114143e0f40d8010719a480c102070740c00b44030300068154111010401245480c540340c14400c03500034011a01e000d130407000c42000c50303000340c2084005556400e00501565071029444000d01007040d148111001a00300203044506941c3d1001f082100c03000000701000400c0d0800d461291f40180155124411780c03420303840c0300ca00580140d00510804400282240780 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 162222859 1250 162221609 162221611
    0x11707090f1a031f05190203040305040311010f200106030c120203070b071a0405030f13080618030d1a04020c1509030a0903023003040504060e06060d02091207060909050c03 76
    0x1800e043e00c0c0d10704d00081d0082c0c003030180180a8200841d40e41c403401410720b0240000d621507072180d5031f07903640c40382180740c180755400b103842a4604101004404900345600812181000012012044802c81005400d0307405401c40d50801080401d8903a80010242c0c810f50698841354400c4095404094031140740403464080d00802a200b40e92002440407480341d003000460f040350050007600d250108000c58008554813128450f6808145403000300401803040c41095046031940c000c203000c4040810b143c44d960302408201d102801ea075007143c025420303004621042c034400040c10640d100e0741e9804e8610b8590b0705d0056451006100c080000e1250340c80401284c0640841b5121410f420b070454082c406a50b0001954030740a861001c0d0300f4014103d150f80a0b0039076102d0200540e519824082032200303540c860b80c440e1040950300402c0c0002035039010144c5a0102c0c07030000068840c01c40310009100d4010040965030310b40210500420542d078054118010b4403908a0184141c1d03c6101c155800c41c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 162224109 1250 162222859 162222883
    0x6210c130510240534020f0607050714010c02030604050309210d0c030e060c0604210206060904061512030f08070c030c06060506040602010e1501030308011707090f1a03 74
    0x10a022640f001ca8010340191820301503a86a217505000d030b0ba0400301010020203c0d980c0306804401c444821450040304001c1044015121507042560903900c00c0d030340703110500a058640c2e00c044400d610300c0c0d120700000c00c82e00d50001c00b01e4819080c1820900e44a90000e81c3c3d10340119a11804040c06484040b00e114070410b02500802400145940c104c90320707a00448100c0802a40580c040c42c1c644c1d03980041c1c803070710120300098003c0d400d040c6802240b14101080d51031a00d60000d50315103100d0340214019922180940304108191303a01d2800f40014170034030319a1442c03c0100140482c1b811107107004803003501c0c4652183e00d07883c51003140031f40c0c84200446801001a280000d2480080c3c498000070341002d01c03c00380400c5a60700e400c000b039601d80140d042040180c1d500c4a040316840400c20040045501010000d0415410341d04d006140083c14041c00b440a8100c254004e110359013000f61134024009002c003041203040f19964400613280e580100400d104180810524918010540400e124 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 162225359 1250 162224109 162224159
    0xe210a0503060105040f08010b01021006080a0305031503240c03040b13020316080a0b10060203040b030c0409141f180b01020708010606030b1806210c130510 69
    0x44108101140c030355000600c80350421005000c00034500c45484143c80140c00700c540080f0ba65103000000918103100c4180d960071240c103005041110a4020481200140c0c240c58440d1340ca075a80e444091000800300410707074144c8500001403046180d01020745030001c4800b03801c03090b1500c652114000a02058030080d04101c0000301154945002c43d003c4803249101030300361032a070114010300d1200c951560f0b00002c801d8101e0584c640c00c101c8020071841d8041640c5090710325450030803000a40e00d004501809844c0c0303200201260000d80928240c900a00d540340081c49400500d1403140007007441615038a12403840e040700b08403282c1c8400c04500503601d03d0302d481a00890703007581182c05880a503400c14158000c104002c1010602802528058240c544001c00d12228040c01e00c19120340550ba0303244008848018400075956295042c0d21001424021400341d00b40403c1160030469000b03484c6a009148850020007216107030090f44c0b0449080c0080c80c60240c1d80d8212034000c01007014010044 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 162226609 1250 162225359 162225367
    0x3080109050f07260708061003060e06060f04080d0504090c020c1503100f1e0608040512070206090d031d03070b0717040e01060309172a1c030e21 64
    0x54803502c00300b1030403950101c40440c02e0040204c00d900c00d51041c1c0d44170740081c9494080000d1030900c403040544034545842e0420425140c071444120300b12000c0d015520410b400181c01002d800c6840641d00602410b4050310a40d4140748405040707079005100b50925242400c1380040c1d1580041170f103e18201002c1c01030300050324030b0100c66415900040c840209034040b4030b40400c104510408120143c540280000d1402d0f801c911426101c9259034421420040c4d0141040b00086010464210a24109100940f1401c55200050a60003410800c503045030000507003205050307100341c0688140407079880c04010788403108203150f150380c680d0041c04600041000704100240080c030291540040e2440d849040c542c4550001403500401e84c010701c0025110b0a4a009200345034030801002406903001d18905500d030030840d61041403290401c0c0b0500c814050002510406000540108003a0b0402c02070541c0c0a2002034000d046840c15000184201c8a10f6482c414a00b0078500340d03410611031590038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 162227859 1250 162226609 162226621
    0x7050d0c053004030b0105150309030a0c03020c2215080309090c04080f060703110405010f1b05010501061701080a08030c0c0106080a0c03150606090603090201180801050403080109050f 81
    0x4105094440030010a41418070200500502d0081c0000e144182d195510320351511003003102c900000c1030304180302c1204000780302e40018004110b4007003c103242040441400303942001e9082c25412010b0715000001e64405d00f00440b00c94040300c2205c4c111410070080284100000940103071180168401e59004201031546d41c038001d800c560703008203c0403040d440d040d11650f82c94100703869441c0c00510b580c452028403020039014040c10720360130032100c0f85500b807600e010002851516007400d074030207101d401c0004661000c1032101d240406a00b10000703215959442400419812110910400310501000041803c01c00070818500040d04a0790040c19a114110410900d51098580e07511541d40e4000008085506004000d0f00c140036001c406122895070900500c1c0a00030020034103501e02c0c00c1d0702840300c21f41020121090f26043d19000500c860030303100685040c000c814000080c540d42a5001641030015081203101e240b0a40d0352a4881c0d03030310314884054650507980da4521040782000150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 162229109 1250 162227859 162227893
    0xe13020d110a0503010e0a0c0f05070510111803070e01141906020309010e09060a09050c130909030912080d020306060f03040c24091a09031207050d0c05 67
    0x4108102490006009049049103100341d502c0b09601602082000c4010424860700c0c0040703d90011500c0004e20800d4074005004009104084c0d800003485008100307041803200c1004400038061f0315000c100894401244950ba450f0064a1020b1140d0120302d004150f606021607400115050014500416400c2030301d090a000d0891803520b4205000da003442c44c04551191030070000b04100d402441c0e50b01ca400d80018044040c00004038040c0003908140640c94441c0d10321502201c1c0d00c0e040001321a2101800c07044144980081c000340091803d80207e0070149943c04001071074480d850b652031090340c400d80c0348440010213030302801c81e4805001c0c40c0407000d600d40080d070340b00c1320003041e480c64011112080506c981003500c00f41ca582890074000d0003607900f0340e001c0800c04424000c00412a90400400519005250098101d21000c0151080e0450070725002da40001c48005c050350202c020511800c101a004000152010f108a000200c00c003405043e0f213134011078110b4050812100050ba03015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 162230215 1106 162229109 162229117
    0x30106081b0703210c05040f08120a050c0c0409030e030601290c010b0a060c0302010506010503070c0308150405190b10020309010804031101020403030f020d0e1302 72
    0x7409418205071815983d1520700000390800020004800c02090848112218240401e03004070580050240c02a140924650405141d803150309a6881c140b150369002c400701c04000d801c014134802c5c002010900895001c440005880c040468111240844190005104c0b83c1e0400034500d401c1c0302c03003401096218044100c0200d185c00203a4080c00050300140003139030001d03030b810150a00390040d00281c035005141010484d5030340c50141c050740c10700f94110019464000020050760048068a00910040c0d8a25501c0003e07950152210360015111503021002c590117039a01c1e80d0780303000302032081340c10100300c01c00d21500001c0d1b038050352200072865100d030307881240101c14503500000380c5001c82070910700b40300652141d04050350110140030800e500c5d54000134022081c035070407201c41c0c148880703207074200e40d001340750b4003021038a03840005038441d40305095042c4c00d01c101006402030 = true := by decide +kernel

theorem cover : BRFrame.Cov 162050359 162230215 := by
  have h0 := BRFrame.cov_init 162050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 162050359 ≤ n) (h2 : n < 162230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
