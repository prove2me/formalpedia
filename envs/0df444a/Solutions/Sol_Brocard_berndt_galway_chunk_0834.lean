-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0834
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:03:37.844106+00:00
-- url     : https://prove2.me/submissions/846c0893-4a89-4424-8479-eb444105dcfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 149820143 ≤ n < 150000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 149821393 1250 149820143 149820157
    0x10150908071701051e0412090b030a0c030b0105121602030c030f04081204050f120102040803070b1501020105060904080703030605090412030b09060604211b082104091a06 75
    0x65803440e0b800710780c02c0100b8031032254402401c0d00c0004040621024003007011000a000a0403802d825142800300c0d03004907a40070062044909c0d0315628940140c6c0e040281410211000100e0700700741841c400e660042060728410f906105080e0f0b407030740ea040c2901c610143c62000344401d60100b081070003401d0300140010031a41800001c8a41d0341ca00c1e11312000d20740080c008031031910080c244014031480d69200541152a4011106e010705412201c08650081c401c6038031501d50791200107408030030064080d0349280720300308158444021345007440040e82658002c4601035803001803440000d0001d000310780900055802403a0000d80e103a01c5a010881c102400d4030183c60f243d450301c4141d2005641406481d4a0791025140408035080c0503001c00c0c0d0350300503401444d42203010020001070030a0340c0001416600d41010072040000e03805441510150740e01d00490b8000c0c024881d5880000c0301700a00c0140e8070401d41c14480c540b0746001c1d0310700c004084d40546484c2e4120007031007840700d0350b4a0700080d00304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 149822643 1250 149821393 149821409
    0x9060d09170423031209040c0207090e01150503070b04050603040c0302030d0e1f02030f0d0b0301021308060a02070b06010804051903031b02070b07171c0c0909051015090807 76
    0x20200e40b0404007002e0f0100c1c2e01441c443e074004110440c092000c07400b540c88890080d240818400e4007044140e081030300e180c219a045910307003030b10526007003c1500402c2c240305810240d24911500d990615483d6003450180801c40001044204420304105000355800fa010380421403c0b0343e169030000b82040d0041710444009184c003201c0e00010f1401e09040b0b10200c00c2c003021040000c0a106000e9180d0040300c003451502500480c01164140240e0011041001d004000310340ea09160200c503103c6410502443c10b42d44a00c2e000101c480105208840d109900000c00c110113135078001c011215444000c1c4103c51500442d13180464015070803280d0f1400501c01e40700420358010b0b104503615001e9a81e0185401c6501810b0200f2240d10a4421a4191608030000c000300d88000c080c0c0c00803e10030080e02910010a0100020507015681e01035200b14540d07640d010001d0ba502c4401c841500e1003500d0030720128070790440c20070001c1040300f80e14185407014107043c000550342d80c0304581401400c1c0d0000c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 149823893 1250 149822643 149822669
    0x105071a07110c03060c090d06060e0108120c0a0803100509070f02010b0d02130c021f14010e0c0d0f0605120102070c150215100512010b0102100209060d091704 70
    0x11070150030a46030110101c42ea4000c0c42030100f1a00000c0d500d02c4050040000341e2070020f0754080544500c400c0f907040ca41c00080c24003141d43e80d46074600341d4107c00d208240150049404180c0f030f0020100803903101500b00b030010310394040b584c0c030342c030109600150060151500c1486c001901d03403208010b00c0d200704410b031128140c91400c00c1c03002c0d080d245800003041c880c86602111100594601100c504184903038a030010310b201e400101640f6050505086142580306000c0071090035029800a40500700c0441c250215071344d0b03508640c1e401c04030541341d1a40b0780406200d6500030100760f0b4030403008032014a4001c503200e95100c2c0800c840c1d01080c80310400307603500098110203119007501e03c9401803000703001c4840c44406241d0000e4803154a1610030092311300240200b080002c1c4419014064200200000c500708200d1070014020308074101c0d99809802401d0b82d07401f2158041c400d44007d040d000d040c06140030355040c1e24100510403004100d84410030311800305c0c10540f181380600003501c07104604003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 149825143 1250 149823893 149823901
    0x130b0702040605030d02120304050304050a0b0415030605060a05091306121b060f05070f1a1501020a02030c040e190606080f03090a050d051504151a03060103030e0105071a 75
    0x100c1079070b4203900114000d51102c18002c01c01d41d8001034090303407a00c00300c41b125180d80b51498150300350302c5240d01080e802040d10300b0103d81c078506000180f049443e02c01400d04400720951095050742c906200b40c0b94000c0303051280509450003040101071090000b80106405c1c152038640c1c008582c0180c0000c0c0c0315842400003442000005403e402c440c406a4000c030742118075007070005080c80d2006142d182040004078590302001031010600440c80c2e8060f00d9001482e40382040c90b800700000703c45083d03451072010003101c12540041a82c02d000351b0048d0142c00301281500502002d0480d01c1c0981c45030380b03d0549280c40d80345010040e031958134494000030031400d241c0303c4141d140c10a00100012aa001000344200c1c55850000c800100c0e1f10544080109094030308120b42031a1a203800018241c1c03010f420002006641d40c070600c1c0040250b2400c00507182d0341c401e41e42614000b02c4a031901907204800501c0407a0241c4010701100300140b40003840c1c2a0b0715a80c0d540c0b21a9140c1d11014030300d000070140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 149826393 1250 149825143 149825149
    0x5010e06100203070215090a030611030f011e0306020f0d06170601050907050702042a0e040c0e0d060e011b020102030601030f02090904020d05010e07170f0a031d06130b0702 76
    0x21107034000e010b2008605020140d00000c4410803014090415a440024403000d41c2d03d03041c025000440d00310501f00100d00302c01054a2641e8412615060306260510000c02c82043d807901004052180804240300207086980b10802035102c4068100f0264084c0301081124038240200783c05880d42d0210340004441070414140b030400180c108a00c120f401c0000c1103030f407680c044180c650342a0126000b2501e1202080b00e1000201c2c6188112070540c807180d6403901c0c0c00c0c0c00c0360819100800c01e40e82017082c050500d00072180d100501c184980d0107030a4011000c04101c040d08010300608048000252266440f41e4117001c686880320b18002503500441040620340e0148103030550042e4001081d4a00341a19002814100b0700a00007841020314451000c2403100c254010426129030308202d40603641c03543c91520506580700307000105403250400705420200d0100c0c410325030a40c541c42e510017840d0840102100a0f4058100541144c8248201c2e40340000040d00007008066201e41290340e8107282c018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 149827643 1250 149826393 149826409
    0x2010204080f0c03240705071106031503070503210c0f03070b0f01150e06070614180f0c01020703030c0f050303040b011e0b0a140f0d020a02240c03070507050105010e06 74
    0x491941c005c0b481000d84100c2c024400583d0208042c40c141f41d46003020701d1300e0f10305484041d103c039030440004170400c203002448060015110340101c0c1247e1500d0350702d20030580d450f000b6010075002425101840d003400c01c003610150040e61101c03016184040c0701c54560034619040b42006645601d00b0106003c203c0d4403821940d8050030010f001a11801440321000d4460030700313200064002e0724000741060912000390301041c1180c0c40f00e210b0103c141007a40c6061091420b54031a01d8031030096400c0c0350701c102c1000404111800341030300600f40951558030180e0303100c030130707040103071040c207035960380540094010b2005611503441031003a18841c3d410405182c481c412303034104034800010b00c1441170140100c0c50050741d070000440c0c80d1a05803503440c5200451140100c0c5480078500c07001140c03000d94580b180d00039000c840006d5085030028480d00c0c00b52018074500002214a10b40f1001c08215400e030b1640007140e200c28607041030340c035100013540d800e42140d9003640158110384804d82407181c20b10b001c000b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 149828893 1250 149827643 149827663
    0x1a01060801060504350706020c0406030c05120703080a0207030605010b09030a060c030f09061b0503010f090911090906040c090c1d01110a05030d180f021002010204080f0c03 76
    0x1904201075810150064034a00c1a03000340c80383c0090f85181400c102c0c800c042e00007100040c1c00c0102004080c032180450740c5006070702899001d0f0003540c42c006840d0400380310b40021a44c10644c980521840c01c17042c0509046800d2416080b40600c56000c408648424002c000c0d081881d8010000300b499070910000329001a009240400340400002c1896034000549212441d00a02c0004130040810310680040407202034188d062400e15101030140b1403c0d0f031010741f400b081c03c19104124094044203c0f2144424001d154001c81001c2e02480324800a0b8840e030a0107210f40410804901058002564440201c980328110b900c29400c1004102e6604210001000107080900c15942001c001a2200c5071180c1a005d04003240c0c00c013080b0300c1c2c0c0310b145090000c2110300c040c3c0e00065454148140c507030b070000c0114501a824002c09284c000c1e200303844400e0082c2c00010840b40b000036503081041c0340c0b400000d0401199002d21002c2001c5c5414000d00d555110481d00600003010440141400c1a800302 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 149830143 1250 149828893 149828897
    0xf0b0406050a08060f0d05010e06070c0f0b061804050309010f0e06070201111203040b070e01020c0d020f0409050304090b09061008070507050703060f0f0e0a03090519050405041a0106 80
    0x44000c00105070020203407400708120703081c802504e641e00340100c3d03103280d4250045a032080e07540100106202040d4000003600d5000c80660707000daa40c01c1400d940d244043c020052001c2601152040803850b43d035401c5d9040a0b008148820090308070604a15441d0140c4080e2559000040d85016640c0c001503000c0303642c07002d42020901c4000600014400d03000f20340c0701a05210410080e400c04030003e00002490f02c540040e2543c40707040904100106c403000312415000f02c2c81071840b00b50158000a255800130400500c04410401c41d5424000101c0410074500c1e0010f0b156145500065001e04c0580081c0000210010300344201008000d85000040e048900420603044091486039100c814941c1c0300d03101d418415903940e050314100d8602a071550001e0805498544410000e2025401810050454100c03d110200d4440d14094aa80c4071580040225400e50800c01040c1070101c55a00d8502008420100080c0e0791004501a03402c11141191450400004018202e19407001a40504164 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 149831393 1250 149830143 149830147
    0xc081210060807090b04150203070b090a0c1d0a1a0a0e070e0402030c04030201031d0303010e060a0e070f121d01090309080307150209060904090f030306080d0e040e01020415090f0b 79
    0x405d0381c8545e40300b1805000307000c0042805150540d4020412510540d07403143c103044240c94110729190b1103040ca502e04490701c00c0070040001d504002e0301400000310103503c500130702d01d458401d840c100901060800b0201010045420303816540da4100d84001040106042d0205c0c1c50945c0000304500c541024051041c2c0c8144144010005050300b0f540c2a82e41c2828001510103482c2c284807058400ca000e0b0f10402c3c4000000491b1100c80c1000c03c0380103c209403504c800d4180c4480203081c11240445290700026019000f048060303106480400c60410b0091b0006a070780c480c080541214204030040c0520361391203e582d0300070141d200d04414000d154810186040505960301d44040c44070b16104c84450540105400c5415560b9208460f00c0481c01001040718005a1400c034400820500e01070780401e16041c0001040741c80410550b06080c2290b454000a684800810000780300d405445040c1e59400e00c070100362000e00160501c0c142c003591b00d4004c1610716041380c03404041d00f50b401a140f14901 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 149832643 1250 149831393 149831399
    0xd0f020102042103020a0b0915060105090112091509050f100605010f0c0c0b030702060702060a1b0804082203061506080118110d0e07080c0109060c08121006080709 72
    0x1840b0340c2120018a09140c0c0c2c00342c0d40c0e04d003000c81c6020029800a019400d0483c2404600e1000240c0080c1d1810116100801951441d0043d1a28081c80440c07601050b03038441b0142d100641c5500042d031142c0305030152054107600d05c40c82d500310fa00c034000c122440d50000f0140c90310340c03400708500c1c3e924500c200c0c0b040c050a400c0400080040030801c600d070b0207001c4410078442c200050040a0340107005100743c103644a24016200079a40e100507141400980142800300d285028140600400035500f5254003c28900301c1d00c1c01c0342d40b0319008000340c400d03d605100c110090454401032461031040f061200d104141507042050445104241c2d41c030215848040802001d60030006203411903810a010381e07180d4a10f4083c00e005496095031454507440d0000d5008030074420f41d80119075604001c02118a080d0710385240c50340e0f030340b124105d00380400c0080c10b003082001d01c11641600c0040c0300310721941c14040410920000d84400760341d20b01000070782d044140b0020f44c1c014445640b242c0c0e64903020711001d01e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 149833893 1250 149832643 149832659
    0x60c04030b0c0d090b04260f0a0c0c030f0209090a051504050a14010c0e040618020306060706050907061116031101180e010f1203050909070c0b090d0f02010204 70
    0x20503031000601500c030380000540d1116415050f2819858007101c107101020b2580b801d85200b0400701c500b10ba528043c140000d0000c980400040500f807000080c00d03181c00031400c40c241c40c3c1d4100c41034102c00c2101c003903c0c00000440301080200118031070000950350100c03902c108601d507000140005aa80c0c0000001c401003103001070208524280c00c14518215180c45c24602e09080b4809070240c80d082e800510710120405c158032004a8107401d685440c0c1101c510810031050310000c0c0f1550150361410300c2d207183c0c28440d56000f15080200200003034903103241580c1700010f99108440d030700c0b95a00101d00400810781c0041002880204000103440e514040d41d180d40d8544c6001d000190a150400b0030249682c0d00940d640c0704c00c000000c0300403900c103540304481c0390074803002d0007490412040400f0004071002e42c15030b140100303a0315440303103810300003034906002030a90700801040821041d03082040c042076609100901078a6894081c0658401760b0501411440768504c0b0f00b02103a1042104025100b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 149835143 1250 149833893 149833897
    0x708090a030804032102070309050103050106020c030a080d18060b040c030204080d180b0d060302041d030a300203040203061f0905100e0c04030b06063c030a020903060603060c 77
    0x42e52509054150b640c501c511885c881e00301e0009840c450348000740200078141c1101d46c00e0704483c02640c003404a40e8864130120389445040c0100d41c2c05910512041000600c09000703000f0309905540002000c1d1020300c000032514800c02001d841b0541d0744c6180c4801d03400e0902070003050381500d007015864545010165580c40c1012a1440100014103e0070944404079250b040e00804e480c0e104a038a60002121140041c480c51108030310031132804404440c1460071310250a408500c45014504040941c5010385003415084400341d0003038242c0d8084080345501c00102d4a460094001c010388900d000c3c8149071a244002d807030100d00d940013000e001f03140b4201140840940e010403030003092586961014648203010ba030440c804811101d020400c80803150005842202d00a607054012601c03210b040c058188140b180000b011160102e003820640702c03582e40c0c0b4903c0d510054072810074590b201803445498000f5241c18190310340009140900e49410000541c0007082200940342c1e13420003030142040d074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 149836393 1250 149835143 149835151
    0xc031302060703020a021009050a0e09120a030f3201080c06091903030521060102060604110d1401080f07080d080714040e011508060109140307050604080102030708090a0308 76
    0xd040000342e50720400d442809165101c581c00b40160035542041038019008a48a00440d4001c1445800010707880b5000d400160068a1342070107081c0e0018410b9406d925035110440c44014940c0365000c0c81c80700308080c4a00d0f09402c40c0c01180b0100002c03084003680c40503580802040b13180400701e0040c06074a4010800a102080c102c0e65030355645001804203210030004820031031202102070000081c03640181c0113002e14440c03d0304402c074096042c0080c07602c0c0c50f01602e0560060340484001005030801d6030194261201807890203050101040381e40007654089110340010243c65001001a84010051986155100310190401c0b50501c0c445079038540034074031907070100320b203003c0410aaa80608040a001c401d02c25010f45e855403a00070400070f541c000e00c13035070328240400d9004110492103200840c1c02000140d45032001a440e0039071003a060808035a040f1741c54016107000007003d80c2e43c0e200620007804032100140c3c032880c100601408100e0010324980c01c90b048000fa900010358424001d03584 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 149837643 1250 149836393 149836399
    0x6010308040501030615120c031e0917160809130f1a0a030b06150910020a0b0f04050d08100504020703180b04270621120f02030706110904020f03010e0c031302 70
    0x6460b8401c0040300504112010090030108000c01544070400e150810f0030be050203090b5114110482158202e100d204141c0b064481071340a84400300010000320050000210040c2210008071021254100302c0759000a0079200c240c4d1603d0141c09075500511580640e2412946220300038170f15220201408030050089204050b52070369040300302c0903042a2540c140000e020700088803a80040a541c50114440580310440d0b07202c00542250031070100c2e03500c5550f20801924004030002000c1e14034040141c494034801c8048040840d090301c0d60701c0a40040348c025070343c82183c40038203c2820800100c40e008159510803c000a0000b602c0c6806501610071181307503445502e101036141d0100800f0310f43c112482e041844c081d500d8104030f51038980d00020340100c80310800b29694075401d5441c80d903a02e40810142e0414030012000c955164803000044032203070141481c0c4a1050001001c992100c0110001c1110200040c4105441414165884907440303482910314204070103403400114160131b000b48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 149838893 1250 149837643 149837651
    0x7060c020a0b04060203030106080c070c0e0403020109051213081209060a02010209220b0f01080a1808030a050f070e0a05120a02040501090231050405180601030804050103061512 78
    0x45490300e207400030007011103402203515180c40da80001d4490380300f88154400543d100c0c000c141d0702800740b421a10415845500d0500e410b15050a611220030001c00c29401e5560358603510380800d206201e405d0980c0c1d904041c40703545443c0d80c2501e81d55000a43c000402c00d90000c0c1138085034000179070440e501400d0440e48940c9442802400f02e0191040205594004004004149071624090780152100094400600048000405200c140f40d41c1c40140740c002400840030400b0030f606a400b40700b13448580f0112808003000c60315005100d5205441d120903441d501c42c00c00003d080000351300b070303004101e0345030600f400b001c407400244601c2800d01480d0701c604000203030b03003c1c288810442271903035950140080c4459a0343e0301607440250030130100c1c1081c3c590200d040c00c01403107509000070061040c0140000303641d41480117002c002d00c40103000701d4800440a1841140386400c02c0414000c500c18003200d0355075414000010190703080c650100401c51946141a560580c11041c2c8018002003454001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 149840143 1250 149838893 149838917
    0x306150305100e130525090903080105090901022704060806010f050603180d020f100606080a05100e04080301051e01120e28060605091b07030302090619120e0706 71
    0x25004010703140700108944902a03002406d40713400488031181e0345010f4000f01140d665208400140c91415400034002240400140064a00214601d4010540c10001410121951085592141e0b80d07082145240c00401c004881c5207440c0c0a03040c06090454040c0c1103e51601c1d0f0844800c040b103024251140c0008400142100e40251100c1e602c080c07000d04851a60340001006500d03001c08102e84802400707802d1900c24084c4650103864115400ca584070016661040d05140007082c0c060404141c090095030002010781d80b00541c54002c9000304491503907540340038108460804c081400400e4980d040d15101030503a040b483c0000d20140420340401c00c501141c4400b030a180c500185440c81e5041e1400300c0303448070f00b605803d04a00c1d00c1000e04100e01c0380c03581c040281102c400c0300c0c07003420204640e031680381c0d80542001401c082ca100e4200541441c0e0f5a40008a080d00700046469200d0400c10340ba210b41584495a8549110440020040f001711140800e8071340d01d140c040c2c5014008104114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 149841393 1250 149840143 149840161
    0x2090604181512030915020a060b1f0503010f150516050a12020a0b010503060103050705100c0605041415060105030a0905030403060603051e030c030403020f01030e07060306150305100e 81
    0xd03220311020040880c0c40c07962243c104900d4000c0c00710080c4c00040c182000411405015000070314202040e400501c1600070325038a5601901800b40c990b0781094201c0300d45c600c6030b11690715040c03040e0940e0710ba03a40c4a40c10040ca60b046080d0543c020000d442c0d40c1000610102c2d003010484c1c4860341d030101220403080da41c1c1811071a2401c0385500070600550100345490f540c1d03000c070341d018040340701700380c00c00050f41e0304c004055403202d0a000140503500803010030001864450715040e240c1c405824001808502501c0341c40490f20100c9081d129020410403015100d101403150203c0b2440398603410526080140008201d4000188802c49503a540d03410401440710810540d002180d209000384403568403803a0040d100c0b03041e02040c11842940c4940c031403450301d0110544103000d102e00029801c161440d0200700d03183c038009011a05142d501c444117041c01100f0300c10138000d0900d0352000715103985130405000c43e95001464117010103140a060100000c2c2d10050102221501c14900020352544440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 149842643 1250 149841393 149841401
    0xb0a1806020f1b0607020d0515090303100603060503190302101b0e09150405190203240901180b0d082101270906110d05040b06060705100e01020f0723010209060418 72
    0x204527102e80c40020421642c41c000001c500c5481c10f1100004580d50f1041c041d000e96210f4021690300d42c000a9010f42c0e2005094850840d4600a1044800c0c1000d228850000c40d0b003900300c030042c00c410319185100d21030742005032207030a15001e980101c50b914204038080401a1400c030440e104640326004070300c40c00041c1800103150014240c04555900742200d081c004900000c5010408041012101e24245464250a4102c61035005c00401e101d05000f100c1008100a216030b0741d10002da40b204001080c0560050040d000c01c541760744182c9180e0b40740425010700145d000c0040306c0c0c18140c000e40d00c910580082c0c403e03c1c0705900e0201d600d2885141c00000350911411600350108040780f0705007181459040790740924003d07103e20394692190020300a117486101e4002c0c20b00c0c0c0c421030114500c114203502605d03504410100050030010624011810f503032003900199580402c0c40715041100750903040f013281d8068900001c52820b0070a002051245c081d030302c940c00200c1660f1613050003481300c5400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 149843893 1250 149842643 149842663
    0x200a1104020409110c0c15030a0902030106120602030901050a0204120b0604020706091209060206060d031803020307060e011407020102062701090305030702010c080403090b0a1806020f1b0607020d05 87
    0x3814001e1818521004c6001e80000e020301c803c52180009100d8103041541203400c00c00140c10b4140e00d10b555100d040d20190030f1202c1c003240c02d507503075002c00203000000c808510350482c8542c0e005a0399040449841d8207482c3e0140000610600c104002c000c1111440a203004499200d0400803070383c0c1e6401c0005009004281026000509100c001c004100035006c211411052503114400c1c8540ca4000c12a0b4582c012605550410400d85c03c1c94040382c018090501006d143d080588409074495002c40c2c108140c2c0c2d0701c0354002c101b400202203920360f0407400f00d842503141c2d0a20107081000d80d40000359110806402016100c6444018208420261b086035079401c407814000d00c8403039901c0c0f50003012a80100c8940700154601107200c00c803035102d41e29840c007544c3c040e074841840500b006031681c6d01d0781c882030003502808080c21072042c06011243c0c800c001002d45401034100d101505a02070b007056455003c0346542c16a501e0010415a0b441d03045d20b00d019016a401202c151442c80c0c0360b880d0500f5aa = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 149845143 1250 149843893 149843909
    0x90a0e030910090503060a020301030809060c100f050a0b09130803180a0c03020103180c060305060f03010f150501050a0212070206040314060402040f06050604051c0215030106200a11040204 83
    0x20000c4542a41c00805000413184140d003255070603941c2924040c100c0c0402e010040507070408000c0d040052400ba009001410080010358400c40c40d0f4540c200122054200c643c50b520b619072040101206030b5100c2c0c842441c00079144000325107481d10380900b8000940c88020901300020000c0b41c44140c01c1e80d40384030407005072000c841d403c084500f00702080800700d00c400c83c0040d041c900c4e0082504808646000303143e80c0040c07416441400c10006502424005001036041a4414105102940c00f401a41c11030450650700003140440e10000c1d0005c4040f6800c414144001000651001503002600e034500500c50540070b52a14132520014195118992028050802c00c078110003800344042042405144215030812000d940e80d8045400c0c1c5499102c0c4503440b81342880100b06908140000e94a5000c11428007203504031141d00180800900346400c80c02c018001c0010b0100a4000803004042905142d28523800c070302d01c25030340e0b544545000000b0305a600c8081808080d40750358041d14040c0071f0003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 149846393 1250 149845143 149845159
    0x90d0c0503060108100f110702090901180c030209060301020306030d180306060801020d060f060509090c0f0a17360f0f0f1002030f010b070c0302100804150b090a0e0309 74
    0x6415450b43c0c0e21680751170007070070a20300b41500f202044d480c454031140144080000341030203200e400300840d113180206020a1552109410118607440302c044c154890f1107540d050030014154018440c9942000301414001c1e0b10401c2444915540007800c416825034503e400c400074480000d850482002c00da0005003010b09001010a0319041900074002e900d0f1655410800c0c0d0b0382e104000032040d0300620454010480400c1550b0700da003002c0840a130301c00360120000303107407103800c4180c44541d5100d2a0100c00080745005040104e4025203403807a017000c00342d100d80f04800e14003032940380751085608146001803016051035803059000e004143d807074102c0c170041c0c0e504050340800383c0e502e519150520b5003030b9020b009841440001ea03031007a02c2c0651020800c0500907800c2090740b52040e80944000d80780402c881c100000140d403040703d000343c061450b0340d51032158100f0349400303a030780d40c0030070340e124082404c0c50381080440d11444810b552140d03070114003003000200468014110721030080c0b4580c0140d80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 149847643 1250 149846393 149846399
    0x402070b01060219031d04020408031303020102060f0103020307060806030c091f0b1801050705030c031309060b180609270402090702031305040b010e0d0b01050f03010c05090d0c05030601 82
    0x4015024101e5803aa0282c40090713450f40a072000e1603a28100080c081103c40215000c041541422089201000760006280c152030760740030f501c0e5402c1008500303083e40c2001814411075906100c0c85070402401d07a0745401d907505580c0000d40b19400c5009501c20414150b000a510f135504011710844203c01074900201030a010728031b00c07044441495640dc40d4407030300c1b00000300300c0188021200046108007000410504c000300450745a84040400d9501d032000344481cac01604414401850501481400a0360279031800b4184010b9070810350240700e040c50140804405081451140441071504980c41942c4000040001707020580c80d43c0100a2504000c003c02c60100340001d005004900844505031550b4070b505c030880e0380c3d20a10100103140402c1d148104450300b40f0350807800c8040360504006150100110128003040400e0070f0548480241074010412400c0c251840301034030009400130700c00700e101c034080130b0490300c54648014003410b40b24000f541801951100781c0090440201a0b03511965 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 149848893 1250 149847643 149847653
    0x91804050a050d020d020703020f12070e090105060604180c03061e0806130c030816061806060b040b041403010f02120a0b0103090b0402190f0f0321080f1005040207 72
    0x1054121043e02c902d00c1c01200541c000100d5881c07010b42540105821404e650074410034240d86049541c0100c460103203418038510a00101000e03000c400b01e04c180d40d150600040c0d0a55001502140c0100c8003000140011403403124070420f980c01d02c20002c02c0b10300c1016401c400030081507000032503900780000c2084c1c4405201e010001140c0342d800440300b280d1246500300c2a102101c3e076006200d1080f0701802c00004151a0290580c888107004848030031900351508804e071000040642c0d10a5010580c8008014580c4504409071520b1203400b410a81480c4074140e02d03205034002d860194407801c001ca0700c6941c3c250000d600e001c50810066460b40da0a0b8581402100240c3d004d1408604115082895501c648101010b131500400043c42503103487d024000d5400d840980d90000d022002c0010580850080449d0000d0100340c8510b50355925601305a84072031480701c2024440d0201e003081d20f4100c0da0010300c0030f4000d40c140c001d0300314648030340074105a03401c542d80c80a0f0704140081950000c3c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 149850143 1250 149848893 149848903
    0x80d0306030c0f080304050d0501020706180210030c0206060d020312040e040308090a12030c0c050607050d0e01050f0601031d060f01031a2814010906090b030601061409180405 77
    0xb442280c0303540c4140d888030070b40c400c3d8020342e00810741d01e58801d110410052400136059014a03006100061810078039891740d100343d44a00ba940b80a50400d480600c04605103041080b040e2182e83c42c0c04c000b503442d103d900035111b46000e012584503c00120844003556002d10101c440362442c4012030b40e403107546a80710560303050100ca06401140c649000a4950311001c20712500300766010307610144420050005400412403a4900c804000d0b00303001c18000039004000c0f203402522141c44058036041030001040c1541c00e4000e00074003e03414501407003031001c83d85040f6030700903800342400300304002464072a02d0780c1c00c00007a04c4005841100e06003c01c541d9044c000d20b05a81c012884404680100381040d50000d40c1962010340c1b4010112207000c100c14908440f6092800030003000c12043d162590b01c40000d84280c1218030069550752082002c10424410300050203025000b90505615014003e8840c0358948203081d8001d400141a07130855440b820029614401415550083e04160400c0d035a96 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 149851393 1250 149850143 149850149
    0x20907020f011b030c0207062c13050105090907030b161e0e0f0f0603070309080f04090212010e01030c0e041a0c13060509220609140703050c0901120b0a080d0306 71
    0x100707140c917425011440c03021910000740e40d481d03140c55080310180901403004014444c0d0106071901615000d000c1a07607442114607940c1c1c000840819a541804100000b2060182c0b441c105075000f048100001009000a55809040c015000b0408a001081078030520080701c020078100384154200045c05400c035080f030040100655600b2410039031001405031041e098403032268031003014030006003450b200760481c0035028426044542000b10b0741002c1007494002c1d8000104413500800c0308010344100c09445d90050449941d0503d441d491900c1e0b060240910740200d00c20740841000040038818103443c2c66040d1100070086004920f070002c800f2020707402001d020044e860011600180d064810016078000d40d00003401d038000d132503000c802c064000301481f56012600b900d4140000d40c0c10000e1140c4c0100e180648038046052814032401400c980d4010f00000b9580000e010442682c1d9000d03002c5c00c68480c1d450380c00180034030313101c0005404540d642c3c4150380f1846000c4000301d04642c5030f0010421 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 149852643 1250 149851393 149851397
    0x20f0c03010501061215030c080109031103070c03080a0c020a1202040f060b09131b0905090f0103050d080402040e1f0b06091302250b01050a090c020a020907020f011b 73
    0x4108006020503003a22030a200f50340010302d0f010407030500050305a02504201440c1c0f0f52400000340d499580d101c0b102c00a174807040890355141c025405050308402d040c294070b05544003442c03400015075680c50034154213000c05400149d0104015150718058203136070b80c0c2140c00504025846654110308012001900c0f8220300442c1805400000c10129014890039130fa100c617240d0342044400c1040c0b05640144124143e00c240c4c84040c1000300c00315a41000c40303025001e0b40c400e020181010b0074844284001382c12041200303401c400400200310045100c041c29441403a00400545070303400020040e01c40c00c0c0c03162815000b0041001130444800e030b01143c824001e00e03018880641d003001017021900a00c505035401c030303895400070301300b9842c02c0c0d000f00300c0709000380c4907003d0041e3703c803070400303411540c0a000712680c3e036000c8018082407800c5031502008240e030000601c00c003a24120001e444007000780d00240114449000700e0b010740e000f484504100024600204003c3e09002c64003100b8000368600540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 149853893 1250 149852643 149852653
    0x503040c08120a1b02030604020f0415080102130503240c070506130c0602010b0303120403021203010b09041802061e09101d03030304030801060f020a060903030203060f0108161d040903020f 83
    0x4250100034041300f0064005018044980d80c07074090226160310025190f81c81a0b9456503540c000031340c1c0c1120400391603070400068450280c03d034080d4002c00a0b030449031083c0d010400422032000550614141d10a904410303e0245e100c221420003e4003031307248014064007466007081101d0109540d1184070a018038400c42c0d565503035010580c2280e404046207034140c0c204200301c1085c000c580c0201078006100c0d10403150030503c5c00b4030710180d030781082e0000801c543d400129242c0d107241c40e0141c00d40c07042d00141520380d004455800146c80d0b204034000501041c1028107824540d141d25415583d0922000c3d00100400340842c000515030482038040c001c4d04504c0c4460321545050001c1076034400e65241c1c41d1240075908004082c4c900500b00c890740c078114801d0b91891301c001076641c05044219480307074a0142e120305001007005505215802d8080c1001780d114204407000c0314025030581000c0c0203040c00034250040d01c0898181c50f100e0f0021580190030040d141c002c06500054182045d81302105443c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 149855143 1250 149853893 149853917
    0x70f0228061b020a03080a03050c0a0203040b091c0305120702190f06090c0b04050405010902070506180f0a08030906060d0203070603020c01140f040b0f190b0d0b01080f120405100503040c08120a 85
    0x554ad074083c0440040050b8400c0c00306001000c0304400816846000408155079200400141c4107042c044140c00c0b000110301103050840350718003c0000e42c020120340090244800c401c18444504086050060003040c0414070704018450607070b020101854201c030490025603214130f8002c6e01c0c0e50080c40f48600407407820000003400c6001744241c94407107511902908194442d17800c3c060403047c010f9111003441c000e6000f0100c105108000070300f6094030484c807481d168603010070018206040140301c0390107050880c03c84001a500030812100703507900c1c0e081c01a210211442d415005041d150100c14000e1410b0040c4203c0700000e100c018890b0b840ba602140c4c050352200421600d4580544145420240a1072280c0460300356401c503a6500d4005480c504036a00725454600c4040801c0c0d1145600d50410310a0b1245070074107015441b1994515443d551520389030002042c96014030004000810002001040800c0110001c001c010b01600080342c0c8840d60f004d15241c03080c0e00541c40c0c031000c0346050b4411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 149856393 1250 149855143 149855161
    0x20f0d05130504020705072301120507120e010612060e0105010b1309020306011106130b090f031206010302090607050706020c0904120807030b0303070f0228061b020a03080a0305 78
    0x4402045a0041ca401400c2c03400083c0806500208412a1603018481000c00c603810300d80000d0b034030307202600300d800a000022400540f961180d03240d207a54460400c420045c42c1a040f5140300c400e10865440080c41c8040c03400c10900428254010a042d0314858016109200c4990015001400b902c00200321a0341e84456002ca54895901000c0360751030008803c00800380e017580074691080043c140000030041c16004223003054411266902684040300300b1205118910781081d50004540d001031003c0700d43d1400e02a960701a90001d01380c900142c0c00096074a03442501030301c003c140040c00b095110051031074555101c1d90903001d41c00042c17040f9902120302c0d00e03044900c1409682c102c2414001e8221441c011240a02c0c001e2444042c1a04d034038600103181ca0400c02860280e001d0104c02010444610400004100704d045206a01c0c0c0c00c0340c2c59a45014441d00258200e407101d0526145000c800441f03096500442e01001e5405001c28000009000c403c000400c8030300c100303503070401040d902c3c102d00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 149857643 1250 149856393 149856397
    0x706120609020c0604032a031808120f03060a05060a021e01050403050a0807020703080309030d05180d0c03022505040506010c0809060901030e0f0f0f0c1008071707020f0d05 76
    0x1240b00310354001e501080101c5d000d46a007401240c001c0c7d80901100c04088001d080c40c828840c0704030006695151101c3c43c4906000440300507081c43d0002c0e00c4001e000c51107040203030084500e030300194078001011503801c0e5140d1810030002c1070044c0c115611030309402c5000c1c1d254803069102c4610889411148042c428042c419a4411503145d1240c5040c203580500481d0f00c854001c0070401980b1907039102001003400c19010714072440c0108003c0d541c0b880080c8141040c0c82018000b1414400010810707501c10b1008a60188080100d04c0c1541e501041818101c2c68010108185440b0540d100108407983c1d081d0241c810a03070340141c80034405500c0340c100440384450b03020005820120306101c940c28a281403802000b00702014900450044080400c8a05201003843c1d4803045a125500006042105211203c0040c20410103800c46084000119102e00300c10071078101000081c400040c2298050007405460090b2803003240990304c1c0500c40655942050910400d0030300c100d010313922105100e442 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 149858893 1250 149857643 149857657
    0x10b0d030e090f0c03270703051608120706020f041e0501030515010917011d0309190b0a0f03020c06070306061b08040e040f02060706020d050c0732070612060902 71
    0x132414030319551040204084014681d540402c00700320341701c4031144002006580051406100035100c8410201403029224034241d1242c801604a641d020940b126950f087c0e0b500c442c2c01110140e62100355800c00800c038803d941001c07005640001141c5056002c441603201921030a0320100300640340e115100e42c1e80c1c0504501c160000b2121503041c0710307006411288901241c6194000b0a86400002d644920f0207081d145841d079070b43c00420a181078bc030340402d6003039142d0090503041046c0d50910616210b607110b183c82e00380c11f0040c01070407848164425030484003807480d01d0301070350554240b00c0c2000300503010a111746400940242c142000003049142070b548207544c4085203611349490510b501c502180010310941c2c40d8002442046c0141c0c0314803008002051080c0c0b80181d4410300b105440341107880140c000004d447c02406007400140004414000c070f607050405d101011214120200440700c0c202c4100c03186401b58580000e180b42d00030b03001d12032003000711a040c058107403103242010490258403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 149860143 1250 149858893 149858911
    0x70512030702040b033901030e19020105040306060b0717031909080c0a0516060c0b0a150801020d06030201020c04050402330a050a030e0705010909020c010b0d030e090f 74
    0x40141c005140c00d92040b0802c0601400b52203188900016000c6030211110008215542048080700154070140e61080c1c1c0c450242000c1100c91010319416903035107003640c0a03c01e0307205c8046e202015a805141a2801540e0041c17042c0301c2c1548417070700d1104907080780704100c4114002980d0302a4241c1c0200940b403103003040300400a030203115020b841d80900031511058903810b004001300200ca42c1c0c288042282140070300d0017060303a1004088071505c144415800882040141980c02e0002842d030000d640e00140654000301d0715000800006408144981c0807106561000030780c8150391035160000000c4034000d801b600c00e0703515003c00384002d4400451f4001e40c0f10080340c8100c1e4491a4410760b104901c20084000c08204851580e142842c0d4844000c031004074601240d1209502da050240c04008401c0e003010f020481d10781070028055101c40d00401031400d8001c0341d5010501825031025130791802c000c10f002c41d104900c0c140a013010003a8185280038034003000004180d100200c5141d40194282 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 149861393 1250 149860143 149860147
    0x1d13060302090f0f0a151703210702033424020c210c010c020604170c0c090c070803010311041514060706020403051c031506020601031502070503040f030507051203 72
    0x80b048040080c0681d54446512405203007020684603035000004d003000c4441c00003540da272101c2002070300001d5a4420203250440012003004940ea03400f0043d00c162a0384c6030509801c6d0502081c020034251851107030005400b00001c03c20f01802080403a076080f000500c007004907a10400f01c2100141d106443c0d05408651009543d075800300811010b09640c60429140e43d400c000e03c0d41c10302070039503229140030401030380484240414424026094440074520010040c9010300d00e024194507600900e00039803203000141b0018040044250455411607841503009039a0368503460403004900e911052140514a042000044060940d11107000d442e8034108440138a403d14003042090ba10004040303607101d80900c00000001d1081090000a13402c1c0c01d0580007440700d44000030100c4000c0a048280702d25020703020130005030046003040c19a41c010325046800441ca04070311029104142c0020024800041c0001d401d0030100000c4003030300e105d101a100c0e0f0302c1d0394030f00304172202c0c021480b03000080d041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 149862643 1250 149861393 149861401
    0x1020714030307020604030605340f11010606050c0d090f09090201120504080c0c0a060c020111071a0408010c0e061206040f020c0a0c0503061003031d13060302090f0f 73
    0x121158403040c9600604492070685281e01188040c2c1065000311019501c600c10300c00702c005070340111140082c80c0b032000c4480a440410003030241f5203424075182800012400c1942c40752103242c1003440c600452000b405013595644000300350303030301644a01806010302e280c01d04886106451220440304c481c2d40c484241c82c1007400382c078024100d40b20124148018031941c0d024480307190040912450040c80404e440b14485040c1900303040d10000e01c280b00c2d10719920309203d00c175001100707244a160286013655060200658140c0703010703000c0d00b101c50301d01c4050600a41250040e0700401c159070041009001c010001c440036618404003c05050b03102005012014003512050407036680700c100200045080f541c0d41034440e00303d03406145c0780d0070726800010203e420701c01d00342ca0400050405400a107500e140800c8911074010603800010304000700d4165400192003102a50414504000c1c800d85c401241d510854005049610080340140b10700c00c0024441c43c4864000f91040e01c1c0b03030700c02402035a2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 149863893 1250 149862643 149862659
    0x703140702101803061e0506121b0324090d0302030108060c090303070b0a1a030c030303010e0403021c020a0c0b1206150d020714070b07050a0303090317070f1d010207 73
    0x40014400c4030f0014140003003c2407040c003452280801e0481c0340c040c000c030800301d000181c2d40000c041c3c40c02500d01c0f0300c0c85800880c0008650a0b808402081c892504c59101c3c0024103148085802c0400340c4011050510340b00040751015014410000455401302c1040b40d044e0160300092040506030380155001400a0010000414003510018152032a00149039034a40b0002410748600080e1640c03030801c00c64000b2500c1440e50080003c4004003586400e0b45c000940d2031205014010140304500e012a0030540200001d41004203503c0ea482c80c02010250300968418070a0300650b00400c000c0800204034011070103d801304503c2610b003948656500080c4200b040c5030403a90703880070710f040203e14443d40240c805021018860118141c020400125280c504400b50b0850082604100244070000c0d00c0001c044000680c14200400e0b0582e8604054031001000fa01c500f46100c004420003656650040c84804068034585a500082400081010242070900d85031400b40e401500203122a127 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 149865143 1250 149863893 149863907
    0xe0112051005190e16060c0809061b12030910050403020d0818010218040f02030108030d09080723010c08070203040b0c01020c07030f03020d0f0c02040213030b0c070314070210 77
    0x2c01c402c3d503500d10300030940c01c81e20458a5018400d1042c2d003081c0001141d4881c02c0210100410341032404074040d0185c4d4545020511502c0d04952140400140704181c0194081000e8102c2041a040d101c0c021250310390101c081e44100e603400303c503001d0030b43c4e52001c0d20038038451540200d07055801064040e1900340c0a8030300c0940901034546081c813038002070182035001d00007000f42d629110b4099226889140c00d100c141c80800440d00c4201380144018441601e001055a00808001170080360940b13003420300d002984208038000d81640300e451060300400f000742c2885050710138a40b008102c2c90000080c1219040d50540304000140c01c01c001c01c0152020490282c034144007e03900051030314400c00c02c03127031900185a02c11100d14400c0c0080509040d01400101c50100c80c506141c0d03d900c003103c00003002440d840000900c41c0754080340954400d00c00100c0d42c80619030107a1a00e0a5082061110103241c2240500b24000364200154600103908a0182c451296015018401c1003a008105980352 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 149866393 1250 149865143 149865151
    0x3080a030c1e03241d01050d030e01050307030906021306300b190807030507060f0504030f0312110417010618230106080117010905070e0703021b06010e0112051005 72
    0x10024901001528107138088140003091703580d415825000c080003000c081204140e00441c4540c1080f401440030030f40040b84071100c072209180503135990391030741c40540052503003207406050f29101041910006041024040a40c1c040d9129a01c050240d501c0366802002c001841203545265141c1ca0417840f40c9a07084400c05040040c000d01c03038440018044060080d44ea40030642d281d22140080052000c14004c8501402c490b2030214640e0b21290340161481c03003944402001c0802c80381d0744a080c10701c40d04a00605a03481c1205100625030036100914a4109000341824440b40c03407107004280310144103c01c21a80d01514070074420107003035580c1c4002c010300c1180108800034680083c1c00c0025451140d4043d22494031243d5a65040c80501001420f0f103145201840c0c0c5021803110104400040b440115121030410900ca1781d03410800310060302030100c502c030103640c0000010380c0382e4a0100e501030507036103c0340301a0b600e60390f54914102d408025450240085c2c000032001c1440c1c8400350003640d0f01c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 149867643 1250 149866393 149866421
    0x11a040b0a05061903050c0301060912060e060a050703060f08060f28020a09051503130302030903010606020a1203020307090e040204060302060703020d03051b0a030515040603080a030c1e03 83
    0x28090782e031408182180e00c000311601d2031000c1e40080d03c40490b018419140c1090354038200344e06560609001605c070890b140074449440c02c400c10244100940740d00003601c41c50120040d2240b80c2044c3c0d50300c1c00900001c2c1e030403802080c180003002c545041c80c1a6140c0440304084024a910784490b060001407240107803040f000c518501d02404050f203089901ea040c01055246c0c016079802005070007d0045100350007451244d0b101c0d188bd110030380c580304c0580b600071003980c0c1070319601c182d640340a030318500c03a850b00316400d542441400a481600420180300040c017070b40b01c0c40d8030300b0450301c800c07000c03444101d50a1000c52801d442c10301c0550f030859003450b880f910261001409540700e8002580b96081201c080740142c2c803501d12068807544c103020b0b0340d402c64507c54039082c00f0240c40d0308500890042a00c11002c050342c4400103a10348000081c0074444000c058070411007181c907410a241c189d4003201124021a0030b04210600d00c5100740b008043c075259110103200e0702c8076081c2045018002201c00248 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 149868893 1250 149867643 149867659
    0x18020a1a04050906150a0815030a02060f0a020c0406062114071b08040f08010c091a1e07030521070905060a0e040e010e19050304090507120c0f0e03011a040b 69
    0x3281c03044002044000c606c0d803034102541c54400c0303040c540e8042070046a4007039000b107007031100140c403000142c0f00481240860314ad01d80351021000c916003100b06084c82c4d40300d070030010009403964000508007031441000b6042c2481030195000320050300c008003046054a442d0350000b50540341301c1c8906e4103040c001c1500c0c3c070540308820344801c89aa0482e400094009201c420304001922091094800060650600180f954a80360114105980030070b4074a40c52000041c1c003500b0301c8181c1c0c0c01044146840d000361030b21400d09080046c069000030001c4002a44003240700c1600a0380408401e00c920f1180d6202241c440c04d10041c41140e400c040491414481075031988000c81e515400b0340101000e0342000010b01d4100c0102091410710100e5a510403026503809030400300c0c00100032a0240c40c07410070041015203683d0000ca52a03046000500c40079450320b1605031140e41d110000c0040300c2120b581c0c44070f00c0e1450404141c04c0340c036082c184c6891401400c3c1c09040c0c2d814580c00c6042940c5000700040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 149870143 1250 149868893 149868919
    0x2070c050607030c050d0f0905040513080c030d06141801031509060209030a0f03140901050304060c0509030307060506010215010b07120216080609061302031504110418020a1a04050906 81
    0x2446c111000d0f0004011070fa444082d803c003a030b40310003800e0040030211010300050070708113407403440030f541420007800e04503001418440b0b80b0820011a000c03113000900c1003041c1390707441c19540b001c450034100f050701c240c841500304c046002e0360045950603a5048100400000b002e02405030062807a10340446201d40c092141113101c3e90705000701e000b401d01603603181080c1d04082ca030092240081281206085030306110000c91030341d0105c180c95006503c8580040c03104810081550b203400782c0001140d15100001c0c02c0b40401c00c058003e140250390a0f021140091408034103124061400d00418009401c240210008201610f40c00c4210102c01c0c01580c05003240c10006018100064207c0c3e1046d034409030510180500401101d45d11a001c0c1d400540f8034040c0e030380001c3e181c6010001380904407000710003184c00d0240d01c1320550000316004008008503240c4001030f00e800c0c002490305911541701c403040007400c41078484114052a04d9843d50b5840c0505050802240c01c80141c41c190300700102030300303034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 149871393 1250 149870143 149870153
    0x230f010e0406151d0702280215130f0e010e07050703030e100207051504050715030605061201080105070e09070c0305090901030c05100302091008060418032102070c050607030c 77
    0x81024044c1030004904050303101d0100c4c204848068040c000b1544030484400c40c80e1500010f00620040100721203071060564000144505a16004082090000115203008808030340031101202c103803203485c10400f5a41c1c4c00c0c2c0c211001d024800c0000c0301d10f003040016565481a0010090948a8100092801260b80d4514500b8103440b841090300c0c1e600041d020305028042185010305002160030209074a800e070394468803000107216042c041c0c21101c5c040c4410038040c0e000313600600340260089480c0d0003008811000a8420b105a075807079440e18020418541c800d80c500c0e5101e100c0607120910781c1e180c1c1c5200311410100b015042d010000140300c640c103640c1e99540202d00a40c082c04000d040d0302d041800300110307940ea286d5182c0c1454410040d0070001d4903820380b410f0003620103003820501380d500c80e400b04001e4445041d20710502d03011003920b04201a04075030030b1820008400180c56640990351032400403440307400c102800b1400b1b22202080240b034074600626000c1e1080c07402041100c20742d595 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 149872643 1250 149871393 149871431
    0x309080d23040b09010b150703030c110102070f032c060307030b0d080301050a15020615010e03100e0607090302060702060309160e0f0a0c1209030504050310230f010e0406 75
    0x100312540d1590b07100f80300380004e09014040d03003034004448490b9103920a03261007803248a0780d42e004050646039246910450b00540c0c1300e100c0000e40300000d55840810b85408603d12080c003d085000ca002c50702c040000c0d860303841840000c42020309005150070079110400c510b50304001c03c0601099280c100c3d03401580c5468000d100c1c20341c4184990350b05c1e94101010490626800e0700701d41034400c080c5062074686980090796075005044807000c050041106c41c01240c0c032035441038825405100315007610300d140b0300c1c0d41d0010940c0640c240544202d42c941c43ca0407140d50b0300a10001e50304c034905000080141c1750100c001d50304100b1240488085042d0b1040c00ca04220003944441e851074040c0f02000300709001c0d02041c5070302220590381041070607019200034000e0105141340080c03980d6200070080400d405041101c0203040000e084482c000481032128000c0c242c8000030440d000712480d803050705000b2440c944c40c0642c3c05640052002da080032010105954018000d0314101c2e1180e00d1101140c0719005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 149873893 1250 149872643 149872651
    0x60b0a140c03160507060c030c11030c0d0b1611070614040f0816060519030504020d05010e0309030c03010b0f0d260c160806011e03060c1e0309080d23 66
    0x20450007146484d04200303040458981c0558280401c020300c607000280e000c0d00803006154840030b014000031046010a19050b84034090f107800050b48909103050007601000d8501c662240320311000c0015100f00c007150f407000170f13499070304039640910024000b50b40588228410410b500c1c00e9142002d94620010320400b0885c0c0c0b003821250065a00441e1078907520502101a02050810790315020200d1810034140000b01c088408140e03540000c141196245c100c0a80b526030040c0007800713414101400c007500c81c0c0c00140c0c00351003880356258990260906004007141a00000e1106030083c002c0001d000c41201c0c005021203010401241c1d5003441d5180c0500420352200982c1e18580b03803400b00345d8661400d80101c0c1d40e4039045100703000c01c01481500207079290548100b5000114919262405440203640e5500000e002a092642020729948c1c0903081c21121440c0c42000c1c0700c0d00400d45400d90464910030005040ca030800c0042c031a425016401542c400d406413500c03c0903480c0300301c0d002e6001110a803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 149875143 1250 149873893 149873917
    0xb0711100507031206030b0a0207060e15060f0315040b06060c011505040f0e0a03110307060216030e0a030308010905061305040f0303111c0b030a0b070c02010210060b0a140c03 77
    0x700340b000506510071305219583c0d81d1114100107403421500c5490061800074141c04505070005442d400b0040d03242c00a24085171540c013290141042000e42c04c9404008454260292901140c0288145070010354810100d07080c0000c40101c1e1582c6e210304042d4540240042e411100420a80200502c00d2044030030151203101c082c0b40980c00d0074100019200c60b4030301640d6560914146469644000c80c02400060b41800d02c214800c4800d8a01400c60041c050087d00051000c648504d103481100d2510803101d110b50768036104c11a40d001000309000f070500010f0300007459100107203d1031100781d12107500448002d00a84114940961460644404a804640c1d80403403012400c1015054044c45400b00000003185061180810404802035000140e44200946070250545a500c05000f068000d5412960f03450132441e1400000d0a5800820f404900621444081003d00d17522440b408082d1005110207520f042c2204504442c801443d521011800c1d100308100d10403000200014100786001d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 149876393 1250 149875143 149875147
    0x207030b0a050115090b120a1e06050310020a09030b0601021207050d090504180b04020d052e09020114090102010e011d07150c0b091207080705010b0a0509010b07111005 74
    0x130251100344540c50304100511040030001e0040c02d1441094503400c10454a4200007076603001c01041c00340014070f0030701200203403400701602e01816035044030094036410b500301d803103604140054808901c100041d88000808910342030000401d0140c550382c000c40148115241c4085481842030141d1142c0030866103907001c07400280c6000d401500c040020107048400b00320400340e0014442c0091041c0800501c0c201155001908641c3c42e00388142015400c4012100c0d034110004200e405100d04403007405100e41c0c800d4520509a544d0f005410b400c0381e040e500c41803c070101c880d148040d41c001c20011810755480780d107410b00050b000d10513107004115641c4251401540c41c0c00340c601b0491b00707801801c1a0054888140310b078035000005072518903405160060301d65648280d8038107207400020000b030260400202c1030144030003100038146440c007a200030000c6c07541000800604c0c030a54404e06800802001c0100034107103001001d0809540a074510500c0034007020001503549108140b440007080c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 149877643 1250 149876393 149876399
    0x6130b0610020c060a270e0a180c0e010302031504080901030f091b051207032001051e07020a120b0601050a0c0606080304080f060709181e060e092103070207030b0a0501 74
    0x140701c0040c211b600720a041c2882e11414072005403004174004000551142c0ca410742c0b42d009019101c01240e0103030304890002e21041d220f2440c0c0c120207000788070982c03091203540018940c0081e6602c020f802154003034455850b00c2944401034001e007602c2e9125a0025036101c0880010a0f02400322608202c50001405800d509200820401c2190428499050ba2180d50140001100d0000e441115242084000c00c0e91590100486441c0b19003034040d6210142c0c51598400c0b154103001800318103208442040303119440c0d840313000349250301c1c2002030088028100490402e5000750001c01d44d40b1910329122201891507101c420545e000356101c0e040d580d1002401304034840040c014100e003208104007420703c82c1080040100050403c0c000d500312045400980b08405807251710010304420b000310581c0c00141c14410440c020842d41c0305841d54441e50300300261010b00c011800305055115425010b103400d0b21840c007140c00740c00c020440025440380d24000b10118405a00b60f500c1a030210f54040786541c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 149878893 1250 149877643 149877677
    0xe37230402011b030203090405061c03080a180809190803040b03010509070c0215030601030906060b03070e061c1104030b090f07080601060f080a06090f0c0206130b0610020c060a 78
    0x1900f030b907652102508000c0c1c0d9600084d0301000f00c030780124080703a0228040e19540000342c0500202501c01c3c1840d9042c080d108100f54000688501c9052861020480b441100341e1060b8040710f40d00005020b01d004008580691610703141020806042408902140b40c036240406c1c44d65000d5080b13a400e0410200c01080681ba11a200c0f03540a40d1500d0a0039070310500e0790124081e008080102c9000a002000040c0542d20a40c005040315030010000c0c0400ca5a800900c41507a0060f030714100040c1014545043c142005011604180c00c8841d049000b1241c40c07604c503008009c0060303800c00c845d10800000000c47d41d8002840d0146008038003500144400343d418a2402110358000d0340c00c0d400000c010049243c10810301e5401c0205400c0042c410b07500d48815800902040c0c10410707290f807500344441e0016006510101403c2d00540860f0400e8484401d42d01050f02c14540040c90800c00d040003440380d05114051803110311150044804036003075030340003903102e401c5000440b001520442400d41112 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 149880143 1250 149878893 149878907
    0x1020409020426030702060711030a06050f0709030c05060702181005120c030303060f04020c010c110717060105040903050705030301090b090a180813080a050303010e3723040201 78
    0x400c40c80c0d010303c40d40c400011803504c9001c4e4150103485110003240c20020702607180302000d00d100340101500c00f20b11941c80d00c403000b86130030b4604042c2089000b00003481940981000010759402c00a440d850303070324040c01c21a0a43c0314000490304810746d245909554041601003a0041d400301d10301d130b4406400e200c00c1c41050825072650114580c4000075000f65a02c01008603500000140c8005040b15070090218010f44142d01201b02d43d5031074805d0a40300c86522004480ca00b080c0780c01550300207541c903035410a480c60528440c50103904a00d004102c10711301035115521041c030a06215003090382a44890382150000d902c1545c019803229890006880c00841c4154041c5020504110b2a811800b2607036490051a5009048610005182d03a580412107841e100806c1282c1c11282507002501d0074a80300d4101b1301c200e01d02c184016002c544038818180303290f50300240d0105420154180780b80342c04084800c4104800000d0b0391248a0941007505000034084080c480c201c218040c01c103440010301c52 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 149881393 1250 149880143 149880179
    0x905060a0b03010b030406061e060e0f030616022b0f05120403080603011104031b09060b1909090f0b15090117060310021201080c060307090b0c010608010204090204 72
    0x10300c0c803103a0184024101030003a641500c2caa0600c05481e81e071030345480001000c09800000c800c500a01c183c0c4102450070104105a0ba01075031420700f6603103a4400c0c00380800a40c24030903415041a000910000402452120f050055104590b94000d5180050309030381c0301d00580c0c0200700503d441d000000c58008d20008180c07412072505515001da140300b280400f01000d00000c003001661404103031156001d411000c50403020580700c3e640c80782d4030300e0180d0001e0884d01285006076141074000580d0701d9240304203802c40d18000a0795181c08000c0d0132400c1c603955028001024488404408603803050305110b043c41100c4290400200d01c240042041406403444400e0f000400c0c0c10006086e00c0d9900104644000028520014007034543c6800079040040080000403043d00c0420f564416034210580c00d130481d4800419a0618044081401010b100481e0350301c0106058030410009a1303605002002078040c0d1000015105480300201d07800d90307100c0d07400000d505402190a00401c0500d01d071800310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 149882643 1250 149881393 149881399
    0x602070f0f0e160e030106081e010e060118060905070503040201020f01051b0f040503010c170702060103110d0f020d050d0f0c1e0201140301180608011802150403021504090506 77
    0x303070382c41c180031200c008200404110b0400041a040c545507409a4941445584020001d1011325203d4921613555400d807c0000350011496850340c2d1a0101032241d0350501081501070003060703003004020743c2078070100c00141d5809682d50b500040c0302000f500c68240110543c0d07941030303a00d040c85d000092600081c04843d18441c2d00d04410f104c0d110390b0a2035203000300252a072900f522001104140c64841c0280d610141d010350806540015260340080c41f080e400c062008080b5441c3c42d100da040703030381d44804d0000818908466030006d50610b0002541540c8a1092060a1035000a81e010032501c00060350119900da105581440e400c42e000500423204c1032170b500c1c11804d620700c69112480d0ba01106000b1030846038442d4480c0040da41704407400ea000310b4900e80c205980b541c2d00e844040c1d0802c105840320003803c0c45c0c5500401c9451060080e80446c9003e030307a0400008030036808010f03503807504a01152812008010000c01610b40032400100c8041405041352681d03d002c0201060701c0d002403100d48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 149883893 1250 149882643 149882669
    0x110901080402100513140103151a160203010c0e040b010c02030601090e0106050a140a0605041d07110d030207051e030a0302130506041202180c0703030b04090209010602070f 76
    0x106664400d0326141e0154044030b0000400c02084801c1e1045d00c80d003c9440500300300d029002c11008514419030410a60a0764108451406288801d4903803a090051440c100c04070380c10342e00031060740c1000d81104d403c0d003c2d595042c01c04a90002e03085a4071a6104000b0449020180703032540703850f21a468001100782405000031006600203510703488140140c0346202c3da90146200c0c3d40d042540150050800a808041031a881d25403c010081d14410494840c6482800228600e03100d038090782e0840d0b010426a0416141c03000801c8240103001f8a0b00080290f10401600c0c1100b040201503840c04960301c0059465049040007801c0c000041000b0320708011074030012052032000001c40d20030600c3c502e001a103c0c48100c400e10301c1d08034a503010307580c85600401c000c40c41211a1141c5003002d0700c220349040952030090790300b00c0100b50444044001d000140b215401182c02a0440d04181400810005582160368009620081d080c0c11520050344410300600841510307045903005444200390f400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 149885143 1250 149883893 149883907
    0x8060708060307060c1b0510020609070603060e0420031f060503010506060f0d0b1009170a020102030d090204090204020d1413111005090907030c0f180b030712020d0203040611 77
    0x581128060800242666102203001c0344401807010402c0c01f07000000c0810201110040c0d000b035640200b80e40c0c2c850340b401070780000510300d40680301c0d03481159800c0c42c2450307440ea81c03a1100701e54811101850f907102c89890309840000d0b501402040000c4a03200146413400c83e807075007824102c80c2c4030740210b40268900300501070148e4034901076540415058084560310a0000250005042e02c69641c03a00801e69000d01c0f0215600120410300380d60094807100307003580309584256038401c14010080d025030130400400d819144160064401c5a0021f0004290b1038065404182282e214034594042c0642d27440c20000b0090f0030752a51504010440280c01c40031010791200280800300d2010745103e000c914500d040403d00560a03180e48030710080c00c05a6524124502901138a00c07144240006101d500030992a940542030305504070426a0103420490308103034104c070941d88050160313018060154000011042d1358002403c09560403400543c0300d00702483c0c03c00c181c0c1d1940842c28580c80d4213125030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 149886393 1250 149885143 149885147
    0x1141506040b09090405100603030e0108150a06051821060106090608130212060a090210051201210c0605040e0601050c19230109020a0501020a171e03010806070806030706 75
    0x41c0f04115821500d884090315249000c0c0e00d400940114410000d041c003d001052580002c0c036451a00b03020b880c1c44410b90b07544050803101201c1c0c3c41290b9070140c0c1440d401d220341403041002e0000b442200400b50000c3c0e04030380000303204800c000da403800d08280d080d810608410041c40703102d00501c420708120041070300707003000174003030220081c030050815094080c19000d544c3c40800b640307402011541a21840d00300b040f03000c0064007140038142e000c0e080315643c50740040d12407401c0300c80c0b00c010013040003c1e60342401240f000f41c004181d1a00e04060b00401d82102107034916a07e00d0081003540c40d40c9640c3d5186c250403200d03600300285041c2c140182402915500d40d400700d03c0c0400701c45c4400701210a80c52500c2d10424807502e668100c1104402286c132140003110540c0018003250003202d0f001c4a8a0382d40004a80d50b03004084010140d0354034206040415210b4009040c00140c7d1940030010b00718404804c031920f070001d034054080d541c050018030018a030801e0340107800103003c0c1c1c060702c03070a400c0c8900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 149887643 1250 149886393 149886397
    0x102060c090f13021308210705010b1c03030b10050711131b030e03090d0314040905040602040e09010c0206220605010603020405090a0c09170a0501141506040b 70
    0xc0340303241090026041041d981d80e4090200300480082150850b4160a000c1d00b009420400450569110041c0040351404000404c0c80389111220b904183c0c00d42c5440c502105074000700303022100382d074a50303041c424903654144100643c0071204509910941c81410014152038402c210350b4000e00300c916100310020750000c00c8800441d00300d2a9918440400800b241d41620040314400303140c1e1601041c2c945943d420b43c00e418210b101d690b1b0a0061500c4001425241c0c070640d40e0659200d1200034180c1e0009001c0e5034090440f01e503085145e810903039203179115030035114102c80444d00180d000030148000c050740c0090315044443c0c1e400800c003520b84a01d010f55a068007034000c03040140b801440d00d0300034003e90780b40010b0690020003840b43e545d4417040507000c2c2d0010301139a44a405880b00240300c0a02d180701b800c1c0c43d000280d030342421003458031080000d02e484400107a055070285140902c04903009004c3c1981c0d9800c0c8200280a505c7c25400f2050103845540d4054414102000100151000303d0300b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 149888893 1250 149887643 149887651
    0x60105010c030203090405090102041805010506040e0603030705190201030507020c13050c09120a030206011e0303050a050f1201050a0504110d0c020109050d080103060b0609011707050c16030c14010206 88
    0x7004081000c050500760314501840154130340c40383c2090200821010190040c108441c40160114203009820081c10190780c0c0034015560045000e01007040306c42d20602100350804000b809903803a06100c0c1e10f0b40c60806ca52080d1519142e81c0c01c01c0000308550749841082d6002045d8409407510310801800201c075084420b098049030750310f85010a040394048803c8810b0031000414090013182c1a08245440d00d08100d02507016004103000000c845039000d45800c04241d81c403140e106c0050455800380c406400050044003000800d01c110b0244000d840014800d494000e00d0300c0e03441d98580350401042d03141e55000300740030710b04100b00d04107203183e00410740d004447c0111011541032400b0304100d005091018014146125071411074140d0f0750020342c00d0341a04d009840c140701c03194246050161030f1081002c0680024041d00301541d00407000c0428030340128080c82c1c65032400b00202100c5152071032001000c090200d0300402002040000902c504c010040042c035003202255243c0040c0d161a0005c2c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 149890143 1250 149888893 149888897
    0xb0a0f060819060b04090504050601060c0807081e1c0c020c030d110a17030a050601020106270b060a0f02010b0f030c0d080705061503010c020109150e150f16080906010501 75
    0x241424440b01d6581c0c2000e00a029001e400584440d522192200a09816202951107008050000c81d180340304440d0a0b00d07160700481d82c0c515101d0300b5070b80d03a94158002101c14540702042d481808039603540d880101140150304020460b2410310721000d03000c039002048030806551100814089640f40030506911074195420010111540143d1050030842c446078001d000051100382e8240b42003d42d4041e60082d03505000401541e40d0740001039080380c4c498024000500400c030411100b46e4852000301d0607a540e410808100c2258140106826401c44505007000c06c0c800381c082188260f0901c1085400d01040b14600c030510191b00c04246c4035170509113007070b000700d03060f4026000348620f510855428503840341c112482c92608103030038207290f601c2414082c80303942842081116203105008924800e0741201d9004c4100c009107003000020f111201110745580100c00c0b2101041e1404211103200d2407081d100f440f0f031880c1415490401e540c0340f1501500b400340601c20301008420000b5042c1c103441c428 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 149891393 1250 149890143 149890171
    0x1051f120201030b0904060603030807050a12050c0d0608072d05240a0206221203021b01060305030912031602010c06141302040f02040803030a0c0512010303030b0a0f0608 75
    0x1c1c00100c02a008100d841a0480812000d01082244030b40c07191048030700941c1c983c0d10f5a1180751003207580d445048a40d00000f82c190072142c800d1070700b03a400150405036451441d0b181c0741035100341e101030f1011944440400d801004040002840c0c4141400078140740ea06240482080f078003401d101c10b00301d0301450303004604c0300882c03543c00524680c2410801110351070072500c4004844009603100c4044840a014410004820015000b604101d0040c00d500c8487c00c5c0090300101c8044000b500071084641c48881c100c00c4d1826940800e06c5241e0165000d14042d5030384400c40c07000d1001e880ca020307003803542c694401c00c40760b03200c51221407a03400900e90900e406040e80ca018141075010b020303a45070303000c0114002401e0210700da0501c1014000c0710b02c2901d06001c01c07411540487c041303010320320402c800c0c1d4200704009220704580ba804525000303842c2c180030303042c0760a152110026400980048022941e0781c282c8228618041c1c0052004004031940c0075561403e00d1401420084040c103030100703880c88 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 149892643 1250 149891393 149891429
    0x50a08090a03080705010f0f0c02030328020d0e0f03070503070b04020109092d0510030308090106080f030703120606170402180726090309060307030b04061701051f 72
    0xa076804841c02180c0016185841e26454108070340200003030303448009158608204100341035004c0c0544240798220340c014500303580d25641100c9508403080600441401890386212851304244090405070800880c009803d524103c2040d281c010740c006503444a03402800f080e0b00003500081291800345e8080d02052041e115072005139850348054204248e0300f400c20034008158125200c0f400040c1c0000013940304002114003151081707590a840782541260000c0301803001c01d00441c0c0342500303e1904000001e06a1303458100c181005141c100e0310034103800000741d03002415401002603070400428a4108040380c50710750050702c580e000000c2c084440b100540098159542d6040350810b0000c1f0303941c80c2d1a2850011030040c0141448040111103e85c401c10030b080d51040440824031540e07025006520f0704120310104000b9400041a440c105902d6140300713940da849034000e4000500030b488001c08020140001c1c103080d100d000b071803010070781d03d440c00512841d1016880003049807807a440340120406 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 149893893 1250 149892643 149892649
    0x9031e1204150e0109080606121509010501030b0106090803090103051e010303020d14030115050903240402041b021f0605150903070602070e060126100e06010309050a0809 75
    0x200c14000024400000304000030824259424003200500c1e5955800d45074400c1c1005450b000c9841c0a465490351040f0700150441c202040070b002114004003c440d01401c4140c41680c0c480001c80f010380b21070f51500010420841500551400f601c4142085c04280e81803201280d66401400c5c0c0d450f0400d0b860b000030071007031102403110188c1010402c43c0c0388076568490802942c2d80082c0030b5108005030000580c0380b180302103501a039060f0b4003240705000080090142c1140c55400902c1f1455040c09068100e01c3d1651403810b41c4031041d0100c2d0780c4100030f450580100011541709035042d0904424118126180c03990118080c0c001040700710100314616288030218004140941000750808481040001c1070226440500704d08841142118400340d1a410101d03252811841800d0b02d401200010800d2980541c60007699000721a0a4240d40001c030803001d0107076842034a2100000441c0d030f0b0148440310b00300c0035007540003500b0b003001c0c4001d051550b6183c0c0d8030b100c5204054201e44011a02c814256 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 149895143 1250 149893893 149893903
    0xa0e0a03120305100b0708040504021e071217040519081e07150209060f090402070204020f030603070801060803040905150d081b0a0206040e06030a0204020d091709031e 74
    0x3541090010148410907070001c0c0c0201000d46002d039442c656408001160003040c811102c185500c486410704080c40c103002e110107900042e0000b195043c50191110f06121a280038002d80c0740180c0320380908100b14800a0020b0b28540a60000ca04c80e09081001181c000210f0745038280909075440465a0107090450031400b40b1038111000301c000a880307000300510074014190a5000750582c1d403031010700e0400c3c441280306090440f338200c01d051181031040d2140c48068070081d01c014101619000d40740e07000070101c1c4d000142440c0e038141c020081c070007603080802007035025041030002002080e04040b0503642c0c07400745128000788151240700080c0300303844164580f6490700000d48060301e8001e840c81c010600d50062156030140d05500c00303111403c0319002503c0b0300210307000791950f0b1500d410080c1280640d9001840290540f05000c0030b8001031700c8610041c60300c1d09035000f000132681610310b42415078040c82c0248da030040000340550740f400d42c0c1c04101007200c0d2454180ca042c42400e2480314505003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 149896393 1250 149895143 149895149
    0x1214040e070e062106060403120c0c05090c22051e040e160305060f01060f0c022805040f0501050f040e070305071e0b03160305060402091c0c05010f050a0e0a 69
    0xf090000c10031802c2d0213049640610305403c00011544c0c107940365001d03c0034501a070b10003d044084030310340360000c1d07901038000c0000d4540075000d0b20341410b840f00302140d9054400e4031602c02c1440c00180d4040c05a1039841d04101c0030410348481840039140000060340b941d0820000940b101600a10f6040c5076207640c08155400509019914030175401c40c20060300808610003039400b8050b000000341800c155400c400c0c144e49494403000350007032002101b162107403c22601280c001105545d41902407940440b007601030351407583c0da81d008601f0401840143ca4440d03240c500401c2c204801406503903038002c01100c004005a0b0300042039880c031002d10f8640045540054950700800d9404101c45100d485059101c030310f0040d11103482950b811515000744412203056201e00086440480002d1198005a80200b00200b0140c1044a00c200051294400b034075034012401702003030448208507102000d1001080242082110000d500d407024015101d00c8403c00c0400003011441d5640d50754200c501c4000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 149897643 1250 149896393 149896399
    0x1081b070b040507030b1602070303230d0603050d0309020a0b0d02070b15030c0f0f0d030302040b040b0d050a18080a02150403020109060b0306060310050a0e0d020a1214040e070e 78
    0x40c01d1034103143c0d4807809603010644a01c03020070000381404158a807a0340400d4901d50042075140e19540f822104e151411009030b880c1e20302c15184580414010014160a150b10b44c1c00165851451801c41d2900c00c5d0701d2950001d1500380060900980c2e0b0b142007040443e941c106080d503551a44404003002441020070041840c8101e000740605000c00664940e08140160110399000742184100b2117888043c1c030005502c000030465490680c10410360600b011446810302500b4161940405806a049034018903003051002c5455842c04100f4003030981c00c452240030400c41c07101500c000301500c103011040907141c110001141c2110354070800414481c10480d0060500c5810705280007400313000019000c0d50b9040c10000e801042c1e203000f0410038000c0070010020710f040c4d94990030010103410010448400c3ea950340d410740c150320805005038843d01c0e840d40c2c00f0b4100c211951500740c5610790708100110402030700c100b00190740441d5000f20f40588010b007045d90300541c1d0b0b0141c100c2d10801c0080106030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 149898893 1250 149897643 149897663
    0x90b031c051b0330090c0a031e0501060b0a021c05072003070905060405070207050102100c030e1002070c0816230d06021e2a0304030f110111010b01081b07 68
    0x50b00d40c3c02c0740e50014040c4101c0320320b44001e0b145c0c002550380c1c036900c02030341c0ca41c000c4402104200140d0103490900700c910082100311040111382d00c030309084072001d9008048140b0b0000707030418402da060055845030050a050b400120031048001841c0c0d0107a40b600621112141d03c540c111154402c6200580d6440141103420032522000140090702056804500450800d00801c44090010403410300b0303140103900a2900046410000014083c00007120040c0b40c0d40f031000241c0341c030007845a10349101c511a40075a840301d0600c2e2440155006a00c0101303035800004c00040c84a440404590480d42940d0218103c1c1d10684217901c01c410581c1c20385c1e0340c08603020503050708002c00303a0058444042e0000380c1e0000550b1413681040b440c452000561100800905171555050419101128141c8510f040b00c1c203140d100d070350301d407070075650300500344e031014150500c440b890342c0d02002c0300030031780c07101d9000740500090440045d00c6000d0203811104034507540c98a0f032010303109540655142c140c1290184c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 149900143 1250 149898893 149898937
    0x30307050d0b0103020309060708100e090607080106111203040611180907031107020d05010605060a030f1104051011030f0f0d0b0609030a060209061201090b031c051b03 74
    0x280c055071007005509801414046950b20940c007902c03e0301d1082e4250000f03441240d07500d45003282d4075400102181c3c0c248820380d00108003c05040500c911903510540140b1542c00c19280250000340140c2c0803400b0042c4142044c0181c1d0804540b003805c030400c0c0104992291101d16043c00581007024440315201e0010840400c20400300000f031a800e207040d1500c40c0b5944400c1c40c110b056480c1e60481c3c09048600b0400503005092112007008058002c000004000f500d440c0010410350040450b03400083e00c0301802d80000d80c151007000c581d884a06800e0740740518103004210b002d0310b025010420700418000074580c07a01c0500440b0442490001410f960304400072564900390000101035820305d140c402d6083c41d41c00c02c10308554891030000d000b40704410701950341d000654802c04102e9044041030001306020403081894902800001a000c81c0c1e00c03040509041c5094180805040203005410340419456001001c54400c500c1340390540c48460750071089103186100f102780703140d00c1c491440595 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 149901393 1250 149900143 149900147
    0x3041203080412030e0703030e06040f06090f140108040201080604110d060602070801051302101701090e060a0902100e010c080307021e0309060307120b040509030a03180b0c0703050408030307 84
    0x1038070441c481d03900c220200703210f0a4220200c0700010192040703644800003d101003801490f00f0781358154020300c49031425480d215980400026540810041a040c0340e080c01450105001d40001c4d19403c00c50005010031203000a2007500b019001905000c10700010404903150341e00300c0f070b20083c690f114450340c900804501c000100010720940c8014080d10401040040060103102e00910b8001c8102038a200c0c55000c0000c1111030b00a600c0c02e014400b407800903d01400c0d41c105000b400a00303000106039901c140e07194240f5000801c4440000c0c9070132500801642c5074501114542000d03c3d05460181e284401a602c824007840c0282607400007004121420741e002070807450100f00f4541c085030070103004443c140d80e402445841584500180005004a031180000311203d445441002c2000c10015010404807007003622008520b420000d4521051030300741c090007816007520324001c1d5204026031100d6000c100041e00b000203a050000726034050500c660f0a0360050400a003e8941d281004800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 149902643 1250 149901393 149901407
    0x7030203150d290f07180f030606060908030901080109021303020915031606050a050d1116030206010f080601050609041508010b0a05040516080424020306120a0c0303030e03041203 79
    0x80d4403415035414500003e040c6140c3c0307000c0c060044807584d100ca03922040c40580b684200d0300304040d40060840c2c0009468100920454002c40c0a000700098031400c0c198020f141031401d402c60070040d80100300601c6103981c0b0024503411903000380c0f030041e159080940450301140f00c0707a002a6000c1394039000d10609940191101d0324010003141100c00b150444000c035900d1408030700c41e01c0003080c1c060010118850052006000300b60710014009010b0340c00040110840e0401c0d02050340c0800304000150070580c040141038003602070b84254159852408802c81e41d203410500070700f40949000701c2d6100c816140c43d04213194501d200c0952055007030f1220019402004407a020a216061642d03001170a410944103950040c0f641220410114010107400e03501c5a6028001f107070508610801d2405680a17110304c4074000b0042600541d89060007070030442200e41e00220705149412402e00340002442d50700004041781c0e81810086000b00b180d500f21420f40c040d035480083c481030180d1582082590140ea = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 149903893 1250 149902643 149902673
    0xe0f1509090a0b060f070303060b0a0203031504020c030405061c09081306030903120b010225050114040e0103030f1202030c0a1806020606130e010c05091201090b07030203150d 77
    0x50400040d0396511030b900140c3d002c203c03034a03400a80401c4002c40d00382c640070042580f207001e0b040100388580c1d209180c411540c44154442c005030004410300902a12035255965140c40842d0309509020000240300d482c1d02c1280b10356071045200045038440c494802ca440d0a4540205034104012104ca091540e10b5600885002200054040300811214000e204003003131030b038055507203071480d8210350700303440041141c03840280c190310403541d103080c1c80c0304e480c00103600e450031003030103030303040920b45000905844100d106041002a0500061200000e07580381181180c1e05032400300c03000c800014080e12100e40c29080d18076124000010044110700100c001e212100e460380e24002c1d440001449036214070039034080c03900141c01200c041034684c9080106042c04c10056000003c040c612082501e003141c05007001d040c041800030503841c03094035140d00c0700b540400d14070000307101100c01c1e0b544102c008200100700034241540070012885d00450400490745881c40a009407543c8038407400c080f0142c0540b10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 149905143 1250 149903893 149903899
    0x70f06020706081312051c06090c020a0512031b040305070e0a0b0a031103010e010e061e04030509040f02070204050a06091506020304050904021c030f03061508070e0f1509 75
    0x100300080c01d40d200c1c40c00c1034450030094214503060500c030340c0c0c0c0f00042c495217502807003001028080d540c0e4404800d100740e00c000c00301e0b00340040d8541c40c3c02c1c1c546d001d03a440f00d0456415034205400e070a000c1840440c081c40404021821580e8a83d42c907269481020b030340c1244504e50380b602040200c20402d0001d19003040d114040110078041d96848890000e035004440340c00d8104222180401c0010302e40c034440607410b01d0080000c0b69554112001d9803c442c51284550850b9000b04140440d40b080c0442c00140b0304007003800075420786010303200500305d031044200c02030160f5070b1031000c0607a042c02daa05490003241d000348140114200b842541000c1d0805008030841203240120000c01c140040d8401c8040f0b0b10f46802031400c1501d018100144110002c00c01d0740c203e80c000980d00b44614031038080903006403003a03c0b604040261114010111038203508100861071243d812a510769801100841d48242c1519102c00304280b1500400d6504104045082d085010405000c0c0302d10750050241000c1c0c4815 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 149906393 1250 149905143 149905153
    0x702150a0c030501051e091009091506060512131128050f031902040605091312030203100521010608071403061003080f070c060305061905090601031d070f0602 70
    0x17807040014803035207051000f401003081a0081c200b420304019990388100b20701c4030030040d6941c484c002c100f62100003204441e6510500c0c4400302c4402c0740d00c0340340003600e450700d41681064051840030890010150100b008018242414801c2000d55040410031420141480f11014035030280c0d0440380c40d162a04180d213449122001c6080d04114031501810040200104001e0500420795200303019032400a03a00303e0f0715090081a1a210000207600a94190705130018180d07141c1004005500c011100608040c0100240140110030048039000c0c4c9400f10b071400c40c20b4010700060704a0300d158401100895080c90000106090007045050407500c0401c1200140c2141004141d10b92030304948481c3c00692160040c404100c051001e005021020001280b43c40400c0d16102d8046c18607601007030000c1e40310000c010950404400802241005144080f1881d0802002507034064000340320034101a40c42c0c000007002d0391030301e10302c4058541030025502303019107030382252090b41043e0288038054424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 149907643 1250 149906393 149906399
    0xa0c051212030c0c0f0304081f0203012907330207120804150216110301090b060f0a120b060405010e0709030f030e0301020a17150d06050702150a0c030501 68
    0x101140002022818030740e02441c41d560981100d4450700500f200901e030707201303600f50b900005034200001c002a000e094001e0900700403104220114000ca0074a800450340184010440321980500199584414015101e00640b0342100c5800310300600c4406803070600101e0302d00e2104c07920210300c1d1144c030022244c108143c0240e044040140c1c815520000c000503200c034485110b01f4403403203040740c209100e01c0e080305403504c24150900582e00143c49808000c148584480100030a1140101c0d031544250700034030020148d921413014041004020a000c1d8860036503000b03460f0344031005040900f20207032817001182c889080004200c2e10071100207005900c1c1000200c1d00c1c42449015074070603121036480c0381c510307070070360b07658494103410b140e0304609014802e4251602981d013070000c0c000890080d642d041d41b90f4180704140b403a0f1840a0012f90a0b0600d00000d002075072150004800080d8000307201048036244c2c2e03e4104e1a100301c0d20900107022142c5000d01004640c80d80220b509000c40356400d10869072 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 149908893 1250 149907643 149907679
    0xd06052203080f040305090a0815060406030f060b060c07170c300a060f151502030703030b030709110a110d080f0403020f010c02070306060e04030c0209180a0c05 71
    0x20359010041c1c04212020300064400c00e2100201d07038454400c0c40c4c000c1c140703107102c00030402c0c0c02d09a0b00700001ea40c20522008200507188502ea5030300850448040c4a090325684911001400c0c41c03801808a9448460380c90264450704102d402c0c120004080f14442c5950703840c1d05001020703640c03040305280230324a500f202900d04001c2c03a4804403461020741c1c401c00400d001040800721380b400e00341054000c0054440c0401c00034030a42c034900d4038050004c6000260000b841c40b401d845900302c95040148994401c81003903001040c0c42200360305040015030810503c000a24000c8584d01200a0a09041800e011790031044042c1c00034065039100c40801520f143c0146840b0800240240000342d00940044d40c050040100650818081d00503138081600b840001c82c00d60b0040342e00180940d01400b0304201704001f40c42500300400c803413049440182000c0e80d008200014103480603104500403800300b100c1003488140c00101c075010b2021152144114540340380351080c2c1d07100f00e5100d140d01c50510382c8414 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 149910143 1250 149908893 149908951
    0xf010c09090b0f01110a0209100602100519090c05060708040302130e06190e07030c0f0b091c08040807140a141003050a0e06090f0601050d0f08030c07020d0605 70
    0x202d005107000815900c00b40115001d41906028072038601c0707100c2c0341138050703100e40e005903015482c0910f04448180c144000039107802d01c09040c0e805081c1c1340c0020010042c80150b6a50100c040b215000700f1002e62a0611f00c1281e105600f020354015000a11903081105010081084034800d640d80c0481c040c9011450084546504060020b03800440004400315180d014584100102600002c0c80280a6910901d4805103800483c0c2c031105000b02400b2403840d410f00c02d801401d450303034842d00c0c020a807004030b027403c0300c0310020825520703c2c039403680d0421140304255005000d22004032643e440d516200e40030042c0388180c136280101c0c55084089802103c040e00ca03c84081c001c3c140e00c14150200c0310490013880e004014004807591760401000b080410702009004086c0c140c004c0001c1b959682d0100c0c10400c060340182d00c41d44400c13240d580060400603030204800d402a00c081d07200d98902540e412a8803070400000c2d4081e058078006002c21400764003103030180c80e00e41040c0001490340c0f11200309131 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 149911393 1250 149910143 149910161
    0x70e0a06050a080c0603060402070515090f07080a0b07020a12030506130203091908040f080327030607050304030302040b070f050d020102032802280e0d0206030117010e0f010c0909 79
    0xa6003040b039585429091280085410030b07c0904010300c3c0c28400d49581d414082d040480e000704000760024880791800c1002804032002101c8040c04400f0300d002c150355610780118400074100081000080d02c0d16000f401004056500521440000c40e81488010014402100c20718403940400c11241070140451098a01c2209050000c10154141d0404642c42c88403003a01220300140030840401c0351400b85000c000101803941c001c5031200681d5030400c001c0c0036007a06108001a030494a1a2155000201d054200410b0b0401075070304c0c1c4560400b200640300d141c00c1034810843c000390036010401d103031030815a00d81c09403003591001400850120700b1b0740b0040d176070781030249201e80c040c41031244902c494200320040c2032401803409010764620780032003034105001c3c5062801c0305507611000d40c0200484c00c000350211070403403d1070a994001841808103000b604074000c00346200c40346540095008103882c5541c2c004031626410480b014038040c08400c00300000041103090001006c2081d0f00840e520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 149912643 1250 149911393 149911409
    0x60106110729090d12030606030b0f01050406050c030d11040305010c0f05031803120a060503120309030711271005010504030203030406030c090905161115040605070c05070e0a06050a 80
    0x1103529442d407505030f0820a03040b540700701c8289030707840000e5020100100b002e0142e18042151031420758068100c505002d40c00b800ac60100c2d152071901d80c0d0000454040d1b03051818a280c072400040d903070364618090310301041c5102c1d151030039080d0960007000241040740d200d080240400700103a0300031074800c0c0e0020240d0f00400d100f813012903c440042400d207480307480e8402c2101d0400c0c2e00840d42000685058601ea100c055170b8402c00d11543c10248042440b9501c0c2c1c2e8101483d40c14403802c13944c0d492090a20281000c0c0c0c2000680a00e0351701c1713400744221862080514000c1e03102c0c068481054500603100340e50001c042c3c8800240d69401042075070112a0001c1c09941054681113094001c0e0252038102c004004149402140c030034214070445004520710500728401c5152201c010703007100d10890440702207502c001c20303034006150025803690b0300540c400340228003601e488205407401066608010020b0040300300100e4103802c40224148954107800d02440025560000d101107800c1034014251 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 149913893 1250 149912643 149912699
    0x9070509100509240a020c10020c0d0809060a0e19080a0605041b060509040507170412020c030d03090203060112020105070b1012030f0807052502060c0601061107 71
    0xc08140100c029054084004c1e0809100465075920301e100700e501e03072090031054070002c9a0805000c0e0b040010450703a040540d0b20318a000c1c002c4602a540740109000c6900c0341010807650230410402c14150380c070403540905580d07102c0e0351000000d04015031003807405020f290010711000c110840b01240d40200c414040103004005280e84414014080051050300c00003401c2c0d10343c00080707082c1b80e80c030340060805030381c0c20361104490b10401c4240c0d6000b9124000300801d204d0b4103020285140450340c0c00507440002e20700c0300c40034050b0980c1000d05e410543d80c0d050191041d20a00140c058004020782d610840c20f44106a88829860845d89128040680061000d0000400144c81502030300c1d00130b18108485a0496038800c80e601601c810181d0890024054240c40c000d01504080d01582241c001d04200d4103140c04c1c0642842181d14184000074240c81c4201c11000f9034a41d4412204000a0082921965070712108043c20941080c3c1c0000c29500c41c0300300009080d880e0140401841210303003080c107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 149915143 1250 149913893 149913919
    0x23010507050d0b0d122c060a030209130f060e0a0212130f0206070807031205041e0206071505181513030203090405040308091218040908071505040209070509 69
    0x82d0081001214041e00130315a40d00c980c001c589034840741d1241c1c502594039400d6003203c020305410b1030a101005501344802c05541c12650307946000070b8a6160484d481c005031110311160004a2840c0656844506540760883c511000c0c0c2058205400395050890855881e44070400301c10100c0c401c030900340815801f80030200303003003e00c000245041140144801c00414082d500098603d9006501c200c4140e50001004801c140e0040241c0c02d41030b482c51400c000901c3d042e100c2641074a03030703c42c05800450340440f450045640c0d050079a211544c20035400b0301c400c010502c031400107020903200b0141b0544031284035001341000044005105000312005402c81d207400310807082c401c9801c070307044065020500c2407008949580c03040c2c0344504c3c0030340d44003404d60030030010890512800f0503103610118402c03c916441c08844004100e90800c080e03a00044040407410580000c0c014510020402ca0209603101c4040c0c1031a00101d0060740202d403401290384848000b41c1c0d0520408182d43c1d08801018603803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 149916393 1250 149915143 149915167
    0xb0a0b0403110a0f0e041208040c0512120708040609080313050402160213060f050d03141b0d0804050d0503060906040b03160f081c120f14042301050705 67
    0x38000034082c0840f14403a441c0d644a10303900c0802e03048100c801c0320407010007040c41002c2c03445501c0410316007001d001d24140364035640089011801100d01a481c03e41d400e1b0240401000304a800601b1000c40540706c00180c9840d40c1c140d4002c1c402d00000506c0d2420100f240c90010045a0501440030898000580307000d06101c069000308220000307001c0d0300a480320141c0c4440f0b44030414100003140015480b410000310146e80031058200c0350045400b0009100081e80015032014913042e5242c034a501d0714400d11040c1d10a07190841800c0190091904980029400c001150f00076031056050302d80b0408100703030485a40c00100c0e0001e9001c04030b03c011410504041d0300070002c0300350103002d540d4038015003216001005001d60050038401309c481000c0014a000341b103c07042008055080000c0e520031110010103540100d900c40003002e941b0700d1b080030340342d04a030300c031820800c106480000c891a1034203100d0115a800f00448030704002e0b94100006c02881803041d01d100308400d442c2ea909114400e620 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 149917643 1250 149916393 149916413
    0x60504061e030906020d0203040606060504120807060615020604060f1a0409021302210a0908091c06090305090f03120a18030503030109061505070201140309100f0f0b0a0b0403 77
    0x10440500d03030f44140f2a400700307000703000600c0c03442d00740c0c0005a50303418a460301900f1603200703500c40001c100301404144070f07a0f02441058903a50303421002032515180241007a0005200136130044601414a045a04003035801282140c451405100108132028490200c503040d03a4801c0d0b441c1607000b595a800010b940781561001c10624009010340c5c80c3d07007000c600711100302e03481803801c91b50700340c00045440382c031b400300c002c451b940556104000e010760401c82d5201220b03400b548800034416821400c9003500c40403101d203444801d51704030704188107081d41d86c2000b03082984401c50483c042d0541d090180c0311400c00159030b984400021903000d01d01552142c0c200d581d0b015620b10042008000c0400101003241000a1800380c014040d0024400345000800f4007400b4202c02c126090001c00c1c00300c01c000d40c0e009450061442400f03006550350f5030300e10803440e0910712000c03500c2c2c100c68074040018012400300c0d8010000f181214504200585100c8200500406103105600806a08101c1400043c1c040d060b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 149918893 1250 149917643 149917697
    0x101a060d020c160f050f060409020a050c1002030f0c0702030d0509010306080a060f06060c1a06011b030e0306060312091005090a08030a0912051e0f070b0903010606050406 75
    0x110060030540c066216904001d003003058041d5210a0f000d041c4481c0404640d090300415085410140425a5102151241c05107126216030030340d02041c2c40d0011030003082107480c1c0300079205c2583c90540311218020000c5d001601c00910841e02702c0d0010360003008600444200940041c02009110039500c02114158003210303249040544900000800840070802181d2461288a01140c0b4414550410003115040c0e4000c1b8100700804240c0740c041a1440c0003c040340c0c0900a003914559940001aa025005080307074040902c4200c8030b038002d06602c243c903603401000423010f40d9000c1e102c0074101903403404400e0200328100700800040c090743c94413030902011142e180c2030031401c1225950020302034202c5070303019001076080040c00e02107040c0d004500303402501d501401c032021082640c5610707a5a0300d082510700c00c0d08203076028a21420000300801c4030303c101003400700c55996844056070099034002140e060300a60801402207081401a800c0d103040d6030441d40d0b90325407200c07100c0c0d8030030f0050a00c0c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 149920143 1250 149918893 149918917
    0xf0403091206020c0c01080105060703030b04060e0f06010305070809070521030307080a110a05040b3f0903030103050604030c210905130905032b0905010b03101a06 72
    0x200c0e00107000c406021548207018015400180c6400c264403111342002900a0340504105110300140000d0341d580080c1c070030194041c03071300041c52401d11021070010840c0ba0030120201101030200050030b04d0449010303110301c0c801c2c0d070188020349072920f09917407800e420340ea0351045802000301400300c3e003480e0036219000340c1d03105210400302c0241d00756641954010390340c207000a003500c010801c0c482100d01680011400002c040c0b460a240c1800080039030090340034029a45d9000241400c0c00031040410003506002c4640c26804c1003c9254407845040032410742e00822000c100000c1c0b02c041d00402aa4100c0750000058416961190b5044840c1c2100c040119400e55450003100c4020a244d501c0e000d1400da180c8800c07802d58104020010905410202681e078507041026000008d0f00110941d40002100d03100d980310a4401d40c0600550f0b801940c1702c0e4a01427500c0c002d4418003074150400f8142c0c500560644a0f0145010102d4007603e0480004590304200d041980c101805c08900402003030fa010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 149921393 1250 149920143 149920157
    0xc2d0d0903021221130b040b060f030106090b04060504050103150b010215010801050f06030105090c091003050a0c03020f060f0702060d020d0e07080d030623180f010317070203060f0403 81
    0x45143e8441d180c10104038840000340550264161108950306031340c01207441c400400561809035500c2a1a013002030004110303181c8030000c56502e441d580910340900400070000d000f0251180304010041c501c403401103110350306012000500e400d00340b00d1a8140c1c0c2e040170303200300444036516426000d420141c10b894114440e60305c07100641d00540c01110301030000c480020841c0e05010321250641c0c0800f600c218820b03450a030a00c90084000241c2405040003590706115642d40c9608424805449500280140c02650000420040c038100103078140d034403c40da0100c02e0414641840340c2c03802450420000b0700c00820403d005032038810042e00c030801040101510301840210340d10103544002d510000164403c6109114460041c000e01d0644455840c0c1005041d280008042402080d9104c101c2580b0454004003000d03140c40d50781030303d03203148524003440310b04040c0d0004e00da40c04244029a420030026001c00317480100942280c84d843c0c0c00800500d072a031143d110311044200c000c0c0c4124103015107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 149922643 1250 149921393 149921413
    0x601030b01090506090a1a09010206011d15060435010c0f0c0c03021804110405100b0705070b0424050307050f09040f05070f0306050f01080f15090c2d0d090302 70
    0x45100243c003207d010b03404648800e41100068644841038001d00300906980c007101156042102d0b48aa02846443c164845002072001041b86e501c55500003a550300100a01090803d048208900002d001c0581c207800b0030031480c800740e08035802280c0640c0000d840140700e881d203078450003074816814082d00302440096138a42c002a9008207480340d06140000e100200000d02c28441c1d0800110402038906011616211a6241c5200c075280100c10b00802c0c0840c0c40c0d030510508001e0031020f044000e1410b075030b898071a4239041c0c2604081c0352555215030a0311481303c0082c0300d4003e403070107001c680d1102424044144152403a0b03422100409401030b55030326103010010402d005060003140d843d1111034040c05003801c000d0903030b81103812440c00f03403225450840103a644020500e500861026045030346880d9040000203042c10b01c0701c4150310a02050611000030010782c024100c45a41c000400c620780300c40040707200c0590140b405c0b100030b49024485c603803030307070980c3e801410b80203200e03205407119001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 149923893 1250 149922643 149922659
    0x40b0907080a150507030b0306060d03030f090f020307080102040303091203050c0a030323060f040504020315040803010e0a050f01090c0912061d21090a050907020d0201050601030b01090506090a 85
    0x810194156141400f10520000c0304150344a455000901480e0510542c00c0700f4001c02e59810002d08114001d001c51100072041c1840b0384e000c00c0040c000d800e000d00c90f0100034142080780101c13410050f481f030301890b14006142c6005108a4040769030544800072107a2030450f000c04d14201802c000e40a20804000140d06148140003144d0038901c283c03000100c030000c0c030046203040d2903410400000041c004e8244100d6644100c40001403100c01c98000ca00c940d52440844d0410302c52a140001c080780000611080000c1d03140507505a5100301d036118420794071402ca01c002c0c1e0380251200c184a881140044c044194180c01c0a0756004a07800c020308500d0b503d26445250030414035080c0d070700d182c0d240750040c0d204114181c81d4441c034111000074032008100b1807014060384c40402603107001c07060006d503203120341e1a8074070f0351001003400502583c0c13030b0304d042c03640a503c4441a0b500c01d001540b8020001c0c0041d8068428000605010394070000814100b1040c004158000140300798880e00d04200020080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 149925143 1250 149923893 149923903
    0xd030504180608070504091109040609080309030304060533060f0c030d150305071403010902060a08150a1203120b0301020a022415130b060a05040314030301050603040b090708 77
    0x8207201c500150240c9400101c0d0304102c010b03000f59100f241410002c81c080b03103800c20380e0140c5040c100c07030f120841d8403103242c880c00811010038000c0c01a440401084010711011000e548075a02419040c401980c8031641d0308400c1c19454860720320740c141d010b80c403140c1002001402d20000e42c054412441d08220824080e115004410750040369480000d000c03e121025009030341d41c1500c906a58081141035984450300d4a184d4080e405174220510700801203a5025001041c080c2d0300582450b5407074103000001800d944040722184034490440d2140062801d03d80f0a100403105a0640a0405200c07a035040f9000005100d9076400203403920042d0440c0d41c0c081c0300508911034144c00500003001c28440382d4283c00d1040f10807400d051404400c10100d504c0d0252495148501180d145484043c81e8400000a10300200001d4100d82d021502c8550690814010000d0704c0c0100c1a030318240507a94103480d96440240115500f00c0c5003400810001503003c0215604803010200740c0303100c152240c3d905442c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 149926393 1250 149925143 149925179
    0x8030a0c0e33070b0106050c0c100804030e030d0806060c01151d100803030a020903190c0f0506070519170a02010203070311090a0608070201090b0109020d050105060304110d030504 79
    0x455003140c0d0102a20480b010480ca44200705548241071000c0c1d030f1111210316030144107003c00d0010004104141030403d201e100442100200014941c200400004102c82c004544c12400b00f03660242561071854009003001c04c10440d13940b01c00b600d40c2c8a40621810b5000300c25082000d43d2244d402d5034200898050382409003140204213003000650302c6032009506406840144c5940c01c0c607e0601c40c000300803045a61107640030402699481914004c40d10349451050001402d940000e013030350400c82e6020440d822a81840708140d4015114410444180b144076001440c41d40004400702507012855080302e6850700810b81e503240c0502c10910141d11f6404849100b0040c0d5000040100c0e054140c0328000c0c015400450480c2804441c1020900340ca549010700b80504c0440350001e01024403d401c00f4200c190300c0039124940d542e6a0880e44003030741198004c4035065003000d0000c40c00741032400a484c45150004000f80c800f00e0a1020700504017265502581000400c11002c188542c48890003220 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 149927643 1250 149926393 149926429
    0xb0d12050c030301080f0c060a23072310151802040e0406150905010501020a0308040816030201090c0b120a09081209031e030c180f0d05070602120708030a0c0e 70
    0x3004803080c01b041d00341f180e40d4100501c00d0009000050685503c680f607000d0f40ea0040c01c004007619040c0030081650b000d1304800801964800755600703610411420980d0001d0780f100c00725081204400b40180594600c10000702d0340c6848420200400850548803882440e03103202c0061415451ba072030b445210104071410f88003151a1666984091a0802c2e118014404030108108950420f00000e4850441d080003400700440d00b40801c0600c118a0301f243c20b02c1900701800c4500c11420314010303010b441e02450a403840c03007400d43e00248440c0180115120641c8515440c0070300d41c0c0b1401940002d1681c0441501d101d502400b001d14070515100c01c2a008000450085403500380e60000650008108808a1b00c420b00600c180402e800c500ac1c1514049000d104649900c3c204de80007240090440540712517020002c500880c050200102d00c140a843c801d90a0b034003800100c07030111144e445910001480a60b0401c001065030b201540840408500c1d450182c0100162030009890b21503102d20b0400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 149928893 1250 149927643 149927653
    0x1703090619060f05190f12060e0c0312130302060301031a060f01050a052b051006020601080c04020c1609020a17060307090b0111010507030506090105040b0d12050c03030108 76
    0x7a4440510800d00820284601480b0342410a070038070b088400c0d41d10443d40079942e81041a480c010b400c0c007403200500b41310349039102c05a947e0940340180303020003402a40c616242944508980502082900c00c0640160082040ba0703010001406a5405044d4402c0e1951050301d02200584d200c00045000754010880c601026076802c07400c5404980217420307140b04e00110341c1956290b903040f000f40c503070740a00c0741441512501d22a40c2c00703095206000c003544100001c0340c085c1006820a072302c480c0c0140c410101100c4003a0715070800707076541c03a000c0c0120b1213641e0003d03500d401301c0e2415070001c0000c01814011b0710800b46914800c800341880036045000f40e01c1e000702d003442d10150304c03d41c4854410800c0b4220702c414100000401d4454405004d5030700c1c515111304404003280d01540b024410b20304000020000e40c40c04020050044c2002c0d0b603880d1045d17146400009051a260080040210000b0400105503c0d582c0c1c8103050900344101110500c40c1c14400d10340c0d00c020a0016500070b01c0160068a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 149930143 1250 149928893 149928901
    0x1806020c0a05010203070c030b22140f0706020303060603040606090507030c08131112010e1510060c0b18121201080111070b0a0f02070b15090a11120417030906 70
    0x10710351441e402040c1154400d01886000c1101c03003060404403604000d01d05131075180c0c18001480c07288000100d04004581018271801c0142004070b45400d8a407080a5601903c00620b02c60740703410f014801c400c0103901c1440402c5003031600e0b000864110f4451000000c1d4140d484c6030150a4800444142c0007203503550040c1ca00403504040060390000600c40402c152a030103941c0e40442c1106500c4550180c2c08030344c08000200310961140300e41c040c194040f1410103401760140040c000701210100c0340780c0c0140c00001a001c0c0034800700d40000d54040303a0701101c0c0d81d400d000600c6071021108103043c80e20802c3c0702c654440e40d00000601a2032100d0b1150f59466040c580c04500391034001d0260354018500700010740118819440c4281c10640d40000030400d840c0d500c0f13010019014101018002c007051405004030061240517a2402d020203861515003680d4410340901158955080081d81c4101001071902d0400700d1100389610901c81c1d80c425007024001240710440750002c4075012440c2c4d01c000144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 149931393 1250 149930143 149930149
    0x6020a111c1514010503120d0b030a15061d1302010c02090106231306050703050f04090204170d120b0a09020a03200702030a150e150106270b0a1806020c 67
    0x80315038602015503c0d552612001c00d81e1802043c5030149402008191352010791a00e400465071090004c0c200d900300a604e04100ba4036505035611a44030900e400d2002429142804200c10702540f031048074152507959074011500e400051404034104144208a0b8005a4500486501a1a5590324034203804440e086003081d24090705035058401c2c0b0140501442191203045240945000345130040d200d064074942079801e4003071111413940101d404034001c11008180e9000e4000c41721412480c00c5481100c10b03d4036240d0003e8804000080c071420318681c114501a0040d43d82010042c12072540e495507021900101e800c45400c15000944a07550b000b03014040c100c0c41c5002c0c04113142c00318544243c99001956410b00340d40014032070170344441c0160b1010100d45c000c4003e0041c030020b60340100142c11519200e06001d02035000400c0d40c0100300d03112240c0740107406010284a2480124090038001e44400d950081d90070501048080301c2090b04032604010101d00409140d002840c5e030740c811200b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 149932643 1250 149931393 149931401
    0x50a0203100602161716030303090201030b010302070b1f030212030703030c050a02062a0c0607020106140d020607020f270703020c030a0c02040e03210109020406020a111c15 76
    0xc080119448014100d504c001c0364140b22040f200c0e0f1a641d0f1001c071009912150508011600b50700b025545041d0000501d60182c00c050080351003640c1c20059010351a006400301e001da084050305101c6000700185444030401040c15500c0444010700100d160f903940000e803662410508812640c00c08101c100402d81c05000d41c2c8801c0d046410582e08058038104001e41d107810042c01d185550480f1070910880700d0020019120b414206510903540c2d11040700429070b1200c06960b0040150711303050002030004030324a881101850001e0041c2d84990040c1c08200081d00818416648a02e290740310a0540c0e640510407080703840116031030b05044c82081d4103c1d00c221401880b01041c9401007040e44c2100c0d4010088905140050070002020021070000c10000c001c4001d80200710312002a03003c82400760700c0341d40c5490310310003803d146c2c560b81c8404856040e030050b40704007000b690001390390703100007248031081d40d48070140900400d0701c41a0001e02c00c502e41107550020b89510000502e0314140e0401405 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 149933893 1250 149932643 149932649
    0x10e01110d0e03150712051510020a03090501030513020409020f0a0e0403030506010503070c02120703080d060810021222060609020a08090601060806270903031e040f14010906050a020310 82
    0x513540040d481c00507005031a40c80d100169100703030341c0d8500c005889030204034000702d0f207070388041c2c100e9131140c4184202940c1d83c40c080b07a003075001c40c15a0100143d198440e004962150b5149041640303503181507401d0001401c801c00080b6404440051005d80c3c9459508826004001d16880454182801c2c100a802c440019200e01c0c1045010030410203903a4100c3d03411404c0580c10750700302500308036603c0050304180e90394000900d40080090095002d114507000a010744031120207075581d0541c0e004101c400ca100342c0c0c151030200000c200029008100003000c5c8040407004001d0000e4020250b40c8480072110315810080d000341d8040307059007a50b43d001e0011071340003125400410040d418084d0240c10004010700e90f600c113290070046290303002514604464001805076460038241042c1009a0712600211440790f600e01d443e110b604044400343c02c0741c5008036084045880e80d1003442d00e40e0002d0702d0a9003010f100b559210701c00301000505521810b8030841e0501070040e01c0e41018804505a981254 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 149935143 1250 149933893 149933923
    0x906060816030c0803040b030f060d151a0a080d0e01050c0f010609050106110a06020901050c030c0a030f080c04050603040204060e100302090a09020a0e040201030e0d0c03022a010e01110d0e03 84
    0x2006c18000200c1d0042101d810188480556a042da40c02e8000303640307481c600c08014136100424400b42d441d14400e8012841c440c0d5189030380318580308005d086c03040030642841041881c0d80000c901f400c159002c3c02c0c10b00c82c1d0306010716109151003080000300349402d82050b81000103030340d100030401c00400e280c0f03e041d015080520744000c1205500e1525503030743c510704c0740141c41e0590000342070029a00803412955010749147c103803521075105140f0191a030790b0400c0305801080780d032030040b41464410141644240700c800702850415060100740070306070300020002c9030017558442001c1061542500f031107100d01304103141c0340905800e502c14414908006800b1341942820201c3e000016583d8407111025901050240b0000789c0d40c500048020340810304c03a07c0c60a004c0c090b999007a940d40700c03042d0010940a6000c41d03030900e40302e80d2030346140301203602801c105020207070b100c165940c81060108268041494a0088082100442400c00007022195004140919144c2e5150b007070600205501c66243c1d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 149936393 1250 149935143 149935147
    0x903170703020a020f030c0406030819080f1311040501080303090106050a140904020a0e0403050304030e0105070309060c0507091104030309120206031308040b0d0203071706010e040906060816030c0803 88
    0x66030300a0f540d070780400002407062260000c0c04495440802c031011406400a000348034813588c83c01e0081d01c83d40400c900b86e4101003959a080c2c13149003d1118a4002d0700fa002034148295260310100390070540c250002c07078000d01034902e074880310f0741c540c0034445c06014100003459490070828120f900315045544401d02811642c8801c2125402e00311400c00c20700c0c01a03414a441d030752184002022a1101e801c48681d012000c0148000e1540c8200914801c52190f1200c01603103c04000642d0280030b112002000a188403005000c028440d10507205010b20070350482d280c468803048548256118030a0b0a042d801012408005143c0c1c051800c6005107550040380b12601c0032074010540510005203000545901d00c10540204450081120001c1c01c4032800551195100f011303044c0a50700c02d9031504000f400010b083c581080724148864019801610744100000b990414003001d030103506029507405542c0c9000041a80d010300c85442d41c1882204107003801070661400008041d0545c000c0012036200f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 149937643 1250 149936393 149936407
    0x210e06160305090c030d140d0c020a0b0a0b0a06050742020f0306060f04080607391b030204050c030703060605040b0403021302040323190807060209150a090317 70
    0x407410712551b5489150130404161003900441642c455100b00c58015450402148047c40e400f007154031903940b00304071a850544415031780001b03031407087d0012681f011001004000590041c3c004192640c07041d21101c58112032003d12280c1c215100d410f1444c000240300300c203850000486240d04248003c8542142048040a050803660100408280c0504800a214541400718070300f41d5009052203c01c480441c030702244010200c80241084600180038440c6403a240489c0d101003402907181e00200c50005101c0d5140c42c1c191802042032070002c090300101c0400580c459016161203070303030ba090b00e00303969007480d0500070202d031081c0c0e0100c4204a13041c841840405034000413501141d0b012a046488c80143c085814002d00c02e80e032005042002d015840e10341400581c080030080344000083c2d800300042e2040003040d580c28900c000b002202c0802541c2c00040103035025210000d0068454901e24018241c910300551000120a01040700030a0800c1000f04003000e03800c003005441817003800d04032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 149938893 1250 149937643 149937649
    0x3150506070b06011215050409110a0f151103070209060103020f070c08061e010e1f080c01020c041e0e071203020a0606050d0f020909120414031c210e06160305090c 72
    0x30460087d54403075a00c4243c1c000138000030705c1825404010007468440388640c0c58900c1800d40322035200d94044010110012800140a60000340410400c4130145140070701a508100307510200400e094103156080c04080d02d6041140054014540701c1c26042c1d0907142881100f61806c440100304201920101c050201d002c1d8601c212541150008142c0c41001d8a0340b500e8200c40454108464440702c00c040000501c1080000e03404850a17001c1c1c00b6505510401c4040c40140c520940b4030040854072503203002c102c61480d602000e44d122100c1c0903a49495210f0b51201503400c400c210680c0143c3c011784e80da0f018092644903031801400700f00d81c40c0c035121503e0b9546142002c11204003911030003019001814810050008003080360390304040d20b03a550340391a00100300010b04041e40d802031050804001c0c00d1014014022818035240e02c40c4400c0a2010038440284075003003050043c02030701e40703001d8440b501003046014000c0c5d850b00c1e01403662521040d0004e08070b42c4018840c24080d4051501080251 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 149940143 1250 149938893 149938931
    0xe19050c131107030c120f020616020c09040b0712020313080c1608030316020102040f0b090d050a0605190203040201080c0a090308161406041203150506070b060112 72
    0x401c0d60140020300002001000a0103501c9804903110000941d903010164481c1030694814490405002c00c685036000848138500300d03002c1700000d40d01100c0440c801c0382c2c0604800e900d503111803045881600e4120007080c0c0301d40b0191811039803c15070710140b110640d0010403000e082c5660b18011030552070018940c0e00700a61007070300582130490010f5042d84c0c07a41c09001403480c090703180500f4140d1039510004507940754411208841102080307511000c603284103000700c0b0b007154406100c007102142020007000c420790180903000d40c031001e41401400010024041440d0b05402a4000989807411b10081092682060310f03c1c0741e2144104100401030303030048449a0024020103059454184400d001d0310308400e2900f0280244c04c000c509546a40030044448500611a0125503110340c6031000180d581c5905440040880c0b0200e0303c030440c1c9074402d51041c480d404041c0c640e005420b03501d60208070b00307500502090354100c46d1b11003002010758121108940341c00202504200d40b103055044400d0300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 149941393 1250 149940143 149940163
    0x60d0807060c050c060412030b0a080c0603250203250213201c0606020109050307030f0905090106030f050705030c1209121207030b0d080f0c0f100e1905 67
    0x3540e5155038103000984214143c8003c0d483c1d81088503d06e041600b00200c41c80e815003180d01c0000d0502c1c2d03075410103041c5001000119204403008080c00f600142c10441c16400c001c16500e0719500c01001d00c0451000700c0c4071240b1105198010b56075659155920b001e40310350305680964820920100080180c41d926141485608070040002d0b0240a43d50300040182041d00c004000180c081185000c80d0406055040da003452074008200003075a4150036800d9944c0c41d100980660400d000c076501180c080c40c0d241d1000c2e1140c0c94100466501e501c00103100e11020780014001071703074507007400400c0a000d108086d046641802d0003411840c11080c0700303803244111624141300c3c441c0c0c030000c503068440030400034134036104202c1c546c3d80342c02940e51102944241100d484c400281441c0035659039041c1000071001c0c158010720f101d0301c0d003481c4c0f10f0701094a0344498940b007242d218161101180f0b075428052800074a00100c00441e40c11505018a4900484121003039400b1041080000000d40c0000d0040e0309 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 149942643 1250 149941393 149941403
    0xb180619050709030c090b18010605030712060f0b030108100b09010909060204031713120f0609050c2e0918050603190c0603060b13030b18010207120305060d0807 71
    0x425680c2c07a104980f110718a6100070700b901200e100204250007140c109030032003003094542100942060040c039035019000e11810340401d50402c0410049480f078182c28081e89a4008080340040e50303880300c4400807483c0e5000c06900140070006100c0100107100244111542d0075041c81005404400281c40300c0b0b040c0304074603a141c1c0c0e8003001c1c002c008054054030010741d00050380300840540f01040a951b40c3c80007185518840255401007051554095503045090f00078021540c1d61509654010092215900956441c4107100350358025079180f0310b03640340182e03821400da03007a000d188594641e40c00b41521400d0034403c15100520602e5100c03400c65921100000c0041450307158100480d0414104c0603070300c2c1c3d42c4111840c1d100c040c00343e00d900e468101c9a1560f8104110f95880c00034500c180100020420f004c42480c8040001c00e41c044102e0b5003241e80410103001c1040850a0380342207a002d204100c540200408005580c0758062040c29071200c1c058a4410000641b99286081403140c0340300105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 149943893 1250 149942643 149942651
    0x304020f03240910050a060302180106090303120905010203090a0b011409041520090a0b07030c12030605060a0c02030120040312090f182d020708090d0b180619 70
    0x643c0e01d004208404941800d03403010842802c03d0171a100180c8154042a40520b0b0510184105451160900c078101e50300380d980c203080c003411a5000c0b1100c08000810410f0180c03102c1c986004140300b0320045002e000060004e0825120501d0903001818050344021b60440001d4040d9281d502c41c8a0758540c0654412840541142543e2411005011071004020f1540014051141d04240c98000300107141d011200310f4580f0356501201c1c0590300c45c20b04000e0000301801c0741d4400103072070050140c4208030300341000315196444101164441c1c000300c2018000602907003e4005504081c85011451203900c000100c107841240a00080703445a44401403640001800780c00f040f45c40750089202803c0c40c0031000c1c1344640e5640300b20701c800340c2c40e83d4001c00d03c9290900c8940c1c5145590000280040c160025440b000e00d0294680003e400c81a030689030303000100600303400ca645c2c801011036402e1140c0906600c0e4100b0300071a00c1e03011002c0d01d01d80582d0340104240800048406880b00c40e054078840301003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 149945143 1250 149943893 149943901
    0x60303090f0310060e0103150c05090d030201061a07140307030e06180919051003111002031c06080f0f100b010e0301060b0a0311090913020a030b0406020304020f0324 73
    0xe280584482003c116a0f16000c00800c0c0c040c2a80c071100d048a0140c03c0070400d0483c080d2004049a02d8141c0c1e40011902c1080780106c18200307100001c601c2402400005003075641d81000e00d0750001c00c900c081c403d804c4c00156070010055581c000014101c0000000d5080030056a07014090000d1881c8030381c4144d002060140380e07141400c00000d80501d0107041d4544c41d092000c0d40c0c1d00000d0005184020f01400c0c100010b40801e0410703c11811a0741182262084550400c00e000c440800c00c0003c4007140030070030045001041e0f0308400860402d181c200000d81e9803a0020150404102c3c05050a4581141000d104c00e40c4000400c0106030409420000d0858010b01c0103980d03511512144a4141d400c004001980d44481409040504841e84081c4510301e415004040b503840b6003a20f19501c00500c0004c140c0c001030082d0311814461014018295071b68407500d440c0400d4004803422205a0780000402c4118104a0020b0301c400500390010501a8202c0c004c002c03e50720340381107628130240c0c098001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 149946393 1250 149945143 149945149
    0x30e01110a08041506080309120c010212211e070f0c110406080d020f1908031f08030f07050c01050702030303040201030509011b09030b0601050a141303020a06030f0f05060303090f 79
    0x24113002da0600000c1040740c2e50f40c90b1464503900400901c41c8035600240d1221503409010900b070f070301d624050b0b024088106051861200c41d41191000c1035012010440f0003013170040000e8154058064242808020170f0020402510158000c0c800020000c50510b2084065041050803800c1980152070011065481001c90000c11a0394840d0085110352280740c0111500071803010f400461010544029902c80c490782c0d006442a0000108003003000c0000a1a00321007051107901c0c0d000b2014018211581d9a401d00d00d0b640020280c20800500003c0d1901008401c00c468060800203080060500e480d50700040d0300c83c0001480a03040c50b0701c410010304c3e84042903010500288810804800c5020707040e00081c200303406030204845038180381c40460b40780d600070020784400c400e03156241c024032185071208103070603000700c2504042c0001414001c8016aa20001d8501500b01560005a24030301c9006031419201c10711461041c4a00d420113024003900c0100807507410f400141c03819030a0410303803408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 149947643 1250 149946393 149946413
    0x306050c040608130510180606080c01020309040203090703080a05030f01060306210303200403050111090604030f0807020303030406051f0506090105071e0b041a090a0b0a0f0501090b01030e01110a0804 88
    0x520f0b44050301d02031501072071540347c80d0410710703550040c8000c004158945140039a43d007840700c225400f41c0d005010091301031031306070011503011031404140c51140b030f41c07983c9418460700031802c030a010071408020822211700c40c0d1949401462245030074003c040c50641c452060040441c1c05a40250000d0001028140240c010700030002041040203c600031403078000d4501d4200c0c0c0000c540341d50810b2400b4400c0174080c01075481444006020300d2815245a0b5400c505170002c0e00c0880d401c0c28240701140c0980e40a0000d544100d0240c0c00104403407070100300c4081e82c07112900c1e40c0d6081719081c44082c0a079840b00c0059454500007820420707503400320b17800d244807103400c0003140003a416660640c030f0301000405810640160300c80d08030b0040c0108480318014000ea0100c1d1000b031554031841e40240445c11000c1b8203504400c0c45100080d0b20001a0140020f4036026000350300c4031342d290b4200d54200d50385442030800b1030310303080000c11242e901400100281d01ca940004800c1003984004101800a4040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 149948893 1250 149947643 149947663
    0x130f020603391e19031e15050904020a030b0a050105040b030a030903080901021204120218010311040903050f030a05040302060c0f0f07021504031101090b1c0e070911040306050c0406081305 83
    0xa841980248404ca008010304601c0303040507042c01c64800710000a104a00468000e04c01020395400a54105010b01c00000e0b00100142c3c0d104038154000400b00e0070f00d0a440d4080e40a030900030070b0960604050109503143d5581c0103000e98840c90320321000c654003403030101c00d032a885524950784050800040380340c0213060b113003104480340000d0001149083c403038070400380d01d2003a2a4106840c048545440e0415403d22010301190300c5040c0f0064103140c15801080c245109040081c140000704862000941089136019041e0750b40b1001e10041c50740401401d98400c11440e8424034102419004501c680035003114403031609404203540d0215038554940e82e80c01c16a001c040ca840b2a1780e810110090303541365a9160109114107404205824024104c50072b070511508816030b0f002d2480b502400500251164041d94043c4d8000490011950701545983c2141c0f01880c03500c440c2582009811500042c00340e0940175001c010800403103030400da00303650100c80f240c0484450310040c00d0480c20040048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 149950143 1250 149948893 149948917
    0xa03030503060f0a08151e0709090c18080c090a05060102030706180503190806010507020d021c0606090f0506030303090601030209040c08120c010f06030506130f020603391e 76
    0x901c206c040100c05450042c412015008010041ca90207820f80004c804140c52000c000f88010038280046440c030303008030b001d01c8030741c1c900200c0800303a10b5003648540a4580188071150800b10f0003034658a0202d00443d040003405104000d1400c0c04400070f50b80c1d00c1905e10061032070740c40e0520fa2030305015040d40201d20356000000e403542c1d1201e1400041a00344000c0c1220b0200f0f4840d004986079501c9102501e8171580d01401410382040c10b5000c00480c90004030080300b044001a080e64009109405910010040014040b95083e502c407103003001e50780d0042c6441e001c1c0c0e200303000300040348000180d02811070390103445401035074030380d0304014a4680d055040341d00903101d40c404030004130302c045e0300801d0804a000020014107940d19071000580d03c0501c406816603010b9000b00e02c440658000d51030210303100300480c081ca4003095001c10000e400440710740080b1051280404c0c1d81c10f0400c0500b64540c1c0454220719150401404c0410f01405002058540c9881c4040c1d45034034503400307004403040f1038a0303c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 149951393 1250 149950143 149950153
    0xf0c1605030c010f0c020609060f0f0a090204061410050702090f0603250315090b01091a03010e100b090c0406030b010c1a09010c02010b0a03020d03030b15030a0501050a03030503060f0a08 82
    0x13031940c800351148070303503090051141720000340c070300c03140405c8540c05460461043c07440c41d04c0e94061000c4002d80509800a0155200b04400c01640c130741c4a03590042c256007090001c080035802c104003128142c141024140842040158016500c0009403580865882d0390300b01070f030b111980400d00c1d00e03240e4a00294182c0340360040810490724a0300749411280314582d12400f100000e4940c505880314594010045010200103101c000e0b0f4542000500300d07200156215207440900009082d5220400820001e4000c10403140d000621402200701c400c2080e1078840a504000210684a105501c9a04101541c03842c50b50181e070701c41e40d02c019506400ca5030301e0300400b040095400102009a426080941c60000c102003e02d006000c0c00c15201c00041c070030140c652840c0c0921489100c1810100c04142c1c0d106119109a0748500480120402868200d510380ca09051b550f400c0b248180c00082c400c000420080000a603ca0304490780070f8400d541000e07801b40c25074041070131850306411654482c014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 149952643 1250 149951393 149951411
    0x3040f02060301080109050c0103022a0f0a0311010e19080901050d1b080f010f0611030f160317010e0402240a0c0510051003080f130b120f0c1605030c01 67
    0x150001b0001034056025120801d00b580300560032807240c0007058840510100200c02345038249039147c81010503440944609584030103566041603070000b01200400d10301a03c40207696424440c05800007000001019400744101400c0d10000417000d0007004842c0c00a10f00d00340c0c5e4070810640d45042404c3d00184015590001c007584109044d4000d0750001360300c1000118044990340509048900c1190300d03a62150901c001140c040e503e0070380311841480100050b103403684918004000400070010401800340c8949070003007e805000c0c200c0021559144010700a0301c0100716510340181d4122103415100d00d4602e00b485208100150556041002281ca1000701e0b40180d00c1505286c401c030300b900d101400e040000012070b68152962042c6800b20070091000502450003440d801d400d01c1422800c00001604804d1a8505034000a0807540041100600a10b82407400c44e0044403071595402075140401102d030740743c000c44844031844d841300e0010b0030501c1010b0003203c400342c0c040d200038006511 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 149953893 1250 149952643 149952659
    0xc040212040b0a050417070809031605032a0d29070e040e060c0304030504030b010312030c111b010c0221070501090b0a030b0117070207060801050307120803040f02060301 75
    0x8201d0741607800c4881000010402d2205105081c80fa0307034020000a0b807040054405042038212110854140a04000301c0300955010850545c04141807c070340b00300c00b402c0c80300f418148203210700350b9010602c000b505070800c0c015682c00e407803403001c1c203807080302910046081410210220340404280c00c46000f0030003490308005c00100c0c0c03180b000c6450b1520507401150a02c0704458019a00c00600c0e0010004107102d806148021a0010f0003031803c24207254494488884a003001e0303104964229034843c07501e151982502640040740303000d08159048444102c18180c50b00040c503031160558500110480c0d1980c0214620340000360041d12000e0b24604000726062000a00c1004414511484030000307a1988185405015908101040f90a1071701305141980a0804400ea0a043c090203a0b11050000b54403e1103902ca501c107a8010841c0c9880d10601404192060704282d000e50000d04042c009128005482306000b1303031003c9180d0f030b80d43e2142850407950900f4603000790f0013140000000b40c0d0381 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 149955143 1250 149953893 149953927
    0x20d060501050102070b0a17040f1509031205010320062104140118150908030717091606050c0106050a030515060a0515070c03060507110715080f07020c0402 69
    0xb4420b800700d50003517480d80b95100c03241c010100000001070003c18005007a4100a401c1c03078020b841900c616070280c40543c1e03850f102c0744100c40404599507840442a0034180c1c00641c0240548800b14208215415501c1d10072501c005100a280d4840e03002d4a40c00c040d440d0a411961000402c50b040c85001015482c280405841501c00b0f580e068103000001c074800806108000450030b4179002019490403555070440c0e40d4540a802e900705d650760710040808100e4801c01544140c007030b039035407a01a0f801c5030707025000b00d140a80b1044041d40f00a402110000039002010180c4a190400035241d2100840c0d190140495810043e040000000e00004011000074072009080b0746c2d0400c0c075499a030300c000f44418442d80f842215440003d03120341804058070100140700300e13402a811000e50b01c0e260384074042a2001910307407100003211011090078040c01441988043c3c64111120b020445407403d000300b01c0c2101800d0f1703d0703140d1400030100d4030760b80c000c20281300d0703940c0050019500c3c3c0e141d000403d504c00f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 149956393 1250 149955143 149955149
    0xa230303030a09020f030318090406020403020306071728020702030c03070f0510050903030a0c1103120d0f02040b0a08071b050d0801050102030309151b040b030702190308010918020d060501 83
    0x701c0c402c4c102d10f00b0a20300401030b244440105a42000074451000c10002500d0020303209883c2f003a4200b001001584050142c85e01c40c601c02e468030a440c42c040f8209810a460081032640790f80504840310300709849440110b40c1c40e2107903400c00350f1549404d000013070404114500070707a80341c49802c0f0000f4822000985040440c1d4044a0090b072500703c40100b6610340c0b0402818a905400401c01c0098841c021308400c40401e0264048205254030b44010929100381c4500c0e030207807203d01285852781c08020303005000803019899829410286080804207083c0294071015040c441200d0000c2d400e584903d0062000080804070f6607894442800c0150710303a0403940c1100005680c800c00070540354000002caa0240c0001c030000e0a041d107140090f50406600680002070702c00441c0ea68036480c101204c068405030205243d178591343e041c10000a4a0440b2400d40d1004212208403c440801c1cac0180503030341110024100450400030102080da10713112414002540710584400c20b0f000d1200c6984583d0607 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 149957643 1250 149956393 149956399
    0x40e010f0b01031d0a02010f120c020c0f030c0108040204110c06070804030e0414160207091a091308070809010512040b0a0e0f0a1104110f03040516050a230303030a0902 74
    0x4208003485499880c13401d803c880250130b6120525010065108100c0c400d010380c2d00340340511127a60b41020701c40645003414030103401030380114070000c0c2e90b143c894240001100110004c2c01500c4030b101c00a441c060000340068400c0d541c07120704141e90710110044030441e220120039100c091a00d290082c246010545054001a484840350071043c20700344201098004403600c0207004d60307a405008035019800717410311400c5000c4d800000a41c3d048500aa203d17464248218000c2c8045d98070034402502002011581c800d8005800e500c0031414007402c481e0a55004826039035921003110068406100f604100306020714441c0030841401502e0b502c80d406500e241200b80280b110001403141e0310078180c03880c0d511a4001011040015070001d5014070307007090107400401e601c1907035400011150070445020214240001c204000c000c0144060703915170000345c3e601680f150408000c221070340614007400e5042c00c0304448041e1112100448041c00f150000e040325502d19081e10300c10054010564203c5c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 149958893 1250 149957643 149957651
    0x1203050f0126010e01110405090f0f01060c0804050901060905091b0a1d06030a02030709060903030e060903011d030c0c090f130c031502120105010f120209040e010f0b0103 75
    0x400c0c05004036440c101e031200c400c10b0a00080b008051101d26042080400311596a40000005442c0070b0140f800701c440c00d07241d0151120302c1c043c280403181d50000d2040c4031104049c010003116205100065064800c81d14010780d41e6040e52070300441500c038036048150b0262010000291595008900406640041c1d0341c042c01902c40c42040d8400340d00008403d41442014800790607240c0c0b0a070588588403600441c481c1c0480c0504001c2120ba510036101d01d01d000c0d400100f00240765030888a050010100d6281c06030200d480c40c0c0b03004003003802807444d41e0f00ca4040014848050b9609402621102c81c00001c44242050700314403199507540900103440341d0340901c41309039102d4602000010720448001c01c080c6d080e527859009030000c200c2007100859184000200110120795060b4818101030408007005a4940d40712414200d80d600c1684998100402d03241d0241c0c0490780044551a6107070045000743c0c48422100001f8060711003140f980310290300e08900d070042d10301c0781c1d0000b01a800702a24100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 149960143 1250 149958893 149958901
    0x80f0310060e0901060810170c01031d060a0c090503010f0902030c010f120903020307050a0b060102060c161401020d0908030a050f040203150403180e04031e0909091b03120305 77
    0x10b201104461200c66100180d140104042802006040c0d4800480c04801203015121600e000480c80200c0f5490144e50050996413a0355816120301e00124101f0651413001140448669503203010081c41840400c2e25108040c0c070490260183c48040c2c00014024403906200300c03480e000515000d44142c2c403038820044510055400780d4429010390100d40d0300d40048100c0540f016018000c2c5e00300440442c4030030450f00700440c500780041000288150b03030080c1c0070700306500024602140600044120241000190907084400744102c0d000ea07401415809041d4198641c40c0c024081c0120442c459402c00701c00c01d0070450000021032041404032010001c58543c009110018241141c000350164803003103c00c0d8810216020302580644245007601203110340704440310340d005840e408410340740c0d040c1040c8410590018403030800d1086050358615001c8640300c005000d6200da1040c0c0da141684e402d900d40a00451050040120015030f460824440d600c2c82d2a41d180704c1c00880503400a45040c001c0303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 149961393 1250 149960143 149960147
    0x904140105010f031109191d01050d110406150c06061712030a0207020d0f05010f0c020c1207030b040317010b0408030a03020f0706060f090c020610170a080f031006 72
    0x1a60503180c040c2e5941c0c0780300000160a03401021018669039103c5c2e0140f24030189603884690714140c0340300009041440910700300710260302c140042c070718800000715280107222703c0d00e0304007080794002d409c00045101020f001020400400780da400c0001015032160b07003c10b0180c0c0008003940902d120780010404180e030f4804a84600319103142c640140c0e00034ad01d040702c2c010b040e10051904681d686600528041282c1c0c001002c0e414903140031a07074020b002c0c49035414440c0a200703055a08203049002c2c0004140008025240c0e1280840d0301d1117446a00c0c02c0b5424403104004080140d075018808080e40d0500e400c002d0261540c0f0001141591042c200200321442607805035003c4615a0009500341101c104007500070b50025800c0c441380520a210324001b00301c01d40900e0005000c06201c0461503030070005080f01b40d842d0020040c0a42d4420420303c000040101604000c4540320140d00012601442c02d080c2404084600034002070320110350001c480c0004e00c02580205804640c0c1c0448550321001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 149962643 1250 149961393 149961431
    0x30f0e120606102706080903070308010302130227030606060408060a0c111c1211040512031c0e1014070e03100e07050f0a0e190209150904 61
    0x200540d81d0000c00201e0304038140120b48814400140c1002c6014030101d0305005008100c1030b4024903502d114a004110058001b020035030890300d46400303035181c031050341c40c007030065181840020702662102002d22601081c550550760800d210ba03203c0d000d198188560420b800c00c070114050312034020706002c280c0c24a00300d011901101d42c1440542020b68130840c844005120300f1020301c0a110600c800040ca002e41841000f481000030002500c510b00c422400820100c603040e05090018680209605400015010349044500403150142030f40e0300810228194000d20450700c407140398819082c03454254903000a510f1403c1c2404903940300d13940070301c0b100c06c0e200f4825014181803600404100110b108500484460303074060b08854080e1603208011003151200082070405030080d0744140424504070b00d12844801080f82e00c40059400c10303180061604010303007098411201c41d0540003058500b43c054440b10a001414003003031030b404141c110140c0c1d100e031003428465890620080c01c540d800c680 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 149963893 1250 149962643 149962669
    0x1090602100f11030c0705010f110d0b13050c03090f010203040f02040b0d05030406170903090a181811040c030c1b05070b0a0306030c0b040501020c210a030f0e 70
    0x300030400c035540d00c91007000400c4070300c8000e5581d649541c0400140703a0800b00844c09410b0304c12a240c1d903a040c5080c85400c6900d50420400e5403400c05010800fa00000c0e402e59200e8040401d00264408101e80040e80c0e51030485038210080e41040100405c82034410302441c0700342a000e0503a036a200c4070011190807480304940c000c180d05c1841606402505003036002d040200703400380114900002c076445041c0785800c0350b8040360003d0400031303030b000c410704d0032420481c2c220313481c03800840c2088a2036001510402c0035010703000c650088244000d8001c074050704041d421200d00c0c82c00c100c03845001c0c102030205074212000030340564104003150f420103100340700b40001c1d0700041d41d40d1400721031002d88a01c541d04c20039200f5034541c41101e00215040b020f0030018800d0f11096280019507918524021800040c1513000800500d424081002280d8001c03035240300c1901c04441071000700c81d419540140303285140000810b9440340000050401d41c000000701260f09143d128484d491021b07400308182d28280f00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 149965143 1250 149963893 149963897
    0xf0f06040213050601050c060c03011401232a0304060f0c1a07181706090a0302070506130801020a0e1201020c0c1309140d030606050a021b031002160c05010906 70
    0x40032140b0261a840250041414900a490803003803a54240c50100103990003104101c0000c01040b00e50200d00b03103421614828246507100c15000d0700a0780e6081101002459514800111200656800c44024a45100c851560070310740704c2d00c01c4029580e40141c0a071801040c0c4020100310041e01840c141d4102c41c6c1e01c243c1c02000403c46144204c03c1e000064841818800c2c501441c1514a083c40d40020203407501e1203040001c0e40710404401d182c800080d004900030b0700111000c1000c02d40c04240390080c2d401c1611081c0d9030b10010402404500450f0b0300500702540302041c0d010714282e119041a103040c00407203882d5850480805110300b01e20448104070087e90014080d1049400d181e07583e5141080820000541c6100703030345a507440100c0c8004000d01640007958413401460300f5119090240c2010f1401c18144010f1800280d40d848440b80c1510640080404d03d140f076a508101b602801641550305540b40d880348030340e201c3d0030309022500b100c07485000d500103d619442504000304442c07190b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 149966393 1250 149965143 149965159
    0x201050a060506090d020f040212040215070308130206090409050d0305012c0408090301060f0305060903070b04020d02130c0c110301051e090c040606050a030b01020d050405060c071203020f0f060402 87
    0x19070410400a2608900302d804c2000702d0004040340e562403000e413458404c2b080070b96480780b40c0f80c41007100250480404d816100c0045c80b00030003180c0c1c410032a40d407000304015901c0350804a1300010341a4040c056400b40d100d81081c43c0c0d4002c0104c0801c00b58071184103510b091225980382c01d0f00c000c400d003540c0011908404e81011000d06101006050b42d005070103105102c3c0b4001d0080c0129007500c615421074024500b511004004005007082804e60102c040d030040d50034076a4035951000000d001a001030300c110b440d81d6603c070540d501c2a0034000b22414115081104241551015107003130064202031300d1400303414410503071604041c0210791040070500c0380d041d100017140780e88035130700000913020701042c0c450825441e155464078840c4c08040c02003512629110050050001d094070700c7e800850781190400c5507001d034103d8000c1c080d1025510100c0719152107050100e0302610f00042030f4030001c400c85031a010380042c140c010880c9941042c100d815203440350782051810340d03201000d4900079001601 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 149967643 1250 149966393 149966407
    0x18030203031806070f0812010f030b04060902210706020f0106150807020a0b0403030504020f061303030305130b1003020a0e0f011401031b09090b041107060510080d0503070201050a060506 82
    0x4290b07071001000200412082c01d000c40c649034400c1240a480d000c03512180001804d00d031120500601e2030040c034140500c0f1007084d042d035803120b0380114090401420607494651070700840d5039691500b0390701e500e000a02550078040b0080c07141d54070f8182c401c000c00350007400c0aa141510040c05500f050f6184400c4107404803123240300072580000300810750740071405200b00c0240012400142d0030b00aa01aa0b0085001e040500401812502480d103440c4100b01c02c01040c01500c080c0e030706031002c59826081c00202a514514107240f40800644002d120b02e840703208220041d4542d0180314280c900a40f0006201c40e1210202c034607540060b60a862042e081d00300402000b80c1882c600c0c4004a010b240100320010380802403555501c4100707118000c15141c01d424040b441c0144120740351000c04450500661614080090041c03080d620041c10380c0d40c8410010300d5444005042400a0000340122081c4040404c801451608180d0750741c4015420b203004900c00102c9401500151180107202e2032600311 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 149968893 1250 149967643 149967667
    0x41e05060f060a0f030506090705040c020604030f031806020c010b09072a0c08060604110414010c0f050f0a030201150b030105060319020c030702030f03030f06060a0306050d03050a1803020303 84
    0x1c08443d801220003102040410b41c1d6504d03040214881d000030110382c05d04028941c1844055089180a10314185440c2c060303d50014203560416018103200d4080b010101086000d4009240170103150b2480e01e81100800100350f00420f01c0480c1040200038419102081281c40306095568400050305003d04400f42c400c440c52000c1d82c105030109401c01d554241c8e035082c0ba03001b0795174400412078201c4400c121030f5007040c0c091851400e8244226919290403c240004074055130780d40a03042140c4240303240d0410072941000d80d0480e0b0007074103c0301e02e06000780038542c0c1c5030031480d0210300650a0005400d85218400c1c552415103010b120050b04503030a00040c0545904000d04000141e1004111551050704a2000b040300c001d0400c00b8542d2030f041c5006144c07514044d000031040580c0108100000d0780c40807804c0e10b170055011101180c0d01c050448041303020f0403041d04090341c0069000608004c05070454000c090004113034840040c0341c000d040300d41051050074072019402d6001004001c0d403000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 149970143 1250 149968893 149968921
    0x20714030d110115030311060714040b090f030106030605010f0b0301060c030e03010b1009061d0a1a0d061d070c150203101d01060201140c090f150c06041e0506 70
    0x80c00c2d20000086150000c1c5910f00380c071050382c3c41500030414610103001030030f0040c0a05030b845030040c00d04103024024001021414840e81c4100f460100e070111310a60b50f0740e1a102c403c004110004c00a200d0141c490a111006110a10501c0c8040c9255000001c0c00c030200010f8a04a9509495210060506840607176010315003948055155690f9007034007190759140004502040780c140c0e00c03850014203052018040c84441d44804515245c24200e0580c1607640010f08001c3ea0707408043c0d14503500d0540e141011074064408a40c07502400c10703001250070444003a6000e00b11203c0c0c8221510390b11400c409940541c81c0610141c084261007420100c060303c1e540041d504007910501420385681d031015510f444c10b420780040000310f04030b8801040101d03424042c0e55030240008804008a0401c0c0d0607843c007a10801450601415420140702c01541e1800c1070301c1c00003003850003c96580c80e50521940d1301c0d014100d40803525800d10214030070800d07110107818015030307611030000d01c002d4a03072000a428403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 149971393 1250 149970143 149970167
    0x305040e0c0706020a0809010f09050604080901090b04090911040501060c0f080903010627050c04060f02120c1e01021e07080705030c03040906080309010c1203111603020714030d 78
    0x216400b042440001100c03071000b00407902140d5100310072030074078294a60070b58500303125246005060035544c102251020a1107600240d000c5d50240c2d5807013056006907648038071a80048003030900400c0000341141d0355000683d41910079601441001459010041110028002c0c3e1002031410401080001c6491a0310000c3c50302a901440c01c040700c45002070300f520000e401102d0700191020006801c501d0484010326540411007040c8540e02d00b031151028030380a030b0301c03400c0100145201c40d41d00d907034006d100c142e184100c2e543c0352075520188088219135071040440100d2540030b90010b100540c10040c800c1e500d40206084500031501140c0024640d29082100c055130115020058400001d00400c01042140c0d01c02000d19103481c40c0683d400110b405640c0003090350b030401c000c80b401e1b1b41e91101404130300550004c0c80c0c0030b5510400070120001c01c00252140c030b40ca040014443c000d1481d094024503036501c00d40c2100e581c42c2e11007043d1112064221041901f507401f00455940031800b40e840c1e0941 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 149972643 1250 149971393 149971411
    0x90405010603240b04021809130605010e040b090705100f0302120708041208090d030c020c130213060e0303090d0f060207060510051e04151e050316030305040e 70
    0x441e91242c0310103044400d0140c51003c0341105032800c4803080c1003401003018240007200c00310306101408803c0070300c1a8085a2080c41600090005001816001324404500d900010b0800040da1a00d001c848220b400350340c1a10210315100008000160002d16607044c0d900c0901025a0b10000000503122100941e80c14070515400340b00b004c120428080081c0d1080319203070789545084c2020300300200f60b9910141403c007041070100402050010000d5041c883c010286030005a010300050101d080442001803143d020442c80c4d00310290029a4014116001d041004250b0441d903030841500c0680b64000f405405800034000e440261620403a00b0b00301c01c0c0520842c1c2107007a0385958203012a80a14000c41d111642d910034041c19050b4580d250000d05010703100400110662a500703011880c03004081807240e03840300e00d0322a10040e0995010014407034512030003001c24144002d07400b03000d84d0b07000b19400391041807241c5075046800300c405c230100c035010703104d0328946800d0109090040c4001040424 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 149973893 1250 149972643 149972651
    0xd050934080f0a0201110312010302060f040305031c0b04180f051c0210060f0e0f091c080a0b030a0807030305060613140a051212070f020a030c290909040501 69
    0x14016010b109032410040100054a100d040c540b0014104035a4860b280c0d0859200744090744140310350141d072030306680c2c040300c0c101d8441800403141105481280c00003080ca00011504544000742d4500c610000342c0c0302841030150030380d04010301017110510780d95240c007001d20425400100c3c001d0361010080030701035001d03511412581c038078040b02c441050f14487d00507840405a000110340318802e10b4040c009800d58044407600d0980800174908000e840110904001004581c440004108080c08820701141d03683c2c1c0142c5070b03080600398080c11283d614000e420001c400180b4036000c07401c8082c00b81e00074805805d10300c254408400a0100926280d0004810800d88114084800e5603800800070349070400c90140041c0c3c00c1c455408155071007240507407450210310b4501000802d858004d081110342c032948031856401d040401c003089a80107500001016004030501c000c07041107800355400904c1c0c001100181d00808141c800c40400404040042400b1030780c028039000400303580180c0a500003003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 149975143 1250 149973893 149973899
    0x60f0409140a0f050f030f0a1d1507060b06030103121101060b0d0c113409061707080f030d0c200102130602011b030c050706060b0d050934 61
    0x1403401030000b800355080140004a202000010807110740d2460401c0041c504011024500220340e00800d01c440050101a03400101d04030305a281008500e000106006591030400070802c00030740c020a010781d1070600b1306040207807504011040324101c130741c0031940200c5042c6941c012075505502c0f091211141d502c0e0240002c1c1280d5a10141005c000d03403d20010f1200f01000c0050844141e11840101c550018923101c110703034242040c13a0801c00d200c180409004080005064107070800d580100c0451441e00b41d001c80c1008101c4c1c00451401d15034011100e08907280d060080c0da07a110049064080e41c0b01308048004640190000b00b1407502c039050000050900c00a002d0003440300201000c0181c4d070110300082020410010100100394038002040340424418a0300010b02c503041c0c52106058444d5010f2680720305c40d01c1101c48003030b0403007070412290381c481c1c014034995401015446a000c0c20080800c003e0741d40401c2c642c1c11181260206082d940c070030002000001c00c0c14940b002001b0440e8800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 149976393 1250 149975143 149975183
    0x301080a0303022125080403120f060e010902220b0f0901091203020606100e090406050702070302031024050f01030b19061e03050c1b0a0602040b030604050906060f0409 74
    0x9a0007200c4450803240d840c03552913803c3c003840900005170000c000f5514280310100717400140e02c1140c01c2c1c00d0880890001000400500a00006e50140a610301c100c0700000d10400907502401d85009407210342e01c200c1c958600410005c074040e0060212a07a0104440100e800218004020540041c10a00f03015560346504052420101400368050307044803041051a00e0030030251840ca4030341d410030f880c80001c84404a040c05800802c01044255500b010884041c004c204031802954001c0840d0710410886455130302500550740710b4010740300115900500e6001d0180c240b030544070090802400442484011001381c404c52101e150007c40721140b00c1500203035a05900098010b0740c07a850f0754901c1000d030010503818542569820580f501d014080e0b171301c1c181021614002040207034100c400109a02480c01c0943d1700304001c00c0305100003400100c442001d00036611400085a081100e17545410449840d04001c941903548004260b1008501340385c20341c042401307603010340b200740d150162061704 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 149977643 1250 149976393 149976457
    0xc0c04021b011508030d0e0a080a0c0b01050f0f01050706090b1006080603011104060804170d0608011805102c0328090302010c150609060504110301080a030302 70
    0x84011103810075540c0e9030008209000c0c90b25921600310b4060300207842c107184c2c26124003960031680c24003902d8015406500f842041203061041e00000314130707690741c0c18840c007034204200c04800311141d41c0c10744000161460081d0328100c421202902c540502a140b600440d01b9a1041104940d020356a00c60080801e10203e102407040045c03120017035000381050b80103001124001c02c1c59102ea030420070340d8001200740a084d034003154840d08120032030352161b01c0c0254000003640a1001700c01070202d0781c082d02c01c200b50070810869032100000c00000380d400b00c449141100359800504079034442c800300302020354103a02034504412001da0720002d4541d4071800440d554009040d41402d5030000c600815040810741240c03c4122403c004589003a0354424060401041d500c00a0f041c4040d0740d02c1501800300c42c500e90041c6501c041802c0004907200e1418100824142c0210ba000d1490b01e01c0c111007125111046070706843c4690f0080004440980d0214007942c40840b01181a00704080c0104da20700c3c0f4000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 149978893 1250 149977643 149977657
    0x50a1209060b03070909151518060f140108070f090b0f0307080c041802070206091c0b060a08060c0f041a070b1605091302191124010b0c0c0402 63
    0xa008660b50000404043c60b000b10f079040801c215142203810400621581d00c1858401a100c07008607144070b1891440701c800170f00d07601c062140c5104011402061318103600020aa541c01d0f90f04c2504191652080c0d0144092221007034045610756001c0b840709030140c1c800d0241c14a152600740c0b0000d07158010072100f6001030714035442c0341d0000700c140003143d508046201d50009405110a050514000030001d0b4001c25005501d526640000d006c415515a0422607210b010302415503402e04840f424050390943c3c0350b050586804500c040854403500d421904542154100c100809143c1c48540e20121705501060080c92254010000025690b10340003010b44058024800ca44e00c513225424541c00010004000402c0700f0080b241d280462034005064404800007540c41c07092641c01c85044100a02c01c0c20242504905110980711890794000805081e64100400340d81c030000302c2d0180790304215045904881346444c0c00d001800420824000350030a440c9072001c0702d400728015000f1504a0340624 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 149980143 1250 149978893 149978903
    0x13151a060f0c06090a030507030f050405150705010b0906010f031a10090e0a0204050607030503070903050106080c01020c04050f0415111209191716020301062402150403050a1209 78
    0x100b41410088014028158440000030240aa4100c9941d00400034030421030000c040c04426000001207a20800544014100140103c3c810f007480c41d41c00f807410303007001d00c04a41c0ca40c00d15000ba0000d050604030580500010303100c0b8290120a840250003038400003030300c0d0744c40c400d55400500190f600d580c0381c3c000340a0907444480f003850807c4001e5804034002040d00000301d00410003006643c80302800c90384550380518200781c6039240e0032021a01119150b002070081d60030000b000c00c0281c0c0100e030b1031075006000d808030390000f5420001d0006583e000c540c400345248558000601161150300d074151740c00105240041c002c0c9030100c005981d500301010081150f9a85010001e80d000100101e0340410391010051810800d00da480d80304508411886403140000810149a1348ea0714000c880030031b6600078000c0c02259160030160345003c00311280740342075424140740d115905002180341607104100042a0125a81c0c980342a03850742d0110040303004003c0401d8011200c40070720321031035095610170 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 149981393 1250 149980143 149980147
    0xf0606030c0f03120807031b11070603060b070f02060c0d03090c051f11010f061e050607050706080705090913051c120b01030213090f0513151a060f 65
    0x60400c0d0702802540d82192100005404040c00412198414111640740c0d42c40c004950342e407450011400303401100403907503400e00040d00c0c40e201c094000d41500240300c1040c0c22558901e5a4020440907520244070b1940c00c01d03002c200c0c0c032007c43c8000f241c0d0b21a0b1400602040d2821040070b80983c6071030800040c40d0f000030f0380d502c84001084039400d0741000424084800c0101720302d204200a681d00c5504074403c05120070740e802ca5000c04001e400ca500380c0e541b00031081042c1559000c041c0c05920140260352040d0381ca0000202e05403400304240d0740915005002007034110b080840c10740305000003900d01d106000c01840848810b41e22002034030312514081c3d00e0f0070409105850802d2410308007000300342500c5040c1d0459910035500800007880c1c00c0180320301082c8c40750100d006900900c42c03030840012040d10400d01140010103500414050210100d040000d40e440c41c007901604580c0b0700000701003245441c61918101da02e0740042803038400701c13000c266103903c0c14000603145d070703012803c0080c0d4000c1c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 149982643 1250 149981393 149981399
    0x50106080706030209012f01020408030d061a030a0b15190f020705012a140a03020c010c030c06021c0222050d050718020906030a0207140d0905040b0103090f0606 71
    0x309100400042150f0b040c25070400d03101c40000307420744284100c1c0c1f1100c0505440074150103c1d0002d01100707080300940c002c5580d03603112165aa1a58800e01c03040c4a11400d042000860529034101c011452400348401c60135034407482042c45c06851080310260f03200404c40c0d010880e03424004020074400304016256000f10bc40c40c6030107001501110009810764220440800050b6000311000c0048040c90081e000c031084200b03245880d58905040103443c11200d24903402e480400060500744007400f075001c41d8140c14400f4011a403a191120b0024009007856010b0400588960094806802c149011485408041550300200e0b0840d0030014505e40042c800c03120550101e8202501600040d500c0e00600d8005496555607100c2c180300c1d800c0410750986214515030425410b40b0360080000b080140d80f03003008800300c00a0b4000e03440999807184458031001e07002c00c0010351001c40400d161241000d2900e0301080100030503120646505054a4403507110005910300342d00350060303120303000005110341 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 149983893 1250 149982643 149982659
    0xa020a1205210606030601051b010c0801031a15091801090b061311090910030f03020d0305070e0d02040e01110409020711010f02120a0c0203060406140a09170c010216050106 76
    0x162a40700740a035207003104184420b940710202120751265088c00d040380d40303c0d8242040c0c00c040e044d161245401e540303003c00540080da401861141203034000c07009811010103a440d101201c0740c0503903c12012000c0017690a0316401e0a440441e4001c6000c2c1c00c1c0d4110740c00486110b0b0035292440c2c400c440c90038500301004400d20b005408006800b5002504212010000c00d162500d4481e40c2d0441d44034091402c0017907000101c0c02000400346d58400500e4a0881c01d51501940d9a800007800c0c0c03000c241000d002820081c8980301444050300020301c2601c0340d4000e9001e01000344040001000695207a09020840d8503c070401803006040c092030040e5624500d04040c031550803941407a07810800c0454400000da40e0009900810514542c0899900e8016050944101d074014400a400d0700464080100b48026a80b02010584141d01c07000300c1669143e0f0203c0454038007880081c0644424070b14a01160074803805458443d010b41d0005181400801c403407441c00c03140c00c008076041d1b91070305810b0150300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 149985143 1250 149983893 149983927
    0x90e0106020309030303011206110a090305010f05091905010609020f04080f0601060f080a02040f030b060306090d0507060f06120c18051003080a090506031806060a050d080a020a1205 80
    0x110692002c2c5007410002800242c8038401071081440001901c560300c014418958880800740e2042d450071030ba6404101d8000d45141c000d44019a455480c01058013146030070f5001d0b0350301c0f4a810a0180c010b0390003486d420031b00c8071043e44090307405640c0c0d60f4010940c60002c0c4000c2030f0342486422a95142c502d003200c81454111140c40c2200b82d034202c200100030a58008001040000303070350601c440c5c02e982c3c8106203030007401198441004403842910010600040c00100d600074103080e01079030425611070341d01550ba0a5a000d44030f0025204205100c0400d20300c0d070101c0d000510105012481940d10303c2071001d99a10b0f540155440c20100f0001c01c583c15040010120142081500384007900c1e00200d02241d1441621002d400218005180c03a0203600c100071020191800400140d180d041c003900111080c04807034011480d0307118400100b599440c00c41d80c10411210004d0540880d440d080e520a102d1350000c240c0071096226607407544c1d00044d40d881c81000c0c548001c2e07940da42c0301c02208001034401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 149986393 1250 149985143 149985149
    0x40e07032303040b0a0201181112010603120c0201091203021e0d2a0605040b01050f0402030402090a0914060c1309051510200c18070c06091a07090e01 66
    0x7610540c50101c0384880842924102c8112440c0136444402850f070503030245c0208640141c1d07070b8040f5004c1104014401c80d039076a900d03205485800c904000119190708a0740c0c2400040c00600c0c45a900002880c8103070300f84021140b040c900702e000c8a94a00b40c1d030300d0b107480b000b5040f80035811047c3c0070241c401819603000f8101c00c01c0002010480d0302d100f000786c441401c2104204080c0d0400201900012652005070380300395000e0070800140c5001e0503c000c82c01e00a000c7d19108a500c07042601e43c600d043c1c0262405076030010409562a216121804001e00d5408000c5503080703c440345032403140006015070382c810603000d820103aa0307510a04140c2c01d906130070f410450303000b454030003800700b2030407046100480480e003640e6000c00c2c20388084d000c2d1040c81444c11814030503244c40c851203041c0900031a901c11030a6054922400594003542004280c2e00100d620304005075846013400042290fa4200e07100c420f00a08400c050101c030080f503c400103a0803149070000c41e410f241c041001c0c25103011b090b401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 149987643 1250 149986393 149986433
    0x10e060105040e0c0307140c06011a120c030603013201050103090f02010c0c080703081e120c210403050c06091204031511040617060d0c0e0a0b040e0703 67
    0x2e8141820b84200360718001521003c02c00e42d021001880c86d82c000e41a1205a00f20540b01544880c0410000d55840a00b401000e0803005100044200c040300340042c1d81c020100911040d00c42c3e660804042c0860300020302c001c0d810b640350481c4403c2090465100e048401c48588141e030520b6510101c0615000e060b4015070405103000413600c0407900d12602c10103400d03424a0000c0c0d2803109814520021a110b8010362114000d20b007000040000e0b02c801400c3c02821908084040b285440580019016031010040720412120004041c40d02982c01060380c0e030780c601180801c00034011081e5034038010032942100459030009079141d40d20750411080f0382c0007000700c0040c184903140300d01354110ba00961000420b4604a459011145001c50f00050751000310611039a85031940c0b550010b0880d400585000c1c1e00c1740110010407401c1c2882c07811808002e4004040481142c1340460210319074038014204a5041d82d94082d104003540c50b070080c14007030a05000200125411400e100200144480301012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 149988893 1250 149987643 149987647
    0xb07110d081801020703021009030605160c020d0609050a0f020420091e131d121b012c010c020a02031c0207080601090f0c02011802042d05010e060105 66
    0x100180c0c000080302d10340204100c0a000c141d195600503454503109400081d804201c205083c08800e5102c0e1109042324007408050002d515010451070814241c6007225000504c452490030241c01c0c80c0046003509441041c00142d00151511214240a000c44c4110b80f48501040004254075050095942c0d10110302032407901d2a0840b1000c807998406d01483c01e000303900ca50108030712110411900f41c0c0d108009892400503020201005009100c400d03240040e42068000c3c11728035640c00154034100da800b800405180151032001c9206c0c0c4120400004000d40d00d462003044200f032142e40340307030070f82245195481c0c081000706841400e4070000e03c54001158442400e18000d42c0d0002132409407080e203540c01c40c0d1009003c0000303e0804005d034004074005c0c4a08070000980746500d0b40804101402c80c03100b00000d0682900403401c1c0d9102c00710244080e200308250b4400341c42c20354405000340c7d0740816083c842101205007245002811586695641d0381d9100401c007180c0b040724000d50085091030114 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 149990143 1250 149988893 149988919
    0x10509010c081201053606130f050402030105010e15010c082206110d0e0d05120304030c020301140c120c09100c110a05030d1103090a080619060b0d09080708040b0711 73
    0x140e0040c00c24201b8a60300e0480501081180e101d42c208031000c03014414040c080138081ea50910058242624100d000b9860080001865003275040907c2c0200c0c1c01110215615a200c00110b58108070600e05983c000c00400460f00382c50081050321b003d1812800805551034540714004e08601c0100200c0080740c1c1050340c409500c0c950000e030300009520111507019018182c0d0400505c0c0180c805036100c9601c9000041c001419003104d40c034800117100320020700c4842e414414201d010700042d12100d140120902130141c491140700d4014cd445920741d0712460500107030100103102c880006802c0400305540b90002c900b84005000800381e5038209440c80c1a00c9850080402c1d50f0303040c110408801c000002c003403010050b00620455070224402440b10680d50345507140d80c0d450700c8007550507d888914045a0795199242401243d0480d131042c0000760070040e460080d000602040201142d00400c1000412700042401c4064000b4084040c01c081d21107680b0f20300b2000e0242c0f20324a8034802c006c44400a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 149991393 1250 149990143 149990209
    0x114090a0504021305040207150c0e18060f150a080108010504081222060209040513050d0e0a15030b03062802070f0b090c01021b0f010509010c08120105 67
    0x108040754010380300140d03541d500101603840640c07142c120a6002e0300004040044c480c0170300048200c0d00b086c0071704101003083c464090f030b004220103000b03580040c0f40702c5c6040360603840d09101c90360080010b0480943d00344050b00051400500110907640d00c4400300301302a050b0740c44400b40d03014002c01030007080340c1e081c90b42f1041f2941c084c15242000612400001407034213201009540100c203114440a16440c1c45031800001941108002034001d500d00000111020544892640455004005020003a42a91084800480b03095080350468103920001402030740c038503442c2e2101c0849680c001001d415100805d0b0414002402c2072000f1003400580e1f64640d01d03141000250f02111447c0107949189034030b0801d10f840303041d03036000d0003040c211010413003090070200300200d0450090742a52411492142c4082e002900140510380098041006c940d180d4010001400885414103180c000032400d81c1d5101015807001c0c4101922003100c100401650508224226020640c516034101c0f4940381404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 149992643 1250 149991393 149991409
    0x2100e12120702252d05040c051c0905010e060906070e010e0d1208010f080307080a0e03060403111509060f281406090c030c07020102072102011409 65
    0x1518009034000400c0b9070600800100c0b2400c2c898941c442d500001d000c1d8441c94020151142004c42d10492030f100307001040c40000c40c00e140f103480b104910390b2802c01040c44000c140003540030b014070a040101441d201c0206141310081c96508030045034035452440d2031400d55082d8141c4911941c05801800082c100100f09503502204038600000544030450040710f52a2280c002241c1200140c4140c0b020700150103400000c480c0142c6400002c0c0c1d0340d541d0801c0030b4808501c56103206400902042002400d10802481d900b003203880c20340e10710010030001070b080c01b5043d01c003100451a524141d0011100600402c00c4403030030649041010714090404030b480c0d03031005085054040c00400098011400d620401804480d07000310b20040c1e26514000d40c00610340c42c8400d4051030404000160345141500304940300d482014003c0341561100d503440745060308142c800b00d055008100c80441c2e0704030403100c0c901c003004e0000744c5c010b040c11982c000900b084060a000c0b030003031401041004216185d40a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 149993893 1250 149992643 149992657
    0x1030b060d15030f030309050c0a0b1b010b0a0f031709011704050f01050a020a11010b0a05060711030307030305070e0415051c05010e06160918020c01090204060602100e12 75
    0x24011546840040c2c290040c49150b0b000103080c042c090302c03650207141d4142d02501c01a4403075002c03030b10401c200304108818111184540c0b034411108226901c04049218480383c00945072800109401e0710010010780021110307000200ca0800034442001401494116100140c00f41481189030044420000f040d942040c0040749850130480041000c04c0000c00c013090402d44050001c00075410003001183c00b0794022044d100000b446051400010803040c82945507000300140300540c0300b46070109105140d0400c25003030b91030416500c0c00d5542610180002c09100b403096a0001d1740d480c02c0000035128610001c08540154901308030b5030009100d25030607100f82c4504440c13181c900c002d0a04c0504010308403c000900b55402c04246800c103002c0041d80364080ca0600480114601e01340c14201c0d0650350a20440c041e05801410489984000e98010154806d4040000c107120805801150a4525950081b00164051180c8000052581c030604034083c2c81c000241c0b551070301001440c559406005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 149995143 1250 149993893 149993917
    0x8030406020c090a0c0e060c10150602120c070303030b210c010912050601181113050306010b03160509010905030a050a03080901090f060e070503060c0301080d141b01150902071101030b06 82
    0x23a00c12100340080041920030104040700b0301032420042900030064110784a11000f6129240e182c034100540d00e03040c2c840b48a0f20f2001800f20701d2550301c00320090300404c89020b0300030308032140307804090b00c0c15107a108040e034a200080034604500400185100b045078032502d4088020100d52000403408580681100d4a819030344e4940085140300b80c2c0105004132092000482c0061020010040f03510172000300c2d13004806480309a030fa0380ca038600742440115180303040d00801060705403c041c0100e01802400700c0600d000c0003c41e448002083ca040000c031001c0c0c0b119400b098100042607441040280d005102030003c1c020481107a8424208140c0c2500041a5540701c3c1c40d285101d1070104400f4000b814010102c1d1450300349400e00c080da6174000e01030f011040c01a031102159403801180c4000c100c104a1600500d010036a24592483d84840c4100e510195218410f08402d12004010755018080c40b182c0180d9400701e62030300d00010f20358002141d040c14245651030130141d03100010317159108880 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 149996393 1250 149995143 149995147
    0x30203091e0604030c05090903160b0c0403060207060213060e01120209040b040204180b06090d03080a09050628060308030613021306050a030b0102010b061b0708030406020c090a0c0e06 81
    0x201240c20000188181450b003000e004034002052010b030701a0102155025140c0110355100c4090441d01e910420416581030209c02000c0d100090411120701e0b444103c46800d18101a180e41ea03404c140e0b402144280e40072900880e806050f1028505400d008204508008519020000000e00b84032003148000d10000d0b0702160911054855400c400001754006200b10340d01e030f07102d07503200410300e15441e241c1070014901100ca00c141c2c280b100403211544401003c81010a00942e400c4072010340c001c00d038546041d00c8500c544e0029208100d11800388241c0c4580204609480003100c002046e0310b0259001c45080600410101e8118422039030030000c00d07103001c80ca950002c441c6074040e01c100c0495616207042e9210014100c0d5120700a0000800196801d0080442e03850049099800f203291050b4400400c000b100159009a06513801c0c200ca060700740e4880766902c0000c1d6003160400d07402003001d40c00c1400e051460303240022409a02c503509480c1040036080c8900d000f03000c5103140314010702441d40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 149997643 1250 149996393 149996419
    0x170a03081b091306150c050303190219081608010b0f031b070b04021e0310020c010603170d0501080d08041217190b03010c020604080a03060e01030318060305010303020309 75
    0x728100321140a40060080b41c80031421a80801c0107140510618500c8201c00b01c00f8080644100c9411034401d800000460454599180184901040d4008492400d5082207425850f0b01c44054150100340c10303450340c0795545403458094107642e04c0310008400700610180107204150030103007510016002d4140031034680e0341d12442c1d00341d0100409401400360601140002c100202e504581340700314426281001707101ca200e02d800c00400e19811600394150000c500070805200c45030701034046607003820b0000c6481c03a43d0380c44a600c940c4042c4110280002e0020722100b044809005290040c100d000050417020040e0000a0090178054002070000084551f450f14035845040e00840840300190540541e04000c0d401c90728100070362108410540c00d103140c0b41c0451806101d01008414241c0242000341d407555034104032a440317550502c040c590b450b8004a141e0f514525550f0185100f0340300e0810550b6480e11218840d404d69110b90201030601c0d005000007580802a600d81410690b20044a030344 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 149998893 1250 149997643 149997691
    0x7152003040509010305010b03101b1409060a09030204110c0706050702060f0d090203070b0301060e04020f28110a02060d0c0e1507140601030308011511120301170a0308 74
    0x101c0c1c2d0b4800350307120700004008000d000d41135002003a9007000300c0880e694000c66100c071400303865078103000b141141000c0c0440c560048c01500c842410007454041280741008032000200d258103d0460a00040c200035014001c40c106481590141c407098403a02d41001c0001000940e2114240580c004004011603502d00b1074850400b51003c14482207580c5407201841901d8500402c1080400d0748070b841050000a61050000100c9040e1011507076400300c0b031943c280520020b0350000c400c0c079a140004000000c000045100090300c0281081c0545960305003484004109108104070301d00103030000c810351001a6195422960604c3c40d40c2c00106580c420761101b900c0445064140640002ea4045401490040000108a0140b2505024042421166815695240901008000c21030040040c440c4030200c800401d01d04020317207808210390400e14420f81c200180111485800180440184075600980c0756004001d030551008009000d21906c00034090354028201226038000c44d42c039802038003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 150000000 1107 149998893 149998897
    0x20d03080412090e1618030308010518010605030609070309051f06060e090105041d0102040f030b01080114041203060b07080415080118150504050a0e07152003 70
    0x203a80c1c25009881d00e12900341740350140a40012441c0169031010b100c01c0245100e695401942c0d4580400d102a280c689691016407503180401440450f500000340daa0109040b201c0c0c40c0302c1c1e107901074280d0080042d101e0180280c043c0c401c4080395080c42c5503031040c41c10050802000200d035524811120346074501002684031124100400803490b040e0850401c0200c910003a40d2442c2c02c50070792600b2a8001d500982c10451142c00400500c100d0503801401400c1d490001d05c00c1402c0312604825156000703000914060407043c5017071000744294803200180c48419280ac0d9143c0ca181030800d1250042c6c89244620b045200c0052a110f2290612604031280c4000c04406500c034101d04d42c1c05404081c401c0502d03e9a603b2000510740d54500a060140a0000d000a00544e2040c810707401c04031540c000205049003083ca1030300701582300000c20b07280c11988204468625813410074038214 = true := by decide +kernel

theorem cover : BRFrame.Cov 149820143 150000000 := by
  have h0 := BRFrame.cov_init 149820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 149820143 ≤ n) (h2 : n < 150000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
