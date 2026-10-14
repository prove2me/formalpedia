-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2310
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:19:42.721649+00:00
-- url     : https://prove2.me/submissions/753246e4-b355-4aa5-a98e-5263d382b924

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 415287769 ≤ n < 415467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 415289019 1250 415287769 415287779
    0x1f09033509030a1e02070807170c03030301030c05150f0a120b0109051c03030e070b0d0f0c0c06051b0c030d06050306010e040b0903071a060f0103050c070f150203090a030207050109 79
    0x2224807000f00b480c4244211902c8413000c24001d00c0300c0400341003440e045440e02a5500045081c154030302c42020701074028482c82281900b0084100c9050b81e400c102c0c00d01c140752800c814051510700c2d9940382ca11400d014041024401c450b800180a03030812503483c0000e08240040c1c140440d2169004107040c00551401003260f44c440703030b034480480214801c2c6860703282514102035001d04081817070b03079243d8059104086101654203000c3c00319405984410095052030000a60031141540c2d40300010a4000c0e101200003503041d040f0590041a082e61b40105101c19182e91076503821420240610b41c10129001300251954441e5078001c0c60205c005001551400f1109140400003410180c4084820f0300003d42587d4100215000c003607224960000d2507062100c1054421010707122180b2515450900b51401d40c882c0c0a0329004080c400c40f91490071010f075031030518108a1001c2118240914090300010107038a01c0554031864000020300890f4000b882d0080c2411259004941030041c03441052107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 415290269 1250 415289019 415289027
    0x503030309070b0d02041a03010603060e0f150a1e05040b0f090712110a09090c03090507150e040f02130801020310060806010e030f030c0c031f09033509030a 69
    0x402c543c2e4042d0004e549040400203080688034640108211000d451646074410509030003e40c100d0301195070800906840c0c1100c0154914103840b50704100100c0740c00300301c0c20000c80003c10703c1d107a401080704800e03507a034401c0c01e1201003140c01c40304040001c0306402c100b2414203025034001840219084a40000100001880306038050444810400e12800c100d450080c41c1d0700c4030b507912107100d4009407a03004684c0e0082090095024581005060a0b003448039103019000741c506c403d0b031080160115905050540c0c031164140d007102d0b01080b020103600d18541e2210320952407035000d046005070740d401402c4061071102040d0b51058849030700c10801c0000e224213898044040d69076910300341100d911007600495600c078200a049902d03018003c0b40d540e00ba00004001d0030740310900d40c16036071400002410161280408020b850264030007003003804010f0500d80c0103510083c8a4200607200c5925404d125012016118400070201c0d031414000e48a090074001199200205800440c506202c0f079030014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 415291519 1250 415290269 415290283
    0x60319050a080913020c010b0f03010e060103033c18060e0d0204020f030703200a05030f06120a03030605010315030f0b0414010c08150306010617040c050402040e0604060503030309 79
    0x81c092000202d02d02025a40301308820710641c1048030203541355100118864001c161044000e44588c1e10080d600d0403071304043c011010010004009070495030310b103882c01d4540c08292501300070b104100c0000030078240090b01c24600451000b00a0020324040001e010341455881800314141c1c0e00314000c1000499400b00e918032a0f102e007611601c80c202c4607407004c200607008440100c0c0e43c01901104200ba100e81c1688002c0c0341034201c031102080d940d940d40481000d0300c691408007000800400000e10110050742c000e503080107001c0c108511650301031410a050241446040b00040c0c0c560604209a42e4940580500b0820052608410318510750b20400091480340c0000c000000008c001001c0c0a042039500400380e100e200280010a18a1001800c50780c007203403c0464540300c071140340020b0900251042c10707110a61100e462403010038070407030340c0154000d1048542c251b22041c0405c498689001030030003040c40210350000c50030442c0420040d00c055800c028043d900500030008020700005880c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 415292769 1250 415291519 415291523
    0xf0703110309060a11070501050f16020f06030c04060f050f0403030c0c05090c04080613020f0904050f01060906080c100806010c0201121a030f010608060106300203060319050a 77
    0x9591880a810030a4158040c40000c150b10100210340540065040351240b02c2a50400e0103a4406a03160001503809009202c1c104008410500403c3c98030206500c40c00d00300e0340010254110118001c0001786036034811200f143c040746001c5401c0041c03580003035400b44a00a05c0c02c0084c200b074081112115280034500c40503003080713103c140c640140080d64000c9005054040c10800c01480c05018001990380035103c1c125641c17203050009104500b120712a0304000d94014840d103000c0c2c260130104940104054011b0700c217070244441c5c0e040b5480091082000408a80c41d0100d9001d1400c0c901da0300b81b40c01000713428068400f8102d8071900ca540700c05095402842400c119003403144900040b181010b8043d10804050702d4024140b600c0480050082d039042c0003201114403080d01d0381c00b900d0a03134420f4481d0078400c0c1d2220006100380f5014195165a540580d0402104801e80464400ba105002d10840503419800424003040d401c05000d1496100205030025828104a0343c810b80d880086000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 415294019 1250 415292769 415292777
    0x31205070203161509030e0a090207020f0d0c091b091202010c03050d09081303020907110606010c300e01030c0816050418050708060a030807020906030102090d03090305070603020f0703 81
    0xb020401058824006141c511340d5810000c0306850b20707024001c0c81510800314440c00c01c0c4040003510f56918003c40325181d50103480000181d407041c0900c2003003075101c4030032581c1b800e0781d210204081c1154852850f0300403504469510b4901c0701c1c1006440c0d001c1e1900f01e802911005100703000580d81041851521590601d441591540c0c9402c0b040001c28400e0b0b00108078810019105241c0c00f20040c22105a900031584000140c03100102915011200440483e5a8208200040b031a6008020340706810713000301b045120201d03040d4800541c800e4050540360a0540e08017410402d654450311104414001303003001c0104d20794095007e0494503004001c141981d042c80c54400907280300704151801403200c0402d8a0000e03410069030000b4003421a00800083c2071640014010b1514010f040200c80d08000350ba4986031540e003d104010400030161500b66408018801c1c541c2c5403880311100044c001d903510410f80d41545003040c1480c0b000c0d40a01c007058014003009400d80700c1c42e000c80342c01c4c9500d414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 415295269 1250 415294019 415294057
    0x1211090703061d07180306020723150c07080415020c010212040e0615070c06020d170601081003140a0605060405090c090405010905161d07080c07050a0c12031205070203 74
    0x1304030740001c1d24518581102e004a50000208100d40e0003400b29a88550ba10924440a080c5041c104000e101400f204540c07021585081900c0c6100480d608007402c010044d140210648a4ce5007030b6000d648907005500d090702c40c0940e802d40c18080e00d81650400d04c0544800016200004901d02440c040d100100c0c0030b03000490b0150f6240808800340e1005144c1c2c0c00d0300c914480c282600641c042d442020098003841d4a40c03000c103407007010011803818111000070020340741c02c001101c42100040c543c41e10b881400c180403001c0b030340b807000d401d80200b140402845090420b2a1010a03124003030f108034090b5003008180021030b4400300d1071740780c03001d800e403000f803120364590600740c0c0540f183d00c0019106001d2900610014444c82c81d0b081c042d0344460641009000030b2901411603c24102c564000003440000880d003801a41c5d40240380b0180101c08a540c01401030701c0b403201e2100654410302c0c20750601c10120040540100c080c022903008500204038510303001c2000f0b51a40720f848d80490240703002074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 415296519 1250 415295269 415295281
    0xd0b01030e0f070f06050306030706050f0720150705030901080c0d0204060f0f0c1a0603070b0c01090b010e090c010521041b0f0b0f0903071211090703061d 68
    0x1e4080a07a05003080d0860320041e011045440d00c0d003003a4003c0201c94031a40ca004109103009800b1a40980d0000e0010503055207003e100311465000011040700d441030801a4001049032100c503512026029000c0e0150324610104202c40e024182100b0004c01e1030074000c11011070301c0403055501e800707020f0a01001940d501da402703420900c00e114940781c0441c4041404545c1c1076100b1042c0d180c2c1596620348000ca0380f400081640c0134146032000902a0b50840495007400c11070515683e00f28802800320b50031562a0340702c8411035049610592810b82d03541480c40284000300c1003150042201d07070710114981c00e101420549610394003445074140300300003403e821011641032030070441c0000a02d41800c1ca081c0762401e140341d86840071442c483e0302d54130040450340380c100c04c4803841200c49440e400c620300940c40140c150190004003919906000b07400700042e50140b0010b40c24040c03482201c4180e20582d00404204060340042c0000d0100340c83c041040c441c108c080b00c903441003008504029a170580e45d00f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 415297769 1250 415296519 415296521
    0x1090605010e060a022803020714131d0102070809100306030308160c080415020f032b15270b06040603090203010b2d0d020102151801021b010f110d0b0103 68
    0x41001140740348103284550500c2d0310f012a440451481f90342507850385a914401e1aa50440c400700c01c0b580a201c1c1001703100c0010403603102c81c04a02480e003212151403815807415003260040c0074207803000100010742c03038040e00d00700d12415100b02c414101000782e5411524020702c07404008003458083c00c0360700180c0c0b01d424050710002080540c040b07900c0d40e0700c645914038882a054540d0030f1501502c9040c80400e4070741d80c0803040c1c0e0598600d035141c00201c41c608010203d4140c22000c140503003280d90305910000c020103c600c1e41c014200d600810502110201390840e4524070005029240c1d9161072041c010b5076030b50004940456985d881c0101c3c001d0202d00002c0c3c0140f140000c0700d0740c014007040d0110a20442220030805e500713800d0094881c0c2e0250702e0700307000e00e500e80204024016001070400d0888400d00c44056500b10700b0704c0da04442c008000381c100701d00320780c0030f80c50b90b0080500401c040c4214440c00d01038440400710310001400340c0d04810056031594007c0308500000300381c43d55007041c0c9991007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 415299019 1250 415297769 415297783
    0x80f010e0423030d020a0e1f0e0112050a05010303080a0e03090405040510150f0f0e042d050303190c0f032031060c08070f120201060e01090605010e060a02 68
    0x481401c2d6650b803003e03204c09200941c01001502c010402880e0090018a0449403400c3e4a268076081c9a8012114813800c03242c5940418400c2e05205560141e12240704075440350078880d40141c1070024095045003005085880014034a4201605201403441444c802006503003e064090700d0214460301e46203401d0742085400d02110407403d1030000d070548103504487c92102107070380f4081240030043d25080d01d0300d12042e2900034401d14105c541f002c200040c19000044440c0b55003281040c02d001100c0008450b00e0800010540340c1c0d92020081c00009401c0d84550347d10454a01800c0000004064000e041c4944c5880070b0740505a86203640c20420214443c030300b200d0384218601c00e0ba00c102030900c050b0a0410503401102c4410211503441c0400620b00002c030541e1800cae12246139038034195030f03504150340c4401e404a844008036034100f4001078160410300c4000c0e0381d640000c40c0b000e0400301e81501c0c03d80168840c01100741803610400190344c00a204a05000040e1007883d0368021200d0b00340d1038400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 415300269 1250 415299019 415299083
    0x1120f1b05120d080604090503030402190506040b090102010b09160c0201022d0f0604050316060605090a0902121906020c120418232205010219080f010e04 68
    0xb950700704200704003000c40c1401850109480b611060345408007480100e501c603030801049a030040011402520b46031507005094565100760070006512800420f4a9400650001c5070099020411b003506603028025482c24400503188914a407170071003211902c038049d404000b418061030030410400c0da4402d110560501e08c02071078200310403400841182c00c4030720600001805000340c2020603c0c0d0b0002040d0b05001d50f81180c021801d00621103100b5a00300b14007c03086800340e6071342c8000101c0307454240c1c0051150090400001c3d14101600600c0346d50800002031940c140c0225003651802d5441c07010700807800b50400c1005860f0040d518500b0315204013030240b00b0359080b010400190f0410b0442200c50112503140e0180f2803840062000700203000c100d0052a01e054090740003420a55207600c0d68006200102c2d641103062070292661400c85e032010f0500454982c03108140d402c10350b044440c0d15000810440481c0c60356141001c0e42d1070002000e040100009154815a083c50000440907800d200c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 415301519 1250 415300269 415300279
    0x12020111030c0c03060a060605030106120603061e0f060e0c09010504030203060103080705070905070806150d240b0c06060904020d05120d051f060f030f05090d0801120f1b05 76
    0x254a000060f034030310314080c0043c481d03c5400c0014000000600952040340c2c401d84030541142d007404d03070513100c05480e121480c01c5d05640710800004501c003405001c49605500145280341201c403a40e00003552611044603896500700700040000d0702200bc8059070050006c414251a50340160048034640710f01d40c0042e41c1842414004424041540c000b080c5c0307644500101c840b0b06035185560000e94800712040c001081d90140001c0d510306003040600010b4040b44009450302c00290400400c60381c1d10310181c124001041c0c1c180c03e8001c4012149070241104d03008503810180400c0c54243d0f99080148681c0c080c0c00540003080031502d8816045d42c50580c0130b001d440d0030300459419020142c00c02d240140c40182071402081c60489680703405100b007802005821600e9003841025144842c5101e1440300b050b42e030348810400b0410b20720400d4040e2150343c025003425500705900400426060b0443d907061592284c0150028002d05880503c840d84524030344001c007144281c0a00722405584640e0f041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 415302769 1250 415301519 415301527
    0x9050102070b0105041803080c070c091e0c11070902090307150203030916050310150506040618080c01081612050a0902030708070b04031401060b070b09060f0606041202011103 77
    0x502c0c100703041e20800d6404021400840f0481000079003010409404514014042000b410300400207004170341c01242440f0b00c43d42d483c20b85c94107c8800490642c2003420496280100150300c0c01951260031481ca0305100a8000000158840d14144500c1c58140d90010751105240ca041c06840c00904080b60702130910120610065200da00031510155a401100404212104040019802e4032409401404161044000c1000038403c00d0072000044010004c0040d040c1c1c1c41d040200040c00341652601c0c0e81c5150381000c2e10381080141c105000035040300c402104a039922401d2107034089401d102d80b1600c4014a00150b408030340c0c00a403561058100020880340c80364a82246294920039005c40c1d0354540c2c0c4141c01c40e10340d9414017820507109800c002c2003001c9404a007104124510074400002c0039652400f02c001a0350018804072020031626041000c4088288031103513000400c05c100703000c1031800000103151841940141c0310030845800c011015644034944019005502104072a52 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 415304019 1250 415302769 415302773
    0x110c041508150f0105030109080711040b09130308090721060b1c050c01020f030d2415170c0405010302030403020a0b040c26100902060c0a03050409062c0a0905010207 73
    0x80b80da42190340030161510b560000905003070500c585440c85030445540c40c2400d03055510700102c80c100111180d4820348510514000c4e6071200403e90040e042c090710301c01785000c42d190141c00e1a1008000074140e400980f400c100903411840c10441c002c00c140c9090845004920b403110080c21a2080107821060300b5001c0b43c0c0c001d00003400e01300800d0180c3c0465640d90409001240d5550072482ea0030040e030803d024104488041b07401c0303180140c1d020040d0240707071401100000e2001003507a0140d001c00c5080c4c0d43e000209600701c035241000d0300d03040c01c1080d4a0b2074104504542486240711f42c03410160300000081c14148280001d4050b00e5100c04404e540382054244801b072032510307005203181800800300f10508100b800681306400840c16003d00000c2400c0f0f003400703004004415040c2c2e00f00100b00454060b40b034003402a8208584241c80301030300c4908054407070044a442d501700038901240c00030345c0c1141c81c3c520319404511904800d944113213a52152010009410840e000070015030000c100d01c02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 415305269 1250 415304019 415304053
    0x6090c0d06081f091104110d0509100c0206011a0318011803020705040c0c0b0414060705070c060507031e1103040f0302090c0405090406051e0124110c041508 69
    0xa2003855440c40343c640ea200110454046480341a0014140e003981140c0a2660800b0b0300038903c0001d125403814101040d0500030010b03158221510000c0390404810801c055005204104002c450751000701569030501c1c04600402401d07072602070707610801200007600c0c4041e650080d081800140000d1111b404551380140c03100d10180001c502600402c2008a0f582c2450310440d01455240d40d120001d1055680707a2280d405c6020780140c2c3c0c1e0b0480145184103100c801c10a181c0911547d40c1c5460340d40e500d60030680c07000e80d030710740040b02080001c108a5010a03805624440441c1020725480f070328034200c4000b512090ba101c55032410740d000202c2c0c005902044000304d401220300988500c801c50352210b025040910075809003940c030082e11800b06004c01c0c01b03540040c1d84001e40100044180c000c10001e0306070810300340d00425120300c40c00448404d400042c038008400d24428180013a0030452404e00640b10710001c240e4030b009581d1a0305040942c00203580314001015500d0981d9a41194052840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 415306519 1250 415305269 415305283
    0x1e03020d030617071404020c0d0914030703020108070806040e070609030c0503121b0a0605010f0302011d0931030305060307060e090c1c110406170f06090c0d0608 71
    0x1c24030741500068a0b00c007002d1408586441e12010700318003070416a00c80c0c4070030411059140c00c40c1d130a00003040840001c00070b00d203900c400f54845035652490865281d1036021004041c078005c1c2c210b04410130041c5d0b040818150031102605000309150740f00e0000c1001070803c05603210f62032068030703000030b0555000104002034900890690a44684840906075152503602c030100080108000291504404129594500780c0f240241d8003459156210301065601c280c200c1c842010072000100308541e0070411041c4d024045841d681c1d1140c1c4840002001705400034882c410400e010f4a10000c15001c07881d220030342054020040e1803100540c240107008080844055020b0710035880086941c5004982c22082c6041c01000002213a03070307018001c82e564000c81110352912040c0b030071220030006107000d01000e680c3d41003200c503282c918203240100701c45841d603a0310450080400910403101301000302c15a002c00d0a94008003d6100d04003622850f103c0c00c1c541005840c45c00b0404505924045003032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 415307769 1250 415306519 415306543
    0x5041509200102070b0306010c15020f0d0b0d020f090901020d0504050a17040e0a0b01090315140c0c1207051207050c03100e0d0c05072318040317041e0302 68
    0x7000c0301480841c016a50b8038041e00485048180034000194207610914501c40401c3c460b0300c40144403108155546d083e038115a124050991000c91980880030952044a10101c0c080360700c03006002140d008500c401c0200c0c2940e5000304062400205816000d40496944803440081040301d45030034280581c4559031040c0403504240711441d1100b501d50014156002e9801031035890800c0c1e11039200d0304000300f800f90000f5061010568000010031100345000c8648801042c0204400c1c07204528083d11039002800481804000e2000d82852080010510700806805100654074031a500740146810140c0c81c125100080024141040144c08161001160016402c45100300c02007a00d5105407801106c0511290f4004003c101071240300d290580c802c0c50140042c1d80175251543c110b0310900b40d01d0500b5054141d05000040c40c141001503401c5440380315800d0005983c107059400400741c41da41c00c581401403041e4008281489a050100300c02301c0c0c200b1805a01c040c650f0b1a000c0e48070b07203040c014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 415309019 1250 415307769 415307813
    0xf030f0c09061805070309020603131a091b03030d050c0406020d0804020d02010e0d0212010213050a0803040b0d060b0307030507020d1e0c08041e03150b03060a05041509 74
    0x9a492002d0080c0010b80e5055450b24020f088583c0121000304001007011040586030110b10015803200070003940241503a50b000e03103011000341840d41c41c0004850f8204241c10740c50f820480b05a0340813480d0100000000301803c03a00404100283c42e40c0540300350754012520f000240f140307085507403004008890740d03602a50118107889500341d40c05107040368040d400000301084400150b20600c03040c51300b110028070f106000c6401e600810081c0410540c03402081c0e50001d0200c1c07a95a01605070801004215241040c8034200b43c1c0260b102c0c0600d10501420000200304210f03030741e0158020704003500302060165241e2510103030090143c102500c1e00c1b0050b01510400c121a10b10540c2c070360314081d00b070628a4110500c3c400c000c4450745c0d00c03d0b100780c403000000e110200e07031944441c0200e90b421012007034810340c1c01c1c29410807001507500000c10319441c40c40c01c4207001c11514040f69682e40315808071000201d99490b400c11070710212024100c1c0d080341c0c0c0b414203181d003003001100d00400d02c1926000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 415310269 1250 415309019 415309043
    0x9020714010f060503060a02131a2107021203060310020307020a060212070806300f010213080c030a110108150913060f140406020d0209150703080a022704060f030f 72
    0x1f204e02e0892080503101d4444004550302030203a0100100801070660046116902e0702d0100341e04001403045003420320002e4040c58040c000302580c10010380380c4910211084ca0b2940c01c014000036a12148001c411181c29000b10028404070300034421100301c1030b0840425581d8103400c1d42c0ca801c1d1040c007202c000300800d41c0d02001c605c2505001405000d1b80a60103400808158010400a14200c010041034400d02c5190001054154280058802c110001c1d80b0f50300341500304007007a41010040b0040724002d0b0301c40c04c401c43c08035600c40403600302d1900c01c1c00c0001c4507880c0e260001c40c4c120500240190041c0d850418849a07224504000b41424000c5030200f1160072040310500076160711090380d00c0302101071800b040110b0307443c1c1d0082203140c110040062030f0090f1440031841c49280c202c100d02140344082491814113400002141e40280b2010b0b0840c07910341d0040d406041140c0b2803001e80354170501100c141c0401d84a650004028100c00700022100c41e5603860580c102c012001c2d0200d442c000205 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 415311519 1250 415310269 415310281
    0xc03110303041d1806040f0b012c0a0f020705060406050609070801090c14040e1b090105120c0d1104030501140f04030f020a0b090c03070b03070c0b040503070807210e060409020714010f06050306 85
    0x420000c414a51200010b00d0725400d001102b1054001812003023003580d030f03904c00908007a880d10051481e58810310280c031041c038007420114111a0014103841c000e0000004106045911801050554000000c000341d22200140c0c120f0719200207100e4581c8800c00058003040d001e828400c1e240c820280c44081070340e0320282c1c5030b425429000b99041c032400b0440622100c10000c1c2c0354021550320690740c801032818400b0b0584010180c4800f83c903d030704000f03800038050007482000c0c0194024880ca0790030915040c02c2007088a9032002d2b008101070704105440003040006407007031204140c00f581100c45a40309062400303c0c55280c4a01c0411703030780300f48501000003c1095008081e40d1090700c11780c42d21100c04001ea200c484108400034012100b5000400480d40051240c0340078042107030280303001c0700c0d00e0354040413201400c41030900340601340103091040b00d4055440701e0032a000d6810401c0f01680303071051403030000341506601c00012020f5080c031034154802222940b000e402c50f1801c0302100c030252580 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 415312769 1250 415311519 415311539
    0x40c0801051207052101020c0a030e01020601060c052107050a0c0f060c0503030718030b01030803100b032518120b071407120e04090c03110303041d1806040f0b01 71
    0x1031050341c0c5c000480e070780801206054142c0124043c1017040000d807501c4100f040c4203040c4071500c071080300861030300c1305500c40703950b81001014058801400d2140c814107080d141c40c2c2e5500f48500e042e130000c0300e0001c65451420b030b44030187e13241c00758060301b100d031061154078201102032001e00800d007042d4141207000401620030554070892a801001039461900c90384e00440e400410385255201115200c9400800a00700d20750040c029030140003100e0b12070410b0b050510041d50164017421803400d082c030900140710b40c508000010400c0c5030364100c512410103102a0f030700c003c1c0085504481508000001103400c16440700307072803d81c401d0501080a030b59560003030310300840d58909403c060340203024201c0080c0e00031144602506081c04d11030112040301000806440f4102c0c01113441c01c005d060104100600c2e0701c010440031404070017070b40c01c02c2d003020120032003080d0200d52040032003c10383c045129030141e8401c0000b0300003104207440d041d20385428906451149410701300c4030107d900000242100030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 415314019 1250 415312769 415312783
    0xb010305060f0a0e04030c080a0305070915210f020f07020f060c1b040f02041203120b0607020607020d0206070b041e171b0f010c02010f1a061305040c08010512 70
    0x4100b03d0125040210142e440000244128140801c60007034501007040400030b000032800d903a0f00810589003221009010b41c41a03888044a58450072072004080d80080c001c202c04501c11000124116507070880308042c024600c2e5244000d4030003c1c1c01c002c0342d1050002003505900a442ca02d2031248a5014403086124280c503040f0240c014880d10b6900428100c1c0400424030018008284291a10309200407640958041011041203a00c2042003540120b00d00d5600404440304000714011500450700520400c1d500922900c2c00240c004110f64800752120209030700a40100e0f01c50200d8135140d045440150b6083d52450420120881d814192803691100240d000b400700d031518284181d50b0704150070214000004c0c07000c4078030650401c80108101d2808443e0040041030840850102030708507910b12142c0c100c1030741880d501c0720000403801000b62030715009603a80c65441c9013045100324a81c0c4075030406640181040d40c3d890741076500c0950707075044c0c4e4030840f40301d00e840c4501000c0130b6440d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 415315269 1250 415314019 415314049
    0xa1431050f0909011b0c030e0d050d0c0201180b0a1404060504120212010e06100b03060904021002070812070204060602031e03070201150f0801050610091e12060b01030506 75
    0x7003036605524a5003002d184240c0c12902c000004501ca034103401842040568410881c0001140000f0700d50900d54002200f00e40600140ca001e1642d180c19100c4c1e646603003400d603a00301403203015101c0034216441100c60007004108024100142512986d03c1382e0954010b184240c00a401a60322800c441c14050031079080322042d4868615207480d18001080d41c3e4030f0b0f088180d034800000020740e42080004e00650743e00240000c00750009260201c0351170001c403c150041042d494041c42004110b8980701c00c13080d04690102c80c285a44a1104800c03460440b144e0444013141c0190021400c0980070038002d0f05210b03208031001e0140548508041b40d99003e103001402c4604e0612246007407200b0b40c0401540c00040e54400425642c0f00240312041e21241d0307500030410b0403003a032000c0101e00b03001e110381508843c0498606060700301101004044110600a000400d02d501c10b0b032035061044680b05000134048a40150031707910250401d1030040c400440c886001c40c3c02d10001586a04d802d4590040001d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 415316519 1250 415315269 415315279
    0xf060c14041809170705010f051302030703081b030d020406021516083c010e0402090c0c01020904060b0904060602030a090e040f0b13110d02060f0a143105 68
    0x40a0b04607144064042c885064582d00d900754450121490a50300038010705028a001023009445c240341401181c000030441098030690210a2005940208414003260b401c80c50013525140306070414071610303132138055031550380c400054440740c0e009c0305e82c001c0c004448260b002c2d11410140703500c1000b094107080760b0540c3d0b0f400e5401403d43c0d400d800f81d043c280d08131030003880464241114908180300301c510b060441c00080b10090f0007454803047c424882e4050140b00f08a0607460402c1d41c041460a4805081d504100c60301040320001c044096058030200400103006000095480d01d0f9480c00d60b018914660107282003d90108200d80001300725040c4420276951070040e1483c00c50030304401c000141040313481c014440455800300303202c02c545038052290b503009002814424500605d0540721088014040d1403860310900159890f40180c1740030106454035560740d02e00413401101e210800900c0b4409000000c119074001301d000e01d062000e124004c0c0190340b402c1030a4214030160720300a20840d9400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 415317769 1250 415316519 415316549
    0x51002042103110607020c0a050f01020d0503040f0501060e041a061509060f030a050f07111902040b0a090203101410390b0703180314070f060c1404 65
    0x19180c03041c10026040c028075100d00ca070305030480400d01303102068604500603889a03918003681d1034081651001098100c032106044e00f0501c002035103801041c02285c00b80800800000d0500241d007800d003600c1680000200100b9494028105070a101aa07066441900c1c4031b1218084075140e4004034000e5000500c140241e61b076004035510700341d000180c5203800140900c07805c002210324502442c003592072000041460700e04281d0141001c0402003050f000c100b41e08141c10000d1390702045a440e050710f841143d8610030803500114003d45820084260058041000012a40c00d03a60285001d080700c05401d0307219554810640320b0109082d0100e55010211402100315a401000084c4c5030b0041320030010250401174071080d8a98001c2940205c03a030b1400c124103801c00101040d280da1223681d90904110188014030f80c80d4103000800c2e0010240411a074803008003001880995070388681c0900e00c0b200200f5a49810400b9140210000700401c504404221042c800da205440c16240c2412002580c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 415319019 1250 415317769 415317809
    0x2b1a09150f0612010e01030203120a210e15040203070911120a06081605010306052d130f063605070507080d15140310091403040305070305100204 64
    0x7107059500c2419848101004101c250910810480d4000e0884000080c290742c9940140f50070540c00c80020348021208100700300e4029003000e4402c80f80d030080010042c0d040d04d5100302c03174001c01e0030041c004150b120f01e803030780c20718114544002445a0701c281d0a03101c2ca642d036420000151140009a40110001841040159071505048a9000007581c001066030f42d6100526801d0513a400c140c5d0007049a144400d0102d56090b001c1c01c00106015200a2070a4048081c880710441e070340c00306480754034800815490316a0358250b00c0340c1500302000c0304110800307804e801c80d4010300c04c5114001c031101c18155010240c00c900240640380d01d01ca900044031018040071904014040181040203010701884803001050848019049544000c28000303070181d4074803201380407103e441e80144103081c6280302000b415100070581c00030084880344080303950461450700311146070504609048521004c500001440f0000403524101e0340640d042c0c2c0e0301010301810590030380c03150b030150200780c1c0c0c01945990301d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 415320269 1250 415319019 415319029
    0xc031407051204050703210201050c0f0403150b06030c07021f051903200705100903140c0a0f0c0f0b07030e100e0d03080610030204050d02062b1a0915 66
    0x3e4403d1040080d682100c2e00e80d43c500748040440c1c2d5000f66001031142c80c1181c2c45070244502c1ea0007286400d501070078286246804030070b40c0301e00e0000508860114541c031407510244d8000202c3c030b250081510741c491410702202285500600410b900c40e10028402c040129043c0c01a072481c0c02e0507507201886c04642c8482d19140c0c000c0100da8070100365640c6040c2c2900d80060707003903030280901d8141d05a5240c2c0c0b50b0502030328001c808182528030a1a024411000076080446441030011380007407503440310102c42800f400d02d01c4e03201c0c000e001d400301518148100071400c0406404d89040000c41d08a147d1104950207460040c45070060100f4101c074401d404e1882c00ca10080600b4030f1610340590780d50040008a613000c0c00c14103040f80442d001005010051030250300d0000700240a24046080c203180200040c02002120000f078080d45c40022171880a09091002c0f00c4640ca001d41d0b0001c00c0001440f4020007440010840140e1691a0106001c03516045020700d0080c855146d99420f02079030300702044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 415321519 1250 415320269 415320271
    0x20f060304021305070c03032304060f061215060812121302041a0f030d0519050903160602190b0f060f040e0c1201050f0a090201030b040204090c0314070512 69
    0x10f81d2040944641e42000d5030140200c0744280100d030348804401080c2e142c00740036a0007084607012085000011030614101061002c3ea0068012002289412412135040d0041c06640c00441151292a00080c00d0215084c8608012144034008020080c1e4076080760707071560042880326050400030840c0c4510700c4079607a004c2d9000380b0141c6180f001c031015540000c04035400030301c5030704a044607a1280c1c202840d01143c4914084c0701503015046c02e152040c2c0003091441105103c407003200c40400c0b0700080c03078030030410303034000d09400743c1140e0540c0490b0841f1240740e21188510001031290085100120704102c4504c42038903070000600140d84ca070b280b182d03140e07143c005244c01c4e0400b41d19030b0300031110ba449000300200d840200c1c02038280316010000784100840004a500e003d6810301d400e01c04c5189400340310640c04000c02c3e000260086e03c44c40100e01502c0100000769000e400401d000c00c1410543c1d100d4090101280c80400080301e1311451500a402e04607249404034170203000420000712045621 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 415322769 1250 415321519 415321523
    0x501050708070c1d1b09060715061d090c0a14060a030f06170f0f0a0308090c0402070b15180106140c030c032208060103030e121f1107020f060304 64
    0xa040d8040d152000b0f4890810036030071041d0340024040501c0001901708003051501c4801c1c5501034070703000b205d030041030192284810007401c0d00054124a000124943c1c03141c006403900001c204000e101041380c1103500c2900783c400b4682070041c0b606043c3c00d880c3c0900c07001c040701c00c240b0701c0c103c2d4010440c2c01c00515404c81c4075810245504c0c0c640150141e0141d03c1014003500e4058401a0300750001d581040c1f030f00702e0400150003a50b01c09010060708803400640c1c0b50032143e04d8500603903d0740e2400461401c021003502d00365000760010036014100b08000c040c00d486030202c0307115100c003070400340200134801c00c021080300c00d00307144800103001d698441e41903210003200c0b0041480c43c00407041d460754a95806801e0f0b85005400200d00a129200048c40313148007400204c1200c09134500b4000160345462041c4001000c1c024203001480e80d40e141c0340c42d00103405070f040301a60061600c901c48000f440440800c11804245405121000000500306603102a81c02400e05110215450184809a4400b0780300b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 415324019 1250 415322769 415322783
    0x21060e0c030d0f0e010c1104180f05030717070b0c0f07020613030c0b070809040c0c0501020a020106030b061e040e0708030a05270303030406150510081b04050105070807 74
    0x400c00194a08100c070388180700081d9200b45503140500002040b50408800590402c501c107051200401c0035a142d840002c036080303400152a07000741990f0301600d440c00d20300038418428185104d09014010020344641c0d4043d10b034102c884200345542e031510303100e00c0900414881c81c600220b01c602400601130301c5400740e68414a8942035481d00000e049400c1000b100b40c2d03001081c6070600030050104084d40003005108032182c1004050b9640d01164050320340300e14003e555034403a810400384107425418543e81c000000715615105110001c0c0a41035501040c1d07005500c007004100541002007101d900304240c6061241c2010702601000301a00050172400941c3c0314801002c91540300601c001e00c250740301ca07100c282e40d50703064118060701c03c050b8042070004014400000002602c010044a9001e5400704001800540503528600a9211070f001103402204901114154641000c06a4058a8071181c0c010141c6c44032100d0b07000d180b003103008041c00a4014015500001c1e503040150134901d108020b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 415325269 1250 415324019 415324033
    0x9061d060406080f07090e0f030a12021614010b0114070b09030906220602120403030302090a0f1d060d03020a0b0a14190b01020607020c0d0501140114030721060e 71
    0xc089450262400d00303004070303a0401780d8108401c1d119482030181c1000801c02504101080c5021140c0702e010b0106a50288070b504058071010502a03030460b4043c0e410b080d28064000618200525401c60318039450a082d881c4c081031301e80c507600034280a4048046801101e1401c440c9503110030045102400c61741c000e201c01d014415069451a0151000d0f01f10004c5202090403000c440ca2451619130f404038056401079a00c00ba158120f14080380c003665094103002d40e40b82c0f00741001c1842c10740d6940c010b81e50204804004101ca5054040340d0401012080d403502c040d031102c030100241000c0310300b4020050303800304030700340000740040f16015400543e0820001d101e030210040303140d15030030894803441c002c42100780040d01a0003902c0381d088000c8080c0300400341403800d610040c2d6142613450719a41305104044000d801c01200350801100019031850f260750f607513510100120b5061000341c500388240250b110208115101c00010001c042600f01d10603280042e949500340186007415140b0b095000d420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 415326519 1250 415325269 415325279
    0xa090212060f061e010933050306010e010801120b13050d0306150302070c090e07030215071103150402010c021206090d0807020d08010b0f09031f0609061d060406 71
    0x100041d445040c00030424805482c1101c01c2180400441e000340704c3c0740760810600801d59038007507031060948507030300110351104035500700e003081c3e40340741c01c000030008144000c050154a601034061800b88100307803901f642c684510b500540d04e1480900811410080b0202e030b120105040e40d1155030401c00c0304a0351003100713225440d424104008c40d203031400403941704e000030801680c5e4000e4840180e59075280440c1000301355910f58000f010075218200394951128004d051310304050100000542e8014488910301c1011140b040284c0c0101070207a42ca02e006c0d0100c641907080100e021380f0800742d62100d4400950f03455006464800f005074003a03810030b010f9202400820301c00c201c03c1e402444503100801da01103030740b040140b40c2c050040050045403c400c1d52001450b800c108400d0560303440e00e02098655038014202c003443c1c0202007070243d0510541d101c10716400c0000381c20102c03244045105108480d1510b603400155142c80c465080429101454144220320100c0d5007a04914010f102199a0345d0328 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 415327769 1250 415326519 415326523
    0x509071a0f091201150e160c080f1b10020a0c12090f0305060402030606010302040f060804020612010e10050d020d06050a060305060901020c070807120b041703101d0606030a090212 79
    0x1c060620f810b80d51041c2c460381410307100510000815078083c0030f4140b4074000c01110700b45c442d100040e206000b0b00c8004841017000c01015529810210340440b0f0f21384258000e4080c0c035810142c15074105000b00422041a0f40342d6008807010040141c45003901784900703a40b402e4005c02c0001c01c61003000382142c00030400300c00f00000240114040d10041986003468010076050020140c4000c0c10b0520401c070401100403005500300c01c44a01342170440d8a0780d11800494071905c2035036044541c928040703001050721400000c0d81c80c041d004000f03030701c43d0070350300c0313000340441060700200280d44080c50010b80d0f0006009900200d502242101000c101c05560f650f800340340440590b044201650082a44030002c101041808010065203004004661400c0543d55004a050f2809806010010700103403d0000305000f8649225410050355a280352942c6800a0701800707002c0c0c0e40059281518000c40161655070542c0a980d004000c1c1d0300c0c6460b83c040803002050005401c07600705c0c0600009107441074007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 415329019 1250 415327769 415327789
    0x1b040f0608090d031b0e040b042d15050609030f060405030d0e01140a05070c0c0303021005011d010b0c01110403080301030c050607050d03020a03060519090509071a0f09 74
    0x20648840e001402c0200507141040b102c080366034101440c03c6698504050018500e5410b14018207192a0880920000c0350291503802146a000740c24041d1440b40580440310003151a00c3d218103003c1c0e64102003940340155084203550000741e01c11072000b4000380c503008004120b107003c0141241c4aa02e814903d1a08002040700d09031815000030400702a0340f1030500401c603261003480c00800949804d82d00d01203006a000e041c8460341ca507a00d00080c888c5000724004d0782c0e0740f0b03004035880e00c04036500c1c41c0017561800850414400103041c4800064210389040c0e0f0318681e101c01d107901802c140c0c00d1400d071025940154092606641d00c0d140d0b4044940704031710041028500424604d0b940f503045042c0710002d944554002d5020f00390401c000408038070701150358000e240341d903e0003507541c07100c000b4210094405038206c10b078010036420074403039110401141c08040300c042020a0005e5a40c0d9400c03581c445005215005d00107500e61028802900e5810041840d81c0c291a1a14103091150002c0341d04100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 415330269 1250 415329019 415329029
    0x3001140f040c2d02060c0d0605130203070f050a021506010915020f120c10020f0417011a1e21010207120809010203130b040302010f0e07050f060c061b040f 68
    0x1002c2c0d40c0c218002c00005020200b0003d840c0001180c401101c10095031602d00808401c41c441d03004c1074a01d9800800c2c6c1040004080c010400c00f801e0b40710f01e40c1580258401e4a4042c0810500d11059090034000d10a4401c848400c1e005032500d170310800e41e441484140200f401d810401032660101d8001000d408440238030202e50300811540c0080d186442c58584031380d407190345004041c411200c1e000e00000b003d0402c443c40034030150f1540e0349001c0784084c41c00b40e42c101450402000c25031880f05181507101d8070071480e400c824020104001018000c3c01d40001c2410001d033310b21171180c10b1032410b103458580c1112100170100c1c00b088070107683e068220381100c1021600000c44d1542d0080540e0701144040c1c210701c5050013186942044032103400c40900a0030010b10702541c013030000d410b00d0b00030f50250602a510490a0080c40b020710703103003501d0f02c004d07004442c446d9440c1003078685207050040584a88021120003880300d038548081072155001800c182e1002ca032401c100c081200041c0a0045c40246 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 415331519 1250 415330269 415330277
    0x50d0314030a090c0b031018020720011d090604090804080708060f090304150f0e03010c320304060504171603090b07030f0509040906060b3001140f040c 67
    0x78003036240200b5891041c0d448550400c401b4006e01c08210004801c2d4400c03a008110341036002029051248c010703018540001c3d2118104a11058004410070403240d0035043c00da0360a03004840080c2c01c40301d051219010190803000000000b08203007810342c00040c581d8002e50b949c0c1e081c07681c1c07080307101e150810300d13040908250421010300c0720429a09a00c69000ba559801550526042c5403918001d00c11419806c0104a00340686c072407400c1c007a00c40700c3c0008501078000d024035401104041c285081881881801e40c0703540c0b00c0444020170300400a881000c2086031585951504e4440d4005000040e105503081c01948802c8001201442c0c010804080425800810760b080ba040103072011010307500640303500d041082a000020783c40400c030440c0d1055400c150380c0352901e00300401d00074642c11100800d11031908402091707507400304019100c055192a0703500c1c1160002a850030028a0074643c0500c003068034001800320307215000301008400406010f00241d2651100090291514680420301003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 415332769 1250 415331519 415331531
    0x4050102180108070e010e04060e1017070609180b090421030608060a05040809060f040807060512010e09030906030a0e010501141005180a15020d0c0c050d0314030a 72
    0xe01100e91a418542000b400e0854080c44d0202c000703401c0c02c94482500d81040f1882c0ba080d120b654942e8040c0000e81020305030744840d071070050808011600c05000c1c10540c82d00b0303021900b0114000142007425500b00b0395550008526107034140600174403503564005803a44401747d55080f038480c0d101441c407942c01103034080c45803e284030021200070150001c03401010305011041c4000103000a6454210300c5034440042c1555540c2480700c41c901a00300019400a0001503410b02121100c000e80700342c1e1140310503508000c0e500e01c000c2d1107a20034484200c0c0d00d108010010442c0c2600803900319402540d55058914210301c2000003502c6900844940700810754409010034001802d208643c00762505513580c660301d03c0c0c40310020f8440c030ba2107144001001800a8440d10300500d5800603c2200d00181c1240a90f82d01d07008020400841c51741d010005214564201c1c2c02e09218502190200303802018010703103036040c8014403010b41d02d0f6885c240c00380310107006180602c20848000314800c4054010000d85 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 415334019 1250 415332769 415332787
    0xc01110f0d091403070b03070f021c0504031502030601091205120a03060e1302031b01030e060103080a0f0305070e0409110901030503090103110f0a032c06060901120b0c0d0603060504050102 83
    0x3d00b0484100c0c250081d40005010321044d840c0748212500080c890503c9440070418403002ca18181500c1841c8008040d5000d0000101d60040054010b80b0f20600401c4180c05002c10108220702045518500080c2100310401c20010190044441e450094041e6000c94564205001e07440e846001924002a6146410860061070405640d082100410700340b0141c81d0380d80010343e9801051100d04011f000b980130300700c1184e01903800750644460302d01c04c0e140591396a092100443d00910481c4001c500d01d5902c10070000d1091103404d200f922551180c031800c0c1d400100303220040c80039031412203015200408403e86582c5180185000b54403d034010365542039064001011b840040b5a20107501c5403d120059040302034605440860002e4500041c1d0b203c0d428201a43d0b1440342030414819820718100b40c44070754004035881c4c1c0306083c262820032007640e861002001c5040c811b00701030700b00d04c00c480200b60160040002010000400c0e81d01142543d100d0f220b102c111a01554115040d03980080d81d080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 415335269 1250 415334019 415334039
    0x102040e01090b030109050c0405060307050406080f06060a03120309030e1f11070e13030e06070807050d05030c0a0315090c021c080103391706060a080c01110f0d09 72
    0x4660f9410350003070040c2c6010395950303a03441a041e040180305a4603840041c1d0592010484507000305801441071180382d031346946090300c644030300e45030a100d03018100020700f050400742045000c89500040104000080c854200e00600c80c80100b1003c0020f542c120030507940c3c031005440d6240c070842c900070340c5503c001200a030000c1848041154141c004d1030080200302513880c0e12540c4150714482d00b04046415180c22590603003880070713080d4403990105649081c0410f607406010304c0c0d4802c0c03048541d0b1a8007110191005d000403240703c1f0468a0401c451000a84a074002c3c072680350407030300706415607501d5400c00d5080c0c071715440d441c3c001079101c040540c2e82175040741c81c80c0c4540011030030400100e50441d1102c4210b8213800c080e070b0a07071622030ba44c2021014aa1b900002d8858403400348040c0d00750321a48580000d40300c440f400b4896100b0355001c2905483c2031242503007207a84040050a051030100c1c015200100a90019402c500461802404102c0c041c0188a880146981c07064452420b041c003180c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 415336519 1250 415335269 415335281
    0x1e0c0a06020d2f0610031401050f0a020a1e050c06060904020a0e13060203190c11210702040e0328090b0306060c0d02010501090e0f1c0507050102040e0109 68
    0x8560001641c004102d0700070349102c030000b10705100900c881c02d041032039203003910141481450621503801040a480c0d26000000d064911800002407c400f0703c440e11401d07180c040c2c4078080c1d1110301001080584801d42d00411180d2460306255410104ca404080c51701418548410049400040e291804040520205a01031800c550704d01403410940c000c9195540240540c550342d1602d440400c11180391a88403003100c907403001c13003950f8a00d400f2025490f1b19801410b400051403d04078407500050190f00c8001c0d8412000c00280b2040d00c002111081808480c42000c0c0b00020401481025032202e000c0c40d040c110300c4030001c59491381c1c1095145140300540112802d2420742510b025200c41d8008509000c485112103c00d0300d82c2c841d1170010b4180c4c03140080290301440344d061031148071501900950304036a4003000030000800c04042c0d4580343c1c2c00418405174142c00495401c038880c00055412203580710103142c0941001f007540d590b5402c9a00039000310082a409500402c200c140d02d020311 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 415337769 1250 415336519 415336529
    0x6030b060307051905060a020f1006030c0e2406070807080403120f08150a080a060c0f031119030e0a030806030c01090303231306030603021801031e051e0c0a 69
    0x202c90784c15810a0340c40e103001041d010765131203071000241e401c40f042d1080012002440b0300505031000c078003040c9615002844588000c0307035804002e080005030030700d182044a22418002d900300d000c40201c1a400ca003448041a2003a52022042c44864040b6000c00c0242c003000b031040c9609695581181400c0841100200c5503e0400c51400c1001e64180d0b4426146a000302c002d2440c0c8010130032240006d1841c03034803a04404254416644c1c440140801030300040c101600a440e0000015124401103060754030010b007078001c1c44402c006c0d1000c0c40340246203020000c2c26500e0006004840780728501d08000c2d4905055001074030320018881c09181c103024494814500342000042d01d0314503030b40600000b15000c680401d07400f520b04204003015485048454504460540b001c00c581c031502c000c1c2c01006a4002030740074840b17150102d81b070722002100303e0f030503203402080d03484141d0098142c42d0410b8074541401c82d15401002c08881e0384c0c9091008a4948021400190208411900901c00303a0042a844 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 415339019 1250 415337769 415337779
    0xe010f0b09030a1407030f030503160504050a050105030402281d1509090a060507050c0c150702061c0c090801050702011505010c0203071a1c090c141306030b06030705 73
    0x241d51107990380050703800e1645622401c005074105031440c905040102541c0084d00a200f24548481010340c000d00840c86819108084c4884809000c42112107000341d0003a2600074203039000502440d80100061544584001c2400803010f400c0491007204e29450031490b2440200c2d98070a0041403c0b2140c45119070404440c044014a0814000145611100140b5004545443c0410a141c1060001e40c26864219105000d030b402d203054001d0041d849000b0a03c051f005070880b030261480d200c030001c04003c03010301b49141481e0154081040b5a4001d40604c6001c0d8904035111404051600925411820030740741c2d150003d2500000d07900b5a03200916510469140219a03003032b41d90300042e48400c0d0b8901f80303882c11210300e091010914106668100e4116008944142584a012000140440c5400841d5140500300038480442070340c0701800003c1580d10202070600c80030701c2050860340e910300010312600030880e00d40c1e159400c81c0c010303400c151840c044000422000e03040804c100c00007850180c6d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 415340269 1250 415339019 415339027
    0xa120201091a0d02030c27030c010206160516060e0616030b090c0d0b040e01090507050306010b03010e0a0b090a090c081f0b0a0512070303024b070e010f0b 68
    0x42e02562902c01d0300000308074554080042003500c0782ca0703400e44000c1500c10703840302540b010800d082c000d50314075403146c90320034401d0b400042401d501c08245140214403040d21050743da280782d001924150000100d02d000081549129004031715a4001c1d0b4000d242c0e4170000d0030031810b02e400301290002021905d441810b00300105000c2039124081816484032910303244c140c40f0490108050090f000142041c1e1f4003a003080500c842d8a84198840080c0c28491001c541c3e01513594014151515400d10606405030000c0c00104822940c00c112980d00203a05007001910040f40000140f041009907200d601807990744192408008a0a6606019004110081c0b42d440e0312040359062850500300b60203001754842c60b10701c0700d585a40c5030f1040a010002c025581c040540140d20ba47d403c03103403100341d0042c400e85141d00800c0020801111503031000014040d90200c4215036003a41e08032685650080901d00780000300c3c1c01c0024450040a00f1a00c0c002c5034983d403611180d90701e41d07038803a000310740100740c204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 415341519 1250 415340269 415340309
    0x30906030b06030705090906040f0921140406031512080a020705010e0a0902090d0b04150f020306010f08071103030702010b010207080d0507020108040609060216021305090613110a12020109 83
    0x309803220358030221400c00f815622346011902a2200300111000710b0b0409074544200301c90142c2500d1402e41000d042d0b14084507441003111703840e40f01c0c40300e00003840c2d04002c20701c5000e100350044a80c02d0720b241c0d18440501e585041e0200f940083c641c09072108040880d1203040203506125540090400346000c0c012542800001031607001d5a01c5a804650b81c000751140280d107425000d040c1c003507001400d40e440c500e454200202c920300c0c20141010102d113040f8503000d02d44c609100740c07405420180e40f4003202c1502c0000c180da10100181000083c400001070468502e4010002541300303e02660001ca651030043d4000780c5000380d103801980382e50304078602c034030700f03465005054520582e02441c0000c2251034504040004003160400641081d000051031900203a920107100d0039644260f41d044804510f00c0e0b00742080b00c0b401e840d40c1d1459048100032030300d0090000700c9a40841d000c1e60391042402c030304400044901001e0351043c1c941c48040c252110039980c02c03142d04070041030007140400000c001c06c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 415342769 1250 415341519 415341527
    0x110109050a06050d0b1e090718120201020307050106031b090911040c110312060117040201090302040f0e074e14031c05130f0204020a1b030906030b060307 68
    0x1030207900204000480c540002c42d9a541144104200241103007010701c6c00c01070b10710701079240218a91b010700e40702401301e03017414810585040c0400601d0007030021641400341c040300c020301c0c3c43c40a904600c81413040502141017846030400840c45211030f44000004850781d25040e05c61030340700b4010305181c03c8210001c41c00ca03190001a02804940025046c0c0d48201c00360f4001c0200380440586102c00301d403034003030181406040b6004035002d80f1081d90840e0012400c0518041c2210001e00160390000c00b00300500701500901804540307a6004580f00103130040e80c52500b201d0341d02c0003605215410003210749040c1701c640380d80400540071b400400519511960030b140410810044020708985405405002010b1041905a01daa1061360303500c02081440b030b20302d02580c0b0403437039540d0b280c48049150317030032040c2e600e04016034002011010b14000360200030003034001d0000601403085890303d9a0b98441807480d00b4040171b101ea200d01e083c690800400604455811104c28040c0008105100c001504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 415344019 1250 415342769 415342789
    0x40b0106031a0f2809060f0b0a1409040c05031909050a0b040303020d0e0c040f0b030703080906090a08060403120c0915020709050a0c031406060f030403030605030307030c11010905 79
    0x209441c0c0000c407419480c04511000e010380100c003444061410503c00710b80d81d4604c10310490b00814028070107252103070b50440c038a101c42c4c81206c440346400c120b05480c490181c444d400341321300d801c80704500f0009010045820784841d0404040041c800108000c08203514026180010b42d03001c900704581400d03550ba40d0780da0b000b1000c0260410346003000180405100f034040342c08181e070b4498244004800d0900059983d07242c0c44405100320b0a0035841002007215224104240340d00a00802c4601c8c5151501c1c0c0943d489110b100d500b11004006040f4a601d5441c540d00c020a0068002c26a41c43d10b400c00400c00b07100ba8151440007402d20402da46150741c4007251800ba00c5e12910a42e00f060303240e66080c2d10701601c55003c0800c980c148000c0060071081680018002000c5071010320a03100c03513180310703000c41c1000c0b5213a076032198060010f07a044d5180807014640c0a07220b8100050078039151000607286400a403c201d0001e1030207907480003001003554148148010a00301044403c0c1000006444464 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 415345269 1250 415344019 415344071
    0x90509030708180d1a09010903050306010302160f0807150606080f090f0d020c12070806010317120411040c050c0a060f091a0f0f040321140a05040b010603 68
    0xa0104014001da410f050b8481030381d240003012004d1000c264540b40e040203000e91500c0c0b841008010001d0440750301805040742031540756813414911b6070f881c4010f4000307420407400619005050382035100001d003000300721340385903002d0001d5503200d030014070342100c4500d207898403480d11a08040040107035a8000155a403c02800d200440a6a0ba41018a171600400540d281c1c0e0383c1c410400c00c6600c103070300402c42808495098441008003140e218080d032391098070b8480e5565640c080b000400100b842400e2041854840011141c03070300c14070340f04510f18464251401c0d20f9141100b00c1810b081e2500c0d1007101c001038154205181001c08981c98941c81e488602d2000d4269034845031620030707140302584500d03196236100c11090218400f008803011284021110b0928106440011070740085c0840041c41c4219403642d9807801d01c108480d030002900d04085005884240c44200c0b03060380c14103642d41d540c403c02506000040e07920700381c00e0140300b498069100074280341c5020715000c4034407080807803140564 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 415346519 1250 415345269 415345283
    0x803030411180720070e150d0c0f0510030c08040b040203010b060d14060306040203030712021c0c0b0c130b18040c08091212070e041d01150905090307 66
    0x1029101060000075941c2c20303a010500410708210015801c0340c0394050707800e00c101080c620600307400401c07a82c039032541c000c07074072405140c100090424510041085003002e000d404060f40440503601e21001140341e4109988450251000788105e041a90000d9601031b01c40c501030109140420014100c1074019001811030101d2000203019074509400803603483c1c501818840e601d9520081c42001021403000c5c10700921203080c0070603181e03d40041e8240c00740390020061481c100d29a07480d9100c405020341001c0035406900c2811103a081a4003944000c9480c03620303022610203040c68803a46d414030041c20821014018480c0b0048050345001c0c500036686900e451a540f02540c520305100c4260a295a0354410b0804041d03410312640801ba190165000700c08460409103450440c1d0402c0c040c1d01d507034004c0035903030380c0002c0c10306441420400400c400c0074000045540701003050180b0b03030311001c807039000c3e40c1e4582c2244030b080840b041c03034200101a020030821050070030500c525203a1081410140180d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 415347769 1250 415346519 415346543
    0xe070f141b01060308030a0b120a0302340b09032e0c03140403110607050f0702060918090304150c081b0304170d030b10090302041d1605031608030304 66
    0x81c0c20254800f001454104030f04036140d02d088146180500b070303020016806084404660660700a00103541a0304903030540181a1074642c40140d24423010038100809000740075544280c020f0124049464054000a8500ea41c1d0700c0d041c00c14180b0744256002003501c035540c2c046141c0861210513002c09a0030303916030004104860090022009408a804078260f50301941c03050000301904441e0400c400f4007407406071412507507000025202400b40f141c51a08c40441040428018502000100301d00c110041400002640d0005440d4082c40200d81c5480c55a000150910803000344000d041c00e05019031410200044155503421740c98002c1e92580062032611030b40c52000e0003814802e0710003802d01c0410300b01d040c82e40b4003803580e9101d00300c0702a20040303440d1918001c2035003040310b00303216207165544481c0e4505240d82d0030701c001031064100f01c9131038150a0380062a150790902c298040b00380d10088240f00182404105800c0c0540d440d1300d488071401c00c6104002010020080c2c07030307205400ca100a604 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 415349019 1250 415347769 415347817
    0x130b060906030109151524030203220f050c0409030509060d02120c0d06060e01080402150d0212040b01050f0901060f091203020f0c0a180906020906040e070f14 70
    0x5880d030303800003d141c0c0700b81a03174444068079594003020211a01040e50303900e143e0383d0100380703101c00c8004806180c0c0941a42c0d104680b0b9010303400840d006100c902074000042180c06840b030342c22035038442c00c80707503070745e00d0302018041c44800c0201440c4080e00b12800c004a008a1750080c01600c100401e807400b0381c06c00b1948030308a0119505a60651000f40401703040340c41d11400c08001544420125410030b4074015002c19442e00c40d4a103000181c0043e140c5070040d4583e031302082001204055802071a0b402084003070841a20f44c000340520002415105003141040e06e4004003034041600124020b607002c000041d51a580d00803042d044514500f80b06038460300341c0f41c003168081e42a03002503000900003481c44081550000c2c01e40408440b031030a41d400229400c0c02c001c1045102c3c440d040208410040710303404040030740d00101c0c19611500e001894a8103410116608e07401aa109603804c0c4052410844400c1d0070102d070f004d44544130701d450700300318682103c1e0340210f000b542603400b8410144140012 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 415350269 1250 415349019 415349021
    0x3060509190e0a29010618050d050a050d0507060e06070c0308090c030601030b010314010509030f090414010b070b0705030709030b04020f0307090f0c020a12031107060204140405130b0609060301 85
    0x240d030450003003165203283c1c0b0300321201e404135807804145000300340000040301c510844190006104034261400f1407448d21040040c2404080b500350351600880401c0310000300700300b05159a03c540d44d1a9582c41e0718250604400701c4003030524100b40d58121360b040198040c1e0090754686000e600d824002c80541359211800e10303007904a10441d802d4800d00c000030007400b64500070719040b60311800d400c10152100400359800d0750300c1564a0481544207009000445940070080c11640a001d84009031400d41104c00e4041001d080e44200c18241c00043d1540c1070042040da0541c0c002420b003409807460411110003000c5044510024000d9205c03000814110b55400710804100c84008003194106c546505024001701003450108421910744144090910300100d4034250b0079403c2051540100c0700c0010680103030503030302c0e005034000008110300d100040440c07001d8802b5000d020780f400d0140040e14140310403100b02411504810000c4500c0d000001c9840400503070082094035000101d48680d800b0034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 415351519 1250 415350269 415350283
    0x206160c0305010203240d20060d0f0b0a18050604060e0403120e0c01051e0c0f0c5107051609020304080a05160c080a0303060509190e 59
    0x30500c0608100c0001840070540103580100c80440d40b0072540f040c03004e51072004a103a048019003103092580b24178080340d035000d80840190855109813507840304800014510f6400711045d103500c184c7c0c03181540d003004100d03c43c1d00700c002016250800c0481c01c0c03500045160b900710705081115516100015016211a00210300038100019440802c0c1080c0c03601602c001001e18111000070301d00348010b05001000521007400c80d4043c1c681514050b0400251800c2d9240707840c252440040070000c090146c00100300280c00005c1400250400c0740281c410000345c004000602600e01003103d200074005100b5181d501c041240c5803504600740c0d1148540200180c00c4403c4990448a0201d203290602c1004100e081c0e601d2410341e10142c5541d1200074481c124041554050304050b401c1c80154403980c06103000304000c0104c51000c182030b01302c9554094401100760841d00140d00b02c080c81c00c0c1011740500480014010840d654420340c901015440550700c551900005c182c0d84030300c8652043d40d07041c4150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 415352769 1250 415351519 415351523
    0x51e0102030906120f0906010b0d151a04031a0103030905042c071a0703082e1409070309020f100507050d050417010606020a02010c020136090513020616 67
    0x69140c6031018592403400d542281c0b4064020034a00c0051b10b040004100f560507070303086188a606106d030189500008204404402d4420a03211300040b0300c08a0800140d001001c01e6000182d0b21410351510000564000c650502002d20000040c40065000050101600c40988000070324003400f60080441152100715607266010810041c280004040f801e5420740e8520810001d1022818801008912550307401038001005000030030420034014450210000c0001048201008004801005411150301c601d4144442e1480d241e010300b44a000030f075014100c2d04042015902c0307500400c0318a6001d51080703228000c9055000811030040e07003901ca4032a000422103110081c1c07001e01400d0386d4064020b07206640d00c016045000d0f140140505803d40f103090307000e0301c0100030640c010b40c0c260344050400c038140302c42d91520042c114100141d0182c000145a0102030900042102e840b40d0600c07070304101c8189040c20208041c007920a801d10701c000e42e041c0c90041e5901c46041d56540480001080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 415354019 1250 415352769 415352779
    0x20409061b030c020d050f0717041a0901111504030e01020f010221012711090315040312090b01051002030702030709050103020415051e0102010e01060627051e01020309 74
    0x2400107142e4107074407401e4004119003ca0320717000c0c030300041610107018401c2c0f01d2170032020070899000000e00c0c200b80c082d1084081240c031803c1c580c0720100e102c580b0180410f412041c11001c1002102c0d980e001140d040303024840030141a100c4242c0075203d00c115002000541486130502d00e00b0703507036442001036160302224400215160350041105900c0c810001b040c0c0c8400602260020610240911416001c48480131401140079150b6881e100584050004030354601c1060020b04101d4030244400c0580c50003c06242040307191078030380a462000c00c1445c41c0011440c01d0580c800107051005080d043d5881101c0c00c2d8035503400c01000728610f10650b170300250140140107000a045243c1d8200c0d9058910845052110310300341c0c101c0c800480264840c0e60361002c2010800b00d00006a00c0e50a5890103040c800401c1d00402d001c48103003516040da000e007002a40c00c400c11199100300c01e0b141e480d0409000000250b003460000002c09059040801c0b10310420302221000c2181c0c02001140c01402020304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 415355269 1250 415354019 415354061
    0xa03031a061201030515090304030609050c06070503130b0a17041e05030316020102120c0711150403111801170708060f010306140f130c09020403080a09140d02040906 73
    0x602c480c40c1002848100e415109400ca0301c02040e0b207094405215215680046007014515103450000e080300711806d4610f401480081074041d140e4a0013000e03441d001b1001103503140004841e03a02c000b0810740c000d451180301840b101c00032543c018444500c4007243e4001d100303951540d007004620315005103580e21503548005021010884080040d502c21280341c4a03261524003500d105909074800c000a04481c50300c161f002556402e005406061194000c11451720160084404503a020640c007080408050010804204105645080000ea00320a5400c0707122008500c02e040b20b1414103000d0101569001c050300c502000007045050000c1c60000103e450038149117030b0000019600307001c103545060620300c01c40d0041c4d401c40f164074014107041d0382d000180e90741c00b8046000403000d00b1049412584019000800325100e0000c0c1000d18002d40c80e155584440003009080c0c07410301e40c042e92100507038038010b1555a58060311a240c2d99010303900030503100c40c2d500d458030040028609880b58224240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 415356519 1250 415355269 415355287
    0x1017030f180306070503060a17100903081f030b0c030408070804030308060117100506130815071e02030f030c0d1b0f03140411010903050a030e030c040506030a03031a06 74
    0x1c0c24960503000141d043d2015900c42080844640c48221841d1360407004a5000f0042140444006072840845c407007503a14007600840001c0980e605800c050b00020000e106006910708522035a108003903114100c4000140b440d9500100d12100400c07200e414a008070014081c411807038100c900b200d500142c800d035259224540030303151035015203483e8001505100d0326209402d4540441e4082d900345241c24405524003003c0107002d40c440700301800c9501c2104400680200d0400007100a41c4200032071510520703050400818520006004e60b80c0300440d43d25041203107801104030b949003591442101e42c1e0755115154114540f040d45070596089180160702c0c0c880003800090600c84401307a0341e50305040e44c0074003400c5098841540f400040070805001090008007a1107c840d05440107052000d4a955207132502c5040000786582600401d85e1610b00800502c0d060010a0180108950801c0603060400c003007a0b6a03111560011300741079441c00002c46100d070400c00b1980180000780b0039955800300d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 415357769 1250 415356519 415356547
    0x51c0812191d0c1e220b0d03050a030504060605090403021014100509060409061503050c18010b071407120c1d0f041b091a04051017030f 60
    0x40200000c224a803141140042d10000710840d00d01d18054010104601c0c403004010038007420b1000030030348007162400408262100342c6420401010028115501034110545409503020409454401c0320110701100001f5001010b40d41c8840c1e4602c1c0004003035a03503207003481c01802c1e01c1c0c000b2580325043c48108410158001924844601d44000500012481034102c0d06840d10903100c6030a074064401c0c040c86a0b040c402e8a141e0301c440024404a180c200c10384800080b14140e0f020440040014041802801010020f2114904081d607010704035603402c904000d13009606003d24021410006856424080350400c180401d10101013902d004a5071261941c0340b03070030030b6501114441d02012001900100c0268a1041da0090031084549642c52001d90310000350010400c40712907070561022510704180c1c80c4440c003d440012000540d140104128880344100ca22049210300e00305400c02c603800d0540224101104c9043d06403500451036445000d0445c011640300c83d0328250081020004a551 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 415359019 1250 415357769 415357801
    0x9090602180d051b010c0204020c0703051204060203030711013e031308070203241009020c070302062b15060c121b0210110115051c0812 60
    0x125611410400d0509010301070b010340c48140103000c540107594401c5000c10705400c00901d40c0c00500d0000381c9441903500080490700710601a0384254810b0b41d060040000421070403078078801c0c40d4801c3d41020300d40301c0003d41e244402070481040140b04001c0d001c001c0360941040b11145024000912079400510401400a6031030b07104041c007440703810440940c40701c0142100d008188041801088141d2034841040300d6200c1c0800300d8140c80307031130030840c2e24400200101c0307000040c0386a80c04450901003c600000009901b05030419171041200400c008400a02102165410b0712402d48442005c0d400101c140c85042e07a0a044119240030b070201d0f44c609910541c0c80610110f0011000b640340d25044034580205c440043c5a0390561252511080c00740b08107104020040001c0081c1c107041d0741c0416248c40c042004007020400b15624001414000e001d100040c09451081d01c5107503290000055014104405271400b5100c0d1140c0c0304140450402190154000001114105d0800c10300150784018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 415360269 1250 415359019 415359037
    0x807020d1101030b01051606051f06120c0528050d0f0203060a0e0610031503020a060e01110105090c010c21261b1606050907090e12040314010609090602 67
    0x302d070407000c0050f036001d90107a48110700e81f0700303940094180c195200c400410000e4100c020101d41c880c8002200704001c050a0068801c0f5544c0300c0403a4080d000d0541554401c00c0905c2c240001400440c690300b00c500c4840140b20001c2060702d51404500b907007030740c0314800c00302e01c1c1118a080c40620b18070342e111600218000c41058602e02c20036562482c4a4104580c142c2e2210351010703031000000c80551085d0491840103c0c1d00650020341a52580010703042202c035404a8081400b4480740c0c001583c0107002c191400501100a02941c980840300540740c1e2104803080d8107004102c400319041c4015001c00b41c01c207010020b410400042420409001c0700b1758070b11802d018840c0f0414145482e41c5502015006204141030030650800c1c2d0341c01c203a102c0d0061001c2c003030858980c884c0200802c905004040c081c070100c00243c003000b030600c00c01000f40c1d060140c07000c4036940524445092580c0c079504a40899401040c5001c18600041c40140500303000d5005414940c240000300050100a5000f00305080d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 415361519 1250 415360269 415360271
    0x103090611030702070e090615060a05040b310b0417071e0e01080304050901050f060705010915060b03010b0f07020a03050307030f08090d210920040b01020303150103090807020d110103 81
    0x40c2e200810715032350700f108465642e144c45a0b000c88500609194000c0d0501480c28100242410f4594a80083c0c2c1d030883c011035803440d5042d0319509046102d42c020b02c41a9651610042a5981058103c1c1001c2c40317144144207440d8141c0c41c405031964410300044014000c1031031310010580070300341c8004200405003ea5039803003c40c400009404000041202c040b50030150080ca126840c00c010450755603441240b039900480e04000c102c0001d0307001c0c8a5982c5081c17080c160104140c080001c500300701c0700e441c0c01981ca0400100014003441c40014252960105003000603a5605ea4901c0450003291351a40000c005210108004080540101c1212159030b00c0c1c2d61082c403150781741600940e40f072490094210126041c80c002c03107449404000da1311300042242c8004500040107a454241803030a2194100f030003400000c400f23080d0b140502900a072004244011415802c220115600170280c5602c40c3c0e040c95600c01a000421800d0f0302980c2d1815002400d0000903001c07030402c0d4404003103102030a0700007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 415362769 1250 415361519 415361521
    0x5120c16020a080c270408310303091401020a0f080408060f09010c03090206070605220c051503010e0c070c0513020a030b01052110090e07030323090103090611030702070e 75
    0x1102c0c6134801c25580800120701d20160391a580c440b86000d500c900050f592001200030252802e08c442d100207240c00103c0401103030114a1824010003007a000d821162200c440c4020009841c1e0380000d001d82e516070030210b0101101c4462921404c5485258010031450040d6000c100d100d00f00074000503c00c082c136400a00c00e000301d59008604443c070310403009501a10910a18001c078030107130311155115808682011031100e86031003c6a00042c90401141d2619144030144010705007103a8480074180340c2039849003194144441030303443c1c682c0200b00c2d0340b40380b4021503400d0031b06c0341c2d20304024000c00015006020182120030040b01075803200c1d500c8004071b4146134992070b09500c20b2084680b1441c3c07407440e501c0c40074040c454a858804026281030320920303462901203642201481041d400108040040203141e1542c90041d10904510000d14900003421100a40102c2000216010410709180009146004d071404c0b800500c816400c0f025510004402c00004940002d4150152807001f0301543c82 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 415364019 1250 415362769 415362799
    0xa02090a1509080312040f030215010f03020102010609060b070201050703090905040b040203160303020d05070212070b030f0a02030114040b041d1b0301090f020d03020f01090303060e0705120c16020a080c 89
    0x2d01c2c03151700070030000410b07100c000a0200b0000ca240310349503407080c410b41c0c0440c00c2101c1030083d02c28082c0c204908402c034a1104000f10760302441030230014400020144450343c9003080c901c415010b0450302038103000001800350101441000e9082c0a0811071108110600342070400400120044900724040d2081550288402c051622000202c070350643c0101182200b240c1c0480703c680012104981121620002071241001440b004001d03000120b0381d0f40e200d1424101046c504e03000035100565481c810001845840e07100c00c5034541b05041520080b90450b80000486e0090101d2401c2c0d07005d00d000841684c4000c600821070700442c0c41c03121a040c80080c004030415088419000c4001c040040140900d4014108500d250701c00a0080c01a6401649002070351805d440e9030180450000b55140030500c20320f0a008810382d08009645030081c00c1800f0121810244103010f0445460380e034000c224000940c590306e07002060181c0c0075100d450300319650100955074004488106218414444c0d031000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 415365269 1250 415364019 415364023
    0x608160b030411130e0303160207060903080d11160f0b070f091509050303030c0a1b0506040303050a0f0e010e06220f0201020319020a0308011a0f030a02090a150908 72
    0x2c06180c1000100502e003e000042100d01380000a600900a8545089034010341042c00510b1007500d520140c11140c1d04c80c010700a007804d0060304403205110301e00b001440400d00901c1a2106281130b007000040060f01c0c4215030150780500e01c3e1a03030100b240064002d0404c00800401c2000500c1415071488030307110303d613096505c410106000000910350820400015206088111040c80141001800b094646000c20f056600c12141a2400d11000070780d00400c40d4015a0756009610551044600000c2c503074406840c1c0c0f00140010f000c0580320000305200c0300322a840b03008900500b04042104a1000c04035502070100d0f50185039060158034002a131000240f401a0848075100292000c0d01c0840ea8400b022420a03032410b07411440180208080d14104115001072040d03113030000c190b285910304e002403030008160040811824500c1600d01046805416211466115840701c0c0d02e039954440801c009015004100c0d0340b02100c1038000810108101c00601c25000b1580c032010110b0315100741603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 415366519 1250 415365269 415365271
    0xd020105250309081e03010e06040b06030f0603070b0c0714030f070b180a12050c0d02060a0f0c08130806010f0819140604063204020d0804090608160b03 67
    0x54044815414031240c11440380d8400c800d2188521041414103052404e03841d06000c000c03201745401d490010040c80103960300a881644001e080314140550541007004c40d14901004c4e1900c07821903204000700728503a42c2072011300007616100d94500d440700c0742012080d80c1c40105114024030701407003042c000e05605001c200740070300f4190744004040c0c01c1e180552001459101c1c051100e00380c0d8140c0110140b50b41d42220b08401098058403485003020796003001740c00d003d0180c1200384180da0708510fa8005072140b5047d05e81d0700300d107414103030000754001c1803d071002c0c0000307480140904800980c02003012004041402070ba50034804940d20f50380c0b07515140d0007091890103040381591001c80c4001680280890a0341220701c94000ea204144d6000c11103840e20030180c0e000c494039602e031a0210032141085200140819031051044a02d0400d000d4510f020380d000360020313000b10b80801044082c80040c4080714010941c000003041181c1e5901e4119072603c0a11400c041040240c0c440000d610010109032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 415367769 1250 415366519 415366561
    0xb1201060506071b0e0420030d090b13050402030f0a0b0a0803040e0c0418050103111e060705010e0d0807090b192a0501020904060b0a05030103030309050c040507020d020105 76
    0x15152011030313201c0c503400202588010241d41010341011070700340d13001c2c0d2000c3c0c0140d20580c4030800b40105100300312082d00607002d00c5070080d44140074900015503c80c5005084030503c0c68000d035212201c0e4031f050003035a159000030350400d00010070300070303243d400d040ac103403040d64dd04030200010800380042050b56034013071141840a40c000c0c00240051095480403c1e0402080045203180a40d1006010034440903001e488106d20740d0380c0010014031002c01e40241c00d031442216000f6010016001d803004036824543c1d503500902c0c0104015080000942c0301021440401301151580000c1d00300043c2001704c225112000211050800943c40c0070400941d00e100710031540700b902a00320440222443d400c40b00040301d4405540d100d40c0f0101c1518039803102c2903401040007699451601e02440180d4030781d0340c007407220f40c4003c00c658078100d580f100aa0741501e926103000b0842c0001410041d2504010b8058641d000c7d141400b40700d5440d4000821020f0030310203070000d110b5941e80004c8621550760102d11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 415369019 1250 415367769 415367779
    0xf10051f090f0603090302010c0203130e04111c17160b130b010b1e070b0402270c040e06090609070c0f1502071e0c050f120609010b12010605 62
    0x100c020381103020600400400e11880c200c01000d41d990344445049100e81e105a000c65920202601859070a0003510107509031400203500c0e040940f598007074042c020780708200c0c05036a400c01160030441e520b8840070160000600001408a0b41400703011072960000e400c80d81600c820070a82040c00c055401c1d1460306541c82546c22441ca103a0310b4064031002c00a00e20204d00104905a40014804030980c0e4041e00c81c2c036003d00c0e2543c400c410804e0340c010000c621440d03b20b40c28010100010f0b8201c0ea01070f40640d0581c2c01008801000050403550802d0134540000c0d04040000c010903c038031a0054411034604001c81001521200c007849002c1d00151919600000740320000341c0a2401240c2d81c80d5090b00c6040b0450f0410b141c1c1d00c607150006032100c03004c0e10301900016030009010621284101c0c48614601c04050500b1940d50900800b800c5d204041c0592801030b1098040e6969000c1a140c0000b170800351441450040c0c2401d00804240300c0f410300c0f9880300a030240a00d48148a81c000361a0701500b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 415370269 1250 415369019 415369039
    0x7020607081b01200c21280e010315140d0f0506010e0105030f0319030b090403030b090a0b1302030c09100e010210180f02010207080a0b0f1005 63
    0x2440080e600001066840d00410484500b070502d0046000c003203889002c00000d244072801c000c07941955042d149040003110140000035601101044000d40d4071001582910366480c09010202c41d8001ca01d07801c10482034a002c0210506016452074100d5002036031803d880d0030fa884019811036481c4000f840102e04064000e1189484606480d00140c2004041240c0380030f040e51255a8206d0300b010854150300440010440901c851421901404089024211a88101034070540c2ca0003120510001c412049018040140c000e0b03018940300311002d0140c80151416080180103041560020fa000300402030001c0c0d400040c034850105070000080034642e0300404400050043c0d000076041d0038002d9400c10030001d0b150b440c502180030943c107a40b9807181c1401060006410100c14243d40380d0b0050900d00320344000381c070002e0401161036015040318039602040c00100d151100580000c02188110749000041c010b0f840801e52241c4141d032403c3c0d5095035001c0c110901c4402c3c6103d803681110501c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 415371519 1250 415370269 415370273
    0x10501030912141c0b030d0e01020d0305220501050f071107030b040204110403151401050d08070302070801050a09050705100f080a0b03030307210504031e030e030c0c01020607020d0507 81
    0x140311448001c8003020201e0070465158101500d51300c1c070780141c15005513140480a100e0070240700441c81520346062900700c042d8081c0001c1e494501550404042540d10400162001c11002182c0117075180d43d24020241c030090320740325008007810350f10482c28814401c00544410300c20304918103144400c0300541a8685559100c1042640160041340d01988030f5079205441d41200d009400154000d50150340590b2901050900b01e80a0810070585041c8e00b100501842d150b150701c5044c926440302c0c0c190784d6800c040c10202e062401c240c0020070554201400d000c50020a40c1019005d2805881a661071a03500c44c00c124209440103003060205054500c82ca00c61030050350324940c44402120041000041d00b000641950300071590800030502c1d0b222030040c950541108920300c02403034a4104105c0c01c0548000d0840342c1403002c515031841030941d0000d01e42c1d100741c100fa00b11020000440307481da03403034454480c0c0303508202c8d141c1c60062103200002814103100244100405030039483e150320f44555a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 415372769 1250 415371519 415371527
    0x7080f070504140a080a030512180712020402280207050d050d030519050906070e240307020106050a080606040528110405130e1c02190c03121106010501030912 70
    0x4000044d510502c00d100c00a8000014080003403041d11a942d0a42d03213400100410002d40340260031180210950718052941280005100c0c0645510132400c0e00692850320000340030b84900c50b5401f60708040380042d11040180903162502401494003900d9440c4d490788140b150070300750410042d0a65104118500710390780079603c4160440c072000e0500503a0742c0c20111800907910141d034400030b2a407040c0208130140e90f101d104c1200403182101c1414541503040081e260506002e240b100e05110000042810b0900075401440100800741c0a07014031135880b40f042d61108070442c2c59a0245041c400021800507031404c0c0120452007180f15140341e43c2c4444401401045a00701742e04030b8071700800020809a4071fa000c2d13540c1d8411600b03008100d40074131401050610a0701c00304290139280da0803030b0040c0c5079004102d5a0103283c001c0c6804054501a041c01e049030706440d80041d2050400004842425a004409030032800c2e10204482450741d0b5600110104e074610f9902400b03100446d82510000c0340b00b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 415374019 1250 415372769 415372799
    0xe0a0c140303191d04110a030b010504050a090b0306090607021b061312050705010e0303041a04030803040503031015080415060f0b070501050105240c010912050307080f070504 77
    0x1400b01d0b07043c00090403450800c07844804007403000c6150810081d0b19452100c41e80440d115040e50207004080c07545006010900445400005143d181c40311500c540c3d1155003030740d00070000104045e200c0b50380d402403e0000c2965486545c06800340500240d132100d00002c400b80240c00b070b980104160480038120320840404680031542c8072004010280d42c2d809200380820251a0300040900e06010074581540346c9012680080c0c1440a07004141000b41c2d03021040e1800c40700740b403015220005e001c4600c0c402600c655000103040500c0481400280074000000d144240541d039206858285c43d00424143ca00105000b0f40024081400140c0054400b07125450200e00071100030601540350040101060136030b40103d08041e90202e204414481e003400741500602c007c7d294080d90340c0b42101356141203503c403968100114400070380071155001c01d41c015003c040c0c00948000010301e802d84000c1295006880b80d0300003820140c040381b103038086403103c80e005400e140c540920303062070042146101d1803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 415375269 1250 415374019 415374059
    0x50717031c050609060109030b0c18190e010b0f1603020c031b101b08160f030503040b060105090102100b03121308010510080703020f0f0612010503010e0a0c 69
    0x10611240000810201c1d251481c03a0600002055a1600074140304e030103440100a94100302034410200003140d00b001c0040c2d000010740120301d40e11100c04003d640340c06039a00c0607030340000710308001d241c003507070695014001e68041c40c092083c20790742c0fa00309030b050f4003c4900d00c1c0e546c200e003000211030701d1100c11b00070103015200340141d070540301e4004000307400c01401500d003007407452807041d135a221407074607540c80b584140c0300381400005582100d002c402c9a440c1802e000b0660080000d03605070418030580c100100540c00b03034403c400c2020514000b030003504142c508603408038a040114070590300070000d949080b070041c0d0050200e61b00c0900d80002034815040703e19094003c480c0b04240e04000c1c4401408035900180c20407403020328261240d42103c00040510100b40072494080c09140700116a450881c0d4048a0b65003045035603c0c00548601c0c04010f0556202000184000040011030301c0b0a0480b40708500802c40720310310f5401643c82d00d003021401001048a0f400a10850b80242503080f40e4074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 415376519 1250 415375269 415375273
    0x60603040c03020405090c01030c0315050f010c05070b07110604050f130b1e0a090905031227101506050706050405151f080a2f040f090c090603050717 66
    0x1607940d0f004101152001d13241c217a081d030021840d01543e0b581501440a05d044689400c0100850340500b80141c26200e01a00c0d100d800303000d01c1d00085a1040c9000709540d44c0200a80b84400da0355400320040b0350000c0401c6a8509840402000e5441d006041d40c08440300680000c2000902004006a1007000007105580c07070358441c032009072922264a829055401d503c200c1c0c0e80300907c1402c02c0380c0c03021654800050a820305441400048010082e204406540c45032001661503160030300d800c508850b180c48625074484000c8041600f0000b81c0780e0484400f200342040840801c980406070f8400c58003400c80850401c1020000260041d84a42d90140c00349041da80c40c814000c1c0900e40b81c110075201c11900450090749103240500c203a80b00d000404084000b0300800c03045d60780f002206180c0b100340d9003600b002a002d5080a82061007004001e201c010410482400308a1540c0300030081d401040d1844a10a440070400c0e1069202d0761007a02d81050082501624000a500f4407000c003114032100c074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 415377769 1250 415376519 415376543
    0x30e0f070b0702190f23031203060907030510050d0206040909081e0301030203120c2b030c050f18012001320a050601021e070f0510020606060304 64
    0x14028031444000d07140707000426a50320203500400c40010480c0424100d03066044604114a1810701c4c12034040700c1002001c0c000b8030300b00b0602c4c006690b01400840303826004032440e0320b042e042103400440c45180201d5040801d6110203101314101c03142100d9100c002400700400b800203160810031489018801082540f4060300c0302c081d40283d854513001100c4030800803840d044c2402c1410782080d01c00254480050640d0b00d507800107503407031044102e2440c0680000407160321162062084182481c00f2140f210042c8003840c81d40400f400307004101030000392601000044880c031035412980300c511504543c60802d00ba9595075005041025901418882c0100001d26079402c80c00b81d1450100c405030000031644182d84500074500b0718406041c440800409012010308032208400b500300144580005080d5200d100503490b02206100700309414201d154841e40f4200c0000d624019225407918582d0302a03034610030700c440d1080c6171101c0005030b001000020068180800034590084c081e00910800c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 415379019 1250 415377769 415377793
    0x140607060212042f0103091109070c0c08010b0f090901061a070201081006170726180a050703060c020a12080703050c0309100e011103130b160f030e 65
    0x12a80304030031500c107404052080005000d1080d90151500c9228a01c0340d20b4821252078100c0709113046004030341815601c562100500c40070006d59600604050902801ba042100000d003110800402c1281c1c254028078000c00e102d00180110803000c40040e007030100c08404401001000000205a40d00b10f40d82c81c600000d280407844d1030f00c40e0660701c085101c0c2d0349075a680001800084000c29a2070f5080e810a401c03c2003940c008140c02c0d5401000780d0000c000d459000d42103c88072007140d05614260300101c1007901c5982c600c501c26004080c500c0c00030011460444040e41c951000c0c00001e081030308259010000b00d5100d811009240c1a0b6106954911016540740e00210b0303840101c1c800040c007001d0400007020381500c600343d0801102c0000701c1c103525008021a940d10601144046020748400400710a03200c00d400213102420150110342d16842c000e0768405103102c8002064403004c40d14408100c0d01c0000000c00300000342c15070b0380c12198015401c403d4020301001d080d400e0b07d5105521188078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 415380269 1250 415379019 415379021
    0x9011d040507180e06060d09030207031b1701050603060c0c0c03060c0a0206060102060903090d03090e0a05070f0c030801150e0d050c044209090b010e1f14060706 71
    0x12044100d0b44614007800c00108140401d00d21a41007141c040002c0000c0c00b08561b07603801600c00724107001002140001c030034903089040001681c0b00600b00038203c2c0102114079130030000d180c252400140b00d9408808180b07601802da41c0d007a10314607056003061010410601c0d04800421241c01404122000402210040303850810221001d0a0350712012034103114441c1e052191580151092004010764104000c04907240d02c5070058040c031450325104403804041c021104200289481c062090003890031504203409400200d819100140030b0844800005020380013030407d4540650321000240e08020114880c40785072040341040c03286202c0303210410364699041c60042846080988440764500080c0f00507109009a008461466083c003040b1005185d11000346001d52081441760f000d1500221204502c40398114035a2030b41000d03224030a1061100c00f8034125011003608144c80c1e5218004900c8144c40300304a0000c0d078030002c0c03003000403400101e13078103107010001810341d4070300700565507104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 415381519 1250 415380269 415380271
    0xf021206040305090f0d02011e0e06030108010b03120403030503011206061827211b0b040302060a09080a08220b06091303140c1002040b1c0b030309011d0405 69
    0x6000a03000959800c03103050100700390880c1d840a4880c0800c1011b40d5002a14280c00c90100b1110001c0c00d441d1004500c1c82640010103002e800350046030380b940c5402646018001c1800700f2800780c40b4140c0801407240c1c9003011034085a0709581e50301d086909003460b8010f0f15040b075005803001034035418040b0307903105070040f40200720f0424040010079240000b00641d481080038040039100b41d290f03182502048040c00c00001c0684010001c47c3c004840803411b842c240705070703034950903103c0c2441c7c050b50800c42d0f41c00c815030003180683c0803508960b031100e1080c0144c030100e00e00204080c2c41441f40c03c1d100d0307010fa18440e07040307081c2c1460244c9224900c0c9080d4004039140c2c4096a0010b0108144002420100391058200c188100d030800a11900d840c050003000701c40c001c0304824500090300c440b2084d8144808a01b000c401e510541d070307036681c400200b01c1640000d0807405091142d2042c0c010941040c1c81405011407001c3c000d14113160420005440350001e1556962118065503a40c3c541e550320380c4920703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 415382769 1250 415381519 415381523
    0x6041809061104060e01030f200301320405130803090304030605151c0503040909080405090901151203170a06031403030f0f0c19080601030f06050d0f02120604 70
    0x41000d240d050010a40341c00d800540d00c0300804000c10b004007a40540c4280c0000d50a007408610380c100da0007010001c01d03c190640840000d607004030303100340c0700940080d4100c03510707c1d4425030aa200f0804448140c00015007160400552012a00130303428140c1100390310002c40c4603411010300c129150002c4590080325080c4507604001402c0c401c2001911409030401442c40c0e01c071030b200c540107022810610001100e4007034034940c4441780d405c00c0010000c58000e001041024484140c2d00e242403400f0303811034020640704103000400a92404014403c071800c4062590703602116614003034180d00f000c1070040e030035410481e1035121a00b5880e05111074501640389080c00250080c9141010380c00310116817800d403001d410030814040001003038045642c004554064841c455128090780d51803900c10b19989451082e42400e20341031081d0000d020038410802a2002d20100d0389110f1001e04403150380c080c03583d008941701c0d1002c02090b540040d6261151018010310880051300681d50b240c1001141d00b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 415384019 1250 415382769 415382771
    0x10060207060f120e0d02030a0f0813020d0c2c06010e10030b06130b1e0711060307030e0105090c030d0521070c050316150509030a0315050409050703120203040602030a0e060418 77
    0x1e00310040d5444200c0107027511803403904c9450b509010240560390310f03d905c0003030700c1107030f85150701410311554a4240e4010103c18411040c254060100701602e0390030100c0d415405080e0030005042540a20484009540d00403c0110800c4101400b0390051402e19015504071400344005010351080c030340030300081c210410390503403103245242c440c80584035460747c1c3c40301640e400c2c042c410009403151141070340004122072060301e980e10040110700a10142050000e0340d0300341014011503031408600509032180aa06036040300c446810284c4040c401c142620188a0381c41c3c203000e0300d186410a80c1e0b60010110300e0101030680450703c1d640d01c0c41c0c02c8154010600034100c1030701c0c41000200741401650345034403003081c00740d85000c0412940324021180c444040c180c8400b243c140c1c0c41009034040c0c01900c07000300304001341c0b003c81c10000d81d20001d0340000c076100308408080c04091070000003920300310f07082a4021440d00c1d1040e1000c41c0c08250400040ea000300b01800040b0303014484892080e0134070040d40c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 415385269 1250 415384019 415384027
    0x1d0a0303050f0a060501050f07030e09010b0a021c020d030e100c052502010804030302030612070f030506060a0305060105120703050105070c030e011d0f0f0a090510060207060f120e0d0203 82
    0x102c08140140007400e10311209150010800960b40c00400391400c051541c0d00b015122000e506081d220010441d203503560000c5200008184044658060110901c0c15400c4448c1181c4031000c01042d41031111141c4056807100c0c040c0a0100d1007a01302e402040012820364003d211441600d100340c0f44500b24500120b640440e000600c46000001e424107031941692a4065203865000a458140050409810140c0000c001461340d2641c1d204103c40030008001c44041c580d41e0001048858001e02088076540541c1d40410918030f407003103411080d2a00035001e00b080d646880100300b036644200c0a405c0040c0138400b030000210b1000e00c5994810f44082e00c800104040d00d1a004107400091440305050203000352003182440305003120454211020780382507500000e500e0008840d10a00340007542c4c041d0f03020070085000c2e1442e0304100e00a080400205500648504050f0f80ba0707000c90198000141c00cae241d803a0902d910038070011080d070405200000740501d800f0007441c14041c28503160005644001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 415386519 1250 415385269 415385281
    0x5010e03120c04030b15032a19080601090e0a08130f0e0f0f06030c1504050f0a030f08090d06150501090801061a07030201020c0304031113020c0d031d0a030305 70
    0x78410961101d0020b4a042ca01425640d8045203004080d00316141c007101910511816141004071300c0304541500112070f080c8450321031044990b82c11441c00d40c051011108006c1c5800070f80c1c0000c500381c03201716002d04400e80c03c11300c208004000c4005022100c9c801c1100400120354220004c00401001079010f0301d81500300b0082d451a000c1c6940000e003820148000c200014442803041904550b040154502d2516a84002854100c0d06c0071081c0e03100c103a03c030640a10001082c0213004960040d00e0b10007461030440b04201041e480c5100103890844940550740000b42c0d0000200f60341000249001c401c0c8140380c0b10310040b40c108091107082d640300800288625038021000e0401800030304000e200d100d00340385c054040c9248030303080a9801c081c041203800800d4004e4040d0b0790b20140b410100d036221782d030b00c0c241820000078180e00b05025604a107040c00300c0c214203000711400038031244014000024550000c800410045d0300100c03d940c0c0800010103404010b010181c141406554007245a00b020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 415387769 1250 415386519 415386547
    0x41b08010c0f0e01081501210203090c0301060e070507020d0f05060f06040b1e03031207210603080406051c1d0705030705090118060f0303030c030b220c0c05010e03 72
    0x1c00110003c0c408107100000d007a030380c4070048603800803040c10400741c107214080040e00c200c1d905030510002c0900108100d5121441540607602ca000040203c40410305041c0c00d043c05c0f0344442c06500b41080d909800540307014055402007483d2440507011418020b5a82c45d141520510400304580039000303a4107006c034007107544600c1600407404980c00c0000c44030759070000f000001e100b070000106010840021031142d600740150b5140da0b0355401e0404041c54018802880c441d000c0c0d00511100310b030401d01c104414124030505040e2940901c4039441c06062000684140c0c010000b0700b0440720000f00280041080d0b4000c2d542000b8901000406031041d5410361400c082e0f5640026000e40e0000f60208650b5a5100803036045801c4100c0000f50031001c00b0301030000d881c90f601301b070385000205540041055815030040c413440255503010450080944208400d4012060302400520302c08070782a01200a280c0c80040841c0c41030800091864096035028296904821080400e070004101d0321580001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 415389019 1250 415387769 415387787
    0x15010503010b12030306040b0d0c1d0a022104080c010c0f0e0603060307050f0316060f11060f070f0309050a0b01090e0a0b041209030f141002040f03060203041b08010c 73
    0x100c2c0d10340030f0034015254140da00d02000b040188160307101c1a0301403141c1c40f04050404030640008004070540c0d200e130075071484800c52203020442006180c00107009807105100381c40300e076050094152076000e541d119410214038003500c2a194214104100e03400365109105001c9035070000d4903046e400350b120300720141071f09121034446030052404008010403950042004c0c0700761013085585250560301d00001c203250806036452024540b100e844080740003a0070803003210064245680b658000d4a4100c0b901d91102810340342d10100d05040c5020460290248600c000608480c0c0f0300045c01c5042602c80030b1410704110000d68071420580018841c001c518050b06c001e85016900070f10300c0019554840390321020040019100c640e05500e01d48000348940540320045070000c510103010003036800c01c2c150a40303842842000522031031000060b8060a4000c0d00c0c00c0701c40c0995681080703461a2a564040c0d400200120754100000303000380b1100c144154180c029002003000080d10b09a0701d00d024045040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 415390269 1250 415389019 415389041
    0x7150f06030203100c0504030c03050309030607030c0807120f0f09020a060206060603040609051005010801050a05010e0c070f0c05030105070207030b060607080304021e03010f0c020105100f030308090f1501050301 93
    0x2080800c00d0025071400500d0100401090200180d20702e11010200c1e52401a40c000800c0d500c40110700005214002000e0a1081000c8069070b00945800106178222569100700202060076140020a00ca0080c0c82c502c00030081d1900100e0701c20f03a002c104a01b01e0300710408103400c46a0b40e000040a5003030800400780a802c46000074800303400c0040c0042d01c2408000d000410441d290148141000824441070303001c0300000748148455611845000d01030181141d0f5450500d01d0000001a2445507000aa00071506c800d88170785000d0345525110707040100100151524580c0000001e041d0710244203007441000385601800030320b415031602d58040500079243c24441d14050108601050306501140e4005034100e82521000e1a10020b8040301c0c2841191150316510700f04412034066416000309409405942c020002d56a40c540404003001c914040c2d0b1a210b1200300741400064064100160010300300c104035007150051054951600ca8009004198520303210010491400c0902400b44041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 415391519 1250 415390269 415390271
    0x3060e0c0703050f03040f020604060e1c0206041502010e060403020d020f010c0f1101180c0807050a120209070215091609360206030c03040309060c080304240207150f 73
    0x307034140e20014070340d00403240031000450002002c10208080201e005030401d502403c00c503121a510700024082306015942207004000c4e0804c0d64034040030501044022a078002d00c09400d2505000010800810b20b1200400f9590703601e00322400750000704000c80c4903070b110b03038010001801845d00003828910311005161180c2e060004000c1481e40080b04000e1020305803400f46d10080d1b403091906d024101e400c80010501b11001d00c01c10500110810440c1070381e10300c00072210a99645c8052001544070740c8100c80e02545103207807080052078030b00b01d0590404000d20465001d5403298042e0500c82e002602c00c3d0204d80c2c048492001c41c240c13445640401015000b01c2000501c0e65004880c01d0318038207d020f6800f1180e00c2e020103100c01c464028282c1100d030003a20568603450080f00800382076100740c9040d0701080ba0382100090315441040004040c035805911581036413100d50b11019400b081445004440b01c3c0f080600700540c85510140c40b41c1d40c0101010281240da0180b00710450707000e50b0400044c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 415392769 1250 415391519 415391527
    0x203070902300c091518010e010215010b0919091a0d081207180f1d01180e0c10030506120303010b121005040c0809010f0522020d0b0703060e0c 63
    0x40015480660340c020f0b0204030711940c2c1c090b0000050020b48200c0d0120384101c1002c10000b58000304030041c4108981d0a1700c41c401c4454140b801a030340c4103040d07000c5020642c0c4030001482400e0051001d01150740307018090440c00650143d0304031020946070054442c143da40d05002c0545130300d0f070049405103d015166001550700d19125210280300d02c501ea441003590b850b011611640c4699440c00140d004c140100b0704070358613810410054030851144070882d01080030f05103130340e24184541d64121544520041c11407006800c001c07018080080460245014401400b60b1544441d405421092519940000e042c504181004000030004c014100540c0c02071005209c074a00c0721013101c4107000e030001e01101d00e0341d036820b030020004620341019801a0400e03170086180e680103188103004002c0b0f98000e02c00461104800c10403108100c0d0b24104140840d02c0304045101c05070380c403080040c00544502400902c6c3d448039150034200340d5076900007a980b0101040900d480105203500300380e6055078240f038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 415394019 1250 415392769 415392847
    0x180604031a06040504201f110f01060602071e080a0804080f06010b180f03070806040c080307080913020904050129070804060323040809040606230306010504030203070902 75
    0x2c400072144c4156540e106406c0e9100d10b0350b4800001181000030b500c004414402411401001400d00d0f40040310306101d503002a9500d0001802200161003841d80100700480c50006010b60044080c1c80710f10101380358000c0800d180c074081c000c0012107806840400d40e40e84ca444003182c5000d811400c0b002147c1c01c05001482107a10540c216912900c0c908071310782c024075807880054001003034403000c10341c580308100703000520706400f240403449507026200300c2c41c403140d558840d6900e81c828000001d01c034140c208840300e8285041941804800e40a510050805c0403c1c2e0115040b22021780004410704080d020b072a504500b0003d2007102605000000ca04100c001e584a15850045004100500d601c07100100c01e000b0113121016100c240340c0c03107000c90504050a107502d00341d01c00301109000c0c07400c12001040c500d000d00700522664908440c103846000349851502c2180d08090800340c10000304200020140c1d80070094200507041c003520041e6200700d00081c00200c3d41070072005c0407000d4a04514000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 415395269 1250 415394019 415394033
    0x606221815140a1206050402040e0601030c0302191509080706090308030c0f0f0f0304030f090b030708060f030a03020c040f0501120b0c070606140310021e180604031a06040504 77
    0x860310ba68242802d48614507002603195841070304240d403074416404030348080c043e103500554021802680d0410481e07407941d225070b403242c17001d0101408440400d407007007006040c00e980c400c8050b0050541c110303580c1c0c2c84e0b102980c0c0200c2d500500000140007098140b000310414040540100740d582442211585555a1101079010040c000c40d510100480c04240c6842c04000f290140000250900d5440da07500d51030405030381041d2001d60020301c44010030f070002801001400c2c10f454600748003504569400c00f044035a88401010607400c004e0310241403443d5201003265050840c03090300601090060401072008a50001e549031010301d0030113004016508141001522260300120701c5500e9a503103400d491003500c18442c1c010151450000c0001c0c014030640091420024100c4c16600d461900ca14444281d0103079661070000105a825040c10b8025420014000001d800c2103c40000818400081c1c49402641c8103903140d4031004041d10918548601e89503110504860811860402d911112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 415396519 1250 415395269 415395311
    0x11070806060d061a09010b22050108040f02030a050337090302010807230301050108070315050d0201020c1f2a030e1306030302010f0b0402120402060306062218 70
    0x15000983d1210301a44141061003130f440c0250015010200650b075904001d105940301c1d18082d10100007203900344035025101240341d000c455050b52060030700c1d100c82d15481c10011020004a0b411301c03804c0d181c58009071003403003d8045640380c0690f0400017460b1645040e60605602d200004444c485c00d203000025400c60700c810309403902031a0510340f82e6030f91a02035560b5402c1d421004400702c0030300e031a40400c110301002503041c0c0e182070740c1d2080783d83c5030b25506078281d131409a03244402d00f1f51040c09007d681000e03100d0809070b9005104441c05006248085070054034900301c1800d01d1031341021034002498004074001c0704a81a0480ba134400100384170a60910b01d50f190004007000703201d12041004ad5210392013980801030982d420881030395640781c064020315850600382d00701170810807031405900c0c161003620a0f5065440c5001680e0b501c07a030070084282c4c0002c180c0c43d0300110601c005030452003c0c0050301008074094902020031802c0c41c1400800e04440c0100e108114140030401c1180019440c0c42c1c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 415397769 1250 415396519 415396523
    0x8061b031803070503070c1e03060b04060b0c01021e0309150c040504020c0d0807140904020f1b0a020a0f03051e03041508100905010b1803010f05040311070806060d 72
    0x99200d44070301070425506120200104100c1c070002c80c202040c80310200091540c0b42c820101d24891540e01c80400001c5000c1d05103130070200614078420000303e007258016081154000380b0010b01c80f80c44006140e05038010b8051582280e501103082c58022040c40d00c21086604071344000c40c114901802c0040c1d6580780172821440c410138010219120140c184140c802400c001031083d500d428440000540c2c50a4015250300001d1200c00860710590050026240707410000c072003a407030540d032041448060b510070180400800030400c1610305100301c03080456140030500b400740080700840c0c0104803d005407038000d8104200d400074100000f0f000068407900d40c00038071800301d080700c600d840c00c641035015a40c40001c00b1403040604402d40381d4040c124074030442a090885070140d859091040c1159400d00520000d9181003000101c07120b6131485510300340a0041c004500481400b603440107a40095804038046091450307501825441803100d0304c09481240002c110901e818000207442c43c20003400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 415399019 1250 415397769 415397821
    0x209130309150c0302070609060e0405060a090608060108010f050c07060b0d0206220b040b03041b081204060f021b0f01050c1203190501290d0603110a0806 68
    0xa1000c140c001c8200d48001d041081100042c15040b840142180854100c201c0040c0a09030002c06d005015407110001e9900710341d0341c203600d401c0100600c0010b00010b02501d42c060440d2000042c4501e440c021440a00049400b0f0280340d45008101c07420b49041c1940e6007000c3d4100341c2085009003401d0241e8110341c0d00003070f01090481c0316201282c0012103020010f07411400009100501400d00390802d4a40c0522194071303a0342994902024900f401203006408140340f0400c003083c00f19500040c0e0360142d070880c000344e4030200c0d0743c0e050343e601c0c20000d00c24403460707000c0109080000d150489100e00c080d03803660002e0007520442d4402c1d9030440c20700d0200c0c60301c203018540c0c1c3c03410301d40d10035010740d181c08c0101d10031030740102e00c00c100c400240d82040320b01e2240b4001d90100c0116000c4503015170b40c1246c1c4c40e150660340320104d04030428210811100040100001801507442d03404190041c00011401f46101405e0201c0c10400d21287d031290303401184e4079900c0300051084007030950380301060080701661 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 415400269 1250 415399019 415399051
    0x11010b18070302070f0308100b040302060307050310080706020d03050106081b0a030212340f030f020702090f04030909020c0a0b09010213060215280c030e010f050a0f02070209 77
    0xc082c0d0007030180800150140510000c140c0070150014181c1d402503840740580e00e0340c599030344c1090483c0d04c6071340030003900690b05101107a0040e0007a4007658000301204902801e030740c0c9078160b10b460060b00c1d50105e1b00603880500c0c0c030380901742c0601c603450141400b8680303024245803200d43c2081c5552401c1d41d610f1032030000100c400b446071181d0b06955500300340181070107072810f0021810200003002401c0c1100c90702042c541050341c1b6201c09403501c05c00d8180e2100c03c5003502900c0154001c0801c203444a425640810012006a0710703e52080e10407544c00d0307003c2d03005040c142402040300d04a6080038015900c1004445000003000a00c0030003180e0000d00c014840d62a06c0955029010b18501e501030b0305820030300130031180d40120701541c0c40040c00201c000070307035580319010560616011552090351000c482400c14845183c100442c060000d003004a419014090440e0071542c0201500310030590312000c1c850804041c3c01140e1f104440403070198144512a00000c40d4950094603055070b203941d5407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 415401519 1250 415400269 415400281
    0x90303070f02010909090605010906080607020a2a09200a09180b03070e09010b0a030c0501050c1e0325020f01051b0703060b0906010f0801050607050705090901060611010b18 76
    0x284d20002602261400f40322011552a03d000502028069003203010f042c8030000c07800704400200306200d4642c96008204003403540d22000704140f142c0400c600c4052052407045144040264020024407140400180101c00b01891005045c190410701c03003224410804100295400709591013501c21441c44036102003203208440b0001d05001d1102501b50081d0b03840094481c1020010354450b0700540028032a03003940c0820400441c0d040d000060650348078140074406540304801404045603400d00700c501000428119240a0546209281e642e070300010303c034a4403640315000503172030f001e034909005582102d550005645074084580c9604000c03020a8042a02c40c01031039900d910700b40d000648001c103440f81040000342000481c03e034014200400490950b51080c0d01d000c03074603c425038654031964240420491a60301c290800c0d41c540c480c80b440411140c0d02c0203c41b5004030f1602e0000a43d00340751410140c500480c8400b0081580d1503c1d142c0c1c540f580340c240850100f24258134040b681603840c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 415402769 1250 415401519 415401527
    0x6090106080c0a0c0c060216142b051c200d0c020303040905010b092115060301020702120606030f1c03110c0318030f0c031b1f08040b0c090303070f0201 67
    0x500301816451004400048458000c078072400321200208012141c09d46a600250340d0401c2854000e400006110381d07180307100e52000d510320071500065113007044868a43c9a491030700e402086a4480001c20100c0e40010329006413580c45012420742000e094040d003502000d4883c011007500c0300078000d070824100e08640e002d2003114040c00c52800700300051358550071213040b681c00c180c0e10240107090740001001680340401c1ca0300c03421403e060040c960b069524040318000d0002400301c0d5051341d0280150030060b42c8000721021100d40c680000c1560b85060010180341420b541741c451056003100400f11503c03000e45d046005e50f1812401e02181c8810390004c00880342c814012082e41c00c0c000410303001e80c14021180070880100049045504610740145103544600080108951603417016002c0341c4000036681c2d18400301100105030980007088040610b2010504650071070028842000304020007200d9802c075600400001400c0341000416400720780c0e81d02c65000b0141c9904004d1034a00308580c41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 415404019 1250 415402769 415402787
    0x50a0902010e042a08011511100906020f0f21162f0307030212250507080303040506041505161206080106140102060610210621060506090106080c0a 65
    0x283c0ca101c404c144012500041142ca000c4c0134a032550405607850500052042542e60f2107858100003070b00c0a4228440558010071420100b180c80a80a01040b0b81381e80103800540200c2c00603800042e0703180550318104d41d43d071b4801000005810345000901c01000c046800000c902201414035141d07510300b0181c40351204402d083d13400342210500d151116400b0010003d0582c1c1c038400e800b1901c2e006800c942041c0a40078084106501b0441c20007011190300322505920421409002500c030010340350760601d82151310481c1c09451076400242031204000458024990384862a40d0401c07860510100d030500d07080c56000c0300800c22411214810803221164031400040060380c0081040640d030340f17121240800b040c040c2c0c601500481d400100c880c01d00003d14035640f54a940c0c0c411030325410b100415090015600c01c103603240e551b0403010450201811540c007000000000d11401c006280c82d00380280c1d48014122800341c46e840004004c2e043c6c002c0c81064014010300007881c1c88642c2c2000884210764 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 415405269 1250 415404019 415404071
    0xe030102031518040b150d0818011101090201210b040e0d02101413080708040e100902071104231806060108010b0a0f170910050a0902010e04 62
    0x440001807200002d142010304007800d2007502c01260000100320f007402c1c9100c048402a094024080c00035540040f00c00d0b00440d070010060034841c038204682c80b404032075006400049907011b0595081940d561304800010036030b42d21034009110280c0958002400710075404031000d002c002d100b00000e0b82003601d802440e106200600200804181e03c0601c0c0d035611110302c0c04d400940035101021000a2071030244500b003c02035441d640c0651108070318100d84200c014420b84040070309100100001c2c6a000080c001804418400002420841c5402c0c1c440c0c00704c0d030312001d44a841003105400081550001191041c070854000404941c0d02c5010300c21002c0c170ba07170081805880001049804001000c0d4010f0030740502088600304d998040054079480030a00426200345428090b4040c0361344160115401005079291824402440d110503400309101a0b0780c10038240c20062580144640c2c030300c5a40c0e4824050a014003064216030006000309000c00d0240d40290345400740009800c0540310503440c042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 415406519 1250 415405269 415405271
    0xc070501030f1806050a0b01111c0507050607050a0201060b03040f060902120a08251e1e060902040c0203031003060209030c100f1d011d01021c050403052112070e0301 73
    0x7a04c0c90034030002c01c8211480a44c0c5407078464a0310b41540f084c19074050700a0818028610300d068044040b180034115041201001010000c3d07800050781402a140948020b88403252142c5012801030300307648140c0c000382d03514241841004040b030350301a502601c207074102500045400041c0081140d101180580080c14840d40c0207040c10004200010124804040c0941410070700052002c02c1c1d10114032009012407495184d903034a032070464010510440d110302601c1600e212140986529403040c60b406403119a40c80384600c0650034540140304a46610384090f5280d864011645054540940405400745901042d44405a2020001d0700390b014402051136414400c101001409080900004400502d200e0304000b01c0c5440310a8090100c2d60584414510710785500042c0503844185200504501c0346805960007a400d40303c0d241c54000003503442955550650601074904070407500c81a0b07000c0c10001c2c034585091251000e540940d0481c0205242c56280c0c40340c129021102103074016855 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 415407769 1250 415406519 415406561
    0x1603080f0f1f090e03090906090403080c0a0513060f08070f020303130303140c030115140a081e01032916050a05070813090e03070f021c0602030c0c010e030c070501030f 74
    0xc00c00005c0582032484045928524650b110828003032150350541d00140803519001c040317040006070b02c0142821241a21b0010309040d0858032140f8640b03d10783c003040c0400c546841c007085403544458580e034400021b04025610b01650480255640300003003680c0140c0b9841c0407200708040c403075040b4420441e0b09254042c03041c103203160090344603130080c42400000d9480b11a1115898081c00500c5841c082103141311382024038206064400e16401800307070000e600d01c008140d450300d03261040503010750300400000b0124000f007080041e241c4812440390507a0b4060004004c0003054080c0d881e10b00101528000d0b07161502010291000d009000c0001c12040000c28200840c8084441d0301c1d04072041940306120b0952070481241d100e1042d82c6000e4510350340517440c0d0001d420f01c0341088d4482c10b801c0c65680c3e032012880e00c603041207030400e4a4410141d20002034408524a09000d500060320300389001e5443e04140d0b1034141d0390b800c0944500c50525488881714000991300c1e5000d403440c0c0381401406858 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 415409019 1250 415407769 415407791
    0xc050102040e010609061403240d03021501120c0306020a0e03070801150b030c181c060b03160807030b070e04090807020112112502061603080f0f1f09 66
    0x340c000301340075003070000d94100310000e4100e10901c10f4400718240010300600c2d40e2903100090312034640e035100c4c1c001040c4107031040c54020f486d08410821124000d82c00b0b803c01d142261060036807a00d042c0d00c03540c240e1041c01c0340800404c4174401620f0840381c0c05540103070340d10501350f0151030700003a95003400c0d814002d01d440000c02c49810f4001031800c02618014a207400d450315800a440e00060320051a0481d081c020280e0324074400034060720004004015100000e030301240040300c40a800760482d40c054803010110b0a0341410030080c0d8001405d6031408000500b082c6515a440f0701038070001c1d100e0321114001c80d081d14007643c0c82401c8010090411300184138035040071306081c1d000c00e000b03d0000704041402d400804036131040401210300440f41038900383c0c9010900c20b06289031410814900050303a010801039940e1001403000b00b03014000d0540c0071141d8280a400b8840042508080d003803a4020030001c11030010840f0344c0442665142d0b0001c0f1030100c042c0c4025100742e040100041d2901da45a24 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 415410269 1250 415409019 415409039
    0xb0f06040b09240715020a050702041505040614040b100e0603070e0a03030512090c100e130204090914011506140c070e0a0f090c0306021e0a05030103021203070c05100c05010204 78
    0x4c00540521074081c8524642010300707040381306079800d0600140c818803511005190607080280d52030100215400b03120746400004048800c01c0c1c0c0001c6a400c040380000b8458180360003401428041203610483c8151446005400043c04441c2d0354450240080080d1001e030041c009500300d150080d20300001c450310307490094515071091145c49101800200010010302c00003480d02d88100f0081c00c80030001c100c0303001c15104a904031114a5005403e0b081110080c0042d2020340010030080002054094180c14130404420030103080c48810307410001080700051041c400d03002110194a420440100c00380710340c00c4180903058061580e405026800500344000440329400b40e01003000403c54843e166a00800701c84110b42c00030700c00300e5030717007410004540981e0103010121040d030118000000c00750742062556204d0140400490008030040c015803c3c03800e110058020140000c514108894032190410301051003024032400a18440b0219180b01d00040045140d00800035908d450720740d1030100d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 415411519 1250 415410269 415410277
    0x3070f030605030f0c060f04080102031e071404031b03080a0206090c0307080601091104050d14070f0b0d05090c040204060c15360b041101030b0f06040b0924 69
    0x120020342010004a00ca180110344010300d002c0e0b100061003060b4110050009030781140c1c07006400001c05003c0000c0b0403200303000543c421840040e504a030b80c068920031101141e0003415150410110940013000d43c402d03c0201d805a0b0f07001400240b012034054481c4054140b1030300001c061903408200411215000a0101d000e0034051059a400c0e500e0130040c50b42e516164400c031005540440010444062242e00403141f085c0d0170319203180740940301c40100700e2480103180d049510811000803040f1041c414030812000d000c170620055051441e081340e04032140500d42c2c504507201e6540b0301260000c3c030104081d800201c8080c10940d03c0350380d1250098160523602405441d001c8119090020b010710505c03801705045240c1d0101041a54080300500401c640e403c040001c450b542050b031408101c41c0c0404501c628070030a05a070a40800f5070004040c1c0c0c1185505900820318429595400d60742c0c40241e13010740707a08009180c0c561442d200010303507160180120340031140700c140506d00b146a0b040010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 415412769 1250 415411519 415411547
    0x30902062506050610350403080709050409033608010f0f052710020f0301060f03090201020d0c030c0b0a09120c1707151d0f060103050c060304050a080307 68
    0x10003d507922003051000c641c0940348104002024030401580700c10301404400c1c500881420b46114030031001c0b403d00c2600c034041d00c0030b8020502a008000d041d69004401602400e003ea40521219aa0755801742c030383c40005220380748000b0780359080c510901900700c4d020b844105101210b0311550b510748805000707040820700310014508000200000c14894007800307000d0b80441c124031340c103403501d12065441c04801d02505980b0740510407031044019041d001401d52043d050294036901c0d450020b0182003046c280b03968100781410031411a003d42c0c1c02180c000c81407242424044031941c020300e82100c0e0070420081c01403074407501c00140b00342c5440d640d2081120510640d5140d90750280204250390b10185404000c00c0050342c451606920ba01903409041402d12415000c003081c000e00d14260141c9544800d2148540b2189a95031341c940c3c0100b001c0100c12a01402400e203550554a50703688800c0203000c03044c02a4000404a810001d00b0441030092a400051454890404030801085440c41c5451 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 415414019 1250 415412769 415412771
    0xa020f160503330709090f061502060402010c0323040b070303150819020f0907020a0b011509260d02060109140c0313030e0a0807080d02030415030902062506 69
    0x40b1040002180382c03281d18010803d891043c03020f100706003040c0d5500c00105004100803003100700003260b2000e070058500107140040c000c17a00b0740c02d043d60806001411140001194007510a1102607604503d402c0051505441c2202c1580038199204200b460342400c11035002100082c0001d10041000190003080d129641c10f009040c017541c6900304c404841c2c0158a00c580202c14203103000e426241d20300d240248090081413a03000c0c4000040c4201d40e08032400b40160304108140000c000941e04c8090251113500c0404c09074080c071050091030002c1e0750284440c0341aa43c80745106030100c1601d80313000c003503203402244d45010031400c0c000c4d01c8140a04c900a40d5500f04501c00c00c4003816002814804c441c0040c000f401c641d244580c130040e1074200081603090015841d00003101303440d014000406000101e0041120074582a40d403407070007205202038001c41d0000e22040c0f12805880d80341040480c0c0d540303004030701c1c14840c0c000200c03e84101d4201d100440a40708005c104058040348050082d401010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 415415269 1250 415414019 415414033
    0xe031201150f12020307021915050a0c0f032003040515340908100c120c0816030e01020a030506042409110c0106170f0111040b0a020f160503 62
    0x4000c0d580301545200410104502c02810201c1000603805140d01c001c042c812208c45490140003400c03580c10b401c605982c252200c01005040081c030b8002c003a0803030f45001e030400002044500c001d1251041c40700e0107081507112440c1c0b040d040700c03000d5840c150440c448402c030b6507800e09203805c40da00c101c0c03c00d182c21544c80141c0020800c1011941032045070218900c03000ea0410401102240d0344640d010650506c4849903012481002c1048a1400000c801c1000660a10b0a4034050114102502090309050520300b40310317410359000701c09070f4000300400b0401c0d81c504106902507018100b00410302d21290b1000c203022a2041d89904035502070f881c265010015840031035211a4407004040d48544040450803040085510a5000e0307010141080c0c02c2d41d0a11401402560a5134450380c880c85805000c6850b60448400c248124929190100000c0024144081c8101654043d61190200030600403c01705201170007800080d000d2141c4806841e8040c0c1100720300c2007082e00a02440340a803040c10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 415416519 1250 415415269 415415309
    0x1080c0301080307110d0c03030509010e060918060d1b030c0e0f0c0a030603020a0305030315090f0402040209040923010509070503120a090b0f030a050f07210e031201 73
    0x442241e05850214025629020745038848040c04650002500e8112028480740b401141d035916410024500ca942e034541c0c1c0b00b017550700040049140c0411248605c40030002c1035195907a00400d59114041910300c5174031071761a038000a018040500014088409000b1045000d441044000041d240314042442d070240d2100d00d61444c0800031220f440301c900400022500781009580034140802c2c4c00c1c5804100c441d00c3e60b0214402c010154805c42d0168000701c01d100f03140c0c0c07100304078904400c0c040d0303082d051528000b10303d102d50708005400031303001e07d900027041c0306180c41d0fa8100c5441c9030b4000d00c0702c1c0a44115004040411250180310a0075946802c010412813100840c90108031280203008017203440040061f080140c1c80000c00d20180205041c0000c3e4070004a0098840290203009080c0c8038500180c0410640e60010f02e441c040390104020002490b8002e2010081010304400300741c000b041071038240005004c0058101664032012400000d80c4a0142d600d606130790098509600e005462 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 415417769 1250 415416519 415416541
    0xf03090e07080403112a040605040207050706030f0212010b030411030105070e010509041b111615030209120f0c12010b100507030210181109010b0d0e030d1503020108 73
    0x140c07010030018100d1008600420b1107200c0703642d40c3d10300140030703941030301007841210380381002949180b541810065800b01152600b40b14210081c0320580c0c080d450403034607a40d83c6444141ca405007034241170344c440300c8800403000341e03042e110a408040b039150343c0c5507121079090342107810844007143c070011280d4000c0164241030140030300683c2252560b2030400703008001510340b0b811030b65a203030304669a58400b0748050480c00001b02c0e0410f031911001e10340e0402c0d0801904041c0120300e0681d181802000070803a400b40300c800403c020741c2c1d5207070058990400c1d0000800317440008034404018420741d02d58000c03ca50125968041ca0f5049560001c0c181d1045002030903951885100d1383d014410300300c1000454051002403a000d0310034410baa01c0c00030070301030140c200d40640300c42c644034102c507500c1ca00400c0382042e40c0002052045500311165890704084c49035522900c02e070a0505610344c00105d403400781c20800d40f1400086a01c05000703180c1c005404800a100360300c002e070300085c00c1c1c00125120900b2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 415419019 1250 415417769 415417771
    0xe03010609140615090d0f0b0406090318140103020a030b031b1306051f0c0506040b010f0e10030809190b180a080c0d020a0305032a07081f1103040f03090e 68
    0x40ca04e502410070817040e0801111107002042516111140b01000002485003202d0a03c01ca01c5034200081d441c0742804d00920b0501c2004000112040c145d41c140080b498051403941400c200b480c0c00740e51001d107000120043e150754180d9980511034000c28000b0200f0301841c504025005680c60381a03482000008000d03281f01c1e12031542c02118545600301c03c05500800d218143e81141840d64000e0021ba41d0709141c844125000e80d85200d500c0014001d100000102a0090000300384000036801e0072240d5010000d003610005218002c00a0906156140c28245042d00124a181c0c400c00b50358803807040010754001566000000c8070721001c022140f80201d0721030300355001c800017041c0b103500f000207104440b131080320280d0340301581a800000052041008143e0200700b56660000207181010081505c1c0303000c556940c140d0401e40c001d010805000803200c2e2800f4110086480d1080302a03201c500405410303075001c0d00460000704100031b0050b001d0513403030072910a43c1c030058890b0b522101b00b111900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 415420269 1250 415419019 415419049
    0x3010e250b041a07050f060103151a0d2a0302040b04060b04031b15050a08180309061c060314070b03010f05060a0207080d0e0a15020a080a0e030106091406 68
    0x3005100030300c003920700f41d4045a60460710324401860200709850b418504a141c00d003114003544010014010024842c90754001d000c12808240245500d210300c2001d01d101000175680a41c594941c103609000342501d1300c00c1141c40f050040001c4844400c00c0105400143c002a40114108101020740b4100742c450441243c00b0340b8416401c150450382d41700d8401c1001085101031481c1da89010902107550306201042071003503140c06e552150842c80140000100810461240b090120200407982001c4102d811110048410984e101c0c1e421084c8d00303690102615400c0c0303440c074000c000310401151100703d100c0d2810320b00440d100c40340e0b81c0e00090b981d031109014005258000510822060926a0207000c0c1c182030383c0180c0707006540380c009c070303500d0003c18110000000e1002e000348105810808402000380c040c442c880000c20340079170300c00f0b551000041c0c802484000c002030b01d580d0443c418808a00300000090081c4a0540c0c3c03524a80301415102182c41071202840d000b140140c60181002c0348210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 415421519 1250 415420269 415420289
    0x90c040510050c01050a06091b121107050d0e0114091c05010209090406050a0e010e1b0120060a0b0303091014070204150e0108121608040503010e25 65
    0x20341810140700d201d03035060361500184401400030f142924000c1c010948903241d10107001a00501d0040c0381c0055520b182c51740f0340100011201c07441c00a900112550048010766004a005070802644c024244075808000d017143c0152168200c01d0b90b8856401c0b100c0071002daaa011043c59072408401481c450b00c0ca80a030301510a50031895110782c0c001d00c1c881282d0046000500b809818400f0a8140c0c000f250101e0b0501e603a50100f01c0c54200b14410500b1400da114020406005a01d8070141d035419070303041ca01082c03181c100300d83e60f060b817181d071030034084060950070410008000304442c3e1380c0d00700546000c2c3d411401c10303007081c032181800416990008002400e5803600003c1e4101600c960703040c01c01d0a00c00000400107038001d83c03510300840c01611684000341511600d0021107140800c2c040c4c0010146400030b45010b84c2c81068103064581d030700d80354440c0b0007034070200c1d14082d0030382d00c15907001c15015405c02400c24009580812403d1400e06440c81441360000001948020040107003e942949 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 415422769 1250 415421519 415421527
    0x31611060f060d060e100c030c03020f0306042a080a1a1c080c030f091002060402180a320718061107030203030f1c1e05041110020a030e090c 62
    0x3600e014203030500386502404d4006118000c141001d070a20700140c6c0340c2d18101ea1286691608075605215003105940503182c00c41c00e040e034400704450346d440040c05d198030980d101c0c5807201072462080303031800300d0900c208543c0c400a10b2507540030300461800c540e2203500601d0000b9050b12129050207414002d44c006100211140032280d1030404a0940c0c481900c080c8000e00a40080160820040c10303034040d004240c0740c854441030104050440310709803034011908007c05200c0187c540e103400070b41001c1d0040708007405580300e10035040104405950a43d00e400400310b840004003036130903240a668035400c4e00d24601e40c1d80150660760302402072541c10044544080070170006100b6045004030214007410307039561550300c0e00080d1958128845401d80300400080c2030072484240009044480700c2d070b03507043c04400494400062401103128042c6410f0791150001410041440c030301c0320b81024018683c0060740c2180c10001d54075140c0b080d084020625910901505180c460b4a46100d848511903403454 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 415424019 1250 415422769 415422781
    0x606010c0b04030923090912031315060906030605060109031707051e03030907090c09060f03140f090d140a03110705010204030302010b040b040b03060403180b031611060f 75
    0x81e400400a60402810110101c1c1014901d101602958402c00d5600010040312080000c511070183c00e12040c4d61200706070800090000313060741d0b4410340c00c03240c0d4140444181462001002c3c2c0e40300c0d144140746000000b144066090b40701509407402001d0800840d5521001540d21101d6404090207000125200c200001076100041244d02e1140381071311103041043c51451032102402d407030306125800110802c14182010400b800080801c100107002c0c0b074031003040181c907000c01c90080307000b00061000f0001481e03000b9003041c40b05003042c0c04881500c1c1782809103444081c40641e8451aa40604402018190310401e203514200380c40101c0349280040c00c40d000d40013416007090307210904a0601030080030541c2840074100a50107900080f0b0300340b0b903100801084909000c9194442e500c0d01520350065140000c40681c05581400e00c0c901c038401400c100042014181d10022007040004100030450505040c501480402c1e078540c01e40c8445c1d92070401d5241c240882c0c8a90045142500081c0d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 415425269 1250 415424019 415424033
    0x3090308040b0a0b151b06010b030a0906181a060102010212010e0717040302010902040506010f080403030c0504050310020c0c06040b0a05030c0f0c010b030c01020706020d032703090f080606010c 85
    0x2c0c003c003c581001940080340e4010840544400740c0e2903141d8040454181c900d20390412180f000001c91001500d40d0750f040540e11410f43c00064003510149070364816200c200034541e80012a005074066080c400c2d51810714202d20010035442a50351038a0410380811095401402512508043c89807036002980c01d00c1c51403400c40e10010003075010040302d103911404800d900948907001301d010364004207408035680180701c1600c43c0a040300e410407000ca510b0140c05035121016582055262401041ca00040d100480b81401143c200b1a4103005038113100d10b421a0540c01003282150207400d6900c0d49c0120001c01003540500d200340c10241004005211942d40320b4002140c0c840400c2c0342241c05c1c8100d030424035040e60802d080e03100c0960740d00d5541d00040c3c40c080014001a0710709200416545080c024002c0d00d5607241c45000e014581c803181d1405c80909009120b48a00802c0441c0c0c3c440081c00d420010040c04103885104900315082d903010552950200e42e80d0321855068640c01d190351443c3d5654a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 415426519 1250 415425269 415425271
    0x15010c0507090908030108060c04060e06030a0e070b07060f0b030c190902042312250308190f0e0303032403011431020f03031c02031603090308040b 65
    0x150035000e106800b05100300c5512403219941e001d0f0769a10f40701c0d03043c5503115182603006004c040121200340070402c42e8a0744a80c440d0b01d505401d4a100381c50b5110f502e0010041d1244072114071030790054039008561030010b00f02070200103000b440b041c042d480400b110340c4102c07200715030440c0e015041f510000d906070401009402c40040d1006140520b2540e8412150407a001904000240c00d1400340340c201948050343d881895000403205507461f44a0032280543d45c1000007803403a031072041c440c040c1030411022030b0300500450700704020302d680303580d0155a008094480e04005012652941022884610540d0052008040500154a103480710384000380800000024140100d01511405100ba1401e0090b5071040768540007014603030030301507094a0710708030303040c4600d40b02018501c4007000e070b8208000c0708210a030151085c000c00100d4001190452140e00c00742509903540340e1200380003c1d2154015449041d04102070410950444011010703500f1341000603000601050106020880d1007a0341 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 415427769 1250 415426519 415426523
    0x1e0118111209010f23162007060929180315010e0c090a030b09030f0a0f120c02100f020409060906140a05030604030f021504080706060b0315010c 64
    0x11800c2501422044440c0e110031540460b65035100c101d8902e03580c5280c010b150000d860000d0f0340e00d840c041e02c100d0b4514200c008000141c1302c0d06d140760b02c0c02e41c1402840139080e014858940c4164015000d04503540d20350f2944078003000250105800a894400c03449a42620388005134144100d052408400256800285c48954000c14680609049943c208100d0485c81c1640148484544c03420300c0784800400010594080200f0800c074501241c0d07164800701c0d041e2039001e054a41070f078235038600f450701d58004c1c1c501310009901c0010709060307039a4110355141d02c80d41746a520035010121010000080d0790581c9008005039110300c1c0d020b030414070523400080b015030030b0a0006041550740c008200a0f00c880d54001c490999440c8002d002e9000c040c2080400514181d6044041c80c0c03808021075a40e68004001404015016074040030480c0300703100c3c6501c0101c8521415840b03040504190440d81c0c80a00c00722b69080c40d24400003000a10700c0140ca11807560780e0007045c81e610100d401500d001928a8007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 415429019 1250 415427769 415427801
    0x1507120309021503011e050109050a17011d0f0c030c06030103020d11030303011d0a020a0507170708180108330d050d030b0a0603020c0a03050d0e060702061e0118 71
    0x21003c45034140f03001460003010703840c1d08a807180180078201c03495030305650010760400141400501c820346842d0032242c1150b07107120400114120f2291940d0040440691211204900b0701c0e0401c910100010500c0d151070081d007c0d5542014005d040554944001c0c100b150400c41c18001000076250a40252140a014110f41802c1400040001e030071580240c201a29001d203016850004034549044c150b8024a41d070000c40c50040650006480d03230041110060201c12480780342400c030704c50a8207491900f64400d4480b0744444c01d03040113102e00802005907034002200360002400b001c0210140b401d40090304229801c11740b401110710506034002d61031503900030494081e000001001044031802d060902c5d500080c0f06400e0f070040000f1185180d0203442014014803440c1b2419001050700c24032258103003401079070f031f03c85640c400d8050b00c0e10740406071284c0a200d0410171829004100f82d0b20440d01154251011207a100910380b0420083c080c580070600c110b001c0841880c0387d82c1c040d42d00c4900d803406e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 415430269 1250 415429019 415429039
    0x2010210090309090b0607080304120c0501020a0f080c0702150a03150e0603060117071e030203010c03090c05060a020705062203030c0501050a020f0d0c0315090b150712030902 77
    0x800350007501c122120480015428000c01c101040c1c2034421941c0c0440204c0c4c8151030061191220103687c00050b002420382e001011110300010302501a0940c0c55a1000c001d42d04c41d2441b400c0a0302c080364403031000004c510a6000142c641042e40c04903840c1c079900030000c800011090f40c02846c941c0203c4844000d0607a90380c106020002c010422800520703403619491040d14191082c50b081c0b090680c007040c1380d144800f0030110f8450001c034012040c0c0c1c0c00c0c2510035003000400300494220480303c1e40040d41551030014002c2034594543c2001d0280d50003118500320300b42d90384040c4181403141e502e02900582020364240090314101d00101040c40342c1c6502c016114114000c010a104129401200803486141040c0c04001080c01003036801201400110300b058042c04d404035680c42550012041e8a54840f858440503000358014401132010520700302d8181e8640e00140000c181500d0070074855441c0c84150114052034100700d5034000e6120246e4182d1041da010164060300c140701041340d004503454 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 415431519 1250 415430269 415430293
    0x308041506080609252102100509030105090d05040902180a241b0206030403090306050108010608010e0313050915060d0207020f03070501021c12020a030c0813021507020102 76
    0x2009a01c003914104010380440d0821a44151510003600d803e074131800d803004014002420210305003403c50f122800030b4202040344140b826072222070004025400034814100222042d44200a448000c6058000300055101d03c804541c2c0c86941c40d0408000a1041000f40803861164010b01b80395204201c3d83e10f444c101010005114481c642c0103010f610003102a032035a58002c4a24540300004103080810250203ca45001c52491080c900607004010000214040620900001d4003e43c0c00035010012542c4908465018184900c582401c56003010301a030302c10395012084030b07980c000ea1608229094608821f0004810006150300740c08500d2252818003134841d0350042c400d941e00072000594030700961042010318080e51807690702039401950140140d07600014814110380100c984d111026801c4002203400090109a0030403050020410808140c0c141e04801050109621262040d0340c4038810b103190780d8508400603501c17040d28414942c0440f0f814004140d41070041c41901c410580360 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 415432769 1250 415431519 415431521
    0x1503020310020c0102040513090327060c02010507210f0503010b04060309020a0b03100911030f010324060b09040501290711060a12050903070512090102010608070617010e070c03080415 81
    0x74080c40208a0b27103a1004008150348121400c00d1503850705101c52400821181d6248296014020790080c0800100c3c1c50381507a004200341c40105510001002c11520801500c09101224000f404007142c444680340c00d00c1c40c0510180ca041e6040344c00e010782007515084040300600014442070b6080810010003050702520400190b00c100800d00442c0c4d0064138023507202c030449500c202d4521a410090080c0948910760400c03980c1117940103c00824100c170250000300341c2c030941c84400c2100381d1401c107001982030001c2016001e0740004440c20001caa9071001d01e0035280d028402c1d4100010245140c4001e072403e10b0000d03140d400d0080070300801c540b0640300411a9035004000e031070089010500494214001c038000c40e584188100040c5013408080d50711195240070906201000c40c10201c1c400505034800d51022009040380021261201c0e9a81000303403043c001000004540011540003282d60521710700400e01030b41c0e00c1e940e150040401a101113a00000140040f11130194041201000400b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 415434019 1250 415432769 415432789
    0x40b06182106090d030b030d0e0103020405060a080103020f0619050a0c12020606030f010219120e011d010606080408030a020a114206152503031503020310020c01020405 74
    0x210300028615410812031407803801e042c07113008504150400a041000361004660611504403a003130503d0139111500040e400303405150002034012401046070042268864400350481e4000d54071144030f10042400d000340c5120741035030b82072a0f91101005505091140000344501c005a140452403030b02d41d59940401d155407203940c1d10040c0e102c1400d021440c50240040c44040c0950402140b500752620307140400081d40610b02420300040c1c650a109145807a0440410505084000c010408145030540d1240800d000b641c3e00030b40c40c0c8140407070a81d01070b80707100b801641c0000080c0d06594403001a03030065030200100d241004807407190780115440800c480002c111103110350340140040ba85a60402c0e62410a40300c081129403a0304940c01080b80c20b01c02c1c0c21000980d200714800c00340c040c1845282c4079140d000112503e10342c05198600d0000c9002405d41c92080d5014481e00710090b41028203803005001c040c6d03141d0400c07a00b042030074002d64020455041040009410584d86800041c1c00480c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 415435269 1250 415434019 415434079
    0x702030706090c0e060307061211040503030a080726010306090f060c05030a0e060613090305070c090219031a040c020a0203060a0f1409030702091b13050f040b0618 72
    0x2030703c541c080c4003201ca69001c00354401016401800c0091130711f5001004203541d4851101d8459032045034050049140b400c071006480c02a080302c0d6a014082002000e0a104651540005400541e480c2c80290100600e0401c1c82d0030f80c202c84020390858485000905d030040048840620f031124400005003903005500002e0a1030300c6090316864000d034a003040d60880044c290b0250850340c100495640c40d400340720703562008908001825080b8ac138081d20b161266000260550090f41c40c00103001241e03400420603400c2d07528105100d0515a5000d40a46039902040040c02402d60316400050505d07038009a1800c43c10300c11500c8502e8180c000c82d050210949000d1401c6482c0c4251018000441c042e1442e051810381345030587d4a0641080354030790080c214004e2041407050080343c0c0d2402e1661a80910940d40c1003002d640e4441c808580b0640b04040c441c1d107014034030420492100c0d1910340304090740310b01d01405951515a1024001c800040c510b4162544003810205600c6001510540c83e01490 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 415436519 1250 415435269 415435283
    0x30b040c0e011b0320070b03090106030312020c031b01110a120516020307120e09070309060507080c09150f1605010b0306060d1b2403050c0708030f070203070609 71
    0x25007000d0005107540451164403201c0603100902c900065400007061688000442d11820b841404800a41c201056a48000c420800200511904410645c0814100c030f00c40c0c0c45d4038128090f100d1042003030340190348412010750414022207003296040911141c040c51a0000001c0d410100368440c601c58200c8902180000c0900d149041031003228801c0e10340141043c00c0b00c0d2124901140025900c0c80f6104004040383c04850020301d40302e000d00706054059200509101507807800000043c000d0140c400240c89030350819001c1521103005140c03450089c090801200d2810900100b40701c00c000148100c8100f40d90200030b0342d150920240c02520304c42240ca100c1340001c00d55400e006080d100303007601080c801d401807800e0112071b80d1240c2e803420314154402200394510040241c6498030003221b03808003020300c440c501c019001a0300c0014905012005071030400c4551070b0700400c011365009580c03008000440410105419004800d20103034040c9151040b00c2c81d041c460340d10001a614804802c0787c0762 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 415437769 1250 415436519 415436537
    0x12110a0b0a081005060703050a05070506040f150c0e10050c03120115050306030a0b27030d110906072d0602070b0106030902010905041d010e0c040605060f0406050a030b040c 76
    0x41c6038003420480d0002c0100c440446110f00384400141d0324410b8200040500000151241900e070244060b1006c0c160003406942ea03900d45030800802c02075545004032003600107001842281030482c4518105082165148100e5145c40c405018240c101c40700b4920074000c0c1405070140d01001000141464041904207500e15450b044185039a00d0a09803c6400e000c0309008001040d20009403054415420031030074405521201c0000a043ca0b80359121707541c4c29583c114048111100200600292050b14020801c001c0007021002041c0504031316641c0c0002d081100d10045001d40020714070400011030500c0e00c11071010341c103a2a1818520040b24200d80120b903250511101c10101030050605040074403043c01c0ba03600090400b0100d014140c0f00d55070b54190000000d0b47c0640f108624035059000700041401050301da41d039452402e00da1031040341009004500c030306020040e10303a88540c8604107810b00c1d0400b1310913185504822903440406070340b0088204650303900e0242c0110581192070714220 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 415439019 1250 415437769 415437787
    0xc030d0905010b09151e040f0c021c0c0609031806030615090e0f04060b03030d0213120b040b060102031e030a0b0603011206021b07031212050103030912110a0b 70
    0x3902e403c0801c161090102408220b8025801102ca10303455804460480c00c81030200c62140794180c142002d140c2103861320408151105035607020105401c0b0340c0d000c0310030820000440a040303140f94010440040e19181300400094666085403902a20078140000309800c0c04c03200140f19601176012900003078688004200d4003500580c1c0070003401e003500c1c140c1215418506000040707400602840074903c0703010001428003409920035101400000c0030b480e51426007055000c041d401000040500e814294000507180000d20610b009951b40001c1e40c2d105641d460b103d4a0740050001c1200d81980407c010700301c0d0341e0240401101002d082102c0081d1a13041c185d09e01c00881c1c41c400780c160b000b2002040144040251724200403c1290702c140c0150743c504280b0141d03907110000e43c200e40300d1445240e401200b00f0243c5407c04034090a00c2e500c0d192158103c45000741a20f0007844040c002c0303182c004041c0988002c544105034454080c41500c0c0111081d0008580c1100141d4010002c000d400b0810540d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 415440269 1250 415439019 415439021
    0x140f04031e0314040b09010c0f0602041e050301050708060618030a080301170606150a020a14030c0f06040b0f040206070b04110f010c0c061b06020412060b0108090d050f0c030d090501 80
    0x10340b82d54035180f40c10300c0d0038840d01040522031500103c0c141305031008240c080054501c82201d940340d0044040d03450711f0f030718440b001041081c1101c03820080000d01c40441c440c2414851b091141d00140c1e1080040d80b9502c083c402644e01032000d000041800c0f1482c0301e56138401b000031508151080d0007e0f566036241580c400d0f555007005d00030014940000c407c0c4445941c0740c5c020140b94100340d1070300c5076403031004410907490b050314050000c015001c01c4903502584c04021000d0645030f0403000640301b02014500c1510344030601182c00818030b80840c404904c0f14074056009a9210384041c200b81d20301032a54130342c1e1640340e90403602100c64100d03c1d0304c51805c0f420010201d00c150a002c0c2050046c001182d41c1c0d0b44007a00d040c2c06581c1c10806035030840702025a0440000d143d15070440b00455403961140f0006c40b0401503800c040e5110350802100c81625403244e400c0601c99422100540120008071400311640d52008160424102301030000d120120020300007030160304d0130316070b0010701c0c8100e500d031440c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 415441519 1250 415440269 415440287
    0x6270103051302090105130b1203041410050403060216060207140715080c0d090c0f030203061e06040f0209030f0105061311040605070c0b070b0612010606140f04031e03 74
    0x8002d01c0300e0140540c00680307031100904d041d25001c640011080155280d03503001084440c0e0700c43e07030114024284442c60350f4080001c00666030b01c003860030307a04100034050000207042d003602c000010700700304010000308105901502d125000402c1c54444003e1640301c080980c0c105000a5035001845008100c000b0000c00070400200220803113040403c280e010050402c03500103102c0c1e8105a00018109259000341d40641c444560100c89044515203604210010f2455800100c1c024840c603070205410040c0e04c850b0403011544000204803c0d641d0301c046c4030241c00d503d03010251054090100740482c0d80d0600c480e505113950b000c00000c05190480c00c008400a688481944c820300d40305c0c0646030035403c0380845042c5c804d24100541c1c1e84010f4a0001c03070b0b400341c03540106120f180108658003084540d00615000c2c1504036103480828281e80c11407400c0780c0207032080401013544050140113148410010b0800d5000750444030742070a90b20f4541103110403400c82e1400300d40c1c041d21402c400300741d00403c040f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 415442769 1250 415441519 415441531
    0x50f04090e1c0f05070c03050303103312110f09010e04110712050c0703150b1008061c060c0225031703090a0501141801090c140627010305 61
    0x248200d02c0300030302c080c00ca03010345048941004000101e10040c4640c14003000019944942180c1c1d80b4a0540b04c3c00c07407420918010480e117680b90303030000d0310300b50301000951480e515260a00c00b0200b401c400152500c0c0c8491040031200c0741c481c0c0c43d040c03600d0301301406080e1306124030b00e08035911a00c0c2c0000528101c10780000303d101e2498141d09480204039001038034032890b80a401c030440800c505e44250350740c0c05842141649445113200c0441000b003404ca00400c02d00080800b80b142070591001c00c0f403505e204240000c005032000700010414a85260345008400403012805151022501e4842c01e0b500880482e002603440790100d602c42010000b001100e072144440c1380c419540c21aa10541048600316007210071003800f1000c10380251051001c410500d42c40402000715041c0c0c401313040d14400040713079040c0d61141404000c0c03540d400d041c0242204682e01c0701d40710342084d09180005c03000b40600500c540d04680180100c990078280159255801039880f00321451079001000010140d1310010030f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 415444019 1250 415442769 415442803
    0x606031103060d170f09150c060720031605060f0f060103091514010e010501050406091203211401090605030c12010b0418021e1c03050f04090e 63
    0xc03095010240c5050300d4010b04100c0b0030b030040d0070f6076080080c030041d00071220803920f002c00100d864036034100a0050203071070b105a40c003680845076085903020310301600181d807035a60041000541d00c1403003401e5103001d1255071b00040212014080c55945150021801c141c4002c405030021000e0201c20004160302c445a5100d242e0ba91410620b08096090040c1401d0305040e2078062045c100135441741e40d11121801c0c04401c200301c1303400500340c40a140d001c1c031a0758050302c3d5403400414654481c408540907070f10140c0301c107800d5a141940e51200c0c01c3c0710403403e40c200220300325400b007140072804012410000d1203031702041e10050000d0501c501c04040c5d016903003040c5803820030401c0d41c4000c150100b0015044881a00e4440081c06182c058850074007055801482d202003c07514038035265900c21000d000340e03045140b16000d2451459813044800156510040400c10500b0351041204400360141c482d203440f50a010307040d10101c103250001e4000c0030020340c480b0615071445008102e80c180b44034150354 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 415445269 1250 415444019 415444031
    0x3140a090e011a040e13020405040f02130e0c09060a0e01030b071407320105091e0706091701111308190c090e030912011514030303070804060b100302090103060603 72
    0x10fa02030b079032056104d980c800c020003000040800014410410704e044d00540309000c24945032410f09094440d04004a1081c800001400180040e40c4124040c0e1056003008018007403400c0c0400260070340c000d0015074401003041002c80e40d6403820715007030f0085100b03081401190502010192421a44140703980e00440c091010f4004200e0200c40000c0f44d1130394611000c00300074103d84546e0345459184400e41290308080500c46056000510103c888081001e200d0954654100880d1260840d00c41d0800041242a0030702c4000c900b0a00200140403c4000240c41520f80000c410141c00001c504061402c984030b080060a800384802c1c0145017400c0f04200d680100c0c0d03520201c80600c0c0380a014140382e80e4802d1441c88240c108112410418020302c50540303500b1208003180a040320301648045621032000000d50409101801908100d0003405117046541d10030080f00c101c00010700c06c3d0344803616072a0300c17441919615884000001141e80242e55114050009000d03150507502000400d03180c15 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 415446519 1250 415445269 415445309
    0x2101060f080c0301090216050f10060f15080603150f060108160207140102010908040b0d06081b060f092206060e0109121106030c0d05011406090d03140a090e01 70
    0x5403c69042d0740100e807005031034410030240022544010300e4014090f20415071600c50415001607070025008003814148030303031611090b8240540c1781c14822101d042a40d40d100c45106401038403c13a60019010301110b0541c00705505650408005079070245522071560203114171035a11031425640070110b140b00411036a0000700095071411140709005400301c0300c1e003c8000e070742c1c401c2d0480d58480e60407540658a03aa1240c8011300540e02080c00400820700e00200000c00d00c80101703600812581e0302c5034400e6041c21050a00801d5880a003006a06502c2017104158558403900b4000fa42504500740010500c0c04981203802c9a0311f0386c100c98144021080da0b0b885076030740000400700355070440d010496040464a005441c585c0000c50143c1c1c0414040108030441020001400c05440201c1040c0f11a990b40c00b29504844864004590804420000c2c90130034142400c02d1a00c00f8428600031f10307102c0d1a0002480141c101004000c0011242582000301502503c001130140100131150030300c24482c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 415447769 1250 415446519 415446541
    0x614030a0320010c02030c010e010603170d0603080403030f020d050c070515040819150501050f0613030605012c0c03060d1407090207030206090a110d082101060f08 72
    0x303040041c10009020341c10120310003072541501d000c0c2c109034000e005051038035001a469410001568613990302e015104000c8030014080e103021030750481009094407600050601140c1c0c070a003005112140c6942002001a44400c0240001c500999494110340c0340e80788001d080600300c00d21041040f034140a9524034090219031081168001c0b6903c5840b603031408452441409150f202010034050012440c0a04d420010b5401c1036030310413010062945141d4016000300c030001c0c0207541e0000621940e4a903a0304140c2e004100301403460074039070b41c0c80741e983d92804213480d000d070000d640c8886205c1c0d16008030410031440c01422100342c16282507914101c41c2035503640c04000c206510402c040307052402800311515400b4401d95584003914030b8103480e03c01d00b4001e5030004904400602c030340e9001406a2102082a0408a03803109114540800f0748042015101d14054161040d28041001c4031399854540314407103152428070103c02896141201c05040001d5658125040c016241c0802c007848200c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 415449019 1250 415447769 415447783
    0xb240d093c02100e130e010c080108120a0c140105072303040b060405060a120f1403090a0302010e06040b0301030c05100215070f1b0f0b07030b061b03130311010201061403 75
    0x100e00e06071348a070480c0070014000c500310110030304c410751070514400a0322106400040d03500c80d803511081910790341ca40d00d00b0340e01e801094503c00c00540c10311044a80c148034905640f403040c0500030b0025030b621044121421164261021305c0412524260341411150101203805402610142281145410784580d0019040184068400c558490001d070303655440300b1292002c2d0400300e0070b511900e03080c0c3c6403480421451010981c0e564890320a0302c1c54a0070000b0031519110070141c4003c603114690741c015035465081040d207a502040a01c40458100c0d0f110000e94001c502400b0440082407400341071040e101002407124003190010700100d00031141441282c0d400c4019803401904141091408640c80b0801c3c3c2d00c0e44544044000d010014041c40060b54101a030090b104521161140c1c141a400c4442265106401040600200c48640c141c44010f00414442074266860418010300784201c10045400454140000390b0f5014025607092141c200a00b8080c5800b142c19100c810002e03541e405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 415450269 1250 415449019 415449049
    0x271906140f09210a03090602010506270405010f290102030309070e131a040c0509191e05100311061303020d02040f050a090302010b240d093c02 63
    0x8400e0080c010540c3c0211480703086401a10598002c55001d2030010a4407005126038001582000c0124109281111000d4181c940382e040c0281e40045441400c1401c9000038000ea1743c41d503a54242c400c10a0240c01503200e40348038004031101c42c1c2d07600c3c0c80400000050320039550443d40180308000001304c000501d8015291903181d07000043c1e5807c2c0010117041a0050000c20860ba800342c00d445944c001c80e441409184940c0780402e10a440340188410032800b10b6888009450318000d0085041050b40411040c1641c040301c007025110703400301801580c4042c2c81c10359040844030420014010420005007039550200c941c07614003002016406c83d03109441c0406403040d00026205d008554860b4400d403107103400b42500713201710b2810302001401005080801d07070155080514040051030000e2a480584104d001003044428007011122802e03006a1110010159210810008680482842c003002200a09002000c2c84550b0906210042100103054145030000e24036006a030380344422111a5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 415451519 1250 415450269 415450279
    0xe010303050901140910210507020304050f0f1e03060a050910020d0f0501061d0a0e0a240308070309050d03120b01030207060204090204061112271906140f09 69
    0x1d8921241d00c00309201e170304a82607201240e980800083e0f40c1007204007102c0900440100410040c8240f15003c4d02e400700d55880040c0c004000c00c2c4a9450f1000c550560400040c0c04d06181e4450a004184540403a0400845501c2013590301c4034145000c211840d80131a120344180820704260407960341c0d842032000d001901d00e402080312185225140e0200c40f4510207004284450350b903030710340546014510309225800843c0d03001210007a0500c514400301325814000031070155a54540150010546103807560742c4e20300c3c0e1130808000201e070030707807840060750203a8001c6507541010300e0060311451075a80054010b5244000304804203400444a0110044009003c80e58020b1000101d0091081a40003050103201060106190310707940c0c041c005603107881c3c81c0ca04581c101d6a2040e0382c0c1d0040d4040030a980300c0c0810070340d4008003e490703a1942d155180ca0380c03101c49815000001c1c01260080c1c0702e090003090798103403c0142c282d004a8201c02c00d00d10070700035490030900741422092446640c0690b40a2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 415452769 1250 415451519 415451537
    0x4030c1401050c0d03050402191a16020a030b0f18031608041a090306070801030803130503070209070c0605070509060717040f0b03040b01061d090402030109020a1e0e010303050901 79
    0x90790280c030484014540e000183d80d01c2d4000010084c0040c83c00741c409070b014007000781c00202080300300c0c1d45803c11341d580d0003103801c0f02220024156229900c0959982c0801340d00c0e881c40001603d4911654002e988034007030310f140c6481d00750895018803100800f01010113003040c03000049031201000304e0711910b01a100269900c3d5144c14408aa8071a035071200b9403607201c0340c406451041c0c0b000c002e040310080841c1900c0c1c1c1d944488100304c1c0c122900780400b80400b40104046500c1070064121410700d14402c905682c10210a500080e0308128100d580e81c000c00d80c46804181000031602c0b6440e03220006080040c00c00352140b005c50399500613614001c10390005141003100051500d4162030091044255201e01646c8a49030705000384c2090750100c07001094140046025801000a04000190744035082010f0021f9020086801806030043e038041d5a40c0310801c0241e01d40f07040d850040c0103006000f940c580700d084240e070400f01c070643c000e014124119005000195018040314404142440c2c20020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 415454019 1250 415452769 415452809
    0x6050603192a06020f01050c18190504020307050d1d0d030207051204150908010203010612020f130306050717130204090c0807030b0a06060e0d0209070e060c03070b070504030c 77
    0x1501007811640c180300d001d001000a09941d0000d580b0f0b100c41e01c0c1e03c0c0244080d23199103000c0700d40ca01420000901c03110f0640c160712814100460034800030882d4500c1d98641507621004036080b0b0340f00703803151000074400140203241103499014458250b04070500701d0112800202a540d10380480b40404020182c0005412040c42010000081c50303101c65058950b0f103960b22800f245c10090b421180502290326881c000902d00018400d590407284e00303031506101d42040112110080d07000d104d02c010300c8007044c040c883d0a8032201242002030b62041c0d80008180c10040000352100003003203e12003015000204100c200c0c6501203510ba250ba6041c0d4010a01001c2450000340c2403810741c000044610545500200744000e030014a40250f0f00000100700c015120102200d9000c00000c2841d003245002c50319500504003820b4540d40100245010782c0054007010000380340d58442203100c04c1d6580041814801c2c4003480c00c00d51342088860410703514161031aa1140c600041030702c00d00001c51a010310703c0302 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 415455269 1250 415454019 415454063
    0x60c09040e01060b090307050d050d050f04090507030b03060a02070c030b0a140c031614070b07120c02100f0203061026091605010f0518031504050601030605060319 72
    0x30508010028083e041c0c41c0d4191544035000612550b202e80f00d441d000113404d040c000300c10b00c4404e8200c400350030b0614401700c05581d41d0b80005140d09120701c04010001c2c1c050701d24400e0900402d003554000c06c60098400c10507140000107061325280a05c1085020300003681c00c1c0444040700d80c40386000500e0b0390360340c459000a05c80c161844ca245100031042210982c68540214402c000e21400c850f403c400c8400210780d0400442000f01040d40100018070200f501007485940c004458903003620100c842a01c2281910011100c810240e888110900c28042c080d002d91510741c003c40700110308502e080400981000b50540421003071000a489101000c6500d80c03220f43c0d800c0b1a55610400e40c208010041d50321030000324152101c4280d9800400c007580328803a80c080540b800d40e2040c1c20011151003083d44c814034a8410350785445150710400b82d598111500911a50046002d0142585541085c4c0140c840c0104642e00c6070308081080c6070f800c4000c110f20762070b29030807070100a00b456250310041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 415456519 1250 415455269 415455281
    0x1302120103080301030b010f0501080403050711060d020a0e040506010e12010b1801030303051602060610050415050301080d02010204230627040f060312050a0507080c010c20060c0904 80
    0x408000055002005110900b00114102d81c03141d800b81080340c3e65184c40010903560f03400b884d800103015a02140100c1c1c89040a0900700d409000c0c211000402e10000800c594082003074041d4107a00030035150039054100304044510720342560207028900e4080c000070b0503040030301903071071145141442d2503140d402c1c2540109120140a01380725000d004082c48803031000803d200031030000b402c0c100007400384051100c00152040307a64004102e01e4860f407080001303e0541c003001d941000018840000d110240c2d182c0e107c1c00080a031241d03a41e0354180f081702c5007800290b154000075a801044100a012401800d84184c4668501e00a0b07850302c24600103081441402c0301c501d0100040134509040f0041c1000c0c4a52403001120304020000c1070790500c3d402d80e602407101a15084440880a003024000c80c01009031071102c1c076105281c212140d03649031068000c0846881d250795039102c5c00322000d4004101c1b018000546c0d00c5124144000f0705020380e20100240345800200c404128945180c459030025 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 415457769 1250 415456519 415456537
    0xf1507051308070b04090b0d150209030a05010212100506070312150504090b0118090f0206030601050909070c1502030919020307050307030b2d0c13050a0b0309100204060504051302 79
    0x9114481d40c0d8071800041a00a07000d180342c5617103001c01d8420113140031849080000c2e4801030040c4906002789001d00203401045006400d406290350f503100184007031005041c0500a1140c1c0c04444c280309484040c1c240080d00801c0c020602007010801103500400c0f00700249240b40c0010510811584110380c46c01e13a6030380015006420040e400f001c20030060303038082c10394a90011442d020808454988107981c902d0304041c00c41c040212900001d818020001e40d4459810704005291080700f03800705960f0b010840d408070018100380008800c00c005460300449a9182000c03d6085050820610362108248518080158060100304003103403800d0010000400d0010162079515680b414548a91030040382c102d520034003004440000000c1c146425004031124100886c560358403a650902d165100310010440041802000503c9660b0803008401170509150a29203900b40240d16500e8410041c4410740c0e2240180310078000f00303603c0ba00b40c908458089858a01c410030306115040284203016207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 415459019 1250 415457769 415457773
    0x60f0833090f16050f0402030618010815010e040b010608041a010b0406090b0c070e040c03063204030e130f05010e060109080c060405060c2a030f1507051308 69
    0x1c0015540001c104054201d4011040e556050701005540c1c2402d51030340207003603000c070000492258504280c0d0240d40d100d600035007411b1492400030040086101e00f40c0c044602c0e540444040203100456114043c0101103014981c0050b06040e695040c42a01c14000c40d4204605040000e09020400254116040b000b20030b04041d541c684203c0340e81d95005004003004205020b030005a494040011103002e520300070094868203041201c14441c103100944280d0b04820f18141c0800414258821480600905032810107804100f01c403402000a4144500c0c428801000c2000003194001541070304003001100c110480c10080c1c14084010007006501b411003920b000004201034410340040c501982d403d072948151140d442d01c40a940e03600c2c500c80ca5030808130500c400c00c5181040405171210354001c0e4103803400009011561440038440c5ca60040c641c031003c1d59101c44904051040040f06124130340034200c69040000e0041c200300c3c000d8040c104020380080c51040c000003ca032100080c2000000b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 415460269 1250 415459019 415459021
    0x3010b19050a05090412231611011107150513090903020f1209090406020910090e012c0903091905090f0f1b0f070305030a060f0833 58
    0x4401048080c59004190148140c6007012545107012078942d0f21039a07101d8030650440300790744c500301d82058805d54900c0045d541741411054201002010384922a4100d134842c0c2c60340c0290400d00c00c20a58010001e06000f40300c0000c418071007000c1066400d454140441c04179040742301c14116402d210b02107000141c441072000c04681d078240340e0000401c1500075800c41d42503c00031404507440e082101c800680883c410490080c2d1414080c15003640301c0c1c0030b0040141092110300c0466041c0c0030300040240004d108644c1849022800181c05014215110fa501c2142c0b864452801c240c2c40e482c440072407401c03920300010b03603240c40030411511841d1000d80b04c40300011030380754a40b0401d00c0f24029a8030802060300000d02280d510743c01030b4411f0f2517000030004a601c1c0c1c001c04507a4011030b0060f0701d041c80c500b04444050405000c004000f85882030b03441c10b580c2c2c03900e0b545803070456860b604808140e4014500400c400800083c007907414005007664207110b0406040c070802030b0026511001d00c8645501c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 415461519 1250 415460269 415460299
    0x110d0e1908041d071b0507180f0f0b060403020d0c05030d020601210c060806030a0803190b030c0a0b030901020909130302010b10140a02030f0c0c10020102070308041103010b 76
    0x200500100c405a4541e05a24100c030180c0f06103001d0100c0740940060024543c100402d241c0c00328401e50305000e50140c0e5280d503210500440440a07010880c0841c50311802d0030700481c0028802c0e03032040e1490580820414502e080003a10610030b0388400b034032807000703010408144503c0c41035038801000010115403210009850180d2142c0c0240305e071141c028070000b061109252050051100940d014040880850074880c0c01c0c5c0d200c4402816640d007500c289041e60340012031080003180115502146030400348514040241030740e079096030039802904000a8011140c0741c0420303070415520414405901c90303407a030704601c0c02070080d2204c03e03a106860900340002c20303907640c0000760858040c0e4000e01503a40005c06101c0c0d0940fa060f01c82000541809040320030851120246c101c1010f280b0640c0c2c5000700d402c000a22a030041c0c0483c042c2a0410000c00d0a10710701000d003000c08000e1400258140f80d10350700d002d48038200062010b003050940d1b050b4800139035000c0d40600f810901c000c11004e5480e084d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 415462769 1250 415461519 415461533
    0x140a0b0d050412090b03010302040e011e05150a0b0d0c021009060212010b0c06040809040f060b1909080712020111010f0b030f011808070201090302030607110709110d0e19 75
    0x9403000e5401021840020007940e11801360501039486a114052860b4a580c1c04e0100510003c20303010f1455603a828181c5090f87c0719502e001c81034100c031401243c07030300b450a00c5400008403d0703145481841c8a100820441000b003082d42c00029480d00300198560424000f80e00749120000e6444016203041e030305004114144d03000d400f501e1810210348480703a88480d0500a64070942c0200034450f4480e40018000405900040502136000780c00444c0790144049801c09848c1650070084050754003003280c0040c45642309940c040c140d494a0300c03007401450f1011040d00c500d039034040c0c4440d00a00f90018000d69000e009012420f055860003040100c0b445090440280310080e400303407182c05001e01c851058007050150704982142e28a0301324100d8842d0380c030101142d001e441c08906120030240c0c0040541e82c14070185105151a8481200304810903040c542050300a400c0303114080c2c42e08410b00b260030b003040c051703403140404140c000625068000c1802c1c41c1c541c004d400d01d0420311000c82d26400700541 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 415464019 1250 415462769 415462771
    0x911090906100909110d030e062808010f140312030705030a06060e030d030e010f1d10050f06010507030306050301020a0207090b06070f2d060c0f02060709140a0b0d05 73
    0xc0d0710b9041038001c3c1c840801c0c00c142c600001c0050030f44c00b00c10000700300d10b02d00000c074415802c1c0f013410703c1610310041c5004500c0d25041801e49444400304110f01602604d40000200d404072002c1c90851459810720170000d0140c07c9601a100140044c4101040c070f5440c200003c120040810078566100e107040d0074000c0043d4000c5443c0341d481d5007010341c00100c160007480004500f090040180441c81c5803002e0031002001c03001103044030383d92510714502649a05105401000b018250140074090704003100030b2910042070414140e1515050801030240d08908000d0381124003441c2080c0d4920245c1000c4003e00100e030003069140d44000307241401c8a4000904004a40c1102c5080c01120181c500300403031170040031409010310500c90100000111452811810b00c9009007640511551300c464880c3c802001d001c00b218015980c603c4420600e400c554140321a010074401030400380f8200c0f00060034a40140302d0203801814213180600113603507009400d800f85c6064940d1540314070303400e40c1001c09404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 415465269 1250 415464019 415464031
    0x2107121101091217090606040c030b04090807140316020114130f050120030405041d060a050414191e0203060903031611030406050d020d0f0c020601060e01020703060911090906 77
    0x40c198440f0794404e110b059401e204000c0800986204c0e62920140030142c03941c4031101040541e140308070200d540d40d40c0709885003540500b22043c0c0301c058600d0003030100101203518000030740c810b01c09840b280a060550305d6100c0e60a01c1c02101445140030200b00034041c22142c00e015184002c8041203009444250204850003662400e01d0710032100420040500b802805103000d0304100400c0c4081c0c10300f600034030110301508411040d01c03001480380d9420420f042d500c1c001342070344a006100070700c0b102c4a00c0700c01401d604400b03004110b03000c10300a100d01171013410081880142d0310b0b142c3c42d4015003621529034683c0240070b41d115031a020305815140da0041b11420301080078552500c90b4030b0f1252098400c0803100d100214582030070b19209590980205420104e0381d50200000c4a0549403801880e50b0418466008120109550006400c110058101804000fa480a1000540e900044550499402c90000aa04007041c20502d51055181d110581c101c00040f061004c0b012001682c144104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 415466519 1250 415465269 415465277
    0x7020402070f150507021018110a1701020a030f060506030601031d030a0203121605040e0c04091a10051c090503070506100906080307020a060503072f21071211010912 73
    0x112024805811a4041e5202e14074980b0008c83c3c590020310214114090b0490051524030fa0a982d952111744818000a89040701c0c3d40208050303460540601801411030300c0c614003030001e10b041c0000f2400e5400000c01443c10944ca503504031b030540ca00c508696240c6420b200c152552a550414043e6495204041403c044c02010000070f5201500d1a40710011504903034409203440e10b080444600000090100d881c00c0904200000f0203158520400c040b40180c202ca1210003c0380100b0024860395079441c1c501440b07010002c0926030b003801c400d48040a0012000014041c60398249585940a4031030300034281d114507418008002c041401503402c984c11001d090000e240c5a2007050788a004031180290000751403441488454025806181d1002c00c9241c000c03007000c09101c0c40303204204c3d1802c120003031203d40304021556440500000a103003070280c4509652000e0344c070b414000d0340320b02d2402500b64403100b5000e606180c4101c983c8805c1811120080c41040c66038180311283c10500780c469008a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 415467625 1106 415466519 415466533
    0x30a0e07060905120c0108160203040e100509010603060602031206010320030114030a0515061302071101081f03020f010e040905010f0b060f07020402070f15050702 72
    0x1c00c0c1a564245005160005000b0040303004010241d13182c101d42c01924041e604400201c4c2c100c2d010f186a103482c000d0740c81040382140516080105240010002d100d00801c40c00c1c7c401081c0c800444e8500c8040c1da940d90b0a4048500324414080507801c140004c509010044c4c480c550300240605021071440c0c2c0e800601c0f10881c0c0c0201040000000c00b2005100080a038200b01c00b006509500a02041c0c2403500e400360344110003000d0315210300340c1038001010782c0c0302c04011b145480c042420640d200d001500e0701860f10700345d0b8503005001405a400140d001200c120015041640700000c400440c1d0542d024040f0990304494250f040c041c80d0907060002ea1218031500c469603005900014014070765451075420341d4401a2034622030001401003110800900045400e0b03554100c07801a5550b8051801c4580000f0b503030030140c40315442da008401c183c1c10b03d400c0f0701c1c03040456601b0b07a500 = true := by decide +kernel

theorem cover : BRFrame.Cov 415287769 415467625 := by
  have h0 := BRFrame.cov_init 415287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 415287769 ≤ n) (h2 : n < 415467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
