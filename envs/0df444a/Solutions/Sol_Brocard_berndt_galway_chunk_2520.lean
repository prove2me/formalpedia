-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2520
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:31.221599+00:00
-- url     : https://prove2.me/submissions/51108144-419c-4ff6-b5b9-1d4e4853f397

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 453057553 ≤ n < 453237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 453058803 1250 453057553 453057559
    0xc02010b01030f0e030d11070606120327050105090a031403180d0b010e0c040e0103030806010807021216060e070801020c12030105010819021b0709060e040c0b13080d051206 76
    0x8030300c111002d996120b201e01a001b80903203840c2e4500d4000300c40703842e00321003429a0110042101c56503c2c075081d4080220303c0f80440c0000c00400c0b0910000c80300bda522801e1114410b0703080641d6140030019141d5501851000d034206000101c000003045991a0003101000c100000d16640c000a85114113223100310034071070f0b104608660b0780c140850714094045d0305540c0e44681014507511450341e04803040c040e550006044100d0680003004041c1d10610f298003448080e00c81100300e4840d0305007661034041020660b008104280006050b48144c4c00e40c609102c0c1c012400006c4d031040c600407442c2044000d800c60032030b6071b400150440180c0010001e5040c8909081061815541018002029a8409400100750301004811141080c00c10360440da50314401d070040c0e00c001d001400364680c942c803617440748100d800e2034201c0c001082d00c0707042070310b0b0b02c90755200710aa1179079810541c101c00071b500f00c10803650401c0346009011504a030700300500c4030740d07440588444da01c50741e0025481c0004607005200300c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 453060053 1250 453058803 453058811
    0x809070b030f01050906010203162003060f04060c0306170d080c19140c060a09020a060f0c0b041103060a0213050607020d0f170d05220f1b03060c02010b01030f 70
    0x2a0001440b8015815140304482c2803026403030b080b00403850741c00307118205040c0281e403c0c0d80b00304021030740500c42c015901040c20300309459803542c10142c491408540c002001c00c100000200040e072903501038409688203060002d03000744c561071900411b800714210300c0c4055101443c00c0009a0300305040320707400b90500d010789280c8a0241c4a03a80c4084148000f07100f802105114000445007402c1524001607038941126864034150404802070102c0001c240d004100182000c41e9061081c0084500b40d10305813107008142000341c2c2d4080444400a00646010008200440d49aa000d1084500030f6020b6180561240104101c50031a07015a901c01031080404020351401a12544900700d022a0446201106400c6906080e92041c0001000300c502000000b05e1000280ba80d0f40014001e40c884100b104008a15103040140c1c44207a09010749034003034081036080040c442a000d5241440384141002d405552035540f601950058061400980d440740022096035a06100329540b00303c400c00240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 453061303 1250 453060053 453060061
    0x705010c080309011e090c081908180307030f14010c0e091b1603080c16120c050111040e130b0a0b010c081603020709060503030d0b0409120809070b03 66
    0x40c08821003010000c04254021000400882080d4042d201c1441011060200300401c80c500741e0091a0074002210a442070304408500d10341c0000d2502d841c65003005080c40d0751000e9860ba004c85803c0041050080e581a15440d00381e0345044c045100114440c0c0c0610342c11090380d10340b240c000c0601404150710b50389064640c1150036403004400114480540c1d8011090b11100d07100c14104541c442180d00c185030009510b00040c1d100312891040d50301039580d1111300c0d22000908a041c3c4194585190046243e41049000c1448a6445500e00da8a41465902051a590303801d0a480c00c00c0880f000001c000f24040020b41e8041103da0345c0308811a1141c6110741090359580c803504406080840700b15981c030981842c0740d0044028680058000724001d8488034000080d800f0000528000c6006024950001602540d070703016003400d841c0020051401c0c0a008a080e000400304004c8550b030098a40d811000400e80311440d01126180513683e0f149140b8000e54020b00c6c006240c0e10101e6034081c00c10400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 453062553 1250 453061303 453061307
    0x71505071d100c1e110a0603060b0a050a05120c12090303041a060a0f2310020c04181406040308070f0206040b0403140a1e0c0807030c140d0305090f070501 68
    0x411241202e43c00e15607084462400c21a1800c0907000743d402c0c090384040118414400d240608680c0c07514102e98041046448078022000d88030184100f0032103220a100c031720000da01950281c6a0107000340741ca24101000e25140c50100b078810341e1003016025001a214980d0701100c241190308c080701e41e0017946542001c0e500c400341458111525480f8410f44070204806540300304034403005050902d54903a01d01c0d00c81c2ea007110b246d19404a080650440700c0689011b6082154203206000865000303024212001c1c014440a13007504070142d51040315a26800e00001c100503041c1131110b48050041195290524010f00200c83c0a03010900707000296444c5140198002000b50b44150700c0412081d050b22246000d9070503402003c1000c0c40810042174a1041e80e42c40340c0c1c107050707200300c0000e645035041c070702841503940b450551400341c0803035401c005d00c60100740030b0055100d0a902c5940700365064030030004802e0810112403040e5000030348403018024000701c20840150903401200142920900e05000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 453063803 1250 453062553 453062569
    0x220b130b0a20030405060a0201021201060306050306011a0f0a11070e0c0708070206040b071401050f04020108041b0f09020909011a0a0804110901030b01060f02060f010909020303071505071d 83
    0x82e07081034a1180401c00204000c0c82560b00503c0007030703c038945a038214600039010350020f40b01d0005000b854030000903014031038001e039400c440e00034019241c164280040d010810078000c1290340f0800d01002140701c1ea45040300141030303a0315550723200b4041410b558600c60421740198007410440e4804424041c2c02c2c11114200c5001a50121903d651000c491000c14038034011070b071050b044420041041810300c503090b40003c1c0200ca006008011a60742c00c1c0c0d01c804014001d0307802a00281140000600051021310078642d12030312590300c51410f5036502c014a0390603905810105420b0f070081015041d501340700060601400c4103a000a4070031040c0464045203005805486080012000105080c0606051400c13114080504071005668403401c01e06e032408821f114081c000b880111004000900c04501d103801140c0e04212041603928013155080a04840081030740d00d400204034000c0040c4031060481c818181100c00440e251a048002401d01600c4448886001404841c0c0c03500310707910001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 453065053 1250 453063803 453063827
    0x70503042105090d030207030f060e07080d0f050d090c061d010c050309090402011202070629090a0e1e060703111219060b070506220314220b130b0a 65
    0x400480713041c5603080803450403001c1e600180049540c07907164014048142c001400c4180140101c590056070f441c2003c0e42c8160b000590700000e800500e8002d1030620a000400900c00d590b1800b04100e4a0f507101c03810b46202c290300c42c00126118100700c026003194580505c0c1030329400d0a00590721170300d43e11036940702d20503654858400c1101e00009000c41e0f024004000314150000c4045465070054a040e10003091001d08006c00412550a000100170f104c0e410f00c0705410f0041c14000490b140c1030000400b0f0302c6542210315150240b8210005081c0801c801009011428402000d10b8105200c01a0446c1c64240c410f01050104104c0f05801710503900c030301c5402071808400c01da02c0c5400e8407090402010719030000780740ca0b40c00040c4001807000024109002d9180d144150341081c51030540102c00000e5940014041850442c800606004120150500c3c204080541004201160700c118074028542c024a24000c400b03d000040e4100309009600500044189213190500e1184003410f0349076092 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 453066303 1250 453065053 453065059
    0x171c0c0c090504050f0a050c0108060d020f09040c0512011d06040506040b0916091a011b1e080304030807090f03170c1005010621090b04031407020907050304210509 72
    0xb070081010044100001c0810481c0402a5626200b051502e01d8580034034030f2030180082e0314040852214600104d07002c018076401000c141c0f0341d049100c144416040000c10a856071780703000070001180d0b00c1d400c0f01940740446200000400001d482c655840009031014061427550000b030800001a80010301150030035000540304690760b8a20500301e1a2008070742007d4a10403a80c4000205850141c00c0525481d000c03040c4070a14295501c01164a400d5042e0604000355044c051200881d03400410600d40e00145980350884451640b100c011130351044d5030840000d1407142c10403c001d540440c032200502180340c400d8401c0c6c0e02d1364480115003105658480101d80000514045880b0100f000c1c40b20403c5569042c4115039450074050200c4a0400c81c0b1000340c0400d0403020a00089480348180035503000c41c4420b210b455603142100c1150703c5000c00c1c01f0801040100601582d24080700c18800c002c40c1d50303401c4d0340c3d151614210141007800361091500b4000140d0200c45a80c01130141c4040d401c040e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 453067553 1250 453066303 453066311
    0x1c14090d12060305100204081506011d0105270a081f0b03100c02030c010e010e10090201110a122007180f02030a020a03060803070503160c171c0c0c09 66
    0x4000c1c008000740da200030040d1080c042c880705030b084160013420844207840260360351100c503501c00085021049408a000402100159a21029207000d650955906140c61810034002082a00700760303003000300071140700c0303070b9181d03400424500a8400000740511401824140e00090040c40d4142e103c2290000c0c01620750442c041c20351070400c00010b015122000601200803c02c6000c1e48940c4910028980d41d400c100f003440000c4414014440c912880d40c0042031503a04849500004000c5040201e0400c0210080c8c1900b5440c1008401d0002e400f401742210700c500c960402038400c40d250020307118001001c039441d5040c9230b40815124110740b481c2095100c88505005c01400802940c45801c1d9210b01c04420701c80a41b001e94060301c1e845044d9141041065201c820082e628050300700b0081c1107503c01c000121800c0e03100002c0c801558400d280c4903602689425040b05c10b14904d081580841d40416070340070442078030080916081d8142e0410301012880c032744946143c420b690113525015526 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 453068803 1250 453067553 453067577
    0xa121805040f0209030a111926120403120f0905060a0804060f1a0f0406270f181104020f0f03040c08120c010e06010501120c11031c14090d 61
    0x42d0b404495001000038280c0341c59081d0740c50506021451211054001c400b92040e0540c1c10b4807458420095450700205802c4032003007250300c100001d440c150288031500403085000c1c0c44254901c0604040c501ca840f0401260100060085c500d070000c020b444204a0300d840c0800254442c81300700c4103950700701e00d0090081c0c2d5a40c00c00071f01828404249281f06403070001320b03041513400d201c08e170203d04404440100d00031905a0030001030b100c540c080c2d10802032414003691400d50704601410f2503a00034500201c1c00b040c1481da1541115698900b4a10081e00b061000c4100248581b481c140b10004070350440c184038070388161007424090b441580c41020b0002000c241404001c40001c1d008203a00c104484001d69a01884255a0041c2c0c441d64059800c0071241c403030303510000c0b6580d03042e90010395130001c03140b4800c10780e00c010b0682c0c0d0403084103210041c0400400e11303d080c001044042c0720f00c200481e05600c072803407500858041115012003002d5113400e0000c617180109002142c20b119180020440032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 453070053 1250 453068803 453068831
    0xe07080708040317091501080c1513051e100807030e01091205070618030c021302160b0c07120917060603030307080910060303030506040506030118030f031104080a12180504 76
    0x3403000a19200c040300c3d1b0000190040300254550f0b00020640d6580c60b1200312a04909181c0911480d10b500100000024842070400c49401406a03400640006421450303030041032a00c0c410894050010340c91004000d8129014001d0080660030782c0000c106031900d94442c012600c104550b0039080000006400c414807110b0340240c0031140c8106a80ba420200c03d01d8003400344070382c0c00c1d8124040c0c1c0d03840614900c000c942d8401c1d186580250a04a00500180d60350380c2c205160050000c030300c0b01c0060000b00003040c0ba403624408101200d4031030914003410030440032004e842c00b184400184c1c0c0010b0802003251004400d580d001307041c6081100c3c00e611900d10090600f030780d901d00c448106250280c0001403581c5500440e0003050141e07130401c00c81c6c41d950103060a0310321800a2a25040000c0140000039200b44038122006045180018060002c0404900c15501c15408810300fa40280041c2044c0300c1080d1a8000f0054141489018040343d810341d405501c44a2085500c2956592601c1c41090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 453071303 1250 453070053 453070063
    0x30307021e2e0e090907090209040f0c090e01081b04090819020106031a01050d031206050a03050f06101a0706060e04031806081b0702030c06040e0708070804031709 72
    0x1001410884410003540703000d030b220300d01200b80d00100048280c2c00d00d4149050200c0d001c0d005079907400140c8103d604110b05503000e9407010716030b5900b00da52141010f80504140c818a600c011320b030b0362503030110b524080c0e00c6500614182c0003280e03240c0002d4a074a400d10405040e8104480c0140c8021613440424204107005000e14a144010344004603201c88880340d0640c400310950707101d03480341c41011400b641815a00842402a00c1d08007080b481d414000c40d00601950304d482d0701094010807215161f0340450031903d91580304076007581c030401404040d4003042c806c40e41d000c5c8990f12051511890050202c010100e000f0400c8000b18001238407005100d0b691304841d014102c0c9003006500c0703040c5464028030108000b05c1403010708680c8400859003501c10040540502504582120100b42c200c045401c154807141080368140305000b07843c429034440e01d01410080c0703c010b42c02110b42c0340c03070203000e00320314001405d00c8100064036041000013508040c000c0310b4240070558102a545e40e10441038a41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 453072553 1250 453071303 453071329
    0x1021005091e0d091409010b090a090e011a0603071b15050705040602210901051b0601060503090d030b15031924050109290f0712030605030307021e 65
    0x80a611810404800300c0000c100f030200c02c45603034500400f95a541d010440152621260358856a60b50040016107440c07000391482da0801020031042c136035212070510407a88154880380c01c69454000c0c8a841002541e007503038540409540302c41c90f52420041c000c207001c602c80380100340043d50131005010b00009064007001200103074801c00c15800c015401500f560130502c11708006107c2c0707841c0025211f000505032802504200ca819080219000c010348180e0400c4151590b804041142801c0014003004418020111a220b035503403420100e00c09805d140c0c9d40d509010901d41040711541040c2c451034450000c030345030290329a81700c3c1c940101e441d0381c19010140c80b401041c00c11001d80d00b481000000c2003e00100038050703908490340c40d8010360354900d4038801c207801881c0751080402a04060003880700c6a00040070350f1032078855807880100f80c40e00091025540c060803010707140850380e014440ca034050300080f002581460880e074009034981c850f51519000c0944660750300c950300d4880c0d400c0f41c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 453073803 1250 453072553 453072583
    0x20c0f100c08071e1202010e0d0f020f0313050901320d321908090409020d030504030501180809010e1c030512060901081b0d080712020c040b0102100509 67
    0x722884904e000540707540120540d800c60b2041501c04489005216459a1041800c050314100f40ca81c41e043e140c80d0240300502c400c4d07025080052113014811300040002211060001e0311542c2444244991800160002c1d8800c0b001403020b41441c0e013041c0c042c0078a00200200520a04140340301060301000d840c200248200d1102a180031410080525000310003440c1c0b4001c407586d0b0300308c0d5204e0faa03199110104580301e42c1c40640400881c1081c001000045000340c804a0034903c10b6000c5444030b00c3d890410b800207400401d00b0710400c80300380110b000c40300c04a03414440130251500c58902510407007005505206161080c2401034588078402d140c100c0046400c20800e0a00b070034054134950011103a101c0070302e402c10000c0c0b01ca00e40b06421905035040f400c01010101e001c40320402144036250481ca6100021502a20009038010024001a80309201540e81c586085c08042c0c54178801c40780951090f801c11a0304031250f40d00090026408907082c4d4040780c940c4801150904099441c600644 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 453075053 1250 453073803 453073823
    0x20310151d040201080606160f1703010e071d060d0207050a0501020c0f0f070819050304050d03030c1101112a100b010809060c0706020c1e0c01020c0f100c0807 70
    0x510201c1501d41c02e1181d0f000ba2500c12091b580c60781084424415100008004013071a80340e8004102070601c088802c80c454841c845401480c2d503148007003604242d011448445c1c02404100e980e40e80402c03035068040c16000658a440203900c0002d40c1e0303004410088200179404681c2c4001d22100b00309680d0703203a0b000002196545d24220240741c8a100c0c80c40041100d2041c00d1503841c011500040720000c9401c3d10300680196440190f500784807980044080d00d0130300c410702011403107a4400310101301c0507119131000251551500d50103050500003c0c010b11159140051a403c5614642d0813158035640c101c1a80c003603a40341c01d00507500d10042d10b4800100c0c0c420140400d811000c01d42c050f4011460076252046d05660f2080e003144c1e29503049882c444a07401c240400400a42d6030340107011040c071540c082e11145003014011500c1c1502c2066520380135800070340080c0309541c06119886008900f070314030452100c105c0000c548034031018801d0508111125000d0801e0144003800e0354001c507404039800d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 453076303 1250 453075053 453075089
    0x2120a0c0812010816080304180b210c100305070206040303020a0512010b091804031b020f03030a021c03020c1209041401170106090903080a0b01050d02120901061202031015 76
    0x1661781c1840050f02811200f0258081000c1c41c2c0001542c04880c20090f020692414030030602c0054080020a540c20201c038090500c00c50800c0c80c8060f500038483c4c070007050802494810003c01e028041b0808040c5450a8140096a540462400e9000340c1600f0b0142c2ea400d0300403000c444510904001e10352003400c190020807040e60300f2000b4014410100c912414440051541c04005031043d2002008100555090b404104c5e950151514003400281551814801d03e800310307041d03600207070040d401a040490307001080c1c045000440d000701494a001c5040c020700144099540c8040d030547c400d20000441c4102d42c55569401c191103500340d000040ca52541c4d660743c00459030180072024002942080400700d40300c1d0913803288a56580d01551006820f40f00c1c500803000903c5800c2286040020822480c4068121400103006440c85440c10301c82624184080b039007101d03260f80041e1510b07081c0c88072140240e0741c000340000c0d002d80c10740c000141c24406d03185850072600d440c0c4c0c003071100c60074035003461 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 453077553 1250 453076303 453076319
    0x20a090b091608040b2716080105090304120c030605130c060906050702190b0406020703030e0303031522110c060f060d0308070207090c0806010e0901030c09090503090a030f030f02120a0c081201 85
    0x140d0b5022404001c01c0c0c00303248c6418085003a604201ca51007007a80c07041c402003140004030360074903079054001c130103584005442e0345030750007651012114410414900030f100401c100800c0041740c001c10151404c04196401c000004005108030400a8410b506140200c000083d0b64000b040040c0400c2c0d0501c2d41c1c0d55170300c000280d281c4006200a401241071841d008480b41004011a8458044030740300c2038904120b8400c215052550030b0850a41c51520f41d070202405449118034841c110010403100d031507100c00000140381c8080181949180c5591405000d980c4e2600840c000c48540e2500f025072541d035620a04a1402e000c50380503044590424140c2c414840d00710402c640130b0030080e81e0f03182071909088248841008280b0004019a030b1840041020f008180c1c0303d00c0842d03204400703a82c80c0c082d0601c00950340c507407c0c1e00b0554110141d900603008040e0800e5080800e0016400940f116003039420b4090014001c00e02c480c014488511211700421003d242200c50301d622440b210881543c6400035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 453078803 1250 453077553 453077563
    0xe07091a09040c170303060109061d0910090b01030902060313030c050712030e06091e0109030602031008071d0406150b03090106080105090c0a030f030c020a090b091608040b27 77
    0x140130440600c03840021101c01000c000c60f4810380060b12000c102c6490403100311980031550a0900d00d02c0250141d450f0a070355850750160090b1540c00d407910249040a45000c2140c44040c4401d040c585404a041d0042e101c00d015641c1c458078664000d405440346050030b0b5140088828010064000d411000ca100080c4141d01a03c2d640242d40d03900400b400e4800b40b1030305210f20003181c1e80c8100e2016801c2d0383c049051004440c90101032510190042d6250340e40b1069070020f4650030085040c0e50414481d004040040400400030601c8070010218201400440301c6c80140003c1c0409440d4400440c640c0c605014000007004c111268a94900d03142c0e0070b0034000c00190003000f5455080c42c2c00300d0184e4800040c100a01d031401021813202a00d1503a034810503840c91203044051142c1554041e0140e9031300d003041c000418184401051807480002045000d004c010462304500f02240b0341003d049902490070781e40a81c0c04429078420740c03211900404c1500ea0300078a0400301c191050800485540455 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 453080053 1250 453078803 453078809
    0x702011a0904020120030d09080c190b010b0a032306090108060127090c03080c06061c11030a02120f0724051e0f1c0e07091a09040c 58
    0x1040c66800c04209003002200042910084d00180402c2d8105001c0081c902c560b0701201d00d1041146d01d020310301100b680c29580d41d24016110705e200410040600c00003844500080c181c1003000160060b455590864141c1060113000700f034550200300215554026407081c3c441e0301c3d03140200030904100d052070b102851002c4600d540118034040000614800c000f5a55040c1c401d80f00070038040c5d589905400e5891400c3c2d5005e000400e865985000100e401910315402550245642c0c40d40c80e410000e80070303d4a0340c007620303c2d4003d801c4420409048403143c400116107650060a0380741104c117082c0068507240c2003080203548040b216920b41d5514000044150301542c0100031f645141e84c0d106580907403406029113040c1e180344005508410f062103000102100c0400f256240302002203110b90088580180161140741e060005110446490300c1c540c24083d040e01340001e118030300da5404020389890403445861070050f147c2050202e09210042c00b450720b01c0002d00740141d24030702818145080d50301d80c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 453081303 1250 453080053 453080081
    0x2090301062c0c0f0a020717010c08090a05280c0b0301050f040219030c02030408030c010b010305130c06030c0509032a1f0c08041503060305070602011806090203070e070201 76
    0x1907070411007a49410b000780b00d12072120f0b0f22400e010340310031030a0b2198041c00c400f0086010340c05010503605044608001c81c04e02510000916208004002c0c0960002900b840380c02ea01c51058000050030014083c1304016003440d0602d40b4003200a4009038405075034200820f08210140701160a01c45200514120741c01103070381040700402482408101c0c8170341103100070607951282c0f90520441c0a0b4200c0031178071045104981c0303015550180c0c103045420286024610b44d45501401c0000d43e410f00500f45c002d1011602d150800825981e411240d602c584142c03018117480c0c14200c0c0324240900141c0c0c60410002d07058642d107100d54044561924022040c45110800302d59203004103003004c54100c40e4440e0070811070b050028004100351103413581c604044030041e50400010070f0f4010b0001d000400da05c01e5071000b2481d80d0641c54540d061096a411035011a031400781c00003003080940c03081711000c039002074001481e59441d0000c01d0400e0105d0308074054403050501030185541e415480b04080030001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 453082553 1250 453081303 453081359
    0xe0a0f020901050105210c0c120307020c092818030206040b0a05091e120c1c050a02100b040209180a05010b04060915090e07050a0914090115030209030106 68
    0xf84005403041d000300b9149141600d100c1610b0344201603101e0384250410b074100400c900744482d8001483c0b5000040e80460302c001d07408001d211456404005403180d03901e04450008003440c01644240c86003284070300b00e0020703415048a00c0a1700015901100c04040d504880c000e0705130540c100030f55201c00030b07202115000c050200181403003101d40324a600658890024103600482d82003200c170803408000c0b01c5520381c01002c120000c3c0310fa49400a184041c20103010b0710160340c24214103940c0100d020310035400d0184c00c014042550342e010078008203520805900044143c00276000c03900034000c0c10000c0b50041002d5005c5140d0040356181c0b28032880054200307122507a01c61200b1a202d0080307203c3c2c500030440805040c04510b0150380003850141241c5030407645203a5403000e000c40f003103051301d004000c2000001c60703611309540105683c000d03002c8604040032080c102c4c8085910100144908607a50390500600054580700e90121f90708050010020f207e25511a43c41c0d40e8000d00d03003040001c0800700c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 453083803 1250 453082553 453082559
    0x70c060e2a10141318050a180308220f081207030605030303010e06061e030105010215090c060906130f090b010c0201090504021303051005060a0806010f05010c060e0a0f020901 77
    0x1e00d0441d01e405000e0340d00c0700082c00d00161007414a8011140c03030b0011308040d9101260b0340304c1038450001000703031103080410103007401841981110159502c26007800118035415000c6038001e944203400041004080482d60b00a4541d20150048280024131511141e0307000414414500e01421550480040c000e107640c682100c01e0b822a01c003440381a816403c2880108004140c3d915859402040605440d142086055081034003c0d0b20344800172034650040010b010b40c1d43c3c10803071504c8603141406003500c20b04214020031355902141101a20810001070f198005840e00410780c0c148507820703981c0040c101d4445c0f0b004000748031280688200d2a2800c200c2048940c461811401460b8060312028482da0400051101a6004003034040c40c403c000480040091010042c18260003400c44001030302d0300342041040340004450b80711b07178401d5100800610100490307480c01d404031a400d007400500c400762458110090840001070800d01d01034081c0a20910807001c6501940ea4802c4440c0d40961380c0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 453085053 1250 453083803 453083809
    0x2a0405090a0203091e0d2a0c1406280e030d0306180c050d050c0f13030b100305030406080402010318030f02071e030618020418110a060503070c060e2a 66
    0x2480d843d017224591041c0b480174030550160300000b500b45040c0d11031800340846078a4144500b241c000c4104c4010715240030401454050710000c02000000f140d00d00c1c50f100c0c003600c00051603400e44c400f0340c012980c0d58050b180d04178010815031040c1d02d405000c0e00c00d0611165805001020544200420080c0b0030201c0c002401c4e0750321402c06a1815500c0b00307402c140c0921921801130000070803940442030f0410100311000d8907080500100d40280f00e040d00300341e0551a207441404006003006210540e60f40040c0006100802503409031040c601d041d403c0313580c3e40d0004034042d0501c8904a00040d4a0344081030034035a10061010291026808071640303950748038540c00701701048a8010841020450041c00003426580005200e50841a80c419a915540c3c00241c125a88841c100c2e0720400010958810042c141c5400d0490510458142da00c071032030680050005c0c80028926010406070011200230008241d000c19008812002140d03004040e1500800c4144010300c81c142c1d4400d4482000e124601d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 453086303 1250 453085053 453085093
    0x30a030e0312070c03020a150b0109050a08060615090913060b1e010c06140108030a11060910020f07050709020d0f0b1309141006060806092a0405090a020309 69
    0xc000550803002c40d035900d94112807182102c6001c034210301070502d07040007060b074500320511514640301c000181c0a4a03d000034100110640c8118011050500d04100c85200840c0c5541c0c0910182c800341a620041c0200b000780348a00c07030341d590340101800184004182446a05c03509240700780001c120589000082040850b00c3d01c82500001003000754110390f9520070a100700720303584500008201c0d205031001189560509820151055101089080405900244900381900b203980030b010070f810240e0860342c86000d641c8545e4481b94001a103425a443e100007141c0c08681c100b42a1350002d0380760b40b00c0102070740c030102681641d9414802600d4804040344a0b01c495410700920140a070884001048050900c0030420790700c00c809541d526020500610100d40950711900e400036200c0d0400801404032040036240501490b5000100107461030042d000e42c1c6800050244200030b100c411a00b490b1a108507000380741c11124010500404450680155016040e8a010342e501a07000070000c081c48 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 453087553 1250 453086303 453086317
    0x11809020a0501030b060d061707240507080c010f060e0604151a041a040e0a0c0815060409150f0603090b0408030a060b040b03040506060f030705012a05030a030e03 72
    0x1c01c4a20811543d0300a902c01d0040308400b422031800d01d00070074140411205035074071030b0602d011504241100001c0074441c4d01c0184c902d143c0c41941c0c00c50008034a5a081c038043c2c1402d0140a030004002042c050b480c4c0685a10301d107200000d00040130700c408014058445032184038841d0004202094041c40c00d07000720182c14210051101c04079240c0184890080088500003403244d1040202080002c954604d13030b00b1100c441c1d129a96510320300700e002d05100ca03000303112848292030000f0340440e00da070003c0c0c460380010007180ba030703890b03055594006542c1d44110342c021160b140c03500040090342ca0140080c2c41c1207071800c10248010310307514a07098040c1d814600c40180005100070005002030440c101954101d1540003001603039585500720081c5592281d00107000d9080040100700030030100f000707841c0d80301c0740944816201121440c003203599213501d0f009441c1440581c00030550700c101e5803010b4508080d109841280c0150203410580d460f580000c001da400a0f08050000030b000c034000040f2800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 453088803 1250 453087553 453087559
    0xc01050601032d0e06040b390c0f010c11210307120b0d11120c06191224091e090317040b070e0901050a031103100207080301180902 58
    0x94008507289080d8028240e083c031800d10398031844031140f0002002100c0c4078600c00c0101c01c0050425880750100ba502c03000c2003c00041c0d5401c40c4200303080b0f204c4c2078060641501405281c40d0b030b045801d145c0c00d00301c89880744549903290001900c1c0560380502c0d2540c1c1514041c0965000c0d034661810000313882042d002d41007079010100040b5002900c5100450b0780d24a0080c0f0006130068080001210038000b030a050307958400d902001c1d1464a440581210b0007000f030f034002d04140403d8400b1904a008122001621044c2e490792102d00034003070308807003028840710710040000340d50081d4a80d43c2003040e079586104021041d00041550b44a520a1001c0c102e0384099001d43c4950380c03002070001d0f2951031422410048400070190b0702c0000d030381e4402e010714850040d1480301e241003940242001113000c0414840c1c05031100400c000d485190352601507c0d040400706036006480d01c0460702d4026850001e0002034400180c1005115004000d903050b941303d419004c00e042e0b920b011030380c155905040040c1d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 453090053 1250 453088803 453088841
    0x10051009090c0608090a050102070809130b0307031101030e011b0908030a0e040914031c1a06030613090b0f070233190e01050a0b01020a05032b110c0105060103 70
    0x80078130300400b5920f0784411144110340f081c0e08a42e64140c00d80c0c10441007290b8481c07010880521a14008600f02010309111208100c000e031104c0010780d4880c0d0920001d452044a4000c003100e6902c650400b0703c0c40f0300510000c1c8450055540d079881c881e0855814036000844250001c42e0454001c000c4a044514a654207010000d4030020080106940c100c1141e04250b680c10f0903100783d400788050003d41c00c2884019031480000003001065a400c0181c841c9080d400e80003a40041c4e86034020380703421180a403005511408040f1b9000020300c1c15141c05801b402c107440c200612031076100c20319403040f500765013540c030300717260840410201004a1000c00401e04907070342c1114443d4545080b0980c41408031110900403c3d002c800c14080760f441924041c071903519001005408911401940c103210020b2008022140868030344588a00031464070710038000c80f035429841c820f00000c501e090f100c410101c04012010581500d4801b661124051840300e5081000184a07503000344038441304480718200900d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 453091303 1250 453090053 453090059
    0x50301030506220c080606030f210903030c0307053405041a04050702011d07050904080705070b03180105060a0515090301020706090f0c0f0510030c020f10051009090c 73
    0x182c0e000f0079062a856501890201040c024405200180b1354038020380214100320b030600d07080c9072150400407810350160310750454180003020126416500411410340760400d040000e401c61150780e4405049d8800402e400702448004900c030151140700002c800141d0240c2500d11090118060100400207102202000341d81060b8006103e80c2c0c8141e2980c40140d07000c03000240c01c40c0c0301541c41000503035582c0d44000a4a4854800c2003003081c0c08001814050300d00400259001402080240f054502080c90002c020341000f00c42c000d000c0c0b81d0180b9449240881c080120500256070040e004c0d07003800046021410500e094030b003070714005400014005c0000c2c8071219290300200b043d41e0150350804c0799002107040392080c0c81001c1d01c5199064036043c400d081810710780003550841c0c0d0030458204001c002c0da80c2d4031074007031081d148503050106d40412904416410300b2002c000c140c92a000741c243c40344850900c1c0e400507200314402c0c1c2c4441403150300c0d1150807003240e0000340014403403a8601c80c14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 453092553 1250 453091303 453091321
    0x1080303010b0c0a0c06230c0d18031e061a0d0209090c120708010b0901230406031e02100512060913020d03050414010c03020a02100509150316050301030506 69
    0x9280c0f0305001c0045910f010b040d542c6031207040520b54480030015003d01071481d80e1040c2d0039040440041010174240c24041d0701016291114625800c880c18407450402c03081c0074040ba452180c000716005000c40d140706070540001d180e000348818049440c03500c4c058018201600100100406500280003036224041503401d010414034050a51901c40c40b45004c00b0b00580e82d050101d010440040c40540031403440d00f89450b0039101e6400c084c070320075064000140a00d800f082090581c0b00340c07500302d8100345070200e03010800500e80ca0300302070300301403144020081e401c08803948160b07068800d030781d210384641c040d84044401d400760301d001d6007122a1000c00b00310b80d4902440803d8011642c0a05c4c400520150760004101c181c1441084000c00c1001c80c04004940b105c900d020b41d4507100707003800800d000700b81d600203455180c031440081c03044d0520110045002d10460030740b84061070140c60711103a010484140042e5400855100c51001c120452090b8441d1054050701c1c1220380c020000c02041d141c030011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 453093803 1250 453092553 453092557
    0x60503040609050111071a010f0b1c060b210a0b0d020607150c0c0c050307062a020604140a120c0501080403020f0105040f0b07110c040c02010b09010e07080f01080303010b 75
    0x30a42e0300d592513211700541d00320650000d100d841d125080079140d080100f141c00d400f41605030f12982c607200d8011000c04c042d0204c04115002e41001d855800380745031403280c0042c0100002c0e04250708100020940c03015143c074900c800340c228030364800703c1c3c0007682d201400a0240e5031100070050300450052810390050805002400006115554243c030301041c81c40e4403011a502004400005198038000c1000c2c46015410078000d49015005822140c0c20410003804500010402d141d000b0254042e0301440b00d500b4041034580b13540241141c0e601e03956000441c0d62410302da80842d2045081c590005081d0b80d01701c45d16103209600c8015000307054900801900c00700c4c4000e00c242c1c2540103207082e13019007031020310529204a1149000982903400c0c1c1c105640c40000080c00030b0144144c0d5032100d0401c002c005488803840900721804104c0d05d07182c460032030140070300a8445d43c0091502001140d010f01c041c841c00e10a83c965920082265a181280344c032507034081c80360106130b40003000180704500c00600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 453095053 1250 453093803 453093821
    0x60703020c0301020a05091813030f0e09040b0a2f0304051212040b07020a2a0906180e0d0c03051305310b010206060616050f0f160605030406 62
    0x54844004070394022a0982c0d0106110300b0000b00c0000c0d06d0051450107000c1701d0400c2c5403950514006107000030441d845880d01080140c2401440c400080b60103200f0700320b4105441014012014604052400150060003500d00050303050800000c480000398614107000025070720705171007061011000480c00c0e2580094021b6500c0d0242c180c2c204c00c00600c45c40105544000c5ca0207028052515040031805284050012002c54010351401000329081880c41e140403070340381c1110540b2000b07644038188120b9890380000212800c0450020709042e0641c040c289111228000b8810a440e6510003500ca8030120082004144000d4203000428401c001614841590131105d040c540d03101c0e0b0003d01c4502c2060851454498084a2010025050741001001440e14401440302d81803d0780003075212480203121601401020507000c10710300c02c0c101003904d01d6800c001074a2402c00c45940e11a200d060362180300c0c0f441c0c400e00125415484841c90107400311005a80c80c9811511250350b4000a00700900d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 453096303 1250 453095053 453095057
    0x6051806041b080604080702040b010f0806040e07091805060c0901020303070e030a0f050d02100209130504050319090e1e010b090d0503130509090d0206160216030804061d0f060703 79
    0x10100e41e40c83c00700543d6002d80c1c022030a054907004188100030035114401f501d5410082c03401d11502c1507a1b000480706400102c12a800324030803a64100c083d18145c040e501000c10075007401807050002c03100c1c0742c90f1208180144240d55855841100c52000e52281078442401a8000c10000d00340a109075511002d0303000040030f6500f8100c40e61180007000700103c0c03043c5d42940181210210140d01084006140720511100b03600300000031002811301000c0c50752503282d0a4441c800101000414070403517074503501820311242000c424140041c001609801030400001984001c00e029807a001821071541c0c1e94554180c03203036800c114800d0560b40003441d649402516034610540040d40c1400604a011501c22213a22302501c0c11003003200c0e4000c0540000700e25080a2031005500b40d000c030348150f1240a40c42e10a00207184610101d1030071400c890250401000b00002004005d2110010000c9135250369941c2c034404a484110802c1444c1c0d0709240da40818041c14001d107a040c00005440078601078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 453097553 1250 453096303 453096353
    0x6040b0a0e070f140306090d0507020103021e04030c0e090a03030911040c03020a2307021c05030f09040f02031510050c0106090b011403090705011d120a0605180604 72
    0x1140032032a0003083d402032110021003000c1800072004a850b02c1c070032028101c00911071801c20b0341c0b4507906d0f41e07981a803105c00c2080018a43c01036901a40440c2c41007402c03030080b90070481e619100a0765a82040c0411520700c11004400030300e145601620f640640b4a030405802401c046a60690060207040400c84804802008400d810b07541d40c4640360085446032405603640100640c0101080a200b4015201c1182da00d103540b80d002c01102034907180da5058407582c0c000c103c59062800c2714101d0705001802848006181e0303152900510141840139400e031030512606089030030f821f0a81c0011581a02010f00802c01401c2619051710000d80c401468144245804c81c0006c0903425100150403002c0115103071001d040c12540e200c4007591a403034164907828207508050740155295078592144a04000013460152a81c503044240388081c400d0090094840301c40c4d50b03002e2903c038075210f4002e58070135203804009240382d021131002600c81c1e502400074001d1580c0355541c0030010a440040018000701f6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 453098803 1250 453097553 453097571
    0x60c0c0b2a0307030c1e120e030f18090106050702130b1306030b0402090618010909051002040801051504060807030206070c080706350a09060b091005090c0c06040b0a 73
    0x1c94000c5005078010b40e804104880c004001401c4183c0b804440c0c098440400b41c484201c07507002030025491640c807000440c0140c0b02007402440c45c007504109005103903001812621a07420480790300110501594175001c0d60381d0f61001075580b40100d030400381d04400d080710b662035040c3c825030014140d56001003060906c891800028001c444580d001128804007420134001549080c000240e4485001c0721410400c15090440203007450062040c0c5000d56100c900540410a06005200b120b001c1d10a045441da55142101c1d4041c0005490070905e1200d1150001c3c05811b250051f0015a040000103008a5140d0380c24042a5400501d09a801c16110301c000318603150144850b1001703101e25946c550b180d400c0c030a010b080802c0d54490100e100c1c90441940d02c008500c801c0e00d10751044c41240b0004150000d818501c0141c1000c00310203500040c100c04004c1031043d0424824140c82c415a054036050343d0b01200200c00e4841c010016800c0d03400200010001451500400da01c850302c06804a00045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 453100053 1250 453098803 453098881
    0x905091e0a110316090b0306010f18030501050412030b010906050301050f06041d07080f0f06010c020105120f16022406030a060c0e1806012c030a05010603060c0c0b 72
    0x81d1408000b090500380c03504c03250707a071201602018043c1d40a8803403640c1845c40000e0007000704014124144103109401c0412040000c7c0c88000454120380244090304d0603203009142c00307c111031250f020a2a024401c840307035108465000546500d80c48180c0746909020410040510300c1d0302003030740900c0400012540400502e4180d49400403201d03c040c0300c1c10f05400140c09908010423191704102c400c1d0412a0400001e211950000d0080c240590b0080345800100c840e8420307040b0180d502450f881c00d200f07407150030204030b603c0340002d0180349640c840701250480c0c82e01988180c80895941408281050241026030740b90800c4000b0116402d41ba443d0b40c1d0042594490394488000c24003200c01c062080c02d0011400d8203140462103c0c80182c9886400648a51a104150752440d0140f40c20a4440e10021004003503010009044aa0100c1149889030181c0240c2c00222800c1d81001520f0040d00c4c05031004d80185540800d0040180e80e0f00c0c0040d010700c48003000d4808201040f0200f801030310b8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 453101303 1250 453100053 453100057
    0x3140f0f030403022e02030705070f0c0303080601031109060307030b0d0c0504050c030405100b030f1501051002011b05070f0204021b0607020c0607080d090c080703030905091e0a11 79
    0xc012261099224038150030041d050541d8244d62046082e15104a90310306000c0e428104442090b0354001078a0380c40b4090100e0b0f4074001d50600405440743ca91108052248901403501140d209654000c0e80356a100d00460690f040389120400c2d1700c809000182180c80d00701e000e544e010149190018840c52940700048a0005d07000042ea0201d0010200340110b0405000c1c00da4440c0d172203401c60b465400d013076030f48958070400143c10900f996540c1c4a1040999400e004111040800b10112884c842d800405040b40840a10800d44204800c0d28181035140c010300a20701e0720f0055407101120b490b001c003001e84440d4840001262000e92441e21240140d42d54409042c03000f8040c0309120301c150401445500d0040060b184c0c4041d944a00c028229540e100f00c21660519408441286c440d44e104981601038070074688024a58000480041420b42c000038030079086901964440300e04d039607204244410954149c54105030102091419000e0680400d01340340c1294111b040080c43c1061070014000316 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 453102553 1250 453101303 453101317
    0x50406110c190f0503010b061c061802120f0403140703180902031503150601050904020d09030c290403030507050c1b0f031605100203070f06060303111903140f 70
    0xb41c403401c1424000780c0c0c0e48400c00c07006000d00342c00800484402c0c034001076581c040d40e4801145800760035182040e90501c0c0c2c00c100001d02409116420f100054070b640e10103908005082c0b01c100d40c4401c0051100102e5a01a5028641546980424000100410030158003100d42501400340b05088244820361b0315030724800801d68540c00507101d040aa190260248110880c544a0390081e880f000c0161000d01a55801400909009039240c000700040381c0a4002c006112503c6803420307645506241e042440c2c0d40d0054840c0c0c01000014450703131458018015048418203003084c0250015000034020362219401480f507080003800c1201d800c00b49898070154a001d031441492100d0003111506100400079002e000c1140a4400c844203003014282c0c0d200a8032440d4480c0000002c00b480c014000c0c000c41d14002d0300308000c06400340c01420b1000185c0014031040740059a0401c10142d40380012403003604080c6004100d00c1343c022691011070301e46000d014034080960341040f2014001060400510403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 453103803 1250 453102553 453102589
    0x40206070b130c0b120a0e010b120309040e0304031e02010c020d1a091203160908031b060105040903050d0b04060503150103050c06190507060603020901180501060e01050406110c 78
    0x20400c51804020005541e48500d1000c1380c248850319048030a606081c5c1c2c0003204810004050000b180ca041c0940300c00b00300e06402441c54610326030482800320062403185c500303a030709110b0046000c0845589204a1202400c40e1096042c1800a00b01c8051210000340c014507103402d60001c140c000804800e50000704440c40b28600c00d103000c19070303002c440380c2c0e902071700550290000403196410b9a4107880f0042c011495903603139182205030b042c040e00681000e81070403022a500d9940143c800c1c031183c2100c41c910f41e00c5110303807400000e10f40f800c5d0080c440701c0d0394141d03901d0b42800c03081d8040f0f202400c816a502a400f036111310b404280c50301c0400500400100d5443c0d10f030440d515506001e420a100e500c01107001c2c4508000e50f0faa4000801c1000000b1090740ca001d075a2000c1d241803060060925400082d8850200e100002d202e403c0b0306411324944c0b000748401c02080c5d0b41e510b001c1c0c5d25100c142000790b001c81c800340000c00495020700c0740508034106d04400d48020032051000690854a01c94100b80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 453105053 1250 453103803 453103831
    0x3070302031306050c0d0c020303010f120206120106080a1518051003120309110d05070302010807030f1d011514130b1003020417030406080f0a0b03010f0f150b030f040206070b 77
    0x10ba06d07059018044600300c0d9030001c0c526550401060f030039900468001d1064482804400e41c1c1152185c1d004c07117080311503500c81d803903455840e8a001010200c0568403031504500705440010351082d13040c021021909902003050421845d0100440a402c0041c1445600303e02101d0010205600e103119841c0c074045070303500280d48066450a00c86800c203400d40341e4090341004107444001040010f41406030f940900701881c0f075035180f0008038040e014000c20b084003075081480f40240c00c0001d0500340350750b0b9082c030000c1c480d8108402c40c0c44c05180881c8210417580c45a002501c0480c1002904990758450708000454861420404036032248050a50070f400640d00007404c10858113481e0100040c0e400503006586843d05d803031401414004007030a561404120324001c40c048518550240d0391244003c0c0080c010702156507030343d100800024200f0411300b4105118011021031092681c4182c800f071450700341c1180c60f2060704c1fa800d100010b00403030300480c2c02c0192001103020281110301c07034030384030001034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 453106303 1250 453105053 453105067
    0x1030b0307091e022a03130608040308070503060a050609040b03250f0311131b080106180501021c2f101e05071206140906030a030503070302031306050c 67
    0x4504030103084202c80c0901d01c14041c00c1034220480505c4181c241300400301c607500101080e1000c2c11440b0741e902043c8813640382100002e40c0ca812180003031145000b0340f18052903070b8680609071981d2008849072039000c420a8024001c500d45040945181034010740b0004422084501181c50b1040d4812a840c0c00c0003210f9403403c0d02e0343c40d043d489004d0f140400d190320303070746103540d030365914051085041510808600102e001551410750166294851968681020910520300540501c8080c05030100190802d4a18404518010380036012070308181d004041003210703501e031f414020391076820400c00c101003d5080e0842d003441c004418102c80551903000f42400c104a980c1d460901c1a0790000380c09401c0010103548000a07084004c0c4600030010f021440e583da60380d0454220620030302c142e203202c0c82c0c840c3c08601010019002484070a00751840c3c800e0340c03111000c0558491a41e00000d000038400c00c005004680309401940d00f10041180c41204420300d5039400040d50012642c0c44104100402c0c05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 453107553 1250 453106303 453106331
    0x210060501030e06040f11101e0306080d031d0106060207090f050c0d0207020301060803190e060903070317040308040b03071b0b07030e120c011e14070e01030b030709 73
    0x280104402d080030407800f010110038a03140c11004002800b011003aa0902c2c0500000318402950108010551a05c4014081c40030b07110071069480107401512098071818554000c0c03003001c09848110000344600310148900310064104e0b50f04c030002940c2c0083c8501d0003d00240120310241503660054144181040c1112080341c9802608080003800c03c401d2082c488003200c202e5141000000c8056036954880c004240907140c9680080001d210024540c0000605c00300d0148101d030340d5a642c0c84070745940404005907030140c3d03072005030f1640102008000041181003021422402e55500030708081d525111a8260340150b0702481c1301e91000402c001d0043e034880070040c9015041480d000b1a0b01c0151250005038074002d081806042c1e49402203035002808001034802101164007503982d40451014082c0070382800d80700d00c040400844a140d620b05030724041c100107051081c076010003590300c540d0100c65041843e110503060546c1c40c402e00c86551014407c02020300184880440c00c0c14400c501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 453108803 1250 453107553 453107561
    0x705030d08010b07110117010603060911071208100e010f030b060d0f0303050703090609060e0f120d09020d0501021201080c04020901020a0b0615040e09060c1602090a1b0210 76
    0x110003001002070042c051030600c42e003981c0589401480b002107610002c001610105a040c2c18030820461103400058010340c150001020360342d00103800d200043c1b0005812660b03008510005058070800800d043c5103030300c15001154480e0030444040000350390b178510380c502658280c212426641c0d01314818401d20084c0070155070060360a4441708061826521480d8400c2080c0100404141d114404038031458821703000000050340052007000002074510b0920010803488048481038000d12460900d07504020541c1c060b080a2841440c0c504a0b000030884000c00082404030b9000388459898408144244090807556800c3e0309104403035414050624609150310352160320071130041020000342d980c082a10121207501000c905102d403141c00014041c00c01402c2004600c43d000302c1c00040c081d17102182130340034410480c1600d103903032580c01c40341420744a110814940000a6a0030b0001424440103043d8807140040001448500c01a110070200300d5024010780103a01c1000b03a00403070bd440d445 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 453110053 1250 453108803 453108823
    0x203070e09030d0f020d0c0203041403070e011a2506060512030f13030503070b1b0f070b04050f01020d14010f0e0c0c0309060d060311040903080112050102041205070503 74
    0x200448540350070040d640d900c0c07055424900407651039100003100b10343e040d01039800880030000c3c1444040f15081c0000d60300c0d000707449002441c5d005d440c00002c02c0d0a000c110b0000743d84010f02c24020503824501017101151028410000101e410820340039100544641203644000d5038510304009415420030200741c0c2c00ca074110612a0080c4d030b186122640c8000304803004007180c0d09045858401856000c00b41403030944c0098445d000000d211010092801d019a12986070030008050944014558000d240103c1c0a40a00444c082203203101289a003820154404d220308122050f040b81d402c5502d099802c004c040b492074039116a0f0382e800642c1150b100a014001d06007030708030140d11701a4200d043d41000b500b04c980070080024080c02d407034030074000c407440e0090103040550b80d0b5100a0b5020000e007900d10054403050041415000a40307885e0150f105410b4240d5200c100300c1c4d08020340d0b18044100000304552541d820440080e0070300082e035000034a1030103400540640e034900000e150900044003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 453111303 1250 453110053 453110069
    0xf02030c032a060c03181504050307050601080120070615030b0a0e010b06120712020403051c031404150e060a060501080c0c0607053907050301060b0904051b030702010207020307 78
    0x150421145006a0042e40e0f4420031b0540000340e550003c0361003d04220702850425001c0f0046030800c02401400001445a41e105900301c82e003a07a6243c958a080ba50083c0f010030100c01d07040054182c00d0740300f9001e010610300a40380025200001d112007070503180c440c0d1040340d04c01d2a01040004541142c0f04100307883e0341c1c0b24007c1c05644c040d8000a07010788240c149030402c90311240e0100716818401c800c900d14042001d030302150303a0703522400c2180e515011030540300d640100d40c0040002803880390040003001d201c4126200c407152200d68500c9000b03c0600300c8092541d641c0c50f480340b14a0410010240076030401440019428244000140220401400c040080c60100074076050310034002003a83d800001c92a016448148140c9810000304203980040e020503005080c1d44a2490403208000e0041ea4400c210360030140c0d03e105150030303a5064402c40d0000c0b002030025100b1030900340c011b45da1004105002c07408440000300700da00103400507a00d480050f075020641e803086080800100010340014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 453112553 1250 453111303 453111313
    0x3021b01090f060537091506080601050109031208071806050d110f070b04020d23071a0904050a14070206040308090a15020a030b03010c210b0904030f02030c032a 71
    0xd41c01d0030034000c190426101040601045000311817000d07401600d49990004d013402800b034800105c54040d116a005094160040600000d00c0c4d6000d0362030341040f00d03448102c040001e6445038050350300c0e12000b003104c801c0c0041e00d00001d412240c1c010924000e854681c2f90640c454101c80349140407200b00010050202a003040082c001c2c0304600b0a0754511a801218400103649510100300003c910520042c8041c5140703020403010205002d0480d40c203c4544115a4095a6030410303004000074205000030700c40c0c0400801c00c2504003900016441101a003010601d220555180d0345030f00811203109006070052001c1c001015888031a20b07800511035001000800c0003921180390140009202244071940050103c0015010ba00a601c2c0403000900822403201c840202410075080010100180d1174a0042108090712610030140c0004000c2d0003a0784564450340c00740e034000d12035174102c019848280409120000c0400041103184070641c00510440e40090440d442051202050006a000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 453113803 1250 453112553 453112591
    0x60305060f0607020d080d1415040b060a0c0302030f0c010b030f07080d1b021e010e010206040f0b060619090906060201180b06040b04060803130602070f0603021b01090f0605 76
    0x25400658861680480c0c0b8441950340300d01e041c986a100d880c007c00d84040c10942d0322000b20104c0c40c41184100303407103900d541540401504100c120b40c5540740043d07003c8000d110046965100e250703c40085442130044a280014070b40c1e0410064002444105583c0e44070400e5001604003032102c1c1410f6a003640c020071074242444245515030132904401d50800c030801d058110180c1103110005a031f6a00a40a20390515413468144450a4101201408209103804015441d4800039036548070b80d40048038038403a4000c540c0c581140f03010140400d50f01c8403040c40025143c61443c844031040c00000d0715905245481c0c04086001d8175001d500040c19a454192055072001c005080c01462642c03161201c2c00903910203002600428152039001c1d001440d0290200d11090008000d10700300303111480e0510341a9031210126501c0c030301c0d4018003014062031441000200c0c002e80140c2006400104030740a803080122019007115840d14040c0d41c0382c00301c10110001e110030352040c940c01c207115c107a4221540340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 453115053 1250 453113803 453113809
    0xb041104230616120906141603140a030902030d0903080d0504060e070b0403060f0e150a180302101a010c240908180306042d020a0906060305060f 64
    0x9505115400d0305a5001c010826681da0400300d03000002c40c8080c11100d50064100801c0704180d20310000085501168085900d82c02064610022031b50880410318002d40c0c140303400d5644600c950110144588020720024040010015202a401650380061461110300405240402014581c0180f00b0080b5040c00451840011110420041c0d80007103105d407128900100103000140c07071490b941c043c0c1b040c0801d07203c6580d8018012203000f00800d100e07c043d558400c9003210002c2481503507660000200c44004103034180c84643c4400c01942c00a0007401a00300800c070f2a042e2002100141c20009080d0a0920340d0300c900c4101c071809800c400b08050019001914034401a0405403288104035694405030f02c0940d05c00043c00c40001040c090b00c800e07440d110006400c08001c8001001000c01d00c41c1d240d081c0040c504e07215680001d00310000080d64075520107442d00150705500a01d10b01c9140c034000d07848020041c00205400e01000440500d810002001c40e83e000c1e182c94411001c2a000194a0b9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 453116303 1250 453115053 453115079
    0x1c020f120609040b0103020f011404060306141905090415020f041503060614070507080d0203070213020906090402030a090f110102100b03060408250320010c0c120507050f010b041104 80
    0x2071f0305a0300400049035000041c1e41c01205681c8061081d000050701182c5c00d030b0b150700710704202c0d241001140381c44032003441046841c03507820008000c000c070a410b00304207506d0a048180d4100b80100c1101d00e00348030400f8440c00381c0e80005c140a403a03d000140811500900900107101c400349454100714543c03c021004158000b000490483e0000c0402c0e148140710041c442d01e4010900d0100720f0b00d03141c48400000e92242c2001506130301c2042e4210303c050300828140201c0e05640c0c00100203918040114080000035040034144205a03503503400040002030b00710b043c240ca16801506802c18030506440020b207440e03101031100420604101d00b414241d1000a0541e400c0b542c07100081c0d40303405800c1c02068907030094135140c24102c04800207020505402124049000c5031280792004803141108181d07087e645c4400e0002d000409903d0003001040028054400110b00e03494014502425629080e1900c11803500d103044a955a46488030b6a1900c3d20070024102031112800c1d04140c40c064429100c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 453117553 1250 453116303 453116309
    0x21e0d060f02120a09051207080910260415140408070302190f020301060e010e04110303090a26010504120807030b06040e0906070e060d021c020f120609040b01 70
    0x2a54840103212490041c0c2d805031414030b00e4007a640981c0d842c04a0050000d0001d0110170794440c0a030340c0e4000131a1014a00711081250000c1c0840d21b0030519100384507002603040b40ca04108410107080c00d8010480d400341c118410f5201103182c40c141482d080c07030107583c600d49101c0000340c2c0c5000c1c3da02e40803c031003201c5240c0c815001303c051a03e55516040603400c0c40103e0841c4100b031103049480e4002c0004610407000714a000390000c01c801078450150103c0b450080c003814201801107400280000e4901400f08002680581074070306001e143e0010512801319500a08222101a254140b15262040390804000c44c00e500a00c201c9c105a29050100300007610b010341007100030000070301614001e82000403a25000780555984560795002c1d0341c0701c1c100541d4a200180509070116104521800103e5160b07103005015900e00a50f48a444c0300035401088403880e00500c515052514901d20310103040b0070407040144695500d01c803040a171100c280103091600c540100130520011400c100d40301415 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 453118803 1250 453117553 453117563
    0xd110c0d0c0503060c0301032108010b070201200d110106030c0608090a02030d050306040f0504080405040903090e01090603030906050a05030a0f090204051005032103070806060f0c0703021e0d 84
    0x62110316003820340800409401842c1c1500c0341c0b038284400008100d00a5040700d000301d640c0caa00091a1041040a10a1551450001c1c1c1e03942c006108440128006041d00f9205042c004030300e03103003202c41c210300c41815074141d01150400300d00301005e590403880442082c0111002040124110b6035100300095060140d01d080048100004003101c804104829003070ba0006c080390b101d00040307a0001c101da401220700034081c905114030b00f00300b0342c180d00803240140d502542032800d06081c601032000814102a0642c00c2240846000a1004903148281c0c00b8020600010405d075013581005441400c040d409482002010051030718055405000d0340d03005046084c0108452000303260306409441c4105020f58446d20f42010311452205110784802116010b07000d945140c1c0e490411955104800344220195800410008040038031031440d290344106d005004078144004031903161090b40000b03107002c2065203c0c060910a6207011031180200302d001441c0300340400c200b070f07010501005052400900c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 453120053 1250 453118803 453118819
    0xb0d140d030e150601110102030a0203060f06030f010b0f070605101d0c040311010903150e01050c040602280b0712050a180308060a1208071401020702240d0501170d110c 74
    0x80703168406c5078148402e500b110000d40d16170402000f00c2000754400d603203281c0302e0a08034007840b030701e030501c0c1081c2d0b440350b0056007141c551a844d1100380c203499800340405d00c01210040040d2400199644a95406000008810800039081c05100c0001c040300303070a582d8000800c03100b080341488240c4201c03426a9032080b42e80c640d400104005944000075038000401c900b0520130310b0000c0041c00e070b2046d40f8903020440244020744624924210a00c107a00894006030010150a10080d40380a00454188414201488051900d8842c5001110184c4c4c0000003e030040b03400c007801d00c005020b200c0e0407082802d010844080f41d00c800c04106805040020240702010b00010207603a100c01c54a80102440340905100401c249000740d80c82c6d1003410102d951240b400303c008400001482030302c817080d5000d000c2c002d2018600d9580000d43c034000003100305207141000540100000c2e13028680c0240030000f6400d410008c5500585e0911200340d09060412001e40640b40e40f108001a2401c0c40c1041582c1c420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 453121303 1250 453120053 453120061
    0x3010b0f0d12021509061005010f0c0809030312091501080d0806010809101e050a0213171227010e060d0f020912060708011e090c02010b0d140d030e15 66
    0x282c00c00c958007803852209044c000800a64120100d1141d100340850040700640030b40700e2005459950380300a00718002082111728400140d0b850b0001d1001001c0141200c0c10509842c426815230082104c1c01e850b95081818109070141380040c3c4540500002700140100d9103407000001c0c10710788000e0003203040007071403800315541807400e0001181807481e101c02400450394001c107002e00c2510074440d208100d8500320000311401c01e50310a0700e010f1544079914008051800c0e81525541441610b4900c9a01520341e44071601031280000b00000300f0007141042c513400034468649882c03440c5040c1c1c5070500c403080c00c011030213984000880c0c020003000c11f0300240e14020420020024000c80210030340002e0b005003c1a41c20714002000c903c250141d95460119a0700e13030701c0600c004420036401107500440e802060012440581001d076140106100006e440303007050000a03060701142070700340e800400380304103600540000c0c00034400d0000c5a080920610f0000e0003041e603100225804000b00882d100041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 453122553 1250 453121303 453121307
    0x9011e02030a2105040b091e060c07020102070f06031e0c0e01030e010e0601030501020c0717030403150f1e11070804031205070f0503091906080a0504060b03031803010b0f0d12 77
    0xf4903481ca0701a60100118545450302d03044090003601d02d14203a100b010310103040c010049000d9507680c8110300152049480b004203124603038020000490550145440100325120b084001c90000e00e29a600841d607554020f5180c0941080a47c2c0c0c035606508000000503443c0e00b0000e030080c20402813030006500360481e80d405005148001209580e0301584000006028054000d860f01400e504140c1d26050b940d6400c42501d0700f0105030110300c942040c00b0030004a9401c09898482d000180c02c0400c0400318450007204982d1040e11043d081c0b41803610380d00ca1601c40d4400c0c02d41d0a81c0d021206031500c0b1a940300c04100c4d010718840181000018004a4101032292003902c0601340d01940304017103984030340380c81c580f41d420242e07004e4041c114002e004d40140d41000d018200b100c0d100e403180310740c0f911110028009014001c2050b2451600c40c5105072294508000034203c040c0203820115035000d1250405081d200106039131807142c603540d00104401d95035500d06d2100d20303500028440ea42c051746102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 453123803 1250 453122553 453122597
    0x120206090f1c030c02040f0501180504030e10170c0a090509061305130308090c0105040303050a11100b0906040509030301050105180310061401110316020a09020a0509011e02030a 78
    0x12181481400c000b01d003c15411060050215108880600c400304059440348101d802c24815071500b83d041c040d402c602c1e80b20b1940855005070003841d1600d100c101d1000801c04545d82c40524500290b5500c00c4c981c500d0304e280ca00d6070340108040c0341d01c500d08403285100620200ba035020f02c51256010300003140c010342d00d9030808185420705410a000d14940082c018002150010098001c1fa040d040000e082110208990941c0e4005860311030500d030964034110759a80002817001c043c01031940000341e003d1010454210303012005100858110302050503c0076003034000d480b00d80294201418032a411001000384c0b81900c50030300c0c0c50341c0c8540c00d004e082036244003910941a014000c1c0045204269100e400104c05c1d40c05d1003035024081c0c0c83d45001118503880795410030250340c000b40100004504140d05a590341c5000401282d202a1103000c0c69049a01403803c40000c10720018509a003960401e03103000d04501103c641c1440003c036614065240c1c412810300c482000390400c0600340c024242c0f41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 453125053 1250 453123803 453123829
    0x20c07050a0e01030b0709061b020d0b090102031503060921070b0f010608070e010c120c0203011506080601090e01060507030c06290307050d080a020f030c0601050a120206090f 77
    0x460021655a11805282c41d00e00078002a518241400001820079020342c4c86001203030040d60303480c41045040040d803080d810001004aa00000c0300b1105c901141030500814060103006c0001656428440e41c00d00c1402500d1405600a0f0080f40401c00310100c041045400c401050429a041d04840c0e40c1d088105d100700c81005111085c18801c1c890030040d41900b01c3d059800503203840141d912403550540d844d4120b241041d00040744c0341c8840c4001502d00c0710b44c3d0b03031840b02070502c1c54030b0042680c0004c1c04d50712020803402c0c5884549030304210065201603001c2d003000e400e081c00d084090410326107400b5480b05004a4050110018400042500c2013050703082080c0c002c40204500107070b07000300150140340c030300342c0d408001c0c03252242d5006854046000c3d8229440140455107d00a50b40c4c0c21105400685244056005075000a04050320520003804a110410003402040d070419081100c8010755400c8890002030185134000141c45807012502c102d0404c40c0d0110143d400383c0001043c802e4035003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 453126303 1250 453125053 453125059
    0x8070e06160809120c04050615031b1c09110906030a0803060d1e0203120c0705011d06040303020718050c16050f030f0d0509060402030601030209070e15040302100206010e0703020c0705 81
    0x6803500e0100240454241e29410040304d080c1f1064032920104010815000b80403003a0742c80c100081003403042001c05000c401e04005186ca4103009014442854010842d94200072030307038807980e801c01000b0070140d0143e4200c10480d4141d88a050620102c0d07902c07241580b008060103000404a80d85503a03804581070050343c080821100c9a011300c0300d41341d100340752001c00c0740248115115902080c0d849000d542c0d081405e540280b4101c0e140600442c0c100140a44c2ca00c510076070f440000710b2a48640000b00080c40c001d800604200d454101443c42d1130032a1480d58091502d03180c28440140e07010400c440745104400001d0440035120704000d410403d6242c903030034962000141c102d0a0041d03110191016820b03501d010006640c5140400e41c40b044103c0d80203600d90000c0b00180014945440c1d00d41c0c0008462503c5d0b455001e1a401003090f14010303180602d20b0100204d030400442c90325110001c142d19161000d000e19526000c55090342d40c001810701c0003859008070f00040010380810444009003401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 453127553 1250 453126303 453126319
    0x17070309050a14062505091302130f08030a1715040c08060f0607050d050a1202040305010b0405090102070b0118150902030414030705030a0e0d0515060108070e06160809 74
    0x1520f401c00c00250850030040c610700451002030403441100150001e102c010046108245000c0d004c00c0f07403107900544042d1351011125250040c010701d50700c00303403000c030000c032240c29400c1d4206060700c08000c0441d449080b8a07401085100992a4008460700781030103014180d90070b940710b0070307400880701c0e422420702a00f15140c04150b034002903000012030b010b074005988110441d0121414000c1d18402d40001400d581d100c0d00600c180203105900a00782000c480c540041000e90003100d41c400c3e640a83d1050b61103a4440041c84441e1900707105030743d00300035004000c62a2040707035030710072401900520800710390184103010442d40c110305400070a070103480c010f413052a003511071518100070b420585054505006800d612070101500100300c0e10842d0700700c0011800c12000d02da080314120100c1c400d291304280c28a614400140741003040f04048ac42060703040400f481c103000018061500102280200b181086a90490f604c0b098111100079182c42c4040840b4034081c24204807611802490b1074000b03400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 453128803 1250 453127553 453127573
    0x30909051f0b040605120907030c0f151728020408060f0106050c031821100e03091c021f08040605010e24040e06010609031103010c1707030905 63
    0x21401c0d000703001d510600751009000c0d10b60581400c18081c5010b01d40c08500200218444040c5403040940c0c000f040d18200c60145850342c0d00c00300c0d044a61350000c4119060051f09100811501305e6113807468480c0e242c0f000059003203645030040b03440b0142160940503034680307904101c8140da0754000b0303071154482c5003903660f1a40d821085a6501c0f003220168007100700000049140c0f4403843c1200c03601c2d43c2040045060440f2948025103d8901054455025440c3c0015040381c0c1030303003080181240e0707100c400351500c44060454035090b2040000d44484c1a002041550607985c4c0700c4e0080507181c4070b40100c048007602e10b031001c241c942146000c00300e030039058800e482000780d038800c4c0c4c03042c426449400107102e142d99440b040c203600d60301940e0322541c06410011905861440700f00b400d8490400034004103030300385982c0000381000300130303002031000400e0142d0a2080c4a02c075029035003002029030003080182d0400d0002454990210a14a1840f4201c1c000c91000c1c1d200741c110304165608801a1118106 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 453130053 1250 453128803 453128821
    0xc07050a12030212071101081302090c0c060702010c021c12060e011e06090506160b09240f060103200d050601090e04030c0206030a3e040308070f03090905 68
    0xc0c1450110010702c225088095540f011130242c8525a500452031404040c003d00103480c5107000600f101c1c041e100c50031485016a403485c0515004a4007840650303900d4002100142c20003100031710000541e81031050024180c2d500207844648000450036600840c00e03050800c4401007860003195816600303013400031502d4200804003904880a1440c04a0008000754480856101c2071080f400890f41000b810061800d10500810f83c1180c09202408004242e583d0607071a04025039020710182c2c456016103c5883e2981520311841990798001440c030314001c20101150700b0000c1080c0e04050300c811039210020b00d0524540d0f14a5144400030f510351007807101603801003c0c101c802c0f9000458030000019180e9035141d07814000c07a0503036600d003441017031b0740c0034803025610241070340e4910355640000d407040040d41800305a21628844070342081004162503080701941e1074031710782519602007000700005101c0c203088648865101855500d0040a0b00b8151600e103019400888a00d0400c81000352002d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 453131303 1250 453130053 453130079
    0x327020d1b0846030e060705031308100e070b0d06050a0608060a0e160c020a080d020a020414060109031e08041206470a0602030703030f0513080c07050a 67
    0x303494400d060f003403000f4010070440d00c0040d010408041ca400324414401291145000301e41c081000362805151000035a601440d542c0403114411504001c80014446210284050080b4800044041c400d030b4500b201141d894220a1290300a0302000203a00126020700e604054001c00d070051040000c16690364020700041400c0b00c60500c92650803a01040c01805520503602130b20005011000070501ea881c25a402c4910250999000100500001d06030a04000c400103c15095010f407410b0308142c03041c0300965900c810170b03c40010b072110030080d00c0d99100e51500b045903000b00b1121a44070047d4200169030700541005456050002004190824044072602e185031145100300b00840c0c030311798041c654a4a0040d12000010f51791428035140c2d50031030140c03420b90003100b04150101ca000300019100706e40b0364041c9016800c0400c190703040c550184104102610742c03903802e00c01480c0c50111102800b070b4a8200400521021514002c102c501700070050151030060444010140c03181c01e048249 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 453132553 1250 453131303 453131353
    0x10e03070806190f020403110d020d06110a021e060c031306051003030f030506090c130e09061608160c05010e01111b0304120f02130c0327020d1b08 65
    0x528240021a06a12402d00c06c5508a0703070840520006803810904000003205e8040c404d030703402031005000d5400f1803998800d00301e150300c031307984202d0b0396104459002c1d040100d481c26041259501c0d00c504071101c20f010a1050307000101007521607580c0d403072080c482c141c03d03d0840701a041c10300e0081082258804040c5802c03d60b0b009440b400206e48540c034003142a603404688041d0802c182d81d0105203003030600800b91608c9450012000b00c1141c031442c00c00b10101c001c03201995154803a45c06d00c849081c801c01e03207169502503031405448514012118205040101c0c01080030010f1411010041c460290f110742d880030014070082c41440e840324000300c0180c02040e07200d10340240800c0e909150300780c004119011500c26101f10704080d45079440b102c01d50020510300341c1e000515100400c2c0070200b90710601e499095141c400107810340c5401140c20b441100980d059141c03281c0182603201503030300e292741c80d1240c943c4061241200b010361108529a80d446134041070301132142e02000300317201d9000d01001c000c2d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 453133803 1250 453132553 453132601
    0x2031e1b04080706081602070e090c04150e2413021b250e0a020c030403080d24030b16140c010f0513080a050a050906031906081b010e03070806 63
    0x41d541b40c1444001b0503940e441026000360340042010041a03501001403a0b00840000503200072110300d10208040d81d03000ea00180030340203195418092814004443d0b90040c480382080c012403000400b0703284442c50301001860bca14035188924107410a250100d800c2e841043d4080200d1a403680315056550f50001035040181e80c480d03080003090811080010101c4112850f4203182c0d481d8004101c000b5801105c0100c00340c0010400440400e0402004010080542c48000703411300d1780010a200300b00150aa1160700c50101c1d20420210744210b078403503000108901102a0350150003015a00e80c201030800f290685004111030746614019441685401715195080c401e81e03880c00748200100e94110f40003040040d050bc0000d250620981c081d1032280c0082c01c2103031400c88500e00080064004841d040b0003141e04403444107030380c0f0041c002d980041180300004d08000c0f1a1307821002c108400c44901a04020300c54403c214256810030840d002031295900b907400e1418035140c02801c200c85007000e118 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 453135053 1250 453133803 453133817
    0x7141008040f14100e06060a06051308120705120a05030a0b120d0e0a08120f0307030e03041212090f050f010e09040f0b070203040f0e0903070507080705011202031e1b04080706 77
    0x80c10007103501b6201d6900245504000d904040b001e1741c0c250001c500b54095000c880780302041c800010000c0d0200401d94248403500d41c4803624105241494000e003690020b02c007401184031168104007580d400040090700401e00c581d506002c902462003485030022b040c421520030390300c0181c1102d00b509049106827001412180c40d5034145a84103d0040c0c2c0a80000c02000039032149820070b809140c100d50107203008582c544241e6000d524540050300031110074184006400c00700800788141204401950174100f03c500c0c64015070180301c040e10301c680d43c000e002140845000e6032003661890301059008003201c105080a050250aa0b1314004046619560300ca001c52600c0d40000103940440e110824010001420643d000c025681d003e80146040e03c010310600c5c001a00c24415440540300c05401040b40b1031401000401c1181c19002c070b80d44123441002444540112560122910466031410790403a450300c000c901d8105140072814402d942010402090000c2c0115a8030112590307651419 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 453136303 1250 453135053 453135071
    0x90506160221130f0e150307090603300c0602090d020411070204200904090c0e0f100f1211210115170c0d0206090a061107141008040f1410 61
    0x3c000211140985041514100001045001140c1410106c1d50018040d110300550750b01c283d206072280390b0411a448100800c01c000203d20707000341c2c01f9020510070303078020070008103210103884c3c4240958064410b83c0c00084042540d03c80541e2400c01341d07406001040180b16001090f0310307a17005600c00300d100710304221410b4011402900b080d40f4151040e0482c9240000c0700341004024010300500309e0b400b00361040700203000c0740202a40c03840f400b000c040110280c942242040c460131a0760300100c2400005080501040b0030381c50310284a180c1c400302080d200e1a0840006500031001c0040750300c0d8044046000100c1b50042d0442d55000c04c0e24000b12418a8a41e00c1040751420003502d4114039601000405800e07240c82c86030300c601a400130b0401450400908007080b9080306607041007010400c1c80d0b000000540d42002004028120100a0805544d0000016051a01000280080103442c2020405010180844441040c0c3c004545040d41e680c0c141c4150300e1300d0316801c494041c985004068 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 453137553 1250 453136303 453136319
    0x109060e06040209010608090111070f020a091107031404051c03170f28020f0705070b0a0507030f050f071103300f0f070b01031509050616022113 64
    0x450045034000c0414903d17a09024040710003840042c000e08540d03490350703050b5485909141c000e201c80c900401c660320890740580148082d04140da44640643d40c60040b9100c0d200300d006041d40d6419a0510300050098043d0108041a0180b82c100d90b500c00382201585801405c466014644030307219885d203080b4214402a20024010b003114407090030000e2000140520030f42082080f18944070000e4002103022a12000307049802500855125100004004003881010824000100b001c0d00d0a80d01e040c44104004202d405888002424032400c00315144405001d602910b90740c0e401791391415100c444a05090001940054010f03019004410344510021501900440c59004a80c00784252052109641040b030b0701c03107a441c6070110428000c2a1842c20769000910740740d401281a004e05505608200c24000d00700c20758070300c07842e00d00900c280016001050b4664010310340c11b402c14225003442d0060f81400d4896140c0b5828016500000c8106032000021344504c40b08940c011903000e45034014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 453138803 1250 453137553 453137563
    0x80615060307030c0c0b0f0603010e0c15030618090307060b1914060403020a0e0703061d0406051e070306080c060f0403060506060415121b0e01230c0109060e 69
    0x81190494020030000e51203601a400c8407000c940740d4900000c801c080c41d269500c085609559242001c02c510341842403502c5d0034000d58501d0a109005020414100da00280e8014216030b690744910401000251055076500a20174105088003c07110032803403d4000c1035243d60000c030003110403518015810810b402c0c003640c841e10301c003001300342d4030a0b290801c204400c5000301d208000e03034800d10801c408401a111b901d03c0c00010854005110b9030307820510301c0942038868076004201202e0180d030f8008c00d1101c2c2a0303100c0342c02940062000455488002100c41b011401d00500007041c04008180a11280c0c942d224a0440b400380c0182c80c20411810100003952040b0b00c0c6024100c103045c0701c01d0000c140b4947c0001d8001400814051601c1e0366252219203445c5407004003808112540782005641146000d0351007072040302c1058501e8070341003800c090a00c0000405440c10400300c1c001c0c51603e812031240c21711041c80d038075107926250290300911a001e05031306413080310b0840c01c146d060301d886000092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 453140053 1250 453138803 453138841
    0x30a0b03010e060405061f0b0304030c240b0a090902010c08070201020703080a080601030e121e07060e06011505130b0307021203160e1008070c0f0c090b0f090103020f01051c0e03040806 81
    0x23113400d2540e110764a0807580051b080c1d5054441d11100b8904101051138a4038015400f0200716000c940da0200004100c01d1503090790000140702d04010035000140e034443da80c1481d5950001002d5201c807035900040307103080030315000200301880018062500d2600040711520689090741c05020081801881581324078141c504106414000d02c010000600c40c1c280b0b56050389040f8500034204032a5884041c02d0741c4a80342d00f420303150082d8005108800980031451a02e039001d05200345428100c803040b40010740540b14910306a44d021001ca03850074824014056410400300c03841d0740342c3c02c101441d113102044000e44840400c1d00090061030a04044920340d2080d644d40d1100d6000e40d50f407082c02ea82841052a08441001c480042c03600011424045034000c1c0c118810300040504c0d0b040144210041d11400c038a105009650040005a0300d100b130019102200303181103520741c3c1481c5050080c410282400741d803240c0c28007000c032810071310001c040c0084401e09000c541d40b9884144190b01c400310000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 453141303 1250 453140053 453140069
    0xf2701020721170d0e06130f02061606090506011d1e060307120305090906011b15110d09030206130314160602030907030309150203030a0b03010e060405061f 69
    0x1201c00c180c000c07004105641800e0050070f0070b940581c0142c000c002564400218070385001c1e907940e880c2d1100c0004001c0c07954040440841c10390440040d4544901e1981c1d08a0000d100b20000900b0031780800704075012421350b0f603105e5018861b10440b882c0054a80c1824003465140400c40c0703c21400c000000381c06075001d0314405a594040010760706100d409160001c202541622075040c00054611441155072511802942c90549512401c420003030101c03400341c0103d04200d249800f0814201010003242c440f558440405400c501080031440050441ea01040c007040c1c43c0401d00b8082c44046800405040e0712070b50940703801ea80e901114501043c01008042d00041041c400141c1c0c88000000034000e8454140711440e07400440c6d40d420301603071b108981818164100340420410903070440100c8005d45a100e1000d803541d200c001c002035807800020615540142c0f100046102602e00794450701004800000b914a80d1405080c0141e4840b01a211001201914641411720b06550f10085c03090712814 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 453142553 1250 453141303 453141329
    0x11010318020a03060e0c15131d1906090903030f0b0a12060222030303090203060c0408190f0807120806090606040e07030b031902180709060c05030f27010207 69
    0x5a182c0500031306420f2031900c4181b08511400740300341c0c0d0b054600306000680e030a0507952501c10002000142005900129824142428440000c4500c2c1c00b0b080c1e10103c45c0d290510684006080d80000c1c002c203900c43c004240c5480400024194540c1100c084400006011b01140c07411109100c4102010320818202c010b164401c00c0003d6030b950000d00d0101c1060000082012a41039001c0b0400516031044000c02c2d503440320241107003428410554060310160750b03582414030f041460340c0c0300c0071048035080310706d1842e000310400c0161080032844d0203500507900355142c03172a41c50b1141070025080d0136040425050400180b4524055034864884c00d0090803c1e400d00713190100400d40d0a40c0a895070003410340305c000c01515910104481c88141c0d0301c045208045100714014004520b40000380ca241c00c0d64014100104103030428202c008072000c42c60110031815003407c105045000c0e0402c0000040301c00074402c2800304c0000062442400c50540c0d10f410311070468010b82e40c48801d442850341407904 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 453143803 1250 453142553 453142559
    0xf040206040326120603100504030e0d02010c0503040905100b04120f060e0d0503160504050a0b0307050c1203040c082e1103010305030a090501020a0f0b19020711010318020a 76
    0x204a510480c1910302d03a0a040400700d0003404946411404d801c0300e00384001410440076140400010307842c014114020000f81c18a510028220611100c565000711011044e0341c0459214500d01c49070b054004041d80d0b1910344a05d0007001a09082e42c4190101d05030300d030013081c0700740780354100e40440e0044e58149002d40102c2c1e82d64488102c0c184070075901643e462900350409081400146d01c004e0b40d0b0b948250313a82c58692a0310f448174100c0c000a10412205000c14032103521455200c90540b2180042c3c181c482c2d803880c40440e82441000c2e6141510701680d103107600c515900d4005140901e106210241c0c1450301c0d485134640e201c640c54680c0b1071401a06984088901105000b180340e0410030001150b100241443c16507103510a900440c1d599200086420001e640903406401801091001d00515a00368680c3c41514a40c000041c0c0000b80c6071000c0703130b001603480080c12101c480c170b1038042d034441075982010861124040441800f107410308604100c0400c2c91486102443e60040c00d200480d41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 453145053 1250 453143803 453143813
    0x105060111030a030c1b050607020d1b1511070f110d08120601110d0c11040203040803040602030603030904062c01180e030d02030c07050f030a1e0c0b1006080f0402060403 75
    0x12082401c007030182000c002046c0400c024032110600c0d0060008001c28248a440240b624802d03100b21010004c1f5002c0481101e807180c2030b0b03801441c1d0000118031003400940143c82c01400b6049964840443c000380050170003103690040f03c03809010700804068160700306c1c02c2c087c00c070140f03070340c002c0c040c10f400c01040492802c54200f103038004c5418941105010007214a951070304003240301c04000b103064007002e03004012200c01d08501c20b142c02d850940c00d6080640e80ca0303140d4003024100804454020000580740e840c204299032900400032300a010803991030040d1040304003d4000d070740703545000c001001e059602514030355040300d1103a8046000a403007595070304002c24040015400c1d500081250382d540070442d00143d0b01401e160b441c0e007983c40083d864070a01d4102c486038001407540050100180309900300c1c103070256403001320084502c8002d25400c126141840c04030000c1a40c2007030700c1403204205412100600366425030711080481e0712071000040040b481160b0003540280204800c2c00062 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 453146303 1250 453145053 453145061
    0x60903090f01031503200f0625030e060d05150a061b0503040306050a0209010912020d14010e06070203091e2115041208060409172b0b030105060111030a03 68
    0x9088403040414030307130302c0341c1c0c5a101b41001c0300449120385003459041803840c40c1c0461910064030044901515100c08400050704500c0100c0c0c100004405800590003458050180280100d10080c499580c414180e11a80018001541c19082d840d103181c00141c81410680190004c0d1030702074465080e501c00d0ac0502d240c1c90070314214201d486000500001001a000303000c1d01d405a02d01100251f21240703d24001440321040d68880c95041da815140c01026807605510382c200c0c150002c0d06c4107000c1c00030744001800741c4a4038440210743e110323100810043d903034044040d2110b0102194036000a076040c1600d45031040200541c5540100d01c90743d8485080017496203400b0704225902a5540000d40703104a5408400c01c6030141e92849551410b106455480729020b0390050040302d081040c6030080c3c451190420360704001900300c0750b000481000c401c5146408810000c052182c2c11005035048007820050700b2180222030180d82000c000c2503581d802028070714038881002000354245844080114060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 453147553 1250 453146303 453146321
    0xa020318010905060105090906011805060a1e051c0c170c1012110301060f21061d0c03040b0408070c0f061e030203060303040504050c0d0617060903090f0103 69
    0x6010344039034800030020700448280e14020f001a0040d0341c5000280010b07100002c00164090304814018401c00707190201c2e2122400c0400c00019282e52000003084168980c3d42000d20b400b0846404044d0885414840d4420b803281a0f40c0d10f4244036038506822540501b644004142000600c011b0000d04040395149859000040c200c45c0006086000300348244ad4034082c8500050344185400c0074403405010380308001d80111402d81c515031411400500b203140c0743c41c0400030041040040210380e401c1c009011440c203403010302046140d540307080031f081c440500021021006040c1c0000744440e82d200d010740f40b1541d00a400170402d50744aa50780c228543c8000001c0701e000c04800c2012601004090540010341a240c5400c40d40f111960141c00e0f0000440c0c5840701058010810082641c070003000790b030100c80c1c0a4901103030640343d10014110038003034402c0f0510344500e0b1940016980c000292082080d400b884281d0305d030307a1260084a5101d01c26035402c80e030800d0700c8070500c098952007580b000c0e0b48 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 453148803 1250 453147553 453147571
    0x90a1b110a0b0a02221e0312050918070908011103010609050108090114040303020a18030201051b07080d02030a0f0810120201020f1e0d05030118050c04030611040f17060a0203 77
    0x180a602881d040c0d0850841c945c5019030518101c014000301c0f42c0c01400d446e41c032400048441d0040d145039146940c13038030010b110404011000c50701c55025100c0c003046101d9808401c500d0384075440e00d0000108156598440c00c008c640c01d007205003082400040807603040e00c4d41c4e9032b240b0980c0c2e400d000c0192040036029090000307641d44d4040c04207032442d099100c507009a21079034001d81d030f400c00c41000070101014030769010409014130b5001c000603a00001166600c01c086800c4003031844641c2441800e01200380d00c541080c3c0101c500003010300740e0100061000040ca500c400036000e41c3c481d000c1302d46917811545844404400c0c2424800d10400748004c003400b507c14070403590030445000755a0705194070480b07803500d091210789183d04d403a10180314181441c0c1e000d00c1e00c9400c5626103c113114810401a03091103520350f958001c20b100800140032980a90b400c0001448003c3c030b144440380c07095029200d00800d154414a022505005c1048600b804200ca00c0003005151600c0c85100300951014101c005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 453150053 1250 453148803 453148807
    0x110306042a020307030e091e10080a0809040c0f09060e040e15191404140a080304080703020c0604030812190609060302040b030f030703110a02090a1b110a0b0a02 71
    0xc2080d070750821100102640e68043c5455403290328000c1c00100c0c0184d80345104400140811441c40707114003880c00000700c004034060b82e41d2181105420040a142c001507018018460004c4c00e00035540c0050101180c02d0b01c1c100030030702080c03404813510307803010032203d0009078546001c00001c1d06c201042a41804014000280d4820078000586450448030800e00300181d03000400240c82c03440c29105201c150882ca00f400440e00541010b0080140144018140034104c078049101182c00c10030720580701d83c4003401607528103141c10180362503046080d040307005125143c04200641404410f94044990104105091070203116003800d04120041c6815202810494003080080c0103000300c3c0c00130900280001250f0b4111700622082d16400031196010f40d2041003c400182c000104075030407107415142000ca441c3e21b001d4600d00700300c98502c1c0a54801000b8050282c3c0c0e41060740a6000303a008a0b00c00c601c415102442511907045805840e10f40741c001032640c0700402c590b800c00036032003520000014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 453151303 1250 453150053 453150101
    0x522020d1407090204090f241e090501030b040c05040c050403150b2206050609010c0b0403050c030a0e190509070f0c06060306021917131407080d090911030604 70
    0x140480e040b55009144240d100c8044280c451003030f2007403d0021510031022844401c3c8031a40c0d40f820307990740c45560702801450f074003003039106011409c0c20301505145071b05020950752803c00007038611b0150740a0b20040703084c2e80000340b2403031300d031090319660611070b15501d0a081c615112100402d0200e0b0310180026143c0515203410b952b00d071200008120070b000441c1c0915409515076084070b00f250011400760388100503400c0d4980c1c101104c0c1e100c041c5d20861324041e03603903285006c4a00d170185c0558078409110105240c0b0109070003081000038540141c81c01c4484030920160100e0180540c0715440d00a031400001c907100c2440f503080d0507414401d604080320503c1340c1d55111022200c1640c004d4134103660104158842d1015103d8401700403c03646013400c4410b105000f4403c408034060601110b00d01c0002c3d403001008410517041c1c0042198038107a030181c564551045490354203170140c4500043c0e0204000c55001c220788942d50030000c0c240d200c0c506598465041c003005121011002800a003840b52503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 453152553 1250 453151303 453151319
    0x1b1b07030c08010c03050903040902130e010f090c020307030f030b010917010f06080313140d0b10080105060d0c0302190b0708090109120b0a0504030e030f010522020d1407 75
    0x5580150300c100c07000418945031600440c00c4400340c2018004140c284030a02c40050300000075901640c0101d000160f69050158a0701602001540400d01d1150b0700400002e03088401d8130010202c8183c0c08003400990349010301207840740b040c180001c0c040781a400c0400582131190f032008205820604042761810340700c0001054070506080c1540c4585e4540104107600c880c00d001d0040185005030083d03003800c046807075000344065140280d1401300c0a41400182035036652448641c05608402207c40078145005203400104a50042d03504a6092a0200c0e49600300f07584080085038001c641c540c2028155801c0201c80303d0f51405e81c105404c0013040c00715071000d202c002001814441d4006e10f55a121010005d00b041c2c0581d442143d000c40d000a5841c003181c5420003c40e0b009014210015242d550740c642070b100000070804d5980c042c429801d40e0785856505621a80c010817000141440394143c01c0b030512042c1c110004000d4000c000d10201d000001c178010354070481640001c084d20346058580082c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 453153803 1250 453152553 453152563
    0x4020f0406140a080105040203030d0507120606051306090b09061305060c07060f080c030103080c07150201020403061409030a12020918040b0907030c061404080d03020405090c031b1b 80
    0x101c2d80c084010000e501c81c1d40c1c80c150700f120b401021110002e1000b4506030b00041d840f07003c0c80310040310407500c80b400112160300c80d864104070703226000010442c803070f10368100500b079400441908101201c01300011a40701c0c0580c0300201210421200149050041c00c1440041d80103591169000c1c0c9074120b002c29a0740d540030242401803100c000030070591f45000d80050460540740350f10001c0c13020140c103216414100e80f044034107503908196070301c1d61170101e8519503141235080d03480b403074aa0414a843c00c1209506400070000c49010301418404424821205502d0a40039140c491080e4010451108078034002e0304d100c031903012007490042c10034019101181092200303603810000e04400200b040100f1010100701031b0450303100703c018100141155914000c403034641c0240418040c0044240c5072982c600340c2150080d080c00e01c1074650301809014068043d4006d4041c0718810704d226000540c55201070070030b81e0b10031041c0e0408100381c0754800c0c03c603054642c4013114600080c502d200311040140c1d41000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 453155053 1250 453153803 453153809
    0x60903030b03060a0c1421041202011d0715050d060f211220070807090501151710150e1e090115090f0e0402010e0604051804020f0406 59
    0xc0224541c10600101410b100e40140030039007241c9020016800d1070303401902c40c84030058440605561303030f03151482254803103d491007081419400342c042004001c1d41d4456000c070300c641c6400034044600e007448000780254043d44100007551010008004420078208030350401503050030802d18082d008034400003a2000340c0c1091241401d056020010807202c99048149621981200a1003401d180e403400e10000034505030204000c1600c20010070320010003440c0c10303002039420071112910390710404180c4404061084a5485207408000200300d030561003440ca07618059510300341070380b000f0000c281d0b420300b020701800d01c40c00c03000740c3c0402c4442510030258407403181c68a40c14051030842d4104680d10810517403030b0703403480c3c0c02100c16080c0b138a403000441d06542982480300d140c3c424902c0100c0d1899410b0b402088a880b003c85c002950090b0591702a004034000c0c0d0350519030561400610513039204034801c0c0c40e04003000781e0391841c0940c0f003030070004d402a100804041d41419140d00107819110550 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 453156303 1250 453155053 453155057
    0x1005120a0c09050109050607140c060703080915160809010f020a0315050f0607080706152903070e060d09080c0c011b020a05060a020115060503010509070212030c16060903 75
    0x28166007240d000b9080d14000d00c1c003407170910000d50400000c900940607038040100600d01503c140e159401060100040408000d0111621780f800c500b07009101c1681945c81041601a40036840c002c06140c81819100b00c03032030600052445829a02101c042000034001d282e15541e50310300e01c420300c0041c002006807100f80d0340d000c2455031308648800ea00d44055800a0321035400c0000003805c5440700c0e001d441d02c25411440b480d40700d0882d4182400500b07c26101d144005894180110b00c014482d19509207091001c0300d0040c0718230401c1c401c1c04051100f540d0400202d1041d1a40b0102407414000900c40d00d040610007040d10885a0303900001d907081001260b072542c20000800b442940e00c82c0c13154242c0455074030380c1c3c00f9018194004c00e1246c06103026090042c0301c0020741402c0c29000b50019400807440807525003c159407108000c0c40c0390400e0040511480c0d007400410012803001403590718602080c4034981c80d585130000c0d01c400e5075010640c101d807241d10386002100410301622604500398040d1f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 453157553 1250 453156303 453156311
    0x160516120b0702010b01090b070f020616050d020a0812150301060e010503012a030510120b04061b090605130305070b071b030309030605060a0b160201022a1005120a 72
    0x518141e100041c0c001d014208580c540480c540d8a80c1e8400005002c030f410051895640d0412400d290603412000d94010b508031000148080989280b01003504025001e04281d03413354904180482c0c40d0b070070030500030f1b01c4074000b400826017a01d54003008942200003000c0d1051703101003460110f800e65000d5400681450145c50041200d42420301400b00d11f51300d2403803000c848108040304075000380c072140c2402c000c00d40d4a200240a144d0a99030348409801c82c03d205042010061803e0241014101c0e012581c0c1414544104010500ba00c881c8810008589610142c682010030071261038000d12031005415030a890000007280043c000c0324050040034058030b9540541d42818503031b00580030130782a81d0050035402040070950141c4420140c81c1c0c000d1000c02e858494800090b552003413604405140180042c10300f8410300701c0b82c07240044c141300380c00b80d88022089800c0d182d03c082c0307040c0c000c1a06500d6040000400e241402600141c0041ca0030014202031810605820100c800c5450007841552 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 453158803 1250 453157553 453157589
    0xd020c010e0127051b01200d0216150c051e0a050c10051801031e0203060f03060c04060c080403051213141c02040905030a091e050105160516 62
    0x24002650701020035101d8002d0b0720f6982592000c1c0e03100c800a1301503105020081800540368890b040f83d1042017145010340e500c4000041e01c030354a074050440d407207026218240752180e4004403001c80d41704490070703030200885040d00700302c041e00c41001c0d82402726a24051480c0100a40440042420400c0c581e000208000749161415030715103031000c1c4100344103454205901ca4100d40c41001c40d03100e00c41ca149170f0088102c1080043c2c018092034072810300d04841180d1016014901c0d580551300c070700c401b00c44803010300f50624240768035684140caa0041100f030800c010300c24580641001c2c03c0742c03482850145d18040c0e59440716801d20a20a00c810030944000507400c1c14200c0030204130000d400300d1411003610300071200015694003c0140d503c92708180c007890308020341d40c49502c2036080c160000305580d0f03038140103600145812114024000030031424030010285281e1000d0303081c1a9903041e1a410b2508145585c0090f0120112078201c682d84030742c80345980c42056003d03203100100b0902448541c0441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 453160053 1250 453158803 453158831
    0x30a0905120331051b041a010813020111070e06010f0201050907150c06060608061e0a0506130b28020a0f061a090c0c011103040b04080d020c010e01 65
    0x2078000c0d200001040c061050150703201609620031140c440d4582d04001020549040e51010f0341d007050043d1003800786002920700c005084d10342d42c00c8080c0c102c0e400c00a800d0442d01021a18100e40b04a03400118904001400c1d6485017403046e11071070050400c600300c2d03445003050b1407400d0709a8201f2481d020064050003480e5801800c159140c48290000303004502d45000001d9541040303121f1902070302950141005018000c1d5002c1d80c0154200b402840300948410010303000c420191940c501a100440c4070100040e03640c16401010900141044055450f0008109054004c402098959040ca45001481c210410010500440b900c460240d8020500c903002c881220071617115415500034003c1d40c4009040008028615a401040040c0d5a28048513090100111003025030b00310303a49000307000100e42880b000e800c008010400a011401031030b80d944c842c6010030f503001408450910302045c0002d01000c064085d8410f107107001801c19a080d0795403402d480f188020104580d54610020340341130 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 453161303 1250 453160053 453160063
    0x4090b04061a07021e060d0b0a0909050c0409030315061d10020c120313030812070207060f0e0f0d0b060909030a0c1e021206010905160e040c020111030a0905 69
    0x4551060b80201d2080780444207214030075800028072a8041740100240d4403520030f695000b060000e80344035100d550f2520310000404652400c98890401d000001440e100c1501850350050341c040d014080a0244074140005403502113400c505154640a2075440caa031589001c0c0010810ba039910106010f030000748800312241c00c0005800b88032030f240424a196000214052a85010341d040c3c8082071403008500c1c00c2d8000c1c1203c010301407040b0031001040c030800c2c0d00078005002c0031090401c40d80d2280182640d50399110f20887d400316030f2407400b003051103010b2008400300d50340251424090015401c0041c07145441e0780c8003203d54010140900c080e605114080e40e0b44000104002c40c581a046d1901416a440720f500003415200300c2030440e584150082c0b1030707904131540589003142c00c40300b07003145035100d1a00340a4181e61a140030001080220200c0c600000f40399a507c801a0304140d550038840500402c11809096649843da40941c1e0800d0344000e600c110441000090641c446141480c205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 453162553 1250 453161303 453161309
    0xc010207030623071220071203094707110f060106051b060103081c0605100c02030d0e132309010204060905010c0b0f1b07080306040b0d051203090a0804090b0406 71
    0x1211600c0a1b2644455404680c001600080d080d8140790311104101c0242c030341010010921500303035101100751000c0c010809446260a50460030426450040064200042ca5148026108440401c820314000c215200c04c40c803101c2d05803075402414040f90b5180c03401c203a102074001000007030381c14004000500104042d100ba180a00242e52540c2c40301211801460b03d14000d40c05c41500000b146041a40244010719015180d802c80c0410007801500003004500242d019010740e410035000300c1d1140d204888482d40082c1100362201400300850001c1080400c22414060819080640b001305441c42c01d1151000ca0000f5940ba420300b0380082840c10191300040c144200e1010a00003c0d840c0300d0500d44c0f01c03800590010803070348c40c03210b50041c045005030f900881c0040050110b0511820b040103622659080ea03041c00a1000403003030010070741071814081c080d0317082044003003e0400001d008580000354a811a00b441000780c44d003402a034420303802151442c0d51380760220300f5818140240401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 453163803 1250 453162553 453162581
    0x60f120a082b09050c04110d05161803170708040306090c0810060f0312091215060e0906040f11060f0d0605120307170d050a050f01080c0102070306230712 68
    0x303d143c3d8656a550742655052481a529401c03003040c110303400c000765012403582903024001d0303040c15801c6d50f4103d1031581e502c0c00011003a4206d00c5070070007170401c00400c0726804420f8980245d086641c020300d40c0c00500c8102e4201000f044008041b40140c0a00603c480c06103442c000380f9407414404a01d802402c07401600d6407810310004101c182c0d07401c03400004803a04200b09107078110288038100c42c1c1010310b40003e050720302c418000c1010700000f50015040c1d492400c0003041095120890303910600f4003154104000d13400040001c0004000c1c480e100030380c506c55407244c08290107031030018816070400c108a5042c1440410115412216409a040100825680d00d4521380010b0346854491040d030780087c0026050b02400c0301c1c420b0700c841c01c0720122008180d041007142840303450000a00340569440c80c0d004031a000109203e000400c00f50014030050f00248070003480c682d1041c02510f44504545410700c80405200592420094100e100c5c000c0c42c0d560620003103a00c0051005c8440226038144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 453165053 1250 453163803 453163811
    0x105060103051b030a0603060516090b0f040b16150902032505190521010b0406140432040b011202130b130603150605010503060f120a082b 61
    0x241d0150305020021207003d030307189141e0326614620b098002e08581e0380b004241600e03100030000c3d080351407001ca82c0c0c551810754481e0802c1c0c0d8bc88031400220700520f44c100313041010410082259500510051105400458240703d00303062070b8503100346408604460030051512060403c04614041c040f015000300c0c2c101644160030540d50007411840084c0c02254054065040809074904105160000400300140b0140c901d180400b061041c0f0764090402c1c44842d801e25201c0d440924090194400703803030310351783c8012b041c86280d0204006000725040c0d2000c0c140350310501d281903000301c0c3d504600b2888500902541801d152a050601c060164003008941030108010310050f518085014850003400c80c0c0417400011140c002821501208403030002a45019400030402c0a0108401e00c00360010f20704000706a03640c0c00644062104851681d40103010020900d01854204140a014500d0314200c6804890556600303000d075001800420100d20071200160000501d41504200380032a014240 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 453166303 1250 453165053 453165061
    0x2030a06120c12031e0e01080c030708061309060f0608061e0601030504140a140606030a050a0b04050c060c0303010e0105040c050910021212060910050603130602040e09060603010506010305 83
    0x92000c0c0800d001c1e44041030180b060141c1418800c407405c0d803008428a090448600000038081c2403907a0b2091258085543d61001031540755040044e24420403160704c451001366185400c100201c0004030302c03841e02903a5554440c0100c2c5440c440d298450040c40e80c0000c5042c10522010315004000f020381c0e211f24a0400d9102c003400140081c213801c500d00b070030041800e45451900101e07507220040018030502c1034044010030310000304c00c6005003039440c006a41c2d107912803e0a0503143c80403000e004d00181e000c41c220800140003851915030160082042c0c80c2d10f25032080c00075580f079010790540006036201000500c0614505110075004000c200c4040000300388160b805032007405802c02ca184140440c10704098098001c3c0b00304c24842c0900e4190071b9960004c0c030100202d8080585005000d182d101d00040c610f41029003071601580c3c03006118500310795030f6080b00001c0424492003261255003c2c40006019600180007500603800180503114500d000030600d421a41d00824003410541000d042c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 453167553 1250 453166303 453166313
    0x303030601120b0307150f080105010305070c03210203040312050606041a03060a0812270a1502010209030a030309062406050a03020c0703060504020102060903030103110105090102010b030604050102030a0612 91
    0x51003180c602d044010a05004100c0000c0c01c01e1055400309050180800c0c400d010581d100500d81104200307901c0301581a43c80d100110202d070403c0703480b0300200b030640720740c1400f02c2d0140d490003c08040c044e404009031021400d04100740d0b04191021000b20354085d072025690340060149070b44c00741086e0780f40b82c2000c0c5804014001d0042811001d160300303200001060343c0340c681c010b00c50050314111045035600342e41010920140c0c0e10400910002c1c80180201c4030310a100025890301010004109040060510801e540107494900c00001950350030418841651810700038203c0150003514009541c4076141041025182c001803a200b40d4846d44a03400703406282e00c2070050a640140c5881c82e252200c01c032040d0002e100b0088846810711070080300004002c0d581e00040d1282e8400c0c2e09503001074640005242e640e0000b8003000344026224141a08154490701c05410034880520011650000000200381003c00c151800d40d12039400208008030000c9601800000340038110020b10750008035229 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 453168803 1250 453167553 453167567
    0x207080d0824030109080306040605041e0b030f061009110306030706111039051204081204030f031505010203040b07060e0303150906010f0f140d290303030601 70
    0x20b4448035800d1200c1802c8060340d5100e0b401120384090003c200b210154141300328550011560a48941d003001404a242e040038000c07080780c1032003a1141000a03094040701c00c003510528000c15094441c01060369603201d4100081805030880081507440541011032400c191084031586100002c2c0810522030662000642c150465280c0e140401e0807622003140349041c41c606014601010742001d4141a00d00c07454800d840102c5020151950140c020120809a0350920381300003010910900024041251102940740e21503c50072040c2d24090304a6490b80007804280c800307800194040b68882030301034044c0308410156407040000d0040038900300c0000d54902c2a405070ae55407400104d00175040203400e4105004000d601d5003030301c1d203900d0b0110107858000300010410744504402004a41903500645100003c0302003a5103004006182103819101d0603542106010128010024403812403028880e81d5041c211001460202c26848491410413080800343c00307100e500204240480307a03801c900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 453170053 1250 453168803 453168811
    0x105130f0b040809060a020c1206060a031712071715331612080103111e0a0801060e0606040b09190e0c030601260a0e1e06070207080d08 60
    0x15141035596203c0c90180d0680c01070142d003d40002c80480c281c0140303900484d5150740701006540d2080300303403548000269682c2c010744105401c082170010600114420021003840d403840203102c5450565a0484034410300d4040350310f0790018404044c01c05001040195141d0024030316400e00c840d040d014000038441000c0621003003044280401c42c510400d148200701461100b03400c00d426124000a0a20707401400c80e40803c40c1c03c08500b200c0000700d00c1c042d00c845410703203410004005000c1460018040800401d60740d000110301185199031580c0c0d504645c030750251802c48008202203180604290400d040909280d10a003000e00c024003844030140107403510801d040324046440c030101e020b08a14110143c110001e441504020031006181200045000d11400c1c2e8645900c4038800015016a03e000d0507540091211354000c80ca952490350081c40445c03050405032215843c10340e07005214a1030080c10fa1170759410040411928540502101c170040907804094002262203060082262030020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 453171303 1250 453170053 453170063
    0xd020d020615010905060d02040e070504300b100602101404030c021c060b21060601050901033b060f0f040807080318120a0210020d150b0c0105130f 65
    0x5882d102940e1194100000070314003d8a45a42e450451400401030342c400d009001f4841115004510703050301c80d808640c110303040c124207145815111442c3c075420a51040070310b00c0d4142e280200a010440b6800340c103014416122002c842c4c1c0f49030180103401c0c0840358030041031480c40c00a80300c21580741818001c1d4043c0e854900318210b0241807000504410210a41440082c0c000000c2410889940e10800c5441011a4580c180c0040c460343c0d84000b00d0221441c190303a401a03408a40f195000b4005030105071414100428008103600500445008007050f46540200440101c01d01078400f403840d040070b001031000b0f080c1038038011b452440722050107001d14049603a81d100050500c6000307016140c0b1241c2c40f8004030f43d1b03800c19003030101504201500d00705c5540070b0342d074414a0308503c101c2200d0440081d80c02070910981070300d044000a40040060091850303c4e5540744450a00c0da000600c05010b88000580d01c65206003a0542169001012802142d51094988000c00c40000c840d05032250706c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 453172553 1250 453171303 453171331
    0xc021003020c06070c020f0d030c03080c0409020f07110a031205070302030706050108010c020708030a091811070f1a04030e06090a03170c10020909060d030201061a0405030d020d0206 80
    0x114220024419000380d50858040d443c01d000e11240d10441602c100350003110101540d801910412000c6c0f010030800034003260748102c03920002402044040c0d4082c080201242c242552840002d0a0341c0c0721030342c00581d0f490b000480100b0001410004a90002d040d140f490100341155500e82c14065040310606c20b000300442e8100130948200700301c60b4825484030f070074002c550f92015811b001e000d0110001001d806501c00100d61604000290f688001290356001c0029190554a5039007480e403c036030071107080d1681c0e51020300d141004000c0c02d006125242421041072982404414111310455001c040003020341444082984078070445144442191a9039481406900140481d041980018480140d400c0034164007031100014014024105050b20450603990040034101e106000a890b171006013030020400a00f8140c0030f41c3c108900c40c1c00009509503e490700320003141d000e40101e00100900290611017820248010100c1415600007803c100d10458030103911030400a11280c6603c400b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 453173803 1250 453172553 453172579
    0x108060c09060c07090221090a05030a0e01050c0303010b0a1d0a03060c0302120c030702010e01020301030f031b0c0e01090606031e0b1309060923060f1513060f050604060c02 76
    0x2031260034024a0340300c50071550f030070542c04086262140c481d00c8440403150000041c440c3c02d002700d640040d5652041c05545003808042095540d0740c90400d103241005000c2c05000840241000214040d1249000c8903480c0c1945034401440200724240844140c2e40440980c002030b00c035840c20030192540500f001c2681351103100c00710024041c92081c6c1c45c2c0e010303881083c0715250030500b0095025088503402481030420fa40301040c242d200a00c4005c0038040b22080080209100786030503010302c0008280e0705505980d94a81c403040c2c0990303801003041034038010010402141e09110f4500240b15071b050a001d10b18100401c0c131071202e04101c103044003a40780c0204c006140e546141e4240c005c1c82e101c4041100313164604081000309540c0c1c000701e50b66102da150181c0c0e504840340340b4505091480c0001d00580c1e031400031b41c03140c51030701414118088400941001c003035a00d00100c020790035030400000400510300301105003c0c940651050780101d41c2040b0900130309030301807406848590140c500700c1030580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 453175053 1250 453173803 453173827
    0x302030307200a0b0405060112020310020f0c070e0709061409150f13180b060a0c08041d160905060f130e33130504050c0a09140108060c0906 62
    0xb07103620000c20707500841d15582d08000b29820403070b01541c000c1e400c4901980c2c0392020950502c81c2c2460183d8103038031886840b000c01a15030003c050110082c08401c1c10700000080543c0780c9141ca812035401d0700c20250402c40d1490380010100700410091030041060f04606849201901c00d6070a0540560a0001004407000782d4104883c110490b2491465556001c0e0b520401603800c0d901400e41107180c100c4002540080d036014425640000a124074504200c151094805103250b1904403001c030f209000001d0451685070043c040240d000c882c1c49074600c3c1000341d0016144018422506010204d441400310791035007410740300308450701c03034503c0c0e51502c0301d8860a416034502c3d031182840c40400d408000745560050903100d81302c6e402c031424998048149542e001a101c000b40a69003002420b941c8448000064008580150181c019502c0c0651900c0114403030821540180c61541c0e00e81d01c118810040300d4807460300505100c0090506c50800a41c18449803190312a02c910130a400f181c11107000d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 453176303 1250 453175053 453175097
    0x604150c0f111c02070e0912030708070c050105040803070e0907081602120c0c03070b04050f0108040816111306050a03121806031505060306281a030a060605070302030307 75
    0x42c0d0f00742c06400d05065052002036403800240150340c0c401c0040d00200c0c003d013030001091040706400380340741e50441d510340170704803001d94006003000c08210840e5590000300d8020711606000701e00403044942c1c2e0345003104024006107150f491050143c480d840070025005d0f0300c4555250008000100d2055129007080228030701030078918040c41c400c400041c04024440c0000e125100008190150f9031503903659a0446803c3c09688602c640056010001d0381b010340c40340722500d0b4410704c00d0030040c4c1008000d145e498004603440204903124403c1c21750a808500d05070700c0e0718250261074007040c4299410300c0041354020045100082981000d8550016058010041040b0f04104842003051032503136098014054107001c02d40c5401c1258401c40401c4600348001145d1280001500c210041219a070074810214100c0b001240a03241d64000450b440e40346d04600562003e416240c51303124105040034030203c840d1940110140801040464006038011080da81e0048982c1040003040a41800c404050307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 453177553 1250 453176303 453176323
    0x30e011401080105011703250c0e040c0906080a080d0203040503190206010e100501020d0c060f060303120e070e040b04020a2d0e0903040905060f0d050604150c0f11 72
    0x2440c480000403420708415030245040350800a64108400603244090780c603485010510362140d480e210100e10f01c240b83c8001100000d11600c588083c42c0d9035803c980d002c01c4000c0c0c50032200820f910700d04001140c2c007030103640060018100500b40004c0e0696810382d007841941da10301c0059401000003000d1020500c03e035140b13070219010f151014403500f40c0003901d8140900034508102c48440114280d4649144a207055640c10780082ca840c2c8141c85095034101c02e02c010842c0e20545a4080e810244823600070003004510a07182d08031504072000c4118103440b002c06218949500400c03041186000007203145410680180d5040c4040e12180003040708030b0125002181c04040b1401d13000f13090300c0c040201100f245080851145d516032030740300503114074809a0390100c9980c001e100078000b4410952005410001c0100002800d2100e440031070840c0301c00103016902d5802031030420080c007450701003c011001c00000100841c000c3d100001d0200040c41c488034040003c201080e92140c40200400188 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 453178803 1250 453177553 453177581
    0xd090b0c0309210f070602010e030a14070c03082208030c0d081302030a210c0b0c2a331602010f09080903071d04030320210f1006030e01 60
    0x600c1d1505004c176694076003807140c0001903182507101c1d000c1c20004001d41c0e040621960301c811001c3e03540e101c0c490058000c0e4034240c461a461040010009010400070800f8042d207240040b22110403160b019411115a40602015001000103104100380401c08065011407400c000b502915140c9230034141031401540250544654103e400c02d1002580100c40108801c0c1c19250245669420445032450800d0008011860b900e010131442c1e20b0a0026240101c510040c18040005d401d8000300c2440d0500b080c04082d402847c6015144580c00710740d050380c501a0039205a180c00d114500d20014040100341c290380400780011251030901c01c2d045416803d02010080c01412071908044843d6480700c00d030b20340b080c0305401c80025000710489074603220442090103134607195034a4400341c0c040d10704840c00311068501c0075201d07030708585d400c000340000004516000079a00440b46450250b24805402e034001d0030300110800503014110340c044016103401d481d0110f402d11030030075400e014041c403030030310b0031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 453180053 1250 453178803 453178813
    0x12050f1207021f14010311040b04050c0304050124050f1201291509120f0706050418050103111002070504020f0d1a091618080d090b0c030921 62
    0x312141c0d000400b04003d0780c0c0241d1041c0401c801c2c443d1001200c107a4194421600100e000400c00319514256690302c0c008080c0c00411400f0884001408440b001c4a114940290200030321041c07240c244103414aa81040d04c1e03403248a000b41c080002401041d00c43c0d02d109200308602c2d58220303102c4104030005803d40c50001e01440d2321103100700e0140f807068414260240d40308401380e0320720314000880b1080702c214048041e160016180070300c02c441c03410500c00b041d54030072a40250b410020801c580402410680d50b40c0d600c40c2e0511072440408000c07078014202e1242040010b01c04104641c030f03000e0102e1000c40f103680301e12000c039038140d080211907841240d005202080800c060060a801405511412001003211906414a41600c80e0485500a40203520080011003e4002d070112411594050030421160300107444222045c04040d0400707506a0488900c0840d40c40d0802581005044040b40550070032408841d0241d4a003d4504414840e216850221400340504600051070081c01e07003d0b03030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 453181303 1250 453180053 453180061
    0x605070503480a030c09120f0f0206041205010f0b090708090705040c0302070302060a020307050405131803090302100825050d020a08040317010f05060c030c01140907080a12050f12 79
    0x140341d4000c41110004241007000c1014018486c8402d001660121101c0e00c0340381d00e0350f8071040c2e02c105808600b190804001c0044c04e001daa102c1002d000201039645482d0b0841d0300b5440c195017504d0309105000c81c0d40b4100100d4030000e50700c02c6281d503800311321450481c491795074041d241c1d4034202c0c4690040340c00074608086024560b6040d0000c00d0740ca8069005c403802525070040901c107d2004171140d4000410a1205005a01c8c200d050841011003004000c1902050811201580c1d422454102e0200300e0307520b820401c60400d040d10a0301a422400e24145c68941a031400040c04c4a550480c102e0f03d0441c040a500a8020300595a29a141202c04c54403180010009010300606640680108448001d00c499001805142c0780c1603426144100c550140f400040c8159a005140042440d000c14041d000100100f4442e5001064001c1504480c6043c01166181088201e03045440160080d00b040d078041001181000c0ca040c0301490a1381d41c03002c481e0641c0c43c1e070b40201644410104050360903c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 453182553 1250 453181303 453181441
    0x702130f0c11070b032202190f0f05010e03062205190507051c0b131401061502120304020f0d020a0602070801060611060402010c140d05070605070503 66
    0xb5402804409080714a15510703107007580064002180c1540d000000c1c070119103550b07856505038042035032001c0d080301c440344402070701c0d4580d01c0d042d60001021542d12550400074500080743e031100820080c200041002003e00c0800e0311403500611041d1150403040c0b6952514043ca4406501243c2020070764100901002e654586507441020998580c4201140850245000034840c0c2d552000e101d0380b649000c07010b90343c3c40709000c0d00800d03569203202020b0b66200800c15038410740400e031300402c000140302801d08120400a15050384548115849200e214044030755240407241c1180d0101c4000a12001080020799550764040c0c0080d0000c4040500142254000402d00140d07140350000307000381521a90304903a0010481a5032001d6032106010401550080b052800c002c0c0c01078540b0308078a08000c40c0c061030110402d48150010b0340001d0054280a0315204250700700101d032a129144d070401103403203001090700e0882c0c4426090b034216803d44180d1042c590140b03012a260103400c0c1c9030202296 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 453183803 1250 453182553 453182567
    0x11030d030b03010b2e0215010602031b03040609090b030c04020f190c0f031101060306110406080f01030c03030f11060114090a0507091202010203040e040b25050702130f0c 75
    0x410b80298208801c1c02103e10740410103154001112640d0340c8941305070b103188030042021120001c158006e40c0c503601e005900d00540b060280240e9001165034804205403a01182000555081560001e220511540e03500803115000c07980240030114004500100003410441c00b14141a803091000800d40740d8156540090916011241c2448260741c0c090402920304c001f21540c010300d0201135109040020f8002c00600d00c00320084400026003544903075645080fa1071500201e100c103800441c082040c283d22421070382d44a074801012046a5146640707005515030640002030900500070585c8140310310860442c200c854a401c112030b1b0650f1749000100c004e540c44000c1a00030b598100c00030344070400c01d00519004041c2541e902c200c1e181741c140c60042c4c900801c01c00700d0450004200c00030307102e011960391034000c9000c1c070310700b0240d070030040c81199070004500c00f0340d14003211002d07803091844d0300a02903503c1c0c02d80503194040c800d020303448810001c188251036414034038074000200703002c0d0f680054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 453185053 1250 453183803 453183821
    0x10e1518010e0c01050c0a02090c130503030f0f030402150d090221070306051315050906130c0308030408090d05070305160e06060d11040b030403020709141311030d03 73
    0x1010004212080402402e039040c02c00000b52641c04030204183c554401c40040c052440c804055960840300ca0380001c882e0002581d0300314001c40003141c04490354070000005801854110b00540ca00040e0308803a4960b402014410244050003000080540d00c400e081034220b504003140700c642d140c4080e03007604004c1205403000e0340200c600d000000e102140340d064010031141200010200d40d442d5a80d1407029000c0145007450444c4480300500010700c0308a040c2d03405291110010076140303000041039180440007007850100c1c001c10217045000c02d102411810030340e80c10402d004e59980c1c0da0b041c071000d20720131100b407650131885804688040c404040348600562342700300191b400208400031415000c428600401d100c40e4840d00104800d450700398010b12580b01030f020042644091004a280c858000b0351111200020001c200820564140940b0f0041c101080c0100864956045490905100240380c41280001d00c8503e5040c00000b51300e42080300d42c014200c078590914110000c001d020285 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 453186303 1250 453185053 453185071
    0x3070503361002190b1e06010c0b10050604032103020310091802040c2102030705190c0212070f0f061407030c05070e0405060a050621010e15 62
    0x50100c01004040140e1549503026a150a400603203820410440c954094806019031160140c2c05140c020f802c41d00c01300c030f5070141401d40309900d0117000d07016800c00841010b0b0501280c1108100300d03680c010900b03859180d0440c0425510740c8d00e05003e40021380d1039401140c0d00510109001041041080301380700c04948000290030340405c200e405500f03074081034602001c500090314092040b041140e008002d82c007405103071025100000d4021404480b0900d8540c4005141425020754102d07107045200300700041c1e03130400c41c95850004801809400340080c2c01b5070011010b8512000c2e42c3c840c803412082250020552082502e00c0e80d051983d0301c2d0b2034401c1007150045e00c0d00c005080c1c44100812021506039031030300500c8000c540a01801c0d64400c607021800d01c028207810354046075007006940d002d005c480c0f8041700641400c0c00e00c83d00e003250040102000a00b008104091911030300340d01c068041c0f0f003050307140c0085088030409001d0304419071a89050700ca41540d052486000482c0c65000709402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 453187553 1250 453186303 453186337
    0x818030708032e0b09010e04230106180509040f02100e1e03060c0906160c05010809010c0207050f0109210c06022125050c030d030b0109030609110303070503 69
    0x3400d1800d5002d04025001c00034030407500d04001300c940034401064001414545030110401e01d00000b000c42c1d00d00390a40c8a001a030f4020360f15000c100b030a82e01d006d40baa03800d00141041851032034110420070b90260343e01940980f400704007040b003030b980c0c4400021b82c000c04500c001e500603100107006c0381100800a02c1503101c28450045070b079460342c410300d032180080c3c0903180c0760f503a5080030503040c0e00c10000150010820051410b010b99011038140c09030b881001445031107840c00c0b000400c8000d01401c0c00742583d06d0300c05403402d0150000780c0d2104070303102695260926824440140c81d80c8060340e204403000f00740b400010318464001d1410a580038440c441c01c118850300c81404a945000c012615100a4014002d14400504150190640c0c00b4405c000d810150b8800481580150584600719a10b612050542c68607103010b100e00d8040403464501006601000000249601141d11015114590b00c1d120001407121000d0082200e02c0040e00300c030307926842c52130040d0f41e0350b0095083c50081426 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 453188803 1250 453187553 453187591
    0x621030201060501051201140a05060a0801030b01090608150c09120c150a050a0c020a03021003051005061918032103060602010b0109270519140f0403081803070803 72
    0x2002650580f46c600740f5002d109030300b00483c07076059800001016078401801540041d25594040041c050000103685050b815491880c1c092416801170b00250100b030300f003401c140001c040009030010440c0c4c90f692241d42685500348041c5491040100b82c68004500b8800b07102c20600010303030848901c50030f4859030307a0f41c0142980d44401b401a4082040028001c01c100310b5005e109034200040203000a0641c410990f403076001070036018000d04070b040403a44030010418a42130119040c4000d00003680d99a25085c4080740040386a01c001c03064909001617803000340242502401054091584845201144200304d441e140001095800c1000000c0c06d003c400701b0502d02c103000d40104668103031201d1090340d081504a104401d0000c0c41d20140108204559840e4809401800d01540707110400c200f1441a000c1e541041e44e80c5a0b01c03004034013000c3c0c0240050f24400c099a0340d03015404d0b01c1c0c0395042d41c540c40c8461120b02c901001c184050700c03001c640d00b01031241e040d0054cc01064241024494545 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 453190053 1250 453188803 453188807
    0xa12050d14010b091e100c05033016020303060d060e010c02010e0607050c061506130e01050f031c0309080f04180b0405190e01020c010203090a021822060621030201060501 75
    0x7038081140d64001403c0f5003103d00842c024699000d89034402e4060f0ae06000c03400f81400c108103144440c454101d40c0078020195680710040016802640080c0781c0000301c0c0c00201c0c080d41d00d200103410715004a0b0200e1500d41803008980c0500304480b2450020310681443c0c980c021301070b200030b000da98094003c103404903951a00620441e175041c3d6030341c0040d00c244d030384500a0078110110145580c0d080041081403100c460021111030020307100c0107069031841d5051905106205c205802118000e0740700c2200168620803070414480072906603c1c2c003248100751450002818002d1400d908543e40e0045800304241080c5030310822083c03c40c1c9030401594850300304200540310f0542d0714600002141a02892136140c0343c214842c0542c006002500c1c15010001d210308a03802114440781c10b8104a08803070841c0350101c8404010021918100c819003081440002d070040c0303001303d03003e03c2d86d115004102040702383d030080030062550803516070004c0000c880014051000b81c000310015460720101080302d42c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 453191303 1250 453190053 453190099
    0x1503060e01030f030c060e06040b010e0604090308010e0603070305070906030b130f0204112703010c0509010207140d0609080c12040b0702010513082d0a12050d14010b09 74
    0x66009070b1007001c000c43c1620240c48442c103e1030305844c0c0d40d4880002c07001176141000003070b0145220b80e804031a10342c9407034500600240c01070b094521880c1040e5105010951128801e4150b940c3e07004002d90944549002034a4582582c1c00141070b03008041e000035007812036a01180861b8058035000b021035450510b0602403844a1030014034030005514258013500342988610214201c400c5420705c0d1800c0c0304d15a001500218440c1040d40005802040c100d08081c02812070181250a0040c180849640041e484212314020000006a0b8074080141035480c4d03200c10005580024082000503068180b0040b00c0d4801c555000f03c41c0305500c0d050003400d0090040f901140c05070070780e090910100c3c1d40110b40a502840c07a44400d100c0e20369002c074502a09014036100313510a5400000b00c0803070390b45400c0103420550f0048400c0e030044215000440d00444030074880000320300c0c16640c2c4448001101009003030bc110400d405982e01c04c0041028101c12000300100300c4100e0f04803051405206500d42c1d50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 453192553 1250 453191303 453191309
    0x908030a0e030720010c020a151107050a050d080f0a0903060e0c031207050c120c1306050108010902030a0e1e014a0307081308061003080a03151503060e01 68
    0xb0880028207461400000605056107020500d01b2000300d00c3c0c07680014041c0e20080d00010003101300c01c82141072003030300b000c10040f16004200c00380c100c035890b0000054052030a482010700031490300b081c5104004c2c07190120345112845031055034440140c100020316140c418001180c005207041e148000d4604002100180300c4001402040f80841001120312540c00c566001c130b5492155280180d056920090620443c0210500401c0d10103500c80802410050903000441901d01d0504107100a9074000c02d124190307407401a0242e5030f0344030301001000419100d0140102e9000d025103498450000b690b0b960301e644411030091140340101da04007403214000350044410010a480f07201c1c90442114012032550715080000c10054810401e264210340c0310920403a02c0d640c00103444e503071505c4600100c501401401004020700d00e06a031800c490894030380406400d0321008500404494400d800c4100c142601d160b080c6201a500c400d0321498040d10351080300403e00f02180803a80c0034005115070f0403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 453193803 1250 453192553 453192563
    0x60f0f0c0b0105061305040513021c081e070f030f080108010b0603041509050601031104060b040305060a090c15110c0423040501060905041407093605010908030a0e0307 74
    0x2982e4030380300401c201d513802500b82000000102c4030009055a552161703074440d0301c1158110588464910412000502d20b44500c0101c0030a680003102080c210000e60f416000340082c503841a00482c250318140d4099660014811150700815508260340801c1960f0650300340d48600e03126907204c0f00d155003681d50010f1080d810000500025021a90790708040400b0314816800041c0d45039945c83d020300f4598241c0017502c04240c06521741f8158202807190030002d040000d207090a090840d660705894600241000c2d0301c4544841c40b0300240900001030300d000300184044507041030140c5801a1200c2c070b5106880c4071902400410400d541010302843c1c0c6001d81141c0d0035070030203190100102000354054420703100ca668444000c254903800b40304807030065005000c21512030001e4444140341c10f105801006041d0b0070915184058540740f80f58001945400b49502c1410110000100c004140800c2c0a49550308218030f01050291006c01917024620900c018481c80c000748a05a0b07592088000040c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 453195053 1250 453193803 453193823
    0xe0a090209010305220821130c050603010501080106051b06090a020103050108060403050f07030306080307060b03160303080a0e24250203030a05091f0b03010b180105091f060f0f0c 79
    0x18505c8009044284100d40d120341f003101058429480580c04403810244041c1c004984400d0161a90408006040482c0c800b0300e150b0610000800164041c8582c005201c0c0101d600781000340c0341559001443d440c1800c82d07002e482c4c0040526580c4a0304001a40400d260030008030398501c02081a520858040d16031a24194040d90340326005e0340000800d40400d42e4405001c0f480003801d00040c40100e008000206501c602c110402d41442c0c095521034807902d04240c81040000e030042c0c1695804600000300044d8007071103148680c10100c1014051340701c2400078542000407003e06ca00940103c00c40e000040c2030500c0c1d5145031604800c3c0c24407010140c0d0007440002c2d2100603d8100c1c81e4416a01c6050303504080801003002e580054440d50180c8850f00c3c0c0381026900d0509114944400804803000031030320180c00c1d00d400710b104041c06101d00451402c8005401445004a441480007100940d01602c43d92110001e00c2c00b801c11030400d001440314003003028554400c0c5152940c240d01f0020b044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 453196303 1250 453195053 453195121
    0xc01110705060306060702031608070608070203030603071710020f030a27060b0d140609062d0a0204030f1118091905070503070906090b010f0909020a0e0a090209010305 74
    0x4111754000c0c0d0000c0780e1500c02d01000301900400f04c1c084000400d80c410040041034104003024000c1138004281400315841802007000760790340000c120003280c0311842e66581041e40841014104040d95079007400d050300019070412407544800c02503208080c0d41000708942c5414084143c95200486003580b00f0004581c24600444c941c4d0740080e403801c100405a40c201c101c039642d9121607800c845400d01c0035400240411a0070710060280340e500ca00d0345c000842003407140600c2d542c0a44008401540540d40e02000107103d4540d5034111006144c20400400c03100c510ba28164107400c884030101030060945109541104180440701401090b108019040c0210b4a0404034150400d040080d00d040c40f521f13100043d980c9082c06403801800303d00030301048650400c04c10344296070034442e4031410090300304407041d04030390320003524000e55081d402c0240ea6002c4180c82203030100040111164400320060380084c1ca9502c60b8010300800314280c8040c001607656030300580065481006038112141075804039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 453197553 1250 453196303 453196309
    0x705070303080901141f1505070f060608030301030c1a030f0f060a030b07030f1409030334030e0606011416030309060c0306031502040303051e090306090c01110705060306 75
    0x41035111440500010704403241c182042c1700c084041c2d91446040221880303840d0042004021003010382404121480041420340c1d00a04500c074028000d042500108480000c10819800c4000103010141c104ea40780c3d40c480c1481c001d112568441d01c00001d1b4409198500d001003281680c0c4036103032500308004543ea80c9007007210719030030081280342c0c018041d000100c0003035601d48480740210140e50380012041c0c1105c0b0b07404100c48608100c582200c1c068400c1100702980002100c3d13108a11078085c4885001409142d000303101d03200460011040c8007203048100d41e40c03542c000441c0e82c94100440c3d13480e44580005642c0c404100510f03560050b0100408401d09001c21710803142e041c800c1c507000540600319164a0202c42c2031440410000c2c3d10303140c0400c24004400942d15080341b0400701180380518541e8003034010f1050821368840c45092403420030050034140c05039100c18038003606644841c5824940203441b130030100c540314041082c1c203882c80905480000c8200942c5d5010b00f445180d0f854400070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 453198803 1250 453197553 453197567
    0x30b01081f0b01022e090305030105040c05091c1a09010f140402030706050a0e060f0306090c0a0912080403061a010224010902030c070213050906060d0209040213061e080d03020705070303 82
    0x201d004200c02940b41800001841206d841d94025640d00b5100d5040c10200420340c0d4103140f2003410010248070350f0b0f20b41c1d5030710480880f10340074000d015070b9510450b10f0b000c17149402c550015100740500c201040400f600c190020081940304102c104050944c02c4400d503800c5200790340180d05688025000e0000742d02890040c08801c2035410020325184103c00011004d912007071110703003008400f20511813141030041c0c0454010a81c1c491160510801000081018101e0b1092884125500c01913100f030203402c00c1220301942e00080140040148940480000001c1c1d1038441d006200b44480901e400c0d00001910080c0400d01500104513417030300c1651406900081c14035800c000041060f0f200580e50310310b2031554014002c5011400d840c062a0060030108014078943c00380c6030804003500143c0da40c03841d840c1d0085d41192020140c071403900d8148000c2650342c1002581e0300e0b80388002c4a091010192002c2264003444c1140d104c000c0403030044040e4010010b004100358092041800080d0240031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 453200053 1250 453198803 453198853
    0x509090a020d061701060e1b031003151a120a031809061203080604060b0d1a040213180204151b0b07090302010e090105060d02090604030b01081f0b0102 67
    0x1405802d042054104608440441d0312050406580b0825524110420701454000384462403117182985462414584452144a25004000e50000c0050058880e200a03040a550060340442c00a5400c000c004018074002070780c64406803580c01900f10618207a080310501e260040041c003440800c4d580c0030380342051030800315440e40c945124003207680b038410700c1380f0b5008105c2c00d0594480d000c40341c10083d11f104000f40c641c5019604245c810300c030203511541200c0b11060342e5080028210503101c00303042075907848280b1680c49400061a540c4812807406c201060310b07540301311202c20103040030060049103e00d10414410340d000415844019001d5154140c0014642c201027800008030b503580d281c070030412140e03074010a03000a000d1043d564001d41503030b50500140c0f151100c45d41000005407103401030f0050301d681c0c0b64000905245039107903801658001c55001b02c01c1d442550f1112042c1e52100301c00e034126104190114040c1c03491501d24002c403003c2c44010380241440340c0b0f00403802c09080d81040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 453201303 1250 453200053 453200071
    0x6030a050c120c061303140106030507030201050a03020d0e01060501111b090c040902040e012d030b0a110301090f180f0305030612030309060a0c140d1a0303070516050907050909 78
    0x3c1c2c4096103031506001030941e80c03503060365810000c2c00e41c9000e107142c807003048140103560f01d014401d1000960029040d020340e50242000f076100d04103100210068404c85034061400c80c02c0c14100491030005400c03a205440d400d0301c0c0c20494032000e200c000c0c3d0300e080700705140c602c904a40015071007074184020b04a800480c00c2c1600e6241a40324001001a0ba01641c0712000998000004028220312070043e0340701c41c003130a100c07210080c4140003081000291030001518290801d4041440c4000a170301441c40700010001c0ea0361607681d5004e1141c001d00640754110031190603c1030041205000182e03d1140030780c081020403807800181c80031a40c5410080000b0b801c40352203100381060400400c065442030075064002c020300e103407604d41c1900381c40301c684401c0c00303001350074210958008002080d51081080010001818500c004400d40444054003000d9054080003505005101000c241c80352a100705280e400d40e5981d0760014015500000ca400c1c000041091000340309074a803420b80141c20840c21 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 453202553 1250 453201303 453201313
    0x209060f030403030905061617270c0a0308130512070e0712061203020d09060e040506030109021203121005010509130605120307020a090c0206371406030a050c12 71
    0x2682e6042d05c7c084081d106413024030f860314001950660302c80c44442c030403e8030742020744882c101180100420040143c1c2080c0d10000b203040c034034203490100301151150100500c03060754a9580c0c01c1c00c5000d80e0100000604180d00004046410705104d001708040e000703944000c5c03000a24080c0104081031000d000d020070455881c0b149a0b40c07003028010f240141001d6003c0400c1c040c014034020b881c20914400d81c006100300c8403803c0000715003144031039104ca04141c8020680782d50b0040000d00412035498001e50015500560107c02c0f90000058a00c00210200555058640d0396085901c100144203240c0024800c0003011214106a2210307481007001480103d090398503100090791440c03015442c00d5103a0300110703110b82035182000e0740d0300080c004120704021220800b02c0094581c08010b00c00c0c0007a190103003024030721403124408001411003d640059143c01412500005800c1c007285104000c40c0807004500d0616000c5094580301d1b82c0030000340300c58071a0380140200380150250594540c010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 453203803 1250 453202553 453202571
    0x1b0309150a0c15020913090b010522090b070206010603090803040f0f2411120403050c0f0d0f0f050a0f030e0c0301020d020702120a080405012f0a050d02010209060f03040303 76
    0x802c1031a405506043d100542c403000404144482e5210f42900313030401a0404904d04042510004c1d9035042d2102503940c0c1b0544440e501c00b80c20044281503103a41c40038540790449042c0032000040a010794043e03825240581d0f0398a00403020b40700c08103006040f552017000810000782c010420078149034800c00f4441241c0810f911885805807030b00700b0710312140e03048621007031840340c0c107100385940c4116000300d85051141c0558040080680100000c050110000342d002030780744100840c080b459445c10403100003100001c801868015048440b002140109403285819401242502c001c1c034030070f96804118103500030041b00640800c2441d50210f00511086400341e481c280001c0180c81207440b005a1b85103140d205215006041d500c04101e0f0f41c12110300c800010b1088421103080394402d00c0c120403031840f01e555240d10345042000c948461045071a01382d0f102800440d810720003600036015616282c50b840c200780d00745d20400d031440d94880720070810313804801c1d2520040c5030004e000740307400104065 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 453205053 1250 453203803 453203813
    0x70203220609291b100b01020d1103070f021c030906080a020c0c0f040f0207030e0a170d03020c031b0a0b0f070917010b060708040f15080c090409171b0309150a0c 71
    0x4462151044416100c000d104061f5804111034100045c030340c602402c8011044158507240c0c000c410005003e460501440410356441140034201c2c00f600c0c4e000310041442d00d2078003a024a840e44078501c081940ba40005902c910741e403094402c0803440c240901b040207135170420405043e0b241c008090f407180e42c822101031800b84a201400360700d031091b103400b9680500841081111a05544442c800762400585000104408113031005801e40c141005030306d130030b41c1d5403400d811801090f180010380481000c640f851b400d800a20041300c0c602401140f0307002c1d19541c0d090010001e0440e4282c1c0401d0b14001c0c20003510381038241002c10035142c0400010f9111012002a1459101c04002d44464401240a0090800c0c00c518035004114911083c11084202c0102034507001004061031030201011503509038540307a54100703035092544030302100400300004c1d00f4581c1680051030440b100310413400034070300c01c0c901c004111202418001c100c0c2e480c00e8140181100154010340f121402c00100707070098000a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 453206303 1250 453205053 453205063
    0x1060617060108061908070801060506040f0605070c120f0605241005040e0f060102070902030403120902060c010606050c07060c02030703170f030703020403140309011403070203220609291b 83
    0x303200060000e448c60004e03070609403002030b009503200d510200020401e85040b085240200c80942c1840d80d11006542010100103202d80c2c050a02c29100780da41d081001403020080900c00d00c1001c1c04c205580307481400c11801411440d24852008041c0700b0784c0d03001d1500811790403401d145480c0240c0707015200d40c0009218070003514403024042d040001c0c492250b80500401002d0074500104600718900b58500030040907244044020301603a850101e0b055407100c5d0111401d000343e003002400010740e2554000e109604c40c4080300a140210403020400314400d107480c01d5015001070041c0082350035030300d40203502c2610f000741a0034100c040060110502c2c50101851264202d52401600d807803031420160702038a169514914550001c20039107074641c0c0c0000b280c071070254802c0c51641d1a81d5580d54280d24600c925044404260340e4640c5180c106140401d201302590401d0fa02c0a4080d5070b44c00c007801c3d0451808a0111032040d1354043c40c1c844130800c201800711505003844480300c0f0100401464106 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 453207553 1250 453206303 453206309
    0x804050a03052a160503120d020901050f1c060b0703080a0e150c0903010c0e01050a140d090f020a12030f270b2106030a0f15021b010606170601080619 66
    0x1a00030070381500300c604c000d428400003000c081e809811041c5284003802510300c1080340c0607132150b6020803d9800759100c2c20641d210040c5041000f0364890a1080a210f10031840c1913100c071083c185680400c031504030a090b101c01c41c1e41034a03840240d032108014200071f00392081198445105a600461b442c40420340c0fa14010303601d05134041c0d5130798000b40c149400d40340780144400c1408008000102180d07807000844090ec0400e290000302201c001a80882c244514094225668100850030003400500c00f4110031561084a0001020317641c1c1030f008418411000000c1c001c55605141c10a040d800303005103001e400403848980695040b0b80e010f060f00c1d4202034019004180c8049031620000014136041096600801868160340c035140307002075562051103400a064000d00e2805d10104850180603600c1c00d025900159100c14165400441ba503050700112007240d0300781400001c1140c020407401c10050300d9112000005c1c2d440c5001507030b43c85e0020b444250440c1074482c62403080b07004a40d0b00009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 453208803 1250 453207553 453207637
    0x11b0e0103050c1612020f0106060e060702181801150b0717040f03030309030206061e0120030406032702010c06090218150315060307030b250810060804050a0305 71
    0x1100301789000c02407504d1103101c2d164003542c0c5444018010300d6000034150420502c1240c825a44072030f14408101c440764000f09000c10241600309001140c0c12001c60424000c5903980200305a4640c002c0745440e43c0b4481c4952101c1d06030812090010482001c5500c402c1c4039024015860955111209069100390754030580010783e03a007007a2001c05505204840d00024205c0720348000805440f4200140e035102d521040c140034030420705074020701b00c9030b030a8a0100d51f03c505413a110781c2c0d1550050083c0c100010300705440080d102054082002011039050b6440d01030791403001610441e502d0340d005003201c1c441a82e0198a9040e03445104580000003481242c55072080b41c045220030044c1440e042c0c3c0104510100a0003404100540e2000a128803c40740c01201419468442d80e41c0001c8012446038050444407501f01c3c0d0f500c4050b0001d000c94016041c050100111650780e203012a0101810b550050158010810620120b449000074141c200074807948803103099143c1c0f48003080b09001d0020482d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 453210053 1250 453208803 453208823
    0x10f02151e010503011406042414030f060f010b13051e09070309020105160f0503030103061a010503070f120b060c0c090603060405060f130204021209011b0e0103050c16 74
    0xa402515881c98900409007900244140ca005840800300040018407642c0030b15136030180c003031100c8040d8510341d01041d0540a4608000d4459001c0440301c10065146402442294800030300b41d280010310314400c1c4411800030b210fa90030010800825800345030941d03a0b9645000c40407600b80e850030080314904c0c0c1130501240800f080c0f134090142d1203c0c01401c07072052500d848405c80c0580d03080003c483c0500100c05038401026030354076040c004000000400381c51844044004001c028413684501c1d030001100805a41e0242d41c00011110740c031040342c00b90000b85080003a00e03c1503009840b10004440c03200004211002030713101103400c0c1c2d00208040b004a6007e001c940c1040d040c032000c103c0d0842001c2d400b8000500d8a0340fa06c1e50b81c0c0c04003500014040080c4800100e01110351030b456024980c0c0100701355a0703804070400320441c204003603511440ca5403030202c80c980020443c81d04a13894035107580f030b4080a00c21441c015001050001c290b042001b0040080d0004002c0003601c921031a0310480e0058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 453211303 1250 453210053 453210091
    0x70804230709061403010c090815040609050a120305100b0d09151802040b0a050a05150408030f0a03140402100e0103060f080d0801090b0d0213091a070e0105040f05010f0215 76
    0xd1b09480300507007140140540c20030705100b0307d0404500c1d640406035210780d426443e251840d04400410510f8000340c06030090301650400c20520070341d54011443e00380d800b030003e91680c20070f41504013258401c000b07203c0e80411060121a8072074021002460280003d5101c3c0e40e08005501d054406640e0301050072640ea110710800c5190034407070601c81c008180c0d0409149410701000c249245107600445104508400502e10510314901c210380142204400b600c3c0c641c011001c021485811491030711000c00e040454403a01c61028400c41c0f8440c50700100941c1a40703409203003c2d58503000c1c042c0b0345410181c440d08040b881c2090304290000030f20b100f80080c1030303c203a10b000007400711340c06030080c030012402d0100c0900d007a592840e042484940455030080141c12007080d0b94001d026647d00280401072418100007010b100315036242c81201282c4906042d901e01000459151280d0f0290805041e51804207110a511030740038190410206d004503038008080c82070805072100c04840d5010413034800c0382c0c65 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 453212553 1250 453211303 453211309
    0x5030714060a180305010c0e121902011115090303010303110615090a09150507020d0f270b030a0b01090f051804020103060902041d0708042307090614 66
    0x50001040d408140d540c00300c5000002410911a00320780c42c0401071600f01c145030705064001d50f5001503610000800000d041d440026150800c49130000c1d200f6408040010b40c500404070303080351003006c0a480482c131110f0075401900c0e9108040c102c124a4884c540401d42410029181140510f10620040da2039625503e8020440003030f4118101250300180c0c18030040b081d080d801140007d10851703a14801c0d5541207419401802e05070006040000700c45041046100c141d440706d40181040e1b800d580711801c1075603007540c03a0450008407000064112040c10041b110071900b020190700710619100382c09540d0480d450703007034200b0340f1718044041e0707204500303000d035070700a22010014061010b021500c94682000140c80c030010028107071034441c2110020381168800d90064001d800640006c40d103230364982c04680d10304220407151082d80422134020800560160707a0031440340b0b600000c0c0078118180d6401d401c0400c01542d20940c0ca5124003003010800040c0c0c1d018034005400854101c508081c90b0b00d0070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 453213803 1250 453212553 453212563
    0x6010c14010f140405060603010c02102018010215060d0b0a020d0c052706030103031b120207030611131a0d0609050402010215010303051902071a091f020d080712150503 74
    0x221f6100340c0c50040b4a11001d9000704104840859401380003400000d0040310800751210889004100032000840020080c80300c80c2c441d002c1c0b4405e0b0300300d500e10603426800300c101c6503003610300d158403100000300400054215180b0a5008450303010140c107041d50100c40781c05440508040c100410070102e42e19915941d19000b0703c9040b400114403810883d60540420300920041c00050100640b400d01d80d46804c1e265402080c01c290310003180302c0b12800d03216001b5200c0c442d50204660f1a81011200d00014480000fa01d405107903545014282e1840c2c5044c802c81701d1b45d82001c0c032030740400a110720502c3c59050320580c030043c01042e4003c19a49000c1c03000904000c140d17143d2541d1202070000520100f6445002e42e28440c00150318200c1100d003022040e440d0208540c0704100407040201904061344031017000d07225440d41503541c5010b07040b201700c6041d0f40825603800340b030040c3c0c86540d2003050307188502c4043d50400110b040400d03144d40031011f0001900d960483c20251507812403c1040030703040400c0b0f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 453215053 1250 453213803 453213811
    0x30509100203070807082503020a090e01242604030305010e090c0f060405060f040f0807080312101e05011b032f060f0a1406010c14010f14040506 64
    0xe41103240d468400d00151000102601420070400440300203444100e0326004002401c607961440c481907541440d0081c080e41c00610080c00103817034000700155040071844442e06860708680f2000c1d9010541041180c1008580700070b50422517200c00100d1081211030080c1c0c0f20f006040454031042c41c1038203010b0103442c0103910058a001e0030404014920340042400d0b000c1550450710a811105008001031950141b500510390000c00020104501098000103008544544000c0001c3c540c1e90f460140d11610705115900c2c1390b03002040500304003900c00c0c02176580068046030850226440780400242d000c401050200e00344295881401103682203c0300031400790702401c0c034074010180c582d0004c100c86e600140c00c020381c03058800003400424000f40702c091030520040031a001c600d0851110504140180c4904d00f800b0300d0240700909142141c602c0e24070610040c0c440e1640307881180d40d1945140c4070b00d10208480d560f0750041c000da80c0058003648115510140e184052800c1c1401c1c00e9040404c050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 453216303 1250 453215053 453215083
    0x32a290a1704030e040c02010501030507080307080706020901020106090207030201020904141501050705281e080f07050a17040e0c07030c02100207030c060906020d0908250510030509 80
    0x1006251115a202a041003485058a0640990b403507a141c02e884680c60a100c0d558801c1c20210107040c001d6055220b00e04803400b40e811a007209a90301101500c0b4482c0f41c4019003031900411048000c200f543e00140389509c0c06100009095540e540c2c42000c0303810900c000c500507500050000345515090054490300c226074810084c507402d11000d44161050422802410b2003000719041c0140201842802400103a201007146106400071750003000548144048130b00c41c00051840b08240d04806c0031411050344540d140d898054500204911a0441c0e502211503225032203101700060720a500070280110180715031610b40d030a081404540310001000650781c0002031160b100801c1c0e000c1c5c1d0300b4003510380544081c00c00070310302441203040100d681c0024001c105280000101c50b42d20503682070480e1415800d5a078016514403080301c40f500648079940035a402916a480c8130041f405141c0c10b543e010903041d218103a641e1005c103014080311284031011035030b100100031948505000400c140c20000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 453217553 1250 453216303 453216307
    0x103050108030904094403040206090409141b151201090213030b010f03140f0d08090106171014040b0708180316060b041104032a29 58
    0x4980540c0e62805010002842a51140103040500c211307400303800c00003a140407895958502070b50f10324445404a60071b0403140004920822031182d090400e0320b000b00d50003015641b41100c8142008003410744c1d401c0a03030356031400c200c40c0e0941000801056209440070412104100d40c60401c000c0303240d0045100a80a0300704000300844102d41603400d0f8113486c41503c0040c0c03240f45a00b1080c0d02012550401040300030390703200100e01c2120382c14402040383d1140100c0104442d2041d11140c42c0d00d01c1c003100120603400307502c8080c12036000d4178142da4840342640000900690710314074555201e501ea21031910329086820001140d110311f0141100e03070400e415030a1700301d007820fa44242500740c004002808010919000c1046008400302c0d001415100c8000c903038440c10001c50103201d40c86421800c0b1000c500c3c000c1d518080d0300b0b26004a129000001e000a4101407851325007519015140c9041c2c0c090044010160005400300d4030b020b000f91103403100ca95075146041660708103110426051150350041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 453218803 1250 453217553 453217559
    0xd030b030f0708122808100605090f010e010318030908061308040e150a03061401081605060f04270606080c0a0c0501060503120717040b0702010804050a080316030b01030501 76
    0x30010b9a0240ca0000711031310707a0344440b41c1241d0941c8085100c801102c110410512420495001ca6118080d070b61500d44004071070b541d03a001351054030800c4083e5811411071740c82b00c2c60660180800d00d00740e43c410304001c5001c01d075502d42c43c1c5c40318000381400c5010032442c40061090301001c0083d2503100c0e03201c07449a40c80e50030315201c50015000d0381c03048000c29240e031800146244e0386544c0102c0c0b018405094600b0305912441d02e500607150503900080c011a13a400006140f4000203403910401d00103540803102e030ba08040500059a100da4802a1120741c104070020b04910200070042c840ba075aa102210500700e00c2e504101513400d40c3d4400410031a044090008182010742190b000c4815810300107454240c81c40c210b0b000d0304d1184e0025505000e070144080c0840d0f0107074001c00a0520070b250380030060520002106050096002c0c0c840c242901f0b12002c00154058a08250000d001e0720480e0242c021a0350384040701c0c7c0c0100c507003807501c4a4136540459001d406006600540809080501c040d40c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 453220053 1250 453218803 453218819
    0xb090402210c060334080105010302092107031505040b060909011d03090a090203040c0b0c1c05190f020d051309060f030215040b1e04080d030b030f07 66
    0x10004510031140800e003100c8010308070040092860000028004607201e01e8580c402040c0510600050030644d049000412401c618010000c5034410254480503079503400d1000450094001c090456040798010384003e5122001a9101c24810014401000c07c141186442d501c0402c1c441c00b040c00a50900007417200080f03034005403a622410a84000000d50354009aa90240426072460320b514544101094011031001c8020041e007841519109074240d50350007001c040340310031503001d0000d04170902c0903c03031903044000600084100750100c2d4a43c3c08cd8004001280d012005542c0208400084503000400b02c1c00c0401ca2854940c1400d6a40b641a040060340700ca40c4c0001e50400c100c0d0020b10750b0b03d032070b10640311000586400c1104100c000d03250300340f180100b007060106070b2044a605100b2003601c0c0c903081c11141604c04000009080251680642d0300e8420f40400300c02c041740c018000484c0c809010440035061030107a82d03001c145140d080080c1404c00400c16661030107900840e800340001d003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 453221303 1250 453220053 453220069
    0x50312040c050111150403170901060f050307030c120201090b040806012c070315090e030409110f070f0201030b060f071a01060c030806270403080c0a0906051e19030b090402 76
    0x48100809070b08942c2d650315046442101400108140381c1230b84041c41020001540b058040d04d650184014603035458808041e504e062502c0002d1009010003420b025842d4402c0220110601c103041018a054032a00c011009802c00e400c985841da000b00c004000c0c0201c2241d4510f84c1c1113203200c0c80302060301046980401404014442024903440e840301c2420240e9003095040103005030601040349218062840e40c496025104000d029030034081309200140702c5c0381c1182d102201103520140340020554070290f00249144050341490307640d064240f11902c1d0074005041c1c0344004003480c1c0c7d88081c58603001c0c10100c1c0400d0254411807804006106607030b0020015803c1d00d4050801c80e00c16500d108c00600c03ca41400511801400d141d0014954406411040780c003843c400c2d06c804900c0c1c2d85102c0c0b40304050203085502000121410410440503014600402040b0078200000e03000303503400d42244a00c0da00c0420042c3d80071200480800407154544208039044134202d0705603559081c5900007803404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 453222553 1250 453221303 453221323
    0x50610120809090612010f0b2d1002120d27080f0d0204050a03050105060a14090f190c0f02070504060b040311120d021605031f0513050312040c050111 66
    0xc1c01042c404204c00da40d802c05101d145a25401c0240034441e0300030301c841c000e051407a9000f8005d1881910f4403000c04a240000d00082541580360202c11203c0d07002c020034400c00c0d03400801580681e180c00186051840003c100c1d000320300303e000c9a03c46401203840400340300b4240c02051202c40603036030300c0003a0f0b44d48200c071203100c11200c9498071030031a022810000e10031603011130b41c03140b1115000810003106401c00e034840c1100700c2c1c0644680f50396101c1008510740c40304903190b004010400017040c00783c0402c8102e801121035007542c1c42010309400d4000482e405d0100060100f86401240740c40c10f5410007882000e040d050741c09000a6142c4503e0507250700449c000102a181c5007140f050703854607140201d400c030568070000c0b00d0841c0311003032021b91100e0300521400741d500301071400030481d030030001000c1006040400003c03a07200c2003030f1605170007018090920100304406540c0d0402041342040600305040c0840004000c508181c94081c0b20b001c41940024140305070802401c0d901c5001241c1c0e00e04e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 453223803 1250 453222553 453222559
    0x10080114150109050d0f0308060616020d08040e0403120e030c0a0206090613090209032b0804020f06070b1501090b0d0e03070f0803070324091116050610120809 70
    0xa2401c0d9005842003803240d040b1603040300c0340303244035401e100218120b10503103402500c440c030490700c03241d00f84122403286c0540000104284050b050050a12130320b160f50490055403001e040540b540c45448201301c05032003d030300242441044406400c80ea10440088060500081d4604201200d502e6110007503e0340c068820500400c00004540343c80081f9010105a910b54565040e15603003454000d40060320858024414001040c0051400c034804000301d5031500baa1512440c1150000c40762008001c100300c2c0c111141e542100800c0c0c0f01d0748040c100c8140300d11031222039450445070303111684001915140c10002c1c14681009030480d080110758030314010500c04682004400981491403158800080c801d000414201045c4950000a13601a600b20b035010300202207100e0095508001a00d1000031081043e0420800395456620a4940340b94600205041091282510203e05078000b4281c580b07412200c01c001c1849980c81145010340704d4500c849150303403803944880d0b665004042000e40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 453225053 1250 453223803 453223831
    0x90112020426010e15191806020309010902060d0c030b180106050a030e0d030e06060907091e03020d0f02030f0604050709050a0b030a05010c0f09050303250b010e10080114 75
    0x244030b2000c1d08400e1541c80140103d0340644501074601c80381000841e110096121110032024241040d0b00840030b404070641d001c079580c0c2015850f820025800a01390703040710f640e101e50070001038503814054128001600750004514030b441d100034007a1400e00e010144030307401c03040d504900c0c0c44800d07102c181518102d1031300ac0d45800c0d00f8081a0020489156920158850794490800c1958140c2204030507002000c04d4072010780310441448050381d0103036030340d101183c6082e40c140030b45001c0e40710301c5d15070340d52840151451654a4010030030722000b80c4800d0320032614070b14010040d407e04001c11003170820500001c000368034043d15070944a02e0980140280c0030307190404108000b00940002003110b41c0201500e0890b811450700c1402480c41c014008082040d01904501040c0a83c202c0003c0725409000340d49400b0240442c05128283d01c1c05003140c3c0011220303c100810461450130740600103a9000220a080040180c054101a03034000d00e40c6038100810b45550404454075141c0024460602035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 453226303 1250 453225053 453225119
    0x3020c100504050307020406171b03160b0315030d0f030207021f0305040b01090b0607060f2c01060e0601020a03210903021c030204120b040611030109020901120204 72
    0x80c14000401048941182031900740000e000c2c000c402042400d200325000c21259075a00b080342190100e0b80c0035140d464001c80c040b030340c0d0f0f0030306c0c048542030250004090340d0001c0103038042d21007107004d950040c4601c01030200c100612000c1030351400303100c9501100100310301401094010310546141100408058011075914115110364a81501140607040f500e82565484200100107000440303099a19a02c3c1c0c100024140080b8820740c1d14030003020b4952403603c0081d84924000d00414000c0304112640d8504409408030110041042e92071766800c0c004503124903080c002e086d43c406410282040b01d108d0144009682c0004014802d85c2d41400c0080d100007a1035400b8591050240400c1d40f580d007001038001c101980828031005d1100d49906112421483d43c0b002c40881c0554043d884071105400c403c400818142c10100e0380c0944a0030010130410041c6550740890f402c282d014500c15500800c000c0c640703603002000d4070101c40c50548214102031030301c40c3c180300202d0740d40040d9180701c81001c948 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 453227553 1250 453226303 453226327
    0x1103070308070b16030c020c09040c080d0504090b01091211040e030a18140901030b19021207022a1509120c10030c05090108061c050c040e06090604030302 68
    0x11200550700040741d5900da40c0d003810070100d6102c0841d0780c26030240e03400d0b42e60351340907010744030300054465160b0092420f01403002c280003036410301500c181c400748141603001540010801c180058100d9940e903ca0320b603803800c041038003542c0c2d04681890601184540510459110884420700290400c15410140602401050040020740c0e540700450200003050944160010b14902e4a214402e441050581d83c0c1c84440910100514407580d201c4403400c01000401c0c01c9050703076030f08984080d12102e1a14580c3c2c20480403640901040d80c0180380385c00401440503018802841c0c85120000e9011503145d03100005980d20202c03022080c40f542c81a007010611904070000d50b1040e4a0180000e081550106550766840400074085d40c4282142000e045005120703000c0d52000003117684405013041c0b13207000190b811140c001c2a054021344003654410800c01015244000180a00080c20f8a029400207100980d9070100e050100c5510550071701100d1000015910340c030070b03050300c0c005807620714811070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 453228803 1250 453227553 453227563
    0x607020613090515010212161e0b0103170a1707050d0e0615030a030801120206070221010b03030909040f020a120305192c030709020c0a0606050405090a1103 69
    0x401d400c1e900100116188110b50f00c110700500407003496441450b1a0401203a40703503001d0860368115036041c88001d0143c0c82c1502c40d0b0711300ca132080035003007105504641c0d1000004a040000d0701d00382c40c11401001808400d0500d00d039140d0070800031500d0704404d1007000c0c080c030740250814102c1003214000540590300c20000d940b03d01250301002c0c000c04000343e00456561506458410100c00c80b9005c00800f4a400540310007a164162a4145d503a0728081118503444014402039802900c02c00103140169a641400c1034807420300e01060048114442055003126021041c99010780c0c400c0104800035511490f2040d03105a0203440e60114040502c0850021541544002d000050a1100908054101c0040c285008042900c0500300d6549401141d00700008600701098501303514000c84c801001424094401001404540480e940e88403074500f2a03101540c03465054020340d0040c400c00c021800b58074005c01d82101c3c107000604142c000252107540d222802040b1003c420a800410707103003800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 453230053 1250 453228803 453228817
    0x10c080405030703030201020c0f0d0c060b130f020711030c0a09110403060204121101091409060315011d250f11060c030f09010501030804050d1b060512100e040206070206 75
    0x40d0380b0b04130360300e01d030180c080d410200c1c144280e030080a0401c8250500000d144806405541d1440c0e90340390107449010042540100903900900b0b9401c48001c070300002e0054001034480c0b5100140d542a160070040348440c0e004810a100b41c200710040261070ba00c50710f020055425012001854410aa0700c040051007070368401401c21340082000207010311050050440c05014143c01c400032441c2c0302c0112040a42c0e4003d901040bda00c54990380d00742001c1c900c0c01d0f070050b40981200c10305900d001800700440401da0200b00b5402000c202040503c242e040c01c507404c0007080a0030359000f4843c541414480c440c8400e128200080c080440310f000d407044092030700a5241302c041c3c070107609004520710016482203e041c4c68000b900408240c80c50700501c62141202d030803035085420142407404002528400080c265072441c00c0040141c0c8445264525900a0846403142c0d44d40301c24034040300002c02e20042420f00c1c440d101030001c000c00c407076848101d9030240d0b04544059903901c0610015007a4002c80f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 453231303 1250 453230053 453230059
    0x906040c030e07151e021209030a0b0406051006020309030325060c1218020f0103020d0b060c070510020d0f050313061503020a0816030b09120f03042f010c080405 71
    0x105000444d46294241d0020701c121035603e61007155001036041d03100e400f00c0520000164003038038802121a07030300000340001c000014190740481e006074071582d4810105035010f807152540c030400e215101140700d0580e00280442d00146051207600c4000948038040c0041d030000b10112a250015a40d00d06002244401d45c48502000000401d0000801100c000301000b8061441c1c9091040f2214880c3c41038030316a580102070078258160320004402035048a460380b40001d0321403d41c00300507541c0780003501442d10103000415800c1c0c034010410500e00300010601056400180684104981c84107107040d1040540c100544e0307a403a215900e10915200a202030001494030620084440360140040c0403a0b000700e914014003034480300c1064071b514150707100d00c0c511060600d0800000d0450b030b400c0d691251840050300c03015150301d4144005e07548024010901d600c0008104400c11869664400911003400030070420303001d800303200003017071920710180740e05014007044008108400d45080710040c00c000307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 453232553 1250 453231303 453231313
    0x1a090d06110d0506150306061c0e0d03050912030610030504080d14040c060203030118090c0302090f010f0902031009020d1b05070308181c030623130b0906040c030e 72
    0x100c0342d14010642501e00c2c1d4410340540e11712840d5510310320f064034004e01c4002c044501d4240c1c1400400aaa88000c01d10007580e0f0f00c6281c5056221820b0100b200311014640380072076640391000b100d41c241801c1c00c1c12400208814014001c40c1d8849158180c00701909003000551911103041c40c00d80c50090707001c035560250808c500a00000203030b1034864040d42c810511402803e4885c502a83c0300d0100b40905011044186203581a440c01600000b910390f0058889004c1180c4030f4001c100017041c11910845c80b42c030300382c1c010000000841d440b00010030b07200c1411400c505000a07040d000713640c94862480b540e81c01080d4403071009059885070444c0d8444000c08600c18981910241082d00450070aa01145001001030700c4a00a60545040c1003034000c0541a11070003004044203071480801c010080603515400413581b04a0010311001125039030042c405000e50034000c1002d00b8411000300e48045040180e018416280c3d41405038210070211008200009419400c074010030950241001500c91 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 453233803 1250 453232553 453232567
    0x50402131e0b0d0c020d03050c091e1e031603080d0902040f14150103020705071e1806052805091e0a0e0601170c040c03060b0703090501091a090d0611 66
    0x200d07034015100d51200f5000c4c4c0e601b138011000142c0840d5000c4900e07010200301000990040c1c170b0301c21000d61181c05d000c03c2d4107000950010200381c060044d80180001807510301a604000e00e41001b0000b40700f0850001c0001c114195a503101ca00d00450144040132501c66464800710b668a40065100380b14a05080101c2202c20320134081886080e1032000e0440e418100b011401c1d40b0a008441a46422030001d00001d8908484156102c1100c0d028900161010601080c2c43c0c100403018011460b4000011074038900700400c00404d049007440d070564001c00f28102c9080e4100040244c1e00316003044840a6040c0e0300e00c074901c880303040c0790b00400086034500020403c04070156440b2840300707100a03003200d81982e210707419007410805180160f082e59100362054130661802e40c00c00103c0d82e82c0d0b440c001c90800c0c0d407015404200d42205400b2008580144ca00788143e50703004090100900000348076038095002c42c104000b4501c00c5246072800317141c5a14400c0c0500c1000d4100d480d1040317403600d045544804c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 453235053 1250 453233803 453233827
    0x2160303090209060a030f0b06061c14010905070f120e030a0216120314031009050106050304020909030a120902060903190b13030f0305040627050601050402131e0b 72
    0x90754007401c0b0700c200041d40104a4500300204120250b940c80b0b55425405500794440c410645401050154443d5003080721900307032060195078214003c3c018401007080709c8414400568010305800c60300041d40750400b04440c40798400c10401008045082440070450b20700303d80405052241e801410910001815501980c0c0c001940c1c01c001d03014410f06180641c0725092040407002c41917014002500c2d51618544100c0094015608408401e482004007540c0c0c22510080d40c07001d902c420085038012041000354101126a16400174035003014600e003807151040a000d031000724941069a0741d40c2c021800071519a03004590450000908070303446410380c103218100c2880031a00403208803541501003030b940c0700d030810b082d0807950745038903038000742074207600c1c11401040018020307035101d034a0300e40301c10a000a50b981c0c184400e00c10001000c4800c41420260f18114040e44503602480c41040455188920380040809540c000d2200703500d10f4692128407995001c0d01d070003920603884005011a4205 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 453236303 1250 453235053 453235061
    0x1b050f0f0111070503030c0a110601030609060b0d0507120204020d0f0501051e1c110d1421070609051006080d030606030b090c0a030f0e01021e0408100b010302160303 73
    0xc810320024005041502001451401001d4004043e9402400850f0514000602400803060343d80340020180d2551801d107403034001e0aa0050b0f80d060744c0c0701004401d000e01c034000c0481501c2c040c1c8038800d0002280e502c07142d4801c020310a00b8111680802007004558036501120f10f00880d07a80c003404a4403040d68801c000745002c0c403900380314002c0d07408604100841902d0702040e0800040c1500ca0950001380110490640248216110038200e52654800c3e0303601156941c0303190140c140d403454081260702d2140340414a1a0007080400c20007540e54091441c0012522460350101001c2986010f5242980c542880c140e072412025081110218207158001a800c00f2000307a139500303010459803000b017541200c4e02000520313042407080f800503504120441c003e221411040c40c000503448000010003044990144c0410b83c1a500040d00e03280d2050462155107910340b090300c0040c6042d250504071540c8041c9402c0404200d520703140c4498140e8080d03819111080c182c000503007407281043ca0010020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 453237410 1107 453236303 453236323
    0x906190e070e1807081f090e0f0d120c030212070c0c05130b03011a2101060b071425060c1e05070801050a0207020f011b050f 55
    0xa40b01d43c1803e440c14015410f40346024100840000c148034405031030b011440d0171041031041d4076a0b0303144411003140d400d000e0015201000d0008a0f04001c403084440101d4000c0712a6103007102c0d0850541c000f150240c0d9030800080900302000e03000c900a401d031040c41c54928600280030640540300c02145240a802204134080d80c03940003a94181d03000800c41c00154030785402d07030043d0509004108828a0002101e99181904804500540c2a041d0720b0074611310070400d800003101003907101c81c02900c041030829950f08020700b0518558104600e1002052142115019803900710324a0303807904020018500c80500c0c9004003c80700f40368094803d591039070003548140019980407170100f080901c01d4000e030071a6440c0410f682d007100c1008003080e80c91401040920010303511080d00d0043c0c0442400e203a480c000400c5540c0c88004070201000344a84158040c00c80303241350000d009006 = true := by decide +kernel

theorem cover : BRFrame.Cov 453057553 453237410 := by
  have h0 := BRFrame.cov_init 453057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 453057553 ≤ n) (h2 : n < 453237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
