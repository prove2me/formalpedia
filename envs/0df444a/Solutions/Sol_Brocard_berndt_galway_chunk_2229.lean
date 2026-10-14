-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2229
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:03:46.892989+00:00
-- url     : https://prove2.me/submissions/c077ea9f-ba01-4402-a65c-589af05bba47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 400719424 ≤ n < 400899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 400720674 1250 400719424 400719439
    0xc0c070503100b04110403110622060c1b0321090b030c03190e0304031203090209010b090a080c13110705070f031101050702030c190b030f2512020a03022503030b010e 73
    0x8d9008011031a8800b00035540d0000c4600c100700d41c44042c80e0150720041019450b03821041d0400d140210f04040c10103046144600748800a10102d41151211041e480e9943d19804124090800c103403a2002181c0c08800701c00d03070000c00c22002d003005202460040c1c0000d15407182a11001c1d0b140c109540c4480207421880e40240400c0020841a6490900c0c61009003000900d02800350041812420260410b900103840040c1650140c1440202080184043d0b4054020060618009030102c140058584c000d80e480f00f64100c0e14000e980c0c115507806a05c4000c440340241d0350f603814502c894003813106680d040a0b00d61001c2455010b0411100010f50080c050030b4140c8500007001840c1b8400365100c020100000c00c04603401a041d8011402030301d000007240ea86142040d50480514070f030081c080310f190640d83d0038400c8583c1214200307544480d0b176000940c036007101d10411402030003440303094103c1002201c0000d200c140c102d0301c2c002c0e80700c1c005d40d81445000c0c0c00d0001902c840d02c840c0d03d01e9410600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 400721924 1250 400720674 400720703
    0x9091b010503070509131b0302071109060324060103060902040303201002070b0f0702010b0105030f1b0a050702030f0105010617090109020414160e090c0c070503100b04110403 77
    0x1048000710350054072404c006081048290100700c0103084503805d003c101740da891031500241c541c40700300c10b0f040840d8030741940b0746102a51442c41c1c52540052280c040ea000b030010940560f0309008402e00d02400b58409420b001040035110804007068501c503011929001c40422603003e2402103400750703900754451016503100400101d0103600d649010b221280202420000c40440d40d0000b0040d95001c1c0c10324911a06022010040b400d8005e02840c0545e85003c004900990b0400c055a0b4807060345007003d0903964070440305594140181c140c3e4030700303840c00007426040550000d000d00000c030f00a40c12543c0030501c1b902e0650880303030207010380e0001c00c1e4041e0340910709451009000781c1c42240c0d8800415641c11a03400f2a0560705c05035512440c2c8010701e0200100018259490710508100d4070303110144202c0e141c0802e01c29500903140002d40c490005510240520400c8104020140602211900400c480e00380d00100340e14810680b06a04103c2944503038030340175042c0c80903217030030007001d011814 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 400723174 1250 400721924 400721927
    0x80a0207170903100203070e0a080303090705060a03020702041506030e010c120209010507060c0c1a010e0f271e1b0d05150103120e0103020a020d140d0e0c09091b01 72
    0x4010b0300301036074180305141007440710080b01e002035405a00161035074680f8241c0001040b00e124955003203200d00b036100b031040081c40480090040100d410680c0c41c81d0b5036000030a4214060b03c41c651010303401c07074204080d00b441c42d18641310010848109640c108003a0311700700f01440c00d89003424000c000007176004c4945401281183d00a02d8151300504055140c4030950360384000b55820345055102003080107030b03683d0601040180aa8004068599512940d1f0500d04c00e040000c602400700625203906500080c00241d1f0321800d5a060a05c0540c09600d09034541c1da0a90b680d00c2c4400307081e541828010410001e0358000076000c186ea0140f108500c403100703200c0c048c000d5442140340161298400e03118203a02280364034401034003941c080c00e4008146000306002030001c04e00540158101841001028034281c1e02280e000d0903811140b0f0700c0d182d40ea0140e007403a0030b1402001c24112040b0f14080d1b910b892942d000440180c81031040c0c8010341d140d0b560000441e00c40f03620300b8055141643c06070923084d456 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 400724424 1250 400723174 400723177
    0x40f09050a1209090513030e01020703052802060309010e071e0315020f0c0106030302120421051f0f061d181f0c09090b03030403020d0f12080106080a020717 69
    0x8041c0f86404280c0b81d0350788403250161003064a18441d80c2c050b00b1105400d05a0208008003070700c40030b000402c0010304d503aa60b03d44d15402d441102d901c0c030300724240c1c1c000c03100b41d100050308046400902c9143c0740c0c00e041062500804000c001d0f440a8400e0440c002403601075601d0310580c10400c0e075002c0309003a00d1070b1200e41d019982d00280d4500c0d5907081210700c0e50146c401000e400140380c607000001e485421840c001e032410441841d0131696040901c820401b17200c402c0c5581e505600040c00120011911b480d14030f1030b054103000003c5280311a501d004141509541c041e50303108000140034804c42e0b0f5070f0305135501418081e10000220a41032000261004070701c88000a40008400c1200c40144d103158041075101070500c0640d5110f40c54584d13949e155075014008001900306200100203c0e0080030002c2d581e4491440f0082c01401504014014002c00c42e1603502055000050340500180081004007040700034011000450341c4000420a485841c2c4241c500050340007440c2c2107034040540501286 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 400725674 1250 400724424 400724453
    0x901020409050108030309070914151203041706160c140705030303040309080610061d010c0b0103050102190f080a05180d03020904060803130b07080c030a0e040f09050a 74
    0x15902040005400c01c03107486058003e1500c6030286889041c400c000c242400203d60040e4811400c0541a00803404103040150300842c60603945030b4030712821804030f40d4080f01d02c1506d40d070f00c0c000898001042c4004141c10301a404143c0161480d5554030045460b03800005900c0d08001807076a2040030015074000d004403040058482240c0700345980c1c00009185a00840741100001c0121000700b10400c801c01007150044284411a4a101d00f000340080081d03580e010030104580c0702942c01000c40e401a5010b00d80030360082111699980c480c00d00f24040e42c0314082c60b4000b807007103a086141300c6224801d03090340400142c1e41c44038982c40701c102c440e010b428091720080082c80c1c0d130034001a8000080200c1040e50000e906d000d61609100000c00007110b942d90b11035070943d041000302c002782c00b0785200c20f8001d4502c10b40c192525074101c4d08140d8454085c22a030305240748000549559006c1c1c224180520807141183c080c080c1c1e40c000800142500c00b41300303009285512541000d800105c0640c0c00998 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 400726924 1250 400725674 400725691
    0x33010509180703110a050102010c2102090d0c060e0105030714071406040302070303020c030a020a150e0604030809310506011101090f0203060f09061302060412050d090504150e 77
    0x30a9144103076214140105548222040762803d0744c02c00742414210b01e44c0000701030900003000103841808018200c10186220101c070f08180c0b440b0307074600010310781c155508848051309080713450801e0700c0c090032181420f010350700220300b118403c412158071607003c69115445a40d1a80500c002d080c4180c4515006140110740b002c100300c0b0740041a01d002c12410344034501a5000703001c031a195040180c24146804c08050080c0c21421001000d40c4900c044481121246800700004109000040311100460b40d00943c0c0040000341c0041840541d00240c803489004076419200c50030700d411912005403805101c0c007441c4c61082080320017110310341d01540c1c0c800e81c1810000e0030182001d40580c2141d044140480c0e201d001e1180100545c2010031186038807619600380c01080d800c01c0278074241d0350140103246100c400d403462008802c5403a00400e40c2d000f40111038098001c201c480c54070a0b181d02070001112b0014080e90b100280c01d00e010700840000f120740042c0044510f040154075221400300a02c91403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 400728174 1250 400726924 400726951
    0x803040b070303180f020a08120a0813020a0f0e09030310030311070519090b15040e070504080102030c19020c0906040c110f1f020406020d0809010e07060233010509 72
    0x8044d65510751040203000d01c02e0b0240c1841d061544100940700c0699008042654000d41c0b2910355100ca500031141200c80390309040c05559658125408201d6103100002d40100b04018005400480032003c5015161441c94103e4075640f0308040f10381d41c1c002100c0d8291807081c407003000c2000c41e00030403091594039101401c0d0b44d11541ca40e008501100b40e0902e01c1816102020010807a071010f0b40b003100b03840c60040b0b405900341e50408105400c180640c0c040c140748860402d0203c0d4246000d40111740040040781c00070343d120300d41070303c1155007070f0000721100443d005610316503841c0601c0171802140803140100030004a07211481884010300704d100400d014450300c609032601c5031504008401c10900060018202c94801c040d103401c0220203c8144241c4a0062209202c00c940100f542440d01d021454441403c1e03a46440840c050700c80e400c1242a2070040d82c002251455001c00c84000707460903686003a16401900460320560f00c00c07002c80c00c1c5903505030f00c018072840c900041d4a6401058803507015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 400729424 1250 400728174 400728191
    0x2120c13091a0c0d2d0204050901030b0915070512090a020a060f0507020d08030402040c1704030f031404050706090b04030507170a0803070314222a0f030203070905010803040b070303 80
    0x490031203070036825449002050302c1c030b080894144682071000c0320b441d032817095007002d15140214410703203010b001c000c0010a90340000359000100700410152070340308404c0c1441d58204600c016100b0b034003000c1004d00091081c000544100b80025680610540c06802640c00c5071805c401107504a80d401c0707141c810400d0400141d405070b552003000c03d0920f8010400716949040c90310402044034030203000c19080c0300780d0182044004080000d00350740320f501070403d4107050320b20319011401070102c200f00003242d141520901091050000380e08058500707d846400500e5110b140c554160300452000074400da10072542400b000b115030825180003403100703044074240c030a25551666a41c04c12292400001d6407008001c50801101c015950001c2040840312500031000b22001060159004090003024030516840100b1801040305481cbd00c1b101d1040705c3c201c5445602e9280701380d5852200368800d126007d000f08a5041d103100b103c0c12030340c01c080214605403401440684a0300700709010350a0503500d03040c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 400730674 1250 400729424 400729447
    0xd08190b0316030b01080105280905073203060c0d09150608030c19030c110d050105100810140112150f0204030201030c1d010311040302120c13091a0c 66
    0x82c000a58070a803080d401940c1441000c40c21100001e000203100d00e050514502551801c140314116a2480030002c01c01014504141c6d00c0d1010550002259410301ca0b0312030100c100303d24455a900600034008401050b0341d408069031554242c80c88001141e040190340307c001442d5008050141c407421190750740d8880601e0700c00c02c071502540a88416080041c100c0134440c02403200e400709151003500892525002d883c02002c0000410009143d10050308180516aa80084d41c00b1f50342e50000084c0641c0c40c107484010001240f6100c0d9008a125100311052050203d00483c00004070f082d042c0c1e400f580c6003401c0c0c1039901c80074080a4448a608180700041480180a002031b021140000580d4aa1462000404403110140b0a50400407a528103003035000103581d680764007ca0034a000b00b4003054803030914100d80704580c07000b075201e0348100340390743c0c19000810400e900e02011181000d000c1740b0ba410400c155600400d00a01500c500304146c50b02600d140521500810132003480c6003880c0c1c03103051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 400731924 1250 400730674 400730713
    0x3060303051c18050a1403030c19110d0f0306050a0b090d0f05030304050a020109081b12071d040308010e13020405072c03011d060412051903020c0d08190b03 69
    0x425922071708141d100500b03200e000c004015010359040010341c5186040010081d8074082c1403000c0d220644200840e4030b10b28810241490848402802d03140041d058000140c00a1011906640030905240000400d4901550114200c60171921510302d000d80b1b940c00c0041c480308915003102d5058100700004085501003003e54071440c480c3c001428030302d469000140c001c07207056000120540c062459041d01f00c11013110f03000c0114041d25200c520715004004181402c03031982103500d8649280c00380c0c1c80d51a11452505004134042d8aa4001c140d80307070300001c0b854210845410b6440c0044048a400508055018990001652503d502940a140c500f1030780c00b00d040120b10b20b165500203841520f40303000c1c4144512001ea003015809101d00400d1100d803104402400581000c4800050202e4203008004444840902c19004043d080c907c0101034000e40000c1a4004a03216240d031956401307000f480c0c0f5600458400c400d8420300c440e0780306000090325041204981600500d81c19174401c4031002c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 400733174 1250 400731924 400731971
    0x102306040e010801090201080f0c090f0f150d0501090e071a3009070f0b0d0603060606080907050904030507150b040606030e100c080103020d03090803030112060c03060303051c 77
    0x170642d45110b0000400c03500001d4050754100b5104418050b00308400800c42d0103c140546860340a0010140000c0c40100510400d0341c004d0701c00c0031541000d55441c0010100d05583d03840400c1640d0f261004a01100c1c5081c0d0280081d03803016601713005242a002c881020803103002d451034a00f0b2101d40114020405090051000750803248440800071124454946e01c204090000c003802480c00000d0050084d441c46a90258900000c04010304071f1603801c80d0000d503411a40c18020b003655104010b041260031905500c05004115002c1098500030500c24000c07901030345c0d5030303043c00980d0300d80058011008101c3c904c025911100c070021906c803406040002c1a0036180043e8144071154050705081c0a41401d251075031520f404415400d03088510030303056903010b0b0703004550259940790030340d955030382034010640134400440009040d4041440a5003954070a0405000c88440e42d002a42614420300008007c22070610841180032440c0c400b60341001c0d514080482e619005c004481215403025 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 400734424 1250 400733174 400733189
    0xd080c070f0f0209181002070203032503110a05060c160c030c051318030807020708011a04111309022b051b0a0804150b27102306040e01 60
    0x4042d03800035481c01c0050140e02c25210480900225181c5060640fa00300300c0c41c503120141e40c0800c03000c0954408009070350300969800c1c10100c1011040280e030603481c804400440002d41110040d0f01641c10110300c1d9010350780d00100074161911039000b4281c1c81c1e0088051400c03c410010540004205039008083c0207500840c1150119030a10042c404011100300203440c5003820aa1304021112005026650480d010300d003040c0c5a4840500407411301e00b055115555542c28406500301c1e4028480304895450340c100c40820040030b04a500350344a0044032901118800e21741000c111410b12a0001c140f142c0b601c01001c4107030010030403524031724103460290300c1d8180c0c1d4a108004002e01400c2518041d45520254075042c000c41e080024110103000f0401007001e81e4000c1d141d562508660000e4a0402000788000801c1e001001d02200c80a69920301c03199400240c40401c0804110204100540f00303040b1301d18189a07540c01c030000c00004460141c41c0c00a00030440010341800b00c1c2c00c4540070b8001d9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 400735674 1250 400734424 400734443
    0xe010c060c030f0e0d020613060605030303010b04050102011505100c060e0d08060a0512100902150309101401050607080f0408010204240806010c1118070314090307050d080c070f 78
    0x25030041007210102c13807140086030b2100c0f84004d01c0c1900090545c0d03000c0c504841e02003d01c0002d1a08070050400f50b440980c061001000109241d021079024006580c0d0030790082000c030603e6a00c40c40044020704c50b07290010781c6803142d0300c240c0c2d100b19070380c0f111540100d4002c1170240710040740364a81656501074400007058882400403e14000c01c08400070401250800c1c905000070f441151140e030089005d000711039840482ca8110340b105422025480b4002c0d81c0240c9030303c0c00301d200d99244c07881101d41004042c907045600302240310300481981a5400a4000c601f80a01d69a564041c0d501c00d60b603034032244c10144070004600c5000d000030005007410444803109141081400300c10402e04008842c213000407a002c00013944d91101102d459290880119880b0403209000300e000310108080c103c24002601e4200011540c041d00007100d230700700040303003c1d9071a81c13509101c40d141d00a40e0703001011034000408541c011840341000c0b1390009164410207180214643d51002c3d1a41b9404086489118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 400736924 1250 400735674 400735691
    0x60c010b011101020406050f03041e1a0f190b0301090204061410090806041e06140619031a2e151e050a030216050c120f0604030e010c060c03 62
    0x2840b90072012400c2d4480000e50501e410008054842d004041d000318071010040700107000d0185442480061030749112a000640069090907280c9586050604040600c1a4080b82e0344a0f814415244100184081500c0301412042c2441c042c0210003445945992620306510260380d50340300d400014421a1150210ba01d10039080c0003c030190501c80750f05000401d4800c1013040d00100301c2c5603015034000e400c030146089032403192010600342000501454030b010951f01000d13840d03c0c0c105001d0882100c4c0c000c0c02529035844d8440d00d03002e034000207102e81c01410901c0400c0da150751000d60044800e203100c22240011440d141c6600c80192910070f03500184d4501046100d07242c80c2000303403500c81880c0c8016042e86260325203420b08020807198082180006d07103030a40c107100341c6c1a100746c41080b40e0b100b558450700d0309100c0d544500343c500e003503c40e462087c0b95050301c1c0400100d164200100c400900341c141c0d6503403409e80e00e00141d03002060510860040f0400010010300c00c2e800408011f480c0060440c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 400738174 1250 400736924 400736927
    0x50906120703051e010b0307121503200d0605060402090603040b040605061e010f03020c0a0303090606090204060918180305071205091e1c050d170f190b060c010b01 72
    0x20707001381c9820280209500c01d405a0110b84410384c1c15544c1d08640c095070703916107050494814000c01d6600d841070b8a4011140a1101031090301c408482c0600090421a021000d8003500250400340c5160300c5903000d804a030001b01e10341c000030740c403403001000141401c0076007010808a500c01c42d0201c0c1d00f10610403c000c10444248155900124155554400d801c405091112114401001241030014421011400354403a070111030705049030806840101c4480e15005c0e02800a09c0d004651590410038081100d40d458407d40d0704070384d041e60b40d001d501c0d403802c0e42091100d9070540300a0f40c0e00e611001d0454640d542d281c0c9008426110356609540e5018900300100701e41c642c0f0351a0820071108202a4085640c0e44e5031000007030310321004105060040b040061030401c81035446507884c0e01c6041914050040104148100e82030640303440e202400c0c9000052280f10782191003001016040001c2401500300c0310110340132440120300050302d4241ca07400500550480419502140e440b1101c0c80103a5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 400739424 1250 400738174 400738181
    0xb07050307180b0a18050411070203070e060603011509030b0103030504050f01031e2a0f09080106150c02030307022805030109120f120c020114060303090a03030e01050906120703 78
    0x104512503214602504019400a0314800c0c000c50f0005c00c00140010041c160200140078020000140308100700b1880310030141e0070360081c440583c4130380900b08002070101010001c0500c1007100502c82480d5030700700701503a44144520800d420422081c1403000c000a441541c1050103540241c4645440e940b402c410031884080301c0b443c0780d0415042420b04495040300c400074800480c455132001c02c0417008e030b00d01800c84001e0100440c42d80301805000500d0b07a600505058000c240c185d55407840c0527112140c0509071440d501c03c11460001d89030f03641031510711550507080c11510003001d407460000a900000d444840c2c0108851265071540b03081c450302400d4001a80003000e041d002030101c064140c541500161282900c201407041e810740c600c046074440c0c0c440e0a00c01c405858100040d13400841c0c02030003006e0580c40e2440c501c0b1240003040140ca40007080d10004032000b031121025904551303086036407044074000c40307045c000d0500007000386a5030b641c0a4180504030b0740200d4600d10f40a20000c094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 400740674 1250 400739424 400739447
    0x6031b0c060103110402120402011d1f020118050d2f0d0f09030f08070501020f0304030203040302041116114b0a030807020d08030406150609080c090903070b07050307 73
    0x40c0e104000b9900b503000504e6005234031070b40909210348041c003501020001c0e9400340000c80d80c41004210550610801081c0300ba042205684c001c21a02040c524041814003000b48060940c0d07000c0000a140c2c6071140b002500f035802d0b030001020301d40014080c54074228503903212002c1603401900008945c2580f010000d001c10303480b4035101d601a499030b20381d0010114004009400b034000041d015050140035012906081c040502d025a0380c5014240251680c1290208038455828103409117000d41c802400d4461442000d0b118651822032540c680b000202481c9040740c01c12491010344c03101442e00e009921500c00810300700e414a4065171381c0140c074018620b60740340081214948044036130329140b00180a49903c2070760b41e565001c450000070400690108018019180042044100556a00910b0800c1418039983c0142c5440342416203502da0603000b03480c1103621814402d04185413010f2255000344401d02980d24028042d220000e03003040c100d6411000c1380000040c01104c42c3c1c000c5043c0d03203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 400741924 1250 400740674 400740679
    0x1e0f050a02031918170a1d0a1208090d080304050106050102010b0f06030703140c0a020c090c070813030f060c0215070e150708030a061503060b1e12070e01030b06090a0506031b0c06010311 82
    0x50307e0303c603613000130000c0c80076024004800d4006180902004048000c646c50484014407008210742e192800000d10ba10480702107415500f04100000c0c25401400b45100080e402056442c2c5180020b09203d007a4100034951000c1540380c2c1c0d410082c40108000743c82c007466520300786554545034a24081d19295580200318041d0707111070200201440c3c0c090a5a540540c0041c45a80c2d0b410590000c05482000d50405043c401340c5082c200e080104651000710100d106809076843c40340550042481c00e03604541d04c9010802c0c09618400320319188403445000d0031982c0505081864603103c0b24a0340c0c008071160039156940701c106010302c4071120150640418203150502c0440e06009008085000d007224407010203150010300c000c0c2034181001d90b10f264100f2101481d0070300d000d02000700180c554109880c042486c0ca0301008490409008940501e58041c10712180c1610304030600c207040c0c1c0010314803a0191011000d00c000070040708024110b403803041d0010122541142001d0041800c16046a031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 400743174 1250 400741924 400741967
    0xb090901020c4c15181503230f0d0806061c020904060308130306060b070b0c03090a08120f0123010e0102011e0f050a02031918170a 58
    0x60b14030000502155031026410b04500241184200c0810148600048500e0604100040e03228844035040507040710f03030f1848020340c58985e51544108039880c1c50780ba10501c4000305001e1010400c00704403403452500b01c404654018080e40b1306c079400c0154580d42a0840d400a031001481190b04c03044880c0c018408950592501842d001c03011b13101d0040e2001c01744a02c3d004a00444c140c0d40c0e96204130300071038210120759a20307490b500400341c603010240402c403051460950042080c60002d0141d45945902070041090b6480c1d0000c0302c0300981004082c60414410140b1210000340d43c0d50262840690b052000403060520540c1074030000c0050f0401c00c0c030748048503408075800080340102310b20708000303007090710718040c82c500100e014184070964a00b401c82540040918402160b1007413145140260040006440e152884070a0344400ea90910310740c954000e40b801d8030000c0350f1084284581a2032030300301442e1240e035090340041400310b10302000b00b404619091007503000081d542c038000c65184010f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 400744424 1250 400743174 400743223
    0x40c020705030618010b100203070b010b0f070201050309030f0f0d050603010207111e04060f0611010c0c1506030b070809010b1206150307030506100617130201030902040b090901020c 80
    0x2030f0b510580245a103100d1510341e258203180d00000e602c031108810000e4010b0f0800c00c00c1880180d13403a4080a0121001e0005000018400c3c000000f62075100c0810301c0750501c0c3c90310a80044940340c0002d01494014001082101042e1380d8a0004041e100d00c9146d00c203840d43d4480405c00d0440c0c000400aa0090340108814000205c03610005e01007280c08039044d421020f0001e000c098409403846480350400e10301540842ca5081040a0400f12403d5695511820020034481803d960120500340085141103400000260403594040074134070940b8400240c0300e0792034031910110103054554202262003403013408060002230244000504041d07500c281004404d004490b542c40e4002c1000902e0020340c00c021100c1d503024400003004541010840e4554180286014503544052060320085080d41c00b02c1017070305038840c4c281c5104003481d06942407040c1598005401070706c07982300300703e81c441e81d5410031640658562210307a000d90f010400044c0c4071086803200a04d450108440074400c102c0f0038600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 400745674 1250 400744424 400744429
    0x90d060f050a0c082a0c0c210d021609110c0a060b0108060d1104020f0f040801150f0819141617120d090f0b0c09041413020409030203041503020405040c020705 70
    0x11700000c0786400081d9a62101c003540d071a810029035544d556440302182074256595102c988101c0e814114013000d0329a100028542a80d4442c00e420361001c00700882401000b441d0a60707403203050070300f02c0d100300d2900d000780d0340200fa8104600f450741118030540d40c22505a8030b50707018040685c8030206850400c0181040e45450100d05140e5a83c6445680c000840d4042000030a00341c4003004886444103450780d8803044032a000c0c10942c0f955511a5100090001d5400d1680090200722191a401b81c204102d042c98215101d01c01000705843d1141d003450589000b000c02c001005074520528450360b080e81c02c00302c2c640c0040b032488482c01e01e20b522607503d2103854920841100c188000d40d12002070100480c2c540700580b0340150308050040482002084400009140100301d1803800b12000c100f1403501c3c820030811080c2c1a0f580c1507102c03815a450100604181d07110780d90300b60103401100d0406607144002e042e00d003032401c00c40c400280c0100b0108403030300306070240380c6414070940041e144003401d0201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 400746924 1250 400745674 400745731
    0x61d0d02100212130806070302120703051f03030e0901060228020f030a0305070506090304060806060a1809060302030c090912070804050604171011090d060f050a0c08 73
    0x9000e0721840c0c288403001c401e103000b0401e000c400b421a401c96a201c3c01045104062094a84110746142c081c060024070f005205c0d02c220340302c85000302e034145584c4c0c9811404400a1400600550307500c4404c0303a0301d14144d9081e0381c02301c00441c401d030781d02d80028159800388074460340107a10000956115902d0f04058001030503d04805415000510401845600010b4541c41d00240015054001c00102d01d050581c8a80100005402101180d10740e0700c0380b1261507981d10542c803454000a0551001c507903185403d500620300c1d000c2d10700c2c1140c1c0700750314648048012461540a10560340c0d448204000318281444031984004c0b00300e65030002450714041b41c40c2c40d544503280790000c0f0180010a00708001d001400c0c0d401418020f445240c80315280c00d11401c40d0444030000291900c209002c0a4407c00c1b1345c050071250260a1a1007414003176407805110008079440421101325440d04d080320841d6030280300c2c80e885441011408200e00b04201f2026298076005081081442c40c200e04000c407180b100070307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 400748174 1250 400746924 400746949
    0x18091905030f09041d150c04080c06031e0106020d1803110907050d090302010204090b03031c0e0717061602191b12110f010e3a0b01061d 60
    0x8010325030f10030500300001d00a000e1801003850825840e1309036001c95200107940060b610740340b01c0d6544c80b500c0389405200540514400d01d400390f8041c04000410742440005035412080103150200c0500d01c580503c41190f1090b002040181d00114541c0041980425550b44808440404411190541d02d0b1030200000c1d44c03427828000c00c00300000ca0040c07803242044685c002c85c1c08804101694843c07400a010754058410a10300508002c050030151801004440c0d207403115540300303819003214125001c0682080282e290b80c0b80190704001900398908041d502c0c0741e68442c0013400326131404204d82d4981c901c3d14201c4200319070140e0360710700342c40a01342c91620b0015000300520401e5555074004810b5440039406c400103801ca40802c54003003125002074103100308812640c24082512103030044549551000200703604c8010034000012014590034213003034081c2d4180c0ca00d110311468500b4042107103440e22084030034110307103401040100d80c003030b080c00c001001214482d603450b5401800202c4a22500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 400749424 1250 400748174 400748197
    0xf030f0e1e01050f0403050312240103090c050301110d0f090b1513020c0313051e060d060f060507060509070f180b120709060914040f111809190503 65
    0x701403612841e070107070043e11100700f1000c580c265100d403649020b40d04c80d045075000075180c0009074082207403a140101d081c2d800d0030004a50340c000c17100400044000c1e0001d020140c070000007002c03020036035880038000c0800b00719080f09450380d12074644042600302c44800c142d14034441e192441e940000344d400c0301029000301c0c4c4d0307019034450350f0003400002c1c0f0019a08c46508828510000f0b0455480c030020015000210804030603402081d43c1c1e6041c455030544d606278000e41064800c02c0492586402d038040c0030101803e41001175880d44901c401504882541c21030300104502040031402c001c2540038050380403900401620140d46030203051004140381380506078170080b25190200d800c0c00300354400d0400b201c006245a5003d81455070b1191640b0300d90081c07201c66070410300301044a05440c09034000310b001c0c00c100b800c002e5940b5194200502c17480d480842c0c9250b40c5052030300d29555021500b00401e250300d44080240e0400c008001e1401c0c0035a0b080c0e030003c100d105a00004034038080192026901c15 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 400750674 1250 400749424 400749469
    0x20c18010312050c0604060b03060f160c0c050d0f17070203060103060207060e01050708010f060e06040311011106070810080f101a030f030d0b15160606120f030f0e 72
    0x200b48090f1001d00403c3c20004085c0b04c1c0008000c14001c00390000011164150103403013081d10b501c070540b0700d0b8107021100b1041078059482c0350540c1ca44110070480902d030041116007107898a600009007501105101500e82c030450f100c2050031b002c2000811801150034007181403500c0310319400b203038136000d0500c40601000da004c6014014005280c000c0b6810f2a6040c0c001c1001e03240c40900500a180203000c0c4c140700e0300c403480d80402d800340901480505c0b10340080440d0300780782c55940c48000e20406140900e04000023003203440b20f010410001a801104140c0741e041719460203521801d030025042d0b100c00456888095510400e4038007082e00d4246030160080481d074010341d0301006200f02204001c00390144910010002c4040c408409040480e003003050a1120301804002c002c022411048050a10801040f4814020031024180d12400e4411800070615941d0b5142090282540d0300094035801400360044082681c006580d40700c00a40e414048000030020b00821184040ba10780340c01e61910 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 400751924 1250 400750674 400750703
    0x110307060c150c09090c03090302010b060414150c0f100c050301120f0203011107030e12010b0a062a030203090103050f2a070b07020307170703140d060302060c03040501020c180103 79
    0x101d00c4111000e0305c00c1c0d07841403152a4001d10010010082d098054005510f4401101030a25009040714121034075243c02c14105c030010300800c00c1d82590420701c10340080d4104201e24030aa403c0c0325130308100d03400c80042d09003640100390700010394000b01407410801c9420030050003a01c0d5244512440f803500502d541c1c1480c2c50f41e00c0170070700405040304141200c03580440e001c2c0802d980300501b402d120409450400c285c114540c080e6081e00c140c69080f95101e0f030328240600c5503522400d0449050f541f50ba140040224290101001c81211400145d005810000c1c58001558140c05401c0e002040861030052500c0c02c805100b06101c00c0c50380541000242101c00c100b0101c5072016120310035009410485582404503001c0d569500004086034001c5400c02d8075007400310324405032425184c041d20741000d003044101502d0744a80c0321107100300c4440d548403004000743c1c48001c05816601c28620066940e1402c000029113402003e08109102e441d0002c122a0101c03403c581c01411a076000d005400040c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 400753174 1250 400751924 400751927
    0xb0d0509070f14010905040c0e0126040c030308090c03030904090501090c0b070c0b040506031306090512030910090503090126040804060e030607020d18050d110307060c150c 76
    0x400355800300414842c0c4240109542d036242c00030807114503091302c440e0205544c0700284000e131a09162064041404010000215402342a24243d108951040c40444da100d001d41d610f1070706801d41c0c0c15078014070f0950003402003607000300c0c08581041a100003844281c8030500002e9492051243d414011601c0710000b008008003500440210350788206030240d030075140c0c2400780035a00982d100b56541c0d943d0300c60014445074400b0845095a1000e0300880c5140c0e148440e000e800c01030402c088032100d60f54618400412403e1008100310000c81e080e80d5035a0070000031092400c0051b00416450310308d08070304103000a8000044a180b40e0003800d002500d400901040004148150320741c4c004003490074200010401000010b009544041c1c407014100502c483c289941d8544c101c030b180b00981d101c0001c0e400d0050140341c0c1070080c072001554106025842d5070201c0c282c820030300021661103110b1910901a40380500c02030001d00000d04d003c1d030107640f40d502c40a00c0c0700804480303203050f26600d0912802c1c0301d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 400754424 1250 400753174 400753183
    0x60405132310052e0303051e0f0a020a1103010e07150e0a0f05030111040e040b10052713021e0a03020409050c0102060a02030c0418090203150403021005010b0d0509 72
    0x180c0c80c2e90800203460b2a140c009100c00501420561380107400054000443c144d00e0300d1820f413074240c0c2e01e640c03d0443d00e60740511007800d80403c40540030424041002041844070040c43c00680550281c07150300414900301e0610035102011900c2a41051b521100b01d03180040c011080340e4014480c646146441c1c0c41c02e490f4500414480c41e04034800ba1404924644070005417000c588043d80200030800c031200385c0300c00c10301a0b8018640d00b500b0120100d0040381c507002d8000d070451790302420b0001c00750351a000200075524015506000c19040f2182666803c0020407070303540001102040c4030900001d0740098100745007142100e03240c80c2d0041ca40340946d116100381d03d01560b80a032040004000344d00f091540c800003000d40c1030043c0300340c1000894003410b50095a001e030b86039584c0c19041c070b41461400741c0d000b01c43c46000071035250303581d040300302503076080000031480808290f4420003800d190a000741400318210308030003a14102401008510803240440c1c0c0710075036401c8002455141d4026a60a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 400755674 1250 400754424 400754443
    0xc03050f09340602150124120605130902040f0e0c090703060803070b0405160f0b161a0403110607050d09150906050105040c18030f08070b040602030604051323 70
    0x441840b400201d8025000142e5171030300c2d1020907440c0200ea030b07204c11030032618002411800084900c0b00c07660132144d0150303c9099030040e000304046034180c0c4800c0414042740310304556454454030f4040c16419401d007032007190340c80030700350f44248100c0750039046081d50b40070107450003800b4004203400100c84900c00e40c40704028018200c19a6660043c1e42004000510300b0f0380c0507200b600500e088660315645020041041b41d5005400c07011081c98005400302d55001140303070380703079007580e514140c400a0180321030308203440d0b003520b40d2040c0c9042130f040081010206510001565108905008078140c00c0800e4520310b4020000c04641c08449113081c2100300160481c1e18225400c000044080140c2500242d050351400d94003000220880041201d00051020b4094090841d0400070701c041000e40c0300025003227000d01541460030b4180d0b66010a400411102544c04c0365002c0244406440c0c2800380c00e8019110b50300090850505448181e2038446c60b24024401c4581041c94060760a0b050050400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 400756924 1250 400755674 400755763
    0x30c0c2e030213080606010801090e010b03031306020d05030415110417060601080630071502010906060b070b36012004080d0e0a030204050403030c03050f09 69
    0x503454504002030040c1d04626580f0b80080440e1002140540b400100f80340325000503075841549034a4031860b40014861a580c4039115500c41d43e0f001c100d61000c00090068194046000c403407c0e1504c10020f0500103013003014000c00c0400c00610000c50303c90b07001d1245201780c0c00c00006030500144089440707407003942d02c0050b20305060100500d6000000c030b070461242ca001c0c1c0380c99407142d841e07030200f00540c0d900070034200380400442d4581c100d02907440d001c807010040d07000880b100300740c98042048844060107103100040c0c2d1500789060401c00c40b400707520300034042030a980d81084e078555500074444a0040c000d01007103038413400b6513034400f10744549600b40302c2d01a00e41c0d0041c0c804031542940a4000c0c286002080d140240070024240f0540b03080f10226140c5402400010795020802c40300c4940c40050320313501141031540880540c0d20351095500403880380c0c60008287d4130192015003903444c010064843c030703a803120030401c540341c005c14414600c1d1000150201c10a81a90002d00d24003000c089094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 400758174 1250 400756924 400756999
    0x303030e0c040606030b331e03010f090c030b0a030201053601020f0c0f0108151302090415140105090a030503030a02030f0a0e1e0f010509031b030c0c 66
    0x60103501a40a14500402130310201c51f015a124111103403500c2e0708210342c074003030113128601c4808040701014141d40105203440c1c21030b400c1e040388a507175250401e810452401c2d074040030400140f0400d01c96800380388a60300b828031020406400140e0788005621010781445000900c00c1801c22000f13500a200d8403c0c2060210300c3c040c2010003946011002071020b01511560450101a140000d100510341d80001c004000e821035400044807043d002401902641d4444000060301e80d60b0104a00c0501456510050700e441c5d00c00c00b00001e503040000c0301985043c00c0340040c002400c1d41616008035200030b00340f4503550305a5001162270800c056001411502010040c09600480b0341c00860003800450b4101c00302d500c4011050342100e0f00801091b0495000e6032111080150070101c050901c3d1440041e00c80c586002d403c05401d46800301c5403114250000074030a1009940384840d41040c4520303200a60a000c48540016035807003100200c00d1052248003400060140411104880041d5641811 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 400759424 1250 400758174 400758179
    0xf211509050d0f020304050d110102070b03070e01090605120c0901052a0c060436140106090b131208071e0b06150a030c050c0f0609010f11040303030e0c0406 69
    0x15500c400302c00c00d04500140c4804592140c0302e100005803415550010600f042070380c0e05a80350441080c61000381415401080d00008000c0f06c0d40b400781d40704a01e035407102e01045400400042c40518580c015034240807090003145e101c0703a44014126800700c1a1007030079a4820f02d5400507180f50182e2810301107002e070100241100da000c1803040d000b07000d00701000c48a01c1d111074820000d19000b180105c03c10101c10300d1140003a400d40c6441e02c01c41074902400d04640880072800c140c103a4440140681c01000700c40f004100540c1e02c44030300001071400001907420300e01c41c1e075210f2072101c0c007601c601c61141c080c5200100c280300d0158211002e281d8016400d280f00160800c0019070400400802d83e107105114000400702d003008101c42a100c00c9800d241c0d40381030300d01d0f2000d81c000c0c103048a5407003c00200388805078408008201e091000d0a040009104d28034042501c1c0d030031345000740b800e455200d040410030560415094103580a8079031606005c0b505920f400d808038913284170b03507050356400f5080c80d000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 400760674 1250 400759424 400759433
    0xa0302030d06050423100306020d150602010b0612040813060906030e0d05030408030a060e0a0b090a0c0c03120e0303161101050105130905150403030e06010f211509 72
    0x9100c1807070560070900105603144200011a20030000580044092540c0610780304200ca00c030507444540140c0c03401140d526134940c1c10480c1c110000c1d0310040d560b50840c00195444000c5450010100d9200a010001a68020070b00500400e0a41c11505604801190800080300141c0d42c1c070740013800301002140d98410005284502070701c0303580c01007481c2101e00104a54081541c2488010300d4440710314544903070342c0340210350b48000e051540d41d9a4841022038034115210019000b10071440c1c001c119210001e081062003030300501a80c0d02e8a203403010360481d05800a40390f5510340d400d4100300404204c3e00d0005000b030810022210568000041005008035002e80e000c3d014400c030741e40350306281c01072011442c00c9650a025207644500c44c00c0c0d40410040380ca41205e07112a10076415600001d00e0108802c0980009881c1140800c1d214040c0c00c0340607604204240c0105110740d000072110349424411200c001e010041c0000c0e1600c851904801d00420280b2101c01c1f05868900700300c1c070303052810b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 400761924 1250 400760674 400760677
    0x6041106071e0602120f0f041202030d0f02090312190503131e1707031e05040b04030803060f190302010804020f0d0f0c1d1501020a0c060306150503040308040b0403030e0a030203 78
    0x2040c400b224600046184840020302c0d847c801e450079807814915895a80700c01c13054842d0303801c0300000c41c402008298001070842c02003070444200903001681712250b02c810182400c018003c2191101d0f01805030070505443c0c2c0c03000300c02060390b0f0708040d580d0340c991440105154007210706c068401401c0d003000081c4c1040718903105e245280940c1c10082d038060202240c010900c0b51000280000c1c0416500c44980207100c3c41001c0e036122281010b518141d65021214001e800076801540d036170308040f041082c10f0030318203107200720400112a41e40a0000540703030090b6032151408041d04106c102d83c0010219200c1020003021480010040260403a103454540c0a61030b50580455070203410b078800040000c0c200f0000001c051920051007010342e220070042e010403410300c0d00c42c0e0443c840c071111140459596584a0301501540c0d4011648505142e1a07503060304d4002100c0e01040703070410400010a500c0490f4507009513100030801d000d5103583c2402c401404203d03080443c0ca0181d420088205a000130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 400763174 1250 400761924 400761937
    0x70302090c090906040b1c140f010e030f0a0318050105070e01020d09030227190b0105030103030507030503100509010602030a08090607020607050d150f05030c0306041106071e0602 79
    0x212044400e0780c480211031401e0103400c0ca4190001c1001d0003050051801d0b8204a05510b0b002e8003820b101500c1074103a00c001c1018240568448809a01644283d04140500d142c0c091592000740080411042c506036244185000300d600300d0030204098031094441c1d0820a4040e07811016105da214450a285009100c103403110f0012541a215020403540080350320f07040c10a843e00c622542601d944c083c403414a07200c5c000c4141c0c98080d5036081c4c0e10040304a455a024040f24813032081008481d00880040312030102400e414450207200410000381e102049460580d407600e412500c0307403125200700789169401d0304410f40c04030311071001158080e4000301500e003840c46542d8035080c6d61180e21040352038070030650b02840140c10800001d14850300400040c800000c101d90005021800120b00714030050640c0c000c49003504544004001c140f4007044041f0307491100314007800039810280e6803100840f05200c2c040c0e01407400800c00390103202d02c1c000808010102200130140c501d1032803422000942c4502d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 400764424 1250 400763174 400763179
    0xd0209030d031a10020a230d020106030506061315060509240901111005010e0604110a0c060e0a06111b0a03020303071d060c060103031e0c02040906140405070302 71
    0x45065000d094820300983c0b41c5641d103540d0500c85a01c60f4814007085007a450f40030320070342c031601d28444006a107654105c101d03541c01101036400021403031041800c01c80b203a5203007421a03040038018004070340b01007041c4c5d1708040b0444405030401303c1c0000e0b84020b0040e0301c3c100400c82661880003c4c0482d0403500400b441c14044640c0b070804030180d600c2860b0300054901c000042c44d030602880002e54003900111003030f0300d116802c6910b141480c0e6045802c1d544241c00504100c010303041031040e00c1c01c0034040d002d500404103110317030700700040701070020034040199401401e4a500d4050001d410801407013642a038a406c074406020315000c3e0744071038465500c441140d003040782c9682ca141c00740e0540419042e55159069000d54951b03240c40004031071406210b040501c0b03119201030030290540d51640204041407125010704090340c518200582480c200100c056001541300a481150640c00703070030303505656030441c0c1c0010132006600b440401006000e082c100c82c000c00314240014080005030020072a4400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 400765674 1250 400764424 400764433
    0x17040b06040501090903080105101b060218010305041e0c080106061d0102030306030712050304090f0c0207051f030f0e03040b1201050a0b0d0903140313170c0a081303080d020903 78
    0x2220f00c1c03132084450001d0050002481280180003e1508101d40a441c5c3d1a5141101100d4180c16402d807001c03950310f60031503a459000030320039090b26604441c2640c5080c2401c041260f890136448052100e0400040d003d91152042e00706403c0003890301c0c0350006814144004c02c20140c030f13000003030240541c1a50441c00072101a410720841c1d0320000480b4407414025014bc03561610305940d241000701240001c03034030341c00180004074203d002d070b125058260f4203004000c10541d85481d800703410810b5a4010a0003040c0312520001c107801d101c3e0701d01c030074991946800518501c128035541c1c010b218924108910b03000014001600c000308001400e5821a00d4407815216641c4d1000c12110101170710442d0300e030310020b00418099a11680c0454001d138020b0605685074181d152004409034400c0310a011481d144584102c2442942030600b0082041c2843d168900070040e004103a59076100000280348000000c2ca5001c089280c541110003154400c0200c0e40702e5109403900c00280d040910300e02d000348903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 400766924 1250 400765674 400765679
    0xf070e06060406020312040501020405040c1d03010501080714011106070f09060207050102101802030a1b17030304020d0c0e010603020d050708060d110414010f0503120a1e17040b06040501 82
    0x2030460440b41201d140303030000e600d0070480f46918412600020001d0321255405d100015480d216409030000c005140d0341c842503401f843c2d00801c40c4006280a403107000303a141c10010700211400241c1d007405e4a048544034100c110003000100c4280143c3d0321490b2950190505111800f41c128198072407113600750704d40055482d20784004981c1d445883c480c0d80e0050f80008400c0c070a0740b0140c1d115914143d01206180950801c03034001c40d1405005100486050034103000400c0540b10b03008020f00a000d0700d480c078004001e4001d400e50743ea80030150000e0b10810805480804000b418100c11009043c0010038001e07641e5207e8001e80250800c0400c80c6155040c00d00061070340780301c0d68807944188401449800300061071f0f02d41c11403504c068403d00c0c0d001680e84c4811254001c02103281070081c00d50358464140d042c2484281800d11103109140705121030107101466969800c03950b54084080c40194a03010b19500d4002228205041281000300141c0d220910040c041003442c400d10036503082c5d40602042e40d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 400768174 1250 400766924 400766929
    0x70302100503040b04020f0117190c0504120b06120706020d180b12180f0f19020105030c1e030411040c020c060f0309100e07030b0a020412060209120f070e06 69
    0x40200c80040813206040c00080040c0b5251742600912030040c502400c981808002180c10f0620954100d0205149060300e100c0070140c0b405442080011031800c5c6003882c0c540703100c000003105d503500000c002000c81c000164041d00c40c040c1225800f8a6070080b90000303039540d030010f03480f1344640507054000380c10100b80241d1542021603070f8003141c0e000d00300d02d071500c00d41c18044044070b5400b8090300c0c80d52051810b0b00c0d0b00a0310400164103580d41c0d940140c200703180b41078065442e00000c007555282c0180401c10300d5001d80e07044401d0b254014806404503941e41e100b0f00840440c004a99501215060044148424402e008404e580201d00980b000c02a8030a20003090740d54503130618640740c0c4030401708158800c50320303942e002e0f6410468050071203ca40320104440300982d070b110055442c10703620841040050010002c4070f5604591030550031464107040c000d5030000380d040102c02a2060360000340300170503611454812502052024281c8900920041d2115180c039428070808031700301d1010000c1503003807 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 400769424 1250 400768174 400768177
    0x5030a0e07140607051006060203040611061506071103190b0604050906161803030309031206080a030311090a14130b09011a0417010507080109090203121c0e0703021005 74
    0x8441c1d11a40c0c9002c051007408103e40c0b5803103030508403028000c40580c05011040d500521025102940156440e182010002801550150307074520780c1c0e42c840c50510640b0250110306030b030000001c2e0307021640e034001800e01c0d500e8810486540c1c2d4052260501c000110304012110b41e0800e4031940890629403101ca0400c003da500c299002801504410081041c0203500c0d15140003000c0d0078213180103002c90108100304c803a044c40c0d0003600802d845030001001c265005803c20415454010304100490601582c1d607a11140c2035002070a01d55615102480301242c0300c04d03203100d80b50007001005003d40311042c04080c1240a0304660042181d02886500c10f040342c012280d000c1006452098180e00c2c014030901c05805000d145001a0402c10010a1018464007001d44186840c00041500d0409a5000300903c805a10507038805103421032140c010394000c24075103982d0a4004810340c03160341c0c1d00499120203180202e400c43c0d181c900541003024010200703d070700c02c480c000c030b8096405c03812861064500b07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 400770674 1250 400769424 400769429
    0xf0816090b03100213091103090f060f040f030905030616022406102304032303070303150519150810090203150603150a091a01030e01140705030a0e07 66
    0x940c214001c40f1030003050b00c0d8007800c1c00000352510040c004e66075078840c00440d01c118501c0302c40008000308000e0840740c01c102c202104c0c00a000107026610749914202c0303034040c0250005081c2d5610500100074980b02d242d1610240078020296942410b1036065040f49502440e401c601600030328224000b004080754089030b05c44940074044040740d0b51042084240c52185200d1000d1000c0700c464540d90070f020f1803104481c090740740440ca68503400e5080240c803541d94101380c0c000d082e00480e820304100c2004400c0e28502581030a010030555041c1100ca451803031039800070341d00102c07001812407800400f40b03101c00803503003d44112101112011001c481c614421500003507071038200c107420810b5008640c000d40d48803105203c8022000c12180020300d82c0e600c250b034103181c4615070f109050694504042010001e1007101810050700c1035007180f9280c14000d000b44141415035a1084961406003900a82107194224120103501e1400c240007030110341041d6290340c1c400780b8001489805d90381c0081c00105 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 400771924 1250 400770674 400770679
    0xb0c03040b010f0b1813150e06060901201516110d0c020603040507180506010e09220c09020d15092d02130303110f07050d1b0f0816090b 60
    0x5004a014105c44000ca42c401841d6000b0500d003821070001d01c02c0344500c00d25900d4001e8204480c0e0300c2c18001030860344000c0c0066116102c1084110881d07a00400307203100d10070107059000080c1510b0744010b41014001283d5218003038014041040107126a04600c02204603a1030b450311081004441d0b0303a6500c60b1110100103d107103e09400054500348025540c810301c40c10032075003101d440702800b0603444100460b00c4030f8640c407034042c0b252942e0072115082c00301d1000e4504180a203808131450fa00c54031140f03004155845902d90120900440813207410107051030010541d0f80741d2030310074100d0040c000701304054299401c04a001c0b071011440d004d03801e100c0080b6440b5007400010100c80d0b032a0510804140d0503029420481d402950101c1d0340c07644000d6009444680c5101160703003006060503003103140c00300d0a4110b00411711007643d586044da910140c2140c600001d2070340084503110b13242c08641061250401c0d40a002861100001c0c200b0301c917811030f0082f41d03109550fa0b900b1500703884440e190a80d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 400773174 1250 400771924 400771927
    0x1306080706030231050103110a080109050903070615050a0e040c0e070302040503100b09100e04060506060c340b0d0506041b0201050a06050a1d0a06030b0c03040b010f0b 74
    0x79039200390050040030f164900c109400500c0780c2d19505001c4075001040c2c1d032144104104000799030305803041560b1825000601d510b428407920004102c00414011003000c00c1d541d4002c1a4018000c2054550311940400c081085210045e589001d400391482401c5c8a54030a00c0c01080c0008108034460140740d1180391446c00a04102c0c00303025000d8028940c504241e42804006402d075410001d1040441031141c0004091030710f00c090000001004041182840d0807080401040042811156100750060030000d01e5845507800254140303e408032401c10b902c28044402804000b5001301180290030700c40307000e40f9070a00fa10281c0b04003061712800020f14800d1015008009142e0030040c0d004000410008407164141c200c0d415004e00c11581c0c20040c3c0d599400c201c4040c0403446040c0140c84c0450303001d18280d1030075a030f00b02e10406400300403e21130b0552003c583d403586950041d602944c2d20060107645032030301c2a5000c0c0c8a410880d800d4402c03280030000041c040385481c1101d07080d92105a01c0300d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 400774424 1250 400773174 400773179
    0xc05090907030b150f03040c0803090f150909180d1d010e010e03010516080a060f05061308011a132c160915060810030311030c0a1113060807 62
    0x80d4003e25903440302e0340d00304110300051012401104c00403c10080d4030303c0d059440b4241820242c00c0c1003071766001b00328168010800310596a54024444900350b808460811405206011f0105140640340c1c00d103401c402d020b81800544c0b0a040d0210b1181c0001100711150240c410768211000e0600021130690307003800d14980e0f0119445034080f80407148060400c40101e0400e140407034210f84c0d0484418205609903e43e0b0a030aa511080d0342d80c21082194090107407a04008981280900504ca024415080080d4041e540480c0003086002400c103800201714034800b012682e0481164004050320030b2410b03040c0082492024410503290500321040903407902d80c2da010502d001080c0c034440781030500c6210b10000c40002c40902041c040c00940d500800d0a81e0b290383c0e00580a4600e40007441846240e9041200c007580b600b80e04802c49406181240c0f0105044492500f50b2007100078400e0780d03015000304841440034015540c40528019a01c0084c1e440b09049090119400c9010b809d0707540d042030404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 400775674 1250 400774424 400774427
    0x8250e01090b0301020c0d0315050a0302060a2a03020a020a0605030906070e010c0501150501090b030c03060d060e0307030e0a05120a020946050f1303050408030708030108010c05090907 81
    0x42c001c08a07014000504d030900308a4040e00d00004d802da00c42c0060349424013031032103203003240707100d401082c09490179500d060841e0300051050095445900802c00e03182250408061920f020b000e00360604800d49203591010b090081d00c03203990610907405042021000030b200ca1255040324411076140000c1c000759291b10300c0844259984442032410003c280e9202d130007140c8203204502901032000d03c0346070813a10300b81c00500a44940d90000103040b409008104401031800122940b0042c212000750305400d5516081c401806185240301552201040c80410140c000e600441c409500321038080e0001d44d103408004a1030301d5008800d8130f68001d024000010708141c0c0115820040302d138216860074068820111014108140c00e02081d48a4518141c200c1c030310040c10240d0300c44100050203180b900691032030024034050300900b51800141420010705200d04240d030050041c800540744d0354001c6050600300c07508280a02c0002c2e501c0d2440482c00640100c0880d0383e80303800940501419620380c0700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 400776924 1250 400775674 400775681
    0x24181802131a0414040c05010e01050a0c05122106030316020409150c05040e0f0105090c0702010c080c01022101060818150705031501030608100e1608250e0109 70
    0x320703600e00e0710091280c216030f51940a0403c52010780c0744140340b40d290900300b48003511500d91200341440800d4032241d43d1644d20004403000301c0d18605083d8030315041ca14200e0719140d010392a28448000200d0901b0000c24404100411198040d0007501d2b680c076400301701501c1307104510002105503480f01c8040014103007030b0450040c00d0f014140b0901d190700407900100a4407048042c44002600000d0244107060881e03054580010107403990303030029070400000c03c0c0740c0c0d20064030a100e440c80100308402103a10030090030b070744a80e200b40700c03540310b04040071881d000c0c0d04410450114800300a818010411100c0000e9040310065034403480310b038549082080d4a010084d04210342c0b0301a4204c503451248103a8a614065207a540d12142d5070303d090b070b016031428a144501c6c0c034101400c0c00302c10070004100184c1d0301900428414000782002a0112441c03400c0001030070b450744070840520008000401084d0b0980ca4448860340d504121452458888a0001809490195400d80c0014800f240c055403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 400778174 1250 400776924 400776941
    0x415030605030118020117060d230703120908150705070f050f061005060910030b0406080f0c03150c040605070f0816110103060b0d2418180213 63
    0x1800508562030364042801d6aa14a030f510030f041d240001c0710011941d004249148072120301e01e20131458100390f00010300c0034134a14000b821a103000c685030354003070498141070310007104540205c1e04601e0f41c1c0e241c80e05603000650301e0080803d002d07440000c2c2d81c0002040081200e004602c025a5a5854803000e44903504002d600751400c00f009007080000400401c2001c0240030031400420140c60700004a8840d41001d412181c00f469040c000300d505521403105080c50440541000b084c000d02c4a004240104003581c0058030522540200380e48185000c50300406c0d2440650588030b0b005659515411b5044066401044051080004102c403521840141c0742c010b10662100f100000240c4030740404d500003420000c0b401800d42c04030410003400164207010300e642800d05004962804c61482e4440c0a00c0b03d480103003070b032240311000505c070103c40219408030fa20300081e1a01a12401179503d00c000e6040c8512803039103408039442d01000400316034940a0303401000038286480556070200a0070344c16 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 400779424 1250 400778174 400778177
    0x200106230105161707050c0f0f01050703231303022b080703020a06050108061006030c0903080d1508030c060f010e0c0703031413061103060603040b1e040804050f0909030415 76
    0x15003404c10b4107614020038006000d0001004a0b00f0404108107081c140c03c0099481081c00100c40301c03c0381d805c40c060300e15003509410030032500c0f4201580c140d1440c40e0000503c055400c0054030408012050700d038482a80e0003030f101e004c40448041c04070341c4007194844400a0f4500c440b031081c4000342a01c2c00914140c0d1281c8191600804155240c01c181d070405e07001006281c0043e4100b2041001550321800240418582404030140c10040600b42422a00011388800c5000403554003a52147c0c004400c080c044007101c0300c0c555a01c841e07440c2ca0b0381003810007280c00d02803c80460121b8140001083c140c0e00601304103070300307500c4081c002c0c0c3c1e1542c04075230304030103140d141c000c0e40e0300340100c40030014070441c09003412100c01080340c60004106c802d020211100d0381007d0090184944420081d40c0c2e110303610400140c4ca0b900c032192020b00701c0c10094041581d1081503410041000410030207401111020356200440002050400010403001c0b111065154014801041529040f21050b81303031050380d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 400780674 1250 400779424 400779443
    0x1305060f04030b090a0206070c03030f02010510150302090603100609091e02093d1704020f01020f06312a050a12031b050c010503060120010623010516 66
    0x201d46c0882d525401c1108142e40b03000c0c801004009054000c060300f4040280c500c020001c5141415181d84240ca05008001310301040582c0402c0e001c0c007982c1103815001004202589a180426034050b0540e0075005480005051401c00241601c1d113004032620000200d201000c04c1c0d00c126180070080d000681c1d020703030160040c03410490800f540441c0101c10040300799800d100c2c400d4070460b602e03860001e401e003404010101c00311510308482071003600d81080c1c1c1140c01340307210521800101c0c0361114403428a1918050503091052029604c1c0038107850008600c0d9a260542c81f442803401507120400d005014003070600c603c200c00790301480c03414551054100d810368450b6140c02c00300b904003109400c071102000784000040107250300640054218448065024076144259a4454841801145c824140b04020012507190303030040614802e11441600815002807030405030b140600b1062094940c1c0c0c030401540391440000001d00d0035030205068552915041d254081c00e200c840214106841c5520b6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 400781924 1250 400780674 400780693
    0x1107031203020d020315120c030c060a030e1902150f1206030f010e03070b010e07050406030207030917011a041107020d06201902150411150f1305060f04030b09 70
    0x1004d00c09940205802c0303009403940003145051000700c5009885101080e03021040114031680c00241c01d00c44040c0036910540c68074812501940506a4601c40303503558041c407448400c50302803c221095985008842a4500d4054403420750000e10036100107031080da2080098a80e0303404841c18503600100c015007203c07012180da00e07100b0b086038948241c0000c1904001140c0c003d01c49540e00703203800b4142d58106910b4034282810094228480c0c0d104910515070049442c800b803500800e65403000388035992218100349800710540e802040140180f0004982060100a06043ca80702d5080000f0450310414607105003a002c0000c2c101401c1d40445e44a510395194140c02ca03200003e00380046a24aa11512009420218032265000d00041002c5610030600504092803c44049401c41d030070100b50415604a10003298a9810307801c0340008500c800100e84240500380030040c458600340e5003203400d0254a4000700201c610656205c13203243c410500c818408038802250300d54001d0000f1b002c0f20310392003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 400783174 1250 400781924 400781947
    0x609070e030f0d1d030309120a0b042102010614130912090806090d020a2003060403080a060e10140a0e0a0c080115020604111215070f110703120302 65
    0x5440c01c1e1070815403ca214038008803134015040c40380c0b00e40d82d0505048007060136070209a0b03900640014602c144002c10500c1c058080034403540d400306401c121b400820740303007608140800c181c503404142012080e85001c0000c1a1040c0b2949040c4c0345400d0044807001401001c20015050380070210b02c100c3e907600d8080001600d5a00b09640c905e51584030400c4c1c03a864203c02c503040400c020400c0c06176420401c4011030f800e0340400c80f00704140d404585207046260982d200b51240540e21521038043c49941c061000349a0005402449003441d41d42c141b11143c1c0f103003c1400c003008150740d2a2060309211a007404000ba080c0c587c1c08041c0f0002d0b00c4206942ea59003410720b00c0c140c003620000426603036003c0e9600300551040010b405044841d44048a44040703103402541c941e4020000f40841d004020891042e03582d041c008039112a10b001210044d000c0619901c0742d0800558511021600c400c0d0055200c902925400c0003408000c8064025030307282d920b80b42c0e08024254480400c1560801c072495210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 400784424 1250 400783174 400783183
    0xb0702150a09050c030f10090804030b07020a02030705040c05040e04050f0604031206090603110f0f030a0b01080c0f0d061e060303030903090b180607060b10020a030e01080f0609070e03 81
    0x1070405540c0801c82a00c0d9042c01c42c1071070240644103000342c20001d4012503078400080d0b40c0c18040018030000614801504200c580e60180f40c000404024501050102c40360b40011032621043c000c809449440f6510701c1000111003c000ca40000b180040c807041100c02d9078001e096034014003a074103990141c01400b02082c2403410450b0105d0100b074251018101c071000c40d1040c134024001c0c000040150304e007151a0445000304881205200e03d41101d681d00d001c4c0c44a807580c01c1e001c500901154048152481e010040020034040d0b060207100300c180c920403074070b81140010702d801c0d0040c1c440d01d083c40258030b42002401a00300300281041d960740541a9440091242c80e00031802030f500020389003861b160090010107541c1c00b132400c2000a000c20200540348400b801c0c100e20003140e5280d994009850018042c02141d18115030060002800e05041070700442c1303440c1018032a940703c0001c11420340042d59aa48152039911241002200007009410100f48a6420800d10b080c589454682c040010f49030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 400785674 1250 400784424 400784431
    0xc02010c05010e0708150a06060801090209121f0b0f011707020f0a080a11070803180f190312110601090e0a0507150905030a02060304020d23010902100c0f0b070215 72
    0x210b07803243d400420a041b0b0001c110341c000b4070780d40041c0201c1d40780c181c00070280001030040a1a040d400621901c07a940d0b07080d4aa1060102d0760103681213800000d40d14564604501d924502484c20100312103400e10b0840041c84200405031141500300c0100044074041d020006c0100003907104a0140d0b44000808002c4200c0e114460120b0b070baa111000d0100804140d0b2185a600403a48260401c5c405a003001c4280c91b5180d495520042c1c0e400421000220a5900d07c030b1443d030401c00080718074030300c0d080c09100103042d60b005030603039181855201812900042c01800d9242603070410401400b4000041d00070442180c0250100e4885880a1315803a041a032147d11000c4c0e212a010300900c540e0ba08228000020078040300a08040b41e80d580100d1074500c0b00a0000340f1030320f22480548200015551440c04107d0000200d5150380030303940c60320307000344502502039100768101802514054424502d81600946c0400c2d946008001552031038002c9070040e09a2081d4090201181d44441100c0700307541c032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 400786924 1250 400785674 400785689
    0xe03120c0a021c1a091905010f050702030711040b150d050a0506010f02031b120409050106080f0108100c0201020903010c020c09010e0435030f06010306150c02010c05010e07 76
    0x109010074070400c0b83c2030b070260b44800c054088255064010401002d101c0c3c0610580ea40c00d2809070740c602021a0070203e034001c80c0040d01c2c2c29000c481090150542c0100d043da044000100550b8507042c40681c1da07806a440002e258140840462480b414250401c0203122000fa162805181c0003800d1155076422446404580c540d840f41044038170900c40c05015040823003802c00d40050f0000400080d00d038490011075184011041d250700c1070100d001c00c2241403c403205a50180c4503622212410f014050a11440c400100103c1c045401d04200d0507000d412203070084006c11001f82d02d812404040e110b40c1c1920002c3d95400e00c0000103548080c00b400d00340e1700e81540940040181c0c03604201d03103402c0681025082400c4101000005002d000000d201c0c0c040038080003422034101100611000203021002c0c3d07a00001106001d0740981984003d40624001d072400d11107941c4507190f520074101c0045500000550030b01409e00554001d40402184500410000c110800a101c1240c07620065500890 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 400788174 1250 400786924 400786933
    0xd03030b030607030e0a0f0f020a0602030408010b040605060d0b01140408070e0a050405030307080408070218010806060d052512050f0d0503060a03031214090d26070e03120c 76
    0xa5180900290ba40507049013020442504020305456841c07822900060010f580c2e48400400d00c241c01d045c0d4801140d0007040315100c2a160708000b5200d070007912034803003291700348980000720746000d0250301c040d02c5015103520705011080c11100d0240c48054000750501080c00b016040201184c0024001780c49640c001b0300c0c100340740a802e140540002440d41c00d84903e130205020015901104032604100e540c9020585a25541001d0ad09803040481c001d40c40710a100090f0400f107854440345049901800c241e440e00d41e60042441090189030360010520340260019021400c40034007a1031681c10708102c00e000c070796107990b8119041410039500f40d42c140d00582444032402410817400102e2a450318089046d0705200004c00c0086003540402018040034950650388000c0c1984944170101c41411b0714201c900b815400d580c3c540780d04280d428006200300a01030b070345e441c0c807020b406c801e0703040c00f400189140d8503108101d03158007170300c0b0380b0a07030502039060201000d00f9400c000d885d15006040141 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 400789424 1250 400788174 400788191
    0x2060609220602090114031003080a12050703051512061b070f061b0903050601060f0509100e0f030a03020606090411090103060225020319060e16180b0d11010507020d0303 75
    0x24018050b0030394100401901041040001c65001c3c0b0a00109c940c4041c480e500c5120b20300027503a040e50840c01e40d42420340f802041150241d40342d040a400750020f000f095001908500c10300070740e01006010f11100358040c0b0045060072a405107900d1003106140d8100c0c2c00c0c00496500c0c01c0b29010400b0302503a003030b515074441104d039542c20301090019a40b1428100300442c03440e80c480d80c89103c148602c0041c4080c1205500d03035180540100c40880c031000f40805400d101c0d11801a10600c8400c24140c000c07400c0403029115810002800400550542c000f4040b9070b841008010360040d00400071903181441c400000480c0d241c680c01103019602c6060b001d40c992242e01d0b202c00c0c0c45801704880401c000e030049840d002603207010603d01c0d04400e07030204484020b040c03810000003178508009800302c0c030310032820b805010500c240d0b603440548070346503125040700741038040140a0300c0b0f031940e065912603400d508240008216103c02c041c0c1c403106042250520b4242d400245a40303146003020340100e515054034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 400790674 1250 400789424 400789427
    0x11120c010f020301060c06020903010f0f020a0801060f1d0a050a0f0602010b0d02151e0a111207050c19081006051311040902070203010b03010633020606092206020901 73
    0x44001407201c0100441c10740d854510b00421105c0603039400381c046940002c90306000e880079080518103a0350500280454000f240d4100300039405113800e603000807412000803440038032038080740210745000c0d5a14020344043c1c0c00391040005130344a660354441d000e21030000b0540c85498039400142030006014019515010003e401c0d998070784002441000080c1142e40140e55104c4a03003084c2500e40c03000344e100e0000004c58210041100c2d1a24a9810302044001003141d12043d140c08451144007900c80800303180310760303860900648000811a4218140e00c03042c5080c45a1841c008804916107002020343d12104a410b254201380d50382c404648445e000c1c0114240b1005401020070440340c1004070000300d04019000d0301450080c8200c01d90000381c600c0c00c0d0b590075040907110b00300040007000180d03640d4492080f00e207140c030707011a100140702d01c6241441151821040041c80c42d81c014203c507607201c20801030302400041c04010200d22102400090010400f182c0e03204609c910f00040e40c401c5503400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 400791924 1250 400790674 400790681
    0x14010203071b08190c0e0a0e0a21050910050702011e0306060f111005070c080d06062c01030203070c0b1806100b0409020f3001050a080a020d0311120c01 67
    0x100d0b189440340410102001174480c103404421a078550303070400d426440e403424000191040c0000300c1060301c544c842c210148801c0c8100d9000110345035880125031200454166194003030000820782c032030f900d2201d52000b1800f80004140e040e20514011070207038654662200b10f03040150044002035a26101848a02d401400c6203480078281d040c03400c0f2552243c10754aa503950390090402d041a2070b10081880140582c841841e0107500c0508147c858034102d40301002030000d4070030703800000d84400b2603640015006c0c5107207002e40e403480f50b07001c05c1e00c8507480150041e6201034120402c0100101c218004140f000ca4118080c0aa010700c981c00e06c488182e409103004405401c17044151081c18007041110b00b0341f4104c4044608079080940c4550b698004003045000b502c24580140c04500c0d4454400d800d6032254000582404600c007000ba6218400d200038120341d07020b2541c0c158808840a009441c1000991034801c0c82490480c560b41207134003140b0b080020650075002d05e100081040010f0321700c20301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 400793174 1250 400791924 400791943
    0xa0203100e090604030c1524090e0636010c030b04020306220e070e0901060b120a0203130819080604050405060610021912080906010e0114010203071b08 67
    0xa010616410400b01d0320780c44aa01420003402d01c002401c80c1010407050344000c582032410888100460744508a120880c200301007030004404184240c007003600c482c54403903106101c070824028801da65030f841002ca42c004402c558810340e52078200451525101341c4420008202440001184481c0200c3c2c000d42034403d425500c5214074014810001d0548411000c005243d070b620001180050402804500030311040c0c0e0850240d002d64000480c080c0000003119019100020080110030b0340c404506120f401641400c914800040001c0788840f05903401a64100c0701c0c450300054180b0242e500c00d101517214400d40088001024800800f8036000060107500040c25101480329150603940d2980303c202c01000240f1074860f00704504819442004655554040b240076218003c03640c1c00e00007201603081c03610f4400607071050001134040b0000319201e812140b03280202c0b40d5030707400d18400302075a014001c1a030b41144418030000010030750707079503c01115265141105a4540c1030080c031a080200c3c14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 400794424 1250 400793174 400793189
    0x717010204080d051215030d20030c0a0b2401030c03020c070f05041413020922080403060c0e01020a02011407020411030103020a05100203120a061203020d0f030b0a050d030c0b0a020310 81
    0x22940c42140c80200703074104a003030949040550140303000c00c40109e0a010744c500d4050352201042c40705c001c3c41c00140d208a05c1c0e0003074100b00481e03503030111300704110b0202c500040440c104003041021954001d030021401e101c3d81d0b0401604010010002c64900019030703100a403090b41e01c440c100150f0602e03200c0c0329646000c3c0b4a984d951440c00b80d4030001494501038000f4019001400052404041c01c941c5462443d103185820100700c4130781c107201d0210340041c0800d4421034640020951418000c1c6569809404186c001e4651002c03190015140101d541012a8410b01e04002080043c1e680b4410161401c4805051301d40703a5045005100c01d1044581246015030040d24400d90455000020b0301c400a002408241c10b41da260400381024019541c821413031400300c10391800c20960085148044410340d640c1e0104400d210340001c5094030702d0000b4541d040313003169000f4000740c1004c88045103158001d05000c1582c2e0000d80e208170212100311550010176a02200744200c0701e40d03102e110001805032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 400795674 1250 400794424 400794451
    0xc0d110d02030f0906070812010303030b0a0e0609070519050d0b01030203010803180f1002030703081b04030f060e030c100b0d150e0705040c050c010b030a050717010204080d0512 78
    0x400e00d02035035074403422440003040a000314910009a071084210b809090740601c1003510f07203141c5000824205800e0004801190030074a1044143c10b11310940300c102c816a660714041a01c41c1814018000c0c0040d00e03507030402608001c1c941101c040b4000a40490683e0b03a502503035048040115401c4506010f0320904141c01000104010f10b000015104211448030440400780d4003100000c10300d0750341107200c1d9000490420340024040e00800540f8400780241c41d00000c6e40c4d039400450041c02031104284501c0001031000348013041c580030070460100d10420300081c4044541c5070452440e004101841c281d5400316030071281d04041d601031000300d0710301680d6505d90b03c8003c0e91404025100012800c601644d1203000304d142d15810000311000781805001040301c0c843c29003004160342d011044170400c5600381926a0344a040000700d50f1150303500310029101070360614100040035010312079019490741d001d000100d4203803014030400c030300c50b09142ca60981da034084990601d034010008008003a5070300e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 400796924 1250 400795674 400795693
    0x307120e011d07080d1e0507061112060a03030207091d2b020303090d0e010e040c0e0f0913060507090e01061211030411011b4103070204051b0c0d11 65
    0x100300c02d800e206d09030f20380a940b10f084404042200c960003100805041d142c2445030504402007040c00030310300c80c000d104014035a507a8a2003404160341d030b0740c40b0007001a0302c9820100307d4031261ba4028100080d81e0b010304080519070b01d000f14500400c08001517428100c1e03e40e0b8040941d11681070311a03124181c0040c42c00c42c94002c4071207884000550145091011020508410b42c0c421244a001c1d400c000b4070030001200311510081c915031004031001d01070340862145440a2808410041c0708803900143d02d01141c101d0f580c1c100107840e0140594080c0407a008001c100012131504403400b8200541e14017408400d1801510305403060401004100b41c0304005200c0407075007242001180901c203003401d940030300b0824941c01c108800004040c0902004600d030005400008440d0410440346190440325081d0404642101100e5440c005000b5802000000018203144c0c0008d5440550801ca410040c1a15114117102da8050441d84180350412915500c01b150806140784612802d5002810300d640c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 400798174 1250 400796924 400796927
    0xa0306061d15060702010909050906040c080a0b0c0f120c0307091211090705130b0909010501020106060522150c02041413030305100f0602030316050f0307120e011d07080d 75
    0x114016070042c083ca00c005042d005590040f51b6900040c005150100101c2c6000041d107921001c00713030340c00c907540700310007000240b241c00002e40c81105c0c582002503029140c40d0911444595800b2000d007101d480c070240400540051802d850743d2013244005d00f50769403403810020003400369003241c000202c144503007024100460240040d0040c440d40a5400885540340d8240a90b16070152030901503140e420f40101182035080e4401800c0e181d04291194420751743c0f13a000581c240c0d03e00340138100001b202405021a492401114818030201c8400004042ca4517010305441024400f44200042041200d101d003c5081c00d00c00c41380c1e1711407907840d5000c01b410917480d03045000d08044009400c158441d8086940320041c0104d4800402046958541c01c41c0d44010203074030782d0000c40301d0610b40710324040d04210f040d0042040b00c070013010425826295075035900c0142c69412500400c500c5c40d82d6210040f1180322030910417808102a14914001003203000c500c0b06241c16401d4010721a0741d0072484041c0c8019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 400799424 1250 400798174 400798201
    0x60306051f050a02010603021e01030e0303071b06140c0c100c050a0f1b0c03380903070c031103070617041e05060124031404030305060f0a0306061d 65
    0x40c0d0341d40b60483e503c0b2007100007280517000c19080a907100c0303452941e0044a8401400004203801b081c4c0b801e01404072400d410359140d020484003c00030514030042038084049049414612074414030300041d103600820405450618201c440c4011b14070001418859844100841c2a41200440d0b0511400c0340203071004007079001e05076000b801e00c11f0030010f010385036020740320301101303c542500300000507840782c2840d401b061074030321090703076003d80c1000c0d0095080b03407460110200d0248480c41020304005402d090211410080500c256400140480400a100860410001c50140c1080c0744013101c803804141c104900c642c8482e00344042c94070302148009180500542c03280d002a14200c901f401121000240da2070824000c2150207003a001040101c0900003940741c8074064800380c2c1c03260200c2c1d4425012503403540b52910343c1c815220001400248207070062ba612280150800743c1d0500c0c5600800d8a01d403140c0c104a480a40b0791009110072181021090080090004140c801d41070403e04d60750103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 400800674 1250 400799424 400799479
    0xa0b090a0504021e030903031527070e030f10050a23040201030b090412080f071709010e0312190b22020f0406020d110706051209010e06010305060106030605 69
    0x30380d000302c3c081300c0e01c1c00c410401d15501e1007100340c55641c0b40380c940281c035240d9004540702181380d003800c074020115080c07040c4092424240c840803450700176010360868134901402000d4034204820500b010215403010310110203900b110800800d00d04192801a034203441c0c004128008403883c10030001200344801c0c0100c004400c00d101000741c2a2506e00040b17018000f24514284c001c51400c1c107000c1081000400c0400c0b4010303541e1030400c60b455001503003024210903103928001a142c80122600c2c1c038034140c07040703800c15034000c000242003600144081c00c41d00490190045404000104010f0805d03000ca5199411101c81d0100424803d4400084201103001c6912261111400d42160200103d030704071044490411049504c59966480003503407005404003400c00178000c84400166044000346280982c3d14503142c403410004400340c5c60342049402441e0900941d00d541c10a4014102840b529010394013840c05400c6c2981810310140c01d450890f03004038041c00101d0b48003d5503842c0e03294884076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 400801924 1250 400800674 400800679
    0xf0405040b0609033703050703050306031f021201050d051e0120071109040b070309030516051c051303030305060f03070801020408010c0503040c05010e1516020a0b090a05 75
    0x4841d24200701145403800303114002501886480c0c014400040318201e2a0070000c6003043c1d03400f600c500188070a401d001000b0004020400500400d00001d0143c1e0107164425005001c0742d00c2d0b51140344411005c184184a80c1c684c80b070b40020324040c0140784603036850141c40291120074484d0344507526590341e0658070007284402d000c9201c001188400a4020350000394200d03000680c2c0e642907400901d100e51180e00c3c02c41d071100e450a0310100c00c0c2005588144a10f4004081c10401c0e0b0310180140c0140460910840412900b000015420074080c40503040440c014070040405502c070f410b050540b075072000890030505c14180030150843e5a44503046041da03501d031502050940b5010081070000c2c000401c4103505019880c404544240705501500c11a5403a9000b4800e94010b40c4c826602c512055034041c0c681c0b005584148899402411001003445010b042c1c4080c0c070809001e006540c0c1c105050100b40c0c607500300410b07001d40c40c040c00e282018101a500d428688415000050804c00300ea116450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 400803174 1250 400801924 400801931
    0x60d021f031b180b0310081c1d1e04021b0a1205030c0301180905010e151f14150a0903020925080601090801020a02160803090d06090501061203020a03020708030f040504 74
    0x481446d250300d1144010480780045400214820149400b40c8080440840004004601c0032060211560b4034084450028040300010011411180c01450010402c16006502004043c40c00241014442d100d02013140161440501034506405001202c02040c010400280103200c00c10390300303d003200c0c11100c0040c415082503502e07044113009044a82e42c09025540b90060320307002c0f094003150406188900007030566190395045854845803d528104c03c10301c20324180180a201184e00d08080f568100074510480300641c410907610907400007840c0000201c080504200b141003031018240c001190100307000310020305c2040c01e464140c0352003c45040007901d00c0071665590288081320041c2403400020340d520719403520041e581d61000d2405071040b214105000488000102c02c1d5850344400800c034244200b025280e200151502c1d4a060f10555660b050001d2508101c6000307206c000d00c42d130040d00101025060107424505542e001310002d41080201c0040000130a0031902983c900f110f001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 400804424 1250 400803174 400803181
    0x31a0f06100c050a021f0f0f051803010f051e240904030e040507030212010506070f02090c0d15090c020105090601060f020a050102030a05160512060d021f031b180b03 73
    0x5502e4a18001400f0390000d80c0103488180322004005540ca0006c510b40303402c09030b18507040080742c5480582d6568000038605022030818000460003a0100c52402400072509211004001007151004c0c1d0b04a8440000c1d403001101182051100a078005001c9034102454a8540e401d95258a07000388150311440d101400101018064a00840725000c0504104424034012101a0003580003491865540b0a208000240c1d85060012180340d035501c10f10b00c2c2801c06883d4203100310400d001d000800201018800e440c0400540d11580130301c134020001228810b460602c503102240c441042c050216414041002040e40c00000c81c2411200d40d86050800d4408520080341029540840100107500000c148681001142c1045000d482032025100c0c1451a449050341c40e88501240007820794010b0f0300003252480e1144c60b00d01614005400d9480c020a120101c54401c000420180042540d501c030324513604942011111030b8070342604111980b0f40c404151070302036400c0d0340305a0f0340204001001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 400805674 1250 400804424 400804433
    0x31c0504090f140406050601020c0f101b2001080c0304020a1502161707050108070e06071103030a020115080307030c02100e0d080409050a0c080601030c0513031a0f06100c 75
    0x802d1a001c1142900f081605041c41c0070400341005840680c01881030410740f104170702e0304c48641080d14000400e0801c1c03280540030705492542c80310451a01c0700c484110311a021403401029201c0142c036030f041c109050801800013414069001c0c100328440c1c84140100030041c3c60383c05490003a29420100741c0e40d0b84050801c100e1a160300050400b0340e140d001400000d00e850b40880900820700c0c40e8098a003195199001158120011500c0c03e0005000410241c21410b00d20000c0c000c103801070b0a541400b011500200785580c1c001d00051005079541c0c44500c3e003c56000c20604060050100a10310702040c54800074070751000700c88040e1041c1d21041d07041c821123001d034003002d132000030250002281c030386603082103400383e002441001c001c03506200001d59043c041d44201c4a0040c0c0d203403520355881d180c80340118001c11000d14850f06005041050304c4204410000d1200194130420a8080601c5000a00414403c0251185042c400d4080c10b11100380da6900c82c0728102e564038601a50400d109041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 400806924 1250 400805674 400805681
    0xd0204110d0603080c010f0203060a17120406020328020c130e070b071b030c1403120f130e060616051203070c0605070e240405040c02070302031c0504090f 68
    0x400c0c0709241820010400180c1350260103c41850360007040382807a980d41210507444221a00c03540100101c4041c401c100468415000d103d200004455081803080d5004c000b541c01038005070b0269101103003450084021230200e419a00c81003841d8000c000d09048080e6032035135140f0010b48218044031042d1028401580901c1c400e02d04842110031403581c90381c000745240e1080800341c0304000c80c0030100310b601450061110460703600240c4e800c1064980070718101004046400f665050051500307041001d01000d000c2e00caa82c0b207660f01a5641c10721800b00000d01d45031584805101d0a500e0100724055a17030b001900c615516101040d01250101c0c60701ca810050350340d0700340c40006804424001035951141020fa03880d480343d08200415112220140e440183c940e00580d40060041550051609200d89000c0d24043d0f200300c2505090301c070000101540c0c00804402c0050b80021360410070b601c1d0401a00002d040d1285514589210441d80108184254050718600b140c507001104002707000c690 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 400808174 1250 400806924 400806937
    0xc020a03142803050108120c0312061c060b030c01020a1205030c1c0c11060609010501051602150d050c0a0c03030903140a08100609140d060902030d18090b0d020411 72
    0x1800b1440c08820500500106020b00504c0340500c120300c41c0c0300510300807004a8031440d152200450901440c444580d0282e00018041a003204c5014480e20040c03c4038001107081610441b00401c4036103200c010f161030711801038030751070465000700c0720100460380c0203141c0000e00b200c501d00b881d40ca40e295080751102e80324100398882c9403107110310f060030f00702551307031100000b5003155840710300f1010124011551481c00340c4416601070314603c0100602e40c040c0009281e511a0194440005a0303d600050f01c2c2494101103184851000241c000002e1241e20859500c4040700a001d8200303042ea02c0c008111080b84040102070541c3c5825150606001d000031002005040c2d04056544810107001003810101b03603104c24810712404030218031103024034086010b441d0400c003038a44500424040144c080c422a200707541103681da100c00e20150b202844061440c407900d031103465500c141d002510315500c503d980b04002c0186010b508071040e540340c0e91204d4506804039000700e00c00c56081c0000383c041c0300d03c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 400809424 1250 400808174 400808227
    0x302090a0222180c030605060d0603020f190e09031201170f01020901210e070806070807090f03230d0f08060a030c0320060a050d0c020a0314 62
    0x15010004904201c1e0014a04401003000011142072108401c1d51030190714082c0710301074082040d00c200050003c0d0300074001c0d030045150210300107a650003c90441e84c40a605804c0c0c4a80f2568140198209071030030030354805c02605e0250a9503c60300041002d0195400340740c24101840002c42c00888082003552002c0c1c200c0b960480c02c2c0e50390f40190082c0e000032141d0f00f1915015040c0d0900c100c28041c0300f074400b50201a164103c48882013159181c0088d203100b03a5205060392800492040d40042001c28042c00b201801441181446600a030100e132004003003030100261001f040c402c0c00f075a10041d404980e0700c640040c01d079042c201114900345410048006803403090940a5a00940c0004c0c0d000790703001181c440d017440b607c0b22003c1c4200c141241c04080c2a440b614041080014080c0400e0b032461508000720440480104c0300280507036008406100000c1c1c03000c141c41c52201b066118603013034001e0034002041c950340e4030790b4040c0c18030180390a0003031070520104141d442c100d2000c12450b00070456 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 400810674 1250 400809424 400809439
    0x904030c1a060310050403021c03090b010312110102072d060e240112111206010b041805070e040b010918140106020f0c0f0d1b0311010c080d0e03040302 67
    0x10621900340c0d400c040b142c840c880e105420301a00c0d403102c01d01c1080c3c003658060b40500880c20203101400180004600e400b002c0654032101c52010680c1500c00901952091101030b1b0001741404008181d1a01c003800440d160b441041010000761850344402880100c401010744c0000e428000940c5651000c14050907103405c022440741d0302c00d4040340c811003480000d2126a0b000309030081c01001d036002405000441031110a080002c0794a070303521000803c40c0204070110304dd07642808503003442002e03404100181c5002c1000d114a44046081c1c01006802d218200701a1501d8000141011042c0c000140175a80d590003664559116001001c06491880500b81003240314840000c0100030302d11241c0c030002c03d50030011031680d10105407800e02000000060801074110000c10007407000c160080c9038001c518081000c0001c0100202d40054403240c03000950729890f50400da4150403800d142d4504200c40b51a161340010703542c0050324a515620303c0c000400e07a483c8400245035108580003c0d500002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 400811924 1250 400810674 400810703
    0xb0a171305160302090702070f050f0d050d0c060b01030903200106050a1205060108070810021c060312020c010e1c0204090209042009010e0a0b010c0c0b040501020105010f050d020904030c 82
    0x4000c02d0040450344269a0261107075900c05049890b600e5034000d04655001c4180100050701d80512100d600070001000301010101c03584e68240380c9100c3c2c80e900030210303074140e103090280b01d098481d640d0524001c0c02c05101c0c1c0c2419031323001014030880c1d02c8003a1895582c02c1034910000001d51101d000b9110240007000080d03140e20b030b061410105904100c40f0751096900110782840d004c203c1400f251290740003002d18207030481c0c110010b034118021f00b4082603c6000e09540c004124095200114000e01e628050b00c940d882d0000e00f00b00c401e41c0110305000c900d51480e8140d4854049404170710305444080c2d0340310045031000a0241c50302000c0a90300c000358100b400306100408070802c401e103180181104d08003000c0014001c0d020000d11510603010002e00c000b030903a44654000b000301c004145840404e40426a85020000007960403440c035283c0003240c140300c5542c09101d094050088504070703c1c1ca0364a40380c0010034404250000a01511060022a08041c003c0c0b0a090700c00d64441010341e1942d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 400813174 1250 400811924 400811953
    0x3150e010e0d03060e0a02040b07170903060103080d0c021204121403030708190e060403030203130f060f0c020118060b19080a020f0f09040308130c090606090b0a171305 74
    0x28460280f0310f80a41385c3c03404a8a5200e05100b200c044468850449080444070784076450340502c101e41c00058044c0400c44403c6554050213101d02071031140c401c0c3e588034107407a429001100c1c00c2c0008081503510040203682c0c52a00c60055804039003581400815180d56440c11000301d207100810301c00f40c1c2c40040180800c040c1c200384c03080d11500d142a0350382c02c20034507192210142c0f42d4500d040400794110102003000b0038401d400640d03120b5002c0c1c040c1c814884059a6904801c10017220990307035680d803020011114885401030004081c2c9030700c0240100818604c00340302441c1209001002c00e42d07610000d1406803a4a65506c003003100a20f8010070b0135540d0300c00b00e030301c0f01c00d4180102c2c803503150f84e030305a02d0030b240041e151401108041c0214806903100d40e0240c441c0803026058030f50114020300a100001c00c0b010007500584540b07400400c016141c8000a00018071982200c8100d61080c401c1d2510795910903003603203000c423010540040c0e545071541088040100e06101030058016161011a03c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 400814424 1250 400813174 400813181
    0x20130e07090b0d060518010609062307060902040e010903081303090b0a0e01020d0807081306110a02150f0105180c1e1201050a0503100e0f01052401030603150e010e0d03 74
    0x407901541c0c2ea070311500803646ca038070172039209000b0200410451032040c400d9a1142e2591b034211804202d0b049030240c80318003a100382d50084002200c1c0300d500c904929003141001c0c0607045000c02e0b148000d01c00502d6030364010300b400c0c4004080ca50010f41c440011420715101f81903400c001c02c03880d0f90456886072046801000740c205800d840d405407041c401c904500034403980c989841540d40341da0311141a01e0f081c480403040074000c0d50580380180c65022510380301c07524000900c2043c5140d0000d22540307400e01c1c0c03603d400d6080200403912403101c200041005881d05d113004030000c4103240103400e890744c4050604146001d044100b030501c00303081c0003a000510300a0020841c08a080c042c0c456030380e07a41c0c02004520f09490040d980c054200310104600c42480380c0080740c0f40d50811003601c01204185008500f1034070211104090320f400808450418100c0e01c03000880d541080c81e050108908580b904450400e04104034000607540311700542c1555401e42c0480400c01d084000c0c3c4840da0724040005026 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 400815674 1250 400814424 400814429
    0x60602061803040b0901030b041517060108120f03090f10020d1d1e010b040e070f0b07020d02101206060905030f01090c09020f04090f20130e07090b0d06 67
    0x101d04215101d904004004103607012900400c0c00c981c44c20405900440150071010a00740d04035031184131002411150500c6030740030b40f0080e49482003d01c04913070b8242c50044180d0103d101504807a101d900c410881c81c040b40d0f83c03030409154040d43ea03151124010b1400000d210700303050764000c0c0c0030500b0410a15070014080b0344100c1100307200d00c00400c0525816543e4901c801380f002e601400810706152401d05c100000d58000c0000000d0901e6140007242c103a505030700214500d038200483c01c0c004010309480b071402405030840803c2c18200c403a40070900388968040d0282c03003044136083c1028070912998401d00300c0c1a0404c03042c0000c0765100c8001e000c10400b4040d10f031107030040c00c000e6410940144201031000d0341240031000b0b0305103090700880c000d41c031a10800800200410020406803014007034400b02d000808170000700040d400528040108080c0341d07a0340107c1c4204003043c4005860403660040d1340415010010a4545040a68035100c25038888020781c10089055880300702030f81d0146c0d04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 400816924 1250 400815674 400815691
    0x40801111201060206090a060507020102090405150406081513060603080d06150203131712041205060106030902031b0f04180210110d08150a0801090c0b03060a090b040f06060206 78
    0x321643c03628000d913100d031744c1107480003043e501007405200854144c0d08040c0d0803502900005180c403000902040546404072001c0c41e40c0c00402440d805c5c0d44c10305110b85001407070080e000c0d20301428010304001c20f03500301420b40500c09850b115640244091603001000440d40b00c900c042e91030703d44601d090080c104510400d540807030310241d4822403600110480350744202c0d100c494890f06051041290020501c4070100383c00d4400c0401552002071800010301c0035000038a84038030350b9101d5140140c64144140c1014041500b02041c01c070060710001404080c03c1c04501ca422a03400190340402c0c448418082181d505c20b040c014200c007403007003042080085a000341d616102d52416a1015110880d00003803480007540f200707a810301c49910600c0f0042e04141c481c401c1c078030003203141800558184110f4101e10b1440c1d5407011031200708640301c000c01e001003282504490442c50281c0025014503400d203e8480260384890b81d014040d500c5070f205110700d04024001f080003903110a0000e5907804100d40c25075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 400818174 1250 400816924 400816957
    0x40303030b1504080c040e01060f0e011503150506160605130302010f0203060102210906030c0309010e0109020f0105070807050d0e010f05031311010c0b0f1f1203050f04080111 77
    0x5101d002c5150448083d18030340402480b4048030309050000800c07010790b144800c0c1d50b03a00c4010a6540c103001301c0d0b00c01000000c070701444c154105041d49030700c000e60003281c0d010b05141c54050b005550707030240300d14200c9400f02c0c0da084d00c6001580b00c2040c00040000300800c031514110421010040142e42c2500f298065030007045032040800d0031800b00c1c841a078540d40540e0010780c040a005218124000300d23000b01e0407005090110302d80202e00650410740c0c1c180f12031030000c4100000d5031001d100e108641c014490084c086281e039600480c1846c80e00c81d04250411030002001018054172038115a0001d07402001c0328410b1203214001130041103c448058000b40014040c001e03e144298140d034050a50300010825010469540b01f95445004036000d043c03203100342400780440e8031040c800b0321034807400750104468506405481c00c1c84496466007c84481420b41c2403001024100030800301c9585410484d03500e52000c0c0c2454001d00440d030000d0940d60030658110400c0074460b0103420b00034070651030030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 400819424 1250 400818174 400818199
    0x1090230010902030405030d11270a09020c0a0206070c030501051008030d020304031101090c0e06060c03121012060b040f0905150705040f0e0906070e0d0305130b040303030b 76
    0x5580010030350a039162400c040c100501c1024125401590040e106908403894602205144019204408051140490041074048603c0c000b0303071a100c95020580c1038000004000c0340052080180d60040101142d0f0114903001481420455401000d40081071103032200c907503107040c107102c26282c0002c17078540d421321b0045040d0350341c520b8a0314141d9040102440c1040818039401d030080d04006d00903400c000f100303c0c4c2c40304400802c0c491114000d019400201e0410700388104024440c0c405403001e401804100300311195500003000355010040001211000354481c0050b51a003440c0c1c41d0010b000a411a20b95201080b40d65840340c0a00741c0140c40501c10700802d00c040340202c030700c41400600b040c0c006256080002c0d402d6a00d0b2035009440c1c0c10007600b0315450724080001c00300b42c2e4002e0050600d405041c070810807010010164441c01c1c51030045c00c6140080080b40002c019000c0040500001280744da0014194094060140003809646a00c480d03481c180100030741070390f0000600602d0300c1481c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 400820674 1250 400819424 400819477
    0xf04090e0c0a06050a0c0c0b0315010203030610030b0307090507050408070f050f10090b0426010e0a140102190e100c020a061b0206030106080402030f06070c02010809010b09010902 79
    0x12a42081c20040144803003a00d010411350304c5038090204401007010030041140011100c001000142c00c0010106840789401f980c0209100d0381c0c1010326041d03510620030407106644001c3c3c80d20340c408461801064046124020a10f0440180c0000851a04002c10800c9407544030019004a03003501c81140d000d15075901400c0410000c50085030317000400f0341801c8072281004039806108a0491400f001c1d0f01d80d0340e2100640c0d5800c550411090341112440b03c1411151950048180c40d03565030003044000131140c012565528406130040280030340344060300c00404294103480003064490520340c80840c680034000d0200c80003001580c46240000201558581700b0102c103000300358043d0582c124030b414000305580110822a146d0610841445240016210840510300034803154a03001034a00f03082c41050b04101c45084c1e290400c0d48442d08000c04194040d403015802ca03020b00303100c2c5403a220341d200300b40540b02c1c01114940011211000044201d1070f80e009113560040342c001c824804000181d0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 400821924 1250 400820674 400820683
    0x20109060c0b071d0d050c0307141c0807050609010b0901080a0c14031615320306040f0c0c03021b061c06030b130506010501050c2a060f04090e 63
    0x1c1c05031031104000000f030507050042c83c01030078584078120440c800c50300c4400091203020110b641204c4130b801417003102c0c1541c11b04000102c0035044182c030b524003181c2001c0c0417512481c00004442039069880342e124043c0070b295001c69410760b4009090b905a0f240000d19107000c3d10038240705901403500b410000038030f04d5020440b034a0309540320281c0b000b0f41d85004400a0010a00c80700907074540510504450f40d480c020800e00700411140144544a0605000103055080f00d42c40141c90807450a25041800400711240c0380c10a1403407141710341b80c0d2900c0001c00c0082120300e44182100745042c4c0148800d42e0010f0604082074820707400c4821860018088200e443d0015003d0345c0c001030705120805100d140034012000348800f143c00001d1665a13500c0350012800b0036601e9020719051290103c0a000c0c0030700041f40500800c0c00c040303160800e041d0317a00c2d0f6a41c00d194141480300e500403105901c17000e40000a0014000300501694468000582442e4158041e214140845280001c498110100881c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 400823174 1250 400821924 400821947
    0x230030f010f090b100e120307030207050f0607030c0b07050f0319050a0b1c021f2001020703200703061b030509160b030c0409050123032b0302190c02010906 69
    0x7805088008074511050340d01c0785131082a80d5004440d40688400c1f560304001a085450007980101203042c03500003408120b401050800c1d00a6804000080c0401d4015a01c03a0209500621100b05a40c07501c004451a0003000c2d14084001c00000c00d020381122040b402d080e214402200401a5495103030f8554110b8000740c2803070b40c02078081138540004946e038441190b03000c0c4c00500410048a2a00c1246d5400010700c00c1007000b00d844040d1641900031400c205155400c0700710001c514044560300c0140400c101ca4400324004424001e17000062201401244011540a041404801040c1c001c02c0140300302c0c1080500024030b40300024605510004840f21140650742e8140030141c1130114018465000400103c504841044001900c90980c842c00e030013031408503200310900034030020517012000b00d9441c1c58440c8d03008400c00e001d00140b521441da4040c010040b1000b90b09a511810740c0603002ea515a61044001c1007114016190007044034420903200360b80d050700c0181c131814180e400324400c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 400824424 1250 400823174 400823179
    0xc0a030209060d050a05030d272006071403031f030804121a040c05090c0913020a020a061a211c0c210306060c02010230030f010f090b 59
    0x1c0400c8803070405180a2070030a0107401070b02c2003c0f00c6901c507249107a0100d41c0b54040142e98208103455540c105200e801900f0311003ca11812030980d44600c0000c40c02030103404030b190741101c01417003542d41e58021107842c01e9000d20080340c451441c00003681c0700e42046400d60806000b601070b8105111101045030252584011a281010705100c0b104042c615036040444820340c5004640e100e15000c00e40052080f44104003201c200d90905040c4031000c500a0548504800c05100800c0c423a0355038810b07901420303081a001a00c070b42c50904224601030309074401805140c03400440c0c90a86036805450300071048250741440c8400c41001030741070100180071205042d50011118149180c019502c01407070640645045070405400317468074864401403000c949000b400324601c1c1980030b074240c040d203002003105060080081c0745680002c0c3d2608070191400c40c042290195500401a555001d504104401d2111540f40d180007821841030f00801e014460008a0b107110002d489a481e006031850840301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 400825674 1250 400824424 400824439
    0x6020a081e0f0c06150427021f02010b0418020d03050918011502060702070602030906071e050a03120209010e0409020d15020a1805010f1b05030a09080c0a0302 70
    0x105141c000001c0c0d8440c601d088280080041000e6030b00c04402a21195880c0d40181c2074074188045044e004030500450300d40524141440300300e4501c81102e120100f55452400c0d45d20812540c0700265801601c2141e20303c404100e00f0021000c1541544210781c00380041da0100901d0108005411030383c80c0160b070080d4060710483c10354000038841c0d406414030010151003d0030b054400304407401030f036100340c0002900418000b002c50f01300b0b030f04002c2d2a40203800d0703001501c2c10034201a0001d440f0f11568201500915000950310100440c5603150b0b200c404030b4031901c5607000024501161a60762034281900000c250400080f06641707684204c0e801458142c45100c4904078800600015210454003640c1c084944840000410551703036850214010640c0016078504810030064403104492072540c59040d42c0823024410740c0d070400100400e641c810300b4580710445020b1903040030311a10f044010014000420405d08450700311440506807a450700698078556212402d002c9403096a200c0030303602440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 400826924 1250 400825674 400825687
    0x30d0201090201080c070b01210b0f041a04050730120206010b03090c01030c05190306050a32120f06010f05041a01050a121401060305090a0b0f190507030501060906020a08 75
    0x8810410100c04442c034907840c2907150302b501ca43e0201c0c17a040302d1440201030381408000411103803280c0c2c1c007a180440b84d100341060410f600d0b000e590700c0281c002c52000c0d06107031888507408020500558400c00c4502003109110b85586446005407d0b0002c0c80c1000d4410f0384008501403500d642540d00c190549001445624214001100600800e5002600f40081040312001c28001441c03548041559034402045461500080c003403515400c1d4407180700d80503074540c2c90030070403854507041e64882c4060b0516000d00c290400014800c1b48140680c8880b0310400141e4280107402140d000c1c1290700250892980350345d140240b1080c1c448141e010100b42070b034134843d00401d41c050703400791100384035500d4103030503402c01c04610f1401c076101140c0d417002130b042c298010000f09925008195121140030058829001d480d99030014151019011030101000c0b200042c0d000625041041c1102c6402902070085041650016004040c00c0c0600000a428000007184450000501c4145241e015003880d19111 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 400828174 1250 400826924 400826939
    0x30601140d06020d141503010c0806060705011d0105040221100e03191211041d07172401050405031f0e0d051804150303050306040b030d0201090201080c070b01 70
    0x850074007100c10300d500f40b081100564151145680c0d180e00800d5048007130030080459481d00102070a00e6100c0d07810000040845c960190b29950001004e8a1003078030781320a40f501501622100041ca0503021b4001c1184060040c1500700c280900c0c0266142d0300325600c1c620286803601e16810b0b84100640c050302905002c400a42d01c01002c202802d011b481c18141c0d8800d001200d541c1c00b0006c580041c4903034800f40c41e08601485400300c610503444850745464075024845110446c155280400c0003e000d00189800d03000c0d51b211102900d00360101200d5107490078840192440128a000444011140d10312095010300102d400762503004005021850302902d880280c882d00200704084140c950814a1647d4010006443d00d0f195549545880e18440fa450000350201140c100e4411400d00062a6405c900100c4107415241c16240840d0740f580c0f0500854003030100c0384600b903014400c0760300c0c21101ea40d0640c001c00140d0304c00d0f0f0f520f113902d440350101082c241c014000301038a10700707032310004000e1407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 400829424 1250 400828174 400828189
    0xf04060503040515070c0b0a0c0f2102040303031e05061c020a050306070201020418060b0909070323100902281709030a091e03020405060a0807080c0f03060114 70
    0x2620803030132a0290f1000c1840c4003e11041075540001013141020b40b0781c10440e006a00302ea01412568040050f0b0000e190024007c10840c0c4408051100c600727440c140ca003d1840c000c8000c3d9584110556880ea41ca20b4010014258080400e1014145444244901c450381c0501e90045200900c81181c841b1200390400308083c0840d01264000320100300010b49440c1881071500c1000b05030001070b110313841c0848600324034240080d03541047e480c0200c140000d4036800c003954140705050390300d91b045541d01d4506800404602c0c514009505801c16012a00100341007121f01c03400000b03004207611a03507103244601768050b14980c003090b140030042c4c120100042c800c500e400b5900e50721f043c1c000120201c10301080d8840c19181410b068100007500b4040e80c3e0802c8030710008114002ea002a54a1001645141c640c0c81c0c1c04020300c120385440101c0c0d081c0c0e5800007114050142c2c6400e42e034603143d03640441a60f56508084960161051540d010701902e00418554102c480d01040009600311032820003802c1d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 400830674 1250 400829424 400829431
    0x2030307021002131206230f0403050d0b0306130c050f0a03060e15070305010e100503060a0b1f0203030f0105090f0c09060d0c11150702071e1208040303080c0f04060503 74
    0x4035410f0f0300c0006502d6900550281406d00458000030080f2244c1d80803805900e10020111951a0200c2804196000c942034280d001d40c142c5481030302c0d4034501c0f40c990050844178a020340e0520661043c81020302146440111070342c8100103810600f6541d80c14403014268080d102a03000007400070406c0401c0842d044400100294002c1d80d45000c0200150215000c003525050f00190b40c03040144032841d008011181c1140d0219084600c040c40c01c0002991040d00600c0012003e496154a84050700d17040b2103188061800c0100c0314101c0050207009680b0b8108403945800e207400d01700005882d080a2000718081e12401c09007528903039801c1070345216a403141007400c0d00007200b000007100c1c03207683d8450004030241c01e85e40c0c821040d0360089201e1902d500c1c510032840301000c0209010503c2d0b0009600406c6401c540708100000c200b48038203c0b01300000ba13001e5403841180460340e0080000020041c415240700362502e20640c1c8034928818103a010350540c45082d1203080205010180c0108083d590 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 400831924 1250 400830674 400830697
    0xa0608071802090d2004020f0906130510121505010f18050a12210203031311090a290108191e06061d030c0d030c0b070c021002030307021002 62
    0x2410310300202052480d4082130095501e00c0031303280f041d210320b1900c400002d19094200c41c02d5040a00f0095172111a10035031075200d1180800180548042a4203843c11000f04402071806501850861000d000001d924544100c00c52a01f9030a40810780c241c120003003500e0045e52040e0040d40b12081c1501c05403280c0303c066100707400190001440c0c6d600d040c801005480c41b210080501043c1d8600140c0081c0609140c1c040e00d1401040c1d550755941c00401d4981c807400011410f14810700b241002002d0480e0403044540144580080100801c070f10b4208200e490011100c6201c1d4211800380050740b4542c501000c0e0001e4000000703c1e0b150860140c2c0c984040c001054000341c0514003031200c03040c0305805000401025103e107410840d01f50018089807194101014145200c0d05090010b41c980c00200603640c4119004096403003403600c40d1040500305940f000c030000c5941010386002e0032030004c40904130b2090100c40e48034090644044140c0303001c1c6d00c0035002400c05412100d488000b03500111032445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 400833174 1250 400831924 400831927
    0xf020c190b0112080d2307020312060f06120a06030b010b1c1116060605100c0503040302210604050a0c0f0305030d0e03090402130f08060105031207050c0d050f060a0608071802 77
    0x181c5d58252449460412201c072440c1540280c1130300a0440300d814003e010b00c09541061200b401c5460540203500d5101d0781c111000720360600500c001502c40e0041c2ca60031070741c4603101001c04c8114105c1c0d40c0041c0c1502c1c0103030302105041c0e81c0d40c2c6600080c5e21501c4000c10001208407038500e0102140e070440840544401c02131070a1807401610308400c0c12081100383e81054482c0c5041105040600c64000394014916054960301000c2d245d482d581d104511000b07029040b205441202e14002c0110550100341e6001030354024145400d0a554804500c14280e0700013403640d0000811501a01c61102100c0d8803101550405455428104c002d003000030300410140030400824600d07940754402440041c541070507072904036051210a401042c40e82c0c000b01c10075801140180001c0d03800164030045010034081c01e03550b4844500e40503050840f40039500350030050a14843c020000041000e8210780942c03400c48850b90303a4042524103407640c505c500889a04148002e00c9541808100c04400e03880514025 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 400834424 1250 400833174 400833187
    0x207050d12181b06080907061b021831032303071107051c08030403030209040c030912020a17090d0b012601060303080a09020d060f020c190b011208 65
    0x341a01c2950540865989000e201151a460702030440f0001408581ca003010b103034605102055502c40c007a00075141800f0460360078000c40030421540c280d040c0d0380a405c07410840641211a00c05600543e6003800c0c1c003592000c2401c072203002030445182003c140740720384025840c03a14150398041d43c481071800d81c980c2036110005110826001103000d007039640e4450001000312018141006903030707004640328800d40c50b03003841e21a560a001c3c003065034020100356074075115840d00360000c3c4108114a03070010f0602290807080d0390164004038003207010b02d24101c4407040d0074000f01c6e02c031103481c00010100b00c041d12041031202490340281031946006408481c1d00101a00c1d18080310909910a00380b4044a644496198140002050740880090000c5c0210303411542c001d08514030040811552603039034541c00e0255a41e0002e80030305a50046410440c210f8503c107103001940c804402d06a4a2081c60042446030843d0420b0f5214a90015500701d080c4e424524405080c00c01080300359203100060101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 400835674 1250 400834424 400834451
    0x10081e0a0f05040b1f030f080a09030c08030403120509033301080601031407080c01120b04051e15060304140a1704080d0914130608011e0509010207050d12 68
    0x240c50040e80200c44000b0145417040c0603e074208800c16039a0400180414204002044c0012111000b54040300c4543c13904d409940444250245600141540d48442400283caa40c040001c0c420389000d0429181205c4c1e0840c002e8030240303d10582d280d010f0344551230303800c0100d12030380c02d1103c88281722481725030180c10402804001c0d03d0030b8010b505141c0181c0010810003000c640c1e0581041c2c890300c080d018052130300c0d50041d11070452101036418002030341c4000c611549182e1000866000c000c200304500c0c14091154819041040c40b64019415400089580402c03040c20680000304000c100d10700e95503d543e070300d41c0200450700c100c01540c4540702500c0000791308218092904081c0071005500d5510701004a4a4039203194040418010b000c641030049403c0803200000703402e42510340400700060b0812000007032016520542c215460031600c04020000074015020030442c0c24002d100d03036100d41d0309a03801c034840c07c2c40091103944442101c1b84614010464100307002010140080c00000b4a0f50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 400836924 1250 400835674 400835681
    0x190e0a050607112404150e0d06050f07030e030706090f0206120403030b0117180a1b03021207080607140d0903080901050a0507090501051305040e0102040510081e0a0f 73
    0x2d045030016600c80c07040002d4100b542640c90f203200f076540346203d50606208844064466070240c40c0c42c1c4014003591301c980b11300a12200d06116400b509011990b80301c0e0034030000a2034141c4568005404c50004110800c1c46130003aa1000341481c4081c1d03140c0341036130395024002c0201d44021140b0081c0a40050301581e5400042c001c109550803d5094074a803030b14004049513180c140309818403442a107140b511030050b041e0f05901444001d091f02014281901d02490110301e01700061003034a4880034105503850301ca5040040707a2095911003948006015519220800c41c00f92443c580e11281c00201210310800d590520014451200c919002c5840c12800c2958902001980414154800c1c44402002485425404000184201300908104e000100001001c0c4150390406c4004683c102452011849860003001700610800192a1074610a4040d402a104080c41452503442e452402402400000c1c81003a503000d1034801c8484002c02c8403440c0401a0200005551b102c980380c0844100e0310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 400838174 1250 400836924 400836937
    0xd2c040f02040503190803180c041b090801110a05030c13120b0a0b0d02040b06090d11030d090b040506181315060c031d0301090803240402190e0a0506 66
    0x380980ea0740c0c14003003414540840070041c52180c205681c101400701c2d1801b4140c940040301c14103054900c8404210540c2342600100d0295072052908601200c200031076070b4a41800b4504c1e8a0744202c841d034601c0f0107070072511540b0b450100b07001c041104900179841480119800010035503240e0812501020590740d103120354100b484900140b010036001d1204c440a4a603004410072028002c0c010b20b8000300385051610b510090180fa04d5000c400b5056840500f030303e441210242a00031b4840247c00d03c5444d03442040c4040d4004d025130301c0c207041c5c100c1c4501c0c012010355004403041450a8075040034403031642e100713442140810700c3c000c1c0f54840702c2d503d00c0e071290f10320701d000b02d03001c106403800f0f100d03006181e04d2540c840000d00810b0381041c0c002036003009207420412520584003c2d220032010210f409070003e0307403006000300000000c004071251000e1100c600e41c407002d40e15100840c51041448100d2040410540c5582d48468802c40e00521075180600340c5d1714017600900b00f01d039488010400c41c2c1c0150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 400839424 1250 400838174 400838201
    0x1080d2111130603021e0a0c030806040e33060a181e1e05011809050a05030316030501050a0b1603030609021305011103040f03140703050d0c1101020d2c04 68
    0x650140b2128850488a20b4101042d46e210310b0a80c142c000500f91003482038005041c000c224000a69075a510b80c080c800c040c0a04064070000c0f1000c501c00708003104240f21003003044a81441000148032141300b82c911811000d040182200d0400c000e250b90043d010688401d100d072282c0f502490724254114806100444000219074034000002c8003404114800104503140d103480c2c01040390b101482038581400000c2013001644c0603180c10f180741000e0000034040c000303110000501001c40240300c4040060344469a08020690f02c66040224500b01071107140104513041c85105c001206540803034050b540300781800104907030f40b07403900702c141c0c0c1050119202d420301c000b00401c070650f00001d040da1949140342c065890103003006100c20040d0018000506040001003445064410800c021800340d60010308131607810000c0300d0300400e04140d070b450464020841d01345442c025400041c40070f045c41c00c00d48507003641c6886440402c1140b284880190041a010050502070361158880c0314494240c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 400840674 1250 400839424 400839427
    0x31d13090b0f0408040512010605060c06041506030803010b1b0f0f011a060a030e0a0c0902030402040b100c0312110304050609070501080403020a060b0103020d050f01080d211113060302 81
    0x41e0900c03006501005141411907402e41040100044045045034180c40d17080f15040d2607e00010021070040a2603040240c10040004460158510010b0218410f034031071701e448616400d0403280030b01542c60701d10009102c030700c0c1400140080081c90740a01200260314145c84100f030a07961080f0700d0246292804052074102254401d8640c10078041d180d9049607100310a500341403540d011030780d144503504400301003555800f00100c485000740304824095801507042e0601c5a1200300303840080d0b0050320100d10540ca407114114442c101074000d68140d00050310b07010352201d440d49082d0f4545140c0001e05440c0ca607507880703840c000c182600107180036a00410050004e444e100102900d04640340d0450f03414811000c04000c002035000415211042c0d002c040070420a001200590207400f40d4120500160b003400c0411044035101c001780d0f41250120421110107040c42c40c81502c0009e000c103132000060350703000030792215002e0680083c0c0007103841c1c5000e14a0840900c04180d0320101540108002a40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 400841924 1250 400840674 400840691
    0x1b030e04020d0906050a0b0306270303070f03150302030a030e03120d090c06030b0310020c010b1c05010506040c0c0204021b1c08060105030709030b090f0106080304081513031d13 78
    0x191380c49519030101001908106150b4910700095450600800422140072640c2c10b4080910585511a0070030160808603a2223041018015090303405001200c0000f900d84201500e907500c050001904894019015101006440e28101d4207140e981100d01d0309881180fa0405500207d08024442d241c1025800500084217103002003243d07415074030820406040c4a484812607401080558942238500d42c01a500d030382402120740900b02c69003660b98414000b00108885680b004404055507115800810250f038503007080200312011f032440500010380081c00c15005050590041002c081c201c00589000a035940c0c08500e400300303c1031071201035100d020940000c0340e0844804c5070014002d092050461030008030041044140d484013814244690000c192566014403110520741ca1100090081c40d07210210156603a0091103185180e00ca4001300900396141088000d0040c45001c14190581035640c80458100700000641c0309450250080003104e0364410014080c0031500301e074081030070344 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 400843174 1250 400841924 400841933
    0x306190f09061a030702031c0b090c122401050702010309080301060512070819051f0609181506080915160801080a020907080711060a0506040e030a1b030e04020d09 72
    0x51403400f200b243e2100500038002019004000c0c1c40d8030428a54a280350120044000c0d805480d0344030380306810a4001e0309100034000c00da8000e110664007000b41205030346806030000c183d010103640c1c01b0f1200c981151303600c03020f44c0700b05d00400c6010300500d80401c07001c4181d100d10f0200e6002b03901c40004910001400f021107401d510380c5030f40c4510b181c14107011074500032900d1403804205140c41c6001640d82c40008003405800740c2c001006469410307000f0403650b02e5040c05804564603000344003203180700f6550200301d040c5501500007110f43c0341a5581c600c80c58940d0694440101078400011802110600d540e50941061007600c10044100040c0c1103021200c0c0150a60106070420348080d08603502000158441d44005c0350003102516040d1074542d20340204403030107000c2c410725403224010300040c13240d550303040c3d00075a004810480e8100601348208007807030b603244941a000d001080f01b503150103000a5000b07030000b50960203030802001103c406d000150482c1c0c0403401c2040300b10340d174410350030511 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 400844424 1250 400843174 400843199
    0xa2604080a120822022b061a1c0606150903020103060b0f0304020d030509030a0515060f0a061206051215070302040b090f03031201030308160c080306190f0906 70
    0x1040a03003490b80302c2d410142e402d440308110040400410741225808141107480d42c120301d442c6036a00311442c0161482000a250710010411400c2d6502c50030180c13220809070b50008007403180c000081010000c445289c0c1304d000514403a0406036540c595403407001511120382c01c007494210a481d66070400090540c40007401b150325a80054000d440244038204214009500b02d1743c0254048031501c0101d141464121000d10400c140f041c3c02d400b40c00c000c0e0040050016a0b44800040c42c80e00505070750301c22050010044801824550149014000b0094280103501040500008130320100700c2c00c0c2c0390340c0032032055054450b05540e19031005016034100100e40c204240c000c0c3c0e0a280c10340c035040c0b5001d17955000c3d01580b401039100703492482c042080c0d0b55007002107610140b840560742600e5030b0b607400c015100c4030044454981d04050540030001c41d500c681c82640403550b1241c00360707042d51215400d1040d034008400c0c81d8121080f8108010841c4001007024100610700201c01192803400e001030031100c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 400845674 1250 400844424 400844453
    0x1906090b040b0414130204091d0a03170a09020d0b240a150c021903020102120924070c090b01110309060711060d090804090c050c0a2604080a 62
    0x10350050006020a60780e4508807001c941141e81c86124600322100020b08241c0094200c010091000900003400f9480d50070400040b003c0d0703103541c43c501122010054549481100c0100010360a0b40c240e015544840701140e0011003504002801303410300c0d07010901380182350800f6504c910740d840801504c07a042c0141e100c00071001c014080352840408020443d000c4803030003101c0c2c80c2425038045031102441242c0c045101070300100601e042c400542c0ca4a40c04d80103a02080e4014005c01c03626202c002c4200f01183c501c0b8201801001e55000548120700c050302820300c00a080000801c003030000f02c0c61040c50701029102e061400207072601100d0015298010780c1080c105a42c01c1030080e55010f64505058494042e00318034a0403015858400050307181c030815042142d2a460042051305005600028000b5a150041c0c10405c0f031401c0a000c1c0c9a0f80903641941d003c5502c000c5614001518048064801302188600410074a903100d03400402a00729400184050380a950700c0803d002d40410100d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 400846924 1250 400845674 400845689
    0x20c010203060f0d0b010303030c30050714030c0702040b120c01090f08060c030703090c0b0304060501060e030a0f21081e09030a11070b070f0627021e190609 69
    0x6981180c1c0e80d82d032150f0a0305200c048c040c10359400784034480e40e008114494401c800d003000c000c5100c034088101c01380740d4a01c000c03002d0603e03e800d00203846540201e40d1070b030400900004280c25a07540030304d03000d8140e0000d0310803070700f06498604023101750700d0300c1961903011a0460007130f250014241d800140000055442048130524084042285240100319036410a4030701c5141540c80e074a00d0300c154080d01d00c41c44000c21a462100001441d9100307100a0360080788620024040fa90380c1700f0084854004451040f58540c211900c10f100185a0012031484244036000c140d82c25031a404c030401c5940c50000070540420204030030090480d172031105c121002c40c1310702d0001196040041d001a82c03401203455503814480310601c07039442c1100402c44c080044c03081075005a9204151b240061007105540c101b140c0e01e80c10545221401400046d003003d019002d02e864030340c1d0a0300c507000c01c10240c4185105070111800200b03004c0c4903072150b1603c800b105900b80e0708034200c641380800007800000160702500c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 400848174 1250 400846924 400846939
    0x5070b1602031c0509040207020a0b04030c03030e0603012111120c0306061905220903031406010309080306010509010504090504080703081008060402090c1b06070e0415170a0501020c010203060f 85
    0xa00260804d090300c4136a0816500180c0b20000381c80840c003902e03000e40100304043c4020400004000343c00e03202d42c1c00d82e8440d41e1115000081c00c81030017010300081c01228034007881c602d0a0a040e101f080c801c5500c990161042c140751740e8444001ca6900b20302c043c0990f41075004640d89012030308041102c5d0390464816500302c813100c10503440d107003558503050188500c10900319581140704134046804200f04050041c0c2000151f8842c6006002082580b0800c1c8100241100107046036000b4440c002d0115041612240f445d038410f001100c96502c5051400d040c03040c02c4c0b0001c03807520341074403895100702d114420301540c0700010b0034084c3c0b07080001881400f60f40242c8006008800300825840d030403070360650742501e075500c6040d0b45447e10b005240f44421640c2c000702c46040400c0340040c206001700f507143c49141030020920180404e0302c101180325038031149251010440c42c1d11099120303071100c5445042d03452400d4203aa030305003a68040e8886480036900402449241d203413100c10200d92040484500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 400849424 1250 400848174 400848223
    0x160e0a03020f040903050d0e06040b060f150c0a06060801090302060c1908150d050a021009030c120501110301030804060e040506010c172a1203101205070b160203 71
    0xb42c401c00501e010a000740d4458404c0010513006500340d400a82c2d00c01414066800400010342e5075100848055170a0a410804a1310b14200040d0001c103409010700105d0040061409500300b0703600590a00206100700034411000c00c580b885624003812100c00041656034050a00a18044024000100000081040000e040411002924000082c5c100680c5644c0c0b8007161042125140f0f403001d4101082503002c100b0410f011071010b520f244202c3d03001c3c541341c039200130884244500340001003e00c142000280b000b4403004906a504521460012509180003040e00f13209170420381c81100c0c03c56021409201c4180c010b45206d1010b501520104128034150000130460a646c100161216145030341c2c0781500540b4500b00c0e9856400c40d510003201007104c0030b040107031030024054100300d80100d014514511030102d00712805001d85900001d442400c08074122140400144111654030555000203900270561010704104290201001d410f8450303801858200b40740b11891024603c00e11200c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 400850674 1250 400849424 400849429
    0x403051213170a06090b0906070e030a0b0402060d021b060601170f15030601080d081005090103030f1101061410020d02061b0c0106090507020706020705060301060f0203090405160e0a0302 82
    0x4600840d01182c4144201d000d4410619041c081c0f40d1001410850414810000348210202c50740c0c0903402442c200c5116903501c120840d0f40c4400c01d102c503981600030500c0f0710040340c40e94403841d400c0360004203a03502c1c000d101c9900c10100da00c40750200211110300a86c100c3c0c02541444030310352011007802d190701d14107000c82c141e2404210007042c508202c03d81e440482c54070b00382d095070610403110140494465507166041582da0b10440450384000895510000d541640101d01050072988054002002d41c0d0031341d502034500414104566081140320b1103d405501024028100207000c1004008209994a814014881891a511001d541c000041080c00c0c6500081d890361014400031590204590410b40b21160b1041d500c01005540c204040818003824a9101c0d0380141c083e6000c0310742c2c0560f1414140e840f40028841c0f150302031403d00040000500a0000ca400c40b0070520580c0d03e404440400030f011180140c403e08900840140403448458000313070030304040101100c130309104502d150300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 400851924 1250 400850674 400850707
    0x102070e0702060f0c03250c02100e15070203100c1b03031a1e1c0f0c17070312030c12140106121503062304060b040506060c030304020d02150a0504030512 68
    0x511f40b8903541e0320b4030420384184a240d5814250b07a004005a0740c1d8000c80d000200180141c48506114118201c0750710f807074051410458402d00da000e80504119030b03c14920700024840c3d09981814003441003c80071030703c240b646070f4008551003501c0010341032042101182034010f17540001c030302990700c80c018840000d0704481e070005201c500b19400c800440807104501011260054010705a083c250300c40341c10441c017000344506544400703582d12603000ca11281980c3d124a14400940351f110f9009c03000700100d1003900217900c001d595051121102d90f484220b0000c81e6480c00101d070b43e204081005100403940720303001310070809015400380488002d092192200c15014800102600d907201070640b2a40c0a01422070741591419502541e507141ca410f294014101d0610503031311492610b0001112443c1c94000e507001c0c21480030003142103aa03a0747c24044110f0321441e00760303031054510b0344111440d0f4181c001410031309a40e03a80c0c2c540711803452504503d403044480c1c0c0b0603400a001d11840c80c01558450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 400853174 1250 400851924 400851961
    0x5150c07050904082a010204031a0c0702010507080708040308040308070b070203040f14040e06010b030718060909150503030a020a031701150f2717060c03150102070e0702060f0c03 79
    0x40707030800c00c40c40f04032501045c50b04c050000229400840c0001c00c0c8200c02c819807140d03988020340340c040390b902c3c850409024411804000c0c0441d005020f00004a42501d000c1c09082d446011001c0c580340d10b1b610384c20000e400551049505c6000010b04400304140700c114103405c003c0e58002981454103000740d81a5000b100e000d08a24400d01340030700c42407655560407800311488141d06941203545c450091200ca54000c590040101d41014000341e00b103007002c048442102c8076680da40a0301814905040301401544041c1c920120741c041003c245642d040c00100410240c580040c18100f8813807030094012088900500303c1150b1003001048038a0840045080864083c80c22064041341003609072148601000300c86100b04021055058803801141840305541e000303020805c10754000b004842d40d6447c1111a00c88404c0144003199426650758520303000c0c000c0500550b40c00d161103010311281080100d51400c010782c044000d110496a06014450300101c2c0d02500f5131640c600046140307010702c0c0c0c40303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 400854424 1250 400853174 400853197
    0x90b13051504060f0e220f0c03050108060702120f0a0203070501050f0612070503060604111303050a0b010902190513080a08130f03030212090a0b030405060412031e1505150c0705090408 81
    0x10f504c1b00241d80c04e41e078400b402c2544c4a0108020741d00d42c2c000c0086c020442406440e0041c41088017003141c0380d0001400d101c0d10020403250b50300e841081c2c1e02c00d0702d43d41c210b0365103001503100038804040000d000f801001d1007040000b014101c103180c41410410428210640e41009421500040c8160b842c04500c096010301c043d2004100d010503204607d120781b250210005104080070404401c006c0c01060f0722100a001d44944074159899103003200c00ca101d03007803400c1c071824070502e41e4159550241e00a0000e808211400d407005035680c54101e0308095008a080715110b00c0050380b5500590700004072006841404082d8002c0c500b140c2d0040d555200c0c4641c1002145070200e400c0446070340380781034000904046102c65460742030600d03001d5a107003020f883c111002c000d0b0083c020545c0741b280c4540c41031030102e0a42901e40840c41c0325510000d0060300c0b949101d44d80c24170320100303898480c201411003403141b4444242d030b42c00e01c0c0b405e40c03400e004650300000c2c821001c0303a00303003c045254070303041e10303c0d40025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 400855674 1250 400854424 400854469
    0x270c0504060c080315060d050618060108180f0d030e011d19020a0b0d02190e130e100915050a14060f03010615020d090503030307090b13051504060f0e 66
    0x90700b0740d20b0039044417007104a41c03140e0005410404011190002c500078032040d2820041c1ca580e46c0d084880c269401c81d00a0b00040d00e0704001352004440c14821442c0e1101074090f601f1a15401c00024240301e00d244410021a0311948502c01001c02407040c40305000455810a00c002011440140c039900e017148400c4141e00301754007504c00d642e52940310340c000781002010b941d40d41d4882c003003000203500a100c0c0450501c080b2805007041a000300200002c55100034900e00441031030010600c01400d08148250740d0303109281d84070300150070a208200b8014064800641b03a40324900402c416180010040000360741800d1090300c001d1420905260091401ca4640c80c10a0700300300404d00501070380e4007000e00b41c1ca03043d83c610f86e06600480e40d03c888810307954510b02059150b0041c1541c921060343e89100090007101c0411054903039002400c0c0340d109044000d1503c076692800960050307203120300c14541c1080054100480d503000b5040318074509260a050301100307500340010f8582c00c00c4200070440c0c0e021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 400856924 1250 400855674 400855681
    0x30307180812041206020c010c0905010e10050d0906090c0305060412092702121f05180a2d1b030b01021e0309060d090c05030a0f020f0a270c0504060c0803 68
    0x406d405846a012292000704166118020300400141c030300c3c42642c0c0400d008111211050906030344101019170141c40c0c140c41c01400141d17080060101c1d50741555944d554030800400075400d44102402140201c00600040c2407900b0039003a010340803070485052003044503080000c014203000724104050580c2c42801c100c511300c01c1c2080a4070681d00321031604030700441041904000000020047c8550002907220240c580060204405e04901000c08240e0b108001a001c10500d0304101642c10710f80301180e8880398982d411900201c03024441d01407160303c603000746420001c400c00715009a000c0e4a02800341103880b5001075100c00026541048000740d1080e02000d031031b41001155100303400901500d40d5a904203a40c00000c1005540c21175400c0c82c0003800250620300041c0040c1002e41010440143c2c600d00c0c1c1c20040950000100d00741c0011b4560310000d4500c02038050070004003150f202c10220034060396180780443c0d4010729030345e00f070010610007480701c5603000c80c0300000c0581c4840100c1d6a81c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 400858174 1250 400856924 400856933
    0x11e02060f18160306150305070306151505070b130b040213020c030a030b090115080c0a02100f020706110c1203060406030f051f0b2b050303071808120412 68
    0x1c0110400c070092040183c900c0030901449950011203000c0d44c01040a440e40452504080703005102c040d01540c0100d0080c000310307520384c0c0207001c07100821b070400c0100c0c1e9440d80b6901c3d44402240b02903000c96030109201c01800344941106904c0f07201150144c0c5a039401d0f5850311180d620141c0064002c070704941000c510030030554120740d83c418801080b640c550140000080c0074003143c0000768000d42c01040002055140071804040d900410380310b22180c1c0c0e5a01c0b9854503650000c101d441d0440c4203130f40443c241c040a0384100a00d8018114001d81d8030301403428010250742044030304004001041010344040a07001c01c0103a25403036241c00c800e07030b2034039507400040c064910303500050320a009810003039017000300014401520410940d003012100d00c0c649000022280c0080101e50440c60142600d0700c00040c807010074120350b40f0410f0444d100200c54940720720310303001101c40d01d0120741011000000c200c05454400000c0c200d000083c0701c1420144020b402e00d020307520800d103150607130040780d10030030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 400859424 1250 400858174 400858201
    0x112120903060501120c0b040e0403180b04030309080c09061318151512020a030b091e0309040b030a0c05092805010509090d0e090601030603080f0306011e02060f 71
    0xc0d034000e01d0500007541c48080c0d092070070b20004011901400001b42c0016200300c68800d072011180c2c904e40d081d100e40c1d603640b01620714141182410324826802480402d40c0301c00761014102460080e5158070300c840c10001e01c18074140240c03181030300c80d0952104209650756920700003864001d03041008103481c0050081c3c0c1c1c069040340500185000c04402e06802a01520341c449507408d0103140f81c040050ba80c1d0a0a12070072040d010000e03400030307508101400400c1c66211f0b1150400403403401ca4110680d2a1150f8502c810b090b64401000c2d000000c03484050701c0e05001c1c2c80e00911049000d0000c00c500c1e41d6950349991740501c6813500030010b0f500000e01100241e8001076040d40710b02c02090121a250440400400d4240580e5101d01440e1001c54003e034400103031301034003040d5920740c601e044200c90308220076a40000c0069041645a400200010380402c000e0003010600401d960b46a060200c005440020f0340c0d0010180c0522202004500707590008901c0d4211101760f00e0000c80d52111346504021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 400860674 1250 400859424 400859429
    0x30e0d02030102030903030619061407080909040302010605040b0301021c0f022206020706080402010c0b0901061a09090606070507061b020405180606120c0f030703060507090306050f01121209 84
    0x75503c0441040710300c0d00d02100842c13044e00c04882070b140d030343d100c80d005000700383e80c600940d0001740c0c82504181000306406c1c01022458060f8550b1811724468200040203840304603800c8005035102d540800c0681442e004161601104a00940c02c284000d5880b81020010307071480821a81c4414510000c101c0d40d5044a15200150001c0100d030b0740d4520051450414900c45c16005205100c0e002900d82d215003a42c034052603050b1340c0e0860089003a00d50140c0303943d02070301305c10340765585100014039202e140d858044800c42075903655807140328a20401000c088014041130069008101c1c0301d000410126007141504d40605080c2c101c0d14126080070541142040c0c005e400902d000305103c4440400c00c40040c18030b403000b040b0340e51a960003050042c0c10f5115480c4516940c001c3c1010126854910220030032002c0240803550004c0d0b40e52181010b8030000d80c0d10501050014070140305100e00b034021075500982d816800c40c01c0d54908001030036a01109040500030942e02e680c02d40f9928403d0919000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 400861924 1250 400860674 400860679
    0x7020402071115070b060103050708130201171303170408070f1a0406050603010c1d10120c0e120c010905040f021c0b210607051b03030106030615020c030604030e0d02 73
    0x140e0354201c610042035a02c40300080c0c170658480400118250b101c4c4c000c407481144503594030002c540306c04200742040d000c403400490503c0303010210318200711201d0003894400d00712a64115000d403d02d0074080d103000951707400c45025440000c00c100c085007070401114a01d071b522807150340002e811418010200070030700d00010604941c0d60180801d10029402103802048118020080340d40d205409403083d5810070221070600d500c00c5026031440c5411f01080e89224160709042c500c098854125074220b0303119000c488041140c429098809082404440680425000045c800c2081c0e12001820003a624400d45120b1340d200d4041400e11103003a0107031050015041c02d403295a204040c2d8243c05130000c801c409010300c2d6115059440c04400c40c40340c1d10100d520001400c015190b0f26022509544070840208001040960038200c0b03800400055008003103983c0c00146450800c54032401c44500c010800381198480000189141c2e40071036244d820a03418207155200c6202c40307001c84c00c14541070300042e5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 400863174 1250 400861924 400861939
    0x603070f021e1608061b1b030d0608072132070e0705180d0501090c090b0316080d08100510030911030312040b040201020a020a0612050109020a05070204020711 70
    0x9801c900064183c114000c4054440152a00c0e0b4950583d15442140c140180c0c0340134581010071810308400400d148480c00814142c0c440180b000240303550720481ca141e113080e03550181003091040c1404400c020b40f01e03407001c0071000207400b4103120030f007109074030003030304220080300c0b030288844803203002500c90300e804051440f2444009019a407903030318a104050176040c1c801d00041c52144184122000f0304411510001504c20390024003441c802c3c40b40302210a59a2109503901203000158840c000f0910410041061a4604249424040300002c100d88125a08500340080c3d42c020542d418040d0312460039a446030790f60a010034004102d98019900314106c0d81124031a15070680210a246001e0f0350140300b6a43c0100a042e079a101d188411209040440081000101410794103508580148100ca019219580001d80582c900380e00c00408a203601c51600d4502d0524040d550050141c4041113003080b070742c003002404510980310001c2c4510f500281e2401005401081e45030b01040103001d84 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 400864424 1250 400863174 400863223
    0x20d06050a060f0311031b0306030709140907060c08161b0f06031b0206060108152e0c03440402130e031e07060c200c0603070f02 57
    0x2402c221280c40b03050300080d013004101c4110464017012a40110707107501c2404001da88668508505800251001c3d90500510000058698550040503005200d0041d120300794204607406a150805550250003401031400c80b81c070204004c8003d696004c00700d440c054988001518220481009401700300c0000c0014000108088848888520a8a45a8a00300a2050f41c0c80c50800c2c800541c0715100700507400440010401e5100b00380482e00105022101002001408001610b00d00d044000c0c0300e07558400b03c40e2680c01c000c40740c5010020034141c00d014421056940b0000c060b82c0604240003201141c0b0071419002040007455140c1050340c6100f02c0c03c040007041305808040400350b4042e407044141e03010000315100709209009424504a00651030801c0088071080c1214802e8102c1c4403001050251102040c0366000c1c21050100503a120800b140f9620b80982d40e0001400b80d4440c10781c0020709007030007600c900c07003240d410040c581000320200e041e80074100d2410804600080c2c0310307942511103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 400865674 1250 400864424 400864427
    0x10c02030a03090812070f060c090b0706050402040b011d01030b060d090b04030215010e0601141c0b0a090b0a14061605070e01090e101e060617010509070f03020d06050a06 75
    0x107800d48070013030140c80507010301c00c081c000b1a000ea00ba0240142c06c03d0004a0300092081e8000f40900c070b4242060300b03c031583d59054800315004441d050b10582d0300d450070071045240900c41c440409009003805001081c841e90840b01c0d14821403005818565203840307261413135560302c00366052250609000d110140c406d103042c03400c114081d42e0480c054824622041d6882c050004480c3c10b030703501d6854004544d0340d4040111603072020b0426211150340704002c41c0c05c602e00c1d460313100d441440c01c0c04000f149410000341480480c00c0241d0100414901c1d2240940c1c0a55900744144200e6843e190558550104c14001034424411318110402601155010604000c00480c208e021a0000c41d00f10019130781c0c802c0d52406883c50b5040460042d00720034a40000100b241c3e200000711100848070b01103444031104601b0448005d50081d03030204035910844c9400c0621080ca00703014010540d565181800c3c80e2a01420441240100f0400c0c1900860032104d91400750303100070001c280040941880540d503140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 400866924 1250 400865674 400865687
    0x260d0c022e0b0105070302060f040c090e0f0c04150b0304020a0504060f080c03210a090e0711010b12070b0c1504030f1b080d0c03021b032709040b06010c02030a03 71
    0x290685414030b14005241d600030760a45640c1501078000c1c3c1085d076140c5088010620000740100c0c4d00c0c43c1c0740140841c0044091007240881500700700100a0740140c19801c900d000d0800325828422410103440840b0b002003000c3ca00c08031516186425200d45540c0f002038195460f54010a4000346060800281c3c030103040c000d90b040f124444140e800000d407810501d40c81c0c004043c1c000c5038031b400c103442c9485d41c25610790051038060940e24001c00c01d00d407a4020950602c0782034130350600045400d04044070b40d581c00e01c60f51100340c1e411100710000d10b44c446252501c40140d80700b41000c441d4041044941800240115a0030002e1100e924480d40303418500501030828660301c2c0e400140c56115441005c0203054905203020760400c0d48942419031a8808601600c80740b82d0500426400703000c5009000c1c01011a1804070701107a01540e291060ba00304c1c48155101030005400c03141c0d00749441a41521401561500950041100c03c080d6950000607254504460002501803182d00440c406040d4003030f5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 400868174 1250 400866924 400867003
    0x30a050304020a06140702010c030c0c030302060106020d030204150509011b0303022110050906010315080606120d0e0d060905060f0f100503030d0c030b1804260d0c02 73
    0x3110245819244c0c98102d03000c4100444402c0199800c0281c074000d513001e9001101c40f18403d140094454103981e170354065840e51a40110b025900c004014801c154043c07003238406c9900189400c40c2040d01e0304218000e03071180390358801c00b84900003c40c48500e0b4403072500541480c2c1070402e1070245000c3c40c40c0050017907001c1103000c080f609071114800700c0f14001d8848207000d914504503164009042008108038080c020f417601c0c0c180b5948220380c0503003000329050a00103210000180840e8a01b0000f800000611240e9100c1d280d000a10507a0500781c00c4040036120100641d400500c003181ca150100040100941c094000d1040034204940d03a18005040380c410000ca0007a0303d0591642e43c04459242d04902440e94180c1040c85810811b4400d40c1c46401503041301c5c40d001c507070749940c800440c4070920800030303070324011105e041040140550300c0e00ca00050780034241e001051f1692080340340c0c0d690080800452007240c548287d00b620038030800802010021054103104614220100d2521049881 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 400869424 1250 400868174 400868179
    0xc1205030d1d0a080d060b040e070806040209033301030209010308070c240909020a0509040207080427050f06090708090c061809061903080f0408060403030c110705100e0111030a05030402 82
    0x21b2004038a1450202c01d0310f00b124202d0740c1c003501d6500c54260a99100744001d008a40141e824000982e02d42d50421000c4030040c030740c207100076040d99900030700701003800014070b5080c0c07a0408c0401040140c40700c02809044030b821400c020b49a01c940e02e00000d94519035404417407440007007240848104ca020000a02c222141d849805000b560355152000380d01401508001044050111915904140c0c000303092251007240700c54a06a00e0b100c92001c3e0280e00005030f0200e07030f541c1c030000b542c50703225109490300f2140100341400146072610000b0701300c0e80024001000c0103040b00125100314801c0003001e40c0b10380014015904d80348240000b845102006910300d100e5416180400c1c114144260140c41022000c008580301c0c50458030f42071160303404040020072841c81040001400301051200c180a0351296601050000020800030b0481880401c00140740d00f01c00c208104617035030103098100840d031700c2c180b0400388070112006032001c402d0007181c43c01c1404009190b00074194003600641c4298800c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 400870674 1250 400869424 400869431
    0xc0714010614010e12060c0a0905060c0d1701030c03060b040b03150603011d0a120c0602040909060509010b010c14010b03060a0608210906090406050d0605040c1205030d1d0a080d 78
    0x100002c1040e11065001005c113160800d2000ca140c244e03202004050500c85420064030141d40c88021641c541c0c030401003c03001c0d4208211405d0515400204180d040d20300101c500c200b54110b495060f2400042d103c01405543d079070301c1c0b800068a0715000824140001019a10200c0c00d03000480c038100400c0741c020b8400c1d440c0c499101d5150720109512168001c0351001043c050000b56601014010b55940b6082803004448030800000c0e400c1c0020409004900004940500c1074a030090603248003074012a440e9040140d45699a6031120034801300036000200c5103403910350148158010100d40103816054010082001011401c0ba003090044600344002c2301c0344a01140454040d41040024600915104003c001c46610340300b0042d04608074024400a5400e9039140014460040380c1001c90b0004d803508108400c0c0310441c0d580d18014000441c00382405115a91042d4680c895000091026541c031583c045298020018800441030a10204c468140356401c00b180990000d0701401a01c1d420f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 400871924 1250 400870674 400870697
    0x604110a08070f02160506030601050708030a020903121c05220303051801090308161202072303090a03170f031009061a04091a03120a0221030c071401061401 69
    0x1000410040010031100340074105c0e8186070070440c4651020340110b040013400c3c0705401c0481e403054015402148954001a913440c456803d1504000565a01082180c41071105410031100070055400b210703160304c0002655510b41541c600400c4500c4003050ba0508030701141e400b0940c05901150107480300480c912424078203040380b0ba00780d03600b1500040000780b41c0e1010441c1c411002450303001406040c00e0402c0403002600c03c2400b00e03004a8402e40d01004d4510204d5001d4415101d0b8400610118000d94940180f10002c41e07607480542c840181061500c00da86029150100181e80800b85548bc0c080d5403400d00500048000e2410302a00c0c50a500c3d141000404011008843c201e00c40020303081d90610380b403c880390340284036041c0100d265160b12510441070341e80c240f00c03d205040c2007808064840c10340101c02860700d108601a042d105149550301d00520303080906803640039130505d85144d500d1510f890034032041600c0100046496080800200d007800e551030203240804401c0e85c50303003220f11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 400873174 1250 400871924 400871927
    0x321070b10060e0607050f1506010f09060e130908030c1e070b06090a0b1504090c030207050307020d05150405010b1305150405150a0e0604150311090604110a08070f 72
    0x10740e2841204040740111070b0902080c20440c0c05808098080c0c000d0740d41031000121510f0404042d00081041111088104038807580c1002c0c00c200e50b00d0040c60030044146c00c01e08042d0158100c510201e111b01c040120012004105412060b5000d60144466859003006499103005420034030320301002e5107681440000c208038030401e44270760f01e4212135044c1071070302c8000074040741d403c015003100103040d00d8842c20581921142c8210b480104407903040c07651203180030040d008032400c0c000703070344101801009510081000002030b80d40850f0102c550740481c05051a12519150010954018420380030040009002c019407084003846029101c201e81c90051055a03400caa40c220340000480c10103001d0002d4906060f803025500c01043e4180c0565840d0001c0060700c13000180c0d00203803241c1607150800011b41000d01511060070031081c4e00c1025141141d0f0383c2e20740110101e10310b500441641d400248030703a59a0300b0541d0149070017411301d580ea44600c58002d044000407583d00003c10110a40700f980c0d00d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 400874424 1250 400873174 400873201
    0x6020c07080f1c050711040911281a040f0b0703090509191d030d020403050106050102030c28060c030e060711030a030b041512030206090d09050f0321070b 68
    0x384950b00f94000382d00780901c252501e8005480541da502040079201d400c5413154450558901e0141800c090984084000c003c01007440c0b04050400d541447c4400421440841100f400c2e2050401010103064540c0f00100a9000315400079882c10341c1002d001420520300c2c0e00500c1424080c0e5220001551283c0501402c0e41d000d503401c504030044010310700b1600340f450780284880312855904038040000c05948030719607005040000c1045078000f90410801c1000d1090b500244002c0c0090340c28841c05041682e1920590300050020000800f0024001010071805d20012980284200400c081c603c000034003c3c0f1503004030340b13a244140d80104001c0303030062008030040241d80c1e000b145400c8141d00300724068480c7c03056a641080e1990a14180d185032412140c016000800c400b04519503141002894a040503184690b503400c49407074a00b4140d80080b1007010307034805680d4200d1102888003c00d1910001001c14030f420800003d404803040451401800300601a0030a400b00b51240507540490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 400875674 1250 400874424 400874443
    0x20c06040303050d0f0501091a030a0b07080405010b1504091a060a03020f0906120601170c03010e22030e01092c0403090e04030917010b0f06031306020c07080f 70
    0x44410312003040040d1040004207040603110101044540d900850340c010758000b82c000c079510325200d058910401c00c90b0f180810b012013003180180030030b80898440f40c0b0095006008901003110100010381400f00942000c0320070880a40312100f000b01e004c2580e28103400a00840d034200e401e20005401441130008032004009005004d0351500341c0c078481c194001c1d40201042c00144405220021259403681c0c007416200c0100401202c40d85041d100040c1080511a00c40150310500005d128041400318192410350713045440184081d120300980100a00c002216940e4218400000b0b80405a1100f125100030302e00380c8401440903100e2018142503805282d4201c04002001e04015041603501e184582160080c05d01d0301545403035450400da001000c503015808200320001c108400c0d011002c0c605000030440008021855030103000800900550400c60301c0340d034000c40402c2c6004110314103540c0b226802003086650b50054680b01d0386941c80351013002c2c0310f8040d44c5400d009501010030380599 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 400876924 1250 400875674 400875679
    0x907170c1206060901051e0303041203090602030a0c0209041e03030f0c02070302010c1203090c03030302130b030c03060409050c040f1a0301060e0f040305070611070b0c0406020c0d1514040c06020c 86
    0xc01c5c0e081c01c05000c81d08401007501c0401980c44814a90651020300040c8050280c00320042c0560035035080203001c1221603404103003154030404c481280c04d580721003440b00456041b200c80c18242c480d4280200702141844000401c01c4010300001c040580542c04400e90461640f000e2103441c0d41140266207503521844042d0108640034100c80c0000c031080300d2070351850100d0600280881103a11000c1681c1c0c42a00b0440200ba8001160101400a42c0a0030018000350150fa407452038944c114072581d0001904445c0070780d0b1160041002c1020500614030718034030182c801c0116444d245645000b42440241010b900d22070050003001710b050601903c01a83d010310b900e080c4640340c440c031452144a0050041d002c2020510000b00060b040303010b095030034940403005507124011810040c1e40c002d400b52511000600400c403c000c410707000311382c4030304482040b51002d03000e15250411030700b0b1201d0a110400b00791301d021340506e516803090840c00d0095014160411400e901c4840990362441c0c500034055 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 400878174 1250 400876924 400876939
    0x120302091809070b0a0c0302011b0c11040f0203130c05060906090d0c0504050a050a050901141302010309061d06070306051503090f1209120705180907170c120606 71
    0x15020310a041100d0b002641603080360380d0960b94484402882d009001d020001a20100c00312062607424003400003204d00085000140200c1050040c0c0b0701022004018002000f07a80449415510b6034007540c6080c0440c2c07000d556901e409054502850001d101c05c80e04154119000724043c107103a03050f40e00f404030180500707190a017440e0812448000880d021120101042c401294039100c1d40202405031208120202d80c504108411105640c801400041281e15081b042d0140403204419950410f00c00c1310300340800c01c0c080c00104c0181c031301d040b0b001e002507041c50068001007440110544882d03443c601500c0a030381b6040303011403e4402c14422039921003d00300000e40406038450085030880c050004481c41d0180d0148200e041001240d106801e140d00404e8007105401c240c01c0000140a6170405410304508180020314024036204040030182c0c4c0b03040c00203c01315810050440602040c50005441c6890f000c105952119440c42003800340900c110756104900300002c00c0e60142a0082041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 400879424 1250 400878174 400878199
    0x30c021207060e031e0703030605030f0a080f480705061c090308010807050105070b151804151b0206150f0414161b06021806040b030412030209 63
    0x2d01a0090361081c5407030f4001000080c20a429a8420300300740c1450704022602c69080b41000340481b101a848107010741c0180604911190000c50040c2c11554401074443d221590303001d0504441c010064040f2461201d41540081b000741a10b5017120011854881c0c2808290080c00c1c600c03490350714942ca04240d001810038407040ca0100c014041449010516000e07080c040d454000c1680d00c0d00000b51b022645010041c410340c00c0920240e00601000c0c01c0c540e181c2085640d802c081500010580700c0c448403070425484c070603034030322955005129403000100700c2400c15040903140c0418544400d02c5480c0740c01c0e815062402c44403e07504141c00e541c0c0241541e995a2034200c20070322800958580d10248400d0390128581e201c4c030031195445450a0241c0b00c034a8915183d0092503482e118000a01c9802c16070f40100e0031011000c2d522040e440600075840705d98241400300211090fa41c0c103640220049008500c451440001e140b085000b8010b010482410100660403132058400c0c0329000700d041085c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 400880674 1250 400879424 400879433
    0x40305060c04080a030c081303060902090f0709051c0b010e090f0c10031d0105070203090102062a0703120516030b040603030e0d0219090e060f0c04050111190302010c030c021207 78
    0x3c61b0341c80d601450540b841d0001c11642c500b0548020f810172200d89a54110380002d509021a40703a61281c03400d8018211402d0038071024040d028180300341803141c4442045003411040b000810040103034401c0d40a0055615100f0081c601c2100700e69455482c0b0844042c5401c1c0075002600d00c03501c110103001404200d005d0300b01140549422543c00b005540e00c1c6070203040e800310074800c440c4a0140781d03010b5529100c40c1000281011030241070690340800465007240640c030300d01d4688014821010203941d40b49440c2c13030162500c03440091598212480c00081001807054040c900300e110155036005c221260070070003044102c1d2124007000d000111007a200c2290b50403c01c62162149000030212030400550808040407200d07190440b220141c1c5030303583e07070105280401c805a088500ca80740f21586241c0368010300340d20700980c8074490400429200c0e0034a294400c0c4070341010b418650310700007891140d90070080e000e410013841010000780f03030952941005101068190031469040c084901c1c281a5454 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 400881924 1250 400880674 400880687
    0x2031612080a03020c070e061806101b081809090a030f0503060105040305030409020909091219050405041b120209060d0903030b06070c030516050907180b0c03040305060c04080a03 79
    0x64202c00e143c0d082004072009081000207000615846110124238079142c814040c1500000d0f001e42043c20301d000a00c0344541e83c10605082c5406a45044d405c40c00c0710b031203060700e8500b12280180065400044401c00500b00c0c406400c000c035816290901da903215030b5289a603401074101c024001841704103005101c1841a001107400400c14940313a42001d85039214a4195885076003c03200385980010b0801e500d0034041c9040f070340041c1d000090302d100e0700c1c0c840042c004d40c4948812203440c1c0c08030b40c0c0d030300000360b0080080d54003600024004110f007903412181310619182c3c520208020452046070035403101154021030f0183e200190001d418032401c40c6d40880500300b80c40044081c540c481120900b03544548019250250150b000c1c0304c201881c5050480c20030200c3d122041580b40e40b40f40c103000d152100e80800360403290b140303009000c03400c541805d0106c1c050300781c10800e181203000444ca03008031000070251050740e000b5130507101c450b03c070b00001d0141c40c4204d215071060b42e0030250380707140840d02410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 400883174 1250 400881924 400881937
    0x90c17071709160e090c060a2703120806030c12070b2107180602061506071506090b031615050c031207050a0f0201090803160e03060901090203161208 66
    0x1c42c0c5060358002c2140941e02090b030044c0c031005468204020041400b0050750108080a8540c14903001c41e140d0014550718400c1000e40d01c1c4102480000c64020184100c10020358001c807d0000800740060002c000c2c060035604648644940e400a5030b462030842000007180030702c3c0c0010581113203050402082a0040e000e900c6a00f100950700d89002d080703104a0710310034800e030390300c0e904811550200030311901c0c0c030b40e0421021503010808202c40041071260740c0001160490300c0c6901d0740442d1501c5103000c65580401c40c400d50a00c54001003580e080e40107211450000c606036503800c10711283d10340f40340748607100d1a900200300c2c484080caa07600900081140c9114a0700f40c030b142403046142401070800603170303800c80001c20010788440d0943d8040c43e628003101081c070090045442e1922031b10b1250102400c0703482d48824800c4c110035103d0007858815101a00602600c086251a40301c0318000e10256a0903400380c0a44840701c0280260f440004064840354070001c4007506240d11a5035080c0c1220 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 400884424 1250 400883174 400883191
    0xe061011030a020715030510060806040e0f060133030231061106131401140c210403171819050f0106180506030c0a090c170717 56
    0x4205030088050900041489840c1c80e0000d105640c42d00c92600d030f101ca03072511030710f0401d4a031006004c180c145601800c0c00b22105071920760741c20380752035001070010060034400848611922000444186000c1041d40c100d540c000c1001c00c41210300c00e400607a140e0801c002c207244036103146000104900a0740a010000c81d400420066110108100301c14041503c607034521507151100c0c2041083cac0d00c01500c10900c0c03000c40160080c4c1c100511120494a15601c00a02c405400c101c80c803c0c00009600030a608110180e020f44941064440520503505ca030006800c138000c804161498030000807240342c052945952075110024280c6681205894050600310b040800c0d2000c5402140041100c00100d2050705c008446440752481c100c0e191880060700c4034010390500002b0410803449102100280540000203d902d558820010381040302e40701c400c1c1d5200a10070008904004258010407200d0740c1500c1d103010380303610214a1910703490120b40c01000141c1d281402c08003005182c000076008100c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 400885674 1250 400884424 400884437
    0x30f0303060305030301030b1b07030c02092d0604060801061d0a1b05030a1406100305040501060536010320030a06020307020d090e06010503011a07050d17100e0610 72
    0x40f955003e0441c2e2003a0710a43e200090182071001010346600540b10404044040c11304d4041c003a45d01400d5001e031242d019103d8420320002410100031b400f12245039488000c070710000b0704076080200680084c1611028081e5203403120200d0442414418007056452001160f6070500300040c40520403007008004841c0140c844c22146450240c0d4800510b90b50469216a0348034903010760007500310f9117a580034240940c800300a02141e61074505040d01c0c148010300d40450540d64034140740d4054030040e44030780d030084203850a80f2403101d281050349100140b8114031000151441050401e0380c2c03000e02003c0d100200c11441c0d0b544458045070070204105020303060714401e481a44404049804c00c450003000340e040340302c10917000e940c404010006030100c81c1419405040001c0000c1080c0814010720441440c2074220340c801e80504400e40b00d0031039005040720a07100a06000400c50703c0c041c0c41451480c5030800111b0785007a59038819900b0342346c1000130114595542c404006641c1c3e1240089070a201a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 400886924 1250 400885674 400885679
    0x50703080706060608060405040b06040c02150c0702010f05030c0f0d0b040606050c010b010915030e0f030706150603091a0c0d0504060614090c0d0b21070602060a0e0304030f030306 79
    0x65030805010380a008810000e525880c00307a003d00000e8005191038402d510301810000001c030040101600030905460004075124508000d9191800044419907055644010011a10092801814610310030f90301c06954000559094032140801e488182c1c0c00d420074048a42000c3e03104000c2e011040b103070701e0f0101c1d1144013a40854121800c07604590300007800040e04100ca5039007401115000d45080c41c20b0003003540b80401c20801c110799408030070105900e0342542c0003030340b0003000f03400c82000c0c018040d03d43c1c50300e5900d0080e004041070803920707603903081866002500601a2164a168030f4105510f024403c0089080c03a0341402b0081591034000414042c5d519462030900ca0644900c1c41001c0c00211a4240302ea00b4101d4403150840511891101e010060785d8003400742614401b40c82d0001c0840e1544915000a100c80d0010392820000c019140484815800000c2d08200b2a442c540035900b03da201ca840d41d50680b0417138002c4222541c000c100c104002848000c80b240254040c1c80c0c00070b02c084c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 400888174 1250 400886924 400886933
    0xb180103030e0d140109261605030702100c0615081510080d030e0118020d060209060910030506040c0f0c030815120d1412010b070f02040507020a052a0607050703 71
    0x52a07081300c0c0c2c00c9a99100c110f0340c1004502c01618100e903030510629201c004440701454001d104a02c403c010025000840d8400c00034108152000558001c011031074229200340c1c010f01d00c0f440307200240c0e21207051501c00700170807180e03100040075070f402d44000d0030070340d9030018201000300c60180002e00c01c040c13050000940740e8800e100e860581c001d16507008c11603070f1180d0380c201d00792940000075101960201c6984001070f40c442c0e107007560841e80070700050385500e450720000714103005000381c103600144200741e06062150705612003403007010200d808008100a18101300e8001401c40502000315490140c0080407038005d079102c80d0300c40920061071413510040e03c0414200c20700108074048981c030080c2000794207904851024041f241c1c0e900034900303285032421380f0030180d03606208843d821840001c9250034401c090301c100680c103070090010310241c10900701c003c0d0359032102c2500799058040d4940c480513490f091420144040000c401c1d05d0300c580720440030480b0590100d00100d80e81c1c8684000000041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 400889424 1250 400888174 400888193
    0x5060a0f09081608010e030c0303061306090513060f05042409050d0c030912031b0f021207060e0105031e0603030c060c030610020114072f060a0b180103030e0d 70
    0x30101c05980100e5840d000c1404c5c2926116241d0f08a540c000b486404c40c0c49400005070782e03201908480100081c003008041d10014000c9420000805040c40200286092100c8041307404d64400d020412000e5650902c07801151800e0380e0040000f40125001c003010049030700c0d1303850701e0103102d01c0004403000301d9034410f49400c141d2204103020a00c00c41e1104103050b04a40c90100600425051241044a55400034070740708601c649600040c000c40719820034800a840b114a50550107400b007000400203655159803a020740c45030030002164114080c942e944034005603401a11040200217007011001412040c1041c020851509440144028100c41400304060307401a50281140d0356241800c00a022024102d00003407805e582c148481c43c02c0e03507080c2a41130f5034400f03078902d84140b000d05030048550140f0b41040e81000104040e1001c07046040300031a0103802003144c0041041201c0d0054184060302102a44440580c00484010400311b40074801250814500030403042c540c0b0300695644120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 400890674 1250 400889424 400889443
    0x303011401020601050a031a100504020a2304030b0a05040f0b040c140a0305060a0e030d02070627051b011b060b010f02011506030b0f0901060203070b010b0405060a0f0908 75
    0x20300404240c0c40e440ea50301804141d000d07202c10394400c4420b6065440c0c0ca004812400c0c0840c907881c51039800501d00e00c2c0920700b51000780c440184151340d10031910100415028403103e03202d590f464166046841a0340b843c0c00c4604a95001300c00184e55a1450061780007000010400e032a82c50070f100340140020074109a051080c2d100c0d0040c00d600303a0034000807d010703c00c0c1d4881f1034001c83c00c010382070004c80c00011ba8103600c81170001c008100065058040c0c0d06602848840740c2e9800d00101d000020420180c11141c0610704000040480d61800fa84015030091720900141c0203030408481c2d01d248401c115a01e0b0816001030420381100729010386000d01e0504840000d440442c0d449850341c00741e42e402803020403a0601e5200038451458041e2440171545114030070142415550400340343c46450707081c01404d6001c8000c2c42c00b015584c1d40d242c0030b034880d40000002c44003a208940046824800301040d94140c80c00a41400d040001050003a1503120380b11030300805011100d100002e4615041260b90030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 400891924 1250 400890674 400890689
    0x14010608010f0e070c0f020a0b0c150901060524091906020f1612031826160608130f1101110106080c19180605010e010c1101030e0f030301 61
    0x5807580740c15080030885056400280d01004000c0900200ca503101e484031218039000b030b041c0800403070300d0320002d40300032810b0340b15640c410b5010403c024000d60218581000245110352140035a51f6040500c0c03c84441c3e020700c6130301c0a402901180e40110031070304085000c0d01105124982800480000c0e5070658912011806140c071400500005506104444502130310360003c144148462405140c501081c0c01a190300e10390525800003414810303602c4140e00252560342c0914039844000ba08021612200d60300c00d1410950245080f110000840c0030384c21340c03402c0031040945c0c1013800450f040c3e10701400e00a800c0500358080c00102d20b00b4050710b4030403407007160004d500720512000504040040380100709184d162107000c02c0801030105902c410070700c0403501c0d0402c403180f61089146020300340c0c2103080380010241074500b0842403513201030142c2e5030903240c2221540b0500011103003c404024018400f03001a000347d0b076254000e40016001c10403c40a484100422480700c0b407139038000764803104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 400893174 1250 400891924 400891937
    0x10605070804230406090b1e01090e09060115080c0a050d0912030c0801050d1a0703330b042619080702040e0a0803040803070e09130b0f2701140106 65
    0x3c0b5103130512540c0b0041030b5040f02403000e01c0f004400910111094001c01542002c46501c142050784511606000303040090010b00b90360800941280e6100424001e0010f0380803201c031040c40080c02282540d200b400c0410103075107001413120003140d61350041900d03c01750b00e844040100c00160390151010600c03899940002d10202c126800410800301a4807042c041d8180703480420102c0c480d140d00344910010140c2030059521007440407001003a85411904011a0492181d82c00d414003e000c5200941001008a1265140d441c072039250705c514482c0d0700715245034070009040c172011040118070304800c4800361900411007500341111f040b0080070850314480000344281c114a01071198000071075a48000300100e422170f584401c010712010304040c0201030302100003102d162141c41240b01d5450080e0a103001803c0c1100e068140365808102150000500310004542e039424680040c4a07011a5002002540b5070604010039a9200010411255252079151507402818a60700c0d00800107640c2d8403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 400894424 1250 400893174 400893239
    0x2a11060f12071d0105070f0602040308040602010608030306060304030c03020c0a060e01181217040906030305040302041404020a06050702131b1404030302030d05090f0a08190c020603010605070804 86
    0x403403410000501010030b111426141d40b02c0340034042c8244143d004203090184da44c00c298105407501e400049001456030303000090101c10071504201a100321050740c0c009001e0300340c807a003145441c0d0100b00c51481d00803a0a00015011074894054555203e0103030060341c0010b071054022aaa00e05217411035008101c0d00013004030b0b42d5074007844d4144008490741e0f04c6088035060003048280d030441410082c0c0b06610f10502e181c0305201a101310f50050082c18400c00080c0e54074035014006404c144410b03441030303203042c00b581c2d0070f561b81e00388542c440d0b940142000c61150512009465540085006903000541060410401c0c141c510032494030702c0c03041076103000392030120800400d0400d075030440c0a47c0741800e000410019400005551310240107490210715965015010303483d2541c980390428052194802010500298000402d40309a1103008200225500d40e0107903048008140000d401100800042080d20b110b10040c1010070701c615009440c25680d20b103403003800e04048018165a40145070b89 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 400895674 1250 400894424 400894447
    0xc0c01150f08060c04060f12060f0e0c09030705120c190812070b0601050f1603121d060103060509071502070e0106110a120504091104050f012a11060f 66
    0x1e8030080226030000c0915140600e50300c2650300462142d40140801d4222608005024810010110551900820600e0755900c220403c5d03c02600c101c2c48a0440c00d00030400000f922021100001c0014005000d128600014002e100c1241c0407542d0050091034104103c5503149400c3e44101080c1c3d0455020443c00c0c5030203107013042e0300303036422165484041011100084a1004041d481380c0c1c242802903d46009508101e07141c4200c8002c5400b15654084040815410203218140380340342c00d40c200403880640c60341d501c02c030310f080020a40c60f6010000410018104d0340265074801741e003006654070f096850302c0a040ea02540040c0b0340250300800010f100003a00300c59100d0041c442c51401a072070b02c0006a006840c1c043c4064060000c091161201341c1c101d000b04219001860401410800254944012103840e0014010540304d0000740d4083c02903584070344102d40c0260b85120010390001d40808080d110290201c02c1120401c0600261340610342e10800a0120fa12000c034507242e842203c1203c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 400896924 1250 400895674 400895699
    0x109090f06031109160c080409050c0c010f0b13110903061006030f060302150c0a0b0a020c01061403071e0305030406050307230306010309081201060e10030218090c0c0115 75
    0x20705000e241000c04000baa9041c3c05c01d521500082401c00000780c07049401e00610510580e0451000c030b03410201030005444105008103195118980204030060244040c1e034240c5a900c428558411a02d070350205600480760710110000045108080c41d207160034010a08050b0708681000328908140b0341046502d8040c06880c0c0c0b00c51491101304500d0f42103600045031351110008002c2402e00c08513000c6454403007007100d00c1c0c0301500049041224600a40a2070207540140203209143d400c0a50004e000c004c0d40c900c018403050f0007405001c01905013000e21a003400c0106801c460345140e58070000200e10f0501c0100080d21050769616a2803603d49005400e50300860030105c83c460b50700d1301200b9034103513000035260044024a0081100201401d000e459400b84003004000300c50010000565190004921411a01c050f500410890002441070f0201c2c01640001e440a500d202501c2e00e2615020061551088030343c460030b428030800c00b003414210fa07400300c003080852614003002e201964504c0b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 400898174 1250 400896924 400896953
    0xf150702011b082a0f07051801080c150d0507030207111e01050d15080606010f17011505071e020f06041412150403030f0b040207110108060109090f0603 67
    0x2c4031103400d00c103903921001d4910540e000c04158031940a25507080600e0f0384403000b15800d11400301e502440c14180c5040e180d071994410783c0e21a069170748600e010242c030310450724122103035100500391100044c0c090004022030b1684044064000304188502641c9a102da14043d5003165001030b02c8a019107071446108440404082c440e01c000850710009040006113000c0c2c0c184e0030310f401c40d1501d904400100c050303e61a043e80a21380e41c20b16001c40c1011000817494400d000998034000400c03c000c1e0184e411240c08685245502e030307000014405e541807a050350180c140d543c58081d103014040e4807140449902a0b0126034040f001140010562a20f40c2800400484c102c444c0c80c5401c4c07405041011005061038803500400180d00d42a0b40e040c824020002c5800310500643c0c024906490000c0041c000c0300c054444651409501070246e04140c07003070341e4845174411039140c10740310300b0401540e540000038003d03810455035080c0480ea00c91540560b01054580500200303100307055181c0721805c182e404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 400899280 1106 400898174 400898207
    0x70321180b060604030507031103120a031b02031c0513021203070c0e040f0201120f1802010806180f2d0105040c080609010605090f15070201 62
    0x90303444a024464941c003007140d514441004054041da01018019a104220030310002d20b450103d4440d412006080350603210201044c008540e000d400303070341c0000e5110070110807010444520700031014824006581042c217401940141c41480058041856898202040a5200554480781c0c641e8014168000040d680c03003545940c1d030311849080ba808500c3c5440050b03001040e821072030081e0350121828050758025001110030300440e100c6102c0c8941c2c0d0304541c00c046103203072040c2810841416103c40c191001400058008400101041d010b401142d42d11261400804c0b00741e58030844120f403401c1c1035105d00c1c40c504080d085100c0302e441d880f00c56203640100384411103187c60407648202c2d020f000325010f100007102d41c1c40090303520540281041d00140b00c0c0c1030162002d000c0000000d40a0303141c5850003c0051a00d821000c034010fa0030364005a1a01035503404058005440c000 = true := by decide +kernel

theorem cover : BRFrame.Cov 400719424 400899280 := by
  have h0 := BRFrame.cov_init 400719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 400719424 ≤ n) (h2 : n < 400899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
