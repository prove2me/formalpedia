-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1626
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:55:59.318425+00:00
-- url     : https://prove2.me/submissions/2d2bc666-7020-477c-a94b-91290708789b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 292266187 ≤ n < 292446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 292267437 1250 292266187 292266197
    0x1305090114060114042c07030b031e06062e020304060807080f070e04020f18031002030c0708030c04091a28060507060212010308040305010632033316 66
    0x49407020092020b03101e86e40c0c40c030b109444007810b05d51060310f424240f44509150745001c140e40200000340b5290050704812010003074166030b1700c83c8075180003140356504401c046900410b844d41d100c00c3d9419a180c64014070401d03100c0174041c0e504194010000e8400c5407030b10386a134029590b13a413006894000040b070b50030480c0746415000680c1da0f0302514010214000280c801810400305c0401a4001d90140b1110307085005802d99080c9940740810194243c40d80214040d411814000d880174824010311030300801c40040030000641165001080d10020010100148000e80c000050580c0d8a842c46c6c420a01541d9401c80034000c001d494148000855840024910313001e14026085843e41c00c502d00460348250200042c5060359601c542c01400385005124507a955031840c03070020300b11f171000c0c0d000740c072040ea500b001280f0710040c03584443e0070100550751905103800c4150003c0d081210044c10304004503180b241c0c0750040e5502e0021078036a00e4480c2c90000b81d549400c54001d40107110300d03000d900003070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 292268687 1250 292267437 292267439
    0x105010c080a0f0c15060806100b03220501050123090402090a0c0504050909060711010501080616050909040b060a17032d0d0903080c070c0311130509011406011404 72
    0x602c1050644400e4041e0b1034001040644c075501c80030b07400011282c000d4529101d500c240160340c003d1040c6070b0001e0000b000380c410540782144100403800010150001000740b0640da040c1007519102e501586c03603110000300300e190384a450b9032020005211700d40c810f080403214004000d040c818801c6024680041c9040710329030314540c240c4090650b800e050010084103000026044d242c4120325402110640c01a000515004030300030001a00d9020f0588541e04040040100f000041070064024052514214480071880c1303040c0c1d200c3c032030407447e143c00c0108030040005000043d94840d00600d012103500742015503549016203000703001c428198883e0010024010301110510303070303128014000710024802d014195040525500009480c0140b540c44007911000c259000007503962100020318098105202525246c400d014680801010015406000581d5958070f0140010900020714188440d00e05201c1050292034442c1004081c14020408500c02d90f0080b9450380c0301091510666040c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 292269937 1250 292268687 292268707
    0x15020307020312180303040b12100f0501080601111b10050a14090307050307080a0308070f080708090309100507050d0c0206030406020310180c181214010b060c10050105010c08 77
    0xb1340c06051000481000b0741400c50a0b92000e1001d840104040448681c8508944020342e0041c10b000700603405804015030280b102d8100c079022a02031301c00178a070294059640d82c00503a003880210702c41150501c9a0303c0e01e0b01420a4403541080c081e0801e455041444914039810b5420740185102d8101203541c0d210303100e0342c8200c484080c2a400b54005c2c1284c140c15a1031011078207110031780e02b100c0c1d0581c1000012006060b000441e9035040301c0f85140200b044842100000c102c1d00000e0211410400c45401081c4e140c02d00f0010b85404010007843c182c100c0c44035001c041c10540c001d403403c0f03e50340140c5d2078140300140500c841e81e00c030710b030090901c61440d03450340e4415000394001000714551016450000c22054614043c542c4105001000080d40d003202c1da002038909c4507292200f4040c800900f07824050105c080d0000201103500410302d45c070229240c02d5140c05042c2101280b82c01040101c3c00500407007001038080030040300700d10200700691301d45004550514402c040581459010400c1c6a19 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 292271187 1250 292269937 292269973
    0x140a0509041b1d061305090601020a051b0a0905060f13060f0b040905090106051c1a04060917071e020f0904060608010b030109020f0d0302030f070804150203070203 72
    0x2405034000c20004100b804020301d0110548501c22040c00030b40721000d500000440c4907a8602d010008413140343c01c0110084c01040c03645400d0007128020b90640e008151755900811035a040190701006031041c003901e400d003107100f0503282003a0b01e110389403150002510907001d2240c50b0142e28050078881540e4914001e000c0700b40140304d00c024005641d844000b4040c40c4000e1104003800001c0b180d142e545180c021900160f480141032000141d1400b00108007a80d1044411500c0007c5580e07040d10002e25402c00c18060700001da012050038150360104020001e0300e600c0188610700c03559803651040e0440c4a09810383c022490010f107550721548418a8040f0b06103120829180b00810b00251107450300b01040d80e8030810b941c02c6403010384511050202075000c0c041c40b0a02c1c54240d00821111040d5000141403680703806049000e400440c7d03041e42894400c0c002c1741c0020254101c25aa90310080c0340070810380d40700d44031382505140c14140704020203102100316480c40741c008006020310401004150b00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 292272437 1250 292271187 292271197
    0xb0d030507020d0b0712060e190b040b0402120a15060c0201050319020705010f1109281707030201031d0616030f060612050c0705030318030904060e06010f140a05 71
    0x40c1c00b0303e400b0301e444001030280524030302c0f50f089a074448801e0825141001d090754015000215186200c0040181910062080f0306510b6404a804201401c0c00700101e4010001011001d03001800041e460409400c0c104490b8082e1610403404c01c40040c01f500c2c5034818400030b000d604001041e144045006d90710508c09982c02c201d0840c40314504950103c0f070300080b6030104104550130707519884102c1013404544644440c03000c10081503860900c4540000c4d9000000782c12007412095140c0240c82c2040c8000c05c400c0141005070800000c21b5000300c180e03640c0d0300c02440202d00013402c2c1a94030041c50f860a402c01119454400102141d8a0710140481254040c0c070701d901c1050394070f01c04c0c41740c40c0c1c240d8010003006080030345644140d120078500704015200d00810792000c0e20020865003001400000c11a80e10030004034120140a0302c16034035505601ca0480440e0703009040003000301d9a0000748141e10b001c0d40090300c4001004901e0a810f0782c043e0b08034820800203e109001d07a03184140900010a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 292273687 1250 292272437 292272439
    0x71a030406060906030510050702031305040f021911010b0a030b06090702011e06060e0306070e0603150a0306020406022103061c0611040608010f030b0604021623100b0d03050702 78
    0x400c2d05503e03805010221006648261070907813002e8041d030020112403080540211544c400f5618100d40d00040e025421075601c502d070f0250340e80d04030070410000f10f581511244440c000000084900d5038200500e0000144e80c0c20915500c0c1008141141c5070042c0110b00700c03a40b011314041031b5a035240c2004140b0400500001c1555200c09038400e400e2000c541c00c3d504404984000510542003150050040d8044944a4002c0e8000e0080c880441c2c2c001c05409802c44003281c25607900d0350f841d03500c640000d11050a09030030888954001c0b080110580242040d544c0d10341c200c6980e0f210885040102081c9101a001011010804901d050602003450b200042c1c00c0d0342644544a55540c034941103039941d10b0aa03082080119007841010380c04451507004006402400340380300d00b503440740307640544080c0c078883c030980e80041c8405503540d1007072640c080075811242ca003400e00e40110756103800c0030142e1070070701180c000c20f02c503900041058801e0341e0004901421201e419040d5a0301507503560701c0b6100c26 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 292274937 1250 292273687 292273691
    0x110c0106030b07110106030b0a09141606031b0c060b01020c130c090807150e15070c06120e1f15090c0e0409050607030b01050f0a050301050909071a030406 68
    0x4010004000d01841008500c1504100a41d2034045002404410740050380d080a905140017000856003034555140c202100c0c07400083c4014052909500100c0080010701d081d0144800c0c0000c21b13408800c0e00d208507603030f80e10b0a005409100c03903035005801100401c5408100c00c0140b1201080d001d600a0407030072818012a4120804000040e52200d10540f0034440140c17151900c039a156404403c2500520492000382030b524100750000510b901c4400c49142007000104080005a4030803030b03501c070440d102e410301543d1100107081640c4040700302d02a000c081060003440c5003421525108015044190360050041d40460012901c000711143c12150f04032510746022121407400d903260f20303004061b5104006035598001d030380a049800a494000c1c401c600d0021514041080400e1059000500c0d24000bd41c408541005031070350f00030364800900140021440303480003900180254140c503800c03614003183e66100700d2915640c513910300070400b4031981c4255001031042c040002c1c54000d4866100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 292276187 1250 292274937 292274947
    0x90403030c1809050411090f07050904150305010504121103090603061915020f060f16110f010e1c0c0b2e03021e01090618030602120106020d0306080a020411 69
    0x3030b84409208681040d8110795503074040c80100300004812a041c00703410b540303034141d034602004e102c0c19419005046e00c043c131500103140e0703070244e07280d034080d00801860b141084450758403400c00f14003c040440781102c1c00c41103150650151801065104241115080214034000ca040d003400030300c6d00050700141d04800e0340d59240000040340c08510020700301c0d01c0f2600081611640b0020324080c120380c10401c09401900604c80e603180c0421103264450b68103a141c0c100c00e04c004904850310f1148410b5200341e8082c01170001e2218106400c80132410110008840c44042c0c050a08404c03801400c0342480070942104045002400c0d419030581e010861026400781c1c00080c003414901e1404400f102d201e2020390890900461038001c440d01005808401c0e004100540781d80064403415032401603c044c00741c0c100d081034441041c81103480155034042401e64981301d14041419004400b0701030745001d030042112100d00301d84284079400482e02090300404100d0156000d02008005004c103805d02c09000b045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 292277437 1250 292276187 292276217
    0x6030911100e09011a040e04150e03030105030d020606130e120d0b04141e091207050607110f03040504112712030c03370206010609060e090403030c 65
    0x100307001001e050740d25541101c00c0d0660402c504080c05810441c0c0070b0801c3c14001e80d030384805806407400e956010001c01016165418481d88030f080152004803e0390601d9141c0c1c46840004c40a54100c031401c0e000c07200c03a20242035003030383c5130141129103580102009038201c89610b9250090b1110300b51001c1a501d84c030711741000c24045544a54141c440311507d609000155040921401c1c02880b0541e40108050800e0002650748500d035072086100600444003081030940240050100049812803041d80c0f41e24902e840d0b901ca400440c2c89001140e1810f850030104000424882d0191130700e00061032509040c20104401082d0320f20850244070b40c01d029144075003103008042d004050080e60040309000303840c3c2c01c01401c00d488015103925034005000140310f4200002c1941c42400b0551004100d0b869048400704840341c8c15540b61119882c10300400400c90b0b00812118103072240b50340c0d011030280c2c48010a5036140d00350b0a0064002803614005008280710f0350120b60444018504030301300c0c41c00c2e55 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 292278687 1250 292277437 292277449
    0x40f06080a0b0906100602150910060f090b040b0303031602120c060a060801110904091122050916030f0c180e070e0f0112051906090302010b010c02090106030911 71
    0x11070896481442d0b600740f160b012810020641e0010f900552240740d5400d00c0c07002034a038001c6a103040c205488100c00702d40140e1041c083e030101000001c10400c01240e54840746070400d011032080c0360b00c2c10301e00b08500ea0142058081c4000a00d0060029403450301e405810211000f292040380c0110300400340c4080b00c011180c001031400c040064014943e6003803480710081121415408104c0a03071402d2a03900d4034509e00400c7c0c65128508480008011891342070071750503000c8401e51190310000d007484d0003100b480c99142d254242444134008220303a81e91943c041c0c0d80d90910321044541d2101c07844d82000040d104944540e00d01c0d105050184210303903118406881e000c0c110b040c000120303880d0094010400380411892000301020580070401c1d05249000c0380070380006001d1614064900b008440c02d21408110815070340d10384900c1e180003003819040c004014400b10703800b1001035081207a101c0c3e82d5071103600032600c02c9800401c1034020341d1908409600a02ca410402c0320700c1c004409010f031080d5070b01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 292279937 1250 292278687 292278703
    0x2060711061201140f1011010f02160b072a0204142508040c0b07030203040b030106030c120b1509121b031204080709021b061504060807080606040f0608 67
    0x862102d0321541030040b19402283c0d0012854024503081c07501319099034071040d601000c104281010095221800e0406001d84001300d140040716000056407a1011a40c1c1c0b5001503203805060038441607110b0680c21641110038a101049075940c1e40c008140482c414200001a13510050001484080d02c10403003000c03450031150060701da20b0445c0b42c1200062200d20303074040041c1c1e51600352190b103400d946103060581d440c02036107001c43c030200c0d039281014000c00c11240900b44602c0813580760340e5501801000340c03414220760030006909000c0481c41741140d02684104500041030f8a08804440c02c05002d5a04181c4020f9403207444482c0c031640720b000130310214500b00b840c03403003160b42529050281441c00300285886d260100d0100420044808041440026191440d07030140e43da00e0341d54180d0072048501c507101160381c0a800d00303001d00f80141408419174400c06440030300c82e190b6500c01064603520301c0c0c81007204640005c80081d580c0d1a2990005107403030f44518002a900b42c8070700140385080301c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 292281187 1250 292279937 292279957
    0x31404031406011401050a090306150305100605030c0a0303021504032001091406040203060f04050114090d1710050103090501022a190f140c12010204140301020301120206071106 78
    0x1100c40103008080c403c04d60210000c1080c01c100e854103030300710001002c030402440003424059680580e01d070034076030f003400f05402990468121080e10b0328500341350000b0115846076038441e10540310003035411304003941c402040300d405802405180d185142e24002030240107008030100040341c1880e52410604201c1c041e120b5103030380000100c49045d0b01d04050320b0098040c03141840d074401020000140c1d00001e12a40c0000e000110383d90544032403030943c0c091b02144940e0318010300c5a000b04210791000180d081c92039019a03403610050711803109100c40c10001618288404003c20001340919402038001038101446040018502102030103a01101c00300e0002c03850031807840c40b1448407880c6040180b010041000c009620b1100c1c0070b69180342540340d01850041041851040324508100c0031710015801c81405010310480340d407001c2c107440c000d60240c000c10314000d40504165042e0300341407007660b0580e808144a41c1c02c840e201e808100060304101001c680220210750540003940b00e100180c01c00c5d0350 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 292282437 1250 292281187 292281193
    0x1f0309120309150b060f0711030303041a060a15230d050117010507080a1a0a08030a2303040620070c090506030f1506040e0a0f030212160314040314 65
    0xb40b689001204000c1030044003d60a080244c0404983c4d038440841c1e18500e14483c140d0f5480c0e00e503141070544018040c88581d410b000100400050103100354a002e01c80104c40000300e015500e00c000c10070942c2031402840100b00710807003800001d5000726802020540580024403070b100755804154025404403581b103408a803101e004001c0454012004070030001c600d00207000c1c41c505100000c0050500400c12031030291609110741200f035000d410180407013405011f141d881516000d079166258031064060001a0b404050385140858000e940980b85803583c001510715107a91325400b014001402500d10300c2840b02c020540b86200d03000c0140322840c071414100d0001c92500205d00111840104030760f00a800904501c5001c01d40421801d0a003052011075446c0c0b901d40e4004980107142a450a140301e04c1148050070078040084104c07511288203508583c03440c81090807240c401e000c3c9040250f0b600361060080000640104144103514090301c00540c2010750300d44455011951142240840350 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 292283687 1250 292282437 292282451
    0xc0d050c0f0d031b060605090f040302120a1710080607020105090d0f08040204052d06033319091a010602012003040c0b07080c0d0207051f03091203 65
    0x3003088032201c0c07554803088481c20b98000e042d4501520320b40703c0e8403481242c00b0150b02da000401215a010102030319000c0d1041c7c0ca1031400c0c1140403c001010740d801e8025102e2843c0f00e050303401038141111421906640d40e08030050070849000c1003601c0144c540410101c1c1c4090115000c0c1c1c08004141c410f2050754000300352820b00d10251410305c02100000710070009200c2603107800a410034115138106074181c80005055840d484403071700c0040b0b101f030511b510241484d00345a40b5102182c0282c0180d004600703807044803004640e9860304018000c84c44401d2108480310140d01c00c0091394403a03004d29915202010440358a008008543d04940200d07007040d40d100c50030070003a005c1c485480c0174017a42e000070802444134900030a40c041340e2400b589a04c840c00000a8100010182000024a104200c1544451045c0340c10b00c3c4070380103113101c0a1310b485040d0a6807172035440014188101c1d24080c00d803d03150100c2a119903030302001000300800b07040d1601e001c44005420190904001301c010340d8001224 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 292284937 1250 292283687 292283689
    0x3070501240803030f070e01170112031202030405060103082d0d050a0b03030f07020303271e01120c020a020a0303020f160b0f070c09090b0610020105040c03020405090c0d050c 77
    0x7056000300005610900c10007507141c070809095a0010101e00303040c03019102c1d01d00122450b10800361405801100480000f078081c848007501480c1520030744034006105036071f40c500c100b00e0008032070240803a48101c1c01000851114402490701d85d603d1464a013400d02842000740020010880c64007655100041c0460300c0c40b01346c440d00b500182c42e0001800a0a40c240c0001e0341c0b4041d4105606696400040c090115581041120321240038446c2801e000c0901c5203100525200903c1514050020b8948101e84600000c02c000354400050315694400380310550403c00030140f4a52060551084071105009a41c414401d04025446035004002e04c900c0b09400f942000001912030403c3c01d4114010720840c01c103141a56074454036140925164a51400c000002507202d510295000c3d1500c2c090034180511420302c24407818060300c803200c070b00c101500100d0890342d0465001e4255104d204090006250a030006500400c0f9141241c1103002410300203003000c82d91401c03c880c280c1c0000c14035405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 292286187 1250 292284937 292285001
    0x2031302120303070206010506130f08100b060304051005040609060e0d090f030308041502220f0b0a05030a1509140a0c020d1d150d0213050603160c0503070501 70
    0xc1e0018007014500b0b500304038002940d035510602446100e5113001c03401c010300c04000050700c00200000e5102c1c2c400a655100140e895000b51901080c140b424600304c0d1456041640481b40611340c00002086011200d05d4050010000030b0422aa40c036202c142c4640800c2f824041c1411038080400034000d29010702501134840c0309141d0002549800307440d01000030981210304c20781d100b074000c002034020b0203080c41c210303000f4820480c00e0441070f004451100c010042d0500300b5000d0340d0b0800410f1a80e00d4861500e8410303405003640c1000040d0040000400b01ea5590300104143c0c285201d4020104d51140b0a40e820740702c0c40e0188020410145041100001c07050040810050703990010303080ca0103d80e82e00400f050461602520900300f001c040c0c20490f1580f03200203541c09010b042c0252900c81c00c0801002079480401d001c205a001030001080a1078600704032030046841a0b504101030f200b048050391121748525080d50103000a00500000c1602802610301c1c03540c2c0c81000d0071f1038200600700c201ca = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 292287437 1250 292286187 292286209
    0x3030203133206040905090607021014060105090a090c050706060902070206030624210a0c0917030409020d02031b1303020d020607020307140a090e0d0c021302031302 73
    0x241e100b00c00050040400440141d4100d1021035501d8550b4201c00e40041446840365500c08a0300b18500010882402c0000c80d5090146c105d0354250303150104c484007100142d034803040201c0302c0400020b02180e06d56020344004c1c1a900c8024100744040b0783c1d40d2098070112900c000b00034012070f5002904008104180c410700001c0c1c14003e0046082c5001900461403600002b06030600802c803c024240340b82e0091035540985400322050030755102e800c0002c864981d03d4400c0e801840500080c0498124801030003a00885d801603640c04641c54601402d0200030301d01501a2080ea020030080810300c0b01f0580000d081140c0305c4500560b89040590b884110041000448805020184890340014008002c11000c5030f404a81800d0081003500008406114004000b5410300c240c26002411208042609103191b204450202c411540c0f01c0d08030040c0c915082c0310018640103240c40342c100030301800b502c003100380c0040c00b01446002c00140841c01c9910a68403c502c100180740018114642401c80326 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 292288687 1250 292287437 292287449
    0x90605070e04110c1e0f0f2d0a03050d11030108070f0503061302060306180a0501050306011502071514040303030b10110c040b041803081f0e070e03160303020313 71
    0xa2402100c0d254031500d4a000f1242d40341c075417081180c01c405e541c0041008542410108003551980c1083d100081e644400a60214411004400d44c0c0c1415901d0001010702d1800c0104c0034190312080c1d81c2e412520307940300510360050590b41da0741031604070441d10055400b030800d0f40010140b4a044c0040040d00ca269580494443d0b0f109a08003d1144900940803441d2030f81920aa6200e483d44400900840c03503c0d6241d849040c0d40c08208144000c01d23810650407150f080e8165031603030340ca912581082c2c0c10410720a02c09a44909420401e00809801c0b800c080321140c94001d0540d0202c0041003542d600c5580700381c000944850444900c3d180c003280140146c2202d00b06a42d02044000c7c0715500d0327101c1401601c1c4550303903c0300c0c056030a413110b03042140349002c0143c540352050b0040c80d000d40f0b81202552028400c0350340107154482c0089100d0385c9401d82d00c00803060010f80e51072840485259410618464141c002c200c2d80c0460b40740c0b20054400994070903006152130324100310120715611a175030700c28 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 292289937 1250 292288687 292288721
    0x70e010b03090a1b030602030a0f060801111210030212030a030c0504051302160204060b1b060f06090414010212150d0308010b09120609010915150e0901090605070e04 73
    0xc0030b1042e100162080c0095880141c44801c078072294079182100e02d0542c405440720f40000100801802994000080d00c803540c00308002603034844900074221010105620510001040742d5148003201103030781a4401c2a21903003081e200d0b04c0741d011500444034010341e15400d1b44041142007055415000d070816219a601d803180c1410300c1d00c0c00241c1b540d80d03110500c030703c01a40060110740d0100d026544c2c80e0034580140c01400260360b11401d0102981c005006031050b0000c094030358103401404a00c0034003426002c801c0c202079485407403c010051901030000c84104d82ca0400010848400380050f000d00b84000002011505d41016641090184084200c5c07083e020a00c00302c00181c1c100719814152400600e120740c07954a41c0d0041218180c0103945c03000140710790000c00c1441c0505401c40c40344039100700c010071405004240814140e1327050003042481581052402e001512816907005d6015032010004a00e00e803464a80c1800c40d4810354960001901101d0f1900b141d003401e0141d074800108800305 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 292291187 1250 292289937 292289941
    0x10f020712120507050405060a02010e1606090b0f0405091e07080a0b090415050901060302040905061b0711010e0607060c03060501020c0a24050909010e01090f0c05090f1c0302070e010b03 82
    0x4002c0680c03180d4047c0a1003108080340c0c09a0191003503001400030f4007010220354004c007100000031103d110394031410f400200011000706010400005440d803041f42204068242407c01c02000508900100807214001c01e11100300302000d08041d105014155a8589800302d0030013040c050f080d03407000c100d5140034010020034071001804000304404d07801070503400003810703449060299001d841c5643c400f0f035000e420013100340280300c40401d00b80c2c098590b08500001c0d408800080103014004d02601500075000d1071040380582d4003038030301d654580350010300c1c0d40d02c0e003075031503a0700c10844100c0001d100000340d584906019558042100f08110b00b0100c4d41114035601c0d000042c102c0c1000300b00c0c01400a81540c55820207280584291101000010281c0001c4e6856004c000301c9040300344181d00e0010f00340b41030300180046911415030010500d5444506d45a43e813070600c0f401020818080d82c014040019010307100c19071400e820705191096021349180c0d4034005d4084241d61040e0400b03140c1841c1001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 292292437 1250 292291187 292291201
    0x16150311160515040807060c11031c0501080a08070807080706182a03030c110306041a0105011404061b080310080c0603010f0608041704090501031a010305060c0c010f0207121205 78
    0x1034455587d80003030301040c2e01c5030b5200c0440703812110030400d409600c404111541c105000e8106100000f540c10340400c9a0783c0e0b5441c6141d511500810041d048007820010349021800b0180209107090249000071702d005200e5803044c1c202d400002032000080c11103410f4000300611580090103100100140c03040d10400d0300c256188005103840005c0900006460400030000c140340701105180008060740d04902d050b0034261448030803040324030341c511403203000422a58080d41400300c000c02c50390354aa040c0350808400340d03800c0e8404c2e507000340c0d030f016842100780c006441c00004600c200c5c40c3c0071100e100c281c94050191b1800d048422550302c6048180014013200140165110803200c1515107240e41d81c44500f000300820807080c088034100301c0d0024010900480d16048241201d00c10441d03a001c909082c081c11101030030030b0100401a801480114020041c400094950034540d0000040c1d01d05c1c03014042000c0f42e01021040300c122a00c030342200c5815421000921481d12400401e00451401074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 292293687 1250 292292437 292292453
    0x3060708240a03051c08070f0525060905030a030b0a0b030402210601030606060909021c051504091109010509070804031b020306130b091615031116051504 68
    0x9820075020140421a6000a64990006a0007150000244c61003880c40d628030034407050500170480b000c0b41e240780100700d06a20072808890041d039240d942d1401c20315050b068241c140c003801c5050a42c010300442ca10f0104484c6c0c8071b20b101c03040c8104010342d42d0f24908007020f0b0a50350002c1c43d15209480c418010810218900c1c01c81380e12550450300001e8442c204410030461a47d450400000e0344280d20011040007c0366111500340e41a988468090540d1603e0005c164458101014056000c004100311068066003059800900410700201400024400709040701e9800c0382c140c3d01841c426040483c3c905040060794007400b000e64185445241840b00a40191005030008080024002e2a02181c1515442014041760700806039249420305103142c04184d1020401590a107164601140250800190203c1c500343e04640320503106140c41e4001c1c0d01c2525844078403041c151202c140701416101000200040850900301c0d004901d81e5040c0549402d42050400303903249050070900010071090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 292294937 1250 292293687 292293721
    0x5010f1709030f19021b060d0504170703020304140102070e01140613090507200d110703060507020a030306090b150c0f1902010e0d1e170301090b03060708 68
    0x80c1803260a07211891100c1c07841c4154041004481c80106103880044184243c1e03a25080e080e90843c0d681050840d020b482410181c040c07650304c0b140801a14045201642000c0d0340140212201c00b50f4a0150b540140a03a200b020110010381000400b0701c25481c0d60102e0446400081c8020401071b8204113043c1c011007018011040c0c5403009111403400d90b07884130b084a10803040502c0d076481266550f1881d4020703100640b0301001103054807120106114640140c14030705045000140086020f083c0160f41e1980603ca6542041c041c894010022920300d024043c042c1c0280c0e4010520340b103280c100141213411070340112032035600345032961005544003603105814103402c006580d65007070039082040c500300682d0000e8440740180d280400700c1394090205070f51100e00030b0700d440804243c1d0000700300740060030784002080d49142d0103c91211010042460b1160340c400e113002048600482c95010064000341e114aa149881c0c07100d00c0d04d141414010160400c1e11800c04c2c450341e040511480d4140400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 292296187 1250 292294937 292294967
    0x1140123090a0902030a050708040507061103070503210a0525210b210303040605090f07030b16020c031b03030d050f09010e0f121b030d1505010f 64
    0x14100324004502040040307840c4800020885203102d555100507030040c0d00308031452055549030400007082140110145c030700c15640701010305040e03400c20344141c69060b081803209680c0d11080c088200014000c00007040440807e2614480e15000c6003c00c0c500c480c030080907a03412500300024404203a026501c0403a0042d40c1010340280000c8130b25044a400d40700849080e04042114000100a1801d6012a40800041e91100d8510360141344244034804600110402548208001004039446034402a00920420309a410300c00194000919010041d00160340f00701c10b180c14441d0300407142148110103507007030000d004115420400241c8072100041c1c3c0c903c7c102d42d0714000400550381481150741c0800f084100700301d1814070007620805980212040002036103400344c00607164000068103042d010048000304103210310b0f04d050440e0341c0c11450803800d8206c020030f0b00c5120b04100784040c100d80c001041c800100810950404603a101680d401340d81401901341c41003040b903901070301803945010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 292297437 1250 292296187 292296227
    0x12080306010c03120515040609060f03020d0206090a080304061803020f090a110409020d0f0203061c0807021201051608061003200a0207060f0207140904050a05010e01090b011401 78
    0x2c002c0c202540c0311041641822507981c13500040140100000c84080b21002013030320100411030315159040115801405182d0146a07488410001407400c55400030319a44040d24242c10441414040391b0100045d0b0004a40d075040070405000127680800b99901d285013280741400c102e403551700031502e0200740201c070900510781400010110101c540180626040c14055507544075038070500c204c002c0d0441c410a5115604040a1895012490007541c1c001c0e10003c0002c000c40e2843d506038210050841011a40a1003e10010000d03907075603902c42d245440064004030759403414841c18211006401d801009009902050111a4403000c1c3c0c2186101441d00380014840418800810140300080c2200c1200308e0001d44d4204041c1d02140080895400d901c0f0003030300714682c40040c0e80b100441c1c01041c01c1480200410300b0107160202400f9003141c01103042c1d501c0000103450741400c3d154443d0202d140e580d11804600c04000c4502080350050440710240405001031000003048400d0300e44000c0d010342 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 292298687 1250 292297437 292297457
    0xc15090b070204200c010b0a0f030b0f18010203100303030e0a030f0c020d02100207060212040b1603170103080306030f0f0d3006263f070c1208030601 66
    0x803241c089940300861000c01c44d980c80b0601481880d019103c082c1d00700c4d004814825000030411515081d0100b505e5001421148554424078078480c08000203202e5114070110740e03100c0554032028401180a0314500d100202e0351070860230081c0c25501c0200880f82c15500c0016003201207030780500d0742001d5140618006860070758a000103001000e201d02d000e5404206030740c94421340703500061507001301d50094003915043d8040c00500b61080c02a480b804007449010098500403800020041070050701c80d0401e4010aa5058122009503600741c2044981107400018482c00c1e10f020044802420031880c0140106100d03080b01c2030300e51080c240000306002500003840c00742d1a180c140300d040d104041c101601c480080e1020356000d84010300c02c400e001c03100007142110000524201b01e5441c2c640384000d000601380304c400008000184079105080c0344c04002a402c1405000c403d4003445130030303481c41d07603110300076410030402c00030030742c4e1029024900c503498100c005841c0c40242c03640440700342030038140d403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 292299937 1250 292298687 292298711
    0x30e15060f0d1406010302280312031d070603110c0304090f0b060a030203041a0f0f070201060b0424020606011b0204270501061e0e1803070c15090b070204 68
    0x1007040600040889920700d003c08400000084d5840c101c9000300c0e880280034005080f405180f03070740410240c480030b0740b2613030500c0070545080c1080c0c80f035650391038000340400d80180d00140740550424201d000c0d40169008109207903260207100d0446a51144080c074241c01d1a00241e92845640300d0711203001e4840070119541da030194800001407078050b0040d540e075271903020000c0c000d40c070455007103445508649460003980c150980c154800c2032a10508584e513142c0031600503007501c0c000c140500b150f40300c003000b0641c0300090003d4001855804044541070002d025091001c0c412040c0795003c44d0700c2441000403681c1e00800c1c0118400d04449208e03013600c01400850041c005046005007a504000b580007840c07125448203a01282c0110001c1040c261102d509943c0810485807010441c0851482400812003807500c250b08001e0300c00390190306002c00613089045400110042d120308203030001c1040008001090000d0100d0540381100400342440c54202c0c5500460601078021a991006001c0c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 292301187 1250 292299937 292299949
    0xe07051e041d060408130e0c09040905010e0106080c031c0e1c060501030c15020607020d0f030b03060906040c0902070503070602161a010810050c090907020a060e0d030e15060f 77
    0x103600c0d191020784000d4585070170841c035294080c0c0ca03420401c4483e0840020010072990b0f00c6401144816603451034076038080308000c00f07000c0088065845560f2a848601d41c0c0c2000d101f030000421058010b08032080b0004109810b08042e030111520010010741d090782002d034454031079080e00b0350881d204442009100742c64100000304543c001c10003450040040300380101c80c4081c03402c81740b10480440b0304601550341261600c030240c55507405070f848188114505806006c07100840a40c9242c00182c1d0800a400245089810b458001098102c2428002400515010000a809018025490848580d6681e40e0340e01c40c01002504250f80810301c0305601d008880d010f01c8a07600b101000d0070780a01901c1c0007003440000e21550010f88a440400c242c202c40900440b84203030b031500c900c7c500703091590707090140d4414003c3c40e002c114000d518132400000e007913214030718510b160000180350110540b0400380485202021400d500da03c444541408405400030706a803141c4141d030740d0f0801d40d12190110300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 292302437 1250 292301187 292301231
    0x20c04200309100f0f060504021306050f1c0209211c0519030c030b10080109020f04171606050408030703030c05090310050a050c0c03040b0f09130e07051e04 69
    0x2030b40340c10702d14070304144c2c4440e4000354006103641c1400c005046d179031405c00080b80b150399800024040300101c04c00000d40a82c02034070141044001d00781c41c01000b408240e005d20340c1a040300c43c1c616808954061366007009440d5210001d114043c4481c88104038040fa0703907604084201e04d0515640c03412040c0da5a201d403040d1500f1349502c102c8400d803081841006000f404200080320002890711a050302e543c6002d00141001d15081c0e25035007090390801a40d60040e5110800d501f03501f00301000300141018109040b1066800144080c01410580f9001030500842c2c65002d102003260602c0280320704800030003107412040d03260800207400d058503101501c0700d0142d45081ca46c10f0013101c0301200c40e102c0d660425881840305410030070072980c40400400540c015054280461780c010f000074007072502c0702030080c10702140b005169070900a4480000c0d82540c070811070010025210001c05002850410002010300802c50b00e039480322400446d101d034010300364290035116039188c041c0c3c40d41040c0010005a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 292303687 1250 292302437 292302463
    0x6080a0c08210a0c060c080901050f0c07080904090503031905010e0f180c0a080d02010b040218010c06061a04180e1b120a210306050a0320030a03080601020c04200309 73
    0x4800101ca180000d0241102122008c5040d401c050000d02c0c80d503001c2c1c14080c4a91320811030b0a090440c543c5075451741d50020100103030003542e9002030b040402c00070405180f1410f209240061188001c442c24000d445060340a440c9a0040e4000c8c043c1e02c1c4075100c0c5840d0b010440c4074001405122a01995142c0508060001e401000a0302c010907076060205402d070301c9030142c0d0024082d844c060418030049119481c0062284540c1c04458031084d88500c070340842c101e01400c40418031584036014080300310403560040407600e00020b01009145900d1500c1d200c042c10001d070802c803206084100c03980700c90141c615184503281201034099140c1d14201c10f43c80d40414001150701c228200d00d040301c2503648644010f658504000031a102c1035200e4050b0317000703580b8090321092045203541c0d2200644104c0812400c52540e5045440c0d445803820000314600310301a66400c04d00d0708142d00064280b801001e00c03d80598244000c0405050080350110390852034000d81565030ba45000920703091400d070341d1140b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 292304937 1250 292303687 292303691
    0x4050d0f0f140712020d170f031303111906020c01241d01031218081006091a03030f09010e0d0605060a3003050d06080a0c08210a0c06 59
    0x40042c800d14003202507614030b00104070f0f41c105403a119600310040444200950001d014451031002402c0041c2c900714003002441641e041c501008000301407900103d640c180c09030003000c040030615038862002d00c81c0d150600003802c681040300348c2141c842c0d02141d0020b0300b0f1580005a80450480c02d51110001100c014520085e40d4030032021280312800511921909140000b000e0485050703980000c0e049951051015a800107401000d40700e084c20054203d0901103e4080041d000741c0c01d04c43c658502700c0302c41c40003030050304205c40c880031215141c0030740c05011012004c040458800004440312001c00000441c1c480d001800102c03040483c0665594114a03412108400c00c2481c0e002940100800c031021211203440e080d0700346070306041c40c140007143c0c01d1030310b441041403d1105850080c0c60180c0b510700d18180c1c001400100781d42e030311361140c80564040440501030110206030240a004024054845000d9000d0001030300d00310340d0540800d0f0741002440322911030280d0381d200c00c050361003001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 292306187 1250 292304937 292304963
    0xf030605012025050306010b0c0a030309051501061211031b030402040b0a081005010605071e11040203010f0905150105042601140601030c0228031101050a020405120703050304050d0f 80
    0x3d40f00c0141c40d10310400d8040d10030440040f5244a40741c0a43c1c0528a05900070300703440d4450340b405c8000d4591003c0c151040e0103101c0001003038101386401680030301240c0c3c451072052000413000d40201c49101d01d0501c0c0350030f01813040c09a048001d002c00d244460072241200d032280c8032400010005e005403002c42d9485044a080003c10322001b241110301803002000420480c0c2e0389410a071007034070940c0c4000f4003518101c201c0b10340d452803203400300000c6c40c021a200303030001c242d00300480c0c2241d0007a08140c10b48003d40d041008015040d005542d4000c034140d94409816a0301c0d800070344507005034001d01210f01d058030030552044162880d005101d001c100002c5c840115211903000b481d260a45515000908090070746094134000909046d200d01411468a14800c0c04800d03c59681f6000100300c04001014071040c1010409001e40790080d51120001039440d03142000700124000300c81d4103a0b105400c4985d00f000031910100644044030380036601102e0340c001d28078004800900c5414000c0c00c2c0803052070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 292307437 1250 292306187 292306243
    0x1020c0d0c211205040501080606030a0f0c0509030d0509100503060310021204110f0f010f030f0203010806100e0106080f06010e1e12030915091815010f0306050120 72
    0x82c880d00564080c420740601c01c0d0042d40211803031300c103600506000c00e841e180498928140b1000869009040c140c0014880e4000741110303042c5c45140307050b800062004a20351005180070b0120f44070b88540c4c0d007131240c5081400030106111114440c011b42c1805008000200d50351400e011154130b803607152034119655101425a0802c0d40c0080e1415299070302511001d1540d81040d448a40e60244010714003078900ca950001140c803e0000300b030f442c00b09903d440011801081d640041c50180030440040d02d6203280c10303181d401c040340c0c11354468841032681d40300401c402600414030a4000034241c070016641d55407400160f580b07003141965a1340082c4807480f080050030011041e000302c048211503952a981c4016441503407809150320715580030900c5440542c03801d02001c010030300c8000c0501140103500d070440750388141820480d0411402503098101d140150380c4642050600680da0800304012802c020000341800d65403419540708080b02501c00405603800c025880c0c814441428500c80044950 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 292308687 1250 292307437 292307489
    0x13050a17030a0b0a0b070f060b120606090c0f0a3c11010605060904050415020c1014010e0103120c060e010b0301110403022803020301180b070e01020c0d0c 68
    0x90b458541c4529096403016180383c014400c40850311440101404c10071180c40303100c5500450441100d0302ca03640c41e020103043c0c64101c4840300090340c21018140354905442480304540d0020310b014418001088031f040314420040aa4030203401c030f468032040c4030b40203a038200202c090781d035074104010a06004280c040200550030b540516059510f040c3e000350000f00950a980c498001c0d954008828440d651040c1020b030b110035403050041ea6010340c0c0035036440d4440100d074802c01c51140250018080d00034a807a0901500080824248110003651301d840c8a0040005060100802240061950301d52a82c45660600300003038110404100c24907180d040d1500030180032205600a5090a00010000b0008803e0314200e0380c000e00b034440401c080500c5ea0202585280d9000b400c0b02080c040070000d600c0900c00e80c1c8020030b41c102070034070311500c60030b000316100002444c0c01c0410540004010b4070341d074049142d1200741e80941d100100c1d07101603c2e00c418100b115420201402d03d0b400310704c1700051116 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 292309937 1250 292308687 292308691
    0xb03011116140102220510080c030a0c050403140a03020d0c02100c020f1905013005070203040f150e0607020a0302130e0f0304030201080c030f0c180303070c090506040e0613050a1703 80
    0xc0324011060407030124188c4e1403060445500700800c00500001c1c0030709005e90030a0460300074a20300340380341a8a9036100308400e4016003050006c0d034855190f040806404100c0d60100c8039103030510013a5001d2690004412600d00d09c0700608012060030040e04540302d034040c041c3c0e0464014114507142a81d00801c10030f0040520513940041d24084811000034000072031034070030340e101c0084036040708508d80780032024050103400700c000c510003008001030351a403d816007005848940390f220040380342c9980050000c03609000c0140704600401090005030ba40fc40200d00f142d5040c2c464115400d0940800b500900c0c4450381020740303004000d04207100b0741c0e0110060066a100340c0300d0032542c0e02c2d1300e801c0d80c0080c0011145004881c1d03c200c0860580c0804034054440007501556042e1b000105201003030450700003801c100d4035500041c074240001c9030940a82a07000c1c4082e1000c00070341c104201313003e80c0c626014000d07491120300024a6402d00400f48603034040301e900700300e8104900a0800c50481542c0c02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 292311187 1250 292309937 292309939
    0xd0309050619200a0b0612030d0c0e0f010509012708030301150503090619060b04090506120303060a0303120e07120c0e04022d130b030111161401022205 67
    0x3020609803d4000704400da0050010503001040c0c004426904c103441c10001800c400d50101086c6815480420104010061420003041c085251510001c018100d8844000b040740b1450300300e80b1503140c50340d1040544095007000d20706032030107408801d4007070582d9127982c0b03030f8141746620745c0303004200c110300040190b04a41300400e441c540588007000483c0d0501041d1407100c5141c11a00c0400c1007072440c86c0c52045485910f841c001041da03654032602c072060f40907500108120303071194204100c0b840d0a012424440b014070014510714605000021652540c5002c01010b03c40c07000031000070460150b0081e40a00b2444040320846500d8000f18104000065400c072201e104085000c524011442c021a01855024084988130701c42e94508240303140c07201810240200034410f8040f119640c00312072903074540580500086051000301414251220740c404507110f03240030000362110020b4041c41e041680e07080b0030000ca03c80510000d26002e4810640d813125000b0301480e4101c5400381c014400011034038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 292312437 1250 292311187 292311197
    0xf13031e02010806040e0606090c09030706030501180c0f0c060207060c090515070308070807020f0105010e06030d0e03071710050415050708041713050d0b070206010e150d0309050619 80
    0xa04d1208210136181d50f0401d1040a030400c601040c4241015091960090f1503552080c0c00e014901001c60300c1d01c2070301da01410000c6d40725001005050140000000100307007820003800010410b02c400b5060381204400e080070803a1081800d018081d02e0750560755019880081409501c01502008007500c0d43c0740200c43c8280b01160044000d224000200c50740f240c0d0548840e070190b42d4108081d20320a80040140c01540030b03242e60440008400e12566000e06603011410565051170810326103840100940d000c00c0c86034141c1c10103040e65001404104891440b03100c00d441480c5981058113100886e0705482c541d908001c00d20081000c5c80c1d0001004c409c0d0603004000940d00c00f00121011a4103550192000702ca004004800213221801459948203491b06441c185a6410200c0c4001c41d2200c0141d404840c20300a0010140e4184240f07130042c000e07507080d101d40f030600d0818542141a1900618031441e6084075a0b401c0600070303040e50000301402880703d5111103004402100007001e01c1c00d2000000e0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 292313687 1250 292312437 292312441
    0xa02100c0501090b0138031302060310081c021507020a12020604120e060304031116120b0601020609031c060e15030d080106091a09060310030b060306010303050f13031e020108 77
    0x1810b010300c3c0606c03c0f2514001c8950744000e81d05500010741c406015040c10320340d101602030141c0c03100c50007140201d001403d10070310180f50121706802c14400742c6820000044040d240208a80e000071000a28800c0c3d880c40d55043c0c845003410307454500000d000400382c090300420070340b0440d00800c6a03480346000328413605200d100b4078800c98200100c1d140c0554030004c00d04c04100424840e120014a0140480484080d541a59079000000c1a03541c4000c207000c1030030450504020000f8400c1d500140b0030700041905e420110000b40d281e000c0e00803600340c0303003080480750350450721260018402001042c560359800d0402d40c50103180694140c0142d4013900c01d0302c0344c6548031031141540034101c801343e81d241900d20b41040041d080360122110026031b80f40050207840c0c80303941c0d008011800340203003404244909255280c00c070200800201014440c0d0400001000482d0304141142c40e103c407440c00980d9500140c4900748001d140742c2d040600f840800c4540302400344103800c00500014006d0b2500400c2d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 292314937 1250 292313687 292313729
    0x207060c0308010b090102070801110a090b0403110904031817010e060f160201020706050708040506010902070206030c03070c330e0a080901050418020315030a02030a02100c0501090b01 81
    0x3205060a004000842200c01004008000c101501034000140b050701c8089664402c010300f5512070382e08403074030410002440d00072141c01204920007001d02ca4015814946140c55504150f100340710040d00541c00b600c00103042510900b00c80381d42480244032400c0040d200c4071a603510305200d40101e6000e6103808075418a605001884510840e01c0304500c6400340c1e2440c00600d0b0b070043c0c003412a41550b4090120500181003406a0751040c9403a0b82c07450b01c18074040c240540b030048180d124102c3d5520410241000d62601c204031ba5002e801c0c000d00d039a4035124950200c901080281c4090001c5070000000001c0d80d42007500401803080e00031041c43c02c0c0542071480400c40305003903040c807207a078000781d0010001680500608441401410100c4c103160790703000c2003030052031140c1182008960010401c101140a503041c2032320900b040c0c00500310360640d580481c0e91402e0008029200712400203440750000d10518900100341d6001c8000d0000d240f540c0340000072101c00303008610001510340e1300c810348 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 292316187 1250 292314937 292314947
    0x60105040522080a0c0c090905070b0403030903020f181306050a0c02030405090c090d03020708010f020f1803010e010f05012d090c050708120615040510030b040e0604030807020706 79
    0x40842c0d00a02d40d24102502c0d0340301907a9a01000501d02400240d5102c100459008481c04c4020b00110101080380c001518025003051015005609007100234001800801e9001810ba01940c0c0c1c1900c04802003c1404001952509410243c0300005440800c01140e000d81d00c0d141c030072a40c0708030410b0010340c441d2110802030b1000040494016072040c0020451441c290074220341150030851800c1c0707000201d002003401048030450541c0560320940742040268001d00c00c945d6200d0062038210b0403c94841c004d1481071240c2054000348445a0041249682d000c1d841071454410b2040200203000312130340707500040c10091040c1c0e28a0b4001c0724407030b200c0210580840a800d030296070010305030380c1007074400c07402085100600c4080203000d21810001440b4000100900000f1662082651410404001144021102425801a081c8420840b43d19540404507808000c2c0c140450b02400602c0482c000b40b074140c141a80f54450032090000b0300d60001d08050180c42d50750300303841310701d5150003056030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 292317437 1250 292316187 292316221
    0x3609030c0d030b0f030a03170a0209220e06071d04051b0d090f06060819020102031c02210618040201050406110c0d0c060e0109080a06090f060e0601050405 68
    0x1950300a0701c0301c10480c5120380d125258050b0020044041000800b01007460086481412004500c01c560411b100e07000c40031284c0c1c2e01660b00841980b8041c02038002c1540100c006405070800d0000003200c079000e040d50f41000620011000c210385007032a242000401c42d00c0b41070031034454a040310720103030030b241024058580f0906045043c410300c03010070031200c4080c2c0e220400d501d0010b503844c9802e10008805134440426107024001c0880d6003070510007043c0c2000c00a80f541c0c1c0d05030b5003c100d060010303600881a41d00300841c1300b042e070342014900703640c201c0039201d580c07502c491b840918442001e081d0100c41a481c01084250340b003490780c07243c51a800c80b040d0030596019010510501c020440700340b00c0c003520118407014405595804607600c01180000d004050226030301d01c04200c0a21545601c1145261209400d181a0000341c0c42d10000f20344494814402400542e15641c400c402d00144522124525078401000c021170003420f26915110482030003014852030415000c94031100211100311 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 292318687 1250 292317437 292317457
    0x7090c0305090a0209061507030e011101090507180608060a020a081e010b0a0c080a020c1903210302090a03050601090b04020f031302120102070501090c06030c02030414360903 77
    0x7100d104002c4d020011240402010694081140005101828020b0019000d00340c426102e910048400100142000040814410340c6a14184044010440000c0c801085600502212100c80c108811070809454150030a0000348160f100340031400c06150300400d42201caa42e12a03400c0d459164061a0388501d0380e080c1d00e00e880e502030048c080d00143c503009105003411410711011380c42182d07503030381c0580d041021984050b0700170406000190030004405100b1459814020000500710f030b41d00000007142241e011107500340741360702c405241d010f40d045400c9804001c01e0000707015a01c1c035090750703115070900840d5001c1c0c1c20301e031484c40e05003014001c2d01c1c080c00340150000d055aa485441d41403011000006a030311095030700d0541d200480a100a001c0c060291001007100c0d803003030802c400c4140340b83c0e0000c410549014000300d03d45a000c000e0742c061f0798514000c07810f2011041c8c0010010070380030740c51940300040003c0c115000d4111b6821841d071040c2e04050207400e0381e54506881d8a80c002d8410324 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 292319937 1250 292318687 292318693
    0x2303010e0f0a080a021f0e15010b070605090c1c060e0111040504020702130509010e06060312070b0c04150f021e0d030b15070f020316030f030c030c120207090c030509 73
    0x110b0000d031050000d01500003840c412240303000f0142c0044a618000c56492503c115900c541007200000b06010200c000a81152800f09552400641d880e0b644642100605100c0e030700d901250300d0140078800d20321090030081c0005c2041c80b100c0200c10001c44602811611203240280101c10502d040c0500210a40800300300b504262030003060101942c04008200c0c0c0c405c1c1c1c1219114915500d40c41081e004100c2e83d000043e030b10480c00000c0f494003c0c051f000c207100b603101e03403400f41d410030050048842c65030703100214044a8903110840e184d540a0b0350030540d101c0355100b0408a107103900841b200802e0065508030791829210084030b400303180840351165442d81005103410700641c082d4020103480071000d8000401b50461181100c0035401c206021981640580d1156080d03140801c10b822071a0b511014100c3e00c00d146549250300c802004100070107010030618000181806070419043c1a03410240414054050b001d0094885100e07000320103040741b410320208400c42c400c0c85454810314504e401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 292321187 1250 292319937 292319953
    0x501060507081c0c09080c0105070818210c0f0105070f060e1e0106030221030a1b02060307090602210f03040606150503060405061e040b0402042303010e0f 68
    0x2641140382c1c03044100c1d0307203000248210403612007000d129500856016039904100a03042071b52031820851102411070400805010841c0415440012500441a01076450039a4407014020800014202d0700e070180380411401001074042c80858400420b0707200301c60341d0500b1950ba10055071a809030100282242200b1ba00000010714036074401c078840c1c0d840c80d080301e40c00140105030407411001040c024006035140c800410450404500748039095109204c0d2103912808080403665a01851026008118541c2141044c80c039039040c1451010360040e048503964902050080e141c851b03984940c50062241e5604030300402000344414030829007240c03059240035107040040060340c10180040e160b195a50600045134091340b9403108513040280ca401d526851300d0000c0208807500140b00030b024100c0704003e10310100c2204c0d0104030030030049400180100100001c00c0080c000c503082100355804031802400405610f107904042c4020442c000e00c103128210410544441d10000d14014680c0210701c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 292322437 1250 292321187 292321193
    0x5090f0403120b031002041505040b12061804060e150c0901110708010c08101a040b0d14070c05010e070501090521060c030a0c02010c08060d020d020a0e0601120501060507 75
    0x10000c002c070052140c0200e154590040000c0c2000300c0c81c6400544164002010040417a81c0410000700340460304141341014503000400009100e11034607000000e0300b103800680703940d07119480c40b140407030710030310b5601580b90034500307039000b481060203c0129215a140c681c245004036940e1a00c03070b48252507143d051405a4005580d0301d0074551007000b560045200220b58010240320345003c41000395a02c8030117043c0581c02c0079800c451a04000300c1c0d107000421411030300a1a108070b0b0100d4007210006591003012001c1e9800074688612000d444401d601d0070f01903042d520491520100d8051070080102c460b8661910b55289510300c1840e0102c0c4501c08108101d03d022601c181401c260185001001400c4101e60b9042180c02c89140b49d9044010080c40b1010741c40380708200580903a40001c1260100c004009400f2103c001c1249102d00d602a1502046403134045010030b5040d409071660b04401d0f160224090240305c21528540000c1040060303050422407802502d048400030744a0f00d141c169991 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 292323687 1250 292322437 292322447
    0x2d0403090b0d020418060e090d08150d020a08070609050604050901030b09030f04060207031505100e0601020a0203060f06090f01123206040314090604090209010c2a05090f0403 77
    0x2041c0c41ca002e03070342130000068148529400d008211402440015001c2c10001c40c0e960486d406480f20413203621a21240750000c1e08031040a4009020a80b924180018400020b01e4a44038500080d01301001e00d00016540c02e0004034401520015190f1003600740d200c6007402094002d61080513030200107040100b000c100420381e815000010041540d1800118100c08c2030942c0c400e0b40b0100c01030703105200030403d00980000300c03449400c0e0b0030000e000700c2c1032800610041d14503d010f94a007102c244004100c080e80204080500d81d54007400750b807e076281c034040c03010003d9000ca40c13050082c50150000b803448000b20809030f040e0340300d0f0041d01c0c0d081d00341a103d04010000c500c0518421240e40810003950080c00e03183c084800f044400241170610301071400401400040780243e00c03540f0306200c0420269143d0003aa000e58030700c8039005884a0b4031b44012140100c0300c81000d8007000420740c6005c0701002030b85003204c4e04564014032102003a40d0b0000e100d0409021580d081c8101402c0001c100028811 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 292324937 1250 292323687 292323697
    0x6070f0e0d0c0b04030c05040c050a020c01030e0f010c030510120302060a0c05040302061801030b040513031112040f082803030b030a021e0a0e07080402060c0f01052d0403090b 77
    0x145911141151109681c03e40c56025400540d1140e0741010b040241c4d25150042070303ca40e83c0c52078070038200284900040d41d607000c1820203605040c1c903030ba80300c440c400042014403840161407000344540f41a12b04060b00501c0e0942c0c444201b03034003607200030800b035040d0040400103550507402010180d650000190082001c0c4451004101c4200000805a6101c1002c1e0810683c030000c5014961703403400014044601c4006040d01031410941001400080240d900c8090b03038050400100310f82103209018242040c640243d03d181c4004980480c07101d001c3ca00030000d031180305045841814031100d00f11072440f903c050184081011004981c0042d1017030b000100760550240c11204042c26541c001510160300c000702160030040340c1d2002d420751400c203944100418094010300031030b080100d002881404014806030180d0000240400090010044842e8480c9002d008010074205100030011070200180070401d20942c5642c05104034403000c00890059605490f820300343e03854003850840380d03002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 292326187 1250 292324937 292324943
    0x81302181305100509101401050f0609030f010618090b060409020f03010f050a2003010b090d0f0503070c06181806030f060203181b1e031c0206070f0e0d 67
    0x640c1d440c40000660030045041e110003102d40105051801303c408130301d8810148007110300c41d800c003004141c1304460200c5040c10740c0d02c10380708510b403001c804022592038481c0c040f810382c1510860070300840100044d4440d4058a4070701c010315020701500c0f6540c006440800f040500010340c00d20200b605071600d40e0105102610103030920a4a0711a200046d003152450703880c41c0304032500c840420001038120f210303509402200303c003200000c419080d80180e03940414014401c4910000411003c035a40703401d60014019801883e106000c0c00518102e6200d42052000304c611000c1883d020030700d940110346480990b000c1c0200c065465140c07460030036004036601e0800b18000e584400c08408103a00009881e080c9024000140c1d8030300f480d011512180001e032200c00d982c2c0e040b65040e0320750000e1100c1c02a40410741101c8004094402d441034906c501702c20854240d26100d00b8003841c14081c8022144400c1c01307050780039146542d4030500e068071f80d40007082088000035051090040c00d4a4502820222540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 292327437 1250 292326187 292326211
    0xa020d0810080a0b07020f030403170a110f030d1401050d123605061e0304081306020d030b030f0705151603020304090b0409110409060b04051608130218 67
    0x150710b0000c01d0412140301d8081e520070014000b048240343d0100038808400292900440c509444c60719690010000e61035130300e1555400280d80074485101e108202d1b00307411a001514040f481800c4025a20b0788000011400542400c406984441900448904a99003d0b0006003590041e54401c0c508107440c40204080c0004018a041040481400d40c00002e001c3d046ca141400340c1006d10541d4460b00d0743c04039100e83d0003008174010b031054041e00f039401e103840340c5186501c80e240d6150101580c021f15800b41c010141e400c03070000d58a540010b2084188180341c8080000d00004030a00d504c40c02e000903010700d95030066204024505018000300d0380c1c462801d204c00d00f4401801489041c08216100550043c1c1c00480e06100c000802d109568801608442c1001052a10f5071181c04008090b015544100e54415507102484041c0d0004112018020010040f0b454040c8102e0317280d2101c01e1315000054004000252106106241d01d1711141d002407049c50817145175400c3c0c500c15180102084000c1c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 292328687 1250 292327437 292327439
    0x90507021006120b090102030717090c06032e03022809113006010c08120a05100b030c0f03040f0f030314060102210901051b0601030b09030a020d0810 66
    0xd2200e1007618050300e070b5161108102001401c01864950005e0b0240f0403603403042052025281d000499204c8074406000105501d5540c840f10504010340041030f1034100200208120800318070346041a8100c00e07082041410b610013540c1154003207d40d020094210b01c1040c040d007198103841c002c0c107000c1030041c1d041c8100d0503201d48400c070030303681c4219500c002401c000c03418603025210038415412410320049100800c0020000b10307803010703001034619410705c0074078414101030220080440b0001d001c1c95104810500b04000e00c10028401100c2400440c1e45104001c14000c00315000c036801a405400002d0801010907182d81082d03001520444041c440d003032080000401c0020101c0006000b40c40014107052a040101d070a5400140704504541043d101c40100c05aa60105000320340181d110300e44500d2082c0040e655442103c0c140b140a0030003010112480a00081a03816244101c60007580c170f440700d044031540c0c1d0095895407809078101c10351403800760303200d80c4c05683c0c071240c0354404500007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 292329937 1250 292328687 292328713
    0x4032118060b150c0709051303020606010e01141b1b0d06050a0204051201020903010b0a03030f110309030a21050304021f0c0b0c0304051c02070905100b0f0a020d0e0a09050702 77
    0x299201d80458144d0b5001084200040451403064550000e80365158038016016a41e0080d2980b0340103000d00d0511031310100c07000390b59203d400d0600f2010849000150380e10005810b051800b0300307080c0000c1a03031040c075050346115003400f04000c00b1110060640c40b030040306030755602c000c1c0400400814015501b8000020b2135035440303c0104448080390001a03030b54441200741803e440070449041d000742c0001100f013001a6002c0900f10010b00320b86080007002e10030710403ca007035100c1c0390001503141c810a4280380510200c0c1c00704441015081602003442200560305035120300084501035400000703c144010000c001d111200c203a43e41034900103550701404d945071210504290b450442d4a44040200002c1140404c84130003100340b8400700c0540c40c019840000e40d50003480c021801d1054642002c520b030307920030480f800d018181d5940b585454800c000b022205a4200f03404030401880f41c039014040d45401002c1c42c03a00c424015000348400c1c0d0a168040780504000b03003295045214001445041c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 292331187 1250 292329937 292329979
    0x71a0705031210150e04051005030d050d05011509062d09080609280203011d010509071e0b0f1606050709062a05070305010504032118060b 61
    0x81030814103080e00d6820601c58a84040300150003074a070018169000945054001403005c400c100202c6000c2032503580c0ba84024403000c0507500c4541c01d485400095014160401e0207840e1400050b0742c1005141c0e0b8034403002c0c498203180700c424408101c140105000640c0f180003165030400e201c55002420304015001f4044552069882000140c45074106100341c007400d200c5035800c000c5013002041086043c0c592642641c0c41300b0707030704000702002245500c00c5440a42007a5590b4200304c0c0010000041c91401c0381c080d180c101d4004c13a031400741e100045554020000c501030b581086282a15125087c82c90a1000e07a00540c5c90304086c100070b010300040590007000c00521070381324140109841c249614060302701180d81c5c0060082c4502e0042513450307078810300e60140c0d64800d003150b1010103140e68180113003080340302e0704040e01c01d5080c0010001450340195030066100d882100d003240100e0b00482d08411289000c0007900e20740e40381c6030182c0125102e600486669040201205442189194411a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 292332437 1250 292331187 292331197
    0xc0305060a0903030b0102010905070501120609110714070608060607080904090c0302090106090e04120e060325050a051903020f13080c040b100c060902090703240602071a070503 78
    0x341d41c03a241c054039001c169150103100269202030000b44180041a030780c0d1920340c130301070184a04000719041d200451146a4002c43c0c01090b05000402010441c0a50402e070303a8481c1c0780c2652840e48103c0d4500c035409000030780e00300704c40c0d6641d903a55441d251601003100c3c2c0c2d80b003d10141c50f2000140030091031550baa106c3c0f0417180d4810180e0510061851052003540359050740070509110080004001c80c11643c91410342c4640d002000380d100074aa400180c0d0703c4480400c0d42d03600600080100611915104440b60007a584602220051404120225680d102d0050320000044050048980c46401d015013201c0035405420094240012182080c80e1038202441c45035201440307035000c1000060074810076200b68801c0e6130500c400c06141c004505422440d00d403200402808801c0042030003101e9000300100c9900034850000c81c100a10700602138280c4120048202a1080f84102d0315040160000101d41301600500511031400d4612030b8114209007118001c104100040000500181700400d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 292333687 1250 292332437 292332451
    0x501060503061f02102004030b0a0629031e0c120a05070c0f0602070f111c02030d1103040f0602010c0f09080c0904021f2106030215070c030506 63
    0x3035100c1c54007104000b4504030304003903102d03502d80c4036188400c01580400c51141d00c25002002258146196080c0300103901440b07003409460707002040c04402c200d10003401d00d005400051050010980f540440f141080c2242009050341100420016216140001460307006130883e41d0b103141c100a03034401408030b41c0c0c1142c0100020310009407500580300d102c400e140d00005200810804c070300d800b8001601402c0d0940c0c01404440383c141e90340b0704006440d0102e5404c2c1d6404002500b8000c10740c648841c0d0b4035000d04105100f19004da00014002d4400c07103001e0042070300100100007165500308203594440316034078003c15500040101003006040206c3c410010305031940005034060103807000404401c0c980820108000404204010f00400050441c4c0c00150403201d55283d40c665100041444410b00d2040c0d4105800a415000e9203810803194010302e80303011580d491038017804171681304031811408002e510002c0510340d00c405000e01d00c0502400c5118070800907041d47c072030712111325120089501d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 292334937 1250 292333687 292333697
    0xf03010c020f011d030409051008030a12050c130b2d0a090e04150b0a09141f030b0c0a020a0b09060702070b040b0a030b0415060203130e100e0402060409050106 70
    0x106500007004d10802003049588168075480b54001411281c603031080744509a07546403240045540d000d41802108028541d4404503a0b0711043c0c0007014003640006408101d90301e20300f02c00180250701030380888140b40d11380703655a04e9007801c11640403102d8015a00742c130240d000054059906040703210044000b24041c40d4415261249a00d004080c846660040c2d04452902c8080c40005042101c01003030740286004d002c00e510307040c0701c0400c1041c94640d00c801c00250801c5440340349540c003162020b0040704100c04801a03003c0001c080c903c40d002c2880010a03102c00c0b130001030380d611040000346c111070980388141c418212031911102d0350b041c001c0e44c20012940102d4107000440d0780400c22140204101254641420700d844c0301c030302050065110500c14980c6500110705107a455500c1061040b4400c14043c3c000c0b070702c0c1d05001350350390024010084010000d05000c64000207089296101d072001b0b030610404e06040200700488140054000ca0700300200b0300003c190980302c4d00505028000175925 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 292336187 1250 292334937 292334953
    0x303060506040b03060306060f01140a1e050a030b09070203042123060a0c05070b060315090714030106030f020d03090905072a20030a050f01060812040b0313020f03010c02 75
    0x405003801f20280001c0d01c5202c1e41850b6103980e0340c1255080c4240541c602e0000d84601c050a0290f136080072100c1100f04401c6c039010003000c4603070070030090302d2200b116580401941d03501c20107000c0990b0003540c601025030310500c000c000003465414244045070325102801c402e1115503444810421200d204a400300103124105000300d80b040102c039a2101d60010180010150010301601c03d10800d480900443c40003000110b05403801c22001c000c80e0b0007850000741500c0c2803403100351070b80c0f43e500070510640b201c04101d04040c0360502904040e42c1d003210038501c42107101e40c01c200d000e4080c0341c422002e02248180000d0703845a548107292242d110ba85601c4001030200500c3c4218500b0f204407229000510032002c00412100b0003505c400c020541c2c1484101e000e4000000d14008407900d0040c2184160750703c0303024425040d0455801c03241048101c0f80b41c1036410410510900980c02945a13982c828030004102c0307100064620081400a49542c1d803280501021a01b59412a00e82234050780c04881 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 292337437 1250 292336187 292336189
    0x80a0915060311010216030c230d03030e010c020601050a090e1603080a09210308061507060603050f0f1903170901090c09021606020a020c1002060105010f09080a020d0303060506040b0306 82
    0x2095030382c45610064070031747c00c41d66042d0303111000703004002c506c4042c4071031070f4950201c492040010700b0000b481c5071000382c550314004020b0300000144107140d500785070280611500004002d8181c400081c44c110005040c11010f40041004070150310080c80390006400b0112564400c4c2c5021b140145441a61900d5030b81001d01b03580d1180d0b00180c0016425a0104c0b0000110f140e0415031650603c0d0111490b00c0e60000986035820f4036445000000b00002e4840800002d580548101c138810b1080d600ba1000389941ca84e00c400c100558005207402220416516030a120004d0280c2440f90500200404d500c1505220100045481c600283e54600340c10040c08441000303031000f00b0b84070703805502d41b485558601000303009a01c0c000304002d4011846000460080c001d006030040040c00c1581c11505a10000395541c0d028810709000c9030043c9644c4111038402c0a058041d903017548010001c0410301d0b801e101440b48500c00940405030b5607280420a43d0361500180003c00410b01001d889041c024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 292338687 1250 292337437 292337443
    0xc070506220f060b1201060504061e1205070b04170c0301020901050708030411060307120b030604020d110111070f060207050609010c0b0406140f040605090c01080a09150603110102 79
    0x500140d40800c05000800030403034060070312150040e44014820100e5100b0701c2e04001803d0400843d83e41700c401c0000b000c9000105520010444004441c18001d00b42d5400386007446e07021381e8900761803d40e0036180902990b0411110650030a00c104101ca041c42c0c0c0e1004211b03280d0b00f0a400883d007074150001e4040d40b614040141d4060355104030001c61074140031070006061881105001010141c1c0403000030144910240a0b044e4048060140b6a89107844100108010316507011001d20624043d90603c0f00e00780020114030884e400f600c0d00c54040c0640e191002c01d9440d500440d410422100c0d0286110941071280500504490182400d5a400c1c42400b074145100ca800071402080b0500c05003a01e60b07405121141c00da5005480e41c8510b40b520309040c0c000e410801101c00041100b5003d12605040c0080c0d6a4415030082c1d0003006a500c0d035220b82074480010b03000c158005104003000c66908203041c2c0c070a0004038492807141c0c0741c80603542041c0c0103035010350b8000e032032400c10460000542e58040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 292339937 1250 292338687 292338691
    0xf110d080912060c25060905060412030b1813050a0b061c151808030412081806191d07030201030c0206010803041401120f05100b07020306060f04140c070506 69
    0x74000d0710303041c682044c00c0e458600424031212032020b81c0304100110956940b10664036180c10540501043c0350904009603901c0e804d0b41c044454001020281414500c240b00320a201c120044c0801a14507024811010400018201742c000128400c0c03500b002075020081518158420101c03c00c0c1c1d86054000c2042620408080107200d1400c072440f400007400307030b54000d1254202a8400148032001c03c640e40740c00181440c00400c0142d0000a11040c00303400910114005469581c1101981e40c0459900b8103190854402949a02c18004680b0084031460001420310f0034540001d0842c5040b4019140c0801000c1c00c01d074150040041030007503580c140681056130b2118001841c0551404905903601d1040d4490a00c0c921050801074402c0c0e03200d9555201490701d6050305000c6200780030b007600d00510068400382d82c008800340d400038010423818240c0d1410b60300140a00101c3d0f41e84418001d01030031625406511540d121409281002c0c50340e034543c015059481c9031a154071051525518107130740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 292341187 1250 292339937 292339969
    0x60d14060307210f050c0d081e0a080a05041115070501050702010504030c0321050108010f0b0102071811120124030516110c0301020d0902030105060a05010c0f110d0809 74
    0x1031031080c0e688000d61980b07074441c074035130000a07079001140c54100281040104e10006a2060922015105000b15100036004510242e80000380242051a107071034184142c1c00e80744082200500000c0c500a415440340d0f40c400d000f086100200b920000004211544a0030035070140240403c401051040034491107038400131340d0008201c1c40c101038034003400041c1100e1004040096141c6201926100c20074060344c00916614280700360750f161140b09001e0023030644106069490440c0b646615840040c40904907610411030312540050a01c0340406081c2c0304040e420011002c112007400101410211402820f400001c00c8a01e01601c81440d4441d82c4503443c8020075052205000000e44a02d00240315440c0c9400d02c0c07100307040040e8609081074851b0004c1603140d440802d20b1400c059203900000840ea200b10002c220b2a5104010800320b0f003000e0142a0018825503503242c00501c810356a03024441c007a10b80c8030500300d401000100c952101e6203007108d00120229911809050040f0300081c2c40403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 292342437 1250 292341187 292341209
    0x1e031b09032e0b1903150b061303110108010b030a090f050604050d1d0a17011401060f11030f030604020a050d06060507140c0f10110709050403020d051306080402060d14060307 77
    0x50203540d401303640450201411003000c0992039690b01c3c1c070743d5009013070440b80544446d0310f480c503148000107030a14a03c410340f100c00e80102c03048180d620610b80141030320440300300c0508644556402100030281110308072aa8220b000c426404a1400c000b51072180d4440ca004048c02c0e4a03a2100820410b00502d501148621031107034600c4540d00c48410740c06072400de0300140e0280c514442114050049080c10380b00003c0d03084000b20b1019401207403d00310b0040d44d02c84180a812400f030403035a03481041113544c209001400415800d02c0c02e030300282540c0059180607410045529061022180030340c0c08036000c40e01c000b1300c4004020b03508ca40c41c0000300040019004141a0781c02051b8801c1400d00918820b4001004954280780a0000311050403034950032070314001d4541d15070a00501d0305540540151160603044007946203c0c00c11200501000050302248a280040990f44c141014004076803061080c00100b024459a03c5082400c13008950200c5840c144034042c141411966002103080c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 292343687 1250 292342437 292342459
    0x60f10080109420b1507050f0d0c11060c0f030d0e0106060c030e0906151210050406050105040e15120d030c032d020403171e031b09032e0b 61
    0x10403183d0a021603251542c4086038418180d000105c20400c2401810151100411150184000081c10f4074118100500f02c0710021200075050320f138209510402421410390b5804051a424040050b000c030100b140116060040030b41c040c20b0645d048240355240f01d030340e10301451441d0a0309010703200042005080890240c061510024a441000703680c8038042c461403004603132141c681c0d003500c459000c0b2120440743c43d090301c900c0b004030342c1c0030540c2d0b81c0f048000e18210100e81440d1510074030b811140140c642502d001e00c0c0074000e00542d28010b05203181000e070914545020f4440b1000340c0100c054200281c2208020890301404540482d0301300010507183c0b1058102c002c222410031080c1900105c000086035a110070001c000c0e03c22508010800c10000c02c42070706150303000000c0e044c18051901c1e208540c0810400740001d80c0811641010030f403009100342a10107034a031005050031360002d400d8030350f00d070160740c414403800342c4801c0403d440040f044014180d0182e248031301844c80008540140c681 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 292344937 1250 292343687 292343783
    0x816050a090b070f02040204260c091303030e011e0507081611031e1207050f0304031115010b03100501090311010305100f0b04030b06010f02060f10080109 68
    0x30701e01034010814000600f043c00e101040042910042e40180250340d666142e1a0b20504001035041b0010700307031070125800314285008110005100c00140100fa03007a83e800500442910301440192300b4903580e10481c0303109080a0080401f00003110f08400300031455134100d81e007118001060310701046058030502023103180400740350107650304520700f910100d005c6019403400e5110b80c00c900c2d04040407040c2805007401220028282039403680b0030000b9a0b54a104060b2000c1c8240380f208080031508000140000303001d01c2c0007e000c60b54910403600c0c01031a0310780001182c0070070380200b000751001104010b400740240c0d000a019160a103001204d49103035548100c40e484e10514210305154a62000850a500f000780340d00040140540810000d580c805501001e9401408155012413500000031465402600150781e00c402030780c010074842e81c0b0b8402640320001c020340007160f405050343c80000c118509004c0d40c0708883c080d9203a00c6d41454180c2c04401903042a0300751410200f40c01e80e0804031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 292346187 1250 292344937 292344947
    0x10f17070f050d0e0f0f060c07031404090e0105040b070e090c0a0e030a060e10050c030a1d030c100c0c02100e0a05130b0310050112080c030f0a0816050a 67
    0xd409401c2078a03104120010503605030050b10800403011349400c070b590b03580d180001100e8940d18500c1e02518900983c00030455229070049800f20b4411804100210009110300800f00010b403c1d038502c1420252982811802e0f035030740d4810508182e46600920060103040d034802038100d1180d042c509555180c2e60003142070b24200030f2403c04241c40c0400c900f64844d00640059225860050507103800c500c040c60030600a0941083d06002c0384507a0305e442c0040350706441040d004040f54401e081c259500c44c00c186014000c41944a2001c424060040d1035101c01003000d84800c00080c0301a21880f0381c40e071000d07000c0750b801401c0d031000c200c1e640003448090707215103070011803c10180c54080880c2100c0d001003030903141207501054100c0082c10b1a103100c08a550301c442d500e444200e0a0307500052521880074160741007805042c03d8100d080c400312000410800c0180a0390408100762424055840c10010068101804d540b01180c8420100a483e00402221020030051410460308103c01d01d070008203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 292347437 1250 292346187 292346191
    0x302010305040609050a1412090603060f030c0402181306051008070c02130507020607090317070312150f080f0c0427050c10050408060703050c040306060f05010f17 72
    0x818503980d000441c0034401e0903004000c0041d001421280a03540c0703460030320361f032684400940c8100e0183e030200c484000f07041400c90b480740500509141c21600e0760b00410006c0080d0284066051190f024280c0041c1c0b0340d0700150940c1d855145508591615013014095000281c50030480040e145c01c600f07101c0c0390342d0600540c80e1910f292500340220707582c044e801c2c2d80c085405e01000c2e41c00f003044030f15404034190704d42000e44582c0c095402d82d881ca44441006984000304c0b400018065951405d414602d448000040c04000d4003074640001d40340c039442801e804a40e180002c840100000354424002d03000c020040b00020001704000f0320320003001505550700e40075400b0000348240e4403581b030500e2549014407004c2048150904405a84910749450f42e036524507030000c14000d400c5100c040300124020010b5804545056014103270036902c043d02200200001056011085c0045c00040701052030b900c212005011030f1130750f51901508000001d03040c07543d02142c2008018074400c00c2040704001c04000c1da = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 292348687 1250 292347437 292347439
    0xd0b0409050717030f04080d0306080c030c102304092306060702010c02060a03050702010516050d020f2119050112020112020d0216120504081c0c0c090b010e03010b0a0302 75
    0x100d82154a100c01c11304502c514000210006004680800c1051010a060240000d691420001b955448000316110a681e4100741c1c1d041d04000508211410498070f9107003140344509d04030100000b25000c2c108800303903070303801500322318008030701400b244050341700b2550881580340220b110490300c0c004105400100801b802e0090801003098011640250251320206500428040d00d40f1031080c80140285821580e441c0158241408210038058080d0021100c0e0842d549144c60510412a0301021394041030b5840380d0741c501001000312a0882d411020004451070345110054102541102c0151040c03030040d00d081850100104080d01c6102c4114200030360a0030210007031803015000030001d00030f003100740c0d003213600004410b040c2c0080b00740f0480010744038040c035400c00b02000408a407940203900607484140c0c00208084400d11500302300192034044c518100001d9081551080c3c90001107601c02d05484e80c0b40c016540030b642e00020512200c0c407040e40200a0a0412000642d0b241040d20020f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 292349937 1250 292348687 292348709
    0x2007060c12020d050412030c05070f0f020a120303050a05060a05040504061d070f09110a11030405030a06140601031b0309080c1b091e010501121509020d0b04090507 72
    0x3020341900486140000c480780441c00c5480344018000311025141c101c5003200c01c024a1025283d615029120745540c112542c0e4445040504507514280000441a003d6840058521040e00188e4800340310901800c40807940c0e840600451a014054800c054584013a0074200400c2152688800300a802107800480e40440e980c3c0b994101140144103106c08e02c1c4002090b00001c81481c140040c8800c229005c1981c420103075a6550b190408841d43d0740001100c90f00100010b2a080384510420044035002d00305492030240e82c4d4002924144a0309002c95034252102c80318000c0c1030360700649607400402801c0900c1019070101542d80309500e602c40810038155100c20b00014020140c0541d0302c0b80c001102200c1c80b108940700e0a00700b20001503200e41c17003200c800000540c03a50858461042c031903099006003125908140040d80d6645101d440f00c580c0e180d0f54202d030b003046032503a02c4d200000c100080340140d40c0da540d03810b2441918076aa1100c1e024030f040c0465030000440002ea010f00703c0d00c0201070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 292351187 1250 292349937 292349951
    0x80d1517030921011d0c0405150922050601030209060f090a050a150314071e15031119021c0e10090b03010f051f050d051f0315200706 59
    0x4074050800d00703c0100000c961903c80380000805008003000900241790049600101126040009031039044403803641c500783c00c0390b03801c1c0725041c10800f2640141c0c0c442c03212a000c00840611a640140d4900107075042d03800000108150304004e0155600708000340c0d00c1000800e0729001040d091003018068800c400c1d552000071781e2030795640d400f03080540c1210000c0c070111581d81c10072600c6810041c070392001030f004030140012801500a59101d215034206040c0420503d0100c40c11590303003000302d01009054499080c0201c000200000700ba0701051b48044845001044a0007458031240a804850040300b072400240819004102c3c0907180408030358031a410010b0130f804a44802c055401022040000300020801c8604201d804090360b070203541481130310500f07207503410030a2200703030700103000c5003081200742207140c1d240d0030069001c26071004186444496900c001c182101035031080d10380c003604089488020300c07140180c110385104400084241900c0980c0d12a252040440c014801595114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 292352437 1250 292351187 292351219
    0x40b07031b0c0b0c0403150507020111030112030f020606010c060b0315070203032d011203030605060a11010b030105040c06110f0d0e100c0b13020607080d15170309 72
    0x81084494064410044011a14405041444100000c840d0302c0e41c60f400040400b1101d4040d5411250801100204851140c940d90000d00001e0f007100f08554803501048401c40b10140118020401e04414003928490350a00804c91581d14580800319000701d000d0010f04d030391008000801a400c5400015681155000249001904002d04c464140104100031809070080003542c402c00708030130040070301c1d0711001401c031280d4401d00c40280000001d20051240070071902d06140c11620a090010352243c54100162151f006580c40c1c070001805c1e28507016403402e080c002c0341d42c01c1c40160024485801e0594039600c2c900d44078002c400400c10248004900705008110801c0c411242c6810b81d4a10b00b2200700080503010045412030007001c8003462001241d1060710480e1505400c5880c00798662030754030540c00700c9a490039003641e12550038054400882c8041d0b00510362060302903000560f41c210354580080e1154a0f901c542c0b41d980e2000104003914a0101c1180d04a07503086411841c3c0e048445 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 292353687 1250 292352437 292352441
    0x301091a15030f0f01030206070b0601030b030a08090a32030312011508012301080c0408010f0605011106090303060105160b1f17071a1908220b040b0703 67
    0x45045580000000d0030041044203010042d0f0140811100040581d40c400c9003014200100380300c002d402502c1001180c000c100121801d94110f001494081408090440040d10300040d071841a00c0c921000644c0307407560729150951100920140c01070510000c008501c0c1c080200d910203249070301d04034035140e01641d5a0107008580c001c035200405403001c1c0d61694080501400c0204032900441c600700004501c544030000c200080d0720702c400244009400c0d1800464642c2800782210303425110501022411320b2013806040901000c040c0000b4141b0b140c14001440e02e00c4268800040b500501e0500c100c2940103c00c59600000c207003072160342c0300000b95884182d590380e5034011b0b20710352605007405041da481c901d5503030002c44e51102003c0a80c3d1100303080c0009804055079051183e100c80000c1205002c3d81d00d1080c450600032080034202050300d010015803100701000400001c40075400c000c200ca07500161100c06c0d04004210120303e5030305e5602d0900201d0082c1014210540140010310810721903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 292354937 1250 292353687 292353731
    0x1020709050405191101080a0e30070503120a090b0a091509030210050a02180d02061e04080f0a0206041e03060608010b0109050405061507030905040203180d080606030109 75
    0x103500c41344030504582000000b0184022815000840490100310500d26500900350b40c01031348800b078010b014070b41208402c0c5e4194044003411107043d1800c142515941e400c060301102e40948007640d030b2440c2440000500e80f00042c002d002c2c0516080c901004110180304a6910114030503000640854074100300d49402e04904841040702d046c05078007820198040707600e02c600c02e004241403190340c650740c40040c140d00900c011000710350f043d02c0c0c6071041c1d40307007000d5000a200c1c0003810b882e00d0100c03980e00d000c160b2805d4035503100e00d407040010308111404003000400440c2d45c002005d0031b4440c100d80d0004540780f05502c01c0507001418030a42030f001915000c0c1030b41c000d591000080000c141da410740180a02640200103000c220b040340c002806050900840340b203050014078203e07100702d1743e17004d81c007245e00702c00c00079000c1044806000c00c480d01d80e803000358002d80041c0c44104a000e040b0320a18640034110718003604000080081c0703c80c40d00c6080a80341034070300e10032005c100282800e4001140c80f80c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 292356187 1250 292354937 292354963
    0x3091e0304080712061a03030f09060f120603070801020c19020102100e010b15040311012016091b140c120d0203010e0106020307080d090c0302100809010c0e01020709050405 76
    0x4151002401240220228844c14802d41061214030358602d82c50000b200a10311a07501904200452041c461000740282224440240301034107010504803144403a811510314540708110180030b005080c03070200700c030000514200009614001070780d05903540750144240c1101003840f00c040d88004688c0240800c0044c801049020000064070300c111078080c08100c00c41c1802480301042007030450004008850550b81c01601c03110480a180c001100c0c05011003d1075000c110500321001c140d13010600144103030900d051048049941407022402c201c0d0720380a0f0151130b4000d1104d01001d082d82211000000d0341030300c210345032250450700f40d00b420108070b4950811072240001d1010b403c5000741d8095811394568004039070007682c07034140030b1303070341340720301e4002a100c1d0b0300a20100c00d00800c140c202c103000702d2003900b540c9889540c90f07000c01d4182c0b16081814010464940c10030404c542c00340318800da4181186014441c110308000042e444150a006008442d40c4440c005018000104049000c40c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 292357437 1250 292356187 292356193
    0x10c110a05031204170c010b040b060c0705060d020c0a26030411090c0d0e0303150a05061b0a0c06050c16060c0b0a1103130b09070e0115090b03090106030b0c03091e030408 75
    0x821b403075006000307040300402d00780312702d15020906006040c14030940300003580100c02400e03550b007014100301094110240fa0441c6030f40800c00d803550940c2c144103000030306100b80300c0164822000107480458815090221302c000310148200000720b0f41000100031103004c283c80e10f403200e4562321004d4016218154031101442d040c80244643d821000004600c19051901a07800b0201107104102c0c0041c43c500c5036940c000c100303222501e00100d05030381200d60112540304442c030550b40c540d2861000d2400b44d00c19804039601040000d00c05c0c5061142d906403484614003001441e0074070704094122001224081d04503191100002e008001e2903000c40400d0100c0c2e8815074580c0f914110a10031803d55000072510242090301040c480e10001400e10b065407504101c6601076030800c0301a42c10700d104a8404c0d010041c10035800140d40000303030019402142450001b042c00e0742103007058a07810340050b00c9185965010400c12444080100d1034410740d1440c002c498045016008641d891802150400c8101d80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 292358687 1250 292357437 292357447
    0xb01060302210702340b0c0109020411090108150901090b01031512020a080f0a060b0f04060608060a12110d0c08070801270f150603060905010c110a0503120417 70
    0x41e80004540007402d4028045e80001e44507030090007401d80749003c030304829641c6100c06100c0c1800c0305000d80308501005000083c150f0300c0f034001505407114000080545000080c244d02a0750b88030058543c860740c04c0d40c10362082715244010074034112051241700195652000f203520144e100303030092f00560140506850845482d0110400c149211847c00c030321070389089200042014003c0f40c0490b41c0daa070100940200202500d4030340140c40148400c40d8060a1b1000c4200599290310603c40a00ba0307643d241100c2e4079107881480030039105900112140d503454201c0c28002140005050495881950703600c020384160324003c4071003001070700203014900a400010074120f40550221004112449803c41941c000038540310700c131229030001a003050803810602c0c0103e101040f01094881007004006942692600c82d42c044072240c0400b10307500d944030801c0324100f6902100c0c0036000e0f820f40c8081d05842d60070741e552554034824251040292203c420004003803200c03114044010002c0d401c0856951 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 292359937 1250 292358687 292358701
    0xa02070c08010b0103050708010f030308131202010e0c01141c0209090f0601021b0102030904090804080a0f060b09010e0f06010309020607080904150501050403081305060c0303011a070b0106030221 86
    0xa043e24080c11800203141c600080d03442440303007072894100ca0082280b101a43e0440e2812240408010501c602c1e40041492840018410351441e20003200d03158000650700d402e1800d140e00b40f982010340241081a5280081c2c4a0714030481101d4504111000354111049200c130840007a000d03403014268040c0e090b40c10070034410300f400401032064200f60b0035184189404a0b41c128201664103030a401a0300a21841c042e0341070075400102214001c0c07940c28100799440e6000361400c0180c9204131814003100c22182d00300480c034018141808011580074002d03605007030981d014075030020031903c03080740442e000c5426a4003d52101e0042078000c0c0103251f4807115401c0920380c660014507485e004a14246030108100502e1070030b901601e0b016910305103040d181d6120311146030808000381e1803240d0300308000a070995500740142181030740700f0081e584170341c541181d5003291062480540c021643c2001610300142c411420981917805034100180c403840304016005801d40b01014004465400000340220 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 292361187 1250 292359937 292359941
    0x609050604031d0301020a080c1305030d0c0c08010509060c160b010f03020f1e27090a0c14150705161701060506120105220203070302030a05070c050a0b0a02070c0801 73
    0xca2800f59540050080c400c400349800c030f119645240000601c0d4a000c121f144948100824002c0344076002ca42c01a03489400003810030300c040c00c0d0400402d030521210300c2013103d0115480c0003403c01000802031894000385260b110f0f04002c10103540590001007082c8402c0103109550361041c1c20444024096031111081444021140401c1c0d10034000a40313048980d10b008100812068030313609110021050b40c10034021030402041800354803229451015552242e0880c4044c0700c4d150240041403c4012810620140c28054102c802025000c1b807003c035646d00c031807a50140c8010320b10455540c07100d00d81019424181410800d0603000002e060028003402c20070070407514101601c0c020401180d984007045150320039032826484c038020040c0100304524221508050340c120280d54080c901101c190320074120380c0111000f4010075800320a22450b014a8030078617500041ca82001032035006161281603586130b542c940207284050301400a4240303d001e40684880315803011091420585461040740 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 292362437 1250 292361187 292361207
    0x2040609051302130303030209220b12160e1b070c060908070e0604020d1424010e130f02090a0303090905070801050d0b0c090603090d0908071401050304060905060403 73
    0x2102e0341d2005088242c0340c00901c200d803141c182198980b0030b032901d10381e005d0b000794011002250340829600d0035070b400c012600f2036294040011110015000312a1005c0142c48010546119826801104a500040c82605074541500c001d81c10b09221641c4644080540110f02e002107001e0300340201d680c00030021208080c03816100c41d5100d82d45180d40b1a81d00d99a03c601601c590f12190b940d01c000b1a4103410254000d140d25010044003041c102c00c142c4400c4544007040d200016050601900d80200d00d903131030200a400002443d169211082100002d40c40c0a680c424a00685a42d0344107244003100c1d0b6411545107443c0602034184160b540e040182049589110320b00b0300d20f0400c2d0015500901c210801416035000070080b00d03508078640c4619003008001058841610400c12078a021070b500d07500590f100d050200b000302038140480100500e1140d480d031106000303a0000300c09001d244c80f030355a0880e000318203107032454803640d6905000c80605204100030303115000704002d1106159100306142 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 292363687 1250 292362437 292362439
    0x50723040e06060a1a0403080703210204061d0103320105030f0703030c050102070b010906031203050c041e15030501060207060504050312220806151c0f080d0204060905 74
    0x40860400d00910b5242d00080781d4080d440140307618240000c4036448560103034004a88800342c146916039a80815550041000b540441c0100c2001003400b08a600c400030f403260414410744c2824074203400546038200d82682000400c146007030201450344264000310102c440c4042c4c084c61000d40004a0a2001c1c9141c0d8580701510000f002261504001408003107200d070038001031800d03e01e1a1402c9070441c0381c08070200d4065400b00710b40700c007180c45003031298041d240e00f80000646078650305e80780c260380345013000c00018076040208004030b000482c019941181d00c000b08180280b925081e0b264000c4425801c07054a106003614888803441c6d046c0d100034180c4550340c089030352003030721050b0903101c2c0c1c0518814954942d010b00300a6a603480004041c1c4910300c0340e0311605910002801e00c40006842c40d07004000542e20810400c80b5056072208040e50982c030558080526071340d034402401103056041c1024000f041e80780e0101003000707010780c2115003c1c8a17440c800c540700d6481e00c40c003c118a149111751 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 292364937 1250 292363687 292363691
    0x31b060306120a0f080c070f05030a0803180303010602010b09061c02040518120a0306050111030a050f16030c02010201060f0b090f010e1207030309061106060f01120c0c1406040f0f05072304 83
    0x815141d23484440c040a07901c0007802003000c51001e42d1001d5065200600c0030a540ba0007941007102440100050360181005400220701500c0c44024041102c0c00109114400d102c0c0c02264501e91202007920441c040e01500d01103115583c80007506948248100104c07042c2c800c1e00c144030361448241c000b42c0104452907400303001e0b136603076140110380705040242c8400c001e4004120346600240100f00030544140aa2102c60424030055805441e07543c400105802088101d00c0d043d086690a1150304060a00d810560342c00c0d03400c2031940384942c02141c0c00f003401143e01c1c40e804c4c085680501046150302e140240b0075140c85007161601915080710f4442107001c03a07440b04010503e203006100d551040001400100443e070794001c1001003100326211400d050002883d60318060403158055800e5241c156101c940b0f810aa515010040c2031100f420581140c0080c02071000184001c2c01808205401c06a541e001e0510384c100641014095800340c0001c20b20746070703204120103c10004c0c44859200f2102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 292366187 1250 292364937 292364939
    0x105010509040b070804020a0b0c0d090e01140f031005011d0601020d0f03200d060608010f0503070308030c0409090b07020d020d0e10181202031b060306120a0f080c07 73
    0x40c0401d810007070303400030f01c001601d00c000b61007540f0030704a0740e5103e0f000810f03200b06680e8a800c83c0300254009101d580306030f0004148686e01d9078008200310010300c401c880c1101d40f585007012125040824552042c1300d05448003100c03059a400f040b48520b0b400c5030000c100704550323513480b47d0010031980c42c081340d104e600c804e400500c4540c00802c00d083c00380d0003038a802440700e0712101e040380140001d42008589511038034046403081040009000410004080081e02c1824414040c204035070592040844074034000301801a51004201203080b603601054450b2207450304030408005008d590000c1072501e18000c0300e03c06022a00c02c3d024020b10f0f4640175117201e1410302804913102e0142c1a008004190b00c43c03e0540e0358208218440b00f007005c1860030566480e44042800e000d010240d0010b202410300381200e1080d440c0074420103d2130905080000c401c200b502c001b00d00c45001c000c2c05148030b14100b9968801e4000d007030110a207816440a05041003100524002129800c4075a42c40340324421500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 292367437 1250 292366187 292366189
    0x1303031103041d060d0b0a020307030e03030105030d110a2a14030a0305091c05010b1008070e060306040908030f04110411160305130b12330f0a0308090301050105 71
    0x4100d9003610718540f004071071802c1140c100e4106030030140103190041e041c9110b00c4d0209444048150140c000c0c220007503960b06186d0342c000c05480e861043c0341307003940041004001990700001c0101c8481c1450a00c52842080313500014100054070001400d55018806030b651900c03031810b035a4044240410340d0002c00740c1ca8444a48030515082a4660168400740e0134002080c020b00203800e044000902c1c40f20106a070b803007903845100805a00f210aa034480c402039006140624100c0f0802016240000c1185000c1c000100b90000b0301610a014640010100d403117030311280c0150700440e8222403415500e08241c0f62490480740111001c0c0d036140c6a14280000c2c40c9000d005e90032074013044c26115403c103100c180085440d07000c007082c100c040c803608100c40840b0081d10041d01004124010415031a03500c2000c680e031158900400c2450512581c50892520742d05500c20340b10f00c060607440c2d208107030102901250b18520801243e540c000380804000080000c0c02d0000c0c86032101c29402440140d0344e40d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 292368687 1250 292367437 292367443
    0x120f061005030d080c091207090c03090203031917010e0702010c020304050a0509060a1703071203050f070f0c081b0f0319081e01230108010303050d0c110313030311 72
    0x2000e102e51541100100c60200f0b8803e24400d50800b078009901d6207040a8100050041328200401149580001c0810400c04246119100c04518903090a001c00c3d1111341c000303030f124410040b0101e1000f0b80381c0c0c260f4400034402c0c0c540f40f50040d50101403000d00d5031a041c0c5000c024004840780c400641c20107008034412072001c01134808941c8098034503082d413403c1c41c0800c840500000c0099410007864071000502c01c504012040192540c00040c503034840003803d16030030003010201007509260408051003007070401c030080241d00c40150f160503035608500c07200464007000c0e03841d03020703202281c04140110352403104c0f100b07040c40050042c110340909001c15440d50b10303801001a035600c0004406400c17030665016920380d075440410f04074102d00e0203101c550003402c81c010070381044040441c0f1100c19a42d80099041450b035901e0242411480340d0315580c0c0c010001d00c42c9186011020341c90f1400008501c0c000d490448203500040e0540c0d8403951324014480c0500700e984000d0300001d80207003400030806404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 292369937 1250 292368687 292368689
    0x40b1b011d060a0b011b080301061b1113090501090303050601020d081005012006090c1c02091f09050c090a0b1e0a051c060f060e03030304150902120f0610 68
    0x200c01416456030340405038801040f9130070b00b590602100ca00801010400e0400300b49201d07100c1c0203003940320350403d907008096084004580758603821003110140455130003589246008000c581c00101b1416050703804028243c0d28000030a0356003040901000c05030960000c61003903600780d00b181c00c0581c504408607503c1d84190b40c0b036400076070a1541030006501c07819030504602c1070f44845101d010303001d406040c5441000c603510907482c1c00c10002e4048a1610100c0c101c40070280c82c43c9805110100d400149081501030700c08001d240f20130400c906440140c80c0024010407042c001001580f610910001d07190380548005e0384103003401c2101003100d004131015500c59011a03009002c084402c015812056441505800148402401016111006c1100400c0c03030102c16003011410f94a480d5a081001d03000780c04c01c100703100c00f03514200d0261300e000082d40d61264103c803400031100b405c0141c68005050041020350002c410150310075004030300041c14483d012400040701d21590310003404074454291 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 292371187 1250 292369937 292369991
    0x1209050714030307032f0303181e0d0c1103030f04090507030203090d180905011401021b03030d0209040b030f0d080f0403091502013206090103021c08040b1b01 70
    0xb103c054114188904808449800041b1036455441130f00b904015103140c01c100c41c52410b410050421161420090020900d82c41400041d450390501186e0215160360b0450000000c00500402c20024402801e01020107107102409981ea22a00c401c44003081b5440360045034403640c01e14000c0b0f10a68464403c0700d00c00c40c0340d14042c02562204290032030f0740403c06c0c0003140c800301c84540c01140d4016103200e11802070031640d40c071141000c1c030b444c00a0300340500706d007a5802ca21001a2111420b0700c0c040200c0d0b5802201c0b180059980f007603003000600405800754110380610410b00e00b00d00640000441c40e00b082c171503840c1d40340141d9039600607103e80041100c0c014009403c0200401c0703039a98901046843c8011400040f45035101010341540c10134035400d80c00b40075030040e41010408100e110030260030031401e0301c00400703545c1540c010541e090808103038003010b1030000b6014030520181506541c040c00b40340394501c1c5d4588070f1100036100c18040c0c5ca4032044a5107001c021208001406085c1a50561 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 292372437 1250 292371187 292371197
    0x204140d08030c1b0d0305010302031e0d030f090c080c01170705070b041109150112062102130f0605040f0903020c040e010b1c060c09060c0210120905071403030703 72
    0xe2080a40c2c00c85421910140c030001c5294001c00705418001c1c0328000e0141172aa4001a8561650040502c5e120356400c1da81d580854058100210b00408501c10b804040c540c100825600c100b408803000070241502c003d8a14001e20700c0101d51414045418803124170300340d07603000c0c40c910341342100f09446400303849810103e0000c100d4503000803010060761341d201c0d008610000380c01207400302050002008030340780e20400c50a2484da0810b50303000b802e400003400c0306941c100101801c02e044420800c502e8940344403540064200c0380115500d80000010394140c500c41800350881c41910103003c2c1045014440c0f2503814041c003600010118800d100d46107801d0f50003858154000700911000701004028a4469526509420120780742c44583d1581c0026050603041413000f1410072104641d0218011001c2110105040000c181c0c001c50501520345c040340e40c0701000013646810303a48101901124803030681001038010a00401045900403141a0000c00034011440e50030507032240b05588004021030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 292373687 1250 292372437 292372441
    0x50a060503011d25050d230a0b04020d050313090903020705040207020f091503011103040c060f050304030f021006032003030a2a080f0a0e0d0b040b1b040602010204140d0803 76
    0x310071044801c00041e0011003010f0030b1605e6401007183c04008081c29901c2e4000e00c0b244040005e0390300b0001d43da24610382c02910702c580341552452200f050103000a803240c0c00d007010190a001081c030850755001c0700a800213620301d0380d440d40200900185130054000d80200742c40015141024000c96207076076030003018033b600c1c141d0030000c1104940c0060040b454212540150410a403005d2040c554061443c1000503100c0c9042d29059150a64a400600421001e070707282d03280c0c19070000283c0c3c2d0030a0b410b0600e00c0c0d5603090044106e1420013100605440203041c80d00000510486004034980c040c48556420414049041455940d10840c481c010004a807140100000c54030b001c0000200220b140031154000c1c0340b6103940505801c85114074038a4000007520284454100001c09030803070040d280c6910050705034554000540d401000545000c03240c0c000503403503018601402e003410440d0481c1c140c4554960350024001d4104d8061542d01c45240080550b0750700e030101c4101c61040d4055181c5142d6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 292374937 1250 292373687 292373713
    0x50102120f1305030f1501090c050f0f07170c060f0f01050d0507050303070303020910020106080c040207021c1b08010501050a0603091a090607080c070f030e13050a060503011d 77
    0x155001c2c030842c0901c503603035070b41c00304440d6800d10210040600c804014552003c85101e0b185403041c1c1a40032811961030403105000043d0010103036200a40992070242d1901c1c2c216025001c00d100c1c0f990f00810001481e00e0000072948100b02502c4401d206d4001c0324595a0f0300c40844071060426190b9400f01040200100420310302032007840c1c0000e00c42c0c8140c031003080d5a8008a03103107421098007240402d4000c104460a0b05110034000350820b4144000c3c041d1500d848215902d414680254a001da500040c1c0c03402503440f41d1003045a90321307030034108a101c01c07035a041c050240b00d071841040b003c0c2642d5010002c3d0541d014007845040c0d410040c0080c10031450828103600800254008580b00c203080c00404c2c2e201501070700f00c10302c2a50700b01d0103403210780b0744904002d091200c01841550309100034070000e40455181e8001845503541410310186400c203a42c0050310300b000e000002c107181c6081204010762075005170422400c81c0c2090300244440c40104610440402e03101c5550045648000300320646 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 292376187 1250 292374937 292374967
    0xc0806010c02180c070b2707030305070605130803040b100906060e0904050c1302040504060b2701020118030e040e0a0314090f0d06051b182e0f0905010212 68
    0x1190a6940007490507030b09a403080035016041f603200d90b6440c0d0601401c4d02c0455840358440701000b6910180260303a08542c3c0107006400b4070748000d403640b6039400008446c545080300c024060350b000900760341c403407501d440c01490119044030350446008410380c000802100c14040e101c252010742d103a81102c680260f091100180000303009407003c1c400d2014001c203030b40310303d105c6c5820f1100300100075948034104001d01041e5580307503001e907008100c02c110042d00ca11b91b4040034818000c40100f00c038501e0551000407809840b104042141c0d203071761303201d51004164000140c54001c281c00d46080c84906640140710b03484910140c00034010811140102410303000320310003804c0311400213080e01c2d02c4500e2000070500c0c1804040e82200d03420b50310b4062007060381c0905540380000c03000130b82040c0341450110240000305254500f4074012040d00001c41e02c0000420241104c80d00d03449485a4040811302d0001c1044000c80c54900100d0b00300d580c041455480883e90140880d0320555561070030f02c0b11020710034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 292377437 1250 292376187 292376191
    0x90903270314030d06031b08070b040506070323070b010e0f0403080403020111210f0c0d02071502280804030206240301062702090307210b07030c0806010c0218 70
    0x81c002040700c0d03501c043d04c81c4115000307140101240410ba040b80c442084003411190070010850b402104100003248170b0300300300c5042d00c10aa8005841e40034030319043d41d802a4540c2c60403103440403860301d001c4948151002d00b901d5400792a001c4050390740c035240945600402e80d11400aa0a90400900032a00400c925a045032003803000140405855499141c25003101303008010320420180c2c0091940d07e01800290442d8641b003210000c5d040010b0ba0541910448134107a00d0395801048000600042e017003010482040881d0a556818010040050301440903400ca1080400c002c940101c02d44908481da10966060b0020001900d846191003425041002a00180e03e8036800c460040e840c2806140024421007c00b031200350f180c0c140c2003200c1103070000b4040b8102e10600c14019a90380002d40c80d02107880c49041006840303002000f11001c3c465001014181d07010100600c0116545680300c8a6408038075541c690a41d12201e0044914410b2101c0103544210107548c5070540421000c0160303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 292378687 1250 292377437 292377473
    0x171902070c080a0302030a0305061c0b150d081905040e06040207060f0219020c18010927030801050f0616140c1306030b160f080a0b0a0909032703 64
    0x2a100e1542d841d445803500700c25a100f03c1c0140c1001c00d0301c9140d16018003c83d074024130300701c80d41000a003d416010b104000b84103c00340c01c04000d00301256030007881c3e50030100341640140c5562060407032400c02140c1a4010080c8200d00c1c21042040e9080320710400950f4182c03080388c805241c50380c0f540c504100182d0400401602c40071383d508200220413640744010026058001d4480c6003000030400042c0c1407030100704095016614000b003121000d16040c019506540321400c0c0020340c0090504020a52030050050300c5074054082c00c281300380754205c0781c0a4120381048440d17020786d104007400d000041c014042c80052a00340b071011100080d5004030006400011403044401d5a00380c08c0c00501140d90100d07404c0e02c0c0640d121418000d02048420b01c540c88801050f04100001402d20000c203403c0b1002c16040820082070003150b0502d1264202e501c0d28003004040003600c1c1d440d04940002050080d204401003100032804145090945000031100d00c10b0345000a4503c0c6140c0f1100c44003400d040c0381d8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 292379937 1250 292378687 292378703
    0x6021002071505011d060103110901050d150803030115020a02100806040f0f06030501050609070509090709030b070306081c050a0c020111060903030402030d092411061617190207 78
    0x104800082c0c0d1203214000c100c02c03801c0300c2820241c1007a5851010b4060303c81ea04260038a81400300d0000c1c988101ca02c8400c0038603105584651a181c40f4005101500300380701c11072192640010000e03000030246068a214040c2e00000740c0d182d1074260303501c8070f1401d4000d4005c41102d9515400a000e569032903440f1101074004100340e05000c002600301c0743c03908503a0a5181e903515082c810b00100b40b02c2d2035440481034511042509003c1d101420354080d0003d500d1090282d000041d4001e407040414000565001459400b5420400400b5001d0400350158080034802c10140007107940300c080045d40d03c100c0e0fa8a80e6403400401403403c580b20360b0900402e0341800810303032401c010088108482c80c4130784c0451001d90349070b0603d4810981131581c050703403540030460070003010700c0034084040f040011060b400300d5120341040c0c142c2d81a80d040c6001541514035010b0082009038180c12041508a0451181c0d140d042400b40041700c20340807401607030701006000681c090340b903880c0c0341d550003040e11074010920 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 292381187 1250 292379937 292379963
    0x81507110c0a0603290d0b04020d050a03030c080903091008091905030702090f16030c14030403090609050303040e0610030618060603141303030b0604080d020703050d02070602100207 80
    0x315074007500b41d50041000075910f4031079460301307090503940c0d102c40c1e0f03680d020981e880c0d00101c0004101c0103d0000151107180b83d1400b241c115a6440151944940e0140650780080c005060140040c01d0403003c0384085007d05001458070f0314048103c0d07041140080c0310351044200c0e640110381c02e403001003c1e14074620501001c41003d030710000404c04281c0c803500041d0769443d001d10620020000c06080e6403920300c0180284103821503c9050350092584c1450b00240c0c06500b89012594480c8240302c0107441d900000a00040c0344e401200d81c4240c40007a2141c011080d03807902416a24451032040d200c06484010100f401c9241409407805404020b1401151444c1c487c4800c1c11040da100341c402000ca9646d807000c00c02142c2500a0030038950211241c54910f03d0004102111006000e40040802d6038a4030445025640c0700c0544014103058001c90700d600000c580003a60ba205035000c01d4a81e4482e0a000d0002c481c80000e41100350740181e4054038000030007128800194000f030b02c0c1220042e84841c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 292382437 1250 292381187 292381189
    0xc091805060a080703080d0e010b0a0e0a020706050c0702090f0c070b060a0306050f010f05040c0903020f011e0518040b0109051507050d0807030c0e0307061103092107081507110c 78
    0x202c070130059030281010960b43c10165070f05104a4490300311072031b03ca9042c90742d0042c40c0c0e56480354120455801101c045225901c466404001b0701c5003007801444585000d0501100d201a05d024103a091710035a0360400c1c030380301c2050395500a002114401d02004040200c1400246442030090b0004006800a113800381c0340d5a0b440c080e140100c1e803518036222407100400c48100c0394003c100c0204000e90301001003035076048000705010320303500000c0d0048585400b40c000700d0340b00304c241490382e004420321101c0d0803c1e4900018401e50201c0f0784012098151908440641350520603051144016180c400d003040c0b40c6024044c82c14840034450300d52701c0c42031042001040c003d1101c015842e40c0c1f42d886a02c1840d11781c002404541c81217180c5010029803403005940d640700000d003c029110b06041500d82241201070592441c440d03400055000110610005d050404035401c1d02d460354400300945001e245c0303441c41940d990030b022004014010448000c591a240120840507040601206954540d90004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 292383687 1250 292382437 292382443
    0x50904051305060c09060a1d13060510030b060a0813050303010801091a1b030c04120f0204110f030a0f0905010516090f0b0415020a1709040c091805060a08 68
    0x1e402840c07201c4001c541c0010070205000b415800001c5000d5141031641c5e59020602c13074003c2c9411501400003110100400300c0c87c075444070f405100300510302c040c00c00300341c0c6d4001d0160a0510896000f020026034000c86540240a1102c2c1c1000150819042030544030b0100c480c1789010b044201c02400304440380380481c8040c001140030b400c0b14000446c40010f03516248540950070804503030300100b90004d01144491008800401000d81c07586282c9a855180311005036100b25400380300400350903071064041004441140094600840e070408c41216411040501c92060b0201008a03403c2000003c01d0204103078044170100c0e401d02c030001034441050b5038041c211030041c1c0320142998240c84291314050382c0810a003010389042004080007501d0322100d003900b0300550040c0401981c09118200409200f0000404c4040d001194490600e100010741009a40544025806181020242004031340031314500c5049130340d200308003914030764140c0040d0014140600082e0f440200240d0004020f1810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 292384937 1250 292383687 292383691
    0x4230411060c03090906060c060a09140f01061701020f031b0d020d0504120f0219080f0a0507030906080114010e12010501090b01022802060a03061e060809060f150105090405 76
    0x201c4010341e900c1404c0d0040010b4142d00901c068070441c010012a485511301280c0250054452040070660001c603240450201703140034506030302417203600e030781d0842f02005400040484a202a0105031019a603003000d0a0784980074035031043c0325042001c00d10041d0440003000c025036400c11424109180100014103a901a403043c03a222078030391003400103220a808007040c4184d50350904064620720f000307000e51140f0317401a00408664021103010107005820049623590788005071420794550000801902c80d41006005800242c8250400307e0f44e10f010718003003816950031442086581e4081d0004480004014424a0300000d100c07055011940c801d004050103080c485d0300124032018a40002850400c0f010765290310002c1c10009543e1b40c0c1c0707000103025078044cac05441190703884030042410740281c010f55106424048004c140e0720720700300e50102c442d01580c1d40356860402c5903d5040969542710700c140e43c907586c6440c0850100c2c100140d00358030321a0040060505900f00701101000404440c81 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 292386187 1250 292384937 292384957
    0x302030102040b090306060a0302131113060206041b03030e04020a1b12110114270a0b0612030306010f030c020a0b0c18031b04090303060312020d030b0423041106 71
    0x1041d4113010f40780522100b540311806603801c80280d861600014004030500382e442c0c41b0700f0b45d03803c80c001d140650704003214030015a20480c44215035035228020350316101203400703448c128103000185a21030504140801140c2c1c056030394807603000682c802c010096101700b170305c0c000380316400e682220350000300b0b000814042d00a50031a00c0104207507001034400b0f0b0000460030300076454201000400c0442c01c0c8070940214032140e40281102142d00324900d041c01c5400c1488080c8140c03105a07082001d41c6520314480c034420f603a1101322040d80081155a80030a0300c007036002ca600800a1300195200794070180c60611544122043ca2445803140103108809a44051041d9000201500140c0c0c0104400c1255941034004140c0800383d110501e020000301d07400c01c1e109545070a5400c09140c8283c05c128007a54002c0e2901031030040080340a5a201307101c40074440840e0410490b00098a40b07072040e4141c0611100300c068a01b4130804a0315070a40d4001e04c00ca65203201c80d498a060b03a103444000c1c14185038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 292387437 1250 292386187 292386209
    0x51f051507020409200d0b01030602070c120501050703110a1d0307171c050c100e010f051f050a05010f050708040905100f05040b01050f0a020f030a020d031b02120c0106030203010204 80
    0x1182005644482610405446c080c885407100800041c60074004581100c0d0806001a16404140b410060648041d03210300c00e4043c83d038810030240441940154043c62007a141003203840007400709d800a40c019001d03074401149018840040d04848a45000c0e40305600500780e6140c00e845190313150032546240c00030703041d0741d00041817080b1084550292460070a4141410382c100b6181540641d60742c0e501c603e88450264540c420000040c00035048a13000102c2102c040c002c0746006a800203500d6284500c68a802c00d0540b40003440703003018135001c0300741d46040c1e449000c1041c05040030f944030f40c41400103e5100c10100400a075560b01841031500401031445801241407400d100300410b07450030f0304002d01c503c0c0303040400d440300e80e08282207400f6030880c145080c2d180c21080c1016818003643c1c0c01d4030748442c0000248030101660200e003040300c0b80e00c59242041000c4101c141924200e00303481d030301409688805284403d5000070005016a00312600002c200c0d903860764007180c2660481c3d40007101c04d071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 292388687 1250 292387437 292387463
    0x60e28031103040803030105010c030201020702130f0b040501050a0603020a0e030708061e06030319050702041103090d0e0310150b16060c050a0c0201050c190f0501051f051507020409 80
    0x255100c040040000761040c0114241400c0c00001c5480e488103206640c148201c40701360404240c003e40540e0300c00ea8000344052001c02d14000003502800005181400d440d18009074041280b800c0e00c40c0c0b0f41601c002a04040d103141c1001c101764001c1d84480011008c0c44507040ea850321a9804000e2034000c1e0400201070080d9041448a02c40b4041d540c40121801c055498204107403038800105582c124087c00c00d00e070b04002c8414034199940e11580e500690080c5c01c00c00f4004040b01d90f4030045005140d1801202c03a981040f08089800a03ea088410ba2641228451011f000000e030480d5241e00704202c550f10b1000c1e503d24010006500c210074940e4403800c1c2440040500032140301e15000701c0e0440c00c1c424504894540d0040c510403003244004d061020104801a80d90002c020f14080c0813440a2404088445804d0464640c0302c0d000341150603600b040002450041300001c00448045420a144c00c2d00341010b041021140e9a030f5001e501d043c0c000e104100259480340036549070507000c1d41344130b0310071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 292389937 1250 292388687 292388693
    0x1103030c121602061302041e05060f04090305040905040206042403150605090118090204080a0506010b0f0d0c051213061103070c08090d0503190f0305040f060e28 71
    0x1101d00805601e1941c0000078a0b03040940c011451a41c0325258800e54141c068031440020024050110081080d0401d111280d500c1c1441d64082405080d0031103e01000060910030403003619103003840100021000e001c100210811500b12036000f174401092a4241030710b40c01000d449146844c4805125680039040c410000c2e014801c81c45505114814420303140d0500c9000380c4a44640ca010fa41082911490490910512403400c1e0151011260a543e580d54403582c29941c0c00c101081585e40c0c0c002e00000048201c490700407190b0180b82140b0050404200c035041308001e011210854003071000c1000401d98140d00341c007019201ea44201c04803104803d06080000840d4900186801c18040c03c005215415402c4210714000c05d500820355170b0f803007101c04042888841ca058008000380700109008101c00c00511a016400120790381c3c000840d100c001c811010740c2c1040e20040c10904a400c2980d0108819401c42030071404000110b030a4203810900328800000070244500501615400b80d80c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 292391187 1250 292389937 292389967
    0x3040503030114030712020613051f26010338150108010b0d150b030907061421060103200306010908060609010e0717042001030c080406020a1103030c 66
    0x40316000784c000b13001d1507081c042c0e041860b040c02103019105080c081100340c06581001d01d9100035042c09041d1074207150a10a400800d0200d030301184001c120cc8005000d9203130100c0d0b10000c2200491072041406920b1500c500c40c40b240740d014a0075081c401481e800803411042c20320302c031000d0341c3c1101507550307894500250440500b0a44c0c180d8100140c50004000514504054a114442e136160000e400840303410b808036070803c10f070301000381c0a401004103c1c0c03109001c42e0700c01c105c440035154080808105100101644035030240304140d204100c03200ca1a51010303a030501d52007807040c103000660707070030700f25002c4c820101000041c42d045a00004210403075030704c01d00410080059800071315843c00c0c414009586aa4140900b602601003030300081e504c0c074800c07180b0540041900a400710b1604150603c1513050b03401281c20340c1a562416800c1300b10794071901c10504c0d0b0361443d558070b0703015464555400c000382d0300c90660710003001103145002801c0740c4117100560003880414141559901c6400c00101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 292392437 1250 292391187 292391219
    0x1b0f0504020306012705090c1b06010b041208040503010e0a0212010b1509030312070201090308061c14031c0906060504020304080f0309030d0c17061f051806030405030301 75
    0x1000c0c90060050283c966000f0914042c00080d581e24941245030125282940d140941d009941c8030300801c084c07182011501000b4582e60002c5501c0450207030070010503030741e00ca900380f10b034400001041200b089003080b05401a042c1c90700c0b0b200e00e54505655400001c1c03d5903d4251585e585821401140085141c80c2e2000e81000d101d81300288040f007920f1002a034400600246201d2500e0005102c011654003803080700c0202124003003880385c0b414510b500a000b0420440220b021404c40d030041f44a40c1303006130300004940002c1000403181030055079468146036103049071407480d21040c06400d1740030700002e001d9001035444010010709081c141c102601501c0e090785c00a80151b104005000115103d182142e0a0828800d1841d41e40d03150064090b1640c4110081ca10007145802500c41c00540d01c0466658410100d4055824588901040200700042008002e00b61203448410450301c5015001030140e038501c84031380a40400c1302e130003c10310b50790048500725250f4200000501a01382d00509050f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 292393687 1250 292392437 292392439
    0x6030b0f0f07020c010c0204020d020a0908011107020607140705061b01060f0311090403050d0609020c010c031b0f020f01050108150109110f070f151e02121803071b0f05 74
    0x1100c20b003400100070352948240d00e00329040043c2002d04100355240d81d01210440c40c0b03000400c41d912032107060010404c1001d40503540c7c255007841c48141c01945c45001755000d05070000c06451806020355035081c0c2e400c81d0207000b11030364059040d0000b11582d550b0007901c900000d4000c142401c00134445098210341c503541065007404404041800440d1280040c00b21440003681c03040b05c08e40700c604080c3c1d018004c0500c0d0303820752400e011b00860304d018250003030603040300614000e1010b1468500c0540030748260804181458440442c800034030342c1b0411140c09408124016900742100e600192425524241c00c21a280c0d03000000f901204091000010b0060082813000c200c41c401c01220307140141b145903090451050046000818405c141458006060b801440b100928000307901e400007038200502c40310a1001440e43d10500100f560003180c3e45061040c0c000400340d0307180302090001044240040360b0341d20083c856003001864540c00c0301001c1305c00821010714940b505464078007005282e0059 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 292394937 1250 292393687 292393711
    0xc0c0105090f03060114120708070902071e06090b0a0902130203061201091b06050a05030c0a0908100c0318150504050a08040e0105130606080a0507210209120c010207060e0a050406030b0f 82
    0x204842c480112b1500700380e4200e01070140c5d45440a041074100115640004441c00048410040800040e9802824181c0c4079030f18489007903403002c00ca101115401c0b0300c003940001c2c0302c43e105a04900769900540c1c0c0100b00401c559108041d12481508403845100c0890380c644030100081c81e00186441300d03c00501c4e030740c03804038074090320454020424040540580300240012134402e0f0482d0184d00303481c015001610072102c00d2003080d940d0601408620141c039001c249014020008418841c240d840710303030380007000092409082c4607490010400100151000e0159036802c00000b84100000c000800e515006c200d410350420b01041400f84ea01d4200e900c02525242e800c0090503003080c0700b6a80140200390001d070b540e0341e880341507a42d01e5202350a82030021101c500d40503070741003e9020b0074211000341c032202030103034078141825500c2d0500e04800d400f41e8010402080000d09c0395a40b49503140c0064441c00c1d6065882c0d0125069a103150400c40380752a09108200501121820207a449861140d40c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 292396187 1250 292394937 292394939
    0xb0604090213021822050f1e0603010b04090b0906010b0322150204080709060504020c03072003060f07020d080f0c0702030106030c0902031602030c0c0105090f030601141207 76
    0x580c0c08000c245070500b226000301305480301d106820003042100c04054069070040c06074040504e00c82054111014144d45400301049540d9042581c4601c10010310301103025035070101581c00c0d00c606000b405160305648400009801e1b403110f002d600ba00d03610698001c80345090010085041c0f132340c143c000c0e840140090080059041c08d420210500c10098000200d06c9101d030304182100866035440041081d0000800040300c40d000100602156100d0404000854492082009901c1401c1d24100c0640c81070040c4800b04403140c424124982c3c40e13500381c81360840800042070500300d085a2020040000030200941e80343c0501c003821a0f2901d81c500541c4929220071030140381c05010700040040c2101280000441d2000d51211002c1c40d0480035200342141c0c0d5039101000780d4000c482c400d00c52038450065480450000043c2d540f05c124240240444000907001160290884104298405011400c048041c0c805202e218041d00b000095103100340c4d00042071003410f6103100711541d00781e441440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 292397437 1250 292396187 292396189
    0x201090b0103060914160f0506121b04082401061b08030703090206030f090705090c0d0b0a030b07020c0a120b0604050403050702030601060f031a0102030304031101061a070b06040902 80
    0x50707056aa00a100003180c1c06a03040860072042251a00c4d4142e1051328003800138109805d6084044400103a03480e41d902c0e4440050111902420f541071960000d0b10700410341300007144002c000360b0250406041c0c20141d40d2483c0f2443c1682d00700c00c0c11441e12511161100c0003103001c50042c05402e5500340b810084903500302110071614444c4006c0e040c4078020007c1480284070380c05c0b807034100ea001044142c481c00d160290b0708003100c059802001070722840b4400a0141420816170f8405e22081c840c1504000341d603012540075002c010740c120307801000700c1d82c0400096409219940544600d6004010700010b480034008590100d41241040300f50a00c400c00024500400c0903500c0300060b1004195510703a4502035410b0301540700020350500a01300003080c1540d000d920441d14640030b5406000041104100003844081000824010381040001030042070150701c2181c8031034280400043c882d95a014152100507007039103047c21000000603610240b002c0b0b0181260041c004840c2000905010b0f4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 292398687 1250 292397437 292397453
    0x7030b0a050d150f0e0714030c03060f040f06020409020c0c030712020112020f04060f17010303170709030c080a1506050306040201110106050405070302030a05090f030a03021b0a0c0e07020109 84
    0x34100810203c660b000018402810741c10140072108544800e008002d448044507841d03814a004503010038010054011071403900007200c0300a520068050b2a032a201c52024038541040140181c5200c0040c41444e0001101440280010545814016150301041201504000807000c420780709900c072040c240140400400030303032046030342420080940c02c000c1c00340c01701a01440c4280070281c03401140000e405a040400e401040600781c0d19240500b010b140c002550704402e00003d40042c605030341010480c002c480c1c003290044500d0030044019592075a443c225265950080e0640c1c2c0c04c03e030100e0f001c01c42045403440c00d054030018180403042c248400300366200700050000e8104404428ad0400f03c142c203503c42e0001e000302074402c1c409840c0214020f006075100f5966890310760702c2c110000340007100100c1c1c00c4007442d00c214007540c50000000402c4000e904000110588410301140360500d021003008a041d20521404002007078074070301049641c0c0010000c09550559040c80c091100207038400d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 292399937 1250 292398687 292398709
    0x1090302130e0a02060d0b1801030f08071a091b090412200f01092306010303030e07080613120203250f050303040b060f0f0105070807141507030b0a05 66
    0x1041c000a0281242410380c0d00d401d1080034040e401010008030b09170140015000140c651301e0565040d180028241540c0f102010300b4071002d0583c121018002002031078840c001c0a449000e088600c075185408558102c090310305841d02a4103602c20506651642d00703111000c0700480307003180c4003149890305841e101e18251011415808014040d212407150005a041401007a1401c030b00b110010308132107813401d00038270600c18255000f004000d0840509900044420440009030000c0c101591070340e64250050074894981a406001d0300b0408140d00303000f040030504c00c20034517a10420401d4241000d9602040080021f030440d001003122840c4c42003040146001400038901141500c0c0c0c560a0450324012003c10061403400000244000d120441c407503e8017481d412182179a03030584c0d2004100703445a421031041c0c0814001d006d4503021401080c0a4090b05010301420058250340c40c04072410b04102c0ea1b01c00d140802c000c024481c14070b034107100d00c590900080c1d0317502a007141080000390f008500c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 292401187 1250 292399937 292399969
    0x6130b0f090f0d030c0206010f05060d0c030b04020d021207050403050712020613080c0315090c1c061b091a0d0515120304060e0303040308090904060b191401090302 72
    0x24803404039031415020403403034440e14804016201505525030b80200039040c1c0c0721079840107100b10400030070410420080c601c12100c00811242c5441418241240030f01681183c2a0038903540d802040b104d92510700092200a9804a0050f55000901410b0b0200100030b4804002c0240510050000500020391070043c0e80c00f0100c4030036204030303d100064040c0700c3c030070b003180c2c1aa400032800600072000080f4000414021810788403030403081c24071560f184070300301c6004901e50700103806003c0d40d00f861404c00c2181105400022021091034603040159103e5044026000c848103141921083d48001c40c540909880c1700703181c5410184c6a00e08240d401803c0306086c404d0b07a5803002c1100c080c5c0d0440c003003282001c0580307c502a00c5c105881da0b9100c0d0401d10646011900500c900a4940b401004603801e50f64000c1e01c0741d04101c10642072102ea1003000304200c46081c0d90b401c0201c3c041c1d40e086004040700c009034038011480750601c610704418038030b48204d103418007260f5207042c4016500c4c14400711060035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 292402437 1250 292401187 292401211
    0x110702030c0d0807060c030b01020d03150603021e0415110604052e060e06011101020f03041101180308030a0f05070e04020901090e0103060501030b0c03091218040f09020306130b 78
    0x4203030f080100702481652070040a43d4540300310480780d1794264200c14880c00742602603421080c17007032034141c0690341956000303c0d0f00c1c00d1144050003418003d6024144400d0501c0c4c2c2a140040c4a0100300b06562064002510804504481030300c16603002c2d81c600000f04808001d4a07150800e42d82d4582d44da1044880d000b00c40100e8400d4041314405801c000551109240043c0162a035441c004842c007401a03a0303e0b4002007a81d40080c1e0255814002c40d070760680401d05252465849440300c41d035520f40040e04504000e403c1d858145910034440f0f400c030286001e6494031750759081415185041b201c0c0c0500c0f80c0419400c01080200711074000340b1102c00c5c4281904c4c051399880311000103d0f0f4084050f040448031040040004c41031100301e500c004e05903445048801d000d5100c3c00262010b6010450302c1402c80e900c580240362028941602414100d2260034042c2403504aa2001600382e64403030340e820030317042d80c3c4014100540c07500701700c2580c02c00410704d030300c13411804142c90349242c03140001c2154608007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 292403687 1250 292402437 292402459
    0x1061205032b05040c05030d05070203280507150315080a14030d06120627061a09090a0c09020418020325090801140c030a1808041206110702030c 64
    0x2c407403420700c40c510407040d03000300058a8985460280307185c42c1c0c02500d01034800c0740781c080300fa18000c2c81203c0c001900280101744030a403c105d25000e900c041c2003801da05203070034074214002440230005000900718801d000d0684945d403410040454900624504045103511002c100740300011850400d01c68008000d80c80d0050109005465840f802d004920860300e001000a07038802c01c0036025051501c0781a085c4441c204001d1070800070148207540c0f42205501001d82d40010f04543c0c0800080e100307500010444032081d4000821a02c402c07125010350350032075a000d0741048000c0c0130304030180c40390500c11802d1034142524441401100c8000034580d680c0003000c03c00f0398240340d082a102800d440c01c1300d0480200c000e4002d2489510b80b058070015800e01c03048071019450042118459024012960b0940c0d56124404001d0014980c20300b10100f40420302d030001c1114400203002415640c2020307481d403810307490f19104071003420041c0001c40d0f00a00280006035804103451100400840d50806c084c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 292404937 1250 292403687 292403737
    0x103120c0c030210030c08011406040b0309100c0507050609011b0e010e0a030c05090a0b0d020d030e0306040b010815160f0921020111010506240904060906080106120503 74
    0x1e681c580010790301007450102c26441c0b0b94550040c0380400c4996032022256641c44114461003480080e403994045002c1c0414480310072400050f5620400c1d83d0201c450040c0d4103d41c40c002c98a07005000b60015000188603000e002c1e040103c250001740000c020008a000c400c5540c000d030315a15501000c1008250108480c0d0b841307292a8044440014a040030f05a500e140c21344c0003a81601c03902d4020000c10f00080d070042d03854400d803108514050000c008000d0181e08001c0c000001007000c405000d2410840c01701500d040142c81e101e54031410a5103059410000080d1421900070a030070412000c1f03800300a5840c07040110450a42500c0c1040c545544c001801030740c1b4552a60405925401212450351520f5428115484401e00070788030118283c4610f0003040c244c4200b11803a5400a44411907544240543e43c0c3d070700b5480349415140c80c14007030580d0000f4141c0d500765215403021600c0711000c0c00111003c1c40784a005151030b60301886607002aa03501500e90007080e1010584080b103034156410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 292406187 1250 292404937 292404953
    0x6030309060e06030f01060836010e030a020601091d0619180203031917090a1703040f0f0303180b091506090c0a09030f06020c0705012307020d050d020d0f02060103120c 74
    0x14030030208010004041494143c12050303090911006242d8201030030603843c0ca00c04001c848150700f00c0c0e07014101c1d9a0030000c540d40540446080781d03a034441020300c10740f28a02d0900c451402030000030030a0144030344204a0800365110140c401c0160103100c15d4035801079030000101da440901100c181001440d44c10016180e19040851003201a04450100301c2078440218048801600c244041040c68203150000000c6000031a0700034489080144800b01150300d400301c9101d110300c6850007203600881b2000c664540d1800700030484158566006001d41c20a0522401c42c0509019002030740900d4110002107c6400180100350b48410001d03482103010702c40e05403540510780000e00c82803040340070300c0c10340029440314501c10803a004652010a0661050800302c503d00340103250b4000009814450044580c04124200d070310404202c003880008000380000c0302c00c014150040c1280c6c00044002801c900e004507001d008640042c0d005200156003215403121504485c40e080180c101c1501d41081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 292407437 1250 292406187 292406221
    0x1050403021309140601090c03050708010b0d060819060e0c0d020d03020f061003060b010e0a05060903010f1407140a050406080705070b0408040819050a0b07090906030309060e06030f010608 83
    0x4900913003141a0b0044a40c0090b000d0b0490300110750070040700074010f50440c1268002d940510000b000741380100000004040540fa40001900c000600e080e034034401103150849080809011600740444a8140b00c914840d1955050701c4e040134100721f50601000070034015102000034481d82c1c1d070850385001d26100300042c4032a004804100c5059042c450030b1044090803270301c401c5507040d09140c00c002c140e51291041c1e4034106c4001c1c00c1000010308090410075160880509182c0541d030392400c002c20350049008005890158829640180c1061351006102103580c1019481c2c090b820884801e0840d8000e0071141120014944403407a515019422a000d102d0070b00060a00741e644c10174001800300500007001201d914608883c5010500e40f00300d10301c00c1d01c9000140a581015920b50041350345140e1551748405246808040c541e280c5041d401241d800341c20a41c0000c040003024048507410010002121408540682c1589054200e44a00b0075050251004001184010440e24240a80111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 292408687 1250 292407437 292407443
    0x10516140d0e0c091e06040e0c041a01090b130b0f07050322140a03080c0c06130e060405010b07030c020303130e09150709140a0306090b101401050403021309 69
    0xc40707051010460280d8603030030901c10b148244a09004a80a028000d4440d0303043c3c17039150381ca4484d80c1c0d204c2041000620700d4000b5800c0074010300c0082d04079075455201311143c80040000720440308084100041000c2c00c0358021240305882048242803913518030740d1050440f40320b08a0246d650008007014044d40c051070100412901c0082600c81045140f0080d0b00c201c650a0f10f4400381250780c0e402008540000040004c0e0010700311300050000c01c0c04d1200034044455800100c5010b00302d85008a038a590080e11b40681e010380301d25007440203d1003e18040d801c0001110103000550404200d07400038450244004c052083c0c00c1e010404644060040c0c513030030202c4c00b42440c0400d40e1000e40c0e410b1b44404444520701800303461020003d103442d1409030390040320685e5030b020b0440d00381800303002100030135910b40394400c510b1200040052240c0c000c8031115480b5060303100e014181400c40310465604d607001398100810591407127109903807010a450489030110384c02409070222042c4080103007030099000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 292409937 1250 292408687 292408691
    0x41106041a09040b0a06270819050c010507030906050d1104090c1202180d03050f070809030d0c0b06061c0c0503090f030301050108010e0a0221060f03010516140d 71
    0x30320701c030311220107010809000da03414018219030f0801c024800240d4010303000441d100c0504030700000c40304841d0303403010042d140740001c140740c540145903d00307035800e520350b803070059250400420000140a410080c146c01e0070f0a50601c4a1640c01511442250003020100107001c5154081a030194001601d001e0320200000d40e1070381c0318900f26020b00101c0048401151082002d810004254402c913000c3c007803120990f18072400d08004000074201000402d80800805100c1e913048410364100900c0303d5032140307100741c0d0b440000e0414107003002056122541400384513107109d4041001d03100072951005044400a81d112028080c000102c81840c581480745842e0141a20b01150800c004601500c0c5150465408418100769242c0d80d1109004490004414400410001030189810f640040c00140054100300b1120008a182d00403010300303a250700124810320146050440d8124600c0344e01780c00038440342c030300600f00c200010565400c6400300706102c8002c001c100a0300c81921014101082d003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 292411187 1250 292409937 292409969
    0xc1e0e12150901290f042a080402010e030321070c061407080f01081b0103020c010525020d0516030905030f0d1e020c09060a1208040e0a060e04110604 66
    0x25590003041c00700301c404060241c0030040300c2044866802c0741c04d414002041e003041820001e09100c0a4024090703900c09101c8000e56103010b6905401301c107d0041c4031540c07034000d00d00d058000144103824000c900340c001c0d0000c01c0095503201480c40c503128945102f07048034004d0f0b2a603903c01c4030151404100a00900c2c5040030580100501030310b450301881903039850a4941d215488aa02e41840031310500004d03622480e8840b84c6031a0114454410f010705040050421812041031401c0d16000c440004040400180740d040c80401e01c052204610035504c01844214164a0302800758454409904094000d85002104161040b10008042d1101a003911525803a440b2420f07519030004401d82d0114071100b1702085130016459400d081040070754001d200c00d030407450030b011030305d980070b404190809800400850b030f128504a041954920072418035544030b14011071f010303003904c020309040011810700604001c042000240d00f0303006600218612606060207000410510803030340b01107217000c8080c1c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 292412437 1250 292411187 292411201
    0x320010e0d0623070512040c030b09030901020f030903030a0e0d02220e1504020f0d080c0c01020f010504050706080901090c0e0105041503051f0e0307060c1e0e1215 72
    0x420901e861104860034031803c84081601c0351100700322800c0000030014864007410782c0c0300c900b140d6003150143c41d43d52036054803500c03643c1011904542c0284141d000003008940341d64100550040321644502450030030032001c0000f601c1307110702c09111041060104907242503583d0070002c1d0f01d0350382c0d00a007103c1005d504c04860300300383c5c821307046041621823420302c695010300404903070a00c880c0c1300035046c0301e0310b03545d15820420047d04440755290001d54280c00403000843d910300400821035540c0003810b40300030400c002440c090801c00c0030301d6944d0400c000c1c000014000900102911290708020440b030781c403100240d00524415601401400217058005440c40c03240e81840e060705c00070b803014402e180a003641c05055166511008015900c00352128041d030260700101c0000d82040304020072a4a140b403625480c513005901c003a00c1e0f8594401a03684c41a40040c44a91103203240c001c0014600c0020f40040c02d46211300456a006a0070f50b1813011010400b40000b0300500d0780b1504910003814102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 292413687 1250 292412437 292412441
    0x4211030c0c030d020f0d0f050d0c05090a0b0408060406110f130e010603020a0f0509030a050742030504020f1009030210050c2d191a010320010e0d06 65
    0x1140b0301074098540c1c204141031000c11030000131040100200103082d1000422207800c84110f0200c010800e06202e940500f018030b0191035803c402c0744e44d80685a086620400082e01c1c5107900004038020108030401004502041450340280c20440000d4280607030069001c042c0b007001c200c42e81d44800095003c2c09051420100c0040d918034040e0b1004507a2118810f900301d01c955525130020a46801d4403a1100c0d11440c018800300d030010f42600ca07843e0607030b65514a0320809030404203071401c0c00c1060f182650f01c101415010314560310b10f44224a80503039140d005a51a03944100109901e80000600795241c0d500050300d500d00191407980d080c800c83c000144103000701e00040703225444c0c0701e00001d855803250060b40c100c2c6418078040c0000305210b20704001071050080242901820040320103100007010f12182006401030204150301c16010720300765040c44012051038400c13276a51001400452001084135400c051403603054a01d034482080113076510100d0030f140c41d51140b05107068000b000a40c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 292414937 1250 292413687 292413703
    0x102040b04090f1b0c110307051e04050c070f0f081b0607020f010b012703062c060f0a0b040b0411090117010303081605040801020d02044211030c 64
    0x40401007a8500e80c0c801c4c0e40180c2c0056102c3c0010800240100458004064240701c0300d03009044036051035440000c100c4d4040158101c001610400100781c200341418000e2070fa00c2111880d1007440d000c4503540700c1000340103008014041000e9a113564040180716000c5480300f40f0040b040500c0316111f8011a9a180310449004005021f407942d003080500c0c05009105c0007000585913800c1c02510105000148460307a540c104d007030b001107240040412003902c141c0c01c1800e001403248112981c2081a105d0f002c180d5105028141c3c0320342c04001540500060150b0001021400415402c0c0040c002502401c0008001b50f40240303407c51100035042103a004060780074003a21a6800c1c004101d05421946409200150100740c140b000100100320722004c00c040032040d400e0840c10140c40c0c100701822070300601d8900c0201c0d41d000074144504c00d00c1e000c0f18640054001d80d40442e0494082044107007414955001d902c0300360f6840703080c80090242441d0190f00e0815000c07203031140b40107035036a980c510b01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 292416187 1250 292414937 292414961
    0x150c0f070f031205062407020a0806040b0f15040902061b0606040b030f0309010e1305040302030d06080c131d03072a0305030a0c060908030405010614010e0307170102040b0409 77
    0x1802d080380f03507068000d0090520603c002010f29003682c40703080c400341440e1507498080b5080c002c200901c40059552241440180c0030030401040c079480c06290481220202038071880e200928217040003000030106a41006001c000e13140802c144403030348080703202c0e030240c00c00c9146000344030080125041c0d00010303064400c0008590600c400400741e8281501c1c1c0c80c102c2e902ea40260401c01508080d54002d40300040014006850240b1a81298000340b0803104240c0f8203c00503000050382038140240d6014031006400e4400c0900034400741500095100c00380300600012803908e904111035030900c0320a541c05812840801d0700c0d40c440151030405480c858603842203038169490401c100c0c0c0e0080e0000d400003603075071140c011454425000301c190703001e941d002c0c0c2c200e40894565504034001140a4007840c02035102e000041a00b5040004e034400d49482e04560324108906154044119500011500207c03071080c502000780c6880d88400f10f01900c0340f0341046000707003000180011018010b5000c0803214070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 292417437 1250 292416187 292416197
    0x1050d050c1509180f1506030a0507141206041a0306280c0315080303071b0206130303030b010e030f10050405010b031905060f01062f010c020102040302040b0306060102150c0f070f03 80
    0xa2209880440c3d182000492070f041f01b824400a00401c201ea803009801c081f460419000048424415030307a070758408100c0380801701081003800390398241030080108011011500e0320040c2c040c0e80c0401d58484004184040c84000d902071b10505280c9510201c4003d030340c0c03e40510107520151400f502600386684402107180b0003c40026000c400442070324040c5a9980c3d820407241680506440c0c00307a400982030341c0c01a030030403031000f00d50baa100303503c40107520946000c02c041c0c14500000d00342e00551580030740a504068035551110700045850308090b4132002c0001181d40751401d00c10f00500c1c4404c0426010712800807100c0d40c420184040c030800714440c00880301ca9030303070b4a11669500030081c8108008a401d1a50071844403c00e0a050f51541503071500b01e0301d40292024085007510004202e034409030350f00140520540c1403170300405a0503c425001031006d41070020000f55a017028400c8442540c00b4000030403081811042100c041d143d0f034808142d04c6001a0074a41c401079020202100454 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 292418687 1250 292417437 292417441
    0x7150c02010b09010b0406050f0d0e03120a0f05010f12051c270503060c0702060715060504150e072f0607090801330b04081501050d050c1509180f 64
    0x2e042c176030494003a074105594013420001d82c2c0c2c0b0210503541000002d440d07880d86408010580003000c0010f403c4a690740b24044070a41010b0510100700c1d04d00b55504401c0c141084014418641512a000d08455045000c0e50300e000c80d0341003c9042c80240821140c0105840c094184841d501039007607801c0d41300c41d035180704030b1080a00303140c802c040711881120b802d600980300094660b0010000b502d00c032030000c0c00c5e480c5402e81d40c1d1b44d4081600307040da040485040d039400040c0280d0500c0c1c46400388010715404003502c424108020041c401a006000c43d04020f2030489008030130012405c40720000c0c25105821014040640c000c6031141e404940050005203c13500018100318140900c9076800000c01054640e85480008581103565487c894401580011030018120014000620081610710003510861446c80f40051403840c06900284c401e8980720701310800303c2c2004c100c015000308212011902500c032400c210b40c5a016a60314580e1201440d1a902003a405040c482803280260f186808216 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 292419937 1250 292418687 292418699
    0xa1406131511070312120f0c0309050111040f05090405070302030a03031a0a0b0d0509070f0906030203060708040b010b03190c0f0201050c0a05040915033311030c07150c02010b0901 79
    0x5092644405040f50700355903041700b0482e00445074070a60200310315022808040e41400e9005682c04020251300181e0b0f00d00750b5409200007031040c21540c0781d0031140180b510345400881620031a19015003442008194041420040101b01d180c00859028082d2403042c180b50a015006005100400e21010300340007408a23903191203030070034083d5015178020b40c1c00e056103030b00007000901e401800d4040d40c0c8611200400d0b42a040c2d18190010700704081d01041090561050600307110002c1e12080c00e210523102800002510024080d041d0b80d290a4002c0d103c1d91200620002202d644a1005480385008030000e02d00c4d0b0f01901002c6184084e4000b84480d072180648149544520311704240000c1d000d000901400c0c0d490740010300c1c40c59035466010362144c5c40740c543d070144e81001c441400d40744040c1c19041000000a40d10b928040f142c00c282040b0303030b0f900d80c5c2400103e40700c0100306e05c01c190000140344040103c480141041105180800c102d00c0d24803410183c000c0c804d0040003482924103000010304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 292421187 1250 292419937 292419943
    0x8070309050609130c0c02030105090a170a0c021909110304020f150901030f090c0f080d020102031608040602070c0335040905100b0a0305060103060b090a1406131511 73
    0x4803c0540340040c1c032888804e82ea001009025134901c03c0041c0004014051381e000d002d01400b40790b0010191080300d50706e207840c2d1000200262071148946040c004c0406194103c03e28001ca2a010365207001e044c0c030615070300780b0024429000308006625040019140c0c02840d4080c0d480341d07109131181aa0400c42c50304120f40c020004440d2144c8034000c01681910794401e80007002103c414000100304100c2c1c6a0303600720b8070f20b03281e01302498001c2d02030010004124108111000381d03446000031840d5081640303031911200c3c407170700c003800a10001c40046002c000e00799046610b070310303004031410b4001b03922071400075115401c405140134008240e42c0000c1c0081448071070882c00d80c1c0ca607080f55140c40d1504603c10f000d03100050001900d20741a050000b0000520001059810b0710380d40d0000300d0340f900350000b404560094005081c000c200b03010340b01c0c260720b0350f01080e030540e100304180950200c81800010078520502c0b401100e40c400c041d1000036480050640094881c60b9511032004840b00c0c4444184c1e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 292422437 1250 292421187 292421197
    0xf03020a050d0b040809060c070e0f0f1e04110301050709050405090706050316020a1401090c140d11040b040c050304060f0e070b0307050f0403050a12080106020309041508060103080703090506 84
    0x3c0a24410105000400c45801040c1620020b40101c4c2010300e4036000c2c5080c06040d40c0078840d55082901002802198081a02d501c41452001c403d85810b0000e04000b003c042814001d6540b88034801107024801050707841e4041c0e2000800a0026262129000b040700c2403e1046a00036420800850300c00103002c203d4a09a9405607103840c1103176180084ca4150b40e1000c083c0205500031031941001242d41d8a90760720819804600108500700c07945020305d6504880d80c00f0b100c12842c0d6402d1541c00d50b0b13604074003942c8150402055034082d0007c00c0060f000b04284001c080c0d005140c25812003440e41c0000146200e940990320401189010030a600c0070f6415000301c5041e1034104410501c49441c1a00185400c00c1251802e01e080600d0100c016410f40d10940050365194041076841c41002001d81140c1c2403079142d0b24100340305500d08000039547e4024454443d00c00e9865100d1100c02080306032668008107001001c5034120359490411035256030040c5426030001e0b0141102042c1d504041084407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 292423687 1250 292422437 292422443
    0x20a0603020f0a0507080d02031e161e0e060409090311010c09050d1e06020c0118051b01050c2b030b06040b1809090102090f041503030e01050c070f03020a050d 70
    0x24a007200301c03d0f084800e540503100c02c40355001d0a000c1440010201e00c059445484101000c0c0c40c81001e0b1902e000d00100014060007290011840b00000320340d0ac2140c107440c040c50002a00f14611024009581108883c0000c41c0c03c0000400c001680c0d04542d04441c5e10380e8029182c044102207840034050980c0e03e40307044d95005c00c021071410845c504000585038444c60041081804c4a8060820103081c040e05940c1a615940c0100360250281800e1040354144080030311806000d000ca941c1721900c480d8030303401c007482144a065480309940d008004845205200000340c54125042d0f440c51248404181300000c03c00d0008048140014003078072038903030900c00003003116080c28074188600c0b1041d030200c031810300c250041154058140d200c41c400d080c000c0c1460070016880b2000681800b004440c1b510140e44a5402c1000c2a51241c901c42c03d07600c180e9130940340c000c80c04054540107880c207101b070310111402c5216000000641c40e60070fa6012040c0ca05c2126034120582d0f542040050b110f016003005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 292424937 1250 292423687 292423717
    0x403050a0906090506031b0f03040c061b0f06020d09210f0206010305150a09060e071a0906040302120109050a1b35070f2309090d0c11041107020a060302 67
    0x40346c445041441d00000c0180c801c10194940041001c08c004950001d0302c0844000340549000c0c800a50801c20350f091016038022110410300e6252104010855181c801400f081d5001407040e602c02840e410600e446a0015501150740070b55402000003101d01807600b90006040881c4a01030381c0c40414401c0c1242d0300100140400c0c1c0810a48010030034014148502523a500c00045001494500401d800209450081c0021619228442d000319a4000840e810001d0400c20017441c0d0713540a041c1c50540750103681000f0000d1203807555500604c504031002e845485985880300800c00641a1101060300c005109050150fa41c1e0800800606c07002e014040101c0784001010300b14951502c41c03881ea0000801c513050303650784e40868074145034244c0280600040c10341c2c4050220812490307128440c0340580b541801444d015024903100c03d082d44c860713020480140c005c0c400f4032490350f4060303480030300003001000030182241c2c4910059000601c01c0340074040050002030024040e01c2903544008a801d44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 292426187 1250 292424937 292424941
    0x4050c0903060c031012030302030f01051c030e03120708130509060109050d03090509090c21071e090f0203071b020a05150c1606020f0a050712050a06050403050a090609050603 77
    0x3050f01039000206011422101ca21000982001a000c0e0300540f6000e03803001613403400c0550900011040581040340181c402c000700702001c40c0700851320740c0d20b03580518103e400300e51642c0020b400d080c0764041300104a0404284102449a800d00070044c00491040d00000f20741c1e28000c0c45002c1004907045804298051810802c5d818070310075100340e19109183c1404010303141c90003d10710480580b90180303d68064034551001d0300b001d00a01c011200500c0500c04e14a011340742603613a94000e400b52201141603e80140903500b250714808000c2c3c101c0d110144044800118003c00a40048070024006141c22886901c1c0380c808000410310a9009414003500e01c0c1010207100d9501d91050986154800400c91404003040601c0003c540d0001e14240144441c03405070028503040c440782400005401c00301c100c40000d0400902101212821101a0192100c9060407410b0040c5000040c04060408080004143d8018000c042ca003481d6141d4204e40b94542004072034411340c900546402c2030302080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 292427437 1250 292426187 292426201
    0x8041505060301181203140c0a0e130207050102130b07020f011407020d060903090506040b09210a06060501182603070c03080306010f2c1302040b040504050c090306 72
    0x8180d50001c8041e0000c01d001004003600c1c41c06490009060302c800d203012001710111681030003000d071a1260521207200e20b060072020000386c0d2040340800418003c881e05070601e2a1600b6242c0c44680c100380300b046458503854204203003c3d5001d400e11848550826802050440200c2d043c2c1d03807980d4018200c032201c550948019241104006011785c15020140610030050f41c50f00c40b003000700c40c80780f800850104000c0c0340c0680080000d800c594403d0a0a000501c201040704041d58000c07041150107802c0794114014251645920f0004840f80340a25240c0f50203110140c1c21080032034600f80d80700d82aa0b00400c554882404040c0a0081c240840b0480309102c002011803c80c0001100303c182c0e8a007031900d5403280746040c01c0c3d42c0222500700010081010700d6070002414103e801e10360820803a83c45c00403c0b175081103004011001c4004104601d1448542c44e40200909205240c85045640380e0321081c0500160b040303486894415070805c000602c14006030810348810040140c014266502c0d0b0f46 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 292428687 1250 292427437 292427441
    0x3010305030a212414010c03030b010e18150406050a050d140f0f010b0906092212110709090b04080d09240b091012030e062206080415 59
    0x1600922034211000d9000f48840b031a03100714103a81489440103044004007028401c40b00b201588508000c1c4246080070f501039030010b07104442540d1610b0002840030380311f8010fa5280c1c0080c51010340007042e607aa03d41c01050020540c501503250500349090f00000041008160b4000340900c0c0d8000e48404010051401c120700c00300c5125105056014002c20f584802502c2c00e40c116002580c182d01100c06401c070a0704c280700b8000c1c0c19105445000b254542003004c903c8020000d000c0b000a2070100f280d00c5c10402034100301c804071990055800c1d6894030408e034010804003407220300701c1207030040c2c080005184106119548201d5404041c44c2c207656030b2500c480e05140c00802e40c0b17005240d101c01d80000000c0c0880c181d85240402c0404015103503620b69880401c176200101e0080c058940c4c0018000f007009181020011240e04070840190b610b06ca141c12a40b00681180e201e4110782c1c00705180c282d0346070884020302c070004040540c0316001d0380e034401100c3c21601074802502e0380c24000e112031750b00500c035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 292429937 1250 292428687 292428707
    0x12091401141603270501090b0c070c06142a2406091003080307020a0606120308010e0c130b190f08060f040608101d0c011b0201090b030c1e03010305030a 67
    0x2201840082d9143c04e6000700c82190360083c1150a139544030020420070103800709590f01f000310042c806082104940e104603100b075040c000c0d901400541c644804180d10250210b808984410f0b45652140400a14488051074000300b20351990240030344c0c45414007102c040c03100c01e001402c11070340450f8450000744401d01c0c1000e0034868001403a00300c0840880da040c0c008501030010360380284a1002c4605003e01103035400c0c3c00c291a05a9200030703079004603901984a90544005400d0881540c56210700c0700300e14444c0300d58a42c3d9155a85500043c5000d20002420205400f06c803c030751075540d1040101c4042140040e80d0011400f1b25001c1100381c02d013440402210000a0130000c1c03483e0310b8203061883c1c101d01070240000c00c1c3e02c40349000c12440b4540c903807a07500203017603004000c2d0a0310203002170000705409040d18003408200340004203680c480c1c3c0312a002031840c0e103d0981e8a0902120b61516507000114003002111080182005980c0c42c0e02101d040741c0e0080080c40c180301d09148101c1d02c5183d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 292431187 1250 292429937 292429961
    0x4060905030705070611190f0b0a0b130518030a14070317090d031406030a150f09050d0e0906010504031b05040e010f0b0a03030804080a12091401141603 67
    0x28480b840015008000b080040c0400b600d03005040444268160f2400c69050240c45440030f5440000d400a50101c0308a0003040c1c1c801800c1c030090b0340c0c2c207007404018203010070161b91001d41c80c407003031480d09065400a40a1465035242900f4444004803060788c03886a84c0c510f80002d074504201042800712000901200780c46441c140520b181540084141c081098507408482e411140000302c50b26010702c164030f03000c104403c000c0410702e00f001c0000d0f11888491406031440b061182c50100c500340070350003440d01c1c80744000200001241782c103185550f44c2074110050b0204d4200e0007003036411300d080c00d00b862003254140d4480c2c0c5068107641e00c01112000103c0c0014049c002c110f0045060f640c1d038001c0300c0f03204e0402000010b81c0100d40b4201000c0d00e0041d40301c140590030004050011907400040300364010780162846a4400f0034100032034100700009592000c00d032400d0380130000c100301c801030b4100301c4822400a00c1460708000d09034a450703170191840c45000301c00ca003601c00c03214040c0d0080408541 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 292432437 1250 292431187 292431193
    0x60403171201060825020309010302160f0b04020a1205062701142a0f0705121c0b040c0c03120902061c050f10030b06150720030d050304060905 63
    0xc1c00000100086080c1c1159000c070b1900d0007000803c0044490200350100e00d0740048030846052680607440b4400c03580c816041540002c0c185030310300c00c954590740302030358484500c021842042c103041504140c00e480403440b906102800181803d1031a4072042c20310b40200117080c064581d0100d21000080c851004015070768211040342e0707080401e05c070303e01280303903030410bc0d14141c91314569030001000041c2c8589100036040d6000140b2060705025520308011041880360350701c2c0b240c18003e1030100a8184003040030b00010306e004602404100001007100400c2d4140f18010f1201c0410050740d1007104150300156440403820080313440380040751341400d09200d00095007815900801c2440d884000b1101c41010388086080e680002c51140d59444200c00810301050300f803c0340311800b60b40040c0f10151900304040c001c22596130340c44160320048400b558255541c0c600350301c2c203005581880d84040072007542c07003012080b40b03040100300a48102c4041d0703205132031580c0c1d95036940014071580e013050790030348 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 292433687 1250 292432437 292432447
    0x402090a150809280b0406110f040303020715020604030e0415080609060105010e0108070815040507020f0d09060e13230907060f08070509040908160b100506040317 72
    0x29480d4201003041051650390a041460007055041c41c000260410042d003441c000114540011560013a032050b980c014800e81c1191550f0528402400c284444520b0541340000c4007000941d0303c1c401401207902c681c0036255400c0da00c0b4a40b040c1d914011011001603080040000c002030300c605035070711614400400010741000c0c29105e4042008039500400546d40c4854203100906104020050040009103008407214101500003407501402130810401d2150110225581c03103e1a00d100013400b102500c100601d1a00c0c079002541e07218040c002c01920b02138682e40c20b400c00d2003840308030b00303803421516510402d0341d1800c2404995001d488480c4841d0740c0e02e03c10a40321710348402d0040c4084d2a42c00c801c11060401010709400d150f21580b111703040c49006500f89000035000141c003a4040d120341050b6403508404404035001e008440001070800c41e0004460160101d0104046002802030303800d01c50955908810001ca00414090240e0202e4240310400000c0c0c07980c404e0154501010b0540741c240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 292434937 1250 292433687 292433699
    0x6010b190c0b0106030c03150602070e090a12080708150105030c0a02150c040e0106020a0215070203010b100f0e01022a030307060203040c03021305040b070e0307080304080708010506030d0e0402090a 87
    0xb44082c3c11420000340c5030010031000c9645406600320040210b601c82103090701e040c2c40a5601e080f0780c0b1030121010041d034006015000280494001a03421030380b8504140b180010080c0a031504451131000300311860003241d1401c024a864111320441a1205451916013800c00481c54005508950451180d0740c0143e1000c021504c400340a040350b11001ea4981c0d04140003080c1d00300050b0061400c540c014061030703000d6034403500e0f2900c403441d911542550701e1640d400440e025180024416400824488111040c0b680c442184c80c0b0315141c50f5109511080342c9001203844440d02544900c100c00d00b0f95100341148018034421a0714200202200d00d0700d4010b85d6402c05980040358140c940d4030041d41d0400550030411040da03200c07240c9900c03c004c00e103003d6441c1b4840b040d0142c51030003004007a68100c201d07071310200011005442000100c039241c41e6100125942e40d40c65001e408819428180030034582d040001d03804806a05d10b4aa10070110140800d101c000d407c1108120742c4a1141c007800100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 292436187 1250 292434937 292434953
    0x12070f0b03040c050d0b040b100509090a021906080f070e1e0f04020a1707051c09140604050d110a0c0e04060b010905030309090402060708120103120206010b190c 71
    0x2408500e08aa07124070b480c3c240700d00c0301003103644068020151107201000150034090aa40d10960100e1160755030744031b030000c1c80f25074100d0790070141d0008004024080c1d0400c0c00140d0302c034800e200321004110700c011b030100980c0ca0701c618402d0201140c09400032500038032044804540c07041c828580008000d81220020780715400b8503c040d4048640c80c1c3c50000d0a040c10112165280c2c02681c055283c004440c20090500c4110744603039181c20140d5000c242c82900c0b0303800325103105140c0c1c082d141e60f01c1903540f183d0008040120f821584034a040404d84511040455180d10481d008000741c030352408031a2046c0c41c0312a080503001068010b0030000000140c01c680e100c0040d00454612042c58500307494554116640d01e64814140a29008200300300d68000080f2945241d050f6030041c5181c03114804500c0b00c0c0581d00004282a0010a112405105d4914040d0489016901045080c07503040010307610b404003802075030303c4440100441c5042c4406c40b070181000c51140d1a140c820581c858440c148 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 292437437 1250 292436187 292436189
    0x91a060a1b1b060f091d15030a0615082103131a0106052205060a230309060f0703050c0702120a0b0403050405210a12050d020403030e010f02030309060612070f 70
    0x404241128054213030a41c4c00f402c0c01d0081e00d071031001c084034815080c10302c1c00501d030000c141c010200000070f0000310b280c500b4040e488140f5030010701072001240c0e901c0c801c61155500d000c0e0300c980344100d0f00d280d04044c206100a41158001c0e40402e8a15100d90b0f000c6007920104190940d0310181e090800c00744a40f00c851310500810365660b40f0707502e90788605a070840c0307a400480d44e9005508100010700907540d1b80c0d4210f90340d14000b4180b2444002c00044103003201036240c0c00c8001c50810100404c9003000d400b1910f54801c842c4001103043c20f5607051003d03012504240ca141416004c14006880181020104000912203034811910750501329682e40b00405d03001c860480c00174002060401081c00c186c14144030070101d40307030f80003c1c4440c041e02c40d6580307510191000d031801180c0311500b07502d54060310846441c10030b01d000c15940d4988a0a0280814455101050000fa014140505c1c01480170054034014031004010f40440d407180ca04006004c18500b84c04c00712409070a80000b0303a860700004600c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 292438687 1250 292437437 292437449
    0x703062907140708190b2a030a18110108071407060209010509060d140106021908130503070e070905012a03050f0406090302030c030703050709021e04091a060a1b1b 72
    0x440417101d28902020b0b2407801420b0500008041c403850001d01440c2c250301d45450b15a101440c0d1a40e8400390340201a1808030395403402c003098802c0c4007080c400c003000600d05202c400e0300d4000c62603e43d0711044841070300080590010030010f01c90346000030403030307002004003e42c140b40040c1002c00342c40000300c0e20751110b203a418143d9030324408861030320104000140144481c0c00908920403010750074510382280b0410051402c040000d4003846201d6030500380d0041c0030090300f1950282d0710750341c14000d6008240d5070000400c1284c1c2000850b503208034007014440c410340343c0c0140020b0811900d92880440603c0c107e051140600544441003031040103800281103aaa0310f0307211900e0b41c01458203120052031042d0003500080c1051000ca00d0001e03882d000c940f4028001030365000f4240e50342c2c04480383d22880281004000030001804c90507504000d500c0c4032203441082c03242d0318a0040108030f20542040102050b00380c0c0080300900102c1140c800030364000d54090110300010704030144030143c1d40e0096 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 292439937 1250 292438687 292438723
    0x302070303020706020d0506030f0d020a080306030a0b01120303050a021602130b042408030c0c01180816050f0307030308072016030b0c040e040f1401050703062907140708 75
    0x6860104000103cac40154000b5007017510100318002d403945105a809010000000040b40380d0742c404216401d905031f00004611803a503142d0001c0c80600c204034806030002410180490903c0c401c5108982c0e06000c101c0d04034010300c4040c0d0a1100070040e25000c69482585ca04032644140c4640c020340d1424000115294504410424100c09055941e009100554824002110702c0040048c3d01d004144090800310600404c020074420031001d140c00c18041c17405641206100302481c020010103480c01142c5101e2020240801e0507512400e40c032000c1c0c0001c000383c01141285005101580140b0403944545900300c10800d0342c0c41c58042910400b09616880920410074400784480460308100000110f0346480e14040d03846a0303416015001411928988450070200450828a008501c407030700004d00480c50600310141c020b003640d105648520545802030350307080303240070107580e451035691020900300040c1d5100d41c90380c21a504210341503445907010100300c07074038100052000406500a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 292441187 1250 292439937 292439941
    0xa05040c030f0f0c02250504020c0f01140a050c130e1f0e072a03050d0b0d05160f27021308010203070e04050106210213080c042a0302070303020706020d05 68
    0xe103891040401c0c0b5200d185903d5104030000804071b00c000c2101c1c1c0880f005605d41584c2c401e003d05254120502803019031814201c0c0c0508205c00040c544038441e08013041003160342d8103d40030301c80d11903018241e0440e190b5000a201d0100d51340b040681080c4120072200440481700d00303441806d541030b00b2480c1006e101100b007009643e030080300021582d400b000a940c1081c001c415514076985018001410300c00d01041d4580c940301540e00c042c481f088010202c982e0f00d411824030907125800100503443c00e01d10010040b44001d80018982d04890b20856003090500803c4030060014410b14103444403c3e03020000340c01204805200600a805134500050b44c0e4104040701916a5100b0b91920f800f07507042400401c8140c1c0c0180110400381e2803107102416407610900d500009100c0c0b082c40b809100c081c4080401c060b14002221040f40701d01b41da04100d00e800ba1004190018500f01c0b40c00b8240a4034404031500d1442600038100c960f101c2e007005401d10405a0340c14043c2e030030031051070b0241540c6a013 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 292442437 1250 292441187 292441211
    0xf031124010e0106030e1b03010207170c07051e1c0204020f0c0c03070f0e040230010f14040305071403160201030f0c020733030e16050a05040c030f0f 66
    0x2540b500410309030500700b285540811800d51a0210402000f044440780081c2043c00d0710f084d01140c61641d03002413010800c514403211031745507800c07250081580b8444e03402c0104080c10000100c0101d030344070110180744d8822072010881c054204900c0350301208200d805100041e2a5070010f01002c0100329461611920710b112054a42016a400c00d8030a03440301004210b2501401500000c0d81c2c0e261381009440c1e80d41d8004a40e0003401c0061140300b010214003021a40c0050076591070170100700b54000e00400100d441072030141d9001e505d004912050f00f40108001a0241c1c00901c03103140310380301413000d1040441c641c1f811130b00405c01e1800c076003650519540c11581d140c4205d084d032050101042200c9504503800a50b10260350040717008800c5500c42c00c0036148401803580400c00309621460b1509003500e44024050201c00c1c90440d024030803080d0140018240d2408901610005040354904904d404100805030001071403604c1070540d1250680b00d03065003400352884014248501280c0b0752000e01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 292443687 1250 292442437 292442459
    0x5030103021f05030403052803020903070e090d050a1704060902090a09050c0f040603020301050a09110d0b07080406060510020708120406050912010605030313091401030f03112401 79
    0x1840c54007048242e4406180c01c035000740903290001d8041c0f420640f283c0010003c0c50480010b41c0251034031080040b0054080740e0700d0b07001002d40170415000e4600d0a542c0b601c41180501c0d050f030351b4000e1f50300a0081900c41070700c102c1c080c4c4034207017040c5880f540080810038869210302c41030f1000d40307131240c41d140c1110542c1400716044e9000203400c4070801c5050201d44450703464403100b111540c0308080c56100200c00b5515038211001031500140200241d040056104008243d401400c40d032419600541140c42c0c501680300024558111030300071078030b90302d88108030340c2c58100030021600e5640e02c103400701ea6515120b545011629254008007c0241411050303440c04800030f0680b10610000c102c24043c0507400001c0e10aa0300042c2c1d03601e00040100c20710103014000b690000e5805d071001141c40c0c801c924400300d0200c100c82440d00b00b0040e5011005465449650074040505140d0550300003074002031040a0010342c0c60911805d6902c03140241150025589a114012502c0c540c82c00051100d50070034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 292444937 1250 292443687 292443709
    0x4051c020102120a17040305090307080f1209090a0b061902010c0e0406150e0607300903110d061508030702031e1f140a090b060a210302030f03070503010302 69
    0xf001c07620f801d2007800c0d40000c060b20510550b5240b42211400030504160150301540d0007003400034151842c2c3c07138403804120340d191490540c20035548580d00c040b42808809000b152503c01000d4280302c91607554034a180050300c56100c2150708840b0821022081c15441086107035020056800819840d01902c0010601d01d036501d006849249481010003001000303061004241d01181006400641080009055802040d0001c1e02c40f100c0540d00740c0c44c00c810b100080300351046c40113051454a030134880c1100c03902607500000b062540840d2110300d90f40340000f22100c2043c03143c0340110b01c1700740c8500d42e03800c6480300341e00044903603001203401c2d801c41c07905000e0000d890b10404140c0354000039203107800380e580109001c5034109001000302c500d141186904030346a0b0b03c0815a040003903051511031a0020003103110150385420078880400d540f40382800210f0300f141c18490307115003508000c0c1c4207501010009078003101948001c000314008154150080c40c410b2200303131031b555140e6146005100c085140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 292446043 1106 292444937 292444963
    0x1106011205060a0207120c0203030d090507060e091005010c081e1b1c0e0a031a0603010606110a0602070c05090f1009060819050304051c020102 63
    0x52101502014421030032114107a440f080b4a000301c2c0034500d0000e0800e000c0032035403002c06119940200002e0b0000701582d103894000840b003030454074003032401c03251604000410440c0301c0d00410614460102960141642d01c0c0c00410001d103040140186c505100d1210351a42c14070680e0000d403a00d01a00b0896082100c802038030407880c43e04410700b4000c551000394031054040700046481c1071021540707180902d4600800c04142e40300c0504014140e0070019010300000400d0b2903d021010003200d4600014160a100080c5030a5440e150031050600203902c2c640078000600003480600c0d1034101d4401a01c032010b40c45c042010460a41c4499406100c41043c000741044003040385000d0791b141c0300014101c0d560380c41c1580540f032092103600d010360000052007440308031048900d0441c611403416a450992558001903103461050804004501c200500310115601000880501d8074 = true := by decide +kernel

theorem cover : BRFrame.Cov 292266187 292446043 := by
  have h0 := BRFrame.cov_init 292266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 292266187 ≤ n) (h2 : n < 292446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
