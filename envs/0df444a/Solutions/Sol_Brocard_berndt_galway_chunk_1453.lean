-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1453
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:03:24.140299+00:00
-- url     : https://prove2.me/submissions/100b97d0-cec0-4128-8e07-7c4d9a54de8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 261151079 ≤ n < 261330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 261152329 1250 261151079 261151091
    0x31a040c091e05040203180d0c0c030816050d030b03071a04090207080d0c020717010504111005040e010e040204060803040312081008150103140c0108010b070201020307021507060501060c030c03121d060f0702030301030c09 97
    0x184407007080d060085a4000d0443f052400c2004014000c1e129007401c0901c80e0059940c00112840d8624030080c0081040d020946000d080c290400000d411210043d100700da41880900c450710305500c5569990250780d001050040d180681c042c0781c1000d03840c00c1101e80c0e41010180000940080c01007a15258200c6800858402240c0211010300850307020710801d01e80130b400014042c9980d5280c40c081c600989050290544a0155070f41d04d00c12440001c0490301d101504003016072044010640000c030040070306070819a64403d1604e030004290302001780248290041080040900424a80100e400060320b801c3c2011000688034040c140300700000804002002004c5a10070300c203d68a65500500c0e440102541600360a2581c102070404c031042c1d8904000072480d50b02612030402c0d11541959808115080d070f940031600c1005640007120031640f148a003e440705500320a010740c1903010b40c0140710a14100c242c00c3e9040a024080d041990810030050003ca00803000c00015944681c02c04211 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 261153579 1250 261152329 261152347
    0x170f0402041a0f0906030f01090614060102150406150312030c030b01090614031b03190f06050a05011b0507120209010f060806090c09030d031a040c091e05040203180d0c0c0308 77
    0x40c0547c4072100700565203070003441c008109096100c40750f0700c103000600c0306556480d9001680c1e201f068010344509a212100002c0004080790864156552940c241840595499940d000400c040c40c01500209444420101000307a0610170049008000d1030985030340f500d02000a0504440c142e40148041d1000000810000450a10030703c5810700602440d66481d000125030401d000c00103d6840040c10009081d00303c0b8030034040c06059882c014a1548a0340c980401920b201d0211207041002449203c40c00001c5041130050b40001d2070156070341020803107107104110500b01c05801500a9070300c0d620f02130101a601120041e8407440a46d020049078aa4a24881090040301030303865040c803032461442c2a8503030582120b0614804400000002e0120801304416918043d447d5000244c215408102c0b0310f9030301c0d24003120702c401c0028001c0e003d42c80d10041020790f807017101d441d840b03842c4913540000051410002241c0d4441d0f1031804400051155554900b400514440a44642008156121 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 261154829 1250 261153579 261153583
    0x609040b060f060f03070206061002030309060112030c1b050f04050c0a08090307050f0a06050702010b010c0201030c050904060b0405090705070512090f0d0501050901060b130e07170f0402041a0f090603 88
    0x2404400e540c03504d600ca28105600030b40c1c0f0b1004031091402a510110101d160b14000015280241d540401802d4170b80c0c240328000c4000010300c0001d50030403410100030004074541060000d4040301d80240004200d0401e414045c84401d5510014002c910700701c100304629441c2016140f48118629007044542c1310104550302d94000c1c01c0002d0641d00520320842c2061500042c0130f10103030303c1408144100e6842c510304dc0e08864a540002c0d020415a8000e40010342c0300350b20a0401883d541841801e145000d008541104d5054118028840001500740510703d01086643e030301c10795600e072035803400c1c10960702d46071a2400b0101800c0c0412000c00c8640d60ba46c1c44030505201d0301800b50202101c0130550420301d01800b8203862060055282010100d000e220382e00445004580c2144031140c014036056141f0765400005090f0320400c5000f010f8074200b40200d007413443c0140c1c4d604072404840d0403c0e004100894201200003011001c00b48034140607030f214a0301021010204884802180e9907000c00300e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 261156079 1250 261154829 261154837
    0x30602090a1503020408010c03020909070c24150e040503041a0702040e010207030e01090f170102090d050312010905010e04140a05030c0106140d05031e07050d0c03080609040b060f06 80
    0x1d21607084984003030b58031070352540c0503004030307100440280140f200c50769081d0124401d00728050380041174400040c2180e8040d141401540d88500c01c0f02d4080060401c0700c8840d4101004005401a1114600d4078072400005144004e070000c481040c80381e0500c0d64409071380344a01d12075214175030250307140b40107030140300c000350741400b07030054018440400381d500454000c0d805204200c022900b9501d100700c0c15403051180c082600d0664408034502402c045481c1d06044007942242925902001803903e85e403182c0100300350300b6214000541d191605442028001c050503041902c07e030b85030031300421051250300d90058120390000c0216a0300e0320300585075803d04408941c050300512000902d02e4030003030154850b10440e40080301c40221882d85000700140840c5840380035007550300501c4181d000c0182038014104d2001071040301c47c82c0c0001ca039909420b2070103081e01b03030000c075100d100100d05050b08042101d50002c1c0441d420000c0380307082d40d16204a0b500c054041b600603500e0707080443ca2601c99004907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 261157329 1250 261156079 261156089
    0x20a08030408030117070b030c0705240103120f050304020609060705060c040503010e030f070b06030a170d0509160311030106031709180717060d02180f060604050307030602090a 78
    0x25540349040d007440302c0c1c641e10a104912042c00010603040e64164003241c140207481140062503c1c54580b8143c105150304003400684050060340c040d01200c03070002d15001045040c0b40b01100096145080800f81c8010740c0440c241441803400c083e051196110044a50240d0f048601c00d440301c0e0050b012452501031490000d200b44240e4080c407008010000140040719001c400a00c071040b0306420558884c040c903840c80320010350621481000400c40241c00d5484040501143d060000c0750b1581910070700704510b002c0b100480003808900d0b00340c03240102640450460000c2c4950b8210181c4030303102080c0c610010380f581503803541070039060307600b074110f500159082075203503918080003009682c465000c48030981c805c0b26007181d44128500340c004868480d005c0346e15402a894a40a1640f0084900809d0698001011604600187d958080d1003c0c417043d00d90300385540745081000d4000113100a000188144c01c10b10040001e40d6000500d0410790380c2c0310202580b1a001e04000c50160070180d008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 261158579 1250 261157329 261157343
    0x6080f09061314060709090f060b04180b030d0302030402240702010c060f061413050708150a051003050906011a0d18060c0804060f0203040807060911100c0309081b010c03020a 77
    0x174800c8195002c20b01d481a1000301d0420400c41b02103000ca00100c4034240f01d030030329a10041c80700f0048006d80000c101140c0d0a101004130b08400d074040040c0c2020301d11000300022a41c00b005000c00e5092070b0b5500c1c0c400389004041d0b01214035600c403640481e406407071802810003130040103000403c901604890400c0c4040c8406219241d100c020030343c10f440a1020303144c0140450341e00c8a42851403406058028002c6032208070f0710740c0303e2124031801c880c044402c00da000341c00e000000038a5201c800301c0e0701000d240b03981c0011f091300b007295009040c6103041c0d00400c014140c00c00b640c010401850101c8504d01240341002800010311140996030f201c181501400141c603201d601c60940b031f0400ba020f881944500700400182d41200710080c100c6c002940c02800548040c400500043c54580c046c05080d8000c040c101580344582000444d40070031403260000054480381e001c0101900710f0340702c07400380040b00090207604001d050313568030403203604990740e0400907130399004001d06000b031001428881e0820790b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 261159829 1250 261158579 261158581
    0x5031501030e12040302090c0a0807050a0504050a03080d0507090305190c050a080a03110106030f111c060b0a050108041203180507080c090903120f150402030405060106080f0906131406 81
    0xe20b0010b140c000d84406e0380215001d8000504a00c000c2007100c018501d261241000c41e1503210040f161034000842c0d0505000302000003150039541c00e161308006604c1482d1099035404890098410707070300d015001c0024040101c0c8240001600450103200c05500d1510b6400b640100307003444202150b4590141d03800440b000c001207480c58001c200e200d2202d000f038a48041640320b9601c1582254500c2c48044c0c0a00920581b5500060f9050325480f100000201261071080c0c0300d4803030850107c100c0030100d84035903458203c4201401c041c00604002d040c01d003082d10f22460a80c844d104154202d00e50345d410141c0d00c10300c002d03a001140400d13150082c0c20030210f4180c140c803281c41b40c0e40d400b07450100a01c980d0a10380042c80480d0004115094058060701e0041d003a00c070010304032421440541103400d04050340c103501240740c45500c0035520a40c0603400030f080551600e24081c00d44e41d00908000749102080c0c0c200004075200151540d00b1208a002d5650340c009141029807540c071407080424503c1c05054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 261161079 1250 261159829 261159853
    0x160302030a1103090a0c060921080d0203090a02030601080c130b04200a14042312012d05090601290d0506011e0f05091302040e07110d05031501030e 65
    0x6054100c5030300c01d0292116207502c4801c26160910381d84116514000400c03e0b40714075084090509c50094401c0b922030f400c011065989009076041100e102003140d2182c861042545010401c007401000d560001c0c10752a8000808079100e000400101c1d55440d8a407410318200f600ca41d070042c4c0e404a00d060030940361240d81045001c1d254041700c4800d001655003685260380b100e200088a04403010120780307400b186c3c0111008116281701050040d88440c0c207800c0c03424542420b000f0703042503a010300c14848a240446260500e8170108010101c40c0910340001c10480480010341c15043d2100e504401c00360103070030340b01384d14502c04020140e18640d10120b40410703400c0c1103801c098000e200903210005848140d0f051800022145c03006800050065804c0004542c05540184201710024105440c0449092040010303a84143e10120b10407030700004014070558061040345828000b140a80030b201c600c4400207000d07000103061190309503203c2c0041c1c001c43c5c2c000d5002c1001c0e50460400d036000c0315246 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 261162329 1250 261161079 261161083
    0x3020c0f150a06060f08150307030b010f030302011103040809011404030609060906050f04020609121e0f1b0102120a0c120807030b06070f030c0317010906031109160302030a110309 79
    0x240c2e5031900450074140d020620b103009507518031640c1c500b590f42075180d550361110002c0c4880d10031001074050150312004804103602d11031041c0640310710102405003614500e07000b42141d050b404071a490346418030030f0000107004041141e058010900c1c003201180700c8481c142241d8401c0b80d00013409585000502020880c8641040182c14082c0c00304001e01d0f030711100644a031042c1110029413101c0d040101020368a060a90b04a840740b2034402c0b02d480240748001e01c0f40303c070f811889040d69940410f03180e40241c04104241d1030100386602c00350001201250004c0d6442044200328031024a0109181c2d400c0c07032062051801540d001031051204190f80103000d04900c1003607900c200041c1c00e164482141d030512400f1a000150320070141e03000702c001920101d400080c5402c08404104840509a00ca6180c6082050191a21040010341d06240d451300408152030406600d000c1c410040400c80540b291203c000d14614281c01c0160303807991030070a220010b0091503024504a00007100380300b462800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 261163579 1250 261162329 261162331
    0x1e0301030609020f030109021f0e030604050a02041b1d120102070c0e1003020319051203071706010807020c0904031b0302101a060a0f0903120e01120b030d03020c0f15 73
    0x1c2d110000c130403004200303050aa404546000c1e41080946580c00000320b00d117615002d4101d0f65282c114000380347c00000034240b0b0416034040d12294070120009040d0310307052042084a03084a040c4241020603c40041c00507400410702e6100c001c0d00c0041c1113429258416080300c501d500030002c5580d0030151405103114200350284113004011180080d1103420f07103c00d100c2c160b0340c004008246034060580d1400c040030400070700b00e584d400342c1d800408042d0803060185001d012951503260401002c000c1400082a00412543c1000b680e9000d200149402080c80c00c441c01c001e40380400581d855080c19500c3c80ca0800b240b1f44d0350051203400710700b419030100301c00e4158400d0741c4003401000706904030783c0d1088070842550341d80440f0400581c541c641c00317942c01d250042c219040c0b042900d0341c1d9455040d03480450340c8080010858504808502e9a40055040984c070451032003000783c0c8a0300e101003a65509035041c110145607000915240d50304080000c4025260f1150071142028501120a40c0c0860 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 261164829 1250 261163579 261163583
    0x6040b040609081c050c030106020a0f15090b0121030c060902010e031b040609150b0a0c0203010606080403030b0901030c062f030405130b0f01031a040603030f12060b0703051e0301030609 82
    0x11070300d000b04d03060b46c0314101100c5c1210301030380c0117055612117a01c444504101c40b00c0200d5144007861400c0c102a10b02c0d00808015138010021140c4070740c500b085110702c0480c0c034540138110b140880038400c0082d400c0480c41c0a8542c01c800c0000fa4520300d880140c401c00c030441c00c00caa01d4481c2d001040940034401d0100140c40e00181c2c3c042c410240da8110351010344c0c1c007280340340c2c900c444d907840c1c240090b18a03070340a072818111501e0100202103240d0040307030860b417840d0031100025410600700f20a040c2c040c02041e00031501690108103940c519141c0d99000f00590207036508000b41070100510f03961400400e605210002c0000b15250401c41e250b02c0c0d529402482558000d019078000302c1c00f0a032007031040c6042c2c08800341c8249801c0a080b001100140312140c410701d1580300c0302e901500192103170710030b00d00690b02c03a0301c03004005240424040c04042c00728076100e4035581007920030302490a1740d00c166500300385e040c00d0182d11a0454021040b004c100403003503081100d00400008144042c58114694840c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 261166079 1250 261164829 261164831
    0x3182104060e0a030f0311071a07231002090102160e011d01030b0106030f060306021314030a02030a02040507050c0d0909150e13050106051011070603090506040b040609081c 76
    0x948032800307100640d000c0740320141c1040240702c000401b081c0900d000340c49103a044415210050307150880d001702d0098460074041d07403104c041021001c10207140041003500d80c6c5002e800c1d0341c1d00804c00c1c4180e50b0380303e66500d941d84503401251142c5142d00803c21201b120120903a01107004c1d0311140301d070020001c24843c120b540000c1c0c90302c4d00260107000c01110f0689410414a04090382032480c00e801404664443c0e26640c0e0362514000089081440580185940030030165501c40c640440520100f1512440a2282e001a0304d40c100580e4001208882c055040c0e901092503520901d0580380d500880d08c021800380540760400d20b032103500510707076420b0b26404141000350000422800c10000d9240c0100da00e640c0c05c0c075005c00c00c031159281014070030038800d00000c140a5110400308900d0800d83d01c0b910085003070700403d00c0d0030b00c209015030000b4011502d010002c40c0201c0d01d4040ea101c0024101805440c0010b001c00c0a010094000d07180094006040b80d80d90880003d012040500101d1098035072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 261167329 1250 261166079 261166097
    0x303090601050409020a0603110f0307020f0624011d0d0507090f0b09011202030f101d01230a141302030d0c020901091a0301150501020d090b0318210406 67
    0x6103024071440c5404e0740c01601c0324514030300703019003a0300034032410701d01310340d4520244000300c000031040c8029881041c06078050855540c0c4010843c1c5000000707042042e0012200102c80025500301c002000094800d1070a00000001c103940f07001c0c0c04010304101ca4000715840050f8090010000e2504200c0300380f8001081801209540c0c0b50031030366810f00003135001124600400014610f1030300326240500040941e40d10855038101e0350b2400700d02175411030340f4030b890340d5034080e04035181c078041030307101c0341120090150b0000d2210fa41c0c84a8401b03c2008440328500d0042a09010a5806581081c81c0500400107605240c0e46003003940d400054201c3c420301c1100610391089124800300001c065003d8450403c50b400c0c02200405021144400424200601240415039409000700c018502c50706591001190805000905112000040d101805400c0360f0400120b140c0c0703400c40e688800300600300005c441d03440c2d00060400d05c1c504055520840002c4501c24208080401803040303440c1904e40d4440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 261168579 1250 261167329 261167339
    0x2606040f060e072d0f2408090c060703050c060703061a03010317070c0b0c01092a1802120f0105150a0807050f21012105060408090a050a0b0703030b040e0d030f1d0303090601 76
    0x1f034a0303801c94126640743c201590494090420502600c0c4082c42401c04c0c6080011410005280a80c00c0340c1840009480340d8003041030080c2e103c80041051045901c407490342d03042d516a1b010b0204a450341011090001504606100340d003121f0001601030b4442407942d9a2002c0102ca01805035141c042e602d2a5040c1c1308810010b0406c0c01d91200ca0004800000410380380c00101e2540e03180d10700c92281525000c2002140000c45c4214491103800d4494040034507504140c2403041443c040c0075218042141002540c2c840f03074010184540c81425458081d030395500600014404d8014840140c1014001d6007104511841d6400c1c1141038412590819034076040a491a140c0c88201040140c482d8014102240100b41403500070408444c024140c20405952040440e070b468005a100400940c4c020038000c042503410b00800e012040300310f4080c0180380b0810f1500340c076540b4504880e028140d03036441018030600142c00420310b10b03502d030380c84400d0034104102c0c1c0b64895208642a1031980994000459 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 261169829 1250 261168579 261168587
    0x40905010f0906290d09032007080a0803070309061103150a06050906212d06010e1908030d0b010201061e2606040f060e072d0f24 57
    0x40b281d04e01000c084403071640349403908039541c144110a503400100b2491404c248103000344555680700341d0310301d40e4842e03040c15040c0d040f00129645401d40c2d04005402c006400c0001500030000e90040920382ea80c2c1c03503a1509400a02c6421402001c45040c4060864240d14400240d1b201f015a514404000c002401c01c2100e0300c2054000e039008502d007441410030900300038001d4039050f6468400703060702c031180040740d0b90302c46800c4030046480040300001d41d02014911200c0402590840118055814403100281070615032a1180703010310036002007030030250700740d034103510082920b0411340b0f940340094240003010700728200000340950f0a040c0006803141c115001c24540d42010514030300301c2401c09003003510100c1103c00d520002e034481886a610388a0610034140180e1040074103412060780d9190a0341903d01502c4100030300e411030314017045106448030581c103c0d1090300c0400007000f2041c8060300141c601982101c0600c030040c2c7d0303000c0b4142031715000d24403840f0074907802d000410741c90b404103d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 261171079 1250 261169829 261169841
    0x712110d080406030f06050405090c0111030f04062715110c090a0e0f1902150304020d02010e010c3207031707060f021204060c05120609100308040905010f09 69
    0x2020800d0401040092900c1381e400070781c0010b29408042495551880000c082d560250350a0000341c200a0b1420314540c0c202034034040c4d54a00340055400c00b4130a100e20070300d9000328400c02c0305000c1759440c00040d230f00140d1032030600341e200503c802c051140c8864601ea4500212014800890110400031421030800203828203000c03001803500605607aa0701d40f0002800b907200100040d44616950619911028040c010503001c043c0542c0060b4201d034010040403004007000c0c3c8201113010014400543c0320410314200710364081c01e044440c4c1080070012500c581c10743ca4046d001441e9020a21216201e4500e400c0140e0150f40464003480039640d101c0b030300c41005d407000400041c4056124001c50401c4070203042031500801001548024044002c0b050b82d005002c0300c0c68401820081004100180c417601003200d010b4a0700d06d04211440481c10300c1028050110f5216041800005040079400b40401c0d000e96070120046803a190303074003912409000203000340c0400d4240d04e003000c07070b07040c1d203511410f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 261172329 1250 261171079 261171083
    0xb010f0306080a0807210804021c0506042406090509010c0f17270a060501080601140405130218101208120a09060c110c15070b180712110d 61
    0x182c9040f181503030301c0d00a19801500708a58101038550450040d00701c00350075583c0c2d01640d031202c15161600384108050408106411481c15440141c2e282c0400c0c1c00280c100c3d48240d0141510300400c01825109203200f2404902c3d09526080c081c02007580c4045400090003591680000d1003610318400c4140c40201103801038100040e02001039600e540e41c06070145800c0403c5240d0002904032445103210b01115000c044e0f5119441103a4513020080fa0344201401401c03680050105d650418020705400c0c043c040758184203d07110000305400b0000e1500300b07800603500500083d5003448001d0320b0410401c0840300804520200f4900040c500c41302042140d400d6030215046103820032003810031445402c040c2142c807503140d031034040400080540c0b24a854500007900c03240da095449031802850500d0540f841c0c0c4c01002c08042d140907942056083e110300301e901103c901c07510781d6100907140310310329440815041e40c8154200000e820440802e40c2070366038090000303003403600000c10520a09901c00a00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 261173579 1250 261172329 261172333
    0xb130503090910050a060504170c03030405210a0f1401050c030406180b0f011a090303070f0f06020f03160e0a03061e090803060108010807120201051804020d0b010f030608 75
    0x980807980ca001410190320144070f0604224a07921200840c8004406400c22000300d540090244001510b2100b445034214450340240000c400810120b80c0324004d62261074058246101d004945554041801a54182510403034a0303450803400c0840305d0750081c00d01902c2e41d8030040d0f00140708a6045c000c55206001c220052840e40d2036650380c00d0010840040e00c1c8075007081346120301d800540c0355081903018034610503400119506002541184000580d40d0351810318080048000b181c80200640784141e030440d01c008805181c0d0300788030103120716610006200506c00107caa0b04d29254401460250300324226200454a20310000e6419200c10700d1050340c040c098400070400039040da0003014815400340000c40e032891004034a401650f00a060031202d0b0b480c00710800c080c41d640009100c0c010881040104001c0d494028615000000000040c2c1000b40009500100c090402001010320f00058400c554442e00c1800c803c00420b91207040314000780d10b101142401a22a00410054402c4500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 261174829 1250 261173579 261173587
    0x11031b0714030303090312130b0420010201090209190b0919110711040e010609020a0309020f01090302150d090c0b031504110a1d100206090607020d090b0903010b0406080a0b130503 79
    0x14007420380c0c001070500c820038032391401a00004859840c0b03030307000e1407140000254181441c44000c00c51182d404040341160b1408a240c03025a41c2c0c537103656040640c0382d00c5002c52510b001002e601420081100680000381d0130217002c052080181c0002a00070102010046101c034100e114020348140140a000e4210b66414a09107107411782c02403405600d00000050b5080c0c1e910400c4050360414140e69001c26038500c144810340c103026450402d0703075500f484e001b0b484c2803e55000800410712041c01e550309100100b0400343d40c00c2c659000c4603545401003550080039544050b80d000642c412114059010252203490200c3c0c2403078061000052010070615040016480b0102e0307a1002c4140c2e103040841c485800b40e100c03602c842d0010b0001030065400b0b40980d15140001502c3d18102400810842d40070071034808602c1e42c828030707640c19918031103d450358500680c4002809420390076000c03540b00d854942c0018100200041c5000124428204205980d68031000c40c06401040d0301d0140c21604204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 261176079 1250 261174829 261174847
    0x301051f02010b0a0b120606090102030a050304030e0603040b04050f01110d09020301090b0a0504030912030f030504031e050309010c020a0b01030807150203070201140c03100611031b07140303030903 87
    0x4a03582002942440001012561540001c490308903e500c20f03134030098009018690040070b8480d1079480a01030b01c00e6844c000741c500001750b803441003410040030007c012022a08061107010f8146222500800d0281c40741401c4c04c050040740ba00b540c04551034419a609049100c806006208420030409045030074080c0d03104050014203240c100c101c5c0d1555a441d019400038084007102c2c0d006101d4030b9000141440d080c03401422006e107941102000c0b090010f18030000036032000c0101d0485269140110381074843d841c0030703255242d030440c03598007030381c50100c40042a0780c1c010017452080c04003200910480c0c0c0900801c0e602c900c154000a0420300b030342c800600110b401d070b10080c4941449290024095001e19031080201c0c0c1040c0c0380180180d4441c1d5000f2802c0306180b0300d2039000004c03a42e01c04d10f1814140c8440d21005402d200b4401030190203200001c0c034a0f82401a9040d100c2a40c29235103090700b003803c01a803035001c5c070701516034900e44004901569050001c00d41e4480d02c0080d00461425282d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 261177329 1250 261176079 261176119
    0x31206120b0c030703060e190b0105030c040311010c020607030305041110082e0b0d0f060b1206010e180115050301061d03161203030506030102090a06180e040c0614030105 75
    0x3000305042c107440f074030001049080904c03014410b441e1205183c215408c0340c1100816148000c540c241001001d00c00e001c43d0041d48012501200e40c05409400e1200b903d600588044810050203035100d031011034444185a0180c0003a442680301d04c003c02d0722a5000381c10050b5001c104444880003800001c00941890300611510403010300105811210b400740e6081e5101c0310400c2e40040c0003080002c1000594000240100000c4004000e13050205c542025a8003c0c01d015041d50400d1102d21440820481e9000750000b0070f080001500c6c2d0b02001000c103182201074007080c440c20055030388010100074141c1c41001a24140e8070142c3d100c410790344e122080030590b909108510703a8140030341211113140071580c0c80d036100202112265a29103100a04000c0c0464400522050280e40100034021503a40d420506109440075418442c0442c010211401c280612a8001c880070541d10f01c00d0005000d0548907000c02c80f90140d642136102d80310701202100324042071290300d401c000006015920b030300d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 261178579 1250 261177329 261177331
    0xf0c16030c06063201020a0f06020310050a080318090601020c0d1b171e060c0a09030b180d091202060903030c011a030c0609030705010c080c0a031206120b0c03 70
    0x40e41c000c6182901d0361860001c1903c0c00040e901440480c203a10001e01252815030540b02c58240054540c443c038648903401c0307500d45844003c0aa8ae80000000c0488450071035890107008050041121540c94030744180d529844082c0c94042110f1841c4080401d2a00c070708040d01c42c03c0b040e4080c20b013842204c01448104025560304031480c10b08441800c8845603800c1c100401414019018522541e10306455800c01084030a10203041d4a000c0a9060342c503c0010403075001845413480d280c0e5904140011201220b298000500d0440340070144070040313400703144002000b00070a0980b940b600501406442112a501c1800e0320102110743c91005881c0c171202411406501400341d03132401601c510b4540c210340c035002c4000341c400000809003120741070800c41c400d540e510984403030707140201800019640341c0b068440d150403c0310501020782004130010a0703d042501080448ad0400c49524002d08607407070a28216141900d065000a00b02000d03611400740039400c0090341d02651281c005011503580 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 261179829 1250 261178579 261178583
    0x1518090c1d1f1202070f0308010e090604080d0902210c010519030b1f1d01050a05090603040203030c03120f0a090221010b0a0b070203060705090108070e0315010e0f0c16030c 76
    0x81d0f120241160000600041c9101e51041104007a80a054680a4082c08040c0c00c0100011004020070003000e20009409030056045007607240c68507a80c81c0d04c0b101030100690020341226502141e142260700c4074140c500d51700f0b0400c0c15600c03034011202c01107a15004680e0b103c003154106d030380c0c28910705010f9030116105074006003007032140c0d103044161500c0003003d01c10048001009482c003e00b2030343c0303a070000d054000d1091030403601d096000c1200900b10300840000510503e0004003050840d5810030884000080c400c003580c1d00e920038030843c0405030f901122403c0409103150001002ea0816100d0b240751240d00a0803164018013000c1030b19114441281041c445660f104120441750759010300c03440042c502c40c41015aa980c0d80d2061504145000d807034201842800d00001d029a030f00900615030118180c42d14240c1803544d440020718002c0030346014518000f00c41d001144951240001500c50710800040f42190740710720f4484480c81c8034510b4041110b00d003181c829000070340b0626500d20424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 261181079 1250 261179829 261179837
    0xa0c050a060905030a08180325061e06050301110304080306120f1e03070c060819020a08160801051003090f06020d0203060a14010503011518090c1d1f 66
    0x1081d40c40108842c05604191001c1c1d00c04100d80e5420f90b8409012580540850380004248800c01500c541d240280030040c40c1c0c0030841d030130a1200c082c01ca0b8660807025041030080c0500a4009011007100c40c4c40d400001006040c402c02040508050240349400c0e8102000c0c6442d550f116182c0200c1c9410142c1010380c0414102c00b0404140e9042102c0c2c2840502000645500c914406d140348070035900074604484c41e0000e0101c000441c810f104140221102414040c80300d40d104134184188050349948101207910108800c0c501c298424001032203441d244803a2107062081550950382d5000901c2003c0d48080d0421061107454825000340300328038840c10b005006000319959074402c1e40c1101d82007880c659070101c20400b0f0781c6031010925004080e0801d10140342088400001e08502c814011021020711020000c01040d01c1410444203138034030510b004180c02d07203c8018401401004480300d00060170402c00c4858032604000742c1c1d02c507000042083c8045900c401c03031a40802525a0594140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 261182329 1250 261181079 261181093
    0x31806020f06190b1207140a0b0706090f0f060501050907020105150f1306082b090306020f0d0914060a0b010203030103171204031106130201020c0f040608120d0f0b01050a0c05 77
    0x241ca800304000340c0c102117500075208083c10820340280351200841c07034601c40d610354035081107040e605000f00d0f01210f4100f2004038140c1c15a08000307031411140040108800c0c4515135200900400d54400307416120300325030401041e04c41d88400c0303081e2882581e91003405115034218016519007001b48c861018400341076190320820314256582181c0f060b0b402508142c0003055124840700188a5155680d15803414070190f40b55414002486d418132400010100d542c0020090501802d540035209003610001080c040c0d9809031400c0e00b0700682c031b2080d030340c014861140414008951401203442d05007041c1d00550445c0c1c60343d2200454204411035001015000300b000701c04d0000d195020341e03c5a80207031074450035034022400c0e4030314102c0000d00000d4120794100c1d041005070b0380400c24a0000c0012944000758440200c00076008201c5540318954900c2071640350441004e42201034403522032102800c001d1101c280c41b040c0c1c265883c01002c24001034003003000c002a180034150020646021f50704840032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 261183579 1250 261182329 261182351
    0xe0f0c030906163b030d08010e04020604051c02090601031a09041b06050406021501061202130e150405150d020904050f0a0602091f20120304031806020f0619 69
    0x103030444c0038110340712401c11401000051800d04100b050f80c1c50742a80140b021443c04080200b103160103000701d200d03200d140004641955100c0042d50040c0c840181000780c1c1401280300c0000356954124101d004290490004d9015030083c0319407800d0080031184542405248410400340c154014400c45254501d09110b05404400d070811001402c05925542c3c2e641e410184040e01e000024141c5207001500300c170051000c7c56000f44a403c03450100e681c05a02c030808400ea040c440f006c039401203800e1001881c2004280c0c0340520788c0000310318090324100102e0300e5000034081c1011428a10641001301040003000504080c4040342c0e020740510280d40300c2c03c024811980c00d110041300291001500805d90540c2d602e80395001901032484a800240031280092008e1301c074a130a40107582c45a1113118440c8a210420301c0b10341c0d079541c001c00c0416a603241603c0e0242c1920850401e10004613405180800e1445c00000c40d2450b0b90702c41d10041511381e90310044200c0300e0302e44200103181c02d6207402d00c03041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 261184829 1250 261183579 261183617
    0x6040b1e1605070b07030e040c030b0d0305040611060103021e011e170708072a05070e100510320a0c05060c0a0507080702010314010e0f0c03090616 65
    0x31401070340400d45420700041c1030803407a00d00d0580240300c5154040002c240000c1c1c011907011450401501c2c0418000f0f5402002e138000c0c00043e0040d900701c2c0281841030101513004005106440711a00c501144507506c3d010305a4900d42400029040611000c82000d425105a814007010f401403420542d45240c9038881154090240380c00c0000c00c050b81e4101d500311040340d409950059891418603201c1c501150000d10024108881e001900084d4454443d148401e0550034841c41d041412290354030303130f00c20851015001c12514a1442c407100030300450b5034680001d41054140d01d41d641d4450070380001d02c14403803401031100c2001030a1080451140200c1070880070703000c070340900c3e02c40c6400300d003a07810030b03070b0610f11300514119210004101190100e50818217552070a9040080b0944611503480141c00612144d20031400d40710341c001c0002140300d00c0026081c0716582500700c0700b20342c0c0c640d04686842c40c08183e40445031500a407000038000d480844a0b0000e0074403919080742103901e401c3c6988 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 261186079 1250 261184829 261184837
    0x311090415052d06120609040303020c0102040b0c0c0402091005030c04050409140c0109061205091015090c0806090406020702040914010207050c12060403080a061e051e06040b1e 78
    0x210700f00746840110094801100741507002c003503080d0b801c00d2070400444191a55028014422441801c1c08404141810321a80c10f0741e1990b08840e00842d511911444280310a411001c0b0750a844e10402c4903080840c1028000d030380000c040900060800d0704421819200340c0c01c002d00d401840c0c40d09000004942d82c0e103000302200d090040b604001c0808880301d0322414003c0500c7e0380c606102d40407004118843d446041840c14000e010400a210b40312101e0303184c14030303610607420400d032070408103600c2c20022020406030840b160740c00108000b41802405544641040364065800700d9881f0004002c0f0f641a001850184d100800c00540d00080d0740c0d412800c0d003468802a600f9a60104182c0100003040203280c20456044616541e042059424241c0d60301000304001d08200e006804102c4910680e0803e0340500000446819201034000241200200d188900751181c2502d16488481c0b40f1412060350020802030492450039040060000e19030344946000c10001d4180d026100d000141c400c058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 261187329 1250 261186079 261186109
    0xf0301090302030f0c1f02090906030c060301352401050609011d04050a150f0302030d11120d0c0e01080601090303080c0403020a0f0503010606181a040503010f060510031109041505 79
    0x503110603003441070050300b0270024079141c00b03a0b0018540352501d90b03036401544c2c116038007420f40d0104008080155442030323084c2ca440b1008510f07162140100c025020501d5042d11525414841d941801c540c1100400a02803040e40c2e00302130b003085500d086c4e511403034010345c000c0310b0000c040c03203040c0c0301402060883d602190107146007907684070140c41100d9000c1c40d07800205001611911481d05540002e030f1030700d54003880c680038092110928140402c042c410200311032590700c1c0d0b054507201034815610180c07400c00034a80c0010f4100b020f5004540c014103000e409610182d45150310b00f42969000d941c100c4015007003040c0208103110010043e84d5250128010b0b152201b00c44403010320300014507080d80c1c402d0b000001403003003881c204400d01c0000c4660f0421119210b406a031001e856000021003803040350800da8042d401c1411800621a40d600602d00f00c80c03042d241c0d1944902e0340d800403412645050380340d42d092101040410754901e40380e08205500000010150191559900042c40e802103000103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 261188579 1250 261187329 261187331
    0x1503291b0f0a020c0a090e0c0904050c0d08030a200703180f0f0e010e011a0a120203040308090d11070e0c04091d0114040b06060a0c0501020301140f0301090302030f0c1f 74
    0x100032650605017101401445041818050603a0107552a03403901443d8000b1801410003000090034881700f0807507902c0c07480300a80041c0e1100d8070342c14415219031044600c1d0304d24a0610b200c5200542907a102c240c0d0001c0c0310002103041640650341103800040a242031038080f2200c880201d80c0041c641c00100042840c1e032041410645004c0b02103080c034005901061442c21150010450550340400c1c104044801f071080650761020500f041d20a0f900d034180005040780301200700010503810030509801904030034100c1e805008505000c81c1c1550402d0006249500201810041032000180650b000125946e03a28102034a41004004442201210011004403042464111030702841b410300400c09400100149180036142c1441004014225a00038030300028040c0d41544518000d00340c096100c402035541e960745148031502c0b0300c208c0d110745220302e1903ca15003207207241c14400c0c8490550305801440c144041a800031400d0782003829411061300508105540403d0810302d1a40c0316000340714 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 261189829 1250 261188579 261188593
    0x80d0903030c03121a12071a0d0e060403030b0f0306010510030b0315090102070c0b0306060702011407020a0305010501180e070608090a14060f06061303060b040f1503291b0f0a02 78
    0x301b1a071507007952504022a08524070900001842e03000d1480c24858104509554a0f10200d19400620b1003800d0360200740110418001095410381120404140c2228140441e0021b94201602d4076020300c80e5690000c0c0c56060a00064082d41091040c143c004003900c60f00c200b00026004140412503001409943c0041d59508119001110034060f10b42c00c242c03641103107001c1d400b060342c910030703610007038180301d408024000003c02c400204d0b601c00b42d0141c07038030515a0b56442c2036400b81ca820f016140d00d62a282c14884112080c0380304154603042008010240640ba1440c00d852660307000d00f0840f500c0c000c1c501786401050411500182d107580b00c01c000c040c10300d451202000f4030b42000c0e040500ca034504011400b4803000303001940d426280c0055000485600385800200209100d5901040050030545009101d2121503032407000c9a0141b80007040c00140781d807130040441d04504580b03440708450000318821501140d07080c420304e444150550328109240b2024032032500484014001640101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 261191079 1250 261189829 261189881
    0x5011d0901080d020d091203080411060711010f020c0f2e020312010f080d1812060e010506011b080306041d0a02010e012a020f0a180501080d0903030c0312 68
    0x40b01017600316840c605001498107008058281e40c0c0d082c10701600700071041005c1000c2c04110485c40000078001418150340303000398540600746100f00d15a040c0451400e084440ea030f44d0011510321a0b0160081c00c208418101d0300401c01c00000503007040000d01c42e101400c0b4818003d0300c0c0e12101000d440e80048d611003c07042409518500140c00551515002c400100034a8500180304400c050b40e9081040500700c210090048001999111240c030031021640c0308188050b036489441c80110110090003990794400042d65024003030a40072021002d1041040d000c114900055504010000e101103254071180c20280740060180c62200340b00c0d00242c410604541e04512050400682802c1162858000301004600310741c005a0068100205002010456995000d003544401e001449048003030345032440590803000c03652444d180949040b00101e201c080c00030700c002c0a0609581e8003d281810b42c0d40031125804074010407014040c45413848561558940a600100d842151191003886020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 261192329 1250 261191079 261191083
    0x1204030f050d020a021f112409010b03070506130509040b0108060f04050c0f010903050a05070602060a02070506041e050a0b060f0d0b0f1e0f04060b06090a05011d0901080d02 76
    0x2c081040103560184815500503102c4428540242d007010106c44180c00410343c080d0794103c1d200d038031a05980030303808600700d0070750700525030307078034105622401d03000c56610142003508039141c18645951683c010b000401152a1680050003109011040f20144a50312004500182e40c161011140d0390001001400180000c1007441d50050303040c00c0407070300c0d802d1503100d6907190b001c814070701c5000d03801a070415540c1c0c1c2d0084280700b00031548441110495065810300580fa4030190060800500070340001c200d844032940241c950150300040640550340b00c0f6551518006d40c07006444004201e80b00b100ad02040e42072000003002d5001d00400c201c28540f4070108a0343c002094640d5220348132481450020400c05d040d0a41e06c45000c142440d856202d41405440000c903010201c422106128104804140d00b042d070f00b4000d610034141071000d09200410000d490113020906604500ea4400c10481c661040260100c050740b180c010042101c0b4100100704401000d80000d02c040c2d0104c466484072030740c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 261193579 1250 261192329 261192343
    0x12111f0c08100509092e0c0207081203061f020c01030b12070902160f030c1b0605030f04030513030804050a0506040b041403030d1406040e030309100e1204030f05 71
    0x403900e0910014a4074441c442e40007030460182d20300913405440003074441d074000c1003942c920003042c148440200700481303808250021000c9505603030a041000e814206030000418606681e141d20240c18410181a119145500000c143d20742c85100c180c82080100c015200c05000c5a0850b8040d12982c04001c001400745c5e44401403460144c4e400b0a10a07900c0403021511005507103d250300980e4509040324045561410100044c003d40300c200a42810950042094282240328004600038005546107860f6242d149110b29004901c2c108000b5000715007100c003203684a446810403600380405100c01010b0713085950812103880400040900441c501100300c14000d03c4200e038030340d241504007580981ca501846c407135072700400721490782251243da06205581010b1a111410400040e403103503d600b4404041e1840e501440c50072920811903071010007120300c1040c0403402841d5090a12541078000c01c0d100c030000c00e072400b40000c0c1c9002c0c05405401040154001c120305603409110b07003000c90400390 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 261194829 1250 261193579 261193601
    0x1c060e03040f121106030907030c0905150d1b09060609080a1e03030605040f061701050403020d0e01050403140a020325031104020712120b090105060712111f 69
    0x20041c0410482c0b55a07100020080d41e403a0300040d0200c803014500a10300c0042d000641e0381c480c402004001c0540d00c0018071100301ca0040303204601040d624980d12007205c0040d01c20000d13800f91042c16004a0404030a0b8000e400e1061000c000350075020520f0585540303c94000d42901502c0350b400300003c90b44101080081c040ca54064803898503240d50307900b0031401c40c2181e814150510b0b1000c40516010341d00c4100101000780051013002803440001c0b0007000d03180540303a080c01010441010030f010512079176100720f500d82c008281c00003070600180c50508095080d541000420040800011f81c1806c854801c3d807002c800615050080e80704050404804154850041000b07480350502c1480010b01c1a04503500000c070020b440715038501180191041c0480945103003030030342d00320300075a03884038a0000305204003e04102c030b540700342c040109058082c45065070000090080f000860420b81d00d6015140290900e55103032071028010718201508020404041072000d011904c0364401d5009640c0345003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 261196079 1250 261194829 261194833
    0x908010b030601081e1608060a1a030c01230c0c0307080d0e040b01170915010b070302030f030709050a0b34030e03010f091407050102030a1202181c060e 67
    0x58180044c181c0e4403140c6000904c0300008984842240c0d21707040c0010900c4500c424040b124840d118071000780e64076000d0b900144140d150003950400d00c139005007450380181008000c3e042032031001e8011140140800c0f8442d00709610000300c52111580b01d001070111030030400c003402110800c04101400d0040341c0e407000c00f040d088001c070400802da08c2000c40c526460101c400007010440c00e030040702e501c20381007854000c132000320341802041440020040010510758000440680c4c80710300151070350003000b000401681c000e1000c00c815644550185078044624900303802200d94072000500f601c040359124249040d00000c40e20a421034180040314800a000c9140401940419240f14003a840701c00103000c000b483d0345003245c566401c0d0043c2c04156200d800500802141d402e00c13041c0c841c2409a11406032050340c800041550010082c0c80d001102600d43c030000001000ba560069404603a8a00100c42c08060106191b0345110b48880d4900900f001403003d03600b41e24100c0201c5400b170303000c1c070f40701e03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 261197329 1250 261196079 261196081
    0xf13060905010e061008070509092a091302070f0209040807031404050a030308090106090608030405010306080a0b010b030a1119030e060402090703020a1404061e1809110d0c0908010b0306 82
    0x5845d4000d4907020300e40c20b131801c1c0c100b82d82c401400711036600418403126440b00c1a0003c4c848007070f0071020801480014054640e013611603c9500c45014444d0703504260704688c5190310346040d541d02e503000c1c00c14240542299142d00000b50300103040c1e807400715800ca8116001155030700606500405042d0031003900d0700740c01d161508140001e15000c502d03200c0181003000703000000b0720000b401e41080b001400f10f5001404055155a0030940f82c3c0c1040c0205800603140142c00200ca100c0065080c1416811456925069091001d0a02c05030300c000c28018020f03444550141c40c1e099607074010540a10301206000035085000303402400c0d0b4105054150960b030000707041c400580da40005903a080450303400c00503510002c446041d140c00009210070180d0700070100d40024a40e40200c04506030001484203100012003014007030342c450441c9015841206100d4000b4090310b00c1c40e0b032008100f0f5445024413030825012104510a1350803a000d80c10018207001c5007042000c1d401d004031402070304101d0150040f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 261198579 1250 261197329 261197341
    0x6050a0f030506150a17010305010b010e010212091207030506010e011409190c030b0405251407030c0f05060a0f060803041409070c05030a081f0b07020409020f13060905010e 76
    0x1c1c640c200e0110320300700040d0318040d286c01855041e4400c513405484800381c0d0307541c0c2402c500070002218601d0200b94203075201c14a661000c5408001024060001400c0222890920102c0301c03c9130a100303140c0c440c6803000302c0031880c100031941c003c0c210121301c04d1a540c1454000e665030700c850481d640c003030b07024441848000310340201400145400800000741d41024031804501500006521582240c5031a042c01a20561f0311070101468100c0c130900c1840c2c100c050411203250000070000701810320705020003000240716000c00140240031f02c446c8644405aa02d4490070244140c4030802002c0e0740c0e030358000205000e03000d213000401d0480040d42c14103161510201c40c202c00303500c1031403088607070701f0010782c0b458001d0900d00080c0750410200c0f52141e42d10b003005800d000c030546042c51401508108102d16a1b007281c820001d488a50140a08181e20b5909210103019800412644080f0b0201c954202d5254080a03001080b042c03600403c4c220704d040c15000882d0030680041990108030010008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 261199829 1250 261198579 261198589
    0x302070f02010c0201050d11030a050906100b090307032411090f0909030706050112031803031418060307090f1202060909090109050d09091b091413020406050a0f030506 74
    0xc4032030702820a001004514401242c5a06c80d03001414070b003d00c1d00340d044a035420004043c607c2034410000401094580340c140b0303550b540085410200c8040000d90a0228140d40b0000d0080940040c046624135500c903601c0b0500740d6548030b043d007035800c18290f030718003003040340d00a0700c010f81702004032035180440407404039000305030300c030280c50050558402089040004104950445402201c104502c0d61298400442030410110907400514907503604039440a10302208021260b068075035102400400c0441070154101c1030002400070b101c0a00ca545a4980b4001184200b038540d80740c4290a04007142d001c07001046801c07242d890043c603600c050060f11150300b1600f0621040780c0020041d81c4801e13406014202059000301a406458102d50916410508403001d6407070b00d070803d0004c103081e950000c00c00070000541c0741c0013a0100c9010801c3c01e82a4001b50001e24003e07091800007070b445805401039030b005c3ea0107000050780004a12005a900540c402c28091881c0707030600c114148000020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 261201079 1250 261199829 261199853
    0x50907050105070309090504060c1d0603010608130f0c05011211090609130c030f05061c06020c012705120304050a0b060d021e010206060402070b040f020a080a05030d0c030207 77
    0x1030706004002035480c00741402110b0800003060740131400c0c80b141c43c10746403100161000b640d403a00403c0300e0811503d502c19904070416609040a00014110780c42d00808503082c4801401c10b1216034407090309280401e00350104c0d9a0030a008214000c51240341c4400140615044007003c854141742128201c0d42e0f40d10030080300c02a03c012203480c4e4852008500048084884500d060080d902d843c03017801a654145d04580c0d9440f480907400c0145035100b01c240700300c17080500e217030011200c0400d031200000362079079020346854140400001030402c0341c544004224008103111018481c810750501c2d041000402c04803440c040030181460175400c213075031034940d01c0307201401c01010944071200040d4591900d0442c0790340b45030000d0410206240084030f20112022034074074280180a400000750003414140216669641e01c1480c480c40341e95035032900041d400d0194170483e405900290b0019455204002d00d854040c0030324042c55030f495014508100b2110041d100c0414540103000c2070021405009400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 261202329 1250 261201079 261201089
    0x610050328080306031e0a05070906080604150b060d0b2403010e040614070c050601050a0b18130e061e010b04091a040f0c0e1207170a050d030e10050907 67
    0x1840d00d0780c613800002410003500801d036540180d4042d51000c038100d00024503003a464022400c0e11a6241c03592480b1098603000c0c0129035041c3e1000c00031030006001d0000210665000500001d40c0285d030000041c0c0d00e61000320f00690702e5840b04001801841c21045001d43c001051914214002511312a056103001c1446442d0025103840c0c0010140501c030b41110200700e030010904e60040c6001400035061660446054940e0b11480d000800c540c240000d0f0001030700c0c60350b6005418444101c1c11044030076094401c840d040310000303403110260040b174014400d02d1404680981403a19124401ca0141007005403200710b82d02183e4010003c0001038402c0702d0070303241101004181e00c03c4d02038404456800d002e54054025207454109000c0d060b80e036002403980ca145a80b14610280180100000c0b0301d0748050ba444943c0040314200100503200602e49007122a0805960010401351199801d0031050808000401c1d2a58151841504203100c1c443e10741d00e465100300b11608000c400f9980e00c10b154014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 261203579 1250 261202329 261202343
    0x70804021e0d0b0403201009021f030e0f0a0b040305090301090237050609061c020d0605010f0f1e12060b2203081204140610050328 58
    0x4002441c40408250414040001d001014540018508030306984411038056000441807224050303540b403503200c03c0260040c1c09008141e11116001a030000b806c82d00c9040303a01a070644d1004080c50728865850500c03031819140064000040e6000c3e500b0400d1b0300c02800780c55084400445c0019403a1a1010f400c984c1514110382c4442004000c81c0c01400203c6000c2c1d4441b18118260100160007010a000203a04105402c01c0c0350f101c1c00c41d9141d8258a0241039840340b418040030180d410100041c101d244c03410382c9907003c221800300424080742c0c00889001a102e407504400e00841d6004000e800443c0e81c2450020700040c40b03134000404e41c070448a120281500c2c20314641088912425415030b103840b940908200c05a5150386003c1140d00c08048014400070004280184030402908501201d07003101000e858000703c4030f088104468018000c4404407401803410318031040402045100e0265481455211030500041500e09440ca44c0c21004c0e14000000d15450f10746418459110342e648810 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 261204829 1250 261203579 261203599
    0x211c09060c0b040b1b0c0a031209152d0b032815020c030d1b05030603062806150206010e0603030403020409140d1d0108040317061f03020702011707080402 68
    0x40e1509418201c980401700717010010591603202c034004265076000e00e00c251580407070006817003c5030068a1a180014001d44002141e42e0301c80c504070303000710100c11045040240303d010609000c140440c0e03804030411449503a0f4460350795901f0308200c4030508003007481d40341c0c110341c814602c40316590700100701c02040310814440f0140094080e406464004040800350303901d4090354409100204140e03040500c0000600d82c40c0740000c0d0040045a000c1e40c00600070706480e80d13070050040b07240d82d100074245400448480718404184828800c801c0608046503c0d04007401d1450b4000303182c0b500607000703001340c00c030980148000780d42d000040b501142e505403400b1a129050b420103141c0000c500c10740441600680c0c0e440d812641e40a9001031800182400480e10404480011030790920300f2280180414025198070b0322003e0700185103035200381c00500e031440a001080b18140c52403d5102500013090b00403070f28800319a0411b03d45640301d8250305030342c00c0d280344c41e0b5001803001b0805031003c0c0c05a000c2c0c01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 261206079 1250 261204829 261204841
    0x30b090a1a1003022a0a2904030815010908031e0708040f031401020309070608190e100c020c030c0402091c0b07030c021b211c09060c0b040b 62
    0x14804162140c4020060190080507070009400f17507000c0503210011100080e07881000390585007000e002c03040307090002e0104070403664074041e0485954141d18481d0b00e5070a59507402444142e25140308078400c2d503a480d4541059190184030540d0b00c3d4545051100465083c880d803540001a50b0740000401071b01c1030180b000c4a141d0043c2e2040c4140500034080014011500c080c000e00030f00b04403032041c410803d01c2000c13084290300301e00094610308000d80003090100200343c071801c11990409002042c42d05020001c1454a0458401000c503004c1a0401206c114021003544100d6102e14501e00150030441008070010b615080d01040c214821540422031201c40e44600514a220380c030301070411004c0891a0601d801d024100315860300000382002036100c40981b021031500b03014015821180e4541713a904003000340340900d0b403800c25000001e01d2840300301c912040248611070309040b207004e408520f10140c024080303140d42d0001d4040c003001110b1400003910008000e0741c003030341290600109032580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 261207329 1250 261206079 261206111
    0x30b0f01121d0601030818060307080606030601030e1507020d0f0503041b030c09060510050f03040b060f1c0b010801020c071a040e0106180e1005010c110907050316030b090a 76
    0x2400542e449101e220004001c00c140d12005061031440100c40c07150003602d074070401c0b0451100f01c400c8000117081e600402c9250405002854002c401410042124142c0105552604055040d17420400d00401c0c24801e80c10380502060110004500d0b003007100c6d0042950261280c800980020701e000100e0107902e4521510101c942d0245034081e512407103150f5182e00a1020308554003425200321600b00c50100418013074000c0398003110f0b54880650442c1e8076a20b4080001ca4005c2c0001d4001120760b103030242540e1000790100da41131b15103030b444010350310b1030505092140e0140c00200d5140e1040000c004030550002d240c2c401c5503903e06441030300103d01c402141d024082c030351040300c031000e0030800860800d80003c4104098140c074a1b00000c8070f50380d8000001d001da070075620942d08982c4800c0a01c46540302c2c10000526034013a80d031000e296403507400850100002180d1000c001003010041c0208135002c2c21640030740d4800c0d03143c20f2201078001d0f40022031881c4080d11000c1c07400c0e55401100050a06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 261208579 1250 261207329 261207371
    0xe060702030a1209170604111e060d0905120c030301121410021b0111041421010903020d03091109060d06050703021e04231c12030b0f0112 61
    0x404800d0f0300c0e60b030810710805050240c081c011402c0c030101c0e01c82c00312031014000810368407460300400b4007485c10941005001c41c40d048144940000c803132421240d50191078000082c4031660011100007528a41c60402da810146035000d01020309204201c982a1260000305a80c103547c112200e0000b801c4892401d450688002003030100e017802104001503c0fa05184e018090b410100e174804400a801c012599080b00c4070040801c51460b002e10091100b001140c0c3d80034154180a051404245e246036075402ca1120401c83d070060a039119080c80b001c06034144281c42d42d0b0400c40c1403d00c94410155104440500c0020816010f2140b810006010759214030000114540290040100d414105070050296002040040c1164001d1940d548440c052008035030071500c2101c0c845e5511011036280d00182000700c0031083d840b0001c010715507404000f0780c5203541070501c034261000c00d510341c852000d000d8031044040c661007402c0d07121006080743d800440c2c4070004448118000f0301c0412080c0da0040b6006c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 261209829 1250 261208579 261208583
    0x1201804141b07060f02040e0c03090d0e01020a05010608010b01140301032013140f06010903030512040204150801022107020c100207080a08040801110a050d020706180803040b06030c010e060702030a 87
    0x81080d60700030a00617903900500584003510600d60f0300e030ba11541d5211180c0310a64104e42a0b611401d29101000d01c2110f039402c0301c0c607051043e00c2c00100310740c948a0a4598503080140665500c0160368039541e00210309107e4000b002c07112034227541c90340c3c0786c0e941142040c00309000c903007071404518155a6208860344458407001001085880c40089098801d40030881e0352202c1c07000f034100407600542c0594100400c0329415511706d4940300d001034001001d0000036008076082038483d04800c408060400e0200081d2402c40700040e00e4807040c56420b4244e0418146404102c02c1610034080340b50744c00300c0c40b0048610143c0300480c0c15000c0306d1049160400703513030010080e07003d52140742d42001400070050003110703005002440300840341403040d1240e21a583c94000801d0007081000440c264580140032058003a940014465411984000800c0712007581207510680001c200000c02c410403000b1600014164020310410b8141c8002a141d80320700410b0b03501c180c0000c51040115034041181100340ca03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 261211079 1250 261209829 261209831
    0x5040b0304050c120f0a020f0f0a180b0a0506030604180501110703030f15050d08070c120204151404020f090a0b070c060c030e1201201804141b0706 65
    0x201c0c06090158030b8980b980e049510980140c135100d001004002001c01424054a001c1c1c02540c1d4940c3c20840c010106041a0307403c084a03903a0086540c2d01c0402501c014100740105800f951210721001040300c0f8081c1d242441000724400c00d0115865190941340d0100c1d0903180080c0c04040c521601e41141d1b00908018182d608040c048050058448082d10b8030768071070b031020720840414103000400c2d10000f2031840500b42c0040c0042250b880c100b914183d415000f510101d1820f00355890307148003a11190884500140d801d4144001c6003801d00c81c1442516032503100d0032a05007040d101018102a445141c1d110341d4010424058142008040b1100c80c8001042c070049181c0d1030102e149a508240f1b000c0e130b100700280200282d01d07030240d219109090390550fa5540c0200c13906040011105c140c404400580d9680d044040700d10540f07010803201b1300c2c02c500e031003a00d4008003c00b034182350078949181c40c0103c0c103000d0f600800010904c10690058443c400381c81e40c1c040302c181480c0c0305010345d10003d040d071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 261212329 1250 261211079 261211081
    0x30c171e090a0b07020306041106070c06030504030806040c021e0f03120612030c030706020304081210050306150a170a0506010f03330b0a08101b091d040305040b03 72
    0x10a04040c0105000c5205070342080311280e4a0800019a0180a8000c0d400d81c020070000f900056101c40c518808400041c08103051031304a46070802500c0d082e070416404a80d8071000d00c014107401103030700c43c2e001404440c2400200502c080c000d444c2c44006040405080040500e01030710107040c0043d2003210a42c10031030361203a030052001c40404405980703841c000c003404dc02c9040c141c600032040382e4044149000551401c8226600c0070700950000740181c2d82404140200c4034003e800c201d43e03a028200325920740e00c11a00344405c040c1404005007a522030b000e540031484a142e100c50201000312910071403a0038002d00055059800c1c1101d0003801440c90141e1800494000c86844d5039005407401003502c1014401c06d03180c1d4526203905420000d500c000808a0703c401e07008540c01084589001910b54500c99a40d5600daa1030000c6140b0802c01d003e07200e0345101e1019241d00c18030b03a41c1159926102c1c00d458a8409400386103a07940d100da80e4494008000242810f0080b400c0358018031030120134550b2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 261213579 1250 261212329 261212377
    0x9011a180111101d0c010807050702060706052a03011a0d060915080f0c0108060d050106030b072105070c0206070303110f0a0e010206010e0105300d0f050403030c17 72
    0x180b070011401301142d0142c1d8600940c0080000d8026040380040e100c918071602c0e01071069901d03400c02d4900320782c02801088924000745c01401207901402a8a001d07a100c40761042042104010b40c0c45900076850080c0010444c03681e110030b180166460080c030940d640d800b43c9001d8406030840703800000940b800c04501c200e1081041401c98102c400b000241c401001c813040c180d43d203401118012074001542d20700481d07060310f0040b501c0d40106100c1c1d800016a10340da50384044080a007140c6202c0820710464000704440e109043d00880f18401010070007442ca440500030b4590740301003d0203409000003080402c02c05020380e011020080c0c50300d002c641c841180500c50080c0340d000c0700480e07002804404c03008009500010b07009068440300910104560300307040512500500295250740d5602e414451040d001c00411140c2000741c2d00700001d400040d030345240140c17175110484030075420000104003c00c0400d034003491046125034054038100400f02c0c1c50001c40001d0245500e00210900d1510321582 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 261214829 1250 261213579 261213581
    0xe031617130e070f020705010e01030f0504060510081518031b070513051005120115120b060904050606010e01200703150e030f0903031b01060509011a18011110 70
    0x1044500031800e01001e583c8180d8211284100000e1000145c4c0c03205405202540c000d40e25060700c0001850300180103a10b84d40d030441518000d94003520160713a0381e000c1c003c824469000d9074003e801008010004d10240c1402041447c030024020300d580d10051007a90300c0f040c0240121001d03111011008a110107144281d0f64441d4114801c0501c256181c0080d644044420300a20744508403d0120201c1d10303103001c00b03024510b42e40108208480d540d03642048442c4819501c450042c1c039070440301d003074002140d1900141e18440036144a206140641c2040000f800008404d07601c00030030702e00091079400e074030011780e40c240550051081c9040da80c03030000101d400004014048038000d241d40680d800303411100008030303180111405400c2c0c20402c0070014a0000300020328041e034000c1d04481c94010892200c28030185401e03044002c80e5100c101c10000d503d84401c0450141a900d00340e24000507105080039898456a10501100002e000b250161a801030104000b81c83d42001555201c00070502600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 261216079 1250 261214829 261214867
    0x518030c0304081506010828020412020f04051909020402040f06050d0c1e03110c0f070305240a05060a0302030f010e0120120912070c0e0a0e031617 65
    0x50f203032144c941e03002c41003169801014000c00c0180c4452915848681000300d40000100251181c0c40e004000103006502520081c40107007000d00c282481e0a0180c4100f003049114001050f10690600080c0711401600030381c180641d80c0210400110341c107051010402034042c60340500d01007001c050001813050782160062100031628002001511004074050304d2103d15071103040d411200b168440e500c00390003503015244c84041c0403441c904210700c110380c0308d1602c40c1a003400b076000d4108a10800c00c01070104051150446040d104524100300e1a03458000d02c88002c007603051940e10794000c07812a403505c12002c4d02968015040c0c0c0c800701e0a0842d0759000c2c0a0042d11180c5030340c030706038840613084208008015442112145180740c12101c0744801102c0e840034110214500480381c0030300d180001c410050012a11440520903081c0c508890307908510001400c401141d800e10301c0d010000075005c0112071003145920700800803101f0a0410740039880d41c4c005004990380001400017401000302140d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 261217329 1250 261216079 261216089
    0xd0204030b060a0614090a15020a150605030a030e0f040c08060a050105030f070c030207080a0318081b120709110c0105010501020d08061c02091f060309020604090518030c0304 77
    0x1081d07068807240107204101c00b952048030002194100d60401940c4444000d1000000081c1b0420195449540c0c000002c0c515420000240e8440a180d2041000507000306070080141c20041100f1890100800d8a40c29107540080c1045100e90101c0f949a403454031610521401034400c000272804800d01901b4600c043d0303190780c810020010f00007910344c46102141d20801e1030113400360f01502c0e03031001901c0d48a0040c80403000d600600d4000704900c0c8042101400f0b45001c0d541e901400b1030a68211100c1401e82e4022121540142c2d80c406000031941c01941015842615044803040200407040e083c01c0032500720600c00c5003001c0c542d00d0789190320000b400c2103c8005000f00103d0745c2e54801a6540e06a9030101004558000f001982510300781c0890b074407129240c841c0d20668800f95002403d01e0108480c0e805006200103c1e4104080c0301c0a1654090066410100605650394001803c107000e00e12590714165140d07000516440d140e00e00050001441c0380440c5d031200d4044090070303100d80041c011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 261218579 1250 261217329 261217343
    0xe42040b0f03070902031302060a0302030402010f0c080a080405100e0705040b0102070303120e0c1503070806060a05040e09010207080f0d05631002041d0a0609020d020403 75
    0x8940440e141c9a200d10240c03a01c010010010546400c40b941d01a4000401d4044043d2400c50682c015841700002407100c0203090f40d005a40389441d10014103403010403040042000207d14188000568000446d420552182421482c5561b180f4002d890048034001c004035a5041000120b0440f0000809000b030310003c6800388610301195004980e200440e20016000a2001802c031031600000d074030555201d11b2602c25156603840308000b00e0014560b9218003080c4003000002c104a682d0721011003504441c1c100c442c0340c03400c500700c00f0081c0103010b50701518440c98020004a25030390000d504032040c296204a40726180c00c0d06074895241a00710b00b40b03803581e0030304043c00900c0601100c031501c40f16409183e0159a64107022844030720007105451100d5510810410b5650555802c03014a5405400303070109800030005074041c1c9050030510040701c00c201d4014041031011048042c2c115591041800c0c0e00d82c1c20399640703620100a00187e1380400b06051001801000810031900100300340c80c01900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 261219829 1250 261218579 261218591
    0xf110d060e060a0b1803010c122003070f021e0105100801020403020a09020c0a14031902150f070207030602070302010c09140a030809040908041206050c040e4204 71
    0x504611401c000c451aa6201034a01e005101c8818440c0c0030301108009001101d1600300303040f0200742124158401d00e00400d2101603010b20b1f4200900414210307000f6400e03a1140c5001502c0c4400b51800090440340038443c10418203201d443c404c002c062001903070200c540c00115110b143c3e050003400c082d00c4125007031306110004103445005000300c4088030b90280241a0042c038ac10388440c0250000d480d614114080e074024100802d5006140084039040c0c00c0256545102202594903149640303000e40c41950480c554a01d44007000490031a4071600c0e0805040071a81c452004909224590704010b00151010072943c044c275074154040d445410390ba8880c080c1058840043d100d070b103000d0b000c14541c00a400d010600c0016101009016006005080451a05102d5581c3d0700035070003c3d00701e0176065129010f07071414044d06004250300104c500c80c4262a040c28004c20b44007915004010301240c2c4011444d03d0342080700b081082c007050051689401d02c1072031140b910411a201c234001e852003141407807 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 261221079 1250 261219829 261219839
    0x2010201140108070303030f110c0c040b04062d080319022127060705030910091d060118090e1c0f110f01320105060414040f110d06 58
    0x1210080c181c6402c2c10040403c1855507500300d002d4110302c02c0d6040001c0e11001c06820300380000c07000c1c040c02b000c4071014200340080c0e2400d10080b200b444e541c5520503428860704004510360755800d15803460000c034115402c441c032075025010b2002a544203c40d540b0000440d520108a140c4900c9642d0b0300b02c0e07007a110808140c1041c3e807100e81003844001d06410081204115251003940070112003048482031000c850b00d50740c0020303034581100300b06036004e030800a070f003031140d2801c120b03070301440065410903541c0c0c03e04003001e042d94900d0b02d00181aa2503010b50128860368001c81c1035403109641c1c1c41003d42c40e1529400c41074041e1022072412002131141c4985a0a400e1182011104040e01c0e5943c0051103004160700311061000602c4502060084400603144403c0070300540c03121080701000584800f501d9030413102030804005101e0b200c10050310051000b65100c0040f142118030740c0351420560a010000079004090007071400600385e24082140c82003800b50b1000c0d000049140000304000380d80c81c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 261222329 1250 261221079 261221111
    0x3150f030609140a0c08012d180803130309050301181401022b0b3705040c0306051c0f17160506150d0b041b170106170a03020c011103091c02010201 65
    0x44120802c041c441c41c09230600164554413018403c0d41515508800700060b40b00c610b9140d01c21390703041c2941c4403007842d04010306802c40b45500007004194020010440c0000c1e0707440000c0d0355424001d20050908004107070b805400d40541c1c42684400000c5850040103207600c00550500781403000903a814080d11400d5450560b01d0ba00000c0034041061412a0041e5108884200400082035818003584000300b030355213a80c0b03e040f480c043c8036180002d106040c0700400552041b00440020300030000c040800010b00f5242d25600301550000c6c800c00d00003203d005c510818000c1a80306640c1c96a2401480240140020070303a02030340443c6034600c60312241e8801c3c40810f8011160261521030240702042c00101106407624030740300ca20142d0000c481d26510301c0c1e84032012540340e45007aa07441d1103051100c0f800e800c190440c88074034040144011a22940c0294445280703ca40f1030510480b0b00c04100c5510f010300844101d848014005060202401c2d003203140c03400350741004d0f130040d0f19001c0072100ca03200c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 261223579 1250 261222329 261222371
    0x7060c0507020f040f0e030d0b0f03161505091018090605061605010207020306010e060a09020403030e010e061902030403060b03010b0307031e170a03150f030609140a0c0801 76
    0x1e8440c2e003124100d9010300c0701038803140050030039046c0d0b180f007035405251050015000620f030131107020130044100c10400444c500c0c080034448c400e4029110740e00240940d1424041198a82810084203107540380301a41d17527008000d601c903040260345809040c8280e01c000e10715044014008440038150311110601c1c115881800384507003000040142c0b001c0142c51808000a10f441800003501d07006255000c01d0400303070280c0c454a00b0380e0701ca6050026900d498011407018102108046080619640b0000e150300100344419040c0110800500c1150700c685d000c07200841080c5554040700544460020750300e61007480280d914503c1c11481d07030794a10f0306008904040c0d034014010181c82c0d0440e121010710768100041e0a100035050080a40080d50780208800240440303d0102d49410300d080000c0d094603070b84d582c41c48000001d40d01c00d120a0280c00c0a500a803034010100040c40c070002c0c580704001828019031103c0c1413160324010010005c0340061071094601d0f5900902860203211000d14080345 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 261224829 1250 261223579 261223583
    0xf041707030f080703050c31150806010503060f22060b0d0501140108190216030c05060703050103050d0c031106011e0f12080702030313080607020d0e030d05030403091a07060c0507 79
    0xc1c04008c04000da03400010700b0504c140e00c01488403c90400c44081c0880280c0716484140c40c40303410b9040030b01c80364000e402c2552004081c2042031562610800061803c11546c2ca02481342c1074840c00e040400c9848954100060a04d40c3c0c10403038070391100130500c941d4001e0070000142324140300021170800750f568070715080d41e00103855000b410f48031600007078114042c6007244100300303a00380004440b400e80c400b0089415070080c1c4031040d02e0340e41c90034130f5401d021005040c0420b250400f4010000141d0008408804c0380e81480d15102c039401603d021920180344110701c00080c85198004601c0403401069505400400c4035049101aa05c81011443e0b542a00c155000b408400090380c010600e031100404403a44020207482c501503141000c46841502034001a4403984100100100d503501000186401040c07802c00841c81d03414800020b0ba501d000ba80034904103c004000714003014040c4000d800a40000c2e0440610204000d611360420342050f103098900318241803841c050305026408441e81c60f6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 261226079 1250 261224829 261224851
    0xa0f03050d0f02030715060906290d0b030708010b091b0a030c030605040c08060108090c060d0b1c030210110412020d03110d08150603010501080f041707030f08070305 73
    0x400401c01511030080d50814642580020041c60340040c07001104d01c02c100700003050025a450800307960800701c07501031300110f140400c1c10b501250001d0004821480d001d202c0e0040664070a41490814041c044c030042594140c4100e803800308074600d040d0014013006006030341c0070081d0707070300c41100340d101341d0080000c2079005008100c90b400042c46034011586503c41c4d4140490350030354510126048818071038903c0e00040708442840035969101e4486a0006181c0d0000e203101102a4005411449184401c0d0802542d400d1841c5082c1c5030040c0c60703090884600d0380c0c034001c01d43c00e05000c2d4aa52480352588070140c6491503d4075001103510a840545200c1d1900400ca198035509001c140000034000380d00340496403c45101280c01041140a08203813903440c035038503003003603c0140d005400f5112414820b0400307100510040e6840000140e000c3c200058141064507182081b00021007010048220f050002034028141a0490301c0c1078200c050310790f41d04189941f002011001c0315010780c0d82180c00703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 261227329 1250 261226079 261226093
    0x5100201110313020319050309040b010f0921050f0303070f051207120f1805010b0603071b0602090307030809100309051207061409010905060114060301090513200a0f0305 75
    0x80100300c690f01040c0344064100d0300705c200001c00d41e5942d012512412a815880041c0d916a142064003984045010a00f070001450092000203001c1004034060700034034000340d9000c440200c000780340c000241ca81040c00c0d5112041c2e0f681c0f005499510446032800451820401d02c0c02c610320500449107140024999400343d0f45540300d00710b440c40c240c0c80c1450b207699190088e081d0940b48500caa02d01c0c060f102610240c1c020344900c2c1450a550b4210016440f070724040c01000041030b007003840e4070341d0f0a61451440c50b103100b40385080c200a00444a101d07400d440f89034070101c01c0007091f030002c100c0c08004036090030300485019001c0b030564000000090094102c1041400500141c10240124500c24080411501101d040b5000e5140e02103e41036602c1e074440c0c00d02014054284801409020030300d070101c00c00f985600c042983d41c0710620071212103d40e03807400184039049880e00524281c2d803090b800c000d4244a0000000080a000c10785441041d10040000c1d05000f00d05104040320351190142204e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 261228579 1250 261227329 261227341
    0x1050d0b0703150e01080d05130506090105040f060f1d0d060509030d3e07111c0309051e0306040f0c1503020415030203060d14010b04060e01051002011103 68
    0x14808015109000b4182c640400c440d0b02601d0503e90805000342d1034a051456150803a00351a100c0702000c100d040c0300f030401605003c5800c1c550080243c0d602610b030316a48000d8800101d034240300daa40540c4101c00c6144000c110aa44680b43c0c4e01020900e50b07405135218139400140010744480c618055000b14090040c80008010343c21045c1e1250b410800e49081440c008081c02c10341d076000c400c0410512600096034881e046880e01c645030040040620329490080d0004c8400900c82d1010141140318500c00c01000c603a5841c2c4140c0d49440d4003a5980011001880c01800c6c42e08203020f228400c03c460501c0c0e4014482c0b4100c502ca02050080c000c0ca41c98aa5844010b07a18448407000e90742240003540200d1050007030610f9640031052560010303561441c0c607400344404600e40c0000c5080500400c1441143d581d8514800e1040390018840701e134105040b0001130042194041694100d030070540c000529084004e80c2034121103003601c200c4401d90345001c04900301c070800002c1c08240c80b018000b00d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 261229829 1250 261228579 261228593
    0xa020c24070c2909061003020a0b0c1e0109051506010c030e03010207080313030f020d0f0302032a0a1e05041203090504020d02040918050d050c0a080a05130e01050d 72
    0x1441d03014080d21070503050790941c80e441d0500603021402d1407041160138454140010819154442c504803d0301405a05550000e0101d401b81c4c0b00da0500c03060045410803454a06124182c035821028012184198a401c640b074040c015482080d01d241c0030740068009540001c80996100f044165529921440e030f0b83c0c0c09071014240048401c1d0107650905c505400694070000440c05404101c0304080a0445894018007804600043c80e0454000c21090720310150415001c06410b00b0b1802e000d0303101e40e2a0844044103001c0392282002c4490b65000121106035014000d1405400035039038502d40f08031203090301240071726688070400054001c0100b0003000700558a50b20b58603210b4503101c40341581e21800102641c205100e48a800342c0c3c00901049068807500c40c10080c4205414011807460040e00c895483c0c416607c400d00502000080400040c0070902ca510036483c0d224070030680f43e2981260051131500700043c1d80045800a003400700e903c40481b04824102c1d4402401000814000e5442d11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 261231079 1250 261229829 261229847
    0x80a0f0302040306050f0f090102090d0b040f020d12020709020c0c0409080d020307080a0b01030e0c10020a02030609030703020c0a08030d021608030a09061d0a0f17030a020c2407 78
    0xa01055800e100100009005001e02c42c080c503144500c2200e1800c0c04a040314240201812401c1c483c0c0c8100590041e50700c680b00c4503015541c0210b40c0324541c1d82d03103051243c0054020300c2c0c001e502c010868803880030880c2d01c4030042107004440c4d003200d1400ea11039494800700d01c184c0618a616034807985442c403d0346410782041001d41d104a0255041a50188407801079030400c0d5180804503a42000304450b00d5018840d000f400c82091809114140404900079160b050b40c094440c0900c030325004084100d4000c0001404203a406811124a89001c49141e501c2e0f802c03240f4100c0050054000f116010700c7e08018a07002d80302c5a0019616080e9030620030030082d0b20491440da110140e402e034040104400d50007440c4525001e110115110069141c00001c075800c0101d60b1501515201c045c40301500001000c84003103501c01c4c05400003005070309040707240804e03108030170001c141c0001c1080850748490f0040c02d0116808070488160601c4003481c0145403411400c00841503840500180e0b100303215482c50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 261232329 1250 261231079 261231107
    0x50f0103020f040609081002090108040b1807060c14010c02030d020a09051002151b1e0906130602010612020607080307031e090519170c031204140d0804080a 69
    0x600d40000b2070103100003a003003540060003140800208102c801010311000b542c64140350000c514114032013001a20002000e0009400c2054140024500d018280201c0900300c90308030880d103119a45440003411400c401c0320444a5030364003017413046100014010405e1000e03843c1c0265091580d41c1c100e003002900484015020403101820018083d203c03094505131003d4658007520380a008003400c40040c0c0c1c7c001e86155522640c0440394491000f1090a80b0701c05000200d4501c1099110250360445028103082113a01c01400030700d00c98100d4040c0c451208441c200d40003800303200d590740028121201e00600c0a90460010002d490000d10010019507000c0001d080001c0d0b100c20007040701c002e00c071244440c04409961100b5002c14444108015007542c0524020144003002c140d883c10160b800f445080c01012201060301080ca4030140140c0da41c4044040420b0703480c0c941801c000365a0201d40d5038000c894000c80300006070151082c1d00c118440c6802c691118981045c1c60800c43e0028144403038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 261233579 1250 261232329 261232331
    0xf10030605131b262b020610081009030e040507030219080c1b0a0f1202010b0307081009020102070e0f0f010509070c030e011b080c0606010207080a02040b04020405030f011a06090a050f0103 83
    0x3c0070003c0350140d405d03004904030500c0501780001e003d4074068604032001e84a00c0180e825810200040c03003000500c05060040203c0100d04040589010741d4403140c01c080c840d910906000800409030b6056005c0d10741802c003120100c001c000b2a0384196070a000590b60403006000401807134410005011704050454440c008070f50035690180c031291484130703130440b0484003105001030301d1001541c24082e690009008030081e2407030740d251010950382c0c3c209141c1c800c01841d032500b00000541e03009002c0000140510740002c1070790b20705081d0319005402d044541603445d224080020542e82006030139507101e00c4440e10340c1c074000111918151a5400c0842d92141040407404580112003d10901c03001101c0c880d10441da225004a08501d0415030002d01c00c030f0440d4020320040101040000d00b07440704580560700080e09114450108000e07229541003281c052084509542d010313441513001881b05142c1b030f8418848801c50300100410f512807070706c8856104401c80800d2082e4540406149104001410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 261234829 1250 261233579 261233593
    0x402040b0d050307030315140f2e020d09090b181b16050d170a0b040219020a050c01140d050c0d06030b040c050405010b030f10030605131b26 62
    0x16505285a001c130200b03c0000c1c4d102c1c0300c80000c10001c2c03031484e4084c0401d03000f100d020407050000304100010b9030700f01611942c032622207200c0121580450814107041c000035458694044080a0364407a0910034080024991030381c000f4560420703100390714505200500c10411400c3c030814501c0c45660207055060005c2081c142810010070110051903000c400c824416150401810a02d00305031107050050280700000706d1002ea2021032214056000711210000110120101e000c500240100301e200d51042d0709211b0303042d50707150300000c80b65050340c032801c201d0b442d0244e42001112131001e040c548003030382d50003800514105071007604159404040100b0440c10444403000820545019510561340c4181c0c110502c01402042c88001c809090207442c14480d95140c0466503186110040882600141c0c2c0d4000c5902d81005200d41e00085030814024882428001c07403142210090300c00846641d5008a2070700341c021000721604040ba544943c0541d0071542480e45c0300141c8030718010803078031030040c08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 261236079 1250 261234829 261234833
    0x12110102180a0f080c01050a02012c06090c0109090903030209190503070e040b060409031704080a0e150a03111603020a020f0102010b09070509120f032802060402040b0d 74
    0x12000d03214400e4502000c100140000040c40580c500b203400202000c0d050f242c003032000c1a400100d4040a400c28a411681c0700203841c0101d00402a100413160038031140c0d040141d5a101840140ca00c5802c8034091b00c11903165614525a5018101c0d10503002c120240c004018001070b652240515a000f4200545003041c140001180d0450b110044071514001403001c0c00541803c012440c080d0580c082c3e00c0c041410262901040700754000d05040c4a29115241c440030140314150304030000450200c540d29906080c0740920b031a40140003504009070b00c00c000c206842c50800f400d50114250301024a240c8213000302d00b1000b5000c0c428050b000c0388000c00a0745031f03041008103404c071040c1c060b03800382007170244e24410400344100c2400401d04583c1010340c84591695000442600401700381001c9540e40300c8440480c82d51480300b2080c4174140a40301140c0080f85001c402004444040c4807856100c51100742203801e1440c02c02445001a40080d0000d00182010780c01804d80190092669405c03a201d6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 261237329 1250 261236079 261236081
    0x80303040606060f0503070801030f2102060a0b030c0607060c0c080c07030c0b2515061e08151b07021315050609031203130606031407080106050d121101 67
    0x19102260200daa0340002c10280c0c0d030003c00112160704c507280003440c42c200600d0080c00e040c010302007d024405000321081c2001480c1e0000c4501d540e12003109010289010000794640c541124003030091401e0007440d41c02480d001c1032050140d600201041c1c1072101c03548400c001800d525500380c0510558200500204004002801c00d8581c00401842c10030b08500d80032176100f01d01c0d0720072070f0b10034424403060b0050000c52074482c07030404600fa50f0700c84066003400c00c4010304104d50241402c031454184046401c03050304185040c080c880114102c1482c0d5504211680e07084020300070043e00321280c1c0410700c5080301c0144003200d07038140300810303007030002940000360503e000080068106a40d5030b483c55403006181a28001414101d030b21a040280f4040407a464005080c40141e0100d000000032340004010b000d001c801c05e800400c2000b42545900c0c0400422808541000b0244100c0384009080501401404195013005d0300340600300c060303035a4490144014480090611140001c466440314003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 261238579 1250 261237329 261237331
    0x1c0c05180d0c0807030c060c03120f09080f0702090c0304110904080909070906020118050d0e0a030804060305041401090512030402060d0f0501050f04020304050d20030705061806040f030305070207080303 89
    0x40ca0701806204d4554507180141d101680d1001c800d01240c0c1c1064004a5007140941d21400c41d0080041184000500450001c0104400040510201207400110503c220001c1e003510380c429070380200d00e61141403000306030f80000c5500500410f1824107401a50500c49201c54005108402050030914400d00141d10020110b40c4000050800d100070010540d090260601401e00c8071003042402600b0f884554881109000d601c00b4480d069401c800d441d15092070810055412104c110340301d0307481c1c0c0c000030042c000c19034040e0780049400c0c280c05560881886842040e07540003000b8000749007680c0030000e0315040140103136800403090007500ca400d0041e004400c82c01d6540e0780c000490358100f60402a002c0401241940a248144100300c00100001550040ca5110f8280441000601e00d5a00c24410640c3d03001d0710b9a01012030030000b04040065040e000e401070940c104841c00404108a5a440f422103028111055030703510a004640a41e001c19000041e92040d29038043e04e6071040b601c3c644c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 261239829 1250 261238579 261238589
    0x150f03030f071a01051c0303020307230405271303110a060617030406090b0d02250303060b0a0f0804030e0a0f030b101a0d02090a0b1c0c05180d0c 64
    0x35010220340207200c3c08000860145c441241c504406070200490004a0141018002e041c9a400004101984e0280c412046186108107000390502408403140505402c1403007242d000700b410103003409103602003c5480c1c1c07462001c0b5900c800199200c0c1440189210540703400e905000405038104503c100c00d10025040c0c40c042c2c407010404a24048081958040005100010f0f80040c0403c2c0429436100c0f58031000c030348400c600c0035102d21800ca0984003d20902d00803002d1042a40200e0200c03d03411440381681034000c1e1401c010311940d644d1130580c10f00c82d111200d8009100300c440342025500a085e075503081802490001d17601c466501c08114108140e40144500d50300c8a801081000051818143d0280f62a200305d03594500d8292a0025102100281668800086505180b180c203617416100e140c44002c1c070045505507030b0341844c100c0f42c0c4018913900c5e90040300320f40340300c4c2c481c014050010220b00a41d00e261605c074214051100d00345480c04204d510064182c2d446010864800310b40c0d01900c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 261241079 1250 261239829 261239843
    0x3033e0a050d090f030906020c030a030e03070905091506060702010c03180812072109030b0406020c030f030108010c02011b1d061801080f090d111e07081203150f03030f07 75
    0x84c8075810083d0200450380d00010455126129550103500c010509000c0180c0c0740c1028011007280900203070800c40d03550098046140b6243c2044401d1100064287d80304040b41d156000545801040c01a540710b0b5010281c0400c1c1800100030000340300e8090550b202200c0c00c2c07005c0c400c070f8440341340d030f824001c4400040041d000b0209040703080c00001490070010b252892480c00f114110180090b00d080e49611021346076804200004041c881c031a0100c1c1e8401a080c4183ea941c0c1130200b42040c202d800a01526207a03610b0b211800001f42c1c014481c28000c0496100311000b03500301c40c2c0007151020359104104154200f90300c40e5030304640700d1001074226864a51a03201c0381e0442e280004118981c000c1444071090b0082d814000c051001050740c00d50b045442c03600301314404159890629150303e01001851860f13110f84803440040000c5031140c00c3c5d840030001c1d07400d082c180e050300c0c1c8058081a10310705002920505000070b5482c2204142c0701d03104028050300d040500041c3c4402064000c1442507a480c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 261242329 1250 261241079 261241103
    0xb1f06051911150612010213030c290f040f090207021906090b030a06030b04140106080c030c120708030301060305060f04050f0a1d0a03033e0a050d09 66
    0x14245002421620400d528002210724000d0780785580ea04602c06840e8140d00c584008510903460705c181c411003488414000b0340d030710004000c140c103400c038041c80140c404860585d008911810740303180c101c103500030680380c02030b80442c075003540b00056102001550014400b00800034840c00c11040c0032001f40700c00c0e4001070706ca0380f1a005001c200c0c07440c0d2071005025081c1100510540c0e03001490403050f2564804070948030740c0c0b407448520003801c1d150030240103100504104020061005a050300030b0041d00000c1c89916561803603195030b80394410b08142e25422019003c070083c1481c50540d030022191400f2200010b950710081400c1d54802e80040001a8a40d0304000c0f280c02d2585800107803e40c19038007007060340342c484401412410081d0208040684170710311a07600c040c0103071010f800002d184094448000c4540703405801444201c90030040d41c0c980240003c070000c104031862a030710501c0a40204113690240401090380d00c00f0040e80d003409814440c1c401807000b00e109410406118041d03810741 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 261243579 1250 261242329 261242347
    0x10050d150c020309060403080313080d0e101b080907091407090f03121b0606060e0306090c0a05090901180f0b09160510050c0a0b0708070206040201020a0b1f0605 71
    0x41c1ca42030a10141903500c2001a000d244d15200225802c4a81003440c0c992284ca401e00e910017000f9082002815400c030220f40310480412680c0070f03541c4c00d450602155610a0032580322401e41da4a1868034804003000d00c000d02035076014014541d8002e0100c2c00b039038400d075103030041f850485d0380d0b124540c100c4013145000c1012098001103500d01400001000383d1100c0d2555a82c603840c84c109005000030406460801402101001c45104409500c040c00f408101c3c1ca90303000400034035014000a100f8452580415010030000c910b06a600030003418940d44141050180518000050901c00041d90f845180d80742702c583c0c55031034841c11446009240b000740350900f844403110344c0251641510740c1002108801125102d01660b040398000d4403143d0310489405d80c00c0d41d00340940007698409010344d0300b03040108a1001c0e0382c94410001074a5406603511200c90032669080100c50090150f40000820781c081500340c1107082d40540e281c0c0e0005000510005402c42d0380150380d0204022620100e44810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 261244829 1250 261243579 261243581
    0x2e09060e06091c03020c030a0c1529040905030702040209031006030c090507050306030703031107260d050a080403030510050612010608091204140a0b04031b061e030510050d15 77
    0x183d04080c2d2800f58200341c45941c8141c0c591042030301e07240038840c03840c504004000e2041170301610a491014200300580c00c4107410364100800c2c4803021070f20780d003100240903103152500c14005120340040066081200c141d0a0000951044100b6581882424100705800c0b8a502985002d1481619480d880610301006102a00d0024090509000e801d004101c1340792000941c0100b2690907241150004207040706075814414160860740040900361708209400d81c424422080340712221044600018940d441221a40143c4002e500010351550208011034401e402c00317600320004002040c0501d56404c0083e10651081f0f6a0130f4801403e000100309a5402c49483e076402005c0170098040311000c0c04070101a80304901400e8a4009030b05581c41d41501ca05025401904540c40c50355602c82e00c9080003450300d41850a0035826001042010811901c44c1c4d10078041c056040c8071480481841500c00da001d840300801c48480d001038140f000689a9410103414141d502030b600c41c0a55443c0713401940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 261246079 1250 261244829 261244873
    0x5071b05091006020a03080415020a0815010302130e060402040f140901140303071b090603050a0b1006120911030d030c110307020102071502010b04020406112e09060e0609 75
    0x9202c88440010401c0315076004119100441e03454501441f40c4d50307aa2074172285226500609c51340c12403020400b2102e05030008040e03402558450041001940600011811b03881000042100d88020320301c10015401034002154110400410143c1003d0b140d40141040b0345c104d034001800b0320800e0072a0650740c18841466400340800c9a45070070142c5113403010076600d10030300400500d260300381e401d075296500c517103000000a00000300342440200d9480c00c1c441d035542d0340984c06590684a080125181071a002204000c41c0c0c242c0d2200d045e4560807901d584014807030007070191140d44140310840120750b418008100320b008291000180d6544514004040500c2404030340d4842d4801c01480001d0707a0005070707410440300c4c540084909034650760340c124050240c1c9080c807a0090b0021602103540e03078200503103801035110b10080341c00e400040880840941c00700942c40800120225003200490038903080600114000c00c8045270300003055021601d4103d04440c030480035081001d0362001c41c450f00b2a94 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 261247329 1250 261246079 261246091
    0x150504050901200a051b0d090b0315010c05011806021b240417190f08161202120406050709120b01060305070e06070c08010609090b0a02030705071b0509 67
    0x8104940702050343c800c450070a00d08103402040302055016003244a841102c01807000c0078a002c011000d40003c042d03841080e4a07004000c1420301d107000c00c02c00540001e407441013888441c0f09450702d18810041d14005640a01522a55207880200b41d40245207021000c0c0a8481c600060f901d4020034410491402c44105040e09a0007c6940d44440d0540c5030851018401d80904d8a8040d29285800c502018010740b21070305806012075500a01c4180101c40c1150a42e40c0d22442c10103031390f007441290100070450b90500419030007170240a042c1c0c42030b0000da04440720b40b140140b030195140d00382c1041c07140c1114100e034501d844008221040d58009041c01c0103060b8500905804030f02517a54400b0b0344814080c000416aa0320002131283c0e11030349032006140c10141090382e40b0f13111814070b4180004030780900d944941c02d04600003082542449454071540e08a00e1000698451120034030107980090001740c01c100c03040c803040700403560045e54410723001402c5400d401e0051a0034180081c0c2d2400820fa = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 261248579 1250 261247329 261247331
    0x7050402090604050f0d150510060c0302100903020709150f0b030105010c0b1018050708090d0f030209030124080721031b081305090a0213060507050a0204150504050901 74
    0x1402542d07100c070720940c0c0550781d00701e4017075a400e0800c2011408409500e10701408244803504550f02c18802da5009a00903510580b0500b8003d0312038409440c2c08810300001801a800700c406139071607414503031100e03050b14849d106860340a075407000e19000b51101884061405e5909410030088241080e10041c0201007440070141036615000c0041c1c0400000c010244c8440195000120100040407042000e04829030b0243c9201804140010080c5003c03180000840e84100100c1e031581e43c0050240c0c2c40510564409800366400b06044000e5000621a82c1d090343d20348042e0506000c000903503400039243c0c0052070b0340052030258030b149044415401b146c0001c15007001c2c0d019460b1400016180300380c15041c0070400300002680440507070402d000c0a003a40c0e10210b10070500e00d680380010b070220748080710511a651190303900c80d030491060a0103c0200c084041f8201312080c01440607100c85030080041e294030100301e402240c1070f82d00540e4180d02140d41d0301001e020902d06446455003020171040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 261249829 1250 261248579 261248587
    0xc0215010807080d14070f06020c010c020f0d050d060e070305040b10080c0105030903070b04200f06070b040503070501050c090a150c0213110d0e06070c030c0f021305070c030207050402 81
    0x102c1038070303050413001840401a080c079800c5510038100007164007966204480c100a0170160904600039080340b00b503070b60f85500302710030007180303900c000f41c11004006c500001d0400154901c03400d0300d00b036020344c1e00c8250365030712500c001440c0407500c83d0052260125480105031807900340b4008805120061441014180c1c1590034001d07040001881c050b07070202802c003644d0300c4e00c900903464030314080c0c140000d021141610800c4100102c0c59610340581e0b04001c03402003040140341c100604207070f482460540200090104802195544034620380040c0100c040d60b14209454a0f800c0c2965000c440c000d4007000001000365081c10402c550310010300291000d101060703640b5030000c081d130300c0e240800f9104002c40d41206007117030f01590050002000d8445c0c03403940ca14102102d20007034650ba0380801101d00400c000204194000c8120149407541a954800c004900f42c0e103012030420300b01c80c140d030810001803880f01c07010498032806008072400d8403115160012490000e00d020746c0d5410450003180140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 261251079 1250 261249829 261249839
    0x615040506030411030f1e01020a1205100314010e0c0108160f050d0218090a0608070603051e01090b0f010207180f02070803130309090b061b010f0c0215010807 70
    0x401510151042115031a40e60380707590800312034806802c4801d0b5814024041007020070a40007400e44142140041c103101a0b00845e11b44a00300d0003841030510100340407000345000c04030182d000640c040381c05011182e2058036500e94221030402105100707141e07996010703551902030080040044086c0c0034a0942164900380d80240300b804c40100c40a07003401000e5031003492490003071055508a480e56070046444821200180e800a01704040d00c41c05035907803e02207254002580103440a4600e000d0041c4011483c16400324024000209014041c824111205c4c0c02e0080d80043c507402454407406c04102120703aa0100640040c1d01c1e42600d0555001c00c2c6e04100028183c2d10107401c41c81c00d07a000140d040781780d10024001e845803101c000d29444001080181d88540d010441d4070240c080d603200d0309442c0e284e0042d81e0032112044c4419520031414010b00c0200055803001700c10001c085d100118606ca003510501c02904e200103010070150b0496810048684d100d801c40c2f40c0140702c1c150080031624030b41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 261252329 1250 261251079 261251119
    0x1080708010603030e1c0206032a0304081204080906030c091c02130e10050c030f0a0207030e060d0b0a030605180a200102120f04060e030c0f010810090e01050402010806 74
    0x40c0d00c1403401600c640b0103000c1001070145031b8020711074000e008183c0d6850a5030b000348248002c0c500001c038902e01c20400040121035501500d1045600c0101c0e2840c200d0302c01200103089000030012200200c0403c07005d0152784074000a50301031065140c00e203490b035a0010401950240103e03440c881d81c4800c03201d120141e541c003c0301610b000c0d1051700003c3c44800b412101410201c118040c4080c9508103024800c06424110080d44980c9030604405070588804032040e099104805018000038109200c0c41807a250440c001c0400c031100c03507800107500b564100407404101302c0350b200b924002d5488040001001c649542c0c007000600800c05040f0210281e80d580508000000140300d01100105284034280d008001080511400300e4800c0d403640009204116030342d100380501d8002032014200c1883e5030034001105208204014004011081c000c401101c0940000b0943c03403001d0038192000500d041c040c410081e011648070004201c03403600707000140842001401d040d00442e8054903450f40c0c4489 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 261253579 1250 261252329 261252347
    0x1050915130b03010213030203010c0f090911040302120607020c12120705030f0309010b1005040e0a0b150a02161202060a050307030603170c060a1e11040803070305030108070801060303 81
    0x300719410316101404150000080c16040d1045030158400a540340e4501340ca0b20703440302100c1c42140240f02c1d9845285044980c60092000c02002c12048181800792405036040b1041328003d0005182c1455566000104180c00700600824250001305c1804140e1364103201e002d40402c4142d440e80c1848851051266032000800020b0300080b07004034200040100900855206801d1703101d2107603c03800e081d000d40e8000c0101c060f00a00c100040810361a00b240180d05560466042000404043ea01c10755488058848095015880140001100030f00c7c00004040d0002700f206a000b4076030388038910000032034581c15030081590014445000e400680d18213044030300c0290f84e481d1031a16a12800c0060300a040a03400c010901c422030502c02c4000c123076101c00303000c64420110403a05540c451078400021070318203c02c05e03240402c000f400100c07800b0702900640c05904e0301c1e40f009864240c0d00c0e80b1650031600f25a200710001000040100003000c0200a0f04005d408060000c01200e413945c0e8020b041d11203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 261254829 1250 261253579 261253621
    0x90c2a0303050a060504050c180103050c1204030212040f05120f060103081b070303030c0e090f1501050d02030106050307020f010e03120a18051e0a0c17031c020909010509 75
    0x14580300010f08200c6030703030020001007901030400d101c03504212070755122a41042111140d0503482e110744500540c401c0c061580a08443d00c2c07032501e071500c54642003a074107000410640a510500c0d02034000920754400810060420302d07508082d80d800c0000f041a0801020740101d410742c4107449046504101056031411690310840705982c9e030354600b820307145442c10300700217451a0243c1c1d00004103054060b0000113902030203030303a50b5030856a070004200904c2030654105003c0e00400d0001035855004104d44030341480f050520a0034881450410703070a9038000d0300544001070002c01442299501080301800a002400c02440300c519888c1225540740241d0f81d040340382655070305c08075511042980c0200b80072a003010800c0c00c40d0240f0b061041c2c7d181001f0030a05448080c60554004155001c03425141c0c41358030600318071400345090084400001c0c2c004100241d030004106030440840c0d400075000d40c80c0d964400250316040361000b000300608050384070900811482040001284206110b410046 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 261256079 1250 261254829 261254831
    0xc1e07050f130c020a0c0e0609180a29160906050a0e04020d0e06090c12162d1403011d0d030c020f0114100b0a0503040602070219090c2a0303 62
    0x3c90600707040380341601c3c10f64064218038400c100031500d0a4000740043c8168016030303c0c40b4417030700d510000d00d9449640d1a2401c285410540e01240042d90401130305016407401c8100452040803107444034054002541c515004a1581440740c0c5526040311a00c80101050300b881070800030b506002a10f40c0660000c41407080c1d0340090011221001944a02034040b0342c0c504640292900860203940c6002112400344980000e01c00c40300c50080008003d5101e9200121403800e00e07140c003642c8882c0b04100ba140441d07a0301d111100060541c0d0752424400104520055483c01e0007440040c182110390760044207401140d03140100b41a241c0000d1b69032031f03a02c2d00c1d19000500704071500d000c03402c04220404441055003042c509071210305e03440794000d0042a030006110721065a4130b000215500c5000340e8500421424000200410006e0303000e4141a0b0014098034203d8101e90842d003400311054102c004029918503002140ba42e02c40c510070210002a010b800030f484007140461010306e000c000c014101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 261257329 1250 261256079 261256091
    0x50a05060906011d1503040303020a020f0c01050405010311090415330c0f0506070201060302030c0d0309030f1b03150b01032d32070f1209020103020c1e07050f13 71
    0x5071200840c45c0c41c050341d6003080c2c85d02c0c3d06145ca8002c1c082c1d440412107100502c42d40e440022018008100800c00d060140c417103a00d040e18000041d8003410745040c2e40501d544051000340310f0b030344850145514041c120301e11880c04504021314030000400460301c0030300c50701100c0c0c0100300e12015a902550558643c0c1002052844d0700d00c2c00316101c0c80f900e0b00090050103400c3c04e1010f220340540000041d80c0c4203c0665450700b80a809001850710800d50180015401032820000b051101440c0603480707001d0031021326504486011020540c000780e00c1150800410440040413030380900c0f0700200f014003441c040c05040880ca80d50450b220380c0c002186442c80300c1160130b0f00c480f469503001d9040d00721003200071505004000e23001401d465010340102001d211200c009442c41c0d1080140c60038080c0280c0b40c042c40c600c0d02c408184024000c15004a040c15820400700c26100c200308022132001c81e08441701c02d0a40da58050300d500303142c200d500103070150881c44084440d507981c6001c07040c0030744200c401c00030350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 261258579 1250 261257329 261257387
    0x307060f0f14011a0f0a03053705010b0c0601140d060513021f21020403020d0b04021002030a02031209011e051e13030e04020405040f050a0506090601 66
    0x2080300341404001e05103001c020040c08100c441d82036040390207284080391400d80b010a5803d151160088041c20884100046081d50b03000ba070041d60400080c500303401e11104101d5028043c07030700c842e43c00da6182d1900721410340c066074203004460140010101080c00e09003003010240d550401030080c0708003601d01e45d10814007911807481d41c00300310340c01a50905c600c3c24042c00d64040d844012a0a1340901703180d210b50070007a4401302041c0d8640d6070765911882c5d182041c0328100c100c9c1d07203915420451680c08000020140c0d0340e1000c0c4000e11405419402a641014410041a00312103910b480541d0028441030b00065008420354406500d420f11056140e92070054041c0100f40007080301d84c041c0c640b0094401c04c03c1d4a90300c0a84503c2c03240c041e4032402d5012003e04c090460701100c011104820000c0451b0000348904902d400219018202500303240e21040010140c9094903018030301165038200301700c545407860141d15049201554400264204140001c2001c100214225082c1c0d100c0b00324205c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 261259829 1250 261258579 261258581
    0x60503060a2d0b0a0e01051302031e1003140607020f060702190f050303040f0b0a1109190f080d1403010302150a09030807080304020910060f1d0a030c030b0112050307060f 75
    0x2c48690300802a1000548890240203180705c00e024050041403010115584018240308582c09003000420b01600200002c0d00003140d150700030200201030081c00000400901c0d00b84124005505120243c5214544807a00138a44116545110358940c006010b0040c0c5a401140920342c50f40d032044181114400c501b070408152140e02e0008010384800010003052004070032840030810b100d0800c0c1242c83c0c5812009030140d520300e000ca810000020000c87e10146000c044500004000048410b0020f076640b0351009103c1d1568800f41094004291189130740f42d20480c1a403802002110345400c5504540204048400c14010001d8808002411004440c014100380c801075074049501d940c5c82541d0301d84000142c100742d03001c0340168103a1000c81c3c03800b0000800e5000351202a07a0703035040c5815940782180d010b02e4201501181c0a08040c4100c0562141d03d40d9102450282c240003c120345145860b0321858416030091501d411141d0100300003a6011040720080c41c2c00040102c0d1002e030705440c2da4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 261261079 1250 261259829 261259841
    0x23040506040308091908120d0b03062814060607022b0b070c0b041b03140601060e090114010c08040902191112071209080709060503060a2d 61
    0x40d40c001008107000040007120b07802840d1000c000e55004d282e800300d40700342c4040e020845c0601031250700000c0c60805020111005803802c0414000301040c0c40f0b0b00c00c0042405c064054079181c0032140d240c14150a01d920314521543e41c3c1141039030070014030400b684c0c0150351103c0505150300c20303440010302c2420341d980c1454a07400350842d0000d008207510001031440140c00d014204840c1c1c15410b400244e64103010b2061206200c2d0421003d8100b5580e9a560228804041d03203240c900704601a40800851008080c04a100680314001c082c81d5040403006040000c0c407050462254050f00b0040c040c1511000034211041710a09141c03440300124030381014103008079000603030042d201050110200c00303c040041c0c08421191510130b0020321a0904079254202200ca0346a1315901708080c0002071455070244540d8015803070855140c40d114241c0600740320a50b40405105a02d0381c0f010300c0f451800b40040341d04516020f40400400c00c038480194140e8064508602c1d001110f40d00306d82e01344842e50469 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 261262329 1250 261261079 261261089
    0x2130603050715030b0909100b03030408011e05100506070f050c04020307020c0f0301050c0f090409020303070f0606080607090e0601020a080c0109030e04090c051c0203010203180d09062304 83
    0x25403100e40e11078800c3c0c11140c6a2403500c400090500b19080c80741c1c10090f0986015401d4200035000507242d0181050103000344e0f60700140c051004207c0000e000c4d9081c840c00707034000708043c559455101c2c07048401c1e040d1103019001039200c1a0280b0100004e5072040300b102c003007652002020000e542581049414112034039103c5070400c1c00041003040c507950204078050000411503092000200f4401130500300c8008603840d4040d880204a003440019040c4080d11941c03c0040000c0794500541d03021a080d80c0154200310b60610801c1d10a01c1004068041c0101612281c0010291484d011500030510035642c071401904412440118a059109120303540c55071707421074205561100320071700c3c0500900600d01705800243c0c419a640030a890a030050400582c0c02108411000e401c00040294202c0b400b041d1002c582940e8420f60016103003800554443c20076418070380c81d41c080d40c1e40c106090840b24a107100400071000002c2c07140300d400c1540400f2000e00042007400010303401c8c5419036244199081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 261263579 1250 261262329 261262333
    0x7120306080a080306011205010e06040e0f07030c0503070605070b0604090317010611071a0a050306010215090a020f010203090321090904060f0e030c03030708070302070615050405220213060305 85
    0x10b220140981c64000758010602aa02e031480c41c44520400d6088410078011203907030f6844400030512900e059003003c441d1055600a9800e101510b0035120302d0101190700c01c070f540e100c42510030040340ca0140300180003440ca60504038644020342d40c030b2410306240240414410396a80154500b8184521580100345c075451005000e00d5850380005408a21200d8104440c1d1003002d07004612445121102d1201c580d00c8a241810078580681c1601d01c5d8100030500c904511403a00121820858003c1c0540109504009050010390500601a20300040005c0e14103550040000160988000602c01200c0c034a0307165800041e016044d0101b00351103241140781e0700844681c1408180805540408401c50090300104000c010307042400c0d40300e02440501c54525003003400080e6000d0f000d1030955900081c40d1600520b810011b030344803030480310b00b40f100c2c0205501e84078051004c0c0c00c0a104168021190701000e07850903040c1000002d8045255070024084c55800761880c1441402d6049080910343c0314003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 261264829 1250 261263579 261263593
    0x120304110405251409100201020c030715270204050402060c1b041b170703061203030506100305010b0a0c022b03121401061d091e010b0901050712030608 67
    0x20b4010340d030a010044880f8244034803501c2c0d6802d4011101200042c41055410b418625008200b0051201d00e1103076005554003006150b002c0581440200a654031400001104500e11b0712907a00b107810628007451ba007601c900102049054040b8415055a4100c40c0442d0070707070740c0c0d10220b00280140a40c1014a1290300a1202207410f400100c1145a5041d04c1c100030013040f07110040d400040c004004004540b1049410000380048084c8907808001d1342400710b049940c940e18100001c03c20741c400c1c0d00003959031b0b0030b01ca554030703021500410480c4145810700081d410010705d0034651060404000a1201c11201d0070210740342d01c030391000b40302c0d5024803100050034003c2403000c03415981c01041340012415000c141c4404814070034107050a8148005055580c01c000042d43c520000100d603e1003091040980345c032641c7c5e80c2840c5481a90454000c4910b060030b003607429a419010f0b0001d0040007002c0c01140100e0340d00600703275100c40303030880e00c110244500703250150002c00c081c1d00030003d0f501600c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 261266079 1250 261264829 261264841
    0x609151b0703090b044119050a1503180816050a020604091b08040c0905070c0b190c0e100309030c0c030c030b0609100303080601030e070e070f11120304110405 70
    0x50820101900c3c6d030f240790390701c1010020302c9030f07081600c030900d9000072500b201d403648203051807104403042d24100003d5000040e210b80001d5891207c1d40e1100c00ca0b070709005c241d404042c0c0c1c18000c200000000810030580f004503a50341b00c2580c0262407403140c200c01504220030a000c0c0402804c000315801412480d580d58903501c03801c01400c0d81f030b54440c505800e500c210002d864460000300344030307071b4011740b600c084c003810509000007a00d00a89500700304240c6c0b6440d00080380c00c11700702c0e030b02848a240c19020000d0744500304c0c500f5034411103004c0d018012100c114213590b45840c025501411118070300001c041045240564801c00301407009851502c4401000c010414440c082d102960b02404003080680c1d50b060810080001c104e5030b6108010000c07004100190040c82e6168002405041c080f0310001d4203d03100786007454944c4880c510003107441c10b00100e0f03600005e10075091006864034090030001d501d0019600c040b0305030160058000000090f003880880c001403034030110000c2007484641030007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 261267329 1250 261266079 261266099
    0x141801060b0324060a080606091f02060708010609030206041401200105041a220203031c0b130608032d070f06060b1c11040e090609151b0703090b04 65
    0x420708002c2032a014501c0004989800000d84100080c41da82c1c14403a030780c6200602c0001e400510002d50441041c0c00001840ac03000141c044440d02254024011494298002400b030281a0705c1002070040b0b006060015844801c101c401b510070b034003a40f0001c40744540049a07107129100b10310181d2120000c61200c40101908214040d034003c1071032446000000c08200a030203000d8070f818030040498107001101001c205454a01c0743d00007801d8074200307402141180f0640fa070341e0303c010350340c2942d030002c0c000700e8540001c8622001012210030069141040c1500da0f413072180ca6050700b0050b00341ca01b01c603901e56043c0301551844041d14461031311140c0602d8507040e41e48000d02c0450340542010700125402411506849403070b08411181b40c0000c0d1103128840040a81c80010200207000f084003041c0382c503111203140c0c01090389000501d00c500d4041341503402c203a034103603840d6084610380c2d09201c50340340c2c0c2c081c1d030f040010b9000b48030f07965424103854103690707811642e40002e01d10000030400142a00344 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 261268579 1250 261267329 261267361
    0x80f0a05010b061312020118090606080a33050a0609060807020c0108010b09010507020607030804053a0201150906150305041e0f0c090b1201141801060b03 68
    0x110310000e111046030300e003c01c625400f50600301010040b051000308442c0084100c19a20710740107051030b80420903140440e01d0000800d400002065465640070800203502491041d405000080d08100805140c181e002c501a401459114101071401141381c803441c0003001600107000080210041c2030b590600039118015610400c800300d00b20300000b4580500102c1d08400c0050305960303420b1985c0c02c010240004d038105c1103100d410070030140800030060b100c100003044614025102c10001c0e2a0030300d040d1345083c5040c2a180603906030788080240c004a4450010340034400340342501c0500214010403401041d030741940c0101140d040f1030005551020b60700107002d9690031942142d080c8a032141c00e0307098030344c1a0782c01032491442c50400001e00300d5020113402a144541e20034614045103444071640c2c50484c0d04034980039643d948942800c0e02c0c1c4400884610200c4900902154540784c50902008900800da4031040380c08030748540d18000d0a40c000710243c0900d0740341540700d04040c0000002c00d61 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 261269829 1250 261268579 261268583
    0x3020a03030608030a080f07050705120702030613110108190f06060e01090b18041103070302220311040f0e1209040e03040f06050d0f0513020306060a18050907080f0a 73
    0x8070380321011030040da0202c1200d070311759100d450300c0380d451b158500d103c501c401005101a04001041c4000710004900344000c04d905a0910845c4c1c3c1c03201102d004250511102620400c200c0740c41e004013900082003859500c6020200f402c0a030a00e56500019949001000c100d5044562501925000000c01503010405841c6642da45418082200005644d8a480c6010300c4060b80c0044c400030500000c020b081590300720f40030b0408030340c02c0100c00181d03250750410350390040401d070042031500c101d42c1c0f41c0f644805650203901c0d00341600d030b186490359038001c0a40390416010b0390300c1e480c00350903240090f006014484030b40b2046501d4541c3c40003c040b0741c0e4100c482c02c14804c1e8100000754204410000c2a00c0a5402d002c185541c200d1400c101554198810112541c009441e06460910381c01039228461066541c001d0b00300f0640c0c450310415080c45e030020080703032080145004c103029203952060300d81c075400714200d4005090385849108a162040c079034030082031445000007502d0740c000302103a0180c43c24 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 261271079 1250 261269829 261269831
    0xa06050f041203050606092b05071403070605030606091f030b01020f01140f04050f030f18090408030612010603050304030615090908030628140102071d06090403090b0703020a0303 79
    0x40e040e0000f10306590054820700c0d40039005019490080c03a01e45010b41707001030030710080000031071040f0350103040c0380104c00180c555820110041240091444264540030070484c00342243c00d0501c4000f412902000d4502c9015005c0462403a5040d2668242142e150555480c08d022036618141e00402030315008001a0050084188c0b00c1022001401040b241c250440b90b6280035a8910b02c521098a00c0104144c4d000cbc07080d03401c00181d501041c0001e10000c410103c40540c6c41c0c10740d0a100da00303011408801405030180c0400c000114200c1001c1e240c02c410120741240501d900d07000500e015000e907800203405030000180c00130800c40075034458030714050f611050416581d583c04c0c01c0c02c11904a81005800b1540410004080e45400f05c0300710240b00421612082c0541c2e55500d4448030002504007550340b1100c5582c0954540c2c040005600401240120481483d2480042145407a0242c42c4074003414451020070101130050149101170a22400c12648907011410029545e600081040e0007003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 261272329 1250 261271079 261271103
    0x10605010f0e0315041a01060818060417030c040e010914090304080316141902090c25110d0b040605010e061e220504050f072301020a06050f04 63
    0x9000307004280d05404000c3c05407901000e0700f0070303201000300000d004a0b14540320013490080754a1aa801c0d6020b030041c1c0d81d448006140080b41c0410204285d241440c043e8043c0082000040803102207a03142c0400044840e180c1d100c40342404030341d01941c3c1040100d080424008142c0d01e2075a40a0720003400704100d4081607840d6903c905071a40714034002c1401c4c40d0420408081008100c00d080300440340300300c000003a13003803807011a6414100e96011308007003280190800b505520306007c4103508940c855616500d88410540800b03d003103540781a15602d10129440e0a05100401030719988900f03000d090b0b00106200e074a480c1c0f60300d4000b2141200c10910303000020845040340c0000c0c51203580050620810403031003521210b501e052040140b0b6100710302c1c000e402c2c1080866070780e2800b8400a6103000c201c81c1498602075003072200d184108038641d40020402c01031108250b0aa0000c81c01380c00780c00c2ca407000702000403030909010b25005030000d800d01050100e510f40400c81c69110720300030945002c83c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 261273579 1250 261272329 261272357
    0x1201050a0518100e01080a021201020a210e031209010c09030308070c020316090209040b0915061305030d0507030f0c030e15041208070c0b0405060409020307030905010e01060501 78
    0x10340c250501903280c10010a0500d580622035160038660041107650401074803543c2e0780d003c5241458246c01003100ca402c029000c0045007014900d41c13041c908070310001d42c00c110341044010558411044003980018015510b0a5400c1d502da11465001c2424025a640e030002c451240104000c20b5601e140c06601c0d00c1c0c1c021400324420110081902d90595550103103455001e0708440b9090200c02c02d980c1402608910690548803118080091604120151300d0309000400c0004540d5103136206809011b21000700204407100341a002c0d40c1ea001110b01540b00c0030b801c554a203181d030207900300c02c8d0075110f0040303a28011130f0080c3c05000c034144680d480b80e007041d070480340c2240e0440c400078000f008500c0040400500d46404480103491300c1251b0130041c2440c0c0d03565070750703000c40203a6041035480d010000b8011080c0020040706070050200d918a01d07150038507040200f60148120306c6860551980440072580f41e502c82e4214400c1c0d150060000d106118602070818001e0200d482840c0c08900c00b00444c41c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 261274829 1250 261273579 261273589
    0x90801061a030411040501080d0e040603020d0f081902100509010b0102060129030c0316210207031e0315091814032803060b030408030402010e030c15120105 69
    0x2503818605001403080245100c00c03590b6000584221011411429040d140e0b1301c1e2803242c075009000c240c006181461300c030303031002d040032291100b560f00560902c1c00900c0503032a15070102c0740702d61340b01088070510700090603c1003840c01400e425181c5003444514800c14141d0028200c10a1400c0c000204503a44440300d040b8202c60740204943c4c0907070085801040028040045595072130300d42c80160303c0c0c0c00788811102e03010344d000315400c0409110100c140031081c0c44044000c02d01d030015061520140c030110151084070b250410350100100d400140400425210700000040600c40c12100300310613042c00f002a001d0400d03040c00c070f08440030020b400a426038081c060016044038001440076070054130f440e4101c3c80850004d034004180300800084d2003c42c40b00740944050000c149075484001081c0da80142039a034664040000d161044c020b120120b1002021a0341156090904000c0c0e0011540460b0800c11800400341d40220a404a08031011a0304010094a204501d002200340c2e25481001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 261276079 1250 261274829 261274841
    0x1206010807031b0c1410090501060b0309031827092109040f0e03070f060e0304140603040c18020408010605060c120c010f1b0e0d12120e100b01090801 66
    0x750706400c241c500e00303124007444c44110020300a980c40c80741c1c5100000182c2ca003481201c004032109a91f9802d820500c4402c1c49003102420004030191700e03604124014642d64000d40c6500c90609e003140301010b680742e45005000c102c00144085060030364140c04202d00340c0d560b00b180c500c00070b40691101003c1411100f0781c19183c0c040a045d8007130810300d0f84070900008010707981e6410700301603450400110221081019007001031162101c41405011841c050050341c9400c16460800e0344244414014036180700c24100c03409106894142c0c4039540d82c10200a028850741c80100601d2800c0300c1c4003001d802a4008100342e45105001b4800941e468081c49841e1080b5030700b800550708050300040004003680300900641c0d810000200300000d800d080300b07007200c2001040214441d1101800c07005170b03400884103030b00e80d0003c0316150749030308045d00c64548201800a60f0010451441e15501040b40c40c0d80c4140300340000902140d4903280c0750480030f4002d000401d0110b001c207681000000310b81c44140290 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 261277329 1250 261276079 261276101
    0x1030f05070f0c0c081c0f0905010207050f0f1503011e1404020a110f060703110a0c0803100308030f0a05060603150409020609060a02010507080a02070309030b0402060906120601080703 81
    0xe805101c00d41000f103d03a41400c00080794804c90803000054003a9007001801180980c6001a494445404402034140c080440200c01071103507a0000700071a03078011030707240e0882c0e4040d500540d2400310310300055003031000340c20700c04c2c0d02030003a0070b040741c07850300000203903050b6038070081c2001688e04100c0d00c46002112610030a605854684032041c0141000d4014194503000e45c01c04461903804442c0f05805c01000a40e4070b451030b4072100c02c2001c1c0039414003076914400f469040c000e01d8110b0281e8018030340070f400c902c00382405500001080360192140800700046801ca034000380c8030701306403581030300c00e040a942c100d0700241814042901890000101ea024801c000303408039001c030110003400003601d0381120990348443c0034400c000e0700d030325035200a10031001c55074000516480e1400303001d451110058100825035105014250000307420507038042c2925000032102500d60740310310000d4414428400b5050700074102054078030300c081d626086180500f1003625201925540c001d030031030489040c2500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 261278579 1250 261277329 261277337
    0x714072c04020d061506120b040e0d0c0c080f030405030606031204030b0a06030206030f0403030606020d1409240c0607080f060906031608150a051b0c0312041101030f0507 75
    0x12030014502102c2c03801d010f51007820040391403003044184440f041c4030350384640041111882645030540c810312415541400807241040200d000380e160541d280305d11140f4070103102e46421400103121440701102c00074011071003190000542c0c0001c0c0c54480d002445907902030302c00d4034041400342ca0701103020702d141480381042c20300302482c41d100c03030400d00805080c14204a0366104088050b884002c0250f12a0600c0c500c40100c906140c0b13401800c0300c0b4207a0081e411500289003520060350f0121040c403080040e2035005840d80101030003ea0303029500c002d0390300750b60500b14501c1e0340c1c180c00382c003d0081440d0381c0050300c1b2107554922055980750403c4400900703d00b40e19002030041d1400086058206201804403810907000540402440c01c1540000d2410703848040e04000c040030011005501441d011020b2189050544000c1041480321049410b060f001040c8204004420015540c1564030125182c00c64181820f00c44070710500d4444550002e403c021108103110f00394010355024820701d40d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 261279829 1250 261278579 261278581
    0xb0a0e01200a0b1b0a0c15050a02040e092e060b0408010e10050106020d11150103050606100c0206121905010b0d050601030c090302040c140304060b0f01080702060415020714072c 78
    0x3411500441c0c950740880c0c000c2c0300c1e08080c1f4000302461040303a00c40d00081d01c00680d80e0f0f003441305062282e07000400341002948250780c410718002200700c1030455107000c45110440c8024284040000c1d00070cc2d0850038405001041c0058017031f005400c00f00c07140880c60f0641d52902c0f14481d03040150780090040c040507a000c108030481d110300c1174560700e40008945091f19a50b074802e0140c60f030201000e0b80300b03441c16408001440310038035002a0980c158065070030314418501543d4082030550203101d8240004400c488006080f03050100350541d41d558009404001c190386410240002d60003034054590a10b00d48000180c40394001e106095400c0056219130345a240b03142e00b00000b0302072038003104042008003988007082e005004050760086205580c04500d84512006100012500c070000a040082901c140030742d464020400580054021035103440c4450b5214120010344641040100484848690201e05050100d842819500340c511251404441c0f600200d21041001584404020b0200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 261281079 1250 261279829 261279847
    0x13060903080301030821041515051507051504080c15091f0e010e06041505100905090c060a0e01021615030504110405100315060b0a0e01200a0b1b 64
    0x4000d0031b41d42d62680c0da52046065490001d04c0f0103003094900b2100908030800d8041c14040d10701500880c440c81d4010718505034901000190010b506086a00240300c00190701307001c0c0081404510846001c601c2c5402c03c6082c2880c02500b607501a8035040180d0140c0c01289100009a820145c0a10f45001c001e00d1200708584410600b0721010f508400d071540d90340801340040100380a110b90341000d440c094803043c41c060511525807500c2030030840126240a003009889480b0501880c2641c81403400050340f03980e0605180c1c541084021001d83c01480410a641180d40c0b06000340140c604c02c0e800c1c0d4504c10382d00c41c0c4045040351035002d0400c00256038680d043e07809101ba80aa68058000e030200440713881080d0100d0100c580c00c0e203c0240060320490b040c414002e040c0b8502d030f186034418000700704182c6040b006900034010380031560104044800e003a221030384200ba5040038401c2400170035a48200e468081544c50200c0e2400b00c5100c1d690a0000c1e000030010440400a4841c0c101d0300c40c0b5140c1d0720f03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 261282329 1250 261281079 261281093
    0x11e180e01090c0b0a1106060d0305130b18100c03020606010c03020a14151602070509041109091b0d02031c021c081509040317060303041a1306090308030103 69
    0x490300e40d0459640e10407060b800300d840442ca010042040e2180c00395285260300700204160a5200e1407500c0e07a20084c1403000684401140103061601450082e49900c1095185143d01103640c0c0070300914100442d40c1e440c1d1645600c00030f030811200301c03411301c50b5000c504000d94030b1105481001e009a0802800524194080c041c51480c8038801d20540b02d5501417941c820014014140c0103400641c403181c454030310030344080300464101640d03590240403801c142c8002540c41215010313690181500c60040780c1040188250300764424002441d070805407400c8804560303542d0101c1029903400b00306403403004050811140340049690068050b00c5023824501c40e00740003d822400c80ea00314811041d807524100600c0c0e550185850860791200801d0420410303c040c64484d080c00c40e441184600c1c1840300198001d06003200d0701d041c1d00b2000090740d4900000030b086000703552125400795014440b0308101c40801c801007a0072948a4103040c59262035000c1110180120b010040c00d5220800041c4085024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 261283579 1250 261282329 261282341
    0x80919060213050301020c0102071407080d0e0103060503150f07031e0c211a040212071808151e04020d0303020f041208091002011503020d06020f070b011e18 69
    0x6184408401c0310383c0c450109007207a000c05540305043e540414080d00f00041d0001c484d07410000e20f4000d022040c101502d090f141c280d0b641142040c400e4044050429034000c1d00040b00500c0d000b0155600c000200820101540003103800c0d025002c900400110164002c0c0305443c040d030707098007081855103083c40f001c9008081048211040c40300d82400d25400021034820301c214003000c0140410003a1608134014030150348042040c0c4210700502078046202d2040107055070142040c603004040c202d40f9145103c110200d9082807100340501040d076941e11004400c40d80c001c205541183e808000045103444442c0320546d40290302c03030050003805002c03a1180e005410283c1100890030324082d80d4030b01031010201c15070700071134000b5004901da014a01d44404007684a8100f40000e0142800d03401c40c10444100d940030081c420004000410706025032503041e102c1b1080c3c0010b0003070380c6804e00e080407816030b0802d110f035059155030000d43c100c400d401c050401d13080300c01f030844007024188007015020103802c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 261284829 1250 261283579 261283597
    0x80306040617030d0b0103050f060409170a0f110a0f24020d1e050f061003090506151302041a0c0f0d0518090108100905030c06160809190602 62
    0x107207a0300c0100d0b080034030900030400c20719032900941d41d54000054000076200c4400107141030510b008100840002d0349100194030443c00c80340050120414503102e440014074941704481100e002c14400c840d42e4118410841500c0c154030303020003103240018000e59840100e500100a511440b104400180700400319280c4c1d0907140c0d042562505900141c1e004a80101521040362030710b030001400d130340c0d86411084001c0016040c040c4010326000000304003c1e04050045e6016942203540805c46034880e03403040403002d910400307964080c01c0c060042c414000700481c2d0135100e820345c0300300e03082840e9651003110121084145171300c000300a008030141003900300c0c5581d0741b0140100d850518403030106000031fa01301c5445845098407026440d00309014018940f003400d01a1540c5001400041c8002840e40d006010110700441d102d0300501c1c00904501501a001c200340c451350060081044035030484c0c49451407690b80b01003c1c5e50b2800a426a0b0b070416001540c0c980c2c442240201c0800c4490b001001880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 261286079 1250 261284829 261284831
    0x20f0a08071b09020d1407081e1504020d0501050108011d0606030a060302040c02010906060f3203060403020a03030c1403040f0206091003050901061208030c160803040311070e01060c08030604 84
    0x359035a00e643c3c06907440011140c100c00ea5400c480342d00c500100f05000d030002d9641c44e04d517155152030115091410f0580b00325148074003000000a980c1400e0301c05a9800b000041c200b5901c481880741a07101400081c0981030102c0c2155001203119510100002442408181030701c40544602041c40780342c0c0e00280003010025241c481c084003584650003201a14442c039400080c441c0503904103403040316000e8224501000c01c5d96400c11031011910b0640000e0040d4046601300c0c5081c0d24800010b4008019001e44c040c051001008145500803582d0001c49010382c4042c0400d0031501c2049403c0003407030b160b9485071803082c00401c0c00320305540603c02c400c91019040301e2403c030141000405400641c68a030001980361420801404020302482c002420040d05104d080b84040e03035003100d03501004095080607100411720940c071580d901d5607513400c0c0350041c154550328141030600800b9034811040010040c840d040340000c0f280e81c2d030b1a40d28100d549980c2da04400c1c00c299928203c903540043d041d5a842 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 261287329 1250 261286079 261286133
    0x120f080a0e030d020c0c040b030c060a051b010e0307060507080121030c05011113050d020607021309060603110f09060112090311030406030605010801090c0909020708070f030e01020f0a0807 83
    0x118806100820910700010014030f1b001c88201c041001741e40c400d0792007600a420041451301940c64400958500200ca03042840c0c49a81d984009254135007802c0501140d907080684c4001c1400012004050b010300542d4140201c1c1d85115059400c00302c28031880c0240c4a0b401d003407aa5014074010004130542c840d14041c00c00d100039488041c00d58103241450010039a00040d18449009407100100c010308058074010f16085c0725400107040d6004078180a80214041d000326040c5c40c015901400d0340f26402842008400d49a0900c40d070560902018140a20070302c806c18080c92800104071845098143d5406007503000c1c4c0c10100c80500902c08040301885540242418801b02c24000740c809013102e90380c001001403800000500c02d61060b408003110030f103409280904654000300e440190b0300070240150b9511547e1a0020003031042c01c00c0980f44415005407001007503840740c1045130f0074100b6421180e980f060600f00c1a10741461100c000e00401c010002080092181c0e00f00c44605410f0981e00108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 261288579 1250 261287329 261287347
    0x6031501050c0a0b070e030a0b160c05010905010b0a0e060f01050901091a0d050106080709140d121107050a06120902040b0d0b04380408040f080a120f080a0e03 70
    0x500207550204455003004e0800b00403c056100c0e20131104194228010142951030752544030900d80d0141140301c50907500a03e00c50068001d1900200e400e0380400204607440040c10b16a008020400b601c92007406401030005064181c0d600b264040e000040541c6a00800440150703415841160418140811050700156100b00c441815110740744016a00741d070381940820315800c6442c160450707020310440f4418448410703401109070b01510b0902201c89024042040000e050001c51080105540c01c080d140782c500d41d511440a00581e1040c0d0100c0c0d803240e8480040041142c0d01d0b000d003000040d0405610743c4810300e240c118038100d40c005400000c901c0300c0f0700d01140b42c20350b00010903100040540d045c8030400100c07081c901c40d40004181d00314071103914002849810b01c0c1115100505c080000c01240904c4038540444008080205003500400d5035109a80d8036030100140690703c2c10542402c039800d07a401041d4401e10500c0a0350b800300c180c0d8a0194440081c40c8002903035020340700600c111310b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 261289829 1250 261288579 261288583
    0x506120d180f0b09030c04050405070611070e09011b080601020d080a020912060403120c0c2004020c010c03050105100e060a020a0b0f06030d02070e0a0209030c0d06050f010605040506031501050c 85
    0x80980220700f8440d41c1c2e00b051009143c41e0040b0302c6180c030b00661410042001041021501e030080e100b1501d0508000341b103151040f40751440c0c80d08102d65030410344090000420701540050b407608290640c801c1ca400032014296101e2404840641c05a085008100380d2544a8559164481850ba1006041107a0740012400340794903404401c103558451000c0c00145601705000d044c030341c0c41003082441090f200f80d600825440b400d08004000c03401c0807204d440e0031898521000c1501001401c01c40d241c060000480d4060508040444042480d1500205150810146c040400390b1143c0b01c5090000ca103c040c400d140d0700c2000c0c0c04007103014102e0f40f14005003020901a02a84050b44000c2e603e040000403d410b01000301041c1d000e551004d8002c204050312a030a03103501403d1498010313181c451072400b19041091222105501503030301c9203454100042548000d0107520b01c2c41c1c140034283e07203803001950b0f98072a80c0100740d402001440000e20511568000c94955601072420a040c03c4803014118 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 261291079 1250 261289829 261289859
    0xc050d11120a0b0105070204021605010908040510020c21070b0406120e0a050a020f0f03060406060f060908030919050616060b0105090a170a1b08010506120d18 70
    0x14403600000298041426840c0c10480d030810302d521010455014030a0000c1c00034800c129000740a284c02040504000c03185240560401750008004d20021055140104584e8458020184900203030b640000a041c4000340c2c1d482000c0010f000902c050702d00500c401c0082c54102c603441d11178421202c0115011071420050001031140da1143c840e103d901050301c1082d29102e6042c100c0c9640100d0300302c8040f860019a02c00169010348002c0c100c0300c01d2201050451081c3c00882d074142c41803005010030400c4c02d074010f000b114a105148a50240ca82c5001c40c1c00b01c849200702c91a0340d00034084404207141c1030040308500315003070b4202c0d840944d0303c1c00412943c1d000703c2c118000c5650005401002e0102500a01c1503516003440d002e071409558000050304003007640a001440c0c2c00d40c0450003462501041078240d841d0700088214440e458140070743c1e011850320300a81500d0350070303d00480c0c4242411802111031402a1001d000000d9002000729140c01c10b6501c0c90452030440880003c0202c0b011100c030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 261292329 1250 261291079 261291101
    0x30f02041d030316030905060f0c16030806090105030a0b01030822061205060405060a0909081209030a020118020a1503110c0f071205070302060f0d1401050f1203030601030c050d 78
    0x42c540720b103072040100c911207803070060035424541001c2c3c03210000f802c04907906500000d90b0b20140617649809030002c4483c00745d10391104020304100341010505402207402441880c048884051903078851040c0341e1664100030009004404c0580140b0028900c0d5003d400d0190122820041501e14590781800b280e81650000c808a4013882014001c00301e140a0305501040a0340e003408941003050228130204074520420310840e0785c4082e044200402c0008440d6039028414880c101c6080c0005083c1e201e0b031005940340701641c80c04007008105080b1842c82d01c0400c0d002050f80a0103441c0c40c11580e640d00811104404056840040754507040401001c1e00e10b80b1103207001040004038a0080b03e01c1d112090700304003e414442c80c0c80c2d0f80050341c009a840d041d268195542a00d910702c405907418180540b0182c15a50341c1021601600c1d0058400668122007080741c0c0c030043c112a003814040c12a0400044c10410780041000841030b5000c0e4110160445c02da01d41140741c04003200118045508208903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 261293579 1250 261292329 261292333
    0x191514010e0103021f020309060c01020d020d14090703050d0f0e090408130509090d0c050a0f05010b040b040b0a150c020414011406160b07090806070206010627030f02041d 75
    0x14002c4d03080a011944920b10100c0d01090040720a85000e980c0340508110903128201c00204041c0700502034042d00c5c821542c20030195110342420140c4006084441901c80c15003650360000f641820000810340c00316034200b00501020160103401b1030754101d00e00c01302404d00407c41520b500d9510f072024442c0c4594000c4580507200c88044021942d51502a03201501c207159000c181300d13480b4004110f400c0420020300b010b50490b101c91603c41d06000d060880a0045000c10400d0014010107401c851884801150100038036903100c000c02c0216544080107a801618842c818003070000480320304880e0800a0034104140780280d80041d081d200c08444420740c90126000421006000500380744103002d0403540c160400a01c20151503100c45850b43c040c00000c1041d003c0781109000d140039102600d66030064425a192070200655101002c2c803880c1c4c0000c501d920300381c0400100e070004050503406480d850b03c60b2484d5403181440100310301816a40265a130386522510341000d031000c220040f00c000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 261294829 1250 261293579 261293581
    0x706020912160501020a0201080f0a0615020f0c01030507170a0b060c01021e0f031603021903020c0c01030b060702123d110d0515060a030204090e191514010e 69
    0x402c0b07119a1040c0c1c092410740d44411076200050703801464890f44004450700300003e65423450f081e44064641036000155a6000040c40311200b680031078051410100001100c200f0480d06d8011421070f482115450002104810400200040310f002c03035410034003140c0d0120b0080000310003e4141e03480b5001c00643e503035001421000038040c408030038004600d54000c290510150400901d500d2000402d101041c011b40114409214004d0f81503a1031601c1e00010101140c0d00c240026000b175009070052441d0303120300c0503220710540c805e020b500110300000e001607003491813a500303101c0c0000c000d0b01c00008600540e5251901c0030740c58403142d000c5c1d01c42541400c1003008a4140b0807641072440d2449144941002c880f06c0006048004661502022003000561a99122103038500402d2484950394071401c0020703045840c03a0b05401034021b0382c103410400c0000940e81030596540d01c055020048100c2c90950140c0f000c14680308440d50340c0c244012022450350303543c0c0c580b0400848240c000ca41140b003148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 261296079 1250 261294829 261294853
    0x5011205010e01050601050a1107030b010e07030b0d030e0f04110f0a0809010e0d0c030e0a030b01080111040f0909020a08010203090106170a2d150518060103030c06020706020912 78
    0x4080c1e040754032100b1000300003d04000000910303071312440c10707400d052003074141004c0150681048000c0045401c1005450349585074144600003c01c20740740000041e08003103407640c040c60b140c403658800c103a050f1202c011b2101c50300180424040746031400346d80240d80b070400c5d510040d0108010443c182000da080c030741c3c3d01c802950180075040c0113840c402990303150505180c0d5080000030400c244030990704111600c003405140403a03406491212454220034044000800c001e9024003440c1aa10070300000c1c45001200401500940102d21540d00e8a0082c00800c11200819a011000380c900242450250640b03c0c95460700307981c01500c007211960b645410811200119207039002e08505180c1c0074209482094a66201c2a9070034218480c5010601701d0100e000e9003841407a1080c3c90317100b20b0395100f4216174107210700101821511140110019400c1102c00c6501080c0c3c1c0e41680d515449100710101d440d1075003002504125005c540c4541d0030030808015a4817480414410a010390007003440741e51071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 261297329 1250 261296079 261296081
    0x6030c020c120a062403060b0a12030c03020105130206030406020d0207051902190503100b0102011e0b030c1909020f07170a030e01110409020904021603081006020d0e01050c0a060501120501 83
    0x140d10101045405042c29517074200c810482001200e4010300d006c01c039200d00c0c0c000035018407215400f404c0c1c0d14984d1642e401c201900442e620342018045e4000300314075517546102409030b081c0b21000a6000004100080010b8041d5014080d0003031803000040c10074281c0d56416160002d100002d04000d220350070fa000440c50040781802811100020303c901251030507003c2586d4036007101d0412107007512660402105d91003548000400210852411a0b662001098400034600d030074665000c0c0c01884045042e03820315000201a420704450041c100c07500c0c001d9044001e4200e0076882000d910b04021000c003184410140c0038190541030200c5035141c90002c000f6045034809100d00241c1c1c1d0415240041c002944016103080b5030510401603510901c5000050080c0300f8201410225200c0150301002e260340191250300c6585120803a410b0142c440038181e1791600001819000989180a07891255210314060500002040c0031a00030306056a10101591000d07003004074001810a101001d008003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 261298579 1250 261297329 261297341
    0x1407031a0c0403030e040f1113050f04020a05160f02060310140f0609010c0213060b09100201140402060f071718270c0d18020a06020c0a06030c020c120a06 68
    0x214103074103480c282c40c5a50142800b0f80385d4100c0c03840340380d44400c824104540303600048501c01200c2036495541c00d00360044c6000c0182d42c05102e020b80d5110704615460b0a091088400c650044d07150103007042c000d410108210240540b04407070340c2d005000040010384841e000740d80070703011080c1411030140c1403040031001d83d002c0c3c1c1d140328826400c40940d5003454030b80d0700840e0401602882c1080200065001086000320408104402245014070020b00059210040c25429001b101d0658103000380741022820f850010800c19507900030040030400502c0c041c0018402050402c00e0b00303003401001c4e1a9a0703140040032901c44001d01d40040c0703260460356042c2e20b5072070300c510031034228000d0900540b2421040d421204440d03500f51158001c20758886200090741d81c2100820014070003080064500c0a2020fa520402c070301aa0f203a2002107a52030011465241580020f00740307082c02031500d01d0440140105e400c820041d8021010400c0b040d071034010900e00c04031120402411402e8003442e1640890354 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 261299829 1250 261298579 261298591
    0x301030b0f040b0109022508070b0c0711061c02030709060909020403031e02010207080f0913110316030e151b120703090c050409111503010503191407031a 68
    0x1001800700b1002031043c1c1c0740a41960255a401621020030040d0001614400c841c41800201c00c51007140422031154010043e003841400c444441d034880d0505004a4003d41000400c100000340604520342014030241807840d99401110b80d60900b1612031000f01e0380103a55450015080c04001c1c42403d800825050080070a01e07021031a040c5942c0300108a110b809003613441d5200e070707043e0f5100214405d40550342c040f900304690954035659800301d5101640010051401494004200701c104120b40c0b0039055245800110540b87d03540d40d00e010140f400c0b11000c0b403c10b040d55000c002000007420860103102d2010580351a0b00d40c14241c4c98080100500c0516203003141c02007280241d00040f03410354a03041042410085034000540c40c03c0c3d942400d43da000540c0151824400005001e4440c0340359545105c10345034a401c4401c80015101141320074020140c041c2e00c032010090000302542c0700e5903041d600032190320310b51400301022241002c0c00b0754025a00c00141d05080c1d90b00c8100c00710ba140d00b0031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 261301079 1250 261299829 261299851
    0x712020705010e0d0303051e070207060e0102030901050301030312091b03051b0109060513030b1005010f0305070912060b0d030e03070e04030e060318160f091503080c1906020301030b 80
    0x140458002071440000c4c0c000040c205034844c0d010512600c00045043c050071714031041c9100500c0d10034002996030b105481030394002000500d107081c0c0d80d400442240c000d0f01d010b940c0ca03481c40c0c0c01d40d20142c6000340800d0180d08843da4592000c0040382a01c07503101038061215081c4a1224954100343d45002c0c02075440303003d10f00d50380e03200c0d0700c1c5617800000401c1160b0550611940340c01c40001140c19480c9a41cac4040d001100c44e4040141ba0303070321155200141e40302601c3d4000040481d400031801c80340115442c0c00071619940c010300407100c2803645000340500c1840c02044040c1107801203103565158020860106840c0500702e9000d250501060000d014454142d244618143c0c030b00401c40e4109483c014024000040441d00c603102c411040c200c0905254212007481a28210000340712a85200d05030b20355800030408108512a40240340094600c4610f00c0c4071181191103104c4a07510122040d6041e00c905003042d415400c0c01d030701c3c0640711030003900d0058072580345080804c070069000342189802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 261302329 1250 261301079 261301097
    0x50d270b2d04020111160e040b01360207050106080303061c030806060f04031a09010f0608060c1803070f140a12060b0f0a12060c02030901270506071202070501 70
    0x1c0c54020220701d60054091130001c040c48004400f8504014420403c0c40b040e0540f01004108400c03030b40c0781c0c2406588240d5680344240c0ea0f40b1408681152070311013143c402c40c01c405030103010a070000000b449039504600300525010310360f61042e003101d0850380030400a400100400c610303841d02085464880070f1646d203101c01040103581c000c20364200202001c2c482c09001c03d002c01d01700a07000944014541c44407011001d841152402050043c00300c8824020390300740041d0324601000c500940040301c803048010300c00c54031118010211350300041041c074916a18001c1c40340317040e82d0130010711000713169182d0301003541030800400c185038680500c030540c0103001d0075100300000015188800b00c6d40d078120034005240c40180c000140481c6070313819915488810810007082042c196a502d1400c503114100420111641e50010f0340c0f0780c015640141c1c0801c8080020705540401900440b0f03610000700e442c43c110f075444500241d2240c00580c1c1c2903450807083c214801d5815010008040600001d0900b9075070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 261303579 1250 261302329 261302401
    0x3021f0207030923060409020306042f09031612030212090105180409060e030a0201230601080a1e0204051008060f120307080c0c0307060f050d270b 65
    0xa6485078820803440c14124100d41404d019a201c140341c41d5400241002c0e5256030321402c05003e034006a42e290b04c1a450861200111102d440c26090007a051020b4040500f030b5400501c4c0c0280c210743c100d141c040c0074503410080c0000e680e04083c00606000c2c0700e07050010740d040c10f0082c640160b414059680b06020004540e00b40c0e082010782e000302840404102c285403d200200380030b80145100209412700704104180c200c0408801761401a68a41c003c1100070701d82d031a00f0340c226114048060b104d00b074600214846500c2038030a00e50001503210007284000d650034100403e50142020a56845d9000c5000d0029180c03848041184038003519255010f402e0070800640c001c0c58000050744102d00140c40e1103030541062003580c04441d0040c1c00303d0f8580d9080c1182585604800ca4031030320a004002020400701e0041c1d8004818000568942d420842440d02c80001000525188141c9244500915544041c00b0251352212440fa0844188a08080c6000040101110184800d02c5201100010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 261304829 1250 261303579 261303587
    0x121f0e0c0412020f040e0d0e0402030103020f0402030c070b040507150203030708241e0306070203030f22081308010b013209090a060311090906061e030a03021f020703 73
    0x142ca01520303902000b5602c1d40b0000304080c0181d600150010705080100030401004110100d2007c001c0d19408003caa4041c00c00080b88400d000003035109402c05004005802c3c590b01a5900088031880c041c68981c6580b140d0050303010031181200c90f40e029103030901a8045142c03010b521040c580c00107605509001d080a00b030340b2801400300104414600980c4000d085401c0900c6d80309001130218148003622244e031403900588240250b01130f1003208086550584000122445254503d040031750725100c0c903540d1072486800c2007980c0c03d1000170802c0440801c1816004091a10183e50101c41081c43e002c1c0d0305007035031261120701d8140005031183c44038001041c48d030300c202c034159064100a035030100c91000c0b005008400c00e4540281e902810058001415441441900d004087c0d00303c0440108082090780751007114031802c03039000b2001050003420521542510f100c040364500c0c03112011031000c41d1411050301ea007680107070f00490b605880d181144032402110601fa0100b5460010903450140c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 261306079 1250 261304829 261304837
    0x4080c010305041208040c0b0408031306080405060c0715050c1b0601060e210d050c070504150b0d090210020c041a01020607110106090f09060b09010f1505121f0e0c 72
    0x7040c0301786100007a08116107064480040d015840c1000e40b242d440340c1099540b50000c084000303100c14072100104103e070050303032803034880c90344040140041c0d51513910707281c00c60700621021580c4c00112025059800f06c5400340c0e612070200804025201d0038501c0400d0324022500400c803000f034100d2001804240c1d48003c410784200e4054803070000c0300501c242070600b00051901c00320200d0140c42c1e400c000260b172280007412003004010850704a9504c0d5010030049940240103010301c01c500341010001612450094003141c90708050000d24602c41e90042444000741c2c00030400140c2080c8100741c2649094030a140410b840302480300411610000041e40d6000054201c40510080c0342511001c0030003500180080c1c22030490501c481440720000c40c01401031079108540719410003070045041c2c208045554100c652003413048004a01c1d0080a0810003ca421008100b2604010030a040d011280049014400640750710b000c02e615143c0c6441b032f441117038004090028045090040c0b002d0910291 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 261307329 1250 261306079 261306113
    0xe01230f0907060f17150111030f09040c18030803091006030f03030e19030903031205060d080c01140108071a0c071526060f0f01120c031503050304080c01030504 71
    0x4c0c01c100d4060841907a0352009605d201040100d030318204005020001c1c42e000c0d0480c1c007a20f40102d61402e2124041c1c5078001d60600b044901410b012000a5150503040111400b1071402c00031807134001c228013541410303219003094502c542e000080c01120302040028880d1307009004410411039045036110000d405101e071018003016107410540f4001e4600740210b0f580142c240030b0604002940d40703406004241c2504c010350104030001248084d41c100703801000d1040c6402440304039844010350300c4241941010355a0070320f17990f85003201c0301614443c80c0c2043c06000803000802c0c0303007440d002c0c801c1c040b00381e85044422808000d10149802c4400022901c00740d80b03501d00102501219450122000700820100d40040440320b54081580c1c140072441901881054aa85a43c5041c1d0000e011b0444080040c060006802c6403044044c07000c203521403c806801460041501000e005480381c00c80303200c2e0030a8645410004040298000c100000b14101070203007001c0c8010b20b05500c40a4000c0705280d18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 261308579 1250 261307329 261307337
    0x806060f03030f03160801090606020c040e01060915080706020a1703060102010912030e010605092e030c060f030506041505041a03010204120519080a0c060e01230f090706 75
    0x240086654144150380c5400451200141c0785c0ca0010711018501c60052000d901003160000045051081401140c013a2030483c0c00502c058001da03010320000784a680c0c0034080039541c500001c2820b560034000d04400d40708440308440316605280c842c03410003a56500400a40d40402001000114030310764040e54504072129094407079452400607401740403211f800520940306c460100c42c1907601a481306014683c42e4008003c02a207030824001c1580081d1885c405508000b0302c0101080310000a05010001000c10b0b403d440343d413561031202c4000c441c0c205101103060001c418400d00c0d07052045c1030b44644100c405000e0b519181c000d0448015450084500441d141d0441844540f916070139405d40041c090007c554aa83d51505044483c0801d50308175201e0051110182c1500b4401c40c40c08a9240c001c03074801e10f482c89621b000d45400464a10441d68aa12284000324280c800c0c4a800c48005002000700014050f0701a03114814800410000d829040d5400740100f04000052440c180c90741810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 261309829 1250 261308579 261308599
    0xb010807060e060c07030b0118051006020c0609010e0a030602030f0901060605090111150a0b010f02120904050414120a03240e070306050a0f17030301080c0904020d080d090318080606 80
    0x5500ca0902020b500047c10886100000080045117243ca00d0186920380c18100a1a02c4e088140022902103120f404016030060300000c25524040c4c0040c4450201418241c02c401508000b00e102414a81d005507040b5134007104009900d15801c00c0c0660260f411002044000e04083c4041c040d401926030613410003010362060310b18040c0030000301100b44110a02020546401e50540000d495004029400615408030b81d40c5020300006460b8007800980e15001d0401c1c4c40d040900c4014000140140c51440003091210b80303403242807202c04544400442510355801d402c103009420744030040d16002d02001c03801171302003040c840c2c011490140e0f80c01380d140c0091a21007450440141800c1e822582d031000143c0c1c4009803064150940004480f44a80c0181c00c0034144500039031240401d21074010b25401901c1000b8803442e10600507540070b0710080681c004214507459042c500c3d0402e151903203206030f4a0700c8200034181c1040c2591040e50701d001d0f1000125042151280e1921005804180520038a20b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 261311079 1250 261309829 261309847
    0x718031707082a0c0307030213050402010e0612060306010506040b030411130e0a05010b04020403050703030804031b05060411092e1508040c09060f0b03071112070b010807060e06 78
    0x100458207011002c0c201c80070525070070040b100c0d060708040f441c0002e130301c41e04c0719207021801c010400c403040380c1d001000031007042101c61074000a08001070081f410800c0581c0031003000d03514900030341880e08440840456510f4000285860900107800062140c5803d02c4104841410442140d5006500084146d6040d4900011130041a8588185880c6900b02030b0f2000e0581030000740301c1c0070f96006000a00a149801d000d100032403240d40030103800d070b070090721050010a010340d107040d0700710780300341340c5903e486950f10080c0320485003040d411181c941084050006201440400307030003184040750317074aa140c2001d80000510341d00164804084541c02043d01110000c0a60514001e09908021f540300309106d80000341000360132101100d5036030041c070300418011020f1080030161000ba0801104860134020414550f4200901510401c40320703801c80801e091041c003c80c03110028031b030740c540d88403807081c80d0040f4509016008030340740b580803030001c1000070740c411480c815580040d50700c240c0e100460 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 261312329 1250 261311079 261311093
    0x3040209041203111c0f05090a02280b03010806160504060c02030708010212191415121b01030b0f03070b09011806090603110703121107060f050718031707 68
    0x25102a0111500824124011700c6001c0c0c103084c0f240c1060208201d5401309202c89401c07144292002001c59100c5a80e000040c00c00c2504004920050950014004418040b1014003400da0304880107060000c401005000380070400705402c60b003104092a0000d8544030018054003980c0f04001c100030294029400350346041c800c80004d00490740017076640707950100700000e01d032206071604000411126402e07216048a441100c001f20400584002c0a480e00440340d05551400340042c0e900c0200640601a004420400c190490502c011004001000c9400140456201810070790207401c28a101c0300c000da901103009810f89010010302529002c0440c01200d00c412210613400c0c1c90041d074480030078042c1d0404c403c0d0003260301d565014007941042c13007585c0c501e0340101100203011411a4402e419116410303007042c8204c1c9280300b2003d0904005846010556200411400040e591141072200070740d40316200404d4001a0345112a030785245a40c0d00b9036040d41e0080d03c030105200400c48808010b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 261313579 1250 261312329 261312341
    0x604090e0601080c01020f1b040e0307060501030516050d0227070207150f0e010809240615210604200306100e0a180e03070f0b010b03040209041203 65
    0x28a00100011041002203603903034982030164945911074426040750561000500c004404800c80140900f04d00c0c11900e8501ca49043d001d5a60064851102400c0080c00708058841c5501446000ca89545181082401d203c007003410031004100c650000c8c01562200c03100788081640c1038a08030441c0c000502e800b01c0c0800341152801c00808130b101441426a40041c2c480c003641c04502c0c0c01c0300308942c2d0a005803524070f0809050307030103ea800c1c0140113056000c1c840b078560007004401034940080e084410006088061008101c1060b231010902c9a14244500f902008000f02c0038520300d481659030741c400d0803000c1003410402c54402a40007801580780c0f6045540c148003221324052048002e480d4248090b002201c00381d0250219901d5119014403500c22034501381c502804480710241440ca216401160303600d01c0c804100e07140c1001c1c0603842c3c0100000c1c040309014200c000d0341c040c00c52600c0c903141501039020030b0b807080c4140144000b5a443c0300b0065007283c3c2c405001d9944840c01c610940107000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 261314829 1250 261313579 261313589
    0x33010e010503131a070e0d150509070509160809030406020c0d061e0b091014010507030507120201050601020d02010e070504020919171603170304170304050d0806011b020f0604 77
    0x84e0150091000038000d10001d02859441d1038050b0401503c0303041c002e18140803007000d001c040040c51012000740d031560155402204210540d0300f1980c4132000b040900b0b209030760007481310400c0e80501c04040d600c00e0b00381d50000d603054040c503d07240c41d0010082d40c40e1100680c0034800d030f50480c81c400c2001010391000071081c2c0d000e4041005000501d0342e140c01030103140500d50044050100040d4841d0f1a03071001410f07201c01e035240c04c000707403007030001100c2e65080004120180b2804100c01030102d480025510021a055400860705241800009040c440216901415a8101540b503220044040390760029105d09035001078444c2070329400121258405403001c000d200c440304012806000861004c078003e0040002c071204400c1501809038416441e12000e0142401c0d040681d9030200710728000d581090007a5103544100d8200082201594030a07142140d665200c3c1503002d8160740c1000070f0075404074007400c0c80313624100d00380200003511034923440086c0f00360b510f495149115075072a000d64000c0c03c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 261316079 1250 261314829 261314843
    0xe090a050106120209070806030604081602040603060c1e0203030105011206053c0306150604051e0901090204121410060b0702030f010e100504110933010e01050313 72
    0x181c1d4400b0380410183c26200143c2c0203c20b1200040c400170f002d8045103025000290050841e55940d07140c035099038009208801d640705440c1c600d40051303039650142c20040c40c0203440005611406480c081e25144504030034007417101c183c4081d9050903030040280c0f81151030a090200d41c01503003807800b100400340c80d00619030007040000e443c080501c80c104d152070024034980c20002140201da0300f18601311303503018040d5410b600580000d0b21480c5250320f80045404054140750806440b040014004a800d4400ca0803214143d4041e00035450030030207036801000741c4201140b0302810103200300d40c14001e241000c0d040c543d140ca8074680c454410042030442c1d80c460b4401700441030300c80c140e46401d940b22103000ea01c01d01c40c1480c03002c4826018480e20300d46000420007030450351810802c00001d00002042601c0302c01c240c0a801599484203104680325030516050302402101d6241c01001c041d4075a8481c010300c0202c0c007503070b2005036000802c1920041e400d0074400c6d100ea50348a00c1285034071820200034912 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 261317329 1250 261316079 261316091
    0x40f03050c0306060f10030f09050102070b1e0403090b0304020112050c04052103030f1302040504030f0f0305040b06121006120b010b090604150e0d0308060f010203040f0e090a0501 79
    0x200101082040032010704906456035502e811040040c0084107840c45544560f0b60b100502081d4081e5002804145e0140c50100b08240d058545031301320380020209540381403c07003007008804090603d042c490010f0b10b0031845001e0400b620010304c000243e000c1c42c0384000380040031605581c0660002d841c441d61142e0144080e190420748002950030034803640d8001d101810f03074002040e000c0c82c44c0c1e03d510a8500300450441d580d280303041400240c007070200e40880354030002810161b210340c0240fa00c528000d0721804403001c0300ca140104501a800a1301e02010b141c80d0601000810400e60300b604072104445404850f0701010480d401c2030256035491101c0d9191100000300c102d02c51080c082594050580840c40baa6101c0c200e40c06c61040c1c802e641d601060401c0140b2030303101072110342a450f061900d0f012804c910041c5c0424000b50070150150085040d41c030803c0344c0341c0313490303412244007080c00e1014504040c984101440c5180d418040d600000d003c5000150b00c60760200011703540550860006d21803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 261318579 1250 261317329 261317333
    0x7050c130c14031e1b0a0e01080c07050c123c07120222020d0b040605031f05070c02060a0513050105031e0601051b01060e0f0c0717040f03 61
    0x4110840001011421100c4581054075842c0c058a108040000144082180b88480720350301042c01060121800301c0190010b8040302c80001401c0408000c0c2c56441d103d004d00700000d804070304000d00004c29960100f2605d00040c0000c0303403c00444000b0346407080b5900344003150074185054101003402d0404c031341081e401010070b400483e00c0140c100c0510201d109204159070344d1182814040d614104c01c2881815005090846640d0780014803022110201100049180c007070740d2215410700302c000d841300c048c846240341a20443c070040074210010714903541d014848035450484400e0001044c0d40e6000050042c5000304107481159500401c00340d65941c020002404a4000a0f00302c1d291540b540c401041650150302102d003e0070f0340502d48507808840b104410030105000b81141c0c10090b01303015200c092103803140c50950101800b0004241c1500b8960101103107040144441d0126541005114610702580101c80f44a508101c4440340640c40d800380c8480c920456010280e10140c04400000f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 261319829 1250 261318579 261318581
    0xa0b180111071b060f0c0804150804060f051303030b060906160b100b0706090c05090a02180402040e0621060a0207050c010c120e0301060801020c01020901021e060c07050c13 76
    0x4038400ca02c01030032690392100728090a03a650080802181158001c0600c050040f030301040031603c07c12241d85001d403140c500101c40000701a104010403115010b000c200030f070300e015070008591001c0041007a40740051a80c4c04007181020f0160a060b540e2070020010780764130b03041754626800130340503d940340c504094030310200025003001d0300c840c4c00c6080820121901300d0074400c1220b00c112207190030504252500c800070303c40c1c41d40845404090100000710303500e0300035440340f1500080400603110740c0c8420010303009628249510b0b12451041005010101002d151a40c1003003082e80c0e5000480000b00c000808050360440c6030310144101070400a061949400030861184680161007544101c14015901c0d0106800010421065294030681607032051581d1074194100034000701d80c00741d0b5680c0303890881e8810561184e059400040010543d6010400c29003141050041c1c041816108982e007074950b030014001100740c41001401c00c040c05800c102c140d11211004101a0719503031404210341c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 261321079 1250 261319829 261319837
    0x10b130f121a070c060b040b10080907140d1b0b0d1a010318060b0301110309030304110d1505040309180507080702010b0f0f0d0818040605120a0b180111 67
    0x89003603101185038003185031000b44407402803100c0d86031081442126a01d20b400340400200070303508607945400010301d0b82ea030400f01c4003c00959890b2180981401c02c6100c0c00c0405a40148540300741c046142065600d8022202a80603000a030340c04001c614243d030300300082d01a500040c980b260106484007208100c3d4022100d08605619420080784150b00540070f03103a2511070030801c108260260fa0214849070000080183e0007000000e1042c032174242c03460307542c0080c2d495629560000c0104000c011122041c189141000c40f41009e02c1c808aa8660640543c0c0c01c0c0303003090322500c44c400705007054080c080c0703007014140002038104900000040c0e103004000480380c1038001110500450040381c010305c500452403001400e0b0301403041000050000c0803100c002459005810020100b02143c6d40304050f20326600036481030002c00e0074a00402090300d501e07800561044140000d009010b01c000100d400d9aa03074880382d4080d266035402c80f04180c492049605451079402c100c1814407d003400c600030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 261322329 1250 261321079 261321083
    0xc031205120705190305010b1e042114120a0c05070515070501060f051305060a09050702060a0e030a0c120e0303160c0e060a0b1c02040e01140117010b130f12 69
    0x214202e0800f01400300c051b10303028811180142401c22030b810501c1000c8001c800b0282e86043c0051409907101c1c0180d0064800980c3e01011400c003802d07450800002e014400385000841004145205d1403d0703103004640710303042030b54007401850b0030000c0400a0501c254402880014410282d25441d4600d80c0700365400701c002100c8a500e040d0010035110000c0c040f0004ac0d9001402c0202045e00c4118020010000075100651000c6025800070758480c203070042c28412081030380504200d0500214000681d42c901d2801003d541080c0031039411181c2c40300500d071486070804285440300f07000c640d003902c5110781c589526405000c0001c0700100400d0842200c03a5880c0310710310342c08040da40c0b5440e60100c0c102c25200682c2c80b1201904c100844000301024003032404218070742e12000c07030500800000f2070b81315900c0426081e00320801000b803a040048004050369081c00d02443c108004c000c40c09410805004064101c2c501141c070781010045540d544024021080c8884502e94583e00c260105c40450181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 261323579 1250 261322329 261322357
    0x50114040f1a0907050d060906090c0f0b04030512030a14100f080f030f07020a0905090c10020d0c02041505041415102c030a110301050c070c031205120705 68
    0x340c9400c0120000c910855103c0e000e00845410541003007088858a04151001d50b218081007020a003c4d01c504580148200c180d2079065240c11510903010406911605407102c0c00e20042001ca41b020804211040300c100c0c02d035507641d41b034903160001450701074014600c082d000410401c9032000740c06000b0641c3ca00c906881038250742c900e811a0340706070a481189460b00241b1614180000301000381203418801440d03400216125403e0f803003118000c50f14140140d11401200c8643d003000054090300d000d091010b080310031042070f0081d041d580d290364024091a80d680c200f001072002d2450440250000410601204030000013036a20110709403120004034140d0003200440d85000311217050411455103030b4004504000801c503e50100c01e80280307038411001c005054060313030180000c2c04e00610503258414418030708010f00d821143c0c010a0342d940d0400800007540071a407506001030440e81d015a024440c3c164100044a4501412501d02c0504a102080c0055a60410f0281c00d07100d1140c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 261324829 1250 261323579 261323603
    0x1409041806050a20040b1b1c0e01080c03040b0a0f0c0504170c0a03060b0319080309071e090207150c1e03021926151504060813050114040f 61
    0x2c007030081e40d0000d03070403440100320401c01001011141030150001c0030351f45501c0090034108000c0b0f10300b4814004666400e2041c42000c583c4585d401011048080a0038a003007421403820244008492001501c050301c0e510003100001c41c2c13100c854012858282c6009004c4c4048040701e40050a10740250003404038542d8001000c0d100c042c80001c18291f00d00b03008010b07443c401c0c61904c81741c00611121280c05c2c0c060048420803034040c0d40e1000da120712184500340f4269245130204d405400c1c1400e41c1c22030304d040d40120641c0c072144040318500300165403c58200683d155058070745000c150341159403c900b011b0074111084895a00030404e0004003030840e905143e08903407040224200e118008207100c040513944841035905118201010304600c0b01d04800c0e081d40103080e12881c2a07102164000c5140321708200910a508018a0017124111044485800c0a04040010784441c6004107084c0408900d51094000d118007500002c0d010f8178005021359003401c1505181a83c803148010540d0801821300d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 261326079 1250 261324829 261324851
    0x30605010506120c0706090507120302010f050603030a050f07140a0308010b0a08040b060f0405010b1b01060312030c050d050901091406150111011509090c0b0a1409041806050a 77
    0x40460f04407044068964005548850320350b0700c42d400001c002c1e0b540d40c1d5034241c040c000070810003003c0080c0c082c4a03090f40601c159450b0007030079180f0300c2c1d241c9182c2500700700901205403000429030f0300500a03400c003551030704158111030040f0301070000081c0c600c030400c0c0c11500d41d00c50045404401030340070317a98503422680c880e00040c81c00e20854003140c000803001c00005001c1140e1074071058000e240244500003140010b4005403d8550030307000882c510700c001402181d0000900ca104007848081c80007806254035685640302d000b2a5001d0301c0c8285a150010458150b1080c001c40d404103401c1e4408100303d0134480e0240e030003030000c098100c502403003843d904d801c0e10034000b50052007401649805000d224400004607043c01c0501e159074615074035103c01c440190702183c00d16002d4444c0131400100d005441c104102c00030900c1e882242c80741300c104095100e0a0340106480d222002e080f806c9643d4079660004100104102425003e0031529482c90b00100219900101d000340880d010501c4015401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 261327329 1250 261326079 261326089
    0x608070608010e041506080f0c0306060109230609130c0306060c020916020c030312060906040c050d0b060d051320010504060c020d06050106021e0102091320130306050105 75
    0x207009200f80d1040c0007001400184040d03c030070001500c512800719040d41c0d50f0030400c0c0340805c007066540381c98105900c00000d906080045503070001007460044604c0340b0300309414249040c051441d6450700001e43c10700603107403601800c84041c100c000d4601079499140d85d0740c007401001c10154540020341401320000b220351103141d41c0524180c006150035110f44440c1d940c5c1304803200079100e210550051031000541660309101605419100c1e8100414034a04481048100c1c100240501d00c5240381c01c803805403642c1d00000742c8240c04480d200018909010318001a07840c0100c8000011103800c000404c8a06616441d10500d11440b0f684400750034208901507400980900c0c0c480b40c00204140020806180b10b40f40c840300303050014200a100000070b44440c400d85209801000142c0c5c400301c071600d0a0603041c49841d0602c40080021410036521400141c8090190040c0c0a90b8648401d098010b10f6003847c0b07407603483e40301641d109644503c040403170001c0c820390f44829588689403000004c3c10b800e02d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 261328579 1250 261327329 261327331
    0x141e010b090a0b0901021204140a090510051210060b04090b0409050d030b0a090603060b100903021e01050c0609010e100603050a02150c070b090918060c0a050c010603060608070608 79
    0x70450385500f03040090002d0140c00200c00c0504520034042c600d4207807200900204058501040608174500e01c078400e02843c4a0306a0103140c1c2c25141500300032246202200340001c3c0e030340c2243d80d820b8041020a0181c038000c1100034038402e9510b0010005206a007103c0180100e560710030040c4001c0003003c040004695a080d4090655009600103c045034401c3e80208045070780207042c040e000ea210080c00c0101e42041d00704488403699050790203400c0c83c10300c040c01015041454628840c50035640461400740340c0340e80d00d004810002c0300a0842d0b070301820503143e41502a5084903054a02030322001e000e8900003000090358007661508864807400c0b03014400a99821400900141d0812360a0144200c0302c10040340907140103202c004511501841210000c0651080141e199050442005401c0c200a4010000c40444140e001d070b4134400420700590005408a24035200c841d42003068499201e000c40040095180c01004420084940d014005840c030f400c0c21611000d07100d907000d5540c404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 261329829 1250 261328579 261328597
    0x1404140604030f030e030d0e01060e1003050703020904020f1009050a0821090105040b030103061a09040210030903051306120507020f0a11030c060d02030a0e0304120b0a141e010b 78
    0x14090a2030116000b1780100740c06400c5002207a02c1c104921180c20104c0346034440859003651500010040070a4064215403c09880c0c2d0036803110300e2440d900c184d6103000d2403000902400750311001800351b40d40ca04407038401410240690801d04038a0f0b2001300139170468082c1c80d00c80e411501000c00e084e940015034601b08603601c02c028888550603410b804850308071a03a0a0b041040810011034049000c2d0702560086100e00404285101040c00007090040008851030055141c3c50030040940d41c5c03400d00c02800e0925040c0080c4012650a0449a074811100b080842e0841d0345000240c0c3c0d940010360b2000c1580c0c02200700956102d03280226100d4007526140021903100b00e001314003048961842a140500003000c41d68100280c101203030303282e04420081c401c0d0582c08000c02107081028040d4040a03200034014516103810300c407841c8110b24142e103010f005490380e503000074a00c0c3c5250340034042c00350803000741007528a8000780180e1804084903081c8941e1803180000200b03544c166056900100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 261330935 1106 261329829 261329837
    0x9010e031617070801150e060109080601060c1109040c1e180608010f0902131a0901080a030f0c030203161a10050a050303070c050d0302030d140414060403 68
    0x403c550f00100c11a4101030303404042000d5100b0a806075030410b2a8900030351640ca004071340281c017940104d0000d2090703800100303840b504400c088c3d9099104001c142d200e98080028408148800e8800030103030f0b140040c0610840c1c400207421003040107040107600c0042d0740c07040d007020f10080036000308051665601c0300780450345e020b002e0624400c3c4129810311040003180d000c00c01b40c0d03003100388210f10903650303c03ca50100d0a50341850010399800402c410441d503154908592180450342c01100418405a00c03250058066003031803140703a8240c0c001d941411031420052007175884120048841000d90030700c01510528082e042405105020030349440b150400c400d002c00c180d100d0304031038400d81c0306001e41000102003410340c0e402e1321016200041a42070304d1070180e14500508042603074450420305011520350700400c149204602540e046055180076180c0765450b1802501c0c041c00107 = true := by decide +kernel

theorem cover : BRFrame.Cov 261151079 261330935 := by
  have h0 := BRFrame.cov_init 261151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 261151079 ≤ n) (h2 : n < 261330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
