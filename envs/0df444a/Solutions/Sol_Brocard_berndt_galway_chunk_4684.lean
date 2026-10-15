-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4684
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:24:27.559156+00:00
-- url     : https://prove2.me/submissions/d98a9510-2f18-4b75-8b08-7da997a8b88d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 842266187 ≤ n < 842446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 842267437 1250 842266187 842266231
    0x150f1b02100e1503040506181501080703140a0510050c0706180b090d081609120302071e0f0302040b1c06090203060604050f0f19020d0b0406060207060504030b 70
    0x80d9a80707158040c0d0380d050300d0752424208022207500c22008841d40034100b841040300058002440c1c0d034209110b1078440c0c006100d010202413500d01440e210f8800401e1100c0005564080054072806582c401c1804080b91800400c20036500c912030b2002a1007a80140904146a0802c7d44400d07000903012000318540700d01ca8513041c0544031034140c84414500d4581960041c00741c0d0b4421250411008005000b0003961207500030100600502099403c0f0702d400e01d501c2c015030240c002140242041c412072040303c0d1850074042e440b0b0540b4421943c1e80203c1030310044148228103d420309550740410034052a80c115009d100003003c504400740c2d00022900025403182e030b02540302d0300010b8450320001c03440c00c0182c4181410310a014288601a038204000d103e40307040640c05503135020325a4918031596958000000b071852140c2342c0c0c9241410f2000032501e181c0002170300450300c0500107807001d0100680d20740089950391014884d80c40042c1041c001800003c0c03134845800d420140301c0182c0312078560581c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 842268687 1250 842267437 842267449
    0xe060a031a061b10020f03180127030e102115030c090c05130504051b0d060608010806011d040305090a09020403060b03070509060d06150e0709150f1b02 67
    0x54a1406544803000030030040a0f010041c41d030003070380ca00c80c06504200c0d034501a50036038080980b00141c0c404c400ca05800d1a2242540510030745c0750010440b002444010580d010400c4042405400290300264200e445040400c000320034690942d54002e0540e001880e4100524110051005115114014004c015039007548443c051800765026a000c2840c00148004882046c0c0052051140c14003011145da1030b604030030002c807001034501290310380d40c82c4201302092540400c040e980c540003089810f50000c1650140b000d541c0c40f80c8554180d40d880b001a1581c03408244074444920302003440c450350540c20342151641152084c141181840c0c075a000080c00d103462608075001c0c6560111b01002800018000d8010944065028144040c03c00b000b10b110a04c00400407400340e00600082400c01c08030780e00141030340303034074a06441c0c0305a21030300d608034007a00c20394032640010800381c40070440c4a00c0600e068110300994841d26108001c20b1015140344140d06501550030215522031400341e1500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 842269937 1250 842268687 842268697
    0xa121b0504080601140303180d140d090501031104140d080d0203160c020a151701141008150f010c0b0f07260114040219050a0e010e060a031a06 63
    0x9500c900da20746007020055032070100141d004104801002da042542902d0201c00c451600c410b245940c2146c40460300801d00403101144010071031a08852134020341c2c6e50114802c1e440072202d56031803030744554410044040d00c01011454121800411040200300d80c0100c66160058014090f21011304140d145e10700160400b00800b03814640000030407080104460200c03802e09102d0030b040340d9008643c1c000c00d0400034940500b0540174441040d13885014003454075050303691100d403483e1800d0340c0c440b0000407240c02d80c100041d00400c180c4603a6044140141ca000781719908640300d10301c1d18401541080140450105a141032220520603200840c280c1000d50348100b58251240e01641492003006140307540312028a2450142907a0784c0c403014451000d0903044800602601c040c860106000034000d1190400c0707100c1c94441d112009840c01c2c2c102c8094100c0c54066251902c03c140400c0054a4044610290a078450810000300050b00d000e036100c1e69084008003000300b1941c0300d10022a0140e030103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 842271187 1250 842269937 842269991
    0x803040501060f050a030b1501021606050702030c0a0e04080f0d05090d020c04020a090e040203010b040c020706030f090f0308190e1501080f0606060a020f0703080405240a12 76
    0x15480b06202000340400c07142c005100688940d016503203181c881c410503d1010b840380d00c007089034a40021940c0e100b04114610000c101480b048925076400700501141d100c1d4100324000d0080c5003e40103e45003201452003202c000d02054015655603584118103070b402409010b80441c4240b00200a00d80640f003140d1140d00620014508a695041c0181c030740f441c0307084030510039401000031106165203d023642044070540d040c0c0029507155440081e01400e41c1d0311955400625140e120180c0d550300092560880c0d00c584c804200078410f42842100f83e0b0381c41c82c0094000701c002030314079000a100d41c5a13940c0c807100b90380c005860b4404000c200c80a031026800230345802d6100c1c3d40500007109000d08050b00422280006080a8500b800c3c4d4944402004045030300c148404200031000c54024403002d00b900d03520310140c440f4a074581ca841b007042e0300302d4003889001c3d103000c80d5903111803100c08070300c0c040c0c444508900c182030900d240c000300c03034525034071010700d00c401d888412020901e0071203103070043e06080e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 842272437 1250 842271187 842271191
    0x110301081507021b0d05010c081807080a021c300e0312030705070c0602010914010b09010b0d0f0204170d020d0e040527150108280f0803040501 63
    0x100d48814549030207444003000456462030300500038100c0d00001c410300e1080105107001e000d10650000100c08480d00800503029500b0301c0e040c1000d00d070b803008645100f48519422040032507440380016688000078040c1080c151700c0140b41001501d0700043c070000070140d007003484803201141d6444220800c3e0b160542e2580c81e0b0300c0c0c00b1404440510544500e10420b00380303800241c040070640043d981e24015075034803074000000004912107602c510120b50720260800d042a80c5203503107980c024002c02d080d50f02902d13045514032055190300c1040c010758501c3d28000700754003060303400d1504185d4954090015041e0300c60340d8030080c044201190024000910454208055200305206954200156081054119000b16010480e2140c02c00c0e5440c0c10101d0990300025250b0300c0d180d8158444080400e9240c2507190110800107150000645014803428a4114601c60f42c1e6201200d9890000424036001784024007802c0c100d4849400c0c00400c0c0da03003e8071042503000030f25211038045a0041c0c0d0160380700e0f5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 842273687 1250 842272437 842272439
    0xc0506190914010f0b15071101140a080603060c0c0c10093c0f09051906030f1b05030c150d0507050c01060509061302030a06170307030909020301061b0c0306110301 72
    0x2100fa8451906644010388030204216441c80141ca103c1c807c4520061010284035000e03c06a485095a0460441000300b4903544441024000d0401502204d51510030300c501d500154034050f101f415101c80589a03001068200c6004081000c00012014600c01b04510f0480c0020070b0411441030000c001143c0b040c000d440c807118181d080314244140801020300c503403d00104880c4000000349070440b850a4400035642d200c0840700009024903403144090141003400c080140a00c00300c81803c21442008042c240e155000400152440107100f03440c0e03d80c01074403002c12a4105003c422500c40012040d0b64580140c2403551801c0b50802d54425001500111302e80944410900c2080041d0104076a86841c41c504140011228000c5889040c555900400840d0b00d040854000c200905400c080115420080f503500300d81c1c0c0d4018480550005441c5400058815454401c9a0603580150340310400c0054000342c00803004103902d030484201a035440000041001071140d200001c401e200f010380c0d25 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 842274937 1250 842273687 842273711
    0xc090509100c0f033c1e230402090613020421050721030309020316080102030601030f0516050f13030501020a0f0e130c09180207030f0c050619091401 66
    0x1507105c1000c1c100200c016107543d101c0c5444018006940c81000e040d200c41c018400406900501840c118611010111100c800015280c80d00b02c428050a0340301c40742407068a8900c18801e0170410380e070103500b1008030700128202d420000c0d04040081510034001d803815690b4190302e4064120314004144c0700203000450010030001348040070082c206407182411b03404206603205541042924018140740d82ca0300302d0300440d102444940b0004a200404008090b550066117010350310480304180064504055806d440300036101d0a07000f10b0081e6070303007445e40e0303104070081d00c031644000c0e6204449441800603808440c82c08010320b000c1c501c604005a02c035084a4005001a01d94960380700500c0000800942151503840881c01f5115400e9000300c0c01c01411881030703e40443c41d4204a819050f0b008402c1c20029494000f010882c0c466641c0c046140c3d02c1100c22100c4403013101004100d504a000410740d03400d002010880f1840000c0c100140b10401640c810104185c0c10704e80d142c0a9464000318000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 842276187 1250 842274937 842274941
    0x2104230f0906190e0f240f0a0b030a1401080d020312072021180118080a06091703090a0f020a0e0118060e070f0c05070b04120606120c090509100c0f03 66
    0x7100c4907016889280020641d040690484142070a000c0ca21809034007005684088c5c08000510141d42e0f4180c3e01e0400c1118031020302101540c110070403c540000203000b1500041c00021014190301440c1440042e95254201e0f01000d00040d040041903480901410580a40c08401103000b400901104000e010142d035a000e8401e50010841030038031000f0303000f040340c5a140ea0101403d1912091000c05851116a0309010790003802131340c840d4440c21020010340d60710101d80940102c0700060000c808003821a0300344021100816550001c0741200d0014150f00da124034541d01c0141560051a200e100072021440260b00c51512020809080c86280c030f840c0c030603400540045c98980301c0902c0c00030009858406246601001c03c400c000c490f505020043c003200e805800e00000b890703640c56a9000e48165400083e909032005460880700081c9032300000c403882c011039030080b00c8200040c0b4007443e40d03005000080c0006102c0c015401403c107030103d1031142001c115590384584140140c01c110083c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 842277437 1250 842276187 842276191
    0x120703114c0e1e07030f030509040905070f030215040506040302060c150a0221010803191202030c091503130605040614070f0e09010b040b0c2104230f0906190e0f 71
    0x303d9400c03c480c280081488040b01eaa030068041c1030150f234502d00f0300041801080d0f40c90001c0c06d03501038000003041d41c8503002c0c4581c00b1607000701c2c3e130b02141c80b00807056440244541d20070558404400c10040005050110203002c0700e880001c181d8410150141c487e48005d80b084404140c1203500154006000e40951074502046121a03851101581002c648a51300d2051a02180c00c000d02070010140140c0300d0f030a43c4c8045054020155101d04040c5400792040d044903a00c14032546081190f1256620b000c1c0c140c920a90040c3c058611521194a85000901014109a8001d40c07150900300312800740c50304080c01040c240d030701e111400d11090002070440c03058804d0f5a104a4850004000c1e5003003640c151810f8a8058845030750303800500b00c0030b0346050240100c050301c800600554143d0311503418054001c40700c80e8196460390003501a1403c2c0000202c4421950003006c005142c800340c100500c3ea103601030400360402c3c2a0071140c0140e02c10002160744031104c60608542001120814035030410307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 842278687 1250 842277437 842277493
    0xc03040b040501120219051b0a080d1125060b0d0c03170a0503040b0a1b021501050a03210e220e06060607060905120703114c0e 56
    0x1400c24001c0c030192086202c0c0b5001d020f0400c50003150680305c00b0000d0356460b45002040c8201c3e11162094030740412190402c124bc20307035082c5020208941c80d495a011241c80004980c1d0b14140d550850108025401403200280c9115a0b07030341a080080c0c4035050703031400c071a0058240c2d00c0607071b20f940703070814945414010012680c5003d0001c944031941050590f030700103510030b46022483e80c3d0001c1c0f50004200d441c0d0041c01e402035144100e42c4540e00071a10b003101c081b142d516030380141e8840c004d101d44401644002040c0c1490345400300040400048090000c0c541442e0260110121300006441540c120f80740305a2055100480c91f00c2c2d1040b84a04002c0d1604800a001c180c03403c900020060f00a0001c0501740a44034440801080800e2100c0003120215000c40c0380c6445a50400600061141061100c0d85c42030003440700e00700b160414608502c0001444484200000640038400c000039601e205800c000b40c13890242101d145801075001c03002c4c600d4020f210f07046803909500c0042811140f20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 842279937 1250 842278687 842278691
    0x30c0102120a0c050c04050112060506150d021e03010603020c010f14060d0305090402030a060e180601140103110d09030206070e06030c0a020f0607110706031a090c0c03040b04050112 80
    0x80107000c04030740306841c030310111403c0c045403225590910604009001c50704070361192400300086801101540d20807000c500407070f0100082d0b5600028403402e0404034040525900313091041c10060802c640050804029000104241d1810828000d601d0340003a04400d000c00e030045001d5141c00804d12550803014100f4600348805140401405003986000d0700c4c05020300003281c100300074140160100ca003174030000342c011552480c11880c020028045400b981048001c6100840c1c4445102800000c000d0422401381c4240c0c2d207800481404c0060603100e15041c107884800000364a00c43c03401510000b6040c81c000f04980c0340d245802824008024462018005000845c2d603503600c8100c180c03540040c03034007055507640c0202c1e00180e15180505031910171511821080080d071650100c00d1090304c42400088540d140d444100035400d4034201d6a8070108803245100c074020516140c02043e8000074800540fa00e0010307180f40c1c00c0d0540c0d2180e001460000400101002556804418003404180782801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 842281187 1250 842279937 842279953
    0x120f0f1204060f020f03070c0f360603080c0303161b0b070c0b1f0b09010507020d021206040503090109150806040f06090c0306081005091c02011b050702030c0102 71
    0xca8482800359000300c82c1049000711560710b40318000c00c205c0c20001400740c2201e444510500c4e02000c0002603028042e01e05400b0070000030715090144a184182e000c007410580007900ba510303002c090801e14160152007644131a4004042034070340c1c00403c8000709510140d5500e00d801006407880c240f0900c0503c0400000c0c001c0702200d45105407142d980203500200c210129201c42000f240d80c0d00e12001c000c1d014440910074000414298045003825140c00076040c20714544e03c0d92614228011140050701050080003a4801403600e91203184c3d8403803008110a1f03510220078862803a041049504842d2070b41700056040351981c0080c0c01c1c038020411910110308100406000400045c800b6107801c0c0902d40f60b48084c80e03010000c0c1c01c148064054a4020450764201040040103401036200312180390040c644080550610350048610804a0100601100c221f4050809400c040484590110b55803903d2140d0382080c1c1c81040c00401540c0d03502d071a110445401054284a110294141075504c80c081c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 842282437 1250 842281187 842281213
    0x306041203052809020906010201051302062a03040306050f041a06013609052203031b030603050c030f190807060c090e0c0703020309120c120f0f 64
    0x560150881000e18000c101515003c202c20020820100d0060803203e00b40c2d00c1c0c0400351401d901802c4268021a46810181c54031401a03080390001c0d14603031681d480c40d00c2d004000d8207201c1d0007040c0f0000e1600e0000f01400200d101d200c841e009140a132034440e00009001c2060250310300890742c00425194040c031807814641d0b54440c0902604010f07440c00048140040c0185e800f52400401801e00d02142d003182038605500f40301c0c4c65400c0c0020310041c0700c4110b0081100c50b0b00d032007164800c7c1c55003a42c104889460903400d200311804000d08604254465407041c04502e00c00103107610100c4561408501182103290003810603284105590003035000b01c0c008501c0e5840000c08032400120b6101c005803580e01410030b85818072840c000a018a810501c50b00403c9600c1080d250803140019030352045615141141111b52248150160041c2d04c18481c04499240c1860b0040510202c2011104d003240d107940411880c5c403c0b4100c100158100b0710780080c4800003440003a001c0030069024104444080d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 842283687 1250 842282437 842282453
    0x4020a0804051c0509100201180b09010e01020c190f060204080a0c06030209030a1103070308042d0617060d060905011a0303130b030709083901050a03050c041203120b030604 76
    0x10944031700c030709075401c000001a8002c0d40000041c2708074000540145016080c0000025010f880c004402e41c82c0000e4551135030018400d0700c0c060003035039010f0300061640c40512040e190a05009548201480c0402c200003240c07840100300a04221000c0d24250400e400c20a521481c81d5000c1018940100200c01f03ea0b070740801d5000e00b5035400109044500300900c08613280550a4000500b042800180440c503003245095905080b00c48000c00030f036042001c4c0b00c03000f041c4114807650010406505400d111941c0300030281d0b5019102819080d80310007613845801c161000241c2c03d0320300b03965034080f0044400d040003007000740002c01e4004603e050341618030783e050400c551069458408002c0b010440c000e11900a40c401001d006003103030100c0c5243c0c40c015006941e5201c0a2403800352002c040c0708500442440c400701440705071030b0982414104c034001e0f00a4140148484900d080800021452800c1c0e0070359400914080c1e6100f0095500f00401081198242903030706105c0e60201d4100400075441d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 842284937 1250 842283687 842283697
    0x60c0509090420060c010603020a05030706090b0d0f1a0f09281d06011401080403050f07050a06020a030606180806040f06200a080f0c030a1a04020a0804051c05 70
    0xd0740c801d8416004011a00359034008840f95440500021240c201c0103054004170196030003160040030075079460341055541e200301e00c1172801103907816038100001d0714190058588a4210000400c289040b02011030031112240c0d00e10a118194480500711814048509108001c0649014a80f0b01340f800e00c04071059032250003041d03159940054140314a00740d42050a010f41c081d095240103ca0017007141d1344855090041c0c0780517a44180da2080f06620600115001c2c0c0d0700354031000c0c40e00360000c0d10b0381c2d02d99003c80c200742c4491103085141000900148002c2511115683e000607100d0304100004000c07a040c401e04104807402d120051190324008100141c1040d440701042c0200038007032a028020b4400c0c0c0241a0300e03428101c115841d42407048000300407090325030b510240141d03107141070100c028034103407010a0300a10030300000d030518205a104980881d051070201018048090008043c0c1e0301540b400b50020700c3d80300a000421108210b12000b418011b100b03030502e80c42d01d441c014404c0c028 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 842286187 1250 842284937 842284943
    0x2010e071e03020607050d080a1a040b030f0d080106030e0c1503100b0d0506100203070b180a05030d15150c23030a0c03021006061e050c100603060c05090904 69
    0x6400c05450307144155001c2004542c00361240342c0b00c80c810300b8429120300340d90b003040f0081a600300004542094500c41ea503d805401c5c2500e11580e9005414080240100c0342d80d40e8151060488046c0c0c075104c04c0181070043c0c0001d61f20034107558180000241515007140105030320707500c4010703100d4040d42e5040002c0000c40c008071003d1344954666140003030078031160b03010350004a00010410607440391a0840b611415044e01c0f11048484400d038101c4c2c2e00e10034241d020303080e0501034000c1520341150300c110011003060b110031611840340644801d821540001102d0190f1030780e4003080300d00c50120704840d01c01005104038401a00804074000b4014000000009002e24459040c408880d445202816400406202100e454040d04040a028550b01200507005485010340da156210514003442c0240d4401d036a507031000ca0040c030407200301c05000c22885010b1107420f11840300b80c2d0f0000c1028410460f00c200b00483c1c41490342c1000c0046920b10a061703c10014208007404a0351648100c0a0300b140d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 842287437 1250 842286187 842286209
    0xb04290115031806020703021212063f06010f030b0a050705040f0801090c0816140a050907050a08070207230a08241005030c130b03060c12060102010e07 67
    0x4601c504400a0912802d180341c010b4440407440e040c0000c5901400c1d8140c40781c4c08841310080f122007400c01a000b151000d003403540000d4000381c80ea00b080c03580002c0b80140d04003040d50100145111000042241034070382c2c50400d00d1035421030424410010540109011004001400c0c115196800d80200040102c40140d840c4c1000c6448184200304540043c0b0701030102001e101d4440003024082c154003e000d80701280b607114049888940031501c1a0310006880104000c2854109002c100c554000651540401d04010016464039203a1007544217010783da0300c0b01c1da185131010001d4000c1c4406044a0110f503c0b411007400758240c814441c00071109c501224100c070100c12000a0b085c1c500c19000003002c2e0240381851801c181340541400f071700c5114180711035240d5951041c0a0160083d034403c0c254076034007805c0d40d03100078200003a0000c04052507200109a452011000c2450000180c66442d00d00d48005420350440d00810100c0707400a50074402406070000440f01d603603552455008404441c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 842288687 1250 842287437 842287469
    0x1213051c0209040308090d170105040b151204120302070f02060309011506020c0f01030506031902030708071d1501080103060c050d050a0f0629071a040b042901 70
    0x45511003910022a8024580841c1e403610303160050240c40d007174404016500c10f20319002001c82c020039003405840203428400302180c0c47c220402014241840543c1d800072004958202886140f0000f03001100b85142508041d00305072401080c600e42182600040610502418002820803807e15100b903030100c9030391b130300c988416900c107004044490070031000c04281b1a0000d40c42c1d801103001c00702000c089030b520121540110044d42501e000b120312541c542c000403522200300c1c29408130100c40c14000382c00c6501d819210003141c0d1504402c0e070824085232010090480b12031800d601081d030300459400b441d41402200c0000030708030040c1808000c1c107864031038030f40852640c0708000341d0306a0920701e1014080c0b400c00c0b4612200400801000404045c280003000c00e42014494000000741155008560110000f40843d4810f4000003c200c87c80140f140d0901c0d5019840300c2c42c1801307140a800c1221560606c0e10b4160100180c5404018645d040201d414900191008406044900200d40541c01d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 842289937 1250 842288687 842288719
    0xe06120a020a0e0402030709060915140309011b030b0f040c020d2d08010305071e06051e03012d060210090f0803100f1e0302040209040b041a0102121305 67
    0x54100f140710760080e10100030080d01c0c40d440446002291810380741c0c190b21a45807203800e0144220790f184207004c500180d418081019400c001960700548100c00041c1c0118401c0c0b04041a040103026040000c0d166860341f486c3d45032400c45180c404008039000c00c80b02941403006908d800e4020703004820322607490080500a03015140c290007410040d131000d10364418020000d00221420302080e1098480c2e80e0f4003044108411030f0072094040000110034070030b031074008115940e6000465080400c9541501441d00c4940d880140d40a80040d4803580b900c404c2c05040491605100d900e001c291011403042048a2a00810302010300310b0f2044000ca83c1d0310b001c2c1008040310000c00002040e0f0303070000080001c08500c5500b180141c4070b845801e002c10b1071b43c4139403041c00c1d8104400312840c00041d504042005280c15401003031000d10141000c60f0000201002a0417200610450394141c6621520400d644da03041c0304100804620010890070041481c02e44d0910001902600340118801e200c0d40c200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 842291187 1250 842289937 842289947
    0x101202060d1e0e060a020702090c03070c060f0c0e040603122006041101020f0a08030c210907090f02030c2505010f090b0105010f020a1b0512030a0e06120a020a 70
    0x4100c6102060031440b071080c03803100208042c080500c0a8015000440c002061600803900c03145d800920b40b0220f9106c10030a0040c5a102411000a001e0b400580b000000c2c214001c0030310902051070b0008280004601c00f43c40140b00a41c8903205a2510b0740034000541e41d80c0c0341c1501016245032085024803e450549022011060125200c4c0f01d03030390030801000441e500d41c201c10317a000c2e400d0b00d00304a161074100da40c83c1f2a1a0006111190500010740b40c1420b41000d010020441138807100c03907106041c8079020100040e1a03550413904100818400742c00382e80610030081c0d450302000c41c070710700e0501c1c0c0c4c0750441d0240074082c1c0d05036200b00c8030040903038050521040710304c2d40060080040d0b0b02e200c981000101840841100c0d0300c01c214000041540c040d0020001c501500e0b000703408550b01c0d5070381d084500741c08408042c034013002461000c2900c1d00e031403001200d0412130400a560b030744427540011b40700050108400b40701d040d04000c0b51040080c8a105150000f00c100c001684030a1000d5090322 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 842292437 1250 842291187 842291201
    0xa02010608010237081303091d090d0e01080112020f0915101403180f030a110f01050103050d030b01022a0901050f0604031707050a1505101202060d 65
    0x590700114080705440307540c9103c43c116601078106034031264070320300320040d010a0720004c0350b020030038100001d80b69060008060007803605c40d24107204407541368000869050786121150100303003011010000c0700c400422500d0fa4480c26410100542103484000a24040c414007424040e030f07528452840854803005115010b45100800b445140e14240380e180c07c0442d144040c0381d2140070030401c00021107005003d201d0044251140302403542d5074100750071048110060070012107124840b01e101a0440c140040e002007402a56070b042001101d4482d02c0c81c0c030661000c00b5280341d2514004000180000620607486107075810040740306166000140d046c00111124405807826084c0a4012003240b00030144c2424030484880820340d8030f8005020703008804824084e00f02c8804c000510105008810013300007e03018242841d214445e0748060030a01c2003c0e044800d11541104259003040c103004499110708090a1002003510b02040f120101c0d22481c0064041d280001e01c8156042c4a900300304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 842293687 1250 842292437 842292449
    0x6150c0f06050f0a0b19062706020307050105180312090102041e0918080313080d0c0f08010b0304050a03140c0f06090c0f131806091b0b03040b010b0a020106 69
    0x300e00d0f02c3d01240000d48001c88140c0f000038030740b041c10015454150502c0b40c00001030041c800c103503800d00c982514500c132042c3c681c0a01c44180d000e080c0304054810366100c042c11040c1d000c0c60b00c82d66249000741c250795014150705850625092400d115400020a0302c10050700710f050614991110048240240f00e00e40040c214100081e0810603d10110038000d1f0498100c140100203901e0825154482203140f80d8000744540700404c00704080b0f000e0566000c05881c01004598039058031140384078100e4414000560215801c00340b544c100f190480c841c14010042004650328500d1700e81d43e8191540c00110006042c408622100c92180a01d02c007910549109007080f5402c0c0c801e00b000040c0e483c50b04075480142482414100c110506018408550010000e4842e8400805188040700501050700703101c9441245c50034400049101400b07101036543c002c1020a4015401b256048007d0100d500500540c0b0010000d10002420703801d506811a507038680031507102e54181c1030403809840d03194455 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 842294937 1250 842293687 842293691
    0x609180d020d0f02061005010f1209060506180c0d0923010f0f0b0f1c0b040b0f0606071e05030f0d1b020c091f03170d0f06150c0f06 58
    0x10100e030540025a11800c03071a15200c0b40280203030305004070b9079050100c800c50200c0a001070100310070350007101c0c03107180c050b5a401e20002e5410700c44595421100d440b042601c109880d50213101d424100400210440400c81080071020300c0e042400c0c0c09180b28641c0d44a50750750340e07000301200740400f201a1540b5131142e12010750825408480c440c0c060500e01101512a6142498041d940d042911540855a00190031801100783c5101000030040100c041c80c0c1d40b101c2d2101c0f020300060116000c2e903208a2145085580500700403e0312422494001d16080c05a0010403180010a0002413135481da1031101d42c20b4511039405190113411405004410014504007089800030000b05800083c410041c0c40444001034a140c0e0b000c0f680d903005542c0041d040002000407480d0f84500d81c4a031810050420403c201442d62641c4144440c42c072103540e0108004041a00c0310b10606074015011210b0a01c1c4003841410f0078400d1245204103502114030500c00e4445a090400121601024002da044682 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 842296187 1250 842294937 842294953
    0x9140f1003020309011401050a050118081204080105010b0703080a02090f09090a063b0c06040e01051c02060a05090d0f0f0506010801051b0a020313031b090212060918 73
    0x1001d0040d410546800e5072a5084c02e041100d40660949164100c40c001003c407805907107080015100c414143d20b009000c10b01e61130010991107010005a903aa04003103400554407480c00c0f084508450041c1c0012100c4001000a080440e90040065030442402903005a666104000050b01648160f141503002a0301070200a02d002c80800c038020711602609061140c46208004420007425070a08501c02019013101c2e170300204232030929020340203002c1c0104d8001540c0280040d010350410b034049074007200643c0040c0043c1c2040c07ca810203200049410704400c0b4070560015450303005442e01c174000c01c003000c81d0010003540c030000b07084040c3c0d4001c040c0361071103401070410410000e0842130a0358140702e00e00001540800c14803c16108001801c10006032102c505000d00c10750740074205c5c5108605c01446482141c0741c0c152003400080d403040c20201541105001807101031070441e4400e81d2001c0c1f046c0107041c0c2e110b50789480c0c2c650000f403c880d01c2c41d0030b9551224050b0012000703a81c4000c41e22400306 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 842297437 1250 842296187 842296219
    0x2030f0415240815190b010908060f19020c0706050a0e0409060204031a070912081b010e010c050a0503011418040b1b04060f080711010218040b090709140f 68
    0x4126410f940700c810581c2c3c003182240d40c8007001e04400351a2000c040c2ca0600640041c00819807020b00d40a10500d4000e008a85c3c4084017440c0090a513140c076265040341d018402011846888842001d1200c8010f504098902c1c01c11078035090700380f0071070b814041c1c0045c1100055219a041e07014521000704104550342150414000a4003e0f010440e1220104003240307107520032400ca81d074407030b0110b6561006903e0412002c840c0d0b0320207901c0704441d105d10a00c1004210603030710300202d44080c0d00000001e890001c0400c540e003903411707810340d03102409003c0202c01c2100d5403180441c0e055501460440608074050400715000139007250101440c40c2c1c00307406000801440580301d0303010300b90b0200f4200c5550080030350601644102d101e4003020642030301144050078043c0d400a50301c0324141c10075081540c20b800c4240d003607074001034030b1842103c04000c0d600d044e840c080c440c010340326000743c030503000e0fa28280c1c00181c4001594041d0741c0000e17a42c0380ea082c0040d600c0d80000b5442000c007501c207040f034001c001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 842298687 1250 842297437 842297501
    0x1204030606030b070509280b28261306022b0515090a09050d09052404170a02030706090306140f060d02031510030b0a02030f0415 57
    0x2c0022507a00f071030f200100d071486200b0b40030748100c10f600410110002d40903a01454210543e00c1900c0c0c0100c144a2000407404040340142030124008059544c5e8404131903c00b00d0b0602080c51a0828000d60101740c41c9801440c0480b07450441c2c00b0381c8440c80c0e1b9258101086428089980d00030a898000034401c078a404910030006041000030b0000010351110001e440d00b59401210040180b06800700c040050b07203860100030ba007040c50040c0c0000c0724240340c0c0b601400c000030002240c0c081081400c041040d414010340500440b004950364501030b20340b07506244c120740b2452007160303540000449118000e200a02c2640031045d401030454514a981c3c14005e0034400c9144000c2c4c0e0214604903900b43d0141c42e00c09280d1151901001c2e440c0d19545600030020010303480301044c0e070103105d0201c401c29003c01c0e000d0400d0049a85072500703482d007840c52404180c51040184190203480c01802440000002c44a0040c0c016505c581110312101e10601c0c1d05000b02000d024808040c011701c00c4400350400f02c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 842299937 1250 842298687 842298689
    0x90703060f0e040510020f070b0c0c1506060d24180b1008241905031608060f0406020f1204060c11060f1806010b0307080f01030305070b091204030606 66
    0x1805440c100725580c20440c80580c038216000340190b000348520040b400550760041c401004205115070400e1181d880340036822204031001807102c0b4000038140e1940307004003c1020111352066110303a00b4900344010408078000d0038440c1ca65691503c296000861040d07011202e01d401c0c9030f2001008540e03c10801841030380c01200d074081145802c040c0c0c6003500707102d00900f100c03d4094552050580b50f0400b0300f071030340c060b10002014158906503100701e2540d40809011007604605501d0005c1400c000425043c998842804a41c100070060204a00748000c9015640850010900d0415aa1300d0410501a20402d500b18215450004402030114407a1800a020740d00030b00003084211903101041d0b03003040c104940207001e85d22080002e0940725000002c00e0348000c04441c514503100351103a2051400d6000c0e0010f400d02d01c0302104000788d140d480100658007214901c070007106d0794510707240608039115072074020b00703468032110000781024410007043d01d1012403044410380c0e85a903401c04034010591 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 842301187 1250 842299937 842299949
    0x60415050a0207200307122111030304170f0408060109150f0e0a0b04020a11071e05120a02030f03120c0307080c070606030c060c03080a020903070b0c0c10110d1d061809070306 77
    0x23a000b0041d500d80718500385010100c3e480c000b545113488070707100c6c0030640301040382c0d01c0e101ea182000b1907940d070318000e40544002c000c01030080100b541400041d4055a2102841d0b81009202ca10304022081c941c9142c0c8048400316a005145515035000201c0a41544440d072a002400081c0702c4400c0b070380c4030b030100320074070b100000351640140c880f015410000380060715441d881340000000e004502c2c3c003900241c0707452036a8044451486903503020a09001840070000066000800c9606202c0c106054003a4401440600c1c00d18610b015040501000000307844411000408100d1404000c2c5580c00fa5010f1a004803041590325968100103010310322a05086001501da0008103065107401d000341c2e00e00f13031b0000b000b5000041c141030f4040b170b00c1d800c140301c482c8541c400c42c05030704819112048048800700240d03403244039010034001c500c2e1404030a80702c45420014003050b00d1083c00285407040c01c0000080301d0031a40d40301c4501c1515410f8440486159200010300140602c80e50154008021215 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 842302437 1250 842301187 842301233
    0x12031e01170c030604080307270308090a090207120c030509090108010e010f0b0d020609031f0504020406060c03021b0d0c120614010b1e0c060415050a020720030712 72
    0x2940c0c0d803d2503101d130000c1c2c0300188546003e0005c104540d002c1c078841d0b4001856010601030030000c640c08070004c0545507205482c3c2690009116246003014500e0a000d420f030403005503e014030950b6484486030fa0b0408120070001954540c0d41010b220714115000340400410741c4540356116001c480c020700d5050a0f9175003961070011401e03084e070708600902c02944002485601c0d0f03174406409012460b80041103559042c00388441c6072901010030358954900351403806000480b80790520600003102c0c016040701d000e2144001104001950000c0e144c4060b00515107d024910300c9540425920245881d00a083d802c1c0300300c000c0741403565000801c61b810300480051281080820f00c000d41c4040a0140d01d00225080000445409200c003504041508010000b803501c030f1425042420084250740445030720031500c2c0100a0726030180619600620a00f408528122459541040c0a90001b21300d0980e05d01103144c8071107d80e02030180200a00982440780054a034524001c0e100c5840003540b421811 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 842303687 1250 842302437 842302453
    0x910020a052206121a0f18040f0c0e0412140903010c0e09250509060d090f03030f291c1a09030f07080304060603080a030204060e030f12031e0117 64
    0x150050252400d0f140c0c41e0f200044504d4180c5e814070150941001d5002d0300701204986c200006003070b02043e544154002c0c40d51030795100740d600d40703da4a02410341c00f0342c02c1c070300c060420300001c685c402024021640541c01e2030900460f4000011075503010b1070a449903d546400038500e081134002c0640d880b507071402c0381c0c55840c90740c41650f040303031002e240c010401000c8108034001d8051070003030000b42004039000f0f100d5801c11b16980e8804068812515040f5203601c0740c0d801c401c0801d42c150148034110780b0f081c601031107040c00300c600340c510f01205500c01c5004000409806859901c4000fa589102d50039002d00b822810060f051150504032450b000c1004695058000748420a001c015035030068081000070b4a4144030344c450450a40001d807040da00076580354400400981410014203007440551000750b01c9901c0c206000d002550400080e034001d40015214466040300802e00e000d094024048107512a1181d180390281c0041c00108451a2445d020003c5001d1001c1662100005126400c070f511003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 842304937 1250 842303687 842303717
    0x1104092a181508040b10051c150e0606191e030c14060313141506040605030705090a021c09260a17090a02060d06030203060c030910020a052206 63
    0x202c90b2154080000702108041000a45049039180c4c0081c3c0c005801c101594403680041c80710314107030050a6034038040100f9070040043c0b141c1071107c8521603060420014608105064030b0b120f0003490a846010014444840c50043ca0000b1000c0c0c62003040e40b140e82c00e20720910b500d88035007600040d81c244400002c0080c20030050700301c034403c14101a00050442d250b2081c500340655010301c040342c50117610088610b8101e42081000c0f0f200c002e050741b11905061150600c8115006070700114080d420a0a06001310345034043e40541100c2041c60050366000303207003000303180c0882540c4180c0307985042003485d03024401144c1c0782e060741e07850007803406203941d140900ca0111031080c807101a02045400c8859602035490a08095220340064140c074204041c1c0c2e0300140c0583d21a01c1004100c5030380f2a000d00643c00c04000b6554040c8044a071076280d8200307000c0d06a600c480314071211121680010302614024428000d6034021810124250440428103120340c2c0c1c41585401101700080d4011180314407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 842306187 1250 842304937 842304959
    0x1112180a08091c0812061e0a030b0603160b0c0d031419060b2814030f0601021e0a0506070807050708030618090a0302101104092a18 58
    0x145501a415520b03102c00d4509210b0441e0044000c0c09542c1540c03104803000c6548100101000701031034450501d10f2810500b0482c0514083d000540010076518030403c40e40c841e020f04000f41c0c0d80010407101c00f42c0d00e110000b451b04160b00309400410388003a0001882485a0015141c17007014441528040c000b4040200d08071250354114002d0310b4140300218281c20031a28112046582c3c0080100d1519150059104c3c0c1e948031004030a542d484210322000b180742c0c80c40e41d0021220703c504e00000441a80c40301ea034018003000c0c1c5082400000440450701d11f80c000c2068440303006803034080f007181168240400d510760502c44001d664600a180008583c1071003003d03071a214008540302d081c113001c8591030301101034000a2085e0340144000c200d003441030b182520382a2041c17140100074031a0f52420702d002410211131401036611f05080c9103403413400c00079400179901074580341170000400600821a05c0003040e506031303070302c41010000c40e45041c81e254007407108004145286100c6506503510040381107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 842307437 1250 842306187 842306203
    0x105090108060609040609060f0f0902090a050112060503071212091a0a022a130507090314030915031b0712050f0c1c170412080901111218 61
    0x40000d0758180024034510300b400180c14044000340000442c1916120302c4000c0382c410390080320410000300e60402c42c0d138100344598409001c0441c02035060100000224182e007142e4051541400200c2c0c0d600311000c565680110000e11009049403c507541e92416603042d00305011069410101901400f55201c0c0107000c84d00c11911241140d03496401580e00144280d000001154110700070700e800810411600340b0664210308d41d281806450742f1500041017040e2001c03c00300e000c00c45c201010080c0030380e04400c841007125001002c4201d8040020201400c0d0301c03500020541c070209400e29007a9009480c00034502c0750040303200040c1c244030903041d0071000340100c2c0d50080c01d151601c6109102144560041c107041290700130040e0415207400302042c01c1c40c0e19050400b0704840402060942c59a1040d0507120711802641d1001c2542070940b1507800c00c00c4072a4241040c000e0074008296034003001d520036501192a0140c86071209140d00c22198108029140000d89160400b000c045100c40400c0ca84 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 842308687 1250 842307437 842307439
    0x127090b0609130f090b2509080a2d200301060305030304140705100f17010810050714180907030b060304030c11040207030e01090902193c030b010509 66
    0x44400e40d8030764401c0050036400700c1c440c4da01c0e5107500001e400162041d480c0350003400340d294030b500b180c94070100c0c1220728065659103100308800306504111031180803031054a05500616081004880086640c55a02103859841d40b0095503c070b00105004d9044240340503207580310140700c4000b01c1e5004050a1354032a00014016810800c08034000504803094003100c517190b442510342003991500024510f0071010030000218107440280340002d41d00081030301800d1100381e000f10f1203504081c0966501c42148031941c43c3c0036a20000714082c1c42c0500c40900901c418540708607540c0828210110007568004889805000c050000c43d4800d802400350b0b41125101800803821950769440403141001200c03c10b4600e41c1c0c518150410700c0d22180000d201c4c00d4081d845010668024070001004c0c0c10456104450f03940c0305101c0030041052007003c0c0e5003a951140340800d85101055540415035280c082c9100060304114881498010066440040300010b901c04200e19800c41c0300540d01449105021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 842309937 1250 842308687 842308699
    0x1603060b0a0c0f14030a08060a15120f05010602010603110d03050313080405040510030218090715271805010e01030312140a0e0c06040e0a09020127090b0609 69
    0x1074900d200ea031079000494010780ba0100548081c1c1c6607040400004070b02c034481608002180e10119400c48220380d00304005881c000011450815040080d40c00714080030f08001d00241d2003070010317109170005000354909080c100159692000e029000704841e00c401c5810b4000c0c05444c000c0d5103418400078081c50342540703900d4a141d41c0d86000141c4001c00d04022180507405100101307254403070b84902c07440b0304d154503960052903003140100440032044881c4962480302200422180180c0883d42204130b81d040681c0c006411081c0e00140d4400c40c50703c60444140c8035440c40306101e2707100800d0303d608843c03d034050b041c5042c2c000404c11041c0ca03001d00580c00d4001080004100280c403500c040071501000050025620801500982441d0310031307500040b0154842d004c11003e40800e000a080d0103104581c05480d103440d00c8414010510001c00700d08417182d40e0318070a011344e4014a020301401e1583e910028013049100c1c0d100400c940c00c0c0c001d901c641858580084d64900700503088410103030b001458 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 842311187 1250 842309937 842309947
    0x4080c1b0102010c020f0318191d06061c0f0b030604061413030903020f01030b09090703021c020d200d030207090510030209040204091e0b011e0f0b0c070e0a02031603060b 75
    0x1100d1108e6400310985904054080000c104030501c0e820f24402520810481c24030403408034090896400004d030000f8420481003008803070b0f030b9040c0002807004400284011803c6091109400000c01a21007126094000ca40c1040200156603204118285400502d0491522000440c0c1210100100000c0200b900c0103c02d001500d4810382ca00d4580c034052401040701c00c24140441c90f81030059403100483d0303000300018011848c22440200c42d00c0704054040c22001c9040d0005074120303a40c008042c0ca031000d050041b011604101c0e5180a042102404070410741a107490000c0d40c0d03103428412480c4091031f16020480501c4410208400c60f034004051000c651295020070000340400c03c01200c003110015454070385080a148101c0900c1d01034410281291b1601c409008500041040d08101c0d4a03500f6090100c0c2c0c141c16a02d00654610760f01e910f4651103640c0000c1c2c40c020068101f5441c1001d0101001b09100481d00203601c01c1c10800c4044c2c030702a107981c100707a05403040b40c060318102490a05c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 842312437 1250 842311187 842311207
    0x803160819050c0d06180e0606060412061b080907081f05061212130f080712030509060d0603140a0819090b07050304031e02030a02060304080c1b0102010c020f03 71
    0x99400800c1c126240303161400f04c044083c202c032401c5d845500003454040c0c45124102861164820310180c0e140a840103140c101c0010b091031085008018220740e402c5814000d018255000484040945c0304a80f408459204060301c180340446642c00c0c0780c81894804105404081882d2607880092030344124150101c0800c0300c007810000741000d42201039a650030603406410030003416240450600c43e5601d8a081c0e00c07603021400d8540003074900f50140881040700602c00180401103600284840d06614501c1c90f045070548102106640d1150010035541080015a40040c040340d00c1260444c0c128800c060380b594490141c6440a04142d00070301020307030310111340f000c0d4003242d003402d260010b4940d0721000f07009140d0700b000b02e00760b036260b0010505208000e400c8007022810800702d8100c1e410582140d000176034805089100a0141801001145c208055541074500708441d0070141c4014903100325128180002440b4090700540c280405007402a0011032a505207000d03d4010b0341c9080c0c4808 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 842313687 1250 842312437 842312441
    0x130204181b03270c06121a060c120f090a080f0a02010305090a0c03060e06060a120f11090f04060c0c2102150f010614120403120b06070803160819 64
    0xe00b6401d00c003080c3c14440a20000b9410300204161281a290040030300f4002d0080c21052960010f0701c8540c0707001c501202e49809003510701c0c0c0010080700c5242e43d070092240b215080020809640e03440c11740c01b282c1ca404043d0160b018040c180c60a40700c2c046050b03583c040b090b9a0303591540480015401440344400903512903000b8541c0500c01500300d44042006a0b80c0f04101c10b000c2d4002d66a0750758481c40804070720028048160031034400c031045d9421074102542d003101703031403c220020040c807000c91250041206080c4441401c442c01400e2453354036204031000303c94002150101d0303000f0303d00304400c40d005015084409074140c029004041d206401e9803268103445004841800798441c2e422901c00710711001e00c0d01c5100b48480e54000415500d007030005854003624000d244160401800004542e0410011265015030145000458220741e4042c40000303000001c00b850300024002120000c2c81907040080d40940d1f616900d5002c080c5201c4000ca86a030810ba40400e04103150140c41450a8240c1e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 842314937 1250 842313687 842313701
    0x4050f0f030f0d020a0507060806010f0807030b0a060e031203150f030a080307232b14070f0905101707021626210711130204181b03 58
    0x2070308803640380510364502403504214100002c01603201c42010010428180602c070010304550802421500380718001030318051700450090100701e031140001e11010310903009582d440350302428240c2019101c4800a00502000c201e55010707116014108940c04401c40c01c5910681040c07a4003411011716208021200030b01c00c0314140e00d8812a000b5101042e900e40045014040589400b840f0403202056400080d8091008140d1014148100346c10a0114108030040921b550200b00340a04000c101d01e0040c83c403981c0d4030002a140408100c1c0d030381d07000403420800d01440d031070f02c43c4000c0e40c03541000600d80880d884d000005420b0620345000803041c607807640e000042030040d1510802d036181c10310740050a982c000034600780014003d042020380400e00c85e600c9070001d8068501010390014103030b050031b800300c107201c50000c0c0040e4000c20300101c010302265106008180c00c056149055010703020b03401ca402412350140d000385403903040316114800c14242c1c0c0c818081d0100034000c0704000354003d24035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 842316187 1250 842314937 842314939
    0x5120d090212011506020109030804020d1505310206040e0414010504081c0b012708010f091e030206040f0611210a06050904060c0504180c080c04050f0f 67
    0x1100300d480010703a1002410b1071088401c900008404a0403092501c0c0b00340c40e0740c050310541e403502c01103002003503014803900d5101e5011390319002d1400c2c6916205884001c41010445114034000a004100c0140041c004519000c0300d001c1a4003030001181102511965800942c007280c00c11041001900c6083c0c42c80d445800389440091081c050504203094030307002c99044440303120000300106c18000b0802e001c1007002e0000800c2044203880f60018105c0d03491089449203401100d000071102d02440700540c00a403210b240240040c43c2c0c0c411600014014024046a0414003481b00d00268021224000c0b01582c242d030090116484948680b00c110030740c480d081d0f0321785032584550625501c1c1e0030014050354981300009104406090b0061580746006003d46d54007900306101000940d480500040d046500070600041489550710151403502c25071f8044605d00d0313401019400090003560020307403502a1340d141d00a103544c3e440c0d65080c0c184034a0003201da005080c00307a152040c1c00c01488038061260 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 842317437 1250 842316187 842316191
    0x50604120b06011e080f01090603050d2703050a0b060405040b0a1e06080303040c082121040f14010506060a110705031b041404170309011404030503070201140405120d 73
    0x26401300010049603610005901140300c0e642841414010801824010981c481c0100842421a07880c252984c003132580040400031082c544040c0400140c1d1210080c164034170400ca41103a9034074000381c482040d6201951418205000907856080c1401000c1c0b0903640541c4040140d0ba07010b0856009000c1200d0180186a91f640700c0d078800c441c140325881c0640100350080d44c1f03030710b02454003401d00071183d0445215600400c2c004c10f108d0124400c009808023240110a4403165424440c655102c4180e00c0404091300350024403041c0940001106540d5000c0c06d1045212200005900e003078034015629143c0014040154604a6100b071106481020b1003c0658403401d941d50006032900c0f0750800041c191009181c0c650b0725510303052190583c901c0d464442c01606150680716a01b0380305050902221070f01c1d00100280c07842c0002e501190340d404027408a0b410604050038000c1076504100e5040c00558a8481c4a92002c1486114a8070565114005041d2001042c00302c0100d6040550301c000d0a80d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 842318687 1250 842317437 842317457
    0xf1410030f0f120305150102010b0a0909020f0402040b04030209090606031e010905061918020d17040e01030f02010905010315050103020f0405061611091509130609050607020601050604120b0601 85
    0x3c2c00340c8428208020303980d0b40102e0f1074140081000181884c100c40325065a140082c10309040c0c554004610486e101381c00b0029020800e0300100d80040310105116510030b00c0085e01103907503110040908180c9000f9a024502e50b0740d1400b4080c8c1c4c4490a40d4841e0b4103070f0001c00202185c0c01c00c1801c520314400a0b0340007050382c6205555152a0070300a58020b03078254010303401c02880d642030b0700c50382416500c000100640c102007a000b10b000c10020740c1c005000300d10340da454410702c680018101c1d001440880442046980d480c10442e03841015980708a00040e690803001446601c64015411000c0d000c0c003983c481f80749044010750080d400300c1c0c00380c036200703205220000341c540c2d5240183c401d04004010305048185c41d80741c4245010b5802c000741d0710a01928052000e02d19522181e4015180c0c01d94000c2c2e4152103500f03040041480e440700050240c0c1c1421884010031001050300c6000e0a045d4003190b4160b62503404001d410301440c017444105801100c080004940b41c015660b4020f070041c1403d95802c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 842319937 1250 842318687 842318693
    0xc0a0602090409290705070c0b090a05060a03050601030b060406021c030e0703050303040210022107080d180b10080c01030510030b1014030a020a06050c07050a08010f1410030f0f 78
    0x10310344c181340307070f58031000c440c440b104c400c0f000034a030b10340d0081746450310034a4400b155840f41182d495074012030340c1060000c12840d4a03070f06e80c50004005440005c251680b1040b80c904001d005c0c1c18212901070009052500c4001b007801d0a2056030b00f0f0724056005031501780042003071a43c500701c40091160416407555075a084014050103144040d50041020315500d1900d80103000312000d0000e20541190300407075030000d0b480b4003040f040c140424000070990340c4640b1070a000200780294072000e900c16207002204d280b846003945500211b41c0c40f400180e80d5545e0341007070341c188101c03452240310500d40000740003c510358400c0e400298009005207070045040c1c1c0340c0c1c4500c54038150071100b0300c0222021700410b10040589001c3d030b003102407048000700030300a0f082e4041190103005224050078080042a840142007060150802038400034103a06002650303080314070b01a22802030103204040c680070814484d030654600706442450b03c04004103040e07280d0740c0c031b80000620a16041e210f07000d84520341400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 842321187 1250 842319937 842319953
    0xf23010c1407081603210507061503060c020d0801060e03031204050123060102030412060f0c050a0f09031a0c0c0d090608220605070210110d050105060c0a0602090409 73
    0x1003189070007011864240700a59190180140c0109507181c403510042000451b40005821142c0400c0f0401003030841c21002503c0e18024004000d04540c1440008030f0754000d000c1c11241140d00429060201e10a140401d98070762210303404980015840c1c00052003824052118280c6210000c1c044a140c151561100840d0342d0080d2030880e0075944a58407050415103e103d0400301c40c10b485a40380203401c110001035524419441040d4109030380000e5401808660b6004c5500805400014000501c00400003441544845001c0000c94596079103c451b0030320505008055982c0000602c28250124030302c9029244014900040c1030001c02004d82004010b00091401c0c080a031100b1510900b0104003800003a4020b20700300700b0a26a07500c00c0c120400d0351004150050700604005515110044102e007003a10560b54040700341e00300625081464441c400809421440c10401c00050740c1b103c00304042403203548401e0201c0c0d8002c544000c08203030564024401500010f0000880c0d80080c0e488100c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 842322437 1250 842321187 842321213
    0xd030e061b16030c05031207110f091f06141b12040b070204270f230a05100903051b16090b01020105250e060d0203090f070f23010c 58
    0x540724440c4108100040c0c1034103134010304002c902603d084005581c0c61501805040c40180c12040c6c0490000c0742501e44c541f100481c643c0c045c00011039454076002c6d00f11060b030359042d5546121010440000c403188a4102c45003400360008510f4039001843c4203c2c1d00b180d44c000e142c460203001381c910781820440c62200a000a205441c045520780b42213004210440302104807024440c0b0001040e4510b9914940d03002c0c800541c4021035543c5030700c403801e0a052012a04141d403800d000c240c5071294060100194503200300d84117804880e0400404080e840544043d580018080b65060044a80300c0704001800010556030724121010780b80040c0400c14140c40c1c0341d01c901300c65a1344008070910b43d40d0a005203680b00312100748100e1002d440a140551500707010b4625410014543c2e200c8100d56a4030080b0780764044c2d00c03c820341d02c07801d1000348039445110701d6081031080d01c11440006100041010030104590041d000c0c8940101c0c95400c6c004005c40c02d40c81c0300d04000030710805400060405181c4e00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 842323687 1250 842322437 842322463
    0x20304112422081f020405011b050709020406110f120415111002091201060506030105040f060e090607020d020d02100f0e07080d09090204050f0d150e1b0d030e061b 72
    0x4040e41c091092003411800ca04548860130600410090040f82d82081080740c100c95241c0541d40e10f07407a981005400c101c415001080814000500003501c940d00410150716220321001f5105810000502540d82e90318040700401c0c03a101c14401000840c5100580c51391200b2642046400441c211045604003405242008802640414942c807181011640c210003581c080700200032490902001483d2404148076052040d5180c52086201460541101000300401c0701200c07480c2c1041d00b107042d1600d00407590170700180301e221501c0c41c1e240e20004082d12215841d030041c0070750703502c07088080e4041d001c9000e415081036110580c03604600c400300311100043c01420042e220f52080480018200070b49a40708440d07140c01404140075a58072101c002c001c2c2481110400041c200c6841d1460581e95a03007000301100f440d0034500ca4030310304040f500da0142c8000d0109030040500320000c200141100000180010320010106c89950801d0401801e03494000701e4821101045000300501d0b00c0c011709030b09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 842324937 1250 842323687 842323693
    0x8060303041a07210815040b180402040b0907120b011e030c030627020a180807140603040b060d08190203130b09031f02040902030a02030411242208 65
    0x1030080c4072241c0d035040360755859100020075014040311300500c154070107424015406030700280c0220b00d41e07a960100181d4140509000340d0303c240038031610400442200c0aa0040e03040c8500c40c0d007507140420300c603171140300e064031031540c08405008580c0c020010b041d185814002d00300000b50040f401d0f0550315a68610959008c51805000400142640c845d540110034001c1000d054103680103d116080078000f041c1301e00161110503116084882003054503042c504040c2c81c101c007058000c0b01298074026115680c2a0060b000307000d8040c000288400c4901070072100c6200040b94083ca81140c4850840d030081492904000041a02640d0f021014800202580c0002030b084d8411207508a200c000b0005120030605180b03d07080401e448002c0071f503605802102001900003c109694156800790410032001c5481740381030344641e0700a600070742d800d48043c00d10400b1100c0790b01d40f0b00440030030705894040c0c8045061030014050302d41e400c1100040c10b0418042c3e01f042c102100001c688004244040c01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 842326187 1250 842324937 842324947
    0x3050405011103090c1002070f090f0b0604060c290f06010c02060a091e051f03150b0408010b0924120a030201090b07080702030a0f0201020702040627180308060303041a 74
    0x1080100c0b40c2046d40301d8155000a00c0800c01b0700d4002801004440d071240c000315490002a003654000c0c000300a1966004001007404200b440d8080000308040e84030b404281110b65003504000000b110411102401007590070014030b24289081d640b642049042c10b280311040400d90004040390000c82409c0009114604104030808001055002c90486100e802d640b042c2818040b0f1002010908c0880c0c40b0030304a0102d400e483d02c40c0c1d1101c0d99048100460024071521a01c00400303035401b902c200b00c15982000001c0c1c0a40c50003444283c080e098035190b0107840d820f5003080c2d1802c10207038540e09034849130601182c0030380e81c0e041c17000c030450714402d40c00010000120f245c03844151a000c4c1944040128010402000d80d40000032208040480e007400344140740d040d507089000e4825008001e400a003400b000240c2504104810300c40480a240d64103040c4c01d00000d140129440d144151203007984c960015004240a0a05190464001f80c00d80e49016200d0045030030400700324a0036004040c2c0014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 842327437 1250 842326187 842326189
    0x3061806041502120703320c07031e170f0709060311070f080a031b1d120a0303050601030b0303160209100f0f06204305210a0303050405011103090c 65
    0x89000e1020428424080040c1c55058428011f0078000c1013000e040400042490902d801081a8560000098044440303a146050020624115120000c0d0448c59060114924840310030342c07a889140e441e83c4428100f481d010b8114081d100005848101d01010044240420100a00c44403118080e90119584840c0c4560003021584407503c0d0080d6490445603510300282c0c01031856007150b0311200850200b13880300e40060030b01210080104128031440401504042c0c1641241c0d2140409880c01c00840c803000c420f0607224420a0101c0100d4010300250800614040c05102d0b00507034040d0101c5055134554100305807925868101446943e10300304100080e036800000c14200210341641e007400304502884072642c0b01800302c6403d280c1c000c1000b9604005a512486010301402080d94403501180505a2601a0304a0140a004951500318490454440d240007409100300e20000c051400c1d042e24210020140038104442d43e548031804141c04000841c080c502030300e0600050805a58064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 842328687 1250 842327437 842327471
    0x40c0504110c0c040506011202091c0b100b04180f0905010c0903151814102301050d0507120f02101d1f03020c03130e040203061806041502120703 64
    0x10100c14490350414003003040699108d036400a514144000260303c43c10440006100b9891408010b1442c040508400d000d004641204074041e00940280111898880b07000201c14407850081e01c2c580840354000b280c7c41401039220840e42e0b15429000034902d201a550642540c404018120014011038024410300c034042e21010ba9070181c0c107008020811078400b180704c0e84446074401038202c01098000024100d010701c41c038241403000201c10404c00b01da40c20124085041c140003c0c000410180000c81c2500b0034015034104190041d000b000c0c901c2c503040310708a007140722000032508049d00743e10400050f10b981010344030341c0d0b405441e0400c2d50201c0e0020362100503180244070f0f115400002e43d1031079001005d0031070300300654907213009650b561a02000c0740c41d61040c94040b80d140e0100c00c1c00040e1a000ba60001400759208405540c0703180ca802c60810a0004103400010719074104501081c0020711180105104007150200076003841e0b40c842c0821480001103805c44003091301c50b0a9140440700d92 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 842329937 1250 842328687 842328703
    0x8040e0723181206100e0906060f0307092d0c09180204030b0406060e0709031101050a12020c07080f0706050403060209030705030f010c080f0402030a020108040c0504110c 75
    0x24608100d42046062610521aa1285401030301d030000054100c4960562010784a0014001c3c050b21101c040002c0840e560b0f100444a14041074000366021a1041a02c902e4500440f0170000510540e2140410008185901502591f06116000001030002c889000d000c8000c0071030f10100390101d00c03078404040080d0070170050004080c178000c8940c0c401e54000d03d102040d80d0803581103101e0b4500c5421782070000c1c031a582000e0700c071080d80313010401040860f420080540303c01100d81e00b9a91100c54042c0d07061811400000d00c00050104140302d0ba52040000e06009480340c40c0441940340030280d40e07012070344404036051854001c0c100501409030308100a52090484d80010905c40e460540014100e006c0e80c000240340130f0300001c0c0b01400b5541000000c001d0a8010b0944d41225207401e038040c0207182c01c07010000440c40c1c00c000100f42005840441d0312031034010700680540700050340110b17540e9200501c1200c91103180c22003c2400d0b00c0c4c510600400c0c2200350708503541c800051410905c0c2101e9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 842331187 1250 842329937 842329951
    0x2090307060f050a030b01090f0b031518130206070f0b0412090605090402090301020904020c0d121404030e1f02160b0307020a021e0904200a050603060d03030e06010308040e 76
    0x818414601c500703a10001300d400103071591400182100d00100100c400071456844095089804400803c11040d0100210300541b44220042c41030b400740803e00c15113030213103902200d014040d21300064500c03021000300301503a80f00902c8646031000c1d940e00d41342c0d00403a007201941d0300780d1920100310070000310b0300065281110a0a220090300d04d407050003002840b9002700c440c055500440c440c6002d0300c01f5019a0b03080c1310014415501d5008040140d42c1e01c0509805050001c1e410742d0710b158036a07000344688050ba044000100c490b0b5943d644007a030f03484607240324550b00700c07101c4194141d0a20030300c514100b070b800503a4041c10408146000c01d080c1a50260019480c40e5810428008080d80014000c0b503d19070694000503040920400000000c484840701900400c4c0e01007007100b08070b0b1800031980c40c400300b4288050010489020701040410b14094a60003600404c00700e411407400d00402e07408140f081c6408110741080324003142c00d1000a83c003c940e00c103000308040c03105501c23000d240381d030240c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 842332437 1250 842331187 842331197
    0x3030f030902031905070f0e160905030a121107060e0f06040f0e0603030705120301030312020703231e030601090510090306023406050a0908040b031003020d05010209030706 76
    0x141d503070002500ea8650a4841800b444240142800c1003010700200c03005003d02c44880c07110580ea154000181c9004031003031011100e80c401c2003090780d406901c414083e500c02038024644420655140c0b00255150703450b400a00c00039181002400d1410060800900810b55507000a6004030703051203802c141c00342c012031003444140018031100c00c2881d030407000ca60141d07442400603294100403a0961145440280c0319004000022403400070305402581243e00c00d5030b440002d180c2a902c04000c034022540000d0000318400d83c5404210381d462042690400d40d00821450a40410410744290a0100c200108c629020040003025a0041c01032001400145ca41c950648414003008102940901004000d658080b0b03000000b13401e06400c03035401f1100c481d9292407094003901035600389241500c084600c0d81c20a400101000d005000381440702c0c0c2d004164038149030912003240c241d81c00042c40310f0a00c840c0b03108008056540c0480781d04050780210001a520f0001d28203040c00c0c40510342203481482 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 842333687 1250 842332437 842332451
    0x22107090911040c050702061303020306060603070215041524050906010c170d0513121b030e03010902030607080924062404060906020705240d0b06120103030f03 71
    0x351540b181c40c8842074101d4001640c1e1514440542e40c034041c0184c040d40010000c100381050783c20314007481c01500d0080741100c2c1140d0b104020002c1c28441142d80380016007100b03801c07a03c0012225042504248180c00398580312100500000854038828403aa803524240844c103070b4004034251818000d40415540c041581c5048070020b40f0003106c20380000c120b44490351a180c0e03034200c130400303564035421841da00740101d0030002806080307a4221841a41c1d907042140701c20302e00a0094100c441c81d101c590507610007288050300c050391110b400d8010300d43c1554840c1d10b2030005a40038000c0a1007540d81b0386801c6a24105044242d00d8050b0380380e0000040c20000703058a4003800e8100d94164065411102140301c4a46401e0b602240203652480c41442075000c0b50108405402c9050307401962919400c55005968410801444100d2140720b5080081c14800307490703144001c1001001d03003d80c0c1d03881c040340c400040800b06000c0e5008081d8460400c10610040c800c00d6441007980200d84000c0c9801e00102c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 842334937 1250 842333687 842333693
    0x708240603031e1c0603030804050c0409031d12011b020f070f0306020d02070f03020102090f150901110f06070504050a080d2012030a1401060504030b0a1104030221070909 75
    0x41d010000455882143c04200340140e80c84054010002400100b070511a8507901d01c0c5c00340c1903070300680301205c0d02d002d40f04603640c680c00c1900ca5a00001d4065941c82402d2000c0d040c0c05000b03050004a403a00941603103031200300700409028108061850340d90300c84001d01d5000c4000c3c00c0480c030782d407a4032564001000030000d000c04584d402c000d580e000280144d40e003140240a2000344500a002032844108540e4001415019405050311100565012440c001484200030346030b4456107070010030700001d11100103c0c0d489606580c1c0002004d00032107543e80d50503000c591520300211080d0f00043c50018081c01907044c014103002c0248402c1c0d0081010f50110346010b08075040d065274050b01040848061650310b24200314010130030009824080d92800d10044400142a1009140c0a0a45040700000f0807030320503000c803801c0780e80098000c80f054542000c030102030300e000d11980c201210148000704c0544d54151150400001501c40052020b014280d550b00348499035200e510303024540038404000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 842336187 1250 842334937 842334967
    0x3010803191b030201050709121a09010603050a081e0301210302030f0a030f050105030a02030d0c03020c0604120506061f0c08041703030403090b031512070824060303 73
    0x203401c0c0da940d4032003205407031150101d800303000c1c0d0385240d200d0300e50005102c800d241e01036100d00d0007904243c1d03411003a507448840d00e40d60240c079040d0040c1001040021851a00404555150480400e100100e121542d0b130303c54900d0b01070000003d0f507030901c0c005002240d40c4a40c0d1310700040034031300e0903a0504541c500101d088260410750303140e4005074014084041014402d00c101d416000740030702083d40300ea03c7c0010080060a484908070a901d01d07040022949150000c0c914203240e60045c000c0c40d021f8540c0004070707070302d0920040890a40c4901456948240e440d08040c00103414050a514460300d40760600c9031a045015080a00034850250907040388003145600d500b01070406e08140020802c00e2030054024481d40d80f044c0728407031825a0f46c9003541c1c0b0110081d8002c038065640d41005944400300c0c41c00901c0190789044c8100244049441c15084c401440071000718803c00790745d0200d90b139001003401c102800d04549004929801506a107400125419070400c009900075414141e41c4889050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 842337437 1250 842336187 842336197
    0xe070512090a20040615090302040e01050129040b0316030c0806031002071a0109060e090c01080105040c0e0405090105010f080606030601031e0623130c181409160b03010803 76
    0xa92240301c0761041107541c0f541e03005400201540c0f415031b15219145940281100c080b800120310803410310513081d00b28001405154180d41d410000100c006203250359040c4481070002e450300400c0d90034400064118448000366100310800c0100500206965500500329000d08420005114901c403d1081540b000240203120060740003006070303222547d007040d03000003c2421b4689040040b010001c03500c03804540201048130304040c412105512201c800d00e444a0200e04a1400200d0700801040381d460150440f00009100d401c103000306a03000d6000c5826607008a801850030703034580004106106842d42ca8500604408000c0c10340c13400d0880000340c4a100610000d03100b0603002000741c0c0c0c5006e076001020404c5a101c01d0811a503410710640c54001c401291400d62401d0150b000203061414000422070303259400f0f01c1c24079510707003008003007250b01c0d03854002c0d40029540c07505040c0340816841d10190050305114001c0c14911101c030094102d881e416045000182c4061004020101000060b10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 842338687 1250 842337437 842337473
    0x8010503150115090f0b040302210a0213062d0902040605030610170703050f0609010b09100504180f06170a0b041b06030203060a0f050d1b0e070512090a 67
    0x110000b01d0301c3c80c04852484440c0c0103282103001c001c40c0001c400c00510000c10440c0d10940b0b26410881003070301c07080c0c0ca580050030841c26a800c103141c0000140f130110741140d100001c03103000090707240d103800c9a40101601c0c2c00c140d51240c810600d030903c103225122112002480703600c50562500d414890000c00e0350101411090040700c039408580d030300314011382c0481800700d0514080703021841e048e080103001d040c003520035052091407440451558181500f087d410380d01c03903482a61900d03914900307101c1c42c989211015001c024041c8800300344668146642190a00c202c0c80c0403444007151000c100c12500c184d800201d0580720003212000540e00410b0400f95142c021848040a540e24200080442a0b00c092100044050380c00858415056400340d0300584050358002c14041e00e400718106a10300e20b00985070310818400c1140005100400c00381950003100700124009a030320049030794110741c01c1c0c0300040855400b0480400b090090310301d2a40c8440801c0041c005141683c0b60440c00c00240076402e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 842339937 1250 842338687 842338709
    0x9060d02060c010207051c08060102010b06271306080106120323040b0f1801080702100c050c01020a0503043509010e0d050105060312040b03010501180f030b07080105031501 76
    0x2022009400e44c1510805600306044d40c10a45100110030050801c0d02240b40204104070041101c95205100d041d07415040034004629101c0034121114071500415007405401e860b0001c10403450b210000e0a080c10400084082181030801107501d00792001138201d8051404241461030109a1122822045421005034a4095400709140511910854105600814001456403812401003000700070004503562658040d01100c001101c20328402c1d2200c03001a8070008140a9841165000e00740710909403c2c16807400e11103450f5142a600b1000041003c0b079408402c020a0101c003010410b0400441c0d58042031903406403038100b81c15640000208420715010441103080c1e4052900c01c03040c02c00040007141a800c06142c96400380c101203800724041d0065082100c02c481050003a141500d94200300c10307046030709103801103405001c3e016003c801c80298100001c3c600c00380441240186001d42d444410700c1c60704030406040e1940c10b80c08240240e120200c0841c880642d41c0c1a10b054074031004075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 842341187 1250 842339937 842339947
    0x31104140315070c060e0a050a080a030b030a060905010606050703021005100314060604060b2511090a0f1116030f111501030b0606040602071514180102010b09060d0206 74
    0x210b0300d081c1200d0550040c9034140d6041c002180d400801800320144580307814000c4940b0500210b4640b12000e400030800e40c4110401c200243c6040c0162401205903d00000c02614800000303281241600307094440540d20010b41d01807210038096400949081c1c10000d00c0c203021950000d44d105c145042c0300c82819a038102095040d6000200384000f59000f0101c02402401c1c514003e0701e892040e240c061049103081c00000d47d50070414280c8450141d800703501250041e0301020385c016694000c10856845420b8071404141d0b9407422404c1d070040403c64800900c0700c5448907020100e802107400d0904410782400443c040380c2401c1164400c550b410324180c03144030890b0006682d189840125070a4900070003044002d0075581000b000d0489008050344046610364030240700d4588140d00940700140c100540900c05410300a045c4440c141d0140b8180c05201103007141c070a1030fa044030341e141e90b51149103241c260342c940e42401344c114052022078a0103070604024000500c0c2e0007548900a000e0345010079 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 842342437 1250 842341187 842341189
    0x4090b04080c0c0a0303110c040501062a05010c091401080c042d060302090324040b13060204060c11010815010c0201020703140123010f0e04060b18061003110414 71
    0x4540300070014013800c0004920340364a0090021040c81410400d10710403685488410b2500c0c0c06224100e600b5500c503d1189801c2c03601103001c4298603944840d81c510104403800018600f440b40f50380041c880c0c0c0e6110402410036254108040c003464140381004104001d014810310040c049030105c6016070400001115a142400300c1c10a02841d04030800100c07030000101c0c20780580081c203501208905559a96400700605001c1070341c840100c2041103603020004000400503003181c0e0f0048656a00207005681c5690394806036409608110001649544c5c40c0b010889000901441e403002420305046a15010203014110702c132000089040018204039081964024850318000e960071a01e8000d0040d40344440c0c42c040e20008945443c0418000590701c0300c01c2c01c0d41c001c3d80c1a2074410500c0c2116929190301032958410203403003960390a0380c0c5c80c031080c259640c2c400000782403190303007181c9201d070b02d046020400c1600c0410007510605080070b0801e080140d6400c12102a45c80070000303805050b810760 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 842343687 1250 842342437 842342443
    0x1505091b0d0b190f1b0e060d15180c020d08130b041a091204060e1804060b01030507050703021e070e0a0e071d060f0319140c04090b04080c 61
    0x110082c122408040034080c8419600103064020b81c00d1542c244240642900b000c001c481300701d4043d940401146070141045403203804038240d6248000d000b1801c012101c1600c100704c4000090110440404160410200001107502c49450b02c600004110100b0275440294943c100f4403a40c40800005c1d80c00681c0d50b80802d5840b82d016038009080c0d003060314151a01c058a0603050b11948200c42c0010b0018040c900009000380c800c0c960748008600302490240107880f0341100215031070307203c024000080410403842c48045c0c8668010403001c560b00d102000090100c03200500b0030010014200001004207070006070320440b07941c5007031012840c681c1102c6011b00b00100c64005100f0441e10200340507aa1031140c002500310a1500251484160f03a40c417804146090020b442107038500e00c400003052031030001b0039a000c04030050261640d2101c1d110740507807503114050f02142c0300d00d2241d0300d01161080810500d0080182950100300d144085e85903001d09040060000300a031400240e42a0029824 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 842344937 1250 842343687 842343709
    0x31d041e0f1a061207020106051827030405060325020607021002121602070308031006090b0703050f07030e0406030c0501080a0b0f15120709031505091b 67
    0x220040d01000e03800800d120140c101064503415141c103111141c60b10300c0c504401c9600340034005200c586045640450076076a520000c1114066541c0c0c1c003000100b60300e94968190407003000d142c82541c980741070352480c0440d1020410002d00c045e801102c840440c18000121015100c04540341c5847e9503030a044900b504008660484100c80c0000070950b1640e000103225004080300c0d02a00c06c0120000c40f08004c90081c51101d040141e10000032030100c0d51003424200c0026030a206550100b9129140c10704242c0c000e840400c42180c402c2e504100c01c82c3d00030050300c054a25a1840b40c9020b0154600400c540aa23a00030b107000d5400140c0d010426005a55003a01810054028001c2a03928141489200c107988106400315505400190602106215070000c07150001c00d5a0500c1c0d02503000d00154000b4801c2134400c480e0200400070392034030106040ca20500080c0d441c80c400d2070461074510714811204028081c3e90703042800703200311003101181680d954061811010400500940050002c2c045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 842346187 1250 842344937 842344961
    0x170301090f0e1b22150302011106070503070309030e0312040602010b06130308090d12020c120f15100b0d0501050406170d1b080c0a120914041a0a181107031d04 70
    0x341c031a0409440200c000800c049038001d07201d4002c850490041e05031268005c0312f00c030300003c13801c0000a004034000e0340400107031800b0385440311148040f0001b0174500301601c1041162411b000c5810030200c0c0e424020082c8250069550508100103240507090a0540d800010060200400ea4007602e0b00d460501e450100c0e00641c0400385403543da04060340b02c401d06c40c03a843c00b80640e5820b264003e48005554021000b0840c02041e00080d0524040302551016100540761780f0044000030b00c00c06114094801d95040304000200c651400c41004110b543c1640701325070f5841c1058521a2545000c64106090485070820402010110400440185c22000020500400030400c41c03c079181c0000c5031140f0520a06e2940c00c0d0f06a140819507000115116080e070310010404060801c3c10319401c00604041c1310000504c8003058900000c08103282d84d0040c580443c000468904150301c240a00e1036003c6e050003c04d031030954152002802c040a001891900300d40704a0070311418fc4070740c1e011000d8506 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 842347437 1250 842346187 842346191
    0x201021c0507090b030c1903020c010f060f060305042307050d05010911030f1b0301060f0303022a010c020402070c05190302030c030105160c170301090f0e1b22 70
    0x56084402001c055810314000f50890601280c141d039118201c900480d0f1005075141420040341034a1041c41c0c01d80d15420170560240039031214403100740034002460040c0d14010031110b00b001c0814241210302d62122f420541480240004181c0040401c46400d201034800c0002c030100c3c0c180c0c14600201d95018a4000710406c1c3c6034002e000040d40092a035030f01c00c0320001100a22402010355440c1440441d80d410303003100c40c50340120b02003803c41c1d20400d000034002003500c90340c0319070500006007180d00a43c05a00414012000e00300b48081e417000d0540842c84100c000c0e14a00c0000703020940486009008a50000e5400c061104c0054004002c08001b010002e450a0300e420800103c1c0c100c2c88128040d21840301e0144140c0f4040c090241314001c825940c818940d8070100c1200c403414fd141081d0360b460a840c0d00c00c030140c4414801507000c2c0c8800c08001c0b40e40580350588004980b0b00b5200d0401c1c0e0f41108210643d60f94081e801e500d20981c046400c59020350300741c942103500002b840201c0c05014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 842348687 1250 842347437 842347477
    0x302150906040e06031e100f0603021005120c0711270106020f010e030c0a110a0b040608150d0213020d06081b01020105090d1205040f0f0606050a08031303080a020102 73
    0x3c90078003503044c460202941982e40d00d007071543c4c04040320840c004803040b80382c025581d80d0311012181d074040118a90a240041612503981d000718901001a0b154034000510029a400034401903190716034201e00328000321441c0c0030707031500c4141d2001980120240316003039032200426a010000310081820622502d8007165507906d25000e9501c21708d072000007a032542010042090700c540801543c00525544011708000200c44d61001006858805804e03800b00000d0700104070b01442c480504042e06007611407048502f00101310f81000e14014640707620a01c0c151b0031a41c0181c691204002c0405100314015071104010b2005001410558000c10068412104c201c5000c00c01c5650b030310250042a0000c110644030320300b642d5150410403035010301180320605112440c0640d58002544240039000700d481000c202e40d0740d10740c004003015083d64100c1e11210180814039005841c640141003c800030742c54819503400c0c0b440f0b018020321000c1c00c1b007500032562100b034034000c1d0112055a140814040108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 842349937 1250 842348687 842348699
    0x1b11091b0931090314120c2b0506090610050702121e03120a05010e0c090307120b1801020a0e060c0106050612010305010b060703200a0605090706021b0a030215090604 73
    0xc03d00c011040c0c000032020603100c83c001e0303807050072514040010905c4c195507030340f031910100c01030307001c3c0312082e10315003440074660090300401c2c1508003448411100800c0c0c80c00c0000400c40d2400c40500b41c0c500c01c811000001101c15000030455140310740c103588090420328807071401411300c907a4130907040314001d4800e0300401581001c0f0060a200100e104000340719114000040110b0350309019084890190340c02043c20341002a02400d40310100900b00c8180c1c0344c980c0703c080c07424036200300121011340a0009000c1d211458a095a1106446400842c1006220000102180e0021141500901c0d00054507034101500303402c184060203024003032590f0f03032110842400351070b0f009220688455103841404409850510b0440300c0c903d4240e92104800f0044103001e00291780c5040b56031105104590007000002c0403801642c3c0700380200806070038118640a00681095580810003016000c41c603180c0c0070710743da8420203905070381e019104204200c5108180c10000e100d00d004155100d64041f80010311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 842351187 1250 842349937 842349941
    0x80403121103090d11030313080c01020409110d1d101806140403020706030513080a051b0c0f0102070515030606040b0309010903110303090607030c1b11091b0931 71
    0x100c04d0070782e1641c0c0c0104c007059a00307071640001c3d00e00c030708021541528140450044005010b4556100380014035207036482100c2421a68201981c070b040e00c001044a510502c1c2c076118090154100142d540d4603160108491521600408450039100b660703115070301040001018140d03c081d034003032001c0000d91003c00c0250540001213404500507c03400001249081c0306c0e0041ea40520100c1c012061882e8099555201d507402100b102c208000e003c0c012034450300c1c80c41001c41e40030034803500030b840e403110b012090110070907040c40f81c00c1c15540641c00030849502c6440c000c90f506120701641503142d031100070001c0e5481c40340350f002c003402e20008400d0151445040d40401300c0301d84240c440120807003e445070395849010031580c148554201400107661a8045e800c00f0103c40b90618003281505a110350b5403500360034000054450503400c129007042801e1202c1480d401c040701510341002c0c1450742480c11004c0c07103041101030180e080207008003003695601100c100f180b011440c02e00814a03141800c100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 842352437 1250 842351187 842351203
    0x902280221031f030f030f2f070b040506040902070f020d0b160c0b070818030406031a040204030f08070c030f060203150909031b0f0a030906090603020a08040312110309 74
    0x2000d010022100d600c14880f950301c2c1c0101d0750b01c00b81d500a880515142510743e07503410003440303080c444a15211400c101c1035500e80f400520360b0400d095200300300c00001751b16000c00c680140e26240d20410052100d682c1c5c103400e45080f2041c490000d40d03298480d1410700c1e0360004080c0000e410000c20701e2420704001765508680e00c113103020000d030030610502da1001c490750009440301504021070200800c002030701c1124044c5d480401580a2071851414032019072860b40180d210700700180d038800da45410032101d100780340000c0c4c10441d400e40c00c160a43d21845050300f4401d00c01400c140340019298208035041c1007202c019500405812542e584030705001000c0c1d0300442d981d52155443c031140050600c1d065142c41d00a8074024001d40c102075240c1c051030300020304440078071480d00c588076807009a02000c1210354002403007941c550304031038a426400780001519810034010301d4018084556000da00c46d24080c1e0268161a0441031070b80c000a96034000c01400014848a040000401c180070f40c000800705 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 842353687 1250 842352437 842352451
    0x60d14120f041e0b07080903010b1c0606150f0507060b030d0c060b0a3501020703020703030807020706020307030503060d1203061d040b28180c090228022103 69
    0x5003143d10000b40ca030303481158a0007203007280710042c030008000c02c40510141c00341d000f0280001038410301320700000b503240054651f01810112107402c81d604010240c0a10300084c64413641d02c900148024102809001400504000f040b10105d0351000b40000c5070400c1d0383c03160018081e60030b4146100720041050700440401d8070450b081c00259002c2d0304200300e5060450720304d00051026105881c00d001e0310b03040a10f00c0c102c2020f2000450615070702c804c1c07008160041c440e80040038002d1461034041d02400e4010b1a010a54100e20001c2104640200450741965403628081d80e499440c4000a00750503503114000e000c00b4800c50b18203444d140c040d844001900c2c0d00e20b000c0c45411500c0c01040508070b40884006028050742d00100e00b002803603281440715800c115040d203079820020a000c804480d24108400c00c4400010441000e000800811300054402c2e0001949414241c09003000c500e42c1c4031004806c28002680542540c0d4800d02074116200c12018888408034600304420740513400550300c41d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 842354937 1250 842353687 842353709
    0x4090e100e0c01140d02072009060315071209082106190e0417030c04141e0108061504140906010f0f0c030302210405010e0105060d14120f04 62
    0x40c519641c00110b40d00ca00c041603649652000d561004034485412888003140c104d43c0030b1151a00180b800e03412052200904542c3c5c02c3c2c2803d42c201004040300001d44a507000350420310700c40342d0f05580820740d00c0e401703031990510140740030304a1a05001407c1c0c0c110058007110010614840c205040b07c81c04515102d003078520b0b0070f2030f140c0c0f800f0040030942c15145c1c0400b500a0950070003142c15030b001c41e41c1c0d01500810100c06031245900c0c0d010420b07802140e084500120006084c400000705080b103004801c0c060303400b00c08480560604480089841000782d0610403044002802546d8420381e44c00300e03010403184e41d516240d0700d94940480020081000d4441c441100000b5010f51142110a070603c00c030f0703600d44801504400f000d44040b4030103003040c4d040540030040d0448a1402201501010751102d65501c1300e0700e0b0900300103003140c0c01f856500c8101e0341001e061000e60303a0b440e0301c40d406c0c190700f000c01c40d142080020603091070050703258138a0745903907001304004410f074000ca4041d004550141910f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 842356187 1250 842354937 842354951
    0x31e090a0911220f061107211401110f090f1c140f0a03080702010f0614062101080a0b16050301210204050a061d010b0412030504090e10 60
    0x159012a0207410401005002094100240d1080000301c1d103010040c07401c40d030b511240844d1900d03c0580000c80425040340702151402d01c10800311005100440d07402030111100048018494603103c0c000e00300003210300016000712130030340c403510103807180d82840ca039111507076140c200503504105801031250f12880490001c5080078000f045001c0e425138190340e2200010307661218084405119400144540801065205420018900c41c58000d4440c40c0451512841c002d0039240e001c0a825140d5041c800d081080d101040307030035072003020100c0c1c0780c1c1e0f2510004509440011540b030802480d416020000241c802408956001e405014403d0b20000c0da65400d1045900c1c06121b0349000090010170040080340ca5502a180000d10451194140c0c02842c0d00001d043d100240d500045007983c80a0030820700e40307405a10012240750321003400056240c20700461682c000d40c032521898514410301c000c10503200d8000c48018001000003040240d0745075104503a202080d82c020400d281c90102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 842357437 1250 842356187 842356199
    0x10c0e0306162c1012060b1905130b031e0901091a0c130909050f15010e1302030604060e07141c020d0c06020c0442090c1d0406030c060e03031e090a 65
    0x800c8410404103600300c0000e04803020002c0710103511145d41510780844801002c01e01d985180d0085d0702918840c00480041d49015103100d96015010300b90040c17070b03171401802000085aa4500c00380a004482c1484c250f5503070382000f0703c441d10540032114f41502c0710310404a80e2080c507900064805010300c013103503443e41095801d1950b88208012030306000c100140104041e0035004043c9a120740031201035101143d907580442d2070200180d408030b8400f600d512a08041c41420001c9400601c1c120103107440d00c40100000c61049154400304201001000d02080f041d5241c1c0703c07048507013640c81010f0008103030352804002d41f10034840b502c591083e030030315101d840d61021a84000307592940a804c0c0000e00c04c0c0d0703111000c0c3d849070b00c1d4030080b43c01f000d040c4001a000e4194420070380031000d10b0710340f10000640d210042944154404126228928040007072000c580c1c0072007010b0646009052011070f44103540e00080c070f140115072004500000242081812095101c050406198281d80750104140c88070f03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 842358687 1250 842357437 842357459
    0x80a0606050d0c09090c051e0102060603060106050a080c1318050601090b0d0c03140a14090a03080f0a092f030c130f0e010c0e0306162c101206 63
    0x2040c041c02d081c500000a00030b015145d030000d0191072168099428803a5103101007402c52170441001007040d1403010360781250707580501c40c0c142e01170402c034060400c641c14041c02030114040c5440341e10401901e00d002070b003040071100855124003001510326241c903680380d841e0850b50b100d44641003110750418020400550040c1f29881c01c0e1203c400030386007050280344022004100c01d11204c0200342c0c4943d40c00500381101510310303004030301d0440e002c107201003a9201d00204800252402810341d000244010219502044840d003094070412814540d495440510028052555000e05065420b090307004551803691000d007524400c55440e05a4141081c040503114801c1206154010b01c074010402c1012503aa40612114546d04100007072081c00c4044c40e6003106e00b02d016240c0419100da8800701e0703501d02000115408464810550580c4400150042044015801c03010f01082d51880e03074101031418a180d0081000060040070802c4000d010040000820380c501c04400e510746070b004a101c148907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 842359937 1250 842358687 842358709
    0x150109171c09050d0b15040504060b0a080a0f110607142a0f010302130e010305060f22030f05070615090614090415060302091303030612020f0d110a080a060605 70
    0x200000d13130602042e2107000c4402401030406011a000c440800c40565451042038061030280c00e001810402907010300c91526540c0e00940e41c1130303210164032000500c0906000b20000d41c0403203c1400c1c55000320200d8028001e4000040000c846500320701c13600ca200241c4422910409464071100410400b50342d071700c402e00444040d4104003510111030320303540280c00600e00c0416100314003459a13925903081039954000c5e0000c079120f810000a003c0c000324104131b4140c0004000d0710f4402c180d0880c42510700c20031702e0107030002c0c24000304002c91480640104203541e8103a8020f04107100310400c0c082e5400710200f0724050300d002d2520700500801c00900105c0321610105015040072101d48a5484002c80f07030306603852664245442d1800400145c85145c0094003071000b41815401c0d64019103800380c00d43c0c60540100400402016070743c4003595034a4000707154000261030b40c040409507030800fa0b03840b050f40040b2542150315418001424000054107000f542d004610801070143c1342c60401410802d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 842361187 1250 842359937 842359939
    0xe0105060d05220b0a0f1103070e0d1a1f0617090c03010c0c03140307090b03070c211e080610030612030509030d03050c03150109171c0905 61
    0x1051140d18111078455122a400c14142484000c161001950708120090011001c80e45041d42800388501041503019a5480c1402d17050140440c88401c1510b0710140070090403001040b1010616416a80300d2003441c000c0c95401a00f844a05a07048980c03c810107019142e8881e01001070b00040100c0146900e48815078100766580c502131a210303440002c06610150042e20031f8040d00d0414200d40c0d400f40715813070012410b40c03240d1805008505010705880800103421709405010000c0142c621b6008807228213a61920b60727915103030340762030004840070b030140c00740100000d5652400c40d042240070004070100c40703100d41d1540058488032900310b03041009402c0e00b502144100d03000c20395929003009100c034400030754600081c0640e0b58464500c0800000c41d015000b24600152502040c101805600e010b00b4003800d0a0150303041200c0f030858944002031641c1002d000000000c00503078130841c0f4800083c1255482070b40d03d2502511259210950b05045c0a00402a64081001c841c05040c848d011948 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 842362437 1250 842361187 842361199
    0x2040311100c0201080a2d1b020109050c0d03051201141009080a080f1e03041205031303110a06060b0d061d1f15090306050108030724060305060a09020a0e0105 70
    0x15000702403405000b402910b06100b08881c8054409890f140741b551300405d07006034010403162040891442030b00100450f01c8c0031079042426110100340c0004446290310815a0070101003840c0d41401c81d168050140011a0103400800004541c0c005441400449034121341b0030040255001c000e43da40340303181c45109003a030412080d40b004038620340080c1c01d401403c140c01c6c4e441d002ca5024400100011369000c10030810010081c4801c1c088000c4903904c0707a0880e410940d01e14103045a41c00402101702000404004d2640d0044e0507030380c002e02803644100c2c0c0c0701070705001d0607031101c00aa00d660402510540710f281b9190000500341d100c03085a00701d49100e42d1140d926900c48100090000100c0030400811961341d100020700784e0010144020200095036a018006043d031809006480060340102d0141d881400781c000441c501d04c5404010810360480c1402e1426090100c2c1c001d0700700c9600142c118001d400c2000f040d402c00e0707040000d1705403007180c0e8a9500c03511040e20044a4000b806019048a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 842363687 1250 842362437 842362441
    0x1050121061a1f0e0901180e030405040906090618080a05030a180b040308090609070603090f0b0f0a050c040e18070e0126010209010c030c1502040311100c020108 71
    0x1803031540480310500d1201085100d40b10600082800001c1004880811100c14500500c0d040d900078a068075a01045543c40b1103949084100040160303000c1d010401150340e06811426080c04004072402040f02504c02d2002c5201820164010200401c00f40c4049003811910f14407410f80600c81012103074000000c07400c080b00c6400480301900000c103080301c059914a000040f1281c01d0000d03009a6129600c042220728007460014074505025045003c01c0d4411000d12031107041c042140800c2d10b10740c1c54000340354211030602c242402c1d4181c501038428150304042c002c0d07482c40b9101c0c0b94815032030442c040c001340d2942c840e0420036105a00c2f958414294403c041407050030040506055050711070103c2d9101c42d01c0b482c0d000202c0200703a000f00d09000d00950252115a00d61004030b5041011500841c01c1808590020f441000740d12402000c100303070340814100308420140d08030b03600301045c1011911180c5034500304031340316282d8182078441c00340d02c00200d00d8240b24089410701340350b0607902e8541c19 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 842364937 1250 842363687 842363693
    0x1507021807090f0902041e080706050903011b0306080f03030603030a1b02030105181603171309090302210313200312120903130315020702130b010201050121 69
    0x29000640701004112019400050a046100ca01c0d000303062054030043c0c2e140e00e042c0d642d0814500d000380602160048060810807210007103035400c2241d02908206a030742c0445400240109039440c1c040308030540850780c000c0520b07407580c0f0507400d4503200412162010418028955640800c0314659810380c820004048618031601244003c0b411100d40c83c0c1552041e42c1c0000d0a4490445400b500d1041d070003000144104104410380d00b40d4018448541c400b421a1140c40c9940c103007207061822030303000188141920b00c200307174250014051000104600344407841c00a459031108105681884814500e40a260700000c00312801280314981805050070a56101140c9000004000b035101201c0e0041c1d0405403414444800c0110070f450400e83da850a141304c1803000c85000e00310702c42390340c001e11095248000c01c80656042d02e4110b081803286072010f00c2d02d18041d100c2c81c1c4c0000d4100243c05d40350040c440181c1c02040310460240c0080c086a82c03070702c60079460030f00300c4040801104028001c2c0404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 842366187 1250 842364937 842364979
    0x50609010b0910142e0e0f0f0303070615080708070f06170a0e030c150a0c0e030607050c0717060f070f0c20060f03010315090f061a09090c150702 64
    0xd2817500c02180c00c07649909402c2440b0480360380004941c607030076845058070b040142d1010710340007114140b8003840130401183e1783c2d0103a0980281081c0c4d5440008080641c100b103903c005207001401ca580d05612000b0701b07602c9900d58850707486010014200420f10b640903440c030140c552950400c040580e41c0d42d40141015001128584030140010003501c01d2405c010b10180c0d145070401c5820a00d2801c02050440481d18054006010001c0f2040c0941c05680c002c03442d50340103101c1d40703801c0d5228050080385a042c2481540021403094001c41900000840450054864080340c1100c0420b9550001c00b950030724010700e4100002481150003c0009070070904090520440952b04981508840e0125200b5840710303040d0fa0345a880480100300b08640b11040d84403c2d0f540c10b034144050b02684d07039414015041c1c484018012616502d40c10008000e0802e00308071010300805040203814138060309510348030442407542c0200e6540e00e00000d2041380800300c442d499405004a4007900441c3c007030302c034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 842367437 1250 842366187 842366209
    0x209091302040e030c0a051002030c09210d0c0203062a0d0216060e0d0203040509060907020328090608010b03040b06030a0f0b011409161b050609010b091014 69
    0x42d000d9940d110401c01000c08202521040c1c4140000305852281410b001e484e1440c00b01454080c140100104460101041d02380e800b440c0c0181c0b0385003000b00c400d0703200301e04451645800403020703c141d0002c880c4481c1d21000340600c4a0080c0c00795400750b150151900c1d01c29030f500c01c00c010050403200200b6160100c1c00001c14402421140060400d00c0b901c81410300500f08440503903000da00d40480a691520074006511444014001940703485d14100110b00701000040035940708142e000002a450340c005c0c8111034020014161803103600345492440d0540e5803146012800040d08400c01103820785c0241ca24074161900007030000d0a507900d0355102c1e40b00c0c20005040981500944c00c40800240c1090b43d4410140e10452100c4406d6040603100084c40400d01000c0e4840c1c4040d83c14401c0d518507000c546020320f00d02d0f14240312140c41200c03507603418012924000f455403007030364100b141c1408107500030756210030304460140d0390791901b00045130070000b00d00034203808080c0101401110f01d40800360003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 842368687 1250 842367437 842367439
    0x7090506070b1b04080f030301030201090f0e0403031d0a03210e1b010c1b0602010c1b0212031e040806060405040c271a040b030f0a0303022a0a11040209091302 70
    0x1620701390f2030300d030b4140c1844002c03048880c083d07201100610031980c018040c031001e801c0c90804240040d24108008405004c0504060145917803508241056842d1071030481051020000700d6600c6101460005c3c14014410080a101c801e001944c0c0303828151401481d240111038001042c03e1928114400c80348032080e418581030041a142d5500091034040d04140d216200224001300a80383c100040e0031b540280170680104030300d0808105035840d00c00101203c01c3c0d0150390318a02d101e80901c42a00d9840344580094841170708004444440a8200060059a03600e1054074040d07103e84080c8026150107807001403d4000c00f0005012400c0c83c20800c0341d00001640b00005189045080741c012945500c10451100b1910030400c1c6031802c1c80d0095889400007500149040ca00c451269070b00d50301400e40c003d04141e00081c54803100c4030184e01400141d20228010210703005041d030f007a60f1380c17403001c0c00440d800100142c1104045c6018400e4400c100c4010340304010941c0c607910603d00700c0003545005c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 842369937 1250 842368687 842368741
    0xb03090a020a0806071b081b0c04020c01091406061819090606141008010611030904020c060105090c0c1f0906151d090c010315030501110307090506070b 67
    0xd04007682e1070040341c200908908016041c1c038109804001e1810a9101041c100c0c1400c0e513100c5000500801d04403507050f0340d6100c01c0c0e52075400300c014403428010081c0300c00e0750043c00420041c03803504041d400480010b115441c1e0044c0c07c0c00031a00d00d03031925811a10740780c0c0f01070620354040140320114000f41c0e104d01d849031320901c0c1040080071030045511001c0d0170360b1981d0b41e400e800d104000003449050b210b000219180ca6880244000061560105000d20010040804a40c96102408109984041c50000c00640d140c01c0c01e1240540d90700c40c248100d5104451b20000303d1100b5013001e0440d21440e0244010b001c15987d80b481d020790a0a00a8080700541e0365010b074480131484511401c141010130b1a41a040e00d0b250080000c044440c4245800c98140360005000143e40001140f28100b8000c0c28003052504030102c0e000f00101c880d50000d0440e500f4420400d801b40d441d14000d51240312151203200341a43c841c0c0a000150094240081c4641000e1002c2003252191105040581460ae811 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 842371187 1250 842369937 842369953
    0x609011206060503010306060b090f130b150d0b010c1101030902060909180c0121091b1523070b0c2a06070e31050906190e03040b0309 59
    0x165904941c070540c81036000440100051040240c14001c00c4010721050200e24101107041d0001781c007070b503540182d0b80e00c074441041c510004020190043d4020300c000504401a0880860954145a10540b58100300324500542c0403c0ca6004180111905070802800910421603900540040640307a030240d9000c402442a003241340e64100042d4407a188402c006207800740240032051130a960895043e060203518050a02c0305081c2c40c840c1c0181520740758020a100c115800c107180d603102d00511090b09194003800125030300e813039046c1c5203100032500e9440503105058140d00c0c103800c0d030002c9880d114100f0208604004070301d0282c040c5403ca80c56031205032030000f030080c00000500500d541030305180c01c918000b80c5142002d100c001ea108040303007044400c510103640014000540d98010b0701141410160701d81303030600001144078020420010820090915484043c0c0c0c1d05012581c148031104080144064011a0f0041c013007400c500000070350a06041103001c08850f000240104218801e03000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 842372437 1250 842371187 842371217
    0x109150b0a031a01030c0509090a09050102030906160513030b1519080601050603060a030b07030b060d06051c081605031303081201150f0e04020c120a090611070302060901 75
    0x40207116140e0709841c0051900050f60b05481c81c0000c0700340e00e605062519105000d8141c100080303a444100403644800740c3c4e80c84c600c158000b400c81c1d40002d040e035071000c804c00040c030000040040c0910313041100d01c00007a03040542107a445c40303442140458414101810800207016025842d0480a44003501d44031000004c00700d0100d6a0a003258035602e40700841c03c202d07a940611016025100544000745075150940c085110281c0301d110091803500324400094400d880396001c02079140006050603580d000e44150500540b03503a0040d03503c50340a614805291549202d010140e045e4800c1089003406030102c21201c02ca41c502106507890700080040e400003480008450b405103105044c0700e034944881100c1a2410702050b006189072119404210090503040310012064240d2850b015008444050108001e4024003011082d107100c1da0150010344d2081802501030b00b41c40c2e540d070043c059941c50044844808180c0e01030040d411101c424005410309078001e043e101010b06010346070805400e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 842373687 1250 842372437 842372459
    0xf0610080702240a0c0903020d020d080d050f0f182a06030a0e060106051c020a05070602130303111621140f0d08010503031209120403061a18010915 65
    0x145007214450143c0b030400c004022548103040b9007051916180c1d112508507400320f10030000c0084082d202c1c0314044c00f5032080001c09002c130360414881c190180454205510110b850080540341c045048100d030002409002d0603011210303030a4500801040901d15083c00340c1420320110312840000007101100e095070b40c0300c0e41d005500a042c1c1c4e81c400602c1d101c01c10741d01400c0c1030042e0040410800108036207802c400780c40e041002c4940310341000513034921501e5019120741c452008024039441c008540c0414204c0180e400d1001c8900a44400c034400081400103511000e841c05040c00d01c40000909001c0034000710f10b1401158845020780b807604a054445c22118000404943e245600c4004145042c0200f442070364410301d0030f402d20365901c1d414040026142c0c050040002c40010600c0300107042c0b68070401c00c228031040c41c41c039034507030b501e4803800d102d03025242500031440034034130000301070003142072413400001c2c1054803541800b0142d08001d2100c0190503200000c14a95408a01c085803206c0e90f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 842374937 1250 842373687 842373733
    0x130605040c2303011a09070e03100e0109050106090501050d0b0903090a0f06021c1224080a0b1f121a0c030f100f0510170403090305060f0610080702 65
    0x140c0d0740503803040c40b4074100340c250356010040c01607182502c3d065004540324a6030160f00071a0b2400c101c92058603800c08245480b21a807001d091113070404500850303414040d030000c8140380c01913000f44200340e1150f182005030382d000e12480790441d0504e20602c0124603510541c9030002c20101c1581d1410b09084d001231850f000326048551031034a055020454140c042101a115415401140c243c90010744405071401c55420b140c12003a80d203551441c0081d100618181ea40400c260009041c1c5070303218900b0950340c0c481c1d2041240c103126603402250905a100c0307505043c02040410031038249041100c4506102c0052a08560f1524503000da0480a41e0520419100340c0d001c01c203158407490035181b0250051005041c0703440341011000c0502902d50481e0072a0166541130300c002c2a10941c0b054201d500d1908000c120351440c20040c18082003550101007402200d02800c201c900c0c03a1590103680040e003500740c0d074080e0300c51024821511304500541202d0390142c0580159000e40a00d6000500c801ca41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 842376187 1250 842374937 842374979
    0xc031205040c05240711031c020d0306080a050d0c031e030207021813140a060f1d06010f290307030f2702040f021603050702031005130605040c 63
    0x6072802c0c007071414054541c41310880c080d4484d072580d00a1400400c414407845e05c000e000c100c0c40001b06450380d1010869015200a109450319228030740010080d01c4003010380c21080002d05005001928002c002450821290081c018043c0b040c1000011740e06501414000c8041c070610710070710b102e01510895100d284650a0710b0140e40d804252041000320044c0c1645107031040311789010b10002c0f10503032041114441c3e10070440305402006200091500781c2c4440b00034a8503040141c0c007020212a90000c2e008041600d00044126914450881d110702c2e00f40501080d401e0000020071111001a030303001980700c801901d0003580c0c074028112060941c01111140040380c1c65829a0310010b80c1d6214a48601c2a450707040340c2c041a075416201141200d40f54041d101e140c440030b058020381c80c40d50444591a458904107001c060703540c1b42c058481c0c2c00110b010f03440b034012a195540d5500359405420302c600501010031a0b88400c5070b42d184000d250140054610103020140418801d01c0c5c0341102d402840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 842377437 1250 842376187 842376203
    0x12120a1e09020118030b0f040318060309020f0a03050d080c070204020a031d0d05041215140420060904021b030f07050705030111090105250807110d120c03120504 71
    0x701d400003500038509050001480240c010041011030b076989406034000c0407001010b0705075100d60500f12242c100c484035081845000c1d00b0001006501a4003c0c0400c9100b542c18010060040b0200704110000c1c2c44042c000703030000d500d914149481034414591000c903404c1124100030841c0c010404a23000242550042030b600c1d41c84c02e8844c07120503110715641c80303080020496042c182400800f0b0703000d10311499a19510102c402030030403c0110884010100c0034104100303402400e80c04000d00507090300c09845960303031141056911001d5404a00c1030301d0000e0266450650244140002548007110401c0025000a0818001d07038084c0020302101d80c181c5042902e89070b4904016040800c0c07030740030034400da241200c140e0703e104051042e44c200e22401d00f001c546601302060751400700c0c400c0301600500380007800760b103c0400c5180005008114020b003110540f00304138009210301d00c440b03d40c02030810010700c20900c0c0701a2060100c1546603200e1310b89017207940e80032100542940c3e810384049071984 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 842378687 1250 842377437 842377451
    0x16020a0b16120b060a0513050607030f0809060103020f010c0515011e090b0a0302010804150f051e0403090905090f07030c0602060c070803010308030a020f030a05061212120a1e 77
    0x1680300c076a0b01c4a03458002810444840c01c00c00060840c070405140e03000703000010032401c0214a00e888010003c220181956075207400e0340c40c004002d90300c1d600d20b4030041842e02c4041a440135001900c141a694064581e140c1c8140c180015510101620000c550310b00c680b40103026000740c1c0d540c003c1d00801c8100c5000f800c00010031080f200f1403101d60403014003d850b0a8803800280d54034038600741125020300301174049880e03c0c14080401064540c280ca070050400d01d0040d081c1c005980150310402054074105604100c01040a0a0010581e80500000e029035010301110345607600c035980007800740003203550881892407010309051071940107481054481e201040760359018080716512114048101c4c0ca0300c20b4640d0350440c54001804060801c00e000700028841e640c56604a943e500c0c01d40b0811500c0c0d14001c0300d980098001140c0c02c03400780c2c0d0180440e280100000840c02440004080551704003800f220b040c00568500400403048142c5034561800851410003c1400e8007a21035400b003031003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 842379937 1250 842378687 842378731
    0x80601020d1d0906040905070e04201e0316060203031b040b1606140a0905070801020f0711150712020d1b0b090114010f050102010501120b16020a0b 65
    0x8030300300031401c1804580e0008900c00d00d000203010107404422900001d03940c07a0700002c0f030010b00500c1c40062444c07007848400f09410b80206402e910a0b485000c2e00026483c030078154040c001a808049504101c40e200711003a1a040c80c400b60395109009400c803990b042420560308400080b503070001d000b41c0c10010a000e40703201607101c0075140c0454102d11a162a1420401c01054031403031241c05030400002d80d00008000183d0084a0071483d488241150b82c1000020b8600a180041040780d49200307160001404d805e041c000c2d00c80d40d510703c0103002d040113a240c40c1c40040c00829039100b58400e5100300495040c6031007002030160f290242070100403041c05000c02038a000c403001103a80030b100050751101141116005121801c59200035041c5407620381880303160242280c100081001c00002001040707052503402d2910468609a00074005030741d9a542440c8507441d50000a88840d05440001e00c100e84e000e0b50076198145c00d48101e854510458a80080024045d220754940281400301d202c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 842381187 1250 842379937 842379943
    0x30522090f11041212030608060a1d0a1211121b0607080603030d09140d03020c011a0a0506130914040b010501050c1506040207060e0304050103180510020304111008060102 75
    0x3002c0a8450514907040c01c02c0c4074107103521080300c030003801c5980181c2000c5082c0d1082d04041b000302075400c00c80703a06040081e0304002406402200181c0303441c81701c0d2408a0600002440d211003508440700c030000441c41c1d90103d901c00d00c000d2403e00303144141e039114004c42200c0c400402040e8007480c20260000c07420300d00c290030200d026101f10100300d20003050089a60b00031044445e0519030b02400502507600b450110a2840c8005440f1184e010b090f40780c80f82140c051300146211101c4500811a0040c42160100ca200c8003550460f0461074aa9083c0301138105100180580c0480c4003001080a80c0ca656800c1641e1014078074080c2452004284030400c40e6114002d8007608003400d01a01b401c1c88110015a0f40341d180408400c001c12103004903070345803113682c1154003854002000b0301c035078060500c42c81c4d030301c2d4054491940080e151042e41110107861281c40c2d6a015484009000587c3c16a08040c0107504050400d41e00141d80d03c7c1a049655280001c48c2e03040e02c002d8403800440d05e441000642 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 842382437 1250 842381187 842381201
    0x12021b150105010e1503060f181602070f24030b03030a090e071707030c1407050120090a0909020a090204091e0509031210120311010c030204030807030522090f 70
    0x10207880e1072092000c51a45d08416030ba1710403021303207514442480d4900020700c800c110811b0700d1000800364080c0400d00b03a480d0348441c3c010030303550211803445503244000b40c8182d540d4400c200b54034140c4000e00c9200c08014190b0102c140180c540420366011800c0000d0844d070140603000b002c910100c204108561100c05a01d5220800f400e0280141800d200c1200003408010321040030943d494290198032801a0004440140d004030007589429941c03411078004c14841d4080d4a802220f5140134056580e200200c8801241c090712a003111403401000d00007604549904aa01030300f01100810301e01103610241000304180c100c007180720281005003c8080f0514040c1040d9941080100245c010700041250280301044180c1e58190b030f2126810a450b0000e500300070144140b8200c1d0b5400d0540c04640c8080c080c02282c000c122040e800c480580491140d80301c02803111005000100c003007070145010b030030301100c40018040c0c50400e0601400c00f4899a4200c1940c1c55600d81401661420f1842542 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 842383687 1250 842382437 842382439
    0x1020a0807030e0105040317042d020f0301052e1a04090b030c150703140c030301030b09070621020d0e07180b060d050402221b0302030712021b150105010e 68
    0x6a406d00391001891414080001e070303140d01400300800c0c104010081c0c1d40c84410700301404c5803000011502494003004900c44182d1060115840c5a5020b1406105aa0042060000d8076002c006456240604190fa140407030140d00710000c00001d8070307141c0001c204840703540c40714055503c9040c03c2603001140c1c0000b250318001d5103f20f0000b8416100c1d00c1d01604000c140b03254a80d02c0e1191444c0c01c40d00002500003d000f00c000200e0102e10588001002e1416284a0395044c5c0b0307140d482d0b0407000e907510b41600c20007000442c1401c2081c080783e006081060001d130280005031030810a82c1c5440259090140041c07882e0748401030811168070201781c15180b100807080240503e007a604002400c81c000c00e0162060039503240085011581ca20700503202420a400015107408030303000042c401400b601301c0883c04824070000c4010703c20700c82e2003124401c10683e00c4050580c0e140c4c681510007900400c11024600550b000c0011032008104505510880f130926810199030520300010503030140008a6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 842384937 1250 842383687 842383691
    0x30f0203072a0804030803010306110a05030606030601031103090d0e04060503030904020a02071205010e0d031b03050c041e15020c01360b09040c0206060a2601020a0807030e01 77
    0x4480350307540c080c90050040c1a00031210111402e00030a031504150b00700c0004250318000030700001013000f448080c5049034000d0204115007110300080b48105d22074016200300003841000000c00c0c600d040c0010390780048042c5000501854089001e052a500980d11031819a02c22016243d00380e41c0180e120070400300c282d4040c440540390802103940c9010b124145c3d481035401140749490103100300705035001400c0c0d5545004201905051103402000a0310403011103014a8014840d0300340603000d94100b280030040c40131562030b4168821001000050080b855500d420031000800c620907860708101c030105070308026403081c64840b40c4241010301e01106001d54004400307092172170782c0101c1d40008602010440c11034180d580c0d100c100c090300b08403240f07010204214a012172551071480107054505001c0d50104040c0490040a0b130341e6110443d4626480021010140509401403000d81c0d20100d001e104544041150002d4a0a90300200002c000052504041144a40c0d260055400c3c047c1030f0402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 842386187 1250 842384937 842384941
    0x41a18100e1e0310091704030c0603060801091e03031e06090b0d1a090705060a09051008090d03020c0a020604031b15050306060c1e06180102130303030b19060807030f0203 75
    0x4030fa250800010300707400280d075174070480d0140402c41009505582031700c95000d40c1c03583c40740f0700882c214500d80110800203251020105a00700c051080d100011303000084031082c5020031100c1c4042000001d407c80c20181c07a04441e40a006000343c01208100e000d1502041d03441c1013000302802c0304e08034144d140c410711070160183c1c00301d5452004885c012443c1c3c11130420907591600e0791443c2c900c040d48400e8104c1c000140c800250740d4820200300c155401102d030300340600c07001a01101d540c20184e071902c516800442803040014020b50040070b07202c0300401611511401500081c109070066881650302d0030359041941c0070300109116410242c911002501003201c140000141640802000c243c0100350000f2075000450040100380c81c038012188000c0c035a0503c0c0704285440b00015030b8102d02c0795400200009610b1018020f44a400444901d090100351442d00d0407000f400780c80607110781007070a045550140ca2100f0003002d002c0e150340d496408072030070050001411140e074540780036011441801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 842387437 1250 842386187 842386189
    0x3030301170c0a0603020c15221703010305060a060501030c120f1103010e090706020f030324031b010e0f2821170403020f3f0c06041a18100e1e 63
    0xb10070342c1e15803d40e040894101c9c02482c046140c0070714143c000042e018040000020804005000e92146d1a1a50203005084d82c0d007005409981d0140740040c0800c00c84511301503041099400070241300c441c5c43d0003040e00e03200030441110710fa00c2a008074070031003040810041c045000300106002040381e403004000c2c96a420000648a0201801210f0001e03082409404500700c0b180c020414864002e00742c403600c0c0c40e0000349408000140c4005404100d800d00550840d1a200c070182c0a1305030b005d86000c4445245210090b502c06004101014032106594042040011340c16001c6800072500c03104141c4680f10700300581040215584017a8a2004010610058035000c1040d910620161004070250200c004007105d80700034400c400c2a40080340301d0034050000984105507107401e000c02590500c040440a100f0719200d02e000d82607000220100f0300030401c2c0b10000600a4041100050180d11040c200041d421001c0b0711070340c000201e5188810807030b440c10740c84204500034148041c54040e81000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 842388687 1250 842387437 842387461
    0x6050408160614072603090c030f070b0d11130f1406040905180d1d0a031a0a020c12030a1d07050d0501230907060e03030301170c0a0603020c15 63
    0x102d10f211210808103d0390704100901038401003107602040580070ba58950390800710076400c103e682000307920802d0344114030785c100440c0080c80011864050714016003881c4650842d0343c04400c100c1411603403440387c41c0b10031002602a0101ea151126a02401132030400c0030000c20791103400c0107413103854209c65401c0e555216412a0122045001c000c40c0c2c035a950101400c0101240701c0c0c0b0601405420700300000305a10400c60000c03480c4807102c110800c004041800001c041a003c020005c0300d0144041039480008441c003503012040300c00243c60508985400c03420042c803031048a0200c00040184064003d00b8092000c04d041c450140f03540401040d004180d55880703922a2500420301e2a803114148071081d045250703640d41ca900c0780b80c110b00011412092032182150300d200c483c007628a011809510400d0000002a401401142140d003016281c400a070004100801c10344203440070102c007500c90154040044c1129200181c481d42c090304183e04121014240044520a8400b0482c0c03034501c1d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 842389937 1250 842388687 842388707
    0x71403032203022104050112050f22080d1b0e0108060f04060308030114181b030a0608010f050402040b030313090e01090506090c010e0405070507030804080d06060504081606 76
    0x625014a501d0315030409a061642d44080c100d00c3c44005048212850500380c000c1003214800e0742c072000072610401d20350044540030b490102d6a4070b10f500c00f0542084a00c0c802c00d41070550142d8810851415980c1d05145920003050000e0941e181d618400d2a100880c203600e040c0000c03404c08035081c1a8000c00204410001400c031031085a002c011507074a170310382c0d5212102666120640940d2544c45464148881102581c041e00c610340c07161240c200c150b110310405004401c02ca04c1c450511303403071281606903508002c0034004c10654441c40050410300034000e4030703540c002d2600f000030309080a0040c0016228280341c4240658020007100070820074030b501100490318120700008503007000f41011400b4000f0303042e02500314410042400125040401c01004400e4240c03201d0071050400014801034400440302e05000ca101802070b480864041c071501030717020340714401c081d00d008412031444085400f113401c2040019004241444815002c2080001ea0758110000b0b92403d490f060b40200070302da40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 842391187 1250 842389937 842389981
    0x60708070f17150a0602060f01060302071502180a03060c0e06041412030c010c080a05060901050609010c020109030b100e090313120c03020a17100504030e0f030c060d0207140303 78
    0x80700d000154421140c3c0c002001e216801000e20000320b54030507009603943d030305440d213003081880e49000103813282c068400c556415034001140260000d0400c4a140203411012034480b044c004c0301d0024040d580c50f040c00340701662107445c0003c1d80050a81000382940301040b490360050300d0802c412300c9a8450780c841b40500282c01c03030750704400b00700d207801c80c5003540a038403841c00d0079608125866182c80e4010506903c586074654040040781e9800d0208450340d00c0a104843d0450801c20003400da0b940305454028011740103041c01d0b4201683d959600100d074500b1103d1070610b07030858000f88511041184101d03003103010000114100b006c00034a510014401e48914000080000d02000801072804040340065400500b540d61039960343c414007200125070f00002089004034070344083c000740140714282c025501956010507819821040c040000b405080c080e074144101c0101c800c80d41d0b202c100601d2081e40e03600c400b607150940c520303000c40205958054050107804c18170410010b80700e4103480f402d601c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 842392437 1250 842391187 842391227
    0x70c032603160e0d030201201312140703030206060f04090506011202280f210201081b0304060c0906020d083d08070920210405060708070f 61
    0x42a900b040e140d011082000710b82040002d2211302c141750f01075104440c181c892103c00c1b00c55040100750341c10b80e4441e160f02a0719608c8010000d101c0c2d01ca12025881d5090700c100021040415060549031510082d0340c001c0b80141d000b08100207090900900450300042d082d103050080283c0c654a068031200c0502400c0c03101d0020b60700142c259541d4a00c0b0004403154003500c40017540c5038180b42e059210650240c191807515a2000140c480031140025020761401c2400c1002134045a00440d034581c030141c89400c4c20001d07400140035514401000b9070040c1c1c803035180010f100101c0b680283c461040c0741c1c07003042990007195203441d07026009a24558401d00581088614003c12409030b511500c4c0c007071528412028401d107130704920103100940c2c010f40d0810001c41c2c80041d51a082d00042e2081000200e060000b40540300c0840a080c402526601000003001e116491241c06080d0840c070b402c0f03606031042d42c00780c400d10680a400014140d0030400514080c20328031962200036200000803c0c3d00d010000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 842393687 1250 842392437 842392471
    0xf05070b0417120907080d261504021804050a180b0a06030b011409090f03090f030309040903200a03140c0705100306060216050307051014070c032603 66
    0x60100b904607620f9100c0c40c0641d05103401c1410000740e507040c00f03004800d6144030310f503c200c12003070140b9042200e070180d103030034480090150700072904140405062400c0c284012502e640f1241e55600250203136a00c040310110203d070300d1104020030b0307a44c05090707402e6042c03810b44024400c1907090072041a085d00122074000781d40324030552100415055001a02c50380300400042920384001c07400501040007207403084010348618076069150201056000d03a1980100310902c143c0c2001800400310392401401d583c00c01010001140585681c0708088000507102d039960100010003203001254040b584000b02581841a500600081041d04136150540c0d00481d6195013a90b04001c0e040c042d11020f011480d00141d220700c050041c01c07590080c4c1016000780e0b040241c0c001070b003403003e4044480085c001c0540a140005000828502040748010040c0440c4840c00f100350940040c43c00c81c4c400d1120a60b001d1070b40c00d02c0400c01248074000c91032400004070b0001500304040039281c0103203a911600b0b20003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 842394937 1250 842393687 842393723
    0x106051b060a020405030609010c02060712141317030f0613022a150405060106181a120a0209131107050f210309030a142104030f05070b04 61
    0x1184540301461180408118064001e60003520444906600f29030064035010001402d80701a450f5080040e804080080d41152003410303401d103031802c0401c00284140b99480480034100003102c07200140310455513135008000794803c1c0007020300b40c1194030710300750706280d07500c0b41d9404400360402d84200156080d1844500c40c541c11904041e20700700c0741c418449491000b045807524043c0c0072280038019000240481090007000511590f8050060403540c0e081501c20f45429641412555030082019404030306100c8200900103150a01c109094a0b214000501040428000c0004000d0750062201c2c1c800c0351074035810040c4000c00f480002c1030f41d0300c030707800140074600400501401510558070700c4034880e0300200310111840c076400c0e00e084069410718200d43e0144801ea82c2903900761310420044c10a0f602c1350f6101b0141901d02c0c0c500c04c1c5004585c00c0005580ca80c90440c078000300c071503202400f0030990400f20000d400c82d002d0426908180301a02c50040410700200042c0020784808109100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 842396187 1250 842394937 842394967
    0x325050a080112330e0a0f06050703021b0601150906080402010c0212010f1409010c020d0507020f0a08010c030b030d0c031101271a040b070c03090302030102030108150c040806010605 80
    0x705540c02c00c41408251690025080c2d491402481801c1080c40e003a0385040c2e005c800305621050503001450078030324001c0d035681c5200504008101c01c0405500784460350f84940c221950001d03442c9944001c1103694100402d0301c100b0b10a441c062002d0100440c1d080041e01d41018925a000342c09003030222040c5410f00101c0e01001c00d8214800300c41d40b0300130180c00f100c0b03059840000f0031350f2800195140c03596203c241500329040c9088140c0580e224407080c0003c03501c0381004181c094400b40071104429503900210f0305c0c0004039040001a65100c2c0d0403418016414400c109034058200d004102485503104090546880034401804002031010780e8110b01100350400c007a00c82e01ca940100400c0450074940e529040f1540b0103c03103080b1185414080048004501381c000c50300b28907500a107403255802510345c030004880c103c080c0230003d20008091780e000e00c0590b008104180240c005400b005001c110b61403801031420903007100901091040d6403000a001e07055406600313010f07964820000c40480 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 842397437 1250 842396187 842396213
    0x708031b060f39070c120b01031b0302181609050a0603020c01182303030601120e01092102120c0322030507230f030a1113020325050a080112 62
    0xf4a21902031002e44803544028014400701c1e0081c00007a5400703445030019800c50384c0001004e001c0d02503141c010b0002c900ea44282041214081942048480d030320b6000c2030400700000c0540074403620f000104003918154509040040700b045c90485800e078100390000308190102c0c01a04201580491400d40f0343d5025407016240400310025140214010b1808894452204003200140209840d103000c0c001400010369014400503141c20107041c40109480005004190400380030350740b158001008070380d030900002c9219a4803070301d4004014803600c0107032926501c1140e078200350b4000c1000c5008800e0110035503a00031056068041c8210b074000c0240d94100c2c9942000d041d42c02609000211480552180081e4003800d0740c10031079100030401001559840c81e115150117412031260100040c450400280382c0d4140241141d0440900361440320882e041150b151100300c001200745100c01102d200310000c4108545032003840c02c070501c0401032041e0310600c514080030350360540b03e03410440c05400c030710 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 842398687 1250 842397437 842397511
    0x140f060d3201060b070501111602040f18060b1002030c0c1306211101111504020103021303152d1a0909100506030714010c080403050708031b060f 64
    0x84100f60720f0300810b0103950b100c000304461640ca020061f4000f080c02205841d54034139103410800203c803082d001e100103400b030581c90f20b600c17550b0340803034a084541c80182d14a50034011940040c0d680000014840e81550340e6100000790b50007803011a1040c840015481c141031401d80e13080d040c50000040c40c8000d08081c0d0405201501c4403003400e41400c1031340d004005011b0103500d000c1201c0318004015a0702c1c0b0b049080142d59504030a0221800d520441c818540052061400514040d44e10100c03400300c4450381c008485a0704001450901400e45000f0751128546241c4100c1501c0c91142c0c40031f40d01900000d00d07441954540c00ca00f48a403009107690181e60801800340403442c03619500894948510302141c0c01c125140401140c540e081c0050300354103507880100904080341c00d1500548406c1c1e5050b0b421a54404200000700010f0801c0c001c4400400381c2500840c1c0328049245c0f03100c000c410360b4086180d1544902c04102e1034040040113550400c4c004003a0354208142200da080814451041c03e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 842399937 1250 842398687 842398691
    0x3040b070c08030a0f0315030308011710020301060c060609020426100f05060315010e01270c0c05061509061302120403020601150201060e0a0c05040306140f060d3201 73
    0x340e1405070084202c2103820803990b000c0003541311941c4d003003c1c0b80b287d5010181c0000c000b803006001030007100c10106004e1990000306d8481200d080325580590340240c000c0d500140c5034001c004100301280c05600050280540258100380c1452042a006001403002d441c0c1060001007034140a40140200d00070011413002c02d0228038885101000a01001e40b03d56005c0e10410301e035440c4c0e801c201080c05060714020314140c400c41e460070b03003003542859514100b4444150305004000001540303210b0018032142c0c0e034031050401c0107241816400d00c00001d1480305000303521007003000c12ba42c0f441000f99200d03100310380e02901c401c44001401d000340a00b020700140c1c000c0d070b40244014503400168182c101c4040003900004903000280407800c1e915a4480e0003690f9489501044002c0070b203410900c114406460100e0400781d07a626518243d80c15158103814118085092266801040001c654401400d4841740c800460b2907844081c2070710500070110709654801d9101d00c20b50130b01015622003a1040c030003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 842401187 1250 842399937 842399947
    0x40e0c030d360e0a050f0106020604030c080d1413050c0901030305160303020409141815040f02120313050324040b18031201210506150414150411040803040b070c0803 73
    0x4d143c00408081d9980007240104000000c2e0075440021000c0c442c03541540c60341128207840e070314401580c0211309c4200406489484070403070f014884840c40d11649040c1d04e1210000c01a00740242400c140781410340c040e00c0c02034014000309401030120390421901c2c900841100340c8a040c124020302403508801b500d10700b05010794600c0342036101494007509840c0580d25500c907505444554a0594000d400b0101d00c1c0100020003003111414011082c60000d0501c400b40e8102d254202d04503400384041c1030700b840c0315107418029803c08000040c080351703181d0f90005070441c01040c181c2b440d07030b40180000c0c188208800005c1d0354080d40300c1d40403802005841201c0e01c1d41c82c210fa00200b040001d0080c0b00c1c1c44004941c1c0003030080e44a00c24006020f030814042d100da40c64035900e100c9100200c40465420a840f6100400d04071030614001d8030400000c00c0703d21781d41e0080300800c000d6510600d01b81500040a003c2440404404002c44086030a0340b5003150352600c00c1d207054240300c04158445a614000410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 842402437 1250 842401187 842401201
    0x60f0303051903061404050c0f0f04030b1605040306051b0406032f0901050711130504050c090c040b0a030b041404021f020d0c050c040e0c030d360e 65
    0x2910344540d00c41c40140302c181c2509000c4040380e00c61701c01c0c2510300e0784110003040d290030954071103074122052511651600316440d1b02e82c00d80381d1080c0c121050380c4072b0001d0100140140d0700381d03840d0400320f90f5100d01030118132020000d04038000c034000034000c5660340010800b602c0e14101e0080142003070500c0d032a200c507030780d0070b01030010102c0c04a1100724030701c0c8050361440210114100042010026451400d1011781c00c011103103a0005c0e00c01301c800c0340981f444c000940d0f440c8441c106049a8000000c105407400340340c01030030074000080761070107410280309101404d210407082d90291800d201840b6101c048148045020b0008248220341103031511500080c00280c0da40b600b41702c5ca000b0381e9100001e184813445030040c1d03080a620200180c206a9002160900c030b207200c814850700800440e504c0100c0c0304002011140c443d159020035911040e580b240300d040c107110302c007030008a5092600d240e40d00c40807817040c8000240b44c01454264903200780c0f0400012610484054590306c1805015481c06507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 842403687 1250 842402437 842402447
    0x80d0518120a05070b1902031e093f0a03080a1e1e051308070803060f1906080a020c0a080a172e03330c0203071416060f0201060f0303 59
    0x62030591300e00001d2020711b800d00303000000b150000741d00b00101080c1544028a005400c1d00801c4c0c07000e60046009042008460144107aa03808038403188040352403202d403e03c8000040042c8d02000325940100364000c0c04281c000715803941c005081da10115000c0100342e00f5070100910101c1c0021450314002080c4004081c1845481c00c20050240400180d200c1904400e203100e0300b45801890300204101050008200402840d00b2940140108226008040000e42540440484000c0f0702114a03420022141d010301c6058201020740030840c44c084011021946801107a1009031049000054138070000b4405c004c0711440850704401142c050500d00310008000c100d980036045545100c100c00a40c4409501b1940c08503a80143d10080310b41456443d041007503e0401408111200b40060107010021401038649010f200c0d8040c0d55154402e190990300102c0b41500b1404640c40400108801c000d0901075805481301c0d420200070800d03040360100d01604207900600039220310200000109a005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 842404937 1250 842403687 842403697
    0x109031a360c0105070b04080a0302040f0801020706050106090b0a050c0c0a12050c01020102030709060c050a2a12080301030f0804080703230609030f0c0304050307030c080d0518120a05070b 83
    0x103242030310b12812042e80115000c0c00b800c0e001610345110710001c900000c0b0131400a05400781c82c0d0a000d030406584183ca000c0c210030302e42c0309181d45d9400190138001c02c207052050070b000d08114188507895074184900320925001d0402d2001c144800080d2424884c5000c01004e0300303050b002013003416030030340301d41800601c4d112040e400c440b203201e521900d02d41c0d580103009880c13240001c0d80e0380e007013803510b0203800319001111a00151014041c1601e07800100e6260350400c802c060749411640004408a48240880403c680c4222110f50042860500040c1e04404590449800c8550f40781500340300d00f03160740b4510950348801001e00c2410800010004181d03203500c20408282c200a149085880340e01d501c030750b030440340c184e40d43e00100040004181c0c054041c0c10b280d0211001c4030304048e150400300e4075005050b00309a030107490a031400c0050748020003a4002c4034201f460700a003008800900c80c02c0710000d50305c405101f600391420850641e00100800780701c1030740040031199a00d0342c90110740815804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 842406187 1250 842404937 842405041
    0x5182e09140105120c16030e0109052707140d0902040f05130b090a05030301080715020a1205090f0405070806010909110f070c0b04090209040b0109031a 67
    0x45180007581d4404031451100400040e1600d034540041411411288800201039803a0071000340401007a081c82d80380d00c0a0810b20907118455401a0440054604061940414031a0002c400c18401010a140391411a001c00d14964031254407105419540d540000122380c1c400c0a0100f1140783e440901c0c0c102541943c001e860030050f084030400030000792002101c0788060801002400d80000345403031111980f02d90b8080564605040326550726040d50300a1b03020000b00e0780100f200340008004007030010741580c0c83d8002840c000c3da1584c0e4198280c413511142100f404008120140186c0b18820f01c0185010020001c01051600d101c025107220b00c00d403419800907800c5200480e02000d24414070b040b04d500b044459040c58200c24604a195005100441d900401300c0710008004102c940a08058180b900c80543c075000b4600c18007049410f1054182d04100c840301003000854010081e000701d4400704514a0740555500354880c1e0030846030141072131648144901464074903141d1681000c1542 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 842407437 1250 842406187 842406197
    0x110c070e1b1602210613030201020d060906050a060f0207090f020d0203070203120c0c071404021605060f15130216050d18050607080a0f0903020d0309140d0305182e 72
    0x242e2280041d01034004101c080085e40910040783c41060a0010a81d030640300740300261a01a10384010001d65059600103401c50303440e24018042450a95401b1010381104d1429003281540900025982e01c02c0344030308001c65607100f01082850180da011174542a6900f4420343d640c1c280450020b5907a400103040d007000c03012120210ba54104400c04a03964402140d000b41156410079500c2c6408040c1c845d94554410307820080581d03c00241c00081000500903000f0b404d5614000008000c4610000d105a079074001c40e03110066695115024200030000342000161a46110a80848810403055014000d0300c165008500c90b42d80c44140803018518010721144100da4540500c4001e0059050080c0121010300c03003809120311400028000340110302d40315050131368030b40128003100720b0b02d40300340c00103101c40d501170141101d44d02d2003011410046d691041c920781e0700d45006040d40500114403d60358240c00c1c07141080d503a459842c071a00011000c2c0720b072160b07807104400c80040c00003182d1040490 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 842408687 1250 842407437 842407459
    0x31306020c0a0f051509100207080f0303131103100e0706090902070215090a2103080603060709091a060d3303061509021c110c070e1b1602 61
    0x2003402040b2000b215603140c80807010a041c80c040106881140616160445041c09840015aa1300303001c900782441c940c000e425503a0420380154140341e1000200603a6078000c20502c403070321310160070001d070380c6801229240c1d00b058900002030400182c0d4003040300b240c0c18a0380140b942d0300301050300300491307103a03881c0c07540c1099540c0c10080c107900400e080a94089000e00b201254034441d00c000789100724000305681c0031035884024600b24280b01c0400715051060400d200c808241e00461007541142c422801000c1d180b800502c0241000703090300842401a0f10b40783c3e6050300d2048080d0100f4503000c02003000d03848840310b000840c02050340b40f108400b48594103041d245038404500107552485c62220700800c581c1c0c03c4d43c5a0364094181111b074040b1902c11140c0c009101030141c40542082008071160702e0020035801c141c0c1090302e0340d0030b107140d50081d020401d1607181e0340c001682c00c1c00c0707452806540ea1070365509001c02c0c0320000000350580c1c4991002910b41584884000a000441e1007150840584 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 842409937 1250 842408687 842408689
    0x20105070e041a0402070c050d0b040201080109090503030601030c030219050304050706170406150b0414030606010f17090c0a06020618011107030e1914011d0102190f0203031306020c 80
    0x41e6483d1a5601101c001c0b03100f4082d00707400c0c2a002070140c90700550410400075940d078081682100000d03c180c0d1503200c42c0050100315a0b0048210b40105007084085c4002409525880e440e07200c050644d5041c155502c00c1080520700a4055604580041c560228006048cc101a226504c202c82c2160303e07010701000070030f2181c003a1148501c2602080854806943c0d5907603114010a1004810301003051006800150a504240141302804642c81071001c00c819176010f140c40e107003019000034188241d01c10003401d03941d4000c178030b80f15681101c800486ca44d141c2c40c0e42d160030700e01e410300c8460300183c80361008a0b0341c6400103030540c080c0348401c50844008840c7c8103042e088803c08004030014010030000e00d40032a2046443c006c1d4031030000c00003918901040d4510a0b01e07540e0b6800500181d0810b5881401903820080d00c1c60481e540c2d007101100300ca001c4000175140d01b0900c0000300c00301c040c4c2c0c5081080c0440303a4550300956a001c0c0889940c1c880402d6a260292041d2280d0f20062164580012003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 842411187 1250 842409937 842409941
    0x4020d020d0f02120c16052d06040b0c07080f0708070c240c060e06071101182315041b051f03020d09080d02090f06130e0c0d0903020105070e04 63
    0x4480c3c4c4d082c0e0051200e84450030b0340c865503441020b403212280d50800d00d01000c58000c1c00045800f103c000140f10f81201c88180800500c103800424403c203811001c00c0001040c200c886d246ea22000040d2415501e0f1850f01c0c2041e0f103130241c11400355504401003107280420221030014041d00e80685c0c0401c42c12503a038041d0040f81468014062504980162480d454038000d04c59540380d1031190f02c010886c560741f00c0319245441e000711340b60300000324580c01d207c00240c000e203c0c030110031745010401e403080000d580780c040140900d1800500d070042c10b800082c0301c040c0140f200c0c14034042030782c411a46605080c10040007000135040e400c20100071480e00000c080c903280c0401441000413201c1140d002e881000154029000140f84440c21502c030024000005d03601c900608502042d5040140c4490030030080c400716102030448140103d01c200001070907042c8550702c2c5021101c4034400e038041e070b50710690285e0f03d501880040c001c10ba4240032400c4100368040d04440d04c240655501c100481ca484410401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 842412437 1250 842411187 842411197
    0x100605060301060e0613090c080402130e12130e07080f0c07020d11040636021612181502101503030e0303040302091806060a0302150a0e04020d020d0f02 67
    0x800c01c0d11180300388905001000e000b80c81b10900175260020b90710103000043e60300e040400030000f0b2409040000314a8440c4500482d8500c030f09042209440945000340d544801150b03140182c10080b480b0141c58051b04007540240c0002403140c14107003000040500054420340e02c0041e900720040001d6000ea5564068a641640042203041a4074058454012402c094550242c0050b05c900700400d041100c112800718154180400f82c02d0741d08000070a200c03100703401151104503401001a480008041c0010009030354006545031508000e80740140c9801d034584025100300c2070f17007500004007203a51000240000026800341c62155415074007060445020250b11504190a440300303201007485004d122104400107002c480c41d0580740e80025a401d0001c0300c660700709035040891181500003d1045a41140041e074001442c28155400079201800c02d05c0d070420a03000c040303000b07006144508a079404404029102311f50324100c03070300350001941c8400035144c00c036810042917200b20005442290 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 842413687 1250 842412437 842412449
    0x40b0310080307150207050a020429092707050910050102060601020a171614030403050f0a05030a030216022d06040e0103022403010608010f080f1216080408100605060301 75
    0x2e0341c0f20004c0d184a100a400440050303905100c4e0341d0b00e040042e15980700740d84088940002090300a810078500c50304d1603840494007801003000d0001c0c0b0bd6882e09000c0f61030050110300000c23008205c151400107180c0001580195488003046e402c3c041c21404407032085007502c0081e82503d0003079a4440069030b9070304070208010050070031902882030201803c0003404240110101d051089103064940100d4045076003813851080d04000360030002c00004004c10017923800421b01401c1240e030152a100d480b4011006d07010700380740c0c00044400740e0341c281d1840c0c80c2507140c0c020100b62001c3c03035602c0300620014006040c00c0d602c00c405030081c0007a01e00b0509032400c07124005820b990903800c41d400d2103030082c840102055050301c03400c810604802d100d000b441c081c04d0303a41c0da541e43c150f240c080748004844490740700200c03980200c90607040040c804200c4903043c00d00020314650300c0c15402e81301d030101d0f40d14000140641d0004140071a0200c0d0108942e800c65410710010f0041a4446041040500c8284550 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 842414937 1250 842413687 842413703
    0x411190906140c2518151d0a09020a03140a050f0c0a05060c150a02120a05070c030c210201061a04060903060506060f0406210605010e091308040b0310080307 69
    0x109541d03e040400c090b91069031002400d2401d81d842c50002400e80c06509081c03560f903161b004d071100d103004401c8001d0040c045040c1080f4105640d014108007900094210b03482682c843c860b00055442c0d900020008590120080a21320b002c1340c0c1040c0c44040703000d411212402004041e5100c010700180c0c1c0c02a00d0300051803a00814500030801000360306c10308400c50700b8000c440c200d884000d00290010711a4501c05005a0368410075040c600f5540d10041c04501030f5441c0c001031000c03196001c0c120061959040c2080300c4100b605080005064842c00580404504a600c80170302c00c0364190400e0088403626035940881e000c400c07814800da40a8bc1c001c0c000010b10800080000ca91950009034200314040c040c24582950701100c0202680140c100c034011480a004403007030703000051300d0340380003c002c601d040000c1070500300001e045002e5642e16610038405080030810310302c0e20301c2d020624941d01200d0a80c0d5aa62224110a1600f080b40c1c008108098058000f41035031022044490b01d55001c506 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 842416187 1250 842414937 842414953
    0x30a0b0907030e121b010c110709091e060f1a120309150a090b0412030f03060e1302030309030105161707020303070c03020c0306011e230411190906140c 67
    0x1044070701d60090784001010104143c120011a0007e124103080559035560f0000b0400814115610b4407841c1e03440a02a245000c9149020800300030340140d01c400a40c02c510000ca03c20b0500e40301034000750740206505072414440860b6800c03464001c801c1002e0a82d483c0c0d4114505000c19034aa00540400700d40184078600c1c20301e40c0c84000c8000705810561418013080240c1c0f90300c8443e640d60811b03040110425899488035092681001d801748182504c0e01d0f09210326030070302d10800c03c81c240162500603482142d00000f800c40da4140144c13100c10001400130441440c1068002840419141c1601e01040103810781c40c059160810360380c4c1c1702d45416002146551240c0c0000c68940b0070081056045004540e50000b4a560a0050703500030014200103054050406032001c11807a429070184040f402001d000000440189040d003003a031004440000d00007640303440031a00c91007020240900d850b00c0a039070009013608160001c0c03e94656a07155039071a034400310b000d038061041d48a55041c0303030311140c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 842417437 1250 842416187 842416213
    0x90429040506030a1e14030c1b0d1a04060c022410090e010c0e0103140a02030601140706360f03050d0e01050613050105011b0611030a0b0907030e 64
    0x1c919000711001d0129980ca50f856119155204801d0328414811448a04c3d0030043c44aa11003108030071240c00d018500e0040280e14055071542c8690720710130b00d01c51004007680b551740d48400360000c09030001c9210a102000f0341c45151800720403102168003501c3c0603070800e00b20b440090101042e0b001255805800203010034504c00002d4005d09940705480345c5c00c0b0114206405000b1003102c10000c00010421580302c890280101e100010000c3c1054500203d20811030340d40000c0c190003401d0140700590740d842c0e41c801250001c0142c0240300c107417080051840204501c5502542038606422000b032441c404119844041e06032401c041394886401d07440c45030104030443d210144080c403c0c20031a02d0302c1d4200d10710000b555411004100165551000c10005003080400b00d010080d03400800c10642d818500060005203200c101c000c06030300c007444a20204080e41c0d00812030320040d500700340d0f00c0e0f14001e03c2d26800f2300004000d40380182800408a01114024090521141c0e8000c01510803409216 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 842418687 1250 842417437 842417441
    0x170106081002071e050705150a0f23091203070c18060e04060b03010b0a09230c040e090115090501051e1f0201060f0b19090503060604020918070509042904 68
    0xc07105417058012004000780564036005c81c1c2052044800155854601c1d605000e401c03549491400e030280003040c03100880f00700703019850010b000c840300c0c1c41c3c17034403000d08030701259110325404c8102c04944800100c40040c0400c480318102100d1038006a21a0076001d26002002c0d03d09502c5007141250502c00170400217200717900001c0c20440b0207400080c2c0500041c0000c1e0303031507180c5d40c00b403031400b5a2560042d5011040c103c0340b6010124903001c4121f28144400c01b08158401c6105041c6a403a855011490040f0b0a4115000035004c804480031015201d00b01c000c000c010a125842c80342050801d02a803d0981503d42210f52000804003242c0d000945051407850b40101444811556906030204680c2c1841e48248090f24143c42c10ba85c803002902840500341d1409134100301030100c1104100620b90340024080d5110030282c82c0980c40e020b4000210711107450196910410a10766000c1050b0b45902c04050100980119811320100640c11414a0020289020400241d0b039198071400181056 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 842419937 1250 842418687 842418743
    0x109170423150a12060312020d08090a0f03090807030809040609180809120111070201030e1506101205160207140d2a030b07081008030901140417010608100207 70
    0x64145104c202041c500c0d400e00301c2d14141c0084441080145040440e41e07810481401c100b44541482e48482c200207017010b54440c00716100400d540c1da020b41041c1011b101c0d144100080001c50308542c9900d0312842c014081f50400c4039290b006900e05100003950080601403082d0044c4040303807820012480b600d03904100d40c0048082c5400103103032100c2d00c0600100340b058801da50000513140f0703120a900c2c400101075074400e030324031000c07540034003215102020f25200064002400311450403c2d9180d0000665180d00c5116144410928040810140c000000310500007040f00d603003030f42c46854035010041c10540340c221000da00012001c2403800003403503043c000d6148070322011000b008500c0c540400c00c4082003a0300101c03800740c00d55051101d51908031107400d4019660840005280c0e0802c0301c1c82d81d49029148801c0d0400c1b00400f003802070b03803020100301c85c00342c0700c250b01e04e082c8012503c00c400d018150b148501620342c880c1140900043c3c00718400d441c0c12580c0b20b6681804001c200c031908082c2048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 842421187 1250 842419937 842419957
    0x5010303171e0a0b060d050604060b2a120a020d0809030a05270a06170c030106050a08060a0f12020316050f130e1e06070819020a02010917042315 64
    0x10344c032101c100d03d83c1c0f0031003e855040c60702c0e080845c1d180350040602041e51026800201c402c901071000300d61040802030000038481a60b20f51180c012900c40405141410460030404149000070300400f81c241d000c030302440003014a0320352070f035103441e10180030b552845800780f00400a041440303d42d42000d070011400b07502c0f40382441555180344c41d242c0012880707031440d071140c808908071100c045081a90403400307541c000d12001d02a410744d80761100c003411601c14828008200080980010202e0307682e2075a20015012102ca103400ba0b6840c0d028040e801e0050903416440b0384070346c208515004403c080d10303601342c1c1d0025119411035081202488894148130702140c17141c54403000b84601400d130408c088080301046030600342c2841404501c02e8100300300a4038001c00c1006c14010003040780060341c24940c550846900c0141da6008000c0d04034014125108010640d514800c885038207040580042d000f070390000c451407050381c5016102d40307505000c2d80900540080303007940c00b6110032424501400e80340d49 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 842422437 1250 842421187 842421191
    0x90a291c021f020102040e1605070320010903050a1b0c050108071413090c0e10050c1e010509151b13050301020318010b0409020607080c03040e07020105010303171e0a 73
    0xc41c160b0021030000000303051005030360109080003007130401c403030b1103400401036500c0440e04031b0701a41c010501d1040c124042d080c00703424149100000b04449030781c00110f200700e008108a1207a860010404c3c0d0154a0f12400641c80c500909006503092008904580d4400409030745a880c200040d10900c400425490500c01310364101242660000024981e0074000d0160b2075200f400c0803004402c03544079140c800204138001c0d05041d0951901e959514088134141882510385021702c242c1c601d0010000d00e1815400502c07240e4440840c415003005015070110001e03280c0c040700b45075031004118030803a50017072030f254003d00760200049080b0003030054035044100030b03058984402c0460b00703991050703030081038060052700300440d000c1003882200741c0104221024080383d8001d40000300b06006003d40549120000100604d102000f04101ca0007464200d040100515080202900030030092005801048540ca80801070038070000d40b0038441d004c884074276100740d0982c0341b0049610700b0003020503109907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 842423687 1250 842422437 842422459
    0x206150d020405060d08031e100303081f05060406020709050109050f18070e0412030e030306031b04020c060709090e010501062c060f1b0a021807030902090a291c02 72
    0x744040c002182300d0f5082c507003000180c05400354101a4580e00074071b00943c1c44461241030001a0344480388503040b440504030300d2910080c2043e0480048003a52010f40e01c040e0010b400039050390049546000c450740340b1000c000c3c50f03a0301d02004066070301c2190500079504032540043d0214000320101c00040038400221212281c130368414440074003043d5000d0303443c1e0041c01060881a68180107625010222030040e500b10700300b950100703645a489046045600b0b8100d998002c080d00c960341030312003e05a1104458071801c1503000075200390141d00910044a06001e40c81100c4072050103003078100d60407030303032a0811f04040c07409180c820800c103082040c0c40004a60307941c1440c0e55000180201e07101d207803a49540c44c1070000c1020b0301181c8031501c042c5070b900100308100c0940e0b5902851010300b07140000802c2641c1d1651000c41c010004410001c0d8414403410502440d40031980c4141c046c000005840c40c04e078071420f0b8905903644040040b044d4032042d6800c14215200000769140e40e441c1c4013070301c164500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 842424937 1250 842423687 842423693
    0x112050c1302040b12090105060a0f120312110301060215010b03130501180302011e0501080303011e080a050106060e061206300a031b2604090903020606010206150d020405060d 77
    0x95000b1704032100120310904c10711820920a202c1c0d10342004007100d4914003d4a0a0314030401a2002c0c401c2c4110f12507032003080e90a042c0192000c12440c0c80c00e0a040002410400040600740c01c280101c4005103e030070031242034131a1098000b4143e4100b60000740c03d540c0c50f410700c0d8040007200c81044800d0f549401560303400c0d188901ca00141d0074407036000401e0301001c000400e13000102c0389641c1c0082505140040200180100c00c07a030642c1c810001006e00010005010540240c85600c00700c118070840703640505100c030641c00b12050307455603030303409840c6481102000f8660246800003030f800d0051901050b0310317203007580081c056a100d4010800c00300c20550095064002c1320502c0365480c1e003004000c0b000300f55103c0e849050b441220224100300c1031040c0c442c01d030034103590b504516080604086580e4044c5c00c4e0020b0b2401050000c2e4207020b808550301e00251581d0007912403502610641c0003142281c0303912603d99000002c05481c50481400c29000c00c00a00009040726400c440c0b44003000d408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 842426187 1250 842424937 842424959
    0xc060c030a06080f01061406070f0f23030409061505090d111003020c0c0427260a080a0506010512061804050a0b0a090c0e15040c170112050c130204 65
    0x9245500000784441c54011f02403003000c030850840b40305041c10051100061308514400411a4110f0458a00c1220034a0240c2c0304480038071200154503a418100c228050000000300305036802c2c21310a02142e61344000502404010400e40e8000c21303000d005140742c504040c94540b00b51405500165288080310020030a91071004e414000001d400250351086a5810804074030980c00c00d8030108040c0c0321849403940c5125620b00c5403908100b05803180030501c10a460640700703500030929070b807455074002c1050150551240503528040342e914400100b205080340304044c440c0d20103031a1a0b14150f0f12001c000c0c04000020029907200c501c64599200e442042c2c02820320a61044006124806250030310300c110200040c0050889403c04201034009003480103103604031110440c85040c0b9407190a8401200d0640c2000d0a03001450b0080c42c840d01984810100700465803810900c0340780e6243c900288060b100d95002502c00e502c040d03044009420b0203420915094108080182410348034604950 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 842427437 1250 842426187 842426203
    0x11401021219020c120303272e05043c031701090207020d0b041509080315330c10020d1a0a06081906030506010305060c0c060c030a0608 60
    0x341080c0609001e00b1540c1c0400450103103410440702c1032095562003107a42d40da4403000b0040000c03910a40d103004007010740c003030641580d00001c0b41501ca0380740782c42000464000b810f0009011000102c070020680c84002e1203518015908800d1050b8032200003514140d0a8410f8a2202d65801001d46103404003614015442c00107442581d66107414081c544a042c003114040e00410a030754030410600005a484404003041c09500182440b201e55690408a66949005035415000c0741041c0d005002c02417450021362040c0d0341d00b0038030b04d56490745405200e4501f82012036500c01e41124907100548185035410009960112940a490449130341e0711141040c0d100c1030500d280d560041100402d1032401d02495405081850780a040345481000203101000c0350304c01c610070700172030b10302143c8514405050044030740c46048040c1f00103580c0b407800d642e9600c8240302c03d903850701580300425110b4468800700c50705070800750010a050b0f2144a007840740c0b5030003e00095070541d6904000103100c1c80902c012a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 842428687 1250 842427437 842427457
    0x10c11010507020a1502070806090c0411090303030f040c0b0901020c060d09021908061b0d09020109090e071409040309091109040603050607141606090c03081b011a01080114010212 79
    0x60b4012080001910380380b060303004800723983c00040400c0703900040040c41c151585e00403100899094100d01841071984036900b001500b50200100300a1107002d031048040c002c070b01c915180e0302100d64070035014245001d21170f004c134016049810301c14003d15024003d404a03000000b4005015903907a40058030f61801000d400c0c061080880b82002000c0c0d0a03c10107502150b1b0103031030a41d0703010f05295080d1030b00c05c230710001d070305036950380f03441010b59110b40b440070040c1508120412a001c65003450326581e800703500c909240884030001181090a0681d401c41c0120307415166800340c1c5080075400300141c00383c02c10020b0301010602035007100da9607502400d00103502035005400b15041414004058020110307051070030803c1080003020769400201042075107a00040b00044540061401300300422103a031002e461807074041290712418140c1000301c1c0d99010218000c2042480680c07071180c24408400035203000c109100010403000362003103900185608144160b9541c05211180c0c040b050b00324000c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 842429937 1250 842428687 842428709
    0x9030c0604031806090302100503150919060b25060b1306060806030c06180a05130b03070e040f0b06011101052403030f182704061802010c11010507020a 67
    0x4914010115000034003034040380c50178192040c215004a0b600442481c3c0c040304100700040040d054510710200364801640003840e82c559410500042c6003c011101e10407000c403484e102d0000b4500c112a003c036115200c020030704074992042c99030a2a101e00704a503007a07460139240e03914010315a03030344007800080401c0c602c40051501d04100008241c00c03001403e103030081d400a000d1105035614401603c04124a16184420144403003000c1803003420350b680100c2c1c01c43c00a1010040b204ca41d0f41212070b01078010b800f00c4100e01c3d03660000030351080d0182c030050040b44c20080e104020502202c10154041010304040c246030300403200c3e403800c484044a02400c0c0e000b000c48401d004451805424250041c110002c60401c00d040640c9a1184100c0e01d002400804180c04c1c1203183d1110100003407240703010300c2c2620076440301004261041808079070440c0c9140c038004860702c0c5a22000e055030328a40d01a03442c0340500341c06035034118840c1d2486541a051260620001005a98580001c8041c200300155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 842431187 1250 842429937 842429957
    0x3060509011406130e030309030301080f0706050a03092f150c1c021e0f07120f0209151e030d030b011d0409080316020c010206010b04050909030c060403 67
    0x40142150806041205140d0509039000380000c80c0e030001c00d402c4102258a03540e400388800d000402803821038415690f0f80404020043e0501000c07011350f04940e502001d86541c8000401d8030394407400d050058034082942071061404060bc01d07803252038850f109940101c408400540101000c2c403080345180c0030188120b182c1070302414909040a828144190034034200000c80b02117913100c00d0500380d00c0d50526410b85800c40d0091007000028080c0301d110030014001980000c8140e00c4542e9400e0310f10f034074844c2c0100050000780710a4070515a40d0051a100c180c11842c1c2d003008440700020744441e0f011400e03551601100d0b9140c4513002d0710080c0120006d83d00e4440b02c4203150a00000d041c5040a01d880c04c061440980d03002901400400201c55114610082907030008005101940001e40644804000c000d00c01301804001d0305602c2240d02210703e0202000c004a9448109014000107010148010007190800c1c410054015a082064a003000c66a0070642d03d00182244c050b0005503502031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 842432437 1250 842431187 842431193
    0x11401021203060604050910091103010801110405060f03091c0c0507120c030b070c06020406030506032a0d032a02090a180809030a050d090618140409021306060903 72
    0x1401c1d0800c0700346114a41145086000121a07008a104540c0140300c04000182e00e5001c806982002e000e0089042012440027441c1c1c2c495504240a810005c0d03103001119440d4102c4c0c2c2041c1c500325540103041a2401100f80d010700c10f0385d00b015040c10140d20420f00f80709402020020013540004040e50703100c012034240d0904d23610701040c6500c1030800088100e500804501101a56000d40e600000b42c05110707190188211038000c40c4840144c090341c40450f0100d050b41d41a08510300445084044403810a10a0140095600d40d501c0d0840500d00c0c036400500c1a0074034030b1000e00c0c100c0c0203081100d0b00d40b040b44403041a105501c1c0006401c071450f0503c070000c41c41d1040300181c04c20511041008003141c0030440e80d0301d600c0c4040000e130000d20003203070b0740b92599820010301000645c071109407050101c0010015041080ca402084085942e482681120004201845c41110841d101c204841c80b20203007030000400b0380000030390f00400b14820543c04e207540341c0168802800940e0f0340002052a6007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 842433687 1250 842432437 842432443
    0x60901060605040f061b1b0906171c0522050103270201140c0f0703120c0309050f060c03030f01140114030a0e0712050328140d021201140102 62
    0x904803800b446030522007803002207030403020380054410a080c80785070305442c0b9007400703811040200002d014107070b020302c02ca801c1c42d5403009442c00c54088020500a1540f20344c051f0f202c0d0030600e81c044009600000010b00006c0f25003a008148180500300f03030740f901c5444074000b81e80c500d0100100364117645001c0d0070011942d15108000341446c0d401c1103a130706010030000380445002c581d100a4100410b8410a02421000300221540010407070b0071603410408852001c0d03154000707480141d41c1c0d61100c85002c9006800350540003081641543c8207640300c4d0806040192803014000140c1d00030380188040c4100c00070400c011070082c0c4a002d0086000d42c584010000140c48400c1d070300c1e0410114005003507000c804001075a81240b82d001c004079016040d0700303040b072030000991710030354400003580f007403000f402000f10050000000d01c000c0a03130b10740340340c130a0340882a14041d0203030006002c08040c0d017200f0350501c0c05000d014111903000351070040c00104840422800303800c605501c140400180c3c24545e010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 842434937 1250 842433687 842433689
    0x2a0d111302043303021e0d090b060f0604090509280c090c080109020306030a08040902070c0506040f05060711041a090a15171002070f0b0a020403170714070806090106 73
    0x8407000c440050403840f000d620524a0f079181414503030041034589041c1040c01e80c00c0d0080d5580364203144c42c1d0500d5290000074011518094414006480201d6401d040100f559503016001070942c41c68145011400d1005240042070016103010780c42301c5500311201c0000341d014a9050042c0848505601d042c00d00e000405030740902c0d0700d0340c50007580d000c5440d04000098110b079410740005840e6a5203002181c1843d84c0c444009060300c80c00036001c10384021540c0508142806210780300d4542d51988280103483c8683e00038240e00c030390780c3c01040005190800003008414403541503115040b0502003c5029200e4080c807140d4011004600303c5103908003146210f0744015410028400b4048280030003801d1074290207520603462618640e81001c110800c881c0511f00740c03030300c170841d5900c4203410b0800b500c84148504552030b8040b800441e51200d451300039030302985d41140c0000f681407003507034200007507a010303000885806814180c103242000d07040c050440100400701c081e0000d0314064200ba0b08403209 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 842436187 1250 842434937 842434979
    0x906020f0a080106110607082e090b030c090406020313060c0e09061c14030408100606020f030a020d050315030a03030c0216030b04020d1b0306020405032a0d11130204 73
    0xc003204440013140041c1d1b031500302615003094265a11403003d036004512510782c0400e00c02c000400d81e500755460140e558405c844070b001040054207900020951120f111319000c0750b0010188010801156030303580151380100c0314100d080031074845035039020181e13540319054101040c8007032012511800c180c03010301d5000e01c1c00c07140144007800028450034000036806001e0080051300d100503005010030000c40b0054410482100c801407488105000035140130b001d1400103005880440704461800016585001c013150050103065a101d4000c0f2840d80008080c0075102d0300e09141003101c0d403402e02032101d002c3d000c1c0d900412080314074140685803096a62806201c109210010004180d85200d181d400ca0350450f0540003080550901020000d5400d0343da990216400c0c000004004107070340203208a800a8090f501c0c000100a01c1e9851080b85812615000075558404122031a01c0800d036109a44200c4e403c5e0420704130000416900260042d02c3d10f0650390002c0d09100500880a08012441c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 842437437 1250 842436187 842436197
    0x7061101060e13060f02090d260a090e0a02040b0a020c18070c1b030203072912040f020103060305030f0409060f06170403091e33050a030906020f0a080106 68
    0x51645007061400d0f101c22024000595602030745100a020740c0444000c1c006c000c2c40120204030508021002003210030001c4602c000c040011000e401c0207000351040c8041588804020900d480b0405a9510740244031420b002d908000102e442c40e010400307444090516401032110030b22100070300c0303e4988860509840c04810008010450344c0c425203080465034880d09294008805a5094100c240036070030007035050240234004920b52102000c00341c44045100202e4444004540c51000306114000890301e803542203a0004011802c503d00c80000c80784185030004005540c2c1d1500340c210781082d070800318074610000d42000180c0d1a402400e0250403014070390121a8034262016154241c0c801811410103c1c42e0005404d15000d003010100521a12000040c00584002c6400b1101e0071390107100d0f944000b641c0f0100788042c14024aa02000c070318102c6480310003a02c0410740b8180c11541d5840201074440342414000b841c14000740219001d1314028507103803091800f005d4400c2c2c80c16008902000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 842438687 1250 842437437 842437441
    0x2040f0602010c0c11060703112b050304020108060f271b090a140a030501090303020702120a02010801170f0304031a0105150f030703060302060a11060919110f0307061101060e 77
    0x44030345c0d802d008040800c89400da0303500300d24135017521f070091003000440b501d0003004a041841000551102a100711080f00c000340320030509000e64242c0001d0380c019002488180002c1d00f01d0504000c0c510020030000c06000202c40a011003602c03010400c001d41904109107014064900042d40c4d400409014a120a82c1403003190b10100701000038910481d03036455429600745000e034644a141c500030310f4210000740f26040e602e040c0a4003940c0811401c81c040c5445024a00b10300b00b01144c58020340703605030744045041e407900c0580340e03020380414501c3c10180580070403c18116410001000254820300040c1005504484034030044c8205030b0181e8018004003135140303501e2400c002196245000348001503125203a42400318000d00302a00003e401440010322044060f41001100620709421030485e507050b66003c0076541c4079081d10780401302c004c401048240004070400c61140907060b018112110b1101c114002a1400101c0d03404a0045607480b00036405c2e640742030191501824490804400358 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 842439937 1250 842438687 842438693
    0x230714060604061406070303020c07060522050d1103010204270e0102030c0712050d020d090516060e01120e0d08010e070806100e010e1207080601081212100302030102040f0602010c0c 80
    0x901202c1314852080300c001a2060030107005e9419601070591620403508001c0d00c5100140181e44189440c170480300724000d6a5580340100c0300108259100035145118070040e036075403c0c1e843d000c00030103903906540900c8041f44a89814264018680e40e0034841040c600d8585440d1088401903e01c0382d8660b4010400c20101b203011604a64030a60f110f815900c285107070b484111000d020360848041400d0000030f601040e240d06400042515004d0019100c0c0b0002000d1071040080e81031044c3c0001c00c84040403000d196000c2e80c040e070a2201800004680e821156060900308800c0c01e002c0310206807408014003601c545000c000740c1c010910304004140703003810000101d5041d0041c0d0341501b00300d0003001c583d40c0f99104801040c46140080d10700d00904045c0c1a6541e202ca0040c020012644030750400000d01e20b100041040383c1c0c1c051204214584404d140009038500301c01405003d0000c100d01e030000058030244000c2c40184050440300d4107035802c01e40e0003070039211a48191803c009014070b0cc0004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 842441187 1250 842439937 842439959
    0x2806091d060612010609021c18030e040b0a0308040e1806010f0b0a020f0a03021b0604120609140604150c02030903070b0a11010f050708070c0503040623071406060406 73
    0x2082d811940c100190107860782190140240303420108440740040303000c8503004200c03500d001c41034140c0c240600c0280d0110750441017000030507030040c0002d0309401c51100c0e05e04280d4003101016402900c4103060f991a5120700405600c1640b0100422480004100c9a52600100100d4401142010b4180d5524001301840f8583ca68022000301160006042481500801c450300082c400305065440c100c509080107034682c3c0280c41c0900c03507220514181c0543e8900f14048809a031006400c0a180f8816500e0302070050400c800104ca1083d8142000021210100300c4548030714402c6003071030026210003c1c05000d4a110b0720901d4195481440399903401d41e00400c0031b6050f1031030100ca403500c0e070445101c1201c030031030134110004265190503100d0214044980007240300d003010b0348610380d850b241d4004c103c541c0007469402401941040c481400030798441d24100b14080500d54120050303490010f00600c840d44403400464040c1e044010b68404040140041d940c04002144d08001451510141081c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 842442437 1250 842441187 842441191
    0x801060509040902040903020a02090c1e18090109090215040b12060321030f0c09150a140c0f07061b0b0405150c0315100c08032806091d06 61
    0x40c01404210720701d250b15580e1105010b241c00410500545615060180d100d011040b02030f401788110380001a51042d022045460581083d20a00c0700031001d500c000c4850b8002c2c0410f9480040c08131204a2a9074402c03d886003e815612800501c0030384c40d1040250400303100e55200b0100707030180010403080740540103440c2020800c1c0d1b9291001d5560000003414888e80420208603d40d8624903d031075000a0700c0075512940008030440c400c4c0d2074800400100307014445840d5805412107948041e12500c14001d0300e6030340040d0a10803140c05c0603a160a0407a000910504803a0b44a40c00703001031100c082108200800e014280702c040a544003681844031447d450000e068842a0800b0508021003040440c3c01040c401100208500f03040812000941c400d5810f619888400d01c0c43e141315150211075403440c01110745861401d0001c5075505d2074580c00060440354540e082c81440c640101c040190840303500b494000014100e1b040c00c001c0c0040b5500002c4005202007469507903c801000010115 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 842443687 1250 842442437 842442449
    0xf13090b011b0b040501090b0703091401050603071505090d0602220501050409022a0f2509050c07020d080a090608060a06050304050f03070f03091d0a02030a0b041b0e0306070801 78
    0xc40c89030b43c0c45c10183c1c050302c94008000c10020b08901085440f80d8150722200f181e6119442007155011501411801e0361804c2d104c8950640188030708021403911400f041c025500e15041a50409d0803140000700341c1c00e40700b80c066402680016030303480d03807103d11443c042c2c442204244064400341001c00007401f6001c2c3d4058002034540c0000d0104040344403000707004070031581d424414420240c0d552019216054440115017910821b01000c0c0d400031451407501c42c580104590300d0881d490003480c040a07101c050070000507641e0811031310025072171723000d014000d0078095a1120760f039103081d00e401000301caa00d6020f80c04102d400340c2800050b5441c40040011161103103807440c2c59840b641031603420003090000c040024480000e8107020030041d498054101802504c2c0c201ea15595442000386003980704002c10a02494240050341031595907003d1074015608100000301c0000343c0340810101c0329080d041d13019542c2d0019000f80c4582d03110700340c80c1d421300f0107034040c11550808480180100006000300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 842444937 1250 842443687 842443703
    0x5181005060a022a03190503120a0b06070b040c0609051305101e05010215070f111e0705100c0206070312020d09150b03010527030f13090b011b 63
    0x1040c2c003580300b009074151083c629800c098640c00d80035408903d680700342c01d00b14002e001e000303850849502103d0840c1c0030395410070301451815020305034540034034200912400c1c202e0ba4a540c0504151a60750103440350a1041148042605040c10155401401d42e40038200300020720b00c081c8401e132100913a09080003a0100041044c1d00d9020303000400d40300e66040310940c80000b0b000d170508110319a0928003100c0b000e07000d42d204040103035a8580703080c0c0d04680c6100425101c0500d00c2c02181700382828404801d14200382d42c4541d0381c01c105841c105143c1079000c081eaa0201c4014083d500cbc0036084510013080f5424189508038403540800c5050003282400b50078490414070a11001000d0303011102c451401c0c001c20003178200d0303500d0828a030381c0368000700c40f0559150185c3c203012401c051190a0090560001d800b00f454054084801c80141d01c0e180c04c081341c041489030521501d13410029280c003000c0d02400d0301d112400d12110348102c8050f500c0950400c03039980c510042051044500b2486190400a6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 842446043 1106 842444937 842444947
    0x110f032116051b0f0904110d050f070302090c03040506040b0907210b060406050a0918080301060903050f0d3609051f0b090919060803040518100506 65
    0x3417074000712507a000c84c0101d0108880e80042c2c2c20000c00111740070015545031800c20541001f50201d580c01107405004500c1e04d4610a540110103c22460540c0341c82d0711000c0e6150300141c4080c100c41101004180c030400f040c85404003400300101d81803624803021600c2410307030030b551030240e0b86002c45401013650740ca003d0207160201c42000f4030b01c101c058108a660401040c07452034002c850361602007218000344a440c060b60003009161540d01c43c0034a581041303030800c0d500d04c43c503581d1500112090103045801131211541e070701010b0810036501030a480d514280c03041c21082200d0300b00310010001541032480d00403512030241e0078582003007034820030b01e13805044051303000384818103c007800760b40043d040c02124594800d0340c7d0141110103882c2541c003801204c800d0740000c42903400c005800c1c015400c0890110300e400c0a812a84482868511901000070006014481c03166000041e = true := by decide +kernel

theorem cover : BRFrame.Cov 842266187 842446043 := by
  have h0 := BRFrame.cov_init 842266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 842266187 ≤ n) (h2 : n < 842446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
