-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3465
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:44:20.41841+00:00
-- url     : https://prove2.me/submissions/b945429e-6a39-4676-b70e-f4a4179a3a47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 623021582 ≤ n < 623201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 623022832 1250 623021582 623021603
    0x50609030a0b01080a110102011e0b0d02152802030415050c010c111006050105090607170c060103020405280c02030d0213090c0801051c030e0d030e01120e0c0d 70
    0x341c07500081000d00703038407940c2c040e4445d001d070700c04109818010300e5080c0340034002089501000400d2510540b40c1130300340342e10540d4a45142c8543c1e035034201c2c100d100580140030314519070380f00706010107698801000450400301c480141620034503045030050f607540440e406941002c0c5080c8191a6031100328000c141800014040450854024403a10045544079074458801122a04e90705081060305403045441c2c0e41088002d2041d80d800200b2152480e82c240c0c1c00303564a900030704288843c1492845101c2440c600041d071200c0305400080e00034117070390085804000303e44541c012490301b9002504440c8854040c501404003107001580101092905801030700c0c6059800359810b07089a00c18402c2c2c2140c1402400140310880c0d5a210b607004925250030003281c1941071100040d00491400d402d01a001c070040700020801d8800e02d4001d40d0890040c02200109a00b8580a401c480c0f0042c095030000d222200c03681c0700b1404500810151941c0c1c000a041e6940d07038a41405601e140104044c1ca002880 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 623024082 1250 623022832 623022853
    0xf160213050112080d140c13150c0f02030307050706080a0c05091804030c170d0501080f21090402030c04060809060610030c0203070b040b010f0b040e070e0f030a0309080d0c0c05060903 81
    0xd040f00300f0f220310b907d05105a0ba46047d14220004c100160b08003140e00131940c07241c00360b003d4110350380000784d54100628010148045c8000307440c520071040b005119014510f03000401c00d03040b040b8140500c843c00c0080c000210701d05022185801010b4a072a8408451a50440c64411008000e40c0042c003900d4405500b80094458805600c2201500c0b52034031000600340200c58030500c0b6007805000588081c00703480389a0581c050b9075040f4108540e0503e0000c003003d9401ca40f0302012184001d2026009545900c0c1440000d04550806e1250b50045007604000481c02d0802040c1c1c144249002485000c02c45000142100245048000c40080d884100300d54004201120042e51045105200c101c240d0f6050819400c403600407940186c6c000c0340180300c203101403007891a1071503202c056441c11030f034414021000540041c000103031b6a50140102c0c460035003030640c40703054502914840c001300c031200d4a9080b0110790b03404500300040c0031005000301c24003085c5814401055607a2004088400c60300b80d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 623025332 1250 623024082 623024111
    0x70c23060126070305250807060306060e0d02151b03181c0510050c0d0e0703110109050a0b070221010507120501061b030201020f160213050112080d 65
    0x900380c1066403120085510002144980c0c100c0a0709805540041c0a0031895513685e55a02c0c030710940254504000000722544c00c402110a07000146040001c07a030701182da4800107802001180120f0001400c04040301d046418042c5003245125030141900d1102c05000384890025044943c0100f0703040e0480d0b214052010040016003403a26491041031070034888901000f411244803030b40c03441c9803050203042070040b4002140200103142004030108099460142110f43e17481540d00e0844824540300108560f5200003d4034010b0303a22840c0c11003c50304484005417413520b400e1141d9588500c00c0142400425100409411002e2026105514025502c10360240801c0162a1554031360344d01c0040080c2d050744100824040039001d80100410350601200820407041c0400c103c03081e688032200c5a0406100354100c0700d4000d4000d04503a180c200c07251000c030003500814400c0c3d20811003042c02445a8219200700750488080404402d07103040c40c0da8a00880d81c03c0140d10101c0c0656440080b1f14805 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 623026582 1250 623025332 623025343
    0x20a0902040303030f051b0315031504080a0e01030b150c0a06090b0406060b090904021c08040f17010e0303040215040312121514011413060503010f0905070c23 70
    0x502c01d1300c0110781c9608060440040310002420811141d01010018004201701d10840f90013400f05480c1148892080c1c0c0801c0c40d100d1902080c00c40c081c1100708000a01951780050100c0081c150350390791407240d500004406030755109500c0c6a21210800000e6044080c107002046007006501c10b80b01c5890860f10742034111880da64060f01d4aa8000003003108200091040728007130002c0440450904950740c020483d820f8006200a0207960211510200c2c00061010449075680c85010180d9994031416041c0c60030005d80326102c1103259500015900c1d01d018003c03880c01b9249440114256683c1d03408016604018900d820030501c020030000c008100011003000824246803107440050000100c507408641684940b558500205407052207041c441e4170402d11130001c02d02c0c00b900084080051144507105410300a0305c007122007000014200d40040c040e42c100c510710090f44074820350781d0300e150b410fa940449808000815990456001440702c00e410b0905c1440c0690144611164201d05440d02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 623027832 1250 623026582 623026589
    0x2100b0109060350190504060b0d06020c010c0e0619090314070510080f0403030506031212010303020d0206040305090904170c01140c1809070c0f0b04050105250c020a090204 76
    0xc075901c00300d9102c80360320400e1403661600400400520344010b1404002d2185d28007001d1194a9001140c10300c0110703003010030b0b155002080741d2480051b52800718000d51280a04108a5090a08800c2030a000c1e041c040c49903000500002d00d4000a45845422441d107480b4404c1442150b000100210341702d518442e140502e0752004103080d80c240001c002c0320b110443c00d46003c00000c50700304580390311201c5003160090790500b4003003501c6d10f450300040d042004606203200c50780000f050008081c005107242c1c6049074002d4080d118090f40403e0101d0701c44c54204c0e4041c0c00305404020441440c1001d02030550300c00c5c010001414040c0d5901010186948103003401d000c035070f44031070480c9884041c4070722658200e42e42c110080d1420a0305c1c10035518007651000ca841c0f082030740390001a203060140e9480c121040d03000003142034044841c600303140007036010350301a9080c3d86000d00050000c1e03c00c07103400500311820829800c00d441d910500f2038010f038420794200d811680d071010001314680c0c3e40c0041c001a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 623029082 1250 623027832 623027921
    0x2d1005160c08060a050a0f180b22060504140a200f06040305010e070510020c090c0c010c020a120903021f182711041206020c061602100b01090603 64
    0x586c14105d440c030040d00c4401e40003070042403800080d004402903841c51a41c0150b403000f41720b48507554610141c2c0c003200320741c0144082c0c0e00003801c151040003520f6000a124520510411056194003050310759030701c903080310041082003400c1c900e081c00700c601e441c040c9407041c0007040794405540610108072140c005030320071500c5a440b100700350301100c01400080068182620b0700b60b06030240100096454000c0c40b07445016040d4980810340c00c4d825036040710300c0364031520000d100c0051200c10007076503100070003429101800c80b408042c4040d8820b00c8201b044030b4004110280290b42c3c0800460042d210032404014001c4550701c200708811000c1d5080c0c0241907012051600e01c8200302ca16000750401843d0a0509180a00c1c4004031101841520151028a49200c501c0d00643c85d01c40024415100908403a226010420849854000b9500715070720650382a502040144d8050300c040e02e105917011800301c3c1845009021440c420340c08440300301c0d01001d4029110941d2446d1b45407807001c00c00d03d44d80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 623030332 1250 623029082 623029091
    0xf0c08090c0f090a020d181a01090519020f0c06010f180203040c0e0c04092408031201030204020901121401051f0c1b052d1005160c08060a 61
    0x85405040c0810072511405680315281c065058002903031120b030040a4110407039010070030045102081e401070a802100320714170140d0040504040504200c001d060703d4074581e840300081001d9000e401000d002c0e00149000d11400407810704140080d41050b8140d0403030003401c0c000028030b0307503040080310700078001070320240b110905003114000360000c004a1007940074010800c0c400004c9410381c0040c00c440ea1440203011988840b06440f429129951004d4035050400030300d8095035900140c0b000c01c0031010096101c0e01e681c0c4400c5142c8a009a20030607030342c800802c004202508080d001042800c2c01450400d0500c10603040400407210030400e40b11007401498010300040c01c0600000845008001d05078060100d01c1000030800c05d0020801028900c3c04e03900042c008446825502c0644001025080e402111000c0300c1032960b0540207400b03075003502c41b0441d07000c0e080c224840221400180d07101031800003188600010007949950440700d003c2408400140310707100380000e50003020785207400300d13 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 623031582 1250 623030332 623030341
    0x2a130f060504150e0403020f0d020c0f0409050307150b12030403060c09080703080a140d05060a090216060510030506250206070f030c0311030a1d0607140c010f0c08 72
    0x400300c03452900014010340c6400c82051005015110000c00c4031404034142d84070782c0d40c03480d0490130200c1441000101c0e00c0b9903210000c4054010503d0500d0140036130f2601d011910303603001c00003540c6403900050b095410400464002c604444140824560008000715400d4018001311340851460b40d0b02c801c4580020805108222032406846880130716450b101a2981c10290550b440b141c0a01c80105807050000c0c140010030b0044052403140c0700071111860f110380c2c4030b0b0100400344c0700c12a500c0e482800050f1010a00801e14401d9031407440321161035541d40303102d0741c1d00d6400910000d88030b03030350f154200c0350700000140040000030701c181281c000c032610b940761903405166040102c205103002e640085041165060340f0054060140c0664038001c038802c01c5540b01540104110030600ca684100002000840156078010440c402801b4130a02c1e680004042d181e03403101c0003a01d400740092181402c0105404030000234001000c84040002005142d800108044032042031044000c140c010b001c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 623032832 1250 623031582 623031611
    0x302070c0905040b010506070611030406050f16020303011806231c020d1104090f05030405120102040b1605030c0102070c170f1e190503031b0c2a13 65
    0x40d0010148440103000c541055135132201c0c6944140181ea000305c0010408006100b40c50700a4248450f0200c0001d640703041070b0500b00050941210003e0000f400000480c0d40300c03240d900e4810306074030268061400d5900b41107110105a458030a10f2030010b886000200307507915614188200c0400b80104007022044070b0080c040240960108410b0f580081c0c141e020142c1c5854410030310380740d44010401240581c910004005058403a0301030240c000d038002d4401000b400100504c04d07035800f218031840c031205c035150060070f0344194000e05645070800c1c07000c0f0410403d0060307026601481202503e08194104100a08a0708150000d85180403c98020401403583c86075047c007105201014002d4140b0607107103595520b040398402080d880303c1040354104c808060140e481010f0b03055070150750501c02800d0096681e0401e44070b801200e12468035640020300800116808140c000000c1e084d0703d400d1703504502c03224015242016100381c44c200791141d95559941080c11020410314006108403120740745 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 623034082 1250 623032832 623032853
    0x50a02040501080c0a09090c03020720090606130e04021f03020915030403020d1103090301061202032407110705130c0806060a230c0105100617040201120209041b030207 74
    0x440000c540401c441700e4101c0d4400d1083d02651405a00070070503248882040b00248610320000c3e2882c0800440e1480640070324117a01c5040b80110390700310440e00e612040040d01c2c0f04004a01c03542130001c0c0810012403004c440e469a22500080400ca000707900c1e51081c0d11400d170091103080000c0d90010b2041042e18050080c42c060800c20141682549895500a5510405910504c00f44100f1458001000c00304200319140c2220140c024002d6903075a03840b08a2050321104124800c0c01001401c0d038440e52004212100c880c01071300300048035140d17401d081d105000c0e60340c81d244144c040c0c104040b44640f52038a440790340381c1e0303001000202e0303d2034404028401000500858821801002003a42e160361181e00204005415207028641919018200342588114074030b06c0059400d020400101d030310b00c1a000e00481e40d0366222081c0405a02c010b00e0340008040318001e000c207011564a188074040756020344001c040241000404e0001141a484211907002d40c00b800a1740010b9240c0030405031446 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 623035332 1250 623034082 623034091
    0x220f050907030c0e0f13020a0b0a02010c0806040509060105090a060305060c041806050f04020f07050607210c020303130201020f070807080f0c0a0e041b0b04060f0f0e12070801050a0204050108 84
    0x410000b90420076002d170754155001c0d02d404001034940e6280340556448140000041604a000c01d6507075110b4500a07000c1c0c003880405501041c1070800040807428103004052142c078888002c2e01040e800c21080040400c40504041c82440c1d603001c4c0400002c204110981c010b108480d01c450f100c52910340d2031071084580740c0c04a8031990402004000c2e0361216218100b143c0012500540c683e011145810610701914102030715511074141800f80c41508448a031441e201026024040c0c088d400300070006582c2d804120500580c410000620480f100b00c0000c0f000030720501c140d401c0000c8003509186442030700e80000c10f0359044a00c003040aa40b040220b01c03120b0300c1540240c4214411500003415940c45d074840c12841008c5240064100401c1c5010b954520b6400c524104120383c0725009100c031504070340070b0381c004200085240705030a07000300020b1810704896601c0d03411421104082c001c000d0f0381035006030028828820081007101081c0607683c450703000c0850050302c851902c800100104005032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 623036582 1250 623035332 623035349
    0x204030b160e09130c1806060c0b0601030b0d0206030f07110a0503040e090c03070305010c030b06030c1c0b030118060c0c03140a02030f1605060703050105220f050907030c 75
    0x490034000c650804042482d6910440b80514150303507100c0351000101c40c8083c001c00860040002142c554021542118901510340d010041241c4948068406030100309014107030b14424800140c0340e40c030179008404004800341c40c05104116941c040741301038005a03206072208801000300311030f465100c545d00c6259080c602c0104070f081c1d42a12926240d20503030090081840140c000a014903070204007620182c8005000c030742d9031070b0792400c083c1c0c000d00c6c00e002c2c2140001c1c281007002000d4942074040e24000c131030b030b41e0485240042021a40c840000c1000107240350b240c17503445a80f00c80d6420b214a18140c1408540c0d4a044546407400d142200e858440100c184a103000340e1001183d402041c028011411204c0c3d203668050440d010791450044110442d40758600060320900740003480d8680a000b0701c2030045a000d130301e581c00103405803002401200d41080c012442c6548102130410510140c0981c1200091080f004007803040666108513a2081c5c0c981c007000301001080b4985044200520f001c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 623037832 1250 623036582 623036611
    0x6040e07050a0519050a1502061006080c090103090c091a030118081806040909050609060103210525030f02010515220e0709110c030910050c060a0204030b 68
    0x800007038030703142d40e401550b0199804281c412280300e6100c41981c080e00c402029503001e1660303801101c85001080d850f40005000e41e10203d6031900400211206444c2942c449107910784d5107508044154001161003810961200d00180100d186020070502418590a0210b006104441c18002c03000f01041d045029a140c014000300024a040c1c015040e298030030441d507654036031500c800041240b03140b0069840302c0005800107070001103038401980d2a220380181c9401e80e42d0000c000340c84400074800070300040d44c444804540c01441c80c508162400090502500300583c050400e21240400070052001a846030031140516800060110400000d40b00078410f41c600301d060b400c181110002101d0081d0314081c5151142401303c01001001404000c0c1003101680009155507101d03c64800e008056241610002b4810842c604446a511000c0001d620b844043c900380b09402c00303005204d00030001e003400b080c40016000d00c82e69006810031030b0050f88071825070818068a150142031050001c156 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 623039082 1250 623037832 623037839
    0x16240b01090b09012105011404051f030204150e01120b09061e04060e0f060a0c020c030a0b090705060706091b24021c02010912030e030315040204031a06040e07 70
    0x200302121030f408028030f0617160201403000c101d0240c18001d8100c90046042000124441800c10400c8454107401c860a10454a420864034802c1820058407615406e0009040c400360415030060702d13030280d40b8882e02d030b01107070313510b400307545040c0e082e04551140944103a10708140311000c0907007a003100710500034100300d050030310b000e1f40070071322032040d020409040000103800d210013580040200b11081050721000030205640a844070011208645000d2030103070b02055080c80001c40c03034031224001e402010341c46c0c1c1030b440d04100340c00010001d12651060036004205900c4042c0a0400e07a0b1140d07a011410169924203081102000740101d00714004018042000000500d02a21a401402e03120461000f5441c0f00302e0401003074110205d090310341595400141d40d030540c49103020790f00401d1040c9100000c24030807815104442c100011070303401840403501d5401070450000e0311503001440140350990302d5445507a8080404150002c40003250200885400c0c58014428503400c90006400304909 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 623040332 1250 623039082 623039099
    0x31b16051c1422091d070801060602030f07020f10050c0d050712120f060b040e130201080412020705030a140609151302010903020909010c02190302060c16240b0109 72
    0xf0380c50469440c80740032107032003a11410300440c400641811501400220312a149502c00004000004c5480748245240007490308010b00c68201614050b6024601d410a8082da41c29160807080d02a64400002d400b120034950700c201d03008501105903202d05488410024803a8109103020b060070043c02390401040d00011a90f02000320400440d00f4591f0000f074080c880000101244040d048403246080c1e408210b42c0500700203001250b01005800c4a10751381e0340c100090304055504001c1c08101c4420100d00014031500b082c0600c100144103e40400303660303c0001c2e00d04410850282c440340b81f6480101d06001c002d000180d8000e0a0704008c10b502c840c01030700038030103d600412514901400d05520021a88030309a000000d41e0000c007a144035042800d04170b802008403402880162280d001e030b0108200800b40f01802ea03d07015006030034507a894018a503c654060b8030580f0103d001c107600c01c0b0008540e0b10003402a000351580040603c1101c111a000b00ca1045c5095814007801031002c002202 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 623041582 1250 623040332 623040337
    0x6090115050c061f120206120702030c03030a020703260106030c020f010603050f010621030509060d020a0e030f12030105100e09011203120b06031b16051c14 69
    0x102402080c038911240c4900865a5019a00c031060707081c007485003406081d250340404541c2e944401120300e044665140e049142e485a4404000e400080911051050300c6801c2c10f03103035000130540140d03444c20900c00d140b141175a100b240e1825080e0380c081801820b00d50b001c0e940030390315800200940566200b2a00741c640700f00c0d05200344020507496180c8101c00c2ca20a00507040307000300420003880700307507120301e0b0450301e69005c43c81000c050740c40c000c0300185141700e00307481503010f540c07120034900707e800c85890445e8a54803d140c0e841c1c01c4241001b1030412100c03140f00608180701c6564803601d44c0b07880e80b400c16060943d81c0d900850795034400e01e034040e0070300d800c80110381c1162021031760204060305881c0160b0703200c4036a0005a0780104c0e468000902c102981c0c4003689580d00c80d0392403010881a401c030800c00c0300d00c07009680c0d81008051000625800b0001d6041c4c03946800303130501c0d500b4405018840000d9140f0305034100c48a4110035000c5562070886102c0c91a219024104400c001c81c00000c090609d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 623042832 1250 623041582 623041589
    0x10f050901081e1204030309030501051513020703170112060b010e0307120203070503030406201b041d030c0d0e06191404031709030c03010c0801260a1b0e060901 71
    0x10310551202000d0100300302c440f20840d1584c4841c2e0710b0340d6480c14060a4030b0418401a01d481d400c240000c6c842c0710f469083c03600441402401d40124a40f8072044100079045050704605100c0c80c04d46009040303e0015004e4020306400041c04249007443c9003003425600ca44030210306010340c002ca1442c9681d070101d902010354000e414484841181d60000900e002e485900050305400009004921107074013040114400c0b4540203003000c42c1880d0480b41e555245082c140811120304040380301c62b1441c1c550004400d14181425400003c2840700c04c860450340041a20300c01c0d80d00c04543c159005812031802880b42a003210703a9030500c0b03c00705001c03003070701c084030304540410640c150485600000e20303050f01c003d10b800100341000d50b001d410030381c1500d84c400c0102038820b00c101c5070010107a14050140d0800403069039551400c41c1d2a018003103000c07954103544c05840c0c1c3c180181440c90300d90200f003020761450280368491011040d81203440b10a91304c0e908000c449140d170100300708141c5c0b11540c505046 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 623044082 1250 623042832 623042863
    0xf010b060f0c01060e0a0b030601080a120807020a14011b0e0d020405090f0a0b0f0c130b1305090c040501110a050604120e100f0908151f0e0c03010f05090108 69
    0x82c2c2a48a4140d401410160800014980705105112290b455580040b00c60031090301161116600c420089542c0d681c43d440090881d1781e00c3d082c4426452199680d60382154031401102c4580b816543c501c0f1090981c0150340310140e640340603003c900360303024012102c0303c417443c01c01c12003c50503000816040140030754041d00494a8001081c00d0110070856090400440800d4500b1030380b85151004200b14241c503021079003a90388011440c1c1034821011039441002d04110318580c149005542400d54210580e03409900034400c4001545840b0081e4042c802e0030790614469486081c50009000380c1d03002c0300c54010035404600040700241000031440c0d08550040c81c2c8050381419088210340840c100803403d81c100600001400341280c0080d0030032a441f51945070704821640328030000f030341c0d00c00c0f02e0300c00780c0410f4000300070815400300000b0944d00c0410101e400d480940c0c03180100c251802040c0e6001c2c0745010000010402d04007450b00c010003401086076841e40c00d51600070815034590b42d60480c0c4070b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 623045332 1250 623044082 623044087
    0x2220b270408070206070f0203060105060f190e0301140a050a09022815121b02120306040e1c0e040908040504021b010c03150f12080a27080f010b060f 66
    0x28030001c0c40c2603e0b001903004191550b641e00a103090118590400d42c03c80c0248a582c0010030680f80900c103841443c000485294103103042504c03000c4103020102c1d0010280003688d044282180c5080c0a45d015106451540c20050300382000e1400440c2c030020300e2094218540360700b41c401a0f071194900000400541038012241007a00c0c100c440303290f4641c1c800200007000000010703040b41c0100160285043c1c1400801c5a03d000141c42c03484400790500c0080107030000324034080c3c0344c482080615002480036100044106041a10914003a00403d0015149041811a5480c20b900614800003920107032070900c029443c40d5a841d00a00483c007406119075000b180348010040707810980301401030700c800248507a0480810141c01403c14000e0340c13070350005400c00401c8845a40b070140702154910000c4565a034883c0c0c66112080d040f0280307400403c16007080918080d0781e4030f9a240c20a00348aa03460708000c2c60141110b00d0a2405012402540d04008e1503d02135a00c217810f9803030021100381d03881c0c1e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 623046582 1250 623045332 623045341
    0xc2407050f1305040f061e030c0b071b0e010f060525020d02030a06062102060d022809091a0a0314030c01090b060909060114040b0d02220b27 62
    0x440340c00ea507800050304546000e855070b00c124200d03040001100c51010806846460743d003105e00b07c0041c5030001500c4001a100d0411030f51a20740c00916001d40220402c4078280310341c058901c8040741550100703c0020084005000941d01c0c1040a4005c2030f2500341145465000280a04900b010361030b980d4500c40115545020364494007400070000c0e90041c01d0b54441d070020701d800030007026503020b81780300c0c0d041c2441011100c46600100c40c02082e0000d000380d013008512081000a940180e02c455070350000180c0c1c0000c0f5607282010540c071541d66403102213605082541482c22661613030000c0440103800c01694040c0c1e140c0b003044105694011043d820b0251682d85158034521070701503603280c2e03036183c0340407401403010041c0b066008103012988002140c403071003080c640d291000c0c06139500700e5455203a8103e080c0750560049032a00005000250018119000501208a83d160401d814000140a070400040c80d02ca04484014200c4074050021600c070b150b00701140205000c62040102840406c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 623047832 1250 623046582 623046607
    0x61e0311070210020d0f0906090504092603010504151514041806030c060c02060a05030a18060207021003060b0a120e010203040c0e0c16021908030c2407050f 69
    0x15140180c0103050f00c0710440209000942d0b030946600c2c19800159580b022a2000d48070350340c8101152280d0341d490101300c0c20312007000010981c0103800c6aa8004068002440c000e6a003602c540307034036010303840d50346a41c5414244425900c24025084a50680711001d02601e11014400c1e00910020b1a00c0710001010050316a41071049401c2544200405110750010b4510341e0060815030788a0301284044503a1108150703601014040001d51280090118040e054455400b0356442480c02c41d010400c0500c07181e2813100150b07124408e4031840c0d0005a402c045d810700c2c841c28101445c06142c10001580350a0030296503000d2100c2c5441040124600602040d020307421882c902508180215900d08003440c007100c02500d41d00c05c01c0801d5800b200000c60009849040da52035180c00c0d00c1c05011039245508008002c51400440c40790201d9240001c0740b82c8000304041c2007000707072800052084e12041300404002894040d160445031118030104180c40707034001e041c1c50205586060054031030f503138541c60303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 623049082 1250 623047832 623047837
    0xf090103080d0e010f09020a0503031e030717070305220c05040f090501050c070201020607031104060c062003060a0b4e0f0f04030e090604060504020c07050307061e0311 74
    0x201d104a40c00e110541352034004640c0701b0038a003072080f28813990455a400505481c1d01501440f00381d014049007140b441d0101d00d40046501444a20700481c100480712044110004191119000a980c40e810401010403904400c459035412010660301c41340740c0da41c0c0c0d51400b40d142c01003d000e261074440d0125410070030340003031540356480002031000b407030401c001c3d185a07008404141d0051041c400828201400303031292000044a050f0706503e030504089043d100301106410484456995240504480e554085810b440310350f0313104281d549081c808104a03100340c554000d400c4041c010046401d1042504000e5412140550030401d01011310300d503c44000050800e0700745902400f41700d082040300450820a225000c032004400c0280c079034030121103488904540080c081000d40d000743c522841c00700402c1c5c0d03001c1001840418900d4480c0c010a060b80c000302408201a40008024000c0b450300780030245c060410351030301c034130040c40802d41040ba019186501800780341d0348032000c05a01c03100408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 623050332 1250 623049082 623049101
    0x6270a020907050a0e03100c031407090e061807080103060c1106010e0a09140a020901061d040f020c011a0405010503010c1d060d020f070c0512070e0921180f090103080d 74
    0x150740c0c1f60030403501c524028013941c002c43d00c0020700d810240b03001d903c6200320170340c0100c40a50b01d10138140c2c2040d0001c00d2078103001e0900c951000103520b01040b03281c07040c0303000c0e4440c2c0c0c0b480d0b0340c0361800e525615004090300c8008400e1021f000701600207510201c400101941104c407092104c107490388a039044400140080d181c00b511a1707409000d050750b600400683c50904910940c0c400c61280c0c2e0f250f808603a0341c01c1d22085c0c80030212400001021500d040d8100c0c4241c00d0f0341a01c0149400d11091101d400c480450103502090b611004046240d45000d203c3d4a0040006800034403103d138461340e00a0a0039010120101c9a82c8001c5d074600168803101c06585441d00c00700c50466617502c4d5420315003800d40204e2000c4800f801c80420100e0366052050500c6500c1590b203008001d080c1c240211240d054000400143e22803186480003800c0201283c4140340c0788007036504181e51048050000d440b241449003000340100840310400c035039500c4211500d41140c1d00316100c00d80311a018071420f006404d1811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 623051582 1250 623050332 623050339
    0x914070b030411060415030515100c05160b07150902040501060e090603011b0e0409050304060309140703120e061b1f05060315090f06270a020907050a0e 67
    0x1040464a20085001507000c2c500582d040c1008814100030040070744100d000320180c3d000d900741c0f1040002d000360080c40e000400380781a003035249050340101d00424610010030f00080c905c02d10401c180b14003413000440c1e1111480d44c11520038101708031387c44035100d03290004101c0180c442403140061041d40c004040241c0c020300038040e5580d0341c04003c0c02c0b0001000b00c07a214858140106145140502c10100c140c140709650035800b214a07070060b10100b0b840c040d41d80d0019100d00e0108005102817000b48045d0005440025125003682040701d00c2d12580020400700383d1120342c0a00c0072a0b40b6030040c0801c04014070b0610010421300c4045010b9010312038100002121000c02a401300002240480004515601c00c00703d00c0e1911007100d090300c5007501d1040c2c141e000311403405044854402003a41c000c289004030b0303000400080301c491034800200c5940039100601000c404490180d40d9640c0300e0b1000c4c0c030000781501c005c0e9400107021580007070100070078458001100f0000030300448040400b4100203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 623052832 1250 623051582 623051593
    0x51e0c0c0f0303010f080615040506030703020a08161d0f0a0e0f0109030201110909061c0807060504020a0b0a0f120e070f0305070e1015020c04020307020a0b0604060b09040914 77
    0x500e100782c1e882e0001c1c028120140130105001c20a40300010f009440b926071070010b0401e030381c07a03030003800010310019204503058094500c000c00580c81d120421001010300c60001e2106a041d2840801000701c40e07080354070040d8112403901ca17548545c400342e5401464952400740d5641b9618180310003855040c901845074001cbc1e4031041003c9006522a001d298000d40081c000c0d9420034150f40d0f07042c4a07000b0b85039840503a07640420041e040664640c120760111840f501c50b54a01030311b6076011900690070803030b803681c0ca490130001141440c40001000f0041c900e0114240a0b800704003a244070200c60220701003182000c021a10480650410b2121025890944980d252100d40d03029584c0c2c00740c0403c2c0c803d4803449000007000341424810500c034015007090f01e09803500341040c03e066800161021030840c4150005011a540c651005602131651a001080f20b00d030300d460700c5200301c40000c110754811403400b0702c02c00c43c880d42ca504840c0b03140c1c1c04032000a81151035181000c3d000000480c00c104d039200e02c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 623054082 1250 623052832 623052853
    0x3060e031c0c020d050c01090b010b0c070b04030f0f0309171b0607030e0607260304030e04052401120204030b010509010b0f0901120b0301050f1504051e0c0c 69
    0x300080c107207124603505040107000008454029995a10351100c01a8881c50b410f5148070301c0f41c8040c1c603c9005031000405e08070070a485506800b5000c0c3c104100f084400a1001c4480404010b201d009011032031031603042903c2c68403851803c4040d00e00181003550b05c40148010503108220101c0580340000701d0001e444015629566030b402d0144c01c0010314044800001034038500a0142c0d8281c55040e6a159051031140040c446250030101c011141c00c5040048806541c56015002150181048000c0c0c1c4a03c0c09050080c11000d18a50542c02a49880140321049c68400030005503130320018403114610120308012206007510003100c0000c58800310303000c01000f56180140d030403184121030507036650340c96541040700780c85501505032400d001004070384025402040310122500c0e40200000c0c1c20440303003021900303541044504440c26010081006884038100e0f100351081c44041d00c0410440c5013001c4242d103181004c00010200d0411180000c0c1045000821604e1060112003030b600900720 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 623055332 1250 623054082 623054111
    0x9060f04081c27020d06090320100f050f01030b0c1b010902090702031903180f03020f16030803040809120f011a010c03050d0905100e030d1113090e01060306 69
    0x554000020100004074160080001e25003d9116466001400a41c1c0c4080941c1c4030001050f1401c011418880d80b0707203c000917108982d00e800078901500e4040c10400e006403c14504551410310805036640c500300600c00c002c4520340750281541c1d880103a604941c0c60b0744c00801c40c07a02480f9030039000143e6803c0441030300c0c0419000070300c4682c8284c035038082070f88401e00140e07200d0084082d160300340201120100103892207a00100b0003d40702e00c240302144080c9888405d0400b61080c800d03405640b01400c207181c040c00400c10aa2040400d915561519003140d0304c0e8006803101420181c405080031460000d1983c40151120040d8580c404071402400050300c0640a400c007108507203509080e50107031755400c0d402022000c00d400c0e03066841c540b51004505600f0020b0980e06400d85481c45450300301d441e03d103054030030120440c14403401140c4400f11000500b00391849205130382c4000314240440700c86401840c031214143c80800c080840e442040300d07031207030042c1016400900810b052000039408003a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 623056582 1250 623055332 623055341
    0x30c1009050c0a082a0904060e0c0303090a0608100e0117060a022a07050909150604020906040e0a0209030312060f03070305071206020c061510020609060f04081c 71
    0x30700c0341c015140841490410022030714480e2050060369004541502003a9644544041c240103460b42c841038402d0050010850f000000c4074110b4604c0c1e564800c6044068080103805070307000e0100c0085252482a5000c01c0c1060324500c21072007440703a44c60100300c512141c40c0c03488008d00003082c0302c1d90035980c0d50408008102403c01c0c07002d80b41d0080002081001e4040e008854502101c008520a8001c03454103e68241220000742d403803a004960340400c06a031140c012078001e50550000306243c85034500307200c1c00010060074507440745104000440040c2c0b10003098a04485200343d6101d415511440604040d100e0040c070643e15020016012600300703616410a070090005507000c0f1504c00020061641d40c5860380000307400c507407000c1e07001c0119040040c00d040f1000e2040001605000b42c100320b10746001025a03140704540144080c4d01c600342014a04520807841c80d100504d01414030b80c81d41c0d9143d00c8003801207201d03c0700000004042c04604002c0b200c4141004420790f07402850141c6400081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 623057832 1250 623056582 623056601
    0x702070e010603050c09060c030d0e0d030e06090a030f021609090c05040203040c0e06010c0204090b061203070c05100302360f01050f0703090e04111801120f020102030c10 75
    0x2000e004004900d00d4442e100b4184118100d42110786001d50300810800590000c840e0000d41d44010404030620320414012414442c540700d00070000c4072184030004d01600c54103025089241d000404200702880300040c1c190100f6010300b4035405210040034100e041c1441140c2d812284416800c1c00285c000d0a81d012407a102c5c080e0800a420540314000c10081e4401a00c0160907080114801e2224203602105550030080505200c0031008903a4081000d07107400b9502900c900d280101082282e0411120792198580c0b80302c0a07500d05030040c3d5130407804203058052580640b008d8455000b041d40641d044a10500505640150040c82c40c01d0200301d080441c1c011400700c1160381904002410820008000100f05850b0303542000030506140300142c00101c820340c1003040c2004000352443e01404100c0c0110b0180360398448843c81d81e010300c406640401000c80c0e550170240d00410801550300c50785500329911100a000002c2e0600040b880c6001d40e20041a050240001001614a0640c04406103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 623059082 1250 623057832 623057849
    0x3050304060f1b2d05010e0f060c04030b06060d022a0f0705010c151103150109050a1205070b0a051308032b110f0a0e0a060905061b06070207 62
    0x60844003007103070302807002c0151841e03c1040d00c07410b200007001e00d0b112650240c3c01e9115007075070a0b0205840a60040e8511044e56241d5513606001154002401514950b02e40e4000400301070030108140d141c40e00c100d11000e44102103510108a090362004116244155019403d54888011a01c500710003024444003205e00c011018005020070808175032400e180440401820720280b8082c015103108140403402c85100d072903510040c810f902c051148a024408550a8a440303281c140c1400034100c00d064074150502c04040c10811070f0750313550030003041541e07900503454101c011030385855450038134143c00400c1460408111025815448400f51820f441c0c4e40307000300c1109030f51f407100903103a114080f1403a05090310b60414210b03111100c46e000502c3d441c1c00000203082040d02107981c42c150030070b0b28140c150100000d0501c5032140d000440d01e0092600300e480c0c1540f20314044014151250921402d030089801152400d41000c6038008420855031507800d580300751901c410003d45400f00e03070207030020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 623060332 1250 623059082 623059097
    0x111f0f020a0213020c0f0f0708070902070206040911091002010e070906080705090601021006080d0905040e1f021b060403030501061803170f1204050105070323041a010305030406 78
    0xa51440000d41050090700506078030303032901070f0901060180d407011403c0442ca1140354148100c18500300800d0070b0707015511000d031206504001490f402d11900342d1090300c0160050107000c3c00351b40d03400101ca044580c6540c0005004d480045030002d80d00410300e805910041244c07170b05000d5901034009845210103201035490040d22000600212041800f5012050344090030900032801e00c00f40703071500480140110740714020013280240648100d504010900e4200d0b20401e092150441200005010111000d01080005040103a0703546c5c0350f0b18140c2043c0460400070101c91210350704846154200d5610300e102c12a10f03950b1566035030303401d850850009141c0070000903602d208107580c03000d1204107104407a80740d146464080c5001064610702c02065410400e0f00d0602a03140000c020382e00150700a0041032809003881801c58200078600014103050140c801c2030b4070b000b40c000101100200c1c04e6204246c4440c18540700706403c5141c2c02c222088001300100c02e000002000c0c1086492130ba807200c2c0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 623061582 1250 623060332 623060357
    0x20708030904020319020d05250804060e0a080406030b09070e131d030a03050618010f0b0a1202040608040203010b01050313060f18030c050f0114190b0913020906030a021c111f 77
    0x21041024010740700018140342b01140014000d508120b484490b070300c089600c084104d80740c011403a441940200c011a45c2e800307510916062015502e035006605d424042d200210b40e4001c102c201c9040f56007181c0d07a69555160186021404006020300b150200403aa107418110401034020101601e034039104840010700c160f0280310490507281031344d21030a20342584900d840300030701003174204000a5003841815800106040940d00c09040180700c0c90303890015034200303401490b003103580d403410b02410048100200003081034003540c190358040d84200c001699208040d0228010003148903201000140c010390201030590100c150824980954266814946e10f00d080790301700d6000810f0060414180400101c20542134041e0381301d90301b851304000c00c8503039800d00010300e6141c08a461000d1041000130382d10550078806140c603413040b010346c0101414880c07600051100b040206051103400144e850080410007181040e5034020305c0039000c8031251002c80080c9010709042030072500020303400c200c041c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 623062832 1250 623061582 623061631
    0x204061718030702060a03020f0a09031a01030309170a0b1006090e04020a05010e060d060b03010906080303090709022506020301030213020702090a0203060a170609010c020708030904020319020d05 86
    0x59900301c035a00642c40d00620307609110b03660300b01148607824541d003800340181d03445105004000c1009e80384d0320b50500509601d010ba144402ca0140b4048480b80c02005000181d00000c024094526a84540080a406c030076050315020301507400402210381071050184041c1c078546048251401c0d921503e80103625110391401c020400c07540654000b101d050104903c1d4000d60301001c1e00c001c0504210710300305c0301e9840301e030545840c1c0d4000d00600c4800001000b94000c54401c80001d0a1284040c42c80c50400c1180e0359920b410034003401c0ca80d103500094040e4203c080c2c0100400243c05c44580140c07129032410104000d40003440140e0066140c0c42c05036000300c2040c8221061503600502d03845450315104000e8009401c020b02071b80e0814069503010030b400d43d042c00c1c203025081d02d000c0205001d00d840d110071429980c0140103030040d50301084003842440c4006c41078030502074043d5030050f140c2d950700b141441d00d44c400a081c41c0c10944002003040050f035007500001d21485103000036104208000045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 623064082 1250 623062832 623062861
    0x3041a1512210f0a0509040605040203040507050f101d030102130e1b0304030c0b0406181401150b0f03100e01080c1f0c08090d02120a030e060a1706040e0102040617 72
    0xc00f40801410064012203134042d40240c03101141c0900700043e010b8840c0f01040032030780180d038243c41c41c1c0e10039a0100300c0c600e011404401156410742d40c0c550701c4100c0100c0a84000c410021009000320040e070401020f480950584180e60480c00c00b10704115501c0c003220f0300038401521040403c044000e0803114202114084900903513050f504d0030800c0c111034840d8010302e078010b0000c441803500c6890030154002a00700e210b05c1d00e4092041da00d903581c281e502c40e80c2150840d1112404020100346d04002d0760500c1000d451520044242c41c1d5940c0c2d0740d0b070b5042642400d45400103040c401250300040791541c0001042a1a04010340e000309400e242c400383c0c8030800f0106031901d000146810107250000d42004d02030710740312001034803c0406907201c0c1d000811464040d460701006500807a5170030f043c50b901a01d8600368203000d5900503d0031020080040918030380c44541280000c02c0008140d01c3d8a5585c0286207145107000210745403030726002d0040c152a0140418444504903101060a90343c40c07118 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 623065332 1250 623064082 623064097
    0xe1f09151e080601111006051e01020d0c0804050301090b2a0a1d060f09030d0507030e0d0320100b15040504150914040c0b03041a151221 60
    0x16494544204803030700302d604800061003d41006401da000da40407000400141078076201415020501508050503c0b000ba00c0350031a6004c020020980d910180e600405c9a0910721414a0a070f04440d4003405c2c26510f40c840c0b684019010340c605000c0806000b0840d1149028100b000c0300c80000e06404000c0110000c2c640300c0e02030212201b0007100740003e020740c6d0311080c1820090000100c00c0c052a00240d074603085282c04140100000802e020b203441c05200420150406062050400000b51401054a10380019050041042e4031180c000c0c10701503080c0340030290007225002d08070b281a064030358403003607000300c0200400d0070001640c200749000000c0e80078008040701c241e410145403408001c042c0c40004030403189411b11150128888601c0d008615407055402400c1885080c00e01e481c44280724164408244400140107000020312541d510040004413448941502c1e1550498040c061095100403079105440700000c80810102151040e0300545034250700100114810480350244038625 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 623066582 1250 623065332 623065367
    0x1030b030105241203130303030c0f090905191a0307050117060d060b0d08120109061409180a030206060901050a0b04030b07050405040c020f2802010e1f0915 69
    0xa682014080e503c034502c414128000c1c040503030090204207003801c40d844070150003900b4070303100d905000385038040c054115024450f1503c140300302c1041800500300d031070502804031140d0301c60700407070303c080c0f03400d401071009070a01941044122001c1215460003d880400715009000d40203000035590f0040c1006811480d83d50710344038043e80d6078010401721151605c402c84903981d80386015035181d110703402540e4250b8403c1c2c0d035995179034040c0030511112000590200131a0313810010300f440a00908808410800805e9030540290f8039a01c204c01c001100c0c20b242800c151080f1003281050542c00141240500400e60b40c540890340c880d82484540d00f500d015040d8021402c000820008402481d4240d00500c2d52034440d003020348800000d0240c074412450b280040c0d02c07182019400003424065012421044170000045562009141031440e212020207418000d0240c0082419120310300000c4495944041d030f018211301414000c0c1824001e0b0007041043c01c001400015880c0c002c0381e80b0407101c281030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 623067832 1250 623066582 623066611
    0x10810060f0f05090916030f06140112020d030e090a0204090b0d0206030423060c0a0e0306071b03020a06050a0203181b1c02090106030e0d0e10050313050a030e01030b030105 76
    0x82d0600039111009404c00c9441c0c440c1443c006c600c03040f020380300030103544210f03401c081400d4142024425201400c6000f1801c00100004000549100c89510282c036030681d0352031505902c0707003001d130761191000e406e80380c20151003030410503843d5581d40180280d6140c45070820607013103100b050008454034020700a402001c00c00c04180841c0700007542c04281894000e07505403621107643c1c210f00f81142520018440703c00418401c0c5940e810419100860300c4c0ae030f008280c1c5160a0300c2c020300180301080132090640e00c01810300107140c1300780300340318950343c12103000d200a06042c450b65009500440c0ea00ca900f0b0344042c025100e5040200b2880c03881ca0307241030103502800b0650b041148030905405080c45101840281c100145c4407094030070300a06054400041100c400310066007000e80c0814440204100c14103207955643e40e0034a2010fa240a91a115132070742d8481c5a140c03410305a0300d00c00703046441a110302008169100c240403405540a0f41e09005480541c01494241c0c0d005445010707482220 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 623069082 1250 623067832 623067839
    0x2070c0b0702060f07050102030f1503060408032a07120207030f060209011709010509060c040f0b0c03090d050f070b04050f0108070e060a020a0c0509010305060a0f14010810060f0f 79
    0x1005041e00c1030004203614506003042038080007070b500c8440100d030240d4000c820858035070300550b2099403201c440042d6000030313124400000c1c0c5807000100024040f42021002c18104510b041020b20117018500703d880d0a1140700e5242c1820303400000d41100c442d00143c3c0c80045c1c0038030109141c030403a0760040034280d20300d1040d030314000a90411881e071030420a0801100f0036030a000c600f20350050202000004030f508080c0760030790414100a0000300b00340010031007040050003c2c1d1850301258004011207440300030300d86840d410b40c41621201b5a10124000884080c810041501800424050308484640740d0b01c40340034006014a1280c1031b4000c0041075030180c01d5026069a0f42d0280ca03070f103450b1244c4414400003400070741000ca6420b005130b0200c11003800700244c2c0b00c60a406010129160b00c0558550f6881580e01c00b001804580c203076440c1d070403582100c9066040300d0380500115028250660310b424110381d66408845050042030300700840040c50050100e003480a982c7c030f108050b2882800d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 623070332 1250 623069082 623069099
    0xc090102030d020d0b0d260a020a1b05210d0810030b0a060e011502070503031204022b141912030c050c0a0308010e090325030512090102030a0f02070c 66
    0x240d04d80f02c00b4103448803403103a610780d1101c4089040b03d21510f4454030714070b90454170300090395800070b640382003585c204030300310440380c0002d161542d09502c00303d400c5400c4201c54000c4051010341d842660030040740e05c18491802455491212406241c50441c1d15450340905c1c01c0761b2030703a41500e41c5002d0483c001000e1020a24807041d159100728a280081200c0d0f690381201380d12840242e00031b41c02200c2990b4100307001507040c0561001003000714003c45c1403a51031800000303441ca014000074411200d010200750344113003041d5000c10a1040c5400c102103058241807071442c404585640d071001d8052040101c0c180040c2c82702084199400a02c4080000082d44090300104005440001171080a1014811200d8104180c00d60030340f1070740d02c84046515164a416a4003005030500e64a40c00605c070600c03064000801000e1046000300c0100500300044c141030f21349100d41d64804281006500030040c00e0380054008501551001c2010802d103504012224203d000b640c2c002400103000000c100900340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 623071582 1250 623070332 623070337
    0x28020c0a05060f130303020f1b0f090403090e07020a03082203111603080a090b070803190e030309161509090509070e04030e04050a0e150403030209190801050c090102030d02 76
    0x26028010f40313803100d014001803900c80c55900803001070380f08405000f1901e00500000d4425502c1c0040300300101c102c0b800040b0341140450100e401800c1000000e8280751080d070b01c200003001e26001e007880b14200040b00945408a603417099010a17141700c0444d100503003000c001c407407169444400800700d00e02554104d49050a0521002c114071458040904015915400324011031103644d059503219041c05003e06282c1903940f081c09210002d220f0b160215940500312035104203503454480c881e5020f038010100500b844605044c29120200802c4500c0304002009280340030f0410000051a5640501d01c0441000c0c40c221000111480000c10060303040d5002560044007010030f841506c7c0c1c840100402840084070154009000c40100e000030341458810550400c0f04200140010b2900e0f00754543d462514902c0c2c001d055402030000340505120f9030644150810041c1801c00c0c0c60030501c00221000042d025103c0c0d00e501e04404a8070381c2e18510103c4651041c107130091820010000d82c584000e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 623072832 1250 623071582 623071597
    0x120e010908070b041a0c0706030b0a0306021803070b0901022e290418030e040609020a05070b0c0c0618010e0105070f0f0c0507181128020c0a0506 64
    0x8046034020411400c2804190b0241c039061040b291038070325004d16010300e8641d80d0a0940000010030585070709000100d81d83d81650114280403450b10755180108400d0a8554800fa00d024404103054042005001c1c04880342031007102201d985548501c0e01d05914421208114051b82c054081000e00c01c2001c2c881807140e075002e4022023504000300c00140c0035a1700103c0070b0b22600000e5800074072901400c80c1e004c82c802009817010400704881404100b500103c0c9000a070500818100c880042d540b40e40150f030241c03500d41c0003552605410800a00a50489201181c4200044001854691117802518003524611006180546034005481941700d101038a2540554803030200c0d442610302400351074003a00d115030b81c442c445440b00384014000b50300c07090b00ea010032510b402e4100200d10005000c00584e141da030742d04482101002801d030014891030031154112880482c01007550a0b20495400308a000c3d81d204c40000d0803040c5003241c039802c45200160b480710282071b040c8450304010018183c070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 623074082 1250 623072832 623072837
    0x3151205010e06181e0604030305060418052a0603010302060304080c0a0b061c05100c120501030b0f0f0106140313060914120901121a0d030e1c120e01 66
    0x242d040c04200c203003403080849404134510100c0444541500081107100c2d15203140b0480c200816085441103a201c1e0790180026040544600210306a80e071194001c10842c0c1040c4c0300074680141916203503454071610402c0c52102404a9820404019a51841420032500401481c610303801c2d61b00300050354001070415685444203201d00b41321003c0401078005254011440110350b40f401ea0100b01c1c07102d0314079048a1702c40c0340701035079840050000200080401d12440c00842c107961011000c0394525440b034000107965051a0000041c0644d070f55425004992074042c8100355501c0441c9006849000c0c07040c40c0005410300d003d10003014481014542140e42120440b110080e99100c0c2c03c1a10301490b016540e080f044007650b03410203000c0040442c09600f240e02241000401400078144007055013405515035100d040c070141c1003481c800711100401c002003166080403841d040040c045000036011034010000b44590100044101c0c401303910095001905a40700f0360800e100711a042c0380c17060094107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 623075332 1250 623074082 623074091
    0x803091014030f10141f120c0806031e060c0f160506090c030c010e0f04020c011503140a081605010b0a060309050c090f071808010c0c05010c0315120501 67
    0x5804600802180141e01a400580690074180701096500d0010b511200704003000c16035401c0151107011508a0000901c00d0091603803100101c00d840c03081c400c8145092003448c105504948070313044400035000c0c2400b43c0855540d4210809c500c10010014100308006030702490015007a03c03864401400782503000300c0600d0070b00380d0000c0a922150b10300002104c0c0c82c1c11801c2002542c00040224089660f0224001c3c8030050314800013030002c91600c0c030348a004514014034003647c2e4807a82c04552600103004020451708041865032030301d0020380d00049401603d0b400320310001c9040025031401c05a00201118904103080750f1142e0060100b00041380e440d504d60030712264941d200514500141070584001c11012012300c1e14a00300002002428440d001c01e4007030007548038184981550009082c00c08400000403800030294901165005480c25800c0202401c8040d1f44001030400c02e51040c0001d0044c90001d480a07010740f01308011803408903000c1d01d400c00644105803104418180100c0000a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 623076582 1250 623075332 623075357
    0x6071b030507090b0102060a090c0504090f0c08010b01020d050f180f090c03010f08010e0c0603091501122108151201050c04050a0f0b0d02070c0e09060115020708030910 74
    0x182004129404000001e07604c004003003031540c040c00825488440300c88100b090310007980d12151220f89900505024980c0c803007000040100000c0740d0a07406400482169600356540d5100c2d02034032010740e5981c010300038989501d9910380914151441c00c00c8036401c01d402c00321480300d0b540da45244480c04507403000c040680d510035034507400e000780d00404101000b01c1d940e6051401030a00340203564410300c039680c50072202202022010a2012084404444c455907a48801c0721252400840304201c0c3c0303070710f07004000004030000c0d013220400040c2d01c24a154801ea404500c03501131801d0b10080da03100442c82d40f500040458014241000003407a00500c0142e14540070110305084034821258030b184c452002070244018a0030101540c0200b00303d45107400428200008085240108114000c91540120b200340c1049180d030204000340034900000322051501d000c005580d25028884c4c40b8012281a0780c140d441d51010805605446003c001545084090400c1c000c00841c0c440405041000c00c00c51407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 623077832 1250 623076582 623076593
    0x40308030f160c0510180212010e0606060a0c12140a120e01110706090503070206030408130f0605040b0d0f05011508150a030803060f120703031106040206071b03 71
    0x25409081c10034403608452a080aa4200360500101e03003038244810303280040300041001419460003420014042401c11119000851152045070700960000108414078103c000542c0094280c1c4800310464545440d04d00910065110341010700340000d07000c69020001c00e0551000c24803000c0c552824107000c0400804d003201c01d410000802000030800b820501746c503103460040301c601c4c80400c03000700b05010f540d203a980111b100301240105881e44841d41c01041c00018001c0d140c0701c64024000d2980e034900b0381743c00031655001c40300040b8125803044000c00c02141001c00c0000307490154848030f16007802c0c0401c09110f44c1200c901c070008680c45041c1d00d48034020794002d040c020b1040020304031072503c080e1800343c0940385c01803403a2034424400540b20f0440e5516000d50f0300322504408000d540c1c2d01c986000c1602c015144645503001350b840319101c014581c0000340032081b07a0081d80d60460315070080074041c0e00d51030305640203942710005000420108100e0290304d680d1094040942c504a9030b02c4e81c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 623079082 1250 623077832 623077837
    0x1504020702030a0813180e030a0c0f050a030804140105010303120f0207050d09051f0806100e03070609090c05340b010e1e2401030b1207062003030615040308 69
    0x126003020503166010003028846d001d4245442011030070910000b814048100d5036801039107c10020092041d0041040c009002ca040c0c3c0c615800509540800280c1d042c027401486040e5000c0743c126030210581500c160061080394141c95142e6190302c070f140c290b02e400030003604500102c4800e40e5030800108001400030800314041c200940c4035544003501e403038100400740180b81c4180707135400c1304107416031036040d804080c03240e101c201255110000d41d0518001c462400b0142055070309817003840f5000c201a074009500804072190410288000100c0e49000c40e81e0b40122800c107a607122000f81c604a00d0008140750b40072502c51040701c00089542d0381c490f0342034040c00380c0c425045d12000800703021040c0606807042e90f2030f130004c104403078050803c7c0062002801d1a08010032200ba008464002c441c0c1c466084a0f00c0540c005104007040c2002d1032001c0c1d00c0b28218403610700402c1c1c91141150701d44002015031020490038101035811035450380144a5a005100280c00300180c040102100056201c1c02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 623080332 1250 623079082 623079097
    0x90606030705251a0f010308030a020d2f04121e0236070203032415040504050a060513020d0603141b030610061110020f0c0d03051504020702030a08 65
    0x10a45607940c182030000006a07401002d0710848013a03001c11001c2c0101390304590440c1d501200070355481d601e0030501c1c0c0090003a8004c0e404800d081c0401609180510302c6411b00d090350300c0300c8021040c140c2c1c070050b142a102c0c038803503c41807994140600000c580f862000800743c80000103415900c2d8940c2e0300043d400964209007910300c40000c05260f80c4607034904141ca00b0390941c00040360080c00c00740d80c0a56a0300008000241c085e650503124165a505080582c004502c003400c2005070715031040000314190001d004a81c000c500e41000549440c0413801002e00b154005800103d010411f860030201039030221814810094803040c00000054a000003d030b01084120040d018425004041450b00e1a00480b070318442c0e404101404291060040004122074450400c0030760b41c10303070500c0d403400c001001170702c04c0c0521310100e0180410103444004080340c101c44400d44190000c045010303030845005030b5080c1d4035158001400a800e040c25401820800d000804560402d406959200751030b41c01880c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 623081582 1250 623080332 623080387
    0x90b130503071e08010903090509070908011803110105130f0c030b0a020c0c03120f25050d1403151e220c030920060d06030602040f080a02090606030705 67
    0x80d058040c100c003e48006081103000034840d02140b610000c0283d00d036806139501c03485001c808660303402c2c0038401c044d00900e003120082c007481150721180350780c8180c1c0010a40c04030341c2e22441030414001c10310415109065a08092201c84507a4131440300e251911a070844404951680102c0440c20300881948104424003000d84d071380040720f02032030800088141f0701d4040e5000d00b40c03104042d442602603500c2c0b00800c1c1085a200c4010f40ca5416448210040c5010f000c030f070307843c6608144070300803807505070400683c0c0f501d00a0b142da9002800b528031040303406d210041180380c01460305207401c4008c3c0000703e01007980c80103114103a40014100040461322415010f0141812001e01011406043ca281d085414100403c44041d2500c5d60302c4840040029501803c2c1000c0654659071403065505004040380d003080029220b180000081d4403a000d08050218803000010f45100e001a4004c2d40e40c0e03015104d105681c0307444082c441c0c207400203422642805018030004c41495103021101b4400442c08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 623082832 1250 623081582 623081609
    0x50d0f05271510081002030109380307120501050a0c080403140a030e0303130318050112020a03020408030304050303060411280201061d040b060906100806030313120c15090b13050307 80
    0x440e0011210310b00c0f51034141d00450200d102b20601c10b450300d5074281009140c06d550170358286002034100303c2203402050744004030045910030321505500c0b21303100700c1100c00100108100700c0c000f03a84010b02280c0c014000303850112418003007a619400343c0451401070034042540c43c854903c0c0703030860700121031140c0d2043e4040103036410302d940440443c501484c001d1803100030700c2c00c01f80004c14020f040c0c03a6030103100744c000601c000c240b4880d0341104c00610301101034a449081034038095440c0d60085d01e00307511980c2484942c110702d244907800c9070140940e8010942000310382c928207130000e075204020300f0290b540c5e46800144460b640500c071105001481c030175034040e1500d441d003500707486001340071280901285c07020014580c41d0840e510b00640613500b8000000d91b1040000791070b6209030180081d07051561480019010101d10181d1403035445424800c0c6916119611003240344e081e12524400250803140c2004003010a400500382c003080c0580240915451b04c0110786002d40341c0e4044403000001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 623084082 1250 623082832 623082839
    0x5040632100f09170d031a04060b070515070c060b04091401020a03050c03040f171c0c020c0409020604050409050304030204020f190c0201080604020307050d0f052715100810020301 79
    0x1c03400303c40140c424125003002944412510035641c00400e000071050580c3c580381d01004004043c098072503c00000c10610160381c44022114040d00702c0719040781c0310b208200e0504100301000004034401d5425030f5503150300c0700e500c0d141c078400b03000f000c8807075504140e541e49001e003c00d011340b0801c1200c1d10a5800540e6a40e08603600030101e070001440702d070a08100313205110009100000b141890368002d042c060b0b9102d11808000064820001310203514062200f084110507011340143e04510070b81e4007a10700020039441444252245440000c0d40528201300910152a0503480101490302400449041c00c2d243c1d404101280c0c005c0d10b40306c50345800840c1e50640002810424614220145842480c1d10301d190300107020b224001c1d00151280350080009003080b071041042e603017426030808085c00924621a400002043c06a0b903140355010b1035500001c4107200c402240c071107560018010f14105039040d18416500f032001d03040e0561400070b032100003660002004800740300030340c9040060f0346e540b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 623085332 1250 623084082 623084087
    0x1050f090414070e120706050a090b030702100b03060f0415060506071b1d071b08070c030203060c0c100203040609050a0b060a170d0f0201060503010c030906050105040632100f 77
    0x18203801309124000e14848000c0e1000c02007020001c81e1000c1c01c0030b07603e0305060042582c0003c601c2d0020350b0b060b0400700c10030003426800983e010403c2c040c0242000781c1c2000b1420b03da1a1881240c00b0b022403c0414003080005a030b001e2511210b0101d01c4001500c241c41d1070004105501811068a151030132980f030000c0144142585c400804000344a01e2080040c0000440c44c148000d0508050000d11545510740b006990b85041c501c41e400040141d403100c042c501400c0380140d82c00309a020317105450016064912503000c613810111940f000703042e000d02c01c5e404030002c0d610090084440d00e80f038800800001d0720400410303800034481d00300104540b810381c041c8242080198004d08004401080d48400400702280d045202d0480349085084008200c2d03040c1d01400b6950702042e010340c40c00780c44a64041d4103a000c03071a110304c1507001380f00c90390340c0307404000c2038807514000d054407541d41201004bc203a038000c056136100c0c1c0100801010040f80d17007002401d444080429007010800b040041c203a041d0303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 623086582 1250 623085332 623085347
    0x7060504110a1a0d14090109050616020729121602011401052419030b040908030115090b030c04060f0c0b13050f0708030c070905010503060601050f09041407 69
    0x800d94440050525080c2403e02180200c942c0103103250703000581c084e00003100e03007025919010750406440c00781055018280241070014042c1c0382d078010400270034010080440603404000280c0e004082c41804c1143c11704248400841e6000083d1401100c140c0c40c12103a805001d0301c10450140a5507450443d04600c1e040f130844921000310b924000c070f401e006070304001c509810f480b800e60344c03100100809244800d1940364030303007003605a010126084000703406081d9110b00c1044250340501c0b030798188000303100c16580307240c3d0010121841407006002c6494018001c40f20007540d89049001144d992014400d198030039241407030020b0b0002020300210b600b00c83c00144403801c80c6031125030705145072a4408400006402d040e2080d4095a10070300340141041744445c17105060b015a000a50368411080c0d0340c2d0b003c0b41d03110205002d03c24001481610b03d224241c100c03140580a0100b50341c0c0d0720f004484940c4094440d0f00220070500ca031590a071030742d03c41d5500c000091001ca00d0b613400c0241c0050b0240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 623087832 1250 623086582 623086613
    0x40330173111030f070302060d05090102091306060e03191e1a060114071a070507050f071e1401050906070f0312181e050a1406061e061e040b07060504 66
    0x80d881305d5001c10050b00d0312011143d9130b41c42080002415214199202e003e4070880380c1c40e43d80002d40c40c44e0748543c848150b200c081160305940f129104024500309160304c602c0070070503545606090400003000700350040c03001e05603a84641080c0c08201b00c0c90303480200742c02103810400082440f0108010325560403c1c2d1004980a5544a05082001584d1651403500810849503d02074101c40400d042c1c030f0103001641c10f0300da84001170b150843c46000d0141c0e071700e04c2035101d003102c2c4030805481116680740c41d0b1051002d6543d02121a00c10a14420043d940380d40f01c440c105400003010004003000c4ad549120810700c080c031940c4e1740071062030311600c2402035039405030342812520200c0f114003000a40c19141c0030340007010000f800d040500541041418052000406820064404101e82001c81c0215002c0d1250703008403070030242a076003c0e0400300211081d41d907490b00107008024616803081c520340307280c94080c08810400c0c80c00b905c48000a919820824084440d03035110300c14001044401284c0a009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 623089082 1250 623087832 623087863
    0x1805010b03060d020f01020102040f300c061b0606090e060a0b0310091104110a03050c0717090a1a0705010e060c1e04033017311103 58
    0x4508050001892822010030f0081c8501300748030898000e80d0007901500c00420030030888484042e940d80d2484042112202c0149180320a62881c61070001d0130117040d4410354224440b030700110b060010607100045400401440e8054414481c00045c91f03e0082001a123001040410086000b02c801c41c07501c0d00c041c2041030310302d0901da602020303914000384100b01078920140c0440c841d40681001517066003a00c0c661600141031424845200d00c070003008040c0303e50301d69030411407991070f44070003806801107140062840d030340031106899024880b40500031010f001006240c81c1c564031003d15509203c0c240d1409804603001c5a03004c103100081c80340d040b40f040d02c440a08494a0445e4041309284541200010584107003440001040ba091094801075a0301c00c6042c041044c0c4c030380c8000c440d24a01e00c58250104000720300715020f43d11032450f205001d03071060300d014801e1f00d48840c01c1d410f080d070298012060319002c0840d281022101200181090300954a07440310440080502d41022110b2205080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 623090332 1250 623089082 623089087
    0x6060303020f0c1e190b040518060a05010804050c04050f10050a030506070822080421051b030f070b0a020d0f0804061109042c0a020112180203071805010b 68
    0x41c642c403101c044151085120003c00c0c52401040700140710b805809000c805c0b80b030815140442c046058100034000d407001100c55041d00d0140c407501c00014101161455000700c01d281c010481341d4040c1a074150443c0c4200b003500c01c517800305800b140807164100d40d010103070070082007400000e212013654030003c0c03c02501c0d05406641961a6140d5500e0701416080c200100d840024801810009007074060700030348241b12800e011182800e400c1c40d0068019819071000401018011000840d14041100d07031020241c55026080300002c00c044c01c5210826405d4081c407412a244405c00b0700020024082c1040310306c0c0c8591030741400034503000d1040c0d484000d0110416403103500a40050065903c15441940844c2101c481d081c500d1188c0285c00806800c0b50a00304000300303c140ad194080308a00c0302d1000300300000e402110b05d540d02d0b024441c0203800324940795440c0404d4261500140c1c1440011107500405101c90340c042480c28000398442e50240032000341c00c3c6500358090180b1401001c40307004060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 623091582 1250 623090332 623090353
    0x3110402160f02130e07050d080403050d0806011202160201080406021c0501170c0d080901300e03040b09120703080c0f010e070f0501210e0a0b0c1e18060706060303020f 74
    0x782e844015000f224423508090540d42d042200035400c40d40030b180e00c042540c010340742845015102803415605107000c43ca00c884950550141fa100b07803a0583c00000c80a5081e038040e40055500a1025009840c150740810400031800340c9a0790500612507016400501c0b503141410350b6440074150070f0030084a401c9036050034801d54402255043d41ca0f0081612541c6032420401a110711040200d000c6216000d01c0c0303528080e20000040c03000e01e020201c820300000e41c80a80355503c80c4035900464049003000d10880b0610705041c20f6070610354020008955203540c5079241c02d00f0507007141c0d188602e280d0010507002101d40c42070040292607042c03040148440d9040160440f1030101034068030f4100300034404050090307043d044440c0d03949090034000b04800e100b2071166603210780e0000c006131031013010400403a0305c0d03241c86e204851182c840d0007119182e020303540484c0e882035400144100c050020385000c140481d07a0b400d008010843c810350000450918500e03020b03040005c07408035100a40c00c09170204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 623092832 1250 623091582 623091611
    0xc040b0312030a090c030b090d0c150e010906090f03140a08160302210a0e190303110c010f0203010e011d042306010f0602070503031303110402160f0213 67
    0x6030074044240e403203442e41e030780407074800080c058104080c20713081260340000140701c0303800b03202030041446e102620b03813124034034a0a460100c1c07480b030010100c0f00740c004540c91070781056004030001a80c0600100700000c00d9296141a1142c4a80954518030464491002c05170021048102c1eaa00b0f079807104d040c10940c810140090000400d4004c002482240d0300140d80e1295040310700d64000e00b010b0b10740000c03044ca10408070f01d1003210644121490000580c084000000e419004424800d4031080301100c1c0e65401c4015280200d14040700c0d00d414041000e680400380a001d240b032100b001c1c0184c50350302d00b824800e81104103900803089000045640c400141e11125126406604070140078181e00c001074681d4034140000c00496403d0050b10000f08030860161801000c48450780d08903082c65480c0c0301016200e01ca145059801c1c540800700030000910078403021044002c2c0104010704122001100480388501003a00310750054000c20400308528080c0141030014141080030464442c00c0c0625 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 623094082 1250 623092832 623092843
    0xf030d090e0a0b060309010618140103080a090f080a0309271517101406031f020d110c0f01020f1210080102120a1a1302181e030c040b03 60
    0x560440d503060800003090000d02d504289000750000d8001e80d600d05d081029140203100900403d590f00e0700c01401d030b030713a043c14500442d80380e034150400804a503465035a400303a10741d0189a40c3d50a1040c42e010014111503040070900c01030946030050000d940a40c5002009003800d608030b071075010f080c03079034081c4801728820018800308038190001440f2403802043c0650f4003040d61100d2010000710300000e00300c03040401e086c04480310383c21007800a260141d031a00c5244100f118910341592041401c141030031002150b1044241007054010325180c030366038008082d5060404102c80b810b00008011841c504104001c1110300c032401c00840c28801501440707400e85c45030380003c0e25403001a0000c51010450450800c0c01051604000c5641d0b40c03140c0d04200c16190200c881c2032045181002400c440c402080721902140300c0103003100304401c020954600250041500c244001e0f0003002c2100781da0300c5c2c581400d1840741031005804550040202010303e004400d1106600171801c10300c1c5030085d07440c000b44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 623095332 1250 623094082 623094089
    0x70602150c040e070c140303190f0528140708040b090601081b04020f0a03150b0a0e0907021e01051b071709130212040c120c03020f060405130b0f030d09 67
    0x20185d04418240c1028210340310588644041400008144284001a240c40e400a2891321030b0902a43c6804c42a0384100e90045401d41c1d030f40c00114406080c91082c1c11010040c0e000204400502c10b0b81d90035101c000038108598400c0410030441c00c0c40107100d4212901e95000c00c04a0080480d981820003068650140a04480d0300c4a48491091015900d6405449080c000c8a0712241c945140c0a4014090f1034901e546800c4442c2c4188007085c640804012200384813100e85641510700101070910a500d40000e1003802103000d0001c0c4243c2607a12112090300c0e980010001003041e0a203c4a00800c00d9169115034181500c200805000500c0c04d07152030801c01c2041501d1500c6001000c04a108a58000040c01c2001c0c070004984201d910000c0801e4000c80c02034405254894480301301158050815101a243d08000c0c901080181343c1141c4003407030884040d00e0b480c00c256842c008240302e691001002000341e40c80b20b511648a0070208000030303154100310020040c2084400028180c40303210702 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 623096582 1250 623095332 623095337
    0xc01050a0f0c1d0a0b0c07030606120b01050d0f02042306010918050a111306080115080a0e030f1c0c0e090406050901110a0c060b0f180414070602150c040e07 69
    0x40d4483c18580d60000c1c040010301143e80103d0b915400455180e07100d8515000450b40d161030310314003082003142202003081c1158040310100c002e90070071080006030400f4071000c8450300c60743d00d5494016150341c0142c2007095582907074074a2000d400c076540800820000d024a04000080c40108007848161580d80c8a211080100240c01e449590700c5001500e000c013501120840001003103480ca492444100c0d044950315941c00250b81d8840240ca4803586c03180c00071800060481000c41c100c108035a021a2141250700d04170391a001204484400e00d03040a2204030084003650f09188d00c0302628041c42c0c150389003500c0c1107401e0100c02800a158010050000b42046a070f0710002024814258040a283d0014010803601c0f0b07080703060000c0a180000303c04030b50351030a10320b86030300c141000b0980b89035904008200e20580c0080035100c94a166000308141c40c0c60882d8614010000c0741800b4800241c0b80341c2d4081c1c03200c28400006002030380c40203010303c604035604120801c400600d00c0086030b009031443c17 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 623097832 1250 623096582 623096627
    0x11070b090304080105070507061109010507080d0902100908280b0901150b07030f0903080f0f070b13020a171b1201060b0c0d05070206030f1003080c01050a0f0c 70
    0x30649146503000d41c0e045048190728013414003600b90f030480b01030b1040c00d200d03110900243e0341d000140080d9004450310f0a010440500000c030009009401408108410060019130700501d6000a038052940c0007042c000f0495068080c4640b100c28001c0034900144410701801a038816100d070301c980c61407082c2c041c1100d42802d01241e207688080d00107038551804941710406c0300b81c0300c0e009081c0f95800000120042507150340501da0180c0203a4610b41120780100c080c9080c6804180c0d0307095243c1c48241069150b5a0400c82100042e00000f00140504440c003406802c2c0600361040c04028080c079003102c07400740700413070b501561310130002125504c0152022030740e1450740c900d0000c20070450761038440cdc00785035090000c003007808019080505905d550500c1201c0c01c0307982503c41a00e1380c2c4140300d00650401010800100e104000305c01d09900f040020511801ca070365a5180c2a40603084061080c801d03944607804c1c010184644d024001031405a494204901c02c1d0749600601003081100b404c03281041003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 623099082 1250 623097832 623097841
    0x1305010b0f070203120a0e0f04180b0a060509010f05100815130603020d0f02102607022103071805090711100216150c050a030b0d02040908071511070b 66
    0x6010301d1a9146642554035202c2c01c4000020707000100100242340503040c0351009003090301d0302e4014019205009400c2c90030301c045907290f00d80030400080201e075076076448220000b41a10381c541c100e0300070400c10200c034030300e9420041045083c40348020000c0c20001100e05004650701140c4040000300c038119440302124113254103c5e0040c00d40c1d0303800a50f03c0710002514205100c8940800d00c1198400c039800940904c0c11717002510b06400969070004014040c2e003070050000300c01840f19030486924012103141003082051154510103500c80c4c0899101c001c804e20000a81021038108040301c2c440d50682c0140c1040c0101d034040701c004002c08104814002045141501480304141c1c000460380207540d220820320030041481f1a01104582150860b000000c0000c807034840d20068032841d0350344c00e01c0e041445904a0280080082e05580105e000d42c41e0001680c49210b25280a4454000039031206074078180101c44a00300c002d02c03018142022000d440e40707500035045918046d0b1000840c106030300c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 623100332 1250 623099082 623099089
    0x50307050c150f0609092109040b0a060c050708070501052709330913080c0102030a0b0f03210706020403151b0e1c020310050c091305010b0f0702 64
    0x44480d070450348015a0007445500940100c0481c402c2006907a4405c19841d00c1032a155a000800c40e029901c1c600e20281d202041d41d404020817a4060040c808150039403038500003444a003042e807002d4045401d04240e1410040248403540080c02542d010b48006440c1c0400a0032034490001c00300442e40b040704180340c4904030040d1703181100101910909003440c00724a6194240407150560004030303d0810210682c80314422100d000c44000381c841202078a480b80c02000c98614031030116600d6000340301807002c0c01e400b407026610038840d80c100412140541414001281920380e40b040c0a40c102040146240b4005003115903040582c64107a40d498007103040000c024003039504000e0a12410303481954240c1c42036000080f442000340400c07014400c01c10000e56600403218543e44c1c00010300303110803107150702c00c086000b0843c0c0007a00f900c5200e00c6a0800c1400c035901150800075076080840c90a40301d0900c401d48480503a00c1000420180d4100340c4288801e0103103210180d403402000800608545 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 623101582 1250 623100332 623100343
    0x6160501020c16060e04150506030c040315050105090c090a060e0f040905010203090606120c060d0f181104090b010e040201091707051c0b13051617070602030a050307050c 75
    0x1c4681e0183d40341a0007802208001890500ca0040050100c0f0b00a0301540340600c943c40f03901d0804403000f20a00e03e88414441250401441c03000041f40c207100000c042035a0380009110144601e800049c0303581030008100510704040d02c0003204000c1440000c0040e151400340e1000d4411500744240c5c140d6520000940820030f20010315081070405032060b00b0084150040c41c065500d5034140d480c1f030b603200d006001105150295202e1590b1200020000c20b0820200400c00790300c4a41c00401e038201c503008044180c030440f4910004c4010344e1480c04c000c0c13110a407014411300e5800c480902c109c00450305c80348031000c0b06002e4010404001404201160700440220b0028900ca0514201d0b101724100304603104c1d2182d104180c0240004100d03440c0080303020080c8911284e120b820f807407403900c4800c01040f80c031130b0190040b84c8900c04e4800b0130540e00c03904d0480d00d00510414400f4407440954000392410030006078041410b40d401405442d645035040001e4a921030761600c2c5c40e549400700b4400043c50030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 623102832 1250 623101582 623101597
    0x3080a0c0203120d0f050901020c1209010e041a01030c03020a0f110705030703050d03050106140708090d05061602010b0649020d0b1008060103020702040f06120c0e060616050102 78
    0xa03c070000700c6219201c2150804c000b07a80009401b080142d070744c00324040c00e0b44200101c0000603003040010850a1016a014142c000030614169600080311000308080301c01445030f1002c42c0e604078944414039a490b000c0d441000850b03180940c24103c243d1000341508030a5900306090090418010210200400c06e40703001301001000c139a8100e40e03906140c0e0b1108100300e090400203080c0000455014041c900d000d41100c2411415454040e554450016980000c100036a000c07280044010118034200000c44c0980d0300020014150111001e020707084610a0442c18000d10080c0008004c1d0303000181c1202105e10161a203102004018201c101e50b000c080042280001000842803c0d01d880d40d07000c0c08422464000c2003109404039804c022100d810301d0035410001e2080d90000d07207154800d4015010092003d800480c4002e0f400144005441c0c0680000b41400d2019060303009010fa250541c00051000d210111000c0c1000030202e842846000e108035041c107628092013081010950485068 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 623104082 1250 623102832 623102863
    0x8010911070f2111031206030109050d02010b012007030f020d1b05010e061e2212021809150411091e18030304110d021309170403080a0c0203 62
    0x1441da191078080400c6821100502c4003901c0003030f1488200c0e00646110508940e100025814400c50550080080c100181019059500e8810140008200300103410054009070008540107610100040c00d540031071072850b250100024084403801030108004043c1d940101d0603266840300340c0040b6107481d030500c00040071000314107100b0b014112980b010307209440c800d03600c0c0c0c41d480165004211032405201000307030700d02d486482c4140c0c264000e50000e044c5400180480c500107468500d1500c210050350b445030390844580b51680301180f800407184100c04118000380030050400780c022541e00c80b10b4091403204d50100ea000b0a09010148902c040404401840e142c00bd00c0d21404113071186c440b48c1a4411b11250389400f01c1c1400c0301c080b14142008030304100660865a960b2210103044034400c0c0c42c150400320f00310402c2c02588640c562078080344856a00454810010300d411078000545555503120701ea001d0100780002460001102d9441c601c80c40c164050305240c1c00004d007041d51061500340c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 623105332 1250 623104082 623104103
    0xb07080f0d1512122d080a050a090c060e191401031a0f091b0a020307030f030c12050a1118120c060a0804140a0807050105070c02010801091107 63
    0x1228600e03800041d110000a10b84500c09560780c1e4242600d034442d44001014040049208001c041c0700b483d4544204000d00322100046000c2d80c3d000340e1081482000310009802c030f00810092041500905800c03400130300007041125141e03243c5810001c0c0c0ca000c0d80c1c0c00c200b4901c08100c040c0c3c0c0e0703481d8a1007140070a50051080203650f84c005400c0300b1565030345c46006c24105220f40000348200c8850500305100a05040709080c1603004001305000c00520b401c880d4000d10083c0881d034403402001e4008030001d07400a568174446270030b0281c521001c1c5403240c000c0505100501340515030010f0003024810660201244644030300c05200c0107400b048004186405000c03800d040e90680048803644c00a034150313440c8405d0b61130580701c00c1d1250724401c40c2540003202041103104143c854281164020301030405030071003441e021052410b18114407800d5444480100341075043c85000c0c1316a58020710641488007440802c1e900191010700c0501c40c00c84159076a200b21031607400c1d1442183c2c06103a2202d1a1032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 623106582 1250 623105332 623105347
    0x2041503032106031211160b18030307050f0105041a011d15042919030b090a1b03020a061716030f11070b0c0408100c110a03020708010c02030403020a0b07080f 70
    0x61510103100804c01d1903100303100780c101c40d5000560f500b10030307103a0400034649414460700316070427010036800001c0e4251008000b803601051040c089041c03401940d1001007941c1c102818400751301c040008000070442c5e0500c3c0100130b814440385110788405043e4444402e5030340c07401a420181c5c800264071642040c20310411584040c9901081080311502581a50700b8000b00c001380b2040c7c0401d80039000010244000a1010071480301205030701001d4034003128095401641c8550402e011840182d4000c0c4140400740b045280c511401c0002e4030061a02c0c4591120603038049865240150501000b007041c1000f02c481144280c000300300e03d0710541001c0c4030603c905041c4400c44ea11400b000c4c1d49201312580855041c213501c1040b10704a81d405001080d40c903034101c10540040080c01444401c6c00364004040c003401000744000d9180d02e00a4028081040c54a443c0c5402d485882c074031340741150401c0009000581c0c42079041c4040d1050202c00a4071a5078910300304030548900c102c0e12854100104505 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 623107832 1250 623106582 623106587
    0x5150f04061e090606080601120c0302040b12070608070f0e100809160e040212030c06040813170a02040b01030507300603050d0e03060403140a0e06030c07020415030321060312 77
    0x5c100716042c100031204140e84e88d64000d8404080c0c01340080c207580d05024200098a41034203d54800c0b0300c01041d03100c600c1c424410407840c0010381d0f40100e011600200400c04215040415050080c200d0f06208000c5640d40340020411a50300c00d4038410b021800c4080307024401c2c00c0102e000054005044d40c010162610039111303e880048400721711510600703074003d0401001006a42d203c200740c1c001000d103038645540380c58040e0401035451864040020000a400006641d03055110380310b43c0c06040c4141d45801804281d0f07044a0f4054141070400b801c0c000300503408800e1191000340030815245222150742032400c0c0201c084128100141002c01c007005201003c00d1001640741940c88140071142010241038071550304607030242c04124070104030310343c450310708005003104103551038490066444070f40041e0703c1c1e4005032401c85019101041c04411403e2901c2184014000002050002c43c41c641d801000c03070a0300001c203042c030381001c01140081d0303000303070418030140d80c0c45090701c060303031200c00c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 623109082 1250 623107832 623107841
    0x1803010c030b190305120a1101110306010314070503060607080403050f0619180609020310060b0306040f02070b0601111903050304031b03091512061205150f04061e0906 74
    0xb0140719000040000035040c40d000079490440758080043c00752100c048000d007101b40c00c550744040a01000526181d0a59800e208014642844565094403400d254000404a402064076100d04552900c18411015000019250300c80011614981d44581030b2905180c071b80a0380d440188280300f50780e40b40800c8000421014810458518003403114003540c5555400c0c0c800e07081801c01007490610101e404035685d40c002145503400a4121000c0c03d1404202000b180d550340c0c407864050b940071050000b0307883c25004490445080c0300c0c0c1035082000a45a110f44503c000d0700e880d0602441a0402d0203c81e018420043c0d0120b402a0b00040c90003e401d002c1d2075030b40300304c07000c07030005501c03030500e506151007189000400742d019528810114180f0951514001000a15905001109103100507003c0c0301d0140c000030b042c140038502041c0707c80313142c001d180c02c68000021010480e446c04020b0041c0c4c1d2005c00340c0d88660040c40c042041000c022602c2c4283c0681e000381034040c0d0400241e2000e00c00544c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 623110332 1250 623109082 623109101
    0x80307080705070c030807080c06072f070e06041409250803072319060e010501060c110a0b070308090615030a06110c0a1a0a02030c0d021803010c03 65
    0x2121030381a41c5a4108980601c24800000e100710005002400458402d00240849a00c82d8100520784081040c5451070030000302c03041e034001140c917840c498034030301102e20222140368500120308081078103c3d515270b00d620369070280400901c503c0001800c0b070380d544c0d08460920303800140d18002508140302c2d0503440305a12401901d400c40032040d003480c1500200d4036074003100c128801446c18000256903916904048a0442c502d00458029004078441c0c00d0203242200d00e10a030050000300c241e4070b00001500d0071104c003c5241c2e450300c40104980c6400c01864a896036100025030502d120390000154004060b800207034070a00046044010150403111070381c000c0500c8822100303107a644481400301042e1140030f10b0780617040301c2155000a480b541000150755940074080d41407003c0c8000d16441d040c0c0340c00090707a051900e00b88e4440c2900e6030400c5250009002074080d440d510302011b0b030f07901c00c0c0305803421440c00d1036002420386032094010080d804090b0008009001411040300700401400d41c46a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 623111582 1250 623110332 623110337
    0x100203010f0f0e0c2a060726060a030201050c07033e15090102010603020607120f02010204080307020d030c0c08030c010606020f07061803060c170702030c0c090601030e0a080307 78
    0x70000c24055040564144135120301540d06261070240c4102c484806104203413890041c81403241c0703404c2c0140c14001c6905c29400d07075949080c10410646c01d16480302000c041e076828042d00e041070180b140c90300c4001106070b0b50203003042da55406446074020714107600b60380068070030302c80301c00302d4180711806006038400f81086810003645800c60543c0000c01424200040703501801c5800c2004242d40b0754400740104190500000540c0c559036000701e00e50b9070081004440754034611081e500000d03000340d00c80d62050010320085090a0400d0421030341d910a29a010340f18481c1c01c078020b02014801c05054504583c051004110f159480210039500e4100501042036542005400b044d00b0344001104070045066000030070f00d60341b41c010182c55140480d002c4042d1001d80503000b00208840c4d000e404450b0201d41d4980e00785044010206c464000040c000c0c80443d042001b83c0088070000140701090712400321641c517110303101e607401a070040400b6598204140101407140c0c0c14401c40c0c4002d51b1141c8590b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 623112832 1250 623111582 623111609
    0x2030109020405040b0916120e0106031505180706030906020d0e010c111209040b0102010912180f060804120228021306030512091305040f03300509100203010f 70
    0x24006c21180610840d5a041001401c400000d01d45100d4489030f020700c4541c980000704d0014642079142914240d410949082101402160442030144150780e48402168030702001c4140d500151505e03030201b84070707034005c05884003aa0000d110081d41220143c0c0c4c1d240004008514480305218041c0012842c00008185c0c181e8205044090118404550043c0c46100d60300d4003820f401000010300850f800f450441d9655481600001c1c8032001001c01d003011500c0d5034000036816442c0c61078001c00354101d41c600c15202c440402c8215001440caa4000b60b201c280038440c0300c1c249078228075180b080498071010181d07500d05141c84181441c103090318039000791000541d811542e8200c00543e00b851100405662140070001e40d0740b00d0240242503401c10042c112102182c0d01c500d5001660b4041d00c06461100c0c071781ca0704d40101500032800740030300d034500111150484c0c40708462005c080c00d000354041d0b0294461000802010f414004619a000c0008045450b941c44d10503031120b88409000d034200d20300c40c0c0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 623114082 1250 623112832 623112851
    0x91802040e0705101b0204180b01090b060d09170f0703020f030f190302070f0602030f240d0c0906030309060f030e030f0703050c2e0506030615010207090203010902040504 75
    0x2141c1034064030800f8100e8101382d80110411580c012000c01d000482c0708207000500010781c1c40b8040c18101064107882d0420408060415128050301a40f000c269246440540a0030752110400da070803a40000800044517407983c185070f90804040c40007885ca001000031003000740c10750743d005402d40d80d0099003100c500300d11702c1d5030740c6a5a10480143c81d0103883c003423040c0c081007100c0d100c203410034008901d800350a119166403026903840611004440d8181c02004201c10b8643d071a403c15409008035006502d0305000c1130f4508030800310300000b40c1c09944d891036502d09004a2003050b0005150040b400c002c51640da06000740399215a000c2c210004122480700c08002e4440d000f00b00000c0b203603901451401049201400280e40581005c505001080c000030344252014070440440c91018003d0b02c002210290034030f5803a00c500341e043c0000314074280034040540c400103101703503200c600c01000c01105074099006030720b094941c0d4004ca54084c000800400e2042c0e454000c0c1003103440c1510144411001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 623115332 1250 623114082 623114111
    0x60c0f030905060c130e10031401050f0a0c02010902090a0207120c080307050a14071b0609080c0609010215240108010b1c1506090f12050709051009180204 68
    0x70400c800b41c4140d004001145030704030311000900c0c1c0380308060000b00c001ca0b6103041015000c1400c0300c407040755a111400c20001c6c012001c000d0200744484200030001e40c984949480100100030381804842d60751098421f103098007d5100310b0440340c00800419561600784407000203540074400841d112a545990400312902815644503800d0784414070505596500d80221040d400403880e400410032103c8031500b41251640080040c940240706251604c80003214440e016441c650240702041325940d41081100008202100d1409007210601d0785c0340c0240300102d14080c2101c0002c0343e41100e403401c0c000b000040901c0c0c40c0459044900b00341082c0c00c414015118127409100b080f82d4094200003024440040244005040007a1900060b440b2601701034a02d00d5040ca8201201248004c02c091040280364515000148034601c600310700c0f0303280c0359246c54a0303074b0051051020558544000c44c1d0100c00d00c01c4000094403242d402003003402804031007940d20017651401a4015403900040348812072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 623116582 1250 623115332 623115341
    0x301061215020a0207050603040f050105010b0a0516020f090f070f021b090415021305010e030106120b0c0d020708070201030b0406230d1205040501110c09040303050c090904060c0f03 80
    0x29000030041c161507103825150800780d0b1155a5030021402061030200b195a200c0d805107014500880e1002d45205091070040e08560041e001420f0800342403007900c2003213520200700c503220002015003030a80d80041c40801e0648000188055000342e0700020040741030750a03210b40e031081d411990b8202030b0710310807103050340c6402e081c030ba05000751030b035034010007100c0d0614600240d0480c0c42508608402841d1092100c1260032130300803042010b81c189001c11640d0703070040703040d00c009038214000c0111928054144001c900d54550048c48002040001503100004109403411030806038000d560740c0b442441d10510340c1e480082c0803400319107442c0b810038860419120381003da540c844445100307000024150401c8020282080350700280320700350364001030000308080e101081180c41d0940c5a86c02c200015146000190820b07040ba80704420140503a59101202e641198243c10005226124050b55000910030f03c140c0e0380d0044030342d8050108114171b651000111105a82d25900c030b080d0300801c11410748 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 623117832 1250 623116582 623116619
    0x70309031407020135040c17031c110714160608062422030b1605160201050909040507090b060c0a140c1c03031d19081611030106 57
    0x142516041d20144445500c2c03040001c0020060280c0f0060700320342140080501b141c044514400550082040c0e86159501907109544103000e10708243d120184005060020ba2411100b1a12a015107204400c070380d003120883d581041d51444a06100303140d89549440c0e009004501500070340b000556070b03200e156102d019400051029000c2d400106566000301d04075984d001d882581040b0303200000c568903019001102c41e400600310300e20300e141802004040002e024070304001e0082032400f00c80380d000e42150b010220185030851f402c9040e00040f9207034040e650b803aa0b0010100701c2032100384400001d0071b0048441200d01801151001c105001e480c1c0144c0e26000207640c0002d02400025803c191564a048003080071139540500f000006510b003108800d00840c0258100b640310f05140c0d05004010101c400b01c0c614011840d41090340301e40e1881148010600c04040001d0751040042890071200400d05402c1d07001680d00c000d01388060001000d83d00d1074031962a21030300080300d2250071810342c02c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 623119082 1250 623117832 623117837
    0x6090402030a0615050d060603260307110a0f060e0c010207060c060b04090206030f0a0f0504020114030a0e010606050406020f06040506072109060c0e0108060a050d060608060703090314070201 84
    0x180b10641c1d50b0100540401c009044050320b0355000460345840d000390340070143d0b0007000c01295107407640c01c0c901d100d086514158140d9080c0413091100b081c400307200b00c82d00038015292500350841e440840314104401460010418440450003105105003034002c907100c0003403a07082c0c5503405444030059a440c441c0e8070814020406101051000c030b125031b88030804c26100a0000308041c0f8151740012095030040364041c165507060b03810b01a03002d02504c04c8000006181030700704864107154001030038058011460340c12101c0004009a407141d4540c11031600900900005d100e0705844500c00741c95604075004940c014815594035010f01d280008115000d00d40010182420740c03643d0904681c00b0882003642101c1c844101804240348542d4442c2c249100d0042c0c0c40050018010301008000c43e465192240c10071040c081801401c1da60055203008652003290009a5001189425406894282e1000006015580410060f03e80641001003054842c1d581da04500d8420781682c0418060900080d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 623120332 1250 623119082 623119093
    0x50f030414250b0d020405030d03091e0803040602031504050a1b02011b08091c03020a09050f01120b1207182f0a09150e040b031908180a060c0b0609040203 68
    0xf0811498000c108415a80001525054480c00400c0c41e2440d04440e4100007613540070450b061000f14074400d013106000511290312019641c44400d01400080e0000d443d540d40040450902e14082e080156019009007003840a40f4116501400419010a0703e0602c541c02c500ca94515900c18480c3c8000280040c120001506400780c040710a08030083c0000805d00c5070b00e0b46500149462402c4151a1801c1d07900940d0310341140300f00800704685507110743d005100d4015201c81c641c2c1c002c00703040500350304510300040a454035000191084c18560f1001d195024615000c50b05002003010f01000b0007210105000c5103074850b610942140090a80282081c16820100702804080700148170407a15803070b0001c02c1c5519060801c1b1040e00c524030390004601d1501503003046080034090030b00c0035036086020700040040c4144100010101c1c0b45c0060035030000248004a44c0c0055421485400e406085e140d140c588808000c1c103481ea105030140c54802074100021128034025802174421355001d00540f4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 623121582 1250 623120332 623120339
    0x7140109090b0607050708060a060504090b061e10080a1803020d0c05070b032805060a031b0905070c052e0504210c06060e040819050f03041425 63
    0x1c004200a00401d40d000c80200509000b04004003d0803000e0110040940b105082800107130040f944180c3c01140601e08184a080c082000e03140b80035845541a100d41c026003104854600310071003100340250b485124a12814000c1da404081c0c5441000d880c001001215464000707402c207030000e008010016030014202c4030500e4811714500c040584500c0841d81075588440c011411504110340c58004220300004503440301a1402e6403090702c648420b010842801d0850100318800f20a01016140102d00000420350b0030042d4203500041588480c20011400c2c03041c001480d4408041042d04e0a128a001e0880c0303405920307614444039607820000945440802100d6400f400c0020070030b031600c3d8008a40c00980415030b1400445680003a0f49680d042c121501d060800c8401a400c04245172000804020014001d0300c00c94001c103440d80400c0075900e80185040f240c9204100451160142c00b109100c100100c10149411141054064400000e126100c0d8a0321545101410751140400c103800c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 623122832 1250 623121582 623121599
    0x30c0f07110a0e06100c030f111006060c030815031e0f01090309170c03060a1808040e0118050609040615050603161806090e1e090604030207140109 65
    0x1000d01a129071480d110740001980042c0c481e209907449261154086820072409203002204400748580c0d03814003426080c1d094400402405003481c0080910041680c0720101074000c000c01c900261842c0c2007403103820740b240002018030018550880c041660000450402d01140785030b80c240c140e020b0020006000114203111085441000c40d2105d801000c00320b0348030210038000d020020303001e44ca501c0d4a0f286054403007402d14011036504501031304034101c41100d95901240598000b140d03800d01250101104244088000820b14020a4110700241c002459107903c8200d50483e40340c1001403240404161044050729022036074154400b04000000380042e070154400400800070244125455888034041200340d40145c40401c0003640e5010740c181215130080d0f00307001c04540342903172025440c07070007038003400495250040075111031003140010004581c40a0140d8013450045d1940301c9410152003050311480709940c02d074018000d540000c100c4031000040300c8242103040c0c0d039600c455460100f41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 623124082 1250 623122832 623122837
    0x30203060f030607030b01080a02250215030a061d090c01080c091806040c090b07170f270901120b0901090206221a0f03070207030804060903030305010902030c0f 71
    0x241035200007481004401030700c04018452160a09881c001018180080090721480004140c1d02d106401000344015241c0618001c51082948018010100c1c03154800540c20380c1e80d05003c80801c0c039000c0b040000004081e0481c2048603144000e49845016080d8884429003003100e00d03440c960b0204041d103145500c5070181e036030b100600240703550030b01040f0000a9400684600c5d01101010401c080c0311003840d007407142441e00e4441d4100114494502188100c141c00b4080014102c014104070b901c0e4810221000ca44524a15940080e078403590480c15001040c42c80803421000240070040e40650b040ca103a603a4182d803624103010741c10036161b0f641c8095985006103800c06070354031042c0c45001a2100009400304c4081d0301d210220f003610449159104040c9070303000c00d511001d40c000c4101d4180e0568222511601040c1443e6a0781d80d0700c3c00b0507482c00503150700041984100050005a15074001425815207120b59024030099907645001010b030701003030b00c858442038006c010188184428a00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 623125332 1250 623124082 623124091
    0x4030c06120e070603020702010305010807051f12110406021b031207050c03060f0603060703090305030712140f07122901210f06060201380405240619030203 69
    0x2021907110b800e22038090825000c0d0707000c840402e0300420743e10210340e058051035024045280062000c1442d180010702e42410081c20280780c803075048213411803144501c000e0001c5204540052240c0300368400041d5096006120f6140107024030100e601c400e01c182034a001044000500401c1550391301400e5852540c4180000c550300e11502d2501d29854405001c481d101d840309a03080d0f803d500d081c0c070605042150040a0408161410200000094100041d04d402003003c0c948441c8150255800c40001c0008510070280f450840003040f08a03001030901d40c0c8160707a01e5803078075405040c0062000c25284191180341d184240203058400381d4032040d1706d14564032414581442d8041c1c6403023942514100100c2042030035074030b5a05d0a10034512074056480144101e200030004124940c00c01e4105c1084582c1100c3c12841c40281200110f1440d07404000d00107005004000c24244030100b40c54a51b0315402004c00c00c2c0d000450641d5a1500a003600c1c070142040203800b441c2404030400314002d5000a1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 623126582 1250 623125332 623125367
    0x90a0b1f020a0c150224010915030218041e030806091b040b0414010f0c020f041e0b030d09060503010308130f0e0405060a200309190b100b04030c06 65
    0x408410101e09440c02807030003880102500ca0f00c190304078100a0a0810009065485d900002c1b00c0fa007a0180034003036181125100c1000003103028607149452180c40c0d990380065880b052954516007241c3e0a00340c018040c0c0c1c81190440c045a006080c002c41c01c004100c0040c010030341c48400101a42040504941c0c4003207840b0307a4610800818442c40703d00e80090f049000b1b0300340045420b0150f415465a9052106400d00340f840440011107001403401c00e48050080c0030f21180c00d900c0c032050b2619000314801c41446900780e414a00c02c007440c60000c0402041e140e21a2042541c01340049000d050200107466240d5600b07031071607007180c40d800155800801500d500c5c8052040004015404504202c041d01d017083c0540c03440d080600b001340c90a1009401d46600034504071048460b4904000c07080c80070000003840d26183d40e240d000403810140140c0d104540200a01c0980e41001500340c0803901c1045158000c1200c0b6494044404440c02a17000c0100b4140c58030105000f4207002d00100000704101d80c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 623127832 1250 623126582 623126593
    0x6050a05010e03030405030604030c0614100630140612060403260f04060518100c020109021513060e010509010c300201110c0604030e01170c0702090a0b1f02 69
    0x81c404a071072305608607010f03000580704c0c1d0f910104204c11802407100c14901000140c0c8107042014a14103a844c07544503030001d12103114980c035900700d903c03540180e482e203003174019203855108a1114400740120040d680c404010744800100c0074030f41401602c260220b02d100400082c0d41c3c990b801d4807290b41c0090b2220203000c2c01c038105032080b03482c24940d034400c5100c4c64408240b400d1a103814003d46801910440803844501e000240da0180041d5801e5810071200d03002c00e0060311400240e00410114174044d41041000540b1030b04c00004c003009180d050217000301c03411241e40c1c0d003100f01d034040d8082543d04e00160f401c000310f900540c8940f80c050302490203000b181e000c6481c00c070410206500800c142d80100e00708800011b40c2c01d9020302c101e240c0b19409100d00b074580500e03d0305140c0c580000400080038003108190440b000e9100b003054484c441c2449899001c00c2c1403000c050a010380141104903c242d4280000990076600c6014030300c1400d41c06800b42211241b05640040e00c85006403040c42148205c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 623129082 1250 623127832 623127839
    0xc070501050405010c09080105070c1b170d02060606070803010306020a1b030206070318020306160504031703010302040b060403021309050115030f0b010519090b01050f0c1f06050a05010e030304 85
    0x81c0315550081d8400e0000280c01c864082d13028081c41d032940d000c0d8046914050130030031026007000d00f0010041d4800011484d14042d80c51041644840390080f2829510b20707a090300340300100051030428850b1030303001c4919641c4e4041c2007009604c503201004000030414001040003030155009040c000841c0e003072119104558265800121428420590043c1d0124062101041e0103100e05200c1025405140e6401e4203d9000b20f40c2d58200a4004e4100101da0845944202e101d01c0035034025540c4005908071243e800c1180e91890b0f002804181d01c00d03850701035042c80a00e4400201c2c0c0440f5405040b52181d010719101e00002805994030646030355484511080003805a104044051441905082d4002600b42000311010034140c04c4140206243d02c408007803100f07114407400454440c030380041404542140100c60703034000c030718000b031503d000850b00740e01e40384002c50302c400032240c151b00c000c40101e211030b508001d580b9103218080d005000304c0d1041c00294402c020340c1c0c4800c84041c1c00c4905d4181d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 623130332 1250 623129082 623129093
    0x1005100c0f240509030a0c0f0c05030a031d030115170a150618020906042106020703080601030c0f2718060501021501030c1202030a0b1005040f02041203080c07 70
    0x5a03081610310604038150142c8240e0400d204254014034650025810050280c0020380164090440581102c0100c0014401c0150251000010f003001606490b03403580d4a1030050080404442c0c890048d00200c000d422050070148a40f18240c40201d40105410f0700e01011b407180d49070200c0c0d41310840c0c0501c040c6400407881ca0a040c01e040b42e8000720000d030040c0741030500c0e00c040c400180f007134807111300400a0500c20303520171027980c1c241c50b040bd08508940b045044a8003251007984070062003e400861424203050704110414030903503003a01d041c080700080800840b0181c41c2e01062a0104040c3c6442c00411501a400b48000f08000074031021040d4840da106104040783d10f0b090a4440d440c1d260502544d64180249201402e80034248001541182e64880301c1d55268001c40824410182c0c550055503420030032006065002240d0504038104114246800002401014052418540c40e541d21100740c0c03003103a088920b40b1380316801100c004d9400300c441c03610243c480b20514605100c414003190 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 623131582 1250 623130332 623130353
    0x6010501030c0210240603050c03041205190c0b07020a0c0905060d050102160620180d020d0302210c07051002030c032d031905090f0d171005100c0f 65
    0xf900f040c2d003121a420904540c5e0062580c981002c1c04243c181818080014041d00549400c0342c1d001c04620701465608800700c80c1c9004244404040c5a69640c620403159000411305403014051008001e090317982c440107a94848800f0001421041c900204004c001000c0d030181750031142c02028070b1074010058440301e082e0380000035607a038003201c1313410f00303030108481441082c540c1c407295650ba60417145103005034050340c0201070780c1d008240d03094230041102ea5941c0301d00d50403042e8000c2c0700303000000d03440c10020742d00d0303201c0b14084001000701c426010300c04542109441c154408403004090082c107020070f00040b0183e9108032020351000344500c03080d5804c14005000f525a1001d1900a03030b01030421031648003030102990012200d02001070106024102102e8040e10821070f20104543c4c072104502031030314180301c0310206103011320265a103465500c0166904039608118080c0da0988035258208021100344c410140c2c0031004c0690b02529900a0304140c0419000d454a84404c5509031100948617 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 623132832 1250 623131582 623131601
    0x13170a05120105040b03100c050405060304060f0c020613021e04050c0309011104140409020a17031b0303060f0907050409021603110706080a1d0a290906010501030c0210 74
    0x52000c01c110351020656400640100000c5500b4484540c2000100b9221402400f02d0742c9020380310f0070180c290324014000c9400400020340260f586e0300c3c0c542040d03030003840503105100d00241800070b405015413001580c940103003e07411040c00031403026070130410300d51481c04288008000c0c1c15039088083e910b9209042c4148070020606580f03103000303003000742100d05010310404840404c2c001840003400752480c000042006a03000151b09941b03000080d204001a4001300040d2140c00240241d0b4030040060240c9045c4c0707080c1d41c0740d400064542c1d15181d0004581041d04440400304411103843d004540310f4100030340e8180a842d1540b510031000580c0d2100d501c6000c3c44000d48010700415501103c3c80c410101c1e444050060f041c28101d00501c0242c000c1d0215003e991214030421303244500b520729400b124140307404c440c82d042c0c0624228000544181c00c1009680c00080d141c481d000c40c080c402d42c0304243d8000074156030303030800d0019002413102000c4041103100300d00d65840170b415640700c1c00016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 623134082 1250 623132832 623132837
    0x20102120a0522080d051602040c11070f05060f0703180f0f050103022a0c1201050708061009091e14100611060a021605030315131413170a 61
    0x10703181c008198946800d044001421042000f101c01c03c061080800c03848030351421440d085640f56400660740120000460000e94030a14000a211845400020f44040c408441080c1c54140b42d55441049404603684581c0b6000f0904106000e01209510300074580644241440a6151079114401d14001c0c1d807500704a03234002c4105014400c60412a082000a0009280c01c1d803416044070b580c40c03224084544401c1c1c809401c90aa007480e0f00083c090300340c0900003e4403a28000d41c003001c00341d000e00015a05040802c2070003000c0703034083c145a203500403207040c80c0d154116401e02d4200f00344000c0198035809801c1e0140c82800201e1500540079140c90729038103c010000508000348448c0300c1494690003142400450714802544000118000354400000500140c036109620b40300340684490810081060100004001c2d801c015a181455070800035558006800e24034000ba0084680c0f00e88000e41d20010346d000642030f10b001c0e00115001500c80e0741040360720802407900a801e41c0003075188001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 623135332 1250 623134082 623134087
    0x1905031c0203041106030631141006112112041109060316170102070506010b04090b091326030a1e0902061b07080607120b01020c06090409020102120a05 67
    0x2407101c0026030354040b0351304883c0703107245003462400148002520300b080780c24042c1c0b000c0c04c510032000c1d005034100700c0a4803a009024640144984010f400e030300301c54a8128075090b0300d022880c14428404006d04a003541c004003807490055810065850401c6841c499401d0b00b000b51078a480c0b422800039014a1207804644030850f1741900b04203102c80c2c014005802680640351120003003404145050440700c0d880c10542078004030b0055113004e0303c588031001e0903038400e84c0000201d03c1480e07c0240212402400c0030450200c1200c02c1000e030b05400d5641c1c403c500f2403005180d002c10030312040505c1c55100c0303000010441407142c9810707280e5001150103070946030342c1d4003582510f1440010300003484d00410340c003045558070f6a8001713840d90007800c9000381028004040c100d032245d4100480b401404900c0c00726900d5250409000b40f1001810502108017800d18461140a50000448182400004005500b8480c904050200410400c10706030704600c20100c40d076071121a03403001408000b004e81d40d42c0d40d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 623136582 1250 623135332 623135341
    0x4030c0e07030e030a0c020303070501061725091805070905100812040e0702150c090a0608070903060b0609130f0e03030c0d05070c05060906190209031905031c0203 72
    0x14400e0003003601c0281828803000348003080001c03086030300c03a003180c2c105950b20701d00d90300121340b030750058600c000c09644ca401c1011130b0542a01030368450030602441110031007020101c100225045540120003408008141844400d020341c0024a902c0d0610101410604030754503001e01d080380c0d550014085aa0700d0341840030300c5400010410180903100b0041450380d1072003108103418401c40c03003820705406200002c940c2c128400e000c010360003520902c4074070160801c0301c4100d042c1e03032042c03241ca449000114400103031580181701e0300c1d00c100034548603101c01d1032850702d0307031000741601800056101004005005850751000c880301d4006c6001e240c005031300540c121000088403100c070800129540148100071640d426002100c8140b4251003010829807980c1c00e06841840d081c1500070b25038003a03481000400c03080025043c2c41203803940c501031101300f0003c01d0071080307100702c0e90301e00e405820020020403410030302015041685d1141c0c0803a450904443c040c07141256503401c114030095000814007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 623137832 1250 623136582 623136599
    0xd1203060f030510021e040303020f0d080906061003150b180a030c03031b02150c070501080919050717030705060f0709171e010605091305070b0d090804030c 69
    0x10301822034900c1c100c10700319201c0c903580380030612400951a030001030008040301441180045d440c54059019200c07920b03440e000c0e4031045519003c020610803018503032011842a82c10b03034003039641c00c1c014180c10303110401401a501c4a0601810038942c4660031040d50150308101f00b001081c1c20a075031519010102075000c9010b01c1c41a10921450b5000c0c024000728070400c121a040781e9142c1092044180c280f000c40001c2407038414080d60201000ca100002500700b280203040c026107150544103031907124801074424103001e03252804503500c080345841074980e40866008a250040303049403c903d6444580f008e044045851140e242d82002c50a20108007041144941049400750b10240a25041c02d0040ca20912889004d0401050344003408003024244880148000007071421100c06029030052800380c00c441c071804c3d000740810000512003031072002400302d4641c1d00c81c001e416111b1030041c407a01150040c0c002c1505141da01e00740440080c001d200140300030b511801e00003401900d0820341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 623139082 1250 623137832 623137841
    0x5030c040606080f09010605061201050405330a051002210a0c060b1c060b030c0108010e1f0b0703180b09010c03030e0102040b0d1b0212030609070e0d1203 68
    0x2240c0c000d9081610900045811095403544800108644001951505ca0b16800f600c03441c1c0c030041e040040000c501203a240c0c0303450382605071081600c052010343c84440002c4000e00032900901d5090aa038484002e00708046500e20340700d41001031100c0d0b001c1b5158000210380140040c8070700096400784001900b0103241d110b51040110941512504102c80d43c0c4c0e015148042401c1c008050943da03040b080040c2d43c884207401c4103280c580c19040c0141d0314516080d4010540c01d032450b442481125503281d010740c03107030307000d103041e1107038111100d00c10b0b250f07400060b16600d1410a140d003900c0b08c0c00c9010455049040103450400e000c0d0340e911040d1694100840a242d210350400071410004003c0d264059802c04003440d07620742d151070000740800034800c400740240240d4100b8403088a000550040d03a8034030745c025032083d036100512070406411113413040c2e0340c07444015402c4e00a100148001102460540401d036401209810080a80403020000400d2801015001c40300e95201980d9034442c1c9a05128 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 623140332 1250 623139082 623139103
    0x109060e09031c150b192705150c0d020f10060b04090b220207120804020d0f05120c01060f0603050f040b091002030702010c081005151e120403170610030f091b0503 72
    0x80760031110002e8142052071440070b001d910f029103041410410403000027011500e149441405031a510744104500944402c040910f880c3d061203007800f6140e81c24001d100b41130440c0d15925410b03141902d0042894090800360381c0480d071000c3d4023140c20070134404084200d07800480d668001640d4000500d401803261341841888001c00101804200060301c500c402600640d070003155174002c02145250140c0351011200c2130b00072500f0082180e4070304440540065040e12964103501501a45594003281224030403103510201d0f44400c004070300490b100c41440c5030840c2041041d1282e080c81c6000340750a82e401582c400d00140c0d03442010705c90070703035000000c550010483c80380040210b20f49400510200050b40f440054a00001409120b401d8400105158103805540107910340d0300c4608400e5074094100c409401190303444100440c9245405901c0d48a050020a150313080d480c0d4841c120002c120242c005c821180d51013041601050700c030700d07125500c05054070561012a05202c14141000032007031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 623141582 1250 623140332 623140367
    0x4080a1203180c0b0705070504110913020c0a1b080313050306130b0a02160f0302030a1119080901030b0411090102010c0305090c010f170109060e09031c150b19 70
    0xc903030b5000205060b040b101110300ca402041d407645010704040b0b0500751142d110683c490324003038000312485100000b81c810400304940016400d110001c04006a1207002c20072803442d00401240340001e50b0380c0601d136081c1d90402861310301643c0c607070351072a1540d4030001ca07181e0010556a41042549000c0294a50100700d040c000f8005464554035600c1e1a003003d80103000040d00070074460389a0084145441400d40c00c07082d180622076450802035143d0348034195000004902c103480c1c521205001500840c20800881c4160440383d182d1108207040d04008034660401d622844443c000c1d544078040c80c004081554102591090f0601c00a800c507005117254406260a20041041031503000c1414030104e6020300701440380c0c1840840071101d41414029141c6201e007480d0001c91f1700080c99000030705890111500c0242038640611140c0d80c1c1c0590644001b0884c881c42c408c0c04044156081032128440d4070001000b5103071950300c0400d40d07801443c0d0301810020140180c2c02d185912010b040f08100221 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 623142832 1250 623141582 623141621
    0x9190e1b10090b0d0b06160b011502030a030c09050301152102010507120311030a0c031404080703030f0b030109050610060809070e091c03410c04080a1203 68
    0x1a0000b4085031814400e1950710440440c4e40c1c400c4000c0b0307400c10701c0c00a00003401107580d5100201003643c203813483c007016a00055190004035554082c1c416000342240c5c1900214207004208404802808005a07144100b01216000040644013405402c0e4021403400c1440451410700000154101c005142c0d44c5240c40f540034180050b0b60854112103510b41c101d4195031840b01c034044160003038030024000c01420303400002084600e1401d070344085104480ca540a0201e0698030031111510802500c6c00350551000b00075000000e0302983c0110035001a180f00450104140000a0b084540c0614161000d420210400000c80900c0b08400d004c4e0079141007080541c101001300c542d40d44a40d0042e520f82030444004289800b4041000c0075603112292848555100501e8004000d48a40c0030100c068900c15100340b201c0d40040400c1410b20a407210081d14000840840310543c68809010140030141c20400400d404005002150655016004141aa05001c01c00508072121780d500180100c215 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 623144082 1250 623142832 623142859
    0xc1002040b0403021905150309060c040501142101150908120415050708040b070b0f040206091c15060e100b180117090f0f07030b040209190e1b 63
    0x9030001c1c0e8090700d4040c1c981d540a100448001020b00403a501b113958004030102080803940181002503108500160039212a621494412a814080c41c059240451000000000704401e110064141131186404a00d280b859141d402c1080344800c2c2c1051558903040f080e007a112a4000303148400500b0f10000030103692104030b2031800b00e40114003a003210044080031504050b84108150784095400034181c9588584d40c288205256015560480f01038444c0d0001540712414500c49a2159401a04640c07800e440c90b8200a8202e29807414044184101c2030000041010702c40180014800e010000030340500744421755004a03001401c140d0103850401c0300340880411442a03c44550103a20014816240781c001615082da03018984500c50b0420700402000800014520a11040c00e0050760030120b10a00ba042d1250514000500412820340104005007014420581d10102d11200402c1c8080142e0115081e035400071203950315940b1a0410085110803a000712260800c100d5803900500364 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 623145332 1250 623144082 623144099
    0x109061107090c05040806011409090105100308210c030106020c1005040b1315031a0d0b0103230f060613091e02150c0106180606231209030c100204 65
    0x12207010320340c40c2d251164000f88005000c0c2058501500c2c44070240d891668481e802c1c19042d03003451704c0d018410b0a0000118540c000107102c3d003402400102d85a0700d586007103444545241e4000c000b092207040760014080c0e003090304002c260740151050140d1076501e525100c002440c1c11100e031001e6110300d1461110740400381d00041180c04841d00041c00c1c1d51960358218074500b00b0035191b4418007418041d50082403c5950507032010200c0350308800e800d10b4442c01c0c58148584680f01800003013404007014010710126a00380000039046117060b01c40a05a030f44100c003142045082d501200044c0d1080301030040740d25009104504180c2e080781e0410000440751110580c203040e841c8041d48c0112010ba9260542d2a0a000351030002e028248096540c96043d0903070340200034520450403040b07409130740d4900c481e106006038800c0700d521340e40d06000030020040d24412002001e1450300200c40800c02c10700781080c0e0840f824450803480005e56119400761103441d062a045003000c0e51041c3c4100b20034400101c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 623146582 1250 623145332 623145343
    0x5060a05190507090b030115110705010e040213170604050d1e0e01020a06020315010e100503043503040605070305010302010f0e030f3702030c0402070213061401090611 74
    0xa22046002c100c64031004800d66013044650814002c20000000101d412390b102c14020303030301305259075902101c698002043e98030740805000d801c0c00a80e082d291007000746403d0b00500301c40c86c44440e012006582c0e41050b01c0e04120740003040099a0410320801c001e0090602c41e00c05244070905001001a40300c050a4421410040c010414020180100482070740308003c2c400c0c0c0503a01490456803030404c8400381c080d82900c411010b00040c5c01050158507403c110010b01d8001b081d940700c017030841e100e5a96110030a2042c0c11640b18001302e01083c074003105284102012224803161003184c1e01d00b40750801c00300307a0700000c180d41e0505050500400050b640042ea20500c290030f40303440ea20b011100b00000341000c8058211a10034800d080c0c980300850313200210f51884c0344486a030912084109030602c80c2c84014100c01a506030440064050f641c01d080e0020f084c0180300401041d10b084000102104030b0703007550456a101d5486001c80c0c44a560004404009401e25007041c0010a2504078a1603480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 623147832 1250 623146582 623146621
    0x2406260103081b0a200307030f1403220911070b04030305131b0501080702060f1f0801050915130f1104060f0b0915030708060d020319060905060a05 65
    0x10500000d091154507405900b16a40d034100d4000e80e5030010841c01c0c62000c10035030385e120381c1030200301040306599071500050300d0342140e5000390360710440590360f26101e1107060794a85000940c0030030001902c0c02800403503e0ba182580c0000203581c001d0034207852008803481c60580c0b5148410801080c40450741d24019180e00c99490301d001b061566540507801c2507803210880040050341e06050108100c03c81020007002d80d1402e0740c55901a0b500c502040f43d13606010350301c14841c2381510b40400c080e116500b0240c0b0508805660109441f03607030300141821120126409007a54201580c180c4400d00507000349508a042003600c000000f00175101d0341e0798648401e01c01070040700f05008030584c0751075a40144c002810303070303100a000180d961640c1c5200c59000c00d8445100f240c00c17400a540060b0720034166400380ca403503600d820050791100c052044250b8040d4042c2e03030521500d009800704048a15000c000a031080d000450381141c1c91034010702e400c201a1a0540d81c0f0301300380400140f03440500da44685c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 623149082 1250 623147832 623147843
    0xf050a0b12060102030f04080106050411160f050c0a06020d0e04020a0203090f0a0f17010c0507031403040201030e0f0106050f0f36070305090f01051005132406260103 73
    0x860b21a140181d207540b1810545265480001c1000544c030501980014110340c801c0d5418415100c3e12a00148c9602c42c0c400c81044504c03d01803d0004650400782034044144580d0845211000e807030001000c03816264400342c0140c0c01000c210550680c0001b811b245081d050b0b6082d41061085140a91a80140d00c042c60041540042e03654481d030390340d5068801418141c5008040310b44034a54130040644803a48609a507003807441c066801d610a004075030002c2e4059581101c100800201c8100903400038005030304041c0c580d01d801090440a00c40350148030b002100000b11a450241404654445003080920400098100d1030ad103465251503801401c0d0b01c2e550b0b00c29000c1381c2540e00da042814010f00184600e1441040004041c1c246c1c0c8414040c0b44140c0445464081c40c101160a90f1000c94801034209204801089039042c13000d0307000358400f0b895402082421031002c10f4501d0300c0c2581d100d070a01c48074000742044004e400114400c0d21034507c0003005e440c04070106500f420300d40d06100003401c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 623150332 1250 623149082 623149117
    0x70608011401120f020a021b0604050d0f0507080c0a0b030f010e090f0604080706140610200109080a17012103030f290a06020a0b091c03060f050a0b 65
    0x101603100d0400c0f45480035140404001d0302c0900c100c01c00081d00040941c01c0980314050b05079100d1804056007190a0000034441c502d00307801c0400f0b11a5823100c0c2c1c0c3c4101e8a60b00d40503c1e40000038414040c0c5000340c003a5030020840540e42900f0080c00c04110381c8016003030281041880190341c4107807400d90556521181001c0395031101281e01c4d15282800f13031001c2141c0200002d001c2041140e000071300070203020300000e01a040c0249004401b00100307a030b50031b80c4081ca400e0040b0000380a00c146c5c1c03240030f0440d50502e80f1303540300706412800d40d441d80d00201e4000e00700150b89030326580c00c80c52024690782c02c10f4140150790304000e12030300a4503160078240c1c42011240c003210b0070540719800c081d60305260007a05001c0c112000d51249410710f902c0c024002101c08840c500c20060504026050072104940c4c0242a0300f04151603100c1c142e20040e1140e681805158810f012440e29458080c040c4140c07035600240551907c1600c100100c0c680d0002d91150107085002c224181018099032481880c0084251 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 623151582 1250 623150332 623150369
    0x10b0703050d05070e18010f0506251b030602120c09030a03230c100c1b0b0a020f0403050d0f03060e040201051308070603060e0c041d07020c04050f0106020d0207060801 74
    0xd461541714803056a105100c2e1000d400300c8a0403001e00c6040b10705912592620076100c00c01c21040b0f0250142c0b010f0100c0032828041894401c14a9000c4014090030000c54a4043c0048034030700b0b40c402c1d410035140c035900003c50064061401138115440540200d0307050605425400107611220b120501500b040140b003a1070188042100c01030ba200444085059a9103101480c038a450700d00503404101903501d09442c601c003407070082d4004496901000e0820030207032505d95895401d244050b1415400301c2d400c0c825407510000c160000d2002e9070150300106404c03031402e64000c01b002410500441010708051041007120564281c540d002542401d0064032010303142000d440324180b6a000b50030300e00c61050001360341509540002c00b0344080318440569a691841004082d206500c60b805850030801034400e48940c24515040e00003001e0f01c10360b6051906100001d09075641541c0035001c0c0b020580c0100710054041048105000c0b141c0060b080c62442c240001d4407041c01440350207190200d10f007100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 623152832 1250 623151582 623151587
    0xf110304080d081b04171002030f01081908030a090807150b09010902090105030f041b0e060102010c1e0c14060106050319050402011e020c090a05070e031c1407210206010b0703050d0507 81
    0xf400747c1d01e408411910b0340782100b06d242240d8001e100b501c4042c019800d44030080900c3c20181c2003411f400032586031035512460080801000c20f04400c1d11201030902c280c1e4000b501c0540320444d6222049004507505185504000c5415010fa0008000510412032000070343d1700981034a903c411035100400c0255590b0400c0e210701507a40c02401500c00c1d0b451004281491000c0e10180180c200f07034001c00100315210f030140d542d41000c0408501000380d0003465607905c0d20481035400c40501c0380b40f040d0401c207910308032249004d90a030003036008104040100100c0401c1c03000ca03d09c0080d103215043c042410560000303010050b051240228041a85a0003040700d8020030268a8108000d412013103241383c00301144001b090103954030740020301c20134406180703880c0004507801e00c803040b11030900d68000301081c107a6000d10300001310315503c0f82c01d000c0c04001c11303180d642400c5540311002c1c0350340c0400c2c1e40890017410300005030003410301c2443c2404003c01003940035040c1c3e0b8aa400b0041d000030240c803084001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 623154082 1250 623152832 623152843
    0x5010e010b0414011b060e0f280b040c0e180c0a0b03060f150708070c0801050606160510060605182407020402072a06020d0f0f110304080d081b0417 65
    0x54440b0b0304001051f03004910000da10031a4011540690700c400b084100800d120b0380c0900300c03a59889070414081d90103d4044d178000340d0081d20a4668070842030303803926a6010103200b2a800804e51481c202800303c1600c041c4222500c2c0082112401c50160800c0c07132421450001410781401820324084446454444002d0042d4038400d00c40c040351155464542071000e64040c4004035404c5140704000034844105005960051600070303c45810706c0e0442c07a0380c1d018410b1000301914144540c00c034030030b040140b03031145101a0800d0f80d5096500e10b00103821100701c3c0c541c4041c280c0146001009001c0080c1c102910030fa40c515000c140710303520300702c500010300030740604400541140c4182c996141c4600610110b0800c01c4c60b05110300c1c1803641d55103070691b21400508009004074128000501d1101d00c1660040e80c030025505000b0441d811a204451954026800591071940500350b20b4213200d81284610364880510254040c1c00e100d501d1112020380203902c6400d09404136013101c00e904110a110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 623155332 1250 623154082 623154137
    0x40b0115021f0f0902060f0702040609050c0702060d0603061a010809060903190e040c2d080403050d14040302011a150703080712020d14090607170606040b04030605010e010b041401 79
    0x30700c6484411f5031402104c964440b00d01203105c0c0c0e180040009004540f07000c0e080c07203101440000d0342070483d0f0390240906070748030f144601d40c0c40e681c0b070703d01200103255840b8025a080629121040b08a0180c001512400014207804100e60040c800c00032041c80000440310940c0040307501c0200780162140980340501c0b4030061a41c40b070706000c107101140f030380100c0c800301000029015400c0c2030b580c071311354a00843d40016007134002150140020040f070b000e9001003110030710b40000040c80c060704001440e03c0d04801d540460050751600389071700c0ca80115012316100e0703d00c00c4610a5403c0c1007419000080d200d051001000d11400d0000500d0050140c403a07100340361303400c101c15035580041140c03500091030302d80c0481c0950000900412043c0b48001503580c0b0a0100c0d807180000925540310300d4042e14001480b030740c1d100004010214281e10300310060301c000c52217a100424654140135090100910507003016980702028801080003800701030303083d0f10f42102820203180108041c07042d20b01e00b030345829 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 623156582 1250 623155332 623155339
    0x71203031d0d20030f0a031103070c020405100e090a050601050415050411040512240613090c1e030c143a0311150c1b15040b0115021f0f0902 62
    0x248030503450250200500f8620703081e6400300312062341c41158002ca800b044e900a000a080e441584c40181490341c04103401c00400f18031008a9541c1d0314502c84403100882c3c02c0c07480760300034102c00000c1010412986000d030604031801d2020080703283e00c10418802ea8401c1500c2903403509a00310101c68450304070303002f408014100700510408990a90340c0e0710300390b1440710030006841d41160344a901c8003680c21300903000244001000c10f240d00282014002e04035060300c0749600984001080280d02c1039084d50221206450592141303581844051403851740e211804030480e102015140d680c402c0010418440700030500d4498006040456440040034001d03001c2826450030814103054003c09407540e1b0001d5a022a18050143c0160303195107802941c4d44c03000300f201031040c101441000c4904560011403a01280c490f104241c1085011000554041e1400b02201005215490328403000e443d500f590350004003490408144415080341443c10b10302e5034550740798a0302502d20829006000c60a4004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 623157832 1250 623156582 623156587
    0x90409061104030b0c0405060306120708031b010501090b010e06070519080c060a0903120b0f06070b01080706110303070c08090301050108070801061703180111071203031d0d2003 78
    0x20381c1a03500354002c0c001501c1c8200c0c00c0c070004d00303c16004802c4400791403002d4250341c10368072800140100c0e01c401c108500c0c424010404046103084c8104094540200047d014035584030000f4950382c210352040c0c0148010500344014a09140d8100040300c01105050b98403950354070160030f10760b040c031224241300402d8405445940c400d01a849001e400c40012420941c0c0054507580154811203100440040200d0509102404901c403e948980021700001d0446185140c82c50b001651544c41002c040390b17011031601c018820303a6010007030791000e090f041c00d044180d5054540b0381075580c04001c1c201d804001c00400c1c0703d0100030341c040a55034844000350007440315503120544592101d4840c0280702c030701d44c60450300103140c51060700074900c1991400c0186182a003600c0d80c405004101040460600044006070904010204194401840300c24805032040078035160040c03d80d04840030100c0042d51603459101c1012020810758035548460508112400d220420302c00003040c032140740c0b43c503800007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 623159082 1250 623157832 623157851
    0x706030203040201030e0c0f270414010e0a03091823060f06040b0d0b010207080703030c0203010c03020c1f0f0c080108071203080a050601030204030f030e1e01020c0609040906 77
    0x190003460040d0301c05d890900c559150ba1050f20b507140540b0403180da014600b840101d20604040410741040100c0c02d80000d081603024114680641d002e42d412910541810b41d161501d06081c850100c003450800080c08218a56403802894004680a41d061501e66591032023181d0405601c0303040e0641c031400d5032000c582c0d008501d0840406041b40c60900440c203414503092685072910032202521048400c0c0e03818154030762084c0d40240034a0248605500c03171003102080d422010848100103602c81d82d43c000c054802403050609407010005103506060040c00448001000400c1c2000851186c0003820800c0c0382030810400074101907003d0030400c61800c042880410703400000035060350a9002150f4006a46020000c1110010307480580056502c1001c034062100a8000300d410900c145005401c0644075102c8148070b801500e0f0807404240c0c5c200c400c260b2801c00313418404110a41d50360341010380c245d490011f502c1d01c0a0b28001c9100d0000001c00360740079600e6503c0400303a00c0c1c00410422441c0d90 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 623160332 1250 623159082 623159087
    0x80a081c1103160302190e120f0303090106060207050607030e01090905100509090f0a0308090a0b011d1e1303030207080a0f0809010218060721081602010b03030a0e0a080706 76
    0x105032080202030691059020f1081d020707000b154010444441c501346000f941c8001100d0f03081c400c21038107503c111446d40b5449581410021060150000e10185a480c01d01030700359800c4982e02d5000700155003055200300b00310340d643e800f0703240c1450301b50070140000b00b181c100484070304009402c840c2d820340ca45005d103d407200c800c880c0d240942c0e0055030682040d4840f070301596a07400311404248003a5100c402c4080000e4440c41c0c0c0c5540042d6100102c1d001c80c0030031390310046810b400741c00092050b0407090884c100c1d1075046820703d0700042c40e5851201d4118271003c1202e4240002810007010710300a4600c8402c051096048610740c036000b1408a071508032040b4010702d40d03e03401410100040c01c0c1d101250440350107108a50026105101d000d0b1103d00da00c042c81a103030401e91043e50740715000c828464682190160b160500040c540d0b40c6030040c07909540300d000c0d25140c0c0c03208500316807500010385c003c2d84001003190385090440c142031102c3d0303001900203148102a074112100e580100000010b00a8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 623161582 1250 623160332 623160337
    0x60602101e050709210c0302060927061c03020604080f07060f0c200a1e050f0d020f1501090b121603061b0e210a030203130b04080a081c11 61
    0x39012101c0b000010b000043d5110001707a5400c01404100c0100030800062400000034050042c0150005001c603001e0268410008944540a240c9501107010407480d4505462164900140000e0400a007595a20001c1d91100010300080070079200103451403003420a00d050b5050f0316405501440590f155507212000342144040c05008941c40b6103d4602911050841c544842e07d00c070018806090350b03483d108150051401009041c0035112403070004182e0902c403034580c024200c8002c10780725241001c001e00d411f1000d082da1109070004516181201011144641110660307900414031034480400903500425500901c92544105040d90010b80d1800005030300312b0380509020042c03925171809003100103050718118000102c040007240400d144c0303e132074450668901031384002c0703401101c10703c24070300400d9070010340241c1e001080303507991070001a5404000e480d19801ea2814289031001440e0748000010004000f10400304140d03521b4000b2542e40d01c1391408000c014000155601d00d00c80c030300d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 623162832 1250 623161582 623161589
    0x10051333021b07030f030c020109090905160608190b030309061b0c0d0c060c060b0a08030403062f0f120c030105040f05060a120203070512011e060602101e050709 71
    0x203400c0861102c585507002c03e4080449070070244042c0c480c18603503022207a0356000c0310100e043c01500200402c9202d100e114100000f84108000c125101188012500c1002c0690018082106a20403c0f040102c007042e14400da8807441004a0401808030000303046010b5481c0b9203401c1003020400351586061100e110340681c004809032100040d4503801e209104190440c09400f40002080400007184100c00c181c60039802820009400703006030000a004407070320b90100c2c025510224080c02444801c0c80b6100314418144450074105902ca0329200001c0c06080344102c00c20385c0802c904000c001001c04550440700e480c81802500d02d40600407200e0f6400030b00502e40035601d005080c031501c00362442464003070203004140301c40c11840c22400c80000080d0907000c0f44c142c001c0034000140c0d5200c48182e5040072114400214510503401240c01c0729150003ca8042c007107080150030002c10f90042107400b81c5440d4064040b982e07030703003042400000c074110002d0044068a820204003107a40e000c0d030a0420b8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 623164082 1250 623162832 623162857
    0x4030b041208010b030f18010b041a280b0c031210030b0f040b1605070209040605071413180b12161422060b1b1005133302 54
    0x1c0c2d8a45135548003d010885010062800400c0450070b02d802d250090b000081544002050f020901d1000c2016240c814040039074440d042c4000101ca440d2082d8450071002c08400d001c0754000d1000941d000d5030301c561064600802c00040e42205001d0180120340c50f2908040901ca00c0e410005000140c1070301ca4841682c1840400000c581003424010400e8050b03074011f010310900d0380361171500c0000440c00781c100206114080145000580320b242c4441d1160340500c82c0094545005007002e850040c5400304000401d200308109540f50110704481c800303492501c00d5080c810040784149500610154022991043d5961084000c001000542c901c0c1036500a039061186691034130382000500098090540c0001d510b0034010041040b09080d454242c078134040440c3e804c0d950a2854403e9018802c8208060354961004036098004c0140a0201403104020003041c54003d0081100d0340892000500400c0d00d220004070080403515048220947c40c120b07020b0000d03040810b10002d41c82441d03c0e210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 623165332 1250 623164082 623164097
    0x314030c06180c10050d0606030522080f031905040b0405012412212c091302040b040204090c08130201090b0d0609090606080f1b0d03020304030b0412 66
    0x1152468049096214095034000f00b41c0551143d0411000d018105000001c0000c01e03c5400e070590700070300629004000710703103000410741047c681d000c4800b05200400c014a0703ca20354654005100c0340100c0b001884980e0140b9101d4440a194040b4184003190800c0014104410f1100748031200300e207239000328440c400030003070249241501801c0f1003480b11240e84010705c0f642d08220130b003402107540c40107a11501a00c0144070b20582c0c480b408071605140c200c0003440c102c900d44205c108a000385018000018098102d44041c58002a1031000050807194a111260b41900441d11103030460240032034018402c2d500c42d91500d21000040504050101c0011202c2d0082580c035884c07110010744860701a0340b0410414101107003607110341d02a00004003515500c4200141802440c0724203060b01d4030544c000f040003403070200d0a0b8908881038840c0f00044d080400003000845160301b07141c1e6207000580302290000407504042c1c0c15801258009444103400e00104020003020403825550650340e0f440b4001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 623166582 1250 623165332 623165341
    0x501090b0d02031209010201020c06040c0503160b1801030e0f2104030c0b0c0f010501030b07031127030c060d0203041a090303040f140a031e1d0d0c0314030c06 70
    0x2401c48a80003001c0d4041e0000008000f8443c85a0000d00c0c0307204060001600d00546642c20070720b07040007154295041e0301100414010b600c1d050203000f10b145800e4862801130390034444042c44c02c0c80303181c0d01d800984003680c0c00704210b640245c02002d500003501054429000844d410151a10a41c0c44040030052401a4141030200018103540070b4039000341e061203902c5c1c10540c4110349a0302101d104825172003902c0310105030100c00d000d554043c41c4101100c0f52241003080006d070640303040b0036202c00c490800340008581882284000160b01c82c0244810000e180710b50042810440030041d010740080c00092401e0b4480d420380c0085014520910120001907400d9030030ba0b901c80000c1d01e01c2c01c42030300104003040204425410084c2d0b284e0103403000107194002d00034624a04001a1411008034002c03011802c18114906140030303241d8103900342429107a140040c9011a50b28010303c0d10b104400710360b03804050010300140314018507880902d200c88904c0400100e03031350b9001032204403014811540002c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 623167832 1250 623166582 623166589
    0x11e200304030302150411090118110406171801020c0a020a05061603030e120d05092512111207031401140a0c0c061806060f1a0d15090501090b 63
    0x1d41c1100e425501420300300119040100340c220000c0c005a48410b00b0910300c010543e40e2030b45075402450400321114004040e81003150031b694040c072011171a00d000748010041d00341c1002d411010101c1c03841c07419203140c2d134202042e007a8a04414217840c8640c40410030b0541c403040052569507182c000c44078403000d04d9940d070400c14903101c4e0408502d0315956001c10440000d003c1e0300203541e0040c0c80c0e001d4421205180e40d020344190004600203100913126428000112810b01c00e480d00021040c0ca80007001c808a607040c150b060407440f8050403a0240021002070044a0420100030800101200701104160201507644c2000740001c0e2094600c441c400034418405115800980405207000c0703079103680340b441d03050050400350b011000313028450342e01302d00280c041e102e803c04286e04085581c681c0d1001c0d042080c2240d031a84c10212860040001c1442800c000040c0d1416580b0815071407590f41c041c003049100540b9202c81c0c0717403002130707520361020501c0c10305500080d042e207907404e208105960140040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 623169082 1250 623167832 623167837
    0x230709060809070b0a180b030703060501030b0301093206070509130c0206070f03090507060302030915040f060c020a240c0509012016080105041208070518011e2003 72
    0x713401003001c0070840743c94490b0103400341e4074180c1c1040c01e10614450741c0740d1401505074412195040040e40d200303028020381da0188034801c4d0a020239402000068034542d5040f4010003400034003144403202d8070341649140743d004e125043c00411714091390a0f41c2407216016000740c00001942c0c1c800c400111208400c9446845401c50300c68043d40184002d0302c4040c011744040c0444007000c010140c072948443c0c00b091003008031400500040ea0010303030320301d00380340c07500c0c144022a100c100d00359800d041408080360b002481c441c40c06802c0314000408941001041c0e2502c482d480e8000c01c445500c40d1091a6500360014001545802d00710a000038020a041180d00384508010306001c59401c100c918903c0f414598503000c2d815200040380d035107800b0b183c42070005030019030040071117030744803410030040020020503020003100c1750908880d80c3c1071090000d001c90050310300c00340b90395404000300c0c42260b1080750b0800070030b0407220380c801e09001c88080060030040110001c0c0d075200524250501241000000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 623170332 1250 623169082 623169089
    0x60d090c050f01020624041b0906030c0e0607020603060604031a0402040605040e030a0807021e0a0507060c0b011502010f18050c061c0209030f160905010b180423070906080907 77
    0x81c0304200031500046c040d5003e400424640055440c041612044070031080c11000f00c0c2c003516000905071410b030000341a1031a5101030400c000d60300c0950606911000c0a94100540c100c4555849554583c003141d018060380d44003600c01c25046000358881403010f00601c1c011070003690180142c54a5070203003c207960101801034615402003040740700c42c03845899400d4020059206075116040c1034100c0174001a290b00c284501d40c1c01a469101c20081c00b00302d00c2005000380d08019140503090345415121074014494030f1010007103144001803641c801e40c4a1600551445000c00c40803a0f003020068078210310754807c40d000e2003114202c04242c5482001d0782d005000b18000340403a59030450800010350042da82715070305489801c4803001c0d101c40030f018886001c07003031412213220380d89003d8502d4141c40041c0e211286003d82001107410600103000012807000050300c02042590410312558409001c1302030201201403900c0a110074950b00c0052071048076225505c048246c0c5039891103c0d06c682d45c510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 623171582 1250 623170332 623170351
    0xc0507060f0b0d0b3d090b1f09050d030809010b18060d0201140d09030909090807020d030c1a090c1203090f0d0b0703060e090a0c14060d090c050f010206 67
    0xda00000603000108581d03000414859100c984070352124a145c00d0b2100c0000c2080c003c2c4044040c40000200d0b0780068024481000c080c0288445540460481d84942c0c881d0001d02d442440125802d40c060000007000384409042800790365090300f002064504191100c140950811741d8101ca035151180c48849900c0d502c201d01c2c103050300e4030000c0084126038100203c0c18043c1e034500d501d0211680002800d03144109000100f62056140b8000300300d00741c6604030700d040c0ca1410095401050030402075a20107a4107440600e08540503040c2629142400000200102d841807401302e012a03202000f107000c0c61000c8120b0358071582c043c0400c0454101030b4003090f001e0b03200f4000c2801500e081c1000f81c54251004c0c008014172606d0f501ea40755031050450340c1d9404a501c40e44100400030070b0f560080e92022241000e000805015516200300c284c080c401c0030240c036109084201296203070800c0343d241419558003002202007514019001c04124450710744511309800c0c40f018154008030309144949010b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 623172832 1250 623171582 623171599
    0x260a0c0603150512010e0f0f0a0f1703040311190201080408030c0c060c13242007170c0a0e01030b1504020307111608120309010f0c0507060f0b 63
    0x4504a00070701c00b50110621591030814009482d0316a503a281c003602d6150300010664295400748545041003862031503d140c2c3c00800184040c003004500400e01d280e215038484800c00131403d0110260b1012441c5000b13000340041030000300368110010084a10602e81035840024154103040611180110041d0120b0340c01000100028225030003558484a0f0403085030400301d04ca441381e482c00038200c03030240340e501001803107019030300c0451070780c200429104071070b002d4100d206003414600c40201100301050002404100054200d00d03091440c0040ca840111130003240d0740d102440201a040a000d0140e0103000103640306400c00700f0070003082c4c440e04038001d146a482d5550784100028020702080200300d000380c403044999940d000941c00382c282c90b038034101d8040700602280c1c186008000b0300d00000c5400c41d0700f00705e1040041403030790003108400082d90316a966400000d0260403a001601e200601e0480c0318515681c201003e82756542c090082003029444d803101e0030302214005da250a40c4407005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 623174082 1250 623172832 623172839
    0xe0f1b16022206170f0705010512071e02010f0506061801050f0f03010315050a0c09090c1e030c08070207080c04020702060904050109021c060f030308040503040f260a0c 74
    0x9403a9007815000788510b8401850300e40c084800311030164000e030296103074031240c00d1070000301040300c0950b588400300606003403441c1c0000030f441c91065882004a41c0f003090000703118140902081c41118104c0540c00b4543c007d070101c001d008101e48103000d00120b240901007100d50800a06a800d0007810a1544107007116500c0150b030703960401000b2410060781006420707011200300000d07500840c440c120400034160b1709181001501d01c020000701e000c40c54050b040990f1030380011080c00f10f0700d06040008441c28a4101103541424141e140c44e000d082083e5451140c1c2d501d9881107591200d10b035070b002c00d02e45550604a0725100c061003030039126030007840354403403d01c1c21780e005010041c401490140740086140109046e58001d82c00030411650200c1c0940e80e0b480d10002000500700041410030146081caa2016a005900d020107010464040c00150410004104030b0b0050319079550007800d12507840600a40700d100c07045640da403440803660102004580080c1481c00c00e60b104407003410807810b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 623175332 1250 623174082 623174089
    0x4032c03031204141218030a0f0b0604090203011b030e0d02060a15150c030909060305061603090b0f04020f0105190e0a050a0e1e0103020603010e07090e0f1b1602 71
    0xb8042c00c1039601d0380800000810501d000c214101030010103002090b00c4071260012400d41c0410551518001d030000a10103000601108081c45100e500c401c901000b41c540701e002c00c00420459070025095840c242601640307640d690360458000c5000e5400b805801c1042064a480d17030f892641d4400540c0c000e00c081150f41007590002da004100030b81484000c51ba4501404883c04640210400030409140b142030a055000c4a040c1c0609505c0e1002c0c80b0440c6103950f007907507561004100c410100b050132046500c5a00c00e070445e901e000e410466140301e600701300142c0483c015080d6405c034454280020901039070b500890030345840e40d20816101c603441d100701130309482c05000d0854240e030041d5031060100300c0c1d9032000c2c4020080d1121401c00100d074602004a92018440b030701c25694000c0c0c0000041005030303240c41c2203c2c195404501030000c152584141514111416007140703072101d44107070402c21507003820008103100f900c0f1241000f01c43d04510480302040c2c0308a038400704c55079a02c081944054203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 623176582 1250 623175332 623175367
    0xe25051206010c0f0f050115150302070813180c0e0a050405100905011e08030f0405061e040303030506102a02130510030218060f010309081204032c0303 67
    0x2010304150342030041c0b0b90784c1d081c010058841c00b1502c09040d02c603410300b030110074800c1c0008074541e0f0088000b10750602e5030b0114140c1c50007000d03030f08068000560404006c0c3c8071050701c0d0196a07100c01480751588482c10404110006085001030b02e14090301c048105101d081c17030414071003004d000701c0e41142c2805c05102c080c0c0402080c2180541512400060108440c4119402004002c0c00304141c4040003030811482c468980c0004003960050144a008000c108112011100c0072680d03140d841035004040511100a10a048045030020a00005054040d005144186011962001d800013134117402c0d20004030207400e031112078219041c0140f09c40d0f100010354108a0000b0001a50740d1004003c070f60a84104850b441400348002004004500303080302c00800000002030204003501d03000f00820860903458804604154070f691540041c4002c00084805294560820446a207070505000c1c0c121101440718042c4e10a032000071540122000c10170220000c0b000300918034050260f014503e514 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 623177832 1250 623176582 623176591
    0x52803090203160906050d050618070923180715020a150e06061012090201110303070305040c1a040b0708040e040308040209010b04060806011d04060e250512 69
    0x1039540000e4405070b98200000340c403088201d070303c495485050207010400d0b035800b42d002501600d222062600000c2d8003003542a4840f01c0f1801c8100d84030f4180b540d00345850b009920201429140c2007504240c801c031b00010511401215060311044d0b12401381c880004294154074092039040b800b0103000884440c06210315041075481216010907464030758407558011300000d10b01c113581d034803184100c2e01e03424444158420302c2100c42d10740ca0740301c00d20301a007080d100700703c000075996444410204581c002e2000d11000e040356011a620b0b0301d401980640241001e403001d4480c0c03440e540c000981c030500034000111707c0075100301e00d07810301e860503007058119003180c00c0465102030140300118264140c1c1504070b1155000f0b0340c40740d00905144c01444200d14041c1c0003803503803042c20041441079540050001d0f400036402e280100301d949202050200d41c0394030480080d171103420700c100010359045c00182c0a01406001c40d024072044001030001c0b041c600e8031b03016100411001c0c820364030241880b085039540b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 623179082 1250 623177832 623177837
    0x90203070512010b030d020c0d0f150f0b0a09020c03041a0706020a0504170706090605030702073b090d08090307050624010809030f0f0904020a03020a020d0528 70
    0x21522000002d085001100c0c0da14140ea55520b0203024070f1400300815894141030303002800041c4400c00c00f0a4042408050140942003680c1e46801084100416980205070040080024561401042028186040b00907104444404001c82d00c003040c2e1007280d1051000d0f40065203402e2501d19046008044a038980a12040500a010218403980001c0007c201c0c41d5980950b02c0e801c2680704071240180d030215481d0740c0e200400600c002e0703400001c04029182a81400c680365501d00d94124075000d051342000015504a03040300d00541105851942a28440c140b42d124141c4282d100151803042211000040d901080f01d1135043e80c0140511a0058038640c1660719240170345d20341e5864070000b615001c0881c000f401d01c52100100e00f004c1c980c4000403d01e40b1260504104401d86d98034042e1039025140220001040c1d030b440a080000c031014080090003c1d07484402c2240083e0080d04011540307405401181e41d0075090314414000c0741c6000142d00d202e02d004500d003c01c0130744240881e08420b420f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 623180332 1250 623179082 623179093
    0xf09060f050c030403050a0201080c13060804110301060e07020c03120d0b03150907060e0306040507090e0312190501170a12111b0a060908030304121b0515070804050a06090203 77
    0xc03070b4018802040554011002418203000c24800144442c000414000e03601c44140a6008004242501d250131a0200d1030200a2502c550900c02c401e5201c0741c40440e8990b00c0c081d800a55040b00103051403081c421034090710ba00700809018161600d031101c958421011040140c1b026074402c992204c2800708014003107030609000c0c8110702800c50000d8908800c1c551000c2000c0101550040301c0c007000e1039060f400740000341020396400d03903205043d02422940c9503c841c01201d04102c00c0007511744688820010050500300038003055903450385c00c108481600e0400002007900c14030781c1c0b209041e05ca8500028120040b031619070400134004040c0c0d01c010402810b02000203c40104680842c0f221910b00d59100c1d04a0360080244160040c1d00030b03001d1000e003e1082122a0340401680e5001c0e411035441841c21038815002c680c08003140307400c0c3c100d55103548501d005100c0c00185000d00320080300800c1c90180c641c5001581c14032802ca5005220f130307008001030703400244150012000c95101904a0300d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 623181582 1250 623180332 623180347
    0x40507030c08160212030711120c0a0b0604021e0d050a0b100f03060f1403070e1306020f040302030d0206040605090c0607061d010c030c1e0905060f040803030a020d05070f09060f05 79
    0x350170f03520030b940d02000500c410b640f0340c2001c0011311200408103030703040547d40740441c842c0c02203840b406030020107428004120002116a10303680c04032075600810303802c0511080e4101004c2c0b1801e0300011010110140740c40c0c000b8143d9550351048419101c0c0040148001c0340502d03000b107070340c428800100010540c94110010f5100020141032015016008058102884181c00e062401c0704540c445000c48201000b80400c000141400c0c0c0c018a8000c900503070b446210720340c0d482c0248a240d0009406100d03102110420546c0800d10f103010b82d2084000340259280c05a010340e41c3e85107070540f0f0741d000700100140340029040b80e0014074011003401880c160f00416240726400c50312821103460201e0748617101003c0c0c003544100c01e022070500220030710790f00f1880000d0007001c814a0340103407406004c001511004104e1000182c6005213511404c03295286005180c0c000a500a1041c1031551820100402c9103580180c0d05440010125950040124902041102c4455248164a00303000c1e0410603031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 623182832 1250 623181582 623181613
    0x70b0114030a120315331d040e030a180f050609010e1903051e070e010b0f12010f03060b011e3504050f031801050d0b1905040507030c081602 62
    0x41c0024024200c0b40340c2c500c0040501c800b99805040c03410000003000c1100010101d4000c0c81c03040008409010f50014080035801090040c50285058a490710021400bc1d503902e600050700c2030341c81c44107800140401d642c1c0e43d051980b0390035406490f6000c0001e203c0410154820908003000200061110007180c8820081c0d480c4840c0305e80003500c3d9504076085400e001480e4480d00c1c039595405000030190030b4a04040c4511007401030185010090b00061230208a5200100703492680905000c51845969100aa0303000d2503018401101e81d0360401e40d13070750f00e158001c4030316190004c14900b2502141004400c100d54404482280c04144c14607982045111111210305d911481d5202d184201d10703013024245540381903018803030b20355264001c0201111044040c01d80c444102e20a080158444100c80800c20140c0382c801600c54100c05440c00c00048445000203540450350280d4003080551100c00c0102c080d02c800091080c0421459004544130711100b0310450300b20007040c410340b41000e2414821 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 623184082 1250 623182832 623182871
    0x150504030206040209090c090609070201140907050f0f01230f0c0a0c09090305270409030201020a0e06030c090d210c06060b04030c03150608070b070b0114030a1203 72
    0x180d00580c859001c00085081071301c405500000380da0b009200d000c04010000702c03035100060100c2c0c000d240d00004120950f001750480c80d4550b841c0c1000704080e00d070640074540c1d128214401c1500c9513002960343c011034180b5282c030050380d81060390f504948507d5200d0050300c007040102c00340d940302000c009203006840e4039400391502042500c05408075285d1414603122045803600412581c0c3c2c0b07419400c100090b00101100c020b4480d0300101000c1c41b60400c80d1001080f600c2010a070080d0900006204150341036008040141e84d03a03e80790400c020a90600505001c101c90503000c00008201942d214903003e43c401d5078191040c5044030740800d0f080d0038500108242815000454003112010080000c81d00170840039001d440071250a0616546903491402042e21024180c0300c03105007a00b519400381e40001000e07040c080c088401036580c2d0352a01e9941da2044a0130b0f1000700c0c980c400414008141032051402110050003054171702020340b119522901c0d26060101410340e2502042c0064503003608 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 623185332 1250 623184082 623184091
    0x4021809093c0c030601060f050c0115060215060a060c0c05041107051e030d020903010b031f11030c0d05060a032109080c010206010e06010207081b12030a0504060c1505 74
    0x1d00c01003880c5190340d100c0c0ba00e03000c540740c140c00c0d00460f120695546000501e03d044819600d482040c040394904240e03245d104120385201d2550070086d481c000c0080c10564201200c51590840d0310180c0d103200d0710817209405580b003582c86850a001000140d01c14000803420380d000d031030a0302c140c070350340c00004040311001200700c90245000309044d03042c800c003032100f8889000d01401c0b80001003a00740884e500ca10402c502801415808103e18000384c500b540a413940340c4014007102c1e01280440845200c0c011249545000d160801c2c200890344100101520300416500038a035042041501a20b405418000c0095810040983d00007001c00e0540408441c1042001d05c0408940c01e641002001140d080d00f200b85198852100e94a160741c1c0040c070b160455294003003140c1c00ea200d400040f030420001d40c0c0480c1a0b80318001c034802d020012840d107200303400d2040350018514010406d556890f406803c084901040d824041084403500801c0e141b85441d115000c0011800d44486c40c10301110820f41c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 623186582 1250 623185332 623185393
    0xc06140d1505030f0f0a020103020d0b03010f0e01291002010b03030406030623091302030f01020a110f0c01020a2409110301200421050f0d020c0402180909 68
    0x340104501d04080c0a200540783c4404e003d01143d200c2c6805882c0c3c0c0c2e1070640c000904140c0c2c0003c0760f18107411268094223540300014002c3c08182c103803159440c054404012818440d51a20b084d0001e0106c8a40c03200568481682100d51904140c00420826800c92815031083d5501d03804103040644e070070700041002c1c09031a2000119141840000311101e07144046c0603080c2010701607124001c0e941c1c5010503500c14074154040040110501c0400e04018003045e80140640c0040f6091040179000302c001d0781241d2405044601c14200120482c0c1d6856090581e18090381040031079402003a2415100d138801c40d1088000300039401c17004806001c8a2a00300182d580303814042007061245000c0c021324203c0b00e00007003039000c545d8100340808000c4c407642c814607030b80500241c3c1f10380b101002c0c01d6501001039040000d88500740c00c054036890700c403500c0303448640040c0034941c1811004d10b0b091080c0c0d5407500d40080803081080c03003003090181040014041c5401413081c0e180301e040c02c8a030505440d00413014038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 623187832 1250 623186582 623186621
    0x2120c04061e090504090c08010218041404030f121b05030a0b0405041101030c1b0c08060a0e030904090317090106080d020a05150c040e070c03080703090c06140d 71
    0x14000b0161241c0c400003545626070005118030065020381d55800f5103004480010344c480f86441c0c1548040c450303520412107540007180310054020207402941010000341c505020110040c0154880350100701c0c0d0040c042a0b01000400e61944954068101a91200c8001420b88020340707250f5100e403050250312002a500100700300d20341a643c041c81560034015103003800181090b40c1c1d85440c1245c0c0d50041c0341003682d40c40c3c510000c24070844000c0041c1ea01c00300c808118154034206500b00030340c43e006106051140401040000030984034134601010b001001c0c42c20304113114100805040c446e482502002004032803001d4801c0b0b034104850050342420000100c4038039140e4000d0820780540d4901d400c0d90020460b8001144021520100231848101e162030340d66119a803219240c0107542040300380d241224104220560422408003000d4042c4d250214680d40354407003101a80c2c006503000f0100c0303079010f40030820140607441c1c0341f00c3d0407c070003c901d003441c489000c0c400c12600788107a000d8a0400c1c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 623189082 1250 623187832 623187839
    0xf06010b0c070f0b270d080a090b040801021b0a0c0302060913020c16050d08040311010903121211030105100c08090301020d061e0b030c03060f10020607080c03060d06090602120c04 79
    0x40816600b070b40000d05044200c002a0070000f406142c6d1510001d04030840004540203000e1103402400c019004000050703407226224980f00d0f000350031048074640102d21269112003019000220106000d90100a0f038082e107041d507090280d2130300800c20858102e40d10501c8142202e1485c00078109903040b010003800840d002c400742100c0b081c041d912950041c004901c507400440d850701c08680c01e59070800742181c0242c002a0048032440c3c1c041d803010300009005186c039403001c1d03031002d00030110300f1007001e007402400c81c205020318081c40280320b03144e8018072116248805c54080c0000c07001b841d0255a482e41041c624038003007130036a80000d142d02031282c0c3d282d071b0601038411030101c0b02644810a0b01c0e11603981c4c0c1403c1c2c80002621014001520000c0003000248160307641020302e0b2048280903100b94000c00740d0b8030010b55a80e4003a5025030210703901800080307064244e1001c0d01c1c4500c800414543e1844499124203000303000422054914035000c008000759204241c00c0e00e40143c201c00c028503a214503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 623190332 1250 623189082 623189107
    0x21c11100623010905010f180e070206090c01020714042f0405041b02060402091801110d1d0c06091903030c02100306033201061e05030f06010b0c070f0b 67
    0x2c071060b20341e05005941c04140301d1079a0103402c0a82c640c4550030b20307900c1c2003403c8881c4460017100d07520200901034810100f00c1d90b107501044c0b0781d005940a008681106c00301c0300041ea10b440f203901650108580502c601001031030035400130300c0410128542281070800802100070305904941c80001051000103042105040c43d20070005035003203400414010000e42d440003500c1da403000d0006449420101c02140140004100c1600144101c00003004844040740580d039054106584203007c0c00d10300440c0360b2071743d01e40c1c2c0c4030a5507610700030340a40882a501001c000064004d0700103590843d420404003e0b000c070200c1c007914007940c02510390f968105c241340304200122140340140710030103040150802c002840d2002c61070001c010322000e161218080101210085502c91011429600b04100011191040302c8030005421800d09030004040e00c58052507500c40d16888072041a80c0b090004010742511080074026402a880a42d116541d6507601420980304035000000007050004038241041c0c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 623191582 1250 623190332 623190389
    0x7081f060e0703020f0c061515090f040c02120a0e010305072d1b150c09031a0408090319020f0a06080a0203060a1d0601030506040509030a0f051b0c030d021c111006 72
    0x9002c80b49e110318000a50020902100d055008540540e444040b01ca0941d4001e1201921301c0450f01042500d9500d9041e000b13110f440d03420340b5030f03002c80d14040128041030b02c03450401d0424054540850040364400b502c6807070500881a1640403c845540c65a04c80384035070304030b040014051040a1040c00764209040d084aa0710403400d014001190403c100080f0380c0e1080101202100782c04001d29600c9080c074034164840e99040b00d6241c040c010040800c036044541c000216130094a940120032520014001c03003203918041c01001c20888000100c0002c03281d0029940b048025040309162591410b00c020540002d0b110000c000c00301e44100032a6590600c00c05600080454092046003081c40d140c076100e205500304181040015010600701c50301803011200c0c030103101c3c450750401d02c24400407541ca6080c1d1602a9101303028420070342c040c1900c005000349000b85250f1003d1010341b1040d4003540c425201c040d400c44240250002101142411b00c924001402e9003e071603e4285180d080044480 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 623192832 1250 623191582 623191609
    0x7031b0504020310090903030b06030c030403090923041a04080a03150e0402100e03120703020f03131806080616020d0915030b030307020307081f060e0703020f0c0615 73
    0x300d01c140f0822500001c2004880d040b10700310301c80024012203500b011030151850403010b03508030000000340981504160010b62047d4002d544100440c0c2d204d50b00001035500f4554400c03498889940ba401d1907025460500d030300030744a1043c00040d00c2c550801c000c80e400003150181c0b420440414010007054040c0205001d5802001009140508010000641d08401b0f44041d005080100745d0026140c0600301040d600c1c2c000500b200e100b101d44e44071446003a4070511007100107000d40307038400d0303c030181c0081a982c0036580101022042c50034103d018001441e01403401c80b00c3c0e516400c0002d000c2c142030142c1d0303008a0b0827018a180e80c15640a02034907085080340810100440ca000030002c0c0308000b407694068110511f0007160648864000038950701078400040d600d4000c800002486807070001d24031007200d64042a403280081640e10b41c2c401c03100345110b0b05d884100020000741d00c03a40320b54001c1402e03402c810b1007241003c2808504920f000e50844101c032183c0c08070060585a460204e0302200d11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 623194082 1250 623192832 623192839
    0x150909030c030f0816110c040f0e0c010302090a0608061c210c11010302030702010f020c07140a030503040e06011115190c1416020d08070b0117031204031107031b05 72
    0x11706051074046001c0140034800c400700304001041e1807030528240002e005e489402002402440c03002240e400041800103c4c0310401c3c80340000214465020b40261066120700809843c0c600c6d10380700065440480003044203501403901c40b01510303042000c000301004140140102014070000d180084031070030403081e1000501032804007c4c030005500c2c600080c1206020301e0096200d840d0008140d001d4400d11440750101030000c203c0c2d2003604c00001d001021a511001c1c2005990071038014020a48034500001c0c1141d00204024002c00c51001442a04420180350030428102c54044280c00e10500c2c1c0804d0075140000b00c00d0008406540748000a10540c0401c10050503156040251400d40b22010349880c4031400300b042062956011074101c2c4040c0c0103494030b15182c64509d449580c65000c444100c40c00c4142790004034244005c041d08161400c05500214070b080114209440c609100a000b10308122600d002e07081c2070031091084100540c45040150f004100c100c1c5102504d9a041d0003c902 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 623195332 1250 623194082 623194097
    0x606072004060617130305040b1219270201050f0f0706270209040812010f0305011503030917010e1b09090d09030813091505091006080a150909030c030f 67
    0x13200b1000c5001c0503046400d981005813818018501a243e43c0542d038403807003070310030041800740c81660413509180c817416102c03903802d50203100c48041300201e810300d051055810070250590340800324003c424102682c01414054200a0401e0780440e50754800400c0300070a8502088840130406240501c007609034800700304014906143d800c0f041d41201c60003020b0310994000001c10103201c409011210307184642074429582e0b43c3c440d00d0940002d281d030b120860301c40d0310b0405468562121441c01d031055961540c0c400306810b02c1c0c0600a1440c0d1001e041c00b030529561141000801a810414080c2c0c04845c0b01c2056a40986042084582c00c0020000741d165088a0390f0116a0b0341d00c200d40006596010000503101d800702e403107652001131035070000e42140d8900b10030344043c11050100741e4101c41e41101c54a03901c0e40c8281000081803010721842011440c42740104069403c82d80111052031440394400003810ba503001d001c0d0688031103e0b01a0045800c4040800c03e04d41e011480144031074071800c0150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 623196582 1250 623195332 623195357
    0x7021e0306130204020f0a20060103050d05030a18120306050f060f1605120306090c130302060c0109050712170a0c0f0c0506030403030c030b03010b0609040506060720040606 76
    0x751a0707040103000b281d1411401c50503208665075641501d160044525280b510340c0c00d038240140241400001c450510301142e801109801400600103060f039601c040680001e8081e01803d030be0a400107490b0b0301445880f03104c444240081c46441d02d2440c0d0150300e8044d4548400b903006011208550419400b50541e05140441e6803208811200c0e40c10300b0001856070340d010a600840749031451400240f40d030003034000d4420300d03d6000d0091401032008640e008819210764031220030710700c81c9070010750101e2075480b001c10251a01c42c0c050b10807000b1480c00400d030708034182e94060800c00b407900801c0d01005418084803e000038141c00100b280710301030b4139074680404e820020f08004422040109100b140744604002c1121003c0c000000f0a00505a59140d0916103000f80150102003941030000c1d1031300540142a01d41401800110b4202502a03858103044400f0300010300002000140c000c58108150b1001580c541001c05005010140030341c6102c41440c10001510b0455100d081003203c104e40c501e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 623197832 1250 623196582 623196589
    0x1c02220b0a080a110f15070512030f0415021b0a0c06030b0d06020906070c080c120105060a090213050d0311060c0301030209011211040c0e090f07050a120e010c0507021e 74
    0x2111041d0403d40390401d1102c04c3d000541e17411001a000d503004143c880010502112040140c03070035900c21425a907040410602c3e20800c0c1c0006c403100c10200d03a81f600402e010500102004508160076a0b0151a103d42d080d45150a0520035480003540d45c00f120720101030040b80300b1b401029024601d42403003000307065400118001c8601e00082c0c00349900049038811580c400003101c010307a80c4158403a1095a90340c51130760301ca15001000714024124030290000e421010310549201c1d1500801480d0704a08000142d0300030340226943d10b40030010b0480204542c3e440e0424110031610940c0c807000800074001c400f0742000c40242422503018030a10050005988040d401e0b41903804004803e0000902c0303041202100c0b5040c0800c0342c02501e400c0c00810155880411542c10440a48098195413200202c0401c107003011105000040d10900118013018410315190071480500f960104010001c00d03032050071103503070000c20404600006281011070400000c0d001c40125000f586800e40d00101010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 623199082 1250 623197832 623197843
    0x171303170411100c0203010f02040e060906100311040e090601051f020d0c03020c0a0303081b04050f0108090708030a02070911070f06021c15030c05030313051c02220b0a08 75
    0x15200d03043c0000d1400c8001d1148040644854009000303004040e8a10780e00c8000354811b01070309038800c0e24103000a4441c20705a000d180512405402c09050020701201200144000720414000b11010000040d0040504803103d02408400c005000c055141c42c0c100100e02448034092440030074031a084420043d00490074415803e840d082400c0c004a05140890402c001c0b00c2c082030f44a00d203281d020080c10b42c0881da2a120784210504460750740305404100505000303902c6811745c0a00c011460b0100c5501c00c2c0c62054000f40c040c001c44140c1d6846012407410340e04001d9140005030300080c3c3c200441e81260040c5242c0320b1030414854540700d13080c0c0380d849000181000213041f0b07940000700c120602a40e40c640041080c0150780410060560011900c0d08201a200c2911000400d21002c02d0710f1901008030f503d011005207000303c1c03013450b20081c812844181c01524020081200f40c10307001d038940c1c4100c05143c00d170743c013000c0030303405801128481200c01c4e280955000344840203003800950000604c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 623200332 1250 623199082 623199113
    0x6010b0304060608060f06100201020705120f07050f030306030d1d040c020f07080c030d0503061e030703150c03060f08030a0e031216030f030504020616031713031704 73
    0x2446562995142028005885030f81c0c094400f0384651070070884095000b0f40454003075401120004202c002c0440203d00742d02800b80d001c1c0850b0003d482000c40ca440d148004d0414900c440612420302c0b0144d1582801c01440000380e030781540000041100604c5d0900140e0380c406014201039041e000b4a00c0c40e032005000c85000c1c00c2c09603541d1481c0089880c001c03c203000cac09016a1080351110b17511102c02c55201c582c1e00c80c81034000d10400e0110340c922030040040d00d204a20103000d0501500030949003080c0491440d0106e9058007034500e0220100705a11212001002c1001c0003041d1105071030002411169143d21440070803005002c144100c41011003200c188031424946445110019070009080c1041c41c0150030056400088580e039001c0b42e00b08094200d4000d8031000e4042c1325460094066a10840e4020350002e010440111000e80024103001c4150107841c1c1000d096110310059881e00e40d013034581212050400e80044105680110310a08001d14000100c9007810203944880c404020381d003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 623201438 1106 623200332 623200349
    0xa0915051815060708070606140f04051b0d18030f110307022b0b040c2102031e160e010f05060a080703150902070515090703050601 58
    0xa5809100c1c4034031080c0c40d21a0b40b0b2800c100006984490021200d20340d05018840200303015101d2000130b03120f40500101c032407c48108004054080486203442181050104441d40300f416910344080c2c4081d2808a40ba500f4002344500a049940b01030301c01c0c0100c255402d018142d0000b00151480e00c0b6446115402e0100c1c1034603500d9205420700039400c402c07100c01c80150381c502c06032008030480500d07e07c848030110a544000c11070409450640d4240400241880407038035040e604111841044850503034881c1e140d01098581d4110f100015242c5c4c10481503458400041c400f000384544d4034030026a0003904e5070303454028403038280540301c031400c060600450075090440490700e440100d0303200c1005076039418000f10301030080d64070490f02c24240800c00090709215030002d010304d80e206201070000540140f04503221004001d051500d20350010070300f0408204040b030036505440c540e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 623021582 623201438 := by
  have h0 := BRFrame.cov_init 623021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 623021582 ≤ n) (h2 : n < 623201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
