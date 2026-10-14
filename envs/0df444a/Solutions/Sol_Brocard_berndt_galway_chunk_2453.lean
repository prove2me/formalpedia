-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2453
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:46:05.338001+00:00
-- url     : https://prove2.me/submissions/047ea6f1-7779-4e57-b6fa-26c9a85dafa8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 441007194 ≤ n < 441187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 441008444 1250 441007194 441007207
    0x522020a0903020a030506061219021507151d0304120f0f02030303010603050a05060405060102030a140f070c05040501050103090b010317190507020a0f06052d040611010b1e0108061203 81
    0x300060248c02440f00311501c1c48103079410074010355208604c1c14000d642c00d000910308405442d00002403107510f00000720380340c81d021640e030303070b0020403040328041141c001d80c0c400519490020042c58041c45080c1100150314007400c103484120031000e4004d00510404800b550a02000b1030040a00e800e990301400312610382d6101d40700a40603003c2200c1011449240c00c000800c1031825009140c0100d40680155113001800042120904180d8000700c4c0106400c00a6100c42c60301031000b070101900980c4070210081c10201000151403041e84070a0402d405c10321008041002010a1811243e020444449500d01048803424500440c10200005100c0d4102d800701103400400500c0314600c01ca0318881000e403280c03254400c0c5030050007080300160303090200c06031381182d2140c10026048041c154144284c2d5007041c002103a48507402220001e8040e0308000c490310004d010703800d1822400c4903442002903200d8000199004540c0015042040400202e191500c0307442000440e80f20b0401036070750b90300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 441009694 1250 441008444 441008453
    0xe040504020d0803070c110609130b0a0305060c040513050f0c0d0f05010b04090f0504211803080c070806010308090609040b0904050c0109080a05100b0a080109060c03060522020a0903020a03 83
    0x70100071b042d40d2000c0d00b01c031103420510380340301203620b001c000034454004081c003550703441d004050680c101a00881c000c20007001065040010398442c9060200c4180c4ea0350501c0180448d13031030340b02601c1090038140b800380100703c0c8040d60042c1d03011100c0c0c0c21240d00d401081c070a0714054141ca80c00301465510307180002c104448410010015110751840c14000302e41031a01d6a0100c580c1194090180c0c0705501c0c842025081801d00c100e02c11465243c0040522280d807200c0b0030012840e4400c41e520900081e0421500a0a001d003400808105015003819031460700c07158624403c4007034051041e08001594031023540c480d400b08545180142003801c1e6403800d0701c1d045590320540400b207030204140d03210008034502c0000c1c48502c0b8950010291075074000900000d40039210b1282030540c08154050301040105c002d00c1280540c60148001280a0387d80b0140a811550b058003c40d0141e00102040c0c034003102442140d111010840500680e2143c040c601211030b8030003500000c1d8003c16000c2d0020074417 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 441010944 1250 441009694 441009707
    0x103180b07090e090706110312040b0604090b010b0a020d09060504091d030307020a0203070803090f0609030c06030405031e070f030f091203090f0b131205100f0516020601060e040504020d080307 85
    0xf240142c81f5014102c0c2c0c42e1014036540d000b8088003410f0034007201b000400181c400903240e5082071020f8004542806590350b240d41e62482600101c00074600811102040da82c1005020f035141e9550420b41107180c20124001c0192140d8000c640c00f203600d0388980030408070f9010f015441a180712040da51681000d040c000d45130b030307030b40c10f001e0b446445202d1002c9040b0b039003c0111202c04100030a6030100c08244010b0058540001803840d60601928200903556103c01c802117100d54450800355544010100b10046440e8034811005146002840203500280c00d809400390115010304141c0016003104a040f140110035401c01d000709800c501e10300301050303004a9240c054035000c0e03503180d040715241c1c0e0981d21140220070341c4030750b00c49000b0010403840c2900c2d4840001036004e541a0340b00c5900402e03101c002e98141242c5180a40d40c1c3c4c8007005620254020a5943d2050b40c0c030240400d5494100300900b00c2d41d841d41410320459075103010a0455684014034021144d000e03049540324030b020000034009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 441012194 1250 441010944 441010949
    0xb070507060f05090c0409080d060e0a060f0e06121608010c090b030c0a05070501020906040e04050d020a02010f0f0e04050903091309210c0c080102180103180b07090e0907 75
    0x802e06190001c401d80d035480c011544500d0040000305a011402c10401c009051100d07010340d4108000c0040401c44e00003802010007500054055181d18105410b2000441d550350f4400c0f00c071190380034000d101d5003080d0046d56411001c12501e4043c1c1c1140103030003504100030300785040a40c0d05080c00008060b00d041d0810654030110391103804050342d40740302c1002c403840100d4540307850000c00c00500700c00300c3c01540a84111801900014108403619001c55120b038000d070000400358000408100c2000400c00003030318020050700c054030300822190b00191100411200e0241400052150172410314811182203e4240000708144100c0c10452001d036100c0d03022072402402400440c08000c0314240c030f070190034180c650003804001441011700705040f000301c500864104002c0c0c2c046c04403011074045048076001d007001000059544400d02c02c2d030211034900c13408107418182071481603682400b00041001c441e41e00480034104907942c4c00f0342210b1941c0346400440c80c83e408201403000d07a01c1c001501006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 441013444 1250 441012194 441012203
    0x161506060f02010b0d020607080f0d0e101a09011412010203040c03021801060504140109030602070510150b03011202040e06010602010509150c18010e040908070209061005030c160b070507 82
    0x802c0c0002c400c1c0a400c58117501c0c00303904000100a500001aa03280081c050a13a2407640c007030404444c5140704041e02c02d02c0b1044140713903000c808140c800b01001d01c030301504412201c030074100f03c4621902050070800140b04040411402d85c1d06059030380c84021501850600d040c00031580c0f440c20346403561000c102c43c00182c0c0110420036207400c20305242d51205042e40c039207407243ea003002e141810078022140c4041040e8104628035400000248503400a000610720400240c44080c0c5d4800080044070042103030003411800c0309004011002081d130460f41920340c8136001e8000041d903400818050300c29048066400d1041700d000003580c82d070640c045401080d4600a865003092816520048100d0a45840c214801c007007185403264884c0c0c0c401d0b401c5121042c1044416800c00100080442e25408e2054030080c3c400540d50046141c01032800364000c008036010791250004c090014242c2c0001088129071207070004052200c111203480e03108116500181d003220301e18010704010141e8008100807107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 441014694 1250 441013444 441013451
    0x20c12010615020d2006130804050607060920010215040204140924060d03030906060e04080406031109011706130501060f1103130b070620040501034b0c0305101505161506060f0201 79
    0x5403403f42881030004e001016402002c1c192920122210900030145c41281d206030303074031036040b40c400d80b00c201d05200711220406080808101c0c10b803045428103103d6110801002c1404000345035541c3c18a21a55036010b01d00002c4943c8107103440c900804040e08400c2d034440c0010108400c22038188010320995040741d406101c4040c2d0400c25072014043d2020746404100800c1007040000130034140140d1003030005202c2002c0c03203025a01c0104649080c0c0044001600d1010510786868204404c603c00800b070100070362078859503089444005070f20380504001c0c100c0000b040300500075130b80c004480003910145183c00c40000400050100d900034407a842c04282002d000300c0b000c60b481d80004041c0c500078406009946e51a110300c4d041144210103007101e6507801c8410030f0200c6954400e20602c454192400a09428815510307483e20040d6400001003ca0710180c0400c5240d111040d121601c07000c0c603c8038035160707681c0381c030710560b0780c40001c03102820707240000010b11240c2c441c0300301c404031606030004c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 441015944 1250 441014694 441014723
    0x1e1b0b0901120203070503040b041110030c02010e1f0203100305190605060d050a170d021314060a050913021902010f050a0606020c12010615020d20061308040506070609 74
    0x2c143e00044910754086001480024046403003010321a40c071034032496219450b5080c1000140c010141480d6410000340d4502200081e190240309046189014030005c0540c850700300d92802a884a03041c09180b01da4012000c10304040d0040080401345a001c02a50031940300607040305850802c085041d02d0306410200852010700702401c002e00c1042e0000c0203803083d60607d842d1104554104c501c1c120a012007084019031a1045101428445891100d00d092080ca4009022503c02450503503034480c0c2004c10004841e82d401c0760840320300e10000d40703200e40009104d81d90131000340182045154a5080030f0160b210496042d4000882c84140040c10402619404005000c552581c019140941d0280580700280c6c642181107524114a040020441540700c050540456400903120400b5a210140d1101800d40008001804810310603c4040040c1464102651100094821500c1d00134071800d40c414490154202e0f4054003002e00f9140e40c0b40031500c0d11600602400780e041d01d2840888580 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 441017194 1250 441015944 441015977
    0x80411041a131b03020a031b0203090f0a18020424050a0e03030405060d0e0f03040503101d071706070206100e090106080124090504030c0b10050301050a0b031006031e1b0b0901 77
    0x384042500149d00850800c0c180c2c8050103d21a44240d5503984030450803000550721030758103140411041020800f60b152458503002c650003809900d6001c0c0c3d9291402c3c00f00f000c40e6130110a8410800d50352030010721480010700800e046110300e80026403c02c000240c400c3c0c111046810404100080000b10f40891100303086c891384a015070301450364035802035520010b10b0125504120059040f4510740708c2195040b0452514010a5038400700304803184602d108622b0303500f41302c4194000103a00261141c0c0c40c0003141c0340f0f0158000c2c02424110454500030070500102580050013401804008119042d07101222000d00018025482810707060141c01040b0360869020b00c0b805154540c658410003050780c0e960000c3c02c0c4c030043c261460704001d0480040c03950703401d0044900504a800d00018810034400c103241c10f091000c090a10928100310081000540c070030303004000b08940b080004841c480c42e1030410300f020620740847c5200e55403008041911180c28004041c404030980f5806040c2010740c51 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 441018444 1250 441017194 441017231
    0xb12070c050a0602032d0a0b01020118110108010e09070612021b0601080c0d15020306030f030409140a02030601020703031d030604140d02210703170403080411041a131b03020a03 78
    0x90b80001a01b082006c10340d501d01d503030841010090140004941c50003240c0822401d1241968240e4040c0340f0000901010350304400001d01516001c00d0700c4443e480c11a882960358819803055400f040000004026502c4503541071751225440f00180301c1d00c0414411109551b00402e020380c800c41d0098451304545071070843c1080080a41c00412a82e0010101e60124001c0d000100420b82600407500340545074101070000f0800703801615800100c0b48805400b01298803001001e604d000d41c4100140040f0740e07000210081100c1d0b051811401c054040e4080340140c0009040c2950180f107035100f4041040902c03484015003a060034111915181d0044d001c0b0ba64002c2091300c031018548a400608991621000030b11075640282030480300c070136003031305c0750070744140111019000070300c4807414441086010300d140d10289808403828402840222040c1030f040c3d010400092091402e000b5450711040d15821081046507045003000e03c1d082ca10074054065845442c807600041d280c500c1100741100b8404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 441019694 1250 441018444 441018511
    0x6050615090d020d0215030117010c2604081303050703291602070e190605010504181d0a05062d06040213090501121a010b12070c050a060203 62
    0x24028908510b2035001d100024a0542042c0d810555514485c00b410200d58000c500802c43e00c03113108981581d00c80c1013804c45d070892031800c0c2009050341048084041490121510f000003824281c2c03180c07202e01d000796540c480d10420401c0008102c0001083c4040841d80b1001ca9002c1c3d50300706451a6150107100c800c0c42c4024654083e010b20401048400203819041101008280100c2d5990340e191040c500100c0300071200c00000d000110b48090500703002e070140000401080c20004e0500342444105d1000c08050a04252142d9480e02c0c010b04d00e000301401104000300c1c000649101b4001c50030b000e070b21400121146c80300d002c0a0284004c1c102059221021000d5020b001041e040d180c1c1d80c00c000180d40410103440180c801c00c0380101d801903052050a00030310303004820010982d880d181103a905d00507242e5a2496440070301c010001f60040404503a45001103010040442d078444031b042e00d501281520250862040b1441d2100708100c076030003140109003180b0314041c40309008641503010360220 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 441020944 1250 441019694 441019699
    0xe01090c091404080d0e16210510020c0304181d030a050406050702060d110a020d030212011406040f1e12030c020909010b0603090109061103280908070605061509 71
    0x8600141c00300c3c580710003801090440c848040380ca900e540041e9468480c7c500052101070000f0300041042440c80300c041070030311000941c42c0c1030a40050b1581f41d110414403155802458000881c008001c0c0c080c0111005003919598a045c518030070031b0110000d014071452042000d40d5100c035001c250000100381d4620801568804d0706d00740c103140040301c0980159401301c0c0c00000501a9a591008900030211503000ca002a60303180c10207480300038030f071230041008502818410029800c5250758440824151500e060490183c047c4183c0440d40364420780d4420005403130a0031000c60000300c44481c034000c100219401404564583c00250070b0000d00c5500240490391506820005003802c00e051544000f2440001902820103000700354164030481d0944402e075034810b0780c003080100764406d0710b5076401424220340c11464803220055140040d4581085c504101c2c410105100382c00390019190710b6070024050b0380b120300516204000c0e11050314003c0c4520400f0b5501c0d055400780f0b40c141c41640100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 441022194 1250 441020944 441020981
    0x50d0b04031b05010c080601080703060f0e0907180605010905010e330a08040221061b0904020a0507030e1005070204020d14040f0b01060c0c03030305190e01090c09 72
    0x15560140d030100c12695119000d0081e80b01e01401150f000e2090326191030710354070346480c81c0c034014000402501006140d07500b070601d05002400300840319200c40c02a546049845070094860900044c5040295404a01c0d1111424461002c200341500908225031003a01d68425036502c40f40155180c6003851030590b0800c40c100c0c1051a00200e401030031405040b581448071031490202454031541c0e00a1600b0030225541c602481b08600300503102070306110b00b8001041440745003228054442501500700790701e008800105804080341d0200322000c618004004643da00c4224001410a40200b0800c0d404260310807010744050070110b854407440c929075540c4625010250703003008000d4100310110b0304a99a2404120301840c0c1c8000c0c100e00481c041c040c60050000f40d0f1070031304115030050f0400c8041150108800700003c40485560301980e6042c2808201380d40d442c05194402c0710581078004d5072500f84a000d40504206600642d0355030301902e82c10305441c4c0c40707000340c400b5034007690401c40b5030006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 441023444 1250 441022194 441022201
    0x1c1d010c030905040606020d081e010b0d0608060414010c0815100903021e030f010e030d0c0e0d030f14030402131517010b040e0d080411010917010f0501050d0b 70
    0x12489903414081e2003420001049070710b03200481c044400e950410300c0135a00644000d003103241c000d4885a480ba410200c122201141d540705454010018401c03c0302c180f0010030820303d041c069821190191800030225100c038039281c00c1c50011482240151540d40d40303085581d482c154810f081e610f02c03650302c01480011945213001841400b44030070150b10304009102501100580d584040f10344a00000340c0003000103c104802c050510041d4803c0010b00d03031525030540744d488804003c1d511085600311000a506070044015245a100200c01c01c0d4003011640600003055045002c200307240c80180d440903100f40054030114042c2c401030b10065803101007506102c0f400f2031240c2010074002803c012a50140d913849000da0311220700140701c0340c1d45035140d03420240507051a1103411429140c802c010b00900c40303840c00290107110007502c05444820007210a006603402548040d0040002c3c0d0a2003080303c4803201503500900500b1249441d45003000000030303051410382400a081504101804180d86 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 441024694 1250 441023444 441023447
    0xf0d030e0111012903010e06070806091302121c0903050604230709060302030c0a0320030309060d02070b0606121f12060e10060f0303030207060f0507021c1d01 70
    0x41603022079012642d00c8130000056a00c041c00c82c500c4040000d02c040c0d2607044418101401e4480703060f008501ca42c032900030400403607404100c0c00d4004405980d50741c002d894003119584018190040a50000e038040e50003200c00100261951603030106082d880701e90510740c00d0840b40b1101c18840501154080320110300454140a80400714409451103c0d24900070121f5490810a2940c0641d00580c1d9550003001903050502c0f40c0031a5031401c45202c0b0110f81550b44400010710800190102d081d00c01003910641d803400c004480810200900e03071500c1d001034124000103940441403c071b4040e268030021902c0d80c2020410b80c0d80303424202c00c16040070b17618900c00600900f0849548400304042400000311202c0c0080d0380c0f040b15004000200f11249200069803809038802c0342c0d100c0c10b625081e410409000020010f0080d640e01d8074000d41d4415083c280b12003e400c9201c403110b66186030406001701c05030002554260104140d1009102c403503c0035060b68442c0b8444c0d912031a585000c100160550f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 441025944 1250 441024694 441024707
    0x10b030307061a040c11010f0605010c03030e0a0203030f090307080304031e0f080310031a01232214090c090417070506040c0611011509110c01090f020f0d030e01 71
    0x2c058004221980d41c00640010b05a03003090309a078006c1251280112454913081c003800140b4241c07070400f405003c2c03400000070141b041005c00a010103a0314503500401c2e600600490f543d20f60018220381d141c41c00303034000f03007600c2d88504001b501c0f80c80303403450008107271202105aa007141e80149004009400d0f0852a0b144250707586012907071007001c3e00050000804400145000e0111035105102c082e0031450896405461941510140038080c4010004d0520000d07072490044090311843c3c0e1021582004a030203108001c5403404000c01002600e06041c04c03642c0401c2d8401c8214140c1e400c2030f00c07142655034481400460312038004c408003000401244c1d248990154028a1112040ca007010a403901401d001058a00322158070f10010108203035640b02035040703401c0104e0b900070004502c40c0384021450100c40e1044100c115100c41d80542205c0201d400e841e201c541040080c0615003c500c2e00c5a503417202408201d118203418004d1410038100b41404014441d4035440700d6176452a801c0042d28071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 441027194 1250 441025944 441025961
    0x80304030e1906030b040c0809070302190509151503100308070c09021c150e01030b130206070c0614090303090904141e1c0f08060402040e09061008010b03030706 71
    0x30807010712001c8500700d500b040e4107000b0034640da800a84034045a0410040e10701d880c070903e01b08501c66042c40100b2102040d8803040760740c100e41440041480340b485180052003540842e910010040c1042008071100f1803400c16035204440d44040c00350301c005540c0300d900003a2001e0748440140ca000303000040c0204002d080c041c2c01501c4c060041a40c0c0c000600903a40701d0203c551041c0c41180f000d044055580c014004a068101c160060450a081010045190500c4050300350540d4802190351107400c880c014041c0364020b0a069030392419030400048204051190b6070000d40b032000480102440d0b00c068560000c0000c02441c54a55502d0401041c850054025170b00c100010b0740b26038110408100c404a1540304448400306003100c12056410030201e42e02030580c00441001d101d002950101c0102003001c05418855056207a0101140082c00345e03030020036003040303101300340011200000707003180c03280c40035002c00f11005854000c0c190982e4214504141c040e4018400500000d004d038200030031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 441028444 1250 441027194 441027199
    0x11805060a0507210b1e1002030306180a150b040602060a0203060a060809010f020c010f0b1203040515070c06030203160c080301090b0f060406080f07030c020607050c1011090102150103080304030e 86
    0x35409111380001d00700707600d006100c688401c80303006c603401141841440030b0407084850003e5130441c070b850030121740c19104240d04900d48002e100d0004400d0400c6900c801c002044200500401030b40f2045861010340c0280038481c05441500c3c0040c0502d819402168460340d40a03041031415490301009440d000b07009400c0b03201075520f5075203402c40005544007402d11b0509210020490207000401c9008a9081c10501805003c00e040c050303540c2c1c0400421603003202d40690f104991030132840c5840025000d9a03e0007018850101e00000d21998141c0255000c3c103c013070750803401e0f42c510100a840103074000c0720007480844d052004000c0f92402d075000c01d482c800080c250400c600b80c0140014000e50054002c0d40206805c0702c1800b110f02d12100d8855031046840c02c080104039001c0030065601c0c2001840042000b500003440c1f40031890901885000c0b07520000c2c180b2000184444011458000c80d64041c01882811782c0d000300b00c01203040b01c0341280c2d0000c25091450b03c40c0d46040301c03440d500240c500e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 441029694 1250 441028444 441028451
    0x203030717014b061d0604120302071d10050f0102100b01020309130e010c140d05060d0602130513110301091a0904060c080a14060918011805060a050721 67
    0x140504050b481c1c50b5000c00101c4403c0c4155040a90181c2521440196000005840440c0f42960b490780c2c8201e40c03c2e1000c000301a400b20240780b504034034200c910380008500ba600d0001c2c241d0607230032406126009240c80c0c6000f81e00c0d50f4079001845200940821160b006078400000151309082d990321280c0c01203010b10659140100034008141074900400016110565600640b00b2040080c420a40c0c50502072030300141400b81c10003018014001d642162082d40d50b01d401282c0c10355545241c2c0c0741700310b60105055444282054408001e010688142801041c00e075841001c0314043d07111316040503418055840c02c50b401e0803420307402018482c00d0f84680348101d18640810b075a443e14114030640c82800003242d044140c4000030500f24024000494041c20031010b1a0a01c10107143c8941c0b00d60103503030503699641c07529416100010f10840415281d46495a0000282500c840141400f4094400c4030003070b895088813501217610072501040058072140000f00e440400c1d10803046240800d8a011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 441030944 1250 441029694 441029789
    0x6011e08060411070c081b10030c0c062a0806010c170705030c07180b09010302090604060b0a050a0e0a051c030302120705090301140403120f0f0c020303071701 70
    0x10300302540000f00645c1d02e07180c0103008000480f010000820344202c075050b1203040a12080210700302141e101c01100c03d241e196004480c1c841e1140070305e440c00f1604910b0a2264245001d5012183d018451501d4180c4003041c440411041c0640e82d424083e64060b5211021804540ca03a18942034015410010340d0308204203a40118070100050701542d20b4000180c0780c05032501c0b0b00140c0400e20500020b011a00300342f1420303250b548001c00f550450350140c1300c3e0300599582c00009001009a90000c5981040203c0c81030360306640300b0050704102809407554505a12000e0802c501c03100740c0d00c03450341d01c0506d082c020f01c0c900a016524840c0d80e031107801c1c050b040c0f203268040a1007403401281c5450000e0800301d1402254a400d00a19134148101e4000004900b4913403802030607010b000a50080c0d1584035042c0c448205800e0748200f0032540ca01408000a00c02c0000085d180c0d80280d0743c4000041502034400700b600090360f8524129480a0140c0c28900c030009041c200030940301c189249240b0b69851103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 441032194 1250 441030944 441030971
    0xf050f010b01271505040503070608040203030703030e0c030d09090617120a051b060627152407020916050a080601050d0912080c0f1c11070b090606011e080604 70
    0x704521178441ca5207440c00c0406040c504840daa10003800c1010440a00c40513880100803920844c0d054034000ca2012803400d032403890036040d6000a42c04d4442d01809034041c541c82044d00302698901784041c45040e948428800303100e41079010031007040d001111007229001001c00208481c44403410032500381140399002e120403980303d02c46402c0980000040000910380001c6418034181d0309000305461b9807007001e02506e4001d00400c2c0c03284e01e4071307240d500d50015070360005190240b25419a1243c01c414a0b2800350320030750800002203005280036400b10301c0c5102440100000c114850b5102400c020301900200d40b815009013859040c00000c2100c0d0300c290700e0500401528034055061a542805424001403441000a216050040050082c81118040d1000321544a220002e2800d440c0d00c3c071610401c010400c18070102249000000d03044d040000c1808542d11403130b5083c0a550b103641d103100040d0b030030618582e40016a4a000c40700c2440309070260401c0758110300c02a0000840e90286181d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 441033444 1250 441032194 441032219
    0x1116120f05041719080a08160c030f02101104090605030d0507080d09060203070c0308090325021503090601091107020f0103022a03090a05150a0c0602160f050f010b0127 74
    0x2400c0d54051700000b2000b80081e08107018070f0f040a40d040c0410103940603100e001b41134058800008040004030821240300740e00c208042c0840c240c03003000030495031540c01440c3c20242d21502c200350960f401c1440c0090545408902c9090f2410700e9181e140c500001507580b5015544400c0003808084e95442c8070002041c2d803403001d94400c1d8141c2d1913048540b8802d06005d000d4000c014507500e60366104214008550040f034240800c2c614805100100400c03051000600c0340240291900740c441012081003520440003680074100c883c0044104224101d1803002070aa200b0701d84040c2d040340410580000651184d80201181b80e580c117124181c3c5100e28010040c0302011a16843e5281d00101d00300c1c5c03c9162040b070850003040100c0744004031030300180042c040b03030003000c3c252740601c07d0101d4000c2c01e00030315404941099405044a5080c400c0900d81742c05140d01c1c00205840d02d102c0c1c0e542e54040c40c4414400c503119218161104440703681c250408007804180000403846500c4407540004c2d80c0082d010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 441034694 1250 441033444 441033493
    0x70306021201030b1008030a0e04140405010c17100b0a0e1815040e0d030b12010606050d051e01142202031506040e0c07061116120f050417 61
    0x822090b5490f606004442e08009030064918184600f001c2095604c00812915103084600304440c000855100280003000540c40b024031808a490408c010800d0651101c40b00305080c0d00c408403031249a842d0408154011641c0300c0c0f0518042c0002e0244114140c0a480d0b0707150649840100780b0000780224242004c0310714801003801c180b0341400700f482003030440c49014800540f4104544891490364540da40c603403400703d0091580d100007941454a0744904607504040b140001c2c00015661301005240b0313485080a51b072030502d00340200d5440c42089004402440a0410350000c41c0d082035101d00c600e0b1080841c1c2544130306018a9103103185980803084649420b0b03114010703141e1030038140c1c84c2d00418442d01c600d441118204410f010205c824940160031420300000d440d2510b07480d143c45801050f0400004003281d002050b0710034907040d001d018071a0030384076000c0501807100c494020b0b10504035801c404404070f6400e010600000c850b240301d10608a8500c401c450500f14004484005406070310b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 441035944 1250 441034694 441034717
    0x809030f0105060f0609010909090606050907080601080c04120b100f08060405011506080403030b060906030a050a0b240f1b030d060f120210021e0d0e1f050c07030602 73
    0x850422074a1316080d081c490141c1c20a07118140b030070008074002410140c150080c407500503900c03103010040c40503c3d0302c0700d009044060701070074260400d800003501000007119179600162800d0009a0b020701d15070103640490380b1560b004e68410481c0d0ba51001c1307100d0024001c0003a1801000c00041d001000783c5200d0080000b00c4c060156810039090031425911020401000c1d44540e010802440d54030106a5500517090318002440044c3d400007e0118401e0b0103020303500003004418010440e8044c3e21440c0550016181003010050406c10b0100107141640d01040248207086100f00225400c001401507041490b0340c10b00c2d00150304c141400c580d01c14054086603601c04a502010002144500009010200700348140f06180c10046210554084002800340c20680240c5001c10300070030209144031644c40040185041410000340c3c1c90342d000800000003018a6504040c9090894070f1a0030500400e9000648080d0840c06944590081b2103400f4203115810002000c900148041c0040e003085 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 441037194 1250 441035944 441035951
    0x221011802090a020a2703021f0504260d0e040e010504030f0c030e0405010f0e0124050c011b12111206042a091505032413111209030f04120809030f01 66
    0x40d030042c070042c1d030000c0050009d40401c00c00c10441540e0809c050710b0845001c501c031070146003244c114140b035203000c42000340040e22485039446c40c03140e040000485880b100352800c000c0c50420401090a841c016140680030502d0441e50140b100c1c46028260241070083c201242e11240d101c0c049421074000340d00c64170a000c0c1000e000c0c07040b0440c5848080c0108074080c40108007188500c00491a1301c484450f15052090000f2646607040b4213402069a40a008003001c80e00251501d0140c6203800c0800640b0754645400c45030600c1041607410b0740c0070828904c814070480d50b604401d000c000c07c08402616048005172101713030702143d41c402c00c050031128039a0302c1150311032414004600510800082c2424040f0500400c8002d0240c03402c0780e06a240c0c1604508030074a903800218441c02c24110300f100203e030601960030001001c1c640140014010300f042c000d00703603944912064a0340241c040ca079442c00d070108020000003040d4081c40a6550094000d940f401004000003851301940e44409000c9946 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 441038444 1250 441037194 441037199
    0x60f030714010e060c123001150c0b0a0f11180a05010804030e10030605061813060513020c2b030507020c010212160221011802090a020a27 61
    0xd10405030143e40005461450400c02c0300800c454032041c52824980342c82c4004201102580c03100501e180306481d1220555500d0109583e51807007007403003400742000246001c4c44d81d8031400c2c480d061026071180c020b040d0f10942d4a0b02c4810700060510b44031800e9802d91a04e203451800003480000b41400040603014003541350450040c00b0000b46268080c03410f022040c410000131a03080b11001102c00012900307550450321401040c1c004007510b03085160042c201282007442042100d0107510003a80485480c8422080132480c0310685d403041c040c0c0350300175544d5040c230030082000e50060000d21958406841c1c000c4007440313562001440d15a1107192840580340b00140c1240c05200e815041188c501c050b02a6080410010355110308000d000e041040002400400700c015019102a031b0540c0100380c107800d00c2d0409461645100102d440500c10f528062102c1d0b403032081d00d040104850350141c10395a1a64a18034400e000b500403402c1d081c00d001250b200409240e2500d020505d9800c2d120700306064260 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 441039694 1250 441038444 441038447
    0x41a04030606090b060a03050a15060909050a05060d03110c0904030503010302040c03060b090f01181205060c0a0215060d21030e0309060301030f020a0803070507170a1a060f03071401 80
    0x1039250f841000c0710b92500b2190512a00d40c1d008458040303406060105054440b00d103098000c1100307032210340381d1049800000c00c4090703110f00b21307104031036402c8010f000e1078a40c018080c040780d00c1030392480c0d4000424200400000c0c0119001c0c550b880310501591005c480c1013011846184080307404400094000005104501d49880f50b03505900ba41c0c50100f00c100d08141c58a1464445c910001d44070700007503406081c8603071240c2529190310307003025010042d0340c1d983d14410400848d41c4404a6207405008000780041800c0420f40c3c019842d03550003410701c8482c10390107110f21313180035066940019801e50720740c001c0340c0c034868030307000305c0d19113040c40841010410002805c40e8464040c508480d0410021250166103140945e41500e410182e40146681148006103140015134003001d01400003103691401d0003c0858102d00305c80341e084001060894900500303455820303c050081024031986002c4a6404c203a80000c0e510000243c03100302010701d134800007490843c150348104088480d0b01c00030300c041d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 441040944 1250 441039694 441039701
    0x102071403090a030206090a05040603050a031e020712060b270603070b1b0102041802190903050303070e040608010216110105070f11030c060706050f070519050f041a040306 76
    0x1212180041c41c2080d2076100001e4284505200180c4034030400b24820000fa1746103450100200002817082100603034034504183c8480c2b403503c080d4042140c0d02031043c2c49440c618881108022958013a04003941401c001c11450580c0d503400381c484594888148a450301e03800c00100141203640b0003001401505101d403081204000c0c803641c000e4100210802440a1040a0700d036550000342ca03519000492000c0103009004640c000d5178421541c1c0310008034159907500401318504080d900d0381c00c1d207400744c105440c0e440b500c2c4001440c2e42d008100060344240f0035104803556400080010500641d1840f42a09a0301324a0804c141c5480e0543d921040081851b6005101c1d4400e00300181441c120b40c0fa00383c0d140e0400301001d00b0342c021a583d003040c03503034051001d1006140d0060440740c1f034182504000000702030848144424548080105a6042c001c009845101c4c0a60589420304220040100c50707139040084128407031042800701180300c450080c59201500b0640e070f090760302c81c0d240d41001c070241c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 441042194 1250 441040944 441040973
    0x614060a06051306051c0519180b150d0c1518060e060a02150a020307020c0f0603071803060501030b0921030720010606020102040815060a060c030c080309010207 71
    0x1031150403c2200c80c1c00d410440c5120440301036050060f100ca104281d0084040354603144400154500b1040041c0c0e56445429003049402c1e410017040305061a1014806518444401030600c41d03241740003850b07110860608180a2001500c000b071014015900c8030f0034510030f5080781d030482c4041140c060180741d0044801902c3d90200c0c19140400e440d058015100304550703034006000b0440010740701c4169008000a0302140000e4242c0c00152403c40d286000940090b02c500c0014024400b0300002071901c4901a00300d05401050b492458940c04070944108024149003039003602d014000102050702c0d8031806008500071403041800d0300c1c09404007418010391080b068100d540781540801c1000100c000e980d0700500c103003003030003411101204e92580600b131046514500e6080000109095606401820442c0d00000c00c5a03180391441031085100d8000711125500881c1031581004151311400c40c0360845402800c0c54204211141c8513200341c0d034402c94000d040303a900001e00c00108654901d88044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 441043444 1250 441042194 441042197
    0x20a020f011406120313031113140117070b0c010902041b090b0901030605040c0908010b0f13110c03070f0b1006231b061b040b03130303090614060a06 66
    0xa0a80e80544002c0d00c0c040141032a4041c0380c3c02040b4070040c0b8005c20440d0300313106080c4a02e03074090780d8a01d4a48680c28440b0300715800b80464158146810344140504044401704005045440e824540e111500c030342c40260b20401d52241410000340214520000c0c8800362402c400841c034035030340303005110540759001d0021045100819030034002c01ea02c00e040c0c005039024580201e0b6104007150040b00035184076080540d1180c03505510b8a98103422907071081c00c80d080c0900038815040448108900100541030413500130f6403150040c0360107190388c3d200c1d501d1340c520b04c006c00f8200419003049a1441d04205070841d80c100ca030340741d54018008183d503110ba0140090703146000c51402c01c1d00052401e0380c20b4025030380c60000d040d51000c103040007c040e1a0f00c0407207212024101d14090480613540c401c16a8000e40840c080304600d232046c001801143c080d1010310004910359101e42401e07200460701180b064007055602d40c200c2e4009005801303004048048005601c2190034540f04020701c920980c0e00200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 441044694 1250 441043444 441043451
    0xd020c070812160309030b070210050a02090d0206091c0b074e020c0304060e030c030606150d0207060212090a050717030403050303010906151404050f030309030d03020a020f01 77
    0x100409100c2049404625405400d0800c140041c5015117031450035400c010074002c042803c11801c503500088104903421a000f0130b00c000e88441418404038071a4940e0240c1120070401d00710003504011000308184200030b00700307400d440d03100032641000b42282074040f03802c1d910781c406000c0c185a01180c3d109802000c6444140c01c094942104500d40d4056000145411150f400c10061005011000403071a103207181e055644294484540e9241d074480d0141c103000ca0390542559200341000144901201400780042c041c0e0340329641000180e0706500005011031104200700700c07442d003c60000d052003920404026803203d8020101150749100144203c6455200c1c1c0c1011003c1800002e010302101c007002031200e524801c60110f2400c2d441203420160081c4000000041d0320101980540d04662810b01e4450080c0d60202003200d1a40310b0145580c1c07595000d020902103860800310300c0d541740400800f2a403a222030302c00880d042c10030030807114003c05e9021641c910401e0b01404410400c000070002003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 441045944 1250 441044694 441044713
    0x1120209160c020418020310021b03030f04030e190609181415060706060e06090603070807050f0103020c06040b102c07050c0f03040f060905060706110904020d020c0708 74
    0xd282c0540d03404064841c54407408014480e078146100c2c2d1300078540103408d4500900050010002075030000900007030505507a48071078424400841500d0003501d0305108480592075985080301c4030388010700280e900a26101c1c00a80c1261a0f0094500602c072940f1481d020f01c2c6004c2d0100c44026000100036441400c212660003004802c444d00c90707004035030020103445000000b0100d0124000c018009001c9440d114004c40c002002d260740e02d00c01c0320200c1d0380451594841050680711702040c414040b8661012009014a2400480076178142d5810300d401400d10314400807c5180020664064480c20300250034031194900d44001140070704101050300048048855800c9080d000b14080030351100000c00c04140140e00c00c1045401541170202140c0e81c10407034400b0291070b680107105201070a8049880011441c3c0600022401c81e40d0060040313042014940f03810010307140d24030f0000742c9a80100520f40d410b94071880685180c441c2c1d407800503100c1c4070744d805241c90a0b455420210280e4030800c641c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 441047194 1250 441045944 441045947
    0x1509030509010807091d0603071e1403150414011a012f07084c0f0c0302070303140c0403021e150706050709030201140a14030112020916 60
    0xc4600d101e0003803806064550398540201d40c2914190052072803036240010b1044180d4620402c1130056000f02c05070384009a40305503240c0014550500035542c002c020404009110a20840348518000034096400070310201650522607403003298100e405100327a400020441000741310302c1082c070400c442c1c0204181080b80c001380942c040c521203060940d03c21a0101031440c4c04902402c1d05020000460348a1502c0c0c40945440718a0340041e0130000c0c40c9508140130145410b0f225003912400004890800143c4c0c0e06005041c1c20340390b40d041c2c4803607107a01038122244403511038044501441c0da401038590383d007894000e096450445400e040480c40350148021000384004031005c41c0d074104d0340b003401c59444001c00e40d506090090190f0340400085031400c030070a9200000d10110307209a208000da586c911205036a0f0841602000c0e00254008200303008690083c0000c200150341c0c2d09205034a148000c2c0301c00600c1d0b0098220402e1b0101002c00c2c0c030110b050410103d900300304c0858400502d120040c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 441048444 1250 441047194 441047197
    0x14060f011220070b090d14030c22060e0a0609031109130b0108030d0b0603041a0c0903070b0712050f030a0b01030b090f0f130503030c0a02150708010315090305 70
    0x90441e01556800402c06030a40c0b1a10030803424545100561180b035241401e52142e5000c031100304050051140701c086051181c5040c61030165010401170458451131062400e50f00110b40d890034011009460038841182203a4490003024942c0c2e51441c2c007410300003440020b000b0755100c1030502182c07500500018610380500061900d090b9641d000135600d443c1668600050800050408500b10303001041481010008040d00001040c041c402d076074264003401001c1c80200c03000b0300740c02000360119048004500d589074000007041005410300c0d42e410b000a0802c3e079160b10520317510000042c00300c03c0114420f07020b41c508809080c038909002802041034410700c00145405101c0b03903201c2904503d68081e82c020032241e00054410f903040d14100407007400b000029200d90fa0034040d51000200b03402446050b0a203040d61142c05107086407035440410f580c54011048840548c007902c00e003402c00415181110303204491380c0c1d42c3c800c0c8651660410002c3c10b503c0b43c01a5024609100070280420342010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 441049694 1250 441048444 441048467
    0xd0201061706180c0a060302090406051516080d020c060f060301021333030e1218131d03031015050f0a0306080f010c110703031710030501050a14060f01 67
    0x440c07150f004071400400034101a00d070f0310b419521089001c40403400c0c6034564060820080159020411180ca4a040101c1c103d02c11140403140e260400500d4401100c4c050790303040d428412960f2034101005540b00c102030b82c0042c810300c02d880c0d02190420102c441150300058100c4015402141707041c00c141007140c041541405140c8e441c2d5002c8014906120b0849441c51038059525410b0f40d89129540004010f0240640c460403a0f12070540c500c52580340b040300f100c0414030201103000a0181d07450a01200c02d008140c1e540c86640c1e03072044088256030a144090340c5050100c080d56481c036280800c050001095081400c0000d140b17a1034840e03482d0040e0032a040031420325491500c1d005002004c44c00303400315420450f0103005d180042d40e4042c9054104212000d100d0701c0d020180386000190720358650b40f1348400385c0000e85403032121007600d82500c0d1098000c4181403191644503100c1d2215400d50780141c814070003450fa220035064640c210030320b1158010303a0454a00500041d0000002c1c0b88940741d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 441050944 1250 441049694 441049711
    0x60902040807032303030f250816050d0903080f0f040506040b0901020915090103060b03130305130b030f010906090b01020c01030c0c051e0d0207031a190e0d0201061706 74
    0x50700800d4010854580000300d459181040781d9484c80c024500c4a10404191100e1034075002c5001120042e9a082c0c0d007023190000666074800c40c0da90b0b158002c03408491400e40c100b007440b0003081280303480c110f24083c016545010341c03508115420641001041c0c19070044c5468400100f07101840001080407170300542107074201102e000103803540c0c42450b00a21a01c0d0501d40d000c9101060403c9400c280d5019229003002628204011a500c036800c040e6407000301c4040f81194000700300703034000a006402418200524640b190a4281c8802c4004410360099540b6040e4ad9607100c01000007120500803c409441c0d21002802041003240002c0c0d42e804641818505040d00c074a1841002403003030101d01c00864100c3d00b01c440440004441c0316107421078010726035160080c0d1803c2807903a400014000c04581d07110222000c0740d000d08110300c8103204050044d8003503034504401ca80900c440750080d9660070760717401701a00900c1e00c0b10b0000b03421208140d200e030259042004a0300340e41c0d10045225503005070300c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 441052194 1250 441050944 441050963
    0x303070507020a5d0311030a050d0f0614090a0b15090a050306040503040e0717070e012c040f1b1710030807110301060f08030d06090204080703 63
    0x2520016003846419000102111001c480c880d907010005a81c410080d51200c00803001040444213404000c0001403480340707003111222520b6100c2400000da844020700a2404180c0c4440d103402c0f0505650040002000080c800b0910482c1c90100384501c9403204401141046410f00c2c1040301001075000c4540c003881480804001001e26a2581045e586140e00a02410841140e10201031130768011081c42c03406504040400b00700e03800c0c0040c001c3e01450b0804015130419140c841c0480a1030710003001c0104026283c251034507803e001c2c1c88050f0044d085511200000d08120000403e45284607024281600d2050f4945c449050134070102c08001900740c07804200360300e001d10305d00044c2450041040d06509844064815a60f100c003100300000c50131602111503882d1026618817005483c080900040300420800000a034072464056803950050000724005540e2200c1c030701005441d900042041e080020140c41100580c411788024095080c02103041a007040806641c5da0490700004010102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 441053444 1250 441052194 441052207
    0x106080411101d1201050a060f05030a02010804020d03031808070317100504180203071e0b0304050d080601180e01080f030426031c09030f0201181e05010504080c06060d0503030705 79
    0x5691021245280c84034000f8012400e00810380f80080c41207114080d104d03440c4270b10109032454003107402c803a86034050b500d50201e030703c55408000388110551412814140e0f07402e21580a20384454011038000d004400171a152050b0f820090000c0d2100e903040d100100300340b02080b80002481b110030068480070b8400144031100c00c040c2100d10034040e40701a500d803081c0e1a00180903070303a549504128000213240011003540ea0b0125200c83e0209640c010a2600031084981081d8410705030180e01a805142030110940c00c04001d0b07400c00c0701500800d804021040041c07142c070604100503407071588020011468240b414103000e43d00300a580d50301c40070446801009441610820680d50054180d0b490742e800c03810140139041c000e11080307204401290804004400b91401803103403451002042030b400700e15941a6850241c01c5882614070300f22004040040d0000c18024802d5601c0307284144001d607a15201114642c0c40d08000801d0717503118004942d140f00004a01006a9400169500b080d6442c0e03038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 441054694 1250 441053444 441053449
    0xc030b1e041220030301090203010918050d0c0f02060c06040302010c0f1b11220b01031415121603020301140702070b0a0c02100f14090d0209060f090106080411101d 72
    0x405048000c3d5210100000c28001a1503004504071401034804200700325001100c444640002040a04141c00103100808080d02840108072040d1103074001c52803501c1c065000680540007000801201c2c2c0c08241000101902481801c40c0030382c2604011228890000d4001d001821000c411015041c174440078104000f0041003664900d6001410440da2643c0025504d0900011005404007507050540720034565009114400e1035070007a5240d0141d986e030703040010001c1d083d206003007274110803401003440900400b848980d402c5035486200302402d502e90700405003501c020300c0c01007a0b0340e2a80c1040c010b0468000513004103c509042665071180007488007a80c07800032161020303401c005404800c03c0f00981c0800941c20a540700c2c0c07034a004200329505164018011450016044a001d47e00940585002e050302640018010300310f8080700310b641c020810541c000e9104402140fa1030050204000d54881c0450480000347c0302801c0c21464208010420a0030402076030598003040720040030703034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 441055944 1250 441054694 441054737
    0xf14030102131212210e1501060315053f060c190f02030a1803020d060c02060a2a0c20030705010c020315130c030b1e0412 54
    0x180c0c40390408064081d5186124001c0c43c0d0894401c0782c07615410784107080e5150051042c15101144205210b407045540c0304141c00400381058010b0301d5206941c3c07240010000e03202c5c0e041c06007140e030364081a0314078a01c010017242c04541d0007070b511401d00034034a04c142d100814000b0754540c0c0090b440d805400507490358220850345110450003280100000c10501075000c50040444070002440b5001035060a401110003104d22550300006070810000e160385e5078810148072031a1a08446943e11240d62030340040d455804da09011218180ca6241c0e6100c4213806020030780c1c0c0134103681c8040c40842c001860400007800300741c2c90750001030984240e24100c184240b504105a5a000140c81300300070395480c00c40100c4e109900f07a0b92107407103101d41c0403589520807205c05250550160003040c020000010340840180000d01c1c1c1c5450780c5000b28031101240d603000c1010010360040c0d5001100b400c140c02192031000840044000750200041440000752240341801d00c3c03420300745016544c8254400400200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 441057194 1250 441055944 441055957
    0x209130603110f0904051c050d1505010215040c050904030507080c0a0615031a0c090d0b060f012d021006030c17070b040e090309060c010c030b0a0f14030102 69
    0x500d004030200820118000c925001c01c0c084441401c014060001c0001c000340c100d030000c0040e04582c107056201031416180380c0c1e0300012400c0540c01c1c40c180d00208003c4a2168001d14025031483c00200455601804200c0c2440188984036a8518080d103404a5140b02441594003848401c3d0015081c1803280058a03440c540c815800d035a00c02d4000c102c6030f035965440300d054410600d0410740e00c444668241002c000c0780ea002c04051004043d64801c0d2400c0c0351700030000303021020100189401d039502d8183d00e14900e48034174026052401e11005100694480c1080c0c681445010300b008800051004911007140411001148080d40300e001c2c102e0410728942440d4600c01c1c10074501000f000b24641c001025100c5400c411001540c58a0190f55644814411061400720801003805908406040c03154024a400c044a1401c0155804141d02e40e000d02041c0e803041c0d5541242c640c5c41c680c18040c04044c1e2204075000752059081160126022656200c0c103650505414504002c5450a4041d150b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 441058444 1250 441057194 441057229
    0xa0f0c0917073204090803040203010606050406020a0201080426130b0717070303141305010509011530110301150e0a020703090f0b09102307020d1506050102010f05040b0403030209 79
    0x5d03062892038128010f1300140c800b00d00c01e50800f00c01040c0140701e50280c6040f114140d00800c0c181d407068005442c1002d003c2e0040d5000309200c1802140704003100d480c0040c200242c002c0d01c1e500c1084a8240d450942183c2080c43d40500400100d008122140300364a031550110381c00c00e40d202c01d64a000d800a00c1080700340300b400c1d00c6010820114800c101543c2190700d010310003e0007281c0c2c81e809250300300e845420318012110000c600c2484030003c60302c82c103131b5050b20301b00700710b207681036003001d5412880c299220072500c120384501c0b0030180313040030300405100d2500800322170b01942c00c02c41103c030740c00700c010648a5110b50202e0185e080c184606c50300c2009100e05040e070f98489480e605154807d0b4401100240548220000800f0891058000071002175107405c01554000c145141814150300c601c809a0780b00c0418003501001c070b00120505201050304c00c0000903d140790600190a591041d003070000d03c149013004103c045080b8512056015074980b0b40140e4640e24100021210f298000404c03c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 441059694 1250 441058444 441058451
    0x3020c0c090a0204090e031c0b0d06050f31110604031a060f010c0c05060304020402090303130e01080a05070e0612030d0f051602030904050a0f0c0917073204 69
    0x18980e103d078002c00c140c491001c0140012a298010150381e4882c0030021182c0300f00480c407030760b0541081c3c1d200d09070f480304c0103000c1e0034007001980b40e1380c00b59a42a0303200a91400018203104950340c1c0030340c9100d07003e42c1a0b00400648001c0d404601c6ca84c40340450f02078100c095002030075405645e00c10071a800355074072420340f80c0c0c940e100017550300f0151070807690103011f00b41140d504c550640c0100340b110000c03607101000c0300c1550304100521006400191040360455020302c00c40c03202c3e913001c0c409010300380001000402d1403454440300c0b00d144201a1300104558000003018408140c0c00304200f000d035110f0f200070042d01d40300e40000c00c008120541290b8140d0001144002000b815508907142008481005015070707103d480b0308041c031800c05500400076900c104006486404c04e900490790080110000040000d0385076409010b81e4500701c3c0020004088240c28403444013400e03440b010710a01e200c02814000c0c10200c0c44040c9000c00120450b800a038806954501005003a540a10400191050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 441060944 1250 441059694 441059701
    0x703060603061d1e01060f1404111306081008010615080c0a09050d031416020909060f0402060309071a04090b040e100b030c0d03170a0b0108010603020c0c09 69
    0x250014201400112049810980080e9a41d10b00d080f010140200072400b40c646002c0072000d01010900791007a40f01a552900c100040c00034001d58202c00070140122003290280c0b5030b10410040382d06004042c0460f110911150161501c204003000a07681c0a05240d00c03940c42d5502c0700c02c0e2029140d40108155800d15130085240000304503140541c40700e5445001070f41d00c4080c5421060301481040303034001007502004200514114032984481400b909080242d04090804010258451001203081c44100100b03101181055840aa80580150f001c1c10700c50030910500102141c0281c4003910400c4080301181d40c018080c0110f0700148441651403030741c8800c00c074070740c00d40d41c01900c592580180b40c05051080ca0070140240741d0109551030141001002007070424009117113141da0150035103d4500780391055110040602c100d00d00a403590507500f044840081040e071001441b07100c449082c0b01a200140e600300714200d05650b664200541c55000141044c0e01d41581c07885425400081201030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 441062194 1250 441060944 441060953
    0xb09220504140712030503070318060903050a090605090603040b1f1d0109090321090c0b121e04031d030105040b09210d0207030e130b04050f0603060a050a0e0703 71
    0x1484548500202030f640007555402c140e0450000e58400074001c103804100041502d0701c2035000f04199008807038011480045a1105811150303810011404100005001e03520a030700310782c1c00c2c0010f041524041e4a88194040410610f020140c0010500300b0400042036071000300d4560442400d59202c1c088035180d644841d52150303041140070342496454100004940100d041c05407003c2140c141d107550810091041182c40c0c8071003082c0e29480350f183e44481140007c1d00d01c0b041c22000700f1f07400310880d840e00d121141034a5045000350000310780607180d071707120003142c020603d110354801d415003852400d07141c4901181042d507068034292641075280c4000c0100708140c211800b401801c0080403146141d0140100b498084940414010b890005100982d165503a80c1c00509809219242030a82e922110010900703da80708242c0004442e20b4508d0114682010b00c03070ba5500100307030303032550019003002c03c04030340c80720400703001d00490b141c40b000000c446484582114503294021005c1b1000103582c0e090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 441063444 1250 441062194 441062213
    0xf060b06120a02090117091504170d020c011112070f030204150302071208011202060f0f030906090c0a05100e030c060d0f23072001051914010b09220504 67
    0x24aa4089000300d404259220b02603d00544101c0300c205c01043c0d01c4018540408003054014811210000c00446074ac4985d0300030409801d03000b03011280561103240404506095903440c1400507a402c40620030302c0c5403d00d904141d607800c40a139080a02c0104c0325020110080d00c52174114641c41c1c221801e2203580d03240c0c55401803014502504030b0350481d0450040032108441e080c0304100c0f00c9160a000c510142c07500b08000e1a0b00d480503440c02d03103002c0d40d09001a0f903d4008403000c03071560f000748041010302c100510110310280e100719120806141040009102d8542c00c1905070300708120344076404d5a94034200300b03200342c140340104042d4656403491110f42c00307012905406400c040c145804c00d84445581401c1c1048440c2c07442d400e10169032540781c200e41000d080d02001402c0c040710221046405400e2007a9030203200e00300e10b104407514000e00044181c0340103200140150101d000100f0040c448001075811038030007124a0396400c076a00368582c450401c0280c032401114509818041003055036007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 441064694 1250 441063444 441063457
    0x501081b12220f2006040b18100e011403041203020903160b031b0408030d02070206040e011202010801080c030604061d010501120204050603030f031909120801031e0f060b06120a02 79
    0x420798110200081350302c410000c06105590010030901c018041d070f8036500d001c0c100324a0108181002e00030580d000030003120100d001100495400342125032196400904900d4180707541c44400d2440c1843e5480361381c054202010601003607408200120749940c14004c403100310550200115015807180d10004040d4070903a0081c02040300d0000422000762502c0542d001c03990901d000d9401e040583c00160003035401444100e9002c501004003040b149801c0518601a208403405c0d1544103603031307100141015006800034107160f40905c206151541e0000751403a8044c1d40104003117058040c00202e40200000e80b0310480c0e0399404d00c0300218034003000380c05003800303e8003c85082c040d946919060540b24403c911940b208548108001000e202c119188030b107021108980000d200496515000d9045095004200004150400410902a01d8200108810307000700c9414030001d440da07541d58116410301c0005205940725041c14945541d40000d556112803008140c2c2400d00c3e18181d000001d61050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 441065944 1250 441064694 441064703
    0xa0209181e1c08040809010912060501080d030501050306130303020c010204120c05040e150c07020d06150f060507020d0c09061d0903070206030613110a090501081b12220f 75
    0x14a01610007080708546151403905403640300c0303d503d0703e03140d11142d588100c10352810701a804c0400207a400701c40310000300c0380d4001c420000d4154100f04d49603060510609404007010f041c00014040d660300841e2080d0881c03581c905110310412585001c0d0041e0007003220443c51940701182c00210000115a00202c10388503508080c04181c8600402040b140400b0b89a11941e00811030400b0041040c504e56401100d102109418521140e0008000c0802c00d60100e6081e0f840e001c800911500403000a409080c25040c040016400c080004103107000d09003010344245e5502e00c100e810301014015000150115103030900100d505c80310580b5100344040303400c0d0021003c600004480701400b0040e10603050380100943c1c0b954945008000e80c4505080000310000d40d540b80101403000c100002b803208000941382c0164107403826002401101004204e410888004001841012409400c8800b050080c407007146403520b441c90703014000413040c05d00d8a04480d03443c0142e0705121380602e00f9076449103c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 441067194 1250 441065944 441065953
    0x30c02121509060702070608091c17370b09040b061201020406050301050f031501030b10060c0f1407080d0c15020a020d030b030c0619030615020a0209181e 68
    0x400da046580c9103c21269000103812000303003480018810003900347c005d1001001c54401001180b00418551072031800900860044506108441c1040c1880e84e4024114468480c0410320080700d40700861011000c001800003401020a030140c5c194002c140048c40546507a140e0300d801d2904074000c0109684403846009068182090344405000b128252092a6142810340e46030a040c403039844426080d0300e60600803081ca130f030b05280480d500f42d8000c42c01a00d80c06144d0400076022441d003000d68201c0c0c010010001c186001140e0300c40b1000c5082540007100d03170811089221203a00303007012034001d012503014084071010f04a82c0101031201081c0a40c04007030000c202c68040c1004c07840f480440d036001d41c1001d0b14024440d40240d2102d401840301030b0550701000182400141c032079024000c5c0c940070b03d040c41d02c280221a490710074113024140415441c2003410141001079a0b40405641c020b109140542c001800008850201ca9003c0280c8040b112511740f0546034503024000d0b1340d01003400d03200d03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 441068444 1250 441067194 441067201
    0x91810170c0909210f0c1015050102030406021b0415180b0f0d03080403020f030406030207060b010306050d0b09190302010f0c0816110a05030a0503150a1809030c021215 74
    0xc011a51000c60f00c11301090550382001284e4034180c94100e0301d0030700c90b1076406105c003c40118060088403814100810300040c404001c0d01e94200c403d1503500405c1c110f5100780401c0c45401d030000f0700707822076a00501d491000801c01c000001c0140840c0a050100c2c0c034464078001441c01c400210b030501e440340204080c00321500a40034060050503c18409501032019802c00000c13901030706145030054000d10540f80b034000c041f000303285154030503801080004c0d80000d000b018404140f00c2c0094038030b02443c0c11f0085620b014001100d9074100040600440c3d283c5004c20304205041150342030a207404454014141c5d03031390502900070003c060700991041d04210401c08030a1103140f44c0d0f031203100781241c81c1040d4051220304a0b5647c407d40510503180c401c901988011403004c0000d051f102c017142e692107a891905800100401011442031030041d0588072041c441811000510b0142a021140014601d501130600f00c64540302c0c900d01135009440c06049680000011519812071010b030a4442040c0d03c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 441069694 1250 441068444 441068461
    0x10e0903120103031206081b09150307031b1a03150f1c0c05030322091a040c030f05102d03030c02010c150204060801060203091810170c09 61
    0x3007180c0e00240320000d00700060000034040c01c1483c0050400d8100000c03c1500c3d032650614001d0340d0542024410165080201e05d4500f020216920401404c9540d1880c241140401c1c2d9407040c0340001425030002a02c0c034112803841d05000780040c1601a602d50820840841700501c9500a90b196030114219001040e00c03400e00c0c455440701c008020301038000240180c801c0080424864004580c0d070003020100140c1541c08002414105900700a4010b581100c1e400340004d401055200502c11400c040d003034107114107100104803095400741e801095030010f181044000703103000303a41d49807958505018444d0400e42e800040041d14034004000c0d00711200b0386c466171001c40070f040f8801c5410070750403000d1000078418042d03100c0301441070409100b284034581e1055030785c1040d1440041d90f164042410030440d90720240d2030340102442d002451401000e580807505e081d003040c00202620480d400800c0c03ea5240c800c108005000b066010720503080750a9985440b5a03c440ba0b45200c1c200e950701094a44e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 441070944 1250 441069694 441069697
    0x10905061f09090b040204090204090e06070809060103020405101206091704050d08130b07030816050f03040b27010b030c04060f090c021603030215360a0218010e0903 73
    0x541c2641c6400140c2c500e400761a002a02d9040900d94116409100004036000c01d400030f03002034020404082290f8080c1c004052429800074070490400c8034080901c00c00000200300c16040d260140c03000300e8196203c4800100c0100740394080300c0b501800d103c2c0b0130f090166550103100745038400c1e207810350014000885d094480c0984d00540754450036032000400021a048010a400400740c41c10750003499580201c0c0a081c3c0055406401052110007005420f221900048000011504180303081c6070002c00b1884150200510041c56081d1400100700040410030301480f50840d5140d400c81402d5900d81c0e143e019101c940102030107031207560303025030443c039150141c1001c0c0c5003804a0321000510300041400034001112050084d405046422100f100c1c0801e1480013440c0242c0050030741420a2601c0800d004004044407180202064222481d82a070003041000c020324805441c601c0d01e40c0c4025070b0801c80094402548048080d0003085910300c059034080c100d0b107081d0741d0203d103030340e41ca1245a100d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 441072194 1250 441070944 441070999
    0x1b09100809071a2b1e050609040f1e14010903030501090b1c03090b0d0e0c040b0f0103110c01020a09060f140a03050c130e010503010e190212100501090506 68
    0x1041801108001c020014802c07216420030a00b03c001003001300c88020403618048a10102c500100c000e1805540740350060075042036094a840c0d46a15158407115008030005400401000c0e8150004036601715034880684490341041001ca45c0c00740c500b0303c0d0390090010500071008641040000940802103104070304a0400c003502d025040f0700c0340c5461202a0100380012824014552004070382140008054141664800c1000810300400a115860300050b03940c020300c554245540b60790603403641e080c07031340c03280e0800c4c24049444005420189820f02401c4002055503201085541c000d6a01a50300e408592440e218040d80c1005080202d50000d040d400304065094104110203045101e68411a4000508207000c0e05160b001c50191040600540c0120b03400da05250051000c0e107020b21902905009060080c509410242d00e43d40a0041c0c00c0000307031144d000e0f4010900701d44002e000000c0c4600034854100125a100e080b440c1c003c200a0710114003503601035001843e20b6902503040840f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 441073444 1250 441072194 441072239
    0x1020d0c031e181716060204050913030c140106240306080a051f0b04020c01061a070b01050405070e06040305060405070506070b1f050a120204050c030601081b0910080907 75
    0x18602540d40b10600c1151500504d8004d080c0c0400000844403218000040382900c01c4c000075030b0341d501d403c0400142c0c0801520131070400c0484001940000d4110960120040e802081044c45e140d4a540c01c500401644d40075140300d42c407038004200641d500c10760161785182c0b55101000240d80310b003090784d52800c20150003032050b4045180602080d00c2e802c03a50001d0106980c01180b0921035601240581e08031810748070031b50f9154041404424410b0a0192070311425030503640c02c0c01103d40b1440b00b80d41061041c5400303542d803a00442e8065200c0c0481512012010302010382c0d030b640d00d01d003c2da41c03020100e9050712180142800451589021400c5a8005400012404041d02d9100c503a851303060030108840c402c0e1641800018481d01d0300e03401c10006000704210b00c46048400d0041c48140d900050440b504603408002304500361781c000349420340004854440d00000800d62440c1902031142040c220f81c083d0840c038403c1d890f02e034045a81c074410710307250056442d0181c2e41d818040401c2d81050a881 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 441074694 1250 441073444 441073481
    0x40b0d09120c172a0f0601050f0604120203101404030f02030a08070f0207030b0c09040f0c08010b03041b030b0108160302091807170106080f071202040b0301020d0c031e 74
    0x1c0c203400d003460280c0928070200d104203603400705203010128000e8801410b59013507001000c2e8814410010710640340104420b9444940c0c101803007001808612480c002c02d18480c000c0d000f42d00564408214007602c003c0313840c000300700c1c10746400300e4072045403000c0301c0c1100094001070800071440d00c0802036481002190700e41c1c403580d0b100c55005035040808815144110302c503421380000481c4144100303a000e03101014103030707940303000c60000e1000b500c920003212003109040011111007540c0c0084224119052000100c1c2c4a4480d0700c1c0c40d0b24008144022005c40401c140400f1060044600003603040311494403c40700b1012030a107944c00d40d0012440080e501210b00340010f1720351400510070036422010742c400e90b101141c449800c0a0300008820150070107079906d080034460404100070b8407001041c207500901c4183e00c3c0044082c528010040028003498965100c103030306407425010360741d03401c8410301e040c010807516820007801040d0345400c2d080540010010007135410b25510031003440801072126107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 441075944 1250 441074694 441074723
    0x31709010801140609150301170c1327060b091e07110c03030408070e0106170a0c142d1e22030b010503010515010e100203040b0d09120c 60
    0xe0300b800b0f11001d400000400c04081c66540313555080300303040f122000301c644a50402c0601407180f81220780780c068a41c0441040c00c2180c0c3e81301d402d0304d91100100c2000c25400101e20315082d100c0f0b407080a10400408401890302001082d0708100f090841c103480011a90b45d171034480446900324a400004520741039404141020f10a04680345c60800310700c04ca5140542c50408640b440d071160780b0400b22508540000d02004433031010541c01415546842108003404450304e444c80b50b4094007506001d0350f00c0350301c40080c41c010001030214040007011903440311024411142c440324001e07415085212a070781d40d2001c0c6046801929407030311840c00702c01010062540c01c0741d0254428030b88a05410360b40341303085d69802903640644000e140708140c0707280c455241800345800d40c0e2018001c060a568810b070194942d9030310150700111207004485c80c501d211500d82c4141c0c114441c54001c844a401e00040a48880507190012080144101000c0704095038402003100c022590341c5009000d0303d5202403a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 441077194 1250 441075944 441075959
    0x501081501030221010b060c070e0a050408030a150b04080619020c1203040c030c03150b0f15070204090b0a0b030c03070f05060309010b090114090612061b0f030907031709010801 78
    0x4018501e41301c0000000c0310001600040d80c250000c3c0c482043c1a4807a4505002c0304840b90aa10b40000d0f04110601603030030300d0340d15000103010050030340c1d042950361b90b048034400c5800340d1400300421640c43c0403030b6565100c109075522090110b070810b11a07031500300308010300500c0e8821100d03004041d10240c40c0b8411051081d9496510140c000e0b5801d5941c1d08010002c500c050210200440c858205201d4800d031075036400f802c0c0c4401122076486280518405111070300c541c05001940850100d6050352898140b0000300100314035480a0894504813040169842c050707404a03007148002c90031100310300b021800301541c2d100140655031409038150820800f604001d0099074000d01007800104141001c04049141008264005448040d9010050226051070803a0350f8004405640c0c0901224110004a9907036101070840c80c01d0341a8032600303406e0352403041c082c1d410030500c8847d459568240500c1855a507851400162140a40414080d2000320740074100c0c1c8090206855034101c583c83d0041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 441078444 1250 441077194 441077239
    0x6140f061011010e0d08070207060504080a0807031b060501212d12020309130504030215060d2411040f061b2f03070302060304120c051005010815010302 67
    0x1020b095664a070792580d000c0d5841400484000c17045551560628078080000914040190b07014005000c0100b009201c100d00100d800c8415580020046580e86c8961030f0032102d4590b200809409002000250820000650041b034100c90759a0080402001c0f00a9003030494481c00c4e400a001c0300000c0142400c0703080f41c1e141c0f00c40c03040381070f84120b11400441e1140000c07a91240489001604001409840b6282c400710030010100f540030100003034502a5806580c07210f16003003517031002e480350300042c07d641d4407440340211050303000da504411040780f0a140030f2094100031a0400883c00c0c07244103088580504150303030468041100b070058139440c0220989501085c1402c0301c1501c4a001511004902e0103a104405241d11301494602c000744500c0c0c02c1d06403e11128120f02c6a0040c80c1c042000d6543e80e0b0a8a13080f5070049170804180704074800c1a40e100d00301030001000c0b4020702410088519169100504a9040c2016901982851044a14580e2090000a43c0f00300301840076070301c01950342c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 441079694 1250 441078444 441078467
    0x60f0108040f1e1113180f06060503100905010e010920010504150815150f090406050d1b050103061a0d060e09010b13020a0e1002010f050406140f0610 66
    0x10140c3c081c580424264182c50a4410380c280d03600000c0103200f900e00d0401800e10560461110800c100b00c0c08200d80680348005080ca000d08025000a440300074000d00b03a0000004101c0102181c3c4190003150316000136048100b81a03a00754a400e0595030159410f000d881e007070580c00030100c2c1040800b56030340380d1401e030200e000c2070403c06c1c103001c0800c6d4124000c2e165070403000c1c191221040d0340b4080078456540b4130b219030524024104d4a000f4420049003800b0741c0d01480340c1059040d1104140310202d030041140e0b82c030070340c3e01081d004100790034000c0c0c01c01003050303041e00c80c1d81032102c040c6c40303000640c20341d05070f882002c441c00e01484001180140300303006004d04410a07000400d86c50f580e80d001c1715103c1815556034407643d5441c00c41c9542032900721500c07007003424504020360801c84100400b90400080540442c090544030501d0b0b140240f00b0351001047c2d40c1004c00820250406051280051030140f07108031440381d000d0041240c1c0c600800d95507100302d200030600c2c000380300007560031900c852808 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 441080944 1250 441079694 441079703
    0x6080d020c0d170a0c0606033503010b0c15010e2502060c0d14010b0c100b151e0a1d04140a0222030f0302010b06040305070905070c0b1e060f0108040f 66
    0x454030030300007811b038050705000b03600032014940c100d01c1481400c001c00e40e041e04594200044040200000e40c140350540f0704498409801c01d45500c107100f84d403800c0441400034001c42403080800401d442c5003040e00c55001e50658035040321507031070048259888100304022400541d02440004005841d048004d080301560030202041c4000c0d0070381444201c013802c5c1c00c2010541da010075004034452081110841045191b41e0600400303140d00041000c91114201c13030815202c0000d0f0800046000c1002c1801081580c0c2649554180400e80140110300c44e00c0303494544815510303001034902d030600611a6400c1a402d003d0341a84840e45800002e5003da80c00290b245030000784003120446d8060910011405413409640c21f075100d150003030840d41d5014010384600c03400c0c8401c1c404034031700003004010341e140001c00143e01c0d180c600781644d041c6003142c1e00420f042e14103400c0102030050b141e0030310345590030348200b50901e8888508015010454544080c00900c00f4800280801d6200c1103510030030b4040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 441082194 1250 441080944 441080957
    0x9061418040b10030b01020c0a030314030604020c120309070b030402030c04091e03120506030610030f03020c0a03031101141b03040c031e171309020d0b0406080d020c0d170a 76
    0x1c0e1400f01d1103a028140382000800e590340c40060722960140910100f00b00d0488080232014210303540540110000c05c440310741100040000f4025072126411110442024000ca88442c03e01c4d01440d84c40ea4030407107911045004ac00c3d0b0010740342c801e171020359014681c010301030940d1001200c1408020f010740b5038243d0b008012054240c800d0090b042038444c81714001d0303a410034180d424140a10031789d1400fa1203180a940040104042d200c0c0b4a420f110903030b80d108070750030705218403400c1c100c0c5480b03411060580e020a00f00800410541c01c4080f5200340c1d52060f00a001380b040c40c0e00302c00d43e1608101c42419802c180d1141c503024070302d0710000450f4001d00c580c6060b04821b849031100d08011060b0303021102100001c2c46d441c018480e0000d424400311b45046855454500d100d030340344c203e68240b4822404034a0300424100c40e96030146e0014140303010094070801201d950361001654445104408502500403429940c090342030503100800700e9500940b14855048805c007000440d40e001d414004100b2030b9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 441083444 1250 441082194 441082211
    0x60103050a0f05090a0c08070302030c0d05070f0e0f09010606050901050a05040b1201170304150807030e1006090b091003020613030b040c030b2d060d0b0108010c0906141804 76
    0xb0a44540342c05843c0f5500200300c00c0c90709280182041110b5046201c166010010400050390002815a14a54240c880b0340f01106c00d860401c0c603010395070b00180426034605101244504101401a1081c0c151040c007001c00c0c0c4954503c0c44c201c40440c000c10b00003400400c2a100342d5401180140098001c03460714500d466690341070010b69801024078400c40c0e10702d80e0010010581005413101010800740041c600d0140f41c0030000380690810030010041c04411070000340000d01941c000210f444400044d10340f900030300f0507460300500d0740b8011880702c50710304140c0000b035007410301d0381c0c5218040b8494003064440c2181c0030099a070b00b00c2c400850240465400100000c0c07200da600501507440f0701d4100f03500c14258a060340d0b80d146c1c014000e5140c80c42488070840c4c1d401117801210480a8440c00b030fa48981c4078040840c01d0b11081c044c024090039140c1e030000881650540c0510003e485907900d0340f002a40b070706000c41d045240003c140d9103500d0240020444003031040c0c10784e11000e500920010f074000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 441084694 1250 441083444 441083471
    0xf0409050109050405010b0105040617060a033009181d0703031112030402010509131803020c0301050903040302031c02011e33091d0303250314060103050a 68
    0xca00741c0003154001e407528144800c00c6000d000f084403400c070908000e82010b06108004029070110704034031a8907400c11001c01c1a0744c48068900d40655000780c1e49401d10012491740210601e06640c80c40b02c05030696814012080c80303221600300707440403150340d805201c0d41200444007914201212010b502099009010040c00820001005501c6a02d8025203911519000c509240301440d11252a0742c04008010050b030b4030604541c0c031200120f4400b81c00008800085c0028401104203268003040c00010405064000130451481541103000344103070340d14001d0b00d580340e0160b4800250540d0020607516500000d030849443c1840303051000260a511010520139001c0d580b0349010095a50ac0c0c0d0441d00b5003070310b000ca1049008480000d40c2c18802e07a808181c400211502c1107404d503036075603002c1d01e0954503034481c0411454240c400700c1c1c1e11707818254500160f1102c1411b0442420490301c0712042891701900a54446003021802010103544e00001540948002800b4884490380e62200c0b01041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 441085944 1250 441084694 441084701
    0x10020702120a0b0702011a01050702040207150c030b09180c091e040305041e030215091c1b141e12120a2d03021b06090604060c0c0201140f0409 63
    0x140078403034030030f40c0d400c00340070190854940120f258035000040da40391500b641c01004680704280c0c10f40d0300503a2030209040100c1400c01c400c41080e141d40c1800b003d0040940d15130402e15031014100c681402c961a480044200e250894042519a400c2032802000398a04000e080f640f01203038410b00d10b5070400c07200203014030950440e81200414008942031100443c2d07120f00142299010300001001c3d4156000035aa0003101d41c40703001e00345000601c0c0307100c0b9112120490090341d20129041401180b0f458000c2c041180008102c0200d000864005440304c40414100d190100c081c02d204407a2621910941070303562103402070303508a000380c3c4100e08205020002142c0002c2c48115040e111f030a421002410030f402d2380c44001940660f01c7c0c522184a0000d8000c000090041c14010703641c6204940d10400c030190f140e12200c060081c002004540c540200d081403155124010400540035444000d48850f115a10043e0005401c040d980144001d40c074000c0600019140e0041c0c20540e5481500081d1b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 441087194 1250 441085944 441085963
    0x50f220501090f0e01050708010512030405040203010308210417030705070218060415240c0215030a061d0601030c050d0207060902210d05090a05100c021305091002070212 75
    0x50356921288554001c82e60311642c02101e131404001c4c405401c03c140018000d42040c040c45114852586200c8081c0c1000c00c1154000c00000e00705544a680d00c0c100000a5006581e105a815072140f03c200e050300034030082544201c0d84185c2401150a0007085202d0307980006121a0502c43c0c10003010b00582d0381c50340f040032000240c02c01d400c0c05241810900080d03568858145c5030010000c0ba007801800c1d003400c15159810b054000c400c00b0b160106404a031007a02d141c4d000b941220141014501030400c00c8001c510075170302c0038024040780784c2d1140c0344620044400700d6022220075260100d400c542c0b09800400140340300c0d02d0054103080b561a84c600407a0b001c224103c49159441c40d0307440071070820480d0b0008036038030440d6550903104000f82c000d407103035596101c1804001c0009080c1c001541e4030540b0382d0160402a00100c1d0324059800050310301e0740300c0340003a446684d0740079000c88260268042d0354070941100002e8002c8500b0487c6600180d080803d0407a070001c1c5a02d0328002109080201c240c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 441088444 1250 441087194 441087209
    0xf030a0e130f0f0e030f0703030f140103121e0e06030907090608010618050f07141c02220510050d0603050f03030618010e07110a140c030d020106050f220501 69
    0xe0203c1d1801c0302104480381c500301d001c0c458000b03120f00420841482c0a546201d6014100420142d40e4180c07040c000b0501c0789041c240d080b05140000c018081a50341e2030003085016100c461010b407582ea00840b0050014080c800010364842280e90b55061940103190000e602504035a0717081d0700c0341d200f1026140141c1015086039500e16007007180400780c50030302280e5140030100304804e082c503510f1030b0000d290080440d414010340f0009184021022012911140c0f9844004201c0c060300c1041003000e944070651083c00c404404416a03020780420342c0010481e03000410321012070541d02e0050ba403580000342c03280c48845c0d46d44400808148240071803000102943e02866036880c1c45004c02242846151054603180070308001801201c000c00125900304555080c801c58070710801040764908281100000c11004035142024255080010b0f0149030103022030950302c1c1194540d00c12800c0300c8461240c15800800000c100119040101111643c0302d109500c100c030081e50354080a003920070070b901c10360 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 441089694 1250 441088444 441088451
    0x40c030f0e0d260a050907120c0611030c06040b100815040515040c050f06190305040302060106050703020709020726030703060b0901050706050703061d0105030f0f030a0e130f 77
    0x942548019114242201c980b14601001c034429040706000f0b8008066909007941d450104801d0710003000000c0c014800440f511078071003100d243c00c01c1080c00600c6800040b5984403840c0c10b0120000c02030754080010074000b0541c0707603107a031240d1010080c044d00300d54019100304008920700d24203010000210b5440d071001740107410300c2c1c034260b03242100918a440c030f84e40e00007040c03000141c109880041107a4080340c82d50307580b04144001a0b81c0d4403451040c0034030240810309141180e90035800441c4103a000f42c007a504942e90711401501d4038450040d00400507000b0f007100340201815580600103c2d8091a19051030320b4490b01202601c8489400c40040e4103404000c100505905000316800b17044416001c42c01c11640c0da001070441d0048100041450340c44800140600d80300381e1050000f01a2114503240c58294403074401e40d803040030701030103010b4000d03800c4882c0156000900390081550180085180c035055030790071240c40c505002c11a611041d0764144480301503a601a19094104003003001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 441090944 1250 441089694 441089713
    0x50d030c050705060901121a0409060902040b01020c1804080702040204030311011b0c020108130c12030311030f04120210050a0c1d1e03030f12070206010e0906010302040c030f0e 78
    0x442c82d251103a40a035200da2400c00c520241030b6400200c501c1a009200400b0400e06149090007078130784064000581c0140c98004c10805001e42e43e0000241c140c020344e410041040035500480c1c80d0590540c6068208402070845a8113146a0041707541c094011f40310b5a0405001e6030004081c6c0e0710030384c01a40080c1c80b00b0600d2008800a214600c0e40c1c00980d400c811090080400180c01d0044690b0040c0c10f1101520000b02408000d540d91001290301c4800a44465151114050b600d4080c60003603000a180481ea00e65410400f011680948502d403070108c0c0c01d40d11a502c0342501c041c08140c0108502038600000d1448040f402814062003568601080b103040c21070300142403040e01b000840309481400e541c3d8540d91144542d403500b90307484100d001c05038510036012901c0e620411000080d03c400000740101100c0c04081c400303002d4802c07503081e64a180da07950f142c0c41c000d0300e00303503121003c45d044440104010f00d0305a0021010394050b06001ca02030a1150400c4201c400c490100151f641100c0b102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 441092194 1250 441090944 441090953
    0x10140906010b0307080c0318010c0504090b040203101a13030c051f09150309080f0703090e16030b0406030b390f0f040317091c0b0f10050d030c 63
    0x24603002d080d182a500b0304501d0104030003804280042d162840031180000840e207484180c2c0c48060b0b040c0e111a0090020507103a8900800355441441200c500303502d0403560200c503113007a0080f0380c050306640c18241c1e07040d810400e440c3c401c800c240703010504a45080144050041210702100025400303200e04115140c40d04e414010382120110584407071004c10614203204a812120841c103440040c0c62810030318018140c10b030020706900c03101030310384040480c0d00040e22080c0d00082110700d201c5d50707404a4032955035403c824a40c0b001d84001d4000c100c40d01d40c00951318800d5100c54052107004201003580c0d55070f1f4407183d00842040e00c828001010144200c0715002c80400410208104240e807101c0b2b90031030303010707030f52403409401e4403c6d2602000162108041c541082910b002c1d60304401c0103003142040c0000085d00e980300402c140d0241100da40480416504103421101d22034000002203078030380e2008a5945401d800a2009100380c0308003c0102d9151290200d04d100f0901c01e4071a05811142401e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 441093444 1250 441092194 441092203
    0x918070212091f0905060d1d01020f030c071b1409180a0b0417030c040f080304060f0309170301170115050a050d0602091f030b0307140d05101409 64
    0x8050000d07010402c094041500c558115814090321074000101c205408101101c5a01c5190300c11640484049400004004503900800d03200301102d65840c89041e2403501b140c00e0f8000c01c03107200e00c7c0e98014130000310707101c90340c100500d03c19208a0001f00c074207030200c1e061103583c00190400001d2103004005800715061101286070005510744d14494214003180d68107581c0e100c0031400504c0c080749040424100326240070441902c40b0915400b40e02d03403500008210154006128181090400d144009607620002c001c69054031090b541da01b207542170b409020b5001d0400b000044450030754044aa403591512180a507003e031126181b2440011001d54916007543c0c8a0002001e0328100c0c01400c01c410340e254040350b803c803102680c040202c150305081c044000d00076072842d243c2100d2000e250441080860029082000305078508108841035102410341ea10307124061a0b55194102c0c62140403440d040c080340b40c403e485641103504d040c86409490b820344600492581200c040b07a010b00051800501c07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 441094694 1250 441093444 441093463
    0x30806090f090d05070f150507170c090402070f0c29040b0306010c03020a14100614030d03180c0b031b0f0d020a090518090706030b210309180702 64
    0x264520704034204441481e031140070311102c400500070005a4071040190003003810f003c0f40c7d00168082071245180b010b0360013800c01154a00001441c4110002c0c06402144545000d540c651383c18a00b0510b058040c0002903001d40001c5c0e90b0301d8001c0403003d0000b031413903001c48068500f81d009850049040c10104400e01c5203c04422482501400b0500c040c01101003560b42c001002d2a2218800c0c06509080c1d040c82c0c01c10300054020030141104003050b05e800581044d8640c0000400c12200343e0b10f082d948070030a4041c0106d93705401c1440145113041c0b01b60030101e03032081140394020348a0110380e0f03069106800c076800b042c0b1056000c010400c07034000404a80c6404030026560700e152009120a0490610030f100034141041e9007c149806801c1c840d44c00c18000d80070142500c4140e040351409845600d50864540e07203a40310710a000b14a582c400d000c2d805401300041c0442c640003082103464001070701c0320040c0d80d40754841031002018035600c6181c01c1140c6007900d0b02f9215603091014000b428030b806035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 441095944 1250 441094694 441094711
    0x306091b04060501080604050a09081206011803030804030f05130e0117070305070b03100b03090c03010608010c231303030f091e0e07020f0d0203181c0312020d020703080609 76
    0x240b000c00141e600610440d5000d103003158000340707e558149100004200c1c004001d40303200f001250481c01902844442405040c1c2600c40785165004c550035040c16a00c18080240003d03e103002040000340100c0d80040030910a0a150b801d0a8a540300c41405088941c80065a80c1015004011052000d070742012406111805441c1c49425901c409550301014800c4164514000001408008101c038919010b4600e290340306541c3d051082d0115a00c40a1910003807080d4a0b0142c00140302c0c405104c0c009008030300340c42d00b40e195528010401101e80c0000380d442c250407010001220404142c6000902440c844c0c1c8904002c000f0643c0028105030040c0c001c0b10300641414603244901042d02e2414048610b00c4505095a594105c4102e003408041541d1a1040c49108503c80c0000d4002c4040e0494002840c401580d050b04001000380924842004400400c103c040320340100303205001b11031407260003800141c50240100c4800d812a8004c0000307078002055007051201a01e4001c0001d90010341e00b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 441097194 1250 441095944 441095951
    0x1b03030a0207380301181401060e120a08040e0109140118180c23060d05040f051906060509061305070e0a0801050114010c151a0306091b04 61
    0x24020b560342c080c81c0039010380315400025011601d040080344101c07041841c00903044800d400210b4401c140c200380210325180d8000021085102d440b0700c980300d040f0502c41c1e070900040e46000f03810741f400c40a00c0701c00c6810080e0600520b03030016080001d041510300c00d050041d540ca240403103587c3da030841a085407500c6406c0c40c0c00119640c40d11814181540c28101c01c0f02109180c403180e840040114805404030842014040d0051180ca409003404581c0b1000003181940020321002080100701410203600880c14820b821702e4138501d510143c0d00c68030074030348000c0c800c1194407190300c0c2c1450719080780f80c0d546541483d842080058081c14004003016120a00b4074203010001507094400218080780803503441c0300140c90a8070600780071104110190909100300d032901e062a01926090046000400c41442c5021840d4860030301e00c03524582110b0380908160401d029040504200c1c100d6240c2c0310940015074009650038005030307001e1700d04040105a04285c080e00d180c2441104540144200d24 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 441098444 1250 441097194 441097207
    0x50307020d052808010807090b1c02031f02070c06081306111308101109130e0a080a021005071b15090f0803011a040f06030e1203091b0303 61
    0x800095001c40701ca814140702c2d4039032000004010105100c2c4061100074003a0303403400941e680e04503900e81d069620200c155030481c0c1d261003200703059840030100340c0c0e0000300f182c110b50035507800008030520b203d10040c140e484234214503002c01c170000811030b40c501e4082d43c0025036404114201c01554010403043c100071240d031038252064101c4602d0720034081c1219071500d150020844080302280c1d0314528003503079842001e843e500c115035903ea07055070700c0c240c1754a481a251402d6100c00c0130b9130501d4070004c08a898070706101ea9200003411078004650154424080d1315030000b08020081c1c07070520455030040004521200e4410140c03039000d0a5041402954044284290581c4a13171840558000040035840b0300c01104280c020640000c001d4100c0c1d20504c4030030104608503004504860b6130300c4a01c400c50948000e5001284901e101c2c40030b4980640b41c1c2004064081e400c5038101c0380b420010b4a80b182d85802c81c0d01410f03401251000390540186405021039600150300940740c600c00d81c000c500303020703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 441099694 1250 441098444 441098447
    0x504170606090a05270a0302010f1815020702270f04170a0207120f03020f031303020d050114190c02031306032403121209051015170715050307 63
    0x8405800c84100740d4852001401441c0200344503900c0d1040b003540c1404041c5c10442d05529002d103064214010b500b08102d0303889200c00350103251003841c0c0545280300300300301540e11000f407901c0c0f00c1c40a0a429809201d1007000d6a03d0035410780c2e203601070700c00d480152421403550743c034494401080c2044d48240758043c0004141e1000300c02c0924a00c04c40300ca603850f05020000e0740b8140c803541c8891080d200500c964001c01c205c1c08000c00b01e1510a808551041030440300320b03500d82c000e403101070b010310046540c1000507103001c0032611b00ca54051000020109003200d10980c1503981181d1102c680d0243d00b00c80031001c641c0d44142c40403036030544091070a18041a03119003540200c3c1c428030302056110101c50780406a08800d0303d200e000008603110b40d407a0380b481c00c00541900b02d1288008241410000450118113000c1c154503154428060403110a9040e81900141892200400225000b020100c1c90028084000c000c0c03840042c01801c816190009821842c0c2e26030a91108000d410b005008030103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 441100944 1250 441099694 441099709
    0x17090607030b04020405120a14060702060402040906062d08030405130b1206180105010506090d06110405180603060105010e0d170702100c140d020d0c060213060504170606 75
    0x80d06441c0100b5140148030000380a4000c0350041984280800002800b605000a52501e103501c60700d1000b041c0182c51004549428041b600c0300c001d60001301c0010010315161340206001c030300c1004001405c0d606c48040d1858288014494a160452600525407030891403c1000080c20304070029071405060001140c500c0111103550442d40d40c441c552110070350b440a20100d4000d241c001103030094584108800d280c0815881d161415518141c0042401e003040811642c20f103001401400c07504041d030340e400c00100780704005030081100034000031807241d4802d550901d2250304907003625410304007030007054201201030303120905002a00840380300941392144051402508911100c0c401000616065080d00c20b14100030760000e0003100400701c09802c203841e84000c0c1c0c05200c41000f11015180b041d0744e135030522005003001d039108211071481603100e5410031480038421070f005401c10f0104e40c1d039032090380110703007100300403600106061041b40a00034440c004040c800c00189224146200030440e417 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 441102194 1250 441100944 441100951
    0xa0b040803061206061c0f02181e0103030c110109030b070215150109051002070b0409021c0902010207050409110910170a0b0106080408130320120d050a1206080d170906 74
    0x2030301129040001d10600e43d241070b41458000d05411440d000594603628227440c1220050b03030710340c19620844004540c400200c0d06903581510354140181c0075440b269905408044154100000780001000240c00c880410340101d003550014080d400c400726090404580040440c2caa01104803640c070010b03030b40001403904450007a21010307080004002c00301c3c1050500d8002e299650030015000400311003030307401000ca040c0641c1c40800d11010070901c940545100a030041d005074003904003800f95103082c1e07004152261055282100414110780891024030007100c035094141c01c080c10410103801d0101700319404148c080081c7c01400301940d41c030b50307150006000302030801413180d000408001c2c03030f43e08a40c1d00034038440c10180301075a285000758042c840c111030054000d4034400d01c240a410310716030940c080c5c016440035200590303098504440a8008070102010402c0d811740141440082d4891706000c2d01034200600031580c1e00140140c40ad5280c0303003615015110390f1003000510b24010408580 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 441103444 1250 441102194 441102229
    0x40503040b03090708010e1533010203091e0909062a040302041404050c0a081e03090d051b0105040b1e040914011410020a140a0b04080306120606 64
    0x100c03511040c00312440d04e04607800c100744d550310f000c0541d08480000100c8100c0c5814500d15141944d5500c00c60b44d00c40030b095408580e07050030f1340c03400c0c020400c518001e81c05440d0040c81117900b4800001c0c00210150000d4152f01451680c4d00c80c1d204907403d200410035800000b20000384418200315007000216040c4d40303c3c01c1c0050103880c00d0030220710020000c51b8001e6400400500c1201c3c0e68600d8100519016101260140708440c90190710782000c44111007100e030b803000a1708010702ea50384920f00e074040c0d03000650120b010800826030103550364107c410311140100f004200212800340c403040d0a08030388064a06010061008010841100f41110381c00703640c1c000d415900b8019000d602c001030055400500341c09061110fa038080b1401030405274102e0320450681d090000440052000e0b40441725402070041c1c1001241e20041044070411554840d0104202c85502415444100340c040d4280c404503100c0c04d00100f40800ba15146148609040c10080139040b0b030300b01880022440380b1140e40024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 441104694 1250 441103444 441103447
    0x10c0308090703320d0906050f0d051303120b0a031b0803030c0c0705040e0a0f110303031008010f06050109060e0414010f030c06020a0f0303020c011e02180405040503040b 75
    0x9000030001e010080c01550b00c0119070850b40c0104800303581d90502104580e0041801004003800110001880703240617540352a4665440c2c00c1c881c044445030702c40044010310500410050900141c40d224003407192907400e0b848078100c600d518004140f4802e102e0b0001400c0c1c02c228006c105552403207149000c5039400301410f6000c0c00c1498500c1c803001601c0e0310000490001000300003003040d008000b01140340a01080d18203141d110010030045644402d015240c0e540030201c0340300040e042001e440c450034010000c3c0c5108804ca82c002a28581c0b00710749000a844a20b1002c06c1000400d0080000280c000301e0280309a50422000038200385035407040c082008410001222952a00e620180d0007a40c0344800c0b00e042d684908039804030051070302c4100c031024540a400540300c0d20104209020f19030286008034400e00c10b8030120040c1d0400700808072995600c0480b20081c0380d80c0c00c030000f5110800700c0d0250300e1380b8500306811a010410041d031400349007403004200004a012040f942519002c80070345 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 441105944 1250 441104694 441104701
    0x7030215130c0e070c170c0c2e020a12020709060504140406110f28080c03131e0303150b070f0204022808090d030b010816050f0a08060a090209010c0308 67
    0x205d802d503e034000044c141030030440e224200814801c00404101004404413000c2088140900c1a0315001c1e1960000001e846040d8441540048443c48950701051040761658500c40d00c074800c840c06210040310140e071082c54108031003075103070007560002c1c101164200052002d08001608000c40140000c5c25169100b82d244507030302601c42600c0f1090380801403d1f449155004465250900c50108500203565400e4070704142c40c410344203184a28000d504c01d90540e00c40d02d4040710450f0707a80034101d58480301501d034200000a0401848602c078001d80d0003062030303a002c001c9000d0b02c50b800e8101031803c12003080101d002c20140007103106142d138103980040ea91b00340000d440d014522401da80ea20303089010309111300b41030780c0025031501500b01d420980e06175009900c0d0503005c4540d941503550200c1c0c44800022030a041e00e1030090200c040c031b070404a20302075010b101c1c910b540d4000c2d43c200f0302242010007400014100200c4c0d80c0301802c50144214600020100080c0404640010040800030b0b1032000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 441107194 1250 441105944 441105947
    0x90d08040510180b0c030405030a0f0210020a0302130b0a092d151b0b040f020d15020408010b03030c0a020603090304030b0403050304030f030b060307030f1107030215130c0e07 77
    0x100030b50300c4258502007107041c0b0218602c078800104250241c46803841900070969004255080b28096540000207515008400c0340980788124044143d1056000d9070210307035050030032070000b0100d80d00c0320f81c3c0040e41d0f001529900078406489422014448100788100481c076a000550281a104500f008912036132050408840b41c1c1482407204601820a42d0006000a280b521480701648070351a0910b5025014682d000b00003103200014000c4c1e09000089800708041081c4d22140d14000350090340c41020b281ca4038010302d01e844842c40c840d65400a0204a450130a00ca00005814100c002c1c501d400c0c03140e60a680c1c0d1390140440688140703c00004030300140b0080044034002c6070300c50286c0b40c0d00c0c5402e0a000c3c1c000d400c2164240c01017804014070041141c800d20075141910030040c80030342181c5815004034010304850022243d51540c540d03c0d408011001c9018280c583c0c800d50042040c041c030a007100c20b842901400041031110001008000107403881e41800c283d80f01e040d032080789030b03035a020f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 441108444 1250 441107194 441107203
    0xc0207030c1a04090c0c020a0b16030e03010209040e0606010908030c0303280501080a11040212040b060607061503020a081207121b0f020307051203030c09010306080709091505090d080405 82
    0x146003440c548460305110580000540c6c1da0b1500803103034012107556601c10790416125503d50701c02050180d0590000181c0201d00d588080b2201030001818a810326010504941d0690750080155101500704481907900240d0341d009400002d01460138405c0d5100d11907030b02d01000d1702406078003001c910426404241050514002072020406200c1569106a2130b52034402880080c1e50100512414000074105402244e65000c108410a006580d5030f0b25a401501d4000d403080d64010305c10007920001c500140144104101d0901911040f14a1441000b0210b1820342c00403400f90407026020084071180b030f0598419517007100c880880d000c00d101d02200c1c0301c600540b0310720000241050090a01494100d111003ca1007a0201d80e507060312501003001990616607644900e0707200300b0001c0c60180b186000350084203c103045c0411406d0322000f0641c100b030155080304000d246c1e91a04201444146a0810201000040200a04d0625410413a100c001c03c102140a01a521780032a0400c4000c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 441109694 1250 441108444 441108449
    0x206070804030b0a0c030c080a0f060b0403062306010f081902040b0d29130e03040305100c030b0a0302010518030303090c01090b0a21060503060a02030a0c0207030c1a04 74
    0x310031a41c0d25280e180c20302088400395a520f101d50700d03008207454514024491307c0500004c58560380100c1c1d55851000c0040c1008540c40c1d07118036100d00001a10030002c0c4060310180d4840c900c04100580e00307081e0152010513064800801884000601c885a60002c00c035540c0e41070103281c100d445540c2c040005041ca40f244c40080c0800b40b00180000c2c00c640c01d103014050344595940c1c01c2c001140e01c0c520a943c020310300418100c42105c0c00715021207034945110b0a82810030079200c04100c0c00f401c4401541903400030b510549080c0c100400401c2010305074421100b11038610b04041000e421b0b02170204081c92600d0000906000001445801012441c2056400020000e04480d07403031811014080c3c0340c101060000340821001400414a0608a01510380440b0301e6a1441c00604144800e018001000c0036100075050362200042416201802420301c40c29610302c2c096501c0c01c00690940c100e8032807991a004641108105200181205401508455160b503140b1051060100850403030700c17499 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 441110944 1250 441109694 441109703
    0x3050a02030909011d06040903020d0509040905010207060b09100b0d1a0901180e0705030a0f03050c01060b090a0504020316200f010603120c1115210a0e0c0109030b04020607 76
    0xf0400028003850520210041c094001c12521031603c80c10706000688025402c02070141c2c200108520500e4421009009507180092001c12101456203030542280c1c0080d00a4650030b0300c1d0103844a41c1c1c1000144150000541d216201c3e14500d4000f003c1510b00540c0700c01440f564440d040e491580c07020486e0641111b0000304085400e59540344841c3d440072907110f403840b07014103180d90040705280c041b54403012544090082d001c40d1801d59200c0201d0b01003c4002c400344a030512858090703100911960015100d1f0312005036552945000b0848218055804a8801c0380100100b118850750409212a100c84a00b070000f46030380001c41280c0d509142a221003071610514400c169400030540010382201e008540c0d1f21000705681904642c054a1703d4409810211080d44a40c5c25042681040640000d034100e0b0303500b010740071068900e45006141c05440e01178681000e0005200440c0b207a1046410701c0300c010a42d00b1004c0f00083c0c05991b00c5d100140441001500040540d125001143c0c0c559500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 441112194 1250 441110944 441110959
    0x20a0e0909060612030405030613141e150606090f0f060d05150109150507380c091c08120f0f1308071209170c181303050a020309 57
    0x42001166942c0080760781e14855203031188020810f4002200701d50907584d01802402c0703981e0350380b6500904000c140c00304403212040b0302880c04204c0030070301036400040d000c030000c01c07000411485540d1400301e24002c1c0c84007440716102801010364070141141c40078042600c0a07201c50300b400380059038280601c012181c100400041c0400310740740650040d44690700c0c1d03413440111090744000440d88481c160103154811401400900714140c002d00141800502c541d2103a80c1ca01c0e140c50856114400a80240c041d10440c0c291140000e03000d80201a400040d00766101c1c14802103000046039090381625480c0a642003488900c244505101214a480310046d00c0c513909040c8811541003110040b01c4141d084009900803c070740e513a245014500840d0000c04c020b051200c0ca8035040f05449000c9405c0342446011500003550000303507031003944082c1d02d1002500ca895981d0007440101c50740d8080c1408046400c82c20000c0b541c1010030800103058251810944894a130700081c2d203584207000170036a0090702e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 441113444 1250 441112194 441112201
    0x18050d0c02041b05040b0c070504060308070501052404200403030509100f0e040f0b10030203100603060b04060507031b110a08010b010e090709051f080903120a020a0e09 74
    0x1000905009154400d8404101006404051503000c0310140318040024004010411200031072001510740d002500c0c00348e030b943d83d5590001400715407a47d8012100e011006c41c200e01405820320035268800707104071100070020b000c55041e0308088001000c1c2842544d40308012000590300c8403101c8000807481384c074556100d8990070083c3c5a0382054003524401e50711911003000d503d01c10340050300482d01c1c81d220703c41c1c18500041008050111b50929044082d81d40324002c0381ea986400c002102113046440042e60f03030a1035420b01d4a6140d468210500345810480704101001c0e00c002100c080b070b0030601c0d00c1925a255498121781881c000462194095254081102805800060070100c17072011070348004000d5035056130500f607407070301c1003820b0200c0c82c0c0203411a001c0c10104101070384020300b407501e070b4851600c81002618030b0b00c815407281038140c003030700e03240c051190050915900f0420f0321004500381007400c408070044040c01021485007d4000c5001410036006412110f001d61004090360201d1a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 441114694 1250 441113444 441113447
    0x521090d03201f110a0f050f0f0d0f050612030313060b0307090c090f05180402030f0d0503060f061219020f0711010305010b040b04050906060903010c08090d09150318050d 75
    0x1500d2032203902c092440d10a1440100110714100d5821041d5034494043c4030a181b2402e80b503d4001610101c604d0350200850301c0f01c4c01c4000010614a600014000707540c1c1003031000c00d4104c3e200101098000c18418003241d001640000503030b6480380d07110020480c2d5501d00d2030700d00060302c001c9501035054451103034041038203507550300040e0460b00c140e9148184035544140c03007504e00004d8402c01d41c2201401c5005401800368041c0340f070b070090010342110340d48001d003202c1ca880d00c2505101c00001070008801d010851820481e03d030f515080483c3c42c907087c01d000016800b44030314003418040303a00607242102d0440030f070de6405840d02102c2400c00d035600c0300e003a8100004900080080c550000386071200101c3d41c600d160090f10151800d802d41c0d1401c040c18030003071040240c0080c0c030541d4020001e000e0451103a4003402181c8054a503980c03402d0083c1000d805452611014100303110602c00c0303070181403000084007205402c0e00b000174231700414030415a0449059040320900c0151a0303010700030b0140b8000f03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 441115944 1250 441114694 441114733
    0xf0b0c010e0105280506010c0f03030902061602040b0306060303030c07050c0a0303050c010f09051f090c0909030801061d5d070303080615070521090d0320 68
    0x2101180800320181d04c0ba40880c0c22510304a40c10350105000240c2d800100385c44040502506200703090016204000d9000100079410a4150100326111030040404500f050b0065804115090380100428100a03001945a00005100405148000c5104000d10504020759101e81c0b1000d0030741c241064030f90500030529403090880408030f60070303d81c8100f408800c0e84141c418490f0080050a012011a0301c010380038010103405500302a2101d00400205045466880c003c0811220000b0180703000c0c500600486070503400441070150303150511000c42b0201203500a81201220509900c18616454411007550706a003082840000050100b480c0501e1a80422012002c03951500b0200c040038122080c0311400d0704d05503260040391003000000d009801072900311000034052003400b03050051980158200305001c1d030b2103501400e50240c14002018144298505110b0440c5c60640c154004ca01050341542c0010104010308800d890006082c03400c101142100c2d80c25128101c03e1511282000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 441117194 1250 441115944 441115981
    0xa032406030902040612110634020f060a0c020d0f0605040b01030501110702010207260307080a09060c08120601120e060603330402011e0f080f010f0b0c010e0105 71
    0x41c1c1c17404101082c020020340050703a6140e44400e00001c9400c1010500c01142c00103a07500425407103c0001610101a0368070717103518904050880b050452142c010000e07408403d541c3d513030180504000350703914070b40d00c010700c40511074041e00c0c403490031012440e10f048040b004401c0a0710035407900303080c00f0421800c4081075048a0280d0000c0c4480c090110040483d8480c070003009000d68003202c030400c44101c04c40c09200c00d44100451600c403006040344054110b511102045035074240000c0d440e20210303007195680003d41040d21f807a181c1c50b1540c0c0d071028000d1041c0d51a03c66000790150004419038403a00b4103a40e48500740d43e041c40500da01100c10b40ea03c030320030750b00c083c407d0040302c4000070003a807500102d80280b42c1c80061409061591625002c3ca804040d02c203904001007902074003841c80b4004926402c0030b0507541d8640b07140d6615a40188200e10140c810015607282c000100001c410150300d0505a0340002007041d90703081c100d0040c500601e020051001d9550801c001c000d00d204840713600311803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 441118444 1250 441117194 441117199
    0x40609060b01020c06180a150207030606151b0c03150b040506040506030a1b090c05040501020c121b010e041a01020f0309090c0309030d0f021b01110a032406030902 72
    0x2600440341c0059844040c0c0350400e44c2c10000900008920601c03061030100c0300b01c40a03200c0c0c0803c03030b100c000110030851025041800350340b00d680204100002481950001d022955a9503200400e2480c0180401c0c07071410403900c0d441c440c1b2041c034280319505080b00029a0f0010412030180d0000e50032001030803c00302080d00c10351400000941c642481c1c02210700c515401405030188408942d2a80b0100030040b244620221342490701280d06140340c40380000c4559180c55043c3c41d0340c600b0000905e01101e02c0780490041c1c429000b100044030f00012404203c941c181c201c079503224011001290310011240f10070358414140105044480704a4002070380b008020307401e96045921034241035681e0f114041806801066840000c0c0c1e0120300b4802440d0003400d124180c900d001880d001e5003064031418481031410f01e5000521008922110400c0c4040c10380090080c03003140080000075415005210082082c141c44510301e18181c03c0340704d1b240c003900140000b40c84075640c072408000c000300b1400700c00700e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 441119694 1250 441118444 441118451
    0x90501121503020918030a03023420130207050706090b030601081b0c2d1504020301090821010e190b0f0a06020a05060709080a06111204060906 63
    0xd0345990074010081a400000700c80c2510919560a00c101040e0080481042c4c120310f0520300c081041c148000e0080c44c3c100d039409038840142a00124085c030046030b403280790802551005020030b480c405a00d03516504149850020640e216510050b1a8503031605075101064624401046c001d03a0301611905000d241140d25981d02d8000544144809025020000340144000b960f81d42c0300d10f141075402200000e0b031588101d4810034140058102204104086c0c0245611440f040d4104850000e1010168000000485414102502d99544049496152458100090554400350066151150300440c850b90b20f04a04244070f1400f40e42114004078030240a00000d00f2800c0c072918180101310300340c070242d101001c180380c52005160f84451180c0082c6d0a1803035060aa40c3c21039042d000305404e801600b4510980c1c03074041d040020086c07204060107040e100607c5508000290305503865800000018640000c1d030072403880b0702a000e01c40700e1440702c2d10100000c0020b01d4005094280c4154800d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 441120944 1250 441119694 441119717
    0x33040609140603100b07060609020d02070308091f112802060601020a08160c030b01090c022a1c1709010e030a08030703090f02030105012c010f0e190903090501 70
    0xc802d03c82580c02c0080c16003009402c1c4440340b00c100051082c1480760380b00181b00340e5101050410b1b43c21014600d5240359000c00c040c002c0c9500990080d034000300140c0130340b80c0074181594541880d407844131401182d80c1c2c1e07108070100320428078040f90010910005a48000e91240a001d8101a0b000c00d85c8001801940003046584d400003985604865012000c9410304100000c0d4650f000c2949605440190242c40c0c0003010410811900d4080c03c200e01300801c078101100f902a00d4200e158141c2d03498505501c0125100114421b98119280b501300c5507503503a00902040202c90140c50400075140c06500f0705080c1c00c80212000a048142081c0c0342c44130880348240405840f0140680090040c07001080010440d13481b0b9400089410300c5000780046403800c68022a0031100240c010803d802d8250384c0c0000d07201d681040b0006440c190210f074500543c104101015000e0041c41100300744032030140450807101c4080300c140300c40d042e070000800c107140250800506000451040a0100e071588200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 441122194 1250 441120944 441120949
    0x2130b0c03040317030c121911030106020c0109030206091c05031909050102030309250b13090b10140706090209070c170c120a050c12090405153304060914 68
    0x90340e101b0a03100a01c04d0402d140044000c0c417660380140041c00c80340aa2481081010f260711641620012a5000c0754a0398140f4034068a00030b4804950740c1440760141007003005a40e0302e81255810202541e041d000086845504643c40814920041681c000414820004140540349504143c505d81c0e0301c1c40c4441e41c650059880303100c01d0750b440c07580b604113030382030250759008451402c00c80d007410b00340d13994007580c440c160301540d0040c8802880481005004000340c042501507043e640070101d4000380c0b5101141c3c0302410410301c08003a510318000216441080c008198000300410fa000384c210b080c945401c0340001d00003007800714100c4011000100e50300002c5402d400356490304c21044010030501102502c410104d030070400155040000400189000c0c4074103101c110107000040000c03544480401c010071080c1c1741c00508082d1403070820401c1d0000c80c2d40d001080c241070a0170f0000364260041521403c1c40c0c06603404110413145c8000900090645d50295461044544040c101900e68144408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 441123444 1250 441122194 441122197
    0x190303151e0902160201031a0a060503011806120b04020d080301030b0f09010627090c0f0f06020102090604052701120b0f060f060d06091503110114040902130b0c03040317 75
    0x40d000f07085804d119480c401940a0307441040b0340900546003108070502c0c240040c92803080e6400210000b030021004200c8501c25800e821001044080f0a010407070034940030480605542c800981423505860202c2c007036444101080446940181c0300603603039030310b0b41030040007058152100d0501c880b0240000d0203285040c803038001600e03010201002003030b148941100c1300c80c440c50103c01d9100d94581902c000505483c50300c900400d205003c11040328a0001d005d000040745521150030744e40100a00d010360b40d03900c02150117441c01100c510340080400540c004050000c18490b4800c2282040040341001d1a200c606d41494811490811140d580a1401031412030980340703940c00652565102c1d0503131400901500c82001c5030303e400612280e03551148026035500c401c0444004040b140c0a106000b9003510000b0600020b0034440d80c400400152444503100341d01c1640d030903550229209030300c4a0a890300d14020510242080c2d110918900019242d9110b444111a2000c250000c620200511300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 441124694 1250 441123444 441123457
    0x41205061e0106030f0b04050a0506010909091a040303091515122d0c0303050a1e0207051918020d0e07060c02270f010e010611190303151e0902 63
    0x741c036207159074039110040e8054502c032440d140920340c440703a07070a442da11607101d103905c203140c54180400c032030810b00009815807101d9048084028200024080418240b040b42140648007640301440c5543c1c6003421001021580b100030900d1850052812941243d0703082503076480d4003004500743d125a40da5036000c800c1070240340102070191440601000d07490748c0d150381501b6146404405103000711641c420340d072458503410480206601143c450348140d80540140100c20410060954003501001c0180d618245403140b075108545402030340344036811040e6400c0040983d00c031140001e95140032801c0c040e4012410079514589080103000b80207400040c40c02c1241c860b610384c503500c0ca2154013408600220b020160507072981071140045803507030b02032480e446103015142035420383d4103008141c0341680301a844001005605c00486d2401c602c082a08400049480781d5288500121319040c1c01400f01e52880c404442e0341180c001514500e000c0d04032840e0031014482c07942c003d8503944107804034028203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 441125944 1250 441124694 441124741
    0x6050a0b0703120b280603050a020307021c0908030c031e04050d0803090a0f0f0210021204091d03070c090509011e0f0e1c0912080f1803010204120506 66
    0x710303c0c0c0403030042c265103e00100d840160154280102540d08500000c8603a00c0742001c2e012900000c000070340d0f141c8106508001400415442d500380308200940d5080d402c03c40d60030a00c00340c1902041c03140101031800082441c501030b6600d50310030220240d101d400c414061000802c640f080010301c981448100c506480c4014a0381007a8034040d16005541d401c018074512940c03003401060b4010078078070042c0701e541c030b4030a0701d881c9003a110510510080d44000007142c801d55102c0180d61000b18034541c2a034080e14000f800000e64012a03100e2a01044048210b010720b030b00000800c5402e00c000b515441040d103041c43c0d018040d0b80ca6954081c3e08a48405a08400c2c00d0303004a28805c5102080d000080304030182c40d8082002040c0101207403c4c041103081000c006440b005984951680201105000b021410f0110b85001019144c030310452040103548000e2040000d440720610940c1c618010400b1009030085442d01d44400d0f5441034a05081c5003a80c40f03101d0030380001c1740c02d000100d0340420444007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 441127194 1250 441125944 441125957
    0x30d020607080c0d15051c2004021201062d02070303120f1d0c0301020306090c1b030a0203250c0e0910090b04020a081209010e01090305010e0106050a0b0703 69
    0x29403030304a07120303800685030f0100e020082110b507500301090b001c0c5428040c6440304004540d4906020448011800340b4000320303114416003110045405401d80c981010f5400202c41b0310704480e080040d000380b042d111300d03c030080f803150004624164000109900a00354101007825044588c11062a1803042c60048006074803911060001070311170700c100884014501c40101d0b036940d0780001070b02500d0341e04608000680c2243c06841e00300c00200030384140120281d00841c610700b007040c003103240d41e4401410100c25800014203080f120412a80d0786003d000c1e840c0540742c4841c00880c0080d12a84003080c6000403018044603a02003561130403003850190341c00b1944503a0325140c0b2152030030060004010b001d42c3c1c018410b4180c1303480c0c0c5500603070301c910b40304c1c00e100c0c030711450184100001c2c24150342017030300f41d0760245188030502c1c01c6c079500721851030780300b400c00e800740c240364000489455400381c0004103a54248800701c450100d0542140003a52811686610341c607456405001080c010100040d00182c40b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 441128444 1250 441127194 441127201
    0x60c040807050607231027081e0d0c082215020c1609050a060f030f02130f09060c020f030a0503090c060a02060411010507020a0311120d0e010e030d0206 67
    0x1807000041000a00c01d030340c0c12604003400d6805d40214200d500204d545038028040c0c94204501d07510440c030b481403c1503004079500a450350249504070400100400c1c44078002940100c21190040040382c0f400d01da040300d592080001c1e204005000d01440780c5005c03440d214045200404140715a106000c1440545410b40309661500801919809a109a100e41c20011a040f40d9014040745400c0101c014440071410300c3e000e00c04080303c200420401034a0324010061101d114034107071b11000c8030742060711184140e841d030000a0715002010300c801d4010703103000404120b8915a4100d640040e000f40400c1008001d07040c4280d85410203580e00440c00d400c1000230084550144020b50340080e1030004440420204001085c034690005210a003d64029410402003100083d4510002d500c00c1c60301d00d00707105066001c41c140d8a85408014100405406d030101c0c15151070085281c000c10b08411580014807111020741804080443c060005c0c940085940d01418001000048800c540e401024181d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 441129694 1250 441128444 441128449
    0x3051605060708162a180b0306070f020c0a0e040b090a082203050a030503041e020303040315140421021f0504020a080a0b06012c13110708030702060c04080705 70
    0x107504008940d8000b81a001884800440f04880e034000c3d00b81c1182069030381000d0202121881c2000003500c11424194030001a803804031b09c507a009032890805c901c26240340041030707040040c0325840c00d4002800c0000002c0c3e0111003442580500c0c0201604015500c074082c9490701c0c4d606140014015074001c10144001c001c0b030500306070f0b007941c5a4002d48070803030700c031f9071035500342111107105800150010043c401030148a0f1031404151b0008074086c0701d000d60b03650220342c49000d28840641a55070f039056403003444800750403030b20f0098000c041007401c80c07426290258501c01c0b900c1903108215842c800d103528140c00000c4600c140706900c0050710151104481c0c1201601004000f01e07001864120b0005a801c801c1112170107840c802c608035040340c602000010407003840000030040c01c1c20000040301101c226100e810201c02e00c20b960740b50241d402c1d124940c0141156054090800100260752018843c641c4069802111545d00b0341d6403649a80c80354414500803402003c0031500408010059803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 441130944 1250 441129694 441129727
    0x30903020607140706050408070c0e01120314040503060a1406040c0503010306020a0903050a03020d080c030403082a070b10090b0303041404090204020304050d2c040e010204090603051605060708 85
    0x1110f03040c50b1a4685070540d52898141c07001620300711090035001c0360110030841402455000380500300800011036141c0003410940c0403200e0000b800703101d00d51041c541806000b600321409418060110703003070f50501620030300091260700e0715130347e5280c20380004c01c80301e1905019948000446e55200f07411a42141c032400e00035070001c428031040c04030100b000130020b00c5c02d12108500a020350041c010180c036115001d80b094030014110101900d00300704001c0007035041345c0d815401544481d511405002c2c0c180c030440d50000c428420b031018003070200c1c00100300414a10050702c24a8012200040c4699809040c1c090360080004076505801c180424044a03031884140540c100e40240b0206042401740c0206d0200d90046d1015562034000c054000074a03074101142420448082000200f141050f01007041d0303800504200c907104644075074940207551003d405540141c0300c2c549080201554900d06107640c2e03555500e151a40c000140c1001400c2d182c03001c140c6880540210781f031751030001d060102c120f55 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 441132194 1250 441130944 441130967
    0x2090105090f0f1903050f010204053f010c02190201170403031113091a06091002070b0a0e0102160e062e02010b030f01090f021c0602031015030903020607 68
    0x1c44580300f44141107558100180400d40c401c14116542c075811030030960700701100705c10710a180f680100800c10098035540150382298601202d007409902a141803030b41c0c8001c9a0104044030301d600c1d1740c010710f15141075103c10710882e07694003180d00c403502c07450740c500c01c4c65208600640442d409004400e480060304010f9036001e480b80c900041c41c600a22210380480c0c01070380040c00d0480140d0000e106c1c024031407180c602600008240380079007480200c00110179115521100b4001c02001e000745141c2d5000300308030300240840904a40d152010b0900040c404c20043c11024014494030007a13055401403498440c0039100034046181c1140c0e90102486441000c1c488085280903908143d54801c0c0180300241402a800b1b03400850010003d1041515041c3c059502c1091649403074185030000d0b00581040303925503410fa9030038110741c51800c0280101d451801010340707554000002c11072044024000c110544040806c0b0032030300c40c140c2c0021412502452002000340e03200c07402203a03c140c00380c4901801d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 441133444 1250 441132194 441132199
    0x507030c020a11042708070c120b0a020901020304080303090303040b0f01080d1d03030d0c0221250807030f020607080c12100801090c090b040b10081e01030f0201090902090105090f 79
    0x200715085c0000c424844400a0181c4da01d910208441040144031500040108804942524070754201c1e12000035921010f41203034485980000d072010264024410760300140080c400b0369480e8a82400001d031664011682140c5004403039000404620150791014165000c00340103080c1281080001d1314401c0c0c1c0c030504101101c0700d400320001e03903030390400080048415910010440c6110384002914007900c40d410807084a44900302615014000f8043d59455580141d0442c000040c000614001c40e008210180503924000344100a06402001140024510303a0841d6950354800381c0440e8152000da0741025003000c108580c258029102c19544d0304400c030f0000e01040030f6076412800b030848045c42c40c1100c150030b80d100100503175035903445030b140380d51016681401040101c400048116290212490910a00130301203155003a1a403403030010b03156900200e10071940c580c2440908a004080d040b400103002d8400410001c0a6000b607a4000d00107840300d60405141500b0040e0b0541d100c48810b8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 441134694 1250 441133444 441133481
    0x5060a0204030f1b0b0301081e0d0f1b0f0804080c0f180402010908010507021006052707030b030d032c1209030f03032502030307050306060d0219030507030c020a1104 73
    0x1780d4402d60303000a5000f0300000b40109020040040340e04422400d480745031405400400da6080d0741a046041007400e940e0780d142c500700d80203804030300c1c451241840c3c402800c002c501c91810020000a10010b200b918440411038610307902e4042048807841080b410f00c0c0d084200340001d40d01080402001a80261050600002c00c41d00c45500601b101d000b151084016400440c0d50980c01c0d0b201e1142c04044c1c042a40c0d850344048200e500e081310000f40c201c062480c1c10302e01c0005550680700742e11034205100010709035041c3c103440c104010050080d640c0e4410380300841814924504100300c441d20f100c1030b0444080c12a6004564100289402810706d042c0c00d030103140800701d80080248011842100c90182c401c5111004581000741e031315075051030009660013001406071140d00700095a0384001d00300c8400340d0b11170b60220002c01a006a03000e41c102445142e00d269905905500320070701c1011240e03401c02240c44100d100720307038848068402030b0039910404421015820603810403586120010300d443c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 441135944 1250 441134694 441134699
    0x909021b0d03060906080307020303192c040605010e03120d020f030f100e28020c011803080a060303080a02070302070510020d020d03020f090d0309050a090905060a0204030f1b 77
    0x90030441c0300415140003036a01c010902c00401e861046601030320f0904019401c0c070041d640401d0303407440303003440040c15120b1005204507403a114002001c2c0c04152020b415501400f0211804400a0000d507a20721a904080021840d5403090050403001c3d1401401070049200401d03480c001340d0301606c5c042c40401d07002c000f200400244c0b200114058101300e106c2850500c0c0ac0544a4610751180e04100150f0300800e05008144062001c00e1140c01035407265401c2c02c0010303448120003889402200c0e00a5400e082c2d90410403861110b03509080c4d400ba0b26000826562440c50070112504c80c08000c2c0864405c001180c00d01540d0381c00703884040e10038011158444d884800007602d45c9a02c040700001a0301c40714030031004582c1809040b02030350041c24150300702a40204010101c1c0a148212401203640402c0308040c140f0442419004010240c8008803164444940350040d00c003255040c1d995201e103c001c40e4aa0000e4402c40741166040b80720380c600803000d503507032840c4c0c80d032107490009103805000f502 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 441137194 1250 441135944 441135997
    0x10504050406080c040b03010b06032d011409010501032003040804030b010f03140a0b07120f18060605060403050304170a02090c0a0806031c050d180305071406010501090902 76
    0xc2c10b015201e40c07401407901d80801400c100070b680080000c180680d040040b0051183c45d000305481d006032107903500d4600340d60710205481885034090300c003c5006071014000100c42035000c007100c24400c810b03141425560380751001075040d542c001880802208140c06004146035180001c1d6030403500c900035482c0f429641c0e856019601000780c0000008425419042040100c3d0032441003c142c0b901d005420300b200e41c2d440d810043c0c20010600c000f0b2282591100c000c5004035888201d1041c0c000808000c520141e010b140c0c0240144602116074501d860004203451400c0d03c01d44046070380c03002c000e40c913042c186a00041c4d43c00b03440441540c20b100d114200310060756a851114420844040303503a80350304d800f2100800b00070002d040e460083e0064040480d03240e0003804211008001c5080c100c0da10040380c0082c0c00100b12000b8440525090ba86500c010540d21000500c06103018841c0d0b0110468400501520b60300c080c480c1c1030100b01c41110400501140360050103012140898141e50409000700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 441138444 1250 441137194 441137201
    0xb0714090411031e0f011206090b090c1005040b03070f021f05190519020c0f01090f1b0e060d0609051608071401021911060f120105061c0504020105040504 68
    0xc1101c1d5410b00070080000040703c540e940441c01c10300001c1101caa05101d495010f0b1000c0600410064081d0f00341041c041c13283c580c200c00c9a03107a01030714140103883e12020240c0ca0f0403013420258030590606c001d902e5541d2241c01928283e58000c06030514580300c9140540310900301103552815030207010034800300500e0340030748010485c4150b039002c912440c1003a808900100c564410f01e20b2035180c0f905011040070000c40d0380155105c00000103039100410701a5902d00000d40c1552070b131075800c0c008100c04200e000303d040d510b005d100d0040c0d500403802c00602c5030b2010540d030180f40e0748070051600080ca189004540003103100c7c02a100010000030588426080c2540100003049000b4204420001402d040109400400294051968039a01040001e4880f251100c441b00c0039100e403548a81400954042444070b00f8004000b070f552242c420048400c0740d0800c11303070b1804200f004070001911742800012940040c02c1c492340480c4045c10742d42100d00800011740280d041100921010405840310b10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 441139694 1250 441138444 441138461
    0x1020a0b0c0a0905150a030c0908070807031103060f070c020a0306050f040203070608130615050a06020f011401060f0807030b09010f17300c0d090501020c0306040b07140904 76
    0x141d0090b682d40c1d440b180585015070642c810b81c01520a0312015501102c100241ea0789500589004503620280180031140301c0380a030000221400b680200282120000620204407441840041e0300601c0030020180c440104942c4844134482020000d603d0521a00300d40c1c40311407008011001403612919804101c4204a4a171689903400340248000d600c0c080001c040285100d2401c0c2c0f03c203180620800c41a01040c1c0c0004114513124180d041e0059104540b00014082c040c22882400d40d84240c02503a5510341c83c4a1403255203070044800e00348440c0c64102c0d041e20360940f29030280d001400c000711210807005190100b01540c40c420382d0030039500c65174102e000381074203800d4055803400c0c403500c0384154603440840c414680c40303041000b28021180301c0441400d0805030a4481010305210005900d10400103140d5640c040d8405d0305942c2c580100c0707200c054400a84c2107660040100052640c0c2e1402620081d1084064000107041c0c40c0c45120030018591001904605000101c4c012170300340e42082 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 441140944 1250 441139694 441139711
    0x22060305060909010c05041503060e07020d1206050a06260c0415021c0e060d052508070804020f030f06010b0717161e020d0f150209030304120201020a0b 67
    0x340244007091030001001a0004003990003040039500e49600600729224a00c2121503c42c200d09801d4185400303075004000034501c3c108401d045107130070030300203442e008810300c3d0300045550500c1c160640400751049005490020300701d220344c14103120040d40c0d6242c44801d0043c0f061000072413081414480c042c01030295000c0d120706a142c508010000050b400c00c00301c08001c66024240044501c0c100203062a40d00c4e10900b006440c501480700860624801c15074210b1101d400c00d0184800c4041c40e401c1030405080c9800c00c108080f80001301110201e000382d650500203500703000410058501407082c0107502c03030020125038503031000c03e00c3e25040001c240c1c441202c2c2200411400217109001802c0e129a04040010525042850a41c006403080d54003018185004081003034034900c40d0400844403954000388031221960a42c508100303440c490b140125510701d1000c1a406d044104c1e402034518031003004000e07604060030000385054103907030480280c2c1148034110b986400710369030102c540d0003400c04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 441142194 1250 441140944 441140951
    0x103020d020a080d020714061303080a02070e130203010c0305070203030612010f0603030e091008030f030c0d06140310051306021c050c030a050106210506120d02030408070e010812220603 82
    0x2041550720307141b100c5000240c0114400c10140601043c802788100581c0e40c45003001d521546030000480c84e00105030005030031500b91005101c0207580401d081050b0a208130001d01080112000440c2036030b900340c0310b6101503802400814201c3c5002030101b106245050b00000301c480c4264014010b07a5007992007940891000076030a4001e003001006107600900c540042ca101d1841e15140341e94920840c040400459030100104008080410449000120300c000c14404561204d460031450031008100301e00c04d01c1507010002c0d90001900915105514480d850309411a0070b44814010f52711801c200b10710820080c0d80051404044e02c9214000c4181c2900b4075102c1c50048040d00c111801070300702e8001e020340c4030f05019540582030000b1180190340c0348046443c0c0c44520228841031b0802c008429140183c5001c140103070740c0040a00110744220b012110140e0f5140c0d1034040000017130003441c005801031030a15a054600c00c0040418103240e800300c01c08a510641072040203074503608060002910b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 441143444 1250 441142194 441142199
    0xc03061009060504090b070c05070e15030d031b03020a0e06030106091809050309010e0d02180a1104033c0f030e03150115020307020a030606061e05030103020d020a080d0207 76
    0xa01c0d10590000d81400c0d00c003004031a6242d01c8000d00c2910091070383c0c0810020091b50f00801c8024000d00d402030802456000160910050701c8019585504445009100340910002c00d03030700c207014615020a0120403c07010810050b130460295101d0b40a900c14402071444500054442100440c0200b003980d45d280d1006084c0503401d04410001950401740504141c0c26002260340130040300c02c02c4109090403080c2e04200d0020a2080020b07960280d03101400301c0285100301c0c0714444592141d02845002c002d08240f83c0e003500302a02490001801c1412488100c06469820002d5402228411484811140c1044002207000010400200c07007000609281001b01a000a1559028282103010303000b07036001f070324100000001c144140c6c94542d1001d2448040e0398002e008881100340c014215145050312410002c018148922810000070b655001d2086812291080500c000466030f554905e0340e407841d0208034100f10040030590f40441d271100e002443d1242049030404030740951300508066071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 441144694 1250 441143444 441143459
    0xb1608041b0f081c090e071b02120a021f05031f12080a0f0c0b06190b0703020a0507060905011706040b060c0c0a0927140313140612070c03020c030610 66
    0x46000513018000c3c1101c090003400c0d440000303103501603541c1c5000c0407000100701c008c1d0b0149108a0001c0e421807011603136901c0010300419612140c1e80240e5141143e410a07501c145d4103030b000100d0b8200010810b0000c240c0303100c400c19071030380c00000302042e09014903240c3c541650480910b000881d4010400200d25036241d40003190310100e424642801c05501200b610703160316040e00101041e1003107015146c96090190303402030602c0685828128292294001d180295440760303048000e40c0c482c804d00710000f0f0854410144802901c1042c0e5560544070303c017141c020351400000e0130003036116845480e000c2003622000042c180c1c242c4003000410704000c0c502d00b444056505a0051000c5504000302050034240a070765220402001c00d590310340b60a91800d00507070b81e4194941c07400b00c50100040443c80a00d0b0000108196400350350000c120380c1c003030340030000c0070701c01c40300d0100b4000a488000313450039004800910b4070078040e0042d00e00e40c0662400003030500d07004641400204e0f000850601081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 441145944 1250 441144694 441144733
    0xa06050c1c022506140702010c05012408010504111c050a06020a0e010c020f010e0406030803010f15050901080406051306060906080c0414010b1c0213030b1608041b0f08 74
    0x154800f0103020b8614180000103101240b141034000303100c0000038040c0c0469116a03002031600750000000c100a0030090f00065840c0d82010b46400d03800801000810b9144046c030030b10b40604d900c541458045030010040c803810210810340c15104001804000d0049034007442004902ca11501c0016603a01540344c1c041c01c04e13090446264100040700000e5401629001c2c02e4401100b000d0905240c0c07910900c0002e8050004d60f003008103001d0000c80009000d400400101003502c0354007a00d6018110700c8081168180030b4a000b8030700141c2e002000c1404244c8507440b140d0000c0c0d074282d1900101c03920352110300c161030309640321001c03d43e690502003003020021b02540e02003040490301170280207001f90245001c3c200600551486000026144548685480203e851800010401d54591100e0050480d0700446440151201c3ca4000000303a000030001140080e050700d285c4549210742c94541301d00802d0264404051004c210112011600602d4610280010090b140040182a044008030b1149 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 441147194 1250 441145944 441145993
    0x1a070201020703030e0c092a070f0302060c070804120305040306090f0204151206020307020106050a030b01030b0609041a07050c010207140706020a051c05040e070e0f09060a06050c1c02 81
    0x2260400c8018004541d91002241c2d080780ca406158415061054022312680a0030402c12101f45000240003080001d0700030900c04840c080c2c1c00b91581d5544030621513289200c1e510008144240c208424000f8483d82c104900816009250040c101511f03960380400b03c80d42520191051301800c600c5404500d03046c00b458044d002010003420b903261900fa151041d00a40150081c82c458011000688041c400d5001c14010f0500622090b0301c035136039042090040c0400e00059a44008040008150781000004a40190380c422910303c82008541c0a1101c04607015044404025082143c021701034800d0001d002454050810b000d06a0071048140c3d00d8002c0e2a407218055400c204052400b05101003a40c440c01d040b10070782451144010310303086030f02d072143e50041500344c4018418060403507480303601a03500301004e5a6100c07100703a0a10411003902c0c0c086800070750080c1145000e0112501c91030240400d440568111484401810118034140b50085400401031780306c2502d443c1c600702e1455440c0c14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 441148444 1250 441147194 441147221
    0x906010501030c120515031203070215011203110709020309011e0b01091a0702060d02040602010f0911100c0803010b07021f0206040f0f05060f0a0b0301060e01121a07020102070303 79
    0xd00c40f1001d400e004160350840e40e0950b8490009600408013641c004140c08001c055400b1106d1640c07076883c1079041a07507810300500c50b11a4201a0b1840403900a05a0b0115078501001c050607a0381120043c0c0d07603844002c464027a42030700140300031890001d14003400300300001103a088045602c06052024072840d00c40140c4c200300c8074078401e980102070f410954184040c40c0120300c01c80700002d05644280302000350800030000ba00000d907500d40e0b0161040d182ea560092002c540807040c20000d56100002c060301000e03181640c800b1918100f0410181c4014a00b84000381c40200e882d80545030f0000d0b4030503c041800000c1083c11032910402040700c079070521056001c60012400001c0d81d5141c01840103100c6494201214140511110705003540caa1000c02c881a80c07808080c0400300c401e040e07a501241c94180042c0d001146010b011701c40582d85081003100a9a1030b1034150100c096910f00306490146661050744e0350900c080006038401c6489400143c0d80303030051300c1e00400b15a549a070429 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 441149694 1250 441148444 441148451
    0x2715020601120602070215071a090303240d1b060305101a03130f05070618030b06040f02160302030a1202070f060507050423090109050702071215060905090601050103 73
    0x40da8503004480c02d04280c00010040e190b169a02c0882c035512040311116900381800719844d81005030700740b00b40034000701103024980c0c5a154000041c0d0303240003e503140b01082ca0240b150183d00c0381d07121186141c86c90001c107046c61010090300c8021081440e03610018080c40c0d116003d00000340c00d40036164000d054520001103c0e842d010202c003134000800c20700c0c02110800000b142050209807040101d0702e40048032401900107500c0c100384da4081c41d03c039220108810740c000400e01000c118501d0221390700118109955a501070400c0011701080e0028501141d0901140b24144201007000035205d10070b4000f103a81d96074080c000340860102c00c0081c4003060040008000003152401d0f81402076070300a038042076035102ca0600350b5082c0a03981184403041c45000c1c0c420a40c0320140c81c030220000f0190350484299803502588000c0c1c034022902030001d44d201c03807410803c50108038590310200c0d0050503050f06e00ba480f110306900341c2d800e40d8000c1a080d41c8032018010702c07040c01e00c250340c0104401d007400c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 441150944 1250 441149694 441149699
    0x5030d050105030a0807030f03060911030a05180c0f151b0c04060308040519030510060608090f15090106180e0d0f02060a0207060b03010f050405071a16032715020601 73
    0x503040351040b02c2004080042c0000f41648c600c1c02500f2010182610038001d10284014040d07205158201700c503a86ca50504200210703030200c0503134802201425040700504501c541102c28440b200e00d107440c1198001c0b110380c002040c001a070002500f49003080b040304400b03d500c81900d10786410b2111403c0e61049140190800000300710200725401ca032802e8030401d84800340e184d03400400c00919440503042d030040e418151000c04042d1320600c03c2c0c2c1c03102c0e00c4000301901c0d072030b03007003036449640b0b032020801917000a89407004941c0c00e9141d55401080c400011030056140c058505800c2040348510302070f00c0d2602c020300300740001800668440c0526140c40c1500020031540250341346800f0f01114010341d4005012002d004068109070b0102170050024400d15182c05c3e40f0030001c00301210140e8a40c061002d01141e1100848010025207444005c070508002654080114000350014101d080c400c0341c1160641d406541c2e0481003100a0400c61805590701e40107031088500042d091110843d007020006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 441152194 1250 441150944 441150953
    0x210516060504030f170f0c1c02031906080c0103050910150611010c080115110303010b090108090714090c19270e0c0d06030b100807050f09060f0a05060705030d050105030a 75
    0x5c02d40c40f80c036107444008030380c03561001c031021440743c00500121040120032600324245c3e190000c40c0141102100b01140a4021561400700d58050044001b160000006003107a50310a40055412170154026588180e6080c01403204942018030500811142d8030020041c40d80c2010002c15941c200f40c009001202d000000200090414014a500a03c21603a0104070520030b100310141c8049050499591396150150207d0a810481d01303503001034032030f900103030300d01d0404541217003101d5000c0010700d02e1991003000c000725001c000300717800c5c94807105000d060122400b149a80d000850b607a1240b030910f0003072020480c2d140030007550003540006400e008100c0321041c1c0e911141c0c013185401016454114840d4284081c0030240c1c03018001a0301101407200500a2984c48411900c0040c00c07102159516014880b8809a00f81802e0b80001b81c0000903095040070108445028001015410203940b00c02c0000c1143e007080d10141c400340e101140601c2c10804512469000d81021002407040444c0ca590303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 441153444 1250 441152194 441152237
    0x70c1203091506030602090a0b04030b0a0902130c2d090512070b04060513050415061b0b0108030a02150103050a0312020f04140102010b0a03210516060504030f 70
    0x1000003003581d2a81d48000748071004004101e80051103070144105a500d08042c006504075040c01071090408500000340510900111002c8a502c224210040c0e6550152100200b201034826604403000d54201100c1d42c0081c400c41c02000100d4582d5085500c03c075283c1100c1d040c20b10880c40f56203246001040c1543d407c0005442215001c6a43c400d04826180340c90b41040c02c643e100c1c18039540003041c0465040c0c0c110b40074026400810400c0440305030344000300030a480701c520001d140011025420b100484c401c3c241c0e458a503030668104481800a03a0b038011001d0401d030301a000c16040840ca90600c50307810f20a80002e15011442c2a02c254195103d2030f40f503540c01d901c020b0900081860a44144c100ca03019036151001c5200a40c0e1140d44e01c10340301d02d000714001e00b454010751271301c88810341e41d02d8111014000d49400040c00c1d000c000510b1090003003900e200a000081c004107000788100c0c03000c91901c441500384513800200d0241418580a040b50103186450428401e085001580002e481303107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 441154694 1250 441153444 441153473
    0x1503120c210d0f020d02030405010506190b04050607060b13150f03050606010f0933110c060d0b1c121403070f110f0706020601061404050d060b060d0f05070c 69
    0x501843c10820f240007489642d8844c3c6001d03001200300410b00c8010350050748201002e44032003190745003e089120881d016802554103481081c0800d201c6030501c54081d0014910442c03001a503c000e250004045110b86900c0c890079940301c0d08200305d404504c00020700105200c6121a045600f07580da290b446150040c02c0c541000345048001c0c02d0640b1807103017003008090b01c00d0b0010420350441940810080303040e41e240401007400d14980942441902848900341a5602a102c41031003641000100c0e4000500b0222141c1c54403050318441d500c04034180700b06101044c14001d064a5071503d03600c040404030426051001d4401c81e100e60320200c13000c4075172103100c6103080304130000c100406555044109180e00d50302d10904203086030700200020404269000d81d000c4a290383e03a01c040498030420301c9850306541200900c003c1006080843c92500c0461003594003103640b401c41d0012030019003004403208500d50702c0c0c0800380141c5450b881007903084000c1c3e1030310f05041c1c5119107840f141c450488 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 441155944 1250 441154694 441154717
    0xd0c1a132c0106050405031603120c14011401050a0b03040c1a120c03070210060521010e01020a26070503150a0e07110106050306010e0c031503120c21 66
    0x41030010140c42008101400314204071000c0042c2d40c54003001041c94015000d030b20f0081c402c559128604990160010701182d0303210044841810759400112240a03082804941c800f070580e0600b040000203001c1c41c824120501162090341d1325010030021220741980c800040100108103100204040d44180e0003520b8408100013100310310810094070510407075514262448840c410300107020a18001180109190713801c40700c03003131801c00100c803c42e00c0c00d124280d07010183c1103a031024283c1e20040c0e041c91503000000000c2d1400301c9011036081e0783c0700c10021400074912110808801051902840051182d02140c40131803901d0301002d0120301c0060300850035400600071104095a4410848000c0c14210b65010450300700050090300500d40d031031010149500741100840c040c28005406c6040310f0f0004031558487d162052604000d0b40040d01007007280000c13000c0ca04154808000034a4805680c9a075140c1e00d4079800100c4d4109a5074141c480a40742521500c00c4034030681100350341e000e6044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 441157194 1250 441155944 441155969
    0x3031e0c19051803030703080a0f05061f110703051c020c0d11120d110708010504080306040905070f120c120c060503280203161b030305150d0c1a13 65
    0x2141c00410f15a0b042c141d5181e1510001811008241d03006002d1401080d103c0424002e804d9000e400405480040356529000a9010a0181c10241a40c4001500038590030125255a12039801c0b07814200305400903038081c1e001484c01481780e048844416a0352080b4406403045400403c0025016140c0841c041c00c060004511103c6690f10380c051040d1091507071003200c20007105080d02501c004080c0c03078000080d000b02d41000400b000306004451040da882000d40e484d559405003004010120401c041d5080e200e0600c2c0424441446011180900303160503080e21061010f1429940070841a040081c00144501d0004001580141da403c2625528244541c680e030789c07e800c2d904c1540070708661000301e00004150400501070b95004500401450000e001c02e18512103080c0d07186892222920360310b000e400a190f010034031940c80190000c0c100d4079550400c6294000003900c003c8000005d40b00c407130780700c40d0420011201c1159502c2c1d00050311480c90170002120b00d120310340782061241c7c082036200c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 441158444 1250 441157194 441157207
    0xb01080c100207062f16260c040203040c0314010b0f1806040f1b05070b160c060b010201110f09030601080c0d0602090a03061d1b0907030c1103031e0c1905 68
    0x5025000e02a000c8017003c45024046c03502e08810b13000c4643c81042c0e09903840c0b100c40b04a80203115030038081c0105c010300400c881e601c4201880300035400100283c504e0003d0301c0b0080b0004400c01da0310702526130715000104100d00340302d0802c00c410030b03003503006440f03009018007064802441c19103042c0e00050031600061030b00d04c1d41c003a000c040d1807044c0b01703941018200b00b440b048843d00303d4060310185008100400c25035580c5581e96032441180c43c035038000f00e03264505840025402e0340003030021103010310021400400052086510750880c2c1402680000007080d846401e0a0421103203005000c204000c040080c0240085242005a0b40024005603000662502d840c0c036001d842d1401550b00940422100101d21181d5024540c42e01d01c80d00d00d400b81c07840a402d0f20341d60b80c0340844501e2005020a40e181c1f02c0c45001d8004080c48014142400a40c2103804202001800039610810210b5094154483c16030000d070400f0400400c11180000117100411400f44490880c0002279030030f0600d5aa50704 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 441159694 1250 441158444 441158507
    0x130b24031903110a0222050109020c0604021005130b03160201091e030908060c0301031b0305030f160f05070f09111803122106040c140a0c0b01080c10020706 69
    0x40d0010b80c0030b9040441c01d101240c0c6d4403c00c00e000d4000740b0f81c40c0d00402183e620356110b0b03410392080c1085c01d0032a6011001180c09440c04601e00e4100e000365003030413483d00c140e0840344a8888980e50040ca00c47d00301000304840840e8603000c0d80b034540e15a03c001c000030161613841240451051402c2c400301014400428105805072a00e40c01030152442243c0700e0b840c0680c070085c6603030b209020840d02000550b602c000c11090800c0c51130103613580701d00950b0501041c00c06501243d0400b5810185e100203001c5e4000201d1264025450321038051000f811005041105c046c01007000c42d0b0044403014903103c54000710101403003d070f500540d0760701c4000198045450009242401411002e10303010f000090350301c00d040d152800d180c00480a80701510342c42d88c480c800c1108555100b0340344000b01d40402e030100960300c800301c01131001307904a0400114503550740d15080c0c1c240200f40c0020005a00030407102c8460f14002248407a22900781c40103200b401d091400041800020f0108030303454501084c032009162 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 441160944 1250 441159694 441159703
    0xc07060302130806090604051e0a030302030709050d1b06020c15090105040506030c0a020c0a240201021c05150d120503060103021903090c05120d08130b2403190311 72
    0x40000c00d0450f00f01e414003041040c0c88130340542c1d0407100c030f09c2501401483e03180e038240611007504044006c0d0520340c580c2d032030a6010f544014191f038100251604049241d54840c04181402d500601d00e44c050070ba00843c1914040000350072250a640c0009180c2c3c6103607889108040d0400c4182060075118480b00d07006036058002c43d0810766128502000b00240380c8120b1020300307031840340c80d801c450f8190a22014461036070000d0081301004d1140303d1000d20100001155042c005840d48001490241d841c1c000000c0032040c049001007880d105c1c81480742c0c5609080403074000800865030290004c4166a45403441e01c0c03208051001e00030b0120014107a60300943c1900e060140c00321003910b001503401c8009004001d5010704890081c0c402c0804a043c0c208030b0442000030321120001d0009444404040d641610300400484504040010803000192861202805511320741035030301900303001098411000040c0d1803102d00075400104103003d0991803403450303200582c2504050b00710713441001c109805c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 441162194 1250 441160944 441160949
    0xf37060905120309070501050a050306060a090b0a0c050105100506071401180b06041404050606041104080706030e0f0d020a030c0201050712121404020d030807020715030f060b0c0706030213 83
    0x41c0608030360039441200d002d00462045580c8010703107001c652101c00540d85401140e4040000030800c0c0001010360900788002c203401810b03402d0080c0025650081c20505920030302c21407002403200c40c051806c0041c01d003d0b10790003180400a400c400380c2094046039144c0076988003d080701c100b241500490711000e50242c2c030a22003415042c0c04041850801ca5a0000c0c1603c1180c00b481c41c04203e08a000c0006201502031580240540f005445100400010b004100000b038203041081000040c0500c040102000078490b6840c0894030031083c0c41d42c682000300203900740341c036500b02c550406021980804e81c03800c00755150820001201c060b00040b500740c050b118000300f0005910b80d015031a10b4104581c4001380c140044c00b07010511080005101625003514001d4100c003c121041001a0280d04119440052403048410591351001c107a41c003940240a6007000c69511440d9450a0780613000310300c084c00c6420241ca1900010b06e114543d207a002c1d200381c1c0105a40450280c900c1c0d441040503400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 441163444 1250 441162194 441162203
    0x12080403200102040608070219080904020d0f0608010b0d080d0f020d021303020f1c0210020102071b050907090605120604180b0105090919030807120603050f370609 72
    0x8000200244030300130f5015000c1c6001040c800800501014800075204030b52401d0b07a280002841815034030107509810401c50f06600580900c80b0846201d506c1c425000000200c407000301e5901e00c0c03d002682103c0580020303d0003805400e22440110341c5110840b060341043c46c500140490f86150044000d0140d660390000c02400000d001180c03440328a405025203000304c90700c0d04403207400c5007045892012041c820f0440d1040d290b2060152400703c1a05148000600002d0324280352a60380310b190705480c07031219810310b217066402e2200341442e004c0c50b50300201d075003040d8204508244002d400b502a04940c8840904101c0004249446a8101d5400910401015407a015852034540111502402800d00690054001030440c00000a8020400664102d0410b03200d01e1500c00700c1e42250010081414072107080312036022581a032050b81b00a50250016142c04612031234000d040c6200c00d142c150408000452030400649041180c3e0078030203030b0074241e1803131070b40f2460110050400058080c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 441164694 1250 441163444 441163487
    0x40b10080a060b04120332180a030c06090902090a12021f051e09100c060209030607111e1209030f01020a0903031101020301061d060904240e010312080403 68
    0x54240848508062114803a03110081d6030521901f0b0b0ba1151240500c01c0901882807210710090304403a98000c0c0801c41520300003c5000d40078502144000340c1681c02101c3e06428440c0400c030352540304560001806560000354a020600000202504014010540d80701841e01c034000031990380a00c0d50b00c10907250b24070a02c46540005024001c1d8100d08461100741c00a50300c503c010203004dc044500c003880084c881c4501c898080f108881407458a241258145d90822025002d5034042020078403441c0590703149407405109810180c14290f4010030904503052541500302e40c01c0e40862194418070007040c001c0d03201c0e0403010009140600d6241000c0d04d6501c0043c044c4051940305030700c00142c81c041c5d03d800a0b50400079098500b00e02c403d219800000e21401000b200c1c0a01440a01603880401070405d41083c604900007000c0340c01c0f00f158480d034040c1e102c0c0040703420b522032200c1400070f003462041f040496255844030b00c031040d94900c4d08020040071000240c03c040c051148100b0701140c00a011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 441165944 1250 441164694 441164699
    0xf0a182603060a090203270a1e051f020706090b1503060403080f0606120a06060806030a0b010911070b0f0415020406020c1002070801090305070b06040b10080a060b04 73
    0x4003281858241030400030030a002200088044500450740220400b810240d0f1082c40c0c000c00342c00a410290890359040c40b410340103401c0e542080c0c080440c41d1000c1c40540755000140c035041000000c0441e411022010407540308000c00d40224140448103081100c892500c0d0061030b00c18002d1180c0040188000d141078003140074040810040e603c916028150001c1994800e01010b5507400102c0d07000b00084e80540c00101451040099a50000c0c1c000c1c12580c1000e05600c0000358a4404481715502d80c0e07550f034810018981c1c40024240c00c24000d40107017440740b5040c0ca40c50903c56050042418054031006020036131240502210074094019440141500f400c06500340d54035030685c3d0a4400ca81034032007030311202d2914401c40302190710f540c00404488880c0001d112000c146504158158000d4103c0001c203d5070130b01512111034401d03a51541c1e80c0084d817034034a00304a80600114029480d0800b207050ba5103881040d08034080550902d2441562540b50440251003143c020843c64500402d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 441167194 1250 441165944 441165953
    0x903031508010b040f090506070c020d0f0b0906060a0602192102060a05060103020a0e311d01090209010b07060207120c051b0f010f090f140123030f0a18 67
    0x18010010f0300301c0341071000c0110408004141c3d146484003601c607401102c0800c0c049805400030034030052028000014501c1c0a4460a14101c4040025641c0740694030801210031000d000d0654442012607540c0100e9003460070003540e60300d104000300300040f0404c44000900400850340703145144102c1c3c0d062411000e295000b9100d00040e0303031b21f000040c01d00010071402d41c000e0013620b01c04c00060761003039100c010a00802400c91070980d0071401c0300c14203400c08510305090261860408440c803601141208601d07080049042c00001601c41c1da9140500602c01030707590a40351811121340c44031490f1030718040e080040c0288100e8031b000380100b81c109014088281c01025014039180540e05484889030146d00c0d0079030850710281041d521140d0710455140a6000d076841500d11180381c0380140001d070b00c4d46620100c2040c2c94000315003440084e014446607607409480728010440410600705500840c000c50340c0310303002c05400c42007845681d600043c0d000d4859440039116120510030f941c0500e0240c05d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 441168444 1250 441167194 441167201
    0x102010605030f0a12050418051909060b0f0621040311060103030e090606030921040504092316260d18050321030403110601030c090501090519090303150801 69
    0x2404c450800742d885800008071b008005031401c8450b100c2c441031000d41e100070000d0040c00300910f200d040c05001d07142009280850f1288000aa101c0c100026100b640c00080010042140c50401d21805040201148030942001c40c1d0040c0e003020903516070284c0f9507203000c1d151b18048441804035072145000000901d80d04c43d100f01e03e000801d81d204482d0f501c80c4802d21125100403501c00865078020201d40d9505440402c0e007141340807040d0001400c117a260310004058601240050710344240d90f4180c440e180ca0300903100902840440d00030300c800028620400d020220600c10308150b502c00c4030301c010001005c0002c4442842190007694080007413440c016005c8503a00c00104800061500302140e107090000b1425800d00b9a080c02441c080400003070891654402402141000100002000b41c8601013041c0f030b010b14424424001030900b8201c0c80012104168804078245082009011801c51080c0f080940c14443c02d40116012041d42015005002325160b030500d800c2030a42c0c0024014010f51 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 441169694 1250 441168444 441168463
    0x1b010e0907020f031903050a11030f060109151e030204030218070c06180614011a0f090307030f140a0210030903090503070815150604051c170408010509060c0a030b0102010605030f 79
    0x1b281040144c455908200448900c0c10180b1445003003000814031249074a10001d42c032910516001c44840d0f119030700302041044403a41c580100310050740c14842031107c8049195000f2051508600b05865a0001002d40a80d50ba00c0e5001000c3c141c0415000c2e403042480030b11031600700c2c8080c84840c0ea480a11400c50b5000308040d2103061510102a50700c0d0140f2414504031841d4603040c18141d40c0b280701c10411540100d003000d112540401071655039440620400c001075024031254100b80d030b102d04080c4041482c0b40c00250241d04445d8840c801a65030b0305045005003400e01e00000d4491107482c2c20303640301d8030580145506201c0c008000644513400514021000f170300c0c1030425640d0700d84000d10b01c907010403204520350120342840244014185080104041200c202020505440c141c49040080500c00c000d44040c080000d010702040b2024000c16400c03d122500800c2c0c1c0d0301e0110f00c0784d4454011700115104250b220b14070201160303c01d400c480050b000080c159240d15282d049002e948050301c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 441170944 1250 441169694 441169697
    0x510030201080906010f06050a020106050310020403020901090603080d0b0d1b0510030e03030601181a18011e0302030a06030c120c0e090a02010e04140f04051b010e0907020f0319 78
    0x142c00030301e2549011420324129480404900411421b084064a042c1c014a00b01d500710740d80c0d14800505a501084460a04030302003100598690960042c046074840c16000301c0381007814480200009465082101c581406a50b00000c2501955000901c01c17440c4002c040c0c082211504044902500c00404508135032080700d40b000c00c6075001000390b0581e1a4002e030744c00150402d000048c804d502440404269006c0034181119440d00c483c80421115900503400044140209000500c40909950700300101400d0800c5442800c4000d11b403554004500d40c408101500071010902c25030690700003070003440c0d1020000900ca074580c000070304610a0034005544602104400182c4140865a01809142c444014000000b5180c0042d10008440b80665400035030303540045002c002032310384c041c0c0a00c00102400b20141443d0038280e1030a49036035150012511b00d208025541d030307048a01540076a0040c2d4100748140c3e03a0b1501030f8201495010310b9402030000040300b50710003020892050b2600c3d40c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 441172194 1250 441170944 441170957
    0x614071e05090f0414091006240c050d050a09240e0303160602070501051e010e330a08010c0e0904051516080106080105061b120a09062d0804060f0510030201 69
    0x2034207560550b1028440c8807a41d4000102c40024203004161844520127181041c1034040c10680c0c50b5407400e40d540001c24001807002c40c0c0410000d80c4000d04400524143c0800c0c10112484095121600208510311081c400b154003100026102442070780d112200d86403c0507018010380c14113001941c8100c0c000c81b46546004001601c4030b00c0c03030300881d030329050403da0041f481c1e090008160005001030130800303d4014083c41503a15003019000b4214561400000b151124040700511101e46040d40260001da414000e82c24036844d88407030408422202201d0703514031900c86041240c20700d40c04c6c0304c0d0302e041c4030b0342842081006100401500041d004680e20740c20143c0c0e07112401c956088080c0252a4400010041c8004501046a0200c803681c0070105982c01d5281d42a59007240350300480e041400b150307817144104261500b0900710190000300310f11003420814200488602d298813003003c00240414400401e0a0128903801001c0d152138801c002c000c14100785030615201c0c540c0d8070040780044d59 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 441173444 1250 441172194 441172213
    0x3030f0f0b090604020a0807050f0d1104091d1903090504050117060f0c1602040e070e0a0c050918101a040f23040506030c0301090614071e05090f041409 67
    0x10130b4401c0314600017032991001a291203840c801c075080d0b07004510410b5004400d014a003e460010b103d510041000007100958481c60080180296030000c04c4244d418030f03401c41510705200c0040755402120003410505006020746148c10b0307460a400b0782000d0341040c503000020642400020181a070b40383d00008403055541ca4a00114600c0d42c12120110780400034070085d00004826080000303007520052001c108a41c05107142c41c6024459484014135010b84414003442988506c100d0080044a2030100e20301186100801c4014401040703c0b100307010200c0026882100008402000d422403c9900c40c04032018403040719290010701a0005041007544005400d40d41c005143d04a100181c13060300c4072400110411000705002401e144d01805481c03442c500f950360a02c200d20000340b0500000490416407820380065580041010303060200c4203c0b1451440c4286501020300380c42894040d5848a0329408241d0b0502a590a15009818105100c0c0d201403201c8680f442a00010f0450f01042c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 441174694 1250 441173444 441173449
    0x301080601031b12152d0506030705060f070302010e0a1202011821021c030e160e0a052703030f0601031b0e1801080703151a040903030f0f0b0906 64
    0x442c0c130034640f88242d0400480c000402012400079500d01c0d0750030008103000311a1003030500002c000c0784815442408424030155003160300c0744982004082d0028141c003810b19010640512460005d0303618000c1c00f0400c001090302c01d4214010742e04412059a4600c10245811a140780920113030b100036508010081190035a00c00b200166150480105400d80d100c036403c0c0304d581490f8100203411402034010400c05154007080c5206940c2c5d85640c0005d181c5030545525003000c00181c0300a01c81e4031601030410140038120f860940042c0038510016080c2c60300001e0904400704021407403468003104c40e000001c0309010000d9440fa8444d0320540606036641c0004500722020003440d031515400306039000c40c169104407010568104003800e8250300340c5440c840c1c03482c1e1903004d0f480359425030b11640060007000764251107090240132207842485a514817100740c4480d100b07000481c500072a82c80c41a030003070621940000301d15450041041002180d0801d1441c048c03c1260400c0b070013050910081225070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 441175944 1250 441174694 441174743
    0x5030712080f010303051315050c0712080a082d01060e010c0203031e070b0c211e04020607020901150921020103110d140f0702030a0c020f0102030f030108060103 71
    0x9100c80041c0c800943c0c00c2d1794054500b500a1341c00845400705600012a1a400d5160b001100c1c14242c1c8841d0341b541c0480f40100e1904040e90403c0705003c0380f5015402c00186101c05a80b004c0360103051001d250341e2982111014804c504808070b070700c2030244803102e6100103400034081c186e034682d942d41c03005c0c2c0242c20019107180281c46802500340d03008118100c00314940e0303007109002c01d4219050500e4030304135031541e50100400342d1f10408415000244806124100f9540c0c5000c40340e0781201d5909450202d20041000c5d4440e582c0c01088144140000d045680d003004848031594001d146035070780d50b15a1407a46440c1200c229041c0032440c9100007007404400c081c8118600c82c14113030280d00d0100e0701d6004401501c004103c000d01c80c1f5040c0b02844003a81ca40c06085881c0f00e11141c440c0092908440309400010003825410a540040080c1583d10782e010201600c02c58043e16107004089035480103d180d0300c20001003200140000c000450515400706030745040706d0040000142c250384154500d00300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 441177194 1250 441175944 441175951
    0x7032d0b0609090d0f20060c180a0303230405040c35041104090804030501020d1103040203211b21190f09050a0602030702041a06090402070f06090503071208 69
    0x3c0b85c0e0b2940002d04452007000350700a5000800e100903034030001d92218501d0000280d0b030096015402107111400c2000b00d282c60140403800b166010f640c07a146072005459400717214030a1070004040b4034002221861002254000d080c064001c000f94002100014440071064442000f41580002c8856200d2041d13403581003007080e00c102d244281d07190b41ea03807420701c003110000707003908141c031110210003080d284009000114060300c000343c2c3e10600c828070407040350383c007011096000109009200160318005030360b02d8442c2c01110304210500901c55a54400e010300302c050301c11044141441030401401103883d41d030310304031030031401c1c4002620740700317040140910b800404d417440c2c15600d0710503a03038407843c03505201641c1c034100340040ca03880300c0200d46901c006420040c0503a200084080440c24203109008840b08a42c2050355070711556000a1528400c60707511900c5030b50007160305020b10186140d0380005d0f981c000c03410442c0c400d140c5030041c0c03039400c481e8080d10300b560045003040c2c016002e003a01510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 441178444 1250 441177194 441177197
    0x60c0504150e0307050603010609030c080601150309060b0619090803030705030609040c0b0d0c0e01030e12070c0906031a090102041a0f07170405120703020307032d0b0609090d 77
    0x41e080001c400b00d40628012035040e41c5071180040000d49078444500031401380c4000ea50304002d046c1035060018000c0ea0550140c2d6450703018600400501203810340e00000d00d401e9281c04a1054075a0801c0e03070181c9103100c0840c2e0310180004010411100c408020400d281e41c640301e00c0b1603159914100c0307481c2e020403182c9101140e01000001c1c50380c40c08403a440d9010303210f014001c00c516260340082c1403d40010100c0244103a640c0c000000c00c9800c1156000e07860804d00c1d051104104800ca000c2d01c8010600c3c04104502c0041106000c00c50604144400b822562000f000940e40d03a0403d0980a15140e44001500c4500008101c10810600072141074520017000c900600c181040e941c40941c0c4415561554000144100000501422003c110351100410785a40740c030708040c1040301c50b05103542d01032182e40c8611820001601c0c00f18140d01160740001442001078401c050307014220b14002503442c05003000403820010001c1d4105160300030360050b5034406c0c41c0d0ba500ca5010744c1e6400742c07465070390 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 441179694 1250 441178444 441178469
    0x30106080606130902030f011e180203070303110703022701050109290c06090705090109140a0506011e18050a1d07030b180405151003031805060a0309060c0504 70
    0x3c88240d202d402c2401154409011078013650942e410203800c4035240540caa90f0355641c111242411221401864030300960445000580740c1140d001035580d00b070b9480b0041c144807683c06030301d0010394184045d13001542c0180000c03040b25400c0c0200901c2c0c1d0300f0304880250449905c400171907107502c0713554101e054500801c00444841c507001440f07145100f410541802154041084e07451030003083c814a0300034140d24000300059820181040780c03011058120548440c80e010004102c0d82d201140c2e1908102d8000c000101d03501c950004943c4842541d0a02c0400c1c201242c90380a81a840700940c03035004140b44a41d800d0503150780c100141303080300e84500d4480101c3c0441c400040700e0a42130144e003011090600007403114481002c40c09903102041c01140e201c56101c10003090020510040700d204142203c0401140342c60007100c480c01100d400b02a04100c0c1007071210000c100c0d01d0030480081e0100500141d244d500311000140a05803980d812102641013169030010030f800381c01035405840c1c6455255 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 441180944 1250 441179694 441179719
    0x8010f080118110301020d111c050c0405010806130207050f0111040f090507030608100c021902031207030c05060c07110108062b0c060e031903050f0705010e010614030106080606 78
    0x40410f4040ba080350f541550b0800c04224000750f244584403007041519000758a580002c0310804803e80c5110810180500f00700030400c1c10300011007101c080d0781c030900304182c2c2074031000d0104040d0b0703640440c051030304c910000708241400b000042c0c65154100110090107a041d600c07078100f0050045110300e00f00f04010340e0003072000490719000b03241e002106141c0000d8055a0b400000c3c0303890303000c03040d00e09840c1c2e5562602801580c1840071200c02441b280c1d600c107040b40c039039003c00d64a40d4003402c00c00c910017020402000301031040c12050201d85e001000c46041d814101085003940e8000c0b0b84c1118100c060380445030003075009446192151b03034018003460030318082c00441da10601400e60b0b81036103001104400300001c0d020385805c502504059947c41c600e180f401e0185441e00f0021003030300000c1895150f481c00040c1d8004100e41001d00c0444001d5107825003032404030302414080c0ad4441d125401e01d180070400c010500e02d81820383c00210300a021082d5100005920307100c05a075180d4000428074841c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 441182194 1250 441180944 441180953
    0xb0901050f13020a03240615031103060319050f030a0806100c120e01110a05060129180d021e01020d03020a360e0103060f0203010501050a0c170a08010f080118 70
    0x703081b44880b40c101035021b01040161200444038240c001d116a0305194031001a10b0358103200703004201c4142d54100386503003080070001341d07910f40100c000d0303100700703a40d545003030800100f40070380c0c401184490101d90701e0300c424110143c02e0702401c5500700c4c060324103032030000c40440c4107004a41006810144500f0080c0802004481007042801042d060010750070009091071002c21188030800d001e68060316180d410000d0140000342944032041d01c5460202c0820500c1c2896000c45000d480b6002d440080041ba60340403400e400c610320b0000e540134412140920140c510241c6413950310b40242d091720031409104900350b04030b000c0c12091500040365000c808122410780d0740100341c8030841c4c14207000c2c42140c0400343e44038002d4503042140c0040c0100700400802000f030003030349110004100709605540c10a00001c0c0380d401010445820000280c114105008803420710351450b00c200042c8580e103d02103200a01401c1080c81007402c011002180044c503840103100d030404d400325109414804800700c1e03e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 441183444 1250 441182194 441182213
    0xb06010e040b011b03051605030c0c0612150411030c031501031b050c0106090c11331005090703091a0408092701180c02070e0a0c030204030b0901050f13020a03 70
    0x171414010200079080501d401c5a00d02c28000e03100b0402540d40c2c0804103051820415000c04442c0240814008104000041002d241d44140c0d58080c18000b842664005005400c40c90840b096820002081c0104006520011403045620121680c18180b003013004400311400402081c03415000f100d05146502e21400c0100040e010060001c503405031034103170000480751050f0041c03000c2000c06840c0d01c00c0d0340c0c003032000c941c40c003c0013a03490f0400c0d2010200441900340c0c03000d4101c03005800000142d5244890180348015010180a0702d04528083c100900284071001040e50066584104400503c0030042501e1040303600c003000505007400d01c014406003059841c0010524107504160384500030450041a00034580640441c42843c042c000c48804c94100c0c0410000b1500300307000a000702d007080304016801c0800002c00085418106908034000d00071078200400070101441070028089054100e00c0c003840004a0002d05611110401c201003c8100760082d0080c003492404c0000c64440320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 441184694 1250 441183444 441183497
    0x150c260a030f090209010e060102070602010207170a23090109050415060c03051905130e060a0303050c03040e0103080318030403110d061107050d02060907060e1017040b06010e040b01 80
    0xb40881e40100c503600140003c4030980110115407040c00030043c0a45e810803c06005143d81c0c0003c601d415016201c0000350f4074040c40c4020031000004100414520681c24501034000e800b00c84010342609800c03e0101d503100401903400218200c102003120700d418451a40000c6100010b50704031481c10105551a0b840c20340150203000040c0000d0740c0c6400c3c3d100d0a075001e08407540e2a155101d1000d01c40c0d607085030703686d0040e295000268041080c0c51725400511803d690301410015122407080020502c1e610664000c015540e041000000801000401560042070a121501e02d04180b403039000e81d4900482c407000d4007202c41c0252001007800c03c8050306000b03d009420100b417151080c00c018074240d01004003140c481d40080104c582080e8140046070704000600050400e0320301d03024000723144902c91840248980c00041c0b289000394040c4250340044100440d400c20503252600301040441801c41d4101d010a90b901d04820700f40c6807a2040b0380c0c0300c00058407407915001d48807075051131003031002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 441185944 1250 441184694 441184721
    0x1020312160e060a0905010f0c020108040b0a0f060b0904061205071a1e27010207030b0c0c0105010b0a09090b01080a020c0a050f0f070b0304080a050a0504150c260a03 73
    0x2d810000951600f0005284429240d25015a070f07074900800184a036625004a07020800d2101d98440181e034488420ba400c1500818215080c0d112036014200915400280200e11850141d001403901c0e001341c05005078280c00c68040000390384d2038000341080c42c500300c4000e00f2600140e80900070b00f0f100d00213841000c403071203040702c0c10080584da11202d6a07983c2d21801980300f5000c030705013080080402e91517000300d0134110364020720080800082d43e59403450100030030400c031030000120a90405400da441c03840e59600240140d59562904030701c03540c45090344100052032000082485c000324010f4000b00041a9074615155541c018184020741000c6c4540e5040c3c0191480403001c18010000f04505007002005040d0110040d45d106d481c001850740503001e00041482004080340188042d500c142c3c6c100e051055070f034420194102e40920403500324010b800a465003649032541d0141d00144034034400c1d50704c4106024400e00208018900b5001400e01c1201001038041c628803d070000408403408 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 441187050 1106 441185944 441185957
    0x10c050306010c290117010203010b0a0c0519080d18050a02040b0a0f260115090b04090204050c070b0f1e130803180106050102031216 59
    0xa1000341030049082d03141c0180300c41d0806030002910940311341108000919401e0032108000c0c0650021900b003400315888002c014403c5905070b40114400c07504200d901c0074100ea45510840088409000b0245601c2c1c1482d01410380b40d6006101d1503044e0785440405030104120340c91002103000c81c000e07450f217410225001190041010340c043d107010803d13402d000c0c00320301d03a211030781d00c582c1c0380c690600800906035060b2100d010000460080f400d01c140a50000c81c0c0c01d8a1840352018110000451b041140011540c000345d102400074002040e03104940d0009400c665049801603400140000e22004201842000f9035014201c2c0880c042c06043c50140355a4400064000d80d050b59a04004140041c0d0f42980111200d5801020b040e520b00d131007042103003101c8980340344e580150f081950101d543c3d800481522200007070b003a0102c25a40d0b5683d0b412042103060040d40c014041c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 441007194 441187050 := by
  have h0 := BRFrame.cov_init 441007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 441007194 ≤ n) (h2 : n < 441187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
