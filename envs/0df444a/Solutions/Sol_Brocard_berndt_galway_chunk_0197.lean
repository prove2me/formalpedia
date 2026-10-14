-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0197
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:23:54.396413+00:00
-- url     : https://prove2.me/submissions/91368dae-a969-4755-a400-00208532ee68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 35251803 ≤ n < 35431659 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 35253053 1250 35251803 35251817
    0x21c02030d11030706180201090b0405090708090c0d120e04090b01060509010203070503120411100206070f0302091509040c110601030f020402040305030d0b1003020412080a0207120501050a1803 85
    0x1855600400b88800420214000c8905102096030380c042141c281d000c980d84003607a840185001c560b400342c0400094142c42500301d003414a00000b040b5034003406000a8148000300c80010404081000043d4090390000c080c440f0384142030400d8800b5515902282c0c000400300405545581007602a40c40c00355840f15800790079130319009044074130741c2200b075902d41140403c0040001040307007000030b40000c0012184c10358040c100391030450420312036805854050041881c0d1443c20303a030049071840e800182800c0201c070514068070110002d03c100c100072035101901c0d4650550380007610000d40403102c0c00703441c10442d40710309000940d50a0b864010220b0164000401880001d05580800004620203403000d4106a00d903925142181c201081c0301020716601e88400c46185040b10085541c0d0545080452902e800d1801801440d0050100900003d000080301042c0e00d02c20811040142011b920301c84030034029142060203032005071610b8a0103810250500cad10600f403407003007096190b81522400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 35254303 1250 35253053 35253073
    0x3030b061312050705060307020705010327110a080a0c150206040c030813030b0c07020a060905060a0809070305060708070207090b0609120c09070c1403030f011806120609021c0203 79
    0x46039071041d500040f20203001e007060010f029165800554082e645079000b80c00c0e01810071000400312091030008045800380d140b08048190351444100c008550018030754101a00e000c0049030b040520740d4002c048510a5411038014004269250030550f00401c400c084020800c0800301d0741c0703103004e0318080d1850a0300c42040000554400c01010480c1e4201446503500c1da41c0d403601080315804881c01400752200240e02400c5203850506080030700554100692040c1c107250218981d809020900c00a1056540c04a40a4841044048011648072040310003c0c5800c84000340340440a59030742c009840b42080101f0704440b140504200c0c024050200d504081c207036010444c6001624441c0e00450040d4100b40e0b0880c1c54107034109100d12807946810040c41c149140009100550100310a4140c000b48144400b00c40c62102d650304482c1680c102c1c0c2a00c104031540701006246c2c0c0e071b00403090001088800b200308461034011036515802154030903c46000b01c0e030616010400c01340f000354036400c0300c0101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 35255553 1250 35254303 35254319
    0x807030c0b090a210b010303030911180a0f06051009030b0a020702030d050913090308101706010506070203030c161706062805130207050d050c030d050c160f03030b0613 74
    0x104c0d01400c42100f5400e003031821350303c1d4400a05401c1c0c00a03800207445036045400d0000350300145044081c1550260003070740b000040010740740d0003d0b0543c0b50039501c866400b800140e417074001b40c000d0800180103190240d004500503003503515600c400c813400304000700012002d980d28800d135281c054000d00507015503a9244000c607019480450b001342d0081c88407840c2c50031001c00f4031171804102d201e5203450380e50b410248018200782d04a0780c0650800d984124844845a0000c55041d046920582d5041e442e10300c2c0e03100180c00c6000d0304079038032124452032a50a000039400302114003200d00f055110000140140d4186882e07500c119446a000500d50403c4100c3c81c1c0350020303150194100b5940301d003209840d040002d00340007240005d0180a07401044103400e001090000d9541411503003030062414500000c80d9442c5d005950815405a030b6900004a802c902c3c4401c0303400303047c0d445200702190b000c1c902e40b82c03148074100c65050300024030b41000c91003141496022a03601260301c40850024a24000c0c0e8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 35256803 1250 35255553 35255579
    0x5030f030c070503030a0b0103110405030705090403020304080d0801140103110306011809020f0714070806070f090f0603020c0705010504060927090b0103110a03080d0f0b0303040807030c0b090a 85
    0x8104400c80301042040c0c00b03d401800518012122a813003c25101000400101900d010310744841d4001c8040100308455a40000c404045890686030000640d4441c1026815070041e6030040c02d060142042c009034607544040101e040e201403103221006640700d07a004600700d0300c1c00d54624003400c00070004034115601845400c81919101808040d041c1c3e03c1c1c0c01040140d030480c40310041040408200001008100f0b4005031840b0b03041402403080514210764190b1743e0b4801760990f4140281c0101c0420003600c0f541090b005060b0250009c0c00d10f030360300c1d04020000d600589504a1500601e00c000c1500d40c414811501180c00c01d80c3d800e03a0060070305480510700904540c8800e00048140070404a401c42c1d401101c40726405540001d1696245040016001130100103043c0329028216042c0001103444003500e18100501c5000220381c0120415000141820898940e061102250005031a2800160941528442c1040050391640d5140b80a4203024131000c0300c1c1c0c81800001d0a201032049211 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 35258053 1250 35256803 35256811
    0xc0a05030a05040c0807270c1b06150b030103120207050102030910030213030f0c0806041a0a1404201f030902030a08040305010b04050f0708060f121203060a0605040305030f03 77
    0x4541c13080c0350b66a00c1c5519142d0558401022050b01c0031409400000f0500c40144459614200b03110740000244010a00c44610200454501c0b00e54458410300200d0f50085007000c1032a00307088045078803070141a40c039070024481156900250800d40240768804a2a102110030680007181441c00c00030030040000040c9401d4810503509200007050030b41045180c200860040c90703440800c0e52a03003480f8020f10780c56001003800d60300c2401071000041c07003524000d881e03404044100015444040641d0080c010441c0d2424071030100505008c24040780159120440d81809080403120302004203002845005d40c0400c828003041c9250b01444e24082c1d0001c101c1f061005007603034804120343c0e464154980180e0000d683c569903030300d800406400d00703104580d00456100f007035185078504084002d000c520003c044031300410038840141c01985521902c0c0d640c03100b2440c01c0c1c0e042da00c0403c40713000f41904115030640c13044010990004a41d4041c400b00d406480d0000c02551800855450b009220360002d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 35259303 1250 35258053 35258063
    0x100e150904090506131208010f090b0406030b24010c08070206030705090d0c06030c09140f040b030a0f0c14010c0803060d02100509151306030902030f01020703020f060c0a05030a0504 80
    0x107000b2400050080c03100c0c40c480e00d00421441d000901c00d04129040700d142008a4080c0071501006100c4018144021070451b1000070020404001031008100070341406d40c401030501080c041441401000558565000b4105442803220008007000449a00390314110142404400300702c64009030030a00c1c01550f200d0300500380540307425401000b141c00001c040400381d4620400c07040c18850f0f00d50500414008000302d203000c8103918105100b044071a181d40c0c18484c400c250100802d07429807602d401081010310005c0c00d40390950b01d2030070000f0104454207422901c48400c82d1010455000c48010f0b54022401030359509440f5140e03944540b429400501801d41c869401803801e4010b80d10507500310500c41c200e40d80c00b51284c11030003d00200541c804c078903010540082c030003140c1301e80c81100c40742d044494074540403503880300f1400840d04025114031220119400003807900241500040d82400d040039a90450f8a5940d50480e80b5005014071900351000400410200c3d500c481140c0055800038010f07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 35260553 1250 35259303 35259311
    0x301090b090a030809060c0306042003100302030c030d05090105030a06030807080403060b090106020c04020a0905120a0b18060411030c090106020609011a0306310503030402100e150904 81
    0xd440300301030044121001c9049510119641d401c05610800715500302ca6034900501103402d2260b1290b510f40801080d450150790f45050342824510b00d0380d04200f241c3e11910403d03599084c101d62501002146000c207074042d01c60700090700c1060a0000351103031040c0640c0c3e103050a100342d18004540581c406005c44104544400303010010507103c00080c8404e500c642c0301c680d91503242d80340c01170540f09518107152003840400700400107176801148030303480382004503401692520714400547d0756175640d41010fa080300d01e100c7d0300b2026143c0018400e029030b020346111000c4d40d0f5031540160f064044011004000d401c0321021500041800032465125200107090f544841e0b1010046008400241d102d400103074801c4041c07140c0075100b0312646000380c4001483c8403e411003c0d001c65600c8101034203503079245c00000e039408004418221216100154440c002ca26220740d03040480c4e681e001580d051744600a40741000d41e0183c0079240b2001d0344036010f0640308961441205141b104e4006130301f03050300301e46c031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 35261803 1250 35260553 35260571
    0x201030213031509020f01180b2203060207060b03070b04050402030a090b07180b04060504031103160902090f01030603050607030f02090a09050411190909080f0f09090906060a03110301 81
    0x3c0b00c00110400381030460008500c1c0303080c01001801c1c480300c03c0042c14456441c645003a03040700c3c090603005850400d090181c0d140d95444204d55903804039110300d00003007140080441000880d03001486410700a12050040d0141c10041545412075407040100d5110200020007013400c140d00a50742c0300c3c01e0303a20006070134134690b128405d08400c22515100080ca1542441003040500e0b145030380503080450115041070b0408001030220700c2035000290440300751500400290343c0800c003800522030032800e8a4005035a41c5100006074104030221031062406001c20545075209104000440e50001c009008549406500ba40108202ca0329a09582d0b000c00040425460303107a082c50040034200d10004803072030036082034521410322808652040401c41041c0340b41c0c807102c980fa141a95290343c400208081300c1c1c0340c58007075441100329000e680d9501084442140e030040000c0e014245041d95603400da90b031540c2000343c840f44115016070740440d000c5000e00101d282261b03201c80c0105c01400024a030390b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 35263053 1250 35261803 35261813
    0x8030304110102070b03070c050105010f0b070809030f030406020d0206060405100e0402180115030b03030703020604032a0c080c03010b01050a030b12150610050c070e060103090b090c040e07030c03020103021303 92
    0x84111903070000f0590840c3c0c8d00b410014240305060040030b9181031409200d00b0082c0600451140d0b02c4080c04030300300400c82c98a2683d0502101204400d020222076586d6501c000107910703052074548200c0903000e148009071050419019161181100d8100180158100a03c0380c1c5d89141c00351040e6049840402488148460413484602810160700400483e0f0035154000b0166110040d41d14001d13081131007910300280e0001441500b00d545801c021076020402c900000d1030780005618031401009d500280414001281352820a590715001581c1440e0b0700102891309071200e404c1003500003441049241c0807640710380d10040b00c4150050504030001c00400d80b161401120202d6250b0710b4560200707011040c43d20034034041101c0154144142449404028180c584060b4402d2003420301d00d845c0040d2540e031113548102c1a840d0b0001c550b00d01c505040704060750b24020084070740d00070381c079144207084050800a5110b08890f800b5002c005440d007180c1c0110065040824103e00c000600c950110003d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 35264303 1250 35263053 35263057
    0x313051603060b03101103011412060408070b182508010609050a0b01090b0d0c03090203010c0c05071d1602011e020a090b040509061e0411031e0108030304110102070b 73
    0x50051030041265944101054180f00719680c02e0082d50340345c1b100001110034001c003664111416a41100c0080e140d00d000320700343d5240400d4103040c5000340c60810081140c450050003523030b40900e000c014a03507900880707607010041f403000c49881503202480c205c0c07211400f440300602c803503a030380b108a070242c2d03580540d42d080da00c00c4e400915100c1c0d10358041105c203172840d1241228084003464410582c40c50201100b0080c1304171561018015240c810170340116020390411450194081e00800140c5444100140b26512040e803c82d0a8043c0ea03100151401c1e01d0494810000103c0d0940c0100303890301c40034455102a5404000295500c500d0b1520048540d81001c54080310041005680c4041e010402804401c0581080710040824401408a500c0d03070720425500c8907042d906100c61622045c03407003d03490380c460803040c0d00074107000b100b811b200c181ca809980070301201c6841c1d0b000954a419900407444090007941d24a600070f000082c04a10b401420100c01101070060303c285a2b2240446075081e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 35265553 1250 35264303 35264309
    0x6020615030c0d051b03060403050a03020702040612050307030807030e07090510030203010501081b011e23030901020a030e0106030506061c050723030c030c01050c07090c02010b091b03130516 84
    0x81d4201094820b005000401d098a1710a000c6018060341e14241d0390180190081ca00c411041660100d8814215120740e80504054403002e602011050150b2030026500d521a104c1200058000008242810700030302480c0b804025560103420854182550000244402007298002c0c1c2c489110010140c0c40178810399002e085024090700304649110b0140402c403c0e0b001841e81007000f02d440101211003409005031030220b4914000c810b610162115079201400d460310101060030000500c1743c0300d801507004001aa5a03a1020300584001d0040300d0308888051102620b160000c20014005190031382940043c682505c141162000f4940c40d8986050401e4000c40d140c0300c4110402950810903007003214807110110014001018543c0119840e801b08405203414404041004004410184040c41c09000605000c0010304112400203010745010481b1500400100000c1004d00702494000782c04080d482c80c00e0b9295480b800041c50585100c03600a039450b0048010400c4c084046d08184002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 35266803 1250 35265553 35265563
    0xd1503172101030b010306050601050705010c0f0e01080c03070804030c05070602010c140a0f050c010e150402011e05071209030218060109060f02100e0c030712060b010906020615030c0d 81
    0x5560715012120264541004110410710100c00104005401142140d05480e448000486c041e161440140c030f190140d02c0303005100b03500b000d9490822650107028070000d8041550345080805c4104015108000145c800f5582c9020400015048a0103030381d51079009444bd18000c203841c10b03251500f0381811a5030700100300503512000d01d00b0000d903001180a1020740030380c02c805d15008145102400c0c09001040071030612001207001c0b614880c0039842038080d030ba101e1003680c0010341080d84448074034038216001c0b030214503010300c0480400c541c0103004c009483e40d5203e8030314144035504c604800b84031140b01c0204000d400b00c03010005071140d00400c2e01401921200321035900f00300c40090700002540d000302d004c002030904eaa0601650004508404040c030f0400015a100c1c5e41782b00354181550001c0c82d9416205480c00040d42044100c55860303034134002c90f0108524455140119011000d42c0f24440040c1c0c03106011541e11404021080d03a101c03801003c9810300c0c0e4518002c01e4081907495030a4407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 35268053 1250 35266803 35266807
    0x30c021207260319020708070603060510020d05070f0f06110304060c0503150d14150a0b0306010506030604020c010b09070c05160302030a1b0b04030807031d01050d150317 75
    0x59a8000c2005a4080c01240b000008a0405500c03030ba0381c81c060008001c224105440e040115207000b0b01407100540070f05029100419210000600503101e20311507240a070b1092078410201c3d0b4070209211400d00b0742035803460301d0320245444403503454103640e005586070440803d09400003074070740c491068103040030b11031251640340a0901004480d0084803007014800d0400c00c00c0b10003032400103d110300b044200d0300b1001d041c010b41131007991903a40010100c00e074442c031216080e50702450709000b481041c00080c1801042500c1c01810b407558028800d0a411807030510100c0e005140c01c1c0c0180400480d01000055900181000107402c13140540c0d8072408a403085462005020017440040481341e149202c0e881000e1440d40420380c0c40500c0c1c04050402202d41c809503100305000307549440100a048541c580b2a0380f03034100559154880342044011964080d610420761140d003040000c2d03d481610b529003404207048603040078102c1c100100082c1c3c030102c0000301c0002c0e40d107215481d4600d209907602d0703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 35269303 1250 35268053 35268059
    0x613080c0a08070504021c05070207080f0715110102070507030606051206040503030a02030403090312050a03050a05060d080d0b060d05220b0411011e0f090f0807050607030c021207 79
    0x2609040c03144030380a0107180603180501c40500002501d1046032070680f001603982040300c092800103007204003500d2060b800e140602144542c009140c1c401d9a492038290b50000024003031440d03503016036205200000d0594008444098012000c5050481220001524001c2e981e07403200e0902d1400c5c0c00c1142d2180d40d40c1c02c2480075080c540030042e002c00c9607000420850900707881d041c3d0b69010060006808940000008042522400f941e400555004034000d1100703000c1a8050016001588404002072030000091200e2240380640c41c020308001e441e0155450075a241c024050340270054a000c269220302c100c18941d2180da000f03004110107120001180e00382041c0c00c482100320b41061200d03e03101c2c00e60070800f060011000f00e80003580801070082d24a91500143d50a802c0c0101c0c1078002310860b601072690b2a040040c149040312256240c00940307071076034568100c1503081e000e6070074035501c461011301c180e0030b115004106850007410501c00324035a907030008490540e161058901074101240c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 35270553 1250 35269303 35269319
    0xd020a0b2109010e030304060903050c030409060602101815020f1201080f060f0703050a15090f050a050907030b04050102090d0c030b07050a050904090303090b180705030309210c0613 80
    0x76000900080284002c4004c1a1826500c1c04064000703000c05a60301c1550b0b007010300071411039041c40c1c024416291030f55a00c0564038018446807203040094059200360b40c200f200144203180c070116508a0041700183d4548503885000400080d06060b00e90800c41081080c0224000e450f09500c0700702410641d604044215050515809180c100c80e4880c0b0b05000315400310410741503020f0202c2c40d0000700c80d40c50700070714000386c140185000c5c484e8020800120b2059000c0e0840004240300620a024030340700c01c5620790456000f1181080540c21011702480028071468000380c00600070070000d070a0110789000140c182e20082c00884000d14850030800c10800080e446070350060850410909189c0c0e19000944188a00c1c0315461140d541e0343c40120405000ea400010307440e130003500ba8480340c82c0c10385903c14413210b45520000d1038421401d0000f401e00d400022141d119034068414002d415280d0300600c08800035039000c0f4160f0140d41c0400b40309031145400b8280340411001c46150481c03500c401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 35271803 1250 35270553 35270617
    0x109020310050c0a11030409050a090b130c05010e030c0a0b0306130506010806010c030c0609110f04050c12040c0b0a090f060315150302070c030b0f0106050a0c020d020a0b 75
    0x9144034075080c4020498001c94080c15500e2801c05402c00480340300303c40d080c0e10b0840c8100d40001e80701c00c0c03030318003446010842035204840580c8109410070058845101c2c4441078581c8020042042e02e0451040c403003544070320b9a40f0880c06010b822915040703113060004a4420b81c079003042e07126420202c1001f6251038007035503c80c545040d5260400190070400c000078068000148450306100c081c0100004040c400e480c2d42e210650050740c2044030386442d16000d05210302c804020b84c483c0728480c0c0714681515180c4142405904680021850604841281d40304031500401c00d84040ca003003800001c2c1c82d426003000b4014500d0980d00c0107103030b50414050300940c900540202c4101450070091030f8034200c4400c00b41d020340e1030854013a080000d0341c4604070040d1046031070043c4603001e111000010444125800340c09410000c040462603030700c56038101ca660050264110000c1c01c2501c64401500b40502c0c40001c0030700161000110381c3e02c2e4441d0705450f60000c15850300304880182e06c0b60500a000701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 35273053 1250 35271803 35271823
    0x1030f050c090106020a0221100504140d0801210807030305040c1d0403080a020409150302090f130807020a0306112206230919090f0b0d030509031e01090203 69
    0x900c404043d410302d0750080d03075410300200c024081d05111825003a0226411400188001810125961201e1020440c00500400c1c0c500729160542c1ea200b80900d1072010603082002d006590351111035a10340368211004070001442100401c0180302448081000c0c6001000c1d2503002c1d85010600e4106032038030317083e5024a50310521448100308000b500c0302d0356480050390070981500c0e2502d000d86981800c100207105a500c280a0545424481c050300ca4074143c9900842e40202d58042d21951a203601482202c82100e90f4240c04507004180b40000b42c3c22805011203500140c0000340050b2261b0340c0804890300c00b49086450003000c20b0654100700200c54202c0c0c15950000b42240701480c100300500300860b40000c84a450340c1030321480007007404003401c0c0e600310321b0020448400003100d102925902940750051071051410501c01408040711409010704050001e80003c0c0504801d490484007034010303204807a854081c101d41c40d10b070b090080e400428003108080000a9400480c0704141c03400030303408 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 35274303 1250 35273053 35273059
    0x1201081b04020c010b12160e0c040b070c08060703091b030302030a0e15031f06140a0f0e0901080c040e1204090905070f03051606110607050906040504020301030f050c 73
    0x1000e906000d0000e80e20101804a0507540940c940034800b0005000d8190003905130b4000c0a0b80c000d201c5403c1000600200035010b036445501402c0c0c6502e80403503155012030b402e40040c0703820442040740050520051031807a000341002d5082d6a12a66420f0511006540520010384c80d6071004090041c01100c000d210241d111031841c4242c9581d40194803030142440c49418003007001c10080488d01c400d041000d1140400e2810303941c03480c002c3c0d044900201c0c0c44801040401c00c08801203081401041d201d649070000f0b001c214140904ea40007203850050310030f02c0404100d81e00c0300590b2103441e002c080714060711010300078101072603004042c0801c903002d050802a065028801ca0402c0e403d00c2d0302110b06540c02408089041000c905143d403520109030b001442546d20101d0000500602040d0300c039012000070750440100341d0720780d4215186100300f601c52140c0e03000700d00429449402440203001307580e809802207040c5981c40b40041c040340c009038419108c40c11200314030310401400340800f20303901c1000c0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 35275553 1250 35274303 35274313
    0x7030213050d0b0601030f020705030327070b030604020304032708010f020a1205040203030c0307140105072f011e1e0509060a0506010e04050115090b1e030c07080708120108 76
    0x42d466070558881c01404c0207040c9941c603c1100c804d01c0043d01111411a04041280d40e42c0c05c0210800052241e0800b80100d0000b80e0001410014004500f000c101e0306100340c1c060550b100c410812000b544003410440501451541c80c0500001c0b441c81d00300c0d0140302200400969103414049400e4803604141c000a0b50702c1040340040307a03038000c6042000c210040c1000210741d0707618400300c5c1c51445152003540c0d40e807002251a004100381200e00d010200061b00081c00641c464541c1a10944a8a4105214000e81640404250441c1c07450702c880c031034100002250341380e400840c0341e01c020b00e60040080c04548500d001d0380180c2c1607140d01041e40141e10030800c0035162048074640c48100240c81c2c000300903200d4000c80c00c01e070b101d030010512803c0000d10820555a5400e400b00c0c40c4480b840368100403070f00303090b00080c1d4030b208a0300b503e02c41d00b00c545d8410074043d24880140c00590004040d0302300e404086c05884041480312000c1c14841c0d215201e001c0d45e03a00756604180740070f00164444030f4540c0c42 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 35276803 1250 35275553 35275579
    0x9060a0e01020a02030a0c06020f030c1804020301050612100b0c01020c150121080d140414010c1b1b080f1603050307030e0f040e07050f0102030c0703031112030703021305 75
    0x10010403286e01080070300d084050300b02a868000c01070300c545031078921400d0004c000e000104010f8002407103511250316006009903400c00912040e80000d02c40d850780208280702d020b0304211284000750348090004c3c006180191200f00300007094012100a2413aa90b000c120851580c20400100003102007115000f10740e50300d030800340a8140750b00f00c0303140d4000300140c6c920810044282e054131071f203000d003030001c2c45038540f4081d060b0b0640380b08803001c0e1120490322180354500f01040c82403810f01c2c41076941e99a64103801c201115180d20800c0d8040324900d0900070701c161a03030910000329015140c40c0003d07002c14940c43c45545d20708040384182540c01c1540b00d6040001131800001c0305c0805c3d6050600302d940d50000310003e0322804207242410b400c141008000c040c074039000300703182090300c90440b0720703d001c900d0319001203a4034045d802c00d0b4000d50b8003410051020034040c0350404030960f2040101d6030b009462803000d0a460b04156100400f00341c0124070b041c14460700301501c0300600000e456504c00741d01c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 35278053 1250 35276803 35276807
    0x30209011215060c080409050408120106031a100c02030609070501081e0106180302040c080406060914060f0303071407050306060d0503030609250c0c05030304080303042909060a0e01020a 82
    0xb0302c901c240d1040c054031010301c0d410407812070f003558010103140c0b604001c10b1034681441c00c0c0703070391005070922415114200085043ca00a01c140380210904a118030f0f804024170090000d071405a43c40b50b0180803101030504010b80d01041301030300c1032101c10094008185450005002c41d0b8018101c985481406040d000000300301c0410981103a5052a0a42c5403500e28550b62200c003e00d6000a90003d0811f110001400d8002c0c200714013842c03040300104110703a81c1c0c1d1926812118200082c0124000715000700e550343c48c1007000c540070002c0c0101039030b1500410340e0362500522981050540e082e04141d108010500d03040c012581e200c3c00c01d4510070415000c0c0c2da1520b031203101c0101840d100303c11241c0428150300e030b0791100c1000e000f0b5041c0c110300300351140c40000d481e00060f40781c1121018881e810210b081e040103c240c074200d4079490029030071901c941d92690b0181004144075001d80310103030340052181200100040c00384ea40750001d04141d041072185a001d45041c000b00c400e00742c1c010040740840304c0e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 35279303 1250 35278053 35278091
    0xc030705030d1b021003021305040c09050f060d02070b010617060604030b0403020f0318030601050f010c0213020c010219030c030b03071202120d081f0f14120d0302090112 75
    0x10303038140b030219220072040c01103c2c40d09030100b0780030703400c1444200e000e45220307010390082603909014214000d959a50b5403c0105403004001e1b03240000d498a0020030190410700e0340b641c69400000c09403800c01c42006440e004030303048074101343e44c01c904900040101c1e40d0000c40400d1481e02e0300700c001115103003e4022076140c1c41684402082001003070b0004041c0741c8244449040b012815003076903a21a0188114043c82942d420810310034082d1200028092404a010804400040c2c403030501545040d0200440404c103060840b400b02d40800908070302c05020301c000e10050031100180d4040290f041d500600f10760158020070107041c0351580501c0070b40d5001907400d040f5491500c0004c00c0d160300b4408280416100402c00c1c90505c42c1e603d1041d81d1a4000b00d0040c40b5070004140c10f0350445000a1003440305401f44611014005000f03001d1140c462034264500c070742000500490014040314800078503044119046000081c3e0210740d1103140c0da440000d20309880392401052003070a419140c0d142d180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 35280553 1250 35279303 35279323
    0x3210917010b240315030312070807020f0a020d0303020903030418020301150302131401031508010501050907020d0e1c081303020f2b0507081f150b090d0302030904060303050c0c03070503 82
    0x40556203124174031503900300300f01c0311181002c280420440c1004440032b003d80000b943e2640240c0101150303c51014400180308210580040c0800381142041d1016030095109000d66901408104404a51a0b065040c801134849030420010303500d41c5800c181090711141d00a1074020103004100c600e0762084200303035013819a045d21401d500f0000b80c040041e0001c0c100e0003074452070188040340c0002c00200c10361001c0d0480d0000d40c0c964400765242c400c2240ca400c0220b40e068082a008050028941400080c20b1260f1404107510951182c00d0303214500709400c841e0305000e2504600c0d0050003142081c1c0d290003101c400c00c1d500480e0314642404500d0322807071207071010703030482e115000200c00340502009107100500190301618520411040006103c102c410840b110081c100860f200002c101e2403c100101c82c101c0f01c1c40c9040c51a0340d4200320300118420021b030704610003031140c2d55481c3d4580c401c3d04002c1d48a1744655980c6c5001180c8182855681c014191013a0040402000700d902e021421b6602 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 35281803 1250 35280553 35280571
    0xf1b040b0c01050c0307021f0b15040807060203090a0905040f0b01030b09010e0106060507020d0206090a0b0403030f02060411060903010e03030106051305190608190507050304061503210917010b2403 87
    0x80c07482c09823542002400c01d002510b62281140802c2d006401d00030000b48140d40b0450203480c10b03035860341c8041e6540d1280d14a0305801014980040003022030709c3e40120b800501c0381107010300081054994021166003071300107403a05000f130400d00a015409100d5101024005402070065612381034014015004052000e4090080d070390f0b60b202190380c0c0c203080b24081c19000300007042c0592204080074050f0014007040f808249d101c80e05108050000445500c00e0b640120102c0300f0055250601c030b9070743c010b40203898040d9200c01000000703207800c0c40914040e020750703900c00713486440b000600141e100c2980e0219001790702100c2403a489010002900d4166521401c080d40e103920b802c0401007440f004907910281071361404040c031206e00d60010056004502640c0180244003500c1d80c81d803407140041c4001860411600404884803c0c0440c2d40302c1c80c940e503401c0151038680c0e1440d0511150112401800482c0d54840d0030f0311507460030410508040100e03600e02c842c0003071141040c040e244009412101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 35283053 1250 35281803 35281843
    0x1230a02070306060303020303010312030504150b0d0f03020105060a0902070b06040b0105040305100504020a240e0604050d08070506250507020a050303120108100903080f1b040b0c01050c030702 85
    0x21854001c00941006540c014410010740d42d907420000d48039002800110340f804100310b60100b03940e200f4002c83d4081d80d00300c0c4055070030490508111009019044c440358210302c50041200c041110b0030141042c5074040d1300042680d103000d40820884d81d5958000b5920f1600c180420781c00f00c0e00c1c3c049602e41c0210281c0380040c1c154220001a6403c5c0a5940f0090082c0b00d5110280c21240c5103803c0240910300c2a18601c0301c0c40e4540c011400c40d1081d4103046004810580c030b040306541e20030806004610006007003a8030f025121000306010118400b805e4804200020f40380d1300708242086503039403083c180a41c0b440c0396106140c1183c8040c07038510101c0100724010828070150765550300c0c0e102c010311008040b00e40d5103050070b81c0c0701035248092113510140d0040351040ca451140601640c5c0046900d541ca00e551340c2c1d166040400700725400741001180703500741c1c5105003420101c64003c00240164290854407405580c100b00d00392580100803401c50a414000d1041300c0d40c0004034840c44440c004001b01c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 35284303 1250 35283053 35283067
    0x218090f1515060f0703030605040b01170f061504080a0b0604090215030c0d06060806150c030406030218040603050f070807060c02090901150605040602070b18090702100c050301090b0123 82
    0x1d10341c3d00400400071381c1500e001824200309a010313071002c1d0480340251414001040700030010740d00004d070743d8003040340c54009800003110046080c0c54207034080c038018920400302c0c00800111105412941040d1001ea001d0600d40382401100321506034010021a001d006204d4254041045200d2806640b05001004808180101e9030807061724074401d00d8041c1000407035580c9600414121042d200540240c4011581c0c00c0b500928104886040029a00561500d0300e0164100c0007036002c03199a0341e289256221001099946000300001140180010407485d50070b009003d080c900640e000c1095948081010020642c204904050f01307034040700d952040b035480c100d0290140484002014050f5008400810195001000b510039240345908843c1c030b0700d4a03111a035039141718548001c441107000b0b507030301e20705860f14004282e4400385034070554964a40c010115010794000300e0f04000803640100040c00900640d00c00d04207800000d02c0d0030340c8040c042d0f154a64201e106d0308815203800364001a52 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 35285553 1250 35284303 35284309
    0x201060f0503192108070e040c1409010306091a0a081506010302160b041b211202030c0a06050105090c12040303020d06030203030c01061a070503120604090218090f1515 74
    0x40303010494002e214002c0721312000e4004103100c40c200c90b0040882d20304003450b001800c041c4203c03002c8803503d40f5211000b64808020210540000c00254101515420040381544c03482c0244002d04020008441451022204002d48440e00b5085080190300c071030383c03000070701050b854042d8118200303080060369101a0030320300c2000c000422010701014010710900003002915013090112829400350b080038251034041c000c140c2c41c20b04016100680d83e5448100200b45e01070803111002ca08d900449290200b13621030903090184540b810b864260303903400100800d091102c000380c0e0245500080b2450404002100d0f100a4006000a01055804500203c0c410742d95807001c800345030000c0c100e90f00d900c12520b1050207803030303035000e12110782012150400140c2461001e455507a54404061800c0c01202d14020780244002000c2651003034032801c80d003016894021302100510350700002c040c200d103005d207140d42c6408a101811020399004010440d80c610901e200306800041c03000307a0600c035075010400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 35286803 1250 35285553 35285573
    0x909130203010c09050906042f12070503010519030305030a090c1a0903011805060106050c01060b1603020c100c080306060706020307120606080105150c01150f05010201060f050319 79
    0x200941643ca0000c0b035412007030300614a6000c444d01107500b050141c2d103281c2800300781d032800c0300c5400c00d01c4050014030740c0a0455050004024160605aa003071070f141b03415241e52001309448020128200000512282c10300c0083c00c0c00010f0034080510300c00e0714580c2d00030300f5444004c0c541c0d0360b00340d5980500c0702004000d00c0c4c050024807030684005003801d8003a12440c01644115040d9200750300e800347d20141c4c0b030b074034031003107040c850300003018050986c40d003d015505540030707004000d11556290004200b158008000d441d020700c9500c0300307802d11030451a0203403800c204901564411006101c080c241d96038844603d50712aa88004080c0e113a484240100312580184480100b180c2c2c004010041d040d54800c081c500480c00c00d1400b48282c43d079412040d03c100c0e01c00c0c016035400821a03121117903810403041c01400c1d09031000d400041c40300030307000100040760160b4004010030960180c08104c81c1d80e09003d0304001d400281614020301e403030700000039503c08a0120580092482a8200090101d0100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 35288053 1250 35286803 35286841
    0x308010e1302031204050f030106050d0206030a06080d0c021e0603010b0903010213030b0405060705030c190c0b0c040801060b0301050307030b0402010210090c15050c06040201030509030705011b020105090307080909 94
    0x100701c0f9144180840080f14a030014046c0174040d1a02e19050030f40f0b4503050243d40200d860191031600904455024410710741d0008049029454840324001407400041004a00300c2c062580c0300e6002134a103204010720155420701e10b0042a12060b82c1c1d10701c170341d10b01b0300301d9045496480040d03036a40d101c003002c079029019034042d505014460300d00c00418042d41e0b02d02148034502c0b4000341ca082d80e031060410342c0c1034001550051400e100500822800d510098010b4000003074500305030300c4404140d0f4130032849040854204000f00c4011070208200394090240c0c501814005281502303540c103020220759218507600c005001516a840410117690007400f800700b6051100e1418404107086007001e181e0001d580c031a400ea109600b00060340c1252180003502c01081600300903040355100c1d90011005004040d120180c240410414000001da092040b108140c0701c45134031148401c0c5a82e8080d0854100034a82c00803074108000100002c1c03214412202030700303000c40355640141c0310280400446c9100704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 35289303 1250 35288053 35288059
    0x120a05042109090f021902120901120914160503070311041a190515040302010806240c0c0a080606060703050d0204050604081f06080a03030b270108060601020601030308010e1302 78
    0x40c0d0b004c00c112031075002803060090700f2501d814282c0e9402c004903038498915038002d50108050150b9101984200c40c181d0200c408241c021a980340d46407601800120251641c4080750700c680f03480c0202411010109000304421000b50680c2c52558481901d0135810540701446103942e5544440d9943c244c80120300040f401801b0320049101103c80d001340401540126446811448420345004a4035000c0b00c00743c80d8180d4521046868074000d000791401166805140500004890002e014021016008040a40300103003520007049040c0009000103800181d0550820320070428180c980740201c682007036051510669030300700c94000d00f0080c01250001540007070006400030354003000258031807030b054046841c81d1015949502d410106d90481c030540e039550304500500d40119000c1c1e4841e051140b000b0301410400d400003d41013a801024041c503c90b84c080d24401030260f003904020041d406842800102115415607d014000580502c102c0c2e500c00401000030300300800c80b4824001466010b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 35290553 1250 35289303 35289311
    0xe0d0602161209090b0105040b09150d090605010e040f081b070b03090606010c030207050103091505090304060207090b0d060c0c0b01150210090c050402090105070b010605120a0504210909 82
    0x1e107800351107401038400b00000510408800f0565618510075000301e448140c4465103803c0c5010395040303c8e50400750f02c0c00ea00028400b520480500da1310700134080c443c011040018880c42d82d2918000b148c4041c1c200f009054105400c0100048044035501c607210b40040c150360b04d546440c40c84400e542c0a5106042a500030395600003402110b00e000b541c06101080141c80c2c16603244401102c00c2030200101030010f034001c0c40100501d5020b540038034920b80c05031040100c4180303003034615025900103039000307291540b0000c0d0805ca21369050000300003904400f0b4003440f0f149918400584134002c21132018100c130b075030b0304289814079000b03129540490350710940d01032280d07a440c219050500152043c0c00050700541003591005603880c400c02800302d505c0303100c5014403801c01d002c3c0b000940200308580d0501c10b00b00000d401081d0100e003580d0091185a648555030341c0304c11f03641d00b01a0380c05803102265504100c107102c0001e80803100585044142d9003414000744002c079045601801a0b480842d40900e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 35291803 1250 35290553 35290597
    0x21b010c02060f0f06090a0e0f010e16080316060225030c1103070605040e06030a0503070b04020a1208090d0611070f0209161209051f020a030b030c010e0d0602 70
    0x200361540703d02c8503490301000a0380c8001158424843c120b034407680c0600d541c40007642ca4902ca07030003102000303c10400c4400c44501c244c141421640c41d0805410740307034444036155040402d401d031401c001d00307008800385041040281c15084146003540c0c000380300940100300d60070000d00030701d502d0300340b280300040c0b85100888030b050140040e044210300b550303801c1780e08141d1415414000343c09000c45940d0741c2c4452600d03161a4000000840c09800503505000c1d010b6621b0101d01d082004d0082c042c06003143c80c000d07060070f10400c0640b0310181d10802c4004031079014071004c02c0030001074600740d010540340d020818199103480002094017000c1c3d0048000045901414017514808080c43d0920964040708243c50b1408030f2012641e004040e440020b0788085070503181442a001541c9161068085480c4909918001000140c04290007106a5400310785442d9555242c02504002e1206034050903003c4120000200b04445c02c0d000305000ba45a80858020406164100d80322030f022010003060f0508 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 35293053 1250 35291803 35291807
    0x14010c0f082506050708010b09011d030304030c0e0a0606090605030901060e090c01020f06092a03030a0e040c090b090418020402120601110f0a030e18010b030117030304021003021b010c 81
    0xb40208003076564529200001c0c01042c01041a40d0607695850303421410140701400460b0040310040600041c0139040307048800300d44041002e800075611828010320407030700308000d00214000080a041c1e80340e08110040203881c0d0859441c40503a0014030f0696500d0f5140c1042a001d408690702050f41c0703004000070460403680c0030541c01c004602c26402c3c0c410000e80500e501342d5075801552940c00503044020850005180d501346601860551500200003d00304c400281c00d641181d0420300115825400d51100781c6814402c6495041ca541802070440341092042100381c02913110142c09140d40701c0480c0b480c0380300b034000d505207194020001c2d13640320b00c034240c4900245001e8801d14040f960204a00e64160030200c0c951020325190001001001c0e055181214101409002c5681207070b2802c5483c0744949000406e00e020344540c035413566482d494940e44040040c3c0c2030039000c42681090040c0070040c1e8409003440740c000742a240143c0c03a450340d80da04429000e1070035070168a1b503103040816141e03a5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 35294303 1250 35293053 35293117
    0xb090312180106050609091302011407030c0c1d01031b0306110706180b060d080d2307090e0114030c090108060402010315050d230d02031314010c0f08 66
    0x1c1032000003448590794540c01d000707590180289482c3e00881040015410604110581c0c400f140140f419018400c02051500800e40c031100781074001640c0d42603503e050003030845070040100400303490400105004130307050640f1001800001c0c006d14000b21004018412101c0e510080c41d0404000c00140440c41c561010543c4100b42c112586424884001003401c0799508980506402c002429110342d07441d020806401d2044404944e218420301400e07000759207512540e10b1145030000100b0384604884c00e62080c60f80001c1a9600700019418188803009043e86214110b4904010352000510b45000007410a40e0214880d80c000407070740000039402c0400202c250007075000b0380b4100180700081b920548180c106001313164000c0040c81544c4006007070413200c5031000c1b401d80003005001c034120440c241080480d5001c88016840440d61100c1e09080e4410355000f042c49115030800320745c112001800601c01104050420b40e60380f00c648061160250031100003950003c1c00b0038000050a030240070072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 35295553 1250 35294303 35294341
    0x40807090b010e030d050702030109170307110c060706051003080c16050103061202010f0306030602040b04031403120f0a23090d03090321020d0f0507020f01090804030b090312 77
    0x2a08007840034207194010400500590f00c0540584076000c5600400c0e20740341d101074000c07a015036035074000c0780100346a445003601000e52003094541d242071400000b0030340c8080328031f01030f55a088407424614a640c0c0004036031803e540014082103035543c0703451101403001da0703500180201800203003070760400c6008108003145504881c0040e02d22500c410046044030743c030b070240d414040501450180950f0140c404001541042d18020580c40d48a907100700a1f41c2140d07200320050100403600b403081103060342808040e101d58000543c10036a403102c10b00d1800d14043d100280c01c000403000b03d0701c4000d6039040122401c1118140340540801004c0c0406075200450781c40c0c00a000351801407034094440c2c0100465a034160b60f84d46030041060b02c03082c9509103046008142e1903400c20090182907c0d6001d15980a0040c444c00240b078a84104064206410f421005402e42d25040f10131000803607100a5900742ca400c00c070703188420703034401021910758420080d440c1041c20380c840c00c0100e01400c2913451247e13 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 35296803 1250 35295553 35295569
    0x20c010b09070207080a060218150c010605090402060403020405180d020c010801090515010e030a060609020706060807061707030f0518010c020f030f0d0212010e0103060506060a0c030305040215040807 88
    0xc150b40d6180101d85540540c000e420250300881c20840115045401814080c1184203858084843d1000040d19041d00c1070081c080f20354002c154102a01000c4c81001c4c001d0406840101c0301d850180d0018600d44100d01000340304503a66004034060910303482500032581d8403a801c44817542119607000e5520046c8148960014404d4400452014094040d0320f025083c2c0340c2c0400c0c80c0418000c015107400071308021454151140d440000d0105241d405007200400740326000503074a5003a801d10000b500d0ba10b80000c0f43d198040e2604101140e8001c0e20007442e41c0f024200c0090b21344507a02c0071000780c4001401c50089600300018800f00309260101a070140500300300801086044600603600c0300c0d02c034025805503030000e000e205034000b0020f00801011a12a03001880d00c441410079145500e020303000075074426508401441001414410030b60031100c1210024100010304170000c004600d140001010192070b0004101151116907007004002e800080460711180c50300c815681d1f62480e4458810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 35298053 1250 35296803 35296819
    0x2010f111b01110304060905070501030e100515040c03020d0c050a02070902091918051518090a1202060702010605030105040c050616020312120a0908040b030c1201090f0c0e060405040b0102010f020c010b 89
    0x7442d40c040d11940d3700400b0b40130064252208a0304010004110007003901c2c807040d500d401c41350b09a90361449045181a038036200141c54000c1e080c0f4400440310480c80c21414800b04001c8151102d4000894030105c8104203409030351400c0201c041082c04010000a84201e043c0c108049078001d500030020404800f0010104401e0b40c034036510880341c8400d07002c81500401c0092000e00b2100100740943e80c0200490100d440030002503070351100c00341c1c00743c2c036081c01a00140300740107081d40c0c2805000020302d0118002e001c0c60a10340c4030300550001c248240c510030840001c0d86040d00c15402074405446800030103440e107802041c0315030304403030b440034800340d000c4186207000a0342ca1016100700301d442a0840b0406040906008010f10242d001405002c052642407010340b00e00e003854100d0074040c0c0000e07070020541400c542d000030241c4e01000e484c1d009110703080020074520707140c0c041035070229841280d0101d03ca01801c80180d0041c003112540d92041800014001054081508401c0d5000801d8855103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 35299303 1250 35298053 35298059
    0x807080712170a1d0610030c0f06020c010c1505010b040f090e0316080417070501080a2a050405090a15080d0c0f1a0a0501030302010f111b0111030406090507 69
    0x903450342c4a01600035084109002151901d140c55002c2403000c801000300c90201c80703d81140d03500e0040c0c1100c0078001102c0f4107000b4401c001a241d00c0320000c241c80312a80364040c0c184500a92168042d00307490741004090a00d103000c0c0000c3e044c0c80c0b0f510200b000303001c220380e503110422610290f00501803480503c003001c400240741000e41c45410700c1d0712040700c0035506004503403070b0040040a03508011ba988090500012828079040704071619900340e07c8000300107661501c000542a030000410f0010300750b1a2400a0500c4c0220010803006402503100740d50502c004010300b5540e6014641016400c42c2100d003c006000c0b82503401004101d80c0100340c4452540e5034140e00b40d03550490380c80d003000503848030010700004a56a041225031842501912455840f9a20303030480b40c0c8044840482e0252180010001e164082c81681444008034001b0301000c0ca40c07041c0180030748145403204807521841d00ca9000c464000790b1080ca400b40ca400f003c20345d40e08003414254045d0003104400d60300c1e030007210000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 35300553 1250 35299303 35299307
    0x3150e100806090f06010b0d061509030302061305060601121508010209042007030503060a09020a030b12060108030403021201060e0106020a0501140403140a030603021009060207050a0608011a070807080712 90
    0x1d100d0b1381001c6001418268245009845c0b42e8001407900c90311a80c8030440418868030030014501c2551403a560040c1003880c6080c02840c045000d0b02c1c4c3c0e090910400c00c0000400c0d00070410030340c4840c080c2010031000c101059004000c09050700d034000090003080000c00c1c9484190000d02c081c10003100d042c080d8030701d603100c1c0c244508030085428241030001c10401d000030380544007075039200200401990130940c4d1550300100341d910003800c400000e07540b00d010070001c0c40d003000080d000d125410f0051803d0b6041c5400c0a03902c0c402d50001a2180fa80c030602402e0f500e0094001d85c018248000010180d56035404000e0f540750100e0f14211180e509000c2c2c110f120f03032268119144106e80507a215994118041090a020751100303418a0406485201c080b004d03849846c0340e80042c044640c5c5d02c110203458081c1c020f0804000ba007100c0d1048007c8030302040002d42c44401c050541302078603c00e0800703900040030400b491040740001030141c880400e0304024802210003811a40b0b00034000744070720035168601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 35301803 1250 35300553 35300563
    0x30304060c03021212060108090115030b06040f110a11030d0603050a050607020607090302060a0e030706050309070f030f111c0f0c0801020c1005060105070b39090103150e10080609 79
    0x11421121500170001442e030b61241c032101e41c01444440c000610b030245603042c0c55100900d50420b842603041e000c10b015441c2421300c1010440f140c0f401c0100548640354400d0b484500c1348003604c00800c8000c0c0e00b190b000000903c129442610b121100300510f070b5a901d440f03919425002000d035000d01030900007840990010076541d10a5210340d449003100d900350382c200440f54104d4034a03034007081501070651500b030f00c1c00c200301409882141c4555469251002c8164a40401900810980f00e03400c0c200300b0000d21542d0a5806080d4070803000381c1c80d190060049004907040c020b980d01685d00040f112410f0014014541100c035014205950045031117140180c03c0c1d03c1410485c80b500c0d8000c0041e400c88444507400150040b40515080e441c0ca11303a40c0701c00183c0b841c1510101079080c03000804213803003c8a41c1151254801c5030061008124204414481a018a1080c5418542c5460305004c1010005450101400740ca045c0013003030b400e04048030114511280501ca0342c1e407150384041400d0901c0020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 35303053 1250 35301803 35301817
    0x70b04110907080708040311010507020a02040b0d051506060f070b0709060306030302100e1f020d0e0d12050402030a0816021801081e0102090406080a03030f0510030809010c02030304060c030212 85
    0x40c0c10303c85031245142200c0d803101c010000c3d400c1001c10300b14145c031800c00b809100c1c05038500d40e000f07008402c050300403c000c0382c090001107485440140c900300c00041002c9141e44680002495000030350383e41402082d414404c1e18030145071100000754040c2040003250016015070b206a0703030070701c800d0784508083e4220352081c080500980c0c000c00191200d400d0390741104101c10316a4054031071200f0700301020602c0b22303045400c002c1e0f103035004a640192040180310780300360400c0c0e400040c580c0d021009006020005200c00d1100e626403104006001e54800b084601c1c00641e12004840d503c40c1184078603150710703400c031a080344250715400c81c00301010001f151590580d10300c000500103205131100c26031040c242d03038080f80c60305540078420301d541c0307036243d1066500070100312018085a18262070f009044602081114941c136262100b070003031001e500d0201c441600d07031283c0d000b0341e1104e251005071486000e448000f9814800001c000c11501c1e40220170b46440351280c0c003200c8080c401105440580c2c040c1c50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 35304303 1250 35303053 35303057
    0x501151d10200a030c0209040f0605070e0102060a1503080a02071503020702120f10020a0309140f0d0309080a050906120108030406030e0a0f0209100f060315060e0d0206090a0b070b04110907 83
    0x4178042c05132401c14a01a0043d1064000b103a01c80c0d03c90303940c002070300c00440b61040030603006034260401e035805002056120103441401c02442c005000380800403210740c00040d14040380483c0414065000f00041c02c00b804030291450304150115600802a510150049010340344460001d10044800103603a6600100032010700b4258480d151603400a4101074407040416031030b007648070f0214507608040aa00c080000160014010b10704500d0300d4400f0010594040501e4200650042074901060f110704001038540281c1c1c1d96441800030b000c6005d047d008108080700800000303044100000180103c452948050040c1140c1034242902c40d030b08000007916081180249800602d0708807880ca0f4000e01c01c1c00302e40780094450101c040e6031402c43e0010f101090341c400349081e40c600311a554900400107807030400c81e002d18030404249080c40114000307000380300c041582100f50390741038030380400341c45158049501c803401e80c102250f40705003d03a801e0714100807074140b05032a0f0610a030038600c610750a07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 35305553 1250 35304303 35304317
    0x60e0d020607110a021c02091e010306021b011d1603030c080d021215010e0f010c0b0702010f020a080f0a0b060301030f080f0a02010507020708010501151d10200a03 72
    0x100005540403655a82c00201c3e41c040d0a514000680d9140c44c0d41b00c0490300400c404540d143c540c41442038815001d00300c0c20203141885a1510410303402402541500d5016a0150b180c03291040c02c04003000c41d00f00743c00c1043d400c207060a1b000c84420350000810110000c100c0b031440780c4482c0101c00c0000e2501010700000c68085110012980e03203c003c107000c10907000010700d030411101d0800d071814400e0390454a41280040c19230880e40c0d000800030402d105c11036010950310b07281c00010303104880600700141840c07002c40000310100d0003075203d41680f03954800c0c00e40da200641c810003401400221164450400880701180c500210780c800d140a504010300003610356400c3d502c8141d14031a202504449c403880c00c025030342064440c103029000d1142290008120f42c20315010103814071916800000c13030750707251000412086d604034203501c40690690626100503107c0380220011a20041c0c80c05030804110308546144075030000c065100020014030390f81c14589141c0e416038075900d60ba0400740000d062 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 35306803 1250 35305553 35305561
    0x6090f0306090809032d01021801081005060a12050109020301030f0f080403020a0f0302040b0306040b1302011106160f020309060403120c06050c190206090d0e010c050303090307060e0d0206 83
    0x45580000080ba0141900a0030400c0c8000001d1034602000f080410114004090188a40c0f8040c414600020309000a504100054007030600180108030454100300040010400010012080d00302a010180c030080d0794016030036025182021070300c4000c0889281c40300000d030038116842581d041e6030b800740525400c114951141d00402a14401c00d6441d4602000002300607034a280882008000340c14800940b41e10754010001118904100b00d07010381c00500070000004c440d99825070340403500c00701c100302e040e02d24001200c200c80b0441f50591503102e140148030344a005001c4418481e407041d525000d80c00f860000803600c90040100a5070401005d20007400040d0820140021020861074905428282d039210b4009a07001541e02401407080041c0d88950501002152201455180010040b6080c00380065983c0c1a13032801c01d004001d00c030004425660700c2120354410690b040804ca0340c99042c0318200c1e64482e40510021503074646801d24854140d2800310b00001c04400a07006030801d070303036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 35308053 1250 35306803 35306813
    0x90d081006051b2d0a020d0b090102040b030f01050306100609030308070311070605040b06010e090408030601020a0507060306080c0405010e0a0519020a0201060e0a0204030203030403030c0303060f06081006090f03 93
    0x80d03201c80800c1e0640d00c3c5403030200c0402c101d80021410540b0001d0480c10320b850030011001c00c440350900d40381d04a00181c402603145c00c0d00c004945a4000700100050361307000741c254024040c0350000c40c1010000030620110400340655503041e80c07030480956a45854154108064004601c1400089402500c2c204003283c00303507100c03551083c40303810007040e888400d21001080d64006007044840320366810502091028403100190322540a0800710000c07548040010f0b80e0440052000700041000000188940d00c00d2103540240ba502c0011500815101d0700003030050096030046801d0341c45944a1491a440d05005940c12150308010100d19519041c0644001d071200901208207100135054603071195160344010484000e541d0300000e40e071410403d240c118070001401d07808040340103000c01d2025130350100c100c0d01100c1e030508100034441e200d490180c015152540c0452403019900d8030006005070440b40315807098510003a0039130120748401c0309a035000c840d030107600c942e100205000d0002070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 35309303 1250 35308053 35308057
    0x40501082d0109150903020d0318080309070b0301030515070c20010c120509190302030c0607060605090403030606110a0c060507170c0c011e0e04020f070609050303090d08100605 78
    0x24a1000000c6140740329603e03020404c101c00070726029085e941d045a8000d0590601405da0040080c0c034062100c50401e080701407000d014807101030a400f0001020420b4020b040100783c0c001c1901c80001e41d101c0da9641800703501c80050f10f441001c1440d1820000340355a216102401c01d0543c000088071715425201c610888809a2030b0f62a814040d20b0b410b0302c00440c103907501400c07100c00c0f45e607038aa5641c3c038803e06201551f440f185205010f185002c4040c00160307000305840741d8050b820ba9103242c943c400303030070514040c0c0a0741d030143c3d8200e1065400d010525030305400c400152412605c4d240f1020a00003600c541d0707440303c1080a03003082188002805424482d40003411201c1c021910349102c1031540f00c00c400d1542c003a0407041d402c0d81c840c4a21000a58200d8a8410009603107040040c038402c0014001c0d01c400380a40b4100c0c8919400619915003002140c06d40e01c000350401d43c2080f010b110b40c50240d40e82c0c0d0099800880c24460410949030061064403414481c84820000d000c0407490311000351a6a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 35310553 1250 35309303 35309383
    0x3040c03121b0b0a060b03060607120c0c0801060302010306050d1203020d0e010501080703020a06020a030203030705030a020409020c1f0e0c040c0302041703031b0a0206060d0203030409140604050108 87
    0x200703000c0034180321072941c1e4000c90302d01400341000b401242441d02444003215401e80c003901581c05c00780204010f6030b8428040e60300d40350304200720500b01181c91104940b2591010300007000b080b40c070708000c01c0211055200c081038078400e03201088226100e00c2004030038a04000028180d00141462502040c0300b0340141c1050414100c0200d82580b00365003560030f40f00241c00020180d401507100b0420f6190004801008286a0002d0a40d0012940300251280b01c0208000705028001010500c0c14000360704440c010100c0c560215207d4460943d41511821803462419500007051801c40496006104480307045220390014000c1004007418400a4501084200b0034583d00784400990301100c8400a9261500c01001e0750b40c138a401d134030003501c00c0c1581d508800c4078001848001c004076000038060303030005412100c0c1c0030360b10300c40d1000900d103104a8100a0381c0d60304018400b40602c440c0903100e801160308071420700050782c8035085d06998003050244a902c0703c0d0962003011303810816058400301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 35311803 1250 35310553 35310557
    0x19030e030f0c0f100207031d0616030f0e0a0501020d0c0c0e04080307030c02070f0311120f010b01021903080408030405030d020414030c1005030c0c010b041508100203040c0312 77
    0x50080401c1000c1280c0c0205000000340e4018a40c3c01880c804140310200800034610411420400c5e2603c00401010541003203900c160000c400001e0f40d59a800284e0f07421070201c80d14600c620780700740f80042aa0400005900205060030300070101403070a03566003810744406134001d00010800c44404c41d28459003180542301d0703031024800451080b1150002c607120390b000302449a41e9040c880f00080c01c4401040e4420115004500c0501092140c040080d040f0b079000740da00d1031400c1c40b00e00001e416801ca100768044074881c42c1c0ba010300c1c048042d08400201ca80036000e80c1c040400b03241d032284101d40790842c0180058240e000040000d041d18016540183c041c0040743d080411404400c0201d901a41100400108c40502c1050303034036082081c0c400a00381501d0a12011000010140c4227000141018011680c0440c00c014400000d41c08600c604c80c0c000d1003846510084044102c204085000700c041c0d500403090a040c84101d14022280240da021a182c00b00c0c0e850340d00c0e01d0007081654450002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 35313053 1250 35311803 35311807
    0x50d180602160b0114100e03010e01050907050112020408030301060c170408060103020f04020711040e0a06060b12010806070203090d020f090414010b0109080c10030b0a080105150619030e03 83
    0x1000c1485031029108070500741800c0c40740145a8100450210f10507448143d00c6010301074240420340729214a0300c040301642c10002680350703e4000103070140055119034200f03507103840100041064001001811218281c07036245c80d000f00c545a22047e44110302600c43d282d8030400040011910840c1d00e54000c070f010f0340401d038496901c0344420705558025171000c415a0310a00040c01949024845a035501c10125403c601e4191595a00300200c00220012031007199201c001e180441400d111a44002c0c0c0e00240401c201a10b0b0520003d464001400034412491a40700110302d2501c0010b00c5070050301907030015402e102e005000c000140710420b000302d820002001262096440c0d5a030802c2c0924815200201c00c911006007450071918411406030400c02e03101810030421601150003520010306032241208000d607050154041c1a00c6c8004507080344821000060164040d0310144c05400599164a40c1f010700d03a04000a034080da440f60300c0e219030b500d40c05880c418002d5002826800340d10059134 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 35314303 1250 35313053 35313101
    0x14010203070c03080d0501090b09070c020f04021b0c01020c030628020a0e01030c030506180901140c03070809070302090f0a0608060a09030806090103170a020708010c0507050606090403050d 83
    0x301d0304010390340c07040310074070404101c4020014060080b54050510030b81e040027003081f460005060050090200c2040c012640140d005541340c1c140c11402c071110160040d551000959080c2c2903141001001001074000c07000518440c0d8804105c03d5100203004008106035206e01c4e07071a410046401940e160110951840c1801403041400030304600c83e0a0380340c3c000d000c4265000134003074800421f229000c0604c0c0c070007044001e5540101c0b80356031003040200030810395683d01040c2e0050403010038813100e0710062020000810310710001907224246580c0c4240d00c40c0c440b01071b040c0e1b90701014000254411740d102c0004280d958283c030a0341c0e2008100d00081007203603035104905c3c2000342c250341c580c401607215003802c400d064100140581110041c3c46001842d855500e441068510240c0e15a031120780c0014484c499071310810075000a020450020440032107061400fa146620455044843d4016100014481c0c0380c4050802c5c400c40c1c150300d4540c40c12405400e0788005200c0e5180c41100e50100b40c080c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 35315553 1250 35314303 35314313
    0x5031503070603051e010e0a0902010c06060b0304020111010203010f030b04050c1008071701080a0206072603040605150d060506030f030409050709080d021f0b0418020405060d0308011401020307 85
    0x31800030400e03038a0003c0c0c1400c09030070300f00d10138445250305c100d640800001001481c010030081903110002c1000001d0034a56880121050a00301c2d502510b56414410702040c1582c00000950250b417003601c40012a036070710032006003030b4007091150b441134070303140034007000400c0b00f100050b58071611034825200d45288000003c0d01c807660400b004d90014a000081000854000d1141c0380102c0164a8071322042d032520000554568428400074091100480c4010030440e02c04180c9034000c44c0c046186030200038910010301c81c2c0e0401c03038060321240d003800049503075444140408804820090901d4455013a10b449a002501d0b000d001182c16100c1d100c02010341c03407410300252020f41045000881c06080c0000b0083c05001a904001d07002d41080100481c20307500001d074041042003014849544000604114000388500c503111354101c9e04040340803080c0345402d03640345001d90bc2107900304101e0f25100c06101207043c2154004022400c48801884440030720040700c0c504240502c1200c1c94580c45540d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 35316803 1250 35315553 35315563
    0x20d0c1101030b060a020d2618030408060a0b01030b0603092e0f09020301140105030a0312020f071104110a0c0f14031c05010b070c030308090f0715031113050105031503 74
    0xe40c200503001480c02c2c2c050684d03c81c040000310000b4404816004c00d5232a03010040762409000c83c01e0041c00d078954244259001e0003076800402ca00300545102e4a0320040c06000b61851801040c00a4a4400c40c50458900b90381901e02511000c0010a0110142c002010042c0b001ca24030220080d100303c403060551006001746403c00d500801d01048100041c414942075072000701446800100d01d000500144d18000390140d900ca8052030420b07014a03107116403000a2049000c880f00c5808001942428007d81d00c00003144284103990070003101c1554842c3d81850f01840c11494000740601480d078010070900291b80317040c20302a01034018003549918200d40307168099248070400134100680c2030420134542c0f0401740102404810103251440c035580701c000e0003600e4040182848280000708590103801c029500c0d603c0c002c80111680036480c1c40b0054140704180501800103400c00440c581004905d030b094a86c074503a1291410800c41c1448010b60703d13500f004002042c00c5210700c1180e020343d03404000e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 35318053 1250 35316803 35316817
    0xe0307090e01141b0319090204050106081e0709050d050c1c020a090c1707180602010e070803041409040f0c0e04020906040e0a032a050102040603050106020d0c1101030b06 75
    0x7000090540c18050001d0b044800104440284070714200204a4038003900300b180e81c0b1840807040d03844c0740c900981d02d1200804800720702941061902c4008602181c200704503074080d2201100c10b1002c1c00250011101105048400800191110104100c64209070071512202031003502038a030100480c0d804645901800464034101c418501201740650400c0c8030840080d00c81a10244514408114003070010003460b80b100740081e84440000b83c0c01c1d441070f003600c24106c854440c404191a42d8400080c0602042210104180220300d000a840c100020895003200e04510300724040c00d00c0c5100700719900d04002e0040e81d00c0120308421500150341f031703130860000e4204a400f00150307003400c2c014085031200003001c281c051881c15100d00ca5501c0005803024a8560516100100c42d840ea01c00f16000130032541c5c0074440e605030f081c0402c20040190058410313a8a40e54042003540e83e42e18049a0350a07854922801280c603050982010a01031000c07100b0122040c10041a00b00710b000c041079480e40859 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 35319303 1250 35318053 35318081
    0x9030d0e0a020a0501050a0f0c020f040504030305070e0d020f04020307050c0703080706050f0c37030b03010b01020a1203050c0405130209090105010302090a2c01030311060105090708070e030709 85
    0x140c076000c110b280050051000c0c040070719100782440c1d007140c40900211407c180c2d000030310003202d510004560381d900d25031010301d0001e03009001c242868640940502419141c10001c69070140040ba1113091055190000680040c2a04440c040c000c0c00c0c080203500140000d01040401c0207808540107003000b86c6d00040d8403a5403880c0d9a04010f0829008440d8003500148080c0340040900c1201441e04082ea07104102480550060054100001c0044144040240c00008403c421202600d030194003c04400da8164000e000c0c040c20940126190a440c9000074a01d04003140d41c011118800c3d4030040c1c1c0710300222802c5141580300d81c001900d004200d0080401c29030005201160ba0500b100c0d0760340100000c0c2020b5040a41d101e00140c0c0807200e80c007030110450059090310382041c1403c40c1c2c2d01c40c1132242000c05206541c4904004180d10700c04080b41409104043c00041c0301e040c401760585c81070740e40d0780e6100110346560600302d41094030360300503079418850304001003455891841210203203072081d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 35320553 1250 35319303 35319313
    0x150f08070e01062c010e040c03060e06030c01081303020109080d050106020c030105010305070b090105040905040c1d07090905060f0306010e091b030303040b0709080a0b180303090a0b09030d0e 84
    0x69010101c0c0d4058211904020080c64848001260400070a42081d082c0c4e030b05424840340e800048424012080310994001d081c0b6440a410a425078003000948143c0080c0700c45a80e04e40d000d040e903807148543c81c140005d200e24005031440000418046c54103100303200220380c40310143c841100c00c3e0019080080c0b01130369000100617468042040d0110308200380c00a200f00e6145454064031160b640c400d400d0907110002d51030300c00780c0c429811200078014144d0108014105402c0c84403800c1d5450003811100e50118451500e09100c800c002d61040c0d0f929912883c2c0c250902c0c1c000000b9000140400f900400c1c240000d01a51351305120890280c0054050281c0301d02d00040310624105012054001c640c1001000c1100e948022040701da103e90890080c400c40d88683c441169898002d50002c0218000c03041c0005c2009802d1404c503004121900f900700041c005a170340d180d140e20007528445c4203948055018400170f2010404a0360150304142030380c0c1041c0e0b00b20415002d0b109100704540c01c1d5040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 35321803 1250 35320553 35320559
    0x3050102091c151a09040f02030106060c080f1c0e01050702010c090506030414070f0608070e010306050f04091e14150103030906030504060207020a0e070305010522150f0807 76
    0x8511048420b141d20180681c00a06546407003030703040c0100c1c908407040c0b0703200c0408440760780c0c56145481506001800664076450030782002002001d8505040388207500b404c000203040ca100f407000078280c0c0c1d00b280c10382c0d16000b14580300c1c0c141e650080610b407601015244402e0b285008070f1184004000d06500003150615049400a08645604a682007030000101007400541c0303421040d42d501ca907109035424501c441405103e880c141e080c3d80b081d50440003500d408a504c651100342d03c0d0162045440b1000081170200064082d28024024145c000c0119000000149425003001100c01d009203a0110411185011002e41950084040e07845900f0301ca120284901c0c03c002c00d010794040150315031b003503505542e40240840d229115203020180c0740d2000c10113000160303040301d2995034000e03c60030920750389243c0c1403038000040703a045001c40c4c07914000080d40d050400c103444002154010030412001141d40741e0004199100c0d0041c5800a143c4011a00303015003d101c1c0f000c0d101c8100241621383c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 35323053 1250 35321803 35321809
    0xb0a021203180d09061706120a1b0506030105010c060207060f020c0f0f16170304090f06051002071503090f0506070201020309060a02070302061503031306050904110915030606070c0305010209 84
    0x559048690800140380810030503542e0017140940c02c003074681806c076010b480e18400210405503c1d250142c0a005032002c41c020020b201144c03540d0421600c80b01c8032507903034803020051180024451203010451a09004002480b550f004244403442090b00080031420500303840c04980080c00b01a003264010810842c0140f802c000d1000c808a1340380003014030005100c090320740c42006204d945286401d002d070f213040000c8144240e4000d0300c0008410031548036000c01c01806400680305290042180d81d8440340401d10121b40300e001c4d1009006051520107683c14101c0051581c45015503605a06814000002d4002d0012034041d01c0325500240c0c5900f080000300c1d04024010b0441100544100400c40020b9000308036558440018142946e45c00c280c4000b2a0843c865101c8000c5a011003410100349150498042c0101050a0b034082005044200d501310582c403a1030b080c640d204450203e03103501112150001c56000901400382420b040482d40c412020000b2500220b4440c3d40104940210b42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 35324303 1250 35323053 35323063
    0x7051608071707050d080a05070f0803040b01060f08041101020705150309070f03050d08150306040c030510020c0606120a02090403170c03060d0303050402060c071e0b0c070b0a02120318 81
    0x2c1001c0054a80c00c1c0c41d000018605c101c0813440205090404140551418020320980d1881c64112a000d64803001d64540380c41c1c9030f4401c030340890b80c0282000002c2080d074803400c40c1c80054107103030b00c1e84200e580350385c2c99080055480d0b1403118110320811a0114141e11881716078112036128984a41c0c4908000c400181006040e0300440300410548000b00089180004e540701100d525003406051602d44802d0742690240c0c0040864042c17003a0014002003003190000041101d0007942aa08540c480d2480c0d00c05900c2003a40320070090344804007045e81845d18028060b0f84103120411104000c04541c003155840784121004d50101d40d052443e181501181a003442d440070032001c40724079500d00400050b00e510350102010b020565035500040464469504403520f5860060845e80090781e9400003044807000300806407404d881161000810091780c1b41a0780211241401400c1c0480c1084036130743e026000030b40711600314030408098a0320480204000e50241c1c1c0e0302c803040e039030310108071100b035280c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 35325553 1250 35324303 35324339
    0x240706050a110f0c16030f0302060106080c040608090a020a030b090c01031b03050a0605090109060602011427012703030b0a06081b1c020a021603020a09020705160807 73
    0x1450420074601480401c0b04125510703004404105034542c10b403140b46a240c0031000240c544006800640031040c0105e081c2c04080081c425821500582c2e03d4500071104c8075029540c03040c0059040c0b0051000901400109522585c1003003101c46c0320f4555000a43c0400c0329510030307900c035100d100500005000038084c80301090020700b42480170742c5480d40130140c28403690225800309681c1c2c03070205100d02d8a94006600401c402090000340756114030201c80100351602c03540c0d0144d032800c01e100e404c440707180c007240d841402514403c0d1702500e1080c005001ca0b1040048544c00c6d07550f140c000600b1072100041c030000d000e850440000c0c1d60201e6180241c11103081c2027049204081d414010407085074800c0c121503110201e001c04200400c03095800d844c403401070440c244104403501540f0b000c00d011503409010014101d5003110340c000f03100b8069808042150001a40103240728905008169454004050580c8503004460304682c8801a0070042c218a4114040a8101b12404c010522128100f8040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 35326803 1250 35325553 35325571
    0x31b0806150c1e0a1a0907050a0315090302030c01050406050609090307050d03020c0c03010e01090b101a07031b14012004090b0a030b01060309050d030603030203120624070605 77
    0x40c2c20711141c90b081c0ea400304014400f91002800807105440300c024070603034803116400b241d030b44c1e0700c140407100409029004890031002881140c01c0041e2504d0041030300400c40e50803c210402c212850010343c00603000340101078007548020000d0168040091140f10b110794007905000034a1304001041204011b4050700281c5144c1c414014100400c1011501c030300c0d171120a00f80180c0d1846040c18050801421000e00c0340e15501c0c064010480300c0c07044d04103100321440780107042c02503070f5000d10000b00300e5860f0184a040290305407613082030786000d0b00101606d40c042c0c100600140c41520340b02c8111020740c0002c41c2c01c0780308890382902100e002d001d200180001e51428147e40c20818103065044d0007184075103416661260990381e566142d50100c400519000400c6015541e11104c01402425103000c0444442c4102200740031a28864030801e82a80e074964050341c500f040300810981c40e144094080c0ba4044e00c00301c0031007400c148805510508a100003046515241e85041c00c5003180d00c01010000307 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 35328053 1250 35326803 35326807
    0x1030506090d1e0c0c050a08060117010c020d0311040306020301140f0102010513020d080403050114090708070605090111010e0303090a02121605091b0304030905130b0603011203031b080615 83
    0x2a040555003030f01040241d85241c9441044403134140114800103030ba00990f0042c41c154008a00b190002c56014140c8601303070304049906032048182802c0b40c1c5001c0310707900141c11113040ca6042c2c6220350410b0724901e80d00c020141c01c103922503d41c1170499000b07a00060b42a00c104a0440143c24880ca030005142801d0000300024540010091503210f02228000c0c0f003400314800702010020000c1c2510059600140200200684034800f078208a80944401035144a103ea00050400d0002007100035510a030303907001e007424945801525281c151800c00100c554803850369151146003040590b1207030462a00809209403a401807111300b6078180003011703ea4100e0700300078001001500b0050101d8030155031107400d40d92140c00c00d00c040c502134032031410a00c0300007048c0020700d6402811041a05e10444101c41d149808c1e0042100300c51040c1100c3d60040b500340700400c0511000104141c03824024200450b0005075850a880144001801c5e1004141540244440343c2401c003001a00c21010700f500f28 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 35329303 1250 35328053 35328077
    0x151214040b1b070b040506010501090801111e0d0c020304050f0405090304030b040201120501060e0a061b0201050f09090c0309070e090c060a090b03190507030b151303020901030506090d 81
    0x120800d10000c00102502003102844516020b04108880b10680c01101003a00d41c1010b1900c00c1d2103520070302c02d50380001c81241001ca440c0b201803040810398508484030341d242611501c00403d00d0841002c01641c080ea082c130a400c4c034207400e40966603004250b503010315590b82c200400c000c049510354036007600440c50b1a042203d4484000105c038143ca801105801032981c49100403208001c0c200600da0301603003000000a41035800c00c1500e2903042c0210b81102055440d400219040c008000c414869a00e42c00700000c00b5500810043c4102ea050034650b078908207003e40410401003040c2c5251480e01000070402031400014000d2801510615407401c0b242e0602c4102640d0301d01d02d849140c1d00c114000507482d01c0d494002c12001c0c0c000d01c5100d40341303626498044464502c0c02000c40041b9401801d100016402c18032912805005840041c1015950300964401075160b8110700d8011034010f0b04030502101503550803c8850007503110388001c0c0742501d0b010b40c07803034101240c2c109034105020101b45c0d41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 35330553 1250 35329303 35329313
    0x1050c011a0102010509011401030605220303060317120403080402030f07060e18010b0a050903010b0a06050309010501080d0c081c050c040303030f090305030a0203040f02130608070b0c03040e1015121404 89
    0x1260440707803c10800304094489a100c2c47c070000008085002e8113480d007010380200353f00341c0c0251088031700440038800e420085003003100191041480382000b0a510b540001c3c0024081c2c10341c036411500203802c9629040040324907610704104d6400c0b98000c00c904541c4000b80d440c00e4810303d4106c5542c80c002c009154580b00c0042c3c0e241c02520281e0061200c040750450b01da4900750310810380d00000034403690700c1c955038401c0030300641d00598aa859035420900046484d1000060f00320700d080140d82c031071000f0200c586506001d07404c03071170301c1d003102481c0c9810b14070240000b8046c1c1806181840300b1a50703200c0ca1031402404445084000011250428001802283d0404181c950009031140d0244e600d0742c45251000c0336400210000791322105411800082c1c0b440742d0b102d40240c82030001120780705a21001c905409000d040400c50140e4010841440240b865468140d04107405884003200ca030f131544c02c03540081d440d00e0242c400017580700165410b0800d40340035a1044000c80401940e05080540720 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 35331803 1250 35330553 35330591
    0x20c0109050c04060311150d1407030e070803030a0e03160302160f08031602010e090a150504060b070303090302070b0d0c080c0c070302040b01021905030405121207020f01050c011a010201050901 85
    0x1071b141c4a8140b00e15000c7d4160910421545a000c1c59001080342480880240c401000140c42440010786400514044500d0000ea60300507148075000841c1940d45821040c40941080d45002c08240424009403028002005856980c188a80c001c1d100c55079480d020740390721000310f41c015100c98003480700803c001c4070040110b800156801c89501d00c6160107000580d0048810b02000350001e100a0402c1800c000a038090840d40c0300b038010f811b580e541c0d00c008210650f5030500030801f50070340400108000074065400317451038520900580b0030782c959900400740d840e00910703041d1501d0f43d103c015800000c0d90192904d83e0203038510020340d0401e80c410a00659412311404024022a0346024410782d5130300030000a60000707840c0b0204800e0609500c0c006480f9081889494010300030448101d014900214651034003600702d810041c02c01d0717043c2e0200a4070002c81c109090611108001e0b943c0080c0c400c1c02640d20044020282102030344071400020b084890042200340d159240c412404042c2000c114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 35333053 1250 35331803 35331833
    0xb01030209060a030506071e09060203041205150703020d0b010906022104080304060c0c050102060f0c0f1b01051509090a1403090a1706070302030c04030201050715020c0109050c040603 81
    0x540c4030381540c0d4001c00f00c0c1c8190015040a805403107614200458254441d0b00340d42ca0f01c015049003540d40c2070488068a41c0d00302401408096081440305014403841c0d00700ca4034126014004440902c0c1061700a81791104041d111035000913000105980340600c90b0040e01404802840d289001d5441c21000139100c900c104160302c51115050240401045c241040e5400b0303040702e00030381c0d944036501c0d040a0b10510310782c8021a0240c0c1c0a80b4001010340c004500c051150500c0e0359404903695a4195a542c0c1e0351141c83c0c1c0c8199101c05208084400580801e0341601540350000082d081c00c00c84401310910704280440380c4918901010040603213004601c61070641d6020444c40d903908001e0b002c0034118001d100d40250080c00405001401e1900c20ba800e821080a82060311031035200c519040f0180e1000300c8032a008030381d0401c410030040d44150028130b10039000d88400c601c280c0200c0c62500076a8051040d0a4060303454a8260051040c1401024001d400440c2d04024091135076583c0c00418440d01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 35334303 1250 35333053 35333059
    0x20604030308250f0809010e071e08060a0f0b03012a0e06030c1c020301060e090901140901020307140903060105040b0d1514090d0e0f06090301020f04060e0109030b010302 75
    0x1c60340c01030256100e0040552202d905040443c402c40008000c0303001c484004c0b00140c8550049500510184165a010819000075059040c20440071802d03c0b0254985190140702c5900d0009821000b4400c0074028000c1c61000700c0c4940d9203442903c1510000201c65203e40d260036061741003401003480520380607450303180015840064210660f02902c01e40b8400d03411038000410405500d005400909641e071a4a0400c8502d283c142c15110480c0401d0103580c000c9004540481c48034509003103029030081901c400454411400600480415000da039400d4250b90048103016034950084041c40e0b4101c10768141c10f04110400380040d03541c08044c864540a41e0b49c50302c40c50171a0f16249801240240c01c0240c004148010504140040c000340000c00c0b250300c2e40324045100003001147d0703102c01103003a658150004000204000c220000c00301c201d9032052040180754281e8600313001038910619007180c0303a6126490200013604401040c90f05904200e02e0b002d0900000d00c441401c039042d00c0e016 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 35335553 1250 35334303 35334317
    0x120303090c090a1d030a021c0c06090809060d0f0b01180e15030303040c090c08040b15030106091812030b060f0703020c1f02070501020615040e010204051009030303050c04030206040303 81
    0x43c41e241001003924150082043d90340e41250071158000000400c0070031050f50880c0c2410390042d00c46000c003000c1d00b20300030002e981d0303120340c20100b08550000e6441600401c5041d16180840c0f001400395402580110402030f11003409440c14860781c414000e00c120300b820101400041c02288400700202d5024603140342c1c1c41070b8045191030401001241d031081016085076500e08290511030340c0101311344190b500582c20700130880d07840c9105592290060fa8849542c0d1015111500151340d207650f042c0b202d68240d9616040020100070710f0088050130960781e0031044e40c031004d03420710b444071101503900e000c14181840c07854000f58451004507182c003400700f0301294a442c0c4070302c3c080741410221080300d584024880d401c11a0740d409520380c07002d080883d40031a059540c0d200c005984a81d42112107101c1407030300c0c0a0078281c1e4200741e00030b80c840c1c20400d00010700e0140c441d4009010b2101440c046000180b030f41400348201500b51040d075070490040307100e650816280d64001000b901c11404014200564 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 35336803 1250 35335553 35335561
    0x108060114010311070503040e041101050703080403050703181206110412021c06050a0b040c030c0e040e03040f0806060307080708030a050a050c0109030e03010b040204050a0e0705040905010f05120303090c09 91
    0x50b804c19104540d80c4101a00da655940d84145066058141e8099490040841e003402d03044d030041c0e040362540340e41030315542d050ba51240c40c140c3d2140c000034000e8041c41210810400c06004402c0040060070701e4072110400d01c031180c02e0041c1201c25050040c0311082c01000280321640495802c2c50300c2c5981195003c0e81c00030f041c11132404d13011900d0030050003981080180306144249400070000752406803002c000b07a01d803d450031810744151031184008150340303804110060030190031440d1002c04c404110780c030f001e03504d140c44680503000d0b80c400c10460f0800000d0241900d0140a800010240c82d40140042c0742003c4149480e8032941d0200d20910500286066040d8000c00c261091b80c040031008000410082c07d010707208404001d1070f0741c400c0d441c0c23480c40009032400c6d1003503800fa110041d140707441d4075080c03440084071500d0203840300d000e200080c00001158003803801001e020b0301c407007010b07500200d19200502506407025000e180075a00140704215540c8000684201600c000300c07070300502501c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 35338053 1250 35336803 35336831
    0x80a02101106090a030e0102160e0c04050915031c1d040605060705061603090812090a020a030303090201140319090606170102071707020a090506130608100501080601140103 76
    0x91440d6203440785000e4941040010a00810700740c0d903040c02a11001070248400004a8075402000014505114114014490711200408095100c595040030300c2c6402e407240001800000c04945001c260400d03d084044d4508080c403c00340d0b0304500f0380740c0c8002c2d00401c00001d4864581583e03030004888850b18400e03000c3e520fa4010704010301000d40700350350b611450b08100d0344801d1700f02c0c0c0d0440b480d464031071000c2141d80b00380300341031800e0742282500d410700800420f030f00c0d200300000d044c0040707600c2880188409651140200d40c0250302c240c0740020b2080c400e20014000c0320149130000304422040c001c02040c024422807440400701d42500004002e500c40c0341400081050384c0144006500044030760303040600550081407658081c02c12540d03800120b00c070900c01c41c8907920000303401c102212400c0003110b095411058000900805c1e000110884600e0074040382c1240d4001c840c203074040c0c0301002d0021401d2007080d0241c604e60028000d2581020180c0c82c0246580c44114101659000c1c0300d00106 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 35339303 1250 35338053 35338067
    0x308040501180302010507020706090501020316020301060e0f0a060e0f06042003071116030812070c171209010b09060f0102070b0f090111070e13050307020307230a080a0210 76
    0x9034004000e0140b00d403032400e0090080c6000c44000016201e00c400c0465118001d07445682190016070045190051740a00c2580c40002c1a004a0f095903c400000c1000c41d40080c0e5507100d400541c400e00d1007441c2c50b00700b40c010f8402e15405611015035990a014410b460701b61003640c400c000340d8001c181810009600e8030804910130a4000b268404024042a40e41c04880000c0ca200040c0484d503000024004500500c60548001080d1820401244031044058119141e015065041242d0922203a445d9440d11100700c0c00d02124102e800651030000d0743d800341400340c1000d0400003c100032100b0740c011401c00100074203440c3c4580701c041c10180703441c0e1080010304040d0820414040d21449054040c0c0c107107400c540c00180c0840c0d610508610008000960001120514900619035480b440a080c5039001c10340000c3d12240030400029015850400c0401300600b104258110104d9283c10040600c2e04001d514510800800004022481000402d60400b03901150001025420501c040c1c86503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 35340553 1250 35339303 35339321
    0x20d050307150507090b03010b040608070908030a020a0c06111203061c0605040b090d0f05031302060a080604060504060803040513021605150a1b0c02060c100204031b0b070308040501 80
    0x20503501e42d6408165801500094040c0101d9125020303102d4031240c540005000900404a020009000c10491544140902e580111803418200d076825141c6040c0ca003140d010400f1000543c0c081c0c0c900300d04000040f031048000380440c1c030b801d28004041e68600c0c3c0d2203840724420880945130220100340c0c10380c0e8050f82c020b04c2d002d0041c81302c40ca02d4410719001c00a000c0c112002d0f92005015030006418a202098100700d00b0026510861800c114906c1940c1c80d810182c104003204425918841c0141c58044c000c200030a0b2a89a05840d0704d426420801030300d0b040e404c00d5001f1030500004010414001050750281c40c0c084451006644885100000900581c000d044600781000800424040081100e814074115111740040340d940d5403c40c0d100b60349045210003010085890302c0c88000740f091404818052009203a5460620849083c030700e2b0801c03440210b011654005402c0041084214900c2010610358000d144402e1811016150902501d80d0140601089000142c10800d0a44c042d0f00c4c1c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 35341803 1250 35340553 35340563
    0x1403031f090524041d010f0c0302030402030607031107020904081e13090209131e0c050310060503061f020c01120903020a1401060b071202060a050105060a120f0501060201021e090a03020d050307 85
    0x81d82141c904468041c0145001f4140070601e0407000c0e050036407190003168451138016004044030380729184c0840082403101c006403041c840501c91003006070b40705114140554007580030951a0039607a11201d000ca60740b0050303c10340c54005c00c056001c0004840642c011181041d500588404d55500861410310110b040340d448985040d00b5148002800e09407049209003c4000b0041115040c9003035600d403000342e98441c030280042104000c4148640c000b5079000b40040d10700244141c0c5091400f0364003040040d1840035810110181010b543e10002c8050b00d18900b504c1405210b0741514084e4a40e240000c019003040c0b04005551000740e000d40140e001041d030492915030702c003030034188502445016550800180150b90103d04103481ca40142416540c00a1109240948000082e10020b00f10244030980da600e80c40780d540703107201c1e61140c14005c2c0b04c26000940d0f01d10400c40b0180f00c20341200d503c1840c421044c0707c4042e4507140c119160342a2641914030210f60010340c2080da15600640390001c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 35343053 1250 35341803 35341841
    0x303070602120112020a0302090402030a050a03020c03120f090d03090f0305060703060e0708011509030606030b01091103010810150b0310090501081203131403031f09052404 76
    0x41110035030080680c0e007040001c0b04040e1341c840e28100101c013000c10b0060342c00b041d5504280702520342088002e4101d03100404840d40c0c52201d07600c2e50300b030110904082e0003507046040d00031300600341400154803010b41d101079249014a443d1151045004e07445601d03005880301c1c0b00c4002014042e05500d0301612400070210f000c0c41d583d01d0325548d21482201c003200040e0510400103101404505000c3c040e586c103403650f20036a030800141d04c07103884221090004004032804000007040c02403003544061805840c60440942c104140c89064503400e080410700c040b02000100800100828400c01d100c40b10794000c16125102c449407024003241d50028000c088001013400200303840811207100300c501c10b41003446240e80c1c411036035032109000310f103c80c4003080400010310418020100044014401c076640504011100303805451038200301d81140000503403005900f182124400d0700700c0100102c010030f100c58a403081076042d85c1540100d020850345e5495031090040c0e81c951700246207113403030704030845 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 35344303 1250 35343053 35343067
    0x5040803030f060406051806010806010e040603030815090106200715050c011b120e0f01050708091504020d06050a060e1003030e0312030f0907080a12020d0f0207060e0406050303 78
    0x1a00b901603074500c0c4a503161400018042c14040389190003c6805180145036030380f48401500c402d40002c04590400a910071000019611441034002035030003a600d200d01c80ca080c642c117851031145101035501c21288800100324859101c0c06611421000b01043c1d0140c40401c040c1d07900e0b01040d500001140448413401a1800760701c0030203800302407022030084c0f101441041021891390800a84d20780000c1194200f020035402075002510070001c100204d17401820140e0240b42110011f13900000066102800d021001008012214040711406403105940c246640000e25040c0c3c0806d0003080c403920b580c00a003c90340c0c41c1d8080070040a030a0409074451502d0300e2490680b10003800200d02080b100000000c0909000074801c40343c0703606181c0c45155440f286a01c04451800401200c0c0b03520070004041000201070046086040c8101803c0c1010b921141c4080c4c2440b0044104000700301c14a130420031407540c0000d990048450b00d081c40507980b8a16804a03024180f19001607805210000d1130b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 35345553 1250 35344303 35344321
    0x301020301030614061207050607080403020a0801020a090e070512060619020601050a0b040f031e0606030305070b0106020607021b01021612030314040f020103020d140411010e03031c09030504080303 87
    0x3440b000c5400c111880b12035980d64040141b0003c4020881d41d999100c00c5c02480103050110040200600a001e4181016900d500062090105030400900c0da500860203c01842d04560381a0182001e030801e0041840c207808020102c2c05681ca807801e40e0710b00a000b090f02c41d2154803c0b55100c0208188280c0d00004402029680d010203105450003500400300c009450080c050903601901c8000040044051845d1605221141c101206400340e5501e400044000b8500d8418200114401e0300da56807500c2c1e0309e007000548824142d001c5000d6410070750401c410785502251030884442c54102e070480d80060712004030720345000c51543c024a5507043e0030104001c00c2181d0300c031071142d100713a03824460320200344c2c261051040241c400070541d004202e14800190301a07000351180b1a05c101c0d002070005100404003840f00410745003075600b00394010f803004465034071102c04514690b00340c00540c908914045540c4030343c1400c1707000401440e50b407035149040611810466000300600011203480c2d041072112 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 35346803 1250 35345553 35345561
    0xd0f0308090c04061d0a0e030d0e0d0504120215130314060901060303090b0315130207050c0a0b0f09060d0212010801060e0402150a27050315090618010b03010203010306 74
    0x300e4109446001c441c00b4051900d8003801e01902d01c0b104101d100c2c40c48004890394459005000310440e10b44074100004101303020000f07427090480c0742401180c032843d580c0c4d6107418002e9a0580a0401808100a004468003040504030315075056039400d51001c4020120350b014040c0328002c00300c0303411302c2c0d0f0000140106c140c1a01060b4848200791641d0380c9924009500300c582e54880280401c094860401082c192400030350740c416000c51011180c3c1e06403000242c0c00500010501c4111540454039030140b1004000144001d141a514440141c2c18215000c099010f024980f40da4454000313903001994a407007040c0d50f00382c000c1017130640d01d4140400c3ca400ac0300c042409075841541c84c0241c0001c8101c10660614022500030300004d074090700c0d00d0a10351181d44038603080e4061140c040003000c0b4040000840600ca0200400d50b00b2156080c0420942800b1000038030320f0b110b13400075090000c243d02c040307455038000b15081c03100c00403241d045101c2400350082d40c01d03240d4036500c00700001080c044039401c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 35348053 1250 35346803 35346811
    0x9030309080601080a0b040614010303090e0708010f14010c0c0e0108060a11070303020307030902101d0909030405040e150a0b01030b03010203090a1b03151a120a030503060d0f0308 79
    0x9a40d0492a1190760080d40c500c024032420340743da4040760706240491032001c6480e4000b03000e050007090080d441500000a4082a403089001a5042d001007054121a5400c290456024034044029500d00f0845400030045070054056150f406442150a41e01544804c04030680c411b1a500810340c1e9569031000300b01c02481404800d004500009411556a2040845401c1d1200807282014002d403011002900000d10b2f00c2d00307040e0b40e40311300005641c03400781041c12502c0f250364000c1c80200c0e8040c10341444d594141014001c403540300501c50128004410b903020740d44252000030b00240e4104515140400c03c04054509503040c4044c041901010382112041c07140070307242404548014002c1c14207e10007100d88402641040862100042c00320041c000c040002c5a511022252240c50b002280c03030900d82072480300c43d40d42c4006051010308010003210503404179030155a80ca05c00e98502d44a50340180e008042220000c00207885994821590312050742024010643c48035078a005000000151 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 35349303 1250 35348053 35348057
    0x5010501170708060f0a0b04020904090609030e01090503030f0706110406020a050c010c020d0b04030e180402240415090b0a0201020c070f0b0a030b04020705060906150102010c0f0806040b040606090303 88
    0x108085a030950004d5401e001d00c8105ea01244550343d0780c8003c40042c013404642580c016020000c102141ea40c2d4046c0320800c034081c100000d181e0b58285805803805500300341490504c112078400704029900401512001c0f901800291355661840c079041000b07009150510028040c0490003140e481e40c0007580c40e10040c0b05204071000d1400d01001901c000d8107400c0f00a5005903400da403240042d104c4201c0c0354101e0b12908208070880349440009411921001603582112055810481545080b590781c0e60711074042070300d101c0c00c904290008200d5100f00c1c060340103405602e00b098411240f280740c17000c00409003482216210365980d80028040d50050003100c2c01c03071113944008521914030300940400c550101018500e0f000080e803054024180449070399601603403c3c416540460010b210203480b4050b050082c282619101d020701e8107020066918604580c503081c4c8840d4401d8203c24070301503611705420f2420603030340c4006c0020003030151800b000d070f00f05007012130014545030441c0008007034074807903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 35350553 1250 35349303 35349313
    0x20d0c05150c06092b0c0501050c2706030408070c03050a0303090605100f06180506030406020408070e090a031d0a06050d0f2304080d110901110a020a170a0501050117 73
    0xb10070b00075603900d0f00200c040b1500180002c900d50072400c0a103072032030041721070409160036925078507800d00b118000c5030380c00c6131410001003103411030307418005d107140500303040b0300034001070f007880380801c0050000900c024506407000030841e041c00010f0f5210380c02140d100c0d0480f104032403a481c00030050b00101b002111000e00b400040342003401041c007540161003841d00c1403403100c0d203040701c126000c6198a64068038060b5415001c03c480d1601c000442c440c0b4052900035a54030301d044821032400005621140e8048060014000e140b0030114070071500030340600c0c141c01024a16250180010240e190b02544920002d400042c0c0c160048050100718055110401108210007030310003d8412940340c918000c12064003401c94030160307601d0340c0e4209000742c92040c01c181d1885c3e910800c8071014040c030080c00c2070211b80340c0303419070780280b401140001d142c01425000381c0540c04200c0c203849500910011803120036480c4580e08040140004c510f40000c000d01180d6525010200c100ba02100c05072103500407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 35351803 1250 35350553 35350561
    0x2f19020c040e0d12020f0c07030606060806010503010f090c1e08010f06020a0b0a0c110708030304020406050402091809011b1e03110301120816050606010e03010e0703020d0c05150c06 80
    0x1054030400c03509030740c95440c9446000a013442c020760044110461480e0103100c1da40819004200c00c0000d5032155200040260400788050b14540e0010320242c104002040140682c2c0000405d05044070f805a10203e120448150141d400c682d001918032592601144191700c0c2552100900d8100ca07200100f07001025110030b01240c0355203100d980580b0f000006404114a0001644980c003403020360301d04400c0701c0b68400c05030740c00c100716540050a194008018882540380a210307000c001c2c20300315011407800d010320000c120440302c0b02c1c801d201c03c01c011500207003c0c2d0800b03410581c022910940f8201401d00664030160441108051612134075600018400304030f03000c0e105100c5050208110705040d45e04e0460014404c03114003c0480e1440000e00006016400100c9143c986a204030054003103403a10a000501c460310a1600510980c1010400544844042208800c1d00d8041e900d645403484542490320700b030500b40d8810707a080080c0343c0151804d4001140501461807601082da075481d11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 35353053 1250 35351803 35351831
    0x1170424060b0f03040501090b13030912020f09041a010803040608180703020d03050f0406080702010c020714040c03021c020a0f0804020306131b09020a02010b042f19020c04 76
    0x70040c0142c012036041004440f034145107000145500902c45d0300003280103405682e44143c519001d441c80c1045640072000f183c1015000381c42c40c009004c0d4040e100c42084459000282c10000c08002c3c0e40c01842a580460107202d001942ca0b4040e200700010100c0f15691848120369941c010306c1a80c0008405a0103d007161110070840d05000540700300501001d42503408110f00c610f440c1400b00c1c1031010030800c04200180701005040100a0b64684420901d04108060309494590070070904642100300300380161040401600d0039044240c07400995540d40c503009074002e2280b0b00955403c0c1c00019661800c81540381c00901402d8626619288890204c000a45d090307130701540c2c000c2d8550000c1001500040782e40f80d5000c012805101c0301075003030074050044251030a04bc1c001c802e005400060080b011902400380041c40d600a032000c11005130090400320a001d15414804115040d00b0a4401262801001e44049090b40c000b050510030040d07201a40c0c980d0402e61071070182c1d00b00fa4146941c44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 35354303 1250 35353053 35353061
    0xa0b1801020a0803010927050d08090c0112020a021014071b0b01030611070b07080108061006050f0307090305060f01090f0614121c08180115031101170424 68
    0x551280141d401d59013841d4060000e440b00c483d401c2c580121f40400301c03002c0500c0c20320941582e03014101030500042d10040003022000020000071040d848040601800c0e68041607000320782c0302c0700000680740d41464038121f05000080e2200b0816a003080e003800103885140b03035841d00642d003540340c0000d80e440322848000702032143c41000d840b411714500104046141900a00d1310b8440390031040d8039104950f607582d07182600940b400000a40341c5401448149010000560041403208160743c2c020300e800740081c01441082c10123001448044049020300b406011100081c550207030903141d0138507140d514949100403d03c1903018040c06c081582c0c040088610684050b218a0000032400c1d140d0007060103c0c50000241ca00d54030b10034507400c0c0c01078107604940a80980b546e503484c00c41e03d0a0040d14074500306207200001c8d00b16403604252038051504645000100c0b03502846600514940f0790040c0d40c588018043d04502144e00e000704030400090421440ca0803081d0124654004800442d2104172 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 35355553 1250 35354303 35354323
    0x607020c01050d0b010203040b0325110c010e0a05060307050c2104050d11120109111903030c06090605010b07050120090402090301060f030501051801090f0206180a0b180102 76
    0x2c035008115810801000e5000f0581144040c011070f403a1640e0707041002000d034012244144003110308078041c1e14285204d0780115000c90107143c020561844500f00350b841c0d0210041107814420030408012054440001d5440204802821103849251162018200e03030300248028000b07006008540e0b80f030902a01e00080b51054038840941000d00701424440c0109440e0b5041c1e50700c0d01c464211541598468019240131034110b00017050f600c1c0c0b1480c010307600214050405101e035543c88448840d820807125072808903501460700a144403554117014000700b65041c070117440c090403c0b00100b80032003500014110184100000c000381401d908403140c104041001e03418001400b007102e070800349130030380207011901030050000454039691021641d003100c5a9001322100d075100c0307040001c42042030703d8042d80341500500a108a0024ee60b440707080e9010340a000344500e20100e480014640c1c00300340c00c80310000141c0074461540d120a40100b20750004034002d0075100c10b03020004400e51011078840e40d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 35356803 1250 35355553 35355557
    0x315060f020304090c030902100207050a0504060e0601050a050c0d0207030b0606030f0c0306030304090612061506080c130e13052a0d020d080a030605090a05190b12030d0e0607020c01 80
    0x10141410350b03004c09804041100001c041c0c681e517240d03015030b4030103041c00d1550749250001c1602920f021300340041940140d1140b440303189020810820302010040b455882202441c1c21660340031200019074181c080c00c880c40180780729550104044c29000034800007583d00400040c68556108070800c0081d02c000c0310400c559009070004100202c00c20000780d50018401410340382000c1d25992000708079446030744400040e000349820782c014003000d4071400110091060741409000c0c200340000c3c0c20684041c00099100f140001c460b070080c1c0d8083c0c3d004001c1d080d03482c0c060b2070f42d04190741c0c03241c2c1c0c001c1400c6040d240ba00941d9400040507101d911103900a1504018440c2c0718241c0c8810030018200c0c041050b60800041780414000a01032001011b03c181503440c0029014100303414010064402441000c5003894442030141250400954921100c0803800220305030603d100414007810f824000680c09203c0840c010b1200f000b15005108810800c4084480d99995094100e0341d928000c10000c1c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 35358053 1250 35356803 35356807
    0x207061407050d0902011209050717010b220908040311041b0f0e04090602120403110c01091202030c030708010911040504020d02060304110d031e02060705040b1305100315060f0203 79
    0x81110307164000c040d2813030050402c2c0140d071268602001c2980c0030010109c800ba04800c2040c4001d510094044810101d220b008101295406000c0360030200d48040b01d20548101c0884079405000b6a082601200d40c00304115407165a0391410320510000c0c1c418581c4207500300b40243d042e480c02d08a9a04002e109030b610309020f0030080c0300540d125600220f8039904191030b4501500402d405000401140c40032001c104c040d4945400c1c0200744140080e800071175500030340002c1380d1a0703a2005031030003a03030304900b0381b180071108601c00203151a480e0010360343c15002e1480c000030860070640c0300380c2c50103005803c080054080101007000301c03101184c000b903202c0180c481450140c24010701440e8040d2080c4040d5203103030715200015214104542c1c0032400a0b40030b00300c10b440c9801ba06803e401070b0241c0d000524150612038800f40640c015030090000c404004a8032452142c4010b02d90801800050300140800e0030000e07008018201d003000b2010a000011400a2014030a0008a03010200e50f8050742c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 35359303 1250 35358053 35358067
    0x70b1008030f070327180b0418120203040b030f07020109020907030b040b0f06030703091e0c09060b16080906040909080309120711060702010311210105030c240715020706140705 78
    0x80211b11007400750003c3e01d540c1f8203000e940350301c0b01c1c86048031090241a0000425150340f40180d03050f03a80031030790703411504140001c00c00750802034180ca41100c544010840183c1e10410201d004228103003010b276201640d10140300c455a0554006814068203540600000d803601041c4031220310480300c82608042d00300001102584030390700c61480b1030f03c0761001e030462012132102d070b80306a07592903000e03900c42a804004100d410320300d11580000b801c0e00070503582414041070140b09104420000a40f400800094a11107a80c515044030054200c2080401481e1524181006140c02c11903284c0100d10410030320a2a551400040d83d004d40c0e4070001009038003c084040c0f01964211010483c181500c903003d03d202940c945004e8946104e0061403603500b5503a1292030b0140c41010ba020600a802490402e102602da00400142407000841182400d4000000c4200984120340000d001018503000f45c42c240441a00105000c81c010344041c0110644085c03a442c0324a026105540454020001a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 35360553 1250 35359303 35359319
    0x519110a050f03070917030306101106060d021906020106050a080c0303031b040f0b0c0709051303080c0c06090a0b010e0105010903140109020316060212070305070b1008030f070327 79
    0x8592002140c03130203980303140e46e4040c20405001c04405840b000c1d003000c020008181800100b030500c000781894a96203404607900801c0d00c61101034a0b441c0943c615100305070079901c035101907908140c44d00c410001e2840c1d40700c40080c024109405498465901c1e08000128001c000807030780c03240d804c0103024620310f884044500d031a104041c60410b074816814400081d100540d6000703140200104510540d03104140c000c411308016560700042502c0c0e20b000144220100314502c9c0c45c10080d403600701090b10b9100d003c002d40b00d9006402600d10244138003401c200d51000b0206801d00200d00c9001031300c603036076200c04a40300c010000b40159800294440f0041000c1500040880002143c06000203151051034010030306008500c000089001e4010408010041e030401050400848400c0110300b030160540c0e00510510404070094410080c040104000400c50288100100200da017281d40c0c0d4401d201940050342c000d0f1000382c02041001c45d5070900e25a00c4a82d5141d20502000820025030900743c032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 35361803 1250 35360553 35360557
    0x106030203211c090210270605030601030903020307020a0f03031103041a0d020904090308090c01030218040b030712030804120305040203070e0a0b06070615050d080a030518010519110a050f 83
    0x48100154403020380304c000d41c40c4d2040340c0002681d80c0e07580c1d07200454507a00c206452081d081009120381c412075070400180d82c1c04829290410004d10b03010030800240d04003285035001d01480130754011021030b4001910003201901c2e0085901c6600d590782e40007609059152a03007d41d105d491601250602c2c507a5210070131000601701400c1080700141000c03000000328044400820044021811910620190340300800c030103032520009103010352600303081480d003480c0d03420010011402962289459890340e07074188003840c00303030040480000728503009090040005005035002d40f150307031400c880109110f01c42e006240c032441c1c000e801031001901c0c1c03c5807081c074140000d02d07006800303946131010742d44c039519100180301440c010308002c07a00551002c040490301d13507107030b00441c40341c1089401c51001030601c905413032004501d402d000070346545940b00c0400d4030b40441c001e14455443d01c0308114414403031500303556181c000401c0802c054000e440d4400b2181c4034100b09040404e50611403c0c40030452140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 35363053 1250 35361803 35361847
    0x105010e040f0218030106050402070f0f05070b0c03090a0504050601020a15060503250603021c021e0304031e0806030307060506061603020a0b0c0313060221010602010603020321 78
    0x400525000039070b016008a0300b05180c00801d04200921990701460309014981c054007040700c04500e883d0b51541c40e68095050800d00411401142c0001810702c01c003409104000d1004503401c80d038a860646644d0340340e80c02510b0007071007480107403400b08141c00c040c403403588580010303001040504c807103489616007202410200041c071a00c4a0300805c00761424404181c10f940c000304100c0001c4805038000006408680001c3c0402d403043c000800c0c03aa41e4401c9000d107070500720300010780c2c03090319040403840c0360f404c1c040307803100e150001081c00304041d8000c01c0d02e08100007040c3c40e002080610003044031801c9080d290a83e02d6401070082d440880d2175503006c82d80002c0010500c40c5000d0310f2030541c4042130350b06002540503800100d244414413100c09003883c0e001c20f210076040c0c074514024035641c0f0900b4000c00c0240c400c590110f1300703001140000c02c0c0c401030080c2850030140e0540e0b558100901a00c3e00d400101e00038060f981c0d0f1190352400b02d06c1e54040c02e680d10840c1c5c44c10300c800e6801e0710006c2d444102d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 35364303 1250 35363053 35363059
    0x30201180503010614010914010806060d090602070807060507020f06060f040b03070b041a030c040605030a020d0e061608090a02010804051203040510061508010603020d020906030a0501080c010809060105010e 91
    0xc840069990350910a410082903c80002101c0454100002d0420481c0c1d500200000c4010100b08940783c1c1d02409041c2d21910403110191a14a224603007030081104079002001d051002400600703100e4020041d003191849000b0621056496480c200d0312025203070341c1c0298a6200201081151a01c10340d58007086801030305c0041d03440200c10000e40340c88420b6005103004400041c091000340040c0e1030003401a19510b211501d181403003500c80d00b00340f089103e00c1d010407402101250070310090703804903100001e601c0c3d0280700021000c404540c4452081e02c07400141124502041d164600483c0e07824803848990000e80403116250300150346500c1d0042045803075008071140d049000041002942c001d900680c01087c01c00042003205007111103540048100d03021200d03132440710a40c8102c0c403905503981d9240160b1245d0303820380c610700640074031116076a0040d000310801283c01038544c03126040b2040f00d03080b00c005a0303258005464088040d14101080c0d08180300502565004840b40f02001c4006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 35365553 1250 35364303 35364347
    0x20f040b06030a1a0d120c14100b03060109110304020d0c150302070317010e07031e0608010e060705040803040e1b0d0506010f02121e091005130906030c030201 70
    0x90019100d80e004032050483d1660721185943c410000904807207180005852544d41c007140d030746a005036003480d0709181c420031014800b11020449204400303400c170900c1804607417551340d0580c00e44025010f9106d1840c087c4c8034040000036080b1aa010b4400707002c1401c2061440d648858081c461a000d41d0b4070b00f9107040c3d04202000070389981118180c44071500701e40d001a00c928840c070300140410741040c4116400ba40403401441801d0341070814607000341b002e04001449a8010000000e084180c3c82c2c7c500a491403c4000514502c040d08003e003030101400a0740d9160396000307000c1c0c1d483d00680c09a1706003940140018001800d29084007900300c0003800000410070640b42e0301d415540c1c07118028528054036035042c03008958000340780d0588440d450003d0b10b4601500259900c80380210350303885040f00c0014150041a080315011540085c501404540442e4119080030b070035544102a103413014248004000342c040c09510900003680d80c02207608260350b01d5900115101d400114403c5184407403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 35366803 1250 35365553 35365571
    0x16060b04091a10050a03081605211c0204080a03050307030216060902010e090601020613020a0503060108060105120a05030301090903030e0a03120b0f03120318060c04090614030703020f04 82
    0x22944408142c801071001c0709860a102021034080e0b450303000324000c51a8120900c002403280c01540c1e4200000003900281c202c0f24100903241c070043c00088275020b000b00d500902c000d401200240b00340050050a40f4010709108081d80492089115a0000d0b07041402000c00081c803c1c4020340d0040c05501d005810841000713822011101e04420481c1c05070755981e440e01c210750304046030608a690860b0895690b10704900040d4541c0b90040c850301c0c414041410200840d9900020000a004050100c0701c0c190386640c940c958580081c060740e48200079008416948420025400348965031210245045900c0c103440000502900d6204405154944210707440c038640801001405501a03514409118041004101240c20780c0c40550702400d11340303080a455032000a0004400c40030702c1c440540d0b99680c404801400311410480140c0c60050fa0300b84218400001d0140c019650548000c100080c2c0e25140c620804954108041d01600105410005417078160703110102840003810106070002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 35368053 1250 35366803 35366813
    0xa0c0203120108150a15050f03010908030406020301212a0305100c1d06121806040507150c11010c0804050604030302162705060406031707060c0516060b0409 69
    0x207400d0700a40180da01c80300c0221410742d03240c10155080260340104000da00b00005a29401010b18010310703004400060702c1c00c0a949003507001d4640141c00c84182503c0f4102894030001a510a20800d040012141c01c40034049482d10b8500c00120303400000d00900f03841c42020602143e0210b103076172a16034000100000487c130180aa105441c00f4100c0000300a071200102030f201101402c80f656a200a80c0d540111a41302d8504652203180b0300400103c0380e0b6500f01c00d04540c040c6280c6d002c2c0060144c8000c0c0000c0080018158059a411040e41410b003100e004048a0b8010a84400f50401120070420080d650080b142071001038040c503121481c09448801141481d4056030080340183e0090100c0700701410100c0320349005d045640c40c03450101c02d0700c0d450740c00c40200a010a8000c5507884020401c1c640d01d6500c1540119804074092150001600545180e504926401e81d4000c2c02c200303498191074482c1c01110112413402d001680800300580b6903000820700c01443c01e41003a503801103d800f04e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 35369303 1250 35368053 35368087
    0x30a0e040b0a08030a08010605030123060f120912090d060e1204060f02070801090302061b07020306010308031e0103120c080403150203040507060c0b06060d090c06260408030a0c0203 80
    0x807200c2d03c000c540d10300e01000c0c01040054142d0000d810000103000500c40c05243d140110302003041003885c04104a01640015494442c2a069040058001a040300050f4901c2542c9202e030071013905032141046007140d04c0c1024484c01c0c4802e0361015100c038404001a18950020518070301d4642203e007a040d101081840a0340700b03400c03c170003040c822050000c40683c104001d10291011a0090202030080d0ba006550380c200948081c0c0f031800026048100d409070801661441c50300102110328550352401c0c0303002c2c194800e580000720a81402c1158500c03041d440c40e118126035025038801000403007144100c4049881d050100c03034160341000b00101245880758010040c40384901c0050713590a151400f546041c2040d0310110610070b190075000701180340b03145504d41c8081c0549030240d0315000219140006c10701707440f0050501c1540c840114001c1e0f448040d4006504c005a482c0d450224020042c0c440e6078000c44008040010800000d84407803183c1e00910360000c7c140c0126030808000010410f1700c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 35370553 1250 35369303 35369309
    0x215070609021306050f030712080c031e0a03060b07020d0b070212030f0105120f060105040c03110304050c130e03040b07110907020c0102010c0305060603070311160b010e0a020c030a0e040b0a 84
    0x3091322070205110620300307100004c0445808400400c1c2c0709190626505410b1601c11000d8003d00010802c294040d800340111045036050219041280d0410307981d0002e00d400c24030200001a01c0c1c4000132600410b0641150119900180403020b42e20701d81d0f0f500c040400c402001503003180510070841c1404c91030207002e103005840306080140250306280034080315a1301c000128507140e00ca440074401040c400305019064079001c0d01d0104000f001c884040d00540310403540182840d60001c208001d0120101e00c1ca2503201007240c0d000e01c03c160010421b01034441e03900804450b0342042200300050710020380109071040c440d44405055422040005034a92012a03080d0050707045071848050380e603428490446800780c18101007103641000c001241683c04000e000c4c005040e03443c1103d03401141103500760340610645000c600c0c9030341128504113003202c0d800c0c4500d844007241c542c0403411400942c029252003c2034500190301300f0039180750464a280421b902e83e80c005960b840000c4450b19071038002405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 35371803 1250 35370553 35370589
    0x31801020304120506010503100c0917070b0703020c0310110a12060302040203090709180b0f07090b0a0e0a050315041b0513020901170601081b0c01050414070801020403021507060902 80
    0xc0d940c1f42c64281070501e41307880d0107140000e01d0460118500c9405c100c07100195411510f07000d62901181e130b00e00345000b0b0543c1040041c50000700d0705804140d40019246032446094040d681c405035503071094000d58100c10350480388604188241d0f10114800c07a0703040b205248010b400300d8225602e0300032030100e03482900c00f211940c20018003400a0030241c041c1110708000c80760202039500e4180c07100541d100003e030240010348001000301d194188a5500c0030050704106145595030482440301400c40310480440b18001d285040e00002d45140c003269288651000f00706142e11681c50740d4401002c07840019021040d1080c0400110345a102c6103c2009200840c14006903540341601c00549003225000c0c0d2240c040ca07070042044802d076031000185803c10242c5400c401c281d0400d6800c100c1ca4010f59112001c00d43ca044100300070302c44080b003c0b0750301c4284038050b40c0886450302c0201e400e0744110b0201075040240181c500051281d600010064203001c0c040000784017400d9070010b0307504d03070440000d20740e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 35373053 1250 35371803 35371813
    0x80301051008040c03020405040501020910180b0c1908120705040306060801020a090302010503070e1c02040c0203030c0a050a0905040c0306030b0601020c1e040915020703030b0604080318010203041205 88
    0x441c244124000400c1d040c0741010000d80c0b4203503880c1000c1c8041804000e028a803a0404503040140c00d4040d11074910000b0a0580d004501000044c50351140101014080c3c1405000140f542c6c4c10000710303810380d0740b038001030180120300740f00b0380002030707801c100496603890108410301c0152040040341d0300854140d5121981d580c59070505206170f030444d8110402903403040042821a40c1c10011141c00c595080c00c004c0c1e200e540f0301c0c00c20340d0402e0190800540012034120342d0309502c0307100d2480050341882207a04201010344010226906e000488927210401410003021034080d000c2c0e000340c501d4200303d00e000d44020f5183c0c070204040d168003121030004a900d903041401001100c02c80241c1c420310030301c010181015950006005d146000401074420402552400440c0c0c440d5000042900d4000c0d100c00340c90584180401e009600031442900040d2078a90241100d190090443e800c917141e05000710306050114004e05050035040c100141944020440042e42000204017806001e01810140c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 35374303 1250 35373053 35373059
    0x30e040c05090d11131107060b0109080307230604020d0f020604210c0e0c040303030510030803090d1211030601050a030608160611030f0f0705010207020d2904120525080301 76
    0x21401500c8094814060914045402d2000c0c8a07080d1542c7c00d4014602043d207002070030044c2c98004840d001150580000111582400f00c414a50001e081c12500ca401c0003699050811f074403150306a80080d031050600c6900404242d4151018100310f000802161a0903540c01d0a19134031000044043ca001c0c00082105007400320b101d41c81310003418060400d5000d850011081000340c800c0380802401d0556902c003062486603c600280041c6074000c03c031583d28200300c1049030303481c0d26041c40031000400c180d03210b6503140214040d0340c0d4440e5149400c00c2c29900c5540040daa6500310001a40805584800000740441d040003458102d83d10000d00f0441103080004c018180d082040c01d0500765441046464030003200c03070044070030420005030300d00d840da40a450b20710302911034203d019500100b0110240f003400001d0084408441d10140740150000a01d0425455060200e5020741554400f0b6000042103000320020031001d43d44500200d036000c15800c7c4142d0306459208240c0b641c501c040018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 35375553 1250 35374303 35374309
    0x1404030e0108090d020d03020f0403050106060315080d050d0b011101110d14060d03030207050f030a080a1d1c170903070c0605070804120303090822060c030e040c05090d11 75
    0x3075070003da030703400030705080718001101075502d482110034901013690005910600c40311402c180c0340a15030100003446000d540c0d14005000e4610004002d0302d141c0031503000940d0500000380c0c20b601c018107860f81800c2a0b850703503600c03006222a020740d5045c050461050452050288684910300384840c01154a50102d42c2403002101c00c1001c2044030807a010301402980e80d588440e982c0025031524001d82d031010746152040c10111044150b99243c440840c071231758a141c2107c115481481221810402c82a01c500d0341940c4542200c0c0c8015190821b920140c4007582c8414207020500c490306105c09200701c0b0300284010204100e0340c0c245107400101e80e20003004040601e00000b0006842d00364100003150321071419a01c01c81c0704804514520200c5c01c03003054080c0c0c01c034040321600030541c542c0b0b80e40b9012003070034105900000d01c0a00d803660f40c00410060301909640303480a401d07581d10180102c040d0103100040626001c1d01d010701c201070107180c0075541d03001ca1804580e0300c05c8603418028180b220074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 35376803 1250 35375553 35375567
    0x61119030e0c0301020c1506040207080f09010f030b0f091008070b09090709031e051507051305090705090904051002070302070305011b0c1e060c030204030510050c040b0c011404030e01 81
    0x440c030702c02e9004121b001d804013000911050100c0070704510620703035120b80e000200248554800100103803404281c501d034600101e8050b0031131400c00c2e00c50074100840284e040f003c54400c0640c01750300002030444841d2030700f09140340960001c1c80c0c1e1000c01c10b094807801010b00e818429845048110742c00031314961942001c80801c8d400c2011400e1100f00c0c9800c640c1d50300c0c00c40c1c41000c84011908043c40c038400510904202c4420a1481164040120b003804000281540d110342c1c03651500010903c0000703214107040078050f2181c85142d0300c00f400c040710b03c030030030404410140c800e0303c02d8230801d940d50b0450b001d030788010221913104c1c4c0c0041c0800c9145103411401e4425888448007038240b11194011500c0d002801c1c0c03101150b105801c914a9106606290600580410302501891415248442050b0564000d200f0b0781d00400031a400d89445040080540d4401c82e61010329200900007005040a050058101c5040c28000850036403a0340034440032480045600ba40019034a40c040503031541c01c848 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 35378053 1250 35376803 35376823
    0x41103030f09040f020306010f0c0302010b100905030d020c0303031306020717030103021003020a05070201052b0501080c040e0304050d0c18021b0c090403110307060207060b01020606100c061119030e 87
    0x784c00e50071840c02074006856041c3c102540700c2400b9035102e047c41058801e5000039102403004014580314405424020044003460082d14024450003000540741400060307400c40412000340110700d10740c1c2d000044041a251210110f40c4c4503000c0c00141c001452905101502c2c001c2031019030344941c914010040000c40d41c0541d0400e25204010100c0c0d00c41d803100403100d000b50282000c0340c1e51100b469078401c4041e403101c0843d402140c0810f40d0910b16040382c0065040f603100b80202c40c030841100007080304075031601410800b250b1040000300140d0a281c24030840302c0c2d004111b0b248d14955125584007503d81e208015000c4280c4c0060407800c41d8041414006402c00050b008040135415000852102c071000341026050113894010380c4201b8504100301c45034564044029074580c0311a00d021000b91101c1141207000d40a00320000c0c1144c284500c5005103042c540d074501d05613910359280c00c00200498000099a24010000d60460400071030f0300d0719044d003d940d800285480c002030f103d414600409 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 35379303 1250 35378053 35378081
    0x60a0b060403030c02091005090f060307170601030b0a0e0303070302070203060a06030305120c0c15010906060e030604110301090611130609080706051c060e07090603020f030c03041103030f0904 85
    0x701090011a50103450740602603415203d11015807103c42e43c40680401583c0101da12421400400041488400b0314034010308064086422590b2200c3d4007580c0e413041404001020b40c0101c0040001c9916007004982120500d8000a22081d40c142d8040c10b40c1e2080701c1d610007080e00024851300b103003001c00543d03620100410342004140d08555000f440b511811804c414401030000200b03966050510894505044c21021114207c11140000e1105a000d12800c1a840e150450000c2d001d0b00230100b14a89060040c0540f800344d07100d542e090b829840404070b281d0551341c0c40a8010000d2030921400610b2014202d0507031701c074411100760480044040c0c001713504200d80c01c0030070080d41e0b4002800005440342800c3c131030f45a24048a02d103002c072034804274003840c03035041110000d8a05440600b69001e0105a543d40001540380c0405800360b10402c0b10080752010304000040340c0000e110003840e001f600c85d607400d040c0549000000391440e0060007002203207440000302031059103410312581410103004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 35380553 1250 35379303 35379307
    0xf08010b03041b0e011d060f030607050a0215070324030302100903140d060501020f0307030914120a0b100f030206040b0f0f0d0b01080a020c060601200708060a0b06 72
    0x40048618007000c0d0004081640e0b807284020303000d1429180401404103c1c111061643c0d545400400d01034201c01e85000300750312140480e036a4200344000d001c5803040500200100c0d107030002c04440310350145000c18214095411401c5084040129507030140c0055600426041002803011807084450711600e205421038140810000760040b80b00e405c0703542c5003200082e407640340c1e040681d0701c1c440c030400d0000c2e00303640020f540031803503126407080e010b96000381c2c00c88040e401c00c550255034034818000b000e80800c980410421600d850941041034002d000380003041744110180900d07281182c444c108032206882c010130000710b05014080300008210b0340c0d40603800c0502e1a004100144268020f404040e100000c4000c200c80101c011541c40755912802e265840225614440003040d102c500c5038002212100403444410a50007a00c185095500140545403036000054070513012003203c0d00c80d8450303240070383c2c42c0c074150901c0260010510000601010310f0004408401c950400d030350715214100c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 35381803 1250 35380553 35380559
    0x12030c02100c1104020f0906031003120801060e06030a0204030b0f040b07050a05030f060a050a0b0304020406091b030903030b0613030506010b030103030207060c050a06090f0213020f1213210f0801 86
    0x62841941c41083d05035801640d840c0507145840c01c034460b0074012500100d00005000044101d8540d00d01224003400301c10078001c6070884e04440d519000e01ca40c400084250106080901d130460081d5002484401d0051a01d95240d031075040010085616100f4080c07100100014007038901813841e8010383e2403504e94a0901c50500c0a8114007024014006105c50b16002174160380b0780d030410300041c0000411040c4050f503120091006a81308075012406103040c80c0001800040314000c00c0384201400400111a5032991421001028011003d8080503240e00c00030025485040c001c01040488406010a85003941040d520301001030707220881c143c0c0308100400110340d021802c5000d030340b031501d400c0000311760318101540360445500c070251900d454080e1503030402c020a43c840d01c1241c42035640700d4a144440e03607410100d0040240400e00d0640402c903004581201154041c1d12005600e118108440343e0303112a40007100019120a044401034421144560060a4146411042d240a0020b581 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 35383053 1250 35381803 35381813
    0x10612060504020319050f010c0c0804030201030b03210408010515012304080706030515041a040f0f020a05030105091005010f05070f060507080105040e0304050d0206090a12030c02100c 81
    0x8000009804107594001160465905128011104000c00c40001c550f41c5281025a00c1d0042c2000022880d0300e03051002c41c070705000b04080c1112a07000000305013000e2464006501030b0110790201581402a0740b8040024014a140d00244e016004a0103807a142020803107821158054149440a83c034201c8880d41a079000c9001d20602e19009003031510a290019441c41030700403600240e0403400781150200b002d81c3d0542c40140300720064810f020503180200140022159242c5007810780c1c111a00c255050b0b030030103070890290320758a00340025140c07545030340341d01c105e03044070903a203001410010040000746003510780c458020502940505e0214074100010305405c850603041c40620802082d0318081c0104c000c145061160003e0b018461450210030082c172111003401400e02c564600903506480e03080c00001e98040e960040c0600c0104c100c150200580c40c0c101400b81c580c80012110081018074004199004081c07090b1607942d4001c1071881001001d66500005c2d4040012100110000c13407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 35384303 1250 35383053 35383079
    0x209060d02070201230a030501050f09040803090304030f050d02010b180610050715060302030d09140f0604050a080a02090f091507050d0905030c010515060409020a020709090b0610020106 82
    0x2108003200142c1c0c0c1c40aa10040c0c2d07011100503400002d40804181d2038100e111000f000b0440e204a5607004c000917a00c42003040255040d840803950882905800a000984080015900803c1070805c40f030410b5540d0341c070164040c1008000311610380046404188240d0240100c0e0501c200895003000e04c02400c1e80d0b981c84121000744241d100b01466400c00c032019000303100700c0c0c4c400c1e500140401d102200403008000034006030f10080340203104110304560b500340305164400070b907200c040c0c161802c04a42010842c8051100c03005130713800001008002400e9981ca1414001000f02c2d0020b0010450103004100708000010984454172900c923003002200c81010860410305030440c1034038003060329181d10072101801507900005441e03103409419000e000300000904102c43c03460000b40100c1d40c50138902c080e10744650b800503810460078841407248007400e8002d40302292142c030480b141c00d030b605d10035082035907a08101a600e0341821400e200c020300388547c24064110030ba0000340140751030402020000d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 35385553 1250 35384303 35384317
    0x9030f0a0e01030b0a09020a110d0203040509040c050409051c0e060301051306031704080c030f121606110a030e0d120902030309100f080702150106030e010b0909030c070603020906 79
    0x8034850381c9400c002c0e07000798003403800000090800a00b0a0312080d60070000d5106200180115a0794071445101c01c80005107880d444142d54091030078540f0f07100c103000707480780050800c60741440b0402d00820551110b01c41c00c45043e000c0d00003410240100c0360b082d9200c05c40d0643c00f074100918200400303541d44031002280d0455805883e0f0510f40c8e031840c01d10340010007058000500000880c040c007451035141c1c2e4054000d07503a00070280c800303d0b90700104069503801071004510702d0360081c0003052540910000030b4140344005036042d130f0800c030302592010211164040c1904860001003101440280d061083c011444aa08014142080f000501610310120b4460000e07001c2d46582c4844115101401542c014040c0501010b40040c07400002a08140d0201328500c001030300400058030b418800a1443c4140008a200c401141d0801ca0214043d11301c60b46120440d640300c11440006440d001d11292140c86590090758644e1444440c65003880c1c0141d111900301801442800800e03a035110454580e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 35386803 1250 35385553 35385557
    0x10b0a08011815060807030f02070506010509090f07060305071101020a170a090213020a080606040e010306110c06040b0105130b0109050d060e0a0b09070608150904030e030a03031409030f0a 83
    0x3010b8140c03880e40c00740804101804103d0b02c12840000c2c450340081ca0b02d40651000c0e1800d1000601c000200c0049028840c0040c1c12507101e01c0c0100072034180380300b40c150488081750079038080c0c54007440000c2c905180c0782d01c018000381e0b64104011410b07901c400ea5620301c113010002549006507405e4004c20304e040d0204001980340c0b000c004140d00c21915404100e090340d000c0c0403162005242c180000003504400e20200103e0501c00c00580d6619081c02106c0540700c08823000a4580d083d030304c4d0000140041501c18000204c20444d2000c80c0b0b00400900e031080b840b40501c04100e6042c107051043c2d0b1806000343e07540c40380c00e02c40d2480190307070840b02410a0728829940c10401011905002d0090043c0681c11400c0e4042c1c5841c100c144040011300d00c0c451075503802155840c40c0c0d907850880e8007031000c4030490719200c811602c00019140140600340c01030700916204050251000001e802c2c50040c000441c0480c2c0e64800e800b00a1401c15500c0e0b80c40411100a1410042d105403880c4d1148130740c50000003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 35388053 1250 35386803 35386829
    0x6040b0310111b030c01060501090305030a050a09050d052a030d12020708041203030b1009050103020c0a05030a0507030306080a030c02061c06140102390102010908030c12010b0a0801 80
    0x60b8010410064410311141252412140e82c1101041910790b8416103014000e0b50810001298550149080400b260780c0030300210b140c80206242164150820700101d810451449000078143d0786405102003d14003d4014040c0d107040d03084206660300c42d030422502000400d82102d00240d50101b05901045a90f0811030112102c1c1d1701d0f600000d2103103c3c401402c3c0c0300c01050200c0c0c0f0506a4401d03420392446500c04200e0120307007001304000b140d0689410000100d41c0c15044c82594429006402100900c200321010080d040e0b80f25070554010a2840000840124110042c103605018400007081c018004c1c010301c00341c90310000d24445000101074000c03400000c0d640001d0500c044045181001d0b101c0c10006141c0f54040c441d25030220703541c154018400c9109189821408606540e01d00203565004c088034205001c1c08000a0ba4071541c3d28199580e070007918000c44d1075080114071404840b481075036107032105000b02041040682041d035204806001116810b0f410100d03960640e1900100030f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 35389303 1250 35388053 35388071
    0x9050307060903030b0108070203030c0f0a030b040c02010506011209080d0203040c080d02071a0a2307020d0c0e0106050705030f070c1701060311040b030304090e0a140d02010506040b0310 82
    0x54610310400c400103011510b041c0005003803560591201400c0002642c540d402900d03090300c204e80da8041035615442c861070400c27102004220b00c0000749003400d41da0a01045800a003070005040390711111b88900541d4551007080880d43e8400740341a2061140c0404102640154540440d24050000788146080e40000420240070803100300500800440080300c1d203a505c1e00707000a454030401d114024183c00380d401601c810714000f80613111181242d079510780c031946200d0f07068107900740d030020000c603800750810849000d40c49008407000018007034000000c615140c0b04aa202c440016072040040003818006900004e80120407113840a0780011180d440d41914100f00c03070120540c0d408142d0b549044c1c01000000b52064000754100c80c01910020801340d14402030100342c603646203400b0740c140c100304030600c0044072540c0001c01d070208290441d0b5803a200b0755224511880300342c143e0350103580140d000d420120782c24001c07254414000d480038050701d10281d02280e550074003089003c0301e0f151520651 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 35390553 1250 35389303 35389313
    0xd17070206070c030c050405060d0308040b041514010f05040501030302060a1505040501090b0103051803040513020f1b070503120405040506150d23010803030c0c070308040e09060a0b030601050409 86
    0x41d80802d03800905081d606a624641142000050300c0380d10300881c140302c00600d4600d0142c007003d50003a0180c490381016603c03999481110a00108215100541d200f804060b510341440344242040f82c13607200001d20b5040c5424800b1800741039100511440c2004014000a50301040964100815180203d55001480c100c0480c440316178000681092600c1d000040c41002504040000d64083c4ca00b080340d43c8482e1020340381e840902d03840d85180d5104000400031801d02560722100c070744159900500340020480622031a504c400315020b01e0602d440740c0c0d400c5201c03041c00504020030046004102e00c0804800d490100d01443c0308ac1c6101e19035580c005412510350011403d0120301944c9006d954501c454101d0f002171424502900c00c041c002050703100842044030a01d416108000c1c010360450351603900c079003815403042041c0c05580c001c0000010001e6150400340c006422128001c0d0b0b01442d0103072145107841d0b002030000e20810b007054880c100c6500e0202e801c5041d41c83c1582c001c101c0326114146 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 35391803 1250 35390553 35390557
    0x8030a022125060e060103110f0607060c080115020601080a0f060b03011d010c08061305070c0c030f11040515010807020705130b03010b0d1a270d020106050d17070206 73
    0x5801040b562544445102d01c50040c0c059103043c0b181d2010030220220b141c1280d540c072001d000042840c01221082c040f176180c1941820b50002e0014800c52a041a0ba07451800350b406903050b10340403030f65a0005200d03020982056101c0440d15100415813589410b0101e5503881558201405c4250f04200e558248a9190840b10082001030003d00c0150340f14010084801403d040c068019481d0201c8a087d00f84200c1d4110b0042000038058103c0e41b85041151008000243c581d80074030607110203010000b450640414025030144442200c1c40300c06050240ca2000c00b060540e1065240504200c00075000d5002510011420319205070a6912944203914019040d080250700c0744420488000090040c1c00200c40820247c000380040105c030014003811002101c1d0043c24480400d1013294034403400e00e00c2d5548214200d02d0002e012001c40888200090702240c4032546e41c109041c0c03c030280d5024054034004000c15660500c112a5507203e4440c204a0f1303100d0f202c11a08002003480035940c41c541 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 35393053 1250 35391803 35391817
    0x3050d020d020c0601140103020405010e04050606070212030a020601140d2003010906090210020604021c0614040b07030b060316110703020a120b1312050a02011509060302090108030a0221 82
    0x1c0110340e14407080c03c405650701ca0911407650a82450001c2d448294482c1c000e40302140d1041c1c4803402100310040070080680300040006400500034000c06001d66038004828031020075260155a03039024900000713051680503000004c1e48140349440710502e840c0e10847d8915030ba000071000d40580203441080400340f2551034110707810360034070b200358041c81f05681c0600102d52003194a00800c0d00c515100341e0f12020120341c0658844229032003c0c811320340c40c251003030015100703040000d4009028280c3c00380c2c0348000d0b681a00ca680c40507003003001c02a09440f0b10404401c084412030304600e0400040d400e546400b20305070007040b8045044c03e40da40340402c05c1c07138003840c1e00800782c09080d92524840703030643d240c080d01a541440b60202055034140c015611a840640000c850054442541c5040c1c40a500248a10003150350390510400104610912180641614500428414614010000721300010707042092260020000b620420340c002424a0101508240882d80e40b00381100010050040c22 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 35394303 1250 35393053 35393077
    0x1509040b03070611060906131e0501090609050f071401030b12030705030a080c031003081602040501030c080f120414180108030901030507020a0308010603022a010504050c010807090303050d02 84
    0x50070100c3c9140d00304201400e07494841342124040ea42c0c240200b81d03614010390301c00003500c045115240210340504414074104141e10b0044008805a0741c0c0e644c2101c8d4400d0040c2c030391700d0b07807580c1a00030414184411901e8015142c000d08409007440005680d035440102d440d81455902ea140750115141c1428551030540c8007000d80e9102c0105040180c6c41341e001810a40c0025050400103041d0550442980e02408a002c1c003800f502d0f0a540d00e114141d804804108100001d500001006030fa0301c0c05000c3c0650311803103c2010346450480c1407480c14801c2c500034140c6030400c1009114001c810030945080310107180643c5146002072003c0340c40103040340c2100b000000020000b146003000003004020b101805e81c0c081040b540c80f22000c98031001c45000050001c0c61000041001c10301c03c0d0003622158441251a00c0b40301503a03410600b2460391294850303003036515102000144081440841c000340303020b0034054603928052000a00a44050100505101c408503011100b00e60541c10b44250700340070303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 35395553 1250 35394303 35394313
    0xf0e1305040501050402010305070801030506070c060209210120070209040606050907020607090b2a0705040c020705030705010503100902031b220501030e1504050f030f1b06061509040b03 82
    0x20b828901e010b40350485d02640400e040c04081000741c0e1140e24031604072904240a0110303611001000c807491740a401d0161045034003403100c4031140c0d994820b0b518940d003501c030455820a030101c1109003510805010302c4200ba045500c560002c00902c1e040301e40c01a070440d0b143c03031166202c2c608503000b4001d40d0001e6801552000c10840015000030f91a400340c030050300d5440013107945614841803442200469600440f6100505650704031125007602807080b058150358265403104081022500a000603000685c0031050070007017818140107003800340a081c6440d600e07601c0c000280170ba1269003031141d0452142c2c00000244641035201500040d060f503100702555469105041158134010b00d2500c80000c000c50800103025806480781103032841c001c8010b0150f6140080c40301300a408014403c0d0b9040c05510032000e60200144000e15035a80c0124a8640b07802034005070400e4054000c0540b040d581c4084103121490f650401000c0d42c080b800c2400c01c0d501c0001d000400c000e8007a50704496050300c21 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 35396803 1250 35395553 35395561
    0x70503070918060c050417010506010e1023040311090c07020603070302070c0b030f0a0b09220b01091508010902030606102001050114041401210b07080109060603020304030f0e1305 79
    0x121a0040048501411104440347ca080122508841098400e01d021840301241c2c4a03035420041c211300d1142c1c40d00e0a02060f5038040c0c0c074480c02800d00d120a9a1466080058113004002140e800c0c454070441c1074134006075900e842c0b0410780061113200006803203600040000f803204c2d03209404039403c150303006481c0c0000c140d4030449015140c0080e00d94010300e05042c400140000101e00c240b00c03024500070045045603c1d084112402d090761240d10030020000040c24a010801d48500140204030003c40011701c0311240c08240007480154001441d5a41031200d01800360341c0015440340c000e001180d204c0c0a00140d2082a1a001c0701d61040190305051060100000c0d50103620050407641d004483c1c0050007054000c0001b140d0252a070700c042c203820f1034018000d001000c914920315010200621611000c20b850f880f0800f24211154000650305000600c46d074074060240b00000e04041c07e082d403c0d4103050f81d0242c05042c960380d5520400c84042001107003541c4100155003a40c81c509010449420 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 35398053 1250 35396803 35396807
    0x1020f090103060e040f060f0b09090c0a24030c0507020d03080702121c0c031e0504020312040305060a05070203160501090b0f1006080606070b07050306030d02070503070918060c 78
    0x101080c0e9001ca49804000115002e400a4140c803c0740c0c400c08001403141d107076072041d00401d0300400c4076111a645078084103964990b072103440d00070040d5000070003441803106d082007248104da41000d180c0840c440600c812082030004410040196070401080d8528005401c65660280c0700001c1d50060040b0042c1c0285074108840d18042c02c11a429a500c4902844001e0814400e508041b50001d20340f1405442c540b0350750703114100f000d915184c04503d00104078102401c910140039080c3e0b00c2035a40091104502e410009021500210030846013014516103501d501c5140080208101c1038491000468051090040355114241000486441400c900f002c034020028000d00700c484240f668041100c45400e0001203100346900044880c0e60340c2011000c556500c0c0103000d81e07801c1032081c8070301d2001607265040a03100c0d0015594241c0c980c54000201840d040c144000b00741075400000051080d40c40100341d100680b4950b080106451003802c019080403441070300e01074520b42c50078215003442070b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 35399303 1250 35398053 35398057
    0x2040906051002030a021027080d050c0a0e04090c0506070803010f05041503021e060a02010c12061202010f091505030702060703091e020d0818030f06090d110a020d030315060206060a03060203090f01020f 89
    0x410218010040b030369433425104814858008040003140d007107800c4071842d21305a00046622481001c0440d0750b25030b80c401180254003c64011940c841c400b1005201440d107207040e45008000441c3c05100f84406c0e41d00d14200e20a0502000c2d006070b41c0d03900c01200c48e100300781090415081c0600655941c040810000340240340300140032000507440200c2c0d0a80c007a59000383c809503400759100b84a0715020754015901c200041491100340311040f00c00241c02d0000e141c1400d401c1d0030a40380c00d0b50303904d0103da0003820900300805040c1071500c2c10742d01d0000f00d0140c102c00c10726103c050310801c1c05032030213000050460880e06401010500001100f4488400d40d04c0045080301c030035002c0f940a0200e41c180306445003c210f9a00d503c5030300103225906258800ea0b21038006046483c00e1706d0480038030350007248015407445801d4021030389800300c444113029884103446c010200ca00c050022800c120000450442140c48080c00458001c80480d149460074071100f01025580380085540c0c0102c01c00249584e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 35400553 1250 35399303 35399317
    0x1031e12020303010f0f0b0a0302030711030a03060e061903060506040e060907030b0f01060203030604020304020409021002070f080a0807080c16080a1b05010519110102040906051002030a02102708 86
    0x2210700704009106c4a000c020142510340c00d40e001403d24110000403002908004c01620030068885003e002008003400105608401a074010640d0350034a00100c40200d0301410007402018840d46015042042c06400d00c103895100c8800301c3d40e03844610008000d4064005604198082c0c7e8041c40011280000d98000300c920541080000799500050f5240740882441381c000560010000a5058507056000715489440108000f03021210f540103c0c40000c10340c002c10001da0322602040c4920b00b81c44500800400001009020305080c0360344507000c0d80500c40e0010038001011038050625081800682101304840b0740600704165039048841e0b4600d0045000d460902c05480e0200403039030308881c008161001170712428541801e4051001d01c48504401d07040c01c001340c00760b1079400302c0310070b00040004140d02100455a90304200400c54092040c80d407440565008025500040f500810003401c40c820400002800c00718201c030108a04400340800d10041207404003920802030400041c0c405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 35401803 1250 35400553 35400569
    0x405060c01050a051602030403030f05040f15020106140a05010819091518031b020310051503010e01020a08010512010e0a0f050c030105010806060d1a01120506070203030105060301031e1202030301 86
    0x40741c845400c580b198041720700c010401600200010300220340900b10003c00d40c00d0f5031808903e0103994041ca842803d001c2d402201038001c0c401c09175a02c9940c240203c501900c4100c0001350110841d1000902041c4244500e50511507048000f5160040d2803440d89240282a84240080c00c090b140407003404440d103145003e140d01c2d00c0480380004441c2c01140001d558142c07189580b4204140c141c9040302c200d00d40c2260300d40700e00055402e200c400e50003964021081d0541040c0700b040198101030a4070170b04600c004441e80b05001600809911044150440358103490002c80721200c01c0304640035001408080c85e80d0b125401030300041024008201b84064000c40645055802d0300d01010b0a0740c1003032251102e5948107034046070351450503122083e1aa0b02c2400084010700920013203001d8408240c1c88401d08150f01c4400d1414030a007401000d41c4001c0d280b002e1491981000005281d40c0010b01018082e000300041c1e0b032046a0080032910f03109a00500704001001d46044003c0d6a0351090194500c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 35403053 1250 35401803 35401811
    0x703020706030203060a060809010b041505030c0d0b0708060307090608030406080603030a020718061d07080108030c100f020d0504061b02070503060a05040302070b030703020c0705060408030d0e030405060c01050a 93
    0x24400d4842e10a480c003520700246141146d515140003200c20303c0014100c80415565003095032100e80c0c46201d8009108015030f040005585400100740c00c003c0c00032001800f07010382000000002d060444110b074403125906241c0711035100c03003011030314080701900020440780c82e0020100f415280007028100300d410301c0d80c8400595442c00180341c4c0382d000e849400c00142c0e202c4001400b0100b147c1c01c248030b60542000002030119914200190b035150b0401c1030301d4401d1809428480c146a108598501401d05d610042d032801700b009030041d69407100317a81e14512403a55040080c03101c5005030103c0b900240e89180070700042c201410080c0007010700e0000020451a8452100a654008940c8504031000107004c6d080da507541801d402c01803d0010412030460140c1c8601007614080c1101075401000d440c0c0c0e0058807602a0907203c1d10348011038005920880081c0410007048200208071041000000b10107e03610600701d20b0765166013f55082541e21080118200c0846101540403520070010020244 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 35404303 1250 35403053 35403059
    0x612010302040504030203040f030305041a0739090209100f0c0305130b03011410020609030a08060301060b1210140609010f0e0307090c170c030c0304050a020d0b0411030f03031f080f010207030207 86
    0x1c40c14fc41a854001c2c42508441152080b1003001d91100f24140c030000b070303074904504981103001c5821f41a504565401c50b40842c03074289504120121050300f400500744201d010041c02c130041d2450212010080412000040d40c0f442c0407802c4901c0c2008028851110340c495841d41080c10141441164180c0030301440b101c00540c443c400a501d83c001c41980703010f18604109a08222048103000b88260382540d00d5002c00504002d00000521107031f80381d440301003014200001040140380130355011400790b800014458409544ac1c0c4202c0e10508824241406107020001096544078610303c149a450f014800002800e08100c1d00600941103041c1e54001840c04540d10986024509480401d15040c042c40041d00400303400f002981c11500550480e02c25250980c001100f01c410903200311f980c807441d0302c14041000865105400100b4044024004000d00409082d40e83e01000308540352034010a0f10b8040c40000341003066010300b64003025910031700001c0365414041e6004400c00c9005100b044400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 35405553 1250 35404303 35404349
    0x306090114070f020304031a010e160e060a0c050a0308070909020414010c02011101060902120708070806091b070503071403070f02010806041e06030605060612010302040504030203040f03030504 85
    0x945401240790381000d0581c0c49400084442c2c0d412a519201980b10401000c00410f206d121000304101060068540c81c0d0704128441003120310140418a04800c142e040560441d00002e005000ea00199800d0742c65000c1ca0f86c00700c9042c5000a40940103000d00c4a443c014980e110b00601c4c03144010352944900c02e550f944c00401248640c0c8100c241c03140c00c1c903201e428a036204050b0194031500514141d44c503001800074850031105141d0200d4032259001407400c00e49044941d106501901c1404c0c240018035080c04040c061000060503184260016000107103060707010281040400c1408014684481da41c0c6044c41e92381e4020141135a40190400386400404800400ca0344071035400205440c0146466006444201018110690080e01d65842d0140024100041c2401881c0c03d82c0115950307103181041d600300c41d800340249000b900e00700503001da0a85400304182c112941502c0018040e84d5a040c12800e5000c2c3d81c1140f00082003544000042c9a400000f80040ea804034000b08040d601e61021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 35406803 1250 35405553 35405561
    0x7060506030c0f0f1302040f0f030312020309100509120403030e0f04091203020304080f03130303050601030c1407020303041e060e0901030309090e250608060402070503030112080903190203060901 86
    0x2071180e0104c01201e0001540c10300a5501009040340340015081948034403402c0c0e804c1e88207411150140d81030500820606034400030040850b02c1d00c41c1d08500d181003095107680c0b9200030a50303c080c02c0da10341c0003140c0510320412803c0140d6204449840c1c455840e07140062960440b51059882250941c0c1d00b070015142a10603504495488226940103e8440505070301a400041c8261642c801c2480381d540c100700800011482140d0341c40c0003240e0301e031182c40d000d021900f015080c51b04052600880c81916038201c80504070401c0488030164488a4510001e4614492a007001000c40c24011101100c041888036000541c2e42c80d40320b445107091280c0c103001341c000e4248805000100e05a500700a0403800740e0042a00f48450700030b5400030030783c1c0e9500e00c0b0840c0c048100249040c452140401ca45a0b1100c80c0310380007401200c3c15440d11010741c480ca544da0006000d102c0014041000200030410150110b03506c204010341a9200380342e2035041100800500081a03000e400750b05c1c00540f040e001882 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 35408053 1250 35406803 35406829
    0xa090e0106080609040804241709060105060d060b070f050d0c02060703030c031503030822021503070c170711100207090b01020c03070f05030f0f120702011407060506030c 75
    0x240b01191643e581d002c00c01d0001c40508182c81c200000c00c00819900b042402c0803400350003810301d0020328254054010082034008004407190910311050040c507a0010584e941101c9007214034986a06100da81000100f1007a03000d0251400b00141c200c0800008406225200e8064805c0e5913403140d42620560313440c00c0300b4000130b60050042220000107806603000d181224120300e000112241c0c1c00c5880c0348058200c4d042a000704041d2820002107500c014003071540c0c442c1e481c0e00903402501607401310382000c0e02202c90410384a0048009400c6c0307481401c200c00340c3c030b4025115030354049282c00b00d28400d9100c40c41c20358401703015030302c20f01242c1007640340d10130b003034840d0b13402003c100f40760901140042c01c20809150450241c0e4049103950b580170000316000d401c040d8004922549040e04240c942180388520700c00c00c0e0882114500050f00c0445c06100e5403003004a216a035182e148012200c441210b543e214940b0400b0410600f03002041e80070314406c0c5002e504942d50385006004000340c9008101c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 35409303 1250 35408053 35408057
    0x3020a0b04141c120c050c030706090b03090c060703030605010801120b04060f0b030111091c21140403050606090c0c0d1d062704060e0601110a02030d050a090e0106 72
    0x1c0b900001d60305000d103c020041440044480d01191242e84111400c840400f800000803101410745007400014010401003110440040088a107000009410284948a1074041540200020300c104000f4071a0940080005120580d142858500030f00208002d0042c1800204444008614040c40400e640b880e9500300302001640c0d966542c42c603000d0040094940b40d01c2d030716144580b4423603d0034040c02c003140c040044c0c0552034128050602c100143d90450316a0000d1441d0f03400303004103820040c82c00040507040e07009041e840c0545400e440041c03000c0010040540e000078004103101d4082101c501440e030864541103c2c0c1c45640740200c42d80550400d041a5811007551074401d140a10400511402e00501194089110400155094100b040c070785207050301260200400f0f03400888081d09001041b94100700b40790410101120050b00201034606000000e00a251841020000c02d410705d40d0007001c55001480480b002030a075000000b034134000c1800503001040c0c810084403164180c3c1e05503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 35410553 1250 35409303 35409329
    0xe040b09010608011a0d0f080d020c120301060c0b041406190f0507090b0a020705180f0906160f051c020a090801020906030408091201020d021207020303060a060e0a0b120103020a0b04 80
    0x10801c1101b42031442c0000c894402c9680408400541840068060700480d02401620341e0404844a03040c8008202c0c2103902c41000c0006021442d08200f4110744140c12414100541d561450700603020403000c41c0d041814414a030400002800001d41d0210b44002107034140070846050700c0c120306660003520b140000c01c20380d100034009007040300054020703040c0c9d170b20440316440d0391200400c005200c5814580090f0610004011600c2c0c540a11580c114034910700501d45481c00904064495005c0803030340d4200459a400f104100340306005442040c054254003124041080712450000d5108001c5003001c9002c442001901038011701c03d68195400140510380365644682d01c0d14810340c030042c845a0300501c0424a15424402480334041c200a040c030300607556025590207000b1040002c208a04542c000c0003000902c3e00c4d03408404003201c541e8204064140001c00c00141f45840315040021054808183d4010800e04040302038100c074000e90381c00c070381151500c0141645204600800b0621410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 35411803 1250 35410553 35410601
    0x605030a1110090b0403050f0708030f0403110105040801140403030b060702011403060303070f080301060806060403210201020c0d03051807060203030708070201060512030d0506120c04020708040e040b0901060801 93
    0x40d8406030414140383ca4549649900c824a1030810741090f04152505c1d8042e00861801110410148002e4414640154205420002c100c40184100d010080682401050411003039015405650250050200900180c6048130a01140f9a0220350960000303003042031055460030003100b00e03607400c1c0e010b82d90b45000101d1410303120300f10782c0041c0c03039250103101c20000080414911211a0700700f07031040b010660f07203505d0104002d00b60300d401b41285200b02002c00040bc0080c4100c00080d0411540399410200000403c40030b84c0203014940d2920960b0013000001c15045605a120601c18030410044500381020085d6095503003e56001c1c62002d0783c020004202c0f05030107a6901684000244004200c040e11040424034124601c010a200380d440451300f268161454051903500030002e9800c1d8a644030307810002a92200d0b66840d0130b0090380d00040c0401400201c1301110301502c00d50040c1d000c0d60038545048180414122640032040d4a06038000c14480b106000717001c000c103094443d202044203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 35413053 1250 35411803 35411809
    0x5060109020301060c1b030515040c050301062304060902130314010506010801210503040e01050f0102011a010c03030b100905091515220801020d0b09090a0305070215030a0209040605030a11 83
    0x1451815400c0f42c0404400c00000900204411480000c0c1c1400011103422b140c5840c0c035105109030000f51007a4102403052002c002080055241d0381c0c0d1401c5445032002c03600c80400c0040c803464000085860000a5000d040442000c44804683c4948661017902c5004420542225030658181c2c1c0000d20b50070041101d104014002c00348100c90101650384510550340b454610741c0a0f50100d90140c031140d00400207460040d1003c0780fa50402c0c0024441458410766103200024840415410300034150b24a209051081e409001204030140014403134681c1c01c04007404610292041768032401040b00040d05c00da524078100c106480019101110580c032010030040780c0d4000c201d0714a14142e141180c41101c24111038110020020500016900c0c2e07018003d19041c2c94083d600c03640161010b2013441044d500c0024030f07d108941518003992103800d00c0c800620482030940c840f0a0440002c001d1090f016503d40c001c200d00c80086804004040c1c0e0b030818035032208000030300544180244580d03404182 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 35414303 1250 35413053 35413073
    0xf0604020f0d0516090605120106051b07080c090c07080702130209060a08011502011413030302070b19180305070b07111b0a080111030117010204030b010b0705060109020301060c 78
    0x21081e000780c00d04100140c54003804491040302c00103d42040503030a482c0250308035240b00c02030907492502c289440f01c44c42108424000600c1440704001001a00074410310650394a0f005800e0f00c1d2050320701640d41c40070025550100707103910030f1049031280041001d4041d030a04403203105a101c1000f50801f20b03550200305403060f0040000d0388082d000c201241c51039442c2001010b041c40c49445182e039550505450455a440003004801503a00d00307801452980c00120110b68403520401704d51a0719078251600310040e0040d503a0042118405400b4001121809840c0800c20400b00c40c0030001c4442c1004d80b100031403288140500030076003c100960205012404a5a11410506102003008034882101e86020300301841c0341c031440030f494080380e514500b03501010300404070302c0001c1c4406c0d92000c61000603840184a8590350784500820070106100c2901960000c5400404086240d80c3d680400c2d92180d0000300115424091100081261b05c114400d80781a251306903a81e064040f4141d851080342 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 35415553 1250 35414303 35414317
    0x806100518090109141605071403070501110301060f02071404020304020f090a020405010e060a350708160c030f05090604090612020102100c0c06020a0e0a0807051302030f060402 78
    0x70007080250840640c50381e0741c0c1e050013080e09001c00280000c141450402e0a04007a1000d003c229101800286071644801600c00c020707002088070901c000d00b41c1e060384c9540706244c0028211350900d822807401c0450344000d5030403285940c5600890212180080380c8a18142c00b80322820b83c0003c1d010181030601d940510b60091024003a45908424a0005850310b60121507510000790005130070320003564494000c00c00f00c01c044c1d410609004d0f100c18081e001108506500e082d00b803060244608a9180a6000b44220f000d24090b07040b50406200042c124ac000b100c9400203081450010001c980c4108850301d44150142e0f200140f202c14140221582d9004000a56000381c05100c041200006407203408018015409031085015041c4006410201c2e81d541c030a000e00d03c1d0000e00803c0b107400c07001c9150095800f0350016617603180580182c0c7d10300c141002d059081800e550022810440010700d10003592004c0f03c00c2203000240c1801042684000c4070100108004030780411402d0405401034016 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 35416803 1250 35415553 35415577
    0x403050d180c09021e1204020904171303030905011809181502090111060f040602070201031d0c010305090c0303070204020702061c0204030c0b040b09090901061e0f050108061005 78
    0x700011a0300c0c0e0000c0b03244250048006141d0020300002402c3c03040c00900c50032542c8012045c14907070100440c005440c4001c0002c0d0040c41181d0005007005000c2802c001600c20300300000c0e0b2502d98220000e01140480e010860101354900c13004038840d0b0041c80422050000300305401c041905000180303002d001ea030441c080d9600c3e406109140019a020021080b0f0b07621444016122a0000001005000c203001502e103a40c00103014013128207006110582d00035000f01015030380320540e00c0120010206401c40010b842050340da516202100800c102100680c240c2c0d082c429500d0751021180c60f030000800f020b90550082109000600b442d401810201d8001003a150401034501d00352411080b1b144030150409038009400d008100b000c100c211301402246039464142401c01440a19a114220b09584203248060006a40a00135040000a0300b41440c1e200616420146802c003001c016000e001101054400d001c0f5040d403260400520800e00205003503007003049800e00340c079190700c10000128 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 35418053 1250 35416803 35416841
    0x6031415030f01020406030203060301060909030207060e010e0d03030509060f06030703030e1801060503180d08010909060b04180302010b0f01080606070507050a0312030c03060302061c020702090c03010f08060403050d 95
    0x90202d020320250004250170f8501603501d2070701d88109421140b40d070304a180c0c8103207840c0385100481d40c00038903a03090f102e4600304080a1081c070b8006035000c14917405001d50004c07028410000301035250304924080d00001e0100e03091354680740c01c80b082c42901180c81d590154412101080404d10619013a92080000f525180c9001c452040c10400404240c00108c0441c1c0004140310246074203c00000e4100c0f224006040315142480004100060610802041c2500c230950721050180c130394081004144024010800440c0d8020441d0104844890640265203008415445418140150f40f00c0c031005075030704000ca554500401c181c58000400a4502c0c0c420008040380a440700c09028002d103002d621920b2540f094084003c05850010b60201c00709810000c00b007006032a840156100401e12403021201902140d00e402c009004103800690f1049030b50041c01560800c100046040c0c3d40341c40c56141009450380b4600c1e81e5020240c900800040003000724500d100341943c4802001421004010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 35419303 1250 35418053 35418073
    0xd020f0405010e090d09030302070e0405030913050a0b04021804020309070801140f0a0e063111041407020a080304020a0b0703030606020705030109030903060f090b0406020301030b010603141503 85
    0x40c0840ea426040001c200c54090103000c0b03403c0c010010f001c1449001d2030000c0903070342196802500c5841c0c83c401c01083d0001003011404100f0184260b4400d0300c0e01909680d010850548802c001d00700c01d0710700e1842e00745040800b2019050074002c80b5840c1005a00b04440400e4440a120095100a0040ca828084d800010482c1002030150717131701b0300e081c1741100740150500002080003120050301d600c24140c40c0c0301e005061810049099a0b1080d149000b03050303402d11400c41c210112070758001da10b08086101c0d03409001c114140100800c0c00100b0b50b000c1001d02030400300301c0171601c000c3d141345025901003140c14001410100c000c41d8810304c00790044030b210340d9681102d205900004c0084011035107c580512003a90704000402c001c0408a00074407a04c000c0f6100a040b05805000c041c20080e140e50955282401d02d07000b0030001079104054901030318250800c0c071b00030740081c0000c0340c0c1041c0000001a00521a000b80d0000f90024003007654a80c5030f009400c1008603048215981502462247e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 35420553 1250 35419303 35419309
    0x18050303070b1b0f030a0b090105100c03030e0d0206090114060607060506130e0d02010c02060615030c0f0307020312060a0b030f0709031b081c021e01090f06091b140d020f 75
    0x260040313803041200079840341040030700d51064801c80700000e030044d440300004001300da1720100c0401c80c0ea0441d0824152080d04e60408030301400021051650510800903480f50041e400a1618420301c0c030f4030001c21000503d400c1e4507111032000c2e600fa580c400e10511180020410540c4590f4105100901c2035840480755051071094030704c1c1c1c4035450404e40100c0400c00b101a02030050591901180c4082c00c800d01e014400501740d040030070710401210101100061003480c1175401c0341e1080c080244200d899162418000b95a913100d1000301c07100c917945001040260411010f44400e03604013148960840c1e8544000b41204030005114004000862034000086840b86410340035241c00d0707002e01c818140c140605240742040b803c8401e0040020f036445645002e50100e43c0039911000540a2080924a020401e015240032507000d8450305014501d002003001580c072059000344281c1520200889420140b0030f901c24611801c0d10038074940c4410b42e01c52070180242e15038144014420007100e9225804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 35421803 1250 35420553 35420557
    0x10b1b10060501080f040222150f051003021c0b03030d060e24030c0d02030f19120c11090a0f0603080702030c06030c0405220c0f18050303070b1b 64
    0xc03034195507548080034000303560300c84015607001c0ca050441c12264103040d8040344801403800120040d08800e10340307046494001e41c01a446c44400300341c40320220741d210032100f440c081091040303610400e43c2600088202e4020300a0340c42e54100401710180c5401c0403400c080140060700c03241645800100003001c07448000b4460368010b0f0076070f9010b400c250f1070140781040100d01c2c03190900301d0f01c8650004801075a84c0c0012101c44100c5c0039218200c01680a00c0842d1821441c086010441c1c0101e03840741541c980c01d00d440e01e254070b00030501e0000e050000d000c1034500f0911090003404004a428120b102410182d032200d070400404100011402001405001214200c0e0012600810002580000c0d403500304280c403070540088600900e141400c413035803076441c4513034424a070103020f18595900031404110a40070020141d0304c0d051107258114407000b03007442d581134250300208105240e1400da441100140400b5194007400941c0b07010b10740e89a04c82d1083c8000c0048807540039140503001e1020380000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 35423053 1250 35421803 35421823
    0xc031211031204020f03010b0d060b0f030307050d0906080421021603050a0218010513050a090f050c0a0e070f0e0a1a0304030f0503040206030106030203190e0a0b0c12010b1b 76
    0x10080b1424101481041a00d0300342440380c80c801d030f040243c13550446d500d401203801c000380d000748006507940081001c140e00c01b10807d212981808046201811b1110109011204000d03c0da0b40091082d2034034802d48044000740c4014040c1054001c45203008040d402d581841072041d40116031400c1000d50620314800c1c1240c004641580003481074804604044481c081c4010f1540d5801010798102800b10740015007101c1c00004164890004c14107080c45c5906c4035100c647c101c001c03081e5190300d0307040c020340d5070701a4000d1a008507a1348400042030000c03508036030301a180e165180e18206500040c01c0300c00f01ca0010000d03900a0750300c40001104e45046c20b04988000b42494041d40343e1034103040c0a414400301a4081041c01000c0040000683e101f4040b40c4c15103000d82001a01c0b901c0c0c4800c1d110050b0608054800010b2400940e000080000540880c62512810301034117981c0e01c8000302c0d111400b4060380262203030b12040044c0050400080640b84065484d4035288030603800764a82403505660b01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 35424303 1250 35423053 35423077
    0xb0307021501080a150509060c0d090b0c0301030b09070303140a0e0a09140c0708070210020a0204090803100602030702030a02010807120614010f030b15031503060406050a0b0306040c03121103 84
    0x110312005c100c200d500810107602d07000e40030445881d11840454a0b0f800050002d5070990000405c03240c014072a07805203074071b2500711032102130038a000c0400804d01e84c028081643d080c0c0c00c82d4001209864009000f406490f0300d551022810460305000d00b0003904961014800c0c8140801b0b800b583c2c2e12000400b80050401e01c102244680048145103103140c800703800c8546041081001d580400d11b20340c11100c145505807800449070100c010202d08007920034000a41c081d062180c1007040c0414a00a940030380460b0511140083d038510782070b40d503480f507800002e415401228103140550700860100e9400030441c01c0c498442e02400704440211502c5030000c0340c0f0400c40010303014165900040815000116080802c0040d40241c0081c08001404074069100d03100040010714809400040000c40b4501404803002c504051401a01a00c411600e11949515180229403146030006809000c0c941091030440c01d5130840e1282c442c0b55595404083c10301507103001c00c0908601c1000100702d031020f08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 35425553 1250 35424303 35424313
    0x506060405100303050a08071b050d080709030b0a11040e0f041a06060d0c05040b0d050613020301120807061104090e0d051305040b0d020301060b1c0908040b030702150108 75
    0x40000720340c805054210014840e140500c002500842160543c40c014103042243c0c0d690450300b11060b40eaa200900301d0321400040080402200061a90001c9495154070329560341e840360841c0d1240e01031002414480d01000030800b01c500540c4488a03000100510618150b16a503140300a00c4041e940c1035408840c6204010500405610b1800f070f0010302c3c2c0400d1420304140e8002000c0e401481c007003042541c0e40300010240c0c503001c0d100300c0700149051940c5a0b1100301490020008000848000340030366210000c5880d5444c41c1e01c21a13042e140342114064203803085031190706141d00480021500243c4d5041060040001c0f0400b0344011b05c16150003051400c007100b13169003041d05098a00d810311009200303484c4800701556a46082d15400e0700d0005800707041f40001201380344c4002010350154030301540400c0a00000303009100120324214680180b401d400640c1003150000d0074043d21140091000780666201c4100554221070a48100c54000b0762b2418100c2c4804801c4e880340001d6889 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 35426803 1250 35425553 35425561
    0x70801080c040b18130507060f02010506040203100b070302100906060602010c0f08240603040614011203090b07020f100201020a030b0d230708061005130903020c13020904090506 78
    0x42001040a11030042e2400c2c095010381c0800300e000030100080380b14407141c4207000100c0403010f1170603508038036400000720f0764a10b0740e81401601d0000d0380441c81005509200024015040c68002c03280103072050004401038a1900000c00800e400500f030032401c6000b02d0744201804040c90147e0340d5424015000010410310703005029084036220525603091040f107a40d620955a0050b41060340710301c0f1004401e0000c40358815880f031824807540c070682c2c024400300c18841400703103d0b405185102c0760103446001c00e98889041114030408000014000350020605011101581016081c1144046c02c403c04011004001801800703840c2e4003070005039400f0030109112549030182407a546401d480041d1200034036201e4407030490301403540d002800c0c2155461450880100808401019288150b5185081418100b016003900e4030802c4d114200e50b01701d503640491544201c40e40300e5499001403901405803802d0210071040c408407048200d500f80040201d030f03101c50040003203040c45000500340c0d501d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 35428053 1250 35426803 35426819
    0x80c01060602070513090b0a02130504150e07090e0403050f0706090b15120307060b010509090a0618050708060d17070f06180203060106030e16030302030d0f0209060403030c0f050303070801 83
    0x31119011111070f00305a611b402041c0100c80150f0403466584016a4070b0088100c0a03010b040b51b944010382007440c040f0400205101c590401b410b8030040e02030034181d516040c40403a100e440741d02a03400e032180c20782c0200b00000d01400052440140d5941241e080440c0f0781c6400c070880303c60800940f5491400810444021950740007217000138001c48804424641b04406566603000311400102502d6130390811050361380c00303541903840c1d1b1500180601c0759440c24500140c081d0a0900c507100010b00751185141001200d4002d49100314141d42d182c0d081ca031340d0f031020444881070500040c0d8814425641d0300d600180f11400514580f80100481c944808180c50700c00c040f80c1d21843e0725001030300808007880c0140c0d00801e080c0d0440e480e034030b070114203a1200d510300b071b05081303c00c41800c40111680030000100754020003e40342c2d804032070174100540e0480b14400020b0f03210741400f81c1d9001808120078400640102c0200c070400c0c0c02648809411001691820316640c01601d008003c9120302c001040406 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 35429303 1250 35428053 35428069
    0x20c12060406200d0f0b04110c0105060f010e090615040b0408070807060801122a03020f0405060109060c23011b0302040501080103140c030604030806030d0201061d04080c010606020705 81
    0x103152400420301940f14105401d80d0b40c05440d21100d09a030b01c41c44d190304000d000e5009255104401002003000140007944002141d000b20b081a4440d401d15000034214503140561080c08401a102d17081c01380c121804001410f080181200e5005400c038000340f1944418001800152541c0104d0f03a6446040c00b000314901080d070f90080c941603010301c1c002d2001640c803c034040d0464100c505003d45c442005d01d4054805200c0c0d02414001800740c0054580160201120b00102c0303000b6507000f0050704001041c0000d1f18012601640401c07500c07007040080d10b10641e410140140a66080c454021041020070814010703840009a1a03460707081c2c02c0100356051070f80c800c425a80c0e0400710f251610f014006001071105105c040c2c003652400550805000050025014001c4000c059880c940f5080c0360241140c1c2080e03440c24002c4c440c000a040211b401441a40240c0b0513841c0c061342e0303824141c0e0b04c510020300028021110540700b0f0194201e0707010240151405401103802802c1e4150070722003440104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 35430553 1250 35429303 35429321
    0x10120c091e1d0601050417010b01031a03060601080c0705030301121a07090902030711010507090906140112020c030c070303050403151404121e05070b0f010602030a05070201020c12060406 82
    0x4140041001c2180100b441400c80081c020003201e81416929080140c40c02d0095030b00203104030300500c0103851010010b42c00700c000e03010f00343c8080240e20f0412007026031502c28091019016030044010666543c0038400302580000f100d001a4030b4a40317640e840c141990000c0c1d005103403107607400d5014800c01406403220b03031505405240740d00f10340c134141d00020040b0075544109180d042d03000001c6000076105010003020302089000a000398201084014100da072644030741807180c0c1c900000861055024460b050001c84141d451404d00401c5154040007540400f40741d035841d06c0200884070f04081c040c000ca50045004e52243c1c0c0d00d0b5480c44c10210034005191040084640ca07108a1000d181c0c0031442e0f003500150002c2c041a60030307250060a591208100c0c01c1480c40e03400080303900c3e0956501400030040d981c402c01c40c0048641710340c042c090400c1d40070b014031405a001800150892803154000d4511140148100d600321511140492820010950031101e00d0f080a0b04000034449903004d04030744 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 35431659 1106 35430553 35430599
    0x3050f070803060f06040f05010813050607020a030f05030105010f080402010c1515140a0b13180905160b0d09050106090c1e03020f0910120c09 63
    0xc1d0390011120144501c072210410003203801d1002c1540c041714480706419400d03605000054803585801070458007280004103e4a0110b4001c00116028903110b8020f8006e50700c41d4140205005001558403043c05010001088240d902010280c20030b4042e1400c12041c0e00c407840100c41d81e01101001a106025400d54406603105550100614050480c0c25081042d030300c80b804002c80e010700c81c44039408607001c071080012070a103000900c044000303c4480d000ca43d858111703d5000d0202c030220a86170f80d030707101c0f1540104007081080c10341090981e0500783c802d80c9031000148036031240f10302541600c2d0300c41080e03904120007500142c0107090211024401302c005010014046030000940c0c02c440c51440d043c6a007003501a2080340c0d881d83d008001a880c00c002070f0306200380c41d01502c11446c00c0100c41e04c40500413a14034070500300e0080700c940d10f021185103820002414070403031441e8580c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 35251803 35431659 := by
  have h0 := BRFrame.cov_init 35251803
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35251803 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 35251803 ≤ n) (h2 : n < 35431659) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
