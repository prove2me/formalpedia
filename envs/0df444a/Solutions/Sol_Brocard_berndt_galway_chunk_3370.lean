-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3370
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:02.529991+00:00
-- url     : https://prove2.me/submissions/61066fe9-c721-4b22-b523-03a64e475614

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 605935251 ≤ n < 606115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 605936501 1250 605935251 605935261
    0x6020f10020406020a141005010b09122a01090f0608010e011401050306040911040f0203070f0305100e190f0b210a17070209190b0a0f0501080a021204050a020108 71
    0x3003030b481184125401a0301c900b0542d80032600000d200c40c11801041d0558200d16458007052007070300d8003a00009501c0900180c0c8140b1032500b024400d462503901005020b0300c00509031107254480c2c03038100c808207101c8850701c690708a0303200740d6656001c0d055400180502c0c50300d0f4000200250824013800d6014000e000002c070310702d04503421107071160205a480601d15501c410500c006400401c0003140c00c01c0c02d112881b00c082d500c0e8003421070042c400d1000180c0b00d1402800040071221203248400a040c42c08061002d01440f21500e401500d91007840c0c41c55a80b90250b9120138600780c50907240d102407502500084080036a0060740000004035001e014107504d001c80e209042030741d403016540a90019880400080e5814184000c58428001882c10006240c002c105500011a40e180d10692030030720030315214410b0704c200313a0080803e8402500403030078051400c0340c00c0220300919040c4041d90001407007900240c1c0441d81500803059850200d4202442d00d20780c3c4e00c074003120813404a01e00c100059 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 605937751 1250 605936501 605936533
    0x51e18040804030305090a1508041502040f030609080f0307020601080c090723250c080c06040905220b0915090309060702030a05010908030a0f061a03100f06020f 71
    0x1801141c00014142c5094a540d42c190350660045c4030854200c0c402200024103000c4010074a510020152104007540c6803a14103c0a1440d003940c1200b0124810b002c18044940da0814010650391311440004907500c06007400b400b50b020780c24000c00f81c1180042000610750380070500034100c41807c42150b150300710141c2001003143c0100c0701200058400700401c44240e08840c42d03c8000350a0b0300381d5600d0200d01d95908103144010813441014101c49000080401030700140350301c01400644060301408560b00005a514420f40c458a0321341900c40c1e000c2100601c101c00c4c20500704845140314070010b41c143c507110f032055108940300101340c0101c4002c001c010380030441301840703038940c080610f18108800041010030340200130181c0e090720443d804840051824460b030045d03079000d80100c5440c2d1418800314015070340300750190401a804c0090802540605040e4404414080c0c00300c10740766038410307880c40003c1069510404d08000c041000040f0580c011900307440410920090303e0b0300c441002851 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 605939001 1250 605937751 605937799
    0x611030702090a0518070b041403070b27040f090b060a0510050c01110a09080d02160315020904051503190f02190e1006110607090b0310051e 62
    0x690080b2034440052003644444c0d00c4964040409a1202c20b45507424412518094003500515072101e40010148004060140624440c0504600400003e410008030700c1e1140514060b10041c0d031840300f100c0001200344031a8418040000d8420040c4070601c285100141070b248005403828000040480d0039414024200c605031f4001810f49040100c092104544651101d030300303282c49542e074003021500c108800000b80701c3d1f801c40740c2d100401581440303940750501030000d5464041d54800d82c1d1101d02024000c0005003105d4205101c41032032603c40d0500c0000c1e210f004c02c2154007078500b504004d0400301040c6190041c0d4819011101c0300d964840d2505104107280d100030f08141304031b00c80c990061509a5002e100a0364903045035071085c1d076a500c0c440300f0000c03d9480341a0f494607040240441031340105017170403e0f45400010206030810f05800742c403140c190300806c044840000000348005c205c10880c0401041c000d00095031080d02d40319203424280070310882501c110400440c09410607216400e07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 605940251 1250 605939001 605939003
    0x1e0b060402070512030c07020910030209130b011e0b1210050315010306051806010308030109111602011d062b2705190b0a05060a0b070602030a060b04080706110307 72
    0x1400e409004004c1c461040e00001d0540c3c1807503204124800040c0c40701c041d01030050880414401306681984100f00074443d00034060403140008a8102e408204e08000c2d441c1164881c403029180d03012900d21310303020856140c121030101e081c0043e86400000320140c041780b00740c40c04e0f200142080c1e21102019100d03a600f403029503222900e074005001060b1310b90302281d000103076440314101c040c0c003225007642801e000764000d403002d0001100411007103040380552081e029101134a907140c259000440e031110a5100b038060b0410000b1112109480481107004050703034030040c0f125440c2c580c0c1700d843c01070404841100e100d4100d040a42484050501c0c0200c40d28262040d6030301248410941d035507218405080400d0b80c3d1485008921281d441c140c488050171035009800141080ca05900003400307503000070386503e0140017801410002852124280c1c1c0b07406034014000360380c07070f259404000090f0416400c0000007010009000031900d000007000381c2102e1a5890380045900c40a8090b40c480c00b500b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 605941501 1250 605940251 605940253
    0x150527060f01051c0204030b010602100b030c09010608070c06060f081e030708071e0b061905031011121608010f0f030f0f05010f1508030309070b090d1e0b0604020705 73
    0x1040d05005012124011907400704d080340181003503907030f48407908141740030f0f4004e0000d80c0103000c5607298460340340105c2024003003d80c010400000c040b404a4600c040522525040103940d41c0407a1040c1d10411140090541140090000035122181100e10001d42c0c4594119403149d0081c119040e07440c0d010701d403200880003000d1801e000c0c0640fa880c60341e904c03005040b101344880d0036100403240104084400e440e401421404680d103448070902c05561042038a0183d544c6c0c0b080300800881e5000141001e808144600c04102c58908103203004080c06041c241d0800a202001001300c4c16100b0a407282404d443c5035941d040c40e9036994940002c46140d80100c0d944010301c02418030114210450728444030b84260100701d000c02c21501d965086403114200a03426580f0341800f806544c00241c0f0f81c070007400d4108007071860340c20041c0b0007540c0c80c0c40c58440e0410007000411140c0d000e6903564942041d4603082110007103a40700300c1c18044030b40045800200c0b1045030510228086040c10300c01d40785940d43c410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 605942751 1250 605941501 605941507
    0x503030a09150501080601051201050f0601140717030703050f0c07080f04080619150509040f050a0b0c07060c05070807020d170f030405010c02010b0d06150527060f0105 74
    0x144a04000e01450401910000c0e050081240480c0350b80c414107000305100030141181d0f5040c20100080300d40c03081c92842d0141c1c1070000380f00160044d0701400c1c2c0c11074803d080c1800028010b4000c000c0f05c2c000c42d01c010741000d15040c14025000301c0c1e1002036108080702d03942000702d5075484941000703100f000d9940103c0407405101400c00114110018010781c074203c40c41c50306156a03448074030b00c0c0003c1182c01100c460701c5d107844100c14001e00c1c052901e541540289035002c060a140c04a4000f140c0204080c2800d501c1601c0070090000501405c0303495908444002c1040c0f030100503032070059000c0c000c2115060f180400d95441c1a104e2010740e10800d9200d8502d61500d441a0200400c18410000c00d84143d02e0054001041c40b0451000f0140221000302407600d038034081c00c5c22421a070b9003600010035a410050403c8a81d92000460000d55600110014a025281044a40788001078011039000350881103010008507417580c04940b0509494a00c80c41c680d211403c2c0085a1031081c50507000c00c02c24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 605944001 1250 605942751 605942761
    0x2a0913021e130906170f06070c0209190903020d1d010c02011107170106030309090c051e43020a170a060204150f0504081207140106061e0c050303 64
    0x39001407100b220b0b402c0c00d01905503164424042204c003268840b4201412802008980940a116041041c82d5075000303442546800d0501070202420380780000d20400c2e1500c00510850100d2940d5502194402410080742a03185806517851070b81c0013004010920b912200141010051400c000320a01030350303010b04100c40c0c5d50040d44e140707502c61803118160140c02400300d0000c200b03a201151503440c2800100f401490742c203000d031810b095500b02000e201c4c141485c2c1c035003540c0c10000700d07031a1040b00c540520310841c06c501d903424240520f1120103e080059080e40022071510541c8034410084800e03503402440110440c0303c0f0801780c500c0e00941100504000300881c0c0681c90300842c400c1b010005540d01466a992018101d9105400c003d1040c0190090183d480b0b80c48644840032401c00e04086141c582800300312640c1d40d1608400e204021390004e01d610400403442c1c203174180203a016000b4465640c45010241889a8003c00501011645030564001610910002da581500724000c4c601e59110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 605945251 1250 605944001 605944057
    0x10603050a080703091a0f0702030a060c0e100207080d0507020312070609020906010302031302010503100e10150503010b18150d0c0f1d0d020f130605090a1e052a091302 74
    0x2108d090303a0500038140c440000c114607000e0000325104643d20101003900c69410003d031512400220360441d401044144484c200015030202c880c0b20504100f03880780c1c540d100092500e034180f040101403030804902c0c0c074108046034204e0f50209100300c807000c2031030707983d00c00440882c0011282400c840500c400d0040255008000454008110200d02000c0d9516441c9080708802e00380c45482092440050412401944007003000d0210306c2460014070310752510b13018000070700615240150051440100440b59a94202c80e00c07981c59040b4041a1114142c1c06a071b4020000c013544500480c814441139416a882001c0c04450a0250b5910425040141d01841801c200c002000c9801101044000c10035075a404540c42d02c8140b03410000c14050b06000074800d007404040e00364190300d800d0049281e15601501401603003c51010400205a9518a070500c8000081503050351040d00001100034054040402880d0b8098151001801200d440305420b0403481640d0000205c80d450498890541340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 605946501 1250 605945251 605945257
    0x160807180b2116180501091e0c0302090907020102090f0a0521190c0807080d080f07030609060902090a0f0f0b210f1501030c021c02010603050a080703091a0f 69
    0x10704003c640860155244200b40c8555035002418911021002024400c410b8000c05003d007041800510003403034060b02c0d00c412003e0b00e08000340711544031415807000500c01d40c160340c05244001c3c5004001c1c1403440c00139000b98040d5080a00601400305000381c0743c1000000c403811100302402e2a40008034880d40100905007501201440d0b0040000380203900c084500e10190460141001003031091030101f500e480c0c181c40354840c62158018903000085150481340c060f070700c40c103203221410703c5a40d03208089000348855000442502d20300000451040c0c1d180d400ba200f250015140d0243d1241c4400660643e06e405104903014050312401c280001a181030107000c0c50b01c0781c259044610140340587d1070400004407009800c11000030704200810303600b0281c904600e0801c1c00c0030008541e820f40000c1d1107405c2c00e61000d207003444074071082c060030380b003540001c00658004065518030111403404125a0340304034810f80010300000c4020075a040046a9003080301500300106141ca0b424000d405480d070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 605947751 1250 605946501 605946559
    0x91a011407060605061222050309010c051f0204140105180f0a0f08030a09050402070f1205070503031602061e04020103050408040320040c030b0120160807180b 70
    0xc3c0c4483c80080e603926400017800080c2e000c030052050514100041036801e003010341c00c0c0c8401100f002802408a00c000c012102201801c1c6045c100c107016a06141d07113031520a458080110010900303100155520394003a100351006008000c040e007500301300454807800780c800c44c440002150503000c0458034003d03100c500040f1300940704a5000c0d03130301c0350090240c21480e030168510760000103d02c400e0b00d80c8081c03084003800342100c0842c240220747c1c88001c172081d01d5020007451034001c5219a8805c40c01401900d180d55482803c8955901d491108000303801340e9100150058458200425511814042118182c074903000c1d103140300380c0e62a00114050403000c0c0055808241c1080040041056003c1e406c0007284021640c6070032201001c144030881d4000016542010304d40310040c035003a030740904c0f4440307118030151401d2101c10880e0406420801d441c05080901c5040c520002485d00000c00c01c101140c11105082003182e0004299109841c40030407007650005400c140c1c081340c0c440403054080a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 605949001 1250 605947751 605947763
    0x50702010b120a03030b18040f0804150908010501060e01021216020d0b060f09090718110301230301020a09060f090b0a0c0b0603030a0c0f1a0709091a011407 69
    0x1070603206000c146080000c40300c6004682040104805150b01800307400141c101c00c0d10f04515000031100d2189003038801a10003050001e18060203c1400b0748102694068290f40d1007100c10b1305400e04000d0850f507000d206031200d42d403c00000041d0240a03285d40c08002206130081c10814201c2c01c0301000365403100762500703040502d60403c038026844454050304c0c058401c042120881c00e019040110741d8150380b0010340300710a00401c00901e1900410480212a504a420030b5254220600c481c044c0028100b01a84c64102100028010010200810080000a14004007890301406140c240c0c802c400c0128045000720344200b0070f0a00c140703035649441080b441c2c820300301c94480045400642c8500200b0b030000e0f441c00d1001081c008510105a008a012002145441d03603d2001407d040440d0360090164842c61103504184199966440e4078402c59005200d1a4030340707410040c1107180140600c00b15a4a00342c590914442c142d1040302038403d0503120f54402004014644200d940503000490f61 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 605950251 1250 605949001 605949011
    0x507020a09050f072706080106170c0a1b06051609170312180d0203030603011515200106060f110307031409040906060e15090f0106030f0209060d090309091401050405070201 76
    0x80e4100d403c0c00ca1000d4005680c400ca1f0552400000800012040200600740d4480005210000c94840d080b13030704018240c00c00341c00d0b0350851070404040b4021900082c25a03401c040810152160540165081505580f00d80c418240c45400c01c0d5200310401074400c2440d4401c00c500d88a6110400f00307503030b102101003260060040306c44001814040f50862702c902507070000c010301201c1e190a020b491600c1c0c0c8420441c8511500c1d042601c001c1c610004240c809100f0030300f00321480700d0b02c0d4007000c01542800800900c4155610307200200b40d416408460030000781846c0c944440040c0100c02c0340d850319056502d6440c152070f5940e003c0c01c164800134040e0741c00f44d5940744c24000515a402010010952540c0f044c41528000d0002200300c00280403580c41002c001c070421210b000f50041550564005140c005109604040071400905c0752041c01070f0b10040c08911410382000c1070f0003c0070554443d41d81e01800390b41e0f400c00340b81600c0b000d05a03940c100301c2c0da80050215040c560302140d8018498400414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 605951501 1250 605950251 605950307
    0x11150c0a05010b030f210c0f0a030c05010b0603010b030403140c010c020106150206041205071704081b03011b11010914030a0f090e01150201090b070507020a09050f07 73
    0x454090903220071105a51101440c1c03000349024010300c08111400c0010b44090300d8601a40106002080c002c03200d95800400c4070640ea4000b080140c1d540c0b02c50204445107035034241005000c810464008075140d40c20488030b600e40e82450307026030f4121040507202134156107a958013660010540000004040340600c011a075a503800d00800c3c0c6c140800da000010010304140c2c500c0605d0003407030f9085056511039028440001e0b407811860b641301e420351810980b9401c09280604541304410349a0b40001c402140110b50140c0c08a2541e0804a90404ca5001769910200341403d88008900d0a41c441d069102c003a00c54034061012480c0d2100300700000200b240003a52200410340d2030006440c0541d001154100c881c6030412402040341c103150922140940c03420300900c0c2200814003d60302d98a04210301404a94000d4202003800d80d402544502646400d51004200303802000042c0c1c8510041d14000800326400e214443c0a200d102d0b090724034941d20f03403509442c5042c403c86503080c40300446014a07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 605952751 1250 605951501 605951503
    0x2010e0f0d0b100602100b180705070f060e0105091b060d15140306090601050a060e03161517040c1e0902030114101107180b0d080909100311150c 64
    0x1803150381941a03c01d820b0741001e03802407501100030280441d0754a13084402c40d55a9400003180c03013020070b071166480301d81c0e6940030885042c007650744018032174140e007040201041881c1e00541d40c0c0612080c000c00c0140e442d290400e54494004080701410503144001d210306050040c001c11800403c00004078003000c4803811003440040380c0d070100c0c60030f814190501003507107001e201c45030704460b8a00c014201541040300040c00010b440c800c800c14090030f001c00075803d8800740803241d040440e00103803000140e40c814280d0500400c4200c03000000320f40c034444003910245900390310300070b54014842841d002d0a110102110354070034a6144603030850420001040c021600055010b4011a83d500039442c101c04280480d6001e003400c800d040c45000c0090b6502d50328001600e5088030340c907a04603a481c26041201d00004d0503200344c1b49401c04100c0e20007805006400c0014101c12805407166411680c03102c41101401d071030b0340001012800e00c5c2417074111928081c01061042c04140b03038007903d00100c000c451 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 605954001 1250 605952751 605952773
    0xd060b040e060913080301050915030f0717070620070b030703140f0603101508070b031006020c030304090f140708091612060203040f0807050709051302010e0f0d 71
    0x4003208111041c100262400e2010086410818010729211504c42c0c540c2c49144034041401001e01032a00540080c07007040c40c44040d00b030078001c05015160b6541041e803415440705480d000300f030f0a41c80007040c42e01c420203000911310f08407002969000000300c0942140141280341d4105e003500c0d0710a0140114116011200440c051007403070f05e00291072000c8400b01c03c0d0180c0f00601c0d4050020723100e01080070944004c07800c2d07611404241000500d00301045c41d18014245a9004034001c1e00c120640810740d00c05880c003c600541c18046075170001a913170502240e456040000141c1c0582040c0400c0046060940180440d0b14802c01c0120b4582194452030001e20300403124480041c8003c0c05009406200f030124910506000311803694079400c1c02540c090407421004010107442e400400603080c0100662034401d200c0c0d06c02c54082d41d0301c640d030030a181e403000c050140c01c040c0c1d490080410780c3c6d0070603100c0902c42194103840e9208004142801c100a010625094640004400c1049000030380300ba10030f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 605955251 1250 605954001 605954009
    0xe0f031b0c181006180302040203330310090c03031209150207031808060123182706010b22030302030a0906050405060909092107110f150d060b04 64
    0x20041961074600080f078030f0300310964000010301c20380812400d082c1440414040c1a80c0d0140c9005d652501c42c5c00100c04a0040c0e6940d1405c000400e0a80b141c0a42d0855403000303260300200c0c101c600002c0d50207101001c4403604ca400509540b195501000005d00880c4801d0001803c0d017000596600d145c2c441044100f61992045207640e40047e01a08140c1c0000c2c603090070700c9000301e480008030704044c0050f03503c904c107009560000c030034803405413900010040c0c42c145020015200300f0080300410503004010900b62400c099007120074050f80c050380361f03000800a0314140c090003040c0d507900c0c10405032544c0d4070032115542c420f6601c400c07034581a00e45542d05401584258002d40d0344e800800c40041c4590b0090b0041e070100708082001304956520801030b81e078054000c071495451911811a294600746200c0414000b6100c0114058071170341c54100075058880c003c01e5000080a10762041203904811035005541c095204030700b010210a5000107000d10f007110960002c0c0301521000c4402d903581041d84 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 605956501 1250 605955251 605955289
    0xa060e060105120109030207180e071514070f0b0c0403050105090708010509030c1213151d06030f04030e01090f030f0507140a030b04020d020a14040e0f031b0c 70
    0x200400090820301c50304680f0110160003004042c40507030b002500c4245038450340000580110340e100004807651b006003001c411031402c0719049a40c60541c0e20422080d2001070307010440e021100c41181e403c1c40c040f2902e0740e5100043c2e070141046952400c00c0e00e0790140070740ba41d6801c10320010000032824481e0a00035400c090040010320724018405095810003011544550804d2040d641a8403002a05800202450703203903a0300c8041d800c09205101c011540a100c0b440583e0051740d15180c0c2044565003241c0b40040400d54050200341880700501c0151001c07031419480c1c13000140401e10803c1a803501c84014500040c40030390340c41c1007020000180d00706450001120102a0401a0810900c4000c102c0d541f0742c003a10b070044000282c0007486030720005d8010f202e0400010111f41d1413900c005a91030b40200301000da00d4036900c0e036047e51020046010b009a1030001500780380640024001c2c600d240c0b81004601c0c044840b10411310408010a40d06118440c10f0440e8040d80e59440385c80d01c0d0198441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 605957751 1250 605956501 605956513
    0x1c050703090b07030e070b160c060c170403030504050402160525080607020304060c031b031115010b041e0b03070e18060604093902070b120a0507020a060e 68
    0x414110400b101c007a0184080c54603140c0345461070840030035198100c0703242c0d400c801d440320740050781d1213600f0a080e4401000f030b001c1700c40040b481d241c01c00b15008540e0b0080b0744c0380103400d4410244044a101e50301020f0040742003800104030505d0a074000b4040070503400380c4014401c2103950741a2500c030024490408402c000c00381102c40c80c0550008100611a6170300410182c14184400f03902d921403406164204100c4011805c1498001c10110800c1541e801c2c16001c09002ca04000b4007170304030800b40c840d01d80201d298000b15007043d1910381341030741e031441c1815140c149802c5032503440115080c4143d4801d070300804000340c90b0b0500300c061442040c0c551102401c2c42e003103500b0003a004180d2022400c0c0c1c2c4c00e01405011646d1070798001c2e14140d4880d80d070001071941c0d510010b04039000345507450581c003440342292904070301602030006800324580d8080701c2c40359484201c048242d024011305a40499440d400045018801c0c0e0001c541007460740c015034100c5a00ca486a80c1900c20b500402103aa034031407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 605959001 1250 605957751 605957753
    0xb030615010e0a290c121b03092d04050f0f060a06170a090f0c090c020102040821041e030b0a050c0d09050c041515030612081c05070309 60
    0x442d1a03030300c5400040340c0202c401414500100d1a02c4140b248114422040000c0702041c014018125014203500e2011614003038459804180036500c542c4500c5003002c9215049184810004240d48103100024042c0c0e41c05201181105500009100c800700503054080c100303001600d0f548030341d601440f44048142c03c01d21380031444040f8440c0281c01c09000c1e43e450001040541d80c000c0304124245512591141d040d1290a2224054405004043c142c00d00500e005d200b0001c41598200031619201002d000d41000e108060b4200e0040e803040c2059a0803c1e500d903080c15051a840a0303250500723a00d01307070404e5107668107030069900100000400303400030001401800005144580e00000301030080c0014540180140100c4c094004002d91003600d0742d0000c010494140121080020003800820540200110b84401e20506100e01c41094441d802c032031079035a20900034038003078400034114092010255a00c124480c0e10400c50030040402034002c2e890589150b0050078054201d9a5020800011b0703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 605960251 1250 605959001 605959007
    0xe030c1018261c1b0b090c010e03120708070602131d0a02090a090f090b09030702010809030f1912021308060618070c060b030a03180e0f06090405010b03061501 70
    0x740307054034043d91200c0d00400300c03040d51a400007030b00c0d4550315041c01c05201c107081012018141c1c04000b001401a0700420a4100d000103011405610903601c0c0c0346662920014540c41e07910420800b040d0110404c20400401c07c440b000f09600e03031040f10300500e008440711201c008060700b50451074401c03a111b03804401c100c210703030b0501c0c0d003001c1c0820003189060740300b00c00076051040e1841107074101d50700c0c0e00c1704007000e041c00d03403180e1525030f0040c3e00400c3c1d43c60158030744c0b82c61f83e002080803804149008041020801e001094a200425090b5500d180c03021032442c0141d49456452491b0030003080403211542112a030000c4c0c02491250300b400107800307042c8040c5504008005000394091050001e20125001c2544403460f00100ca90401210740c1c2c120781803007009480107080036605803080440314020154442014500320400b8a055800b4944614514a03410401d442d2981074a6002000c0f6601d854811030481d00700c0d205e0800090f01c80444070110707081c00000c43c1c1c8a80759400033702040d4201d50b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 605961501 1250 605960251 605960309
    0x16030f020306090313090e0102070c0306050907081b0103150b070501050411011b0219050d080307020706080f0f060a0305010c080a0c020a050714060f18030d0e030c1018 74
    0x1d4598013550801c401041c8911580c07101d0f21030710100907114070070844841400c0d411180059003001c0d040003100e440341480005420141c0302402248107072036001032442000b01380f00301c021142c2c400e040c0703100b912a001103005c1c2c00441c0c800a01c00201c0e40700058203e002d88000c01c19140f288001107500d1506007400780060001d05019418004400d0300302408215a606180300381d941125403102d00e80111086810b512200d40065400c0107845442c4400c0c004200050b5208840340e5013150044d035107400b401c03074400006a4118070801c02c00c0c8042041c1e4064502140c0e4400405040780c041031303a89032505800d41301d15201000100d04450144884d440c002d004005103200180028021401c50303135200c5070340343d409100d107003810341a030401d140710b81d507403002260300d049610039042c0d40301c403403568495010785038601e4598032911600d030a5824032405000c0c00f0b4200c00c1e009028003248410700b000d01850300b01103070800007040741c83ca05d82136401411007824405080024244c00b09541d031808442c0d83d240d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 605962751 1250 605961501 605961511
    0x2011a011707030c11010609020d0609090201122a0e041526010b100f09090504020d08090f060c071d090c010c1113381216030f020306 59
    0x70a6102840518140c03014240350040c6003860b00103411307080342408641c4001848a8040c080d4204640068403a1254001d04014400130004010321992030344040c0481d940d0340c3d8000e0124060061304a1181083d5001040403d48900801d441482101c18803018034012205840403541d1031480703440324240341c41181600b070304620114209070b040c41c03075a0b1212082c0140ba000c005c0803020800060060a4011a0074150003074036040e1406881d00c5d002c2d104032442244480001e00d1034100049034030207401214020b64001c0c141071a090100d40f1014441d9000d040c01680110341550020210340b1048001e09115220070041c00c003a034200705428000107820340d0301c008040da07590b0900440440100d01941011400d080c140302500052030222296060922090345c004805515040504115040080f140026040322094110b4100300c05542c00c0b0707401030341c0c0341c48242c20342e2003202c0f0f0610009c4a0b20048214040756480308508120070251003258104a40000070302030380070110708041041c03907085 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 605964001 1250 605962751 605962757
    0x50709051e06010203160c1a1b0d0509060d090f06020a200601120302070305010f060e0105032406010c0209090307060b01020a0b15010504090c1107090216080706150602011a01 77
    0x40c02c0c41e000003550b80c02184e82c1c105201d8a110b0800c010006458410002030410b100685007a0043c14440c00c2150003074060300da2409009a420440984081000081c0c0c10309500c4544c24400108240583c0d90400111340c46500e1341c5120100116543c0300450207114494007001d6134481841c58001c02606184d42000e05c510b80454a5414074040030600743d065070b01040340f0a404503420f0408a10305520b0340d00240030b6519204000500c0c041d40e40041c07080d51104000031846990351024140c2d030b4000e280710034041d02012521f0075003541c49a405c10b80c0061052404aaa40030280c0000d41304130400d86190702545e200142ca0300c20032615000351303004248240060461009251a0b030918060003d051180301c29154495881c282e001e101900d014183c1390504100c01090f0b10000b40a00d27900c1c1c0c900c000c1c20701c2045400561800207000b19034030144054419210500e466844490300d40001c0004c80d80a45c507514541d42c4000c0c01c9182500400903640085168035100b920441165078050000d410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 605965251 1250 605964001 605964061
    0xb030307020919110c0703050c060f0a111e0f0c090402090103060e0312091f02030106020c090c040b0f250308041b030215070302060a021e1605070905 66
    0x75948044080d6442040021204000f00c100300340315000b400e10b119040501c40e000300364450b20120008164007501c3c8514203c84200d800c9404002d02405084404a00010b041220a54941c45021703000a0396908030100c03010304400d9805100342c440381000c01440c540c8140d03180b070780f85041040080401e180955a400389400c10313030007149040d641400050105507c0d1041c2e4041c1800400c1110048107094060715824103203469032640b1440c803210016500040c10140d829101141d1088904856080e0001c3c0001d1040d01c0078080482002428031461010500000407201d00103801020881001e850344c540c0d0f007250500580c80c00420f1b400901e8401c0448505000094101162503003140d0050030400400d10f200040390610000354000941001d0010035283e05031040e0f03806070400c60f2094080d00c0455850070300040c00c9001f603400001039441410444d0b01314045001c02403102820900c98281000c807540c80b418582401d0390310444605950f08108040b200d494048940000588012904 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 605966501 1250 605965251 605965253
    0xa02090a0b0c0a0b0109050f0603010506031b0105040302061207110d0e1e0d0b18060f010308071b060903060b09060f13020903013b030304030f09050405041202010b030307 75
    0x9012264014246020700c0040c01800800341088103400f0954401688211581c44a9815001d040151038200300d100860001c91003624060103120300c0344001030020007641ca291424220494100303d411818018108004009612508010001c03020354052001803420f101c0700c014080c6e0083e80702609a50000605940225030200c4684490081120f41c1c03c18141200318036a12a5450020150b000032400c0d0200308200030982514032a10a5140c9a8190508064244d40704c00044554440345052000144002040c1c1070281002c5070094400413510403840011801c4440c4a4000d040032070b80425040081200740d004040c6414001d40d1092a075051410100d54007010004546205007000c3d810390b010480e1543c141e03001500d004000307000300101804010800010740c0303000030100a80d03890700052289903180c0c040c111050b02c40118a55651901c0c01c031420340da80d02e1202c00704401e1110000e52981d41e409054001c070f001d59840c400c00501d002e0041c0c00c58032682d200c10f019400c2408040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 605967751 1250 605966501 605966509
    0xc12030c060c131e03120e0307050409061d0606031009110f03013c060b03010306152402060702070503030412021804030903050c060909061c170a080a0209 68
    0x282e084642c1580c0262903515820b551869030303070642c200c45904c0410220500b0913030b540c0c03d0104103d81c090703604180e5250102004459003c80200b2141d01680040c10400203818035900014802d80120f4001404100c0c1540400101100295003000d0b0380c4500c1c01c0c06001e14042c00f004002e000c200c00100000c820550721a0501d4112504840c4100102e403002c4185860030740200100c80c40599060f505c49520b40080d141b02c0034050008030300c007081182d00100b00941d500ca100280d40f8481c1c007260440e8038564070b101c00707450112907c200c5884813610000d10100d2591014040703424020b24080c080068480092825800411050031036001190400440e00d02004170340580c2d07103400300e50320b0120503800851a00d041c00301c01480820403000402050507484101c2c2000ea030300c60b1060381c400c0c00000c003c10605004078840340750303c00190350109a40303142102039041c04402ca0000c02c1c12260320b82e2900290406090081c0f42d44003800542030030f00760390200d891680600101401c500f8034410300085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 605969001 1250 605967751 605967763
    0xc09020a08270607020d0e120a0813030b0f0105010e180c0d09170c0f010e07090b2419031119021005040c0f080105061f200c12030c 58
    0x800b48400442c4111491100442d25060140d03400c036485424400d02c029500d40c4190302040000d43c0010481d40ca80c5049007184880303030714480c001c0004811903141c2c45141c1c1d0240620300804072085000100027094a14000c0c031414200f2884039983d072400001600500514640354800c121003090f90b0503801010345441d8101c140101c00c680c82d0303410713103049034020300ca498006094401099040145005400000c01c6c0d48059001981c10a140b4180054280c415004040c0031a400083c014803500c1c1c5240d000040f40d42c001401080010100e0708807405074840f9180311406030000240c00240989401d5201c240000c55140130440d10300c074010901c419000700303142c088202041562000d0083e2007080802c1c100d01c0306800030002d605061821581d07543d518070600c60000918174002410020620401d40f0882c00601001c4880059913980070709009513903100020b1100078218030011440c011342460240c0c900600402d90741400804000004c84c140d0201103040d0310070810500b4002e404078107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 605970251 1250 605969001 605969011
    0xb01030b0a090203030310031406010b12040303060e04031709030a0c0f02060405032415030c1003110a080109050c0a0f0503060d020603040501050f0c16030e030106031e0c09020a08 79
    0x359555600c4101c8404060075082c0406580f40c8008002d20031308007603c2e42c42c0da044038810350709401d00300002d052250300d6410911400100b2032082c0250060084848280e980c8503219140000300300d40c0f91440c01c03840040648040d000549414031002880c181c512a81e41c12440f0039000f1410120340200c02040502c401034020031031102891003208540310682502c010700310007019108001d4004040c4001e01100d03060852244148102155050124521f050118203010b0060492000d002c414450f050020340c6030903041507903419410010040d00009441c10303d416070380308001545003a00c80c90940340080c2009032082c00070130003041400d030810304024800d86541062a00c4e642c4c3d41d40000c203501d20408020350040c1001081000b00103042d880644902401c0c0e64008243c1c0f02c591408805000d01090309445080307030408c600c08079000d49258140b0792001000891056129560046402c0c0c5840d00300c580085001d00c10020461503a002a000d41086001182001c0b4480c20041a8041c0500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 605971501 1250 605970251 605970263
    0x110607050c0c06130e040b040302010506040b28081c0201060b1911010b15030f1806190e070b07150b01051b0a020916090f0b0301170703140a0b010b070b0103 69
    0x141c2c000610b480e011300034004203850340010640d49007500f010001074404a0703046005518020000d0880e107400e10800c290120050058203101c640b11910700744e5503032413481d14050318411080004003240c0c10803214508405640d0441310042900402a085d10110303080031340c1c0014244600640c8041e8040c0300403a0511b02d18101c2c5a40022000701e50052031800d1255801c0b074108846071130503007103800046000c0d14906010f548641e9440c55081c04080c080350080300d80703400c50b071b0210b105c0080303202500c40d0104821034000f4501c1217400446103400e400d54040c002e41103001c1800402e00c228818507030700c0b0400340e020174841c0b01d00c1080020482d100714881d4000300003441c00e60342003060003008840d46060340500004610b05107104040d00312485000c40d80c0002c2d00c040c00101c0c00c0710f107088081c0c0450303580ba240507065908100c00100300e001643d100007413900c038800d8008049244d40318020780000749200134050060b600c0c1080d02d05404141c1040340c1e2544104403440000e1403000003281180d070005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 605972751 1250 605971501 605971507
    0xf18020306060408070608010302131e0c0504090e06180610061805061b0c010311070b0612030f03040b010f0602030901031512141e060f04020d060606110607050c0c06 73
    0x1000070040d00864221044501c104030780441c0c6c151b00b01020906882c000c95030341c6440c9420210810030713510541400318000d016000340350401c40d03075504049288a8181095170806840c5c0a04e00c049444244051100303a101200713000c0c0c1c0b1800c092440c0c400074031100141190780380844080b0342042443c400c03030b01082090380e0542c21042c50041480003901c40181002d0340d41e080c600505404910f8010400064080c0c1030ba2aa400d40c007d20850300e4400c1340801e1325060204544400014001c028551a082250401d0002c106101840100440116804030795200d081c0790902d035000010507002907050718a1040d003400034940000070b81740782d050246004240000b48407041c0c01169495405003854403100e46041c02001400320450309038011200440e200020481807807020220b070300585c0c040d41e030030060104506426280402da40580083c0c50307102c41c042c45a484500300e8100d03a001c08005808a84036807e0000d0034400d02e038010380b26280c5182000c140300007864942603070000e10ba200d50400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 605974001 1250 605972751 605972761
    0x2190906170703021b0d0e010302040f0e100b07031814060409020d0e1e0c030a020d0b07020304030f060207050105090c1003020901090504020a050307090b0301150305090a0203010f150f180203 84
    0x9030121000c203d410416191241400c41071075540d800206c2c2040085418410162038951003407081d0740072103200c0381c1044015490711540303540c2100701a10840b242041d0083c086003910b9400b00a003c07051180c0d56001903100004080d10340345950f0b410004454180020101c101c0e0b4a0380d068a080d25038006005030f445020740c406800030089800358450f02d02408507d6815031b013600000d040542080c500b0f072401d5061a030101030326540341100080d8800c1a10000d18080b4200c0d6048950000e030070300446e40b90a480e0389491141d801150400c4030010780001e040301c100030081c042c650708454090028004002c02100142e01e2442101242c010503501041c112116031180000c80004d00f0041d100b15994204044020040d41c41201c0e000041000070034001001c01740e42040b070b812500c41c401c110503000c207117190450280c40302030581c4056204201000c009664284107546000c3c00c2d01000103203c20400d01010030104191780080482c0310104420042840d54a0200c40700111803500143c0d25a61 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 605975251 1250 605974001 605974007
    0xa1d01061b0210110d02030f0f0a0c0c0b0711030a0308060f04091b0906060507050c01030c0c06021303140114040f0f0c03080306150403260f0d021909061707 69
    0x84007001e03511000c50010a060300b500091020403442040084e00d00781159010b0590b034910a0b14681d285140040255241150662000d0b0105031401d01c0d1042d0310b040d03a500d45404e0402c65401650080000081c62010803016101c2900034450a50207041c000d072241c0c5001d0901c0b00020001c074020303034449401140c1c0f41d07580d40c130600c64a540f040982030300a000c5001c0c0304000d0301074003e10112501d0444045500380c001c130f0a6409003548100103244c0010358100450140902c141c3d04400e1001103c4103d001480034005000706401381e45d0806106444c5041005000c002e500b10b0510f583d01d0074081501e900480703103c0c0c0b940702d900074152400f0076905140040c1c3c21001264064620800418048100042c2c44025030044008032003402900039140c3c20208030b84224480240000c10000d000056070002c51049101c0380c580008490902c4108000c5400603480450304030000c0358001241d1140c01078642c69203030f140c10940b40c4003000c4c908001002d4414211030540c00030740c09100c0002080c170380c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 605976501 1250 605975251 605975297
    0x20c090405031b15010807030c03170904180501060905010b04030f02030316080d14070f1112040b120a0b0f0105161a060111060411040e030d05010807050a1d0106 71
    0xf0701c60341c484810740c1c40400d82c136228008035032180c0c410301185000061b80035000840d0b100b900d4010741a000303100d14664544a41711208104204442c2050012004a64441c8150383c29056001c5c045038290803035150840c2194003940007801520720346070040c045040c0910644041e240c1c002c40e0381ea04820305000091640c018021801c00d800001c1c0340c040200584074020b03100a1001210a1101003482a01c0301482101203940340001803c901800c4815807003001920414082c02c0190f40d1140140c8041521130f901540203030300403000c0000c00600c00204110f0032035000b00003580821140048500143c8280d1500440c20304002001ca016401c0001c0c0107103210500354001103c019044501c1610503005a0491380980400c50340b10250509580110f03555100c0c50740f0041b00135405d032300d00d4100002410b0041c5002424401030006080e01c9440340300d414041e10b0454010105103103013008114031400d85070408d000c01c141b0150844443d00c1420801815214903081c54050f40c0fa1a441108144e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 605977751 1250 605976501 605976517
    0x50702010e030d110d050304052a0d052107050c0402030405030d18060c0e0108040311031605060114120604061e05180c010c0302120a140f03010f0e0601020c09040503 73
    0x3c060040c3d00424990028250300c00c0007100720036680344100d00e03c400c1d1038034082110040c1454109001c8010404050680840c142e0810313400ba1103514075100118118040b83e8000b240c45503c070864040111403400c080d00300008500412529010041e550719031201c0a80e000540150340220110302004814003d480c005400300004109000319a00b440511101c5400e00355a0a443d100c00ca26810703200d0100e01d2040c1c0d40c180c44450041d103813030380c2c1150605660850945c0358082030144841090011075240203650003900100341c154107000c58030000d0903d60100c14030403000500e8150791072401244c0540c0c0560048000039044440107207205901c0e80b00018021424500b804001a564600c160958622916000c40b20b082c590040155070f030280300003000e8096445052424603000d40000100070348500c40c42d00ca80900c161005041d0790750400c61f407518550030040010b0100210018551000f0050060f44030f0850a00c0e00010f5155412010784e01d020750780c11070024050140420440b4501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 605979001 1250 605977751 605977753
    0x50d060504050c0d030e1f0804021302221707230d0602122e0506031b07030c03020f06010b0f0d060b030106050a08011203020c060c0c1503070f02060106080601050702010e03 76
    0x71803d00c1e0007429242040b81c290b104000403203d0b09400c64401030030030120f490513202c001041d01d271502000790990074410f01000c1107400b00020381110035109002d8007020080512a00040d0400d0300044840c0700743d098030b011581c043c420400c900e91900440c2c90400c3c600501e20104850340d000803c0c4100401c0c84044e105030f00020b500407203e0f500c0f00059114284800d10394441c0c0035250441c031320184074502d55200c9200007207014041894401c0013075801c84501000741c0c0618804904980c011740044205078041240180342e40c05044d01440200d51210010313001e00701640c149182d108131402400201c01d009071020520043c110308036401200036007403489007507841e50f941d407100a01d00d500c0035110350000741c0c05400006482000d81a101071030b942c0760f0050302403032001d0820710820b034105081c801c0712480760401561840e25001c002030280c049119080350340c0c2c030f01080e024041d0100c0d040054115031041004100c0f00784e2220000d0b80090703091a15940d6248039000407a14036030000105641 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 605980251 1250 605979001 605979019
    0x108280302070b12010305010c021c0e0105070204150509010e04021e010e0406080601151103040510090906060f1715060c01060e09100c090305060109110c06090a1407050d060504050c 80
    0x148a64480c01307141240e1043c0020b0085c4440389000700d07164a03022104008d50340d46484420b48150041c544002500307018503020303003400c0040c0c0008081c2d81110b90349804810380e038402800390b402d24500d01c601401d00e0001f09020380c00c0c60b9000c02d246003184840390360701c10707144410751045a128411035a07403282c00a20900001d5118440349407101800e10038041e03400f04c164600200070b80a03c60030790781d8207940c078040c6050030710300001c1c0641407054149180c01c020304000f0200c1c4840380c41c81001c0c003030540c6503604220000200005080b42d06290744102c6801141e204014409101c08090000c10501783c86c1d580d20f0b182616800c60140001d9000200b50400c0c1c5030030025268400501c480040803418001d20003819941c10685400429010107096030f004030005220010b01c0340c00038000c01442e110000c1c60300002c8800c0608005080d102c01d41c264014200083c10301c00407042d400300030440c840c05003007400c1c60036000a00751300c2a00c0c4000c0a0b15142e1000906115091011101480307000d030020326 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 605981501 1250 605980251 605980267
    0x1d04020f07060f05092a011404090203010816050d02010f020c0409050f0d210507021504080904060b09010909050406090c030b04050f030a1b0501061e0e0108280302070b 74
    0xc0035080d9001140011403400e40010f95034000050700048038055000c40d241400d4900d22120040c511b116001d40c1400460341c41040585a5a0000c01c018500b0410051300c0354141414a0f04001070007100100380c1040c041e0902c90350b175480040000640d42400c4c00ca110f94500710090b400c001a1080b0242d001c1c1c07400009030103109010409002e40c0402905a40c1c0803000702d001590b184441c40d1001d03112a159210001d450407041c0d0009030052000c0c0111840a18030740207a94a100080314222031149000c1111003907400c00d0b0251a02400b2400c080030304000d1840f000030302207085071281d035441136200c0c808036003806403a51001e030103142c0003506418404c4e100c1c00c101d50b84220a4804640d14401d1114140e40004e020007550341c0c1d800c0c20354600700c2c084462200d11181e04010442030720955038507280060203c02044000d100b000c0c40310900c280440c9003c611181402c4140d010680d1a008002e09400c03a220b81010900c42181000301d10107000030f1410200d1801c8410381040c00302e5180061501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 605982751 1250 605981501 605981513
    0x3080f040503070909030203093c0f0409030f0c0f08030a0518011a010e1306060e100c15050423061006020d0806060c010b0603040c03211d04020f07 65
    0x7610001d4048400c074965500010f0121101e1002c01340050b0020702c1402c4451402d04550068400359842c14070306080c10489003010003c40103005103181d0903036980f0024904204940d11040341046a0401c880c0032952030141103000310030f00410030082140c489000b000a407003031040c80350707400c041203903201c0c038180c64008010403060b40c80741e00b82035201d10350b11085d40781400f034400b425404408803200c0f0343c072000040d00d08904100039642c4c0b24840d0003100c041c1e10f4451180c58000c0c0241c1da10085d800c0c44000500c4162504440c001e410007210f8840034010030406442144480130400000400343d4a5040c01038180c00e5144100c501d25100e00400780f01010001940341c0101c1d1854410303a01150799003002ea82d0b4001070100c000c0810782e000001102131910001500d10345d4a01000410724226140001e2460340c82102e044829943c1d0070700500902c0343c0600322544c5200d1007040c0c23400640a9007070140c49029441801c3c01c40c01511090f000c5280c0300d94054400c175400e640f8085d52541283e103404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 605984001 1250 605982751 605982757
    0x9150302010e0910090b0f041a010906110712030e0904030302030406060f05010806090402031e15311e030302070b160e06130312110c0f0609130603080f 67
    0x341e000801c4042082c0480c9001c1020034001e1184043c8800024a05514035001d001c4041c034a0b82e02140905c0407000700e443d035005418071184611784a60345c500700c0c2d1300054504080d5401040c100092940d4000f51040c00140020030b0354404a00740d81401d4040c6030031034454560610040e00140c009081c0000c01d6010740146005a210b884d041c0081a21041d042407000410f100d4140042c6062010030f42500304800d80d140c11a0000e805d481c20f04040c55007030301234860070060030005a03201c80802c003030400d60f0700100e5412801036008042c0048806403600d440e100100301407101da09040d0301030410418039010100030054401d0b01101141060700b0098001c0d008503d003510307100d1498000600c5007003103290b40500d90805458609480051009200031a04010070b50703209401c9009002c0080351000740b807052203800c0d55950000c2119115001410040a8601c1c2c85c0184000c820055107070780c56400307603032480c0c40a03210310406111040c13012002e441d0a0703001610070880060705101680c0c00c1c03030003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 605985251 1250 605984001 605984003
    0x90a0813060306050d0b0604090215131404020c06220510050702010b090709141c1101120612080703030b040c0906021501051f0908030d0f0606020c0114090a091503 72
    0x104003c0789580301d040c40644000c0b400014910304054000984501e8240d01c499006800a0250b03034000c00c0d03c17000d0b11385991240313002d16580c80500204203c403822644c1c0c819031750341042e04d007582007000c582081560303041e000c0e06201070040f0155442007403090b4500b940302280c0d000700c201c8440b03448000059004160030384400c0c0040d400d100b40d89170a801e203030380c8403402941907654940034a40351500c0718407002d8440c0319031980000d00382c090740811100c81070258540e80c00350010118040b41744001600c00701a11014150003820302c14104000c00001000e091401e4210083c07a54800091500f14003c155807601164401d00c1c00e401c42d0502c40e401040b080540e41aa0201c031254041c00e4031540c00400240f240907400180c0c50700480408508446608901c4d040307081880240b51103038120b50454209405154250b0742d80d101c40036040000b405810000c0000340007074061480c1d00d400090070341e0003071400c910b24481d0000d009000c68a9560a5900604145400f08039944200c0c200340780000d05848 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 605986501 1250 605985251 605985257
    0xd0504061a061315171005012604030806060d050711070f0e041707021816170403201915410a0b1e0303040e090a081306 53
    0xc0804042c01c1400c12554101011030070000c5040c54006525600814132803400d041107040c1820302d03c1c584851580c540140480c03c100c085107810440010040045d0230355610303240c1c406d20852101c08440508c0983c2054141ca007403850365a604000c244180304030b2024108142c80c000400905660003d139040c0d00602034015540042d5960000070400089030080c1004c031030004010a000400740c5180120819080b002c00d410040180c001400203040d0031aa00405000001000b60b02103481c88482c0d8001018108400300220f01030001240c03a000a000405010201c080740070b0200030f401072007000c41c00a8007121240c0116081248022144a008640030540c0c0c0b40740348680003484c01505012440844e0401d5a04507801503000030b0414000b44c0080c91810302204078441e40501c070000e100c1c0204001c04600c00c810013050103652209442d41403200c1840c0300e80b421403503801004540440c3c88076207603103195440b4030226a00f0480b40310001001c0c5580010b030081e5071206070050310101e0300161 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 605987751 1250 605986501 605986541
    0xa0c121a101e050a02190609060624020d0c0201030203040204140c1b0a0201080f041a01060e130c0503013005071d07050409020f0c010e01021e040302031506060d050406 74
    0x520203070703202c0c0134284c45031000d41c12800200310305d010b41580340c49007a03000c0c000c045010602038507560211107240d08094400c12440c00030f04503242e41031688240c040c1c214030003040b091000f000010300c0d000d141d110080c101b58000022406560341e6030032666040d00c2516031000c260a002c50211300d940e2200300d481c0038140b400d801c2e107428090041881044142c0686030b00000eaa5500130303da1680e03100400c101d482500d207952904800c1042050103020300381c25151504220101010410601a540d40b44807086007040c1c4102405030b44401500c0c1150510401c41101c4074004004d40e564002c01c1c404a420055070903002018040300052030004c032000940c02c203525000360300a03015484011200040801c4d410841041545460360041c100500035042d01c90800c02002c541d10300b500c100001c0c04183da900854101031314865032507034420b0003c020f00024909481d69010a07103404c1e100d62005a85200741000070050703220f0404032100303c80840340410039480c2a142800c010848001c2c400c1d806800c1e9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 605989001 1250 605987751 605987807
    0xf092c06060103150b1207020f011107210c1b0308160b24130e0f060711030702010905090603070519030c0902090d060b0a0510020f060a0c121a10 64
    0x4202110180c8002c00c843c5854040da00d194560686d102034202421417250703859440e85840d01303100303d07011070903c291003941d504014103080281405990040011052082080c0d02c5541c1140c444402e041d440580034980c22003210401000e80c103030b03610180c8a0038000a100d031341c0c5085032000790507940c4a16007851203603c2c0d101c41c900200140c80550380354a00010b10a49151810148030400440099008100180758060003401c002030400c52122aa108206105103250820380b0070b200c1a20b4400118104220307600003d0207070b1114483c41340120300d044003240381c42c0c400b4040f079000340001034011100e0b42c90503101c403481181c8510050300c1d1080718640220304542c4d54000c4825014005100710f403c142e0640b035550051101c1d1280660001d014400090303940c441500703c10155140f07030003030814000d201c1c2da9541400d50040aa200403440d10b40d200c0b40f100d402105500480c0b850400c0024909080034038000c2096a0003003096004140341c1100c2c0a40340e10080e008860140d91445144421030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 605990251 1250 605989001 605989031
    0x1424061005030108030a0e03030d1b020601090e0c06030c040f03030507050c090708041b050418060b0a03050d050a030204030c03240908040b180a12030f090f092c06060103 75
    0x84c0075118058008100c90840d480c0304001031461064018103030ba10309420034400c1003c480103c0c2c20b5614904800f48560403032078050101e54014482d2820501c04010055039441c0c1721101180c03658840c2c1d00201c0850704025401c0203507406041d5102d0068041501c90502030101d0b0000c110486480c890101003da0391f050641443e405450640c4840405803950740c0c51140f1001d5180d003800c544020984002020b5445e8001ca4250b1600020b0f07008900d0840d05190090354800444103000d42c0850034204005100040d405a6118641c0360607070702d41c54030030001c0b4040d224550000c1c01311842014007009111600e80314640e88036660092011031084901c1a20503566111005044040706000c00c0101c801a0402000b408420710b8031169003100b020001140800c2d00c0d00002c080f04011070a900404d40c001d561034440e101581030400c1940e18102c024141d0f0340990194461403030b00c2d81201ca0015003607a10103801a8507124684402088007101c0d0b65a03950115501c0d80045e0414815032001e002c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 605991501 1250 605990251 605990257
    0xa03141b0105031303050c060a0501090e010209031b030a0b01030813080c0d080a14030406050114061602150909090f0c0a05060909070e0a0b0a03050f131424061005 72
    0x1a140c0b141542d807103008540003500c049405400b886000c1090100599060064920850641e500010f030b80d4103100d090b204507030440205250b641c2c03040000b002c0303680d00095140d0b244066412083c078905544400710341030140304030b00141040080d03800030042000c04405860f036080d80307030458a8815680c5090f240e49940c000400303034224980c10030010200e0030007001048940b2071805c06001c0071140328411311090340121000d40d130041d503403801440f0844400484a44a0504480990820310911456428010082c1d002446185080b0f551011403020505940100c813004140b9100c61500420a42d11800c0c51220482079005441070640c292821011490a03100060002428901c0d054203002d0b00e02d001800010512145980c8015180cae41c540c40200039003c1ca803502c54071540040700180540c0c0b0040c02e1100030100c440304204541e03180d03000b0392480c103801c00301010040f01e000b40302c039083c0320a6030301c00c4d0301a0520701e0b550f4507080e40842116001d181d0940740980c1140b809141100c840c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 605992751 1250 605991501 605991553
    0xc27050610080a091e200402030408220302060a05030901141605090316180605060301030209072d0f0e0427050c090709260303060105070807020a0314 66
    0x1070400300458010411940301d40c444d58466843c1c0746040c05002400f104601d40e6003000ca82070080b45811403040701035201314101c4941e040e00d0560a60819030f64044090003001c0d9640036444c40c064040c074080e1481e04030b620045030042c25540e03488035600c0c4010070b541d104403005143d80d800c0c50340500c4800c0946038400e2040d5228a580e0040307500541c4101e900d540006006c1e5894410700d94103109041c04118000010208000c51a450860040e40c1e4010388031154051845444c05100400141e11805001d550040c1140340180481d24a0601e45240113007001221603051500d0518840c102d420441d10b0809803c1038850448555201c02008180c80021701703143c0226512103280c256502607004a400f02c5441036054400c000c0c840c0740410503c030000c0303908a0008000c0d00c010003021013008880c90b40468083c4a8114038072409030740d10b80e2440050702c0c0030b041101c0010144144018901690315042e4010018010241d41c1d0130051103c80c0c2c2c6050b41c0d80340c1e0040c070054a05076401a085c1110407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 605994001 1250 605992751 605992757
    0x506030616110c0a0b0c060c040f0b0903011e1509021c05090708060f0708070e180a020f0c01410709090c080106260606070c27050610 59
    0x5641d001d41d044440d000b18003440c070028032a80c800c46019075110409040907140d90550030351925420b0394200d00c0d040c805449403806a508010070301c41240c81c0c1c2c1c4481c2c2540c0040030815690480a0003090041298038800102e031100009842820100340e001001c081c5c0d1042020105203480d00050f804078499010008105210200d24003540691500400e901c21010015680044c0e52000c2e29030401c20116203c620568070001008141a0003a910301e42142291604d05005c400c5030020407041d521062444a460101e0380000d402e0701495011541ca2500039105d0944829800d00c80c1e5001e8001c0c040080900115802e003000c804040d40005417026000d194031094513a81c1800c60071042c400a0010420000c5202001c164030a450152000d1102c050741c0340e01c170b203600d80b1000410302c40502d001c80108542451082c00810080320710145c011504860b8070b80d40740340e10b1070403141c02c1384240d01045041d000c103144403410f0124401070001c0050802c200f44040d40e01c1c0c0c400c00403507400c0c0720508804 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 605995251 1250 605994001 605994031
    0x10b06030a0b010c02031e0106060f120e0c1e0f0405040503160f06062d14010e030115031505090601050a0303320a03110301050f06070303060302041e05060306 70
    0x2020300140c0000c2c44500c07060404604411540d00824280324208201e00400310740c4031100038140009114110081c000e9190002c2401180240101140c19120002e00d240782c88500a040140c0c044c0042d901d407500c02003025010740090b40c84540300301603004000d841072a001c0c0071022141042e02800d8443c50b444001f4614164189891143c4001c10410030b84240c031001000b00001201e603c118400b42404103410802d2103100305245001ea40c442c20044440d0030305c40f408200030fa00c00b15840d05100000d0030140c00f520001c00c08280102098034455046070fa050b48000240110301910103100d510341c01080c8800e684000805980d200d00f1310405411801e01d83c0d08202081c82040a00655040504d000039442c805003582d540c0c005007509a0480d0758800034000390b40c5605403044041803e28000c482d4103540c5860001030300040d98581c40c60040700001201d6080611030741c00075015590080c002c0148079041045a00c4002000403041035451800011414034038000407024452019454000701c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 605996501 1250 605995251 605995261
    0x80a3c0504081902070320040c020d0801121b03060b1513091116150f0b280e19233903040c0f03080409090314210108010b0603 56
    0x59000f050f41200c1107014036000840016a00039401f051511021002182000010104821103009683d082c0556000e29400001a50050394060444100150099501d80e25040040d410502d00d4010b500c155404000441004000d0340070000d62007080d0342503010250070f00e4040b0007e1013000c0c04c1d880681000d000400210316184c20000703840003480030160901d2681507140361903140012003159415113800c101c0c0c41210407440365009000c00441c09108205080c004922509100440d17003d0300c14007100307200700c4c218031180988010461410005a585400480c24009070f58411415921a05040b42e02d032010f645251012450948180c02d480c0d1500c1c0c0b2521220300003800003011f80c50300581c0107010701d10329201c00c90210503035440400555030303d45882c04c0c00032040550840c0c04c1d0940044424008281c0a0047e9803d8030b2051600007005d1040d42400d4882990080c54010305101c006008074081c45001d58405a800195100c002c3c6642c854035424240d51400741503a401c1030042c00060303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 605997751 1250 605996501 605996527
    0x405070212032706010b07150221040b1f0b0c0f07060806090c070b06011119570f06020a12031a0d0c081207110916080a3c050408 57
    0x2608c85200110040c54051805440103070400800640c1c10b2600032203041000740855442080d500c9061050410003407603100081060f40d03241c074040d040f0f040d440031401287d000c9003040030540c0c86400c84112143e032550b641000342801812544140202c2400c0b020a40081070b9406544c003450303010403001d4131030b50750703c0c0115000c05002c03110003d01d114039540100340c406018880822580030303001041746507121030141c0e0b0150154920289080d44580009640480e4400000024120f442400c85180841244400d05400e964100c105940794800001a0f0740d50006213120f0b246105c0c030f40c200c1c82c69176010f00950482c0c50460b881e0030140141c3c90f46049920380003180c50042c41c8110008a101915030341024a002c030340380031420164000042441c1402121154500700c0780c0308a64940300c0307180021469108402003080c840c01e01c040d101c04101f42891941024202c03207542303202024500440001801d03014040e1044003464041d41e1090101e0540900465104680001d080340c030708000201d0071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 605999001 1250 605997751 605997773
    0x170709110d09030e1306080618060103150f020307110c010906230f0c010507110c03030703050f0c0a0b060a08192a0f03020405070813020405070212032706010b07 71
    0x12000c104c0040d607141a80e5035401c1c2c01a0224a4102c00020f030030b03040410f041e20304000501315680700c0c0d04881c01c98820301d00c001400d506681c0d00011400086102820040203402c44045100c1d1550000c403c01080c03d45c0300058198181a800403614841558001582c6010b450700518001500c108841c240411019100300d40584003184850714100021180f210250441081c4002e50394569082c015030b80d030f1014048000b03805800261285010709000030390750380304212000b001d0210105070400404e6030201036800c201d04440540d800304019150115800e0021540c0758070a44a4103404107680c0c0f00010a1000202d9901c200020a010b9448030b26024019074102e0f22400480d4001036120070103c02d1050040aa0825040301c4c1402c620400003030365401000c080801409904101510134000b0322107421540580740010651600b03070049007040300a80c08450754030000814080d26800c484d6440c41d8890140100100101200003e51345800382880350145880040c003901001c61480c20324 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 606000251 1250 605999001 605999003
    0x1205070302061608040f082b0c11030105070e0a08030a090506130f03080715050f060d03050c160815040209070e0103150b070303200406050c010603020406170709110d09 74
    0xd40f0b0f80420030703030341c0c10b81e40c0da05c640c00ca0200c0c2950741c01c08200004081100c0ba03200d01ca540e040362100072011f500440554584001041000b411a0302001800103821010b85802e2002e0000d006502c0c01e1000500780390360710103c040c018500501c001519200110540e80e2855055545076846886d000400165400040320b030b020202507503400050400ca5001e48070300840c81042b0880d1102020b003400940f0483c031f0b400d540c80b05400c060811800341c241080c0540c2c00401141c900d4006901130404640354003800a00c16500d100c0c41025041c0008260305a00855000c28100e508208480d40600f05c80601070b6002500701c0316200c046207035140510b00c0d2001c07580c410302d000603d425031000b000c51114100c3d40a1010f0007000a00841415458012076a0f10400c921005100348030fa0005c0849921451098804100e0301044103241ca00e8290403601c0259002482404602d0300c0306d00701725156400c010b102c0c0c07091080d41000241501c5500a040581407030800140c10550710200c240702400c01484 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 606001501 1250 606000251 606000277
    0x4050c0c0102070f060509010b0f0909011b0903060e07030b06121614130b060301062607030c0f0309080403061d120c0f0703050303010b2a01050f01120507030206 71
    0x16a5160820034805000f1041c007941a980f4500858102202281e0000e8510085641040035072075041c1c58060002c22120402d03111042e041d070b80e0281450045c03040c14135a21030503c030440482c064031352090700401030b280214410402c24408072001544c40c8201d100080004048200040a48c600301c0c00525641c40030400fa500c6102e94000400308038511500070104103284205900789508141044401e5108007520800c000c00c0031030005100750005201704001c1007081040040d03136084414041403001203280c1052424201400080c2c0030b0210001c410340090b80c040e000025861103030084846058000c4165032400f82581c84100c00b8126020f01007942d825020800e81041104201d8640c50b20280b4100c140c0b100380a1040c2824170014000044040d4042d07007051000c5180072040b0707811104480410740e030310f41d07003034641c203212907510a00c14242102e85544445901010f4014501c03e03039108010301c240e44e0700d95445100703502100303d000d03116500c22081030005080c50b40050041c103c09513 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 606002751 1250 606001501 606001507
    0x90c11061603090237080607020606090c070b0f1e0c03070302070602090d030e04060b1c0c02120a0c110d05030d0905100f020c070501020a03020a031d060c0c09150f04050c 75
    0x400100100661028007210b112070f802c010312880ba171500f40ba00080c060080c054038207414107460095031030102800b040c0c494420704020810941c2e01d0390440d0f0f600c981c42520142603152603828400c1c031007400c441c0040100c40c804042c00c0c425620a00052107820040b00c1c107402e5883e016011802504000310071900c0300d501700a1169540d883c5603e8000c0544659600ca116010080a00c41a01c425500c1144c40395001c0c09840a40019102c0110140500c41070005a0b0120401c04030715200c503e041750300d000e54001441100316580401a0781540e4042c509051501030326105000300c441d03082c88050400c0d0400c2c070490940015641100210314052030860386d401200f08909000c440c1c410780c02442c0b0341e6000030020354a8800b4040000246400d0001e480050030985001c0c0d201c403001e01e0020708200c07e0080021440c00c28001000c20104090f044944070351302c070045103554141001030b0901c41c04140c40015424011124000c4c0b1450018250202e400004800c0c0000352138041c00d4900204824 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 606004001 1250 606002751 606002779
    0x307021005090a17090d2907082d01060507030306080d020102070606090c081b0d140916030203121b010c05030f010e150d020415090c110616030902 65
    0x240c02254082c2c25440e000d80032103c140e00c1c280d282d6030200c00140a481c0001d0001c1c43c0329941e4541100c12054200e003064010368070001061002001442104801d40c0c042d01c01c0c080d03015030054020b44603103402c1110b8002001019880140c0311000111960064000c0c001800614492400351445034840c4c14045090368036102c1d420309240b002d000c000f00603940883c030201408464000c650060660807020010070001110007080d0720401401d0707400c4400d407017a80c1403020040c0811a4036071092144108035015071001c0c4d01c80e02e2441601c1090080c8140d0204090740324001c2d550038201d82d402002480c03444480014058590400d001980a10924030500729201c1028041d0700d0714a0035a654890356890203081000d801d110680007460390707009400070450030b1a2030351006c800e070820454031030300306030510320010f0040d0035038128414000341d550b54001281d0030342d9046030b0320740b145545940c03410400702040385546100456256803010200c10802030064040d520004100e4009000b501d44140c3c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 606005251 1250 606004001 606004033
    0x51c060f06030b100605040e0402010e01110706210b091f03081b070e0115031116050601050102010e010e06060f06130f0801270b1915050f010c0b0c030702 68
    0x1e075841600e1041d0407104000032014000340b100041c03d140e0520505103410881d8485800f0f1000704024140498681c0d0003c05a008000103d42143d14400f11008035484040062040610042c00c008079416900d46100c0290760707001e203400548014103400020f90b2100c010001c00941e0801c128001054031390003102141c003003001022045031a25600040960b03500000345030403010307440350000e002c00e81e0060211501c1405070f8201010343c1d18003c90583e5004222070703441e02c2840d0003500d02001840d04042000800720701103040f82c1c002d800802000e4030400c0c403242628010079040403103820150028186286c0554a420102405420725007060000103c4003000185500180c50f420701c0800c041100031002d0144c0800a68010040919242200384c42c0049581500d0024141908070300040c0201c0c40d4001c0a0b264020289010310128481d86e00c0c16000d04814013031203000b4402c000c0009005d501400710040001e900a46041ca00d586160049a035030b08050842c0d0118083d5026000034041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 606006501 1250 606005251 606005261
    0x80d020c0616080106321612180e090a0534030b160e040f02070501140c0f030a090b0f060906010f141602030321090601051c060f 57
    0x249030005104600b00040c00700110107001180000f0001e442006000480e40040c0400c6160041340411400c0303498030003108940c01c0354410a2007189804140300f09010810000340d00d046d409200ca5040e145c1e6400340407a40b90440340b0307481900780b40f0500200050742007002c600764040d040c4403d0301c4a45240ba40c80b5070034000d0700100c540655003615072110083c0c00c0c43d40c0b181d10420300b0b064800e400c140b442e66242da0012000305001344525100c0d0441d0704c0c03a400b4520748202c129005100300442040102c1180094020070300c140e51940ca4034403070503000440f0100060086800150307082c00c0001c04500b0210f99400103041ca2906602c0310b10080c00901c942211a006042d240154181031400100f031015583e0700407c5030313040103684150540d50740c1d04040c808003c003411014807a40c40f81c82025130480c91a000c50025010300c0005001c245295103410304407440140616410700c185c9034044002e564450a0007001e910280b054230a1031548440c0b034440000038416400411603c02080d0b4283c02c4075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 606007751 1250 606006501 606006517
    0x4020c0105010e011d040213050a0e0d08090d0306030f08030720030306040f0b3a080306010207060f08060904060603020d050d0e042003090a14070519030302060a09080d02 75
    0xa04010018007051070150300da10717100da105144074081071800b500041d8245e41c01c05c0180002c00d55a0010a900c812150041c1807080181d03004c44408240480300203003040130407a40d80d011130007558207541000b4402c0c007482d070403241c0082d4800c440d899241c60701d0100c0c0d44040c000e00e09100b010a40034001c030450300c04601260400e440070b035450b03241000501040e2020a003603a10040d203410130382e01096507132032041c06012002003071a5101c201000c051014802c8000c075090306804034290351400700200c1c500114802c0c1e4084e8241c440303150b69003100340d030000c504580000114440d4000070760141806105160b101d40112004191103680342c01150310480e011101f915550860140c44104d10f81010b80740c0d40d0410151010005403000c02c20503048041c1000440c01040400004a090b68a081100e9201d96401a6898186141040e40556184008c1c8901c60003031030300d51540d6022140b810f00001c1220f4041e006010a47d403069500e000804001e00220790344901407203840703d07801140c400b80444e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 606009001 1250 606007751 606007769
    0x504150c110105030c1206121501090c0c0f12030912020a0204060b091806040b06040f0f060302130501180819060f1116080405041803031d120904020c010501 69
    0x1003141003102041c5040040c0a040c04000c000f0b024205034601c040700c9602155400040d859280d060000b000c41d0050400510140f19120003a42150100c0b42654100c5000203010419a94245404d4500079020b2030040c100310102c54100000ca204840d140303822644a00d00060a807280d036980c405038a00055501005038000100e400460410f8451240903044111a00c2d0920122400140c032a00d6203030802c0382842200c80c080340464a640d042207a401c00014074098403030f42c40d0240c40554450f0b0b4812010900d0600340f000541038000c0c800c4806001301c4004600645041000541e50110402d2500712140c90086000075440014170000c04801000c3c640c003c8a03541c0d60808074244c54201807992619481d0001402d0501403180464251503224100000d0003802070070102250b0049a0166410a040030034071081c40d13500d581c00c60800f41c400c1e1001c2040b5441d04003040d20740c8042c580420f80380e5206d88000c080c02001031340900046140104090b20309940301c0001070035144203901801d90 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 606010251 1250 606009001 606009017
    0x1060b03070801060e040b030c060d020931050702030d090206070b07020f01110f03010e0c04180b0411031515220504270803040c080303130b010812030402040c050415 73
    0x203170b20020060541c4411181840101c0ea5080003030b44510b0b00400303440c0304480009035400c843c5066010f850705060014408101341c00410031380340140d4044140c42030503035142050480307262164806c050049801d64000c606103050940b400d001460045c00a84e80a4000d0010740c0004042c41c184e41d10500c403035809843d41c031420380f441a00b07440c1c480e1160040301c0000d102c400c14200000d0180da04490030329104801c29100d204410348070344200c1c1c01804015403000d600d90800c0e40c0701d411a01c028182a9020000b40c0304d01c0c11000801d00051b80e480030b400031400c40005462518060400032008850300582c034100031080620034002c03809031400030020000c1d0042103149410320a040704c10111150500001800c0c1110031190000d600004280070404004601840088030200340900f007400b08881d924145622200c1d041c41344d06800b03c0b801283c000000c1480180854160383c0100001165810364843e942003001400c0345403000381c20010140000600c4417000300f0304803010740c12031b03c640754 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 606011501 1250 606010251 606010259
    0x106050301051305060c1b0f0105090c0f0306060d03031d0a0c1d0a0504050a1a101e03020f0d0b040807030f021501031101031b1206050406062001060b03070801 70
    0x1c01c0d120010325061001c407007260001c0200e100410810b500458031490a41d0380e6a02c600c0d140b69820300e40e00445581d103c0d014084607052415880f1038004c0b5401d80861f640701110004114801c0c07240d001c500d406821690104c0c200342040e510195646100303050200f07400c0004548152030050b54000050310f540a0b844480c1440302d001c240c40302a20341101d00342d11135130120001d0080385001905c60300c5491703920700c001014800248104c0d5030166001440c4080040c615902000c0b07031005503001400074400e01d000103083e010410740500003d141c105918401031071a001c00002ca20f6091215401c0003d5854000c002071481a04034803881c0308903820b90b21004182401029140d144a901080d540480c00c0c000c080605840c01c0790440ea805000c4002e01180d0400480c05810703c072100310503c9408401c0040503e4107c54201c44820303c030038041050a80e900204410f4541314496140490650740340f04110101044003c0000e2010a00101d4407a0f030b10540e25005900444001e0005850440180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 606012751 1250 606011501 606011503
    0x309010c120b03032209020307080106020f0d0912080c010609020415080f0f0916380d090c08031c0b0409150c0e150702030c03030708090418020d0501060503 69
    0x1400c4615642002c118001807000425502e01c0f900b08140b007980c1942840d0503140040d02e0440000c0c1001013802c1d510b84c102a40003070308044080c082c0e81c01501500c0e1a00140807400180701d180700066a9545094a1030030301820010036461320305071240e0008100001d5803480034041e400c0107090b1100f0041ea10b5240005031808618810756460820104000b8007030744007030b80110903400030144107503030704980c4404942924210740d0038103400427121281800940c81d2402403c0e00404042c4201c070038240820000c00340444c022400300000a4001409811020b100a0b031042c42c00e03520404021030410f8a40f400e40b85550403894003102d0524801100c1c0c01c07015900d0041c400d80c2c1c01d003624180f010f144c0c42c0e80c0740d01140c08265070b2640991350f038100020100e40301d00c0000c0500c0201400e440409081d00c0ea001582e40d10140082c0c0c02442100030720409801c0c00001c0700c28003034001040600f0031071564200005000d41c0c540b05018403807013440303060241ea20a90b401403541c0c465000001e150f403500e4141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 606014001 1250 606012751 606012767
    0x30601021e0c01031e0c11060a0608030f070302030f030108061f03080702100203041706011d060916051905120711030901030b030a0804080706090f0501051c09080309010c 75
    0x11420340c4044007205240c0c080005100c000444003420080b81602d060020744030901d041540303401c0d08034244440c0591050700a1100395080c5124410307510701d9602c40007200c0503a107d030b100d40d412990042024619000c9481c002d008011f1086c415170740f82108039580300d200f0b60030a0304240031580002d024000300046000100c561280306441c460b802d86c0c82c1d510364040303901a003140680920240a0074180481c800e0007220050320720b01030080c5020180e00c4040c1c1e0341d040c0901442000e1135441100c0c8101981c26840948035010060000a042c1c0e904412500240c256072418420701c5410301c01d5120024404070b0480c0b940c0140d03500c03991203080c940702d40c00c4205400b80c103960601240c41000e501106c0d0210445041e0381007801c0c040b484032444400320b03281410030b01c009480c42001040104481c2c0003c2040c50496125507214821540c4454900c5401075052051901244d0b04102c501e809008180c080106c032003c0d41400680c440d401d0b10380702e86a070b004036104042030355500d0130700510750740064030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 606015251 1250 606014001 606014023
    0xb0a031410150f050405040606051002010209120319050f130e041509230705060403110901060e0604030b0919050309040c03050408030609130f0b070e0102030c1b041d0303060102 78
    0xa42c00d202442d20900c9000c110240c0205030141344c03180005010300c01a5041000101400740c546400d4003c8014001d000350010440c0c5841812820099102e9a0000098401d400c0313060380002603c016200302034440e54042061031811b200e0a00c00c8520740014001c0310b000500500900321540e140501d410b001100e0601c0c0c401c2e00c001d10304514200410380007003190030046141018184654489905a0301e88816a40325591013440010003104200703001072042c003000700564140307440b6600e07444140e402029245600390001010300003080402c0c1c1d465800350304500342c2c50544130000a40f61484001d604058825503140c1c3c000114019141068410059481c0d402d20701040182055900c1c64100c1c440645814440d100c80c030b01082c16040601078958a0300d0b07100390350116001c55441c00c1d0300d450404a5089000c11111070814006500203c112518840144041d1441c070410010f08802c60300381c84030607904503964001d40c3c90386002400042585d840700304010f40d01c0e4503004000928000100361 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 606016501 1250 606015251 606015281
    0x17041e05040227040b0607060b090c0313020d080c06040b070206010609260708030409090221100c0e12100501091b0e220203040b0109020307050d0b0a031410 69
    0x101800101d0b8228054070600d4199405026030703c0b0414000030058403c40e04c2e9a640180002030607820415242d201d07100180040d59401c546503070303021850150f03000817500066090000030100c2c0040c07405240d02d1600078400d4800300e080c14440c00500f483d10404031341c101c0b000c08a110034844642e1301000070701d005010302e01c0e1220469013414030031407020368140402c00d4011003c1c0440e100c101010b00c082e101405040040b40c0c1c880ea03484000001a103580780082e0b0040000e145040d1502c1c5890108071961001d040080405d440c1e043d1a010007800090030b03900c100b00105061814a40d5000394101062103400010103051400001c403204981041e4003031441a480c0054041c0e40c2c461804e00410703220f1030b9007070030122845440c006c1850385c007400b012104039098074030110140f503c9070f5015600407401080c00ca491680c0320340307665003244010b48208002c2142071200e0755066005401c440c44251020f803c21600ba40d4940c0c62120ad91100581890ba98000f580400440caa041c45070b404240c40e451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 606017751 1250 606016501 606016507
    0x31506120b0a080a150f020307090f080303010506042c011203110604020f150909040f030e0d020901090903020a0210050307020d080f15120a120e04060510050717041e050402 76
    0x9042075511003003600001d2140c007502040402c17011050b88400207807a0b40707040c15566490000310040941c0b02c5401001c0c10a0910100400c00940010070340781a66005000140b0703060500010712580d049004009480700240841d000c0d12183c45000b03a8000e018650100c00d842c602d03481c001c2c140042c820b041303290303d500003020040540c1e03401e007140c2d4a01030291811030f0400100e00d030f180b4030ba11924241c80c0d0003a428a00384401c20003600d20015095010343d4805000c038004404100d003200303c14101a6008030804010b000b5041c00368001d4801911900460322002d405034003040800c802da4000c0000310303001000300050140c06000d80182e50480e440d1624017031034159500c4c00f5020001c0c1c02541c107000d180410035980d8442d4941411100c2d0014100c030484a02031030064582140c6030341c01d00002d480705030341d580c030760a10740107a10549400901e4030620500c60281112282c0045e202074600e001a25242c24144500707100800181c40c3d003040500703194880f1021480c059180c3d51003280958810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 606019001 1250 606017751 606017759
    0xa03060b0f1507030305090a0c0806041703090c0105090f0405040f0c0503071211121c090501020705180703110d0204050907170402151e0405040c0f05030c0703031506120b0a 76
    0xc81102c0710f45030f241c20005195150310700ca291800c0c003100c038000c0071080c4d52200482e0308000004c0baa44158840d45100340152016180c01c4824002660454650f42c0000003800496001e18050038510714060130503a10b040b102c40004080d01c4095130300356100d0f189140701d0010301201c64482c00241006400810f86249429400740280b8591032003c0c01401c01901825403035980d203001902c01100800803030b645800040c6012801546810322140441c4006d0300c000780e194000701d1041d0484400030310107850f807400313810b100d800e654009001c203003050b0b84c1d1440c103080040c100300a001000c224450050b11141000288494020040c01e151305104150711484800756640303028a5010b80d0588001522807118400ea46440c0900c4003492018050200c140703000035984c4010704122841120288275490142d00195000058500404c1c00640104006415400c40d1401030100501ca0b01d4001640802114001c8641450790007042c00241d550318048000c540b240100060800101c600040f41c40ca0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 606020251 1250 606019001 606019039
    0x10c0302130e101703070602030a02090f030c180903040509070909180209150f0907050a0e0f0a062a2f1e0d0503030901090506010801060f0e0402030307020a03060b0f 73
    0x20510a58032410502c0711311250030740050040e40c1200b03a100d103095440e400d141440304007a41240081501580002d650394410345000034000743d009801402d00810f92000c4070404030740c410003c0ca0000b0501c0208000074040d124082d4941c41140d082d42c45041c0b00f030900070b6034020340e4100c40410342c00301c1c500300241c00540e6030181d040783c2081480d424541d400f801c0f480851502121921840d0b80542c0c0d0300104100faa80040080601d042295103d003c04210341082190340d015020046070464602081400814081d0700e0380340034220154181c039070000c01050340c214240c0c043c0d0801c44141818041ea403003401c5500e140c6003240d0300c0d098404d242c800c82920106155000b10588074020854401d010840d81e11040726004400e600181601d80e03915003010b901d8080c08071000d0484183c40743c4000040c0002041c8981406d507842d40d504041d1080ca0224a04410240070f130003aa03060104104a40060741c6240b1000011441036030b0214080c04440c040000200e84281b1950150018000302101c041e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 606021501 1250 606020251 606020281
    0x31b0306061b011401091a01020105091b01170106020109061409100c0c17041517040b06011b11090105040b0603040f0c150824010813020102030c010c0302130e 70
    0x28482c41074907510052015007038007402c1110384001c0009100c20002c0384c03002140c1c126240b280702c005050706486042a0049080300c00c201d80804058208240d20301c11260091304134140702c64145840403403410414801d40303900350700782c6c40100035039950800681049002e014000302840a203035003002c1450003038041611105c0c0e01040300102d560303561140030454011030016074019000541c030903109902070706d80207841d80603010f040000b00d15110b41c015218440c01146061514034071000d080b5840e140c0d9000b00070f000290045050045882001c1d8180003040503031200d407401081004040a012020700a21000681000740203a040c04441c0005460b1402240d0f08030b9440655001c1c54089414007032204034064002410341a010724503807640e1540203c015020b20058042d4151203410024a28000801d00201c180850b0520001840c0d200c5002100803031a40103006603407074000d41c00c4030700c0c4c02c4664071000c00b40030079070200c0c007800030000d42d0502401900180441e5401810401d20421040c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 606022751 1250 606021501 606021517
    0x50105090d06020d06080705130207260706090305070210050903030f0d0b1203030121020a090216080c0a050708070608130303060f0605070b10030b061504030c0605031b030606 77
    0x1010758514003041000c1c5604442815050b04010031120b901c130507141ea103c01e554819284142148c03c0140000705003407080780c1c00f1503403000412000300314000300102500348046106d001103400b8400003000c140a8060344101c1d901c281d503110340e2100c00e40b04000100d01803034081010080184020300035510700000325041c14a01100c0b06884120780141c0a025150701032056401502d0388088407a903d0002014606942d5181108007091901d1a100c8014075021000a584581850307400c2003c081c007a8002c00840c00d4070581032040000d1600c402c1c801d54030640c0c102d0860341c4003865071011300006202100c060141d08003d00101450488002c103007940c050104e41103040e2041e100c50805000e035001100620018007004492582d920b0058000d80001c00c041d150700f00c110740000d02c4004071041e40c4068a9200ba0310320495107031a8107100a9011030303074041c17003680010030011000c1450071742d0405c014000c50781c42595a18101141060381d030100300c040554071100b4030600c001c07665507030207885000e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 606024001 1250 606022751 606022759
    0x1051003050d112d0f28080702040b190b0c10150311011b03020d2d050a03020904020712031b02070b0f12070e0406121e021f05071a0105010509 63
    0xe4408442a1542d1184400404d6200d40c01e07900d280807070701045c826000b080441114200785001107088407002c10001c8000c10200040090500516245d4000e0746549405002d10b20f0485000f2200e42102c1799035001844281800b1480c1819410100500e00e0740010214090240c044c50032a02030016020740001048400c1000400385a07234031407212080e100031080c0c1c01d40e84008041c10040e4441d0f040303903d12400140ba08007a0304074203240604940844010400c1c8080f401c901e5081180c45070000c0d046e0104054080003e0342141c1c0d62400506025802910b09814402031440c01404603501c00090080b6109100209103910f43c0110301b0004542000d4403032642c41050a2090005105144008418842110a00c010079600900f0840c1c40e5000761000c0001d592035291000c00c903242d03400014841c12216190595907032800e41002da965101402d81001b0440704508100070494070b150110000e03002207000014004180e548081d6420ba903a510300d0a5410300b80000c155201b903204d46806 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 606025251 1250 606024001 606024043
    0x9030b0405010b03060c0a021506061206040f020d0e0d111506010e040c2102132112080703060906181d120406140406020a030f0e0301051003050d11 65
    0x184542900303c84440b180050680f00280342100c000d2010f030700404600001441048500300c5d0400342c0388500c0e80640d000501b010704082a20b41d0f00b8022080041006030460784501920711210054000341142b079400d20f101080d04444904214a000d220034841ca007000040e400c181d151034800314142c8441900000528801d0b81e4400040c0d0740c1c039100141d855082460b05007030461036a441180410303482c4444410341e02e400d140c00c0f9185c044c0e00502c01d07803400d41c001e5400300b0880c0a181c1d41e80d0503440990883c1240f8080c002e030325000700c890105401200803540301010000e9140d03042c400c013006030481b842d0400040d4145620040c00d81c40c0e42040e158407617074440c00e05101d03d00c10b050304c40340e214688040310025013055000041a421600c90346e0049000c000e14440d4201110044d103040d5106a40101064101618101d800c4881c3d501d010301840316248085034191002c1c041d60b40320742c043c5940ca8003010320b07610b011450b006e6400542000c00461140c0c02c1c0c008080400c451103210420300c0c850130 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 606026501 1250 606025251 606025253
    0x1031e08070209130b1e160c05070801020c0f0a0c0608130203010e030d15080c010c0c03060e03130801090507060809071206050f01060c03020309060a030212072a0309030b04 76
    0x26061041c420065441452003040099401d100c081500b41c0520609480c000c1d600c80341d003802481103000385003403030421010000407600c0c901000d002100900901d0600342c0b2084030348a55040c4034440e08856441e03500003a10110301c0c14100545196a50000000c10001801d80c5650364881094000c900412028001080710040702400900403150020020080c052840390718039070366403000e100214042e050004171040010818940c0048804120103410010700110044804071041003046944c01030050022010510354826584440c2c8280c00455940301c18003a015401c01c0305600040e016030402c01c840d0300149011440c5411204035041403130322130303c4102d405800c0019582000e4681d003002c0ca02c4030217100098100e01c0c050004540000039503602d4040440f21141c08620140c0940d108004119a50030b00c50001c0c4400c0c03041e85001810901c10b0030100d5a81442521a500090352200880f030b09040758800c2c07803000640404d0384903803a0301690b501600c221f1162101034110600c030340000d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 606027751 1250 606026501 606026513
    0x9090209060903011d1905100c05070b0406090b010b040b1b010e010905070e060a06020312040507030c030f0303050906070f030b06040f060801140d02010516050f100903021501031e 79
    0xb8401060090084c821a5808641c01c60f82e60b02c80000b20341248150850302c85294101c070740080f645a00301000c0c00f0f21036046103000c00602000c008200030050f04101d0350011506280c0002d002d50300c959408142140e280c100071202c900c1c1a0030840f0b0a40081000f00040082c000465882091800d5000b0f03d480c594002c050061100d422000c0031303942000d052001700280811807070180d8420f01c0146805884e02800d01c0144c061901444000d40e1042014100300f401840d4003650103407144044560391f42e141c1e41d400c1c9048505500480798000c0c20b410800425405000341d40c0c3c043c19800043c9a40e203006400180700c0d600d54180842890b41d94040e003803440d100d50007264090891050801c1060755281e0009044510901c900b0303943c941c644006c681c2030300c0d20481d403420041e0141d544605040d00000d80c90080d68108000b1038403403140700000360a9140600c50505c1c100d40d03c600c00140012641001713414100b0001e0f1140302d0070705840041c800111043d11075040d150000304580071000d05841c00f1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 606029001 1250 606027751 606027757
    0xe061c0c05030d0e1e010c021e03010213050112090b01050f0315070203030610050405090402060d1814010f090203100c1218060e010c0c1e0602130303090e0103030909020906 76
    0x1060b054054841c01d59030040e001030500085400956880d4103403820b41a483e100b05240441361800520f09108060151030054643d404004400b84000044210f420010742240d009031203001400c10400030411203980c0140c0000c524000d610b109001c0754902c0c1c0d54407101e6138814000d11740b2546444031784080684042044d0901d00031103035480304050414850295880d04100e0b8030074400c40c450944208a14441c40a45045400141c0114040d448503400c101a0307070010700003a550a55154200402440fa03032413402c07003342c00303031201c0c10482e84030441c4a402d5844419584180c41d04081c10100103803400140ca1018541300784c0001502402818200c1d00300e18808034220059082c0320824240d280765002c9031011504c9203008200c6514050011800d0f681c0c03c800718400301e614000140041028107003401034a1000905800311070303406030740d080d049170000c50303a2043c4100350745030601c00c0507000182d00010b461101178080d480c1d03155607001031807801b01e401034a011503000300d031340c0c2c820340c0303c200035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 606030251 1250 606029001 606029009
    0xc07020a0e15060d05161d09040311061603060f032004180c0e0f0f06010f0207050409030801260d031a0a030506090111090a0e19050405030a090e061c0c 67
    0x3d195a129801c2260401400b001d840c80f260081c0f8000c103800d515400703040c5090341061403a0750f10482208040820000000c020016003d101c02451f2140e00520107100e510320810345000310501101d0b400300b00804403155034011001310b400e0031201344041040306181c0d106d8200f100c2c5031580b40344407907008a03000e01031004100149101c0e4000310020004e0302e000e00819600e0001050013540c1d108408891030200550f12182803070742c642c010910b554440e1804035000c4171980100d03a81207540d40042401c5928469081d40000e424400510000b41184100f281418000018030141c004043c1040d40711164540240c06040c0c0e10b50b90700304c090540019491850381c0003002014500c0d602d0800c5030311003908542c00310a6500c0d1014181548070b445c8152104d440303010740046d881d40d0505500c40300710040070b4000d504810724115400c0d0321100c180215480386200c0d0000e15140d01c4802c202400300301031900701c0d520101c25482008556140c0041d90801050480040c1542d030009007030901c400952500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 606031501 1250 606030251 606030259
    0x3090618030102040f0905090312150a241d01170405070509040b09010e0a0c06030c031b02010e0d0806060d022b0b0f03060f0117120409060e0c07020a0e15 68
    0x50008000280d145c25508a0701440c800380241e595420805440b4406e2240c0c05c1c1240121901081c40351500000d507150207500a45800502074640b0b44003200c1c100040c01161003111002801402694000d4266280c070044561100d030052000001070145441c42d070740700003118100e40000302400004c2010b240280005040d0409606050506416084041700c2d0022150f08108803914099000600c403403a00e0382107002c01d40080c1c20b10320100d014048065030002050f840740150f241c007100c25101c1000459054000144d900c00d2210b407182405402d080c0f590070b109403041045010f4565008850807072030525001a0380e185c0d11130ba0002e00b036843c5d21f0b04800d11310340100fa87c1c061041c5540b04404400b070446840c480000c403003041581e100c3c0c0803a0442030811007140104a205040300001c080e14244000b55651852541c0071840e280d04958480c10595440c0c0c8000c00203c2d1603407000c1034000c80c1c4d4020340e0303260a405401281c5000024814070344865104000a000004aa403002d104810001c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 606032751 1250 606031501 606031507
    0x2030910050717060d110114041e0e0106050322031b0b0901051008150601030b06030c030403081303021902190b0309070902090907030c020328020c030f03090618030102 74
    0x800080000003202c3c2c10704250b4000b5000f01d03c00345170803a41c0703220b16a8081507454400884600445603c142142c9004071a03505010119802c00c0318000303d89031545109500a480d4a020180e80c4c8852040c1d00c41c20502c0402c109000300014420003440c604c079100b80707035900e035544285812188100724855000c3d01d1421003c1410400042040d814050380701d5200921190321540d64503c000e4085100c0c1c0a00d5a00680300592200c684840c50365104c10305050005001d030643c4082081944101e94164804000200300310426801c560104c0d0890814001498594100e5501a580341c91000c0c004014080041140046548043c080e860040b6511681c0301503560711002e240759500705441d1502103000366400400c900000388203a448100000b406125142c50b2080250b004044102c1c02d48118007080050b201d51a07069100c40c8a9205444034620b00400c3ca048024140071044000d2031090b081001e0b0b0224081c0c000059035141e200c00c03141c8030340e42e800d50f2a0140300c40c0710380345116030154008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 606034001 1250 606032751 606032761
    0x60c090a150e011e020318060d05130c0608070806060714030417060a11070b071b0b060102060907030c06030c0c05070305010606171303052101030b06270a0203091005 73
    0x420080b041c481000c0e2a40c4100f030030300d061000c180780503080440340168018492038021014145602c00b6020000e000c50b45000214008402503603000c590741d400303601c1c0d90034040e420080728014550041145180c40a2103040c440c40080c00000083c4c07410f4414440401d0f0720f0280301d4283d00c00c0480e011440c007242d9440c2d81d2616040c07880f004e052039406081c005e010010740c06032180e00030b20382042403c0101034607000d003560710388040980182c0741350100145c40d0000c40710000c0d019100d4003840d0140e502103480740350240009240440040045000d90400e0504000003120f40c41000e0681e50903042c0410f14101c0c1900031a0049104007015129100e40c0d8000011b000040d4092010b03207682e5034814407100c01e12210b5503484002626040c0c3d4103c00c4120100c0440d2040014001c1600c21b501c0e0221806108009010450701c00c0c0c00680b9203050180a104080ca403264580c0100c507105a0180c2841703454460050040c0310080c44000c0e41d54000000840040c02402580300914040c2e40400041c200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 606035251 1250 606034001 606034007
    0xc1006140a1410050a020a150f0c0203090d0303020a0311160b090304031a0a02040b1b07140a0504051b040f050406060504080a031404170f0d0e03060c090a15 69
    0x2422801400741110500c007040141d05400601c0d560a00070f002c0103075120f960101180d0580c003035081c010450240c503c10000081c491a4007482407201594086605846540000304441c0407000c520159801042501401c0d11030b17107028490f940d018100107840b441211801c0d400f514450000140990b030005215400e104518100f8006130300441140e000e070355606980541d03921443c0409850172080d0200198041c2c0e480700955032000180d4809801c0c103039243e18071000e07504500100c80c2c0150700c210840c9031040e0304102d064024003881400b07840c0ea80e00c0c0008600401c585010300e0340550b849000103491000f03905106622420000f41c001d035103503920300c90b201150302c00c2e004841c8245e0520f407000607013034441c0c0e041e1016265141c0242501d081e49035030544070307d80380c00d241740e4440030700b400006250b644502c0c01c04000c2032000090011914055815420b25403044191024044001c1c0d4040040e00c0004600c0e50082c06c040c4510360b0b0700c1205001903208003089d8172015a03d461520000c406da98 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 606036501 1250 606035251 606035279
    0x604061a0c0c010c02091f090905011e230a0b100c0501200d1a150408010f11040611010e06010909030f36080102040f0f0e0702030406050c1006 63
    0x40c40078152810105071200445181c506100080d50001c01c910102e1006401000c81581d0001034441004a06940c0c49801d416070300d91036801d071070f1070355100b460450080c031140070407510f08400072003000502c0341502c00248036031103c005009500c220074000b0b2101c07400c41d805008101d00050450b20845640b10f4000d0590300c10400c1210a0f50a003045800e4450350a4014900820b20004050400b10b00c04400002009c6002c5006d040300d41d0070040c41015100c1402c0c1d02c0040b400c2d04c41d0f20f540c4904040b180c07801d6031240d40480c0903041c50580405101c044150540d0180e8980e40b80421b40030b8004121580504102d0700301e84c04501882d400003030701c00d401c0d6000c07000961094503a4400c0f050301e8801a20309140c42c114103003a1264581031085150b81c040910b5500429003110181050f840e08041400c98226401c1806407000c034240600c418011070349510300401c80381d4038041451904050007504c9000314418482401004140400400c80031301c0304042445012608001080e81c501000940c0c82c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 606037751 1250 606036501 606036517
    0xd0b0a0605070b220b04030504260a060b2b021815010e03161d0916061206120b070e0a06021203090a12080105210a06050604061a 57
    0x62010001051030062042e100d40c550071000e032415580d60448444100344000c0d519a900580850040c1c0004410480b0746004601030382c0d58507201c034145040d036080314036071441c00714910310030f00300038610587c000601b14103296001e4004203c1e400d80710003082c0310841c1c6c0c6100c81c50568251203441000c08400c0d4040400c24001c0f00e0107034132510440a080c041640c00c0d1917581051900d00c8004110754080e4050003d81c00010302154402c545002c0c41c26825111500302d4040c0c05568081e094480d144e02c24503a800c0060800075001d0710710428800904007991b03129190a004e40006205500078042c0d100c04001d180001da4041482a60300c2c0503070040004035500070124040c1142c050b8141012141507050f9940c6400900d8020243c44090050307800c01001740060740b0803041840000303148003003030030300d03d04007900d41000550508007002000d00480b401402c4200034648141202e8200042c20003009400c400c0015107900c8200100d805003401c5e8001000012151503880d0340380c0c207160f004000c54 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 606039001 1250 606037751 606037759
    0xa0e0606130503070b071a060f120309030f030c06010b0c1510030213020a0f110a0f110415061407030e010f0c02060f180a0b030609090f060709061d01020607230d0b 72
    0x140d040d406000001f0103682568100107171110003509400d002410140717201205007240d007010300780d44c0040c1c0360443c240074051041d04082000e0400e6030f420800b0a015000c1d10303514500b05100e49840968400802c03002e00b160031000c02c0403a150094070071800020703640182205103484103100d148030195201e401d0380e500160044c8654440940308010259071450040701518410036280c540803250b03425500290b078601e001c030351840e40380d685604c90300030711954a55035940078030314001c00600090140c0c0b0354100454010810400040d9000304c00310600203090a0941c1e0a800046084031440081304000303412010014948804254000141c0441e202c9914000301c0d40c0700700d000303004956000c0e03c140c03401d0306024008a8164034008102540c8a10190704545180304103804040c907080f429900040800c00b45a01803181c16030040e109901107001d44841d503400100c0500007507440384000c02c2002000800664000313024502903102011400c0001c40c0b54494018503202c5c1c005120340742c0d400b486 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 606040251 1250 606039001 606039023
    0x9180507080a0b0a1217070606031e02010228150203010f05030109050303010323060a0f39031e050601110703050a08130305010203040f020f0a0e0606130503070b07 72
    0x80410b0b5028201c3c2c4010064500c40750540344c101071510351000740038125074102040810000066060313014105071070160401040d803901e11b04050034140031000404480280c440071800142c0d0b00011404505403204d02c07130a030300361a6100c5400483d01c80d030900810004890302d0740c015039119034000c0c40c183e549800012210395034500400d0700700c1d03a030350500910a03042400108040b5400c0b45100380690713194013803614400d000207003860804104845c0c040c049a40c64400000f042401c0c450000402c01580d5031102d207170b40071030302c8000200c00e00802c0d04c0e110000304a900c0e03010384240c00118002c3c5482c29150350711210014000080d003c2200c0c2e02d40007071401c1224031040b40e00012101e0449801c10701811161296403109071507130b804821038442e00f141c16400040000c009100441c402c5000d040c0300e0200400c07920400c0410300c20280b415200e950302c60024070a84620541141e000300302142c00507650400411440700c800701d00e9000641c10b0062201c00905000c2400051500510401450403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 606041501 1250 606040251 606040261
    0x70c0501150614030606160308190e0a060c0327140607050d0b0f06040602010902120d021203060f041401080120040314070305070f090b060421030918050708 69
    0x601d101c6074030450300003520000110800d100c454008641120300600905d21300012021140701038a4a000f04070300264110081214071240e820340246403403c500e2042c0702c0c0480d4008413984d1104115400ba11466542e62080c1c0d0841c000c3c0e100340f000d402c860f034420b001540d03644a44445084d1081e0242c0314024081500e0b00b41c030f00c0c0400e00f00d1280c01151955800d1201c10100c5000400c034661565410482a07028244c407599010302134802451180e001061006207841400700c1c2d159100000d2103160b00400b810301320030f030b004202c09001a010394103058a036a95100060308486080b00c5864100c0c4c0707881410340c00f80381d00101241c10f90b10080000c0c00f894816480ca00001d1088103a1154903100c14402840016103a0b118a1002c240c81030444040c07603140d0f02c403d030405a01342d000201c2580901010000d100c4280100c0c04c042c1ca04440705410145080d00147c030141c55070440312074411250b90f45500f007501400f00100a0014000d101100c446403041072401420300f80c41d040c0c0400d010000003a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 606042751 1250 606041501 606041531
    0x60610110c120a051b0105070b10080304030c061b0507062109030504031208130b040303140c090a1d070c0f141f0b0d061e110909070513050d02060c06070c0501 70
    0x100e010341041c0d507120b1800d070715a00c41030401c140162400c2b1000c14080f200094000040001d0070256008854440c829407812602078440b2007a809030b0641030821200d00c101081c1e02068001c21140c0ba03040640300c84044482112494007a0382c0d01880c000d1618160109065103c80680b090324821040384e130041000c82d20a889541084501c0325a070040b4280c2040043d421010040c0c100303101c0d082c08120f03845400070300d4003801e104540c0c22030460030106071901c60f4a85022041c00801c8510b80e940e074030001d400300728648010000c10400c01c0c807400313002d440c080009802c06900b009070403014180b100070040950f1912400d0717030300d20408013500c000264900c108c540d200c1e20141c0743c0b0041c028417151300d0581d5660301800b00702c40a0320b146540000011206140303409440307840008010460b42e207221032000c00c6101100034007143d003045014000c4090441000003c0015100d00702d6080354a0001880080c8240c4280010f03d00f450280c0c2040c050441e41045403c6c0901d0310501c0240002130317140c603c1c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 606044001 1250 606042751 606042793
    0x5070f090305060a020901050706050f04051207050606040b0f1207051e010806040b1c08030f01090c12020c0703060204030803040c14060d2c0609010c02060610110c120a05 75
    0x2d050303900084081550082a0f0f0700818148006051907805c00324143c66002c01c884045440303045441106040004001045c0f00510310040c0400071f59050613940e071074880c1d0342d0900038403a9000d956a0815141e85507207000b94041e251500803d8090080781c90b8400c11b4a80d120351043c240104030900310004050700c0304854440c40324060b0346001c0b460390f40070200405000d02680310b64028084a071100c0420045c14048583e00d409224004d5580c240340c0070341800c4000590042103924606500e1169066001c6c8034951035007000e010142e185c5c4030302e01c6001e041c88056400101014400a000800c0040c802d020310b1046014018200d16070383d803042c8101d0101c0c0301c10706080d4002d404000807a144822079000702040300d071000c1015000070350144c5401d60315964a440d0301582e2b011608110b01017100740607051110045201030403c6081c10303004a080145600580760602c0040700b007900007541c04002807003030b6042c003d20301244505000221511416200380c10385041c058426201c2d07290300e08840c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 606045251 1250 606044001 606044003
    0x27010905090a090606030b1e0609090604080f0408070608011d090c220504300c020d030201020d0c0e0102070602070f0b03090f031207091509030308100306090605070f0903 75
    0xc5070120342d00e0500034801803105180c12502c0b01d68604011022601e1044078511800d24a05640f0051071080c9030380840c440002d00e56031141031030b0302c1004000c000c0440c869400551020501e034460b43c0b1400079200c580205d810004c40c5102d0514002819984400014101ca520840c9507408803a91078110041220840c0c000340e2550203042001740c1414a0b11001052400d0080b5405204001c0031002c1e06560303040e2001d442d601d40102d03100c0051040002121a480d9004003250340440341c0880103000664030400180c0310301c02c080c441d032013414002e404603280c402c8102401c0150003481d038400343c2003d2003091010f0052151007008100b440c00080c000c81659030701c0900c290600d10300321400311541e10090103e400c901a20007108900c070020000743c03142c0c02080c4440d903200c1c6020640280040410b0b4460025048240003030318509802a41c4bc600f9207406d0b28010350950740c0c0c43c81c4ca2a04180c1c542c0000d1065180c143c2e1102845001d41c000c60146003159600002001ca561044440c40c4503800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 606046501 1250 606045251 606045259
    0x70507150503040c060f020a0b0109050f06030a030c02041104030f05070906090204050609040e070305060f010302090a05060d0204050a1104030501050a05090d0f050a0903300212090f0f0627010905 86
    0x701840031701d0180c0c03200c02c008502d52044a07844200c680e03071130483c003800781d00c08550b1076140c20510601d540c1043c0c150f544060150000c20a10304039440c011303c151b82c9614081e003d540e4034620607a001040c02c040300d01840d005440c000c0c0d000c0d114a01565a90b00c0c61180d005520300d0444041590401402110700b2905c00400a60401e400982040014103c00440d0030862040380c03c000000350301800303414440c0116001d505d0745585180144611142d00801da6518945498100003d543e03482040700185038064500080c00c1d628403101600601e00c40003041002c3c80b0106001080000540219205407892003090000d030f218420069130f240314140700400400e00b5910085412486007001d80400013040ca085014641d0301e45805000c540c80020346054000d0340380c4102a01c402000ca03014021045100a0205280b80f81c4040c00b103000e255003483c801c07210300c0611095665a403800d1351481000815059031401c0380d02c02045800712441b90070880f80c40c4500468030079800350161a0032070b00058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 606047751 1250 606046501 606046523
    0x103050c1327060b030a0f0908160f060e030a1d0d02060c0c0d060c030c0c020906040e030403121e0f090303111e0f0c120703240207050715050304 64
    0x10100d650740d0042040c00321424400c0d07070300038500303890030b4010400285a5040055641d083c070103030f1070003692071182d1f0209944c0d0800d4010380001d500d03007044507041901c01c001180044007500e02442c4090102d840035041504019806098141c00702c01007074500b034180c0f1803000010120300c021140000003072005e64445500d0078042c2c058149003004040c80a980310070344003d50080c50001d00c03a8905e5010035154640d030b61204001c0f01d40c044c0f041117502c0065080c016041c1d085640001c84000005008034020350300c88401d103c0c480c1e420000c0e82c1c055079101c00c05802d104032520005054202040c5490b13140d041c01c8052620786d0740219903d11410b0b0880d41d90011007410f5440039210107441c07210840903489003000005034102c030b09c0095143d0b0010640603240c04030100100b00d1074000382c592481d22130082808920040580081c4601c122a170040300b00100c807401d80300396215810a9000310b0b840d6400001c56500b00800807488005481c030b0000000024500700c001198130707020494004020b18900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 606049001 1250 606047751 606047759
    0xf1b0307030b010e190c09030204060603050f041104091e061103011d040201140a120609020f040e09010902060d020a0828051f03082809031205130806060103050c13 72
    0x6503004e56800411303204996000007081c24100c003100c100203102d000040c5002814421032401703001e40c030010f0070031340780902071420584540841540050801405480440600940c0c0d4a4580004042030f8101a9003041c010315104884d143c91301d441e804440303142c540181e21211980040681c0d0682e007224040c003241d000e82c50f000c00d41c40f00c1c002d84141e050000c1404c2200c4030303004110041031020005da840c03403142c200342d00e04202a14100d4100075003050052140d42e0700f0300f0855003a501281c042150b104026102c2d0400140104002500070350001c10010b0300c0c078428003140d0014400008141c3d03c1040740d684005c011401d6005603a0b440d120147c0001c810003001d440350b04006e07001700740006084e040490503010b03404121019403085039092000b144001100e00c00505940b140c8600e481e00c2c2d241d011072107000410f0880e550000420060703045250203110303881807080d69540114112402030464480b070a10380d4644040382c41e940001d0030314000401c411080002e88524001848184c0703280743c14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 606050251 1250 606049001 606049019
    0x40b1c030302070632071b02130e070803070b0f1e070e0418170c03031603060906062703200d0506040b0f0702060123030f0f1b0307030b01 61
    0xb114041d00e1158461030721040e162038102e18200c100e842c844a10845d4a07402000d82c03d80314001345541e06200c462407468841c21407e210000c0707001e80c1282c1c003030300501c070030a240b000030010003400e090640310b0202d001c100508000300400c0c00d580950841a061365405a00851440e0103d80000109004610514019a150141c990401028208440080003402c04036040781d1000b00b011032142ca1344800b100510103101c001c00c1005994294143c5800381d5884611b5a13880003a140c0540b510183c4940c1521620951011002c0c1c800c4000600c501641c514000709450348180202034081c600b51101c40548440304080710449510180c400441030a12040c0320b0000011a0180c0d0400555814800003d40a01c5840c2c0700d240f15044483c443e0400d5500000a848000c100e9000d40d80444018410080d80c4520000d010030a1480c103402d00002402090034031501c04200035141c40341160b004101c000114500c190240b1070355814582c2500036041507a200c1e154840507000e0b441040040c002444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 606051501 1250 606050251 606050257
    0x1e0c0f04020d050c13090501051e030f0a050105040c06030e0c060906090a090516020d0801210b160e060a08010306110c030309010e060a060302221b090302040b1c030302 74
    0x9009000604228210b040041565000c50f8100140ca0340001c0380c5c03840746aa0715003000900403100081040b581000b010450300c01c12840c0051313521621035002c20043d50b040054507480914002901d50706500b80c681140600303000da50454218440e40d2000c5070b601c1c864440d00050390400002042c40b00c8002051041c0741d401288025001101000501001d0b211761081800601441c2e90000c0c030380c40c0c0462003170320031032201c2c114408542001d11008041a0306c00f000c58151108040e800e5000c03903c0151100701040d80c0c01004040c461a0410017620b01c003440b010b001008090303280c0804080c000b0013009003070f01c2500001c0c0d012801040050010408a520807080c2102402c07081e032901c2450082e0b1441e5400843e00c00307240380e4580010307050742c81c0d082c040981c0004000d4024031090b419a40024041c54040e0b00c0d8406200844110f0b51484181e60010904011924440030b8580d0401c00010000401404181d0046051040c845407034281950740250982c1000540d034140b01080d5001c8000c0c0d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 606052751 1250 606051501 606051529
    0x11a0906060d0c2703201e010318050c090606090d06180507080d0e0402041203030c021203070306080c0d0b0c030c040f0e0106031409030a0f020f010c080105031e0c 72
    0x2003000c0c920904e1060395860001650b0400180c1080c51524519007440d00c0d0b0464040803040d00c1e030344210280261240c000400c0060301e240c80c0e40c6008054407004a00404010b000c0c4260048011103560070300001007000e0a4203075041e00d40c0c0c10349655103014007100f0700c651210241c1120b14800040302050b001d5000c44159004c80c507071300c032110400d61503851a02e6241e40003142690080f0101d558800d810a030030f0070000348261010b5040a140c82071a018003500d4480c00b13414142c491049903d401d00c20b0014000d04526144140d03200c2c02c05c200000d00a05040c024078a02c0e202d0300d4a00c0c292880c10018810017140c0c805202005030303a131161120003540014200105801d002e1101140c0354141c000010064030659400302c0c4903604d40f280003801d6850711401020380d40c0001061005450380882100d05100c0c4504280d02520f40864080340f400c24803481035a682c0d480c021201e110076500110341412580708404480385e81d02400036004c018250380c1c2c4441c0d1030f035210407002c154604144811035009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 606054001 1250 606052751 606052757
    0xa0e01030b030f071508010b0a050d021605060702010e120313051009050309040506100c0221010207140c0a080601050108040c090e0601061b1e0c030c08011a0906060d0c 74
    0x900d07404001c60710b01407074a0325500707040c2c0244009000c0080c500100700840340c02490641021751425244045522650b03070070307608100340010780555403207440c1c0480d56141c071558003042403c1d076a41042500c1d10826204c0c1001542003400c070540340724000480040c1c0e50340c104140392450300c602c0d46140070381003408000c8a0380d010b0050a0000e41d4428414519400e0066029582d03841c0614104000c403807000300700901ca610b41200b0400c00503400004ca0b200030381c0c190b9074245800c00380700d010740c0304401c884004101c0790300025403903080004905103019500c0c0c068080b550919040f00030889440100d004e1500325901000040149620456000f43c00a000d2529001e90f503440301200420b403008078080982d42c3c1d010600400030503074482148030700c0180c83e5446802d104030a50b180840d0031140b001d802d40c1151006400300611541c402600011036211103511816640d0300000c47c080c002700ca12030980c1d01c035031100c026064108100c60070b2080000402603850b00001800684c004e00c10758880c1020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 606055251 1250 606054001 606054011
    0x1809070908030304050102040501021e100507021006030302011e18060f150303030b03070b0322020303190909141009051f060e1e0f010f021204031113050c0a0e0103 72
    0x1020781d0500055004038014000940d849081c400060310302410303511901c03103920360000c08064140011488840252100c00c0100d0251514401280f801c00705120304105613160440010405805501c2210503d07070087c2d0741d602d51071951982808461012007401c407103400c0301030290700180302544443c0031011802c0c0006051040e0800401c10401241c20440209646c1c040c448254901004100c0042c2480380c00e45181d841e06092141d00d5400001103001c0840c0d160800404554080c425907100359494090030702450741c1d03000c00500719612072292407001c500c0c195003406d080c0c90b60038071144285030a40c0b0850102d803800c150311006000003044101c1401c8001d0461885820032140c2400409903950b03401c0080035280100114072181410884034845069100ea51946a210008240d840b017402c1020240034082e030286c2c00c0000c0d041480e8003c100c001004010801020b0b01001209401d44000314010384118a00d0229074064415031401c240522881840300e104590f22541540c046c900414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 606056501 1250 606055251 606055259
    0x70e01050706150b0d1404020109050f01020a32190b0a0b0d060204050103110301050d080a050714010213050603071d030f03070f0506060306100501081b0d06060206070518090709 78
    0x1162403504121130b1510b00080801c0c85000c0c500401080745003505040109040950001e04844050300c50f4a01a05020407182000c1e0300a001d8070210b50f420000b40340c0100d030915550b0410445a14400101c0c240c1c10002e2451b035400000c212440a4a42c0001031405c501030720380e070500e030400501801d88180c0700c0c41481c505444204503220111b10400c009600e5605140006d01522001c003402c0c640410140010440742d5540c0b14211f00300c035044041c2c999500c020f10021129031080040181858050780c80041101d10154001e1140c3c40030780d11040c103d02e449000b0090244826140d040014824890282000d00801c80408249070700908542a0000408100d811a0001182030b15070100a05880040c02018840c85503c0401100980100e2400041590303e41102d400340c1e030304000700352000801c01c0d0b40b00c02141e1200000c28203125103601d16034155070b0140801c0e0203010010b0084c00f01041d02240107005480c254040e5149010b9149513241c2804200300d4010040701c00c004400100003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 606057751 1250 606056501 606056531
    0xe040303050c0d0f09230a020904080903031b07240e040e0d030f0f0501050105030c0309072d080f12130e040c0f05090c09120a02090910050f070e01050706 68
    0x3813460b01909a01168414041c01c04100c004041e20300c03a0300025045003101100b5402284a9031480d9048403141d1003034450b410a81c00d175002d00b05c043c03501888006000e49807c64581600704080c0c01d0a801c548400f40c071154510900380c54012448841c043c20110000c00f41d0199100c0151090003402c0000c1c4007500800951074401582c0310400032982d901d0307108480c0d03c02402107e1414880c00400c1c0b180d54035040008140d40300060000202c0f90340440031071882e100c00d0007030030000c04141704606200e100ca9640c0740244000e00a107007185c400801b4000075040d401007207100385014058068003000c80b003800b40c0352147d8081c0e03025246110005101151f110303840404640980d009a40c05620f07136062042c3e15950519076046240318112000800c200c1c68801c200315100e00209451685009401040a42c40c0000d04000254815500c1d03040099071400000c981c4e000c0082c41da8284140d8545241c4d11040c6a401d85255001802030309281006500400040030050b1058034002100c0e23240754414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 606059001 1250 606057751 606057761
    0x20a0b012c1e01090b150f1201090c0206090a03020d0c1b06031e020f27041e0b040e1905070807060903140c130b030a1b0306150e040303050c0d 63
    0x140d5810580b00201a660900014107038007400814004100440702600040c00705100d000309401d0309400002c0d81c0b000c0703075202e00555800c407403c2c1601050703d5071949605000303070280d070b03400400611401c4001001803a0000d06000a0342e01074014040350f0001140845d000000c01d02c00f6200c2045481c0c124614140004131800180b100303503000219048000b000e404145000f9502d81e02030390041c0701041c0c40c1c4203588111083d07103130515180ca00750302d043e401c08240e10344100005a482403504462040c2c00e0f40740200727813070346520b02141000300f40c0801c0100801c96201c444c0304001a4428460307100c02014410382c0400c024003980440c0c0c1050b035a00201d41c6011300a800640000c2c8a20604100300900018404c0440b05840c025245000c88100031800b65121a01b502e80b0468407031018400c0c41e2030900050500d60703001000c1d009001089566882469250b100860380305103080c4500007203440c1c0840d110705949a030f2400d990181c50360b407804c40c003a00000e00558100b400030801c000001002c2c0c410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 606060251 1250 606059001 606059011
    0x9030313050307060f12020d0b09040b01090e010e100c050405030706020a030314070c0f08191d0d0816060617010e010608031c0504060b060c07080d020a0b012c 70
    0xc0154450811007890300303003510380e88041c0900c2201c0c070f0010149500100c0050401c00c1c12030740141c440d1910404c05014180000c680c0f90801004401e2009000352104103d041e6180304070b06010041c1c008810728229400e10b4051411500070001031f1074025116048880c0006c1e16140c1517003000c0d1a0b0b000131341000c1070740c0d006c44050ba100c40000800c0540601a08050500400344114507151500c4083c2920b600c042c0300034803100080c4950340030882488207650500c000001041203e240c0d44001600315545c1c1d0914108603610045da0b00741600c0c100014420385c0780c2c4805000c0c1002c0085070071030306241c0c108104681d0300da1603807804503c41c0d10ba10b0074190024031150010411003003010446085030303240d40203103010303030010407103441c440d00302c414101964000b0100014059030303541040e00003840c003520625440b0100003506207041c50002600c43c15500c0c454191040b8985981e42030340e03506030380d4400500303044110004001c00901840d100236951001c06001c070182e0440000c1c010712038001c440c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 606061501 1250 606060251 606060277
    0x3050d02120c07060c03020901090b0c01060b03100302010e0a03050706051c112a060619080303070e0a0602070e010e060d02090f09010c050403080f09190e0a1103062103090303 77
    0x1012014440140107132174000020341030840c5400c0b6410002042c004403805401c0300001c00049050608e0070951020703000300300d035020280c6c490510001004410095100990004c1c030078581c100141c1c541020403030210390b031141c020442c20b46040320503107050700000c1994030760281d04122404410100d01480c0c1c004803d010040340d540d90302e50250001c040c12031801185001c40c00c02018400240011030b142c01c2001101c15545619018070a070100081c5034021130480d002c0442449107607a00403103060003003d400c0b80c000107115102c000403685d8088502c503206a80240c040100201c41c01c2203045078100c00042c11640d0014030035004294464030503a0a404116050070800505117001e00c2800074a400c20314000d0300d0a03185481d00070301801202e03403176506003200142500b40d607505d038242d50300309107507405c9074403189540c0320080007044204440f080780c0d00c1c2c03c0500c1c074004080008126441070100400c41d0240d03074501e4a4440306203d0b00d031000c46c0c45110030030000c95156410405000000401e107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 606062751 1250 606061501 606061507
    0x241812050c1302120a0e010b03160306050705030c070201140c030304030c0c080c0d14010b0a03060204080c090112030e0a05130203220317060612042a1203050d02120c 73
    0x828000030112648100d4a0070b4810301c4408030920840090036004000c403030010491b1590300110300d0041a0070851144d06110f044500d600020f145819102124040e40e800c0003150b4444500742d80c00d110403110410900d404115000043d0301074001100144c0c4a030b42c807241041c030001071480c559402504d00f07a010603484002c143c00c019590414401900350303c0d0260120022640204443c544502c1000700003003c02c038500c42c000c04003507009940102c0014500c28103940d49043c004002c1d4014024400e480c06040c0c04294542480440f280c1240c1d1100d8030000071080540382154000400c2c50115030250740400c002643d5581e40f111803250039000c5100595030700301210245284d00d206c11990503803000d00b82058000c2038204048030030b910540d0300703c2502591070200040c194420103d801b900d100c402030910050201492010083c1c880c2600210701c212207011000c0c001d00c01912032890070114020b00c0d140040d100f403010341850030b414a07025081081341080c0400c1d09404448000c103102c1c0c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 606064001 1250 606062751 606062773
    0x1122108090111090a060c080702090c0a02012a050703090509091005061e0d1a070f0f0c02101107082b090f0501050307051204110a24181205 62
    0x20302c03c0c101100c40d4680c6440c03030050300d040451075800d5944030f40f02c1440a100c5500c018450408111030107254000c009000c2813806c5040740c4104d400c00005280150301e0300e0000c0740d0b00850160081700d90f00119030280c51220380740d441100c0036400340d0b00480800c0000c00001446445082e01103001c0c07140c99001d4040d1074072030140402190f40040116105001c000b8590104515400400740b08060550b176000c103e240e80c3c2403040102c04008881421800950100078405611030056009406155240c002512403a60122071000550030080e5010015091410b4481e005000c003000c221883c0c416505803940c0d403e01c05041c070f044080005041444003c40d2600c0201c40780c00290483d600d41002c030202410300e580300409441601503d0705019000004c10102402642514030113111038600b8603842c6010303d00082940341040d60640a502c440c000230522440100301402030244011411070310720408a82110a03041c0c51403849d2151280f084045220480181291010790151005111305010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 606065251 1250 606064001 606064003
    0x71106070806100329150f250b071b0b0c0c0d1b060b0103060308071109060612040209072607080109020c2508031b010b010c0b0112210809 61
    0x4169031035800c0601d42544217604641c03580c8602e8524071100500d6560001d800007003070040700d070f044280310740440c0070980e0030390005000028118401c0000481070684030300c90b0110191021044014105020a00080c1d01503115a411141d0124541c9481480e250b80703884203034034020309450400e0881000511221282d1040004100401040c6421314480b01b01107803a0100d040388610091100b070b10746050981c140e2194112702c02a41d00002d0003669240c0320701c0c00d000d8103031501000c94003d104c000000b03505454220140c803a01c44403c0c1e005115030b56158204a011030b0020010024081d03554a035034400c1b54210441204910500908070203800c105102030f100c0c24050740100811401002071b1000c140b00400c0300410100f10700301c1e0004007020200c2030746115003070750000a02d81c803011440c24021070801d0038071420b1102040082000e000c4132801110ae0b65120007021304140c2c41d034801003100511154101c03004c28083ca81ca1121365085c400c100d0000325004c0f0600d000240c41e0310a1180d4504 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 606066501 1250 606065251 606065269
    0xc0c0501080f01090504081213060501090b010504171c0f02060916030312110c010b19150f020109290a0c0e150705030a02032101080703060203071106070806 69
    0x802420060000e01c0c090070341c154012014054101d016440304013040c10454004290380714203a1440300701c5c02602e0003c1400c450a0407554003075811074101b03000002c490545100301100c1d00c2060b07544c4c91500c2c6c10501004049082100d03503030043d10822007440710315090440b403404c01a086580320340c5244041c0303100070b10b0040040c24051507a005100c040c201c0c10b20f10504038040f07943c5401e0018601010401c140c2c000d22064495414490b000105081c0c03400d01035021325001c60b012036406180f036040038010703142401e450280d12030b41100080783c480e8441c0210000f1620020f10301c004500443c6641d1003242d08007015030301465503d400150142c000d140c10710010740c80b480d0b0a1041103111060600100795140500a40340103410341580070050085d004221001d00303401c41304580d9039400140009540383e200d0946100b11044c0781401e50507680002e0719075812194818002c0108500b103031a000020341c0042d01502c1400150342020514400501c402849441540c450036003034548601407004c080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 606067751 1250 606066501 606066509
    0x1a0307090204061d1206012702090f0103051906030804030209070806090402090705090a0806010f050a0b2505010507121a09011a0c15040c0f080606190b04060c0c 71
    0x90040c001401071039072001611070000e00904c01c11151038440c00102e11031030350fa01c440703883d00d0003140000b150f582032440c90041c480207007510401411180c2071102c0124018200c5040d4000310300705201001d50300c85e130020fa420401079000394200d032031121140c1c1c00710749031944119503243e4041420070a600c0c050401a03802952824001140c0c0382c000001030740350100900003881058040d0108075054403410a8400904006d001c1104a6407185c1e031036039444509102c0c00c1d07264060352401181c2410002040b008031003d250702e80d41024829041245460a80c14003241001048408000401d409010f114028603c98541400c04d0700981c0c1d10406803090403c02280c507841007210b010340340c2c851003000b0b0304480c401d01c0344c0382d01e0040040008946d4800d00b4910081445041c8130040c200326103c924a001f01d2080c444001c10980d22a407624050400b441102c8082d0041400111141040c08402e607032160800281c0120f10344904172440250419045000082d1101c0b10a0081103200313041c240142c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 606069001 1250 606067751 606067769
    0x1050106080f06120c030a06020d110a09030303020d0f18050c1e060f13060906081605040e0702010b0312090a0b0304050d0c0305040302040638042102041a0307 70
    0x2501c0c0c6850a10752981000c0c010318060031342c0000c0c00800305810b01c5008825000202950310003510390030b01c000a50007080380003000620700800100c0b969410000c64642882c661604881c2502e1500e050b0020f400c55030b4014503a40d190b8210386261095403186291140400e4000e800782903060802c14941061104494001e0000c4000d0542060305a0340b40741c440901150410b40e00e1460104482c902c5c01040c40b41004c9402e49140421002d4105035101d0950b40742d99140e48032036071b804181d603087c0910001c003900801c03020082480f5444103800782582c08a080d000104248007168042840c1c2090301145814903800814801010320300b06030098003c0c54160300f11800d508103600c41607150310382820190280003060701002c0c10540204103540046400032300400910780e840503050403040304544c51100b482c001d68110501c402a061601d1441c4012408060402c1d092603092803911100316035054454910361003000059071117010b1a9840202005d258a03802e48a400b85850a0359a030041e80132 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 606070251 1250 606069001 606069017
    0x50c2d03060c19140f040302132a05130621090206090d1e03080f16140a03110c010906060506070f020609040b040515030c0a0609150e0d031101050106 66
    0x121110010f664810400d1104070800d51601c520540704900c0101d5002e81160700401c4000c1c0251a18010340b088900a0340c1250070071101100305400c035026900b114140040e90b00800c102803540c01041100302105040c501d01d082e00d0301408801000944d0300050020386d1040308980356400200b001c41040e1240b03a402d0050b460154000f90590185101003402800c4801c06e00e02070125450140c0040515081e105414503101d00300104503120413122060f6510300c0f880816041c4505a807200c2500d812560b445a2900a454100040f64044d8110104154480f4540150130001c0401441100030f120000280581c1c28900101a900554400e03803203810148076141c081a8018440001c0781e60480c0c0b65917943d8204400600140040c1c17165a410174502010040c41c0350115082c036001e000c0c1102280c01e2110001d0400070002c0148c065000000d02d14042045840a40c0e111648403d1142c20410862016400801d078442e0101d501940000e00c802e246000c120300a00c55035024107154a42888 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 606071501 1250 606070251 606070261
    0x30602070c090e0129030312060109170105041a010302030a0f08091c0c0824091c02100f0b1810171609060b0906090a0506040b070b060303090d030c050c2d0306 70
    0x5100c1c050b04841e08d01059114000035501d82c82140341e0302c0508402c9003180c2107541e00c200f126009040894045038140b02145100c5020b8126008050403a540100101442c982e16a05d035960b80e20003202c00c6818100c103101d5050345941e41e440203801803180703441031180003095003000420506954464201c2c6c0e04010307004003400e001c010312507405501c0c000301c0d07000d03e13201c0b01e0800e803500c80d03440d094820a42c03004040082003580820400c041a500000034001016484010301c11100d04206060744600c0c2c00c880c078010681c05248490b405a500c0390390251096940d903c50b4501d4001c0202d00c045900010307110346402d4140007101010340461202003010a080c142d40d030480e03104441110303108031008a4052900d60322105000080c0c100a4074031501c2d80d90b200348082d0290450b00044030f400e5081d10000d842e0f4140001a0780c07901300d00034440982020252010381d40703560000006d0700c4070300903000d4030196a203480005a218001541d00340035a86088032801883c40745082d00c007031003a005a42405 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 606072751 1250 606071501 606071503
    0x110f150c1b100c0f240f050604060b4503100b01090e04050a2a06051603031d03161109060d14070e18060c13030602070c090e012903 58
    0x1040d126844011548110708030309100e020b5240e5172805108240000741d640d14049026005900f2014654609000544074841040107850107409641040001413002281da0035034001c484000d0407000c500004e02c1c0302c2e40e103031022801010b4210248451001901c1121a04003007104201078030010b4010005121000002040050705e40300b21000300340101c1c00309090000038404a22407a520902c0c090600d02c0100c0300480d0010084180f882800710950009000781c050001c0311700d03e24a0700000101000b060740d054008195051142c5800c4402d20200424100200000c1460b002c228403201070715440c614014003208080421607009a84d904140010350702e904426010781d0350301c4540043c1001c0d5182c0d10601d0721031240d001c09505a00c0300d05101e414107800b22105e011022400039188103581d01c01040b00c1c4c501c94212200b09081341c1440801c04900b0701c1d40642051841051125041c55582403c1c07000d640741c44800b2102655a28815054111041e40c0e607c8400001c0480c603207503412850000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 606074001 1250 606072751 606072767
    0x8010912170406050a0e1b010813081204030203090603090c040f020415120e0d08010801110a021b03010213060e090702010501050105160203010b03060907030b0606030103110f150c1b10 81
    0x108104d4903a00840c14030f05590300403000455608045481414045070302543c1c0c5440c440005000c0b404000100e19551407000c880d4a000d82c005014519100c400300c00708400c130100400c164218041406000a2035555200450143c000500140a2366802008010481c0e560b81c0c0410401c5104110401c40310a9062080d41d50890300d060403071650400750921800780c200e014507540240201440d8090b2a6000303180603040e140344070f000300440c50404030390b80320034841e540c43e52003d6400b12148134454162070800d050790010143c0051300780806254100ea210081d50170950110f0300c3c444003001c01c1d083c44125268000040d10090009504d0200080c125108040c01646031406d0201002e066440940151449050150032965a440c0100c0c0054880d82c0c103000c2220006050070200b5003e1910300b09603410380e9040116074000e90b40302020009489440030401e41c1282d10708030034500c200da084014094090910000c0d0801c0d0781e161400c10be000441d420428820070103924280401c540c040c0c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 606075251 1250 606074001 606074003
    0xf0b01080703020a031d070e0a0911190810020a0e1008060607080705060903030618060102030901030e010f0c0f0f03050f0f07140c03090103050108191b030507080109121704 76
    0x5030f0341d507941c0c0030450250540129085030710480440454605000040030701c00c44004029021160301c454007000190b0f00c61801c054680400c489010b18bd0386001c5c80300340310005040c6601d0324566600c0c1d01007820000d0f40d03219010f000f980030441901e0a5041440140140300445000d00544020310000d452048003604160050310049a607070100202c1c50104d800043e0042e00301d9030613140c144c019503526032080742d05600030085038044558108540c0112030159805030080c504001c7d140b00114010704180440c016250b4840700786400f4050a8800c44001c90f00903592004100700100b0b010b0a2030180004141c2010f20345800c02030074403020802c00750401d019800d60b601c42d459108084580c841001141d007005240020450124000000100754403c42a00c082c42642e0343c1d4003c69455280958001050101040c1020009000ea001d608a0104030040e00031486490351104d500c0c1c2641c40d00883c1e5981c5d5a41488000c1c031500d220380b60f07180441442d00c4000d100840c41152111040900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 606076501 1250 606075251 606075257
    0x10c0b0c03070c05010908041d07390b250206010b09060c0d05040302030606041b0c0525180606050406180e1e0916030201140c0f0f010f0b010807 64
    0x40840d600520070051000e041e03802400a0202e0346c418100601e45a0003889611b13440d80941c0c01000700c2030502d0003007500c24641d50b101c4a15018403000324000302d46011251201c074041400c4a800850307508005582414052031a134041860814440b5881e4280000c868140c004c1130a11400c42960004003603041d110340f07121494642001c1804901c0364026040c04585500400e651035410917030060151080320b008804443c500e8850005110858451480701c0d2010f007500d10b020a0b100e4020002e09881e180703e50300300c415904414900c42000c0442940382d0424a0a0313180800100a40440e402a018070596080004d6840e100d005011031140344611818040140308076051008409a05001071034915200d50051420300b0040389e2502c050001c0c042c016807004086102d1060015010075160201c050050840d81150015139520b60703e00c0340b420030301c44100000582400c0503c546054030800e240200820504034011a00f9282d00c481c010030b0356450000c003006140c0c1d00c94055504030078a42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 606077751 1250 606076501 606076507
    0x616050702042316050f030403081e1512010608070e100504020d0f0e120d1a060c0105070219050304060302030c1603050d06050402040b3009010614010c0b0c 69
    0x110210b0003030400300b59031001640c800e1102105550b22840c0d403a00c1540803901040301d104040c4010303220f6004451005002180900014000a010b003a1841d0010911079088010360a01050b0b00c85000003100c06001106915200798054204032906404085c0c5000080c025039041c520150b0751000640318a50440801c0400b10701840d40c200b243e0030151401901c10b540d140b0544031900c02520049442100751464680b100340d01c10310108007945046004c4040034505060560214040c0c104c42c1e0600010090000855800e03a451f40024800c1d00c90141c0041100d1a00c40006410401c0d41340040c16100c03c460004400594007100304c2e020348401d4240141c5a86684401c42c0312030241480400b807890360040d0b00310a040d0031502074075051178010400d0081d651200c09000c00c0c9e02070f03032040500010f805d01684454940f25204001600300e081c41c004898040342c40a292883c00644294980e81d642e02014400d4007145980700e11714040a0130101c0c50b01001d0355885a02a40013004c0c400aa4004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 606079001 1250 606077751 606077753
    0x80c0105070f050f0c1017060111150117070b070827090a1a10020a0605060d021c020a060c030e01031a12060a050603070305060a05041104020d0f0b010206160507 71
    0x740c00455800c1000c4455840b0b40d88109544e5000d2075941d284182007804010846e00d2058201c0544100d4103aa01d00b40c90b110703080156124030504504100e41d0140d001c0c0c10a0580c0101c43c1d42c0e000f006c5960441551005181c0803d0501036990400140d01c04100021070200e045402254080c1202c0356040e910300201c40c41c42c4094254006400303a1185062040c03000521054000160706018031501c0070b50922120108101d80301c0c1e8608a902503001600d2100114a50f5440164043e0300036240c40000e03082035001510a000c0030b5000956814070001c0c0750190b0402c0c0c9451000b800d1716040100114586031006018100300700c2510381007507182d080c0703080c90314001c1c414102c03074450244c10200b050110100c1151074500c01c0380d44c0d1410341c0c54100011490701d00041e40c0c00031241c004010300b526845c1c00d080b010242c02d005200f80c40164082e040d081d0f442d21103100a200c3c5407032034000083c0200340340c0081c03025038a40b0031031641154000702c01e204112450f9041e40104480c6418115660210303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 606080251 1250 606079001 606079013
    0xf090f1b121a070f020712050102091903030e030606060d0b0d0203010f0204031e0c03080c0705030d08041101112a04230106020106080705010e0316031218080c010507 73
    0x400d4100101081081190404200e2000d001d40ba54140d90711004a032940d9825045920038100225500180d010314410400f110800342810281c0d4090400585031020b1540810780e510f02020151440d1041c0500400a0560110203d04001001c40c040c209c2d41c20315100086d03260142c4140c2c0d00e66103586515412455480c0510001505e0307010340288108802900e10000a421902c0180ea0b054100e41d04c160801d1548480c01a0f11544001090090741c2540c4490200b500105c0d80d18680303100b0039102081c1c9940400490840501c40e554904180c54a0700e440c047c181d600030a2141170120980c2c150080b503101244014003200d0720400340251101007099194800905c10b003058000d807411142102a0b440c07040224503000f4a880c81142c0c070790380d8100c100d088501e03a2041c441c840c0c110113000c0c050356102d004600002d49008040f1181e40080904000c01180e050703000b155000480340006030016046501024032200d180c05283e00c151400c82d81d40d88410390a2076440c10010002103600030001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 606081501 1250 606080251 606080303
    0xc06030614270a021801030902031b0d0b10060e010f020c01030b0a05120d090b0304051504030c20010f0302161203090f0b0f0f090a11040e030f07060f090f 68
    0x40500c800b003003030803c407070003000070740c4446552255821a42d0700130b245940203016000c14180c0c0a030040011600e082c110038915201302501903031100d030304041c2d0000308a040007418090500c41075403401c483c0c60028003504ca0817258400c2414000302d0004040c40300d8011402c0f100c0d0910a00300030655104000000d10400026007120354040c034030480340040c461000610324020302e519114a40499125221011180000c0310010115030000e8140d24005207103a9442e5001391081c10103c40c44600c69a81e00c8140b0301c6c80c030169400c0c0c03ca4900140075503901041014900480341400c628140012208643c06a80c0b020058054500e001d1590b254520981c8500310b503d0b0864088a020b10881c600340c9038141c0161110980c0b110f0400116105101104600d4090070700c000091803a80c04130381e14125405c404440d00c55005d0b54900e0148541c8400780300501040c0d040c0c0c10319954600c0c2d40c1c50181e00300c0d2280360351503148030318040310a00000c81c1d086d00b00c20016005030300715520324950518142025 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 606082751 1250 606081501 606081559
    0xb0613060b070f1109061309081c0902150f04030b0603031902030a090603050c07030f0e13090203150c0919080d0c11030625021507020303040c06030614 67
    0x1880040c80c80c1c01d000c24500f00308070703040c030a80c00c500d4440790361400c105a0482c262220f035030090320703450100c4880e401e56200001451082c01c4407403c03c60010040300b64200000441000300f51a40c00d0300045113442200c40f1341305100055030724140b401e03595804000c0d0069000c014451006003003c00d055175802c005480ca0b20322201408150000c15100094403a003000b82c039200403032802d00004c12454002d0207054440c0291b81e4205003013502c02e490850714114424503a00901c06101d003030781c0f0b054a403407107004c1c84115401c030040b45001c6188107261500401c2c1d4103547c0044848024410081c100f04d0469170803030760844500c0c0b41507412481c0e42c0b44c4840c083e440091603200b24075001c00810b410000c0f02d0310080c014500395a0001e4150185a00c0e040221004000304204c8494080031008501e1100c0b104162407045030410072501d104010300d91015901040542c1c4084200402c110f548400400502514601800710030310b00b00640018240f605034443c0f18070180354581d814022a00e203848010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 606084001 1250 606082751 606082769
    0x403080a020c160324200304150905030c0c0303070b0103030309021201060e0a0f231003060e010f0e1b061b011b020c010e13020c01090c0810180b061306 67
    0x90f40c1d60f45400c0f00d406a0305d14440d0501d001e00c501150b0520b60500c148521036000c0c50000700c415204100090040d8002070013110141c00b0044810b074074054900c180303003449114100447d69019043c00651802c0084d2001a04c203a0081140b03500080d80002007504481d4141008107880c0001e2001540380e124507403900145620301040002e11413000c00030a80030750140315040050b00c0d401e180410a65207040f90803521075149880c80c1c5420058031084a50000c0e90520f64071461b0b48030383c3c07a0015581180d411910366034450a05003039038085841030401b07990794240281100340d82e018100d05099000d0403030520070b40001c50103418142212a410044100f0f01d40200b185010b04180071503c407000b07600c036100600c1401403003441ca50080320f1030585c840c0700a044001702e103980c80340540a5400100b5401440d500c2d000030000140a024071600945030700d00182c1a80414046a501140c040b80c0b4280b0305ca1900080e0310b400f1419a030146500a1000d841110705400340c1260080035240541c803460034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 606085251 1250 606084001 606084043
    0x7050904050a020f0a0b18010201020417031905070507030f020607080c06151e0d1a280501030210030c02070305070605120f060604150c080a031a090403080a020c 71
    0x10071002003003a006041c422540d0011400101007402124140c1d4014440480001c000650750300c29100e0401046a2051001628168440910585140c5c1c84017903280b0517803001c41d01c3c1582907400b040305100c501da85c2c50010304216450315003030351303402c40c034400a00101440408082952591002c86aa198010700c40540d03e90010011b281c0d200c0301110540c2055500c0c24001c409483e041c1c0c004000360908061074564010ba000c1003014000000904455014000c110303c0e00005400507000d01c0741e801e60311500761700e104030724002c1c401e0350691903082185883c0400500040c0c0e21409201821001454001142050a04183c1c501000d5800140c5544150807001912942c400018900a50410203400302516800642220840151103031584400c0900003030200e0300c070742e250803210b502c10351400e0390003000691658111544102420800641c50301d81c0098050045503680c101d69000365110780681c50310b17403002814108058240c1109680005501e08802d10030814200b0034441800154030f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 606086501 1250 606085251 606085253
    0x31e071419052b0807060b1509010e0303120108070e15010206010911070203070e06100315060e030a06020c010609060e1b0c1e0604030305060306090c150408030d06091503031e0207050904 82
    0x142c0d40d040b12408686079414240100301e035003422380002c0800c0d805d15401d81d091450035401500c1c81ca8a502e5a244c251009004820070a121104440e000b17001c1c10f006007031800d00304040110608002056812541d9030100d402c3c082d43d84c00980c880c11281c1c10140060011403081d090402d5105400f0060760510802c03a010540c5500440e0450240c01d045800d104c180410b0321050b02034030039078a0803604c0300398248010400079006502c00b110b0f510b001400d0b50003100d080d64844c802c03604800907144803130f90344542c103100c041454412640503240c0030a5100451500b800c01c0c00b0040342e521220000700502003906c1e040000100040e00f42040e1030b076007100004039440c102940c0c6520031641580000d090402180c007030b05010031081d008042520240501c42d9510b805d00c84404c00c1100141800282000002034245060018000609078071202058480c03410142c2020780795846551004161200420000250445181602d1035050041e090146d848550240c1c1000c9031940165000000402004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 606087751 1250 606086501 606086513
    0x1803050a06050f180604060b041107110306060d08090103090212030412021e01090632070b090313120602194802031e071419052b 57
    0x1849144682540c2500356542c421541310805001090159030708000e0120740452011b030408038a2520182020581c03440425100d5000e500101050360111b0880030550010710303043c4445504020100c4200102100d235460391423180c40350200e0581495030b5030354a40119200c00c03600096410681d401d0760341303807983c4d0a61610751070b140b403208a00c01e54146850700c41e0000c0200003107040c0c03541a51070302c0340e40b4100402a1141d5080c44038201c248542e00c0070b6222100303c0c000c610600710851141407929039455142100b0302450140590300035070818050480c4002401034000c040340c0c030400d000741201143d0b0400000910421a002e210086600c000d500c0b00c0d500700361103000d659050282d5034411b074810240901c02c40e0105084d201c50700321500030304150741542030141803a14001010303034451202c100500001a1035290f021403054005520130032400c0c0c00c0042414803030780140c03038011f0820303400708021842c2200740c043c040c85a03180490b400700341c1d003111800c8104e0803149031317900030320a04a050003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 606089001 1250 606087751 606087761
    0x2030105011e0b040f05010810031704060f0f0e0d02180c070213020a02030306061b0f1e010618050702120d0b122406040e03031509060a0f061803050a06 67
    0x80b500c0d4420480340001c1c0c9107602c0d412501105c0100c0e8820100c5414040111905107001c3c040070420006d2241c0840803c1c0b861032040c24801e000b00711265a24070f855000741c0103a02180061080c0981c110b13880408035002a50141500403c6442c00441581440011034120491210000c640e4030f541c100011801520000d100780303030007100c4c414406108a559102640702e0300890360016002400450414240500903000c180030720030b40d6080c80400070386134a1905038400707440070080d48062080c407410100200c1d41400203151000900190381480c03802400c004019240c4270401c0d68034400690220310a110040001f6050500f081c0d035149001d1080c40a000070302002440350b0f65168540114070b038002900800b90310406040c10181c400c0040c2c000c00480b00920f619002500c0d03a255511380a02440250f118030004094000c1e02d022680c14032031007200c000d1a65024028001042c0024840700845030226413031881c0250f034901c400040807400713503040d5100030074601c5103d070001c0030008280c03c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 606090251 1250 606089001 606089039
    0x705060f04031e14070f020603090c04060909050703080306030312131208070f0311130e040605070906051204020d0c0305061905011a180a150206072d09030203010501 73
    0x60003106102410144454101e6081c0d408040707400380d1602d003c8803195402603c031841c007501001b0038202c01900818542e91003200c0d480203541250468002c90300d054840d19029261089040109005070758a07607560784e002c1c1c00040c00d8010702000184050344c04100b01e5003400160149406103090502070b10751151190042118010761311070880c00f225204807102c5208205640e13a40041c41e154507000c0e001448059913540030028104207940c180c55a04150030010501202011070601c0c103070500400b29007014014004100e00d43c8000c00449070700101f5a103206c60042c1c40300801e0f0701e85100040105c0e49031803000f00240941301d80002841000303c1c68601c11082c0e0807a84042c40f2100c0304480443c0d600f402410040d00b540901d250401a04002a210b080c2105404800c070343c80740300019a034021982c1c8a041801c0700803041e020000c0d8140700c07581c0c0002a90601c1b07001002c40c004d0080c414641d0342a0a201c01c04004014110a803244039640300840d000b400800c02c2d07507100c9100002c1080e503904 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 606091501 1250 606090251 606090257
    0x3080414090f01061808030a09050103060b070206120c04050307030b0402042a140909090f070b040515030411040504060204050f060313030318120509130e060105040506060705060f0403 81
    0x601196a09010031460b00c40c052030352280c5100c2e0f00b009420354005111581c1a11041d00c22078010407061401c0004004080d03007502e524202c0c0b807403c0f0006081d64a20307001152000300030f03c40c2000517100c00081c0c0314003118050614101c3c0c1d492400006c158021640000d038513204098001041c0b01000341d401e800f460082c2c80074400100c1d140000800084040c04032008800c4415008080f17a115a01c40070410704440709040ca080e120900003008100255014a100d401c5203170b8400c3c1a4000704201c10003400003040c103a051529010000d640c1042e030300e8040f49404070020000c1c041040d1400411000c520090040041d42440e06010340250064001c9074095241d50710103019520303200040d28415507211050000508141c0c2c0c048024280010400d90505481c414050014a000410f1800048140e403100c0d1641189800c01c1200082050001c001901e4040030103401c101c00702c0c2c2c0c01c1c11340f0420390700441c064031a0704c04203182e40300c2e050024180307025150074000480032140146003e24040da07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 606092751 1250 606091501 606091529
    0x151202030a021c02090901030210030f09121e1407140a0f060e030708160501060b0408030a140403021c081e0c100c09030609032d0305090304080309040b120304030804 73
    0x3e09000320300c1503140b07482d0700c0341c05400100010319000600401c0d421403440c001c90b2094000140ca815240e64100c1254031900d440c002d501d406910201070f8101110424210f1540d403013a002c0a441c02068100d140400301c0001008400d00115140407488440750504442c2c500020f070070000c0c0e4410000c0c0c4102c40c01801d007240e000e01810004103440300d8541007007002d4540b0b450103249103005548180d08451654030741900007040719045014000038000040515940c0c101454014020380c40c1c203010b003a47d00c005000c02d10142c0c850308115180760841c0f4030036141c18291410320060a0082c0c101c102c1004c640c40c80c0c1601c00c1c8060340c0140404040010485240c1601084007405403950803001c04001107109404001080790b58104200ac0c1d4001e040c480610107000f1480c2e40d0308004107280091443c60380114001c465030603c0340e40d0b440382c60b6101460426045c00d0a0640764400c42d01d60740d210b2a00c4200442c110781c0c441182c00008410f410440366650340e06d1810a00a400c1446001c403016820 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 606094001 1250 606092751 606092797
    0x120c170c0a0309090e070b180a0b1903090b06061c1514030102040b031f0914041109240a0906090501030203060c07020f040c020a0b0405070f0b0c0601151202030a02 72
    0x13902840410120180140a04504080103940c480c7c0140c1c0b00503001428403c0031400a0301c811441c3c8010340404400c0a170384015228003000c4442e6021409420503107007014010208200d0140650030000450b5401d950f003d04c040410703005c1d4100d99011031410700c3e00d40c104007000380d84a6000211032540741066030540c007890406080b40501e120328000642c08100003116040448120212040c4d6150014403c6803290311000c00c8420031407032034842101c40740030302c4140078020411503030711001290002036601d0290b403403142d8034494454410405050141100003941e911687d0805002155010050241d44140d901302429081c80140d0181c041d43c408075042c04444c004035035149030060030f9201c000e101c0c00184402801010f100c41c0841c041c24901900051481c802030b030213140240000e184c41c80c14950240b05801050b8070008221800b000141444034010402d107044608982400c88031000e0550b0948501162603084124a8400400c000c07040000d0f0707014140402442d2082c2c5a02408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 606095251 1250 606094001 606094019
    0x5071e0905030a120903080304080d05010803270d140d0801080613080f090424051017091507020d030506100e09041104020406091701020403120c170c0a0309 69
    0x568001c10782c254005203444000702d0058252501c002c18079107070004500e43d49482d100001e41041d2412a07903004001220300c4000c0c4117000d5140508490000307980340c01c140850b04407100400071031403001700158070ba05070b4040c1d4544076000f00c1590070442106640740b034022100d0720352000c110818042000c0e5000810080e03000182c0c81e20030311450100c220001e1a5898003a1540c02c0801380c065100c908104190141c0ca03a800743d00540c1d054100801040c0c00c5c00300031090000360940220340034405580410440c0b40e4000c82404501c522041c084d402d40d00c40404c024200305c49900904000c600d43d07028045030741d80c00540d162000030103603010406c80d04c4401c208040f034900800807400080e94001c0c20282842d000c02d1242c1c2003489081c0ca0185d12200d0341c0071509a8005601000103c0c14003a420031460380e411030300c0004440c60a00840c034141c15940c4d12280140c50714074440401c80313a518403134100301f070701e50f20001c048008034111030702c915084003d59a10500b4030405c40004071450000255690 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 606096501 1250 606095251 606095267
    0x503100e010c081003082a0f0709150306020708090409140c1906050d06080d180504020f030c07030c05030304230d0206060607050102121303091703030403030f0b0405071e 75
    0x401e80c030704c8044c6171a41e100c0f2489500310030345111001d4480b621900f628503180c801e441d01658460080c22029840b40f0010381000300c5d9034414841c0f58100000000c210140070f06210a0f40d82c00000182c40d5070941c200120310340030300001181c01924020011040c042169444194080f100301182c0d00d4642440c14040c80740c0d01100d080c3c44c0b88060500a20850703003d9800361500b0200f007540000d00c999920781c850b241401461a40004c03034099001180c1c22105d01c0800b1024103401e43d0294a4000342180902075880024809108848040703827030001c25124514501015030082c1c03c0301e4403802d00d03040804c0044001c1d1005000641400310100301e442000c5040b00c0ca100154000e481c0e140c0e5210140841c80e80194021107803554200011864016441c011074000c404040700c0c034038800c0710381c90007800c42d09081d0400710074400b00312511031506100100300c170740c0180e041c64003040c1130f00c5241601c00038140c6c146005da8058100b20030480c1296000f000d0301c40d01c1014030220042e40480c0e11058480d45 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 606097751 1250 606096501 606096511
    0x601080a08190309170c07050105030c04051002070306050408030117191709090f060306090a05100c0512090105040b10061b08070b071e11150a060503100e010c08 71
    0x40144005070b290500c2100c801d000800b01e040c081811061039545080d0302036070007480c01804101244000071041d003084180040e00c400c0c2402071443c01c100408ca881800307103109103481220200000e800b007600c00d0201c50011540440b007400140ae080c600784031075800901075400f002000310724103007441e4000103440081405200900c02d40c800c0d6500c0e86403103400480b110340c5081004014840c05034481b02c1d041d41c81400358120100c000d0521a04140c20b121003e072140d5020f0f482458010085100130a114480e24081c2d5000a81001200c030b081e01c0c6d074000e0041003615030564404011800b0f006400040c4070300d0ec140712413901c40d66408418580e03800180034160008246085003501d4007030180c0100942070040d01404d08108013540e80d0140c005c0c2c200c0300d41c2c1c0020708070f0790b0515900818441e0000c0d80308444c1000e103c40055503d0055541041807034582c4004060004900414241e5004002501e005400d07240c25a00062003030000d800c00034998410780d881e180c0a104214840c034a44c40c011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 606099001 1250 606097751 606097763
    0x30e01090b191e17010501050301051305090c06071a07030608030a05090f0a1d0105040908090103090f0203160303091e05090a020c07032a0e0610050c010f06080601080a 74
    0x100d40da00b2110842c4010340d002d84140216510b00650701e4450720b00c84520074189a5440302c0d01540b110b41c00c1080380c2c041c1c0c4079030306020051006101540d2140c003a0034010711041d0000a80750fa911000700e00e85050301c07040d140c00102c0050603000748a00c1080d464448115010980c4882e12002d0701241103482e43d200700c090642052151400c0300d4403800c02071044010051502c001e4408410014a18800c1c5600c400c0c08041030518a050a000103200940102404c0f242000080242d0f12076818922800190707a0400d96203c80000030048140303032030305820360094201e0351222004003903e070545565020a0f004244c07070700b00025014903500480302d440700241c101445004c0c642824820301c004c000d07011401881e0240700080c6d411000700b00c0000154007c608040070340e0031a0100c0800100e4164020320300d40c20081e02402002e0102c03400075000340d421394034016509080a0110b80c20700030511104455400e00b6031036032222a080d000351080d685001e0a0b1001030b61307590403880d80d40800070001014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 606100251 1250 606099001 606099007
    0x70b10140402070503040b0f030603060f04030801060c1b26070308040e0c04080607091d04020109060f121407020c030307030c0206090f060d0c2705120f0303090a030e01090b 76
    0xc41d0401d9005408494410800c80e410241c440c010364401d030b002518614050640071007007080c14602080007540041e11240b00170424102910700511512050190300300703000120000104203d84890314a620361031444411080b59282c07002c001310100880c925071080e0091459022002d00d01055500c201d03603001c9a20380c075040c0741c4040000e95980042c02102e4051007800001100001130007000c1c421241c40e50390504180c2030041c0400d80c001c0000030500388080302d03410000180d81280c1e20500366101803c10700c004810000045035190a01e0004440705410902616160110801c040d40103008640941b0790080540e0189a520b00030311034041e000880e690020740c090b09051000b0240044e014040c403403051041c1022a40950000e0401a1a50350b90701024a000b41d000125031652403d050401c40284214030795601d004d0303014003c3c180304000c0003540c0d001955080080c0800d009460341520744a2030721070a2140c035501e9102085e40815940c0306641c40c198802c4490b00143d500352400c083c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 606101501 1250 606100251 606100289
    0x3060e010b2b09050f300d051f08060405061617150901030305071b060903020f2e020d091a0a0306080102161a0f060d03090e010b070b10 60
    0x44a10011854810b0b86541c070706901001c90800d00c040f078002101c400050400104540d5011096000c688452074658010213008070750144050480f42c495082d45004a401c3d00c0354046200b00b0b00300c03407404490790304c03004030001003e100202d181407040d40039400303640442d52070041610220454090314070025a220144030b007200000078100781c100000001b666107100483c0c000c40c070241d2003a0420f03400f10340041070f040c0801c54209c0c040034640b0f604086008403d464007801500010540c0002072099020300601007160b121019900404d22070008649040e031601c2d498900a1503200c50440014003e014184216170300a00c9024112040074003041c2c0d1b148004210010303075811a044140406171110f400059601c02400a881c0c1a1458005041c048282d4500760300c0f140c40303105456040c0407030301c410000c0c0390000e4041158002401d68000081803c01d00c0e0403240c10983e034000c580503010501c000314513420040007800800d44100549103964560384a40f0b0f41d20310183c420403a005c6000b980040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 606102751 1250 606101501 606101557
    0x901151d0108010209100f122a090503030a030908070602032a040e13061b021605011110020f04080a05010c1b020306071409130c0e1005070209220303060e010b 70
    0x47c19080a803800d00f0032445200520710554003030791216100e2004003000c41d894800300401e0214403e0050504402e1245800301094890084a150704249562220002d003803003951022a0003056010f4001c5560345490426018507016280260100d0801080c00e03d210308800700888090344c807040c0050b1410703038402d10f540e204240c900808542e865142c220310706c42184003240c202c911400e241c01618001c94104441113070507903c0d034001030401508005000c492040401d000c0d200c4c01d0300413405a55881034103115a800d2040d42d004800c1840307260b105405100c0306500c004080d4a0a503203c2118840204a45080d21040c40001c3c1d4190050008580498082c44910b8042003040c0d8405080a881c000020000402c460300f401001d030300e4031480c42c0c1c500d9200080c6030707000008603020480c4058841e80140740b8005c5c204002e005c1d00500020641d03848204045590001d00503c2813200c1901038900100a0111889082d614400c00300c004280c0cac841940a4610003451901300b20b4011420031411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 606104001 1250 606102751 606102767
    0x7050d0810030c2309070c0b1b3f0109060e0402031f06080d0e2809021c0507120f06060f030f1d0d020609070501170901151d010801020910 61
    0xc03015043c184c0d4140000c2c4c0b9100d01191181031903031524079551109043c00c03110240c2c01410095400e10b000141a101000c00003900c01071b04419071104084111001c48003030702c5d008031003001900d40d62880050240f580c3c0205440c140e07a4034510501c0303155580d01d8083e000716425100254160000c0e2020700310840c000c1c2070b007001c0b040d503101c0209030755969007800e504103000d5201d03003400941e18901c81d00c82d0b03040c21803220070a903103040010f440d0300505c4580c18400741058058400d4082d0005020280040c24880c80c1303c1c1c0c014042c004211a00b044000a001c1961400c08680c01e00e040030100100d401440c4150000c0f50740700d440e24503003c50b201e01d0460060000004400c4855a1445071842260b1504040403001803c44000c0405c2440440c0280c98034400502c3c211035907020140c00d100c01c0e40c1c014441c1d03107003400e1407045440a40f00c404980d4007620a01d4416200c910215400040e0200e00c046e21140b00e0404418281044e609c0d5080d030b074203034840d0200a079041200030910b2a41503100d0042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 606105251 1250 606104001 606104039
    0xc03030c0e04020a110c06090d03110f06070503180d050a120603060e0f10110703050307112e02070c17070b270f0904061d010207050d0810030c 63
    0x700c200c02800141c02c0f80c1044903100e000540800200d4022201000700b0000528200c50090905d144840052500542954010100041e0a1604800c21030400040c60720140520517181e4510f0306040051003500120f901036845892101c000e082043c0200362440c40010039500d03207141440d401010ba43c035100f0540c010340656511031000020031598480c4c510340c024204081e01c0d054006842c1c03103290001e11080841c41c40d00c2c011503400301040309012070300039a034541401a1240d68001d010b4610640003458540306005001d40021850624554040d601c802089041c1c88035140182040481c040c54200400031075440384140002003c03d4000e00d03071740c506081290038280e168107a0011a41003c00b04000903403803625480303a0a000140180c0e0400802e4a003820305008880c00034050343c1000d8000382c81c01d50784e0a050385a00d25042c0300b904100b42810020356803520381b4275100340d4a1600031034010004000174042040403442114640c101c0b40c10102c5c149141c1d041001101190b094009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 606106501 1250 606105251 606105257
    0x1050a080f060a0e091506060a1e03020702030d0906081005030a0204180206070b040215031e0a0e1e0106060e032104030f050a030e030d0c031808031210150c03030c 72
    0x200144d4900d84203802c0d407080c607001e4041e0008010044132900c484001408041c89040d040c001c40180c650300038220002d0395032965240c02c00c03110386007042e0001d12900310041d40500030b806030001d215800c00c40b1a01245c4660303480c0035140d503d2510081419849014140c0d02d608148001409407900b9085002c0c841c10301107001e00a401144c0c0082d465a000e0742c030882e00802c00714100300551030814640045642c80300e020900d140707407110002a00c00541c0c100c0201c10007214000c51030780f642543c09050904804d03011038a900c06424a54542001c6942d0828140d40c00c021010520f140304506890340c0140140007801c4000c0010b06281007036441142c43c0c01c00420900000022482030300180c54141d0080d00500704007003036403e00920501400407110b001317501c14580a0080759100b0040d401705605450a00b100c0c410388030380606400314035072040115200c0451078a0308107005e0a402809030241070140a02c40b60b603004000383e180041d001c2140418504034100c808030340207402c1043ca041c4149 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 606107751 1250 606106501 606106519
    0x14070c050c01030606090626011e0f0e040312060f12200a0b030a0f0c0527150c0a0510022503090e07050d0609020c070902040b030a090305070b01030b0609010501050a080f06 76
    0x8c402d059540903402140c1c0d86002540000e1103581e2a08410082d1848441a2040500340341504820302c101500007020400b01c8a003034140081d680d88900007800d50841e19554181d40c940c1742c5000c8003005102a41c111300111199050100702031618140c003140035126030002031401c01814a40e0300010560990141c55051403008800b041c0708540700c250070360b00c4182d12090303021420010640f90341c041c2031981e824000319514903a10b8040703c1845891000901d035450810141d010f083c580400c100501c2c03449100381503005000c940d0041e008091864840e140c0c0101c10810034200c00c4000310307001d00800d100d03130810b004119038940c4582d032000b1917003080e0b840c091584003007101b240c55640c0008072072640132440021f040303001c0c00740000411448009500b0b260908405480e04c0c0b001a28402406a5941c0e01c142014050410b40d01c2060b04115100215039403801c1c85101824100e800d94442c00b0310000210301580600180c1300c0940c85580c404419a48480301c4c448400f1001c0e081a80c403690700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 606109001 1250 606107751 606107807
    0x100e04140a03200309010e060c010b04090b041403160303092102071a0a1707021207080909010b03070c020d0c0503010e0708010b040606140d14070c050c010306060906 73
    0x1007010141880c4240d407900040800416202d000c0105200d40000300d07002081801c10b81da038840001c1544440071500d560f034460101540900400103048141d800500781041c4070107000450700c1580c07095000300310f0070000c50906040640c80e031052140019014010640d5a07010070f200b940045480c600c2500c5190748030a80410107000d035007031140c13103000503402088140003918261001c03165105100a410b4108010300b10003400500e0790481c050b55070079500c2d0014000780c3c82089030600320800c1d504001d40e142003504003035070349030701c4008100e000341c0c0d945c0c1c00011541500c60480380f0401465403800c1c07050b1840d6082042d82d42d0f101c5026224082c40d01c03000b08140d9020310540ba0780004d408020503029103070003041401e507403145601c91301c6140f428801700030031600004411034020110a1203036640c0c070040c2e0b004004100d607400b070f6406a5869020400750a0300f100907000c000d40900200c42c801704400340110b0958245001e160f0018414003003c0103000d00a0702a10f07880d800c00d14035041000702c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 606110251 1250 606109001 606109003
    0xf12090a0b010e0a0c0801060f111908070303050906040b01090b01090801020a050d06080d020618010609020f1213082d0a090f1a040e060d05070f05010e09100e0414 72
    0x3a0003c0008040c01803e102800c40f45202c2d00c102d07000300b4100200250302d42500601200008003809041c40034101810340701520a00c8004414048070300c4803544a501c03418545070b55040040120082031030007001c10030501000400900c51580138400c01010381c00d00f00c180300a07000b0745e0f030b0550600c1103040f03020030462400c0c006010340110365603c4907219070041d240b00c2e00341c81590f0311000182e001044070503215a404103000d80d01002143c2040b40741e140c0c0021246c010242139100054407440801e19244102008004190310110502e01d9003541e200c0c50601c0c00d01003416000180441d00c204415600b084400090800903500c0501e902c0d07c801c02e07001410703210b034000c404c08800980f10840500032500710200d42d81c0901610064800054030441c0c10300c182e4400c81c010903001107298400220613075109031580071130540c00700c10b40b005640d860000d90000c1d6464082d55000c40c0081c01c00e03403090300301640c269104411801d941a215494001c40e01c1030280094000d441d1071a07080850480154 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 606111501 1250 606110251 606110273
    0x904060b040b18060103020a1701030804030c0e13020f01020c090f040b130b07140c010903030b1c0201081311032e020702090f06040204090e01060f08030f12090a 71
    0x1004000104149030518100011240c051040300d2055000d00804001050001c888a5200c0300a007401a900c004035402900c11361180b5034405001850300b0300110800244a01800c1140e00c5212103a2045440d4404601040001c584504180081d01c0c2c0440c05840c0c008802c91a520040c0180c841007180d0802169000e6011150300c2600c20121080c007041090001c440303a440a42c100042c1c40c00c1510b644c494400c0400940420200030303101070420440340012003141d8240c1b608a0080119100301c2c40e02130302a000380c5685500c107040b40c50304008520140003013040b09a60503500c1c0c182650354900505004200b41d0029106200c07412404002c9442c1000b0140449000041d40451944808024100c100f6012001200c043c01032103d803006032608882d41b900b10382400c41400607a80c4410108009019903401141c090341407d005001b107501c198891800d884504c0d60340c070a03580d140d5049541c1d9100f03600e400c41c80c5182c200441c00e54001007542c02038000c03003044107640c00750f03402d0745130062096 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 606112751 1250 606111501 606111503
    0x50304150e07062c0d06090201140a0e03061005010c03031104080a030504032a0e0402120d0e010e03061e09100603110405090a03050301060302090105090d08091822020f0904 76
    0x1640c54030000c40101051100d100c1d032030300f94000c1040150580b0021512417048400028000c42d01c54240a08583c00758060440c04405000c055840d032407a10700007400b40c086045010b0183c010200810005070040c801a401d0310b02c107031207100705000280c2d8220010700111040c1c0f00d461030180f1020600080038080740180038000d80e1619242d509606041c0c100080700d80c0700080d52003048100000c00d441840b440001c441642d6180746c444d541e10b002140a441207404d85840324010521012901a080341100054800c00c3c0c0c0c400010941041c2030540ea600c0546918044d98050385c01d0300865203d8965030340d4011070300070989464680d80c105010503180140c10894101290f043e0074103441c00c02e8440c0b1540300c07803601d004008424064170043c10505c0f040c09440c040640000704c1110710f90045c400c503003507400c000e0418440d54900e130400d106550403507810070340300d02c02c904c01c1c6401ca060000940f5000d8512410368403d0200b004114003407280c0801030403a00580c041004180c80d0742e40d200c50f0b510507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 606114001 1250 606112751 606112757
    0x160c03020d050715030911010503070e04050108060108010b040b1f0507060203010f06030e03070c030809010306050901080615030a051b04090b070e15040807030206030c090a0b0a170106050304150e0706 88
    0x69401c0ca507042409407504001c00081511b060f03500303004a060714101818281007800c0c144d942c3c0e22082c4c0200c60701949031650076001414800005607044000a0035812605080d00030080c0304114805c01050341c035040c40084c1c0c4004c404508120790403c06045040320600c0b4100309182c0800c3ea07a4a00c140e030801d900400100e00740c030f2000c000d40b6815010b808011020480910b00d40840b603612042411145d01001d4840800464401d0b0b03030780d001c2d501c1080030f0f10300100340901541c0d50f1440c60341c1d41d04040302c1d04414600512050b4045c0c1c05d0001e400c1c0a6281d101c0b015002d00d80704403104030038030500302c1c40d000d520a440c3c0c110100450034011354540590341a03511000d22400b40804c5c0210704e44082160308000404002c00c010380d0300e022179800709403030741114065a6511030035071002c3c072401003400c545c0d80b00380140400141034503064014080302040c0d0315120500c0e409070000e2402050709214100108100708005000100c44409004442c05901800100000d0440c03215140851030b400c1403002c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 606115107 1106 606114001 606114013
    0x7030506060904020408210702030d030c0201090f0f050609120a1b0c06080f0f0403090b090a03121709010b010207050d060e0102030a05041511160c03020d05 69
    0x9030b220000c006540307031500c9920150302c0354000a441489205060000414000c1e5841960403881d002406020300980d840410341c05402c490030b6032400c5550313801c0b0a600007920103100e1034446011700744c681540c000c00c0c54001d01c0c155004e45401c565601c034401800e81c03036402000f1126004028500329003001c05840c107110500801d140000c02c1b0704100d540c08185545d01001d62841808500d103000407035111000c0c01160340c3c90030b480140005104d1042805001c0f4040020300000c3c4020b0545480390382d0b651904034110540504241c00034070038040980308121b0110100e504045514001c1210060310000070b5510781071031080b2801046424900e4003070184a41c040030010036010000e650300e02d4003016982c001c00040f00c007102c0c0b8400c1c402c060b8924480c20311540c80b0003080080e4091a090000842001c04c02400300103d40000443c2c5d03006c80142c48680c1d030002010707c03940007854 = true := by decide +kernel

theorem cover : BRFrame.Cov 605935251 606115107 := by
  have h0 := BRFrame.cov_init 605935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 605935251 ≤ n) (h2 : n < 606115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
