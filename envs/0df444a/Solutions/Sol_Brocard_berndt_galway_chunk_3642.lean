-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3642
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:15:50.772143+00:00
-- url     : https://prove2.me/submissions/1bb6f2af-63e2-4066-b042-2edf0b87b893

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 654856115 ≤ n < 655035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 654857365 1250 654856115 654856117
    0x30f110d080c072604063002070213050a0b0118120305070302030d0615120209180a0e1005060910060815010c052a2b0807020904050f06060d0323 64
    0x2030f0301c03141007941c888015404109401002191000d480391401f0ba407104ca8508594006000300400c131070503030fa040980ca0304555004080c082c0c4001e0a112444074001621803c450080758515403459948648001e02c0da0800e400f40c080507100e80301e10118600f8800a0a00b800f04004010140700d400b1580b07000b01402407003650011540c1384002c1080342e42d40c01c620840d20a072501d6400100f0519501a4440d0a41c1e00032594084c001502125142d101250150b00c03405006180407840b40d607071804000249002c0c441c2000c19a03000c0004903207410044100280b044000d030007038904a1906504109407504001201d41c0300b8501089a0000400c2d1001038610150320140101b540c0507007003103010840c62540c605003601c0d100c1612000301010040512858082d05059100300341c01d00c0b182144824002031660510900c0741c8507640c2090069030105a804c14141e40440351a0020303000d02410600400c009a4046d008450416201714a9140a03164400c0183c691650b115560700904558664030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 654858615 1250 654857365 654857393
    0x609060f1905070318050627060d050a050a06030b070c0c0b0c06040506091f09060b0d050f06060402030411280b09040e030c0312070e060403030f110d080c07 69
    0x462104600c07004400300508940c00036038220003058800700150405080584858103907071020b00800d00d00002d40c2d00038030204209040700c040051444010580ca611260040c0c4010040407001050b1401e0101d0070409592008001d149101d10313180e130400101300a1000140c0040041c01d0910200b00a03060400b00c0c00c0c0030703400030854802c00145105803c007000401d544038070300460642d03880e030b00e0340e041103629801c810301c4c2060140c61200c41140b100305142c1c40000f100c1c0c40b84500007003401c4004042a8903001509041c6e8064001c0050b83e59180b0040c00142e0340480100d030114a5031919580da0810380c4003444015006951300c505070800c101041100408002c86010b84c4050182d845085c0f04281c0d11000400b0300913820a880c00113a03690001c10b036081030030780401440c104960594001d0708a800101484104070920408500075100c9200a0010314041d81e42c21030013100246000e404500c4a80c4980d14960001220466140e41312103007640086103107a1503907582d10503085c1010b44036403038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 654859865 1250 654858615 654858637
    0x60705033102030609070e01050103110c01060902090315040305070f0201030f0e030405031203130803070c140102030f0c16020603070e04050a0c0e0d151d0f07091104050609060f 78
    0x1810346a4680800107a900c1a024403c5045507900e036106070445845600a101c3c5040e004540001031025601941180c02c0902a901100381000c1201580c9400d488180e0701100b92160300040c40c002c10704061004c0005040140d012080c0c50615580081039880784007005880f80c5044c0c0348507411684a40c004880c41e011190090000403d0b0b02611500ca40c071620409101c1c0c407c01c00e0820b2050311080c20b6070303c11054142d401035210030649510f0342c1c541c4000c2841c02008078948600700054aa9000340704d1030b4003884001612443d002d02200305004010b03100103ca1102403220107030205024081c00d40645e07054444c640c80385c446442c29034070105030751519640141001c080202e00c201e15400200548199a1441b1458111006000d2140d03640703038014000059031080c50028211603000118641e4003510510322b80302e6940c0d0718070704240cc034510048032900207102c20000d02000e80664141500200c3e001132419180c000010b00301d201c1d103201c00b0301800010a50091002c51703282926204803031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 654861115 1250 654859865 654859921
    0x1d030307080a0612030509281d06010e1c060b0a0e09070b1c05041104020301080114060613050103050a0207061806050f0412110a14070306110a0206070503 68
    0x24040600554000ca0b80c0140c410310b0800c0000e44120410032001050b5003546450f0300c1e1010381c6051040030140121449240f1001164406c088000e4454010040a82c7e19200d040740344860900101da0a002d400b803030410001183c184529551800305070628800b170790080d81c610b04145050009080070b4440103501c10303800100041c113024120117007482820714205440310310707480b02200d44050050440c3c001e2540000c81c1940e10301c0049030b0029800a00411070300b00d0742816480018281e910036001061941d4641702c2c0300540801c110b22450f0418401c0300c1c0705007400d4400b101610b1502c114403d01d41056141d101148005e00300d68102c4198607001442400040c0f1000004d0100080702801104d9440c500f00c0056031286280c3c0c0114020b83c0d2000c03140350b0070341060804891011703c100e2511010b0190700b50b0b11001605441419820b40165809000b50915500300030046500320703441c1030034882d000c0104044c0154046095540f040c9181000d98890300e503200031058207100e8898080707650030703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 654862365 1250 654861115 654861121
    0x1080607090824041511180a0e061c1e02030d0f120b060403020303130f0b0301051c050c10180b04030c17070315060314012903010f151d09060a1d0303 66
    0x11b080051110350080324010342c0e0f00425106001540000c0d100f07905606000d1400700b58030340b421032184281d1203100040c000d900b806984400d01441501d403000c1c40c0313401c42d0003101011820113101200c3c5d00019420311981416913035201814810400d000103c1c115503231359440b200d0b50344890a8601035030700078045a880e54000d043c681a004c095028060158100d28000103220360040b0413a4107840300a4903520000c0c081c400c81c151942400030007120b603405140b100702c001e0b81301c1c015807081145899a400c69801c01400907000185016040850581c50801c0180042481c01500c1c2c0100c2e605200c040c152400100512801e00400307800080a03c480000070041705501c54000005032030140c64044c11529004041a00700c0b01c10415a00981140840500601c0780c0b80c500c0340781044000d03002140c00d5030303620031440840d10404001c00008441c281d041c0001e40488071150000400c04d110b00c00300f4100000d80503a100d00041110220f50b44620600a40d000004908074071107842c00101e03510380c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 654863615 1250 654862365 654862391
    0xf03030e160b0c0609060702030a0305130204051009050108010c0c0b0c0f03040305120709061e11030a0c0615120b071404061e02120f03061503010806070908240415 72
    0xe8851034108410707201d0313000410300300d03a004600a4084c0c0a190021407514807034501c00d034050400104104214281c00f2100400741c0c5490048900c5444002d003100ca40c9410301aa89085907010303082410b00360b140c0000441859004042a41d9035070b00322100d08040d50300c4500c00001441942c0f42900c4403880030050108164002d005030084130907100300c4860585d40e03480110307000c41c040c0c814000010300701d000110001400000488480d181850032401846004512510b103610055407980000c4050441e441485903612981d074480c40e00304111482c00d07150108821003007442c0c0d480900409100d001044056000750b48010300a40c6000e01e0341d0f22550781c1e190103000c02803c4402c1d2840c50051200b0120120310100710040c01a24001050741401c40d049041c1c2c4251300014244c50b004055080b20b054004001e401840c001c19054004013070518006c480108078801da9400f1050035400004000d503920560000e00c54683c0c0d0704010341d02c80d0703540c41c1402c01200b80c1052045034a00e190a100101d24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 654864865 1250 654863615 654863617
    0x30a120311090105030109021b2a0409020a0302121c031e060303020d05071704030f0201090f030507030b1509010f0603150f05010507170a2a0f03030e160b 68
    0x560119181008144000392503032209104541c48180040c90400040c0090b0042e68082d041c155202103001442c101a01c10880c50f284054400ea01800d0305086244818446020381001d02e1406540c140421641580881d140c85220b00000b4070540068010300d105040c10032424800f0b5403214041450340300c2e00c450140040204560100030066038410201410b038250043c4401ca0303a0550040c1000c0d10755880840e480c2c4c02c14502254010b0f21a11092041d0382203c018201650180704400b1000c0b48510016084821130361001030740341c400038000c20105102103000703401c40303401000e80a10f950b141d110000242c814119680d601010080011914110909403001500c0407910708000000c124202d54004180728030600085071050401070100c0c0d407060011b0211144201c00684500c1c8003040103078125080400803200095500001c90003c480030308171000c1043c0d0300b0825521650032910b80c15030f1156400005001e25440b40702c908120b0a04100040c0090103408144080a032140310183e01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 654866115 1250 654864865 654864893
    0x809010c02012606150c1b0f041a0316030507051309080316021009020312071a0c0a0e10020c120304050a0603050a0c3b1221090a0b0d0902030a 63
    0x1500b50410864000c5c0010f0b049904d95a43c80009288003508001003805103980a44080c2c0c0101c0140e0101d905900c3d1409100c481c140e041c404c4042591004050520b0560000001606c000c96102d0409c0030580216811094503016600028a014034000c03417005448040d1004016160001c01c00c801e2207030303c41c407048211107941e00fa5a4424204d844031420750300c518002a45c9500805400c0008455840c020450584101900c400500c1e10101e517046041c030449045c85580c0000a295075030b031760b0003c461b0718000070849690142038040c8200a58400d480641e0340c1c06a2140d030320880e0081020400d0b907000380402400e54070040d031507440c018060401512030b00e0030799060440280b000c1d40182c643d49000307018040c41070050001b01d400c400502902000d0400308001d00c0c92445c10603250a64082c0f40800d2a400500528070018002c000c11007910504403806201844014200d640b04140e04080f03c12014545407500d08030a031000041184003002589032050703051030001c0102e100e1b100c1d08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 654867365 1250 654866115 654866119
    0x1e0209040c1d060304020d02030d0c050c0a150e04090b100611010c17070903050715080f01080607050a020102040b0406030501030507150807050711030a0803090d03090809010c02012606 81
    0x3020388407031080c0c80d11111000b03080d2444103400d00903a00380c01d0100c042c0d0750090005001c440345640da50042810b1030b2000310707002c001038501032029081c090b00b0407880500c610103803440c18011303181042200c1207691140340c01c070420481d007915075000d80c1e07142c1002030001c1c4c000f000d400c10b40c00e14003081006c01c200c03849010080786d06804072550710b02e41849025500040c2e5111003440810010315038410140052244041c419aa000800030038000c000340303030107880e007210340019403903107518050803030078004011040d069040c50060011900101e80980c00c0029800d0158940311001c1c8103a01a01a43d00008580031022400180f21540b6403c968102e0b4013038415503013031a40b10f424260080000e110058041030920001c10f03c1035104000400359180030f0468680d1680e010800242441c0c40a042503a8008000c400d10241c0c4000340104c84281d0750383d080130050380c1c0450f614440c141c001c1600c85414414002c50000659000d54a040c40102802202082d118030700c02c100d44510310244d079598 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 654868615 1250 654867365 654867371
    0x30c06071d040b0609190905010909110402090a142209020f03030304030f2d080402120a0c09020f041208070303290f06090301141e0705120603011e020904 68
    0x40c119040500c0ba040c2590000b41c4000d02c0c0c00100ea042c4030640c1006c10454225040c580710014650b1094403030b0a000e003940380000b0440311854245844101d001d540c504e031080d4810840b140d0156543d00c01c00003140c0401768050f000d5030b900d80001310f454184010059114607141200d941c100350b50784c001c411981c421603010b0f4440d1040428503680c3d010440d0020f001c2012024180c246078001c50507400340010b072100e000205101c11a0130a07411703485203801800318180c0d0003444118a0710041d19040c44103c0c5009001c501070988610002c10803500c280072550342e000a6001f660810002100d01904814441c92101001440d0040c600da11541c82500043e142043e440d100c848200c0000e200d0403585100140c4c004c0d41003080003401c406110301c8640c8140c0c10441e42903a0b407001c0c010030000005007040101a45840140451070524109140b0024240401001000c0ba00001a220204c1074001c2115090f55800b0200e4018030050320401c20201c05001e1810004d00190001c06507000103039018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 654869865 1250 654868615 654868667
    0x1b020c0a120309061110140a0e24060d0c120c08072601060e010b1209030f0a0f090b0f030115030e030405010c0201030902090901020301210809010809030c0607 70
    0x840c56102904a0040008201c00c80401006110b08018400e017028001901c44414040380e03440c0440d1140d50071500701401c90410402d003104ca03445000134a8581c0d001500540e20240c090f0601c51018031454540c0381000004160390342c0703c1c1c0c642800c110b5407003040300144540f2a0b961001901e150401101d0b42d07036030307000b000c20260804a0030100b1919110415100c0d0307500301020a010842801e05000190750344c0e9000a030780d14000c004540240080003606a407083e10101d561000b00d4020b00c0c0b52543d5100f040740078418008001150700c40c0c1c0080c03030150042006e1007801c44080c421a407040f004900041b48240c44450240c005604982e90380041c080d0206011a069096989038040c07030201c3d810030f21041240d9401142d2480c0d42901c1454000f507001c80c01e900081c1d22010986240d501a9408030050110001040c80d000c00046d140b10340506225080d0703502a0b0702d211718031011381005140d001042440b84200103591415682c1015180140b0785203000030a81140c481840214003424008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 654871115 1250 654869865 654869879
    0x60605091005100e121b01030f020c0604030503042402030a1a0907031a060c070314120405060a0c1401050f1008060f0c0f0a0804051e100c031b020c0a 66
    0x1e000111680500310511201d080902510140c1d201c0c035040e0340110310b02000304000170041c080a100310340c1c01c804c60140450b10600040803516101000200d081c07040100b4040000c2c0047e145900c16803500d00f0380c2e80c070380d250700c0c044010f0030785a4140001c0302c084c82c15400c4000c911f074002e50703c20b1038510310402040044110246800c0003564006420580801c04505202e1007a0049225241c100c0c09000d07448480030041010b41c1c3c4401d41d0310420390061441442004010350441500e802190001c007942e50480d0701c4041644120300c9241d10550000a00c01c60f0a8054414041150f4121144490000c011988107010741011209501d05441440000704007600400ba08020707074400c4002000b480e5900040803c0c0085c001e00a00710f0948140f05810074240c03030f080201120011a03036004001d0805103481031401c4c2072070704007400c40025800040b800900010b202c400108000f1004680070094920560003002001d00007051a0342c256030600c42c090300011104c00300c1c4c50954103000300c6d40c0d079211 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 654872365 1250 654871115 654871141
    0x2041d0105010507062705030405041d1b030a08030103060209131803030e070f120618080702010305070c1e051506010507030f020c100306080d09060905011b08030406060509 76
    0x70303030b40801d006100c0395001c21225032007889454248a0b40c10400381c80e05060440559840c28211074980c00010180258105802900209230245528080c800da2001500e0345460442200b00645a0309040141701950f00f0840c0851854108054503600c0d40c5900300a006944001e0b0035602420b0b2008480c01d00c2010b034899400780b41c030039081082d10b041c031070b0340c045018202c6503071022028441c6060114070032072080c1a040042030a9142d2880800d020300c1c02900b034403000c00d400040c007900f090329800404c80080440c0c05440d424600002c850707640d4141070700d105034040d5001d0164180710b11100401103140265514140c095022a0746e10046001c0c5030803641002c564160000790280f24210000740555541c101ea15020700548890400b10f07008202e01c3d0485442050000e0b8a500d810024000248082c40b0503100500c0d0000314142004800b0309000e995205140c10004400a0000c5507241c04840400f002e41c004203103a078a05003820400042c081902445224418110202d040d60107640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 654873615 1250 654872365 654872369
    0x51801080f010b090a17152229040620250206040806040f12172a0c03030f240112181b080d200f0f0102041d01 49
    0x1480c40358550307081458185840d000741040a4018840380e001251082803019010519014503004154003e400d52070080d692030048c4c9001901c1701c0007000c1c3c0140300824010307494280d402c1184880000518941c00c26035084408500300b0452215041c44100700958000701d8020a0000b640c0259503101e164115842c811035442e8400c0342c019220000358030b170240140d40343c0303a80010405814103548501c807a0805204a0f0203c4624801902441c2049036a03405c480b0500d4892800b154030301b6044c210a1810000074160440c031800b818170000c011881295603554481d482c5413483c1e11022550b200c90350340d410680302e91070030000c1500003c1010400f610301050364101000c0703e0454620300300054a02e0b400c41920100340f2074840c100c9807001c2d0300301034032070300d51611036803455602805602c0c0003110f001554000380b5260f008102c0c401d10f060340c8180c0103c0703d00c04125182e10b410718040c0c20301e4940f050b201403080240c01000c280d4210030b0810750251089568824014105101100c0b582905175070074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 654874865 1250 654873615 654873631
    0x905090c0319061103070503011d010608060909190803040c06140d0c200318040506031b130608030a0905040c17180723040608060711030403080a05180108 68
    0x2e8004500c41101d4155141c00190080d81c002030505400108890b20f54070485982d408105d0010040120618048074a140e2250460040d060380d410700400510042d00a00801c1c1700c2c04001c808170b0b441c004203201070740c0341c130140c465a08800300342c40c500a5456041140c05445081340c0c000006480350060b940007440100e1200118500000f01d501c90000300300c00080d100403c003000c3d4501381c048040000300c0e4030000d4140000d43e03e03200e0300d01903103440c010b07180b02c41da004500306010300c1100e03100041c09039941c4182e043c2500041202d00e001c500c9078400e50b44c1c29035075a0f04000340020100e401100802c00001190750f03031200c581d01c2d80700b4401518020484800001c0ca1140801c1000311244070a9030012020180c003620402c0e050401032805040d900220036400583c00824009500ca40e079684c0c100700d05072002d1000d203150000031601c44100400180900ca20304100e00280c10003402120007640d44000ca07540c030b451507140c0080058011034484407204225841c2e40c0410b60007981d001d4411000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 654876115 1250 654874865 654874873
    0x40501050d0309032301020a05070618080412060e1207030807050403020a0b180a090b030705010305010b030a05062d12060f07050c15130b0f1b091f090905090c03 71
    0x10f940c0e01c110700425086040b002c1d83c2041740c14506110020f00042070303500c8850380ca19880341050308092084131071005503a800d40070004031580000d0008170940b411070301030aa0384580b101c0d2a0078003101403d0071502d00c82c1d0b14020b0301d01c0c256020048001030038074103020755030b05c1d01d0a549a08081ea0540300d10300004c2c0d801503007402c007004510b03003060040000300d0700148941d402070080804600c80844a821111001307407100b010b89800c3c00c0402848005040c02d107824400e5514000516086102c040c011080948e10b85001420a4650302c8d03501e416901000040940f410782050001c0111403144080c0b4410114011010203180e4001602070046450044005040d03d03800c0e0300b6a0075610020000ba02c1d0300400c0756160f0604900543e45129034a40c0305001001000f925040b68103140c006e0903406050800c00a10607410500031144182c90f0180440c02d5552502c2000911602d81d980086400c101000c880c1c0c41c0c84a0303200c94500202c90a0b05030602440c4c58440c182611505005c06c0a80c0680c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 654877365 1250 654876115 654876119
    0x5060c040806062d01030b0d03080108061b07080f04030b0a0b0102061b180310020f13080a0b010905070c120c060b01360e070807020c0105031905150303030a0b040501050d0309 77
    0x105001402e46030311014100018040d5051f000724800c1c1c80c008109801007498000100a10b040c14000542e1200d40503070407a49402c0e41800340c040c14010100d002c1c06084022992110b50204082210069500926540c4407454000300d04000307012444c4c01240140600004500b059104440701e20020742c88100302800d0a1441644d03007260028207151543c54400c1038250383e20880d06100612000d5414928a03035105900b020b045240c0c03580c0d0f4803030000c903803005071200040384001c1c80c01d40c1136501c3c520303000c1401e0321400811a03951030240f4000c0c0176088040c03041022260442490050b1a201b50824070440c0400740040d20150310307400c820409441f01c00c4151584c00c1c2503038240e400d4a407040b211020030301c5c3c5600310100c000c0030032a05900800d001c4d01c01d004903182c0412030f0130344004092818600d07620304849640d0f8400c6403000e1454442e81c88902040103102c9034082507588040140890741c4a1074403118190260071260f0069004030b00d0000086443e0402c08891034002d9015151085014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 654878615 1250 654877365 654877429
    0x1050a030b07021f0f1b020a150b041406011719020703021014091e10050402010e030d020102041e080706140d09080406030516080109020f0705060c04080606 69
    0x4000203142d072085005000481081004280040003500c003030441c002402c103901001e1104889121140380c1c00c003040010000c00041d0300040340f00341285d22100000d40c00c07401c1581d0700050050003604550103400c05081c01c070740c16102400c242c4140c40980e111404110954200440404186d4200b401d90300c5a00e00320a1881c240c1d00141141031091044400750076844c141141129000703e2041d0100c1030a005202569004000ba03030b888004040044440ba070010105590740e0311300d0551601364a499400207015a0700560070400c8584003e41582c030003080c44c44000b030003544280140700040c0c40d006010540040e00900c20015551554010040182803500541e2900c441035100e0143d00b402f003003150f40d0b100311405800f046ca0b126150041e111410814054152880180141040705001c113260800fa5030101d40f40c0d0440d04092070050b598140740c403181c00309200e00784025004d0703c101018403511580b84401001210542d0068900a07181e410420880c1504415098648030513460031109030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 654879865 1250 654878615 654878633
    0x10b0d0f02093a0b010611030c0a030e2101240303050706090204110703050309240f18011a03070515070803090102070c030b07030515240904021306020d050301050a03 73
    0x10810808040d003c070001c8400715100642020400c0300d0106040c8010030050b0313040150030030f042c64130710040e50034865080c92103130361818851005420441080404c015076114035803454440b05a044032414480903030004540a031107828001c5804882080d50055103517804500748043c1c0c1d0745a541c9a00e002d00c99251540641007070a820f982c003eaa44140790f002c00a5180180041c9110b9182c46031a0f141c1031100c0d84c00e00c0d5203080e00b01d80c144040c00301c522030075038180c080d02d9100794039601200c07080e200c180c2985124202e084c0300c807120b9131a061600c000c0c559403a1220301030640884c01c0360f01d043d46a500344a0f222004940e207003900300c424030600f800100c1034006950300c0b43e80000014104106501e8003001d074000c60384187c4200c18650188000c1c594140503069014000100480c079104101004c956880010100d040440340040002400c8001404c01c47d6a140c100030019900d4214100c18564000c891703101d224098441c010303101d00d40c1c3c2d00030020380b130488000410100951f8990b488000c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 654881115 1250 654879865 654879919
    0x2070210020f1506121c0207060c0209072303091b040903050901110f06070f110106060504060c0510091110030c050f1c0603060e0c0916030e1203010b0d0f0209 70
    0x105c40c551a000c201441e50810107401066a030810011741a004860081e05107040386d00190108901c0044590140c1c031061a080c2c0c000d492131a00c4810305003069480499260030544106400d0800010300c0303008140010480c03c0380007803582d4030115400000410040f0f070780b51031009002c941d0034809443e41d507020703d603c10b1040c0441c0f0b007aa03100120300050b55003400011074030080401d96042170385038029400741c44081c0c074817001d10081001e41d00b0250094124069032040000b00b08a2068020401c04d0901800b05d20341c54900c414461400c240c07912402c0342e20304002d0a4014003080c2c41841c03d1520078040c501c1c8002d6a910341c83c0c035010300b080c80384202d0303403103241400d5140e035400300140c03141c00951043c00000c60207542c000515070f40340c0c50490300300068461800c3c49103180a0612414542c0f26102c40840c000a08002460310020803105003006c480210f18641030300041300002e80351650000900c1c10940d9404100264101075080204070b020709035030650081048404500d003207014801040d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 654882365 1250 654881115 654881119
    0x6011505092b080d020a030b040209130b120f0a03030e0a0b041203110c1006090204050f04020c161d070908060f190c03140a050c07240e0102070210020f1506 69
    0x20704102c4949841e14241d004800030484598001071030740c86507905204a02800c40c003214154500401a000140f101545c1825041580c0d41c40192030296a9900007521a10220105070b520400c03d0281050f00d1314090710058000c40c0c2001e10060080d40b01003204480c00b03900041c10242078403551110310089400e0b040d00e0061694440030101915504005002c40c2942607004000d24101c4a00303040981e2090b6120f101ca1301e0040c0b0003844650359080e44100518000d0300e0040e250b44031400000e180c0704446048501d2180300d010042107031004c010781c0f441240c0e10284800c0c0c0c5912850000c5842d4000b1b881142d01c1c5407c104042401000e2448400350445948102d0320f200303e10603144101100c014940540c0482d680320200d4440358440b520b078540c0404e040c00c08124518028542180754890030b0402080381441c1d10741b04455220640034000f10750055402000004c1c280d030700c000d00030b500c03a880c241e100d42c28815440d011b240c03001680b000911041006000244000700110140c500c01800084d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 654883615 1250 654882365 654882439
    0x906030708070c0606080f0d1115060d0204140411090f13030207030b0705040e2202150712030605040f0b06090d0f0b0406151a1204060207140601150509 67
    0x1c501c4c0b80c020b00300508080c0d0302038908400031680c1b05180500784100c80d03040c801104051051090301040c0c14900c1c000d03030600c129450342c6041c0014049030081c080258041e140200d2030310344590ba1524a8803880c40b0348a82d121035820841000101c5d40308031505101d9950480004a1150180720380400003031180c01150b038081d44a42e248d04d060b0800715a444d0003c0c2003c2010868410040034141c0c01c0940b03241742034040e20484180144c3c00c0a07000010780101400016007030016012030449030a550001441c1100850810000b80900402d21030203110398201514075560f48182d1085021080e03000b00001c3c68125078009100b0202c03250380f016202e9149203d10580401c0075040481d108601c111070000d40490418110418944c15801030014140404d100b8a545202c040488912020a400031401a03a80f8a0814081c0c410008000d080d1030000d803c50306540c2000a5582c1a1198201ca070204030b003071039008460342e00074614510382c00034881e842c0001c00d80a848200c114643d054900c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 654884865 1250 654883615 654883637
    0x609040b0409121d100f09031202010903110d0806040e070503030c06060a0e15010c0809031615020a030e091506160204050f040203100f0b030f030c0c0402090603070807 74
    0x5002c03601d200d9000d843c46030b002c0000301610381d07001c03e100301e44110f0101143e10120440307004c00c03210940c0d10b1191040c004508000d10669026a41040041d0742c40004d40c8911200840028080c0c0b034100030031008941e8501480958150204201042d0401c0d56102c105d035a40d00000c010141141c0c1690840c1406059008100c07524140b004100f20241e00e07000b481d06013400001e020480034150301100540001d54284401071403814000c101c0c11009181001c07802440b420882103900c2003200c079907454402d5401c41c0c080603001c410a08115448083c2d002c802020304041030380c80d02e680d01c01c0200045e00002200700d0525050b6519034010f2007510f00f40a480c40c80340302180056100e0410754032103d651148086c110700c5d06004555200c02540c0b0041d00354146a4086541d0b40c54a800ca0300340103444800650000c4100c1d8403038440300c6c9000f030854100e42c00c8101782a03120351028240d200503000760b090706525828103000310342d80d032103001c0d180341d2030b666618a003124041c4c00a81101c0400c58880e42c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 654886115 1250 654884865 654884869
    0x1701080d0c06241d0403021005060112140f09010501060e0112061a0c0601080a12050a0e03060109060f0f0308040302011409061216020604030504050f010e09040b010510020307050c0609040b 83
    0x2400804903d080c601614241000c002e0090008a0001089070000350010000003e078007058000c841c10f0b05520200d0203489550041e10180d4500a0000015142c0a940340551000741042805204180041c000e9034071154561b0b03081c3c0d1070900030600421800b10410200354882d00e00306200e0310b100400082c240343c650380242e0301a80502d802c80bd2200b004100794400701d1091003000e0041625400400807644280c1c0c40800542e88482014140400402c071a84018051400c0e20303d03a580003019510b0541c1c40300d140782c004100d140620400305420b06400b040d802080e070f81d9001520b800002040c241840c40e4011507040003001070301022410240045009a11b85001070240858030708a20b000d14034015040e4100a41c0003943c000c2190301400500004c2900b20045409450742602c001196400442c0183c90040e40f00c240250070a2161041206200b4000074150582c1d504880390300c09029a00300c100c6ea64000d495001d401600300c00e9010b041c5282540003803000541c041d10210300c039a03d00d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 654887365 1250 654886115 654886151
    0x20090103090b0a060512060403090e04051006031401060533040e0103060b0f100c080f04030519030206010b0406022e0906060303092108090102011b0207061701080d0c06 74
    0x141000103103413214004c5c485c0b80b1b022005143c18541c080d000348058074098030f00804410642c4104802441c5d0754011a00340030007842002440c10b10030100380069aa01d290110b0801e40e1816450307420751a000c0003203120718040080c0344005034005030b00c1942d003034860416406510900c0e41000d5910b1b0821000880307120044c006402140101d800107501420b034070600503c0c250b05100035101c0d4000d088684051500440f016018980142009898045c6800b001c001c91003640c001820030b100307541007a40075054803503880401e91b00c81c1e400d86100d66a80c0300801d020340601c0c0140405600b100c113800710105d030229440c0103580002d0900d01e40311408000c1201c1282c030200801d56410391901000c0c001e02d600982d20301e000f03040d410311080044580c050505071144418500400040d0f001501d000e240c1e1003504440c1502162000e0014641456003020303661701d03458820040030030040b100450b400c207009a026030480308544003818418a455104032007241c4034200842c1c11560300d070310451010a41403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 654888615 1250 654887365 654887371
    0xa050d0803071701052d040f0203042d03030f150b07111203040e0a0b120709050c07030806091e16020f0a0203121b0607030b1320090103090b 62
    0xc40003a6241003004005085031148009254a2884440100182e4036000c41d41c0c0b00d132415086405402c2501d00301c4816030841c0c600a803035071090500e5421007a5104503402140100e00c80e84001250203000d0046599160100a660200100104412012034002c0e0046504102003010001c0c0d2810785103103c82c01800190814540940041034007000c1221100d811007402c24100c5118081440443c0d007a940c038440c90140c080d4844441020038442946a00201c005000c000d1100304082e0303840d01c42c2e03503490300c03684a440f00050504011464041002088401250b01640c0c0ca030700c1c1b680d1708400e00195010241043c141c0d070350032820340f01042103105405030052003d6010303041608004080245000c21903110540e0540082481c400181e0b800100900e031110602407060301c8044550200c2d80a21f0082c20640e201d0040408003c1e840c0c2d49035210341064034084071a4001e0b0503e49401d8000ca0740140405c458109141c00014204090031026108000b4140740c08a58505a42d58020140c141a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 654889865 1250 654888615 654888623
    0x80f15090f0a1a0603012a0306120317010e07091202011209080901090b0f1e0d0606020c090c03040515060409020301020c0a05071508070c1403070c0f0902070305040506090a050d 78
    0x3c00f446007940180c0311540c0350011070842c004d1001c080800300d00030b042070b04004070038905502e04081080700c0d40650400002030100321000e5440342c00780d04025103082512003006039201182c50012502d2072440900034000d07400c6030b894a800c4c0c1e041c207140b082c80181c03081c01a81400100d01102c200310810380910300304c0d64070520109450b0503103071001510310000c641107000e03820740502a0b20032060201c815900100d40c116040f181e040841c501c08200b9205070307100000c1d05402c5c400003080f030a40005204a2030501075400c004240d50b000700500041c0000d4800502c20f40009004809104160f1486904030b10014000928a0311a500082c2260701484446d086904400203070003d10000b40031210044c00d50380341c00758400c500310000600e058801010b440910110b4030040080c01601100d003402403803840221307070b030f00e64032400c0144401071140b06404c11302c1038510000c03602800300d0007a20004c07907154842a040a00342410031131180c0206070a95013169940c0c600040a07641ea085103a070b03242c09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 654891115 1250 654889865 654889883
    0x20103090f151d030702100e060406031a0a060f03090501060f0e010f0608040312090515040503130b0412020420030c040305012306010e030109080f040807080f15090f0a 74
    0x40d03404800152210b03194804498214040380f14002040071080f101c026071304070345140c14092280c0c016948a03e40001940c1c00c420081030114a0a800d0740c01525400c00d2041c04155020f103440400c0b010040502523240010350303007010b20b105540260003d108140c85800003082c0241c40d0b005120802e54203a2012603551105801005081040b8450401808842c644000545015203000d041401d021000600d22540c6901c68401e01000f0b002c1c46840c060350b409982300f10700f0700e41001070b501e42000c030380304036500318407800040c2c8038498404840c101c0e10034180305440e126545e002c100007402459200f500481150101e03c602d000d042e0700a5100e80c00f50300003a0344450450400074211414001d842107079070715070491600c0389007203110741c40d45c4400e0074a084441c070040d0502080c050050702900420103440451300001e0820074901074010303104c0c032a003166106a41e030084a50360701c01c0c0500130301a43d046044c00b007680c0c0416000050780251040308a41c140c80c0c51407586031501c00034000c103071202c1070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 654892365 1250 654891115 654891143
    0x19020703110d051804063005060c0403020f01080601120e120408070e010b09060706050c0c0601090c020d022a0105040e070c0c09090506060f030a0b090f0d0f0c02010507020103090f 79
    0xc082d100c40c0e09404c0040d0340804c01d0b5170034151421f15210034640c41c0540c000400750008081c1002c82048104942e100059030720a0803d1100861590014042288960303d0b91301e01c5102940301c3d05195201e0304059440014041e44928950010074181c44050030a01410020401c4590058002e02c006c1c078090380244051031400d0407140410070180c1040c04214410403030b41d40d446d84c944081c0c40d01035401c61800201b5440f6803441225520800482c0c507a24094200005003060295000016036112031b000c2d52459521000c08984604003a40c1040c0104464007000103105031034100f0030f01d001c0701810300901d00758885844008041c8202c0d18000000c8070180e1a00c104440070383c20b0801089111420710568244e552500c2d00d03400020402c6d4060400d100d0b0301d4045903410000340c1d00d01500540d00c2c3d9000c0c00d009043c9525000042c9052425114186100c004075200d6400e4100c92400d95a914030b4418096004403081d80c800340c01641016110510b0354046001e0540d0926128841d01103900e42c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 654893615 1250 654892365 654892387
    0x160303090b031009021c05042f1f20070503010f1a0915100c02090f07090b0309010f18020a05010e03100509010e060403021501080619020703110d05 65
    0x91419005155607a01c14002c0c0510210301c200c81105440a043d405602c4107110014005103081e03403225844168244000d00040c81420300d0b0a04414014110000e01c1c1401c03520300700300391184001c8a580003540c90788004865040c0240c2c801d0000c08624000010000c4c21400307e0044060003049201038225180402061800740b0036103240100c40b82040c4031003c40c20344d070039401d00402c60302c99014110b18030005034040c405062041500d0b9000b486440d074802031400007048180e035903404030701880803000406c2214102c148100e1141050780e88482284e81010b044034190303000580a22015034030751580c0f1035540e0300c1e0b00171400b100c6004c0c10702444005a50040018048842c1c1c0030a041c40503000e801c50240d100800c1214800540c504003040c5074840b103200d0390040807a140c10410070b005003c2400308040c3e021848201a80040c140801107980320607090380c0340c1d1000e855020f03881503100180b0780412210340281c2a075034002d0902103800c12a0f41701e00750034602150303040c00c00514001181c2041c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 654894865 1250 654893615 654893627
    0x102070b0916030308070e1536030a02061b01050103120e0a060e060a090306051e0c0405010c030804020315010f1d241201021309060509270f160303 65
    0xc40c0e03100104030406031841c0c80c00750102c0d034040c2c0343c50100047c40034030310361603103400440d22a09a030401009039a03403d08810030090580c101d100d00b60017120b40303800d4a49140403120089620710001d001e01030000055080000d0303a402200110001604948d05404a1000784a000d0007540030b003006c0e040b440e031003180062248071501c040d603114403050300c001e2202e503501c0a450780c1146011ba41c5a6624407a00400752003211080d03000078406810102000300702c9500710514850b041208080320303800d450b007117911a890300480c0515400510440da0001c0481d109407500f5802a0000e07080d91543c142c040d40071307203100b00241c0100d401c1003900503042065503540078049405035030b4001800709074100124110b200e070804c03c90909261403002c01c00c14040d515000c1c40399101000720003c555424901d00c038901c00101620030070403143d2810750001903030f0801c03410780b51103130040d025420012442c3c103000040c000281c028600720751054003d00700718140200000c19041c95080601c5200c949903207002041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 654896115 1250 654894865 654894883
    0x705370e091605100c0f0c062003030a05040c0314010b09062d2706011803080d0519020408031206010c08070f05100f0b100f0c0b0a0603050102070b09 66
    0x21075446405510b0404191203800c005440c0d04079031215040c2e400c4c0e0412142001e0448026103104200b40503001084a03a0032140212076541c1c0f5561380301502c0c444004082e219050b030b00c00f1982c100b00001451805280d00c0542d00901c200c4451843c00d44980742c1d000e1100490341d401103140c0d0760f80c008024030720741401c0c0c8aa10510490f80303101a4450001040c0ca0720400c03d4004811506c0c11011a109980d0240800800086040300300c40141c00403c2c00070201d10b09540550100d0703209490011003164405040094a030400c1441d494260801c0d4244000c142c02007600b100c0340010f580c0c6031412000b0740010801000b40c100256207580041c1801c585040016052074148841515040c00182e082c00945034240d402101d4195241d590341086414031280b100c042e41f284c0d01d025a200803e041a81c00110600f805484001011224450031348080a4041d40b10000c0340c081c0b50500001001340e02a150b001c001101c011840075502d0751078500766081300400f01d031505005820817043c20820095050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 654897365 1250 654896115 654896131
    0xa031a0402040b09041d010212071101090b34030902042a1b020a0e0702010f0e06010504020705070f090207020907050306060f1b0a05030c07050a080705370e 69
    0x440d00c1c3c60f100300c80c81903200718a149800307a6140c1d03520407400551045c5105081509400a5664026901c3e00c9600c0c00f000b100e8802c003080e00e40910890354101449103a0600d03070300004100780350b01c03000303486c4130400c5580c0e1420a81c10000109038592281400c0302e210900c1d46901c01080450140c8100000c1e5842d06819900e01185004c282000001c1c0c8007460203400d240b8101485800c0740f05e60181030001c00c06401039005011100c000448180c140b0344144550003c1d0b00070481d101d402420f500641e001c0c10300341e0b00654050b800500c002c0c0f07026030007014040e102e01c0803600400d0f81c4515112900c842c0d41e0040c00390342e038041403000542c20306034440c584c000e6040c6001480c5181150001c3c2e5a0b02031801075414442c0c01245035140a544018030807801c0c8580301c2102c41c5203c040c170f4066038a41c080802a0002d000f843c60000306402c20010203803d0b9240d40740540019401c000a005803000100300940c5951503801d801045880d0964000c0134122105c10981000b82c10400308a10202d0080c0441c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 654898615 1250 654897365 654897367
    0x6060306151407030c080d0603080a2d0521090f1501030507031506030f0510060f0b04180204150215010e040b060f010e1801031103060103020618150a031a0402 70
    0x1000c024001c0300d500a5141c2849120341945041007213860040c1c2e0b501f51030162600c1408010310034020003070403405c00c441c2e440ca0800303c004040c55401c0261480c8020810508000c20301c0654040c1c07014080e040cd0361101d030f01c200c000c504a0351440100c01e94000105400c084a00e180b114814040403c4094a00312804417079495641d8050f40c548541c0700180a590b4898890312030010329811107070080d6003041e21211690540c0c20499200c000c01c40f0412140e0385455800210b01303041a12807021641503803121401d0030300d03180c212500d04d5aa501425a074580c200404a20071006070031100e440c098942c0200440c01200210f01c02c6040306030020050a0603840801c4000740702042115070103030007540c00001200032100140c5900d8181a80d8940c082d00710303243d4240c01c040d0b0350051412070f030080d03961a801c05e8400c410305455100a020180d005001000550030b0300100c5140e00d030f40b8000103482c2c0404001503a2041102ea0890503403000065164580d252504d40c5600340035007880c004071021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 654899865 1250 654898615 654898637
    0x140d17060d1a070201181a01141003020d0e1903080a1802060c070e070302072904030507050a0c03080414220f15030506011706090309120307060606030615 68
    0x11501500001c14041a02c04840340012000c0d8400e40141120200c080c444a01c40d07202864034000302c600703540a428500c0844400007030807000e00b100c8400301c4040508031040300c854070b64049020f5401510319840c03440d141c4040074150001009003d0008440c588240340c0840780c1c1c0340040c601200a080c142c541410700f8188002101d801c280c3e1444664100d6a01c1c0c6d465541503042801e01da072650224400010500c104a01c0d290541c0081100d50711600b4040f80e203044044214090400e58810a403001d240000001c0c000780c040c40090200030b00a40440380030b0311155440c40c21180251700100c0d40c5d481e0200f0100700d148803052021075000d1045428280181d1a40703c0c03070340c0f9010180302141c0d05c02d40f6480900003a071425404801001489a80707041601c0e20382c28081e645000a1003226851148000044480c1c400428407501415034107001c9e5142120200410001241d58032030f541040c04100f00c80e50026070740b84541001440f10b074502103089450481d6850300c41101140e007400f4001d410002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 654901115 1250 654899865 654899873
    0x111c020a0f031515270602011103040b0105011103040902030c12091f2c030703020c0312190e030d030b01090602150c0f091909050709030807020d140d17060d 69
    0x20030050b038040900d080005680c504013100c98601c85141071007601d415105c1225020b5010360010142e030490340081c014540e2428200300c6130310084030040c0817010300c01c00500041d0f100390002954a068081101d0906443e402408200e0703205980c0d40c0010040010100d0303101583d0140c0350744c00500400034044000880c00d880c500103201250341900b00d503865007880d03600c0d001003c885040814188513a281048058419662644540800c0d0007520440c01e0000d1079150004040180102d4030f00c4841c240750a8071141303103a0f1411244820280014660300d10700c6614100001c3c00e40b00c3c05680d0100d42031070620b0024050010607003004003150850409030446600758082d990b040011860210b668100e580d070025814080d0609403588024001c1c04150340c1142d1542d03c00568032002400c01c00350307c81e400291107420b5207110041540005024010140c50843c0b038070101103014444401d406030862038400d040074030f0800340c0c6010403101505041002182c90300a50311280a4555440024503516 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 654902365 1250 654901115 654901151
    0xc0a0e090307060b0a080f0a15020a0f110109080a051c050615180a0303210504020f0d0213110a02010b090903031b0702030304030b0105040e1f111c020a0f03 69
    0x11020f000b01d600c542064006846003070a000040010f0b0099401e26045080c4094840d184124243d600404988281e0f13459501442250740d501c000b074542081d50310041d401038620643c02d403100039482d5600c2c903000c03001c10503200c0104003025003650340d6552840c080c08060403031a01d01c402500c0041c6050104802900d0394200322101c82c1c4060800c039140c9040400e0080340a14042c0b40c00c2e004540c82c44000702b09904001c000501c01140d1011505400041040c40c04960045070040c3d40598558210107941c10a1050140c0460000d044840c40350412000d0342c0030380311844540110914001140540c856080c0310760600303001c0854564800b800d261041c0c03030f03407804003a02524aa0a010b20039a498040420455100550103000d40e9120361f924104108085424483c89004608040441885d26808203004001002104d080d80e10929030802460090000074a8100020f07000c00c031903440b80d07010a01c003680305903420700c01503038801c41c0480017815400300040c402c00741410820ba80c010300070421 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 654903615 1250 654902365 654902377
    0x61305040c170102040503030a0503070f020c09040b1509102c0610110a06021b06070906030510030c0f140a030809010503040609021f080c0703201c020c0a0e0903 71
    0x30a408640e0340b65049a0350080c1304aa026540c180310001c0c0c42600309402002440c03280c101ba072905030f006118054140c0c1c0f40d608a4142c130742c2c031000c140002400916100030558001001404080420503408081f072455401500c400c1c004030f0300000100b200f0b01066012181001c0f9401d8580b01c410712030001e1030544103020303000030f100e00e5020b0505180d2910a548002e05001240c0841d0510006800c00d8802548016555400202c4074051101c841d040044c01c6c50042d1031580d40d04681c036103040401c40040070094031000c2000014000000441c0c2c50707194400141c61102d10b4002d1042c44d00c4499030200c00855205405030750301c2e0400b0408114541d041d10100070081c20019526611890f10b40010050740314020352103a075a030308140d000400c40c00601f4003011141c5450301c41e9202c0e00f0112000b4000c600c070050004940400c021502a1030aa81500c0c82032072030112480e46244110200c012070800200c5c10069001601c440c00d5868038044060040c01d82484650250070104040c41c2c60344a60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 654904865 1250 654903615 654903629
    0xd140f16051e0c010e03070b010e1b090d03180915050a03030903030f050f03090f061b09040902063a060b0d1808032a03150112060b0d05061305040c 65
    0x1154903c0e940800390400f06115210b4804e5030f40d50a02071030a0b00a08000b03004d1916584900000101107513818280f10158400030580c150826004034100700845000c504102d0030404c00c5104451841404e400e9900904410400481c0204494142c0c800c03658050340001c6c480c0c890034034100086904004900c00b07a90309880d029003d42e401c08404d80d894429006aa81184000803c0106001020035004001040c0d20284d41c01390701ea1b00700c44d0340d624103481d0070b070490700d202049450b1003460564000842c007480a40128140603038603483c0f010840c6080541e103c0383e144040441c20302d001c484544140c8680d1034604000706401c1c200c071044240100c28070304c031400ba600c0b0115810000e80c920b4138110280e20070030b00c42da2460594070350046100001d010880059103440900000080034040d41e1241040c2c503501c40d0540308100c01183c80104400303a01090300c0e5102004120512950300030401a80e80d0032000c03981d410800140042c071390340700c044802120318042c203100c005150803400340112580 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 654906115 1250 654904865 654904867
    0x50301050909190c06020d0215060d05010f0f0e060c03010609060f0c050106063218010c05060106020a0b1623040513090c120302070603020d140f16051e 67
    0x40c00c2c48030303140051280b0034005005140c2c02e20010031040000c480b0980d0103079800e4400c80c1d00d2141007030340d8a010303883c2624a80181e201c001001c6081c104441c00142d8003e00000c152100101034100c2160107030314003400c14a4445009586003501041140e401c0920186c1882c61585091001822412540220780030046403641c002510381c41610800e240d66000002000204d5403000060302e040862541d19051040314424090322204050700c1d2096400d5503003010346404001d4000d09000c4507801d8080b8140006c07070700d504002c03c4040014601030140d6400030035030180356040011044a005012400340100c44036884000c640c0104220700a440e40054000c1e44292004078000f18020358210780c2e08140d24900c0300d220020241c001c130100034014181c00c05c4443d26040900481c400204020340035902c820000c0145600c01c0d0b00130408810010b00010b510105503a40240f8020290f44001000705c0820602c4103c5101040c402d440c03040c0d60030031501c7c0c48050002c035503c2520802c400c0100a030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 654907365 1250 654906115 654906121
    0x12031e090f0312060a051815010309051506041509061a07051b0102030f0703031d0118080d1d010c0206060102030c07050d0c09050903031f14130603120e03011b0503010509 75
    0x85010b0258094a0010116400003106005081060400308c8010340e00030384402009143c0d500a100d001501034210f8081c184c01221004001021240940f40c207030055510561040f201e61443c5680c4040c00b0104404260300e0304d0004c444681c0c03500d02c5200d01850004104c088001000004c43c1003441e50759542111082d200a80141e0460080403902c5c0c5030b107000091698100b6a041d07011081d500f1000a200c44910310010700355080b02c8098204104041a919a00020840c41030240c1000b900948020480340c1c1c6a0000b84010540c03102032460b02c0e9102c070035940c030f40354050003415400a400c2c80254100003001c072889544c1c50751803041c0c5003d94a4200140300307010010800d58042e020303400701849182850a029030783e1b0740c01290042a0b0404010283c1c0c400550401e14130201d4035a000110000c000e540204214148030b5070740c150f1201d58a03d00000094070800440c1c0801040d511814020200d5805043c02c0d1000f5000b8a04020f00303c1d6041044280c000055134107540040c0c44d4001980d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 654908615 1250 654907365 654907369
    0x4060e19091112010f0e19110d060e25030b0310020307020a03090905010e1503010902090f2202130903200c211b010212031e090f031206 60
    0x40180d07008880c505040c1001c41000d2152034008080403645034840304816aa911404d141d000624091410110038020200d41011160007144244004c030610025a13030b42c000ea240703002c03680007160841441b0b4603542c0070414000f585001c590300c4100369160107812841209500c42d81080911128145030352808081c0c25030310f00700902c50181800041c02c660703a007420300021b950b811034028210002480c0b858085414421402014100d0b480780410242903107400d6404042643c604050b2501136580b0003010003da82d500944601a500031144c042c4241445160411a41c103142014260b2030362880e06c44005807146003480c900f021078100b002448a03290720f17003142d11140c1e01c4120001c075802191150612007000c1040022007000311181c1c1340c8150b8103014440d807c49144002c6071590020f032480811048000e1407021340820520540d8040c00259a562485400c113503044070380307094036040d603c60380303416072a00681002c441c200a04411030f004850540c1e03403040300c401c0071210b0b05040208901d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 654909865 1250 654908615 654908659
    0x2030a02041e0f060c0506011a070605040606050901060306031713050d06051909050a39081209090403051305040614090a1802091008030705030a0306060504060e 71
    0x26180b40816245600701200000030804114060180250f040402c00200d15010307020030300784c40c0c0d8020301038202d80e0720307000c03244c2082003556041a1070404100504000610644255845248201030000d10f4508003014050a5403058000710107062501c042800443d1b043c460307a6022100300c41003e980c0d82c0c0c2c261180c40100e070442c0e110b1038100e000c1110000402440c1c0e0000307403080304001c03c180b082940581900044d150107800281140e0860410040070894403003001078029000201006403010342c90483d224000f410840c500410604501408400010322102503401c41c1007d0507030070014140009880030b0409000107050103000034802206002d024040c0008107801032082059669481fa82c0440002c4c019019220301c0710100003c08640d9103118003000754064411a0049944039404e124207000302925030a64009817510001c1c2c026010001015054480c102031600d070105084090159007094101100b40901480140b1640da800f0501607103c66041b40d4100c001c103442603c0712a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 654911115 1250 654909865 654909869
    0x310030210091d0411040b040b03070f080c0607050d050c01180602031e0919030c0204090c0602070b191b2f01090e07081f150e06091302030a0204 64
    0x4901c03044482000d54200140b042110b600a03001c0c0c00c4580066100014000212801801c81c3d640040640d00782c00d0680c841d4000100242c4002030b410b1a06001900d800b50f00e9100c4902240081814001c5800a01040c2481102990900d0501c0500e41d2510b44070103a49144204000000c6141c20840c0710941044095560344c4410b001540c603942407005c0a540100c3e54200c0010703840c0a10b800c514040203106101d0000b00029141c4550101ca5041c080e1306207140c19030030040e24500303400260f6118400c80c1180d83c0314480075a480344c5880030207410003403a50300c1668415002e01c0b0008004004003012140c1901070320340131442c0500003020705802c0301d0320840034041c2c1482602000c05039000d00d801c450004040ca14040d400c101071030044034041114050010b2005040002c07611441c01010b41a400052101018410510131458004040040c3d400442100c2450300120160343d00030042d00c4c140901640c94a282c48915000b0441e548c0c4200480319000358000002036500d1021390607500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 654912365 1250 654911115 654911119
    0xc05040909031808030a020706210216050d020d0e09040201170f0103020f2b08040e0903070b070305010b091228020306090c0904060f09080a051e1e03100302 69
    0x1c140c0607642002030441182003481c9450780c0605a004c1545200003050b0360400f04564014504079080c1b0780e0848101454a0701c21014813491031a440f080721840c0040c04036502a014861400780341400d00d64507242c6c2404c246002c0d0342115098045980e48004406100c1c071003a1102041e40c0c440748012508001e180f41c4000412217044140304011404001c8503040b2402255405074690f1180d081116104080507400040c001c000003503480901166110110f0b14081d041440c105591041c10b40d01c03440048078004c2440d080041d00e2020400c1d805000d9400034000e180401566061204070034403482500c0c4401d00c40c02c05001da10880c41c408001d1000801d000c3d43d00001314000c458003800341142c04800072403083c01a0700c005070b4582c0e8000f070039004c0c210004100c00644e0305d0302c0d100d0314000c001c1c0100b42110180c48460210100384101e0091182400d81d580300c036520050407a105070540a500d003100b81203807040068500108040f003140d084117000500342544c0340c070380c0030140d40e8000d8640e000035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 654913615 1250 654912365 654912371
    0x31201240807181d0610200705181b040e0601030209040f060807030c090510060c15061814040803161b051609020708041404090204060902091c0f060c050409 69
    0x4036002e03080b1801c5844c210740b101e001e2075540e1240400c0141c011906012140010030401c211480711041048101c5800034400a841c000c03520344c80443c3d40c0105041c1402d80c400441c1c0300f0700c8004854801d9011621401c48440f5041c241440161842800003030241da0401d90045403100d0665190b9200b0709110294100c204030306983d0b0136200c0d031905040d200c151a43d002c0b903040082e141c501401001d03c1500403055000000f400c0c8541990401c40d0060156010380c484000c0705c20310486842180050a00c4152203000264003503508401e40340c030a00c10300a404815030a02001810b0302081c0c0e600005641501e5081c45650041200c0070306014105a07803181c0984508800d107c40400c0080110044040071980c4544441c1680e081c2d218940f4028800d403020881000041010a401420032030001e0010566000c0380d0001020f035102604869038841d8001914400c42c074107100c400340c1b42d811241e01c07244d60a130300e40c5074192207511003503003e00280d07100c081c0001c2072489001240d029000140d010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 654914865 1250 654913615 654913619
    0x20a0605210106030b041103010e070c0503040b0433020705060d1e05041407120303051801050702010e070609050f0409060e1b031209060d11041703120124080718 71
    0x134090b00712500680c3c0218a00b1703403021145034802e001c07030b17060b0340000d100c000c515104c40d4400c0300d40c006c0f000420380e0a40810700000c61145804c400030802401071140e142c210005090302000741c0c0707858a04108106c0395956203070700c80380d4001c1800d80c200d44003210856183e01c0c0071072200b4090801059401e50404400a040c80060503e5018a0065003d02c01000d065200c90301c0d001d40d00c181501071040e10b010501340361800240b0a4010940c424505481c80300c0110133100c1036400d6640039500c9402503510b490b10068001e800300f1902c0c000701414035000b5044c030710303100c0414015501c545101d402103494040300014000b0641200080c240b400c011030f980d483c1d6a50701c1184413032540720000d00c6402404110b004012480301030796083d40004210601d0300f15048004801040941150040000d0600000400703043c14045800542000300203035a5400403000c031103a000034160008013402c00840040d90504c000031000e045031441c1410101e4090705c8420080c0c3c2d8282c01e000f40301c410011f00b4000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 654916115 1250 654914865 654914867
    0x12110c04020f0d05010801270f0212060711011b23030705030f010f03020f090a090506090a06060e070203192d0f1416020a080d030e06090a020a0605210106 68
    0x8180c1d41d44103c0c0100030990f00c03480038500342c1c0c9002c0c010004211200006126890300e41404002c1035210704400100c00443c2e901060652460048130201034101004000260303070041050030b241900b0307000070041d01400281aa07486d103002640c3d80e08100924144540030042030203160086a104110380c0d889140c0b4400062081c1e0046070300107055110b080001909070070544090040e03da00914034031000105d001840040b0f50b000380740309581032b121308542c80030030800d021081c003c0060001a0040c3e040a0070150113540da1580200c2c1200fa00104200b41c0396800f10a80f030f00c03840c0c0c0704240c403042e404004048901a41c14100f065640c1900306142d00c646110341e20051400d074150708d6254a01c90b101c1c10564501815603904c00002c60304026620b410040c0320305000c03607548014804480320352070310281b80c50072408420200110365200e04182d00860104215584022820300914414500e54042005049140b0030710f412f04c440401c8000114a01c2041c030a01583e411100c1040c1c0d40c0c0d90a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 654917365 1250 654916115 654916117
    0x3070804260601030308040609023024060d150606020705090a09030804023d081602070608060a230a05040b0a0b0708070218101212110c04020f 63
    0x155880c0310a00d01c1024050360500420894100c94040e281d01c0c010782e4460701c80350301500c0c1c0070200300d0344001c03d201071200c202901d403502c00d00d0306414091040c8ca0070740c0c030110629081030031903803143e0755540c92215041f1824920070140c0c0010251a00d000c0042d1501d007503680c07912280b40c25013406041c80d4011030340740c2d07000440750119442141c140405407a020000400c50312188006400a26080c0006015041c45e04c14900b2890326460311032001d880b0720300302803003000e683c070000f9085d8102c45600b031701043c1d13010280341d4100350081c120b00403403520004042c1d602c0716144a00410b1100700d400264003603640341c107185c0081591000211403d56400040e801c0c41c0c18034005144103542901c00411141410300c03505030b40030301c040c200c0b60415041c0402c0b0b441e21340140c6400c03108407000300080001600e5070150700441040182100039107052144c44601d0034442ca41089a1403041c008040010070b40386110341020048a0504000e071814004620341803c0072000e1741608203000150340746420040c50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 654918615 1250 654917365 654917399
    0x31d01020c031c181a100b03070c1713051201060e0f0405070b190207290705190b010e06010503250e0604140405090c011e050904060e01060e0906091803070804 70
    0x841780b107125903030301015400100340c54040d40c02c0c511814000995002d001d01e1000740042d00030813401031010f00303070211803000f0f0384089001e9480e00d0f0b52583c01c00090a10200750948001004001d00c0418202007000320403d00042c00041e030125031002042c00e100040c440003014003000c5007000c0e582c400140511400e00500c0c1f800714010b00c1000c01c005110320210190b07031400e6510300c0440745000e5041c000014180c00c541da0544003400344108140c01e0440000c0c00c49401807140e6202c054a40c505800700c0d80f181d03002480789060003002c100b00407482540e10711900010b242005903007464038020790101d400760344040c500c9801c80070024001c900d200d160304208103410000c0350f041c0020742e680b41c4130783d460700c840d07240e681e010807000700380c020b1840914240300740a000140707440c500b0401c8110008050340c015502001c5d40e80b4001300181b1400760300602d1880c10381825580505d0071700b00240484e40d6103800030300c200c02e40c0490401c1418100000e0003103030f919541001b92aa111616040741541401c040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 654919865 1250 654918615 654918653
    0x30d200a030f180605030705130e09161a030a02030c0c0d0503091e063c01030b0112050c09070311031f080604050d1d040c031d01020c031c18 62
    0xa040c6010504070002d9815180941e035094111f4542c0c6205035802d400280c0c0d42100c10700518004648844211400c1e481001607200903c120320024212001046507900001c41c08030600c1c95030214005148102c035082211803c00680d266103506840206006428090304907010b40c98161f84000e0340722016501541112041d138540301031714445603501c08541c00c01001ca41e04070000103070401d5881c0401d800080d29090f0605248205080345488043c41d42c09000011350b0618014400d0142c50015107001d48801280244410b05030740341d090369002422440352140d03a155002440d002d01c030b60041940000d52041300764503420b00e061b1f0905901425501c200c80d00028583c00188800c000a0b00c0f0700481c1c202e03001d0039000060b607408a41115001548024030003880c1441d91154445c0c1c030400501c801d15a4002440c12140e000070070001c0601c0030b00c0c50040e0b0042c050340400301d5002c002c45a41e11a00009565811f140c072800002601c401c4c145500b1160a42e40d16800703101441401218002c41d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 654921115 1250 654919865 654919877
    0x103060b03010b15030402011e090305070e0702031813090c140103020f0409051512010b030601050a0b180d0b0c04080c01091202011206030c181109030d200a030f 71
    0x50031040c542200c0d916071203554800905000c400c02ea42070705000b540c01034010700d003a0300c401f00650090301510382243c1e2150000f0700358800810900005118440181010907100c4046007080e0381c00075568011400001c10240f40141d80071416a24800086440e041442d82801507100034141488a8040e5214040071144642a41050307036200e48200e840034003c000e04103060500b4070441c00011f0800800c0006c654503468582009030b55017040c1c00300070384107090000c5140d12032403050608020044e8000340c0543c83d851801d1102c0701e5105d05a41d0110280f402c0501301e4800034000072040204000090036221200040c00103260b0510020400c4e60980d5040fa1120f095090044940c0a200d11400760702c1c9092229880c010740c40340b0104220144181340201c1c01d19202e846134481d000b000c0d80542d400036036074140d800e13a251407802604c0060300741c4403549061800f85804a0b4841d90100786000410101c240024103145460041d00083d905480481d0404103043c5400740c080400c226143c008662 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 654922365 1250 654921115 654921131
    0x30d052802130f1820040312090e0415181511130807080d05090a0e0718060f0906230306060708041509120c030303021b010905031b06070f0e010e0d0b010306 69
    0x4100d07401d0030080205c640c051464145076444446003403001400400803c0780309400043c000d0070283c80341d0301580c05400d9801c40329244100d10022500001141c00303406040281301c4000c40c0150f801606074020035440810000b01c1c483c031a0b0480d01c12804a059813103a03c2c0c802040121002a009081e101004115a00711101c4002600d160203072000b81030f8080031201060004c0c0000c00b10007600f00d1020309020605098100c1c004910f044a0f40241e00010098000d10340103a9018a129000309070604003a403490044400502c0e8500b120718551a8244000021030215140d0750704a41c0300940241c000c5840d244c44009810744c0010500000740042d64120010030381c900048020ba8a0030760156458042c2840e584d02075020350081aa01c1080d81c0755811281585a000c3c000d2040c0340780b050001d16524804424101640041c45480c0843e59001a0030000541d421454040d075039110f07400d010400c103403500c0c0100c0d55401c003101716a801c81000c10f480c0e810003d180c420103050360f2280b802071121032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 654923615 1250 654922365 654922391
    0x515030709050a0513080712200d2a021c08030906190204241115160f140f0f0406020a02150913020c0309040509030d052802130f18 58
    0x201d41000702421784001040600000b4000b021182208019420206541140804240200c0442c0c9c1580111a04421840306c000d59100700b6070358009100008040c0c00311450240200c0500390503030b000703016482c80302c5003da80100314180004183e030700c5203400c0c2c3e981c82e0614049854100540b5038400190b0000c55000400780c8600a950a4800e04485900d042c4804c407900103403002d40148070401d01044a1010003032034424800c07141c2d01c002226034a402030501e40f10940341c3e0b144808000302004041e420021110380e003d105001c1200504030020740714141041c5110051040ba180704036015000900040c0103500030919032500d0303000b16200300d400c400c1455424101d124111310294007880b0304e0b45181500c1e48903406416aa40c0002c00c9900b481c4441b8086411140c06403111495944003090588000c04680941c540c04101c60325021503140e030b402c00b003034a14480d64003d100803d03008a8441d000745200740e45503000f44801c449802c0465680d4001c2511900d202c03c1c6810801d0424540500076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 654924865 1250 654923615 654923641
    0xf02010e0c0916032a081f060c0303020903071508060915011803021003020913020a02120306031c120e1522050703061d19060515030709050a05 63
    0x441c0080d20400640d0b0722a9441e152240d440ba4084003071654603000260303010541940b01c01e02c1020982d40350200e02c8a05405800224001e0051800c110000c0c2070401260191040804481e8a4240351606516030f00d0250064080d04103901d406114808001982c9407901d219000c061069880b90039103520b9040500c580c50700104c8010000c152103558050455120741d01070711024100091034803a644e1a5400039441854840803240041e8000c500d481c541d1030212841c0002c2000c1e024114500a2400006500d07809458540c80e01400084001815a00c082c40522809895400d020707543c0d9124280c060b041c411104501001585807002004000c000050a1120941108420020b55540000108150560b40c2400408000c05c200c0310340082c2d01049540051448bd0001042010a0300413101c00e201600350403c4441c3e11844190300c03180c450345040031318290008400304050b520100814400403559940c15014800c808000440c04620f80c86140160102c00003442240c841600c84615 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 654926115 1250 654924865 654924883
    0x2010e010804050a02150d060e070207120b01120201050d090c06020c0f090103020906031c0309020312120a090804080d080603011d062a0304080702120138030d0f02010e 74
    0xc031398012036200001d07107080303001d071481031400891091910142c1d01d000c2050f2051a1f2140e18440001c00501140030f40501c41e035000340607a101018000032854460607420354061103840a50130030209a201035900c10b80886031100030100c030a1190200d41d20f0300000c4400c0601c248070041c00f840b02d200c015880c115541810740b0701d008100322490f174215020040703144009490180d142c4140c0d07000403807580450400d07003d068800d4070005001455070040c58103180030740c141d401d590700b402c114603600e0030400900b043e080244076a00145024083c075040c4050b109980100706907218981a244016903c0450244540c105a000307002020140e14101d080c226207103c4842e417504294005601510881c444a032545c2b141e4044400e40b0f0710040345140c40d03074000c0c2c500340c032968000030fa81c1c01541417101d4003d24410030b10008010b16140340301003180f840324041c807000e10780344e03014121400a440c1c0c2c40d10040f40d550082c15100c017058924000741c035199000102d00095400d004844e5450318012401501c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 654927365 1250 654926115 654926123
    0x1a1b06062e031a1008040507060305010608070f020703020603090106091103010501090e07021c0c1406250c02060406052101030201051605011805070f05040e0d0503092802010e010804 80
    0x114801540c8058000d000c0f02264100b03a100c0040c0c0104203680c40800c0203003c0344003030300d6017425400c0905005003852419048601414141001005019400100194040c0312071402c0c80c2d003128503560403400c02989a00181d401840401031207091901984490100c03030003800100000030440c001054180003d2040c94081070491504001030742d4030b116425805503581c8143c4414200400308a00c3d04035100b6944070000715207507605010084500a40501000303034100905282c6098802030355940c8100c180c209902000c001e8241c5694090705c41c285006500908140d1503a80300c1c4001071140d0000218020407040c0c10060f4000b2031854441203050b0b81d010f94400f071400305901c2d82141204482c0c8021500c544d81c42d043c0030302074030004a00a00d0948a500034100491401e10515083d48882e04141d102c3ca2804421003085c0000191400c00c102d80c80c20310740c2e01c80e07646008550408600951015050006100140c0c0603000d070b0030302d08440b901c00d03210400300c0c044100044401000c1200c0c010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 654928615 1250 654927365 654927439
    0x13050f0307050d1a01030803220210051e19090b0f160f12020a030816090905180d0e18191a0d0b040b1f1a1b0606 50
    0x80034a00f4400450707510300b400f821205200f40c0c25040c182022580036401510240f2001c030030b11141172035080d0900d060f45907030641400318812540002d08800c3d0980046414131000240202d004022075500041c01d4415944068480000340c9206512440fa006100c00190b120600403c2d005508002e445c1100c4a001c10329040c01e10b00c1007114001c2c011401d0644281689030012000070742e01e4441c80000315042d6000d8800c41b0300b5880c0142841c540500751007113941c485055100010380c000340000031038600c81d80100d650f458a1045410140c00308502076001c0c0200c089045032142c021900800c40a010390f118001001c07554503d2544c845d043d210207003000303e2828500144040c076041010081c54010303078200c03441d054400240380c9160070142101d690484404100a220b90700c501140d20662009416245000046046200c080301e0b01030b040c0314001c04045003d880014106030b1b410041c01b004400740701c1c260640f1b0035607107030411503000344206c007244086003e80d8454030860f0a240007102442c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 654929865 1250 654928615 654928619
    0xf011505120102040305031b100204150e03190f0204061505071a060904030c020f09151504050919110d020c0c03010b010f030b01170109060e01090506030607030c0e041113050f0307 79
    0x3281c4e1166040c40b260b000e104200d043c0410882c40c0c2b005100400d80300300c200b183d56040d40e00140250380c032480c2191283e001500c40b040c0c18180405039014981e0300c05008091407501d072000400418040c1c03c11031000140e0107030300b00c40c02c0e008030041039058011800c080b64a80308140c2200441d00031100c042d00900c03001c4c08900044d002c0c0d0029082070703100070304114502c01c1c0c0c400030605140048400102601700c0084100150409122840c1014a0b2208035071505090402146480401400201800642148584010310319602c503440d501110310750360b03644008006809019400c03021441c003881c003a00143c0039480c94144510381440506848800c50300985450903802800400e40c00c030306000c40b50b15400060722000300014080c001c0328100145031070412020a220400580040407800d00e4507052080681e07000910a82c4100545808100b202526030101d5031306484402d03c941003402c000f003c000034581034020b0281c144021031141d511542c0d80d402c004442c100000d1080e0144c20020301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 654931115 1250 654929865 654929887
    0x3100216030818010e03041503150e0603030409020a171303020a080a0302040503012406020d0801050f0a0e070e031606090e070c1506031203020309060f07020f01150512010204030503 80
    0x481e0368010000c096059180303014140840c20b41e0403172000744255810008043c0211188294aa050201507103001c10200c0d014a80c210a41903580c00f403440604440340009407585da040003210068244d0000c2951219240b50001d004141c01003004626034403140c000480420f0a040000c2400b50140d00070a100342c10341c0c0300c02c0016444003202e0020103808000200702514240514400c0d25581c11503000d031000c1d507510403c0344190399008541103400132171603848855841064103064034021641e03440800d50f1100025100c13034240d40044001c0c0729004c03c000d80e0b1034000106250000d003e5042d540840100d50b01c0c01c0c481c803000c2c0182808a0802241408103000001001341e0000342420300400b50340482e00c840150b01c040024529040d0380b152400d10400000820b0742e0052030460800b9810340c240842c426803101401003001c2c07100340341c1700c001500940c0f00300200c21404420500810100090010848900c0741c280682070007001240c03c030091b100c205200b11021240c014028506080c100c2103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 654932365 1250 654931115 654931127
    0x11811180c0703270b040f081204090f02090418050f1c08041703010b1c0b01120203131b1706040c030209070c0506010f05030d020a0302031c060e01060e0310021603 72
    0x1107413411500100070061020000d1400c840094010200b0080d1150f183c04804110340c1c1540d0800301403500114000301d2400d00800c15101950481c102c08243c5000b9108114020b00030090b54036401818010140d8007042c1e00031102081300d000340140d881800326080318596503202d5510411084180e4851000c615204601081c5c106100394040308c20030743c1098142c0c0280e002a040308146000c001410700000c07031008208c05203440c048800788011141040080c01440440742001003090700000001c00140620031246000c0d680002d00211130005803842080c0308c2403d00850304088521140d2900310200020154401c1790302240b84d40c81541160f00b800b1500030080c107102c0c01d01801c03100f060001001481000c0c00307400c03801310b0349030b032680b4040415144c416940c5580e403d5401104280b804280d01108448c2800c0080d2201001c18900ba442e0720014006030340072204400078000041001a403019042c040c00324203c0881c2c032150344214030b035401c92003580c0420410150302c441d000d00080c0514 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 654933615 1250 654932365 654932387
    0x105071209060f09030e0118050603240409120908030906091909020f0706050106050304151a18040204051e0601120f0516090618090905011811180c0703 67
    0x400218000c0614240c0c0c0c800e464903013008070b01088402c0010945960700004e542e40c02c19045100d004801d1034000424140e210190801001c4412001c0201d44c3c0ba9580141d1400358a0280c020003807400c090400305408407000001c0000140c140c0400910721200009451440f900100006d03c5e14184000b04090b03014850301031280007104660001d11215244007905d0050070174030341b00d603441c91a407509101710f1304140c000b1000d11400307105001c0441c41010070312280c443c180e030000900144000726081c4500e40c400c2000d5100a203417030204485065100b500c2d00445c82518240540e4803400e60040313010840a007078020781042540050f00d9503100c1e80c0c03a18252800d410001071031b0b4803580f150405451080700c00052a0345455143c29075194814001002040c0514000c0082d0181c1200c2a20844092054180361a29800042d007408000e6000f800340885000c85032075a40c90600d4240400c0c0240620a0320956001c940c0e5103042895800551080e07518680d0780386007403a0b994040d6900b214035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 654934865 1250 654933615 654933623
    0x510081b0a030b151912060509070f0b0c0705090405030a1b0218161b03080603071508010602060106090e010501081b0c1b03030403020f060304150f020306030f0105071209 75
    0x1d2040040441c411500c401c1c007440381d00c60500c8190aa140510241c0048003c83c52038018404100300104840c95800e9110780c1c0d0b00400200d100d0710b03801c203581e01e06800c075006030000e0f00401c0b1001a000d480b003802000281c407000117548089580e06c041100c4c00754115000b4000b03400030412011083d100c0c1050890914600c0c0009441602c1034010588480c0b0740c0c00c1d10714030074107014180205500c0c0d03049401688412441c100e0048900165010310304a20204000d017481201c00110b9250369042c0040000303440000000c000300d541c81d03e802001203100784628805401000004100b0700e01c5400100203503084030b240400a03034a8034004544681c401041c01043c42510840140c106941100511480348e90000415003824031054401c0f075008030340c08080c40390b0310400007040180c580d20105c030b081c098201c0700b1a8495030390742460307d1410700100d00b100c0054075140114242e0702d081e5000e180a083c082d0103d17071511080030552800c83d803042e04c0100118551941145164402c0c0e00458551886 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 654936115 1250 654934865 654934879
    0x170c010e18010b1e0712271205030f0a03020306190617091603110114030603070506030405031902010510053001150308035a090703060510081b 63
    0x40c0007903101c66a00105822244205416104520b440c1c2c040c41f0740380c1510081d2866540401c01043d01704920f00740d4800c01000b2800305500c4820b100c81442542c207c014808440c44d903800c1180c0d0020025401106e0840c41208101e10045150f0002a070700400d03184503460b44038140c00ca0080007503081000500581e9507210341000222001d003405003003001984960a2020424030f4500090100240c1e041e102000103000e00402101d0f6400241d000704807882920100d42d00c0c2ca0300d0a209065108240b9010200c0c40701480c445540f95056110b148201d03400304012a10a45a404000d83d0f2640c00751841c8034003030013104890014100304286061034181400004000c1c4e82e03000a0f05114515500558483d031010080010032808000492840721010701c20380d44140c141c44241d98070101c040500030b40c5645041d070303000000125188d0060f04443c10200d00d0f81d14a030a0407002c1d03907000180012500141001c0c04100d02c0e0150480d06000d0f40c3e1007c0c040e0070041c0c0c4204107c400e84034512181c1d9071004d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 654937365 1250 654936115 654936157
    0x10b0f090a0302130e01060b0702030c1522090c081501081503071d10031e0204091703090f0c010207330809010c0203070b01030f050106170c010e18010b 67
    0x38130703998980580c0c01584008500c146070101050308440310381c0d1028440400070820b100040c2c0c0d010a01d811404011a5901070010180c2c0920741c01e80500c3c20800e0700e8110307440c030b032104018034400c80703a0894000c03c00910002d81c0509086903010000c0c0c0d0340c02e4204054000d0005690b004106183d0700001c40c1806941d145d0031000000e10740700c095441700214006040c0c65000c440880c111b00c0c0c0d404402e0192070640a850340ea104406204520004040c44005d240d004045540b5900075040305504546600a6008941c802c2443c030703071041c2c420804a110361680059030500c08202c681c85a04160060003903140f9098906000781d1800b482c0d040c6100300f51107078003460781c048000c0c080c0701b041076610b1407820f1605884541c2107948810200c01558000e0200c0000185014036070ad05596100c5c12a00c580856441d0280c09010b40d50041000144500b48122150360001a14192410f0982e907848813800c0680510074000140840000184039000c014000c103c012001441d0140c2109801ca04140c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 654938615 1250 654937365 654937369
    0xc050708090d26040311030a020a180906060b03090c01171504090b071701121203090303090b010e190b0906041805010e03030a06060e100e012a020a0608010b0f090a0302 74
    0x80d400c003000e207955407004130302407040c060000300c1c46012180c01d40090500c100581c00046009125104104180103a185d03039603460b9181d50841d042d16035100c503050000351384a25010703070345400441d40c2603140c2c81745004810981d0310645034064280450402d42007191104408500b400e80d00d00e28244d00142c0310400d540c0042c280071000e91082c01c0540c1d48026500b01940764001c80b035410b900c250b01d03152051214401003036228440e5110b1000506000584100c64501640504a0200c000c0c0234260071100006110307510a5590380303e030591860840c3c80c90100035100084424440180341c0002120380090124245030340200000e00320b503c0b80800040075903a407503003540c000c0188a10640c0010007404024819802280043c1c00282410005802b002e00420308003004858400d041103000071592001d039002d90038000b19070b040340c041c6201e441c3c9000c446001402640c0001c074040c0301c480400107006803003040710a040c1c030f0b0300ba050b01d0703c0c058854030648915004241d1141d03110201c000c00000503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 654939865 1250 654938615 654938663
    0xc030d05092b08130c0e06010c17040e0702120d1a09040303140109020f03040213020c030a0c1209211b0801020403050d05070507030f02041104031a010e0126030c0304180c050708090d 80
    0xac0302e0100010f0b80d0ba42880300720380da4540f0103080c1d0b02c15548400602c62140305007806031148034a000c070300051880141c001a0345090207a8200303d130014040e00500082c90b0b8035400ca2034030016003650204d050703640c0c3d207108402c81c400c484400d00b810390f051020400602e0200540101141c1c141c402504040b101801c06041d42c0c040c500b1a0f0108210281c01d000f000110384090750076042e00d0400d07092a6191000c00019102452040554104512205001c000801201203c600d0700c03500036420290b10303021024001d5125000544080c807940441c4a20644100201d411095202d00a070407141c0c074680e50590220a4020102d80c003e071075104138050301504101410080d8002d4014038003204d02900c0030000104103800080d6803000c290018041210260302d22552054252022940403241481060075800303070308031000c00f6000000c0c00041c3d40501c8841d9007843d10100300200b101c4460400d05a0315445100001404564140701580262500010380301003540030f51140c0340a0030108000c0752413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 654941115 1250 654939865 654939893
    0x30d050d0e03041d0601300e06181002040311061c050f0106181a09060403050601150f03021602040e011b03051801020c030d05092b08130c0e06010c 65
    0x10400d030f400300b0b01404c24084044180c11150030b0070101d000041d80340c0e100c8900d15466041011890502c1c11414005803140c0c0601c112881c260180c1d0f0143c140242c01200c0181d50200240d854403035144d4081c09880144203c0e82100c0d407080980c2c2618204109000d42600306000c0d654015002e0505070303403100d205010703452007440c181c40400095814030364090102070382e81e01d800b01c058500c11010b02190403036041c1807403012544400d0076114801d880c0055107900c2150001400e41c00303040000642c1e419148041301c2681c80d107403145144c140c001501241240280180065012840b41d801005401c040d0b00040d180c00f411000841c082c01841c1012464400e62038002e80082d5451080002c500c02d40c00ca04e0f4010304e904d10083d86003c00300c00c1c020b640c0b40500111140c1c865500d901080c1400020440403802000c50f5504444c0f19580740d5900b81d60706d0382488080003082d901ca0015080c0141074010414091f0b00c100e100d0b1140b030806001114007800107090a05101c4405030f0940850b13005040d920b5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 654942365 1250 654941115 654941129
    0x2703040305010c030c050c0606010315090e0105070e0108100605070f140d090503070f05090604091a071d091b0d110702040b24070302030f030f24030d050d0e0304 71
    0x38040440ca0f000604039004040c40f14104103080c03084042140b8007146094200c1001d180204004000518040301145c01e5030101c00c0017440c01c41d02152000042d04410b10440060300c030f11418660042c015211104c2c21605501640b002e0b03031052240d20701400192501038080c040f510150709250780c1e820221401258111803030b41c8071003078040c040c0f0344c02140702018201c194003a00500b4504800386104911030f0203203511405040d0f000590350f880715030106011540201250404464410500c0d003070300d005440000001e1603070315803012000c6100301c402d100c503007000e00218020f542c0d41e0280720903003059000844440030b040021240907001070284c100e881d0085150240e90b1401071040204596020108500484030300035038404501c10040410a003241180342545c1c2c1303406500d030403421849030040c0888490004810300c840754101d55641c0d071192086007810f01022210b010b500718807200c2141c00700d0385035203c028120010303480b86010342089420f010002c640319001c8c2c075401d419904103800c590 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 654943615 1250 654942365 654942371
    0x110a0c0611090612041e2015040b0706090204020310030c09061809230d02010f1103040201050f0405030a150506040b10050c0c0607051513110d03020313090f140609270304030501 78
    0x5041c128184c7c0c0c0c2208152003200c85072880300314180300410b0b5000303030720a03162500004202c0788184030f80d80d00080c00e0581c2c0280210750300d103050010208640c0490005403080010301b1000710751f02580c1e00c2010242c80c90300845508000e80740085602412008038212081307044000c0c03d003140c1d21f60655410513140c1101c090201140401d0009017103d800a5603004118180315121120b002600d04031b030b4000f5020728146546940c54050f8010034032450b4010f80d014404c1155480901c40300c40d18500b40c244414601303100584640c800c00098455200d5000e03441f1800b580040300c105c0c0a81c6c000c04850880b50309441070304401d80000b503101c2c0c1200030151000d0f0841503140300c030799019040c2d141d030040c4003040d0b18840d01d01c181c8582d40032101c611581390044400c10558030505000b001500c48440305401c180e14495150300510001e42240816900c00508200385078520311032000c07007640300704006002c0305000d40d641c4820010f040c00c80d12101100c40a44603004010328003c1c030080c0302940c080c2c8004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 654944865 1250 654943615 654943643
    0x5041a0307080c010f0507110f01022113060c02010e0415170307020f01080c04060f03020903030309070302030609070506073905090601090621110a0c0611090612041e 73
    0x16040c801c0c145c058804005c01005500d0001e5049001e03411071100644610600110070f000503813a101d444070f22840c200c0c0301c107aa006001858070b8000d2035400c2e600c103000d0f03006076070b911010340780110281740090110382400d01082c654141a0b014216020406a034a144035649e034403a47c01005200c98141055000090b2020a50801c1424688416000c1c1b0b814552413601c0e07295032005e401a80241e0f000c00c2119040c0c035610a21a8054680410008003030300e07a21b0811064603a52600a840300301c0c02402200c00161586001069550446e640640711904d403501d1a5900e600110700c00aa2140303c908040110780b01d40050070319640300c1000404076586a90428040001000b0010f0903141007011092051000c00e50155211307c04c442d0281b924a0f004007a1880000500440c080c1000c18000101c3e00b40c807656808038440c0036450180c01e0030005403801031403010042c41070b000c807241c1100040142d62130780315a0402c074560140c001c0f560309980700702c3c114036440c140003818001d6594900c50910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 654946115 1250 654944865 654944867
    0xc030b0f0613090b24070210020102130306022d0d05090304031208090c1c06060915060f0c080313020315040b0109110c07030c08100905030405041a0307080c01 70
    0x303000081030045075014108045000d81100b14102805145007850300c0e0b8090003a00c3d103940100700340502d9000e034920844201c2c00654407150300410016031049010184c08607003a80103200b120b04171500c01403032466890071511448069403000c20303041d11380c986020226100702540c4c4800050900010764182c0c1d00c410f01c0c203144003903c0002c0c1c009101500100030400001d10b00500d2007024111900b4240456580c1c11982800c00c181a200150070400c0041502000701450715034125a07072043c102000300580740c2020404a440800d02e80080652645081c84903034000c00800070b10b1403680c58814401506541d4140e40c0c1e4100382d4860b41c00c215070258002c110715040c400b607036206103810303480000d6150039220340600050600c569001203640300c400005540c4960b00b112070810b04c0d0b004071001d03152360340340401ca8074032603110303056030f90080c001ea801c0b003000c00340503035000f0581101c021420141410b00700001008030140d00c1341e4019400400300c0d040d440030710a000041981030041e00c0c5401032500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 654947365 1250 654946115 654946129
    0x501030c14061e122d1506070503040b0c03040510030507141303021215090d0206041e05010f0c0315180506010548100b040b040c030b 59
    0x82150800026124554540c40e41c8040e204140e0390039045154800b44005510020710a40030b00104c2c14100302c040020400b070ba924140078801c0c0c8202c200207a03415074040007840e201c003650145c100d40098400c00700d1500e400e030090020741e402201683d03d895130301c5014119540c071a1100b521240c0003c60104030074649043c0102414800b42018001881c013100020400d0341c01711186030f120b40000c0340101001c007115089a01559010300045080c58604030115a03517403200420342a15003014001900d0004c000c240b100c0100c026400a00b80b91303c0ea0b039105a801e01035440300b5082844650415004180c0900410041178030010300020f1100c0b105000030700b9100780f0203100085080e0351204000d080405900000d007200809800220341d00c0303d0340121501d22800c0c400c050300c000c54003c0744100b890300f043e04132030a644040b0144409802682025100d0101c103120803016048411408039440403a004500f50340030040001035071240c0c030000076003154aa89400c1d00060b603a001c0c1c03000036084c419 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 654948615 1250 654947365 654947369
    0x12130c0609060503130c080106091d070e070c050a0210030e1b03120f1218011a0609011d3708250b030109020306090a06050918030c060702010501030c 66
    0x8a001c0d8041030510001900500c409081a0014007899002006022461008901074004840284542e680da400c4440140c01080c0c015001a4000c1450348c04041c400035814046070300c0d03400d0b00d03125a41c60303070303410303104450354407019104e6009402200c1f00684e14a80500001c40709901c000800014420a10f8039100320710640444c40c800400d132a0352240c0d00002c810368005407241203166036014140902149025980b0401c0040e1003503003d0084c80d08103a07409806191969008000a40100403c05003010070008020740040c0100300340ca40951180101c0008403407554004000c021080010864000485070343d404040c95595103600e0401601c5018a00c0d081c251108500040c203200d101c5456a8003011341ca80074102104c034000d04503540b69201001040703480038160f180d69442c00204045e50086410038400d46500340040c1003031031148180e105465005d0040c0c1c1c05641c5000c40c500c00c0500d490152003c512041c016803070030301e104101040c8654940e90020400794594500700001141c26 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 654949865 1250 654948615 654948617
    0xf03032409040b130303020c0a1a0c03040f0209070219110301140c1210030501090b1e04050a06020c2a01140715050a020f1602131a0607030512130c06 66
    0x981c00d00002c81c00c0040c10741d400c0100c03440c0c0c1d07104411440ca4254024801e0405211a501800c4411001c7c4941e9180640440d110f0500d8030602e43d4560a0021041c8001c070760041c10302101650b004003508020f10f046a10013003600480310460400b5810721145a5005001c42d0800540680091503040c01e0046c800003444440f00580399041c1486000d000303000d4082c0a10210356071400140c0d40b00d44d04480080150382004c02004400c03a0307400e000850450807235045140034812440076503125a4a0142441543c0083c040c20392030f840c6030b0783c400184d4045904103c562003017403498a0804041c0c88664804450410111030307070b17040e2800240044400d006401d0201d80240800400301d901400458101201c50100080558031003050100034000e11240c1254204042400c000c0300701910786c07400310740d4000ca42c1c0c02c0d18075921140c6641a07801c00b044840e60300721018100425400c081c0c01a000b041d20a0500c5402c01601e0701d10007800342c0d02120200743c4180000310b10414040c1848850000e0310b01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 654951115 1250 654949865 654949879
    0xd0b0a1508030403210e060a050c010614011e02031c0e0c06030603150402031c181a041404230103140607080c160510270f0803090f030324 61
    0x3558544c000c500400c41d103e1035101c585c0008003e10a88210625901c8032070080c041d5888a1044c2d01c0144030303401508038100c1661a1000200d5404860100c501540c103050796030b030f8400034101140301d140342d1b1510811015840240006030004c0b80090064142c5a9003010000741c560983c03000070305e0901c9400d400e5000e00020010b0043c191004110380e0700c101070002d11120305849070b1021900d4a407100070130210b041606c0425400141e4802c080e84024854070b40300b00c4186407501c0c51590035080c504624a0180c400b004104a4000b00300d80e0b40c0c00c840700007000059400307600703184142088a02000350342c4600c441401482044001c01041030300c101e151000f4080c2c1e181001010f441d03a200902003424405001c60620041b070507a00d8a981c8180d03002040d60303000503c403445034024120454902c042e40720f151180c552402041054400030725042400c110001900781c5590695610140c403c44041c083c40c05014802c0108200031030140546d100030b107485200d0340c1101c00038140c8071001d10780328200b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 654952365 1250 654951115 654951119
    0x9080613030e041a09100b0315030c090c0a0e0a0506070602040501170103050606090411030114060f0402031e040c0b160311010b090106030e0a0605011e0614180d0b0a15080304 77
    0x32000015600c0e1300382520310070316030340381c0120018244005034450500d4420000030802e0350f4003003101c2c944030b101f4160122010340c0074810400540c000100d03580c950460003070000c118102d204071640044494080d00108280d0785440104000d40c1c00540b040c0c4151760005030422903075038040c00204e50b0180b5074061342c2055056988041d12410003401c043e220f8080d031400700f0180074148402c3d201c0d000004000301310203010030080145124084481921864240f1100d00060520303000322440755079802040740800708000e040300b200c2c100180090b40c1c102402280455a00c0042c8000d01e002010401d0044d002c0420346002403001c0e03607442c507074501641441203c040359190880c0c1e40e0f056a6041c140454040c0c1c1040d4402e151100c1c4000281410b401e010002980380710089003002c405140900e40f6070181e8a035201654911a40092001544030811000d41ca22019603d61005235200401d2111200030707039110a07145410903148c42c24500d9662903c1c840f03113010704001000400746600138600340b034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 654953615 1250 654952365 654952391
    0x7110f221401080a050c0f010306090f0504020103111c0e0a020a0902091e0d030e040209040903050702041404050a0305031f09020a120507020a0308090a02092404092109080613030e04 80
    0x100c0140c841b1401105207200000c01c1d40e00a410602c05800d040500f0003500c0e000d102c0a07005403809482c00e03030111b407900000c5038440041008070b400703003009101911a50360f2018088801002488141811402950b580f1001640d400b0230800042c400c601001d41c4404801c0c0800c041301c62110b501c0f80c001007450248a2554880c10066507110340c050401411000c04080820081d08c070f54261264401e1504920604054101006d840c120380240c0e400c03c414070b0724000f45c0d6100802920007800d0381d8000118000082d1280b8011680300c020350046003082e0551400c450741020840e00607040c215004500c12107070303a0744140a415902d05450003031045007041e85003c1e4441402c01000340400090100090b08a8001c0088900040d80034280600746d160005009001d04800100044400c5400750140300302c1c9054001c0041c00d542003d054140c000c0c490b40000c241c402d201a0308000c0c0b00310080e0000fa1003609000f91485428803070b141d01100301d00d0340b80042003000043c1d082ca00c254605400d42d0030503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 654954865 1250 654953615 654953623
    0x7080c16050d030810241b0b010b0d020705010c0c030206100e011404140702011d061b07061419140108032d070f0b06030307110f221401080a05 63
    0x355054208000c1c0c9440307101c48505003011783c3c1c210461002d40c2d2000361490460858107003460041c3c0c1e550701c121502c0000040c42e40b010110710060040c00501e0018845000814010003425801c9034006280814941da040e082d903011000b0700c0c0224076082220800d042d0180700440e404911100c2c161032140c2030889501d003003201030150110442c1c01c0180024a5116940700c03c404070580000c05901f03107840c0d10024041c06a01081e440d900e03180076070b91010345900240d200d0061805050704181d40d82d094421140070380000c90150b41c0c0e80e84580c020b0400d40b50841e000381c0140301142c400300c18000705881d0101952113507415035540421340343c0100814000403094605000c04a4100c2c40505040304003240c0c08040b2465401d0700400002d0004200006070180c0c2504034424540000d05a41d002c0415460f8040c0c071001038044000d41c4903122141c5000301d03407040031803402801c82c8002c0d4500180032080141d0b00203210341d0103a0700d803050304100020081003070040c003044c8020042d1500d1995840e4403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 654956115 1250 654954865 654954889
    0x15050f09190b09030c0115060f0f020a0210051b340b030c1210050117010e04230106080c130e0312040314030406020702120d05090d060b0607080c1605 66
    0x10305003420002c1000c0003c18411104030040100003400400c6020240b501b18003814803c81d4013080910b06001c20007401000d01110001075034015001007003e54082c000241800c1010500b0000c040104000030300800421400d1081c01e000248082141078034074403030900c0e0440011102c0c04401d1481c0c103000804200c0c6105540d10481d2464032138403241007050b01c80c040c3c4510342100b054400708224940016850035001c50b202640d40c03c1e44c100c0038010300d045641081c09102d40e00c0388104001004103441102d28403412034191030000d404c02e4090a0700d401c40752075410080306a080f5224003400703454003200f030642e0303010507040c00c02020b03140480c0c95030b492003490b03800304007228240006003c4c980141000042226150900d41c0d49140c23524040c40254403860049105000e80e1518074948400040c03070f0306030507083d515120302d800c480300200800292019001c4940e079403140700c4031100c0d0705e400f000740c015984075503e201d03118014081700c503050030384e81075004031040000786c0c01300580d039200904090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 654957365 1250 654956115 654956123
    0x603030a110a080301060c1109071b02120709060e01241d030703030c021306061b0203010e0a0f141b011b05060103051b0d0807110a0315050f0919 64
    0x207080000010050900c0c918010103486841c0220001501c0d6400116102e420381c452407440400c00410000c0100245083d40c2c42d07070010300240c40c61504000c00350b03e441000ca00080ca041c000040c07080c0f5907480c2c202241c101d81e501e50b03100c1c13001300404114000b00501412031400240e000d581000307040301c02441c02c13101110030001e601c2c21030595201715804010074900041c3c02c0c2d899058403802c01a00064944030708900462000d0041c4010141611034a015200385a544503141f802561041101c1c440e106401d07030303065595410701081d42204000b00d5805034840d0000314524071403810424094500b07942a002c00d900003100c006201c0035402088607020409013060510b40c1e01c2009402007040404100810a2240b40f0011040c410300051040c4801400c8c452003400c02000402c0c000c030038600c1080108901010b011140014070401040b440c00b51000d440d41c0c4686680c5d841d44890b0f40d404030b07180b0150035074410602c00440ba0381d17407499074000c82403001010746101540031548441c00a64011f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 654958615 1250 654957365 654957377
    0x10201140f0c190503010e070e1e0406091505010905100522030b130c09110702090702030c121c020301051804170d061409070807120b0a120210080603030a 68
    0xc0c0011000801d890043c0c14001504500d5403104a01608641c0207018885144000381e000039000b030b100f00c0301805000c1340949924042d115890104091070445190140c3c020389941b80030882e102184201d00d1090700c44042c2a80640c58030001401c000d20f5904100d02801081c0904140e413038101d021580d94480c035a0810100c0c0202c0700841c40b24101c0ca070001003040031824140104038249090040c2214014610b1045040d51084480200c070418040340341d03a070a0a004003c00351a0961300c0b00e500198074016640340c02101c00d06182080204a160074011001180702e0100214564500328203c80c0d0314021031455041c10f0004201e00d4813607110a07071000e0b008001074100a417440e1484244a10200f070651146440e41d00c14000d040c41d405403401c0c0c0305c0032500388211450124407c0d80a584161135500f26078840500032107903410101c9028900d60340383d0003480c00036215261803000a1480300c03035014a8001c1c0c0d10401500b685402082000c00c00b0120510825650100403600c01c0c130400d003051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 654959865 1250 654958615 654958621
    0xf0d05071e060f11010f020705010203060103050a0605010237030801030506150f0607060b0603100e0a090b1801060b04030b010e130503180a09020c0a0c06020327061620010201140f 79
    0x1405401d05580c070561050020822304104041500a940a58806d0720b05000e1542c1c0d072450f100417103c0c036100703c41c01a40401c803000243c00b540604801d015031000850301c03170308a07140480001030010040c110300085501c0d00401c00c0c404248107480e00160b0383c0c0f81000079010f0820020340300c0f00007481c0d1544244400640b603000c00000f60f1180b00340e02d2014150540303a150000301c500b1016140c0c810101c20480e03c0000401094a503c0760320b18107544540c0185450b101c1c2a89036612000c80b4a500d003840d0b6031080302050800c504009400110710540c11015158102030b8036505524001d01510031404c841109503001680c0841541d00c0310311051401d060003d01c120000307a415080b58070420900b44000b4007c1c20302000451200d02e0640610300301d0150640c3c506c07040342d403403043c004030889007044162008480c51050541d0f004040c0001c105134142040c1107030010098120340300483e40c2c80043d17000700c03101225074038103211803c00900003005104049100401c2c1c00c0e500402000c2540900000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 654961115 1250 654959865 654959897
    0x1203120412052208010c0201020c030d15030507090207230703080a090e100801051f1206020d05090109031b0206040e0601110d020f150c0703030b0f0d05071e060f 71
    0xa440d100000e00c00001d443c2c206102540c00c1e410128054040103501384040300c1c150368014001c82e021a941e400080d0b04d44103507040640010035070354100e02c07003808186a00002103403042180f41d029066852005a584005140030a503100000e5080d8114100007142c21011040100350b0008480d00030b11810f45c0c0f010700b003408440310b0a4681000d100c0d01116400e000c00f4040d503e41c000d00ba948100c00820090711001046094050520101401040340980921500c2105d00308007008034401c0310050709109095400405031601200c0300c4050340e5481030f800003030507405900055181c114062401855400f0340100e03415120301c0c014001e04040420204006902c21910281c1410340e09050b1004000c810400075100c0f440a44096070600c9500c034069a812003044405002d0f0703264802071450028980c1d01074014005031212245c2c8034045525000640d00c55000000020784a94060003070182041c2071454440303490b1000060264100b00d00703109458000c020301070049020705214100b281900c0f5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 654962365 1250 654961115 654961117
    0x1050f0d06051503160503070e061011011b05030907140f010c3e010201060f290d0e011107020a0512120721030b060412021206010303050702120312041205 68
    0x4080303802d440303032200301001600007406100a8450440c251810230780d8440b00100d2500c2e0070b81c0d1035a403245040210510302030007101d0070407104025030004110100c0705005011590804a0b144000c40c1002042101c003950500040000e0802c502a00159140b01d07004100d02c190001c110038140640e11040c1d00600114003440e5136403025240c944607800c0403001042903551a1805074041c0d0b500b00c2151030704150700602074002658054902da032105850901c07880c07403a000501180d140f0b02242c2c0311600301e841003800140b142600801010801485022205084460342e07500d00018140038801c110041e56002984012104220b9101a03c0301c41c0000090400346801c0320766080c0c4e1000128201000005a10040c90a07904075040050880101082d070680b40c03c650001c2c0d21900401c414801520034522414090b40081c01280360300d18503210b1145010020780058010130760105184003103282c090002d1492010f003001950070041c0280c607610210340b0180c00280b140402035039450b1542d1282d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 654963615 1250 654962365 654962401
    0xc09140d11120102221401270b0903070801090f0204110f03150a08060708010303050a27030c0f0f0311011e1e300902030312070801050f0d0605 63
    0x1822100d195001407080c0f4001d51210643c24100d9050b6a200e59582c80b1502d0038900301d4400100303d00303444e4610340c01100c6500b0304030820724801902140c45959540350315242d0026110749201d10b075031400107804040c500840b0350302000c220fa05184120000480b03104001c1190395060313a0110b2100c4411400060f1406040e4211000c104080300f00408000301088031520103000b9145428029101d40f180703600c0b000200c0303040c00414604001000080d220304000d00f0000c1441c90b040d016009a0030791110740601c0b40d0480c04804600384021300c10301412003000300081000c0304640080a243c840d5200e905929440060304401804a0080302e0340d00842a02e91801088140f24800b035039060000f6100385088844104884040400007181030f014003060300300003c9203c20b68058008000e5500d1040f40c00110070302c0840e4032841c1181c01038400308041e000310f40b41c40b86c1c20b90040ca8402d5001f818007005900c064425071803c071600c443c0d82c44420003056041c1d00004007250703590310132000207440042d407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 654964865 1250 654963615 654963619
    0xc090321091c0605010e09060f15060403050a0b060303090109060c0503042409080c010c02091f080303090609070f092f0901080603150f070c06020406030c030c09140d11 74
    0x2607000082e0400c0d00781c28407407018403550f0300f0000b0743d0701c80030142c204407400c0b0b90040c190390040c0d010600001950a04e55030020b0416018020310300480d01082e00780c0c200d6031044800394000914081000035500e4541d5012200b98021400e040c64400003d000700701c284900002d1200691602051100520440d400b4011400700714803c190b08500d140613008407070f20301500140c100722000c19109404264031b400003d05a40b040c80c11030a6808001410001400301c007a02021030b1201140c2100c0305054400074211035016540ba132030b050500d03a0030710000403e008c00e03a8000381828400401c004007254107a903028900040da40603008074212406141030207010362103114181c64040e24400320000c00510341c0aa803040082c0c2c27114014140e40d03540305050b403903044881e4000140900c08100c4000c0e4000744178944110003401540300c0e0f204a0b48250014000644c55031806504160540a0b002c0c40840500d4110341c40b42c5042200d07030345440d10030000d52190240020200901c540082590161800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 654966115 1250 654964865 654964879
    0xb060f0706061517160e061c0e0604030f050a080f151509010201061202092802032a0705120c0c040203091b0901030308043002070306050c09032109 65
    0x103d090f01030401e11080e802048050f0390000012203003203611403014091001506d6540140031710b03004000840c1c0214900782109200c00909501010041c080d40f00007440c52005803d0905003410001d0000280408120901604200000501d94131051a0703602642000c1004215107408070000411419200300b00d9000310010003180b40202904010301440500b40c000f04941980c920384460390030342180c0007940c817072185000104961582c4424540c0d0010042e2501c00c0801c042030041d0480c0c206441c1c4101d00c000300140c510b4081c000c280d8050781c15101610503420880156215aa5441d41142254440c0d90202d01d48000ba1410483d0010700013009200303544902d416244103076074000d03d0f10904407400c4911100200d80c10588240f50503660550b0b140e20565a460311401c415003284610b000030912800c81d0001ca002c50010b0400e180900b41e03014040103461824108142c800c0a49440380000c8104508a096580040d1002120a118503100f00c50034815942e150b09004e2900200d0700501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 654967365 1250 654966115 654966149
    0x8071b051206071814060a02071a09040513050d1112070819090f0b030709030803070c02120d0e010e0a08030408071a03041e0203010608031801030f0b060f070606 71
    0x480c40390f2180b46207a499540c0c00c03034990310640b0307580520b00c20760350602c0502e014003041e820504000c6c820490280102c40145617100e10f20001120380000c03107421050041240c841c9031800c1c0c000c50360441500c1800002d00c0c002601c0d036a81b50180d4541c100305108400d00c4a00c010b580178061120031212101065403114035608111406510201c0e00010414403c0b511303040490007a40c000381030b5160b003480d42c3d034101c0c00c1840012043d8805002c3c01d007482003284000001a242c0f03030055101c1c000550380c04403002001d2041c0301c844409886100c90035044100c0c90300340d890b806102c41d401e021003440d01d61018610b03c0c0125411f0740c1c0580013200140030000f8040307031100300010460111041752120782000c500880030500240820b6070014075207011000c104c86001c00000560108034001400045d0403a52400381c1c81c5103500c00b072010b0321a80d1000c400c0b84500c1d80c00d03206555901602000a0110010720800100c0350702c0f90200c0340803201808208281841110350100020b4002c4640c20781d05c010b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 654968615 1250 654967365 654967399
    0x30203160305060c130b030702070503010f0c0828090602090d03020f1908090d020310060306060906080303040807030f170f010314031206060c0a0203070b0c060c0708071b05 76
    0x90500e010a42d000c0c401c05010a429081600440701d00000302c107141c010a609041401c89070343d001a049000718403030310b00c003c94a55400c1c4115801d000881c0390000d0007607072451025041e039000030440030a0aa254030710799000380303c03410b030821544248800000c0c1710340f1500d0400f00a000740e51035190010110341000080540000c0e4440c40c02c100e070401c4a4003100e412a01e0024411070000003046120144545d600714140269141038061004054843d4800458541401ca840765401a10303030035190001009800304500c00d070000382c90600003079461807409071503200c80f901c82c8034402410450040492140345202d440d0b04204802d58039034007546400c006200205214080c0001e50b01212001444807a1000c00003c50b80d800389416a0f400c0666141007c0019a03040503144c10100d01442c101c070308c0160b5040c07100d00042c0115815842e114410004664646000203041c502c0c245030802c800008125134000f6a91080d07404420101607107e100552440e102c00c0340d114682000100403084612 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 654969865 1250 654968615 654968653
    0x50415090e0312013c1706070809070509160e0a0311040f020a02061b1b030318010603022103120405010f0f110f071a1305010f0203010b03010e04020a030203 69
    0x4481000600d500036601c614050007003d140c203400315100554450000b8614005c0403184580202c03000071006815a50901440012103030329080c01c49412160402c29400c3e007015460b904400104c0041c00a5410140800c0e54680043c060311854204801014a0117220f10901206e8500261000070026602d00c1c2022412864151541c480c50500b80d070143c2003d414400d540d0004090f80c010005916841100040043c500448501074007040000a004007010f4800c1c1c510b58514100460707483c40c000014035001d1003403c224811590400004001507940e01c0d442c0b5141640101c00c095050b58412942480d61090b000038503100703c10001044117000c1d040d44010380c089a034600c184a40340410700d1440881c0d80510800c00c0314a01440325442c0130f00300002030030540348036580d034481e4820100c246071520300007150040b0032080101414001c00c50b007030103a0300100c0d020300c00550655060070102c14050005009102c0a0a04c1900040c1555600c401c407030025a00501940c1c9000841e1100c0010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 654971115 1250 654969865 654969877
    0xa09140307050606190b0c0a0507060c0510020705120318100902041401060f0309020402090406030c08120405060403061e0f0509070f0b121b030c07060609020304030207050415090e03 80
    0x2442c098000044c0c00c50038500070b040252030100c1002104a4240b003c4800c0640241768211103c1c81526161400103108210240140c000343e25090040d495518000e40b0742003403690041d8819005014a500241c1c000403103195034082400c0346501c0c1d540d414900c0810007140d10310068140700e05800e44440a545074400b2803114003d8406010030140c60741960941182881600c00141340200c130080c0d8240719511000b005031004001518003c070900000d01a42c44580040c0c618a035081c0c0c00f0001c1403020801c4140784501400c1d02810700380750100080c030900942c400a0102900c1302d4a40340110860002c2031913200e403a0500b041301c20801040c08000308022102044640300d00040803414400308960101110f100c80c08a82c50544109100e8164040203410490a0318410b60500032101c00c10740a10f22510403001403d03201c2240e410036030300752500d5500895040384100103100100313a0101d44d85046e1081590b001c9801d0b80c02c00410b46162440394006040ca52078141c140382e0180011000b020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 654972365 1250 654971115 654971123
    0xd021311131508071803030f110f06010518090c0d020604090e01090210140433020c21060a0e070b18100801050a031103010b060a05070203151e0a09140307 68
    0x501c43e40e400c1e5080c0e1703c618252088903116400d00c142013000a210300c00a010464041c54880e10309000d1000603480c086848602005030b400103401401780d420010000840a1a81120800c03541040c84141c2e8030b8610030107c1d18061040002c1c540b003551070f11001c5400030101d282003040b1030300717402610500800c1c106104a04c0380b0300201308000403030301c6000d40640e4549a80d400710b02e024039043c8003980490481e9001c91645004610b0039281d03090050f4003669010540e0003a0070032030714500030401c1d40c1545101a01c1000c0500358401f94089000481503804006c0e42c9000543c02110a80c2520301130096009504041c40000e6164850310503070002807103810306482810351905050002c1d20341d40824081c0b260046c4020740100003091807038040101110014000050f81da285c0e00101c1c50a500003c85503003c210b00140754800c6040130060949a60500a41d80071141020052002c030344900003409200300800c5004121207641580c04038550302e5101c40c5490f69a00e840c05040c2d20f0341c000401c00c0e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 654973615 1250 654972365 654972377
    0x71b0f030c0c140307150f051602040606170912070f0c080106080d02010f11070f11030102040e04120305040b0a090c0e0f190c020309060309030d0e06150d0213111315 73
    0x94240e83c1d1015483c1c070a0b000e9140c0c4105441e61f044211402c3d04805030010001c42c004810b03601584403031080b071000e00101c0d071b507660003114003401283c0043c0c400340110f420b96001010344500c1404038800c0d5400241e1040350a484042d450424000940003034000003010f500c0e200d0001a0b00400040e500364007040c640007440040000960107084510120000b0240e0746d0800083c40006d0310541083c0e48248100c440e26240812940402c0c00c9800940149892404070004d000900c1a0001000c458604528040c0071600e031550701e81003c0c0304044c10742c02c90f003912480b241c0304019501c0c0d40080030f01612030403600949000c2c81052103020301603c00d040748005420f1030418203090380c001c20316150540c0c3c00139850100c1401c00d01c44240c0c001052412280070034404500c4540c074034040c0207501c1c1c80d2a0010300c200d043c201004080d41c0c15500750140701e245500038100c0181c071946c20b688080c0b90040b200040c10654403c0045591040800710284d1140340c060214402004280c01000d0480a0781d4038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 654974865 1250 654973615 654973619
    0x10b100504030c050105030c0c01022a010903093b100e1308070c090c0e0f180f060a0302121506060a0203180a0914040b071b0f030c0c140307 62
    0x3a6214407842c080034000c0070b0414818000c41d4018001103803c04000000c04e440e112900c60340908a800600010500b0241110b84480118500301e000140d8201d4000801914200b0358020305904158480c1c2282d0502c40320700c040d0300b501c0358051141490b83c2c2d2140c1220002e81003840c110040d800b121403524540b007450000ca601ca00d08018644103076034488000c5102c58460b00c070030919070030503041111000c021060101e009041350080c81d80c220301070740fa910f0480510800700f040210180b07001c28052401c45060001b080802c9690035008881e00d29035000076141c110100303c0d1007071640c102030340008240b081078803241c000080400301003075a82c43d540820f44805082140038414421036000607802400384601840c0301d80390310310340c1d4240241410001691840140c003902c0c0854005103403000820f0070002808035104810364092001c5c82c0042540c2903040c14141c203c0075031040900040701c1001d00e0070400d0b006501d0344651641081c0041d4840e96546400c404a00d549850180030307004038140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 654976115 1250 654974865 654974867
    0x130305041a070b0c0306090c0d1b12050c0306030c040b030a050a081909051008070c021005040801052d041b090b040b0405040203031b1218030607050a1b080d0e010b10 73
    0x240c0b8010346c030040c01d80c803046c0c5400c585e580d01d0b40c2140529030340d06a500c04082800d00c800040103403400f4074580390a00c4004800c0324901c03c50310b000300300c2c10400d14200f040001e1070790085040b00040b04101c900294217107054002c03034500142c40300d00030301510404c041d00007070140d45009031a02032500314030290484141b29040b520500c082c031800d81c0154071602c0c0800c80714010f4000591240d00340c0760600a1140d1900056407031000b0300c03041d40c042900001e0600001c202802115882946400340c003885000038201c40314409210240d000703100203c0d10110b000c001c84001c030b816030f5242e0155000403460f1500101d070001c006d07503160188118074100d800c4180d41050b001c2c186c8201d8008002d5070510349513400314035420700303401d000c7e82d014040c144c0460040d580842c054a5250031406e9810f00707a80010050524061010303090f0380a103c01800341c0111aa80040001d04804440c0308080e035003001ca00e03180801e80200d6600d0b0803090b040c4100d5980200c415840024078807000c8510007140001024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 654977365 1250 654976115 654976117
    0x801030507090903080a020306060c0105010611070f0b090103020a1101061d0901230618040b0414070b043b150406050603010e0c090d0b06091b03130305041a070b0c 72
    0x40100e0000000501110b4075940a180d0002c27001d0700c010700c0d003880712403640e013122000d0b0480400700340c10301e052950540c800c00c81032010301100000030444504080d039050050160001140c1019000280681c80510506402180340400002070000359180d001c418908001240046404010f03400083d0404d00140280480311a40c10114843c102010b600703c08031600052001350008210400807c2005964190910850084000c2c9445050900e0662404031510a004074503502925007071214101001c00c03201158030070000c0301502000d00c2c1c942e03c0b5902c80c0400c0091a00c004010030310b00f20312545001480b138001e989810306603d40342d108000444005000b01c40e04961b06100502980000514180c0c10809213400181480c0b00e1100041826114800440f1500200d500744401414020b850030b42103009040d110903d46080c8090350000c1c00f0062030a4004150f91946006141c080d100300c03030103000070340b403248505041480c50000e55442090300f01c03406170040e00000c8250382c2e550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 654978615 1250 654977365 654977381
    0x30807031b050703140f0d0222060807030222080a060f060f050405060d06020c03040807060503070531151d0d0213060f0f15020a0203210403060606080103050709 71
    0x30300d074075003003086a8504595040303840044840c2c2d81c50410407080c00d02c900ca405020000c2c080e000142e51105421031501d00b40d102ea41c0902740344250900140219600700c440281e00c0410384c0703001601c50072412801c003007201010b1501c0c0782d11203084901080b600008074800103494003800043c000102c046005030200c41d81c030f110382812003a51040074081850a03810541d04050b00401d80c6070b0a003101e44880081303a0158003460202e5200040401c50748500b070283e0402000705081080c04e51506240c003416030b100701e182082c408039511007451004641006003000302d0501c0c0c2110040c068843340754425043c02e002043e808142020f85906c8000f0201c0c188220107032014005001102c0d0b240e0a000404a41034070f07690541307840d014040b50b190f5015000000a141040d255000680340c4510004070b081c5003a08203046422103283ea1005d604c0004003040c2984d800051549051101403034980580030b113801c000c1440e4200000007800c43e9100007054180d07030155098a02659403441c4440440784c000f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 654979865 1250 654978615 654978617
    0x1005070c0201030b180720100b090702010501050a0b0c0312070807091208123102010e040b0906121f061d2206090f0b04110f06070204020901110703030807031b 70
    0x1780001100c00341f150b0a482041882c04848800562020387c1f45070414540e0f81050900655a0b40e031005030f8030386045950303045240c600081046505010218802c0c501d40c3c041c11258070b100082010054004004568a40e484d442140744a810b1181006000c101c0070344603580003601281c4041464424041c80000d032640c0802028900841c50010302c1c1e0903040200340600c00204030302000381c184580c10102d142001c0000101a02488520006d081e4800e1040010b001d5460321507014a540c9420840581280085030a102803107440800103140001941c01a0b0804480101d03e02050085401030400e4841c90b02010007025260f07049408001e20480b10900b0200180284186080300e494120381901c1c060b8001017070b101d803562140d140280041804a4030039030440e00700014040100142680da100840d0b0460f00034000000260150081c11406032103143d00082048244e801610300e4412461024280c030905681da0802a04003001180c044002c60708203504001e04520502d4400e4441d206 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 654981115 1250 654979865 654979909
    0x60617030f1c060f030b0106120b0321040b0706020405090c0901050706050408070204110a080c0a09050915040903020f010e03071a1f0f1703030105060301171005070c0201030b 77
    0xd03201d10b00382d612500300c1c05402480d501c403004280102410b140c10701660107404940780300d52400310300038506010441a05070841c54000780c10081c0d0303008103141090010000403812206e410002c400110710890b03100d1042450700107441006c00006802034001c40d042240c540106135541c060580d031034840c4c1c0410500240c02005100c00040365544090741180c010130002e41064069400b28044510b49415203865a402080701a01350f64055001c65010003441ea40a041018081d0050100c3c00e0034040d1034881e0000c040024a2440100c600c0d28006100600a2000c410241806034440c07001e020a42515420680e800249030710010880d48510380c81201001e400c0c160000506882902a01218001070301d1840b08604140c07480030007002d80340704880c907480d16160a00d00680c00e00030036000c2e845900144010041c943c0c821041d0b03411501001c4001c4131006604404608286185021300c003a5803904080c0420540d0100d9501d200c40d00c00c2e2000c1000200c0d00040211028441054001d2401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 654982365 1250 654981115 654981127
    0x16030813080301030f030203090607080301080c19061d0402190917070605310f0e010e0a020f04080d020105060f04020304050616230304050607091203052104060617030f 74
    0x41705581c038082103070091040c0d03410450301c400042d00540c42010242d941c04d002000601405005222002410070b0886194005142c405054010034281d889508e05111031540d603400400c080b1390f40c00c007960400501c01c541d22500d010240401d08240c20324000003030041c50011500d007480059070184c03001c0d490000c00d48140f8000080710301f80d00824941c0004104804038594a280003407100c1c808440c0300c40c0490406080c01401f12819400b40d0200d401c0041000c010450500c00c014032030342014a032000036a13600da0700c820082c070501ca140d000404a21411002071403c80d41075002c41d00031030701140c8001680f291001040140e0000303540191042d044034000c12004040521445807450546c24a402803400a01040d0300c070383d10740190010041d80004c200010040c083c8400c0d0307800352190814000c081d04180140d407000d0399075100107091000002d4140045c051601c0101003200c5040f01202c0e86140904c0c1035009089a8031540000c1d5400c0e6007503403d0160080203179a028400041524103080b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 654983615 1250 654982365 654982373
    0x620041404230910112802120d0510121101030b0112150312020109031e120f090c06110a02041806020a20150109020c070503031603081308030103 64
    0x344031100c005001910000c10015096410191071050070460051300e00c00c00340b1081d800546080400326150420108040d4548006084112081c50b14a42040c80612007200c81646000c1e5a08450b41d5041004221803a009426800051045860556000b2550b548001101d90a450f9680041640d03107001c9420f5100d5210b5400285d101005140400403502c0c070104510481d074001245860b01b461241080c02405560182c2038007051580c8020410404248c40c006d02c1c1713504122402c143e102c0b44079501c2e034141e8421003160b000c9100c28203003082400040c50340400140107204080342c8041d000400081c0b40382c040c0800242d070400c504060490f0b00500d508100c01440e0302c0180e14400049403105e20042010f51000e040940d08640f1013003075141030b10882282c0002d048403104102d0303006800510800c070703544100a04503900b03071001584500b4002c07941401c02c400d40c1c0040d50148004105000030b80002c082042c2564001e48490465445003441c440c420024120094810035003000104005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 654984865 1250 654983615 654983621
    0xf0c0d030e04060504020a030f15120305032806050f0d0c0510090e040f210512090c0d030f11030c030f0c070801050114040f050405060411120303040620041404 70
    0x3654010000940c503910341340000d080360042e11084000a44da048140c2d43c0c0003083c420a440281102100702e540e0349441c442260040032202d0040810001101141400091030b529542091544502c40035500700b0a1201d401840603120309032003040007060a41e06420004c048241c4144c100c9000500b00f401d050510254403060780604042046d944000a5400c1c95405440e015511500030526601c2507410108903180740e16003030082c2d030840d01810140c016040011500251004c0c0d282d030030302e0341c0d4030148942001c4503d800c0716000b4104400d420201a84142101c488a00540b101810400c0f0a1641e07580c90191000500c4181e2003003040803952110000644043c00181c81184c180e9625003c110b07080d20020382c054035045205016250491030540101e40d5004021030040109103001d4941c1950346c0006040540559010014100c00e502c449003910021074940085a99904207860a00700502d1908c5560040715045680b40861200b80400c0300c0c12240300098902102c08050100001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 654986115 1250 654984865 654984887
    0x904140a0f0506010801060b16020d03030207060203160201110901091403010e07082b021009020301110a08100906050105040b0a0e0411070303060f4a090f0c0d03 71
    0x2510030008640d00207821604030320390007881040a00159494942c0321800c1d40e0003600008003403602400200d0951440c03c01904984c0c0c0c0444440003110315a040580c007d204908003c0d1a41d40000104480b02c0d40007144201d02e1080c4c1e0b402040fa122401d103841c52140101000390740000d0907220304100b4904a200d414102d040c00500006821024801d51454819950b029460320780058008100030901000740151003107100c4040d9070a40004a4020346810709111400e03092640d6510740c00940d18258804480c00c2200d10060f0f55840108101425450003280c01d05000c00da02c4001181d0b03115180181c500311101070b102d0600303160a101600050b50080c8100c42e04000010000900036510b500a0380640102c01b034010341d075030074503060040c00c4d6411900050740300102c0a0040110442d450317070380c01c002e44101d005010f501c1e09941c901d0b1900c124040c2900000e9044500c1440c1e0105400c46d494014180c810455100b2031844100d10740707940f44403080340d610140200540700424095208040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 654987365 1250 654986115 654986153
    0x1517030f03041406100618030312050403030f24050406030305030402060a121e050a0c120b0a03021915020c0306190905060a02040609050306100506130e0108010f0f0b0904 75
    0x485960350403d200d14140d0f003210f41a00307920a00c601004010741092084220001c4401a420020700b5510050010041d180c0c1c00c0102640c0c40000505151090f4801d038443e004038101800b68840740c52819000c010341300d6040304c0101c0c103030b80c00050900c0d152003040112a85074540a0569503a03400300845c0b600b0489035002407100c412400448084148078075510b0320200640ba20031a40312240d03c40880d84010107040519240111082d4150382145030660541c10118001c103140e498030700401d1213a222588001c1d0000402d00c59592050308610518082d141d00c403800035142000b014040b40d039100d95030a0a50950800d1002c140350385200c01003402130313002191011410b4080c0d0740d211480c0039000c0b100074030402c0d4041001d1102c540e101d0a00c40040c18110002c0c84c1c1401c21403050300c40f1a81b02d1140c0792003420001040c40b910685403220900600541d4101d1416681d58081a40608001c10848841c0303441d00c504240c030740138607100e44103404030050440441a40c0d15581c110301e21054890602d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 654988615 1250 654987365 654987383
    0x6140910090516080703090542070320030106050904060b0a0804020909010e060a020d0b06040b2805160201030f090303060e09060108030f130f091517030f0304 70
    0x80790707810840c007480d4040c1c041c50000c41c482c510110001050b100d000b815100401d820851244086940080c0d51015124041650307a81c2142e0006c103c121309451a9100000d140314102d46600385150074081c3d44501d819860500840c41d0441400b01c524406e8156070040290a20061180600c50b00c0580403083d406000010015110184030009800a40c0d6440004644800300400c42c10540384640c0c000300c0c0740c0e00a210589942c88c00350b0721340300c0091803140400d80c003055420303040031036070010401048040c101c2071b0784a485010a0480d507010b01540d00900b4090078000101d21518205a10001c01c2135840b14105845480d605440c068400800c2c0e04042c1c0304e21188041515503c542800c0d1403094078000340b094a0070310ba607415400002c007411101e07009413004101301c90010040350384c0140c14a261a5170780415010707800601143e500007500404098038089044a1107a01c034000c138030500e06426114a985109902221002f015880c416800500018941148580145411070700c40c8102c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 654989865 1250 654988615 654988619
    0x71509020414011202010e0a0f030b06030a1202070614130b0a0c05010507030f050c070320190f0303050f04051c0512090109031103090a030308060d140705031006140910 74
    0x1030010b2040031307008911640390304040c1204560700002c2c0740010510944842001602c0c0c502528200007891002170840340c40e120005400e80d4092000c040490784c0a9007030000c1c2001200e00079a921154021107003c2026101c15462683e00e0384280c1d034540090b448944080350400c55401d0481e040031402906004c070f0182c070100003c1081c0546031107000103507000106d000d03070140f110081c5c4401600d256203901040142c44082640503540b1640a110040c4100c14075140403400f600d0070404180c003080701c010640500c000c101c98811001040e0780a5a000d10250700d80b140c3d15a60300c601a1002043ea07400080d03030400c01c4144034025554040541050b5041100900c0000c04030340c400c07904d500f29039540e40512401c0680164900e81e5850030b5000450500c1814004110581d0740c44c003025050001d920b000421556a40c0d500a00b80c40d800751a204601424550140d0f50304101c1c06985d200740281c40120ba4080c1d482d10600003150403181450300e071030343c20034203102a0703c03000346c2150502102d078000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 654991115 1250 654989865 654989891
    0x72c011406070204230a1104080601120c03050105090a020f090603250b1803012f1303020d06050406050105030312010b0f1b07091514010f0e120a0c0b0715090204 71
    0x58542e5500f0701301c003550981b50072071204d401c5520303107100c0c0303071500c4010f00c401d01c0038440c0081d0003415240754485102094a982c203042c0060105580000e1503076003007404001d0428804688001c2d418403e80d1049400d4501d4003c02040110441c5c0c4036825078172460098030408215911111844200032040d80f07226202c1c80d41c811030768040714080102e604600306002480c00e003441a034484161a03000d19041e1b81c0d1905084406000c50703002c0b00d420580118881481d107840042031001554000e100415003062481c246025207001c0f10700355442445c140000a02c0c0c1404012181d11261024507004240e007880c0d1603d0b840d13004546141e03c2e00038144000004010340c42d507401c640420f0f0070000c000725840c100c098029603089000e1200b0240c0c0c1c00030100040c884882c0c0030000040c003420700020081700740b9000c5070b854800029071684820800c0a50003a041d0204900329190300424140410b9030f01c03650111002e108070340008240105005440c034075940c031548065107844c40100017140034184105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 654992365 1250 654991115 654991151
    0x1406010e061603080f0901020406093b0411060c10090615030309140f0a1401020a0611120a14040f080405060a0306051014090d020111072c011406070204 67
    0x9403c401042c40034050020414195000d59801440a0001d51501c1c1c2020002002e0340f0080c070841c40440050280400284802c2405072922903400107000b0f0b8034907404104194003001540e00f56843c02143e01187c0340c41c20070700300311004018164010030407105540c00ca00018a29444107070390007680c0d1402c416940b0b0b004810480218000c2e85d07501380716801c0401800445101211942c4180d5232140c0034002615101340307281c211580341c43d840710400ca403000181d040c000100d030000c062034034040690b401d082003000982004500d0035030100503991003c034138600300c490010118100c203600300e00150004010324802100c04c1d1207144114201a541d0020410b0f5401500c074440110741c840c0800e20890902a02e500b06000346032820400460a0800c0240c640c4110820f050040484400c5030081d64001c241220480180e80120b030a295511825002040c007418403003000101250390040810000301d00d924144c4a0b02c8001071031136480441000950b61014038104d81081e00c600340c005462034510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 654993615 1250 654992365 654992407
    0xd0c030203104511040603260f04030b0402030a050d020114160f051b0312010503071a040620011a010801060f120207031403130c091406010e06 63
    0x1480443d0b4200e02c00030710078420100d4102e15106001d02c00c484070107010b22a070034032103145140c03248030921820707401e060741c00d040310360880341d00541029030003c1080126180b2000a1104010b101480c0b400300340c20040c1031042c05000700300b41000b03200c18004105145c140c45d420a2005086506a9180fa079400f410200ba080c000c1c40542d64a998003005802a040e010780c0c465140d400e68941400c10b6540074003081c3c0030241c404100300011a9a94440c0903a510030740b100d021800450ba111403810805030365041090203154000d00400b600054203088180c100c1068800c66a141c42c1000d04210b0222600e50082210390800342041c916507010940038491009815040d8000907161141180050506c40042c0c0c002c3c1d0402c00c80030718602c851907200c07881c0000040d410b4009a91640a41800c40384140c1d0200c90703100100c00042480b035000980c00c00500c2d0144966000c6241c140d48015810448148004a5040010140c0010065031085030600c01d03040c40104020308184068603410740c1d1000c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 654994865 1250 654993615 654993643
    0x305100b1302090612060a21050d030203010f0e040305090406080a0c1403070911070804171b0108070302031308030a06090b06070c06050c01020705031204061d0c0d0c030203 76
    0x5508aa0124106001d041c4040844080c055141c010301d1408a40184520385015590300002e40225500d0368603400b6440c01040040c8188558050f2200e805101e8424503074111110320071900740f6003801e4028003d80b07040310040310340e450009151140e450800c4030005c0045081000130010103072030341d41d203115601c00b030001c070401440341030032620f030407034003925590001e14030364809148180e42c0340d50008420f000e5640204012030003800030224001b09010350400180490700124000c0f4a1035640401c0e2004c0040d00c2e0101c40804001541d06801c0c0200441180d0004040200150111b4080d40046070004602c41c642d01701400c482e1911001c1d50019245d0041d401c1c0c48030008c006034191030103503004100381110316501d0551159240c040b80d094a00c94036081c002c0118496150010030350590360100e800c40c0680e0364400860141e81c0035101c040350222184d81ca01a072481c0503401541007a400515003070010b084e01c1507030740100a904080c4810031079078151603482c01320040e1002d00c4602122602 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 654996115 1250 654994865 654994871
    0x60706021206030604150b0a17010207050601120b0a05060d0c0303120b19030212120c0106030b091506091305010204090b0f100503040209100915150f05091009030510 73
    0x110306400c880407010345694800d030300038818440840d0400c0d4400815581042c0c0005102c9180c03004a07c131039000c0e52140c1e10812484201045c3c0301010340040454900c2041070321190317070301c803c011074065945500140c407c20344000090001c00440d4010358020302d00a0900b0424030407a1743c1c811205040703420450004034132107179545031180d081c0151411645d003100d46184d254a160741018032603515200c064400c0c80007059500d615001440000c410718032005030542e461440069041c06410b0a01c130854440c2202c0001411541e80865035028080108031a4100350b01d5220412400500241515000c42100c1e41c0f8680081e000b4402003008195110001c5000b401c0794007001035260180e11003501483d4000381d0340c910700d5440011258820750480c1c0314900b42e25615201c140110350b07a00603241c0b4601c4c00d40600384d454580c8032001c0445002c00c6001130301d080485d400700c40110303860705c1c0000810341c2072120340b0702441c20710043e0903421490f00d0082001e03a66900c13a185442400a41e202d1440c3c0e07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 654997365 1250 654996115 654996127
    0x525031b060207050604050105120c040e0c04030510020c0c01030c1107030c0e06030c0102121303081602031c0f3c090501050f040e090c03070b2809060c06020906070602 74
    0x50103204400040808880306802c16141c1f8001030000d00c1412201140d0040c44400505d0005004007558040d002d10440c01840d071810806018840d80107000c00c4d141445a2403003122001440d00071901d207041144054001c80c05c5140055014144003c102000c1c0040c140c000781050504100070303c001c601a40750f030617089240001d031100001025108502a41050460341416600010712007554107242405540d50300c00c02c9007e8921a11b5a080141945000581100c040c0ca04015582400f8000c4041c1c5490050b0787c441404554512156107000c0b80101c00004103040c000d0b0f000d40e01580314819241c903003d40241f1b011081000c0003410030341741a41c02d20341290340c60f801544c1c6009030000782801c43c6010500719910815010768803543d03140703000000010301d4501c0140142c0700000000b0f000c490a6907181d02e00b4402580016030004802d090080641c8561103001d41000c01440007504c2e0440381d81d04043c81207406108060041c0c7d9035035020000c0c00f13029244e101c0207155207030003102d0040c0c40328 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 654998615 1250 654997365 654997367
    0x60a06050414010e1b070c03032a0b01120203010b04020406110f010e070522050a020d1107150905030c0a1a070f021e010e0709060519030525031b06 65
    0x910300c5400b00880d0101280180001c00b0020706041e00800005010b04210f408554525024403502c2c0001f00b80e240040f500004140e0800e103150700c29840240800c030809413044210961801d91800070b4240060309004000506501e03001e94085800900040794002000d000710302640c0c00741c2d000c40001b03011600c440d2080791042c00004070310084d010080c004201104022035444001d07001e11489003940480020300e44100c5040d044810305030f214240482c0c5008001c1030b000790002c81c0004140d6040c018101c4048894a003201c0b50135501c000c50b6280042d006440b000140f400395000c40f003510040040d20600c0c001008005000c0717106894001600300c44075082d0b0030703085000d8452001e0045c80400a02610b270040f4140c400c1e5000d510461404228251348980034086600261009008690300440c00d41400c7d04603205607030041e2905006120300e4108000b04000b40d10005e4840c0e00300301c1302d0014147c001e00c85000d12902130035040300d0607a200d0304d40c00101400140080c05401480008200c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 654999865 1250 654998615 654998621
    0xc040506100c060507120f0c030b100804200a0306020d0f18142a03010c0212030a0b0406030c080a05010e010c140c011104030309140f0a2105060a060504 67
    0x402415100201c0407441d848001d030881842d200010304041c4c40e040042c1040c0c0c82504c040c5400b50f2080020301202102c86036501c000c0c281c151801c000282001c18500c094100300f010307100413914a943d00d0401e0f5446850300d1128035007490700004001081e0740b00c1042561106461005180120030060b0744100280308003040300c400c150307105861030900407000e00b03071804c00314680815034001140c3e07404e418030003030314904002e0a0006a412081180c00c40500450030b146445c2c1940d805070020054228183d00980e5035001600c0600c400c07000c00c200092424185411040030418042c4c03011a1130340c0c8a641d0b500c4010b0603604240f120b54400c44c0c680051003000d016942e007118018000700308214510740010100901e028441c0014900003549002999096011001c2d803d08031202039151134032454000c0c188000d9114010543c50340b0b8140a20500d020710a4001c1000d0081ca120021403508003000c040307441510b50021881005c0c00000c000c9401882001d100e00850f2000244407814041000f00f1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 655001115 1250 654999865 654999871
    0x6080109050103021c020102100c030c0e031203070c14010908073509180c0703090602011b1b02031005090f030f030a0905070810050709050d11010305060604090504050c0405 76
    0x3090341003800400250300c99090714040b018183d07034541030440c80c900050740b50000b494010b01c5614079002004604950650211011035080da45202203491640201075039414900b002c070005000c00c001160205005405072007005114002e220384d1103480c4800700382114403150007a40d49840000e03c0400b008107c0840816410510301c2c4140180c240c40e0010318017904031040044d165500080803000c50b610204003c024200c16505201d491a0502d12100030350442c0c0011801709001440120305140180180320a0350040401202049084001120707030020514590000561400c40d1f03802584090010281c40035481002062030f081c4544104c0c54031452000c8410980c0060010b40c09000f49901242c0d00050320500c0400c1104150821504055441d800300c1e0702407044410400c904e04d01c0e504040d12030005521500505980e846c00e10960302003a010040c44c0c005000d141c08003540c06580300503000000500301c00d0406454034465030880d07900795015a1030b540003c0c011102441d00303005a0b64 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 655002365 1250 655001115 655001129
    0x18010602010203010e013305040305060c0d1b020606220c020c01090b0a0c020909120a0c021008040809130b1002030408191505130215090f030d02030703050c030f0c0304060801 77
    0x144c5c00d1249041d082c0c0030503101f00c0740d589036015003041d022018070800665002d180c00c031054518604108001c07071601d80c801d0b0084100d0301d080c08038082d00b09a1403903030020540f402e50050041c940d5148100aa0004540908149000c1e4861003000421041c0b09a900890603900100030315840c200016009002542c00030b040950104030b80c000d03007544800e0403400b40b0782c143d40060258807180ca90380e040091001d0b00381c41d201c90109949042c1ea40c02444180c50034000d90380c145490751040001c4807030000848000c1c1403007104000c1d41d03141d0304001c3e42e10070194580d60000210420410001141c40c0e5000280c0e00050707201140500108a00f84260182011804840380b4003c841c0c3c1c1c0c4404071704c3c0481e4139650f07195965400142c1d004102d0501101e0840d030050060460340c40809030304c9004d4201d2603481d03000d04110085c04805080001d07204640391081c0e002075062100b2070b50111204d42c044082d090040c081805a4040000400090b1140500c070f10701035a111404e00100501410059025507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 655003615 1250 655002365 655002389
    0x20a03090b1f0e1803070f06050606030411061c0606020a06140f04020112021e1c0c1b0302150c071e021003020d0b091014030c1e18010602010203010e01 67
    0x690801041042c2811254610500c0035107589855103100031540902c2840c903d80030001d05001000b07042010035240c0751051400300a9500c5640622145000444006180b02c0d9400c1c001d41d1a40380c544080c2c1000510141d8802260300b506c04503001b614015400350300541e000711715075000c01403c0d00a6094030b0f844042c4443c0c2c14030b44982e00080d585805000a814803446090340510900c9640446000c0d00343d0014250520318102c0360090154840b001e210581401e64040080c6004103024600c5040e880380e07100b911445481c11947c1d66040302e40422000d600c2111803111488103004680f070311910f4404001502c0700070b031f13013405440b48082c41c0c0c0000e1554103104500005030b5078080c82c05207240741d40c5001038441c2d14a0028500406c1c050325019030100b00901001100c005c0c907501142959011112018075502e20302c18075541d1840d02444650042206c1880143c4203094065501d84a00c002d060094413882c4a024100d1100280c0140005075000801401111308450142d8010207150000ea = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 655004865 1250 655003615 655003651
    0x1180b0d0b06180402031237090e16030e01020702090a0c020613051515090411030c0a0e0406050406062408060603090a030809030405130e120909130204020d020a03090b 74
    0x1903207a9802c02c0700c87d0382e054008140d030106c0703040d0103d003a483c034030b400190000030000c1608900400050202c4c40700c00200c100c040410248403000103071740580300e005d1600030701c4c040b0b01c0c0b0107030003400c02c0d4403405445640c24800c88001d03a4400c81c1450140301d102c900061034188410000381000001443c1400300d00010602000040c0c0004100d00034050410b003051a81d2941c903a0080f330301518030040c41c0d0141d02203082c032060003802c81d0f4800b42002d04030100c0304103003c01000e00c24003c82c144208008a81104001800b103849a049141d0081c0304d00e04c00a40c1c00d480b0411120800407446081d0300403240d9480480c002504240502e0300403100b190742c2c0d8203500d40101d00b16030381c0c2e1a40c040142000021404507490407070030010f64020f01402400300c400c400600340050000c1c4600070451115100310050101041c01d10b8040b61071080010b402c9134880e54030600c09100032240207804170b070416402c125141941100744098038582005070341c08110351200381482505d07064003418410743e00b1480d01c0c1e5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 655006115 1250 655004865 655004869
    0x30c060d02090f0f010c1b0905040b0613151a070803070c05070f1a0a1e050c1612080a09120b15030c0a210c0b03011a0a050301180b0d0b06180402 64
    0x121100482c2d0007050b42c00d0074490901042485200b40c0e001c844423a0a007414002041a824002441890166140c41c03006441c1c098900649130b1440071540019602c04041c46000c4900300c11002981140104c1c034500385180e80c40b2861580101c0750300780020f2078000b4101c20850b0038040d4038001c11690b2800d10045060001d1042c560302428030b65000395000040660405001d5400b80820b40700240b007214591030300c0381c005405903109099600060082e017131220858846e0f01c0c40382090741c2020b05003e0011030f4507581c40c0c40c2c42e4012410402805003c8500003008201c803002182024840c1d400700403241802c041d1603040071402c00059100380c000c001d400300fa40d120070140c03804540680204003014208414030031214901420b015045072216000850200303441c038010342c1202c5500c0400c1074a400304490001d0340c2e0007085200d40c0001c004000401500429071200710301805920382c002a283c401d10001510070306c540d01c04a44001060040101d00d2a103901380e901e8100c0c0024011059240c07541c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 655007365 1250 655006115 655006127
    0x60a061d010c02030f060f1905041a071701030302150105180c030703020d0f06030c0803070f0809060c0a03080601080615030615160308040b07050f09010806030c060d02090f0f01 78
    0x400d4504011100d0740600a56500304608034044111030141c90260404d140c1d002c1ca2203030101d0341e503011050700c5804015458500d2003803920541d00481250070b088042d20b58058120400742044040085054114048510782c2c50407034000e610030380040610b1401c0341000800064140d00c0640f040c00143c400a5020514403241c5a0018400010300d0340c1c0d80d501441540280105004c50034400d14024000c103c10f00c42c1e90150094900510071503500a5440c90220b0b42c070310811200810000d03d480c00080000d003844040d1400410040c10b142c1058400280301d490414880700030780024044c5018001a960010491904003000762072541d9107012007141d0200501c000342c440d40c00382941c03030704610020701080e0941e00b032104800700401c001d40241c01c00070021141030b6800d40c0d60710005000b1856046c058422696520105182d0381c0c24000c07401c1c010750303030302c000100784a40500800909405540e0340000030a0902d800420050300e441203001880318004075040b41c81d0041080018406c4542c1e0030030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 655008615 1250 655007365 655007417
    0x604060c1106070c1b0e010f090902030d08070c02151801050f07020607050703060204080f0f0303060108010302010305040c09022b021201030f030315091a0307050a290d05060a06 78
    0x42081300d8000104d140054100000194036405802840350101c2c0b000c03040c5010310b048400c505d041d4070001d40c94580140413a07000765002945030b48040e10125607a800703600d03520f40c4005141011000090203401040c90350101c0d01e1001e030b0500001421420140005407110503411003031900c903052819600040c80e05118108010748103040c045800340810004010100296a1101d400e41d180d0380e58044103603540e5205022030015000e807a03580301c10010004182da2103504140d40341402a4615001034004080107401903604a41041010403100d00c2d5000901a10000742c140651080642008018464880410343c02c501e004005202410001c56072543c10b6907000106000d1494031460242e0080007400c6547c802103101c8080010321401c42c0e40a214500780800c0840c0344060a617040503141d00030340c0103456001e110b8080030b100600d0078980f0348401d610b00c0090340450b82002d240c2c0110541120040d11100e0740c640c2c0801c9800d0818107103d5005051506180305412404105030701c0640e109 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 655009865 1250 655008615 655008617
    0xa0c030f0603081b030f07140f0102070215090d05011b09211101020f010603110406060503061311090303040e0612060c191e020610121a0618090604060c110607 70
    0x203640c150905180178400c8070110a03000301e800f03548580c00d2404100c0702071141091505405101244116208103000b141c1110381e00600e039054110405040d080c264110404c0240c20449003805c420000780244120a030000b060804090201e8072690b0040c51040315421800100120804021180900d42c20044905031300042010410b401600101e2420308100130840349503003000c40000074000d0100041c1495032040c1c0301402a80d440d48001c0d200d621066412540244040e81e400312070f000e10307612030054041c44c94146890414003900291954000d508110b42c000c0c0d4460078082d00d0b180540c004925000c500000c0c0560b8031707041a000500307010f00c1a94942c2d1540c200205503d02d8465403010000a107240c81c65030540614043c029680c007030803281422250014000400c54880c042071032016079500450030703045c66034900785250a0441c060b00c0c0d2500854000d280e690350401300480507114602e08801012640707040e041080580d5801e4404130300b880030b291896840c0e6800462001d41c00261 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 655011115 1250 655009865 655009897
    0x1e080613050a0206070c090506041a0d02030c13060f06031814150403030b040b06180d02130504050a061103061810080d03020a0201061d0f1e0a0c030f060308 69
    0x1541069030406003000b4009500c420300041e19000c00c04540401070a4441d03070340f0100880c0d03403218180801c603040b81c00e00145006440780740c01101d2600301103150400c1d10180645104000040100710140002c240490039507440d0341003480700001c4070124400910b21850240106064200f2200000b203000b1030140103c44510080f42180004101c80c46a01101c0304462195240c2420014001e00449d010184610b0034140064070340c3c9001d4080d0784003240200303040c2c0160b404410030080311b080005000c03a040340c0f1031440b001e500007551150a11481c016800b50110140500c1d00b5000c5418251144102c00014010711080b615600300d204044008040c0004040c0c5076118a0012900f065004000714410001200b20903607254015050217811500240212902e800c40e840c0803082482e51030704001d592000203042c03071403141201a0802c003c0c86031102e09100551800d140901c08661040120340c0352255050201d500d880b8203140070384903600400c60141195a600100e1242e1410f4050140c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 655012365 1250 655011115 655011151
    0x110303180111071a16051f150302090c1305060403030203190801081e0c191a040e0601030b0607150221060906121e0c0108012103030207060e03030703061e0806 70
    0x5e07a082104001c160000121402c0b60000104821841100d1504034161030500c40f0081c6949080500142030325802081081345640c1c9803100085508003908410400c01c3c80e25000800307464803c001c2003c0c40c0030350701459940c4a40c004803006c820a40d03000b1010400e10034010030042c04042103030200c01c0b028040e02103141201000107171405140d042007992048004000000c03120000101c0d00445002444101101c1c0310551090301c503010303a03c138480201d803140700081d00561103507100c2100700000601030b41c1081c1490304c1ea003017040c030700034002c0c600f46600042e958041e420304243d030b51541e14045490013080ca480008a042d2400c007912040c00b0300070017a0005080703407042c80002800061102c1c00240c41a00c9140c2d0759445454841c2640800c008a0011540306450320001c0c0d0741e00444690401180080d0b40c044000b58080c0d0401c0da880ca40d81e500220490b0010710007103000e298181e401142a42c20301d00c0310881c403001402e40100e142d414550411039000e000c40c0c410751010741e03410170019400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 655013615 1250 655012365 655012387
    0x210021303140d080903070b1308070c060302090108010b04150e010915020102071506060f0c0203120c0f07060315030204020d0609020f03070f02070b070f110303180111071a 76
    0x284007070300700a20a0740d072000104181d035000039100c6400205565911107944407800b500d6117070310500d44090314a05281c4009030046551030388200c0c4003403080500307515007050b0381c0b6016424103440d00904000303900012807070705c2581e01c012140d000d0a01956140c0c506803500031035000e420b0b01d94134402c007130002410104403075a009003407804c000c003419551300c050482c2400c0000d000f94031458003129102d40b91410342c0300705400c62160005031445034589070400c2c1519801640c000021100c126894854080d5145034611944040c042040c0100c000700a0307240c81002d601c0c10000f00d07811402c00c00d841c0c0314200c010007171907590000407a50191001603840811041800103840c164100d1603035a40002900e00c840207075200214801c214990b903060521844000480e00c403481c074490301c040c228051100390007040100c18001e004603c180c0320100b03500a28404a41142c1080e5108142d88459202181c5103580002030448020a4a40604549130034400c4000c07080d003451425089031940412090004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 655014865 1250 655013615 655013647
    0xc0501080f01031b08070f0504141006120b100305090f011505010f0c080f0a08090a0c0b0901020c030601060e011815050702120105040f150903080c0d09140a03030605010f021002 78
    0x84c5c0500030540c0c8182c1d13220402e8000d1400c441c070405028500d024411031047e05501c042d80e01810001c1c1c006001203107054411204010416140c40100f6590340d55140c0660311481d180c10803003065203020600d0b1811100050820302040395a11043e41000180181c0490303202e00d2a094071800d01300f22030385c0810703182c041f94140001d503c0200401c1c800140c0e5200c065500004c0c00c1c000c55030b42ea9040b51603803005849925414860f10007800700d50101428802d0280384005014030b4107040c41260042e800000010740b802c00280e0081012440c1b04d40340d41c3d200d50b400700111700110303142110504083d1606c401c031442240890014030801c9004201d00303045658440200000000c503000a011034101380c14128114480e44000700c659014502c0c0181c1002a540181c2600980544603014a6651040803d910754091080030b81016a15a00080002c0030620004070704001d400051030425103525001c0c0c02c44d42c8a402c502e050142c00b04240c1c44031640010108107044000e500580ca03184e400d0395a0b444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 655016115 1250 655014865 655014869
    0x3040b01060807140424090e010513020903010207060605211c02030c0601061e111f0e071202090a050105030604061109090901090303053607091401030c0501080f01031b 74
    0x5200b600081c00503106c10800040250502880382040080b003980a094681400e58400d03140d1040c01c08004124a10380100420244100b414000d8030f0540c9070400242242c0c4904421136000d50f8480c02448981070030b00011002c60110032000442042c01c000959946070390241c20440700c3c031b034143c20001c02c2e4824810b5403105c03c4a8070885106584410b0090711460200f00c406c518030302d4807000e01c089180308110404411140e84080d1100c0302c81910103895401c0c2819130582c0054849132103190311001003280800401c0d01213140d10301614644100452130a000d482c411507141071000500060350301045842d0440e84c040740020780c080700305060801070b0207407030391450b0b01c4203400c400c00032046810b4101c8151944281d400708020354500c10a8a0304800c440d00625400010365401003182d0803168144070340a100400b103410307141e9900008415924806007240900c021000104100648071003c01d014010900700501645840e0890800134101480b020b00500c02014103240760702c58502480e00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 655017365 1250 655016115 655016147
    0x1b010509121606110931020a0807032a1713030509060d23160f02061611010f0b210c0f010e090a020c120403020f012a0506060a0b03040b01060807 64
    0x100d061188a003651401e01d00c07101b204201d03003644007480d01c10416208035621904180c4407910340340c6070342c0b508800a052401900d48100020304030b40c0d200302c150200e030324140380c0702d980d07400c02d0345c07000400304801094090201031042c0046640c3c0c0000a40060544003840010b0307850a86440080c032034400a41541440c0380d00510010084030141c40e000c0e0703403280c0300f290319182c14401340104440844030000e4807600c190068025601144034101402c035a130000403514a0544442c000102806013120401c045d110b000d0f51380c4600440080c14100a441d80e2070114030111080d1650125007147c980300c0030a10f081c0310b4a030ba04800b4030140c0c090140701130111006481c02d0810b01c0c1c51100480290310451003042e16104025020382d0b40c00c040822039068a5016140d050a140c0c3d2400548908002054070200e182c041c903407508000100c00d410070070300c034042c6004160f242460414041020a0b6030030000400e4400c20410012070f07007071400141103e0305894078001070340c2c404008036031300342e40959109 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 655018615 1250 655017365 655017379
    0x60c12020c0c042715061e0f050307060f0c06021903090203070519031b210b0a09081207030e03070320060402150f1b0105091216061109 60
    0x2101c5403400a00c229166400381c40c10002c0c0d0800c0d20140000d01115000300610003400c00b5007100190010844518042c1c499401003400340c0c0360503d0400400c400380c80001d01820204d0100100e50783e550303803d00240f40542c06801e5450605400819060281070700800344000010b94204000403035044a88845031413074010ba003c401000001c000d0904180706130310a2090640214407441d010705007040300c60140c540c0d40c0c134035843c542c0d50100c40140e0351203040c911001303044001910561248030b040a84400c00c0310715a88002850030103107110016100800e0145000c00b000c00207215002100d1030b40442400700038940e0707209075044001c2c01c20b039802c0786501d0101043c80802c040d0004e01850050719481f081c0380d01450024a00c1e0b0ba03811040710040d6100d81030743d2056012094480003042d11003a0411031514100c01c007404420752407002540f400300e40e0b640b001000102a018000d91840c0325004100078a2b1200c51605040d4030307219048080c00f299500d21071988440c40404c00c0b200b200d40058540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 655019865 1250 655018615 655018627
    0x711070e04060c180807062a0b0708070503010b032a161502030402031e0703120503011706070f051303060e07170607200c03061906080708030403060c1202 68
    0x1100c040c1940f94a0750740801c0c001080b04444040803a06402640d0117407006004003841d010b07003191140043d8460001200f00da030001c0710034002407603000d0707041e90007141c81c0c51a0382018903005015074801801401000301c00d100600c508d181e4002201c0e0404882e10710460124490301140d04020180460251000400640e21807604610307050303111083d009884920f02280c14018a000342e1008450003503054100d40c15000f01d4903091200b20102030380781c0f400c49500d00e85039507a245424855100110115070040010402e60b8200c0e09030807541e00c502000b8200d0b43c10401c0001c0d010209905803d02445000b080e114003600c02140d5100065030000420f10000850907512504d4908a0281d040d006c0c0050001400107403000410740d00600055864a00ea05020581070b2100020401408003a0003425040300995400708030b01030040e261140d0000d0750352781403060709085a10a9204c507500341c015420030000040003009403021607070014008552085004012510000c14210b61100c440c408580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 655021115 1250 655019865 655019873
    0x70302151e270105011514130b030a1d070b030c090d0f060e0303011809080f0d0c02010c0c020a090c02031606090c091a0d03050f04030f12090305060711070e04 70
    0x1d640c1c009144080d82c0003003002d0200d0141c00d8500900038065000300a001804410703204014503242d6030100c002c05420144e000303e25070f400c01c426900014580c1030210a101e5101020701c03550f04c1103050081101150701340f40c4805501c900040c480c21407030507004400685071010100840301c40b0f200060507400052004d00d00311030114114801510751078a0003005505903a00001180e041e50308a00005803010301000b8244040c11820313900710b502000602031a0b012080d000b0280088101c07144004c681c0c1080a04003d0856242c900301d0001c0010307030002c00e400740e184d056500c0e06640003d500400c0070115848203a00d1b5115014118a00c004031513000740c18844254410541c0510824600006550702ca00784410303144020903540000500c40007032a06031a02c060100c000620a081c002c1c100182111682c0c0d058000768010b50345500743d081d0790401c1181000c41403a2060403405c02000b05800c40c2c446d10742d200c600824860a12014000c4060880b404028030030040c0380306000078000b89824a8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 655022365 1250 655021115 655021141
    0x6060507050708070602031603021228090b090103020315030616120204051c020114031e0c0a09030209040c090219030506010e010e0409080d02070c030b0c070302151e 73
    0x10041c1c07000d004200d804103d240c00424018116095603000b1410007074180203002c0c40c0300c001c0b0b8044080d44910a14840c44c000c006025000007440d001d0300c0e900071540c82c041c003001e503a20b00010344100512030f8018481446100161044900c0a1a0040c0c07660380b08007201690b40c40445a05901d0321a80e0300b04070503001198985da0b5039024660743c11004141900021050380514065141c2c8519825414602180307070000d01e010540c014540354030140821034801b41c5642c001d461580d0283e11500800c10140b00189940e900807000c11011881e2440080b8028209170903800020700c00c00c1158041410b004241c1000405032100300011581c440700c0b104c0064103023030020790203000f090400c400102c103503005001d40000c10340180c40b00e0b01d44a0303542081000418102a0460380c10405001a41401100c0c0c400b90040e10b00c502082d00c41281182040300c0074078130003488006103a03001c000b50f00c0000d81c08502c1c1490449483c050351455160b091b0390085100914440d50199000b182c1045103040c0895 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 655023615 1250 655022365 655022377
    0xd05011b03060305070303081e07020102040503070e010b070f03020703320d170a0603140307050c0d0c120807061401170a030212090411070507030b1e0601110c0301060605 75
    0x10540da44920800103050701038070440d00c4058015040180c0410100c7e011740549540b01d1034680300800c22030004141481070590542e81c050040c0c3d80810140103901f81002400c0c081d00200c411000c00e50326091000d01380340b050048c020b01000c00320b500d04082500811001d405160b002e09000510312040c64000c0741c81a507821419410000054207210400010504800c41440c0756170f60360a1540d22150042442c0019100c05060f03695910000b02042401c50704020540c0c0a10265940f03200344d040213440c0040040d043d80c81200c00b0746041c000507411a0b810001c0b034800b00340c00c004280503824a54020700581c48003a0000d8140082c40498500a030b6a06050342c01510b50000001754801805075180704655005003d640001004007020503000d01414481b20018000301d0010012114908030740c0000302d013100d040d805020b060080040312070045c2e81c01410400c840c41e018039007400700302c074080300a06a14180075600181c9814038409201990600324003034021b1125940e1501f00030440d5000c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 655024865 1250 655023615 655023641
    0x509130e010c0f0c200310020c10051003030c0c05060403060b090702030a0504050d290f091f0b130c0f020c1807050318070603091209180e010b0d0501 66
    0x401c00840005014681c40000b4002e1641d4181941300f1a82c0d5003c20312185a00d1924191705110065000d60b9041102c0c0d41c0b213005480d80540c03039603419280e680c9040d070f08004040c4007900344010030581c810640f65510841c0d42519020020900d0350400c4d026a800c941c02103500040002408000d104490b084000c81c040d05844141c40c80c1d440c0070003241c5130b001e400c10b030300002081044100400e240c003008900020b0b003d0051042c8000901c1c43d1b812800281c0c180e80a08803a5007020403003107807200c0701c00d0355200e00c0c85006480c0d800c80c203018080e8450024110804005ea40740c14030340440c2c582400003980c0e00c41e07545082100307000c06017001d095280500031050041c4206e081d0510981003468513401c111311200c1e12400d080c0c40d0300c4010f903550381000b48000551941e10b286c140311000100400701c0142215180041c1400c41400c180490024515045080c031240c41d004100742400017501503848031401100007035010100c450300340036084103c8815884038800ca100c905002040d8400e40c3c101e400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 655026115 1250 655024865 655024871
    0x30b0d08090f040606050d0f06050909010504030906090602060a110c0f060a0f0905060c0c0f07030606060905101e05040806041a0127090309120c0501030f1e0902010509130e01 77
    0x26a08000640710280140390008134103006c80c055071f0640d80c00c1007140b25911040031420366241c00201d071240b642115009a2a074581045c04145038110840001a145510708030381c00c0c034244640659580350143c00e40c600c8960300c1c1800c9030400c52400545410250910544901c0301808500650b980c2041e07461184192400c030280f43d1422a521440e0203841d4800044c0026a03509000b45126801801045000d40251020041101e00a1010300c0c0698460103002070b0031401d02d40c0c01000c2000940002d03010b01c2c660210540b003550000e00895120800b040000c03550103aa06040310781d409980e000121510501c0b041c0004c0020552010102206c12034080705903a0342c46074125510315028111880000c0152001244140310b6000894031034001d040c106041d50780d403001d560b0b0090080f4030590f102c01c0e66107818011586d05024910110728144802c0c40112100c2150010031441d912100c0050380c0d079a81900116400348080c0e801e110701c0105490022140e00b03686a01900351042c0448981d40f0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 655027365 1250 655026115 655026139
    0x30e19030e0a03020d0b040c1e09050a05130b1005130b040e01021608030604060308030f0603060a0b0102070509060d1b06020c0103020f0a0518030102030118060e16050703030b0d0809 80
    0xc101c660801280e40007043c50501c0780590300c500e4000c0c40c0c058001d8a0919016401207080b82020050100300003275110454040c80c5042d0b458012614042c007800d003840d003424107201c0242e50740c54a10180c150844840b0400c0d0b00c074020f44e101e007150a80d2100e5000341c0f19080380003403a07034668403841c07040c04242c6051200c5480c01c103c0500300c0c800da000e0307608103002c0100c88002042994000e941d21240203400040c5107a200d03128040c468004807640d01780e0780e1031b001c10401d050409103c90b642042603520107110090000002079103408a0303001e40347c040c070801000640d455803100107803c1d001d80c1180706400d03807000701c0d030b0b201030448164011000503100d5654284030b10f5209201f22041081c1c0f01441500f00141a80220788035441101c1c0c002c2110030002c07025801e59001c0c07009500070030490b2103101d1038031000c0c10058161000e0303600903138500c4c10072002c114090800c01803e07850b084441c6042581c075281481c098008101e90380e0400c0d0001c221000150400c10050010050a50110382c07a040c466 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 655028615 1250 655027365 655027369
    0x20c010807140d1418300309030f120402041a090a020708070204090308040b090a08030c1c06081e01050405030a0804080d0c09030303110a09090e210306150a140307030e19030e 77
    0x6641c40e01c49800603400c104a486c81c8442c40020b141c1120b1103100385c0303240100d031020451240d0080e07a0355901e10440b800520045240c02d21074100c024013107290425070002441c000841174031006000004036a00050113104100404040343c40540d8010403c1082d05040c1c280103004002c01ca9007143e51900c00c4000c00c1e141c54000441d5103015902c01405450741d0b450080003130300c0350007450250300741c8213411042d61848640d900940303003c1d0070400024140780700d0112540703078560485039079400540d00d89420f02002c1a03010044a002110b80d013002d4486854034035000c1c00c03d02c1030034050f0f50201c1ca04060301011a500078285005c07a030003942e06018610007084050000c1c815100144041041e0080c10040b00035660403c0d00c10003004019a10340302200045c0e20f0075142d010684003213803000041041900c5c50f00d00301301c0c0311115424100c07a00380441090050441404801d00c490180804000500c541c1d00c0f0390407982c52040b600040c1e07490344482c0703c414154480042e80490106052a80c0c845080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 655029865 1250 655028615 655028653
    0xc0a0b0c07020f0d05210409051e06040b09060f0a0302060c03040e160c0b070201020415030506040f0605030703110f060a120b10020d031d1903020c010807140d1418 72
    0x6160414050641191103c4c595400c040342c01c070010202c007a0a002c00a50714541c0c0c41164455110342001c6603840c2b94481d146e03048604001d199a20461500701c4007845031b04c1c1d82d2501580110182e40c0c1540441000d0000f403402825a4070095007d480083c1c030003c0c4080c0440607108039000141802aa0f440f521088070090700805000400184200c000002085070298002d40108990000614058440c0100010f40e040ba8803e203010076241d1003481028201131103980d110310000001042481d040500007510b032138407880007403d80d01c42000560000d03590305203e0901e500c00100f03030590b10140d03800050420807081261083e046e1628620074071608045005660405090b4040c2010344d44944d400d03001048441210130164070800c0d01000c2c04e07501000402000e82c90b10b420f0310300c82d841c1454028540b0010030421030422114200f8011199009007160081b8406809440c0d26481c07040a80c03002062001d00042103811004c0034414010241011030b040a04e03140180c030301c00440e04040c0051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 655031115 1250 655029865 655029889
    0x618030306091406062b1a030106060813060f020a090509130809190e0f090607020f07031514012916020603100305060f1005100906050c0a0b0c07020f 66
    0x100f20880c0002a603075103005c100030480d28961046a402402a003611807090421003000c1100203903585400318810041c41c010b444051804600901504d41401c000400c2c0c020040c101c101c401c800aa1018200151600000100001d00100315118902004000e001744924410329000300c04034004140300c1961880d510b420070340c004820525005400c81405501094405807203001810032001050320b00d9080f071603c1c01441225102ca241e8100034020604056010b4122020b5600010144181c004003040c03e00442e074001002c0111600c4079040c3da409011081c59008402c42c1c480b001152700d01c600c1e80f408080c50b00016540c62100754403400601d1300d00c615603244141810711015900103241801c01940d209041b460100301c080c1d501e03a642d601d460416203041c19040310007000c1100554800b661500100411100c0303241040100401034130000060040d81d040003400240070001100c00c00418000c2c070741c04060340743c1d646000041310b0859048103000320f01c0ba00d920701b1401860b103012110303000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 655032365 1250 655031115 655031141
    0xc0f02030702010f140409060e060f010504150e01050d0203070c11060a1403220f110d080910050903030c03180102060124020c1003023a1107061803030609 68
    0x3412070900c0065655144080241c0d4101204020101c1c01001c1f81c090440240381c48110f110301400c085080003008121105503074100402070004100b0021a0840c0b19002d0225091004054441c0c0d40121041e00c51400c031298064000403d0050a9500c118050580e074013440c3c145805211940070410148980070b070346000203018070041e41c2d00041d5080255000795078040d208105503050710562004042c040340c19901540541c5410051060702da1452540c26011104604881c041d40d8403007035a0700802c04424061091940b4610000380140201d84035040004c048039218060703203048591b6684840c80c0442c1840850a69070402d5000142c86410b0340c8034030303800181e21110304003903e4070801c80092680842c0b00d00c00404010303440e00d40c1c2c03c120301c64282e0340159685d02c0300c9403e410618406500f0610284107503107441c1890b500042c1e60034003140c4e500d2001c10990000c0745030034440d018851001c2e001e6480d00f0b11410040e541e81000c0c0914521980f4103101303855540201328121a10202405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 655033615 1250 655032365 655032377
    0x18060e030c061c0f0b0a081f02041206020a170c0901200327060d090b060904081626031006080c0a03050601180f0801110310030620030a0c0f0203070201 67
    0x1d41c20301da954100d840c1c4d00d9000e00c0002200c40c0782d440081c000c51442d904ca154103810078090502c2a6030151712502680c034540400354641440e00070121070700e404510010b8105039010070166103041c440c0015881603101083c240c1c8003030401070180d660651142c0306450201c4e192801518160f190005020043c0c0d0010b8003442c1030098003205001c40f070002a800303503072841c403d55409045c0e0340c642c4c01030900c000c141e13200001c0040181c075100c15001c20107000141304007000002c01c80042c01c61000c840c80d00c42c0c400c0f64081c800c0e03014501041d0b80c111001c0802d4410083c6100b1402c100412006140301310f0002905800069803440240c0e0861400d4a1003e0021000c210101403640640c01440c0c014006140281c03401c6008511810b245080790801e001014101c10100000c2500740070725100342050789452451030405409140918965210040c000e58488100d1400c1407961214040c1521f408009542c8d2840d108080f040240f80e01002c0344040384541e02e00100c858400020f4694082c6d040c6c5800b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 655034865 1250 655033615 655033657
    0x110a05060114060d0e0106140609030a03050f070812041b0303091e0909031706010e0901030b0601020102040b030f01091505031510050301240b0c15060118060e030c06 73
    0x100c2c030400c580a0500c2d410000070414650801060f1050300c030303034090000002544034240090383d4211840e5003481031040c1c205011060803542c01142c508002545414143d540d05000f0040340c02c14010800050101540480c0c0e252901e0425440c59201c0c1d031242c140c403905034944030034210700652071b404050001040c498043c04284900004031040b03000e542c0c16800d08603a290494429510029002c800041080382c0c1c030b000e00b4820400c8150415400d00340782040d04210000714403640014032000c0c2c0b52004181c0072410690003035040320003a001c20020360f60350740740503a4141a04030082c41625221854140e9140881a9002200c01903c800401904100c41070030400120b4050140256079044000400060f0640c1c00340304c0c0b00078080042a1000700901c0c5000e1642451002d648502c0740d80038200080c4c40c0d11a004601080d0039420107007075600c10348035240100c41e10b0740421001e0f0700308146490003055103908045500030f2041c04400b00c2d40c00d4080e2000f0701415004071400d04100100e400e04c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 655035971 1106 655034865 655034879
    0x90d0215070e06070c030b042a050f0409030e061303030809030306011707230405120a02130b01050708121f0803031519030b07110a050601 61
    0x303201481c6000840601040c0300c000d0040d2240703c00003190310030040455054000b03160450f0f03004555280619258070345c0580b801c98125489240215061001510074407032040d141f01505038504004d4501c20302015190b40c020885c14000058500c0180b6116000644605803403024441c9a043c90b6040c05080c00b8009440d00706283c208000b004505d03604000c088010010300e09810301c29030784118080313071460b5402c401d0210050f000c02c000800c02d11400058815100121792240d1100e00c1d05070210382c2c030203a07800005d4011f4132074052410245000c0d4030010101d04181000c600d0300606544c0c8842541c080010b4050741e400d0390703041c00609031151500359070752140348140d8001107091039289a07072400300600241d5444402c82650000d5101c480c0a5158085105006040c41d40c980c0307804000300f2001c8800800185d04020204180300d40090910101e030340081c041c1041e6424200 = true := by decide +kernel

theorem cover : BRFrame.Cov 654856115 655035971 := by
  have h0 := BRFrame.cov_init 654856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 654856115 ≤ n) (h2 : n < 655035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
