-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4524
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:53:57.321044+00:00
-- url     : https://prove2.me/submissions/a4149013-2ee4-4335-ba4b-71a6703ac971

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 813489208 ≤ n < 813669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 813490458 1250 813489208 813489223
    0xa021b04141509090f0a030302030405191a01081b090a0605060c0d031d0c09090312010b0c060a090b0c0702010c080a170718030809190f05010e040b0603013005 70
    0x854124a06440e242c8210340c40d00c4c028030080d04298411b807030000c0002d0090f0043c42d4050f0061090310603a03070f2005203044015401c850700f100c5158191580901c205440c1d45c400b4090440e84d4001e0004021700c0c6071110a102c4001080d510480c0f10200040102c0c080340c0006025050280c00d140d1140b52a0b065240d40d1a000550703800072a0803c41300718007074022142110308600c4058001e221024800c01400005d081c041c00345642e50204000002d0b80741c01a03c0040c2c020084525642d0350780b070ba80e04819081c20000340c10b6100310342c1021018004500c1c034460003500410654004d5613602100c3c8010786108080d41300003003401c0000301e80c602c0010b0300b012007540398400d004556078041d940c00c00101d641005400320a6410101e02d030080c03004c40c00d42400383c00b00260240540c1000b1801d100c41304c20f031500a50100c0c0d01c14114000602195030b02400440415205541c280154480140050407500050250300d074440074080c50b03c1134104281c0c3d00c4d2031907400c1c8001d050090320a613051940e1036541 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 813491708 1250 813490458 813490501
    0x82b0219020109150518010504080304031103090102060a05070e0a09060608100b030a1109130509251208071a100b030105090708041407060c060c050a021b0414 70
    0xe030034040311062070043c011207003410760110b0300341c84414222403104000c0a0241031181c03803801604844c0030f420300921920340680d0080d801c05442c1d1a043c03500400280507200151007a410600100c0d804d030340c000a0583e00420a13000101d12076403a03102c04c032528881d1080c05540040700940c00503182d20b559006c0d00903201181d031494190303610141e05404699107071052010b55502000041d5603143e6590080c1441d140340741d082b07031a060062002070211308054001142031079a0318103112102c0401c112001100c1d84203000300300f407003602c001d415410610030711800748000300610424042200800446070742582c0911081791195460140c614100030403201c020511041201c0490280b44450540341215030040801c250f83c1da03811021940502c0107801110070060b25105041c4540b0140800c00151030035aa484008800d541003a205a4503404443c0c014407000308000200c985e404207840c01030020b111942d6800324840b071302280050031b0803400b86409180c0c280038440d031241c031502218007444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 813492958 1250 813491708 813491737
    0x12102070501202b054201111006030507060206070e0a0915230906090402010c0807050715111e0303180705031e100b06030103082b02 59
    0x3c2c14001099504010b4003501e40401c0d400384629441419100106000c0c07141401c000b1100480c81000c240a90300e00380e40441c801008040d0096030902032642c8000610b19040c000d1043c0f019003541044580d40a20301641005801189510b00e4441041501c156030002442044140e6403410441d403201140c3c05854010700074080400c0c00c0a01c18981080810801004009400c2c508200d0303030020807540d4900258100381a500013111084603168100ca1400da4058102e051401d504118000d04014030641c030070410203041c08050b036072000040c80d829a000504a03030f640d0041c2403142c070b00100c81e400b4007030301c078035842c000e50007a50701c04d0b00c4c1c49100404104446844603040c60140107440941d5840180c0d60041c00051107401442a1003d00ca400c4401951031054032403011a0811008904950907007a1007000900810410400e40400c0b5800e0482001104400f00005007184818880a454180701141061194406001c08407840100304403c4d81150030140e2501b01170f401c0820280c840c507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 813494208 1250 813492958 813492971
    0xc050111031e03070c050714030705040504050a020d05100203042141070503040e010b0c0d03391e0503011203020f0a0308040c0b04061706012102070501 67
    0x54000241d488880c1507000248450b10600c20aa107582c00003401d1000b00042d01444101203842803081802410303031256450761080101040c10f243c00041e0780810b002c2c80c9000204004100c0100c0c50f081c140394121280981c00c26503043c05450200c21182070808140b000040c8020411440001d81045410380b59010340090b04000c25a1030011004a1102490060140104090705d038904030200074101c2c01e4207210000c008000007480e4011000c126400c0e03000260070702000303540005850041c5441c0b45900c3c6094100d07001c0c03a4507040d001c8403241c103150f114a81d2442c205414a83e0100448d01c003174260b41200703104017400051044108088006c200031840104010002c1071820580a60544800d441c503460035104000c4c08100e0901034085014903019424415001e002c1122024000d0352200c2e03880c10b06040607641d2031101d91080c0700c0c5a00801c81000203d0700208003240503140c80030201d1030b0f40e40b1880180c6580803402c21010b41002d415403a0807040346036901910715103002c1d00013003040d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 813495458 1250 813494208 813494237
    0x803090309130b13090c09021305150f0d020d02070b15120d0e12070b03090601030c0905010f050609040e01022208070302061209151003020103180213021b03070c0501 73
    0x21079046030640da4001303455a110b5110007029800c60240c02d841480100300907035031849264100d8204202d401c1705804100001c010700e2411544400c41c0d840009480351600f200342d11240d41600c28a000c0486054001c03c0d0354140049035416074100075000b1903440d10030315000503080f40c0c0740c03070044070345104110003040f0100768140090380c10112089500d8803050701c190082004108049101e20301e00343e10801d040818607200d6032026600032101c0c507000f40025419860032145080a98200062a500d000010096020000140c004951003550440c0d60781e03840e0780100d0041c0c02580c5e0098490b60000411002400d1b80304e001c0b049405222a001d00752584900c5140d450f225070b840041e500407014440f1003050760305041040d0704002c400701150100d0f1a9540309460713049003240c002000c02c071642c41c20802c0d9601405030b5107001e4206190803016801543c001100440081f01c441c244640c0440d000c4655150740080d2242c04030003008880c1c80300701d01e241c41c6501031250f000721400a9a9541050308 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 813496708 1250 813495458 813495461
    0xc010c240c11210301060c0f1208010e070c0b010e090c041109010e060412110a09060b07031e090605090a2d0e07050307030b150703110d0f1403060d080309030913 71
    0x822803e0142451441e40f800c20121241c001540c3d090340d00791035010746840021050356880483d0f0000d0b440c1c0a44c150301d06032464403070300c00041800d07080c0100b0885103000105500d00b40c034103450048207030700c007580c64518545241904880005810902c0c02c8140040310f18100d026042580003640c641c8480b076580340034405035001e907104113281d04030f1032a20007000902e62402c0c0c00310688003414061030303640d481e80341d6010395145610606510324001180760505501035284841d5101d4410120040c80320000c005064900921030f0400300400031412030910743d201c4420000420615a07411022011405d900d041c0381c0700c4610030961070000c004001410102c251400344103016580703601d41155070b0460180c014090b121460b562042c0d100041101400e00100903140b070038020f030348015a00890403e014500483d001d800c0d020b02c003168080d00f600a038040c080c64140c2e22043c84848c0c49880304400300d95190002c00c4010614a008403c01441900000152841c60801c551428031030b100c0f81c00700c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 813497958 1250 813496708 813496753
    0x50406050d0506160516030c03120204060f11030c0d09090b040c090603020d02090618130510060c060b03060117010b100801051c02040c020109050f0c010c240c11 71
    0x18810741000002a00c9135440d00071603450700016040c05441c002010700e0240c04501c07190022400b14400725000710a06a001500403121070081030304510f0035051010240c448060300ca5090f0402c11341030903002001e04107100340c8446000000886c0e140500c44a00500010f000303008624130189010700e181001c0c54503000b2814007507441d03141c40310030a0900030100d020f9032004100c140602c0d006c01c48440541c417448020320342003000c1c1c03c00003400500c4908001e90900000e003080c00040c285424800c00c0550150944107d4a031070415076003081440c900200544480070380c4680c14000c0000000c1d145000b0b044e41c45c14640c900c0f008100d81d10300380040000c0580000301e22030018440c0c400500850030400c0e280300000e8a0a05a01420071541d4001801ea0f01d40001010042c5d4440e10101e040203402c00601052050800252400301c80681c00244442601d500290035581420a466004454022500c6402d48140414418099142d40c060403140417071b000015144200c0301a100c0c0c104d507504184 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 813499208 1250 813497958 813497963
    0x20306180f150c0a02010b03070b1b21070c150f090603060f051e030727090b130f0803010f030308130f0314040e090106140102191e080a0306050406050d 67
    0x40a094070f55850390035058000e004403c0030740d9030340e030901d00c025507042114000805041012a6858410394203041e00d07038402d6101c01c911640051003460b403507080307000710b54090002c01d00d1082d19035200d804c01da06a2042544980103451040100020169002c1c04544d0b03031400c161603050381e043d40d0748401c40441d1054030a007003003030300c402d00d0070b002c20324015070306c194500c48903481310081c0440a40000c0c2003c0d201c0d406544007481214500c05040781c0e05444036410540360740c0801818105880c0c2000c1083c008205c2e1030521003514102c001c000115140d00c684982100b0f0340ca4596031242010909410503010a5011680940008030224903803c034590200b6400007110700c403903506035010b41d00a1031280304d00f440d406061001180d0f86081e80b46181c8650f00c160004204986440c2c007601d841c01c0407240d0302d811500b140001c2d0000d181c000303c030500a03580c0102d68103001c0451242552148584e030703030010070a00d0001160607500703615030481026a4000c90381005019a1403080080101303402500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 813500458 1250 813499208 813499243
    0x901210c23060a0816033b16120507080a1101170103020d0f080f07032003070f080a031103070503070806010e220209150d050a09020f040f09020306180f 67
    0x1710701d18900480286009850708000c14241164684100c503c0d1400b01825a10b00b603407001400c40401001c5d24844100b8018090130b80241c11000c0343c0b2242403980200001c08106d910140d00b00502000914014824401625103468041c03500310032128041c08818009101221502c20b1407441d2400b8078126a070040040400e00319565440403400212001901c0640c41132020703424a4003d4002071451901c02d035a4840802415010003485560001445035254810702c6503000059070705001a1030a0b40114071f040e210400d020044001d0036a4a2050160520100500441c0b0360024050f50088001c1c4c0c9a01d607003503441c0d500443d80b9007440310205600510540d0500c0c2d1071021150050442c1d20a01c01c050b01d8500c052010400641c0010308005c8110340024210b09110700c207201d0150441603c410030700103441c1580000d403980041006c0c0521542e41c2d01e00c05000c41c0c03d135900c560181a4090191401e0340352842c0100d05d030180c08510718401d40148058802442004600c603150104140c02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 813501708 1250 813500458 813500461
    0x70c0b0d0b091e04260c07141018050409031110053d0e01150e03030a030216021e3a170d05060f010507020901210c23060a08 55
    0x2103212152002610640e19454106a045c0400290441c120a562060b41300c0ca81da42c100b0044135440c103401640045103070030000240e0905940c031413030861107801540c80c01200c50400366546a03610440d0740e1096034814076199000c42015040030f2011780d02c2c600801642c0600034003500580c00e86d24100d074250f290080500414402d02c5072038202c5062842c0c566401e6055410212342500c0b00d00e02070308400040c55042c001044101d1541000ea2840030251415140003441d5602181d80c82c0901c611110605170046a14000400d07092202c007082500240381c0c911810039104e1414075030004803001d50142d03100c8070301c0d04003206503030280d48444414010780c0f115103003440c030001c0c40e001d40c1440c04450085c0d500e40d81d030811030000320142c41030002d01500028075091490802c082c05148440c41030500a0074001c1c0c0c00540e0758020001e044074095001d410820049456550824050003c0204540d025000c0818101076034402e03403124421840c484244207145404100300d0f0702500d886000019941c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 813502958 1250 813501708 813501751
    0x906042010080c04080102280c0f080d0b0d03030b0a08120d050703020f0a050324090f2d04110a05030a0618020a0e04110109180908070c0b0d0b09 64
    0x2d0b840c0380c0c44500e0740d850f241800c0c0c491000c142640e02240341c2d50400c802001c45121580d800118030600c0303002034104007a552a040d902c2c1c1141c07074007864019014943c080b594460800389a0001f03250307440014001d090240441c50040e0040c4a00d915543c001d40003140c0204100a00041c0189121002d545060900002161070400b4180c01441401003603024061100c1422102015040d01e0600303807a410348070b10740100e800e4030b0312040248608468000c122840700503142c9201054000028082480042da1000260b6021080810700c43c0d0b55903804031100407150000c411100c1c040ca10504240030074030b59810030020903511600401d40d140c2c20442c1d40c0c00001e40984d010807864804104020503c8030f5580008a900101d075018402d44955a030400c410011441c19030441c055017402c0c0754001506041d06502d0900c6840e80502505680d0b4010006014500d41034800c11130f4802600300c0400d880706541560303500140001d2144908142164401d80740c000b016500c503100000041c1e0b0954a40b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 813504208 1250 813502958 813502967
    0xc1002090d06020f0301170a03080408091908010212010b03160c1e0b07030c020a0809010c022808060a06060c080a031e06060e040614120f060906042010 67
    0x6440d060340081a4072540001510368005420002c06640c00d00d0f0b200c5d0b150101080c00d5044c10b80307168409400082c402000039402c04100c0760400d0300680150307118040783c00411000c10700c0d041841170003401714a002038000c0c0150001d1103002c0e05403408541991380c44000302600d000c291640d94210042c1e40200038607600c61740404e4411030190b1040ba558800300d4034001503680c0414030a43d90069205c0800c0b007256003500440a65112500c010070006089480d58806405035145060420160202c14021b5503a40355072001028500581520820030050b1610140030f5640f0504506004402c00140e2000052080c1401c6440f0707074448101d0101c40369600c482d00e6000756014400c1c0b66460200340d03040e51100e00c90021030100c0c1034002408074145135000e0312000b8102401e5104a04151050040c03001c1ca100b6041d02040554002034130591440c440c608020840701303190703507611400c400c10100e0100028264012801800b20801103580e000b41d088400d4912800d0a0700084c501c921071f09074a105 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 813505458 1250 813504208 813504217
    0x50108011a1e27163b0609090a020409060b030c0319020d0f060801110f160327030b0105010c0b060907030e0307030503310609081317070b0c1002 64
    0xc0c1101c02042c03a581603c40120004140d991000ba09030001c600f140c220b42200345101d070040b800417081e86041d000e9242810703e02e103000c0307242030740001007a40c41c03a00d880302d0003500c40390100200000c02d60f192252111001390460f2061441c0c0c40c4c18200300044180660045a000c3c801c12232078185140d4a100e0300704800c0301d070540302e04c006581c00c00150511811600c65201588a081000310707146203810035503401e50381040c011b0207045c1000c00030640000400400c49400f000316403244901c51105003025079012001905403240d0075101107245848880300100c40c820b40c2d10600ca18800d0341d0300c42c801103d09503440b01009183e00d21690100c0d005243c00c0e43e10300c1e071200f103a1602244400d1810400c42c11034110440c11004944003109010042c0ca40342d42c1e4208081e040044007001c80e008035510301d03080381c03182d070301600d000d582d81d004e013007401a02000c562070100010442c0300001e41e104000074103600c01807280d07040b1380100341e4042135100300034085542e032582000041060240f4041100c009500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 813506708 1250 813505458 813505489
    0x70b1608060105030a021e070302010e1002190e131b091202010e1e0a060e030c0607170d0b0603010b03070f08160f020307123c0c05010e01050108011a1e 67
    0x2c0c4500000000300c403403002340f980c0c41c802e40c000720300051034214840ca0002d0340c01c920300c101c41c0180a03500d40003141841941140d0500c0c541242d030070402101080c450781040c405140c0c02da0030050030f4038494241a14103040080d50744e4a940a0940d00c600800c0c0401c40120001d001030702009111400c1d01d03019041c080c0130400032101c10702c000b14490000302054081d5016001207025140e2207149881d0610040c0310407603054070719614004c070980d1a40300241890040d051101000328500444045076803140501c910054903551f500d586444020714a80c10440b444800200b03a072403d00515407090600724040d050303a42038690150305501d4255480c41c030303c01101007144424800030300840d802241003030074080951142648a034503241d9251030b03054044400c2e07400c0903504413030958120010300c9000600b203240ca40000b0751042031922034050604500321801c1582400008102010198407c102d000e181c417a14039030030074500c2c0134809052000c240c02811f00b1325138400c41c0c0c01d90410481c021082007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 813507958 1250 813506708 813506737
    0x14070b1902240601030e0c030604080a020f01060603090605011e03030e0103091a06150c0d03090804080109120305090f061305160e1902040e18070b070b1608060105030a02 75
    0xc44041001207040542e000105860503103a06110300343d6094890400950180c034080c0088101800219a85420280000305400c800240108041d0301c240580c0c00000c2000000b4000d4503943c000040141501c0700e01507071914a40000043e20001c0c16045008010050003c1c5080e245540c80c140c4d1090044000c0d58141a01e4009200000300403880c2d00340d890103480392000c0319042441c1404101400d9005030311403201c04000c8507025010010385070107107103524680815444000c1c90501101d01407680b00c3c0480b0760078120303058204903810007040c1e1080b505e581d08020742d550f494000d43c3d03100e11585910010742c20110100f43c40007400525188907500440c12910450f810581a084d140c44a40c02841244003542c20302c9907000d810f055001182400a405609150a04210081d60400030340745801c2c0d405041560540d542007442004010b01c420490b0b5605c8082d1403c041a2510303040f074010b9040c812100390352440b03a001c4c0411601624041c0d5549007141d0300e80c0b406000a51000d061987c003038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 813509208 1250 813507958 813507973
    0x170613020c1c0507080301030f02060d05091e0715082e0e0f0103020901060c0c0b0c0d09080d05070b04050a050706030e06280c110307080714070b1902 66
    0x12045000400a00e1600ea009041901c040c00250301024403400e2050100a000c020a4003c500c49a0a8031305407504048240c00d0b42e2818030010700281706000d110031000c0c0c104001c10103084800b24455000da1b0300820401c1d81e071001070443c03507201e589a02820081e00c0c1c403d424144603e10850710b00b60312144d030152015140400c0c40410060409501b503840c1c0d61f401c0e954013880b61174102c1013002d030800e0312800380001c0c3c0e50440c2e0001d442400d050181c070f4200508501c00c50280002288550020100304003419654075a600d400c1d500c403060a5590008200080780001380b10b000019101e203420540d80e569404c0c5000303a580c0c0f41c01450050426905031164006410108105020081c024081c503240083c0041403015220708204005240c000c00d4503c540c803204052141d08803000b011843c045e00040c9a01c0c16210039100d01001d0b000d5003032284804944c40341088008001014040d02a59881201480104411b0756600721401118020320040c000d8614a55042000310381da200c440c019079014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 813510458 1250 813509208 813509239
    0xd03021b061c0618050408030106080901150806060a06141b030d020c031209010507080708092418070b1621090521031b07030218010602060a06061706 66
    0x41c1c844400402c00c1541d40e080c04000d520912a071100a001e01d501c0280200d107080e4940c0d074606c1c0814800c42050024080004d110b401082d8000741c2c024842c007406449803501c0b6540d10f035940300700302d48990060010100115030a4010244054400d040c090814030748640425240f035a40c4071054059850722040c0000904c00d403403400070f0a8201da108004580b0740958012080ca801005407981701140d1420050210300f03503121641035032200441c18640c6140e100c6200c0c4c20300d4030a00301886800d1060b206c0da03603074a42c8803060031280104040b01d0000c00c1d20718410740050302ca8601e8816600c0b000420004060664042100381441030f02880c1d800e8040b00280d4416160040240c400c00300003134984400303000078505808154400c407201c10041d821400c980019070303035a01ca00401c14401e00c240f0b50350000001003c2068401440e40a0400007803541c0031500901c05010070700980b070140c062000000e8102842e4841c000c100d5240da5a6080d00103004800a00900006082107400c15280c8800c0c050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 813511708 1250 813510458 813510487
    0xe280201020c061c06090c0c060504030e03070305010b1203090a031e060615030608070f050609040e0106080d020c010f0e09100801060b2205062b09200d03021b06 71
    0x201c003d404540c1070310640d01101144c1141d100780c00600e40c0701d1520a410b800280e00000d0540b445501180000e5141c45504095402800d104045585031003400004400c1003010b40002420740001d964404044424500464580c01001c01c015040065482c042003c100e8800158140120710b5081c0c10790b1030002d0300d9000076a841c50b08810203400401e00404c0741c15034513105000040c04c0000182c1403060400007c40742c4a00c0c140704040c480d0350f0100e2100002e0340c90f42e102e010b03001181c02c000c20030395030b445031a1034446c0030894420380980205071400170b25500504040300c03204020f643d40308941640c00c0400062803130241c9050480b001c5810041080c100074852800505810340803d6180c08070340552980c0c800c402c50707410114080e040c800308911307200d072070a860002041101d01140031000611607102c00702d59441007000741e800c1c0900701c07040c091507608100311104d210341c01000514102042c07201e14501c026001b00181c1c000300b00b441801550a10451840720003d20aa00d0070615940703030300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 813512958 1250 813511708 813511717
    0x105160515091e100b0f06070b0402011407020603010506210c0c0d030e06130f06020a170105060c0c1e19171903081512100e280201020c06 61
    0x38804103140a20003215000c00c1540402c8001e8030003c00c00b401042c01841d125001900768400c21911410074205903950800000e000c4e24010740407030346800403810081001d581c1514180d010a0304001c06000080f002021909031035000b61071907246920380018014160f00c0b0442400c0c03030440381107002829001c40f054050003180001c0086880d91600042f85040c40241112402414901410180702200100b2029800000544603400410071410240100c560591004226920008082e07401030303040b01040d6001a00740400215130303a00c40c401e0103e90b100c0c80c1c54040503584450b0343c030f070801e181c014114500a0500500a14070b0416000030a2214055164030802c3c80d015a0051291420380d0514403882000303480201596940b0541041e8480c3c101200a0200940c180c005119440e0300e02a6401d40d00010f021070309030070b404074485520b801a0211117001c0e50f0400140002624001034a02c2c49040d84207040c900032030010000b00006048480e081703066002e2008101c00e182e50300d40140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 813514208 1250 813512958 813512983
    0xa290d111009030b060d050c0f030a0c3b0a050408160f1209270216030201020904050a0606092309040b0405010b220c11161a0301050f01051605 63
    0x40c0090851900c026284c800070210f0307001e801d80101101c0030480010b5003035160003090b20340305a80000000864107010f00028040c00d0076013803020009094064400e1101d004030001c080a00403201300700c4100414261400c1025804007600c0403c07014441d030750001e0741085c41000c5c40b51603e0014075003e5040200c45500341c6820180f100e54106000c0100d030b84001d00c06a40c0341100e502810050a80c450301000701d070f02c02900408407204181002c0950440d07002010b01c241000c0b1408807850000d010303520119043d802a81803201080c198ac006e80603810a03035800e61915141035041654859505004100d00c1007000c080006070003050319400100390065004a00748052440c040c1021030a64480d185154001c00c0c090350011041007192001c610842c00e110004030b038000f5818400c8a20118521580400c0d00580e5100d004401e00c101003502100e40c0a012100040c1100101140310300091041a40011142d50f403a0104e600c100b0003402d01c42e40d60b080302030301d00302551161454200003c0c40c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 813515458 1250 813514208 813514217
    0x703060e01080129011e1101140612010c020304050409020604120f05070b0711300105010f0b040b09120a170405040608030304030f0806060c0a06050a290d1110 70
    0x8000c04041007002e040c86402044480604d04a41c0c40000c0004000008040e03a13508a03d40403480680300e5130002130342d040c0107002444400060310307990740301040c1503410a12450a209401c030100d00306000780e40d0808107580280d4101440c15041c00060300ea0380b0401c1303900010803c400700b24981c1507000d9600283c010340c4020f004081910704240340005503041610750344000d200c80000034080b0040380010b441c094541407844041803440c04600703031410214604407601d006201e2404801540064125040d80c50303207815840d07588081d80d18030300c214052104000703030400c51881e1500f08160019801c3c26654116201120543c0300c4400c415801c5905461002e00001e04010b40d24040c0a40009081120051442c50600d40d0700038101c40001190541809212000201d0315591034040e00c1003045000280c5a07200003c1c40d00c5402800c08554404019203003c580f1020101c40310380b900c11200f034120240341c42081600421404203a00c0e103013143d00e144152203007103468544901a61400525850707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 813516708 1250 813515458 813515471
    0xb09030702010216030b2706090c040b1005090402181e01080a0203070c140c060a031b090506040311030a17030a0f020f040302040f14180c190605030703060e010801 72
    0x84c24800558190481060400800c1c00482e00a1035040d401803c0342600060000344841c0d4404440840807805119025200400845880125030101e481000301c50800c105c9458004120090207000200c07000a08240440c21890400e80d0081211814040843c601c2c50002400100104200c01c040001e040100e00c000080d56009a105500041d00c44410743c02c500d4582002010100340c2c0c00003500340c1b00744008240066509107ca001e0342000544a0350f51078090340740150113405440c00101c03c44406400c003a0680b4400c0342004180c840040c42d10341f6152854803004c8010602c8500d560740b5010b0700300c1680000310940003924841520b84103098a1381f610414039000c641c0c0581c964048140104215058892a04219800e41c4c0d41143d0010301e2044e00401c1e40000c1c01c1403030040320956030800502850700002065a000c1c2440b4034103c030349007002d100a125803206a450030030028012070000b44611801138001d0340e8041081e14000940580d201c5844212003803e91100c1ca55035034458 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 813517958 1250 813516708 813516713
    0x90106020715080f04022205130b0a060303050703111212090c0102120d020d0b120a12050a05070f032d090f03021503070c0602042301020c0f09130b090307 68
    0x11008680410b050400c0c102c0c92030b00842844c03d0f00801440203105008298801112052030203007020b0095032800c0410051400c60285550010419026a000d100d80e000007164040c85004260a40e540b580d50141401207a82e010340e0713000c00001a0b000c050081088030341c0c002e0602d5002d06000b10400d40d00100909102c40001c4c1052940308000b4115041142510400605c40c4e0444800a0340204016a07400c1c22060041c01003450003501c3e41d0000c4140e171160014400040c0e0200d2080c0188032038219242105401d682d42d00c201c2c4a0b4002080e0b091087e00041004420b0912400b07000b030500c022060350020400707042ea00100110304101010b12544024940c0c80001d12020740380c41405c0302d01c2c00307040d5000211214617014a10b1f807040c100100040d1154030559060444960001095450701d450707001602c501003000015a170310104d008000d841d65807000a21403507180010f851484c003050204180006044010041800003078560111400540e508000380e102c0c1070303a03c02840c0c1700d41c140e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 813519208 1250 813517958 813517979
    0x33c080d061502120c150103060e07050102061b0702010e130504050c0f01050f0d062c0f010e240307080a3f020a0c09020706140108030d11090901060207 67
    0x580110020529425410010b1600018010b0050301414401a102c0041c0c418980c50148941d85050099081000001c1000707025041503008460042c00e65408507102c000480e60349500300c2e500c0c01498500e02400d5101c45840000740480760042c94000b030b41665520100d80003000c01c41403600d5031035444080006100c0148a640d5200300125880d0307903080040c40000b00140150703d03e490103c00d00194100e045221588413800030321070807009100c20320795004c116451204218807056a1440c68001912448103c60281d0503241e43d00c04029094803820781200305d40c0c6000e000020045034445008400b594100400e4008000c184d000b000c0b01c00180c40c010700340982002210055200c030b44452001502c02c40d0b4000040310b1480010005010403400891800c100120b01405441c810b0402140c9254160014820580500801d020401d030302101d903920a0000d11460106400c00d0106580d8404603811031104422030030308407402d003181c520000322682c4003a4000c10240e44503900810460150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 813520458 1250 813519208 813519221
    0x15040e0402130b01023705030408010f0605100305041104151a07050a0b1e04082208031606140702030319090519080c0d050919033c080d 60
    0xb00c0c070052124040e4100041d40d203100d00040704501d840b540070150b80120170a413445400044c05a03e80d000110305081181c0c80343c2c400e01440c4100c2d420203c09080851a41c0903401c01c03640064100e400c04000b4542c100c0c024000580300322a03444242926070403d581c1c0340103109042166030741c941503261821110b104089030780c00b0300e00281ca005026800100720f002c42c0741e04000382c202112a8940d500d00000404080301d151300111845450750900081c440c0b00390142001c0381c90011300c51602498040b00300c1161400e44148011a03200300100303075020b040c00501c0b0207038500c91400450130b0341c03212034250200310307040303400e4001070f0f00220410147c946211181c0021107000541004400d0b02a15425256811003a02c2c01b00ca96101c0d02d22010001e09604458030303140c860064440c1641d0b50f4000400395072001100503c01d400700b47e02001195800c81d425030480358403894a0b000740c0d02000714031003103030340403500e400e2400d40b1081000071810b0b8110305400024451031060b80e40e00103414000085900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 813521708 1250 813520458 813520489
    0x10804151104211703190504080d0c1803110402070807061a0a0312030b1f031d120915070b04030503190b09040b0414010e030306090c0307091415040e0402 68
    0x4602001c1050380d208000080f1440344020360b2651541c40346006c0000e08440c450316a45098204814413980d40090403a801070341d030003842003440038541111140e2001e031034184102c0380d00f0030400018031704c1100010818405080503040a01315190011103811984003540e8194079442100200f4400581490b40c66004840c9425042c0c15a25008040e42c6024010000d06030b541c0c08074030069660143d40501c034511495400228003c504004024060680030040d0400d0416004158240b0201d0810aa0408014003909040302d070320400400c414440400b080460302008404042030b1880c2025202d2806621b52950740c0c200060002000800031081085907841c041c0c800c070a9594003101c0c170340c0050308103005503083c1c0c032503080003541c42003400d628900e6503180c491441c00c1104040007030751041e40302b1112140e05980d00031404150381300c11110b40e0005004e4440501141102d0b50b203003454000c1c0034048000e04101141068031300e5000350410401c07401d00c401003004601e42103040b03070850075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 813522958 1250 813521708 813521759
    0x20060a0c030e1c0c320301110c0d0e0102060c0d050c0702280518070e1201020315040e0102070201140c28060b01021c050903030706110a170411010804151104 69
    0x1036240076100035003e08172003c4281c001041308040e0207660300350005119005914289582c9560050906949080114000d80070035290140b0003400d42c00850f4961044e45550503030391501e565801c01c040105001005424942d5050100801507100c1000440154520901c02d20740c8a0b2460312124242d000307984043d100b81c411421500d00e84c15071001b480c3c0c229600e4100740101000d4900010442030910040c050198804010011200c1101503032420000c0300361001c08c04062130410366800d038031440380083d0100b0103214030307100e95200000040c5841600c60085e5201d6111680c118092220300704610040d900200280a0038441188200c1c4544070003400106061a01941d804a0a40341180c483c000d00202013181a01e41d10140221021740b07030720550030440b440a20000a145400082c0c901b00000c000d20b002241d5030101490080c0110b410180c00e4407804c6192004442c0d41d00c2c0200304803100e2400503120040302c9094020250b00f04081882e4540300c6007000d44a0400030340c0381421040d40c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 813524208 1250 813522958 813522989
    0x1308070501021b010e0301090b10050d2d0b130c1707150201021b070303090e0c09091504090c030209090c0f0609031501090920060a0c030e1c0c 63
    0x740e0b00080d0620300242d22114100041d605800143e404c1044800300a40550910000408000400c0106da1180300900f28442c1000d4035202400103400c801800185060142d20318101007103516809a00407085021021a0407842c03980c84500c040b40655400030780343c2a88480c181000304010106001d02201c40c00e501103091001125550f641c0140700d0401c0b11050071080300c03031461003901103c1036071841000600b0301b144482c24030742e40c0301d08030300c0260002407005c1c20115007030044c0380f00c680c024085000410f05207103040c401c200050001409a1880106100b410302c0280c86900910440901401c0350008c000e1450060284600006050074210b8002c090b400e2036582e165002d1040200c1d05072190340c1c48040d0400400e14041680380354076000c44940000084a180030b070451800c50344204c106611520007882126004c80e50724652030750001e410b1140c88842841911031003201c0b030081ca000c644121840c0040307101d07074a008044101e8001040000e00c14020181c0c00340c1e006082098055218 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 813525458 1250 813524208 813524219
    0x241517071212030b0a080307030905040e030a1706180106080405300309120f070302011b08010303180312050903070e01150c030504080303100503010b01032009010c0611130807 77
    0x21903a031014181a07540400480b19100c0e2040440a04801d9080320f0340c034112401c0141801c4850310444cc42113040c50303028041024040181c07134000801d5215058114074400f038042059000030304961f04001c400381c00741034180b01c2e040700394000c101c80c0c1c4940c1a42c0c03d19090950400e80040d0301e80c500041540e0345195100c404101c1c22a40400d00c41d40c19441c0d445001049091200700e8a0041c0f2400340840c0d0408035046010040a00611907002002a006081030895080010400b0800400d55220042010a005035158414001050400341680b41c9075681c100c0d801c1c0c200200c1c1d03c0080c074080740c294000d0408020003805040c03400742005c02580741110b81d400b5002494892800c0040001401007094000c9040c0c0c2d024200039415030380c0b84d141403074048100180c14403880f407282d82844450182540244100b141704820160f410354042611030200701c069000002490420a0001c10040400d0f200c0c0704100c01d40c410301c0102c55492400e0f4522402c103d00b240c1208406400c155000c202 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 813526708 1250 813525458 813525473
    0x2109120e0901062a060c09091505130e1b0114040e07050a050c060f040303141510050409060b0403060507020708030a12060506030702010606110a2415170712 69
    0x45648a00c1c201c0010620410b070100401d846655402c2884641c0070410104440394110a04070000c6e80d889014140d500c0c83c004c0242c41c911200b85d0401030a510b01408642040c072182400314100e80030100300248684ca180e03107005c40d500c0d103002a84e01d440808010560b440f0300000d08121482a40c1814241001202c4c3c00056020300f4510a100d0b0010300303542340074064400d8031007801071007064586906e011084003031804011902100041c0c60b10241282c1d01d0000f00525000e0071501ca6134040e92104c110a20180c03000d40100c000502c00244070010b21954540106006010f002900d2522a0701c0d40c82c1500a07100c001e401c100c1990400e040070f2003013480020030341c0c0384c0c903045150143c00c0c65405100c400c0208a2504501c2e04600c0002c108a115501500070400300d8072540d441c0411800d06140c3c00303807a80c0108400030b0010200d454400300e048032540d001031740420303a004005588000420100c0070007030182d0003555562012303400c0c2d603000d4074207200c0c00008110720318003a0880001e80d83c039200c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 813527958 1250 813526708 813526711
    0x210108011107023a0305091305070c0f03230c0705030a2a1a0307120b010212030408040f0807030618020f100215130615030209162109120e09 62
    0x213558480d490070381d204150306a0250044c000f11030420101642c40c1d41001080e90f4001031b802070240302142c201d000ca503a80c5105071846a14a9a22070710440010350721034480d401d02d121f0941c2085000749600d140a1048103a8101030a003401141e07607113080607841241010a07650000740700e5003200356034201050350582c0c420b00030b900c44421481d04690040710b8400b0020260050003247c12001004a0201030340d100841c010ba10a495080c100c56103e00302405540100f540b0500581081c1d02a22085014002964100c0e00c6414030504058a8942d519021100e80c0d0068600e688615004c00901615109400c41190403103904100d01c4100d40100328840186020030380112291594130513054401c1c08108a8003216200b20042814111039001004003a4201a1549031030402002d52081a091142c01202c1d405000405541e4031000b9401122008000b25000c0c00410000501c00c410403125442c00c45084d840002510045401e02202c1024900c0b2040280140d81080da0b4213941c0d190f0085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 813529208 1250 813527958 813527989
    0x303161e0e010c1b0f0306050f01060917010e0f030703090f0f0b09011b0309090c050c0c040e210403030305090a02010e1201021e0909070f080a050c21010801110702 72
    0x3018000c2880c984070071315070f46001003960441140c1c5408111800c2200c400c01c1200d02443c004c0c085512a019a07a10070402803103041c01244950804006003000541d91490303c141c24ae00002d0fa41e0326462800741014080c1e140d101e03051700700091440405401441d95006803d001140d1103190381484049031062501d80581344200c1d1000c00c068059a20900740c904081c00301c00098504c4819501c1e02a00240c1c143c05014119424100d51036a002d1298066422400300003004120340406c034000c0c00300400040060740c80500610008a40109681c01da0500c9030040e401301d03540d00d5146040080855502400b41c82c05074029080400250385d1001442c494110102d442090300300391102c00e03600902c50110032003401c1d540c05200c50025180d440150503080070903200d60b555a55891000c54004501c0b103018008104860003040c4102260b512099102d5403110301d00c1e14145045c1541e010b5140c003459541d00264000c0010b1003c0c11080c051180c41a00c008500390030101150f0000340724060340c0d03013403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 813530458 1250 813529208 813529217
    0x1005101e1d010e061c060f0903090603020a2a0f110918101e0c0e0a06080705031305010603150e0705090c2b0216060501060912080903010b030303161e0e01 68
    0xd08017a0f00c036030300200a1540d481170701000711031555071060f0701800c00004190003103241060001b5101c0c1c0603000315170003000141d451009000c844a00c44180c0c0079031007041240761083c0340b4a000040e1030740e0000c41805014200c000403180340b0100704882c000d4001c18500c1c510b41c43e204080700d000340c00944c40000d6400c401010582c90b21031001c0c2e20ba02c410b440b140c8045103040140201c0f100d5000303007918010181c05e585507103116844800944085109941504c0040c004100041c14003c40d14601940184103200100b4021341c0d03502d85119000080c8007203020290b07201d126141ca113104000480040c03000766401c158601d0100a04d003032038091710f40040d15424802400c19a202c062555120002005940854036403041c46003824200284a10072181685404004104e06000e428440e045803441c50921302d640a05544c1e80400360812000150159251a240b5420b1354050004c0c512844140c0e601c22701481213218001c1541090f40d0700c81394080000000000c0442c0d104040c0141800e003801c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 813531708 1250 813530458 813530479
    0xd0204020912061003060609050c0415090305060c030a050702010b01021e070509011d010801020f0409020a120905010507090b03221403030f0106090501111005101e1d010e06 76
    0x1142690724141c1248419015001c20040113a2071101030303005480c0500304c2000802d03180c2c103100c02202c109a034001041c04d003e000400403070301745c0800440514a50314046030040c0d40e940e070b00c0746044025903580140e8900072042100c13040442c422560300200070300c02032120f401c4210001c0c1d201d840d208144800c00c40000a41d80b4140d4041000500601c4060500480c80d03035960441d6401c070110b070205915982022000142060703050003543e0400701202c03000c40ca001c0c5884003200003984030f1400e02c3c0030b1204018620441c2d40f4244100a4494068400410949002240200694041d4125002595051040c4510001c2e40030a9056181002504d41100059400c001c543d000c008040c5415601c8004104005010048071160403100181c84202801383c403280103550001011817030768000d61205880b050002d819805c0303660452500c1c85443d403010b4588001810880306019041a03140e010b6008008884407040c0d0602c05e002501824407403541031120322501c403c4c014240d10310807c80c104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 813532958 1250 813531708 813531727
    0x6050a0e032d0f030d0213050307080705010507060e0a26070312020a140a1107331101062d18020c01021312030e061e131d180a020d020402 61
    0xc0f03a841109001c5046070f49480305010f090010f580b000b03114000284008000040d03a040c0000c0b050180d5030b07118041d0403098105001160b098218a400395001ca0300da040d40c6076009014090180b0250207090441c440c1c41581000070301d06d0203c10440d01c90b80d941040303d44042640842c1444418806400c09a55180c0249048030380c0000000d0240142c8000100801c06640051b039541d14046140f040d203812550ba5005504607607a070f0400c0c13550f150502c0703c012400c1e00c401910500d1200075400c01d03c2d8030454840c3d034942140d04681050b070111a100d1140012070851821081940144c82017103660182081c003200310580802003103a04240e000f056402450b202901a940b0012a16442c49403456464020240030301a0110941c0428500e903800780c0c05080100031600a81c0d030001c91483c54422965082929030f1040c0a10160356291300c1011401c103100c0048592b0714215918ac400c1d88d41004001c0c800c5100e0802040d5502d45e00039032035a40140c99800c26600b1385601242c00684aa8510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 813534208 1250 813532958 813532963
    0x7020304060f1103070b10031208151917070819030c12050409090b070f021605100903050609010b030f07060f141306030f0f14010e06010c080406050a0e032d 69
    0x405006144980c000304107c010b441008122003164010011503004403030842045e25034000c25030718815411943d00390301885007404510102c402010a056074805039960f00d840701440506080040d01390805482088800c4e0108100500c400c11131214180d8800c0a0350060543d248910000300381000c3c00804c41802409842690700800414406002d07043d00740c6801c65403010102c0e0103901142c2c400000c0441c41307100040d00c428110032422404101818002009541c00c4000d2111080024070800880040d07130900c030890044a522002041129074030003058204100051080c00a5004400400000f41d0004015801c0040e41c200040316581c0401c481000340714006040c01d01d0740b0a00b0001882030b0341a4003c00150042180030001200c1086e628803c1d00c5061031100c040140e03c100500ca00d1202e501d2260b04003505041c0030103010126513408800e41c02580c4418003007003006c10510449604002c00002e00305040300644041411795a081104a03095013601d41381c182c0d01e1429a0424008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 813535458 1250 813534208 813534217
    0x2e03030f0918020a09061d060d110d090b06010c0812070c050a0b0702070b070218181b0f0108010303081f05121e01020418050405010207020a03050c0907020304060f1103 74
    0x720802103003400b04048000081d5010810341000218a40300c00140075204100030070340c0030f00321049503421081c0d11040080c02e42060156400b4555140e070340d000c1c40c00e0003100030300454012280104554109003004c00300f1079002040181482102e03110307000000c546070102d500c3d000c1c1e840c44d0a40140c5401d001103c00340b591170030003019032154942c900c00b8009500d0b01d840c45000c00742d00b1030b40500d407102c1c7d955100d07009010b8001c1d00010301391200403610212196503640801040d821008200070201e142d483c00f114080320048041c580b4040e0251070800740040d070f441c145d00382041040b95141d41d0340140003031030051440e10303c001c1401c02101c40d038011039001001010020540307800403203680742c40c1c0c4d2140c202080c40b18514a26480f0844801d4040c001e440072604244542d00f10442c01c0c4c0035260240170300801c219160b560800608005a513001c008001460280004008007a03458040c0500c012014280358150340c420f20082101c540c0c03000140030001180c1c81c00c2200918814003ca2542c0035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 813536708 1250 813535458 813535469
    0x131401180b091209060a03022508031006020d0c021e03030a0201020901030b040603021c0606080118020102160e1602031c09170a0c030509031005010e2e03030f09 71
    0x9400460030103001d00d90010710302070a80c02c000e640e00030000c00201c40303a92160f1684c07190030813030911000410302e0280c0d0242901c2e040c16201450345400074203610b054400e03401001c61b498400070060048103904100b03141d02405450005083c5100a840b0181011005030002403103856240d0140c0d0214400b101d403007507800c002504403034980d001c0a0010b4040d400c0141103a0000e807800042807000d10b8240070321802c40c0e80103811b45540c14502d05048440404040003642c2840d00d590000664403030034800c040c008990b907212800b50245c0342c4002400e014030f00051140d680c8407418148502d00020a04507080b024910707002020f511400c3d01a4110f00a0822119040f0000039070080e01c1461500710140191048100342070010310099201e0f114043e2418000010703142e2002400024081c4000f881c0403580141101c0003415000500d9041e680c0981100c2e4881c0c00e42e8003449011890706450802034801d4180303048610402c2900c405032140700f48005000c0216191400c850745000e188110b01910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 813537958 1250 813536708 813536741
    0x31602010b120f0c090c0a0305071809090201271701090813030b0609070f1b02030a0302010b040b040e030d090f170a02120333030a061e0203131401 65
    0x508141d0010b84031101e51154400714040d9400c4d0011915008101034820710741041480c0c00c002e10300d90202e0040a00810300c405100d840250b03504800140110340d0020940d020000c14050800d10004014003203076013032804020400e252100d039114420f10100190307240c03906820f1018a4050080d40035100b034031000790809600040d00340310030090703003140d9042d280501e59114035a00c03294207200c29000121500e40004000d80291303800d0500c134407503845c1c5c140000480b81075401e109800090401e004d250048015039500c1c0800400d509150003410031044003103c0030412452001d0070303280c9034481d0030103008a4994828403201008000ca841640b041e4100050104071a482a40001070703900c40e090b80405449035030480d01448840c0c00442e0b200392584c1180f401185500c0c61030148020491a2201d10701e4028001481d03691401c104912185008400110ba0095007041c65180c4c0e00300d03c00d1034104240100100090710020701d41400389250b20444500c210210308448900602c0355071a01602031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 813539208 1250 813537958 813537979
    0x1021b190915120c090c0203071a06031c0905010305040602040b040308030f060d02010f0c05010f151a07050606120a0210200601050906130e070f0f0e0c031602010b 72
    0x3040c9641c403850400305440e8a59403060b4031030341c807840d03890b000f860020085034120310184000c0c00c03180c00100701c0000c05c0c0116402d01c10541e603114043d5088004002191002608208451904208030321000151751160100d00d4900400244440105c0c05500c0c1030544580100d01040f03855130485000302003000e044d903182c1d40c83c0c0c507120354941d0082c2d03240c6002903400c1010444a140c401e0f00c81952980c140c45480c2d004440c0f5a003901d1040036980166044c3d50703070300406484606913010b070158842d0400b0045003030030b00300070400105104152040083c0f445c1030004034002000090303419000101201c0780768505030b05e0500e41e45400e4107004025040603540f455151a00d0b0480301441c0002011502d6210310b0484280143d65500d0910405621407190004610a4101010201d4000081810108984031076018a6140c600268440c0d28065402ca20410240c070350700c1c16240280031354050a030320320f0502400326249800b0140101d00c81b844c07407202000600d4000d600a003540940a800407564 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 813540458 1250 813539208 813539219
    0x507050703030c0b1806011a070c0f0f091b030518150411060c060f18150603060c03011401050d0609090308060f0102030a12051509100810090201021b19 67
    0x240c65605044581442480125440c2515175040400140f020002003e4980c0382c1410202da228440c1d80c8141080410491100403034004101140a800c00d0b01071001c2140c5040ca10039442c2481d0b501040d0b9540c644028807104248808a0241046080ca400700b203940390307038054882c07643e0464140500391207101400c0e100304100a02d60b501ca180901406181850b51005100c070078800c0c501304844580003200020780c1400100e240ca50081e24401c0c402140b0f06155079038518002c11541030700c00346091601040114a020030440368842c04980c0d08608651504070018000c8450f500003038144480440c5c0380301e1035070607030740120010a01d8580c24050074003242005080c0c03000503620301d80504c10700c003000c0c0415400002140c6d58200240c0c0c0b440341b00b100ca07000680082c200a0922502e00d600e010342d451309039641001c002d01502c1a8038903401a50700d40034215140030902c0c042018180d0910500d00c02507a00070070418400700008042c260900310030b50028008079600c1441c801c02c1d140344c480100d038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 813541708 1250 813540458 813540467
    0x18010f0602010f0e0303060d030e0301150312020a02150901120f0f1a0604140a05180717010b190905120714060313150f020d09030f080601020709020901050705070303 73
    0x2100c0d01a002040050340400c019002c1c0d0f1641c0c100f001c1c4581c001c2002c90131a08084510300002c2d4080d1034001a0035140c1030000b42518002c411740d002c8224140018000d01000c0c1c0c2000c46100080d00060000030496804180d818480800d400447d400104418444d640103644545005812081c100004003100d4130041c0105011642841c0040c0b51004203c0c1d0b81d4103a09201c0b250010041c103190030285445030324400c41e0044c1c040f05030032030210702000030310f81c0b00e04c12a25204016820481d28925000380d004040d4a51907001d1101c0090310300040010809180807203c3c0c030603150f00707e4034080c0b0802000b42c61b4060554892900701c0aa440d00e84020303840401c4070410b0310801c004900210260108000c0240010b6074401041c1d0003040e445000181071140c0715002e10b590041c0410b0b048558a10101240c100f2101c660110b600c5003e09010141d01c1881c0c0c0200e9211130801d60411300b4882c00003507440995003d9855103940c00612424282e000300e0a035034041d0f07031160840d040c50782c03680750040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 813542958 1250 813541708 813541739
    0xa0c03030c120c200f0402040b0a0810062a050a0813092a1b0606090507110604081303080409020a0201181a06041e1b020109020603040b061801 63
    0x1211480d5404248030030510079070078002c449130030003030030b40d00d1840d00007003c003548824101003540404d00384138060040c1c0f501d0014100428000c1a4a40c85000d0448041c06443c3c00408046248581c2031051180a4001c00d0014a0782940c0a01218100405d541105090390480d0042c0651140f000914100700f11107005000c400c0d00d18464090f03943d92600000d040e60221041c040f01350140e00e138011603003d541405c18607000c0507464040c01826800c00710010380c92200b80142e6805460381e40c10f022143d418011a07420056511b0300c0e20780354860a90b00d03034a40320041c1005048803400104841140034455002c4059600241120303078540da1540900000c4d4080d58500000d0f50902c03008480712010041c0c1108416004841011260041c00780c54400d91401410381c0d920079910700c0201d25007844c600030151102210900003400d0004120040c4006951452110031681000d0f00d1030016100c0701c06598005601240051840d02c0d1070780011441541c403502702c102d00c86401c1c0006035180d440540722 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 813544208 1250 813542958 813542963
    0xf0d0c27090c0e01270e0f0108010c1b060911061b060609100603020a031118041a010c06020702040b041407230f0c010b0a0807060818060105060c0a0c03030c 69
    0x401400e0200e1600350740c89104010340f0b40c00325122858000e401c224607024410034030030a007940560140c0350006e404000c4001d9444801100c1d80e07400610240500344180c0e84160003906107824014000398481544171105074000300310b0340e1100603280400c004404045074021008100300e88a09103c602e1580c25180848009154410b03040811910b050030700005014210703200442d00c04a0815506501a500c0300818a04040e9580038a003101107414020340300c282c040c4407100000102036410442502c014007440d040306003034424104042da0b00702c0c01c02c00b54243d01c0f0201507141e0203940005401007545a05142d04541030403007803d29141031860310b40c070400c141d480d000c2c10782516281c10301c0c2255400740c840444170410010b0001485004010b01046d00042e070002c0f030300d0038440000c03480c01c1400d9485061300c1d03031222809120f8941c00050140c0d00804003003c0076080c103184011a80e48441c1842414010b5600042e91400e010741441825126600110107412036a564a0010100a5220000e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 813545458 1250 813544208 813544211
    0xb0112030201151d0c0c03071b090501030c080114010b1c0b060406110d020307020d06020304020301180813081c0302092b031e0905090603030d1e0509030f0d0c2709 72
    0x200e848176014196401c4110b000d00542c1007048958410100303880510f170107683d01c004590001403891311400b070036018501c01c0c43c40c014150b00d003c0e06542510300c512a0100364034031482c0144900c484803810fa4400401e0301d84404178800d580f21341310300240149003a0703603000200003c4c00715000c1c0d0851821415a000501100c0d00c0c0014110220b8681c000d80030001c0d8480c0110b0481c00102c3d18580186803c94001800020454a05509064502d440301e50850785408040b0346140710280301440900241400c03000b411040141000e0f0324860001c6101c04020b01d0390120703801c0c205450701d03644102c0d0f2024110002501c04683c2c09035140b0000041d40890008460309001010600384500f592200300e40b60311030144060815042103d00e60005140c560144414440408040220702410710032100c25454810a0081103c00d83c09844d40201102d05a034420080500c075081810b00b16800384100d043c000a1081c0800700441c1c010f41d02d0365000e083c2a02c1d800c0d6500086025142140031251078000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 813546708 1250 813545458 813545461
    0x5011113050105070309060518030a05100b03070303020c090a0219030209090a0207023a030504140906060a050a0507060e01050901200f0306030a0b1008100501030b0112030201151d 79
    0x110780901c02c180d401000141c46d11010071090b80140090224a0f91400d41d00c0c01041c20030010900e46040311506442d40d03400500d10122034080c034811940386940c01d8014207825030543d1000f0b90b5400c80a180c1c58011148240007600800041e03040d104080b4442030b282c00030f070115650003400b942110114511a02980001c01c460070000d1084a042a90150064030641d080c0c00403016601d044de007071100380d0440c0c0200600c80c1c1d00c4101101d07800301d20030345415880b079050506502040700031034183d41c0140d000c2c5040c403000c0c2e9107000503114080d225140c06640c032a90040c1c203d41602607443c0092456041c01c082e00b140c0101900618496200780008220300300c040800703c00b000c04111070354000184200711602d0401c410300e000303680c0118003400301c4101401503903a4a041c100100c46541144000310014002c00703006101002600d140d40900740a154110388500c5221704040c0b040282072258280038408040c003e401040070b6076076190311080d290b03a64290055000402102d1100301c1c01d20b810 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 813547958 1250 813546708 813546719
    0x607080f010815041e06020f1b030c03030408250b040303050f0403090504090206270a09020315040504110a0315060609030b06010f1701031505090105040b1b0705011113 74
    0x999181c5205246003103003e1600d4945071000f1681e0f100f184c14841c1c0740125100d4010400b58001011250307038030000d9565400c0c14140b40e8440b90132883c418441c83d0400c101c1c0c1c000410f400015603401c1500082d100d03650341580b801841c503843c62100004141c41e10b40302c51038203110341555014802c41c0644c80900c0b9030340c0d40c2c0701c18038150030341140d0082c08150200414001401d00e540054100351000d00854600031059003030100310900704614444034040c8100700302d11802c2194112004105000f811f604500788512200490050508110300550703841c000181800f0f03200b222103100d03140203802e21408a48a09040b0030168410380141d0049007405d00014003580b1502c1d00c1411250040c000380c0941e103c1c0001161000d1a8980c2c0400700b1940f112821400075201581034001c1d4841d9080c1095925440044400e481c40200307001030503494101080086030b200d00b081d5a100c02e0074144000c83d0100c0e50084c0c41540900c0c1030280242d840c180304d0007503804501009102540140d188104203035940c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 813549208 1250 813547958 813547963
    0xc020606010f110f030c010c11070e0103110402041d0403020d180e151c03080c121503010f091119081b2e08010b0a0c0b0a020403050607080f0108 64
    0x90361441d000592042482c0c031464030402d050a4080380c204161100401c2030040c1928582001c44c04a20507550380042059680e04202e9032404000610b001d400b401e85014202d103201c5030148005050480005210007485c4c0d01d5070f0481c1c000d0142014902c188010f41c0d20f400c80c074a4401c48089000d8800d49a0000c485801002c450054032039103a820341186040090440121070040d045100e0f00e4a00c401c2c0300002d036521480411951071058040d00d80400905004000540c05040da0a01304400c00c4580245080c8443d4650b1064464802d1590580d0b01404a030060212051882c000d034584003070742c4100004180d50541016049407000b801e9040c05650011000c941d11860109a11070224003c11540c0c400b00a541c1c481d00401100841252245c0702c518004000480320b1203e000241400e05540c0002c0064003404070043d240c0e00701400aa0007a0000810900140605c1000000036020680310b4040b1805541d0103001d0364240c0c14621400f41401406a4105005603941c2d0000f140c0c0c030a00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 813550458 1250 813549208 813549211
    0x9090204050901180204180f03020312060a0b1b07170717030f3a06180b0303030a0209190902070201120c08060d050a1407051c020315060d0c180c0206 66
    0xf40c0790b144080000ca85d082000070088a441e01103400e44041c40e00e40400c0e0f18003da108110702036006969030309007411400d800c40d076000344100d01c9a80c0c0e548040c042c808032403042e503500c1070681c02880407480b0076012451500c6030690000b00e111070307082483c21012a001c65005c0c122001c0a0b5031119684c41520003580341d0180d0500414145010302000d5a10755810310540c014080d0003c40b0010700000080c082d01070146d02004079686a1521070420503044410300750010500014010807402c0702e1100003030707186c0c403014204140982e000b04400300a1703a28441908407640c10456030401d05035442c2e0103040a90880c240c181c2c0840c0c0c024940403006140303030241160280d400c0c0c0e0740000e02da5695042040c601008002622030340300b0f880509001170041ca50700b042130b05207803004180071803401c02007105056660340b01640e120859045c010042e100003c07044081c3c0d00c006e5029900e43d4486c00807032006944600058081d80c0f0001c400281180106c003808610042c0c140280180328681380c2c00d0380d95050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 813551708 1250 813550458 813550481
    0x30c150103021e0105120a06030b06030c031203070516111819180b090601050906040c170601020c0a032f060a0e0f0411040e0907080a06020f1309090204050901 70
    0x100104801c00d100d28143c0380000c41d19050403d01d0410b90000c0c201703105258102da0555065582d80303401c0c002d00c0311810360ba6070b001504400604407845001c0200340c4800302c1c1c80c114944000d000c804103c00c280100241c03000940d228140c04039588070760a00107807081e00001a00e0068044c0740c005844411a0010703644500b001c20302e030b41c8501120712020401849011242d4140ca040c4001440020b0b0b114041720380030b0b0510b64014042e95051104010100c5005172015100c1c51400340c1081c030007a000f902400640d070a02c51080070f659600030041c0e0170711400002e2140d00c24070f000c00110400c203a484030560182e40400d6001c10400f08000e5030980307600510506070b80440248842101c0c20704c19160551002d0717000c0c281c040c05220034800b0030207594003d86241e18201c0085400e2001250211074203500a200400804000380382c02d540c16160b00c8001406041c158000800c554035074540821a01c3c50001c0000300c40009686e00c02d071034002c001d90b030012827040c1e0405001c105880c205024000b5400d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 813552958 1250 813551708 813551719
    0x17061c21090f0b09010e04020f1e130320060c0f0106090c0801030f1505090d0e0405010e0c1e1306020f0f0d0c020316090c110703082a010509030c15010302 68
    0x18100f5030415402c0e0404c10f180c1c0d04008803040120b4003038035a8000b4144d440f0000301241c0d2100000d01c3c403c0542c2540d01d00c50070020409008805031000314841040032250400d08145d036045d03002090640c8070b44103030491504014002100604000f0002e556407411007401e0081168a07202d0780c1004c10303918581d0b0902c0c0058001d60050011034907046840d520148100f04240200550452490a60b001103500f8440c0350004030501c1901504105070613000705003254100b14030f60620309000d0000790080c28580c8000d0010450300c0c0038403241301e901440c0303003c810b00c0607440310641d092a5121008900883c40180211440e8220135200002c03148407000050000c3d110203011484119041d003101c0d18140d81c940309412450301d020803810844006800c0c0880089a85120440701405a4005e8441c1c0f10155000540c10400b151180094400000460310316140c10f0f000ba0418680c1612002403104070f40d4600b10900813468400401403401d02e06550503200040d604480c08064960240300194000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 813554208 1250 813552958 813552989
    0x3090604020a170607120e070e091504020d14030c010e01090c060c110402090310090b0703050c0a020a0b06130c08062103040510110d0c2117061c2109 66
    0xd40c0103c0001c50030006c42c240010307103161480003076481d10800364495201c021800d4207000852100303000340300340441e10380440306542c201a030114008950f20503001d00046411000303010555003e00440d40c040ca08000244240300540942d1402000c991000300d03201d1440c00c40c001205070080c500340d042e02e0b07042441d8018002c81c420a10005c1c0d405040d02d69410b000d02913070103002d0900d910070041002c0c01602c80614a1500c0385014085030f17806000e074601600180241d840d660f80c0050382010075030348600c65281c261540c40c0171030703204010310828104040c2011000b10041c0e500c1401680700d298202c3c2da60758410500344001c111030315004114012074108202c00e0019007030800700700d115014140391807188803000740203441c18182801da1010002d40e03540d690b102842a005c0101000d00045145000034902000e0b0240c5a0b0300050f5204005150500009140e075543d4001045640640041001005003501d0040d583d078583c0c41c0c8a0002c4d028010010190703d108061440546e4102107485104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 813555458 1250 813554208 813554221
    0x108040b1f1e080106091b0e0a030f0602030718080706084305090607030c140d170a0b01020a1401020c0703062a05092403090604020a1706 61
    0x60300c80246414054a40d92100000c03503441c84030740c0b18840302c0c0107600560002d050810391400c1d03500b5030740031a01841c140340c0304101d180450604002000740c20f082c050303158100c443c0800c4d01080141c6c00907000010620f58a000c0c403140e5001107100710469900c948803213440302445e800c620b01c24041c4000d50762060006211240c01160300d55002440d14960070017828507055003408544080361604100c8081c6107c2420403090030074100342c007480e80e05019040080b0040481c9050060704005020001005002c00501901c1910002080d24000c251031929544000c040c05120324580107034001750702c0f40e0004100000c1d5104134068104140c0c0a01282d040d140c90f80c04900e010106000c18179582008650102c034020451080110f00c18080410301050324201d11800100a44146040c1700c7c0e80701142c10000d51101c11103100050031211a00d410403070034048924006945840b000348840001030103001140000c450307200314170172602c10500b140c8580034030f04030100c1621855041d038004404250b6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 813556708 1250 813555458 813555481
    0x30c060926072105160f090509060f0c13031209090203010e01350c01080a02090d1502040b0304080c0c10080a2304031701080a02030a0f0804050909030a030b0108040b 73
    0x1020043e0700140003041451326510f0070407911251003180d84020100400690080225400050002c01801c020a03d085010a921440010600403558880a00060a0210407002d50304d0b442d90301c2208802058882c0340015010f120300d483c80c030104e0214080040c0300d030040d008503410303181e40b030307042d03111507407174000d12003850074202982403442c0c061200400403422100391000071540103c0d0042c080b600800d00007401050010b0000442a401042002d83c80d884181c0c00c500500c3c2d10290307001d40e40e044400702c13400074000c03a008100c400d0000024441806004000f07400c80340d00703800540301d100c1c40910422440d070035034030441c6000c2814900050074142055119040c0c000d4822140c01d0150241d07405510b110f5001c480460104000390b2440228010400c2c0d418050b0030103200901c1300e40e01d1600003c4d607541c0d0b1044010031800c400c908203800c00c900b080a0b00e004000141080ca190705029030501c0d2282c121442c54000207240810010381ea6209090713035030045800112041594450110008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 813557958 1250 813556708 813556739
    0x12030d05060612150f0108150108040206130f05030f0105070c080d0603060204060309060c2111040e010f0303020d050405011b060912020d0201061e06050a0207030c06092607 76
    0x65001c04280720f4a422840210101d510580d0b150111400ca20203110400091150543e00e807810813038001c0800150344403a0818851a40007424806082c1d0350f1440014030314411040901100000443d0000e00e40c82102d40f83c2003681e008405803441c0c1e0800c694501d0886034110b426400296000b540e590110b15524000e000e049022000410000d4803038644509030791050784000c0010313548010701814045144154000704c111460034a0b0300c0314424076134514010540200c031405a5070780714140003400800c000c442c0140311280728000c03a0740c0d4850f0a2840740d1a01c0c4420380142c000c80340d1043c0a180305200700e509a40c4161182260100000a0f454102084444c00c844d02562140c510021601c046488601e0811a5005015174000c4034002802d4420940c030101607544540840c0c840c1c41220a500c00540d41d0602d841d079243c2100b0b0104070300d00708865101800704080e4034000b04841c1e90014011382503800359031443c00310100d04480303011011104014a203c94129800a11a0820010121 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 813559208 1250 813557958 813557971
    0xd09060e0d080c190f0c02041a0f221508011409060a271410061e0305060c07020d0c231c11040b1314010b0307080a05040c0b0a0801080c12030d05 64
    0x100780580195004c182100d0217004100060031019081000c0c618000c07941d515968010380d241d40707481030a108440303200d2f1442034000c0049922580354169681e00812208000c2903100020300407911403003601f0600600590704043c1c24080e0400003240700105011360612031000408181c0042c0d1070405000d100c207882c031002c85106520450340c03110610704001b00e840300000c603000051214544615110401e12080050315800c1668004001040d0041006580401b402c1c4103955104010320004aa401400a00030041c140c036010115003c924035800d010340708403051001c45082c14140821428804980315003401703000068480d00014184200160340300c0c0c000e4000301c1e911000100040c0302440f060305680029584044114102012000c42801490242103803403941c1084040101210303401001c0e450f46a4030f640124003005458009140103000d80100715131a415a86001885450203100d031041c40e00c1104401c66182c80c00190609980e00b0400c0210b04d40b40e03550001501420004011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 813560458 1250 813559208 813559217
    0x9150c0c0b190e1e070f0b04090f0b060403030201140a1803030c02100f0b1305010617040c0b0a030203070311030c2a0a0507030510020f03010b0d09060e0d080c190f 72
    0x341a400040008240e00d910b4668484441d010100e016451701925074041e400403240d402d0b04103e4026104203d80a690244e44046411240e001ea0791004c0e2641c000e509800c010f000a0010038180d06501240f0100c00020020b0700940329040c1e0182640c4100c42c124865400c030b0301090300003038080c1c1e001025007403842c01130303c4036020840074800480303c1c00d0120003502034a800840300c0614018070003400040152004005070750410030010f001580c0f0090480380c2003440ea002c5000c0c40907030344d1600000c0a00d030b940155a05c0305540c1c01000b0390420b40305030000c2800e1030341111081c0004400c0e01d00c41c01e000303409141012082d1118112001001c80c045d80075184003942c1c480c1005040c00901c1015000e50001c1042e24514a41a46001c2110410075600c510500c800c00304004103500700c0381120780684405032592055082d0f0b80c01004118401465a40390040f48030070341038046917210042c01c43e6129400e0f265030303c0c0c500341014400c00c41c082d01e40007028a05003c005003e0b400c03010780c11600780340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 813561708 1250 813560458 813560471
    0x9040906060905130203100e0309101403010b04170c010e01051e030403030e100207020a0b030403180e0703230117070915140f0a06081909150c0c0b19 66
    0x500b042141c2080e185445044c031040075880c1541002c00010703050b840f0104007004a8034441e4811a12401000382540c401c1c0c8049148443c0a07200740301c48101e01d07100c184850703580d5a481040e907480d540188076460103218011560421201c000c11010b03241d04041e15606214075805004640d940e1000e07a104144a5610340800c0c80d40780310746c0185104900c43d80b0300146003d05030340245c5c80d001d02001191880707401048075400580310071169004032104107003241c3d102c2d1100d02d0280c2d4011111000c0f00c002d40801000020184a561003050282030661000c000741e941c00c0800c210a900344103c90b00f0440740d000c00401028021000310300c1101c0300d1009a8813155110705551007600c9214480340c500c103054001c00d0110b02142da001000a03407007200d0600e940d00c100c1011907041d07001e51185000b0310042000140b02808248510181d82c0f814203420803140050340fa1031356035100d490842c140310500d00220501c1c00c0340203086840d00250010046003565944502c490300042c41e4403490124640c6445 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 813562958 1250 813561708 813561719
    0x90501021f051905090a060525050a1202070f020f040c0c1122020705070b0c0a0311011e1b030203090316051513302006072001110904090606 62
    0xb2070517004c0c5500f0030140c464100c0030305021065840c043e240b07034258107060500700200c8100c00d0354400c42882d1401d2460702c2c0c102098054a00702250f184181219000207158001c00c04104582c032034070b500c00c64080101c000040700303000c1180e01c40c400b200080340032400d0020109260050308905900c1c02041d07040c000501c1d80500c150504001031098140d0b4020030300104014081c01000d002e04400b81c0c02c00e041144800e11169104054007001d818028010004020400e081d00b100030752210024039103404030320f50300616000342110b406042c07024001001e0411640d10038022070f40111045001141004410150004101600388003207819210b00311400d0712000c0301c43d18a81c442c61040346802098021820120f0070403001c4081e03101c29900b0900040c107040c2901032502c10031020742c50072848500a0003031042d100c05c69040c802000d840761404000c41c079a0301a43c14440e4042c01c01d40b00d810201c2c07011780682658410700c0b4415554805008031449410a9401704c06100e00070900810b4199407803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 813564208 1250 813562958 813562961
    0x1140c27150c0c04091505090a0503030c07031701050a0303180e0f0915160e01022401171c0f12050702060a1404052e060b0a090501021f0519 62
    0x2000d2101074400003140c0c03031100396410301000c900944251000d100c03000032a070b10845511540800303101c44580d25404101c80300c1b800c00c0105062540901141d54034100240d001c9904c3d00464800c90018001c0707030509480d40c92145045040354005045510458116601910f0b0420080720b90004441544800910030181c01482401450854204030140c245111694107000c643c44881c000d15039000203000e8002e440017108403170b1000d03520b04180b0303074400c3e000103c0c00c2c1920003c1d6090140c1c02c06040010780800017071054122205440c40c00800004801d0b1951100d20b0f04072007002c404501d0b0320034501d16020f810102c0f1000042e00d07060100c030130303100404003c598090b01c0400c01039002401304020020345100c1c4c0021044100840d11680c40d0075a40c0d103a40f60f60603030940003501c02029059600780440c51a89102800060091000701e0721040508541c0e0080a441d01c0003840d030305000a00d035400850300c840080041001080c0384030050425030701801025100814140c040c4140c440d190700036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 813565458 1250 813564208 813564229
    0x2070f03081e040f030b06030a03090521161706160f11011401060315030203070504020d090f0323031501030903210207060b0a1805100306060e060301140c27 69
    0x151101c030b05440f42507003410006c044004090a00991240e60400b02094006012008aa00407100c03000b01198804984400d010700d038100c666280f052449000315010b8050009003940c09d5000000c130744080407045a50b44050541c3c075a608100c04019500d0100e110b615440381030f00e0325040849080c43c0d4800c0047c2180c1d0030081000700700d0300c3e4000520081798103000788040c941e40165186002415230300065240c6203c5d00c210751190b940010485901e03559070300516031440d00a010300207000c0d030604024102a010111296903c0d405489521046211101350380c0240304884031884204800001980100000740742134080c8015404034be0080000590f0031103241d031541d0400358944410385884e0091383c41680321184152200d01040c407032001d04600c1200b1300d0f814080045660b85580c4094200e120103500040d10700741c00c0030000304d60036541d030210f02d01900d02900204810008406a50320509094402680e4010104280c0c1c0310b146071842c21040702070a540404003410513010000e80728590 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 813566708 1250 813565458 813565469
    0x1b12060f060c0d020d050307020d0302130506030907060906020303040b0402090403020c0604080106050909120f0703032a11060f18010e0d0e030f010b0f1e10030b0f0102070f03081e04 80
    0x4043d81d01900c4a506214850b80710b002030406504500382600040d4503103800c6485541019800700e04080c3c0101a000050300618024096690781c5c2042c0d8060303900c2d40114050040070401d2410005055031000040b2403013981c01038400400f0342c07295800c00c01030700070142c4140c0440c03141d0a800f0000740e68090082000f007900c4400001da562074207081c000c95a00090812000f0b81065120b01703082041101124000c07045060201d0360385205140039801003d0840b40b2445070f01310035005800d50b40e11910503400005c4d00d07494a0410f812400307800f95850008075440048500c00202203592910700c1450782c2c45031108800041440000004501c0c503019100245000041010a013180f0a040c284010302c0191014402881403c07100d030042801c1074000162240103400000310100742c6d802c0400140b10403540202030a54442c00e40000901510035490280d00c541400c5000b6011507000240345803c4404061440e00c20300d2454952100a030002c4144481d81c1234200300b900c68400500c80144040c0c007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 813567958 1250 813566708 813566713
    0x10206010f0f210210030b0411030105030d08061f050901120b0a09021b0625022107080d0203130605010b04030308150a0503060103081c11190e0d080309061b12060f060c 74
    0x1000e0208000d07540d000712005001c1072704000510083d200400c90388611a05401d004c0d00070b4485801040c600c85c0c6040c0d0010f855290600491005070b0b00c1001807030720b0402680c074240030480d1004418201d594034026039520031000301c1c040184980940281050f1603944000030601502c5400f100d041c40412201e0205140200300d000b0504203203d5425104052584000d11900c0314007030a03901005191040078a9a120100380c003010443c0800485419016120080d5102d05194419450305002e803d41101c1e09410a800070a6800703459040d101140d405039141545600c0760203529030f0840c41d1280b200c1c0c00000180e40458191020001750b80210b11803908a0b998100c40c4010303001d280441011400f0260401401815070030324001a12079030316030400c01d042c82c404000015038031130314003040700d07500030f00c1200942042c8051800070750f00c0b0742424000d40b159642e8a2908080386442010042c1d00100300380001d1164984200da1103900c000090700929100400c42c0c0060030301d0304a00070309200e56 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 813569208 1250 813567958 813567971
    0x151a121005300c03100902030a0206270618060310030203060720010216150e060c0702040b060c0604150f090f0510110904090c17010b010206010f0f21021003 69
    0x2c80749810003a40c040d000182000d5421640040d480320005425100705076141c12845055550a2090350000c0d64010040d80c1d40e1000102011206801d43c042409404800e000c0e910341d6080000031216019180c0c4030481d52903440c00c042104030341001d00300c00920805440d001c001a03d081001502031880f980710400c09420050001d0b8807585074012810569005020705074501c820001c5807002c0700e0b40407240d0f12a02d40541841d500500030000c180289105202c248003181c030355080207200190081d10b00b031102580d81003e001e407500c105008070120f03a010200250204115a2a03144456011080440d154a8022a00341510354111042d9082102c0500307080400c0b40420000a007141a0201401003c003140004c00b17aa0080c060064003c58a4ad0b4000c0b04105170100480083c14010316640d00e0f00d450100d400f0b0003001071760400c0340941b0a0340c00102703140341210140301c102d80719040d81d0400d0500f06411200300a4030340e401110303010325254a80d00161750303490140304161031036a0002000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 813570458 1250 813569208 813569269
    0xe010e0127020618040e0115050f010305010b04060302030405030412051614090a0509030c0105090c10020f0307110103060306180c052b03091206151a121005 69
    0x1200c10004840c0780281c1e04040c84016141d010580d051151031040840d42c07031039039501244c090130b60241108419440c24590b0a2241c0c6c3d1001c50205848050718100d0b4100c010a005400301c1d942030007030b40700404007480104800380c42a001160701500c100d0589040540d101d00f043c50400340440c0803940e640014181c0c0520500b140708410050114a8043c4c800580b0f01e404108500c501800c60200c080e101c0c400940810400c000f111a171034110380007000945040c50680341c030b071441002454410b034924130704d00c1c0d0400d100240741e4040d0303200600610710781201542e684a102d00700440160606446070000004540310b48180380d038180680035090744090042c40d0001c040303030113500039a20410000200100080c50a44000c1c200309044014640d042868101603450105590140c0d0040b645e01800b80204101d64100e007641e0300d502d01042d502107444108420460003480d240303044140040c0070302c001005040c04610741142130703001c15004041d2560f01241d100404c04000384c200b42c207000c3c0460f02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 813571708 1250 813570458 813570491
    0x609060a0603030e0d0309080f030702040e030c1b13020307020f0f0715031503051e21030609070e0a1d0f0403090b03040305093006010806190e010e01 66
    0x180400031103000c02105080d558040c1014150604d4107000e800c80942d03140030180107180c00e00c058464002122042e03603440f051140d90381e002c031004a0180c3e080070058100e0aa000056580030002d94001d02004c00340241c245070340e82080c1542ca54001000d40c2882c0c26a01c8610056000b02c103141d000c3c2c8019001054040d01e40194502d076403c040e40104030401c00341c4030131104000003e400346000f0480040100c441200c00210350000381c41c7c2d005401c0004490100e2251010107a00350506580240807050141c0008269a95902c054803104000180391131410281956102d6928141011501404000302d04981c0b00d1382c2082c0502d203100b0034014000380d4680c092641c45406140c54074428682554020100741d9184601901d00074080081420540507206651034440041e0103110b0350504044144018820150b030100d1110b10101050b09101d408030381c29058030700600c0100b40d1a1070b83c0c00b00c050041003068044d00b40c0780d5200e2000038100030030f014030f000a604180001c64800e0460b5640d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 813572958 1250 813571708 813571711
    0x311010f150e070207080c0402130801020c0102040326070b13210201060b0310050d0804031718011d0907030e120a030e0321070509090a0c030615080a050603120705060906 75
    0x1d0542d8084402042040d1b400540d03600c0d098015180541c860302c06084440313600806411070b580c554008a45144166415030280c411a802a070140429424007600e443e0300040b10001311103444030421418000c9400c08403110340103003800300007401030780450708c8810b5140810914100343d40309182540c200799609019103006010201d081031b00e0340c184a40c441049245070320840e8000c02410b0440024040c0070f109071401160481101c0c5039030501c00d40340c0c100c598000881803a440a64885a14055100c2c0c010b4604403031408101410030f804010810061410042aa0080503110403050800740342c14000300c0081c2e9440d40050381c840c1c121007400340568507010344808140d8018001414202c00b0701c08900907046002c10f803803406072210300040320f0501c61040042d03000a0761a0520203510404c0d4480e43c0007600d1990b00b00308854450011304450301624107210b0001e01c03007001045401000d54440364000100804440000c1d68041421600d81c20034081034900e90040020010003000501155 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 813574208 1250 813572958 813572971
    0x3100e06062d010c080c2a1f09030c1512060308070609140d120f05041208100b0a02030a0201060905240d0203160e0105060405210c041b0e06070b040311010f150e 71
    0x1f40d184c40b09400425180000d00f1044c4d440310100c2c54110200e980100d441c14060b58002c0d80d001071184d182d044680040ca008035004000586202c183c4004001d18486e81c0107990740498018a460429118140900202042038031150b94544481618a0f0f0030003401c01419a10388800003400358a0303685000700d585070f1420102d014200410400003d290401582411241d41003802850b156880d00c4903000e00a9040103040b6240013a155100360f0700080603083c40240e540c002c0c88807644480130300c0140c54050f18030140c40c020050b14543d10091a0204a4001d8006810250103000540000f1f160204408030100c01103c01001400145440342c0181d002d403d0580342c4a141a1808000c590b01c0d5a140c07030340030b07041c000074125418501c00c00d004075950100010700c140010600f84200d01521080d900707004000c030f00d018400c0c0c0c00c9410007805460305550080e0094109950720307101500d44000c481c0c2d54901030f560b10b160010a854040c03066404a080740081c00c40101c0c1420085c00028001400c403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 813575458 1250 813574208 813574273
    0x1090c09150506070609050d0507050f011512050f012c0106030b071d0a09150f0f0905100e04080a12050f061e03100e06062d010c080c 59
    0x810141d004005608100c0d5010742d003003541c50308242040c0c03000300040403000303042e070090041d410b811652040280210a02900035592444100c0880c81d0884000e50200507594042003010065440c1c00c8175a64040c501800035124185400c00d8202e017121070500c40000260300c030071100c0c403a960100c1c14080034020b60380020441d25003991030301440c550008220f141009101548400b0007200c0461404401502416141000741c07102c480380d01a007605c0744000c064613040d1200296080041d8034150440340c60070b0031120b8190410300b540026120040c1201c2184440c220006414408000058850360042c107580391200c2d5241d03402030981c0300201d94803202c0313814070b0240250b41e004550510f41100007211050003404402501d0640360581d610360719414065680b41c10701c0c01640d03070011041c4841c010150b900c103944070010400300340c0c06d207400c80090281c44400d40b403085008404c00c0800c000e050402418170001561020403640c44481e0303103034054105450000c0076405511032924485030b00d600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 813576708 1250 813575458 813575471
    0x90605192d05060a08010507020a030e0a050a031217010f080601060905090f0703110c0c03010c1b0308060d02040f09030806012a02060d0203160215040c05060d1103070201090c09 78
    0x140056644000d00c1c0501c801c550300d6011610300d0f40c0d41d201c40710080509000900141c948018065140c1e1000740007600410030210088085140803158101510340042c00e520740503042d42c4904054004020001c1c06100a52915581540c01400028000c1c01e414000c40c040380e003403010f264140303c010381c40b100c248040c600e000d211f91750f00c18180700d5200d040014030404035502d000c4100d024050b6000f40001c1e86000050603a0b5003280400c0b0007113a00360540090082499084044503400a01e69220211005201c00600003070f11502c5002d400880c02880c0000c85400c0350005002c40301e100c06000207480c0d9030b0384007604050b040081c4561045090070540140401c032051840d0350405200840805020310403640119030f02d603c107030b07202c800d02d81d0f60454581c41c000310106035030007261400601610603041c585065442648055100e9688a807801e85210b25000038800c081d001854001419503c0390441c01c000da038442c0146200b0072090b80081200845400d02c0c400c41c0101c0d400007040340e420b110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 813577958 1250 813576708 813576761
    0x5060108010c0513050d050c1003020d0e070303200c130f0b090121020604030605040609051504031205151027030206030610050c06190e06040f03050d09060519 70
    0x24129001c44001b81d4003201c0b035401c24074045d801c3c400150015039102c040c1000710381789503900d680601403592031404208295021000490707500c06052000400181c41c005162004540204420f5209005801120341034100c08000070403070080042c50303c5e00c0c560740c1e18222098003041d00619004010594291815506140c80c043d030031001070040074112115052110110340301d1504440c0250381008040001e13050629180c000303001c0c3d00c0c4c02034845110ba210b0b44104000b402074424003e031b91581307650080c200f0081d082000713007800800d9500b80c0814810841c895496003035482410303501c00d648980924242041c07503580c000494000002c4424031400030f1005072903a004482d04031000b03c43c003070303496026110f085541e489008500989809040e09101860b1485035101140080d002d4052100c03004032240c403640c03004211000b9150b4552800c5840200e8000c00c010050b0f100314072804220024203031030351002d568040d20250f00701d030785205004080e8a00c910481c4050711105614424070a1a42c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 813579208 1250 813577958 813577987
    0x218060102061620071715011503020d1404061107080f0306060403140c1c0506040f06020927010b070b010e0703090f230c030a060906060f0305060108010c05 69
    0x2c0c0f8440c826803102601c2d10505000300d035826920780c00e42030811092a80d810a076500e4040d144546008099594405503010001042413203034080c8103010814503030b191060100b501014440d2000a0507402c110f100305160b901d00416440340c1161989800b02e00745032030142c01701c1d002000c0708690044280117160000c1c0303d0390115803102807115406922602e0360000201c0030300c11a84001d14150703040e42078002c821008203110001e00000c0782e0305c1c122910000c174058210142100014550b42000f0002400942c01b12080341c16640101001818040d40d88041104407002100c03440300d0025015810f982010036015150150031180d101c2803d10440fa42e69114107441030250704410031a010000c0d2803603101c0d07400b8000709a040703010072042c05d899081400a00204405180c0840002d603003407000080009a001c4c1000c501800030308840c05241c442d40d0040c01d0300581207a03a0b0b6150f0100099800d102c61007940594081c0d005040039524100c0c60600715190240000240170080c4500b120210f0034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 813580458 1250 813579208 813579211
    0x60203061008070c020609033a0801030c05100e1203180d020a05012003070c0e070906020d0c080f21091603031110060b0c010c020604020d0204021b0303070804021806010206 76
    0x40d14850b032684040f00010b810004468904496260030221000302703400004c01c03400080e400013035584c001a06030713481102c2c0544c0900000d40350b00003115081006090030350b0801d848032603518104c40c43c500a5800212148803040300c141c01d40c0d201041034142040c0e41c603144250544125580da040d0000c0340d000c540852820b10450f0705008102c0701d1b007840e240c0c81c100d4103240b200c00036040d03907601c6443d8644a042c2e00054041c1c0f000c1c9560540010f0b207600d000b07400240603505c41d50005d126680c404003003110420109042121102c40911482c60040c7c0c060007d842038031009588100e00e803030048500f84c030b44013000b0070340d8006600032880024105511001c100c00d0301d030540b03001c1c0f101d07481c654101458031801c14107d4114601d890380004900324600060125454040020f001d040ea031288220780d00c840c19a401b82d440b84204603c08018502540140340c03440440a4180a06a0f4070100504581044410f1000710395030404000440c0b8002c45000318840c110395001c16a8140140000c3d642c510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 813581708 1250 813580458 813580463
    0x1f0e0c0a0e060625260c070b0f0918090d1803030e0d0b070804021003020f190c0c0306020a1403010617070201021b2a010c0609021c060203061008070c 66
    0x10400a4139411805100d10016400c110700540440b07032400d41008072104101c03100111110f00010000c01140d004c4a0b070718051600100315050402ca444d02da581e000240200c10400200412039240c0c417075698001102e0b03c1e13802182c03280e04d03221514a08203828284410304101303248625911800285842c0c005603909403074460900741429020410400e080400600411000f100304132400e42d004d0209071050b442074503294407446117a6015020f9010710034142e20412028480c00424000500c100c070030031415454095011002506c3e0564942420740040c0d5079150001015503c4581095043c0c06038041440100d140d503141070740050070043c6161094203182c5801001c41c0e2120b100350150751038800041070000e40100c040c08119903c00080c104c541c0f4280c0c0e1082c00c2d50801c401c030742c4590000e00741a110b2a452001d581e549100a10041c5012a80300001c0c07560000003032408084504a180701d024016901d04049082054032401c642070f10041180716006c006c0c5055120384a582d6656 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 813582958 1250 813581708 813581719
    0x3010b0a09050709120803090d1806261611070506070602070f060204060e0906041a0918150a0f060b0f0d060b030a14010603110702060a021f0e0c0a0e06 67
    0x4039200021204809503600555804002c440380400f401007003401980180070650403150807110070342e010b4410078049020f00c1c02000300d1040070040c4074001c40060cc00da0b8054180302940006000d01d50f00320785400d035000b5115001c1e54003d804402c0d0444000c440041c51940100b0b80189810005240b922440b280280348036000f092160030000f01140341d08a484d031200040d0348503a00c40200030300008030003121911402c007410115600d800e0034450400350300c90707021017100070001d80030a1040d42e40d4054405801045c041c00d0f60100d00005002850211f00314080031440c604103003503528151180d500444001d07914040c41000415020403c40700024010070031643c072581061043e00c001c04480d031082400305800010001c0c200001c0c0c0c0403d203d00c51040f0401880e90729101304a08850a03403082250b00481080a4400340c0b424101810940500e88125a100c0d1f580c2204002c0400181e40801140b6071200c0901190b9103040c005c00583d24015980c0000c0189003001000f011500a40005c2c001c1c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 813584208 1250 813582958 813582961
    0x6010b03040b1602011d0102031f051e130c03050412020f06011403150f0132040f020c19050715021902040209060a0e090a0902012f16080c03010b0a0905 67
    0x143c000e4010003180000903400000860346d05441d94081d50081706c50000d0f5000a00710303540c0a09925800100399400a0320395402d0428080c9440da00500c84c80c0701552114180d541102c1c1c0365041d0040001210442c1d401044500b00351130615022000c4501d914150b4120241c4607599a0001420a04543d08031400e5501202c1e10400b19091007220750208010707042d041e0400c841080b44588650484c1c44169021402d00340b103a6043c1c40540e4403e902039001c15080d00850040e08e082e8000d12800342c10402e0040ca4000c0540c1018030780003894514000d1491500301680078000f003030000c41c0003404a52401d0100121140000b902e0b44c61126501090306020102e034001d548460b4195600301c64058201075030391603030900160403000da207107106110304070500000c0d40181c102e0052444d41c0d0360603190302d16140d5080100362111044500800e41034070368068001e8009004110070103100410b1800100d5503420301c2d000ba4209101c2800c280d0082c1e0508600001d19101c0406c444101d81c01200300046a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 813585458 1250 813584208 813584251
    0xc1409060f070c080a020405131208060120061609080a0b070e090a140705090d0206030a0204080619060f0308160f0203030a0c03090509130209150411310b0c0f0609030c06010b03040b 80
    0x55410300002c0c203b000c0410f02002440c03c00162003070043e104113246161003404a00202c031008154095401e060700864004000148e020705075a401c007041e8140710f0303405080b03c40481c080020071102d8040c1d082d150401c89a6201c18011001c0e0401d6651500a2415041c100800c6605025210080c0a44800400141c0040301641a10041c10301d08055941500b044003039402040600d050f0855014502140010003814180b241030440354401d82903814040084194108821181000c3e11480e00e00308a07000140c0d0140010f194042c2c2c561035a1240810509000709601c0554205a000e04000701c140441030800b211548042c80d07044528030440e581d090f40042c0302070702c031032000c0740c0107800e20300440c0501c3c2050b07010702104041d01200d02000e9400d1450a4401900705101c0300036564540c5050148041850042c0010b0410340308a950340d210b00c60805291107800c032800c40e400c0d000030400140c4001c0c280301d02801442d4071a5054210f003044c0d00e0b4000c001201070840c8044c60000c805080c1e1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 813586708 1250 813585458 813585467
    0xb04110405281116021216171e0304090b0306010503190812010b0a11010203130816020a14090907030503030a090f150f0c1409060f070c080a0204051312080601 70
    0x2501d40480c3c411510341191000200c682068a81d0481c8180030342a4003510703800e00010401da02400c1c1c070050f04c5c075803807034003000c2c0c0101c901c4200c00c0c00b014000c11031003807210344404409200084802d40210f0351140340c00603800840b0341480850b4882e030070402c01006140d9000419800b44c0c0c10ba400540c000202529040c880ea05c42c00c40c1007034940a107000000b46a11481c00642a08101f5490394110010b520360958201c0c40102c50000d01c0c000c2441108001c118403002038945024a944c03240c1d8038064680014050501d240e001001c4d00300390130307501c4299060046000b5000360a103c0107080490039552010f40b00d000062407415402d035030b200c801d804e001e5040b4100882c2500081c8810207680a1141e030006800684003070000300d41007441c000080d920a25460b448030712803540807828080078000f0402180c1c4006c106803800d03a003d104207008200421445c0c0300401042c002054460f106205120a80d40010301e40e0b29071485004a10300418519440420001c82d10720b8007041c0e41d554400180d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 813587958 1250 813586708 813586721
    0xa0c090e030a0905060d0b0a03080703030c030536033606070f020a1809210c03080c090312121b04090519020310050102070510021c0504120b0411040528 67
    0x180d002005c108d0000070700c03040358010f002c10b03070103079600f401500240482981581c0054801d844080b241c0201903800302d40c11400d40d80003280b40c90b681802000b40103181c510715000300342a4031078280303800f11540240c958541031440381d08801103c02108900320000034114003400c44054034141c0c5200060381190741c0d1820340c1d000f411031041181d6000c81c003048940000d02000300211020415244144201c2d510004094031401143c0d483c2808101c1c182d07400c41e640500900840c0c5100000d1110300c03c5a40d00313000c07141c6a44810340302680c4500c3c2c10306201040082c094180410040b07012600c6a64842040480381910140300000c695a1900c07007542d880009403484001c942e074404030034001c0b101c81c0070b81c180c811103000764210340c180c0307440f01e04100000c0804903003030307000d684407191040060006110078440304006061007030a207541c802412000d0800c8400440700c2403100410002088184920f5501c007035000d07a82044a0324040d0a0046100c4240445400b5260101c1c0c4660549200340c0113030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 813589208 1250 813587958 813587981
    0x4050603090316060f0e010603050618010608011d15070509041d0115050312030609040b040203211903020a1706030703081209070e040f1101110a0c090e030a0905060d 73
    0x1c3c07454006424554010035541c041c180f03200341461480029200140258402c0c2c039007190203406141c0b5901c0b001548014441800302e50b03952512070016035102d0a108100d6406150388010b0b00818081c484c0030b0801002e2031190700304032003400503c04140d034003e082d04d102d410b066900051300081c907a0101d054003120059003a05608000000325a401050800401c840c016403c40d035540119404580a1740000c485840d0040201700c001808070b11001449500180083d0907030383d00341890614450000040b144000800f40c000a0b801e000c841c05a420b038401100d40e01d02103041504840d40141944c032200d20618002c051500810540c6e9400d001950085a201644503070f107018450144080150031034020031340d805800d80019400201c0e040d03203441280e0000705030001201c650b580101c00c403001d6803614104880088030081c8420204011240705000d0080d4001807860009607030107555181d411984680c000340188001c3c0754114044030141c600c1191b00c151600d1010100200400d04160b10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 813590458 1250 813589208 813589237
    0x1b0e060412031b1e0201020f03070b0f0a0212040b250516240e1203010f03060c0201110f2205010c0b2203090801140c03040b420312040506030903 64
    0x21040101e0460310003150a9201fa000c0c0ca00318880d0080705902e0b07000f0104041c001c41c108800041c5010070b05201c507070b44051400c000600301121010807011459048900307c0307120032002e0a0000440585041140c0006841c41000307828405a0b030051141c0070311801c070b080609040c00c481c2c080000031410f03902c07c54101c10340f00a00300406c4001001030510503003032035414041c003003554199901010807641602c041c52a01c00c03580745580d58030402070207000f0440c41107559030b4031700a00d4000d01ca070080038019a1003084e161a03104030b034559160307404000702012050144010400107039800c050544000340e0041a800156070301d114201000312503414006005084048039041010341080e10002500d8410000b0843c0d0784041c0c01c0c1c01c6040c101919036211008086c800600000e4500c480780c2d52102401150b442549643e0500b441c0051f001c00740c0a605900c0f22004000440030740504103035040c0114024054414201c4640e6818407030341c00703424011600000010f1000c607007001210103c640e103184 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 813591708 1250 813590458 813590483
    0x20301050c040612060f1a090301060311030606100e0415050904080304122c040b090a020c0d030b130b0d0b04030302130605180f0a0302041b0e060412031b 68
    0x40c0860755502c9400707900c01081e200c00c60108003024038403a42c02540c11217039800c0204c1e401c200304101d41404400c0700c509503040400000c6402d4400b800b0b50b4005606c105400b49401c248582003604188005100d20b0043c600615107070400356100c035082c0e040e4141a600026100d04c1d40d60241040c40c40e6400407508030f1940c0003030004000421005610540c02241e201d10049009030048944200751039056081c40841600050291154071000306880c200901c002031607441e480101300104821524502825030206412203030b8042817205000303071091441c040210000880000f00b01c900300250303a4034080e940b44060010b80d107401c84003101494004601030007524080c90300401941c03040443c0350b03980c5401400020b0b418040c00544c0c00c0c0004c00e101c202c1c01d012010301484408011006110340c0404ea4150020150f121841640c0032000d07880c00700d6a0718844004042c100180f05202d0500880040008005113005103102d5807803a541860700f034503070290041c00c10f500d12003400000362040c204c021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 813592958 1250 813591708 813591721
    0x20909030d090b0702010b01021902011d10020109030f03020405060d0b0406080a060204031209030f060e122d03010b0d050408192001021e070507320f011209030c02030105 75
    0x100703184100c0d405c0e4001c1c8212400c5600482c0c450040170342405a8041c2d903500d02d00107601800142d4460241380084200c5804c41d030f030000700c181d02203800140c0581d41d15500c2d60181a80018840340e000440d04041d4034027450a070200c0d02a00c2450344031764031196604961001960780ea04683d00405185040300d1014015062a01c020343c07044c4000c89940140070b603610030f824060007406040300c0d040103c071181a2800d844040c0946581a03200b0440c1c05144491510360440744064480007492510202c641182c00017040c0420001c90307100c8180130003d20041001452450403a000442c4034800841d4a03141c43ca80800540520440c4d01202d606040c4486052030707000c80854803c440000f10180c20f5110380103510b00700d01c5540f01140d5190008001c008103510410700030b100300352103482200e450f030b075a4640c070030010004846055460704e00b051006c02c00350342602e11307200c0d00034080740d0b940c900fa0303107690001e0b225544198108809648411806040c540104041140c007500030f8000d021504c2d000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 813594208 1250 813592958 813592973
    0x61b060606090e070e060f16020a1502010e01020f0f0c15150f04050702030904110f07050120040f030201080a021306111006120305030c07120e0f0d0b04020909030d09 73
    0x1030140240740c1c880701001920807407189062179000540988010f18018550384c452040c2d60119031417180c1045079410150058a50200c01002429480105881c00c0d030300040c000d082d121007401e00101a8014884511490402c0c2c04440004030b0b04422180e43e240d200e0030940c10680c3d144208082e04d280c640804c0242c0c250582d01041c1510115191048100c10034100011181c040e1002d80060b8814020810542003a80c000d4400702200c40b28503041090312001c00c1c02a610004080340c0694648480c081980400580881e4001c05081c100342014100385103a40c4460306ca01c070282c1044071480108008d110103604170f904100c8080400885180c0702c4001620f005103010210310184a40900070398000e20750300c900c1c0c0603249803d8100704180a01d8400311b4094201504445480d02c0c00c200c01c01c0000d429850314031302d4176240c0e180d9469500500c002c0006458100e40d54502401d140d50300880010290800d803607200758102c4140c04941c441401c0e0b940f0354003440303000d008150315140c000340620521 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 813595458 1250 813594208 813594227
    0x70813051c261b1e0a050a0809031303060506010c0803040f0c080601030b191d2a0f0906040b031510051f0c080c012405060406050a030531051e07061b060606 69
    0x15912031708c0080e10350300606070b500d104070400311426410020f000e000280c01e94111070740060051502c00c242ca03210f41c85208499000f91001c42d04545070706010302c02c01158002030002082941d0203042d02d580755456041007000c00616481c118000e084484007038230740075803043c050040a1400304a600002c504080d6580c0300052030b9641d583c00d03484d411010722100a5102080c80000381c40242c1c2088040d007031204c2c0385406000c042d4020f4a5031091040c40d01d041000110715108440c1c03a083c10b061440da140441c48a94205500554200c070721750701d07c80350903280c4c059420980e290520038411541030280580c02005420402c035402c00018905501c3c60313480307484908071608a40c0101f25502c204000440c0b040e441140c002c131700144200114280203621043d840204000020010b029030500140c2546168a00451203100d9401801c113206040003190041d207482c02150082d600c094426a943c1c10151055004008402215401d0000c1d02811001015400b00082c0105502c3d002c1c0904000c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 813596708 1250 813595458 813595477
    0x1505070e0406060c0f0f02090405030d05130201090302090619180e010209150310081e1501060e0607020a08030a0305040515070813051c261b1e0a05 65
    0xc4091001568581440303118100c030b0389078075040c1c0c0b1403507075a99080002c1e92107101601d1a0446480800140e1103400300c15110318801c0700a540d5a1a0602440d811030740051300684985c00f0510b18100140d0b00030b00300380140c03038048404610301c1c6e0761400040d8500c520032906007040c0161030390001c0e04200d40d695011201124060038840040c1241180d8201d018503580f0343e07845644c40300c03866010224031000b140c04c441e01070489520710303441d80c840b103150405a5050515807141502e020111090500851400c1075007400c0e004072652521100820001c23940c02503500c10000014906c6c210755801c60320400400000061b030b0303100d9103100d40250090201b180c0954850203980b6142e012603010340c40043c4220842d442d0300c0580e407aa610140c0c881c0401c00400c85031442081008450140d00c4422038035800655680e12203000d440b01b25034009808107142d81d10801c0314510078000c0400d02d1401500c07240d00c9106c0c0c0e50b9213500001d01c0d0190500002c070500403048400080c2c0700074450b4442c0c010000c0c000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 813597958 1250 813596708 813596717
    0x501050f01020a0c03030f0903050f100605120d05030a02091905030d050a05041404020708030f0a15030201050405040506060415080406050f09060402010f140a0302030906090a03051204050a150507 86
    0x14500e03401680c0300c2112a100500c0984803035028000280103864060310341145140040074262260b84a9142a880040c400c8995000401014a540003402041c001d04025901c61113420f44a506a980e6012010702003000c0c48000b00008031107a0307071a0705846000b800200031040314100e00e007011004032528061030340240590415002c2950180701101c0c0083c06583c0c80614103441c2125004906000814070740d88a5000c11480d00404d410301c003d1809040b06481d0010b103800c10394201d204645403d550200d03c00115501040943e80041c180c070b08a40341074030301092590301e00000840314841c0d47c000203110311550280d1030001d070b40100e406128070320400c0c041043d40c80e1303810400008041111400c800b41e001c1000240194440e218002c100706042c280310000d0701f200208100750790810b0880c200069408810010719002c03c111854111001201a02d00b07450243c400030007622a113420a01142c1078040441c1c01c0040401c010042690066820380c1d901a001031084040c0000752207140016 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 813599208 1250 813597958 813597979
    0x60801060603050f013005010213090b0f0402071a090307030f050403231c020c0307050a0506070201051806071203050601090e012304020f0a0f0e0f121e01050105 71
    0x354042c0c03042c3d500800d07525241e540160301e40304503070500941c401d0404804c00100c00d0442074211420007611a000d100340000360325561460880c401c110401d602032000c485c10b1040550042d02c4082955503009400d980c09a43c0318003504195400114005145414500c400c081000c00013011028001e991700c25a070f0b10600a80716030b0b00301e1751070090740005424407225540032460365020310518900000c548003540d4050103105003070091340340301002642c00750300001403102080c035041c01402c1c05004212a9920034904140100f00c1c0c0b809080c100a060003000210500c1c40d100584c503501048600409180d560b18440c50308030300c0304080300c0300f0b8030119003048089102356010700d16000586007a40d032440000d0f032030455002d080303110585a45011307000c81c60004a4a171143e000801c0303c00c101c28910340e99007140030340003014071100320b080104100300c000340704246666864285d441c500c022075541e070380040d049a600741003d6151600c2d41504152400300343c42e900c81904158102c86080716200d150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 813600458 1250 813599208 813599219
    0xc14160b1306081f03050f0f01050f011202030715030b0103050606030609060402030a0906090b06091f031b0b030f040219050303030a0e0f030301090609060b09031009022206080106 79
    0x89008030700318001102450501801a18030540c4440d500c03030240640f8072a00c19070303a60f03a012204401d0304103441d150040102001c0c2d2510410900a62404c0b940080006207010611003140d650103002351005075003040100710030f540c4c0c1000707582d0260011265015040c2c50144020f030041503540078503408a8100000602a807610a0540344100c0300903200b046182d550a08000c0290f00003000348030800d990340310313400209a0b14444e5980c01480b6902c44080c5041c41000c100e85000000c02d842c00e04010b119600c04499040306509007240d5100003103e07003110201d82641c5d08003001d50410410342c00b001c0100000800b8002d046401140203030f9440341820034807001c2c2900320100e4041e0301c1d0182d00c03c00126042e074000d648140c282014417420b0b690050307540c200c03031810b40e4402c2e8050100103071609001c3c40b202c2c1161007210020804684420300e8403040c000402d4480d0840e80d04040781e1a80c490404056441d1508031001240c3e034003454544e03201d074030403811000b040c113401580d0b100e40c60038030701085 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 813601708 1250 813600458 813600479
    0x270c0c0c242b0e10050402060d0213080c09160507150c0e0a050306090304060e1c12020606010e130f270302010510031e1103120406030c0e011e0c1416 66
    0x1080102c1ca0f000e03181d03031000398aa510140402400c00c9801400812229016540a1000e050006400280181818641308046107002d058407085440b40714040c0030b20594400000380850050030909041d911401241030103d0300300d0503010300d0b0131120305100a004d40b0b03075400302e0f80c0e400c1c0740011a403828095449006041c0c0e219000c035610752560f44108411701c4410f01074580c645284500409109804c00107044100e4500e034001d1040310b80d02d102c5040c0250796501800060b074002400e190070390810404200060764943d180030010801940d0b49000f13828040560490525004110002c00c3d10900c402e070400749070320108000340c0040d403800011034140e100e18039100302101d801903802201c02000c0315085541d030100c0e000450301c0c5c14840d40350410540741400414003000701c90341c911f61100c0c5007480c060284d4543c480c0040807c004d60980f01016a0400b10640401c0310600b40d0480070002503100303440700c2001000190520185148444038445e000400700c3c20940600300e11082d0613503c1c4424103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 813602958 1250 813601708 813601721
    0x117160e06040b12070801020913050402010f081f0e1e0105370f031101020a02130c03091406010f0503061608040f02270c0c0c242b 58
    0x1201400c0d440e010032607a1915820100c02d03908000e081521448040807010300c0c1180d1540081000e075000b080440643c54980444283c1c80843c1c3d03030600c09494154002000100700c0114001440130850100300305601e9090449860040c40c4c105000b1a0384076680055210011108100d15209412051010200b0345130818100e4002a1810f8040440706502000d40700ca4941e001c01c500881440e81142d01c8120f68002d0028030b00b900660034642d065080c01000104134101d91415503128814090058880d10b0f51404090710000000940d00c1e100c401c03c03800f0f8441260083c12070850340c0000d0380d00c43e2001c16024100c503004401103074810354407010702d501c1d550304907054038a0207076103100c4a030981d00400d16203511520902200159050b81d900154440c2c07040340d540c40e00940d90b55042c04011000c8147c20707401424008940e07081520b16080e49503110707813152a00c0e000d98030b1608400300c5890b40700da540d02c003213030003840064407801480112006090360002e8450642074041c0000241000b500c07402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 813604208 1250 813602958 813602969
    0x170315030f032b0908041e0b121b09040f0506040b04090b010b031911070302151b07050111030c071115030708060d1b030510050105030312041505011716 67
    0x3e010040750300e031003a4980d5184826038010a0b2100a44400100713403200900c090071041e800d41c01c10f040079504030390301103180d90401400d000d41009840d20084d0815039656028403580702444681114905007103203401180c2007a500681081d14104004806405c0a84202c0d4150f034100b06509041c810441a110921000340000c1e4241c0d0040c88001c4001d002150305c0400712203003101a0340000700d280704131500340350460342d17000340030504c0d10402d541803010020717801e4981c140341c880d4240f28401601007126248400b1000c200050004100503007034200c403108440b1074003d9601d900c0c125405503c254401c40c812105e1a014503910105450040700d00c0c075800741c01030092411580d40c408140e03206a07002d0011507002800144490000b0002c0e0722014100b500c2e0071200940900d586070403071810310b80e20803038000035041c480180000e85000040d149281900040c0300c940b074642c1d00b0710f50304074084104446a01400c0000108070041c4076078030800b02c1030510007101c191140c0c0c464404480c1381c0394001c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 813605458 1250 813604208 813604237
    0x150a02040f170a02090720060601020304181404030c0b070203030c0304030c030309020a06120b1203070602090a0b0301090b0a08160620060a06260316170315030f03 72
    0x240310100c20300441000d544900303401c40f0f032403075a1a000101107500444018000414a2100c0d81088981403065005000c10b200140f4843c105240040e46900a5006601840c06138a00d6240882c10540002d800041040c0220000741014203000f482050440801d80d080704010000c01c440c3d52001003144e1081c0b61039141c5a080d5100c560302100c0301d030b4030102c00f41c04040d181c000000159031943c2c80c030b02c002e0407140ca0340100003035a000d00d00191642c0240032031103803103980503507060844003104a9101130780c880c10040e959060f00780003c005580369041001050800300011407811500d5000d568070307110403103c12406541e5000c2c010703070f60595860340a110044004d420003c981c0640826000404101c200400e5130007510301c107500d0404e04880c000c0100382c840904101d140304a400030401080d10a080c015035185243c045680d91080c0c804589400224003403900c28481241030400300042c0b40c02015075070341000101c1e502c4966a015900e0f10034043e00300c1d01d9090b00400001c403031024031250741 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 813606708 1250 813605458 813605489
    0x20721020706080f0402130605101d0a03050703080304060204121b090b0d020d170a0e04050906092104050d0807021e0307060c06090b07021e01060b030f0604110c150a0204 75
    0x28003424070b101d840c04001f0251140008070306e598902070440030800c200c1c1d90350a0000744c407402051040c80000c04017400340580400c1032002c036201044180940e500140a5a902c0c1c87d6442c214000384103ea000c0741e80458800089403c102d0200606800329001d100389000c0300b611211000100e0380c036a032502c0d910070582c1030030030014104050300c0440c1e81d0241c01600f007110304804802003107912034100c68000070150550b01c001c0c1c0c541881000d41200562008001614111004960343c2c9401c1103845521100068500c6101c80d03030504680243c04060700d141d501105034642401c19400200d0120322a001140c0f11103212403009403030003a000ea00600030070005181280c01c1e07551182194098400c561924006000b0410b60146203006100c1daa00804203801091029030313551642c0e07880b00700c1e540d041c80000c10910f0381c64401d83e60000041c0d6420711294484000040c01844000c03a480981d0901062400c00341c0c40c0401c40400d01c1000030f49100495841c1c10b0850100e10550007010500701c0c0f0a038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 813607958 1250 813606708 813606713
    0x1021020d05010e061e1312201002070302011407140705030d1b1e052a061504180816020604030c090506211f020721020706080f04 57
    0x4030101032581c000c41c0001440b000106509003005000c80740080c46a440307018621010415213041a400344400c012448400d509a98404440003400a032000b04030480480c50403922030440c00800e05203a290071650801290100200603411a01c07081d40507510303040b01400702010610499115100c5a69030241d07101d22241e40030780c2da81280b070003176500344070500c006c0c21204d400c2d2040c0040345038040c00d410041820038900811105040c1013001c481c082e01701c0128000e41e000001d4401c040d007c60054503460800d00c0da040415140184214024494003007031002000105101c0001c45100b520207000001c2220003003420400d800400802d1400c0802141c5407074000c0b5042c1800e050306c02004180303070942c0e0342c8070b0a1000015400c4614031b541c0d50710038001c3c0e9191010070b8154629080c40020b03940c11410200036100c1c45240b01da0107250584a4408880b0240e90381142c1c40303d5448840154200154404110f90500401c55a00544203030300e808107005014884040c4200c421140c20655542c459 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 813609208 1250 813607958 813607969
    0x12020c100f02011107050a0b060a0609050d1a100305060709030f0b090705060d1506110a020f12010906060302030c0402120c0901140c0d080a0b0607110a091103102102 73
    0x1005040440d580c415404981d40b00d400005c1a51a0041c8000e03c4034080d01d0800498403803024040a10030b02d00e02d5420018207403c11001011100105c0e081c01482d42c0741c2c24070340c0c0c0200d0204c0d060b000b800000d104112600740310494880650740600c0403641e082d9190f0000b91155002c0b80809404440103032076500019100c0c0d1085a0301c00c02003000d49001c0d41e90781002c1402c0da0040c0d8042c4440703d450300c0002c0032071568503ea07400204454608140400d526201a03611115548030103401010440f80500094542600649254801d400200546180c90400f40018180ea0108034400d00a1021b4500b252030540292058001c2000703080616455a644980c41070303000c0e11180d414040e00d40b0a5095a00d90400600311091754032018100040390b540009240e013000070800b902032860200da4080ca51520825140029440000036104a04c0c6000064402c50030754000380b212410601c0e445400c0740c01e0b0700a9802201c4205840c0e81840d01c81340034003402c2d081c01c0034410090022090a00152810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 813610458 1250 813609208 813609227
    0x304180e011401061106090a020604090b0d0b01080703060b040e07060f021609050f250507060e011a0102060a06060c02090406140106021b0103020304080a11071d0412020c10 76
    0x18100001a94440c59805110408090713100d075001c102ca2244e10340c410081032001543c03004c151000340c02440b030ba40c0c0c0020828050b9005040e01213030380c1c4402c841e072501e404c4000100c550300504c1d200070760b42c0e607984030303690318442800308a4000d030070320107850500d003460302801d85a0000d0760068a0114200a070440e21071052034032800451061806220b044210154210094031825001140c1450800d41106c81b01001510200b404126001c4600c42078001e1048051403d81514140c0e951b003c1d642409406030003942c40110040d40303841e141a0b52034880c01c01400e04200281c09456003661015069001c446043c031440e004245c1c03030b00b90380b00185000545264041d220320700c005010800c0900c0741803007a01c260071180241c1d1242c54000f8110790400c80c9111000d40900c0d00350301c0c43c0ba0564884020703000b51449101408080303200442c00d440188200000381a00c503022001d1101502250228004d00b52016913101030f050540401d02840400e1149102101804940c0d030611040030855030380e011b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 813611708 1250 813610458 813610481
    0x90a0902030a1505040c0b0715020f0405060f0702040c0c0f0f1a04030201140108011104052418010813080a0c020307050a08100c02150109020706020f03040f1103030418 74
    0x14002803000001c0d07060b584568000d00c10040007505103454501400b0010140e00000d4947d0418014080001c40241d003001480d00e03070301400361f2100c90400301c0540740c4c001d5800003a48000c02040b01d20065910b0f07409091814001c4905226a0710340032020f6840b520f14140280c5503481c4c43c840c0001050075810300b040b03003034480c0b08031010018210412225003034040d5421001030351902c40340d205024074008500e0241012100030000407600e080a0342d010700c250b104581c040c1c01300002c0c501c4a98015000d00c200190f07041c202c6591503810580c2030b021401c088485a001c034600e0f00109441c00e00032003a03071101c950b202100900d003a040c3c0c2c400380e42c07401d0302007001ca904d0b1142441c0400c450701d0340b40748403004150080080c00b032100f1003c0d080c42554000d0310043c0466201c110282c0c1154465400181107801c188801070351200309007050070117481102c0740d08080e102c001060104008105100d02e0b4168007070382c085075603000300c1410181c41e4420b9102e142940c0c03501d60346040703c442c199444801d9952 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 813612958 1250 813611708 813611713
    0x330103080d0e0a06061d06030615010315030813060915050a3911040506010e09040503190e040c0305060a09020c070f09020c0f0c0307090c0302121f14090a090203 71
    0x81c50356030b0034003585c0c0d40350001064529a404905404940e10780000c0c0c1108085014014920785a80e900300c0b440c580071400c1d03042540300c0300c040a5136070801840304081c51308090300b82d035640310a41507946115624414240001c03500794000451100886513110120030390f5403240e04c2d020b20719500326494125801d01165140c11110010848070031038003e0228001c03403000c0603483c1d031850f0038400d403800c10100e40315005c0d906210402031103a81c0a455800b5211013181c0c0f40c0f2041e05c85003003080c914011031205040341c44803003a002100030303040810582122004c031380900c1021449a411400d4860503540e080e00124912700500c4600001d03005480e25410f184122500e01e40d90b024072944059942d4070100849a0000d0080348505060103e043c800c51804000c010045075900480e030b0b507070200e1007100c0d10329550307a503030741c400a01c69012100c2c00f43c030000c80d0800b41d0070003100b4580e040e003800d00340601c2c00329810740019403840180b0700c1e6840c84c4030040494016070740d405820000380075000d01c101d9060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 813614208 1250 813612958 813612973
    0xd020a0b070e041d0606040605330c030d05011404151a0f0d050f061005090d03171006180807050d0c180225020d0221330103080d0e 58
    0x4484c2c2a8040010407070080003009141800d80902044030072981166010350100f40d404035080c0c16104050042c60703910011190408800f81c200e0340140a8620b022940d070000241c48810214550030640c181d580c0344000c6440044150200401c441090b0700c000c0c2c078200300e000104950003260050101040e880424103282070584401820540d01000c1c4082e98255100c042c1704071540420386050b405002500d10058001d48100c01510368010401c815204e039400c60304201c1018854000401007124070420786003541401c1441c00503400b002d000740c0740040c1d00c400d01100c0d1406180307812811506003030f020305140380c1440b00740018000b00c12016109060764020009100d02504150f082c006220140140c58400400300801c0c604004102c411640030319001501c05a82c0e00c1030341251040c0d044441c0d100c1192200c00f420340118645000d001c65004003984800c3c000e0781c81000c02e0310004401c8140c403246a0f41400305000300b80a0102820010040c0495034114515902400040340d1000c12103859 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 813615458 1250 813614208 813614231
    0x901081f1707090b100212090f06030a020a14031311060c030f031f0501120b040905061e0a050408040510030605060a031a0307061209021c0609050d020a0b070e04 71
    0x31101d20210005140d02c2220100060f11461003008141c40d81114804c2000c01d418100968640f0790004107464850002500041c0c4d5071151441d101c81d0700040e01264491400e111008d00039007000b003101c07007c26036490469040d14404c1007241c0c40f4140c03060f0800d11800e0140c44404021050000b80c0707411900030000c45c855000100013070840c0c605003100841da24900040c0500141d2200c40c0410100049200309211582e080030f010389001c40c60701c0d030004000d21580d000901814110b00c000d8040d00400c014040e58001d0f56151040c909050701c165070b5036880e141000c8046402c1101e016188250602c070900c05841c0580c4500a40d070368a240108216032910005151075100c1c54692002c242d403003001c1d5000911501e280b64040400310050141e0624103040075100d001450f030026603444d980c0003414119aa4056908800256a00d0203100881245014002440001030640c1c040c46040003850b07003103100045001a1a0f44200494080e4403484c0c400d690b0ec40c5134010751035010340c4805000c0d40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 813616708 1250 813615458 813615479
    0x10c0b0a270b01150512010902030a0b10080714030402060904020c03040e0c07120203090d08091909020c0601050915040906060e130308060105090a1e0f030f05060c0901081f 76
    0x44081c0034148054081d450b00300b404c0c0070740f02c040302d900082c41821b1100360200460b044125044030485800507a0780d58031800c24000600e41c44c241c10380d00118524080210031f501c1040c8901c9004262981c0005558186960349940000c4a0080d031005003000208000d041c1500075001d850008400c030303400d0a4603124501004171086880880f03100d000301d07445003400003056090360101958009945405113000101e9000310500201801c0c18800203000b030302c0c507203c1c2000c00d200084100c01000415440d440c0d9940a50f10240107852a0310031403001003014a8030300e480c0c40c01000c0c0219081100c40071502400701030a804501030302e800da592080042c80e6540302c400d01e881080c00b401c1e241c0541c030b100d1902400120020309032130304208040c032004a49445014400050741c10b11000403600e00c121a007260100702d001d4000041c03000034500c00104102c00e10180d110060f1140f019680d4640d583e00354822940160301b1828000b40c40e100120b080101c50750b0b41d0a074400048140c110499884216800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 813617958 1250 813616708 813616781
    0x605043b070308120c0903060601270b0306040b0f0603040318090204120515010b12040c080d021506041503060533190506040b0a1815030b010c0b0a 65
    0x4680003c0010180d070a81000b20040742c0c80004905a141413458400100351740d213000510082c148401d40c02d080004100c1151400f041807102036034400c1940c0c9618082c0d110350400d6944e240107030301b0450f4101c0d861406d00d035415001c901c0605a10304681d91078604503440402c007039107142c012031000307404030300c5103118001800688298402a101100b06203001460408000c988a02810034000144817801542c01150b0480c608202019180d496074100744c0c48590302079012881a1042c0b918403c5140d40100d445240c0801a1280f00810343d184c03403d05c01500c01c8070103403220200000c0c80078070020700590300041d088400548078007002c03403811070400354003d080a46543c440d901500200784a203040b0300c00380780190182d80c004540300c0c07030000840c0c050b01850064400c2104040790061040d440380c04030041c019000c207a1051100d5540808040740402c1400c1040003e0074a080100c16502400f448240203030b20201107100e940d11075180a00030600d0900392249180d0109040c41d52940c0b868801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 813619208 1250 813617958 813617963
    0x904050705041712041404060f150f0e01021f0b0d080d0c140901050a020f0a0b040b0c0702012c060f2515050c1b010b040605043b0703 59
    0xa070742e81e03060500011204000c5020300c061540460403452a401c2910244c8085541c80d6404c003541c801c0c003400140c0600001d82060714514850306001480040ca001c110b80d44102c143c8034403a01000c14030044989000880081d4050b9110440031010414017126011444208041c0040d404440600188a0b09100601a13400710342c003003810310f030014451241c2c240440380c905040709454046440642c5e42d00880e03031320034180000810f80c07501d424000c6c03001c400c1411017102034440d245058908a91101c078243c1d0182c2c0e4020380c0d000083c003c1b16055080310303002c5405031034246012016081c260030103843c03040600020005040c2100c020f4640a0281c00d81d03149a50030240c0340d40c0038038203010801e0420104c00c0e5840d0820356820001c1503000d0034014080aa03400c0c0429199208140d1038120311031100012840165940300070900d84040d4844250804200d5003841203640c2e510420081e509035400b509461451840741c81171001440d2640c807000300c1000300b1940340142c2546140d041401d0b82c1c0c0207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 813620458 1250 813619208 813619217
    0x120717090d0e01090815060a050406180f060b03090615090c031b0408030403050c100201020421260703030c0206060102070b160501060b1e030c0d0f0e06070201150b12061509040507 79
    0x20f1141f40c0c9400f90b00340740984020398041088626106d154510400305940044550340d50b595462182a03640e0400d2024004040c02503680381801c904a07070b6100e1003207621170200065809402054600003002034056081c8880c1e0072f041d51075000700f200076200480c0741d220340480d0400000421041c1070019000031400742000d0810b40c1d44520500c4040c0480b100c01b030007103910402003030200d00140744d803510403401209541c040c540381c2c500c0c0044141100c24250000c0b00070501c465140356845d00300070070746188243c1d03041c06031002440c0d081e6038842041c0c038034a0168010b074100b400b001d9403030b4000d0040010407080300540f084407034617503c0c00c407085030300a0300c161000021902d092070300e2580b6010542d454010799600e1743c074109410b0b12142c041d07840183c003466120740c41c1c2000e084068001e0046500302c50151100c604002002078004c040080181548d1482c107000042e440aa150590700070741417003030f10403031903a4402d0100140d49514a110710050b282c144034860440d00c0b0341c4030f92445941035868 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 813621708 1250 813620458 813620461
    0x90a02030d020f160b19050d1118010206010602120705120a03050103140708070905131a070e010804020607111206010e2202030703021009050402120717090d0e01090815 74
    0x41036810803840c6131216000c402180c0741000711440001c221280312103440362804003480c220f40200e5003846840d44002c0b01c40d0400104a0b000c1402000501010381d000b544035540c502c01e4030041ea210007091081c48050781121101d400084000001480d0182c402d20035034104400b0000200f1b00380c1c12021000380041d6450006000300403501c401c60045d01500001880ca0754034011070985c0e40c150a010b8060107984035008500368002c0154003500043d803105690104000c00c0c002c81d8440f20003251503000140001507905035a500804240d801a034001c0d00701c624144031a00d400b81000110150346420400301320b81d00c2e032040340600840340030701415035550f526802c1c2154070f00450b20801d124907640c42100900f2400594002540d04101d0b60705440344041e0541040094030043c00030760180d600310340001203083c5600d464060760341c031803030745a11a45c2a4a4521940c0350180c001106c02d003440b40d22208080600b603029201c1201c845d10149003610780581c9983d078450a1800c00c060f1400307603905400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 813622958 1250 813621708 813621733
    0x120a020a080106110601060f05040e04051c0504050d08070804031a040b361015180504020a090906020f040801050f0106020d0f080408070f030207090f050c04060305090a02030d02 78
    0x1c00e50700500881c94411010075042c0500d984501d0103118401c140412400c8151410380030300d00351030007090b002000c6001498242044c68680b0740c2c4001980005808160301060940180291416244054a100c546a0095403501200e50000f001074407510000e00c40000000c0c03013030740103188031051910308030654146494140001d00019042a05030000c0d41d0718100c44a0250410f14240021050310005650008000d1418140d0020b102100b840c2440140c5006034204c200c64411110703201400030301000c9155020b030440b10151002540902891810800b82c42640c204a10560060300014504004413400c0710040c1c0c0964401d40890f5160307003c01150a92515030b82d40100b03d1800a400d0100e8844402055aa14160140244003d2a01280502034000c055407040c81d8403a00d02c040311280b03428041d5903280340703222b5031b40b1060034010790300a0311110b03000f260701500501b07400342d0034142041e9095000e0f00005100d20582e201c2d03900ca610241e542000710894490154000e44140080c88 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 813624208 1250 813622958 813622967
    0x110609030f0f18031e07141c030e0613090e010902030d0f0e0621100303050313021314150111190206070602030a05010914060f15120a020a 61
    0x10104551608140710711280c8100440031140e080040c1e5458a986611200700e0000340600340070200e40610855400f0300c012807044829000702c0300e1420444440075511a00140d03013101c0c510044c0d403c102d100810f03002404404c252500514440e007440340710251180042002a0059103d01c0c446000440080266007510301c50305003920001402807115010680119030345204007181a010020b4603502e4208842c07182456141d10b030b030020b10799a83c03030300c00d070020f1903249459100e0f200d001984007012036400d1140b50140701c120381d416100d10b401c42d952401980701c0e194101a0590b000400599184c01e01c8200e4410710311040024103890026003410f200b2038041042c2c1c0d030451030500a02526501c10b15500058489910711a040140310b126098408210366005403540148154004018403844404540082d41601d004050400c035820b08038240e0008880240e91050300000c40b80c8000c001030804040c0c0031180c0e5168072155181c0404420000b15001048135881d5246601061482103075602 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 813625458 1250 813624208 813624211
    0x250303050108160b1b16090509030a020a080307050702040e010509012904020f07080c01200a0f030c02070f080a110a150507020f100e04050a061217040b0301061106 72
    0x1440300410074103201c9401c1903603d000301d00610300403420101d628102c2e006042040c84d490308205090b40c42c40420f00700b014003801710781d000703817040340f8144000a0303036604001040d507282480c0d0340d0042403841c2664a50a01592010b007010040010400c00300d0050b0301e03603008400b038800c0260000100341c1760203103c46084510b048421600b0400d1210026100c01008411307070102c3d2021500141e9801c04001414468844d4120040c001140030804001c5e065066200000e508000090301440d4440800680e03854400d0f00a0400412450042e60300d05910a038005c04100b40c01e401254000f0741c80b008800d8819856030702203030866002c00d0005041103c04452a4031840c01500c1c246420b50419011454200b14a8205020090041011400c0d962660305403800a0b078050001410000b9141c00103017030b5504e00b00c210380101c0c1880041030300301d280d6110f0081221444140360041319003d5a4204031f51854081125034490188000310344100004004e41c02803646807501c0a50200700e940386810140e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 813626708 1250 813625458 813625469
    0x2d01050a060f03030e0423091005130b090f03030115020c1516030c02180a0b100905120715030e070b03220602120903090118080c0d05032503030501 65
    0x524004000b0701211001c000c00f542c2d414203100c40a51010703404107000300300d80c2e00009400325a5001c0404030100150685001c0c00f900c40590f074000c0a80002002910002d4803c0d661032104400c0d06008540b410f00d0390741d008030169050303c1400100b540302da4a180c000f80c21a041035242072495910494040010404814090720320080e01e0700c840d41c00000500400492108610780c52200741c080600c20b02c80990865801054591600914803444908040c12980c104041d403070047d40241e149060b04400341c100c00c1c10f50301d2900c41401e100600ca21410345c01d914101c44c0c815004081100f5480e030b130007500207003803c4e60001610105804480e14040e0a60701100304030008105110f04090079400c0c0c00039011748940000640340541c50a030000388601400d80c802485403005010407040e011009195001c000d03a0340420000d50850058020421481359604039401005064468108030609a0016010b10141ca00300140c12500055424652090800030340c0c2455a2204041d0584a0107000d400e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 813627958 1250 813626708 813626711
    0x7020a12091e0f030b0702072c010b190f020a0b010806040c0e0705090607021f02160510080a0903360f0605091201150b0702090106020f03030c0c2d01050a 68
    0x41c941451544038030b0b0f00d030102030f01416140c00050b05090007040908000d15018200790200c0540e050020900301c0007121481c00c545a500000480211031404d0f1200d242c00310794000d0026044c100260785104072000504294000c09075000c01060303039004014001d043c0280544194909480c040481003207a030040d100c2420030f0001d0042c181c1d17000068441101081e52410703510006400000c0d00d4040030000000d4511710961003004151380800d085d00c002c80301802850b4080e0300c0f2402c018a6424035400766001401c240002600703100c440c0c0290710094080d06180c07001c2c1c0c2c0c0c410a10041001c4048000d00c16500c0301c24186e10a500406450008254619404031401d0030034600500500c00c1d030300c020b032041c104860f4103440003900303500440241c950f18071580742181d510030000e55a504451b105922820040c0000903640d80040b5044242c00400700c0070b54956a40c0103202070322a041101d51200901c01c646180007401d11324500340c0d150307240920010b00c510104a007100d0948400500100c541c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 813629208 1250 813627958 813628019
    0xe060405100e0c0406030303240b0d020304060b030d1d0603070c080702130c09030212011406060705100507050304050c012d1101090c03050f011404020907020a1209 72
    0x1900807442401e0400d40800118241c807101241d0b40c9082c0100b40301e15405840c0000003c00c058240c3e000c0d800d071145220407941800140d4515070100308040c403a512400340e0810040c1c1152100d64021580180b01e55070000f4000c0300b002c0413907d002150048640840d20701220503440884a8003104024a41180e0441c650b01d02a00700410070011a640240740c804081984400c40daa00e01c11400f400310903a0f4100940da4900200414511480c401603006d0311000c90f80b5401c10030b040c0184107103402c2202c01c0c140345854130428401d89912000702903502d40924081ca0020400314001d00b4001c00095031103580724205400c115003001080c4500d01d0510460b04201051160b80801c00303503040401d183c42c00784001605109460500f9900806500d9502e015101010482d06441043c01c1e2409101280d02154103181040d088030056140b0351003c288140008005282000210b5030122081c4140d4150340901da0b641d844d004080004034010840c0c0c0c4400748000a00300c0c0c43c0d404030002400000c002c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 813630458 1250 813629208 813629213
    0x309090c0c0705060c0f06091b0111070512120706050a05010902120414070509010807031202070819020d05240726040201031b080405070f06020c130f0908030105040e0604 75
    0x700d428603c900c40c052130001c1158007810074140140403400b200d40081d69202e280401c4225160b2001c035420b0b01d00180075040030781e0a94441d25400840c43c03602001044018184030400c40d0703500c04440305d000e09210f50169204400128400f40c440c0034411000801c0c2401d0074000001981c0d170507000554864810f2010400c040c4a9644507a003194000c00684150410515090b0901105070401504810f1400000440c440c00060b144e0841c1c1c0695a40744801d40e455800f2030300e0320031030320845000b43e00c0701a50703c0a9609844000d010284010070026040c20380d952068201280240c003241c1e5280713603059800e4400a400c03403140d80103885150a8800020503110030400e00b10210320a08501c0300c450004013107900903030000103103086001210440f4600c02d00d0003003030303030300d003164101d602c1e0260100000d40034114102820962f8095005440c1e884041020301c85802d4400740701d10010b40d11148034640c1d8000b14031038a60720390300400c50a41c2e030307606000a11007511040155042241c2c4000b080002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 813631708 1250 813630458 813630463
    0x31205061f0905031018121215030b18070308130e07030c030f020a050f0315041d0d08011406030411060c030702041808041e1d070315032607140309090c0c 68
    0x791942c0300c3c03000510448102c2c4112343c4440052508001d4510b0301d00c1c00e0b41a16000c100e0003003224420b281341300f601d03070f1441c1503c6c0722103089100e034003c0b0f98811135040c800601500085c1c1045401c03800c2d600d560315a5072108500da83d4054a20001299480e00c41c0d412091f858024880c500c040d0540c158900805068014002d03c1900e1481c4a01100800800d030b04a4041c401c820588000920600649202c40f2145e00d0311000d0f00042c4074180700c3c81c401c902045000700507050480d000490b6100611222106002039644020001c54141c40f0b0406840c0040d56520b01810086546000460302d5848500c1400100c407048203400c40300c584104887c000060040b0100c8051b62410f08001e180c002d20031a20110b40c40c500c0d08045c0c01c900a500c0400107003416458510f100e840b1580d810302c1045656081c0b0a00400700c4d00029083d000d0b850040c410350b280780705002c481200d0200d40f0614210440e20340c2e0440000c2c0010740c4c82d5903000060008014540585125001410990603901e400b40d61b00425a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 813632958 1250 813631708 813631751
    0xf0305092e09050115120302151306151a03060d060b120109030302120f041a06240d0b15040e060609130605100507031205061f09050310 60
    0x407508400d95008212040c0c0004150a60301c04085061100114610f02036000e0100008966121110b00d10002401924508002980c64254010702500c83d036041074813100060003003582c88000d0048800000040180c4a001c42c600c030000c075040a5503041134440345c1d10075010609900c1040083c001e0001e03533503c1c0e07582005801e50050000448090170340c08962105000e44640059502e00442101819055001800c0c84102044681c50036504c417a51001121015500900001e10390311810249a00040341036402c2000281b08003180304442111054030481000100004140440c8900f1199020b00840c202c801003240c2d900c12101880300360a040340a01d201d0082d401402c00301040580c0c981a049940140014164a070304101100c46440948074031b210301707070213540c0c002018003030503224000b81e80da40c9500d580e50b00c880643d445241c00c080c00c0c0140c042139101e006014030040c0045129103201070003080384c9401c54914030788801c00d402c204400304845030b114200900c4200074481e240050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 813634208 1250 813632958 813632983
    0x1c02010f02071a1f0f141807111608030c0607080105030a1704090c030207050c0f060f0d06091b02070b0307090e0a060302190e1f03021002010207210f030509 69
    0x7003155640c0750100013542d40c003182c42a0050b01d11510105032a5901c4406a040c0e890100c419000c4055880510030030589100d1704c004902c0303910000c04d8000340304007080603108a807542101d4929144c00034104440180340d10040f0554030000d00490000c00500c08035034021400d08000595604d4100425255120075030001c3c00900d154511620b840c10007800d0701c0140104080c00c0210342d08032080a002544001c0b003c1c1c840d0b02c1000214050751414140c604200c0401400c00c50400c0c030040182c022030f07080004d0704201c0e640c8400c8089110903c61080c488100029138046e4110901c180300a030501145810241a80104004000d030792608803124204440202c85000c03a15034500c25000000c00450300029405180d520000c1078000300900c1c20f00960b000000d110107641c942c0b4200d0a00c4245008521000504080d000c00c00340c944440c3c1e8044200007800090301c0e2810540d00d04401d18070071101450070b9005001415000c0f80e0048500541d606242810071041c144080c250f61fa44480f580c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 813635458 1250 813634208 813634253
    0x12060402060d1517210a0302090f0d0305030103020a061e05090d0218100f03021e0d0f050a030f0503240a030209010305012f040b0f07051c02010f0207 66
    0x506400802c9030740190303400c1c900c1c2520181c8054603032061024141207050906810720030180d51645000c41030035070090500071070141c503150402c2000700750069040140016840781c40c0d4103110319961198140084080e05c0307a500e555032136045104012421000790082c3c0200700301a03101c5203814074136003030300d02d0b80401e20b04150b501c9452120024038a4018190000d42181424504040d46080300030b1041c00740c2d505000c1242da042d1501440411506980f00282d4070510b5107491603180783e81040442e8010101402d25204c0c0c2c84141c80301391070204005070440e415071006150f00213040d445001600c1c1000c5600d031180c41c5083c807a21101e000708024861150800702004400c107034ad035990148100455002d040080c556a403800c1c06030090003818a1004070b000804844240c03502d0940c4404201514011400c1c0ac26040403a0a13440d0f81115003413040700c0e4010407001000c00c00c00c1110284450004008100243d050f04009080d035082c50041c5070388038014800386000840d0841210418405d0b050b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 813636708 1250 813635458 813635467
    0xd020f071e03060c0f0e040b030307021207210c060504030b0a0e100c0c0b09070e01030b0a090c0e0702121305011b0c030b0f06060f1615180c051206040206 68
    0x26a00c1c0005481c0c0c001410039107051500340840c0c0c2c0003500d80b04c5481040d10303400743c44042d410900059072202810943d15404c1005078800515005902c001a4003007a0115240ca80d01c0b840840071900281050380300715600800b5490800040b0040540504000d16003241494507503920306103024000342800c12a19101c12100340600740800c8050400c48c1908030502c03e445c0c03042009402450840c0c02030b2000c00812000070124000052440110f80603203603126140d07032868580300c40780728024103a10300280e01d03013502030041018244908090040105a8401410145c001a242c020781074027105c049030f000d1280c840010641c01990b02118420f09003440b03a60341410150549208100380108500fa04040100511006070700d5544640c8081c001145c49032210010840c1c14050101d11010f05901045500100e002d2000391005645c4251a100c0c0b000381d00d04030120599090045012103001450a84411b0112030342610000703103025201d0384400c010300c03d01e090f04d0307040050019016040005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 813637958 1250 813636708 813636749
    0x215060418021e040b060301030f1b051305070f0f020318040221091e07030f02060c010c0e0f01030b0f061c09050a060c02010513032019050d020f07 65
    0x812144140d4002c082c008044011610080c3e01203c00300701e580a40d260140741040da04080003128162a085951400310b141b05a03100400ea808611801000150045000441d03448010602c040158141c1000c1010f01c0d0000307004000e01ca40c06041010000340303a2120aa154003c800c42d0f0f13602a002245d0203e00e443e05006c00c000e03204018800e0402c0c240000415020021044281c3c06642c101007660320340c00459022000311b022030003001605403c030120410000d80381c0d0216503c014805481c550070b1605840e810b50031a1a0407252001103403110b20044400d1604162440010009003001c001e521034010114180444d0400494029440041d101507100e000b403051400007580e1035002e1100101038607005443e10002d400446402c0d050120200306207006001d203d01c18110300d991a115441c5d580c4007140e100f60709050310040b000e920051058614403e010b40c102e0184c0103c0a0068544113140c458645000303205c08104642103100a081c4041c000704000089600d00100e800b40c6580c3d08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 813639208 1250 813637958 813637991
    0x1406060d0230010605070804050906040f051e070c080d11091e041a09071d0d0308010e07050f0f030405010b0d050114010b0a050d11090a06081602150604 67
    0x104a205040780c084140c40382e4030482d44180c070180c442c1d01e00354100d090341e850606035800e00801c02c005004250502051000d402c000520f2548400000d1002c5540c81c005582002215401d032110005c0d40360924405000815600b80c441d00710301c0c18601551500c04a4032030000c81c0c01520700e0401e280b500e80360408017481c8601309451214900528020f9a10004a111680d5010030011907005e1400c00001401c07229032540d141030700321000381c031070401540c07082d10840d080d05520704800481290f0301d014000940301e52100d00c1c0800e00c6a00c510190354104000c45000d040c00800c2041080010041c08145402e05001d8408400e00e00003195140d4545282040c0944114055960440b0a4514403001d00c903054000080c021540304003580241d0300c1d10100380e614450003c00c0008140d0030007040b2600382066012444210340d000c405801c01034254001216900760b903200c440002d049900f80a041e2001000449801d04a07000401c60003040203000000a1402483c1c0c9204507030b41c4100361101c9144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 813640458 1250 813639208 813639217
    0x30609030703110a2301060504050402010c03050c10020315010201110901050910110a0804090b0109031214090a030f1a04020d0b040203030c070906080f0a0c0909080d0501080d080702011406060d02 86
    0x80008505c03044541021607400340c065141c0003140b582001000242800c10b40304e080d01440d010307503940356800800e0310281c44075800b8101841ca1480343e01c1d8154401b40207072001c1d600075003854400d440001c039120002800c0d20708010102940751810400035100303a03005011550034090983e2880c0000000400a0302c2c003c040b10285400f50180380c00b07034400c0007040001841600c0500904200740c00c00b541c01116040114080101013284802840300310700e015200c01d41703444418040082c501081000890f4400030154011208600003201040070810f81c14034101d02941541d0072500c113441e064000507250801080050070b80348540d00441d0035900c1c2072044480368801e510803551025a5454500000c010754411220a8054952148040c441c0801d061801030703000042c44490a05254290b001400040c004441c004010448801da409981c010b00d030090810300c020b020b002d43c1c080070290900710b0091841046901d080511044103017002e08040d000041580d603039440301c400b025654001d119 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 813641708 1250 813640458 813640463
    0x1101020307050306040606021c080903070f0c05040b1f0c1e05070311030714120f0609012412060506030309120f01060e1b0d0609020f0c0705030609030703110a 70
    0x801c1107141d0000010750003240300f55820040310f9964101261562549110900c41000720269101d805101300d428036001940007003036030714160444e80d03281c200410300b540482d01060400000c00603442c00c2d00c107000e0f40d418140c843c8111484a2960f90756440725100464003803142c0f031a01142403002041c1540c86502c50603000416114090520690f5800d07244011100c4514a07078080d452410041000003c80700306041c10242200c02400b0401d0311600c8201041091040c031400c0d81050381d0401916010700841c0e000003510204078150b8602942c2840841681c584600c0c00c2000388034051814407040b86e030032650000d03a603140c1d5030010f404c6201c1c1c2540c807944440d158282da118000046000664602084000c01606594000325400448100d68a0b0f010101c4460040900b0031a02d00815121052060000d40c0d1a00c03841410708980095144991103003020420f001002000c000368000f03024200d00078006850710148050307480c41002d00c02010848000f011281c1644200100403d0700d9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 813642958 1250 813641708 813641711
    0x60605190215090606040f020a17060316061e02030906030a020a0903051c02061006020604080d0204150507050d3b040e0303060117011505031e0106051903110d0c1101 73
    0x7040d80009a4803441031700d10360f21540c40c00110640c0001c42c0d108584880001e9100c43c9220005d04c04002501e010003000c0503058002c0b51000e900303228051101d4401b501c002d480781d050500001d5400c40e0f683c811003100e00150345c401c00c2680e050355100780c10f030b0740d01ca070401d80302680c0e410100c0c40440d60310840380d000424620458a840d2003050800b50680b00c0380358141e003142d00e20ba0303d40203100400c4a45104600140e044903021030041501980100b89000c03080e0b1015160640e1128802c2e410941d501e244000500c1c0401e4010400000b8056a01154200d20740759050501d510318045046a02d1200b16400e06201c840d20b02c1e440405e42108034660700010420803543d203c0d074140070348a51044917107a00095010380210608a48030b8810383c141e82c090036540e05494801441a2850703400130b00038609603425100300440444650810a002e0031960342c9a81d1203a0803001d019400d200c8030a02c3c0028141040180801814a007054602c002c1e030303249000c101880d4a05e425601002c6001c07490b2200d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 813644208 1250 813642958 813642961
    0x11d09010f1b0e1503040809031c02010c0e090f150102070302130204170303100b0a0e121005010b0418020a030b06030411090606181e13061503060605190215 69
    0x60079a105412a003400380c1c0721070b0000c1521000300001000d0911139000d1040c01030000c1004107620b42c01619954070040c0450381560384064221742ca80e60075000b80300060b9121007940b0010b50f40059030381140c182c2a11000310354201024507107054480103050060380e082c00324a40c0c013160f200300300d5000210b8014004484d00b10ba01b1035036801a610601031101c12511018540f0b0404034004102c903c070744610b440191000d0f0501121030483e07030100b00e0020412500c81c5551826589191074031108021450043c40b800311034160210640704160b100d12588031081c00100040000403440c404404000c04006981d1900074401350000e212545415811401c0801000100b100804800441c140100c48a03882c0303685003401c00c0394912035030780e5000704102600c50300e401609001c207002138080718008010355100c00a9021402c036002c0028843c141545070b0004000e00ca80c0c4e151080c0409080380740c244190760411801038030134460143c2012500310454100c0801903c28082c681182540c2c00c003410f0203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 813645458 1250 813644208 813644231
    0x402090f1009020c0114010b070c0b03060a05092503050709170715230403080906070f080c010f140603070b0d0b060a050403030314060f10020a05010c03061508011d09010f 75
    0x2040040c4010000c0002003001080301703015081660940c5a00414402b0110f0038a903140030703039070005800a03401140c50f403400b061b00d81e03440b501d95120301000c29031220b07044041c580754114142408002428140342c035041c0826194442c114000f03031041ea4001282c0098041041e07454542c0030742c484c6030764801442c0b00c1e0600580c05900046a141d168001d60719082420f04001294461072000034000003007009015024103015000d8018079000303407000081c0c201503485a00155109465400b0b899664a9904c03045d05c14600c01c00d920b0b000c00b810240e60900d80305011a0742c41c0e040d402406a0b1a07404522540418500e41000986c0d100150200d500e9a05050003c0d040e90040d01044021038200350400304084407100ca02c611903203004050f00c00c51240182444601480409000c04501410548501043e424000d050799034505940020380f192a08640808000b03401c90200e081080c0140104040802410008491030b034103481840c40341c85000f4040e004000c2441c4600303030541004d2200c2c42 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 813646708 1250 813645458 813645461
    0x1021912020706080f1302063a050907050904050a0c060c150b03071401110316121e0302180306130506060402070807060209040b1806010f080402090f1009020c01 71
    0x10308480c0c0703030201e90305035490341c5042d100e41e0004c48009207a04c104400003000c0c070000c2d0700002c0c80d290018040d949403a110707980d00d103031100d4054041c815900781425142000e1400380040705428860390390030000340c00c20003a0691201500e01c43d281c0300d18070a402090911a0038010300da030469201d201c00d810b00b651014090005010800f0686020400107140c034086012400380300e9014600a0181034410b04010f018006400f000403c070381006180000903810f04804c10080c84040880d00301442d540d0624030340100c3c8006000303901e07020051405203da022409407858401540841c2c20056214500d02d00c0c020402101391986a5051041c0c00030b1080c04c401660346021110b01400c25180280c2c0c42505000c207078400c103100104140030420504000c00c5803540034060241004101081030402d00c0006514640c07080801c42030030b44c0890900c45d0f150703000200118440703042c0c00c006400b858150005011502c00400c00116030000d130000405600043c140c00d005060002d100f103448052080c0c6150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 813647958 1250 813646708 813646733
    0x290a08060306060f030a020907021f0e010b030c030d030506150a080915060109030311030d1506020c09040f06020a031e020901090f083409291e010219 66
    0x1e000c0d01a0714003099080c2085001c00440c40e030003800500840050307609120031b00c00000e0501d02103008080314002c1c2c1c1012102e00000c0c0503014000402c50b41c07004000182110640202c49100e5841400544281d03280801c1d115120400360900041c4c9940358000305001035100d41d1221056080021888500c81c2c00405160003068014100da200b01100d200170108007106440310750204d081084101f000070f210b4004044843c15040540c1d042401246229081d80c8100e91075110340c500c075910900000358108900d11003100100c642c4916410652185d613070341c441040c0082d050303d1300040c04c414202d00a8000e11554407510a100c4c0003403105280b408000d410031400a40041c56182d0001101c0c004621382005443c89440070f0010f56400e014040b680c4600720880000c14244420b28100940303800440b41c0080618080100e6060b80c00040c0103410000320300800428042d40d4500b40c0162a1800d60400d04410079036075590070706680e00140d01c1d2007109030051500750702c1d0008000800c000d032031604 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 813649208 1250 813647958 813647971
    0x30703050a0f0e03180d0209150316320907080a0c0c150213031406070e01021b01120621121b170f03070801150207030c290a08 56
    0x20402c04984a002c40103943d441c400700c0b40d080e40700303000d842604004844903442252005107a41901945540401c104100c01c072040e5001040c5062290300a080920424203881c06001822210908140810301180c80010010300b214400f400802ca40c01c910f401c480d800c426008102060926000000420921080f103c503088a41042d60080d01d050250300700c455a16031244603402c500600503030a50080d00100000d01610500840002c0442c40b01101c014000220102130302481c0b51903c4082c224000680503281151b0149010403008440301c2083c1c00301902c2441c20311000900702c2981c1d070240c001900310846040e0004982402105034160f003409640c4141c0d6400d521440c800b50980c0c200d2011b00e40c0d01402d002101c01d400001c0ca0700d2003400002c4c010786404909040000c41c4086150b0412245103011414080050111341c03521201c0c41c8000d2400e1000300343c03e034116928070445140b18460b65031000480300c0306080704c2010001503414031040c04002500c400c0c4d0315500400d00030050b100c0b03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 813650458 1250 813649208 813649211
    0x31b060e060411030a0c091107080f0a02071d0403080903130f090b04090f14011d06060a05060c0a110a03080a02032508071529030709060602070608070302070602030703050a 76
    0x3840741c5130802040150358942c021182081003403400c4203e00117080106003410021204100050009403c40054880b0200d10319015407241c04e00742c1d019143c103005270480144c40904a2074000c00310640f0b4032160f802541450800e450b5120b10002d42d1450140c0407e01d000a40c66070000710b862034044403c0012200400300078460661000288001c480303e046019211100306c40b01c800114142c890390524082c000400001e1401f26440c620307120707041030415070250750031440c140a010310300319120001401003141e04c01e01c1c1505094040c0c1d038030f600f22070008140c80c003c805105250354038180703036100554110360180c0d80c402c1c0401e0000e4896101010074408000c0c10258560404014200303c44075a0b80049810b00e000301903142c0703c4c090036407801c00c1d4808035115a207400c3ca111807030600107000384c003901c5010402d050400c201410b1400c3d03600700b94041d0303140c0102081078903400560603003141d255007040d2005840710f01040340030b4803c05401400042c000410300000e039a140e0321441c40389621150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 813651708 1250 813650458 813650483
    0x9060b1507150c021e0a05011a09090c0634050f0601060e060a050906160b180c0303040510050c0304031101031802010906030c0306090501030605060415030b04031b060e0604 76
    0x900724215600400280c00503407111100030318480309481400186090482212521b94046d50b41509403010558825807070b50a108217800e031410105002c582111101000d82100080d6202003071090051040c03400d02c49000d02121400301054042e0034540c01800c021403c0500d0f1141000350380c3d2040d554845019118580002070300a10844084207a903100500300c51408800800448003504080000b43d442182000105400b442d0b0b5440b11203481e105540c2c42d82d1a24040360108d01a8500240d540100e81000035a5503007540d000c0115402e480d02143c0c0b1102d03540001104640328002c00203190458440000c0100c10f100100010301e1000000340e90500504202c62400b001948508500a01245840304d041c03000740d010b074100320f035134880c83d01d0b00203031240c0d54404400c00c1d14400ea00a603110307592041844000d0505e400f4403041e50009070343c01901a4650707526480700140080005c1d0412401822002d150708101900c95a0150460000d00010060f00501515203400303039021502240c0402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 813652958 1250 813651708 813651743
    0x606010801060504050105070804090905010e070b072d150f0b010e0310050711030f13060c12050a02010f050702060f0901230907031b0e0a0203040f0609060b1507 71
    0x304054141c80d0a56119401c1a251200548468101c440d00315941071052001060700c591510600076050300820010900d90f402410090520b1141c2d003044007820020010708000c00c28590550070302007408029043e4844a9441541c030034002104000c2074a14040e1419981400325007000ea503040c41480700300060015480151002003203145110b81603080340c40c40f10680d84d0b2590140c0c2e400301c02824100d00c9040040003183c01c42e44001000c2c00c1c00d800c0407521108494508450402400c0309007030070f000b601c2d41d988440e0703660005121040c040003400103030618594400c0d0001c0c103034010149418011401c00c1d1802a490382c00071161b42c10540d07066000504203c40500440b480f040c01038081d1801d0241030015013000c0700d0001c0402c002e9103d18400000010a424101c861510402d0b00c40c03080d2600701007000041a50162408002c1401031040c000424a9041e15a4a0f260301c8800040e094500d03190001c040d042008242e0703030000c5107900c3e2031442d820b0200113080b0f2500c103101035501200780342d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 813654208 1250 813652958 813652967
    0x5100f140f010f021609060f0506041a0a05041d0103110315060423090601082e020d0b040e0606101e050f0f03150f03010b011215080703050c03060601 66
    0x410001e90040e42403030116540d500442e00c44225052030f20558248451100d4106000f0701030394008500181d80d041c08019010490000d28040c1c2400c1380d10505c0c047ca000c007002401540c022203106880320002d01580c01d1405441101d00600d02c80d1003240444505440380c085d1007109120585800b180f100300c0c061585000b081803080b181d00034504070580d032203e00502004003001c0f030700002c90900725200b2a0354490384114041c0f198040e42c0c01403030b0541c1800140717030074110903c0c2000c0303903840302e00c4000640018040000c0c004901c1c1180042e11082e88000002c007070310520049680052038000d5006007040c010445920030b10003615001100c140540c0304880c6020700c1140400745440f00c01c3c1d080f03544ca10075002002202c0c0264103080c105400c1c00081005a88242c030201c1e90b05451025250300f50a1200200807040d4049000b0008840580e001a0240b041500800f10f0703290ba445411244206c0f0000c41805042c42d0303400c841501d40c50303161840d030310004611514400d09c603150018840d50720a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 813655458 1250 813654208 813654239
    0x1030c0501170f010911040515030403090614030403080703090602070b04050706050702030705090405151e18211615060e04020604062604030e0910140f04020c0105100f 74
    0x3d80c60300e4020f0781c03a15001ea00108610000c0d0381e6041c108010010b416507405007200031410000c00d00355a42c1c1011303d0003418413200b135403000051194411100070000911003c0c1c0b40e1080d00740c1081100c0d541c0d10700c0d088004140d902001041c81c2d2001c1412401c2c0f00d080441144038034864005c8900a980f04c1d00159114000c040e00254544d001540038040c0d81009944581c2003441401101e10b078556001d000760702032008680c070b560382000414000415050000b0581d8001c83c403d103001e01c20019507000d060b26021400e072034030340c00340c04150f410320170101140898568090b40843c0c80703c020700c90f14000341000c0c006494a0030741800c1c24000314644641491060150ba80145014601450444280c07500040109001c1c01d100701c1200b240c04491240200c548514403070303540d0058520381d280c10041c0106021b84070072405850281c0c140945101c190102c07102c0081210807450541042c00007030080e100704803540c0c409500304000e104d4920702e1034500c0d200741c03850b02d6500803d0a4540c01307505200c425 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 813656708 1250 813655458 813655471
    0x3090f06090703170f16060c03150509040c05061b1b01020c0108041407060509010219050705150408011103060a08061e0c28030b0d0b04080309030c0601030c050117 72
    0x2c01040011454030340051444080760501d4208003103050600210b81004d9240d814101941d41c4003010800903228400b06444070b41000c000102c03840d01a0101207041d070080c0c034041c0148001240c1400203000c180d000808009050030368504201601c00c61910100a0302e06052085516120090680b00b807800740074030b01a4000c010003548040111085080a0002d450040120302d00d00e161640c140013501c0985156101c103a07841e441c0318002440c0c440158400416a140c5c2501400007440110b1950304895044035085140c02c2810300200c90f62240703501c14020340d07181010519083ca0f03038002851040300126400c0c24150b075144135050f11800211040050031201c180c551107020090518150001c9a4110090800c495054600c4411a8810402e00406400f400810142e6494096903007400e0f0280e5103180800429a160088090301800040c00c0180200004407282d5040068074542c1d078403a0100c2c0c04d0f5503541d0500e60324285d041c0c050b1900080740801000f030400d60000029001d050b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 813657958 1250 813656708 813656713
    0xc0a0f0206090a030807050c03040303030b01091410080603010b0415030b01080601030809040504030504030f0510050109061202090903190e030d03020405030d141c06051207051f0314040302010203090f0609 90
    0x1100d0ba4101c5513400c0080c41b000c10311500303010458004200b0000750015600c6500c1c0001c0e55500c000016101044e2684607440d040d100c0300c0d0405d030039140e05041501804040c201038280d500e5100010b40900795041006400502e80003154140b0307501207046208980c0034100008032640ca960505450700c1007408050085c510400001c0031034105580306070f600c503020745001414144c982c0d40d00c0703a00106103c000d0b54680c1c003110746ea62103070700036100d1799006101401c010000245001340643c0740d1315088001074414214079001481c0d50b801441219560100403440700984c158214002e0034008101070160f00910822040480c0c450107403013140e06a990040042402150a040844008913200c0d590b000c4031006020740c81e21002071030351594002d080c441001c83c0307183c01d04040c098014800c1c862030000740d101c25170030400e41d00c030300400c542d8403030402d14428907c41001d0f03010f5028044441a8210100507035040000b4941d040d8091402428400159404036038081400755031034005036074201194 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 813659208 1250 813657958 813657973
    0xb1e130b09071b02040608030306010f09080d0c17131401300e010e010c170f01050105030a02070c230f011202071a01151b030507020405090a02090c0a0f020609 70
    0x6405402501802c552420750f015080503598045000d69616500c0406c0355440072040c010907607040343d00302d66041c40c10701e443c1011610740110b0755038601e03040c400d113402c1c00f200381608020b1201c0341c2c6c602d5901c0342d000c445981c0c1d580d081a0300d40860451a00c03500800401d120041c1040f0b40c4100e40040000346261212800c0d00c1d4007001c400c4115080020482205a403a00d44c83e00c680000c1c040c00100c01060400003038042d2541101500a41d04611140e4800d0990380400811140056032541505e800f841c00c02d03140d0303903a500d194000340f080d00c0700076291407291403001603d449100480c104255642c1c449244924a2009005000489583e007a02081c03038240103446010f100c2d40681442400b03812031602110500c400c001200d142070300300c14209050220980f1000390007456582e0343c0f006240500500c10200d840040084c015800000e100d207885501052485200300034494160350002c00d5000f41e03040c007602003850350f031101c54440d002c15925904100200d002081c001d100f01c100c1c1024001d00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 813660458 1250 813659208 813659221
    0x5062a0304030f021504051f050108060a020a0215040804030c1e090e100603120314070c021c06050a0519330b0f210405100f0b1e130b09 60
    0x19215050b510200718412042034008000d1740d0354043c0c0c003070b60044014000100500d000410303090382c40c0c100b150b00d0900b040d004000001c0005103c41d17000750301150042e20f50002e100124204521401c44150449a1806100c24481038200500440344140310081203d652020101400b04403015403960558041c3c130104880105a045000081242d00070b9034104495695003030125811a0411356540360500c20403444140c041c411064680210030768038141e807400b190001c15040c03849000a00a400d0003c1e4175420302040da5032006541c0d1300250502c0240b5200304500300900c002c03542c0110390280e6416520004106114810b4001c0078041514180c0b0424100c3d600400c10b19020210407440d00c003070001e0000b9201014100d5502144421036455105000f00c4203240c906450f295030280c510800c1c000000c200185214a03108405c50108912000c4903440006160340300702103820002c0b070000c80101e1011510b4250040030101e0701c601c00301c805000108115048140c040760000f0f41c03880070840 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 813661708 1250 813660458 813660467
    0x50c0a1a0114060a0c0c081002180409051b130e01090501060b1603080405031204030c0b06190501180f09090302061e01030209040f021306170a08033105062a030403 72
    0x4502c6d0180101103956962241c0a600c0d15802c1040704640503030114641d040303d9400c0384100803440d4211001e101d40075080c5c9030075490302a04040046640413440b050002a02c9038001c89500340c0c0500c50410100700c0350f4a182d03028110140d011500c1d54604440858060518000d9426010f040c1d030354004081d6959a081d0f80e0320310003802c01d490520040c0540701c140148501d09c1071007a0705c05c5c1da80e142034408514100c0010800504414890801c089041112056400e440c00480b5800d10b005110405420550b0700d0354181500214852441e00d040481c030080603030011101a0b200344d003122820303920303458022901c0407020b103400e1014417080300420161074407554031908a8003c94814040e1500c2d540002c0301100c9015640309a00c1d1035030707810416003140e100703031740c030800203e1001d8640301100e90380b039001d20303c401060401c0c4000780c0182e8064040c2140301651010303c0c50341107800c5840c1c85080266444070b003190411400e80e090325451244d5240b060180001e060158051811034807141e50658 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 813662958 1250 813661708 813661727
    0x30c0705010b0a151409030c0108060103021204050330070f021f050f010e04030e13090f0c1e080c0907030b0904060c090605160f03050c0a1a0114060a 66
    0x124035640300c20002c0300320b9689110f400004c01200c0180075089006440140111410080c2440c0601d001e105400c1c6c1c0e5100421071080e494400d20309608a0768a040c0140c009001d6031994206050a41040104105d0f00100902c2c0703002e80303078150074500c2031002200801140040b45981c2810b141d03101040510307020b5801301307042102e0303801070303440d010101d2654101c20103200c40244113084d282d030280000c15040f4407000c0c1c090480318601481c00e00e016280602080302c00c003240d6000701441519a0420304459000c050003039408140e0410b4420581403081c8112003034050510401d01c04268130503454882181c24040f51039400140c22500c0b0030000f00601d5040040800c402c1c10f0300c480d400003a40e40c03000c50399071189100f070000050440070820003c1a5155503001841840f00420880c1c903e076503074a04c60f01c0d10703652040b103a211a115078641114140201c2525410600c05c03011a20100700f501b000c881c501484c0f003103683e1651303a0b031214a00440b64448503130a8219004108042c480d074422001c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 813664208 1250 813662958 813662963
    0x30e06090a150c03030c0309020f0f040608010c02280f030c0804090504060e1501050d0803100801021207140403080a0e01031d030a080109050c03060904060e0304091d070b030c07 78
    0x8891250360740d40c45042ca0710210b884040000c5840070070904158142c8698103007030002d45410480801a5030114446a5200e44054410082802030340c400c2d0380c40d034201d08050070420740244203500360f00902075607888140d800240c045c00741441c4040200c2d0b5440c441300f0465003054080814482d1620281c820648403c0c040c0e600d61420000454004642c0c02028003d5128081c0002c000142010701d030b0905212001f90350103034035854010401a40c6480111460541000c182940c9898000b07049804078070541c44019154008507481b0074504401d007101d440b8102c03640310328100202c8541101060b110b03d00000307280e4001408500d41d1240300e2080f040043c0b1041c14000b9940410451085e500790010300d10110b01d5100203a00d615450340100303030302c2c0180301c4000c01348154242410315025074040108101d00800410002900788092a0000e2540c1015003040c0c9640701e1302c80300da40300070b81030710010307401510341200728031290180001d0034a04540701c1000d050f041d926428003900791a400500107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 813665458 1250 813664208 813664219
    0xe01110f280209040c0509160e01110f1605030706020102070201050a0503270714030303040f060b15030408030a06080a030801030308070c0203030c0303070e060c0304050f1305090a050c0409030e0609 87
    0x4500040e111540f1082c000c6006030500d061080c0b5143c00c10a0b210310007449081d458252102294001c5c1e000b040c03a1000c81c0c5c00f4281609a01e203120052450007903071141c5c03070300d403032140419a00c448901441090140d5505070305071507019880301c1e416804d0303100d0014000e0002e02e0400440e03000900c110040e64021346110900c2c01602d9040d1440d803611110031070f54031481e40180311300b001400903000914400e044103134095030951a02d51a603803180305181c00064000c50301d4032170f00c0140780d0352a2100301e0b440c0060b601203a246e003001e042c22103207600100c90f45400c052900401081c000000034139851050b5160340c0d00c20321a82142d03411203412a000c2c049409000d032114000f40166418009025002f441c10002e5480f0301c0d006800500101c407210b03046004140c1003011010340720000c0308540c1990320035241401615034040c00f0070540d441240c0f4003070070303149401e051140110012401c03440c0350780580c084030580805103003007200b203070060703600240400e41c0c0f0031800e0924101000a0210700c40010719 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 813666708 1250 813665458 813665533
    0x5060a05040807140607020705040b011b110306011403060114130e070506070f0b1302091b1b0303150604081f24060215040c051e0604060e01110f 64
    0xa907003041554805481000f50081d0003084a580c7c0d041000c3c10042108031818041d580c1400c0c006001d681d440001e541924071880c402d9400d00086c061000504140030301251425a0344080c0c00760341a40c0074140c0b612a01650300001000690340c4e24001300004000d107042420845441c1e000d00800d05c5152000c44d80c09034450024041c0c1c0d803c40134260300b03030155031420201c1c0800c1c03500300b00c0310300d004100076901900c0030607441c0903850703003840e25034000850f01d1801c04540c40b143c04074445005102c04001000d92481c141410313420080007940c0190303090000704a40b49011801c0010364000d6004019039075000044180b54540c840e2480403095004110014002c001c01c0c110500da06142550381820984080c804c0086942c1000071020002d910303881080c7c13906050351600368400c014860540f207030020740d641600d040b450300010310072840000c00040d9215607505000e01450045c00146022952003075210300340c1c000101d83c001c0101303800b1002d001441d1507040b103d213110720070130306000c04091210b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 813667958 1250 813666708 813666713
    0x10506130513021209030301031e0c0302060307050d05070e1e061e04031a0f06040b06122a070503070215040308040b0426062a030a02090a0f0305060a05040807 70
    0x6452081d0004030580144e600e0300c220001444450300074103140c05940c820401000894001c0e201c1ca07540c901000800f41c0415018241b05403212000d81020350300000c00014008403a403c180140403c0c04040c5080c80740d40c0d170f48942922081c440116594004036842442c080c000f01038128400905e070010080d13420b000854241e00e801c00780c00c94900c410b05a0020b014014403000c01001c2d4006081c90891614500c0c1112103c60304a4000d81000c1c0600d8407501008815a504000c1d141c801e07144042025440c54101c610a075281c02e07000b0321581d0742c414241d40300f6000c410701c1c046031003041d00840210700c0d0034035503400e03c180454040f035000c584010920002c000962144000c1c002007041e00e507101c0d101c43c18891810440700c03505c2410011051121a2204081c201241555200c00103030143d0000e54070ba18024141d18101e21400300030b82400204006001d5003e40c041c203074045050b10b40070300d069285c041d0304013606102d00000d0125400000015a40380307190300180da10910604030181031500a9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 813669064 1106 813667958 813667969
    0x40b07150b030a0c15050901140318070303030e01060b03040f140102090a0f08070b0307020615130e030703080a02040605091504120506040605010f0b030105061305 72
    0x91296450080c1903482480310000c0075060303070403804040c0307060a10841c150041482051145100700c0e6054850b1056a42c843d0040c1c480761150818103001c05180d0b08018240b064030400112142c01c0c28506010036802544a92800301c3c28800600d400c900350391554210f80883e070000d0007040b01040c45105503420080c0c1061800303c00c03080c1c501601e80a0b12442c0716464016001d0440003c268034107040700400c85810303105030f900c116250f0840d05035903c010b446600069101c400420304027883d4020700004090002c01054141c0c41c031034107000c1031b24034069010030150000304412041c540c1128001364000d100c00d07000c51909041c810f019120707008582006000d2120b08070048800d00c2c408040b20050800041d04100c2210149802c0e41c0c2e440007120101c402d642040c0000451036070844441090b00c400e0104942141e08040c01c0c4000c54014254003461146041000107482e00c80 = true := by decide +kernel

theorem cover : BRFrame.Cov 813489208 813669064 := by
  have h0 := BRFrame.cov_init 813489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 813489208 ≤ n) (h2 : n < 813669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
