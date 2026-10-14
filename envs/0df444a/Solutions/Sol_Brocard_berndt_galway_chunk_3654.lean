-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3654
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:17:35.914284+00:00
-- url     : https://prove2.me/submissions/e7960b07-2c98-40a8-9687-347aefbdbc45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 657014388 ≤ n < 657194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 657015638 1250 657014388 657014411
    0xb0603040308101a09130e030f03010905010807050901050d051606260c030c0a031b2105220f0804062c03190317191406031c090308031603 61
    0x480ba101300b1060480c0c4d83c108003880c0100245954800f2a20306d405840756451062281c0500040545a6030105420380325414190b00008036801600410b0301c90788020428403d0b6501c041c109811964101e40d02203054185142850500340d001c20a8821815900804121031741c10de400c01b44e80c400c0b0302d180c410041001c042e42030803155055802071b80120041020840140001008100007648c600b408129044c003c800030a041604071644000a01d461240040e00c04d00c0b08020441890700328418052420407a02e86031000c08410f21003100e00d11180d00700c0040201d10044200c007280c010030071585541d034445015040141c1512102e010802c0c944041d600d41041003401480c44901400401e1150b45a5550381288804d645069092140c628071036030a103524090f0b454131607910b114510b50404101c1c801c0c482a10032400c40b894266042c9070410060b5200000c02180101003050b01c09021011000140e42c1034241c1e07000940504800020050702800310300c0d001c24410b850740d404010020208 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 657016888 1250 657015638 657015659
    0x60717060a03320606010e0f0f0603100518060a1707060807121a0301051003032a02060a02010c08060d050319140d090b060d0f0b0a0b060304030810 65
    0x48440319482882403009001040c1c12107888144900714004500810041c01904a80308032030811420b03481e40003e04100e081d5a10860303103914004140e940701c0c5c8814408000401c84c000c2d07414400e00801010000415013040002000000c0030040d068010140755242d82940d68401121142d001d0002100c0028118030344100c040c0705081c0b90000b0b0800a801e0481c11100f1210190226003005031822420907506802d1044040c422026014500420209000d140c01d4600040254000755111802040440d411064198101000742103002118100205401c09400300603006904414049211010340c1d40552182d2a4003069444c1c840c030503601c0904003e14020340210042840e0400d201c01407007521403034500200200745c4c2c02c000ea007900e850707140071610343c00200880c41055110b100745414070075250406500b105007a19242490340172500c6091400c002a00300500b090070140001d0441c0e0f0040d0320180d034868000700f03110707078a00702824014520381041e00c0c44241031101404c0080c040904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 657018138 1250 657016888 657016891
    0x1503030206070e01090312080906010918020f06041511150105130f0608032106060a090b0c070509040f0302010506030c0108070e01020a080d05160302040803070609140a05060717 78
    0x568014107140d91100307012100d4042c8216400d060080ea0400480001e002c422800380c400600da96400051400c3c0e08018508030041c0e01c01c2581c0362802455510010020158003406901500d00c842c8111100021a00500c580c2d8080c080d01d00c01040707203010555112165450400d00d0b6000c030b0b004200000344030303840c4070400c1c0b25042d4400e505030560b003042442a044440c1d29143d640000a0789070351002842d0860b800b1711500b82501100001000c01c070061440419008101519110706100e07034800c0c090501201b600a45103c20300c0850f1030081d0000401441c0d0241a010700451160305091401600900c1c1d2101c0460165007418005055414009401e1001000c16074070943c05880b003900079681900304c9110581140070b1940358034089500740c17004207980c0c40300450008092070a50380b110b001036404c5080004260040204014a81000003641c65a540001002910740241d10302001d081c0c0342c40350502503074060100e0544c00d000022480605c0f60305a901c64000c0b0300662a22005040c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 657019388 1250 657018138 657018143
    0x912020f0606040504053409050f0406020c031909060807030c0e090612060405030c01051303170c0910020a060c090b0d020a020102130e01060e01050c03390601091503 73
    0x1c524001400d070b02c1e080e003180d50000d000f001900e00d03100d194094003e505a280c1c071003030a2103881c4801c5034842801d1a4001c002801503a10401c4682814030050b4200340014001900301c2d40c0204605841e01c40c00d00c102c488585d03002d404450324504545014210440e24464403000c1404d9000140e8014003e0041d0000c1010581e200900c4405110401078403e00141280380c1110020b5800f440c041c400300450342c0500e006800464540c008025124250742c00104690f070303460f00008002c40025040303140b403140c00418064001d078680c0d68903213501c140c1c065000c0300b540c0261010034008075135401040440c440c60188006015000f600d1070203440d1084948282c0c000b08004000700c0503601415401b4107009022840094500310b044800540c0038002500008110400c002c01003144c5600300b8000240c690007800c001b418a503004001030349900a850f01400d089191280381d058405c482c0180b21540c2007103402e0340f0440c1240151055440009024071100a031805249003851040c0703046080860750b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 657020638 1250 657019388 657019393
    0x1807060305090a021003020d09112b060c0c082d040515070206070f05060108070801090809010f020c1e010206060d05060606070f0c0e0910090b0c0c0f01020d0912020f 73
    0x140c1136402d110f0740504170030110080543c28005403d400ca050701403039980718081d04202800403150385c100407040c01e000e2003683c0801d0850030190100f0443c490801074068001600144151b070303248054030780c4044488000d000701c00008a11030301d4101c0e00c20941c0025110f01b025011210a2a00d204240c03040b030250036404594410034030710051500000b4602544041c0c0b00a086c11a40c0c4d65680c0c401c2040c02c4200e410390050b800601041b41c0800c4010024201140240960f04940c0c54240d07480c8a4400050704004101d40c4a1b40c0320b5000b00121012041e0240c040752410b600700c032402c400e4a06402c2c21900600460f00402c00300e1034586400200d458200000d0a06900c9007001c00c8065400800221518440d0156100100e0711180c0c2c02401010511050f85a80c60503040f800d044c00c1040c140361107503a1a241941c0c010a241499003907210300c0b01c0036401e5035001c3c0300702140d140032406174162200b0b60001a860007a0400ca4010540c0c540c400d00300c0c103101c61070410081c0e0311611504400a0703680e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 657021888 1250 657020638 657020653
    0x200d031b030201021c060509070203070305040317090316090b060405060414150a0207030605071b1502070506130c081f050a06080303041b0b090d111206180706030509 73
    0x4500319406003400511038000146442003502038008600502e5108441003980c0354402c0100d07051071640710386e0002c61440514030f00b107031968001c0d1460045001c090a07010308080403118901c2007104850080710010304036050b41143c0c9a040d5a0920903000340d8241504100000100d81480405d8a00f81e0307900428403400d2605211016002e0704c80b4088a41e84006145800300c4280307200340051007032420583c0585251030642c2401c5040d2200540680d080005188400d1003d0a41100311040198070180c1840c049121070b031450064001c814015055000c0c035801e001c94154411192000144240608032003269503503c840d84507080b01c840186140f40781c2e0500b050109a951186501c40e030380f00c000003070240d1030b044654038503003040310101c41d40031680f81c0303201c000300e48116400000e03c010700c0780a10b803c3d0220007255102000100c0144654411a8001810780e104083c20b564500d0303d20860304285086a03174441c0074a130101000c401070280d09000720380ca034424001d00d48540290030040a20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 657023138 1250 657021888 657021917
    0x13050406061a03060f190608011d010315051b042315071113020d020318120703050d060806090a060c09030f1121010204050307090504030807050313020607200d03 71
    0x1800185641c176900014242e40420f00b030001140d01c0e40544400c2e56075045ca981040c1f007002108840c0c029000342c80841d04010000101c8050f589541031500741c0f804107803500e480b9881c02006080c0041407100c4400828003140c540440c0d4800c40ca10301840450792244c030002c20500050044030030140100c400e0402c013880201c0d000d4060b0030310807640600024121700000e00000c040b130300003860501c15981c00106002c003d44407189080054602e11001d0a4000c1e94400300070664071424034018140036020809245440d00743c0e05c4500100b84190079101c442ca80802c2040c0c403001c01d54000c917145450020902a4940303c0c2c00b940c81035950001004c4000034141d1100711096101441e45640300001c07081307200c032580e109801800c009400200143e2524140070070542814220740081c0d8505161104000109601c00100b5801135441c2c10709036501d0303e0380d40d5001b5000d00ea60300040e40000f0005034800810281031480c200d91074050400d0030600c03802e0300410000c00b0381c880002d0006000d0001c034149 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 657024388 1250 657023138 657023149
    0x1090207030912051014060102060709080318061606090b0c03040b011703090d030905010e030a0b130201050d0608160e090a030f020a060e0a03030e070b030106050d060513050406061a0306 82
    0x10f005001c2c6040700c40f1246600880c030700307880d41ca9030184075400400301802865601000f03075030340280817800e1924205043c0b85d08070b07550303005d0000c01e0a481140e40c100442c3c80e0300d6039000c54000f00c00d40c0305402c0804289040c400c01419032004101c44850405000075099201c0f8010f581c05035602080f0800725901e02050368014101e12441c00c0301ca030004100c170030802d82d112200b8080003172090b110308004070300d05070014100c00080c0701014069000104040c0c0001d44508895030b01c001002d981007014111400100c80a0290ba58440f02040c03524002040b000000907a441c044001144500700c001e0712400035446619041d80d0b66407182c0e205e4013245001038060128001c0714021481143c030500302c203403a190142c98484400c00d800d5000300031400d091660501800030114031440c0240201032070000659103d201c1440342404111001c81c0d0300e8460310183d0060401840014410b102042241010341700030030f0262400c9031994600600001e030b915041580320882c0d0340c200841c41c02c2d545d510040c0030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 657025638 1250 657024388 657024419
    0x31110050906030f0702060c07032313030b0f0105010f0219020103020c030d1b0302030603190309240215150d05010906060b220b0f0c010b060c0c0108010902070309 72
    0x50010a0020320442d484071000b03184180503c00e03812200c0d080072100030b400c108000e016850b0300d110800601011a410520700940c0c2d011451005400307012111074806180541102d43c40c488030165000030500c6181c034003050180ca8204484640c99030f803040151800c070180005880581c10582590788200e030070300c003428040c07401810701518003140d00c0009410f5a00c00345041c000295200201c406461400303200c81071300e002c5400c0851031410700030f00080d910700c2035040c1100c522010031044010580710355a05001061140e0340a1850b20f4444c110001c1041d00350600c000500c075032003589110b246104011030046440310305002c41503401500b40301c654900250183c070b80f5900ca60741e040005400303204180003441c2c001600b58590808030310010070310a82492200c82060321b80b005000b0914280c0c00c0300d116404958195981c0e50101c580d66025002c2d00c0035043d884a0301046585441c0c41c003140182c0350060980e283d0201d80e0b21070940900f280110301020300000c9142100f40241e02c58041c001c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 657026888 1250 657025638 657025669
    0x626010311030c13020a030605060f0327010f0501150804110111010207020307060e1804021008060d0204060e0a0e1b061e030c091302121911040b03100602070311 71
    0x4a0541c102c04010500c1d4003408244c12003190740c0003c507040807036071500c203d6000c1c1104548103403500701da4040c3c1c0e1001c3c1c0130141100401010f007a0381c40005080e540641d00e424544480207004110110789000d0042c40240f0824240c0e121010254020500c10400207200300c0e0310004a116520126004440c201e00f402d42050542d075081260b6005a5001c1140600910341542c80145110796034060125504c841c440030740b04107140400f48001a5141c402a000f405058a841c0c02c2660740d210000b284003d0226011390040d141c40c501140e04640d24802603c500300c1402d080c81952100c2804617540d401442686102940d12203144041740b90132001485051050044010010701203d10241d4940c015100310580318000595407002e403d00741802c01000c0710803e4110300f040725480300754402c9400109040ca14140a840e0902224079a50080c500d650840c52460f0300d40c2c1c0c0b02d298245095205030341000203090302c500000396103403000502a0641c1e609c0280420312103c035409004840356904400d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 657028138 1250 657026888 657026893
    0x1906061502060621070803030103050105071407030c0201030c03140a0603120513032a060e15030613051f091d0a0c06030504060b0d120306230f060408010c050301062601031103 77
    0x51880040000d5400303140032f0b200014842c20003080c040c0801d00e21040c04880c0c0b540a21044020035000300031030030003d80a080125a0300d40c010021001030843c082d003851020201e10921444401685c4030034140c070b102d00e80d0303402c0d0b50894080c1078840780682602035840304813494003800002c00004480d010038003501110741400074080d8610650000d82d4001800082106600c0c90551500340c00000c4c030072903040c4246156080a0b8007090021004ca00300192054641d400b08160074500c1c803030100c1d103201c90b418003408180c90b80707944401f4140354100b54400e40603082950a21660200300d504855070311051190b009031408d0f0041d00540f00041090b64082c0d40c07550860302130345403420803c9100388079071229002203501032005011124039030000c000e40f100004408040d80d61465082e07100c048101c0b0380c0c600e0f0b4140700000030018400c0b078010381a154246043b52044035004000340d070503a080c2c0e8a40c07100c1218034020480c08220582d000032064002c81c001040841c181038540280d455001c0e06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 657029388 1250 657028138 657028153
    0x2010e0d09050f041a060325080106050f0c070302031906110a0203030414010e01050c0306100311031306150b190e010c020906011b080c010b0f03070e091906061502060621 75
    0x6d689810407144401044030410510040c110408074403000c8d102d45080c4003400b5414243c1c010321500540d006039020041c001031060709110b04009150056600038204d89401290540700002d004000c0002c5510f030f418800c541e1205103404003034489003046540110700b1503541d0b0311040c507403412000301e010139550b88010b41040c001c420702880d48141c0030241210341c2e900b860b070240904181c140501ca01010720300384200880d03420400440342c002c8603100d040b00b400d590745e041a0004050f1000c1507911001e51580014400b40d4000c00b5104107080303080640074008a950080d209907000c0781540c0e00003102c0c0083d000042c5050910b0a803c5130040c5060340e641100d04c051810092128101525100350101c1c001c0d0002c0024040c600c1c07840d80a44503420030110303e0010036500c00c0c0038003603040207282c03500001b010018100b01300580150b094080c0e405002250418000030042c9004501000c04008802c030052400012282d00403500a800400c42060400e9928000720140943c610744d07026400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 657030638 1250 657029388 657029441
    0x70c0201200703021309020d0206030903120906391c0507020a12020a05030d0c0512040819081e071e12050f04021e011e02010e0d09050f04 61
    0x107110828801821004201c000d0031401045542c0320350001042201b818060b0700c6006840c2d8501c024030460b07050f10015240d1b2078900c0c003d41503005031411500c941503c0010400080000600c050165030120741c161425440b4039031903161040d40800d405003c00b100809400c04075a00c0c40108403841c0e260641d030104003031211404080e41d00560340352006034003400c1100140414a240d0307a00304905070004045904190762a26224062007180c508003a5454100b0000c030381c01030040303616004071078000e030901e46010b2134001d000d0b4020156048044d2452641c1c01c00e0b4900903140c482c000c41101c410200b2440700f08401c40c1c0d03001c800400360000c02001c440c8074901d401c003128002412000d591500600301680e5202101183d00041c10711800c0d08441c0240310240e214101d081200c3d0041100440c0d07078106000050b2841340c5000104c0031890360010304100b510707a041d40681c0c00c80304410180d030082008100c0403911241d80d4011607510a40399074860703140e03181c140d010318507250f1103614402c801c040c00d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 657031888 1250 657030638 657030677
    0xc0708120106050702041a0a061224030b09060f01150905040204090209041505150a021501060309031e0f030906110705010c1209110405190c030606030e1203070c0201 73
    0x1e038007800203d20046031420841c580343c09081c0303c1c0d030702c0d00a40b92500d0342d170a130002d5183d941c240320b420140842a1502c2c04100134581041d10f103907800030076000420744034044092066401e44002c3da0401107450110f91040310124455015114488480913a070f42003003000a00c09a59030314120131f00c4030600c4000340544070360010740010002040010380b00d490520038002620042c103174044502c2580b02092045036034100705000500d41c040481629068842c0042c1d20304030396029811454655000006005030781a080418654800d5445407859a01011480c13800e11a054442c000f16182e90030b0541041c0c401d03803015014078010030003c243d000c0d044401c106250300c594000d0700d0350394469030f08821a0780c0000d42d400c1742001820041145501e25215094400750309400c0500c12501c61010801160740800b204820300089a010071001140700000340003085284603042c04a0705000c423002840700c000c26062003249031302c0c4000f8656510018111503101401000700d043c400036152085e480b14a2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 657033138 1250 657031888 657031891
    0xa1e12020606010e1206130c3f02010f1206170706030e0712170403080d1a0a0e0c090d0c0906090b0a180504080c010f05040b18060c070812 61
    0x690050110750821800040c408582c140125000d20110007050300c0300400007a1040e0302c190358440460380b20200e031070040000265a808416a1044c080502d0034082c2d411a18554029040810f000242441d800e02111510804c901a0114441014200711280501001c000e0f610702c078503002500985903005016141c8008070040300907400b00700180610340d0180705c1c50842418540061485a1401c2070304003400b000c11100400541c0182c8400007030921000940d400b6581c84a481c1d40c5910405580c280101804420340c641c49032044108109810325404a0307091b0356000032002c20650341d442d0051519030100404940001414400344080f80c00800414050030480c0b801040241c901145041514000082680700e015040001c000281c01c0c0810b41c0952405600003080903600c605200800303004600d4000565403c0c0002c3c0d03c1c0559096000320b11591080c1e201480300e840f800a003032104280d04550481030f900c805d012890700b0203034401a14800e0310404180d8500142d01c06004a131440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 657034388 1250 657033138 657033173
    0xc03070f1e0206090706031b05130905010b0d05070e100e0a15080a050a020a0f0e0d0605090106170a0302030405010822210f0206010902090105130305060106170105030a1e 75
    0x4040b0074001d02e21401d005c04401046503140500001c0808403119200203980b100386018014001695000501c81c03080e0354000f0718601e581002590795503c03401743c103903000c0c1120320492445c0400140101d40101e244594a6a0261540c00380d0340780e0840690354880910100742c4c1c4060564000160b41d81030703004a08180c1c52507034940525017889035210054a03809002021074500600c0815007d55104101c80300503802840d2000d2000c0600001c5a60080c01d40c10140010f41000100049a0015000a021079000000c54040c0b020f0840030191128951040100117800c100803c01c1030b9885000280d40140c000034035440c40d1101c40c2c1c0200e58403040b1040458005024010003a17500710342e5080c2c0c0d41000003c1c2003c0201c049170b107000070344a84050260046659010a10a550b41d1182c0e007514211098680700c07201c0b080e200e0a040da9107240903c102000150b2542c009850110149156812100050000d1802840541c0c4600303984400c1141010310140c5ca0660350003203249910950520741 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 657035638 1250 657034388 657034393
    0x30e061b040e0a1e0b150a030e01050921040e0f1e041a1609031502090316031707081c02120a0c091e09050c1201180609050c03070f1e02 60
    0xd032095052040c220420f40200d4054507241c610b200b1515001d051b28403d28030394400e42d58500614006800030001150700545642c68041000003000000400d403c000500070f20a820240d940c1c5d1a00c040391142c0d0290010442c0e800f00810b00249002032071a4001d00101c406070364100c0c03012215000301e881250161002c00502c001c880b034844104400e6a00040c074541000e000c441003460251282044e480014060040c003504280000c2413581540e040c41c2c40141920900d02c46403548503802da5250100b1303a012156580409030011822040b81c0d8000da2080d0005c2c1801d04003200e01c0342004d80c02d9014050f960f020800c0401e2134510b40000c5101d0a0401c1002828800d02032005004880c241c0040b011000b00015410300f402410a403001100e1480d8004a040d0340c415045025500030003085003040c071132800010503440407100076030020180d1400200142580c3d482c8410660780261070090201d0744c1007007c500390b140f251781007902c0018a0b050019010120340300d00801c98501c04803140068 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 657036888 1250 657035638 657035651
    0x20a02070803122d0612010e03161106071703060a0314060a0c0806010e190306050106050307020f0d1d0114040b120603010c1b0c091401090c030e061b040e0a 69
    0x1640c02d01e40c0b130010480c6507121083c0306444451120a1078000b61042e889041840805c002c2c0071000d4200ca1602c40d0440300741d0761900035050b803031a10b00c0c00c101400c81c0c890019092540c814104075081d584200c0e004210600318035085117000484d5031002d0712194228240c6080800401d01c02e051010515040000500031450701c01c882d24100c0d07060742c401d841004441c6041c46002e1380c0c4000039485e103070421140d030075174802c031284c00860140581d031000709102d04040002943c0d6801002441c03140085800342c6040c443d038900c145450300f23034084d16500400e0044040a482d240402080f085034079042c144200d12100c0604c441550b900142c2c001c0d140c040740040c603c1590020300903c02e400c81c0301580280500124900090301240d0b042480e001085052150790042c0662903622200919810030100400600614110406d000034001d041c0240e080c40c025100eaa4800c2c41581541c3c035491021b003956071203403402001210161001e00484510520021034507000041409004102c40900003508 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 657038138 1250 657036888 657036901
    0x513022203031b08031906120f0b090a170a0c1b05180c0702040209060f04030614161e0c0501060e040c150207030305070c0e070905030111040612020a0207080312 71
    0x4410720321189901d0f03941801c0b111000101d0900540750881c041941058412022501d83e0005000c0c0d03600207410070445c803480e0401e100e000134042141c98010070101c0d01c03560360744d650f0b80c1d640d1040c05401013141401c0000b012941c2c220348003601101d88035181284200100c1d0300c1d96900800800141405803620180410283c030301031040042600065501c1c0b0014a480311100c0030314050444064055600000e425146580d800704803052280500086611152203041c06401803004c000401d403200580c1c401308889001000c80c1d4071000105179540b404140703050800901e809001c400510a0118810750500000c400f800740e6030241c180c1c2030750401c0c1c074509400c004200c034486a01003c1049540203607104810f6010a80501740c0b0b815040140e5590b0090ed0a0381d05012103901400030307290f0a10034481000d5109803540c0895408030300038400d0b18200184000c00d4840d51007800081060001640c505144540251100b10034038015900d15a43e2807001c0d07070655200c00c210300c400283d06005c02c5003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 657039388 1250 657038138 657038147
    0x11d04020327030309102c011d241e0a1a0402030402090703090507170c0a050604050d08030c04030b070e01030b12070302090a020c1606120216080c1e0a020102010b090907051302220303 81
    0x107542d00b1110041c0240c002c240440014501107649080c0e60502350b0000818064a00302c0500c0b00d4140a0708140031464655402c0c8010300dc5070b41003410101c0b54050080052925000f40c9010f950002e0049030244c6070194198014401c08408031034034000c0c0c290014a4449440d0f0076080c06e00e80070094807841a142c3c041282000103604520b10900c01480280b103103482d44402c0c4480c0c0d0341c2c032044042d03690719080342440085c016684000c0460795414104002070b0b5121114114401c0285c0701485003030a807000b0403c1c241504000501c250748140e008002502c0c00c105410307004480040014a00030f4404426400c0c2412a80c20075480103070206c040142c03d40c454048145203102c0101181002078040d04540800d0f01c2800240c828035010134081c0b90804240036040346058480e24200780340d00c0c80c2003035a84500d0b008900740d001d54038000701030b5040d060180d1524400d101050240c81c81900b010200480c0e00b24000460340c0240e400e109025249184047c29481186400303140b0758018650300c1c0041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 657040638 1250 657039388 657039431
    0x103110c03071e0b160315090219091a0d0b060703030c0224010b0318070e01090f0905100c0203041a04032f011d04020327030309102c01 60
    0x1103c10240d6400310046003a0042041d00031018500301c540388036080d5000c83c040d1802c0b82100000b040100c5000881c189294000c10181828134502107075460002025a1940e50500c034900014810740e903001380b0001a0001000110b01690f00002e00306804004140b0717a40002504030f011035600d200c46c101081e01002000701d1040007004072049030242d25001018103c043c030420010400c0400440c1c60550045c0980751000001e008465586a039640540000301d820700c22488140c0c6800c2e51000c13449041d00580102c642c00030000c100d41c25845415000070940d85040c0340c00c5000030b1001040640280054800c0080c0b156440c80c2c80e02c1c10341c00c01e14819541030410302100310310002a00b40f10000c58204c00c8110009082105100002402c480750707003018804002d40c49440042000980641000403001c0c1300d0300301e68910548002c5884c0c0591301d2000765098072a1f07601c0300d0207403201c281960304081c004101c3d2225911040320500c04012a00060031000c0607565140c1000d110890a00724201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 657041888 1250 657040638 657040673
    0x3031715061c05181218010c0212030c10050a11121302060403060e1e0a0f2102010f0e0f1e030d0c050901180609030b0901140c04150903020a050f0103110c0307 70
    0x46203400042406c4403914084061799505005803070740301ca81555607941c80c6c0e80c003003043c400a8960b140c45480081e500e075284801360b804120320701008100042e4207842003102d2940445a000c0c42c02507810102c0305004001800601c10b00c0000c8071000040c0c6800b400350000f10310030034005c20800c000c007080c10b0074a880e02419200c001070016074400d10b0b0724009581c1944c03d030495482ca4800d04542010700c03440d1010710030034841c0c0c0d500c8d090300510550705502c1821548400c6000300898004541e00707644401c61030303012640aa00100c0401d10402d11082102030341c08900701100d280c001222420004d803960103140350f01103030000c12491620b5800080c1009910740f04000800c001c2d0420b030014043e502c1c20b00018008881c85000039076590300950284072400e08030510348010345031900040c4801e40c00b60041300b04040003245cbc0c07030310860302860085060320350050046a0380b1f4100002d0000700941020701d141050b4440c0e5881920880d01002405030006030000303182d075a000c9041540d405854013009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 657043138 1250 657041888 657041923
    0x1d19090b0406111c0b0301140709060210052a040503060709140a03080412150e0715020708120a18031b05010c0b0703151802030103031715061c0518 65
    0x10500131584142c103003104d4803880c503400141000702c400881d0040c60780700a203468481c1c1c1c0c2c1082c007100c076401c9940c0f00101c0304980d0031985940341c0005420207540c3c040c0d0300118160a0701d01c443d00c0520101c100540c45012104c0450b06040c0c0e00e0000a1034504240c0e110004110210000c0c0410704003562000078162041c3e5040010030b20b90740d45c401c13051103544181e0a2408c54003c0c80020051740c130408507042c1c0c81010090202c3c140c85214540c85582505c2006142e00c1070700500c584007400403945100b1941d10303501a081c001680c1e80046541da005d2403180b000c00000c1c40c0c40b00c0e0f003003402034516800b842c02580900202c0503031a103140080c1829401050601c1140440c8000180e00304c1c00c00c681c4051103290100e55110100d441d40e29140d07030b0750442c034841c032101c9428031004a2141d0180d07040328025a6860514840300044c0d0211340340070f5401e403201464110031a0490b040001c000d150406001c8070b486408403540c650802101d10641d010000000c407039400e2210340c0740802c6950a80300c0c0700da46 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 657044388 1250 657043138 657043147
    0x3010e0601110607050d0204030f0b06040b0a03422408030f0918070305090706030c02031909080706090302040c0504061b0317090c04151d19090b040611 67
    0x102e0540c2d900c0000d1880c001c000c0c0020385604260001d805403401103600164a08190b0780307529100d20b071101d040701c1c0c186c0074524045c061842ea2401c0017840c001c40350400010200da01511904c0075a9a001c41c1d00c050f422084c854101c00e08110a6110000901c140100018250102e460454045d0700c041002e1445c0750840c0b6050103005030100444244042004120740d88010907000700720058003c4541441081e240010030644030f030180c01561040d065035040d541c01c1c940b120025000c8074000009c03c0010790040c441c0c8290002c4c03140c0c1f08202c0e1032440c10801052550342c145549011542d40082c00003c010241c104114203041c029103409080d281002404c0a0904500074508403400f0b100d60030310011f1031111800c0c940101900c0ca80005000c41801003464142d035525a90107a1084403030003a444d003174260100f810f41e10360345002d643c090344030300a101c40d58040441e00c040000d090344042144510810035004080c0c4158141144240c2070321030140781c40d0078070030110749060001d921303004030411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 657045638 1250 657044388 657044417
    0x2101080106081518011401030b09160504022d0c01050108030306091306110403030905030d021c050a090e09071d0606041802120f01090c0215041106071703010e0601 72
    0x7510410500b4500f04a00360f07581c48002c008034003814800c004545520700004a888441d0704142107042e2409807800c114079403654901a0390320403032110840b01712545003d0038000c500e020b400808041d920f05240300c44c611204290a40025181c0c0030f0031001d55000111070b407441e4030038018140145a104051400d40c900200841c2a0401c000c0040d2600f42c6128009000c1125540c0310001c070001400707042d52195200d03d0041d01d01460f501070248203219800041c0b11a500c0050404844c030310844840841e020841802d80e1590044021b02c0d05001400030301040002118400d184141510001810303c0c518080380310b050441900300b003041c4110458100f01f41515103200f241c0455440203800d005500005130b1050003802640500e111103030710300040c0402c140c6d904d83d42038141d4088820401a40c04404001c0c0d9403440c01d10710130b002d03a030034540005010400003134440b80d4484011300f90a1400c00182d850407611801010306401151000c801407283c4801c4000d0150b1100080c2803001c40c000b0040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 657046888 1250 657045638 657045643
    0x4080d09140609030f060a06050a05040213061202091f1812120905030303070906030c1d06030a06081f15120605060a181e09170a0c08210108010608 65
    0x6482030301906000541d2001510b08000041c0c0b400030990503240c40e424104070407c0544030b548101442001d003c5004107032464144201c1d07045081451b13880f02c1e2245444000d43d030041c4245807840c8440c0c1c0c24410440c96849044000100c1080d01080d44241e03034510380040e0408050349181200d00d5080303841880202495018041180d402a1601200075091001240d10039003507040140c050201000b4800001c0c1c004c45210103076102500e061101c20035125080701c50301c1960000d51150602d9914145560806600454200d04100030110b240c80c0c035555610319240703e12800d41034509542d6940d00e40c0400520908044100011040082600d82406004c0c0344480d29005410550f45030042901c0742c4d00d041c04000182480c8010140c0342c22503002110040c030052442000c6e415a0704010031800c03d00d4882ca40e080f075400300b143c40c01c05051100e10700305c03500001410700903c4854044000410710a00140101c0441e1010b011801c44070300c98040c40c60801070f8400c132140c0e81804030901141102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 657048138 1250 657046888 657046919
    0x90917071211030d0c020a031d030706050c010f091b0b0a050a030209010c170c0f060601020d0503090109060203010e04060f0b090105040b0604050a03050606011805060a0305130b0c04080d09 83
    0x3901d41141c40b91850384a6600314811a14410307440340c50300b12043c5200313801268055241d8020388400c4031104119212880035012044a41d5144e00805804d100c2c0c5805140541aa421002c00000f070202e00450907408a4902d10025158041c01144a02094070302c0120f00d4040c00d17400081d9070800341c02c460082d1950080107031031340a2640100f0408566482a480400d4032034100682c0407803074141e65550b40c5607500122401c003007030280078403032503c03404001500782c0201010703402014542407030f01c000c031000d810203010441c255498201c81e00124200380041c41c00f07800c01f000003c0140c24039141001c00c0b940c0407000c00d0261410710721108040e9451241c114111041030714089074410805000500794071654020961100318810301005000d400100340c1d103d0017082e01c60059400e0a800040c0096038944203140e0b0160301040044d084512a0704140d8100c80c02c1c4c1d042664030012590340d00c4c19441c0490302003e103004041000c000c003079400c210603503041009040c41d10400f42019043c0b00d407040c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 657049388 1250 657048138 657048173
    0x90b13140109050c0705100e0c030a050c010503071205040804150215180f0f06010302090f1003080d09050a11011b080f07020609100e01080601030c0806010c050c0a09091707 76
    0x1d40b0000501302280c844211582035510006a8010898250040d001816031149807002071180b2050702201d8200001d41c00303401e40d0400014103030001c0c111f004540c0d60b40014410030400000c21100f08e1120b000f40140e41c0030b82d100e800802d4489040c440c100340300130800300d4440215803012800b42c009031034104109070130500c2e07810310070300c0d20116110a500c1e1078040b56122805210b401c101402e000d5002c640c0324182c902c2226400c00503202c4280c1042040c0c0d054560b08282460b80e08100700150201d00204021032800d1000700c1e400d4195151241000740c0c05009856404041f404115190303801400c8810140764030400b000c0c65411074a031a50300d40aa00807001188a00041c0c610565841e14191816400d0040aa07008102400303002040d8040781c69169000c940c4c0d070804120f00d580070703010350b544644442d62141055a03480004507121200d5640544460155603404990b507110010440007a0410190100b241c60191821a090100c0000c021803844d00034840d100020707070704402060b100304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 657050638 1250 657049388 657049391
    0x212910080c0a230a1d0105040819030c02180a06090608030a0509030102070206041805060f0f010f17070e010e1806060703111009123e0304090b13140109 67
    0x50b000303e114100400c400c00400141c580070461801d260b51040410002d052603140300c9505c09000001510305004a02981c2130755001500c0740c0c84452200d5645071000d41c00b901d0704a06489503034011a80b41c2008800400d021481c43d003c101842000340a40001000d030018200616440d241017181c0301c1c01114088000c2281c0010801c400d0ba400350107481c2955001480e181d605c6644440f030b01c4100800c8640c0c80c0c030385418800001c1a42c03501540417906214098621500b4004900044a01e4000ba07901081403010000503905a0940003800394807620498440607078103000d0b040050500002d0420079440380b000a004020341e406020880794004400b60740f140c0d122030007407605440651854400f403940b489100030034441458035400020304c5901943d0701c40106909200c040350030b41007040664606602d49902030040c280c013151b411401c504600b81140030103010841c6c40c0d0030351780164407500c5090b4442c440e008081c54440461180d008081202700080c0081c11302002d1507d00c1481240079a6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 657051888 1250 657050638 657050657
    0x108060a050901121b080319030903300504030810140a031101050408010e01060306051e1902070f121b0c060c020a0902030708100f030201212910080c0a 67
    0x4102c85e581d01400c02c076503d91000e142d1240c1c00f696a0744c2280c0150340c60341c07004240b084100da0080c03050910964250380c0b5280c12805a1809051040070745103100d000c1e01c0051550355200e4854466a070245100f03030343c1c107241800c05181c8180381d06056085854035101c81100c1480c1d5944801281c0d0450343d101850020114591005a82c030707019075440580356509003110000402410362000b815288100c0c0200070b04c2c0ca502d1039241402e0204080e18204c803880c200418160a03000d264a00550407c82002d031400000381e80381003034007a180c1c0c1c0450343c0001d011411100c041c0c0024030a0340503051004290309a280341d45601d8003a054601c10f20050101c010403c8040d500c41d0159803001c2c04000720103640d2070400c00c00041c46100e0443d203049040701d070790300b011030f02d5450701d2410402c070f03074050f9510321405800d2098680389101d650400307018250349034951102d000303003205410700b0711000141e0494a0744642040c021044145055502003023841406c011030050000c0903640c845055207040b6884 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 657053138 1250 657051888 657051893
    0x309050c0105091810120507030302073203010b130f05010e0702070905060307090608100b0a0501021002160c03030203030a0e030307080103030f110709151e03080708040918020108060a05090112 85
    0x64030054100d54141b901c6044c1800621078005889811244240e08691076140d07034428230b0000c1118100c0309000c2800200d1003190500c0d010441082000e402000007030568a200c000815040742009013240c0302d0748801d0348810f003003098850b06004100722540c125061a202200070f40f1130241d030044d42915641e070300110300c0503241040035801910203144100a0541c1321f00c2c01568400f1859550228242403414403e028203243e4024400c56030181c000302503200b9100b501c00040d4100003181c010146420303e5400110f449654002c0003103000c0c0e000340d0ba990400b52060029115070200d07210b000d030310410038031100b1940044080c1c112030700740c54000990414003a00711008080c008d4405841d00c50a403008c22003002e46d603c001035444528101032142e5a403640518002c0084a00081141d6540d540400c00f00b240c100c0107058683c4150400352410307448500d0002183c00180c194817078003880d01c00c601c04558005c41c0c1190010700803244051107a00c1c100020700c000b4014065092210101d07080c0508 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 657054388 1250 657053138 657053161
    0x1060c030305091630031e021f1d030a050310140d060207051501030623010e0c0901051b030d1404020d0201030b18090c0405100b0d0c0512070309050c01050918 70
    0xc1100c03102d4070341c1740c0b84041c50400816100c0e0303208602c1312204015600c140e00c1400054140c003c0d0812403a103055041050b50718030010900f0004100310315100d801d4182c0c5008050004181c00d0200b610b40c0c60b1242002880014030002079086440d1441d2042d82d512440c2d62030002c4114120b512040150b500d10040c03900310f0500101d9801841c031456858008020403074103030020700840c3c040300c50404106288500e1b0885042c0203124886644031454042005041080014400508181811498441d0000e1203040440308000b0807003490b000131074205203400751401903203001158400c0d0244142003940010f035a9641d090320007170505a43e00b40021054aa0341d0400002054105036210107103080041151100d451402d1180704506d04400108210454a4040240e406040030181895041866040100b40401c070b10703810b02105001420f1003d02000c601c4d84a20815034000c101c609492800d0b5281400142c07000e41400020701103a00262184001003c00c00b602100449407074803000c002d01c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 657055638 1250 657054388 657054449
    0x616060207150e06061f09090b0d0c08030a1407080a0e042705160303090308030603011b0c1b06020c060306040b0405041b12020627030601060c0303050916 68
    0xc00e11070520850f602d503554081a03c034403c102c2600d480113900015100011000c070341608040105001c0b20b0180030480aa40c01241900740140980d41d680949440e00c0261080750361044103035a10004c1c401c45600d038400c11043c003000341504918100401980c60400c9806051000000c0262082400300d0a68071904000305a5084602942842c802c0b20317030083d10441c4000d025107030761203100c2c011b4a241702d05551120031a6050360781d6070041e5096580300b00c069440505070a905640340e103052064124000c0c502542c0e1580b079112008928602d281c9452003d0101d900c3d0204440082400c104250f00400c0c1c211680360101d807031681e25034800c8000b0740200120704059400038a0041003004120b01d1300071003a43e00100c5520342c0784090356030000c8241850002002074000000303100035112101100d0504420600c022855103007141c101c00408d2514009900c1000012000e0090505060301485500e0300151104003600481c220310500c075000c5803039407150303580c01d05901e03901c1c0608407283e043d100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 657056888 1250 657055638 657055673
    0x90114131b18060608010506090a06080403050f03100311010201050c030a020705160e060916021b1212031b0c06040f051f060f091803300213050616060207 68
    0xa020030320b840c45807400030700190248002082c084000410140f808c2000d40d00c6000006000c507185c0c60034094205d509440141c401c80030b00030103000b0005000d841c0c2d000741d031040302c0304050402950300c1c40c200444261100450681964513140a100481c401002280e0740900080d001603910040c0781b07049031400d591035024091004545102280854195104d41d001d800c040758a10304c00e0711080c0a4202450118140c000941d01007803e4402c1e152880b404856400401401c0119413103071440c050f402c0c107007680d81d01c1c0381308100042000020b4044072501e501600ba540002411705150b1141d0980d947d07030103400940150320342c9020808022042101e0354031076541c140608180b010012280029001c41e000d12403070701514450125001c42d403403080c1c407030010306200d42c142000815203003a56004a083c00c41c804034a1058101510091502240c0904100303c12006039211005040c8a0364070700700350000c612414003040300b81c800903071200c4680c100c1a00020010b0b9170b5a00f81c0342c003544c180a2201d02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 657058138 1250 657056888 657056909
    0x3010608010e1c2102070204020d060303030c0201020703140f0432040b031f023f07050304081804050901140108070605040e0604060506030c03090114131b 68
    0x4160a00103401400701c1d0305150741110030041e4060f128140860912604100203241840821448810f503665614000300380603005103013034403039008a401d0b61700942c1910f0816880700400c008242d4180f01c0c903810385e00d00344001c500780001c941e401000540e44402c440444000410381f5012040440102c03002040c03420501c180300c8141c1d2844501e001e6804880e402448142c41d1801d52500b054068840d24a0300207001c1c058180440c000128040303148040080e100390309104001e5500c04080810320121071a048000190b901c0003a46c0f0038901c6404282d04003101c85505001e802c0360003200b9207411907030000031aa1100388070a040100d801900424651003070526080c0482c03928103501100b41c0d21002203804005a80359400c20340d4410b02881114005001000104880e81f1108035003504444020000700e50290340e0310002c0c4250700300352810380714102c000041c001901c8092080c9417002d0050b0541c11030501d464140c5005400444101070400302e25288415240404401c508002d00103070a003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 657059388 1250 657058138 657058151
    0x402030123100821030907031524030201050f391006080d03020903010e0102040b271c03021f060f0e06030a031b081c1d0616020c0301 59
    0x10079039119402950300066070450301c0004036944202184007404080012000e4085007020400c065003580700400880c02401522004000616050740a0f00c4406100ca80402e00c807408803907034030701855544055009841c41070020030051341c000c029100303071952840020343c032501703240051803840d04009804440c04640c0d0410b80004640c000c007000c0001e503940c0445000700401c0614004540d4503010702a007941c00100c1c002c80c41032198000740782506000d070003c915603110744007103420fa80040c0c019580c20300004c210900501500003414441e1400c101c1c16512003481b65001c16001000c40b2803108440c1c030f0150903201032500802c0350a50348040710205208107480200450700910560160100381d01007410005101d040180c0064014400100507001c001000e503000d0b5000440007940796080300c01d0301ca60401240e02d1a0240c81d6002c40003c00ca81c41200000f40a0102d0340401c00580141a01c03400590f01444009101c5600540403008840e1f041000d0006a140258071f5044a0b4158200035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 657060638 1250 657059388 657059441
    0x60906120109050a14030c07292802060727270b040b130507180b0703030f0606050711011e0203070c080a030c12050702040f0203061509130504020301 66
    0x41c281c1e10140c0201c4e117241120449500007500c030b2040c00702c0c0350f03080e5110250502203141200003003178801d000c030a44001b0174440d610454030076400645c96100828011710f244024601c8280400d04400c0007032008c0e040303034640104050305d88200a403a045106442d5200300907801206181e0700d015094110703071400240f01c0b81080320111000cc402c040000c9003800c0380340045041c5405040a041c1d002030404942007002c030800c00007090002d044004001031805204141d001070803258015003000d505055031410b07141000380980354250201407021386000c10400400ba442002da501c00da0f44101c4a400451003000103e0384002c00f001664108041004180d0000c0e800000070083d2134860701c109000c042d6039080d4117403500000304000e40440c0b8050b0300103000400100c101341012080d4184241805460780200382200c2c1200031b2620750300e90000500a8919000b0901780c0151507040f421450010b6400103d444c0201c025921a0b034591500040760443d0360a4005050058240c641d8065130248034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 657061888 1250 657060638 657060643
    0x904060b1201020a0e1c06050903130608060a090b0a05090a06180908120a0608120d0515010e01050a020717072c04020f030f0610210b06090612010905 66
    0x100c0528031546503403009041061040c025903c40c100d00c0e80f20036803071a070600140000c00840c0461511a199000000b00020f9407234402c0c1801500150b0055482711246102002241c07c240c0000c0300b48030780380040100310b030b030b562401d0000d4481090021680400c15004100000c410707030049035202c19404100030305080158030072002c40c0e00004a102030f008802c0f0140c01200c20b000c0025241820030410007180c510340c0c5a01c981c01401041c2c00040c459501d41c0094186003c0d1030f070354070740c9000000e0b030011122064010030b6040100741c0282140302207175030b0000c0c1440c1da05800c014188107003c51840d90060081c0050300003843c074111000d140c1800c0504160316031f151802070741411f4007220600070908004c068800054880b014102c0b03a251159000c2181e0382101102d6654036120342803041c0d02d44a400d1020318042d411130000c800b246828440fa00c03181c080040181505e40a100c05600c01250207100c1050300800706450303407001c640301c6102040740700001000b1400c075903003000507080810800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 657063138 1250 657061888 657061901
    0x2102010507021b0f01030b1504061d1f110c0d1428022407050105060f0609010203031906030c060f180b07060b270402030d0c080a050a020c090406 64
    0x100d5095880d6158031551103003031070f00c0390110361342c100c248403000c0c010350b5001c0d501c0710071070b401c0080025000e0144004826030640c820b40002d40044e44641c0b115014803000056400340307050031100c0b4014499181403422040c1d00940e101010080c0300154205084402d2080407461003024200c4400c42d1840d080149150095940381001e9104001003841055a64a1030440800c110908070310301c0881074080003c3c50000403c0d0209800070f1081002e003d4100e18001c0060500c1600080303003a107000001c215410449502c201d001344000c20095807503070b0740401140d0f030000d11455a80c190b002c1c08807200e001020540c00c002c0c2020614400443e1954014241d400800c8c410355503070707280042211a0320319180c11440380060030b58041c03110100048054014017107050014140150359076420841c1d4514203101c80d6100e40010921007400f042d400c080c4020344981c1c40381d040280c1c83c650980c1d249a01c0303114003c2c010003000004541d03049124424015200548030080c1506818101810604001d200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 657064388 1250 657063138 657063151
    0x40801141008010606020d0309050c090a050a05060102070b0703080912070c03170f04031101030b130b01080a02122701140603011535030c15070c05061321020105 71
    0xe6070200241d418014000e03041950180d40c06400151038a10090f40a00700c801c40c100c88501940810300403640300c3c041c01c60b00c520781030301c0081150700300b40100404540002d880a4110341000c6010b121311080075085406055040c0b0302524113a032443c14a0342001300d040b181d42e840d0000041d4000500982c09403071415a809900351001c006100544400c1a10400b028600600414402080403485c85948806044018180401e0365400a000034510f45449450081f881d0381d40c1d800260196801700005074271410703500e000c514040c140980c8200445009080c1c103000d83c00d142413803d00320300001c00b112120803044000c1c000d040841d0800d220417502151403034003075840c0c01182010082009506400c50b16089058410414608258002c1c07407580c50b0f985a40c2c801203e0b4040513010300300020134110b10031101074406240c1594107011000b801400010070448034801d40c10210b1400b140300c9400c91000910303c04004101e103001150500303054140ba1004010201d5010003030b0301900300a11800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 657065638 1250 657064388 657064411
    0xd0b0d050c0901090504031e0e040e010606021603020a1205070902121e060a03061a030f0f0d050408060109021e0a0206090601050d03120c021207051b1206190204080114 74
    0xa80b80c2249008a502c02c46d00039000542e0fa490303100c04411454841c1c0c480c180c203840e00f0030341c1c1c1445102142c10b80b410305039201000c0c0c1d90381c07004112055051040c0000105481f02c41c41c602880c44d000500b0038036240c09120f0054580d183c4030f0b41003110421192008060202d019910f0f4123488442c0c1c41040811102042c07241c4001c8440705981041c40041849403200401150720242942c590340000c4c02c84149104020346d4600c212442c81e5410010301c100e04050760010054502d0341902282001d0401c59400140b010610003880000d030042001d038103448850600503121010441010407039081003088040185000401c85074081d03012a106200365651001c071021070340e0b524144005440c081501070000740c403038640104403030100d42000416028510407203448407501d403051034060780404001c4880380d000c601c140480d81c045103c14540701504680d43d111418813413071382a0300c43c1c100170700100c80031000e825000c08900107a4150f074054080c8800030005940e0b00c004000000740c6c280c0c2d1080030031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 657066888 1250 657065638 657065641
    0x6040f031a060604180f200409140403120c020c04022701110a0204052508330913060203090703030201180512030a1407030207030e090108060c0d0b0d050c09 69
    0x60a00000300c0e070454075070b0f1501401d03812803040705da0000c1100081c00d03244c04e40c0302c41401c0104441e907000326008098030020743e41e80e9854940c034401150103440113121286444e10400001c607400c00c0c0e002c01c20300d2050380b012492111400e0124200720180c019036502510201c1c0f811205d014640030300c11090050b842c03451a502d4208015110f01e914061641c503142e015491490050605800103600010a070140403c081803482a15180c540c3c1c95281c0800981f541d8100f1002c4000c2c00300c042d24559509106801074190b5081c50705c42c0498a1103d540113030428804a003804960030703140541d442d0801011500c070306050350b15540b240c040740300c268015070130075103130b1010701c0c03ca100405049540600100b28410101d0341c0400d01c2c1c0c000800e015105070f07641812403070a9141c240c125101e1529070b0b50040c0e81d100e80c0d2902030414440709100728001e07141080103200701040010415004001580c50071b0325010340361030f43c40142c014492a140c011040c00c2030030301080000900c20468800071900010710303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 657068138 1250 657066888 657066901
    0x2010807020c130b01120212040c0f0b04031410110c12090f10050c0313172a0411191e02030306060a09082401090605010c060b06040f031a 61
    0x60320301101c07149a001c026602407040403c410307070124151600c1030410415015501e04c043c0c00326000885c1484249010004110411400c001160050301400580554441c1040c1803220230b0300031808010031240186241e00704000040082001c524010801480300700d68035410038140380c0060300800c0941c803c01c2c1c14500c96000200c1903480d000c1000d0f0116500d500220100144030085000e030000b030200070400001c01d103200780003c040519241340c001034545e00d080f40415401c83c000e8040c1d00c842d002a12007002c800e001c0c1e401c032200d000603144000783c2d1081e07100000d0000d114100c60124490400500300104c03e070684084c2481d040e06494100e0f4510007000c40c50f90446102e0705110050308200f00040e02490160094800c410315864100d000a864045091a02010103002c424450b001e500109001c90720744201070140c00c200302c0501c4814503080010381582180800100201d0304c40b4404059522042d0030341c3c00a0001003084603000307580781000040d108100000036004041840020b02e0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 657069388 1250 657068138 657068143
    0x51614040e100906140f1e0601020c0907020316050c040606090602031c06150c0501050645070518030102040b03010e151e010908070510050a030204050402070f0201080702 75
    0x9028101038040c0c5010001071036040c1c01071110a2044491075036820f00141c2000e00038644901c10b900c0d4001500c101d08020003111101c2007e004000d4044554004001d03c0d640e0204071840c0d4800245c1c0c5120450300d03440812b03403e500070440c0703085800c942ca01800050040001d01601e2044003a1801c10040b070721908100e075880668021840036900030800c841181065148031605008503c4000039015103480c1d0982c80d80090032000c0c00040d180c89018018440288038041e049002140d00ba003099003103a0302c40d903c25080d03517440740c03100702410031902400300a80c003070800a007140e00c07540c4201e01c2c00d001c02603c1c54012800c0c800100c0d1070a5082c11903400c05108a03001d0307441080c0040e06680c0f900b00808a1a41c0c001e14400305034443d030324485e00c143c499100d2000c2060101e4001a06105500001040b809450740602c1c85580120420440c2c0d403580000d0042c520094500340769245031041c0d003a0060300c1765074080351b00302c0d1000130307000144603851000c0708a0a100342c0c1d881d5a140c03a20f81040303a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 657070638 1250 657069388 657069401
    0x31104031227030305030103290601030c2007030b01091a040f020d0e100f051317070b0c040e0f09121305060409060e060a12060c090305161404 63
    0x24505480610051a40307030160541d00c049528030018451021040820b80441040a910407408100c0100040c020055844810341c00358148a1845010000f00840e0443c1d00e04080d00300d6050540c0c40c0c290000c1144100c3c206403442550f01c1954014a00b15403185540758410701c000d4403462030782c9001040440007400303000f000400340070380074220b180040b00700710042403001c0460104a41c20000c3d1419101c4600030401198010710140c20541a0401960b058452504030610f05a18000402c01d8100b60104030001c4580c0040c0c1600c81d000754480d071005288107030540500708140e18000c008990f5000c0006100f074490080005449440d049004241404260f903a2241ca411240d903040d01480003d01400c000302000304003000309991800400c849522941040822680b40e038414000c2c2e131208140950090015500700d2080b9103050f00303110102c0017092000701899160308410101500c641c016001440c0c0150640340d041058442c90010b41900e8884c50541a03607840b01030290303181038410003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 657071888 1250 657070638 657070643
    0x806120309040c050d2901020a050616030e03040902041d0106170903041d09120702151c0509100509010b0a0306020c120a0f090e0c09060306031f060603110403 70
    0x560800c100301c03041001902c441005407040040501c5140d000509500a00c102e00c010f5032014000690b10140da40c220407242d01c100c81c1554400c0b44042d00150000559a03880041c045d41050f03a2980c0c0d420450150858000110407440081004648458141d00810465001d100741c1c05280b4103200c2c203034410090904c5040c2c0403544c115445202c405004401e04d501282071400d403031601c0e03143c0302e00c810340038000d1007580881e138801030070440d4045040094030039440e115010317142441507d034009400c1512a094031806200040b130300154502031304201c0d14141804103400c4c0305a18281c0300d1640d40b0501c0c00146034403d41440013181d040d080611506d16840c0001d004500803504685491010f9486203401d4009881490194041060703980090b1680c14510f9541c01f0784012210801040304044d030f00030036614542e032028449800c04060403102d1150040e07418035280d644d5580060308100210944914030841c5d0031860040d54100c1d84001c0965255880400c8070f16510840c009441c042c90000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 657073138 1250 657071888 657071893
    0x60501090f030201120e0615010207240f03090b310c170304030b0103030e031e0a15230a0c0503091506190f170d09061b02060c0d080612 60
    0x10b0000d0b51003240034904000b0f100c01c0204100c0c2c5402c0307010b0300e00002201c1100c110444007646008943c0d0511540e4010460a2800a02240110104540c0004130980c200c188004554600005402504407c40f82d5410820801ca24681082c0c03509851028050b02d2285600c07006410f541007190b00ba50300f44a9400001a40086040521481c04101c038071070b041807140b109200020000e80d1841c201ca0207148079648070700b05084600c06141c40c00c1500d002c8900f440d02031130211060050001680304025030040d0110100c00c0808422000600c160700d50300d105640c4211540a04000d1141c1042c0100c080d0f45003001071401503101101d4500040e20032400715041084600a02083e41180c00c1d08030b400100190703802d40380501426011810b50b030244030401c2c3d00160400c0a5007040001c1000e9540c1c0320302601c00b90f16100c5005102c6005402848240300c04181c0c003002e16601c4440d144140e40e80500700c60360b6429054402a81c0303000a411040000e126080040c280342440842c0d070400b088090700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 657074388 1250 657073138 657073169
    0x3031406040e060406020d0603080409020c0c1f0507020a0918020a050f03060606030406110a031a090c070b0c0f04081c03061206020f0d0507031a010e010212031302060c1006050109 79
    0x145c10b000b0390301c00ca01da010195142c50300032012690710070051004003899400169128118034a00b4240595414964803480400580c031240d220740c141c4900e144c0240345011507803031f52140300103180700d080d42d0010541545401054032291f410001a07a80003402200c0000b812607a91082081d00841071295a406800640c01300e240e5080c903501441c1c00038420700001c6450880d000d910360250300502102c00000c0d40300c0d061500300c04042c144200c00d030340301582c0178030300c3e80b80005008040b485003a80081c10681401c1c0011200d909420a44003030b90042c802107991a0b035903940d21942c031541c000340300135440c000241c0004440d000341305190880b80b24008856500b012510b41038000d40108400c10724503031080241541d03810700d41c890507200342d5031506c0014003182c0d102000980c8000312055107050103d00380c0c0403401a85c000501c510388800700b13900d80350b9270341d511341300019038102680700250081320100d1030f1300d42483d002c2801c000751501c0040030060182d41d1001101c02810303500c00c0540018049a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 657075638 1250 657074388 657074393
    0x3050f040905100e091908070b0f01170102030c0a0804032c0112020a020718140106080f0702070302010806191d1b0304080405060d090f0c14090910091e03031406040e0604 75
    0x6c500038002c50240170103904084194840202c07074103046429088400b00d940040c841214010480b2042000300b038000c41c02e40c50302600c0d1804a00c42c548005060107042c000281c101480b498a6461030704402201d0351100e13a0030341d580011420303500c54a9001c1500b07104003a03500403840c03007611200704443c1e0003044520700c1d0100810a504c0d155a00400b01502c41c1c107000122041e8003116070080209a0304c00740289403d071440302038440042d00d50011504425010000350307070303c4a03045801c03d13030446500601172880a8100c59a030055800180b80150440146402d642040302d01c13881446000501383d4210f0055018291703500c0b0440d8000d0044109100920550610354090f18003240220f60006040b417070745c0c6680c1da000c01d004a0447d01400741500078060120a9030301e4207010b00342561110010300303112100b9600c8a40980f03e0350711007695a0030f8042408110154842700700721004240d880a0f54909004014000c014400e035021800c1001080903420f0600c6059041841c942c05404030f6161903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 657076888 1250 657075638 657075673
    0x50d2403021c060c0804060b100909050a0207050a050307020a05190308070c053307150504080f1815041508060a050a0617060a2103050f040905100e09 66
    0xc002c040014401c0141c0c1000580c240f040f29901e81e800c1d10381c040c1d10305d45881c018003a10004580e4a00800188502c40341064004182106840d001040810300713580390001100240a0b00c18064480d1242042c400280080400200500ea00a4804484840d00c810074001c0800c0700d000080b255070140c00c82000450320050240c001036105c0c0700d003040400d56620004074620b1950040304100044022080c0810802c1442c0711030b898201d005442c01c1451640f500940300c08820602403a15450f00001020040e820303044600300f0751141c00154443c1c0520210358101540d011f4000c0c0950b14003c44506190115019a0112808001c180c0a45200c845044580800250007940c0080000300302046650f24501c184000d80348642d9220942e01c50080a03e04406000e00482c0c0130325460101840b10205001202002c10f06c0039904601c3d4541c00e00d000c031241d2040465400c110ba00200300420050341c250051405540e516001d01002615500d500a001c0c000b40e504002039480000c100201c0040c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 657078138 1250 657076888 657076909
    0xc030702010b0a080f011a010c021e06040e1021031d0303030108010212010f0302010906051606140105090912090d05072d12050601140609040c050d240302 68
    0x803840085501c5481c0c0001c41e0001e41690409441c0fa00712000c0041651424826017042e6500905c1d1200c0d501c080b180060507051204201078043e260120b115450060b4402c00c141c0300c000040c2040380e94030307598113141d8070085007034590030307034072410480001649014601800b400702000c42d00030110b010716a07400e86805410180203400118012605903840d541440958020240c0c000050707990592000040c1c16070a058000e07440c6e4241c03c01c014000350340c1c400c00f4242502c03482c0c18801e0380c45070800014141c480f600710303004115908109010030b0028442e212a4100e910542d031078145a1121000503403200c01c0e42c120100c1161050000360400c2c030f05030a103007031601c2c01030007558050b40e21005403118041303080d190f00b41c0c4940c4009829000140d0003079184020041e60340b40d096024101d58074036407281da062061240b004c52a9450000301ea0b0340c0c00131604078440c0103104220000d4044c4029205800c0b025032035a4880c6001069440e00e070b852801c42080700480c2c2c0d654aa014210342c2003103100f610 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 657079388 1250 657078138 657078151
    0x1020705060d15140a050d0b010b0c03040f031101030e15061c02090a0204050a061404060e15190834020a021008040b06040905100903050f07080d05010803030f0c03 72
    0x2122071005043c00e05603686400030b07183c0072a04003611000c11090101d142460743c4413502400b4500420008254921f49441c1911400800e9555848803450920301d540901e0700300310041031011b40300200304240701c4807844941000f80c805005125503002910386030981041c4030340c2040007500c00680c291074070714480150a18100081c5245690350b4000c1590b18408035580b401e01940058240894070f00601c005005150600e84512140d0084d070f906a0b0307900640c400c0b201030150100140b01146d44640c01644000c5000740c0e0a034840c0328602c0841c1c01042c0350803100b004a2886400326200c501c00c4000e04541c4c4590f8591010100c030746107042802e80308151598011806031803030910060780c5600b00a50700041a940d0040142003c2c20800d42070007018100c1407240349040186800510080382d01c0c1784c01c0c02c0003c0000794400c541c1c1030903036144c8901c5030108005139002600d081003010f070801520004116900070842c036a01c80e842c07182c0d01d12060314175105080041d400540c0002d40702009550001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 657080638 1250 657079388 657079391
    0x5070210020f01061217070339031809150e060307120c0e010e071e02160f080c04181b08070b090414040201210603151d010b01020705060d 61
    0x4a046040c01c42c1c0054010703145d8420480300003002c1c8045a411000e100200a442a00c0c0580b15a009010124000141800f111703514001901c0d046198090091104440c80c103803600000f40c3c50000c1581520010a520340c0c25500c0d0003141005440c414403440740e000494121400b03061295400c0100001003005926220704079000c06d075451820142402d8900c21903c0301b011509045500c68400d00507000f4040000d542c0c410007411940c450100848003034420020607a030a074004049081240d0844502c007401000600011420003050984084400c61816039402c3c100c48001c120680e01510680c0524032035540300c150106e1250030391307441c0c5018200148070906070740e600040d0905845911044c5d800d203000c40c0e59002030510780600d050500354440c490f41d05103000d0f0b00203486051075007441d140458884c065481d62004991040000c1d40d00801e5100d415101c10303c0c040090b0100b035030f044900b00c161211100c0020814003a03001c0031326058014106082c285014482150021040c12300f10f00e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 657081888 1250 657080638 657080653
    0x903030c0d0b0a060f11010203070c1e0b071e021207030302033112030207120f0203090424050a030302070605070305090904050105101a12090c18070801150507021002 73
    0x5035512001000109845e0326914140980b2210140200d51071285846041c1d00400030000c0c038940c8403400c450074a41c44008042404c00103072548080d08188000280401c0f8514103004403103421216203118000000001c0c29a070f40310354802c90721012040600c903024a028415080028000d030042d51f40701e190701c2d030b4079040024014101d00380888611840b048881801c1d0104080c8408007080320f01c0d030384103070038150715140041d0b450303180080d8000d522030101314000b841d00c14414400c1c4102c0e10b8101000344240040110010501d050005050004c0700020111000007a64101280c1a07400c403a01900544551894040265103c4c1e200301c00480030803004024008807039941c0b80748240100c0c01980009824503280d80300c0074003590960048030301400041c0102c12440c10500844c0d11210310f80c04c4100258440302d03042d03442c00150784442c590026410b50000101c82501004511481d025610303103c80381d0740c0b103207403100001c90142c41500181040001d140503062050010200c610544111502c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 657083138 1250 657081888 657081911
    0x4030b132603040501050c1804050403030f020c010b1806090109050408040302060c150c1603140d050c031623160b010b0414031914101a01080f0903030c0d 68
    0x94800008240c0e0781d08010080c001848424400d4662140c3c008202c0c0b40b0b80000c0c2c014085800440002c464070070341e142e5000808041c42078004d20a600c02140c07040d902d499204680c14068104801028000d010480c24842e003014030304459800f8000140c0060a0ba90800e08141c010b0b000c02002076aa40078104000801604c40c50f0040a01502541c05440d541c3c0c40319242e52660000680503401d50b880a1040213160b811840c00c05541c66810700700503035600011130007448940600000c00703941500c0c100c00c1041c00c0413103400440c8581d05800c560011540c2e003001c04d031092903810220460003480102d1100310050b07810020030500300084954140214150381d051344410090704400302c07649011404000002e4554004109800114003400f407205500d82c0c40a0009160200a06410b140100544000301c00b070040301214582c143e0309002c1c100040759850031800c004808640020309a030005003079100f0841801d0302440d0b0a202840c41e40e103444182a0181e0010202c1485031031303a23030851004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 657084388 1250 657083138 657083183
    0x1a030c070f060204061b050615011e08061003021215031005070201060609080a110f190f140415030813050306043005040302040f0e15010f080304030b13 67
    0x800ca44105000f40e950f508010300108525880582e040042890101d04800120b022079801d0381b0200100b010b548021060300103c4013180c0c14112083e00300b1aa80104003a82d0740070040d14810807054400d0054881100c10803000c0340b04800c0c103100b2064a00d000301c1ca08041c0c42e004000b00f45002411600a1b00300c19901900b19241a940708025070765512080080c50340100000c07000b00764003000b8040300c50564403100d9100e01c560155911500e56509440d565a840c0c2e01d841510080050740030310215101c03520313610b8450703150040c14003030f10001c0c01031065464903001d8003903032100b000c003403410085c40c550350900d198002c4614200305003088400407510b034070208043c600c02c0380105441054400c0c0b041014010a01c03150407114600a030401d00c003601e50300030003100c00700c81d415200010f10010700c0030554020450130006004c64040d104030704a804a1548800c1e068615008040c94607966458886580344a2480300400500f003010014a5841400c044060f055000d06055002462444010310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 657085638 1250 657084388 657084413
    0x12030f02130305010606110709200d0b0f0f06160606080d030515030c100507020324060102100e100b0a080105070203030f160c060507031d0c01080609011a030c07 71
    0xc0703210341c0803842001484405d00800700181603904100b6110800440440e440303040d00e00031a10200d40302c400d0303080007099906990101c0400c07801351a0702c4022981d40f21001e410000d010510542803d080151180b40907060b1001846008240b1850a51200b03840c1d1406020030701d0544646d42d0301d402c00140c1e141c8c1031150303c411042560300044c0b24a800e410309442151461042d40c02031b4016861a08075807180003881064070030b94245181c58841ca0f1000a152200c440c1c10001081e490350780702001c8403160201c0e41e01a010036006d03a141c201c2500d803040d0031200742c6895903840303501441080450301460752007d03c81035009404c007003015461341540d84c2034440580384400103900000407c80c07102030740300540f03401c0740d0110010914000610401401c0f51b2418101800c541c0e0b80b1004a0802406540074240b4920501088486101c1100816850f1021104601e012402410000c0c0341e914184c01a00c3c1a110510103c0311804010015850503810051640880c00c004000710804121100c9401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 657086888 1250 657085638 657085657
    0x90708070e04020d020a080a050402030604021e031b09070f0504090b010309050d05130e1608130b1503240a0b06070812060f1e01030216081308060601020708030712030f02 75
    0x56a6031442002c01804204002c8c100c040b01c41c41c24042c8070050707502050144d00140c04440d0401e00c044040410003040c0c1084243c141e00d4410110700c00e00700354040c880d90003020001c407200005590745e19419103406487c90082400100308000c24408400e00f98440050352006160010b07011896a41d5030f40391020303030540c003404500c0209000e4800c0400f000c1c120050107402402c41824140300324000c0e08190480150410302800c0d00010f455420301105c0d980005421542c03005160a041e0003802940142d0b0112500a0007003103406042d024504c245009501030020706d1400c81ea0f106101340c8010100c2c01c40c1c2d0340d88410200042c40100e01050041c0040100504000c1e8140c20048100841d10391034207030b640d000d9540030b0105d5500d0844440d81201025003801c000d130b035559026410340702d141411880107250440200383e00d4064040844180d0030703180b0500c100c1c0c0882d04c5130300042e0ba80c0c1d401d500c16480654010004c0100040c50080e18040b203844c18100807600304000312001051780c000d0b4404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 657088138 1250 657086888 657086891
    0x1e03130306050615070b010b03040f050d0801030204050907030b1314060a050a1a010509130612060b04060906260712050109030806101b0c0905090303090c01080105090708070e04020d 80
    0x340b041c507280c5102c3d41c142d11340d0400401480c01c851a9104a581d8205100c2c41e0b1b1007000100000d01401000003945810f558404240d9501040141002c0c060100a01041c0c2c015454000010792440c00012008240d9820940c40e01c4070b40c0c1c4128139140041d00500080383c096115041d402c2006104018440c0180513041011840e03140690226080398551003541c000d5121601040c88035036040021250a0003055600c4100f0700150202d603005081550302246410110078000424460240d0010f048403030308030703410300429075503000b504141c800303500825144103075a04414604042e1405218501e010442c240d88006607a4446595072a000c41400c0c1d030b103a5101d403001001c1507840f0f4161640180220f503a003201c480e41c44401420000b2080c0ea90f654280f0201542040c080d0542d62030000f0080b511081c407103842d00c5650b8075126001901c0d04030052082000c81182980500e170f909050b10b0340603060700c1103680e070386208440c00f01c00a003001c002d200c01051802055101c90004050704512040d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 657089388 1250 657088138 657088141
    0x4060207080609060c03070f090305030a0306030b0108070b0340050f0607050a030e0a0813030210080405030a0509190e15040e030d050c2809080f1e0313030605 70
    0x901c40c2004002031185000d034100b1410401e500d004001500d40040c1c403840c0c42c0380c1c5031844040a940c25021608060124030012810500090740354022506607446003154100d40d9076607883c0903070740b8000f0b4055414900c07010b10000390b050012181c22400c500a12084d0b035a544940720081e035081064100418544003a94643e105019040040702071505020004140c28540711301c008007680202d04503003040546442e000041c4003402c006031034100d9004800680c1c1c80c0080709001c000780e421880100e0048051a940d46070490140c0d28151049030000c01a500d0b0000641c0d04031110740c0940480c5134030035681c00e01004030210490146000e4044551800385504000b03800442c203d0265075168465070804900b004042008415907106000c400703c041001d072a50a000c20740b6010b18580380c000410321030483d0446500f2400b01034251692a00c84150702e540794010f058807002c086141000030f5118100010488550002511800c041d0406690514164100c07034503c1500070352090301d20303548400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 657090638 1250 657089388 657089399
    0x80d09050318010e180a021c050a0c090e0705030a0608061f0503010b180c0408120403030e0a05060913020405120c0306010509040b1810060e041a090709020d0b0604060207 75
    0x385402100303000f42080e40344d4001d010f0024890480300b50004400410b82800300d0080011034054846143c0d914410308000d26807840c0d00340040c1000c55101c55520706100f4103020b040e00801a52007a00c640910040c000c1c0c1c0c0b0b104050307070250303c06030034030614070b075100e800142800303050058a000e0200c403404407915044c1c0b45c0b00b0b072604840980120b48264900507000c41c0554411402205000300b03003110076125618070b01042e8140c0120342c0140002e0140c0b1030305c102410540c500500a5034801d4948113400d0554406100484000d070142503040711040203565141c0c0b0b0031901c4820f0310f82025a0252400b602c800215003814040303a83c2d603545521480c02e1a6040c501400110b015150580d003800303041c6095129091a40d40140002280b0503c450b8103003082c2c0300a01803491000303083c1c1c3c1c0c244006546e880020024044c00c64040c0c0b80c41d51150402c2c584440c038040c01c01d008450440052a0b101c1c02c0951800007907210349030381025155a503044140d90345801024000070300c1550042d00000c2c1c82c24 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 657091888 1250 657090638 657090667
    0x606050f090f151b07050a03062301030f060509061303050711190302120f0312090a0221190c060315090f0b0a0602030901120e160311010e040b0901050904080d090503 73
    0x4454515081e01711540c01e100e02d880d1110110201da0b00201d01083c00882c9914001140000c001c80c811040441b00c00030043c44448940e280b04c03180f0801c801c102a903078007912184c4405044d02d407039080005c080344880100b442140a000214014001400004044000503125900483c1340041d00000d1000810030340c60080304a0800446101c09808409070041519031241701c0d1280c0b48140306500404100c100700704010444400340e000d8003e5040f02c4840301b451071241c90445124800e841800c20329a0702450391078092405540c01504030300c1207030500e08240c000d400d42007041051015803060000b605003550041d185a84848100014641d80b200107010980301e50350020410b42d40300f00711202559030b001c002d240d0240c40030031001503000d5000ca5681c1c20005009980c49807090342240101c01e01c8903c1903002490310090329220400103608003480151000029425404a01e0200400080c00c0005007550300c0ac0c42201c80c0e0707140c0203030700c00c03840c0407901d81205c02c2d1103541c004940e07281c0070b4015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 657093138 1250 657091888 657091927
    0x1140f0a140412051614010f0c030b090402012303150301150311130f1e05100b1b0a0206040e01150c151d1504150606050f090f15 57
    0x301e1808112482c16445070340314040081405010004006034145040880311402c584e0340358800f1100c8150858405800e000e0601c103109070394614078140c022a50760703000384035040d180c042c00391104203195156001510700581c000d5005ca201030300c00c501a842c042003074000314880c61100d440700340c540c4000300615007122402d884401c8000342140050010a17094004181092400c42d8400d403551014407460b00a0702ca4030354540d4940d130070078103c040e24200489028144c0b00490b102000207076540b00b085660074200d445607220440040000310701d141106e00e000f0400740031050840d841d05540c0e60100b011035009038080e0380704d00401c200510072141d4034080c002e42c5801a103018040100c80c5e490300b0030f0502c80720a000c156250344407446003084400340400044540c040e4103540c03481c284221400c91001c0115421a0515164185049410200d1068074250b5282e07030359050038030040441140c01c0d0740c060100198080d40303502002c45c45d41e942910030390300003078184401c5889080c0d41e80c0c185d846060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 657094388 1250 657093138 657093161
    0x5130c1b0c180507090b0a02240f0604050c070201050304020a051504090e0604170d0f2d150e180105040606090b01020a0819030b09010303090602152202010201140f0a 73
    0xf818240b2941c01e034000140c10581c1c0240b8a2103075505103501050740f51a54413110320f01940c0003018001040620444103600c0b4a0181c080b4511311b549803401c000464404036020004070209001c605c0240d4071810103558401e10190054602980343c40004030344500402100400307020015007407140d02458003501e0042d4039248020010303030925a50ba008625030001c03418240040104e40c05c60f0703001450700b003901040c11040c1c08104900b40c40710700741c230f101d0894040310300c0b500c25004999852028034403d416030301e4440321006043c5801c001660780320000c06000c09082c01566003030012900400c0c40340d9402684544000509107103881c000380d05a601c800040ca066410084482022500b00021683c8980400500d1498528200e03009c1c0c0080c640664611f4014160000201c10140c10030380390b00c07d40d03210350210f801010180101441c4241d04584c40c0203e84140c06030044440041840c03002041d20500000c0350001210780000e801c4101110050214411002405001d943c9071194030a0410b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 657095638 1250 657094388 657094391
    0xf0e090d020d09032004060b040f06180512120c0c150901140306030a0f0b070207050915040207030509181b040303140d060b0a0f0806040605130c1b0c18 67
    0x7400041e010b0180e01e4180f001a00a42d40000094645c1418003071755041381000410800c0003e84035402000d142c0c0041c014046050141c180100b04140219440401013140e4100380c41000e0409003405281000e0010707000701e512505d224100308541034405001d1810300d42d001428a4025101003040000d4820601e0b40e40351000c001c4543c45980c081142e120002c2c15054103560f980310b48010034035111120901070884034003c4403c60400242061844c000d110301e9013100d040e181c90b0800c105465100340c0b0180340c0741c90406a071010074141900545481c07806403c00c0d50a20480d00c2c00b1403051044d00008010350100c0d14108080050220b000d0101402142c02d428109801e581d406040c103584203041d4110240007007881c08a812554002c04085d040b84400240c40e00e52040010303081c8a040303014400803640d421f00140035130406228800481d14014424008130080c40c8142c0300510815100104109186c504a1041401030f903841c0c20a41c4590034410607140b400341e1400d026040020a10050b0703 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 657096888 1250 657095638 657095653
    0x5090f15040507020c09090f030c071d0c04060e010311030c030417030705120c0403060c020708120913050601030605041d1606020a1b0806011203111203010b130f0e090d02 75
    0x4544c001041d580040f401d540d801c05948030803926503c1d1212028080800b03104c00280060440e001141d0072084803071124101c82940d40c166103411b858501110f90000c44001400100f140c00c1c480e030031464200350181000100c04840341c2d2418a203034003c5501041030400041404100f0001d42c007403000030751a40720b0307550450a00030750040c164800c5541c010318554841003c20410f00011044030b004541c0300c2010883c4c09451440a0744a144e5440b0350a1140252000d41c000801142c04882000310010075400b06100b07044002402003034044c0071181003580e10725011900e5184c0d0f100765a0b411440600c0405c00400d101d0042e0320b8161084007480035084410400c0240329000150490165030140d0508007080031f04001c03c14046c01503001d51500d1007007100000794500192031141d40c00e8001d5607000e40030000592100d50741d42240d1400b05000908100400054130900080c200c0a1b07101c0d130b9001255542c1da400082540c5487e042050010400418484c074641c0400c02d80e81c0d60f00c05030000e805031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 657098138 1250 657096888 657096901
    0x50c090c0f0315031b1f02030408030a09030201021501031a0a090609030908010f1406241809070203310e161115010b0a030204093809010512010605090f150405 70
    0x84910040d107081b07162614a0142814001d000f6280541501c408603507c8100749440140314044501c0140d025000b0101d03007800c030340348014403141602c0c2c2203440c005242004804000c02040010500f2858966030716a00d40059418010f004e8018080e9072000d009030b017011007090031100c09c2e035a4421650324000c41c003406800030407030b101d6001c1d000302c91008030209240458402c1660313000c2c9a041400002443e800413107400c0d24010901c80040d920181c45595010302640d036441000c1b00740b0075a107801c1c402000000c016032400c1c0c5440000f00c2440c1c0c000c965a405a07000841c0a454420301092624500e214560744800e944c20044007160042c00310360003804070802c10704410b0040751040d4400007101c104e1180240c044030f0003425420300400c9070440b0410200340d858207032200762090b40100402c00c00e0741c12804805c3d02d2030110050a10f14107901c0c04042100440a900500c07074030b5500c0e03180010f00340c2c0c0c4094030107200300f40f80e40311551180342444001700e0404003018024801c07031600b01070110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 657099388 1250 657098138 657098149
    0x90207051c03020906070804080705010c262a0d05070c06030504060b06040b0c1605010e010e040e0d050d0e06240d0606140108090a050c090c0f0315031b 67
    0x5054101500800804010200442c042e00c0b48000c02d54001300d0020b2000100044e56004000f04c4000c801502c00603502d54004454252070620043e068003408103101e400f091070794407410740104a00ca20b007440c003600e00580d141c000304629004240120780215611500303a0900948039441110310381549081c800303030740d810b203035003510f01402c1c0405a54000090410031a036100043c0103400914460701e4503516042101b280d40022903000c000d0190f240381c0304a4205c5046901c06941d016101c00d003c491010004660703110f2505d510301ea0081d10b038220349141010501416100e00e0240e500c90340e0310b100d005034000075100b50940030300031907110400304400550171681c2802440d00101d00d03a28000c420000040429400100c0034010515004000a02219410101349281ca0a03220100140c0c1c8441089440302c04d00030026201e500312010340301c07072880e05440e1664418124a02a42400114802c45481c0d400850382d00c40b9840b0784c0220081c017071a0401260b248240b203141200c943c0054071000c80ea = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 657100638 1250 657099388 657099403
    0xc0a05060c0d08090f0304030c080c01080103051f02130801142413022206230a0e0d05011e14090a1202070504090606050a05010f0c11041409011509020705 68
    0x40800c0f00c00b40118070103020070b21000f04d204103c03004813900c45480c0d0a2000d203000461043c68081d05c44c0008100440d40140e00f078070304980d0080040d142c140400e240011000c01da95112a441660800c12000c0741c50001011a028024030000003a103000400d1340001500c8016200c6c078038071032840c65960039210b00030f106a05c5102d000c1d145001046072008842002c0d00400240354001c2d811082d01d0759440c01d00d0283c03034085461640e2141c1c2110414031100d49403080d102c201c0442d40f1401c01c8049400c071f000e0034045c078107854040d141443d052041e0320b91908480c62905152001036141c5802c80c101040b0303002e642081c071080010408581030001c010380d40c032038180308010400844102c2c0f0700d48090003444401c000700b8020740284103105003450540000c14803070084901c12081d0010104195100c0e10b00b4880112160b218103682080d80d031900d0301c0030200e400705250b10a48482600b504c40c0340e24841d8030300418203680046421407100c4a42c010b50051900814100c910500c6a01c010440029408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 657101888 1250 657100638 657100663
    0x215041104150302041b120905061b0c07090207020924090c19091806060203030403230a0809070e07090e0901060503072601020412060b0a08010e0c0a05060c 69
    0x60420005082c00001c0411903002940c014500410801b0460441e80d0400182da4030350b90b902440b40960701213000315600050054000d91180340085c40c1000001d110f8000001c0c1100350504003400c44540610380341282d005011100c1c1c002c1420b10850a0950440d50006032540301c1d020804080c0e00310440015040c030b0a14401c07203022020900c54500c202c00c8130340e0a200c00846d0315045081d038101400c018068418141c12103003048941000800300e01c40c01058980135409145140c4030741c2c400f1541840a00c002940d0b5481240c17800e80940341450061000740100c1d01c1c1c0b40014035101d9580d43c10420305511009040500d401006517482d80260004150342000001e140c4607101c01c540f4600515194001d140c041c401c1e5080468101c4e60070016108800d5001c04250941441e00405400c0c0d0003284210036040c0b0381c2824590001c2d589400c420508a80509a01c1c8500e59481a40342540d00d001d40701d0358980c0101c60320640764108031b40400007428054030041e250008503102c9590700e28454124 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 657103138 1250 657101888 657101891
    0x429150d02340507050d030f050703091d06090a060303021009050f070b19020705012109021008060f040501030206030a15151e020105160806030a150c0215041104 71
    0x41c611078080070829442d01c10300200020a240340d88160041c0210380401c01541c2c2803007100400581881e1000f004600b00780e065232508428900b860b01620b00d500410012400c1c0065000040307900a0010102003ca21a0b009121041e06010003400203801020300051821420240144082500040d28240e00720900000088a004a080c50742c104a800100f003903182c011070100054038034910b005400c0d0032804110108c1501c0e01c03000c2c2a82d450855214540c00300700b400f5100750303c0c150400404040d12807070fa10042003c001e141c0c001242600c60f03808103000b081102051055a007407076010390b201c514041c2c074100500d504607000140da40c0401070150308880c1c0c072209149c0080009140c1c41002749101030801c1d140d00e640620140582d0107078420750000052008611340301d51701c14000c040c0900d8401402c003040c010102c10840c1c0da264000d00341e580610074820440006103106101c04c11006020b000001e501c1c4042d00b00a08008640002d403080c0c140c048184808128210b41081e85100304480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 657104388 1250 657103138 657103147
    0xa08070305060303120c030a1515020f0d02060f040c0801050f0106020c040207050a0807050a0506010801020d0506040903080604090804150309060e0313140f060d0203040210080907170106050429150d02 88
    0x238258040c106050705024015007032030001034001c1c800000000355800c65002d54180100504020b941c95865460710b01c01030b444540400c003240d28140d0440d80150090003820061503e54416601307413001545c04540c8004120010000b86905006484540d1030864041d40b81c10b0582c3c407829030741c401c1c0c24000b40182c0c800149031000c01004020000c41c00d80d1150a85010b1342e510701000d0300030740264000580081c10300000440034078052007800380c40c82c4c1c1a08c031070034903456900601000346800030003100c020400300700c040740801c03031114004008a180d580104003a40f0500d00130b425501c451071085100d50041c0b1101003c004103103044803d40300e001da825400d40001c0400204c080701c00b840303644d8000c900041c1910304050b294004610a500a40320303034580740d22624040700c20406c203c2e01c8800f5a080b1310300c140000d082125038048185280d200114985483d10005011542942400000b0451840d0500040b0049095071002c0d004111910f507501d0000480c20242032154041c00c668241c0d0008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 657105638 1250 657104388 657104401
    0x3060702280501150905150d080d142712091918050f09150a0c020705121c1803020904030c0b09010e1002091806030a0501020a08070305060303120c03 66
    0x205419001d900600240141c2c00c205502100500c1140101000981041c00040214042010904902c1c1c0040d10110b40d01280d6111017045400c0070354580d02c1e09031248401e8074070300b11149003d4002c000201e90740305500a444421801c00303441d03085450a1350080381c44c0308a03074034075203068903a4480242c9061541070504081d800880d141504004150050307480d012480c2c41c1581e022912a1007c14110f0740e80784c0340ca1900c259120001104140c0c40701e02c2c0f2000501c01942e9070400c00c483d10031401103c6103281c82d5000074206007641540d4003420303884030356002c00c143c0d020080d1100591403410200c2020b00070102d0803841d0a810b00029006507080800309007007510070164200e403503405c200c2d40c0b051402c240d107a00b8083c02d030401e01d8010324801c20b105d01181100d188226001c0c0c0100510750031501940442450010744000d00c526070600803100440701103042800100301c2d00490b90350342403d604c0c00b880c0c041c003202c1d4003404950180e403040c021600c1546100c68aa134105414688264503075803001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 657106888 1250 657105638 657105703
    0xb090304090f06180b1012020f03011719050303010302010819090309030b0105060a05090d061b0c020405010b0306102d020c03010b04230402130207030c02010e03060702 74
    0x15440702a603a403418601c0c0014122a62103901943c0074600c0d0301c040007801205501c113840d8444c10059110070700380c44001c0c0403801200700070004d001c0e40c9009030030f110030800d140100d500242c1c8502d07804682c1c071254a00340a010b01c500903540b0360300e80d460319485c0d160342ca490b41d8038001404000e0521000134081092095140c9880d005401002c80030b0200d4001864020311000b040d20003143e00c89020000828246000800d560702c0020b283c3c1c606050070802070030000044005801512440e07130395019403008542c0a001800c1c03503900d9444000d0441254410710003213420507441009050780030300c00c0c048503903a204d4002010340228980110088213410300d0b40c81903000702c1c1241501c0742003001a03101030f03500800d0868800c001100200001801d40d014081520288112240345140468005004040b4411407581080c0054019800caa00c000c1d0000102ea1090750240c000c0f40c20040d107030007150792008400f4040300041c0c000c3d01581c1401000a0368440c3d0101d00352991800006c1d0103030028402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 657108138 1250 657106888 657106897
    0x14180102041d13020a0b0a021002031b0906070c0308130f0e07030f0b060a090e060636040f05160309030e040e240f1501020d0f110a14010b0d0f0b0903 66
    0xb01702c4a0256035505030020700e40d0088048401600500751840601ca031140709582c8211004e0039811048105a11801c115502055034540d02c8030040c07200c0c50200d40110a248040c0d8070440c2c145554401800280ca50805150f0200901c83e020010070b004001c1400d403015004541800c0100721100b1045902014102c0d5112440e08124041030820010342e01555010880c1d1005402980d15100c040500c0f5003445a40034030845c9046081607002518001c50390341100a041e60382a0341245000c00004050303d4141200700555504e0f401801803450b85000c01c10301c0f071f000b542001c1107203207807580e0050006920701c820305200f10303030300e41c99007140b103070b091007414280c50072849500d110340c00d1035090800b81e4405882122841c59240002000355405407401e18204405800501c0303504100c050860307030703c1d40d0042e12108001d80b101415044000c10015488060311a050074100030302c0c048051070840b07000210b05403080c12040f0401c00412415030802000d1604403412212aa8504072200e19500c0b9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 657109388 1250 657108138 657108143
    0x9020d0b030d032315060a11010c030c0e030a0201080414010b1f0e060a090b0306210f0606180105090601050c07060801030b071106130309080114180102041d13 70
    0x1600e000307a407072294560f10141e1080602c100740c00360101542444000c01e02c045174502802004004d241c030591078400060b2440c42e40c60301e00020f680d01c070140460f007510703d02103107500461740b900d4001d94003540110140310303000340950082080900c150002030510f0350161018081807884d40c83c002e44050b080d00302410410028040c091241301407441c0300450400030307924800041c105c5c0b005d440b0b140b800404852001300c4035038a10000c6c1e4240740c5044c1c100d07480500083e52092842031005001c10402c80c40b0710050700340300f010f040b184c0260b0122501f00003000701520300c40ea8000c2650880c1401c082c0720141541e200356284189a42e60f10016612440f55104002562181e0354000510070b50000d00c0c68140d900c07d201e006065191b003881034803211000e1389008030a0b002200000c802010400c41c6048960103480d011283c25a83d000c92421074041c0c4036950924900c442c10072405900d252080e080705401080214545490f1009095103d40081940071841e8495404030358031000b01080702c00c140d074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 657110638 1250 657109388 657109393
    0x16181107031119080702030105100e0406180c09090b0f0702100905032b0c181710110a09080c01023a030501380d02070b0a0204170705010909020d0b03 66
    0xf03d0900c8401034200381d104a10a60030800001c0200860040705401c5481c40344280c2510303116680d803800544480d0010003081c041f030800003400b0944901c41d0301c0c01004c2c03400001030401d00e10305010100c0300c4000c00d0b0710300380000c80c1d00340003459030300180a01c2414225480010030b01c1c82c13403500d18114411240d00301d51044030080500302100440c0c980e6050894032f0760080000d070711000e10070b440c00b10005844000c80c8004140801403014441c540303401512004080d290b1482d0f07104800030881e043d41c400351300018004100c91440d103420000520251054000800d032100d00070000030340d26a40081920b01040300307038400032244040e1070860b001e0b580e8600310b8894407040c0b0b00380c01802080c09200f0800810f660024180700d404c0040e0014459141107200c0902d008141d43c5500c0c49544900c103000c03240f66003040814086003070454114021a15210f015a0700d5107020b0032600003003868020051582c2200804001987c1c00c100c180089410001d000750710b601c84401e4001c0103040d81c4640a8060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 657111888 1250 657110638 657110683
    0x1104060c150203041118040b04110f040509010f06080a0b0c1c0204030312060b0c07090e1e07050109051e040504140109060507030f0b010504090b0a030203161811070311 74
    0x200d641c050a40100b10b06a07144504000c40f026404c0c2c5c480c1b030544010b8402611030000c200461904420441801d03005820401421490b10204040310411a03403445141d5403000780120401081c02110003e110070720040803810a6610b500c200c5071800350100740840000540e01d0b8015245041c0c9115101c60b0303180454440ea680d040160030305032551501c080c030b140742500c00700303040f0540701c16a81e9464880d002400084e04049450004045d1003090944074812909007209080101d0000205c28941d840980001d80c030b8a00091b0804c4510740041d0310490004010000040c08100108011601142c012885458a040c00340e418070a9030458a09542001402ca06008064011501415035582e00300098020400e42d081101d41d4201c803540000c03800c00c8200600070f0582c0103422080002030000040035501d5001178a0300303c80c00d40080503e0b4640004000c05090001261850aa8004148500c040c5092840d03101c0c801c4031002024040c602002c4c6103100e504000030625561481b0902101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 657113138 1250 657111888 657111893
    0x7090203010e01050a0b120712110c0106050103020309030d0921170c04080706080c130e0a0c030b01090e0a110408030c0f07050a1a0d0f0f0f1104060c15020304 70
    0x654024010060b84038016000020507060500f1080122182c180400f4146910301c00d80090714a800382003c400c004060221801c071448900c80d00300c1c0410303a101d1700c69842620740d441c20309581f076030b60142e81818418010001c82d640d011045401030a0b0052001540314964a8041c1c61440c0700b02007119080514084450802d4104040109c24050300078140007541d03e20306141c960788554018400302c2e07000300500304241401101d8244c0c1025413041418101040c49c070b01c0c1902c200541e4400c19021040d4010f000303402900703114004c005da00c0752409100207188a030001c0c284800601c40c0a000b4081d40e0f0005850070900d60022050404000040780d039150b4030804c5550300e0f00080650105800b51900001611b50000382c02d90031140c01428064440b4900040d00c02282002002050110000c2105101145072071084444d22030703d40000081062415640104071a01b8101c2420702c00d207000e03072040070300c001442650300300d64040c5442d00c2c85002c0c82c6402c05004001c0340d907052a050010050004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 657114388 1250 657113138 657113141
    0x6310c1d090601120e01091707020109060302031b09010e0307081c1106150109120507030b0105040203040c0e06030f1902090f070c3806092d09010e0709 67
    0x19140c080420010380340c98400821140c00e0050351000d01107000303051a0305400d91140c100003c2c0e00289000003503210000e0300c41c201c2c02c0e00c480c0400015440002a280119a0040303681d401400c014034085045240034001c0c218180040103030380342c01c2c0b83c001c61000142c0c0c0c400d2011000710b03600034041c4c40c0e00c2a900e0f036540ea42c41d00e038401001e5205c501400c102210b54811003807e40001c030070800034115511442c10350004014030b024800d040041341103000c41c0c079082d2614060740d030302e114100800b0818a5400c00302c2141206800c0300b44154010000d000200358045007101c2650f44501500e803540e1601d000103450240b10100182c654002c50040500e0682a00812a01c0c90300076102c6a81c15507511803070744a00fa01c101c800801141c071500d00d040102c3d1507102070034a9581102c601c1c400d20107286072040c40c1c10640e2004185005245002c2006605000017039035000510680e003400c4c040c4000d00c1000a6840c103400d154040c649100002c1e07000301c400d400043e28040f607001500e07000358a46070b1410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 657115638 1250 657114388 657114407
    0x90306110d0905100615020c1011060106050a02190f030e0f0a12060507090f150512010b0a021606050d0f0b0a06050705071202131517010603020103050f06310c 70
    0x155610303001700000e801307031514050100644d4581c003400817400c80800b00190148950780c80400c000c00d07103001a03424082002054064840d40d11501c0e00d6600e5804000d10781028005480d92001c00c0251150000341215035040d4200c2e45401c1c10003507031104001045000b103403000d0b41a4484140300340090280c0018a40941e8140144414000d5503503d12051794900ad440c030a00e210041508020829807010041503107442880b490310b2840c1020242510200072401c3c0c00c000c00301d0400003a109040743d01082a01c0448bc542195410800d240520181103400b520140c003412540b50041c00c5690310040d4050010780300010015545035803034640c01044da0300a0f0a0440342d6204990001c180f00380908585882d0704e600070030400003c08541d00c00c00c0134001c0030043c1d85610762864400305840703c880907102114180200001029446c5000040640b48080c1801140d0706a22061007481d1321103070781c0302d0030484a40031110a4220700d1008008410000d41c0d0b4230150350320740300444400c95442300905 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 657116888 1250 657115638 657115663
    0x60503090c130605040b0f09040b090a0515071e0801050f0d0614041502040e0c160f050d17090a02010e1f05090a05012f0f1504140706090306110d0905 66
    0x10489031b6504400d21842503040700185500180c0301d00090000382080d9406a485003005040d21200002542c0b074900e400c034100a4034806065900401c407c0c0c0340e12261000c3d40c0f0b0404258aa44a8060700005d04001018000c990040184204a61941e103448010a0343e003a805a82041510a1f02c403411801c0702d401c2c0d0382200c074220710704440160707040c190081c0c5040d0760307460703e1840c0c01d03440e0724402044c59031151003c4401c0380a01c14541e40491405080c1c01d0041d80600045d200c03031150201c0040890007900004240c2d942c1c520103000b1565400281c4081c640d50a00300300d8a501804400103441c014060540c0c0c10000800500a900541c007201500d00e902003602c40c541e00949480054070911064035115a00680c6820400301208001d5558034211500c1d000741c03000701288034446410506400d0798858500074400c1803104000910340b10045550100001d80a507070705110300103040500900c00949910344496507070001c140c40d0b2080b9087c0e2514120200081030007480c005403255a0803494 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 657118138 1250 657116888 657116891
    0x40b0a03150305030f070609080313120c20031c0e0a1a1e0f0705490212030106020c010e0f01120207060b06070f2604060503090c13060504 61
    0x5445071001c1030031140d401d03240d010b0040d505142d003942117401d654115040035078507151070700036200108400e035000b075024403d122445070440c50242005942c882d01c0010400400405009200110700c1d10441c1d5595413a401c1c3c42510411174171030001e490a03402e0140801003854003500b28a100e50000c1e03801400307500c00d03222144903035a500540d110881c4560b461071048031040024204903245040c000300300c500103031242400d00108001c81c8500b0303003044c03000300c4e4a640b02a50752560350801c1c4540d007800c0b02d100203c44051014445416440c1c00745072070071510311811440c840c8403550003484425070610f80e180c0119207130341c0c2d81d5a0096071099461440d50100b1030720403460b641414045d03c1200300c09010303111001d6155103002058002e500c440c001f40c580580c0c444158445039555030042045501414a680c07603850315040881c0e0912000c030042040030701c10010400c42e9424502500e045600e1418110740341d50320044420304202042c94280c2d442200d0038002c4160201650080d000d50714241e130b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 657119388 1250 657118138 657118151
    0x3270602070e130c05040b0a0803160c0906030816032c09070e010806010f170c071b0e0604050618010b0c0f0303040c09091e050a020112050723040b040b0a03 69
    0x1840380402601e80f074060f00f50701c0e0f0755409008500341a0401d2541071005402d003070000da070f00e0031280d0031034201d0403072019100c4410b150034003840082c0c940a0040c0c08000001c026061441da80c2551a1156010754141052120105028140602e90348526040c0b101c1c0c1f402d8510300e09940304e40382400030100341c502c180e0440022a592600c00c4000420004040e12101440d80b90a001076074280b0211071050100081142c040880c0043c00220742e011302e561180081e191141d91904030904444161683d1488440160401c986100c0a0940e41c11003070039500024580c65400100f01c2010900b40c102d1040021100006104880345c00280b0840c1e5845054171040f02042c0060768482c071090358003500303040b142d100500022682d07034000e141841c030910a50b860b03901d101c1d0b91142d100c0d44612084d80c254000b41c040306d09558110211007466192a80c040043d072400d06c5010b81010924140d922512030030710701b5000440031300d02c01c0380c01800c00c8003440e40d00c80365203003c4100260300062488001a04080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 657120638 1250 657119388 657119401
    0x2090703051501050d33050117040f08070501020703020d12060f030206030c160609060c03230603100f1a090c0403172a1b030a03270602070e 62
    0x4211409107050000c0302c101d072039400d401111241c02c11105103116968a8424040c4840c00b0804031590743c8025428004034200441c180d04107914640c4410705000b10301081d810340f6103c01c0140741d40b10394010004411160182403503100c5010700c0030700520303a62002070244241900020090003403a041e07034910340142c15600d10401510240c0c4902c112282c041d242c00d000501d802c002a41e408601800c00a04100b4a220401d19048503660b0a07181c480d0f071007400d4018406c3c00e0003004c1218856042c14050b0f00c0460745610a450001100c40c84002a04400318809a070306000145450711102014458a101e5000c18070080c01254440e01c0d40540c81c0c03032100c5003820a000c10610814140180030308262551300c8078080180d80111088951004002044900300152041c80b031103201c44550001014041158a01d0031220581721340010709040b400322a0755400148415080b641458030140c1a400b4013011103d40020840725500c0242031603004c6169940010a00e040701c0209485c5410760722035a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 657121888 1250 657120638 657120641
    0x904120309080f0a3207061a1f030e030a1e020703020a0b04080c040c2019060617011e0e030403140f060106050306010504060e06070b07080a06170705190b031302090703 74
    0x2c01706198041082c010301000c034201d5404200d000b00001d0340c4014141142c40090104120800c076840c2d182000031000603003e030715100381007070314541d08000c2d0702d040c1c841580070741000406049000c0c003656403228440c86510078170142005660151100c240141c41f5000103041e500f25014440807441001c1d80300b4a20f2400e4040c061446003161290220044408015581030046000c030510038495480580000b5034250380c20f04545010300400031713000d400e018085035504940c0084801d140c1c10700c81e4070301c41c8000050810004007800c51001800708a03040a540c25070203981d001800b442d81041c4000300c2c00c08046500400b10b110a4251040da0381c94440640c0c81e40000e85030a80010411b00c820b00c0103d00400c02c070140751800a0449040401caa6141500f4200071a039030340000307180b001030200c400e00e20300500b00070703112820041c265208400040d0b031381c0e2001d40c81010700c11600075281d184540c007501d0540c400b8102c1d08900315076034a07007254031180070060340c40c1c124060304070200029640c0f4800d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 657123138 1250 657121888 657121967
    0x1020d02031801030b0d140303060a08011b08090f0717060609040c030b0402060f0a0324060507110409050a0f031704020607020904080f04091a0904120309080f0a 71
    0x701160b00300003a04500044005102c06414240c100e90a003c106021404601c608520143c8800c015071b582d141800034040022510350201000ba03040445125411100c40031440200b074075842c0907034041c2d41e00d0800b40d182c9150802c6080c00c41c0a50300020811a1400740d81c00319501c143c01c12540e1a0f140c6609000d8110720440b0040c04240980f0418000510202003083e04140001c0449061122800203440c60fa4070503010840840d94402c20803001c0901482c8184040b45802d50010780d5074074020700540148a40300000302a4034403504550a02c1d42c482d4400c454054004045860400c076910700405140d000450940c0400c4083d601c034003076444486141c0c0e2249502600301802c1410700d03401d1001d03920b0041d104403500340044c0150030240840c500a0401841c8a600c0410503944a49062196081002140307000329212410003000c5101941c130400c508506d4a40013407102c8060070315020750b01805032011008580003400001031fa80c0151422071601684015121071000c0c1050f026031100b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 657124388 1250 657123138 657123157
    0x9030a080117010207082a010e0a230d0507030e0a060c0303020304110909100605030d09030f030e18010e070c05070b070c150206041e020108060906030a060f020901020d0203 76
    0x10010060003001c901c2d4100809101030705001605003800303580c402940d034111010405a18100e01c0c00c40010b1006a452150300781500d030001c1010107138140141d5203403210004040c2a1a00c80000340f10a4071140d00003040074141171003a180c40b0b9410f0440241180e1090713800364000b6003030b440c6000c041d00e003200d120400c46246842d01102c00040d641c003030300a904014001e8541e028100822001601c1c0c058006224007092000b810f01c5412200c0d1003401c540340d07500020701030f41c00141030040040d00501c0c42d405803034010411011904103490300320f0351445881505900001000500240c100700540b81505a4035121154680c41d078410404594007940f40c6030242490340f0050381040280450b9009000d0507010b444c40c3c10341280c035a420480082c181b031369a040140d02500c1040f00740b0110b882c0720710910b0030900703442000041980000f04411405412240701c1d4081c08040780950350100213009401d54410420f005c45401d6007604c80080d00b0648147e030141c011000c0c4103480e0342c40801151b88400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 657125638 1250 657124388 657124397
    0x10b18090c0d0302010f091401150b070b181b101107150c0206120702060f010f06030b010302072f030111041404060806090109061104050904110105210a0509030a 71
    0x1144070040281d0b154101d4400d9065550340d5446000c41c1c2080d00614180c0c40c081c0c038422001001100e4081d085038204240f96039410341c001000d1100d55072603012164642d411030440f040e59103a200706a00039441c00d200c0b074510351044400d02e106076400f0517207400040204035000360490303000c09400c0c0d400c2c0d440081d100c2c01540220744240724420b5001074040701e2407598030305421007610707640c00f04600b64002c08810001d01c48040c2084101d07a030401405a004007071201d80101c552500842040b105818000c410030301d07468035010511644294140d9007103507002150507040c6801c4411000307405407a07000201c585204001d03811264201409600e007964110012607142902c1c041c4411510351294003016406905c0b0140002c414008015150007620200000034440c0d1181c40c100341280c0a2141001d00b0403000d0108001c2541e40c160300c00e900603002041b10103101c0d02580100d68600c070351849483e01210ba0f05d00e03100788410701508248600ca1904007080359803180c031012980e90144855200000c3d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 657126888 1250 657125638 657125653
    0x4020304030e01122c06010602030c0a031110020d02072307060804170406270e070c030c0203100204060305090c0d02011115130203100e210409020c010b1809 69
    0x65201d107458540554890380c0014004405d000b860506086045034504815110500c0c20207098003070007040d0040c0954001540781407000070b0011346401d440310018003401082908990760340703404e001855030403031221811580c600421000710300130b4003c044195085901c040c07a44418800f10b003c22082c0c50b9408006050980c50440215440704005104440a0441c0c50407000a62410000f5002525154a91a09081c0304500607032103a40c0c01e8202d0810807500311407c01c82940050342d400d03000b007807614100f00c115600d418150760310568040001d401d84102c2c03140b1802c81050394080c2c010354125540620441d200c25a90301e541d00c01011040b64002c11b481e04170001580601d921168064102c015285100710402c014035140404940d00a10034001c204035400b18501071041520141d04503508014045511140b25600c0500d0010390380c0f0f20042c801416040c600700300503180105030300d0b4000c2d5660315000c900d480c00b90050245450040b032035400e0030040031086e50307080d600c84c050f00b100a0420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 657128138 1250 657126888 657126917
    0x90705130917070c15020d050a0e06090a030809041d0309041e0f06060f0206090c130207080f0a0305130f03030504080405041508070b0a05091219060e010b0402030403 73
    0x18800d001c1c044a04846254044146000d8040a0720805005000042c1c50f40c0c030b41034941030041c501810410454001c0d00d101064181c100c003d456160805d45030010900702c1c11408643d562040c00050707a84003100070000010840148014041c0c444296000e00090b48a908403420b00c40e02020341040356041442092010305160307200e4014401d25a818824035000520420111418410029140758840505100c0303d13410802101281d801440140910303e007120410792162210004240700c0c1e022800a1500200c03160150781200b9040b60b02d0950f90311283c1d071100302d582e014540100100c6d007040001480b61407140c24840c0281c8d0480030401240300b6955080300100b000402c00c40b00c2c141c041c03101290b1034680b4419101e070219009000032030349040810513031a14203030b0b078008000c5100802048441681c8541070310034001082d928a1020b506011070300f810284030721401d11440070004055800e000558100303a0305241220000c12a0492a40900003684000c58000d400f00d920a01001207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 657129388 1250 657128138 657128141
    0x180f07180b15040320061c0903021c18050109050d0609030507211107060e0f0a08010e030703030b060306010509190b180405090604020d0b070203090d0804060809070513 74
    0x8070224010031207056080c0760041d81155402580054900001814034104080c00490703542c3c8040500704e41c114108800b55110440a440c00d48152000580f40d0030217008045c02005040300c1c034442085480f412910310200101802c03500000d200520005990005481d40651503450580300064407a4103404c400e601c0d49800342007a01c00880c20800200060790104107030124854221500c0c1408138406810311034020868051003000c043c040e00f103541c0070410079800c0410402407140540743e158544d048100050006900d03075201c000c840d424240006443c10001c0000c10101e8400e0310100580030082007070041c02c1c0011aa102c0c0843c80401018065161203102142d84220800d070350404561070708942d88440e0050494000701500c1c400c43c01d0407134500750180366171040e001c0780100160300c0c143d000542c00383d04209000c0c2804019801158510344240225403e080024024050200c5103240c104030b01c0d801842000009001000410000f80000ca000411a003000f808580d003048050700f00b10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 657130638 1250 657129388 657129401
    0x31c080f0f2422050a060f061b06020304030807090807061205090a050a060c09090908071b1d0f15031b040f1104080d0c050d120e0303180f0718 63
    0x210007030385015585140356215000500329000001812000d8807140c0c3c1c030001941c001414080700141044018860b162008280700122031031490710180405c1c1c051031703072607516650541c00740400b07000000f00700505070481c4005020740610344d500010140d40e50881d40e15103200d40184e0000560b211890002c0c0304903a04000c2d000420344043d16000c401c0340d03a41c9450210207003000c940281d20341d052100c20790703002542e4500901071000c1c01e201c1103450f0340c1d8100851041c0d80c80104a42c07180e10482115403c180f0f5458040c05904490f0388000c1c1c5000ca01d601401c3c0200c803e00c50844514000407200300d6148141f2101100203401040798175400c040707074508000517520707694006950380c504c0d1090030514010401e0900301140c03045e50702c5040c200354509000540b16044284003150011400190001441002003c41854010101081f52014002a187c491400039071480003205201d40c0300c29100f0f01c1c030302c404c034a201102c070060000c2280300d4444086201d420002460500c1d45048100142c00c1507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 657131888 1250 657130638 657130681
    0x16110406090906020c0d1403151c03120e010b010503270d090503011a030a2307060908010c05130b033c0907080c040f0b03010c02030d0b030106050d080a0e031c080f0f 73
    0x8840a61020300344c21546d4642b01c190005101c1e0f084800c404035441c0309070904040c1e280000e008583c46100081d16510003d08500c4000c03082424062504c20140000204106040260303000c0c000e01f054001c107206001d0144501c02c2d440c00c80c040511020346282004140b0015028000c0c203c082e48407c03014428100403500710700954048070004110600494010304042d441301481d460818042c1402c46110700c2140003400700812050f55148050f405040031580124601e641c1e80d527810081040c07054100c82c10030b008160714002d810100d10b401c22183c4c854051081c0e090b403255038100d03107255a1f04507849000029003000a005040342455044440c0103503402c8404580144448003180c210389003051260700603000800c00025a003801d01403940760150403802800343e1810100061104010303014000c2011400240081025014069170700b10340300010240d079000c0030049860f40004420544440c0054030030800264483c9400d0503c1d4050104a90070380c03202d5545030f403603c54482580030803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 657133138 1250 657131888 657131899
    0x1140607020112050915010510051c020906040902070201121b18170606090c04060806010f020a1718040203190c0c05030d0c03060b16110406090906020c0d140315 71
    0xa51402004902030741c0c5c02450703404010259400041d20200340000180c001e130344110054130541c03000a9100c41039410007034500d0050300380074042110500007032141c2490150403050100d000511102030740d0180c0a424001c0e03c48183c04007041c0079031001c840b404a070312440f5040ca600c560700100e00c5843c0354001c00510036103d4240c01c0c0c80703803002401440200000c000760f52090f1b0030442c07541000300d01190440381c82c103a1181440d007045005008040020406410002c0318032400104510030000410801c0d085401c841a4600041c40740e00b071640a103444021821030382c840301e800f03420244200e07803182010701510500408001090740103000c15038a14020404a0328061012503014002010100d0a400e4005000c00c689640541a5034550b844034400003024010107403c40021600420420350114801c2030010107000001d005004c40d4000c40f141c0ca180001c52410003025900801c0c05c1c03c01002200e50080c10910110b407441c4202012903c1c3d880180085034a030103603203601c001d104000414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 657134388 1250 657133138 657133157
    0x12080a110c0606040c080702060403080c041d0a15080a06020c03041d0f0105040b010206072109060902030c0d0c18061703270a061d030a050706031103011406070201 72
    0x1103114181c0040801c951180c01a4040c800c80b0300c0c280c440c9040c45e03110350403d108203241611000e07441d070000034005000c1c04200f03c009042640075408903000340401c0402c03501e1a98800002540c00d0108484500e01c2d40d250585012480022044c0340c011141340800502802c409a50303114040d40181004080610040c04042a8a0b02074604030322010904004070385c0ca840c00349a00500c0440c1a84880e0080789010751040347c50b640810040d50004c017900f0f03c1c2c4807010800810403e420b07148a41070143e0362a020225081010a40003002ca15000b1005c8030500030500b0104401a200f5223402041e0704003602e07042000f03035074908104000c40349d50340c0009202aa205080d680e820714800c0051380940001440025075074135210500d42d00045550182c60f110070780b034081244c03044c2500030b450170300c05c1c076600c8800620708128004401c041d01400740d0711107008910f8210340d46c004501480c40030900f0310341300c289071003990020740341221410b0211030a21941034040c80001e43c816401641041a04070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 657135638 1250 657134388 657134411
    0x4182003070f030b060f03070e0d0209090a03090b36060409090b1303020d03090c0315091403070201050f030408160c1d101a12190f0912080a 62
    0x4080c41c03081a00da1074802c1100d6140e2030050850329078080303441c80382c6418428807640f42d91030000c0c0c980c001140c0c14a004071802c030038001090000082402035124011004100100c98007149291499210b07840b1510400d45802115103103002c5c1f140d14018a102120000c0945000010354207030800c18900b1038448900c031400414035552180d0400000c0c2d64032000c54104004c100d085181e880100308882001003100c83d41c0080d01d07540080459000c142d103410603582888210b40c0d03540c000b1035019202c0e00e01c5807444400340c8054694810141c80500188450f504000804011541249c0c4e059648030f107050281800840641c1015100b40c5041c0b005001c410303404902c002d241031409006924001c001c03498843e094044203402d00e14006400011028044d800305001110b100703030b5a424400c600d5641c44140080002c5c0140e100804264130101c013448044404c00d001d181d1500c0f40070006003e403060b1954606c060380c0708508000c0410300e0790b01c006a98241300c0d489154204090300300126a030786614 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 657136888 1250 657135638 657135701
    0x6040308040f0605150a090507020a02011206170c03160605160c0b13050307050d150504031b080301081c020a030807050c01020403060f060608010e070509030a0b012303030418 77
    0x201c17031011120007600c01c464150310300142010000c211080d411700083c540072030000d41f02e14080c100207060014001000c480e800c1581c2250000e00000118201d445414120480c0e4410014000e18000e004403850107007000c22942c6007409848840d00c4040c60545400d4601d0440a07c0d00d8083d078024240540108429246000030078508082c240c841c40e03118108000c01d401c008443c0e02261140218591450015184040a4080c01d46074080010160340f1401d00340c4402554600080c03103001002445404c01103070401441c10703030300b0f00e50403140c00d8881840e0f0741c0c0781c07040000064405030707000032101400203103d480c00781ea0103122450000c0c10910004030003800e83c0c1080c0c0007241c020f52621689150b10000744190741c000d00c414600505c065140c0890003c1e0460f01038400010800c001400240c184c034104110b8400c183d10000c00040796a4418001c070319030a14440607840b0004600c90b211040c9030000607641135074901c0010b91640710340c400524006044003160006c0502c41c5000f18a00304800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 657138138 1250 657136888 657136891
    0xf170114040302060601020f01060f030609020409060c110c0405190b0a03120908011107080f07060603020a0f03020f03010903020705102001050906070f0504050409110a0602011b050c06040308040f0605 88
    0x290000c144c1d40c142200003a060a24520310a51140c0c03401108001003885920410110f903007100c1700081e1207072140045000b41480010141c0070509007000400801c2d030045490210400c0f00003602c081550319002c00003030321400e5503841140f084160b4950742803030641d484211004001407a040f003c076680d5503490b0400e0307508540d0f4804a61144404c110394442805415001009440968600855603641c0c0c1414002c00e60b01810024010a04400700240c03503100c2d8001c0d41d001812030780c11960711701095003c9001804200e002e01c06521142c1701b1801d050040130030540c0d15402924285090409100210341c002d403801c420052010f240d540306041030242c1c032496054200000c0340034905081c000703141140150115007082500c3d5800c1080aa00c0310030f0f2020f03031b0401c950100f813542d000d050460300c02015040065101400e2400011107a805600c04a0507559296042c03200d01c082075404d946900070101d8200c000d401900005000034400c044655100d0311410703105101d200c0c0f60300c6003011181c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 657139388 1250 657138138 657138143
    0x5131e170309191e1419030f02011509051909120801062303060d1a0103031202070510180b04030309050730022103040302090c03010f17011404 63
    0x340210403400380b00412403600070200f202151103d596402d001c42046076140c40c40390183c90f485a08220712124624040d6214200300c468900c3c0c486800c80b11081449004c401140c1c9001e82600e0140c010702803030307500c41009903604401c5841c150400700508401058201001c43c0d240c419121a0321600c0780100c07050188425001c900001580600242c80680007034042c415025110a40d0315918152555203c41020701d950b245d03140d8001160750040c181c0001400740d203245504100084a0b079419034101c80c066904c004841c1e4180c0280b200b00d12940d4000390141c0c2100044507920112070300540300307015240d1b048080742c4000d5211407184141c00d96045001070b80b12007080d401c2c0b1204010580203084134458200f22500b00303c1c03505604020034684480a10100d20840c002d560303682e28031014072201c80d004660b45a100f0a03105860398014081284148240e402051400c5405005c0e40e05030f41030000c41c03007007550801e601c00c2d20307904411207030303c20940d00c680c14500780c1081e460440e4011031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 657140638 1250 657139388 657139433
    0x1140f070b07080c0a050a0c0c030302151503030906070c032111032104020a030804060e01020106090c08130c0503160e090a03020d050d020f13030c060305131e 70
    0x4580e460000030708540903180504000a00e820320034100c01c11411201c480c001810f00790f0f03564590500c269200701c9020b001901500c0481c10000502d500401c0b0101c010040205144096443c000f0300702c001c15681654a40542c400c0c0481c542504081009161840c09461900e14030b03552644d61694410608071105104451003d81c040c000e074115078540f80261854015504248011070051001d0a441103844640c6100750003050954841f001143d0140d0b403ca40d40b1982e8548a42c0e000e8144044844464015031a0220015014103940300f1058050226610881c440d00caa0024200380c008a9a0032b80d41004290780020301035a00300840b09105252124142e10140342c01c103405000c4d10010080001ca4101c4841880001da002c40c2e611100789075400c00316241e00d004d86550009004400000c2c00000000440189c10400c42e5095801c07640f20711142c54007184c4480c800ca099400c16680844000d103044500070008003800904140c0302c4a50401c00c607603120a0b01c60a500703070b0722403194071883d6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 657141888 1250 657140638 657140647
    0xb210c09010807020a170703030f050a02090a0b041a0c0718090c0504150b0f07020a0f05032b0318060507171e0f060a080a03020706020706030b030a060b01140f 70
    0x1540c224001d00d500180f5800640031100d00e507202c0c45502e42400c003403182a1000024a00d08240c000c2d0700114a89826030300400152901031148002944a9030a15106480d0380400080110b24681110299842031400c6405041481a20304e087e41102d5000a15405081e03404600703503802d9035005c01030194001d000300d0000c0c50b074103185802c0e1856801550040d410558800c1da0704110707445140440d000c0b104074a030744017155120886940034200b0002e40c0084c241c035000a20003021f4846005954045094a03e403012114440c0302444550400100492b100580c42962030b019600c400050404141c190080021580e50031742211400c40b001000309141410032000d140703c08104503400258200e01e91000f618480c503248501d0030051911206942c1c210005044ea2124010100140b038260f0480340c04e084145800380d2034403400d02800005202d00d00d00094034a20a020300900000c0150240c02a19415200d2102601d43c0204083c188003c1c072201c40e90040150008201d2001d4885055031076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 657143138 1250 657141888 657141907
    0xf0718020d092a05121c03060f080a0b070f0903030e06120906100b09060d2c030c0c03060f0106080601021c02010903090b031b07060608060106110f06040c0b210c 71
    0x40f2184d8200501a0520610702240010b00140440c0c080303003500704901185204800c02c030701038402900050f000ca0805400040c07181b50000725100290701c01d400400c29a5030b10842251400c40340300c01440019070458040001c01c4c01048200c0c0842c0000c0c100601d05028000441c01004d01601c45d01c4c280c1d4008010452440c42c01d00ca11030140800941c83c5141003407000000340c181c0100b51801550340d139a410000700032a011984807010f001482d0003c00c0d550f00003d0b2591316904043d01c0c00500340144400d81001746800f00c3e40300e12412042c94818102c1e401c1810817100340d54020700680c15481003041c141101e40d10802484641e1034250b00108440c207080c03800816040341544600555a014018041558440c4204414030f130030b880c42003900d8000b44d05040015014541c00320140f030144c20000b040d081d0740310082c0c40e40c0c940f603034040792900e80700541400d40d00c5a0032503000d400c025520344140030081204001f09850000705140c003900c1c00c159808188842400d86060380601000200517a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 657144388 1250 657143138 657143213
    0x9010906110702091308040b0a031e0e06070503010f140d05100507111204060806010c08030106020a02090f040b01090b040b0a1205010c0815061e1305030f0718020d09 73
    0xe1101143c1c005ea10440c1e555520f810050290f8054056540c1001c81c0c0c04142d244a5400141403020400321801c0c0748a461240d0001010031040300d00040c01036100040f40b445c0100b003164100c801030070039043c900c1c3c54a051241400c100400160340310200d01043c10101d4010030841a0f038145482d0001a1418004000703080a01c0303802c0e202c00d81d0780004450003000803c0700c0a8030100c84903410a80705694076040100e500d09a252401082c048004c03001060503503000a01c11052442030f40e141c071003034030b40d0101088000c404403002403d9080000052100200c01e0300503582c11213010b4008603440c60100d0014240300c1a40e08a200700118510481003801001d008825840c109400d01d40c120741480d038440100d0051140b010750140100050040800010305982c81211f001c14542c2c0780c548042d4514000388500522034a0f1080c0b040401c0d050f00d082000c540c1c1c1080303514580c10f00010500203040740c00a501b00030040701400b56a070201c8408581400a60f03030300d00500c208001c52800c07401d03c8a04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 657145638 1250 657144388 657144391
    0x4090609150b1207050d020f210601061b03030b06090d0b09060606030601090e13120c051513020d080408120d1b0c03030e100213030309050d0201090b030901090611070209 75
    0x14410441000c0300c503000c580c086113075000d84005a42d0303c0d4030300d480d034004076600c017080c0c0000d40d030003c00031840b0724042040032801c2807604c1910000c0c0d60079a640c40d1001c413040f0000c40c0a0325030810f88803c0880000380203a020900800d000740c8441d0070030308440c0001c0c2070140f45410a4800500070820880c2c80d07107040c00392951084003200c00034154140080001c0107003c90b805070007004a1200d01042d1240030070980c00250380c2d80300c040030341100c90a44000f406048800c8045515115039100540901c80200c00c3c2e45c8200c1801c01c50340a2401146c00300956003108050a85205d4001c00012801002c2480840841e405800a050b507e241c20000c640481e0030038101c00c151880e44c42c4081c003415500419001c0095014035000c80c00341c22070300c0203e0504034026800036205200051710360002500300e040400701ca000380c031540130140e1f4031402d00200242640001b40050304410b41403100d40c00490207150001010000001d54502c155503400480e1103142c02c026140c240410000114a04910007a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 657146888 1250 657145638 657145661
    0xc0c0b100e0c03070302070605040f11090103170d0f0e0d170402010c021e03060412030e010b1c1707110a0920090f03070e042d110409060915 62
    0x16640900d0700c0195591400c1c06403010415000010101c0c2c2c0061003a0151081d0581240342042207040c145000c1074400807030b940032240c44442022141252821042c100d04072a00906d09100b021804458141c007907004240c01a0700c1030780c80c2421001003040340300f02d03900301c0312860051420601720a009058081c0c91042c84840c1c4030b420b401c000050740c0c040b481d4120740d0350644d5600240d151110082c881e4000ca44000d03074061103580200f1041c04542c103851002446a070310f007046a000c03903024460986a02244417a042102d0149443c0301903410035030348103518040c00380a403030141c034030101c1e007010741c8062800c0c0c8824426800b141410302d0058100001040304130700030000d00c0c8420a002c0b0b5080e0341a6001d12241038003088080e140e4480518100d01401e00500340c41d20240ca5141c8244550410355056400ca0100310300484112004038040c2900c0c00d841907110300c074819595450303000315002e803001b50b0040d440da80354cc80082d030b441c014248080d115400d991081200c10540c20102c0d07000e902d06 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 657148138 1250 657146888 657146911
    0x5030304030f08030c0418060302120f071203020313080624010f0c020f0a06050c060106020a0302070e1005040501030f0312020405010516080c06041203060506040e0a0e010608010c0c0b 81
    0x420008041c00000c4581d940d02c404070310340307075a038460345d00415008a038402040c03100d80d42c103003d2002d2001e40c003680c2034a03c21202d060710309003005070301aa91016603a081ea000d501c04c10082c0302e08150760003020043c0744244100ca03c0c1c00700700b0030300318103010342075001003003940c8958140040c00002d40c88810061961811103905003072607100003403038402e032418210241308400c1c0c0000c0944d15040354607008220f002c0c1c083c18155544003030091140d40700a0394034196002d1440040740244c404520302c030000f03405500030000700d801e196903400c000300e000c3c007207112070034480e0000100790700d460013014000e40c02000c8a480c42c410074107014200b140751a0703000442520403c810304c8aaa00300042c0d8025141c92a80c0010800d4280341111051040d42441d00040c8664810003040106008601c0e8240150755800c0c842e507540d035400d104680c0517a008910204c00e0002c001051502e9035840030041180b201c0001ca40182c0d04c1342080d08440700301d40301100082e040c40503030080c4180f1101040d0000c40714801c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 657149388 1250 657148138 657148147
    0xa05031204111009091a041503060e0a020f01050a0e0405040305040806070905010f1d0d080c070f050d03030525090602070e160311041a09120c01020c04200c010c0207050303 76
    0xd00243c3e4a02407000e40356690b40c141a1101d61b001c50705201014041c2040200150140450100036140d1004039555402d00b9411006c1440100344018a181e002c0c000c014000341240065070b40350462640401000b0482849645036130301c60040c180920300980341c60b5502d40c2003070b02042c14840000c2c4101c05005104200708800d03680031400d2901001c0c1c525040642c614004103215142c00440c4482c0d41c08a4032056402c140300001c00200403100004080341c40d1030f55a69101c2a45449030312416900205812110b030100740030350405a40844001f9001d41803440b000300c004804503645841c03034005241d442d401d01c003071b507010030501014200c0307102078030350b14a00b96240e61941a14140b449042548801500498100c4401610301074240500304001310602c0040549280d0000f403040b620801c01290054000707000842c2d14000c02c0011303809855184e600205000280440e58481c0764080b08030643c0d0702002181c1c0026210390141d40c00003084041c030002c0028038000458200e58440d400420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 657150638 1250 657149388 657149419
    0xe19020a140d1d030a09120b06010309060e0604050c0a0f080606040e0313150810050904020f01020c0414010e010f081c032c01060f0b18030a0503120411 67
    0xc01d45900444403a5842d900c500b80c041c02d0000e04040e400d4002a200240a0340700b5400010000c5d0204514039500d00079031641e542c021070300541030440e020340056014000705a00394840e07000401014012701d00421141080002245080c00803101a121600b220600c0701c140d150255610b001440000001d040d29030034010a69220140502400c1c855070ba282c000448079507040c8196500d4241c040c034001c1ca480c0d0340d0100107800010000324140040e11080008010203030581300c0c141a5200580300b11b101e41e1311075091080303905140c03907005c0c150f100700a541086507031103006550b041204402c1b26101549095080101c0c82c506800a01c60480c41c2d071010310181c600000c1816038200c45801f0081d6012544100f9001004480012a6030224a42d54140c5944040074464080320410b4020400e01c0d590f000c1c500c88201c040e00500300581000c1107841000080403110403242c600003416140b004000d40d0b1943c0ca558030075117440c03542c03c84020801040c4440c0d01c10b540802c540c1500d00e50400c1840b813 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 657151888 1250 657150638 657150647
    0xc031b0906031a09010308070b1e0105040f06090c0e1c020f01050a182c0402060a0f030b06030f01080d03020c032a060f090706020309090429010e19020a 67
    0xe0082800b0141d55000c00c0c07a41c0301e945602c440102802a04c0c02d440c030350f1030781030101d025071142030152072580081001c624104132032130210240605200310703502c4c107034209420400034080c00d650070320020707032520300110300c0200304d1288640e58070a035200e803012580c02109201c0c01d058000851840d502e1101c0f01031300544c0781d51603da541e14100b440d15603560040c100f0143d1700c84010344c0602c00345c24181100481c020864504400d42d18115070b43d11a40300d45110800d552000c0207c40c006e401030340074890340040b50300803080388141c2c00d035500340400d0080500003c40d84a8100b126a8182641c41400420210906102c540c1c3d581040317103004c0d0316003074100880030755034811354062480580c0106203188000342d8012120005407090010b17121241488a0112050803040d01c4107c240c0c01114400607415000008580000a016107002c0362946c82c0c0d203d50b80855040400030030121300100440301d2428a04807402d001e8103084a4000060801c8402001c0303003401350740102046031040040c10381460300b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 657153138 1250 657151888 657151907
    0x31603060504020d0c030f0303050906090a0204020a050c03030a0c0e0303041a070201030e01020a03050103020a170a11040213030b041e08091216171501032616060c031b 74
    0x1035021415841d1407010500f00e469141d805403101c2d0f20303c1000700400c01203c0e000301394503000f607405000b0740d10358501c1e80e0384407001552504480c0e403003000c0c0840103051030b80240080d486181000b0382410464252142185d000311110500320b80e07901c03025241c043c0c11111212491209a00442c2411b0070944070345403503c480d18050303808203008118041168131a0b000f0004030381c103103002035440305540600540901400e0104920403014074002082c00d205280c01e2540002150f401444000050748503a14000100c820940e000707902080106855034041c0302c000020b40c880c0d4041d0400349400e04001040c039028a4420000340c892040b01c1021403c804242c816504d001c958002c442a41c803036030a898480b416200c01d854001c51200081c014500c902048410f24000d02560f65110364a8421030008409000082100300510311040100000c0650206090001041c0c3c500d8075051041010021040e01000c0321100d4a07a424512400d906000760781c0c244002150900416000c200040c01e030100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 657154388 1250 657153138 657153143
    0x201050c0322080a0e0406060305070e2e020a050c1c08030a140a06170c06190509040501270e0d0e18070309140a20010c150e0c031603 59
    0x282074035001032182c00682c0241403554403007552a514004460b000d005000058403482c856454003100003012030080c0a000c0c4100c06036541d1301011000ca9042000001030b40a6180e0005da02d01c85001400d10000700d800700303001e45078006108400c041e1414500d000e600d41d04490203030212010030703050502d41240041c1c40b01c0c1c2c07180140e0748070384c0c522500000810801307012002c0c00034154144400d20340980e205100361510440c0151090581c1e54544d40e48003281450f42d0b410400c1081181081458104114158171462170701d50300d0601e1000024040d07650a81145081500761140c00400503a0350145c40c1c5100400b0b0310511449015003021620380e41418060004d01100504480032a61140352900285404061665503070801020003002401900c500700c420010003074010b078010400042c0041c80b554030026101e02c3c02e0050050800d56010203030054140000d80041c071002484480104840041e90840041c400700c07485c0200d4900600078074000d029801800409003200b03090320307603c0c050381d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 657155638 1250 657154388 657154411
    0x4030602180a0f060e0f1503190c02010c1119030503090703170315010c0b070f0c0b070201150b130902070f0804030503030601090b04080607122903010c0201050c03 72
    0x103003900946a401d0424800c201d80c00104a64041062400b00d1010410b90341c07159a0000d00010150602c00c0b034058000c0219444940c540d81129011040002103900407214a140001e8542c204241030036940c1604080d400344c2d460b51404848640d102000b84080301c460002000c581c0e01c000040c103500250b40070b0103410400b0010014120f00782c03c01031900210350081103456001100c41d158000d036041035a11011050300144c9901c1258402c0403103440c071981054054080d5225407a040e640881c0404603a000d01007000345810101e00b034002c5292007030815800104446003042814051510103070000b0041503400d002440e9a05075822031501503078900780005039035902a041c01501c03000c0014000b004918001804001c101e070110103940610400c0c4c0f51508925100c039581b810601a9008010603039010500185500f84640a003448403003248600050207607201c80508000c050000b03c44090700e02031200e00c207143c2000d104040c00c0b450240700801c12410701c001220354a1002410914601 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 657156888 1250 657155638 657155647
    0x31905072d0e030d1d01080c0a111207060c080708070c0b0603030f030124030c271a0c060c0903060408030405010e0d030e0f160902070813060302070b0a0c0504030602 73
    0xd80c0a0700e82c00c155590700404031605840800d60090500440451401003a0341c5908405040c0d40151482070040c0160f070300c181d05005c010b00040340e0510803800c4a5209100302081c0e40400001840182082c600482c3d0101c1c0090121070003529106000d0401801c01c6487c5080090720340d03000c1c900c40822030f070141a590884d2500302c006441d60190300c2c1d0300c40352220000000600804a40e885902e0801003240c90400d4102e0f841d03060307080b112800307840004540340d5843c0002c03000f8500d001c400c90120a00c1c0090405844411002c1d8a0354890700110380200009040002d070310302000040e03401100c400645203000795280c0480d8540ca000f510060980c1004008101049800e41003100074039040e0045610394444100020013400c1405001d405a020b407040d02083c4540102e20302d442c1001451142c001c481c502500d000c001c4d0300200342615440300074040c210a00046500c9100100f050b0f607000b60721820541401d05072110003915a07550b4610700143d200d00d4503007120036a402c90313411001c0103855 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 657158138 1250 657156888 657156977
    0x907020a0c1205011e0b0a06050705032a0d02100f0e1905151003020f091b030a090807060f05090d020a021302040302030d20010b030307120201090803190507 69
    0x9403810240000c0105c041007400caa2404441d4014028070700100e54907403000307981d600d0544452140305000343c070719081000001c15400b490070100d03145000d860503540c00c601c48111231609014400142c84e00680003040750246682c0790780241e2a02c55040c1c1d40400ca01c03e140060207680d1145150804c40141c00f44000e00140074041c400038138103c1180004048a1a0a166000c00da030081d000c1240f145040f00c03c0d0024508260850742d1180e510080c0751104100119151312054100074411030b80c070790b180d04400c000200404081c25400c0c0c451000803800e040002d01460a5500080000708141c0c08000407551480d800110340180540584044c1c940101d455050001b0b88070319000a90503100b00900e1501082d4080c2005007074585031002d06000c10b00d8040d01509803066600c1d600c1e411313401400b224001c2400e4402010709050580000034050400350f44201081d0401c9511a0150301d0700c0179507a25510203070251581c001141c0c504541a4181c0541140800d10021092100c00c005840d000c2003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 657159388 1250 657158138 657158141
    0x1030b0c091e0105091903020310090b1308160b01080c2d0f0406060804020108060f2101020c07120c050a03030906080901141f1a0a2703110907020a0c120501 69
    0x11000d00c080c1c4416602c40003403002100c20040d610049001e40300cad595001c031806200d441010780d031a078440c600034001d0b211002c1c1002680c42514003600c00d03510801c0f1000c1040241191000c00511410030600d1562428000d00c1c2407210300d003601030107010042c0541a01031102182110341d4502245541d2190782e40c040415041030248034081d400929007100440c0058200813030603c554400da88024050b9215424400380c020380c08400303034001c0716800012600c03928808044440380d4069000605115100382440d00c2d200283c0c0c024654919040c0d00f000a1001044000e030182c0400d0786c0f03c01c2614910b80e802020a900c0344900c0c0100050301000c984054029000380c0b10001380c0301860b0320a802c145041503c20f191494900040b140e020200144004030b0303407078410b8002008211642000d00c02031007a604011215038402c1c0c0f041002c98004011501102001d000e14011032a24149190307480a003c01000090809000e40d48815400d1000030302151031001562104c002e2a428594030745001030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 657160638 1250 657159388 657159397
    0x9140a0509160903021302030603100e0c0f01020a0b04030917033414010515030105130305070302160303050901090e16051305040f091b0e0c0702011704060501030b0c091e0105 77
    0x940c00081c0783c0c0c41e91074011031b98026500444d8110241c908807403690980d00101d0b10b01c048200441d41062601d8103a41c80d040c0500c07000850306006640b6010010360715040d06043c04c44040740402e000600610034a1a0005417081e0f410800006514092440e40c200c070300da452a5803036003410018014140c402c0700c14000d00e006110741c003144107003000b0b0207208014040c0c4012182400044034032220050507190501600740505c00e40c0390040100ca0443c2c9003102c3c9a4030400050f400d6200312401074900001c400c2902008501940c2c840307032201003000c00182141016445040124202414400c68480d030020345141d11340c450a00c5907407510a55031441d01c45e0f03000c1e07110960142c1351583c11800300c181a00305c5050709114584600c40341180d101002c1c03020065000d081041403c0d900010880c1e1543d030000c148140c0141072003500900610b82103014003104031003c03125103440d80300400400503c20912600700704880702950402a0340d4010504940702480901328804002c449040d11384d00030310844 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 657161888 1250 657160638 657160643
    0x60105120c0415180f0f11030609070e18092a090a150801410c07060507020d0f020c03150408090411040e010803030408041e090c09140a0509160903 65
    0x1c900c2e1906500001418031110f1840006d0810460f40f0308102c083c82403584000b5085941400d5407500c0c0103110001d00010201c200b0301482c3d81e040134990b941c0d0440440c0e00c0d950001d0320206483c00742119410a00244482003040600500203444075544120034828030300203640c8440156034400802000d0104a00030015861219001240034041034000c451046001366007804191100c50400c1101000200d9043c0e8403100e00704880051020152440d0300320036040c5425090081d40c2d207442c421600255481c1015074400301c1c1c0f0060b00ba4111006800c0c8855130f0000e0501000004040b984900b071400103200c2c03020342c040004040000440580e6040c04000e80b0801450790540035240300e590250244500240c148000010452000003c90b849244e00008140c01c00c0d1a041c01e102d111030301070f03c200d010031050141c04035407140c41d80700f0b2000490490359101c02d0545400440e0b031480c6000c0b0079040c0074400764242030025881c3c6e8002250801021001d081d00300003d600121040c0c0d400341c200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 657163138 1250 657161888 657161909
    0x18091e0f1204030803010e04082709060a0e060103020a0c140304030312050105061b0102220f080f151314010614030f0d0305070e090406020c060105120c0415 69
    0x1415841100000c100380681205400c58996030700707401c420782a500507440000c051142c104014070400e00d01c5400f003074000d88640411401c2c49503814900031030b20042004504144680340d10003d151a0440650790401001d46241343c2080c2040781c201c2900e100200a50306050b00060309000c207600c600d010904c1141c100d880e458a07426654801c646951240c8001d400154800039a20640b444c40d1182904030f84004116520308030210781401c4040e41c1c1e030008a032155509009550b58071044400e003200000c401100701c00e14904110900e584003040f90010403407507000d04075000d600000029607960a00f14045920090385e60100384118000001d00000d1019880031200c05041005400000640e1000c0c500d02e0000401c0c0d1040c0341c1d031291003200300781065000c2c00000c41103601aa0220350054640d00c0c0588640e440580800c800e42002c2c1c4049600a6000440e140410f10038040b0341d0250100301c80c0064500c80e210100d41d0345103102040d052040343e58000e51032081c10090034000c000c10b00d0303145 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 657164388 1250 657163138 657163183
    0x902132c0c03070f0512220828030b0307050622090c080a0c0f03051b2b09081801022407030c0e100e040b0303040806010303021b1809 59
    0x501d07031120b82040e81c0c0000030586200906407400c0c0070784203583c45540c2e50701044080c3d44d1400c3c00d40602403401010340d00c4007190450b1440c00b050402008100c00d0303030f048490a02904041143c035840b00d101180d080201858080450f2560790046081ca04a801c11106c841d00c1f150401d90820201400d0a0040000740040c100003801c00110b81091000420689810300b240c3c1c0d03904840415505c1d8960000c0014100f00b4000f00024040c2e03010581140300d010f0807140051914400d140180d00203410200781020035021254440c50401d0204400c0380300c1e1070140405049a42c510308240905040b031a1942c250800000c1142d1003000034000703421910710380103540301c00c41007031602c1c0040684e00d0300700182c240440020060301415101c811b0b210080d020700000ea0860f00200ca178551640e030a20361180c0c69203e0360195035410005071001e4003021014220039451444c01a103000c900d0303a02c14603104c810720703c900782c207907611850700040100101d0018102c3c0d440300281d40c24440418084031042d8045803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 657165638 1250 657164388 657164401
    0x11d06070516090c1704052e060b09013f1a040509031909080f07061e0e04020c1009080a0909050c07020d0c08060a020d060902132c 58
    0x10704000c0c1610150050b245071619801c9440950b403010700d0304408500801646400c560b205000340f40e22501420580c1c0c01080c5040d0702017840c041e0003c3c481d810162010941242200b01e101e4200289041c2c0f880500d00b044400018243d180740041e11074108180300e22003191b2086805018030a8800c0002c1c017420840d084d0030340c0c0300818440404000490f04001609114200741c82a00e010304c0b0034100941c18041c41000c00c4003401880c0c0c9102007004400d010016a50b54204004408074000c4009004101d0400e84010101502a103060760381c1440340c0c1d036810039513030000c1c0e0003648030100740d401603590f01000403420f240a100390030310040c041c54000b24100340700c81040545810340d55a99100d05d415551021003058400544400d1703100c4004102c0000103203001c10003403c285208003540342c1d420f0360796030500341420021103440d82c500d900056900e078000c02a01c00c0d1406045a18011800c140d40b5072a0395a420f03140d8042c060490310000750100c0e10942a801c15a207a50004585004619050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 657166888 1250 657165638 657165643
    0xe0715112d0a0b0f280207111005090409060b0607051e03070305090d020d020d0b010e0c030903030f1b0c0709180b0c09060d180b01080706020309011d060705 69
    0x1c0c41941603141000703010000e0014080340b141007241d007111541080b901c4003180804d1560028098030710054002850701d0402c1d510703001c4810403000d480320043c0c4a017402c0c20214145038891038a80d1103001840188081e0340d4001c400e9500c5504180d60000d0b00b441c1030b250100c014586850401e600c01004525a800c01c000000c0090005800b5800c0303165910350225815920b024001009001c2001030104010300d0402d015044500d60004058044910300c940114071105403068050390480103140041c05000ba040303185a42000150400514514040724040c0d00d80c00060300680203410a10041111501c0340c00b007200000b81071010483c0e503100d10760542655500c0503c41d052666080280070b40c0c02008070300c420b40e001c81e040a503028480e920304606c4251b90303201080c142c0d48100140030120003002d69200c0c4104c1c12000d68a5554143c102e4180a4124481603010064550040700d041c04079a5000c81640d034040c100b1309050b0a0403c08001c0350002e01664604542c11000200b250130501500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 657168138 1250 657166888 657166933
    0x15060f0311180106090b161211060c03041a04140d02030c160b07030c0501022203031709030a03150509040c06080a02180f06070c0f08100e071511 64
    0x40303400d09402120008440c841003024441c4a0110750381755020454600c060006289508400d5140701c007003901651180100c10b00740c50b49600103150301407280d03883c010402003144c021241d114442d00b1440e00d9610105540c4003026208060010000400c04000c0780140961844400c501580d44800307101400a50341d400c0035000d9051071181110b01642d40826102c2c4a060321441c04089192400644042d94030310503620781110b40d99420400a102d05940340b111040a00880ca0304548151850800818400e0864101e904030a507070810302203040400400c942902c0464240032401a4504000304030051041c0d101d40e8004006500304000c111191600c0e009565035511003071255164103440b44101d004d201000000c3c9000030911400030310780581a415078000c001c0c0f003140383c1000c540d107076108400c0b241e0028402c800322400511440310103110108128100810400680c50703d0000c2c65a12001485415102190b000c00c080510b031123000c0c03401c0801285001c131640310300305003104ca41d500c40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 657169388 1250 657168138 657168173
    0x10c020c0a06081b03090708060a090b1609090c0302041d010602070b040e071b0812062b060b0f0d050f12030702061f0909081809010305030715060f03 66
    0x1000c240100d44a40030340e034003d01a413505500308082c0084406003005540c409040c28465104805001a1400003081164031a100905022403003030241d240108030711001429480c0c00120746008a0102c582c00407104003219204140803508114400c0181c0c001c8c0304070340005132a44d4007540a50a07491554130002d04036011a400c5400d00c0b59100011a0640110300a2490110050740440d5009108050400c40c041850201104920307031a44c5041241d0301c1841004249980c80081140c0f40ca028809440c55440010030300c8020141c03111301e400e01c0e0743d003250000d220720b60b04c6010500d147c4420000720010400642541d20a603103d09086646900e0413110a00b140310321800c001c00c112011094900462142d002000300340c0b9218440c102e00e070390511115040c091122400600800130340904a00c1d1405503a0850756401c1e0010111114a07041c413810b80103000030401040040c0c40042100c1e035030b0f6002450104c07180f03021024980a4410307513102030f00c0305204160210601a01c0c0700e85690404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 657170638 1250 657169388 657169399
    0x302090702010b03031c140702010c140306010207300b042d021e0618040b04180318050306180105070c030f1b062a02190201050c030c010c020c 63
    0x1612800200d0030f8403035107444103401d07400a105801e1311144880045044201c0c1c2100810000302d115804032500d0b00840301080140c1d1941c1c80d140601d50044442e61509840b007000c58075501d840f00002c1d544842c0781c4141c90490001030421281c1070b10403000241e40101010380440c62060a04084030100c4c0c0c16502540c4400c41c80c1100f003010751300d20b40642503030013a03689100b40041258013040100b030182d01074090414080703a1341040aa407000c0003025406400c0307400100094004080c40212502c42601c940035500d482030900d0920051740c5400300071949403510002505c07054005500100c0e29a20950b051302c5041c041c02075281405402040b26542800200610740da411030850b40521409005404200e80501034818284104500c0d0382c100e5081040c00b840101f1941c074641110000f54040c40c10903103949820030088850424142c130a00644001c00030612010480b65441d50034a50090500c50300154007441d00c203050069903d484002402042292800180a52a2288240d019101e82c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 657171888 1250 657170638 657170641
    0x219170c1b06072703021f0c060e060a110403020901090b0a0b0d02270906151b010603030f02060f0705030403030e01020c0705190810090602040e01060f02010f0506010804030c1106040f030209 84
    0x1a0003400ba00c0c011a034004200801f1160100c000142c01e802c413041040c1005008141c11001c10071030701551039854178010041a803441c1420100c4120741e211035401140603802c11003080540d440c001c1c00c50641c1d07000d03400000c1804405c80020780312006a40034420035403000c44c00d4640b211a40e40504078120703825031211244940c0c11f20b0080701039145c3d880242d020f0780d040041201ca082040c40740030000244c0c0d413034a107414140005030b10f01c020380240e0114640c0d181d003014820158044021494090980001c0c0924180710200350403041000740005c003040381c00b000190a05200b90406844401c3c5a07008550310b04801c12695150f60544c0a4203001c0d040c080090380804013109c000c001103e4043c0040c0c05101c4404007070401807c40c0f040152000398080c4000b040c03e1115400ca10300802c00380d114074001c0c8031001401790a41d0000c4c041031604c070346080c00b0480aa40c0044103503910560629102c0b80e580514981118000003586600f900a2001304003c030b41d1902048041c01524000c90f00d18066 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 657173138 1250 657171888 657171947
    0xd3c02011a060901050a11031303060213051c110609090f1609080a08070c0305010228051303120327020a05040501080c0d0c09020703030219170c1b0607 67
    0x903c10624003500081c4100103440c1618401d01680c105100d04900381d84c60700c5120600e40c400041c0b1500291191540024140240018a08000000c05054a0144201d0450000d5501c40b401c20080a41010a17002c525204c07543d421048800039a030003040e0142038100426070449420088640b2100c02c402c07620300c80d6289000e0b4102d1002c46044070300404000b0420382d605252500449400c45980c1000000400003942c00e0010f00441c00300c2011f16000d03110345026a86070800070740b44040520500304401c001c2442900c03000026282c0002911641202031813081740201080440094100d030860025611042c083c00160042402100c0300740090f030700ca90401045400a205a42041d4041c4039601e09908243e401e132581240240c1d200080207503100e00d01e8060b640f10b084124002580010074026241d0100d144520381021443e15001082090095403130421000c0e00b00342104802090320f003c00d000c0080390103911810f00060382c1c01414600b202500803c1c0d00c0400d0795984108a903140031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 657174388 1250 657173138 657173149
    0x51608010513020901150309050316020a0f0302060a080405031b070519180b0d050f0d1d0108040204052e0306060608070f0c0c05030105070806040c020d3c02011a 71
    0x8054001340462030a0b4a000040c240a42d0408111010301d81c41c0d4480b140400c0c8280301030300103a86a65003107180d0f00b4880c03041259051071a00319135031408400e00c0900144e203440c01514264822414003034441d40700c5051040c1745001e040c540804600525586c400084008109882292800da030307000b0701c1030f1481807580740f0406640039503c0c0c0c8021704007040b80c1422454210524002015003001d50003025600c4d1942841444c2d0200041580003030001c41d80180e03c450404403003880078001c8842451040c000070600c14011300085d10650700c860104265464045005a1450b030390b56103001d0030050060110700c0d10f90f107071006542c41071810000080042c051603c40d4030403080c0f966001c0c20b185007081305643d580e4420b401940c100141e03501c0454240c41c24800c403030088081e51141d8101e0f08e8020704002c15038051418030011500200a1442d00e00d420581c0034954a102d0a140c804080c4180072003220b210640b8900d034010741804400001554045d0301401c80e0001c031003040346262044405104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 657175638 1250 657174388 657174421
    0x90807142b080a0c0e1f09090c0c060c050409090c170307050607120212010e0411040c050d050402040906050c0c1b0f0108090f10020a0206150a030b0a090516080105 72
    0x410341d060b002491981165020080210107420702d501218969800300701c1201c2e01c031405c501c20021a54031210916080441c007002482071410602442012000080c200f6800810040c1140d4590700c4044c2e140e4050000c1d2805403074480010498220310303080100c0032141d05e10504542d401032070160209c407003000c000c89480a070080000c049940703611400f110800d080303000141d081c1c1e500740071149410b44400703103180c000c0c20101805401400e081c180ba8160b40c1c0d0b2820b40920551030030807035440080e0070030f0943c1d0010684210004050f0394034000f260203040d00d01001405d1500e0481088800c5541d1005041044018411190034110103003003401d401100c07003c4290f2148524005000e250f10070035001c0c3e480071040301034908411903190400c2c030340032000d42c01d61102900452650101d5a04201c410341c000d440010320340e0601689408104000454000900400300329000216240d80c40d4000d03d0460b5802002c6814499094008004070310340c5025640b0107500b04400700e040240e15104c1c0743c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 657176888 1250 657175638 657175723
    0x90308060a03050307200a06080402122e0608060708010f090501050a0510050d140105030d1704080f040f06031d010209010e01051305090c0c01060e01061209080714 72
    0x8624289080c0c81d400345020001020340307107003590315038903003a1507e03100f510800a081c244c94501c41420544100a68001c80054600c021362040007501d829950282080c0021044904c0070601000704800102c0a42655040b000d43e40c441e44c010b2150f02c41c0e120780401e0403100c00026090107181c0f12001c44040c2d580a01c121580460303500710070301c55803801c286000354400060421170300c1c04400034030b01c10545e038000186059000b1080010000c0781400c0c440d00845080500c0d0200c42a06c46540b0504400740c042c0025103400300104800d00380000d40d1003241c0c050030450395441d01c0e0a54034440180949200c4440d952480594051102010014000d40c0c940410585030210306110b4540112270760782107104040a04000800005807545a5036000d6004002e000c50450350342599a227401c4c25580340f58022148031840d00010019150301c401340d080c3c40d0190440109018809041c207030304502070340402500d420003613520004c6410000520f08410721244403560100042031003441c2080f442000c070b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 657178138 1250 657176888 657176893
    0x301030c052803170910120c11070b160b0c0a090e01050609010e03030421020910030c150512012603030c09040f1803020709151a09010e13090308060a0305 68
    0x240300240403c13482400764018008142d003810154000606038060310301b429800b02e001d5030030008403a2840c1c005c8004503d40c608100e007007202078181c07d66480c15144182c0e100e020000c500110325503000681902100d070003c42e24021410801d2003596560b110505c10f2020030102030001400a0b090a1102c1c100d030002440281001c3c0704500540e4142240104107506000800c800306011840e0855003014070094047c1242c026150b105000d0711601c05421348a500308011000c000080480c1541001c0c0c0c1c05010b14174001640d4900b080d1000c0c01110410f00014041e4000401c0000d08003041c2009007046004c0c03019010b0765a101c81d5140e2105407003000c0c920b20104080103240c24290400102c001d200361001500100c41c040041403820358140440c0160840c910410400405008040710820b802c908605220b00d00390203482801d003440120f0712401c1d400700f40944260300170001043c83d184050450152102600800c60040c110000f04402150f400c402140300c90078a080c030903040c2d9610200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 657179388 1250 657178138 657178219
    0x91501050618150901090b03010b0406050a0306080601030809130606050306040908040503060a05160f0804111f0809191a091e07030606060c2d080301030c05 69
    0x92084540c0240c04050300d590307031114400e02d0b980300c5901c40100034261440680d226281c410005001d032a1a501890b50141c0600040c02110010000c0391308803146804d00b0344c0d40c3c0b800d100e8250003400c025448000c0034041e0000010500118000821508501311400c9020085003a40b810444240703006800000d102840007441c03d060950115011034003a903419420aa6104c0001e850900d017110180d015544900502031011070038002d50450300490b0502a101545404000b042c600e0b000300068120040c00c0c60205050701d410300c0c4195400c04c1100d1a040074101210302034100e800a4520244500c6000c100c0903048849000308800c1c280e10064003240403200c80343c61010020301070b04200c040d000750004a04421401d80f142d0843c0d2001e50041c0c001e1518508186003119040d92000c0c02f400100710001000070045007110368104c9081681c18140c0e0005071260540314480310f4000c1c00fa94000001005019054062030118cc0040354104083c441c564500700e00c4040300005106150710034039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 657180638 1250 657179388 657179399
    0x3121503012a0c05010e030c011b050f0d0f0e0c0a0f05090105041d03070507150305011805191401090b0d030c06050916060e03071e0302130b0409050f06091501 70
    0x400141c0440703840c0c40e100c83d002800b915542d08455001c40d107424981d2002524500c00701c0c083c001c0110a114480e00d04030800c00030180680184a05019110600000200c281ca001807907440301500b190143d0381042040d20f0000c080d030b5240c1031045441e2240000078400540032691001c044240c03076004d41003103050f9203040c0c14000035180070f071800e292650f65100d054643d04020005008224080c4004110b110b00d80a01c161000c0c00280b0681c0c01c06040c8001071041e114200300450303d030034605000050a0792010140c0407000c4c02e00c050391402e507040142c45a208454034003024143da030307410410410402c55800700b19402084032801400316442030b070142c01190165105560080700002a18500300c400e05047c413002c0d20756008207020600044001d03404d400c0c00c0203240098a084252068801c404181209030b01040f840001d12501c2c040b0034008141d0701c9900203a80032000584244110b0045183c00ca86600c0100d050000718400c220000304009400680c180041e29000000311aa90800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 657181888 1250 657180638 657180701
    0x309050a0f0e06130c1e0f05071218120b0a020a0e21060109140a05010f1505040b04090c0206280e03090a0f080f0a020f01030902120312150301 63
    0x24840b90380200034641204e00800f0364000c4030000d602a0381d52081c40d00c00c008040845892808141b010030080703200c0440c2c9550080e003216015504404040116098441c044801034141104960f00b0034241c01d00041008a00440301d140c03031711607031844500340d071200c0c1824104d000d1605404001441c503681c42c407941c10300007060f500c0201460102c10103901c15099183c545002a407013010351036541c0e003189001a14940000e50000c00f00c1e10140210b500d418151a0510303414000c0c3ca04507080c9081c10f030381060240d81160700510083c119140c80d03603903c002c10001012620b100901500521001038100c801140510501000180702100010404030049000382030075600e24030280300801902d000b0f42d88840c03c50700103104131a28096664140500c090410002541419460344130304c0c0c0c1c250041e500c00000c004000020f00c0e0000c1c103401c980c00010146140d00d8448080740c000029007805041000c034216219410408001c0505007011050508a502c81307181d02c50304600035840e40740c154801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 657183138 1250 657181888 657181891
    0x10513022404030f02010e030c0f06031f031101090b0f1c090501183305090a140102040e06120d031e0204080a0c08010606020d0f0c0803070206040309050a0f0e 70
    0x361140d440e0700341103240349035a0090300250b9142d44c00d079000704210342e8020b00b995000d04c0240c026280c180e1841c3d0229485005441d1102c0c81a05d0200004040c000d818200707200c25a80342001c03a200555a082030075440d80003045042c002241410085140c50488003110521030410f4252440c1641c05000121110341e240141c8007900d444402540206009018422050000c2d14221810003028904100b804070040b4403504141c00301b12485107001150100c000c000190384c138012500d0740c0c82803d82424480c0a0800030121481d401006095000560103442a103c560300e10085030f45921040151441c90840074074580c1d4001d80c1c0d0100307001d02c01d402400140c18041000e81e018400c511181003a07030481e0300a162181e01072801d14041c40840c2029500805500008100c1d844c2440c500940b5a940c0c015000144401d40e1208034441e8401e00300700030300ea5044401140c1321300300444005e40300d900681c4c0640c000ba1040c81c0100e514640700091071304807005544440318092600c060744000a10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 657184388 1250 657183138 657183169
    0x9270303020d020a0e0405061005070204050405070f03080d0b0436171e0702090412050c01020409020903100c02032a0706020307051002030f06060306040207060c0801150201051302 79
    0x40a201d02c070100026030000d00103408082d200c89000107050000d100441d24001c0c0743c80d1207441b02455001c50207801008640c840c0780c045e240402e183d6a24103226252070078540c08018010704803580042445002c03000340c50001d800d141305010241c106e0040106841c1445c00c42c1c1c0a00524142e03107011032401000030919241c042140d508000c1040c2c480403140e00c00c0c01c604401d41d030782c00503950030851240b0a102c0e19201c091250981010050f40100e40b410310b0041009080085802001007078900520a840d13001d00524029075845854030501000707500004101c5020f80f00d15080f00a52172618015044000d2103a030066052840b66000038403e5000e690000d2440401c0d103d802d01ca10314107000d808040d02490700150b80c2c4800d913207081881c21000000351840c5500c14024003801810303c203c6d40c2e8016174101d030382645075155500064001d200b2403800400e507910b80010500c2840d00310340c245040381d2580102112402c10ba540c281d013a10710407a20000c540d40301050110040c42c03c45089601c110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 657185638 1250 657184388 657184391
    0x1704030516240c09082a0109090203040305070c080c03100b0f061b060f0f06040b0f0603070809070b0406020c06070311060a062c07121803110709270303 67
    0x45407202e005102c01407030b04441181c549a0b0b601100841d00030350103900410090000700402e0072220799400145034514648030b01d500240307041c41002c0c0e2048070b4010150407201d00465403030419150140255104080032248015036000019146401050860020354060040e14080040c151004014844001101e9204079001034090003510303068042e03c01100111154550079107021819450020300401d503d15066a04d03040040b52110b170003881d500031000341d40101d4504038480004a00c07031500c1c01281c1d001f041c04410051501e9200354001e0090f210f0300d003582c25181e220488030312141706034042d03a009644024004041c03410311ba80184007da009151000080181ca44982d0800400381e40004540d6150f482c203000142503801c3c10803000c01445e45001c80c1b00408440d00b5450300d4010150381c18024103151001440032160050828036046298410b0300d00194900500345a0b5840b000a030948030b8540d000c54090b02d24417a4507134046c4040130103901452840351401050500c00000c90406 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 657186888 1250 657185638 657185663
    0x160204200d1d150f0901111602031f090209011707120c0f030c0609060906120915150e0901180807081312150603020a1205150a020a1704030516 63
    0xc2c04140f2444041d0140c0b0521406141040d1180d0500b4503c05460b008290f490704620900c801546030445a1032032003c9a22002c050282c00080e0808210408000d0f25019200f00200341c0760b50b580c00cc280a600c201d410f01e0300c0343d803960000980c0400303080302c041051f81b0600381481103d00d005e1001c008584180c030100c1c5120b03243c038001000a0810340c412034110400030f00900c440394001a500c0054802450003005403807070580010551f03084000c0610481c0e41e582d0680b000c0c840c0d0f0200740080080002000d103d1004102c0c849401013030540b0543c10100110004508520300601075800260074184240f100d08810340c84442c655844108101c038000801c004d20000031a007011200010a0668480055080e0038100100180c102c1c0801c1c2030481d150a006000580d1084d20724020f40e40b0a80c001031940707180d40b078240d21b4a03a00418410340034100c8800c00803034070040c2d002040001500e0f510818400c003140140000300c2025a4014007280341803018443c11841a00815003032030103880c3c40310302d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 657188138 1250 657186888 657186941
    0xf1b011a011b080c03191b0b0703021605150a0b04150905220308072d0315050a1221020304140d060911030f0d0804020f030f03160204200d 61
    0x35503004c1010110640c184c0e8504040503030308040c04895a47c4400041c0000e1440b6070b59100030a04020603d0b41810350106141c4042d001e84d6070300e9403a07d076200044510210366110b9054441078221000e100c12402d0103460740e400c1c103142c020714202c10020455202000d044c03401c0030000d49801400403d80f802c00000c03402d1005203188001e002103009890300c00d81428155001022082d01007070340401445940c0d201240c0f01304a40014000701c0b00341c0f4000070181419072000e40714030100c0c1e120743c2c1d004420f6070000c20b08503185410100c0c079030b00c20300c445040040c00302010b1440c0d040106140e80940c20500007084840c3e000b4080e22126440205116841c00065940104035031500d80217550000720440700100070b0804100c1120030042d2400200b8070a04620b1006100080041000780500e189861485c0340e83c408005803050850780c64162506e030303052410380956100e91241c00360702c1f0b2402c100448450725020f00000405caa903103d40b00c0c2c9400444032584001d0700d484c11081c56400ca507540c0300c080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 657189388 1250 657188138 657188143
    0xa0921020a0e041518170408010e01050609101203051806070302011b08060d0f060e25050103050c09040b0d170901120b01090302010f050f1b011a011b080c 68
    0xb4001400355103550381090306013a12000004044161076a10b40f24242080d07074292000804c44035400228450b070000e5403000e400c00c80c0110b9015140c198204980071041e80d01c103402a5101e0f10302954041c11650b42c1d0403140134881072621941e0b12000b804820403010a101d00c0040440100c1d45540540e8040003a000c507503203038840319058005075502c0303c1c00c0d50100301d08880120700080501c4c0c0002c240c14401c4c000380c034000e45240010b0020741255003180420000b80c1200303080c031924809448141e2442d0b09142010203e01c0003811046541440121303056000b84513441c000c4813880c00960810704140c0600005081000da100c0d4052540c500081c0050a02242c50504540030743710540c4980102001406901c2c6c80d45044441c0c904046036850240d82c08040c10003182d4091030180303c5090072003810340d00c2c0d200d100015001c1c030030300243c0700c0100400100009890300c00c010007000741c101000e10310b213014401030400c2e90015210345a2150018480301001c4a03003070191900d5403410307090400c07852 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 657190638 1250 657189388 657189409
    0xf07110102070c030602190e092403060720010608031b15040501020d0b150d2c0601061d0a060f0203090616060e0601030b130f08120f0a020a092102 65
    0x702c005400103016001c0c20506410240d50343c7d003c1c20300746000c0c60240005001180020b05051b07040510508008081c0e481c240d10403c0e02101409132102c0d4101410001e0160f190070745034020807000581c69001511051160104a4102402550038000d1492810303103070640c1511030440740e00c01c400c40010340300650200030f030003a40f00d2000160350700382018180c01a0b692355007407203100303118010102035070005860480350180c1074504d00040030b4100000c1c015024882d40107080d180115210380520541000881c2810789040e0323110014405500150b254100e07502408003034010300c14410411445020f40a03180c0350010b03900503281411102c0340410b42d20340100c0b43c40811003036003180301014400c2c503108804c28840701e032024000c60f605623151401e582501500200004130a800098140b0a8507803d600b82c05a000320000d0743c0b104021081d160400c801e65608070510b159102098101569100f16219800340b0f440744600b40e13103410320401408003148250031f2880031800083c0016540c424500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 657191888 1250 657190638 657190643
    0x6081006031e0c0e0a0f03030801300f060f0501060e01230a0201090c0e160513150503060306070201150308131208040305100b0a090c0215070e030f060f07110102070c03 74
    0xd07130390101501c040100400c069800b220b1260748000081c030109520a81203419a52031281d60b440c03902c42922681041d5114800e10a18105030451900401c40c880d034545454502801c002c0c008481780344c274000d003122000e2181c0340c082608200e0b101e1040d4018500d85015641100040750302328240c0702100b189a0100f5034550050b50b588203102c0800405851704400b07010350b2042c0180a1500ca0f0550081c120003090242c1800300201d0251808010304580c0805480b0240390700101c0309940ac0f028040e908190b134414402d028020000e50714500c14454100c008807012940c250701459920307900110340c4200a5041c4000125402090542d003902a1a030414442e600040da00d07480e42c2002818040480c0c605d0307800d282400380403400d507a140d011040c2614030079040043c00b865808010381c5032002c0f08001d00103190101c0b0810498075007210f141c0d024044150162031003c0c18248929071103001c11180c03203076045103180201c0c00d15032140142100e50194034000510303080c2d054813140d110052a40c0304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 657193138 1250 657191888 657191897
    0x53001050114011b0302120c070b0d050a1a1f050c01090803060a1a0d0e010b09040c0f0b03060d0b04020a030c2606040f021002070306060b0d050106081006031e0c 71
    0xb10038440d40c3c0144a004d1140070300403490b241100f5954000c0d2205044145414210004152404410420311040008040f00c040d06590ba81102c0e620710041c1c00215135a20496140c50012240348c00344114441c08618001c004402c400c1c91130414a0016080b4450001041414003101040c0d2001348204d50002d405030000c1e540f07901d400410001800700a4009104140b179552030fa03401c0e013160105540c1c3c5801071540104003104000e0603240103010007400c05038004900f200b80018489801110801e641034400030300a00c9464800481107480107442c0d88d6000545905c0b510301040030000c400343c000388001c0c260f10700710b0b030769481c0d1183d200c015400201d0050b03031f1564181403198454400c651f92000c2100548001c0c0b409490310076194540c0000070340100e060a03d200000d5100340b09001c0510741c0720001b04401525031040704026007000c50700008817444c0100204605019060b101e00c106942c181000000c0c0c14101c085010300000e5240d1010756a0411292003200550301620440b0403e5544 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 657194244 1106 657193138 657193169
    0x1206011401030e060f060a120c03060203040c03050709050708070801050d12020f0f0c0307050109030f06090807021f020d11031e0405040c090f0e010530010501 70
    0x4410316005044c104066190008043c030300480042d66403410f0282c07101000601085c10007800380003520001c40800005455030000c41d4094400c085c0444541d5691350744901c2c221003500005d0100ea00c0d0010054240e5000d00703401c0c0d1003249490f02000c0f40d458080440c146040d280005881000a40d0407000d96500810803810720034902c000f216080211110800d8680040440c403e01c28050300c400054258490905030042c0c135001740090400d0291031ba01c100050203040d104555100c010700c218000b603902c020007006072450801000d01c110300c042d00001c3c20a141c0c0d50411050003a030008031030100070000140c8030030f103c00b1a4a038069100c4110800b02078091030344025031040c00e01448129055201400d60100d90302209aa045544c6802150034411401d010b540d4020380421800950100d903060707081a420b1a14003c050f094811800341e0f0f081d0b850036003001c0300d4506400c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 657014388 657194244 := by
  have h0 := BRFrame.cov_init 657014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 657014388 ≤ n) (h2 : n < 657194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
