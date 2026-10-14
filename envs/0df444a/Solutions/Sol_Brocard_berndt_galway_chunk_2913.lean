-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2913
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:07:02.908269+00:00
-- url     : https://prove2.me/submissions/80611bc1-834c-492e-9f1e-9c44c813b0f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 523741007 ≤ n < 523920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 523742257 1250 523741007 523741021
    0x17030c04030f0302070305061302040509010e0309060d0e03030c0910020607020c01030c0e03060103051501290a030f060806060307090b0a062a03120e010c0903120c0203060408030f070206 82
    0xa800345000c02030404810044890905108000040142d904003042c1d0b411810001d00e54000040000c034100e01403820034000801c1c00c001849101d02e100a0100507514000c200b40c01c1003a158040707070340c0141c00799503401101030902c001c10141d44102c52031110386940b204a0400c00c2100c07002c1c0100c000c210741c0303c807080201880e40403495450103842030a01294030710000400303540000304580c0d100d801d48241c100010a05c9000200f100584088000c020296625035841c0303540301d940614080c499644400030174200c02c0000004241c00c00d818030f40010026400244842600c0d038550164005600480c1446010302c1c090040708000c0110701810007a4041a00201d044a000b0748211000d0007040c0485040301050203c0b62a08e440e03000d5a2698070f100780780b50203840700d61040380e441d415030303e8501510007649051048094111044e261300c0b5046146a603160185510759491a00704000d2151910040c1ca00b00b00303180c0a00d02c0fa41102d40c881c0750a00314034080301001000c42085602c102d00b80026 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 523743507 1250 523742257 523742281
    0x506040b09041520031f060206010305071e08060907030201021c0e040b0409080f04060306171c030f0c021c080c04030f02010c290702031911120a09031703 68
    0x41c01c0141401103541900c500e5894a41300f10742d916907907581c10000c01c0040030846c1d0703110041140358001c4080030040d2111400ca0340d0f00d50034040100303658407a0301c0900ca00c6d110280550383d1001881e0000400640324941c0034100041650460429801600d040c8215178040c45820170350541d1a03800018400c0407034000b4020281c2c841100c0c052a81e84c561840243ca40c0e0300f06040150b04641040e5440303500c0d241350030345a80700344507d600180c0f0300040410711801c00301c51541d148050000074440d18118054141100310311019000c2490743d0740304141c020b85040c3c000ca0040340000e40181c0948003100301200e5500c1d02c0c0301c07501001c220b900801c12030100d240c80107030390076650043e003d250011428401a00c514411103c060100010842c907442340c801000e40c000340407007101422071002d40f202442030b0380e03e015900620040c0038a020100303982c20b129160035420001c000e01150394000b20204002169400b1207010710005030f1040003402400011502400103103026040203286141c0b0f4140600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 523744757 1250 523743507 523743533
    0x7020111011b030e0c180412090b09090a140c0c1e0d050c0709050123030f2107020402040303230408030301030209130209090618160302060a02070b030a0506040b0904 73
    0x209140e83d03003504913031135941000203030600c0ba000b4121000d0324202c0c100e82c0d0002c900c212421101a460240ca248825200c3ea03402c1741140c2d21211068241407040c0c0401104803c0245460300090742c0303c4803250032510010006006e91010840e075503950050454060510300360800e450300d1340d402d40c03c060a03aa8000039001c000300c0501c0c6805a2031b9000c1801032800d00b0707060791000f003113503003081c001103103c1104000900ba80200380c1000c26901c1055014103447d4442c0e0f03e61068644c0004481c08580864131401c0e080002d445807a5514201450340000c04a820a81060b000928400b14061480340c0300403142116000590056044c42e01d808611603481c8014000203000707080e550041406284c800c1c660300000d503801030460a45c0e140c861030440d80d540b4200c908040200004170724400124002c1242c0c00e900000d925122051307070864003441815400307001801c00b148039101c400152005550041c5015240502c8046a1030900d601000162031601d5030321031080c0c18640c01d120005001086c44a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 523746007 1250 523744757 523744811
    0x60e0703020c0712030201020a09050f090103060213050918010e030f04090f0204031e050c0103020c03040905040519050f0607051c0f0e030c0102091305040b15030307021002030702011101 82
    0x369858282c0b520035402d041c0250f0000003860760075480d140400d43c040d0043c01c900034640c1c2d01d5001e160781d0b40b4100829a90721045d20313030b0031491503801440465001e400908482c405d08050101d50791395038000c00c10f104021604039150441820086c1c0c00200207004400d040d0318940011410320004d1003003546140320f40d204e4000010307601c648039041c1c1c118a4050742e00540e04044800034803011740c0645105644407201c111070900aa6140c0d660546c000d1007500c03030520b0b10600441c00d150410b0741e420010000076200f62514400e221043c0c2600003c0c0d40207182030f6205030f0180c03032040d40d06d03c20245271080140080003400014005052041c4007404108840840c11801041c0141c00c00c2203500100441214214035000006002490b048150001c2001003c1078038204181c032100d0695900720f4100b6940108004010000b28100070b01c55542c1031884880201070300c0c80e00c0f00076400610452051034070080542c001081510943d81c01810000e100e0050100074800c0c0110100344a02c15004c0761007030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 523747257 1250 523746007 523746011
    0x905010f050612060d0f14010b030102040605070b040f06111c09030816090e090c0112020a0507080d32062b080c16031203060b1b0307050109060c03060504060e0703 72
    0xd90705030744041c14940c055400207002084401b145c14007a4014010200d09055503003403e01c010901d0405100b210100c0e1003030b40d102404c294055031010b400e280c01070300a95140210001000100b007052044180742c1070b000d1090395951030440344158840382504041d4a015203052040808a60001440342e4041104407004180407030410040c1e84a41042d00010300e001c5105081002c1e201d000540c02d07444240c03d072030394844104600c811200b03031f202c0c078212100040d0040c40210002214400901403910f124400032441d1410f800392071b0200d1071030042100001e442c44003440d10380e11001004030342100c01a294040c0700c011380c07001d1944d151389180d8450b40000042c601d2405000c440429501140858800d50b010a6010358010000b00d08a0109540340c00940043c0b0301ca20303000e07203d22000c445a07525180d080040038803500750884040c180b800743d1400f0402820001480a104604400340300324400900ad49021500030120744507138204e580a140781240c144643e41006107030560009080c580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 523748507 1250 523747257 523747261
    0x2408030a08040605220503040617040812090a050d0201060e0a0e150901020f040801060f06111c030e010f27050703020f011e08060907080f040f03031e060905010f050612 74
    0x1200c111903035a00a200101c0105d0603403410084084003d0044420590f03500c00b144913405000b59408006039401805584200052001524203100e50f82d031000790003040d1103090f2550303256281400c210000320030050f5500c05050000510405071186c102241100c20070082806010b4180e0311112014001c5a0380001c43c001040b00340d0035011640c485604d41005a19140c1d6222142d020f000b15008410461030b1240300811200d00ca030100789090b40b8407400030710304070448580c4e00080440c80e028160405450300501d801102c0700740030309045044014030016052107402c00300c0b4a0b003074000002425444034a03070842c01103400020900c0640380c040b1145480382c4c80200040c0e4044100c05008400003500801c4060020f404c0211f8511440c0203075034031402c6580f240f00c116504a004c455602001c2c42c00070200f80850b5984030300300c19107440ba08000511039245211040d01302c0076403000c000780e00d450f050180405142ca000301401400101d8151009600b040c000940c81d00445546100304d00031140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 523749757 1250 523748507 523748521
    0x10507020f13021602030f0105090a03080603101e1b17061824010c02090c03060d0b011e0e0c0406080c1c1407080405210d2408030a08040605 62
    0x24104101c440d442c0045540d03180303200d01d07059041204074007a84280684510f10805003810302442c1e1155201c0000341c03d1a08840c0d0302501d011030080d00311a018403a1500c101d55401c40c030f2080c2c069607051282c502c010000c60710980c0c82907400e800036007140c0ba42101031008185802048460351507003a41000d803110b90302d0002180c4241c00a040444d100107c400601c0680b450086e81d1a95140c86104c031500ea150f00f001c010340d040750008030001c0d00145e00400003462001d020307014540089004004445200694981d8103d42c2002e0304035000a1090145460203942901031800042581050b030022500e00160032801c41e009601c0b850f4103206071003001810502c000c00c21902e01c9100400010030302c1d008032411a0080c80f02246a800010409002c0f402c214056000644540d6020000300400b81c1c882106500703802e4004e00c1581a2030090004251080383d034062600c1110414404100340005544401b4100d03280c2e5100c2042a0410031455062550103030752550301641001c0045020f4480030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 523751007 1250 523749757 523749769
    0x308011514030117120a091a031314010e0a200a080c0f120a030201021e070c06030c02010204050d0f02090f0f27031204060b0f010203090f031507090303030c0806010507020f 76
    0x84200104405e0000b01c05030542d404c1200b0703405580c6220810b0010800c00103803480c1034842500d0340c158417441c00e446400003c911101403158041880c00109030480d401201910b020b02c40c06080b28038690640c84412004919040c0c480b41590032103400102c1407800d1140c680b2501410042c40c01071b60302108502040d00c0b10b080c940701c100c2011040711080030290400038001e4001b591401e01020b08105003000283e1102c0959008503005800e0710a00c601e0319a080e0001c0048522020565409000008142e510a041004c50038010344c2850b0052009104000c0b120744000d1040c481d00c08410b0900030440d81e80760842d13078004401c00000d0300c21040c0300c420861002202c00c42c100e00340710000350b001c81442c0c0c08201d903014038440e040902569034030f03c0800800e42ca81030035040c0181e10a005003000c07454420621a494a00038051701c0f85000b412804001c40c400c01c50f441000710310b01180820030554103110792504960303945000c0304603007040d5000030301912034110080c0c070a901407054400365503100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 523752257 1250 523751007 523751023
    0x61926011401110709020a02061e1609050a09050f0703020309120c10050a091202010501050105071104060902030112121e08070201271a060604050907020312040308011514030117 78
    0x100e007104c01840e540c01040019501c140c60b02030050149502107100c0c400c410741039031038030341d44c15104c4002903a031004880e400500c1c03010403008000b2503403000149900c9402400380680f588003070205061030900c038140c0428001400305400c051040080101000f030106400500707003520704169550341c0f01a441c440c54141d0303032400a44c0300c1c0d01c0d24040c8501254240c1c404001c841c458003803410303001d0340c02c0d02c2642211424070416001c24005c000307840c001582c000c1a044c001100a100081c01601c42c4020002c907082604100d14110706104110207104100c3e0305010064858a40b80144100c0f0f03188410881d92206100300601090301b000c959864003e40121542c00810761a0308407043c240c0120505806244200f0780b8481c00d80001c4a4039054103509203407082c00080c00d45460035150405001400c1c400030030309404c501086c0041d1003541c40003000301c1c0c00395001c0d82d95010303a941020312101d0301c01c89400c001000d000c40c0c1d442e2090092103810580341101c1101e41190a49220903401600345121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 523753507 1250 523752257 523752287
    0x60908130e0a060b0d0e0f0604080a0813080d0b010c0f0809011202040e0106180b070c030b0a0e0a15090206030408071a041106070c05061926011401 65
    0x808103604596000e0021032404469030654062942d465041c0c0c0542198140d018903d034911003005080c412006503006a8044030a40c4c080703a030305038010200f05013001405d4404a42c42040014413260791907129811642045101611802e404115a510980d502c40ea207201d400c45a2500d084158680c094440c441c1d4107600581d040f5a052050316104009611012600307002c14240030122a8a004c64800d482c20345e89643c443d84c0e440e03402d00d034050b901404240c5d10480c480c1c0c03280748017042e400ca60401412040e07110b400c0440c401402d43c80c1c25090582c00801d045100c40c81c005400c481ca5100090310880f00780c001402204d2264502000b00c0642400071002c0e4010324000240410807100100604001d0302070020000350302c0c1c06002c403200a100503500030300445180801850a4a0804001c15009115000c840c12695030781d0301140e021742008150b042883c20b00751000401031707041000f00e0025802ca221a40350012900c401d4400350506020b0380003003010f0314040c50032760b9001d01c20031042280c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 523754757 1250 523753507 523753523
    0x30308070c05010e0705041a0f0609032e060e360307080702030607020d0519210c030b04063204090f050706020604030c080d0b120120070209130609 65
    0x20701d811800f036681c5e5203071240601480c5031155110704020340e045c101c0c201d407000415101203000c01d801040314a41104102c95494014115028400710703d048680590007032100326680e10070407403845001282c3e0282d02c4018ac1150010400909108910080704002030a0f00c14262101c101400c5921800052034008a240b00000f0f42c8010f2010041c0540040d40c402c4080f05c030035aa81c10412a1036000c4040780d08042102404402507802c6590030080320aa1940b805507000d111180355480e00e20485d06d404c039401030307985d00c1c0b0202941d410f000300c0300d2101c002d032414400940b4041090035400c0c030300c2c03400d01d441040d441080c000d010394540c4d0083c0e040030020828841d10140341080108242c140c1812a00c034405c12200145680c00403800c540306d40d405443e085441880d40d03c0306020350f03004002c08442290350780640030302542e554945000c107401c028000103480500d00c3d2544110442903000c9025050284003200c0107a541e10441ca910105002e0f055801300060300d0041d004d031849580c0181088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 523756007 1250 523754757 523754771
    0x115050c0114010f0e060d03020a080f09100903060515101b05100e063303150a02211005010e0a0909050606270a0b1c080301050a15020304030308070c0501 68
    0x403845401c414183c036084920545d050315035004014108041e0b0000a000d40c0090742c03a000070422090280c240e565100c4079140c03400ba1610f002502d5808000c40010110300345410a2091081c00e201d070651016216070580440301e00b500006214400c090044410405d41e42c001244217001c3c4c0484480856016084580d418402071020001d4140e984031640c0520500000030b10002d48004000c549441200701c55003d44200499220301584009000e03815201e5010f0319000c1e80300c80740c0414400c9556020050312004152007505e50031220403071141a168041c1c0600a2800380989001c044170400d0a0a0b4400004140424070f02c21030307035100d1080140f8011001084c401c3c049041c605c109400c40e000f69186140030001e6004050181e00109072884070b0300000d11001e1960b11a11010030000d24001e20128850640169174034242d4084401c03030300c0440100000d0618498400142c201350401241f0841015030080d079a00407403101500b00500311000c107003003074014940c603484176800500a00c01c030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 523757257 1250 523756007 523756019
    0xc01020c09090a1a1812040b0904021b0d09120b0112111201140c030f13020102010b040e100e03031605180d0f020a0504180b1b031810050115050c011401 67
    0x1241d0202c54543d80d09517210144104030801040007101e40c840c0280702c0e404c03d410b1004a200b143c025125181c0c00c140e08000b040c111902c001d41c0940301032580d00081151650550005020f100305512102c14040c0311100340d0005020041954192002110a08450140741c00d01c01080c04070207665540101c2104201002020190003500c0101100b81c0001815110380c16410383c607110460703401290052080101e00c0c00071600c400400e5960052002003042c1c80741d0310002e0219040800001d000c1e0740408004070708064140507950384490104095425482c14464161403c0d4a4030003403000c0040c0002d510040c4090315150b05042c450160107826044020715152150420000085e40f04807800140003466280c28000c0c610001441c0c540900c0600d180c0ea0340540200c0094892200b502c1c02c0e500c0e040910420310065071003024030700882c14203049003880050600081810440101d820701e4014405400c0011100c1c1411119281681c0d84a1000615500401c0048aa0b910129a03080000b84e5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 523758507 1250 523757257 523757303
    0x2030c1b0616020c0a0306020c07030606140a0b070308040f0f0503040f081006081902030c04020d02092b0b0c0706151502070e0a0507050f0316110c01020c09090a 71
    0xb1500510b1003400500880c00400d982d0703407180c520800d5000110a9041c400a0b10303a8020307003580f00f2404c04880b00c0c00e072290f84000c140e0711070f900725009902d0b001205410b07d1800c00e000c4801072058084031884d140b41906c005041c0071000304081c0c01c071510030013140c00300710302140c42040c015004400d0b80c0d2619100d034a07650f0144100d00c58864903205912081c2c089400c50301c07500040720b00c0500103185c2104080081d50030380c801004c1c140e074140550740c5110001c1e160760008280081404000699401c071500030880390661694080e0a801800c09040d1000c64014008100498004c1c80b001c40720b90f030341c202e840c4041c030070074000608043c100300786042e40000f0060200c090394601c04038449014041e0360304980d215054070415581c400241e010400c43e407070980c80301c0d070450a20f281140c84c001c01103169010591040d541aa8007180e0b410b196080c1a5005e0b01084c030902401d0701510110b9002c0300005d644000310300c0824840c550010209403400d804002c3c00350011740c4900802c880502d0355590b106 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 523759757 1250 523758507 523758511
    0x1a01030b0a0605030613061a0a08070614030f1306021b0601061b0305120601020304031703010602010605120c0f01020f010c080405160e010b0f040b070809010e0307051302030c1b06 79
    0x1c109420300e00d01141d50724011400303070b1090445030940c8482821549031000601106001c410700c44018079018000d545070101614003a103928001002a5454a00003c01480340800c282003c03070001e2017030201403090094615000000d1404040380c034105802c2481c000d12402001005030440049604041000418403034121151a22050600c00c51000e000c0040b088811000b00007038020842c083c0d01848621001c0c0d007224040c4101c5e41482d40b00e94550020b5071030000104002400440104145a424004c600103090140c4600c02e140c20544607460344c0d80b014600c013500c220113400600e09164030800c01c80c400000014024031403514000c60191481005540a441c50b025a100c000e091040d0b5440702411a031010b003040e80d02c0d0780b03001016012900840c1d250f80d40683c04100014601c03580902801c40140512000b587d200d05110000d0300c2c4401c0100980e0007500f182c035081150b5524010803c40315070170741c01c001d42c1ea956803005050b0315208010349188808800440002e80c0c12000811034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 523761007 1250 523759757 523759771
    0x180901240203030114040222030c03170702060d0b131e1116121103030403030b1003090804051009080706020d11012702031c0210060e0f060d1a01030b 66
    0x1015a03080341c5034442401080c0d462819844004c88030b00b041d600030640316680c280343c440c101c00241a01c68075020369038011394174080b840c2018014801d100a0750002d051000e04040d01e00f0300340343e012840d103010359034001c11869900c424401c85038845000004140711410b00820000e030201002030300c5000c0650301c2c1d020452030132210040d00c20421045800d00114030a0032203040580f9647c82c0d00010b40b405102040004030052101c1c1404200081c500940c800c0d2030105600f566181840245820a00740b00205420f2032104808521480111030644000340c9031401c65002d006001da03084403046c4d001524074481e2203030004d072461303011074007041d00340c116551030718483c1380e050545007030f07804507152050112410016190b52013180000c15850340e00c05000e841000588598802c0c060303044048070000340c0c10030340d480d1080c0c956030b10442000c0c060b41200396100f420210407182c1c519000400003401503e280a8500600040035010541070403034500f09155580c5034070305151103039070599000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 523762257 1250 523761007 523761059
    0x6050408070b070b0103081b0a060c0806100c12140c06060906010c05060a0c031d1f0c020624030a0f020a05060901080f041104060803091305010506040605180901 71
    0x1c0b400700c11000403100742139001046181940d00790713241d40603140d01003100e2468451405684c030803089030a000d009811402581c0006101c0315980000d00400001046144240c210f040321154072a0000d00c121161a044162503241400302c0342c090301e0303540e401018800d40340000725010890800014545216480541d103203c0e41d511410f005683c440c021890040c641d4002000003080540660b005400f14405442c0100e01d03c0710001d02d110b05102c04403240c04042c0c2001c47d6050300510074070700070114002d001c3c000700100030405c00025142e40307001e4000703141a140c11000e020698010118a5080b00e4000d060304e1104800740740c021802c01c92003400302d0060f9000c0d00002964030b0301c4d00550b4044030b0107844200c01981c0c4c1040810303052000030011900404001650b400d00e440b24070994001d4034900d402580c0d995003510802c01c0500c14828408005418070005000507244c6405540c2240d0303ca08125481f603081d0141415907841701071110740c0003d11040005030280f01c04030102540e170400910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 523763507 1250 523762257 523762259
    0x1808060a0e062404020405040207060c08070212091905061c450524060607171c0c1e0c0b13080c120a0f080103110105030406150605040807 61
    0x41c0d40c0b01c0004480c400044050342c1060944640b0707000c046036a2041c001c0c4018601500c1d00002800c980120301c084e20502e554000d04240d40f40c10110f840e81002c0c0d140000c1c50280006410f01003188103001c0101d0090344036016448025070801c070780c00b01414009213401e4a40444c6400201c0100c1195040360b001030524542102952040011100040c007404040b103a501c40d4001032100c84103100da80440000c0d0000030140032500902000c46010f6035140d41c05074242d010001c07018050405060309218030003c000c4903000400241c0b600f0001201c2071080354071150400d00c0001d0038403c0542944096081c172102c07141682e40102d0300b8580c6004000d0f0008081740e58041203400f001e9100380189680314040110700418817150100d900244601c18041c40d01034440c1090b070078020446030101030400086500258030780c0108505441b21060f02d0b182015600d15101c42c00382e400e94400c0175051180010214052003640d40000082c03c207031000b00c000080c2e84035402001c651042c41441d01d11700903500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 523764757 1250 523763507 523763531
    0x30703020c0714130c11010608060105040c05160b040f050a210c0b0c0c3c0d0f031503061d0f0f030910021501090911220c1808060a 58
    0x1a0100d040c3c8805060016042c150004007401082c491005409020758006800e501801c240200005441e107500034148a51500d014401543d440216120a002d020f01406c0799100d40e000a0a1480750824141341c5c0035116803c0090780d0500c1f4020140060103000303400020310224801c0b0b50303110a80421808603228000400f15006550a0f40c001d08a001d80400700301c034860038001500e00418034800382c4440c1c41100c07411941594017800c0000c0c62039880010740900c003040c16800310003c0d09001c058018075402c480024031000c0c9a0f10301006061b960100340840718030220003940070315070090b02088440008500704260343c1154260750400e202c0e092507400c0024012074880d6030b41c21003600440c1480400b03010000c910b803401c09400114802e540018040c803d4114403a03000301440b400c0001e00b10010304140c44203041c450211802100511456540710712043c111044c001460700300003c5c1507980f07401c12135981c0c1c0000c080c100751005545010030f01d80d5001c0358690146241460030040594004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 523766007 1250 523764757 523764779
    0x10e060f07232101050405010b0a02100f0f050a0e1c090605030603030f130f09020702091302042a0201140601050316090e040f050c0306010324060308030703020c07 72
    0x551120015a84045880c0c00d40c40055201d400190b5020300e6505100c0801e074441c0304241080c400220b11400e2a00401644c1014407660f4007401c1c00894491510030007842c0a59504206010303034054a60320b03c0041c03a801440da100c2c40070506988c109011070300384206010050300c8004106c3c2100d02030480c004040828040c200100380040c1c4d16200c00041ca0020706030740725000104100d406010810465204c40e4508000708009000e0040c0c4030b00c0281070480802c1900b072280c202988051042010340050381c5c0d00a50300307600001081303682c0300d540c2ca24801710340501001500c0740ea1802d02c80b8044007180c14003e044121a03c4154000c202880c0c00c102c41d444040c0e82500d4031808203008101140d1024040b0030809010020340c2085600560784404400d0201c3e030490b0291029904800e0382d01c01c01205005a80904d00304a0050490b541140c8984a40d414044d11303a180f50543e41c050303040079a03c00c2d00048011074200c55440e0b12803428030809006036108807036805403805040004a044010b007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 523767257 1250 523766007 523766011
    0x16080a030b03120735071b06320d090f02030a060b0414040f03050306030f0d0503011a030f0a020c0c060409021b07060c02010507032106080c0102190f020d14010e060f 73
    0x100d070566401c170700946010b945a00200702580c0262150424059082d018450322000700800c0e519450640030001211081180c0b4140703540501d2a0002007040141e6130750700752950400d038201e00040501c00d500d8000e50900c03142c20000d4040c001d07400018144200b40c0d114070f203103400070354061051000611450400d4041140c00130821868020b107440442d21420155501c840d01800700d40700400281d0b030300340c5084030200800c00020030002c01030004a07450810840301e80340c1810000d00f5420024641c0c503802200a000000301640860000c141c124100024198120080e0250340d5454aa162201c06907004040600402003110104c1c00c403080c0c0080c14400f101c41907030ba26400903e41d0f900464084e40842000d5041003000c02c1d003100320515605582540c4a01002d000580c0c5103890011803c140c440b001090640d009000601e006c0a181070189145a511500c8060600c84a2000400c10244c9050151055403211240304100c1415444511500000821101c041e500c541070000000d4007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 523768507 1250 523767257 523767323
    0xc0108090c1f03061e030218010806070f02010204150504030c060905030d03020f0409020315010f08070c140708010e030408010e01020313060b1f09050906030316080a030b031207 78
    0x1408050358800e42c40900c41c912046141c0740c0030501658540714081d440000c840810b00c089003110041045213400d07458941d90800313140c20551250324092036181c0301e4500408100c1400740c15102640d009100b0350448002d04650180c1d402c2d00c0c05a268000c0480d00309000860b4500210030020500314080c03e0380b4012990700400401c031429104c14120b010b1b4200c40c0a2121601041c0004500d10751980051849100d41d03050b07056081c040743c0001802c104503442103e007400080d01c03d20134a02c1d4008118848550409454400f82188410582c5881c4160b031022040354600040010b0340c440c003000510484000b41d00030b22105102c4590309080b4802611207881c0742c1514080d000c0060003e811012010780020881c4940d456600d40f5401040c14500c40700c80043c54080051140d0701d01600c0c22600180c056005609100803004440401144410081e04000c800300d0350b030118074400c0d0012641c2c4540a01651158800c50110503656004040704462040e60102d02c0b040c00d0504142d034411380742c3d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 523769757 1250 523768507 523768519
    0x1080105041b050714011103041a01050102030409020702030a0609050604030206150a06120e070b130906120308130c08060f0a05070906050f04090218101734020c0108090c 75
    0x242d80754161816400302504030b4801861008001e40c1c40401c1c800c02c603d4011b848280342d603e1030180f800003642603d0386600031803d42c900d00188580c1c1d0740002964180d82e40110016912055400003034608107012700000c000d17a0401d01400200a070100da035a002d10b01c00d408540b6503448000400380c0c1d40e856542441d030002c1a8000800106100d003c1e84680258007003000149449030729116820700e152a001070000400c005a50342e44038821090f030750020b24003114100b205600f8003e41440c0b02c0720030030300a4100440d02c408034a0102d10441d9101d21564090b0313400ba0360b01d548130f11954a0341c004903000541501082c0c0055201000b50040034440c01c0c269a44881e05410110145e515800504440b01103030030920000c144594141300603c1178000e21840c0340005044007080082c3c0000c140c0c245008c11980600c0e0525100049925541001802c034003512404100000710b00d2514000d1a14008000320074010f654440d004076100c401010203982e0000c2560302d00004d240c2c0c4001da801410380100b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 523771007 1250 523769757 523769801
    0xc07090c020304080a110114030a09031d06030109200318060a1824020403141204060c0f0203010f02210135031608041805060604050d2109050108010504 67
    0x89040c0c01c0e03080d085005040c00c0100c403c8d901801c80c107030340049500610055035a640b440a0540008104828422002a02c1401d902260200c4c8a900040c442c2003038440d1945c40d94410345000ca011004034142c203500c160740b42d15104420010b1740f51a000480458001c072408a11010054001c803d00032005004040303101005564240300d0b0740d8001c007140c90101c8840c1070881900440e00041008501440e44401c51402c4028170500302038844d40048241641000100003c3e40c00888010030f66070402c41894a9050600200b8090705030a203a60741c3d02c7c2c1c40042e85c8c00c2d450304046503c803210040750341c48555681c6c85a483c0d0308c0e4080401009002e031030031946d1140c9e00e48120b032241c0200d544610252410051201d15801008200170001c8440d00008501403201d00c002c602412000541401c080c0201e04014011510a225a001c0d160003541520700340b00c01e004103a0600c61589611464800690b54141001010521030703009150000c0c40c110700026003480c190207072082040c07503a00551042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 523772257 1250 523771007 523771013
    0x170a090b1201030b0a1b020309091e16050915030a0c0c050322030b180f0a080a030506031504050d1103030405030306010c05120c16080a1a1b0c07090c020304080a 71
    0x103a50024403003500c0319100c0361002d4001c0600c20061b40e0358240d980003507480c0d584000c10030481030030050500d1450050100211408000c400c0355503003000c2c0038141e8030b1540c0b102c050211150321903a5041c1d40c0000941652800040e251001584182150034003044444001141202c444201c01e0b0042e00a40c410321007034001d01c03800001840158051070922907200d607640d941030100300f000c49000710103c081881c4d81100070818020130042c000da1201800d80c04941c2e644a0301a03000b80181c100826a88100141c03c49c0c504000c60031704461030b500204407500e003d01d01160368610714650000011403c0705610b020300303400010f0f6402254008095811580c45400442d002031146000382e82134800d40800c00700c0794151000400492800304040d01c078102c100b8146114240030382e841517135643e00990200c004142c00d190001550002910303030501c252202c1e1040822442c40e0140c50485072800500c86003480b6000071900c0444604590610a8111024061ba05c9000e0b6115541058020442030000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 523773507 1250 523772257 523772273
    0x11b0b0a1517010509061602030f0322050c040c0507030c020402030a110a110c0607030c060e1011130509090706080c0f0c1b04050108071e03170a090b120103 69
    0x1c40c540078801c4800c4503600e0100c00c819002c10840110740740d54843c14040c1c03140003800240e6000a00700c2501e0307524160000c0081da04c1c8150180d99941307440100c00309946680000f40c00801001d000c2c079a8038000d00034100356448007446402541314a103400300040c440344c00350050310882601512002d61500107902804040c1d44000d0031008040c0c1c0d40c1001c40c01c809601000b91910b214140c0e11070f019010b41c070b1600b510340000d03901914440d00d800d01104001036441205501079a83c040f00c0403429003042e889803032411440e28458480f031800c111807200324242800c0540302c045269140700c102d140d525000e101a2000030b503801c030305582010000707100b40790164400301d400c41001011070340740c203d4101d2600b800d07030410020715540b60009045040f59043c500c1e112042c1c460211000c00140d490106c0e06541d8860705d200304100010300c0c07100580c141401c0c040306401107400c8000140503400400d4164101d50042e01500d0200310019008142018043c040d60341280061a03518840c0c0d085840b1105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 523774757 1250 523773507 523773521
    0x90f16110a140a171201080601240e150a080a0b101128110906130b0102030d0218030f0109030e0f1c080406030c02150103110607051506011b0b0a 64
    0x34611410b0080f500040d181041000201e11a90b00541c603020201c030710701c2040c081030303200c021690701110060140e822161081500401c44460a000881107450140c403142820001706900c0003d40711000d028141c2c42009054500c0c1c6655042c960780c1d2000010310407610140c80c019000320401000d2805140162801d4040c1401d10007283c08101c0f000070500c191608414200c3c001c860341c0c3c101e241c20004d03841c03003042c080181141d2442c3d07075203400d03804559881c46020001c0300840d2540381d02d0042ea4001e0003124a448010350081d51f40d43d0070a0420b00f0940c032929062402840b030300b1340c4031120034070610400466175410740d110050312004608000e141c140045026504c0002c541001d00304106842280242512401d00c1d1601c403854040f0246c1169200710025003990407a00032a50f034200380041d142c0c150780d0f009403a05064035200300416910f01601c1e030300819a1040044100f1010400080280301d0b500985e90542400000c17200c009140d04450401064000b48001190079480c030340e00820 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 523776007 1250 523774757 523774793
    0x905011427070207090e01051b0d0e0f0c0306060102190b0606040503030703030603060c111c020c0a0623070506070c080903030d060302150901091401030b090f16110a 73
    0x494420040c0d41d100c681504140c4070840503a21030002000115454025600c2e1210450000c0015240144007807099044640044d14040740c005801c0d2a03002042e4020250080004202c641c401d000c4c184490742d510803240a14404c3c401c07000014410b40c80081e007494404da5a069100040d041075642c8030114401402141d84000188004035150b1000c20141c001d0381c1c00303542d0100c0c02c2455400c0c0030040310303000b40740340d01000340d115542004080700280400100181c4241c1c900c40d40600074080341411155403940e0b901c01048030700050403591200c2d03191148400c80b800b4042031116042c1c81c022500c16104002c1c456000640000d01c034601643d1031f42c1c600b60081c2d004518080840b0006420b66001c00c0286036004d60b22441841541488841da84806808401d06443c2c81c0000c0006403005c240762081d514483c440700d01800207a40719400884d4002c00c0903111402e40d0810841082c0600411078a4851022034518000c10092082e000c41500c0540d40c40603090000054403200d5481740c06441714 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 523777257 1250 523776007 523776049
    0x32030c13090f0b0a0c170105100c1704080307110108040b0619080d03021206040c1b060f23130201140d021306020105060118050a12020f0a0e06030709050114 69
    0x2c280440c40040301d1900c01c1030141c3c40010268030400c0c006e0044001c84124030003202c080c1d8010300c15516000700340d1011b04607604140361503640c2850802180710010900c0005a080030900003203010000000e0a4814030410384803c2ca2410030004691103007045802510048807440440d90344d00785000101c0d44000c80c51003000415413a40035103460300d00304198550010f40c0c00218098404854030099130010822101071004113007558004001c0c044000300b01c951040d101c02e00c08100200c9500c000c0c986084400c050220400d0a0608404c8040d103151010102c1010740001e01810505c8100c10703013242e4146c403400b114240c3c100d000c1d84245c0040d00380c2542c1903801c10484c00000b5050b8014401010f499002190320b14100700010134404155100c840e042a83e00024052592100d80000c2940c8268036400300407500d42c00058281c03080410055001100410003180c8140c015a4981c40b0300415000c445802e036846c01070030700300c480920800e800c00e41d18400842c100d00c1d01c08151180a19440c102c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 523778507 1250 523777257 523777283
    0x70c091a1e0411030702010b01020a0b1b07120504060f050705150702030702090103060b0307051f030b0103060b030f07030605030c0a120201090302100e0102010606030203090a060e030432030c1309 86
    0x10a08a41d0b5420f41040f90b2103010082006141c0d09000b00c0c0c640c00703800c0c405812400c51541d1049a0020054405000c0614505581c1e01071420034066561241e04001421825260790340060300c01e0380a80101d200180c080c0b801020441e00070300440c0d0103980e003d40204540108200031140c81500a881d201c118001004080003603550718550601031400341d180041c800401104040c078018050340003074001e209140c0c401100c1030707206412a0000d4107a007004920311000f0801200181003941042c290714202109015440f20313010b60541c03159145071020801a40c1b950308050340c6050000703600383d111081d2507061100031030f000d4040301042d10604240b5019605d03980050311408040d0380e40c200040c112441d4603190360707090166000170503d6007011460760501000c21500c50082d042c01038803083d21072424001c1c9e180108201d03801000d60141105000c45507401c440001c01c0d9a082c0c4040c80c60a0310344126081ca4045200407040000610040180746001e1140c0003600740d441c0c060f0303030003044405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 523779757 1250 523778507 523778509
    0x80c04120c0e0703090201090e0702070b04170d030204050d0201050d14130b070e010c110a17010603050f0f0d0809070308070f03021b090c070c0b040308070c091a1e 72
    0x12a03188054401c40366848081d0a001e24070303501010040c0711108060500640c60050307604580c0240c00e031903040b01003140c20799400000703a00d0400da40d80000d846030750020300050345a041024088520350007400303450300c0b000c90410131000d90040f802a2680010000c00910040d8050801019041c821400c08500c000403450100706200302100c1c0400f640003103200c602d0400000c24000d070782c4500729003403014180c10280d0008040c0c0c001c0f02c7d0000c0401e0684044480c9990b14041c40788003c2280d07880c003010070500e419890707019047e00c2c4402c0ba003510440b10b0b450810900420009040f40300303d03000301160071024600701c40d11100508221f009000e141d00c00702c041600b84005181c5240116909084074206103002803900301074080c0e43d0f14010355407420300515500e110915070480c14070048aa154860790428034100102a80a40848400041c0000c10003148401900f01031b4046e003c0d4190842e0703100c540d6402c0e03845071088141030800e0704038803172042d24000015804007114008010101d0400f58 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 523781007 1250 523779757 523779779
    0x1051912180308010e09101d010e160806150103110705030f070b060d0b010611190b0702060c12010302062803050a0606020c1e0d080403060608060601080c0901080c04 73
    0xa920180e41a181c0150344061541007030000307005100004c24000e081c82d080c000380e40c0b1510290412138603d5110301c0b0080c0a0120545510000c00c0084020040751941c031b04c103155250801c0c0e10059171200400000100602c002c40c131070348070301d0441191030a001c070103000440017000c44000c5414080c0051101d100410b20800103444071b0100e0381400c47d529802e506041c0b24a6034000c1800340b10b509203181e02c9001a44400320a411620707241000625003048014007401e002070070f88602e041a80702c02c620001d000217052518064001c43d000d507041a02c0d030002005040c444c003800c580108401200400050619400411040746030400d032000401f40c0b414814250701c02610100e0001e40c4a00c00d01c407401c031151103808024000c2e4001401480b07480c40200341070302c50540182405100c0c1403241c40e49510b07801c045600311580501d4151b5101d07164074200c130003440036028081c030900c034030b0300052850b50140e1922030203508a00312260410f5001401110141001032415200784400d02002461906031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 523782257 1250 523781007 523781021
    0x1305010933020708060c09190612200a02070e0c03070914012f0c09060a030807020409020607030f12140a1508192603010e0a020c240f0601051912 64
    0x198441c2647c40c000f01040180c008580c54021b844a810050100041908030030b1500419190000204111140162103030641507560104840990b00290031001581e0210b030183c01c0d20b0481c1d286860a45134030105010320b000031504040450b4900344244175112075802c644622000515042b990b07150b5449200b860ba246e03641c0004800b059140c1d000c0d0001400f8003001611500640d140d89441c90036a0010318040304922010b801c180c00040c64009541715038008991580c2c020b082199210303420300e0300070011502e99140c04001410300c61400c0c9080120300070718120b107002949110f03d41e01c0e6645c045004068a03c00720381d0000300e002000420190030b104003100100e04112050701210136040425802e5103540e200016004001400105c034100c0d2003d60f415158081300c880c1c12540d812000500078458240b2440040c030460850f0580844551640584039103c2c20310131a40d51103000855a00c10420b89907280865014490002c000700303042d80b00050f014440c51720110188225440104445c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 523783507 1250 523782257 523782271
    0x15030309131b0905030c0301050705090d0804030602030108071d0705040e0a0912021f050f040f2d0c060c0f060b01031d161707180b0402130501093302070806 69
    0x3201504014600c1d050280c941c10f524147c0003441305181025005006118444215110303200381c41641c010300010100350350146502010840d41d95845a09042c0c0d200410300c00c1450b600342c80c1060740195281801094040c51140e10740c281018288200410348020040c440e145a6903201018001f041007401e2003000417500750040d007040c0c03a0400c90b1100707100942441c600c01d0360629081c4002c0d40950403142d5803003a044101004419600d2424503040092102d550241031080200070ba46140000300707100100d44144810298240d86000c04c0d02d144020000252540c1850f04411f404140faa0f0004010748505150000742c0b290703103030400034401095500d506d0721640240151441d00042045203400b40a14400c4840b92a040c10074031561a043c0b40a80e842c54036103900120b00414854010a28540c001801075480c0c0b06884140c00540d107c611803640007070f0a01c0750010340200300c2d084c00c0480d006e121000c501c500481c4a00050511840c5204008601c00c03040b00160040040c416036000790b035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 523784757 1250 523783507 523783517
    0x40504110c240c07050c0d06200310060c0209040f0501111b0f0a21180b0a080610231e0301060810060504170a060204180515030309131b 60
    0x111002c004880400107040f0b00c0c01d2a400c100100124030006582107410034115082d481da041d0038500507003d0300c000d02080c4521480d140d6503460008029015520849148580c01100ca64502c4122402e00002d080a500071080c8404079004c505400c4990082d41d0149001103601d00d0003076a0004640e103c4544002c80001030680b508090000f4812000001012001091800d509441d8880c024081c40020556181059002d090282c024501a00c8090020b41d072860000d03640c042c4014a40d00003850100001d00241c0001d4407407a10028a65803034485a6844412002100301d14550b15400e10101180c4441400385d41c009a500c0408502c1c00c015258200b616945410400382050001400444102c05050014032401e94400107a03812180701d40e80284031603100b46101400d085a01c600900201d00005d408188012803207052400140c0710507040203265922481c800e9181901c0202c2039050700208a28486c91030302403101940c0d852820700c00540207281031005a600c1c5804521500850 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 523786007 1250 523784757 523784803
    0x803010f0e0f0405030901110f121c05160e0111030f040e010608280e10150501050405060d09050723090106030506132d0e071703040504110c 62
    0x101c02000580c0c00100380c07441000b581c01c090750f460351030303001380b003943c03030400031001003907040e41104204a4003480700074000d40340e5900161041100381da2040000401808074070350544880c451a00c070b003520607400701c252605200e19280040f9425240c944840341004612000706011503000d00090100c21149812255514a0704c600c46011000580c800d01c28400f8080420008620250b844040d6840900e9407034030007101401101d0051554516920540c480c4020700616440d6079448500c044400904e811000303566080111628807440c09802e07001a0705006031061044542c02c0400304503c80c00948007110784403251107a407115014950320080d0001e1040781e44030306210500c5405800d451400707210707034608407022031030706a403607200315440383d50703c00303010400c0c05084198048407100e400c40c50001c600d04045030005003040034070701c0030940124034002a50305143d6109000540c4044091420b00e803178601004002c0440310301452844104110100c0000c6081c000c40850882c012580c4c1801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 523787257 1250 523786007 523786019
    0xf060d05100303090614042105030307030c1e021c020715020703061404020f100207121b0b0403051203130f0311160f09020f090d0b0103031220160803010f 68
    0x36016a0b04c4402885211b00f5020103940480c022a001d6548030549400200803c1010341c41b07241c0b2260014006000200c248a131f00c5502d41c000700132000c00c9603121820601304003624210001f8481481c8050390010060040484032003130f04c03101c45080c0e401942c16680d81c94480c0c1e20000a04182000107800080042c0204541032250741ca00384680107403011145403586c0818900c414250310540f180194101045d00c04e4800c10406002d172400d40480d00c440e090502c2c210343c240d441c04681020594000b0b001140216646080d00c0c21650404020308a03000707966401e2644e036001400407015410304680e80c0c0d01066041e01c20785082e900c00d81d580d42d28503180900c0ca500b402c2e540e800c00082054048410000c2c00d5101c01c0140544441c9140141e44903040c058003e428821031541c1500403140c00000424802004002412a402900e035031241c140d98000c01004c9507503940121800340394802e840d0600790b0141000d0700c0a180f40f0503c6006070300d000d80711302c1080c2e0000da00100241e90b14201c01d02c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 523788507 1250 523787257 523787267
    0x3030e0f030d050a181505010e1501110a05100617120f0307140a0c05010c0807020c0f03010f050c04062304030f03050706110903191a06010521070305180c0f060d05100303 75
    0x49c0384c000d101038aa4144107110400118003480124101f0005450000400c0c105200c4003507180c1e402012208003215170801007024042c0c030b00c25011000780304c1340c104d03101400228680b00c00c0b03031005842a1421403803800403085074000ad8500310400c4600e40200040070f03c05001040884480e84401e1908400b0b49003060075541c00204000c10443d201e0103200441c0d800095a03040c8080455056802184c40400301c1d00400300b8a0551103801c0c00d080034400d101114500070400d60b00b243d640e4400d002e8100b000586010008a010010458100010004140a084d582e04103910910f4442e00c1d2107031070f0302c40100340d404d641c11113030107200d00241d000306900c1c080002c2ca081d00721900038003103c078041e500c501c82c40819445080030011145000104030740e1090089a9207500c2c11806030300710808142c40d0410300c4400711454000b180c9824041948503a070804c0441c0f0a0355064000c021070020388003071003281c075500a00c450b080b59090141c82d100d111a4007805104210407040b4280841c510308000341 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 523789757 1250 523788507 523788509
    0x80f1b010b0a15170c0c01150929190e090706090609061e021c0804030305060f0d030c080c010216120503101e09061203030e0f030d050a18150501 64
    0x540d000c04043e04030409030400e01000c1e0021030001c40350115a90100800540d100d00211740446518003c8600d84450581501c0020b842c00e8071400c200c240b19120349010b601d01001109082030403640c0c680c0c00c0501d0002c1d0761120513203d25003000071041e83c5019401c5462010380d460703051600020381c1402a2a44552000001e203c05c1c5840c030321507842e00c600501100c0400100c80d1000d05c103c000440c5150007009101182942e80041d03e81203a9661070040400c24241c03022000a42803d001c03132030300e14040500344407185005080080f401a56581950300036680d03074044803924000c0c8445a40c2000c01e00c0074203894174041141400c80701d1140b41c140b0414032201c20000c1801400d01c1441100412806003505544030032080e55929601c0303a6000745a00c14039403100000504100000c1103001140c00d0a5180501c20b403001d0005007440e401c600e488210582c403143d1103900500220901d400c40c1d070001078001a4107840041c80405202540c6140300f17450390291403266408150100680d001e02c01c082c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 523791007 1250 523789757 523789769
    0x405010e060f011412040f14060412030218060d1104080a02010207050909060f1503010606030608010c0c17090d061505120109120f12051503010e0105040b04080f1b010b0a 75
    0xe1940340307041351480101c0c0120180021908500000a010490b08640d010040d9400c1100350200c4444008810f6880c081120119081c41c0d030b2a05400701640030307000742c80024510029880541100700240141500600051280151500415000080340400078405012880c0c05802d000c3c1d12400003a103481c00d81d0384110b01440c07414080101c094808600301e50020044800c240c0d142c1c48200d00814180136150140343c6c554607000c00020301e9901644084100d4150200034031210860322030550702a809a0340c080c01c1020300d0803600c1b4003a21584000d241034030005110008290301c584030f00301200c1020701080880414803800344110704c0d25246115086411200901c000030203036490302c40d015800c1956009115481e0f113441c10f0705001d0301007109603109a110400440c5004817518212548481c15980031754600306211481503c10302501384500d4210008500903142e41d0383e03000590b404030841c0c03840303c0000d000110a1800c0600d04440c072003400320002c01d5141c0074408000c81c01c0070075030000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 523792257 1250 523791007 523791017
    0x10504050d060203040c0e0901141305060721020f040e0606160206071e0501050619080714040b0603010801061814180106090c08040b0c0f0d0209010e0405010e060f01 73
    0x200a20365510403070941d51584140050388076210307464040e2130030905800400c04400c072002000006d0b1415401144403400c1d0707101009241d182d1810a0111100403a00981580c20500000d421503002d40c8444ca94610706040620b100f5040500c000b0403a0042e400142541d10300040070800c003003c6034079943e00b01d0003c640c518078041c0300c060b03030141c40d400091000340500c802080607001c2c000403501e00d03840a8440501c200100761a842e021717008000440380f9601c5407203617201112401e408000e510058400b24001000014140151200050804600310750302546612541d03030a030300e03680f001c0d50007860300c04008074106043c4940700ca03d4040306404428158905004031040c1d501c1c3c1c40c002e41d0040b03070b500d6010300c855084100041c0948107603003003801c0c81c50a0000c0e001c003603948040480c0c03013180a2583c00541d038071081d09103d030500c60301680008402003807000480c01c3c02981d00625149030141408c0002e004540e0205080e64002d90000602e404002c0c1042058101078080c1c0407040e40c24031b01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 523793507 1250 523792257 523792259
    0x50f01090c21020d09060f11090a0e09160324090f1203110c0703020111010203060d080f0c1905010b04050c03011802070602030c0a2601030210031416020705010504 72
    0x401001c500070345607400d22601c03881d01a1114041035604413800300510316070600070302c01c072801c001c405031001c140e6030103817280340000d00958510894240c03030700b03400000c2884600d40d1900801d50140c20300503001d0f05d200d00601039030b40480307181301d600e090085204e41a450f201c03001a548821725005100110901c05041ca2100c800041c40780090034070250f44040c0e248000180002d00310011300c2c880241c10254000040c5134400d001d80082c010040700d100766548014007440c8150903090740020b88803240c111104400032000180c2000c0500200c20410549034140100800007620f016003011444c0c1040f000c3c8110721081c05028020b08160001c02c4d20180868104209541650721051041e0004d40c186e02c2080801ca0285804440030705410200540d2a03080502d840072181d44400140400305800c103d51500035060701541030b4400d9010800c0c0e007100c0e072941d001e2010410228140d5420580d40e4a011401d02a1131080c150203054483c10540012144020203440e00102c0d802c550305011003448 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 523794757 1250 523793507 523793531
    0x8030d15060908060714070606170d0c0203070b0c030f120106120e1b18010906140901080304030b100e0f19020412060f02040e280e0c012003070303050f0109 69
    0x35070070b80201407460251401100c50748460b03011f004528004218504140340011030b6809540c0241c202107400b01541d5550050b040304ae90150364030b00c8029015000352000700864907411001d414280c00503070549285c03d4005d1080802d0b94080e03440420044e07840ba00601c11158845034032060446000000c00c00c00006c0038a980e5601c40819810a010540701031040315912002e00300030380c8a1404003403126a5850301c10300c3c005003505005841100c030180340e002d511071030300f503d085040300e0070b41c4042d524160a41d1610f0404c0d5000806c420041441c0450010b050090140c44601c181008444d0103198108010003000c1c402404108114082c0188010302c0304103203c004458810350b0208000680c030407a00500f034080d00031070f480184045002810040e4007035104066101c0c250003c1c4040e90310550307196a0004588401d40c0d148503690082c0700d80141d55016801503404034004900340c1950042e20304034580303590b100c420102c0001c2d40711010b03c40c0c0190300810741805050b490006202d081c21080b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 523796007 1250 523794757 523794763
    0x21c053c0402011223090d1e170403030504110306070e122b02151003020f040605060301350a020618030102034f050708030d15060908 59
    0x103620a892000390324045011a0300070322040e0740890304078409000112010500940d10100402c00c002c1400690700000c0020b44045100040c80f204d0b41c882c0030400104120800000d01c9400c4250103025003441054400c0c00c1400030144542c0c802e0b94042860316051070410b2911503e0001940a54814800d1040ca183c1054501440000079294481750030b11061a80b49420b614500d490b4404010259000c40220390320075200d025a180c0c0c00700e482c1c041241a500c1e0b02500304580c980b94103190240240700600e410003109502040040010546644075000564079900c00e9004c0b01c0b114400c44c104010320843c00c01e900280440403140b0100a0308121401500c401e40c0b010024410030b4000b880004142045004140102001c0c00031074403490110700286d52921641d0024040800030b0107690800c04018186050040b81103030340c0310442c03904024411240020450413503040c0603a01c400300e0038810030809019056140d00e008a842d000600e010303161202940c1080041090f01017050003104000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 523797257 1250 523796007 523796101
    0x2708040b09010c021f0f210504060b0a0b1305061206010311070b09070302040501080f0a020f03030c060c04140105031b1305100305090c0109080c0d0204021c05 70
    0x21095403034500600480f1207188400d0025804043e0540c410340c8144820625902420b10343c07120181c40f4a00402902c40101c80242e6030016018885012040219030300070f40e40040c884d40c001700d282c0c1c0c0340c100003c3c952045c54000c2820107002003070580c81c07010715203a2000204800d482140c80c0c0381421900e4100480002d0240d410302d5101c82034100580741120440e80c150390400d10000050810320402c43c2ca464980c403081c1d208505000000c148028040390103820500c441000301041030256080c440000031001c06d140c0d16000500c80d802c0308180900c1807074428003105090036919420b05020548896240409504120092040207007131b4042c5600006405a1006055110035851a20003a03003106904659027003104d180390a15080e4040c0c114174080c007418400d954643c4005d80046524260611030b43c2c1c941e0307120700740c2580d007400c11050181446001500161800314003c8041800e040e0761005050003e99035400c011b04400b5001d41c034a020348401845002402c21b00a104100040e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 523798507 1250 523797257 523797269
    0x40e0a020a050403020a170c0604060818070810050103020316030b0a0b060d0905030705061f05060c07091503030f08040b0f06450408070b190906270804 67
    0x20004050711001d0059007038038029a402001104000c1d11501410148800c03026000701c94810920001d04a14000040d942642c55582c1c50410303d80e9003400c26000780c0500804240d03d03005205c40402d02c0041400810407513280c1660205481d45907205051800000e1808441e001040381b80900000300d040d400150080400c00c4c1c007041801080b00040e4140c031a401d8070000d07041c600468101000000720141600c6405882505c580303907164a4078491000d4040c0070405440c01030b920921180ca411030181200c421140e0450f110142c490708404c088641081c11250b050043e1401041010307440070364a01d8000103490700300100e082541d00d108140344050b0001841028010004805441c1d00c10342a10301901514548801001030300e0410b9264110710140c0c0b0341840c159183e501c1e841c106500b03130b4019580542c4080c038026064549059042d4060300b10b00045100c041d051040c0c00050107690050340c01020005840e5207034aa100c2c484802c10000b071000218a1110f40c00413445404c1030f2812101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 523799757 1250 523798507 523798511
    0x7090e040c0b0a0905240901120213081f0b010f031a030703030305011502030306100309140a030f1d0f01260c0702010f0503090604020d02120609160b040e0a 69
    0x200d51a00e280c000040d9007104a0903a40460030106056004546004a4100b40ca212088034004509501201110744c0003400240341000008030035403080114207a41d4140e40001400c1c0b6264000c80b42d50b9544544c4040c103203901000d5058118012895400401080c1c00c0080000d4091a800681040500700f00142451f5a80c0e5034641445c1081d800414941001000e41d040952a4030300640102828015040c0300308140010740a4580000112401408000c0004011041200c800c44c05416045400c54000390090740a6500e22420010b03001c0c824865101c0070030084020f80010003800004002003601c4010851000031a2a10000d0340e084e5582071a00c1225056810500c41112414a0860b070140707005004000100c07840b0805028140d100b40e0341c80075180600481100c650000303441504440e000780003c2030040c5800d0318021002e038400341002d26442102d44100d0b003088412030707000d040c64002041c822815480c4000c8580644802c0c0d54140c14981000880300084000400d0884500d23 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 523801007 1250 523799757 523799761
    0xc0d0c1e0611220b07020d02120f0303090f100501031e2d0606330201090f14010e07081b03102a0813060b010c06020a090e0a0507090e 59
    0x441900405540e920b440c08803940e841c0300c00614080c442014100b04003840712400041050242081205d480c2c0743c0040112084a0a61b002c000b1580141c41b0004660311420f0a19801504103001651151920b80d001e021941c411180d00c41c102208040044034140c41c207070050000a2031000258125203000340700d0400f02000b403405a450040c0b0103881c810300480340030060b00110401b1820b0f114a4854002030000e590780364201822101141c0a6a04a0f60000046054229441c000c41103041291001042c2c1c10380b603803144514182c01a4044e500c0c880101584940c1e80024002c000d1102c05500080540c0c91810034882c1c1c861150301180103141c0740003107000c3c419035002c108290700400b01600c02c01003030111403210703005441d009040c1031a040d5440329001e0854002c40710588250001080114260069a41c030b02c0101050f00d2414180031036816650085041d0b88003500001e126601c501c00024240350303507201c201e030b80149046089030400c001c1029095000304118100c89420101a07425 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 523802257 1250 523801007 523801013
    0x81302010f081f0f170303060105040605070c03080f12100e150a150507052107060504020d0c08070503010612080a0809101109090604090c0b210108030c0d0c1e 70
    0x6920710201002141c10100e8082907134011542a00c0444541e0720001d1074100c00c0c8814582c580c042101c28a001c907800b8802080002c1c0500000d00d00144182902c0a14607100c0da80c0005a4001c80d81d8111102000301b240109242041e41f1542c101440f074901c1003020340741c14038596a4050003000e84850b0728100c40d4111141c0c6500c00100c0190400d842100082000201c004100350000c110039200c501c01d070110004211280e8640c00043c0940840b01c81c0f5040841d2111009060054800c90b08433150070103035802b01c0c4c440c186071000313088600045c16925190408150030b455140e0001d540503240202107400080c2c120040302c614080d141008010740c1d80f4a0b1075182841c6c07030740503000715903400d04940c80d0106840100604217203000310f80040f8240c4400d801d000c01ca90074800d00428011980505002155010780900000415902c0032900c60410f002030343c98440084e400070b50340d60300c00320300f40300750040900900c45410640e140425040c078460302c0720380c1e418425282c4400c504103681031000c18 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 523803507 1250 523802257 523802281
    0x3061813060b060c070905150d080d150b0712030501210f0f08030703060504141e0a1d010b040c08060904120c0f0f11191a0d1b081302010f08 62
    0x214205001c00e8900d041da51b045100051324007101c9130440c4a124a401044c0c5150888a410b41107402c40701103400c2c618240604401000000d040d400d1240030f511000580c046100c00406405102d84000440400c8100014003550010380100032410340b009822081c0c021103200800f016500200300c8500c000c500e0a0102241c2c4a401c0040c180d24000401c0088c9513405400c494125102518200581d8154100513298080c094440d800e01d146800b418104418034000419040300d42c500c000a031003403032401c01c02000c21801c600310a060351280d40782003003890079100741c1202907401d081c25800352400500260180f000140300409520301607882c42c410303e20034215640c55a5124080e0316a03446182010249078403915000c031030000a81c074000103d42020120f000340100004d010815550410303446090341c101000d01d640707403003c083c44006c0c041b400c503001c2c540c120a10300800e1546805058030081000100500c402e0842d0800020680144d9104c01e4010382880300f49051180c1d9100d1501070a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 523804757 1250 523803507 523803517
    0x318020405180c01030c05120a1b0f09080f19030207050a0b07140c0f04090201050904060603020307110a02181509010824010e04080702060f0f03061813060b06 70
    0x3402501d0942008180314090342c03505006041001255030041c800c03c011405c0e14a8406d070750000a0082c400c184800f15403050942e00031043d07910119400032036400e05612902e209099030002910784c1a401002c0360030080d1356000e03140407005032042180716134041d0390b603102100d5400109070180003007105040c403d12044d00030300360017400c2c485919603d181c1c60440e604440c40a560580e10800c01c601240307000659102e100d503024050091445542c810007004004454041e410b002040108015603940d40c811800a0941c9480041c1c981c101400d0041050503810400480c60340943c040c4030150751503031883c807030300c0ea25201c900e05d841d034500d47c22a1468241a41c11a0012003103030012905800c0464200001da81480e06400031b08c9194070303e1881d500c02803080c10525809000440d0100304040010302c0600d0001e081e20b442d1004660b0f1114141d4484644905007003008000e0000d685050380c0a01014481d000c2c600a0340c0c1010040e01007068548500200083e43d12009010551591416a5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 523806007 1250 523804757 523804759
    0x20f0604030207060914090c0f0906301e0a0e010c020c030d03090b0c0f25120507030e0f190303021005010906030c030602091807050a1805060a031802 66
    0xa44581440d14001c1c0d5940900e00800c0046042c04c0c1c0003088003400d41100702e10002e8000e1a50245498000b0030310003640c0098a49002c201e001c21503a26580c54840050070b01c4a2410007041e031070300d040c2c1d4084460032041240d4400301c4110310140310034041010000070180d99404841a02030301d5649840d000ac0000342030255003075091900f010142d50300401c07216034141c01501a11075501040100310101c40000400424200098002c900203c190703101904080e40c590700d9561030400c070715840f0790021a82e80041d074612561043c12108101d10011000180c003e541030240c10f001c0e856401806000041c0c00340707030040b1003c01a00a090742e41c0303160180c5100514a42141454a03418025214114240c20b00c140c1c40c1444000070300710b0868425001203030303009041201240d0a5541e00d0000e50b00c881c500b680d22481c00c0c800c20180109850542d40136080b281c9510b5601c0c44c55980180c501860380f085c8030f856104013201044107440355021a251102c3c18030300081e0487e0481d007900c0801c0e000b21000703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 523807257 1250 523806007 523806013
    0x810020d090f06150506090112020904022503030c030b0a0320092a0c0703081b0303150301050f010602070b0d02040b12010501200c1c02030a03080a0e010b06070b07020f 74
    0xb64103100c0c850b8461a401070a10303040d400c442e82c8607014441c0038800e204440740016681142800c68405540c0501a814401040989440801ca032100c1c03541c0303508104151030740710b691011010590144119111000c80d0b04040c0140418900043d02078002031001a20342020101039030400010f02c0941446041c004186440d542401003041041545441c0c1c055606209507847c840c0640340d00041d540404860401450041d0440c0e503030049580080e8440000d5070003c40e44030010352014005980b0a0303030307608100c0010540c281c0805094034409400e0b0105001101c0c0141b110580c00f1820009850130b60b030005030b80301c40009403c0002c4c4203039400304040c05d201140301c5500d070100403035850403180240da031030b802c6400d001110804d01404040343d0321141d014400502d000d040150381e0001c03d41503603c1c2c4920b84031036900401d00b400030b0108218002100c00b81001442500c4e40328402d018406000200321002d014404200240f04a41c0040e00703031004240040e030241c0c401c1015001c1e1100003015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 523808507 1250 523807257 523807283
    0x1d0105070f05011d0a0803011518080313051206040314070804080f15010806060f0409021e01140406021b0a050a060c120e01050a0f03111b0607090810020d09 69
    0x122074001d115408242c400015001030350304c450907002910034400c035000441c25207580d00e0042c0c003460054900c0d030110b080c01404114003207040e000342002401003901d11b003d103698441e900d40c00ca107031074040c2d00194480c24603800b50350300c0c0d4440041c00c2c591040c1c0c1410850480e24880850400324003e840d030041000400241c0401c4444c00421040c1c440244c820403104070351a101965038840509004007025580488001092880d2801d43c6644100c005403000070040c0c480d401040b0b0390320080b1030500301441c118560200c41d5a20103421a89801c400f544103050a0828100940b178071109800180b42d0310f11400303084010350360024410f00600b4000e0029140a50310800609000390140083c0da1210300b007008009154080d03a0703070f40d01d544016503d1515000c05107505840240c0960081020035903900302c11351841c18050f00500e13511000c4802500002c03103140e01340d4a400001009441040707001c502c20007011100240c06078449a280c04003580b502d8070458018001d00d0340300d101806d03d101c07070a1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 523809757 1250 523808507 523808513
    0x504030f230d0b09010501030506240d0c11070609050f0d0624031106040e0c07030903060c0e1203040609030b2a0910030b0f060c011103010b09100306061d0105070f 72
    0x40104a036503002d50b0f40c80145c1c0c0c1d0310130040d800c80c0c07803c4403203a42180407401900c020744156058180b020312048078603410401c86a400c2800c4841800c0e1810200c0c105403100c000031002040460010581494905601c50805c800304420360490804036000e400c80141180405c40706802200354040302d141d00310b4072070036603281101041505d44801d5419406000c01884182007080880b000d03104d116044078250303220b40d0395244450340104800d50402070250004400600d0038040c0303042e41030440d550764807d02607035010061090280f200134805c941c01080104116a00400201d046070f40110304410607554040c14050701c1d00f0800201c1d11480301c000c034a90400201d40380980030030002070f510b08030584000d0350254203e800e0404030641c00081003940b41500d103042030007800251004000810745803140088400c0e0b6400030b0b00224a4003c1c08100c03da014244070600c441500309034501444518a0b0817000b504080c0c1c0c06100b0407520100f010300911590040d0212001903070310071106440016142 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 523811007 1250 523809757 523809761
    0xd020c15010f14030303150103090b31170901020f010e0a1a270106050409150c05180411071b031b05090c090a0302220f0504030f230d 59
    0x10260804100b088a000f00d400c4400b4480040d0501c03010b0011450341d20f0b40c1e0103200030020030100080c10582c40d0110080052004005240208803e9040c9081c1b500d030313603000140351500000755482e07004503441d1250114240341c0d440021018001d5025645000c4400100e04007081410030817902d6080404a2114500000f9001800360245880c83ca640c0800c02500e05400c4082e40c42c0036481d40c4d103c0700010310030503046000ca0202911400012184d9440700420140c0e0030000041e5080000c820003203050503407a024036899650549456890002d40740054050400c905e52142c0c05140e40d484840b464030803090440e02d4681e00f0921007006c000c402c00c101080c000242c0001c8411000e0300c1d0401c101e403d1001900b10558000400e262801d940320024031409420043c2995031200701001c0020160700c80c41180c01d030b843c181a40e100080080c16000703806480b005401d90f0181441d040400010a62010780c004e80c049507481c0181c1400b400407035401852031510305884c4603060014200d100700800d9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 523812257 1250 523811007 523811009
    0x717041d0703050a0207020d0219090c050315010c03021207032001200426030f370906050307030e0105090c0306090d09031209150302040303030b0d0c0b0d020c1501 72
    0x950b02486241c1c1c1e9030710414143d00510318025001a40d001701000140b800020150b6454003180a050010740e40c0e01c440402d4821149103c00483c0001060054134050700980a0010b03400782032200302c05009540095583c50400c0c00a124060007180315000c01d445094a440110801d8415071a904240da004034020480b044420303000d03540e0740540700220704890061ba0200c44219803c800a0b00b4080c021054918042c0c81010690004201c0480c0300c0d00c0c01006060200c07100300000d40380c000128109190301e07184103501c0c0000c0c5d0200c0c00210140da4080c0004040d2541480c006449888400050700546418000d40350341c0e500300000c01c0b140346000100c07150000c2044088407402c6d103520000700c1d00c410b11309800360001144a1340a1010406000b0b0111a201d038900c1c0040505548401c0c4080c040f06c040e40300381c002500000c0c20801e0591502038030049602c1151395035004110769807010f428000a2103940d4004d0800b05000780f4142c040d9043e640031140c2b40050b100321040c2410426008802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 523813507 1250 523812257 523812271
    0x80a0e03060a090506011701090804090506010809010218040b01051303110301153605130b010902030717090721030f050c1527010c03110a02030717041d 67
    0x8041c002459841e80b40900d8400caa004800382c0041d07400e02d403811314144030121071003c50f59200c0480300c00161005e00284000d140d101000110744c1004400105406805450b0985607801400035a450080060307640134110000c440004d000241400141d80078014041c60307070142ca401000001c180449005034020100b0200c008000c0d90000c1030b100c807110000c40c0103900c6540c1010088240552003020350041100500100c03001d0014148440e10544d00c08440044003220788800040800c0989040c141c050701c07417882c0039401d51505810040901c101001000e001e080e03480d01080462030188296000380445c1800da010300d540b600d44000d4120410402180000c15406c280b10480f4852030070307a8031603914807000d4000c0d01c0200b120000d00c2c00001e400720195200c0c010b060303030800d036a00c0d401c0b180d51000f900020882c03c62040019080300d000010300c90408400b0048110105e90102c05c82d41855071058480702801e11190034400306001d5a040001e45680c030889181d18150700e94480d0313203d004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 523814757 1250 523813507 523813513
    0xc030b03250b070f0b09160b0a170c040503030c150a0b010207120501060e01061205070f0c060e07150507141207061d010c0c05060a14040b0a09080a0e03 67
    0x5021440c80041c5918030030750856051000e018018044080300401d121030280c008a6644d44294480052103102520340400641c03140c0c0014251501501c0060b00403c05401d0f41420103218a901070100e078107203810004503c094030f00281c82c9034034050030380b03025190107011240c5912100e003029a4a4514510220444400400045003d840c0c0e0003280120395060380901182440c1011050307081c02550b908036615502d480000c941c40541e80c5043e0700074100b60b9590035103006c0c0b03844150200c64002e4092800c01c115001c407000301e0398201000030840c50344540b0018551880b1482d840c10310304960003060004c900c0c0185628001d9001e805000032900541d8a04d07401122a0040d507521844030880503407102080c40040e010500d41d9104800032584100600010001071181c9401c490300000414045101035000c0c005100b81045881d2303220359900c0c01049a80244000c20401c85001080140000d80b0b0b00c0004801c1d68240e085075545072360110825403154546040070f042c2110141c42113010f88 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 523816007 1250 523814757 523814773
    0x11160303110d0e010507050c09040b0403030e010c05041e080109290106020c1e0d05010e1209031510092a0c2d05150a2012070e03010c030b03 62
    0x101010600041070011500c078503110f2112040107640c02c0c1c200038001c2d502c2e4002c12890084580b070716942180320306d1007040c000885181920f4064100c8020f03032810112603141c180c01303449440d003000455003940c400315122a5015110010014081110b40021040d542003052000400ca200441003502c0d884480d0000741d0048448c01d500b15103079003417040740010390000040c0001c5003821a00403d00b0811841c850300607004860101d848007440c2d020842e816950340b0144465410300b404040403d02d40c51001516001c00303403001a603554103000c14041a041c000c4d02181c4025040b103c140020b02c0036800a00024802031000960a6040c82e0851414030400480e803074090700c100701c0050f02503804524400d003551410100d402d400b00b42907007122001084030000700031440400ca40748e410701492991100074078203004400203a944100c1c9002c1443c4c40da1110500c0500280150346034299401d0110310300b41d5a405040701c000e560b1002c656015440c011611800c0c0358150821080c00c1c42c1036003207034100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 523817257 1250 523816007 523816037
    0x61a0c01110a080a090c050d030f020606010c030801030b0c09210c1c1104020c030c030403050c0a05090a05060d14030702090c0924071202070617040c060e0111160303 73
    0x5205a4041d0b00c00a68040002104600594000300c4c4141c040d290040e02540c5401c04521b42000340c84045c0c0208000464a0300520340c104400c3c0d500800030303e000f45008c122585e01600c0d448041c000113060801c40d0380028044a010812307914070450007081542a28091109131804444030b02c4010036500400d20701030511f00300b030846039100e900401e80d4012183d0094490001042040c1045907106408000c0000008020130140000f420548061036803503245240161030209074840c1a4054100c1c034504004a0f520b24080070303482007040b00081040d545400005042d1140018020303c0c820724082c02d00640d60000000c0c1556034400c0d0346c1c803100c0e6229005002500d020386425203078040c2c1c003680745c0e5084017048903009070751120084120f8200002a602c02d403011041c100c020005a101110412016a0001034003000c2078201e5010303001da0030640c9404580034801e0040c0c1060018240805d00c950b48900804d203214032a14064444a01d502103036141c3c00681444290001000b411040d006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 523818507 1250 523817257 523817291
    0x8100e060108010308160204020f04050f090108150a090206030f0f13172506140a0b100309021311040611030903030a140c120418051005060904061a0c01 67
    0x5258140c503441c14030f030300e5940c480d8001e500140c0d18811514074a5191801601c8500107001200000100261140d00300014001c034840043c1d0320620540400c2d0040101c09004680c45041c03048070300649403503603108840d400c0a440d584c080290081000400c200000000b09502801230281c140741d0340780d07510703820304020035410480340240009248120072518684244000c11000318003500c820703805e00215a00440c901020042910610b44900d0303400c040c2540002003270792120b0044400c0022010f03981c0802c03d04a114401d1909042c2e480d850780c829951aa4000402024880c0062007902c407100c84800d0103030454402e0b174010508243d004103042902000f5100e2501c4080d00130760505800003003c80e001e41040e03101c1c1d0110881040b12402c802800d00056000c001c554842c2d5640b20710301070700281c1140610203200d015030300c1c0205002030071528082003011500121581611542c8003400500105a940d0000102c030f01241080415000f800c00500340c442c889000030424008025001c0383c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 523819757 1250 523818507 523818511
    0x8090604030906050a1209060b18040c1818030e0312070213050a02040305030d020a26060907020f010e010629040b0a02120f2701021e010e01060608100e 67
    0x10200b0192507042c4100d0384510094200c00680703103000602280d40708558003c60f04401400e40b2020b84070f540300c0c80c0c60b0400c500c245001599107040c4481503d45034441c040308168a008865825652444590010391b0580040c00300342c0c01d02c9400042d6010074980540b072001d2101c10f082c001c0c06021964907408101400b600c0314190040c107003420b400441a0114002c00c0001d00551380380e82c0c02c5c0000f0021803402c002070006c05402c4c510050b5101c4001e20080c0001c820071340404a10f500741c4a4840c40d8400c2c0c1c0200320b802400035189801d61341c6821000380c2c244203040010a1031586040a22072103008150003d41c2140c0e16107041c2040190000798400c002100d04010104c8884100020804c60340103000504501242e403040e101c0004005030746042581c441c4049a102040205217404104848981000034000c41201d0801c4283c003480043e466501480c840c00420a1441c1d1259110074203400a40c0c014249000070840c071521040f001d812210144c80381441c0d00085180440c20070720503160700b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 523821007 1250 523819757 523819763
    0x30b0c09031209150c280506060a0f0e0402030a150609050a0b010921080315090a1e020f0408030409051e010e0103020f04020c01050c04140414040605091903020a0308090604 76
    0x8076113080c0c1d0b500110313000e40c41003850580754460344028058120160000307252040e070f400310b020b814039000d0403e145001005462503114400f1418200300c400115481642103a10b0440b00800c941d030b4030b000190400f085040d010b001078444040c1c009580303c0d294080300644811141c00c001030384400401404540c031006074070f40403800305202842200d003022070880000c000300500015560865460251581080c0d84548d19800c0400e40e4180c2840e01501c08c42d8410f4000302e080089030040c2c2c101543c00450090080310b550b5002030305100c078404034003c9402520030803080b695910b50307400c0500000d10301161103142c5181800000500895690384141c100d03244040e034102e0603400c42c0c08000300703103008800c0c480d4050307400c02c01102c55003000e02400303201d007a020040c642c589180801c13400c90502c0c0c1d802242e103da4030300664a81d42851159a0700d0b00310b0b400030000107a030343c4c81d40c1e40e1038a41068100341c00003810714403030303401c1c01c0546c0060b05034480c0b442030390759240a8030340710b06840d5a140181d90007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 523822257 1250 523821007 523821019
    0x106050a0603020301121e0f0b0a05130b16230306400e1c0f0201020c12161502040302011b080a030c09052116080d110106030b0c09031209 61
    0x308042600c038a94416080c0003103030072950803210b07544d0345052019112300c225a140180380c10441ca500340d601c103080c2d01601c2d40c46010b03e100840c7d510314102940040c0421625012100100c045600c41c181c1882d5134014501e54544201103210712814641003159803a01c0740e5030f410420011203a16102c030501c41c104030441d64a94001010089440b0102d00511040071551106400f100c0001003125490004080301c0e02e41151030840c00040c1030b43e1044200c0c10642e80100200b0b41c82407000900c004041114085164851284003d00660325940d000301821100c00c458140701c04405660040c01100d00c01d0300c950300001c81c4550011840028403001500c9000d040c4a5240c400b80039402c04000b0410a103030038a0100d4940c80050300c0400c00c071304030005900090b92041951402004104280e110501c21100d00c18600000c150341c0d511000700c09020407454017a000000328003500300001455001c1c8610300b441c034006a0424690b004020380c24400d11804000450a1b80b582080301d50700c000140103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 523823507 1250 523822257 523822289
    0x30711031f0209010c0804090507140c07061805030f06012d06030f0f0e01020c1204050904081303122c09070e0a0b0a0206091b1f020f0d020106050a0603020301 70
    0x1050025000f104003541441040381c0c0703140c0000c01c03040c0140098007020700000f070141026103004203083c0741890100c0d01100c04111003101c0c04400038615044460600e1b201c04801d001e14241107080965511080d01407280203002408003070702055280c180c07603107901401008103c1c10040380750b58420400c0c010518640010a2040301d1080d0400d0b110301d13000300320200300c00460740082c904540800d400b406140e540400c00c901100d03400d03c025200510040c2e009420241400002101c514000e0310042a881002404414400b680801d1000940d085018060301e0300c0c0c0180094907405410308003a1150014042410741071501000c120004800a84012160303901c40b242940c0204020345015800800c01a0014003141a8001040440000d80c09000d01e400d02100803840e1001200303494010f0920386503124025251000d01d00c1c01c800d00d404202400411503581a0300382403200201e03a5041c09a8246c111400e0303015004401140d000340c0c0c0d160b10b0903581e880308608901081c004c07000300b0400105 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 523824757 1250 523823507 523823563
    0x110703140403152d0b0102580903030f03020c070b030a02040302060315090f150402090105120708010e010603110906070c051804060b06190c03020c1203071103 70
    0x210980c9054298136401c0c070601480030450164400d031002c03c19066840d03001010b120b503814042140c00141e031014224170102e00c003401e030105000d164402d1558502c90303030f04004003440807042099502a6078142c1c3d025070700f0005004216090034002035000c6245000b01c108a10720a00c00ca030000404040900005410000c02d40b001d50b002a0401407440d40922001c005a5951801180104070012a211884c3d8454041c8200c0e0340d00140750032100c0d85034000f0800c00e0045c00c110b10003c41c10440c1d0040c0d032001c3e2200169101e00a882030403404c104207104100500e504030001d141a40c0c1b0583d00c02100d0381c2d132000f048050342c01d04c0c84c601841103028002d514050034554040c2120301d02c60140241c7c40d503101d0021941e0072450300c2410007002048010b04c004c0c40f4042c4200e42a480f0181c500c0d07454143c0440484605100a5061108021300c0481c0c0c001850b00c24420340b80c250300e0007841c020a00b10042d10940d0f40350060401030701c181441143c0040b4602c1c0c00944070301583e4000c1110b42680c03103049 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 523826007 1250 523824757 523824761
    0x90c03150102160609080601080d02071413021606051f0e0a020c0f06070f02010b060a0c17180102011d12030405030409050a1d070506030a09140111070314040315 71
    0xd08860662003000308941d00e801c00c649040024006943e6001182c81c0b90150036440e180c41a0304c16985500440024556241d000c04c03002c0980b541510008401400345001c50784048011540c955114404650094144010b01c10281c0b014000c40701480b158881031010700600c000391080d20312501900c0010002c0c0608003803510350008072282c0040c14003208d1040d00d0700345005e04540310880c0d0405010401c02d01d07000003080c040201c1c213100802c0102d101002040c038501c00d401d10842800a0b602c0484100601c4002483c83c058a161445403100c00104503101818441414280036500308171219001c040b8201044085c280b001000b800040d00c410b02c14104d640c400342c002c2d2880c0c04104404202d05181d4060180600c4c40007000003190f400b09503000c613101004512021058200c08001c100659030381080d40e030403840031f2000090803181d92409001400d040c010b034220a500b458614045041c11101501c03065001c1c1c3c40301100c58602042d000d0580c4254000100114070a49070200c44140315 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 523827257 1250 523826007 523826041
    0x15010c020301090821010b120c0c160807090b0303030c031f0305120405040c1106010605091c080c01060803072d05030d060807080c01020a0206180904060b040b090c03 73
    0x2a000090072002510b407520f20b5801703107446401c8048807100402ca4110b1400d50540185000c4c5130007401c00500c90341b02da0121078042c20402c0301000110b409503650209104240301e504c00004018082599040f2850701d400d814030071050303078502e40f800100840c200442124410340700c0582d010700e55650585600084010701c0b2060008941d00c020210019500b0070880c00300c00140e03104142c80e245054108810759801a0b41e10082244080c2c0c6154003d0000480070306403805800d0064440281d00013181c202030400714041600100454880203004034000140601c0141c40024071089844001c041d5581c2304e040b1004109266000100300174200181c140340d0091551001d08408a000b80c07603591443d0480e03001030f09000da1f1440c0c10421040d0810521b002000450f01800d038030307904040080d448039a810303800307401a5400114860900450124054100402000d0013414241801c0c004000c1060141150007035103440480c00844c906400414402c641c1100500c4c656039401c18425801c00311 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 523828507 1250 523827257 523827259
    0x10050a1a0d06090b250f0e09091f050910050f0106030b040609020d0c030e0105160c0804170a0302060a09350a1d0a080706080c041508150915010c02 65
    0x1507a900f901c00140340210450007441d60041d204141d454154148011502c0c0480010070b00c4025000f00105603008859146000b4049551b0b03040d694844590754100b4a4460110301e829001554940b600c0100d684141c0c000e18044080740c07a80b0507621080000c542003a20642c480703039016001040310500c00e4010885101010f4000319100e5a50640c54040c1d811004103a04000c1d02c984101100aa052080b5940d44460350000c1c000e60400b42400d03041d86040c1031950041200110f0084203000c128800c4500400e0669101b10a906009032100c0e1500303540c520440040c02000e000c0340e0a010760380030b499002c07904501d0f00700401e0a00ac255400c0ca00700c440c04d24040131080030b00100090700450140507112265201c8411100c03804281d48050000810740c144074517000e8205100c0010002070950590311135081c261034645542086000364001d5034022148030084442c03141c03079560f203c01054003910070001d03c2150017401c2010800807150440b0303030035200c440f014000702d429881040c00d1800180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 523829757 1250 523828507 523828511
    0x6100201060506031918120516020a06050a020709052203110703150c111213030b010b071a0613020f0405061305031c0e0108180f10050a1a0d06 63
    0x1070ba4801040141e00101c0741c0c05503034080b80d505002040702c140a2408420101c00ca075550b031200aa0310301e0501e00041100104114010945045a005444038183d0340c0e034000b00b07802a8aa0f46400042141c1e0000405ca0010b00514900250026950040714000c4001801080881b100b00c0010804003c00401c26010460044100040e01c0428403400d000303103014150100c0302d214007c1401e001e50741c0155441e400c11641c44403616038080c011900f0340180c1c0c480500d096946d1000c182421440c4000d070400303000b0600d070500000703d016100300104400c074455140001003a4018841101e00101160f07000d401015501c007058420003190b00606490901c10200c0307013415203d20201e061600140e0082d004c1e401c41c51014800e0385000c00030010f116070003103c940c00c51803121400918903103111000f10305010300d40f004240050805d243c03000c0100ba030b02c0220303225116403002c0640e44a00c1c503131851200615180218600b50032a019441c0254071090a000c11207602d0010300203400d61424060351030070b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 523831007 1250 523829757 523829759
    0x30e150c0307090f031217070e1026160203040501170a091202100b0901140d0c120c0801110301120807080412060507080f01050307031407030c0e04060b0402120a0209030f030d09050705090702060610020106 90
    0x7c100bc04041c910001039041607280b40180724030000703403822041c04080d9401071100300030580c4d1020410181d4811b01c1d00801c2c06455044069028100c10b2000400c004500e0001d04c40300c0360f001500620907845100c0070b0024100d640300b0701440030428041d0340300c0382a101075038030514240403081c4040d03144200508581c5641c2c40321982540e1504200031124852516001c00c00c0308024040c5414052030036244510f117501d404180ba0440e0305000c001400380c86c01099074418011004259401031540700300c81c200301380461400c0b900030301048407000701103605480400d07503072245105424140da04c0600100f040c1402d5072605000c04840e80000f803503910505002200040030303110302e04010428a4610807841c2824034000d025240c2c4529007500840c03050010f40d038410800d5546542007454500c0044c5d503107000c54040b0b07081a0143e2140b016501c40010154004c6440c0d90203d83c695002c0c200355003125496104010820360140c03104c40060f80580e0101d403e51400b03418072202c806580c000040c6039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 523832257 1250 523831007 523831037
    0x90b03040f02090907051903021318030f02010204080607090305060a0c0e010c0c1502060103120822030c020d080d0b0603060a170a05100507030e150c0307090f031217070e10 76
    0x421040d05007c40c00303143c2d0310710800860030100b0121410480100051128541e450608401390030900c00140401c0505009000303e10700039411a00503009074415200e051a100c5070191040f113552200f1180c0744a00d20000c0c0c905400f40c41030041d613622941c0c0c1c42c00c640c1c05280044400542c12142601d214a81d280000f0b440b00d0a4076401e411318100c0d401800e110b42c91810038507804441e10816a0502c81c0990401c1a031068640b8802c08490640c01c60102c2c60714642401c40d9040c9501d42c1c025080640305541d4000c4c4800180641500150281e00340030905160082c4609404107844054114000c5281800741c018003148038003a41b012801294201850f43d00d641d407a040d10700d1b000b164025540c03401c0c86800d99060090044d840c2d0100300400080c2030050f0503076083d650060520071880740210103d0348061003480104010524120110b052646908100500ca0f40d03000310080810100d90038011a071101c9103015100c1e04003600c9190b030018110041c0f00c1101c08030800c440810a00400792500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 523833507 1250 523832257 523832269
    0x604080f010e1c0806040f140a0b040506010309080f030a0905062e05100807030b04060305010b030601050103090206070f0602070f030c02030f030f0a120e01020712090b03040f0209090705 82
    0x100c0c0240000704802e903003400780605242d054410f03660411043d0400604841d0012030031a00542c00f51000142c074a80d81c030303411004060048000f03816803e45018010f18030115001803480083c121f800300490740b6460700640c1200d1210078000c3c15003000f401100c4810800d50087c1d0b40c00140c0d0f040209488455030b072085d080c0b80080f98081c1861043c01180c1d040310a03290b09804403085059003050100741850700142c104c084440e0b541c010401180c000403400380c4a50002c50002101800030b202840d16890000d01900e01c0c40c012038040c0c401c05000054940c0310340251100950003821003450040070b40c07140380d61030f850264103039151602088500c000034400c045500010340a55140880100d0702d204040c207040071007103089460744c81407080c44000000d0b40112086c0d40000d0402040799083e00000d13001500030146a01441d500c081109010310011410780210441180d44810b0229298101844e0a00080d94060190610700c03d6000041c1802281c40740c000f20020304031200c45030380f5400180703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 523834757 1250 523833507 523833523
    0xf0c0103020c011b05070c05010c150e2508060c0403111203090613050306161209020307180b0310090803070f050c1b01020c0418020f150d061a0c1b060408 68
    0x100061001500800f4021f0360900540504401d190220304d08449860f080751a200c000203801c051503a46c00100b0000c00d040000c144541419010603101c05150003458000c1d541610034540745000f6900092001e10400701141e050340e40c0000e4805024040006000300ca206041042c3c03003a20040080700d6040c1e07071b84000762918240740600008031a0501c41030505102c80a0601d904916881d100400c0040d007181c11070880d245440740004403410039000091801d2155032100a0441c040c2c195000c46d00d8041d00720720b50442050b4200c1d130310681b803003031070740110b41c40e8540c09407040b001800451b00291003060a0307803906185107040b500f00312400c5182c84c03c200440406103480d5002c1c00c0303503407050758051128002440c02141c1c1046600080454920502203090300240301d8621050a0380c0d26a5401d044000a46071203030300652540e4820b514800141024001c003100204403071450303011243e41900700c07014410001c0c040c0a01407504a09040c0d0300162421183e4840c03820300011461080070070000c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 523836007 1250 523834757 523834811
    0x180d021b0102061e1b040b04150e090f10090207060506010e0d0302030a120b04020c06040606140d060b01140a021b04020f090f060c0102070602070b0606031b090a1508040c080f0c0103020c01 83
    0x7d603030341e450481001050000d2810000034030241035401c240300e1341c94000441d4803668500c5040a150b40c0c000703103000c00d00341d160448500b140c03000c41e907401400003590110380f00700e4003030703c03000c110800713001c1044104082c4040003401a4010071115030705a2084807004401c0150440200d041901440042c2c00e90708801e0300b14070141d005904200074064240140c44c002c00030300081d25424103290011481c03e10f16008050701068440c8450030490748103015403881442b24030300060b01d68004450007900e030024101e02030b401014209602c45c1070f14041c0300729070f00c03924081c00c10307883c1681e8071050020a0440800c9554403000a1100c0c80404030b00380000c0c062144640c00050303441d01c071032034901540440600201c0c042d00c4140200304840301c01c0800c42045848001d40140c45090000c00503a85500135004a98010048901002015008880c041c000c0340b0803030b92444811303100c8010320343e948040c1c502020164450000000594000c1e4018007402c1e03180d00000c940c1d40440b110031000542c15002078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 523837257 1250 523836007 523836029
    0xc051b0301140412020d090b1818010b0a0f08061305040201110607091e15080c0c010606050a02100902010219030210020a050310090501030803060603180d021b0102061e1b04 76
    0x80104d01d68140242c00284030309003010300026041c1420200d050140e85518005c4100d8a00c03403a1059035050300c00501c0309052300300c2203125070310b600c0307866080d4002c11810b0020401c000151590180a016050312404002d09400c03115810070b0310032001741c00301038400e030705001c600d0003540d0011405021032807003000144c40301e55801c0e24180e03a140c40301461003510142804441414441c26841c002d0b00820300d101c2d881c1c41030740780e01e401c40240b180341b16401241000798030f4041c00041c10f40d00032000d0f04900300c803502a1a604c03491030062100341c9401c02402401a04405003508900c10302050301d14401d130091044611350307501603175407108903405100d441021442c00f0041211300f0b214001000c000d418165003d0010754919070f5000c400b03000140681d4402c100200008200c070001c5500940d4a000b140304483d18114003400c0a0f4a4071089007020321054410340308100d0755400001c0581c064642e441c64500c0181c2141032a80c80c491014008030758402c050302038210300700c20302d00181001c1c00c410604 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 523838507 1250 523837257 523837283
    0xe01060c081623121201030b071101092d12030e15011410020304060228021c061a090126120408070914060f01090f03030804120c051b03011404 63
    0x200504d0001922000c60751080304212a503c4000050720340d90441b603000440b03190a840d00002505c002803458074100c0c0ca50310700640c500c10b00203030010056030400012402003686018030740c554070002c0c00030f10103032050380c00039030301c080300c0d4800d40c40403842001c0d450a0740c1c40d40011078004240038400380e20000a442560b600154149407100c441c8091160f1800113502c6c1c81d142c42c030040d4a8000003120400c40030128000c9045400c00c00c0740303d52059078020b1111a10300320f03140f0f40e94640c2481030010f9440c00e03d801400c4005100c085c0100c13200c0440280055002da10300780301102c0340d01e80581d800003944600030740c000b540d1804001e1034184544c04102142c407541002291882c1c0405640039000302c42c18075001c5650002c00d54600d03600060181c45808103c15800d0050350041d903158030201d403041c42c0c40400018142d001003042e01a43c403842000c40c140d50416000c48d404400414060200d8002201c00d0b0021088140f680c840c1960150002c548050fa1540c0c07480c0c542c008640582d40301c044812 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 523839757 1250 523838507 523838573
    0xc060c0807110121061a07030215041e1a06010f1211040801150306050c030402100c050f030d020403050715020c220906021b01050f16030b13020901090e01060c0816 72
    0x406e50011685400c02c140c02e003035941e100250382e021a8207001c4d403080b800b00003044c2480900b200801d095100700400505140c118a80045407000700c50b255104545140080303611584509041d40c0c2d840050398800424401c044803c8005002c819003112054104200c00205040d007800340d0814500c0c0506040c0e0740c24518180041520350080100e82400c408001f0000142d032002c012100f0b45940c0d144c801e503003040030314089140400701035210030280f101042000c2101003503001001039a00c40d070140d6000a507a0f400c1d01c941d22000c0b40d00c140140e08490500f0b009401c141140705000550a140c5a480400d44a846000c41d1401001565802d07000180d5400184980c40e40300c0f4601c0b00200204101e291034850038030720400c050b005031000440210281b049a10a03081b06140c0800240340300a21305021071040b00a40c4540500d601003444250002400e5501040701e074100d881c1e507101d49403a0318244d0b94168140d80880b400b0b0040e1080d01c0c030010042002c0f4010184010b00e800c03004211040046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 523841007 1250 523839757 523839779
    0x110c011112070504150e031005010e01181406010e03070b030703090b011409010e090a0b0f04020a1d0a020706181a13170c0c1503040c060c080711012106 67
    0x1854101400f0040104000b440072002032203140d01d00c1854002407800c2c002c8006401c01e00c3c111040082d05041c4000443e031780320030b41074203070480e181801901010b100120044c02564024207180b0010080c0d4400155294000d030060b075427042c80103040c0e440003038942c0c5502d40f5542003070320107000081c2d9812a080c10441c171621118007411960f404040b421b200d80c00011000d800c14040c4c0c52100000c0c401040105c0002c21865144903804041c0102602d400448860624070442e0143d10401401400240c02d03004041d040b40c540404240d0111950f41e90109080039600407801260200d650b01e044204143c900034012079842d01c2035441201103400c0740c2098071a03d2000c0c02c4041c08100c21015a40044c00e5403002800e00040c81c0b68030342e01c4441156005050103040c03c440ca40182094400014a503100301c0118881c3e489903d02c0f24044e515580f00b16480c24448100a001da03a04204580224080010016490034145400c80b15561170502c4207004008410f090841e00e621298140300c865845 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 523842257 1250 523841007 523841011
    0x14010c09050406050d0f0602041d0405011802030d0503040215120a061a0a140c070b120112111e060a050a120b0109030b070e0612010314070b040603110c011112 70
    0x102c0e0184006070034071000a004440760a4001d2241440341202c10400010740c055034001c02603003525201000900700c0403c6580d008480882e0154604040d281514540584111201d60043c00070560b042d8080c80c151920703800540207076440700fa0303074003803581d0104800010404805a100b1054035410041880c41c165440c82d000b50041c2200600c545d58031050000c00d03104001c6051400740180203021031145490f105c0c0070074034902e82c0079810010030070800c0400209101200c0600c440315580e6610036014000c1c1c0e450400405030707114027070040801d1410407010300d8012840c40350140e100249800084075903105001c5000425404240048255003004198071381854184060107001c02480000301841e01c1d07400003c2c11400c40502003180c1e0f622580c600f2568000c064440c55440d50b041d40b0361040e00200744003c858802141540301c45100300424140100d440c10f03001c80d420b16041050990150040740300210a1650078051740c03065240c01d00681c0607003014100400d684600c0c144180d9500000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 523843507 1250 523842257 523842259
    0x7211b0903050c1c08030f180d140f0909010312030e0c0303090d030504030b040609020f03010c020d11010e0613050d090602030403030c06060b130602100b0d021002070314010c0905 79
    0x1102410808180d001c280380d0710034141100e207046070b480312494030132040008410181c2104000700410005011142c04680103e040183e200255260424100e0791340100c402000300084162000003d4080c55101034804040c0c8a801c85041040d00004900d2501d4241d00c140c540b0180c1070400c1c1000c0340c02d40b00307441801c10800080d04080d10003030003107640d81c89105507141c001d80843e0307124814107108806403005158405610344c0307903040ca400e240f0054500502c041c2e2003480e19664120043c501403281001c500e0542d005820b814030300100c25101c4105030640c03c80a0b5480313410b10140d8000a100c160303c1380c040042e2840e510041070034070500d046c0c061550181801407008051191580000a0350100d83d85454401c401c540c007403a0020203070005610007242007401007610f080e4010205010020b45015078200e541482409806a042d1382809074044c0d00080303d580d901025082081a03010750246500403205001d030f40742e5a6690003420b4444001842c1d41d20092040c0280d03100400600800d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 523844757 1250 523843507 523843517
    0xc1701020c060c0304020a0f090c02100606080402091506121008010e3c0a0209150f0603040501020909130605071e080702070308040906081603080f0307211b 69
    0x180002042e6960b01c01070240c01c0ca11402200040441d41e0302c401e15806046a01c04441c031140d1b4480c03505000e071208a0030003000d40030b0044203c45514152042e50202c1d04544d90b1100340d9111a02488080d09001d0003280701560000000841a12010001c00208130590480c14140c50161003a49a508046c1c200043c01d9042154000c1501c00010711488000b404042c00c203455035148016225581264468041c0d090300c64603030801808000c40d03003035401802134556200350b956032540c028880005800c40e5600c014520b41000385800c180c03014550052059000520340150000041c0741010202c51045450201e504074408200703242c000e2642291381824040c2000314500301020324200504400c80400a01c0300008140328401c014010040d40c20609903980c868480030690082c00c12030194500034858071103000b100000341051101240c2c4c00c10700e018101449800070b030009500150040c1c4c10804641d05989003d00710710f905103000c045040c0700140c0a2000d2002200d00961946c056003408 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 523846007 1250 523844757 523844767
    0x1e04050603192406060c051c023d0501050a090e1b01030b13020a1d03100b0117090d09050d030f030b03031b0c01110706210603020303070c170102 64
    0x42c40141040c449035205560241d018031a6024901c800030001e0320303000c841d040140c0003501c150044045031600e80240140c507003850300e95203035000034508164044016442a4258000084c1070602c2c00815488103124032182d8152000401c040106a480780c4101c9559000400491a2443d00907004200e00c410502086281408464843c0c16140345008005218964000c0076807090b8400051308030020881240e005001c00b0440007900130141c45030102312548408400303c80c0702c401c102d80c0e40d00c00400606080300344441c00e20140541510490520001000e1031800040f40c0c404148100b80200040101982090005208811645c0400d01032040c030011400403a500c100c180741003108034107011803403c040d00301207407a500c100d091600d54858061092840403402040204941d90b00f680c40806044920030001d4540085200d80c002103903081c0300c0c407250b00c1c0c14284c5001d4140300b10040000e101780e0f41d4011074210b50041d902107544242c00d00d41030052800e184821804189410000c500780 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 523847257 1250 523846007 523846033
    0x190302030708090a080102070615060c0203030715021608090f01030b090a0e1c05091806010f18030c1d07050c0a06020c121201080d020115050103090606051e04050603 73
    0x103440348010103000602d001803918241d807282d62400c0014150b9000071983c412690810310300800304035180c1c0c0142c1c0c96401000074010b1192241c20601e5070010080d40c900090781d07544450b403544240307594800d00d409208100111109200701b052071030142441d0383e96007408008002c10028907900c2a8141450003c04562544a4911f2181d01c1183c03c43d002403c4510480f03020300e00842d4102d01402d4104440e4001c2c91264440060001e000054549912002c2c03251683c0c0050101100c509001561b501c0110400d5842401c0064800d00852f0341e80c2c102d16220b80740d03015144120f4002e00507601074544604240403d020342d0760762014482c07510504000c40240403076103445148001030300c0700d900403854510140c0280007000d10010381e9600a6950b00d581c65035409041024455060a030295200105401d40103000b403c45403138042c0c4000840c10b0510300103400501080c1c6c4152030280e900c2002242c2500c4a6400030345003642800b820003140303190010042902c00061541d4060b0308840d0482d051 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 523848507 1250 523847257 523847263
    0x309150c020d0201020a240501090e0a1b030b0f040b0f0115030e1f0b01080a0e100c02160b03090d0207082805120d0f05060a030b1009021902190302 65
    0x98254101d900b2848003100f400101c1c0350405602018200500d5429241d003080300b01e010f011401030604609001c1682e8686d80c11046406180c0308080302d4004802d048000b41d440c0e241c864104000c1c000011210b038581c0c45100c00e80c0b41c01c0790ba18110a0b4003209001c1841080307103405030b22020000d0308518a6040c44190602801c2c043c0b02c003c10b140d2281c0788041088414484a800f00004014814140d000f100880c000b4080d00b0b1802404203243c040401e5043c0041c2c060300640d10701e51001042e1040c103100341c0708003e118103050002103000d202c81c56007003820903a070080000c1142810058590801110060070a5403000f202025540306c0e140800101d8800f06004440d0a410403e6980c00070420003010940901184000e165010303550851070146803850252900842c04c1404012848080c0c0440044078815135000e41d106c013920b00c08000092841c0180340e413062114a4039040c095945c1d80301c005a030003000c5250f003000000d01da07891905504015482718507407888a100c2507218240c5001e51 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 523849757 1250 523848507 523848527
    0x10219110f0a201c0b01050d0c1e0b0c0a03030e07180b010e06120403030c0309021804141506030d03050c040e1f0b180f01020705010c050a020301060303020703030915 73
    0x10264030003690301d02c0c00102103003a07905918006445241c46030b181400c0c4a0801c4c0051008884800301d2000120302400c0510001200325404803540c220fa50038003444400b5072072202c03509c0200040145001c41c40856800140440d080304000800c3d09030364501d00501681c007040301c20354069001180402c00c0401c030440c10003076612001c6000030b40c091403034012120b8080c0c01e10b45540009000599038403868110400d144280c3c0a0307582000400810070045003605c0308000081d511048045e92094034585903901103400030700c5014401d1809105004071400c00350118407080800c0c041000b04195814148046c03081040701d490208454601501c40320b00ea07014500500150710640c0c0c0002d8407020405421403030711981000140e407021b41d504044030203544000e019180e0300200f0030400000741800280c0b0b585410050300500805410003004650b04035040c4419505c074800c0c0c03440140513887c20710505e406107000b90f018220440c114203014000141c0c5a00a0394406d4001200361a100e51081c03030b00e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 523851007 1250 523849757 523849763
    0x6180b01080c0a1d0604030c0f0b040b0a0e040626010f0c020601030f0c09020f0306030c01030629130e16020304030b0c0a051c021c020c07030611040305010219110f0a 73
    0x290700d40714110000c0001e82081c2c80e0554000a0000d03020003441034050fa00c5003196040d20085030402d42b41c441d6803481380034921404450840a00001a80c41d0040003419001c660113080050701656030311950704840b90400c0c070900c00d110700082d1103001d15000e00480805950142040c441040300359400be603185d40521015000359159400c441c10031869225403402031880000940d00c506040c500c0b214035030300a0360709520074410110040d01175400780c09002e0032110520307600b5a4030301548010881091001c80d0b0165020070030001c149035005051900005081c1d0380c40140380c00c1c078162910070903045400c8440819548144010000502400d071070b240d000010500c400e4036a51414000e45603409140d600540d4000c884010a50049480d405042405c07101c1a10320740c01d0500740206022403183c41e086800700d400c01441030000c1046030304811b2042201d01882407410b65203444040c2284c1103481c003816004494028282d5080d84038040d00441901000a00030340900c46074050b030f40303030158a002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 523852257 1250 523851007 523851017
    0x405040b01020a0c0e0c0708070501060f140d080c0709020d140709030b0406021c05131e0c050603130209010906030219260f010e07031401110403030309060207020406180b01080c0a 79
    0x2071141c2946c105541c421a800550982c0764000b92621501030491805445504030100e02d00051340842c4a1002e80c4041003c0c084ea051200f0a4807074040d5503200064509462007072600018600751544000e00c60ba010134000014400040d00c0c440c40180b01c080c1400080060111003800454142e00055400c02d07031002c00181d886c440c803010241000c2541c800c0402c000c2ca0701d000c00c460211408292850780c0d100d217840450107031003d0742c81c058040c0f000002a20b041940c840901590506100945c2c014400d03190340075407486070b940040ca910030b00360400d5032541d448020400071800c081e4081c52a90194517280c8040c02d040a4107408600703080b40100c1c3c0e40c00a807040048400405200090b04069004000d01c80c28008a031000da9400f4144011280c42031745105a1340130a42c1031242d100d2443c81461035501d818030f1074800300e01403c001c0d20203907400c5501f040f17410011f86e15032040f40700420303140380380180b01e403859490401158030545403141031004d0f82080184410072142180c1421042e4242 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 523853507 1250 523852257 523852261
    0xb0427050c160f0605090f06071b031107030b090d090515092205010b09010e0a12030f021501060c1e0206030109020d0f060b0c0f0703050705040c030e0105010b0405040b01020a0c0e 79
    0x701d103c114019840c041c1c981841c00d01030207659440411465410000380080f902e02c6d44808804032240c000b1020610500e01d03801001c540080d10075842d001c20307199031404844959849441d0b01c125110b0070340d014040d640c04620401070464206040500400c1c0840c1c510540200604024030309104020341c8920802c0985c03000c0c03860210a0420003d400c055410402c46903841c0e28140240e40e01c540d00c03c90106120790411580d03803a14102400580d4580c4244000b14040e42da025262550b40000c5101076010340341c41c804000c200a42d000b4001d10490340d44005040e00e509003060581544150510704122103c801c00258032500d003144c0c1120b01d0b00100699030038807260910010070200e1740c802c01403170400b00c0c0010224618400760884c1074815082ea12004000c40356103544440c43e110007449074010900800c481c2c5040d40c80510300b400385080104080541407001421588240c009002e006400314051109090911034158238490a0008094840f10354503420000b151500c1603c8100400c180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 523854757 1250 523853507 523853513
    0x100905030a031b06110c070e0603031204030c0803040c051003090c0e0a06090f0203102907020a0312110f0c130207110a0308040504110418090203070b0427050c16 71
    0x1007404001360002c2d0304006001d00c4080e21034081d444064140040c0c070900c040490801031840040f4020f00e4000c00441c688003c04100800c034540080043d018000844546004100080011445a88900070b10340b5524244010400b11304103080746803080500c0c009407403000a00142401c41030303800f6090080203598454241e807000d81469000b560110707050084400611403da006103004d540007942001c04191142c0c800d0480180224111055072030321a0300ac1d0034200b40740000c0034090300145c00c4c01403442c0c03a6120361a58178240f00704040002c8954a20028030340d03050123400054840f003c058650b24200c3c00004046036800e84101194076400500760003080321510103000240c8010b010f1f6640c00380ea81c02c2c050759907081348c0322b00d50185091202e03c89107150000e0441c1d0958415030b417143c50100c40000404010498114200e81620400d880840d40480e4600504000c20b809a80d00354681105440d03001d43d0502014141c1c00e950404080c09044101d03a41643c0c1d0400070800180a2903845003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 523856007 1250 523854757 523854797
    0x2090405030405060409050f07021f0507260405010b100c03080603031306090f05010302040b040603050915011502010e01051003080c150a06060f090b09150403050f010506100905030a03 81
    0x6440250704c40c2e000500000d2021150300024482c03043c601ca510f8595803855416a03d40d00d59a9000c00021364150340e004049071240c1c80f49803c2982490605c40f0244d040c1c00c2601e180703ca0340314801840d4100790800c420003209008044403402d054445108001490078050001c152012004040c0300001c030000d8940d40f410416612184040c69900ca00180e603450041d2815504d4001c441c44a11142000b041d00c1d402802280e0880d10501d10042ca8a071a01108400401d4003505041c050301030300c209042d11030b040000c802d02a1054865006000c2c800c19800307801c5411502207440c0703d9040030108203098880118600441e600301d41d4590396800c441e24203609000101015004a282107410302048202c16405401501c03c2501c50403a4a030600c04141d80320202c911030004001400c0121060380d04000269141111810a1181c181500c0780e44207810440d5803443c914461399500100002464503020107041071195085c001c41071414070010035100c03d0a03050182c1400702030480311020034108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 523857257 1250 523856007 523856009
    0xe030d030b0402160c0509091605040c030207021002010510091806050903191709031c021c021b010b120303040308060d050a1529131e0b010311090d020904050304 71
    0x61900c810380b4415145c9400e032000f1502a07640100010400541ca101001400850701003992a04148042c03034101044041c190341c1d0300000406409001000050300e5000140e40401ca00b5000480c5070320348440002070b240050340c8200c84040c1400c0c041d002d144500c214100019401030f002050b1952000310040c079512446407100040b541c80c4840d5a6882e038054031b032800348500300c468680581c4a03503044903034038094107040b0200d02d905002501c04c0140c480e4000d1100420322501207200c014440000012a08004c0310f000d20303052488005c0b01c40c100207120b00310700f0b00001c81d6980813a002e24240165a800f00810081c280f1598201045d1540d4502040700e121036805400c4480500182c03408004000303a004254403940d0074044205400081d01810321900c005800c82402034165200401c000c117591801802035196480340c5000030a17031628600781111783c0c6001c0103c0d0040701c1000040407603c81c1c1e40301e010201030601aa00381799440c89413100140d501155403400c161190b040c410304602c12 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 523858507 1250 523857257 523857277
    0x2090703020f04060203120a060321020106080d020304050a0f15080415020301031a090d020a03050315121b03030304080d0c030b031b01021b0603011a070203120c0d0e030d030b0402 79
    0x3c41c0000d40d00f0390000c000d01e201646241c01c010243c6610b16040d05556160100074584414214070310400705a0030058005007140e4400444d65981d540d00b01741c20100d18080c154010380000506201d581000002c07400181b5114125000241c0b42c80f200c4408450041e0703031030b02040b0030100428184080c07000d401c01426083c042c1155256075a1619081800c02421026411002480081d8a01e9400305294103082105e0300601407035055a50121140e500040900040c064400e0068802c0d03240c1c449032944803400b4078024032111071010405041780ca02056401d01c00d90040040000094501c403d03642d402452840200b4094035400707046d8080c02c0303c00740098051040d8040c101c00541c80d06800c000b48402a0244e5124008901e0040004a110003003e0740000d0f081004011303000d420703040c90051030350250309282460f000d580040c1c03c06440d0000e4401041011441200b110014064007580c0000350418141034120400466218034606608900b45a900c070004001c070740782e03601102c0010701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 523859757 1250 523858507 523858537
    0x20c04060b0901080f0c04060e03010212010605040806010f051011101401140303070b04030c0212070803030f0f1302040b0303120126060c12061c11130b0a030209070302 74
    0x80c80748900301c9160005100580000d0041020a500c1c908103440107000301c02c840f0046107803d09052069409445052000340c2541d402c102c0140603026860f00503018110310742e10141e40d24a0050101d10301841a08003010841a60104020342d5503001401200b669480c10044244900c0300e03003e0703081418030f202c0d01e1052824080741a0220680b90360b482e05885600c14a1a110943c090601d40d03a8094a50020041e0400d40040740110340610544562503100402c0b034031310f8002001c2c4050410b403042d40060700b194008414482020b03030720003480341d01c000c02459140c0030f41740a4151030894101c080029000d181d8a0206042944040c070172112010320320705c507031039465030340e10301c0d01850500b0494440303546010011015071400c0c010821600030504038840c00e0811000070f98640c1d200c400a070a00d540140170701039810a25002c140d9511f440c90190040404c460460230610400c03082d0800d80480c4a490f001104149a9800c1445401d40e0b405641040c400c0d078662006a00a201d000c4100b08820 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 523861007 1250 523859757 523859759
    0x5150414133e070305070b060f0616020a0e070f03090501271406040b04141005040602030a050f011503050a020405030712120e061818151c17030403020c0406 69
    0x10750340c6601150b4806266091000c00c03003020340740840d00c0c0128040100090001c01801c0086640d0822968109900501d49502500000d00144090340030422110310b4006800d4000c2c2540b0b800e80c010401410100410561417420b00001441400b461813000145070361802d80d00e00b03200d02544504000d0780d4550380d102c040c06080020b1100c0d4050b0b000c04030341c00c5a851011811410700404c1050185601a0074407215490316616001200003909441089124405d600000d07040c123030113545c0c01140030b0840165070741003500c0810140c45008040c00759140346100100325040205a5894592803240780001c3e40e071312450085d0000c1e05c03d642c00140d15110304480400c1c040408d0b2044810705110f60481c0c0d07410840118199540085a4882680010203018a40c1e095245000c0d8001c1f40310f008100311105000c00d141d10351040c40c01d840391440041c0a854182c2a810700030f4040380501c0e608a8003030088841a5540c00812a490f55a840040b4002c00807808046c000c008403081c848000b4400d02981d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 523862257 1250 523861007 523861061
    0x1302091f06050c011a09010b0c010f0f0912080105130c0207150201140a0603051c03022206030f0207020d020d020d060504080d0606030b01091505070803100515041413 73
    0x54003c0e442c603400f254039011000680300d4068003045000b007009044403003141e1038510324090710340120f00a4074043d5220000304090040300e1041c40c0103000d14080010300f0342120306050030840d540d92039a2040c00840d2005206541e61040c001203d6200b543e400b02e81c844003040201c0c01c0126541c41103a00020720b14070807101c40c0d0190061085807010050b4007003159505004c00064400c10721000d403690700302c00f0102d820440ca22034101805c0758941005481c0c4624140990610000300c4503c02c82680207500510010740d1500425400d4a8503800c00e41c2406917030303000108444890702d802840360414007150070454840b2007100700e546401001c100241c1c13400d424452800d0303002d580c0c4d8600d464500940071405034043d103d240030403078060b545c4256080c207290145089006440d2640300340f14003884100002940f49005601c540603000c11a44018508018021078600c00721010140784c200780418802817030b200c003082845071803c5034039814010b650380d1060020004d060b100740c100c17200a41821a1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 523863507 1250 523862257 523862267
    0xa11030c0d060b121c03150e07030c020c0609061611030a060e160e0a0b011422050f1309060b18150415060302070507080703051f051302091f06 63
    0xf54000540d00d6000036140d4070102c1d81c6464840740144d290b40e80c030102401c14244a6403004d58030101183d03105007410303201c44400c0c03105041128288000b07a02c4480c0032480c981d050001d481800c00130740f0700509246040c80090424040e0800b881c00d07003000c0003180c0041c490079040f951050300d07001d800d4400000150400401a00c0304014110f050300c1000703c440c40c03604940041c40210340040741800d2840d00c0c2d000c0d0460181c4003400c1c04070b0410044031242501581034000401100e140d840c035421403291160007040e0103492a0344242d101e460741841000145e242d2f910f10b2502586070388000100301489142030310040c001215208e41050701c0d5154180001c1d18060403502031141b110525401140c0300d0304003c1500e480d8190407400b40c941c2d410030022240031f60094101c4c0c902c82c405681c8042c0c0c43e45c071514581903007030780155090742c424146040c80e01c000703914954509610b000c06110b01e00e05654089180d0300460030080c01039402e5000540d420038909234a05004010140120295075203c2000784 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 523864757 1250 523863507 523863521
    0x418090602090a2c1509090705030304150306080102190807021f09030806090c091002150a022205030a020112020705012a0309050c091f0602010c09090507020a11030c0d06 75
    0x161888040c0c0569410801084d00140301303040080c042d008000010003801a86400940700c00300324402c000002c102594244090320203001082400c00d0380124401009081c2c0d68164002a41648100000d1116210141e17200c1e4588045003000c0b1056116100e08924003500c01c0240c2d100354803200c50030241601160803405581d8040d56455085440f58401c0004158083d5074400310030304200314140c803d0611604d249404401401665290401012002e0240c6000c80780040e04c298009030064024940404000300c1840c00c000100003181814003007552000c0765800a810b0081011180c00d24915580403600c001c0d520a0091040040c2818086400303813110700c0c500c9420700754800412510b4424032454540340d40003002013a20802030400e0041501c00a08001800c940034100d40c40d0329110854034070020a8a903000044003003860348000c0001c01180c00c11540035082c40184000705a0003e16450380a4006803074040d40e40500c0c00281c6400c03200300308503401c0703042c136a40e10f400c1c480340350706c030407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 523866007 1250 523864757 523864799
    0x91506060e040f0b090a0b03071d0103050613030c15021b0718180b0606090303071a010b041401030c0201020c150612010b01020715090302040911150418090602090a 72
    0x20150445040502e0b0544030514036181d08003100d440060000001c541040090f0342c00642520ba8190315400b0051111090301011040cad140c0c060010810044100101580503052035110300750040d003030760000c003050200e86015000411035110301c5001080ca038100c0381c8002070300c80490040001c1e0340105072203030071912541d100001f2840f41510034542038040c42c002c4024010100032107201e0f41c1d4030002250303c0601601d4210005000080d50b94804100521010340034480d10000042d098441c20000d0b103058209840700f203030600040025000070445100d110100342400304142c2c2d082c2c40124024003912071018558482c261030050300c0500c82c03c2090190300140c2d10111604070518900342078415003d0a14016441a0b10070003000307640c55403554503034a00d8036010500985c0d0b17030009820f41d512420191000c60f5a00140901e5140441d8800100304070007049504243c60021510300b110b004818900100341c6500030b6404015403030b812909191301c01042101c3c0940c98090442c0c6419443c2d043d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 523867257 1250 523866007 523866011
    0x1e0412050115050d031d121005160906110c0301060605090102010617070e04061103150103050f0f01060c02030109120801050111010b0915040902030f0c0102010b090415091506060e04 80
    0x1484055800386100c0140d403005000f8061400310b45d5821550321401c4140312440080e210b402038226030705c0182001c1c0020081000300381c0340c000d04200e002101d4002e005851131428001c0c040c502140c124140c003044a0003428003108130403441184030304003141714010650551a183c800301d00e079a00100a40381588080c0d00800c1420f4a4200c0f19811843c40c401e05142c903400072070108540c01d41f1444150744244100d2020980d103940c440110170f90341058810a14000800441d02aa9603048c4205944001e0180c43c01d803250a100361842040c00381809500200410304101c4401d54a00f5040100c01991080b40da4281c4208108000e00c005000e00a160010361b5070800c102031103070140525045060010080700103601c880d40329a00d04030030f2804298115448088160141ea428806030220030f901030090801d4000200009085510f101900ca20804402c4c0501c03001c642d2244110881c030212400000d41020242444040c14004801900720b007403c06102140d00ca03407152620800c0788050390700b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 523868507 1250 523867257 523867271
    0x3060e010b03040b0705130b0304030e01180b180303040e04030f050415051b060f04060605150f09060403120507060518061605160b100b0313081e04120501 68
    0x204610644080c4628004140d090000c580403c0d404400c00e500f00c209401d0080c5015007102038520b00c00341542c081c1ea1018404030802c818035401c80c003410f407440c5003460402e1f42d0044003503030040000c8450140c6816644d02052036191a940e1501c02070800400030210391316965540c2c0c60124682040394210001100700903102d203260301500546043d12800c010440281091038011106a003210803003641d0004080c0381141001001e00c4000c2c00380d0003111500d1300307924050605c40d05a52842d8031140c041c000c1a005907104101003025503100349040d03404940d0f0b950310200051114001d0380c00161403441088410300505811800404a40c0d00c074000501581e95003500000c180c090f40e00164160390415030000744003074008695082c0420590038000c1c1092000f4410300c0b50607604d0401201d01c28032810500c01d805000c150884010941c080c40240f5603d0401103e1540e400041c0c0c004042e42c0012408001e54004550700c1e107803994101843c00c3d1900d40e00d541d2208a048048003d540310b501c0e21131 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 523869757 1250 523868507 523868519
    0x141006170402031e010914031201120201050d0608031b1908160c120302010e030a090302060d0905070807030309050f01020d0503040c0509150f01140a050c0304082b0201020a090b07020f030a0302010c0306 89
    0x61710404039000e07049d15001e03031800d003c810461403414403ca0402804105000c0b1890380c0d031103050050202d550086440e2804201000d0302c1403502802506c0a502190401b10360080c54000b0131611640b00c0c189584624820b19114004625920010a0208540c0c0007103a1200c0c03443e1880b582c40c0c000d500a1045204078021140c9034820850f0360000581c42803401e001605050008002e50303c076400f000540300989440b042c2c00c001d482d40114102d81c103c24000c0040c180d1004403a4090075080307848940c0c8507102d0300082d607240c40703000301135003840004400242804110780c2e4402c000d00c2c024250320000e24010141e80480300010640c1441a1050b44500b08994800e01800104903000c41e03100e458260031180030b076819040b2801131205403004000102d035180b801d00c1a01050044120359545807034002c072402148110306c90700fa81c00c42e0f105121008072158061424800c80d42000a580d0351b400181c0080340205034038441c1c6503010320410210000b016030540c480048010b0541d000c000840e10b0701 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 523871007 1250 523869757 523869763
    0xf070f030f02010305040839030309030406080402030f030304050105010e0c070302060712091b091d0307020d030e031b030105010b09010210050a1806141006170402031e010914 77
    0x1000291080d001c201c00c240065010703500054019004582da1820020800c00c559050303440903007a1962080d80480504607444034120031746111107600041e50030351034a6044542c2e01d0042d13100780420049610040340c1591010b01103464806402c6054990f245030904045d4060842131180054082c4100c0014542c1c00c4403c06440205605a01414040e21441000c60780342c20400c00c4403820a03900d1072000002510b010500c07040c0800880c60062007031508452504860524209032054440c8111140d01605c01004442e269a4100c8a141c024655418101c90b4601940c00321900741c8510308a110f100c2402c00c111000d6008100c00a10107aa240c000c0303411309020380e262150140e0701c907002c04d4400030a140c101c0b5078000c100e1240040c1009404074111200d04990134191901d542e1000b0310090500025400b5901101c16046a60400d1a2030001000031510365603a404500d04200460110b43d0f0501c02c070684100d051035010150805041e84034001c103041a0200c0c1d00c040a90524405a8404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 523872257 1250 523871007 523871009
    0x120f1c0f0f0f031116020306090606030a1b030b090604060b0f030d1110020708030403090914181002040b09190b07021c02100c1208010f1a090d03020f070f 68
    0x2666071101c070007001000075218840e40d00301c800305068442076040d0400604002505c1004007001807072460b11814010700d81410b40c0902034034110380100c0200402c90f1400650011100d40c000301e40080035105421020750343d001900000c000094030418014256400141240964001d0100304100324459042051445d640b2240075050f0300b202c8088202030340a800e030300e0f10301211801074602801c04000e403c0101ea0222000703c9030414040148030605900c6803407000580050070042122280750042c0d08502d1b040200b85031640b050140d1000c000c10003c0c0480308420b1340004007552115100c500c0704507036811140505010303210444400511019110203d0308a814104040749810916028800047d105900d03203a50303490b4458403c1c0050316200241c61410f0050fa075030360030305026072034281e0030305c1000d0f0004002c11150303c2c0188040c00223003a20358211070f230384441542104089242040c41d0300031031862a500070700180d6100c0900d40c002c1011114a600042603594068a404150a0202e11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 523873507 1250 523872257 523872287
    0x130503061e0a150f15081e01050915121c050405150c0a0c031b1d0a18080d02070b0f10060e060405040509011a0103090201080a0902120f1c 61
    0x1d904086144003032076900c500001d0381048807080701680c550454042d50650340d80322210b5005200300540307141e544541680d0300407554122034a915500c1c911f5001e803400060040d0b070b110b6840ca002281200d401388410703001025028000c01c00190304042802d88805070404080c002011001028540c02d02c1242102e00f551001031032a0403c04010501d90403d4001c0252074606100e800c04c803e021485078801c41c00250b22a001180c080014881d050300307544030075482040c9460850204d040c075110b4800007240d02040c00100000e01349518142c1172141c1c85070301d4000d40014000910101d02c0d1141d83c000f000c0003401649080300d10344520402555400d821a40c007501000340b940140420341c03013400f0042075220000d00050425840d913001904841c4140c803081401d80d5075403d90181910400ca501c0503c00d400d090820804060b84c0020b080010010b1a811115988403035110440d40c0307400804d080140d101003107440102d01401c010796500391900b510f000705441d0106c00000035124001d90740754018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 523874757 1250 523873507 523873561
    0x90a0c0f02010e192a0810050402090411040204090c110c150d1a060408150c0a09050f04020706051f0b07080703110c03010216020414040c051002100213050306 70
    0x1207000c4500d0807200c450408480c03503404817803e445407058412025a0503800c0007000c1021030f02d0060007030f10301244141c3c3c40f04854200000c02026a5940840c00d5006400800f01c1c0b0602c051580094024421600004006444d01c810ba1024603406820150079003402d00850b24422040000c00071050580b0050524240c000c01c1105080c1c13040390050000c0403069120f40d10f20302000341c0040d4042d0055003084096901048640c071800d88842d04440d00504c0c5040c406241415902005002050f81e009180c01980358054002c42034403240e040ba604c0310703002001004641000007100800c001e0404000c074201320300e140c021500d54009021100c80c990700864651070300c241c42d84c0603903c1c04035440004019029070803805045032028002800b41d4a80000c4501100095104201c200c0d900c409070300720b072943c4403010080051045018030080e941c2c100c0c0c241d41c1c410519442240f40140340403424881e0307400070903032065110b02400c4200584104405483d860f9895040ba54400c20b01e08100f011912 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 523876007 1250 523874757 523874773
    0x50f01031205090a06052106030309220c0507050d08010b0913140106080a0e1c210e0a0312140426030c0a030e0a030903020103020901090302090a0c0f02010e 69
    0x1454075948544026031810018109503050002401030b44190f80898041880000c9180001c5500072a041021480d0001d598441c05c0050202e95a03015415802e405034000d440190041044007099410302079942c4018007103100700010080caa070300800d030704030b89910884900c992030901510f0154140d6030811512810105a1342c04c02caa0300000e840384c0e9030580c0d60346260301800d20498803206d020303051507141d904050618106143c1210b48c1000701000a8004445906902c80610420f0506403211b20300407800040d14a5600071016001d441d44640c54039180761402c408901280844445000361500b0440000b400000f10903520030701051200308000800150001d090b0003440c03620317001c41146500b00c0e0084100e1084842d442900c0d00d1140860203d081904554180691790110580c1e0300641010b640559015056810b2404000e040c9030300030402c288980d2062903c10b00030b540040c0410b0050030300c2000000240141042040002c103000050700015005009a10480017003100030403282c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 523877257 1250 523876007 523876013
    0x12051203070f210f0506010e03010603210302042105010c08010e24102313060e03160b0c010f0605031f2a0e01080c0f130806010b04090b04050f0103 65
    0x20182107819221108141c0f18004203094003845510800745500000240c00c0c140713440050112002460414030980c10407000f0b100040030000c0710110300b04222007280218400c010103501900a9800412426035900d0307003078070b0300c20841c2c1c120b88130140148000c2144911011040768082024003501088500303500c04220121024400301114880301004000040034600001d06c00500e50826900000c0703546a4251504420001a80c82d4031b0b00c14007540e1804442c22915090320f07890b40300750b00501210409640c00d40e1000c0c410007071036408060540520756100e010500c8940c0001c010345816600e044c9580300c0b0020107104007016194010000c14414466a540d240641940e5002409083c0c4820424030b140e801c00180e885003085039990301098046150000b0106071480550504210b050800d0010702498001141d9490100c50b20150f503c10102d044040b40952640c030242083c0f00d07210002614840703a00c080d10940d21203510500291965a040206858003510388a0009040034010400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 523878507 1250 523877257 523877267
    0x7090512070e070c0b01080316021309150501080d0c02032505060318060c090108040b090f07030b01090605030f03030a0b1903060c080f160f03060f12051203070f 71
    0x140080308100d408103500d03400e9001d0b800300c0941e503c001103a07940c0b01240401400e0004c80c1d001d0301a00c0010740c1820b040d03095030000c1c00c1c9050341c007a024003035000900c0c5110b0110b8112903607454001d03c180b10340480703032800d4100910092003601400d00882c8084142c00c1e104007543d03200c2c00d40003801070013245940c060004800076060210310842080950000701c9889074806103107d6440c0185a188407003d840200d4241030000f045c0801a800400c184400d50303030840c00e90b9030440d400800000183d91024481464840d8400b03449400348a001d200008100c110762115060ba82100030611641c4d41d600f0a040d070f241c2104001c0032081d0010310000d5100440b83d80300c1c52650b0b00081c0383c4203103401341c52480080300015810a80740181c0f60042d10140d15046501c0980040c40503c0c1c0b40800c3c42c04404170100e6849180013002000188002600540d10940041020b00242d41e0b82c2c1e420107986011503840f5045100d4100d915014149100c4501e041c00e1003034034411510354441c022188003a42c82195 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 523879757 1250 523878507 523878529
    0x308060108090309090c09031c0c0b040204090f110a08070506040e0a06030c030623090c0d03050c010c0206090f07031e0524180606060a03020d140c0706050f070905 72
    0x160b544014407850a560351a2010640641c0d0452140790b91a1050410702d405c003d054881904894a441c030800400d5620041c442d030403e40100d4001e80300d032034910020f405820000805416103102082e0030381440030451035041c86902c201c032903034005696401e4464840a40d03200c2c15034007940511081140388032034500756034071100304880001e00c0740d180d90f41c0780c0728082c0b9a00103941c8aa5034058a6015009040101013500304010500040740340c48140c02ea0303105820300c500c5001d103220f600c041007014024419200940d21410080c01080c0300d62500075600c4800310707900e50b001c0c4595810014222004505181580d821024401050166144400391940c50050844092107500480f5041c001c055400d00000741c04034100340c04070b0400c24402c1403c43c58214804585801030020b002c059595281203802e000407a0a001d61203200766203511000b06203010b2803d58510039a0208506c0d0000320000f81032452181303600700155101d001c104942148100c80000c00700b403904809001d14076100883c41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 523881007 1250 523879757 523879771
    0xb1005030402120d050a09211e0818030709090b1b0d061d091b1e0306250c0f080705010228030b031506010509150c1501050103090308060108 62
    0x102501c0c940500403850507404c07035080340016001003103250301c6c2503021610388020328034084515481305088400e5402d02c258076030001c0c8001072404140010003c00700b45c41e03d8458011031b5054580708086030030303500c081e404641244207018241c00484e01c030078140f142558450f04101400080d0b620020b081904081d401c000341c21214003480072000103083c0340a40c48c040c000707450000c030f0360081c40c2c82d80c080130810241050100d50803183d103810103415841d110303000030030007202c184001407860581518010300407808203805004503000c0002060807180f460752400a040801c01c0c9403040d00f03a0488404950b10f100800c08401c1c600202c01103407030075010f003165600810005140100141a02d100c0030140c2005030340042100f8072034005c040c1c240c0314005101c4410303005010440407a000707100c101c10004168505004000c51120350035144d50280010302c410b004240e40c0d841240d481c03d1680d07a0348202055031450704180001c92503500c2070003064000765141e10f51440986640f0015240740304010710f0a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 523882257 1250 523881007 523881019
    0x9160311010f02032701050d2f16080f07051c08070804050a23030307030c0206010b1201260a050109060615051206191202090f090607050901050405040504081c0b1005030402 76
    0x2500840645115038010312440c482d0007141c00b50410071202c10415210762782d1f00804021f002d8280c0d01200d444000c15440e52110940c1d54440590300301607120f011350340b0b010f85544a035400191001c602003214031410460f680391007900d40d0380c54a044907100c0d42207500910641100c1d100d6800103105089110442018600c401d0801c6241100d161039500b045650000090300c81c40032030b0200760140115030251425000041c50005940700720142480103200301c81d5200c4c00e0340c4e0b588104003145801c40f4018104501650b10004007410300602038a40d001040e120a89410740c000391100040c50034100040c2151292402d101080c1d00c1d01c11005002410a81c003c801c02903600c80c0e91020340800c00142c144610110200c0b02a80180a810a001028060020107c1d8140103000000241e03da5102c1024030389143d85043e04401200d440c003d60380a25001801c10041c481006110405084003013007041e45c0f44030544d06002900107031000710b505141c102c50110515403003e84036000541d0b02500242207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 523883507 1250 523882257 523882267
    0x5100f1b110a1a0420060909060604030f031d040902010801030803040c09060f1a040e0c2808161d040b0a0515250206030f09160311010f0203270105 65
    0x60101c00200c4210184030702d58407070f00708010000c113000031903404c2640c410b0719400304140c0e00202e843c42c80b0300c40c00341c0c2c42501218001010b035500c80d000c0305d025541c41540380080000c82c4ca800b90100d0703c041081210506c44c050700a0807810548203403000d040e0142d4501500b40d203541c5030b0341d00d181e0001d40241c0c0e000d49108030101c5d45100e2030081c1001402c03d034800031485450401c082040d40301715155040c0300201040100120031a0350020381d00300340900002c1eaa100c15043c0c81104c41c0584820103034a401d06080a2840990050005032055252100744619011080c4003220710484c0c02c40401d411000c01181101c0908196102c2c140880014013000343c0e0b2500c03040003e05080584008000e02000012800108081903051841c4081d0b030624050721541d29a0002ea40d40c0001081c41035002c0da8540010424503007048658000310b01420440d04058903410000703070251801400324040f800001c00e64071518400011240c003c00d0f03c0b0b50b80781d010fa150407a54210b507143c031601c0c1810040d041c02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 523884757 1250 523883507 523883513
    0x40b04060b03060102120f31030f0b0117061902070605010f14030304060c060504111c0308100812180307090501080115030305032e0305100f1b110a 65
    0xc1680c01508052441d9501c0b45010741c0024a0311398000c00000d488902840fa4a891240e0350b400c0d94004010104542103035055400c0010681d0a201c213044002c0c020100000244404034204242041c06410988001d81e2070b44600401149564490711640d0302a900003070400d01c4c1c100e01100e80d401c6070080540b40c0f82090701c3d40000d6a80c2a00f00c0083c10301881030070041c0044000704009000026006181060f2900d80302421082c400030020300195162400141013010620214030a400300602e1207001c100b481410340040d050700d00e0100c003c5001140271039a85c07083d14446200f2104202d004005072101c998020541c0d4110000d20304451151070552003142e64248050005842c10200000c0c20b903150a00e86820740f900b0f0540709200514900c02440402e50003000c0b69400f42d0540c0d8000c0311a2140441a204002966200780c0e40410542c0c000c01088400b1580d035000d9488000c0502c98040340c0001e04c000c440a4204009a40c40f6035805148070a001d00340244070341701048291800071006031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 523886007 1250 523884757 523884761
    0x70f02030c011401050a050307050102100504080d1109010e0603060d0f05241501030b0d0609020d0803090f060f060a2304060b04090e0111180a081b0a0e04030f050306040b04 76
    0xe03040f0005405100c00500090901e41880002070408400070840b0a140c000041d4941c0c4201200d07404042d21140001c09201d00c10b0f044404001401310100462000091180314542012280500188a0003640c4800d4940782043e24040c040081510227445115036070001d070203c4031203003198940607464540340c00b05200c4c0035020b01c031481046284020b1030100280c045048156180c54141440c020030f0030f40e180c403820b118030360b640c0c0d0240000440d41d200d800011640e12030400018400d4100004110400c0c10206007118102200012288941c507905402090000c0843743c60b50042205c00040240511f00901c9030386c0d19540006002c030f02820900405c00b41ea196400040d011b0100260402030400c0034841d00080c02e202000030002c2800030307010300015100760080f8003c889140046002c1c240d940944440003007103008111810400741d2a081c40c0031a9401d05118802c0e6050703903000a04200d2018540d02c19039042c0c4c0c2e55000700c0c0d0040c0c0203a94a0700060002a006030b80c4554009041d1030714 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 523887257 1250 523886007 523886021
    0x905010506011202041d060d3c0b0604090309152606010207051009230a1a07030f1422050a080712080f0706020309070603020c06070f02030c01 63
    0x1500041024501800054483c1041c2584800a20320403c0200280310b042440e50384441200c989000c07040c0c481c05c00081001c601500007a01d281c02c001808050490b000140c0c00320f00b135030001403004a80500340851341c100d207103a501500d1341ca00200028580c1c0703415408508241d20078105404001d071070f0382122004010300201d80d00441c03603980c9121110f1000180070040c3c510140c1d80d4041924100c40000e4448816100c1c103801004d04191102a090250389800040d0094000314400304012408030b103c607004c2d506410380203011b032030404038201a4600100e4800503080f03844c0d5140248070f6408480440300b051038802040300f055040e020b1900e1a00023048a00e07511031030952040c20040c020307a648800d41c0d001a00c6800e411400300080b00011401900301d41240c5045c441110303250522240c0351240300028111600001411800c12a0a9001d58040c0202c001112002c0303455400580481c0b040780c100102540c0b086001480003403060106800745100341c4140c90808a241d0215400e582035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 523888507 1250 523887257 523887263
    0x140303040f030e1c02120f011a1201050108120c0309100c030201051f030602031b030711060105030111030c03040309090c0f020f06070f050a18090609050a060b0409180609 75
    0x4540e40340380c01c2c5070f030044003606415401c40b594486919401d407a00015141010000d014400030060800d0001b42480402d8031003002c10020b00c82d480c09103003024620801c1101c072501c02d030801d00c0d41c101d58110501c00d4034103861041c4010070b4007200100341224507400a4200d081d42d88800c018098941c0c503009038107003440525881c0d0090131107075440c010f407c2d1400186150111504050400c1204000603103020807240c00c02c0700140c0c0d98032500b0f00d07030300015094885145c00e40341c0007042c008001e50200e005004001c0c41c00503259581d8a590426081c1c909035071480c110341d1000e0000c1407000941d0001150024401c1c20802e00302130351002407a00740c5141c014060049154080a0384c80c00e80c043c044085854413030f802409641c0741074a0b0103082461042843e60810c00d011401034417060184000344107540400c51522002540d88400c080980064002c0d0044c8905010114020728400c6c0692029150b5074400031b8285800c012081005012454411051018441302500424a60f104510b5041c0c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 523889757 1250 523888507 523888523
    0x42117030712050f06010309110405090a02130b09060f060705060c25121b0b10061b0c0e060a1a030f0106080f0109151502010c08060f03030f0714030304 67
    0x741800340a008035020b42250048a0f04040802440c000300c00701d040ea201500742000210700c1100d043c02e0540004130400e071600507150000b07000542c0c00010700b401500740700715508241420315641a07001d0b910341c2510641c0101003000072036070501c0c00742115918000c0240225040241030b03141c051030143d041d02d103900011400940844944100e5550103102011884c40945805a40d6104140007651003c40001c00a124a520003d00990b035044510035810140c02c14140c01d0501d480000064140b040c0c0002c41c401882811030049050f0050700c40c2174101d50700406132860b110340c180f8510030040c0403aa011882e502c021405000721292101d241c8045030700c1c0c64980c034288904820a400607082407081c00b8240c0104100002c1101125040d1070382660040341d24850056266401c001d540c0104101d10f14a8100001d82030707055102d900c00d000a80d0b9040500d0300c0d99000e110b800314900001c950140c20400c0303109903070a40780004000e00f900c60b002806008103000c0c074590940e0810b8504071400ca07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 523891007 1250 523889757 523889761
    0xf0b0c120f01031e0507030605040c0308040602011a0103060b090111010f18020a09050c1603121103040506071b080c0a06020703020303010807060521070c021309031404080304211703 80
    0x4a82c59541310104501e140e4240c4100079503807503040d52900300b4400101011b446100040410140d0000c502c015503004502c60346668031840c0c060b01801100d060025241040e142c6205258481e02034501140c00c4049002d162010b000011181220817010789a201c1d1b4807411036440c01012841607002c2c5044d00081c1c1034500302184100300f4290702c582d00c647c882901b0001408500d40d407034000c071910824010385070b5052184038642942e07000d14142c803c0841500d009120707001c0f07400e41ca00541c8034038030a40a84800c0e0b034401c8015143c1c0c80519600d2110340d405084030310002031000c0020542885800300b114843c0f0040c5d41c0c0d84050b40d010350421801a0804001040032a904100e9400609000e0034401d05140b025a40a00c00c0c882310200403c28440d05404940441e008983c032001140d005000c60700b0301e0350007500c03000160010305000c80006a2081c0804220404c00d07003500e00b65003050002c0c5181900e0729660361400c4074000c80044c00d440c103444071540020528119000c46d9044048060744034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 523892257 1250 523891007 523891013
    0x30e0d020a140c030618010b092401020f0303071b1205190c020102030909043905030316020d080f0a0306051c11060a05070204092d0f0b0c120f0103 65
    0x88030000c1482c6030b059101d500108040d03503010070581c2c0d005611210000c1000318401959025000030702140c0d0300007111000f8040d806580341c290103000da0201103040c40400c0200c00480e0f803160340c2550380e0000e410074400714218512626003407484101d5000b5250000020362240b0041211806044011030030000301201a59004801c0c26841c21203420700340075009403a00007075102d10920180c284a001c0760b03000a0108000d44101e81e40c191a14100c2c046030907a522010388a090b0344d006983d0203081a02e00010302880d0010072150580200e004060010030513501348041009072a03c1211608814003505d510700010740080c1504400341c0c0e40100b1074074580700501421f004076035094506040c0211700b1501050002e40f00f414815000d4400b1503540d6111101254a4055000c3c020b51213801c10994405001d030200300b200c9884020801e00083c1c021440c26a404001502c400a10f00701003107501c003000c1000c1560741a4080c403841c100790f10304000d40a01c041c0e005403c6501d00410030282d0014414 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 523893507 1250 523892257 523892273
    0x20d0207051e10090311060403030f06080a02130c0306050303030c04051009030506070e0105210a050c031003080d02131d01050901081906090204090c03140a02090403030c030e0d020a 80
    0x81007804003440112001450283d4881c10044400c085070380e00ea4940350f007007510071610f99400c845244141e801d107040c42d16005014000d100150390300c2030b080220109811070081890942650b00500c11004041050328480140004031040018580c0d1984001180d40341030000390f2140e1138042c001c0340c0d503504100401000c9440e8004c44000c01c0310401c41800021000103510f0781002c01030500320410320800004035414824130050720320481292420074051000035030560700581c00140c090040d0341d40c0c50100b2040d80001c82e03985c00082c0d031010081000c100c03400020a800d6130024000741ca04500046407042c0048950700803000f44c0301210080c00e2084000260902410044488003003e5241c000b034569211941c109030b451310307441581e000040007481e910458010390701800603c15040c0a082c13100005c0002d1005664a03003d00710035140200012030306c8041e80740e004080401c80c0d15503850031801020340c5496030061503524103240d00028410412904940c0c3e45500600c0a07003c00d1800040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 523894757 1250 523893507 523893523
    0xc110a0b0406091802120f060a051017060f010c030c170403080405040b01020d0509194e12030902040515031005060307060507051e0c0103060b070b0c1804020d020705 73
    0x20005105001e1b003000304c072590700a2a01300d51809681441c649a07400010000011540b1407944130800e4003181ca4029003080c0810184041248120019951501481010301401d102c10b400107503058241c1c40040c1c000c6101c4100d0070300401166403500083c43e2907a10035405900181c0f00c204011034200064a420300841441c84002c1c030107090f2595900001070094054100c01610400111100d084114041c0c002c40000b0b02c80350042210103804c0c9401c2d8071071013000100e80354a01904c04d008003007541c0310380b201e079400c440d040a444410b501c0ca0703240c1749030509d06a02003008140d2100a02c50259941d405024080e41d0b48038412100070843c90209481c110181c005031205d03a0614080003c66a00805c1d400c048407840c2c01c00d07540d0742c0850301e40103045c0358800e030001640052a00c5520300061000444c0d8442d1542a20b0030030945449a80d0554540600b540041051040300005204c450400014098132240ca0600d011070095008c001800c2e07820445646001d598040340003020f200d82005581 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 523896007 1250 523894757 523894799
    0x60818060703152309070c06050c0726030f0604110a030e0105060103090b0613020f0d06032f120f0a0b060415030b0106110c0409080304031e0c110a0b040609 69
    0x420f0007803160500d1204c0744035528900e0b2143c401140040d145500980449141c00e80c4240c0070892407a144021542d00d82100000751502c5d0300d602020498001045100e4200e02c40b07280d091415503a9591072222800700003070240360829128018032440c901c2007006030040c00c2407901c0c003242c0340e20646441421600011b01c41810182008070141c045000e20714031a800103400d03035540028a81103c0c00c10f01a1060200389411868001001803500c1c083d0361003003050320703c20040d10a03c064841c0b440d00d40d81080103045050701c500300072003003464a464031401000c142c2b0082602d20604d4249500c2e03003400601a0180c42d101444000c1101b031303141520484503100700c0b40054142160035502c0740062104140598400e000c1c1052020781140c00401001540810082c01400896602c0c903219603290015038080740498092141400344400018484a01c0038055440424403171030342d200d2b01040030300e000c407541e00441c03c41e0011801c00503d03401000540f10319114500c40501c0c00c0140511180750b850f0031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 523897257 1250 523896007 523896029
    0x408010c03150b041707030b041505090a0206040e0612011a03010f11160c0302090c2a0607140705010f09020a0605070203072c0f070e01080402030706081806070315 72
    0xc0c800d10800700291340680c1e128031100201c02c1200d8070b282c0d01d0032400c2d0b00060802200301c1c08000400c0b2003c48400001c1c0d054000070b008580f02e6114880c2c0d24800900025030189090000307100c1e03d00040d80460b03010900910044604524080032401c45034410700d800c44800c40000d401c0100c0c10f09000b48044818103d008000344004c0304030b0f02000d401403450340320201c900d610040382882202c40c841c001840d0010700781c400904120000061070352010142403050345802c5c401d41205c01c0700a0784201c503070080501030f000030344d08d4a100300d54000d41d800c03071154190818010000400c07002d20440d01c6442c24604005844d50071401000443d1070b084e401300c010410100b00341e40043e2000314806c2c0c115400716914101d02151451085202c03c0030380f103074644140f5500104240c04540c05110390192031141c60341e0031500d04103001182c104100700e4010390141e1002408101c241d1140007650380c40032082d20034020701001014000d00b400070a80700e03100040c0d01c0e5040060a00e103c00c403400c0043c1462001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 523898507 1250 523897257 523897259
    0x20723060403080a0513060203030f062409060c01090b01140d05070909020607020910030c0803041d0601020a201e0108040311100903080f0a180816080408010c0315 72
    0x340c00d44142c0c04010083c28003c036440348064052829251242c1e00c04500c0080d00342c03550b1000b5502d030021a420b140c0001084041040c40c202802207030208200f8015000d0001d10714019041550b1000c05100c0d0461010410701c0e400e40420f1140e000024828a0128515491714444547c050300b031882039440342e68403203403480005100003448002c072040742102244280560002038900e0041810103900001c0c45420000019114030075101543e00c60410a260b058813150140c0e0349001d07034085e000b189000395801d007000c140100d00c02a48902e0501c122011b240d0719a80382400305800511507000c0602001000c803642c41c00700b00d031700c4498500e0541e80a01c100c030000000c00320b41d0701520141c01d001036869030340643f22060080706141168450180017504076031400a0030001d00301c4031b08480c2000800800e100d90154041c03000c8070390956214030304030030f040e488482d21940203603490000c0b40701c3ca000200001f1100d80c068002170014200001e0380301d0580e40003805654414400c07030104201d07624 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 523899757 1250 523898507 523898509
    0x80c090a1104050904080a12020f2a0102040303020319052b060b0a0c02031209010203030103140307050105042102060c04060f230703090608060a090207030c0210020723 74
    0x2558050100315000c40c0c440c840c0200d22225200ea80c00c90358120b8003183c10403052182d440b00501208003285c2c2d4103144d502c5000c003c80200d0040c0d0401c2c040c41d00007000251a40381c3c2c058000e0943c02ca081c81d4041d94954003d910500b20780c002c0d03004902503000420101c0c6026103101038002500d00d43d0400342d1070590107402801e00f4813103009062840f0102c0b60708031076580c145030b8850740180800070314969450520560150000c19041e0b0100d01c6032041d14800c480c1d01c2c8214060324480070040e0015429a42141d460301401b000e0026102c03101d1100380200404203409000f11802580a45020320301014000280c0f0112407031160888195444030f02031002160740d500459044584e5031601c0a15030054040465030711107103100f1041b070300749140d95803250b81d01c03410000c003095842900d81910040d920203044da1940c604840c4240d220ba90348c4010403404055800600056110b480c20b80030301d403265800101108072000c60700005034002001440f0a0341d0401c00540c04484196407403140c030401c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 523901007 1250 523899757 523899769
    0x6050310090809060f0d0c11070909080301140312030103030e1509010e060d060f080f1c0801181103070e0a1d130f0f050d1404080a020111070f1707080c 67
    0xc10f4681c001c400004030344c0801c40030007040e01e9080480320000e00c418207000400401044070000d00d412203016000002540e1400b520461031003039440200309086070320303000030340001e40000d1a4958140c0a01d50807600d00d0780103030340118042e40c4a034580039004000314007484801280c01070401284c0008100583d41683c0180e41103c10420491b4410303541c5008805007006401e16a00168031b0700410a000320310b425000c01c034020091991070403180042c2910311a00a010720780c0603042c000c5581000103024903844085418102000303400b0220b00c0511620f50216558421149000018880f80c0c400c8200d1600954120091110980420000f070503184180010080031b810015401d10b54640754007001409007070f2800b05034000280380903112207810000d403211110700f0780800143c000b01c221101e1019090994098070905030046c0b1403003040380d005480180702e180c002c044511031002d00040700070040c0c0c007440180a0301c50810200c04040003810345480c855030012000c41e00541c3c0d2110460b1105 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 523902257 1250 523901007 523901017
    0x5010609080627070b0c0f19030f05190e030106060f02030f0c071511010f3e0d090b0a09170a031112010302090f010305060a1a03010e01060503100908 66
    0xa4030450141008211802d8441000800c400864010311a0004015107002c01401511b510304080da0b210f081d042076426151891030382420210958550100c01082c40b50358442039030340e80c0c0e00749146801e41d5000b50a10300c0c903180b0f80a0000841c4911055a54103080c001c21000b08202d040205249100c02c001030b44074020010180e04040d00880d0b85401c00404201c0301000b00080d0f14070b0300c8480300d80342d402400425055004001b0f582401103c44990399181320304150204a9201d80f803008000803001c1f00d0712480b0345010380b51842d050f41e070400b015070a2001001c0c1a88143c40008018400c0c0c40c0100803200002e12141c680e51a002105000c642402500702c0d0326001403018941e200c3c51603a040d00200940c1d002401355a1010a01c18644400038500794182da008070717010314140e6183c2160081000c400d010040c0280c02c19804669518000d41184608240b00c100304040c00910002181c2100c1c0081c10700b40c1140e441310400c0105003020b1000d000032a001034028000302c03400f03444982c03c9102d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 523903507 1250 523902257 523902271
    0x7050a0c03050d0c08040b090d050d050601050c061501110303100605070c08060a0920031b030109020603040b042109120f02130516110a0b0702070f0315050106090806 73
    0x300951042018822412a00c0325000010704004070140e043c4010f00e000012601110221000e8001c2404e0f0784002445402c401200d54420b8030f8030076013190701c070040c24001d804141401801e001c813000d01d0b241840a40d124041204c4460a601d121600041c5181e00c43c42944080790020000d20000040813142002a1885800c4c400d40c1c4103024500b0044111580d4032081c0640034450a0204581058200351581402851007032503081d070003065980140182114607602d5031041c484252480300340e0500d41c505070340003000019280596004110f66a104803403c550380107448003040100101d4000c03800c01c80a00073340010002c00340080140c13030086107005104002d08030301c0c42d13582000380101c1e09580d20769000d4005001c0c06000461600904416a59040300301c803131040029030b452059803020342007018903001780b0592000307803598284124080c1807030045014a0001203a8401c0c0410f00c0c1c001507100b618410340300a00c26820b00b003211010b81144040200c1000d00f040b003041c2c0020856000380d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 523904757 1250 523903507 523903517
    0x1051005040f06110706031a010c050c03070617130309030f1b260309060904200307350109052505120f010e04030c0303180b15010807050a 61
    0x89641000e58560056a001003003070b041e0108045120755015840031440c03014001114200c680310401607040e101c4d40007401004014504850425600c18400d01d040c8038041c1d82a140c1c00c0c0c28100c0440c1c242410f580041000c0390541d03a00d406917100d0b18080701d60141c50400d440162a110340e4005014603051302c006043c01540c1c994460034420340c80b144010849400b000c580c1c08a0365008c061904d5114040b400c0c50803c41c1044c8010a90004000c0713440c5a000200524600201c200401004050310181d42821480301c14600f9080c420020045010b43c1c1ca9440d101c0c4a9041200c0c01249003003861406000e00d410b130120802c6e58201c1c1e1282e1419141c4800b800716003030b40c0d50021640c2541c05844044c018004107652001540c0d041300060100c059001c032605c4030350b0741d00302c4004201c05003031140490700798407003000801292280311207201c82886840e0100341e000da10107001440c0e145a26007520785000c04818030000d0720401100c00b0108070203003400c04a42c5015140901107008818203002442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 523906007 1250 523904757 523904779
    0x2090102190c1d04060e0f06010b0f0702090705030f15010c1203150608090d0302070f0303020703050d2c060603070302090c090612150a03080307050a09091d100b090105 74
    0x92105030b48001d0302d00340c024030301040104914600440001c0da4140c0310145019803480d85002c02240b4070032500a0361b001080180d2030074000190b55441786200031940c034820f2000800603502c101c0154058030403569103e450f4204510600c2040300054250f201c07483c004507480c01c51340d8000e050300640e91f411582c20006036603100c4060b00600490203000c1c800610149001c10442d4000d035806001c1c2d05050111601c103064140150124441c12402400da0680c5403041c50000b0700c61f4004050741440703854224205101114184281c504103c60a4002d161100c18658605205680c4400300c804101c001c0a590801c88042602d0703001a0102901032646000010740d201000e0781245c4044101811156a407020080050700d605419260700310185044850740d2004d10740315040c0e80590742c00c008031a141d500d40d21001c0c1c1e810b80c40040400d00780308454900280b00003181c0f09a001040021000600a40d0f801c40d00301d0070b142e5500f4540b004207241808001098489024103410341d002903a901e0014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 523907257 1250 523906007 523906013
    0x1061202091314070e0a080c040e031b030a0212030105131a060a11070f050901090b01030f090f05070504020c030706021b030310030c0812160f0512120a0209010219 72
    0x20020001008040b1414401c1600f0b04840c4011034620403a1659211001e150103c41086555500b61090841950002d8007401c0540b5265116040407880300f01141d00d4007685201100000203101d01c0c2032400d40012614240064040c000d46d0070004400d4910340c40c640c1014001000c0d003078074621221b0000d64a008110854407119101ca0482100070079103500c54912010080550240305041412070243d044000b404000c98000c02c0180d0b0001400312404d6130900100d0002458440d003400d0425445231a110303841c2005100c0e010710030340100094030322100627041580c5410090f6200d075028510404c01d080140001100b41e80b00301f940f0041c0540d1b02c29409810380074140c1f0900450b4414013001042c44100c036621212002100d2103103032402106507490703101c16150102020010304402003009107201c800054149030300c4003481045506208441031300c52500e40300c185501001581000980d00318a4110a00e445038040d6a1580951802c0d030003500007519200d000c00c1101208101c00001030030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 523908507 1250 523907257 523907269
    0x106170c0c101a1c0f030f0e0d0c1d010b0a030e120325080c03060906190e1005040621170c030415031407050a0c14061006080106120209 60
    0x905950300083c8101ca40ea0030400364580c20300c003501441020342c00c100480540344042c208070500d41200c2c00008000141c0c4003510000340f500e09840400100305040046541e82c4c085daa4000c900a610041000d42000054681d800b00b209854560880541c0100300d1119150110f6800e8507031458003144c541040c90859182c204404821000000d0100420020101220710004500812000c0c0c0003a40e03029441a502044143d034060450311040000850504055603065001740f0080c020300303100440900f402c05404516084010214660740038030420b500c1d00c140f50700142104880400845180180840a82072203180f00c00e4041c0e05800c84506004100f02041031550000082e81d43e10400150865181e500c139010f9122860b0501c500e54001c2d40c828843c90ba000c0880c0034941840744c480c1132050740c4982006c10010100308203000920006144100c0c14a00494150300901040c1028120703a9008103580d0052020005108010020241d000060400c02080d50000581c0da02c0400d01181e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 523909757 1250 523908507 523908523
    0x1204031a25030c0927140c04050402070c0b031015020c01120b01110f010603020a09020301260115080a0b0c0a021b0d02090f1503030306100509030c0916080106170c0c 73
    0x5210b010000e45502500300000c1c61340140d0351039000c00c00c17000c1400f8041c0b500362a1b050f83e01c46855201407105000b2400c0075402045014040e207000803070a40c0c0c0d01c40b410510303401142c90054400e89a1000c014800e1504400c04821400f8000b41080652040008103403c0341d00d14004101c0391a1030f00d100300c0f42d005882110030305000078143e03015003801070a00f5010380301500c4120b024089440380000d40b9202e13442928181c0f40c00103070300748410001c120b0f0104d00400311300110300035541c0c03403101a942c082d4240048000707000d0360015103221f610b6030500b19402c1000401140c1305200801800c0d0400754081004002000410255840610b882002c03425511000d10000e40019410042c01080403805001a20921412803241c2c0c41518020506440c2d00040c2d80264101d88080c0440740c026000d480605240c100c00340484100c800000000741c20b09406035001c040e403036131011800d8400b56020541a01504040c14145048076100705094800c00d030007446842841c1001c02c0c2030191242c2801100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 523911007 1250 523909757 523909769
    0x100506012c1503040c050307140d03030b041a460312050d0507090e15040207060203070e100206010806180f3301050a03080306031204031a25030c09 65
    0x8920020b542c1110304554802d45041e2880c03018000000b0311447e00046c1c1d0b905880b5211480d14114501c4000c5c40716090400c50100e00741078031011031030780d243c4403845112410443c0b0000001088440c80500070b03100d400b041c040414142400220040302c1c07000b1034401d12406000007013401803030705000c078050f03807150350300004e00226040d0032000003241d00c0300140103610000403082003140c44100c002da80c018003911843d2054181c1da0000f0f00300e100a941c0054050401500262404442c0d82c0e46030300702d0307004403240808100c02d40700d0f41c036032070410390740c0316403180c900d400203000c40e50426084542c2d400703000301148048640030040d0360503500d0034046a03034540d039100c1c200c2d40242860b4843c1503043c0c2401c20b00b4085402a9000c10b0f040201d0005080d0403900d002d00200d0103241580c0300c04c500c6510080c03409805100740d00412003407003104030040000314002e42e10f0050001d01c583c40200c02c0d1070702a01221740d4011102c80c0200185048040c02201106409c00156a01e85080b00741c40766032888c2d0141d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 523912257 1250 523911007 523911019
    0xa03081209190809010e060702101202041701020703020d1403060904150c03090b1308030f04050102120406150e15010806033a090f1a0d091103100506012c 68
    0x44042000031030203081344003c01d032a0020005102000d000240c015140040e50141c1c03801c024104250180090a9100131802009441c0c5511040d500d010b107411040b0003441a980050f90764145507050011407036085903403501d0401c1941d242803401f590700019004902c82c01104020404000c41140102c02a40344141c0912070080140b0002c2c001341074101c01500d55041c0e100c0042c0000380fa201d40b034680d1030f5000c4801421a05da07117031400150140104121491740d403c0040080c02034003610f6582c030452141c0404a6101c2c080207072030500c00c12640c003888420882001340081c01c04842c130548024142807810201c80c1d82d51038002803600c0490420100c10451000c4507411729000700700000d001007050f2107400030000703074040100c82d17001c054400c070001c0c0410b800040c40007032507450209940c6c0c1c940d0b41425040908000e00300301143d031002400c0302d148000101d4150780f42403c0c81603c03900c000905040041c2d10b00320001030300d04480989589102100c40001d0710b4114180d00790590590340c05401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 523913507 1250 523912257 523912303
    0xc060f07171201090507080901020c030a03151a0309070f030305090103020702040f060b070209090d0f08040303151203021c1d04020f0d09150903020c040e1e010204050f0a03081209 79
    0x4413000900e4140c0781840080d25100014841e1001402240d5a0000010043d0301d000c0110004030014401d4041c6504142c07420000081c10007000c40016860100c0d0101695407420f04420030340c030344601e56020034044004d86c102000866048001c0d15504071017070030003507681c11861000600030300c629408c64500301c0ca005000310340c0c0522107016125041c425112103000703440c2e0f058000d84d941038016080002803851840107803000d00c9140b6403034200b8442d09012a0f80d45900c0100c103003400d55500210b07030384e04038100a01c05041e41000ba07580040d0b05c401000001c124800c9000f008a11201508010f180c00722110565a454a50450789108a004003181d1115840800034018280490040c0e4244403d4a0b05803055030303051203280022581500206410b10300c0605100140c900e0f5054940c10b4082c0d04105a1100550b09111501601c9000010b070341d58100410070103001c1401094074001d007403d800500009a8907030840b24180c85420b0300302d645642c3c07031051070b14014000400480354608009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 523914757 1250 523913507 523913519
    0x11040b0a031110030615050a0210020c060f24060c0a084323010c1205010b090d020d0807021005040f050f130504030e060406020f0c060f07171201 64
    0x1280a082c02d0b04880400c140b90200c0d07012002d54209024400402c000c555440e003c0300e00030402420400c02d54010b98003000b040c8840c91040b40c022001a0005030006820045610505c002c019401500d000194852225026402180c100c030143c4541c09a00005034409243c0f400304500b10400364071200c49039543c284c10002c9045481c501d09481342103940c0e4100c28038079429645a1500c0122140002c2c90980c0071074540d0015103419a0360341c0301251040060f5801c002c4203009442e9050400c3d1074074580c5520303015070882100c905034002d680701c48050140440c103641b036190a40034290121000b07a0744551508040800b03110b1080c0095121200e560085003240d00400a0011203a0300d00c3e0f1019800d0703446044c01096803051095a501c134120b622865100071280e40038903000f030300902e400201000030740c3c00f058540e03009400017001743e13000c01c00701c5250710b104118502d01c0d00b00a8803a1420101c41229850050103401002400c0049000518111020003420345154010711030b4070400c0c550f5549 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 523916007 1250 523914757 523914773
    0x209072304080c0411030f040807020a0b03241e0307090c08180706080c070501090804090b0a120203030418020903030706061e0e060d02010908060a1b0212040311040b0a03 75
    0x111900000f4064101003100c145080c0c840d0307980c0c002c8089041841d40c0d860803041c80c1c0c002c00081040701d2200c0c080c00a2030150300d5002008000d04100c402982da00e09081d480d5006424006080c100d10b460b0002602d6481c2d01d540c1e81e902c45038130121840280320035150b40064109011508a14502c500c4d0824086001360300101c1c550113007481a902c4803221080c00c00080e00d513490f13405564040b42426011a40b03030f80e042402001c80301d01490000460b810595900d03e025401a84800700301601c1c2c0341211400c0c07420101a0005260001a00c0039a401c250b020a46a020390301c071700c21100c0c441d555031003543d41c0103030110b0f4400c0750028242c95954401703141900060030b440c05000003419140b404100010080621b9105441d030141d01d941d1155205d07001c10454100443c030032410040d14480014800d4010410f0a028400012000c103080025081504820b603a883c2c0300421580400542c003c1c04261004032001e9a80000c02c2603102c000103c082005441480e964a40140101c170700041405950 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 523917257 1250 523916007 523916009
    0x3020705100c140406051b03070b0405010f0608150a05070c0c0b120a02090d02190518091614040207170c210403110f01020c0d06050106030c0c030c0209072304 70
    0x143d1203040e000401c00c0940a69400b4900413100454410441d00703c0c1c0050f5549100b0301d5180d90b80440e031074444d441d80c441008002c140d60484550b91280d14040c400c80b8640a01c0c0c02070a0108000d0030014051107032008520000747c614084150354201080381c0c2072150484101e110340001c4004050350b91482405900d911520700300d1004a9010041010144280200c0b08030b402c00034203407414281160200824920000c2c8500c40445441d1000162500d5130080d05040004104140b456031900340e10079820403188170301c0120b0784c184ea290148401104c8108515490708243c5006803500898a843c021550310781e800702001410101d040441003000040c009420384090102040180b106140300809005902000700080e0101500c0407040c1081d50300700004250510440b48000903030000f150321444181c1c41503e149480e1001030100d9500f50007826421010751401c444a140d0b903442c024080c128220340203205461040218003158887e481d00c40411500175174009260300c000c0004500c607401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 523918507 1250 523917257 523917281
    0x60b0c030307020c0105030106020a1101032403110402090105030a090602070c030b0709051c061e05040c03110a0e0a0b0a0510110106050306040c170106180b1e10050a0302070510 78
    0x6810b80d4013802d94454016281201c5458006120a0f0b240c0d03524070440e40350b0a84050304250382d9814040710101c0004003800c01c092200400c0c02c64600390706003900a12240c010150165004000c5100d182c1d92010032aa070029003510001030000a500e0030341c0180c031403603401400803c0d0100c17011091041c00c00c4594080c0075191030342c2201c0c070380e01c0c0248a0400e045007408001d02d0090050b61002c90070a4101030414400140c032511b944000d031540714112407060f50b054441c00b8500c00c0078802c222400403240d015080c01c5070a041c80c10300d00b1042c0e181034000104070780001c3e038503001c45085c45c2d00d42030940701c0038100040c00740c014103000040c01400b50000b061618219824100002400c0c107010074045c0c003603a04040c0c442c04840c10910444101d0204224a5640c0e40d80c8400008800040d9040c5c004a0a4a080c0208540740c10b0b00030411108a409030348580340c070b89415418001e50703801d0841161a41035081007501d460b4480001d0700207006004010700a8041c00490603120700f07141d0312202e440c0368 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 523919757 1250 523918507 523918513
    0x80a030506190b03070509011206030f0302060c0c0307020f0f0a03110f060f0702040b120d09060f0e130f0b06040b04080715080601030b0f0301020c0609071d1603060b0c03030702 78
    0x105480065054801d01d00c03e55030081d40410204400c0351040c001028850018100307000c5030640312a219080300c1865000790740c4610010203070800c05905200090b0070000381011941071217109240175882c0d2080050081c860070841d50150a2038580c40e0908110100040c061032101d80c0c1c2e8200b07072065034100d2054510402c000310040d20305240c1a03064400d0750306104022820629241d0030300c0000d1202003035850381b0900c485440c000100080104c91042956507a036040301500d8040091b10031204500e0702c2060016035404e1030165240c0d410881e4102521040c007040072090b880700341c0300030440b8030705050f000310700040d001c03c01443c0c2c04005d20860303620b0011541540d645840840c00794441e02102d00020b00c0710400b01d501984650880e0081c1c000041002c0181d110f8400080d0881e404008441c0e803603041102040b040e00000e008004c020083d203a455040c100d101e5a5034141000c1c003d002c45540b5621a0602601510039400080030b001032105195407840c0ca00c07034140d583e030070072607000700144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 523920863 1106 523919757 523919779
    0xa0207050a0c1502010f0605090703050403090b1803060a140f090316150509060105130509010e0706090312091a03090109020901090905060108070b09130603080a030506 74
    0x1019500343c0f2415055040c102900b036034007101400300303002c0c0380481c1002261200a84103502c00124130b400a0955513a28003990188801c2e041800031a0340800c0007480d00c21320300d8511511900480485903d5550603041c0c505482307590381c41c0050742ca80030001c29040400f142500780c0000c1c0503c01c1e681000c3c0e980c04d4080b0203c0714903100741d0740c400d040b4881ca08030140c0c03845843e400c4030101000c1c1c075166040c2004130707080e2140c6c507101440c015a502d002596540c0294428044522040309407141143c1d90040148203860b50302043d9140380b0760042011000380a224440200c41000c07020350008038070081c100c2001d03040200040c10301c1d502d451074100180d0303480210301d010b8050407200088001a60520b02d141c000140c0000865900c800010f003d2904610182c843e8001d0458070030099000c05040000580034641c4000e0a0781f401040b0200300d580c264024a105203804c0d6960b010030 = true := by decide +kernel

theorem cover : BRFrame.Cov 523741007 523920863 := by
  have h0 := BRFrame.cov_init 523741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 523741007 ≤ n) (h2 : n < 523920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
