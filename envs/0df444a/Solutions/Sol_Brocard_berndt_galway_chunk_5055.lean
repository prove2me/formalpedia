-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:35:55.044155+00:00
-- url     : https://prove2.me/submissions/53149fd7-7083-45fa-b976-a05298af39fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 908992805 ≤ n < 909172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 908994055 1250 908992805 908992811
    0x50f07020f1336080a0c241d030c0d0807120e0102070c230f1f02010e0d0e181f03140115120209181005090705060a120510090c03 57
    0x81d0001c54848030403d00003000d0503051026075071561184214401d00c611031080c0280e0000038400d01c20210152035a1040480c40d0307092241241520384020031041c81a0f004405500443d40d0b510100042590119094180100150a4003200a8070a03241c000d0000080044401221641d10b05500075030000c21194400540c507011586081c01c2001220b410007400f0141e1032848852000006000c00c000e00d00565065010000d0840800d421011030540300300d150401e041c4410003240d05510105140000105980c140d840b04101202d00b0340340201c0e02c5511000c101c8000c0d01da2100c0045464000440c4000c080c0002d00352060a400094117610948622583c0e4103025403d01c400e0040b1080d59400c81c001d15645420b00500d203480c0000241d001c0e000b000707050b001031842c100c44201d11055a49e80c6040381c0322a440244058082c0c0b2048515003024050700400062174106003003070b182d0007420380c0c880e1941001d00141101c000c0c4401810080098044500040d2842c4148905003000443d03607004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 908995305 1250 908994055 908994101
    0x6030204030210020c0d0b040f020907170603030c03070b0907030203070303080f0f1603050703110d0c0e031516050d0507170f15010e01020a02100206010312050f07020f13 75
    0x840ca40c001d01843c0940d0007080d06220540e4412201588259211030310f080342e038456041103070310085541c41c0250024284070038003401c0c3ea0400c49030400c6401e00d888080c865a940c00a0549078005c40001441030b41c018011440060702070310f1207607031142e9410200e5242c260740c0d8001910740b95560340b058001c01c0c68001401052480008802e51003441030b00380030401c0c280301015806824a81c51514100355540010882040c03203034000154a8075103840c000e480e03000c94407000c0d00031700c0754440300804502070301001052410040b41403002400b004144003881d82d40c41d580c80741000011400801005005c025801c901c4031148a024013030b004558803004407628030500690b8085020b4007100c1102c84180030000345142940c04104e41840a203040c40b42c401030500103078a42241144000d46c00000e050142d449150300043c6e540c120f80c0212603a003010361049009a84034030840c0e0f031110f8a408100044005406d00c01d0100c60000c07005000a6800c20420590404031504064106440d0000d2042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 908996555 1250 908995305 908995309
    0x30c030d080f13020d060b01120e070f0e0c0d110c01090c180e0a0602090a0302060409020921061302010c0b09011a010905210c030a0605040506070306152304060302040302 75
    0x12441e0f11905039021181030035031075000a5140307048080c0052100761200301168469110700060701c2c20704841c010500c801c0c2030042016458000500400c5a901800c090015a644816281c035000703074510f5890a03d00380034036120101801d8003107180c58036520200500240e1100034803420500c5809160819101130034080d4a0700c080c440020040703c0310341000a10800180041b481005007940501c0040c0d40303003c40000700c0c050ba034181d440a940030310b0105001807000040e400a209403801220341c081c1c4035080e0300f0035400140c0303400ca0114880d80302a0029454098080d41c0345000750050604646403105665100c1540740112118180b60b5101c00e00d003058040200d40107588510709082200c4200c3c1007001040390b1440d0a05d0356040005040c41b881030a500502000c0111080901a5946200300341000d802400741514100c0b19071040e4400110028424407500d0180c0701c4100b441c144501205800701c4060096010060240a405440d0f002016800d40204010040c0d901c4c09602e84c2e01d1801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 908997805 1250 908996555 908996581
    0x305180a050d0302150c1c0b01090f0306020712050301080d030207021302072105040b09060f041203050a0908060106080103020910050307080f010615020c1003021204060501091a100e030c030d08 85
    0x4680702c18261b0500000c49042481150118481da5603040010561054001224000a10b07032040c2e203034a02820001c818054030b80c00600140b40a6001611b12620242003101e00d40300900c00c1d501c950308522200340d9081d1182e00140300140c0010001d20700c50030703c545004102e0f4440d010031250300603c0301002401c0c0190004186916443e420452304103464594201d071280f0428030b40e1440341c41c000030382114540484041c0c0d005442d03207081c02090104107140280c581da008022600108081e003c0000d10100c000500e14181c4807980c2d02d004070340e480c40d804d00c460407101070140c1003105000000410151801c001107001491020b005211040b41085424210f40380da0f085003442c03d20803d5060300c800c0e000940e100f011101540c189070704411240048000707005d02c425140007407036018140410f02c07030f840d0842c60680c1d8400c00100140343e4222229150345100349007281d0000705019580490700e005100300380e040034000e401d0b0f80c5080400e40019080115400b045030104022400744416401111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 908999055 1250 908997805 908997811
    0x212061008040c090c0215090309010206090102040f260f0106090f2003060a0b0f090a091b11071d0f07110a08031503010c0306030201030b06070305180a050d030215 72
    0x1081c66062410b00c1e4541d050070420500a54610710385030341c94510251701c20000c55841812907500816a400c0c03420000d500c2e944030030450740c018454000070581c085018800c450450340c049445c00e00b058030380411900d1640700c004036405e00e100448510420f02c10280034500342d400d60000001201360600c42410202e51401400703011040c504004031040744108c582d00e15415085614460b100e946280000d25030720001d400c100007049002c9070b00d02c40d0313000c0e6001038042c400045901c0030b001601d40060b8001c548541c54090059071141d0b489044150098018025225180f003e0b620201e44800c5401140880e450800d04580000710821403012000f1149a030014020300d0080d240441c0c2e015400e40e10103089002a001080000c00f190643e00303460600120040017400911103500001005130080104c3c0c40103902007800c10b41407840c1c0e860130f001100d11455040d21540e043c100e1180010000000080c0c0d06500a00d180c400881d00360307102c10304000f07007e210750f0040c070502280708503503800c000b006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 909000305 1250 908999055 908999057
    0x309030d0f060b0c1f0e070b090f060403030c0209130305030f2a1308010e0706110102090409050d030c0e0d0f0602070b0103081b010c0c020f04140a060306061211011d0402120610 78
    0x1040c6003690050007c2030030012100310460031a2603800580c002607000083c110060f0740081c00040010415810926004009001300c500010340d41c2c98a40e0802d102100b150002c000880c03c1000070082820001041d401001d1906070b00c5058034004c05120b84816840003401051802040d41d508060342c0b056828050003050000340107000d60100c038a03540e1440d9016800500c445520ba5001c550001d5061300c0e00c00720010028444200d0900f8090784903c0b2051218000a0070800248145401484106482c0401034840c1c0e14540130380c1c03100c41c01c6060391242102c0c615002c104e00c80c04035940c40030040c061401104055903544040d50760140140c043e800c2c0540720f0741014a5001d4080e00001d54105c007580546000380144940000100107001c8001c0d20b010303440803a01400315a1503141d0080d401d8a01c01e80c0d04203c000d4445031141000c070f285150003841c00d045000380710b40c554072031407605450105005440c02001d202c4000202030f87c104484881c81c0101031020009035141103e0506c511540f2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 909001555 1250 909000305 909000311
    0x80f09030111160b191503020102011401060f0f0c060501060f180302130f150303050309010c090806011e210b130b150a0512010209030606060309030d0f060b0c1f 71
    0x1507110f524150202c040c0c02500020103d0001102d44410213042c0740840d0303d040c020088006151041e04012030076000582c010341c640074052180661206a02d81a40c5039038840d2102604018402c45400d00800940002c2042141c0100300261071030040318041c040b1a1141585003540130f0000b00200380d041844800f0810165007040940c0f140d1103084c2d480484c140021455144020540010705040c1d0400c240203809982e00000740f5a00c039003d103000700c03940d0300203119405c020041203c080e4000c0c0280c10031600050010000f652031510b0700c1d009240f094540f103042664a00286c00040d400e0100b081141039181445010405062410780d480550000003900007480381c1ca80391101c880040070311510000d2005610456a5520f03a4980241401004e183d070340d07220045c286010b904242c3c0024080e100312001b040702454000243c030f10030140c00000b542044018a0740c0c001911105911503180c039500c8030089107800c3e1080040500c00040c00c010100c81c0c01c02820040300456542c4244442c0746 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 909002805 1250 909001555 909001567
    0x1d0a03170c0909040c1e0e010f18051f08070503010f0606082403031803070605070210030c03180f0506060108061806040b060316020f0a03090303030c0c080f09030111 73
    0x41c6400c140c58108905450b958016a62132a0070313003415101e40c01110344950320b0002c0701450648020000c2c29680818410805640e88000060300c40b4424001c0345e881c5089440408070f903027002d41c0500d600c04040c1c400c41c0c43c1504d281e038038958404126000001c4c2c58003e40c1062209040900508050200340c6800b04449854510700602a03a030141418030313440105c0a43c0c115091083c031001c0aa10b80003020303240e450401e2861f4400c0744054a07540c0c0d00900031800c1c0058803070300440955102c2500540002c0c003e40f56444100c004040078805501490350701c500c00701e40c01d0684020164040e11030710101c04074001a082491900900a100c2e074104041c80e0300f0003849032105203030401e0601b80f045c80c0b030195446260000300a00948034480360080004002c010b00705100050040310b01b0f05035000d40703907048607030030100e91039014504001c0d0125040a10420020f44603038002846a201890401c81c00031031a0b954a0050b80001c1c1d00d401e4101c0003141107061460300384100c0041e07100d031010040c5480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 909004055 1250 909002805 909002821
    0x20708041517130203100213081002070201050f0d090b010e0402040f0902240c1603021309020f061606050403110705030a02030a030f05071403031608040b18011d0a0317 74
    0xc001e215a030a501043d0740454034100103100182030010425500c0f52000294649502c105210303086092203171f0440c090314082c0b60720032900c005806955940c41c00400047c43c01c081d03840181107200495590780104086401100118003900b21800707000194103081c0100f00680d0812886030f042a880c121154006075191450b1ba1641b000890504c0d1030010b250100300450f000705c0300342d45040c1c0110700311070340400d2042d6003001c152442190b10110003001114444100d51405000940101c01c0420400c05450168050088030700020301100716561569141c02c00c0e40c8081e1030807004103880b007220b40d0012006108280103004c080c0e005001a41c03154001075650030325018054140500a9074110070113124808844105412950000100d04541c03e4203640e944101c65407940e004001ca811102144a10400c90003140c1008000e9502d072a900c520485005040c130280c14659641e108802c600f04510b4030943c4110b08060107001c90054a04000d85010703589089001640c6200c2c041005c3c00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 909005305 1250 909004055 909004097
    0x3070302150d090c031a070507020613180e060a020c1207020a150503040506060405041208060303040504090c0f08152a030103120905121002070609060207080415 71
    0x49404641200d00c1100712801404a84200d619100d0150305100c026428000c1c0449503204480c41407489500c11080100310946141090b070b0140c000400820000016240110190010003007070190780c01c085995001070040d210340d505084260070340b01d41000380d0802d82840030030b038040350100c0f00b50704d4100b6000026841d03040b0044510603201000c03a07404299114517089030b02900a0340d01940b12040b40d82c01c060002c0c0c104a03130849280c424513001907e01c0c181806030b140180da1007551102c206070404401e42e85528010a00c0384c0506c41807000040039a16401403d139014000c64403400e100e400c04080180e40d040a0300f0020f1654060451558200b1846100d65404004210a140268000f4403002c07500300500c06c0740079000c100440080188054005003485a485c0303074492580440d6940140700003429080810101c41d04a01d50364416500e241c1c004001092003103000150030082070741d90030708170303006403200340e400540116003404448203540f00440101c100e4141050750551080001e804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 909006555 1250 909005305 909005309
    0x105060901050f310602010911090910020307030e0c040b06091306090203100501030b150a050d11070609030921020135090705011809230c0301061d0307 67
    0x104a000a01003983d001c00d0700a40e814455500c841ca1020108180e0000c0303000711845842001c40512072001a101d401403140044407a80b2520005400f61300302e08005080c607004100a40c14062006040b480741c5042c0700440c4110754540f000181660719103841032030040c0014010740030f146060740c038508c0c0da82c41340143c0c0c00340402102c1d452641c18500c80305002801490b803210840038000300500c1008840c0c0494401611003e990402075441018100044022000d42d02c00742d0310b0040040005040c45a001403a00c2c43c0c03000b60101b842640300038801c009a108050950303403559207010314010964006c1460004282c1c041070101c0e640d540450000c8107005010b0003d050103038160a1901000074070801c88602103182d0102d588400c5036179002038030070104840742d441500070321401060079801a03001004240b402d03903011900504009015004150a01d1800c00c218080c0308007001900a400403540b00741c0030340482a483e5450404d0180c203c4841c00e8044940940300400781041d500c0c00034501c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 909007805 1250 909006555 909006557
    0x60203060315090f2e021c0609091217041214120f100f06080a09020d2102011a1507020a0803090109050a14012003120f0c04030512090a09020d1506080105060901 71
    0xc0d862181800020340d009504c82200340c2c043c00e003000040c0885d02c65000007003041c0221141c655000002c0f000b140c1096464401e03c8cc0c0d030b807101c804540403404241c403104e3303c60814205040074080da8204414036400449840030032006000400041541040c80e05400507400a003040c885030030034a14240b0b45100f401388804101c0c912000079545c01650304545030042c1c020340080da528141d4101103c901c41900301c00d81da550039040c03000405500c1481400c0b202c1961401c4d59008883d0070301000b005d442050825411098140503440141e42c40c48aa440101b415500465464001030005000340120340e1166109200b125070030006441003280300a402542441c1c0300c0c201c00700082101d07849070710035038a6680e580700100e007980c501d034283c04010b802181100c603001303000d5440c0144400103101c0c1e4040100941c2240d110b03500310060000180000c4100140080085515242c02074100c2c2c0003841c0182881740c07078484030003019100c0e01010700074025500c2cac1703c1101e40c10000451564801c50510b14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 909009055 1250 909007805 909007807
    0x3031611121906050c0d091110020607170a0902030102031609080c01120c0903050717060a180f2d020f040e06060105090d08040803040303090906060903060203060315090f2e02 77
    0x22904c400030170442d201d60a4502e001c1200d440c450a066640203030640c00d0030b004d548041009100784d400000c104e4032a1000c2e03950110000c5850304110001e0170060700020300191074031002c00050b5802c1c00914440c0b030244804d05105000d042004210400c603512041030381d0000700980c0040d0340d0225041c10390084082d0007007095155010100c41c03c4d44103500162460042401c00310b41060460351070784044140300c048448680752001050100c45018080310200d2420141c07400004400116680c46135000d1a122070342d00a5004520113004101c1118950b07460804c51001c0c214030300a182225520b0040c2c0b030420004406401150b9900009418107040c40404200c5480355035501983c852629482a1a0303600c071641c4140b031707d50700e4105010490204148131004140c40c1d0082c45130a089070040d90700c0400e4640341d912900c000307600c05800d543d018010400589980d016a141060050a00c00300514061042c13448a50410203000201c00c00602503103000013919503000548a426000a0801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 909010305 1250 909009055 909009061
    0x13020f030408031512160f0b1b0a1a01030314030411210129030312010303030506010c0b090c011e0903080c071d0417071208060303161112190605 64
    0x80c443c2000b81103210f41d030100040701603a4000714081b542d44c0307039604038130540c040b55030b19900c0b1841d40584502990740c02c0081400403d00c401d580803910196549200c0580d0040400354840421720303c24003486141100254004104160303100d50782c9650804022a82400c41c10a40d503120f1005140c0e010300707481f90200082948443c00980a01007001c0c3d200340082000560701f20111003a4506140c0c00722400d9440d0031402e0907800c000c006c540c020714034111107d906078256a0141c0c01448050030050410905d4058000000c603c0c4a00c14080d4040100502e400c40c0d4030000104144144c480f030506160400c0380d408001504960b0140070350b0b5000c1d203a55101d1203010015031500540303074040004140c54a2460080305000d4901c1c0f070160b4011460544482814100c050446c41323416001070610b9100e080e2004520700c20720080381c02c05001000d0701c0c0b03401d080c20074a08000b59a28829107501c4501035011206240000320030112100c960003400e41381c400344120107108218560064442903c41c400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 909011555 1250 909010305 909010321
    0x40807021e06030a0c021002070308040b0f2707052d04062615040309180507080105011803151d1603080706230412080c0a0309030306030804060e13020f03040803 71
    0x707014003d28071104119241c030300f276080082404c03c0985060750b007010280081a01107001c550360301d02c50b15502c1c07100d40b80441c5c0c0300500c3d403030704601c0091174019000700302e00412540c3d0f40c3c0001c08800d0400115200f07440300d1a0b030b8000b142400b0800c10510861801c0010043c0f00140c1d007660031490401d11140f90b2004011011a062200205528074030141c0c940400c01010380158950080d20f6003580b1400160f1070b69070544084400907207198010804d0900100035541c854008504a460040b0500207030964aa444240c41c107041a0344460341e94664540014041400d81c1039010041e110000341910402a07446400218017400064a503400024980041c03080680125444850b0700308030407021058045622042541a202114003010301190255658410803505004001c0301c1c15207072a0000301807045d00207001c840c40c11018942c90b0400040800c400101900041c03880b070b142c001c5060f061008000d00125010401040548140305010701041401c041e01e0f8440d9028030340d0399803a283d042c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 909012805 1250 909011555 909011563
    0x30d1202041206050106110109031e021c03020307180e010312050c0d0207090f140f060d0615030c0e010b04060309150e1b030d08060423040807021e06030a0c02 70
    0x10140c50010b075031000908003c1a607002c0d0b41216040e580351701c0345454051405007031310700c9020082c0006450044614004c00c894141c0b502807642401100d4030160b180902104404441d001e00010030790110400000a4100d03949224007010346031503010050070420b07c0556a48107010151001e001d200404d900381c0e000e00e0855807103400000c21600007075170004000b907a4240754090044080e00701080e40460b048103004907004907a01c5032000344203542c0c181c0003a00303e240c02080c0b607a01880321f50340080410241e205843c0800c6a0070b070483c0c081411b609104004e0502c50340301c201c01e4030740c00c8010000d02080350240e409549481c44c0c007084903a4282880bc032510581e8400d01d424903e45a00c0f401c51900009802d82840718002d007029650800c40308058542c2070490a000119401800240e12490306500981c084140060030a4009203a200b850624540488007280c5245e1f000410342d0a525002072005c0b0203203d0004200e82c0e001d840c60121360180000750490783c031103403544030f45100180280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 909014055 1250 909012805 909012809
    0xa0c0e0702070518150105070b04030f050d0e011b0837050108030a030609020408071403010e1606080a060b070807030201320606090d080a0c0f03030501080f0c030d120204 75
    0x101210305092003a900d84d400c121050360011182400e5044200455000c0c0c8103071102c454000044a1595580b52416500324018000802c10030404002a0301ca8500b41e12803c404030401c0c01c000a0078105000c8004112140391800c03401b4001040100721664440410000982600c000c10582e11100011441d6030b0341c562149201c1000e04203400401d41110000151699148039035003409440d50341c0056104038400d80c001d62000341c00005082c800c4042c56220705804030000b400024041801c118164106911040c43e42040031040c03404000e110351281a44c1d400c000d10403010002c1c3c41c98210444402d21401c00020320080000c40c081c07003854000c0d4002c02d10001c5500b850b001485100d020340141922035815000b041c42120049001801c003041901c4240c100500030300480302d944d46903000071b908500c0040e0304000314a890b00000034501401005240e21945007c80c8550410122508250b111b103500c17000b40c1e100320f000240c0e070b0b41c001a00400b0900030b42400316003801c0f81d001c000c01903c529 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 909015305 1250 909014055 909014059
    0x1b030602041401120608030328020301032406060c03110a171908100b09120111090901060c0203060f070e060301180b030a081c2304050106080a0c0e07020705 69
    0x700d400600c184481030704400741c400990764554403018200380c2d101250b00e44c0c025a04290b006100203041c8844031a40114801c0c0446c121910b03424540311800141d074001d8000300c49441e0400665a6406030500c40d9210642c41417806002c960b01300240141080c0e18010040c04110398075404082c0e0600032b0001c04801030300500340500c030540008a1040c0d540c00500501e201170103800c010010188034904c0140903280c0301d001c1c1c008980c9000c0041d1803d03001502c2e16a4486e15a03251182c0d000000d100343c15a42c0e000d65403003526482140c08100b96030340164082010b11141c0ca008000603a4082100703540281c800760386004913202c00400b03e440d1018604140e401810000010564442070741183c01a14031000c0280610794510040c59115005100010040c0c0820b1250805880070199500d101c0e914400c000144c00110b14194040c9080d5880b802b0f6119100320144001e0110a00660016083e2a0010042102c40756102c5030118010310910a07111103120104110b0b500c01c1c0032246c010940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 909016555 1250 909015305 909015307
    0xe072303070207030c05100909020906132723150d0503070227010311030a06050c0304350c07051f0305060907050f07030c14030a020c040b0d1b030602 66
    0x3070065620800c0b03000503100304580725000109841c1089506000e6022540d54040c81c81c91310001c040a5002294941c0c1c5c0880203000a003a0140c220505038001c040c14508600484010b0315400d959120700795119005600f0242807030031540700845030000e10381a01c8980302c040e07618500410428008520005d5001840c1170045e0244800040941240350003103d03401c043c2e034800551107080c40c8034161f41710300b404503800c01000440c05010080400840142c140c52042d00203966078404ca035000c88001511140c003200740400e208141414201c003c40101c0700911101014443d505c911041c01c2d04444e0001001405121002d0141320075802401c01400400201c1040e0b2b00c1e0801c0442000d01d0700d00024076000c006036180c40e05401690045102d038480c40c0c5840000345000c225903100c1c0806a042c0311203071340c1c031100040c40c602c4200b454a49240166480d211000c1380241800c01c9079140d070740316905164052100ba0342b00300c000200346500000d00b100d402100a46608807041562029010f544 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 909017805 1250 909016555 909016561
    0x4090203010e010e0115030209010e0a0f02030f090f060903160c030503073504090e010e0f0f0d03020306130506030a080c01020d180f031206030c18150e072303 70
    0x201c1504804644d80b1520000d0180c0c070500c41c5550030503481c40c400a0b41c40700ba40c02c010003940c818184030301d8000d409640081030254111405034280d074825510900c1401343c00f003c1003001d0340240302c400d03004555003001d400310342011000d00b560390003050380142c04c02c0c00d402030703000410852030000801181e1040c03c1d2501d4000500341000003100c07035416070800c4000f02c07246001032101250403030400c80212402c00e00341030819100300010026807820768001c0d91b0300c420015010398100080e1001000c0718009003a13138891580c020b406c0100c8940c9010515005105104548d503901040d80000324094400082075915000040e02d4280c401d40090106000024403d40d1100190018900f004400d401032240c5000d500c001c449540ca5200041c00507402c940c10103000038400d400c140480354400e440070403000d03260b03219191408c00907840030700121150142c0482080c0705016140c1032000d0444003408561030108e0900d1440700041411342000f42d4265046840396440e02c0107603c0251a02c0c24589900d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 909019055 1250 909017805 909017831
    0x10e03010905070e060909060a050a14041113020c21071a040218060d260c01140a0504030207140102030f0c0c03010e1c110c09070215060319110409020301 68
    0x1082d603004540b0603e5441002170014204060040d0151041038002d140755030f5024421001810094440c844082e00d62040d01380304c508108500e40218041c4204004d94000e11007000301514071131001201ca580144141c400d90080482c3d0700e01c7e034540801c0302030091b40490f200d480b1103100e00c3c1d0004080082d211592030104019002041c8200d1003520000c0554032401c03060900791030f0458000d903000036201c00c9000013130486111401c400541c81c40300d101d1480481450762050300044981c2500f80e42d124072a2484088640540d0303048440350400f0001e904240d28003d4452680e40503060107402011020203680c0d20030402c5514a402c04541152030b104104079041d01ca040341c0c035aa610941c03d00c5180f940000e001b05c0c1c0c01c5080b8410146520103071074011400e40701c03504000541001405a4506018a0340f6060b030164855a2140c0c003a0042194600c1d842410b401c0141034075002e980400b812034204081141c0102016410a9901004440010015000e441400b0009416509140b03000343c1031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 909020305 1250 909019055 909019063
    0x1020d0e030703020f0c090c070c05060307020c18070e0d050f01020414100327030915180b1c1a0415080c15031803130f1a030420010e03010905 63
    0x2c54840c0d400e03503080305114040280d4070724041c03040c241d2011285c1c6c0407a10f01c07044c20b0300400c03030284281c803a28090f907a950005109a00308554080158101c1d620420321403412000b0222003000488102c0118100048001c0485443e406501e0080d8100c201910501008210040d00e0740c035900002e5660b152038020300021135000c402c885003c2e2540d040025003c41c0603014160348144103018001c5400100d42c03c802019503041410340601070503100100e40442d5036001c4000410030b41d16803e4440d50340004190760704031541c1c000480d5950a101503076403a40e0080f101007041881c444049508202681c050307107090801a00d10354068641a41206140f8040e00700c0d40480b03440e01d003680e020359072000c1070101d90202d500070700d626900b0400004900d400c0f001c06102407031400c01c1c1240c0c1000501c00307000021704555085040d25028209040105405500703c03080c07900720f00c01c10700c0e045080c1540c9000e01f100c4401c918000710350b686e0384400c4c0d4691084000340009038002b4001e01100d065810070b01c0c0c41e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 909021555 1250 909020305 909020317
    0x100501180c050306030604080d0b030330040506190e1e0d1b120203040b040f210308070e030c04061d0703020c030412022403150901080c0d0501020d0e03 67
    0x2565040c41590301c00c0d2401801503901c184400b501802c0c440d40d031075880031002e83c40413810806441d580d2040d800c07681c40030800340104809040310031211448206200b0001091243d07078a44190620040000060b408102c60b80c20041c07034004c01c1c40b203040701da0b10600500085207014089102d0360045000100071058041c0344181000d0035070b01c030320410213400c41d18440038002c0c1c1030900e107101d180780001880000000e1b000f0005481a2810030340c4480003480751740e0050f44001d030600c21401050003414184400420200c11741200c00d080070541d6a03018100100c014608014882038983c14201502c2c1405083c50031100100100324060715081200c800c0d602c0ca80034132544110010000744020b01074402c45903a007038141e0085051903d06000754950701c85800d81240c0020701c101c545005410054295101c07420000c20403070b240d240c00da05884049511010310b901c120400c0300100190312003c1038541116500b07580d03c1c45e841da00350900c180a88100303c4056800d070b181058407240030802001401c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 909022805 1250 909021555 909021599
    0x1a091c02010b0a170304031b0f0609090f050403142a07380c010e0a03080f07030b100f0e030a050a0b1024020c04050705040603060f0b031602100501 65
    0x80382649941d05119810000591000135500401003440032401c03103c4465110032000e401003007400d40700d100b015082c0042c0d502c10000724501074010700c241545e80c080d090b407a058494003007000c0d203400c2c0c0b00104210090704401500d00000203008d82d8080d40c00503c862a0520a02c03070b0090b0400b111705460b5501d0042c0729962411071034030300304072241c030751240381505192031045a10403c01051015591070391261142c2000c542da2208040f290b180706102c8030010314020307114122203180c0301301c1084680400500c0c4408241c600750100495944184041d40e58001134076100400403401c2c68250766403103001140c240e051140040030000c002d00000c004000b2881400d811091b502c03465031204805000303000d42850752100da504050041d02d40c00d04c900b020070300751040b58240c055500101d811030f2001d88900000980004050005580500034840201b0705406407002c89440d24500c1800d500000c1c0c030381c91444000f6241507000b2031081140811070814800b040010f56955100d60030400706031400c1003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 909024055 1250 909022805 909022819
    0x7031205221d040f0204020c0a0507030807060c1e030506061b010e0d0c120807090b0a18140310020f041703070203010b120d0c030212040e041506031a091c02010b 71
    0x922100e00c0c1040383d0080354840910300f5220007607170800010b50007050b040891071040c048420089542001075000a40c0076401103036070f03000da07828090240e901d80f5441a0070311403440c0c048500ca0100040c595961180b5250015494031104e00098035071150002000d190106564548014001944401400c02d0b00c02c04449005140b410700741d07070200c440781c00070b461440404081c4a806005044803a0b00c601c80385085103007a6100c2c187d06070f541d0440c2804000054428121007201d40c140311112000c7c0038907417182c0340c1541050700040e5942c610524070301d03a080d40106400008003070139001c0c2c40182101e40650b501c0851200c000d540d907500849005d0b403080d030a0900412003805c2c0f10a1400040d41c030030b0302501d000c1c81600d00694103080c1e010003c80451140b0b0790b03c031400303207000c902800180002d140d064007181000e090807540310750400e0a900030b443c503000003040000e460f490019603418144412112581e1841c40c400d0420404408010701d40c4502410146600e0307042d0321000c400300f0700310f5800e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 909025305 1250 909024055 909024089
    0x405031005062206030609050c030f06060d150e01060b0c010c05033c07090501110d02061314060412030f0e03030613021306020a03140306030703120522 67
    0xc0c05030380c410b407400358010300003222001503142c1000114040710b0910601240d400e6030b955904003125150744080d541900407200030011440c00f403080d99101d84411008061f24104100000d81070494907030300400b041002d03040f98445c824290405194049120020003105980e0070040f0f540b507006107411510b651821941c03400e00c5000d24141c074011004120003860311841101c421880104460051007254203500010140000901c00c0c0c9108000c10b58403100744501e000f001419500c0d0000c02d404040d001042c2110600358001030542c0e0000c03100d0405003442d400350420080b64007a00c60710300603a0240c04c081005201900d001306100d0365032030b03600300030780c60400760309030101c403200c6103230000c00e400400124415241c031034030411200c0e031100001450b0100003440400303d084141d0200707000d600201017040070b1503003125628001d00481c1c50710070b03d14503210000a0301d4000d2404000d000364000304428104034400c034242c035402204030074503a042d80080c900c40140b03c1c149100c0d850004684c00c0340c1f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 909026555 1250 909025305 909025333
    0x3120f01030f030f2715080c07110d05010507051e07150b0f09010e0603010506010c1a070306030812040c080c03030d0b06192c0d02040f0e0f03040503 66
    0x10541200e400107600c80e245802540c044400301380d6101c28030100201c00361092510048968100c0160f17440300007160030180b0b080464440712107480704034020720800c902000014840f410440d2446da500a0380750310501d01c600009100840350b500050710541c038001c200b091084c2c100b002040d94048418003c1c107032294160601040e40b04100d00244408100d0008181c80c0815801150040d80020007003019104a0004968110000d91000c134100c2d03120010700800f41420302c50260080c00c00c0ca012400010242ca840746810040418840c0408240d800140018446d030b0201c40555070024185035130f0580303044c60b0070600b1025641030315100c0d000d030740c0040c8403080001d4000c10600040d01460800d11302c030f08203100a0098181160704100d04000004000e0f6078114410781c208825100c041e1300d0030700e140102e02c0040c020b010301c28461100f0070114105a503031008440c0b0a50781194041410148800c41e0000740c4074803022a001440b44020b560395191005c0089c006a070020760480700440c030001c031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 909027805 1250 909026555 909026581
    0x20f03120f0c2b02041802030417090d0809010314040f0b010602010c0f0309020d0c030f030e03190b0612070f0302090f01050a06050c0f07030b04061401081e16080312 73
    0x140e1400254a00211001e0800c890002e03c03c2802250006042640e100c2103020062171460711030000e50303400401c020410401c00907102c81000e003071441904080c1d00710b02280403045019409411180041810074803a0310a0b04191301c04440210074480300c1c20207140078210f0203180f45041b110001088000302d00644144a260130700d292a9992406102003c0800e07001001158826600045051005401b01c0d10070306a10340110b00ca54802d0754a149541001030072030103a100c20074881d4001640c0044005c503220b030482003264000d004c014540c1c54a82c0014994600c90065029a006054000400d40100102002280c1c000daa8065141c0e40d0171180d07260a1209010345503101c900d2002c1807052501c03a5028040302400c8004072000301d490340811501d4112242d00c103c8001c4d04480402041000320300543c41208443c0303445810703035414040c041b5100c00d8101482e00035480d5518448411600800c06124020a840e140581030798565200f90b850794810b01c80c1c41d55000b404804900e405180350 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 909029055 1250 909027805 909027817
    0x1d07080724050c12120412080601090510020a020d030206010e01060903020f1e0d21030506181f090b01030b0d0201020d21060312091203050a0f0e13090c080a0201090b0a020f03120f0c 80
    0x4be40c0d000d81c0c00d023400100505550250500c0d0110b02c108603000005854941d18013125038025001400b00d9850300c0e240f400c0300c1d00160031040030401c100c0360400058035a00035204003100100e808046048101c5100c0420b489260000c5a1104440f243d40017880b08030b08402090707040c4804865074000401c501903040e107109071001c541046445405074800c02100400c20b0f0042c040717810050400c140e51250b04600b854540105c9181551188166020340e05442201552042602c01001c070381c1703558002035112485615160140305114441a000081c06014001448907844040044544030304109840c1011440c0741000305e0301046002c80c03480b50b82070711012100d52594401e46040c1c00300d0310440311405000500410b0089400141900c0d60f50b4080c5480608000240042ca0b0607150509508a07445a4004007003608850f80450250340d0040e030020548292001e159a90b20300d00c0d00485c0b810030140d040420034040850321060314000d894049019034480c0200e1045c50f19110b2214909107d0341f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 909030305 1250 909029055 909029057
    0xd031425111c1a0a1b27140f030f19060e011107110d0c03080d1505030d03110d0528020f07060f1d07080724050c12120412080601 57
    0x440d08035280d00e0001c00f995074040414000800c81301c581c088400090b0398946082e05c00302c1d65140c1d40c40400c2d91512480c0d80035a401001e041d504a00d007901c100008001a4105805900d18008000003914104540b0070410861000c0342c60302d0045c210191345206424008540c50b50601701c000b216903005001d1000400b00e004c8401e8030f0080386558601462082c1d00d40283c000c0340c585440300c0810046581080110301400603a80c0d50001e049140040b00c220000c2c00074448180310050000380c40020350301d80c054401c4e0a000405003c079604489260081c00001c0f40c2540c01c0504000c4c1c05401684d8041d108890341d042c1202c0d440324001001d0a90083c00b9403030007814001d12860b804a2860341210682c800c02c2800019190841c05182100e480c40003101c142c00e40c05000100503c1604104183c01062000200b814504c4804202e54940201514100402002107007040d01c0300e20a1010107044000841210355400700c1440d04014101d0803981a101d02c8040e50011701564091300200d40b2031901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 909031555 1250 909030305 909030323
    0x90708061816141206060a09050306180f0a03020c0d150e031c0501030519060b03121801080c0714120a0e0f010309020f24031e01050d031425111c 64
    0x2426041c00242e41011f0302020400c010800001187c0d2003c1c00294001c010003644030390075040c80011507107029140d0394070254580c010130080000c2a80858072045500702103608803c1e0400c40d081803242403000c10b0301b51005078900400b15a18000c0000205008140300c1850340c03c0315058904042180c0342480003074131641106078940304407010100d181c0b440b039110304d50000d09940c0080100380341170460449032140c1a000242e8a241120310100c102c0d00340c41c00d290003661031425485415440c000c0c41c9004050540c08041d04070b0b41c42d01800020700302e944410546480e0300c443c1c1d4000740000340c602e0391365000d04004000f01c0007552080c0500c0021070340240c400302020030f1803c140300701d21035000101190303450305842e40c40074005504021070107880d001d244000c0308103505401d03003906041a40200e102d99440b400580000c1d4010540b80071014a2100094560300c044803106003041100c0c12024004000f8891038080000b0084003540c0380c41e0545103c2e0b0700c204140f250b00d01c403003183d450150407049 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 909032805 1250 909031555 909031561
    0xe1006031d0a0b0f060a0f090c020703211e020c0d05100f0f0c0c0f060203040303110304030c0c08070f090e070308040e071202090907080618161412 65
    0x1009420041c9040c28000129800c0300e4080081c900b0324041400c100c800c244084203000d000b0380030400f0300340c001d0b50031140040c40ea45800400c828540d07091090601d0300b526072040c030011a0082c808a80159040b009100c8040246c010a190055001c5222404215808184140c03003400c0e43c081d0b0140c41c500e40051182906080801088000120040315144144040400300010b40e0040c0040fa044050300851032a8402e0b206405541803041408204035410f188840480c1c2e0079440e00c1810743c1c0203e001a5281c5541c20124041d1014141c0300c01c04071800024402056802a0302d140342034083d2030b64445060300c913400300740c0303032100c4d0b115050007040000c10500031034240b507103c00c00c042107020440c0e00403a66642d03182595013241d441040c0d22080d00c000c001030075411010f1509c1c290651070045240c010183d000820900d80540f40a04115554000a0307460315211307003500404c100e8840400d0b040c0790290a18a04045d10720800c0000740c0007850020119020009566034180300312144007041d9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 909034055 1250 909032805 909032807
    0x9050a060806150a0903050114150d0809100503041e1203150f030303020406021621050a1403090126010603050603070f0308090901050d0b161404080607090e1006 71
    0x4000e03082643c001c0086042c1141094580010520200d0f0707521484c4c030140c55400c00d103007160515541c2480c0000e4400c00c00011003001c00001c1c5041c00c00b210f140030304ca415824018101e0184c1902c054100524000580b06980c001015601c00c0344a140c16880340d60300071050072141c91407660300803c02d008404541042600075005240014105400381411a035240072500c9090010740c019004650b00003000d014039541400761050091544040720314103450700c440441040d0401d1200403050502040072800c104050003e601c04075080340904918941404c006034403a4800d0424501150319596181864410030315007482044100300d03004000e80c81d100d8250098080180000d5040c0503841000c82d00080101103030f0080c501407460380361a4640c0d1400c0c00382481040c2c0200344501e02100c0e104000800d84034142e544180d08004c24606010762000c1901c0f0300b440c0400740409120041808100750000240382c522502c090350341d43e844a80c1e0b445066100341d809807032100c82402c1c8420280212 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 909035305 1250 909034055 909034067
    0xa0201051803011503030f08072a061416030e03070b070215040308012102060904090c050a09021206092401020316031101050601020115050d0f0206030103030801090c09050a06 77
    0x8640c00e0714403054508000001d0864907618450000904e070100300307009041d44488a80001d00e02070508682c00d0a124402030442000d06000300380040002d40c0f04050520042c0c400c031100c2d58020014450b0f11010000251130320380840300032401c081e030001840800e602c41e0080c0e641101004000e9458080d181d141d520020000800d02010b40c8900342201c03c41554803081288a9402075445030304a50502c4513007820f00800059007150000d201081c0b901603524802140c50035001268006018426803507c0d29000071984e000c5940141c80d20f80014145050740c0081420441c96044c2c80c0e800d40d00e040c100104200150b0740400030240c21100b214075652054140d85607404140105ca0600080442c1c00b40ca250a00303108500045074440a0345202c1320074060300f40c102400f40020700c004080070a0b88280e114003440b03030350300c200c008450500074070043d48a40e0300c80b10380141549599685904024090072801e00c60401900d241407509424244580b102a0590b00003c00d0802030b40d140010464074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 909036555 1250 909035305 909035317
    0x41b0518031c0507050705030105010e010603020d110313050c3c06071101020f1c0509041d060f010b0f03010b09060c0a061e060e01170307080406020c0901170a020105 73
    0x340c45160380899000840b01d410121100d4550f42c2c0d2581d03802d1901c0e0403420214150301c40d6020b60706000050000c0306241c0c0b9400d0554909140041e101c00c0030001c000c01401c52090000108180003007030141207185070000c1c203409030185040b81c0480c200c1c8014000daa5414114850b40c3c000780218402d46500b4548940b0042c40c005060643e0a50700314000501c980d000c640100c4002020325499101c0756014403030880183d0b070750809032148000b1020308800d0386110031500800c0000001d2500810f5550f0340c005082101505a02c00340300904880da1aa212001d41d0000c120101000001980e5011403040f0750010303d6505506003540d103090715400035a0480c83d10382d80d1084081c0310090113072600700050100e080c022480407541c441c812441c40d500829810850f48843d0800344240701031001082c41504440242504260b40300d09a0710345400e43c00b4080e0020045400000d0010760280d0014200c0080ea400300c9030b2400c40d0341d88188821500d14041651000d6802490f0040050740c0070354041c1c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 909037805 1250 909036555 909036559
    0x1603020f061903020711011b02062505010504060e030a020c040515090f0421050304261207030f020c3705030d0b01030209010c0b040f0b0f06041b0518 66
    0x41004403001e40c1000381d403030216042c40001c0e800300d603480502031108003030403862500303080140c1d121021a030740b8240b03003022500c082e00503003001401816400104e000e8101c0305500d0064003a5450140c036049020b04020382d001c2c0c48a608019400c140c4007000f1044481c1483e86d90010095080c000007480003130440101884034481101510740d116840700c407036031442000070f07201c0780c04140351034500032882c0d00e405050b06203001d88514032412078a820100300c98000b034111003504002401c1c1038081803480d00c441c4180c0420080415002d000c41190a8201e0043d011a20188144120814036408074005c518003404980d000b40f4140240c40d00c0d00800c1141c039141500642060010300f01a54075401c0350b204111840c2c0c0c00050021501019846510801c1d042444c0552400314070034002003603d45202d50140c090100c92000c0303002c0194102410b580140d2004412a0900d090384000f001460210303005800b803030600102c465412801621410f5559460716032504000d87d02c41482c1c0c02c1c00744090380e69 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 909039055 1250 909037805 909037807
    0x6040e0403140c0a060c080106050912030c030705070906050913080a121104140a0b0304140a02040c17090a1e02040609051003020a0b1c0c0c02090114121603020f06 72
    0x4110804080c0003050402c3c104001480700410f03e1400c5030850b0504282c2000308641c90307005000c010b41c40021285031280488035014505100800e4030f0451088440401e0540300000340c040c10010042844d01c100d80a01c1d03010014281d44400f40f241c410303402c8071205810340d600e407803c1c000140380c80007400e001e89891030580e40c1e001e491f400c13980480d4444986401c840038040340412204101942c4204440360582e00700c5000d91030500c1c28405030002410080c10500254942e00481e0800c002c80040d03250010000e003d4450b4140000c1d0101000045400503183d80e0000140d4228000601c800710990240200440d22a02884182580200442280c0c49a11440001030b5141355029060040040ca034600c0c1100d807951042141000b07855000c654840d0302070009201000c030180b140c081d16142e265000c80d00c0080200111250045404000d500040890001c560a008008903c003092401d0354100400c081c02c02003039076550401c65000005075801c1c3e105100509061000c4c0070040b02c003418131 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 909040305 1250 909039055 909039077
    0x60f0c011b02062e06052d040e0f0402010e0910050d06060e011707180902030d03050f151e030a150c18050321040b0705031b010b06040e0403 62
    0x207508100301e0120a100164052400c0c4840c90a0380e007030b07440141940302c4040d155010320710154558000907201d040103000303000c11081450105030b44d00340c06500c02150008401101c030400c0700069000350040c504020641c0c030010710054000e1070b950b0300880e0142c40d80300c4d111032410100005000018500c1c80095480c00c40002c240d10341d450000d01e807910803500428418140b598240301c11405a11004c1d228903002000000c941e8041000740554a100800000007280d810070000a0100c0b003000030340501c16520a0012140c1c141c0c0f02a016403104620140b05446840446205450843c0d2050f444140d202d40070140203205405201c840002400b5904c900d1000d0b21000ca410060308017640e1041c4e115a444c1500c01d5120108009005100304031601c1e05003031174042503076940001d0f10144460502603055082c056144282e50050120b0785290ba503c00c1303a440c1090f04d0b5081080356080d5220382c510b62820740301041c016100d451801411940c100ba142c501010308942001d8019002d0107106444 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 909041555 1250 909040305 909040331
    0x60d0f03031b0809010e0c01080a181a09060c090609010c05010f0219091e152312010806060904081b0d0e0102390a150905031902060f0c01 61
    0x35210249240381c862901618241d604517003560342003c00114513400c0003035a000a81c5c0c1003400160010380c4000e00050354180e007070001d00101074000001e0010341014001701e08840024540c0d5200c4e80071305040d6020b945440c074801401d8011101440d03402390007071150015552103250340000240c020000410300e0140751072000c0c226800aa004202d000070140c1030307102c05420401201c001c082101514401200076070024411080070b01a01c120780135000c04040d10720f4810a4448410601c01001e0305016801c0f1503652320607848010a802841ea1580c00000c0c1e004012070918413880c800f40402c8111b03039855803106004d0707201011016241c0c2c2d004280303400340902001008040d0499495001000c90300384006840c0a00d19020000c07030500c2c4034a001c201c01e40d00c0055003450b907038003070740402a100c0c00300008003224003a030049000310b01840e0f44480c034a5170200100044400c181c1c1034500340002c4030b111440410340810b020790031090401c40056110440d41c010010b1841e1040002000c401c9850 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 909042805 1250 909041555 909041591
    0xc0627060e011e1a062a03030603071208130e0108010c0207030807020103180602030108030403061b090b1614011b02030a020c091503010c0305192a0e060307031a0108060d0f0303 78
    0x1401090740d400f06c2201305904a40900711583c0d41025401107040d4903005c00065074413400781c02540d443c0070394407009508010041c002d0b500717600205040800c040d0b441d601c0c040e0b0039040900c074128140d03003449041c00c0034500200300c0348280c0c0d0304094041e01d0f05410b030f00150041c00035580921803000200c80500c01159051000e14040c140c1d00303001d03541d184d1541c20039500f03031500e51882c0380081e44042051106d0b65081000601200d04c000d0000d07031540c16070351030b00100894002c006480e581941496040401c5d045d80192600c0b4410784010110f03a80003a03040740d40b8010280740002582c44012540050b00d800b07004154840c000c0b1444c203486160300800309017034686071480304001c292180184031042c820400041c0a41e4003112040055070311203400c1c80b000c603901640240700c90081c40301e8965082c0c030990420120b0000500312665a041800c0d0081c020180d129210300441400d85042103250701c1390714141d00074407006100300240b0706613444a80c0741045001048062555840056085045c00301e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 909044055 1250 909042805 909042817
    0x15020714011e0908061008030a081b07050a020913050d120207060c020307020a0801050601050a030b060d0c17010e10030809030a1704080601080307050d0c0627060e011e1a06 76
    0x650f80c00c50f00ca00e08855680b41c604040e2007001c000000c16000c2c003200b80004282c0c1d074402010b24007200c035a00c91100c01010600b00100c004000500000d0f4282407040005034402064802d9981212903900d807182c088071908a008000c0194010a0400400390f105440404042c544500300600d008070a950304404c0741d140c0c24443d00940c2020540c102986409101c40000701401030080c0601d141040000303005104800c008000e02d07a03941080b0009403108000d4501d21401e243e810400071041b05005042e003140d202c2d20042890751840082004150407624500414414008101d5076041d9555508160010a2450340521414907100042040c01070107840002e030f4090045c0d90b95041c503041d0ba0401005070000441340e8000c22002d400140002803000018540f4a410b41d0091418602a0083c1c03020f901c0100c0411041a000c01c01300c00c480e40e0005850f40b00d085c040002c45a1848900d00341c030038514180300c1820a43c541c016418040d0740121940040f0050700081019140d0001110742e0010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 909045305 1250 909044055 909044057
    0x30c13091a011139010915030f02040e0f010e090c01020717210a1805030d030510240e0f010c03050309151503070b030c04091a120f060115020714011e 66
    0x490703500130124201c03134900c1074409007868080881402c0c006203054940304880d003602015038640481c0700a040d980c0c1910040d1141a0071080142007508038240c0c14102805810182d13030030040401c042100015410700c1440b41030b005804d08600d401c042132603261011032000524014441001e5060301d002146901030100d40c00207a40b074141d402001032401341c980c14034941d4810300d0b400030300855038001a5407100071071900c1c000c5225030310200c0445a40c801c5501c842009648038080409a21251011340c00d000e03026500c40451503030450400003144209081e0501240f018902032010900c150700455100c140e0804488041750210401e07400008100c0e02081036206884800d03401c5d1500f4441000180414682d040c00d50030a0344200d421442588202160141d8a807040121079820400c070046e905c50090031901158502d65a860f110b090105071500c050003000008222410348406d07003520f071401a4002c1215908040d010502422007042e260305120b2040c0000144680c5160900c5110b002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 909046555 1250 909045305 909045373
    0x10f1d1302010e281203020c0d060603020907050a03140114151608030f1005010f050c0c2710080a140a050d110606010203090117100b030c13091a0111 66
    0x40700710449404030584c02210400b090100703100d010950000c0c48d18042c10044034040e0100100340f5001c030082525900007904405070808000e207840d0050050041011b80e40c80504c40201d0400030010a50760901620300440c440c074400c4403050600c022500d0301080144801d031300d003500c400d103800b0299141100860b01c1315000000c102ca0760360749124058005000101000b606810705002800d000c0880d600c45080020100e102960840104102030010b5030207080d0448001a9110201c140c0813a40c02e6020280000380229180806009080c0c0403210142c001d030a00c215290f4500b80d40c0d800304429212913200316603800010401c107000041d0407038259203680003105400c031801401c00c8002814030381990003c0c002c40751141d03005119419050350b44600321005680d03885507891582e4154100c15581d02012081100d10950803004055200300c5816140748565240315043c00d569105c2040804030204c02c51282480d4010218582150040f83c00d072800400350300e0366001c00007406040a840044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 909047805 1250 909046555 909046609
    0x90305070b18040903080f0c070b010909020414070905010c02190e2401171e040309050a082b210203041707050607081005031005010f1d1302010e 64
    0xd00780c032541000d541c152400c2c00315504039103014020920051814010f1f200d4480060b0400100c041252021688051148160b507104c0d42200c0062104480490069140c6601c00d9054010500d915218240c0b0380e607407048182c10580119600c0500c1c1008982100300c440134464500c0751342c0b410354041d02d460040b02455180140b00035440003c60740400c09803000c03480e050005a6400f003d11341d1804142d1611003e5074603185403401500c040300c400240b91403020320a00c400c04d40d000c42c1500c104c0c2c5007250304118580e1200c01490304ca07050f01e030303194880802895080d8440e1403030081031402441c0030f007400c0d14040d0301c85136007030001e40302840a50b00c01d50f800000c100c01c000c600c1c20505d120301121410305d07040c0109941e03004c0d541d05001e8144014084a60005840040c24900040151030081c09131000e00000c0c08481c1d024200038011040000007461001c0313602c0032502c0c2c40410200f45000c0081e4951106c0c00420b1405044800c2641041445418a00103894488403035036402c26940308210820 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 909049055 1250 909047805 909047827
    0x21c0b060d14070e0607210e040c0f090602010605031e010b090f0103020306010603020903100504140a06090c12080414030106050924030f0a0303180f0503030a05090703080415090305070b 82
    0x80200980301c5d02c01c41c81030040201152906440c0c0c2c81500f0784054120b00c1c034104000c1601d0f0b01d404080c00b194454140801600e01c180d114012440d4880c0c00d844518409483d440c080c1e003a18031500031142c0503440f40c40c502503200e0411558120000c10a0000505080e02c50302240301028100c03500b641e0350b0a444010001c5090070400700d0b00503c3c051608505000d02000025100c840346040500c015807900003050600002c1c0b1048144080348204843d0403201902d0824050300110748290f0f5220560715000911040d4201a03400c1a0342c0204554907050070950840b041200129a807030709076603100804145500e0b08084940a1009003441aa04003000000c4901c1350311038055044c001d401601c3c0c2003112050000754014642e0740350a001c1240744444030000110030f10000060b00b0525200c005c001030140210040d4090a07002e2402e2240d0394030705608035940c44d06448000c00c03210f800c0008103c0b003000070b548bc0600c18402c2c60070344c00840da01c1d02e400d8500700454100280b08000090081001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 909050305 1250 909049055 909049067
    0x60e0609130528091e170d0b0913020609061c020d0f0e0d0905060c100c1701060c15020f16081c060513201306090603021c0b060d1407 59
    0x201125041480440e403c0d590351209803040c684024014200c0c420680108844941a80c07641a94104100d8403440d52481c0c1d4005010301d900001c0c01027001d000030440d08035505c00c816594a8000d010249030401900a2140c0c030303803200c801c0204d80750405002c1c1d4014841400140500300c0c020002088040c41035006c0c00494404584084050b48200c10380f440281d0020303108411100102c03500d0b600c621a200310700f824800d601d40c207050002c0ca418034020016030405420001043d02d00d01081d045d81e21003100740c80309900c00201130055a210208803d0072500d0317070001d01c155941341c290142001d406c0090103900b80b443e0001103501c5000420351400d1201c001000c1384502d2455101480318a00d0320b800315480d00e581c1020a4105521884404081c01080c9203104501c0444841381e66150440810741e88080290b000e140001054400000345552080c001c3d2a03810080c40b0500300348104501d1018021301c1e81c9140b09801074024440082c07a14450710812410b031a12001001040c0741c000c3d4001c1c22 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 909051555 1250 909050305 909050371
    0x70303020a150216061806060314071508060d020a03020d05010606080702190b0405150405010c030b0d03120e1e011a030a0f15150825060e06091305 65
    0x2e548144150030f0f044a41240421031141c102200080928515407006c44007000503c014103800e00b800f0b0000b04000400e098042192000b50540301410f0700d422140114408041c54100050740e100041011450880303040960180300074250000d8690b21303400303e42c92425030f0b902076070242d544480400c207141d04048402d91114180c80501107500c09668503076050304030944086c0000103042c00040410030200401034441d850b03840b8446062400346445070180c0000c400704000641400180310a50500c980f082030095416160310401c13050385103005004014010000f019803280740740c10780d8035015040e480016043c00800100310140f490000300205400303080040d00a5100d606941c002c5040011a0268554044a020030a00c0c2110209002c2d00c001104d4041c100003000000410210004d60720501003030744003542c0200030320100c8454091095100315000305680e418a42118900b2000074122140010000080c01c104946084111101102c0304109810f45840840310b403000b907400192 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 909052805 1250 909051555 909051593
    0x201050d0b3001060608013503030c13050108130f0c0302060a1101110a0801230307061125122405070219030207060509011205040b07140405030c060705030c070303020a 74
    0x1045502d00120880d91900f40840441d90b100500b23403d409183c1003040004c80e01250208994403401d00c08240e0803668030200204803401700c140b800240ca5409410114803e03245a20640d02c285519210300302d0001a61008881d680c02210000c401aa00c460107451100c04540c0c41c0d07140410b0051545003105c84a9110140d04d10042c4508010360398407403007081c190303464100c2c1da5010031040c100b1041c200103440c0072203a040c0100000428001d0340700000001842d03d010496000b000c8900c640440c05c8454000c200d26080010000d100c81c0c1e4211074459600c1c1c1c400d814550f0f80c0710075011007115005041c1e41495803a5154070038410080c1d07040001020b10040801c5075100d0140c40d54001c0d43c2d030102c0e072040c0010f104c1d002c50106a160700440500780c460b59902c0040c0300c00c0ca82443c10000f451411900c0501151007140c0c2074000440c2c031415a429100054002c045042d5082d08208a581001c00c2c1226288020401c5c01903400c414020800118800e8004003185843d500e080c2a41c1800300b60809 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 909054055 1250 909052805 909052817
    0x19020301051003020a0c0b161b110609130501030f1403120f0408040504020705010f110901020c0402070c05061b0114090a0b06030129040b0a030201050d0b30010606 72
    0x30140e603507824102e012046150400683d030701400d900c1614071070001e400c060030366036031b00c000c00020301e00c04d000d10b09a0303c1080c0d07103a9400505100c1c00d89600202a0400350590410013900c50280c20a50014580031230001d102030310f44001100264140c50003600215082540380c0002d2041090004102c41030054500203541442c4081100b08100500141051458036800c004601880742850850b800b5007005801555911841d08080c1d010700010142e100810f8039010601c64440102c506403294590164080e01c2c0c444403001c01c0101a40050308165940203002c0b40000c0c0c1e5580d008000d01c00d803031034245c204852015040c0c04c5070845114400d64102c0604c0d00c810044880400b260b1005034660041005042c0c0d00c0c0c03607010030700520307140b0030351103060f24404c8031103064200710306000c01915806c40d014018624507000340030400e01c451000a0118509000803403c2502c203400413840d910010303080503c02d405805400c01103a40d510b20300d811074071a21001074101c0c80280540000340150b81480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 909055305 1250 909054055 909054059
    0x90a0f0806090304301203230c04030b060f12160605070f080307020c12150912030c280302030106030f0618020901020312040308070906020d02030403080705031e0319020301 76
    0x40c68205540b4a101c49801741a60000d40d484100100b10001040d0460594030003032110040240007420083c032007084180c170650415800001c803010f400d20038101c90f403603581813a26540d035017044c480014200d60b90160408902c00d000c0d84074000980c600044035002801139074101c1007241c4074a02960000b00c10043c0030050707000404c800d04e400801c6a50700c190f102d6074136070701d0800403400c08601d00d10141c2d029100010841445800040c10000721141c24100407198507210520f0343d882000f9502844842d0081c400545401038880142601e043d10245580121803c2c0d0090301b14060045000c0c4040307a800300c014401d0b41c0d81441409c41010340c078002080418100780b24100441070f0390510713084c01c0384c0008a6400c50392090050380c410458040e410502824a8500a0490042140c02400150b09028001026840090030302000d5440d900590314203811501c40000641c070a41044c0d0302c0344400c01645040301e0585449101641011031015220304000d10407018075040500584c3c4124014401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 909056555 1250 909055305 909055319
    0x1060906081b0f0d0509070f0b070c0501031d0607051e122206050a02041d0106090303050706230a06050f030c1c020307030609060b220c05090a0f0806090304 69
    0x4000b200c102d03060758041c1c8846040c00c0307104484c810304a0340d00f40c40b81000c080c403901c48800145074040c8d0b50002a4000d03100c3e01c07042a01c2c0c20b40039801e0041e100012102c0104042e501070b501c8201103d44800340038480c0c403c000030031458064292141e00004000240031890702000004040120020075129441d2440381d40004625032005480703001c460316040400d004090100c44403440c201c1d03001a01380020302d01000004e009400030b01c24000b0400b4100d42c0e00e29100c000c01e040506a44003610f81d0b007030650543c1c4046645801c5031000b22013440d51000003141100801100352000503036070354252198649403070240107568031a400b45006584d88441e024080d680480c1c0241c550a0982c0d1810400c003400c215500303c0c09421101a425008614010007402196080107801a011705410700120494005200e400009070b0a2501e031041c40580007280310b84160030181901c01035140090030f00254030000303070300c0c1105540001d000450310752042003d0a170601641d54000c01800245040a181c075207 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 909057805 1250 909056555 909056581
    0x108180303042004060801020408150105060d05090a02091f061404050d150e0a0308100f051009081f1506051b07030807030908161532030106090608 65
    0x1016000e030306101c2c028081103003140098400e0300400c05d001060b07803240030340d001394000d0294800c1805213203294a4400c0500004a04950380034145c1442c103180200800c00414010b41042c0d180e0240c6000b000150799003007513043c0100d00285a5803054036480f01108110b020f5540140184010700b602c11080014201c20744e001c4440545582000800e14501013801c905180396152600380360000e001100b800018240100c61704c261103600c031584600f10b900c245818a0320480d5001d201950b020700c000d04003404950800041c9003460714203030ba20740b90400d04140030072000c04103211004c40350ba60048080d00403000c0180700ea80111041f00c1c240030000b401c43c0300381603a40b010222113049600c2c403607108110820085070040a0b540d102d41072803400504442c030f5881500940d2103110000481010311500310021907030800081e40100540c0d5005440600c010450356081c0950603000c41070740780014003650568100400c419641e0742c14054054400c03c0290004020043c0c84820800c440d0700c805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 909059055 1250 909057805 909057811
    0x3150501030902030f01050906010e100e0112030c020a03060b0f0402070b04080c160e01030309080f0a1e060509240108030304080d0f0c11010615120b060415020a020108180303 77
    0x2107000308082400b400441c0c9440c0c0404099a590342c80d040c104400035801007802c0e0705951448100e5402c0c2e440d41102c2220904c0d050140e1800d05400360b00400c920b4801c0c0d003113074032590b100e410104034a42e4140c00107400c8a4440d8010b8030b001d0380f100040c1d0305500d000c0160145411080b9400c605080303061300c51b17188600004000810310180042c41c0e000e00c02c0c08201c00c8061100802110a02c030b6129240e0f20b82c00d620030b00c82200070030005d45010445042c0840d20302020300c80540100f2401c07029445a0b40f12200d071505442d0710400400c1d40c400410000d015103441440b03070100410080d070304640c8031408200d811201043c440d1500780140240480030044076040f42d0007513581a110410000705c100200400075902d04100d103024a205e05080d0858100345c0d4902e4020001c004440d656070102e00d8080640441d500001e992070a00003420a0907070040c0003e0300d004d81000d0030541c4905207070020400308000c040c0540e101e0307005d0f10115a03000c1a13140d48407407501032042c2e04210400d2219a240405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 909060305 1250 909059055 909059057
    0x1603050c040f1d070303140a05032a12010e10030203030316170f0f071806030906090605131101020c0105070f02030f0d090806060d02180a020403020d061a0103150501 73
    0x2a000d40d10784082c0700d0b044214040807441441c9848180c066600d07954038518032084000c601d054803180b0b07000030703a0f40545003480d8050f181c1601c0c560310301000c020302001c41499070220f101c08954983d42061031102030102c0c82d101c0222118030394140058600485001480c801c400e0340c2d10310091005031004400c1c1e035040360420301460901d85c1052400ea81217190610044520030351003007049017402080301e00368024031010000714801d40740c01e40202e03113200640c0c2c0307010543c05803064200f020382c3c400d6003d6201140101030002d500e000130703030703a030402c0d104141e50003000b0302501003003041031080c40403c224203004240018008074100c000060158003801902909030604c0f0319224096440c2405508410700015060300c00440c07400381e000d0185403003070007883c00d18411500020142e041145601d000960010540000e00d1000c0d903461030501001480d40d40d0b1a5000e0000200580750903c1d03032220144100c0740412920030300d0540380c0c2c6c4100c202e08428100b500340f0303c5038100208200e05845c283c4a003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 909061555 1250 909060305 909060311
    0x312242607030f15020c06072006090606120109051501050a15201e06071106040b01050607051e0c010f050304020a05060a050c03033108030703020a260402031603050c04 74
    0x22a01a400c0207000e113203508003040c0150b40400203070543c0101000185504c0e9442c052030320309c207604655a6984201c603160804e41c064400300341c6508d006040302a03102c100d04000310352200c0c240d50f450701388003403003003500401c03100100140118503006181c100549035030004400d6150000100900480d01120170200000c82ea0940d940e9848040c0034001440c8440c04070341c480650318901003640c80030b0468458000902c0d8409507417066001240300c40c015900000040016400c00042240c15480414102c9941c411442922801c0522545c190010030b440c00142c01e40075401d0380054851040401c82c9010450708004110060380e0300d0041c0c2c019541d090f01c004c0d488000250043d2654880c0c404500110721001c01000342001c03245090f40c070400c610718407100c14a02591070032036026540d01e100034000e80303003440041c0205200754003038203c2d4032040c50607800250b42506040300302020b141620b4000300c0c07070f80b08000c2541400c00c400700e00d003e4064800007080b85140c507010f48034560045c000d07100740e031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 909062805 1250 909061555 909061583
    0x703080a0c030e060411040e070b040e1f08060f0f01230f0a0e0618010b03151c06020d0c02070602070302010e0607140607020607030203040312242607030f 68
    0x482603000c0040c888000e0f00b100d6041c1424246151400c1d03000040c02d22603401d0000c0704101c07940200380c0c04216100b86803a10b080c80d051104001a02500a02480c1e521009080886c04041460040d00080ca8500d0140c40e40303081100d66110255401443d000d0500440310040142da20243c1050714070810f40e5180c502c070314507100006078500c9a895039040c2e0103e8a9040418450b4030807560318020a011107641c01c3c01c2e420f0544100c00e01c07000740310314407103160b040c000600c039414290100102e10f80002c042d903031001d03480240302e910320080135401d54009074081303010b407055151031141003680125030000700600c0d480d01000950760156404002e0403c0000543c0003070a440310800c2c0c500155200761503440b0a0302400c1860b642d211f04941810042c8030b0f003800300391030382c1c00f902c200d80c0103a03010750758070300e05001c3d1480a0014040030440300200365001251a0041040480c581002c1c004080181c40b5000c24980d2008180703100e00c02407403044d005241e00304001088841c3c81d20410f42d0002d14a4a204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 909064055 1250 909062805 909062807
    0x80f07052116090f05030d140d05131407050604060c0309090e01020a09060c03050904050c0c0f01150b0405031e1c12050c13140402070c030c0f08030703080a0c 70
    0x100081d502a40054000107122486104054158508006542e1421426580c038070600480100b031090b0360b0140c014040100d0968400e5542c10074400300c4440b0a460003000d0907014084800c100e52800452035181300b240200884080808070b9580b00710020040b03241442c0001c0c9542c030851098000b803109641380c1c8010140909400300050900580403c000f403882070469010390301043d420400a8156075002c100c050150a030a461242c240d550740b0b0914980d0303001c1c00018034016184031440304d0144400000321b481008400d400302c0d4001c0010480400d520100b5407580d8494010000d01c0000380014403807614000740c902540e25107120414080484c117044c1a0800e02050144040a038070762041c40d8100303401803980c020350143c41008010320b83e940c40604d5a54010410012840c0d18400070400c00c03482e554a6001c0713202c80081c001850701040b603941c6515882c041d80100c502c452218420800c0b80b0076805030200400550015500d440b229940050501c60000c080904d000e41e2801003d03481 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 909065305 1250 909064055 909064087
    0x1206091b030c0d120f05040f06030b0d05010510030c0909020f04050601090803070c180c1b020a0f090617010509061317040e060f150412080f0301060519080f0705 71
    0x224090804043c038401070801c13101c505103201003140440c5a001580c10001d12a0040303804030307032581c0c10710341e801410701d00218064110003030029032058003070794840e001c580280700700e6028900b01c0040d80c0d51a4a985010310180c019940295081c6207040b202d40090780f500e490a04000c0021138002480c1c1e50346d040181c490301150380104116201c04980707a4100310000b2042c006803440b8034005101c085180165030282e078600d00000f00001c186400708109407184280d03028078144010328407420b0300d84420290001140301c0d8009100725844032420071201880b0303c0120f003070840034402403119140c058070082d590075015103a41e07c3c01c5c0311074613800244000e5030000d01c02980c1b14a103260360345640701c2040540413010381d0704030b02c40c0f05e51803464401441c107075095008c20702c1540d40d0503080901d84031052101d186000d10a8075640410010201e40c00756050045020740959103c0984405e09408a203020803400402041440105414001010090701800398000428074149030790300315241e081110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 909066555 1250 909065305 909065323
    0x110703060b03030c070e0708161b06061a0703080f01031106030403020f010903050c01140420041e061a030f010b1b010e06161806050c07080d0507021206091b03 70
    0x824040c0d07003800700d480520706c0240d6000c3c000e51707566a034841d110340c22410900c03c0060b05420100300c00490340d0101007030620100317034120300414002400e660341b80159081c03490b02d8412101c81c468001440c4d02010741280c0020f80000c41c00700380045543c115910001d13402c1e03101c01c9091103014040001810075208020808100c040c0070000d101c0940b4a01d0080c2040d0019004c00019500b048050b02500114124161240f6000141013400390443c1940408013030303512480e10341090300e80c1c0f182c980711031a400c40307507413036616110001500c0c5140c111a0541280d09014202e0090401c100b80440e4103009880d95055680020141e659074010300742c030350100344900d1100e0b10709509280b0264807011b00070030094480d030180c50500e01c002540d00401c071140342c5110051200c0c030820f141c0902c040d6201e02c001c1c0410450303c07401c840c14240c44814007454650b404040800143d4001211011814540c80f80802d201541005102d541400394040c4e482d4041c0500e911403003040904c0a03203440e54108030b040c203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 909067805 1250 909066555 909066577
    0x315190305030403231507050c07050d2001050406120c0306170127030c06200417120901020c010f0318050c0405100f0b0705070e150a0501110703060b0303 68
    0x1580f10364030b2500c1c410700f1124480740141c00b0701240b183d060032403020500d80480d01075504520042d50b070340e403401d403000d401415040074a4400c4540c08031380d40e1940d590941c001c0c2e0207541550807070340342e080002e042042818003040c1006414482042000e80084c00c07460140650600410316280c60701382140241100e5005180e03580010052480e4100306600050340400b40d003156236004c80e5403803040c005081e141c0324020000346105100b54045040c640c40605105c0d0380c0d512160210341002c0c161102500300e40c0000700808907a1440c031207250002c01c0b0b2941c040031804002810b000a20340043d4803450000d201505206116440100141c400d610100555000d46130000005101d800c2c030700c2d5590300352041c041c060ba1034040810501c1a458000c00c00300c030a1460008204c90800c644410341da0000c1c030003211a8402e003032020804240345044588620240030b546098103140008006410001e580080d06011680421091101020900b48152900709002290040b514804a8034612650300800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 909069055 1250 909067805 909067807
    0x8041511160302101d010b0406050114280503091618050a0608030f040e0f01150f053a0c02030a0e01050c012c010b0a12110312031b031519030503 64
    0x706000300000440404003102e100200980c07e43d440134402102c0c0603000e500d0109624000c0300d800300280d14020400c900c65003c10381180c079104100d0000f40780301c140030000410000b004220500600704a0202540206082c01c05054a000704084407600800070605c10780f42c80d8400551602455007002d00142041c0003203030f54500c01202e042d003483c0c0103800346484085186007c2142d46c7c0100e400507050703456007201d060340900994002d80308151443c0d81c01c0c044c0182449580c0080c071459010319201061b40b040c0301ca042480c041c0351481442c540038804446440c0c04216403240e03034004140e075007042d1a41400d003a0071340700c540141d48902a85070100f04641c07c009c001d20312142c130442c4940244000c22080b00e21050301540e01d034244e49200c0c1186410011020042000004207000d100030305000d6041500440315550220b424a040441401426040002031080000c02c07503402014a09400000304d00f581001c03854203000788100c00800c3d102d042c0301d502e500a00d808510301e017001143c0c04400c032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 909070305 1250 909069055 909069071
    0xf0f09090d020708121921090b0f151207080604060e0616020c010c020103060b1207080705040f152a02040f110904050a0b03010207030804151116030210 67
    0x4075541e00558410300c0040c052030b80001000302e4001040d29208074209165800e10200d1410080c00b500d1702d0b0021020020041480c002c800b18805880381101458400031414111fa82462604543d02404030748040001e04108070105507415100c00b0020030494007004800d02000a0b103142042982101800c1d001c1c8800f80020031010358840e0b001c4411000980c0c240b9502c5400745400c11442082c81c40140c3c200c864299115803090b5070350170902d031050500042d40c0b5100c16644401e900100c5114982480c1c500c18440d03180d80052000342d011016181880ca054188420340000c0031039403140c08030002d4128074401e00ca60050301c0c0020000c400800481440c00340d0b203043d2604045889040c0d000320303d040510340c1c2e110124002c0440031220020070320315001006051100038540100f03032210040e566422107059a40a000404605020781d49401881c01c0a00f011094101e0301014104140d18001807214882540020394080c000e200c0c4002541c030031581001d0742404406400d00d80407070f18103400c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 909071555 1250 909070305 909070321
    0x1120e06091902060711011407050a26091507020405040507031101020105330402040f051507020a060c0c1a040810050f0a0b0424080d03090b04020f0f09 67
    0x20081c454840002102e405a0b402040b2a0081c007402801940000303003041224042001018400c92021041c5030006652401d04200d480d40e030408a0100d800380c00500d05001440401c0c1a49208445000101801d08282d8140700740e0380e1080c41d02a60181c0000d20500500c0c0f102031041d42d42a0760081c2051000c0c2c5042e142058a640319030008031400da00140c00e4914651051191600c5904001802e580c240100c44180b60712042c4481084103034006800d01411503103950010780010214440008115428403040225030704500405010804041c02401c0c00760384d80c0e0720f1031021201c0f1070901c40b42103601ca003405001380c00a178202100e8032100400745500035180340020021a29283c0a4582d200041074483c0241d40c0252400c01d2040c60907404122111516440004440c10090000031014409034010840000c074441c142070811719170720100b041d1032007444480c5c0c100072a4902080700c4401c582da41e029000c40500082e00422608015a4807525a05a401100c50707000f40a02c54074503200e40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 909072805 1250 909071555 909071563
    0x5070807080610091d0d0503090c0f0a060509190e060913050601050111030409060b03090d0c0c03060f1d1c03111608133206090f01120e 60
    0x8545091403152540c0000d1a2601142c8a40601031540458840e0362400c80950042c0c00502c3c0a8418400e481c1800001400c080003501c07035920251f1102074981c40c2c000c0d4420302b0401d5000c0614040e209880c1c040009030380d0361108074280c800320b0a000b921440540041419800520000c4403281407890005c200b00501800311841108200c03596015966600b24035240c101666000402961180740140b200398040c158180c01248410304481c1800e541c1c440031410f40e040c65110311003e100000502c07403040030034002110f01c0308090500c503442c0042907443c802d80c01510311001c0c124a54038440040703601159008041c0004014460705010b00c00c1c1e428075511002c00646a4250280c0c1604511000340280529240c00214000f018107090615a40003074a00c041d01c0f04850742001004030803552400b101600000e091f18680b20741a030a526122480c1c0c0845080c0c64800c01400340b403d400950b603441040300c81542041e5922602c0401d00300060303401301d505d41c262040b150300744038401d03404481c001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 909074055 1250 909072805 909072809
    0x61222050f03070b060d050309150903102a02100c0302070209090607030e0c0604120618030503041202070f0b1e030a0f061203080402010503090a170a08100b1603020115030507 77
    0xe16100d84521741040b2000f0403060700105035410522004415103403d030104129480403042041c9071440740f100281c189000c2c04613588003141e079182c6420b040b41b9840600411040000c841903000b6820f5140039544012041c142042c45d5140e100391042907100e034040d11340003540903000d8600d50520486194503074004840c410f00192501c6042650365400060310380400e000a00081d00d00341c2809410555003d40680a0b90459154108460a040c00030200b028180c0039503a03142d1a07040c01e00d014944514480710110071988165401d004101c1c00520300f000303c1da18074042075524541910b805030700340404040c2e10b0b0051804000c12282c4142c0c5d81082491607030307507001044040d480d8403400307074030008041000d40041e00c2c44000070015400b030001160015074a000729103a40d030507030b900c4c035141d4030342c440c12600d0414010036203602c501d8100e011160402850a801e80c101414060750f40031a010b0304184109840da00d0010509040c000c1d80091000180e13518041341e10303a200d0800d540c0d503007418 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 909075305 1250 909074055 909074063
    0xa0608091902011b1704060e011116140409050d1805030708070b031b030103050c0901060815091b0c0a030e030721082b0b061222050f0307 61
    0x400c109a080c4a800300e41e00d0500c03541616190210f4004d0380200d0100130842c40101c0e0100c01102c10800e45440380800f820043c0110355400c0b04d2240607600040800360404507c61240e880207081541c186c9402e65403006039000d6055822100d440d40c00050701402150f50301800600642d440701c1300745503121a1000888010402001c021f5640f0300034035641b01400d1150309060b41161500307100001003e0011904804030703000071102c050441c40c010f41e8552081c0d004844943c002d401c0b400d0300e4200f4080260040c220390604920324035004410803050300134030f940944688000350004880c61742d006500b8044000c4030300050785884001e240c06030340e107480041c2640031508000e014006850001080025205145020f03000c81c1507640c0122880f0300286812544070005200c2040840c0e5034043c40c04011304000c085031035070b031100f0100c0d508641f0548091030003280b0030006081b0308085109400e4002c6500003030600c00705d4440c400d101d210300358424000d105010b0340b8070310309100c1d0002018002403801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 909076555 1250 909075305 909075313
    0x60609060a1d0d15110405130c120203010b03040212030c011104081506031f02070f061508010c1709070803030405030301184208101107020a051005090a060809 70
    0x380c410050064089403000313000240003030800903c210140c1155480d012191091070900d0f440c0d20018190003070300d008072460390b40d807856403610300e40d80980400140a60410210320350f50600f40044a14840100068000d070070044545914403800c001f120300c40c41d0710700002c000c07541c00e028030018507601600c940070440c49100c00b80d590b44090811081d028220080007442e460818a15a0704490305060300c500750158280300a8020070b00e200c0805d4901442032400040c0c541201c4500c4490088130f0304150310310783c5820340c042c4205800008140c0784802c035800c00c0b80144e4071003056618103003054200c3c807000e00020051008000d800000f80d4141c540c0b820070313400c102054441c031904490300340308031004120b480c1d07a00d4002c1e2081c04005c800b0310780c2e001035140b0802c03024100e0306081c45c801c2e62140d210f82e8407079240448041e03581e201d01c1490411000c01103241152540000f4001d00890140c94451003580c00718840c644d02590441e064810040c2c61035038059a9140003038480f5004403001449402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 909077805 1250 909076555 909076607
    0x6030903030e0c013c030905010c081618031205071a0720011b0905150f030c090a080d080105040501080f100c02010605031e0106050108040b0708060609060a 69
    0x891060000305045c1d4030000c01c4801d601c40c1c0708820010031441d40310600500c00380c035151003100a10b11440c00694a0100c1e40026034941542162101c0c0c0410040002c01000c2c0046c503400c0747c0c1c04504092191400e2483c000c003109980940300d2082c0e00080c00c419011451281d81c0340c04c040a030062500030f00554501c410b00c41280d0140000448064000502801085400241410b50560580911000000c85884840c8070f1001c4600418904020900b0300d101001180f401d0f030038084020340c10425007401c0420700824204031780006030007082c0c01d040108055034240c8a80c05500018441c0104031514021181c0000d07080d1142800340f1070040341410004505c610b000134a8140300110344000b84280105540100020092065003200f103540b81c800004590b030701082080b1043c1101c4032040c201802103c038142c00c4030410f5120f141440102d03010000801d19856080750700014a00b0701c40c5c0c0c1940d48031b002030028402c180300c066009a001c10340000307032603000701519014a00c1aa016240742 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 909079055 1250 909077805 909077831
    0xd0f060317031510052709100e0610020a080f0d05131a0703061806080106140619090e13020108060102030f09191a0d0b040b060703051803070603090303 67
    0x21004640000303c441c14148900000d003004150715801c00300e14540344d1b0410000020b03294100c180944100d212160384000500189032400096801c000c1d42c401c03a60000d4640300300d9407014140244814424032440640b0340d213840c003d00103210403a03400341c04940c3e24124003541124541142580580c418074220000d1983c0c2c01d4207645406c659001b080c8480b084c9500140020b0740000281000f040613100c000c002242041c1112003440e020a004010030b81c43c3c18070340308908540c2142d225030314603880c0e11242246600c03103800b100c01189004120380d004004d20b032020341d8203121691204030403041000c10032211304805d401089101e03100740d840d1021070b15030000490f40da008a40210018240c00c001c2501549459071030304140d54407a10808003204d81c1c0704150f0780300e2940070808229400c80090788095109a1303201d01064001d0441e020082c035240030000c40c50034000c606004060020006001ca07983e4240c141ca08803000004044404450b03ca0704018045d120300c48088010030b050010144102b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 909080305 1250 909079055 909079057
    0x727030201080103060f0e10090201020c0915100e461e05090c0309061602030a032a030e12190302030601050f0406021f050f010513020d0f060317 64
    0x49405030364202c0300d41d0071500c943e002090341400c1c06414aa41d805800c20282e028000314808506520000030784c011280006814001e0b800305180c80740c0c0402c000c0141c040240c44000c0d4021a054450003801021280f0030307189040450241d43d4000240d0f6900c0743e035080060807003003100110f08d250700c0c1342c1d00c01c01c0800046003006405c1c074017180800000c05e120030030b02ea8006440c0241c4030f005007840c481c0c1e80d1010540070f00301610301ca5200280001041200c01c4100020394200038201e041030f001024112009489028005035102094ac5628002050462039500021110403d0650680341010f290001c0c0040600d0394014040303020301c086540014408600361103014070f003040113980d54048030808034000d600040260b81406070500402001c840c09501420140c1800d4005003c0150340e50b41030494100d020400e546650b040904101e401c002100381141150802d4a594242c0c00401d9501c101a002d108180c00b0468a03100c051012050710f6040101102e000c1d280c16050307088048415101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 909081555 1250 909080305 909080309
    0x313141612120807120f0b04150305010c110a030e01140a0315120c09050702070e01030c0e060f03100903020708030d0f2307080a02191110060632030727 67
    0x2c034110b0100c05440c0b4103282c12040440b0804400003e02c0d000c2e0b0f1000404503049c02e9a01c0c07c05846c81031007802080400d101d503003904045801e01d007140703174815200940d45e5110040e006003000300700b0f0381e8038a0380d900410310105840703040101c098440c44405e400400422280603850038071a1810000252180c150808070840c2e500511000d4140d4180220803005d010041c06900862041d6540003860041c820300440c0030754800c00c042d2007070030315000c062007002ca8003805183c4100360790165648030303680020b600074440c550303254040f85000c140e04043e401c010840c0d20a0120b800001540d120b819265488580c030b1140050007044603510074207030840b83e0f201404180414070703002c001050301940140e5845512517004040540340440d5103522030782f8400f800702a40e01040508914502c1d145041c040f414180c14140010480140b80410043c02d480c429148400891b4803642c000c0c1401003044128034010040381e84103940c0b403c00260082c035403030086c08554a812241c58241907145560540802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 909082805 1250 909081555 909081557
    0x806010801080706051803030c2401050d061d0105070f0206090604020105070816080d0f0f0e030306060f0708070f021003020301060f0818060403090501140313141612120807 76
    0x3c1240d0030a081038480d41c4c06015800e400000c1d4100502d05940c00300001c1c13496440c00d401a064003140881c1107085060122186c0b21500580030052049440f40c502c00614190044804201441060503448500100010241d02d0354201400c00040e540c108440003a1560705030708590b4585d5485c42095103d10042c0c3c3c000780011030030007108001c10040c07800b81c10030307100c002c90a00c04441d0f1136894000a034403600400e140e581e21054003004400c0750b0712448031540700c2c83c6400d001001020103a151240300060415201d03d10101d2044042040e00040c0ca00c182d42c040002962811642403d07494040c41c0d0340b040b031003007122000011000c1e11034002d80303049400c80d80f10701d0000c1c0c1e035045054810000c000c106807111103006103100c0038001c040001720b004600031340300d444106040c003000404010030741400a48a031401c006000c4e48000d240d40c2c141c0442d0308600d003000007015099510342410100240d100c400000307941c0100b03004007422007a40007140314005080f40d01c052203000303484214044410724 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 909084055 1250 909082805 909082813
    0x30e1510060e0f101b0510050906070c0201030e1501080a05061e06010c11032b02031c090f020d050d080a060501020c0108091006060c0c06020f07140402130b0901080601080108 77
    0xb04682c1840c181e4105813441508080318210342c0300044684882d801d42e0700740c426a12020b5140d24030010361280c5900060b0715009800146441c42c4050003103507000c200281055512a00007110000c14003a00c046212600122841c0c0d503940d00010b41d880440312420344860050002080e080e400d6860f0250880704070b600c840c4003607619140151184034040900f80d071604d44200f81d00b05203036018010076940041c201d12500c6645818550004840b2034141c0d40401d5500800103070040c111348441d8107000240081c004190881c0707500d445004e403c0082c5000350000c4952088904100010900462800199862a81607502c201c406010350313041c0d01c030b0302d40540c002400034003c551080d03448592010145045412401c1c1491041c0100d941d0340e4000030015042c0c50f0b80c1c0041081c2811541c0c000d051b184002c2c1150301a0303401c40380d01d90616124019400000402c2d829060305c0b40e805480e01c1c1c4100d818961083d070f590b000101850740c0150042d5000441030b01c000b4509601825585043c0d4100310020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 909085305 1250 909084055 909084079
    0xf010608071a1e1303080705060f0f090304090f0603060c0c3e0f03030d0c080a02040e13140703060207030305060901080d0c0515041209090b09040204020901030e1510060e 75
    0xf04510754040302c02904000b94500021000c54805001000f160348698024281841d11044600d50603001a00a40807240e0071b0050208050002060310250348405400046000c28819440c0040c01e2950009050740d0808000c02d050070f40250b83d40700280d004170061a920303140c00280f22400c4c8013454000e074101e0130302070100992070000c2100340e0005c10007800740440220110000f903d142c0150064407425502c46400300100c551006101d50480e007103140640c00d103818040d8030007680000030000c031248140320032114248040b19002c8017403886d001090380c0000c1e40b00e00701003011b580040020b40100b030411000c60101d080a1901034102c401000207807440080c605401c0340c61040e904000d90b41e80c0714031f002107031541e02030720b01c2c2a02070341c0302d002c550b020611084405444c100040c0e0016a42034904580c80322a51120079845030f0103941100c00599800d08940180c4c0100700c503079650000d40c41055030540355030032401e004501892075030308010120350340c994048820900503078001c0d4200c0c410400d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 909086555 1250 909085305 909085357
    0x403230406030506030a0b0901060807080a02030c12250509131109100308040f1e080d050313150f0b040b0307180603020d061b080103021c03020f010608071a 69
    0x103c140c2041380101900e4400d88141c40f40d612190007500d00240d503941d80c84081112200801030368000701950000b600c0c2d03040340350300040d40780c40200f444180200d101300411002c09400307000540c0c0700002c042c0e82d401c0811a800500c80c4000142c05082d02484092021481c1c0d403400700280800c05511020842604070078074240030368094090034444812a1400c03002c800141c400c405080030340a80701c001d1555078a804607011000140900354590124655800c1c0030342c04000c510240b4102c06420581d40d0b986401c005201880c0e00c101000d02921070650303080f00c00700340c01e42000d86100c02e0514103000c0c6d0b0300d4081c1004100e8460102c00742d4558002142040010394450b440020314003c48030014040b952500820385074401c007002141d41a50325040f46642c2c0c141040e0401304440d0034541200f080d030456000c5411401d991092068a041d00d19804c0b0405208200303072103041d1480d40c0244915907075500c00991344d000c1e9005016060384240b00d0340300f0001d0205e0688030060f14601112145800c0040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 909087805 1250 909086555 909086561
    0x807030f030623041104080312041104090f02090c210a020d06080d08010801050103030e0d0c03020a0f0302090915010302010c0f12080a0c020607020d050c07030c0905040323040603 79
    0x2640c2040c15125903001803c07540c00b0003c4918000c80940c04510310702458108801c48400001e80d8414101c244010701045000200795490740c40380d415441c450307031250709210900400034103030140e000342069030b2101045441c0e480b032140b841c808e6864031030343d4a90b2880c110031740c0a40410460300340350604285580c8006103c5990f00320800b0b8000600c0c2543d00d0b8600d030f040d1000d03a000704c150340d4004000d101105501c20300701030050240c0c0300208000c1d41595801020311b13180e18002886500420010310034480044940d1000b107500503c4591525614090220014405e1200343e1098000c0000110000b0f0042489200c10900351031000d42030782075500558828003141c4081c0c4910f842500003400180703d03102441c8144800344c5804401c1d2400103024816564015800b10440d0005024004c8950300001c1070300c1c2640ca64101580c803240702e03000c054600070042e40007900704403501c040080c4212490740510b010700c2c0265500141010b4607840c141d036081100500b0002c95000700f0081040e17a1003a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 909089055 1250 909087805 909087827
    0x11b1b0305070b04140601060f14090645150705030d0524030102070c0905180a080307081014150c010905010e061609090506011b030801060206070c080703 68
    0x401d041c2d00303012082e26080200001160112417121718035501992856003004060b0050426185c0800d86610108006000b04071820010304100c01c0460140d00750ba503070b1410b0302c50500c105030a002200c0d1800c00c401e001c103450000a07040c1d13240744507a0110001991429107242490181c000100c00e8050f8900c8081d82d80a5502610340340806d101460a40d034150103140e0003440005001203c640081e81c03103007242c221962a0b103101360f104210030700000e29020152012164250400a51641c507009c500644d000c0d682c0c2e490ba028083c6503100710410801c00043d50103400705075140b40c0c1da5034544050120b48502030141d00a603500c803802610951410814940450b000501e629081200f103510b600d080d1690141d00321001e945a012040c1c881504004980d44600d000304070203010621182c024101103a40d000f00c40c4515200c90008945134060f07082c40e50501251405d250100401d414000c15154081c00344100502500300400d100300d2141030b14480d80c54200710520702d4508540d900781d5141e1005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 909090305 1250 909089055 909089057
    0xe0604140a0f060c08060103062301140408010518010506130c03060914040b07181205010e031c06080a030f050705010603020a0602241e070e130e011b1b03 68
    0xd03100030000844409100b45018450640415000071030000581500c500034080d80c1013505c0c2100400070f11000008805003075007140b80280d19280b0340001256a1040c0b25801695074800190000701014150f02581c8a000b18038001c2da20302c61545211030995200b51440c1d41c0c003030302007241e0300b86c500c2c507550100c0c50801580c240041c80c01d40d03640d00134040e2002d0954881c80000740204010512200c0d10105500c54554a0701c500d6500040014881002d800d00504842407a8540644100030003540700d0b0070020862012240ca940f022540b4114040d0000710300c00f491800d02e800081e0445c0e0020f440410a030b45a1240078114030080390846064004800564096407a0340e400405a22412044c40262030540d0103131840040e8840c1c10159210b000740c2c80d9220350312000030030900003600c890f5036030480031010410805031035084048a08a2111120300e61202800c000303031880b0359917503200c00f2901507524000d200f010008521a82c10842509a45c00460b410300340c44004914264143c0005e140700e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 909091555 1250 909090305 909090313
    0xf0a1e050418062c06030c0a1e0902030f07090602010b0d08181003020a020c090412030507050d1a010905030a1109072001050a1515080601121803080a0e060414 70
    0x140b400108800c4c0050a00f402c0340d5903c081c01000b030b003540d03c00342562003241540245070f134090301d2002c07414a414900c42d421445d00d980c107138861080140303006440105031512080d5100d040403d48122101410b40308000850200c07200081c203a401800b484a008034001c0238201d071070355aa11405220f41c81111721525085900c422103006a440c40781008106625640c0141c4407059120b0103454884c0342500d46200d910204104400904202a08109903415160214140d200c0040958990040101c41001c1d10304040b20349400d481d032520640400b4509a82d807843c00740d03890060503100da25900002d40102c0c0e0500b000b20036030500d81c801a800048030719050068101c590640303c0d244c511181003116903511081072000341e2030280a90320b90085c21518151a07140b90408040131480700744486020700001d00300003040e03a0301600c545460441c2a060621003104001004070561401c030b001103010565800202e50748000c82c0c800d03480070402550040640d500d4607151440d80702e42c1a25a100343c0d200f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 909092805 1250 909091555 909091559
    0x20103091202060a0b040207020a0b0d0902090c0c010f061809020307080a06050a0f0612060b01031401060c0b151c0f0212060f0106082205070b0f0a1e05041806 70
    0x80084010007998606501500c0f42d800c10b5071928054035403514000c1d00c0703a80140070700b00241c0d8030344280e9402c541c8081c840d40e5441491010001c0581108800694271040750f200b0012103541d4030000b00340041140008000c03a06640858008550340750050940c010040c1e640000c41d224260f020b090201c0c0020112455599681d0149241203026a400c0b210241c03507000380b092041180c00303004075035412050103014240c10400b80003c19090240e000d404140c40303807152149a40a640700c3c4a8080260b10040b69039a125800a0030784031016204580d114001800561940690f0320a81700f80c850007840c0c0b00c03004640c0455980180c502c0442500c11100c4280200016665001e43c8424041500040d10961070a11421950405c059100300140850b000400c1507841c1122900c4614000440c3c0d001d402d05001c2c00c055260111581241d40d20039400aa00c4581c091a0005880c4090007035803070f1801c07100d61090301f60901da28402d158001c16014441030240001203d41214500f5100c980098190707 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 909094055 1250 909092805 909092813
    0xe100207080d0c14030918130209040f1b03020f22060602010e060708010b1207030e0d0203090f5e060608040c0308030603150405160e0106080105060702010309 70
    0x4401c9400a40c04945040303c0c100810221401132030b140100b20000c0d6042c02d0801c000300c0d00e44440c942100d809207403c00006541f45070300489502029401400585840c81c191a00c1c00c842c800d900c1c03098a02d09203081d00701030b0048241070043c080d20307070103490310340c101c0300d0a807d215402a03410341c000071003035086c210640d1084091140c035004004940c000316014400c6201503090103c00b070180420803400100601210340340d002200c080700000d40940d112550350f0a01180180909034031481a8001c180c40c120f5002e50010140c00c0680c0110b03801408140b0090800014079074001d090050222000000492115048071040c600315210151807331a100110418040c1942d0408114101e044c1d512118a003542c0c3c0e10910b40640124140005c01b81082c1e210070300034041c0c603c8000c000342000070005210745c030b060102d80204c85400d403158800c2c0c1031520f41552a4040d45c004a10307013402c0c40e00e000407850390629405048038403030b1310744020a908010a11100f9800703d82d0a80c1450748551300d480000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 909095305 1250 909094055 909094063
    0x509060c0111041d1003031404030b1302040b040b0d1e050d05041505040612050408040b070c09050f100603110702090a020307030501050f06180a050a0e0703110a0e10020708 76
    0xc0740d031091083e03641e505190410341c0118100c07040400841d403000811400e00340c208040302c1507a816041c1202c410708014030004130362145400003403429400d0801e000c9500340751007450301140c5c8200c8040c4a0809414240800c5a503081601540148001c5a802c042110215100000030f0345200144101c0f0071900c2da145030010310103d2030002080002c041124a01d041c100000701206071521516152805070700400f108940b00040c0304066880002ca4100146107040710006c0148141494582c900740c00c110020020310f104004c100c0b4100700004031038100e110b1041e481495604901142542400e40840c024070f40909c4841300044c080140401503903440020f14403030300901e60003607924a00007800038180d91041e032016018109540c100c0b10307166031344000d44107402d081d00301400140e0001e20014111440940c40145c020482c07103000b04900d0744480300720f031003801182c0341440301c00d0304071400c2c4000c0d2094150103000501707505018015890050000c5002c5c103858812074404035107404806040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 909096555 1250 909095305 909095321
    0xa0e01030b040309080a020109260607020109030201060f06080c0703030b221404120e0f040204080102070b0f04200402070515160207080309151b030a090506190509060c01 75
    0x20750076200300000c16602c500c501c006022010050172114140d5030002e008400750740a0580d00c1180c420318500f060050710301100741d03040542d04a50450400590290003031400b4081500103508046000c83c001c500c10b0308080c216000d07551584075581c0c8003031014185400100c4110708040e101c4440300c201e81d4800e60300309031066500c0d2101c5070304480310441104071030140e0251a40780c0e00c0c036800c01c80421800300501200e0015030410168041c135407000545a041001007484e0710030f00c0850082403140056000c2c049480c03081056501588403207026036041102110000c100707a1143c018004810205900541c03d030402034005400c0100c0c3e9614a81402c04842c15128081c0d640400c10001400e8070740f01828070745050000c0c02c3c44506000019441c1d12a0b00c1e8414014076940c4960a00b0540f507c0c1120200600509103030400c1c500701020b02e450b68000485200059400000840c092400c10111000c4429403848100003003007901060340d4070380058404980c030450900c0380c808a11020300072090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 909097805 1250 909096555 909096563
    0x706020d0518011a0108100e010e04061d030901120204030b040b040303060603020909041b0e090c0102100e060609070504090e0a021306030309120602041d0709080c0102070608060a0e0103 82
    0x41c507842d16a1140740c11030441680c40754560f041130740910214641110701d15010700b0a00e4203001d5aa20700c0c2954200341010340c80507001c80006000021034150001040f405140720342c1080c45100e01d070710f040f810700d04c9030f203055080b403500104948122580103400d90a036080d5180d5026040690b01e40390b24040c0d0408039825501115020104410150b0521644000d010711303040460401b4600c0012500d104c00040004000b030304541c140300320443e030002c9510000d103100c100c2c0c01550700d07044100e1a20380700e200500c036015104114103440b04403814022a001c41c00041e00610b03445c2c0d1281c0802903003d0f0050720b070605020081002040d074a000703005440048048500030f00070b9480c0c80c8103000e030165000c4500d903807061418409000280d408210181210301103c104c100940c201c0c203060b0002e103e5a0b002003000f1592010300f030001c1140b031155a200d2001c1c1d8a5602c2c66558400b6000d46540d4490394903801a00215024000c480c01480e405800c0203018003a1401d0302d80310200c88a501c4020f8009071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 909099055 1250 909097805 909097811
    0x40c090203090c04060501020303010f12210f1106010b030f1f1202090c07080306010f0e040f09031e0e060a0527090c07030f080402030313061206080309060a140706020d 74
    0xc0c02500713203402144000c14083c4000d61442d80340402d100791085080c0100340300155440341500500404c50102c0b0801710320b0126850440581c003401a1000405500100c0420144071044104038408644d40b070496500c9030341585940c0d2035905650302d144000f801081d961a040d046145401d100c5c00814002d008200c00e0450180318600422400320300c014440d5103101d1b070401c032903000152801e0590742c1151081c24131500c03d49401c002902c000c00c045240340d800a19004401210842540200046900a450308414080e2201c080440b45040c40c802c00080380f04030f241c403d49801c2c9980242610900d61a2041c00c2140d800054038007001d98400c1300e0740303031000c1c40841c20691900340c90035600002c0034000f0514054803179030050508291720240b5400d1241c03510025095403410300031542803100103030502c040c0548640014105038803280c225149903140c01d80210310b05074000200d4202c1c0c640200307a941003500401c402c541500082c00914145001070021a0008403280003400025402d64408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 909100305 1250 909099055 909099073
    0x3020708101104051909180308060105030f041205210a06080d020d05030a110c1f091a04020109031401240e070c050f03040e0405061803040905040c09020309 69
    0xd1464040300c140440c2445251400c0508840c0c0d40000b02c800710345041c1c40348265a542c252007081c20b4a4964020302d09103003031580011140300507030300240c800b40c841c1d2038001460b121000110340c1400100d4888200420304408a80800c4482407118104181444c0c030038503054031008070b42e050045100b121024420300c0814085660103d00442c2c010f410a04010080200b08a100a54031190300344501d003032020000c00708040c40e2064004010580c04881c4103070740c0d504101655903842c0746c0d048106800710004680850900b00900078442c14a0300540440002d031003144001c0a1004054401ca05200d0308403000000500e40e1450190050a001c000266803441021642c0c00110055074680880f00c00c42c2e0b061010b155403019075600a000d503d002d8aa00c195071500c940342265030031075030343d1502c000f14000901000c80390120b07114038450340c1502c5c082e8031604240701c15828070034031400280d0420f20003849510026400315030312a0141c1054000f4a960f0606003081b64420742e00711035590000c02003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 909101555 1250 909100305 909100319
    0x18010e01140105030a020603070503101502030a02010b0111030703200609060403083303250302150901080105100c1a2706061002071d040b07050a0c111903030207 71
    0x40140100b03000d4000c1c05c01c1380b50340d6000800e0b41c80020210f0f0107200002c808607200e20b07201c00040c0003800700030000072000f407100d0740081d580fa0013a10200c001503003010300759881d03540f01b102d0404c140ea5280e001503040041e15038003607503000500480c070021505600d0b0764000f440010040306010708110809031005091509004100403401070880d40041044969100914001284043c0310401c50900c40e903280e441c0c40c00a403c00c07803420b0307000103820084080360300200018100c07801141c1c803c680c5103c0354008c061084407a4060f41d001d0342d012030f00700c400402844c18080090b62150180d842c000c800d42c10103a80d07503090301400052002c858016402005454110840145064013204038020a8482048ca81b241d4455004201e2802420001a80a21603001700a080c01414001d50325501d0550821280c0f000b01c80c0c103c4050b5450710440012401940c0608100c49240d00706a40f5501080300c01d4031541881070140b488942c10078040b03039110340d01480c2c03070150f0700107107110380d01502c04140740c800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 909102805 1250 909101555 909101591
    0xb15031801020307020316030e09070302040906050d0b0f10030813062d111509011a010f020c012001020a030e07050102120d0c031b12112118010e01 65
    0x42844010781c410424000aa81c000040c1d504841c621003280c01000301d40d20b822102c00c030284400c1c0b9001102d1405100c4407035015000381c03058807004e41041140c190b8030010403005c04d0205002900c464126004502059402450280e00c951420058a010395480d6120b150310350192400f1810401d01d41018050325505c0b01d540d140300f10b801c0303407040d40002c0c05441c0d8400803106003044c3ea09008813102d46484c101420b214400744100c2d60780d441042440c0005129002e8034050f8241440c00492440c501d103190f000d4a0500e2460149500914908030100d006503954036003552008861003900044140c0789800f40002c2c9001100f551303000c6201d032601c02c007042c0382c01000d82165043d50802c07555610680c0c1c48406036100920701c07500100351142c1c010344c143c00510041c0c9a108070000c0c215520f0400b550403206008a40703c000d20100704100c00c0a50040b018012008103050000203c420710944103c048501504040d8000744d034010008103000442c00c4880c1d804203c000d994480c41d0000c44070f10b46c00c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 909104055 1250 909102805 909102841
    0x602180316090609050c0307030b1201090506090d0906140a09050603042402091503150406060f230316030b1009080f070b070201110a0c0b0d0e010606020c10030b1503 73
    0x24006004500b4550301c83e1b0114040201240304050b611070001ca22030382c8410401030502d1407400200940d1100d414965229001180c40b0b04181c4241c17030f56a1540f5105a002c0000c4541c240e41320008942d1007086c84903580d01040b0b80b0b000300314054202240603030b1070500450080303201c0c51051413036981c401078603046011090381c1c50310b0080c8180b00d200c1c45030b191118003e00503c1462b01407690307a074941c03511a10269000081e560818509034000c1403458010203505806a241e8484c0c09450004000c00040883c0c224a00219424188089220b03112000c200c1c001d000b41038180801c0c01c2900c20046a0484044200840085d02112080008607000d101210300e03001000040c20010341071648005480c420900000d04109a0a0210049880600c020805140d128a2010052341c0d651010085c5070422910054801c0c604040e0407040d000c148986030850360301741c01900152006804024a01e0108007840090644032003c019066031f85d410b0842c0f0141410301100d40303a04000000d242481254 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 909105305 1250 909104055 909104069
    0x70f020c090a1d060f010e0f130b060d05120913021e030c07050106091b0e0307170c150d0506012618010c0e1207050d06021803160906 59
    0x65045400191140401194845140b5501250ba0075000c501d40e02460700720808040c440c02244c0c18003605034a002420f030f040b503a060b1044009030b10f85204481c090f0300e003a41c03440061034456800c000000d0612055542c4560000c04203c11001e0580303450b41860fa000812100e60040000e40865615080040e40280c00070454110304040c0c540300031141c02c0860742504900c170782001c00004c2d070158003c81283c3ca1541c0c8038009000d030301e540e044028098000300c04000004a803018885036210700c108032054102400600401c0114906800c0941c5101005000c0d00903004100c50a540d0340c58807600c0300c2ca10a803079100381c1e50313645031103042004980003d402d20341040644003050003010b16401d000651141000e00c9402b0a4446c008811024540c5110300c41d070650818607140c0c1d142d40c12a503040036404055611616010001030840c1d02c60301c140c002d25a210440394210f82c04211164058040c0681071107821036800504000039151a1508915403500000c0900c2404808281e0250900030184 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 909106555 1250 909105305 909105313
    0x3240e09030f0d0f1506020105100e070807110c150301170601121709270a02160303020c121b010b060702060a050d0f0609230603070501080907051503070f02 69
    0xc101c2140702c91046052203409261140c01e10590504182d10500344081424202c2100590740e65020340a80000c0b40c2941c512030401c0c0000410b001c0c18140e031480f030403860b61250051380e201c0e0419141410002d05c0c2c21800e218004078038145845100d0a00800303e55016180c2d16507251103a208501e010100d90305101e42c01c00c600400902c4c000b4418052079903401446641c146070a8014a500343c01240281c9a101c1c1d400824402008403001080c0700341e1001002000300e030341c2c62904a0059100f0740d5038202402c1c00c01c40e007980110f8882c2e4080c1082c41014020b4a01038083c0c01c0481c4aaa0046004611801085400d001806500740b01c0d104803000195203250802015800007002406116002c20a2250004004850361344580c0415040c10b10a0343c01c0004c2a111b40342c1400a010803d011205030b0007a000c0c0d503100c0540a40e03642d100701001001024400e00b0680111030707228000e000c0d4005071280380f07804500c0303644441030b07594460940300500740c803440d05460003030450040122040035504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 909107805 1250 909106555 909106567
    0x607022a010207061112030a060302040f06030201050414040902090c0901020f010c09150e040c0e010f18030807150e0309100e03060a1802030712170c031903240e0903 73
    0x180100fa150211003071801d00d0100703c0e20f200e40460501c1c0c08540d51016042001041004442d0254442800d403402034808122044d080b00041080318900c1c00080d000c514244030400012150a40c10700324a68081c0c004240007601e030707000c00e43c420307001c0d10302d885a41404246040c26590421504025114860083c0107003d203101010f0f00703508040c040c5110122028080000c103d0040c8520b10301214041c00400070803c5009000780072801494107c0c0c00100705080218a441c4980922005041840c00010b1601d00d59a03030101903a22640080b10001c140403d10305102d0800e22030711981e01c007540c000d181e842c908002001a05002d8032002000d0022282da07504264800051841d40301d884610f0005481a150107865103080d0b076408003d40c14803c04c1c0002c501e054500100d0503295104550704500005880b20800c882d01556104020b1030340140408003100d9079140440c0d5030901c95003800500303024442e00042c83c4095080780351181c030303c818508102c01e010344541294403100020156050030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 909109055 1250 909107805 909107807
    0x605041b030c18060e1503010c0e0a0506180d0b0118020304031b0203010e0307031206051c0305070305040509180606040b030a02010c15050f0906090a030512070309050607022a01 78
    0x403415000c2c3e043c580e481c00d001d19403104402d6002101030452417202445518002008112922a03081998040d5080c0784185040314000e060480c0881c5000700140d0086c0e04150501c01d8503081500300900d07031a00000c01e640c00b611080c40080303c0c54022031015155605101c80401400c20b40074072048c0d03544c030400411000c241d101e90702d20005048101e1040b4010004d0001901402d147c4041403c613001c0052588105070f04036880b054440e420520600080da43c500400c220109084030100d9550280c00c03008000a00c100009d1521a100341403c9052079103031400310740e01d20011504510340340c0c070a82c2c442500aa0070007145502c4181141c00744a80107880006caa00d54482040083c18080300300c02020400031400c0c0d003903c803820f100038100510301d002c00340410450820b490307618090240f030011843c5111701060751440b660b0140c071928507000700c2000c4200d200c0030042c00c04042558904810002800a2190368007544a42d401401d03200500345801c4030f20244490169a003aa03800d101c00030603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 909110305 1250 909109055 909109073
    0x307030803070c150f0c1701262d010f0501180b0402041701091403030402030601170a020a0b0a090b120c070f0503071b17070b0a021203040605041b03 66
    0x90100c1c43c0011480307542d4a4200c981c030304011854040e417820240601e48564003a407020b01c0d01d0702c59aa4103104202c990f038940902e80400c2c043e01d004e03114501403420412072804680340c8084100411030720103480c0c1034048503190000c0002422440038611000201710b001340580b521340707c4003520404c5194500362200820348100c0303404103011030b182c270030000003035071298140c3d00100b55070000d200039420b154110074000c0000081c12603e0070640340d0002a47c0c800001903a1141d43d004d80207040c0c0741d00b03144c151000501c480344001920300c291080400140c03901d0346403100403c00d046c4103980310707610498098032072881504404040103092025400000741811140d4100d003c0100040c1d4070500d600b05184203c110f8400500b191200180c10400c021854404009d100b0040c1000388071103485100d007410303030348070701c00e40c44419400054184040300101c002005c943c61a030040724102082000c24200a030804c50b004e0311090b58a2040005000c4984400744840a010404414032410b55590802e5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 909111555 1250 909110305 909110311
    0x60308030f010b1c0e0a170c060106091518030f0605040b0106050a0e040f02040512030d05070806010503070807020f010603030e09011e030b130c090903020c040605030c061303080a11010b0307030803 87
    0xc04e8841045040d04041441b00100313058000100d40001c410301c0b40b020440b40e01c0804450440d01c01d039800081d45921542c2800192421240b0f460078140184034100c483e08035507074440850000064002001800f400c2121a90740d12074500814140350908001040c9a4142e002c0310a10004100340c8011b1544012015400c00c0119000503d050308110070700001e010300e402103600403000812400c000301d4004041c2c00001301c0c0c0101807059a5540404448081003511010301040060011403403880c09121a5035004103244100c4803c40d070000b03403550035100590f2003600450711802d01140941000c40d489030140941650034980d880b84081e542004013441d02c0040e28a0741e9480102e81030b05000c210184c00280c110610300301c101d49031880e40c0700030098044220054800c0800c0c100b0141403e000d41412220010060704c9210120700c14001554841c41d0207070070100d40c441d00440002d408a000d08008801d556401e41da81103606403940c00c64600e041d0a52017a4032107a0704100141c0b542003141e0b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 909112805 1250 909111555 909111607
    0xd120b03100203090c0d080c0d020d1403070e060307050417030403050d081306060608090c0411030115020c030a060c0f170604020a0e0a09051b07080702090402060d060308030f010b 79
    0x43d480d594609003a09026444100c2c0307a0200d0000030b42130070310440001070030544104100741c4011810080003a6542c0321124805800700c0c0c0800400b040311001e41c4060b541c01400c90a01e8002d850250340040d42030350045452201084000c5803c0c40f05c40c1d10900b2200707405864034002c62405046803a040e942d820034500034001c003c1c08000003004420844607106400340d0080c2e040c01413603100c80000e08120400c481049041c030981101501919040c080c41a80000c44610945140d0a05180c460100080450141940324004901c00d00781c83c1005400d40c11f5004400010b6441c40044005003185090b807100310400c4002d004401007180b41102403038018000315030040e52500b800c0e00c151051b01c20a82c2c0c440e4072a041101c002080700e915007015200381030000c7c0d035011402c81c40540352168098102c01611008080c00b043c0c006041c000c2d509500140014030160400c13520105400c02d541054204680e50342e40070090001080380800360a016042400609040c114560b480340040e802c18800c0301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 909114055 1250 909112805 909112807
    0x3200108090c240304080714012c1e070317120a090c150914030f0c130b030d030c031523120d02071d0105060715020412050d120b031002 60
    0x2d42400282d01c3e25201c0a041041d543d07200d180034245091140c012180036181040002e010240304c6506200b008200039801c81003403441d5003109103000300c4800511140d41281b0a82003c5034404545601419400d000d0000801c034803800c61030103580c40740d1501080344c0954410700440c8180c51003501140c1e4003011036a0006005002400c00e8100c1c1039580d407142952407110400c1e1a0125440070b41201900e0a41000c0c89103401c048080c9513031901000304802c0b2940100c100081e061410160855800020b8400410340c4048040000d0418107a0031170680840c4d5a540460310068050140900100c601c06040082610f01529800000203d0003c4540401e5040c07005081d540c820b54201c2e46081100c00f00c070150340b030145d0040e5541d04140a0b10082224028415001f0000032244a050740c0014026600b03100c09a99a200c103495070007000c8041075000d01c00030408800140f0003400050054000b4468050518406007071210340325034150406040090100580c0c8000400c030b030250520804c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 909115305 1250 909114055 909114079
    0x71707082226040303090311180408030702070501050a171009020a020a1a040f061e02040f03020a05040c1b1a0a06230901140a170d1d030c040b0d020a03200108090c 72
    0xb5989c011103030390001c01e20b1000c0f0900090081070701c080d40c45651650202c1c2c07585070725003005503182c0c061401d01000180081107270b0440c1c0c4049950082c4c00046500d03400b41c045480e000f0b040142e0300a00010700059015a4185042c400f10f290200c141c08441e0f904000340d41881d4035005a8102400805005240c0312004111200c48848401d00482000b070000c40d01c681d2100e443c2000074100c2d01c000da11540c240c1c00003180d54541403081116848440c0c80d006028105001007203846400c28a00740e8a42140c03014040b83c42d204c401030103202c4c80500b1030005000b420459000c2243d40204401c580560301c00c000b51003a620307100401d0341554040d00c00e086035184c43c02e0024081d092a5041110700103400d10050021000000d401245805142c6950a00c20740010369554040040c1c0807141d03041d844001c40c4407481c10160b0201c0399090020380700d140750340034035008100900340e240c0c81114109400e206041d100c0801179400c0700024002d10b03104605060611031240e0350b80c2407000c0d41d44110181030784 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 909116555 1250 909115305 909115309
    0x50c120d0825050306181906170d18030f0308060109150905040209041e0506030f0a030801030201051b2508010204060503150621060306071707082226040303090311 72
    0x100c0101b00721103d80c400181d1403c140344440040004e5501c0144d00e08209003c82e40301e1130441c0700c210404849000300011141d040781100d060710461051040c0861001000c4080b0b441821403c541324041c2e1a20503460405a000500e10407241e40008500341281b9525003076a507200c80792320b0464030110340251b00c032845840041c00401c50020030102d118021442c1d0010072401d034011910900040301a914202d00f61680c041d10752814150040c0000e4040d00140015070290b0041d09800c800203280020f4610040e41040c5400e00b0400d00790028070901c141103030020781011006001c1d0003000001c0d0704141c603042014105000281c0500010700c10f54049002581307584040d1443c9910f841100c81c241503a86019080c1040103071070103030081c02600006060b80740142d0348116070000c07104c68042c0c0c0399a801c0d0700700c1c1c0000e00a04a00030802280c003641e910420341c402071040d20360040c00e0025162200703c00c0c2c00e00100400c07504442000f002d120420210350442424011aa00185000480145940 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 909117805 1250 909116555 909116569
    0x103081903020d060e04061a1f020a02040e06090f03040b0a080402030a020a0f1715010506070c030b0c0c01050a0b1c05012004090c09140d050c120d0825050306 70
    0x20301840d018540080005c4140318100410b008502884003080a01c0901a6a150070050803c0c035a400504d10a0f150508942080000000e24014070507600700d800345034001810360b031908012000315407001b001d200c200304081c040240e40e03203581c1c40110700e0b141c580341108086001b9010f0344020311290300c1c000703400d45d14103005040a5030340c0101002034598031a042c100d9000301e41d00483c021001240c00003400d603100000c40d841c298800542c800c90710703842c150400803180d02101c41102c01c0c154004000000482c070f01c0e1850b00612494140645801501e9501401c450780100702400841c01c00480800c01e481e8842e2404102451b81d04038090700c051410141d0240510b424074201c040100f851450820f14040080c00550745840d8040c803c1d030031300540c1185c030300060b80110300d1010a203450b07101032880c01100c4590381605c03a806940030100004001204204a4034803e038890f00b240e4a40c1c421543e1000d5031680c170002210f014495011511008070080d9949001c49040c42400030100d01e007565141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 909119055 1250 909117805 909117817
    0x5071406090a06031b030c080a0b0607021003050a0e0a170c031905030610032912071706131a041509110922080d060e070302090a0e010308190302 64
    0x501510b51a0342c1d580340040007002d0713aa0300000c0d125030b12005400124401d00079001c804000703079070740619034649001d18402051131103541d65020404100640040e03d581949005056803030300c0000300c40c078120b030444098610f105010015070b000050074900281840f4903080707401e4a06000380e5111890050741a245114071402242c0c41600000748104403584500214440c24041d43da002550301000300a6065504041c0c500d11074482c0c401d0407071a140200c201d40000034400600d00700b07100009175111802d0491a8005100d00c1540003051710503290100016504203482c10340b81030340c0780c12076125400383c8000090b000c03441ca050303600490107002c1d1580f1040c5402c207403030354208483d00c260b142c80187d815004800346d0203510312900048203034a07030203821020801c80740c1600d07502da03030070741e03100006544070007039143c02c2e10b543e0640401ca103104100780500c03502a40e1070041e41c9041d44820047c03100c3c070540c40381c4003012060780103100140341e601c103541076003424903865017030060030a0040c0d01030b0243d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 909120305 1250 909119055 909119059
    0x114270d0803010305070f15120e121606060e0603030d02090d020406060c021905100e060c01022d071e050f0d050d0b0306010609050909070302060f09090f040507140609 74
    0x10001006024010405104480c01c129000010580d9010a08100d0b40303041d00708c0010850b038804450001d42079811541d81c0300720030403e41e0300c520b04d98524242c558110044c0b46400300541c40c4038204211940c4202d42c00340030b04500e560b0203483c1c444e0000307035070b40b1620700d00465003070b00890190010b48806460114482d40100140505a224407004089203003c0a081c1d02c9400f40e122449808294000c12809845020f00808605043d541080d100341c040040c0c01d5400c008104038502c0306190a10207001001103170134a02100103004580704800b0000d45170110b114000c108840d45c00100c40d069881e180d01c943d804a0f004034185130910a003000c0c00400800719602a02102c0141542c4c40340060081d500310b888200318099007242410758840c0700b40100310202d22a010140041e140c40300c09281e200c042401140d03016900c03a03010540d40e0f001400c1d082044000410070701403500d047c10900d984501208a04111481c140c0c4a0543d036240d41d200700700e10324002d0820000d0a4a514040306c03080f00d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 909121555 1250 909120305 909120307
    0x60305030a050c01180b152e02160e0105040f2d0606030b13021b01020f0a0f030203040b0a0b011202130e060102240604091b050114270d08 61
    0x14001d00504182e02403d081c5405502c5d0203e070700740340d00740c143c180113002d50048102c0c1182d43c0ea40060714032080b110100f06034029500c01c2030088003150303980802c2e1840e00001c0c0d421030003e003490020780307490002c0240820a21f160541401040d502c5e81c101390440e03000b11030105e4080a160742c4800113051444948140e05100a8034890300281c6514500c4078266440e02044543d40c0d5410450803219010038140c2d00088071301d098100403038039030054403d400202014100800d0850f81d118226804105024506500400c01601d00d9400c901c001b810084541001e40c51480c26617150404110010710554080790758510b040c4141e4440c4030790041d00505000c00310741e904a0441603020142d02c92040e1810304501d0000240f040d48080b0300e20009180c1d820003d40007205408804401c45401010380703030040d603944e1416011443c503600e600e19000141044003805800c0c40e00041004107003482c04180c98004201c151410241405400500c01b49070070300c2d10040c41407900090420070044405416660 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 909122805 1250 909121555 909121567
    0x1e0402060714160506121609120c05011403012108091008010e0604060803030c210c0c0c10020307020609030a1b080601050405070c02100c0b011409100b07080d06030503 74
    0x2000120342072050120001c002020f139440003007000300d200701d005102004c0f500e140070400c040c2e0154410003000c182801c00ca44c4003615500b082c80000d41003a800e540d1107403120401c209550b04006014844407c0000c1280b0319030400349580d01281909a6510307111185c000c10405124611040d59400c44000305402c2c0300209002c40181100002c4c0941340346c0005409c0400d0307a6141c00d225a9080381e21941c055411a6151142182c82e9041003e003008141b10000718016400c0c1d001107030314494840214850f4658184010320380c50104601403542c05110707001d0300306407000e8000003942c06003a41100c61030b0340d5070404000b10341840d0404200600e50050003040001030046120904103550ba044100d9800e6a41d62003044155041070340c2d20800308401076441400360511840c900740c1410581003060b080003042d50307041c1c2e020790240d000d00c00c144c120444a10b446e00d00074400d10b801c80101441c2905090414000801621030504001c04e038020001e40302e4403900070741c0c200b00b000b95044019a0340703c0ac = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 909124055 1250 909122805 909122843
    0x6120f01111c0216080706020c070b0712020d080c071a01090b01110a031209020303191101111903200a0f080105011d01051b06130203151e04020607 65
    0x6004500811101802c2c0e0120a0920400384265110030711490140a44e10f042030f1503501c6254406c40050b600740c2d070208101c94540c1000c200b82c0d4001d04005100b10307034812990600070603e011101104045402500c500c4044c00e41c031101d00743d0480c518142e866520f04c0146016070189a448503501550313110b49000060341c262640c000f00664000307880300c80d0329119140015440701842140100455162106031010102035804110440d2000e01120b24080b44c0c0c6015114410300461000e0000d80711030b604d150344000030f0041e4000c1c50001040c16042c60160320843d000401d10b110707184209030b40c5541a030940c2244500a4041c030002e1298159030320046c0e2001031004020082000210b4404400010385502c1003482d03142580081c1c8007000c0c4000398000440f440d6001c103010a0000b0581c98040c40c0100c424800d8500940c5011500720b40312500c0d04c14181040b50001d80d041d118540e140070020f0600c4200564400c425a01c5030000040e40c2e1807000440502074250058250402c21203109400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 909125305 1250 909124055 909124057
    0x1a03251205060307030501240b04080a1e05060406091203090305030609100b04122f04050702160f0e090303040209040308130b01030803150402131406093a0b06120f0111 74
    0x115115480b41c2c03441d27034540301c040c8114810740c422070300c2d640d00680c200800b2404603403e010703517a6141480400002e410f500c0351403800009076019070700341d5075400c49481000301c01141e0041399105420b040c012014180c5010740315000080140f40100f541c0400224101035030088103003e80000d0384081d0300c41342c80300740d4508103100304541182c0f910000c1100003008040060707400003415840700b41142c1e0858100c10700c006000c021300480150b10419609550304c1c40c0d109007040c0a0414001c980c00c0c2035144c040c03c40c41202001d0135a4400b40c0040050101580f14901c03405d42c0940c05007003000d095101c16a500a000c0b00b1064080e02400c4a140003004002540000718003c0c3e0308115040902450030007088201d108800f00b0700061202000204070700119210030328a54080103145034105024040844c41045a000003414002600340700b045404c01d0303100c1081e003070b0310f403144080741e040301d056845038502603000c1d07c600d02c18440b190705003104c03010411107511640381d128001d1140d002c2011401c40e207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 909126555 1250 909125305 909125351
    0x1020c030a0c030809070f120501060503011805070f03030e06130324140705041a040306022b020c070501030225060b100c0b060103151a03251205060307030501 70
    0xc1903200869035116001410310141d400003010f0010700341c9040241142602c0310b0070100c0d4295242d56001540d0380c0cdc207216502c1a2090321000750304044292800c01c1c180055034000750100f86000300c0c244046a40280e104106d40d10030b442842d0745091054401d00110315541c030081000300d4140c01ea1200310800c10504410411600040c00315082e20000d55803000c0045440a001403000e000c10440c3c3d20469040441035003542c2c84040c5410786a444410a036813007035401e0301c2809503e4010349802e10740d1100307041441072010011410a01810036071612560244180c03410985c01054051900c600600e980742020080307407043d040d075000c0d842c2000180100d403440360300c2042468003c031039850260140b4417a86a020041a041e0b5481000560040c8064001d1048002c429840480c45c00c03c800340304200f02d80c80c800b00711b849190001d02103103440c890510346580c0d2180046004443d541104041e0b4000318616800309041d516100400e181000d20b41c0090020760070040000c2014400b41383c5029 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 909127805 1250 909126555 909126557
    0x1060302040f0806061f09030f0501151e060305040317090d02070501210c05090306150a120203031e090d0305090f01020f07030b0901150b21101701020c030a0c03 71
    0x4078441d61500c1442e104e0408131103840e0069007184554110a00071104031005489604156960907203a454241d42a00101c20846541e0743d500c003800061940900d1500041200c403500d100e140300c0402c0d081048180d03610643c070902d41c0780c00119040502440c0c600350b070403c1c0646e0040040c505055000d542e00e0b000180b880250144180100321035214040c038003214220303c40a5008060000300c0c050003001c0c4081c804041000a0200707156503034090000780d02907010f42c81c0c000140e15805007041062341e210744c420410711007486580401610b022007a40c070011050002e4651001d4030103185038140c41b420703d0340d60340f0884440e0980101174000c2d02806551070240d628003010070b86480160303500c856554481a0a42c0800d00400c0003555248040e54051943c03c00400c002800c4001c2e4030300765a9903000860b004002040316141c8010070f0300086080420010603011509207402d14100c1c14044d80031b640f6000d00c6502d409244404250100c401003400a02101e40e24a03c80b000104400a5078100310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 909129055 1250 909127805 909127829
    0x30210050106030c0e211e15070914041b02030a0909060f210204020a030b01120903140a09030f0525060516060b09010f15051e0f070602030106030204 66
    0x82140307442441035448140054445c904076000300740401c56000c03c0350a16460840340c0501c1b41c00c1c04441800491f41452140400c040134580841e00c25060160301c501148070703a5041d108210200d58070548034812603040071031012141c0d5440c00800c024200000e0f901d95044003c8100c2d040c41d91f4000700410301640e40da5070b248036654503151040251081441415a459085002031152007800440c02c0000c1c0448030606021581d180c1c0410103a80049414901280d82d801c040141542c21400b00c2d040e503004280c0c104150010b90343d01030005138442c580300c0c485080108900040c00d003e808148080c1da080101d418940415140031642d50b041000301383e074420440000c0c0b021b4184c2e400110000d03214a40c13655400e003140c41c0075030001c070403d00c3e20070b84016444035a18640e0380c4a4849040c060420240c4440c411421f1030701c0c1c05844845004d10404211003002121100000390485400709400b6208056582c08680450041c5020300038010f040036100100019000c0d400d41c0c002d10403200401000c0d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 909130305 1250 909129055 909129059
    0x60d0b042406021b1302030702030d1404060b030123100909110f1005070b060d020d0309080c010e0a1e03080301060903060b060a051819060809070503011b0f0201180302100501 77
    0x11084c0012010181e007102c41044d50a01d48003003500555030021840c4101c03070030312a556039031f14169064110700d900103989180a020500c036041c0074205030340800b98000d216000440803031503842c4105502d182c080c1030310b9801050305070f81301841440007085901d906102c2d9521500b032030b030704099118907540d208540c011103100d814180440d61410003141c07a00c130703542881c2c1603464030300703840030300a01d12036002030002c3c40c48005035144000303c00603034066526125240c1c00c0c60301c21072820315020026814842c82100054696445140c50070541c0c501003001d040c005949407180c0d00c0c00402c4e4000400c5400084004566164000503440c1140e008a506000407000a02800b5443c80380c046400002a82049000782d5000c0460400045500251030342c1c10151a40c80d206607204911f0f000400042d034080140800030004119060150004034000c00000d1190042c070005040f40b1034805050142c84ca4000307001500079401100c1e007007500b0001c3c14284500d032800940b13a000010368108001d10b85400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 909131555 1250 909130305 909130333
    0x20d02060c0307061b110714040609061206060b1309090501020705012306061c15090e030a14090108040308151827060601031a0316050909010209060d0b04240602 71
    0x11b080042c428400161144609210f0702c40d000b0b111892500d50841e4455400140707141d12441040c2c01480e000c510580145414940007058600e661712016500c401404402030829100c620402121655500082d00d05958500f0078060301a00300050700315442c0582000320340040c1b08000007803544045200b02955207a00c10805c071406901c02a2008061310740001c462003250741d0120f4401c2c02d8280864407119500e414003030944009410512441d0400302c1c150b60102d400c4081181150344105002d814003070b038140020514000240050104916140030665403410340b158075080e030601501d1041c0e0320080300340c050360001c0144d91911a00038107c5280743c10300005250040e480041001410040d00c91030300445c00342140c440c0f514090000c1155030003c6d583c2c1040695007840e02007038055842840d0801300085a00014070351a1350340d0040255240741da455000300c82c05101141800121004018040350042400e50803d1445582001016699808244054040b10100d500701c810101c49104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 909132805 1250 909131555 909131567
    0x602030f04050f120d0c0203091905130615030203061305070329010c1b0b0d1a191e15030504050c010c030912031817190b04020d02060c0307061b 64
    0x1340081103c44148500d90b81c0c0c40d400d801c903a00d1480203104803400c1c50400d00000345483d031498a4640800c80152041182d402d254031411101d41003031764208141c03468480120554105100313240200340c1d001002076420760f80c0c00b0032040201c0c00c8000c02c200c68a4100800790040071500881c2100340090480030343e0300c1c5601103103001c041030180e6498150012543c2d540401201ea80b03140c02030301ca40300502250b250400c00180c00c8240c0317861004220310b491290880c102c4810364001c20300402c03080d80340d038010940b0075404a04492a400385000c45070841e900c20985540d20b03402c00c1007203c04210342d10303c9066150b08107078000c1d8040c809454040c944c110047d15080c41510b00200440d103014001c000441c50000546015030003410144101c0d10070300310341e00e0442c103103420221105940c01c0b14000c2040d401c200a00c0c0e1001042c0100008011603228004440c3c40100024400c0419104c01c90031502e03039000761480400c00d94112034503141645800380c080c0100210f80354444000323034560680740c0c0c4161 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 909134055 1250 909132805 909132823
    0x18030810090216021e040c020c0a0b03310b0a1d0c0f01030504060f0905161505040b090a090507120e010203010b07020d051f021206010903051e01090602030f04050f 72
    0x1081c000a4810b1a803d000d024080c03042d1442c81d03001c20820304d010300e0706c8502803803100102c0c1d5400f401e111042d04082150401181d040990310b5007090007040011485034440d100c0e90780084201003108000b60285a461071001240100180c00500620840c954190441c0424202003420f200c03440d090701a60940e2004003000003a40990341c41c01c0d103035183d40280e00c21900180607440c003140e07014001c090003042d2404d6407c02c550950040c0c00d8940b032520400e00d200042d0903c00d041d585031400c50b003401400c1c0c1c02140183e18485e000000e083c001556000f91105c028207051500b130000e07251240c000f800200341807034550603942c100303801d0341491801031007240c0c103903031020810505102098080c046007200821049500c0c0c808e48220b102518281400c074140d02c0700010015030303940c030740d000081010940a403405040c410840c1c414400180040381c8c07490355030240044030058140c8486894090328220002030941c6100205100280d04c0c84d807801b070711583c01001150f4030201c400e04043e40c0c0320700311 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 909135305 1250 909134055 909134077
    0x405040c0e011b11010f110304030f02010f032c0f06010b0a0e010c051b06070b190f0504020306010b030a0213080c0a062d030204050346080d180308100902 68
    0x307844c0004c1c0c6903000361200e80c0900070528020ba248000d20411a00e164000c0c0c000350390409038030342c0540440d80c0c40200541c808402e03180904c80b00000e150102c0d0701211700c801d990000b0f00c101c0742001d440f4400300f107008031825202c4122099969250f102c0c1070260711001d0300e9000644d0b8110241c8040d4010703116a902503034040002d041011120b01012044100203202c15441981049140c000c00e003112803081c022a041011514100040c212800407661800894002d0030b0900e03040201681e00880c105044400d01c16015030340e590707104400002803003544c107455030343c141151000c01c0400000501e030b0400c101c01e540c4a50503a4488800b0380b20344803070565600380c0c443c0901c1e20b482004140f404040d250202c900f400f50a0a07180c000090501c035995000426180c44000102c40303049000f8182c04004c01454411462084002c00440400182c460060100c28000408a85040d0280e01c00e642e03401029900400b240c0c40d902d8003c01c01a01502e40e8042448511008a2011030510031180c2c46004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 909136555 1250 909135305 909135323
    0xf0e1e06030703060e0c04180507020613080c01060b0918010503030a0302071b0b1e030c22030c06110d05040f050904060f050108010f3b030405040c0e011b 68
    0x59040052503440102034074201a1507150015052011860b40e0303000e01d505904040c1c440e4100407032072440d03e40d900886100c440c18030041c005210740101350140c01c40310841d5422507002d03050611065a11503000c98480640c0307412030015140107800003a00040c80c1c00c50360311010448803181d981e1403070710078080d2907071581003081803008040c029401000d40d507228181800c0d10022500d001109081c40358015509240e001540d101031841d100b20750284680100c0c010303804c0d428016803000950203407001c09902e00c644030f00b0003441007680d1000d190003598807480d8444001e496203001006400d0f080100c00443c0300d0755112100180c05203054405480c02414a01c0d5568549420440c01d00303806001950345c1a91071020049410701c0d805054080c0070020004210600020381c01000c480174000c010030843c1e50095100d141e030085d12080903d08900d030303500c3c6503815810701081d41503100d030747e02040c0c0c064078105c2070760030654005a0035001103209894424003039291203104501c50300001801410703001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 909137805 1250 909136555 909136609
    0x606120705061e04090f0b121209040e0a052d15041137050d080901120c180e07080a0510081b15070803010306090f020d030f0e 56
    0x60001c00b60903c071503124007441e4100484440b582c8280d101c0e4201c40c40898036032950000e0030080e40030f8401100740c03d640d00d44401d8100d00b0440d8880100111840e10035070001000c50403030b0386070341200358155404400d4a00e0132545182641c1d4400980005030302084040104504c0500410002c030b4035121007a003c0c00e800144e0340122000514005c0044071480255004840c16403220340c41400c520b1b0044145400c640d40098003800364040000040e90003810800d02444503441e8a1401d211450340007000607229003488005a4046080100202d20306103014040050f0b0350b403100784540d10660702550028410b0701d4041080800c4002c80e110008286694042401d0403032603402640e0110b454100b4504154442d0126800c081e80c3c50284611129200c0840b13005243c44405881c148000403c4d03189004109c1d075030810b003800140f001800c2541e54104204c18000200c180914980e401000c94068081c24580a0403061210b084180003945108108995007020a070002d003084500103015010a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 909139055 1250 909137805 909137809
    0x3030406121112070e0102100b01120e12030a06030b07080402011b03020f030f0c06070908100b04020708030a09030806030f0c040b03030405060301030c06020105060102010c0f081b0c010e0606120705 87
    0x24a00c0440b078486500f045000c2c4a0022101514000c4c00543d41e0042d8440a0310002842d2440c1030361001c42c1607140491481050380c20a4204042941001c408203a082202107190b007001800c02010543c48000420011304107241d0740850b0950340719071070803a03890f00d400380211101d035800c40d0000d01040444442184200a08220b001010301c203104171407a01c10800507460440c1c0041d4440c00c0401d0002c6002c3c42c0010081c45116885081403900a1a02e1320304001c05035500000d540c004109541e0b8070b001000c0703071142d404039582e8903000440795580b402e1589080004210840c8294009580b0401160306031602003058164101c40d8002800da5106e03071001c1100401540341c550b40e05200410001170113440704006140251b003c1c2c0c1441061070b01c0c108010f401d64500074501c5046900d00070250b0710300d40d000507400c0b9a110341850003482c69a25107003000d860348042e020400362802c001c60300010550054012007000100c0c0780c15182c094941c036090200e0942c0304220168180c10010081c400c0e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 909140305 1250 909139055 909139061
    0xe09011419060f110109030c2d080405090a0b13110702031002090319020102150c0c010608030d0f060806010b0702012d112116050111030103020f0303040612 69
    0x201a00800240c0741452141032100d000469600040100d011005107803400c0341c01881d85507040920b04020301c40040996070003080c1030f45940d0002e0411900662840346c1c0d00100413416900c19510743c244031016001d00382944250070502c2000d12500c0a44c000a06644ca503018044032448081c080c41c0d0312100b5900d00c1c3c03025000115514034805000c0c40028090303601003100c080b041d5001113005955401000138181001030303007030800108a40d04404000140d90000f08801004640c05440388291240d4101d8082403080c4e00c0c1c3c440d13142d800c0207008542c030724010005002210200c03104016800302d1807440416200144100c03c450741081004014010900e03008141c858414035001a0f04600e9100001030301144405105240c580004005040380c0c01040881c41451030b0300003400b000908004003424800042e482c007441400c041440d10421302059800c4540f01d81c414024880c005d02804900c480e60401d200c103030711500d000c90201056042c04000c941c161080390395414a5041034030862009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 909141555 1250 909140305 909140339
    0x2f0a0818030f2101061d0616151b0e0f19050d05010207020109050d32070b090f06040302090f07050f0403031e0206070c02010e0604080118120e0901 65
    0x10740000c01412140c035040300010034080000301024003881c814900600c01c0000c05070841001e03c40c0824018a1402255680c1c3e00d0300001101c0d503d940e082e4044030f0b21488004e401000700340d1010640e1006501d8120342142c4141410000e6a0324403c0001000311820f80205a4540d0045840969a04c3c0d80c1441d4404081d160322010310841129994400710f039007904040c0302074420341d602054490071580e20103601001000c044619001082c6143c0300c41a83c41c004c0151400840040c10180b60303000345440e269001c400250041d14542c80e52030380802d03c90b50050a51511075125017050500c18079014056030242e07500545040303040d64540145584401c006420301341800003d028a800030844000188041d600c2555500d40f041804200019040e441013500c42c29900000c00f040a429444240d40c3c3e520340d02440c0c07032044581202c0114180d03202d5900a06c0b80b5500303000402c2e5003803c854024800303c5204006403141e8048030b450480e030344650740603050b50001040380100020340011170011a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 909142805 1250 909141555 909141601
    0x2040e0615150c0303070203190305100506030702010b060c03040f08070812030901060b1303110405160c02150c010c02060906040827030604110411031312122f0a08 72
    0x114020301c0483ca6461500102e8044005a100145503290b840c0101040c081100c0d683c10306221904103005541443c0308103005240c013824002c000600058800d420540d25401c0107848183d0718142180d0f041d45030350090240030300c40d0594210011b0070000009149080f20b260340301800c0c108807402c840d41c42c20740c406460b420750342d925650701080b540d23a1100200f01050447c030b031120750103255251100f6054080540d041c8541d02c0d000411110101000b4065501d40c458544140309901600c0080c100c01c5030701d50b400c1c80c0d000c004158101032450560201c0710464298086801590341c15500702d54401085030000d04124080c410510341c00900070101d14084c3c0600241d03d40501d0f10b0012a2912030122004d540c0800e1104038400079007418843c44101e595151211407039403404101c41e004050621130014016845044203070341041c464041c403244a10744003414005c452103024104a06015505400c2c009882c1e080e04c0041c0405820890716800f200d601e40c1c10381603076004100d895890000b03100c05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 909144055 1250 909142805 909142807
    0xb070c0c1a0403030f0305041101050d09060204031b170a02040b1201020c0718060b1c0e0a290423070f06090f0909030203121b0a050702040e061515 65
    0x10840c014407191180e0348458400d2029115440c60a004010b01000c800c80000d0514213020300001c070b0300c414201c8040b1a030070b00340940c3d18038502d400d50b00208101c2c2c01c09043d451001c2004400c00520885021044c034001094450064503102000e2610191a50990640e480109071000500302500a107400040041030413031803804000607242644e0211850790b400e81c004074001d0003a410718101e00080c5c00c6a0490812400f8200424416140302e00907045a901d4034031003941000390299040741c4142e08200e015030303221a15074504a5010a580d80d0000e4088040011451001d40c14450051040c0d80101002c074841103600030321403006120401a4071305001d00507000c00c0c4004015070133070040100d90b8403135a05618040180301440442d80103403c18508111480300403070f41c00029160003000d0301807514029102c00c03d41d501c04098003004500c03c010301281a00c902c5404c04007401c001802039a0600c01c50068001d2240c0b100e004888044012820000460303050401040e0036804155480e202 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 909145305 1250 909144055 909144059
    0x60e030405061602030d1b1e1209080c060306090c03060102250e0624030702030c07060f081e0a020702040b09040f031d10140d0f0f0e07030b070c0c 65
    0x40b401540c030104489040343d148198000440c1401c004004d2404001d10708894102c8031a104195500742d100e2000d4002c10600702000072403290244500b0b281c5911040c0300416001400d4064072045c0c17188103080650080ca00a8516400c1503030031640314000c0149031140f04d6541d10140d044035000a00386c90304512400981310286452000003001c4001c1000080355041c0c0b41201441170a000140214001c0510301d141c01650302d41e00c403903420384c12411100342e40c5030741e10220200c0c07550142d654504214400c1003000a4429040070358034400c0c1559903507030009985d0b00c1124a20000c0da0300c1c101c0d00300308004800146416026409050000d20091010131400022070000c1c05100e02a2401e480b00c8901107a8041015045003145801201c0728140c0c000d22104240000caa441c1e04440140601014050703010600c10079100b2160001d051003c108586503d201d9400000c1103421506000140361041040c45010001083d034200c03070b44548414466560a401240c0a000c4404200c80c020400100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 909146555 1250 909145305 909145309
    0x20c060d0b150903070b120a1d07060315080d081f05120303072a1506030b0a0f06120203030f0c011b0c05010b0d1a040311010207080409050601020309090103060e030405 74
    0x464100c4800d903282c1c86450b4140c0808240c18100300740e100e000481d408004000d0742861a015450b031040c0e0340480003c0700000d40114040d040160091030455005002e00071030110340540c403441000e000310b0405081c5546507140716903601c00c45034141020910110010703c1c4181958a0602125808035907950055562404614010300160000300107410100801c445030341c1c001c0004005009800c201c00d1150440313500c800b404d080d00c03040a0148084204c03003820307405454010704000c44e8008981c00045c0f4003400100010080380c40300320b0485003400c800181080c4004001031a143d00100030f035280002d0000708007803e0340701605001240d52544427008031400c000c800e8028509068681c880c40100030701e400ea00711106606c02911900c02014070030042031401d9922404442001d014440540b81d60905517180400343c43c01c0c04680d80002419020052070002030011500088003e0181d40c40b500700580c0c030b0f030203072000041e040f16800004102184007600300e02c103484000f4007904d01d80781d241c00c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 909147805 1250 909146555 909146569
    0xf06120a050a02101716200c0108061e1c0b090a0b0c19030c17090a0b090d0203090112090605010b041d010803031302150a02160b0a020c060d0b 63
    0xe403042c0e00100b100d6010341c00c0c070000301c20b0260000d00d0b007030a007100c44a0003400d002c41d000e0141d54030340311031000a0401c0c5004112501032200302050310800f0401219085940e003009060711400284440007042003800c0c110050f603140010404d4658424940c00300b072042003078562803e1070400d44c00a041c8008101a900542d000b034040501401600d0301c80d0408070308020010307110064a041c100b0079190341418607840860086654034022481e1a004401102c144031130416440300f81843d20b00b886124000001d01803e0144546c211888a58071680c10546508081c0848005030300100400681c0e58824410482842e40e10b4000164084140d1120300c1260f074241c0014011040000701446030a4050036603070710b0f0403150781c01d07142c80f907041c007284648900001d041a48500141d118000444d03482d503064081c14a680b0b4096500c0d03409100000b940e661100c0400e03261019040e4010406180c1c1d4003ca50b0208866002820702e07031403010074003010780c3c001040da020880c1d9828030a800780d82e03480303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 909149055 1250 909147805 909147823
    0x40c0c080d0509071d01060807170c0a1101050f010e100f08060714030709060509040609020730021c050d091214040e1302150309010603050601050f090f0612 69
    0xc8800507040c54103000ca03900d85803890f00710b0780640d0020305004645d984801501415503d4501c3c0043c2182c54080081e03034207000107000e0760700d2001418100448068610081c0c44512000d6540805042e04100c0c03050803103006941c152400510000140003039402c900c58150030814264003c192182c1d1000c2e05028803201d40c004007025000103083c4401c042c4d01030107002c80700d50420102844c2d8201008050180340c080c1c8529000c1c060b0100300700d1200da6659000400802040c00255600e54052502e0381e03811001b44c03501c80c0e000d424403220103c40c041015100360b250060750020030315104c00c49842025028403480038003c2200c100186104e2907440d001c3d25a040b84510301c2c000d08081100c80c003078000140785001e80c0d8507440c00d01082001e13078815010250003e2400c40ca00320000c60740d0022441c44082c43d5500c0307064060000500c00007030015402442103d00a0042d20700590300c8104100340002010042644424480041480d2020340a11a038001134003c2a04160704e003414009400d04000c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 909150305 1250 909149055 909149077
    0x50a0b0c19030506091819020112180b0c071e061d0c130b010e01050c0c0901061713121b02130c0e0906031c0302040513020304050d140306040c0c08 65
    0x1650a200035030501c01041030b0400c3c00c031b0828a520417105050340b5078402c8603428581c0c4403038070401c100c015039000b40201e031603113611100c042c04400011145184625001c6808071a00d49200c00012502860b1009640c5040c0d40003041c004038011030f032140d10203038000d07039130945049694044d403200071011031440318440461107018100e800c0c0810f0400c41e0b04000c4000c01000c4034149a00244160f034420060240ea070030909045441d07a5a0251003482c0010740c198454000080400100303d460300000e84000380d20360400d102080341d9a0201200c07800e0703200e00d07004255849140c00d0400440c01020705558408a081c80011510b03000e4000400281007020005032141c2d07074010141c900c0b9800b2140820100040c3c07090b410909020004c00da58103650315842c0d02d49030b180b0750790610141c0700303804803401440b00901d614400c0c100b85183c032000b940162001c4480b442034070110440e09001e09220407011034240c034458190343c0c0351418440030748400710140d0200312001d00640001280030300901420840303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 909151555 1250 909150305 909150311
    0xb04121b11031006030314070f230f070303050702210105010306050603150108100e100e0102040905072c1c08070b100e04030f030e0a061e0207050a0b0c1903 69
    0x446014141803980461081c690f1604040303040c40407981245d00d000d4210020403445985000070304100d00ca901d180f01c4020800c00701820511200d00380d401180e1540c41c003807004d48003400c050281c020b5644019100080120b01d050002034058a40300100a284074091800b1004410041501c3d0782101c800341c0048030443c0e0703502c0c1444920b003401c010350716509965000d022503c0d4104105644c0d43c80842ea52030001d15110702841000c080f06101108591017014030a11036044840013850103504130340206a807042c502000503c0d0b191092103080f141c81c1c0e160003100b2500071101c502c545003010190340c6075000074501404541d10568083c0c030990f00780c012030146451740020324100e194032002034000701031030280b42014001c25012144c042e80059150519280b00098500d05a000d04110315445155000d100f40c440306205140c0c100e00d0484520311b80c000403410a90720400228002e01c4000ba02c150300215460000401c1403000c55000716203150403500f441c4081c18580e92902c601040e0b00000f84d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 909152805 1250 909151555 909151583
    0xa091407031107031d1f0e042307030e01020f0706060302030c04051605070c03020604090e101803050f04090914060a0207020117070e06040b1b03070b04121b 69
    0x5031522502c500003002d903940c9032414500781c400410260b403481c92038075110f180c50300c008400d5440401418031180c90458041c007000300741e80d000e03140b034000001d9203004900f411180c4403505240640c5880660010341204015141c0c5d5004034024064204020b4045d13500300014101503c1601c0905521440f4140c0071030110f041d803041c1804d000080d14031a0041c0d0411040c000ca08251149440c0d1500f100e15000c0c2c3c41d078070030317041101e0107101d2980040d421070030024012540e200f05420807141c01008030304031800381c81040071314002c446103401041d8641d100e580d1301034002881440241405000020003d01703240d150804a01294800e00701111250201d020200c140402800703000e81c44a640d580c210b04000306500040c0007a40d07141c484050a40e0340b5000100d07150b014100d40c2c40030645c007501c940d888603100c0c0d00030307003090740981c0b500d05d403ea0420b032982d2180c500c00001c60b4410741d170101a0503020745865030385021011541e5640c50070b0120782c03803001d80b50314241c2030185c0307070745000d40c1b13001d40005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 909154055 1250 909152805 909152807
    0x1200c010b06130303080a11070b0a140106200f010e010902030d0c0c0315020d051602011a0a060315120510060608090d0e010e040f230907090b0a091407 67
    0x90600c1c01c458050481800044211520510300e40116501801d081e00c0f1a984c40600d10300411003518030310304040001c550034092003601c926103072148583c45c004000155000c0c1002c0f40d005403d100b0b1200003160640c2d2802115085404840a074410f9001c0311111051182001d0940d541004094400e80d0b40d05881c50942c0f030204017008100e00c4504052035032610503121002d4072200c3e8000600500105100c0ea01104c0e401e074110740510b20400310800441c2070800d540781545602c4400c11300150b0900c00c800c4590586210901018030000308400140d52400b10700f900580f8003d84184850700c9541c10003c2e0f110401d0700c0d03102d803191161000d020708080c0c6010850481c1c1031500920104003480080246c88680002c2c480818591814145003910b20749004803000800704940380c0e00541030000030008008180c00c514001724084803200020300b1850100d00300e00c50210744810386540074040c20080d00120398040d0310719000107032030502040c1d1650b561005803402d40d021041c00c0c40644040107501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 909155305 1250 909154055 909154061
    0x1404081207051215010e1c0c050604210618080705120708070303050613090503071703040b010608090309100f0305070302041a130f0b12060102060f04080702010201200c01 75
    0x400e0030010308041940c051084100c0d0018501c10070154500b0038013036203038040c000390001c4d008024000199500b8944100034241511709084480c003003e802c001c1030901e0603206442c16914540d6007000c200d0b140171304100c3c1d0441a40c6003039480561750f0705410302d4040c94841d01c0c800180692051540ca00c018a441e601d04118602c2080f0a06028064680041c08942c11078094507058034020989884043c00a035a0712844a00c900720245840c13188420007070007201500c0c07110302a00b4500c40c025914a40101c2510040720010207030303102000140311883c011404076411880d0071044a043c0517a240100740310714041031004020503005403100d105c941e030600980c2da001c40c0d5481d05500340f80c641003c0c0c0030795510310306034012258400f258110541e1021040c0d00010030b08103081180c0c09540341e251000c55400124201c9000006000148080d400000c10f20f002e40107410b00c2c002d40e81c0e110b803211100c6400c20b2604904554a030b50100b181c1144800307001100603103094066035120240c01d4401c0c21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 909156555 1250 909155305 909155311
    0x70806010207030b04080705100501090c08010803072d02100909202703030703091a030609040312090506040311070911030c0a020304180507090503010e1f14040812 72
    0x110340c45042e00380000f070090401681c12941c4890b0503a1a403120340352260808880d2496440554603010000855415a1300920310303a8200c1d40714604135036280e0f045c59403a80f040c840054681da0000d8911022074008a0002c81c08013540043d52114001907030004217002d07209850300d00043c80c18441444074045a102c1d0490220720645504c03400803465081e44618019061a40c45455060540e0342041413400c051000a0b100101540d0380c415281c50060070449050049410006904d03980b40c0350f00c00f030413080300c0c0207550013005890103a40310390707080350811504044601da140d140c280c8080050300400c40907020364407949030f0304041c05507450030500d0700d44254030810b169410a6803480c103000ea139008403904001c0e5502d005507981c80780b0130b003603103103200b1075201d58460585102e009c9850324982d07005a00031031441d6100719145589008041c01c2e00c5800b4010000b940000944101c5c021580e04280d150940140c1d0210b02c0300b043c01c1c00c000341d1241c101c60540300d5500000307005003040079528030198 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 909157805 1250 909156555 909156557
    0x1103160b090a1521090503040f090c05070c0e0408280311122706040b0604060f05030606040b0f040c0305150103090302071203051207020a060608060702150a0605030708030307080601 80
    0x421803c024004000110140420740380341d00104c1c6541c00e0b45016003120307411300d030004101c07550356030307514602c00c2450400d101c4d01507501c1c80e220f000c5049a00c00e0342101c0d40c00f03800c01d132050009410301e0b007160040c0380c0281088800e0358007008580b00516010407005000f00308000440801440c00f40c02800361000704c500c4000b00c03201007280c09010241c0000e0a504031b440c2c45071100e58212422900400c5e0302a042c80f100c0380344961800c1008001d02ca0362228071455054606001c0c00d982e8030941c824010882c0502649a0800d20000b5110f0902d6440306011b4440104492004207603140071500721811945404006a00c640402008a00f5046200c90a40c000c0ca420408040c081c0c8000f502d07402c01e4010700c280003544058080506211b1419a001914451071036200d505158002070340c0c030b140081084030000d05080b130014a20b0008503a6a10401454028041030f4424003804a01c3c1c0e1001010000520f03a40c0d8000329450324100000e4000d0075444c4021035903818030b01405424802c000701094 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 909159055 1250 909157805 909157829
    0x90c0e0a1e0807050a0b0c03092214010509070305090c0618012715050c030409050906071706100c060e011d0f10050405032107200a1103160b090a 64
    0x517038803440458422155040c10f05a102c1c40c040c0100c0703080d0f01c01d0840240d44083da080c8803007080d40d0322018071058416900010401c540c500006040d000000341f00d2654402c5100340084c5015000f9000140d000c0c8500703003070321201c0c3c6035000000c0680d04180c80f0a4070100748545003180710b5800c82910044a81041a42d0700c9004401600c00c0c014043c90007841d0200c20108a039814542c069002da8040030813560949460b6500d56400c80014402103504640f14031501c008560300d01d0144000d40704100202d40b40e20200d03600e42c020b01c00400070303c40040040000409482001c80c03142c0c8290840742f10800300100d501c0c0f00c0d2180441a80c00800c01c44c1906030001110085003010002c2c1c5c00480241c8000e01050b65603ca052460542c00341ea41d0314864584000041c141c107401c40744100744201c038582c42d100d10008104102c940121513001d200001923001c0c003115404155400000705c10700d00018110b4034502500014820416456882004441c00c04185080303a858050100405044600520 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 909160305 1250 909159055 909159059
    0x52818090207121112180a1202030601060f110115081227040f0f0501090f0603260c0f010207061a060d051012050a200a090c0e0a1e0807 60
    0x8034010420301c208100340302400703044d0004d02c1414860940c14401506015891b03086c84012046600e0a10348158850080b48801059200c0c80d0348004001c00e070064020803d0360700b04034080c0c94200401502105112164101c06402e1100340242c040c5444940121002c16181070407a03407a00d44407072001e0320709080500c2041c1100a1246612004080c10034020340041642008500100007095810817407a040c41c01650084045400250488091040c20003280c120350380020b04031082404002e1440ca80c0c100030841c000e40c1895035840200510008901c1c01766421807031498445040f141d02e6090750007088903005d102482c456004031740e1040c50194071202903000060b0300d038450070b800802034607512000b080c00c908806001070060100c40024200740581820056511040200d0460703050800c00709040704d03150b082c1c507100e00c4c00c031024000f1003015082c108030300040c11521000b002006410442c200c4141c1d0b40ca00b1000041c0b40c3e0401c0042240801420900c0324405038114000b281c0c071000003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 909161555 1250 909160305 909160313
    0x409031e0f02030304060b0a030f0803040507061d0607050118030206091c050405040f06090509010b09010f03021807020a051209010f0806060f130504021305100f020d052818090207 79
    0x1301ca51241d408180004d80090080015910a80c250000360014201a40d86010008600000c41c0180d0051003110621541c40208441c40340d1019403c001e0032210702584151402d0401c00b03420700c607114000214000715208149940414914070940050740a00203005117200d01348005200100c580c10342e88821640400042c0c44da2145101d02409035a03681e00e034a0100c4800e03408a0080d2154440c1800325050004070b40b80030707100690801d0f201c0c81ca42000000c40e544808486030171070b0360142c92118008403203003040b80b000030001c00343c8096005041420303000402c14024a062501c0031206503495480315030004140c03c2138078440400f4030138100e06001140c1d03120ba041e50031181c408681c0660320000c0c911085101c103501da100b61f41150001c40c920310200107410307888040d241e0036601d503488030400c00c5084855170b44544c00c10300540c020b40c0c411139010b0f20420090a01e14035590040c41c042e4564620f8912440901015100203011900f4005003241c2c2070107024001c000f520b01c190b0401da4a921 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 909162805 1250 909161555 909161557
    0xf090b0603070807051606020a030e1903080c0408030304060204090e0312060f04020d14010503010e0d080402130b0607030f02010f060311120c10020708120a051c06050409031e0f0203 80
    0x4010311519000007080130b8803680403551024624a0704404a141614000307000e5040081c005011904050301d03103140520000f80c00860380b4048403169044400c5480594203080041c240c4500100b0410001c00c4c8074600300005c5008030b2143c2001646d0b41e1400301044116a043c00c101c000c00d030070400c400c10801c1210101507401c0b2100700c501c003a213190b606000034001d1082d09070400c8010b08056000c1c0014803e1105581210300c01d030000e0181c010004081a01e0344006011000407031844c07804200541080c40d0488003001d00c2c00000035815200000103059170704202022070000c0c090803107880145074207008400240010074010b01c103036401c42d0390349800904104c2c03050b40220a0800f1058030014108100120010302412000d0350101c4641e000f034a50704c4502544019228080742c401003022614200e440caa07443d03903581d500b08801000580c6219080d010018411501d403107000c9003a50b124807850b2400e501c41d07241d00c030825648180c40f00c0f011240d00d090000340b20860b040a900550044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 909164055 1250 909162805 909162811
    0x903091e100815010c0803071b020a14012c040b03030d0615020111252d0606050a1505030405070807060302041d090316050c13060f090b0603 62
    0x11044506000320031040d6a2540d01020500c1e800903041004049660b00422924040c4103d0322101c4502c0c850031005580030421984000c05000c4100300040a0074815080d4049003094281c1440842c1c0c2030780c0024503040025004912a130b034005c035448a10350b07081056071140310002d52506044203203021890081d1900101c2c0ca500031034841584000c107030381c2481210b44060707149004000103500d690b01610b456001e080410055841c108050210302d0a40c02520542456440e42c1e03501820b082146500c2c2205880b0125080e000e00d18444c802800c0e110b2030200d8050410030690030b64610340c00c10100b5a002544100d0040c0e80440c014402c04801d2146c02c0e03150401c5060195880c0c560380b621603d0f0040035800600240654500800c1141e815001401120002c181c480b01501c0010500140c001c41a910040c15500c01c003c030842d13005001c82c50403141c178010301c2514800c03040d410120b020b5001d90181940d84690f603080501c9034143d41c0e5040030107071005100c200054001400030030054030001e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 909165305 1250 909164055 909164059
    0xe01090507022e060b04141905090c090d060e16050a050901030b1905191a0a0306050709180c0f230d091a06120a0510020a0e0303070b06030114090309 66
    0x82c140c800000f00564205200901c0e00a1505a849503a107054440c000b104a559520602c0846606002989130f48000419a50010f1402c4070b80e450f41c3c02401c0143c1c1c0941082500080102d03000d50106045101d10180c08000c02c000c0c280740c02030a40102007041c0381c3e4015a20070174240c441030015895a2035045c0c152603001401112a4942c0410b03510342d6009000c1400b070041c10102000070007004081c00b0f240b0b010008005000b0325a00c0354800062401c1038811640120480200b080800c4039904403c0d004021414404001038454040f01da1889840c00307803428281c0c0b5800b810001c5c0d030b4021191507418081c1e1400034000e064964543c0c1c40f0800007a00d0b400a80004260400070148582c04040c13100e0380f14100c1844051f0b400700d603024019040315a40e1058a924245620940c00415614600c40d0f000700a8003450a00c10368000c000d4020b0f004c4803040007d85500c050551310100000c3c940c42d406441a40c500f460148101400e5484031421108c2c120483c0040c03103900100003040c0c079241d51003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 909166555 1250 909165305 909165373
    0x10b0906030706081f0506162d030c022d090709180915020a080402030d020303011a181503040c08030f180102010f1a090a09030203031605040306060e0109050702 71
    0x70005005e0501c1e43d4039004564090000039a01441084280f040b00300c162207a185900c1d291b4416158007850318a010341c803070a14040038041000a446008026031451004042180c4014890040100354014115121100403c461101f85500d49411200d40c0000d080c41c140754010b0502e050a0034048400c205c1c110b0560b01c0d584104200b105441e142c102428502e00219160900141c0051400c1c0098505038000d01454004411080c40401245d0607a04103e404042e643c036450081390083d0311600004075040389204528243c1e90750342c00782d041200c00d050b40894981c100340c00e010204032280c1e4800701c1550b00c100042c90280060134180c440307510700c401c1500000310500b40143e014203a00c0c0c80c0009094a4400381d1078140d0304224003000d000c102910100ac440d0350361130700360045030321818001c2c026034424030000e400d55400b544d800c540c4983d03500c2c0090400da0b0b01d580311030903a48a41c20a0b030159816000500c000c852511455501031450b10013071552800c0e0084c40000d480d4504070018010700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 909167805 1250 909166555 909166591
    0x515060304080c010f09120306080d050f0c03070f0c12170d140a1a01020304030803040f03090e0a06150203030403080103060e070302030a050102090306070810090507120e010b090603070608 83
    0xc202d0151507034445000002d0104e0030311362002c10001d10043c5821102c01221101c669000381c443d11070b03a400d9440e44001050110100a026034054006100d88000c0070f5080048000321134080c0041c18003144210b07148030302c0d00f80314980742010303000f55088652019264140340001c21440e44188589420600c0f295507a9840c00d0b0200d40600402d0038000d41c00c0b42101d040c013202c030519501410701c0c3d04443d0b100100c6a0950001261680720b0751201401409090000c140803801c001044c201481c880d04000c1c0c8001d981e4070916400e01e03022150703400d24681c5e80e00100010f02049001e4000c04501d807024501d0b42c9425a40503080482c103000c0034003001c2c5d6601c00b0000d941d20030030468001d107400038111690b2a5092518602070350244510354024000c12000c076010074010b220b041c0c001c0e548802141e00035402c00004e08010000200045c0800126400100128850b44200701c06480c03241c001290b0418114140080420090040e44c02680102000c204190b8800d5146d034104602213000b00c1846 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 909169055 1250 909167805 909167813
    0x31c0609360f12080115030b0105030604020904060e0f01050a0f0506030f0901060803341a07030f0203010e2e060c050a0606080d02160f03080a2c030c040515060304 72
    0xc8030b816001429807078804100c01e500c40c0c01c450424101c98107480310340030000080d00200d00b50f8000f80d4040b130114100b400420001d1405070040c200c0440050400100f55588421140c5020f4060b14462408008a001480701d42026800503024100319000d164040b880d20700803d1040c4401400e103098076140e0004904000c500b1b412520041400604598490410125514280c00c803c0f82c1a15514000340384806005000c0c8903001480f03070002c2000c403410034244c4070108451001400502003642d15603502900740759a101441c040c118010181480d03203042d82100070503112001e1060b002116010304c80107002c0c0c0003100030090791058a040543c0c00090724180b8070b02012070000400581c10030790041800c3c2c0c4002082100c80da819422a456049072580e21030b041d0312903001e6100d0508200c0814000320b5002d00007440c04403618648145040003095001c40105d138007228440422101044880b80762038108001c800090040b60200114103258403256440b041da00b810074010300d07021000038280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 909170305 1250 909169055 909169073
    0x19080c22060912021513080319080117031c02120114030f280501060801020f19050307051b0c0a0f06030c08060915030f0105130c1d011403031c060936 66
    0x908000003141c0e00c2750422500705600031400707808180000d1904000242d041003101d90700c81d070091000080c0d450180400014801443c00d214008440380c0c080049200c0304c03107910001e5000344000e289101c0300003c42410035040403003031a00c03502168003601c00303102560a40e1808020141821040803c03140d400c1c80e126000d0111a13010211551010a041c600c034050036005103000c106215070800c1b4140360280503034181c0001d07601c100000701c050121403032001c1c2c401940180020a6001c4407148143c3c00000354140c0800d400c0351021444020b410000c140c0c03d4011030300218200d04292556103010b00102e02e44510080c04e2842c17a03109080350382170075201482035602005042000303020030301d4074180320b05070358484000c1142e805100f48400203444005020088800d00b401a1881099103002211040c019012000b5941400100113107454a002c8401405281c1c581b4a000700341240b5100c501d4044607031100c44821096941c4801d42c0803450820340d079001424a46402a01210603820702d0102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 909171555 1250 909170305 909170309
    0x1051e04170d140c010e071d010614120a09021f1107031a0c090d050303150f302a010504050105190302090a06030f05070519080c22060912021513 64
    0x68003d1510200d0304140904860611003850210b01d5000e0741e0302c9400310707080e00d40c9540c2d59480c01004d2002400b00c104501d200c0c1d0304a50dd003003001c200c0c3c20541e00042e078010612082c3c04541411005c0003c1050b03001803104c04044054000b0348049441c1d5180c00c0e041541440303110850728006130004000e07046110580e1603000700a003100c405001c5a203001540c030360094802c1c0741135071002440402e843c81c10700c144114011000d840080c25405ca8071a910b0342c81d45031400022001003c020422190108000d40550340b83e1682c00641034041c0b01002d0b00c0016a035144103410008108024407039030b6005800c03514514141d10101d0107203041510118028000c46142c00e902800f80d40000800d43c0e41030704501140008072102300700b2610340c2c131802c0d0350314401e04041800541e10203000301c07103090240101035801607040403c2440d0101400b00344070f418884800d1040c81c203039450814414154000d910130054524004081084119500001c0642c1c00048400042c1c2c8800204901c3c19041c452030500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 909172661 1106 909171555 909171581
    0x30304030e090403020f0d0210050c0306101124040605070c051b031006121406070801090b1207060305011409060a1401051e04170d140c01 61
    0x1c0d030b01c1001082a0154004c171a450142c8800600664154885980c00380040009a00e0388104440001d80004010b035002e0041240c15100c062598580c2d56042c00d01c10020140c001003e071511000c03a01840ca01000e20b12900c0c0303401c100c8054540901e10900007880160341d22502101c104900b0b610151499204160440c540754490750346c180305c4800503080e5200f121074042c8581c01d4645590080c03581c0c0b64621840c00c2407050313102030051016105409400d0390300f002480280500c1042c0074001400741e4440020106580d0000110f24110441003681e0f02c040c0e482801500612007440348440040060888016502d041403400b4403e2000800803010241001255414400026642ca0500c4001c0003103000144c03500c52110280810075400981d0380d4240744c42d071441080000c01000c469480f001c003820342c1c02d4111f50441d0b0004d078906550b68031007a61a40e45400342802c119141 = true := by decide +kernel

theorem cover : BRFrame.Cov 908992805 909172661 := by
  have h0 := BRFrame.cov_init 908992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 908992805 ≤ n) (h2 : n < 909172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
